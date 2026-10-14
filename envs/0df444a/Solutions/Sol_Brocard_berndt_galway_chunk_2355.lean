-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2355
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:28:07.342986+00:00
-- url     : https://prove2.me/submissions/06ad7f80-24c0-4c45-a3c9-c4aff6e24823

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 423381294 ≤ n < 423561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 423382544 1250 423381294 423381317
    0x2120d023903071a07060f27061d06060f030318040e0304050406030b01061814040507021501060528350f041b06050f2206080405150c040603020901 65
    0x404510396518045146400060b0b4401b0003810303125055101d20364000030000080719a02c001c0048046042c0310045848a0583d48240b03c125800006050603800750340388c80c0c01d08191215102c2000701d4603140b048048403440341a5080204c2110340300c400d0208400100c100c0c5404010007003040c0c0841d110b15200078400421a52107a2069030080c3d40a01c1084450790f1408000410b14440100b0006001c51008420401c0c1d510081c0c00c2100400125008107044e035660004918261351882080310011805000041d81904440244981071007111120744080e070f410035404680198401c507030000745400940c0001c0744980400700e050300400f4180040009007034691451840015079054400d0100f0b0424401003045004054801070a01d194032200a880d100380509180a070f03030300d003e210840c00903507142c107001da004e8600300309444c4410030429141c03100c2d4000c21242040350115914480c0b801803880c423552400c0c000303200d0300c002490a031605080540840c069081803000e941401100c1c06034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 423383794 1250 423382544 423382559
    0x201232a0301231206180a0201020c090604090f0605190203041e1502221202030d03050a0207060513120c0c09020f09030319080106050a0e0405060d02120d02390307 72
    0xd5002a0020000034407440c1040d06141e10502d0007441d030100c42d070f84841c0d1f1100050360041201e10300900200c0e0304c11560f56801c3e010a000c0c000b550740061290218081940411035035510190049100e00c0410214072804074084c1d040f0312060b50003030301201d1051440000b004200d02452421480b800ca091100760f081c030b244000b645c004084200112641040600d6110356012b000d000400d00c0c1c800c031070f0f071680b00390700401d4030360202007520020140c440340029140c1c2c0150701150a40c5600180401151400e8103450f000c110f40004222451208042003416251050480850150b0045d041d04086403500b154140294000c03a03c0c196200014000e1007120b64060001d0003041da03c0b490440c8941d1181e501c000c00d5944141c00031400d210301801183d10385948070a06003040b03281540c002032191a101c000440c45031502400030b40c40b00c403c0c1c1c040601c10202058080707160b0318940844d101c041184a07060104841c002c80b0b6248545c1040c0e6145140400700014544a04040c045c0e440ca562250030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 423385044 1250 423383794 423383809
    0x7021e04022119020a0f0315150e040f02090901210b011d0703020406020a02011b0b010b070506010503151303180906030b060a0617070201232a030123 66
    0x4004002c1c0341d08108801044074040303001845411003801c602d41411100c001c2c100c103030b14810240c10984e44003a9810f041d003a400440020303200b40509002440040c40c0c0003000e5110031024180140e040600458181000b0f009880080304010040c171140d03800c0c49024070007441802c420b8055940f50900c0400426216020385000e02911917410f01c0707104a071800b00006100241541081501c10032041007020750100b40040001c1c0d091038011803010900810740c2504d9443c08000d040106111700000e2641e09120050000d98807801c1614810b030b98400802d03445001d0340d80b003440010685c6c00052590b0141481c20302032544203090802c0d50096500444201ea603080d0040c000c0c1503a03910007030040c400c40510f400e5100758121200c11034141007610040500e400044d200742c0d901d1420003c0f030b08440c000e400100c082040b50b840508207204a004444018000b07580d802094640403421421103030342244425403522829401e00d241d6480c1410707a14000290804070101c944406d801802c3d150744085 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 423386294 1250 423385044 423385087
    0x7050f0a051b06010e1603020f13180b010801030807080c1507110c0604030f170310031103010203040201090b1305030f0a0203120a02060a1d01180c0b07021e0402 71
    0x1d070349030385480b907000704207052a041942d91031a981c8804010440b20000c48500c540c0b02c18004d04503e091a074100c401e6020b4000ca4020450f881c0001c604141d41001c0c400c0e9000886140880112450510340c10800486013180da01c0360000d2101e80050020681c603030002c000311340c400d03151f07249860304003291141482c141c1030000d803207040c020f0144600a5880340d054802610b00d4000b418440100e000042d01a01c51480000c1610b200b014071345051000044d02000070714100b04150303030380f842e1000b113900080b6503d000441d0600495001d614003400d0520030f07203210b26810784404a055080158502144e080141060300c0c0c000143d9020405131814010a030015030700d071700244001c6060b40304150038207581c90f0412011840c01c0c03150541c4a1707800644150800000c0a000800301c106284e5001800c81c412400c2e6010360a050a102680c0c105010303507000607000750248200e540c0c9403071041c01944a0311501940c846007800e020352094003c0900070b010710070700a00062a01b00810244189080900d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 423387544 1250 423386294 423386297
    0x8030609130609030e0406080f07150e0a0303110607050a0e040b0a05030a14011a03190507030c240e13020310090905030d0e011e1a06030a060612060303080f07050f0a 73
    0x42e00f05d45070505160044102901c4030313901404510582d011010350b180024421240c0da0300301c281e44400c85134054020900701d4070001d0050304403e600d0307050103001c0c03090340b000049140c0f24032400190042e106106035145816650785aa804070408001c02c005001c4070300010b81d019500320320000745c680d0200306103030005100314071040603152015102400c40f01032401003207407a580f068140f0007968001ca941c00b10303014070300c0c80c80c4038408060415602c3c01d0555040100001e40d001c401240903000507034654550391103c1010b070b01e03040300080c080f80c945514a05940e0454645002c90a5a4410f6005158480074400d00d0100c441d644840308004c0e1004100c1c03c6d50a6040007441088100117401009194640b01e0001d0041c030700d030800460040c030403404480015594410380072050366600c080c42c44c4030a03001440c040d00c1e130800300019801006148202c4003c1007000030303101036080c030902604045079095203c80c089695503401945988400030304240800600b04201146a588100a4000301619 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 423388794 1250 423387544 423387557
    0x302010e011d0111070f0320120c10060303120e0f0604080a080a060e0103020f0301021e03070f0c1a090a0807060b1e092208340803060913060903 64
    0x1c0341282d908450705100340b0024070108000c61400b250502d110303a990f1039031601c0c00d074030707125940600c540200301c820340e19078058010b044a4026559071200540301c18030502054070f8440c024a11540c040b15910b100040101720400410040400c840d03100010902d0800d003610404148a001942407150455040715032040100705a00d115074000c9409134004d12540303040040700c2c1801c5030144010014400203204008040d03021900751001c0d011b441d00d4414a10590680c0c24217a007010006800c215402000030780d1406802512138170500c4a2024117400848800c03041d01407001c140c816000c000c200c0e200a22990b102c88000958000040c0211401103400050812400d410000c0c0b0040420555459498410040d0480e903100e0540c3c641010f492110780b80d1103080030144c3d0211480800b006481e00e0000b2030382041030a859040c00b020a11901e0111413411600c14800030150070015000e080d400040c800140a418080c04450b00800008443d8400e1030700340e990b1801785d866400048000445 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 423390044 1250 423388794 423388841
    0x2010b030106080d0201110a0c11040e0d030f0e01090f0602250c0e0c0405031e0c060c01090c090203040c03030c240f1109030c040207061d0a05120a1b0302010e01 71
    0x50a21607d802c610003d11124070f06008020005e000302d0311990007800014984e51202e032a132303880382e22a0609118034404e90f00100d0150078080c00500c42404072044031410031b060040c1c0ca82040c840c80b00c85540c400540c98103180ba54940d080290007007550081560441c810030150101011200c0b9401c07407140090182a03410202003c00030040079041c2140300c0001e200c08d220590300070444501d41403115103580c0e625800b0f80f0302c8a2801031302100342c6030081e1002903071031031580d81900a00701c50b40c080c5004442080d03603980c0d0791003240b01c210340190444280407403c1c00007a105540104000c1c1c007a114180e02008240a82d010003206521100d07286650b0b50701c0d00d070580509000307444111860208803404c1844041c082030300d511001100303030310070f0313600045013020002d2a42c00f003080c0c4080c0c41a0005c00100030000c19590b000080b0080c0c9540c0305010740b01021070f40040c21a148418140c0c0c403a00d506603548078007100380044200c01ca00f5952a8000800d50003400d106a0a5171480010854507054 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 423391294 1250 423390044 423390047
    0x1150b03090c0108040206091212030720071208070501140a020705010e06060105030a0b130e071d0105030d0507030314070801140904110f0612010b03010f05060c100c02010b030106080d 81
    0x942c92402c0b01d040c403131100304000160f5180402d40d850800b0649000588055040c3c045052111021108510010100034009c20030b5000046603a251b1821442100740c1075040e180c103940c1d0001e407003a0036400c21003125000009080c4000307862640d00c40c2001007034003038000700c0c4000062011030700c43c000d00b0b82c0840c2107014803409000c0c07014145104806030550f428103400080031888024820244561100c583d86215121500300d1030035041595801c01450580440c0c7c292038662500c1400a07403c091031084280072403461207103040740c600400400b420400303031400761915041501d041d014180d85428080820203483c2c0d40030300c500c890381c3e6409401d43c1800a454440160310b0740143c054480c610800c030005d4490403800a0800b0700311582e40124014070005800c41c855040401071079080d104c0002401c41c1c9400241d030503620040b01d00c9421039211001d01040d40100304030340305a0340c0300756001401d100c003d80c8410408080d5100118080000d800131900f0368403254410759941c1c2c050030710110700b1b9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 423392544 1250 423391294 423391303
    0x40b180a05010e0f0f15030a0e010509031305010e010324051201020711091017060115032d020d140415060815060303041a090a1a0a050c01150b0309 65
    0x9080c00d081a5042456210225510310540c84409019409250f4501d040d0b90303d01b21101c080394481c00400c5d9491070440007000240a81c00b6421040e0360810002c180044804019910464805600d4426451802c001190022540882e0505241c0e480240224060081c1d1140282d10702180300903502178941010300000c000d0483d0a05e42d164814010180001c411010403034440504481e10709803501c2d0410381c1d07900140254021f590070f910104071a200810040740c3c20303048440349101c02e440f09140220a4003910b5406e01d04441d001c491803059188040c4899017198040c00744400103003883c2d00042c0b400d08680d4500d614050b00e06c0c24000b00400c105000c041d0380582e800c80d010503c909071070001b400d40d03512005600042070113002000501103440800543e4010107020440141e054001c5800707902d241e00c010b0300d40380a0341c5d03164130215110540600350284580c002480a1800702c02807000c417426080b01400038101e540710b8403494507002c1d14041c0301c4017074010480000e98a0070000c50242c0350 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 423393794 1250 423392544 423392549
    0xb090a020a080703020a1409150c060a061212120e010e0a0507090908070f170301090e0f01050124020321071e0210050703020702042c061515040b180a 66
    0xf01801001b0408141d40c1c0886411401c070701250050742c44402080c0010008100061201140303000032400740c40000b000a070726401800c407501d00304121503d4600100b40c2c0040741e2006081081161040c15846100e40c000c10072400c0c0c1105c0001d0514081c059190135a000d0340168290713580040ca41c2010302c60300340305410080241d400f040003540d40303e07030715400300f40102603015040407046204101840308000c0720800755001191616560f68661020000500c0180c00248840c420303403401c000c80427414032070107060307404103000d2011440c0c40b01490b0001d240038108040c1140010300040740501ca204003540c0c200f0320309288900390342c40e0482000b032440c05e45140074842030540c20400940b00e034002c10b81c9082c401060802240c50342d9101000e40c040c1c800c41c04000d42084c07801c04000881c80c50400c1e518a800b40d00035180303800000d8a2241582c924054800c00e420f0700e0b404559201358030b0b048950b440d1421401310a103007850b80d40c000d8203843c2d4002070346010403408038410300e80551624401e801c02 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 423395044 1250 423393794 423393797
    0x141c02190210090314010603060506091009050c0405030106090f0e28020103062105010f0c0815010c0c06020f010c1d040915110d05010509091c030b090a020a0807 71
    0x88101040e01280d041680500019024000541c640c0d06203910440c1c08502039604119501985400100303454001c00e42440140c40c0c03e490480030503058585a05940c1c02158510100c1007400e08040000b0000c01014010080c003810411001070309843c03e0003008000c011420717000030b410b019910683c0940c2c4d408416a80540c00ca042c52035a200e5034101c0364450408180c21880b45a040c1d480141c000b004c07160004902a00c090301100c0805801068480c0168801c07802403014800c078205040c2a0b446052041c8086032202c00011038407610f02d040400000d07014940041d981c401e98071000c0d019111500b24200680080760507c041c07900074003c81444506c07600d404030307207007000101c11f20603c44090703142c1d03205603100c116071f5051101020084030100c000120400049a991250012550050320080942ca0402000041c10720f42005078501c01e0a80c0c4029010141031941850380c0d506c4020703040e40c01c1c5584d84800d032503503458174185203102d124131007801a0b54040821028150b800014003920 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 423396294 1250 423395044 423395053
    0x1005060d3023070f240f0203100608151203160308150a0b0f09040b040221060a03110d1b030f05060901050c0a1103040504020310051201060605070206030a09141c02 72
    0x34006145016162840340d0003074012035040c40d01d17603038200c0d000021100c000756160601001200040c1c2c1c0d039000714012000c2c0803c0e0300b03003181d4441040c0c0d0080001c03643e1072281400d0420b980b03200e00781803070300359144c030b419105891600c0c40b030040200385042003003c10b0740042c015004000c02ca850b10644081c0312001103c1f90138400e4a06105000d00d0320030300325400c200b40301c08540140a41c03142d42282941141c01041591210342210b400d84500c03000243c0b41c1d50310590b4101061070b90804032008019a07800c0303200c03100009a440c0c180300800940301000c031072000b10940094a40684d4031b1090340038520a08040000d0038250801c9458030f500a00b072440c43c1c2e450481800342c540741c83e204844065145051518000a08180542c103600840c0d00264120b4000020002c0c0c12440300303407000c25240215040c0c18014040d03144542201d032580181740c0410820800c01c4050303d444c101440d03100a0001c0c005c100c4080c48e41d20201684400c50304d80882d5803000458965403440d440002c1c505480a10061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 423397544 1250 423396294 423396307
    0x8130f1a030903090d020f04050103060c0914030705040c11030a05040e0f160807050c060a050105040c0c080a080402040914150601021204030609080c0a12021005060d3023 75
    0x2503264801c0700c0200f0b00c01d1009017841e80464a5050902d03c090100030410003066a42c7c7c00c003600503201850b107090004101c2100850350707007018812a508541d020340100052404c0c601440001c0c440b8021100503c00380d0619a003246808100a0184040503920a0b03101d13850320f4452100140c028008420344490481004202000110075100f603054a250501660b19809400d0350944030701c0750380d01c0d0580120010404108034071303008281220001d0718200074401e00800100c800c0f0349104c8005080034410401c141440d807041545c650040e000820005440381d5969465a009036800355402054100c0d0807150030341074071344140c254400d400b0700150800b00c5110041d14103d02c202d0000030110b03075588080000340010340060b901220400000c44042844d103003003210301ca880d0900c890005204058981f00000c001c1e009050140202130315816109503507640c2c00b004100c880d03600b10711000c0018101080c28100c000301e0701508038581c6031409130710b030f00e104042a81f0140c10b1444840d18401c0104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 423398794 1250 423397544 423397561
    0x90303030501050607080306090615070b04050d0206090607050c07170105060411040501120905031b1c02011a0f011404290406020a081b0703080d0b0a030c060c08130f1a03 75
    0xf00c0341e202108a27943d904603560100081d0740f080f00541c48110410380400c00004000315500840c2c01079000303800726805a94900c0d03040782c1d13555048504505682103440440c0c1294000c6019010b09500304003559202c5807100d0390144248192940b00725582e44540a000342418141715402820004490080c40c017030405c8000303080420340180401a040d540c080d15070a00070705100b83e800070f0324945112602885000e0348aa83e0f04080312402c10000040480c520100d0f005205508110414058010b500328000080040b0507616861880c10301500040031b4118030400070042000d001500c08503640d500c0301240440c98140720300e0219080c0c4e00c0030401844219000a0401c0001d980724614a1ba501da0300b030202c151135000b01040c54090310402801108020729080603015810081c003040040da4090741c102b09002d0014400030304070f0442003405000c3c8a20427003c01102c00d0040070000d2070800c0f28041884a802c050380000880110f0340c505101d5131090110361082c0b14880c0e01b0711810342c10f02204 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 423400044 1250 423398794 423398797
    0x610030b0102030a0c08130e0f0c04031205030604021207050315010c021e060d0501091a030d09060f180803040f05030304031502030709091a03061b070b0604021909030303050105060708 81
    0x144081c0680d6176003503030800400e00300300c61060b00106844040c0680c1e81420840030030042d1600c0040c0042500050120480e01d400d40d422650000d109a01500042d04250b4440d0f0002e020700e5000b076000c2008050311911030300310f140211110350701c1a6580c81c1040c00354000c0d0700c111642c0390400c03448044140159540384905400413404801401101c0240c2d070004130035204840d104d1660350b080000003d50f804803580414913844001105900400261007007641310582c039420b0b6008520046000d0084a20545100700d01d0402814402c48410000c00817038582c03401030303208906a91001400380001180b102455000300700a50065051070705655078400c10b1074224074000085540030000071a07a80c030a140c000002e0600d050200003125400e15640c4541c1800011940240b00700030104d680d1007082e0b02607450828130fa950090900300b140e078950300d01d91005001c06600c182c00703002d204c44004501120641c01261030700c0b1500300307074514500a420f4400c141c1c07016105000c20b21400003c950b2820 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 423401294 1250 423400044 423400057
    0xf010f12050c0705060c0d0f06050d030e010e0406081c030b010f0c0201170a050a05151e0d120c0506060616030507020a1a090f04050c041203170406050610030b010203 73
    0xc10205940d65001003088a901440c03001078440e01c02c15040c48000c0403510010030300b4100d460000d01c13610345158108030940c0d0381d5102c0c040d00311084200420200e84500f0504405610514000f40c90409500008068404c55000f1004607004000102c0304252200b8061815410908050002d503603403900103071210020115107028800e481c0b000303104581c80b8a005585500c445800e403210342c104240140c0051604a03990101280b51a0105250701d8051041e880c455a00414103142c45100c0006d007002003801c400d0003504441f40011590024980ca0340000c0300480300d503650110724a8508040345441e01c040c08480c000d83e0100894240c10421780c11040342c1c2501400d205581f8949403004c100040c4060744440d00041e1380790a01d2502c907451030002e01440c0d50480b5015010556041040100ca4040d2945541403500700700400c1400c070016110a4000c1c003d0520004e06000540c100c4107082044900711001c41d62001045070f5450a28034240c00c803e41442c1c2040703804210780000c0d42d24030601 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 423402544 1250 423401294 423401327
    0xa0e1024020c1909020f0a030f06030b0c0c0f07080d0f0e03070302041a040c0207080d17010e0402060c010c030b01110c09010303180b0c0a0b01120c0b0a1407050601050f010f 76
    0x800c10a083c070b007000301402c02041559011907580d0380000794007030355400014958001904041c0003840c803c010740115010f49400501c0388106072988080840725505c88100d4808034080d00c0c4160040410502540e4002c0250002030b00d000f0aa42100800c2078058003221414445a6400100e060701d0005224066030703030544001030848080c0404001290b81c45402d6913200d0b0420490300e40300e9a001c10040219a020300445441c800c2540e0103403030100c00382c2d00c4005d606042400410420010842180d041800540303401d240840514201d405d403030040303a007000880e40707401e40c406440d42d001d0081465144040081c000071002c800002e612000c2c180300c05002c00110b0240384c00a1041d05008100400d90381041ca41d9421700c06171041d03164403a192041d02d034080307240000151480030001513004250312001007e441420b01088a2044c0c0003651840b041114954079a120314040034010a500307400359008000640c50038080001c0343c005000aa8100603409414829054005004c040c43d074000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 423403794 1250 423402544 423402559
    0xd0b0312030c0a030603120c02120d0503060d170307030e0d05160b04110a080601140303030112060f090b010e090606040c1211070503041502070602030a0903030e0a0e1024020c 77
    0x41e45404c401a00590b000907102d070140d134280025040e004105500928400e5818401c82d4290b03441980d201c007a0f107841c420101d20200005403007032070405560f05c0c2582c4250309046203a0324142c03104e03000303030400c4440760007281c6d03691580c24402c0002c0159910044140c5040b130b1419840d000d00f03040307404d00c10400502458114000c2010058070480301c1414250141c1810f900d0340d5201c41550f69880284904a501c0c01c41901052540c18040200e034140d42c9010401e40106c1101d9450f035000f458030701c0c1007040c8140c0d10345800c07001849202885000780b58000c214022418004000c509001003c2c24071849949041080d54889421414411b44002403000c00074049076036076850703000e034800c04030014a980000100422000403c4044680c0700342a0343c00c45040b00d03182d01d0700b0b0f46d81c1c0c80f40d0001000426091103040000920400d00c07030340b45010141c04403194544e01c90980c403403590141c4049039102c3c00d0401c00c0c05000d5030303440500100680220215103030240140d020b920351080e0142c1602600c1c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 423405044 1250 423403794 423403807
    0x103020109050618031c0e040c0509060a091a0703080a0603020f0d021c0b010f1d0121021915080c2a16030c17060c0309010b0d080d0b0312030c 63
    0x38014203c04c10002c0a419142e00803485490034016081d4404100c000c6241d40d030711110349060910419281554030707220a890300d4116420807421f0b4020350803da0402006000201e400b101e40382510301a4402000b145444403820700c1c0c01351880c10000e1140245030b01d400401c03c090b03600d1123281c5606032005d9440d003002ca2500c1c00411901803141481116851015442c04104880401742d24100e40070800c5c2ca1030000c3c0c4030004168008900c02802e444407400000521510003c1c4250400900200d803040d007035000e940d0701064140b0b50300481d98050003032041e0b080006400740101d2000c0c910752032408200510f8100d08514460068000361807407400d00e80080300303490180750003d1159561380421950120749200781202001c032640800c0751480007051b0001291400807045060a2881c40080c00103540e94080da812250002042850a50f40307a02d500111034450340480c40351a0f008060340340d038500500283c2c40c26100584001030207035116900360340c1081c0301d11082c1ca80040c00788441d29a03031074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 423406294 1250 423405044 423405067
    0x2a030e070b1605120301031a0c090f0d240608010e071802040b070c0f1a031810090302010f050105060928090c0e0301110a0e0603132a0b0301030201090506 68
    0x2540203070014094860901c401c1030b440136810241d07040701c3c4596480401521600844418007005440c0b0226036030b001d00c03a01c0800d2812407000064142c2c00b62402d604088661140b130207941c402818031496540d0510350000b4501c8501440d40900190b00085c407658030340007030127969840c0c2d44c071550700d80c0c21004143c40400109034046038001c0484a58181c0c4030019824a040403c0b200d00c82c0030303000035102c4070010f040700084860030005181e8031030301c07425035442685840b4061502c981c4c211050055181220000e00c8510a10310294026800090344040541fa940122101078205601c1a90705101c0501d031070740d4400d544520341200440c240c0748800220010303101c0d44003c1c2c20101c1c000b41170000f0071081c80d901005c40020600101e000340110240c4400b8520140b00781044180052982400c210b0b02e0304003207000790307086400a8141c1c1100005626443d600400c0c0101c00130b0201050004c0c01c0303444905100203009044410710b1607146500d07560001c1c00c03044c0f00f8422a4068003000c00c40b1349084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 423407544 1250 423406294 423406327
    0x30a0201180e090d030c03050f010b0702040b09190e0a050703080c070b180f0d02030d03090302330108160504090303021b030a090f05090c0903070305012a030e070b 72
    0x107040c40c2c0c4005109040280a4507210100908a040001e183c1072001950b81e10a0040030700604020641115513420030481c0c00f55940910004e070b030042e454210001041d00c2d0740e1607072841200c41c2d0110304a80c00c6a4095a03041c0d0b003000d4005030f0658070002004000c2203001c90000d0469074011100c50313646450703404040c1001d54540c0308a40789030001c129440c03a400e03c5030100441c0d0780122120740d58010081c1c10002c162410400107034042d408504c214140c0c5019503c1246900d000380100c515049418640f450302d4451500780007800000c0340304c00e0036100408036101d0701410840d00685030540c0886500d05c80305100344161340c4900d840e0060481454001c3e0304690108403041944040400101c12503582ca030300100711900081c04401c0001480b24410f0803400c240c80c4010304502d103d45035100b00003040c2c0c000140450381400b03150000030001c0e400341701c3c04c2e40300d0f90040d00080e010409514481e07003040529140e0814941400b01074680e42d600401c18200f42e980205140d51902c14030790902810 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 423408794 1250 423407544 423407549
    0xf01081008100f0b030105040f0b060607140a02010e151e0417070e09030f1c0b1e130203060904020112060f0602061602070e07080408070210030504060515030a020118 73
    0xd9014444503484000312030303000b01942c0c0f040200103000d0341808005045c221542268050862151900a40c000400e01c400060b080305c40182501d04108140d19161f6528001500d42c0d602648252404000c41d6001100019820000c540300301c101c034040500c0040303030704c035400c40384001001c030743c12269079011001c060741c0180c506000d116090340c20000c0d40b550399414a02805694001c204001800d00d6000004c03101107019183c01142480303d41540c80540c60070000c0c00000840e2541210729082c0c95000165640840b001f99404184882006002c40c400f030030a003500c8042d0040081054903250744c0c0d001c9070060b41c21f03e4000c0f02460f003da0002d0081105410046000340a481c00089017980011018010020800d41c1c800050007042c0690391100548940c05074088000006410035000d84815503005000d001407d28166180c3c2c0000c03105008060340c18007003035a400620061000600c201c0d0b030f014600c103280c3c520031422400025980c50610b00000c0c10080000340864100d500408203c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 423410044 1250 423408794 423408809
    0xc0708040b070308151903080313061401060314060603040b0402030c060a0f0e030703030f0f021501031a0604110327070807031502040605070f03020120090406140f010810 75
    0x12581d0b480c0c500103000c58001d03074a1410645040b00381c00d00500c1d0241c1e038012100046038602d4407080c03841d900c1c0041030300000d2820f001c800540c90000c0200b07980d4000e4542044262220041a40c1031220140440c0e80301403665500700100e81c00c02040352100001c40e81c12a40121801200c1d0340ca51000030b01e00313420075901e59000100414541f107a6a0030448032982d444072038880d68000302001c000c1c56601c44c00b520020307002400c580401c0c1c4a9502130403600b10f00008a105503003d0000c100d0107041c2c01d60b02030344102c89469025854101010700ba5002e1500207204480521000207075098003403040c00040c0a440400d46541c4000048400e88051038580310f4401c8207607003965a0b92000545c55240d176110986a5854086082c41d009601d8400c0300d0030b55041e40c8842d03041010a4441c40c421403c44c00045081d50760f40d500304031404130540040c180901c8282d0398036070380d58806020320040d00c009601084480c460f02200c60309682e182100448818020300e400120b681c2e60705520714110065600450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 423411294 1250 423410044 423410047
    0x60c060b0409080c010c05030907030308182416120b0d02030601030b0a0c050a140904020c01020d0912030b060d0f060b0a0c0b010509040b0f04080d0e0a1b05090c0708040b 75
    0x103042007400c0f000340c2402c0c140d800080100006036041075800b0300c011100d6403400d4010302c2007440040c0c0140c3c0940c3c3c111108110000d04002000c2c3c40340c0c540801c0c000c1c0c54a894416151080400c1c401c060890fa01c4500300d803541c1ca00ca142110003608030500c600c40c54003c01d031500b4a8202c140c0358200c8038800320350010215001ea503540c2c100004200b005403210400c0740d05140d860001e690048040303c031141d2482d80c03402d440400008008015800c2021800c4e48540c0801001c40901e0342400903140c0c0c030325010700c000b8122040d4a030104512510054100505061180c03a202684c1c03080169400708401e080041407004800c90301c0c4000385450707000010361010200746107a65a40c000388002d03400c1d1080c4407190983c0d0303c0310200040180704840c003d00c00314a640c0060031031002401c40f107400078411228241004031500388070050320070440101c0f40b0b50f80881034480900c880c40c400031400505210f50b2450850800c40401c09104000b05080d42000c03001603600100324014088034004c218074074260303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 423412544 1250 423411294 423411311
    0x30f10050906150a0b030402030109020904050c030d021b0d02120303090a0c0b03100605070f0c08102f130e3301020c0d0c030206190207060507030207060c060b04 71
    0x890051600765440e030075511410340010002c180c6510324804000e00200400040362400185100590004200b26015500c4164440043c5c884409080c02944a14094044038644005052808110401c1101150700a02050040b516950101402000c2c01c1d281003548070243d00214252001c0042c000f041c0e4400001005040352020404d4400a4070455203400401d81e1802207444600040d501d044042e032040b2401c01c1114004c00040022504c00c1d442ea15158406840d60300705000c6a6001d00c0040c0c01850703005142c240103100301a100b20108100c20790301c1c1c0b650340b80c0c5201001060120046964000740340004160701c480d099006083e4043c2c0f180c802d1400e141030000800c046580c500702114902d4041071041c60b50400480f05110690080100c0126142000122941c914080c0d805081c070070808009a20350800070001c50290107010f0f0b03115400060002d00d04100799000c01c0801c0f20500c0100c00090f070204145088452a24144100400b03504001006042e22f503a80c81e809403030001130 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 423413794 1250 423412544 423412573
    0xc09070809060c04031221060303030614120a0305070c150c03031b02062406070503030402190e040308100e161d014103060306151806030f 61
    0xc880c401e10088059900310b894142c80c2c0c9110780250300000707100c6501203038800801c501c40c2081c440842c503030104090300c0e4101c451488007203541d00d8209800080d210a0144078044825011324160f02084e110342410080c804291902d45040300002800c2100000303820b000d00602e1400c3c50040c0c2030080c1e02035100d0010410280c010880c0c40c00441c082030401486c00c03180c900c02010320460307081306d401806c115991400d502d1100c0c0c0c2c1481c92010005001d4580c0ca102e61900d0015141081c403800081d0742c1c900b00341c010403401c00000380c40c04a061140303400c2442001c2158030b002d500700380c0c5070818402c0e03616401d4500c040380c4000e070000c01002601000300421004a00c81243d1002c0a40e00d03181f0341031402d510599030300032150b0710190106599500c01d684500240da0b0622500002c080307400d02e16040d40340222a141021000c40c00d10079008418840c130740c98140402da8200a0440002c00040e0291022030b958070f1425840f101801c202d03030001441910140203c291020201e0b0660740d10003480c005 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 423415044 1250 423413794 423413807
    0x10050403210203091009030b0a020a0e04090804080a05070905010806090a0813030f080912030f040b09040605030a031d0616060b010201090b070c030e0d031b0c090213050102150411010e030c0907 85
    0x20603910700c216030000c101c61009d54400c481025420fa40c60080c0f646410040c80003600088070103d40c3c061041000041c400e2041c003408000c140304501074064145401c1c0c4e40c00694206070085d505680251042c00889200060200121a8800003064407460180301401c140300d05a4400303000404608100c0d4100140640103040366442142c021020038039204109a80b03014000030204549405c00c404c1c050230142c1d1020300307003510717004102150068480c40400c3c1020228142100810000021005420032070140c1031080c03281074031401d00b4043c0c500744407505a00101c030b02608059854400b215242d200390480d40c446504a54007500d1420700803001801c0c060448029000203100544012161400880410700c154060351481c64180b2403000c000344591340c030b480032940c0d210100000994a8118006400e03256450760f170502115141070006400c00c01a60182003072407911804010000755480d0404484400070328240ba4542d4230840440e140c0380b40905020b5015400d1000c01c110580e0060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 423416294 1250 423415044 423415049
    0x1f030203030f1207030504050705010c0615080102130603020a0c141903080717150603071101060603020702040606170a020a020c0409080414030d020a170f0d090210050403210203091009 81
    0x400c8590a41e109138044045900507100100540c0007460304101c40d40c407408402d46000c1c0070f8103000803550002000854414855841a4081d94010600a0400e068400c0703460042025080c20352400302c4a64005102001c2050014180741c4125604101c00308200500c0300c40050450354044040610f00380a08080d40403600e810000f0446080c1c110554611241203004401d404c0400c10300110748420001d540d0401071803081000703500702c2c2911910b80c09001c2c120041400703880059136a601030050005541c0550401810301c403100309400300c1c2c1c2102d08400c03030340700a04100040e15110503d030203c0c1007210f0b104205a0140c02c050030203081c41190300040c0100c0788900c800001d01c2c43c4590602d92034080c0e503040c910140e0400b404039004107045154420341d00280b4000940380c4102142425400e801c02028007a2031307a903802500b021070400303000c5e10880e000343d420f005040a1840d940c0c8a100b000c802e00001c150320206500303c0700e090080080c2c441c1d009006000300e502c2491070000074140201e51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 423417544 1250 423416294 423416317
    0x41e0302040510060c0206070812040308010306051509161101060605030a15060206070f09181b030218040902060d050f1909080d230a020c070f0e1f030203030f 70
    0x94081001d01d1540e0403040f0459450340c440d040484901c0d020444150000f0b40e060340c0c0594204031802d4940705424040d4802d038800c0e101c101283d41141400b0003110001031501205040c20f811040c00c45c3d8624a00c070740d1129000e003841d102000e0201040b18042d001404240c495030800d603004c1055500b000186100700a0f03200c082080e850702c05042021503003140309040140e00060302240c2000d218881c1c46007001d00d14102801101c2e515960720301812604609980110b40d20101c240f6070100365032500c003807190589004d60070420020088030b00503038900c0c2c034a071185960386402c1c0110b440c0c90050301c401c92602030f41004580740034072030391070162000c450312140390030314513160800b05180c0d1158000681d0085040b50810b01041e004000500900350b2130110035040c454480c140707000b005c0806100d03000c3c0e444003680303d65003e1820751038200d098002d0644808845018400090010b00d16a44502c5090350700d075582d0000c40d03403c90030400d01c0c4c00c040d406010004080068003801c40c010220541e10 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 423418794 1250 423417544 423417551
    0x41508030d110306060703050c070503070603051501090609061d04020c0708071a1605340605040518100b0d06180e0d030c050d050a050103050706020609100c05041e030204 75
    0x360544021280f10488005600001c140b06000c0443c2c4140007808040c8561400c44480700e44980000c1d14140b881d42c01035000a448a0410034a43e5083c10110780442003820034442c1d0f00e040c89806440011103018800403c882c80c8a00d1417261600c0da500810700e20041c004540d20f40050405a0716014a4091566107200701103001811101c0641450040d03101d103081d0700e0408040804201450141a00a0311940302e10a000d051031465203a40508550b210a1912008003510f264480700e81c100c2d610010910000707004c1045251103401044a061030b4030320000701540c5d1507803c88590407415030012081c46074041a10280645035900c041c1c152004240002282103007032041c1c43c00e50b031410510000682000c2d000001c103601a4001e0400012542091400e01d00c1c0481d05404440702100c13980345160700d07080100207000d01402200042d012a2020f0720300c61904100361a81c0b050302456a075491503840c034918000501c10400e0354040e02075014404400902c943e025054180b441c00281e216519 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 423420044 1250 423418794 423418811
    0xa0b0f010f0807060e01120204031a010302030120030609072f100e150405100e010b0a09090305190c120201150821030c090402120106030b0301090f0809041508030d 72
    0x10000c0d1201c12071320559588000c00480c0401140d45c0c0c0c1604254419881d001e00c801300001d208040c0c1c00440c400c2d0100395071490b40c0b45004240c01d6a00c0d60f50b0a1031407041a48890301220200d908803074ac40b010030754a110507922044011141d50640f007205402d042504120800c0e0b5001d02d0303400040c448241d02c104e13040366042d030401c0411560122007003100d40d07201070400001440c03241c607281da00038042d006440c01010340c44101c2060383e46542e11069240d540d9040b0204501d01a010040605180740c0100a484215600900b040c41800b403c8444054441b104051140c440c15119100542c8085844141c0e9071000c00a03000e041d001182ca8004230041d24003107035089002070454504541c03414802d40c000500e5040c610303903034005000702c082e5040c10800a86182c0391f82c0010100c1d4840035600c140c05615240d4000e04550310089030074400e9040041c484007040f280560301d5103041d04002803550754444100024028050700707003000420606040f002035042c0001c00a40411111204203110604 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 423421294 1250 423420044 423420059
    0x6130e07050a03200702010309030311040807061103120112050307051002040303020105130c091a0a06020a0201081e15180103050d020d030204030b0a0513240f18020906030a0b0f010f 80
    0x40c2c000d003a072042c469017880303860050341c42600005030340b501900b0300040b03d1045941a039030a5109420140305988400310400c01c80764011841007080e0200009141488003842d01c01e003080b60188101c44404201d0203150382480024421503d00ba0f500008440355144904290310187d0490f2105401551030407001503d81d03042e41342c910403050b030b11805184650f414220301600601c1009540210041c3c0040050150344546855001030301a54004041001c0f5610006007114802442c48a48009080c1440000010400055006505190004200302204000c2840300f00c03070008410b5050f1105000009216010800c0b54605945a00345d88501d441103c041d4282c3c4914840180700011000000f800e20345142e01890b082a02100740c0344041e4990b840d01c5002c0308004810707a0300d88400e08a1305500c01d000e0720440f203000440440c00c0c02108000044a4800c1400311006806580c81d03a0028043d95418018252300c00e40c441c10044c114203003100300400d51a424060301c90095031000d000709540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 423422544 1250 423421294 423421331
    0x3408010f050915061605160312050a050f0a1413170f1b0f0303120f011d070c380624070206040314010902180903070206130e07050a03 59
    0x9000c000880d5600f091000b042c0015540a41d0800603212019100341c00050018002203001c40c1d680492140540d082d03082c51900341e0082150b610078441c040002804042c0c02c40c0941c1c0301c1405051050391a8001c1070410317140056018550b841044000400300104c44440c1000402e0b10000b100e8080d0032040c1014040d5070b00440d2410f403e550380016a2082c0f0b0042c01d00c10503880001c0074041110010780100030070301d150441c440d010480040d81e0104270040f0300e0806124010040c100e040b031410780881c442494681c1c400b0304a4010040000803803c240268a0705002c0484005130003180c005c21003466503c80602180390501000c080480451000d19201001009001440340020050703460225005c8440c0c1c02030300200d07000741043c4000008540280b20300c1203d00d0703c85002192020081c0304025404461000380046004201d051040c034200000c20794540541c1a5540d44c1d442c0f800c002989000e640c175601032680c8910342002c11146540c003c02409030840a901c06003c0d182c84a5002c0640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 423423794 1250 423422544 423422551
    0x813080d12020f07082a0307110a03150506040b060f070c0515091c0b010905012918040e0109062009090a0c03140403020303100b030c033408010f0509 66
    0x4100040c0324640120b0020750041034040364651608031412031100042840700c0310f5890200c42a0000328042c402c1c270400d5081b80305a00c0c41265000300550071595140120402c406040c1101a520300009030740303032102d40c440b01449800508480d21034065002c1e200c071552281f0300840d00480d205400040d07504000c02441d506544018085081c98241c0701804804030385201c2c000308140484240c000440e520280d054042c04403070300003148035814001012480e00c03c1d01a103104003001c0b00240d940c2c140e1203400f0b80c0c00965000c408600120a0180020003612041c1240c40da15440d110741c040c20401c00d9030080c00c59a040d002c580300f54036260048100300b0b02072030310a90381100707244000405c01080d9a2003031816911038240001d080c925461040790b5088111030890160f44000184480d07001080002c50007060025056482c2d0b24100e00888094000608801c201c00d41411380700511030300c0c0e10024180503500c000c1c1d00003003803280e020051036000207200c0c032058109404008612410401e500c98031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 423425044 1250 423423794 423423817
    0x30610082109240d060e0903090109060305270606190303140a0c05030a0903140a0c05060d060b0a0c03090506030108030703080c0c0a11120601031e0813080d1202 71
    0x625140070203104150b1480101c041c070740100302c9036106082d0320a0f00070300322010b0a460000380c41802d0218002c04410080c01c4594558000e12445009a0740001c40c0300c19a01c9601e80401d141e159005c403100c0b030400801c000310f040c00110459400b4640c1c00038420b44190011128940c0441c2d140701603009031003980c000038000036954000d980d5010600b2004107071880320341c0703002c03c101030f5280c48050440d0440707007071400000c400724020018050355034620840d45e28888040c08400b200d5a46000d00044144252800742a000c01c43c100b4507280381d40510700524208000f03d41c1c96101c000700a001988560085000c11001e24000c1030030706240c0140ca0590f450440114681411034070299031410005240303440180c820030903048401c9040c00200d49013482040b401c152240007800300040442081040841a8410001000858604684450000220442c041088410742400e010300e2242048500c65042c00150001d42403100064640c169240307a80c0b039804141c0910243e605910845c4017416 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 423426294 1250 423425044 423425047
    0x30a0b010e090106050c030d0204120302010c08090c12160f1a040e0a18151a04021204030f0c061406040f0e2104080d050c070b030618070c020306100821 67
    0x4e8140100001e094504240040b681403e610003144001d030b901035002440c4a1001643c03420406d41c090149021105440c00c00d000c052410b0003141c2c2d0b07210130100036140314072854140c4041c802c4003403001c0d600c1c1e860551010a802902c03008960800d01d52481414a80003080c00f4964070b80688005a03401e6030340701e400d0340860fa26403200100c064840302400e900c4400c0294054030000b075217014200f4141c02080b27004200e00902d046011540c9001010700c50042e40100440060805405a619400b9505051800007240c130414115121408801d0040c0014a007a51054901d0300c801c0300f01c0e01c9902c00315024890110382005080c10349a020704200a55440260900046194081c40420030f9540d030007101e060554901c0010b08d401000c01c81d031400314400013010348a074181400200c02501d9943c00c21403540c2012404103036220401300d01300014800c18030100345100d10030780c907000b06a600142211041c0c10b04c081d00e80e008124a00c50304070f0074070814551110a01000d2a00283c0614040c070340b9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 423427544 1250 423426294 423426299
    0x60c03040b040516080d0f020313031e08040305011e230a02120f1e07092108030a0c1b17030919110102070e060d1b050d030302030a0b010e0901 63
    0xa0001d200c02400403501c80c003c480700d940c415a01c2004d0351000300381c95070003001e41010b404400f41c45202d00048400c11074000f0804080d407011a4500242102c0e803200d5501c80b100c0130004241210100e1010052903030344001400020700005412001e00b180320300040410b070148107090442201e49410034009440c00d02100d0203a0308010780c01071030348000c0c80d000140c03034000c0b0905081c102c26411100c03040d020340c90409110840d806082c0b120165400040007a9903410113060180030041d42c1d208609001914820240d501e100d000ca124000705d41c072080150f12810800104000360504601010000304601c01c1c0303840000081014078109900b080d9845104403805000e000340d584010031100b410b1107503c0f0f42041492840814249407030245412420181c4084002418080d00360720400340b01c10349409000702d50b80c03415400c0840a0380800e10904000e078101070451302082982c00b08d07601074591240d50046c507400d0340045200d51410002009020108030040d00c0b103048415100c6d8000c40380300d005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 423428794 1250 423427544 423427553
    0x801060e03100e031c05040b0a0c170402040b040204030b04031416060906061214120301050109050d02010e031b18040809010c03020c100f020c0a0321120f061502060c0304 75
    0xc3c450703082018143c900e850b14041c3c0210440980c126109103044da42c034200002d01c00a0035485c3c0d0003410b1201d0a02c510a200a80207240911409003d40340ca01040e01081c11550345074081c40d4186e4026009546595490500403010003045600394007055440051091084180c0119a00354181413418880d8402c552984030040c207440c10f048810759070750303000440c500d10700c0319000e06001c0c41941d03c10310b0040140780842c140032038184219224a010320050000daa0015400f00030754000f40c40707440c803a107400d0004031072801e1612003194060288100a490404103203c031131090003015244d00ca000c1121515051888400711809010503d00307100c9003506602c150a98030550b4005e1045a4214203041d001508094099241d1804103440338040c02c0500c0d014010084940c4048070580c0c0010315640b101001c41081c80329101080c031146c5003200425000340c0d11031030800c0a40074104000c4002c695120024585409100b1031081904511604144002202d0f88a4960f4107441400e64489655 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 423430044 1250 423428794 423428801
    0x220b19060506040f150507020a120f0b0106050c0d0203190503041401231602060a0c090f1205060603030a0c110609030610061803200105070503070807030801060e0310 73
    0x461046554a8880016281da505005000a0f01d03020621080080c5004208082c0003801e48608080c0241030045002581d0742c03401140c1100c11b400c03000c5052030b0032880c0c1500c89480300c1000510003e90400041a040e40c003402a10507080a4821140c10f0110040140e03178a0040f00717000315040008480000c00a0b01c994090341d0000c0c49024120f4884083c0b510680c02d5480400020f50440300001140f8000301d44111040d0304120034401c1034540420320b0384000d4072401d00603c060a000c0d2956400d2404900c82c009003002003402c00300014405803602c24400c04012256001e0b1030600c14480852003518021044541c004000d4032441c81121081d40e40801107415812502c1d8400700611803007020340c90078002c4612034280300100c42c20490030000c000d011462508528007015807403620030b03c0050440c0500403d4640328807a10403044000c20f004a40b51300c030718000208580004a403070310030000e80c0780251501a2081e100d0b510681e0f22500d080b68000200d04009034150311071400e042403070344c0542c03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 423431294 1250 423430044 423430081
    0x2106081b0a030b0f2205030d0e10060303080103060509070e0a0c03020d0f0504050f060c0702040e07080706050d0f0c0509060306240a031802100819090308220b 70
    0x50038051416520340343c2c40e41c0050100d8090340750012070303800c03c48000d9a043c00360b0240c940000c15110b81c1d0303080e40c40b41983c0f409403031809258075503280010385243c0c9040040307443c41440b0314014001c1c6901c0b46402060503c01b0722040f1903140c11303d00491020700c8041180d4040d240c1280d02e81c1020b035652004d00d03028000001219041c1a420030042c460140c850003142907951144502144604040c50940d01d00305c61040e5036800364004000344402740700311101305c40400750100c0d808151350544c600254284001903200160601c1224000201c4e56086800f9080c0a0010081001244800c003024001d80b06004c50400024108200203041d902e4941c02842d000780010780b0802c19100350440c240c46011041616920299001c02c000758040c7d0316004a6881032114201c0c12110ba5840c0d0206074a042c90101c420280001d101c0003c8100300c09503501e02c1c5040301c03200d00b03001000780c501f800f609044040e0707240c0350a049404068035104890058408100b0340c01440f00c0041da0b07038126041b03182c1c0c8502 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 423432544 1250 423431294 423431299
    0x2041505030c0705060c0a02101104090b03150a15060e10081e010b04090608010b0d06050405031e030709080309090a0b03120c33040618060c2106081b 66
    0xf404800041201048003d1140b030f001108540c1e1164240d074040d10f0081284924421903040000c003a00314805681035808892110401180003000031700002c2c104600d500700c8800c150444810401c00054079000010340c03040140f241414603803604030450340d00300c808a2440c4c11180e04083c4841041c071403400140e1192102002c20300e440000304051081c11001c0c1d01000074084007180038031030690680300311001003142c40000c00c00b20102d80f006c507500030542e0300c016000c0ca0351f80340007406000040c4100d130300c018806c1d105a00520007144419215420682d44080001d03030700007001c1a0904004101e44502c080186402120340d203107640103001c1c0c580f0300e00c003c0d05030080c1f120509e44001000050007004000070090700e16881c2040f40c601c1100c0d2182491821071251034103001062020141d0a80c101d5005040810002c0c100390a0241d042d4100780000d240b42e240044045090303a00c92400c1221141000055082014896540c1c05560507030040c004c01c0c4d0000441765604024440343d1051000c8007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 423433794 1250 423432544 423432547
    0x90402010309051b030d050c0601090c0509060d052403031b160b041502031c0b0607020a09140f060a0603090213050c040f12081801170a0e01050a02041505030c 70
    0xa5035810f410494414031105020b50b62904400d111716051000746820380940c500b29081148854041d980d4990600c60f103081c0550700c8659040c80c610400c101c4032400400361200da41d83c56404400c50040c03c085403030080341c00001645c006466900c80e2410100d0100500039070a00e4818036001c1d02e00c3c0035603d008007161207100282c4044543c454032050041c03e00b0742d150380c1c581d407400e603210003480d054610100c110b4008210102c04c00c1c55607410481080d43c051000140d111451011407001c2c4155074001e5440b451541000075010f499030494250080341790901c0a440d20780306414103e24005442d0594403c1801d41c09100315882644800c1403e40024080403e024401000380f049171410b40c0c5140c014031000406204c9400008200c00062018003403c240048058441022600402d040303d40791550741c1161145a80c80f0380ca10901100f140703081d01d00076040228180d001040d40000d181c1040d400e2200080240485100795411991001e03110755070f41500f101c0031201c60740000c2540c203c0f80390 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 423435044 1250 423433794 423433811
    0x207021305150a060e010e0306010609030b09030408100c1128110409060204170309010203030c0a110d0e030c090402030705040908070c080601260705060c01060503300c06060904020103 81
    0x480d03141e0b0320f0080c50261078000e02801c900000401000341c441007a03020798040341c010000c1d6a80300d94181b08032a000040804151140f010340d078250303c41c076880351825105031980d45a4450580d8040e0241d000700341c40342031807450701202d46034880c02d480002c01480e05200c83c0800381c1d2445644c0042c12640705e0290310180300c01c0400020100e41001105407080765002c02d082c4400c1064045a04840794044001c60800c1042e60000b50749100051a583c20b040e4041100030b2014080c060064290285ca400d8945107a0004c200030220b51140d101c0510034440d0000a41d00c3d42400ea59060040360040c0103456100c4c2045c0510010389840001111081000c04c200e5020624045403400500036582c0607001c55403610200140703450450800035188100c0138800042510002444000c8540555030760b81c41c4c1c1070003400c142c0103220f01c2d07100f190507005c1e42100342c10000803840c2c00c016240d4480d090080c2d241d01801c440303602c3e000ea0300d2204220380c4684042440da2411441081d40a80305140c0400c000781e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 423436294 1250 423435044 423435049
    0x10e0a061802030303040f05060105030f06072303040f1119150e06040305060601030c050918040311031305040501090c02030f07020f0604090507020c0616031b060c02030418020702130515 82
    0x6104646c16035072400755608070403c01c0000d000c018010300c0c0441c0200b45500700056210b46442015001d54203004941c0d0b0302c00d40607000c1d008030407080d000701c08155440e881e050504500780e44140000716254410180c151805107424040e83d11404031606489480074140211030124030013140250050105210854459666001c01000594460400b4028034201140090191080c1c03850302410301005124200d16506c035a00742d2003c491002c01108400d498506060b82c0d410107086d03042089000000d050241568900d41110849405950422103603980f0b10100c401c840a54207080b0044c0c00c2001040c0c0f103203801d0000b0f46242e90000300001c141400603400200703180c5c40381c2c0c4114074240c0c64400b00030034070f9014081c90f0300701542070712120302d00810180c400607080d56010000741031040f0380e1000300c0001a0343d0403134528181d000e602000301c0300074250302a69075041442080171310701000d014844d03000c0c164002d9402c1c0d140c0c00340c18882c9403680141688043d0600600708406603214000c0f44100382e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 423437544 1250 423436294 423436297
    0x6091805040c0b0a090905010f140f0a05100512090c010207180e0106060903022812050109060e0606030d03020712140d05010e070e04060b040501030207080c060106051308010e0a0618020303 83
    0x800e25858170000070f45001200829140140d000810700a2441c40c20048502d10403032003c400042150003848091500000031506400d507041141c1080f0030000a42e5450f400c08003c081c495071659006040e0355400391403503034a56102900c0e5005811000c2d080002e802c0c1e01100e44d01d00a11000c4c04200c48a42030480c44c00c407401d50780b010000905d5540c0030015418035080c1d1181044c40900c0d80c5080b10008001141c029105100d000d08040d0f6072185201801070a520002c1c030aa84a0400d01c0007500070400b29a6594040e00c140740301c0e008165034240b101d4040d1080700d803155800800c451030ba0044903400c1c0c58098000d0382148241104106210000560f8414140030700300039030741c25100b414580c00061099624121541c012032034120103002d02001041600c0c1200d10074a400340c0e41d14294030749040300740117283c0150a6845290b00202c0d08640001c09003402c150050607210013a40c3d1040c0c030070f00342d84901038010701640100c42003a02188040c0c1200010703045410110755200c00d01e5000c03a165 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 423438794 1250 423437544 423437557
    0xf050a03030f0501120c140d1e061b0e0409020a05040e010e0c040204140913080c060403030510050d230d0305190b0a06030209040b0901061806091805040c0b 69
    0x10380e5445900a0b040b010f0b01ca11409403c402c1c2280701d240a2560316004010410700030300c41c4401400c1010940daa0700c0071010b1804030b50045621661a03400c80e6458a9008108001c41e525418442108895a000e810140c840451680d556116060403402d00c0001c101520080c0d801c010550380c0410f0030340b00d40c010080c1c0d002d000300000a18039604000941030142d00c0c66214812401000104000f14150030b84010000040302e40500d80d0700d0303501d01645107000c9400d00070011361002c2001114110b010030660301c624000c0d1010f10050307444180b01d03000a0128040c195120004030400e00204144810304201000d44031600e8504c0414003001c5454440c19488020000f62070303400301710344100e84800f002c500c4042041d041c13290741040350001d000d00c2900c2c0103c00c100740d404140b5480650303403a0420800030601a00b403090704d503150f401c010722000a180d801c1400030004a000103e0901c242c0b044801c0701d2407001010b01c045180b0b030594029003c0a44240c41884111402040f40044140202103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 423440044 1250 423438794 423438797
    0x912020307030e0f1011030702100503090c09010b040e040203011127030609030a080a15180513050d050a020a021c1b140f0103020d0c030f18021c0f050a03 68
    0x100d84000d8a0b0003022aa0784410250007a0943c15098a554a40d2408148040c5c05403d05040300c2c06000891482c501a000c0069803280300c200c682e074041500100110301070320840082d21030000d601024000070640c00c1c8280080c481041004010310a951014150030601c020f0012400702184000001113801c1004828441c040c40c2c018201031032981c0e01e10b0800254183d0290000d4504000d82030303240d008400e8407405101700c110008021100c20380c440000d42511110005d8444e0720340c07044c410799088028400c41950302e0700000c076500d540e0302d41c1c180040b030f40d200c0014030265031180b10494080d0004501e103001c0d48544c02004005035241888086045019003920001d000c05092190043c54041100c0710154503454040c461035010b600c1044010105071091b036075140e05d110040380280b1812410501d07403450201100c00c0ca03541a080101c2143c85c07108103104546112340352600c0b420150348000d5001c141c01480c0929900140030301603d240c080d5006007411a0544c4a042c00c1c0f058400c3c0c00c60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 423441294 1250 423440044 423440047
    0x10306050a0c0c0209040f0c090e011e0b031b0103060302060d051b12060603070c150c120614040e030c07080c010909060602150c0d06030609060c02030708070f020409120203 76
    0x10842646108142020181e807420300840c203402d4000c2402818040c00c09040100410308810a1142c0d9259141c000c001002d81000350945107160385008010624040c45030680b03050340d142a03a2001d00946058142c018060910fc68451090380b000c40c0700980c92505143d1100790010159550300054040240032900110f10f5150803189020040c1803101882101d1030280810002e550001c50300c141e00107000e42c2c4032907480e19003200913241c2584051004000348203681090041160640007002264156198000c656401d01050402e4030038500500003140042c0c50000035515045d08a544418070090641e031500417480282420040b0302c1d00400c81550000300541d0071940c1c406603180c0104100281080081d00f0860001d455004a456400600c0c1c042c80c0480e401c10490f500322444004010000c10030300340d0ba4507024001d46201401a2440c0e45000c0307003420413034008801c54002651101c030740351600056a03a000020151904140d030015600c00c400c800140c4142c500b154030f0400c940055 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 423442544 1250 423441294 423441301
    0x501020315091308071a130209060a1401080c0c0307030807080603011802100e040606111b03061902071a040204051605030c0903190303020a1107060507151401030605 73
    0x2001c8204a008006008880c001c040010000c00841100f0025600502c203666401580c1004e04880c1140e2021000540b400c205124252909024181e2502c0c400c2d9003440301035860604001c1050441e102d4100c0481091091440e59071080d03400070b600c0200700101c0e83c10101c001202500d035412510301200800d80c8103041c040303002c3d008810b41d640a68110300a0090b4154104100b12080d0700c414001d0064251140f020081409800807204881c005041049010340d03a41005040075212400007d8901903116041842c1d10b1409a804681401900800050b1601e0039803202c20100c002014281c1035007030007014002a4601091442040c50404107400c0c0c1c00d0500410085400141001c0340d40c00716071403c480a5a00001520703030010700b1020243d100d02c907200100e41024442c1180144202c0036803290320030140c06501422000c03031303540d40300400200c2e5030b50388a5691519000d0200420001c0c00360754001072039074651890300072400c0700110394520000d0502903080c07401c6e00104d518540381c5082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 423443794 1250 423442544 423442561
    0xc06040602090901091503020607021f050a1107121106070602280c051b0409051009050105010e0907151704050c03010b030a02060403060c0306081203010e060d120e010201060b040305010203 83
    0x211405842490b05c00c0003042080c41c0b44101400b0b070307848000c0c089d071004150502550f8800b02c241100c50f90494440c3e0081c41e45000041c0643d110304020408511083c507040074090300001d144045c0c2d8510b0101c00b0030000d450322240c0e041481c20f010700780e000404100705000548580050211814006405601640d401e481c030b01c10008a040150101321488900350041400050340d1031030000b506003041c502500740c001081c048d1000c0d1001610703a1007400c07100b20740c54160381d11611040c0d0091000b0070441e40c847c9800803e183e41603804800c0742d40f08070b00520000034940031500c510460ba05015032000d20000c141417041070210340c141c95030340249581e8015400c082c01080d1040e1000c170040e242c0601664001441d5000f1804081d105075942c9072000780b2903010350300c580054400b000c00c41c4c801a40400e4030214551003401240c00c80e40c031420115a20b82000c025110031542d0044d4501d80301d16044404480c0240880c0310b4504564950200184428024000708040e5000b003001603921b141c10500c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 423445044 1250 423443794 423443809
    0x504111909030c17150c04050612010918230a020904110406090501050618030c18041106040302011704020a0b0309031312050304121106031e070201051909080c0604060209 75
    0x100030031010102d0500c140c0c001e40400c1117588822030328440030301c94544022a5116001350341040390820400900284120031003400039040340c4409000380911741300768104012604036110000c014036001d081c000e41c1c6600c0b03c028880c078510714200f2103208907803540001c1d550020507031302035480e280c0901e4041d59a061500030440984050242440395500d0030000c50003510032800f0051014543d00f0f0307061039a80c0c05010095541400405c10707600000884460104007000340c03021244012000c05080841c28007006a40450b50140c4506007403a10700e01c0401841640240100c0e40089910408a52013240d500614000e40031540150b40710a58000c108a4071803040c1c0048105490081c103910009000104131b509482c150310380e400b84854030f46040361070f4201040e0410b600c884044200b114844000c40f8889035285540d820032600d484d0908260b00320b450a944000d20340c20100c107a15039051070350304a62140c3c0c0c4240115881c00d10110b0f884d90a054060f14204c41039600040c0da100d8902c4d00d0032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 423446294 1250 423445044 423445049
    0x21207080103020a0b0a111507171509061c0302061e040f0212030d0c0f080a0c09030818090c0a1709100b0f0d030f0206150a0504111909030c 62
    0xd0100d80c95046400160120180c0e00c40e03018180000100d00f601e4034440d405480407200725000f2a0385101c116401d40d0310415044a40340000364489004144d00e0b210544401d01030038000b4500c060500001d400c2c07044038600182401c0d000750010314140c510b9105806040541c80c040c4d406801d03107041042000402d2030546590700808402c3e2000d0001042e08009460141a81118908051200c0749251401d5005013221410051318003511600d2071504481042c4101c40e640c1c1d0342000542c0d401105104440013a040840012188030301840080c81a230020403442ca444408904140c035444005000703d070044660b150505004110521400d8014004001c021802c0820300403926123000d906a0b1111000661040940c60341c040a420b9202c010101c0d01c0c420000e072810341c0440403800d0143c18450b0b041e05402c01481820005292020404508042204003e08424606146c2810080a029100300f410480c550404c1440f10000c0707070000c403c00002090b21107004080c0765003032248490f00b141c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 423447544 1250 423446294 423446297
    0x50a09031407140a0509181608061e0f0601110111040f08010608030405060a1d12060f070302090a0506030a0f0504050a2105071407080610050301060b120106050a0309080d021207 78
    0xc6000b448107540b2010401da0001f002c9000d10562004c0402d40c510302012030f522080c00c3c0110030804503205c1004240507104403c1c0c5100341420b240403010022141004513100310a000317078080451900c0d88210118401c10224000120320815840d90141c01942b003035000c2c0031489103c02041010301000e01030b020040c01480301949c2010701e0240401e5903841155020810032800e0801c4040000380d50118548080003d8101e0101504c03216440d0f644d80b07816108180c407451044001141c1e28401d008694541c00068800300070f5034a00f6043c400540c0001c3c0c010308900d9158071070341244100c14441c1a214501403002001c0ba0417050030466100900650700268860303558000320030542d0040215407134241d2000c0c00d04c1070301c911221103600b0a42036130880c040d1806a042808540713950707692004141c400803002080030300e41d6003003413080600c03c5021200400c410b10b0010055940030f6000380017500158203010031803400c561b80c0c031203061f0b100c1ca269004559000c120442e4000480f141184e214429 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 423448794 1250 423447544 423447559
    0x1210f060f050a090b031f0e1209090a050403090611010e0604030504030b100605090f040b04050c0408010c08060a151101020703021011070f020420070b01060f090b0901050a0903140714 81
    0x140e1700440d0311900301c00c7e0001801c03100091507502940880d402040b45141402c1507903490350750184446100c8e401507070218800d00102d404170b94001801e205850040343d1646950b4800c501e4010240c84020075003100f044203558805c40c90303140341014080a84a14802d80d035040da500e080d85018258580050300050a104004400f071260a410004a95250300d0495091304c0a501210000b800761010540f1545c2160800041c07100100b0144007410944000c60020302002078481811110160b0031240c0541c07102d01d071007080001301125804040ea9044600d400d404400c542c3c40320500303903032100c85d00700d005a126140b1049400c1540c82980c11181c03200140500d8034015484840c06030a0b0b12201030301c00d42da40d142007502c11092030112004403080c840d04688640c0030b030900d0400c00c4c400740710300408a6500300d0401d0041d403040c80304031f0a0b101c0c499140b50a20540724011603140d0440d042800a202c2e400b81c0100101350340c95480c00b500c807c06c0b0000c08880f81425010b024026000ba03489000313001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 423450044 1250 423448794 423448811
    0x3140c0412020a03050109110f060702030a0803041106030103080a1403160e03100618060504020901090312091a0c010e1c08130606030f1a01030201210f060f050a09 72
    0x204840c22a401881c840828520900004400040e0355000070059803800c903002c001c00c004540d001c903c0e04012545c01280540441c14040d40b03225440e070003503040e00505803500000350100d000e150402c0c003d1503920030f00d54508000c43e005503c03e800644041a01080c205c03030503907126407044220503000304580e0440c1800c04d07124046c1901c18155500717102d9050f5502105880800503c5e1442c04041800c1c8031156030b9124201e0740b0440e000034003112a0070300d800483d050500703000300d80018806943d0400c08038a0358035200d03120301c0e10744d0a1030100001040700140b07007000003803460303441c9004482d803036a680e24041145007100c000146001082e0440780040307000e440910a2013883c2c7e10141412009039032070803c5142c0850080c00f00412040c40d001010050128107003000c144684030b034001192a5000303940b240d003024800d1000900082c85400c441c48039600d21202c2100350b00056402144600d8001c1c9002d081c0c03252508810080d48601d1020011458407941e40c600034908038000300190107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 423451294 1250 423450044 423450061
    0x6020310030b18010e28170a091a0a0c15090b1512120a0f05040317220b03060d1a04140d050f030105060702030a0803240414360d0314 59
    0x10032006d0148010382c2089401d8003800913099140c0c0e042025102e450755125122078003d45409400e000e101c405145041a01c00c06400704012900f0001c101d4403190384074541a9900700e10701000a40ea002e220740c440c03103101c000648000081d030158960075540c0c0070146008003801075803003e40591807070590040480d80c0ca80074541085800e40701a03460178040940704070700c055406d44100d600007000c0f0070400b00350f0a0800200c001400c0501c2c41c421450602d10002185810202503030f021f4005034071010404140d49142170b1144040c0c4a1050201540d00510ba201041ea80c1c0b10448099845410102c86c410400f001486201c01c0c030401400c25908148031003e55600c03c0c0414090b45004a81c002656429035904008a07036519502c201000d983c2c1c80c00c484035031028600c0d00e1110001588003186c010103441c0900641c10034100044003000c050b0340d004100e091816400000c034550012107040c0200c00b05071079078204564440b002c01011103411000e00203046440e08440107000c4080b010a011500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 423452544 1250 423451294 423451333
    0xf05070203031e0a06030c090218311103090a0506130305030402120a0b01091a0a0e04030c0303110a091a030f010b030702100e0a0201030608010507020a06020310030b18010e 76
    0x1842c559501c00f001341e4809075400003c00342d0307410203890104054000991031000b600200601d45620200410000c20002404540c10010f85140218031100320001d51441c4d13140402c0798000043d06001c141101600f0204080354000d9031004100c0d0018030500c81070090402c40d458101d540e816499200365000e850041950201420080c410460140082d01c44401000400045900a034000c2d9955a6449098005150440b04600d019168503840d030309502d44482c0c08411205c11a602c1140c0c1c0c0d4680ea400c03a90303105005012400c0c160b031500c40072200f8809402400c0e683c441a101c1e010a181488002046103035111401d805190080040000040034845514111220440031986a03140c10505906100000c0d510a810f11f01e80104590603500001c0c2031100d4500030703201002540d444111701802d8070b00c02c40d00c010150303015504510020f03009500965020030503404201c40f90361131b1b0b40c0322018071409880c1c0b04c02c8a80c005503130f12800c0350b00380314121a03800c00000a2000780c0302000301c0c43c0038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 423453794 1250 423452544 423452581
    0x50d080c0307020316030b07140403060506030f160306050a0228020f0d030911030a11100c0204020c03030708090703110108060f0409080319110306040207150f0f0507020303 76
    0x8168011408610940c82003040e2080c56500609071800c03800600c1d4501980080b520007601c07004d000b0004900028003070f040c160b44c402d07541d40115180500755201c5801400d400b411068041c49000f401c1708030b01e0800e1184d010680c0481042c20300b49841c41c201070040d140090100c0500700d10402403101240c51504202c0545412107080d40d4010700501c02c20ba06280d09046025564020210701c20001541a802540064031400100405130100018590746202c03c400007800324405103611030685c42c045c050208107141034500303c885c00400d03a000c1740c2680c2000325044100d500103c1444449a00203503500e43c8007501c4001001c0282c50358440c081c0e28000c1021060600410070085002900e81400c050840d490240080c40418081c1ca8030300d4650b882150700b091410141c0d8044500007456010720012181d40c0220706007181c0752101000003c4d84130240403a185c49144580154042590141d07148451201100203401c8207415000c1c0155000100f5031411908104200941c261301c01040020 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 423455044 1250 423453794 423453803
    0xd1107031106070c0f03031d0102061f0f0305070609080d0806060f12090d121a0609040e0f240f150301110705030702041503020a031506230306070801050d 68
    0x44001615010030030b50b01c2103100160a01d603484a020035007100c0b00c40320f07170100c0e4400d41e030f00781500c41e0020000380c2d4007400d0a443c40c01600300c1c4005c00c10348506c03000309001d05803000039900318040e9100458010b8003510750007152540c011900420520340c021140d80024142c101c0608421801d0401c018000140101642d01c034040101d1891003a00211040c0d90050340c0c4000340108031b0400799901030340c03210000001e900003095414001007141d05805519090700302031000480d882000c000b04003041e040942e405411564a20080010490401c00c40c0e00100c0f102014206002105441d404040d040d102130741c241160020038048501d03803ea108943c0300510f16042801c1c5480c980020740505204114110100e5012507002c09000010000b481d08904c22601003080e000860783d00d203811a200d00c03010750300030091070041000c00d1410500140b0490714002c0003410f2a15400c40407440040c001217031180e05091520f08420381410009180c0100060802510941c5004005080041401130092 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 423456294 1250 423455044 423455063
    0x170705030c04090e0a060515060703080a02091c0312110306060a1403010609050112111204081e09182206020409050c030f0a29180a020c0d110703 64
    0x4100065180942d006852680b50600032000e03880c9113259a01d215101c2030f55034500d00130111300080021030000207080006048141001500d4a080c0d884d44001800c2c4030800d60208000341044c4c4c1c0e030090150301e190b0703688032680c600901400c004004000c10308140d050f241c40c200351070161001d5101907d901c42c03000c84000d0740d070310021a01140e4410b40480313008544a001b01c00811015001001300d42640c5080c0d0b100121220007603402d0043c1c8400c01c042c5105003200b0000150441102c00340185d10a000e10446884c015a1030f0080c41205040489aa81c0e901c2c0800c403074900349020707a01d810ba440102100580c0a082400440500c100701c1d070860b00700e0700d6801d0580f008016898040da03000f848010010022850300c56800007240d841110070452002c1518002003810702a881070305c03081c5c402c0f00760003a259402440114034880343d810345683c0c046180300a06948254031100c95101d032a031660056140e0080f4050580381c4124581c0170404c0c0f00910030010303500c1c000020b00500702c90b007002142 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 423457544 1250 423456294 423456301
    0x70e01030605030c01112b1d030a20030703050f1b09130812132003060c0a090e0f010503120a0e040b04020c030304050a0606050d02010806040911090a0c020c06180d050715080103021017070503 84
    0x142c2c020300034032f48003901809449000400e00c000030074507004104000080d9052496801c0300b03141a6a40c602e0b407540e01055038004a00200b40074070303182590b50700c1005110325140d000d0314000f0760032000302c07050360f07001000c580d04104210401102c1d5205101307a941441101485c640000c1d101c000050081e00c0b40000401d2050042c2c0c81103901c0740c020141c80524151b03604144001c1e9108c45c000b4081c643c00b070711608408030880540c25007261051807041e500c001c8203080700ea0401c0080c2c0480c11038503500c07075000d000b8600c030400d00340011400755126000515103003440d880d20b401541d10540c132070761040705c40c0420748000d030342c2060025601803400c03130340010554102e18201c03070843c8031021110b0b0020540001c001c0c014107607500040c12019181c0885102507640c104000b920312541000c1d004e161035000500c03804c0d08100c03c25101d240c1c456002c0e2203c00303450340340582250821514400005810200400660610b09000074102d0340314070742106581d142c6002010042c01c003801c030b00708001000000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 423458794 1250 423457544 423457583
    0xd030c050c1e100608010e070602060103031407031814010e04020301080304170109050f03031b030705160309030512040f0807030305310e070e01030605030c01112b1d030a 75
    0x280c0f0804002d00c1004c01081d0340341c0500c18000d0100210301d503100d00c905400426064000110241240c1d89545c68550070700005554140039007241c0021014444061070b900b524541d00d082540c06060701200001c1c0302d60000d000107100d14040507015020b144104010310100b4404030031541a00c00c0304030141541d00050480d18014100842c01600c40c1c0185085110100c4002c40114003814101c04880d01200b004401c0300040c0c4004d0b00c03007601044040010091140080e00e58003c02c2d4080d040c000c520955070703224103051141784081b60341d00080000d004e1010715604a032080203001c0040c0181041401c40d500a0001c0c0f0503401e007003400401600ba148118080030005428a80c01907440105e210f0399000710190803441962805d012410b04041d800c5554841d1140008a44005006103011580325005649010340740740c6107d01070040c800c048124012641c00220407548200d0765102c07d2000400041211800d422020494103410f01c01040681e0001030b4040320301c7c6c00500e1403050b503406961 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 423460044 1250 423458794 423458803
    0x5010e040921020c011e021e0f0708060a0e1b06030c070c06020d081e190f02030907210c0302130b090a05060f0d0317070504170d030c050c1e 62
    0x207108044500002409a003a68042114040b00130700fa226441808400700c00d500d141112681c41c0801a805400651880a9400e540310b0303510f030071002034440c134102c01e0043c1c0341006855001000d41e03a106206001c80b8030a1445a4022345403142c1c0079015001d80791214603280500d034444184101e038003002041102110745c0c21280000c0d488101c00d00c10701d59411001e5120032143c801c20000c900301c14006000700c6010000e0300001005410303c4411940e4900082e0304078505010303010b00107940e861101012120501c025401541c0700300040814525200100014160704034078144d580503000b5503000024407107140c40b410342e5811500c1c1c2144941000d40d400c01800081034265024481d40305001c3e001c001030303004900805040e03400c030300c000c00c0c0d100c1445161345103400b00400090078142d0040802d20060441504920302d403401d9458107030f4800c84030a007507a0f21514140071340c00c61442c0340f50301c9030140300b8030010f041079007046401d25008824050b1208502a14106030624005200d040030a042c003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 423461294 1250 423460044 423460073
    0x1051e1003020c03030403091a0c101a0a0b040509100f090c03020729071d010810030f0305030a1a0a05060d061a130503030903072102040906020a0201050a0605010e0409 74
    0x20f007200e480746001d0074003c7c410f0005120701b004156034040700211441c1760008030383d04090800000c1c4003400c40525844000d0030400040250001c00c40c40f00c6d02e00c1d0740c803d0013101c020110394000507140e606140401c0410080500040c0140c102c00c041000300d80402e501c035400b00e0b01e810714000f908205c0c80d00264044d2140b00c8000b400c01038a14070f401051484503c0d0030300c4a4041111141044e62810b00c140c54a10300201144440039503914039a010790300c2111a1a840308202c5a0004403c0d07480d500d00700461500001280424008010010000c065103c1c0da0300140d00c01c04c0d9445da403410f040204045903680c0c0296400b801c00014441c0008284c0d401a000424441d00c0881199540c2c00da00443c1c1c2c1c000c9400c8103a010300b22040024145000419143d200b030008000d0400d440c5094103e540d5032688044062000f580e4200d04009070780c0d07900c20303101114007460015a40e6420590001c0c2154802418000d509290110a00869034020b820070054030003900e000072a01c40394107105401e421804c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 423462544 1250 423461294 423461317
    0x30602040b040612270c08030307020606010f030b06030408030c120c0c010c090e01151b03053a05070905041107060b090103170f070602030a050f01051e100302 70
    0x100050710060140081048450558609211007600440c0d01d0684041d045600c00c0410b19104114140c0310103510740030442c0c8111500c0c0e039a10366400705a400c1d508111078007400360300b01800701f0100356005415945c09030094036041291880880018545000151000c0c200f2030380440001c0d42404410115044088071901e4800245403090301f2102546c013849129109d5420700700c80500d124013030300c569410b072071110094451300e03803e0030000107d0f140542c07150010407880c400d01007581012820040071550113541d40e03603a904c01100c000c0340617a0340c10f9021004602101c0d908860081d82180321403040b075166802040719250741100f15034010650702312036489442d040b980112282c541000301910303032040e203081c0002600f420801c215400d0910010b080c2500e06507048500f40540d900800741032281011144c05d1601070349620301241c204a4032101015071f9141400f0a40d40c01035030392070061000311940f507403040042c408030300c0d03070a1092034950140303440e012491042800303030b0107480b0810340a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 423463794 1250 423462544 423462547
    0x403060b030604050706450b12011203021609060504051605090f1f02030409050610050a0c0c0b030118061707031e0803070815100c03080604060f08010f0b09010807060503040c030602 80
    0x8002a2012110b01650207c00d4601c4803d0001003001c04203094034114002d1100550440e80f070a950300c100c6401c505005c80850241020b200804150114407501501c0e821030000354050400d0184811150302901205102d4622041000a141d021044814020b402d40703075800c98108000c0403d103030300010b070a80303182d8602c418582d540159000010b0300807560034900c10300080d280c3e4024403c8a41c1c1d00090403001803c100800100f280c050040302102900c1184040705190b9203541c0d214160708282c12081980c43c09c142d03003401c07500043c007540c40070342040d050b517050b0030241f6421103640c0c207100c2c84000d00810a440c0213a03588154095481280c50304040002d40e80d160115000305490ba0031940c40c20391182c8042c80140c01d04089000042c480125214001110629182503580c1000203001aa22a85480e40480c1408045100303d0040400c84000704044010500450581c2c0da0120058043c181e0030004204412002541c0401c550140c105140d40c6c0d01e4a0a007070301c101071641c00107030906e0700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 423465044 1250 423463794 423463877
    0x60409090c05090a0c0207090c05031f0513060303080702120d1503120e100905090c03062701050a06080f04081c020304110a060513052809020403060b030604050706 72
    0x142c0c2c005c500c00e803143d81d0a43d44016240c9041d403048902d14040c4500044040c000100c0402d01c4100d0140c02480d00384d101e055840c1c0d18000070341c43d0bd008003440d00003123845507010020142c00200d0150803900c0c034000b03030810b114015055980307030249409076a5520303290011000740e410752405003c051a000004e0b141c0726075003008007410703e125800f0721a0180c0d0204034602a8644152410010740b40024034641840e180c0c0d003c900c005800203400f1551140107441240381e03140d00241910782e00c0e10590b000d00743c4c3e50724040400000b200954001c0d400d1207811410015003200e10700c509a40181c2c4503030750702d842d2a003100002c0800c00d00130b80c480c114030f440081480b09003d401101e101e80044103c841100194440c1000c841e02c0c0070f04050070780781401c20030040c8010315090040f120780c188441000d10780403460030b144d190101e482d0b84c88408880d60014003481030103114041c4640a11040d0014800c5003820341d581a9503034035521034141042580d15001400300c0c080701d0300f0480300c500351500081d0302d035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 423466294 1250 423465044 423465061
    0x1032304140601150e040b0a0b0a02070e07050405151e0408030c0c0f131a040914010e0a05030d0203040c0302121b1219021314150d02060409090c0509 66
    0x103610320407020207114010001803011682c80c10050240ea0300c0d0780741004692510148400b070901c46601942c0a8544000403454000300070140c4a20489540103084a82c9015182d500700103000e00300c0000c104003080300713100c60385524610464004441c400aa5100512030344441c41356110001d205143e48005800242440004080c0542554030780c01c1e00d1104d603414080100070482e048880e60800c40d500c1c130074003040d00b155010100c8100e040c0115000c501c0310400040c1181e01e0810b04a80760010030140d0140002c00b44500440384a460740142407442054586c03a0792401528220200180c0000006081005201121000b1a0302030300c1202200c10000362103480300c0360044080092818560449024a809004003400ba1048800f4105d4a2110091001031038507801c010b0b6002503100403144041c0c001e038400c4003e03003914400140c0360350074095800c145441507030b5051481240441152009039440c42c1c202e4044684000700010340110a04d0701400d00da40c00c0d80944c0d441640d07030041100d41e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 423467544 1250 423466294 423466313
    0x160609030b0f01060e09070e10022506170a02040801090606080625030c020c0a030b0f0a05010e07030207050c0405092d060705130305070f0501090e06090601032304 72
    0x2244600d00718005030340c1e00c1d41d04540c0c9610901c42e80d400920760343e80d40c0201c1e042286250381c110701140b40260000c0508004035004081c0e221507180140d000c824014410344000d100300c40000e44054981e09010702c2c002c0010100030b010f010071070322f10742d05601003281a1031590448008200c03002c02800f0040c2a1306011001703200314030515569018540000c0c010300c0c41140890700b458880b400d5031003242e4800c94224001c001000e102c8095101d00d9000d421583d035400c00683c002c500c0b9901981051074840c0d00c00e99144070103800442490308040050183e511081c50150740188646001600ea08c07003824503a18000c070b024589030b00300b840e020510103401c4002c610100c0f406075201061140c1c0c0b040e20711403940110252001c0a141e040b500104107028400c400a040d03005404040041407512600e990b401e001c02c5502a5007000740040080049503040703246c7d100148070303030043e003543c1d4609100429142640100b820b030405940d880c1180c00c0070a01e451100d04444404000840e40c0b5007442c0c542c252 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 423468794 1250 423467544 423467549
    0xa0b040c0303030b0301020c120904021b010906180c030209070e09100f0b0c03040e0c0c0706030b0910080a03080a0e030a03052203200a1208040308071409090405160609 74
    0xf90801c007040140341814003c903001d90060000a07c2e4102c000352104403942c108107042a0f1140c0c0800c0b0011644140656448000b1041000040c0da034841b0f1909000300c901181803914520411a200c2c03003c00c41010645d0704981d01518041d40c0b40c0c1e030301002104e6078041c060f903607130340249864103001e040c44000703608405a0b007540c051021030513100c80f210f100ca40036813060710703c0c550b000f04401c0c851000002d5046401113005000340c2d0400309010552420050380e0341184002a41d81e4032040c40501d0320584680c0c1080c661100340c1300f86070900c0d5946481e801200390150500c488000802d150300c01a9200880b00008542901d0310f505100600401500003640d50140c8600721810000005c00d13005403207200c0b035626444401c44680050880488040c50071720b1001c1d24001c0208400104083d2007014400251607a11206a803170300d07117000f400030b00e4003038940810048010201200d0b031080b2012030f00b03100000c64604102d65117900e02149401d0100d1340b44003414041c035000107481504011410700303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 423470044 1250 423468794 423468797
    0x30c031005011107090209030316080c06070e0a0302010309140d0f080109060e1f090f0203190c02061b1603021e03030708010603090f0204110c0d0201090203030307030e0a0b040c0303 80
    0x49541c5200444003000040c8041d02141c100c40300401090201e50b0060000850140c01e9900b003a003044c08440c0b00300040c010907034020300c00240d40e51001c1c1c0d0600c186035001409061000060b8004400b0880700ca40c0d44c04000c3c10f15944901e41402d10544480d00b80c001e8518030101c0301041c10401f0002c100141d0340780b0f0307440071510350310020032a00c00c0b60080d041a1145402d0031649641c485a014041d13040c5020314900360a02d0100101e04e903445d07401410b10710301c5d0640340542c1d281000c04501001d41c2200c1c884605081c82e200c60754500980c08545584c000603c410825602840d0048405440c0708085616420310040e024017410550041140703039070113040903804c0d1010035050701565242d11045540c0e40014580350014040c0c87e01903401409224043c0d400200440b60990108045803422500852807690204000000e40c000300060804000c541c0b00a000d00c1c4c5c49076010990784d00020b0702503802d0640b00e0050b54114402000542102c40d000b051142580c185802c20b001845050f010580 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 423471294 1250 423470044 423470071
    0x1090b0109060203270112020c010203061e0d0201140d0501030620160b040606090c020105090c0a080a020f0315010603050a1505030a0318120503091c0b0a050714030c03 74
    0xc2d5503400841503850b48040703200c540d03d42400d646642030038880f800540c1414442110f2011107030482600c0604400c44450000503070342d0612030100b0001808000640805441e1050030b04890b403603541e01004101d84c203080002c4109540c42906119010b14190f10502602d003600002c18001580c0001a0302001c0c02c03009510a100d2403011380030380c4241039101c041510451200e2000810a82c580c545c014040d07400001e1240d1150301c10000c0c0d804010f5103600603034443c02402180201030041300b08040b011580a01100d1404480903100d1185400180c4204400915800192410301016141843c0529264459038440d40007800400301139403901d148503d4880200701c2200d101c00713050284e42c0c0040040c0720192251b13804440000c5c4002003100c0720a0419070020b0f103020301c0301d240c00300d951003000070315220100e203010702c124803800c1c1d9000b60741e40740502c80c3c2002040004000c0c50300444404000700c1c59a54a1006444c12003807418100ea02c54000000c0000080c0e401001c2d6019055507805803 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 423472544 1250 423471294 423471299
    0x30f1b01030207020603160c0c080d1103041503090602070204110406091401091403011b05220b07140a050a0f110102120d0c09030203060115090918030804020d0b01090b0109 76
    0x11070490149860083d08144200045004071100043c0c01c030048400d071802600902e0140e42c0d09504010691141c0410342c00240d0300c81c060394105000e203000c50b41c010021070600d444c040d4010810160030825500345665400d81205000880c1c0480302d204d40c0180c07081c0003103100d600300c00351203900620800002900c030341800f1504000800071180c504005035942012a03050034011000014640e0300194190f60b1402225114618a035412866031125101c85480361958000b802410140c0300711300c1d80651500c80103002e002140320544120341c0d002071b121580741c0110040342d49800c3c64600c0251092040b070001404010072506480c24680c482e814a0540358404d000682e03540030586461100c2d041c0500c00103084020030b030b1005902e881030f40b130018946c45e03403500803904003042a0083c01070321985e00b032160040ca40010007d00200300c500707004c1181141c060b64000114220420040802c890540420250740d500064600d415401c6a031031021542d492042c1c50080c448803a4190100d0420f4000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 423473794 1250 423472544 423472547
    0x30703120801050307151202030a090501060e01050f010816080402060706020c0309040b0402030601020c0103020c0309060d0e0f06040503070807060e03220609051e040908070b011a1c05070201020405030f1b01 91
    0x44000310a0303580c1f900e81d1841200424000a50401420354660701d0b074031050f40380400d000340280b80007000740000243c2a9410312051110311002d00c0c0300345040c88030920900500d4042001801103201c0d03240b4141c1c01e03903140c0e0300c0059401d200b10000034103201e0000c00d04c0c58051a000c4000c0842c0070b4120303420400d140002e4184820b9000c05c60302c0c24056040440c00d9405540130750002c0c840f1104034000d0380c0c6045603e01c00680c050300001881c00000c4e60f02d40a40034515404c002c040d03a045040340041010b49016074038150380e0320070b282c0b0091400201044040c02c100c0d0a4206040c003030384d5001503d07110020051031210308100b50800c004020b1580d0b07400118980200100300a98070003410074201210042c88001041c490400130380d402503900c4c00c403840801c0320900078009261140365a001254545200c5e808441181541910721010400c100010b0305c80c0c0454507401c9410b410380100d03455648410a82c0240119032125406024810100c1e01d0700a000c295003101c081100740440400a21100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 423475044 1250 423473794 423473819
    0x60c070303093c12080c09040c09050f040b0d030f0314090d020111180d1e08041406030c0a0e04110c0f01060f060903020d05071a0706050a0504020609040b030703120801050307 77
    0x4004e8500d0840c0b900c4600101e105184a03940300c84801455442d003c058804a81121100c0c041d820005501600512403841c001c20400400c103400c58061103170300d00440c0080e07025420302d100101030092688803452880d000b0341100c0c06107076041c2c41e104e125182001c51252130340c04101c0510015442c103d0450350007203281c0b054824044216942524001d00340061200b03039000c0314800e0303074500c0300c0c0b600d0b01000b240c200d8040613103036118500843e140ca10f05000000200001294130784660418010000203c184009461460320245010410484840c0220b07004200d01020b0400040c00003c420344d45600004032084060303003501c020003085960b00d40400c101007040c058000001c8000c0e07810005850241400c40300c0c0750040c02138807241b644c1c0708580003081002c149550074101c00440ea1b030f01401100c0c410320b544400440700601c014a0301703070f0026100e48a00c2c0c0d0618032444d40d9811000890700d0330088071028686c00307987c40d11445482a40900081c209118072480303840392040c0400d408902d00e0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 423476294 1250 423475044 423475163
    0x9080f06070806190e0907080709140601141b0309010905090112080f0c07080a03030b0405251205090708060603150a0515041d0705060c060c07030309 66
    0x10342e400620b4031140c08012070b6001e00d1800d8070108105007400300e401658405124003c1e0740c0c40c802881558070b0b0090450030301d102a80401807881c502404030b00340180c40b807841c6034401024a015198940700f20040c990705e0080101c0c1414200d8200c034801c1c081040040202010354007601c40101c1035a032141049140d21090082c1030032400100036820009d5015006404980002ea01c02410705000384415483c0501942c403070305e207030341c8840c50308410b00d034041c8203402601c9030644041c4180e1074041e0b116446c51049180450041d0850f440000910b4815000c0200d08070480c4000d016a0610054060741c0d0803040c014504c01c0e00a00010a055180001f003101c800303120400042c0140c0d580c003140c0802020f0052001032015000da08290407643d0b10303c2035210140c4448040109a45515009480d02d0380603044240600d100b00608402098000b420380ea0202c18020301b155035640c945402c601805048070010f2103402307140c1c401c50a41080842082e2100b20401008440d503400100181c1036400c0b10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 423477544 1250 423476294 423476297
    0x204050a060819020612040b0402011805210709061e080c010c0605060a0b07030c0c0f18020d090c0b1e0a0f200601060201020a02010b0f060306060d0f0c09080f0607 72
    0x20b05500300360a014424203c0d4060000308821b05008403420740100400701110708079640c13000c60003000304540e00115560301401c1040d042d10f200508080200e03d200c40d40c0324819010419540c00d1104010003000341e01d024200c01c0300309001456943c800f0a02200403240240c115400610b8049010800082d21140f20300c1e05130f4801d0f81207011a1a0640284800b50a6941045144201144410101c4000d1546503c40d507103508480c401410901030004258028042000c02c2110810000fa190340781540d01102d000401039803910f495044800500303040c81c004004005860002503540e1400d405052298115840c040d82c111f1043c642e4522072080c0318120b40450021840c4c010401e108a510704101400ca441039071000c0f8a00d500540b40c40402da1110380142c0d00043e0340d10b4940d60a0080600401041e038503045081d440400083c0340f400000c101500400300499040d407808101e41000000e4082c3d124104603030018100018a00616409568007520030540303008460003001078030903c505040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 423478794 1250 423477544 423477553
    0x2010606030b091006110102040305030a080403031a0604090e030412030323061804020112110d06120f1205070c080709180213020d1e1508060103120309030504090f090204050a0608 79
    0xa210050350030341c1051006c501d113590309010100004800b0002424048c0d540d4a803a41c0900d01441e006081d106070745078804030041010b20014058469900340d9099403481c02011030303c0842c0c00381851845c050b6500445240c0000303003500050680550000031864450042601f945021030156011080140d070761641010786019206203d408410800d50000d10514210003000c001d840188250303840e0084841c0c06120003d1905100f00b40f074807890004140d04a06250207005540300c202070b0b01c82c480340c0076200f80105d503007050b402c3d8402c03811201c041da441105c00140760f480b43d170040d07a606c40ca40101c1640c1c500e4070591007080c2048030b00c10030340243d008101e43c03040e85603103000c3d80103500b000f106c00031b0f500d40f40e141c2030452050740d1144083c07540345264001141ca50246030568a40c3c1584d0002d080798018000520200b10440c045d0403921215042c0801c95940350314084525100c1c4c2d40c4100d00583c5024040700a41c6001d421020489008890620194803004155800c68441d03100b02c0001c2d901 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 423480044 1250 423478794 423478799
    0x30c050c06150609060706051006021b0405040f0503070f1205160f020613180f0506030a030e0a050a0806090105070f05160c12081903091a13050d02010606030b0910 72
    0x1c121582c41c0c52502c000e44074034100416040030640c10b0b0003180040307d2584d1110200450031202c4000c190040c03409200400e92020040800c82e588150b51190900641e29500040c05000200c6000c0c072503154010f044981d00d114508100c0102c12030403004540c0d4909201416900a04c94001d44000404005549040b6001941c032051104100e0b81c040303070050418400c444044501c01e0484000700070700c81c8070b42007252203015080110784040382202a25880d00b0140080c41d14000303007202c2011340c9810100c0030b4450b4140010b02c901c03d990303c4554407007040e150204120601103010b6010b0010600203000d291079072401a920245601040700014005100300ea5000d1804400c0540303140c040d00d1009e81c2c050300c5078641d080d500888a001c0d1030030800025900c440000b00c05d01d0310f00f203d5540c0f070100806d00055031510740b110040314003401103800400204042c1d00c0c59000c2082480e51210444001d10002c1402a001e07220500c0b40e400403d00d440344981850511039000c6109000c2120160190390 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 423481294 1250 423480044 423480061
    0x32a0b0f0f040b0a0e150c040303030f05070905090a090807230c0303030c130b040b070308010909050c0402030c0c07090b15030162030c0607050309010906061203030c050c06 76
    0x41640d03844d40c0d96205001b014460900280f03200f0b40943c0040c1c40140e039440c15402c0190580303c0b075081d408030301480c060401814035400482801030f54003c81d2528030300d4540000510140402e004060005030b0006142400c100100c1364401034900c3c840d840800c00c581c00c681c03950319030060030b00040d05a00300b000050f601922000c0105008090080783c69202c54031052032541d00e400c160000d194038030000600b07030141a000a08180105120300d4240301981c035581d1400c0c0c5900c00841954000c40d004800f081681a010058540c00c0e075590040b0303071413507030749806100150402800d5180501c001070f9501c00c065410400703c078140d40c82d840e4084110394000700318081003601c58010341d0800c402400e00040956154051400c052200c0109802c90300442034200c844070780ba0241214140e00402481030261004105180d002c110381c2000d40d10303075540610440c00350034144c2c0010400c85c6400b030702140c402c10510045007000e00a560805c403141842c01d082c3c40d6403241d004d480390183c0c0240d0001e02c004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 423482544 1250 423481294 423481301
    0x609040f0b0a0908030103080721020a0b0403031d0607031107020603131e0c090513051906020408100204080d0206091209150a08240d032a0b0f0f040b0a 67
    0x210181400281d003d060b91036101c0160000e8200f103a0780c400000340300080c00340e5945885442c0a00c8091541210b0042c2c030040c4d03840b07401d0f110080080308414001030501d0700907880100000103071040b80c0c40d01e50081500f9916904110f80c1e000103c0d03d0031402224120403c1c041d07828040c1d003d0600e41c03a40d00c035142100d540c524180d4040304d2156031805030320f42e41407200c910600d44620903204200b001341801c0d85642038500c02070407105011610956080030481c0050180350101107016808004281402c014000c1c0c8295003004106110700d0610090002d5564001d200302c461180c252118006624070498640d4401d444400555001c4c0c404100d00601c81030040444503001031a01c82c0c0c02e9808800c0f40703442d40003000c0080c085801c90742000360000203c3d043c40e0700843c451281e020406944000180000d02409000e01000303c62503038501942c40e07421b101da0700c145030301c81c2800d100f1200e4501848800b604a61908800312600d0201d0441c214000f81d960150354007040d9410540d8500c0143d400a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 423483794 1250 423482544 423482551
    0xc061204140307050a03081e04110111010c09060e04200c0a0605010312020f0d0212070c0504020d09140a0804060e0102010f2f041401031d01050a020d050609040f0b 72
    0x400c0c16100807080345410401025102d1103030001d0000300242c0e04018100038001004144000714078072501c00c3d00c3c0002c0e900c459010b54056030000390300e2220070040b50040300c130702219a6558a800c0b105007e491300071442e5001c44e0300583d00ca0380703850f10301014481990748107920341d20300c2c1e4540c01c0b40c601407005140291a40700c003030400302d4824450541b942025a40d0a90080e5034640a40541100b11a030500c6200d190f100c002008080c00840420000d6407594018841a0081c2c00460460104064034512030018500200295151800a03400b0b100608095508032980380156400036419800812188403054111070043d0810380b030428151807000100e1030345070455594005c4074880361703120b2240f050320940341c440517181c039910850b11154035002241c0c242d034500b03420712040190644240345100c0301c0f5001c1c0380100d2103201820301201c400d00d50710040c0c4440d5003084200510429164003070040740d19080000d010707544806003440100704041d80c1c0500748001d202c4213440890051101c4582 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 423485044 1250 423483794 423483803
    0x2040207020d0f0b0115020d09140102070f09050609160e0103090c05090a09050c1c17070506180c09040b070c020a150c1203060501050307030c17070e040e0c061204 72
    0x1d0b881d0315075240c007280c0610680844070f29204c00018002c0c2d0703229030615146484103000900302e003240c1c22000303800d0030810300ca0074108607040900702909074820f0081c2002805990520010740d83c40320040009444211207032800307020001d0000f11035140c0c203c01e0b022611481d803284000c0c40004c0d0b004402400a610b41502e8440b40d0070800241c40c3c9031118550710512201400081e01040c0d890070b42c6c20b152041a040348600381c20131000d50070700751194006040591006502041c03031000c20381d03c142800f41001c042c01e580102e07810003120941214014078190f2045050f610541011000c20043e802c09483c040d0150010800164000b8055042c0c111101d00091181c4000b40c1e807405440301d4004090048400503048481c90010008825140690503445081c180040b9060600013829404020004002c06840d140e840c030f0744074028901e1032522048000041407901d07000e000540f0f000c0340310728424040c900c2d01c41d04510307440c0007042400c10205d004180e01d00c0c0c03148000c4804404031000c1c10548 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 423486294 1250 423485044 423485059
    0xa1e0e06030f0a060b12060108011e05010309020d12110601050303040f0e130c1e05040c0e01050a03060503060c03090d03050106050a0f020c090a051e0f07030e010e0d050d060b070804030204020702 86
    0x103510440380081c2000110100f050f41403031610400040c190103040c0d100e4bc0201e2070480180f10f01d014000b01400a0394820b00e8001f0320000140002404816020030181c80b4480100030000440d07840420100300201e444210790080e42d846050640d0b070b00c21342c4607051103004900014070034040303202d10352a0400c250207100a4a22515214641c402480c0c0c3c1c007101d003007000100d2030000c0350001e52413040180402c403000c200c020080100a0f002c4440d903920181003010004210448a00039403108000c1c19014003100c2c028506400c01000a038402e0f2083c250134403485e003c00640fa071003401018107803545687c489003803000349001580d0458485c0d41040a43c01424900c00301c540312003840c64030828244d000424a0f0428440c4850f81050108070001900c00c1081003200c0740c003c0030307807854003c04a40307000a962104042c0f071a0041c140000411510f0288a02703c1d014140c0c0308010b000c17440c032424030030041c2c140c2e110710f24904e522135444020690b0005100410141c42d065024000e00b82c000740ca01d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 423487544 1250 423486294 423486299
    0x201050702040c200a02090c0a141c140403090e1306050f0114010906050915041706060103050a1e050411030a05150709140d080c030a1e0e06030f0a06 66
    0x24043e15099501078000403180e09202d80002d25804c0c0201d200c10140024186181d042d8022814040008002160f041c0d00018090002c2d480340e00c1d035414000c00700c0200d0b512194611010307000c603030714140100f5945041102c065407260000c0691409181e0540b20703030020078a40307180d01640c020003e0801207140003944408000c2805070207118450510010300d07180642c1030075501c0c21245a8a40a20704001800100340016504102202e1444100b102c40c000740c0c0500f000d614880b1300c51504080c0000c84030303100f0440030520008146004a2090720f040c402503079400204421545064490520307540b40300000c507280803003a032000707070018020319496002076a880003080c509406410121410351080320003001212250311119004282e0303140002007a454800c0c001c41402c583c1815520501075406900200001d01c4100d40c03d904110090f207480d103040c00009484981c1104802072045071110319118014429920290b1f4164000c01e0701e030543d01ca0310701409030241d00410b050340391641e80801 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 423488794 1250 423487544 423487549
    0xa030806040e16050a0f030c090902031606020109020a09151202060c0f1c05040e0402060c010f1d0c0d020904120c1e11030d05190903020a0b032e09090201050702 71
    0x5646400311019901d0350301515000030312081c00c640d64400b08030038015074018030018280700188c00440b1001d900c0464544264000242400200718000c2c1c1c006881c440001035254064110700380081c000c4441d4000310350394000d5a02690030110308600801086402885215507484c0c90030a62400509042e0504802840d10351514200d85031900f40c95101402503e210703007850101c040640780c0c6103440750a0070300d0140c03803d4800300050301c002d00c0f03541c000c40d6003660010254043c10400074102010b200c07042001001c880394550840212455000303400c0b01d54098104900703642d0340e0359030161016013180d03195240c98900a03030381000c079000c014031003401c0402310f070180f0705002d481c0405100c14040c900413817904440aa1090301007a0107900400c1c6182c4410307801506440d40356610600140107400c0100040b62240040d41000354055841000402c00e0b8442c4c1c4007440c031924000d180c151100e01c54001c004040880004071142031921507500740803403203080d0801c04103a88103043c8141404001d600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 423490044 1250 423488794 423488803
    0x14101a0a120507050408190f1103210901020d091401230304110f031c2609010c14180f01030b040f05160f1409060918090d08090a030806040e 62
    0x9907000040d8004c41d081c06441c86c04d01c054102c03070900040c03801d40307550103a80703e954070440f0350405410109817044003640e42c0c405101078100c2c040300b0b2a0b10521502c007440d607251990410850140180f140c3c6003e004100d00441c07010066829900010440541c80401144c10a00c040c4a0465091000c05030820510380000a14013503440f4030081c03600c41d89010203101e41105a5280340d4881e52001282c1c40d9030349a40f4800185c222400d00d031031100203031001d21400c4018000400b40300c910001c1c00c03c200e0030703450640c80401044040e55441034296207403603800c0c00d580601a8142c01010700350360710a000340b0302600c20440b40c0006040c0490582c004d000000c0c21a40e0b41a1002d1420761100c0802c0b01c3c0d24084450300c05500718500301700001111420004100c0ca0511600d00702c00f82e400911401e00d43c0e6100240c1d092000c2c0149910003403800c0c0e50400c2d09402042c0c48554452151400081c2c840f4040c0e140305115482410040904124a031003c079528000505110341050f0741d50452440c2100070b01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 423491294 1250 423490044 423490051
    0x120f0708040b041d06040504030c1b0f06020303011a0a1d13020409050a0b04020f09040902120d05040618051005130b16021f0c02090403020c060d14101a0a1205 70
    0x903010940c00b401401c81c40d134004000d00907807180c0d240c13108000c000b83d0002c3c030415400d43c00c90490245a01264407030074000310160004110340e00c00c03900010384a43d0000c025410780700800702c000c11070451200c4a44407030281e15515004079020189409864820010007040e500005010304000061005500d0403a48240c001c0c24045807103200b04003490140d4003800381e11480955003186810ac0f01c0c025a031090007240001c174843e58a0780541c5c0c0c295641d614007510886a41c2d010f032403140d145108040c0265109100324404600901d000480c21020305460600300c42014100241b01560220100c03810341c001240340c042d00304040c5000c510050fa13440030709a8a11610400003146003a40100305080d1800c0c074140299030310040a00340030b130391b00541c03001003d541a102c11703404e920b81d89016810002c11155864109030b0105010110842640118688101c80010f16007151201c402c0050300c0c0419004110005501a84501400c44000c00801440c0c0c450f180000d19204281004c0d02561010b8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 423492544 1250 423491294 423491309
    0xa15090f0b07200109270c0e09090c0d030327060b0102072c0c0715020a0e010e101d0a0306060305010b120c0108071707090e0603120f0708040b04 64
    0x2003402c90401c202014100b40020543c21100f10001102c0f0000345041124015989444001022a00604440c65401011407400b600500441040460040469141034012881140140c01090419101040b064001c4001030080c1c0d0460840d074406401410001e042c00c07a900207032500303848a1000c54810030b407170390780304480200b070352002c4000091500101d6042014640040c01d4000c0c41c900007060b00c40c884002e070445021090340c070a662001e4601031114041d2001c1c520a584c8000001f480d030040c90740107501c0d00d030b00c12146404c00045411700f5400c2c0d4031070340081c0000c030340720f0105000b56240031080e24080d040d20040e4203a0b50119801008a0b8030440d056604e4071410b02c01c2000a016010050b20103603129000084014442e40d501c4540b0400c0e58188041c510119048601c41c00c1c59608111000d007030f80324941030000c0f00608072001840f8881e03c18004034049030f030303501d00860080100c0c029611024100f0181c5a659065940141401c07074210104000000b90286c4d420301400007403005 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 423493794 1250 423492544 423492547
    0x7050702031b0a08010c09120606030c0e0109150302010c0b060f12010e010605031609090206040b07210f0c0b06190e010905092407030b09010f170c0a15090f0b 70
    0x80800f0702800c4122600a074040384d060100402c5641e600115447c1200d82c1400c070607490040c141440001480550005441d0720540c50011501444400c2c001d8100c0d2a900810400c44104005850044010307000c0280020860700640c0082035281e403115820200040000180c0389003400001c8016605071001010ba94451070f5104407401c007072088100604054025040104503000c5d020700d80c170001d00448440c0b607aa640300358107540703c0009450103481501005690b07030041e400c000311101c0c62142029075020110440c0148240b0400d10064000340c45d4560031810010ad9645801504c8007c04042c0c201c407441c0135294010500703040321801004003040c5450075504000503501920f00042c0500d5455101d24085452a22801561058113410b042e0382c19054640c540100e01030800b00303482542c0a0310700740004c42e104148000b50411500740e2804070354181c03406102d8588801040301e00d02d0740156000c01c208a45442c3e540394260000b45480d00060550710b410442c054800c5580101414100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 423495044 1250 423493794 423493843
    0xf020609041d0f06090a020102030415020c041a0906010e01050d02071a0a060e07020304062a051209030d030b060712120c020a020f06032a0705060103050a0b06100203030f0705070203 80
    0x800748071306908141d20202418404e0810f0700040e50703d1003540325114190b050700c0c2e245200b15200b804000d0740303450300900500900c99413856070311040c1400d403a02e510510f00e90002c900298010070100e1007441d81a1100d504040343d03444e03440005d41010400384c1d00c4038610700650403840c641132803180c45248448000104141416120754201200070614401e5520400007881031980144103000b4091528200c0c0101641c0814011041020820010061f21424001034040240000074141e06a8190101c0e4114200202c080b001c2c0c410102046030481c20402010001c240c8041103c46140301c81e0528201d01e031815500f91040f18100d07821000141c01c21740a800442c030f401014028071410841e1024210300f00027840d42c0301020350a80850326803140481c0d610030300c40505d00f5580c034550030200f511401d41e52410f0980e00d61082e200f0403114156540006409840c0c0340c030103102404120b600550460380d541c800c801030340c1e801801e0350003408014001d44005a0701040205c0003042d05c00c8500b03c4414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 423496294 1250 423495044 423495073
    0x30f140405061003050334150506030d120b0d08030907030b0f060105090904050732010c080a031104180b0315091b06040e13031b0f020609041d 63
    0x10000d40301c0302801c05244010004510004155147c0c42e038026003a92290130300c0c1c0f0600c040c0724040b0101d00c0300042510500424010007109400a80040f650140056640d00041546071066a11038201040042e8803c22100d01d1542c010918560042d000d60310400786500d9141d042c0e04201c80a0803594401101030041080c8400320907003050b04800c4d06101ea040060028181c1d010340e400309030250b059800018103201040064200a241e071007846002a10000e0943c0000c03842d440180c08003030a1310104d4110b551155410160442d0414415400e0503038890f4124041c05070380f04442c0c02c0350300c00e010104022880c41c5044107001e090105c0011102c0c100c800b0716050201051442d9008107641081116014010481e521a010585007404280d1340641c000351803406190841d8103000d5800040040a98a044400444078080d8440186420004d440c07014103c0240c8801082e171408c0310303a24001400c0007006040641c0e0010700200c2c3c080c2c8144a0080c0c084081d81480c212548411142403144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 423497544 1250 423496294 423496303
    0xd050c04140306010323070b0c010207020103050c030f012303011b02060a090b010909060f02070609050708061909080904090804170f1b01020304030c06080402011e080105010f030f140405 82
    0x60642c0a0000c40d89141c13100004c8030415000c04440d0002c44103189020752050020310081c001d642c80c06502c070b032444005c00e4000d402406089003c02c3c0b074203001c02c5010350680152807149a0308800c1e014182e0a0a00a1540c0d80e20345000100136200901e130050035a13402c7c01218140341000c4480480c800c0c1c4540c0092134044090007038a2494582041e0308040303516910903d0641d040c0800c007182c003544030324040c0001c10100c1000d55941d413010030b0507401c12145070030803102d450241040303d042c1034803a04140d490f104240d616011440e1400c40c0860004d01703640200742218010079046042444810124080c2e4103521411200c90600003014407000703c400c40504401d141c070710014010b06042510b01036540c3c0290111480d00d0b030000d82d41c001168820000c98014542c0000e01c21403069850601501c007000c152403ca0105040c048454440c40020082c00303180c108a13035404460f1b91803d0015201d4024200800f410103450f14158860150917000314580e1214072030040136580303814200030307061 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 423498794 1250 423497544 423497579
    0xa06200d09060f0c020a02041e390f08060a05090a0501150302042d05100f02060c0c0a02091f180b040510030b150d060b030f010e0712080d050c04 64
    0x45072912498130183e940c00504002017546c11b80340014044055444014014000041d485980d41045500551140d09440c9050200300301490b40306004d16502c0a80c1003821180c0340070000485120030318035141e00c00c0c1c015a4000001410f6001d03213544640c0856101e200445031701d000035446000400c001140c150b108060101e040c0340450500d820502c102e86c00b41a421609566515400d0105400c0d8088803015030042100a00000081250b15006445295200c0600d405401813000040001e1004802c845034071100d030b0048c12030805544e00300805000d01800701101611500004001c1d62140b400d5903025008034052600000005056402070300d541440c624016401c140a001140729981141c00540344c0c40a9106101d580300e50152101441161a559200380010600400e102c0075038041810300f04141c0c140ca41d00300d031014600d426034039204803841c00c543c00020100722901c204044007007402d01c60660300349004021b0100009617901038072985d003d02000a41000340d0605040500074 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 423500044 1250 423498794 423498821
    0x110108010b03070f140c030715050604021603050c0f030c010e2a060c010b040f051e0106050901050a0201020403061b080f010b0906160209010303080105041d0a06200d0906 75
    0x91843c1c0020001c0401c40c00385651414498130401c542d2401c40c2400c00c0d94500300d9010100c03912003c4500340980304c200908003a9484904d080082121410180200c900e91185407810000400041e1b900312810360054481c0c00c1c40340290703800b805203180c0900041c90769000e2040041100100420001d09000a401d40340700202d0310400612400c0c041e880700308007040d400b10740c625100ca909150300c80c003416541c42e20580c0a840d0110341c1554140540c003180c000e103030810145020740404000e50400207020b002e124042030013030180203065031003a401080c1c5120144009410f0503544d03990107040e80c02c443c8404544a03031740d42040360141d9221031034962190780071003003054951401d0f008501d40e12491707a00398024030780010701c01466002c1d50f0000040c942d01607e000100d60756400d004040050078054144207504040c0d0401c11000084520500694401c000c0c00c2c030000c45a0b0342c60014003807122041c0301d4000850592600c0412403000d80341220925002203442040342c5003010444d01c07950032944 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 423501294 1250 423500044 423500047
    0x5010e090c0916180b04030510050c0a02100c09050d051c0507030f0e0a030525050d050304092d02070218010b030703050703020c0706050408060c09010c0803040f0b04110108010b 78
    0x100c1e2000c0410070b1181a4007410400d6030b010204414200c03920850300184217904001a0000801000040d50142c68a500e0000c0041e0788408207070351f501c1d100b4460f0740d0006a0002c0b401d918080708641c0511800d090a041c59000b940d0b0310000714038100d1a6582c10380315508645511410040d1140c0c0c005034039070692074403600d404035554029107810010441c80040001544d4810a16212010054003454000b800c660840440403402c1545041c02d11141c0b240c000306041c00070322402c100040700752081d404000b6505103810306940c50024004110074800391040503142044000210741590381418540c0301c09a950b01036401848020640480c1d45d0340500e6070310004005000d2400b007620f030003e400e0b2401081e1901d9803003086000e4003d45284062600a82030005141600007000780129450038060742e282e039a485d244680e4034080c0a042502081e002c0c420800000c02e80c20041da4030902c43da40c5141151050f40324540c00c050200d40446422201c1c2c0f00103146503030040041c1b4018a42e03200850b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 423502544 1250 423501294 423501301
    0xb04111212041d04052e1404030909060b09061e03040818220506130515031204060801120c090f05091006031211070e2502010207050307200405010e090c09 68
    0x5540c5c0c1100b0b00c0309600144240840c0319604008000480d00802e21441404021000c81f0b19105a01e0103640071400f1411074030f0005030821a501420742110b02c5203952a0400c1c40c110240003a035400708080c00e40001d408034441d0b040002d54006180918001c2810545074558a94044c03007004c08510064415441b0603501d941c210104000341c00391401c080c801140a072174210106400d02013080e040080a8142810800d040d981c200c0c910000703610460440d0500f00d0841141425031145000c0c3c900064910801032201c040e10440500d80984515a240e90305d50761010b4000440c1c441d41401c020564440c41802020312042240e1408440c841c03004200c2d141c80c55a41481c4c07800c0c90041101440941d85915070149028030440c001011880e00300001071074810801d201040f18400380c0b111010b5480d0700c510340c5900c148203444100b03920ac801185004903076152100d02482c0b0b00141c040d02c1100e4000000340d501c0d00d00416000303215001d40a1702e103003400c0403214185010078001070700039250403040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 423503794 1250 423502544 423502553
    0x71b06020c1e1606050a170a0b01030b04050f040b041a010b0307090e0702100519090b09160e0f0c0903031309060b090a03080901091d06030d08040b04111212041d04 72
    0x160412503081e420171654132601c9071029213103a654943c106049600b05c904000050001d078001102420090703030100018002041040111001981c1074040305c108400000c00003815480310359082400781e01181c6010109045203803c0c10400d80011041c98400300c28010178981120f9010302503c0094680003191404001c02541d901d203940d844403549840701c0c00b1500c0602420f00340c038841504000148030b811b9203810000c10000c020744482c00c1d02c0c030408015800e1500255880001d5070300000d1a80c1c950f4854200502801c0b03000342a51190050400614619580c100002c040032544e41c80007110003440c040d151000c40e025680071140c100e000300002141d81d42d03040008001e40740d02443e00c60312110b62034012580c1c454190000d4400b0f200180d16501c460440300d140074480d08088084409460a10104980e280f800b5507005100044010104001508240d030902180002400644007507169082c01c500e001c0407161016640e540000f02440407522691240803001c0c0b12000d501841d0800e541c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 423505044 1250 423503794 423503833
    0x31110020304240e03040303020718090515040c0e1303080903090102120c0309040924090206091c0c0b12010b0903030417030418060806150603071b06020c1e 69
    0x3c62448006015046030714000340e44c0d00141003a00d40c4070849880707644038030340a5a242c0c003500904611403203017800c00865140e14016884259800805002c43d1345110f00002c4180c02c018008461449a030302d0081840748070070099900c2400300e4820f503d0342d440d031030401410041e0081c110034410f0300204041d440c00d90b00020409044c10010070202d64074004000d00030700714007649843c2c44d07005041411080c140311402c04822140e140a10a280412003040d070f10310100c907909007000b90415030500420301507280110b5060780c1100071480442c3e04501c02c0d91640b010003c1a00204a03201010078070b000520001c40c120b03400740020080452900c1c10600000742c0d43d000c0d900c211400c800c0303c3c03141d444000300c050041c2d40040030181003020715528050241400707000d480c05060340921542d00000c909074003080f40302501c51405401c241c95a02e41c0bc07001c030f641081342401008081c0340110703103500141c100c1c40145a10350068015250802e51442200c1b0568201c046e9004642e025004554880d0700c1e141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 423506294 1250 423505044 423505073
    0x518010828120305160509150f0d0c110c0a03080d020c0f0a061a030a0b0a05060a030503070c030203160812180d06060612110712020c060304031110020304 68
    0x140450301c051504a161021410402403500d614a5990b00c11141c240d00080c5c050404040442c0070f10f00c40d50000c6441d03003e24103080d5030118110045e801000980d02c0100f0310b03010321130392841c90110048500d4003500c0c03180d141800020180011182b000c50141300b50b2001c0b60040b07542c20111403540c1c0390308401740160420518896070008050802040802502e00700081d16421340710090020304144005001c0140703c1602c101c840040388181745004902e000d8196448a9102d55030388072003029000078240186080d80000c80c1e00b0012011031020005041c1319486503130311244ca01d003544185411300e12045070058024074585000d2020000100d20040082c90404032175446040c4282c400c0420070502c0d0245400c0750620f400c041c1807200780e400c544141c03640b540f03c01164509100c56082140d0308840902112801400001c000940ca0300c0b00e440303891094411034004242c80f0000070a1540305503000c03004103680e08003c00941c0000d000480c03000c0319080e42103003141760540301c4503010071002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 423507544 1250 423506294 423506323
    0x40509010e0c09030f030d0c0e060a110106380a17040614040b0906070206010f050f0307050a1d1e060f031002040b13050f010e211605180108 62
    0x880041e04000380441a603c0500c0010111400c80c0c0b4401801c9480307510488180c0701e120308180d4000303101c0307004110321400719001070480c0e443d040ca0164100d901080d0000141115500c2d04070000312422880c80380f1a500e8000d80d41e10b240c0d64400ca40002c2d00b1465412a140704110901551007500d4011240d0001c2ca100c40d04522000c1e500c0c3d180120050a580900c0805c000d0300000340300612019030006489264014100c840f20b4070750600682c1d460000348a10041c80038001024086424105c4480c9000074001c1c0485404584640000710030f41c089070440e5011401a81903030744110495290250450b0a03e100500c1405d1300f60754640340c0810081c0224025407000304800740d591810000115086588002107440e5601c80070f8000da19070000d80140c0ba5a019440c010450749083d03665403c440105840d18a02616200203001d940030b181c04845111850600400c8103a0f081404441c410450f2490003a001030b0410302049403da007904140d00b02d0320350510040c0000000080e07100d5414005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 423508794 1250 423507544 423507569
    0xb01050d0606050603281401120602041a0a02150601090b03070203120f010501110c092701150905070512071101020705070f061b0c050904171c0f0204050901 69
    0x9505000c0060b184a50080341c00c00000400c000c1c0d144400c10328504c0070000320442d607841080d1560b01c2025503001ca00e40c401d40840010040111490448000030300c40d20801015040c240e40d445282c0010300342615506829200089540d8032a038113100004880d56017080b0104503087c00d400007085c540241c02140060000000843d820a00030800d9031031001c024403c1c060136143c66182126200001e100f4540801c03045441034200c080081042e048000c00030b405007105c3d603566600c103940c00c02030002002202c6200c1c0c1402c01802c0d07080c02408804200c030b05860b00041d00d03280c0c190b011107100070000d90800000344401c040d6108035488035a0051440d2500070702d40c07000c0030f40c0c5600910411a000304944035034400000e019444a24410031a50395803103034508100c444003103028003001c030b003001015021641b000b4060361505926483e00140030342103140f10303440c041182d51415030100101042d050f062840e00f8010800c240624459584442c80079401d240c6080086440c007601800f42c000108003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 423510044 1250 423508794 423508819
    0xe01050901050c0d0c11010302160f03090f06030203010e0f070f0c0206040f090504140f030304031107030c1e08010c0e0f04150b0706050f0f01030f03090306051612090b0105 76
    0x400c1c0b0549054644100a0343c00e034480342c0d88041e10b460ba0954040701e5800b00c25030b81d062590f00a2082d40d10100390920080c2c602c440950703498102a8011004038140f0800d990041958040090140b014048503200103075294100540884040340082161070f201445000f003020107903000000b00c800004a00f40410782030441d100040950045070031031042000e10300400241c100080d082360740140d000f20061100c41c0c0c41061056200c204005500381294001c00101d030010f84a41081d41110b0810002e680c401342c0c50742d40301c29100040d035010f03000c031120200c05a000544000080380080c85031130001c10401e401140d000d0206c005d0001160f02c0b03100440c00d01d20064030713550450308414000511000360685c640102c3d0f11560096407040d0340c1907240c0000940d50034520500140117a505080c03014080c0c1c6150f8903080c8000c1c20500032400c2103243d00e00000013664034000c00f40907501000300783e0f00140c09880010700c0300d02d814a41440960501c0c003204040f60500318414103568042c1d461200300d40 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 423511294 1250 423510044 423510047
    0xc06190b1809071503060905010807030f0f030c050109030c110909120c01110c0a05100e030306150702130c1b080f1e03150a0e15060a1106040c06031b0e01050901 71
    0x410b42c0402c00307800f04c40024100480d03040d030100e0300f42c644003d0100308a0341c0340c840303c540d180341c103020040c0009042004c2034017013400c00130b00307080940c800e140c03198030380304140d54080c29a482154201c1c04100c4006440c0308015040025602c4114280c13540c1405241c018542607847c14920064a05250b000070141c0590301d081d003010103081e002410090b590056405026034450008134280e0303041c00b4404c2c07a40c070070061501802c0c03da0a1003100850850b125481080240024108189640201000180016141c1c4110211005134110001a041540003009440c120101f036001c543d91003c401441c0c0010303814400e480c016500c071100552030303680500c45194040309074117156015072008400c20003000c4400703800405200c0c0945800e100682d5481c0c45401d1040281c410450b54860800320034124208a0007808040a40349407004454281081c0241801019201518140d00482c420300c042a0540100d0320031006c1c5104040711243d10900007405030140070307005410450300165007052603 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 423512544 1250 423511294 423511303
    0x1081305060c0c120301030c03080d0609092006070b0112020a030512040f090c02060a11160503030a0e030a2007030b0a050406060b1e0904110c06190b1809 68
    0x169022040760501d0400c086400040c0d00540800d04103071042640e0102c0388140041624101ea40c00071072a4502030031a580c00003a600030101c0007111035910240015400028010003101c94081e140e0f4800a264034250480400036403880c07540921400c008e8a400100111f4844c4d0468041a136502c1c402074040c40040d140501d540d0014101d4441c0f5244000e80d80c400b58001c000b100c0c1142000020960390b0410901510340c02c0c40c0c1d160141e040000092850002ca4009400d03021040c6c1710350f86003844884440550300403001c4180e50580c0f0110130424001504d2081c4804403220100443c1404101c12004021000005e901c20500b004000000c2c1c0350082000240099507000b00d040700c0520f40a601c0f0070040c1411982514841d040180c000341d0750070300100301c9101d0108641100c0310a00d0091050600342d000c08102da4110781d44207044020f08241d0005032402d41c0201000e090507091010b130310104001214046a0854a003040b0100365540709902011640f0308107020a8407640e4821305941003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 423513794 1250 423512544 423512581
    0x207051c0203030f070c0f080613080a0e100302040e0c030c3703090201170708012907050d08091204030303050718080c03101116050f030f04052106060108 68
    0x1d40f200840d005d000c010514000c0810b0728220400d001060b565071b20b00f183d0b208801daa800c183d83e9000f50350640802e200300001c12a040e41c90504003642011107012404a0500814040000c0e5010078103015600c0c5080f06203800030700c0d140e00c050440c240100541d21500c00d040b4007140740744011003181c41c200c100130110b003048408004445522084031001a003e402089000c034001104103c8a404503000304900328007410183c4da0310f140b01e03800d0454549011612198070400004903013440b40b03140003020010107410741720300080d100000718250090006035000d0210969a08840e1a0100c4588044165000c40b42c1514020860741c452160544210004917090742415102c2200032495000c001001003219000ba03007122511500a040041224001c02010403103031000c03c12403c141e1046140380e51300500139416180c1c070240004c0c80e0352440e80803080d901458900840d041007240b4124443e05031552681e0040215910030140c03d0b80c4649000b800742e414040c038100170450312100310344c0c00043c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 423515044 1250 423513794 423513817
    0x108091902030a080c01050a05060409030905011107052d01090305060402091009020a0c110f011d011701060c020102070605090d241107060506041107030f03110f190207051c020303 79
    0x1e45d4100c01d031099003e482d0460f440c14a060070701d000304000d42400d22030044101d0b051b82c0c17060178090402004640031800390a814200748600040031500c1e56401000f00d616140103803060700e6030f494045d102e100009000c40c0f094140030040d030702000400c0020451992080d81140c001d940c40d644c074601c40036410740340c0d008a00164400b0405040e02030f000610b00c0c040d58001c4082c0c1c404003510400f00f00303e0111440066002803035076001d82c4076102e0301c00e0110303803580e1050600c3e0f40c155800c0140c90710b43c100300764400c0c4001032440d035440040d0358050220001800040c9800c40c0780413032410105145850603000205030580d0031107036055102d00c1406510444c080c1c2001030069004c10540d400b0300e600503000968445280c400801d02e18a42071144032000105004180e04040326510140c0d800d0000201e4101416141d03140c010015880100070200d84c01c10142c143d45550518441f01c3c01e05107900c129405650040d041408036a42d020b01a086020800702e0b4480942e06c28070119003140510011504c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 423516294 1250 423515044 423515047
    0x513020c10060b070b0a1b05030a0207020d121202041530020a0e030601030f15140c0a030e1b210d09051002010501050f0607110904060213050108091902030a08 70
    0x20344039800c00c00030828a4081c01103685c49448040c2044102e40300301c0d81da6904a101490200c034a10702880195501c0700152100509201c1c031034010441d244100304086441c503840c200c10a81680c0c000c00c130b6500f01d081d400c200b14245410300c5030710128000080b8a040601c14946410b0144888003201c0e9114003c820001112000038100c90501a40020f145000401c0009640461900f800144039041744c0e0001c3c04101042000c2e140d1021807003182c884000c410792900c0018414030800d141c124000c0d80a2261150786030500d0784024204d4956030328900780c40d0001e02c0a6400c0c07c6003074510440c540400c44101416600040303c00407011800e100750074079801500c1c00c05004603080700c030784803caa8055a1181d50156940c03012400c85000340034455118140602c100841d0802402400000d03220381201110002a18002a41c0e071400b1681110103540000d03040f0b5560b100941d143c0300804003030030680300c28142804404d03242c608139508102c050b10100410300c2955402c000c0000e45581250025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 423517544 1250 423516294 423516299
    0x60a05010c02060c0d081605090a0e070c06052a030f06191701050103050d05031e060f0301090b06120a020d06051e0a02070b01051503180f010c051803070513020c1006 73
    0xc3c21b5250202d0b80f09002d4803a160110395480e004034101d0343c00641c01403500810b141012803111000f10007900003420031007071110700c1000072520310a15000c0c08071503400c80f100d4281c02210504400300b816404920350300a005110a03001740c0031046400c200d0403500421000c90b82c00146008811990020a58121042108141c1201035002030305990040c400d40381c00f251145410364841c4810b4070362038404840d02414a68110a0451f07064000400511048980d204800081d0a450f43c0301c0080d52001d42c41806e0100c14684954000e1451501101501c4d1246140c3c0029035501712410300500140c0c3ca0f840001c254280e03503c0c0106c2c07516400d40510303140782020b000703075402508007203021501415070100214862510001d50b61000207200d02c45440c545d1018640d406002d00c0581900b0a4031500b24902075100c0203000f50710403043d599440c40d4031001256481110007101e80b20850080c0c21404051055464480d01c01c11260035101015907111000d050741c51408079507030905200a882d20102 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 423518794 1250 423517544 423517547
    0x1806050901020f13050f03060103051020220e0603100b040605030111030702100b090c0904141807051f18030c060809010f29031207080a17060a05010c02060c0d 70
    0x4079058840949894079081c00302c0b4140350ba08c0c0b5003070001600c2603000c01c00920720030340a9000544660018000010903c1e42051088525002203c1c505a4609010840403200fa91942070200074801e044002c0131904003440440d40342d2507032140884189446502c070041c0c80c1c48680081f0010302d80640204650312603102c0550309904141c030140014020031284402810442c002c1704d410340d0300105804030a4540034640900f6500c10340c090360f041a1520a02c0300050006102984109409110112802003480e0b801c2d00f885030302d4111a21038070184c0303682941d4440c40403800301c1020407410503070072012840c0c00181c682c00f51680300500c28446001c012a420340c2c0301000c40d0044082038000c1c1b2424100c0c000e441c00340d50800c41424044421903803581058a0600c001040100c0d002c1c0030b8a0610715450004407031640040170580d4041c0d000a031610750350394400c0b80c80141042030904580c0074140359000900c20905032040c2810490b1a40003001075503a52800c644070f0b41003040440e203240500540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 423520044 1250 423518794 423518827
    0x409021209010504031d040e010f020d141005090405030f0f09010305070323070917010902010e010207060e09040c0b0d0b030d090303090b28020610091806050901020f 73
    0x300485000300c003246008105010f803901966043d110303440c41c11040c04c4030543d4030010a69141e0f20a403101c601002c283c100384a501550480c40001580c2c5d004d00d444400c05940420489401d0702449100308000d5846200d140c4042d503008661142e00ca4450342040c51542c095084d51f036034079080004140c00340626080003007241d42030a032014030181c4d90f041819822600c011000501003201a12041c030080781c813000c42d0350300c122035050007400540c0f1b51240f0408050405110401c682d5111795035003e543c0c10206088181200744000c0031001d061010040030458600c1e02140500801400f1408020f02410101c0107080c54581407134030307070740402c00440160025014281c0680621164080014032912520003030f650181c4038144010f1070040e01c0d4107550302580020700707801d0321035101c4001540400e010210400f40d9600601c20350405156842501000d44c3c00649084c0c44d08504a168010103143d4161990f00300c140003075595102e060b2180a441859900190501e0000302c0700b1911000d00e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 423521294 1250 423520044 423520057
    0x170a02120f0310050d08070201030e0f010c12060b13120305070f08030a050f0618101d0103061b0e010e240a03140c031b07120503070e0301090809130908040902 70
    0x1607206420b503a10414005020300d01e000150106c40104455809540650440383c0e0000040c0205d445104003516280e00710b5a030160f00d4000074401c1e0b9031090030064a8010301000c4e203410301c9018900005c0000f4400d008405100390489400b000002d1002d140c06041550015a04141034100848980c902030030315a0080314004032107450040480c0301a9040c20640e84134040151031074030009100d940c0b44000b801c00074503800c0701c00d80100000c1440c403020307410100c44507140200c1300403a5045103070a6084da0100420390701c03150420040b0111569100d4500000d41d1401e0804450700003695011403011880c83e0110310245650240c800312450401c0001e0000556a1b0b400b0404928941d100e45000442034602e0030342c105051010079815450649211685840a00410319000d40ba980d007168081d4801c5201000c140b02100708000e203a000041060095801c5000300890f003525900d01e1355a000d04c1200e0b40c081c2d04c2080c0f0b2440c42c078415a1046039001d401c040c04544503559164041c02940c480f0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 423522544 1250 423521294 423521311
    0x5120301031b0308180616050a120e03030703050a030b0306070f0e01050f04032405150901050d050718021605030d061d040803061522050607170a02120f03 68
    0x1802d064042c50300d00e084180da03803050580b03241a680d044d81050a07021850150750100d420001040000702140c000c0303000900c14805031058080e5410700c801d4880c4110342d40f00c02d000007600710320704a550202c11100c007260305080c12501c90010020840c020111070f5800d642502c6000f0034051600c0d0410001d401c00382d283c1e60750310240c82d0b01d2401100e080c0200441d0f660f8507901403005100185580c89881c11040302401c000c044170918643c0745080c0c0e8400c0c1c60044c10081041c0080d0b5150a2202e482c43c0034040695900f40d80d502d10703503103c0f5601e9105201d05a00741014156517540c10305250110340764140007062000c01700c01035080840c0c49610107101000c076039140c1b150000f8401e806107400a00040345000b40c004e141d90b02d4484204c590320040030154006140c00341841c1c00501d060240c440d801e0350031440503099980d000d1072544044240c000350f1041009001c550000b038504070b01e004400742e03180c0401d501c1d00f683c20300036842d00002ca000a0300f0354102103109225808580c2c0a984103c924 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 423523794 1250 423522544 423522563
    0x1e090d03210c2001091a0103110901080d08091f361403040504020408160e10030f021306061d040207030e06160209010602070305010f0501080d0c08070512030103 71
    0x1c4030112021102400c1070500468102050007075800442036140c1000d104420010a0080e60750780d5800449440303220080801c141c5100500c04d2013810701601101d52802d45450f0241c2d410b1003015551402240805c03020060254002035035950284030b0000701c800e80c495100c105501d510a039001800c580441d045425203003d845c0c082100c82209011010306400301030f08604030154986003040300910034155900e02c003c1100140f00c0e1505e1009000404045d03014040c4d07031402d030400c03051401f5031794052001c0b200b0389828003c0d203001625003c01103941c0402908080300c01480407a03030012462032041840740c41c0c09000a0303840c0c0c00100803440c8151804001500402520401080f03003e46a0080c00064101c505110342e0f0071b002c0001c04460f142030b11b62502504869000442e846800d802580c010f03080542e0820400600740601400344803801028407031503042034009a51880c4c5101c1c014104015a10700f40d0600c00e050040714180303900401070711702c1012040036074065984280f00c1103462500303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 423525044 1250 423523794 423523847
    0x6040b18030c06180328031d09010b07030315030c05040e010b0303031e011d010e06040b030d03020a17010b0307030c140a031416080a0b061606060504110c031e090d03 73
    0x507148115040d160a8200380d4614030710035201110041d22002e692234040382e08a0340110a95120360b1038900a004001e80c0b6a0744240511b00107007034400842d14012001c03815107060000400e40640b4006840041d80d000820300450f40446014040f1000c0c0320343c150100109205507040d0113905210f0003055403c411b589079a80384146083c0c880044550f00c00f40c52044010700c9007034001e2102c190801b42c010004111104c403000060700b000389805203100401d60004140b0341c1c3ca03400c022030718030b4201c507080008115850102c14003c244801440f04080558271125560603602903101c1c000d214403190521500c40c1010040600140500902c00c45071010040c001b0b014070a0981d804070800354503584819864a0710f46104c005001c0ea092010380c003d0040c001c1c00700c5c2c0c1e0740b0b500142503c0c5015010100300c240c030345024002140d803000701c103140a04003008a0030110030000110f920185286601c0200480d813010300c0380c070a0141581d80b0f5440103203140d01809060740100c280c0302c181031068000d040d88130b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 423526294 1250 423525044 423525073
    0x506030c0705120c030d18080a0801181a13090807050c090f0c090f01020f0f1b0f0a060c030c0623070e03070b070f080301080d0201060506040b18030c061803 69
    0xa0102c0e00490b42d4003c12103029001007a1f0032810100c00b032400c040701081d4980e03403503404903045542030301c0015525100400048040074920310b41d20050b01010421b00826007030709040d1b405660112070140d072842480710140c1100c1c0d40300f20002a00080c0080d1038440c54078103107444034030b64400310b8403428903900032400104160030041c1c00f031203400710f6a520301901e02d414440c0704124118400d06600034104600c1c80f003842800382a05035042c09015121802254540701400540c07031501c0b60080203000c0c07149201e526070b98001c1c0141d0707403d8208484000c0f1140780031505045079074001015a41004603004142c588480d840070740c00380802005000395220395084540c030380310f4401d0740d5040e0300000c4108002d90007100105501da001d01d2025102800a44a00225905c01c1e8080d800c680d002000610481c0e50a00ca00406041e0444d813035403910f0302c7d09940e043c0e20f003d8140e40035514000036500340c006030b0b0104140152440702030704858681e4120550600781e0f11a5002007400b0f4006c6405020208 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 423527544 1250 423526294 423526297
    0x703060f0209060d09020a0e0c0c0106080a030c080d02040b070308010503060717010b1e070311070b030403050406080a0b0d1214030c18010c061416020c01020604020f0105040506030c070512 83
    0x500064410f60500300054030f4203000e0044010266000152004089011051000458806c4400858040d65070843d00a643d007111250350100031290051151000013a41c8603d0010080d600155299102c22484840300001c0c80703a6070224404c0c010001c0c40740d04040c0c11400c180d04803402141035568540c0d524200f030314503103c0880484101d025840040c00500ca904002d40305c440302901010600d015041c40c410081d910203074041d004964281d030407020106081140f2000b400d1031000860550400fa54064994020350003002c09000d49480044d59031541c0d030b0311066201c6001044062086140e08100b0900350900c1e0030f4000007800c2c0c0242e134401940130411240215104481d40c1d14044480c0603141a440120007800d040101008506001c00d0b1103001d500c2d40f041079030003002d103e81003185180d8000c030301d071528240c10764201020191182e078022880305d0b8055015901c00d58910b960300c004aa191080d500115801039002c0305128400f50ba0601804a0350b100c1c0c022550f0003520070716401110b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 423528794 1250 423527544 423527557
    0x108100e0a1d19060c0903020604030c050f030307030221070f030e0415060509060d0b030a060c02190f0b0a15080a1e08040317090a030b040b220807110307080703060f02 74
    0x14241d03d4903442e00250240c1d01c16015000103151140895480340d001803265400f5078004d64007a9051401480340e440d2521343c4041010086008500c0c01d0090759001e502da014419145820481200c190790b1590603910032510301c10b03800300d010400b01c1000c1c0340c040c06640c0e004244030b01403890711200484081200342d54106546258452504014207a420010f45501519010b040c0c140c85030a915581d807070401001014601c10000450582ca24020003864030001d054800c04030800ba69079100402c0c520300100710002d400403005001c69030340c040300030047d005140300d2085030b0130307092400281c401000c0380c1010000d100e2199105441120207280d01003c06005010744059402c00040002a01b40b1009480842450001071f04150004001541e00d2500d90702c00c0c0d034519003480401040003201100300740e00039500915031050805508884d0320b60101c0c144024031100c0002408000d0000750140324540410050460b102141c0781c2c0d104a441d0141071000704da03080e040c6030b41214083c0c01c40c0240d402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 423530044 1250 423528794 423528823
    0x50309030409110c120705160f050402180a0602162421060323070e0a0e10150602060a29060c06072109050c0108100e0a1d 54
    0x8042c14240070301c0060412076600100d900c01002918041907082c840200c800c00c20030340c0592145040c3c200181041203064a08900e448903c42c00d1040c45a0300d41c0620951304242d600685400c100704034485030000e5402040d07400b4a4400b000076805a000414a4505009144200c080350390340b01c20340c94100300001400c081054409a12421612403101518800c94074000c014854104003550340813a0324641040c0c0c0c060448561a8800c8003180c80d030789803005503244c014400c8a207014090069030713402600c52400a07072551083d02c240755041018080e030b00c6006008014601c000c03140c143c5106403a00c034510160003400c000075803402c2c40c0e109100c01d50752180040c06010140d444100e00008a400125901002c1440710002e104402c00c130061041d0042c4d25906a840c02060214099400010366009110700709003000c00020808200c58032040c00030f0a0000850300e45020400039240039801c05c100d01c2c2450000c01241c281c094000d11150089000710500080821b44a140c660710801090003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 423531294 1250 423530044 423530047
    0xf090c17070f0c1506050906010512010506090f040203010803120702031314010302071b1719021e0d0305030a0612110d03090b0f0904060807120b040c05060307170705030903 76
    0x1d0a03580103081c0700e00c2802e0540b40c4030480c10041d9941882c0389000b0743c140300546a403000280094140300407070941003482401c00604210140075801c500d030005008241c0900c801240d10640c0b9103a405e44201344050061003903440750307102c0c007643c0d54a401400c50500107503901804250040e001100300c9080981e03000001503103a080103a1134200d00040d03403841d41050360800410001c41c0e140400c1c0076150a051155050062401e407546482448031401c82c8566000300451100c1501c2150f5a0b444450313041d60003000b00d90303c2d8828005540c0304141400e4010b0000c2e1900402c05a0120007113108004081d0f081000ca44ca4200c6444095101e0400814604140800115914020300c01d0b002c0b4030710030310b0300e0400791342c442d51b441ca103e070440c401000d0b00050114084206281078012000034049a01c02421030600c0c10742c000d2030b041803411b07003c2c29940b0410003007424800c0498800300a0310010380890b549003055407000f46000401c11841d00001e180c0341c0411500c41c2b04c0c0045134015809180110f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 423532544 1250 423531294 423531301
    0x2205060f03071d0a1e0603020a050d0506120d0c0b0903030601050a0539070e0601020a030c0318140f010f141b19031205060d060b03010b0a0f090c17 65
    0x3074441d03030f18801c0540416650a41c01c11210303541c0616000c094032003541d0400801c911250b03400098202c40d0000300038980103000960310603034402c050b10100c00000101041d182c69090101d0a20210020104000c0c010101403c40b02900080080c00b02031164200d10403075500c20007201c2c2c5034041591a03e00081c800c0000d00034161194002e490304243c50b907130900c0c071864410743c001c00500100843c521008603030000460001d00030f1150000610350420481c2003032a001000035112883c580e03004042c0402c0da008401458428003004e4801010a002544604e8070b400d281000b076880201000c0c03050310048044182544210340184810f01c060302c03a0b841202414a0300f15154020000400002c080c006a04a80380d908101203642ca080d6003a0035103141034241030045c0742c03c944080c0c5207809421314051201980300d850a4604243d004070700020541e00f40300000f8050200c00050507406500044081005008070004004030b0f9950101000b0080c55000207035901201d400c0c5d01d028071400c56001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 423533794 1250 423532544 423532547
    0x1120203070e180d08060f0a0302031203100b0301060914060712030e0f12030601020114070c020105180303180109050d020a090b041e0204030308070c150b060d022205060f0307 77
    0x5075a004480c00340440e0120004201503481c0568070944134000584000a00c00281004a001e0750400802d60300c03065841c2c2960080303951040c00c000b015408d990004000341800b8030304190391000d44042c1c02a59625603482500410520035802894010002805401c80b28503086003110140341d8030800369482118407500580c0200704002c02038105008000c1c002040f080e041c042d10a03a96002d00110351070741017034000203003129003503001e80f10781704401c800380801581c0103c184e40c0880d9092a0640d40c1e02003600c1032141146013140300130303050310011901d45141d00d04070706208500d0328280c3e07541a44a594008000480800000c0a508078a014600b40850301aa4100c140d003543d0150000c50307080300c88450290004e0088180703001050b0301090a108042d4030400c0f8941208043c50318454007411511074001c3e00901c50041d51a0b140d071040007400c5900e40f80262844110300a0782151240809510701c41e0850f81c100466030301041d004404074551400400fa0707601c811b103a004507401c565410b0310 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 423535044 1250 423533794 423533819
    0x303080718080a0606030b010509071d030313060c02010f05161103070b0f07060b15030c0d0e0303010f03210c02060a0c0204051302090a1406010f0c0503030c0405090112020307 77
    0x3001840004100307008250000200300308030740940300d800d00003409461410714401c0f243c1e0607048544103102c01014480c034079500c01c40048080c900c503a10f0f01200840240000c0c07851280400180702c0f407080050000c0c540360031031050364010303000f0380f6041c4000401c200100d40c01e214031142c2081c018007002900c3e01240880c0480030b81140040d08440c0c1c095142c8a0703911003500003000d095240703a0002a12402c100700350061140c50324046d50000c130980103000110016000040107441c282e4004121115242c1c0c03070f5042418224159401c2d60703641d50f190388140b2600d050038041070352403100038008400d034079400049010280e02c00741d8405035000955420040254881e990780000c202d80343c0300380c00169036140b180350f010301070905c03240d10b40c000e80d4418020201002442c0001c400c0c13800c0c0e400c088819642e94a668010001d28044510502100082c2d910070f10500002c1c089101c08800c100c24040e0b040001c04c207642c400c0b504051244c2e66103050b000c5401800c900290140c00240c002c1000b054400b1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 423536294 1250 423535044 423535067
    0x50f072607210e07061101090209041118090d09060908061b28080106030c090b0c1f05040302151023060a0201050105010818060c21010909030e040603030807 69
    0x54941008070340003060000c0c1c540c3c258007500e454200f00700400c612030b000301500010000c958020b2065410540004030b010340e005101418044401d50b0f859960781d240da00100300780f440c02042c0001130400f840c9283d82c558401e490701012480000b80810b03514080d2020b00c00f2144100000c0c052542c0d0030012950781c0c0d55001168400100030302c0359038290b40d1098000b120001741100147e01d42c4580d0a001440d0303141c10380c4518149813a100d400c5a1255103c400342058641c0086111354401c0007148803403419910074040ca0042d888100c184006080e16004a4010380c00ba601b1a030404040405a2400810940310b090051003800710400032852035060316000108240c55600c4001c00100100b04550300040719540180d40d980c0c0180102d42e0068900354101080c1e00b00003401e00500080981d96000242082170a41004100c4621001c2490103d0590306205140c00c143d42d6550a030410142211060840104080e12592002c070305041c0b068104036030705a40e90ba0055166140203941000c2e840 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 423537544 1250 423536294 423536327
    0x7050613050c090f0703150e13020a0504020a050904060f06080a1a1008042015180a12030f020604150b0a17070f080a0206190c020301050f072607 64
    0x2a601d01c40e948404580388a80404c20035030445180c07444000741103d00c0c5103c0d41403590030300d601c24020a003c80212030350000d6060035004005409000203078254203d40e0007240d1040c00020004400790340000a00518901a2024840715881d540d40004c1e000b541c0c01000001040340c0300054865071590440180c0a1400d0000b04002c100040460707034507600c4580d03803800300700c5820a101c00c0008000d01e0801411401e2482410b641c0040700081031104031044a20b403110011501d80880d502c284211051030a00502c0441e42035980c1c60b41604815480e40141e01051940444541040c00498000d22031544104805a001c001c83c00080080c034000113002d400981442c0c0105e0402049180a502800d0800041c07400c50725000c00b80c503203203500b07400c403440a030080154000103803258001c0d01e00030100298002050200c0042c1103451030851400694158208800d01204150841c0f02d2405090165200c8940501424171101145510001440741c5841100014140362140108503001d2286 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 423538794 1250 423537544 423537553
    0x4030c080d0b0a090b011b02130c0203192a0305040e07020316050c0f010e0901300803010513020c0d050c030c0106031109060a0605030f040201120903080105040f020705061305 77
    0x82c0303804282511020b41100c0003083d580c0c16241503030342c0c03c2900b603800d00da9501e0752180c528280c3c0d400b043e0248221700c9550102e07602c07080c011000c1d038000d2080c1d84560780039000003d0b507404000740061001044d41c04154002480d60f0082c0030f69001d503a00074203581d4140e04c842d49001d1a00203c042c2c1840700405084c11404188200c5040340081e101d04007001f4000c6009200c540c3d200000c00101d110901c07440d5042c030103480c000704800e0b168109000c1c1101d69000c0c2c2e00007038940640000c3c048010070f154244229001040e210204809440510706a8000303481030f9501d00740350700b03400b004ca100d400d80e80d80082d400030092100f194410401440c00c607169005581c04c0c078807180081801e41e405900103c449601011200d00709080000b2101d40c48070b411125068401d103000c44c060070901c409480300c0300b40381c1000c00050030340e40074440c1c0385001102d00701e00304241107013810020900a020301549200c4c44c1031015000d01c0d00628026512003d030010003500d0703245c03586104030305104081401152140503 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 423540044 1250 423538794 423538811
    0x21801060f0509360a06080a06090f0f030203030103330c18030501020c1213170304181506031a04090c030803040308010303080c040614130e07110c030604030c080d 72
    0xc01c80094192013080120900400f5804500030a130418024003c02d000fa141100c104070844001944100d055000880054032a45504044080040e0140c02411000315681030b07c0405030300200842c1201d01991880c1d040851214a100c0c0d0010440d9141e5110000501004015101580242840e0306241000748001001c60741400b0080803640c0146c40d181d5000c10b18070a040307010311020280d05c2281d0a05031a000700030114001c007016074014610f103046a9802120b502d841082264041d05503071391813240d40001036940e10060300c1200e9101300e1034a034104000619500901030030b4600c0c1e000c0300001e5864402c1d4428400104080320301076400c06c42e40c00001020540c84401103000b113000e46d86440c011f60640c1030180035000c1c00b07800070f07001d60b0b001c03c8200f21565110b0110092900d400c0c0c8a035035161001160202500d0302a0420b0700d107150b40b4030178040f4013500040c466021224000951350100d1001003003503122002220040c011850782082d800025060500030705207250b0850340040d1081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 423541294 1250 423540044 423540079
    0xb070e03010e0f060c0a080c07051f0b01031802011d010c020a0303030903081b0d020703110717100e07090e03071e03031a0d03030209010302040e0f04021801060f0509 73
    0x1800a601081c40d9000703101402840b40043c0040740e4007002c11700d0300c5840d200012000034252040102460405c0c0c501041c1c00040110521400200b001090803843c1c00c10200d0100c0c10060000c520b9550100c0d141416001004181800c060034203a01611801010042103c11030032a107070544a0314108688520341c100182d44001c2c0c40c4000c2c602a517800102c2543c289005841c00c680130b0107220700c100400405a00c241246030855941008a94000d62503044038a82640d030340624071003255a40c001c00d04003068081c40f040008480507010401c0f1000b02e800a42c8020489100b1030001010f034100c44000d01c0001459004008520040001c0703070700d0102c240c0c44a552041c000181d55a004d1420007401007410703490700551481a270f000d984940c18500c260700103011500704000040074590085680d4000741e0007981580d00901c81021303e030300a0301d085288025070305001c0fa0308a11514040f01000800601d401c40e442c165000341c0c4403440002d030b4030501034405403c01900c4d1075016401070380070311000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 423542544 1250 423541294 423541301
    0xc0201051b1009141c0309030c02060d050a0605100e0909070305030a05040503011104080a2a030b01050907020106060801030b040c09020a0302030603010c020c0f060c030c010221060306040b040b070e0301 89
    0x58002c4400155280103103043c418141c424041c5003401d9110390503643c10700f81888030080c4411914280022100700d2851309543e8004030450195000e0310100d080907500040c1d400541c480c8290407c1000000c1d260400c010000748509500340024501401c05610350a2612940750403040c06002c40303140030391740e03070310356146034070030a508000580089420001c50074240907003c12460413071681401c240c1800360f0320f6030301da120210250500340031080d1a201001c600c038080d0026166003c007c1d0400b0b03144d0400c000090780a104241c0245200000074a00900c1131042d1400c1e60743c2c550342c100480e442d64a61584002024205a480e1301598100180c0c44550744000d080880303130b80e200541c403843d10004240c21074510402d110159044091400056541c2070314041c0c2180007100c43d2a01c466040e2046861809460200e140303a6100181d0b0180d41d40d44540010365145e050901750340c1da42d035507000341510796500b610b0041449100e180401c0003d40055000b82e4009030520b0145443e9492000007400d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 423543794 1250 423542544 423542563
    0xf060c020718090f17120f0105090406020d06051003020c070b040305070302090403020111032404050405030d09050705151209010623030109020a03030e1201050c04030204110c0d030b0f03010c0c0201051b 89
    0xd0313040000e1a40b140c05500e1b411180c0c49030814140d21220340c074020201d45400d02c0240000d20b0260700180f59221611940d00490240001610b54103081c030700d103540503000350b0141030810403500c90800001205a4160101c13810b4a52120240034031510f51360a0224040d805801142503540394040e00d0000c0e401840558460400000064050826100c070900d980c07401c2c00792280590308141c01c00001c01c80002c200e448810952034001347c5139026003009414114650441644014010002c00c44041000040c0003035403d140395106d2681c44084509003282d051b0300c68a0540c0300c45440d481c2e021850400c80d01c49035540035001040545841c0e0000b42c800d80181c00440c00708113640820b04041c10a0088904400387d15402085241032900001009029a00c4000c4c81350340c403840180c8121303001c0c0041c0c60500c50040111085100c0b07460000d0080c111002d4024051002407000000a10b41401182d24088950300e901b820f0411a400450b0658498038402d0070520110f403000303003104d600304901c084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 423545044 1250 423543794 423543833
    0x1a0a20070f0608040b010302010f0e091906150e060702010c230d090e0f06010c0b1315060506070f081314030709050105060f0d060b04030f060c020718090f 68
    0x3162424503076030803a00c0049030416801c000000d001c1000041c03a4401c564156902401c20016a500d070728001c44086800c01103142d0004c0c1a03609020350300d07a03000300e14042da1418076002c0c00a50b881e0164142c07020400f4040368005002e00b0402941810440014072000b401890000316140586c0c543c4811942c220152094003d80c1c124041c3c40c26409200d008200d0b5040c0c640817130580d180c5000c00c01c59100c080c00340c4c201d084202000c60312503805043d154101581c480180301e02031800301d1a6412a80d04501c00b074414108080816828258074032038a000e4078001400c09060440648690841c204404001c0310081ca0800c400b440010696100c400100a240382520100d00b850003854103000195008402560402c001404165500320940303000e4124805500d45600c81811050050070311588454400b944c00500441404009040b15011700d0184009002c0c50b0050881240d4410b034034815041c000b080507c0580c0280b8880d0004100b950080c01c000c2d0041c401920b403282a03003001c2042c0d02 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 423546294 1250 423545044 423545053
    0x306180c0d020a05130f12140c030d090312050a17060d080c0307021201050103030806062d03011511190804030506072001020c0a060b19030b19061a0a20 67
    0x640440550f840046e0403400f80083c41c0c81d1901918110b400181031004082c000d0464110000c448200040a1f2230303000103084400c0c40e1074140b8003030411041c1d400182c401f1945102806101c9000d04210391000c402070b41c900e4540c2caa05420140b2089001e80601d07400320707c82515a01007804200070b02441d003452006150ba0301d6047c030411041d0003d0102c10301c45a41018010004281c02c804102d80c010400d40700550346004e610445007591a207001980c1c045442c4031a06003001d003842c4041e505030360b07200e0103c02d04155458800d6a143c17002d0b011300b208550003c50340003400b50403512207226081c8034048050400f6241d684503814448111135803800035074002c001c10611050380b1900341d0520482002149400c03400d00d99140c441aa001d80034110b00e85400445050b40c0b105250401e441d4115902d400030182c4034500f560ba06101511110512560b03540302960000842c8208000c45111b080030214180003404000c030035800c1030742d0900601018000c82d19000c4224604010351781d62810180 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 423547544 1250 423546294 423546307
    0xc090909030d151409060612010803120a0b030c1203040905010801020d1103070203042102042903120904050907081e120a050d050a0b06070f060507050306180c0d020a05 74
    0x2101120b443d28854010325540000801c112594104018200e100544140d00d6580d10400410110301c0303140d21240050941c0000060129008800b40c000c482294181d0600754440c1d401c0034003900c00108040b41e1640003115101100e1604c50481071100d00d4000a5a050658078620340007200e00c00da02c426140d03500080c10000510040c40303039a08121240c441786013036080941c0001d40c0e0307015502031001038095401e04034401c0c4c0c9008040310032a070780c014824130541c0708802407000700140c0d11b80702d005030302201610508a031a002c94022080c008091005051200e260708000141001408005081c0a04d070804200080c052159080b050603a154020740001454906c41c6041c515403010004240240900d0380f0103640542218140445e100c00801c075903c40c5010400108107840f50103a0007040012681c04101a150100c06030303a001d801c2c10056030b55030b02c50586d61403200310f810035031000c80101c001d500c084e00c119800383c004040044450624070600d1000040307902c6041c1000104002040c035 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 423548794 1250 423547544 423547567
    0x8011b02030408100c0c08040b13050301060b30071e050f070303090c0905280506031e0c27060a063603060507171e0c09090903 56
    0x18a0418196480214501894010542c0c0c46010401c4121400764813120380c1c1008900ca514070041803038010491580e21666041c0050a55209140104030700d542c00500085e68130307040c42080e040360280840c540c546000b45164004075141022042110302c2150351079000700385600c48091090010391505070220003038200b01c080c10b29008440304204003007007225224004040c0190380e6100c3d81030401040400607841c180303612940ba50403060301d540c6801d08101044220010505422220317140190782e150030f1050701c200b525001c81e00b064141c0c1c040c20035071840301515409102c800c41c0d00e40603258104000800160312040351580c0403400d8001103004800c940c06900d0306500401c003103130500182c40c40c1850103020020a48918801494078038115030018910080f00e00000e4420042010580d03140d15100004010a540100000b00e20b000000000c200360300601d8080d032449809418034a02010041140b980c0061042510060a016864050b121710100340e0290b902e4074003458443e405145d1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 423550044 1250 423548794 423548831
    0x2307230a031202090d14012d06080606030a080319020406020c1807300f02040e1b0315060c010e01090302011506050414030f07080d120b1e13060801 65
    0x4007500703d00c100034100f801d40c0c0b01d0820103440b40c2c0c40301c4a0411048412000d0f0700500760740700c59044a0200e04041d164112001903c00e2840054000801c14140c4569540c0e60321401182e1881c1c0560040c2c88002c04034000030040c41d4010307030308481032201010395400c000036604164815401b41e400b0b24861035941c0b4204010000c4240b00c0324072052103140c042e40003403d94460708501d00081e0307114012010086000e524030800c5040c010780a000f907034071070080c0c04002c0d8818440c0302c4010810340c01285803200d00003100303007542c00050011800e5440d03e0280300c003801d203043c0026600050400601008076000e015507110078124500004019046081c040d0035101081b00c0310b1540184010148a06034000082e00c0c140c490301025203030009070520109252a50301515806e0310322800303000165050300000d0362200c0c207c40744d40c3e403d0314044441034041507454030361031690320404a61a220304228841000e00c100c60300100844041c00d1110780c1030040714a15001a00240d446000200d4044084203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 423551294 1250 423550044 423550067
    0x12070609050d020603060103090302210d0c0201020406231323040204051302090a030503040e010602010b01050304080d18021c03081f121106130501030c2307230a03 72
    0x8400b84410480380d8005149440002c3c1344034141aa160440700c00e05d41700308244510801c0003100e0a05008914443e071441ea007042a8840f241420900b41c8c039411403042c02502e0890704da42d01d42e8041c07070b000c1000c0f9028203075040920340e0b03100c40706101c00c112155000c2000001002c400420400f54022001d0b801c8580c10051602e034040c4c0d0040008000035100c4203541c1e68948014040181c036841c4001c0003441400be9580013030090f210114010482c1c02040b07954504030b80c4c20750000c000e48094007005481c6804210340203403010506006040170b8103045d41222070100c500b906440024a01c95000480107480001e4003042c800c00d141400c420150841101d607084a8118400c500400e100c491209111800d4043c804a100c0031882600800035400b80c5221409001407180c1d4895040c10608002d045441c480c607030019007441000340d001809100c000340881d45400320742448107018000c00344998030862048502401c209030001c1e41800c100098030540c000348000c0c286006003424001c00c10748050 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 423552544 1250 423551294 423551299
    0x30f1a0a09140c060d020d060e07032403020604050402030a38090112021c0503030a0b0a0501050a02060703180807122006130f02030f010b01020f030c0c041a1207060905 74
    0xc0c0300c0c3d0303405a0b25241541c0000c42d00034800340e6034806524041010b016260300c040d595151590901401540607000038400034440708070b0898401d801100506120124032001c4e410200401c002c3c401c2e420716400450307000c8030303d8602158401551038401c903800507441c0c180c0105d042c0f0705100305000d540d2030500c10200707400311542c00c159410034031407902144164030000d114003214020f180801d041043c5c10610103411800f07482c0c8a140c44002c800207480101e525034891502c07a68041074941c0a807007500e1040526a0040c240ca944000d801d40061200b50360b0502c01106000f00180055500001001d119100718404c0c00103804610001c1d01c1c1044251128910448a4a50304250030b00004e030141d200d203030034152083d01c0e011810300c50441d41c80311038065018003460004510502054002d100442020303800c0710511038440c80e07030395268064010384084070307082a80c010003e4038146c0c100159061031a00e940004404c0c42e000100c040100350840d281540001d40304012241c2c04c407600070000c0405 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 423553794 1250 423552544 423552553
    0x60a0e070c0201021e060a1d0a030e03060601030c0f080a1107060f061505070305031f1e1413110d021201080c041107230d02100e0313030f1a0a0914 65
    0x1700440c5034031200002e1801441680d9940e486141d555107900c0140b846841d5410344500c03030041d0800816000c8414000c0b07010f882410081007240d40319119203070f042c25469484042403440100100c80e01031024025884060b259481200380b056060002c02650307108950000307800c103035000c802081e0341560b03000d0016001244070f150841d54020040380d10301d5074180740c01035407991244680c03d0034076400380c09505920f11416000c039601003501110a5984c0e06000340340702c0d26981c3c082d0118840804050725401684041440107400d03003a800402c102540c0784491400e0205841500c022030b080728130001c00d408010401004481c41c180721800c1e0f440c0c404c3e2800d00001d26600090030380c038422854010403104135098a0340c04140d6031440004520f2500c0d01f0b60b02c5024414800955400c121482d0290161801120300b1013a0000422112411417080070070083e6032440c1c40e0201605807144054484580808074800e40428040c0d240780f00d204000350009002c181800d141d82018500016000158030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 423555044 1250 423553794 423553843
    0x1050903011509020a0e0d08040506030a02130605270a0b13030210022b0f050a0e131a010804020d030c03051207031d030309280206070b0f0f010308030609060a0e070c020102 76
    0x40100c1190243c2b20706848040da40e46030a182d5100900c643d10520590211048001c6400b640c08001401111181c4515040d09142ca08803910761a100104042d07000015041c10080740c1d0040380502842c02403110b001e00c40030750340d4020480300943d800c503040068001503031141c2410204001c0d410401000b06040c00500030703d030405003912600700200f106002c400b01c0d030072086502c9415980340405029040400140d07107030103141c0217081401480e0500451100d880340301940302c2c0803504d201c0c4d900101900c203080354a840a840e00403200800b50f0404c0410844c000e0f05251903008103000b004d40340d40003d208424094202107401b2600c4101030750780c01c02c00611034200c50019600c08001c040e566080d4030744100780039452840d0464480250041c0d4046850403c2c00441c0b02c1503071003540c03001440c6c3c1030f0760356004585125000034000148181c005201280ca181421030610b41c0c400005030121140d6901c9100e503001c3d9080440b00c0c0741c001041c1c84400021541c0c10720412110551040c80000c4a10 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 423556294 1250 423555044 423555053
    0xe10090b0609100315053103080a0b0303041a0f1305010206010603020f070201030b12010905062e0303050a051c090203010b010801080a080304020310061e1a030601050903011509020a0e0d 82
    0x145507212171600d58031100410480c5070078003801c02c404d01c1c42c0c040c0c07000030054007240440308040901003940800e102c500001c80d41402405180221070300200035515040c03d11320105c440e101c0d101c141c4110f82078240702c1a96a08610030090900d82c42c20912400c1a518080009181040507001002098018046810051501c4041e1684260309003008544001c022010030155203400e011040f2039030815000800b40100410320078080c01680e1680d10000c5401d00410034020746140e400400e4416440c0304001082c03085000d0080b58001d031500a103041c0e0044801e282c00141a000c0c004015a10704501c41103280910800410081c20308201000d913240180c1591651402c0801628410000000078115a801c0c403600079607000b0100c1c01c1150940750f18001c204c14420039849031004209100100d00100031001c220700b5100c0c4c40001030b140d0f9946200440e03060300141e900c1e80d015900c800e00d04c070402601642c2c2e0b0b0042c168841005131101c000900c018044000451140d01a08144020341c002c01d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 423557544 1250 423556294 423556313
    0xc010b180a09020103090204110a031109010c0b180703141b030303010b0a050c0a06090506010b07080d0209190308031b040e0f090f010905030304030914130e10090b06091003 76
    0xd800000001d120b075014001a0013402d20010001d5006180032000c028441100303014061800c825a0b040180364000c00f0792014500c51000c10311301081c04801401c00040454004503409001c5006a001c071500800e505803421110350012215460711194001d10032504001d00c0c1c0c81d0580f080f00c611240c0c2d1003040403988910040c003408002d0407001446c2d200d03050040d4200c9000104120807141c1c01540c1d420018024035082208450a01071440000b400000103c147d842e9541c200000b589803600b141644002980804400c41d0080b40030000c801400120f22110b400039401002051341d60b140c04040c000030f41c69043c501e221039000a000134001c40c0114007e80d0b0384000c001e1095200341d2900c802d642c1ca8a1140400450b0369070034070140c4020800c01101450080b4400d403101141d40380c8950306043c94940c1081003a40203001030809911842164100c55078800200302507e070140d2001c901c0400392410b04d03005865041c141e2050000c20b04000ca2117aa00c910120903108c0d0403821070755204e444 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 423558794 1250 423557544 423557551
    0x702030a0914011b0501090201080610300905060a0e21030a060b0a1d0609030606090a0e10150504020309250f0e0709050405060123040b0a050c010b18 66
    0x2420b007054440307071030b0740070f43c000850480d180c04031443e642d0428940325002e0071503010700700d000031040004070340b59041c2421215020700c040d88070180940c042407118949440311a103080d0051090b104000324901c00342c81031101d0680100e010f80a1440c00100020640b4681c05a60405602420002e82da848004001490b405649610903503030345c49502498018004603008490046000140e0f00e00c2e030f54102000440000c80c4646000d50307204800c00b00310030750050240041d010f40000000076058980703440d8144d44800180c0c00060440c00d250182440d01d8442c4403442c429651f80d080b803080e11211451180f00502d0219419440d41c9002c0345030079280c01401e080041c1c0c81c1a0000102e402d6102c100c4181c01074a04007940e24481603407842d015002e8031013a514180840c0e030000b03000c5034a00b0607000d0382c3c0c070901042c2c41c0c210640c01101d041520000180101ca092403100f400f0103d40020207000170402c054150b503400361a8064003039841e00b142e2424105a2060041e0350b54020710b9030101c82c200340e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 423560044 1250 423558794 423558809
    0x2011a1903110a0b13210f0212150a140606040b0405060d02070807030c02040e010902030304060e120d0f08090d0e01050f0715061e140909120309070e0702030a09 71
    0x1105102c88011500c480d505800007008070301d0100b40d424003c0340721000142120001c1403c8a1400309960354401070034610000988403400001c550700c09410803045d00303491462107a0841d2031082c0c5544180c0d200340b8040d54240c03082c0d62a0080903600b020b5000348140c00200072543c00d0319103443c02d007002c2c660384502c3c401c080c0100c5010a1303050301000c00b94190f031005500844e64950f10303449881c0050004d601040f040340300b81c3c07412010545605051090803040703680a4000c510300340c24100d003540c000c159402e1051740312420800c5035400c0300d4103200301d0b504001c007900c4000c12500d03840005404584002d1002002e90310152029800c6a400381d00400195000c0c00c006944010038140d402003449024409411a60044820710400b021036210320121000b40c04514120780d1a40d8030b5003180546403040d0241d0702d1980204440520b020042e05801440306811581075402e44003813a0919002141c1c107903819003280e1000c1101c410b0900c907250348a0000c1c406549845502040540300c003565004100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 423561151 1107 423560044 423560063
    0x3080717040c051c02131a03010f0603020102060c0a02060106141b0a03120213032306040b0702060105040603120f05091e030c010c0c0b09010309020d0302011a1903 72
    0xc241a90086c0b419905c1000c4040c4400a084980d000c007040040045100384e00e940c00740302d84407030b441404402103074480c618000681400b2000340100e20745101006801005540851041d0554050b4240919406415601691603026070880d9544041811601c1c1211110000c0c4020100748a541d8a80d11410480d039060305902400c04c1c4480400c98008003400080d0300c00c18000300c6860105240301d28200000d51140c5000c030151829101034040f402804030680d03040c010f09001d42016102400070798690394414141145180d11b031402c0050842e20f0340e00b8140b0640c203c8000d03035801800003c0300d0340040400e85944462881c1c42d0b219100e5550114015401041c100401075040791020300c43d107140c0742464070b540d440740920311f04160755100c010300141d60b14500840c0041c000d50000030f01c01c0c44000030107041944884110711480c403002c0c0c05034501c03550707074409810343c0d51240c1c105 = true := by decide +kernel

theorem cover : BRFrame.Cov 423381294 423561151 := by
  have h0 := BRFrame.cov_init 423381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 423381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 423381294 ≤ n) (h2 : n < 423561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
