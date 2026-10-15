-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5261
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:16:51.069496+00:00
-- url     : https://prove2.me/submissions/fb704a33-1d89-43d0-a2a8-99f745008dbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 946043165 ≤ n < 946223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 946044415 1250 946043165 946043171
    0xa0905160b030915100e04030e03010606090602010b01050414040c111603060506030a120807020c15040f170a030e12010e1b0d0b060d08040512030a12110d0e01 70
    0x4020a00014422009003407600300c1d20b940b0710f0200c1e1242e0400e5003c141040781540c030f01e001e000019040340d04000984400104401c0c0603140c3e0720341604c500c0542d00b6141c0c2c140d424440000740c8282c02c0803e040413644103400030700040ba01d01004689070b10441c0140da060054505200382036040a034401a52842c3c98104075012070407000d68a8541103103020105942005a941442000564020240c0081c000c0d002449040d4850b80c0340801010107104c0340040110090009620f940301f04500701c3c80c040080c00f030b07803200c1c0c56042c03201c40c0d55800380c004c1100303011005800046410102d0030860202c01c0a402500b100106036a08840050080c4030b1940c2c401d46054171110308800a124068442107440000e000584c1091010302d002d1702100e442e180f04041d0705414102290311440810f51000d0704949649055a580c0340c91010340c022500119001000d40d84200c401d84800401081131144030740b0f035011040c1d680304151090351641ca50710384404505100c566517800ca036401c030001d2045110008 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 946045665 1250 946044415 946044433
    0x1c020106240512010e0412050a080f150d05100509070f0611010b04050f09010f0507020a02010305090a0623090307020609060703090b0a05040501030e01020918090f1b040f050702060a0905 82
    0x502a503c1c20b81000d411210400c051204002556a0105026110341800350405001d064040c2002c500246601c6002d0900000030705504021040c140d40c1e05402800300c24071040c80e081035035883c04845404001c41e03142501245013110001209400c5425451107056400d0030300c0800c540c4c0c01c03070902c440061503480d80240912a507031405030354810444603801440a1038090102401d541c076070b80b0000300240c90a000e1110707107640801c80c15501d42d0217090210b41c40c1c840300401c0d803512010310300280042c0e140c801c03c6048012403110f4104c10000440544100341c4030395041e16141e104406000b94415400c1004041509082c03000e440801d02900b810f100fa1765031141e511500f54001d42155000900001d010b0140750f07010701c558a02d00c0c0285000b18101681c504c0400c46007506151804d01c00c10000c000544c48039010401e80d98110721280586d5501166104d0100e89000510f400318800c80c108200c0842804484c420307a88640300f99070040215445402c8040c0040664040a941c14007401c014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 946046915 1250 946045665 946045687
    0x705010b04050a1406100806150d0908070203060f102d090608010c0c120c170c0115080a0b0c0a020f0703110a08150118020c010507021c0201062405 65
    0x14443c820011282d0100d0f1411950601041c002401008075100b01d00d240c845c40d0850358012003d03035015209072402c00c00c960740005402c000c1c1c0610f0100c240700c01c1c01c2c42c050200704015040644a40c510a0b012a11540c4840aa24038605012100381078211848403080000c030052580c10301041a1502c0e030140c40c4943d0f100700d0000d05045400500d606902c4120402c0318503001d1003100354041d1289441505183c095442020300c0800400c5c0c07030100f02420003414144880d030046071415500c21041d0607900d074008050131740a40a072008001517900042130024091002003589400f03254450340c00040c1e039440d05000210b503000114402c086206001d54540140760401c41100a940640340f502c48020506081107550503503504a80301d81e07082000e0210302e1111a030b1505064585141c486142c1d8641c0c0340340100203001e0a81540d12540c00d0034140500c1a4002c22030703007004000c03601d0040c3c001000d0941030b03090b207000744581424040c003046800294030f140070030784014075018a0003515214203082 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 946048165 1250 946046915 946046921
    0x4020406080a0c1a250204020f04092c1c020313030303020c060c04081209011803030c0510020306150306130c02030301060207083d0f0e01150803030c0705010b04 71
    0x8000c035065480700c00f0501100c40b48400400902400300328a6140052040c4c46032142054248440c5803007140e082e035402150742e0364044d01c0511007280c90302e0752241d5682d4441d4010b0201c50184240d05007040001d5041a0650240d00c0303e00605c51005007001c14548410524401c050107502d02180010300c241850b00740780e10140c00003503000340d07400f5031100c9034415028100400500341c1c0f444210704007c20045407101007a01c040f900c101e1700d402074445191600680f0506000407068500741c0c031042010041580002c1750030340c014054000c9a00f843c2e49012840101c3c8800e90b82950301099504200000d03440c03c1e00103540c4154060000124540300b05400400d0358421507030017015030400710051260030340c104240f10042100500510079000718940700c030418400001d051002c0d885d4030080420755059803c4d00e41d0384000b024001c000184121262100505a02008180e594241605a4001f45091100c0030917034400e04065440d5440300410002e4a52200b03600b00c56a540700c40001e00c941e542c0344 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 946049415 1250 946048165 946048183
    0x60a08031303021206070918020c0a031707030e0616020c0406032a03150e0f07081f0501050604061b0506040b040204110315010e0a0807120c1a070b0402040608 70
    0x307580d42024298410084407410b41c0c001000d4a901c12010003803d40c1d03210410500b150308080c3c100407100c5124070014060b00c1101b0352907003503220700701030f0104060703005c41e0303040800050100a1816031500c3c00b045040c1c40c0b40078039000c1540d21a20202e0701520522000d40c01d1810305004503842d1000600c040740c1690038581c029241c010f000120448409801c0d80c090710081d0044500411450a564541010500ca00ca03440c000700d60310003040940540400c0105032940c1c1c05411198066030301c0c81e0465940368140c0d84880d80c046c60b001d88203044002409403e0590704020582803c241c100a81110f04421f002c00003900400b800030b0358000301d00309000c0c1c03602440c0200c41030b2046242a0041c00107841a000080e12019010001c0002035488400e100c40f85071000d10706405000c54142c0044e12014040e0490110b130300640c00e0010b5010401c400f0256a40c0c03199448102455a4107485030306803807203030340b1140e058008101d14800600604800303644184010000190580c44a694500e819441 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 946050665 1250 946049415 946049437
    0x610031b05040f05010503060f04030c06180f12180b190302120108030301050108071d1002070f230a1203050304061e140114030312040606090c020a38060a0803 70
    0x13510050005003800e004083d03100464904242090401382d030700a02010424001801240e6528060400c80c9614040343e44c05070740120440000300600e00b000c0f480252031404040100e1107010007144514a07000d01d000403260400360071810030000041d14035902c0409007043c001c0650800015158025016029010b842c05200542c1c90b581007400144c140e000c0030703140d0000e009a1071290f0450380c50303070b85d0b880940c070000791000c14404c068001c040e45004202d40212103098092000071500c06030b40c0c1c1000d21090300b0101c1140840124105004c080802400f6000c55034101c51000c60109024034000c5d034005114140c0052a034108014103400c82c020118400e2070756849103043d14a10b102000a94094805140f070305401001500001c0e5407072140689035400f50401000003828400140d0184004005482003400300c03200080d03009464100d00c410449034160b0007105051901c202c50308290742400052801d80328001003d0142d45ea08074003d0500740d004c0c0f10b04030701240d080c0080c80070784058980c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 946051915 1250 946050665 946050671
    0x90f0303031a101e030b0d030c030c290f070212180409320319030638030f0103080c0109060f0b040f020f0a0503060a080d02060708090610031b05040f 66
    0x75079218484507004900b100c0c04040c00c0c10301c01b01050b80d5040c84100c25a0741030400640390300302454251009003100c0c60152050407154038041440c2c4443c0d0410300d004e04c003840311012035500c4881001c04d0b80310580c0d29200590004d40364a400f181c102004240c103002c040084848500900d0016040e01c40d008070446941e141d986407007a85d42203c0e061100030038274080b0fa0341040c01e9101d0401c0d6480c040e11020212031140500b420703c4042c080d50000021788241140100041c1c841d01c0d2104081c40c160715800e03c54602042d480062458074416280207a031040069415a4a5034983c0340c02034002d004d0b0b000503075586441000004003036100300050100da881000ca510a407000c200b0040b030302203240035001c00f40104052140c0022450484284032481d0400d01d88a440d0b010128540d02c901d500040018400c4d44030064070300303400255491041016540303813041035071001c00031030301c40c8820740d80309152a1002d031007440050301c840d400304001403244860211082d6102c00040640d001c004009850300e035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 946053165 1250 946051915 946051937
    0x30d050c0d21020a0e21061f0f0f06020d0906140d021b0a12020f030313380703140604111e04080c0f0a030605040f02060a11060601090f0303031a10 65
    0x4161200f200360f1b0307080000c031409210402820941f80c10b40101551a0200b49011180c6144040320312613000d0980140100341082c1c03150070410200400b40a050054410007550f00d48442c0304011103001da407420b55940f808103050130f00c6028107800144007066070503024048800007040c80c10300d11180c1d5000b600200114001070a0a03407001020502c04021034001940021140500104980d0400018030290301c4480e181d040c0700c21100002d01180c81071a55901d031141c45200c00c0386a07881c0e0500e004000200b142c0700c0035400d41c206d800a1404011000509000076024500359116140320b108a400c0c0c0c40ca405034001d041c18051004441d04880300a000c42c00b4048041d0410003c8980719068036400414102d00700098403910708c1c1d20004209a460358001001c1040100d0940ea9055015000d0703038480701e555001400c00280f207a10110309108400000e0140e600c520400400c40381e01101d09607105003507403012805022105094920304040d244941d0143e203611405403181c1120390343e100701c144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 946054415 1250 946053165 946053169
    0x20d080d18051c0504062a0b040c18050403091e1a070b10050904080a14030109061e03023d03140c040303050414030c09040b06030d050c0d21020a0e 65
    0x3100260f100402c014041c0070134001c0342e800034542e000140721b42071408414890144801c100c440b00c0b84005050750b526009010821110805480c20781d5008a002002c002100c40c240c000c947e001c40e0302500003640140104404602d00c0c0264a040e44094800c41015403221141c0640526140444006000010b401000c1c84520280036820014540c4114072052511000500d5042c000e803000e011582c0c0002c52024060040700f0300d4928400d00c09000741c0360344c1c0d80d26843c0001c01d910300c41d0006c46040c1410769040c1401d40481541030746d50082501c1481c40c01c0d602030f04840955018040343c0b41c901c0811070380020902040140050200b9540480c8aa0760001303030412070b10024110003409501400240000b903040015107003076072400480404456040c00000b8980700307101c00c400f42c100101905200c1030098400a1901c070b0401a4104c4441d182044804c40f1603200d11030804042d42c10450144121511032050340c00600036032540443c00e11441c0d18403104030780c80242c0220104054050861040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 946055665 1250 946054415 946054453
    0x1e12021e0115140111010533030a030509061c0f0615091e0504090f020301050718050d030207050312030901060501091203030c140c07080705060403020d080d1805 71
    0x12a00c000740034454840000042c44a01801034554003c000303026030a899115240f05501e56405100074002400e040c04103001e41c0c0c400e00c0905034500c000e46070516103100c181d1828400c2c5440a0000e14070100ca54401b100c141d00110300050380018204010003214081c41c080400203008094001280000f00a409044562f00d60024001d210b2840428281542150600b400c46401c1c44028198010f1000104104a03242d00b110b548185400449002d03c40c40c001d104032020b100754000c12031070700c401905498003144d85602c1140c24800e80c1c014001814030795445d0046901c24011034411070346600029060042e1606070018408010003081184179007401104000c10003800d040c2c0350103003000921000d107a0a124013070700b4181c41c0c035900b00d1f505200d11100b14060b82d551030b005403209002031542e40c8038101441040d1103441075600c045183c0c50484200c8003120b0740244074182100644c2c0c0c800b60302d508081c9041c5601541c88090650b81c1c800300080c0c800440c842c6001e0440d61059800c50b10740 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 946056915 1250 946055665 946055713
    0xf01080703030507080309070e010b1b0712020d0f050d08090d0302120601030e2b0206092b0507080d0204151706150408030f190c020306041e1202 64
    0x4258800c400070004203402074101d504407034002c945c1c01c2d036a80d52a42c40390301d0a000b0b9801302484480b01c0c00002a00004170000d443c145e18124400c1d10380c041d1800880b0b5541301103000d510141042c04820380e00524000d400c80400f03900c940441420900f41d84c0307813641402501c0000c880440d4002d0100680c0c0700e018481440642e1840c10f0450400054080e83e40750440000c0250b410b240d40c3e030200c4201840108601c07440c0c0218468003417a0380c0003407001c1600101d0341c200981c01610514000c946014404584900e0710718232100c2d50205da40ca40e41054107086140b0000e002400010004400417811200051110180249025a40e03500c0c0c00404002e101509160708100136040c143d00513030403007000d802303500900c0840d40c0c095103144070f9100014920a680c4000c2c120712002521502c5181424041c2000364940400801c01c40c24405096840e040c1c0e101e8020f44c1500440001070004846a09680b000c000180c911403468a02d5a101d6412030302c40c00292001d070740013004072203c00c0079190003950 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 946058165 1250 946056915 946056929
    0x3012702030c030402040e0109020d11010314090a020409080c010501090b010e01020c0d15061205061501052d0d0f1a01110703021c0b040317070309030e0d080906040801050f01 77
    0x116519200c00b0526460201500c001c3c803907601e031085a550710354250050701d050b540080104015244915200400501c4846000c0c0400c0c2898a0946050001c1614910404255010300284401682040000e2a0900048800365424801028500c900344a020301800f003041001a140340c0210024201d40c01084032581158031070300307901d13140351540b480c4000d5050f4450030f8100ca02505a101801400c259003100c1d41034111241282c080c004006000c0c2e000c3c1c1c41507012916000c1c0c04200448503840740b141400300e402124a2043e282c20083c6410320031840310004000e0800c2c0c0c0c03814070142600d03c1c0c4108240003646030780b00d450041184280d0400050000d007000c401d85101041c006440f07018505c0080e102c0c071050b0401a854800b600b40c0c008007141d00c2100d1020604e85442c000d0088001c0d070004440e01c8074a000012041030180c400c503045507401d6241c070904c00700700c0410440303503043d1544201c030110002c3c4450f0031151103000c05040a8440200003003043d141420341e111200710140d200d51 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 946059415 1250 946058165 946058167
    0x150d060e090f2b0f0e03010924200307030605090901020c07141c1e1518080403020f0f04050c0a1e270e01030c090b030c100c1703012702 60
    0x71042c40f00007038500c101800d581803000d100904484103542403880d00404076050b50030024101e00f000b0321211070741e0200318001140e08036480c0c2e0202c02004c4840540c134008480216107240c0001420800256034000102c2c90045a0540c554010410b410002d5400004036034001ca154904c441003884420040c00c04114004042c544104c006100f18500201ca20b0405100f00d05400912020f0720051092480c001401e1000c03078080c2c90015284000c2030070042e94145410a00780295402c401c00100090b00f103000d00b41418155009c000004e070649202030f501594403085101c05d51071341c5c010b82d84900c4e003a00440351a00c112075409005c4520200e6031503507903500104052030140d000031581e038a000c0030915022040780c42c20004030107011070390000d80321019200000004c20440c0f807412010b80303041000c1486034940000c14142e8450f428008107900c02e43e030100403101c0754819010322941350b01030303111900441002030741e803507050b4002c2c1c03c00d00481c1c20154160700c4468880e01e038003082c12441e001c11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 946060665 1250 946059415 946059463
    0x6081005040c1d12030d1505060304120207091104050f010c0b07020309100504050607380601121a010807020c0d0b0709051005030a02070f02180105010914150d060e090f 74
    0x5a81320700c240804080c4261f070742e03800d00115001da1140300003d4a405080203035607040c039080c40c00038403a02c042843d0051154980200e800b03c941c1c040c020f80b18000b40743c00350405041c2400c001c00b40640300402410825006030300408900c5010391640100d4054000d55501c1c011181030000306001c9102140501c00b040204000585825084504d07864002803d00b00c85501b14131011281c03e2030f40d040260f01c0710b02d04201c62a00b0f058049080c02200241c07651030500c0745048111095440c00c9025501410000203803291b194080d505c425480703a0544183d494504444002440310064150240c4030305048000f0030010315040080705000e0007044541c10002200d2190041079031000078107026000c4d4000c10034500304585508549200e640c020320b2080d030500388400e0880903003000d101e41400211700000c000381c1c07102c000c200d40c0a1300c5800f078440e240c601800b061011083d800401c030f030120b040e92001c000072104400072283e8010104807002d003108030101c03001c0e0703450071100c04460200c9140034045 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 946061915 1250 946060665 946060699
    0x30307020906090603010e030d0c081006050d05090c0a03060b090601080f04030c1509060e010b040e070b13030602031305120a1e02010e0102031003140c06030106081005040c1d 77
    0x8400d03030240b0212500691030f81e9160100740134000038100e00030702e48000324141d16600c1c1c058200d4104490155500c12580d514030140141d01181c0c2c1c490700f000320b6410021710103840103507000b09611200c2178040700c050703189520105003071040d140d0003a2006c65440100030030525102100503040f400c01d1800b0b64050030640c00d24032100201500040502038011000380421001c004801c260040c039180c103711088407418208040c1005900d220019460480084800d02d0580b045050300200c03c40100481ca0130520080f080d64004416440403407191000000003d8050000350321400808007241000d103040e103012441d000031010317001d81401e02070000181307542c1c0c03005100c0b00e4000c09038400c0b070407a818000d00b40e004040342221100c1c00c0d4000001c1158682c26101e0142c1164840d0450000c1c603085028810b440300c0a001d18a5032000c9c04000421602c3d10900901360010320a0320390310784031540c2d90001000c07a07811820350b9004c5084c3d1941d05103025546602c0b400c0d401d600383c80340003519080000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 946063165 1250 946061915 946061929
    0x10f05101412070302061c0b0a0806071103040503010c0309030914152b2f03070c1a0a06050f030a1211010b040519061a1e0f072003030702 61
    0x1c601d00402c01901c04090b400c0d01000264021600039101039620104050481c2600110005540101d400d2a10144050501d031010404860742c7e030026128607184d0010450706050030488180c41031105010210f165a000c5c82050305041090310000790a00c09858003030032114803030f44141e9184121200005880d16443d00c41480112100400743e0b03a810741182c442480c0d24014000c0030002c403842e980543c031100540c00800104400100c22400c002c205041c1c480840350204800480d640500200302c68600441c8129051842002010401c6c110b200000d103107175000316021101ea0740c48030020005801c0c9041041404d05065010300181216a143d004006160702004c3e41040300e03026003940307512020351000c8a2020b00900c14005410082e4006250054420056450303d00e0700d80c00041c010b101c018200007010a0440d4542131010b8600043c0c2c0880d007181f29559044810050300518084210003800050b10442601a40039a45e0050424102c10400c015000303500403c08000035a807562 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 946064415 1250 946063165 946063199
    0x1e05030c0919200c25090c091e2306090f0d050d030b0109120519031b0f050c060c060c03060d1203020c120903100207110d080c0613080702240c010f0510 67
    0xa034012440c0d800a000c1140c29800e1a0f015205a50a001760380d100f0318027102c4c540c0204e82302c1c0300c01c0706414880d01800960702c91502a015500540420120599040065031065004401042d12a205240c1d4561509168900b800c00c80082c1e90b64a80d14011740c0c003c10400060302c85c0c00c1081d526080b8a56038a40e4600e82c40b5120480c06100e002d9640c1003610610460800101c0308840c801f5440e03203890418442850900c0446040c01105202d8185041c440c0548817101920001041991a00710441585603c054031803908409040da800e800329996004142c1030038440d0b03500603520003403003480c1c0c6d082c1800c000340705201c803004010041c401c1e90001400300d604000c482c001030740d4584030710348162a954600151a0000855400001071190102c050004900140c050710b2465407140380840c400301d071520300101590000d120710320260600d20080c1100d45411510240802c030f40c0b412407603d9410055803082c00b1382d1200307042c06041c8403d0081c1d5402840c4031064640c4141440861402c0b14030308 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 946065665 1250 946064415 946064429
    0xd0e1c12050f04241512022707080403120c09080606030a0c090b040f14040314030106050a0c0f05060903190806030d0c0218011e05030c0919200c25 65
    0x403103000309290100e03809100a4106594005d0199688080300ba44041c94040d059104401c040d003400f03a2001e0801c48014020540242e9800300d954240341503954250241c42a801c01c4102c6244031132a10a0380b02e00d05584007252240e00034076181003000b03071412030000c01e000d010b60082d64036240010462014041661400c0c000402c4070131191000c14010050f860080042a060010010113450201040c03402a80240c0c2e6028108a6241c0000a03d00c028421140091001c00900c01058820795032422424030482030f6144440840d00d03024a0640c00740c40c1d80055420029060010946021111460302481d00341142d0031304c3d2900c0000c4e204d2101101c0380c800d0045403459841107580d180100700312030501e42248802561108285d808031701c00006c441401c0d0364252008240d41c0740c00654590030700720042501160380d40703181c8000d56105c100b10f51100030546405054103400180d10808014620b1107a5242e25504001f107820701d4400b040480000b0b4101400c41000c00008440b6040160307111 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 946066915 1250 946065665 946065713
    0x2010e01030e0c0a0b030709080a0b0a09080405030102030708091006030203060615040b0307020102070507050d0803060f0f06070615060e06030f33030106060201050c0d0e1c12050f04 80
    0x8141d4102e401d01410b00b00142d408045414080b03124a05200514002d11542d59855078041d200ca0b281a65500c0034074001d00300b010070070001b1707484002c3c58200d0f400e4a840ba001182c281580c0790007007801d9030802c4c2d403c0d42c0800c1008040040508082000080e600610803081c403d00b4a9500400d0300c541025003c140103806800c4003808808002c1d04132001888402131144d0b491500c03802c024000d400005040b036160003452030008207481c041107290311050b08000014950b4491404000d890000e070030301c0d141c121120703136000b040c3d07980c861000d4000c960082102050a0031107038040c50310748a190304848180321403103020540c1a243e85c0190b03a84080754004100c0142c803281400652031040b00d580060b035110701c001c40f200b0003101100d02802013000390003d200742ca40301d003000c0e42607a10032642070609200c14004200c000d05903810507074030200a0410345114a5002035040c120104810300361001c40d01c017001216070340103d441550b0b40a000c980d0300c000c3c00d050641d00d100c500442036000c210340c240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 946068165 1250 946066915 946066931
    0x39050a0b090402130e071101091205090d06151d01031703100504050c0a110c101206150810060807021507030b0d03020d120e151009050f0411010c02010e0103 69
    0xe80f581122010701c11003078958201d030781c3c0300a41e1054070401c503110b40c0007a015405400b46003005014580c1020762000355110b42422840044410350000390000768410511055800810818031403203c030100d946001114182c10284c62140b115150100c04640001b00401080842c444800340707180200c0d100c00350395594032003500c42081500d5a42005520502d00828441b14680200061074103010329160034054810212100d9210710000c07105c99002015078a502c90954440c000607041d800386410000707101502d07410302c0c400710305480744d0044c04101d149050200401802c03032004014000c9280111041c0f409810003511401c8540c8071032510000d6002060803640250070060f50f480015001c00c10034130050074000c0d40d80c482814080701082407844504500f1209004107029200c1c807100505100702c1d000075440c50100c00600d08803e00b101d001010800a0083c02001d000700c0588040c4010f40c14a410001d46450141c000da80c1070101c0d0b0322000c40140d810494401a042003401d000038421 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 946069415 1250 946068165 946068169
    0x516020d020a0803030a090209160f0807020f01151a040312260a090b13030e06030903040f09090606050612041407050301090b1b04050a090e0a39050a0b09 68
    0xc082c9400c02240c60001008005000b01c0030b81c014030160707008a41c0c003030300741d11032900500e4100c40580502c80007442682d1300302030b0240207042c030300d80003100d901c103d0702d2401e0421001342c21101d040c1c40e900800b03405110100010314900d1024004004800300b514a07040c550358488020101c00304944050014080351201c80302d4900c4404441310b2481110400145002c104070030050403030740c00844850100b40003080d410201c2c0b60110301c00503813584810607070301c0e4800c00304a035580004000314158441040046424807403014214000e10101001041c4503180d442c000065030b50981185000e10803d200c1d4801c030809244d003454009420240e0b100c00411402d02c628204120f80c0c00103501903003880303520300400c0154001c142c4581817010660880c0d6000f076881503801e104500c01c560b4841e05020f81808100304940c080648603590600b00d031031160803a0b40f016043c2001c601800f2102080d003100c2916024440d0f017441500c460000c01410080c01c1a001400c200c07414040d2400c000800b2446800c15 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 946070665 1250 946069415 946069429
    0xa080d08160e0405151f0f080406020408010e030406031a06040311030f01051017030405061c0b0910031401050103121805060408010c021e1903021507031a010516020d02 74
    0x18402078010b100c1072508440b080118030840040f540105040c101c4881c03604805280d8446286c6255565000d4800c204011940000050016504143d0030000040c08410921a03026905036902c061a01c071880c0c10006412143c0e0a480000d8800ca00c4107600361580c1ea000c00c6a054030f40c86604110700c00300d00400302c5d01d0281c200d2f180381c0c91340d071038941404103101e100f540110807540e000c680003208a180c1e40c01582c5a008600c01d1603081202071111880c0117080400c441d95450340d500000410600400000d40c81c9402900c0d144440d184c5048280144141e5043c0900c0c04443c06000703001a5245035240400b20b046c60110204200120744103024581b1070211410042030024100c82c1c584d51254000350082c804442004054401d44549100009504090320000742030f00c1d000e4071480c81c421807030403000070b2070b03810032400c5020305604829901007101410f400b0b4141a9000141e51040b50440c41904185d40e081074180300c018040230f00f03101c101d40344c00c4500035810f44090341841c0f4030b44041204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 946071915 1250 946070665 946070687
    0x2070f0807061e05060f010203120c3004020a083d020f091c0f0204050c0705061509070e0a151b050f0105010f030809040515040c020109020a080d0816 66
    0x3282c096441001c3c60460305802c85802442d044607803d00c0d50251800690341c03442124401500d403d0554001403112082c5c00c0545106003d10401070200e0b0030803803158480000744220304084007007180500c419402e259403104080c161040003030011140c0c1e40c0c003407070f5950403626800e036240c28112441007031350320203000710007000c40311300010754450b0368604c000781194000c05411401441079440120350030885c1510107020301c4e000302c02025044081d80920014000080c5480e0050781e040081c6000035004120301072266801010040401c54000104504c250014240000b00300840010855035514507444004442d05014050204443c00c00d0655201e04100e0907002d0b51821220705106104011900031500403031103008004d5030313032142001c080d02000c0307000150031024140310301000e03420541c0c00f603904141c111f1055848002c2d5180014240c41101118a0041c0d44980001c000c500380500010042c1a21502404d218140c625005103045001003000c03240b180c0002d1051003280c02031020402c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 946073165 1250 946071915 946071941
    0x120605390c150405060c030f15060405061c0507231b0601080703030216140904030c02060c0d121a01140c03040f0e13031202092206080f0102070f080706 67
    0x200e070740412180461a09403c0710103680382c0c081c0344000750400d0000403c60b842810143d500011a4a6000d0185091581c1192107a00203404010118075a80d404001c0c1c0040300503070000999070241403603e1420346601815201c20b026400c039400c40504141c1c442c1c05a128240e00d00b240d190340280e042f0300c800800d000401c0c2c3d52405502c00114224101180c01e070b050320f019408850b4508410810030b076070342005125a5403100d58a8400103d40d1901c0028541c010340645403040c490107030f54001135113a41c4558400940b90340092800c4425513085140080c5600c401d8008000524110b08592504008078141904114a0400304542840c5003000d0f1041447e41400302ea03100c5488da6010b0b542020140a01c070010303450b0000080360030005c2c80074031072881e034140e566003034005014a50a01940060000300d60129050001241e1030b50b1002040c0d80d00c000040700864120300d008080c904003082a44680921f034010402d100200f030710114910142c0340d110340b81035076803d60343c10068003c04080705156 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 946074415 1250 946073165 946073173
    0x60705040b1e0a031512030e13020909070e12010501140909030c190309050910150c05010e010501030b1b07030f03020f030f04150e0c19030804120605390c 68
    0x310f0502c1e4503170b100b8044035800c540c1c4021800d44a101c1c2c60301e007a0101a0003000030709802401c0c0c0031401d20180c03060410006443c0541040c146800003102c00f02c04031500d100065001d00b00100c10318081800d50071900f9070f80020001c0b54180a5903a40440c10700e443c5501900041021444e402ca042089404045000d000d0340c440051140c0c0000f0a4404032009400003420110701084c2c1c0e1401d81c41050040400105c0e0880303103481c061440000c90808001c00c01413004154003140860b0080c02054901c9504a000142c90340c110b00e4064001280070b130010242045c9500e4400448240b80c0440f68229003600b08220280780d01441200030748a542c0d21120700710804010b00500808040360580583c3c490003d10580e485940e40e038104480410601002e00e034007203038406c0d00d941044075403182580800201100c0d5107440340c544103a107600c958030140030181000d902c5014000d00b03208203074012a0003071413110000c0203900390780c0500e680c140401d60140441c021800d03002440c83e017140d02c201ca008d0151 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 946075665 1250 946074415 946074427
    0x807150915120b0909030711030111041d01060216030b0a06090e061008060601020304261f05070c15050a0f0c202b11010f1b02060705040b1e 62
    0x305002d629502e8841d08500f002010750651501080c8944070342d0100c0011410441103850f0484828420008281c241d5640c0515071903d900c031400a00140459075030310300d001d0040c07890300010348105034020000c541100d901c040071107606450351340459030001180450354443c269080000d000c1580142d00d10b5241c030070403e04041010071882d105884403904020500ea03070b420015100e210441d1000c1c0141c00401c4244007500710608030b203482c0c04e82c00b0348015402000c01c850618192801070000c901e00000860500140040d00406034041003d14050312a102156110004840050504d001c80c0b5101c4001070361088142e0702480d01c82c0104c8806200011a0f020050807a030300001203075902401422220340e003050006600f04030700180d0303004203040c0182c4044903101c1c0b42c0c141d481802040814007200c05400424064007480030030070080022490001c1c17907018400c404001f4043c0654100d1001c00507641c1c0c104041d87c1c126002c00c0401ea50704d154028003921006030304c0c961074411013400301e00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 946076915 1250 946075665 946075667
    0x50f0a061b0801050924030a060b1f09090515030109060c020c060f040b030403110303040302070f0608090c060f07020406080706182409030f1110090807150915 70
    0x10810315010420703044800700d2080411a0903403001d018094112615901103142103802c0caa41da1415544039000320b0008550f0000a414080e10342c0e0305840d201d854403215696032800e03040003081c1c0d160941c2e21880391140000040d02114061003840401031380c407000200000c06036000c4102041e0010000c1000121a191000007080c400c8164001841004400c040c1c1d81003501c01c40d80c14140c0c0c080800c0c189440d01040c41c0c060b078030080c000c400300010340c62402545001040a0741c001d034401d80250000ca420009644614010b950115081100540a100e012403012641107607441c0f00395605540e802c103d203028081c40c490030f00000c0d041403030004002442e10300480c4540035181c00f41c0e04c22070000e0314031102010040481c020748640c100340103580007030800d4012f0a01540c00242c180401030507500c0d00e5007a81e10f0030148080c0c40b00150090040071a28203100c10f010084c0307887c204140b209042200c01550307203403179004920310302c0c89044ea020a014054105c1200801d450702c400594002c448070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 946078165 1250 946076915 946076921
    0x711091b0c0a0b0a090c090504171b1b060901200706051801020a05030a1b020402070f060c02010507140f0c010c2723040b0907031d0c030304060804050f0a06 69
    0x1a041d208a01c011001c44d030b424400e40143d4810030340082c030059030360307040c952208020318001e44225010030300404001c2401083c24050504085c4200d041e21b01d0010790300340d944c00c1040203c142d44400c0400742d480c1200c0d0f99814141e45520070213180941d080004111502d5008103111848841c80c072842d10f0008078140c1c0304e8014002026031451040100a0b000e0069035108070b40707030b0028103d400521428081c180315003804065100180d5500500d401d241c0c010800301e0b4000740d000d60f01c0c49000c44007401484101d0140c0007030300e483c03071000700140c0c0f9208000070580b0060000c0c040400c02c1c0000c4081011000000781d0b81082040340c000c00041c80c0c40d980103802d00e40440720084403160513400381c40c495081c10003a00c0c01c0b20203071000654541390f0846003107403006001803003d40c410307074031259100c25860301e4518134481c2e4944d071000070300300100d040211105c2030070610b203500c0c0d0360000024041c2900c0c0401510304866960804404079102c602d0803d040098030340d130b01451481000a43c0c424003a80d90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 946079415 1250 946078165 946078183
    0x6110c03040501090b070309030b0c190302250b150301270309061d09060607050a290c04060806010c060e0307021512060f0301020f04170609030711091b0c 68
    0x40c130746200321a075400c80c0e01c40030b0169090107004501c41c0c17801003022a0100403201c1e88214602100741c03408040c0b00d6040000342d60b00f006680020ba01250083c101103010303031400c2c491003041903030003e41d00d4030343d03150303055104024004501c0142000d001d64036600c1c00d400c44849170b090003500240242c440c00101300005440101a0001012004006051801040d21800c840c3c4011b08450b50300028005221440001910150304901c00b0000032020a00500c03180d05003502c906445e14080300000740d5440c8100c050a0130030101000c41c13087c40071000702c0e41c04542c111401801c00005030340c0e503170700140c0f08201070807006442c1c0c03403e000301c91a1805011002704034240c402c03a0352540c80305c400c1c40c8441050081040502e8421000303804900d280c5000102c00401c03100c01400980340548000c2ca51800350050341c42000508440318902da0f0b240810300642da482140d102c0194100001e64540320070340030b120401c041c0184440ea020030490328000c005070071520070009003640ea4500c0d118900342d03510140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 946080665 1250 946079415 946079417
    0x90102030a20121302040c1706040c08010e040602040b030f3c0402150d061703031009020d0f0507050c0d08070909110912070e0606031b0706110c03040501 68
    0x2041100340100403450108000480c544240c10a01c3c0d50701142e0466001900f5420f69050240e104401aa102e002d840101840ba65501c1c40d860b2200c40103030140035002d03046920807418045c00e1010a544440f0250448661209034409516503040580080c030507a006264420310000070041441c0355042c8140c0960400520743c1d88880680030020f4111a003003150078009040300c80808103410740400040e42007170000b0075200c0e014039001703402c03a01640a003248104046e1560420841c180003040c4444aa5070340f407014628502d00411941c107504c40700d0003860382e21980480c0c2c0c00009513495002d40321515141204102c141003070740d80600207402120580034280f03d42c2c90011246881002c2441c090000c5450b0354405600b407600d001d01910010050f080031b80024007292000303940319144001c0d02c80002d0b01400380c0908060080441100040c040ca021b0740c420000e0204181c1d140d1840d07000c101c10341c0640ca443d880c036440c0c0f280c042c042241038202110004a4289066200480104215802 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 946081915 1250 946080665 946080671
    0x1914010b0f032208040e1e06090712061e0905040302060c070f080d020d18080a050a0e0307060816090503030f0a021006180c0215160c0b0108010c0f081005100309020603090102030a 79
    0x1404c1f1460744a66190424101725903191000302d5080c0c20124003840d00101c03e0305051809030104448c0c90103c40e42d640c020300003010031100c0440d2654042c0b0414014001003071043c0620302d8580c401075601c02028001c1024a00005520028007200226003803520b90b001440c1d554580044500704040c0d0041540c0e101600e03c0c1c03d645a04920036400355070601a0310504141c1002c3d08120f0036100c58018004080a00ca614045d02000e030780c0074814000540030a455110941c00c0c00588a0030034010303180700c50107000601000740031a68001054840da030170040c7d40c0d2540e85d600200103d00b0214800340c81c49016003010000b2a503407548890641e10311600c04020094041d20b900c0881e0b80c1c0c2130401d035030071100100401054045031502085045000b00d401d021480200c103590f14901070304260b020565076556907401500c495403102d4035817403001e11440c1030003042c202960312482280461007500d11620300000c00c904058041c2e0052403400e500207252903100c1c6070004101d8040d62046800c4215285 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 946083165 1250 946081915 946081921
    0x5040905160f08190f0c021c0206060d290601021606140304020a0b0f03060f0a030308063106170a0309090f020906031914010b0f032208040e 62
    0x640084806103100c180c0d00c14080601d44001698045005840200091520031164103190054010f0080c449000440000d20180001b0004c0c01c0a2003050040f8129613402c091820241d0700207200c0d500041d0032500c48407a02c10b5842c201e846552040c0c1e041d1a44201098043c09502e00c465409100b0075081c1c00b683c02d80d4825440f958280020313405440007140d8010500720702809088040e507030080c405030460100300d807250100911078004003054807200c0000800c010081c2440e20b90132800002c10740b40030301e4441c01c644e000740c520f041c0104000c0c080c1821940010301ea580c40c81c20944603a0704a4050300414050070500e50103001c09008500701c041c07003034203000c8505100003000d65105030140c6e07035a14441d081c50134a60241c5411000c00c541c0980038460f60b19142c0e100300045003c0c200403500e2107907181a01c5c07601c605842d02200c40c0300c0c3c2d0511280c010820348a40d6021075060307a403110800780e965502e010b07004a0540ca4240c001020283d40d048600030010118020030503107a104a084001796 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 946084415 1250 946083165 946083181
    0xd020909010912180603050406020c0312040c080106050d120905040c0f02060c042615071707080603100c09030b04060608100e0c060a0e042c060f01060e011103070305040905 76
    0x46040c801816409080c008000e00346c400e9202c0b6420500c0b4603000740c5400c285640851458010301039411311111100248000c0000151682c4003d0110350028441170380b6005c0020a24580008080d200c01d40c1c610b104521a0b00c500101000b0f8003000b4010800b02d5400c01e002841e104503255110098031940c00401d811651a00a840071502103003625030900c3c02410204035201c0400443c1c608500c6280f20000c92443d0511086118284965404031840c038181c40b2100450b0000d4104024445d4000510501d07450104d175084034118034603c00300c3c4c040d04003c4100d50948840d031014003039201c2c480c144820824103030031101c2228440000c49044a1403009003404030b0b59069896030305c0350300c1181009a0350600d0b502070100710381107042002c07800041c080440c040d60a144c0c0300c20002c02100c2c038040708a40c440c030310301e503c180e045c080185501c0c030f04044020742905040c060081072068000381c2c0c403050382c8145861306241160074162600c0c0d072680e18001c0c2040e001070282d200c0c0c0c4e5040800003107402e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 946085665 1250 946084415 946084427
    0x3010f0e0604020f2e03060e0912090307030b090102130608090a060507050c010c0207061d0112051317040e0c0c0d08100515041a0301180b0d020909010912 68
    0x240a034000501a00c1c0c03116401c01402210452260350000050340c1e242d018060f1240003075000b00c64508075041010b0003002e008048950740e803c0f10400391110350600c8a54000050b15050200c2c0300c01400ea513030003580001034a44242584010000d160704010040c0007001900a4059101142030084a168840e102501d0407101100c8940340799000000702c60100300d0903089560806107600300700e8036000b1284142802d4a008042510161b44441401c000181c2d00c0b20071200701d03000040780e90003a84900b00000f00a100140148150a0f4036600400c10340800881506070302680200c402801021020032040c3e20741151192241c1ca0310321342c000075841c0940d00700700c80240000c0c90140083c03042e1030400f500c0d0b024010b0800c140507201a00301041e140c50326100c0704200001c0d280c17120b0f04ca525000c0341080c900210303215020301d600700340b004208c0140c0c0d071007840d8a120b4481001103542c80900000c6200c1c0c4903030b9580030790701924403810b0120380c25041d44102c0314140110b40701d03000341c10130260076a01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 946086915 1250 946085665 946085681
    0x9030a020d0507061506020a050f060c04050402090a0b04061d01020a080901031815021b030705191e080306010f0c051e15040506010501020d170a1e060f0503010f 71
    0x1607040a0300d8524941c1c4501c00814071140300e030800045c0d44040e00100f80c425000d0f90880000340c0e1041040301c0901c8800c0120502c086545402415285445013070390009000b544aa207014640225114601da84e03031400e0280604000e44919445540c0c440b80102464803810009014211003080004194400704080c400a60044030403032903c4407007001100103080c81e00c2c3c0c40c0c40c0542c21186580000d80b090b4075a03002200d10000c0076854440002c1c05400034101e010208459903c00c0001800007000800e107a00c0c61390b038003042c01c01100c24504202d500040d07100018000000703d2120b8a041100190295000e80020b03030790014440c086c05000d072949460010050116800140c40521400d80b00c40303402c0540360400280c4110800041180e21000300960301118560041d8006229a590401c0041152006071900001e42c45244c80030190100010b0212540b440d295005001400400b5842c644001400d41c01000740a47d41e0120b0410442d15020310791095081c9101c61011035510f0043c022 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 946088165 1250 946086915 946086917
    0x1008010207110f041b02160504090f020103091a070c0b15090c0c0708011a0102010b031204060302131203030f051311060306010c020a03030906021207051e0106090f1409030a 76
    0x504040d02c000300300c503014043e891194890349a548100300b9134003110940380c030b100207a0010106ca110102e4407000c1e041030307900034501480c54012903401080000c203035240007030340a00f00040d403000c00c0d00b000b40044824001c1148080d908005120907298841d04820321980250280019510f841c0d40240081d0285280c403648410071401007500d80252074001c09003a072840d811503465a980c0c6880909445542400310035442001d1000c0560b56020300581041110450160081450f20303a80c404013401580540c400300366000c203089201d2901003500c50050b01400b4080d4202c844646002409803e050960642484c1040c0200d0801900c3d20181e40c015588403d040e43e10b00c90140a01c0b189070401040b0701c0c1080f042e981d036180940c40b1400c001003d18041e50b542489030341400d20180c5001000140101d41e1001008040d01140e00891424012441c0c8411804c10021420307425001d04410340100b18014a8081c01d00406040c903070140745401d19000c000d80c026511040003607264040d80103104 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 946089415 1250 946088165 946088183
    0x9090f07020d110c031209030705090103120525060509010e0102090607111309050d030513020105220e0108030a031104050303031f0b030709031b080c100c060e061008010207 76
    0x240c0040c090742c0e1400c3d1030749840d404c0314444058000040c1c60100000c4442c80d24960000f100e4103a03007000d2000300050b180542d0407002e1540345070f44440c880000028114104070012031001010b004440d58507035a4205019096108401d80c18000e00400060740e02d003156618061180c0500c95040c020382e441e03018010600d5040168a0700d58205a0300040b07001584000c100c0200350081e0100d106490001e4084e40c0200040e844084014040f03840103000c0c04484102d010782c2c100180e0740301046803c800d1051842181080c1c814001b0003442c150303504404001906c1d240040307994540000613010401c81c95800340b10801c00503042400ca8841c5006080c0c254104000040800d06031a20140042c44400039a80c03140d9654142469186c00680307024000500c803410401c18421040301811500c0b244000850b585813516140729514049800c0b924020a905e10703024901c50b004032142400305030070520500a80d0203104d905621072008442c2c0d01c1685960420208980d00140700780ca04c6254003184903 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 946090665 1250 946089415 946089433
    0x3010b1003150506031806090303150d060209130b1915030b060f04080604110603190513050709091703040b06040203060a09022a011e0e15010b09090f0702 68
    0x4030007602950b080c50b4002c840a040014450300d40c100250b05c50a805061103050f28941200b00d418094050300704034040e4402d00600c4800007600581a0380c0403000c444401d40d202c1c0d1403030604080d020384503c081e40a859400c0100c551142d5401020080744201d4424480788030303600b241c681c0c4a219010304245070000f0940401070b68020340c0304543e10400208101e007048818802c044191380641c03c01101500701d50240810000d06520380b02100000700c82090031403800099484461116908400b5000c3c1c035000030a200f904a81807003004a5002070680314503a44402c1e4000103007520408c00c50720700704a000c05070400399000090340c1c022940031040c6401500d9400420001e50030180c43c1c942d002440d000001000701e8903200800010000407420350403100040000c5403540c4592542c0243c590500321a50759805402912900300148203800044071210700034804c1c50041c0e19200c143e001d02c4030300000301d082034407000a804040400c0340c085510356a15011000c2140301903d1113009a4050002 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 946091915 1250 946090665 946090667
    0x703120506042a02070b0706060609052b0809041103270307030e010203040b030414010f0b03030403060f060f030c03060e0c090708070c0813031509020f09090a060f051503010b10 78
    0x290300096030f010f104a655080c0c0f650007140c1c07158003070740d412940c0665460302008008d400161a000924040310321010903804c045420342155080b492010344800140d14240c10000c90313105481c2c9516025004103c6c3c500e01101e920b2941c1e009507030050801e21654150602112040d21041504003000301442c20038525a50503641c2c2e4a040d003805055003c1840080340300703060030014612541c0181d6181c120700500226990031151a587c12908444c00c24480000e41d403000811141282e6200000023080e03144c10308000000c0c07040790029800086003170000418010006202c0c400d036401410100409660411115903440c65900056009a1881c000841c040e008030462940582030f0305002002c1d40342a0b541940e176038800e110040c01070001c07039018000d1000c0707005000c0c0d45880780f0381b0401c00b42d4013640000301c00e150180701042c81600b48000061040310180034280c54203a0100d01801101900d802d01e4002d06003c4030101d07030400401d254445a4a414040c049a0400185c541c0c09240003441c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 946093165 1250 946091915 946091981
    0xf0c0c02120a08130302280b09030106090e06091204050a05010e0607020d120f080f010b031012080909130b04150204120f05010617030313030e06070312050604 70
    0x8518041d0b01801c2100360209a403d001054400002d580130008642036104100e5407030041c0e03850704400700507d0013100001104440c400e0594102111554561160100090141140d40c100d603e0007824035814081c8d51200044070713800341b02c100d07068880000e07010b80d40d00194081da01c14643d0080605200f0081035008168001c1c3c1d0f00000340c81c0d03524080c444c1c0c001c10011031a41e001140e140c2d07007490361480442d40c00419000a184540340010190405000107408280180521840d6240000108000c00d01c80c0c0c005000502480780c1e00d180704142410800f42036041411300c140622034280025201c029507000c0c0600555205910b82d0307554517030307840b4500394104540b214003034650308010100c0d030714002c0c40d49500d031148601807100221482e441c204d802d480d01030780b0060f80100c2440500e1020b11020083d00d9024102d25a6205c440010b410200c942d1a00c0c40b10407900800001980c400381070b40b08280c0d00c88000322034024092911014140000c07543e25411820001c11005020010b074540230f5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 946094415 1250 946093165 946093189
    0x1060b0d2c1510240908030c1c180f0614071e03050c160810090c0b0d0f020a05181507061806110d0f0c05070b0405101a03010f0c0c02 59
    0xe201840c01e1311180480082d16003e412003603901d050007240112503905c9080706021b003040c0c60245090100400300309580d9218000e0a02000c40c03d6002c09030200c0c85806401507040032a03030258021036442a81e100c075801d03107000b84000161505d007002c072540d0380d8004844c103403584034256198011802c40142c1401052200481c2000070401a01c52031980800925820030180069216401e1629034110328002c004203c0c14055814015000302143c0d05038194012604030070862992030301e800603c0c04c02801c3c500000e4202c64408542c0e07445203544217001d040c0c041e2094200c001990555001c0140d6aa82031414046d170060801130a40014056000880f095500305803030840070299070f132480705880103070002c2d10441402050700580046240101c41c1e5079074240c03500700040a1440070013002440341b58000740032030010402190800c1404c001c08ca00d00780b12007500704a0f20f0041ca4220381e0b400ea10181f028429030071301300d942800080a114800040019448500c2282d1003503007440315020b882 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 946095665 1250 946094415 946094431
    0x1150302030910020406020726120a02010e2407030905100b0d060f09170909220b041112070b03070f05070b0c0d0e0105070f0e0301060b0d2c15 63
    0x5103d014040a000d070001c2c00140085401400c03000781014145074100002a10814141c128401030103490100404c0c40000500030120b8143d035203404643c141e0261080d947c0c90113052081d4500809010500b0340300c134209036469152200315844441c4100c042e00c200300307000b81468102298001b0301068944c0001005000601700c1c010f0319000b03440784411110380e101c003040c0080c0c941c105442004850011b200d101460082c540381400b40001c08a10981c4e00101354090040d210a030001950107480e440e5040701da40f02c1c2c61b0401900e800e14154108020040b495809800f524011003810240882c014003514004076207241946c0e0340c20340441e240c000c00602001400010020074011410b40300380c9511912500010a9440c2c2c0700c100034030b0490310509007030f1460b64540380c1072011240c0c0c001c2042c01403405030701d080c4890484050000340105140d41c0003001e2502d00043c01009603a0980000481c0300d050b241c0c50f5495144182840b031140b80b441003d10741600a0010010500d400700c03c1c00b034200d080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 946096915 1250 946095665 946095673
    0x516030216141f2315060c01020a0908160902030a060b07060902031b1c230601081603020105070204050c13240212040b0319060b130b13030f0204200c010b030303011503020309 77
    0x200303501150300d5030f000f80047d03100b50750001510003245420410710ba008044910040c02c00c100011703202910911a030040404880c0c000000c1100c0710281c1d0000c1c00600301c11081141c0d1032010385030a4004000c0848124000d02403600304031f02c2da1020358550307850300102a103100c400d1400d81b40311041440809204a41602c051200a0600c042810222500302441d10080c4401c0d410010424a41503101081c401085130a910038401030742d2000550300025410788000c2915225242c102d580d900a1130100d22004005080025840141000c02d10f80c140c8602c120b030801d1800283e08070303220a14503a4882101504000400404c215074000f10b41c4142c24000103518104100e901d0415903890340e1100e40d0b0b44101140b02d0303c007500c40200182c02408070f000c61500d04185140d100d13200c0501488041c0402c4e0031640c0007002d41d00c4a0300701d1510420107401610a448144070140e10a82103440e81c0c0d200303907103082424061404c0c0081124161502140c000844642e160000c40280d07100030002002402 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 946098165 1250 946096915 946096951
    0x62709010e0a03080717190c090e10140a050d0f060e0d0e18060915270103051504030c0213180305030a0c02010516030216141f23 57
    0x24003030102c61182440381e42c6910f000e04040400800080814000301000c400f9901032102907241380c05041703140e0030000004501603200c1d8000352003000503640800002d0071400708000c43c0804c51054a429500c07026000001c2241000501c0b0b0f42c04241d026454103c01c45c1c0342404041400070b8200e5030780900c07800c03000c104010003003c0f45041c2a01086030001282e1058051202440c0030b2800142007402440340300c206240503000103900c194054009121041e11454000c00d5031540c1c0200035208078502c0009e20004a80740c10400805400d101c10386480c016401ea40b245d046815041074000c58140d0b8600400740002c1c1c0030450001000c201e840b0200da40c031181d101900d40f02c1141d884041e8040d8455036240c2c540300304807400b41d0700d29105138011a45041c0802200680069041c9a0f80c080c5248c0140c590210082c0d041c0342c800748400103002c80c1d9289030640c94551001070a074030b4905120b0102a004200300c103194081d11030500303110240000440c000d21034002c0c00d40080340d100e094001c100340e41d20 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 946099415 1250 946098165 946098191
    0x1309050604062d0501062006360606150301061409040e0f010504230709090c0812070c0e070c0b0a110a09050a050603090303010303030b04092906270901 67
    0x950745458210700c05854800406c049500413071035180104110450780b014000c41c804c0c00342c0340c000c020700310212510f52129803580c158519001c451000d18440351030368210024200035544003400c40741c1a11440c140d81c024060320801205482c100d0701c0310381750003940000d142003681080c2c0040407104d801954500e400e2803101c404100c000796540e25a400005d9034106070411721094006660780c40320224840340f003064500d01c0080ca900403600c41000c0050301140600d0240883c007000e07408001c0710710400c0358101c4401c0f28080204403961040074180f00d0340c0d03620400d69a071404111181004244030112600125010482c03059024400884c000b0300f0aa4071a041c0308030380c00010403100020b1070320700140400e0030700308003a0014100c01c032607050a501d0b0100740c580d560b10050000400701511055900e4598440f03802200820340d0098004c5091a049c0c021802c03061000d00380b5404403070300040820344c0c07420048003844003004c40a10b809041e0300300301141c071038030103016000039440d650313a900c014548 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 946100665 1250 946099415 946099481
    0x309060804021f03050a0e030a050d0e19120801150903021201091713080c030a02060703030b06040b0d05070305060102100c0c020a0306022701090e090c0915130905060406 75
    0x1d1191524002220305010311440221541c40c00f14140d213a02c100270007010f0f2074200f070540f820500c0c0600085018140c2c0c0c9080d5052520382e00c028903201e0040508801004606805401915811340d02c4010903039940e40400840c0302c04480705d0b404a10703011020f20150402d10790400211086100104200ea0203a949080c05400703d00781c00c2465101103001c02010440044001c0249140f034000c04a004480f80002d03121302603910028800c1c44005510700030103000340c05c0501d0034180180300b652601d50702c84840d01a80d02c0307282c56003d000d03e03200c00a4150ba0203445080d0013200d060b030040c040c4a07421030580009103903076200a0b0a200c4e041c1500c100503650081c4c60006540f10b0b240143c0c548801c0f500741c0c01d440d60340301c0f021a0300a46040d0103410b50390340444600704480700c581e2140d60360f0b00c4410748a03082c107100841c00e6800032124002c0040e1400c4d689100c08a4030020346c1d1180751040e18001c80c1b000c0f075408010042240d08040c010901152258108180e114a01c2031140c030070190700100c41d003903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 946101915 1250 946100665 946100719
    0xe07050714121902120f0c07030b010801091104091a0c09130c170c19090509091c020307050a0b0604150305010c120603080a14090301020c0f06090307030906080402 72
    0x500043c1440c40b941c040040140c8600c0b4a0000b07003030300000c80540c0703410b0b4001e4595201c1010342c04904080d01000400c00d2200541d04800e410ba881d50716010558003902003840f01b95101007560840242604251045000d00c580020400b84040c0c00460f20702d80b01100540340c4440328400348014070080d503c031803030030052110006001a00700c544d4000508088107400f403201d02c1d10074600401080070044401c4681000c1a400074006454032000b06031090760342500002c0d0071401c01030401c0000c5034005a00d10040c00c1502c3c50b0b00b410041c402c000c0344d07a031290000040c51034004c0001c3d071002654200c8451707041342c0c00400101d641c99140b0f007030703d08460042d071040e285691910303901d206e074603040b4407040380448004405000450454480060b0b5218142c112002c00c14044035189029000c0b0058900c0c464000300295910242d0044090b92000b242945420380e02502c00402c54401c070020071100400c1e4184ca038009000d24140b4107580520000f48160f81150904420142c110031b20418615 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 946103165 1250 946101915 946101943
    0x7090801060e06030d0f3f09023303040c030f05151003120c03021005012309060a12050703080406050d0e070e06131103040f14070e07050714 62
    0x2070ba00c2e1a404041c9030500691500c002d0096064654880940c09154401c2440b102c2c001c0300c101c0914002160500703540b51074440e2074820b410840e2000c09035680c0008280c94005c40c1c130b40255841d1802c06a5084000540d0829201c060700c100500c4c4d24803140c0030310790260055200d804066503a03199007180003d90724040f1029003041000c0740500c880b0755209600806100b41445506003150344501090b030503207401d01c05002c00d001c00941050b10801007001c0807060340380309200a5940c0e05220042440320a061505440a125024150306140c0e000038807070b000c0288060640d80c9418a02520179103281425505401529004404510380b94000c00040c83c8075500c983e524403148550004071070b44800d1480d203035081808108500d510442085030403e0048592104400007100301c00d0042c000c1d615240c2c0c07800400f208000600c6140c4010600c420b00550b40402c0081459049075100e05803809414000e440b2a0003081c031842c40744016040c140c1c840d1006071a0840b0340d070081407426541d40200e00b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 946104415 1250 946103165 946103189
    0x9090f0b061b120a0203091314070c260406020c060f3f1b090112020903030d090b01080d180306180f0516090e0304051203090901030809090c030403080601080709080106 74
    0x1001400c1c0b1400441908c00c46510400081400d04a20000d42c0c10290000c420400c011891100f40160042c8203104508524141c2c81e2103140c080c210007154100e4444d2170b0140c0a01b000480384d070b040150403205040322808141d0b107086964030780c0c40140c1d4210454417100d0801c1c9000d83c1d030001c411454100440c00e03104840c1c85180780040c800c1c400c0c101c4001c0380d882441d00c00e000c0548580d0300b010f5040c6441c080e2810142c1c50700000800301c2d18600901e04403d001d1402c1074210410f0041d1050b040e0305072031108007a10850a00c0e52000d4a0356403c4502c60a13038051385d400b0420210703466901081d50398400303000c0c88582c1000d07603c40c0661806042c4d02994140c000c5403100710846c0c51002a54014101583c0c00d01400c0e21006c1481e0b240c4c00395200e030b14040c40480c0000c00c04114140304540c842180141507d40d0355071282401d100503000b201c00e00380508040004038441d4500c00e010340b4442c0da03055440214030750700c29004580c02000a0075442c1071000544011440020a000c1c060107041090820 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 946105665 1250 946104415 946104427
    0x40f0309031e060606031404020904110a06120606030606090308090d0c08010e0105060405061810050402121603020412020120060a0c0813030c030c0512040609090f0b061b120a0203 79
    0x45404c80b01240d02400c00d0500e03040754070880b03422400300194440e0301140d060300b082d40e85041001500146560781a840f01c2c01300c001041e00c0745c00283d6503c1c83c02201d03030100030141c3c69042c140c0490307906e4050f00c4080f80200200304001b84c642002440d42c0c2d50050149030290b511551144c0300b07084180c00094003a5182c50f00022081c009208096000500721400c0c00740d0700b050000f02e06c00c00c00300b5618094925106001510381c40300002c125009040c0a0030440d50340ae565107040000542c26244400700007901c030310025105200b402680c090364460100020303082c9032603005580b501c95141c0034410714440e07001401d0708644140b0445100743e02140d4003144105050314001d14961000f8146406500e200c4801404a45d1045c0c420092a40c10304110000c01c0d4a801c0c460714080c0410310210b0015400140801c1c40c0e07a02c01041e1003100d204c594144844084420302c003045c1d600703040e6541d40181061100c500300c54a42c02c8150001d460304030a440300ca03035120100f401258406242480568000280 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 946106915 1250 946105665 946105673
    0x30f1a15090a09032001090210030506150f0d1d0f060601020705090f1b0d0507261510030b06030c180618102006100906050603040f0309031e 62
    0x3507441104800b04000e0070340035640c058a0450120000b408251611621000385a000d6100e090110b4005092030901d21442100502a260840f00d030b50240d400d84c04c60b0440e007117110058640d0500702800c8181007030000030390310006114005243d0000043d028080107900001e01040c1d06414210700034000d2498020000791811070f5603840240280c00050810035035100a52455821031101140c0c203040c240404040712031400b4228000e5a0030745081e041c8405207800c07454840380020b95405041040c52204200901c0d050221125040b845050f45000303c02d140101c01e403004011582030018855403c000851015001204c2402002d0f000140c0000310129107801508400002c13100189040350400025a6054509069902810802d071840d24030600401c881d03407045c081a00d040030582401c0241c1035954800340da0020400c28910f6002c03c2c0b40000740103c000741ea40c0a4010f9196407103941d1002150007000d041902004155400400000d06645040310200d04c501048500c2d1281e90074 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 946108165 1250 946106915 946106929
    0x50729010305060c07150507030209130609050601050c1b0102032101090510180908070807030509010816090314070801140108070e1012140111070b10050901030f1a15 73
    0xe0150003040500030300c1c001030f0410804c10034082046c0404241d68a030320310140c0c00f034020701c5001540f00501f140c1d04071201c00254045011110034078420300464443c00b00640c0c40d0720904054030202e17008400007400041c0450702c402001041881107038a040c05540c070799500d0310220504180c14840074401005201010702515030806250300109801901e05402100e100d209200c0300e246150725030187c5410310034028180c60f44540c00556065a820f024980240706502607404940400c0c0c000001c180c1c0c0014602800300307941034544a00d05030754259203541460543c03044d05030107a072040700c1020800303450030b004104013400360786900280c82d414204083e0070020b0940100100ca130721035082207484180400c40c00100c1d203d0071480f140c0031860707040041c107891481000c04115803c0103a5410304003019802002d503070380910810f4940b500d991044a40303034041841000d034001c143c00c0041c0041600381054104007072003040040381072215101541080c8074211a201010b120545602303843d801c010b2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 946109415 1250 946108165 946108171
    0x3605060c0c0303041212020a030b04051032040609060623030a09110901030b070306120b01090b0a0e010b041a09011e031e0e0c01080f0705072901030506 67
    0x2032035400e1a040006881d900e01000704090042e1081c6281420124020086940d6000c10341c902591b42d010394060150180c00180d549500651a09000440503000003a05800762440070009840c80312541c400c0403510100c0c84107091113401c0d55040f410960340c40f03114a90042c000f031080801e4003850a04041c0810100f68010110306401e0184075911030031070b0f030031a58081c184100c002450056410031600064443c3c400d41c1d000668a0008000c0c00745581c401889a9840e0b0707000d100e280d46850130010003020303003c001031900ea2030170014090800076030070803a502c940c06004210116a641c1901520320020380c0042003c41000509120440003901c0b81804230010310016441c00d025030000078031251500c01100c05580050042030b26a5100f030f0407030214003030f560103158030865406034a1002800b000c054403405104008010105500440c0d00c0792040d0506490f003c4541e44204080d030340c0d40d00000782120460013182d103111042091080054180301605c4007030020b5810344c40d040345030013009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 946110665 1250 946109415 946109431
    0x5130e0f0c07030806011407020d060b090108030405030c240f121503060402280609050a0e06030709050c09060f0a0909050121080c0303160e010f050904360506 70
    0x20030010b0b0120381c110441303d030490401c0c0b030408000310305040595800c0c099624000d500066110000082c04940d800005040004584403c513690b41c90649030350f61b204620034150507800100d801c01c0a032400e03000361010080000298911001e94a41ea01c5242e4000004080316080200d040c81400c5009100154408940c0c4d03903009103d254800003966032080104003c1c4525440c050148205841015011071600e500c2e00c18021543c50710405404152207005181c040e540b20303c0001020b10b410010315002e0540a0003900407a0700346040240a01002015120807400c100040021a294140142480f4070382e20324141d1104091134009000c0c072200d5009001d141c0c100030040c006880300381034030003d028003054180d9141681d80b901200501407d038005c40640804006c00c954006021540306044081d43d0f2031020341c1140303400550b103c1300124008c0c0d0006e501401054660f0170143e005100c4c440c000b003180c100750001d00205419003c0401c404140c0700e000d1402d100c04004041004c95004150 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 946111915 1250 946110665 946110667
    0x18060a02060a05130f020405150402030112021c12050304080c0703080301030213050403050906210103210201020a0503010308090d12052a1c2604120e0102070b0a05130e0f0c 76
    0x226071121400300c1034045e40688129610004204d002c00301d109800c181c141c000d4015500e940e55581c104845130f40c0311000740c0c003846110340d0061040004040498030542d1042c0a5200c9045461040354070fa00b0003407044a102400704043c1094203070410040004501ca400c40710f03500c4d81184148003480c803260208004446c10300003032100080e002020355a1a4006840441d11602c94104103484041c04600e40c0c20280c0e200c80010050201d080305200c41c0740d01c5110315500f4003072203110403801c0384100401c107400200c1c14070040c00022400c40041c00840303802400c254448904ea1a02518044001c540c200410310005da144031805d800040103240da21505441c0f0100d8092201041e21008242c0d52020480300281c80c80c03c00500410040340d28a410550381100f804100b1a91500071b00c080d01c0c01d071042d886410800c00e59620070055403042070f5061313001d011032914000b0150303803e4204250007802d222040c41012540344540640708000c041e42c200018850030310715606030043c44040c2c100c09120790 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 946113165 1250 946111915 946111951
    0x15090207020d060c0c020a0f0e1029070506070906030b0a05030c0f060708030103061a0f060712030b0d050c0a060c23070e07080402120609100218060a02060a05 70
    0x507521450b10301c1aa000000410101455242180d616000c56002580440c1101d4081440d0075603400d148151610f8220484003502c0b022850300c40a0700c0c5205012003180010101601034000200c0c0220003c501c09000d401d10f2580d41d04d65080007400c585400c0010740c0d11034108480e562500460f00c11150640e42d9601c02c501f004007281c1c51700500d00c0c40500175102e40c5c0c03034030300507480e45402c60b821030707030000c2c140c41e1256141e2a000c4050308a0448204c0d8007610b03500c1ca075050346081c0c401c0203600b140c014161031403c030880c0c5d0f525082d40c00a500300c02c10b03d5039034040c050003910b800c0300c0e0601c940c0c481c00103401410a4a000c0049a010301e420140800907900400000600902a40002452407205150003c0504001c41e4a840c0e03040c0c11603800040100144401c2e941c0200955000e5482114140306281000b901560340d00801c40710307401c50394000080b0119428055006102c1803184003c1c00304400c0100c0049111980441070b40c0300164012010424a55011b00c03e0035001120071040000e09a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 946114415 1250 946113165 946113169
    0x7030f081f0e040f1212060f0608040b04050a0b07170a020307021f0b0310090605090604210311030702031b010c0512130f080a201506011407061509020702 68
    0x7648074002d054454401d000894103002183d1054807003d540400f0740f0811007100400203012080401d18003400c281400070100d0f002224043c480c013590026995400965101d440c0c81000783e50150094580b030080500350700106038245049485040e160b180c10b9503034410166802d00d035010043c40b41001074414000d00400641c082003000b00b924044903044034001c0404202e1005120300c0c02c29941c9441004011107101d20381e500142c0119000d40020805565110340094032140112802840744240d103002c2d4a00389030141c43d01071790321180e103000106262094850410341d803080da170314800342e4400300d042c0d0420031011101000080011000b84080034950300003030300034056010005c6170070b178540001a101c04507111400107420380044100c00b1090050030702d02e6642d4442c158540006422a08403240580c159006010440e003003001001d5500085034480000c040c042e0455040080c0a18040d42c00c0102d480a0020140a400005145080303542400c01000040d4440b000c80344c01844208056 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 946115665 1250 946114415 946114471
    0x50a091a07021204030f3e0a0b0c1e120d090507050d0c050103200d0b01090f0e1303020708060414160b18030102041203021b04201e07030f08 62
    0xc3e034486004c1e007c0f4940803504040d0300740c900e4410940114103c20309002c400088810000c0500103070b81220701d540d1156000c47c400e1003a01d11304c09403a8407402d289002441c102c9203250318401500156948090801851956517126aa05c1d8000da601c481402c0d00f401018007607440142400c445008103a50590754a50409042d48640c0d07061681d03808071100401014584404030390181d405040d81c1d645403000c0303134000309200020f00f40010742d80840840c6600f4203020b418187d907482e0900c40850307900c400024001d0700c009541102103002361070000130f8074401000610300039803003400e103005a5841d03440d00519002144824544810004a0402141c150342c001c0381c078003025402111100c03c1031070001c82d01910903940010388005124880c0e006240d4082107c840416444041340030110304101000705403000c2061031510f00004110613041e060a400042900c0807403400c061300c01a1480c201a1140d1300034810a030042800032603d28601a449094280d12518030850101c907811380e07035070b40a84 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 946116915 1250 946115665 946115693
    0x9150d0803130b090a120207081b03010e0304260106142707050d05060f1507030909060311030f010c02100b0102030403080403051c0c02010f03050a091a0702120403 72
    0x680080070580c0d8440b204040c00700140c00c1404007a842c1090340c0700c540e45d140405415600d4011688000b00d10310700c003180e050100c03500d80c13000b0000300c00c6485281e1034a0b1881c0c0d408541c10b44d40c0348000340c03e4500910242c4010002c88010148070741d0f05407041400000b0540c2c190481d41d250180038081181e03001c071010440d1006032100310042500d10511003100805076102451001042c0400000b5984800207210600400078240b05076100c403401e011004d105003206c1a8000c204041a0502c070740a20040d0103120b02a10380541c00300d0351203c00340121040380d0400e907124410341400e0325981c1000c200751103485072010000c1042000300d1a009450b12404010010181d4942c40d040302e03603038800c205550186400a0440b82e41c2c5641e031500b0369035507001c15502314081400014040b4468040c01c848089d0507010f848003c2d2025551100320014140102a61043c50340e501d01c07040810380d45070005001d641e103000419128200701c0f070080d240c8092001043c6c1c6000f030401c0700b8030000b51300069040c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 946118165 1250 946116915 946116923
    0x9030c0b0903060f28050720060103030302130f06090306140f01050411041a0408060106020a0b04080d060b0a020c09010911040e0604090206070506041205030108030912030c071409150d 81
    0x42c0303450b101815202101d92900c0001e60383c1019505403101d040e41d0344424010600354aa908007a40500254102401c50f0b23400986990000401000400c2c000d0b0001d006004a06c1203102d100354542d44031400070126a04841c1c005000018240708100d1184580d6000c085134602c80103140c507080941c03d400b00c2050140314000c075210030814000040394015134001e82030345081c5c84a040b207259218400d582240c40350118911070000001402d60010500c017900940041c101200303070b83c2d10745a0303110350b903c01002c40c0440e6542d0400005e00200d4080540084000d65014000103a0300e10108280c070351042e000a10079501d00390781c07200e0014089045034103e6010940d10601ea55036a00000c0090400e000d019400c0040001c160040010219459200e144508401c1540ca0f1244004940700d001c00d0281c47d2460b482006610150320703150480003900414001180d242405d0004414103090181e0320010301c54804000020984ca483c0035240d0740703d04000e11007031300e5101d0140000d00e00c141800002d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 946119415 1250 946118165 946118191
    0x70c06060905090c13200705070b07050d0c210224091b0f04090f14030703050313020a0314010b01030506460b0a0e010201051018060306050709030c0b090306 69
    0x21024a05030700b11400c02c0f015848541c1b0345080184d51602d16510214044070f10780202c81012503c00414802da62215070410000d0511440e409002d03146010960000e51340704108401003200b60100c40b0110120403100e9001d41280790021700004c03a000107106191080d0b500400401c0035440c00060700345001c2603983c004000d1403040801080350b20180c00c805503001410500d036681480900e00110407414403510000e220803000000d4291240110200100041e83c01c00200c1e0340400d0710500036030024002070403032510564959900e1501c021056203080c00b6519405050701640c1c151190b07550226041c0d030000690361440340d145030310b00024a4641201e00c0c808846905102a0003504120350007603c2c0740e40c19498440380700b05074603000484000009040507410400380d52040c06054003a420300c103001031009040c0310f40540e0040001c0c400d9595290388000001c04202c05009050103140c0b56119500241d05600741009001ea144d0032100311003404111808064900007036199124030210111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 946120665 1250 946119415 946119439
    0x1080c01030c0513171507050315031f06381c0e071505070c140f03031801110a0b01090207030c0b041b050406050d120203040e070c06060905090c 64
    0x40c2c0b43c0e80159103030142e005007540e070040741024a01c000310684d10051000c45510318200e00c00c070149000102d0340303200000c5d002d201160a100d003443d14102e04820090585010480b4003400191300c20725508010401034071083c2c1003103030070590605400d680c8d04507112100802c441d8110003005124091486502c228000381c035102d203000340340c1d40440d0b510f08010305010901c4a1907500d0f40e1202d00d80100c0900c0e40f01540c4500c01a800754080b1807505504c19038906203140341c40b020040c4899030040702a000340500d240c1c424259000c1c401080e80a12100c000803910303481c1400103003200c4185100c00d80355804003c2c5203020030f03907640c00c540c111040395001607a02c51080c03804880f60307442038100400340904071042c041040b40645184504800701111101c0c4c032030780c90003000203035843c40c03151039000004a041d41c3c0c00702d4071958511581590f40d00440f8034080d07851242c181c10040441b41840042c90031920a0100180d0b40a1140180140241030149062146905440d00c1c2250400c507c112004090 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 946121915 1250 946120665 946120667
    0x4020903060606130e0a0509010b1c06110d0e07180e03031501090308030c0d0c03060b09090a090c2402160506030703060f1412030711060d020c0a0f05010b030601080c01030c 76
    0x84540604111172441c0c445040c010350000260006540400383e81d401d255800b1001c1c10107a41403040b5008000c0d03000482d0915071540c03802081c4002600c2c1400310104003c44074501d04d800790000b0b0550704001002d40902c0c20ba01e00c0655044402041c40f000c0c1440e000a848200010980340c00095042160035590a610016525440103500c0140303604404010003c6110100b4060605540520700c1804041e20f13003c4200e00301c519074041d03d151100140f00040c01c3d814818601c0f603104001a500144e0900c2980340e60701e41c2001d03580701641c0170280315007e6605a240e03068081182025000400b12800c1895541440c2c0045c0e004250182001000098502d40b00e9008403000f4841d004c41c0d01e26150b220014407121171804020240104038002e000040b440001048a80860300508542c085810280c100071140d44910401442c1c10b8081c0110ba40003c42030000544541c850b00004c0074500003880d1482c29034901c45c020310300c2500f200c4010818011f020466440102c1d00b441e002a000c100514 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 946123165 1250 946121915 946121947
    0xa020403051504140a03021e1f02040f0f0f0501030504050c0a0303030c0e010c120309150e06060f03030913020d06080f150f10050d29060f04020903060606 68
    0x310180840c41030034501020214001001800759001d52664401c1c0441c0101050b03a41c00800300003401a8010304060341800040642c004076101c0000503a604051000084801b84100c07158812109600080420040524100ba18000d01c40c01411006451611a030030590003080e114160600d52038000180070000184102100f0302c034001c0c503542031240c417804c0c014010010340c021a40411003c040107821076000e002d2031101981e00045044c000841c80074220082c0c00d030751404543c000361030b01001e44025054010f441c2a401d2600c010302c200c0c0ba12004101c504682a81d4041c02508100517040003910782501d4550440c074100301c05030360340104885110040119034400c003074500134070029445800022074130142c11301d03401880015a8403507449218407510103442d42061f00c90b0b030305e0080009040c03d034600f5020324014a80303407c000c06000002c9030303001080c0120760140b60300e010411481c0c1c40e000750042c001c3e04040d03508500302000c600100795588000b40c04c0ca4464030000c02c0e851300e016031707a41d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 946124415 1250 946123165 946123169
    0x2021031b3d09050109060c030e191b0e060f0d0506280f02040e0c090108011e0f060c060606030203130b0402120109051608060c040303111002160212060709030b0a0204 73
    0x1800b0409554282410303402040308000807250700b030130030310700c0101c140c401c0c068a00640000b402508101040000181108480700401c54510301c0301c2a403564020b05541105004005858600d280d0345000b20030001d98409001e0380354852600c41d540c22000c0b89000610542c400701403c030640011080d0400c80c8000c0c0c105641c0245040e0904048100300d040301c0c0c02601c200c60389802952801d885681c20300103103010f02d00f900b500040e10400108180304482034581078510144850001d07a9441d003084a01030b200399000000403441160550040103090702c942c030300409140c41c003103003142801308803610803401d400f00c09080300500001190a40d0355004000301c0b800361040c001c100307594003480c2864803501403140034a0041540c1d00002a0603e010803d9445141d01680c01842c050031650b064462408918141c1c000b0b10868010145406091008100926200034903254408051040002481d031102e48800e242d0002c0f0240404243c0201d03104091729400708201c40c82c0d503034020a020081c0641c0d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 946125665 1250 946124415 946124533
    0x51308031602100c0f020c0d120804150612030206093c03031512120405101707021c0314040809030a05010507170705072021031b 57
    0x9001000b0a504003252590002698095512410700501000740c80d85465802500f08203400c0349444409c2e01c45c404d003079031007481000042c121441a00411003100d549030066501c051100c5505020325404010b0543e0040304d0f40000e0800d1a003410f943d1245920095400e6110f60381c8406020640c09000e540c00040110141103d44074036040c410308107030340c0c4044100c1c0e00420074514009400200803030a90191400c601d52203142c2482c100a001c045c884000c558801c00000424288000611009850060700c43e503008040102c407444210324401070480342c030303030600d80f074400308289000076410310340c2d0300580006402d500da00040e0080ba00f4051074070402400395180204101e5640d13001000010040700d5200c4402d951340e140c5000391903610900e40701801f6090b00040d02460713000341b40340d2040307460300180280c018031009961b4445070003040620a00d6070b4102050070361510030040401121140480014010031b40308a0a0541204103107060440010041c1c07406211301950031070300740c201001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 946126915 1250 946125665 946125671
    0x3131704091a12030c070605030705071a06101b0210020a08040605040807060806010210090c0f030510472205090d1b050c0607080d05130803160210 65
    0x42a103602c241c01030044005032003000c0101c058150000000152140c0b004040000c180240c108007042d2450781006000408101d010040400007070616070880c040000648194096414584204420611407150160400540c00001034100070420752081c81c203078041c1e039050640140c40100724140074951002030b107103c0c40018002440c40c1c0c0040107204507403140054030b40c200d8403000121541d031010f4803040c0c016402884125134102140d803007200454812804441d81e103980c0d4040034002070071035000345c40942001c005145466440e00a100518040801c1150001c1c84911181c05201002e90704064001c0161030010200409102910030244010f000d00d4403042205441c191382c1c14500003030000705007030401240f43c8240001d004581107403103403180100d00b0451f588002e6822801c10301a90030744540b00848000341c0b50311000700549409041c80a9071100041512019130f64050017155101c03103000721080c082071185007504e4010604030620300880b49121012858a6410400010701c589 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 946128165 1250 946126915 946126931
    0xe0d11130c0c0312060f05040b0f03100f0615140a032004081e03250f08210106020606040b01030b280915060c0c1205150c0313170409 59
    0xe000a208200603100341c0c1c540100f1489056184281d80c10f603c1401246d040c42001408603140c20380001c04804000351640504100c900c00180c0703091a803d045001c55503603880c80304107a404038003600000c1c00024174007540204040354014441d05895261207180c0c0300100300c415095202c2e4216101001480b200c4038183d190701482c004299100c1d220306d4140380301b440e48001d00075035080303100d4030345601c500c01450900c89100e07120044d88401000e94405486801039290009803a0114461042d0080b0310b01511011418001601d41904c0d0344050110700701e10004000041d400284183d028500350b401103410700b8260b005170302030004150741c29885000008070748030200c6901c440d40c04a00d14280b40300003469980c0d0380001100d203002d1442e207034007030070750018420640501e10340f4080c14840c001e40100360317a60302142c0e502441c0120080740c050304a0824202684110300c45290040c0d1301250081c6141040311244002c4610503030002c10150b184201e00c4a20980d07081901c1c020504081c09005e841c03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 946129415 1250 946128165 946128167
    0x81f02031f060207061b0f080a050403060f0603061401080a03230c010c0e0a03020904061d03040303020f070f18110906070b06031b010807030e2a0a060e0d11130c 71
    0x501405580f002131804541c01a03010042c0c80d1b4102c002d80c01090301e0100800b0340c0c0341d8100980c8128060424410100000000100d542c410158420810000041c529040d49860340656000b09400c4050210150050200050100d960030800340d0500700710030400e0100a0400c842440c5c0c110401501e40701291002240e10103400c140720b000501e039112800000710038104070044045000203074114082c403000800141090340002d0072081c4c0c5c000101d4000d034460788480e145074080c0d00101d006030000001034115070410007011010b840741450074909142003000c0005c0c4414040f00510110f42c484d800805030005c0700040340d4100c0300103840c540c0d44180c40e0518000c020000d5a03240d0007071080c1c00d409840d801c0186a01890158160350f40000c54032103480031405814640000d004501440d00660300c0c4400d114201207068008900209945448500b00000e01940758891750038001986400b02e0181c1d240d00c40015120341c000d82d00300c40201c90002260080401c89001180c2c9883c0441c074811035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 946130665 1250 946129415 946129423
    0x1150e070318060b01080f100608040c0e01030305041a0a14160803070c050f0c100807030b1305040b06030c0f010302071a0c121332160609081f02031f0602 68
    0x2013202a281e0920380c1d11240400080e03070304100c0300c4030030184080b00c0c1840703060b03c0392107480e41241c00b4140b620340081d1280d10006c090f040a910407400320320300040030402c00f00e24a41c1c0489400b8580207081c145080c0d0b0801911200340031102070105035000448150030706600e51121081a00b00050716201d16208001500701d403084001903510f8400c004020582000002d01d01d02046030240035216840391010058030140c030064251814107131201c0f42c0b82c5c030507201c425400040e15003148000c252428030f410900e802010262200d8000e030060202c8204a4564140d4114052400c0c030340180d0320903260500c450340348290030203403101c80c1d0341009120842c41c0c048082c1a11a06040741c002071915400003844502e001044001c0100440211903942100421a41940c02030840c4085210301e088141d005e00b000340c50441a020412030130414411264012802c10103025620002c0c440e0a0301e06101d803a03800c000c0d84c3c2d02d5a038950008005407031014403604104403404003e02011829465000181d11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 946131915 1250 946130665 946130681
    0x1409011e0e011404050d11031c0804061407141803030d020711030d12020711040e0607020714030a11060f0d06031a0c030a0c030b060409060311010201150e07031806 72
    0x40c003140c81d4606a1524a0101c600300d0398010f155a40d41b00d09580c4000e403a403401549030303506009004210301c04042c0060a00b0344400a0341d9044132510b02860036400f151001011141e540d54484204401c6075000402d00641892003120360303803508401c4020030b4940d018261101e815000c04900320840094540140c81090b03c80d040300802c1c40c0940003810354480845800100040110a60f03102c1d1203481d41c01080713614090301428171141141008103058031020784a080996000700200215164140075202c043c0201c0c882440c1610340340d200107a40c0d14030100015203584550b0a406001e80d80e6001113410601945003031a403548010402d40c0001c001d284410348070b098404005075401c10385100500d102d6030340800400d007151908111180200101c5044030309040c1d850101d002140e480c40d02500080450010100d4a00c0c00c40c6000040c21010100b400d05581c106089031002500c0100700800751900358007421310310b9441d00d400b100502a00320324105403041c04051a814012107800000e2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 946133165 1250 946131915 946131917
    0x230a050708030a230f070b0609100b0a030203090f0f0d0e01091a1303020a080a0c1e170a06050403092112030b060d050114031603031409011e0e01 64
    0x100041d40c0d9420161684a009180c40000f808411502c01c0085083d140c850080b003150641c608100d03d4803103120b41c540c0720841c1070700c88041020030440303540741c0240c3e0158414000c03048441003518112052070309006025013070082c10b4022001840d5103008100c04040410036034126110500c66015040d1102d04448203880047d1a9100240f0310394061040c0b5000c0341c0a48210740c081e807103510110034041e08600c1342c1c080c80c80d6840d840040507035103105410307015000e0300003d00342c440c0e002d2801044500a59000c040d21400440042250291500036102100c070038100c1c1248000490b40c0090600032071840040819103400309110605074000020010b41c2c14140308a45070695a99481401c00d00c6034800500081d1450b4844100700d219400a81e040b25001d4843c0d0b06040f1110f1040040c0d0b1026004152400441c80811881c0d01d4100603100c102c68854010003880c50235174030700a101007880884039454200001e45240c59034411050500c1109141600303415846290000030b02d042c0c401d41d4568 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 946134415 1250 946133165 946133173
    0xd050307051519050f0612030c0f030c10140a0b01020f0109030504170c0a06030c02011e0b090717040204050402150d0c020708010c021c090b03070201090314030f070804230a05 77
    0x30441c3d800c14461103004d01e042050b1081255680410050701d04d41750300c4a007040707000510220718400c80070802044408114009542c07100c21041d140b81c64a011295140084e9042600c1200c10500324043c0c0b07600503048134408a448810400142d142c10050110080b0640c40c0c06000700c141035003c0060003d6132115480d001030484000c90f4155111113100c002c1d5484180034404000f01d1303002e5404501e9441e003900002c5410420484030b00c180d25400d0b02c00d11b541039100c1003200300034034100700c3d007a80c005c2550500301c0070401030b48004021a10300910080c0201d95400200d425503503012942d868407905403500a544400050010000c1d000311807540001d4440d003c0c02259003541130080300c40108840e401460380d15805a01140e4041d65094114244046c007080400c480c0c0342040110300ca9600c94002046240081c54020111a2030038001c00c008003050051041070034004058507080003044c644003440d500c940c100a59600c4040e440c1c52038900c0c02c8888414401008600031644a024200391 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 946135665 1250 946134415 946134451
    0x40903051912110a050a080403020c030a05010f050901020304080a1805131b02061918020909030a1b0308060910050a1401080c070b0c160606300b060d0503070515 71
    0xb40c241c0141c8049202165052086c030011a2151021a83c414020320481d007c08000b4804070f070503e41810303000c0e52241d444602e1403448680f40e008a94212460303a00840c518585911804007a004000740c510402c8101030018a100c0a0002a0070242c9801022556100310010340700d40180403002e44a0304a0580c1e4681181b6540003013221032142e010180c1e03122004071200001c4004281030b1140e50a00c40f5010405009071f128070105501c00c0b6000801155640c0c2c00310030140c001551a651004520a140c095a00007a8410285500a103040c0c8140f501a1184400c84601c07503415040740383c000c04420000140e0741c146da112880d0015007030303c03401c0c1c10780c884121135146032084c068003900011070280820140e00d08103008105140c50092a2030b40102e0039550481683c0340da45c41100e0258480c00041003410180075601c4540001424a100c0000d084e07840306012a0000c1c107880c801c060001e840001d100e002e00888802c01e501000b901c1851814985000f5124029602508004500455 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 946136915 1250 946135665 946135691
    0x5070e09070f0819110f0a090b130e0a0906090605060103060902030c07111824190e0618010f031403040e0604330e1f0302040903051912 60
    0x1101c1944010f82e9201e00c540d4a41e074641d004001c0d40c926003030307000e43c0d0380500706811031006000d40040c0107000d1107940e4840a61500904650150304150160b1004114581204c955050380d14103c4101e591900d031180d65410010740100709120005d4069401c00744041d0420041b54030140c030510090700d040202c107072240e0000080380021a42540da209040000d81e001c01d04101403186d10010041000c0d00a548042c0b901070a46400e80f06141140700d20050b5001c140306050a001182030283c5490b04020360820b1640044a03440c4507801411440d50003290807525400c40b048404101228a01d40c6540d4440c11000c200c102d1380301c255503280441c0d42a800300c1001000703c50855660301d141604075101d0000300300041c50007000341005401520107280c2e2800e40504500760396440d00489000c0186090961b4090f01070081101c4070045541084200448a542a84007900e0701501c2c0000c4209080c6004c1d14280700d501e508400b2034103445001071440f03910000c081c150847c0e49e0014800c122000340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 946138165 1250 946136915 946136927
    0x60d14070c031b05030f0d02040905060418020409051e0303060a0915030305030703060302100c050c0906011b02061b1e030a0807080a14180c0f060a081905070e0907 72
    0xa4010b00041c801d596020301e010590445404240c000d00940f40342200b6040750701000d034801000980c3d000d130040740802181c1c025100c0c50754444019501817101400b0780c0316501040000c0200248074945c0c403016481840380030072000c414120342e8401c0d20000070360550450782d00d8104880c03ca00c02e02881d007020941c00e6590003070740781100510314800f202c2800c42d81c00f034030346800c0108024109940e0300c41c00009661107100152100500b5201c6000400440c2070440c180500d170002e0781c1c0903008101c01c1c00aa07036402948005400c5800841100200051001403501c0c03040b40100c0215282607820700303071280008a00d80283d2b10b03041c900500c08020203044241c5034040c101c0d0f0b14000c52121000130f0300303590089903480c2d131115580c1400250720799a00e4000704800800d40780f044040c0c14403400c0819441041185d4420440212008483c444012000810900c9004100c004101000d00401d642a0088035000c0030081320500620881c944000020b240c21080d030341031446283c00201050300c042c0106 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 946139415 1250 946138165 946138187
    0x709081902101202160804051003050408180f06180306100807140d0c0e0a0e0304030c0902131a07171e0a0905040501030c0f05060f07110f060d1407 65
    0x2d0300c0d102401c148000c0940f1400c1202440103001c940801034802d904100c030201c1c0d440280328a0fa900d0311141000c0502103001218411502810301e40014400810044402c2d654100100074034007058021460202d811501c00000444e00202c01051003020b17050103241c4104900010703001c440b0755503103c210002c02010300d84151246030b002408103111511010311806c4280714054403004860050340d540e01412011640200f0440007002c09201c8880028050030b0502c2200c0c0e4011401d090a54441c0c0c20b081a45200700300304294001405141e1885c41040d06008003032412441c3d4a4590f11422240d607981b00410454020114004c081c501c0e06202c400d807000a03c0c1000200e13000c4026415010041d8000611072003803013581e08001510750755600030907020b58421502c43c40c000e840c006038002e01e1403c42e00103501c01e90040c03000c140340601602c1583e2485411640040012001c0000f1558004203143c405030048030015140700805615003201c0c4c14a0142c100700900c980c0c8600e4100c500003403d13 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 946140665 1250 946139415 946139419
    0x6061509010c0809031b030c03030a1b030e030d12050a02030f06010806133303150216021005031f1203030203090309060730080103121103030709081902 67
    0x38084100c035948281c801e400c1051080c01050700d003880c081e002038070306015820420404152114220a6405c1c244180028584260021070070030185a0b0090400c20020000c10306440401c040002494400d070621807607410003800341c545401e1004001418071a80c803c0111165003050082070040c6441d201b10b9120744020301400c055501e8030001100c01e200c3c0542540d030310440c0d08040901680640c812914038941901c400005400c002c0c044110000d01000c0d488000e00d5150402c00200e4000410303101c41980a03000160346506c0c0382c034010384034804424080c1d0441c40a9980040c81d64225000318091070380c82c036100904000d0201170248261440c014180320001c00c00d90080042d005e900610f8010403a901640d003046503e01c08150590014801035070102c940708002c1b000c0b4241c0910306120382c00c0e0000c24280101040c8006001c22030b040c40020410a080e15403454147d00ca140c0105845801c1d80989980382000c840083c03508560703000310100343c0107808d01c5181201e106402483d0650f40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 946141915 1250 946140665 946140667
    0x11130e01140609090f13211101050c0405120106032108161b0606030f0b0f1e131b03061a0105091e0d0b13060b0f030709051306020301030f0302060615 66
    0x170038069190310368000d00707030341400c030040d0b1104000140030001c541070300054440d1254048109620007002036500810b40704081e40340c4028410307199a184111419154161401541e41d40041c10303160041c180e540c006400000d45120b00c4e103055520f000a10f1700c079950381e0b44504464440407a04c0c1c000801010114010512120980004405000e20700e0707480c601400c0c0009980c2d030b50b91a070762170122043d00215840d280030070030491041240345d041e075044000c10116220a00090705101d500c02c00242c402c803481f030a620b010804021b28019809408405030250880d447d42c0ea14080025015402d0304540d0712001024104280d4802c1d025100c903900d0060160b64284541c881a4844424482c0c07000c1e000060001d0340000714490581e014002ca03030a030070680040803141000022110146c2d12948104050618010241c1c2c001500006403600c5800001d4180c6882d401041c03d04c0314244007c0c05140044000414000d132015000341d880d0103902500c0301da40c0c800081145140410310b84144e0514 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 946143165 1250 946141915 946141921
    0x6010303080703060b030a0b01021c0c02010c0602071509120c11061602030706080618010b071518060218010302040f0b030402040612050a140609030d11130e0114060909 74
    0x4400d0041507007000950400149131502c800301a02e03d580f0440f140085140c45402500d41d0356410000c01064600a6403042d10070b00c02c495008080f440c2c0754101030304002d007004100c001c0c0000d503412244825884080c2418074582e58640d60090950244181c803612500c0c0201410340380240d0b40c010404d580700300b0114a048100042010355040b41081c1c00300e00814442201c0180c804101c00c071301400898071101150b00d0900c080100c016249115031510b030303420100400600760200c00f07071404030760321440d520032550303540503c44001c2420203030842e680c4801010321424803c80394014400009680a00c6404942c24001501071b4402c5201e0441e0b80319900e00100308100000b0082c5401520050010a010b59107440d6095001000d1300182c4081d0481500001044007940d03802940045030000f400d03540c5084000d0780d441c1d0261000721202d860303c40c040c3d0b0401c80c43c0c6c14112051114014020144240c44441008031250240503584a4041580c0d00e404a0b10345501540c404420092459415a13 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 946144415 1250 946143165 946143167
    0x3020105061201051e0a0609140f010b070f021018060504060305011401090b25080d0e0607080a0c0e0604171006180e0a20040f0e0705150f03090c0109080d0206010303 73
    0x8402444224000d941c0d1902080b01c1d1800d00030300650b010510300e01510ad04007085d0f2103995241c103a2104a54020400204c400560002614290560129800b500d1110f81940a0360022081002c548189000d2040412410f4000015106440d1203503403c11650307803036103107400c080c40129002c0b50100700700a20230044055076100a040c2d811440500150030000d100b68601d03a010a030f03400302c45020001c05c1c000d490450612440c241c3c0703c1d080000b0000d5003040300002d01140c8015100c003800c2c03911200c031f1710070301c07405010014201407010b0900d55071990703510381c0d80070428003280740c80132321340541d0f240c07440d4140f00c030301511007681c4a000305406140e100156010091040f11601cae00180110b0070f114000c18070700f00042c502c10445000240440144004000031503000d0003c0310360b550f01e00b4a40a4440e2400a500d0003507500a5440c1c94140e1034809000e104c600800c102c2d92403204001041010030040070800c002210740030380320b10698988942621351610442c00c8250016440000100042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 946145665 1250 946144415 946144471
    0xa080d1403060321190806010e0306130605090705060f03060108090f0706121b02010e0c01050a120e070302030a0302070302182e0510021c1e0309060213030302010506120105 76
    0x40408405403440c5c00d80b2500c0307041105403003188a20109030607504000c095604401d0900280e0b01c2140034041d14500040b0101c2c07039140007440580034990303460006403028420440c41e0040c20300106a1500c429200140130075952080f58441e00050380440404d4507002d00142d0852040f07a003001616409041c413000310303a0309015008220605888455801d2101c2d59900c1e0107a40011590000c03855a02503040c3d1882c10080a203041e04000c42084110310352544002500d80c0c459100002081c2c5545003800d840c0b600980d904081d50501540b50340380101600050514102c81c4283e442d8094402e02c4200c03459460360441c1c2001541415031039a66042802c1800c580c00081004207040c146070b140d0020400104a110559015070300c50b100c0b01d40c04601904c05c1d500503841c28a01008002000b0a00541d01f0824411381420700d80c030344420808000310381c0c06032101c601101c11122010355807414028060441519140d00075401240c0d40302d40c0f00018000c0c10710501e69a9280c90720451004644114 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 946146915 1250 946145665 946145713
    0xd051015051905120f2505040911090108030a020d12021e28080609090a080c0f10020421051005041208070201050609011401020f01060603051801060e040609030c020a080d14030603 79
    0x821031086c2c400315017552a4480c0942d4039000310900144030380d082090140e411410307006040158400d00405a5599002681c2000006980f41205042025950910190003618440748070b4a01039034103a001c2c1e6030b4440142c000420405500494100c2011040c00c15607880d00c91000090170301c0c0c00141150030700d80c0c0e02c142c00920318021160b61032001d481e40d0f81c650300007041003801a00030080e502581041088400000c0c0584c05c0e04501d0585481c00300c865101b2603039400a070840c040c105000a10800b842242007898000a0600071890301c0d03d094050441c81c40891400324103001e0220b0500c070300c14440c240c801c043c050500403442c1d003810320314a4603260700903181d41188140c1141e800a640d00303024090040a4544000c1404c1c14044059003002d44001186503503a0f140c10301c10400d42c8141000760b41c005402030000102c14010741001c4481d00d4031742d20b000c1d4006005010000301084006290710440e401a5100710010a401807181c0320307480b081d54225403591148640c1038000d040c9440f035200b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 946148165 1250 946146915 946146973
    0x20f040b16051e0139182405090f040509010f020d09050105130c030b1b1b010b0f150a0509030d0903030801050d051015051905120f 58
    0x2030512119a50340b898800c0400348802d500d03a03c081004454a02400784604081d00012030b0500100440034640f2100d800c02801c000c440528100c0040c114094800700c41214000782c010301035030b5114150041c0b0040585202502c4000c05928a000144540159582d81500418814070240710078108405000081d0461840d5540d036141c140b400c1059100410040c0130014004c80d500d443c41c03c0c001d0848034000c0000d84242401241400042c14800200003940e62040e40318a250310303100d4480d6805503000b02d80550320700c800200700755002c0322081600c980303141e0f03100280401c6e00d00600b40003400300d80038603181d000250303542001585103083c4040d01c100b02983c58540d0603c0706000c0020710341601c84200b2000304510301c400b0b005040d4409026405072601303407080c100c40800c582e902a5118a10b04c86102103a070380d60024075240c100320b00c00400425005100c4000d480b640070440c01450b075a031040038881e80f8408042000140003043c20740c003607603001c4094520004071075003250310707200074074003041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 946149415 1250 946148165 946148197
    0x11115061e1c02011202070308010f0605030412050a03062d14030c0f0409080415030b01081003230105090d03150f051021050a2414031e010c0210020f040b 68
    0x170800301540d102900070f007030181c0e17100c1c411035241060820300e00495400241c2048010000c10000c600f8042d8100703041e40300d074900599964195401140208003540154001044003072843e4941881c690700e4a0344146601c00d03c10707520b940c603400002542c08465955800d60490032104006107400c0c4681d9042100c05080815840050b6035040c2c150b900ca074100c122011001d40c004c072242603251040301e070295001c2c01c103074950742440703140e0f510324209a02c0024520000f9105ca2181800508002505031545000a03c0030b400d14520f140d480792807210b03419000070300d0894884811401c0300040821031300c1100509110a003007100303020861090b80c90b00001e204010840c00307a5400043c03c425540c0503041b20000701420100488401e40e01851001008188000f45084400d40380390301810807100410b040301000d5490001080c14584980250004044c0c1c000c000700406106400c003002c00955517003524031100407540b4070800ca0060078404c0343d0442003071105100d101c2010000304030001da50407500d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 946150665 1250 946149415 946149437
    0x111c0c1707050301050a091209030804030204050c1902030c0f120f030c0717120f04020a051201140f1005060a020d030203101509060801120203031602011115061e1c0201 74
    0x82421342d242500c0c0242829644c8010900b44000d0a460700c0582c080c0d271502104492454541500902135408041e1040380c2d0303031000c11800e6400c6001c41d034040d405401e401d9040b01050760081d481c0d0704014101403c9016500e4140320705900850301d1120701c00400445070030300c0c006078600d01c181d0300001c2182e40031402c204062404074244890700700d080302c8a800000c0d6100d4038041500003000018201c48110030000084c00b005903500c0880009444041c1c507041490840550520301400f2403000f604c03400e080b10824048981c0600c0740381ca11614010414070682565101404014416003a10310300582001480302d140621079001190085031a400300000301c1c0d142d4524100782e4195100c0b0002050703802e881013080b40c2e003021a031401018111000c400904158000c02c0d202e21501c140c10031030a1108031a1411a0f00032100101d5050a42048403080c0040600d18403100c0e80c180d4003e4401d14046910741955002d03104121011003000c0c2c500b204400e007616641c0001c0d00c080314100e050001304100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 946151915 1250 946150665 946150669
    0x618040603020d061e0501180f2c1c0507030e150d05100807120303020714010e0708061f0e1b0f04030311010203010605030408180d111c0c170705 64
    0xc1c0c08825003e1300c40000c402502c990600180761160708884900b03400d007401007100302d80c81c1c40740b4030f00d42e40c10410101d05843d007110301400814502030280c409013404108003440481101401312000b00540440382130040198910070082440e810a00c0001d80030803818000031701c50b152140181e04081c000c1100380450b8912590545c1008507a10030b515968410040a45000c0b2202c4d07004084060140c410682003169455001000d080c02805150300024a00c00b04038000c0da101710746a10260007003020303040c640030003500c4824901c40c0e407240e131181c48046900005000c0176420b404031000e001d041c9040c5402000712000c1002840780c41a40d0840c0000f4a09407a02da0041184180d0032501d540d9443c11458050021590b40c116011940c0c03040c00107006854015048a81040d003144020740c813145045c503800c01c070540c4030901caa040310400115030200001c09204120680044500880c1c0c003107440003150106041e0340d03004e04449560107040088a4400307038407020040a40054402c45521040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 946153165 1250 946151915 946151929
    0x608030a05121605190c05030406080910020f04060c050c03060708070f1d0108060a03050f0705041407020c01030f090b1006020d0801060816052502040608010209061804060302 77
    0x22800c0206000280c100d000340c105032601d0381e0010010300051a060f046500c010f12901400602082940031490701c5541c1501480030381280c0d035813000890b5036a60700c900c001040707070034141c2e049020b910880c6020701c0360301300754001d82d0b0310b03099128007450400d89419030844034120b4413142610640108010500607480030b1000b603202d140c240c0c6840c2e82c9828820001010094202d2441c002c106189800300c1016a80700280400308009282c22070309611402c0000748120801d5000600510401d1b012080b0442c000c00c0c035a0403907000f168200000c145211018130140011608600182c00c030501ea00d0881d806a841043c440c085503500103280c440139503c490602ca4140d4a0000c1401c0d00001081495410055180050800c0c9025201c9524201010309800ca000e81900401149202c1c25070000e44140160b440f11b45090841000d0100707006600c2d24201da159400364001c2c0c1c02c215010410301014000c90f210071401410300da10304413449061071140094802c800342d106403920400801350359241 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 946154415 1250 946153165 946153177
    0x320702010c1a090f160e041b1421032d0c010212060f0109061211030f04111c02010305040606090c05030f07080106050307181806051201110403080c01060803 69
    0x1e6651402c80c24007000b42c5140058000c8244903541c800000d401a8a02c8004450100c5a01c030500305115102c515041100c0c04019146075200761403544002105003001603032440400c410742d08044141024071812500601c000400901603004120902c00202c01d864003030140700c100b131108a40700c4141c2003a5030f201d0b440498000d00d281e401140c0131401c01c0d00240100e400200c11601d511891000c000040c1011a8501c205424400701806180d840034080d004000c5042d01c034900507550b480c00150000f0b844805a0b0700b0b0703690a071428040129403e00c0c0039403502884001600d54074100565004402416004000312032481d103070030340000c0340ca26034040d0100c058015207801e07440740740c000e1200703000090040402e4200008a4010002c4030303000781c01c4980205e01803404402e8080328101c000b60a0110394015109800303030f0007540d51007052507030000707003901c2c07046602d80442100340005609070b031004003504030001e1040204200003102d5a009202c00c24a0100206501e40c1c0c40d6030700c5003944c0002d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 946155665 1250 946154415 946154453
    0x1503020918070315060911070209011a0702060304032d020616020f0f060117011b05032203080a150f120c0f09150605070b061002010e060412320702010c 67
    0x5c0c200c1440511010700402e049980c00c1d0040ca030600003190009464000d062289101d1007540d020071400c0c8040076070460f9016074004d04500e5503410f00b45401060440e541d43c00d03501640f0072403000340250f4941d4520a2030481c85600901c1140c585100461038242005904015440b81d680c2d92415580e091090f00310a05410018000035071500055001a160215880e8440e03490000b018048509550405406803100c1c0f03044c917200c0c0d54001651003400c5d80001503c2e0340d2466002c3c0601010742c0280d040e4030805e00807500340a010350721035503408003910f41d01a00954070a440340170b00c03005100e20303d80c40701140a850038590040d91640c400e01113500c01d40041c0001078a91085100710508158040024805454102d2900303c2c41e403100c03010014080c6c1000d22a01c1041001e5806510035008203008100c80c00983d8047d00781031816800c044491540a070205908148107081c490030303880203081d8000c2c140303280313680c0407200500104c00d640421822414800380d25001d0010941a6100340141820303 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 946156915 1250 946155665 946155671
    0x130513050a061d0a0c030318030b240d111921060c080601020303060d1718041506020d082a07020a050405010501050405151e030a1503020918070315 65
    0x60030700001041040c8002006aa078401c80c4c2103000501c140207038800300d9400d032600b000d00168081921640201c10703400641020410000d1022215081d0400c1390425110307081070000b04d0340301c0140155549020006010000c02d800240200c2c149132100c603180522000c052200c0395105c0d82604040200c0444000c4130301041810f88040040510070000ca099013410400854501100003e40ea4800181607502411600c1201e00400480d0241d8640d551103a00780c290720340e0203403c400c0b28680d10300300c41746204130700709514000b8400780141460309803503031a03001d0322117403e0b0301000f80d0b98082c019210782c00d007011144051212200140f400460745c2601130101d903640c400d40c0108100c98200f40c20040c8a20b2a06004012a0380c201080350b0458105a5140c1000d4100c04482c072080c3c055840003083e0034099a6125000441400046101c2e07a25000200400d016140e000607d00c0c0081c000250850128004600710f01c1c803042440c409180000201c642c0c607a180d1f1307183d480e0045202810b92005072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 946158165 1250 946156915 946156931
    0x16080417060a060b03150d05010e010902150f091203070b0f01080d02070b0306010c05100f09021002010608030a030b031903020303010821070b040309091a090c09130513050a06 77
    0x50900030190040254031040c0421420240d0301340c81d42c400900801c1c00e011440d80c140100e41c5440780b00c9100c2c0e036040710007008000742840288c1d0180110800072440b501c1c1c2560b550760003d070a03105071500c4d4030b411100303241030480180c188084015050302800d030070700c030501c02240011004030b1401d1044190302c3c110042e5526000245107024008100402550005038040c014140030b0030a40703a010b1000d01e000490a000c03418080e08102204201409603410281e000342c80d00a01d170823007020180700303450a40d800c0b04007040481c03ca0b04107000c0c40515070020000407002e903100e900860345403140141521102800e0526031035105070030401c124050f0308040010000b003401407108009100c483d1a40e0304071110b84420306038140c45a1000103140d109000040b40515105422000151001341c208001401e461004801140c43d42c131401441401c2d0280040c60b69040b1200751001d00d00007502c10132070700700050030201c0a040700402e00d540f400c2800400f01e010510402204c10054080d000000d0108 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 946159415 1250 946158165 946158209
    0x504060809010b0102210c250e1509041a0403021606141b030f040915121a060303092205061021110d14010e090a08160804 54
    0x49030080441c81d969260100782201640c0106000d403643d1800b42d008012070450800703440da540030f44181412944074803860b034a0351000941041d01d014044102e19511190344850baa03031a90700407180701d941d4000c00c1001e10000e040546245400c28442e8500d04050f90f1141a045039050048405400584c8080b16070b1441003680f094050180146241601c0e000007400301010161003422107200040103041e031202a410070503c01d4070075180c900710003d542d8540e0341c10040003900c69a044400d01c612070907030014146003030205d80c0c0b4900b940b0100c814802441d103000f4210601e4000d100b25054003040080500b50b0391000403800008426941c0d00300c0020000d009041100c1000701000c2c0a256502d4030703c075455402c40860120525849002c000704041006c0a1001d00901d0f803074480440b00c0840d40c00d00b4080340d600001144c030030881d500c401580e0780340121050840d041d5061421904072440d90000b003031500c070041014400c40c024242b040c4100b030351084841e621540c4680c60303100300944184018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 946160665 1250 946159415 946159427
    0x1c0212030405030906271509010c11041409010e0106060813050f030307031e0b060322050a0f05011a0f1513151b120c150f0b01090503011806150f06050406 68
    0x40401034076200304052a03507014103540d101c0c0740794581c12b1040f031002c2d110400503911032041101c00c000e40180009100d814009038001383c00e031981e0519500b8816001c1c0070450500c61070045408030741c1c0c3c880c00ea40760314005e4007200500c8070007981c49028800368803501601c00c10055019803000d540004610964039800c800e0a003240628038134480c1041070408803a6100700c1070f00e4025020b403864020100c03080009103900c0c03a46181c02021409207100200504c0400d001ca0782005000320300901c880c000004000744e0003040b950f045640400c2c1880b0707040c0c0e01d041c07d02c5090265a01d090105181040180c003140d40100d40e640070104c86850341d00d024112079070000400c800000d0120a94400042e65560b0440c1c2541e20707401081041050304034207003808200100c804410450030010400ac520050180d000f07002d0440f41240440c0031043c00181d903044c1481507003110000c0b042d80c00e07001c090542e54640502400100445850a03070341340880c1442c4155a4400104000d40b2100c2d90745250800c06460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 946161915 1250 946160665 946160737
    0x3121101050c220302131805060403031a0d020901090c0e060c0d020c01081302060f04171b030d080f2707090f0207050a260a02010e1c0212030405030906 67
    0x841540d04001300010389440010240d14440f1000101d00d41c1d41400352201c0c00c0e103a85801900074400c0f90140030070725805620001e064007030000382c10030440d1118140310042401d8000290040c2104004015202c0c142d40302e12200c000c0780c03034400480000c40d0000b0300e403504502140c01403038100c0f034a0700701d500350100401d1820100c207007000c42c100c3c902550325824400d060303440a03015560025455142061603021a4090b01c0c00d5507064864024444910782d40303100c6440c04480c046503c0c420104640307000200059101580c0d501e10405544161001c8074105014000511070706508604900907e120320000081d0300c0c405008042a514117880d1000744d03a21103003100788982c4100404c00102c4d00101d4a002c107260880300103042118041c4500300b01641d0710300980c66084020cd0b101302001e42c19048400b0000c107000031500d0b618030110340c01cae0b19000c0c91100d0b40096480b20401520310400c200c0555030003030203402a40d0400254401041c51940511441c4a80d0744821820b804142090102031003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 946163165 1250 946161915 946161967
    0x60503120301050a1e0b131d0f01060806131d061806010506041d07230909060603071e1e0e132f2203030f03051003121101050c 56
    0x101c0a60170180e203080012405048079110001401ea0400c245c403074031440040c0940302680441b1480c0c0c840300d00c85140d084d0341015035006158000100c0c1403040050382c0c02803070b000380b845c960074a2641c9031000400600c0843d100044031816100c0c0f19a4050110f2480f840448505074114032060040c142040ca0503004648102000d02050000c80207101e0300b048900e038104c0b1410761a80312444103480d681100d441c82c2035046010190122426441406805461000d80354040a929040100030040c0400c41d81d00001603900c0700c00c0154005880d1055100a42c20b00780b6000c030100c108401115003250340c01c050045102c4031000324190422010b00400007240c2c1508202ca080707541c803075512a02030070070321014410000000e00fa45071211811600c20031002d00c0700c02c41e800549038130b42c0341015003131200fa004102000105c00d089030282c01810311640028910510840c2141d541d00303c0400d074000d01d0380070400390b038810343d0540a09110341030046000d04030003900c442400409152044010700c4900c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 946164415 1250 946163165 946163189
    0x60f090614030403050a1b0c08071d040f140111091807021e100212090c1912060f050f0402130212010e04050c09040c0608060609090a0b04060503120301050a 69
    0x203001c150000056941096041c5030a50380d40b4440c0c0c40c03c4a003c0c5001310301080f08170b008801601040400000b01d01124a8182918001507a07901d0710701008505a049074400d542020009000610140e145c4102038400c80d80c40360740030100e84440307003103c0506120620400740003030380040611300191001a4540c04100c1d0200528000d44000d41301c800b280ea142e50030401c2480d0702040c068081c0303ca50304804900000315151946405100088030059402d800f49025801c00c00c2d81908200c80b00c030704626030050000c21000d2508090701034010890000b07807007090740d440400d0b00c80c0f249030190602034201040415020705150040003040c02a030420701d0f1446104001036441c541c0310129890449043d100c1d269103613075480c2081c0d81400c0310410710701d910080d500108000c1008a015590030b544090f49c403115255a60070610034940f00b03d607185c5a100121400180d0a585c1980182c521540094000700741d0540d034102103840c21515507291aa40c403c044014401ca0500003441002011005000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 946165665 1250 946164415 946164437
    0x1909020609040902030705031212060901051503040213060905190527101409010f1109040b18070c02090f040b130501021e0325020606061b0601060f0906 67
    0x49041c4030300564540119110844101903550034007425005040c06004d035032015542c5041c00740300398000d045029220390b158010404a0070302c100c10b1410b80c0d00207132200008558004848a40341c00051089078001c045a2400401c0d0a00c0d0150000501c45c004c0c022506041c1000381c0c00650300030880320f9080c607207032500b0408444100040d5540b44522641a5103290414103841402c0c0804070311803180141c2007010b44c27030541081301419071240f40000020490342c501d03407800c142503ca02c14100e4803c1c900a000f000264503107903100d030f0400780f4020b220001e20700758501180070000045030620080380103600031000398182402c003140e000c6000201c00710300c0d03d06a500c0d03142d070034030250001c4c10030400c1246020420009504485a0360031405800f10511003090074403550b5401201c8141e12146490720410383e5900c5070f18508002c05650f0040d00c1242e413110280041c940010241d00130051300300c000c060345210103001c003601929442c0d44000c030b0b601c418407019180314469400842041403a07146 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 946166915 1250 946165665 946165669
    0x5070e0d0203010908070f20060d2a03020a0f1b0b060303071a010f0603050907050f150d0b010e150d0b0f123d0f0e070905190902 57
    0x1101101540440d519412000c0900100c0d006148110700201412000200082031204071680c01030158810044003c2002c07074014070101d410007448009800842c140050700b0714041a4001d20350038243e160003120000310104c56000e0b115404010f10002c07a0303000400458482c4c2c0041200501080380c1405169840e810703c80504068140784040d01c500c2102001c00c1c03a0b5a0240119000f9540110741c20803120442c14100395207240a00c10407030a880310a80024883c0d000e0b020385c61080008001800e8001c1c64182808030f5054407096a40c1d102030351850703450666800e20701600e01145a680c0000d04007a2410000d014404412a5548100c82081d509608003a1001c216420580e12200114200627610302003100e28600d0580340340d105078826980c00e01d084001448010200c03050b020a001007000f4010030101c84c0c0200041d00001d6015600121545020b4000341c1010400c0d42c400202101051002c03030901c0321640050080307903200d0f01032048004220310310504d00a40800100420031560b40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 946168165 1250 946166915 946166927
    0x1c0f06110901050906030604090c0807051c0201080a0903021002040e100b120c0a090b0d020d0f02040f0308030603150f07020c1e1e0a0b070c090b0319080408030406050405010f02010507 81
    0x12130b0342c803a500000000e40c641d2200e400845200b6804031080c03491030744610340941c9400050050600400e82600a0f603001c102c0c01e441100c903160103848658142c1c9646008a000d445001016410752150710070002c551800d6100400082051448001c0f4604249060301a00c40b00c907801f810864000740440d0614554040e0030540020b043d298095448035482000d45043c3c0c40d070b0340040801500498880f080e2102900141008150362104000c070b040c105290314102e024138004c54880e455140404d00000e40c100000f190001c200404440c3c000c1494030310516070040845480400d100030500344402e05c1c2d010030030b410b0540400c0f10400801d007119029180e81c440c40f106102e1103801c180280e45280c0941c0da00e1952080009407a09030610b844080200303903130303000e000100c600200d452000144066144a00321900c00d00174042c1000403010f03000c58028003c1c807041030b207010400700f2000603482810001030000702040d88655407240d25040c0094100c0b03200307224400070f69040000300520268804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 946169415 1250 946168165 946168177
    0x21203360c031509031914040609180501080723090405070302090907080c010f030219031d03040b0306150d1e0c05161211010504060914070b090f1c0f0611090105 71
    0x10545600000880d981c0c00c0607103421f61030840c00940495203c3d44003495006031ba6a40814500d0001c0d05c00f54442201d1003441b4108040e008a0030a00030101d15000c0001c00c400641000400048900d000503004101a20115600d91001200304114144070400950102003200941505440c2170009621902d04c11001030421801905140302240241e041da0720075817810440440c0c007101c0140240040a0340c03294501c903444184c03d035000d0300c80008115001c3c0e642c440c2a141c110345911080c40100304000c005101285010702ca210b40e8050903206110140224840c1544d01040451080e01102c14018180e170030040300f041403030b6500e869692082d030040c1d4050b540d85440b500341c030b000f01c40c00c01e1040c2200109500709410300c400e001d42900116041406910070507415040008101d564010a00c162601041e0170f000c001014600508460401c003000780030341010751000384941e082841590000c0f11840071034103900e070500505101e4a0303501584400d009242910000c0041d010780904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 946170665 1250 946169415 946169437
    0x20106060c1505100905070f110a0f080f280e01050702011b05010f11041d040507030609060f050a09120806061e0f0301080a050d021203360c03150903 66
    0x3c10114003610a1301c0c42e090010700c4031032010815170402c2c2c44020805044003805100060240c2ca036049040c80c08200312100a81c41102d0100103c20307a03940e80050740000c103c00701d81001c2070020714900d00200160502c0249812450200c00815410190a103000c4010050401c03038148042d01c0184d801c030168003420802c0c1e1803134002c0b00c02c1134500140035040c607070411103440303050070507408203058014041e1090722111070381c404840580f40c1459070b00100031580500b00d90300120041000c00d405500603000c03e8080c000100d14800d41020340b0098031340c10f94007018001d40c0c0c4c0501074203200502000a0040003185444141c0341010b500045083c01f580002904a50b8a1201c1c500c0e55090201110141a0244101900e039a13598541503218500100240c03400d00903009680e81131480451085202c0100c0c040143c00c680322150030f684c411480c038040c104e1003814840c2555201d04007040d42804091040010a1810f501c0024036040c2000035501c00c0741c0c20b0b100c100703001540c1008029120b40c82c1003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 946171915 1250 946170665 946170671
    0x305010f0b180402150c0d02102d1103040804180c0f050c030c0703080301030506011d1503190b061003140c090a03080d02030a051612020a0e040509060601020106060c15 74
    0xfa400015a9005400e250180b120000581c8000404000c164810460320607001e480701c0144103480101512601108003040c0400c103403801041c043d1060300c0240c00204440e00180b650042d90030122103078001c0e10300b9141c00801040810950420036400711301440c0041c0305100d0f88260640180074489480c0a410503c1804070300790141000400560b000c80030f08500700d034441556410402810303030080c00142c81d02e010b010000b0520001d0f01006000b40c03a0240b034480c0003552102c440c400620340c40d45509900d8051080d400d0110b02e841c0181c00d10050040108078200e0400b90704200741c2c4d14212024406140c1081143e483c1840102e0400341c0c0820340d494190b0340c03891030000050701402250001800c10902064007069020303207501561003074100b01e0040120741c551211001c128000c040b049400070f45d41e40008540e4040b15000b0b80714050311030810740c041b102c691001406441040701c54419135030003101006125a824060a8000c04480c18542420803458881d0b07000225030812412040751 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 946173165 1250 946171915 946171921
    0x106090e0f070b161a0a0c23030601030204152001060303120e1203070c05070608060904020d030e030d050702040f140a020c100c0e010212040b1e13030b010305010f0b18 74
    0x2a05105450721345500c4200e6020704201000e0607125644251210b1005602c0c1c80300e42d018240c026035889904406148034008000440c4101d000030b5030000f49014100342e003d1200150203500852032600c01c0f182505d0380785140d40a49103e02d696050314207001440d82c1401d0040002c41c0d0070051219100341085004030b6030f5141400d541d881e1044101440c00d000c400081000f0110380d10203458100c0c40e105a060701d030200d540c1d200883c1c12800550306660711940c02000300d80140742511091031500d1090a20715002212000080e08100359080e09a010910000d400811803429204000418a000e00104102075001880001e1007400801c010b04c0c09500258207169003108100c040c4408600d18030501070414408030091081c05219021400b51055601241d0091846000c1e41c0032b8402c00f92855080c274100061001e0000390760f6038100511403040010f46a03040c403144494024501032803409000e945580f600301c0c211201500c0925032186446541c0c41c0e1550307050700c05034219409007015482c0351 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 946174415 1250 946173165 946173187
    0x3003040609050a0c1701060b0406030f0b030708072903071209150b0f01021b010302070614130510020f0a080402010329030106080604050c0108071209050106090e0f070b 74
    0x5a00c1c014003184036a00c001000c114028403048203541d84003100043c01030119190703a080ea0300c2c500800300d00b284144000e002e01403013a030008146140300940442c03009441e402080c10013185811481e480d0b00900707030a2000c80714011610804141c8241080c02210b0f18142e402c07050702014094004102c100440392480c0181c1382c0184000c20341210f86001500600c100072401015240d8100f030042d00d00d909030f00040d600119440146014071034545150503130b800c0c0118000d501101c000c0f98125915500301000c0c03042c42c1020740c0301b035451220f0204485842c1c200145841031640b40b280440b0700402603090300e0301000c000c1d124154103038207102a560f150340c4010f030b01520701c481000c1d20107814026291004120b554004602c1c13441070700204120b03a00d0346185500c6036422500588264042c1140c481c0d0703035200c0c1e450150b1000e80c078a0601c13040d11003030861005480c5041000d80c2d180e07459840a000d0007035503101340c03c0e2030008a002400c1c0c4013130144185880d2503031803141d800d81c2000890800016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 946175665 1250 946174415 946174421
    0x14090601050415080402041b120e100e10060f030c03030f090e31030e0f0d0215030a150815101805160c170c1c1130030406 54
    0x9094010410b0f051200031407070082411004540582c40f40d0b00304501040080c103156500e8040c81456983c183d03001002d60301505c05800341c90041070711440303080b6804401c0d42d6148148440c441904000e0f0491061442080094031540d8002120300c1803240402c20000780305601180171254541810350740006052404d907880c000e150300c00314403404035a0812031104120303e1209054407400c6802e001d00b180151028000000112000700402e41200c0f00040c81d24201100100d400e0000340a43c2c0c8051040d03010410101d40d0080c141c0c00314101000780001d45005001b1041030b01102d442c0c5034200c61903d02003a556585040207008050003180c04140103500010f030032360142040c08600302c03c5a12550920300245000c03164082c400318030411303203006203229a807840822030f00300c14007030000c401c02504031301290700c060a0240d0a00c01e441090048054204074050398281c10f0b1141d800700c1e04080300183c20003440400542c900c041803000301000040c8103010520054003041416126510751400780e0013 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 946176915 1250 946175665 946175669
    0xd030b180103030f030c03020405030d0e0415031b0b0f0f0306030c03062a03060f09091f0501060e101d0310020301141513050f210d031401140906010504 67
    0x10005490004414550481e081d980c0d0001145c0c1d04109020304000d045049010b5402500d605410140c000028030b481140d040c191104000c20001e69409560b00b00c40800c40590300858212544070b1006c0380b03031400749058100415100b003c15181c030200070705160040c4202c004a21840c0c0b004804107405032001c00014201e03140107011505c0d40e00740158118600c500d500402d5a00140840c0480c554281c24400e076802610301030090344188103030301c0412500302c40042030a0034600c2100780c910328145500c81c1d0ba001001c02c0400010303041d41000c0004101c2c01203170303040b0360003a0703120303045440f2041e8425100d8110003261810040c1c0a02d4080c006401d110301c0d0050149030300e0021001041e030302c0d0000c01c0c14103200011110f200c0707840e0305448103180394011901e10300114074429030104100e04001802c807407154802890303041d2115248174040c0e11090a140c0c0440c05511200c0031207941c80d00341c442c001500c50502c000100035032609118507220150142c905019444a17000319086901a00503100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 946178165 1250 946176915 946176949
    0x304140a0c03030e040e010e031207050d0f060501110a03080a020f040314030901090602060f220519061503110d0204090b0901050910110a0f0e03010e0a140f0d030b 72
    0x2880a0350b9040042c01c000303100b94814400e41c54844e15441e600ca0520a2209004c81d800c0694140725004074800401540148100c041c0103081003900c1d40d541c2148242200b05076454400a07402e403c010004007141d80750503840c2038543c03200d43c04802180d00701071182c0e8042d120a00141e626149071181805502482e403005101045403d0703840080341011024141c0f10100f0b90700c0d840c96603940d060407a40c6440a0ba40d100045448401107840483c071a0302c698009610340880d44040105952800c1c41c099400c0e041c1c0b02070b40c075003916410402015001d0012281c03000790300c903101d070ba085444211511058025007403040c1e1028100f803003192119000305030103c0c0c0100d14001c0c03520788100e00502030101203d0002c05405840d00602000c016031081c42003c203116002c81d820b080700e8240c00e0318110481000703c0144160803c030355215550034095000400240c1000e01003803541361900728603041d440319071504641c10043c0303040d617017034030000e4002003071022858003003085186d10010442141054910310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 946179415 1250 946178165 946178183
    0x62003150130050a050c030c0a020c0a06020a051b0105090f1302041502071d0a0b0a090542010503040804080d030207110103142703181005030603030304140a 69
    0xc0e110071400340072080d5040e51a1014889035036840045004c545c1c0840b0248015001480400e50441450003d485100b01c140100c68103c1402c400003001040540c0c41800140c1c88110703240300f00001170003031000429480200c048503110400007e0001e018a5000c41d00599090040300701a640c2c4503c04010b074050500110740d1640c03a00c034940d4000ea10a842d9101510a2800008188921414419840c000c1c2c5c0111301c41074440c2e440c142d0180c0340306400c5950184803104045080c80e4184601070049038240c0601c9035140c4e28109100f80142c808141600045000c1c04844041c03500030f83e0302e014441d0910b040d6030b69641e286000000c034011038010454912030030030304040c1c00e0b4140e030040191601480e41a81d400e4618001141034070804000d0031200c501c100c0100358006840d01d081030b0300900c031004d0b000d010721864021600e1600021103030b014000c00700c00035036030300d040420820100541501c0c115103140742003400300b076591101400042403440700a0741e10f500c40d01c044c0f21008515500484003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 946180665 1250 946179415 946179467
    0x2060712020d1b0815090402100e030d030b040b01110a0b13080d1505040209030a0602031905160f020601030c1503020d02131703070f020d0614130620031501 69
    0x15220304541890391001c148030001140342c20352445d00e42640e040e0024a9420b0641d40da40c02c1c091403000101d0300d0b1040c09215044000311b82d60034032141030290301a0380e0015a1003560310400c030550b0880503046050100c00c0d200c1e42c0c0f0702d29000c50401c2001e508030451800039152500700c00c003070114042c0003601d440404240c40d013042d2215001a0700581e01210001086501d800030041203120b00e041c82d5034103900c400e045800143c580e4001e5984a0031040840401c3e0444140d4007051740c408a40e01550015001e24092915400c0010540484c0b0680f0081c6510b60441e40d4103000140a8040c1d2142404030110344800540b00c0d8040300e1010801c40d00c00d64a170f200c102d8601055080a000f44111034072801c542c010007520000c15200801e820401c80c0c420400141c00784000784034904405d0b20003940b01e4001040242c000f40017240030b518401240c0c500c5400f00e080010450b180c1140c040710003600d4000c4542402c001c0740035a500004260342215081c1003001c010317100e101c83e03408801d103030200301c4101d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 946181915 1250 946180665 946180691
    0x1051207020a0c150f0305090a02100207050a0e0405060a020906030a0b0a32030f1218060a0c120c12110a171b010516180b030109240602060712020d 65
    0x104103043c80ca605c60344040030403040c0c181c2c20343d13108490b502c9240e4001d807450000340c035101c00c08013494001c40c0145c031083d6844002044d008221070304481c07214814078090004104080200691011007903008600b01020b001c0081c620344000742c0400304040c0c6450b030741445590341035110002003803c1d4400900080c19603203440a10300c44595500e04115400d42020028107000c80e400c1d1407a49260003515024a100c2200f4031940c110140f0404001c105034101480c90712810010102540c2a0311104580e04651400e00001501c048040080000b04410302002a001c4c00f9a200b1100a0341001c080301da403543c9115262000044024010300401a511010b5a0391500103049401034018030041011070b0041d1a801c1e40c8040c1d408461041d08500c030023030020f00c141c0a612000401d802c0d0200c20942c0c65a620350142c00070380201ea845a036410201041d201c00e10300030340500c041e041c070003029646002c0c00a03440305401040f14060004455445500d420381d54111800a04013101c10001c020130001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 946183165 1250 946181915 946181939
    0x10207030903140d0f030f060b0f2a03070611090405010e1b0403080d0b030a0606063515120105010308030601080702060108030a030b06091c0c0603090201051207020a0c 74
    0x120558160a11402c0d494001e400801c4d80d02080c1c0c0142c82c1c0f40c0c1c03403900d40c0400701d0041c03035007807050380c80076a64040120341010914001c00100300c0c02d454054480b003102300c100c80c03400e2003071500644401c07140040050b594000320548000b02e410220015603c80e07048212071144c451014840e9115113080000328102e0b00745240c290050700d180400e18280c2a510200303050511943c04040c2c50004107010006242590703130400d1080c0c02018090700e0700c14402c1c0c0e49030010703600c207600180003183d03020462140c10100b54111b03448401440102d007064003078802000418080c0030f001d605541594004141c0d130f603203c2d149907040080c800b81c020422580c5d2410a8a0303141c1058500728001340848003c03501c05880020001d05035003c0d2409035180200c200c000b130f0010a440d2583e42d03000710041c00000304590700c040d40ea00f008042d000d113012414016152852204030240c00c990706040c6000910300143c1d0303101094802c0003040c6c41c104c4500d0340340e00900b40d1030183c099500600ea500b001c6804506408602 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 946184415 1250 946183165 946183169
    0x71e0315090c050418060b01020a1a01080c060f070f0204060b04031110090509160917061009020c150402040225031107031a190c02070f05190b070302010b030102070309 74
    0x1415101c2d4a0302c6504110584030380030480e074003a43c95401c0c40d0020501a030720024040105004a4104852958031030100040c040d41202004030528010007210700140040e041a010485050f0b1818401f07a85500b0240070700c00d00030f010301c00316888040454480c1d5000e8009001959101522699a4581400c825410107000c80c040c4203640c00c40e007040e6004101007400d82c3d13801801c407030072952a900700c00c00785104154207078100241e18030005901e060407803101407460004800b404044c40c2c003505407070400903164401c01d40c40380304000418031840c010658035100d200a01c0d400440d600ca40c000500030307003d40381f903d40d81c840e0300d01c007022580061444003c0c1c69922940302c401d4102d100200090301c400c81440054911266011141c020140c0c070b46400340d110300c00d000d9156080039201d00e0b680445031154454000b50340404001d1100f40070340c0e043e800040c40c0c2255403d010306852803100088030414807810308200350200e60881018001e40141105401c01740003151a10020f05008000d48828 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 946185665 1250 946184415 946184423
    0x1208040201093f0215090913170d050f0708090303070507050c04061d09010203071e0c05150916050321070602070c140301090f1b030c0308040e18071e031509 69
    0x468400e60aa00171481501c1701080024000c01c016585c0c0d0324620241c608540d41256850241705209032030300304650140103400001c42000501d883c0c21840c2130254040600701c4014800614100040b80900008072540705001e407500c15161420b51a0442c5842428640e040d401404c007c008501a0049031000d12090b142c000c10010640301d1028203400c0b0300c0103494407000200103101540946a85aa171901c1100790f920741000d549900d0f0700c0b11802c010740c1c001e466444401013814001810310030000d0301d18400401444d0a2814374050000b9038410840c508803165a2035041403001e140001d0055452007a0004030a665400c21403074250340380b0045008807501e441d80440804a00e050501c5404000d030f911016003403114000d5200e0801c035200c0094a00c0440d520340c1000300015590144650007141f042210586441c2080c14140b81100020144551606d54100885a011000403d5000c94440906200d1b407a100081d800703241880d03640010300790060140c1200f0010b00740e03602c46040c050107 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 946186915 1250 946185665 946185679
    0xa2a090c020d05072f0316060e04270c0f120201090b0a052212050303191803030509012a110304050a030605131e1208040201093f02 58
    0x1140c200f95514094560040c2007040b488078016038100c40420308452546020524149000c0350400107803600451607000681180016810030403180c215910503c5008203d40c10300000c41318480804404011440014003115517120800a01400700301d004050500a460f031807280ba240c500003800740300b071440300302c0c0060303908200082d00d47c4c0300d001622042031080e034903a4a4040c141103610818400c44140640c0000a40c0d0b0008582c8004040e40725224400c10155443e480d11b5001c2c0e5000c0907030380088052050a02d111008440300308440116120b07810704000900e070700c40310140b50040c414030040d0900300420000c889045810f055122802201594402c411051034100a075224015407240d5500000040000d100154a41c0c0190390300512254809190480c030351680481c03299244c5034003000103d200010820b0040c6c403044500c944030760b0b050a100c0c41c10315070300080c100741c0d2902c100c04048000d0340f608030004c0088880c0c000840e1101c200c0701c13615024a500000c1c0030701800406ca02c04c0f00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 946188165 1250 946186915 946186933
    0xb0703031d030c0a12050f0313020301060801051609090506010905220c211401061d061b060f01050603070f0c1b060215100504111e030a0b060c0a2a090c02 68
    0x8410302c22640d19131f240d4118607095846181902c244d940800604a91554a039000401c072200c1c24071a0500c42d4441b03a240e01c2c26402c2d0300307402410641407a00700c404100d040004000450f6044100282124029510b07691154025107400c90904005142142d44030b0a200b9000c05490380580f07a0f5100540078030b80945641b819148090032103141140c9214581da136400100403003406400b040b03181c01e24150805207221541c40c0003030001d40c0700b02da02c40c101200450084c3c0c03d00341e023040800c1d441001d4405040b02075040800060b102c1c00b00400c4001008811801c0418840c428503103000384643c043d5506811910249202044004601411005200300c248a02200d00b0381c110550041800c2c801ca0f1100d2800c000c1440054005100c810410b00400c00001c0000450117060b041c08a00c100850768490419002c25025912100344803842403400380301c4e98203440c3c1e0200c1d2029046500140c960f18808050301d41560741d848004001040c446182c3c400a0f00807296041118801c009609442c3c10803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 946189415 1250 946188165 946188167
    0x9090609060e2202060904021b070f0509100b07060e0d020f1c140d110c0f0111031e100b0a1e020604080a050c010906060b0901020c0108010b0703031d030c0a12 70
    0x444583d60415455070360100b43c1c015081c13040007845103510280c8058506a00030802c10114814000f08012035408000e00b0800161a9111400a064115640c180d00d040c0382b520a4100c082078022001e0003500010f50500700030099005c1ca8100781043c003601c0002c80105400b80d02c0e030601a0005910740907254410400440038103004181118603164064224030410300045260000d80440c0c3c0c02958034000034001c0a100009070030300ca1408030062080c95291121182510703134680314051081014400d00000305681407943c1d8480074418220949a41c9484001c0c8404126911190b5140702c00100c003041103501c15007061460001d000c0c01c0d076460300c107504100e07a0341404031400b4040540c02d001c6080c085104500078000302c0f83c400b001080401240d1035040c11640207500221b0f8244001070f40c0b408072350b01406426001e20003400c06002c25031404043d5a124800e807d001003c0540d0350111440c3c1403c28446040c810300000c0842e80c54000b0050b1a5a40700c241c10010f41e444007040c0c1a0304001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 946190665 1250 946189415 946189441
    0xa05070209041223340b18060f0103061a1509030f0d050702090414030a1706010908100e15044b05031603020102030a0b040b03030405090709090609060e 67
    0x20586100d2510303e0559001d0041d0700340f285e100458442414250049445c80a118003843c40035801070b01c0098507814403400e840b0380c1c461030440c0001c15030800380c100321807007803400740d101d045903040071010800284403081c00554502e00c0c6400c96002803110340304541c508840f40901900c420540c212a00d502e00600c0b003544d9484001030000000310100184401810030f000020b810030701c02d910b00ca440c2c0510018081c110340000f26203100240c02d6400320102d2003c07442d0907540120080c208025103a0504440701c0d00e900345400c900200c6a2588039409514600f04078029007008058202100c50401d440c16400c00000b4802c840ea0244441169061440101140e852155407228020f10741d62822101c002036801c00b45002c1e00d86010501040225008140011500078466400180d481c40e10134640c504441000b19106d0183e0300c2d100510600d614000308403029100221200203141d6281d00701150004c2258000403021400c0160001d401e0b00d40b42c1028080d00d903003c1001003a669540442040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 946191915 1250 946190665 946190717
    0x9060306080303310515010e0610051e0409020c010c02072d03050a03020105071805060d0b1c05030c120903060f0403110312040c090e070b0a050702090412 68
    0x140c0c0c0c20420101d1100040e084d0204c5a1a0b40700c000314150400d070b090b109101030420882a40c0d25005204001c4030000811992809040f4413660b071062810110040b900280c1d004012078180700300081d11782200401c100481d82074400d17600030380c3d40d85c5846000040103504000300b100c5280d828400301c01501800856407009070750406540126100403000e04050388140c80e0341e0300c00003012505020011a50034014610ba0a019400115103810505030003400c0100b0b201c00b58498942d0450b040c0102c0d92000c0495804bd00c107040702180900e10304000500d1809054980c03241031100c200310301d0400c403001c405810a82460010f4582c030701042e5181d60814410605103a5040d0010000505440856201d5581207802803804540580000c15424a1544903460000c0081400d404020030070140c0300001d400b80101c40d8061004a0021013101d98450796402054006980444d5400700180701d0b5003542e00b100c3d0010b0115141e821700d41442848402021144800140e4046c000d40c9200c22108454032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 946193165 1250 946191915 946191929
    0x9050a020a0225030605070305090708010515060d110a1115061f090f09020c070803090612130c091a0a2103031d0c03190308060105070515090303060109060306 70
    0xb8035403110f0f40c0140a2108003407030b000c2008010340120128013580315040c860a01d9840008540c100580080e00e040060341c001400741c1e0500007001300011400206413400742c01502c4883e200c811903421140a481f076000c1e00c000303604020800c103200340c0c0d01c16400c1850501c9582a100800b00d40402d040c4070b04004c1798902d400800e8180078040051200303882421175120f5260155a00e0f40702c5992601844130340c0d0058001c66004100807a18038011312403a4000d00521000307514200c6c040300420182c0c0580500b8441480c803030b600250300211040401a40640d00c1141c05828a0300c801e08a001000c280c140030601c00700c1c06050901d1401c0c401e00300c8041e00c014400c0010041c040c0000100c411040103c124101502e421200c07400b400c025954011003800780000d4403040c01901c043c5854220001140f11242002064110101e03800c402040c1e0041c0086c80c01c5036607452241000c91402074005c08481d00303c600c280410600202c007101a60095000b41c1e00d081e00959140c000300c0a482660040355 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 946194415 1250 946193165 946193173
    0x9090a110111031314010f0504120b0c0c010f0c030e0303070c150e0703060506090606040e0604020a0c020d0b010819050c060a021c0203030403170919050705040905030409050a020a02 80
    0x42800e40c0034007000328a0709010b400300e91501c44854600c0012400076400010284085218802113680001400c000070304145016800c10346001e44564801440d11801b80a18031004081100b0756000f10840c1c8880b01100028842002c0d1a400f0900915a2103100c0001900c2c003035144c80091130100449001e00d0300703035842009040f000e0321028440720425007101801ea540c0c2c0c10700d09071110240703d4140210300a401c0000c03180350803814000300001c010b00c10780c41180100401e000204200a031a600240250303001070b00c41351000d000380c50f14018078001035400540c3c5680c280410805020b154182e46507042a50404801800c01c0c4038042a40c10004203280c01154800140381800405820304950610440c2c00e00706843c00d4100c408445000c82d500181c00c004100420300d03070411340c500c0c043c0d501c10445011a00c0e04481507510381c8905550010222072100c1c001013800070811408014001c010003c20000d9490303c2c10b190740e036005108403001ca80c100320001c5c0342c0103c58400c0c0c0c1c2c2c0c2181d154000d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 946195665 1250 946194415 946194443
    0xc0c010e1008070921140c1003090c09050c0a1103131406041502060106020c0f010f030906090b0a0903020115030c0b0f07050709020403061a031b0f0904030c0209090a 73
    0x82d54031060003001c00c0704202010900241884920500301c400c000750483e100603006650810b6130341095a22100c2580c1d9200305a4200301e601d40c10806281e1002c94540041c0300c800c140f40003500f15602e680b00584e114180002c0c85001070002c8010300a44007980ca418001084802e4040e07282d0246002140040c42c03480000c10018a003018084506103000302098542a214006241030203e5503807403034016800b040041c0102034040040607020001290383d1030064444100080054058015031410103845800460402125030481e4141e1036008010742c44c14030306a1060b0000307040d1603074164019800d10800d40010344090740640c0540c0d810600582a05003000610100d9510440758605545401c0200b0760108509001080103071400350409644d40c0c1ca581000b50565034442ca0706010203a905400c2e030343c075540004003041508080d040c0d00e011210a44001002041503036032003900903050390708020400d40d02002604016100301ca021803203803500365210f030390f901c03080c840100700a94503000c03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 946196915 1250 946195665 946195667
    0x210130150b0f0423070905030a060245012c030f0703050c1008100512010603020310060905010e13020d02042d110c030f070606030203070b0c0c010e10 66
    0x2050005400250100600c0c0c180e8101240480b104650341004001d40300f0403a41c0e41000c044c0c403103034002c61030f40b40000c280c40c101f0380000c0e184e0020507030080519900080310800100141c0c1d15004d5503c0380f8250183c082c40c65046004c0c65411080143d110049992201c81c4c507600a900140c0d211616840806046410086220b108140201030951500c12006e880c05c243d00c0070003209002d580301d0005030800d003140200b03125a00c174200d1300d00000d1110004c100f040300300000c21030720101c407402c88440e00b0100303072003840c18010005600065014061051078200c170b80e03080d40200085404031402000242c0ea607148204065809460b0010041a2a13200c04003510b015400440c0080c0000c1c800500800e2030301030704035265002900541034041400f41441c0c42000791088602c5200718000062a120b0886c41c1251a4800d1244918695501090840900803168005406554060212801941c84412491994001c034102200611030118080c40551041d17a58840f0600003a201d60302900d04400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 946198165 1250 946196915 946196921
    0x603141608071d10050d0c080c0d030c02090711070618080a030203160305040f06080601020c030601080703030c050a0b1f050f06090108060d08040b0a0207150206070521013015 77
    0x90b11040c07441c104d0020600b507581c003142c070007014800d400315031103680362000b07003410646000c4035580300d00b4000b40303214042600040f02d0403000e64111101d0272590750b1303203000741d50040e00303014500e80a00c103140020490940001c1101400e0041c0455003000d169201d1645a655494400083c0180c2082c04034003403c2c83ea89000d0741e015032180c1002401c09480d12003092420714a40d11210000340b4940074040e0650301405100d05c0c0c5801900038101560411241507941c3ca103d220003000c011445c004007050210902000e01c0392907004030880e04608061120240c48072521792400780c20b41180034002000d10b050029640c2740384020b401c0d00e0400c000c0600544207032030020111034100c10700d5100c0c64005112580140003400001344d0700b40d20703440c104000074079104407500000d0101180c400304807403407500000c1c2c40764440c105140c82550b841078001741c6d08400c58012041440ea4034070700004200c1c100407613084115400000d400e509450140089e1811441d42540050000700301c0007540d030b28501082d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 946199415 1250 946198165 946198171
    0x3090612100504090632010501230a0c0c0e07020d0804140601090609060f03050304031b09050c030a050a0b012a021e04140c030a0f0603141608071d 65
    0x1078240740c8030303522030115058441c4080c00302c84a03a9250603406c212040c43e40480e44e005040550039002c107192403000449500c060040f2070600110640b00b0101880700a540c0c96111b6000407480d803510a0355001914901c5001c00c116404120000b01180f00000701d8079451042009038011304100619200980e110503003d03009641c6911401e0f2803590a940800061b030007080359100010b49185802021411901c80e60040c80d0485030110301040414800000da030f06998000c42c1c0700e10524204071403901d102c4929407060640c18284404c01030340400c07072009544641c600d40d40c14041d80d0355089080c3d045480851a0300e010859600002e2051000284000c2074072848400983c0442c2c15034000034050540c020080209005890014469091074010751051458210102c522410a2080101180001041258215690340c0014100d00c401c0d0032990045801442e050280c1000041e015121000325504148030302244000113124080014894120f40000c0c480981a107584030030104150b01c09 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 946200665 1250 946199415 946199431
    0x50c090f130b0411030f06070806060a0c02090604090f060501050f010e180702070b0f04150305010303120203060411040605091e0307030633081002070b0f090a080a0c020103060803090612 82
    0x41c4a00d13070540b810000c404034840380038001c01c1d091900800c010300070200100340d213010304e078140400510a41c200210812031a0b045800106540e01c40c0085401480d2040c8081c006050722103401082c08026402170f4183c1f0000d03038490420f07412010054840000001005402101c01c00c1c401e0609000095407640118052054506542e513032201c1c82c10f25004890095011503002500304001c0c0c13040e890405a10005080a102540c13450300c0140606240e271902d140010b80000004e051130303650713900803840c0c0030111000c02d440d40d80b0703044020060382110951600070f0a40c01030030b4100c8110111340409846009005000441c103641d168006070420804200045500b103054145c610709070380c61541c155008041d00c260492621701c1d02c0d0b02c2c1410340c00008904074410031a0070042110381009651007064034004101a444180d091031800140260240441c0703c040340c00701a050340303c00703282c01a5000341e80c00c1c0300e8680c513104407030b0b202d02c0394500442d030210081010401c1c10a2800c00e01d41d0003446 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 946201915 1250 946200665 946200683
    0x309031505280e07080c0f041b0804060605060d0542010309020a240f0f050a050904050705090a06080f1512060a090b150109032607050c090f130b04 65
    0x72203d15850b01105400804094001c51503d40140c149150305c19400d000898003844922210310186070280104030240c400c002d59130002034140011034014400a0201504050781c0b11414500c0e2401050f040d900d2079003120003042d0306541c951143d00c081d0031681e001021182504211405181c60305034115003103040c5920f40340384802607615408180001c00442c520a038886e142c2c61100c0c000d405032180031109025075189400050f980c071841401128003e41412581e46000360b400f581c0c140509200994082d003000108452250300501400541500340e9412001c251114410742e0003120858170020b4416a04c8001026942024007086000401501e4606084681411a400c210f800c4605904840d00d40f0107020170440c6e1b0160300c40d80140001380420a05200ca000202007041c2840054602410360380180c81e080358088030245100c002c9100d90b50f403a00280b0309507840d6400042071134803640c00200010303040e40c0c1e003950244c45014290f1845604004607640e242d410744000e803003920801d076 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 946203165 1250 946201915 946201931
    0xe010e0406090516020312040206070f081305040f06030305160c1a09100e010503240307090b041103071407050106032a06090503071a0c0307030903150528 68
    0x8039031041c0703400b40c80c40e0803021a0518060002c50a40f0a03504048011513204019987c200c485c0b003950030b50490342c100c810345e5841c00c1d5030510103c04000d15801914460000503110302d100032601058040b14002d07070341840201d100c030410204481d06880080e000c510200007000c440190b040803462031a03c2070ba8041070035901c0c0c1240b0782c1c6400c0e00554010040030f001400b0ac03098030b05003600c800e5040d01440c0c1240382500d1807000900c0342c08081c002c1c4414070417455840070b1030b4060983c84200140041c0803540d00e9039032092a0300140007000c2000b40a00e1038003030710140903410501260b20542e59602c3d40800200c0c402a01400d0f40c0c0700c8081660745540c0c0e0500400007c801041209680040c421080928107441c402c0c071050313a6007680b111062111030b010400c001d4501285400031240010b01d01c0304569507034115035005100b14034080000d0b0000081e100d00b0181c2002038482940d0044c0010a0455514031400d0304480054034000220309511700c0c01405540545082000849810301c0451261 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 946204415 1250 946203165 946203169
    0xb0304021f0810091a010302071505072309010e0d0525081009031d0d1a07020f07031106030406180c08010b090c0d0c050c0319030e0a11010e010e 64
    0x1070390a00da000042c402070502090038040c1c00090003030001c00c0410014510141a00b00c01040340780d4081e8141500030441c00c09008091500b803451070030703000d010f00a924003031000034072030402103c42100c2111191a0601d9020124040c3c541c640c074113858810840c240c08040003410394500004031854441c200500c0d1412410101011031030040c0014400c407503080903035090034103c081412031516450078500d80e0110b540414411444114943c815101e4405080480c8080717400c040040c1c0780c9020960040401956801e2052207440b80d5825182001c10302d0b0f41043d01c0e03507124070018001c070061140115803403402030000c1d82c000e07108050002d107284052a00e5131800b140c80c01c060725000e90400082000d400203018003250040e0469502c071040c42d0a1422400a024501e04130700e50580c1c52078107910407405030044904084400040f40d0f1114000902400c500125007038580009080420803540103400203215900d4a60086a46c14800e14002c011220703194501a014108003169440c2d003040e07 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 946205665 1250 946204415 946204459
    0x7170f01060804240b120f100b040e12090906220f021209010c0915200309030316050c01080103030f08061903030e030c0f090408030712181103070f0b030402 69
    0x4403120301d001141565100c4c5c20400808211540c0c0d1003607400145110010410118110310500850300307000503821040c102050040c01d40303c40ca41c803548140741408184080d0701c4040d00c00000111020a01951039900340100700f403d003904843c11040c910f001c80107040c165000b800030b5442503a0010b040180c00e5900c401540c81c107a9014025035501e086000d01c280d03110b0165006001804644081c02d03a41640080c0302d0310341e0290380340d000560100c0d00b1444c803c0c21300c21582c105000500300c0761101614040500c0c4030980c41000c44407441000d150b02615400303207034014102c0f605901e03070000c449a441030544103d200103002c158009030b0380d0703151a00e40031801c410b42d000c0c501968071b481400c0d0400080c5860f00d64208102403040c2258107440310150354400405a20581c0000c3c3e4980700d45032120251070403100d01408205a9040a04ae000c81d54030241200c1c040768090040e10b0f07049000c072001e160b10350099003d08180075110090071301012401c0401944c2041c40a40400c008245103044400c0c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 946206915 1250 946205665 946205723
    0xf03180210080f010e06030c011805060f0309192d0b091e0304030c060f0203040e0103080a02190b1506040503030304050d080a0608030301060c020f04110307170f01060804 75
    0xc500d600c0c09200c1d020000c003d02c1409050760524240082c20901d00117569802c0400d502410040904038401340609600c0024000b40009480306440b0002100e41000d42d400881d060809423140a0001281031224880340084c2600083d4010034420491002c0a50080e50000741d910740b540220200009001c0b007402c54800c000303038005081e05940c4100c8000b9900b044501100c0e03144c0c410302c002e00c0410800d05028089824038185402c951401c41001c2c1d055005590000e8510070300c2c040000300f0300c490100102600c000603801d4826000403540c15a00118000402411b8030aa40700094140510303865100e28019009010314109907441c40024515031081b101100c9030b400c07640c08124404d4100030016040000c024050141c81e007004a1035940340414071842007040514a803010641d240c0340304140050170042c0060003200d12801c03951110341d00c01e840744000902c22644491507a00d0a09285000d2800b020000d0341c1640f810f041140d80c680040c2083d03ca03903090038010306031038040c1006103003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 946208165 1250 946206915 946206917
    0x9060d050607031a0d11010c1b031a0702031e0a020a15020c1504030804060f0204031b051926190b0f10061b030e0402040305030301030b0c07030f03180210 68
    0x11a02c0305103030440700044030501205c2c060003002030120f0000707041c1028184107980a1030f1900c43c540c0700d801d080c1800d172813140b0f026412944880c0080207000c0c40b441002c1c1d151a400171004000c2d2a80c00c4204c1e034910401c03080f50561540c003080c42c1c46040d01040101000e0700640b0498218980b180c80c1c51502101c50140c0f10f140640c0004d05040080c020311181840c0e44045100710014501602c01620800004200500326a51007100900d42c00d81907054401440d00140030000c040c00c0072050301743c0c800d2a809024410304080d4140824801c1020110040e20408403091001290020105100c0c1c221080f806099005912248036242542c4a10244460003908184507504080040034405400502441c4c84031f026064180302c6160010940622100300600350300450306181000c540d024a60391030564013034000200002406000006141a20301a1201c52920f84540b80c40d01c690340b003069001808669078000424146009500c039184102d10b00c0c2c2100480c408a5000801007048400c60310 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 946209415 1250 946208165 946208171
    0x90a0f21030207060c090806041e0b0403031406030f030f070203070509250212041e0f08071a2104080c10050915060a12060f0c09082401030209060d05060703 69
    0x10044c4402c500805940c8080c80c1403405d0918108210180c035050300070005070003164240404010007001c0d02a041c0180d800899041441c00e19203001005003841200544242e24000c01140d0786140218404004ad00050011890032803100d11100b9250000601a80e241c0101500000c0036240d4201c00351107000d0114402c0701c050b4603180c61000418400d03808100315444007882c4181c1c0c1d84801d0403030302610000031020f1001c11138800304240c41d841c90703044030782c42540d00c41c400651004000707005004e03282210504117000d50507820301155070185050041e82154045910708109025100c4141c11a000b1140f09192100d045042423a21907101c80d5450680ea480d4200000058141f02c03041002e0035040c0002c0702800c0403c00508201c016018010b1070312140410b5408109080d4052588141c40e080300788180c4c0040c0c000600003019a01c00c004182c01641c09001c21f8502c83c00c511000e9915458400e00c0701d03400e540030301591040060040b40c202c030380481d4075000b081c000c0100ca44100340581d408 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 946210665 1250 946209415 946209427
    0x606090a2705012406080c0322030201230c040e06130908071703100b0d0e07090b01020705030a03050301120f0f05060114041e0f0212010e0109050708090a0f210302 72
    0x220003c242890200e42d64429072401d020065006d5003098000d15006d081030740342e4560390b02c002c903400d0b030031800c50040030a404100c2c0c0815070190071980024800d80580107003041c051508040755942183c034005010303002c0100740841d40e02031400581004028240007050f0f190121481c0456400b030206664000d00072840d07400f00403032410102c01c0e001d000c13001903066007050401054400b040d4001c001130140701064261070705e207a035404100502403400442d120f0507682c01e0030344028588150002d006000351300380071840307007400100c284150307074141d8400b861a032074001400882031048000b00c501401c130b160107002180c40c0310000300704c040c080c070003030b2080b54501240c4020402416100307501560030060703000c841040d03440040381c4140d0b01440100c3c044105101c1c800007032050360362905007e03400d07400110b00c0319220400103060f80c000600402060300ca0544c1942e481400301d0b0181c20a9000e030b420440010400100c00960398414045044086110200660000c01c1000c4000c0003a50105032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 946211915 1250 946210665 946210691
    0x1515020a05011823010f11030603010608060609011e0504020f191e08180115030b061804111f0309020307050d020306010b0f070507090504140606090a270501 69
    0x18842d084104030035a4112428240d5440d0209881c000203c601c0211100400c881d9810039000751b40390b0291045c040080c0005c20300c0d028580c0e00141c5283e4000d42c0b8208cc080344034800002d10030700404009002d44096881d00001c002d5851180074407845000300c004000900d9180c0b40040c02a41a05000058490140c2d011105000c5a400e440b0003c22580c1c0081004445e0030061082c41d5010600d0102c609075a07180d445400c12100c2800b4020541c41c1c1444000c15128025120040c0c03403146481c4082c98a6038001c0180c00c88449001030f480160000101c0c00180c2410142200524040c080c01040c4c01051440d142e10f411182c3d180010903115911f1074214a41402804003070101129400320080b6503802107a9101c60500804c2454400000d00a100d00d08001c141c81d41d0907842421a01070544a124007409000e00b6181158006415000c030b900615000c51745610664000d00f24400d681c1c1c403028000040d00c02c00044070f50302c402c22900c0c90a6000c18071981140139001d0000460f40300e9007441 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 946213165 1250 946211915 946211921
    0x41a0a180c1d0c030106110309031002130b0918060102010b03010c0e100302070803010905040201020a14070f080d14030c13080f070602030f04031506080307060b101409041515020a0501 81
    0x190440b085219804000100c414081900e065403074501e409079407200910406c916521800d5805070b03051084503850485000301e6001404403002c000c82c0c201e0007940d1a9203c000f103000340081c044e0f100c10441315420240801040c005c0d07004030140b00114507040c0c020301080c00c4501203403400d000140070386101446420100d0910395030117414a421403419802d0341380c055140c04103018030a01c003910b40010906581c1b00704103c13040541c00440c1c0c000110100e03140c4079515a60f6109180340c2c40c0c400640002d2000000c11508004c207020388030070080740a46015001244c0c0003c2c03c3c412000c505128241c1c01e441c4c560750100180c100078008141440348149000d00d85069548002e08643c410003031090700c807800b082035074100da5118213607003894603080c80490064503464103c641103110104240c41840125049070000d000d0581e0400c5500c6691081102d124192011303065580d0000c003c240380301c0c00c1c81e600500e01002d4020103882050388a5034101415184c0c0c040c5840140d21003181d20040c04420301c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 946214415 1250 946213165 946213199
    0x90506040c0515190507080d140c2506020408030a09090f05010302010f0e03010f0c03050613020f3403120b01030902090c1b0708030d050f041a0a180c 66
    0x10340c1444003c0c0e203040746070794910401e000e034401611004140002c141c05401035a89055001c0c4d04a91143c9107130071003000030f0400d0407207101490240c6d404503591b403a80504607224140016014600178241051800e01e0302c401c548211013850f400c00001a0504050000c1d110030041c0759640d00c101490b00c100d250070f80302c0801c2c07050b140910344001080180e0300b05001c0c3e20450f403141005c80d41e4100703402c0003a00500500c011502403c0c00e000c3c80005003540343e400f0920542c000c4401c2c00503452600744901c00ca015072007000000c00001c10016150804029070380c4000c0b142d041d1a00b51158950028a80780d01248c03000701d000c1481e000101152486c1c07130041c0705441100b1310341000448503d4000174180c2501038203604100070000b8100c001a04200d1200801850342c80803910074035661a0741650700c0d07001e50000380e06540303400042041d001603841014015900007040d040c00b072040c0089080144006401180c455540354101800307064846000f0101d40e000316600140249030851102684140c9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 946215665 1250 946214415 946214419
    0x20a051e0c0706080711030a0e030f1c210c0e120303060a030602091207060915030e0307290408071a0f1807030f0609060b01112806090506040c05 64
    0x1803068201e214400201da6003240c80a2424652640310030000b075030080300c03091031502d047c00001011044e9a130000100c1d001d9803000c2c2d00700c8900400d4130b10b041d52600107011048101c40790701070341c86000500c5004d24142110100707415801d142e10384041d0341c0446000c00e0210303011400b50141da06042c580840303049004c60084018503c1c52400c0300003c2d080000500000f8505540410a035002d6160b0035081c01c3c001074001d084840154407858090181b580c644101240e103806000f08100b400e02c24041d040350361b00c2c603000641c10708940e80e4030103040c1c280c20b542c1c40c0742c450707030042d41c540e07010001f241c3d5240164042d80600c0e580b440c00f402d00c268968040c40c1305c020081c400c042488060381e500503107654001100d0b0700030040d12240c2215142050281d80c00070709101440304541d000e010b4075902010171540304003001c00201004800559039007031080f40c079900c0c1d60840c10b444101c121192105520715254018161041c04183e5203c41c2183c49801c0c0070b8031640c0c42501000308111141407a10064201 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 946216915 1250 946215665 946215667
    0x6100806010b0a0e010302131d0105090903070201140d11130906120b060d0519081b07180203100510030c0f1b1401020f0307080f011a031f0504020a051e 67
    0x41c03c8084c10200072441031904141c0e000901d03600141c1c501c1282e0024114420208031522a4016445101e40c000c1c09075078850452a4003141044000100729600c0c1e5a0603141c45602c6802680001e80603005018240800d17501d411a9941c41c2d1411801054400000da0022a03014100104542100c203507070040b1814800007a4042e000c100904801c90f0700142c121140c0140c11104d1802a061200c2003a40c4c4c9240004412414200409032003c0d10a000031074100c1001038000381e03e22541d4070286d105450714001d028040e0001c10200b500111b42c0655980d00181c4866aa00c001c500ca20040e03000520000796602d8030001c01c0342e408824482a0720040c540318020201e0100c3c8240745109000c0002c140c0211460744408000080d01a619503409c281c03410380e101d00d440040175006440c00c4403494080290b0704008502c1c803203ea1080a424820150f9450235681c41d84100400315031412407107418200703042000502c594490000301074110f02c0769940390300c9440c012084548002100022031480708 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 946218165 1250 946216915 946216927
    0x905150912040b160501020a03230f0415150b07061b090504021303020603070e030706020105011410031b03020a0306050103180b1902031f05032d0f06100806010b 71
    0x1d40381007070b1010307a4207400c1c0d9181e0f10a00c1c41e400740004001004000c1c0154000329070382a07a05c0e016401340501407c81c0e03589002d20f8100184200b0700b03203011100002d40060036404500860078400071306110710a20140080e000800202008030500c10380e00092481e00000744040421640d80501c500800d640924402e41002104020301280002d0086078019a0702040b044018081c0e48100e80065402504040c0d480c204040024083c141c03a4804c180a407094510004540d4414410301e4122862016840107151a01081004162803000318504064841341c107540304502982004040d1000c0707440c0181d41d000e1888002d010b4540a921080c181440e015070204101c004420984085a00c254980c1480d0703910b00000003181c9d1101e0700050107034808010071a008411000101d1640c0c895400c6a130001d94460030140c0d1130704a421495003100c0044948a2029450031500071241101d0301600d00ba807840c0145a031610b00120748103100407009010030048004244490740c0541030001d1024a00a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 946219415 1250 946218165 946218193
    0x311040b0409051c0909022a030705070303050d0f0c0c0506071719021b030a1206050f0405040512070b040b060315160c020a03080702040c0e150304080d09051509 71
    0x1482c00300300e800c4131800111840440520401420001e400c42c1704045485000d02c0386180701c0c648103542c4050031028601480d0720003042c0081581c1046902c03a0050085604641d802c40b89500008100c41e005521125010b0b1040414001c0a8040700207941c2e162004200f03051951801101a180c2000d20000c0442011015103258a19034403000380c04214041501407008000203200e51003040c00c0c0c0d5040d05042c82e40004010006094101c810307652120400b121041440458400b07104540d17200b14100402201030516400541c4d11a0251059441c0980420b1004e111a0b0142c0c000b102e0651180b8104801c001c3da541d417068200034150300074031350001e4280480610b00400b420389000e00070350003000c1710203a01c42c0d11480511517001e80300b0380480c2da9901d01800d40c7d07084008128810750500c0075014a10388a140310008202c0001e00c0c621002c1c00307602d0014030550012b48107a440346400c01c00401c030108240907221384140300790010410801c0101c0311910195000c0e00d4003907107401c904c056440803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 946220665 1250 946219415 946219423
    0xd1a0a030b2e1a070c06020304031b1809052814010b090601120e030a030504151104090b04060306050c090907021518030c010f0204090b01050c06041106070c0311040b040905 76
    0x140751014072080c0e000c03034201d4a200d070314021204010081c048101000c1010369021024108991245840c142142d0792a1030b2f000c1200307004d0050006880c19814200017480f500e4002c40300f0342c2e0184050750401080c0011048004880c452404500340d0a0107012040007903580710b0b548040b9081000700031200c000c5d00013881c3e84501414050401c80048490012005940e000c0b8910501c1002141c1e0744000c43d400280203418100c2c1e080d684602e4000d0400d01500d014090a060321080300d600502e01130620280c8802404810340300d6130029a5041d004c070004459100303a50180403400d02d83d60721000d410b020800c1e00e610060850342150446404018001304100c1850340001d0004049070000501507403e914500840710102155070818500b01c15040ca00d500070820760700100c1080c00422101b00054450b441103500c8801f00e98860000074000c29103441002c400080000c2510f46403c4503501c0b114a18013140d0015200103050900461a5207811700c91040c410200383c909100c200c00a484003515 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 946221915 1250 946220665 946220669
    0x30e0f06040b0a09080d05090d1b03080601110f07030501020702190315020f0f0315100f121a060f040513093f020f0618030d1a0a030b2e 60
    0x510789981310541000420740582e40c80c1003030303803e00b0840d0349070054030103594088002d2440c02048458011040c50b00ca83c04129041507015110b00300642c030b03007400442c1d10804a56001c0001e006c1c01351994403507502404594010742c080c2c00090307290095401003000568800c0c5252415068101007000010046581901117a1201c2001038440000b003d1000c064487e464541c02c80840c0002000b00b810740c500110a0f214000b90344050941542c0841903a0503030f2440302c010302080099a25200160041e0450421400111921007505200c40082a4560071468804100c0c1c40045010b00003400c181d0150f400011904109200451032511510702c0c10545100403210380700b4440e0b02d08450382e2809502c1c0301904580085454070b105415000b9104c503010b10401c0e041e070096001054000c1070000140380303004150006035242c0000c00c5c50f00350003031012480c810032648000544440668960203400002e40c0100642c29007440d01a245407039440c1642050b13010a541b90583e030307030000200c0c40c084007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 946223021 1106 946221915 946221931
    0x8070306241e08030313061503020d15050a02040b0a08150a080c01030e030c0d0804110301090809190308182101090210050304030e22050106030e0f06040b 68
    0x51284011b8503401400003442e0450404140380c0c0d400210f803000c11184401010740e4a901052400c90041c00039074044000c4800e840e040c02590240c0c550000340800b08515150400342c2e04585401981e03c078800700a90040002d69061680f05000040744004094039619699148210703a10001d031003d05000030f00740640e20b51010000000d40380010400805032213600340e83c48088404020061007543c05a8400b000c9810a440c203118a407231640c0a92800303542e503aa0071052107a00f4549842002c02041c5005041000c0303104042a20748040340d101c040440240d49200103404980303031404500c078141c0d03861496902080305500260605100340c4201848c618501c10030344190104813405004200e000d194a00c80d49040054200611008640e0320180303402c890484c41118800d806c030030003090384c50b410140000c100304040c0c01e61001805c024612883c007540c030541c1c25500500084 = true := by decide +kernel

theorem cover : BRFrame.Cov 946043165 946223021 := by
  have h0 := BRFrame.cov_init 946043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 946043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 946043165 ≤ n) (h2 : n < 946223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
