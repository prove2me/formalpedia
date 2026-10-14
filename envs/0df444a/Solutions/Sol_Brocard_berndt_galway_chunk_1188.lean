-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1188
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:40:04.530355+00:00
-- url     : https://prove2.me/submissions/b1fbada1-ccd6-4181-bb99-75d37b64e83c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 213489208 ≤ n < 213669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 213490458 1250 213489208 213489217
    0x90a030f0f12050a03051605030105011b0f050a021201021827010f0501031503081e1905130509040f0620040305030d1b080105060313050d1e0c05031c060506 69
    0xd4076407a558401c810f60045c225140100041c1c0c0342030706601c5a400840d0320005a90640d43c083c2051100f030b5481024402c03c1e0000d07103200900718401002448200321003c14900030345403003070b80c00d2040440ca0304030040c01e07400360b0b10740e0328540c0000208090140c601074200b018118110170400910700303403100c0800246002600814a0701990000801007964144180e04444c101082d0122401e81565901400d500c5218220749070b0742d9001c480001002c10840448900b18806014030408100c03140001d005a0400300544c11341c0309a4035800903050410b40c032507601c110303481101c00c40540c3d0190341d004002c003203660450b98000c803104412001d010000000f000070354040c2000313544410f0104003c1c81650381001d42701c3c2d40c540e01c946201203840e0300301c20741d2810743e0001c9032801e0700d0ba0b41d8817188501c044a9280d018040d4450f11181404440d0805c036040c1c8003a13131414030225600c483c1c40080c1c03446040000014070603403003041901556071840b609001161a8003c01190442d03035000014282d410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 213491708 1250 213490458 213490493
    0x206071e050601050612060f0312040609030c0518040b040c0f030b090f010c0c20040f02070b06040608030f090a08060408030703140412030e12040920090a030f0f 71
    0x5200c2030910a0100400c0807600510007103c245190180625000c5900c2c03201030080d40c01041c0b107010081141e50144003284214010410241d162903a40c5002000e201032484141c41c444d01c6010007044c141411200c142410b1700c1c40100b03038001d407907581d94646400801070040e1220100d150010503283c50151007900114011401e121132414504001800c3c69180d402071f0749640e142c192000e006903000280c0d00206600141c6003040251040c10600d0142c5200c40740c55449442d1038410045038003e54064026240280300e4501c3c03554030b00c4c040c0000c8484a014020b03150340140166405240750f54006c10003100d0217031140c0626036880c0d40b114070303040080e10220b4501101204111080358944220011901084080e201e035082c0b5480b840c00146203000807034101600e8000250030400d0403c49070710b0a948226a03190f507140d8901001000745250080704a580c4402c94900c039030201c140050300d201b104018401794199165646540c44101202d00450300244114040400319061601c149510780 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 213492958 1250 213491708 213491753
    0x105010c06090507080d02060c12061011030f0703030c020d0e0613050301050403320a200a0804090f0203010509130c03080f0a0e03030313030f02012c24070309020607 73
    0x686c907a10103030506170000c10b42c039400b1100340144004009050404c542015042c3c03481c8910a01007c012104000c603000304035614480090726a8070b5840847c0208005130003690304002a11000004a0f00c40b04070380d500b1000180d100306485a14600007004021281a01c9000c81c6041c0d9182c000c00c0c25a841220107401181100000e0000e070600b0306113856200b0010415014582141a1500001e0096103042401c000003a802c1102c0c0503010640d92040340510011161025a6072900300d5a82d80705019160443d070070030b0001d20780d551950094905848005003600203e55030300f074807500d400d0440b81056500320070400e0000f0200b100d08000b0050300304101d5080c2d90f205103049015181c00038080d1560f00035402042008010300d516000600b0481d854070340300481e00c01c1542c04a0252104031082d0081c0444108580c08008407038214002c000101002d6507040d00e0920130606580941c110900002d1180100003040c0030710950003109024401080b603800d04031103448040c07a58242141071035a50 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 213494208 1250 213492958 213492973
    0x8011d0a05060105251403030403090e0c07051b0a0602030c030f0703020327100905100c1704260d0c110109171605300f0625050a080105010c0609050708 67
    0x80d44010b160090701b00c0f00003103180d400c0698009209256a201c0c3c02c0407240c0160104402044800480c0d00c503d0300074044500144103180c215080410000341548190041c810000b0503900200982d003054865001950070800940701d02d90302540b007103c04404500040189003071030b142c20b648101802d042102030480184681c0d062228108980c00880c06202d44d0610401a96841c45203007869404103150a00321005030f0703d40070320748080a80104103a0607000c107000c5100c07402204040c9000704900b0041e0f003d14920f040d0f107501c81104112030400220700c000c1c0752010801c030704041501d00d001850301d400095520000382402000b80d00540d40507800041b110849043c0903040310000c3c200480e4030003040042d5840040f01100d07403154102d00782c1c04200c070300e5490034801c1c80423a01c1c0c0850142520300c0c030b1a080d040c80a080c4440950300810340c48549000c40010311802c00e8840825241d200da04859003030000550340c401090101710b1301d50341c440680600041051110f07100400d102d000a0518 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 213495458 1250 213494208 213494213
    0x6090d0201060603110304030e040e010e10060905040c05010809030d05190b0f06180d0b070c120503060105120a020c10150b091003110c010903020d08011d0a0506010525 74
    0x95800c0b41e440202010700302000015018056401c50382c209606040c1180005400d0001c5405801c0b4040b00003101c1d442c00000341c1ca064070208ac070810102415504100705a11044518104c03201070300d002d00140e07070b0b010045c4000c0d402101c201b0f40090710f0200311390a101c541c40111003036500031990004c1d41c0c0c0b510406040a8909405001e01c00502110b0b1150816120008503109000f5000c85080703008100c100441c031a21080511181290041004941440e040101a040b604001002c40c0c1c07481c2111464841c00d4400e80541e40a0041699054506440310724104500c44016010000040d4200a07060196500b0000002e01459052020030072510211500240541c150f01c041405c240402940d900e81e55001040000d1400c603060000e4001d0821004a640c1d0041c49852140d035032070000300000b8950001003c400c0845603684940050b030325101d003402c5021905070440000000303400030880314031090300541d50205040c5000c2d400c2040600341406034221500c0007172452006903009106 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 213496708 1250 213495458 213495461
    0x60504031502031308090a09150515040e04030e0a080d0c0605151804110607060b03010605011e0309080f040609050901060302070201021b0a030b09060601170709120501060806090d0201 81
    0x2214903024804600f50b150980e00320040c1d0991903801821030000240b65070180c0d40b8244070380c010b17080c603000401c100f2401d0501c03940b5841882c024548a5803130300051000708074410b01107905445008001c00b00740c0e1103e40e015135661301c0e030a90031540f10450000c085101d800800c2a485000580e40d180c90303205400b802c000049450103080101480d004c121610220b444491600354000074400d04207140745d8403414005440e040780610035500090004044090100c1a001480010802c40c0208125583e50f0015a403102500850000010800e4101051203000c0e0340f20f070025a000d0307001145082c03555651082a68007603001071000c030700140d600748003a0038134035412030160006080031450104141c0008c1e6684410414600c108800c84500140725103c15880100540c2d005200e542075003480c0e2041d0391200d00440340d842c000749442154000003d42c0b600564060720080d15004ca40c9414940c039150800ea03c001c00f0b4505648a9600245a1000b04020b42c0303d00e6203d0090a843e8a100a00a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 213497958 1250 213496708 213496733
    0xf04020f031606120f02041706060a0302010c02060a020a121d0306010807030b10030606030c152f010212090c090718060e030a0605040c14090903030708040203031306050403 76
    0x41c025800940d84040300d69030504080c09650710341c103001001a91200c2802d01800c00b20b0417480005001150000308446a40320f0803190180c0401922000c2d03654805000000c0042d11010303000502c80f800410141c1004030051080e14001d2040d958106d03920389400d03248480074607104c0b0000b401d4180d65107515203680c50051602c002100a0030f0b0703551410204a07900d0000c1c2c0006442912418041100f05c2e20000c10400115070025042c002c0b1039890509180c01d00041c0b042c02503d03401c506403000910321400007000d030042048140c5003074414821003005590100c01440e2110340d42040809194100b034000c040c4034200e0007004100e40303044001030201d0020042c1104092007200c00c4800103a5210704408402d841c4245408004000400c0001c0d103400490031000c1c02031460802800140400f0b000036509490500000c030710705403038103c140204508c0c02c0381c50010b40d401c10b00202d062079104a20382900580000c0480741005228015107a0078081a407020703000c07a000190400c10007600d80c0001c5e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 213499208 1250 213497958 213497989
    0x40201120f05010b030a15230d151a010c051f0209090a0207050712110d0f0209150906371e030611120403120e0d030b12030a050406030906140f0402 65
    0x451142c1c81c042e00c0c02800701190020b222041c03a00d40000d032306612414a00f0752142d4100ca150503114843c0501c603801040001c1a660480e820071850601b0b0b54068007401866030f61210083c25000c12501c94440603050700d66034414680c1d000c0084041c281c1e00c081100f8090780c11114010b03500d540300c1c500b81d80751944c540d00440070030307280d0911140821019000e001e007c01c4261410f0811280c0c501d801240071300ca110001794000740140070700000072101d00f0301e500103480239540c203940e03130311a4000c02c901402c1c403045145cbd6410b0091a03201d456425842c8444003185203000342c0c4500c945910580340142ca0300c0210440105100030304209100860042030001d51860b0f020f1450f040451001c40804d50703005001506101d034a15400313210b109158440e91a0900f034006a80041003405c00040160603001c20003817080d52083c5c101d04011201000f100d01e00d4025480b100d2819240100a801030000b03040291940f41d0754039083c20705110521009886140040c94155442c5880d10400070002d2169291 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 213500458 1250 213499208 213499241
    0xf11030f1b070c150c15090501060b0a0806031b060f0f0f210c03100312020f0706030c0e060f030121051903030f0509030405010309050f15040308011706040201120f05010b030a 77
    0x817034021030b428480008281c80700b0f0780c01140341c3c4010706010703015005950107220011000126a04001d50050340c071070040204506840c00300d0003210780e41c00c085c0c0400c00c20513401401045041d600001d0b01c8000d0140380103000d510f504068141e5181c03501c0ba0040c2c3c11010b404200105082600704400d000c2550001d50910150306509142c01c8505020300a804001c06a1884402d229030082c0200710b1080120142d100310b0322010f8868200401405503001c154001c036031040d0701520b591a00c00141c03909285046109400d42e0f1074101c00900301c10040d40d0141700c404400c54442c1c04148140680816176140750000e1104040515006089500f51804100018602802c2c400c5540300401150704640d400d01e07011413140386904001d82003548017000014188206a40103440b0341202251030300c600e00a03290381005030303a200c41c2d081103c51031280190403600030f1000500158086c58454103c01ca070b0040004d1034520501c10482191f20030307044418444070100c1081442d005c03034096190001e0000c0391 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 213501708 1250 213500458 213500477
    0xc020d02120a03021c0501080709060608041e0f0c06080628030308060402040803040e0603010b0901080a1721090111070c0506090f0907050d0f11030f1b070c15 70
    0x2209502d000c0c015000302015000100c844c0e02c8000540c4030080366500c0d20041085507590000390350749800d140308a5807040d0804000060860041c41c2c401e00c41d640044011010760007014800c41c005d012500d0859082c0f1009140307001240d640240c0d00d0141c00151075410302e0f03050070000c0105119049031000950780d090001350000d1580c001286044a5043c10030404903113607100043c001c1c1c040c5403c5170840340710100380015040020003216000c0e0a007038000b003028529000501504140c00d000315001c56100540040000d0713180c5c2000c15003034100b4503580b824080019448041303080116075190b16101943c0034440051402e10506958088080145103020119a02c8043c0500d0501c542c510804000c43c900440343c071441c0380c04007540c100030000030803071a01c018040d255411500000311228035041040c0c400000070b10480421100c144181411542d8054000d040080c0041a06a4000800074001d01e94102070b000340441074819805219024181003a00264000414001007000744116 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 213502958 1250 213501708 213501733
    0x7110a0f020405280b030304210c090212041103030f04060f0e0402030115031812020703030e0a140f040905060702070e1e0103140a0804060309110f03030d0e0f030d0c020d02 76
    0x340c41504100003c801045c800d84130382c00203043d0f01440c0c0c01001140c08103031846180d140e1036880030003014444c0c039003503120b40d4850030180e08a014901001340320680c0c0402240114902c160780d1003120b04024100c0f49010500f2440481d150000da00040101300f086a0400345c05401c441c030000078200a840850440d031501c490070507150841e2010070300f41a5507084e0504140e6180d1195100c00c0e0b001850302409803030280780256655641d210030380010703142102e4500c2c0c030701e00303040020110f920070002d1000c422850020002400c078003580701c0b41c1c1f02d50f64130004000180c003440b44030b20036403150700074101140c07400075501340c800c00042c4801280600070310603c41c0750388a842c189040d2034014003550684c48003030040628008291201515004000c500010a140c1c140c000f032100d04e2103030941d441000c4500051080b11a084504598950803d100090480c5c840c1d41c4010000071101d400c031015246884182820350b84200d03080792100b41c44e80c110041c0b268041100c0f5090411600c010000c400340c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 213504208 1250 213502958 213503011
    0x3010902090610050c0a0309050a06030c0c080a050c010c0e0f010903021c0201020307080309010b1516021e0402040b071e0305030103080a09170d1107030803060907110a0f020405 78
    0x800807441607071003900e14003d0a00c20b506890941807038208495800c02c1600f400303485401c0034854144102c2d0f000c0c03004107041d48a030242d0b2a02035a503484480002034590340e00706290b00890007500030460305001488154400340144080c10b601602c0d60b01c0801c1020b800c0c0080090140409414001005c00400041c1c651003040038440b038007400d01e031020358070a1004074158485e480000d020031401100340815220194400d0211403c100e0304e0010104011408464600480d4019007840c0251541d030070150804403549101c0601321a0f280785c2c40c2d082d076400982240c009401400740c080c130114425081000140801c0120079144128040500e160f60f130050042c44140402801c04401044044040c2d004040880103410709061203c0843c40b800d801c02e82c1c5540901070003000a281c40190986003001051001c141ea03040700340d862845c1d03184418031441e501c02074405401c1011030b85c400703644c1c10307400d0084c468103034070940c58290203c80340d00422060711000f900743c1000014100500048a211 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 213505458 1250 213504208 213504211
    0xd0812010603180c0e041a0703150f1d0615040603050109050c07020a030f05011d03071a011a07050c0d080d0e030a0e0904030c051609150803040612020708040b030702010b0301090209 80
    0x840da1009195607139103007580d040c62031045c071400314510a5091052301601034101c0181101890464102c050740d404110b0054151403061100000003900c980740000007803800c85a004102401501001500300440740841d4820340c0101c1c0080c1d961001840101010b0041c0c6411180720700c0751030304100700340c3c000844841141c40300a18100c1c40441c9101000300070b400c484070340305210440803010501250920380360f0f03114540860700804007600d45d440300c2c801c0d0048241606e01a81801c01c00e000140d41154039503000801c01e07101845002160402a41c0f2204c4100d4114402c511440d21a402a91000117482c029142c80c43d498006000c00122107503c85c000d940141c0040b603c2c00712680b90340c00c3c243c0d1368904104002e4124010750071480001040440d05408445c0d03000010005807281510001070036104c0e00404200b42c0042104011144c030075001c41c1800c01250310010700d002e403940e6030603c069019912800156001000300110b00e50203124447d5084421b50080c03015080503030004440d000c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 213506708 1250 213505458 213505469
    0x1140a0f18050d0b060102060907080c011101060902040902040f080102041809060e010609021c050603100e28030305090606090c0307020a15020405030601060207060203030705090d0812010603180c 86
    0x441c0e048000500010101c2600a05025107404001519800c00b100b10708002c0b1074850240c407801001c56041e4a00281c00070840704188041e091144980004403050795448a10210315902c401c408262102580b009200600707883c500140c0c0c0300d00e48054802c00f03c40640c000702e05a48140700c100001c083d42a0740641d00d040d10040054450700e40d10b4042c0040441102e0b00c6125032900b072011400105a42c010030184170044810245100000210b106550301162400e406802040c041c00b12000b0300c0e0000b141614804c0d00b90ac4503103130f4462444095910100c0b103507020070000094a4141501441450f40094500d07020300300f54540345c03000c01d071900c2008c0c005450f000c1c4e0000010f80200d1090180140c039030307840746100407052844130114003c1e410600441c2d00c2400b80100025031107000291348400c40340540c02440c00e680e1910419151a00003045c280c1d00000307031040c808002004500149892202902c003010103504003100201240c078a40548030000c01c1841c05400401c1c910ba400d00d08a68 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 213507958 1250 213506708 213506717
    0x6090723070204090b19050604091a090304080a080304031d01020d110c0d0b061302031e07030b060307080907090203070504030206030a0609050c070b0c072a08061501140a0f 76
    0x80c0d41c0c0c804036004001086010700110112002c1c0005281c040c810142c2d40c0ca00f1101c28800c81e1036140130807003243c070041c04c010450500a52603441e00d1400b600303103540c0300940f2003d40e81029540c4040a00703162455104076501e40002040108242d00013030310304101700c4004030031944900307402c00117581c59094020030360901900c0741c0410300342c030030802c40002501e50152070b4000380c061901d41402c00300c0c1d003070322280d00c03c0c009a180424a01d0051007a6403161202d030302110018078005801d42601140904094105078440060f00700da40c803000e00440c06491283e6550280b4542a60341608024890b0040e0b00303c03a00400c180105264403030107450035242c046400d03a903242c4800f040a4000c1046600c0a43c01c0f40c1080d080241c03500c26100680344d2640154801c0a2035a00e00310541d60300d00c01c0c104000c102c1d02c0005407244010703103103016240325850f0041204819544803080b43d0b01d05042210781100710741d240544103c4d10750340640402d08412070306103054102079071294058444c46010030000c0410 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 213509208 1250 213507958 213507967
    0x40f0308030a272303040e04080432010801060905120106150f090b0a3009060c02150c0f0c1903080a0c08040c030803090a1a06090723 59
    0x1811035900440d450069001040140d04603545014803400100c007080d212000318040d11802c2d400c0c0c604c00c02c884c1e040c91001452409080c0f81d60042c046074083c1c416600241c06110100300b42168100482c031041c162461216020b01004072151380c0040c094a407810090100b00400c107003034014500703605071001101c0c11180c031855000103e00610660b1310290070320000328805550307150000d03c0011070b041c20f50348148182d40c40313210f0001940308042005000600c8042d6201e0405080201101c1d40300321113030382d0440003109840705010707104600d0050360190b84e030b4403d11510503010040b40003d149061080340c0c951a00501000090048840031003030100700251040c40c015050102c0402603200d041880d03218030b502e00b0b0041021074205c4418200074907240d00c15803518011180a44541d621120403049d03d41543d5800c5d01d0380d0405807552245100701040000002c0b031214400c46c4980700700460340001e191000400c0300294015015134144003855000d500310040c2da03038488160104138100a5500d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 213510458 1250 213509208 213509221
    0x103061805060408090a08030a0f0f0c06020a0e040605010306062f070801051f081b040b040e06190905062d0901050f0a1104140604050409080c06090102040f030803 72
    0x100000c85000342039008810801003080000030190400c1d01041d2800e0413000d44400a655491081e0400c11020404080c1c03110403a070301c50b076101d589100c02450401d442465a80d83d60042e030308844083c4001c42d04650380040d240c1030600c20384000701070920702440f02c646400000340c0a14070350315140b031000300e0b001054001d11111241c1d46a440b01d000b400c44041c80e99a802301402003109464070030b450f19282c031200c140364514040301c1041d6180000600380703006180c4040642c01203070085103a0803584804001c03100340c0c1c6a1060044012104001d00b45915100b41d0f40d900c01c196848040031154501400c6601060740000c40c294005101c2c0c41664408200507410495841003049050042e01a0410071100d51419046035000d43da00d8181400703240c441181010603035a20216807010500b052004000025a0705225440640042d122034a81601ca201190603698003038400d54a1480001d2460079080013041703800e40c00840e031002141072a00b0611243c901e00f0140c0710180c800351004c8086800e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 213511708 1250 213510458 213510491
    0xc2304021309021305030a03050a0e030601060e06070c0e07050d050a0908070209100e0a0903020d080702100c1107091e06150f051603021e011521050102040b090f0414010306 76
    0x6085d0040c210f540540030351400804650100e00f01c0000240c45001d0f0751694180001c02905a0b0b182d81ca5082c00c1422507c14410035801c00142901c402d50742d001d0000710743d01e11444081c0107600769030b2901d6948039007500290503140041d00c41c021484c50110b08001090340b080660780d601c0c0e030403656805252a003400302c981c4681150003031000c401d400004d0044151035944405917a81c0301ea025078a11000c04c50b015210000102c4070070025030030071061155040607a0340000100859420007000910942c40c90f1880c0c50403d401000c1c445565003c091310541d219a010003a015003910140456405e00320381d60309103901c40d290a070510a501c001000344c14013440944032040c00058150485a066007402075480c405107403d4107014260543c01d15052106020f03030362810005000300c41c03d00d403400f607210900b25001d84e0602400303280340708540b00082e02030009000400b290021540c540240c5800c000918103c071010714400c42c505060310b6159119a81c400d41180d8100300c00007803103c84a140c864 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 213512958 1250 213511708 213511747
    0xb070212070b0406030f060824071106010305010914030c07050405060f18011401030b010c0210021e060105210c0904020609060703090e060a050117070c0c230402130902 74
    0x4180d0011030f0104803541d02d0f501100c81181010700a201c01d40e560b8808a8640d42c04c2864002e0340900e8200a03e91000070045164001117a45401101c0c01c45a203071080c00c01c4001e0b08100e42c00d946030b1480109020314481340c0201c0214600c003a628094144000c0e40d5600107074403072140501d4680002907425650300418414411029122004202083d040c809001109002e840046490031492203029403280c4240e04001d4030684403121400103076000c002002d840351681c07508510944a0003400c1050f5020400700c1c09101700002c05a5504210810a0203c101c695030302c03034210900264440d01000107940c1c40d0748081131714038800075203035800400c0311481a40e080f07540042001910104050384203401d00202c444070740d00c070485030303c444013002084442e51085038001843c550041100c00c030810324280d0000d10504144401840e03d58460030f0002c0103074400040c800c5100703010003503070351000301131030048d07200304ca0452501c007003038003142d800650300d028104c54158042000c180b002841d00c03116 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 213514208 1250 213512958 213512969
    0x6080112030815060301060314010b09130f0e0a050d030c02030304150e010b060c0c010801092f0702090a1a0102012a050705030c0601030c1e051005070f0309060f05040b07021207 78
    0x2585d650784070f003c050301030041d9800c80000c2814480000403240c0087c0151051a900105203141401280c25840301600047c007102211a0355621070041300b850422080c5012842140070704040f40c43c0c090041c08030703030354400d06a0a42d0010020000000d0081c00c0202a01140d40000034669011216040c0181400d403851074100300c000074404414040060f05102e540400d031303103000307139070303072500d07880d00940e00340300c00c00c1c04070414034291220a92021004691a8001d2034201030801c3e595400040040006480620299076145605180807414400303101c05504280020311001007c00031210151814190502e00211580b4164401d54441c01c11036204c0c0e03800c6411070351661503002c60a9103640f801c3c4021034007004802d0f0006216a035801c086074001500e65020083e1030701c0c0400340708002001c10140030802c00200010b500144144a840306880c2c000e0b90b5283d011410a100985401001c88884040c17004c03c4c0004c000c000c5014049544550341a1030211280b2010703110b8910f45030342500320303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 213515458 1250 213514208 213514219
    0x2427030a051c030e0c010c02060d0516110604020102070512030d110c0d0c05070b09041407110610261c020303090d0e0d020f061306051306080112030815 67
    0x380061160010b0982d680351140061942003a40c046800c1e422603501221105145e0880322180b4295030040320302d03007041c6002604e414502845500d10b07000b10781045520b22458042c0009850030594804105072013180400003c080301d0419400103580c80f01c1c0741c03050070b2081c4d0103243c801402c1c400500c140ca84c00562002c1c00d00c40310300c1440e45000d20340c000742c02403c1248610f45c07a4240540c86003034000140e0750060098081e0a0621401c240c3c03591003840150382141d00c1301c0321610031101e5072034103500c0350300760750b0300c0500203070100580a041c02c40107002d81440c0640010203000752030098081c1c50403282c00c060f075090a01828a8802c0c10030352460049018540907076004000160044015071090140c101a2913410700c200e801510722a48400c0301503001400d4001d20401414001014031246034014451404c098501c2d903100035103545c0d40c11541c0040c0011426001a00c110031070400602401e080c25100c0d5810b00030300a844a0b165080074040010800c04502d220340018854420740320042d00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 213516708 1250 213515458 213515473
    0x1c0c0b07050c0d0903020312090a090b012102120a06080d08040203250303090501080c09040c0201110a030c030605091b2113030206090c0a1710050a0605242703 70
    0x50191803022244005d03400390292344005074080c00420102c03901380b02d0013042c00c4449800d01c0c00d814003c110030506981408244281c04024018541508040c2c0c00f42100c05030340c0e5102500342141040028000030b901d541860003d210000e800704e17207580c420000d032501044d941c0d29800001c2c5002d883e101c21000c10180c8090001402c04403040310001d40303020b516290012962800110341a034021a01d103045040c05011603009454280c020b810004101e200100b0040c3d059161010654800e03201a40460783e54840b81c130660341c040c0a100004e03e0100c3c2c80b4200d62501120341000d18000485c980c010050004905c0c5030441c112111040c03c28551412110b2032a00f081c240d18030019240c0b090b00036200300c400082d84114005804200c0e20f40241c2003140c1c0c0d0389001440d0060f02041e0000b6100c6009000204110350716500c640c92292810175400300c1c40f285800240502d80c1e040408507007178004028400741003204030004550044512a2a1403092400c03610840260025002c402d41d05004110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 213517958 1250 213516708 213516733
    0x44b0c0b0a0813111215190b0102070302060706090c090f0504061b0207060f0306080303130204060605040308090616020d150c030606021207030504050907050c1c0c0b07050c 76
    0xc0207050111410b4603950b04907111140c0310a200a40c488005016604031465055036091418001078203c02c030340d0403146a184840d01d02c10107548120390aa03080990040240c0c01c010050290030711100085c0041c02c0340a00307540204105204110300504201e44422285003042401e241c03c00c01400c0d540800c011002c1c036107401c4d0014020036203017501d1950030300d8160411011a02061034903210b9540092412071324115007070b41c1d00d0031001c00100506958410009000d03000340002c601c52456102d034002502c07103a1040000320749968000350200300c400d11007480001c0e446001c45030242401c403030450f250b9090004501c1469102480250401e50601d03a4104203c400046000c96414000061103080080007013102160418071038500140c0c4611040d07000100320000400040380030780b4246103001c1c0c8600109641000a0303584c400011800244442104070500c040b9102ca00c01110304603c0c4441c441c0010155030741d029000d4440e00705080491540d501480884948204400a0715547c110a8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 213519208 1250 213517958 213517979
    0x7020f1c2c130203070909021801120b0a080a1e170306130926091008090109060c0f0816050301061b0c0902070c0e0402030d082a03044b0c 61
    0xd030303400c4c5e0200703031210004140303100c40f80240e0f0922051807030000c0003601481c0044075410640144503a01c6540c800120540c0e4031591096005041c1281c01440800250b01c2d110001d4020b07420000c403000003001403000014200d1405200003003440e81e846031a030322000300141c4a50040006840118a010208020084450100f90452035029a080c1041e1201c400f581418030914060562150768810101c0100380202d10203a0040d2080303000280c002c2c06070395080c0480f02911100400300e01603103002c018240d8413841982d13100588404085c0842115407019101c0d00040c01204140080018184001d41803424114100b60704851010042595a1684c500a600c10700381034442e44400200401c40b4042a038001e4059a809001400d4640010104607103810f406040003c00b8250340e401c80400c01055000c502c18100c0705895107507a41424581801c075110305400004170501e00100b010101c000c0300002071000403203445411035848450100c484525642c0b2401468071000d1000402d071a00c14 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 213520458 1250 213519208 213519211
    0xb2d061b060a060303120c170c030402090c07020f130f0609060609092322060c0e0f0109061d060403060603060e06190c09090507020f1c2c130203 64
    0x18035003526815101c0028501c240c554a000150205114422030400d80c0d619078007040005a607480e2405460310350000105040000790b6246000c2d440100a000551510400300342e0800c9440850030300c0c0505983c082040c080d24404800c0c4285e100803801d00c014800c3c0c0d001741c112210084820440192140ca4402c0100801e00829000400915000c1008a980d12926100e41080120a021210150b41c0e001d40c15a005042c20564010301c10010407040f120300f22002010f226100100307008104400090210052086192086010610411859800040440c01e480c0f05181032840e0148103500001d060507000155030700594002000030511138039074000c205480c0300c2d8109000c503080041000c1d41d0b6410948131074100414521041010706559480221000c60a00f00b040105079150012021144229107000168000040e00d006075041881900503e80410300c61074119413035010b00030320304003c0d00444180300c016001c0c1440c003450400004001c10000074910b4040201040c05100079420 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 213521708 1250 213520458 213520507
    0x30f0e07140406060503060f01090e04080a08160806131803020a0605070306180b190314150c1210030f0804060e06160204180602190e040b2d06 63
    0x80030030314940940740c980103d800b100c45a07074401d810f6031928010080390701c201e071b04ca80d4140810386c24001044260761703c40501c03d0b400341c005075071188500107010302001030003080600e010003061802c078141600061415002a4180c500785841a071400c0004001c01480e03080c42c1c0001c0e028101d0004060380000d4900d80207203d604240455100d2000c1501030301c000740181c072800024072811070b1030b48245601c00194640f00800119240f8500a0265025092501b059941004d5011a900b5003c002c10200b9652943e020980c40d140c0f4008846e0081406100c0c907034603000386044080b50449800c0641d500c040c58110116142c032002e10319007100141e016100303c0380821501103d1180e035241800c1a20041c1203000d20340000a50140d08120017405000342d000c0700c0240003c140e002141c01c41c80034003022008040102d0340706540000150980300034401032807180d801d0030314006840d1500800c10495250002060055002ca00d540d03403503a640b001c10b41d42d04108040340380e982071205d040080080d800b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 213522958 1250 213521708 213521729
    0x50310082d0304030222150e070216030803012303010f0c08070c050705010309210e131e0509030d0e0606150a080118090804120c060804050a080307030f0e07 69
    0x414209002d032640694480658031464200d05030001081d004940700080030501d50004200f011030710100840b58164011142841d544010080f500307404005c101c80f09040a50320810175450b680d81c000240c07005026074005e0041c00a0048c051141c802c0990700800c40090091000c410103180700f4000f40891141c00b800611203c000c5100b842c080c00d11011000e8201d8094010306050174010b4001d45a112811070f801c140420040d030b50920f649410314012406642d800300360040f10303800c20020700b091034900c1c41140d140034a40c2000b80010403034811140401580480d8a90b10305000600b9070141001d080d00b207504000a400c08030402103050b03031044808a0ba90942111800c40c1101c26018a01030000032483c1c0c200103128220b4884907400c088140708070081980c100a07940d500795900154013024100d200e20101404224110004e140030305030340c2c64104c4403450302d40c4078a0780d0b480d0100b4016141c400300101103006588070340c0100c0180c0c8500e0505205e812110150103586101901c19024040e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 213524208 1250 213522958 213523033
    0xf070509040e01140a0b0909030304080f0403140d0807050c100c030603120909050106170f15130e0114071d01092102040b1c0b18060115030f060b070305031008 70
    0x80c47d001c41c0f0140100f608200440c25540c81d40c1e100b080326845060445203061051100000060805441002c0c41900c14058801e040340900050074170400a4018003d109040c40601600c00000035100c103074000d03080e00441c0241114030140e000701142d170405420560f100c03860580c10380c0c11066103422604100403c00031682c2e9071004540c1c24032140c1e00c004010004202013907080d4180c020365500820400152540484408001411000c8501759004090f42b81d1501d006880070a218004030702640540c0d010303e07450034a20003040410440440c07580802110388a4142d64400c9010001411440780312400b048034a400b65941c15542c3c050880c03059007410282c01c3e09003444070781d0034100341c1b00940131285502c55940c2c91481050083c4044541c004c504480c00440000300706003030007860350504107a1151100e090003015201030881c070750301550428100704400c131804011248181d03014a401c170b48a440b403c1d404031244a40e0b03481000c0c10302c504a0310724154510820f0345940400d9510300074004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 213525458 1250 213524208 213524231
    0x7020304031104200304020f03030309010f0501090614120709020d0b090a0605090c0702010c0203030327070503030301031502130306020a02070e010b0301090513050a0f020a0b030f070509040e01140a 87
    0x9882125180b529411407607801300c500d2121200c003840e0081d200030180c0001350b005d400440d24580003140d140c1110703919003120038210302d52446450302506010005011890401c208840d1040302c6e81d000b00c0c000d108a0b81c0030100c0c4201400b101d4098039081000390350303c1056081c888003030081b0001a034030408034040890824540e9100d02c1c012a07002034006a02a0303144050030303d041d08002000d07414007150350b102d000160b40610040d07104103003001000440c0c60100d80030240312401c0c030221541d9940b02c07240a10495030000243c0741102d40c000c2d03800040121011042d8068060742081020071620302e0404802c101280d0094241c460b11a401c036210141e8410342c01000307a0003841076125012003040140603200003500107a90211555181801070255036a405203003a0350420141d50721000d100b104411441c0034020100200a1445103504500300120b1542030514041c1840c0d05204d40002e821a240e221908580d0051051000030801a5407000c080002014201c800f07a0b002460700007070750407 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 213526708 1250 213525458 213525461
    0x20117070e0f01020304050303070819021506061803100903030b0a03020604170a0212010507080a020307020607030c0e0a0306020309010b0114040317070c120b06030d0e150f0307020304031104 84
    0x424031055032080c980074250340511a0710003a141207181140400c00010406840800c01403164030b1144c1d81e80c42d503605001501500780c2c808a01c603102150081e08007800040619002c103600000119841c503911114108042880b08141d0b20040d0540918107141c400b4650582c881e0380c1c0700c2d0090b2030500202c900c060800c11a4912400000d501410032300040c0038006c00030301c2c80615582003030101d80040398681c0005200e010071a1103030089079183d0003040400c42e40081690b4008103101019070650806110280d110640285803c003010350360440c25000034890060094208800703460b41c411580c0ba420080040d5108841801156007000000300a41d40b0801e248003000041909041c1400c3c1950f594041040010401650181c0b06008020100307855005c07000040c00150034480c1c00e990707945400040001c00402c0030b440b903001420350b00d20f49030301b01108212001c0100d0b82405171a030030503140400750150700d80480c10094048100002d05170004018070950707000b41059840c0035214401c200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 213527958 1250 213526708 213526711
    0xe0c1c1a04052206050a02090a03080403030e1503180a060216060e030909070f030e0d080405060f15010309080705030d061e1805060301021204050601090e120f03060a080d0c020117 79
    0x3c4602040700306050105200f98420f540107501d40c8000342c50441104001010390714290003d0f210500001000c004054201d00d83c001e945234150b84018007101c082d0480d41150000030032040c280501910343c000200014840c410744641e100394119103602e400504203d402c0e018400844000e8940340c040c6099990000540b40340490060039200c8503036592000300d0700080c0028403507050588888040c861142d0901c56204540c4950b99524442c0c6003a0410314500380c80900305503a41070030302c0b05003d840884040684040342c1300313007808034054640c0c0c80c102640c2d2007000f001500700d000c00316001030044005d401440494284a11203020b030300c50010320040c14a4541b00e610315070900b040000302041c605030070107a4850f500400050418040390301c619503041c01110101d0707160308010018070420403184940300074058240d000b44201e203603001c8821500e108800003c540128080001903150b45c03131150740405030002006813180103030302c9100a0301d014400c01c000c03030108031580c0c4090162100001d0a5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 213529208 1250 213527958 213528001
    0x50102030715021b1009150e0a03030c05070827090712090812040302011b05040e011e03021203090117070e0d0201090902160c060503010e0c1c1a0405 66
    0x44401c10644404800a5100c81c5412169144009200c071484d40140840210141e0700900413845031240c1c0340008210541c900003502451800d001070849040004052840c5d9070f07d42400142c002c424201502d040c01108401000400c2c00140003505001500c071802d456255806c035207075517400039810858a40011111500002d100303a1924888106030780201620300c0c0203000481c80e19951030440f0000b01c40c110340a60140c0e4680c0c0c10707481c88901e454000c06610009240c018206802c3c50000900f290041c803035082c8800710b00074180e00c05003589030501e00441e4028807e64011142c106000d49a8100282c0f0502199900300914800945040070602c281e00a940d0380200300d4010041041c0c11807415816030400403011004a11110180300070700c4440c407024491803c01902c1d1808000a13035858000e00c0c10040140010800d4044100b00f10307402000c0100c0c0d094607652a603581800454041c21034080e021b007441c0361600f00e030b00707408260501d091080c0c8052100d5a610312049440d01c0140700c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 213530458 1250 213529208 213529223
    0x5031e060903090d080d0615030c0215011805090c060c0a030905010c17070f1b0329070507060b1008060f030120090a05040e070503060f010605040506160b0408130501020307 76
    0x106000500b1200081000303080c40c6c000040c1c0c0c151075003580e1800c803528448104c0481c1c0d8036603006030800c2d010003403408450040e5480e8002507040c004070038044400711400d030022503103900100d80d03001024841242cad10390018100540b1107851041056440581000039400b0070b05214000c83d503540320312a11180705030440c07803850f07001c000380046600035808890140e0f941120000701c00002400d050300180c40d0420801d09045040c11410f1500c8504121041c503524441a4001207080d1041480c1081c0d03c10414280f50351074005908000002d01152013405501503042290ba8245540200300c0c0d6004440548401c4196907000c824103080b10603a81195a00c0740300404030030f03c510407480c002c3c81d000d00084c1075090f00a5a4201140580b403d48500d982160000e05c001c1c0203a0604104c071541c07203900001c82000951410304060298411400303000e0040c07500144808074603c2454031030070700b950301c101c540d9880e140509142e9a941c104080b11620320980300c50016996100001741c0b8295130f00002da = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 213531708 1250 213530458 213530479
    0x40503151905150109170c150d060308040f090209090105040b060f0f0703030e0303010e130609140106080c0d0209010513090f0501140601080c0d05040c05031e06090309 74
    0x340030300c400c04010009481c0101d1103a940c4100842030250074020809100c010040603c0480090f108150350f80000303142c084e0b07801d00b0b40010000041c1c0041e417003c00b80c070012558034182c1072000e054440d030a20386a80303906080f800020440484002c0007215440507000e00305d0391b1600303e10001e134400c61480a62101d0150014015071034503901c000415000100441e203003002c11011380f80150402010804105c2000c180704081c50382501030300c0814000c0a01551640d0306210a104040708050b0441c00409885010701c4104901940030316680f40d000510034130100c8189641e41c4c082c2086000e20b04080c042c0c00c51081c20b03400c040865900207640206078000580c00d1005000c14800c0140f40920190788488140f0f020030244004168064007500001c6045800300790140048080a012207041045038810030501301002d20503134400d00c1c4000c0380072803180c40e5401d000300f641090342c0000d64103000f042c0108014400006c02c401c4040c0040056501594981c13001c10348034040d0012242d0880c40103003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 213532958 1250 213531708 213531733
    0x251101050c1e0313090516050c3004150f09060504050108100e07080f0f0f0a05270304051908190f080d02120604050402031c090e0c04030c0605040503 66
    0x941250705031142604507403c080d103202d50074410505a5000c980e4060742e40082c442c00c24a0640c107640048080d051541c50300d101586002e1703440b400448802c07600ac0c0c152640c6120315854050b140e14005001c00c070103403580e446004140b181c04103e40300d00c3c041071a00c2c14416100740900c8095046800c540c44031030409103490010b60b040c0f00b0013480340c07030040c0d050600455a004640c18440c006d045030354035a4502d19200070320701d6000001800e00b2900180303d00c104604010070341041c1e584910700c818041800d4450401c41d04003000f031300c114030305414142805907000142c0007002d4030454000b00c440d001244c000a402c882a12a140602442c6801c8401e41800d005400c00d05481001c0c401d020022404043e40c445406940004240703446c20740c0c0000d40e1030f0320800030852807034110404680c1040103051580c0041d0341e55004008040b0030080001c10750704018050b020b103100030300402010004924042d43c6804c0d1581c05400104c0358610b888502003582441a0300391010b070f54014000b030030743c1400d81 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 213534208 1250 213532958 213532993
    0x3041202030313030b01181503081809070503090c0d020f0108040302070e07030504020406140f01030e0102121e090d05070201052809080f01110403060b0105251101050c 74
    0x442099030144000c0180f840c0c08038101c05610001d60103545900e180c1c4d414400c02d07440d010700d13031900401034508181d80340138540d030001014400c481e44030081560791021540308000554002e003145034400c000300f0403c08100e4109000354850550081501d02c0d0100d00307030420005400041002c0d4001007400d03050300e02940111103040e0840d019004031031846a5400d1408200c0c3d400f2101000001c0e211024401141800d01070000580b040318000c41c0445034501c00300b0803e0b91014000360404da16104000303240c407400e50498140201100e0380052a1603c100210b4401c88503800e28404030b43c440000603c40000801c5803613030303400b081c0e40d01c41c90715031542c00468143d004070340841030300c1440706000b4440707081c0c030b902e000c40c1c400711034440352a03062034659441d08210040640f01000c0c0d041c400012082d1144404460a895114000141e45207041c0300480301030040c1201c00c0300720b03905803100da80f05c2c0e070700c03101607040e41481000c040d5120050301004560900030200c40c250b55a019241c079205180aa = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 213535458 1250 213534208 213534239
    0x5060c01050712060e0a0225030c031b11010324030f14031603050f04051819060803160f0605271911010201090b070f0e040207050309150f040f080f010c020304 70
    0x110110041c441d54280d28031232002000b40c012404544544103000c10950054180312100c9100300000f01c2e00c64541d21603210003d40010304d43e040540d1896181c0b10449560f5640c05800b5402e005596101c1e22881d00302a1600116015601d0807030b141c5d404407900ea0000b0440305180004000d8002c0d0303002035682600d194000d66100c0c110550306000110b010307181d1042c03800503c602c07410350036098202482d840f400303d1904203150701300310b0070b05c5002c0c07020320b00000032a03101c101440b40d00607000c0400c0c2005941c3e0b089101000f0086414031042c014074400320701c103075a8804241e504800c49107001c441c600740d640c070800c1d060f8008143e1134601040800c0e00c110380080055810b000129500d84a030303507400440c0608680190200740d0141030b4401072588400c082c894040f007540d08620300300c6541c9a003a03070783c094440c0e80c40c031880c092070207059194403030b40c10f40b144980340154454440b52501d803041c001c05800d010712440d1740b19010000140840500800310482069009140341504080501c54001407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 213536708 1250 213535458 213535477
    0xc18140114041d01061107080d1809180528031101090c0312270905040c0b04230f010e090903070f140607020304030c0e1005060c01050712060e0a02 65
    0xd0074000090310f40d0785034102d03144000d43c1d60010f0400b9810700030040d00210b44040c2d10302035a4080d92044c0418180000c5056100d121070070180640710040138812440300c010380006c0c05c41e5040c9054505511300300e102c440000c40c460070030340c1c40215180504000044036526008102e4426002d02c90106c0d002c0c40f41c18152500a00003c1041e80c6203842d01d1408101c5580201e8610390ba52090b807103811351104c03500ea00303000030b0014002d81030300700c1c80c0e0303c0b0410989008440406170f980001c28100400560004020700d1120001500c840e035841400314410005007500d204400c454100c61401c0c40c005a442d02001e005840d0707040401c00351000c0c003070001c00041400d40d15200402402c0e0101e0454044403403058441c03e4524880c8009001043c102500940350400f5580140014000110b500141c4030075501d650744441801d955524804e0a0080c041d4441c031340010f80002c111400035010740004c3d10030300302c42d2141e608a01c1c00c18407a808984280c400c52100300c40d8030001c00c0111440741c005000908 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 213537958 1250 213536708 213536747
    0x91e0b07060b030a030207031514041104290414071b060605150304051c0c120e09091b06090102100b040213080708060603030304030903030305090a05030c010c181401 73
    0x2c40c1503003c240b81401c09030081e80503074440030040003088010070142504996108080c8103026103002c14440120001d4002441c0c070f800c145121100b82c9455000d0100c100400c490300c406481520304c550342203411310301407d01031410b1841ca411442c84024040f40501641d50798400082000d82565503145122002196100e0310342500196030780d50100e580480080d0840d44035600e080602d01b0758504204901c4450050310700000c003001c080d4000000031341040c0c21401d0700d28483e800b8001200d031000c56200c1142e102102c0818041d58100001d080c902d0440540ba60100d0789817000d041041070b01454000d180140d00002140280100c0c0b0740003d541014013030005810410784001444140c00240c20030045580700c0e520411142170100700316a0401e03400e40207149141450744000b040c44490303000140c02d05885001281985d542001241c2e89550031606482e200d20540c0000ba02900c1d400144000182c40020b10403800c000142c60b4100b11b800c492034080d40d0590144c01501c01d5006074041c4002c85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 213539208 1250 213537958 213537971
    0x615090606090111100c2307080706021204110f19230405010321080601050f0906090d120e060903062e060302040f090e0d1b020d05060403091e0b0706 66
    0x10303041002c1505c90172842008a4091420200180240104600b07038051003240d00d039510120410000322038200e83c1050704950b035400a0309040003c1d104030a80350000f008010b00300300c2448494048a00120300c11120204c02c08201d0040010b5000885890325180070592020466103101c1001200d00840c2c003c002c0864203003420001d01121401d82c41074840141608250300304084e015a980f02c0c80c00103040c506114200f034000240b003805508040107120400082d2038401e5981d10082c5c40e43d14030000d0802001111500e084a004045c3c1d82030030000c41c0070003000d8034a526003402507a1048030701900410236592109842c0c40181505080e80c108160640101102800190302c2c01c0b010b410580c40250780e13075280c015400b1103542140c2c09208600c2c94103130b416089007000300b1074417510507840c6024401000d1764001116a0300c40201c000307500102400c4030904002d404600d0a10681c001c0d110440206e0740c403028140ca10030100c1c0c00f50b0280740c5150060150140500c0a00001d0b8060035000441 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 213540458 1250 213539208 213539237
    0xa02090a0503160306110c0319050d18060b0102030403050c0d06090c030615090207030c020103050601030f1d0609010c080109110702150d0f0b030c0d080d05010e0906150906060901 79
    0x500d8180410105039610007072003030041c0001030140c2e41034946d26408807454510841d10b01501ca0180001800c0080c0d03009280700c102c86d110388199442c50303001402c2003103c2101d07003c40011142c41c03008112166030902c1000111580044240e9086980003000340003145151010000d03034405102085030196510042c4101041e000783c684009580702e03400000da8181c0c00e01101a00040c40c0d8007690200740100440000681d1103e2540743d002c0e07080c20701054035111180113030040c2000c6a500000246480042807020082280101d2440d9212050b41d2590311a01c0055080e0b0f0300c10115000420409001000324440c0c941c080300b0304c2c0d200c2411450500300141d00151040206150152000c80e000c54401450200c0c3d1140c071180a4100c14100030714030140b0040398507400903040c6680300b204803006900c217005080c0121802003030301d410100101d685a0200e900fa503c8280ca80c43c01e244a0030000400384500303125031100540008040b4291544c51a00700301181d880344d032205042115582c1640791 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 213541708 1250 213540458 213540463
    0xb03030d050c0304030905240c12030c040f050402040f0b0703020307150902040b0f10051305060a091d13080a020c1002011a0306040c0611030c060f0114030309090a02090a0503 77
    0x640c5810a050f03a40d040034200140a50056040b080c0301c0c2c2c08121b28010450384002c007030b00000724460100c946600c004140e16050010714441c588442c280042001400c100ca40000c1003030b15803200741c10320116210000d2100320b000d9400342060004401c2c205200d440e0079031000d001e500c0c0c8a881101e00c2c1c056507941d01010f00c2c800c048441007040d21007585c0d20441c07920b030080014500701550340707410345803800c1d0009007800040e45101c400d2000c0002d00086015001c030801300a020003400c296962103241000a000f01c005200c4c00050b40c1c082072b5084103104a040c01c150051181581c440d142d490700c0e4680788059817203900a842944120303800c0700002e848850040d4449000d540000404138442c1c00c00207565046819020300c2030f04030108010016400e480d8680c140d50b15481c0020020309400b001038614810301c81c41c0030183c82107a04001c10f5501c0c1b00746040c16245445180464100c41c0020306d6070f00c1c02020760680e8080c000034001100072049078007030301e03142c94010001001030b9a80d102090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 213542958 1250 213541708 213541711
    0x50906131403070b1006030c0e010503060120060a050903040b0708090f1903020a090b0315090a2a0501090305060f150a081e030301060c0305070524091005010f05040b03030d05 77
    0x3c401c1d1036803508010344401d0208452004081c3c609040c000c034802c82030020702707401c0c06d00c00381c6052010220100d07105911484000c201c84170101802d24520520019803607840c541202e407904481c0c24000080c105220100a503411154041400c82c1480003550b601c2c0040d8016540460300720003040d030200000d60303401d11118800003440f4801c0b0303007050640c010b0180c84075881c1c203c00c40a80c07d0151248540c0c5001603030b0300e14400c0202c9104001d4980c0803080c6e0802c0c9010720040c01c80388a844c40012200e21401c2a0801c20300c2c58040004c92030350350301c01510582d009200141c1282c200200092484600701d241d19480458022080c00700742096002609800164102001c154030200144c0f05111141004102003030747c28004608543c544000240324039000d0400504011010410900700502044500742100580c55040c040510014034000754a0f011550940c142c400c0619400721900184600c3d8181c43c00c49501d080c1c0d141c2404180700140442c02c0310280c00d4402046140d01c43d100301e10905 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 213544208 1250 213542958 213542963
    0x2071502070807050708120d1802030a0c08160303080106110705040c110c062a03071203050906100e16020f0307030906080f070c020409030e040606091805090613140307 74
    0x10b98941a071401e20390f00d0304205070803078401a4083d030f1100241a141c1000d9480d0b4000c12400801c2d80040d413128040c8000341c02000a4040c8a44483c4c5d0080000240c44201a50a034408a5000c0c01c2e40b0700d5090904100307444050040380381e0750700600413188a425501aa010180201e90900ba6218041011244504140c070002081014a04240881408610075410b02212140e061050302c526600040322040340490402d5001c141080320407500703106840b5050740094000b91146039007c1c0c0540680421690031201e0701032900065030030b100640004080e10032041920500359541c011115441100141c0c50080d4800c0843d0700008403410030082103a2842075440f441c585117858030280540f200a002b10144a10481c100505a5801080d00d490603404407000320700d0000500b42545c4403207910032556042402c180009c50442d0708220904200d50a20740c0366240105030030340c40000c44206462001158108074049040f0020344c10b100c1e460240201082960705500c41e01c1545580c0c080c4070304 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 213545458 1250 213544208 213544223
    0x1e0a0b0a0e03030301080c1903081204060e0303090c0415050607051c0f0c030807030e0319020c010f0206010b131d0103020a0906050f011110020f0c01051510030207150207 75
    0x949481a4800450a54241d080d0300840c2554104000152607680c0c3c00d10442c080c40310324801204540010f07420074011600a50103580d585501010748181444c12903080e2140f6040021040380800d000040702d100d03001071805054508042020000034046640c074502ca426928000441c0e59540c0100134040d1078032030801400f16186100c1001e020900c44820390003480b54042c0e203100700720b0304100500e9280ea41032419503220740d14031000341c00400072210b01c007101d8400801c2c072000c2641e41c0603451400c04100d4003200c3e840300d6803074011142800107502d81c0c00103800400042043c0d04610b00070b0090f403003014060100c1d01d030b1105440a40ca0000484440d0320440c0000100254201021014007500c09850244200ea0800d804038604483d6110450b04101610070b4002d03ea89041c490604511513001080d503546c0080302c0b0081141c0c00c0340c0070b011410352810000c90100d04146e404141c0d000c401418411031031031035440540c0250002c800030340b135081900000036050804c034401000d030940b10720748 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 213546708 1250 213545458 213545467
    0x30b03100207051615030b04150816090501050a0b1e0703020d080903070804050d0f020907030f1104080606091509010608071d060f090f040609091b12021e0a0b 70
    0x100b01e0f140c140440701c854104d29102d0350600925100500c030b40030895035828042180151400810000c0100c448200990380c004034000c611400e020855040380d180b4a540c0d105001c1c4c030707111100220b035006c1c031070b05a1000107039104000b01d60340305000c0c06040340304110340b11a405d0000d81e07046180d4000c1d0000ca005070002001d030018650811200b64200e000300004504150141c0c0d60b20140f480380f4090544200d6080c1903903010410f03028800802264090401c5541c0e0501d68005006840d0b00410040b1440c00c010f100303482000c41c50705560403200c903c801001c240d00d86000388442948054900d109500c1c042c910022140c848800f00c0c0d000b007640d0340e05c07004241781c5588010062051004071803041c0700402904c0c2219903580043d00e80d2111620103850703641c003200c000520342d00d104d41105500141000c2d000900a08254000350440d405a40090381400507518041491100c5000d030f101040c48580043d00941400105420030070210aa03800c82c0d4104071000075052255588400b00020300040c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 213547958 1250 213546708 213546713
    0x20909010b12060d1103010626150109020307050705033714210901022d03010b090a0b0d0b24040312031415100e0108060907030b03100207 61
    0x268034010410504058140903201028040c460000b400d10361061101d11015030520640ca62044685000140204004c550741c480501e0b0b2000800c404850054420300c8074460550041018400e028a10342c0d2045541e007880c031140001d400252100c8100030f820700a030b1f00007840030030003092801002c2c41c80028031000080803c0440052060a960005da80400240c485030000078000c1300e2a103950841c1d8440c18001000c0076081170ba90700803200220307160b080c00300e204010b4ac01442e0140f24a1034481c2031381980000500d0503000d00e00c200c0480e100400c010001c11004030042c01c20064000c00c51a0301c256102d40d20069a0030000d007518409035510b4094800385003134220070792120711013071000e51888280b1404800c0344c061844040d1802100e070554003400d80c880c0d0711614102140c400101600e05003400141009841b01c450303580140c0745203108800342c900130b120b9001c200754140c3d99149241e48840074442015009002101855101d0001c0d030000c3e0350070311101da0510408440180c4070502c1c0e0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 213549208 1250 213547958 213547969
    0x4120c0302090c09130c03020c160e060d0c09180f050102031e060307090902040e0d0c0317060607231f1109030a0b100e010f0623041404020904020d0209 67
    0x42e00f041609001003100285903114440c091350302d4402c540300010003460024054010b4441d610031034401e4004c1951603c80c2c80c8031401f1030307030070b54200b100c031605656941d0040c003d14680384000075000c01c1c8103c00401a07100f41d84c00c00105443c04c1c2c0400b4504413516505c52050002d000011600c69402104001d004801d402c0200018034141e070840340581484400f003502c6040a000d501035054880701c060080d9200c5400ca9070301d5040c4a4102c44030202000707801028111139120480020301128001e42e0020b07000d440036030003000003c00c1039280491503902c0c00a8075401c1041d0440240c40020f5a0711030070024007840e0461000c00c0c2c00f0040a413204060142180c003544a1743c500001d003400920f0035030328000b45c0d501c003244e8801c0d02c8419903280c024a41e40040360b141d1000c1a80b554035400400c1c010314441000c0b0455401ea02c840c510280c001b511104040f03010320442d4880b1100340310401c0340084c000100256140050801441c0c148440c010400b44d030310447d40f01042a40020f180119410035 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 213550458 1250 213549208 213549211
    0x10090b010e1308030606090406050a06051903050f060d031701060e0114041a16050304060228020f04020307050d02220501021209040507030b0d050c010906090803070803070504120c030209 82
    0x40800d0b85034181961101494000545031078004d840c041281e100544480d400751001d004000c0a42d01c0459660800501d540d020901c000106000e6510128684e8024001c0e540030f21802d958507025039466200b80030824400002c240c040004601c06441012147d0b1280d44c060142681d40280d51002100058814030f0300c040250170840e0100400c001c1d5004090b4042d0002940034207080c0da0b0101e00080710040b02c2078103000390050100040c0000c1464001941111054080751117252030b6030f440122101e04060313500084e4204003a03440c0f0107058a441c2d80155400341250074034a003440d4980140c14100d80005451901e080d00410074105a03021041026004010910050024800760844400c90b0302541ca29107025948842c046241240070381c12072410100090071400f408851402c00c0c40e07440d191a000716000c01d030380c0440403480c24030891a500650792014010f501c0c024403503075000050341c00107124404002c0c2c244404101c5154580650050340e00658a000c0220705500402149200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 213551708 1250 213550458 213550471
    0xd050708010b0a14030c0f0a08010617011206110d06060c062a0c02060f0703050702090a0203010825081c110a17030604090c090c1d0a031410090b010e 66
    0x24140200b02000c0e0b44900391100344e01d01c0e2000c0d1130b00c90b25440008800e038000c24204049001004c40c1c81a00d0b694000071303150417a845580c1e0009103002c1e90310f1100c0d201e82c0078040c400c60032500007841c80c0460b00340e80000c0c502c070032207020042c940f9482ca507400c4201d40080e00111b000500464451051042e075018181500540485010001522005031140080c1c903903444424072000312042d00541d40c0c4c103420703102545807121885a45100c68034004041c0e03803150100303c0c070501744000840c0340e080c2144280c070305a918000040424010540c2c03103e8094004842681c2d50801004010074030310000e1183c00c8007520036100750100110700490140400440e48002c0041e07a01c200044008581c0c61502111400366034001295680c440c14041005003458400190000d50340701d400013841d01c0036912120740c00c1060b1b5103207440c100d0500c0d261b4100610a40d0030b2503100c07038425020701c0407840e102c04158801c0d40c00b20407030317800d900105148001d9404000007a500c144207100100200030181040c0f550229 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 213552958 1250 213551708 213551729
    0x1e0c0f060a020306010c150f050c0403060c0e01020304050609030a12021e010c20011409070503070b07230f01111b0303061f020a0503071202010b0117070c1104020d05070801 76
    0x38013000001d00b804000d26001d44401180c0e450031a40c80c160358020f45100500d1541800286040302c00d4032043e500c0340c4021100300d07140145085249100c1d02052040d07010590244d480c140c0b0b06010403c2640101a00690500400c0d545000140020b10710303000410366a0080d000c4107042e500a61180000100c0c103008a0b41403482007c0010ba100c1d81c041d01a42e00941252070801c0c0b074100107030041024141c4804141d03445010f100ca43c06001481500301e0358105c00b1244d00c503844542d4000d180c055102d004050202090700303d000351204404276216000351104455a030108044000d094400000044039503140004030103031009080321042e011a5a100000e5180d4201800880c40c00d100c130302044068420031100c0d00784010310070310050b4084c5400074101d03501d07030515043c800d0440d500c581110b00598604081d00b04954000c0c5a01e41c1034140d0402441420355981e80e013501e2601c0c1c600002c440021014003011201d950ba80f0103042ca01060360740c0040c1c60318103030502402c1c120040c0c00404524 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 213554208 1250 213552958 213552961
    0x50c04030302060a11370201150b0c03070b010e01050907030207050a03270f180905030703080709030606030807050c06250f0206030f09100c05040b1e0c0f060a0203 72
    0x2a000500f060b000102501e002601d07000140c00d001c018092000c03c01c281c5054410302c102d00e205488035130203010712003481100148109042c10f038202d48403104000c0110302c403903030204204c80360440a42040000301d81502e140910940c0c0b04481303018240c01c84030356005101c00500040c142140712681c4052542002c52030654103807103840c0e4403600c4410050810501c003900760b552240b2040304002881c110190700c440d440e210305810700e50410601a001740f548407401841224030f07460181101490b04000510302e404e2407038a00316a020300c0200b1071400d00140d44000000200300f031185600642c0510b17030003034850000740b40090410396000c0c0c1e0a803055000388030f500031501190a06000000d4507440e480d0a040152900c000c100300740000181d80304001000708101d44403002816403242d43c6003801c1e11501001c3d0440b0b03508443d0750000200008800384400d108a03041c4000600420061001810840c0c046a1550f81950300c080e010581c0c54000b00c40d40e01b180a0704000032030b0490843c0c0021b5056 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 213555458 1250 213554208 213554213
    0x30307030c02061c050a090203060f07090501120e0607051908040b0112020d1403070c08070608010902030601032a0e01170402060714010c09030b0601030e060c0c15041203050c0403 79
    0x40c101c1282002e482000b0000703a494003903024014409400840c0304041c025442c002400e1401071550701c1040e070086c014000080c01d00040e4820291081c403444e2074090301c3c076080200468488200528225a0540d580060f80e42c0301e50401282d031149542e951038603030720301c20b6a001c0c00e55227100304604018059500103020004544c0d60040d81135440c01d00f00c048000715140001801c02d10b8000b4060840e244030000e2480caa44040010130005008449a004d01039442c0c0c0915511200d5100380400240281c0060003145803e80003190406c40501d004510170001d01010300c42c82e0003100c240901000c5003001007a0050304001242d00c5c0920034241704036000481100e1141031080200000d1181303100103048404c2003034081c58bd0401407040c8000b0003a000084801600988080c00140c52101e90742001a80a40c031a0007511001e1b0946809404d0f030b0f4071402562201500411180760b1140035105501440d03030380a0005900c110b000d480c082c000d1341e00480001c0d0446134043c0c04c5403068101000203001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 213556708 1250 213555458 213555467
    0x402180c0721090603150b1c150605030a0216020603090d0912020f10140f040602010f0b011205042604140a120b10030b0415050901020405010c260a081503030703 71
    0x891305941004242200b0141244104030140e03002894900000f01c5c0c4140303651902c405044d11904a40010850702d40c00b41501c10b0505118407134500050420800103131021100d80241a01152002c501a1810280e0f4001541d0b50801ca91045081d4084050440d03c6a80007450138001c00741c062580f4070ad8041d903000b00d810120702001c4ca5025440e0714041d000014071035043c0404a1800032a0f080d02c540882e10240265803252286034010b40c200300004031800ca83e44196504103c3c141c48a14003e422045c0031800b8110082c01034940b04580884440b106001c44030544a00480962960343e40e070501130300351156648074031405e006903503007082800b49542d104503802429400c800411460303035524007400721507001500b005090f1440d04080c032081088030705400c19042c46d011414401c1e650f030f10000900700d024510a940c00104108901030114201d0300a6440e00002098070115081c1c81101c0741c1c8699009280303680c00264200304000b01003205810383d44883c03d086001d10b00d045c0c80e0303032002030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 213557958 1250 213556708 213556727
    0x9060c06110906030106110c030312010509060315070507020108102601110f0c0c011e050a020f0105040c17060103111c050601090506010e09010e010e0402180c0721 72
    0x40c41240c0da104040101100081554019400245010b6580d80c480c480205030020850f1002807a2041c030b1010a490301c0c000c000d54113040c0c10003500c06c04a038604006c000c0e40c0c00780a04501e80600a038070440703201540c0001c0082c03140941c0d031141030303840c4543c0c03000401d0300350020302d11030100e840302c501071040402c0d03131550302180070903203415403501c4406071201130041c0075504c071911040100189540b0031b0180315001e07010030b40b116015511800d0000c0c0040d501101c9800c1d40200e040900d01903a040d2078083d201600030040700e48100e80352914207030130311821a641924240c80881480d40c040010161410303402c0400b88880b00038080b035500d1070365042022800502d826115501155200445a1140350304104482d00001220300f1540d4800c50b17100203005c03d44090f0b00099002000803030508210103154101d80310848000050ba2038000d21800400016000701ea1059000488644a145820005010b2401c0d0903801344c0d2214546407042c42c640d401492440380068030042c01c07036141d80001e1f40c80d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 213559208 1250 213557958 213557963
    0x30e030709051311011b03200102070c0603022506050a0b0d0c0e07120c11060c070209060d02040902060403030206151c14070b0c07030c06091206091b080c0f0109060c 73
    0x10383c10001044016103420a2903a0600240086c00b080d003018154802c0b04c8000b040d03415401501c800b02880d102ea8280c0c45114000ba0007104801d000304a4144a0b600900c5a0b01c40003840300118003075102c180101c80c200030b20650b10b060700c960038809508030307500c583c05510300c0480d403002001109540b103840543e46442508645114500010301c56409550083da02e00e900c048204188100e5007406010b00e46480c901c950944a140001780804851404a882403a0010002c490743c0c1e444100304511142c4047c0100e801c961158150741c016200c2502401c042c42c070a03000342c0218580781000c0325000c000403992512070300344244c203000904c04424031002910f40002100b110700c9035400c1110701e441c4842c2d0003241d28280020761203017044800300789401524401e010540015a46440c115114501d0340100e200d2814816800000100c0543c8200c545510503903007404840d0040c81822520704440d40a0030325504a00300420b80b5140010302c0345100c0c0b00908150704c1490504030000c005c8903951600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 213560458 1250 213559208 213559223
    0x3051b070201030b0907020625140f0d09050f0105130b13030c082101080102070507050d060e01020d09230d0c030e0d1406090303010810021b0a030e0307090513 70
    0x40d03009691103508004001d0001400c003000c6424840b0000755100c604540c1c0704650891800d80406040454603c00000409540d5003c000b003d900200702156004c40700c0030b44215001c01110148107018094081d115019a000e8030702000c0b0003c010b0b00355540240b03600310250b24503200000155030603d000e50800303450003c41140c0d006c2890160b03034504100301c0281901002107400d400c0001e411404164207011402d5542c0681da0720070a00d820b030b0080e040300408503000300b0414405401d060030180403040c002c03100030850050807500c050882c3d02089404e00036070b44602e0444240201c510503011480b1100003001c00076510070600a032903200c191205410000c042003035800b85485541e45d04035588000706011242c00380c03071414541c162820040318926000e040700041d200e04001c01664125440040070780100a0344000a0000b544203104590400f0720000840704011020050115180d101e43c542894140c1010100b524021903a4051007440713040004202c0710203c400700d041511b981c405003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 213561708 1250 213560458 213560467
    0x50601020a020a0806070e01021506150d050406050105091303021b010504170601030b090d0e19031b03150903050906030408120406050a051302010c15060b0a02030c0d03051b 76
    0x40707050000102000e98400740e8140c011404c0080407406a000c0c1d0065210788107030b580c0103001640c8415112a055800c5003e140020311207040c03090070300590004001c0220b01c0d000c443c507039903411942c042c0d07800d640c0f503036135240140054203105040039000442d1030400e030409951950020340c0c82c42c0d100c800700c458090001c441d003002c0c4d001d24280c030b02501070607181020805403520600e0766a0024441900d00c0c002c07070000318851810204000d40306041603034465200c40300d8030003404060390351403c61030b03800d000e91240000070808000b43c00d00c480d05007072444141e2601d18204440402040d01942d1400f40c603004140d0006600542107440350030302901d40c15140c2d42d480c201102c043c05100481c100d1001d0b07490800c02007140030340c02240308200541080010f511151082001d013102c010009000c100f00c0001500414001da5110f2030b6840a814089400b03925440d0b4208546c01101800000d0381c40466010107502090004041455140c5000c214624050000313241c1081191a880c507581000078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 213562958 1250 213561708 213561721
    0x10906051e1605090d110a0504140a050c091f020d1d040b031002040f031505070c03030e0709060803040305070b0c060423150f060f10030c0e120105010e0703051905 72
    0x5007070762000d1130b00411300a074000d010f0400013a1881081e0a1500c41c0c3c00400c401f1500b860948507103d1403c0c031910000000b6a25001c40f0402005c3c0a401510f00000901c0389002980c2c5070002c2c24003420050203d00b0300c2400c11980645440400c094107428003180000800701c180c0d048121000700607088a01240311300c06440400e003400581311307030708160a00000300445c0c406040c0d00c07680c040744d22442011410700c10389001c0c0800ca0364242ea4207800508800402004a4841c0e00041007962041d020340e88034036514400102115010348c0102903981012408005111041c452100180320b401c20540c5020520080303c4c1c0c5034040180002c250700200791444c01010080984001c200f40b1210840e1061402008a8050000115000070058610000007a404d05103241c04004090015184144907450103506a0241400340d600b00204402c0c0da0b11042a0b9035228001c1030446040d0000103402d5040501416003000010040390a0600303040a200091100070105170644948440000381a150314 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 213564208 1250 213562958 213562967
    0x31509071403251e0f090e090c011e02070e0402220c02010b0a03051510090204060504051005070b040605130605010909020108060901080a02100306052101051b090907031409010906051e16 82
    0x940005071401707500808c01030050000990300603904001d8a4000490781212480da00244c220302d031a0b00148c000c40c0c0200926250112003640262008001301d1007000d0060400c0000c07001903d100c001035880307038803c004446e0207200c1c0440c000303400d03102c2182150458640b540d0345d04039800b000544070411000283c0842c2c41d6181000a06442c07201596116a01d14004041d030700540242d900c160740c8070b541c500070f503400780b01155003060b40b1510301070242c2d449172141c00040c00700a102c070020340e070240b501d03000088003441414003800030076a001410b8089800018020b100092440e805440f0400052007152000a1030307240d501d5045440c040c4151130118100c0141c100b942c00315401035405079001c8801d1110359108409003030828002c00c0f041c0e6903103410780704034400150784180f4842c007008603501c2400c1808465a02490b5810081100400c54801036449441203070f4a0800d80d56030042c0504220072806203a0304800041e03011600305604e6104000180b01c054a90381c6000081c0b02200e0030507025 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 213565458 1250 213564208 213564227
    0xf180723180d1509051204031a091606030f1d1506210609010e0705131503050303010e090c030d0f1209080a02010905070b031509071403251e0f 63
    0x8501c03d455600c2a0750850b5018106000040f1903034000c101c508054010404240c0d000c503500701e075280000c0030014042013035030b403005001d061003405500c608030495640c45820000070440341e40d002800a040204c0305044a8170004000c00c3d901c01441861060140018580002280006c00c8016a01c070000090800d0074120f020381c40491420b5132001c0008030110f08144a000c0d484000d000590820003400e4591941c3d0090b00da1004c0017004900c28140785500c2000f0703101421030400c900d503860f91100741c5540c209900240219403803c08100c40303040d00340011310468205070006c20780c24807412000f600c90303618030b04544100001c2d02c1c01e01024901c141c001e0455103400510181d40d840030844000d000e024108010784892041a0b0000360307204c0428100c074031800e04580c0c0480d12403403940400c1201e24014203d5820002503061807944072042c0700003103000f0214150580450f0758041c55841480f100c0f54000c0c0188000210a00e00c60681d2001906e8441d549240503044400e201005481e050f00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 213566708 1250 213565458 213565463
    0x10501140c0a0803090f0a021005090a0305010527070815040515090c040605091e0403050d110702010f0503040f02090c121306050c1e090f180723180d 66
    0x70304282c60090100c3c1600a5000d500c00b10107540301c80b80d001416550300c88600e84001d401c40c412420009445204202030901407400410006000344d0342c0c2c1b03030207094401c290340d002295541043c041108000d1428100d6441003001e010b0050b0920b002d1000c2c1d1a4210b15500e103074034142050025040090a00c00c0e00c030400c14842045a50781072000802e5600c0c8080c0351442d003d03a01d80540404d440c50480c44051042e002c901c0307204c0a00d00007031030039006400003500c11000d1050501003842d90100e24010200c2804003580c400307407500402e0000401e4035480e90740c03683c03e000301001400080380151266001007a0103840a5009845850f18500035101d020806081c030803c0405000803840d8030081c444810f0b00901c1d041c000e5458030340071a41d46200343f4501802808a000c8d080b80414608000b400040c0740c001d1800c0e0080940b480400d1b01c004001c04d410460304c4a82c01080203003500400130314000240c80c20303075001403040b42d00b94040510400304481006e1204030f42c1103006640d40c0094221030399 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 213567958 1250 213566708 213566713
    0x40b01093503070b01051003062301020105010b0309190c080703081305060325030605090f1803090d080304110a080a0c0602030304020d0f030e0909030a120b010503010501140c 77
    0x841000c03a004400030301c0d000c1d84608003103114038071034040400800d540200340c004058029507440d2900300490030391303621020400d06071605800201e50f02001c11501707907001060850381d00041c421000a01312030051704203034900241070090240c11940001c80914020ba1075440d04481c00590401e580c100312240e002010b240304910f800300800100001601d903101400380c4203080075440d481000902d020449082034040c4500b9010120380d182e400c1d4110b02c4030014200042e080d41c0b40c00202d2540c4400b05c8204e1001d8480c2c10a0100b40302c2149050007601e68104003842c00c0c5200c4d08d000940340d0400080207000210040085003d1041c0400100160f140080000c0c05856880d407da6840b003c840710141c1b55817010180004600740080200c91182d58000e02d6400504100c2d5a5240e642c0000d50043e420443c690100100d03d80710a40b49034090409000210303150020040000e200485142c5096105070411726010801d0340c00c0010340381540d000342044c00d004440b00c09641014010b5611500451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 213569208 1250 213567958 213567989
    0x8090a0605010b0408162702071a0412020106080c19050d03230406080f04052113051206070f2a02090105010c02031506041404110f010c050606040b0109 67
    0xf00302603009104662401c0217403109082001e051800c07450042c071909001010302d00b00449910464480c0c0c0962402c0f0a40050034080c407900c440002c0c501e10305500c54203120401c00c0c00305118803100480d42c0c9210300d10091108038100350450380c0324002d0401280c0076001c003941d02c04090b41507001c918090321000d818201c05007220f0074003d2250250710070100300c203050042d941500b000d44004036000d0710a0b5480d00f400d00d4881c40c1030041d070150010004d46550003000c401440201c2c07204c60030580120640800754451940528261809030203600c494820802004002d400a40100b00e103688409103040c0a51102c03040c003002d44006039403540540d910211070f0080041c041d83c0c00c419070030542c02038641107440d80e241d03c0191a21681d42c000690700d1f0340030110003032128003850251a4801c1001e00040707107503a0400203403074034050203480c2221404204c4041d00c1c801e01300104460345890003440c00c804103035640d446a40d02c0c0d0700050406030283c1d4403140125000e03406100f0070300003400601c440b003c48 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 213570458 1250 213569208 213569219
    0xb0c070e09060708010e01080304060e0402090303070609050c0d0203060420091303030f021606090516030b0a05090102270d0803010b0309060108010c0f03021c060b070605060901030309030308090a060501 89
    0x48040481d054400300c0d0811001181c46d41c40b00366040d041c2c4040500543c6414101101980c1004c0b02e1082d140c0d115400300210122a14140094030f403a51040ca40410000d445103011428490020500c07030054111481400260764000354040d00140c201d05601c1018100d621038907a04000c0807010b6411031000390900448240e01d01c4412144c034013955041016600751480c002c01da2003000d682c066080091149000860380c1e41d4014039260740710314101c4402034480c010496602810358015544101d401080041e0a2003600913150722410b240001c5141407070300070f0384d59907010940b410800304210388422140e05444203900c4171116074104014075202c3d80d440102c0e403815130003114810303140e001e02d8000286182050082c00450708603a204e0f8403404a11a00032002900a010b01d0b4040c00104000952110500e109202c0034001030710400e40d403a00e0b941442016148081d00980c040d40c0034034010000f10303912290050640754180f400410030b45076001803034a8214900c2001c0c24240c5400c000103803 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 213571708 1250 213570458 213570463
    0x204080d120c03110a081801060b04050102060a0b0607080714060406020c010b0108100b0a05070f030e1503100902071a090d09061103030705030c0706060305010b0103050a0b0a0b0c070e09 82
    0x1540c840070028002100c01180c102c041c0e07032000a54001482c424030503d0300b41c40c00f40d800c8a504c110101380c901c0403c030100503410b00750b6003c1e03480307042c41403c0001d0070301c11940e050041691198a00d8000d210400c0340c580810803511891101600c039403800700b0100c1c100015401c1141211b05d008080741d21a0505080c214003c1d4010880701809619020382c040d165405000140e126500c28a40201218503044041600e9072000c8c08030801c000d01000344000150240b8040d0107081c1c0a0344d00e801503001004e080c4982d06181e0500b102c3c504134107004010704690b0f144810b006848035044050307110f8002d03280144c5c0e032240c0102c1c1c0400b4054809c0030007101c42000525104410060f40e22a010b0503038603c01070300c0311008a07800c010140c2042000801e0b03607000720011034218140526003480c1c03408a8403401d08507091504116500d9440d203440c0f9170f10f50f901d80207d54020714030345c00c2008110850700c0002c03010300aa100b110116040868074038003019040c0a110003c0c0790f104d032618994901149400d4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 213572958 1250 213571708 213571727
    0x130c050c012901020a03021e010b0a0b030406111e07031209060b010320030a050601200601080d050a05121f290406090b0904020f04060e0a0603050601020d120204080d 73
    0x30b42100c441040c20032650301c000303041000640c060300a8a1203d401200c100e00320b1260645404240d901d40010707028507100e00f0005c00040c05070f5030500ea10b90410346010000e454032018850881c1c003003130029242c40742d00d0200800e807006a410900b60703030b000e40389800c0d074501c00366444c5403c013645007001400900c400d680105454034001d0340c00b00030310700c2110054945554030765a05443d00740d0500000794004440c5d80b10300d8111405040ca0410704000a00e01c12046d074000540241a400c21401080481010020501e64410030300b44641001c4121034000d18034050341c007408c2a0102c51601269a41019001c24a85642c4000c240c08205131035148d805004a1100090000c090b1460359845803601d02d10161001c0c1c0e1a5a0760f246403040c40c103100d400340380d00100d031000e500c954208022480000d44200a1005242e00d031107042800c200c401c20803160340d00541c020b50905040000f002103c0c0e1b40854071130580d2200c1c0c24080205014008030600038095504044864440e036211a0a001d41049404 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 213574208 1250 213572958 213573011
    0xa03090e010f03060e0a06020a0f030b0105091f091e0812090f060703021204060f080f07081308190e150a050301050906040221060406080c130c050c01 66
    0x50205503030369200c60103008001d201d103440c040d94402007030000848540010b144c6480c002c0032505000301507100c0e08100c0e4000450000805d402246000c52990035001c0d10403000400d080541c03d010704103011402001c9014036900d030f40c03034426000c5198240200c40e5580604240d01040401080f00980c0c00410030f1383d401610bd041c4a0b11b00e0b004143c030809012030f800c0310340c00303000018039400580500802d500000002c0b0250702806202c0b00c2c40c040840b0251004105a03a54481c421055142c064100b84006e048030b05001d85d140104524941c00403c895044042c1d0320304d8a1a01581e410f01c0032490081c440501c2500c246203002c00b01c2e180d407140d101e80394001d08843c8000760b6007005080c1c40382449461402e002107042400100321502e469000a43c0c0710201800140c0381c9400007c0d0300351095072107040ca044003d221014030406013001c1c03007003074040c1030903500a211641070840041c00c0683d403032035001c9015445078454a815882801620f202503641c0d8001c0c840380102d1a0303418964045039074032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 213575458 1250 213574208 213574217
    0x181c05031c0603050c01210905030d1a1e0a050901090203060103060f060c0809040603080706050906100609050603040f15021c0504021309171b0c090f0c030a0f09050a03 74
    0x14075100e401610880342165030190041805640c05e900541d695000d4920711071420103500000c9120380c0700b03400b981c501e280c81230000e503580c1d40410a101d400c030307071000b15018000002e609401005448d8001400c16a5114110015208040c840011030b81c2842d500034541290b02c000001980b00d2894000c0c500824090b2802c0c0101c903120754076500034171424443d9900080600d005200840c400324010001e0b48400f0303002007801c0703407241c80f00310380d5500480c011244199030700d0400c5218001408401e4000702d403003881d01c0ca460710704640240f074421203000301c0b4451440040072900300f20400314001002c81c2d00181da41e1a001440321148009c1d0040c100310088490407404001c240401032084512450340101041030448040000c68001d0003000801c4500c043c0c0c05c102d4501d4841181c02070810154104903109000340041c001e81c0c103003030100110034002c131640300c00d02c40b58240e4a5007650780a08400141e64072980c1b01c5081e00041d0040312024078113a8509000388040c0040498031200c058001d845 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 213576708 1250 213575458 213575497
    0x280f0f0c020f2a0406060203030402010f0503011404180b1e01270f060b0f070c17070e0919080910080609060f060d050c090a09060506181c0503 63
    0x5041c1c2c0c84884051031000d40d6003140268800121014003c0011400503184070000d42c018000464202c0e48660007140160b440841004119030b0b20842c0c03c00d441b54540350a40c01d6514152454200c0142c1407403c511903074a840d101080c1b0b00304040e1141400d60070100d079804c1070804404121064520b020781e10070840303500380003082c62a4500d54203140b514040008419110300290b89500030302c14038004044603a12210002180c61030b500240620351100c1c0320703481d5181c4175440c1101023000d0952007840361100c0b0008511340d140002c1400c204851980032005807035952003441a00f0101402a00d89114180c070020078180681c0d040609114401592a68003442c2c0c00740c015a10f00d8000c07100c00f90700810800c001009414002e6416424620151a02c3d06103a00890081c0c01c0c0c42003207074810b0010101095001e0240b0744000d41000410b824042000102e003803c02242c9280b00c0c41105000361394188411f61815141e4900202d02c902d0150041ca5540080c0d244c01501d9521072005083c1c00c0d4507020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 213577958 1250 213576708 213576731
    0xb0f010f0c050a081917040f0201030504080913020904060f080d03020703090b030c0301030308060d050628020f0a0306061e080c0f0304050a0c050f0102210405030a06090303050c030c03280f0f 84
    0x10f941074080e0781c01120642340007806500440251500400448980000340100e076807544540d400c0c0100c00c4003090b005038540003040c2c18030040f06e0203a4071008801c0c5162200700031074032000c9000c800c200c2c5946005139590321282405d0390313000101e900c5500c000000004000350380035100080d6040c2c0f80f0994403021180c40d0002040110000c0000c042c041c1d80011012a00402d00160200d94294040d01490042c015500c030002c101d8000700603140000308002204401194140b0444014200078144003000010400d220744580391050888000d0200140c04910b081400d401500c0036910b0030090f0035a00e14107860941d40360301c40c409045445035440301c0086503520740800d03144417401c0180e00420020b540180e50f04241410034609041e0f0b940c4c01c10001c14240c900b81708a02c0181d0080101160150051800070120742000703000801c140e00038000c0c8241c0d401070b40c084940043d400944100f40408900e100c110075210300f45c120b42054030340000c9500c584a00c2c1c0002c5c40e43c001181e4104940f00000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 213579208 1250 213577958 213577997
    0x501020d030e031c0f06030302011b0206010b032404020d0b0a150e09060d0f03080f0c0313140115060c02090a060e040f0f020616060b0f010f0c050a0819 67
    0x40060b10080c3c1c0090100402c020b4404200c40c01c0c581a240c03001c240c0000c5294501d0884d1269002600180d4480702c0001c441480007140a070b0b8540381c2d1004007110340c5000c805080c1800080c00c0820144080f01d0514200e14905200e4442e51a00420465441d50840b5945005201d100e81c1180501100400010b849095804510341c0c43c0c282d0303c8607180c07030b40c0c2e80b81040072030304004180c0c87e8040103200c2c0c4040031409104058056031721a8a43d0345441c1008840841c003c18028040b80101c1020020880c0310700d500c040b11030843c1d51080692041c3d0740940340c404e0141c1000208108000b2110702c0001d0103a502c001c14401d0a8029648008607403104010403083c2e03540ca0042249040f0f41d10041000515a0380c4c5c00384001e80540901c030406001940021400c0e40a10700411741600d41001103001d2107114400e46184030001c43d01280300c4100c00c0000f0302403c60143c0208140050340018200b4010203024002507030f5400007140e80c0e510194a448805010495600f400240510251215003000c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 213580458 1250 213579208 213579221
    0x231b09090a1b1d010507020d05190b0a091a07120c05041d040f02061e0c060a0b09192f0c010501080303010308120411040c0807020c030703150b0f0d0c0501020d03 71
    0x42030040d0043d102d40c000540e0326501400c0101c0c0c101c0424944880032540c14080d01c0304404036894000896034250078a91420503001d000d4618492600d124000060f640000d1900b0302200b0100311401661204000d5881060b92200c4070300460404500803e100e5000c0010420384100403110119200342c00c50f4a500307070700111801450303000c180040d40058034146001e42002e4111814206802c03448001c078624a400c902500120b17540200d06202c041401360003040441c203000d55840c4414500a80c030429080c81c104208103605a03210002100c111403c104000c071921a0070140a680c0400ea0403c00e41c4c1e4010880c034541546000f00100d540c071400f0003103038101c03600b01c0d0b5030500301000d02070714070002540507208545d100700369000101c0036200c40c001e0900b144c0745511a100740d883e0801c000f030704100b260aa0b80d071094100500520010f4904071103d0f2600301041c00010301006100c0105030b1549201c075089920034802c00c03c990800075142101c9090f1482039083d41c007007581c82c03002a419110b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 213581708 1250 213580458 213580487
    0x2070603110417010213151d031e100e030306120118080c0a02151804050601020307111516051504020a12020406050402030a0603030201231b09090a1b 66
    0x802c03040258914030002c6240f03101e0f00e50b00040c43d002c82ca038140707a902402d5500089204015040a12a40f40c0120003202503094020068102400035000280c031040310700c0300081040550300c0c50301903200082146154014500404100414400b007403151340b41c0045901c948201045051010303c20b5041c0904104810802d8140d0300b05501641c0781e5180340c02124100300d0500c29001d201e0090b82c2c84203030a40d408491810390700e075943c4002109103001400c180311240214104824011140d074000110b4400641101030754819500010004103080599030f000e1040c08004200300181d0220b00048000b424444c208591505041c144142e142660456019601000c264020490400c0c44007505406920040c400502e40c0e0f110340001d02260000da6079501c0c0700303075210010300416409104c1c0404100300d800c80c42c0c1c21102c4401c0c414069080040408000001c41d8940c03515020515003620415800100015031514081c04040e00800564401c840070910310a141c026181c018201100b1481 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 213582958 1250 213581708 213581741
    0xf03061b020a080c0109060212070e041b120e060109020c0709060b040b03090c040603050c13020f03060402280f0305010e0702071518030b0a0c080c03060d060207080a0c020102070603 80
    0x200c0c2d0b0715041103030b03001201100819522003a040000410b02e1008142c0103191141403c0c90382440703100201035150301414503000c0d510f420300d010404a8000c2003160fa140c8640b4024601313601e0445082b016045601c00f122652003044000316091780240c010b03001d594581ea04680285030385441c0001559120700c45c0480e1038008105c14444a01400001d40e8000988002c44da144042200850222071465009544507041000c1d070b06100d103403c0c40f000e0810651500b083d0b00f40b14045116104603c80540381c03e125035030014040315100c41c08805800f16070000004035806003020040580131000c4c401e010400680752200100d0051074803104240161182da0040c00510b041215081c09440d036500e1690a10031150284400ca0091040000c0654401e054002240c01d01104d40300c00d41d110260f09405200c184410080b2000008040e2544a4821a070003c10304903d0f0508400a104044001c1c001071070001e400f1250b6508240c1c03441540c0e100b84d00b101c1d1030303d0392200d08a00310351000b0035800b0b080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 213584208 1250 213582958 213582973
    0x30a170106050307030b010522320d05010b0a0f050901050604081005040201110d0504090b0d030f030203041104020c0f060a020910030b120a1203110a0e04050414070f03061b02 77
    0x45c8654080700158006043c078174900301e031644480c04403805002c0350b07405104044c6805d00541100509844410f80c8208900004d5031814507003145d07059003a90420f00034444900c3c041c0900c60250484900301501030001c1d40c500391900030b920701c0c180003409401e010302040d000000e46814072104807011620700001801d00da0780417440000c007038040908203038100700e1104030440c00100e05000c3d9100c0c0038101d4441d00d90b2076140505071001d5800002042d84119240c1031860b0100c0e800c14041d81c034918035071600617525030715031421000c400034002c802e641151012455503080c05000642030a0f904a0900f225040c0d5a1081041c003039110b002903e42d00480c0310b000102c14030b40650003a03084864000c024001c0c2c40c0744208002d2030315205030020f490a243c40a600b86115400d8869540c14003400d000191901c00910000b500c040c1c525540f90703000e40d82d034030b0000c0d040c04814040380301c9009840341a01c10b680e80d40c120551040f240381c0030507915985080708038282c10618910010540242e9009080301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 213585458 1250 213584208 213584221
    0x5070509041a060a05060c1e0a1a0703060e070504030212010501060e13090203030d0518060105030703030f0c060e0609010b0109050d021005070602030901051602030c1f0b060309030a1701060503 85
    0x18040034080d00e40090b0104d0002c5070681e100006800560805002032201d944407800780b842034803908c1104203d5420090f0030383d0200c0d20350000c43c8140081054804072580300d03664100d004000c5644281811000f030024060b01c070340d00c840104100e034003c441070300006404a0030142201c1081c41004041203500300944c1c00c2e800c000542030078204030103c000940d04055004242550301c8a8040c034103ca035118100a520040c0c0b080c0c401c40d280510300200311944c100030100ea5220342c680405014000c3c013101c80e10a070b52240e02c0e000c606540c0700d40d091250303011840b42141e40701019190400d255003010090b08041d442490214119a001040c4c031010307803907540910240005034221002085010031460001c12142d00080d806a602403000084034074140c0d08111481d54196620340441d00104981d0103140c1000664041d58160311a508540014a1002c50000c00c00b152240760417038004801c0083c4450080040c008c210078079260403480810a40c201d50002d40240110000b140d003d1001c102e4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 213586708 1250 213585458 213585503
    0x3060602150a150509040f0501050702031c0b0a0b0c1c03021804020904151706011502060f15030f0709051303020a030309030924020d0503090a0308040f0c0b070507050904 75
    0x4600c203d0108a5811600d03140072409402e01246c090b103500d0384080310241008000d115965008507a840a1030619880442e00d200c1003a50380600c4940646580406450341e0720715240710010a0704801c2030756200c2412040340d0315945031a400c00300b0040b00c1c0a0603030000d40680211426502d00400400c0201c1d171040c2080002d4100d10b20b5907800c55a9141c02c40500b00d10382c2020310113040d094190a158440e141d00540c40c0000503040300520754445d6060042031900052050782242d09518514072594607040080703022a05d5aa02c10780c1845800c040245001001c00c82000303849110310b091000d41d640c5d10680091801481e8002c0050348500041c80200b44242c1c0600e840d54424580030714110394644402024440c0d4207401e210242a40311030600480d0100049068000c00d414051300710f00c0d20b40c0aa50311510311090140a000b5588000780401003000010540700c1e40c001c0a40540300e0702e0394212801b81e00179040445540c0300d40200401d19180c008c00d01d17841103500186412100000c4c140809 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 213587958 1250 213586708 213586721
    0x90106050f0d15060303050408070821070f0213060302091317131206050a0b0f0609042003010807031205070b0106030f0219020c0a0b030f0c0f04030609050a020103060602150a 77
    0x11940100360f00100c403d00003501a42e0019400303503a5246e2038a00f440c44441c20014180d0281403250701c00d48203180a0014880c001c00400e2240b01c2aa0310b4820f6404c11642c07007500310360020342c820350082400c05808099445802540d000740c07080078091342d4400c6d10700281300354180c002e403404000424100701403840c0c400501e004548061038600003666905c0b1000d8042210604540807604d8204010b42c4d00c2003481510f058a4044502d03e81208542003c181c81e0b10440000500403500e0390032124040f20702410f0318041c1220200c0c5607a5a44c5e450003500d07211003ca0204582e5003000a103d01025031140c001e4982840d00b0815440306030340b13000400d60080107002c002040c00c54007480b0704050303000780701211042d410090f009895851801010055058010303040a2174000042c4203101010441c100e045921407040340844c2d0340c40207030040458050103142d10061440342001d02140400c0000300300760074024400c2e00e00340300d40d41e03d941050361603c0401e110400102100c000080c4441e10b660840c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 213589208 1250 213587958 213587963
    0x506060d0309080607020105190b220605212104052403041406010f030812040618121206080a020118150c05120a0504060c0213051608090106050f0d 65
    0x102c0310a6450502505144048841d040503075510002c1201c0c8041036007681004045150007000f413204000d0000307491151252040290341071031020040d90080581c0418050140240890300800000d4040d401c8040d818100452602170300c1443c41c190040d41c4010b4041281604490781014144420b014100c407a10303c51510806041902403024804c100065006078003d03201000a0210710074450b00c0e109040e130ac0640901c403150780400114070340c07000396224592884000191a11142040005050f07400410310740b4841800c245410000385550b032030710081907621840306010f00c6104c41000c0715001e200702240e5810101041c1c005601c03c002c02d04001c504080280c9520f0703202e00c15103001100742014000810203944004044c4181006514850b54202100714604400100010030a010384d05c640004d101907030281f84119520120882454403100070104200e1038004106001110400e00c0c0703c0100703a100020421403041802400f0a030b0748048c1031100c011100d54284106505866000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 213590458 1250 213589208 213589217
    0x103151a060c0313050102070f03110607140d0e04090206030f0a24171b010f0507170a0809070308041401020109060c0801080706210f0b040f0e100204030506060d03 72
    0x426000c1d07484002401515040e14021030304e030051031560030001006500310505560002c0801c00511a900d440380c02620340c00301d001400304000002080b068020140010040d401a51f14400c4440c07001590320413100c80c965440c0c203141185401c1c00219071314034001940212003080098100f08150700206d4010410590014001c10602140400b40e142c0c0804119100580e0208020358110500b80503050102c0300042d000c10b907554130014100d80c1c0154005814840307070046011b60103000c1e60a6441326a000f0103034201001819246200705d07809011504c012525040225010240009a0740e0035203901070301e041c0c509070510214150540c1084005411907481d4404440050b5550103018004000307511800b04950401804030f04061481c0c00100800100c1c080d05000f880d81104001d9030050a00e0780011031404030303e451409480654001034205040400d051500c0c0540d0740940e81c2d185440064484520400040701e040c1d10441c803014050f40d02046c0840c8031407420744614058603200f401d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 213591708 1250 213590458 213590501
    0x10203120c040609061b0b04020102030f0301031a0a020c06040320100902010f180b0a14131509031109090f1207120f021009030315140307050306010315 67
    0x502006030801100d10148040010a040001d5900482d4490141080d0b04103130100301c1c0401d2038510300c11203070b51000d4140e00c40a4042010f59000340b0072600769540e0709038040e03603e40e107a007003108803901015140c02c50f510384000050001e41292003070703e401955420180034517407195201260000318080440e15138401c2400d0200d80c80b00300700403d4101000581020031a01c6090002629106040d8400810f012584002c4440f01880e440032506440759902400d8581c846944200d41042e015450340040c22400139011011800c103c41300c4003110213811442c4800c0e0701ea81421150b134001844020042c0f0004615621540740070041140c1c06452041243c0088268112240c6001418002c80007600380015925081c8891445c80c11102807407400c001ca243d2002d403030700a664040246080c0e450f25034a040c03000803d8402d82000100a5a01e1201c4030300755110400c5080090811070040d200303102e001c00c0001c031400c0100b003c0341220b800401c81c42008100b00c1030b01c000380420740b4802455004016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 213592958 1250 213591708 213591727
    0x60c030a12020d0f060e0a02121303020a0b090f0c0307080705090604140708100b030c040501030e0106030203060702071806050123210a0c140306060903120406021c050a12050402010203 81
    0x440d0f070a200700d0151005c11203902e031021940c19428050070b100d14240c01080a0740b644852107031001d81045201d0040503070b59005040032403c2645d441380040000c40c0c400c3c00c3c800890000070740d01e0503a00a0704155075003054002c0416507540c046106244080e04400b00401003403800c2c010165100340040d1002c504101002000c4243c00d00860f0b1403c00700741307031b001031190720701c1503500403006410500030551650500c1d0625155500032440f440d0304264880119045a40742034004800551b409000c44070309081604020307490308058003230300c80c2140d11050708540d00c840340e0048104807601130312480030300c04485101c00c080b41e244101c4da9140c00303001c00009003006403200140780c000c4203030404690a070914500303800513940348a054004010320701c58000c1c40c0e1004002101e0308201c0440f030547d540c49080f008281040b140c6c00303210b029014040740000b141e98020959803460114100e0a01e001915031009031100d01810b40901c00040318904001d46d00f0035164840c940044c01401100d05181040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 213594208 1250 213592958 213592961
    0xa0b03120406170c04030b0a0903030f090303020a0f0302161205041d04060c0518041806020d0b01021e03072909010b2704080315030609030711060c030a12020d 70
    0x9600c07070ba000540d2103040502a05022201541124855503054541803454071140c600c054003800001000e50756142040030140282c0c040c2d9243c1415100038009011141800b400030341050840c1c00204080098442140d0720070301c201c501e00e081401a0050125498448c0c095100b19005464240201001f001c00c40c600040502c00c20a1400301317140ca09441c01d407a01500359009203040106200e802d03c032803040700603178a4040c020001d00340e900084000c1d080d0303074403492003170a454040d102c0361002841d00f2600e0800d4000c0d10340d050302a000c44506510802c60040b28007500034203080190401c1c030020300041c0207010b051800c070311411800c280c046007021030b21a896405648960890399180308001d06810810031540100000d2000c0040f03600700d00c0503904100d24000c0000f004008000000365032041001400b500c172040c00307803c40350b051412716410b60340c07a4080403090f03446888240031049a403800340100d40c500112a4043e60418080c18001e5400c0001501510346c016024000005c000c10706 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 213595458 1250 213594208 213594217
    0x7060209030a21120903051e04050d0606091a220b1203090406090204121b030506011e08010b010e0d0f122d050f030c09060f0301030b060d0b0a0b0312 66
    0x14800f071428945400000d091a440850b0a01040c1d0910501c00c0c042500030040c0e0324600411080100c011024040b130281030f10481d040300707074400c800e0910401840b8107607103c4020381d07100103410040e105403000c2c000b940c8901c82c2c0e5055030001d065644450603007491000d80b1125420040042031114066000801e1324440703c0082c0344940c07000c94901f02526190041c00000c090204045180074100600d501c4100150b110103401c96590320b821605121510030140c0045030080196407095031601103183c8100c00000340c01d5000e030f10200002c6101d00c1c040c42070280c1e00005841c0c4a034080589418000034000180003907600342c4100103004082034070130003410308401460350746002845201e100031103031a41c8541c18000c0d50301c1c800c0314000c006402a084403401f4205a0307a0700d0b12956030303602102c000d00c0b0300f00d00c0c580c0109000c81c203901c1c1003240c1806113040e02e21940d9450361555601051004208007601c025000d03041040100e5140401076228220301400901603600010340780c50540102d900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 213596708 1250 213595458 213595493
    0x6090204090609050d0804030813080408030f0a0f02060c0304031b0b040305090418020a0b0f040f0609031707020a090510050618010314070c0312020c2b050702030307060209030a 78
    0x103e40c0408010030070305004c40d000070307803a90400e0740c0582400e8400400341840100280d0b40e51582c0b12540c0d090095840a0300c5c02451444d049a9540c072900116000b07903080b407025080450028113400603e40d002040c0c041c070a014414420381150350b5500c0840e86084204030b005a0282c54030061404610005034aa108038029100c0c1d9980d222a0350603c8121141644001001782a4a00280050750307035040c0002190400000561220501c68141c01c05100307607444070f40010008a800034280da080b0103110300700c03405000c041c0e64580030f00441010234450150000d43c004504a82880740c44d04581c00150000b06464440850030384580c0442c610b41c1c400c4a48118038906500000d10035a8075028120500c10300e68008002410041005451402e06a41c01000d0040035000361440b0809941a964045005000c880109000c401c82121004840701d011400c08803060540382024042c8003162612540030303009629090060700e542c4000e40040062642c18000e522090020500020740c10001d2103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 213597958 1250 213596708 213596711
    0xb0414041101110d0e0d060b0a06020c031002190c060f0f0b040f0c0203030403050c150a140603061501050d11070803090105090d0c03080601023915090d060902040906 73
    0x64070340090070300520b2442501c255403095800d08a096442420121041c1040c0d8403228031364407918000c0094020b001b6055001240c405000030001d07400100515240310a078250350004000341c0e45401640319024100101c2c0c0002d0f80d0450b0180d2180c2442c4040300d0061a00007503150000788840243c071010b401540745251940d0b09443c1510385445441c92208422004026060410744065100e0200400c0a03090010204110070214424003d100500200150400d1b491800348200310060a0048440d60300e850101c000035400d0030b0008110b4081da050751000075580154100450700740d07118000100026480d2418081c180f840ea40c060019944262045909ca00c2c1c0a00803c1c21190000c1801849a00603c901401c4d25041040c0766010b80c0c03d868280c5846c0e480c800103070315140708150604448080c40400356450200310b110046c2c03420404081714603c12401d07040200c0a031607012241c2e06031604010300d0015140000030200168461800401c00c0e0020350006800c5405441c000c1d074045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 213599208 1250 213597958 213597983
    0xe03030a0902040f02070c0506070c0b120702010e011104051201020906030a0608101515032c16051f09080319141201140d0506040c14061c0b041404 65
    0x603e014000c86003c5001d0031401c6081020589410406c40c00da03101303447c024440083c0300350911098802050181612120340b80e51919400140410900100c40345030055190280c6d4001d802c0060040d0000444e44c2c800b2542000e0506c810445440c2c40407042810703641d82049526199160100a0b41c81250950000280e442c0b07844001c5080c038404a000000b034625100001c2c4840c0740c2082d1070000d80300580201e8118144902041e0001d1a950b00e01917030000600080c0d44c3c407409401e600303120840018060b100e5500598600180c0c81c200c0d4081d860340686140c4503c811180c0b96082410a14054917001c584195551041402e69024281c0f9461242d5000c2c240850f8036007180d001d100c000540a6081e1800072800c0c0d00c1e000084060043c400c48207600700e44011640e0740c0070a5003014640140036550f06040a24003c9a180c07038602c81e00d03541c50308007003a801141c80c00744282c459070241e5401012400f008000808010851001180c2d4415580c018050b00041503e18039481b80707100e4005400507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 213600458 1250 213599208 213599213
    0x70b1e0a022a030325020706051305030105042607030e09040501091202030406020717031209070504020d0b03010b010f0207090c140a0e03100e101a1801140d02090601050d0e03030a09 80
    0x50a0081d41c00b00d081007041c5e00c44180e5075400103440c400c41d202450600e4642d542c0c0a407200d4074000c264040c44c0d05600785024401481074006a00607d0351441500d031180b15034038600e030289801588005004030311103054400b5030741045213489030b01500c18000050848020764130b01030744045030701710380006903c041814480f96404104210141000c88a45403c0000b5010556540d01c5241016541d00b1307880030100d08844020403140e030207401c1c010400e544030100790202d0380003030540c03680341c0344a50700700001d10415501904052141000b01d5001d86021418400008007400f10303201e200081088036050310f10506c0c2100013074541c50705a6981e006040c8500030415150000c040e400f41c00b5585420b21030f076140c50001500d4099800700d11008910100c0c050f60707181400a07202c404540020360407019000444980010b503041c4c4501c3c07206a004800100c0600441403c022402900007185030045202903010304042c1c0750070f25a1036404101d8a120401c080d0540d0000e0b04e07400106921881041c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 213601708 1250 213600458 213600481
    0xf0815030a030f1116031506090f022104031704030e060307090302121c0e01120f061e03080a03051306090c290307050306031504030203070b1e0a022a0303 68
    0x4070500132400400e00b83d810a6000b8984c02c42e5480000c100402e40a0500c41e00c0d1800d41084005040444080102c104664402c3c0080e60280310507425401c2c1c440600c840780d01c602102c81b4020b68140d0342d9498030b040c2c2c604030070810450140c0300750103100c542c0311202075a59a017401148111410ba451005407407452040c800041c40b1280400d185030451003000102c2c0c2c1130540e2401c600d05903441c040c1c000b0f058500058412000d05c0c030b100180c290819114854420700d41d0001d03401c49181d00c0a4907411000c001251010301003a02000302410000c00c98440868402d411041d040071030280c0e401c1d40214541d0319003040303c07030710322040740c0b041d40c2000c0c100901100c2c420b50004001003102000c41811251201c03521307034071000303000105004020001c41c059440c208507814400200302c842d9905401c01d0306020b075a903008004120b03444184e07080000c5071100103100b50720745490b07003207015940c40c0c0343c00e4000300180d0400200c2d281c941003103406601d542100c1040f43c010555218000c4c3d80c1ea810a10800030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 213602958 1250 213601708 213601727
    0xc1c0c090e010e0609070e01091d010e0705040602070513020d0e0a051c0c120c05101413081812011104030605070503010509070806040912030506010e030c010f0815030a030f 76
    0x1100f16242000340f651900030010b41c5c0003080d4544030540502c2e45006840d0401c1a8020440382140916000d44010005410ba0306a800b8440c00709226650b0341c0c0110707040e04c2140032741d500580001c5804c100a0034444020031040348488800341c1000385d0b0045031022115169061146544002903a1080c0728080c4401800840e06428100001c0201070000c1e1240d240c80ea80141116840400c1042440c0b01d14601e2000d180e1001c03c0c1c8101401c0041c1c000050149805085000e504a801050b0581390a03010000302a41c010348481c109014404c4842000000701d80f8960084614141000290028131a040304800c050001c242c41c2c6042d81001002c40c2e200030320341e1051010403c0140300503900d8480141c0e000955290000680e6500004180a03001e1840020b000d8121100e00c1244190903800c09440348400b83d036031161a41c8541d040603503803079180c101c9070301260028100d00c01c2c02d8070500c026980207406e4000502042d401b480420301d0402080c00540005100300d8080d030480380d200700001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 213604208 1250 213602958 213602969
    0x5150709060c0213090b07080709050a030201091503090c080102120f040c1505070f060501172802120303040b19060305030d0b12010e0f070812030c1c0c090e01 70
    0x600c003141002005845042c2a00c000380c80382000d513844141c04009508075028240d8068001950f41c2895040504040c81c00d070748500102e58072100110703103414081840c000b00c0760140d48074041c480c42e0000c4030220314072161341c520405440344108000b01c0d0860200390010f01240d0001607540300c0711a1000011000502085000480031007801302065107400c010041d180b02c500e00501168050300d0aa5aa110380742d0002c101404002040050000c960f20040c121030040b5021803502001c00d07805030b20303000729200e400000003082ca540705008529286030184144040c05521950381201c2c880781c6181c00456084a00b90b50310801c10106144c03244e40390602607140c4000384005801c1d9038415440e4060794181c0714100c0d0740c82e080043c3e66a183c6101c0c03100c2000c144000c10502d904210310685542095968485d503100c0c604c0005503080e0009142c070145507142e030340139007076823604421402c042d80211043c0740c15984800700d6a40c60707062032181800144840d190b02c8501d034640180b01c011600141d020 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 213605458 1250 213604208 213604217
    0xa1503140903091210050a0603060e01022a03090604080c0a240e0112020703030b011103041d0402010203040f0605070303150e0402040e0f07090509010b10201207051507 74
    0x144a07000c08004241d618821044800c00c40440d070500c0000d00d0304540341443e00c081c90403d802d1140c150b0203a07018200b6280244000e0003200c002100080c241e22401c40c86102c075400c01d0101c0041103402e040a40389225010050b280f034030080100103101ea03042034104c0d00454010b100c00340b0a07031030805412001085900d071042c4141d500c1c8000551814002074002c4140090050309094a038030900261064400403007046460302241c0c20700030010200300307002e2804a800c0e0900108031080000c1510304803002e81d24113000c0c0c96010741807111110809441203065100c18000424503815018141d405044103990305501c5944500b000ac080d074050150b22401c0b41c0b0398800070301031030b030600c2c2d00d4607880313501614003150728080344020314985840c01ca40600760b4096900003040c5444550801d60223030000038003d00105d041d103000c01120003803040030600407540a031420501915061b13940340041f6184029624580012442d40110764050300701140c65805c10500380a0b2602c68240c45500031595250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 213606708 1250 213605458 213605461
    0x307050109081e0102041a0a03060911092b1a070306030305090f0a0905070201060906050603090c150d1104170606061e040b04060e1002010b0306070309030c020a150314 74
    0x202684524a20201850107440880083e076010003d404a4004024200700d0b20483c04040c03400300201d8004029440010b82000300c006002e00060241d41e200c0c1d203461070708901d0103030041d04001c05150b0704e1543c010020305003d54803030103030703074030003004500358080c5924140122080c154013a403000000c003400141071803c00c8c01c1c00030a52102c2a2014042d0a0b5050440c0850b54000509038003040da0091100d03505040030004d03042c1e41034002000f00d801c54002800016100e00c100038450108956081240c2c2c00103041c0c2c0014035007403403409040342c07440f0000d0f03261030038104007101964403030440c00440c44400102088659a04101004018032103005803100d0308181c8001800c40c4500e0001d05042c407044c036041d102c11002401114002c0c211032105942e65507403440041c2040b00b201100300e206090300c0c0c5d551010300d40103001d80880880300a01400701a0f884000c240d004249214080d03041200b044a8000140c0740c3c5407804014180300b4085652a00e100e51005003034038031015102d64004040c00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 213607958 1250 213606708 213606719
    0x2b0201142508090d1b080106080a17070b070c02011101201c0e160509040309030f15020c0f0706020a02030303160e060d020a0f1b0204091112010b0307050109 69
    0x141042008454003071104031809070804102a004031800c807a40844a41611000c10229100000d214030110a04203015640c0d08603641c00c0710360521900300c0c141c2000c01005c00190791403c1c0703841c8203140d040c01142031152a443d486a420f0f0b0072a0814003040c130940030001550703002070f100b141e80345044000307000050358a8444c400441041a61005d076203404110501600c00514102c3d20034a4420010802844c0d000c0c9201d5941543d40c240c211455404c10001c6402c0c240140168030694068a58404092940d40d03011001442604242ca69412410021030b9000b01800140842144200108204519105082c2c2070003c02e41c0100d00355030000c0c144900688020050301c2d40910307081c10801131840301000640708008103200f084d5024100244540e080e449541c003070240b03000380b035a030301840f220345040030340e049055110720100f001821354010300107107460307007151a000344102240213a984100020a600409414240890303945074080b100042c1000c100d0350000b01001d00e01150b00c3c91410 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 213609208 1250 213607958 213607987
    0x3020a08012c040624030b160f08090106050603042a120303090503090414010609080309010801030807030e0a090608010e010c0806011b12081906030309050d022b020114 74
    0x207080400b491140075000406000c100e034840c02481040703140410404103840590000714000e8002110320300ca960380406d00300510506104060102a121003110708200001981c9100c00186003600542d04c4540c00315190b01c4d0040914000c1d8424905080310080d600011083c44120303010b0345000864605080011802e0210091039503a05400c0001c0c0c0038401d07041690451144d11180d039009070501000c000105036520b40301e4102e450319643c600c501521031840d50703101d00c6080b03003080c0000d000d48014008104290010105079100b41001464000d040000c5881c00216900c2051066a181000c0200450a0162140b00301d0624003c2101007170840d40604003034005070a15042004c002d584031f002e840301516950701140c01881d500300601021320004c0110604407130300a800d81c05541c2c0c907142c0c456240554401e8a600d9240e800c285400e2409000c460314952106a92001c40344807c5108510322a9800c4440c81c8030340561100031955000150031b95460705042c030540d40c0304102080c3c907a200d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 213610458 1250 213609208 213609269
    0x809070510082e150306120506091b0f28081b010206040f03082706041401090b010b0c01020f0301080114090a0804090903030e0105180105090f0312060105070c0603020a0801 76
    0x4075131018602c1051100450050895401010840100d240303483d050000c00540c5238030031041901260307034400e04c0d9000c01040d10744a014480c0c0003d80b203418841a4035004608440c01c034820401c400221540034408043c0a1a41c0e22445182c1c1140340821b000c0714840300d00004029003170000f0011401c1c030b9500c110000c501200040c003003000c41d41c0800d80b542d0f101c3d04009001540c81003905504441207404a44844e404d40342140d481d940601729000400c0306010320320056401885c0c100300d60707192104894680e032141d0b110240c0e0755070800007103401d0b4008401441c0031b0080203000003810b1646411100c00890060200c04190f800781d000030300040c0421084400741d0754024000302c1d41c1000342c41e094019110032a6084115420102000030090280b00c01080d0100c03200000c3c0a151035100c681502d0303913104010304046810820492030bc2c003144490403a00100189401c514209558950101c8202e4941204c3e0000f600000d00c520b801e45e01801e0640941881d00e682e0100c440d1801040811600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 213611708 1250 213610458 213610469
    0x2b020703050c0405180709020d1508030a030b06041505090a0b12011a130b07020a05101b020a050d03020f010621030e0120030a140c0c010809070510082e 67
    0x8444c8001001a8140250000c10030149002c4800540e21144184041d4021038640d900d00c134030740b8030301c410350540020540c0210f81080004d540340c0b0109100440140c15103818644d0042001c04c00095441840b60520070115000d9031000d4484e00e10008220411030507500c1103030060004d2003504c3c12100303c0d0a10364110349202d00c4000154240d0b03000b442c4a07015440410208501c402d00000704444454003c0c0f562502c202d42d0350b1045074842080080b03003000010900e000810810710840003d560488010450b80000c103104a220340e22000507080e0a4610b50480050b04070803041c58901c0000d0103083c025010399004440858150112000c04a076520409000c108048082241d2640500d1780c108071619440c803984c4002404003c155500e600203403428002586d05c02007541160750070819540607a003840050007103c860000110f034120780280001076680540580050540d03200e001101c41e84104e6180c0300e84e01c0c0780109407002024003184502c1900c10051100780282650054004251070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 213612958 1250 213611708 213611711
    0x1a03010f060f030e0706031d010e1209041e09030908120703081503060a020912010204050612071103071b14030a0605070c0503070b04261602122b020703050c04 70
    0x2d0911804801030443c002e503001460280000104526a01d038024444403031880c0441d0a41058941095080394907821714441c5580002c8400d8038000340b410010020100014804900f55400f040b04e80e18080b4450321282410342d565000c0bd04160300100200014170541025140190b00018103601c1c0c0e2140f414000c0811842a0001d14030f907018000c03252041c04040c1c1154601e240c0720500500039400803000e41d200740d00210381c00e80422814002c483c1030301e002500e258144804400d088901c850040d0003c01030007a0b00600c040b143c07804101810484c3d0080c943e0b0031034010142202190b0a6080d0131288002e001c100d065041500d000581c0c100e4280d00003000107403030362440d01c2150500d1000c00c0090070747c000001c001040c00608000c01d8015802506020603010944a802464000c204058041c01c50184600b2908124a404101081c2d00143c0105070105207040c0080c103055003061100440b10180c035001a05c04007402e152843c0d01c829000400721141152100c640e2084c5c150502c600c030f203 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 213614208 1250 213612958 213612977
    0x1a040e010e0c070f0c090c020c0103050901020f0403060f140c180103050609070c050106080d05070c0503010506030a030e010c1e0b3904050a0e0118090f03082e1a03010f06 75
    0x19174409202c0148040e05c0104003d03107140e20020b40b0348012010040c0044e007070101080441c2418402ca40c0d104101016242c9030610310f0340d448000e0040e220010629035506d500b0100c88811050860b4400d130050040e041d680c20341800e087c841d4601e0f03e41102c1c10140350104008154451000b410703040703616400d0145900326a8901715003d0409034001c0c2c0003d001c0c50192070722081d000b9029006083c4031b29a90301c0f16684640c181400c8032000c80f400c503410b5100f00c0a0401083c0503000c0d0506100381031612002a0401d5110a1100f104040c446440305054080840901074410421a0080401a1641c85200070f040b82c281c01200340340e201c1c400341d18101c043c139400c2103202403c42d00200400b40105890a9450200300c0c50f070b40c0c09101d91102000c450302c1180d101a664860090156403042d0b044000c8440d81c0c40480d49030000401c00c00c103800040945946100c031001d030141d2205d00118031080f00c241000c1c401000d002c0348000100d820101030005204101c00d106104068455514028014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 213615458 1250 213614208 213614213
    0x15091c0c080310050303040602010c02070503190807051c11010509150c1c090b0105090c0f030f06010c150506130e0309040c051204030201150522020a0203041a040e010e0c070f 77
    0x2030b00e0f0f082d032120358944400240052803980641290000f6941902601c1480e5540d00c141910303903031101900c000380500d0441680020f100000600241d6010f10125140004210105103040c5800409607011503660903031403982860034091135503c008840041d00194002005c400802e480182860144030030125200034408120801200d0014800074240120519820080e15642d02801668000c0110b10001418125031808a4903e000c04255091071940d4548402840010180c1a43d041004880d401004030341905214000d8510303c0c84001114148041002081e001203102c079410385041c006000444500030064510f608010765000c070360041400412180e0f480380c20a80e281c545050b4051000b41a415070001c1c800c03003480f50074a801e1075200c804004140c9100c5190580032800310820021849164028241d0740703000380112030038280c43d051140300e01001142224420700c1c000c5000c01c410381c48918101e00620100030b260010303013880f4203040f0892144000140c1000040020307a803c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 213616708 1250 213615458 213615481
    0x160e0a110909010302040e1207140c030f15070306050306040c0611010b011205100302060715060905040b070c050f0102070321200a090b071415130209090f15091c0c0803 74
    0x465102c100507807991541d80c0d01e841481c6800e0502c0c401d5036031003824040401c8cc100001c50118040070030000380220081e60407004040100244094109600e80000185c5a10f0812105000d00d200c0c4400c2c00d20715091000c0205201c5803a1031809190b810301b01401c256982080c03505644010801001c81c0555413054100c81c1c24180c0e0340000c0d04a040003400409000300c00707941c80d00300030690005000556803514150195041590050904608034011442240c01119410134040c0310b0030070360303040da6055684e0908982000e0419000304205000030890312610520100d07000d485004104150078018602d04414140700e080c108a0880c00034004216900600099009020031004265140b044c0d142888809400c208152403600c120b03c603d03010090500c1c41e140c461440b041c05c0c050045015003c2000700c81c0060980910750040300c0c60103071520f509218000c0c2a500e500d8a0580754200755030018078060902c2440c0039440d090004032200550b100515442598021404585a4507a00285072 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 213617958 1250 213616708 213616723
    0x5011512020c07061701080a080f1b060705071412040e2e0510030504020609101206060206040203060703020322060b0a0e0a060807030f080c160e0a110909010302040e 73
    0x900b0703c100000010b4a5900c060403640f2810328161040035a40e072084500e56654a00e0001048444203001960400545c000909000030b40c5108855403864108515414920180d4488001610010f8110107205601d145100922010030081544541041c0b8090b000d0041d80100307003400e20900041405001c000a00000c1040303140030640305c8089a04480d02c0e803803024440c2c18003c000200398078220602074858244141e4014280b507250201800400c4030704406250b2000074011890b02e030300900a072510501e00507000ca50004c102c6800d0a0040600d03064005150034101030040040207040f100100180c1038015680400b0443e89500346001c0e006400c107140d00310f03000303008001e000400703007010300045006002e004010070000b0345800286e03071030399103500000e0024003c840568002600302e00083c03e07046114000e40c1e000d162240310101d56800c941d405812110064810300240c04a41e00c150040305c07084031a440c0c502604000441c800d94014400a4032031560ec0c0010381c40c2410500074107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 213619208 1250 213617958 213617977
    0x61a0301080a062f0406090e040c03020f01050f040b0a020118030905040504020604030605040605011503060e0c0310030f080702040b0409030c230106081b09060102030414060d0c0507060f0501151202 87
    0x4500c410324400d04d1556604207208031400101d9480001600c0701c0d4010845000e0781e0028116503007a81035400303000030011886005810418200106a0420106006407000e00f00c0b510443d0742e40c00c0c032140028291102c01141e0800c824944500c070001039040190030007161016100850320356100d00020b0083c0c0a07070790002e000141007008000404c101640424142c502441104080c0019014100c0458108e4000c0303044154403203001c503002c0315050000d5907100c0c40b4031060791001c070380b02d54600079500130514048842d114089148811031805000d44260704070284c40410401d00c4588000b0080c8002c640d02401404106402d0081540f81c07440503000500031000038803c507551081600d41d034504000d100031501c011082507201c0e5241441c2a640a01c2d4141e0055041609141e501440c11141000c82da070310500401c0311810085090007200d068002e86c3d218992a06440c1c1803942c203940b00913100f801000d241800500694a811102d20700844940c50003410181c20b6601c000d00911030710452 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 213620458 1250 213619208 213619271
    0xb1204060b01051902010c02070b03371b0305010b0306060d0f1118030709021e0a0e030a03030b12010c090915080703121805031c0210050a061a0301080a06 68
    0x2040320b43c17a015006540d020358190308485c01c49a9402e650040ea0005a07007810440c40062111132480e2034040036885041034003001301c0b92100b080c03100703c01203d0a40e5503a82860411424100e141c0e909807059600500c182c040c001d10f90f18100d0b0010305030f072142c100f161101c2d40d03075944070404c030112a51111090300007440f0f803d5500d082c0c10182c040105054000c19120384240d0501181d0152207000f6281c2c0c917003200b40074400d1030b045003a076504107810010803d0b04100c111420804150307010013411468901035280043c41ca070840b4140045000103441500d01d0741c0c14001e40351507040d0300880e000700301c581c1c050380003440381003034400c000100030580c0c85203e0512a001380401032010001880301280c0c825200c02e254544d00c10000e0003c1c42c02440b5065064104000b0728803007120400107496400701501c190349294401c154400c080301e0056407048030302541c074501484445c1d80c0803241c0c22003140540c40d40c1e056624012030580c0c1ca0404110003007500351503902c079048088001074100780a0684164 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 213621708 1250 213620458 213620497
    0x60509010b0a0f05030106050105090603010e040503131410030b090c0901211a0a140f01030e0312041103010204032a0f0806060102060a0e060a1e02071b0b1204060b0105 74
    0x11a0700380301c03103005007171203546084000141036000341c1c01c40d201c0040140003d03040d6841e1001605840100410656803400100580e100501c0005445005041110010348440d02503034148000d040520010300d061501d0017200201039620820010b45c0059410300c1180d4803504e250041b12148440c1c1e840072030070000300c003400303600c0f68140e00030001c09100b040480c0710744be48900810054a20601c24004141c046c007412180354203001d40050741c0400181804583c15400c3d4600500c1c0d5441098541d00890808080c00100800f0031946c2c81100412002581080c3c1551036007000c041e800c030003245450322110522509844268006001450b407209010341c90795407030810a46441e4210b0312a03005009403000680030034241d100c1ea0b50141d28803002007066540b2145500002c0480038060340d841c1012010200360305c00d040c0002c04030302e03105079031160515108400c403a18180d40707904000304186040c0011041c6101a184440c1d02030f41080000c9035100d003150040e1503900c542108444202040d42 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 213622958 1250 213621708 213621719
    0x40e03031f0e07030b042a020c030106180e07030f0302030d050903180909281a070e01301a0a0e060111011d01050709090506010c060509010b0a 63
    0x103180714030407410003580c1a1012101c080c00781ca155001d0240884052404a90020710a034804410b2900281000821000c02c0e00441c113050103c500e030803840b298200050441d21b6061141c00940345058000784001821701d042403c4441d4200b00030307060190746415a941c081020040000256001003040c0ca4044003400d0080d180e500941072441914240000724a481c01c0000440d1000a0800400d40f05400e2540c01c100d44c0d1500034020222511401121862100010140708410005141a1034052845190a1344110301c40e024201d404446030080210464000100842807642407a1164890303c1190b110745403000c814044c800011650403200c0d00054981d0322003040980c003003603071880c1800c00301304000c03039045c2c02e0140e410fa601114000c510700f5402820007103800078000002045088a1802e010700d460041c1d41194810780d1100c1c240260a81c00004030000f500c8003503402d000d18074005001820181510174000d006039a2140010303e03881c800c0d031041c1072801d402420700900750f5448 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 213624208 1250 213622958 213622963
    0x50703140127050a060207150507083c0603071502100e010e0a0813030b040809010e090c1204081c0606020111091302091f030c0e1c0b060f040e 63
    0x3115076106468940c07440340c0c540016910310031082c5600000400c0603a4040d6100c0c0c02070b400c40d81040f52064030030341d001c1105032400e000701c0c0d100d07040c0d968568100d46445910a140039000040c60b1102c2c4440c25540700051103010a0103a0138051100b49240e1911a080030a20b0001150300c0010180200702d14134007840d602043d4264124020081400a0000d20500908866081c800078606500211800d00051805006041b024000c0e826452410341d07282c486991881c01118125207120001610006660704501c0110340c03103000750f51207206c624001c800c4c030328075100e00001070380100340040014041006043c107d9008207000c000035079555000202c0a4050000b9001c4c1c10055400c0c01550903610490006541c2c5e01103004044541d40350f00c01c5400c01c02075010342e90450308803224980300380740250303500e07540120140550b6000075031350241c083c01420741e9668403029105910342d500313a200b0031b4170000e04214820307000103c0f40415217074100010841c0031f9000d10140c01c90304001e21f0403101c0300003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 213625458 1250 213624208 213624221
    0x60712080906100e0a0c051309020306041d060c18040e03130602010c020c0f0310061d06030a030509091806011502150702030f0d1107150e0111090d0507031401 70
    0x220458106484062050f010300c0810b01075060381011001c009600e107030700c6800200007001503043c801c4c54401100c05c80b00d4015011781000c62030f180c0000034800e56003490b108807107030180000d0b1800b402e81e605952641e29403102134201c05a240000c600007400c00304814010a9400c4000d000700900d480540566841341c00036401e484081d503c1000001c0d1103401030145180c41803680d4060030a04084104200c020440e42108580510a042c005003d070085407260304060700c1d017030560f002032950113a4000d958010041c0010b0180e0020300b00600025080410b503a0700300002c69901d440f517515517a00010620294242106500c07034000001049661144403a8480a065080e200c030b80c240340704100c00c81c0300192060300050348104050180030b504e00d400307000c0340824034001040300145c404403655160020101907800812500d850b00c0c0080e16881000d840b8110300c0000d0140e80c028200181a600529003024001c443c81459803081103014424a0702465210b41c0c1c0c4039842d42000c6c00e607802040c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 213626708 1250 213625458 213625471
    0x30118050f011a13021b01020714030901080f061215150312040306090c08010c0306050f010f08060f0622030201030c050301030b0a11070210031a0409080702060906071208 75
    0xd4241071180c0ca10180615040c0701290300484180744641014030800b8070180d0345811849900b0f110440340c1d04100034102c00c00c03031090f10001d81c440b0418140704101e072050400000c140c1d80700b040b10340e2319a40c0156409a00440310200e85e1070590f200c40c0418040c0d264131803050700c940121000d0647c51110044054041c0091401c100146203e0002307050761f816401044d80135014042c00104000740d0315030081d05055110b19100310500ba591004203094a44c1c40c0c2d6940003085c3c60b04c00501c00c502b0000e500d001c2d090002d10705a9403025015002030004c10000e000c05002d00941d41c114540c03a02c4610803582e10710100c0311081c0b440840c50800c07420440b02d40c00101d000a041480c5015100d115200380d0317041c0e0381c0104000070340f9141c010801005054089150034008010b1080704056601c0350004080300105171000304000c1c0300f500744803590800301c03102644118686a0501e000c40d11003029240302d11780c1500c0882d522010304002038214003903040b0003000814045007404e511981b0900b107602406 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 213627958 1250 213626708 213626713
    0x30b040b0106031a1c0809030a05030306041a1e0a0b04091b0801031208040f0f050a0b0117070303110c0415090e150a051005090702010b0306011202060403031d03011805 74
    0xc04c40300001c021621211049512200c0741040380e0900b0070300e401840c9854072880286250032400004241480c000210a440c1a00f012080020038241401921444031207189019580165000003520074038580c140420810903503654446140c0341c25100c88050b00208107400d8645954070f82c140d002d003000c401d201c0c800b03003503055030001d41038002c1981c141a00d0b4041130140d1442021704044505050081c001c4e94540300e0140e5101c041025000341c0721281d8041c0300a000c0984240c207055180c0541039200042d021031608170a120700e01c1c040340b0a03041d2580740c030788104561034818156241c441103501c0182e1092c91700280d114602d0f450b040010803540094424011100c00c403d1494032194030940c48130300c1d001c0d010002a1140604e83c80355a01900b11241d02001d01c1e195404510200da0032200c450141c0e540b000220010300c0e080121a004108014460a1300c40955011070030310300640c40020140490001c4003948c443c1d180128405000024008005140c1d245100030031107590b181050305c250 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 213629208 1250 213627958 213627971
    0x30210090302070522050103080c1501030503040504151e0816050108060405091509010c14040305030a08090a0515070f0516021c021801030203070e04150f06030b040b010603 76
    0x186000c0c05810956500340c0c01030720f1043c1ca44002c0c421011640110012040381000d040c049035151440303014081c50044022580b60315035000b44038a09421001180000c114110040000420000450707090b1001500d0204512002c0c01e40c0030361143c80c540000b07210400d042d2040801e800e0841e240802c44036650300f00c50040a11a8101c002144e06015550000742100c1c00691582030035045250024203e10469241032080c50313201d01000d0b81030f151034290380d440340210303d083c43d40140100324481000301d18a103428950390b9002c0da00d02c135141411041c0161440020000d0205014201c1d003144c0200c00da0300ca03500f40240035200c141c021645513000c10b8101d00071001091148068440747c01c207060003640c6540e220f03000c01242480490b00c440b80c0d0b130408030b28100140c4400c50940c41c0481c4d602080c000c01c1d41580704040c10811941c0000d00d0801903d01000301103041c00d01d500301039200c030f000c000494080000c442c1d0040c10f4990005001e211030079060204220203049814101c3c2c40c155000c1010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 213630458 1250 213629208 213629233
    0x216050604121404031b120308090c1203090d0203010b0316060305011401020c130b061204060f020f070b040c031406060405071821120f0806040c08180a1704030302 72
    0x2e02c4104090700f21105040c4402d00014142c9240c01145080205080100c56918220b920114240c0d410490020ba00e00092000c03184080048403840c0c0001c0f15510100110b10490b29a6406010919481501601d50480039505c0139445102d4150024082d600c03c40400b080c0c0c0080e1b42c07030a2142e038000a1401000040c500746070500e502a00e2016400f8241d4071141c103040110b400c03200da60042c01c55035540071039690f560300d0354020104509011000007a034a043e060020486c0c28480c4400307a590700400c81155004a603200707c6200c654000b203103425a03280e50400f0344090030b098000500f00c101050041c40c03440c00c00130748544103900032101803000755900e4100312104034203d0301740501d41052650604c440201e0703003041801c60b00f030321041e05801c041c0c40d01d4071500005150799489c04030314608640800117910a495560040081c2c4e41441007440c101c10060264500411040301d46800c0d000300c0741e41110a01a4808043c2c00610101c40005598070480b2180d00501c0110054411290780425 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 213631708 1250 213630458 213630467
    0x140c011701050d030e0402130806010905062110021201030b160207090209010e0303120f01060c0c03020103050c0705010f060f060311030a050403090f090204030303050901022a01021605060412 84
    0x40214a800c190450b407824092104421000304102e080c00b02c8890320764000d031240d101800501d01c100442c4240e007032800405a08080c1c06030000d00d00141003100308400e607107a0650101c082000504258120020110b001d820a5800140d12072000d00000b484072068030260303c0241668040d00c1010342c1522a0010144051100101d140240c3c00001d400c000c00f81c8035501621104406042021341d0b1840180000d0135988840c0920030350044c1c840901040300f80500080f40035142604006410310340589078080c2c24050340c4402030403d40c6501c0010340544d40c1b90152071041ea8004021f01504000400c80e030090040350140d401e100c4200d02e80022014441e020382c0e030744801c000c4e075100c1c0345480704a40b400103450001c01c190248039208000040070744108001000034803003080d00503151811407034002c3c02d9503130182c0006402e0303005200c1d038a1038400c0d8240000340000b81600c000300d4025248000c038064029000c001400d00c00f081070b220180b21000c15190300c12449070300c3c00c880d803c0c00c84c001070f079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 213632958 1250 213631708 213631727
    0x103f150b0d06050a0b0a08151003050307062313050607171308040f0906050a05040c050d0902130c09090f050f04120c0b0c0706060503060108030711040216140c01 71
    0x3030340035006052800104640f54041d50f0040701300a00400c0484107800818140c03007070f036808403a559100f0b0311410341d04080e070090180c202e08a103403000c181501e0343d260b143e5640100c4101a000039038500c034600c04001841c440c440a0644429004403500e004a148204845000015906070042c800002e40043c0702d80040081014090080103458480ca0344401030349644100803282a1003c01c000315220b01030003000f0000b40200e40c1c1c08600175080005000e03200409500440c0141e04000030404e01c04e80001c280d030640d190341c10000440e000c2d0f9000103403d404403c138100003c41c0c500990386925560003800e00f029154031110501400c0c0400c1000c2c0102c132411134407610800c1000d40860000342001091a500d0703022441c000700649060f403104541101d050382c40e40b04c002ca000500300300f040154015400182030860180440e58908049613840b40f16405000304050145803981c4002d41c1c0c3c50341516059241e200300510004280c3c6845810607100400c01c0c5864464034051040c1584610400d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 213634208 1250 213632958 213632981
    0x60609090207080714160803030601050307110c040614041a0307060f0e030d0c031701030b070521070216081c0c03020c190906080105103f15 62
    0xa109a440c140100000b0b400038041210080e4040000801140c0b2848951603141c8204000c2c180c403095440400907090f506521070354070b94105104225443ea080f9068031350041e25810300070000c02d103035001c4604019504d00d810340d0007860404041107082800c50700141691007a50304008a04044182da0708501e80c01c220b0300d5150b0301c944000c0c015203108022070350b411003c03401c2c0440d4600100c00028101a0140207000009444140034000c3c19802903d540b0351030304130499280554119180c407005040f0042030300051000020383c00c100000c1c11031000d02e0300824100c80e00250304200307030001e40b03692485c080380c0c15041003040c0c0403580c07100c08150611000d80f0b80f040c0000384003188900341d443ca00c0c408019070940c040e019050520340c4856115032007510000000c815010b040040000845107560810b80160789442c040080440c0101860403d40e2209007a00c2480d5249500800e10b0240841e14596070200c01c9541105400400c03145502540c852045201c0ba0700c4071000c0401200c0c80840700 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 213635458 1250 213634208 213634217
    0x1230409020d0609080d05010308030703140402010905040e070f031101260a0b06040308070f0303110901090302060906070507090501060f210b060c0f03090a0504060f1a040e0108011e0606 82
    0x480014000e64004c03101907215400d946c0c280000030340900304482d02640182e0300e1750030010400c2046d581c58440c814014100a025060b0b82c04d041e0002010003104c0c0c081d1502581c1e0b0350f400c5420f24901001141e000300000035003c0c000d540c0381d24120400508800c0b107140440c400c07004140d0412559280c50308000301c00c00d20080d0f01da0340c100040c00941243d84a0350f400500401000c00031400721001400514080d84062401544030f03d001000c03554070202902d004401072040c140721b0f83e4001e00b050212078040715410b4480100783e000400307600c1039400c01403442c4507144001990049a8000d18121400d54031006580d50002d501590810800e4107000001d1144080340b9061607150383c40b0b00c12203407000e80340f40d0420304c802c144545050303211986c4d0f284a81c00418050310307a2800400d040045e09060fa821300c245407400e0152418070085026480d03120101007400080303191070606540080c886400009440c1d40e4440d041802004d03080009801c0c0304e0a85007808010340341d0700034202100c400341d0b42e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 213636708 1250 213635458 213635479
    0x801030803161206080303150613060302072d141b010f14160c090614060a053a0b010206060d0c05040906020310080a110909010b090123040902 63
    0x1240d14036a03441040b89024408080d442d034407019418070802e0060440000103607581c2c100704100e040c400003402e00440c45141c0802203951043c025520b80e204565250030096220344880c40c22181a07581001514140d0061000302d030381020880382200030b40e1340186100384602d03004140c200c1d203841d403929030b54400b40a40c1c800b00b000c0c0d510580ca100c10b1036141c6e2070544410310480c1e40c502c4580d0710000b00075800384030030303c600024000403800700d400400d2851020405241b6140d406800b00310000a00c5100d0790002c01c0c0501a40e01450890346103192907454100d450060601c468001e24000c02d0025000380c4034001e50003160300c544109074003240c2c140c000b8507441c0d9880c1c01304600f0045070042211402144100040d882d11303140900c1c070000b4131400c400350300c1c0e260070620310000c91040e51001707000c0d6001a68010228a545546a40030700c400e4a108496a9a814640c0d014080344810182c010300c0b5400002070b81503651845020545018051003a1810780303004020a4401403400a90701444141 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 213637958 1250 213636708 213636721
    0x209060403030804110405160e010302090d0f1b1d091516050409020d0e012d091a070e1009060207230901090e06060901030f020907020309040903030f0c0801030803 72
    0xd42c900d84c4070388904480320003800c001000c40c040d06c200351028031940310b000000c18072503030300002107801c07501d42840c4c214141260302001481d034410810b00a00b411341211000000d00c1030380c2d84400c841c46214418202119a240d080c1c2c500c1029141d840c1c069070410b640450011100070807003001c8003415294403002d07500d03100c11000c41e00301c1c0d0058400510404010006400f00540040c02010102010001d0b1030740b0081d8840b82907a140440c02845045104a541c233080b461a10041c40c813101c08000103042c120610300310483c0780c080025401000040c20400c01c8507540b0841c291040d00041c0c8400245100c1100c058401c16040d008510143c0c102c01030611051050101130200c0107650139070208075803211404104081d400380c00001d1400e840f071301c001c0a10b6404000a030303001141036992950b00d604d1510340c2e14000c507440a0080c4591490400b0a40e4180308100396408030400401c03c101401d2146005001802040302d40800241090090080140140d8401e0704aa400c410b5951540d0b0300d20 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 213639208 1250 213637958 213637967
    0xf03320c0f040f06060206061503041a0a0906060b1e0a020c06071a0405070e010b0f03150103140c0904060902042105160608011809020319020d0206180a09020906040303 74
    0xa81d440c1d0420382c0d4070441c041c030120b14010400103100e540c001c0c140d642010302c184510a200f9407081c0d5280c11040052000213281082101d0090450000c0801c441e292005e068001d85010329002e8100f6042040100301d4410300f1000300000c43c45205080c1500384140e504e40c0307030743c09049201c60152300101100c0e007035418010018106184a14560883c42038a46c040900c03805080d00e0598072617110400901446500c150083e001d454100b95160500794410402005884004e02d1040d080e2064050034066074002d03040803540e2aa42609c000d07003031600310003030303030701130b017007032446c0d9103d1400d280d000541d0080905c22102503410759003035024011ba04e41c1d42c7c0780d081e1030991000c0b07030f1034407a83d81e000c88514020442e400203403070650b2322180c2c1c652604191602400400d2400b03200585000c00e007000580d000624006031282d81d11000402e1100b600000c0c0d050700c10541c01940004000500c00c1c00c0c2c0071189a0040104d4044035034028003501e81f1062801c0b805560f18480c0c014004000510101b4090f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 213640458 1250 213639208 213639229
    0x5060901030b0109050a060f0f090e1522020a170402030a060207081303031e11060609180a060219090609090207020a0503030a09050a050d0305030a0b0a0f03320c 71
    0x6040000f810355403176011820300c9415902480c00100100415070425503c5000c40c0c010214502d821500e190602c5040e0081030070103080055501c0f1106102d00d02522110144c81400c0d01c41158008910b002106102c046c0d8003007040c1c81c0c0040d0715245049814400700c003c07603000d00d801034020078030101141d4880d8001d501c61f02c42035402c036106100c030625148103000f5000155110b41d84030382e200980f0b0030801280480d9891000184911005403000c60f880008203280e001c20704643e08685c40d03c400880c00403c8800c1181585c0500454560106005081e0000c146214080b0589817030200001411545031003507010366000100400010440407403550090b01c1881e00080076645d900d5070b01c5c00003034510b5103d124070f2404111054000c104c0d5183c8441114020300e001d6401a2405a081e07500a12501c0001c001c03c060316a542c4c0200101d4a47d00701a20107000240a8101215200c1c104400c1a141d902400d901401c07505101242100c0303005032201e8445100c0d0000d0400c602c4d284200501c5001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 213641708 1250 213640458 213640481
    0x7031b06020405120102090a050d0809040c0504081905060708090d03020904020405060a080405060c03070c080c24010f080109030512071205100503013b0c04061701150506090103 78
    0x4082c0808152a581c3d0002000c948070710000051755038030128180301d91820340b9070000d40700304560441034010a0400c030449013403000444000a281050341406d694501944d0060b07181ca01c42c0b0788002481039038880e0312002e030600400850b0b607141c4e42d68038200c558140413101440c1e0b581040c03000100e11406500581a0210000c0000d42059283c0d404104190081d11204000031981c8007480248407050240a42000c61402c60711324502d44100064110011000024a041000901c90040300010300101442175802810300503007a03032252080040100030b02a40c2584440c0c1e0800049c2c00d00b05101e00000360368192540c6041101d1040c0ca030721600c000405080601511800d0150000281d2090522804010007080fa0180c101800d2508491400e41d01940402d1001c0d81040c405021007840c0d259260f420040515400c200841c2a040809110764980c00c035041260204003260444c2c0150840c006090080080007104d040900c03621215100e51038000004005021055110f604204040750303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 213642958 1250 213641708 213641711
    0x304020f010804260318010c140d150e0f0a140c030408120405010f0b0105130b0a020a14030405010e030a030f0509031608070911040e07031d0d08010f05010507031b06 73
    0x40c0c8a0120f92542d104945411a07144c00c00400c0001c541219070364000a413000c82d0081203c00b0010201611810603010062059403000c9652000385200e500050080340b800503c15500383c0e0346e1512014292002d903540720801e50300d00002518114540b00b0544840d910a0042070f103525003040d00c0c0340d564170103402030b20b0810042014609030400304850f82d000b14803440c000074408024520b1781044414442c40d145c1044404c0100344825292000440280e40c105140c1a5660300b030020141e16103954508020240d11007083d46080f1280c001c8040d000702c03032003a201c020881e01e0003410544c5520440700000c3c00b1941f10032403010039911580150100441c051700311000100c00380f00c02c2040b0030283d8403c0e00c0d84c1e0310504092002c21480d0080e00d00a402055074103052a040122454503030034010030580406a480c2e240d002d5040e208030f00d41c1c50040d094019158500f103c824020304001d424002c45011261520300080e0a510a40485a0301509607840440c25400b22a6034121881580c01c1a140d19 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 213644208 1250 213642958 213642983
    0x70c031209060c09090f020901120e030c15040c0e010e040b061c050102030a1107020a09092d02040e0c03030703031d011118030109020904082812050a020304020f010804 74
    0xda0382d0b102c0d00101c2402d40c0c45181c641460007407214280c4e0890810111060300500c41140c051340c216000c0310038240740c5040421425242540030740756014800181009200b080207002d141c9a00500841c052405a500c2000c1c00c2d84814a44000b01001c0c0f0800104800c082d00040101d1455449e0a030495401402c3e00141104000c0d500c904111102090751070781d5002003484201d48261285495040d10701d0030f454180401e507000621a03207290701c5100e40040d10b9103080010000d0711007860841904807c0b801c0107075080000305901c8040b401c130040f4005d0349400084000c004000030b80c0c18000344010021447d06044c0d5604502a0000c2215403402c2e0600300004c0e440b854003030250000e14161366091b05d40702c504100c0440c031042000c8031041e0090345030030426409603c544a805500980249490341c0d20418041c1a181c04038109150b07440d50003500a038400d40b1075204000c80240742ca80729040c00360b901d86049a20886c4026074009500501140c00021254010b825840c3e000340611425800c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 213645458 1250 213644208 213644213
    0x506130501051803062d070f0c0303060b0a050705010e012702030f010504060b090c160b06120708010e101103130f06150e090609070e0c04050d0503031806070c031209 73
    0x4011055070761a0786405240721b44a60000041c0135130003d0425201100807500740f82d1070250000c030a80c0c2c004000c01c01c4089400c020b041c040c0d007001004020110b6407541c2c4e90b201d51401007042c1c00c1624110303115404c0040921042c50140038049e1b000b070710417002003211440032418440400c0c4001381240c040c01b48a9000300704640a01c6094030441c000c500200d110010b00d010404100001048818400380900400c40c030a0400a0050481940141c180c8403d4854000168480d0b95881c6140e120703105080021030b0007501904201c0c8000e0f52041194480441180700301706940e40ca400c200c914260a000050f000110100c640801a00400b0700c0313032a403101070b01d4504c1565840d40d400890760140100400082d1024100345034070003803040141c80642081042291a02ca0510030501880d11400c082807902e8040c41c00c40b4000d142c0104040d41190040c03802c16280e41013180c15101d941040340c00a0700c5844041007441c070510266484007030b8000d05a405403110340000301503485150741c0d034888400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 213646708 1250 213645458 213645463
    0xa0b040e12070512040e130204061502150109021e0a0e0901140102190228090905010e010f0209011b0303021603050316030e0a02010c1a0f0703060506130501051803 72
    0x9001180440e40c1e41e0461403c04500d040d0600388003d040d01030411040190441911036950800800314901e100d0503110b00001e800750151790018941080860049000030f900043e80c500c10030b00302d216080300c90f0303a140b441104a006480340031209142c130030142410b02c400301c8010840c14000781085000c00d0301d070700c010855100003608514926640700c0010711866804000c070070f15001000b00103400c20480755021411130714403032240200b40c030001e4022020418141442c2030103000500b00c00c020280980c102140603040b50614012154601400744c2000d410500072112748250684866002001c80e205045078948030b098103804040d07003403100c1c40c0c00400303030f04030844103d0084d0346090300d0f8184580e00c0240a02c8140d05002458030f4034000010000000c1400300d88650242032103103d80459040c600388603003040204c2d03019620303464100984c040300b16040074080c141c155070400c005621003040c400c181c890a8501e00e0103da81644c00c0046610480040c2341d80c04949072880021496240401d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 213647958 1250 213646708 213646723
    0xf0a090210173715150201050f040201120504020d0503130e0906060a170a02030706030608010b040504261201080d170403200309120106062606271303120c080a0b040e 73
    0x41705110620200c01d055424007443d904000b1a0300b011080d4105035001820b4210000070741e840c45078071140040d05540d13030300080c10f1100d0b0f0000e06072641d900700082200454101d5004a030100134021001c02d80d50400050700c90f104036400b42c034202d489401c1100c201c44460300030401005a1042e2000319006807014011400145540d450201c0d5660910080d41e080d107412042c01c1d40202d01c0c0408100100e1000703250382045c0d800b91428802c82244901c400900b62003142011964001c800c1c00004101500080702c0180d03201640e11814203680c0a400c03d03c0e08507003542c028001415851441700c9403000309821301503144803031003200d2500c20701c50046a0b180084a01031041c503556000c0400c095034020b0844c600340701900c1c088a0024180304441d91805a010f89650b02800c0d008101451102494039800e5490310301001011075450074080c08507110560150880025051103240c0304104024040c0c243c0c0c0504944a02d1079903a104d6010800605001940c10343c8030f501c0d03070702c01c06180d48240302c0c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 213649208 1250 213647958 213647969
    0xa0206071b030c2103090501050f040e011e0501050a0c11060c0a030e120c031f020c0a0807061104120b0702032b0b0111060f0a090210173715 62
    0x101a0302d880c1054042c0e04903020000b00e50180c0300001c0100021b580f049002043d0303002403d0254459008500c0a00035000343d8000e51101585240041082402c40b4850248402550300300100181c940d001100c050040400c00d8010440c011424400109203410001d02c8120240840c1e04081d8924841460300d031100c0d07010740204054081101082c20a902b11000d6400e0503070041000940740d0002c6940d03110000f1028000201c4488103100e6800960100d031581602c0204030b0b0b031090420b00b4100603e510021044460350310700711800201c0c000110a40f001c54008000c510058201a11524440300e0014034050440c04108a50f01c003140e5152203001c0405100b6030004210002c070070211045440380c14002d41070011341082d0011010300043e6440c1c2c80209052040d859440b5800d000c03004d01254032009600410081165000c6c0744c0c0229005040b0408001e40c8140d501c0e0403d040c4c0c3d1060100e01910b501c0c0084612898054518280c40e0b021503d100a0000f00c03000030388040e00c0d0301007860b000b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 213650458 1250 213649208 213649223
    0x15031501020307230f061003060e0c0325050a03020a050d050109050303090c03070905090c011b0602040311011b0b13030e031c180503030415050702031e010e0705030a0206071b03 78
    0x400310240420840400001e0151000f450701303047c10090401440642d200042c40d16031950380001849400740b140038042040a01103c0320a184d5048000616031448007000454588100010b224544003403084100c1c1e070007030417680e2218202800c1c4003234034000e40e50030740f010b43d240c2c0e28240000380c0400041d032140002c1000b0b4209240303464200760070040968001580c040c01c0c507080c0080140d020450307242190090070450901c841c2503c042078061600324024007078500c00b14000007405505a13581403842002d0b82c480420001c0321581c80c007142182040581403102c2e1b03000003a9420800550305007510300030b003414000000c44100280c42c10720f040c07a010041e585039496a130721440d00b0520f940100039083e000000500c2c105804a5902c2c000c80c460820700c0403915a0001d0b11a024000302c688668001e0f050f56180a428840107080d040021100105907107440e21000104500ac10390317405403a03000300904100b450503020015241c0040901780d03500b40401100101d142014001c0c8801140306025 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 213651708 1250 213650458 213650513
    0x11803060f0605030f15062409100c050a03033c18120507150c020d091d060d081303050114070806060a0c1e0503130515031501020307 59
    0x24002625190ba120074041d40c0101a00541045d000c0b4400200003170001e25031031641e41c0c160015503481a0711301140341608100244850060f808401441c1c1071030241e40520082d0000c150855a02c01515009065070300002601da001901c07e8000c0c1c0b91482d48100000322851b030451340d410440f0107005030840c44000e407151004200360540140c5040424903201803012a14589504001c400e0300c0710007000700301000542c4000c0000844000c201e0f1041c001c02001600803140b000381d50b400c050841540810110200025980955802c60403031400810704030480d626010309008075441030900071550b503001400286800d4070600555001540102c0000c80c202900c50300181d400d00000d00200108225203080003010f45840044644401c10ba00d00302d01e011a49003041c0303554070845021944c080f00c054400d0010700070000041c202d5019910108003100c1d43d50410800aa914001110b03449030b0140009106180d00c2440c1001050381030041d0fa00d00398469807096011902d00c604840814407208 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 213652958 1250 213651708 213651731
    0x27100c021c080103170901030f050103120e0613060c02030a061b0905030303010302060a0c0201121e2406050d0f11070b1e150102010908040e07110c0a0b0901180306 72
    0x100e40320101032490070b001096504644524013400300081201080d02000201c44409074801c3e030000f80c07070f1401900704100a5031640390040305510781100080c0007a580907511038581c80d0000c100d4802d1050203a413a440c1300d10f00700c415070302c10326926001c0c2d0f4140030f000c03020000309440d401500e480000e0180341c0a0034001602000d802264160401e13030184c1d005000500041c0c840d001101d0042d0840d080030301e036400a920048078280d000007045200340d8105803010b452180c90000141118100e6001440740c1e40c14030000c41001441440018587d001c5280200702540c05030f00105100030f1a1035020400c51351905c0107109440324540d485094840c00614201031207140c810030798202e42d8048258122401d2a12a00c2010101410b1144031304507954800b49282c4c000d62003045e04a5007d01c0554840340c1c4c800010000ea0012220400800c03102a845819500c001c00e01c496131180080030043e5035070410010f02e00c0c40e0080c80400c0d043c405149007501950b00c01c490080000e511032900403d5103840d19 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 213654208 1250 213652958 213652993
    0x40e0703051801020a090902030a090501110a022514031002030907031a10051903140c011106040b0f0403030b061803010c031a1509090f040c050927100c02 68
    0xc1d903010042c0d074030511040c650340d0b40c1709030700e981112807400002d6240d072140d10303000c0003c0c044550b00070840e620f4600d01d15a8452440040c0102500d16000c0d134000454001a8034010181081c413601d00031038108040c480756298124000981c0c4003c0e0488410300300046141080383d10a4802c804150b00030a4100200881c1c0e0403042c580c0100050141203500303010a41b0704500c031090244a11507007030040303a90031b00d0302c010003909c0040d500100f280600310603410f03805440b800213442c1d00c0c0c001040030140b03184400c0c0c00103040e4040c42d4081c100c05216a903503021540301c000040c1007101050744aa1440c3c00ea96142e00c058101101004400101d510703185042600f1601110084010b050505107200c1071070203050000c0c0b20400c410f544507190100c07403c45005013441070038003050780914bc60742849400302401c00c03500d200d1441640380039011500e440402081c03100032105c0119510201060400a00f1401300341c1e907062080c40d08035510010075a10840569146240c03400041c0c1c030411005003504d000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 213655458 1250 213654208 213654241
    0x40f050c011115190603060f0f0605011b030e0a0b030a0c0e221b1106010b0306060313050f07090905100903090b130f09020a2c040e03040e070305 64
    0x90070200c2001034002d6100ea10342c442406042507004071600003445103880d013411034039510100c070402c01543d601c91400c0310042c60040c0b495802c503483c01600c5018013040d8801d1006584058641c200c03001110000617a03000580c980480800c115020640515100c1c9824003000e829003920880d26840c00381c00c0f41c000c4603000d9070a07004020360f44005442d41e448610b40001c030414408001599503c0348a1000023034040201000714800c0700d11002d4044aa01242e10045d0044110a6600a9076500002d852600058034440e6000d501000032548010601d129030a00c6486401514607410140d0042401c0030990f521640c2036548400d080800c0150500602d09200442002001010f15940b0010080d00e00380c050010034400008401040d080d40c0c100c00401031041103100300140b03495100d0003000c4c0d0000c81030080445c500c0d0030a01c3c54030005140d13220f054010144031440c40b0207503400b000042c001041c060b0000f80020400070591000c90711207588901200c1d200821b031428050001e01100e80c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 213656708 1250 213655458 213655483
    0x715050c030a120b19060c050a050601061e020303070509010e03011806050a0c080c0301030204090c08010509010c0e0409021f0c08030f07020f07030804090203071e0908070506090904060504061103040f05 89
    0x12083c140c1e0f8160300000d103100a4507002d190903e0720114928001d0b00c1d02c229040058010711604d0b000040d8dc80d400041314080301b1420041d9584030050720350980c0e50740410f58007800803a005000d1001194804c00365035900e100014001b00d800352140500000d00c2c907841000303139001d80c0c0318410001c0740c500500801510100e2850b10904600c0c140b2020070041c00103010003849251180c065501307100c401c8421001800c10b40d0020001410000d00701c5000700b0138071041401088107054180b02074039151040301011030300a4081403600049401c0c01ea03070302d9825070652091001c413102c2d10020130f03418000345129121301c00b040c0d401401c015102a00e814440a03e00c1c01d07680c0310103820320004d503031203054808031028a000584c030b9458500042e10f802130301781d0203046a24101400c0b501459402158881101c110005464550740c4500600481d4890b42451a410024400110703001654030b510842e4040d00840c030000e5007007880f00c00c244440d070054800f40c40030488415a4003c0c44824000c0d01a00d84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 213657958 1250 213656708 213656719
    0xd090312051320030a1e1b050d06150812090a0e010308160c0b03092d0c1c080c030c010c0f0807110c37080715050c030a120b 55
    0x103860b66800e8108441c14460b80e0204600c050600f2154400f040300345200781d404000c50485406010701d242c0c82019824007036400148030700300d00a180104440060550303001030505042d49070b55440301c1c4082c0000b4808044a08040c0d1400190641c040c000c00d00482000360301d050317880780001d04000c10030700c0c039410038054101e84074010030000d442c14040714194159829000020030303c6040c80038003103030150303c0020840d00000800c00917803000b0170744128805010006913268880221440342080246c64042d001e03500c42c4003000d1071880c1445903400e4402944e03074a02880081a5240442070704903606d151003641c400328900b407080e030003070041c001c807143c1c9403400c00034405000c00001c0100502402800501c20040c040031000f40c018800c040d0142005840c01221820700710108178032500544422011146114090054115854625080700e1081c3e0060034094105a0000e50300382c0d1381c01700001813040821015903804000c3c005020b0001058480070480e05007044100151071800909610a0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 213659208 1250 213657958 213657991
    0x30080f04091b0203030117071d0f09010e0309060f04050a060309050d08102705161d0a14190306020307120b0d0605090c0303041e05010518150d09031205 67
    0x60f070020640c1e0444103101601c011446204048a00380106504240c24050943c0c00042c860b88018821500640745120500003560314480c4203400c0300c46500c4c03007a010703030000c0001e0181071901c48054549038090300c4105181c80e54400010b44081150303884440400e44400000c0e0520005202ca526920203600306000d440c58004148a2a016607010311030003a41045100381d030f00c0e205480003000b00c41e9080e804004900704500141d40001e0100750007000515500c0021a1408182c200c214a1403409130070091144d052291040a06001100c019080a8801c0c1c81c0365440200e01c00c224021030082c00e00503601c1c01c2c00c50008100203015904c4526043c20032403410030b51f0b203c05070740308809500a8000074050300d072055074505107442185c403690701d0700c808a8040740101c0d1008082c00c01051a0115410850740da00040d6214002c40050200c100142c0140561a0800300030340003d800d00305054a180544e001101411901c01c5481540041e140680c41f000030240b41c41061341044250f1040c5107007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 213660458 1250 213659208 213659261
    0x306011d0f0f040f080f03040309170d080c07050109080307050307021218090406150b04050a0512190203030702060c010f0b031b01140d050f0f0f0130080f0409 70
    0x400b400680010691044103800d80103000c00d03407040e00c10b80c1d4081c2030361650b00c1c101420018200c0b500c5000f005032245e200358a501d01c9020004403581c600010792103420540d52080301c0812103400019040da4a9501c0d407100038006601b44005520411058903081d03100e0605400c001d2034178051421100310325004015a82c0c0b00750034018080103800044803039480750b41e202e18028004d080a83c0171081480700011000c1001821f410150043d00e40030b0b80d900802d550344208105140c480c1d14200a04e40e08002240b2441c039a800c50429103250000d0300712494240980d010400320717400340604520716595488041080210703409180d01d5810220010404884040340d416514038510b2011030500c07141d200c0402035814000e0581e424100e0181081125142940c0c0c0d0540d2041d08450203c4000707010f00014260700c07414018a4140c03516021032241c1002d10031418a80c2ca0079401c50144005800c0f480b0301c0000d0340c5a070042165405006543c2d4450f4504804001521059284403e4041c01482400f41 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 213661708 1250 213660458 213660481
    0x3030b012307051f0e2a0603100e0709170a0201050d0c120f06030b0a05040804181428051b0a1205010f061202070507060806040b0306011d0f 62
    0x400059941c5aa540e41d52a29010340707072a010b05100318142030645030300ca2801308640c1c800e100c4200440295021141220030101c44015049500d200008449824482c541032010185a0045101008407800c503155840d4a0340ca07601243c1d5400000d041620a112102c400350030403003a100d42d10001d03c03402d40240d001a0a0780600009080c81c1c5580e184541c0c2c40301d210303095165400881c444100100103280342104050415804207485c601a240301103a40000b440c81400e104075007142080d81010b04040f04056481ca40411074900c41d030310780f0000400b10484280650085991500c24150481c503140b05aa150100060300c40a40e882e001c100410045100e6101070307ca00d05e0b0022507030b6805009010365070035401c3c00c82010140d103408004520307580f030100d1540544010382c407580d0b10340000050b07090681c415402c00a19a400c22002040018095441c00740c02070001000860b0316a060030100e86002c001341d00c050303503081c00b005810388840e40120301c840e080b052000c480f159605d00284200e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 213662958 1250 213661708 213661757
    0x711060306040b0d080a170115030209040204030803090d020f011515050408060c090103180f0b040201030b0d0303050402120a0201020d05221806090204150305090109020d0302060403030b01 83
    0x60085000000107100c980e2640e01c202c0c0040802441c00424215609148449402c0065840040b407910740e0116480520041003a0482c0c0c07601c0340217014a44054422006504003200d07141e08581c082c0000320000f664400a140f04031502c200034645050305920080ca0807604c003c0706104d6074035000c120000003012900040c241d482e20385005105010641d000c45043c4641d51001e01c1d50701414080c41500a10301008190044003641c00307101d07010842203684401f2440020040c503140300c3c0c00441d4000f0340b25031100e80d030081c0141000030710006c000c804601e11008504040300040d94840402c41145000d5000c1118203402000904025030b0588c0080c2d03481e411490b401c1c05000300031900000c0c200c507035010070510440c2065580d1901e0303a6100301c154940400c0d50a0310600b4140f40c3c1c00324035102d61f03100307543c1200c0a031107c1c0030041f44002002d400804c8041c04034961952100f401d41d0140e1510b04a41c1a641d109900078821464242030040803140524821410041d8000f049800f04102100380b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 213664208 1250 213662958 213662993
    0x606030b0a03020922080d050601050a05041e0906060c0501140c09090901020d0204061718060c0a05040306180c0b07030c1202030910050d06080705060301060c051f06150507 76
    0xa0b8407505c40410041130036001c265060168810a441c0701c04200485001d0041e1100d0900144455103884006451078007803050304400081040c00100413000380380f5240302d12442224210441d1540700e00600c816503c480d00319001044001018200b041800d2017801040b2410704034101490516403101d980520609841510401019012410344002941150800034182c1c1c0119500e1340e48820240c460340503a00b0203152040b400001a0401c000600010035010302d44010702110754030802c203041d80d40c001903510401c0060600002c800551503100d0b0103862210038200c41196109450108816400c540065005140038800200065044150382c02c089a11046008245200410480c654040d20140c940c0c030440d4a41100c42080d0803400610001d1400401071000c2500c480810741d9604407403041680201c010001040030601c1107103500291485070094600711840da0b17030340d440e04020790018030300c1d8265072714000c01c222a02e4048011205200d801d1143c00c0c5805c03500e030a4001c2700050722a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 213665458 1250 213664208 213664219
    0x14040308120705041e060e0409030c1b0306060b0408060601091d0c191106160914041d071503050f150f0604120507060905030a06020c150106030f0606030b0a0302 71
    0xc00d03002da002d4020b40d0003070900d032402c444519880416000f0300841c21b20981000c44e141d50040e181c6e40c1000d024000790560141c907081c00001955a0b118002c80e590b44009403808140b44c0701000007441e0b401a00d0081c000c10680d60344403810041294100500038141c941880400c0008000701080c11945000c00340c0e5103034240844e66140202c0d0769007131044d4130079580d1400916148940103078004203a07800025520040710131558488041c0641494a48002000305103481020000012200013104560202600104000c3c01c40310115100b503805441030900c7d81c0180c88d09118046031200302c08800011450280910f080680001c10000f8002e00b000c100c0d5a40220440700e283c039082c55001d14000068a1990740d10782d110800c014200fa010400c5035103008480c0700188881c4246140015100c0003405401518881e5540c0d40095000011060305400b440200b80480080a08014001c00c3c0640380441c2088081004008441150300002d040c5072920b80307101c00c1d94554041c50401c0d03940c140c60 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 213666708 1250 213665458 213665461
    0x5060a02101503053c06070e0a1404021605071d07081e060409050f070e011205060106260103030903050607030509030d0b0112090c03140601030b04060f0b030a0c061404030812 77
    0x86040745242d030500d030301d941d40700000305c1d008104002a420b01ca0340c465510038940aa0803010444145124480c0150100020503200c4492520364010b10b00071100d400c4911000d0f005507a00c9007443c0c50b9170310600030100c00c01d2403056101d20500300d41380e1041051030070440b9440d200c0b115010f0040b85541c9000c5003031660000914944a42d40711440444d006801c982e007900c070b00342c881659064180a0308a044840034000551080c1c194541c901c540c0d03002c4094000340c2e09040040303c41c1aa21a20403020441481150428411188509000c0d50282c0c1c0d8215009046051503841c05001902c0c10080601d00f404000c032900001c020b90f040c0f078502640c0407409500d21801244d01000c1c4c4c9206483c0585402241420000c2080d41c00044078130451402401e48100441c0a448403003d11001d054a08041d0000700056980d42c80b03c44c04004a0710000741507121040402c2c80c001c1600022a01160004d5007440066000018440028007584090f450a411a81c401c03005001d0800c1d030a01d129084d20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 213667958 1250 213666708 213666763
    0x2030a03030c1206031101020d02120306060306220f110a08040b180613020a060f02060708040c080316030305060406051f030e0a0503120f06091f05060a0210150305 72
    0x244600b074080f0024481c1d00c1d242d00f0081d600c11841c041d641d000d44150042c2040740c81c00410404680d0541d07800060666444000703000f87d0354001001140d0215184441c4070410034554500e01051181010020754414240403250858046041e05850a41c0c01d100c41390714103a0000c8070350b51081e8030190520443d02e510503240d8115540e0080c2007401e004140c20001580b41d200000c110450007203c60800b070664030202a60725a0340049540f005070040c10005120341c0c01000896041445540b1038044186d4030110a400c582004510106400d01a0440403e05905000e0f2607046001143d0800400d0328140c00910140d50718150040364203003220107526494001d91140c03403940e0001c01903481c40e95140c03404039129030140c110f490340326481401003401d54100c035907031920420000e00041d026854403455040d054503841c04240c030380d905400c800310303e07902c5010140101c1da51503001042d00c034000803e4002610346c0312680980c3c802c205142000419400100030b030b000d51a00720260314900c1d045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 213669064 1106 213667958 213667967
    0x5060f0d0b01061d120604060e06090d11070512060a0c0906080408070c0b0a030e0c120d080901060806160e100e011d04090602030412050702030a03030c 67
    0x900041c05020302444034446a05445440200440b05040004031031713219210306403c0c01d030000720512040100078040c41d1308010700600030341400d1034000d006640e00c2c0419243d4104004400784032a003e1803092040b0b00181401400d1040002085c04106c3c0c0d030340d001600d00ca1001481c00f18a940c02c01e12800c07650301616504c0ea074955080d1036a49070300d05075400c200419280301c8229000002d0b17100881008100301030040e01e001c51319100c0d8100b01b5082c521054442401410844503041c0d40c079101090030210548582040302d01030320b03405411801056a5044250305101c4c403000d00030109070141b040003021000f07a88200d03009a803a424400b0b1512540c150001285d242048080c543d8000d212020410441141c61481c0d041c49800003804e64028010030f4074410790005c2400b0030702c9001941000606240d05040e403405c009503011954500e09014007800f019512901d100070507124 = true := by decide +kernel

theorem cover : BRFrame.Cov 213489208 213669064 := by
  have h0 := BRFrame.cov_init 213489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 213489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 213489208 ≤ n) (h2 : n < 213669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
