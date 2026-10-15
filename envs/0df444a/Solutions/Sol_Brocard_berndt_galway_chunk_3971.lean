-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3971
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:12:03.597039+00:00
-- url     : https://prove2.me/submissions/3027adc7-2c8f-4c1f-bad5-fa25ce6d1579

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 714028776 ≤ n < 714208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 714030026 1250 714028776 714028787
    0xb07050301140f0310091e03050901030b0d030207170c0307090606090b0a0c1203180c03021203040303020a08091f0e0103050a061413110c0c0a0602161811120601 71
    0x2080e1007070f80c80c2c0079180c60f803000094448410310488220166561840001c3c46080c4a004800c1144d04a4400d1000f4050070020065844015140d0219052440710300e00360034500400b540d071036019030107400301500700910298589002803082409100301e0008003030b550f80500c1107500601c0701d00c0000036601c3c5809000352036a400e035845060007520034007800791010f400c100000d0686900455000c1c16915556040d1300401d01c101d2070190340d040c01010703c4100703c1740b400d000040e00e00803108501a46000300c100f90790703481280402401a0804544207000801070000381c05107603c020030750b8121440455015074600440d0483c000014983c8040020f00d50309480b4850300b140c1005030600c255810000d2407814038404003c100d01a52707181071003030f0f03c0075040e40c0402c150017a0380d0301071603032402d010342401d642e6180045c40381e101d4443c41000041c41c0b400000c01c64007511225407180e084515000200d585260b441c107549146075120b420aa030b00603c0a40101550319074840c0c02d07402801e005000508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 714031276 1250 714030026 714030059
    0xa0e1204170c090c0702010311041d010e0106020d12061d0a0606032a02010603082703060f070c1703040c060336080c160302031c1b050a0b07050301 65
    0x8180c1010b881c14101d511441d10565000d0390341544a503940c4140d01c01280101a03a990002d4005004a404101c203820703000740d9150b100d1184d4070903889980703070240c400f8508020f11a920141c1e00000014014a028040030f6403203d40e00000050925580d1032846001c7c018980c82c41d0500307a140c0c04000083c010b03403180c0005001c10703180802c400010030071440c1c59101b9800b074012548030071f101441e40d024400d42015014503404030130705490384600da402c001d03503d01e800043d1641590700c1200310700a003030005403984510640c0000c0e0352227031198801952030751064501510800510440c203140450a00000c601a52080b64403600161900344024125000d26400c1d0304220b401d200d0701c000010074882e5510100e1410740c00c407c100c000c2e5141515881c419451810a00d01400d001310403c0b0240444c1e41044900a0307040d21070948010f202d0380141d802050f03082c00880d142a0401e03484140400c00309500038460341c100ca44450058848d41d00702c0800325803200000c4d1001005010b1004803502456 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 714032526 1250 714031276 714031319
    0x30607020c0f01030e030d0c020d020f0624011106070203280f0e0604030c09061e2711030a1b210203070c020a0303020610051e090a0e1204 61
    0xd800844100203140b20003640c0a480c101512400b0407001176038103104485211104600421203a10325a4000c2d4542d140e200c3c0c060050700030381c40c1c80d101c441004614640315000310b400c4e1040054a1030441003202c48500c207141c0c10030042880074043c00030300300021030040009800940c0c1780c00b501c0b6100242c0c0f25021100820356104022510140744d0410a03141407900c09041c40d00010203050003044132400340340e0016121445401002400e164150b0205003070710258081c140f601c4041c80410f0410b44a2417080a040e10f001c107265001920035542c0c8105900d001c140c011604020b441c601c0031030703034206458800d0219a9034581305a580e44145200d007800c403540c1880382c1590034901c0a618041c44201c0104c96180d000000130744602c0c03080f4498441554000c2010000380c4c0c1345d080096450100b1102d4035426084030401150034540b540c210081d50b46881c4c0013248100035401405071300070001e080400d03001e4454000c901a244c0900c4075009491015404545079440d00c001c83c1c00c540c04000818 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 714033776 1250 714032526 714032533
    0x50a030801150e22110a030501080f07051e19030b0708060f0307060809030705011103070e0d0819090810020a080f1b030c13060503060111012c031b0c03060702 70
    0x4183c00e44903030103944158040340c0d004255240f0400004400381403507a1004400001c0000c14507001d030b800d80c1c060750681c1da03250304440101048042c0585da400082c010b0075030080309420708841500350040d8000c05450050402170f03c440d03024118101c6641c1ca40c00441d40f0103d0041049202c07984210300c2e0340d018900700c0d100c0b40310840340800b083d16504c8038003a41d820010f002000802d5110200308075010b5541c0240200000140a200140f0b10341083d02e45100040420881c2d030420703d030035103014039101d4001603058a00603603c2e10207030094110084203020301022403000104203800340455149010204005030355400c10220080c0307403200007807802a1007070042c2d09100b40006010708403e102403134400030503625103554010603407600070031221845c00e00070680302060031130f0300c600a0740c000d4400b84c1311021500090301c4400e090327410002c0c00e907815410000708017922280c030b42443d0718145101d0341038074600002d040e201c800050507259011072a51004801c0000f60604001e43e40d800102480038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 714035026 1250 714033776 714033797
    0x402072109030c0513020906070302060126121602220c030908070807080708040815060102150a050709030510023006190e180106090b0312070c03050a03080115 70
    0x348401c0700c895000b41385c000d07000c0701d80c801101e440d298115a03444100a2a480c0c460503185402136a8640034001c0c6080c01b030300d440b1241003191040031440c000000c644040c08019904507c40042c07034001400032018051043e984d1805622a0000c229841d40c024048481103015000002e05a9001456000426207020b20340c0010400d00002c0c1d440c0d80340c0c007031051543d5000c4d50400902c0c41c00b410340003401c08900080c002503c41c03400241c4c0f0003911403a01504226645a100684e01c8030040c481508070350600380d001965903410750f80403c4e40400380313062840031030b6200d4581c2c03450420000c0c00654510b50016000c804a02c407040084c48030801045200e03001e00a0201e9100080c2016040c14091020f18440c6800b100184a4045c05440c1c2844481d807186480c80c4600000480003444120b55442e051000c0761405444c0160007000c50050014a0403407004113015996501182091341d07540069000400001c0b401e1025400c4540240c1d500d81c8194103021640c26551520190b2500f0320174000c20 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 714036276 1250 714035026 714035033
    0x21e030f07060203040215120f180d032a090f050d120305060f0d032303060a0612090b09060a060b1312051e010c0201060e070512070e040207210903 65
    0x1c8615035580100e015880ba2075900c081088200355a10150340441d0115480054004402407a0b2140d50300000f901410b844001c0c80300e4268030344c0320a00f40d6640200c000d1080b0380e402a0041d000d18001c0914003a42d10b0001948400c40c101162504800140e420604002a001c803071800f0004c0c7c54200c1d24a006c0d4001e0f5070f41c2c01da014244074083e00030301d501c5400094031603584402e44580000064146050400c0390f00c2c00401050542c0642d030980c2c1c004200004034404140e054a200350409085100b07054200b403c1520719040110b07029006903295622200054800800070780030f2004603000340214142211482c1c00e41d06d203034024054003070b4144a000010300324503070f0344800c82e0507001901c4442c41660902500341aa500200381050418107180700038500c0540c420000d03060664002c20956403038529400c0d0905041d614200020028061070b030001001e8034240380c0045083c140800c0f010920000700b410780c0c02c143c0f01034450700800c02880c82400c0c4180480703998120745141c001b00c400c0c115038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 714037526 1250 714036276 714036307
    0xc1209010c0b090f03040f050306072a0212031305011e0914040b09070e0a051c08090d0c06020a0204111603050a0315090e01060501170604180b07021e03 67
    0x1400b07801030718031101191a920041c868010000141c07415655205c0e01c6404c4040b00126500c94540648145c0c00010901440713090441094034041148103041c4280f55559038103107140c1d81e4141ea1040c114104004005000c2005159060710392881d01020381c1341c40005410901510764000103111841c15400c21194444108401c3e075420f8040c450b000c40140e000b06d4002c1192081c0d141d00610068180010340b50042581991408200c801c070005580b10410b2202c0000400c558403d400061036000c0001007400d005403c42c1c2c00050080c4c800300e0215220b040d950503e03a80100007580101c0c40c06815400c0c680500c81c00c24807042061882c00c01065920040d1301444440901001b00c0454080c0e022882504017420032801110302c0318010751500d2885004061540e200c10640d842d2600000340c6500071448603904214020141c042c0e6560f14090101a018000900c0c04620702e5000c2e034800186070011203402040076a005220041304a0001d1344440d44a402808290b80248648140b10a03020b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 714038776 1250 714037526 714037547
    0xb070c0302070e07170a050a0b01030c050306060a0c0f0b070201140609060121020f030613050c03041509061b09051507060e0f010203160318020904060c090512030c120901 75
    0x24450307000b8661381d114049482d440034140030220740d08004144444502e0b5900300d24029804030400b0850361084c0070040d0101c41400c4040c40c00b00340c091001030304524000f0081d00c043c1d011070620000c070242d1681c458243c95003802040390b1740303c00181444071a950911903002502860143c1c12014102071002495844c0d000341402d04214200242004030754003013464074900709421106644800e03020703801e0b00c0550401c440311402084042c0b1808080300749400340d180148440800c0524544564513940ea0303440501c0704200d089074540e855880012a14401c14000d8030050348285104004500700034440d0440798440c80c840c16201c0d2100101420300360403034401c1907100c540041d09402c08a40282400c8000b0360f08040c03544080b08020700403c11807a81c0604200d00e960800c1070058810001041c9910404040d4210241000180001c0c9c01135108000c0100325060128001ea601d000003041040004001c0e4015003000c1102000f5203010015101003017010401d0600b8200520002040135105c3c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 714040026 1250 714038776 714038789
    0x50604030c030b180706170c04300816110a05030304061b0b0f01290910120606031a04060302030c010302070f0f050102031008012903100212040b070c030207 69
    0x580400d000c400c5102c00861804010421740790342030340e5010040c140140303601c211498800000001005034624404640984d06003920140f05421150500c440160144801c070300c94059100300d41003c941c18074050f00480c802d40e5200c07440304000385400c0402007280c030b01e81401085030030024040c0307640c0803043d242079403060320784448015401801050141c00740030300608000c1420742030103c160209400241a5007498100d004280f050008414407940d420011001801c02400604024a0492400d240200d0f4501c0d0581c0c030403161405580c01c55a03942e0042021036a02c502904810407031403001840a101103030100102403840e008281ca40840f00d6243d170400d540020340408010700f08241000d0700e904814018012212480d11a00035842501d20303034202c4c05a21310002d0540814010003100f0ba80c403030300000c3d202e00102080c54941d8944a50294140078100a40740400650304c050b1041c82c80c1120207812a0616083c01c0d01c203264007074074a4082108102c850b4000c6500040e001003101e01 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 714041276 1250 714040026 714040043
    0x10e0d0509010507020405040f110901120f14030c010b0f03010905060402191203030203090601090501050d0609050f0a050318030a21030212070f18060c0809060d090506070207050604030c03 83
    0x20140d0040f540c42c41000d80080d8003528200902042c040b03011240390390540324580502400a021007000b0555009110302c11105c111884010b000400c4280003510b0540319001d10300c1b80b02d966182207400c1d44c102c210608402da40d100310190007894006108081104141c0c001c2181e0b440e2903d68070707261500140064010862460114407151380401200c00a1443c4100700592100a04d0010041c0d4410380707101c4c400784200300020425031528411170341201e000402c0b1061010442d0396020207032500100c10f59450050842c00400c401c400c0c09588500392184c000707960b442e00712510180100d111079022500a50080413020002a0804408822121900350002e14002103c80c12006807148040c1e01d00040020b205014140d038110305198200840c039183c40001c4034800540b01f407031908500c00c000028000d0000f00c40400d5840004100b14140a00070038a440009e600035012307034251110480b503592141d000c22a1503a8144030040203801b0880700309103441d19580304c8646080240c00090920907 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 714042526 1250 714041276 714041287
    0x705091c0602030405100e070e0609060a0504060807030203100203011421011104090b010807021b180405030406080a020301060c060c050715050702010e16090902030f121b010e0d05 79
    0x5039400034140345a40e01c010159a240340624005488003116500c0f505802c0c24480c4180f40e442002c50904c2c11342c0c1d8401844441582e44800b0412401005040c45070000039510022549486034000c01000c0c11005009184880c9548145487d051109041100071841840103008031a40403880100c0d40d01c0032200e8154075407882060300505419105e541103c0d40ca05958400c5071920400a00225244044101300d0070080c3c0f00150b5040c203080b01d03030600580026401c100c41541080380140618006840c2284108991b159400d0250058405031440e6101040400c1026171003050f507940086030f5641581194501040500f100c44881c0300146030645401184d500b952144c2c060721102600070326420401400703010854020503041d100d0600550900084002c203420001e01d645030504410001c1c813440e0b10f803107040381c002c2ca20351400326030500030040b07a41d00e0014100110442c00e615000c4a03541e5000c0102e500351090040c080d4401140d040940c04050203d0100f00380c014110942099030344c50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 714043776 1250 714042526 714042559
    0x141204140d080d0f05040201030c0c0c0501030e0304080a050a140a12030207080f1303150b15030a021207030218010f050315010203041505070209181e011814060c03070509 75
    0x2d0152814488890b464860280745440d13140d08a0fa01580c000e803810030010004140c115000c0f1a503840240130100c803102c1c1004654403d80c04510642d005200f1350b42000d803540030b501c3c206900500150303059441000302a09010100c0408031984e50484014241c1401c2555a4421100d12004000505038081004018411488110391445030031024003039641c06403a130b00a0b10072602d070100340c03007100c5010b01c080c04400701c0c0d11650036000c200801c06103c0d00c0d0f404031802e000d58401081d90b580b1540a20030310080582202c03806010303070008d49000d40c50b0000c80d000e4840d044c1c2e52880182c104101c0c00c1c1c1f1000495080760899400001140d000c5506500d0030340180e00c0c1d8465548a102e4095422009154160344074020f041664421101b07140359440304e03007161181c40451080403001c0d401200407004404400364040506100b8940081020040c0000403596559120019100422140c03459010290b041c8041944400c0c842d55042c1581049070000f040c6000e2500c85030b0040c4400001c1c00a02c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 714045026 1250 714043776 714043793
    0x308011e090c02030a110f030904020f121317031306020c0c030304080a170a020705100215040803061309120e031c0908120901020c04050612010504141204140d 70
    0x5400707040ca05205401a041c0000d5036640041e0151000509800c1c504528200204021595a114a000f141011207840c03c220081d4444003400c18220401c10040302c1802039031058500c50020b02e01ea514000714107043c04000240d803d40e284298038400c0081041e40b251900c43c400802c1e40102d00180c88625100c0b02514154840309031960500c8081400205013400103500a141c40c0314181205404603100d021000a0294415170704c09038002d50f60500850030540400c030701108a502c111044056007000b247c22900c0306680545100400008001850816503110030128080ca2410400034049031920040e014018280000b04142d00e10b0000c20750303404200c032290084600b000c40f500700b10500c00145c612b9809210304817290055001d44c128001011080d114900c1e81a0082c1548400070020403004090081041ea807102400c68000d0a903403007403242c070344114448e82d80f041a15006100342880c00c0145954406460020030007444051a060940e101d0340d10161107000200c4907500d8840e01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 714046276 1250 714045026 714045029
    0x1e03030a0b040b030a080a020f01060f03020d0321140705211905090a02010e220513050a03020c030c0409050a060b0f030313030b0604060b031602030418020409180308011e 75
    0x40c1803080c401c5d404240020200101200d003156000c03a030a004201451b10300703aa1103481180007107032083c441000503081c0146e84000c554442d240104401244403c0d05c0c628403040309902c032030165540c03415075a8500704040030740c02845a0070300c035080c004030740c5802c01030b5680311300308802c0c86450074041480006c00d21303a0100310140720b8106000ca8500700200e5a903401002e02c05a0016440d0032018525041521b800e5150208151024240004d01907402002d008050005040360240400307500c042f5400f4002c40031140d00c61b6024209840c4031200701860900d050741c2291145141181c4240018000113031503c0e000e90040307010070b104d4550070000d0f268260003660150503000029101c440749107402a0442a40d02c541003203050b54882100f4401114814020f100d426002000801c2040d41d5642e40c50407480c0180c4100c0c0c3c03406803240c0100404881ea0b540724a0059008038061200e4483d0b402801c120359210700d20403048400c680c400510fa000103202d902508400715801a401e41c0c1030740c080d00b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 714047526 1250 714046276 714046279
    0x30e0309060a0e030c06120a1a061b070e1e10030b0103050d0f02030a050a11070302060f040807080f0703080a05040e0103030c1b0e010510030905011d1e03030a0b040b 73
    0xc0c0c861580c0000500140f41184070284a801280c2103900c0304e02d41181130780c0d50b9005d000031300a4507540d0500307154004c2591081001d461500c11154020710b5580c2401480403007101407510711000070b0800e4681c940482c0d90001d20060b071040c4101b04844111903064061400303c0020000140c4071903040400c8114141c101030919458000040244540091305107007500080c0d4070b1110350110941d0403616402403a1304080099010084011482d1051000c41900540701003030f01c4942c0c3e540d900150a40d48218045044d0102c0032a080208035400e0107194005d00d003110107083ca130281030460a4451000f400000e01d62270000c10b1400d07031503214509403000f42868800740d01032561a402c0141c4040c801031401c0f2905079080302a81c01e000311810b882000c40e0001c0b2210705035030f400d05040111100002c2c02c034104041c1d40c0c82014001c18000d010b12101c0d00a00d0307240350000940c42c0056824000b0b01c24414000d400320f40605040300c0c000208a9500106120000038803a00100c0014007600c01203040e82d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 714048776 1250 714047526 714047539
    0x60b0906010219170307020f0d0c0804090504061404110f0d0c061427090a140408090102011e0b03060f041a10090912030605151801051315081e07030e0309 68
    0x3086e07607000140c000e00d0324001d004444580e00480c504880404c0c809100030200182844100030145598016940041c0b040c03c0104100b08a0018158407080c01c0b2001c1d00e03059500003803403000341081045840781080036244514088510f80710040c48003194800d4004200c03800100d00d031101003080070744420203442c400038071121100071440710040040800c800e00c165070110115461401c0f500c02c102c4401b0380040049403ea031152604080b541000341594191754994040941c0e49554010110140c0022400003940110000031b161821b0070051407003400e5246a42400007055152500041030394a00c0d12880e090742e9178810001d42944281d101c840c4d000d05141c08503040080600c034041c054449564100141a0745004000c000710382142c0340c0c0646501000b00300180408403040382c031404d1060421a03e00071610716072560104150b40803062103112200d0a02e201e5a00040954205045d540c2c0b01d0504030800794924a50034000c0c05500c01c0c580c1d24024107600da4030500c03e4031070510b00142030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 714050026 1250 714048776 714048781
    0x90b070605160f020a021e0d03170105010305090c010e0a0b0705030408060708061c020109090903020102090108070201021e0d0e120c12090a06050310170304051305072f0a0f060b09060102191703 85
    0x30b0014455205680312b500f819200200b10f80d4401c3c070034188600c0c1007034010032100d03481000641e000d80c40c1c100d407150440800340b00816501c441c2002405510f104400840c2e6440c5404e06490501c071010f8055000c000c000020300c0360540d194004001e407041c0758500b03a1340721034041c401601c0740300c21a4042880076091040003c189a01980502005d80007070300ea1066031b41d10315108a00b01d220740070540030580c0543c002c102010f00b040300940740b0881003000016000c1e02c24501140b90600110b08154000400180f200c0d80d03400510074160441045800300d818486000d002940c010440e028680c2000070200000c0d403440b0f0301040c080000c2c18030040c410030381d1080c80d0031951a5030150254601402c00c100c015546590640301e00ca200f03191a5603803e81c091080c2c5c0b801c440d1a038007404c56105041403070107000766801041c03103299186071091441150700522868403005448201d0700113403082d827807803040010700c2c2d0700420088000b00c0d0f0720000c4403180a03245003401c50300e010144442207501d4007204 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 714051276 1250 714050026 714050033
    0x2100302090306100501030e1f0e010b0a08210f1c180b010503150907050f0105040905070201091401050907030b100f0305070e0c04080304090c090b070605160f020a021e0d 75
    0xa01c1017628020f07a400d00405903440039440e40d40c22100c0307454014914038807903088050b0302139003d011070040c17044c004208900900002a90040075400c50349aa404c14007840943c803005600003250380149582c091b003080103031a44a141741c001d00c8128145580440405125025660b00c5607207086d900d40d103591035803101401d041c40d650302c0134021180288604084d8046d0a94605c0d00709115220722401400810300749024042c0d00c50100911505200040c0000705107074000707002d140e1190045600025406919082ca03216034895548a01c0d4164509014031480c4a00415108107a07900103401d0112901d0300c0c02e8003491040154002c41b00e10011100220800901280003421a01204800c40c0583c07180002c401b002d12842c03007842c8096004220800c003840e0070fa001000241401d061040c8203a41c4d0700c58040c446c1c1d20941d0100d5003180d880080004003280e145865583c26428540400245510344000e540c814044601034410b9180c000301000d1241000750100c06040041c0003402240003518 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 714052526 1250 714051276 714051301
    0x40c03061e11070c1a0403020a1d0c16030c020a091103040b0a02160f020612070e0102070b0901051c1b021506010e0a091d06010605090102010e0a020a0302100302090306 74
    0x14007005142889901001c0b01241c0c01554074440d0000b6422810340e00e40a40f00080030b21403107000552150600002015135141e2011a0041c100c284038100340110241d030640e200040107280803c0c181c814003501000036000558a510640d040c10011030307800c0d5500000b4400c000540c04455101d04003007440f01c20b404e810340a0340c0031b41d00c07a880d400c040361141d000d214180d010b45060000003291000c00c00c00440c001d0080109042e00180040780b07170081740003041032043c504646074030100388261528002564100402001171200a100a0070728040c480001c1584c442c10400d101c140d016590b003950800c5046e8040d134070110b04124203c0141d400c249001e501d911840b82e4006040c00850700040720395000b00211608050000c02016030b050078080b0600040580c80c0718900c0d6000b0064041075003260810246002e00110b440306502e612301d035000242540c1248903801410f80042c080b810058407180382007000e40360b04032a18200706c904d80404034002d004007850254184503010600460100c0e85 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 714053776 1250 714052526 714052571
    0x10170c010912021503130203070f1433090904061d0a022b0203060f1f0f120201120c080114060c10051b040e0703060608090312040c0306 60
    0x1e07265502100da40e281603101c0c50050000103908030300c080320180c0b08400300c1c4004540c00782c03902190b200040000c6d00401e15107a215004224140f48580045c4000744041056804140c0b04032080a0b40d030340360603054020940002081141d4666a02940d441490a00240d522900303001d072441001d441d250810074041c10010705400c04410840d82900e820030404111480b0207900580f182500f0044002c1702465090031200030710000c03c001402d07000582d0b051040318000d039903000055006e41030180088990018070210b94590030003043d81040360074400e05029040314010120588614414001a00c05001038030034007100b2480d10180c140c04603040342d0b145058442071300002c448c0603d200c042c0300052040c3d21021009500406940b07440c80115040103500012052025090045810b580d4540d500950071602d039400c6094204100154588038090040c40c082c0f0303105000c0e00380390004039101d104034150418001204e0002501340000414011f0040d80d0003201005100c24048400e00b140001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 714055026 1250 714053776 714053779
    0xb01060807020a0f08070611030708011403070303170a0e03040e0103051606080f0603010204080d0c1b0b0703050304051e0c041a0f0402090a12030203071106070b0a0510170c 76
    0x1401007540d6a00c002101c00f201640410ba8105062540e00c0c5c1e80d400b9046160300321020b54076240800c00302d80c807000155000d4180d54aa021540d41002034004248010030002c41c0294000b040800100e5842841c00c505035014031000e031025140e01071050080d11810300b160032035100c000f50025804141850160480c0d0107882a80d000010502032007014007128418400005e040c6408102d00d144c11203455038000c10010001882d040c0d4030403004e824401c021109d003021900003a503035030034401e00030341d60303030308503040c001e08030b07051170820030940c00134012000042e0400c04040000340c2000802c020500c4070801c01200400c41d8240b070f2203895580c0e00302c02c107a60f00950401413011985885103a409071080c1004100c641000250414040250002c440c1142e0101d103141d00003c6100907402070584090103640619655040303030620a81c1c0420881005029200c2000940f020490007540e40e03030040c034241004034043d21240c00810003910107800031800000107140e00b40d11180001029540d03d0740 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 714056276 1250 714055026 714055037
    0xe010c0f02070b1e030a0b1203040f05030f062d1914070e0111210306090c1801030903230d0f0605030a03030b0a0b040f03140606011707020304120b0106 67
    0x4a681043e041800f60345031070303010120b030001d90740d00c54060400070350360044e14540700080d0f071003040000a40f00149036940c4421a000006e090085480c858840c0c00070b004190000d0142c0318502c07101c555949001404401140070719040d1035103070004502580e01203111200f40340c042d810309581e143c64403020180c0001d1114500410700020309203018145120311000c0d260549440e03040d10055a040c42c001d1910300359400360321074006501c41180024055480c0c2c9641654581c84d00d074041c07004803000a0800204004203005d80c4030808c6c4025034030f03140ea410a03c0c0225001c04140740a4031889107050103000c1440d4903140c078841e034040d6132014080303987e81480180644a403800d101c10484a85000702c81d0103030040d00301000441e00981000181c01400380ca546079955545141d010103411540140b401c04096074410010300940321004a032160a00020b426181001e900180814003299904000c81c41c03200d0004010074020700c10703a0000c4c80c2c08105000740d2021840e10321610b403024041d01d4080340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 714057526 1250 714056276 714056279
    0x3020403050a17160606260c0108091213361802060a02010506090604060303020c0d14030a110709020f031302040e0f2401050a09020d0f02040e04022409060304060e010c0f0207 77
    0x4002c1f079000c038040802d40081c180c142c40e441c00465026100400c0480036106043c001860b1600c50001005807003002446000d14a040040c0244d045140c5a40003000c0c81d13910300660210044910103620740c49013400c00250003420328901c850000d92510002c1d60190300440d01c409243c0e010740150340716003021130700d0580e10354450003048125446800701600691140d40040c94506002c988418202c0c086d070403402c0440b0311908414559440240510000b0700c0c07514403a03a03920800c101c0c1c0c101070008258154140803030181041c0843c003009103071201c2d00000c3c02c07502081d074690b9404a852410010300741c46020080d905031a66644000311141c0c80c17516000748806d00922030302200d034143c5000504d400360961070300308507001a4021051700c0790440d507129942104400a81f0040008046001c100c200500d014010001c3c681e045203200c540d40c0901a4044000284007001c440b50031500300c9a0544989490509600900000c00321150962821750144401600052844901080769080b205143d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 714058776 1250 714057526 714057569
    0xc021003050a0f020a0e040218030123071d010c02010e06030c0711030601051807020c0a12060b0a06050f0703091701020304211d0d170307030b0103020403050a17160606 74
    0x5e1040d1841c1a00041070f01c400e03074405191540060010500e2034003401d40307900d405400282140c080914000c2c040d00c04c1e840044281c0d524003800756100180b03081c2840c600c00903034004241c510104454038104a2902d102e17004580c060200e207440700001038842600c84c544a007079940d0a83c0080415904040e0740010750300d280c0342c005410b0741079800180803640903400c0a1603492400c0c0300030b05008258040c80702103142c581c0f101e1030303240006c10812054018005003424a0801c90710400112801034000e00420b20810707401804036071001c2d01041007181d4941403824226140a095081204181e900d4030b0440309225054002e180180c2c003425920208044404510104600000b00c05001c1051441c4c06401804100141480410040c0c4507904030206559010034103134051080c415544804018489295814403500039405000e003030031440c02d400c5442d05551a0200500200041195007200c051503001d070060381d1002c000f501000d03142c0110307498294003400b000e004402080c0030101d180b442d00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 714060026 1250 714058776 714058781
    0x213090506131a01140c030309240f040b09030d051f0501170412030b031903020106061103040e1008030d05010305010524121204090926030c07030c021003050a0f 71
    0x40e01035058800500d480c0560055440c0340403052401740b062018449a84030708428001107101360442d50140c0a601c0124614803074228940c1500c42c2c40d0035811003040380d048400c0811540040c0c01c40c0c98841107503030301500c0302d2851145000401c009030500d410301100001081030003585200c03014a10034659262801125280c00a2400c0d119400904006c034020079007003c0e082c0041541c0d4036020914600304c1000c20300e000b000010345034001d00b8940c0b42e40c0526034288203142c064600386c0fa000300a50940780c4059644d024500564400401440214031440b29040c080402844000113480d01c441660b010540100001d2200350f40707039400c0c03000140074408000b0b0440054081c500000f940080c000048c03045e40100e0003c401d849104112031110800f0440f030140009107210000882c1c101c24170700e00441c1e00f60140d207410303017103910400300c001c00094140150b03684900e440c0656600c032030715410102c69513048540065001301c50302001d005a180e064001d28820040b08070140640d51200c08000b04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 714061276 1250 714060026 714060041
    0x8040315050603072d03080309010e01020a02120c1903021b030a120c0213021303170c0705091b120105010206091c0e0d0507060509010807020303100e0406021309050613 74
    0x3816008018103001c4051000e0014407017454642c0c401c004034401c2c01c1c07030310041c5103d13800a80342c0c40f1001c01005881d038024040c440c11030301d01c00029070a01c030710703100701947e21391a41d80040703524080401d240c0031480d01004649040c0401200e47c58810f869414083d45030144201075090668080030f0701585400c0000d40400045c1c0c0c0401d1a0340089041d01e000c48007011100012030380b118041c018110401100e0015241713000c12071415442c00c6d441c40c0b40a000811004c082a0f103014428020714540920200b0000d0480700b041d103103040d807a034408850003c005900c4070340e44403441c000f0401b030041030320454500741a41e1080e002c648154803680c0c01c07107a440c0c050540760410110441c006074400e61085200c1502c070a0043c4c01085134030803650782c1605009494200900040c00410001c040390b9005c00c1098010348103001941c41c3d800c3c1038041c202c1218090040880c9101004d000c01e04001e0642c5c111145100703070303410451080d5154440c03c0080d0009a450900c60009203d4415074403503075200c0c001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 714062526 1250 714061276 714061279
    0xc0106033005030a05090f0a060c0e0904022107031203090218131104203402010e0d0f03020606010e03072d0305031c1419050c1303080403150506 64
    0xd003195a005154006044006c213021000c1c000e280700c0c4d016521007040300443d241e200c0c5202141030040034100401907928a00700c14821500e81061202684441080a1000c0e90603c04201081803031750f107251408555a0000300000000210280520f50661004d1080c510072640b2080d18403100020085052050790507001109665100230700060090303401030000e00340074202240000703a811305007040da50104800210300400040544280030710644001070103d440001308030b410541c668090106407107010003410311081c1101c60b84195103440040c0e0029a11110b80050303c0003602e002500c078442a0b90b028017280006a8000191a000c01c400b000e5a1117100024800c00141c454500b10109803401d40236480303060500032000c642c2c14001032000c03c038855561040108801d1010044841482d07a10403590100d005200310720706c1c03080a840c1c3c000301c01503011959455005081845118107448d40000a01c0c402002007049001d2024000320b83c02003000c180039500340c5900c04195281150900d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 714063776 1250 714062526 714062537
    0x606060306030c040c0e060a08011d0405100906060b2a030c0a03031104030b0c040e060103090201050d020706060905010f08060603060f01061101110a030203010305100615140c01060330 81
    0x901d01420180d2082c810311070341b13180000340d5100560110317072550b00408480f000101200700600c801d505070190780a40c8054590150030502e0203464140d110106041611810b5843c0d241781410b020f500e07044900035040105056640701e06d6419500325845002107502d01c02020008c400d4030702d2001005a80710095120080c0404507801c0d030b0118000c003402504845808824000030020542d500180b074440c24100f40116581da00b4420b03070b03181c8460000d01040c1054244640e040c0141d91103016500494000880540c5401c0980341510241009070001c0f2890f40c900030000649004030320360780003214210f03000e941598540100303160312200c08586842410f800703c4010004644940311a513140e1401c4000051a24881c01039040d203544207c80090009402200500a0081c1402020f25010808104002a501e8084941c00b6181605804802d002c09850180c0e071441c2280304454100398200000c001d22901c9103044034140c0c169400361400c400c004105a050b5102441d5118094001c60310f45 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 714065026 1250 714063776 714063793
    0x12060f011505121302120303070909181502090418020f10020a05070f0f06020d020c090c071713050d0305030a0c1e0f0f0207051c2d05060606030603 65
    0x15100c020801040d604101d010030070801583d40d20700703065004a40f8210b02c0c0081083c507004103d2130345e140440e801400c1d04204103010041780c00c030b51038100b2a505000d003c184440b41044100f44a401c1007406040e40c00b01503481ca040c4a9a83d000308040b2008440c2045600c0e240040d01000b048c103908000e4102d50264182e0420b07241400c20641c10b21000e20440e0340b1080c240c0e440c2401c2551903444070b01101840003050000c0381c00844020040c0480e880281406c00c0c042100a41d1200100401802070204002092501444a045902c2250004c050304041d00707006000c0501c1c0e0b40104020000a0020302e404509860403861074807500790190380c0d0a0841d11034000140041c64016004010311892040040708803581622000d074039211901c588a04c11041d880150440e160721030b4010440d00301c0c1105003c0e0740e4070004040e408500e00309000c406c4509500e450611040b01420420b128030304030340c1c80d04030b206403c048494200e100d001603c8084d201c00e0140261801b0035200f0701d9050700010b51 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 714066276 1250 714065026 714065039
    0x2060f2203183c0302120c0102010c030b0108070f14340503040b03070302071a45010f020f0406090b03040c210b160e2403150402040605070212060f01 66
    0x440b090403c0070690103070b25560b0740c00504440519600d01c18a900b180c410581c1360340e02071040a15100d1282028412211000002071070a078004010301c091043e41c41f080c0810a1040e00340c28000c0ac200d00c040e0355500001c4d01c00d040c602035080b040d4000582103030300ba2048030104080d4058100c2d803003c011402c3c1420716001200d0f41d00003c021800301036081c40f003100400c808031424412150f9541c41d105040c1000c5107042d001200210383c00300d0021031101c4011411000004900c240341782d0111280505405115441c00360500c4100c074484d041c00071a52107030724950b01004004451043d161102c0040d903c600814031400304030b4028040c0c49840508011a4041801509180b07038558031841180c4400e41d02d001e810201600d480500152a802404845400c040a007000401c11244000c80400d1906100300c00010704091045e03180c0044040b4241c08500c031340c150080c2c03100500035034490f500c072040103005030858070090703203e4685550500c070180c4c03010501d140944c840140c103902a070b09110b03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 714067526 1250 714066276 714066359
    0x91c0302031b010e07140f0f0a05060702190609051903030f0309060b0d2d080307050705030d0515040501060503100303050a020c041503060b0303030702060f220318 72
    0x90360b602065494480348100840c040c003403240900500c0811040310b903214400d120004000402c0c46018000078046031903a03640c6c40d41c0b43c070100c4070115031302c5c1d64540040c8042a810410b02070080603803420312502162498000084406582050380c4030804c103c4103903090800b640041c030016020804107000d45120030702c40e030404159a405104c001c28541103000c046411120031f220f0548200c0c2c40d55584803400043ca8401110340340a078440031000528603210a10a0312002d13010100b4440700280340701c10441d06006540314800c10400c02c111904c0c0020200130020101c0c0d400ca88150b1500c0c00114030340d80180309890041004400c20501c5c507007507580a4070564401003002041d441210a0303800c01d036945000315000c9821414080022502e10301d4004103403102e0100040c80b0360024820010003030b40c0000c80036402405049111581c3c3c0740c0000c1e030750f23000ca0014180743c54210341100d15800e06410040c01044030f02700107100c40b0860758610785c041c50b06400d12260310312600360105001141c04800c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 714068776 1250 714067526 714067567
    0x2010506191505040b071110090e01152f012a0e04021e0712020a080711210604030f0305010f06030915022113020f090703090b0c091c030203 62
    0x14141149080d885c0e1036a810260460766080b00c0070401c1090070080c90a007941e0840d40050300c0e003030207040c50f42022030030b5035140303014020f0000640c90104911603180c401c1c1c2980b100040504030b4440c20340700a1381508030a24083c0c031180095804e0900102000f00c049028850f00f5865848030202c5040c10035003190082d048a41a541c030a400340501c1c034203c0302401488440e102100881e6654020034a0180d03030820500d50020309540040340740b5804500e503c821030714660350090813200c00503050b0340098525a5040c40030042007400d49007860500400080c8203008034040c0d2140482e5101c079150481c182d480034001e100804844c0b240420009000b50041c840300c921400307545012a0b00d81803d00200c1c1c2100580e11400102d00540003185c0f0b000d6440e450f046420804c044441c4102600400d8640301f245180c23601909084001500c103501c00d901c010722965000d1010241400d21003074203140780c0c10040c0b44d00e02c5410b1011003110941546110070083c50b900d50099407c01d9480940c0066100e0704 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 714070026 1250 714068776 714068819
    0xb04090c1e0f2303010e0610060206180706050c01090b070518040506010221160308010f090e0a080f0909011e050402041a070201021203101a0307210b040f060302010201050619 77
    0x301c0c282a5030104e4244000c6109549858041c24030900d8449c00030701d0b11b50b01520700038840c0356000c01c0010604000c1262000c0c0c0e140750800c0d503035030a0362801c0c031070051404180c0900b054040d1414003484d140e002c2c000b81f030710b00030284020202003203000800003101c0d400c2d52000e01680c41000440c40104d01a03400d00b00c040c1d405400241052030184003130082c003800e000c045002601010041c086074112600500290881140412000275611182b0741c0e200b07030000000c0c020000201300c1200c4641a1011a4200d8401415030340095039102c814a000c02318800d01c0343e080240891011032641424421758080321100140452500140101035a441d44031440a0303046014201840a0b689216001180074029048071920381038a00103007503405090180500c01b914030304000340241c1940c401c001d1040e68102401c414542c0c9003010902c0d000b0030b11800c1071a000f0742400c0b0a100b05403100e078020000c4a0003a002400b0941e146030421410b800b12082106028258810a01c540380d141403500c2c105580 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 714071276 1250 714070026 714070031
    0x20c041112040b0a0f1a011b12051c0e0a0203070503150f0a02070209040f020415060e10090807060c020405090105010b0f070f1a04060605090c0d0b04090c1e0f230301 73
    0x3141640d4500380d651040c001c06c2c4107541d8a5503d126968007001a5400e07034005000b50602e03002c255120070503401d0305c2c10110100900425803281040302304030700c040501e81000d810001c0c041041c1070251120501e82d000e034880c2c02209400107aa06003c036962500300c900f24a5240c545d520708080650441002c1d02040f070165080c42a1001601c0300e46031240101d00801c8074514050709841040282d561074403031001c103094580d40c2004140e410030f041d400200001c032510718503078000c07a40848420740582c0c4030b40b15901c60f0882c0002d2140d00490b200304814002da03000d015551f981e02ca07044c00e0b56800e00c01c0214080080049801c80e00a40b0054100741e440b40000c0340075102c40d500d4542d4120312441d401c440c4002c514003400300704012032050b0f100410080c1c0303c2180c1d900d071000842038070740148451510216115182c808480d0382d0340e400600425481902c94405c03984460406100118484040c0c45989481c1c601181a910040805007110130191404404485001140e400702c0e98000740140c0564 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 714072526 1250 714071276 714071291
    0x3180f1205100908120105040204030b0703020d0e071e0e15012115080c03060610050c070e0115020607030207081e0d110310140a090c050712020c041112040b0a 70
    0x2e860f406903c0000d400ba41015444000d0142210018007040e030029206900c104400c100240181c0c44084c0e2010303145c200141c03254414000e01000e030400721201c1899000b251030104804107065004403800050490607a11180c6a80080a2100c4250b445481686241c0c64032485580708502281c000d50102c2e94807140d1a06800c003c400f031310707490131041190f0302d20346000b0321144008000d00010307118101c000302524240900813440c0000c0c0c0d17654460800000043d50380302d1280421112004082c2d40364001d44969441d4070040594000b102c3c2d080c010300600003c07420151090003070383c035500c0d000030000b031510a02841d1408220301076440804880700038404104046001d10405124055182402d6541c2c50000b82454050049410140d00a0034020418580340c440c0c01c41c0c041543c2d140c00700003800c81d40446d800ea40e20300034841c00411603005810032104040d03001c10003c6d00c0c0d010940d003d0081040e0f078407000d4070b0b40c0121580341c943c1d608040f00080205001048203034001410100000b81407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 714073776 1250 714072526 714072553
    0x60904230303010e0412030b0d06050c0f0c010e010b122508100b040c020312010905090712051014090a120306080a031106060603090a030f200a03180f1205 68
    0x5402c260300054458420000700002c0c060355006c01c0c901c002851138200180d031001d40010701c111181e41c8000c2c1070b0690b40d80014400c1c1501d0000c85201d084111440c42c0c641c0d45800d41c0c075018180c80c0d10703000095401d007055494142001c45611328404000d401500000c0619000f0b41c245e42903040c81803078400d01c0c00000081181042c00201d9403003c4200f804034030050a0802d020a4601400ca00e10445d4000c0129880e40c1d035103030034414191044c9150200b2162225500685410002c0d0005a80b0218190145042200c00180b641107440c030124103112901c1c011007050382c40c0c44201c0c0d00c182c080d0400910000010049000281405201e060024015840c2d401c190329106070260210082104540d40c01e0b03140c2c1c01008034985c80501100c40074030b10b2524118180c2c0764680c030100102400340d1454085002800386402c00c003c0391940c580700d059045c01c81c1c060350350340240138000d0700031030a05002c04080819410b548426103259044458000c0e1425103605545031b0440030603240d0703011706005109103 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 714075026 1250 714073776 714073783
    0xc050d0507121b14070204060803030f0108012007030f0306080303090d14070f081804020f25052a03030408060106020d050406080f06180c030118020306090423 70
    0x803001e0ba40c0302080d4840750007040e002c403000400c1888032000c004180341c02040d80401144016104120103645130070107880820050146078011400500011040007000740400300900d04865001c4000d000070342054106010048802c462449070220070402c40c40824001c00d06441000982e00e0001505a41e91124508680042c0c030051916003100c0300030340c9542c0c5c0c056020b90843c7e18240b81e1070714042c01661000808070306154002c1103004045440d480014031801d0700b40710303801c010b00107568524042d540740145071720500b24000413030748a200022008500342110242298068000c140c00024200f4110208403101408890044081144c00303440c8c5081c806440184007030300c000c1856504042010b814a21003185c908204541804104201036111104603080b001e076941030030440d1125808540c00c3c4040d000789074103090085042c000c080e4000360041d0304880c0e400814a0001e0b41c02072004041e0703c400d9405035031140045000c00d0104000e0805030a5800c01c105140c07003079180200c4403a04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 714076276 1250 714075026 714075031
    0x170a12050c03100b0c19240b010201140f13031404060c0b09010513061a040207060e061305061b071e06201b15040c08070501110303070f021609021309090b0403030c050d05 75
    0xc075120603da0301c030303941c0902610290202c04020901d0b907107051180e00c0b0340003800034142cec1c0c0d2207007624604405241c09000c1140040c40ca105c04180c0d0360384c07034000240c1041e01d1220221445400380c0005a0140360600c5000d0094580c00820303c2102282c0d110440030381907c0d1080903110a1fa070000c07400c0c0e0b650b203100602080b4480c180101c2d15818559805040010081240040301031004401002a2001c01c06650101e4500300500e850603241c0f207545003500483c88004c2650791045043c500d2440c07184891b12481d8441d40060000040d0700042c01d040c4e0365000c0e10503038521000d1040803400490200b51003035006d076003012111001801007210040e0304060f607050b00e1400d5414401d20404d54203000e64400b0f080b007820f0078580e01c1140340b04a0350b203100c010403020401c40346118641580b8400c0c07003080c4401c60622480402d0302d844121b0f000c0254010350700150746c00c08000001845a200d070280a45054100c885013560760b40341d0300c09501424886041c501004000c2004072003801180c0701d03850 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 714077526 1250 714076276 714076343
    0x504050303070c050a0e13030f0c02062a030f070b090a1b0306060b281e020f060114010504030b040602070b010e04020913170a12050c03100b0c19 64
    0xc29649011306000620807984c1001e01c008044004100f904515100c0d44031902d54945485d000e1980f095a003101d10901030708009511100000b40489042440440c445030f04160b807551200382451610032075582d2007103031410003601c02c040c0120705c003094940200640c8002d4040070340b0843c00079030346d4464110b41055441c203050340c0035500a10511145114881c041c4c5100f81e400c0385440d0f2501c0e040805080c100c0076001d04011442020f1282c28400c603550405150480700c103e0200801e1a07002e5200ea80500c030041e01482030034000a084401410318040034103060312007914003410f41d10381400e07070f00c0c0042c000c0c0c490070b070200060350020b00800801c0d8001c01c41c0200d40301701400c0610400800d0310b000b4041c03850418000941d800418600403910074000701c000d070f4181ea68080c401065400e4403900800f1680d140c6404200a4600080d00046200f89110b8101c002880d8031020070501030b016440d41002ca030b50000c211b0001400070203030561038490085d03c4210500080075030900700c2c00044100f22 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 714078776 1250 714077526 714077543
    0x11101112a070f091e0f0b0f190b220602010c08010b0903060106051605030712090512030d02090a030204050a0b04151d220b1b09010c0210050405030307 67
    0xa440400400319203540019029000e0902a443c00e52100710b4041d490161105465851004500641c5841d11040300c0b50f04880c0203029200b203214455004158816a49001e45002425034000d440d20080d080350072040d400c04000c4950034180c41d08100c1d0003d050080b485100c014522044102281805c0010019540003264251900c0c40003000d808041e408108103110601c07803103141c1d80d000301303010341035501500d040c0b0b0320303030100150460004461810140042c00300103003007014080000d002a176840c607591281a0303403903070762014054540100c102c0799109820501520700e11074615001040c8001d0001c09907050f00d42c4076000501101c0d02610390300c2090f582c5000010040c1400e0149031042032205621084040c0703407001000b8802e081954840f031407415400004d0303554041c4031200b90010201070b842c40d2140100c0c60a60280e81003030301c0280360a241c0d0030000031090110400c9900d07180d010307516a4000d0081d41d0030302c280c01c05540b01242c18010248401301e0703140c078100051700a0a0090006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 714080026 1250 714078776 714078817
    0x130c03170406121e050a1d030c0106080a050613030215091525270303050711092203200307021c080f28050c011503050c01110111 57
    0x1a2240b80840d0b603052440d82010300d01c000b244440c1001c802440c4c0020008101c2c1e40d00c0c41c80c0b4400510550171404030740b03031440e030900316864000009000c50200d118002c103c0561981c0085944503407400000300142c1c40341c1c002030120385520b440355543c103100b0700440307420175205100ea003d110400c1790040e1140e44103a49107c1017011a500141c0c00030810400900e001c040c007804a14480001d040c07100910581070404491554407100343e20000c080c0b07401e0450f00302e0301c0c0c1c41e00600e580e029070300a0300c000b415154801c400e460403044450084030580804201c0713000d851144040c00b410200140c003030050030340140713000c2050040c100585030032000c061070b91401203104119141120302d1210313240c407403450243d00002d0858021110042c0c1c00c10204ca803542c01e140552041c207403102d00d5030004211607414050b0400d0301303d4043c0c100c0d054100028085045071001c081849002444050440c0d400f0800000186d4002c00300251082d51200002c02c0410080c0340c00d91859006d51125503189485102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 714081276 1250 714080026 714080039
    0x7030806031903270f030507030308100f0311040b091807230103050c0d0e03070c0b12150409050613120f050d0209040603050a0605040b090c0603130c031704 69
    0x904400b0344000b036900000c40806480051030203801a0007244030344100c111010552030b1242e5044000d02548810201039034491500b079813900742604c0100e0220310104041450300703020524107400da646040c00d2414240c070710703101d404500800008c0c060b00301d40d6815070044c081d02c801311800c0c0b0603007024030001c580d12a040c0c1e0051a0440740d50200f80391111484042003002c0c490304844071688800d1030041030311344a60002150500c1028018000c0c94644004040c2000021024102250103956601021a6101c030307034542610804841050f002c45100000300100c0d03601c1c101d025080e4015000041400742e0f0382d207041c98507001b641c01d02001590000407008100c1660400c48000005182c40c5403180b03034030703180a4150301600e040e14603610b030080f410100c1c5803110303402500119040011640008011308004e0001c0c002070381e040e90045410400901d0307034640040d41400a820103000c2900d1070313840b0417541300002260b2008940c500308070040000801c180142c4182c0e04420fa80e4095038541c90080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 714082526 1250 714081276 714081283
    0x21309150512160323030a031401050f06030f15060403052a0315061815041d03090108041b081f1401031506170c030c0a0f050d08040801020703080603 66
    0x9010080303640084840e0300700e4440038210ba011207502070b6a442c0000044280101d000741700d401c00208521010600c0c0010960541000003403d0881402c00c0c0c41342d07202c10500070b0700f50803040825080101080411002540079408079400149001c1c10166407501c2c3c00050040e1b4000e0f070040d00e8940c0081c0640880003244a8009000744000620304048002c0d500480e44441410b2450300310590a1400580141c40b48400e00a40c0940c001c80e0328424035011181880e0703402c8060945002d545005c101000c9102040c030080d80c8030b0310f81c0c1d00650504003204011a1403a400400440c1c0c03c041d0004e4040f4000341211090001c0d00b110409040001d0010901d00c115814043e6400c800c1e50829003440611103410784045c2c1500d030031010520b900c4800b4004240075102e6644165044000005d142e0f07000c04d4041908911200c086059800115081c402c1103d88413890103022080c0b181c8050130025840c03ca5150600203210b010907508059a6002c0709003280c00201c4203602148103402000715602d000d2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 714083776 1250 714082526 714082549
    0x90f0506091311040203240111070b0a02070b0a0e1c0b070521010b09011701180902030a0f060209120a0f02010e0f12030409140702030703030213091505 67
    0x40801180c54450001a61440090a074814203030728108203000340300800356605140c15000d00305640d42d0600c02924507030f0240552120410a003241c0c90740c080b0350b00c01d140341d003580d00350b4800605101c2d003480d12041c0d040c1d00c0300c0c0c0c100c025849030310000184000d40c040600b00028143d165030415105900511800300203410b00c1034100440316240d000050039210010307030400d0007481d00948451101d200f68104d05e99010783c49420080c2e4100000c0c40c4503142009144124007070341c034001010044001c0c00e06954007800ba405c0e82d2400c251000456450750341c003044440c0c0c0010121200d264080e00c031030751015070110040da80d4640000301d161150500f9550740c154881403200801d52003a580d29800c40c4c002d03c0c0e50340207040280240500740c03c1d42c0e0301c0c0c02c110000c000040034404480000d40c0029580c0d8003921507844103501340510004084d0350103454a126940540286240132815601180254000c1c0d02d1945462a08000492250491b2140189029a942c10600c03c00e09060800038411042c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 714085026 1250 714083776 714083801
    0x1060b040816030c06051804051006020c040c080f040201200321061c1113020c0601060e030d0c0606170c0307080606060d050c121e160c0809151309 65
    0x440c0300c1000013501141030038081301d425180040d211101040350104d840840c40d1459030260a20080c01b075180744005400086507441e40071a0812082c00042c00f02707030790041c4800d4002c14407000000340720200089146034001c1c4149040c0c40321014079205803800c2003860400359541c3d807020a80003603200110700c58101e03185800225041502d001400540c1c44010311510000e0358150506070400c00444940d040b6009000404010302946070f2403007000250008851a0550710400300001036140c040d01120854242c0500640300e02845a001030341c260304540403c0342c1e11a0341e0b480000d52503d9140e40000a0801100030f009003610402c105881e14045030071498041e04008140003150303440404660040840450208540d81c1d10401d01c1040e0140c036071400d030058030000c108020b030380c181f145000c0b00c19881d030081002c3ea12016904003800404481100203c0d505030044000300716114094001070310014040c0480320801c15448034641c0003a912a03e840e9003039030081c1306c081154080c000d10b1846 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 714086276 1250 714085026 714085063
    0x290d02030d020f120f0d2f18060a17071b0f12210c050c07030305040f0611030304020d140708100606030509070b0a170c030403080609040c03121101060b0408 69
    0x500c1c568882c141d101b080e540841e86503407442d414010403100c100f000c14005e41c1e01c0494256000c0342100611540c4110042c543c141095044d005035403600b0411354190310700c6561060103085112050350300c1d8480143c98035007030201241b003110110300c101400601c0a4410a510f00310400d092529100c03007001d0045800c03e010990302e982e12229010500700300c034803507010000301c0c3d02e09000005031200e201d1655019824000c40001005054010b8000c0c000c50b030940a80351038540d5034182c03c9840d130302c060480650341c2e01b00f0000b0401514101b0504100c5a005090007000ba58412206515054446d840106a900f00e10801001c14500d48a04002041e0500b0207000925050b8145501d4120320300682011500106900d4051440b03204110300342c044441c840346a41c18031100809032600f04480441c0001e04200c0010328500f800600203000301e6016000b42ca180d070451b5100382c00306c4800011311080000031840c07002c180c00240201c500800403440307031580c3c840c20a07c815040c10f103101c0d002c20f00d200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 714087526 1250 714086276 714086287
    0x151b0708030a200303040f140f1533010f050309060106140c01021216020a0201021203070318150b0a031e05030f0a030f05010b0406140903120d0b090a290d02030d020f12 74
    0x140007142c000c0940400c0315224800d5a03c40315030742f0383c1e104a01101d000d0b451004030f00034240074007141001102e4500341c907030259003401000203e402d8072045912007a15000000100521400b4444e800100b8500d400f04e903080c4a118001c003801c84e00541d40500c0c508000c1d07014803c0212001c0840d4408505074405007208040c01d0700082d42c0d03080796030204201100f00000003030880d4825030215103840c1101402c902400b1850074200c95080903540340b20851894240d003460f89281090b2168200d039480100c8428011410403c1641004165810358480c0800c22584442c0140c400003009205c080703480c00542013070300c2e03142001224416040607607560b504000500c006a044040f00010306041c2c8001ca0780d500c144c80100341041840d030021706c5004c501040000301c4c003280b0b0300450f083c2441610307110030981d5500c002e00c0941c0c00c040340c0180101d030300300e44010072800b601d0000c12500c40060400c04040c103166002ca45030440c1c1c01c81490058100e103030402d101c030505000040314210750311350035810308 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 714088776 1250 714087526 714087553
    0x310111c020a02190804030204060b031006090501080a021c060f260c0d03020a020312031e070e0f18180f060601090909020f151b0708030a200303040f14 67
    0x204c242c001d2094004190781061410003004100b11005103034040d2081c00040c0d0340b401b40e051070b500309885056100c3c031018800f061091103603280c10b0490304160369820050301d81d42c071f02030001c0d4002921541c0440040114840810301c50003840010106c5100a180703003407524590000f50125003441c440012003c0f40075400301d03000003c044540c40000c80324417040d40424030b0268501200040029050b004100c501c00360368040c2000b9601c9644014480d505802802c04800790f242000c45002002c61141e05a105403400c18205548070613802501680d07400b64001c0c40c03014031502c11120b400b80310803020701d503000d481c000340710801c680084d070401003481d41410300019090900c0f40c09001c4400ba50703003807000150354425030616a00c51300981036044541c50600104500d0b8018031038030111a01804204018100000315041140c019401550030505001c1041759071032070010940900710282d818000c249901400194000d40c820641040c000c0401c2c07404c1e800c0301000d001c6075082e0390084161020300 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 714090026 1250 714088776 714088783
    0x3060b1201091e09050307150b01170c0417070303090b041d1306020d0501051207030b0103140708030a08010311040b030303070f1b050f0f0102190e0310111c020a02 72
    0x640e40e100c00c000c00c2c0041d034180381652101c420901e1084490814507100c4c18820080003d1200c0d43c0510400840400e0345a0b80c0b02c103941d481c0e15000d0020700c410348400c00030540c2e54140d54000030100301d04e034034003a0b4030380b140c442a14881c00050705941140d1390030420540c1112403034008003014104c07141003c0c545200e5013104440340c081c041484c680e050003c0c40c03040103401c21600342035010030110344520810910034010030090245900407503581118812030000010f115040301d80c010000f28180e0708507502e00705a01071044c3c0441c498444c1c00c01c00302d044201480a0201072005603070b05921985107040c0703882034128030030400713008070710b01001054a61000f00440340d1104050800c2d85000706e02c0c15007101e48002d0341c0c0c0214980daa0b555080380410002048045080c861401150f01d0452419251070807442a104101c2c181005a0044003260780140e03a121002d9034010140c42c4050241166801680e000d00309601c40703400c0c00110404503552154111500b40303100e52007142032100d4658065038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 714091276 1250 714090026 714090029
    0x2060621070603090203010615211806020904060308040e19090c14180109090209060402090a27140105120a030e010507140a0609051504030c030c02030a1202070603060b1201 76
    0x101074075410030b00155107007504023000914000d09030010f19034402000030001d4050081520100d03000002090034100b003806034214014004c903040458030303525070b1a403000350701035404c0f5a0490348a81000012401580290005051310a42c9a440d8581051101c0c2c00510840b908005103180100d1900400d0081790340000351681c0b1134a5401c90285640001d003985c000f6403103001c0c110a2070703002040c180300700c1e044143c60903c2035426000c035440710b5003000300b03900078480416081b208010b0f0230484c1425003120204503a10380e0300058044070140c0410b600f512181512418448403c00040066050140c01f1071091011003000d400151596680241260140300e50b650402001080b00e4007030021100090004541c200100c0d14100c0321032600c0c01c098061540700380e40c0c50054018815034668070183c003511541d419030b50380480101c02d5034140c80c2c903861458240d805105070315900000503152980d00781d000005d0303001490014a03004001b01070700c5540d00b040c0d140e01d40600c2104106034101e00e280c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 714092526 1250 714091276 714091289
    0x70902131508040807240b010e0303090f0f0a08011b0905030c01091707080a0b07201906020f0d1a0a140d03051306052203020d030804060b030a030206062107 69
    0x79030f01c3e011800c0c19407981c81404c00001b40401c003425054041440341c0d00600c4050000e880701d0180071150300801da1039000e000d010640051110441254618026594004a503001440c0c4000e0989841540b800c5406006100b01450800f200b100040c540102100005090031801400e40d001043d0000b05500164400d40014015100503c15400000c0c41641e0281540b030003201c13a4142c69003013a031a9040140c5540c0c000c01d102d403c0c801c0ca0914039102c603a0214800344010001221140c0d1702e480305407200c490560b811907081c0304654003800010010660514002004980800c0c01c0e26903a060f8200001110b02c1810030b03c004200b00001c4050030030020310f0880340c5a01403e103070b050580e0b480c400c0324070080c4001004100070607100d03002805000051000e030300344814844001007020621919000103507104030003400c4640064450300302654040d200f590041000c40160012034035010301c0000444c0560003040800402e42060b01c41c031001c2d110101281720811040070300c1d140d1282450700030742 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 714093776 1250 714092526 714092543
    0x80901080603071205060406050c0720012d0e0603150d0c0b031608090703030c060203180102040b0a0e0405070f050f0c03040b03011d092a0307090213150804 69
    0x1800c907079042c001c10f8010002d4070503120003100685040b17912002e0445044074841d00c1d04d800300e80194084003e4a440980c003909013403080001980d00100140d41506d198100240203141a44241040c5901d01c1140c20403400f200081440181c09400c14903003d4096010f24030500412034203034506080030ba0000d006440500085610703003410501101d480d0442c44042c080041805089000303d4000110b080040d0703100102a1a50034400e512011180b00c0035000840844010001c20079076801141c000300b5207030714103c0c04004804100d0990f0443c1d0700000f00b160022a4801116410002070708983c2c1c0c08640401261412030000340c000c4030410080307004c100f400b19805001d40c1e540400c81e10402a610f04076629550b864895950a1340240910088051025000318107609002d0000340220303142c0d0090f16902820320b100a011a4511060203807030030711f102d042aa551400e100040c0a080d6142000d0780e0b075040303c9400c4210141300e60022151269550900c0881644201c843e03410a41c41503d5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 714095026 1250 714093776 714093781
    0xe06150616020a03080a0203040f060c26130303050d200d0203090313140f04050f0708130f0b0109240501030506060d0c0906020f0d09151b0305040f05040908090108 72
    0x4100c1ca00c0f140c0d04000e200140015100d6085a00003001e0b00c101e030006040c20300d00c59181c5400312110b0a504800903e5052000711003229100c051060103549020050600d00b000707940d4081500804041e0320940c00f00e07034006138040341c4041900070402c105041d00d0003143c0b0201012164072131413103a2400c00882c5076011001c10354038030007802110350140441191510303080d100d4084801000c40c21007c144101c48840f01c0ca0400e05240c002d01c2e200301c15100c1081038a5403524010b0f01c1201c002008202c80c1250041400c001038502040902d03807a01401c0542120740c1020040002c443c01800030401c80f4003201d80c0707018000c2da403d9200c1c00f41d4900f0b180101c2c01c0d03100c00c0c003c115140101901582c03002e0070710b002e214016038403203840d00454203a542101d1946051882251b03ca01000d04844000703582d030401403001c1d05003074804002012591401040d03054030244819020361088001f180001c1c4005001c21904840340f00071006803900302c038200b0201d402540c850340b45108201101d818000100300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 714096276 1250 714095026 714095029
    0x603020307090f140411090106080c03040b071e0327080414060708070f1203020901020c0d05100216031103120a05090705060c030a170408090d21030e0615061602 71
    0x40324280190131030004055003824603110f20004030401c2006d000700000000080c03524030030311949006000f8034070040e18545a6488908171007900801e0a001e10160b9282d016010041c0389158482e6007842d80c2c0000c0c003181032650f002c20740089418048200c621500d804020500c0c84c0100c40c1207540e0880d100c414500150040740f498010360344050881100465200c01740200c40418104041c8282c0401000d8150b401003038080380140b42010380140d001a510307240d1401c02440b9000058052000c90700804c0000740c0080030307644014110000c0d9009031130084100b40d040f04181d03128120410240d400c000d00e080b401040c060000780819003c03921040400c02586041c8003600141c03030060101c80e47c038090400c2480d941d52092010780e0001f81450030404c4130042e040358107405940d2210000385889200410010448880311046e500c265107119030710300350f01e403000498505028581b0041035904001c0c09890401070300801c1c00b5030310803190000011580e40c6400b00e800030f5024500c9421a08920300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 714097526 1250 714096276 714096281
    0x60e0f1e0703210315060e0306060d0b010b0c0a0602040303111005161b02030708011a221e0504051606030c02120d021201141002120703050307030b03030d0e060a0603020307090f 78
    0x3200c0c105c0c0e02411000c11804c0d40300d841060400713001e804690044d00d03190244002464032103c0a04114449401804442d15013401808002801012a007a001e82c9485410403a445a131003140032480d50b039504c44915234188401c540344400d0400030007461911110409030750300161007038020003000707184400c4004003515005101a40290031202c20945506000c1d0003050700c1c0000c006410710242c05405145004000004030b444a01c400c0c0da00076144820001c094103054440402d082c1408000303500b002924071034280704074054030041041c3d94829182810f804080d4101404050070b09800b01401c42d0000b40c4905040104035021780c2e00c1183e000e8080003170003507041d5400b086210b42d00000d008184910041480d400450381c420380701c5003002040e0303540e10400c2090160203209011820109014078095540034200d0b0901180460034400064115802542d4120069a41c5d00d043d00e846041081165403126490408104c0f150654001a079038141c28400c00741c075151150a039404121064 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 714098776 1250 714097526 714097541
    0x601140d050726060906010e0c040501050d0c0e0d05070501080705071e15060902071b05090718030206070605090114070203090d060605090c040306140c090904060e0f1e07032103 78
    0xf0b0b4241c94603420541821a250300c420b01c100200700100b540443c80ba61700e070000f00c03000c482058465130b281c41104c200140141485802d41000d00154644002142d11038000341c0c0419440f46018000c52800e00002401c04c1801070401c00403c8810322007400040d88106003441c42084061380030750002c0c090f240844001a00343c1c010200c3c0c034182400028a401560080c0c0202d505c1092182c00700c030700f5044240305021042c071540f584801001c011400300e50060540e20b135072034000c14001340c40316180c0c1c01086c0c440d4040c170811120300340d0f10703020400c0102003881010292140004200818203003742c00a5490185180701886a44400c80040403c1840d52001707000340006040210385280c014960001ca400034403042c0d44050030144c2c800e00b010b01d002c8405111b580541c1d41799060210001c02d00c18070321001401182d0304c3d035941d01106680380c010018104c0b01c50946008108400540c0081c08007101010343c5692164131618090002035109103140c05440c040c0ca0140c030301c0b900d05c9003040b0040c0080 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 714100026 1250 714098776 714098849
    0x10030f051606030b13020708031b0c0703151a0105030117010b031b090a0c0c080d092307060306050f0d0f0804080a0605061c03030203090109020901080601140d0507 72
    0xc1140010b1040d016004034802110071580345a03040003001d0303080c05034450b130800103102080400000e0540c00f14000e104042c0d0400103982d03030420744c2040700c440c60180c40b600159000c0802960254800c0340034090140403000100c000c691035006400084e00500043c014003580409585000903101000d50046c1e20744200101128030031002140102c45840d96000c01a00070380b501c800103420840f41d030103440d180d07030110707070b6502d00a94050700c403501a504101481d004090f02c0761244d07004110000c0c144440b5a4142d04942c001c1c0030000303242403420607280d0120060500f00902006203649401c41d1000d01d9009030341c1c0c2c1d018500d13907140c021101d40c01000020000e0401141c0071407608800a002e1a9840c403400f82000b031a114142001094041080b16a1030505e0f4180440c1c0064804d030055500004180c0001c110a0041da0001d03011200981000e800c3d0340c0b2003c0100203480468100080c0c4000580d40202c91950799100c0c5034484c0030380d005120b014040c1540702d4411903105403090310040c42 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 714101276 1250 714100026 714100063
    0xe0604030b0403031506090b0f070516170106030c03080f090a06050706050106170402041d0d020c04052d09100906051501050a120b060c011103100e10030f05 69
    0x8aa2a081d884500305850a4002900d407400980c0400340241e050f5090740c0300c0c4d031144c071801d41ca480b540e0b05050b070200280c10141107040c8510070000d00f04000d00a203481180c01c04018035030030091100f20710007480d40e540c052603041910800114071084110380c240c0303420843d520391720036028064414070302c204010701d03801408280000520303a40c8040500b490310301c201340510142c4d91310407084400c01c0e0898040d18101c0100c8022800618295000350104c42c0d030003000441903907451880c0b900b440240f82000c00940c028031480c403454a02445103640c081880740c011660706100444440314648900701d801060601400031904510041151607021415980e003485245001d1400d540a468243c0d80d1020b82b9162400c9401a58004d105541144101d90342e603842800c4111444c002800080307201d40d8104200b0889130302d07100c01c2070148003900c91700310b400c1c3c50f50303828110042032031541280d0000e0100d49420062210009810b130080040300e40003400175600742c80c0e0382080740c203050300d91402042400 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 714102526 1250 714101276 714101279
    0x41b180b04180f0311010c050d09140f070611060f060111070902070c0302102a0c0308030a1e0204241826150a090f08070602041a190e010e0604 63
    0x103003224643e6412880381c0c0d01d149990040400311703802da5841c0c8010070040361060010000c288d04903408590110702802c180200c91401c2d4034100d04180b200f012246c015080184144016034000151441c4110040001c04c05440c045015031010400600031904000d0000c0d80882e1420003001031340040d01095000315a11a52490300c1c04c3ca011980c40101c0c05903090910402c0d00e03c0c000c290740703041c8203015004440c0010090210380820040c0da201200d00040322034001c00402c41000c05184034000e0200c001a07195421801907400c1901003540a6150707004100c18010030501c4498150301406005e0a02415090f420b025500d5208000c5114903920041d03200140c541c40315030902e20340c070b89292440745100700c065154903124010250a14010381190021949800059210900250203101c200d049102e543e80c0783d007070303907441000150340c100e0300880d06010030481180030744410034521008500c3d0084070343c0542200380900030724600b8808240c040d212541d0081c1c003003414503070000300555501d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 714103776 1250 714102526 714102533
    0x50d03021b0610050f15030f100f03050705010c06020909100524030408031b0d0b0f100804061a060a0504090609141605090d0308041b180b0418 63
    0x94000340c07241c030604140000000704119000c54894040d881d4481c8042100781410700b48000b050411071000d80242502d001d40111201442c065030091080302280210b0342003a0856010a44180c0c0040143d01c141880030400038000107041c9045510030f003000c42d044000e50500100900a06240d80d410110160400c00c1c0b010440d4203c1e02601c00440720026070000507410f90409100411a00c814010200045000b040d8990f0107968445640c3c0101e18409444100d1604150840440d00c00000d0700c030700c0740000c1d610702901414008201a15007101c034250031a0020080c0788003800103000507a07140001840e114040d07280315080300d0064000d079034907000c18400900e240d210b403080e44200343c41c0a002040c80e05441c02081040304000752003030016120b07020030b08000c0024900e41424003808001c40806c82c0c4a02c600040903038001c0d101c1e03001c103240c5802c0060750150942504003c6801c0039900344114140c0a448070f00074003e00c2c00000c0c0c1044020041001003010b400c1c0c1019000c6c3c920492401c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 714105026 1250 714103776 714103781
    0xc0405041107060e0c032d0703031106071e05090411160c0b09010c1401180c0302010e1009120201020a0b0a0e1606090e040624150c020306070509030307050d03 70
    0x405109960802c1400d000c042010b84803e00611016410f8010580c00c10351f819108a4020095500f0f0b1442c001d01e91594692a28000e0706c0d0384118040b601d17400d80314810903c10b010040d48100c650030400c4c0410a400c000700303948048240b00c607043c4040031921103132549480d4042180251040d1102da44c605642070400301c0c40710403420860300900048808107107901d4802c150b4002007010f849402d500282e959035180207001c000000c6600350750f42d001040a001c01810450780b004e0049100c00d00ea1421400018a802c03c1ca80c0b545004058001104910f2540841860104c408c03001899002c0e80c45440101d05000c00c409001d440c803500d42083c042c880d0501e40c0205840c1d46074200b1944403541900403031082c50814800c0d240401c051080400501000c00300d85540144542400109407074410400c4500c8124030408a042c4808000240b00061414a070910290114249808203c1040c1c1c002555200020000300400c0004501d102081d10200147c6039525408001e40302e115082402c000e00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 714106276 1250 714105026 714105037
    0x507080609010b01020a020609060a2a12050909010918061b020616090e0a06030813090f11091e0307080d09060503010602060a0b010e0a35060a050c04050411 69
    0x6035518120034205150700009800706c2d080e42c0a06a2402c00c0020803c00c007050b0806400042400411428518071100c0c14a401540082c5800a000c86a1403418003580031706500307171010706012081040d100c541d6035030004141140d581c000c1c04650400003401502905200c03500040c104d500b0100301c911000d204412401c070032217195085034030359541c0b840541c0358118281d22030404101d20306424001c407940c00520310351000704a2800300c1c41070b642c0d0740da00c0d6203680701d9000150720300384041051080c4050f81c0110185001c0300034080c0b0881c0b4030540600c100e8030030307814a188520740d406170b20011a250660780250041004040e92030203903940c608141c551010b8102d41c0001540c582c0302203280d034000c10503a4140c6a0700d50017040e40c0d58540c1c0d850001440c00402c82418400c0c01e1548420640d6a0700e248800b030680703400405412080445005140a01e41d86070401960005603034100e440000142c41c1d44c0083e0561010840f91100f8520515510454014540085c24044a0030400c55481d00412 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 714107526 1250 714106276 714106291
    0x1e0303090b10050904031b0b011223030417070e01120b06091302010819020a2f250801020304210807230c030d240515070f05070806 58
    0x2003555103400b0110181e5000d0300a203540651440c0203e0301007445500c04a665041c00c2241d204506040e07268003940070000d034014031441846007800341c10004990300c5211680318000e1000303420340b00c00030300e5070300c2e0f001303d0003000643d007840c08000c80c10f401c0c00c0060b84c0040000c1c18020009503110380d41315032441018607083e981000000d01007120303030030000c0b115031052540e10b8000307805100c0d0758011aa03866024281b10041e4800c24480c0e0743d002c081348014139103892191101d8110409002555803d000040c0880300002c82d07100c4d0715840c6000c0030641010603001c0408038682801c42803500003551540360842e1107550b20100c200810810700881c0343c400d0b40071004102009000c10a0f045611041c1143c4540000310701c0d00b00e021013042a025400700c480429803545050074000c0c051140386401c03400032240100d486909200b0303440c0e10629110700c440302034605100510704100101d010302941e81040c4140900010f01e4a080c4078050520100450344103050310700c01c65584081ea6a1107800f50394a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 714108776 1250 714107526 714107543
    0xa0501020346090b0304030801090b04022209140907090e030c490f1209380118020702060703030b010e19030219050a060207060f090506030a091e030309 67
    0x32440140040517684140d0b8036560381180c681c2440013007400f1340000c514140e00103400784502c080c500944401c00d00100d000344407030903945103000403480585801a4131502c180d05000d003481040d800106094041d600c030b5034008144400c2c100d40c1c0d00d18521070312100202c54043d911400464030b01d0783d41403040d10074440d031080c3d2507111025207088440810005408500303480d183c08044c1c1030b000d40300601c0044601d080020200b501040b0708000c2c0c441035001113445100328001d4003a440d5040d0328111244480120003c417101c2d8101c0c02055090041c003c8081c82850399520842e1603425404881c01240c1c061300080d162074407442c0c09805052001c178042d0110306450001103c44c14480101ca800041c90a00c064081d495a0244601d90010b50280d021040c03069501207082c2c1c90f0300082100400866009202842c502207004100018080340714080200145082016950301d4054030707007004039882e00283c64009840c00d000c101585401008801c41809240e0781803507003640c000c00c0e125004d0980c2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 714110026 1250 714108776 714108779
    0x5060103061a1c052404020411090102030313050a08190305160c08070c090e1e0601120b0a0906050a020912070305190f0203060c180a050102034609 65
    0x15000c0ca980c00300254009224032180f00c5403074100a00c01c12036a01450a5982c0700426580c0d400079aa188581c50846000300014070045041510a140d410780c6001c090381d040440e081d000035102d10003d80303042544d40b4030303002c14000d1020500c82c8203107803507001c01d946560b200c10751041d0b201081941000408a840e080c000740880e209103a01200514865a800e0030004907551015241d402003003041d1a0400b150502040801207403013880025114000104010750203080881490b0385400c0c0f03203e103e40c010754010420220281045909241d111002c1a00c44d540c0390f260400800b4540d001900704c4e424602403004c2c0e40003070390040c0000c5000743c0303100c02d0411101c10301c02e60b85c031061701c4000c2c07075a84200140c5000900c0490402e102c5072040e01d003500c40c00c15a4000a103442d0041d510345190010000c1d0326590200840120303a04031800f0303250810708503c0e21001035181c1c010034801911415105148040203410441e00885200c0300d80e0005980003c50f403498030880e030500307170200089000e1039130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 714111276 1250 714110026 714110051
    0xc0e040c062012130308040e010f06090302060d020c030712030501140901030503030c03090703050d05030a05060d030c0b060a09050f180303280902130e0d0905010806210a0506010306 80
    0x500180240c0b50700204000714044085070304a51102510000b0718007841c0020000942540c0203000801450911109650501c3c0000c00e900341981c3c440c40170301800901c100016103800c0c0540d030350700c02c0140f00140c49030611040203080d0720920b90001d0015902114154009406503c524140c42054440e0307406490084107000f040c036000e01001c0c007141d1013480090980c07030b2520025a8480720300002d540d41d103a62503481e070b45450000100940807850200421014840d180720301a07010f4000c0700c03402c4d5021215240903014604442001c2d0100c510440091880c0e250b402c0880001e1034210001c0050b46002d1707000802082c3d041da44000f0f080038100003415004000410b9a008070074880807901b0203280c000f1211401406514550030554452416202590780c40841459400080d200402d00d81640004203003071011090000043c003521500c180303c9070340c0c4010750a901c510251030303001c1e8241c801100c0384107480d412400501c0502c01c0c0d62444080010125640c0c0c101c0344201000e00c40242c6090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 714112526 1250 714111276 714111317
    0x82505271009022107050a2007081501060e10120504060e10050f0718060c1a0106030506030c060a0e04050406141303020613030c23030406020c1207140d0c0e040c06 72
    0x601d1f000000703840703a483c410701a01482c201c04440362003000725803540380d0f944000307800d11091394002229208400010840319400565a261000c011942c102c5181c209810140ac044031141c0c0c0c1c0700000e60f959000a0030001513500c007140f414180000c0f40c41441c1036080d0300c0082c5c103084031440b600c44031010100d40c4040c0140b03461031003400d00e0701180300b00e5810604126440200c0110545507c0c5100c94161640001c2007010360107001c190368003061500d0803100741032402c0c483c440b0325401800c0402031007503000e9000c0038001c00e01368101e034003061a03111414a400a4500c00f038601c811019030303d041c0420031001490750201030b807103502520400c0d0b898901404d011440c0301c10140200d4843d100d40000030b86610008909a0001c90400c200b81c0300f8461154130b5a00a42c214401680c8584c1e00812036213811090600c07a191401c0c0103104c81400e12440d4840310145441da00d015030402c7e01c2c01c7d000c0000452400000e04510461500e0300c3c503103803c1c40c0c408082c252180303401007426181c509402e0207201 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 714113776 1250 714112526 714112537
    0x7090b310f03020907030207060207140f0607020717010f0e03090111010e0d0e030a0615092016080408030a03050411030c091f08250527100902210705 66
    0x74030380d403070000c1c519000c1c0000070380700604410130075034208040b40014400c2c2c4043c200c014020b840b102c0c3c200c08100b000c245407200b40d120b2001030344c0c480700411103010740c00100300c800e6421101a0076054111409120b024203041d203c07001300c003401c01200030f10100b0300101400703400d10260398410303080c545400554203c0740c0c40040340c003030794100c209941900c1d809200810364250029084403c0790311161940b100b00c4110f040700303c4211007002010030010130540521008240000070704480d52025881f414043c0c0b0a0042c40c0511003410a8142c0510031490180c8005207203103425240c0e42d0400b4000280240000c4504840c03c0140f03450030340c0203090000d040d031f01c4520041d04060060b05c801001c0000d040d44c003d45951000014030012035080805c2c826180c00c00c40240400c1903510300541b8680300380949420160042c0300600028107812442031400d0f24a001c10107002c0c20f00d40390401c404102d481e0b070341c10100300e440c00007a80d1241908100d10210400d540031440c144581c9a4810480d001c1c8a40c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 714115026 1250 714113776 714113789
    0x30605120a031d1c06050601050a020c0d06060b04080f120405132406030e1c021002130e04050f070605090d0605060d0b040b0108160e0c0307090b31 65
    0x1081e24100001d0044060715003440310710712140000d00a90b0000f840c00700c0480f0704071450f4046071180c4010003059000e0650405000d0910a09104454030000e543d0b80505141611920030081e5000c14007010341d1020002d03108131030006513031300c2d1144103590b910100325810600c640710f82c0641c02d01e00300401c4142c40507564020903484110801c8515440503245112200480d88042c001d510751740900c04d8940c400801c80d541780400c0d80e1911004160404d4440c140500b0910242c440e4210403d9021030714407030f03102c070b030a074010384a5200107110394000b5082c1e0401c000c400260420b10050100c001410000041c0b00c100311129542c0703904d801c0705e542c0180040c90b5040048060500f002849980120707900c5100644100010f09058442001061003a1001c0d100a07494100504c2107281c1032080c0c60300e20000400031a6414500a0f94040703003100101300800d8040003001040441d0310030b80c8184000c1018109036926450f500c10a2140c1025400c14000b003240c1001c01075a6180d40c01c0036000440c0c84 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 714116276 1250 714115026 714115033
    0x30f030624021e100f0506010c0b040c120f02030f120901030f0f0c030905070b0702130b0117010305010501090606180902070314160606090207020d020f0f130c03060512 74
    0x696460410315241d40c55070100941c0148924041d5030003200d1000c600c40f8914900070300b41006200d01c41811218403c1850031000d050104020780c3e40d0300414901d03c800d078009030a02c460307941c5003003ca058004c01e0300511040440c99004000780008004c4084081d40201c0c11b450300d0900100803c0e65649048203041c4689406004520032036001c0d0380704a5500b000c0c81d8001c102c039445014500c088500250390600400c2e601c1021074207202042120202811203100380b9450300105400290899503035030841e02006446036115822644101d00801d05266a134417000303025616854554060701d4240034510983c1c3c0703049800039210b40719a050100501481c040010034034209550700d4040d5101c50402c0d802d0040501500101c4507040300208181580018000380c2e40300780345444000d80e0802d07031105000380e0044c001a030140c0d603003080d9144540d6040b10b400c2800300c00700c00481c20103500f06291940c051440401284450040d401c00101c00036580d4003004450b40303030420083c0d0030700200c00c0c444080d032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 714117526 1250 714116276 714116309
    0x50904240b090109270b10020606060d020403080a110f070b0409050c040e01060c0308010f06080a0b130f0b0f030316060b0d080a02010e150c0a0818060f0103030f0306 73
    0x50010006000b2a14189024040710341c0b00c0c8a00c00848a02072011509001c4816150b50340f08068072440d88130400c100c40ca40401b07d07018000959404018000c1407041c40300155110171981641d04460003141e00000854885001e00c501a0010356030454103541e80c080c1180c0b4500f4803801043c4902a181004211404c2600f00b0f807118000740f0005241c0c841400c0c003007001023014641c1030320007402041a9520034586182500c0c0041c24064181c0c000110819100418030950fa040390b0b02a900c14121a0001244c001e403070000345c0348504041b02c8c7e4012a1804140d420001c4681d003081403d0042600c5000036044243e060550307034401d00180f001c03e88000d04c0c0c00300000d1155001000f4202000f01007030000c04254490074001c1d4000100600540e6442c040c00310032030307010b0200142c3c0080100002d111407824500d45451481203291920410030001d000507803060a050b28400e0140202044401034500140344a1007000d003070006802240d2425110706171180309010340b6064950110320f215124 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 714118776 1250 714117526 714117539
    0x5070305090304060c230a080301080f031305060a020c10030608010506120606060d0b19030b070e0a1413020c0304051305061807110109080d200a0e0a030506040305090424 75
    0x5031101c0307901542d041141060031b0244c1c1c02007140003004d40c02210340c655603516002c0b2452030701c24101d4950420b81c0042c80f084821002100f101000c8074402d40c2c6155070341e9041e400072401c18020b0300c1034a60000c40c8104408a143e4154405410340702e40303d00801441c2c9441080005615030300008034540d03070206001941d41e05145000d0554141410400718501810000050403045881a6098413035122281003060118140400790000d807039003080303c40341041201040ca24072090040032170031007021119035103e444860200e8110030340c0b54403c64440d1070a2401d15120781c0f061103018802c00d00142e80700c8049005108241c000c20004014a030015422171000c4680440148500d0034000e907014520b559000a0194005440c8603145042c0d540c8a940010300446484401c2c1c9400405444048260100390700201c403000781d040e003880400b2001c2c80c03000035140141504002e00c1b0780030344000d00c01015000b101810030720000311007d10a615020f0400f072130301039400038030f41d051400760a02040310 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 714120026 1250 714118776 714118793
    0x50718120314070b070e090f0f06040509030d021c060b12150111030703121826040f0603060806010b0906090d141902090f0108060a1113030605070305090304060c 71
    0x842c01030382940790814a10752100403035001d00311411000309a4a10004100389803d03d0400d6110b603600d010ba074140e007070101610000400091101d80101d54400106500000420656403500c007286000d5542d0722180c4201a40094840da8054200e802c10380045010040c86068440100545000c01e400c3c6e901c0001100402c030000301c0c1755042c000b4081ca214221841032000b441c0c018020340303075404041d1755400004100c90320b00320485100c1282d8501c10700000c28408030f4191039241e214080c04521081c0e5001d020620443d4000360144450741e60006000d0f425800040031585c16500740d959a03039940051540501c102da04903584108100b11002152605480482c20700307005804026a0040c00c092452628690a103c80d49490700028a02e0451030800403180c5d000d0b8102c0108112540351040003581c41034081c10700140300d521350959409480b0006c00341c907030401003216030307254441da2418140c000303002c2600c6802c00241048002500e42d0000000c480c1290754954950990510b542c840488 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 714121276 1250 714120026 714120047
    0x30e1207020105131403070b030c0a050c070f080a03030f0c090306230c1c09020901060c080c0102040b0306131b050702010e090f0105100c0507060c03120509010507181203 75
    0x500030f051100780300c3d214a41044101a001c80b207001c44214811104140c503050003a4000e100c036640c10410010200080c1c01550350700891818030a48401d4440f90141c00c041d1260490403c800c0c0710400081e52410002d1580c05045c0691001c003c0e40f00c00c0d011480607a00d24020f803101117070035905c0130400220180c0c4000140d82403110390a46a0304050041d08099800703440d14054a00046244612001e050040318000c0851040810643c400c980c0850355545052042d407061016803035449080c0200c505c03c0712441c0748100002c5603240c0e1200c0010400d904240d405500411000c211400ca01c140b40c0315413440188949001c48400c1f107062000c0b42e003039001c00b00482c10004100e090809a4032204a641d005118a655004c5650306080c1800210090a081d0208215802c101c0101151000c1684020742c0d5107464a050380790813a007410742d0f2003440c080080c02031900d488100101d085040d0b1100c0d009030240d5070f618194281301c81651510b0561401004070500015070140002030083c110000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 714122526 1250 714121276 714121279
    0x9210207050f010818060a0b030f031c021c090503040e07081b090a030501092006120604321006050f0906090418050c09011203210f1e0606030e120702 66
    0x17511003007019054208441501c00c0d052251300c403201c66410b41303803e00904440703421000c02075060081c0388d030b6606860b4080590003100c01d5800140c0c05140070076480c0000c2a0054400f00307104030441c515000b075a9500902ca00040c10750b4940104014511501e191030107008140307a031114004140640a000e603102d031091311307840540c40302e000001400c280603031501c1d98000d2030403161161828580b410003110600b0301621440701004604030104500d25540e400900a4400140510031003902029526640c070500e4140038400e00c01019034403110401c507102c2d8040c1410b02d840d8a0762031806441c80d0055100c000c1c60703400f00b84450021401d2500180c030140030018804550005140c6003a11502c03074141e0187d600f9001070030384d01498244001803900505ca059081014154982c42c01800200301c0b030311f115064420556030102d4100e540c0c001c074013920388018040180d00440804001701d124104901003049040010004e10103000c0d10801c1c19000505026288480c1070a42031001c0c0e5100300c06c201d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 714123776 1250 714122526 714122551
    0x190902030c19051c050c030a23030906030c03040303060927080405060f04060206060a23010c020310060603050f060d0b070302270f1020010e0109210207050f0108 71
    0x1e469560130a5085281452103100c8010f564600f40642000300f04124540a1390080c040322000900f1400524240030008415564420030710304040d0551080d10000756110501000b4428003a07600700056009030721075142002070540d5854024251010040c1d550103c00d046540c0844d11501e440c2004003941c4034043d42407409423100e0016595810003500c404c000318010030207105141d01046030300e400000440b0030340c0c501c5140040d403240c4c41c400c50350b60324940030710422450041d1b406125400e131040d5000f025a6a03044422038a50000d01c49481104002410003010884100115042ca4001c04006d07001c4c00e0210030986501a600e0405410142015403c2000310134409e620300d1a003614020398010f284a662001c070403c0855209444000d204035500200e03070000c1354001d44a0b134141c001c5943c0c00c0c08100004100c02d40148944061842e4039400d003005081000000811602c0126581ea12801018001082280e48615074007510303800503601c030364100c142d6000d101c003641d200c0c1415a48 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 714125026 1250 714123776 714123779
    0xa020703050c030a08010302031608060403050d0b1201021e090f0603071206060309230723030319110a080306010309082b05150603160323190902030c19 67
    0xd0b41d15540c450625040003036100c20040c0114a004d0145402602180007d800da99081c55885a00c07428003620090038050000b5107208080103a80200a011000600f800141a040503e0038044e600c4220100d956512850f540c104030162401a10311a40c006810110790340c0160f820b00c16a40d001503d07000600c40314000008405c0c102c0d01428010b84420340e0049801c1c2c405240c11120030340e9803480242810b402200d21880d5260005881c000c0742e000310384440101c0743c2c80c80362562203203011190a826000000f01a03800c48500d014a80300b02c0000d0303036801038140015900070785070075103c00020301084017003002c10741d20740c0700b600f140c4801800340b010715203401c42680c2c01500107500040c078980211051030451032000210303c03804c0c1c1c1c418134442d0001500c24464000030403501c00105842c01d949c114803011400580301780e1200d010b48941001c9459520a41c0006d0544450201c42c0b1100c414011050702685600314021050410360180040800d000c034242003111041810105846004601c1c60 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 714126276 1250 714125026 714125047
    0xf07080a02090a45020319170403061a040209060f0d110a020615190e270f0c0315040206090d080a030228170c0f0301030c05031005060105030a02070305 67
    0x244441d219040c121004d00148010300140c401c60055240c800510080000040150710302040b8450061441900200100440d00d0009006000b4507074242c1803a10102d000300800c13400d44e0001c9142104130200c5200412000104410b900c2a1080036801140900c070b00408186040301812000c2081070021801c02a07000d440109900308407400c80040e0b01100a0114044040c060a80200c00a0707540e102d048402e0500000148510701c903c2808500e518009981d1b0740c1c4411501c1c0710500d040004a03007090b80519000d0341d0b078842c901e41004ca8010340b00d94000d04e290004100c250840803e044020035070711a000c000194001070324042e045032103034131414001a0800002c14500000d607e0041e142c44800d0060140b00b800c1501e00c89044403c40c4142d060135400c16103587c08805408107084056441c02d00801c03042c085e00c001ea0701c40d020003000100812160001c01801c5c0d68040d42260031704a10803e201040c1c410a41d0f0003808039404201243e5058100d800a015182c002c0c100103107800e41406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 714127526 1250 714126276 714126311
    0x290705100209010f0305060a0512010e060702150a15090504031e0518090103050a02060a0c06090c0504050a0c0f1d0303180a0602030a05090105030a0e0a0f03020f07080a02090a 77
    0x400305030000e07030000b41d456043d038104a204030740c80c110386010401c61a09002045465449002d582d208054a0001030034901c0e00f50030018036013171144e00741d0b01c00f420101c00c041d40c1c0d41d585070516150179042c4400503e004180d4426114505901c0000d41070251800000c0c40013000003910607000c00c0f08101d880124040c40010300c42040510303503505a0f0711928a035424180c4541c1041c100c0c8075401c12001000407580000b001507802d501122525a100b150440644890025a000510042c01c2034100e1061043c2075004a0071228180ca0031700c27480d914190140110b5801c0c5000d480455501c0b10320350070030362241070703ca0b40303181c445408403040d601000300203403441e044040141000002d41d0f61510560038906d9400c401040c89000542c144203d5000c050000d0050b0030800d03041090110000d0a180c0264104501d00c800e00401d40e0000009414100c1555840c0321090f0050b1207040e4001c030034120005800c20442d0003040150415241c9076007040303c04c4c60060016030300d041d00c41c880b194042c0c4038070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 714128776 1250 714127526 714127543
    0x170d02070516080c0105090f0103060e2806210221030c07060c0506070e030705040c030203070201150f120c050316060e0109030209060603090f03270604290705 70
    0x724018841d6021800310302c05040000d8122204035085404d2000300390b600b040598003020004c0303645213007110707078800102c006014a81c0011040500030041c0301955442519100100e03904081c61104000345401c2d20061f02e04030700c031706140e292000403014400700e0007100400c2c10910040150300d0b0030085400106145801203c4400150800101f4200d03540080145c00d00a002c1401c1052080507030351103050700c4000041088050007000c20b8089041d40c1c041c4045009000000d0007040b650708403800040c0250012241040950304c0d0160105000000c15244030440d07407203620105200c0c0c2020f000981021000400f00d5400c00e0503040810745903018040040303041d0b000d814120215103070071001001702a2805065041c08000d040600268941c181c01692203001615881e40d2600ea0851092070103088482040190002040d4441184440c008024082000c12003410380000c04d4030400c190b074810b61103100c8054248262a10403005d000540031094002500300604040454841ca030915680c0b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 714130026 1250 714128776 714128783
    0x3020c060414130c0f120609020d060509100509010b0c03070b0c090310060e0c0a0203070c0b031e090604060e0f0703080307120203060d06021c02040803070201081b07170d0207 77
    0x1609107942c803500b030290711031150a503500030600c030780000040c0142c8040c881d1001c41c02041440443c9088120054003c1740050180d42400c40da1504602e410400400c6540507071803050110320301013050008510202c5058920003003419a16074a040000c0303a4039400044e8070015400f05000c1c1a012811010802d03205215121035699135040e003800301070810004c00d41400c102454100c050214a4155402c164440810450742e9510303004000b09034a1030240072401401054903100200ea60b0042030003443c0604010210031440e0f140000718401c01c0a012948503015910050018020450300c0c0c216480701090f0384240d0350200c29280c0ca4905040103508140e4400c1000400c0c070803040d0740f000d003c1a160648607021821410500c001640d030605080d0007406d0250041000e820384060844842c0483c00403c5045640c0d40c1d448a00703685a8100c0c54059002c164103900190098101d240555103400d01e00232928984917843d034401c0300d0b202c69100742406414051040700341800715032000784ce04501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 714131276 1250 714130026 714130049
    0x323070b030a1107030f1d221503050a020f010c140705040606020106180b0a0302062b050c070308070519110d0810030836092520070e040b1b090103020703020c0604 72
    0x1241c3d41e000040c3c407849c0340c81d0034219614943c2040810350200741500c090380c0c120b46107400c000346600122411384c85104041d01c0d041c0104045500c01c440043c084041b9002179400384842a034803901a4200c95580c400c01c41030b00501a001c10035040190f101c80c00c1250003c18407075000f503e036008a0b0300743c0c1201c8180c02840425007e40944d08036299900419202e607640248803605e40f0120184581c0559680101403000708030208034401d024070181c03201c0c2500c8a0441110345842100144060707101b1190400328018004d04069446c800c030f81a51089000400c03501c509482e50b5500b0b00700754041000c00c1540100180c0b50364004990f401040c81c030580c07800e0302d034080030401030422400501c0030341031442e040910340c47c82d6000a142c5103040c42c99511400c004405001c5440f440c1012404030003022158010340401145804c8202480c90050303020b030440385c5041c2d0300c3c4c10820400c80c81e06421955010428445d07502958460740062031035511071300c140c0d03aa01c01c072400402c606402c690890011103a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 714132526 1250 714131276 714131329
    0x100c1223090721030f1107090509072301140c03160b0613060e0a020c0a1b1e03030c0b1e090c01030c05070209010323070b030a1107030f1d 61
    0x9035228800c41c5156003d0701108111040340d0f4028203083d10340b140c11802d204280c80601741e280d2050148000411003103d09000c141b429890140c0c40f005c6502440c1c503015000903400110700d908440f042038001c010b0b15070700304a681c0340020204c150026407000c12144810001c0b07480010318041c1044201d80304002040c40ea0400404003c088506078080005151810804105100740f400607140c105410100c0165180302d0650303002d01b400b0b045c21000d0300000e008182032848440e0300158400701c40401c1184406c521741462216940402480040e000902c80d4115402040103501101e03008200700c554029814074143ca50700c0c00e1070048603441d88640004d5004d55080d40c01d40a036403201d003203924005240603801d6001604a18040c0009081511030700c400c502803130071003c2100c01541480c01241c000b550f0311074660740d070343d40100c0d9200802e40c2403c02c1240342c981c1d10301c1541c4525506d07440d4084020305c001d10071680003034603080100394051100351060480d1540108404c03610311a08030b00c203811 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 714133776 1250 714132526 714132539
    0x503130f050907090303050c01020f18040507020f1f0f0e15161e171504060e070f1d060403050703050c12030a051c06080f100c12230907 60
    0x20107500003409162036800704601c190b404446442a640c0c1030614944921003410004e009001d448543c5010000c00101c9101d50142003d80700300c0450112001d028503aa0f041e0103d0b10f41e0140d00c1101c05070f510007403609461101a69004886490b4014001000186140700030700b07588500f0407100480d040210003400b940300303541005d54801c0001d94240c00c13084002c02c008180304080039000980000c220f280303c02c1c0601c201305c040b50b4410505102c2c2c54905046010b0342081c030b50201d90501c22803030240b000540403030001480740300e41c4250f101d09150008004041d0b481c00b450310f00d410b101d91240d9091000341e6861402420186020300010b00c401815850000d19000b40003490501c01c00e02c868880440c02d4000040710400310040c030344035485440301c5665880480803030240e01c0000b418180085103a22000614882c0020840704031217041180d8083c003001ca8025014100002d800495000c03100310003038020900d80c480903e00c0d102036000e694580c482d550310640e21043d46400024080040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 714135026 1250 714133776 714133799
    0x60b07050a0b0606070f060c031b120f0506010e12010207080f04080706090b091003111606060b03103b160e011b03050408030d0c09060e0a05040b010c020d14010c050310030b06030a050313 82
    0x1003314100007000349081000010b01811268401d942c42004403688840b50746d00c00390103031040158000405903c1d0002c2c1d840d07032142c0381c00c1030084024900c9685000500d2500c914081c2088030304001180d85440c10700e10030300c0140403040b25a04145030b1078004c07240c203415002c0c00800b4600c2c880288401081050725041003038507110707400010051014030038800a041805500421100c004403007083e00c65181401840420501000310b4801c0541c80a196040c04200c0030144070300108210030b442049071101c25114030f0003600c1c1c65400210051820803120200c4242000c08500a04119080540da400c6a42c41d5502c0075404c1401c0c5502c1d080300a03511078012000b00080c04d03040c2403860480d682440810580315481c86914402c9482d00ca030400e85902514250220b00c1c1c01030702c103030306851403401c117440b00304c0180140c0345440d840c25030645221031007001621b02a8136014045400f0914644400340401c43c040c122039403500840360000700041c8208010000102241d440c80c0400307140c86c140440 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 714136276 1250 714135026 714135041
    0x30a0b01020a0b0c2209140105040c0818010e1603030f080112060b04060302040e0a0507050402160b060612011e0f0303051c060b07050a0b0606070f060c031b12 70
    0x41d50720030030030300d03000401d589034655210134544071103900e0303c2c100000041c000340040d2010031400f0301441d010500300c145400c884132030707580019841130f1643e82d58117110480e01d0f5038441d80b0004103080d001c071390800c3c002c840f80c51026180700300109403204051400341c10300c2224031001511280d00c1c04100200741d002010f8048400c0c0c203061540141d03142c88a1209080c0100d4401000d903a07076a140c0c69543c0d80c030356115202458015204204450341c101e0a19a9401100ba095850b8402c07190001003901e441e000b01c91004043c5400c91581420f80e5680700101240501041e91001090000340c6c045010341002c18006e0807000c1203000d00314001403000700c0505c03050300728802103d03040c00709202003900001110b46142c01180001c04104002a600d002091250410308140300b001852106104c0e0000c0c13010801c0e4018004140039031200340410034540320301b05000340440880e042400104a040e407041d4496440e5040206488031a17022040340c501d02a03100c80040b485030740c803284c40000f442c46140c0b0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 714137526 1250 714136276 714136279
    0xd0201020306130902032d010501080f0a15020d02120a05060f1804023105130201020c061b010603060e06091b0d03051b07150f0c080304050c0a0b030a0b 67
    0x1440d500b41600400e8075041151000640c843e241e503200411510108155036440004d111b004410421078039144641031015849034240d5800e110011601c0040410820181c40708003004141e00c0e10655940000a042d0a104510a076428881c1103a01842400148144010ba80c2800d0b0240b42840c1c2010455030007401c00344c01101c56141b071400d01e403034034034103160f251420002e100020360301e074400182d221410180c0f0300c40040d16050481c40b800d0b0002820342921904100520055498041401460080200190040e40400644241c9040100040c94406114014080008140300c1c0e824251045580200c0703030b05a075002c005501030014814550064210030140004c6800031400024407000021646c0c03143c80d03188580000c040c00f84d000c0358030000d410912220b00101e03070614640c90707580e14410b00c003100d114002c24500003407260115185200250305c0e0940b512210303403200c0030b050b00000d008882d6441907118001244e6259080000141038030542c1f95540e1030100103c0044c0d8451484c1c1d103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 714138776 1250 714137526 714137531
    0xc0f020715050304150912030506040c020a0203030a0f0c2f1c0201050f0d06150f1e0302070807050f0105041b060801050d0c1214241306020408010204170d0201 70
    0x2a01caa80e40030080b41d8100781c020101c1403080c4c030800d201130300030091298024420406c85122181c865090380241e40302c0e030002c030360030041083c8500050381c9035200000c00070f50581040010100440c05007130b841100c500d1500c0c151880440e15600c0903048803a50300c9030f0004544105a80c0a841410340c00110759400c20384088004042504a680c401d02902a0003410b0140119401e40700c14074010948164401654040c42880d50316440500413508072090b0200003a01e030707640c4d00e40090107007208802104901030300d20030340c0e510500c080700250440c48003124890030130405000401c80030804044038402d000000909402c00b0318111440101181d14582c48182d50700f000c00c94a60040384840c1183c3c400c2d140a0b01140b220300c0c0c081a035030b02d80e0300250740c1100c2585a0609105041c0604118100c809080303c4604c0c01051842000700c040c00c101d2030004014000184041240c10b0402140500c5000054141a03c03080c410342640c015803c01e00c0c540342d4148400510301002c204100d40962680004c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 714140026 1250 714138776 714138809
    0x1505180a060e0c010507030c06052208041706090a0303051f0801020d0c0207080c0114120103030906110105040c150908071710020313020607080c01111c0b031e010f0c0f0207 76
    0x3070401c405139040640027942e50b20000300a00c020750f0707600c100740348078100c0c40700341e1041464000c4964100380190f40601191100c83c40e6614000603078035000d44281c1d030082481a06690b03040340a024001c000c1d003404031042d043c4110319113200c0780764000b912042c400980c0b100700942c848400c880c14060345c1c508661010a0802042ca408280c007881c0036420b283c54000c20600300b41200c154420320505900b948200700002081c107a10400030001d03201940d54008089040c410a50f090317480a58002c0c1c40010304100421054070000e0f0501c5424109041206140b5980c4e842d05042980035407281d006d1030b641c2d01000089030003c1c0046a40d05050344011425828004000409032210020090145400080a80510040f0f42c1580c41ca02d440d50001d000440c00400314000d40e4010980d481038040f030007440c1441440d007502920090443c05402030110f804240d520789030400b40212140c04555892410140c24240c5002e560b024041c65210b001201c0d400d501c0c000d00d0440035600400c1c614944481 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 714141276 1250 714140026 714140033
    0x603010510031709010e0d0309030213110d050402030c090f06010909020f0f09011202030a060906090c0e01050d020409050c042409060e041107150b0604031505180a060e0c010507 78
    0x2280c0f20b04501042a4540c018500162104510052400d0b44592600400c60406a00c803480c801541d1090303440d46004801c05940c50260780c00740800141122050060202d150441e5014035440341c001000c4508452002d00411130414040daa02c5140c0c1c060b01e03003044060358104541d0320003445125001c618014020341c02101500884111441e1030800148104c8568410302c1c91600201c0c000d242107517a401d01d1094440106124860180c48a0403e01c000030400440d02c210800c200464880d10074002481d40110381540c0100c200000b1190709000200b2100c2a61003403a115000c01e13003105581ea0f0404440b034200407800d41540e0000403101402d24400c07644101c140c0704940c41030920581480000740010045c001c0c04103400c1103207202040140074001e107003e0310003140c044130204000881d100418040079104500024003110b40030545103880c1140707640955401201c0c80550f19103104103a0a0798140545000300f40c03200c1d030719807020500c001d03024013089aa40c1030900303205141886907038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 714142526 1250 714141276 714141293
    0xc05070e06030c12060712020a021b04200301170c032509021614010606020d080402030a0807051c0c03081f08010e070e090a0308011a070f0b060301051003 68
    0xe8a2409100c620100d542910200407880c03640704024074a003210b8000c65a080c0d6112001c5a051002900105001010490b42d208403440c01c0d03505e07030207400381840a99101c0403500403441d810750040d90b1912400901000010003104182c5070380805c96903549020644120200011420403079904551320029240d5400a0001d900c80c5165501d10703181100420070a8002007242e100300c4480d400090070308003008101c031410000740e104500c041d200304034041c600e0742260160300451000d41e008450407584c05004941d950f9100d88014101d4a0348407070f55031441855001031508131101d6100b054800b40c2084042155a0510171501c2c04600105245d1401041c605000d07000c00741c41c014003070162a241000650b980090303c0c0d07030002808000705060156540e0402c510600c1e0301c096411012403001d54000c80c2030401c8640550711410a80d0800c13101e40004030058000c000d00c2e04c410000c040000ba580044582d500b8000c3c881414a071070b0202c24582541c20082440b815000c021b2403c3c03000034043c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 714143776 1250 714142526 714142529
    0xc0801050a0e011a0c1006151106010501030e0a0f06060612020c0a0b1f030b072c151201060509100e1f03060e0903030412080403050403020d0804050622060c0507 71
    0x11203040115111410500c0051145480d100c0186c000c20748400e588064542200b0116076186a41c4110f582c000d03482107610b1440d5a02d9420b90340c121000412566110383c1294034034941030b809445a00205030781d190b21012100a00322442519803c3c104140c50300113004607040030b50007009501d410714010840f1b84a010280009010f071020b00c0110700300700c80030b070b0101007605030300450441200e0312820512225107044034000d00184030104080c1030224003c00c250a00e07402020b1190ad21036040d0100000c611004c0c8100750701150034005038001c1c10700d0f40407550090a03d503d0701583c881480090003011441a04ac2d2018085c0f003840c1d164241e2180790f9415110302030000311580050110b40110054005030340300517400c5894409000c410300c1d0100086001e580700f4010f62060342d50880d0203989003001140c000d004100144820400b60a081c1e0540300624803c1d00380f14609078032000016555040044280d484ac0402003ca01c2c0d80241c84000c200900090f0138640059445a910382d0703540c89a9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 714145026 1250 714143776 714143789
    0x50c0a0f08070e0d1406090c0d020d2a030201030b150703030f02040b0a02010b120a050a030f0311042702090a0b0d0e0a030206070206060108010f0e090a150c0801050a0e01 75
    0x2410000d60503070f2040b1143c1c0300204000340400b07580002410078a840e420580840012070040c0d0b0081040c43d0030018055542e0740026014a941880507004c10000c070400b414156500e45402c01d1240c00c4039007502408400d150400400c0611504500004045500c0050114050464110752140c0c0d1000c0708296a8a2640741c82c0200b075584450441c2070103400b89900401e0b03034400100d00d0701c00040c1c064004150140068035080840090418043c0d6144041100030704a50404400d90000c03900c00c84252181e4821818045440440040c0d81d56059106504c01403810544140040000084100b1706002e80c1c40c80d01d0550038030316180001816071606100302000e0300800203030724100340c002d0707001000064084400e131a40c0c0140740c10301035100d48013102c1c0d446c014069100003400c02d60042a815040ea2501d0928550700e90401c03a808158030000b505101841c4039100e08540000e8074070031004c0342c2c1007044c0c40215586150b0078002c0c1280d24107800080c0300d40400401404404290b401d024110745c1c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 714146276 1250 714145026 714145037
    0x260904050603160b040915060f20060403050304050d0305010605031f030602030a050615040803090904050f0d02030d0b0306062b06060e100b07030c020411040503010618050c0a0f 78
    0x81e04400246445220b011440084400742c10000c2d954007000043c0088521081060190011107054070340218924007400703011401c11120a020f0b544542c4422100c0b0b244001c005a04408080941d440c0050441c0e04030002040007007000701f040001c1c0320400801040e4202848103506081020301a40001480001d00504c1018154100d0310304140c200020354000c801150b49060103415880034020071130308907005168082c083c040c0c150030f44003120115030040001c2d500342a810000c00803400009002035070244240d00550003494406d0042d501404401d800031a03480328450145410744841140480c881d812420411000d61940c00c0100151001070703102ea900c4107500a1054000d80031208081d10841c40c0c1030f0701185688140c0c4070075005440403461807004a0f5120b2401050307100d030060003000500c00820040060030030342c20481d900c485c103940480c105030303d902c046070842c2c40c10386c0300f0a442c01840e0b1001e0340c016114803c894003c10404181c2d45000c040640142103c200110340d03070308000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 714147526 1250 714146276 714146281
    0xa061b02150c070602040e04060b1008060925020109030f0908071502070810061d15091513060905100b040b0307091805041b36020403030c26090405 65
    0x40d50a0b003201c0b90107600000864907075444070075040004104640440b201850803001803458600211000d8950403103940f400130a9882c2024000030348809044080401d0600545580181100003083e00311402035000092421550600401c11941e44054006015151002344a081408540070042d01d050358541c040c11076840c81c0c1246040781c240d104000342e0040800d4141c1100f4550019421904a005400c2d50014a550640e41102007654411035041d90400003027540d0412426059200c4015040c00c00c07540d0017600410828010101c0410a01c2c0d5117101c1440601c1c0a0710506820000c1080d180b071080d03080040102e40c1d0f05c034a000b4000149000310004074907920486020000e05480028188100c48a1b10070030041e00d8180c9007110350300000d090400340b0741c06003040041150301141c5022007821029032130b42030544608a0412540c01940c2860801c84070a0004000441c8684d50709040050385080803403886614426640200d8440a120909000341100b5562031440446e000110b58 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 714148776 1250 714147526 714147541
    0x302090a050307150807020606060901122403050115080d180b0f070308161b02030a0f2405061e0609091f1215020702060c06090a061b0215 61
    0xa0090381e11071a4548100d0102184200e402004c04003400207946860a603030302c80c094143d8452000f01c0d111600020305001c000348a43c400c20b030062180324080780003d0001701441354110b88159030384043e140d005000c4c1c1c003001001800d2181001038040b802c0440d25150622040c56210041c1c2120107080020504a000a03130743d40744404001082000401e60f07441d02c024034500c2a9402c601001c1e00031582041c0000e04000c8640c0d2401030602441c0e032003442440c140c0281d18507480880d1000c2c1d826220b10302e40c400006003010150007440703018038800e0018506810b640410740d0000d1015504041c104028000c4d0b903260719515a9003100c000c0c1107032941840040220b2030364000d1252056002d0301e03400601c011a5100b81424410840e04a4041c07c00c640310300c8000c4400040200090010b0348801070300d2040411036001d001014401008a445c0a00c9401164980030f0252045c0b2a82d400c01c2d80f402c4208a03103807042003918080d89203030700400d25060038040e44509015800f82038070201c0c3d030b0002e5580b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 714150026 1250 714148776 714148789
    0x51b0a0c0b130f140a06030c0806060d0e0a1103061e0402091801021c0e03090112051f0e071805100f0e040911030606010306031e0c0f0305010209040615020c01030209 73
    0xb0386122801c0300c3c8559901d444480c40825405034003802419900c1c00880e22501c24060003c004c1c003c0c0e1589041c9440b0f480c14840681c0c4441d81c6a05c44c0b030b42d6800301d86910700c402d1241c0b82e9130740c1c010b030401c1e00070120201c10113043c098041c001100c0141004500003190450b085c2040c1e000d501141c460707809669035100468010a6514154125440000d01d164040e800c1c9039030390a800c0c0c1201c01000440d94078103841d541c1c0e10808582c180072810046a141c14055190042c0b548003128002401d1a00c1c00c00550f80310710b01c0c0a0f00810300c080088010454020b900c0b580b2444650780c00303500c50000760310700000700d07540f0b120186001e0100b02400c424981494050299450212405032042081d41003609110300bc00400021151190084030302060b0550721038003800c000d99130850201c901c800c1681d0960002c140c94450115140a01e050f03000800304000c1d050040158003035000542d80d022114104000c480450b000214030080394401643d425600003580c81c0080020300b80181d460aa44000031741 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 714151276 1250 714150026 714150029
    0x13050901031401060b211518011d011401050705210702040b0d33140a0b030a0332041d070c0210050d020c010507051b0a0c0b13 56
    0x810001050000040186801c089840348501c90001c02909844512944041c401c504103945c00300400204200309501d4440317034581003908010314070f80d044103902c003181110f100f90850b107100f00f0300f1000410400307000103842003d0358240c114010362581820021a4240340082030141045408901c0004000c010043c04c203240e4001000a20741659414015440e9800707080200d00440c02d1805501c403e0800c8140a001070b540940f01b00d410108800004882c42442a2540640680c02d52200c24284140c442d910380ca20b0140c0d07000c40c82d440c0c01c2848a05175005032a820f4003d0f400340010790046544036140c0d018a41c05041c100e241d0720320043c08201e0035000d890036910078074000200001d44101106020ba003d10100b01090300590790b005050352181d044480181d007109100d15002211841500102181890b01000504000d6420711807030031200e040710354a01150300090140700c1064198020351841004400410b032030150780da98141c0120b024420f10781d9481c0003107250344000c90005140340 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 714152526 1250 714151276 714151279
    0x5072d12091407240c0b0c130902031009061d0a05130204240b0f0405010305060d05060907050123040b0d020c0d090501080a0b01020307020d021c030e0a0b030105151305 74
    0x400d40c41d01d80b01d00303102d1140440400c80341904e02c441c05122080c0582c0f184100325400c00d40307150036550703211600c0300a6480348140340c001490403080868218080d00c0554069400012510111410584c880c000c0310f8458020501080009141c1017442e900f0401584d0301c034a560380085800c1d15461180164460f80620095000741450400807004524070101d4420140e00c1e66040c210310740e03c0c086400b861083d901400419075040006000b1940240c0040d50000380c06006081d604d0081c1e1100d50a002d002d440220740d5801a203005c220175030b4840b840c0d01c00101000050b2842c0040041074090174880c5105025001c031020407001c40b0007407198107460140306040c081c2c6c0d0210215407402044840c041c042e9902061000d00402da83e40c16030301c00d100180e8010b8006510700700e565020007061b01100041264010015446480e040c00440b4075214a14420780f81ca2561108440400800259079000703410113440901c010045555142c0341581340300302442419655003000101c0817080a21170700711a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 714153776 1250 714152526 714152533
    0xe0a150608030f03090d03051003030f090906080c040501090c0e04051306062d050f1908191e020901031e0501060e0915070917010f05072d120914 64
    0x3411040038200040d84039242617000e4aa94000540c0c055085076010740c0d154030010810941440000d0007035810080d00d16460524020141d40c031842441580c0b00764110945917000b0011220035030400d070245034054000c3d4030050240d107125003c002c00c18440d0702509403180707844201288400d200d1641180c40ca90f04150240581e83e04d0b0750109420383e4003410303044682c1004442d130b21600044280c940c41a41c1000782510382d5480421b04108004401900703030800b5403009000003030b028508000b03030886007030b02e034040070704151003810b045c0c100440500000854000e86000b20f00181c1d81e000269054a0344044003242c0c04400320000900440744820007801586804008140400d5030b035401c0d803244007181d04440411303e441490301c1c403001c420750b003010201d405040140218110750a200101e1088100005014855200c150054070419680040880c50041c1c0107840c034094003c545110341807400800c424000c821700003e005c42000883c8030b064035590000c0d441048541c03104101540b0520044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 714155026 1250 714153776 714153787
    0xf190b0a080607030501030c0f06050a0327030905010f08040b06010c2102070302122a010309021e09090a0c090b010e040504050f0607020d020703020f0f0901120c090e0a15060803 78
    0xd0024170003070209032103042e41c409000480c420101191002e5030311540d1752604051b5801001e03030150848400003504040450341d08016114000d84076500107000355500f062541c50400090b02c9000c41910300402c00000008000c08184071078140d0f50004820b1914194070030060800020300e10700c48041e40b2040800018050f0f0305640020a0030a81740201d036001c1c080001c06c1d02c9941c6c0c5048000c410019030301e00609105d842e01e00f851030b00008400604012031381918950010b41d900106804251401400341c8c00e618150410501103a4040240e03c02404594215201c80b0000d1895200707070b04403543c40340c40210190b407043c5c1203800604005041803015062074500b45031030703a80e4511050240d120b46c4000882d81403002400c0c4d6000b14081c0c003c1e080c59400d50302801203035101079154641018031000410500d84030003e1035130091070f4540e44981d88000510304141440c9155109102050504410a0004801180441645901c0b40c1c800072204486040c60010f4042540301004502000c940d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 714156276 1250 714155026 714155041
    0x7090b1605010606030c080708090c220c030b0d120309140d0e0604052103040b13080d08011d0603010905030307031d0d050f0a0302040803031009050f190b0a0806 71
    0x14803614151144009100c1d0070703190b00086045600c1590003c0004411401251815028210700341c1c000b00396034291051884c0407004610740e4008070760042e10344002c500803107010b103040340b048420400d5245810b00000f10003000040240704900b03005802c0b888280c070880d601901aa10961805500c120403101e0420325084541d01ca840705480840864080741000c00246081e500316401d684004000c00d05c5001c00d00c1c00c5001d1a400c2c00303000b400c0da202c10000401c003240c1c0c0001501034007200009104803541081825410f0103d8081003a00740700d8520010f00c103098404082510015030b550340c001155441c0c40009001d00703510400a0301c980400020310a44036415007002402c40d68985601030750b91011560b696036240c100032a4000920309004000a5021840051203550010300d400740c10192147c40c41c5081da031082d1031100700301e0030212080140d02c00c58000c1603813041c0c2d11441e0341c01501d020411801c000d051000315100a80d0340f43e00602c40c03035440000800240260200310b50603171600c40f4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 714157526 1250 714156276 714156307
    0x106030c1403061e0a0f1805010b01090f0305060a020f090d0305040f1e15200d26040201051c021602090603030c03270925110c0907090b 60
    0x50494043e006001c00602d140264242c689880401004c000c00c081d5510900f072001800b003001c5421525840e08030320192141440c0200f04214010400002d068002000162050240703a2000d03c0c00c0003002004c0000c1a0b0125035107501640200c009a541c04c0080c0c0c00e92440e00c11800199030007039140e804482815840009803040da03402c0020640b0441d221480700621107000c02561020448a83d0240008002c6030100c0c40004c00074140010111030b080302c42007410100e40b03000121360784450081c5201a90051007101d45165a104c4040040114141c00e800c4503002840641404000248903040c00300d1840003031421a00b0f5801151980c1c9088000c0500001015080e13224068080100308940340220440700c0a014150095240651401502a0345845051680211048140504115151060254852425281701d641c074901084c00e1030086c0e04040030444104403a04100c1807031a0000102e18140180c225503420890741c809004940300f9940c1c3c2c10260f00c0840c0031820401e180b00300b4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 714158776 1250 714157526 714157559
    0x106020105010b13030206220b1e03010617060a080d08041202030415030b0613060c1406070c020111030408010e0d0210140109021602030115030314030f0103140106030c 74
    0x168028001640e980c0c1e807900c1140500080040e2503501480c04100600d03096005000340508c9500710745462070b49600004100c1c04e160f000900d40c0c031002501d60781301c02e02c0181040200c07907002441c500f9941030000060005400000c1500d40318a00d9002c2029950341d0780c0c0c050014030100c012075120404460000300700190540b0100c860049550030f05804070b0002c0191800e450707200d000d116500500c2c2d4811405400861300d2150441001c0040710380b202e0003084200040c05454403402c000c0580d0b40340001560030720b40c07002c820540012062001542c0d000c401002003680903e020007045034401038207425442640d0003000e6940c03038043c401410b44000700d042c83d4070000680a030340c500300b500340d0600706941400031186054001c880041c0016542940030300b03030b40700030707803845803015501c41d400700742100e1885551100302d03d10805c041007055880b4480002d10010101098110b04014009511060041c000241002410031030a40680d900754005801540c2041d41c203402c556469042050500d1103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 714160026 1250 714158776 714158789
    0x230d1a1e0c1c0e0d02300a05091512090703020f0f0319110a09050106020c150c06010b0301090b01020309060304121704200108060d0b071206090c20032d070302010501 73
    0x5d440003002d1901ba1144809000e100b18500383c000c00a0030300700180c0540c00070b0350f6682400f005012801550b101e80c840c4580051104500542d52801c0511108990b24014602e000d180d10041d02800141c89500c0940c0c00329030142c0c3e4141c000804180020708102d001c0700586400340c2112480c80a1000c00398201d2840d01094490f810003035250704828041e11001d000d002c1c0036030b0018078194841d0410108040e00b105400b5032807418442c1c910141c5051075020703030008c0303c4d010021006220050092140984030b08090004514041e0481c0c04200e81b03000040c0094000102b0102d01c0d01d82c1d600403600d8012186000212001510b0940b81040e03a01d07405042c074030700110448205072819402604000d0240be0000c001c0d1094003055a100c21046800400d4902001910b41c5001c00c00e21540c0104030103456005c1c0d0100e034070100b1410060840040c407a030141c011294090a20500740c002c0100d52017407904141c855202094011400310b82000000c400c03900310000941ea4051541c1984454103903502c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 714161276 1250 714160026 714160033
    0x60d1403120601050a021906090b150a050102071a09120a0807030912020d0f050c0d11040b10170c07080c01020306041d07230d1a1e0c1c0e0d02 63
    0xc2d104011581e6010714000350b000359020302810303042e8802d590226084c56100b50310121704494140d5846c58100801e8800c1d180f4078400ca605003401d450700e103003060003401081c402000d0310741c540080781c020150007407220041c0707510000c0d12404986030109201c800907500030445848201c2d40c43c0c6250701e03900a050a50014860700e0020a0300b03209540d40c100c0042c1c0090909480121a4490750280c014201084519216096130384446071200e0b0080500c450080c2c0c200c01140400c2024001981c84170f140c8070f48940d0390140a010b40031341016000c1d00d00b03a00310003070300d510303568035030a00c8001d10580c1d2025003810004500c1e00c0d580c00c015001588185015241400001d1404540c822680118540900b07a40c2110300d0038800300074203c1c80c0c00a2804a103010840d40b0b00c5035008504441000441601c02c048020b0500b140c824410001903040344680c00d0110042078510030001c00c0d000054452015502c0c00a410029125021010b404240c990075003040f04401ca003109660714021250510003601 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 714162526 1250 714161276 714161281
    0x7210b100e0a1104060f0c0b0118050a051003031d0904060207062f07050c090109200405030d350601030609050c070b04050f0102130609051e0603060d140312 69
    0x42d60703015155615448207580ca0403c0d08105c0150740d80307000c111400e01001024800c3e400443c3e944c60758a402854800452651020314096410585000401c20b000642c140802d224440640f800003500f1a901440d0465900440c40d1140c007044181d65022070380800f2540c1423005002e50341d8018542c8901c590780410890320420390314801ba41c1c0c00c0c10401400c61018858109100c014001400100d220704181d4200b58409000070b0f0000c1020f0704810042541e420b80907800c03a4070500001015425021018105840c1200107583e650851442c202013080348084905990582250440700c4c03005034501c02c0c10380c0c5c1c00c00c1c8490b002c0f00381107138407500086c00c1410004e2103a5040c8102c82c0244400785145140c5041602d5128080101410031540c0c1e2241100100c1144000e00c050400c051040daa4080c5480c03428a000380514002c1c0c0025101e415007030000350400c0282c01f83c286110300140c41d484d4a80c1e884100240c0ca2407105080500056200d0054810411005c0020200e250a140890740d158 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 714163776 1250 714162526 714162541
    0x20c1c0209010306020906072001090e01240509091306150326040503120316110d030e030c0d02240c0304060b030102090607030c0209071107210b100e 66
    0x9120244040d40080940c0018008510b0315001441c1c0040701802c0c041c64008a0ba13550400e80d01e445070076008810300207403081c03410340e44070642200521801c8290046941400b5030300c19540d0f01c4001c0d032144500c0004048140a020740250f80803500f0090048040b8600444c0912031010501d0080303803482d03d0141c154203d12070110601c0c4c1640e800c1600e0300001c2c0713200302c4034000700301009000030442c4406000000c0c4503582042100d40035410b40d0506034480c14017111f02c1e8008500312055400b480a00c0e042070131554030014008401c0c0d010b41c80c0118203e0080d100ca1400c40c420201303001010700650503400212600003034070341070300b030106022402428094003200d5a584001c1c1c500390381e070480410214001c14006c0d0010542e180c0014001458558101d0000e042ca9005900032000318561000c62000e41c6040201c1039404450340c108640f00c289606200c6032075000a0140d80420034038246420300c4c0030450390000078204d5025400c0082802c0552504203142900c0c85a210441c022702c0008100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 714165026 1250 714163776 714163819
    0x1e091a090909031c09020f031603050f010203070c1b05130603030e030f0d051309060f051807080105010f0507020d050303010510050a0906030207061407030509010f05010f03020d1b06020c 82
    0x80d000d00d00c181d0441130605000c54043d02040300107980c000072801c7d500c40e0544d014003c043c401030f044100e102d42c0d1860f51810301d041021811211000c0e034418001c00c0101d0b40c008100c0c070401c0390712064080302c400c50320803038444200603030300b0854100071485d402e4071a001c0c00340d201c9810b89000303440700b00d41c00140004041c0d6072506002c40041e45e80140203d200c0d190702a4006c0c1c106401401c1114501d291a820805e0844003e507000340c402e1040c010341004523080c4400c041d0010304950000e0307825460002c0e000b415441c4180b180504005082000100c443d00c900241c606003075004005100507003060516a9583d0800c2c0500e0740301da00c1c0742c841480001e0046003124004d04d5152904001c85181c40c8064000790400a000c0e07418603112002e000300c22040c0c00110348214006d4500041d54103105c50080d0842d25800702d01c11605103490014400d0240c00c1c00000c049a904444225400c5c0c0d03d8a4a1041c020f000d103005429030345d1070440854295000704640243c2e02050740c0f800c1c103070000340c3c080b00340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 714166276 1250 714165026 714165037
    0xe010c2609210c0115150e1503070c0b16090506030906041e15050f010b04030f0809011403010f140d030806100e10090512010c1e091a09090903 63
    0x765102c8181060040300c120100307110402d08110081c1003400241d0314a00b0340d41c0b514040c211044146205201090809420804c03031650703413801c1020340d500000450b1a450032180400d40591340440003070030b0a4070540160203000d9015103221960f050501000b01800b50001062010800c24580801c02d4100203041d00d205091000082c42d660302d450300c5000a1078200e0900701c03642480c0d29800c0f0701280001d007818000d908440070000d814603102003843e0480506030803403004040100410804100b24001c2088560740060140741d60340e41601c01070700c40b10284000780c61801c0d004400050310300f500840c4002140c2c81801d042000c80f000c030f010030880120601000f000700d260030f004900e090401000b414244407682c204451404400000602808a4070700c1181c00110644402e201e1030410b0b01010224280130002130158000c0c4410181401c0440c07003040d4003214646002604d1288114030301d000414600507a1882c412451a808400342c0c003c1e41c3e00c1c0e000740321141c089000c03180000106c69 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 714167526 1250 714166276 714166291
    0x40305070e0c030628090e0f1c110109020d050a03080a051009020d02210a2004060c051213050a090903020c130b060403110f0d0b15030a1b032a0302130e010c26 70
    0x1007009e001c900250307120b00c0c0210392042e05d9036035007000c200181c40c7c0c0e0f81d40c0c669640c054001000321441c9460b0040400c82d004003d11011401c0c0018001840355070608a010f036030403190090780380d60300800c9690081c0255450312000341550f90740c2822840e00b429540303004404482c001c2c003d04020421014240549103e002c91440041008001840c410310510f002c681c03140c0c080d0b41314000003001d5a1110b401002c0c2e0f2921801c1d400004101c90311348081e00e1401000c1c0380005018425507520003079290345012900034051206035160300f112901c84d900ca0007840200078081911140c0380d04103982043e290056540c000e542079100000545070050b075800041d5446120342d01550707a52503411001020400c0020741600c0b80805280005000d414404202807481640c070f4502850f50130803205914000d20010b071803041d0501c00c0c00010340e040e40444107884d0103855100c424410068588001c001074000140103504c1d0000c2010950741c003903c90000004003010411162000c403c1e114403492060300d421 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 714168776 1250 714167526 714167563
    0xb0a0503010b0708160602030709061103030a020a111204051c020904060e1207051b0a0b030c03071715120c010e0405070203040e010b040305070e0c030628090e0f 71
    0x4100b8500e0000040003c0e038400e403815410045180ca54011010030010115225a0003004000d681c550088490000b41014913020007142010240e1384e40b644000351102c0d000381c0e000540295000e000390710388640000381508903440d80040103a035075110b400900440e84654051a0817200c4106020912a60540c0040411106445981e0b500c0024034001400701210b0107803406101303003800400702418500c0d024034090000242408043c052610100b45082d00c5480c0d00007050101aa8003400e90f0751003101c0541240e540e03180c0070010b542d0b0b200d2040000d038405010700c00f0040c80661071090807078000d0007602c4400d9170700300a26000d520b80441003141c50000d10041101000c40c03425400c66500040345005903450251520b00380454410241c1141c03401040001d420820808100184c4004009502006055042c102428080c0e4071018109610544011048444403c505144904900c084000312030101d81d50f0061079000d070010f054460900d02075407480421003a00407034010386c1c5424103442c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 714170026 1250 714168776 714168779
    0x40603050a0b151617070c14030102270d0b04260a0c060506061b0607020606101704022d0f1f20010c11011b02100207030e0301060f050a0b0a050301 65
    0x14402612541c00f69100301c0402d6045c500351550000034110140541038801e495418071950480d0550200090790081e881005124000c500304d26916218074544000e05600c40103110002d032006960480290444030460244410440c0400c4940340d041440004a203c541e111100c60110380100003030704000c44d10000700d040028015a1140b5445a0010106801c2900c10800503441c17501501c0441e43c13642c40101404562a0104401a40030030112194072084208150080402c482d032815207015040702c0340401c0071561512607a4004480703800140e00031000c01d8040300d061001e00d00c001801039884401c84100c43c02d10501d0210802510901080011001141140c216000d804030310108280b454050026550030b0003190064046a07445034490b01983c02d00c5800c40f08400c101d84a40c4c1e51030b0000103072480c0c0108180c42ca0081091005849103142e04003543c81380040524542e140d480d061380840c07140a10b5110109581e0700799600540c43d926604030b820a84a0f610701da50114009000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 714171276 1250 714170026 714170047
    0x603070f0203071a070216050d0b0603010e01411612111305090907150e09090313081b0f010504080307060906200904020a020a08040603050a0b15 64
    0x103994115000d184116480c189103501c0320030351500c0d5414054084508a02800301a07641040107404001e00e0340d05c000c01c014900340006085d15021b400c000c01e5544240d0006499540030743c00701c0303103481019000b84202d411010740388800c01c0d50483d50301e042c0f40e00f04070303084422440008800e00b03100b0701d0344822201c0d440301c0703845404150000400e4020000c10007812445424640520340c80c001c00c10242585850405004500707601640d040180203000d18030810040000001c1c1103000c0783c80754a0302d14000a03c0c0c4034210341c0201e40450b0380c1c0d0000d552005208d1542c0d03000008015401101e40360414041d00c0b010440e850f111401d40c060090034030b00003085810b00d000310b5122500201410310a140581c0e568a00d810358201c58020b07a28103a50780c201c1402c0c49058020900074010140c0c15844003070403032071b0600325401a60b1400d80225401b05000f00000d00030004030000a4000c090541c4542c2d4600006000e0a0f04403040c0c2d1071107041c00b244603100d00345060a0700707000c0c045e880c0c00d5003400308210 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 714172526 1250 714171276 714171287
    0x1509230c07050a0f2f3610090908090f0a061d03150f040611040b0a0809100207050604050708070b09060d0f050a0b01081b160609050102031e0f0402060307 68
    0xc019117040520700c2c0384408000c1c0d42c0c1c691226020030590281004020201041100241481109003a06c2208041c003460004500311181da06140c031200d144545030084100199000b5412265070603140c0091b55007800356000c00303071003500000c540c08a200d0503684c052001c0810544180b202050000641d4000b584884070140c540c00e0000d4100e4160024405481c2c6c212401a40ca41c558090b9100a0009011a40c001d4100794070088102e030b4503061500e41302d01550b22444218104028000c4041400f4900a0140c1001746000e20340c01d6442e11202d0030626190142654111074506c500d000c0000d04135008641c0c0300417103800b1040f0605149190742030020340c0e0300559400d500e140d0b0303510010907400344500c1010b00403c18034100044d9411280c00162401c0b40c05001c243c4944050800c00200c00900405c4501c2604000503600ca045136078a040e801070621a0b0004265500200070840002c01c03400d07003410360082c020340d0115981c803006010041e049068902035080441040041c3c88140900c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 714173776 1250 714172526 714172553
    0xb030606121203180607030e0d030f020d090503030105130501231309080d0e010b03070306091a070c02090c091302160203030f04060201060e010b0d1509230c07050a 72
    0x9040e00c003000b103150b8444400c1d9004071181c0716046604541c904040b4010096294031044a05040000e02007511009540d032217101403820030184ca501c20b00c1d00c01c800c2501580e07900300b912041482860100d2404070b4684e0000d0050360300400409040048420040c01500e04840006010842c0c0c002207d220a040b15038400766203400840039081a0008006882504411070062100e0307a10303100d0a04112003039800320414903030305a040c038007081d115036000700b94281140e40c4220001340c8082e141c585203400740036009110364100750340010041d1150b080540c1c84903840c03003103615901542d24500221024080c0c60760b51504040300d811901c07682c1d510307070780104903007084032002102080055000914550060700d81c4401c02030003050800407140c0900409010f40011840c0c030184d5814408071003040e010705041d20710156110041c8880140d241d8440a0160221030000d00c180c101e6102e1180420680c945d2010500034540c00013800100c01c41e0694500741e0b44500940002d05d10b0f6103815074013030030780b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 714175026 1250 714173776 714173809
    0x30106030b0a0506120103051b011407020a0f0902030108070b0c060403210608030909010f0812280201090212030418020c0f160807080705101809020d09060f0b030606 73
    0x42d4004601c981e1a00090200d207040310039404110b6046280860401c80f00c0210b9048200e11a03550203002e80e045000c50740301c50b440c00310680c0c42d51814000100300d604980e01c801c80b400d0b500100460b4444080c0c0045060b10401c504980580d5542c0246409600c2041c003807038915042100802c00091081090900701d0101c503281700000c80c01801c21000301c80703040c1e009028590000907040441c0c14501422801458260002c0300c80510303104000ea00e810440090b440c00f0079000442d03880090181000c0301c4280310590b1691707003090a5881c0a4000c02d074485041c1d21404130886030100f400301c00070464041d10320003102c0c0610840c0849012020790003180350b80686009070780d00081010f204100800b980e407410264100780c81c0c50701441c1d0781820000c0e0010b6900d03400032607052007030f03031500b45a0700498a8a403406c0704403440c2000c480d140c190900e800080c03615000050121b0780c09811340002c01c1c107a00440701007055602d2000e04408440f1080b0409c0d0301600048000b4030189000c00007a40103007030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 714176276 1250 714175026 714175039
    0x8040905060a05041802090c1e0a020307050d050703020f0c010509060c01021905070b01060c030e011d0307090c120216170d0e0607030b010f0c06110c0a050105010821030106030b 78
    0x300c883c006000d580012070034440b65030240300688250300d001200140c000307502c20700d094a050329401d004180344451000704c0c51201c5000514601c0c6a2081003229041500082922448604403100511a5001c00d1094006102d0103110005c100004a0201c00030b0905031200c91404440000740030242c0c226041040c0655424045048a00501c2d0803543d042e06860b550701e65110340d6480c260035181d9042c0c02c490104241ca080003400030ba040a41b0085110003420000a403001999110300203440345d001c03e036098050000300281044050708081c07611241910342011550035652818220b00850503520725003030f40300032040f01003150b00c03c0c1c40c1c040300f001c8a112450070b00c0280100069035003a0565144c1644428108000f1540c0342c070070002c7c802024604450000a5060010188400054060000c503038400c1000011600e1070102d480c04442182501e9460956060180c02440c0900c41c058050082501084c80a07031501c0b01594007402c030003078450944c1d0802c00102c006051a1410300d40201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 714177526 1250 714176276 714176279
    0x101209050f060709081b04090c08100c030e0f060609090304050303030411040f0b18060609420a030e2812180e0604020f0301030f0c06050708040905060a 67
    0xc0c000d01600704406000700051180e0304204100070a9494207a01c0890a5003001007414243c070861980c1d4440218101c6e00840d41102078202403900503110385c08080c0a03c03694242038072409a6411850900700651010400c10780039003800ca880b28010005802280c00000005482e4078105044c00d030044501012281029203135000309180d680150b80c181e64691000d01c64581030318250165071404001c11209010181703001c0c020410950b043d101c19095207100e9000200c554503801e051b5040d035500241101c0f04680080c003a140055400c0041654001d040900201c1000c000101d4a00700400941e100d40b4195200c0000c0b0b000b41443c3c0d9002107c3c1c0208401c0c02080451441d6601150101000c802c000c1d2210703143c54010301e00300703031110002c2c032000004643c0b028456401a0301160100990300c06c0075500c1c03400203002480760004020a0140c01300001c4180581031009010b014815580f21aa0036143e44040e10940101d0500400e2444100300c14414142c0030780266802c540041c00140629 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 714178776 1250 714177526 714177533
    0xf0f190312020601030b01081b060a02010f02031302040501090b0f130e0706080f180c0f030a0807230c310e010f1d0c010302072a180b101209 62
    0xc0d203803801c000c01030340008014070078806224a698018045070b03000386407007c480344071b400200300c010020314403c035030103e00c84a00e00e000f0340100e00302c0344459108550703910307040c1c04002200300b200509a014a1415001065440c071500c16050040c20080c03070400040380c20b804002c886454050b10904540e00c6030201d10000c48200302c40000b802c501e0b1560310a0b440c0190042d04164002043c45104100e10394552003041d1011072000800e1100f0303980c1e1040c5452541c0803900c2c04000d850300074071301b00f00045c10409104049a0b81c80107520b002c40c80c119000c1b0070050071030b40c6081d24034600d80e0003107a4181e80c3c00307002310032800c481e184d40355001003c940c03058894044040ba2000302c3e240295944034810050070740c002d03208e21054881d602510510100e10020782540d074030a440001c5040c10340c00a030340c0c802e20143da405001c05102c0600080b450040c2070310030a981001d00e2007148288601580b624030f0045150040d001c00b0800a41214103015421404448180601d400300c00c180d07640d05c6000303010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 714180026 1250 714178776 714178793
    0xa0807090f05160c170f0c07030314040e0a0f0e010903020a030806150d0f0902060a0f09050109150c1b031110031b0e041407020c0406050f0f1903 64
    0x10450032a0004619100003421800d03100d000304490a204080e490828505800c80003c4140c0c54004819241c5402075803003494440c0b1a040c0b000300c0b0b40e040454005584140010000c041e24403950f114070050003016800285030140c0d0161001180125001500e0f0a021b0f0748507904096011030302040c056041f45015007100c0424000f0307401078002070f02c0c9105040d0008211604134005071201105030140703180080302802402000b0388030903200c101e003503400d44294103c0b492064000345107d6039040760150141104c4400030107480415140e480006256020f181914111150806a2122a001132100300d96000c418401101e241c01c20110700815292009050000b55201d440c1e0b41c981c0f02d80b00e0040080300480196640101800c1100c2d00260710f001e400c00c042c14544a09060f05010030020003e000307050104800a502580001001003155001504210142c4280c4d02080015240e40c1401103c81004900c01d81103030350301c0c1d4518600c0c100300300751814210700c0901c800055512560341e03010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 714181276 1250 714180026 714180029
    0x316060612080c010c020d0c020f270403030609050402060a0c050a0803091b0301111902070e07050316020c090114040216030309031107050109030803070323011419050405060a0807 79
    0x60040021036107040080007403040d01c11740d00313290000f4160640d6004008020b813260070703070080c007800000303280004513251011550b4001844990a0140d6003400810444940701143c01b0380c00a03003040c40c0013480290910815004540250019141103680401a1609515130004460620071002000701040039030014502501088c4040c28149851155801303a02044510080c802d0745000800d149200c1000300302c600c20703904100850707102502c2d910141d0902e00254000c19640920000b0032400680c418000c0d840b60a201300b001c44034442c0048200d070340c1c6130408041038006d80d00340014814114445c0c009880d94000410240c50070140c100b545d21800c0200b803048010907199100d50341090341041882d210801703048000c02906140000081031041d9034800540004d40c0000810b49091003600f00405000c0070700c02115003242d540145140300d880900c00d00c600500200080c540514000268281b41c2c40380c01003090005042000300070007418054004d680c031100d003081c00035265130140400070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 714182526 1250 714181276 714181283
    0x6010518100513060504120209070c061406100c0c0303031a06040b04142202210702070f090c09050907110d02060f100b1204020613030b060a06020309030316060612 72
    0x2910352a43c456003242128194004c0001d00100340700900c01c00c80d0700103599440580490341e0035802d840c2c041c01542c040260031005032005080420410740d0082180f403141c040c003014ad0341c110f03c0754a052000c4840d11a01280100b10348079810007003020078445d40001d13043e0a0520701c0744402c011000009680b99010391700c101c60324080840d080002d0180f024810740d18103400d0302c1c1c1981d409410b00d4484c081000380346100312417583c0864218007040e543c0911040d00009101a80b10303904103210003940d112030030b21079800c1d0303100307100d101195440e0f0724020390311590390a440740880d482c01c0c0030801000c140c0c0141203804106010000d9089030604201c0300c4540c10807600075000718200f0540851003d074008105001d2280050810444035800504640c0b07988503800c0d540599440303d10000b00144038a0203111206184c03680044248851148030500410045030071902ca41e80c0c4400a0740c4900542160a03410b401c140f15001c010300884010071921440b41307000244080e143d40c3c1c001400850001b00340e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 714183776 1250 714182526 714182537
    0x3160207051c0b0f0412080408070f060e0706021c0c110301020f1b03040302100503071806110114010515130f06030c02010b0d0b0c1305040507171b030601051810 71
    0xb4003802001081e40340c01007690604210340c2c4c03900d42c84440049121490300710800c5041c000140c2070085c0c00e0180c1d126644d00805603e103008080c20007002521006141288c91f0188810009480d400050003280c03068800f40103001d40c000c0030f0b00c1a07407655020784050307a1071700d00001800171035a000c8c4010075084010b001c0c066200c0000b605040e48005403206075240590003004148090780d2012a003032000051894456941d540d00380b821107a0f40d9a52143c4050b99400c2ca001154903a000070451002c10075140003088071800c40000f14a032800c0a115143d00080e228001c6140342d81e40f03000510b540c45190898a10071030784e8856180d20100c265005800081d0741d1101081504d60a0044110404080342c0387c1614004d00d480c0d00c1c0309040c028040d6160308400003918540900c443c0c0c402e40080000038000c01c818545a4406011318900e00c1d0308120b079810f030300000703100b02e52843c80364240c200d80744500c035040d5034407000103690f03603840901050503d4030201d02034022a5a90140c1018403003071550303072 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 714185026 1250 714183776 714183829
    0x13020c030a1e0503070203030f180a0c06021203040209042621010501082e38071509060624081810020a030612030521010501050316020705 61
    0x5045010030b02000d210402400308140312885a000054070341101c3c514010380f4203615000f28a0200421303c2061158070700601c00340c50300f4842c08400d40d008481c950b07000c0d281c0d450099034088107140701c2203d00a622060080c00f0402154504c420a1905c1c6074181c8a040103156800601c607481d0801101118061509003110415848403101580188020309000b20281000f0240848400c0181c103071085032545500c0c0580c454000c1503960f4014198030f5009444814000ca07041458407c4060151014002c200b038214804500710440e0181c0b03401400412034120b440300d00801a0100742815540551070b240c01040e4a943d460380030324400d00020501105075014000a4003014005044165000b10121580070a14001c201d45c0721480b01420016039450000c40294000c0c8030541043c0e6000801d4540f070000c140d04a0010110b50446804da036101c003407400c044142d0746409004030340c0020700500c0892550142c160340c000c441805801030f240101d4860020a181d80381e082d61407040491101007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 714186276 1250 714185026 714185057
    0x4050d050d02011b050d0506030c0402041d160804081303080309010b19050d020f04112d0405010509010c14061f0f060c0f030315141c030e13020c030a 66
    0x12616500700420010f541100110400f03030040c05851005140a5140c900154540d0b40078468099a07032b0b8024821512103844021800c2041848015102410758180108014242d002343d5075241c01c200c1d40c0c50070b03001d42e11555038014070f800101d51036091400145001c0001f40440020358032039030010000090301c0d90640c041040c0610303a84040080702106803020b02580e01c078085180006c035011b40300d050140382600003041c000c04426050307145000020442442d4480c001280481c01c1c5c010090340c500c03000314007844025034466807040c1400704104000c90300075540200d010b44d90a40c0903003104c000000c030980b45c1d05c1c1442c20448089074041c1500124a030702d444414081c101401b00401407180042c1450300107048038100f05805803005880a4a0900f00352080d0800030007080c203510411440ca41c1ca00700c1c60701d049032050030f2510881002d14a001c4c0c005200d0324000b0140d41598520309042102c000380441c8080498000000c142c0820042c140000d041000344000c0c8001ea4a40d25461a800c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 714187526 1250 714186276 714186281
    0x3150902040920180112030c0209040f031e1e020c030604030f030e030c03090d2105070c06020f0a020103020c010216080c330630010513080403120504050d050d0201 72
    0x2480c14858503141e113a064401038003820f010b0555244c6034030f030036580b0140d0130b05640d0b668540a000703504c680100700700720401c591008042406c520a0312000c000ba1081040344918090b40503400000840003074846c01108003001a02c1e11b4044a070040d0790044c0760072004030b400d10b1030417a03040e804641507005030b0802c154548a150081030038013010358201007009106985030311580102c00e2040ba0400c50350030510440d0600b045003100c40e0100380c3c5070410070360405491500a00029213b2941030440020072078008a81c040529406602824285469900540081d0002d402080c019075003408180301013001a80042902c9020320096901d0f40c2c03a5403d034614001c03082c060541e2400c44141198a04071a03880c0c00302100c4c0e1507440b11a0259204404030300c580702a640901605100e0045d40443c81954540c0500c0310b5a00000030f002e01e69034610b40c0c00d00c40d40648030052556408000c00c0010502210740a142c1c00f8152038401c0c5416511000a07a0045041c04150340c985c0041801000751074091 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 714188776 1250 714187526 714187583
    0xb090705060403030207180b0303040e19020733060605030a0e03040501121e050411010f0f050a111e1e0c090411010c0501020d0b01080f0f01031509020409 68
    0x1194902e15150075554020f484030400d00ca01003640040c00c8079800c0240040c1c0002c240e0310710143c200e9031550340d1011218860403055804520b18880c0d50501c040c408554000c03260300c1d03608246140042d604007a4403c402c0c2c0300241c0d0b100e070140003642d030002c1d11840c0c0e070140d03c00629456960988a0030704c000f620f01254051f0300b070750083d68010002080941d8000210b02c044865036400002c2e82078030fa0910018500f440380c201c440d480c0c5003008120030048131010011803410281e84403814803e610000ba10500c51400d05280411010300c900080309110b020b080c4001510398054541010200030340e4042c45203030111414140d005204880c001250317060442d912400311200820403803d02d100802d069505c0a40043c1c00d21421009418180c0d0040201008a90784030008541c1d64941250020090190010403400200d4100c003181801d800400020700400110300e618015910303590f505207811489881240210f40c84003020300c050b917100e01c92600b803c2c0c0244000030310310307500951500c20342c3c4c0d10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 714190026 1250 714188776 714188779
    0x6060207050a06080601110c04050f190608072112080103050d0e0a051005120c190c11040c110a0c090c08070f11190c05030d020303070c11010c020306040b090705 71
    0x802c41c10488940d1020351a0782008080c02c00c500070210811440b820040c080c3c0e9201e4001d03040405000300a800100c1140c07003082d1489020408050701c07040c590590f01305100f80075140d400b0007000d1000c18007200c040d404c980c2e50031290702498030041d40d0710450078004080140c082040340004000740003051254641c0180d46160030407034004080f0001d1140c2c030490040c94042d8006c1b51109040d180250116241404a20201c01580c40c0c0000601e403680d01c1600c68101c41c546241c01d0101c514007441c5a80d00056022500b03a00700381035001808001c02d200d0251004101b0b848589034480082484000e2803c0c0c020200107910500f8840080c080d55890301c020001c000c1c10200304802c04c3d900000022103140c0703030310f0000d007014210460301d4075103040d005016a090a0b140b409104200c05510b1040c2140c00a40540784e00c404011401d0380c0b45e00040380c0071004035030100201c2000034286110301e00580070505050840104c3d070380109180c800b00b20740450307481c41c142c410300038800700030400000108030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 714191276 1250 714190026 714190039
    0x1c09031103030f01031b0b0d0b0114040e220b012301080903160804090216060b0103020a090b070606090e030d1a181b070c0603050f01050f060d091202010606020705 72
    0x340b500c483d072409401444090701c2c00c01040c1074210117500200d0034a009059003085a42c540000350080002000c82810050211f01e4444502207200c00000588013110002c07140403d207a6500303680801c007140309501c01080700815466040c0010841c12a40d030203006c1040c0c0c10160720103005054454000403401131814840300d0010030a02d000c3c0007089840d040c0d4200da40941e0301209161070360250062350840c01c505030004c00e4605810005e040c54645d03a600441c01440401121ba00640c120320030303041007000003900c182084c006e10780c64000a1802c00c0c800c0d100012a80e0f80c0d0100340c0c1c120344183d00721807003603080050f140c080700308240120700e41c00381c002d4407100f60201203800082c10400070040c484882015800060800f0b02d03000d0754152502049440c80d650b484a6141c402e07044000c078000e200c0440e19000c04114216a000325a17810380d240a8203070440c95001c1c404014168105c1c0d4031407903080b074403801c1000000b9400000409881c805400100d1301c9400c010000e81040c2560300118001d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 714192526 1250 714191276 714191281
    0xe0406150513091802190302120a051b09130309090213050f100225170a20010f0305060d020a0b21041e0203030721031d070306050c1c0903110303 64
    0x800c0c4061580c4485d81102c000c03111300e05001d15690700b1001503001940c05610130700c00d05c0c100980030840b1080903120340c041d02c2c0c0d0444103090501c0010100c100c000c0d04058410001035005140f90b1031082c140380a410840c105c159101e016600740e0b4440c0c0c441c0f0408126403c4104442d090116910110203012035107100c8401c84d44000a5a4580c280c80740510610360100071010b1070401d16480e40504541c1558200035070720558000d60318201d4404c12140307829a900c106a421025101d807442d8500142c0d0b540c86a150b8064084024001c041c1c115680300940d20f02d85401a50740b0031141c0d006040f81d1040036228121882c10b8141c05183d00c0800c41c0044040017048005075610400c900d040513454041007582025001007172a6005030080101040f08012403024070822003020700706104007554040c004983c00031010b5000306011040381950303501178207003403000420035084541d0042c1c140102d5400c082c64907204045d0280302c4484041100c0d0760391301046c28181e01403500c0b801050002c000b0352a60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 714193776 1250 714192526 714192551
    0x110303090d20270f0106050901031e090302280305070f050102220801060f0312080603100903080108190c03120e060c011406040606020d0e040615051309 67
    0x1003115008090020040c200c005000d51040000724803030024110343d0352041000301d4840403100d42811000e007660074000048120002202e854103a41c0a030b0303980c50414403141c1c010340c050b0041500c0403003846180ca070a50720b0700700203200f07208006001c0c2d4000d00d0032090403d904001e40071130309500007051880c04000340100e42c0080468112070b0b407000401e000c110403402c10074020700803190740002000305d948040400c0706011040005458144008100c0d8945c4c4401181408e0300d40d2100911020203441800c1c1082c7c003460301c0c1c0d44d1040e4013400759010054480401c00840d210b4100440c045210707000140020b1404000e40c5140c01042480100d040303545844204400d24a444020000b00c4801c0c0c41340501b40c407072811031210321317005002da0303454000040c180c6018001c0304480c90081c0b40000d001540c03e00d400d005640490f0f00301d40280000200120007100c440a4500f92113410607210000003030040c003444414004010141e41d655140c00300e0a020604d8140c00798030400c03d4600700140325100 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 714195026 1250 714193776 714193789
    0x6240f020f0a0f0507080102120117070e040b09070b0c0307210203070b07031e05060f04051920030106110d03020903030901300c1704050c061e04060201060311030309 73
    0x80c40d401c0302204034021001c4c80c02c01d10b44030040c1c010f04200c3d4000f01d40d00b50102e60040038141a2454003051950804026428994a0f24544120410700c0320000202e004220f40032406a00003035940240d600035501c401e0208029446400e907543e051340700081d5034003400080c5008203c01c92000d10040c1c20306811080095403401488405001a984480498020340c080d5000c6190350003104502d030030784078104080300010201158000c0c09154ad0100c07540c0740d894948101031040d802003028130002c000808800c0000d0520410340d0f03034142c4d242d0038141452121603010318001c1c030a40e034450b02c2080d0340408a030b042c00c00201710441458014000086207a90100959462045c01c0c0f038100740358840d107925075412110410503088100301500d103803d0660b040c4d070845103e600050700c0d10380360f1242a03504540908401c440241c01078110320141141480d1400080420701d84140c0320018082000040a04990042c1e0109015070340d980401c0041040d14000c0c46101d54040300030f54109650031010600 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 714196276 1250 714195026 714195043
    0xd020f0d091401030e070810060906082b030b041409070b04030b0f19140105150f0f0c03090a0807030201090e090607030c02030d1e05160219030306240f020f 69
    0x14507407170b81c002e00404401001100000c2c0401401c5410002c04004040000c00141c010b05240f242070860101e042c50b00040c000540110351401505561411341c05008250903030729550082680b1803c2145840d541c07401028100703211401403500b43c0c100340240d18071f00710141e0f00540385440180410000f1601101d450356129100d060750162554a02c59403c44861020b170000c041d42c0d2801180350960507942e80f030241a82c1d405c1d603405a03141d0350f5404200b540d000c0e0b401e001020040030441c0c5a17100b11004054020394042d4011a81000e441038009120003840303403c030700040d0b401440100305540c0d201d01d10740c0050113140c1c4800c0860074800ba4140e26007400070320000505403030380c0340105154404c10454404c0c03003078a5020041c41075103a015014001c07000d841380740d01c3c07400d02c0086044603d45170841d100b1a00180c0061070110f2106406c09180c40e080d40e000d50074155940b10000340612401c600120040340d01d804240b003100c420002070510400b0403424070465004c484411380820380060f4410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 714197526 1250 714196276 714196279
    0x1150906120203060d081204060605040501050a1712040b0c120a08180c03060109021209010b0a2702120633131d1e04030806090c07050d020f0d0914 65
    0x50f40c0c1d5a954020075006148000002e0050000043e8134002a01d104a1076000720b114003024044284d503401044140c44082c0a030035404503004008020311155140095500425030050faa10385014040d40e14041d0000d5218080080300007aa400c4159001c0c05401218541c0404203403d00310401030040444000074802c120490301402c140d3303100c0000b0403500410150046c200c0c1c1c100e6844040c1c92019400c03420340d2031213244404003c40d2042ca4180a071690300700e0087c080e421400d1030502d000251841d500c030100d0440303400100400c0300007414001400f10080c050400c00721810080b040c402c0a5040b0306d070341840000300600108814690102000c03000c12a00d000715113890383ca00d40c0a0603840745074070181c42c03049044070915000100e24403d511504000d400e8001e1441400c8241500440496006000580c910006680e510785041c4c0c454100e0003a0014904040e41541c80303904d480600003d50000d42d0140d8103210501c24100321010a0040c01e285c212282883c2c02101e89444041c1c8002c907 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 714198776 1250 714197526 714197531
    0x7020a08030610200319020f0a0314040b071a072c0f031006050316062a0807030201050114180103060c02010209030a081e04050607240903080115090612 67
    0x82d0003261190032074181c0349040100041c900241c0c2102103aa1b0b40c41003102490f000e404252080e0094004554040c492007044068800c4081c13594048a6414075841c00c400c901500740b0010a0440e45030002d40035007817042d00c01c0c0003108ea41459055801038010119001c2002d5010035484580704040c0d00c4641840c522100003204041c0c0d0f000468000f00e14408a80520a0804486140406400c02d4048131401c0e070a4520941d400202520340405600441c00031404200200c016002000240c188151001c00c21045840c10340d940c40007030b0340c01540d068006070f4549005008000249442c0110364800f00e808001d00f038078442426000500500c00600b2841c0d5134100b114019000390101c402100c03008003665101c0c2110b140031401900840034020b1481d0207114201d5280e0001800c80d0300f0389074002c0c1102c3c00c0401654903480c5240c03034400c2d00c501c0c032a9290302c851902440f500401030410700c40d032210025581032031620140306440c8200001000b400c040308004036600552031058284694001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 714200026 1250 714198776 714198799
    0x2401050d0c0306050d060b1c03080f04020a150806030706030204120809041808180105041409060d0506270d14070501022512020a0203030d09050106050402040803040e07020a080306 79
    0x181c000f460154040781d0801e41d140c07031190401c082e070382c41018440d40485081d41500c4000c401c1404120f044000107010508070340c045001e40c0c0819200d26803040c40207101c03014494458407038030302c2544070301600c8010880c035a044c8040ba01d0144010005880319140c00c50a0a242c4091031840440a0700086d184c3e03000041c0411a58685420445281d130001d070340385600150310305d0b203540f0035030100f01204600c004507079040600d503200d14100c03011a480e070480380714050480001c21401602c05002c40758000380e5070390f0040c000340d818884144034400c0d0007280c0210031041c81c1410300c11035030881c002c4242d40002d01c98640158119940d04402c0c2c00d58440691100a903140480c024031842c8080c0703103d9002c81d50a00d0000310300c0440400110b225440c0341c120400454016030b511074414000a6042d00280066a10000c15500211446e409000041012079403400420100d03486074100728071035040040d042c030003e007100c2d0304640c10141e10710080c0300120704c3c0c0e100e14841d0b01010702100d204140502d80d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 714201276 1250 714200026 714200051
    0x80f070c060e0f1f120c02030c0706111005060d06051501020f06160c140102070602041701020c060a0e210309010e060708010303030f020702062a01091106160f06052401050d 76
    0x514005c070301d1141c4410029050728000196507908035990344d8100e84146900403e00c18412018912030648410081c4061203130b509c0705402820004103410381056180ca07418000c141305000c3c640c0556045404d5950710400350380020304105c0200808a41640b00d00240464050340700305c4e0300182d255901c0c001c50714101d545440d4202c400d19090021884d07002003080d50901c900d990041003100d807012030302080e185140707000500b40d0094094020440e0032450015161070640e801c41340b507001c543e405031001614a08080340140c04811103150703188001100300700120f0024442c0c0c0d901e0341003130402005503290100300100380d0981400010201030b2144081643d14200b5015100c0d02540140202e8a51458075030441140d084c80002d1110201c1404052191113011701c10949030580042100304001081c5e424054503602c00a445200301c0d07105100720700402c103506441504c440c03182c0404505410a0205480c0380700640c100c0040c01380c1200d4401e2005e0381c01808403258401a0013011070605009103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 714202526 1250 714201276 714201287
    0x83105101e090f0b031021020f010302041d09010b060304050a1506150c05011d0304031e060e1e070b1210170d08160903080304080f070c060e0f1f 64
    0x1d01c42c14030f8900c010380c04550201000d01440c890b4289003e14036502c0d83e00d03680380e8084101c0302d0100080030915000c1c4005424014541500f00c14181009071900756250080c4586904204901c408202c820041c4081d410080c09000760680c3d045079031500314200360322403030f45641d11030030000c0c5000c0e5044101c2466141075040318000f0050200e0000e00c0f21400380d80907084251134042124694031304005410308081c074603040c4011f1564680254242411559000d41036480407078055002160041c00200003030403802100c0710180c821001d440302910702c0c04081028913001d44038000a42005006122070103903102520f003171150f2010031702040d40f1202010a2542c66036040790745140c80e02c0c1641e80b40d01c04000f5050a543d5403682d0b8903a1541d4504d5401d102007951242d400c00001c4128808001190340080907580141c011000a4507181024807142442d0f80007130340440d41d089004600b00000e9412042109160310705603507a92410520b18001940040c402190603410207054202851891080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 714203776 1250 714202526 714202529
    0x605120114250809010e030720090103080f0c0a0f030509090a020a0e01030513050a0507261e070b0d090606050d11100c05061003061506020c0d083105101e09 69
    0x4000382c88e645d10702802c0c086204207000980040362800c1c0b40c08403805082400b8445d04990b0480000fa0a04a08151074803940d031043c2603a4882e4401e900007003022a0405140b660114420380b0369654940172903007405010707040103107104d03800c51040c000c50103139580082c0d58030b400001c2441c001515035200c030440d242000740740314060303c0e030b00c161140c2d201009000903030b0100f41c03018000441d0a920401400280d80849002c4201440c0c0000d40407600844452101903040c41e40c03501540c0100b9142c00305040c145d00500840032000d51120002401d000c014864400a0041500c9140f4081200c0d15040440c85400a45600540c09840701000042c40307840e020b00d00b1071344401a6003882c01c01d90141403196080e8001a14071902e00b0182c4d8280d00380f245014000c48002c1d4000d081069031005c2080148195020160b480220410200c01000e161141d400320508001a652078411081000d49010b0141ca40026000b52082c1080075603254011081406101c881c1ca034041c0e03040011002190810f645 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 714205026 1250 714203776 714203801
    0x11010807030e0604030c02030c0409020307030f02181303030b0d02030c01140d0e0606090121081e0d0905010e01050c09040213120f140d0503011701060512011425080901 74
    0xf5034040c4001c0603484028241203900850413a80284e60100c1000111001e40a000f90302d07500485042002446400d81c01c00700600003804006a03000c0c800c0340c004d4550084900810103c09116004100364041c031840d01003003015906c0c00c042d0340135640800d0f42e5105500405040c80402c0c004002440d000b00e003100e2000c00c8181c001d1100c1031440e2070f140e50702d64080c0d070f042c2e00c14080000045490828010a400840c0300f00d44080150741290300ca504090b4007600e503804884082524103044c014000005100c00380344c0810000c0c080c43e187c03c0060171140b901d18880a503034103110a01c84001a140c06440b81c002003201c005070398030b0902c1000d001ca019a9801030501042205450b018001988492503407107001d92120b03603040c040300c0302a83d01c0f250000c0d10680802c4090005110081e441c82c0340c0c0c0b450440350340001400030303110707000145645198402206036a4442c80480d49460701c1c002a6074003c2c600d00c40a994a1031140b600c04071203001103c0720001c02c00002d002602c81f200035042003000701c49 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 714206276 1250 714205026 714205033
    0x5150118090c0c030e04020a0206070c0c050406031a1e010b0a0302120a20090105070b0612100c020706051305040b060409060305070603050106050a171b1b061311010807030e 76
    0xb901c40b00604003008210b42540400e01501d1015640c0c10b060080312141c0e1030a501802c00c070780e551041034410305242402550502c101403000300300303501ca81c8070369030240d402600640d00e008050f400700825032000900e0080d210180030030310101c14038102e100c5415a1300307848042e91180c0810400302c009008500015420440304000d01040001c282d0020312000c640070032a0207040180c081800d44d41c0318180d40c03107000030002c101d0072000c00d05080c45d003138005500604154002d00720400061809020b114103100c440d5446084880c00340d01000110014280707410050305200401d521030320340700341c5445020f02560700c0310a80c215941d617420845000c2e11101d07008100094407420503c1d56401e240c080d01c1c003c0ba26000000c14420302450695054212136602c2c080f41d41d020314410080e805001d040c501002c2d03001980c8011954443c0007070881400c2e030140b601c07503407410b000a15103040806000c0050940c3c007900c034400401c0011b25100203060007803c1111880d103c2070004c0b80184408400e006d0a0702 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 714207526 1250 714206276 714206291
    0x3080402060c160f080f0a05030901030b0d050f0115090c090b030a0b0d050705030106050f061c061a190c080a08060310020f0a090e010b090d02122b030515011809 71
    0xc002602d88140c5c1c030984125904562807100403542d0780c1c064071014007681d00c10310034168a5072183e00254010a400f80c0803c54a61869039034501e0881d45141803a00d41c1d46801342c41401994800c01d40e802000614030a0000003140c9070080d003540220301511582110000001d4682116a082000c80b018003503c1d04d00d04000d181016074507021107010b5a4401e50900400144c4c1d1b103810307413101c0c9000398000c00c601d250004400380d000340794540d807414004c440d403078810008403e4010b4400003441d120341c6607019903c9101400d41a514182076034a00144440d0300710017401700d114081502c1e00f5241c141020386464980800080c6007040c0c0b18401400d050001940410024454014010310005a2a001010354a602c40d400c1265424040e07158048014410120f01d840c10100b00c008e0940041c0041c0c09034081c0d0901142000c250f041001141e643c3d5040c8064074207900410394204d00c003035260410843c00c101c000850704099510142c1c2c10424185c0d078081104014680960040440802c200500c2 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 714208633 1107 714207526 714207539
    0xc19090806010603090b060d03020c091b16050d1e0e01030209090108031b0a0b010e0c0c01061e050406030803040204051e15130903080402060c16 64
    0x41009100016051414000c4601030b00c0d10b90f42c0444c0401e01410700b8450800040c001c1409162a02038207070229502160041281c0000c5038603030a60b07198044075204c00103001043c40c840c40d50006d0580c9602a00c11020322502e84144141c8641c00c6103180d0035200c4280c0c140002040d00030780c45d48154140d11410b86a420880705040c010301300503400000ca480220240c0042000744d00004000d0102d150008260701c886c5001c3d401449028469901d1907041c1c18184148d42d0000316000c080307200241c02c0d40507628000c00c000000c104860303907100310310a86042c40c10300650440300ba54001c80d01d824140600c0c415a90022040c603d181c4983d400d010050000034020640226403010421003401003034021801852041c1300d40a42c043c3c0c2ca001c000841c102900c455110034501a61880002d42003103195602c250100c600c0c40d240c810417491507040c102404844090000854800700e107a = true := by decide +kernel

theorem cover : BRFrame.Cov 714028776 714208633 := by
  have h0 := BRFrame.cov_init 714028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 714028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 714028776 ≤ n) (h2 : n < 714208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
