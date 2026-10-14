-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2622
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:15:26.037536+00:00
-- url     : https://prove2.me/submissions/ef577e65-245b-446d-ac07-13cf8aef58f8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 471402877 ≤ n < 471582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 471404127 1250 471402877 471402913
    0x606040c0f0e04020c061005030712030507110f0a060e0103060e010b160c15090f14090a05070c0b0c0309071d0403050d0f02120601080709030b04120c080d09050c01080405 75
    0x14085a82c0030384d00340503044500501300b194034031807103648904410540c00c1004041ca00001540040c1000318045003030310020b50720400365101c0c141e004201d4180540c0340c50025241c21452541d1b0782c1c115981460000b000c551081c9501c1004500303803410030804d80c5803c0340300d030366100034005c00302001c0c400c02c03140311209a2050805041409902d282800703d40b01d8a1110b1000c00b58800c00d00000c2c540c0c04148504a80b02c85d480c0000d0514800400c6200c07520750100c0c034401d0700145400c00196503100003a80c9103000d46c6c010070a843e401407441c2c03443e00e003004102c1d980e41c2065404d01002e200741403000c5031940d81e8220072040315803002002c403c60342d20799030211442d40c01401c20383c1c0d485d03441e8181b1070403400719400504103410b44150301c4a81460003030001040c00368010403540c20442c5003581040170a0300b000e4881c0c2c010f90815506550004000c0c0150380715603640b0b4009001000024441c43e00d00c1041d402954958030490542d00d010f1004401112140300542d00074019400c143d0892480c40025 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 471405377 1250 471404127 471404147
    0x3170304021f050a021b010e040e10090b09010609090503070602090d0b09030c060702060105060418060509090601080c041515113f030f130b07030b030606040c0f 71
    0x7401c1e10038816070b9240440c00741d806100c00c02e000c07034400325000b000076405006401001c240f1034070032030800c00b43e4000200b906880445081c022680c461506540075070a05c181003017000c00b03040a01c202c2100e450040c40720002201d040003503500e007110100700d44d4401d018280078940c0050055007420b046480d040e00030351040d42e90070340c02000c4012860002d10744942241c803070099107004c0c548941c600c464240c10301038000c0c80d81c02190001c9005001d0399844030300f40c3d02a900304010124139100312000c900018401a007146d0744c480407407420807030a05800034400f4181c0381e000303060b591502d04500c00d00040c0d490342d900111052016a40a210010309020600710b82d543d10314114484500d100704690902d05a49841c8001c6002c0030710302003500c0341d482c0010300c1c000d910003e00707042d00f203181410003210702001c3c1c1021000f000711000304491036800d861f2000e80d135410040400070b5080012018008042d030252180c002d000e24400070303001e860103200701078551003544c440701c0c881d031107400c0102c80901d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 471406627 1250 471405377 471405379
    0xf031b050a0b211602150103030503070f020705040207080a11030906030402120c0d0c0602012f030702030c070e04021e090a0e030f18030f061902070606090906060303030e070317030402 81
    0x550164074007403201910b02140a1040b1840003480d484d045000203003415082056451a043c404004000195011007240e43c0155180341841c00c0406000c0100e0400d2401d40c00280c1c020b0000c1844030074400340030020318410400d40c80d02154203200680035502c07801400703260b550040b01800007401505051a2404010582c0e01c00e031506081c1840001c0c10340c520119003910a0703a01c011060003100e409200c1c2850780c091802021000d920740c50b07020005803038503140b0700c01194808800b08101d203000304162010980c800f0140c0e0891501c600c0d03000c1000208032016403080009102041d079540c1300e140c240d0300310140070b80142001d642d42803c20003d000082c1c8d090003140f00404c42001188620400f504a96400c00314840380002d003001054540780c1e20048641540c0c2010080c80f280505100303250015001081c00542c5035881030410704010080c0354000c2c8040c1d1b013011524000c00455138819070a8a01c681c50400201c02010085540c17001540401440c00d03194000304015032403164069988988 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 471407877 1250 471406627 471406657
    0x303060103091a0a061e080a080a020c0d0510060e061e01090b16020a0603051317091305070906050a020c0105180406030b0f07020a030e1909060f031b050a0b 69
    0x4403e00300c18071896080b0b940c00e2086a45140901c260010036103c051813001540c1003400302c505007044640c4440f008580140300c4040068030b120340500078404000007002c010300c00014982242407032074442000d4902c0122181c80c007038003c038601c204500914011940504180035101c10440e07550b040e140402c801c6030501005020000d41003283c01c0007000c8400505070001c007065601e00c18820000d142c0e42180d0281810322042140b00380c6030410030b000720340e008aa80f40c16200d03481c017288011b2168400241c0c01c0b00c00300104840300c8c520394011a000e05420b517540006543e850348119041d02038050301c1ca0040e00034800c0004158032400141c0020f810104082008844500c0020100c40d51944202c0d80780320003504000c0380c0c0e503001c101307140d01c41d40900191054030000d6030000d00e1400d03072621440c4148034a1441c2c4441500c100914406013807402e00410540e13491f002041d08004843c4000c40340394001000c00e100304000c1360000012564080d21880340c6508084503410143c00107484410498 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 471409127 1250 471407877 471407903
    0x5030106031e0c090501080106050306010b0909130f0f1103150601050f0a050d0e0a120c0804120f12081f030c050906130203070305060f030114010302041e060f050a060908030306010309 81
    0x140741c51103014024041f41000003002c1d440c1a003414100700050744001140310341800041c080d5111a0a101d602140c4034410a40c000550b26002e0700d484040e000140c01c1301e03205d4a12108224101420014680088080300d00d9501c06a01103800d90604032515800248280701c0f040b814546400500b1103104981443c03070808120616000c106c400020180c095940542849024008030b007028186043e000c0c40c0441001e24580c130341c0030b0684110310601c01400050200003040c030107881d0310600906d90220038108183e224810040403c201a2007285519609a0300c040c1ea060300c1060304030449502202c0f141e8030610b010100254158010403050700202d4200d10213004682601c0118460b581a442c00034003030801e1000d022080010040850007a8034000c1c1150000c0c2280710018116541207c0c08039803410000100c210203503650762406261801c10502154040d030b1010410f050310004c1d10a460040e40e80e44040322070149521503400e06800c10170116000c0e51280d0403031800e00e0b000c0e41c00b4002c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 471410377 1250 471409127 471409139
    0x30203070e120115080706020a0f02010309061d060606071e0812041209120515180a080903060a0b10111203070f0f08060a060e0310021b010605030106031e0c 69
    0x1902000b0480c040340d0b55505140c44a04400300e881c1d0000c0e00c0040005c007001428000003079641c1c01c42d17000140c82e01805945100c11680320b0f4100c075180c070b54088018015901d0350b54121010030300e0b0140f4180c0383c1c05560300240c01c9040580035030304119008061868061100440311032449105c0c20150340140080040c1000000c502c20746130f014a1080c000326541e10115031000307100300815003002e0184500300207010003040b000100101c07038151221480000e0344407a03284001c40c002c0a10454000e005101203d8180018500034100d03000058065400d5561060440c008541d614901300b640300c1c5120108074501441400004501d1044500310307400900403010110264001f00e510382e0000d0a811041061981d00c10740404100f002400c00c40128180031000842031240c600896003004892403407811030b035804004103503942008020031540c0342c101115400306c09480020120281d03080c030400080c507003014851181101c1e041650100c4502c604075181c240c1c0004900c05403a407490441c004205 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 471411627 1250 471410377 471410389
    0x7050a20030c0f0303100602072402010608010608100605040603050303070f03150e06010210151404060b070605040b0c0301030804030803070c02030d0801151805010302070c031a0103200d0201030203070e 89
    0x1243d116074015600c0386003c4400f8445d04a00c0d4000b0802c40d0400c600030040e00f00083d0b50003803030488030b6100310110849200101c0c01884d83c3c4c0d0001c5025030030302e01d000400c180086100e40761148028000c1c03003025121814070090302c0c2c1c140300040c01640200005007a81d4442d4888601540441c64081001035420300604c280103d990000340101000303000b805059130f0100000000d25007410414800304c450420348201080c00c0f84519000ea07811f11220200c0d95640340d01000240c00c1e8800362540700c00483c10920010003084400311495844c010201d0744070018a0286ca04803580020707454501400c5540c4d110250700064180d9083c48114148040140d4081c8120687c0120990359501c3e00e61400c642c507a14402c0130450081485100b501040110b13250005003000e0300c2c2c080c00c01680d94006d910744103000f07105541c400742003411400d4026000e11103101600307040701d0198603246540c0c1d1910f070204d10925103406c042a80300810b101c41c4e0005500070f402840d031021060410740c0c085400c400110305 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 471412877 1250 471411627 471411643
    0x210050f1207111f0e210a0201051320041407030e010b04140c030c070804090203010303090603060e06010809160602010905010f06080a03030515040c1707050a20030c 73
    0x301c000c035201c10014103d5025840d900326098003070003860001c10402c18103d01d6805080c4e1141c0c0c290721059840d1030300350104409030b40c4800030b4142c28250049040c2c1c081c540d07040b1035094801075007003501007550b80d800c14964106071500070554400200f26401c0c1d0342e03038100d150410103401645503203992000e44266560300c2e1046041c0d8402142c0040f0022115003100d00e11200705206a1505015200115104a000341e015000440b15a90303612a4034103c645401145401401c040d030004000c03030007030942c0d0050760403280702c1c3e120380c0c0c24241c65000c00c0d01a2459401100141224640001e040390302c80c50f80180c000d1001c0050380c1501c0310041e291003405200740c1002000d42c2d11502039108009007480f80c0300180403201402c01c14541030012454540034041409020982c03248040b650010b143d1800f5013001d0030060041003c5200035102502c2c40002001103078a02003100005144140140e00b06c0304a12407940e60354111004031103003520442a031404191032480180b2046001150400c0088 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 471414127 1250 471412877 471412897
    0x23091c0c0f03050c06060a0b0904020d020d09050a030f0507080f1c230a0b010801060810080d0c031d03120c0703150605150405061b011407030e0c06160210050f 70
    0x6640d1301400c4111494080c000e13010303078040d4010070810404044440e06454044d4070480e009a0340f80400c03aa000f020b401408100c00b41e0501d000c02200400a001890101c076070701c2504e502203205010401500c06016040f03020f040329408101030143d01e01058003c0441543c500504d1013103071401d909010843c0e00007072500c629505161b50761041c10750320606040c0d03c2903040500f0301c4641d4150000034582d09062140c4800c2c421060049416031180e100c1910103850480122a4842c3c2d01c40002015000310382070a40104e603504005450001c40841041e01c003000180003448002031004212403203a2020303000c41d88a000c0c150300400050000c05920b080800c0202010072511300304420401c0d24440d003405000500400c00007008180c56101c140c034843c0e00000080c065400c1404d403480d026000348203071000c00c0c030800b00402c510303641c00d40e00c460845a61502182e01150142040c02a01d1180004481d00c86080315001e40040c5095000d0f115018800d18285042c0003155402e00095001140c6078 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 471415377 1250 471414127 471414137
    0xa0b09010c0e03010b280902070606151b0b09010e070801020918011a1c020a02101b0512070e0a03050a170304030527100323091c0c0f03 60
    0x300321902e80c080110700d0010002c800070090003002000240c4200c0e004905e140095602d104401803801c80400c0c1d400c018446c2c040c4c290f503500200c1c0f40070b41c0100034130f003d0303456294000d00704da06a203440380160000405c06440d20790581640342d11654141c1c40e009024580079034035014030040700c1c4418440f01000f80410000942c44030340741c50801911102e1306003090b1714000c10b50010096403103076900c540d824aa5085981d5038503811141814190aa4551101459400040c040665a600146d0144004045002000a43c0e02c030340702c8800000c01085003c00142081c4151040e05001c00201ca0300140c0078141181c070201071001065908401c1e07803050741c0a801c000854414000745078603c03907071101c9a2240b90f146241039500600305010711203020141650f0b40e459410b0114181041c084003800c0203110a06420700010001c024014030000740c2046440061000410044040094050204903014114407128100e41c0c41c18860380e0303040c01003085076055440f80441e18042c0030f803890038000d031781e4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 471416627 1250 471415377 471415391
    0x2091309021c030f030207150507050a1202090d020609030c0a08070f0803041a1803030d021e0702010804030c2402030f060102060411041505090901090510090b060d050a0b0901 77
    0x400602c8009519002c0b04402028140703030000c2c3d0b10001007031400d400307401c00503111041414980303215111000c3c0c0387e0b6503603e024240100e2a07000000390840c82d07440c0c1d807806040e4540e803041c10164015409003d030410340c607580b440018542103014040024018003122480840e00d80060200f100711f0740041316030b800800c0103000707001c0080e2004020780200c3d00190326040c5001c4844d42008040d551007400303050080f0700001030104c4ca40c554411080024212070300c03441c65100400c025400380c4080702160f0010702101c42c14003000c1c800d407401a038058603a24595502d9885c15940c151119008842500c0811502032500b2000f0004903a0607284140050301e030700d080001d0392807080c00907210764195441201040001070340c0720b00c610030b59030003520081450181c03500000710b8081c0d25001154000401e82c20010301410541c8402c090034011801c0740d015040d9402090100d480000001c1c110b1011840002e1480c141030a103c1e4081d4070510032140c0490300c03629400d01210098800c0945651a004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 471417877 1250 471416627 471416629
    0x6040902010527030d0c1e0f1a0a06171e0709060306021801020606090a020a020709020d0f240306091a040501091103030f120604020f04030309050a090203010b07030e040209130902 79
    0x421211711460505068240d00225111101198603400c80486002c1261442c6002c000320b042d45120900c1d44004038411442c1641504207041c101180d40891041c90814000341c1d116142115400c8404c0c103002500381603010f0840c0000c004c91200800e1035512800000040805482c8254030080d80581e1005843d40759010301010050041f0714000e045601030300500580c4d41d6240019600003103400030040e0b8800010f001030341010b40a038010350300720388049900074001c4015080764007000480350040209981504143c0c464085900700c1d510858011282400040d0081d408480040d00650038200c0b1105031004c1c111032403008440031200c6945601d038500801440c503441301e04c0f07908102e01640c01e20750100041580c03405002070f40382c0802900c06c00302e0001c0e00c40358103c61101064102c8165241d480c1e08015000c8034840c841d09008400011000609141d24800d60741079407a084040e42c503002c0b041d1800c0344e880c1c1061018a5102d0707420010565903030341c0d450368025031180ca483d0126207015a40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 471419127 1250 471417877 471417883
    0x1202060a0b0d11011107050a0605091005130b0904060b04061d0405070f0507020d050708210415030b01090b190914010e01110a0501050f0f060a0e0604090201052703 72
    0x1c905005010650903500061001540215160420320304a05d1249907419481d00c3c026043d402103420000719100803454550110040c00c505e103007503c0514020a195104450611a50352456074440c90b005044c401000e60350000c1840e400002d001158407601c984d2074101d00c0c0d006901070000f10325410303100100c64840074000b4107160800c5800308000d107044880607101608409100c0d040140000c1c0e030008650ba9606e803c40d5140d08401190350700c6403103a0b0b00b6641d60880080505a46003044100d0180781322031030440f01a52035070613500350008030340340c4160b0280800403078603810301540c0080400c8451051010388010094036030346001034041184041c040c8000c50704420840c1c0c03000030306841c07203076040000e600642c0c800f864085400e80c840e00c2028246020900000d0030340d42018280301c9030703194030180c0c18022400d40c036126805c0d880b01030801c2000750017807141f00145161040000c0b4140342681c03140402c3c40c011b05190303242042d507c0c5a00c02030446200445080705010b24030b18043d040c20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 471420377 1250 471419127 471419141
    0x50a02010c0f21020f07060c0818030d0e15040c060e01020a0c1502030f0a03090b0f0412141e040f050904080313141b091e0a0b0109031202060a 63
    0x60425984412000c030000700f00045066031a006031038000090340b8040d260b503040710001c5072480381a40d1103024919240010341002100440041c0500e00402c005031864540e0b001c443c0260002035107421144402000a42925030034440180a0503658240130b981000c1c000d4416842804d403d00707641d043c108080c1c40d0003d00a90281194040c034a20b070006242d0015040035144c2c9034070340308550400d200b000c07403562044443d00d9000d00d80200300401501c1e010b81000c108203215481e2007002d0354403e501070641d5071701101c019185000070900642607901800e005a0401010000140350810384115901d03096504000c2c0c00c0b0f01c1c41c3c0002c3c100025107040b086540546001c6510102500b429103804500c0d00000e4101640c1c00f9501d2600000c21894082c03200c0c0380c01001d403d8030b502c48800700c00c41200c0c0d403e200b6840d02503071400b000562200c40c0401c7e00302e00b4404041205e1625200c4140000040521801c002c2c1401010440880820310801003441c80d01d443e5030041c11140f0b000e1512509540c0c6c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 471421627 1250 471420377 471420401
    0x11e0c02011e0f15061d0906011e091505040801060b040803220e0f190506010f030b0d05030c030d06120812131e0b0c07020306010b0f0415050a0201 65
    0x90548001c20389008560382180c405904000480c03031080800c0403c00030180d03000c00d80e4201014040004507113800a401c00340034084d00085024020018080c81010002200d500d4009000035a0841030140c0701c0b071600c4683e865610303015035025298a121030440c90b10f460b440000c5030300803400f000200c1090244401800c11a483da40c10a03103861110382e0340f40941c0700070340c8164500f0340010b04811487cbd41c0400082502068503250744c00e14004100800e00b080c1d480805401c12400700c001c0080503401014020318041c3d651643e050611003080300102000c1c10f206500c81d480c1901c0c000400c40c10405058580b04140140d40d50303040c0c0f190403404580c0540d00054000150420840c042140103040e2560516100d610030081da880f1030007900070032203981c07000300242e901e1200c02c54848103e06030309001030f11400240e1480e880b01100d61030140940e1000940c164040e41c014000d030401d040103855540d040008003070401c4e460702458294158003008210005d0300111b00315161320b0342402012000c0325 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 471422877 1250 471421627 471421631
    0x70504180b090a030c02091e1003050c0301050402090105040e12070302151e0a02030901290109091a010c0f080c0a0b0f040b0c0307050c010905070501080c04060c020d02040b03011e0c0201 82
    0xd0700303540241c0410f842c0240a0f1240c841c6100144103608404801e02c0c460303054a20b07239007040c03421182d05005141d85000a0320306114051803030106040c14401d00313020719001044110568a40000c00028140121050308140240d0b01e0226148501001a2600910940280881d80304072601d01205260041004444003c204002007140042c01ca0654000403545805030b17481d51680c20060240034180304d074048174058002c0c0d8008050300c2c80f00e0f62916840c09d0380c40c001116035501391f02e42910142c02e24001400010001c0703000300d42c001c40c0342c01111407150000c96041e01d0317283ca488100b40c01c082841d8031907801540080d01081b402501040c2c0c0112201100804c5041544820282c000000e000c44004500040410340c094095001d4409404054009000600072403030134645540d140c1c07140501085418020407080c003444400d8501b070706e28650300c145c00c42034683c080100c1151407140598009640b11b001d0182a1400c0c041d00307080307800e0301028038403622140c601c682c01c881c1c10100310b032b0031a4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 471424127 1250 471422877 471422893
    0x2180405160b180406080a0501140a152309040501060303031415240a200a0510050c04050604140108180a022413080708060112020d05070504180b09 65
    0x500c2d990036140e120000d1545008800c1191001c10300400540c0c03c050020b202d40d6103050100310054110707403800b01d4900d036500c040b0b89038a20a00180d070100c403005031036042c0b140c5e01804200882000071440f139101d400010054104500401e0314400c0645069403a40d4507210148245078050080d0140344082e03500102081c40e068100204152114510b98865101d0341d480c0850b0f0701c03840909203c0e4100c5e44071401d0303603034207040c00c094150244644010114102e0740344001d130750200800c030707d2038181c1c0003006403403407007055091100140b1009010800c04442804045001c0c1c9448004d440a0000055808020780c2d51f100003404102000b010552504050660000220000710380f000300d059040c0c441c0c03800711125442d0b00e09022400f1100c010040b401103052403070650480004011503808801765402181c030340f6107180e2114001d01800b0406125400c0f1000142400d5801440140c0280e0658202d15218000501a912a42d580c074000150426003e002c1c0031941078603a400c4030700c03100107005003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 471425377 1250 471424127 471424139
    0x1303080c0306030c040c0c020102010501080a0c1a0f040303030225050712111e1009030b071d090405010203010f090902031b010c0b0108100614130c03090218040516 72
    0x1041005209402808020000c42c02c5034504102150315094020421300c405c141e802c400070068001e074903060f40150f0070300c1c0000401520107c1c040012582140b40120640c0c10861407032403100f400c8044103d40307402000800042000d020282002d50306ca42e40269440204410902c070700070041c2c103010320b610410b9002d100011000a040005c40384802d503100c440d103a0764103002c40802c001c0d418417508041e0b6411130052408001c1e03182c422005040340c054401d845055000ca400790010b000c010083e845804c00326000ca8002d127451041c1503441140c031254440d0140201d0700106051314210b409d60340100c010300c0741068920000c1d000e070801c64010032202505800003540c1b148101203900080d6145ca114142e6644550140071102e80c1010145001d541e441034500e60b00c0714880c02440d4503601d44903020a01c09070b44011901c200704024078180e442401001d02500504000700a84145642da00c443c03801078403190500310710240800b10070b420518290812608012a0503002051006802e03414440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 471426627 1250 471425377 471425387
    0x70303080717060d02041a1305090106081f09080d0c0201050108010e0c03030409200c06090c0604120b0a020c010e03030117060105060706050a1107052401140d1704060f03051303 78
    0x13800750100e03000b0850900035284803924084603045603070000c64012104070805001e0300010b005103941d000070007090307603248007980d1945e5102d001c601412124450701d8061240071f802c010030450198440c2480c0000c111394070350445801821540141c1d44560040012400030311074040c100b07903403070301400b0559540d00000744c03248180c1c01844641691146024a100804120454110007a10b00c01e13680d10400c515080d038841040302c45c10204d20600039410171a040100c241c41c2183c840511011301e5120507594400c0000c0010b121f40700321030f400e01440600c8002401450309510301c18019643d203504014003080c4010000c8980764507035011100400c03042d140c05040740c10040d017001002815407141c07a07103c0040c200c54103006454401c0850414240100807a09180310007600c1d4034103100c502c001a500c40501024855610386481d243c13039081442c00d03c41c001c03645052040c18800c4504500c0302500c000c907082034009030300060301c070012000455054131540b41c01c044e54407840c6c03410701e01550340102 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 471427877 1250 471426627 471426649
    0x60f0d0c0e0919110d0908180109050a050402030403030b03030301060906112b0c0206040f0e130203100903021504140d0302040b090f0321130f030f08030601020f07030308071706 78
    0xc0360591311a002041601c024050f03075001c0d0503a81084c00f800030182841e407080c1c0c205c0b034048070701000584a11080783d03009403d110110754014020701e0301d480c41d05003000002d40005000390140340e224003143c0b00c2c0d81d030f06000441c0a03041544078180e201d801c0c0540140200703010740310700250f5400340c400325001518980500c40d0076100342e48024840800440c0031a0000800718008cd08002d001c20045038081071100d091050310070b0b032640b140742542c0b01c11502c68407400354a00a501500202e00c0d90364000211340100b25564001e004540b02c030421512034480c4039404803803c0d46ea10034800110ba008160902103100121035914043d41001d05107101c1002501c0b403180c45074030415085170034142c1c07500d0903c0741c0500008a0400c070201030242c0540748103660b12000b904c112050342c1d501e000c2000300c6040120420b80f90000c0701620807840b550348030701c1c59500282003039041d88140799140e000104100030390300186200e6a218420350030034280203451154901c5da11200701032403404101c0503031281c082c514 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 471429127 1250 471427877 471427921
    0x60f030a09140607051207030c140d0e03041d07080702121605060a06031214040b0705210a030f0501030b190245060304060b060f0d0c0e09 61
    0x22604190710b04080c40d1850b41048001c94003e080c20400500d400c43c014025030a03100d00c0041d101e94400000324211618940450f001c103851207200d44000b4150000b8001d10058280b0000300021144403661850b0403035840b58280082029060342400082e4000301d4211405003040411802c0550019449154607052503441801c0421000c03885009120003010b001d4008081e52450309224101c45d001e0308140c0802c0e94505200d001c449106072040c82d0007020303591801d082e58100760812000803035941c448013055a0503c1055080d03502c1d40710b0310414460151408500b155240c020050113020b45040e05801041e01d4a090b00400c04644100300465101065001100500c10b0700d10710940203002d91080c85c01b20ba194600c1c045d6410080400340e40b4095010804022420001407404903100c4001c890903402c02d81c20700220780056810f070001ca01407a0010106401c01002038840c0300f042d08070303210044000380c94006442c101500b0210f450032400d0162010009484d0400060080741d419400003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 471430377 1250 471429127 471429131
    0x106090612120c1e03021b030601180b030703080a0801140406060c020103090203101107050f0102130b070503041a09040b040e060718120c0303171b03041e0b0a0b060f030a 75
    0x110800061252080c82400c441c0e2204d0f140842c1030070300944e80c08044402e98480000a08a00d4403460b00207500c43c12143c2c50030300c80350050031160091000e0056281001e415105202c00440047d030340310b015150a041c80e9031070301d04661410740050102c0403c004c81a00231846c0c0b42c400d010b21a1320034040c42400d9028207000c0303005411880844e10304001e000e078407000a403800c40c00c103035100704000003460520302950880d0001030206101c20308074812114050800b060340c440400c4024091009005958064020341e42401d548240c80c200640e501d07000c4859a00300060301c201c0b1890180719469040005403002c00001c0501c1030303074540d50745000d17042d0b105200503111405550361340c0c640360310054031811400d4241c4031600d280140c0741100501048000c0398400b01d9040741041003415281c42465a04000082c2e43e1a55810000341c0d80050805d07103849a040070640c400404204035007024a1080c16440c4482c80c2c184101c00403521442e1140c0c0c401c0c542046044014141c840689801c41501480 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 471431627 1250 471430377 471430397
    0x306060801091a09010609090b01031401060c0c081501061709060c0903010917070302070509070906121b0c0501060605130504180b0a05040b070c02062b0e010609061212 74
    0x3d000101c0c08031807010b54081c18071030010840542c014600800c8070034490003071003c0b04681c0e006400360303082c0009a2517003c4159004012080c89004a40805400780000403601c42c1c5603500281801380c04041c0114460740c410040100ca035110800c400d026465014010143c00c003c505c8544800300a49090104080882c401c2600d9400703500040000e54048a0640e80958107001190103400010045d000346c058040d0001d04c0f03080c01020544190341603622114400d05040b02555480100e4aa01400d03994030600002248102d0240711400078082e154140390000303500d000c9080d5681a0014404c01c031080c00780380da609469005017002d641c012540425445460031003840003031510400034207046035003400d100d10400b081e4003c84c0680d018a4610072542e460142c1500c60345400c040094200c01d04111007036540320441030070440d124225501103042000e22146009585034076507941c03c103075910f03807080006044a02c502002410360848200c00082c0c2511041c0007140c800c48504c003401002c0351 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 471432877 1250 471431627 471431651
    0xa0c03050904020c01061e0b1608040302041a0909010c021e0f011805010e0303010b07021306030b01060207081009020f011413031103010e0f030d2c1507030606080109 73
    0x400d070742014801401c1107407103005041c0103d0180c0342910071490581074048903283e40d0616400322100762149030148074582440c809050304c0c001c050000c01e881c2440140320100040e03a89004604240710702d500243c00d0304806208204451074007078891100c80c4e2510040c240b10070740100782492010901c1000e030b1032000c90301c0781c000d051502e8001c104200d5481c019030380907118101160b150403123015074000c11540d44a149180ea5a12081c040c80b40848000d0114030018036100708000c64082004201041259603984d81840000c0d003078004070302581040100f800643e00c200306284114070001300078807002007560003040c16150f40720017041c1040151580e03441100607520880307503002400400070060641e2420b040c00ca031101344d20201c1c425400d00b0482a0164000502803240c5e80300c0308051407501818249000040c0600b80d02c24110009a4000200c2d4448a121040300d02c1030002c090118003103600100302e0308031700c000d000100b414035005051110661003201d050554000000001d2405030b00c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 471434127 1250 471432877 471432887
    0xf1e01090e0c03091501060e040504051009050c011d0d06050403051603030c09060203070b0c03060d150204050103240e0c07020d030e0a0911030a0c050f040909020a06140a0c03 77
    0x741052000d0303540c140500ca051080c501c02076100300e41031000e94411503c0e07948492202c080c01c3c4242000034451304a600814541070340241e802034822411241200b0300c00301201c003556000241034030143c0024680c181203507080b80f03001d00100c44002e0341c5018202c2d40700000d034810081100242c58a599680050105406081190441c100030317000c00c0d4080c86a440c004014000000710030001915098000804500000980e121558455107914030396a600c0b00340c49064000601c07680d4403203071104403170300031488034142180700108034000075a403603051000140c00e03240d902c1125039620b400030703140100010b00b00500d9000c1d584101c2000c042615004c0c03025055000360100654020b00441050040580005100302074020585140345000e564000342c1003101d1003034500c00748460040000a608044540c045561802117003405030a0842210700610180c11907040240c005548031501025441c101d5800c1c00280700a1606054440340d24146a610b070049106c1d0700207002507840540d00f018068 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 471435377 1250 471434127 471434129
    0xc090f0403111204030c060807020a0f2405010e0c03010b031f030b0f04050601170304061b0c0f181b0c0c15020d08060303070b0601050a030e010606120b0f1e0109 71
    0x180044401d10f5509840340240ca511034802110744644807100056094041c1c0c40f214490402030700507041002d410f0f04e030081010380860080700c071103404004d040403c40418405070304401c10b0070000505e0390b04007000154040c90140050140b0203040c401004055654801c695000380c0440c0103c07402c8400089155041007150001030401060f8001c00c4110f45d903000007148642c0c01403040b584a66038030203c5100043d40031800c600240c100300000d000311400b0f08491007061440700c121044840454556114190b419003004800c400c92170002c000120448400401144400000300586103490101e5507941050300d40c600d0a202800001d50103004818040c8030003004180c40b160a084022140291a070b1280360743c10001c6200752000c650141800001c2d01d03601540400700d1105c40e01e580c00151001d0f006800042c04041c0c98500305110355800307001d10340c010300858888421203a408808403041c0c030070702c06c2b4075405030801c41c081d80b05e03642e40e134052048455100380c40c1da10003444400040780d4403456 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 471436627 1250 471435377 471435407
    0x709060b0702221803120c02060604091103010515131a1c06050a05060a0f03080a1b061b081305060103020f040b18010f12050c04112101050f030c090f0403 68
    0x28007004d4401000b0181140c13440c0070700c03940e25921005140c0305d00608540e0102c2030600107034850f8000501c14141035002c00300c41070045640c0ca0003040314a0000742501d0b021208044200300128013060300b4101001c0d2000d96010415040c17003610980103561201c030710502c45052151500249003121a20b0110411440d1600100c0521551030310701250f20140c01e09a440501903142c0000004600d008640401d0540c1da02c035441526150004a040302c040c110b030500401d042c2c00e61903004001405901c82e00c01205581c410180143c01217402c040c080c99001081d004c0484040d0451034001031011a002d8192607048400320080d820f04400305004181500c891034005869071009840c46030042801c0741240c8e070b050f03025529580c4403038801c0108083e006000341580d00482c821061450550440130000580b915814181510b404041c0c80b400321a01c40804218030032001070100f420840c08100d10800b080d40209421481c500200d080044000c208414031407084000c5020540316004034000c0e445 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 471437877 1250 471436627 471436631
    0x6220201050f040e07230903120306040612060507021203010302030d0c0510092003030901051603050f0a0f0201050105040e070603091406010602150f100b090a09050106050c0709060b070222 83
    0x580b041024000c40200c02500344809245001d1b030307209410603800c507001c2c2140a03003d4031086540042d03a2885070000b1300303903ea1003601c954021401400c0340381101d10729409944085000d040c0f0300f9020381401d440410780d0a80303800420050000d40c41c00500290305600916245c10303101d01600b40725081003800380b4210103007410081e0031000d01c00c1c558087d4441c600744083c90040c0210110070140e59100300e943d0070740030440078001581481181300090703420a0203420083d1034100310180b1082071f6030040719002e0100320030601c9412126030912850f4090a010707a01000b01d203010450440da21900c601c552000c0503220b2400384e003007281d5110b01076291040c4108841c819611204065140c0015140a0040881200c00609a210590601d9008403981b0880c910b03454140b10700c84507242c0c84600c03010740048050000040300c0090f441f0387c1e0700800d401d546081d220703107a20f5040f90030101107030701600545050500c14012100448100c034516941114040144100741c100502d88460020841030a01c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 471439127 1250 471437877 471437881
    0xc0d060b0a0203090109120b1305070812030f0702060106050d0c0915090608070503010e04060902060c06040b07021e0303010e04030909090602072a060f022d06220201050f040e 77
    0x90b000009030001c08400d803114038010740c46040f4a241103e0840c00548181100303408140c81202480c200ea40c142d01600607241c5103a222400ca502d05401c0314000007407698008200038480300c5562085230084454400b07401c1304d5141640c020544e0044203000c082c61079980703ea182e4603500500c41403000f4101984080749140003410041d00e42c0c0302511444000c01c00032800981c00390321550440f41600c6101303818070610f0f1596140e46008020280d01240c020740300300440c0000b40340801c01184114810181e00545142020009082590500d1644884081d000c211903101001106803810742d0360306e29009929640ba41400c03038900c01194005d1142c00d00d84403011050054a80081c0745c024092000c240c05400a41c00000701c1000c205005400c00b464044103002c1d5a02c518080800040750b803044950100d0913000900240c101c2d90070f8512078464660300445041010700500d540302070f200822900c4c15a900840300156088c0010003030400c040090080361094003d0190380c060000e00a40704818 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 471440377 1250 471439127 471439147
    0x61e070f17060a050a230d03170703020d02030a0501140103092a0509091c0507150c05091801090509030c072108030a090311060907090f110c030d1406090c0d060b 71
    0x56654081b2291a06000903428504141400401e4181e00d0707034805a240088040c80c59a841c0040d049404040d020840315642088030300103140039a82d924800103455262440c101b414429407900d4605141c18100100003203080c0c1003c1d010b001c6507a10360001d501c1250800b0f1000e007280350b00040d6201c400c6a0501c058440002168007502c05c80a030780d0b0f4040c0c12003550980307a600805030300904412000c80d070002c0175101c1d0741000d000d00700f103410490700b0301c08807500180c0403029440120452800d001c0042001038800d02131282c0055105000c1c52030304101502c1d85880b5400c034041d104120000c00b43c460740346100e07480d4800100e50403640c4143c41381060392100d40545014041074002034606041c1c8140c81c400400ca1600440c0741100424000303141114201c0a46010505040c900303981e00f50912403000746800038405180c03641d000c4e56641c28510280c000301d8659491034032100b01c01b181000f2440c0c0b0b03000f10107074104281004058032603483c4000030020b002c81380c12607203001c1400f081d43d09034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 471441627 1250 471440377 471440399
    0x30706051c1d07062a0305090d051b180405030a1d030712020306090d0207090c18060f1407020901031104090f11030111030c09040902060c061e070f17060a050a 70
    0x20384944d9078415251a1604104072010700f442e00d171101c1c1c0010321104034400a40224001d122411020701440b44811903900c6480c20044d0104007140807080f0062380403a949000c0b1000c1e80c00f148554450a032608090705c030300d03649000f0400c0400900c02800d200031b40c0c103104036020020150b402000c9841b02c68560710301e101d002c400c0900413070180c410710000c140c00c4032000c20320b141a05c1c42c2c0c3d40246684d520700032150018080c004070801c24081c0d200c000d20603040507110414080c1050341c545a20319248071400a1600d0320084000070222030600500700182e49100d06c0d9070441e60801c0410038080c0c15200010f0013008096402455641c802c1c1060741006114425074540341c0045000300308408042ca810740c3c1a210817601d000b1014810000f14046143c540d02c02c00703620340050701d540d09001d0128510751510b00d05a500304d0208042a6140c1d00c081549851a80d000b400c3e45400710b042540500d01524411145111400c0b6a03502c9001032000d03180c9503284402090000c140d404400da85901c0720701 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 471442877 1250 471441627 471441629
    0xc0b09010912020f1c0507061d0f0d3005090106030311070303080105100908060c0403052802041d030706022502030a030804060f05010303021b030706051c1d07 70
    0x180300d1401d441c12103949002144490b0450201405401c01c1c00881c0301002e03d0880d03080d5400180071050080d00c0c081082c40c41032a40201110002c8407070727820510f80a80c03400c5020280039007140d2002d543c8100c1c150b4841d52a000c0302820682c0700380069207040c80a640030788103044498542d4a07000402c840a041504a901240d000c0c5c0c96649003185500d4816403225904e0202802142d080d6004104d18141007150b004269024948400626100c0d242d05040200a40d11790002070008181481803100500200b5004106040680e00c99210b5404030461341c5100e0601a21540e40c0d20000004041480740704041c400e003910a6030f60b1080a850440000e411070b4041e251959450005807612074003410100e81d106800400411705c524103641c040340c07c0e8100074030486405855546400e110821800b90a01951080e0090062103004520b043c4a400b040380640e8441e510080081103502d40200890303010b448403492451394140d00b0030100b00a0068800e61a034000c0c440c42c01c1503095034020510380 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 471444127 1250 471442877 471442883
    0x31e0c05091305010503120f070b01120308090706090e06030a05010e031b0d020312070c0b0f010905151e010207080303010e01080610050f010e0315041506052e0c0b090109 75
    0x1c1c2c1e0124258180022201d007400350580580c0404081c03c3d080075a800542041031548074103500e814041d540f0180344d2802a8807010645400140c00307010150094030031648803110200038000365150240c000e02040143c410341ca4030040040100d1003030b8405002c0388051640100090040034040070301140e882c0d110401507200109410b040b00c10341340001c540e01030800c51660041d030070a40041e02c9000b151001500136030034406604907020010f51403515043c46440c05a414040e5507140170101819a070000301801c43c038005183c4503074003656070102c0403900030307444c2180b4040041807540180e20744103ca40142282e03210210000030113503c200c10203410b17540c040060b20144d807039141c08507426074a07500880d41e01c081071110744c2e101d551003940061031383c500040480390b2803d0070749152009030358261019140c403440b02c01c0c00c0e030182519008001c010311003036070400000304403586141e0f800b030701e11080301c0a628050004540c240307105075600f50015400000096050078041501c2e8004c204101d012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 471445377 1250 471444127 471444139
    0x340b0a12060509070810081506040506040207120e01050c060a020403061d100908090402220f080705060c0f0f010606033c020408120702040e06010b0a031e0c0509 71
    0x464484005009000031160081c0802c0a1501c0300c10054640e80c0e80200141070f02c6c1070066000882075010042c0d1218580c0f9002244000d041c00002d120544000a001d1030085004010900c001007002101056542d124500b56222542d0800100d4041c407139203110000703600c55201801a104403590090084910880042003026101c1089107500050011f4100640c3c0203030304500040340854000f4502e091086019600d014001d40c009800c07078000c450100c080b551015074411429007032510307200c0501144084d600700c1a00d05a9541d503102614002c45010b19400b241622020b8020003261400c22005400c0c0c50f00c088400d90414020801d03031145000190070628400240c440c6502039090702a0300f02c00621aa1402d4000943c43d1030480030311003c0c5550070440002c0d01c000c24001250451030841c0d00c0d0b503482040f4010841510210221008540c03c20801041182142e0007140c0c0c030100d842c00d01194211200c0010b0049094041c10200341600748840402d610b0340c803800910700f0400031500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 471446627 1250 471445377 471445397
    0x61603050702150a0228090b0903250302030a08030a06090612080705151003020f0402030112020d0c330311161104020708040e01080f340b0a 62
    0x114240c030300544030300001d40c000c1d41c0b030601100f00300051141d204142031001740c5891860030fa007490307414264036403084002005c114616640e50021107407008015481d042400c100c14100020b803909085010300320718008440c1d40d10003443c1e240c80c0e07110040d9002004e0701c900e1050703810010080c0d8800c851406025162040110b03614000788a607205883d200d1195030005030481d07842800a80c4012030680b0745110b03c2d2200600c0d11035a58680c5d00c035034641c2c2e40756610306141d4810f102ca210b214844007031155005000501003450f4030359550b040a90102c8190310804480e04010542081b00d81210300b100c83d002071400b00110204400c3c031119880030b4400c0032080039015086040316071402103c1c1e00704800f04503820545224045070b1410314054120990501a090300260490317200c250201c071400ca012804000491b410380100340101020350207041035000700d490312070b1205130000104100c1c242c02d8011664000a290609410755500c107079040b8860307210a03012203d43c2000703045038000b8280d425 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 471447877 1250 471446627 471446671
    0x30f0f05041d0405030d0c030b180f0f041a01030b04020918060f09010f0f06080f0712062c0601050301051303081503010e03070c080709020304050a0b0601021c0206 72
    0x300c40c21a90040c000380142c46440070b2a01c0c100300050720036074640c44240701501800c031041c4078007002d41e20140c800080700078211051103405041c075040600449400c40411040c80c0740703001e241d03a000918090000d1f0590381c2d450061840241d81c000030283d0b011000011041000350b41ca624060360081f14401103542d00e01d4005106105030607400c1100e508038034041601103240c4148aa0041c14132000841c01c800ca003035038407048510144c0070f00d8000381c60354800c005c00d850a001c0c50860b501100050081c0700e040905603925400113850003082156942d004140c191310511440c045003503d00b0103510708100d002c03100c03641e580702800303554402d51811000c00c44844242000c1007a242d4103031180440c2e580c8054034041410003201071036400d5502d4502d8500d030900103100a005c0c962080c607690481606100303680d85030070015000000f03910310400620012034070005803000025031100c865a841c1e84d5000040303090080c180c4400c9030182c00c0008610b503998012072601d1240c003407900d40e5900080164 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 471449127 1250 471447877 471447887
    0x1b090604060b0a0c021f0504033f140304030e041b020d050705280c050f0609040b240729060d050307020604030b0f10030c0501051b0703030f0f 63
    0x84200c0e61882e104000da004214020314030480120b00081646042c22400700c0c4603403042e03032424421000110001001d100f000b2544d1207440303980114000385d1440b0141c0030304414050005032180c4061002c18440202000e11405001c01c160b51025042905c1e8149031501412101d464060385214500300045001c0c105807003404444030308003550003070860504144c0c05581580c4074290503a0075004200000821888029607007003041c415101860325200c4501301540b070704015800240c840e0107046a05240e65030340a0503228248411500002c2080704074000444054210280c03a00e1703a40880701080d40100c00328042d19030b86000702c02c43c00380ca9282c044046841c1c01c051202800b1a060500810b540381851080041c2461190040b640341140395000240e194000d40c0c03044501001c800108940f0709407030308100d504900c08550b05100d01e8215a640041e0304024003030941081000705441c103682a0143d550004044c040741520156900c0703040060564a00303501620100742070742d900d01a258812 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 471450377 1250 471449127 471449129
    0x9052b0f050a1101090602030906040201200a06020a030b1023040308030c031003171b24150a08030409060501050c0a02040902180a050f010b0c0714010c051b09060406 73
    0x55a0715031800e200c200041e95000c048410501c855981c600d40c800c0000c055100960165440400400051809100060661194184080f03200d01c0c00c1240b070300c100600061103003480e03a01c008090f0716104907010031001404140e16050381300c1600c01600080f503400c1007201c416544040850480303c41c05209100c007503c40c0b44002825170720100f002604115281011795044405001c0c100030250360382e12100c01c51182c000850200c01c0c400108490100303590402081141e104002800104800918005103504a1012040001da0307035400100155440b018001c2c40220040541440503100c48503d503aa4200c1d0241591881c40d105010660358040c1c81076444035171041004041c3d00300f5aa00348405030178051422a0800301d42d41b14070101946914040d171007000b52050004551511001449041d6010b0388100c0740142d04020320700014a010900b9005e55106402c0081442c0014004940104403a0005422801551000f01e0804404406812940d0044408400701c0d11810108401c0780d81e5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 471451627 1250 471450377 471450407
    0x1106090d03091716051c020a061d01031109040b030c10021507091a07051203010806090d180e061c0b01141504180e07090b13061a0c0109052b 62
    0x1084e0400a0b03190208806009154100b0180c110048a40c0032840d07a61040e008107012401700740305100003c3c500c01581080d41c00c246014401a060b1844400b041e200380114540034580360300603455a900c0070030240c07090a40241510741200d1012030b000f51180410030081c6005032100380410b603943e205008003000c0e169180b840c08128910703040c04486903070080d4000c4440c1e0062a0003a07903600a800065802440d0850103810030b4607091512a040040101c441c0003409003154140d0084414808200c0544007940c145036000d4030b07104001090140c6a0689403c0009142100c00030401d0034a08181254000f11a04500600c2c100c104060000c10f000c02c000210002c0c0002c10904090403040002d2003a0f105000400300c103000d441c83d040110380e4221001460300c5078403d0105003819280c9041021059004120040c140880030684003107100c0c484462035000303e0307465000f20303080d40300346c10103580081120000c1552614100d1041182d000c030058a000f0141907111050003a9046240201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 471452877 1250 471451627 471451663
    0x40617091b0d061407050409180819030207020d0c06090f230105070203070e1614090904033c0507030f050d0b03010f060f0b070507031106090d030917 66
    0x400d075414000a21581e00c0c0c00d4400350b8841c420403a0f00945204618002c0001da0788250784c4908050110094500001d4410080030b2034078609008a8804400e441004050500c505d0304000d0030715040703000c0e004148001c0e500c404035046107002c001d500c0403100221505a118002030940c5c80311100c10021329441440c1d100fa058610071600b15a1041100d868400141005401e004c2650007003440c3c0b191940050b01c00c84c00302014040c81500080e60071900e06824580300d03814a0032080c81d8511030095569840c040c02c9000040f50401d030141c1130402c070f11352403414031018502c0f11091390903580c02c012200c421401e111491100b03d181c4508111194644c01d81c484002d40d00292400b21401e0333020801b8080c81c2d983e2a103500d045a035003801820514402c2c0d42000c105241080701c04800300f0355a50085440440c20010703200003603030200ba1a0200e80d006003000e0103043c1210040340f0680724030b00c4001d5000c0d0f0400b80d20700400d40c000240740c042d207280700d80314003120059102e019501e130140f03481c52581d11 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 471454127 1250 471452877 471452923
    0x110313050a17030f21040510050a0c020307140106030f08090f010c0b0f04150c020c03010e15010e0a0b061b0f010501080a141002030f0714070201051b010b0604061709 73
    0x481188001c00c8004078112417035190241d00c1000d050308034020350b0103c9017500684181036182d00c50740551504011511010890405580c502956034415504010300380d803146420307008814006e501c10002182c000308800034941007450604100d80c0001c1003244a07098900802d80d00b9440b0310038404c2c07040d9004d41140c2031a00c03902074604003190000d00c21986241d0301e5450a0310840d0600552104106a4004040c0100751004160a40c1c031090055085076210b000f81c5240501000142411241c0030b000c0303500103843c1d01c541d42c4040c1c00e182807900c0c0c12004c00280c2c0090700040d80d400401d1200c1c044151038014000303d0400342a900700b072080100503171041c611711012408400014480c064008101e500c0445403140c503c00381d810854010310a221803c0402c40c056170004502c0404080b9000300741d11b0001203500103003607409508603e004c0e1a101d500303c00d4040b442540305800181d0b0080100d52210f40d83c6400a0242c542001075101c19284000401c4261b280060070680d480d004076007009202c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 471455377 1250 471454127 471454147
    0x40509010b090f04020c030403110d030507150605040212041203050103050c060a051201060c021302030910020922050712020c07210b070503041415010510110313050a1703 75
    0xa4121601443d40401d1480c0c10700f005030380d648010a907038100080515201c40c0703541421004201103a002d5402810f0312002640042d40c003800315544964031120750100f411400c0390741c00040c1030300d80115402910019110002c000340c5440e0a100368400c20261000c901100c2d01241954001c2c40024695406140200c14528100c40501801da106240040c06d02c0320712140f07000100805e034800c0c0045441100b5290542c1031021415041d0003402109500c0c0d81801c18160782d9503140c44041f4031119030b010818070701399601c1c210090301007120981e81d907d62062080c000c10080c081a078180f40030070300c850070380c003e00d45040c02a60300c0c49003150301401e041b914003201200b00105c1c80f0f02d080c09440e0b4140200d40019002190f44ac0505915030720f203512480c4c14035112400800a89418075a41e100c228200c20070f54000304480d06480e0156610342c1c04228800081d200300b2515a610001804082a80040c151010401004541c0111070b240318003562040010072844519400030f0702504100600040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 471456627 1250 471455377 471455399
    0x5010e2a0903010b1909051605040504110904050406140105150403080304020a0b03040503190e030a0f020a08030a2105061305040503070c090b09012114010216050f1204050901 77
    0x1400d01c0680003180782611600025901c030a004860020040c0c1d0aa00f885142c0c218450301d54040d82e010030942145551680c041c010b401503110b1248595103c60341a0000915a0243d401e50100940180030a0070030b490034001400c0c4e0341800400143d04800001002c2c0340c00300a054590303060102c02c6103000c2c00c648a640441d40000c006036086100d0540014180120314010344c440c42c0541d001d180c5800c240021400581064130b030503410084464a800410794020491141081e802003603181c800b9014404a00302c40c0c9107a0101c00e85010110382c00b044640c11001c0c00800404500e691008040210841c008484040d1031590700709510411035140380b242d43e44640d800c00e001e0012242819400e580307503518a54250022500691505072150741410030100d1603014000c0e41401d030030010204001e10740c9034216820082d01005240d400c09030010000e504030b0703050300c6a0707541c030420801d410300b4081d559001e40e1301d0302c1c0a20b10510007004003807040c440a480036118001c1a04840764a4210b01c20b103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 471457877 1250 471456627 471456637
    0x1022811031603030203031006080c0306040c030b0a0611061e0105010c0c0e01030809041d120a0903051204060207090b100302071b060815010221130f0905010e2a 71
    0x80c0502c01c9107940b07411180310124a5009603c01d42c011541d901d000c410985081800381c1c850360510180300203028a410480d015280d0002d0f0988001426100d1f0f400201c0c041d081d030980b52a04000b0000300462807690000452030394406200441c0d000fa10740c041d10528505840c484040e0450b41c0f44018801c0398070506807050242d0240140908071516031608000700c1c403080c3e108032101440011038460b60300781809401644c407030500714140c0080d00c02c0d0506d078540207180028000d040002590a0025005406403009180c111085036140318003000080402e9005024280140c801c49030001403100b5a8020040d40c1d21002c1d00840c0350420700301040d0042d401ca490111124031000b6820f4840904c01034101c030041c41141c3c0c400070315007004501035460022840701c0c20f04541103c0c101079000034030f2251405e40e030181448940d903101610407000c1a0880b050700312075205a50004006100306044d00018181e9204c0001203a85031601002d804542d680044c4002004003200405886142501d01400e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 471459127 1250 471457877 471457879
    0xa081c03050912041d060d0c030b06060d140a0513031403060103291203070512070812190c0e030607080901110d020414030115031410050901090201022811 68
    0x100c88243d401c048407603580042d0410030130481102d0001100040301d0005035040203042c1c40b800018078107611480c04d84040c500003d00b0102d904004140d00c0c0c1c440c04100d511030700407814200082003e9481290320620701b9034600900b20700b05004907880405020179094000c5c3e0503202c080c400382c1481c82c1c807083e40c0c1006024906041d550b00c4098400c2c10442405022080161100c4020001140c10800071010b554043c000c1c0d6401030004030005134000031030286030803091654a480301540d1410f009503216002d400000a04a00c050201101004081da02921202c4106001d2002ca15604903080c5403644141680f5512400200303440303500594a4540100b07201e0004039a08003900403503440f5501000450102a600107002c02c224500004107241420046000348005880384420801c5203c0310b0102130010700c11500c541c102000200030a070707014611030800f88110310301030b0308040c02464006070036400b501400c034900d84040c0d6a1023140c000c1640341c032000f1142007000c0d00d450103c9a0551205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 471460377 1250 471459127 471459133
    0x1b060d05130b09011508030406050901031d0118031b0804140d02100c0317060f10020a0605040309031217190b090f100e1005040f02130b090a081c030509 67
    0x207074045192608090b1051030312000114101000071417050000140798000103581c1c1090206020b0039a20001b00c40041409180210350302080081e00c024251100030764030f00540c0b0382010004060b03d09000d510140d402900c6221525a00035141060818801801008101d00300820b100c1c20015400055801c0c1000e04020502e0f0300d150f02261401d45410039000105422144280801d40c0c403405108441da2603110040041c1400c0011030541f070110700b200c078880d0342c0311114081854400c2088400c4190001c80601007801c10b4180070781410142d002c113071990300c800c1c4880210a4040c954074a41244200c402c03005950b01c2d07a1402c51940d0b20400c0c50f05119031502c044890666602d6a030602900ba00c0100e0b03100c40c01c040703803038255400d02c5030b02c0360701d802c0004020070540c95000103c810440b0b005450105e5a180110f11100c000e00c100c626041130340030f24140c081821042040501600b50301030315015a0b0301c0c1c540c4072003592901d400c10016233242c05115401201442038001c00d810042d04001c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 471461627 1250 471460377 471460411
    0x3091505010830071e050f0304140103140f06190f0504061d0406020f09090c0307180308030106050d1d0a050105071416020d050d02010c1409060a0818070e091b060d05 73
    0xd8904002485144815550000c14140318ac0c440c9940441ca000030242010010101c0b40d0065504120700104100010501c140c0011441d0321002d036000320422044900401c001c0d1075540e189840142401414000c43c5450004a041000000640c90101c11a1034100c4241c0e665a28400650f0241101e00c500110034003410300743d510340c0e8112500070b1581174003050b101d1405410090030781c465800c0100403400e04c581c1c10000300d41c4610449055400d185809962841266000800707031060140178100c58842c041c81c800d10707200105200070705611074802803085486040c022a1110b15201122040080c2001080101032145803200d01d4248050111400b40c0010b48403d410300310000b2600015075140c0a140c01659800030f40403000a101c8280b5504003048180802c04d14042c903040042403040e03510203d4008641080d00030314581407442202c0400381c03180d0300030744691000e0b108200c1d1845404400c050b180240100124580317070150100741482e5200c03581002078600030f440c0319888215015 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 471462877 1250 471461627 471461633
    0xb181203130b0d151203080c28031a030c01031d01150311090c030f04020a0b0d2c25030b040c2d050103091505010830071e 54
    0x100e00001031600300a140d89458800c100c5500713403080305200c45104901d0140501c03c800e8032610a1050f6905440d00400c103540f03d0520228500c560029006c8111100340c202e000c0004101c003024450b02a07550074010f503491704a01c031071130f03051500041d945500854180c000304d5100c2d03403100c07000e1003642c00000300c40d4165151040c219a00203000d1325480e010a0340500c2400304100706029a12401e840021003864503040c100c4030b602003e00540c84020458000c1000e55854505800180884041855032140d40f140807900500c0703950303009041d5212420b22044030015081002103840c107044081d16120511002d1001c8511030009003000c00e50801c440800450b5000241620541c071039244810500d041c21000d44172911000c0c1030000000354031071040c0e4206400450102212001c2c01d01242c000c0c2c591030075110154510f040b0035603070340c40c3c1000000c001c903002400440c0b000c01082a08401c0c402c0c0070300700d00b6044004030b1515207140104009000140f000600084514042e044818860f86540e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 471464127 1250 471462877 471462907
    0x705010f0c020d1404030503090d0f02090a1b02060609060409052104061b1a0901021b06040303050705070506150d050102220f120807050a02060a090f0b181203 70
    0x1a0441e8010b9109948080480350064015503d402c00302000500f41491aa01c95659204828506008042e201c0c3d018013003100440000ea0195070040100b102464a641c00e60000c11924100e40c030342c048a501c051075400c0c004965140198800342a180b5503503201c1d824440a0314802c90110748602c141e00c2c510a00d0200001d44058401c0380103000c903551460110001c2000101140c2014000c0781810038600090f808842c0707060070145d8216a0940da550107400a00902450240100c118402007a03141c43d03510228400744104e1198808000310f441d071510072074007030081c290300904991100020480d00e9a10803416420140c000b070030b499194200b0303070728182640c00080c55805071104070403118180d408180c6103d0003601d032201120704404d2503e400419243c480010240a50400089103c180002886883c8a0640142c207244d901c0c1c0107018000c144004510510301e02c5d46002d10041202003d4208440c050501c95040143d80205c0c0b8080004c282c054059000040c8810880c0b00320740f00c084 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 471465377 1250 471464127 471464141
    0x204150f060e090a0b130b031614031005010602030318011d162c0a0212010308030a180201080f070c140f0105061207120309050d0803090d0c0c0b0705010f 68
    0x80c0e40c821006a40c20001c0c4880203c0152160090a090071842196602d803410503000c840d00034000451244802c1300880d04128a0b1880312902c03142030000443d90655010112048020540407160f954540d5092001201c4003800350100507002000841c0c00d4540050b89600074061140c00001ca40c1005400c0e40280070f41413030311054035004800800d040002100b03e0800030f2000d95030b411710960315400340041c0404480c8038004400c058001044240315540c0c15a20f101420111220455841c2c0c1889806600700321014000d141c2844480400480042e56480d202c60f410f840d0400245c0b200c0581090b0741000601040802c0b5070500c0140c0030600555902d0f800240040242810703800360030b0400d09403036004081c640100301142c0440312500e00043e01c0c00072540ea041210240425915044684d1000c982c00958028150443d0307100303110411005502480c3c81e42c00700c8540710740c001008d0365003404007c07003d420207106001c10450300b01603500a2820500ca000009401c407210442c0108880d90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 471466627 1250 471465377 471465389
    0x1c18050901060f0809060f06010f110601030f0b011a0d02090102030d0f050601030606021c030e10021330230102120f010b070804120c03050f0c041107030c0204150f 72
    0xd00c8050700f40320794100000315082000000074000078a0010100002e41c84042c04840c100400112840c404910558802030030003a003000b41d400320350390307820700c2c8003121508001640d600d4902000014030040c0c0c541c581e01400c0b521002c0d1414003e0310b0130a00300a42001411a055001c1000940b5180d0014032030301c0042d00b1501e00025550400340001402c079001c5811080c10740d4402c1c84003400310b0091004c80c04a211080c600800c100751301410541c1810101d8400381140f40c00810800c0b4030050b0f4080e540700355605442c400c29601c02c10b07400c0010f02903040c034075000200c1e0040101c43c0490840d14010170901d0b100c140030300784003003000c08441c01c90740010003444500300410b06100c145480300c42c406004108000c811810481c2d1520b4102c03680c860703442000100211002004c041001c180e084038002c540080554081315055035005403603203801d1505c0d91041d440d141c2c4120b1a00020010b5607900f5425a81d40354071450703664203006c000c0c404100585070021407034000144024040d4405009005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 471467877 1250 471466627 471466637
    0x1a03030313060e1506121c0c0b0c28091a07020406050409080412031e020d020609010c020d080a020412030507120201090f0210120501090209030c031c1805090106 71
    0x50700741084411692020884000ca40050082180444030b0560158004c0800c0f5500c00c01e25801108861510040c41201c1c001c0c00c252000c68520990009042c1c00354034010480e0b85450b58505030591070310b200d002d0301010301d40782441c80184601c0c040342e09802d07440c02c03e041901c421a210703458040d10b06001c1c10000c18503030f000660002181424041c0340014032040d03509110080c225036488445001d60f0290041e00645071211500741032181084484e940880bc1014450504940e030003921280e1949000004d4850b500110350580e0741481240111030440e80640a0520500002c031200d10000c0c018240c1d01c0d40900c0007081c20600300842c20503151090300c0300b59407001c19141502c94083c2056505040d64075056912002ca5510240340c0001a411212622041c005100903190140000d5800b10814902030000c540001242c1c0102100e030001c074100d0700c81062640801d80e46240b589107500c09004200d18070200c00b806500c108407940b408450320303203001361518041903122030709a10180c0021 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 471469127 1250 471467877 471467911
    0xb07090509010b09040f0207030c080708042408070e03062a0a09031e0f0b0402030a060603050f160b1902071d0f010e06010c02010e0a080604140d021b041a030303 71
    0x700e0b00e1b10038864118032600042d801c283c9640c5014280d40095403014201b19000103206040151311403c45002d081e0743c0c417118809a00b039050000103c8800b441303000200d40d1741001708030b400c2c0c0a1080400000c070000c0090402d40c0d1081e081008012014407405100b00b80c8584001c6080d0446028225600465440d185002d00c0e50801c0c3c549181c00c048080c902d4038007218a0008a03d04442c0300c459150451240022900d580c03020901d403102030364001d0026854040003000b088400301d080c042c2c2d00c6140c022103032600c030035142000c07400c05240304007142c0340020081d542a007a01500c0780c0d0b100c5003550055846450707844880b8540110f4481180307505003214020441c01b004000110b601402208001d0b0b401407800f100040d00001071280c000e8140643e020b40c4001c01d9480380f26180203015420700340c0303c0e241014130701150303005e01e10700e0444014028a885204103900c00214030309409000c145205081d0182401e0000070040d0307042d954601240c2d44d1810f84251030420080d4003815102c0224000d00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 471470377 1250 471469127 471469129
    0x602070302011b0903030c0201090e2a0f121e0f0601030c1e03050c1e04090c0230070606080f07090216020111100c051b01060e040b07090509010b09 65
    0x1144206000d010030800f0209a5403601e5100d40c8a0701603c0d8941000c07030104619000580e542400d551003030628000000803c0700c640c02956103614481291112011603160307030800034840b8061500a0b101208042c0860441d0130304442256412980034010039042c0001e080c01500b08240483e030140710600c0d00d4007481159641440362100c001c4480c64904054404102401b03042c083c1400d1a104041d00c5002040440c86c062084440c8115058003912540703941d16034102c640d42062160025152030181f070100400d00200b11400c4181c0084c18818200076241d42c12104440c4241582e5100321041c003420001403140d00c0703032202407c1104001c0000c0c04014601c2c1d40b61100036007000c1d06590060080749002c044072030811006c1135090071300240001804014614190030401005a2542041203d004050300f1030000c046907101401c500b0081002000c40500341d84086c4102e20084490000090102d48115219038000d196468011151651040000c00078a400c1c0c1107501d00381e82c001054501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 471471627 1250 471470377 471470381
    0xa0302060f0c1309020307030e0f0109022707050a0c08041202120f1b040212010b0a140406020601140612090303240625050a06140c03130201030c020f0604060207030201 74
    0x400309610422502e02003260503d0f5104140c280b1550142d9500800820b500500035000070500c1c5030b00c0c400303c801c000d0038695040e004e0600003005070b0207003072000f128241302c0c1000104c403c91540362190000e078584034080d045130180d000e0134106080004500142001030a03003030061004044003c1900700c51065030042000e090100304204681c3d40c08090509000d0802058440007410b09003c3c0d800d83e401e020012501a01c035001c03040c000c1c254201c002107584020000030300071040c0c990b47c43c0740c0000d6076994002130b144928003c450142e4018030040103041d503180405a6081c0024100302d06048013028920f81105081c0d90b00c0403960004000c04c80ca503001820b032180f507081f01c803046c3d071b804107034080c085001d92055426420040c201e012542d0380c800c5030a0840045203502c40c1c00c44084103d1400d14000503e032a10040c03002843d034801041c848a103500517a80112110045011003075803d600541c0107010141002d001c0d8046c0a010300b0500308144045e502c01da00540015a0710034240c540282 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 471472877 1250 471471627 471471631
    0x1f06030606061b0210050c01050115020f0304290904052503091a0a060f0b0a26060906040b030304030f02030d110d030504111f1403012102040902030a0302060f 70
    0x100700718400c035000000000b00058501d0491301035036a20500402d900048941c3d1040a060b140190300304800050b400c004030b00c40c000c0178403142c1c1c2500c094440d9000d1560700c0303100342e00c07510b18800b804c031640039800c058000082c161010013026007443c0c441510003140507600200c880085d42c0320081002001d600f1407216040d847c0049150803c03c404080e520203040340280b9111007080c800c0d100020701c0f0b5404a51011001d0500307110240d80c5d035507590110703028980c02042000001a07049141c9051002a034048400c0c0182c8200114001c2e555101844203100c00206841e80c4a0380b10306d0340800c0e40c0c0f0244001c1000e103009480544803544e00340149440d010150303071a9020009614001942018041145401d6400300d145c04a03580d140d605014028101d1400150740c48070420154600d80d000740852104545482d40710141440c10406c60303d2002c1c0803d01c55608007000d0341300703100d91680341c6940045405d0b10003400041d180449070040380c50540310304001c0780580c0c851414050740381d900350040307a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 471474127 1250 471472877 471472889
    0x30402030c061e1605061f0603140a0c0309140a02010908280c0305070b030f10063606090e0f04050d2a051b06180d051f06030606 57
    0x240f03400403a00d09200d20b25401e96100d01c00c100003050001d40030f8000030400e5007903500b09003110064100303141201901280c0919111002580c404009200c60007030041404100060904035101d41e03038081e604000c0c03c4021440010140d0f01c10700c2d43c00007038001d000d004e05000c41d9801450700f1042880050060030310f075005071802d58003054010061384803a025082e204511888541680c0a01d031801d405014165040100b4500568001142030302c17642c0c0c01366210300424005448141c54035070122030044c0c041d02034107000403030044c042600c11003040c881c40e408100c034040d0001c00056008000e03400f003866030004070001d00a84006c100c41c030900c6040c207801a5199410100605156590315030b6803440001c03400034006003680441500c0e44443c2005400b07008480f088a4002035854500d0f1914a06032148041e00002000d11059050210070b484541a002200080700c01c142030821518541c00c10049405110b58000700302d5186032242e0030701991030601c00c081405419417401d1030690b0f0043d0010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 471475377 1250 471474127 471474139
    0x16030f031d0c0f1f03020a2a0b1b0c030301050a1509121103030a021e010b010e040f020903031303030f0822050c03030a090f0b031905220503030402030c 67
    0x3080c0410106100003881800c58000340b940190002107246004a5260310101c400203000d13a440d00c1e40c040d0000c00302c8481e44d55481c002c48035541040c100095445d076680c2007400392418140f0028900011840c0c003c011221104c0d40c0b0400b1190100003603101c20368004403900040300400050802c0c84150000c0c00802c406d00a000840d400001c100d1031051107440c03240c4140c45d0800007446001d111440c0c1c0300d10060142d0fa078030b808244000c2c0d51201800007410301c000c20300c1d8141c1e821b890184904699020143d54a079091800b210421010b07020605d07040d00c40303550030000d00b100ca40e401c000408081d0804040c082c030b16407460038050b0000d58500a400c1c10300800d031080114419040f000d0210b50750341141100c0c444005810224a40340c81800b0094140c070001603804801c0c1e0700070300400102c8081036403e0101503220b4161036076030b001c241c640240c008510b00000f19010341c1c540080d68051141d0010380c401d18203101e0720700e0221507080001d48003500004280025402c0038009d902d46208141d0ba5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 471476627 1250 471475377 471475421
    0x807201f0507050a0503040f020402180f030111040e090f0706020a050609031204030c150204060c020306130233031315050106120b01020a060603081c0c0512090316030f03 75
    0xf411600c90605a4000c003d4000005002c00945c14504140780d50064002c44d01e4882e000306144a103001d0780d1929116122176040010b06160502865191140b00303090142041d107003415000c0e1090001c0c2100035030b4001c074170940440640801081c0f0040180d54028200303040142061820014080c0c150701054208120800c0785c45e1500002c0e41c0c1040d4949003014019003242004900c1d070600c080e900030164000100096225480100003004c2030003102036030744588481a558400e480c001070001d400490358108104601c8170740001c0d81c50b184110b0018404503402c9080380455502c110346804030700710300842000074420300c80c10300740141e000d00c1410061075041441c060800038601c0b0b048102d20751541c20f007144907482070145c0070107264450300502c043c030b860303190181040e0005103083c41c4683e248140d98800601d00e0040182c940c505443e510725080d50500d01c50300c0300d0b00003030800c40359200803c44042008403c0c10399a01e440d02071760b122091070b0305d4000c0003000c1e9413010014070009412a44 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 471477877 1250 471476627 471476641
    0x3180303020604020108040201020f0f07090b0a12020609061e120106110703080c010b0306040606030302060c030426071a0f01050a240323062106070807201f05 70
    0xd0b11581068090030a40003941d65840100c0c42c100c041828410980200e40c02000c0404000500f40152240020103204140c103403c00d01488490724420801c0840d5400b40110140c1002d0300209100c0308098259854004284962102d5101422100e99005400150030100680d050b01c1640500303620f14181d074510a441001c07980e80e141501001d0400e540c00611100c10400035030040d490200050b0a6171540d00e01b60400c40300500d0584000d5015008a01c00a40e80358211400c40b8070469204490300c042c3d040752400c02d140d0728204074030903004131000c00003480800d0080e40c0c0c116003080d40140c0c414141c0b501d0752400c40e415006901c881c0c00b44c111118188280720384250291490f09241900c0e500401e00208200d001c2c0c00c60105041d90740036045c142500103c2004001d40c0318180035100c00010b410000f86201e00710040c1240d078600744c1c20000125250500c1580c005d0340107c460301d07050b40c4954440359680702d0740d80801c07500e0101d503001c10005048403210304070b0070309080150b4034100440d240c502 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 471479127 1250 471477877 471477883
    0x10c0206030702240106021e0102040504060803093d03060f09051005041e051e0f0406200d0906060b160302010506100e1203070503041413060f060507031103030a06030318030302 78
    0x125405903005201d111802448c400b50706580c02001c004109114a594803407095460f507100070040e82c001c00b080510200080502c81c1c0d070700c03a0800ca1902c0e06601aa4071407400302c001184540450406031250340006003d214001d02c1805425403220014aa04003c4540442c02515501442c001d508201042c050090411201681038921100200d490f41c0d440c11410f04940700c1d1400d1864901000d4140030540005540e0a48182d200300d8081114250a0350081c0e0b80f010365909000c1d01c0003041040070000242904003410345071041e24081015a15150a0f500c40d8100201c4410b59000803d41501855424000d030303504440203882d540f071000700350580205003046855540c1c0c01940d448841c00b4220700304104544038075400c60207480c1ca40349c4540110f80c1500200da900d51240604c2c41d91000072030340c50310848007118501e110240885103010000d07030350354110500c207400744015510740742c104400510055225640103840000c05070304514000d4450011602e1020b030b141c00850381800044d03000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 471480377 1250 471479127 471479143
    0xf060105010302070203010e0106060201150e164b14040506130e07050712080601020d14070c0b0405040c1719090510090b01050102010e07050f010c020603070224010602 74
    0xc0c60003583d1040b07940040b07030148c02d4241d110101c1c0e40c600000001c95030f6040d409010a0302086160914080e0b40e181059031000c030071365255030360344000134a13100c005008103000000d42450180a00c0c0444804028022021803800900c0c0c542c1c04640c001b00384003c80040c440315800031400c02951800100c40008014040c40c000c0c24003035100010200d640e298078000400c001c050300c00183c0c4291600c440300a00e81e40200508444041040903484503040c06001070038458901070b40203004030702000c10101c03081800d00715110000c5000b04100408030703242072155030280c401c06081c950f840e0310308070510023102c01c2000310310b0030494425800c940705449040c2050300041c2d4030b40e02c24004000c0e0b0300c00000410140d40010038a20a072488c42d0840d03442034102d454003071301898103104507a0341c6400590a03101601900003141e08000400d00452134001c046080801043c0340800e0000d016074045a110f900a580301c1c4003503400400200342ea01c94031401e40c451038a0f80d641d0100254540100a5910214 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 471481627 1250 471480377 471480379
    0x6040b0604060b1303060b04060510090e010b030702060a150b1308160f031b091b030515011b17031905070c17030a09050105010605210702070e07020f030d0204060e030f060105 77
    0x1107100d1407c080d13843e504403102411001340706440f8840b8042000e042d01ca0703180301c5d04074071340b881c0c80000844100103800d07207114442603000303803009503106000c400080020208001e400c00c6c031000042409109507010b0010360f50303071804c0707c05201e003000c150030700e8510000094140c11032554030031b010144903810581c04403a0300007000101000c01070350208a001d85030300b1a60405d49049a0f0017000c265400c0c00180c0c0e401c00d42c84c100300944908005203510001d1645050100b05102402c5001508102082042d0f0b80100980000d225524805010591050303031001c440881409100ba0301290b140714907a0041e4190908000c864070503566031040030109c400144000d2030100020300c00d41d585400000c00c0a40c000001c100d1507848220244c1550000080704100202c81c2c8100684802e40c0c042140c040c020940081c056a4507100081250321707c010b10100460091070350301f590030541003001e0480b100c01003002588440c100074005100b64550051144603030310507100030000c0741002c1981e50540d94 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 471482877 1250 471481627 471481631
    0x905070b030702010605060a050d050a060f0b0c0703140105090f0a0f031b150c020115141c060e06010314061b16020904050c010311040b1207030e06040b0604060b130306 74
    0x346045003030b4018005581b040e600400e0024030702018aa01400034422000740070b508000356140e084103031040765801d00511080f40740b0500700744003103185040680207a160145c1120740c421344aa03240060301c0f83d602c41406d6160f44803421f203c4245014002548504000001450303203140b56100c0000807101200e000e4107011150b04550313080b568007800300c4503103500481c0a800408880c060b110040c45a05087c000651074548007040282c480d89010301182c0781596030180c10f000c51401c016040070310401d186042c0540a040400048035400b0702c00c020031003900608015850341c209030359600d04072000280f058010000308280112000c0321300c0081020b00740c45075203a003000104080355480c41440654001c1d0020100010400002601e00c054042a641841521420601ca0a4901507405100742c0583e0501544c4c2c5656134000519601101768900800c10f50040580c0380d003008419202554258050420030030181064002d40b0002c0a003d0030840c40c02c000407508144d0720000c0d0000800d01d80d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 471484127 1250 471482877 471482881
    0x1141b03060f030f07030b060307050310020c0a0c0902482e0609020f120411130c180503070302061303120203030412020118020f13020409020a120905070b03 69
    0xd12200300ca102003442c0541112441c075140014155181000c0c441182d0141d0f5140020700203003004689001110005002450704070500d072a0b00001e5000752541030380c40e20507021900082100c81780c0c2d150081c410001c00590700d2500446041010b07000c1c039000000e2918102e01d07030740349030f80869034801c1401c2d00d03141c00082102410710301400c1000c00003c00c40701d9105412030784007040207141198003040c410179040003030950b550040d005070b0145c001c102d40e0140091100e8100070008000b5a50301c54804c80382030701003c450100040d41d00400c012a00106030740e58034030a039269005201c41c0900300741aa0b030314580c50b10b0540000d603035500502009004100c003007940380130803481d0241e41002d583e110b00900c20109250000070340e03a0300115020b581d14401e444401c40c1749070044c0b0840710b401c0070060026010702510303001c2c080c02c0c41d06885d440390030600800302441060010f1001e0409850340000c0580c1e50315109100074116110402c410280500d4100c40c80001803001035403108491044001c035490b9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 471485377 1250 471484127 471484129
    0x150c05040501140a021f0b2b031404052110050c092110050402090f04331a120708061308040e0103050601050a0b12181f0b0301141b0306 60
    0x3441400e40c11091b03286d500000c2075484068018503d4110240d502c042c00035a00c0792400009102c0c0c034508090b2408418480c00404e01c10180078803071500b1100090320b020355a0011507408003400c60740860600d012500209040401c3c0550f481601030001c0a1000d400d00312004842c9100300400c2520400384050301d50241f1318040350096941001001381e446c2000300c0c410500217420205d400701c1c4607148010000b41c09030301d0200428012508600c04e003c0c612281842c101c00150201d24155a014800e2200360740c4450500407101426012618054046004014040e10070002e0b00b040640303400c10901885121000120703958402c0c000c144101a0348006d0038a800e940c484e079041018000a1f400010007805400144a8101c8406881c41d62002d81e48114401385402030059207070501802c0408141e0800700c1140040c4401e42444c00d88022910200102a10801c10300503595100d03101c2811203054902841095204c568503021a4041d1800047c240110711204039000355a610200100d801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 471486627 1250 471485377 471485383
    0x20f16051e1b0f0a051c14010b010f110d0315030f0302011a06210c070f03050307140307020a030c03031d160f053607020c040614060d0e03090d150c05040501140a02 72
    0x1550340c01c50b0849400c0300e00321f64128040e1244521850200321001003801d00706118260038840c0035074150240c070f603060101d08218058181d40110040246c403490010000c216129581502d65100740c000280e1a8808001a030981503c2c81032244100014007003917501503229010030714403000d1230400f1031140e0345006c07c1c0c00060003841409883d2800c105a51402c16030040e0080d40a4046a1a048500651807080c040c03188400c441180050b0800c50900002130700410351002030510034107002c11500342d850140000a11110380f00070390781e40b001005108042907074a0480140002044840c0c0042c209808070b11203241040101e009140184074080d280c00c564200d02d1070440040c8007503541d0b810030355402903841d02c0d0044802c0c400d606d13050f00041d0032100468100c0807044044d000d00e040c09121610031000303102c080c8102803180003c100400f00c55903103001c0c0298441c8101d0091028840589481088540c0100341c00c0c01d10401704820700280e0707000404000b6414003a071040356110b528007000c86c2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 471487877 1250 471486627 471486679
    0xe1003061503230c0f1e0f04020d061403160509070509060403060c0806090f01120203011d03040312030e1b010203070c03060209040e01020f16051e1b0f0a05 69
    0x40300340c03010030b0051484420b20380b108040a20307034201e41c02040c0f21820042112400154181e00200c1b130305441e10842c000d40d48000341e24030b00402003140440c406011400340e034010180409913559462041c804c040e40d5200310f5000030000d4008000302c43c3d48072800c54650000d030145034031442c1200700294603544035170112000ca490141040351038640c2ea20b881e2001d4480e08286102240414000900505000142d00d1050006074461441070340790000d9140c2c1c0c4240c0c288141d8141d521a0721216061407510f2500d152a0785000c0116940c5195007490580105403e0a401c101401c000040c1d10600000901524101d80c410340011801d04c03500041c2d20710700c1140d50040040c03844d079070300100344241a809007180b107005540070310145034024581130807403290b0765803030040301028803541010001c0d0401c2e0603c4584103008a440a07400f18102070050840b0242c1002d03a0351041300800c502c542880003d91031a03c040e100040400804030010b1008080340c0240d034050000c08160014600004210746 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 471489127 1250 471487877 471487883
    0x608040c0b0a09050a090b010c110a090207110f0306040c0b0f0403060c020616020705180c07020607050a020406050a080c0114041203170c16060504111305060108010e1003061503 78
    0x75036260800c00c0058601c0d040c03845264401d0000890002d1a62042e005026013090140d403250780301c1c8100d80e5507011040681014641100404002050140140c0f0052100038094082ea00042101c0c504100110a8002072a4083e8218105100008082d540b00c0700640d507004c0240c0352034007861042e440c1d8a0103598006045c450030009000e103180e0f0003040150040c4002c2242c0001204005410303aa03503500c911800b50010813543ca00005a000b4000d501c2c1c108908400440c0342495640016000f40c001c0202910345800c1441450b0440c0341c644501402008250b404419007490030480980320105003500d58140200d542c152904075401100721405403207020045201c030032a50400a00c290250300c4002c1c1c1d0445240c010602405e441c0c000d40d581d82d480388801c0c421140c2c05540d55000351030064000c480e00d070b054800d4400144e076880400c400d5881980f01c0003d10341351540005203580c1c0c1c10b034021b00248a04005014299041503016401e1381d070444c90114100800d04004a60804598005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 471490377 1250 471489127 471489149
    0x4030f03020c011e05090406080303040302071706060f060702032e061a0f1b060c0d0c08061e01020c06070303020c15061f032a1d09010608040c 63
    0x401084804010218054000c0c1c0c21100103160000c015a050201081c1c0c290452424007104110203100e0001031011040103000400c000ba42e61802e281b40d600182c404070096001150180070017501112696810340c1420001c00040c00c002c808160b800d24840c2400c1d004010026450b030075920700f00700e9803080c40c48419000c134030a84001003c00d02c80500300101510103044c40000600002101c1d0580305203500e891780b039882c158088a08420a138481039108014614ad180c3d45054000b041c8a40307441080300c00d80031a9640905800401140c075407001c43e80c01d1200060910070503460703500e030000c518601e1070f8100119465180050340b518044460113644988001414420154541c020b04981c03985881201c540d80050704190410b03000c1222501d030001c0210030980840850b091600d010421541030014180044480e403101c114098407940b41510141c1c0d5000c55465442140c1c555411504112165800c94030b5000030010203041c8100c4080045c00c0c4003141c00d000514012000515140f00c103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 471491627 1250 471490377 471490379
    0x305071709071403031e0a090305100614040216060213090614090609040f0b0714031612110313030509061602041518110d060e06100504030f0f05100204 67
    0xc00c40c0d9600860141a5940700103d85500c0c140c20000161104038284820780700541084000508642c0c200c40b9000c003c0120140c00080410760502ca202c0440d0980304012034074500b0035a0600e40b684041403142c1c0640e2040060100500c03c038013820309003e600041c05aa50081d0701c0300a8007508040d00022405882d19000080203202c04031a5110200c0a0355001040d0351004104012094125000382180100040e0100000c0f140c00c0c4e03041d800051810100c898003441503800f84113800440b554140c00030703240540421603400521801241072610001e0200100b40050103c0d41c0c080540032040300501d440800e070401d40503d040d00d00d03044d0060040c81e1105150130607481100310740c3c48180c1c060381c41c11845e150740f00c1c54254640207403000700043c2d99028a9030381c515002010084d0141d5603044061011701f414120500920b801450f088412440300e080400801c1199060070062009000040000b00300082e2820300b584007240c2c1040110a503140035080c20740c20078441800100d81c052000034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 471492877 1250 471491627 471491641
    0x18040e0f030711090708010e0a02190e0a0f0b070201110c270105031b0d060b090705070506340306030b040c06080901050402031e070f03030905130b0105030703050717 73
    0x4080d00340b250041c40710100f0058003d05000350301c1e906442c000005002c034001805000d40fa4095030303400030705080f0010328100d08606103114600f1144681d100080440154542501d072903010407001e000f0070031140c811907103410b642d40802d00c16100002d0522982c0c031003484810b001845441c000100241c02d0454020743e100c0ca0042c049640e11125604941d0745001040d1414005a118200c3c4044c80c1005440c59450b01004900042440111491030700e07410944056161a075140303005011948407a0340700c0c40e5502e09141032640040080000d00d0491000300f511103590601501c26105151502c20751208906c0120040c200c26000540b039034292800340030801498038850011203c80d07a40320346a81c0c50760034006083c1d0b0780585000c0d515512040914112100a101c0004010303642d0040700c12041d42c1d44c03585002281142d0065001c258649810001410010309081051285100400402d0341e060000380041c0400791281e41015136500004d1030840c0260001564007a8450a1043c40d2402007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 471494127 1250 471492877 471492883
    0x1419090c09081204081207240b040c0c050601031b091104231e030709090605090607050406141b0a0c0501021b03120702010e0904030806090f010b18040e0f 68
    0x32040c00b02a00c500705400307074403408800c03d0701d013507070b031880e020380804960340c4420001600020425600501044552611104444030804600024020104114541c10100b1040f103a081542c0d005000802c10304900046001c124581580e501c880300398042d190300c2e05030540711511600000c040307510340055400d000d021103000c1c04c110340c014031a540a00980303900d2040410750944000341c01030550365002c01c07a115040416556440e0207070031074403426903c40b0194241c03801200241c43e1171f580c400501503c0380b41807001d585e100a1a0510b14074252800d1001032603200e55041d4401400c2000c1030340041c03038000d000507600e800c0001702100c5000006040025495000348995030144c03240400d8100c482486045505031581c0090150100e030940d19003208955209280c101d0401119080603c03041c1d8030400c025001e07074013039035604000346869418411b00c860f02034074100c00c1c0c11500c00108090304219003250303d00d85544036907421040501c400304000e0714130032458001d180152418111400800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 471495377 1250 471494127 471494129
    0x417070c12022b030e011110090c080a0210030f140c0d0c02060c0f03040804091521230a0b07170a020702100804150204090603030e0108011419090c09 66
    0x80381c0361682d14164940c900888040441509100e000c040464004640520b81c0c48440c5c0d02c041c10800e203403071070100a40341001c04000c52420f100b03688480f25030130b200200c021000034010000003044400042d80002c1d03004400401d00c8000c054840c4c00c42d98014280d03811015040d00319842082032414030040000c2c40f9041028940c01c1c541c0351074105120030344001480ca0280800d6401c0ea0714040288443c50903c0e40010070540385404100400074840f40345100701500c1c00c0c40c010b0341d000503504202146445c1801c0c1c0010b480d540c000948040b01003500d0f00d9001d400400c101c5404445440500aa9401c1901c0c050014114142d1501000031094011540d180102e0708011404085d60300c6060b80707400c0b8014054082e400040324440d440380703036004401080d0030a004d07040040003150310481c17540a03a8010b80001d07160762380322a810030401d50001050003100000b42003250443d8107040300800804880440b03140700b4240100a10301c55419503400401070700d01c410f030921800c49282809081940d1fa = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 471496627 1250 471495377 471495379
    0x11060703050d150f050402130503031b070b1309020a03090515090f06040807061d01090602070b0606031603021b010e0a050f06040b1504020d02030406060f08030f030417070c1202 78
    0x7861107000140f0643c000c02c105aa28400c4603500d400d0a10090100940098080c840344410720140030415590800c09003220400b2806030070101c403204405c6a04104040d03019220900d030174419140381c1c0c86d10307440c640c00303440740c95900580740c10400d28220094800744501600714045d10300018030020201409070b00c03907001801291150510350841c16030311b0070b0854024011407018019400000e400d0b070444003034101c01c1b8040c00c01f4481c030580341c5e5003100c400d440b0850720140e0003d605401c008c000d01c4010361208003200c0840c1140313003402c240f41f55130050102010030140d00080080c2d60ba1044000000e8014002000300710307c0044010325591401045000c0d9000d100700c8285a450710b10000d0220712440c2d1004c602c801a454599802000c0200104401c6d803150b003c6c08040103c0020b44055442035014002c0802c0c05454514040401d0034203400440e595001080a1802402c0c0c600c01c8942190744104c604460428541c24035400e401100401050010304c00350002307030000b6601104e1403141c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 471497877 1250 471496627 471496631
    0x15070e13181103160e04020402030402030a23010506060405061b1009060506030c042307170421110a111903030512060a21020112110a030f02030405031611060703050d 73
    0x2008101341d1040c2d000c1481107401c41e2a0300e000040060070700e42c01840d049440034048a0048403159103480140b1041901d003901c4080c500c1d44c84403403510902403203420001c195042c07480d140c101804a14107229407805450400030341c1d5900d040e0504200a10510b80e0206d0380c0030012280240741210142c80255501da110344207084480c11249800d00c59481035120203140c002c90000315650b01203001c107000f80030f0310912152010500944100c0018503214512070402032010b800005000d4038191285584030003000104031882d0207112000509031001c540240c0000e62102d01c0c0381c00902900d84d0000c00c4030049013101c00c0041010780020240102e1404180041600e60f201018000704240900c2412040b003100c9250440c1c114901d200602c8160042c904540a1154166840c017996002114404141030004250a205030b151007001a0249249015440c1d4106a12015540c0c0a86005c41601c80c2381c00c1c09d001c0c2000410f850784102d81c20050140c5403134040b58100600325030801410382c20706078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 471499127 1250 471497877 471497893
    0xe041b0806041a09070905090403050406080708070207061d100309020a0b030603101e14180102030c04170f0706020601060809030a02070312020a020d0b010302010215070e13181103 79
    0x3140c00d000d100250582c601210f8824800d5030b00b0040b01c000b02618001c01c0c40307480100401d442d107801c840b0a10980c000e0300d0390b41d92a840d00800901c1820010300c400704128680046c0602c0d01d5012030b58004444c6985082403014104076244032b821a9054402030740a100e2011040c505a090780010026034003ca0340c0044c800d680c0d0742c100e645031104031415581504494a030182100c3c030750b0700115508440156402d0b600345000c042000b00c0f00508003006400191b82c1c200b064000340b02000e02d00b030404040007035095041010480025000b82c0c010252400311001d01c00c14000d01c10000d180e01c0701e08000840c0d15055440c0c0019440d0313242800360300c000072543c00004d05140d1001007101c0d8401c1403035000b030610b0744c5541c6501510000e40340e59101103001c0e0f5250440907a4900c4206209540590100c080b65491031001a142c1a010100c5802c113075910010070484980010050fa900c1106881c00146601510f410304001d02a05201d5a40d08109070990010f10003241404024000c0982c21a9088 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 471500377 1250 471499127 471499129
    0x1306080705071707150f0f0b010e011d06090a090509100605032a040e0304050f1f08060321070c080105010b0702060c010e0d320d0c0e041b0806 63
    0x82d20855101070f0445486500c581d0300c0c018508001c107003043c020201e05403070144492030081512106503504042940f00d18000c40070b20541e00c240f0408031406d0a06510040e00d850000e0000654105d00902c2c24078400003025241d16141e0840300101001850000015203543e164001480107884050076880b44500701c40c0c001c2c1c0140b0918041da40c00400a0401c0c0c2d59001c0d10600c2c4441144040010003284442c0340245c0c2c0b65401a20780680200340a1900c540c105000c0c000d03138800c00e00381c2c0391140440c02d0040008200305211502c032510185003540c481c3e550140460301d064503504c64150041c202c1304840720320010100c0031b040d800d48992250441d0039a18144036090b40c90070f0240414900040101c0001482e007000100958824640046a03080c410022903050001002e050360100305004481c81c052004015850f0f044154001001400e551008610905010302407030320740810340d40c4400d5140c01c0e0184040d260805402401804031101d0091100429103100340c3e01400302c0c5809000c1141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 471501627 1250 471500377 471500387
    0x130c0c03020f070303080f06030a120306080c1f0f0e1f020f07030503030a0b1c030f091d0a0b120d180602060c030406090c180b090a02070f0b0a060b13060807 69
    0x13101e403da1340b001c03041c0d22060701000c411203024010a5241c841c4403503a000041214a051041c249030361800604646403034051030a081f418554070744289030b8a11380104400c41034116018489551400f02c04440107a01d00f55418001090095440220a4075112480c0802c84030304003101415420764007003034106050703079075100c0c041d02000789140c0062000840000b0558442c98115900034500c0103003c0a0f07803454005400303150300c150300090f20b64016450440d0030159220082c500120850f41081506d0684d120000700541400c18083e26100d498115030386202440c00da001c4081d0956001c00c1c44884060310300a003d40e1403a8600b240190001542ca0000c0344a501c240e044d031001602d10b50b11070742c1340c0e40180340202040301d03081c1408001086403116a20381c0b1101d601e642000060b08040b1404104c6104002081c9010b101d00400200c000a000c3c4940d44912030341c0000c15401036144d07681000080c0c507964000c3d21560f0004160407070f48400d01c101c17200407030749039880d41d0000f0f4503155400c8407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 471502877 1250 471501627 471501629
    0x80412030f080f1602070504050a0f0627020d0209060d0b040f0209011b030c1a01080c0d03171b07030302070c0603060f0e070e1002010207020316061b02130c0c03020f07 74
    0x40c0500140011195810604c06a240c1a03183c41600c54242d2a00001001c071101902c200c403409940fa4074502410900f40310302800782c20300101c05036a200f11180d60109480e80076100b5040641c020070f2510b201c0c6425010f4800a49004141684407c1090b00190080102e1070000f4820f609100c00d40110500310710031245c1d001d10694800640300d20f1f026100ca03203521002011020410050150400b04843c200071003030804c821400c004180d49402c030850715004070141400c0c4240c01e4418800002030700140c0c40103035141050910205980c910f01e40c2c070003071041110006580c1c48001100800c042d03040d4003d0441c0c40c0309120360010f66840b100c045089513280c1c040e8004041140400f4401040308048407503102845140c1071910322110300c0807880400c00f00c501000542e40101d62441186014415001d0000c8855810021140341803001810780800c501c6060414500c580103070159266400c482281c2d0550100c04d0000300141d9400410318180000b00368018000c0001c0c030400c61130040780302c0c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 471504127 1250 471502877 471502891
    0x29040b0402030114041109040e0f10050106050301052808100501231513060c1514270307080c0706090803090127150f030522030c080412030f08 63
    0xc802d500781407017400000c083e62581414074480c14015581540d0f141d01583e260b5034800b501819200d03c0200f1600e160841c1e5245144c541d904100052218030780c01803e07a0b04484084880701080002a0f4200000844e4100d40782e0280c8030100020440941c00035950f007404c241d20300304000c50780c1e8560660071054031794078054a0113488031030158281e10345003001100440090f50541d103002c5413040c800f86098011380c00180401d0b07010540c20244040d808480a00038070260083c054014103900700300080200414000201501e030340c40403440d907015101c404003456120200d0fa5181a40c1c20300c140c2c280c0000c4500240351240c0310021401d00d2041c00c0381411100540000d40c2030034090b40c0190f8501c9400148900081511a024003d4180f0a014400188010300d030100541404220042c1007080380400201450300b01014060755403843c4c010324031b0344840300d20107140b0320b285031500310b403246221304000c2e01040020502003075241c0f402003030901d2680f09440d400001460301d801034800007001c485074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 471505377 1250 471504127 471504149
    0x1410020715030c1103030a050a0506030109020a0605130341030d0b0f09040b04150c080109091b080c010f0306060e04050924060f030a05030f0d29040b04020301 70
    0x300700e456000350400604682c080c20090845072402011a24640049034400b640c540ca81c0300b4804403035042d11880783c01107401d0700244808505034020500c42009441031004002000800307100c02c0c04042c01c410059580706c0c0007100d1214150300800c5d0740d00004071900c0ca09020088150070b41020900100342018000740281d41800c3c80c0380741001c010a405604290403000d51460082d40750754005042c0e01c104c1c440c10329003041b404c2030f040410100d50b90b04400d5200501e4807000005094000101c181160000c8001142d081c00c10f1420010405c0c18400b50614004039040c041450000880c0c020700429003030780d80d11001407030204101c00b0b071101c070311400001c00c90300203059446050903004980c4c8810181c048840041918080d002503503c80000403000c4407000040c400c0c58a0f040b4507104185d82d080340103003415280d0384c59298032480b541c101221080f0000558140384091a00b108003c004004044207640c3c0c1c403500781c0b03014201c0d26071803240310310301d80440d00006181c50f01c00da905070740031581c0c6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 471506627 1250 471505377 471505409
    0x20c0106152c030102040302060c010f1a0f04050903070f03121a0901030f030309051b043204240911040e0309150f030103140f030a02031603051314100207 68
    0x101c07000000b102609805540030400800903884d41c030020000c6541c510300000c0d094001044080840d92007000d05207400000c07460980b6640e0301c41003084c2c9e003040115130000d4030752035003100a851449039030001031901035825101d41c00e01d608030040320313001d9041c0e41d070a1011408900d0200100341607140003d601c0b0b000e12006202103105900c1c4004d030b00e48a418001010381140d200c01e40350210145207142c03031007400341a0070b00340d08040c055868400380001d200c18400721315600d01084041c60700f030302c42c2e9044802c4e8001000d200740d102d0107444120a00c1d81d04050210188000d10181c042000d080e980c0580c412014940c6081c148a10b50060070300601541c02c1030121010080c07008902510081d40300001c1c070003002030070185070003075000310b10521340081654824140b641c185065400c859040f03401c184141c144030340c1c01004451110140e441c2d481d000d0251450107848a000d42c072110312460040da40046a880502a041c40c0c0c8041d08542e035480f010320100040781c5d108110300030501021007590b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 471507877 1250 471506627 471506687
    0x1b0201051e0709030b0402061b07140a05030604020904051005040305030f090d0804030f1808030a020606150304151b031a031212101508100603060803070f1104020c010615 75
    0x194160f00031344014184da00e00202e008276a50a5809105108400d80101c40d08018000380c542c804040ba11042d00c0e9105401e1070480040e072181e000400290180f02c0e818005070402c402400711280a20407242d04200500386414010000e4200300d42c0c0c20750158800c0080340a514000130180302e0310340c0aa070750703001558456504554501c8903022140078414000d0140200e84072000c2144003400f0403c0095885414000000b45003a0015109a009801494684a0101f404412a40c0c00358115003290f800c3d6201c3c4c0900d60080800c0702c000982c10341c500001e511540da0641000301e52601506421030180400010144c031007a45050901c0e011034100580c102c480020307805607501c4032403142d00d84107a80c9da640801a400010482c0140001c602d01704000b00780342c0307a0701c0f164041c6c800c1c0e15082103500c0c14481ba2a070350303224a40c009050000098140400c01090214080c0d403048050001d54840403c010784178040c1500340101d0b0501c01d4104203450605100d04c8050740395410700002d46031340001e800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 471509127 1250 471507877 471507893
    0x20108010b0723070f08030d060e3306120a0b0301020a120f0902030a08030406110f0405010e0a090f02070b090c0603010e090c1e10020109031d041b0201051e070903 72
    0x4007804414044e2000c0001e4410803206008018065440076603a41d05402072040300310752032600a503d002c181c4400b40556074034a0046552103101c1105041c1040c000400307409144002070501382da0141000644407488400e0008460041485482c10f1103098150000c150070f23402030b51034400000f8200224807108966582107594100091203002078003202540200741404141e45041c0d81e0050004140410410640701d480f405036541980603090030100c4210405034412403050a040051500d69603549603641000e0800802605c1810810824141115000382d040410107840e141c030180300040103070700081055111440007c021354690303800d124440c0c002110103400d601c6580b0401c00d03003601c140c0b1881c85d40c0c5000c1000c095049580e0014008006c050700a00d01d034840bc5904000c110300c00281c02c07031500085400b5510141d0b0200ca00d94001c14003e02d0f00511220310300c58802243c1d0982364040d0310103030040c451502d0305642c404450140b8a06204c003510301d840044e00c03502081000c940c1c54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 471510377 1250 471509127 471509183
    0x14040b0606070602121608010602070501080601050d0e070807090c0e30030a02010603060605010c1203050702030d021902060c0f030c09060c03071208131e02030312010909020108010b07 81
    0x510001030420350440145e5541030011500b600d01104c00c0c11010104540162200b801070440340f00a20441e030400000a0800101a041c6414040e01040b05056a62581c202400e8030094108a418041e80c1d51041035886800f8400c40d10072900e031482d10580a4130440c03107040640c10280203011000c2a50398041c440060030004140620f02110380c148403402c0500084c0541c078035030b0b40007103003850460604208480d41075200906008603000c4003c00030f03044d046008000380c618200044c1390354401d0001e07800c6110b4140c0d10a100341c800107071480304a00c40401c1450203c2e10790700315010307595101c0340070031644900c2115000040c000d0001404401034039000b403d800d038000e00320606003000b401c10249181c10040c001c8a00210040403150000e42c88901194000032120040840c10f03802d44804c840701c2c21010421060303440001d20a420b5460410403611a01ea8602184a4541e03403466481d005045050b0700f20300080e0070030000520141d6440c2501c07451500601c401c280288445c142204220701 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 471511627 1250 471510377 471510383
    0x60105120307200a0e011d042102060a05060901030f0f03090b0c06240d0b0402270f0c0a050301230303040b040810020403051213031b0914040b060607 66
    0x10040034001501002500c28500c0510030a100100c2c048003c104130315020303810440c00c252500c80100250701a0072000100b180352220340c6804c2c1c0c1c0752030030024040f100b410504c045928800c401804c41c590300003180b40c42020341c00c0007003200c0d40b07450003001000c880a20014110468080c00c61000c10410207004000c94403030704128403610b03981c000000da55000042e0041c0c46070003c00c10030589961444849c905200500b040c0046d9109078800603100720040c40b0080c01c0c0304075000c00a001c5441e0000742e4644800044440c10000070343d00409203100a044940a09024000b40490601350440d03040d100b8000c0952241821a800d00c0d40c480c0740244008c400106c04441d40c0012022500c0600007071014090546280741d4860800744140c1c0b0b0810100d40398091644100010004900e001c1000078800ca081d081075503545030b40080344100703040c00f9040a00007000d1841240080401880745000b283d402e49014130000d90301800142c5515001c40b005450b07540014002007040c03801000803c900c0348 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 471512877 1250 471511627 471511633
    0x827150403030f090801060f0602010c0c020a120201032a090b030f1902070c1403012307080402060c010e06060f0409030e190305010906050708090304060905011d0907170907050306010512 82
    0xd1740300782207800d40744150706c000d0502c205039006100d41582070041e9484004581000443c06185901041d03003403000b0700c103032412032200880640071a0b10030f400c403034070b46507c1c011030308000d04c0c032076900c0540e4081c1880c020300450101c040000700b0050703000a580c820b031090f00445005a4a0a058982c00d9003d034030b01c070407020f03800c01591000900e40c0c800e6101402c2c0502e2044000c01281080c036003181c00900001c55942c41202d851418003144908181d400760441c03800d2000d0342c03128800f10f085030080710050750041d4203024179441c0c80c0b0740020f0724502c901412030f90481e400850307600344000c072840550050000b5010190440c424140a40754460311a400d44121415560ba9112035084545048040302d41d01d86a40600440c10750101410341c00600c030602443ca01854a10040c05000c2c00d403289906000480320011a11104c41c0d805620b844000f42c0054414605003900409155000c140307009900804804681810700029000b8260750019004048690802c810018207100c04651100303544 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 471514127 1250 471512877 471512879
    0x51504060615021b01030b130e1f150603290307090e060a0e010b010507120e1e0301050c0301081207020307150504060914010503010e130827150403030f09 68
    0x10075081e001902d030600660140800201505110ba03601c503008400f18105403c00c0701c18001c9030340e0112030030f00c00420381d000002c44254640082341401c1e00103044c9101c11214240200405101f600910400c051040038849142e4179098180d04031031810900054081c00c1d0000c92242511000c070805903054005c0885003150b40c1c0d4880002a103818490002c0140c2280003440a01c2500c0e02415407030b03842d028002c0c400034a02000003462030050b081d0241500c100040302201c00c07400b1300c1001c5245d100242012502080304214154054840d54050b4003a42c039060014075148220b40c1507074103a450050140030140116445a031580e080342000740d03418007928034002481c450103101c2c0b4003607614607159a0b0322076150440161000081c0c0e80506001e001400007581d240c1e9001080705d06407a0210050880f0b0345817803074070880181200b00c1c02000c2c110300050f007240b40050441c640305501050102c1c452109883e9050102910309201980007103801800b05000080c000e0f000074182a125150034100300d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 471515377 1250 471514127 471514139
    0x60302060c0309091510120905100203042f0402070201210501030506011d01060507110301090c181a0609120601060c0b1501090513090209011e05030a0515040606 71
    0x507a02403001e059282e400081c4004144c24500c008075801248510320690400760007002c221144406010102001085c030160609440a6408007100b079800c0000c85000d0110202490000d5105517400d66410a0b00f603041842c214030b408000800002001614901512207070510001e0341001c50201c2c10f000206088100d80c21682440329549a612100440e541d4954200b80d0306007203040e0403500d5484010301e80154143c1580314050304407826031604070303501c050342d05203907040c81c00000f103065040d4203043e04003080c072018034601400d9800c840d411f031205d22024044a0200c421074001d180b0008950740b04011300e407400001820761200003078040008030000c04000750402000360440000b2030403080c4d460040c0081e41c20706652103280c403607680c1c0800700f003076002810303496580c030880c0c0c803410f038803001455401c0d01500540d000f280d0180441c90156100d00c507504a8030604c80604480701c1c2490720001d40c80c94005100480c0b5a00103001c1c02240600f1001c1c5900c1800c01402981c40603211640003500d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 471516627 1250 471515377 471515389
    0x30c0f0304060506100f08060120010203040b011401031505150903120a020c01080609040b0403021002040b0304050c030604080403060203060d23060708010b0a031d0109080a080a0501060903060f060302 88
    0x20840c482e4400003010b02c2c240040000c0306101c3c10700e4200304030381c013000010850340094115801100c2428441c18420300d03004440e291a4245446203050350012040c4010481c03808c0d06241a120000040b071414a4044011400c9802035203207180c40c2d400c00c0c2003c01160501c1000c60f0500c4000050b008d02e4074040d140440d18095070580305082d520070008101110075814855010b445509191503413042c00c1520000b440c2800140c80a00070303201c40804030341018000c00002c4062040c1c800195181c55807111403105503001282c00341c5a60148240c0340d8010314002c507903a442140c0c0a0007040c180b41c29a107542009400c0280704980200c0300c108894003040140300c0000b540c02c4403007560a040e050054806c2e060040c050310710014814036100501c28181e1300c00c1036803a0441d507803400041d12600c03807012190300a00380c5802c6190754a407007802014041000c0040032200c20f9512201020740745d500e818001c40c1d40c24412040001d120b80002d1001030090741003d50642090100801d0301c0340c4070f4001842c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 471517877 1250 471516627 471516631
    0x907090218150d0b0f06041715090f0705060c1203040c0801020403110f22020c160b0426060a0e0a05100b13060806040311070806010602010f050a150902030c0f03 71
    0x701441001c90308410f1409030340919003d080302964070341d1406045001260b0907008600a10740121607007030b284894110b08020100342440000b1100c00c080c1011005503480e86c8408050060600501c0400f052500b0800200ca035400141c400406481c174035203001c007036503410203442100c0c500640d40c400240ca034024000740c009940281c55000c0000d0b1f1807001c206c02d80c9001c0001c1c50080e4808104007a110762103104181300380000084c0566902d079040c0b800c1c4c0c200300030740c3c6540072041d032440300119045030554050710a9403001a0f4101282c000922031480402c8140c2d141042507002c030b00010500d036042d8021031806200c100031105646002d036204c130300300a0642140406640e03914000082e624000100e04034881101008004046c00c001016480c3c51000f040a014001810000d40c07240204002807001010ae030000e888203941c458038000e010388410310000c1d1246d402c00b0007040d51510244176894450301940d100b44152494100c000c80690401450880101303c1441220f151003d1400218 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 471519127 1250 471517877 471517909
    0x7151e05030114030a02010f080a0237021506010f0323150409020a051c02100c02031506060702090403023c07121b05040e160605030907090218 63
    0x58032581800042807181031120000b130700c00d5000340e0400000d072341c0040c1c40028001d403d141c55140c503a104680c410103446025040c00c0030000049922070800e0300a400e0b1340740c07419003c4d082e50000d502004202ea4510034031004030001200100803400350760281117030040404090030042041442103509406c048030703c4048035541d00001007000141c0d48104038a200c0032070308580c20880104103030080b0303503a2041d030f01405010314510140408072000d08003402c12405c0d8000c002c03095100c41c40200501c40240d412049000e48620b00b8280340803c50300350180c0c807825003c0d0a03c0d05091044d000c0081c03c4d14007a0046d800c1d27004100720402403010b140c03041d07540a602509038500c20400c8089a8076026460004940c041c4c10405051081505204041c0103e81d080441c0907901001c01c01c44030880105540051b0b40301d03160800c80c0c03c0e04080466089012030600781072400702c40c0d40e60001d0300c01d44030441c1d058180d030700300c50f0f0280f18400301039010300022510410036143c040014400300c1c1240302e8241100c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 471520377 1250 471519127 471519137
    0xf0c0a0309080d1b020f1b0303390c0d060506040b0a17120309030403080d020d0504030e1f020d0c03140d0204030b0108030910050a0c0c23030f07151e 66
    0xc43c00a06422038429648061417006280302d24200c2c608907158000794182c254a00070100340705440c1d40d41001074030705500780007099029840d140f298010307082d9107010716a41030920390b86001c400f1420114810040a401810710b00d070407051a600c0030002d18009042543c026a600554409900c900403580c0103092044061a140041862010300d04400241d0040030301100300108011f408000c000d5508480e40b02020a4a070a048200c4001900800c80556203e51408042000341b540c000b0034034034500700659a60100251480540ca00503461940184c0035078020008141014440ca2030781282900034a8202c0300c3c20b0380c81241d80074907805101d1000c04d0540104bc24000c0c00308139a01a0300500c0d0603002145400b005001040c080d00804007500d080c000082595010b640c0102c040f5020380c1e45c003549540312030380c659a02c0c0b411902800400e489905d070810030300c040c500300061031220440e4044010503003a4589403075a4100421306a111040103104660485c000419412540c240006a210 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 471521627 1250 471520377 471520391
    0x15130b180f01090f0f030c0515070e030607141c091103070617040f030908031603030506060909060d03030b060a0801030b150d03031505130b0306010e0f0c0a0309080d 73
    0x160310318114901119145592410210b880040c6004421343c2180380d215180e901d00e40c0090500355103003611440007404900450403880036500c0c06038003180c800d0b144d83d01c4100d100245e950070f0555844080b00c0020120720840703801c4820246141c0540880019044e00c8070050462606882c2502c10a030000c40e00c00c01451034031202031a0500100002d800549800d0b40e1040c80129040da50601c0580060450b41c1d00f1820042030511a5910300b01600c0d0039001c0380e680e01d02c4201e01311401007400704150f00003403400c0d002c905d40340740c030904a80080000801001698641c0c00801010800da40d600710103165903a41c0c01c0040b0344035040905184080340c5c841d521258503500340080310141c002d004100c160448204464165512200c86110710740500d070005030300c4444440c04020980c6500481e520102c406c0c20034038050640d401c44c1d8000e03030040e0151800d5036030750014a5052442910340d500300d441008001505d07841040007420086d406450040340d00c080d030f03850b607607141d0b40012400042c441d02c40038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 471522877 1250 471521627 471521671
    0x606030605061212030c1204030203030f09030c03041703040e130506092d0f061f0509010302010903020108190920100f030c09051e130207020315130b 66
    0x709050340500165a01603032042c030b5201c81611000039020068911070040003040d0303520703000f000b03403241403184403400c4219007071a050203941c03a08102c4503c824803030000700040c0003e401005841c2c201164400450901d800c02410f90301e02c481000781c15000744028040000c040d40c80340038a40c0600e0341250040301c118150300704107041a100900c11a583c1e0302c003d0300d580f00099031070707080304442030a51000c0c2540300008494504082c0400d01c205c2d440d00c2038100780010310340c1c0584a1040c59005032906140d1507075910900a502802344006070101e0000107003000075501580c074642c1c0c4031244000007036080384106250411103220307100584050100c50860a0040c0000c0341003900d0180490324012180342c41d101c01060802100108010540c5441c1c003a040c1d940682600c0024000040441155220300c03409444250364803003144c0c4c4070700000c00000c54000080e10856504503006405044104540003413100d441c14042c160050b9503410103a88801300d5500352180d406260354141e58004181c001d4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 471524127 1250 471522877 471522881
    0x1110051303020f0c060a0309020303070c03120f140d020c070b03040302010c08070518040c0201140406020a080c0c2109030f0a020108280902030a120306051311090d0c05060706060306 80
    0x40c1032903001c3d510031001244c10b40c0e079a806640c96100d042c03601091984580c40464110b00891030700510b58213000601101b0030174403080c40d02a0a51076a0344080741c00c400070303086800300144040c040d0a15001c204614107414960010801001c0e1001224040f5a4605114615500c22501500140d64030b000e440c00080c2d20811660304210b0516100e030405804290b5a46900f550000ca103110f181e0301c40d5600c035124001c3d04070050020342c4940c04c6030030389004d0a0101c041e602103a03100300000d4ac2c400000309001c3e0b144068540d0341361144004c0040b4401c1400d11841c00c9900540020790300d00c1440340c2c152a5504000d40010704448102808e10b1004500c0050201500581045114500c4ea100511000103142c0b04000290050b103000c20100c8242c008079040ca03071040c9002c1d00c000307271903040a408550140c103c001103c1d41070307840340d180ca15410391081c1111039420548420590802402c0c40b02c0c940003420348510f5000b40000b100450342d0300c0c000760055000d500c0864485445181c2003003803141c94 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 471525377 1250 471524127 471524143
    0x60f0a030f0b04031e1e030501060206070e040608150a0f140a180f0f060b0a152a0b01060f031a01031505040501090c0801090207020108010308220e040b13030e01111005130302 77
    0x1074201881230394100b45001c0d440740f03001006003040102c0b02200360b00566031604840001e1811805460b8404034410f1528040101100c42c0842d0a043c1031405131a441e01d80f0500142c030b19802c06100d080d031103002021015104414900501400c00350b6440040b82d2121041d00d03a940c406c0d480b40140d00c00c603280c0281600c00be096050f21070407881f80204511b00c00c4488650f50f0f800c1c10f02d450b0701000c5540805019200642c0003005058144060390b004100390005d040b1f050320425120801c61148040e0105c09594400745050380c81201e01c8007400081d4001c0d0032400c615203c00c015201d030307c0d403180b0104003107901c268001940d007038036070725902101500140030070b0161006030f00c1980360860301c5d00042c200b8041071000812080c00060503401d400d189a1440d803080e1016406000c44641e00c1384d58142c0418103442c161401d070b030361101140e80000554075103203050b64181c80d2484905203140056842c0600c0e080004002d016800c00070780e20703454501c0782da44500c0420383c018524240d2414000d1610806c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 471526627 1250 471525377 471525437
    0x1e02030c090103080f0a05040902070311060c03070504030803130203060a0f0b01080417090d0602040303022a0a0b0306120f0f07060c030504300506060f0a030f0b04031e 74
    0x714000510210b0f1901c402c640141c0302081995035185440c0e0002c8500c0e200b00d52252600501c00303d003038010103621040090211141c070301100c000b0345500c032a081091005035070207004503c08201c2000054034010146a100c0e4041c2841c14402d8100c0d000b00b0305103002111039404807660b80d0803085072410703e4841e00f040d4540038a89064903103400c3d0b03110182c0e40d0841064084440c8040b601200556400005505055104200b9034640742d50f07103000f960352901001c0c6031a00c03c0040003142c0b14180e0813004006480c0b0010480308030303540b40000c4c0131a1580b026150079000b00c1030301d03454441d20b1010860503041d440c490004041c502c005002c118244002d42d04160300300710307454510780c0100340c0c018203540036202100c200c1001205005910305d01000c80d501251417100d01e110880087c0000826924845c02003903402c154015111010000314201e1408010200c16080014501013000403007079951203840380c240220080c00903084400401c4402d03080c04006a03a003a114038110400c00684428000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 471527877 1250 471526627 471526639
    0x31d030d271d1302030a0c080106060c0f02010c0312110910080c07060c02070e0405010f050a020f0708130f0b0703020d02011a0f0102100c11070b040303020a0f0501091e02030c 77
    0x104040d12604040d08144580c080c4000c0c081c00b00704031900e803c0011071002d500400300c1d400d118551401d40e64101c00340c440c3c2d41c240d5180990000b1b4241c012529401090380c82000d01c0c0c240569a801500e050700c0b0700c0300075020400d0b15400c943e048000d0303106580c1400e00e030000c4a62903001800401415107030206070407040200b00b80502042041900036604000e030b0124000c1528882c030030049140074a5940018035114421040c0020b0010643c0b120300f9030b0400c030005010b159075420b050741c00c0e0301c15000161041e01d42006001d004c503100c40060120034589100c3e040d10b072543c45050f201d900000c0e4000341c000b40c80000702442015010800c02003044a02d00091200c00c01285289403044c5070303ca0054007940d0100182d4406a03c280106000c503811040d0400090210420040c5207070020000300c641d500c910000031411150150503201103e40c143d00600c008d90055460343d4640458901c12100e564880c108400010199480c407049440c01102c048001d010074010140380007500c070206c9002d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 471529127 1250 471527877 471527879
    0x6030a09290408030c07020303030a0204050405090c09011e0512030c0709140a020706020c01050106081006050301080706030e0f013908070302160c03050607030e070e04031d030d27 79
    0x10709014081e50b010b6001042c41e42c03a42d54000004020340f207031140096040c0400003c00004508a902410a8a20503201049940e482c504000d03034485e4004426640607a62900411001801810f8107401100d80c0304030545082c0d03070f14007103421a0900203010301035804c00726400c11466001c014240c01442041c00902803400d08100144807a20050b120030205a0000340031014803500e0f404640301c803070200000f00304569407054010000d080603944121305280340c0000148052140c0160390682c3ca02e000601603452070131500390001c0032004401e203400d00400f6584500e0703079070a00c10144040b90107170038103d03002c2c40d0344005174868440b6580d182004054a0390101895030017581c00d80c1c02020380c100103030f0310f580662409001403404240100030444000c80802000004a85603004107542c3d201444401c001d450610b0b11100103009000741d400c18080010080f81c4103401d9188180132070031240305808031040100303003004006007054001c2900d500c1903055030000e404040d100c855942010807011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 471530377 1250 471529127 471529193
    0x120c0139050414090a140a05010807300f0804090606021e06043210051005010c08130905070c020f0616020405060333010f061e0e06030a09 61
    0x41e800d44009402138040d04000348821400d507000c1e00c8504141c01503600c9a140c01c09079200a01400d01038185075000783d07840000c0350104202180845801c4c00420100c1005807504507800d081680425a001c0d4006818100410601402400546410400428030600b4104040e2404500b4084110100b002880000c000305000c40d0701c5800c42c0e80407000d130b00c00750304d00e192070003008881b480c0b50540c910b02d50461030b000200001c0c4d05054881046000d10041d40c401c4045e4401d0305107440365502040c1d64400c40000150100000c1c02083d02190003004542c1d02c2d003c1102c1100d408480070004180090041ea0a600d81851550b42040301200d44501d82140303800480000c1c40d0035a8001d0180f41c030345000ca80665018004800c43e5810010700039a0107110500c0502c62448000400804410180011460030030b0404410143d03801a03ea03d4814842001000134034540c04035a80100301d90003807206d4850361540b0007075008464001c008541000369091004182940000705c01410200c00128030903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 471531627 1250 471530377 471530399
    0xe0108030f0403120c050706120b0a03020303071e0b070905120106030c0501031107050d020109140606090408090d0b040302060a0f0e070b071401150905010e0405120c01390504 77
    0xe40b130740000c07104c14012444400ba00c0c401038890006080d40500000403c000e58002040850300008800a020102804040c800c1c0e100b140d010107501074004006107004107040180059000c041040c3d04042d68040d91540c094100303007030b07984c20300098183c402045140f8042c8240c403039500c2c403040204480e6181d90f40304101400c40d445410305140c0c88490305c1d44800303105400d90320007580280680b881486d807400c00a000307009c0c032074040342c1c00c4031800e00001c103030000040d03039500c070758000360416440d5160b980710700303401c2c0d089182015407000030000340c10000350300c0144050156110303070010905800c2266504054561640c1c01d6801c541c50038103c0c0d070b00740000060315421104080c25460756079090b4103000e103443c41d40d035038040800c1d801c1c600c6480031131315140402e00860b400e40d6010841d41c0d80b21240355000c0700d015174010300076a200c448000150200107005000f0241e03103000002d10201522401e491048440300c000d07000301d0b0590800031310300d810b1074040107060416241282c82c142c1450340c007440b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 471532877 1250 471531627 471531629
    0x60816020c041505030307080c240402060315060a0801180207050c060a230720090f0612070603090203010b1906033b0c0105040506090f0411070503040e0108030f04 72
    0x80300c0d035210030b03110070b85094004600f0080d0001a040e03d41d95001d03030030104074690080d8001d00b00f40c80ba8030b102c40b00001242c1c401c42500360288000071f81c0c036120354080200e04d03000a440146503e07039850b281c14103030fa92100100098070840d29211030540c540000c019400c2c010b4184981600d0041001170002a40460007500388003040715242e4561010b040c1c115940e440a02c000c07282407802408007580c81070040050102203109402140305ea101d10f6041e01c0000d40c4241d21260414000004100d03102401c1e146180d2000c005040c051030350070032800c80c614141d025031110003c00d035210b155009600b0207008028045809a4130104141c00c25046841c3d800101d1040c001011380d50080c1c002d40c20503103560b07090308041c501e00d00c1c0d844800c00e03034000442d6036544595050740d20451103500c0c503d5010f68241d030101c441c020289820030240c001846034030b2410ae910300758820342d104141042404100003615805014100460b2214100318500c450800181c004071a50762040c080030051031030000c2124 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 471534127 1250 471532877 471532879
    0xd0605072d0311130609032f09150310060612050103020105040501080403021006060504080d0f121a0312031608010e06130b1305090c0d0c17030d09050304060816020c 73
    0xc1d648403c007504182c40c0202031880e800810072020018000d50b01c0102007003582d01483d40c02100c080846007040c401c0b440d280c480c81c1101c203851f049401c24134016822560204107628803800c40710041001034180441c08060070082c0356030300018403d5640c00040300324544c0080104100b15411500060300a0142d031140d107041110f404002400c1520903c51107100d25204402031059546a040c0502039400c03500503004070744141100194254810314800e17506540700e4580a04514041400304080c048045a880510903001d11a04003906c08000300745413802030101a5880341420581c2108d410082c1507114104408800148045040c84001d10b80061b000c95410030314040f20030074603020b09020900c0c280d102c070120101102111080c3c1205100b5601d890545a0a10b200340402c02541422000a030400c404d00c0814043e07000c0f455071001101e01a00203c0b4244100e81100780151084501d00b1036040d040410100700303846e001410550400040c81c5044105031008000a507601d100c88400e03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 471535377 1250 471534127 471534131
    0x60f0e1210230412030b01051602010e03010e12070c0f080303070c0f0b130201080105031908070501061e090b0406180c0e060c060609070e01050f13050d0605072d03 72
    0x25030882051610214030321140d20048142500c0c041c200107210245902c0004003083c18102c041074198404e400701c1c4c01701c600318449d10100c03000366001120003145400768990503650760946403005032800c200030b01c2c0391200c507060295910318030300e441d41c40c07140540d0017407003c0074034490244102540402aa540a201440c0545500315a0f0410401a400b946009403000614030244155954072802204500f4001c0e21400c0c496680c070020301d66074a008000600e4012122580b210001e01042d0041100d10702503030002c14101e440d0f4a000d1180c0c800074614061084142d9001c1024860b20302034200368180840707003000780610b880e031051640c94121003003030b1b503803695160190000c40c090b14218401c40070103441d0f641c440104a010303d40c1c684042d10b0051080000c0d0001440c26445031514455003541a56114148940c0486100445c0c100344010382c8240e0b01010003151549602540d4411240103080104603810040320282c144540010701030300c15203443e0003054515411130511442500700e0300c4c1c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 471536627 1250 471535377 471535391
    0x8030a05070c0602070501050609011a0a0309050114190f290d05120d20070b090f0d030c08150307140607080f0415020102031528060f0e1210 62
    0x100d525a0b00100024485880410a2414002c0552240c0e00c5003506468480c49641c0320a6140051190441561303d450020000741c440c3c24800c4c0c002040240c8603400205d42c01c400100c112106140850b1004012041c503900241c420050b4003c102400c150313a0003c003c00b04a86180c2c42808001400841e91405480580340c525160b4855110000c1e030080c094a043d512011050703040d60740308140000c4074900b0811800100b82c48106810107095100b00342c13a1504d04565141212040002c2c110394050240b018814034405081c4032040721200d40c1d560010f001e0000100c041c00400d0007810000100c481400c0000c05a05c0009140c0c0540b0700322914089410640c0c0005030035480ba40b50002e06504007c90002c01200010000d0419240c1d01c07618096807000142d0124202e010440e011a9608405101140141809100c16400c1c0b5550380001c0304158101007413204100855000200142c00c54901c254000d82c00604c600c0400c500712040c0441b05590041c5a0360b4011038010f00c94031b55a5480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 471537877 1250 471536627 471536641
    0x503100b1c0c09050f060301260f0102041806060c0515091009152409050c040b070308010602060c0403030c0b09072102130b060a110c040212090c010c08030a05 70
    0x41c91016036405044107220000e416200200550351900c15140284010302d20340d912460a4000c1e070341651140584d8280c0841c400703008003170418801c10510218000c0b2445d1410b0410207000800103044c00c00c011000f100a410504c40c21598168030010412480001d08000904003090b4400400c05d0103540d890780c0d440e501180c50520f0b0030314040d0070845151214083c200005081d4079000001d03c940c08000c4010380344003031550700300308a80700c00d040b0b6200c10f011300079001180c2c003681d00715446400d1541066146c524402941c0d01a08043d0041340b5007800410481d68100002684041c0d0901c4050900785156400381c030302408080300400c01c003050320014030344000802110340100b400d80c220300001c082c00756600c0645055801d0682c01051440c028010008090060000080028005600d801141403085808250800700e9080710300a0185000c0d89641d11f0014007501d805000c41ea000a040c0b0b03044043c80d200c47c0c1e080c1c26041c03050061044000c203e0280c10750380d004940800204690351294 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 471539127 1250 471537877 471537907
    0x120309050a0b090d031e09080f0601080a121404091d0d4409150103030c03084203060f070c0f05070f090c0e130b0409021309050d0503100b 61
    0x540b000081b40d07103c4507011000b940a00385030103d61360981940c45c06904071880035100e06003402620b55580c8148000d07800a00014100312001e80c00f481c0c01d991800358601003030341e0741c1e00550061148a84851600401c1480700381802d64144550009120b400703840d64003c1c21801c205c0720f0050074918140c1c6242031079400340b80c43c1d42c99020703080303100e034110101c040c1c4445d6499001c0d510031495210b08800d1107035852108010381d051b00d80545503010007501c0c903501164030b25402440841d8408848000295114140161032039100c10010b000141007000748080746a41d4070100780701d10a62000c014410000048000140c10020b03900d0904000352190078103201d05810507500500510442c2c50000f8401900142101030743c0018400b400f9038100420304a91041010201c194809a407458605502c0d450360b000d0300603400c02400c00310388a00540c0028100401058810590b00e440d440722108204c424400301403819100e040250842c109400c2d03012414071a0b0195100d0b0000000d18452040112 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 471540377 1250 471539127 471539147
    0x4060504020c01020c16080606060d1e020c0c1c080a0207080607030203010e0705191107080f0c090708010b03060d061118102102031b04120309050a0b090d03 69
    0x6441956a001d4007076040f03000303500146503103c4034018035005414116802110508454210000b04120f484003001c001103540191103000f00c0320b070340309444441d104980c540440c170b6080007a401610340c542c594501d42400803085c080c501c03a104000070300800840024000c0321258010001e02e8803880840f0080e0302d440031307030740040c01d8601c540810000001d41c1500258141d440c00b810b1040300e51100b04003501c8034000c4c080c00d481404800c2d808003002030b1003081c810380d030001080b08480b0704641c2c3d40c1c1040c0c14201454003600c481d0700401640d441504269450381c0d004102480d21900c907624069200240e8000a44881d1241c0310400c0000188442900040d034400001050150f540b810440d0030392049210a001034000e4003a1207a0a04240c0185900308803648013003911400c2d5603000350510300940c0700034291558170718500c004a4030280701d800640003915080c40384908518103400c015102820560009115150b02c04050181c09a070344c2c10f0780d00c002c4066034002c0c07503500145001c6e0340d05500 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 471541627 1250 471540377 471540379
    0x50106030c030b09010b0d0302100905161d010b0301050109060806270f070f0f0c080706020714010f0902010903030c020111030c0c15071236060f0305091209040605 72
    0x80c091011050210b83d039030080c000c8580000802440700194180301d1242d66200019001d80c200110305210350590b900902d0070315100e082580c0e104801031420656004454001e0007000203401030340c0e1841c5e03840864003805402030841550441d8941400280182442e0050504000b1204003140c216226500c1610b2105840218130340128802d44040201c00801c8400008150303201000c036205500842110440207280e0b0341e8200e061030002400d60300c034502405c00312424003080021201080603032000d132032400c0c0720301c0e0001890b00301401518250740024000400003494503411400503a04100075070b0489500d030405940911180c00142c901c944c1c401e251119070f000001e6154580072010844000d000710840c1e00165002003044074080c28041e860005002c480c1d0080c9078400341c1c0c00b40074801484035000c0c130f01c070b0b0442c42c0070034004142da00d46a028580100e4090024404190440c80030b410707200c030603c0d0030480780c541b9404d1540e85201c1e142034000b180300c0005842e130709622030340c00603805008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 471542877 1250 471541627 471541643
    0x6060d110304082101030c1205030408030a0519020705010c0605091e0c0114090f01030e0f1504030806011106060f0604030501180309081506010815120c010818030d0905010603 77
    0x25150404101507032120007180b01014600007811000c03907040d10105c0c140e036044107001b00424204000009250040c1001380d8042c0300900000821742400c0000346030a408039500c441d120048110400d10014001d082841550001c0c1c2d014040f0ba41c0c840f1070101c81035081140818142c40d0344101d0340c21300d981018514200d5201300c1054081e1100003070068807680080c1c0e5202e003443c80300b40701c410040c0030309400345503c4800b081100071558400d40091280f090744106686113007018081851400c0d074551b011807810010007042105058200d41070310341c40740d030a007411840050120750b0340352075010041410f8440e90000551103800d4482c10266009107910100800003800b1500c911400404940d0048000441c0038501044031200420000748056003038807180c90030345520005555455004151030b109002a010200c45a502c00d140c1441210f9000c0240c0031151030000010030310f0320010062310458946481400748400004111804401500c0000540441d113182442c0584031541c000b0b40120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 471544127 1250 471542877 471542881
    0x5060d1509031209080d0b18010e151215092d060117030a030f09022e030e0c06030414030301150f03110f160212010b0a1a0306060d1103 60
    0x800e403a805151560700a4940031280a8041100b000343c50000300014285141407000c10808141c80d04090b0000b040200302c441e0f441071144800c45000d0099103e044000d2112090203a91040e42003000d0080c07600707032614150340140f4130009a03103a40001c1c120881c50003c0d4005600e48006110040040151b034400591100d08001002c850943c01006820307076000f14400014480c9a0900100704440c1c580051810000658030507402031401d501080075080e11500000016075034249010326a0005244449000401d28a504040c6003001410003d141c030b03140002a0070000092100c20355a001c55a4075500e6403640b400b00008007007904281000c0c8000300000c148940386203d000e1400c0c01c20f90300e560a840c0182402c0701030b960452000c1034824003c0022030004a80d81d4002c040040d02c40c0c2162011204960100c0ca110b51903007405201a596010100c80e02e150030107860005051000f6040345c100412443e82d0000e20018040764861500001d8005114820b504401090b4101203501c688034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 471545377 1250 471544127 471544163
    0x3020906010e12101b0c120e0607030c03020c0d08040b09030a0605070306030b0903131a090306010602161d281e0501091509020a020c03070b0d060b04060e0405060d 72
    0x20300300d40c401d000107083c01e060850403024282d500c2e5103807205459032006d884000c00c1d2180c2200b00030101c0762400708524803606520350303100e410080c1401c40c826610312603c8842801c000707041019402d4081d00c02c4003036142410208903030f6010355007510300d4503030708565482c01d6100007403a103083c0d02c1004150364140400c0004a51f00b5611500440b40201400d000c0c660301d9803081c0340c60b84606499141d0b0040951001c0c80400728000c001d29803400c103000407034a0203458100080c0703862001d9002100590081c0141c5844c4006503c0100052480075031744a1200c6c0c9950f401c1943e100c00030542d8000c0300203040641075039888500c1407484090b5022042010325070440c8030320820810980b0b019681410311000207101c00c8070303104d84403a486580c050146807504001c01040654040b81035401184038a00c1c112140d070b6018003602d0300500d400e0011035982d20101110005548660b4405025004180004c009032038100340c07043c000c0e090440d00040c9a45e40d4200003507400056940242c07040304200620048 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 471546627 1250 471545377 471545383
    0xe01120b06120a11130504061a060c0303010915031403041409090607080622020403020a0801060e040f0f06020a030c0210051017010f1b030c0e0a03020906010e12 71
    0x64022038a403122540d8110600045640c088040c0d2056840600720401140742e04c03202480c403120080140d0510b49946145c0c0b015640140c03400c0e128595507031009207640d02d44502144046000351042410300100080c21516400148074219086844214294800c4e08000c100c0e009598000c4400e4001c10002c0e406036500d800c00d019801401c80d030000e41540030b107085458144503403000000ac0100e580d51250880b458500600811b410041201006540c890551a010309502d4410700c0161a6413450042241440b01030b44551200d9141a50900c0345205079410140e00980146400c1e01e40483e41c81d003544031201d1810003409070751010488004d0551b05801584111070940e089841c00c0d0806070100003107c0050301c1d400ca50302c0000f0b03410084680c000181600550aa100014611348401c8150303003079079403c80480c2004d45444040090302501445400708031100342c649083c442120002242c08240380b404003030b00c0ba040f101c0c00528640c0c803d0810041d03180018145810907242d6000288d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 471547877 1250 471546627 471546659
    0x906101824082208070f02090106020d17010308031308070b0c07060f06080331030b040201020708010608030d0207060e0d03051603051510090f0608071b0507031104060e01 75
    0x10019412a012650003440241d110400e0078480100c0c140c0340c1c0241d544e40c0d0813a40701c9841150b140b02c01c0031050000d41c2d00c07110554003c4c41f00d60042d140c40d250301c510041c0b400000342a09503440280f400140f0109003240d0075281e00c40d004d0540c07660401602c0c20032070702d01e0045e24030085c000040a401c00030400020405440003520550f418010f101010214070256a10350084c014503900501012491528030400c038600c1c01e54402402125107840c5602080c42c108942080d40c540790010280011564100070b0300004085d050020841c06040c500541c0d03c910031310008003a503076008101002488600d1740a580d02c4100c9604440c0c0c0c202e101d10010300501390444188030500100c2d8142030b2098001c0c024640703c1d44c41c001c0001e201c605100308010744405948442c01c1080716030304010480c10314803048080502840d0302c803c2110324000d80b0051551603c1308484a400300f4030a60302001400004054040c3c81d0b00154000244541034080340090145900c04030304000b00c07800019400c1c1e03103448816 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 471549127 1250 471547877 471547949
    0x309030f060f0f140f1b040803090f31020f160302100902151602030a080d0615020a02150d150302040c170a0b0103090b150301060509061018 62
    0x1220046505661908840080114241300009000012500c07003850200d40d0344461035003440c0c0c2c44088035142c0009644c2080d080b599680c1d1000840140900e0645e404548005080f0380c0e001e8808210b00001c0860001c1403c6540d84030012000d0083c80252a0190303214001c150030643d4640903818052807045000000560142c002c640445000d025a40121018150003030811008206078040c0e44181ea48041e200201d04a1030040036001680c050284030006800351240c00c0c0c03103002c44800e000c22601d142d88180c9808120150503d040e54000c203100502c1c43d012600e2010000c0c2c501100d0205202e440c40140890303140c000311840c04821104440103481c0261010010076aa4040c01d0b55100c91609120b031401d0581c2000941c584010380094400d1141807501251883c030311760b21048410000d8503542088040440500c409040c24070605009060856074900e2504008000c071340c113590010990400c02c80324030002c48070011902c0d0030380c0c018910800c20144504103e400340f00c0c240f00b21140c0c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 471550377 1250 471549127 471549131
    0x11010f02030a0e0913020a03030c0311160302040c09080715110303070206180c03030f091804080d02160f050a0c06020f0c060703030b13150617040f0309030f060f 71
    0x441621403000064a00001c4075494122005140f04200b00c1110401070080f0100b1641050020041c0c4842808000840c030985440d51540318174078024048140c003202c601d4035a8031002040d0340080b40b501305801100c0d01a02e00003000c480091003101d841115401c090b00c1d52084200c00640360841d82d08114400aa030381d11815429074012890351244801d403101801a0700000102e031002003210203182c81c80001c51300312500e80b00c0e104046800d64200c55004018035002183c14489828500804402010703009150130892a20381e0750440280140d0340380d2000584d020031104078560120344c40c0d84180341c0010040101d0030281c80c280d9618090814202c13141d408050001500900005110480303072041c002900c1809010000c3c000a0b4100704401d4007003545400c022246621056032014500d86000400b0900e810b0700240c22000c600e00b607000800704000c1580a0b2703040c80391500b4680e00194000c0006484105034201102c7d000f049410290003001e40207110740070400b095025a00b4130b0090682 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 471551627 1250 471550377 471550397
    0x4080919090f02120f180706020102071101080405060f270a0614040f02221508011505152a010219091d0901110a02060f0a020c030706020f0d091101 65
    0xc2c18160300503601c415415584201c00f1860110210b0340e0310380d0003c40444910152154500c0341c6103000100e81c400e81c0544d60025250041c05820760b40104a00b40c2030804880074201641d8807541c4540c000d04140c610f00159000c507900030450720340c0c080d800c036160020440c038241c0900700c9130704c030703111140c0454940f03142c40b0b005030410307565000042c4100d8000074100d42e00f074a90b40a02c07034030030342c1d00b00c0030100902c40c0c0c0881c800c5c2e090b0328800d02c02603248003402d41c021b181c1400001030031200c1c80055056108420b007020000e0f0b5031511911f4128010100016031038203124040301403100c0e14030308865402d80700684244182e0301c055020f0f21090208c100843c0d001d00c2c2690040c0e684000342e000b803040081102601507041207000c001c084c0c111085200009041100300c03510205038004a40c080e0040c0c1200050080c108000e541050304031243c018118a03111011246a603039116901e4000c0c055034020420740000d1001c0010341c0c4032000c022009105400140c508080400e03c1c8007001070119400c614 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 471552877 1250 471551627 471551651
    0x5070818073b220204060504091202060109050c04090f0605030601031a072f150a0c020606060a050a08070e0901030b041202060c04052202070602120c0a090504050408091909 76
    0x18045002d8000c01910140070750fa0001c6003601400041800c0c3c1c0c0080e22903c0c0020142c9481c813902d04460300070703524840c003980a282c000341401410b80c002c900c02d0342040f00b4008041c00c414100e600726041c42c0e00000781c103109001c0c03520180c41540c1c8103c0c1c0c14054100000b042c09411540c8200150740411142210f0b6180c01044d556910a4026080d4040da1a203244001c1c860404180d040100c51301c0881e459007001185c1d520410303034220f40e80d8a41c0da803035841503c6078580401c43c407a0047c10441d41581440d20811005145d03000d0394200c2004c0000178404200241d01800790b203000c900d00a85101e03160b40e102c1c108507560080655044403e0160100d60811040c4003052507402015010360546c902440c24003001401400c040600441000c5000a52002e088071301c0200300003442030201607116200c0e0065000d81d80401003001840c04000c002d00510940d004440c0829501c2c2201d0002c1e80d40c4943c01e0580280c0220150705820885078511103207803107807140c120300849180640600c07000205030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 471554127 1250 471552877 471552989
    0xb2109010603121b020108130c15200d0c15050705091008040201120c17040c090b03030427060302100e0406090e0c060a02010b0904060c0e040507081807 67
    0x10044c0250f15035400543c000541c81021a160004841c0381071503144282612074003451150b517032045030410100041d100130a50000c03800102c2013001141240750344074088103603488405c06100c180c108032081c52500c0801c01c03130300020741c000364107203108203c14a051072024100d988503804442c45071804107580c0701054403409411344100d50682d40e01e00c80310301404084001d0011f040b41071060008000300c1003420210043c00302d1040c0d0140c101c05c50220310b400300017812240c2c2c0030116802908200400e01124507020564010202042c0d0341c007070000c4a680810000707000c41d0b04000d41c00903800800c1d002441d407140f00014038030002c450802c00d01d80c2c2c4401180c215890306201001642000350340010303d28188000e4004560300340000b1400d041c2c0391002900c0c10004079404c890680c4d0707c1a405800c142d020001c21030b001c105680800c52802d05d003401a16500c0c0c000c00389000c0c000d9180988090300c40c24864003000b171001440303501c48a0300d0050288030f0604074440c1e06c9481644940103405100c808 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 471555377 1250 471554127 471554147
    0x302090c0432180a061202150706090c090903020d0207120204020c0a020a1d09011a091b042d0b07030f09080d080105010e010c0203070b210901060312 66
    0x1101840d480090503546064000341c40d64509100c264102c0314080750b260343c415041000f00240d2926101e01e8244000300031108079400a030010740007540c1080050300c0c0d07200c2034000044500b5065841d040345c0c2c40c02101a116646008202e01c106e40740000d02c400b5240c0015210fa8841d8003a91029983d120302265210360621031340f010300c04a44a90405800d00c0c1d801801c82e8030348001078810410247d0081120445140d11513240a088100e074000e5100c0d002d404190403e0031a4024080a0303081908009044140d0030080d104850660102e6600d45921200d00ca0128900b506c0584650ba10701005120421070300d24402c0300c414104c200d4840c40c184000200949601584c1340f0b0805c141da48040782c100c005103001c1c40a01481520124190408102c100380006035507580c0d451560412000400e840f10881640381404806c031260760060303502042d81d00c02c1d220804035868680045401c80b4100010300d90150788010000d13014000064810b411801c00e03a401603050b100c60001090040311244e40c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 471556627 1250 471555377 471555389
    0x7050c040f0518010c0f2d0c03021b060909090a06110406091d010603110d1b0e06031b090103090209010905060a0602030309120f09060a120e0106031a06030f07060206010302090c04 79
    0xc81040902110b01a440c030130f92030500314980e40240e42001fa6020700b840307407903143c0e03030041003c0340c0900003015410402c9101c08407013004041c4c0e2905a10022815078040c00d03034024030401000d40004d0181604002d084081e43d00071a05010080c00051381003115800f5008100000c0c40400021400d20b100444406820480c115060755a0b841c00c601140280000b13031080031801420000e01c2040b145034003c20b00c1c0401c1c07106008964040c02000030b040003505020303042c0a500c09104100b087c149034000e1044084500c04d6041e40c911b140c40048008100d0341c0c5000b580225000c0c0041102c07491640f20601c0b44c5400e4840d00c60082d258002640d6034003040740d0300c0c9102c0d400000c60040115046000d0440e10703822914460501c0028000103595400c074940180010352003540c100800000c5001d100c13207000000000300469800c40d12424828000304010f60142550040070a080d91420003500013403c100c20152501d0030340b100c074029241d510a1105a00c2140554003007414084d000d001c44084540b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 471557877 1250 471556627 471556637
    0xf0c01050f090406030206070b010906170a0201110321011701020f0433050a0e060c0a0602090f060a080106180e010e10030b0903090a0801091707050c040f0518010c 72
    0x4079540ca12289540322085030398106480b01030010050b1140b40180461a220394001d507025030600303002c80d040703c070580d01444406c480c0c10060740c1a9503020601002042d02881e100304440001d071041c038558030079551401c2c100700c40140d03002240d884c41160a41030311500e01c0401c11012000451078280d010340d426160039401c040004022880620900003010b01c0f840420107141000c040c90b815150b080103d4050109100040094025a0010909046081c21540d80d4148407441c031402e5610700c40c1c1400185500d82c00204001c11b50380760001c0f00c164030001000b10365594103021300100340035020b01ca44000b00740d003102003c0981a11000d688203540e4000b000800f240c1c42c2c03840041070b02401038a880d046004504000c030108417103201c0c0601c50a151030003160768800660920440341b64541c420440742e4504001800080d081040c0f6162000d9444891034450403182040d6090582d000805580280341c0240f11116080300c1d0042d40c4100c0001c03005d00d00f588500b903806800d072540200f00c40c0010b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 471559127 1250 471557877 471557887
    0x6031a03121b061012060e060a060608090718021804020a0903050601091103040320071707080303010f0e07050c060403090e0a020703080a02031923160c03030f0906050f010302030f0c0105 82
    0x1d008400c0c4500507401406c0c0411344201d20140582070400607200d070900d10342c80782418407489800c102d40d1600303c140d01c002000901e1400002c80c1380d04010760b0719089540d400241340c4042c0c802660240d0055000180110f60307400b85a20b0161440400c2d2004581a005107000010b800c0200d101e00e850341415140042d00c0d5030380703550301143e4206d101c6512805e440c52502d14034010740d80400c0b500e0702804841a140d01c0326031049002d5403400b074880d8000e07900b0b40d10410041c0044501001007208451400c0d0200d1001e40b5150402c1e03480780295405400b0328420507040100b031581c401e1403c800c03107040e2280c6040b6516005515016441216005404110340302c0200701d0341c4203542c0c001e540c0302040b81001072410468074649000c0e6403403400300d000c1c0c844461b01d251200348916584150401401c2c0d030240c008042030030380078020341400c0c480034041c11759405055074100a5078100c01101075200c3e00400c0141f50842c3d00e001200d40c20700041e0b010b446400400e040750036000826a2080b84140c4a950401d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 471560377 1250 471559127 471559139
    0xf090a1502030703020d0905010f1a01050d0b0a051002030a08060a0b0a0c020f030d020102090910031707081201080a03090f050607060b03012a110607050406031a03121b0610 76
    0x82d51019002504150b0b0800040408aa0320311802507010b114200106814001d5003415003a00d050000341d10300028034441010300c503a000700844450079043d8601282d03070990030000544003043d43d407009401040d000c10a50034580e000c8002c008456158031101c000e904d420050010441c0e980c010180b40c02c01c1080000c40340c9020f03c1000e0005840284540300b03095540c00400e082842c5441c9080160b0740100c0c003410ba9280c007040c201d92240d4a140c84080c500d2468459641d071010380c202013000b000002413a8018400d0541c00c81d400c0f031540d0362a0201659403498455954040f85d0400e03400071b01032000200d00036401284c082c04450009000c0c1d810318200c0e40380d00005142440d85294075640c1d4911100b0303040b000080e0741619102d0110012a03800100340054a29000e080d030000f015002103080040302c1d42c0020030340b01070751513034a000210308290b01e01003414071414090b140e50512500a034008a00794a200800e100c000940c02d0f00310740c1712800e18041e501c100544424a03205043d16060080b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 471561627 1250 471560377 471560381
    0x180b1e0310080d0c020109050f0603010302120c102105010e1b07020d030503060117010803040308090d020414190b1c0c0905040b01090c170f130c0e0f090a15 69
    0x1c060400c071110301598400003286440c080030441c41c0400e112600d4003040d50303005030520001313283c1580e50030010264180001c13101e00c01400028030646408100d200c19440030011301540c018090201c4040202107030700501888919003501c40d01c0e44000078021502d6004c2d0248070b0407105031404aa10586505106400e8991020301e80d140b103010510207800582c2d20080342404090003912510340d207040110006115000b0303041091000ea5441c0010441664000121070450741c010100c1c94075140e074800050010b400050000c0c0d441030910700d480350308002003121580220f40340340309080c21000d0307011030f541a03502112180b40d0008108446a007461400005060940d10a02c0030b91f9000d80c0b2603000300202d480550302942c1c140b05038401403080c1406440707910030032051400e01e490700d0701000004101005004000020f00301501d000700e8404288d941c00e1880050780985d40040c410b450f901e43d8003044800b12080e41260f220a404101c21400205624917407a030442c00011803035100045140c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 471562877 1250 471561627 471561631
    0x3190201110c04060b0a031b02150c27030615010e06030915090c01020c04090f030311090406030b09190b0103061a0a080309100905010509041802040903180b1e03 71
    0x31540158050302c0825525841580060701080c1d201039190303150014000c4c100c0d40c0707160b5001c0f101c00500102c01005500019000c100d003a10000702640c1d070381e034123440c1d01c498004c0000c0744003101412500003913060a484060b4024802c154120760955888800800034449441c5049011a11160640a0505200e001076511841010441d4105d5010f03001403c10050201d52540303564001810304a495030341403094804240b02120140300510840c3c450740580300b80204000c080c1a0381d13060300040780341d02c0000d03a44100d8000f00300300800b65503400d001c5401c2070102d988500c54050981032000f51550701c040034000c00d40059262006070300315903950300100004540d840c00044a00d528081c19950070907a400542041c3c0b01a40d2603030100014000501c404580c100103002c0074600611280e40d021055503400d1400311030100355840908481c688512041102a4109050115101c14107030054040307100286003640c1da0b0300a0b03581c3c00d600e594a00960740348840c0d20900781d030480e03081c2000c58003071a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 471564127 1250 471562877 471562907
    0x105090f090c09030706020f060a0603030e01050d0f020301080c0a09020705060714130f0303170106120908190c170f07151d0f120c070b07050a1406060f03190201 71
    0x380f4100d00900068034100d00341d1300c0540160f0064038914000401800140d03040900d0400510055055a402070241d54070b0a2201d0304010700400c00c0710215030650409a183c181c00300c4210760360358542d03283e19210750390342c070105005172700c0c1e1400040c00f2040c0e8803c03100101e070400090180ea80310b80004891009004448941c3e01c0e90510084594101c080f040200410b065440c60b10214075503d000380111001101040081c03200000420001ea003200d94403805d0300e14560001042c1c10305142c644c0395800307030302060407c14044403002103045412901c050105406601c824440f9201c002e41c0c210703980f041c00c40b58240007409100d807100191510000c0b040080d1661070100c3c04d4101524496490300c800d8007401225480104481c504050a0001c0042012049401c502d803c08501626a640c022441980742d2100005420700900505018048401c0d9002d00c1c0680700c44c00100c240b940d1000c098880c18800c5060504441492500060b00e816002c000801e242e00c0c1c101326001900c2c100d40d085480 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 471565377 1250 471564127 471564151
    0x30e0718020f072001030c0309020d03050901050403051006080c031f05060f10020a0c0920070311030706020c0d05120f1b0d0906060f05010503043f0e0105090f09 71
    0x5500258844c6100707040101c540300d4040c0e44610315000181a10958600701090600e4400d01d00e002d0788542c1d81c1c500e100c0e601411b00f80d5492500390012101c6201e540c1c070140481c011210310041c1c02d04660800021030340383c00111070001c900c000406417200000d070717180080c0e0000c03010398120b505400d40000b0781c816001860f290b1109602d401040c0542c07681200400181c000c64451002c00c201c1050203030250200290801c40881c007501c90345180c4142100504854070b000c40d0800070984035404440c00403c40748296600e6080d45c0c40e000010790400b146140050140360907004e4201d101e41c040e25a1b20840d02070007419501c50660b9106130b014043c203503403007000c0300389580e034640c00f10743c0003e05000150400c0018228a6828003804031111a00b10590240c400320040040360f84c4007003620b402582044d0b10020600c044810002d99441301c2d0300903106401c8031003100002d0106030882044c2c1c140d2075142c85402d00941001190140b2414040540c040214000050507080420320154420841e0140c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 471566627 1250 471565377 471565387
    0x601020705313b1e121305040c030609020307090806060d1109090a0b0708010315050c0a030c0309020d05160905090303040f151b030e0718020f 63
    0x2c0790540d4100380a0140500c0d10000404907040b0b6030700a46802c494842040040c80034443c031420092020702010600300700c00c41c05094800303403001d428051601070441140c001c00601d41d0351a84011403800c1c4d207003050040704404203a0f071240008642e1880307420020990064100790400000b4450312030041e00b010350f100b802042100d11440218090f504585030f001c984d80c41c100c0c241e89411001001d081c010840040344400083d075201c82080c2100c03040300d42d064207588541d90907103170002d07042000d89070101400c14414244c0c0c02070312841c141d030700078600e1200c80d24280c40500103444060b50307a105881c2c42080002c410341e21a0b4059100e000c00351402140380d00191f000203c0c503101144040e141ca401104226100c1500c42001c4801003036501000d114034030b0a20b03e51920ba000040c00501015041b01640040041d04074000c001c054442c01d080003500384000503280b00204046a0300302003032400d088420840c90000f4000211241c81c0104105044400003074800381d0131030214840d035035070300b440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 471567877 1250 471566627 471566629
    0xa0509071e020705100e0f1507050105040f03030e010b010c140c0a080c010305100b072003030a030504060507020309061905070213020306030705180a090302120a020c0307050111150601020705 84
    0x411900e000c06a42d000f0b103001c0c2e00b0401042044640b1880220074400e8440d61035009845850070003110407030458600c001380707120203c242c4c01d5115914001342203502c1d0004100401c4240184000350b80d0003583d0030001003040403815802c9400440ca010f010030b01c03100106001405d04c2140b19403449410313085c0c60112150002059009015812003102d07070300204042442075900d8030030f0540c07041105400c0c2182c2880d06018100500c034a4001806001c9540d8204d1f4040c00502640e40c441800501103a0399412041c5008004010541c0d0440700f072401c24000c00c044c0e83c400000d03141c0e003400c000d11b114507084241074040d9809402011801c00d121013030228171301598581642c001480c125910160b0381c0e02d0007200709820300e981a0005442241085030042d0820681440c0b00c1d4499a402d00004a440b200d0074140e2030981c014080380790080000802415840c1d0214184020b0b410640c200c0e880c141d110790056659011241485100740d12119030050304405080041da00640c0600644188940703582c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 471569127 1250 471567877 471567917
    0xf070206061909150e0901050c0d0209030c060f0c07050402091023040f140301110703080a091b24171807030c080609070312050703030b0a06080718050a050907 70
    0x10686201c5100d15282000400300172a4900c4d8860840300080084c1d00d814440c0000a000e6000d1888c0f4560740803c910007162400c1100b611070003001001e0a0315115043c0c45052203600c00c0000d11a5030040b00c5c00010503041500a03140000c00003441c266480780740f034404882000f18010490010400340c0007070200c21810f20001d10150040c0501824424240401f0000000ca55106c250107607152a0040d92100921000c2d102180e9141c03500f40c0040d1150340d00f6a026042c43c1e00080d08002c1000d02c1d00103880752103035248045920400d000c80f108246105000309241c070b001140c8002c141445000103040741c074640403c0d4080700841034404008820300c00b070b83c89c104140c0c0041301d0714038590109001c0c900c4100005640131190600520b0000c1c156030340c5162580c2c840e000703030041c40340200b07000c01098040c1e0040c90320030f6000741c0000b40780da5990300e00902c400400e403072820201e14000d090701031030352020b228001a01e101070807202c015440c0800748103130848005c04100070060701161006441640b2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 471570377 1250 471569127 471569141
    0x10b0a051c05130201021b06030a050a0e0d020d020706260712021306350603100212060f011803030c060216050d021c08010e06010912050102030106080f070206061909 73
    0x481c907903c200f84018400640b80020350f500c0815800d9114481c2d004550300c04013183d03840100140b01142644801e40c0000241407002210500e9004100c43e812085500048114441e5003603800c507210982d5079142580d01d865104050521001800110400300e4045e46c3c141e5040b1680d440c02c8908244001d040c0c800b02d8004000303c02c1c0a05440748100020f0380d00c05191111000415510740d042403d42c0444000e02c40b0064130030030b42c807440300006043ca80c1c09001107800018036410543d03075034880000c0c103040c0903021650148141005d030b00c0f48020b54401c050081c0705000c030281c0c505100f400c5880543d110340c1c24810032102c940d000c01014036142c0d005540840c0e0f0714480c0d130040680d01a07030749000e07060400c031080d40303041d0061817105200707040d81c0101c0d114111000040d91017840c2d1504001251103101c550800e001d140401d200482c00c020055000314120303880c07a59074940b1603da154211401d000d050340e03d400140c0c805400709250345842d81c1c0900941040389440806c0070399401070101540c0707031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 471571627 1250 471570377 471570391
    0x160908330a0b030c060421140a0c0f0b070302210f04231c03030504050a05030c16050a0b0a0e0d06051003060b0d03080126012a08010b0a051c05 63
    0x803185610810300f4100300050340404110790b41c50810b42020010781003032551010f1400c0f8181035a42c03220602200856903500c0403040e9041e5122940e6500740f44452205e144600118815880d1000907810b4010040d109034540c160b000c1c01a800e240f0486004c400e12801150030744090410980240e58400303002407008180c07054814040091170300c814081e5050b9405c000340070b04500d1030300021304c00300210302e82a982ea1600700029645c0b104e040071442c080700c3c11740007081c501c40020b0441700148005250300800d1400814010003a4541090040e0f1040343e20600741e44440510010006500444034003240715006805000c990f11280c43d420262031050b105510a010202d000f030050020b0340c001c841c02c2d103105881d984404000c60f600146074040501c03c10020003800e01385580500d80008000c1412034421f0000d005101401120007403d5480e11501c0b00420410803084c1401c80c0141c0c2c1160403104003108490600061000031b45550703001c8601d043d001201d0a01c00019150315124090003a10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 471572877 1250 471571627 471571631
    0x80a12020d06080c09040c050409260301451e020418020903030301090b0d05030309010c20070b0a0e0405131a0408040603090c0e040b160908330a 64
    0x11404410324101301803007842c240034010f0b130000c01000c200d01904a1080f2902550002120103207418000c45a1a00701c801081c410110b0112442501c03661020b075060310118803401000005249480d40f460424200390072044020840355000d01c1045103025214112168021076240324070004144d040d2540d405140c02d442d40890140100d0070b80c0790110600c0503032140c0031407400c60503000082c3c2d0381c041440386000c80782e10b400a0280c80e856015014200036030110489032242000d41900c0c2c080c2c00190058800504903070b03906140c071040b0801c0d4090b40c64901d8064a0f641d41080840d01c4940e000c0c080075011b000070404074007180d4655100d1580700740f05c10383d5030000300301691408000d4000f4001d04401101708139000d00c00810b03002c404490480d2001d090002d1081707000d14260341c07408083da1080500c0c4e000d000400050052409900e80b141c18110011042136600c908142c8074085240910242c0d079000041217010400c1c80c180001e802c080c881040c4070042071454201c404071344200e07903840c03d00b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 471574127 1250 471572877 471572879
    0x20f060c0d03050121020f152b020f0a08060a180501140d08040e06010912110103050f1b030c04090e0318010503190f09050d17150d080a12020d06 64
    0xc0e03031500c10303c2d002d00015965003100e0454101d04002280038030340c0207031040000700c0d0250450b90701c21076144136840507240100d450344079640003880c41c054004117110b50f840706504015100c0e403542c0300f2a00a103210b40030450524003041c0c4100c41c45600200000c0e048400000f0100322400340c0403080d2100e600c00c050105183d03041c0201c00c1c41c08041a18482cac01a0003090700c200016080d5000d036400d44200c00c00c0e480895985c140120341c0c6400b50780c031114130320030500700d0202803001001a2001102081e02c052200d81c6409a010810030030071102040e07015048909241c03182d940100968110700c403141f4881c10240c465505000f1240207140c107500f1a44006001c1d00402882040400c030301d0780c2404d11070f0540c5410340c1d0f9500c4c2d50170380095402c1003554031551800210180c0d03012040f01500401203a030100d03927001003d861a072203440c3c0d42800042c0000060100d24508148041c841c1000c2c194980e00680c40c0d54000d42c03900031076449000d00002c07c0411804180074406808000243d24001c903285d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 471575377 1250 471574127 471574153
    0xe06180103140106140c120403080304020f0d080405060a1e0e01091205030d0c0203070b040c0f0e04050a0f03020709150e0114030d0509010905090f04060509060103031b020f060c 78
    0x1c64049021a030b803a6501001041250340140301c083d19024140c03101d80c0e40d0011031605a00b0070904054070000c42001003004020b03c1078034000b9612883c270a076031400122150200f04003c88407004801415103004100522181c140302025200c0300686092241c018590036844000c6401c1c03081000001a6425804030425030b8080340d840024548005c0f100d20000c0903460b102c1e240c4c4522078860070102d4880c884481080d108004950301290014601401d0307050518084918900c24420004030310542d08000c903900707a4041310ba0b801160720100034001801640c4d1030030108419004240e00394062071000261905090091f40b8402052554405410341081c80c82c684140041e00240308100b507254071448240c034002401c07000204207080890f102e42848004944080c0c858000075000312880c0248040f08401c28501c900991040c0018002c641d07900a400340c3c1c0f0743c824400900003441030420005540c0115500c0326400b8009810343e00e0059516000c40c449501198102e0034542c0409000951 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 471576627 1250 471575377 471575381
    0x301140103060f0513031d0d05160906061403040f030c0b040b1906031a04020402040f091d01020f0f0903030d05040503120708010503070320030f03210f011202010e06180103 76
    0x40710b030030600002c01419540c0c4006101f07104001d1110601d040c550342110741d99894040e50306400d980501101c210400321080c446005815124000c281d03410040f010625501611200901d600c12036080c0d402c41d40c49484da0060039134200000d8050251800c41c000115026162a0348200d0113410401100d050002e41d01c2c1c541032801040584152503c030080c4001044480d0304550b204840c4840c00e000c0c2c0362800050005d11480d80308001c03030340e840e020006148030a60000da0045111102100e60f8a16a5894601f80c0c0310344088011140d070304200c0e6000c81822714001d0100700c1c2c0003808503404d050404013000100c0d40300780c4090390168008200c0904648d40d107c446907100c191850200c41651400d0007203623680d9061302006140d03e0407030702040d038102807008c122910781800400f202c02120314042e8603902c1c0d90298880d4440d1019603584250588912440103003c0c1c06900c03100708042c1c2c6000e0400268880c81e10049040021150b00300d0030316035440d03000d401120384001061a020400100141c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 471577877 1250 471576627 471576631
    0x6040f061202090a060e1210151d060105070503070602040308071103010b15091c110108161b020d020a0f050301150510030203270601030c210206090301140103060f05 73
    0x1c403450042003204025210a2140300c100c0b005410b000e6802c0c242c0700c00041c03031150000c044200c280302e001032102030705010b17030801143d001c99048115502d9031203071f022213500c88042000c0c641c40c010b00c0340407400551080000b080205c4c018402eaa09006080d0f40d00c2c0207070f80c41a80190751420b400324600c028821511070402c3e0b9402c0c118003c0142d22042004981c030171503066404130f03001341d010901c5c0d0080d0303c510703030f484012805013035140108111a14040c5044040d0100b041d0003c0c4642c0e0000d6a101888560a00010721503226405140b4030f0b081c06619a40320300608a810050302c0c08a040180c54502c8801c0180c549080b00b042c031203041000741030840e01403210041880c0100e01040003141c94483c812640c4400d07600d03016950b643c44041d440d0b8460484040c074040f2040d04040b00c030003098003040041c1130317a218040940240c3d503500c12045154104240040c051140c0031944001443c08000070b0004500c003400124a4134000541c040d40050240e005540c515100c1d034481c00050240d2044075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 471579127 1250 471577877 471577907
    0x2010f09030b010e19020711010f032a02011413020f01170a0b03010e010c0503010e0a2c010b01110d180503010e0a02090601050f12100b0c01020d060503070501020d12060506040f06 79
    0x60407c0d405480e41c4850810005540741440203211651104a1007600210303983c264102c26040045544c3d414404460500c00036000154600306800c40d0038030010941d64020b21a140710200c081e40c1907001c000d00c00442518840c1403045018500c40d40032150513216100d00900702d1f0000795199100140750969950703044021650345400c40703400703c85803c50f0682e415112014480f50455484041d0440141050303426100c04103c003589000000713488244030120101001c00a1110600550040d00c81c00541c26400510707802c040c00021003d0700c9419014a00c030703440c08050314603c4e0b583c0042401c4a02c4c0016507030482d005a0400010f5050800708540c01c08001e20706640343c0003050342c410207140a030751505155130000310040382c1c40b2600507500801815110304903d550744018000d140c001d501c02c0304901203250818900041d2441c0210729081101c1c010f0700501490107001078102c0310f03002c6a0458402d90740d03075100041070343e1300e600300503102814a008501d0442030a0400281c07003001c4400c41c0e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 471580377 1250 471579127 471579131
    0x30207082107080702040e0d0e0604050a050118170a0309080616210f0e0c010e0907050903070e09030a080109020f0d0e010f1a0123030402010f09030b010e19 69
    0x2200104950107441c2020740e1244601503192800303858054498800c8030b40c0698410b080c000d804000001c0407518038031161650f00e0745200c0400403800d10413680150300c1030030b51124000208100650140584010984507505d101c051203881c0c5c0c1041c0101c1d806030b0350f441081e030300481c030349010503402c13503800c8029140e9034004003c03a15161800209030b0042c3d4032004100141030b03403d00ca40c106642c1100113003524600c800c0c031600c1400541480100249807000007907110341200d030252540600050140c1d41c1d1b0103044000e0507900d40000359501da203d00704a40e0184141c07203000443c0e810241440380200071080285940f015196070082580c00d06801c5a01245d05c108000030300b05840c0011034142c900c0e0b0b4a004242c000c01e0250442c010000780e40e540e8040c42c1042c2c4070094040d844408500300070000d0300d40c0814080c0c01c0020014500100c02004040002040814055030054000c0382013800249420b1009a440742d850700310303a40c3d081c4c0c006241d400d190300030700503507400208018503200454641 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 471581627 1250 471580377 471580393
    0x100906091a150604050d1115030c130b090108011a04171605030f100903030b060a030905070f060c0f08070f0c030204140f070f020304150c050601090209031203070e091303020708 78
    0x2000c1c6e0f145004000e10000084c0380c14401521284004102d03204550180342c0c40b40740c81d518414841e4003500c15080410b0540708082074410708070040e18605001a507a001da0f9078201691902c40590000b0348880c0c6905c01e01c4001510901c103e22031070b800c403641018020b02c8081001a80e00050340380c1110b4400d40149034011003a0f0030004181c0102d6640b1900892104003170b042c2600100261003055030130000000b002891140c258000340182031088044a40c416a180201d11404001c0d001e00c40004800413909004203039914080141c960086804629024990b5203200000c2e64140c400c452621b8680d5080080d450300d03200c0e420ba503c9686071542e00782d24110791601318549004040c5818440c144400d820221310130001e8078007502d8100641d2002ca50b00e100007030000e101000d811103003441034800203d1419000c3c000d4589290707010f001080304c902e03408505290751300b00620440400240d01d00c14155543c40810503405080302c0140500c0700c200b5403d0090a0906640001d0150303849042 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 471582733 1106 471581627 471581629
    0x5040903080928080c030c0a0309081204031a0901090b07031a0a0f051c08040b0301060f170604200a022a0102100906091a15060405 58
    0x407503043d500c8100d03602007a4400e45160b0b010384030700e40e03c0400000d0b48101c058491880c0c01801d603400d01e106c1c100307000d00d4064100816800958549420814a44140b120106130305403110314a241c54259140d042000d00d5050100c1000d50100e0b0005030f00301d00a5116942c12a40000500f402c0d007003030350004028262405258100c0e03a20340c00d203241685000c5001508842d0543c096094581c641070400c01d041c4114042d43c0348201e441441103001903c800c005002030030491490719260350610000400c1202d400160b5400c1c03002c02e0428603900c4001d051100c0c0d10910466010030b81c01c0703e09400749040303800810400340300a004245081c0390382d0007050100552800607203000c00e500c0c0c81c909d40030075940d1004020780940c00051007031768100b84d0781e04066035040c0541c00100d00c410040da6102070740b454813022003600400034010700031110066500e20107038900454034107060608000c = true := by decide +kernel

theorem cover : BRFrame.Cov 471402877 471582733 := by
  have h0 := BRFrame.cov_init 471402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 471402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 471402877 ≤ n) (h2 : n < 471582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
