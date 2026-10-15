-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4283
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:07:02.247373+00:00
-- url     : https://prove2.me/submissions/afcc435f-9168-487b-9785-64b927b98418

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 770143884 ≤ n < 770323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 770145134 1250 770143884 770143909
    0x20f1203100b0d09080a03050f0f0730020403120f02030708030a1a09510a080102040e04020109060509030606040c030e15091e03030105150702041a0906 67
    0x10140c00710710305004180d085a0405540c103040a07584410000c08540d0302c502920000c006903401040b40c5c41d00c80440091500d02038030498240c0c43c1c44040c0201c0c1904460341c4c980b505940c1064807040c1d800c0d81001040700c0146480400c10078800500402070003680c088031981c82d40c0c0c45d00c41c0c41c0071074200c0310120381c0d903c9000800f030f0500400b44045241200d06400c07049815804554503150540d00c080080d0301c0c001b00360340c030350100c841c0160346841d0303848280160300407103940da042400c61800c4402290101e4111130104c090601d42e102001d51282c1e41c80d040c50f0302929440b0008c6455a44034906410240c000360780a03804a00708800018105105004542c0401d6014000e80700a46401382484044c054403c40e00041c55200d580d042045c2004118583c8200510380050f8114103240703426600b040c1480e420301c003a0b5070b44618400081d05001048a04483d021703102c07128107802c0200f0b04091800b07182c9000354001c1c10061a105e0f000c104140e450424841201d4041058950200b040140c59811 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 770146384 1250 770145134 770145151
    0x1b030307031b2109021305040c060219111801060207030312090201050a030e1002070506040b070f0503150a030602270102011e0b0a03080c0a12090609050d020103090602030106020f1203 81
    0x1907000c40a41085500003080726042d01e00201d604e18141d40003492013151444145440c544e1401084244180480610b0003006280060601c1c140d040140700c01d43e107401c65000d4078010b4440c0c0355241d2030b142c80031000a4004244291081d55031240002912034202d40300950002d00001c0d11849840303c54400c0c2d15840d5070584580e0300d05941c122064001d00f507009240b809500030140ca20101a00030300040280c24843e4000e0003071b03441c00d07190603500d11501418000402502c02e0748101069005030840b03030001440f041d0003050505050000d0400049904001c144500103e81d40070f5100b0441c541408440c20106a81c025a0115004a088984840d900c1c550501948005032000426038030040b65114040c6c61144c410303031640c0341d40b01e02d80d00040803001654000080f200501c00740b1101982d90301428038096100c03070b28100005003108040c0c041d5512800050010b00308581c029405110380a40c0a00195140e603540c0740041c2d261070a00880c40d0650003041d1a0720b0340500d400c02141c0c80794500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 770147634 1250 770146384 770146397
    0xb0a111e0f06060406240e09280204120b090a020402070309031a0907090b0f0a1401090603020705122808090c01081006030509120f03041110020d050d021b030307031b 73
    0xa85800c006d050340081510300c1032000c04160f166075901c54907000d600c1407012521040e030072030034005095124044a0208513606105000034011081451081c81416030000304580c0b05407a41103505040904401d0025489840002c81d60101908000f41f4411a8000d4108441021112103146441d0104540d150320a401c000c1e0280081c10b07083c4d0050142100c041c2c600a0344495080200b604503d0980088001d003070800c1c2001034560b070100c8050050402e42c50190b00381041952142c2e601d8018882c0d181d1198000318109040c2c0c00c0c0e540e43d0501526145c0300e0024012000c0741c0142240400b03840810982c0078081c030180d81540501141c1f405503001c0804099124034180c0100d0041030b000d801c0b45d4450280c5241d00c1500c5004c1c802425814103c501c2ca40c5d031303a040030b181c008200500c1c28030b440c1c040c060741541594800c0d00800e1444034a0032908180342c0d00c02c20544584000d20441149940345803034561000c003403050000c0510310490756030b00c04221050070444061a54141040c4e81d2000070306 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 770148884 1250 770147634 770147669
    0x209123702131508070b03270a03080613051602060109090201020a120905090a060501030f090305090d0c0504060303020f0d08090a0f0c18020d060504060b0a111e0f06060406 76
    0x2160b0111100d107450a0700c03c3c40464407a0029400c04403641d01c0704416074800f00c2070060030400c0d00780c523524107080c0da03808074488100004038640760219410007509003d0500700023261500ea0709a280035030007e02d0b00c10080c0c2d01d070950914015600d440403282c018130511001061000709441080300c120707016002842100d6082e603034100c41c0074002c003c1d03d003003050151001400b502e0700075401d07008496601d80410780508020005007210f4884c1c2c2015440e42c2401084400b1a81103001c98200003000d860590b41e40d000b81c14400b040030000c0c0e0156400a207842c1e800002d2641c003041000a0b641a102600d04180c43c80d00101e80005042e00c9042c9550800c1e8804000901940d66044146119030100c403101640c807001089000032181c204030784503030006440c4c8540c8041d40701c0d81000c2e0400700d50821456040c80d2208409005010212007801f00c658034100c403c0b0401c1003d1102212841c19849580c42e41d290541c5c0c580300b0004065000e0f204220100721545440d0090000381c1e08540000c980f1041c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 770150134 1250 770148884 770148919
    0x12190e1f11090d0302070e0606070201200a02031608010510031a070e0a14131407030221070f14040b090f060706061e081f0209123702 59
    0x351500a21140701040040c1c03160f224002515080c0340a0b0300a40800341c500b8034036400d80c0500802240c4149400c0203013000603a00001042201c03101c3c2e410b154660030800301224644080aa406580352164803603500001d1031107400c6000350b400c810002e00041e02c80e040301d04440c0c10b503400018992060078074010390000780f260340e095200c01c0e41d00d004440010302030b01107003103000c140c2c10402c0302d80c81e600108595820300200c0b1208540402004000008820300010781415001e0204410181c0028043d44120b043c40582c05905003590050200d40c14981006405c601c0c03082841c4003ca1501c1c1c100303490400c60a4103850488188900184c501901c0c0e80c100007036000c11140700303030f80100203205200204080e88a80e03800341c0502015003150420803d0102d2100c0c68a0303000e40000c1d0300c03130b01d40c280300d054024204c00174846550401584a00c80c0ca8005142070500604141d40c900c0740703a401010f21052041000c0616020450100060950450345c4140411461020750040855100c180c041e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 770151384 1250 770150134 770150141
    0x6080907090e0717010c090b07050a12050f1207090b070f060906020c0a0609020909010b1813083006180934060305090d0c05010212190e1f 61
    0xe40c1c0310815034a143c2e8880c1420710380590480d01350b1030300d40e65448416000a82081740e54001d0904001210300780001c56071002d56920900d18001c0c00307031b90403c148801e41c9000b04d00b80c6600300c108403005500d0700380460a402080b0810ad510a00240d100300b0009004207030241180c01060f00660107181040381a103981024141c8030100f03c07041907080062100c074410901111030b08510802c0c0c00b0070300425a004104030050003030440103007a45008541034041e0340311784002c80d800248a44950395680e80d202e04400d54440d0742ea0141a0060004100c400c541e95844038442001607500100c52040c00145c0e00c0d10741c1c00b81201c01c1504100c0d04d02005104121401d0b07000e80c440030040403a0030021000c0040085055400d00d1249000c160000207031603a80140300143c06415649402c011030b280161040b07542e048600300342818080681c0c0101d050000a4045400c03803940c9803070be82003504000f4100040f034030300c024401070654076010000c100b42c40d0101e15041d076681d10303000c06d20740c03190002d001c00c005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 770152634 1250 770151384 770151401
    0x3a023c0d022107051801050f04090207050c19120501020c070e010f081612060e03181203070305120a090f0b180c0102030307030c0509030a0305071208190209012003040f0608090709 79
    0x1403040920010888c0340860b401000a0907105a02503241c1d180380c90b00c01e1a200342e013041140b00f082c400d0040c01c850611310380b141c0104d40d81c1c404d01c0f20152203a42031460080c401c06039500e0541c0100c08010607501c00900c3e4042c101c681c03030910741c40fa0650303130380c859a01d41e0021020350250109000b01040380c4182140c0001c03006016407030010b03a103140c0e075000b1072a40d4080c81c0024906444d0681c004458a03040c80040b400d8844400958030f828003582d002406e902c14025084003050760741000c20341c81a101c0e40110146a1b209580b4500c600440c14281c0e9107000031600b5110300e410a6407000040e00d400709044000e04010707001141561034040095001d800711410200402c80103000c0c0024a940400040d44164020340b41c1503524000741c284070000b1031490242509220049050000f40703a40c4a02b1020390303201d10140181c03210841b00040b5802d00e000004680421001800030340b1000c804001842251086403040358266580c40098510520071030300c80d0300682210200f0050f00e00039070080d2a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 770153884 1250 770152634 770152637
    0x4090507051b01050709060509031203130f0609141902120a080d2003040b0601030519090311010c17040b0a023a023c0d022107051801 59
    0x411850001d030345070419200b60540016034488040c03007105c5030000303800000380440b40341451614816101007541e85242c11301c810420000040020004140c2000c1e0303132211039000c600114025401e00f003550140c401080143d809000c0c00490103a444000154001135402f1490003401b2130f01181c003005409009860b888100b0301a2860540021703207000700404a40240b03000000b04100d0040101031a06420306c80d1580e480c000b0014000800c2100000c158014000d28020401d99650110f0100c010414503041060702d040c807801783d0801d0b07000501101d9510981000f04001d42c0c0e0000d003101c04000d01c00e0300d0080c14420b231307021501103031100050950005103080094a0100c01d50650114450740038903203030f00c11241071280c0004c408030b04554000c0841d200d030107606050800000000020340d1291680c640385070008a1550ba20000300540c1c218440e40768425104c02804403210042c1d4001254140c550b1419656a0407422200e48001e0059507256034041c28003440310421482c0c04501d980e03560 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 770155134 1250 770153884 770153887
    0x30221091014090a0e0114030303040308340807030e03040b040303030504020a0e0702100c0311030c0703030b330f0f070f05030a2c010e010f09030606090c02120f0409050705 76
    0x4044d100c1c500c503907000741381901c10807207690315001122002c1541180540e00c640c104205010100303500051168028500000606800010b0348140c04c45003900000300c01c0800354074001342030b401c1c0c0092050744981e5454a042c405810603551090301d030b108502900f00048828002840800d01c6030380290780c007d05c09844070710400e403104141502800100d030305000607803000380b10310790190007802800340701d60b00c904050150045039200700d00c45000c001d00c0127443d49408520030b8245407080c1c1107409440c0014281407203824182c40404808001d40300304a1350001d42242d12210101c1b03610858280c09505d8040b40c3c2080d48001e401d001c036500809043e1070021010740c2800114000348001d104d44402622034a050010302982c00342086100301c68840040b03040701601301641d07005668440c08801c00d20b0101511040fa00064071007030041d4001401c02d5240ca0000303c1d4585c6243e0110002059070340844888107012042c1e4962803007040812409a08140001c101168141c0c02c50340e0072014500700603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 770156384 1250 770155134 770155147
    0x8010621050405070323061909230111070c06050310080105011805011d011e260f060c070204020a030f0f0c09060216181503030221091014 61
    0xa07500c05480654240e00540c504000304135542e000d00c82d0721500300c5848084014440d081c162200c0c0020011041e080412242d09580030495224000c0d999210640300442000284038800401c64000314809962a00000d00700c9801181c0a944071564403992511109040050848141e000a0300c40505040c0111010506810a01640d4084c004040041c0e80007035041061100b1b82c5c034180c1c015100031f0509005403603481603210055040d106200040e00d1900341e80701c039904645020341e000c2184200701c1500400e004040400c000c5c000958841110102c01c098941c01c0e171280310036603503412190000c0254000604054024054040d224140041c0d80900350800e401500c805002449007542c1d40c100c03032080c3d2a08014030340050481813005180c0e0002e035844550414000340152030408580341002c00e0780c0916030b0070102c034003038285021402c5150b1ba45000396668080b5000510400d40c0706002d51070511301c420a41d03031600002080e4809a654220043d100214040300d0041890300800c8007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 770157634 1250 770156384 770156447
    0xa1e0602040b2d030705090d03110f0a0b18060106031113060c0203120307120504060b060f0a0806041b030c09091112061008041b0f0902030906100501080106 69
    0x281c98000540264880498820301200307085601903d10807184400078400d0100c61a40a426580d400801f1760703100c4005000d6050a5030303001008809883c3c90f201b1b801c1c404100da90082140e40b211403084102440da43c403020341083d5000da508000342c41c01c1d48520010400c5e144650090303900c1c00503004000e1300d03240c1000180d44280d0031a03000f40c008500c5d555400011400c040004070707003a000310344c8040d00394100034400038800510340e03910320030503520b810201c0c00740280361340301092064000f080c3d10b40e00d100b2100c5c103042035080b00d0340b00340c082a074810000c0d1950405006001c070107080f5000010041c60340410036001016a91000030401ca6807410101d00840e051040c0300820000d404100c0d00c8030840003c401101000820441c001c00c40c698022a201707170003405842c0c003c0e038011011701c641003404105242d000c400ba4040a5800c05010000903105d48030342c02036000b0084082581c00690390301507003d01d5290248102c60002e42010300400c0f445d071051104d4845500040051441021000f90 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 770158884 1250 770157634 770157637
    0xe0f0c060a140a0509030c2d0a08010609090b090a02030d0f0315240516020909030f0a0513080309101d06040f06020d32070819110a1e0602040b 63
    0x1c2000c503a0009001405160070400b000e102001101e41c1000c5186008400480d2046803800d200f0144c80040c02360340c190780e503101304070103000c4c92802006005c3d61408004041d00c0080010346843c1540c00115050600100d8011070741034002c1c0c02805881c0d05020200d503128203808040741050780d83c1044c0c00d400d400540d0214010b200d04269400c101c207254040f0200602545c01c40c0040c4070003008071000d03804080c00c90004641d0104e0303110f5060341e00d1131101c07400e40c0f080551701b62010500042508003031703403c0b001403d40c23000c00031944a912601c400301c4643e2480307101039242e03000ca0790021049100344980101c20041200d5415038100030500404a04242c0050b01301652800a000342404542d13410400c901c0c459600e0701e80304a11504041c2041c043c11400045180480600c1c04000c506080320012610581c1e48010000d5032034000f24803106000c04015844e4001a13030342d040c51200d14030b0006030301ca4015040301c8501501e05012a0b2458480e21104084906580a00c80004c0303200a040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 770160134 1250 770158884 770158897
    0x303040318091b020607020f070b31030b061005031303090807060809011107080406080c0708070605060a14030c220203040812070302040608040b13140d030e0f0c060a14 74
    0x2803070307010701c03c5030b40c6006410319800604107400c5520a50102e80c030b08000142c00707400c440211015542d07070902d00c000051407800490400c020784c0c0c4005880c1003445501d0601104030784c00b99010072610f40340c1c2020011200c29030b0707100d000014814008100151017030058200240e100341481030186030b907015014100350880d84580d0201c0c1d05902000f61544081c0100d40c41c280c01c1c840007500d8200d41c1c0da42d000460086004110030001d0010000f9400f6070803a085a100b15005903055868400601d040d4014000480b205802803200074070009004801d40c0031104540e40003005000e02e441a6428882c2a682c040451031001100322040e4140940c1440114040c0707001c0c0701c08984d0398541c4c403941c10040c807014011004151040100b08030440c0d118007d550070560240e0006807944034078810300242445404041c1c45030041d070900d0109005e00054104e0a40c2c0e4a407000c0c4080350090042e2500e9082810012070740b500308504243c480c2c0f600c20002d200320705160038010410322105101c03042c10340141e03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 770161384 1250 770160134 770160161
    0xb030f0a0201020601120206030720070b070302010c080402130b011e030605031204120b060303090411030105030c0405061503090f030a020a030e042a09093902030304031809 76
    0x34040300d015540d050100394054820701c110b00c95020126800302d200c900c1b000307008004012203412580d91951411501711000990f070030440320099221a5101900d5018000c120050342c613041e00e02660600450b140c45c8140e0b0000c0c40e07107010200d4100c10b103024140c1a03000078100240911100ca244c42030090f100c0d590300d8107582c0015190b08090a01d40740c4081d014130168a50403e0008000101c0c40401007940254812440d004039103c00003c80e140d4000c250104d5030013800d082e100154011810040c604840d0b0403000c4a900e0440c0b0014082260800d42c0c6080d001440d40c01c085507601445001180c001407103104444080960440c05421500f1040031540144c001003240e100f032541c00409009d26040840741007080c0d0324400b040c030070101c11001505801001c40114040c0842c0a1003082000b028005800d2261041c3c05d840d1136a001210952a60103c0041007040d100c1e4092516070380441000c3c1d0019803079519244c4050754076941382c0b01614201c822540c1d001c2800307105030203500004c0c1082e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 770162634 1250 770161384 770161393
    0x20402040f0f0806090d1223100b0414090606041215060510050a032c010f050c0c0d03050a0609020d050a2f03040f06061e080115180b030f 61
    0x20240e910300740140030b600c40301c050351240701801070180c4041003905060241d400c2c0011548594428000075203c3c3c400042030700e10fa25081f20020880034130b4514411f09e00c054030080482d85503200031400340614041d9400086c803500200310141000034000340c0008004210604140d51742280c8800700c0c01c1c0341e208a132805021800d90a4290590007132002420080b2039918240c003084074000c04070301640c05000b08058941503806010308000c0da215026043c1040e44403204650703000b0883c080c00342140b07039200300c614120000d4590040101600c3e03a0000ea00c028140c0d501c84490100d02518000c1c0000072100c0d42e40f14000742c0e00c00e00c4d2004003045246554040340e6450f101c0600021075103440d80c0c40100000e1f20340e10200c0d5560312042e071840c072110034008039120786503030a00d200b4100980c3c42c000c1481d464000d001c04e4100130802c5040024071101030480c80e803a141c09aa50a03500e00e050301c0c03011504641c40a108030302281910000b8410746420001d0381080110000f4940561400c01c51101d810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 770163884 1250 770162634 770162639
    0x51501080709050603030a0e09040c030237050a0b0d1104150f180b16081b060a021c0c020102070209040b220c030b130c1401110118020f0a03020402040f 67
    0x64090154413007012800f40d418007403011405480c198014400c0c0340700d0105840002c4c100074601c0901c0003d590041c00c1030a120031100102441c3c000030818094290034002117942c101c04003c047e0000f918005081c81c0c4549180c0000451142c001d010040605a00d0740c0f1060902e10403c001b41000306411036440404081404000e00010400f0460318100034041054a010000c0c0d0080141110b0454000c00d0342c03a0054428643c0c0d11490140052101000007101c401000040d60050750b102900e034251141921819241d000b244a1080c135001e0b8000403c0700d405602c1d8042d4042c0c25036050b140005444d204080d40042c2c01108100c0f402c9500c040311806000800e45c5124500d8050f90080154642c40981c2d031b01c644078001c4083c0710007880900a840041c0c000340030a024844000d9000d4016110991110050303501102500380c041d0010341d04549011003010140280089516401c3d02840360402d56000d01c8900c5000908807500040d60310380010058550b84010001051080300c00c602090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 770165134 1250 770163884 770163899
    0x90709080a080d0b010f090b161b05040b0d030c030311091305010609090e10020306060c0303131a040b1503010e0f010506150a050f18040e010c0f0f050405010c0515010807 75
    0x45034007895078100b1038584510102c003078004032070a0960f070011108039140e80278901204981e00310110002c0c400841aa10400400940c12042c4203071001120b081c440f5102c850203200004001610140c0010081d0f0403010110380294091410b9041010015140c56400300102e817420462410034051543d5030b4004210244d4007101c0c600c05040441402e006500e00e80d550169240d0745900c0e60601950b0010200d07010341e40388401c40d0040b6503083c09903034803882e006070b106196150f0b03400300751116001014081488842614060300c83d0307600142d1000c064030b070980d030f0794945000850025003543d82c034400003541002c10458080c014408100114140c039106c4140000700d000d01000500584080c0b01a242c542c1d002010f5880c1c510140030b00d59203410744248140039002c1b00c840b08542280c03400c0a003015050f01908500c030b0394035660703c0d4001039203560300086074200b0b50101501e001441c180814407607584502e41481e000760244044408041800541400c00c40081c1d01100544c2c1c010202001040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 770166384 1250 770165134 770165141
    0x30a120e04060b0c2a1908010c0503010b0f0c0f06131109010303140703170a09110a03030207150c02030607021e010b0102030702010f11060c042909090709080a080d 72
    0x146400800c0390b04000c034924807183e4030030f900d07040125036105e1a04031080b61503c100900004001c02003404001c0d201e44524012017440c1405414801d50a14086191040c01141142d040310400c140061030010264040b19a5130800400c160140c00750740c40024204000300b0415001e14180b082d248201c00c5a840c0079100519101e01107802281000010008281c0281994a46c0b0b90b5002c045541c07155186412581200140d01718002c1406800611040c40c65130b5101d038500c988505000030001d40928200900c0c0c2225200007401039100c7e42c1c1c1880030421603208031028082d982440c2207003600315400030342030030412901c0710700681c44141d5406c070782ca06904000d40b4800208000308000f4401c000001e441e446108406030511040c440e0602000d4800c005d03034100300b21403509541103414003c4008001d60302070300c0344a00c02d01484440042a002e505802e6449290040c07045142444000c01d000d681070b40141100c00380b1416000010703458005100c0041c845200b01180e41d03845da414503000c400c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 770167634 1250 770166384 770166389
    0xb2d03010e01050f04060506180a020a12140c180901090902040506010f0206040323031005120c0303070f050c0901141305010b0901030509120a0e0406080a20030a120e0406 75
    0x2141c0c140750a02050900318800c0a4005d900988003144070b0740c40c0c4011440c4594840311540e50300480d2810420a09590381c0600507001c0030b65100300348a415000c5444c1514003880300783c4060100380c000700e242c1030021801041c0503402c46060481c5024214001204074209910500500380c646c4800f030110715182c40b85950008090034680301402113810000d41c1c800d0014001000d002c54101c0d403002801c41d0348944040b8071007a00711230f80d8900d00203111415906461094501560034260001803d080118208250040c043c00541c01c041480d101c0740384030114443e05903110701030b19400306003a8841550040c0a402c038540100b00d03020103403040c0000c5c0e550221207048820302d894014072103504040202c07440784a0907c0c003c9115100c03000814180b50101c500711003041d130001a00200140c03c4440700c5160350003100c00300306a6960f981ca03180c4614822600a02580707500c00c1a003050340282e1702380d45010b1009012120603801596404180c16080e07502c0d14081403490342ca10701c80c3d2030070f070080401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 770168884 1250 770167634 770167661
    0x512060405250c200108090601150302180d1a010504020a051c2901120b420705061503061303031121090106180b2d0301 53
    0x550300d0000c202410700b81c206941c00d001c02d440030860b9a1030a03c82d03000641015000550340321204100c110301000701c0d01c070400440c082203a90340011a860f0010030445d049a400720103488001c60080f10850007540208184441c060b000c060032412621078903056030040d80311751400d1810070aa590000c2240c1c5059112610481c010405204141d0f4448161007031410b80d00c4020303c0190071068400e000d4800c0138641c0c0c2105c1520486160480c8010007040302c08402a22501e480031718000002c07041c1c403814039070b00750040038076504c02c0f101c0030b00b51682c0340410401c10100e20302450020b100c0711800980028a84105501160308814800240303d019040708110450000001201001c240c442e42e0080c03840c6880110700c510041410301030741000d02c1c81c034030001400780e44003e00e00c41c441100d1851400708010b01d0014001032401e20f814807441080e2100c5c1880c150b541c90514407144060801c0861160b001040c502a04081360404854017010311340740c03c2d9210292802105043c00c59190090320a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 770170134 1250 770168884 770168891
    0x5010c0c0308043c03031b0b04032a0b0105190902030c04062607050c0c06120403030e0601060212030714030915070c0308160504080303100306140106080f0601020c030a0305120604 79
    0x103403001e00d5030b204413089980c9400c0411011040d480300301d1419110440113001140039904000c1055400008040c0d49203001500b140300d980007200d0110090103074103004209040f80401400300e40b400c41100025085031400c0b021107141c50302c00560907a001607038460151000428240315590b00103005680e2010712969180c180c03111500200e4540201809000c14004c1c001205251384105004001c848200504880c0d511014141e04040e07400041314140d00081c5170140c0340c072403088045030050403206e45900403c14514450b5400c0e00986c000f40280c0c0501012416010044c19401c000c1c51140c0140d40181142000d5045000702015009144104001030306940303400182d0801d20643c0c00c0740c070486c1070001d68500d000701900c00e44141c0d00055014800402084488010b829054081d00e100d80d905009440c0c00c21081151000c003809101d01051279200018030389501600455440f000520440d90403035078007404241000e00e0b01809900281000803035004c0d12030303103815503604a28140c1e01003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 770171384 1250 770170134 770170229
    0x13030213021c0902130204061d0a150f0516030e1002010203060d080d02070c0e09100b0f100207030813170708150a0209180105040513030203030105010c0c030804 71
    0xb00140c010080002926694500010341075444008030b9002c1c98035101d008550b00c9440344009416090ba80d00f46240c0c81802c1043c12549081401c005011a60080c49131610395004400a880d10720701a40355808221041c80a12804000300c603645000b01d000740c490719070baa031081040c448072803042c00b03580065a004000b4040c6640710180c0d410310179074201201c00c9c1c03500320f92a0508046c2c4522040070340003540f140da010a0009041c0b0420340207901500480b1002003940d0714481c01d5519040c959a40420a81103203441360802d0040410000001c0c4107461861740c80f547c40d04240d421103010815403c0900105001204840d10340d04503200700d41004200543c50460700565502d10010344440c0510050b0105250701c1d405d4041d01d0384880300614421000c00c40710f0070031602030002d210381d44c440d6051070042004524a4082d00c3c460540545c00b031407039a03007803d0043d680b0600c0b60700119580d80d0f003610004041480000035201a002c01e4480100070417450ba0310000c80e4020070f1001d0048815080403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 770172634 1250 770171384 770171407
    0xd0507030614010201290307030501140907090b1c0809040e0f21030a11040e070e01082a09010e0324100b0406030c03021605060a05010f03020d021c02061303021302 72
    0x4031109840c400e8a0400c07107006c0d0086414800c07d03a10040942d030a0095611a07481d030010564800c081d02d008035404195a10b43c81401d0340c020002054000464980c9107118030b54110b418a000c074040c4031842c0c5811030b6100864100d801844410401e03130044000c0a5828034144a00c40c0d19042a411410a24507801ca0b200154880580b003121400e64444d00d8244081e038000c142c40090001303441c20062031400e41005001c00e5000a41c19000a40050016418484030206401b440700030b00f550f12036800060101c18455401018a0360500450b00b00c4019560b404004c0e40301d04103111140c40e2070300940c0040440040c2c0c005440f03010015a4924103101580381e190a46048036510328020440708041d4105034024410340002294518409001e803041c17040c0040c1c01070041c500030034104100e82e030382c0c0400c00010005010080d0301c200031540c80c0015180c200c08141800c0ca101c10340380820318017030740094159841451420501d01070000d042042d0b02c3c20500124840b2030225040d45800c03110b808 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 770173884 1250 770172634 770172671
    0x1b090a2304110f030606070f0b190c08070804200307030f05010b030c090f060117090322140d06060e04141203220f0212030d05090a02090402150d0507030614010201 72
    0x10b100e010310f1002c035050003442320f44d10002c008103400031800701c85070030104c0d036071707411400f244980341c2101f4105081d00c020a482100c00340d2046401e6030322004951a0b6503540403904444485004211501584244660b0b505118000045118601815000c0d00c145009420f44a0151511740301c4d40105a0440c099111800c0c2c1d160300501512407504180e40d2000180d0310b0040d540b540c2050a103018003001411080000282400c0a040300743c02d007100b000000b001004c07601ea00581c0403440450f400c10907223007032411441510385d100d0b020206890361280c0f104070000720101d400391110f1030040c22000c0071080c2481101e20b84860340715001d107185400b0740460f0b00e00c0c18118034088000588e0980b1028802805010020341d0b9004000b507801505002c00c09949401c0b4484201e039907460140800c24603c00001c5c2880744650103056202c003691079400b00034001c1c00c41409d1130b04904d010094132503c44418442c0610421440c0c0780000c2c12030a201100c0c0c0b41001c0d003590541035a140005400402d00c1591 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 770175134 1250 770173884 770173891
    0x13030e0901050108060904080c060f0f0f01031e0c1815091a0f130f05071b02090c0c030f0712082208160b0a060311091b090a2304110f03 60
    0x31b408002e16203661408070558851071000480e0783c0114814030034441301d84130001c1d0050b2030400c9000300701e44903002c040400307070800e00c07000b054200200388852410841800130084580030355131032448a80e450500000a081c19412213429554908640d05583e912980b08405000c91100c100b12000c260500f405051424404961080d02050550f100b5950750074026100c02000703403804d00c03401480c0d0040602900e400e55075840070621508c210b021f00b0580c10f02030444950003c0986a440d190034191000980c09200e600115000820040d625040000010010603200d640c14038407002c10303c0c0c0001d000c00400b0b403642401148035031034213040404c0040c00c104160f0f0000d040a9591410101e140d0031941c1656005060415000030005815091b50025049a004824108e5030900c03000400100c0f25040300c803101142ea0140c9030101c44000ea50180c001d00c28040c011601c11600c94818005034081620000140d80710000c485100d401c02c0c8c01a2076059110411050070720444d064400450302004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 770176384 1250 770175134 770175139
    0x31203060f140d171308100207020319030e1c030f05091e03011514040f021201090b010207170d090501050a0e04020f090901060908060c030610050d060e13030e090105010806 76
    0x1000d5010501c40a05460b01d90b91340c8101403685e0380c01d44001d44c6200e1010f14481c0200e507008041010412000d03d00031a6005079000b00940480014115401e0300340c80b244a041d002c0140f4112207125035196aa0380c0040c1c00207080381308101a00c1d40c0740080070450203049020804c0818000d529080e00d07042011807641d01d841248880654040000c40d0051440b61950800070102a00014400241c3d0500c00030850042d20188042d40841d20720205030301c205483c42d0f446501c0c0c9001003110980b1603100500310b4205105844020f40d442c441c0f502540521080050b0a411100303950014981081707042004010a092444c1840800750300500311100b12001c043c01150005999486002128100c0e6000d00c402456440070b96140c09005200d80c803140504020b512540c400b10f4191040b020560307200f2030004040610282c20f208040342d094000380c81145074030340c4681c0089880c11000c030401d0300c5800e41c0807100d202040d03d41402040600f60442c0a40110300c1d06005024690740980e5807070380500c05 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 770177634 1250 770176384 770176399
    0x130b01050a1a0a020f0d1d0f011e1106041104240b0d0603080708070312020301030503090411090301060305010c120516030203070504080304060c0311060702101113031203060f14 78
    0x3c084042e42010034031044241c60340900c640c0d001c02e00b9080200e840d801d01804400300608a004000d00803120700b10340b44180854100d60a01500c5503016070800c44001040c5045d1083c01ca951058510340403080d201210840002c8030114004d0809101c0c0002440c87d001c4404000b10300f40380446000207490044540344400007034002c02441030340d00a40300840d03010f55083e90740c6055090400c519000101300301c00041d0402da151404c0d940d24003d80c0c1c180c2c4d801c40069494441014100001483c88016078000c1a10601c03817100d03030362780a20404005600800002c20544480b0400070518195104000d140340d01d40000d00003c0c1d4202c0240760038100c0c1c85e040050780c07a121501d05441e94000d236407200d00103200010303021409940c402d2116981e0762094031200c1f0480560105140ca442c411a00e15005034004401091800f81d1504080d00c1c120802204d03524160403190804000702d05900142d4a01008503052810389501d441088010320160f015004c1003401c0c1800e8550745c5001c401c565110724803 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 770178884 1250 770177634 770177647
    0x5061e0d02010f17090303090d021b0402090d0204020d090311154512040806040f03050c011805060f010602150a06170f0f0106270e06130b01050a1a 65
    0x180c41d42044a284210f1441070351170140b524a6683d40121051708444c020031400c4024540005400311500c00583c0b0301d494614030303aa0610000b90084420142e000288a10413400345e01c5070b200404a08140c40c1c00410980354a0038040d02880f00715800c041180c2c07020400964107104000865004140203200700d000841d200102441d111281c00900c2c0d50007910041b014090a044480c6043c0d0f4800c0c806440d00c840308103012418a001d1841554032542145c0000350004003000000c018140c0310741452424205580a00c90031540819900105202012156800e0010400003e9408450b066403030403950b040980083d12000c2600452562441c2a00031801c000c44540244020704966000c6000c1d20304003900e00ca0f914400101e40000500481d415511803000600503902941c5d10000070910113102804001810704400c4a2022480c0d80c90445221411007400054015100a1000e141a005a04080203029410b9104520802d030181d42044070f05108003410340d2983d004886540c4411 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 770180134 1250 770178884 770178887
    0xc010c0f0c2301020f030109110a05041806170307110a0b2b050a0b090a0501030c14040605031c1206050109121e03020f21030a0b18010905061e0d02010f 67
    0x8100402c011a950000c40c466640c1d44803080030750f040b07078100e400c18400700d01c4500a07101140718182101c00040d2080005001c007880f040c1000941c010905070003e8141e5440e000b141c55403c1d5481140020f400014040f4144507580140707018031402142c818565510386492200c2a100d100302c19a9a0481410741c0d840612045916404c0030012000c14821490070a5540700107025000c20140700750241030101e5001d0000d40706460507039900c6090b000b41d2504003034140407804160620317540d226840707400c0411103890900a025051460511041204052400c040d014040304a000ca4500740b800a00b0006d40e80d02100c0d074412500200c10140e0440c2003401c12541c20104003d000c941c100d516203c007010941c1c005000310791000d010301030b00c40c0c1e4556080091203403242d41413101c0014a051011440007803196001d8a03040c44018904075100301a5520305c1e55020099001618080d50341080080d141003404441d402d80074030306049040d4805800018140206681019042120b141d40510496 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 770181384 1250 770180134 770180183
    0x6050609100e012003120718050f030a080c1606141e04081608010510050a0b09032109010e12210c0f010b0a08060c2b0c050c010c0f0c 59
    0x4d00e141c2c00403c0020384503202c241d403030340b0000c00403080c40984c9002a144510400036003014014036002807031a180b8100822a0140200ca103041c1c0c140504807128000078488801045202c04042c080d0030034013460b825900680030540c1c850028010292001a5000d4144086407880e00306100414440c4801103090f02d8503005a8120700da20b07120f60360761000c84102c000b008034102e41c0350304000c4c07261ba43c464003c5506142c240c4100c2e40c02c101c85c48000c0c00711207604000341c03070412009421246c100488040031801a446455000350848001413401e019582c000500c034070303052040da000038421440c6000c1c5592001c03120b60f0030280c000d03003440b10140002d1a81c11503840b651a00100c449058007600103600078006654110711032030000800142080c00490503510607000300041d1414070303580e142410003400c0c1540c2000207a2459080508421845100f81e041c1c075115a683d80340c407004120181c60855007114055418000c81800812201d540514014500780e0322600c54aa40d42d8040c000d407000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 770182634 1250 770181384 770181407
    0x2030c040320040c110c060d0212010312021903091701090b1905060d1a0c040801060e010612140c0711030a2144180106050609100e01 59
    0xa8845160240c0c0b0240800500e0607880c00c0220780410584442d10800d45103c20049848040c5401070305540c1202d04d080d2001d8000240e00c0c907405840c1c90324068405110050903001102c01e901118403203003815904224070502d41c0020f141c4040d410445840180054043c0d03c81d141c42000724104820300c164081d0440c2001d990300c58002a05420300c142a2240c0a10681091030503a203414000744691400b03160318a0010b4010741c5040d610406809034500000004110b1900b4841c10480002c03294800d1042d50010401c5002d0083d0550600800a0210b40800030185d02582807181d400d940d0b00c0c0406100350802402e0740310517910041413600014507101d105400358540a0b03e40040c2c03c1c4208103121680d00c0701030b900e0040e418041c0003000d9074000c50010000d6085040302d0b016030060a5a2036032803070120103510301204002119081c41d0100e060890f0305100c055040c0f1031110b14a0400d018010107014100c44040c2070000b050042040124000c0a0204101d03200b80b292000303034040d0416100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 770183884 1250 770182634 770182643
    0x10911100203091503090d020120031e011d06060909270303090609070501020d0518060904021b0c0307050f090a02090306010311090601030b060304120504050d150b010507080d02030c0403 82
    0xc0021078131001c0f04541003103403003050314060312940501d090f1041c0320b402e8004405841103032a000c0c0c03101350807a0a41000b0310b0220049820f800742c03640d1560027103441d07000745582c2440d40008d0103202c20302d1300c40780c102501ca0382c042d900501420309944d0340e22010742c0d40003201201c540c141141c11081b041d5008041c1410507658000041441805440800d00d617200720003000c226001c86640d90b00481c1e4035035840b5158400900c00f880700d148805295456684006402000c2078100420240090201d901c041001811040c0c8c0103003291080405010ba03580e28a41180a40300d441d2030b0001140d408100141c0d4144038006040020b40781303043d181c1c15101ca80e200074040f40d18540e128607060f0110180603201d14850604076000586a61080c0500103c400d400f901e480d046461315603903440401001400881440003e01001c2051344031402e400f2a07550044201c280d107010180850700486082003105410031208101c0782002c074120004840d54180700302c030700503036990b90003130413104a0069410040 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 770185134 1250 770183884 770183899
    0x40b0a1e090318050312040e0603100c0807110106050109050402130305010c17150d0321050c0912060c0a18050d060207030f0e130f090819090801091110020309 70
    0x206041c3d203d4600080444a00741101d0481c1d180d02c02c040d510000b0812400031003808000c1030000790800300d02c035500450302600719041400403055807400c0d908000e51500000305000100b000069000b5001d00d15081302000030410141454002040641103001e01801150001200b01d402901040d1110043d0340050081100890907400180728100704906072034030310030810224401114540c07a00d440c0309402001c48610a4031641d060752001d4600d00741403d84a514640e50350f45685a0040c175100380c03800303c04541e0362031204d070802694500f248045100b42d8003010420081174460811184448071500340120304c03140480d001000342178160000398000d220403000200300400c58018246061194941480040d007a00c0200c48088144190550018a0030162a2510065488108160b000303080c0030501c022951540f4503954030600200c01c20350000450030401c1d5900a40b1607000e480746030024082425107480304080040e801150f144107500c194010441c8070300030000c450701900c001c1d000303c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 770186384 1250 770185134 770185151
    0x209010f0e070f0c0b0921030a140c0703030e0304180c0f08190e0c030a050a03080609070504140402091002010b040b1903080a0c0f05010605010e0603040b0a1e 70
    0x806994100e0322440162288181c08525198001c060a0880c2d902c0784d590400d502100d0f0b150790b069480080d0031048580030700020341e0503442d030062102140140560f6401c2d03032400c1103451241255900d0350020360354545c0005109060f4400d400326558540c1514001c02d03030003040d03d01e540c1944520f034050030102c0c1088001c5062001e05820400604c1c180303442d034804070094a070381a00e0100007100d1a8043d40380e0145000580c05035a0f012408145e2048101c819101114000c2440c00004010a4400ea88801d105c075041562003800a036100c5001e1f5a00c1130281098800a025805140a1403096007041d1140c001c080e11142c1c166400c0303200080c2090019140000007900900c0c202da02c1c03901883c205440811749040049440f120003012a005900c0c0d02e145807903401c1d1a4020000790001c008110150070081048050942005809480000741b1246044009440c0780722400c14603014101c180200704c0814006c3e00c0b040d5101c0d407405004150503414444003114115458010300ca01c3d850503009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 770187634 1250 770186384 770186399
    0x70f082d0f061e07081f1203020303100801020432090c120105030d211508030a030c03090f0b04030201240501020708010510051005040803040902121b0a0318020901 72
    0x1114011008000d00b80ca40f4000c0191807810540c089070b00b140854402c20204004443d14802191200381c8001c3c0d00010540380c00702c480340300540203000c0e00141d101106108074020846080341c0100200c5000b14905490640034034a88242025a44d4030420950480c544c3c00c40d40820021507404010001c9016240040750000b02d500454060a000c1290030300102d0242070000710303001c1080681d1a075485c5407400d00c81180003048100844068591074400310710701c3c00c1a1902d400d02a0114501654941d040d88a004049131420903d050416003001c01d1040401d000d04140c8a041750000c1d27080301145d4440c1800d9014056182545c20340180c1e01200c91040c0c290300b5508401c0c0c80d026401d0703c04450365030032210300b40d510030f603060749000ba11103a040166141c404082e0240900505010341040e507200c3e091400d6801030b41c89501d580f5000101c110003805280c1d09158002c0307414a4803a48440710400f808000d00941c5080e030141580c0d00e035400e00c40c1007202d00000340d41303030300410145041d80c48912 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 770188884 1250 770187634 770187643
    0x60c0307320106050a180b040203010b07020118180c021f021815090609120a1505060d030804080a0509040e03120f010e04080a1106040b09070f082d0f 66
    0x444080e6801c000000c02074a403040c02000c080380d038010036083e0f41c1814103003040941121101662a25650f40c60140c000b5207640c0081d500800030070303280641b100020300002d402c0100c3d5088200401401c02000d2044048440d090142c51502034400642d220000e5026803422a070181e603520f40d0800340f83c43d0100c0b400036030014004000c600c881074000c0503051051050b8115548001c240d01381051100c0d4006003002c40103007001c02e8009040710a440000304085041181495041d10040c1c1e1510100704081c0850082c3e64002c00281c407107050354104c07500d000740324400160000b0410800000c6e4030046904c94010745400141c000c004000c850304000301a42d03030f030303000e04c001310341002c0080001128400c0e46281c0504030b4410200c200803d58481c2d40f801c0c2e5581c8441c00001c240141e500c1c81d09560203082002510861103030343c10480c0381c00d00301c0b41d05e803500c00980e10604c4005020703907082c01646800f0640046441404a00600c0d1204240c20f0710109020050703051042d00c00c8a0b42c9444140000a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 770190134 1250 770188884 770188943
    0x140a080315010525170c0304150e09040c1a0c0c01031505061309050c07150c02010f020408033721151802070201090b03040303061a04031505090c060c0307 68
    0x490083c180304000c400402d90f02030781ba00f601054005001c10020000c815400100040039490020840707682c000026400540035901907a00b031340840000c1c0a40c40100c0144007848500e288010308105070300206641c0c4004100d40c447c105510b5070440c0501c6a40c508084001d0140240000e868580d15285c10051506a00c1801c1b074041c00c140c04036000400810445400035000f01044880726490f1a000c005496a4500d001c1159a40c0040c07121442240c8054006012400003555480b0502d03160002a118000004010340c203a044084021842044120351410f1260900081741d00b0785d1400c043c400d24180038500d0120703051030411507403107c0040e0094250388940f680d0780000400154400106e008108000340030901c00a0140240350045016641c0b0034868903003c165203403203a403068099422824041d041038000705050003044041c003074004060f000b1240402583c50300641060392103820200a0b40074400003d40122102c00900450300b50315040001020031450800e02402d00c20fe02c1c4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 770191384 1250 770190134 770190143
    0x603020702180601051e12010609080d03060b030a09030c050a0309051c03020303191e0f0f020304020d031b08041e0509190c0912080304140a080315010525 68
    0x10b0310340302c1c09400d9602414001c03101a55401c1c1000c8100b440c80515210707900074040f80d03c0c03051205c050f034a00b600f008117010f03180e5580d4500040349481491840e20841184410505061903010b00181d02ea40003580e5000015007400f003000c841509082d1902d103d010030260003802250078203428141c1140301c050844000b070310b8080201c04034421220640c40e07060030007401600100041000f0241c40d480b04189414008000121744c0d03000d80703942c04400d42d0f0f402082003858848020301c0c55040c95115500d540c0c01c12000a40c0395240c80e5000801128030f0036001801c1c03004c03a40d0100031021005a019020560001440f59220b44800000c20f141087c41440c81030205c009901181c54207202e0000b60007070045803900380720034421000c2d00003e01300c0071000b031007041801800056044106017446450f1801030030440e070340e07080c28203001222004030140c00e52250700911046001400b013208a036031160700c1041111621410000484040c410340098070b1003144c1072032446809407031401000e03410a104 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 770192634 1250 770191384 770191399
    0x3070605040605180f0d06060303020c1005040302040f18050f07050103020c341e0609050105040605030402010e04050103240c0e0f0315011509060e0d030e0f0405010603020702 77
    0x46150455951181c2d005220018000b03109100024011840010410800900303800d000c01880011480e5000303006001e031030b05600c5200030014150107200301c01110301c042e2980d240d400034400000d00144114031000b405256100a100a0400c0c04e80c07002c69011111400ca10814202c0c0c1009a540e0000031402038944c00340800000d007a601a00c02c880e07400300300c00081d007403251300b0360300c0c00500001200c0070542010030513100350551444a02940042c00c4140390800d604404e45070011b04180c19500034009111a00c0c3c428003190707820034203583c1241d00900c1d003142d40e5501d600c0122105158999550f0b0098207240000c810002204041c8242c0403802d00c05030700f848598803590041d00c41c1e0300d88800c0454152404030140c2c1c00c0c41c000400d1200000307030803204461a0707140e907243c1c404001d0340040b4800b00302c40709640b03080b944040e440d00140f170903140c0181040c5101c00051071040d41040f0080034000c00108840d01a219072214000c002c100034810812981d545401a01031351102c0d500302d105411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 770193884 1250 770192634 770192639
    0xd0c020d0305130f060e0f030d0608060117031b0307080a0e3c030a02060a0c0314040f27090b0a0e06010e04020d0503222c042a0b090307 60
    0x40290f81042a07000050f40c0484130454036041c0041c0b811140000303c600400e1400070151601b08010f04100e1401c210001d8114a00710070241002c1c01070300086010361000485c0300030748200200f074a0401300c030900320001030288091010329510403284001c003a010086004250030340c1080319200349003020350798004440c15904035500c4604150443c841a00e1410014031141040c40e4404211384002608491300083c03690005102c1c1d420600841000803140d940300810036034007400c04d450500015244500382802d1180300e0b9481001c038011154001010050905203190396403004140c084084000c014800a030b00703081110090032a0040001030a040222017580c10001e04c3c98101c42641d0b1100015445590810001500d900c130305996030f220500c080e21861410004a41d000d848540c00844620316000700c0308201c0e02103074400000e8507031800d9204950380c4aa140142d00c10f6100403c030302500090b21044034211080f40241880150440020920340100b000400e05400d04400310750030103a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770195134 1250 770193884 770193901
    0x12010e04050d1209020904080d1d0606091012030806030c010905030705060a030b090f0a18050c1018080105060f0307080d050c030d05131b06020a170d0c020d0305 71
    0x1064030000c0c51980240700002a0a100d403184000c41d210305500890f098203a500040d1a104050314240c03042c0500142e440c040081c94450b4442210010140451407040320081607101c039002000540511000c00000313241d20f05400008000d010861103400b0030094138200140f53303500441d141c2d1b00030b01c280d40040c0f071190301400440e012101c00030000c040f0b1904200902840d5048401c110003455140c648848403681c030321380d500c1c0c40384810090342ea00902e490f03c0341c0c0701500c81c1409046c881d1005109048089000440c0702c01d05c1c02030694002140f607180c90401c0307881c14480c0c01b4011408142200220381040c06400441c0200c400300e0301b0071079001002c8101510b44210f0f1040e0005503006600d503440c03442c00b800c091720220000d81c1c290380c104142c61b000c88051b03600407248804000f092002c040300300b0841080040081d410186111104d604041d03001e03545802c20400904509444c0000c2c02c1d0245800c02290000720000c0e030b00b4007038500102c1c03000c1e50f1006c039088894003103420280054403d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 770196384 1250 770195134 770195159
    0x702060c03011a220602030c01290d0f05060114011101020a0206010e1003060906060501200718020408150403120b0a0501031a031605030d09150e0a08060702031201 72
    0xf240600c0500c8524019142d0300c6500781e110907411603543c0d400355401d031104200440220000c000702e4024681e14100d445029084581410a2900300702290f5000704039450b810128110004041e1b40190b240c00c401c1c10110f000401e502402080d510411001140001140c1c0301080c1c1b4580a03290708503e4140102814240e02503080d0b54001603001a004002400361008115007280820600d440f00588a80b510000d0307604514056617404d4807800d04100380e503402000c00101c4c4800c6144500070301d91205c0300700c0d00c52001e4801c200e43c02c0607112202900344540c0d03040701c0c020035481e030403166881520040c611b00c0c10411603041d800705440b502c0c0c802d400151809020090800184200010342c100320054000700842100241c415940a903c014183c404110f000e45108020078524074491500307003050300c0c01291a410008001000c207040001018107130203500420202e061907002c60000e40040390b40c14005e98044c500310304c610003d0007080740c1c020000f044081040c880c913581680e2a00041005c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 770197634 1250 770196384 770196389
    0x6080106062606060c1b0f030c090403030b0a12060c020c060c150c0f1201090f0b03030d2007060507120603020f0d0503040902070602130501170c0304050c040c080702060c0301 77
    0x50000da4445203001d030440341400c2d0361011000309020300340200c22021518250007a410f4004401009048980b1b03441c2c60260300e078030003400301c0c02094001d200301e011130780460001c1c3c00142415118816040946d07204005240034044e8508440e80000040c20b0940c080c0c070f9404810b4002d4094100c0140311070030310318100c3c2d031ba01070351000514040345082c0c0c0e03000b642a000ad007800d00b5200140144030803802d04500810b0b07500b6800c00c50102c01d50518402000719207450f82940045482d09140d151140c80100a9034030080840c81c1c0011500c038034038200380004d41510402c6960b40f10010305207080101c1a4860b50243e2026564408100401031055003110020700020350b102a008020b0701d0540745c480e270f109128622480540f41415604e031121000c0c0d80294804940c05c60700814000c0202c3c0c180180c40340140f1007441c0091001214046080000c42c0103071034ac0d05003160000004007849010819000102c2024008001c10150b60500038914041510718000501415000c0707906024518180c81c103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 770198884 1250 770197634 770197667
    0x70c060908060117031b0d1101020c0d0c0c05030303011508130803040b060424050414070f052206090503010506010e01050d180b1e0a1b050c16090608010606 69
    0x690a10319100c0524049882c4e010361440200012410881500064000c0102103802400a000d056401070702c6131408443c004000d07803052110352030300781d40004c403e23940c11a40d040440960a090800100790210364002942501c8004000106020005141031048103559a0039a460711000c042d03112460500502505025051002c03c01040081c41420382181c0c004200060003001321005402000c440d0316070201c00078031b204080106044c40c0c0900075040244070030f840c0c2a0300d44441b0140c10013515007658020403001013180004400b0021180c8030010820000c0e0065503074402004060040c28068107000c0d50900010402a5000384800d40c0c44090584809080c01c4000340d2100c020442c18100f4030303481c0d000c10070f203102080f60a1661030085000d032950482180b41c04041401000b0060080428030780750000b2102620032400328540d000e00c16150560351100d04120711442c00c00f00c4000306406001d01ca10005407071920ba4003413012104141c00070b0145e99601d64041c0c03840d100c194881c06 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 770200134 1250 770198884 770198893
    0x402070c0f1706070302030c0c010e07231f0c150c031b0806120a0204090b0703053702091e0f03070308031f17010b0118060f030b010e060a05070c060908 67
    0x412050191b0065640081102c00150410701000d00750750135202031390001e401e2900b210000b408501c62030304030070000111401c041d51201c20b940d004507a00c10f90b0010b10f401a201c182601503c0d8510500500400300e400c0510075104d6a04d99290f14000c000c68000c4c03030042403418404180c0c00d029600001030400c02030b00c1d070014955424044c040d400a511511003010f01038803041c2d100503503807849001407507801041903004510300008090101e030005024141200c221076a02e0f04080c00d0701d06200d21045e840c00c0c4404000c1c2851191401034000ca40340c46500000b1001c0c6408040c0c0003001c0164401030031211602d07181124014541c581750140405483d0003c108005601c00f800c0c6005151207a5440000030000341d90341d10b03001310010b00d030210407949945841e0176002d250f038080b00e401d01c0142c20100a641c0c45141003006824a44583d0940041c1510380c1007482941e8000e62071030f1041c5402030f008540e9000d00200091050b40f01141c229680440300e81c021039241d21030ac3d9a20107403030380c6100a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 770201384 1250 770200134 770200141
    0x1509011401180b0a181403100902061b060601090f1202040e0a0203010204030317060922210c0309120f0f11040f050f161b030e0402070c0f1706 63
    0x1190503110300201e14816084800d00003c1d030039028001412500c2d226500c04500b081c540012102c070f104241e100300714044000c5044da01a41c0c3c0810300452241407940009030404551010030981c0c02078043c1080740500148049034903510214025100b030900343d0b114400262951010343c2d503103401d801b030302c40502c07191403038080181072551141c00848401d100301c4038942901c1d40040e09a0f81303e03410480c0003c3e44090703040e80100780401941e400500403940b000c0e207444c00660031480d048030149002206082c44125109000d10091039843c6860780249804144d415100003403c500080321040740052101c030b4002a2940e80042a804e14a80c061180c056206850700e030200c1a070a80b01050728810400d1301d02e0750075a03aa42c840c01648200401010a081c941000106268403009003e194240760241011809a0303101c0340c1600303688090064101903503ca03040840d41c01f000d40c440903401610025445003400360080f18182201d4048c020115059100c03d01d0f94004030820321600c040364082d0700403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 770202634 1250 770201384 770201387
    0x2301171b0a090b03010602010e10050f04020103051f030b270c2b030215090118080f070605240102030a12020318250b1c02030703020708070b1509011401 67
    0x80500050901d851103080d611050b4030f210340d5100703070311450160b03568141c0081c00c1da00a0250300c1100d0751150041100b4503188604803100c0f80000d01c02810150784c3c000140814003070504600380c40221b85080300c9504e40fa031400c4a0308d034005556120307040c0d20083d0441080c4016490180b07c42e1350480c054903000c0558414018400340e03540d4000785216040340030016803801a1041d254041c025801805c00240115079602c0d88032025041030016410900345000100440c09040c108e02c2d409144580e4079610000219250b0094800042c1240d05000502202c98002292a182b40c01110b203400c03040301c2200010b90b40d034880c40b00e00801281e0000208060035000d940a9580002e1601e5802e14608800d0040c50500d949581c1641060004441c0705c03500d00f24150820000d440c0c06c0251500e0480e4042030b01d000e05140c1da41281007144c00000080c0750a00c00c1c1c0544d9030265010982030707120581031910840e802d0f02102c08881c81c03220100290031615002c580d550403a18440a20950000110700 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 770203884 1250 770202634 770202637
    0x9050c0a021506120a081207050c0d0f03020d090b100503030405130e12070503030f010906060c0f020d02220b040209010509010e0f092404090201020309010f03062301171b 75
    0xc61036005004c0c040700305001c0014001e480341c8604c150000e942d641c8019076120700c94000500383d0420410103124846401d60001891050b446090402000464000f1402c801074170a607201050303240c1c184110780040010302c10030783d80207d42c1600e82290701a02d070f40c14141c0e24092403080c150b000024101d5030702c00c0d045c079034040041810034074140c6501c0c505900d2a582142d129842c04c4406910000c10401c050030340d64010b0b80074003003c02c8140040c82c40c102000b807030900e010034090030b03000da2080120110341d1204030740000140d0180c01401c1e000e110b40c195201c1c4c00340903142c50320340340d06180387c450151074107100700da180401c140c692500f081c10740d000448030134400303400c000d030401000200404036607200c0880324811004034032a0005940401d900000b818003031040207015504203040e410050380c010069406154081c03a042804403800c010840141503d0ba20102c58100d041c00300202c083c5200b01c5590b0f9042e800e0f00c66505000791412468440d0004070340c10b0f55641d8181c894240c41c1d14002c7c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 770205134 1250 770203884 770203891
    0xb0705030c0408030f071109042102071a1909051e0102010906050c0901091e060e220207020f060c071a0c03040e010305070e1009020d0212040c09050c0a0215 69
    0x1060900b400d84481409181d940901785080c00850081140400c021480c0010780030b2220664907100e20741031640d40c406000f40c0c21031600340e210005450024405100300200780090600744a203e0128045d00b100407110f622502e108200e907040d181024401c0c034029206002120b40c094040030410909042030b4600c0d80b000c468541c115501c0c1e26a08000c1035660240d107004004440489598a804000241c1202417030361200002198075100005c0d442c410300c40039400ca4985080c20401501c0041c002000340c40103841040b5580368061080e41184000c0d80030b810ba0904c25a429080c520b2110100002c078082c0514400003a80041e00c10301401c5044d8603664400b140903a480390510031111032540c10b68000da00312490045280d8010002e10000308010001800d4100e203201c0c082c01d00c10003101c0301201500500710500d13000a4030075140c1d1031a504540181280750829066400c0510300004010744920030041c1a60404001c28216610501200c0720701c2c0c401c1e0001c200050038a002c6010003000203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 770206384 1250 770205134 770205151
    0x90604030b280e06150102070513060e0c0f07030f02071221050306011b031803060f05150109120c21030f020309090f1008030f0a17040b070503 63
    0x6000000000308414000d0380110030040200407511803124020114204480c122034401d81011001000d8000101d00150082800b0031001015510100103034640507281d440741d03412001942034860003020790361085003541d451701d1203502641c5481313041e81d826005040c80c50351010410013000c00003900a00c0a6059080d030741c0140d60030203686514095001c00040d1302507a1161041c910003144d6084440700f84e18809160512600303500700900000c01307004505819820707c0000e40300e13403000d05028940c031f101d2071241a0541c0003070b0b6480349401c401500040512001e56400c21010844415031001e42880c49074040c0d541d01d088ea8600800200c02000c40007041d601808119004076030313810444140ca2502c2400e0031051a58211450000e0034110781c2d0500c00c0c00c40d0400d01027000d10340d89000406d03030400c1090710b104005840d52000000d1203c00ba5001403104e00c00001d0300c0f1002e692141c00f81c000b40320280c407049059032207010914841d1100b190014040c0e0025000160102c0c043c901658029880 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 770207634 1250 770206384 770206387
    0x150406030c090e0c07021302030c12041406150306160f0e060708180901140a090b0301180605060a081506090408040f090207021201090507030201050c0102220303181503020906 77
    0x5400c1090010300c0195404144c40c034000070504203605061844403001f000c0c04208514514080a640301c0300c3c020721030646506511140031409018540c01c001c0c2084500b82e050b5842c6003000450703207402e5a241c88489011b0b000c3c4d00001407001005c003072100c40a00c51900c441d0581c003030a01040350a0b0b10500801540020217000c0ba401180c00c98004e800407284a036481054030346900c1c20041280d0051f88508031070440a110441c5039200c2a5011044803284d1101041c0f480007031000a001d0f1001e02c0b08080e40c0054080d042d01408640e800c0180144401d40e101c90f103658590b00b03001d44590f0302e202080c0241510801287d9141041d294480c0e00602403481141002e40301c2c5010800210700d0740c003a07441c8540108564041d071800307090301088030240350300030800b02e0352507550b1079118005c9100280c1840000f1420014071a001c1d011581ea5803a01d81020300e614211003074007218000309000503800149460820722a031440c80b0070380700642d242e140d1116030381880440b003207010b5030080c0907281d04602c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 770208884 1250 770207634 770207639
    0x408030301181d0636030c0c0a12030c0c12060f0b030a03020615120319031506120b04020405030a140d03020306150306011218030f02070f1a0408061f05150406030c09 73
    0x5c0c00044000300b0480000a0340d500c41100f0b0301680f424803056490341c03003801a00d00810009007095480035490303030700d03051424005406050188900c407444d07020400c44c400c42c035581d004001d500d0740105500314070020208080b140d090181580c500c0204001800369121101240e1340d8104901d2030320304000020200007a5907503503002c8c0c5046802034000c03451204c04010341500e0441d0180210042c40804400e1101e4242c40e00300000c0c041509940d8424000b940c410548142d0341f0340b60111001f07030a001d022200705038400d20302900141401c080042480c01501c80c081c007254800e000b04d0740180d20003010300201c40325840711004180d01c0609424148110211840700080003030040e030130400d9141d454000710000c6818003421240d0540b0607a0304540200100340907480501c051a011307581c0340c2e50260040d03511044401440c1c481c40d0050101c500c04c96003008051000f50b262585498500201c80329800d99610030f000d28181c843d141030714185000d010522009109c0d621038250b142e0300b8540910f0496 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 770210134 1250 770208884 770208961
    0x11040e090c0d03020304081207020d12030603140a0510050603060f0a090b010603091b0e0c0901090302030f210909130203010f0e031909050a1a0408030301181d06 71
    0x25200c1040f00540c00c0801c081054075000c0c8200140c0c0e640c0104005e1410545600040300002030100041c078003480144000e0205200e90712040245a00804c05004150204603250f586e804d2814200d94500ca89050140a9840c502826001e98005001800e0320789400c1041044940c0c020515001107503642d10480114103a0207d0038008d080c84e80b0002a1225182045000c091021403001e00600305084208078145040600da82d105071814965611601c00d4401254408566803021b98144071300c00c4581b0080c000805c0496803a4441002000714601c00d0307400329400e004603000180c1c000c0301c0000080310148001011041288010000548249800865001c88a1038074007080c00d5840410303001c410f00076038080d105008040d4148010500c1c90000000d440740c81c1c6000324501003141c8407030318021078101019140582542030a50b601c0f503844064600010b0788418854078400e040201e403882c2030b540c000c2e040061000c80c60203450a60391341d89140c08080801d52803a210f101120f10b0480c80007 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 770211384 1250 770210134 770210149
    0x1603081f0e07090e06030706211a030105010614040501031125060b010903020d12020a1401050411090f04062f0306040608240423010e0d0311040e090c 66
    0x7080012034014203824000402041c03529590851500400c1d28003c0c42915540000c0301001c89601c1d28080010360008803010600c40c80031001400c125081000c0d071071203d0400c0e8040314103c441078000b007100c3c1e030360f80c4411688004407544e034400d290b17010002844254800e800100050704816203591034070098070304001c40c060b0400d5152038407000e080440c4081188a004100e06c14409107040d070f900c4d070b0864000030550f43c5840402050441901e02142155009200006806400c4000204490400c0014501038541100c0840b0700c42640d481c0061180780c0046601d010b06803002d6144d415903615501c0000a21000c4e01c02d04410047c7c1400350420750800340804032220030b001809440b8103005061100391001c0e90441c00c01e5421400003c43e001d00e1020100301e07640c10000021881e41c0302c9052000c01c441002c010084580c4200c0900c41107440150045e000b504d2606081382c89000410390228200c421f006000c9031504001c000c10007050000140c4c6940103912b030010344220402141c005002c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 770212634 1250 770211384 770211389
    0xa0c030b1309150e070b0313060203040c0602060c030f06010c0311070b25021014040509070503091005061e010212031005121b130902030708031c021603081f 69
    0x240c03a110744120040182d18800751410307440c100c40c00e10000b13200038600c913100c0c080e60050840c5c000000c0300103401c002c4200f0301d541159802c40d50440d5a8101420b294143d4000f502072100988152804590f05269080c101c038840d1055401c80c24058644800445280d4003526041d0b0030010703080344400c0b14020502c0030700700038402c60744090381d02c22080640400540d1107121070139a03402c00c075000b13002603111038104ca09500824542140700c60124513440599028642103c0c0c0c00c2940703034080240441c1c0001c000d601030401c02c4225641f14425071131a01c103680c0c3c2100d15030b07042a82007500c8a41340401000500110030140181d807408800c040403514a9002100c10b8101281250700802c0141080004075020035042c90140c07170790b840120144034403450390244440c01441441042203400b00030360b00c58803803903070f0080660381c8041d40c401d04540d80707800114840818000c505440d00414015208039080304508079056100d17982151804d0b100008010180072504240c031007010300f0a122500140d02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 770213884 1250 770212634 770212669
    0xb06180a05061212070609021801060201090b0903090a0b090d0b1302010905180c21040506040209010f05090406022206050a09120305160c08011d010b03150a0c030b 72
    0x10103203008030802500f0101c1d07a00718010b039000f158004c0d070700ca01c406040380c0c0260b400050200311050540701241ca02c0851a240c40b0302070361183d002044895040d040105030790b015842c96400745e101c0009907a101d108070444103500c0002d90030104203114986024007179074a802405490b03041c1d415210003128a02c100c0d803801240070410300080c21580c104a61002411066448100d4003425100528890320701030710383d150080c1c0100e603400d500344002c0815519003050071264201410036240c03450b40d414050350220702c6003000900210782403001030203050494a00914051494445807582070080d44504a082da50f182c0024001d12201c1c5001c2e040d1000b481c0d19902c444d624641040000c05252141d0024071101d100c41541401180c1d104040d10310b5076200340302c8139019810178030301070308204400d03031207451113509286071208907141850840c030340d515400009221950240e01003544590b03114504440d00141c1c0008200009440d50140301d41c041142000074102c0c40c0e5800048203d100d40d1034509 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 770215134 1250 770213884 770213891
    0x9080f04030309050a0801050717150607060510080319030e07030203070308040306050f191a090c0d0b030a02030a0311121201090e1209010e06210f010806040305070b06180a 76
    0xc07401d1a421a000518202d802004182003a000c014141104a040b403510702c3c2b4500301280090044100e407003003000004012950720040d610306580500000c0b1072072b024010400c5000140c0782008000c0314040216050b00c42c0d8408a0304d5020360040c43ea4401182103485041d20120050302c0170085400554082c20720541c4441c65407030400203681004201c441280405428007180c540100605400d808610001040b10180c10000d1200300c40031105c00c80e8000c0c9540140186410040700400104440e6003060041007a29028141d503201c2c00701009402d0f40c0005400c2000c81c1c40303a81d90110f600e01c65010f403200c1d00c1d81030641d1045d9800a450740740794559000010000d8480502c50500c030042040301038004804e140c4038555050003415007d90500030040c3c00140c0720350360242100c0b14040e244205008105580c0d0382c01d1080e0601316100d11044024200100d40010000742040c4602e03403580e05d241c609809175940a405601c0501f006e50403c0c2042d201c0c0782040c4c1c1500074039204a41044000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 770216384 1250 770215134 770215139
    0x1308010501120b09190f0204020c010c180b03090309060f1303050d0f020d020a0b1801020c0a140a080f0d1b0f08060a030201200705030a0501050411011e0309080f04030309 75
    0x2100c1c020f001c2d050160b65440f021174500c440c880710380345900301600000901320500740750003c600a80f1134100c185400303506c2d22007481c42e00f0b50050002c03044044020402440641c0311065100070341b2040e2400840daa00030300949005181c034500038611070812304d01c51800c110801d10806003152107600126030580004d01010784c541d038081041000380d1010b01c0204603040034020007944400c03044002034021000040014030b4001c0001c1c41980041d6824021540c40c0f10b0055040e4841c0c12160007210544140800441c800134005110748035680c00110552800340d00d150702000d1a4030071001400308039150307815002c2c078585500c0300304141025a1281401c08030000741c01010101d009118034403400903e1700c140701607680101e50030080002400d419508400008003285460f0f19540300640c1031240c1c0c10b480c410450103400039405a40308400640390f043c840c000540f6105425048001e4008019400c5909184281c000001c0c450062049925100f400100700741c00da8031641040c0d0200c3e1003c1400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 770217634 1250 770216384 770216393
    0x70903020303270d030c0204050408090d0b011d071d04290301200f090406080d020a0b0a05250909060f0f051002070627061e0f0f05130801050112 64
    0x1c02c0385403281200d0300d1321114840daa0241549483c1c12001c0e000da56140c1c005420441d0410441da04a0303001020050552440e14050070341007024086c0070421455280c000b07040003010390f40d5078000c050b40e8503200d028100b0540054034031901d200c00c2c9a44942c45012000c2a60000c070305c1804101340d01b1240b40c00f0501210285070130b4401c85201c003800302034526001e0000040300010780f84211504510590b6604d601d100060113000650400c0cc00c81c019050410700c00781c0c000401c03481152141415021641d102800c1d44229501220f0304a40d42c5210390300b07101c0b000000001583c0b40c008a04100321103c0d1510b00c102d0494481c2d0300150000c600024091080d020b9407502180200740440f4007410740e507001d00340251035010034410981440302c50042c0342034800c003c0007030b40e00d1509002c0003e414240e88200050440e078440034582071012a00038003009071445501440d0f00c1034460744552481c49c05408084429921036411b802d5050000d890108140740c080c00382c24001c0108500d2036440c0e840a040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 770218884 1250 770217634 770217697
    0x1206110a0309140604120c06090503031e010f0503070b0c0f1b0319021c05030d15090b090721111303020a0506041a0a140304030f02101e05070903020303 67
    0x3503c1031540c00070041000007210840070050040e03952070700c41100e007582d161041c040c12440000800030b010201c200004030805400c01c0c200c4091820030891a80d0740e442541c6054070007401890742540151400b0b11440d00450010314012a110b8100c0e9020500070f0419400e041c1110320b5111a10580c541049080c9020411207044012100c2414100c1e107581d13001580c07060000d10540005594000b50700c0520005006480034040c9482081c0083c00d44e0b801c1175818076200c1e010f6050210325100c80c000890805c14003040c031803000c944400c000300e00e0f5034250741010301034401154080d98407490380000c01c04603503019101d614280038441d15406e0540c0304100840794681c101d0380c020385051104000c40813a6400e4034100015010280c2d47d0b0307140750b00c6c00303c0328282582600c1d90703800400000d001c2007650200103070203040810b50a5071000e501d610800400e492180340480c2000d185a800c0f00070051403603100e10342102140c100400c165940758003080c19a0000c51000300b4121580301110b00c0504d4018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 770220134 1250 770218884 770218913
    0x1050a090209010219020a0e040b090106060503070e09101a0301031e03140c0127030e04110901140c2a180103031209060e070810020a08011206110a0309 67
    0x2009500340b840781e800003540e0381c9503460041008255110032206546507540b03c0c4010f0843e114400b20645014100403e08820079a5a50386a600c1c0240020700e1038811000d40740030300556036030003072511010303030800034104009020722072205d111086c00141d110f00f185840c03c1c0744403504409500c1c1c0d855400c11856800005403845920310700f01071076100085c0c0c00700289003035078110340c441502c0d01e9040043c1401003021080700700d0320303d82010401d151850240f800d004410300c66a64800c548074040280420b07604000c1c00d04081035000d2051010715801a181040401184540780d030900e07030580e80d001d24012030107070034035806617800414140100000300b00c9002900d0694080108800c80800404001c205101c082c0803c00100c0c0e06a00404440e003106440c1a04028144807580b0034901541d21510f6510906143c1d1141c0c8106038210340c2c140c020398100f00055200c2240307503841c2c82170344400610f44410071180e041e9a1544c0a400030443c0028042c618650340c1c0000d04070015240c043d11500070035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 770221384 1250 770220134 770220149
    0x10b03070504110306010c03210614010903080415020a1703010e070203030f0a052e060927110d090303090c0611061501050d02120f130f172101050a 65
    0x8849600800146022a50172036000c1c602030b0194809420200c4020146111502c0c4040e040c48040ca5511038a400c0b04081d04d0303003081d401c01e09200c0b2800640750041c0c2440000c1640d8000c0c00100017003803000002038456680d50054404440e155038414140103c0c24085c04d843c100041b0040c4014409014415800740d0310b0f000030352a60504800003512280c4c02085188465100c0c0000380001602c00800c403002c1d000c1c103800c111628140c16102881103113500031400001d405100000c1e004466080721030381c0e041c11880b0340c008160320b410944003170224020b07008100c0b80100014814805a44110341606000c0d40d40024160310038075048588ac5140d40c4030204020541603900f100300f07404500c0c217130000710400070340c1d4042124500580721400b4040e040d05103544040f5074401a01706c900492445003100034515042c03980c8141032030085003034940340a01403820000019001035401c0201501c0c1d000141122402e11908007152440c10684404028081c0030076801088903040040401c03004c0d0015 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 770222634 1250 770221384 770221391
    0x902070c0605030c0d0504060603080c0d121e18021215061f080718030311070501030903020a170405060d2a020a0308101706010f050109030c030f021809010b03070504 73
    0x1644d50107404c1d005410944650f1991103011904000055010100950340840181e440c0c00c601c10308551a04076024800700403605298000701a05018403a01e600807000c440c2d0306035034090381c074540741c010030108482d1900c0e840519011405659264417003602c1d120075000400056240544030454400c026003a28090411039000f109810021000d009021446181100c059034500904586061950803040000380b0244804410300da404a41c3c200c0c05101002140d61b01640c0e80c0044080364414080940142c0050317910b040010032840c42030300546d10f5600828207087d03d940000b0180e42c410741d51120f0040e600c040010030f60095611541c2c80c1070007a0b1440c0045102c1e5440a03480350380e010001400c12590300005002410100c590001521001440301ea01207050b6128544c1c0c1c2c8400c3c0281e10361000d211900040c20b6200756040c40a0360340c064500d007012031550f542c42108040d0188100d90041100080d1341000000c4500e6500c10204940082101c59903c01803504001349a004035004a00707 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 770223884 1250 770222634 770222641
    0xa060f030804031205040b0912070b031e10050603220c150f0e4608070812040918050a050705040b0d08070210020a0c1d09030313150e0303010902070c060503 69
    0x52006850031040203540c601c0d003278001904102c1c2041c00700c4d00a010100c00210034416454444074001c04a01410101080d064503180401b5400301164170034241c0c0a0002c00005080c40e02d0740f10070b4541b904188050f00710903c11a603648088280391307000071164210700296410b045600c0001022004100d0801045142c041d2000c01c4440c0304021304050352302c254440511543c030a00d0605860f0300c4204400448a54002032440b28052540c8903040b500d108800021841500204000c011500e0f1054040c0c6403518046040e0040c02c151201c010402d100031458401080043c0500294144a080604800c1c0e04000800c421a01100f0602e80103135248036040300094a1481218a0940c0440b040350250500c0c0c0d00c02c81c0f428070500c400800700545010000b88280612104281d00c5124904c40f0025a4034000a903a4a00045404002081d20054100003144211104d202401c1c50004080b6207100c04019062540d0301c00c0c0d101d68146980041c114003480341654101d0054034044c0b820a2840c00e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 770225134 1250 770223884 770223899
    0x9240f070308070c172a06010e0f070e0f1f020d080a090b0105041a03070e012301020d0e151308010605031f020c100c0c0b060907050f030a060f03080403120504 70
    0x448005c00c03420b8001c0c00050603449032015440203441e01100c0349200c030081003c1040b854544c0420704c61180002e0141001c10b0b05009100c4890b441120386980740b044540800e010400215011041030360040465940380b00c04412520f18401e00c1c20f100c1d002007100450a03c0003d101401c000c0c02c2420540c502851130001503103043d5507a0440d181100d0214041e0320100100c402c1d01d0b024443d055044c4a00400011902450003913541200d82c41e01e16441ca0104910b140c0100000710481280140c1007403a011007070500503e00d5485118001e802a031104070f05131054030155011492456a000c2c00030010081c4140c240228006020180c000d0320b545500726003030441c8507142003401840d003031b008100a4003c240400c18001510552401441410700c03008000d028140462403d4030300b880b0000000781d80d418500002d9000d175405a80d55841d100302030b03000c0012608040c10010015407030b4900001d0460a030269200a1801100450782c2e03185181303084092040900751036024000c045c002000580c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 770226384 1250 770225134 770225153
    0x605151b0d0f05090a05041d010b0114091c080d0b0316080d0f031b030f0e070b4e0f0601050d090812010609140102011109240f070308070c 61
    0x860b190b0a00503114072050000507400d110755048540c2052402203140b070340d96180502c104065074040000c02504010800444050030600c0001c120706038100581701690500c00400368081f9000c848030320580140da88d0b84000c552210642024954507000111958a824409901c204c20844c10501070b107071810900c5603c4003030709101603080c003481c1d00d01808070500030740192036003002d0034104400c0e1440401024004181000060b4850741c50104181c40400f00041c1a00541e81c50701c00107400c000d449400c50390240d417401c0410451b0b076180307170180f004204420200052291070755010144030140003107503840402c005001c0a00c0d51610b406018050340c1120450703180000005000c40d0003010740c02d1001c43c9220380184c140c440719a16000117491345c0c2c050762200a5682003071000000c00441c000481c26078114008000a4540810002c000391130704103807203201b600f0300030302d2240d030701482c240284d1b06034105c02407101c903100002615504040c1d2112000c0c3e8013011905001d040d14030180c03900c8048 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 770227634 1250 770226384 770226407
    0x11d010b0f2b020102031204051b2202030c0c0102040e0117030a0918091e06060501090305060a0f0902100302091906080609040503040b270427060605151b0d 69
    0x42c1d802e444500803d40e4400e00450304078801610401c2d0843c141490800c0e0303102e4009440a01c0d0740b41c0817a041502d0b140c02c8030540c0100d0030111400e1144040c2ea0340880003540007034240034020104111000c000c503801c1c00904000d161400d5462005e41c90909040c0d41d166210303000001d42d8204010588542d42c0100f0441c06072a9051918040c00c1008a07080005110000018012a0849000f5040147c01d403280342e440c24400c10050001c6a900e40054842500600005009412410028803c1041c1e5400451642109900810001850780200b1001c005600072580000d400095080341d03400c2c0811203404040201d42e0071a040c5c4e03e49040203041c40c10142c01c0da4822103844003c00c2c00c2c06810001e0350007901450032590340e10038114480c4c1e4600400012008400b00b401841d511161916220b00d00d800000d0150700c94017041d06001c045020380087c0e5048941c3c40c4d0f58403003c41d035511100c0f000200dd410b50f2082541d27440c1040054900340b5a1402c034440e00c1d901c50f842203005a03034007401c0145c5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 770228884 1250 770227634 770227699
    0xf010b1209012c12190507050111030f010611060f040b090a060614011202032e0e010f08010b09061c0f0b07170901060302010f11011d010b0f 62
    0x19403103503180c1c00d02500384054600b000240303502d06207007001c0c112500c0b20b540d03000380011a8100740001241d51518080c01003101007910000e103550002c1c03030046000300301c058030480000840e01c01c046681015a0000d07160013030002503c100501140c1c0d00009020180600e601c0281890315101d20310b041c2c0e9803c0188010b110161843c00304081010422a00d926694031030b03400e110311510780480a508540312809035000880d240b12a041e68003891013240d0041c0450b0070200941ca00404404252070352581ca00e01201900c29000602290b80003c0d40b07018000e00040c00000c28604807004bc2920240140507115104a0042c443c096079002030351805005849070b684500c04240c2000064001301d40b00c084c080c55200010045c001e0390242840a04082540d0425031545502c2c0c1184e007203c0880c003000740400c584180e214002c90240703800005042810001042e01020300c06101d61140241180c00e140769161000510146002d0028a1003c0810368a41d425030001502d5030b61180000010070302d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 770230134 1250 770228884 770228917
    0x30d090804150c080a0c02012c1801050a15050408010204060207170c0d021e0303070602070c0f080a02060d0e0f071a090a09380906090403020d030e190c09050f010b 72
    0x71640101e500c4401310b109c00b13201c41403445050824001401c501010184642c0021042010444244100d41c1c141d0780c000e071102c44607500701686403e5421400d40701e0390a00200780030001d4000d000b4001803025060960240103018174251310b0000e04100140030070115005a80369070402d49500c407030f242c000c6070102c502d06400c09014000003100c21000c040903806000c001500c1c803e12406030006c140d010700c2074201c82031007542c509801c089104580946030813034024104403409443e0040c041c10070407101c14000540825000f07412072810188070132508175a0403d0008100e44c1c3c41421261158148649000d80750080c040c1c0000d05c81011401101da02d246d4a0640c40d100f0004405040003003c1806a10810030306072501500c0ca100101c508103226002850009180d420422401030042da4140c00500608528080a030094283c00d243c0450034800d01d074003a40d0381c003046a21010001c0c040d0131011002810a4100800d031200141340380d52020008004000d80d1181604440751040340f401c541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 770231384 1250 770230134 770230157
    0x306060f030f20040302212a04090317011401020a1e0f0b0109060603060302010e0d0311031c0b1905090a060315050a0e0f061602030d090804150c080a 66
    0x1400200003e0202c0c0c510722038940750000303e20341c2850052040d01c0c0200c994010184d84c80642030080054152650b40680080301c24200030140d586c0e40d000030744842006030080c170070b500002c601181d21b100d4042e40012480800115001042c000440c01340c51400030170105081c0010003c0c0d030790052448001c0c030343e081c181e05c0d24141484550140c10f019612004010303950040d400c2541151500b802840300091902c200050041d000b84078580031243e068640707281546855007000b9065000c504190213101c860007101881c80c10903c0200b49406095144098800c005680c035412541c040f05814001c1d01c03c0401c0c9580900d41e103205604030744017202d82124903a030f800000c601400d040e41c002080c2c0d05841244000080700c42c0c121398814074010308100080c04984840a41d2802403003880840e80d04218041982040078004840203401580100c0f03180001020341754040341c41e00c0900341c80070740c000308083c4001081000c07240d1034500741d0718144d1390000440d100c1d0700031031040700c2c060001d100340f5905c03d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 770232634 1250 770231384 770231411
    0x160b07051c05090315090a0305030402120105010608070207050906130c051303050a0b090102160b0a0b06070b06120703080d0527010c03200301090b04090210021c0306060f03 76
    0x11034404441d0a00c0c18115000060000350094010711007440c07083c000c120100302802c90007801d00344140700b0307000104200480b90b10180c1d101ea0025000b603800c50f001004440280200f400394600820b159900c0d50f40070f150902c402030800304181c0100303216071041720038412903541ba04100c0c030714060003000c002000d50100000751075a228161460041c5d140110b40003080c003e0209100803020f001e809024195512209503d080344074801e504082c0d0345103da0000d01003405d40c0407440c0d0245500034000707448603040c000920140c001c0002120408501401c1241508040c07942c03420400c0024000d081c0f541c210342d900d4195010303998503440030035551000620340340016175440b8142441c5003001c0d201c0303610303107980c6a0207000703c020000c0100b800c2c80018000c0d038003600185c6074840c0e0700d8043e190559007000c21300e030050000c101c2442c3e445a15019080c015a940d94070311a001c2410350000e1202d03407519080809110225107010341454540b031001c11106802c042420403540481c540011244c044101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 770233884 1250 770232634 770232643
    0x702210129011701080316050f010908040906080a020d06020d1407080a06060203030c070201081b033310032c03040e09030915130510030518160b0705 66
    0x20740c545044003803040c0607001c0841c84044500082a650340d41500311a040c4141151402e01c2501e00d1a88100003030038030506001c06034150f56106605030b95207100d40710074460075160500030035180c54000060070000c075841ca00c00c800c0149804e402510320502d5540000340c2d0041c0218000e0038a540001d048810700c05c899001000d0f8074440c140d01c424a040c8220000d0041d4021034041000e1407900d5000f05003a400001030720322844031811201d2616010342d004581e2400702406071881a80c0c2113140c80c1540503950090345c8120480810300b154040380e9695610035554520182c076070824150000c1e55651500c40448507480c0d158203000c2422403001c840410000c9007040e42200d001c45c2c1c0903242190450100040048411200b03c00d80c913600c848030380648910802c460aa8800c02100072490710300c00e60070146c942c10700c0c084074804880386d0740d0000c9005044a24440c0000035940c20802008c80032045070640d200041c40300a0403401c01c00184c00401d44403500686140a81c081a1142081400c12 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 770235134 1250 770233884 770233901
    0x30402060c0111040b0d18121101021c02090907091d2805090d26190c1206091802460506030702120904060e090610090207022101 57
    0x40042d959170741e11051076000307070840f48804e50150b00340040084c2c0711144022040e151030304400c0d80c100003000240141c80c4190f030740420589954090200e01020801e5206e482c2086030660005692000e06904100c0d0421009241c0000d1048810003070140d0360012041401c07000100d0040046501d846150b08400f0000040848102c1ca2011000e00c81484503000207000302031000c2104c0c0b44401c0e816050f9010b4001034042001082d95058103200100d503c4901ca4005550901801c828401c4500030001c1e1015400120049412480811032081441c400e1200504407580104021001c0c5516041150b80c02c110181c03003500f02142101c0321180a01d0b40c0c040512071109022141101c000ba1045009242100c4502507101d8550004e4541040400c60344075100c0c0790301070510700c0802060442e190300014a89a006965050013207080500c81000500030f95200c1d0081000f45002031000c1201922508440701c402c0c01030080a00603196102c1d061a03c0002004440700100300a00712801440c108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 770236384 1250 770235134 770235161
    0xa0e0109080607031508010e0316020103110f0c0601060c020d0308060a0914040b0106020a030801170a02060c0102120907180209190608040302060702030301030c030201110f1614090903030402060c01 87
    0x200284030076640c00d5800007602e081c02d06817400c0215901d482c0d4500f00d42c00700b10510001d8008028141242300784222403801c4502c141000070b909003183c0090801d83c2c100c9942e051800c0340c001402802c040c0d0402c40117005080d5850321042c1404540d01090240001e400000c4c20300c050640852b54946e2004032510152011200c10080c807121810208030700c0b0020360b010343e000e154510010585520100d600c076003003a0591038a00745640782000d070300d2800c0c060340959445809080c1001d4010303640c1c200103102c1e64110700300140e203440070724002d048030070310180c1000c0107a8002c0714208000401c0088005810015403001611000484003050400724000307800141640c00850100d5400c0d000300540703000354000e600300d40071550f41c050240d03582e10081c0006400011040010801503120f6201031907203000c8903040d507e884c0b0444c202c05140c84c2070680ea049000840c1d2000780904601070200040410089529143c0c0e82444603040d9242d100c0944003074000d40c00095001c1462809402070030300d502c401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 770237634 1250 770236384 770236393
    0x8041e0b0309100b0a050f190801050f070e09010e07180b0f04030b0705090616080c1501080d020303100e04020102074407060f110604080a02120f0a0e010908 69
    0x408942c503191919081083d880510f401e034015840e090100c81c41d020303100040e00c045c8004d08000100840c4504031843c50951880c48000412041350a0288901500c041014075217242040b00010744500f034500601d038020b0f100d881c0100300300c14501c090b003a00140c20342030544600b5a40302c81c4201010705900b02c00da42400004442c40c0799116100107100b00c9000b00c1844c031032031712410422030352889622a40c0b640f0130b50600c440a00b40000002805010740b0404041e450415001c04190070310940c62002c20305d00c40000010000315005000c1c540300000c06101442c514a000c21a0b422007500600643c1c41108500000804690080140402410a0342c05807429202c2d0035050700e0711080c1d22030443d0390100c3c480e05401c0c0c0400c0700403451154114050040e01215042260441d41040c1004203402000003800c40d2114802003401007500441c040c2e21500d603560860a00a45051403032410508040410884021910444400e540d0000f60514002c5032401c4a800102c130420716a03000760185009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 770238884 1250 770237634 770237641
    0xb0316080a031404080304091a09131403070b0412050f19021b01020c0f0a0909080414090906040f0c0e09060a0e0601060207031103070b0307080702060a0908041e0b03 73
    0x200001d8050649200f82d03582014240382c00c0301110640100d10541030305500500081c40750761442e4101c0701110b0346417a4050390b0042d45000044642406503050a45000c19a40300000d1007440c108404003420701e14000c0d0300d000d00c1540c070b10340180401032000d000c0f003038002e030f04410540c4140211410840780703182d4180c5078026051089505001c5414003000742c424415240c8500d056600c2c6500c403500160082c2ca0361403041c0c41840081400c1244140d8000d84150000c6030036402d03841507410700b42c06000490380388d5081c00404c80c00b0009040d01c00303100d040081c0812541e07120000300c0d0ba90043c0d00031402192800b10f89005191500d69030022060800c2c0e11007000b891080004001e8410300c440541800700ba07015a84003900e403e0280140380040e08240d81c2400070607050707000c1400546000e0100c5034001d580f03505641c0181c1058800c0030014a0180500c190380341d040000c66000400520108001d8011b55200850b0388518403488160092101c0070003905480f690591000b050085600c0d0354074035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 770240134 1250 770238884 770238899
    0x603061c08040503011b03051501080708070e0a090c17040f120c20102a02030c0301050f071409090417070c030305042d05010c0c0b07030e0a06020607120b0316 70
    0x9403145101c100207890040003030500c1020080300c107242a2706844120580d00d6403042203d41a60081c04207081c40b545140c035104949400c030b20365000300b070403800000d4581e0400c03030010f00350410701500c0014110401c080c480071822074030380d0041c0654440c0c0740c0c06130700000001c20394101d01005009090380106e07600c0001081c10414080380c6031601180c500310340343e205500a031440340005000c9061005481e020003504104400c203041b501e40000d0403501201003542c0081e007965000c54001c08100014018424004c0d0050300c503d15041c9040c11031828520000c000c82c00c036810051001d031500401d1881081b0307824401044546240e00006200851602e900b80685030f40e0252140f51910450f030300c620319088401040c103404030850803015584a900e4140111480c07407a4003800d0310300284019000400e445c85200500d0316520a44400b0451711300b00042151212840d801513081d0b40140c4100001c0f103030b1020080d110911004800103440341d0042c0401c3c90030762a00d8110300c10340040c800108010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 770241384 1250 770240134 770240171
    0xc05100e060709060215150a081b01030c0519051608070f12020f150c1308011e060810092111060901090c030f0302031e07020f0603061c0804050301 65
    0x40390b464075a51000b50381c0e840100c2e0307940c03407080e4002c500c07a07101c1010404040540c0710249014a0050042c40ba03036413a0f21800741484420030310307001c518000214560707255030180118400061607003412420801d0080750390340d19410b1301707034104200400012107207015030030202d0f0701e60902d4120030b21503101c190914101005407001402030b121300c83c40c0660b2429061000525108038032113240a840480e07051601c194190f10041d000351103100003031162408007481000c0c560024688200082044070507644034140c8130440c01241013000d4200300b4144501180000c00e80e603000c00c254000110300c1454100800000d4032042c3d000081d5404804503402207a011002c044a031501384281c4601d074884122040c200c81680000401714520741c20100302184044050520702070181c01075a1070055030120b000300721680e00d1181c07506028085010800e40c241211558007040054030010324500740040003550440c420082c1e180c409200a071804200007414040c0c800822001d402072040e9003031040c2c90040c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 770242634 1250 770241384 770241391
    0x1303080706060b0310090e0c2e0801030317100902042607080a02100c0f0c17010606120e010204050316031209060e04020702190b03010609061107060c05100e06 70
    0xc081c00d00c01c01040280f0f4040840b40201c08422041d0744203071800701408064404001703190700c02d020302070300c0348120b458807400c0d0000e0820381d101c1445146510381070722006402e001c0d041d9042008804c01440001d03013001c04d2140000d0380c1042c4a4482c0e4810703030b46003d20030302c98000000a90001c1400140ca0349032880001811550101000101280f41011690b80d80d46208200e0168003400b641f0015060886400010305900e18103104d50364000c1c0c54000e424081258225850040d0f4ae0041101410601d201c0106008040090040e07915011300100151150b0b480101402da0341d18480e071800c0380c00d6044500909018081d9103400109a9001030001401d110682c0c1d51440111580325017032182982005440d6144c440a422207030000500000b03400900d81260071607414500c003c0c404191038496802046540d40040d40d035130500e14010850b200d035a10130300600c54106e8000303a050740082114820f448651510034111500d904020741f40c140d20104002070b492074135410600340400070548920 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 770243884 1250 770242634 770242643
    0xe0f10120e0c030c0103020702011407150e0d080c1b06090105042a060e06070b1302030712020105070f08040506030c090108061804121413030204050c0f070b0c13030807 74
    0x200901c251140c40d0003074024919895040085051002d40c001d42c040d21030b02e8010b00d030090300c0010700e03813545205a200c410107451821807807048080008440c003c2114180494010744018038000101820104024140c0c1c541000d022403503408242070784e0a0882c0c5948400121582800c0c541d11aa0007048141ca080d200001140310708204c6d0981c0740341c0e20102c640d40e02d0039280703200c0c50b042c030031940501301d000f003207911460811100001c10b0b1115a110f000b0042c40c02187c92080e140d01c101407030900194020700101e000e0070588000350382c001d401d603445d00d50040a12410000186070062991089800560380030030f000c0305000070a80f01d0405069480e034282c841d540c16464880400c1814445021807510303103074103140018001040b108114030308001c1820640002c0103200e1000382d8940004a0700305001401020030002d41c60035008440d001412039060070310700700503a030300c3e2481072062004c00382510038804042800002c1c0c0da401c5640d05200e09903003540c0300d5280c2c5450600e603842400243d0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 770245134 1250 770243884 770243891
    0x32a110a030e1c05070b0a03060306021206120c0d02060d0f0905070807081b100c05120706050f0103080f030714030a050f10060207090902060d02040e0f0708040507060e0f1012 77
    0x101d0fa41e41c40074185906508100205112498180304541980c05800b04008154a900b0000005599030015103103016885907013841c14071701107081c04012010724a042030690b2000c5c103032012035140c4458951480f44c040c3e94044d56100d002c0144401342c94203c4a17041c0f9140f50141190611102280050540e4010350680d0003407035454508a940e17007849141c00741024541c90070005246444821984110390504140d80d40c51101d4888038244500244075443c14403000602c2c07400c10246201d15a40072199944105007541140c0320782020340074556100809040c00400708a0050144d0001464040702407000f07907a0746403070440b01c2e001d000d081c3c604800305194031000c644400407206415055034620380c020f1411900d081c0b01c400284c070910009030780040b0108040600c2c0305090006101a02d52001800018108143c40c10507001000704500d0800c0f454a050000192010030010100d88940c6003404911101d100050341c03030700005c2031155103c030025000c0d40c84d460308084c800c02c2365020103c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 770246384 1250 770245134 770245159
    0xe1c24020306010215010e071215080609010f0204030f08030619031514040f0303150b18010e0102150604110d050727030222061505030108010c032a110a030e 69
    0xc0c01c1503820702130035410451100004075458840c5509001d84ea40392500860ad492442401c07541001b0135400c4441580c02800400103c11401d01941c0034212101200b1031406140d52100c0d81c410310040801408c0c40b0b400004203a80e1380c0d4251524034840901078486030b40a80d41d14000034a02901c080010031542410200109510580345071442690020541c40c191000c50740c0c12402060000021202e04283e00d5011440d003043d180a410000300090559401445039000540551540410241194030013281d040005004a0388103810200903100031500c2c00300800501100d004001c000e07400c2c98546803c01c9451a8801c1c10021425281c841d140b0810807145060fa01924880c0030181d0010a0203d01c80e002d5206143c003044014a81c03c000030340702d81c03a4a0391800e4078a50a208400140004c030052050179801c1c49041181121400c0030400300f940c64034180804005200f8285018200809800074103000f01030070301460203403600765800b42c401e51802400c1140d542c1c001d20302481200307500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 770247634 1250 770246384 770246413
    0x8060c2203050c04050709080109080310090b0d06090c03021513080f12341406040c051e040204091505090402011707021515100e1c240203060102 64
    0x1010070780e600074001d040c500b40d02d402032002900002d4050b02c200801805c001030314075002c0c400d140805100c2c451180d40c90a203002d100d500300c142da801c60040e10f072074400714014594400409150482c0d00040104210070b40e41031041501c0c0980d88043d4101000400d403a2030f0661080007815000325000d040050705440f2112983d580c071a5078040c80c2103134010300ba00041c01891201400e00070042c240e540d5000d16800014089903900c008000081080524806042200d020310b0403941c01103140040050703182a481c1d210400200d48621030042503d44140c0f10122111000c00085e0780e07000e0000d55039166a20a20b50080030742d201c810500904040c1c003c9500d180c820082c50150343c050352581e01c0805038601c0e080503110302400700015032154a00500b0003555000105200c1c91001004c81c015605402c1405492a10407400c0030811058020150240d620b945c1d0b10340c8d00c00d181c081c18500105061814407600c04881d810f01014401704031218000010940040d1f1180d4400c0e400d0303400b440c00b403141c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 770248884 1250 770247634 770247697
    0x2a0c02010207051302041502030a08070f090509091603031d010c020603220f0c03030e030606300136081204170c1c230c030408060c 58
    0x3030041e040301d00100540e01d801319000c110f04a00d84e0380145020b80d510307083d000300c42880c100200507800100b9540b0a0a0300002807550103c8141840c0c0a45140c02d1030003400488140a010311179516040070071003914003009860000721003d100700d251903031a410054046041000c1e00c0e00078545d016000d0505500c9510300c0462a1b40c090000e0f411a11868400300c9280c0c4103100c20407403d00400304500108513a00404003140d80a1f5101303803031080c110f040084c0015241030781503000f03501c04014800141c85501038038100c030885c00c6454000742210410100c00109549080075107600f81984860700004410040105002e1910740d40b8001242084e204605a1203020203089014148030307403001d100a40006650240c0f0075114104c541e144180444010f400c019085405507220380e130840c00c1c2c6115100c080c25800c02c90304200101e8040100d030b030380c45c40d400007035482103119004c902e4002c2c0c0c007000c0003950040d180300030988905140c10165140c60750000c581c90b48644450304003e1484441104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 770250134 1250 770248884 770248907
    0x210020d0e060c0c060406030e01150302130b030f160e06010f050d050c09090f0403030515031e03070b01080d0f031a041d030d0c0e0901050d0210030603062a 69
    0x1207840042541d520704000e140e80200d941c494240c001c214616a0940d91200144090704481d01c001074a50304041849084410100c004900042405403e00150391080d102031505107c49401040c5c613060000404d0810b030b03803008502034900c120b0640100040da00e449100540b01540c01c00c1d10107a6034100112584000045044003084040040d1303e82c1140701d410880c2e0080c0310b80c0050f4a010365000c00b244180c1c000b12140149400c080f030034001007503850700a50f41c00c0a0107041140c2040b152200107034403110041055040d01c8120703103100f4074151061040c0c0341d00e83c1c0c2015a100c201d40c1d44001c00e0341c80d101c003042800c0020300140c0104150300d00a20401180c90710b8035890b450400514400c0c00010301c040d02421003001c0e101a1070403200c0034200b0041818101410000c2185245c003403014000400312070b94076124201c02e1005001076129410580d00883c0c0480740c1d03401501c07141409500420081d00050704e1035082c10359510340117072b0f8851000500c8410303a43e00045010441c40480c0d0614403030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 770251384 1250 770250134 770250137
    0x1d15090c10050a02070f060302070b090106030b01140f04050408070302070807030f0b18101e050108030703051b06010f1a1e090301060803030f06010810060507151d0a0210020d 77
    0x30607616915a1061002c0d01c080042401200d080c03e88034003441400320120341c07000c40043e0300000d035103040055110103660000f0040c4024410ba50441d684c0c101c511230305025072103001c0600b01010985659503180c403461100050010001424542408441507020000c154050701c5403200000e8041d0300004c0001c2101e8000010254503050b640d14541c8401001d403500030704c0030b000741002001c0300d802e002d18103040e0043c10000640300780c000c440755602c0500800d000000307461f001c01044103040110488126036414030f403c070790300c01c00181ea64015034000d6124039902e115440010501c54440c104620640d1001000304046007110419421580308141d0340f0001c1140c8040c0c0041102200c0002c0d007450403000340003194003500d8440e4640313160002c5500204605020f014000301c0d5070802003040d04502e071100328200d0325007025005800d074851a18014000203140201100160282c2c0c01280f06034420603071070380005500021b190350707000c58610907407290800c00880c43c1000e00019040340c4840f001d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 770252634 1250 770251384 770251399
    0x2090f0306040b040f0c210507050409170304022101020c10050402061911010f05060a05030c1c02010e04020a030219020102191101020c07080a051b150d1d15090c 71
    0x395030300c81e0480030740805c0c1182d210709484004a00804541c0e004c607030b00e100c4c5501080b103094090410078a8180180d00c6140210315040d0800c02150000b00140d50301418a80383c00e07526203442c40441e981d036114a030440c081c1100110592a8070384103400a24491a541044880c91780320303d40107034104c980541d802540010f04006181a40f50410202c040700a07190074203182507006031608074252040054000c00080d591030801c42e1030b1a1550b4803402a000a900420f06800c0700307400b0800810500c000c0b0301400400e01e400f1811a8031650010000360005041591501c03489203019029410445207810f0a0488440131007010380305100380d80101ca4a49a001c0c0311100385141aa60144080914603803550208007500200c40e0801019000300700420050988102d203041041c244072000d8403811061021420140290741c41506199500d0b10141516580f040314403d8a030040116900c0748008482e24004184d42250201e84d1214282034004992056902e400c842030b10b4044040d20f09901406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 770253884 1250 770252634 770252641
    0x10b0c0f010c09050f030124030302011406010801170f0321150604050d0203010f0c1e05030c030f060f041406041d030406141b06040c0602031602040e1f02090f0306040b 74
    0x106610300717029400d009400003035034001804081c02990b4001581c0d00c110510200c08004050382486500f4448d0000a0304d08180e042c01c3c80000c00c1c2c001c0600c2080040c1c1444407804031804014400c107299190f4250490341d594441d01072600e4049075034000610808240c0c0001101c0c41f00a8841c1c055042c80184002e01d002c2c104001c1044804020b402a601990707504014140da01a034801d64415408544a500c0044d9021040743c0c0c2096091035024200103080c070510412180f90025250001c0c0c0141e81c1c0307000c1d580e03010042400050000307103242d40181481700e210301c150800400c15000d03000c1505c0034461846d9041d1030712074a00420b00c11305031380d07401013000700310161040031401078078031503020154074141d00c01c0d410301032080520780142c2281e0400010300c0104405043c11000508050000c0c6080450b0396256001d52050fa0b4000317801280c4403130b90002024010700c0002d0f0602074510601041001105003032009400003075400f4012008807421042d58500080d141d40329503444605482c0584c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 770255134 1250 770253884 770253889
    0x3030306010c06020f0d09110406060c0c1a09041b1107060c1e050a03050c06100e040212010608010e0304090f05010509070e031501091506031808030408090405010b0c0f010c0905 78
    0x42c4003000f56100001c080c0b14082440c074940c040d04c0c1e87c07940185100300b0030052110070042200c132203a12000c18000803601150005980441c100c0841d00c00306079582da040301c04006101541b0407040340b80e42c02450b00003440042820b02c8404c1380c140d0350b5a070b02e068400740e410b002c41c0d50341c000e0f40c05140b0115101d009000005959000f9040008154102d10104050166255880c2c40b074180001c0303010800204005128007410081c140d40091100d6101d501140340c540c980031002c00250029000324000c605030130000074250884001444810000c11403a41c4030524030f0303100d0b0130500484010f9800c1c0790104400c501e1500a00d41079840091511031551544c000540d0100c2401024a405001d85444510054141d145c940c1c020003078030704003042c0c1d078bc100001420710400607008042070601e015043d0000c072884487c220364143d40180036543d2910b41d424221058055010815806401c00001044036420b10700607041940400b812141d240c4080d610003401c6e40d441000407400188508810444d03032 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 770256384 1250 770255134 770255137
    0x90309150207031e140f0c0d02100e01030b12280308070c1704091d16170f0609162921010b03061806091614070b100503030306010c0602 60
    0x440340c00024403244070442e030710440d011080b0b05c814030050b004034034410300e40e580c24404447d1000c004c4482d00702174166a0b000801d003400d044640c1040180d5664010300300d03402a408018181c900509072504c1d61411070100e9550404090074101c2c0c075007407012000190703001010804c0e0040c0d058403a10641e5030b0742141180c4405408a00b50307404103203000c01d15a4880c04000510180814020202e80e403400c200c403e0f03c203441054a031620079030010340300042e40502200c45038107840702100c0240418440c40940c0340f500070714200d00b03030490044100b40701044000042d519400140b8001140501d9541c05000070010030000700128181680082c0c00d00c0405010000d0181100d00c0390350200d84001c090105003400c0c07090300840401400002031160303d151054084034210003411410301e21745030240101d104240c01800030310324642c001840e21100b600400190099010682181c0d86034207141c01d00b503800010986841c2600d0311a000c010403d8100401240d210b000306031186071051585660b4040213 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 770257634 1250 770256384 770256413
    0xf0302071d1605090a0303080a0f1802030d020d2109080c0c0f1c022b0b0f240d03021606090905090102090a1707150309030915020703 59
    0x118052100045209640c0c604030060040c08150003103050b24000000310325000d500c0b1031440900200780001c1219a450749034a00c25a41d251400e031401d51507481e80705010b440c000e888404250b0404151003540041e019400302982d000b03c0440d03000540c604c0d4266191100c024140c000218400100c000600320f041c0d041280202001e00024206c00c141c0f0b420809410001d4a46041c3c0c010b10314030b85c6107290020203640214002c603483c3d01510640d4052500003103000b10002c1c000d5050781c27690896402d4141c00c02070300c40701c02c10b0b011011042524144500d40d00031104c1c1703095811040b01043c2c901503c0160543c12001c1c5511888001d400307071040124038020040105e045105803007520324201402c9070003400802c015150b03000124284070503801600c50080c4040703010b80c03043c0030a981d01e039900c0110b10211041100c02820002d80000100c0c10108942c001c400180044041114003030b038543e005081c518000e40d0340070344c40c907150030100314a1880500c00e44010713404140103102240342c400300c1405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 770258884 1250 770257634 770257637
    0x2030609012102060a020a02090f0925270614100309300801150507030c060605100e031005010e0601050c011e021b0c010c03110c0910060e0103050c070f03 68
    0x1003075040354005441680b05444440060b001f0810920441c20701850098001408582048a0b860411406907580050b0302d03c070281180084611500001c0c041c0c1214050144000c20502002070318064110200110541a00c048c0c03804000042040c00d9403c031039118500100300d0380064610a0048024180c1c80c03e068031100704036036501d07404643c1d05d4030440024880c01a03612307080e851244003400c2241d050780b0000364204010400500103520500700e4660940c503003851640400a1305103280141000d41186400034001d08200c05540e8201001e4540c000341182240c00c1442589000025074900781308801c00e030084c66000c22110740c0a0300180510489000c0001180c5242c1c0c110405152050141c507075a160780011050030000300b003042415103141c441c0080c107440b043c00740024403207240d031100941000032f183d1295050764810700c40703001c0b00800202411041c0c10202c020315000301d860312840d800318021400580b410750280c0500c2303114501c0012400c0c1403031520748a1000007900800207c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 770260134 1250 770258884 770258939
    0x30905010509132f07020f220f020415021501050405060f0a031a1b0a030c031b0314070e0904020910031a1501091211060904020d0902130203060901 65
    0x1c840f0452280d0100003100d034140c00c49440007005002c1c0303611660080c4100140007040f8800240e21400e040c0a4111416124002000d81c06075a4880144012070008201c50409202030032008041d000b41054803810401a04100c1054906aa41d0340c025a10780c0d85c40c8007244010000b900d00b541c000f40e400403000d00f51490b4403441c1800a100082160012035101c00784403204150070034074a01c4142d12500c14170075950043c1e1b04241032031482c090480d00008051b1030300101c21300140b00350132104184008064011000c2c0c0241c0014024061402c81c480c80700d04d9090010303041c184210100b1030201000303030070710076291555020322080200080c480248034801e0140000040d0554024500582e1558100e005078181908980640c0c00b500d541c103810044400c10a200f03841c42201039440c41b5a2048210034140c100340c01040f41801002122540f0500c0405e415001c02c0c1950403620704548200e4030000e11008070a04e44040b40001c1d50444d81161411005201d04503061130514042000f02c004203 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 770261384 1250 770260134 770260159
    0x11040f030302011d2d2d060c0322050708060f150612190b060417100204061b050307021309050d03271a0703051909030905010509 57
    0x50401151035801200140c1d5a14001c0d031180002c03018400880300300c1d0000e801100c16079404072611940301109080341d02c401c1c200031411003a0812143d43e90104498420703d0034030090389041c480103140c0010004a00840d00021102503454085a1003070b0b0071864225500c855500c407a4110a00a0745d0880d154480c1c101c0c04952104208200da03c2490011010150b0b4544001d011400413410456240030748014440180b040300a4074005a100a20b07604604480050701c100001808607504500c1e00800005804500c21a011580c46500080c120496010014126100049100d24440c080000c0d22240000410130101001030100b240188112801d214131900040ca0341c00147c192509103681c0c450198080001c10300000489001d1418200124142c0122060900040003908420459140d03400b00820101600913007214410481c05105441c01580141c014a4241c1b00140e03c1140207a05101d408440c2c010f00010542c195035071000c0e80d190000640e03082d0400407203103074420302e5038804 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 770262634 1250 770261384 770261399
    0xe130611030112030f020615010305040f02041406030c0a03050c0402030c130b0a080112031d0a0b030907030605130f0b0a020f07200d050304121406040507361104 71
    0x180d400380400c01c00d1415041d01038134000d0480d10b898400d0f442950004810044408030258008101c140300f82004a555a16854007010801c0c4111b4002d61081c90320f441c954081c034005031814403c04040d000c48804050704400c20400b103401e480010b1a44e40502a07000140c2030903000345800005c603208290810a0400d1000e92804407900106403035030300440c0c03214580e9844603420b40140640000140e0941c1c003074170000d00751a1243c540c1908000f038542c0000d0540c55015069004085a0100607141e0030300720511500c4020354403090300c2040c2814049003050104401c10940369500640407110421250b4541d024600001c100711030090f402e101c2805100d08150090030210f2240d1006888449004030074025600006880c1d80a14090f4602e06c000400000c201d9080d110907042c10f040091607031918451000a110303c48103540141b400b8041001030004519007651a0f00b040301d20040300400f01d914000b070203000394800c011003c01c0c0c032282200303456100714081034031091800e2510b9200c03d00e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 770263884 1250 770262634 770262637
    0xd030e0d050a0308180d36050306060111031b010914060f09010501060e04021804060305031201050609090109050411100f14040302010c020918060a051503070e130611 73
    0x703844941080e9007000425503c0f04030075a22149807000704140321200e00786a6a07600e014042c0b4070511a00c1c00b80d55403c18026040442900b02d040034010010f80c204540b0314007581d03188240340c024490700001c101d0a60054400fa090900e00d800114103114001603070300310b60752641840c2c0f5265503031000d0710004a80c01c01e04450722484280d0042140303040081c80322401c07040c02040c512050349400b005000786030b8410ac150003940c900f2a40980c40d4400d1500300d207940710458200c3c0d6803151801c1c0c070000c100f140110142c84d003044120070352440c070380e42e07101485414030400810075032145e0320a005000000070340e480150072902400300c064502410901107600a4512030144000c51500f03501110042c4e8404500d203115510304211508281c038590002c1c01711102888001d01c0b814040c0002603820100c0c04103040e01116000484529081c07207181040100f03400e50328440f5a000102e5050510305000402104654201151b03020980e01c19900c00d6400102c581c1c129542ca072107489040c0507020050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 770265134 1250 770263884 770263909
    0x70f02030607032901050a0c0614010305150906070e090a0b2d03071212120204090515120a08090d0501050114011106010f061d04140109290d030e 64
    0x2100054500c0c100f041c200d1131888840c06200100e2098415060240d9000c019600d4200d40c07030409a41025040c41c2450150180c12050600345280d0800041403100008a140d80071112010422590b1500100207031513a10848019020a506d4075a105890401e640300d00c1d0300030469440040d01d60070010001c0d4102d041a01c0e029980c500c01645550f030b04030000c42c40101c1c20000c03002080300380d182c90316400c00c508001c1000340c040641201c030b40300c60b20302500f00486000d640d00c004656580d00d40d4085001030105580d0314050031101c100103a414140000800c040a040345c008080b03c0b0240c1e034810b507842c7e100101c5550000e140302c18101c0003034824000e05000c0c01c8040e00704804004903500040800d105125045080c2d8016401080380b81081082d100507584140f401d0b40c10408c0c129906c1c6541044000403071f4115140a0b00301400743c02006009050f110030103800d005100c8000d45001454000d0b501b805109038006c0c55000607450000440150207201e401c010701800071450000f0101000c8a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 770266384 1250 770265134 770265137
    0xd030e030d08040203070f1404180c0305060901150b120a0f14090f010c051e040b04290c120d0e06010803070506060105040e043003060305160e0408070f02030607 71
    0x2001d200462401b44241d00140c4040f0701341c00c840510302508000095040514a809244d560b0354450f044948000c0303006960360014407100400c0d40d245401c80c3c0e034450868006080d546042d50070348446091980e118121072020155500b8031132070311b00c24030031081c0c080e00d00c801d1740b0350350404080c80c00311f140101401500211084d5412b490003440290410403070046088169251010b1008000d808c6410780d00340c80452240054220140c101804c2e562160385c06c00d100209010900040c4640904600b03105020811080c4084d00315484c4400014041c1c108000c0707254200711502c1c04808503a0303002d03101440308841301060f10350242d03ca8500302802a042041207810000d0b0000500c442044155044a402e1810303510b024900041300981c00c80141000b4001f000d000d0b0071a01002c075100360a01100c140c4007078030109a011050180040002e440100c07414028030f0710080354a80142d01000444030418034080256030789660300d101540c05448221a107100402c007110150301c040040780c1c8200002d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 770267634 1250 770266384 770266397
    0x7080c0301050606250507030f060509010b0108040209071803080a0203040609120b0106080c1b0d0e04060803092101060803030103020f060304050c060c010e0a0b07090b04080c0d030e030d 82
    0x140038182562401042640a403104000c40c2d405060b0190030b0b405043c0100419480070b0a035858243c1c2400b40a50001e022034030400990b01c01e010b4190b00440c00f600c00d0500030010b9000c1c0c2401520800400c0b1000ba62140c2c04c0760002d0044e80c0103620354400c041c6a0712602118030740320390f00c0b813030a9001036440c680180e1000c6000d0021503040850440540100032500188242540e11300412001c140200420015042c012507000c01001d010f551000005502c12414800d03110402c655490305030071403c00090710401590300c68189849003c0c2500e03040806175240c10070309424480341c1c11103441c03510a100d1400000182c40102031091101410180c4080c56403945540104070310038500750640c41c441c1d10304209000010701c001454101c694400d40790386440d02140c250b0a401015500010041409510440001c01c10043c090610400b45c0d51a5003034450340341e40c10703c8080d01584c041d0005560012351880141c1c5888803a40f0495403180c0703030060b140100100800c0c1020040f07046c3d8408100c5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 770268884 1250 770267634 770267653
    0xe180f040308010e010803090402070f0602071208160206241f140c03180a0b0a0909050a0603030912081c150e060307051c060608100509060c040e070e030708 69
    0x18481d071101d00410001046130860b5051044241e120f10035071407094170490780010f0f06800c00c01c0341e8142004554101000319240c8441e81004000c0102002412000a5180001800c04059039000700440c0c41203a00031b203403d58502d807030000b11456219002006c0d5800c0360200c0f00350b613138101c82a00d80341c1b0b800c0001d519101078400050170381104504d41003d80f240500803807030884800400d5405200c1652890900200c051000c503200c101e0f9600940c0e007855001902d03030302041e00402440101c401e011401c000c00d945075601c7c40121200d030f000c01070025140040400c180400070f40f900002e14040c030300e010724103150740b0905010752409024001d03e840d29426103a03519440045100024014124a0385040c5020310000c0d0b2180c115004040c031603101c08004480646860301c80e1450b0329400041000328030b4a030495150b4504d08180c00d03285090511002070b032006004643c15018042d49203940b400d15041500b40d0aa10f80010050001c03c001e5060040c140e960402c0180e00030315031440903100c03002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 770270134 1250 770268884 770268887
    0xe03041e080d08010b071b0f09090b131721040c05010f14090618040c0207210f030f03090f081e0f030c13080114010e070309120e180f0403 61
    0x4021030280341c240a8040010045034100783c041355612680031051200c41c04600481021f1400580c01541c48090304140100e0900e600744d001c1d28096020303a400060a81d203840306074215415040c40184007504480518400b208010040c0460b4102e2a83c1c0000c000c0502c1d0703002a1144003140c0c265000404807008000c20f5800818810580d0802c1c5842030403c004c1d16041400c9104001c001c5008100014103840c010885103a2580c2c0110700400610546003800c4000355965042d000c0c0d40810100b64105d0045a040034800420459001e41401031170081500e0035500b1030300ea495078005150311446030074005140c040c01c0c1c1c0c007450301c00c0708200c0c1c480403406480030b500c010f5200014010706042101c1480c1401180560303a010007000c0034140e8031a014111841120016881700c5015800c25080300b000f000a01c0800d41038400506d200049135032640300031012381b80014005895406102500c004451003281c41e03424161000e071800644031440076004d200018100c2c1c0100c400e003003034010f010416 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 770271384 1250 770270134 770270143
    0x80705070b09010915020a0807270905060102060108070806041106070b09070608150f0f0d1202010506100c02060901120219020309130506030303180c0901081c210e03041e08 76
    0x5245c0e0b034214140b0301d9415000c1c01900028000c41d091000d51000007981a00e00030501c1c0303108151010380e50034540d5684485026200607141ca9015010b120f0000c00c0410300010494100d515140c0104100e44450325280c40f2145000085e0381c000908000b0107021843d10443d00d4064443d98008019140c5040380052011001504664140309075104020a650714000c107112002c80071201032100401400000781010700c210b070028492041440c203644003540641c086481400c0070f544140d01030b40340040c1203030304816040c0300961000c024001040e040d442000e07035040e04d180301000180f41c0130100244440003070802400c6e1300160710001ea050300f00c0c1401c001115801d42080e0082c81181050800280c07280001040c80e003000b00b950700c01c401042c404000c82e0044100180801d072441d61142d1240703860740000b4121049111307a0030f21004401d842400780f00780d00d096001e445510310981000270009000d00080e099501d100501020408032041e0001070504454407800d000794515004600c0c4c1003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 770272634 1250 770271384 770271413
    0xf080f06010b1615020d0903180509040c060e0d02221a010203030c13050d0b0f090c01090b07030e04020d02031807140904051914010b0f030c01080705070b090109 71
    0x482c40510090008000c950203500090798000413082144001e031491600a0103104a03404045080c108038000345a00410401900c921948401c0140d070b440f4000d010390031760180c600410030606000c007001a05c1c8141400c0c0900e08009008101814140e0001480d09503414589240d041082c1866000420607200e0710030740000c0007410188201c0354200107500d038040100002415000040c0c0c50010360181001d260281000030440c84810083c0d00705100101c20865041090800791004281d1011001503c803100f10f0050391440d40da241401164842d41d04090307011024007864080020307003640c641c0050b00902e1840c182c010f17281c0c508200701c0304800106c09031010300da4001c81c00501c20755200c01410184003406540034402a00c40e8a400d41c0341003a01ca80320000c0344c088141e074000b00050105c040c800c4410f80c1c8020301c40c000907141040050300d5500045c56140d400060741ca40300b54000c40380700d0ba00c402103080480c100122500c48007840c0300121262040c076503443c0b1040d0304001d40d04111507a1b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 770273884 1250 770272634 770272649
    0x90907140d1104110f04060807030c03140c0901030e0709200a08040807140303130c1e0512070b2b0924020409020f0304060b121b0402040f080f0601 65
    0x81c01c14003a150803101207600410180034980303600190280070003120032502c039115945000c0395165960b2000810381c40040c0c0315000000d06001c001c0c00414802c1c0101401403401405216103a200c02c0c9400400350f000c0e003c03141c18540c48100e0410700100c140200c1000704a103882c0400d520040702e80804415503100d41c1550340c00814080300000c158001c0a455005a00403040d9585140c0e40c100002c82d00c2c1d49640b54500b6100000810500401440e8404d0301d1030320402c510224140c5544440c0060311031484030350080424181c0800035480c1c405040600b101080c0242c3e005d042c1c03030700c0080c0c00c258401c03080c501c1010507040130303040544410320804291038286c1604104c80c10140c1d64001a4410500043c0041c6001c0043d01c0019400f65040b28020940440210340d2078070005100400c9400885e800c2c0d0340340385030600e10368081c02d044501c409a25026409800701e00d400d014640027243c105101986c000d54240000704800d080d070301c025000390400d6801010900c440b02900ca10340321050f0441d26 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 770275134 1250 770273884 770273899
    0x30908070b1e0c12030a0902010306090513020f0607060e0d12060b0403230613050c0a1a0309070b1209010e0109030e12150a05060a061107051e09090714 67
    0x241d140200c01d180024032601032016555806020700c3d0078500f48013040c400302d50039000401e00084a00950141e10028809e0702c0034031101c3e981d00f4450080352811520f00803000740552440006203000d810700d90000100403d44c071305208040d1074840884030600c007001d01c50b502016281000c0781d0880c109610089500038188041030801d01c4440050040c1c2c8402041c950f21304c85841d48012801841d100d840351490704803000b9113407500000c072000441920903101801a06411442e50608040802c00d4a8086003c11075150103190aa5115840144206400d000d044d8001c21401180c0c00205500305601c4030300d10303003400c20202080c00c40c0d003100d040b84a182c3c0b601440e180040d42060313600070f01c1c50046584043c00c1c50464910740c1007c0960411400100f064410040c03401c0b20f5600650090b501070303070720703080441e11854280e54500303940d40850943d82c087d80302009a8942000f6040c603004c42c0160906040b0800000308207000c030305403200b00481c1c0001e003040c44a52814403a1420085040f51040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 770276384 1250 770275134 770275147
    0x602121005090c0a09260105070f1d060301122102060a0506090405060103031818020d050c0f030a090c0519090b0303090604180b13050412140a03050601020118030908070b 75
    0x35043d1740481c41202d14284001d0700030001212013201d040c281c3c0c80c601000780590f103001c5400509400941c0303402404a0a940454107500e101070123414107410b0701908803480c507420320801d0b10002215072400c403801c1c050609070761107800d22290320030040e002c19001840542024071410b001d440c4010100c1c0e0041c00c002c0700f0803010903800101141141d405040a40e407410400700d001c80e078480701e500a95003000d170301b40250210f0310442d8014400a21050401c020b1274880c000185494490300002c411904000d001180c0281040c0e440030250a00c1501c00f100311359947c0d000700f542d1886849962201402e00740c0d08105111b600d0248100045d41140994600207031038001624600a500580655006901190880300c039246c0c0141982c80c001440c050071107a030130004a002d04000c035800c54006030214007081030349004449130310b80f03407090412407070030f040e00c0c0c4034104e00a200042980f8119901c0d0300404070161240f444210b40640070f5518030481c035040032032991819080d50310203440030301c003000034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 770277634 1250 770276384 770276387
    0xa060605010815030307030c030e0a0830030a02090103200309010e0c0102030703051b1c030c090f090209130608030d11210c0c0d050d050a0b011b0602121005090c0a 72
    0x102e525990349030620910390324490900726a21800d10ac04150400071150300442c09150001c0c070709a208211038004410445040c121803440c50342041101d218030780a20220b40b10101036006030682801c1890002620810ba02070b89120008030b900300d00300e03190008140310f4105000c2c01080421800f01000740300178808100000d5070384c82142c0c1c01034200040420ba001002d01d580d00810004100c10080328984608181648203000104415001107850282c54450300c9000d00002400c40b4050b03056401158540800c0307801030360000402d01d40c00f803041c0c4060f490300382052003000c01801070500150384805010308644100c412000303d2a42c0c108090044038480c6021902e4504180840a6a48155200c901c15084c150280b00403400c0d0340c0c080e40d1000d40030151f024024041c0b00300360b00c07010702444d00d483e0b4054084401e013031b1000d8006007280003000114040b0700d0001c03a4403445500018548410350a201240402c10380e07070306481b0303940d0540410903482c4c458400e54021210700045481d0544e000710 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 770278884 1250 770277634 770277637
    0xc060c140a12020c072409060f0c03030b0904081308030f19120e0c0a0e09150903041d010504150b031302061c0b1311040e180a0606050108150303 64
    0xc0400c02c00c004220000c1010003541c0540d024214440103c0355450346400744c2d26101411a003001140c0c1c02e00c0440c050400340300c1d10008003160704a032105da02040c2e945c10203c484954691045e0140364031008517404589030034030b060784544d0150001685030500d03c504030300c210005a00c005c0040c3e1003806040051411002214034001554140c042c030340c07401c0807054410456043c0004580c0e490145c0906803003030b01140d072801031201100c0120016803a402c9045100300d081c0d5180089a005030403c0d0360705003001b01c1784ca820a055400b243c1c14a43e562001141f80001c1230100c103e0019924010455400c060082da110f401d0580c3c2404070960070400700d45518000244281d401c15146510902992914400c60740d00d18520411600411020301c0d056010300380403070314103006035a404d5210140001c1842446403107002c800f40c05d0703d0070703203841c4907100190005080c000042401d0740251045160412540541c5441060080303161071510001520100713008008207018150309156420582d400310 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 770280134 1250 770278884 770278897
    0x5070512012009120313090b060a02031c0e12040f060c0201050d1a092823061f0f2d0c1b060306031e02030c121204060c060c14 56
    0x1582c503101c038610000540207200f070400203003450000040c5101d044924440800c1524860981407024008a500b404aa0b1144514503801030704244180c140e07541c0da01490b103003286034814022480c032880020040c00c1c000407280c8009a031600150400000c1c60248000008125508202e250200c0640018106210b046070094005544a1520080c1c88004000e95108100a800c681140c68540e4400141040b880c065501d840500100040201c0b12806050900c1e07101794202420040210b1103542c0016002e000140e2054000c4103807480006400c40c1e146c407200740d03075139454502400000060440c10340d0380f180900d00e02c581e030350311201c02c40c090681e51100451440c01c070002075958181100c0034805001c0c010002010280c1c005446941904080b0a481c06054100e40782d9081c04190a0204280b140094051308071603000303201481d102441e0440c4c04801010f569030350204d6404880035500c00d42104003c68109541030040c4211480b4000026a0342c0c10203124514103244003c3c240e02812 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 770281384 1250 770280134 770280191
    0xa08160c1715100801060b071103010b010e0607020a09090c05090708010302010c0b0a02070f051c0306050d23010c02060708071d04201c0b030610060516050a0507051201 74
    0x64002c50a4010300050500090013044000c01c40c1c0c9807510007500865000020540f010314548004e0f108626041c071465a030b8090503168034070130088074003e00805400c00c260a0b6031005042000140c0000320307008018449200d028145075550130501004013000300a81039004100c0716500500060740c01c02c0400e840302c1d400c502007000a41da0003000d24041d104c0c150700140111050604101000000164202d113003810640e5410011091141103003110124822540c0c0416400302c4c0401150341001703070345500c080e056847c0c401c0140700800c05007982c8500200e20010b81c0050f00700001c4560080c240c9401070140d1a282600600c1154420804c85039034182601c500c0d0754068940c0143e445012154084800c044030544075490442019084540901018051418000541204d15000c50458400d455000f070700009207040807001c60741504281001c80c101d40304540310502140c070801c00c00c011036202e03e00800c803450900c410b001492500d24500409a0f041180d0790007800c107451034415103c0850b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 770282634 1250 770281384 770281423
    0xa17030d021803030a030c020d02010e0a1118100306060509070806010e010e10020c1512010e1506042309090703031103070b0f0a0b010203070f02010806030a08160c17 73
    0x3501c00380920100b10010b4070390520001641100103a015040f54000d00c070280c090b00d540130241e4400b41d080c0c8107099141170b00380e00440108400a012410010340c08100984040d02014a507608807010fa1029101114005080c030400c108001150080781c2c0a0203007501c41440c5401c0c4104080d01d810f8001e080d040c14004040415a9203901c02e01003d10010b0b0300a01d000b140305c0b0014006919480001002802504041e24260742a09401c00700c03002440e40100b42c0a10740c0c60200c110940483c060710204045110581002a5580c2c1201403c090611240c081d0409407200101c04110900407106c1402406503004100c45040301051107400c40c2e07058109400ca03011480440da083d4800d5520040c6100d01d40420300c0140101d00d0090b91248000c8001000100702450069a80b4000c0c0301000b400200c1202c407440040d413160b25080d4000001608480408a0503075405403a50004100130041d0945a003a020600114821000c024065516085040360340ba0030302d5501d0f11962606c02001004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 770283884 1250 770282634 770282647
    0x705030c01050d051305120705150402060712050d090b0109050604090b01090e030d0f1b0c1113020705010504050102090a05180f090a0b100e0108010e210c030d0b0a17030d02 76
    0x20007816000d0580c3c1d0010a540070032015010b41016904080409c2d242449044005448034072004031840c09143c005180078280350595640314a007800843c42401001000e212000e141d6045004100d21141b0030070030000f4640c1401c07a40c038202e6100818180c891424510103074041b9215a98280c1510712591011948042c01d50a040c9107106445501070110702d020700003180980c4581c49045107525052050750b846e50314400c1281c42400d0180058003040c00d52448090034034110f0050050381006060150801e8000e448480c00c6410844d025100ea03500041d41807802d280000d500c0001c0c040888403a9030000f901a141101260000c002c0d1500000c0f03440410410001000000051a4400e200310341c41e1904000b01560703d8050f1160280b0040141c00101c0d012a060040c00034842102006041c0080c0400b00a80d030700384440b041a094410402450142400500c0106814049580007085180c0120180315501141d64401c00d10115a2841200000400703c12255810f0b1b003039501684501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 770285134 1250 770283884 770283901
    0x60603110a170901110c030c0c011d011803080a021b030708060f040f050318031207030804230111091005250c170a05070e19090c21050705030c01050d05 67
    0x1700c4c3c1c00554401d8907000c1005000d00e8000001044082400c00c2550900c4080c48015a119880e483c8500000c1d03958103a005503652144641c01c2c6507243d40794000c03852507500d807110440c82e40084d5003170005130401e00301c0e400f5051b810740124940e800d041d401044113500d0105525102d640140c000d10031129564003084c14010f05d4070014582607003100a4a0fa14a51130b500b4008001402e50260300074010a1f540c525090501c000f034690880e01a1180c0d5925590b40c1e5800110020031142c10520f01c110121003c00650248243c25062140d035050030b075685402d104005615003542038100030070400f04400341c80f1000030300e1010071002c40074400c280110010301e0140090f00c0f054016420600c0070500e00e6400820018410981c82e008200341c400450b11b61440206507a000c8458030075070360a4003d00c4490711180d0f0301c8003540a00922525045607210510000c418480c1c483c0d9260014103c5122070600c9000c1c400c100080000b20003d10070b0854603800a042401942070807511207545200144651 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 770286384 1250 770285134 770285141
    0xf03040e10080d210504081c0906050a1509020403110d0305040503011e18200409020904030801050111060106140f090d032307050307061d0f01060603110a170901 71
    0xc06546064995510b102c0700020614140b20012182d20310240c0400ca0f021030303a42c81010300a0f034000b58084d141c07000100c3c2141d03004108070900e0316810340d1030740c4060102b129445168010000c020002c29040d0520000c0d045071126a001131702c1d03143c41004200700140c0040844912031030103441911024880317082c02d8a0601995100d680c00d03508050109411310001140e2000044c10b07510100721800c1c240102081c906e038292801001e03c0f6403084c512003442c03c01c28048280d1a0001d0012500440d07940c081813544e14203440880109031440e0060249680006500e410040040010302456260001c020400c20321080308101c001c4001420191010030182120030b001c2c0c010f40380040a8011f41340050a484d00c03954003940c0700465034210300343c4100d01030440b40c0d000e07000001103080142c02d1700c44000502c4404410150750420b000d000032035080500c04002e205505400003d101441c0800103401c4e20130751003000c5203040c0e0030024481c0642d040030741c10f80f26100c541c43c0a600703a9105212039006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 770287634 1250 770286384 770286389
    0x2818060e100311220b1509030607080a020717030603061e040803070c0615060e040209030307021309150c080106030c080f0c090d0c1a1303080f0403140a03020601080f03040e10 77
    0x1484913031130502010110326000706050880076101c0500200001c0554101801005c00881d49908202c000c646d105120790480b58004484100043c50440b941d03440307204000300101c0007180c840e008010880356103024800c80c1e0340400000038051008900d03825800102c58001c000030310221010002c100403e100f10020310711030307034405410040c9034551140e801d0210071611516000828090044889090074001d032403803420080d000311b040c100c84d50701708189000500003001c4060307501c02d82d14010500c00340b0400c801d0108200009020021490010020b40303050f00064181350a01300003030b40b001e51000040360303c901c02c01c1c0881d03181c0d201c01203410820710400140ba603011000d0100e0005100051407000c0407101441c00070300c02c40d070628540d4003144c015241101c0c0a601520401c0021550280041940703500c0e48860a10b0076880c0e940b0100c1c0d0b02e264010707000c440e500400101c81015010440700f1b014200100003800c400081800d400c0d520f03c1a03000340c9051640c8000843c018043c4803203613401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 770288884 1250 770287634 770287669
    0xa0611130303020c091b0d200f040f1508070e0a0e0c27011b080c030d0e060a09053004060f27052818060e100311 50
    0x3106989040c025a1100c800e400769109031400000704038000c0c0d084180c4100b040c02e8007061800c0050803100d65008202c0a40001c100f5410341080880f2000010002c103542824444c0d283d8445052070316515201c1d90a400c1040c20780e1800010004041c0c1000200e50700450f40e1a0200021980002082c10a0202c0c5c0c485406c01101209000c1d021130410003406611088c00f80365102c980c43e011a00c0801c000171b40780b0901182c4086040d84243d41803051030304c80c0500a0000070300c0c08502000c6140f03590701500000350f200360303035581000000f2028000e41f60032a6203c9410321001650342c96060f140c800c1f1aa07603840044185040c3c0c8040c1014100c0b1203010b0080d50002c0352540e5403000d010b0100c000c411510310009041c1c810548050044602e41c8031040300d10b0072040c0c1c04031f04200a000001405103142420700c0c08001c040c60252039003401007400b520040d040c0e00b090045510038002a20001e4212490150103a410020310403422070301c3c03004a940080c1c04103041510200400c0244110081e4042c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 770290134 1250 770288884 770288917
    0x31b1b0f220209030111030f0708060312031f060503152407111c03050f0f04080607030c08090c13020904110a05092b030e010207080d031406060403050a0611 69
    0x354048080d07400f40800300c200b60020301940c40e24440000140c030003120324180000040012600062003451040d5000c81c02a044944500b6500300d00a00b6400440c2d405c0746082c0120014012041041c030a40c0041c102c6061517411070406810502910342c10842c603900a800c501d40c2d40c102e01d4140003904d00e020703021092495030307003034181001c810141c0c0450303100d405441c0403140d000b030364510b0303400712649260159980f6003403424007054a141a40301e0002160f07006010f20000c42c1e005020320402d80a49441c1c0c800207981c110050002d49a808010007001148c2c10604400c5a561038000c1c40781035850b80c40000503074030312645001500900304d4890401c030056010401e8002141c0210051148030011200e0740840e07600b5494080d0261034054274003540591032040600001d001c0e00340c40c1c440000c1401503906580e10354a0f03140c0b0742012814103500080e16450400c40c0040e254203402d4000c0c0c000e8030228507040c255114299281101035008254541d514500300346005244240c03590600340c0302240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 770291384 1250 770290134 770290189
    0x12100603050a0c050f0d11061e07050d05030106020c01050c071a0c0c15071104090203060a1a09070c1b1a04030308070c02030c012f031b1b0f 62
    0x3950740e10402c40300326003841410034041120300d440500038285280c0141a040b03182501c1d5500d00701e241d0100182c87d00b245062002c940d801d0040702d114984c0070207400e4110b85032902802e0043c5011210610035051140400040c00382c564049216034400344207080056840058060701d0745041940e40c011890703003861079580621104450700401c44020400300310354a4080c0b040402c1601080c5000241c24071034208020800556146280d0380a100c000344001070041c42174020070300b0140102c1703080340e140c0e5480781070442c0d9804607820700b5407041042d13034a18183c0c604200054000d9501810181c000c01c040c99070054448108400100a072100031002c201c10407880404007010b800501044010134403000008000c507110b01d6200d40c803160000d008003c001311071001540c4655400b40501e4603038a501d4162209111640c490403180662200111f507151100c0003105c11b402c03100041e45466400c4110501802c50b24000d00c0410114101c03500845040c113080092401400ca0b030202c42804210000d6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 770292634 1250 770291384 770291393
    0x40f090c0b1c0e1c11100b0d020901090b27070c2d020a14090a230c030f1602030403060f020714010b13020909010b0a0215042d1112100603 61
    0x1550108201650359031504c1002800e81c1c0c0f450503903200004503805001081d20501050f086183ca0300f002501d103421541d0b41c0d80102e61410f50036040320440b540c0b179000b0070b0000d007005150380ca403c0404170312071030000302c403120054403640c0090074400400842c01001010b104400d1080c15502c4030044042c0e164281d02c5045190290300048260720900c003450340050002c10180301401541d03c01003012500e0358414502a000b003520084a0358103030100e5005420581d45070842c68020040400e11035101d2821301402441030740010021900b460b00360140007a00780c0c00205590070b0301d500c1080070509101100300e603030086c012000c000d407910704191003814a02e072040d80b01401004055403008081c1e22034040345d605910030303001850b802164100c0100300045c0044007030420004103105807450000b01e180c40052900d0240d80c00d0f600480d0682c5443c0100c0554408440003c2e030080324082e03035284641721044503d08881089000e1000c1460b016604041803010086402080c80200031131a12802c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 770293884 1250 770292634 770292643
    0x306170114061912050705192603040801060314010509010e0a0602180a0e04030206160c141501030b0901060509060a050d0302070801020c01020d05061801121506060e040f090c0b1c0e 80
    0x856014008e120604c58190f281c0d0b602c007209031907166800e850a654403001c100c54130344c50013024071000d0005010104030304400f0b000d180000e60240a0815650b0030114526003100c101400c1c1c0f00040e89420a982494880400e44035161038006c0d100585901c0001e10389140080c3c81100b140d4042c5d80c029020500458102d0b00724040d0307011780c0c00c6550550f5050841c076075000318141c1e0030001c50405045c0000260f00c10003582480541032007078805a1007030400e00c584136802038104440300c0e0607040030880d414200b449000028081280d1569142c201b19011605041d82805254000c4800000200505000308451002060000f0085580b0511660f225000703411010405c20328900b00b60114401e032400d46004c4c112140011108840ba9103400868010855246400c0f41d22001282407002d12217110702c0390030000c0c07030382e5100e00390814801c41c1000308941025030084441807802002c0404242e882e1018001d69104111041c1d072800189201400d0380280541d19000c14188480411910320208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 770295134 1250 770293884 770293889
    0xd03270e0708090a051f0f020403080901020f030a1704060e060403030605040b1f0f1e0c0201300c0e1f1701060807230a03061701140619120507 63
    0x658004240e11440440c60f110350703513500060f003140d0000000d600d18551004000b50038014440c40015151080141a0140e030800c3d401603810703050201d606240c558042c072044191603a100f016500e48803c898010b007012100d1510641511068000542002280d500c0b054001d1103c00c11507240d032816250080140c445401014006c40c1846001445401c00b003a20745685903000051038880c1d80c60310000c640f0381c1003502d155810011919208514807482003003c000481c001d0340c2e0341008800da800050104c000724801480044041c0706600701c0e652600717225070070030300c0200004100c103114011300326103c00020203519030140c100c8500811604e035032036200303150388240d07200d25280c0a500303035400040c1c0b4802d101d01c0010605080000c1c50781486030201514200325122005842580624070b080140c00c810750360401f181c1c4d00c0e40c2c1071091210b82c80c059000c0001c00e8000384a841c010701c0761107081a5010344514003801e2200143d6000300c0c50101004007501c0f102095006100341805c2807580c0d0300061 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 770296384 1250 770295134 770295137
    0x70c03050708120f0c120a020a0303050c04080c010f0905130501080606030a05030a0c0f0c0314060a20030604060902030f070809010b011d03160603021305060403020d03270e07 77
    0xe812031000c41c00411004985050f9410407110b1030315050254401702030128a80900c24001040101100c042c002da605254000c00c000c0300c05180180480300040c00b004038110301400700b000b070010000b404d521184001e180a20501c0e00124056802110541025070f02284440d9158000341c02d6500c00c41c101d03585001280c001cfc1c1c8664061580381c6915610282140d0010840c080481c1d0144070090400d42c81030b20020400403003603c860b44120f515800c115000712040607003a4001f513040000c16003200c2991001c11880300d0000140c44980030a6100044c0c1a80210000300e560b541c2c1e901c614024440070303c0640d030700c0c0340003019907800403030840b10807000c070360410702184565005200b22004800c041e161a54650400e8080101260b44041440d50510a542d0214088102d61640c0300c01409203460158441c001280555008507494014030301030789050008002681c1c6e04d034000d0074500c0d01824400c4070040d000403505c0c0e5080400001c900c0c1c1c4e4a441000084002400d529944220b1f4079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 770297634 1250 770296384 770296393
    0xf06050a08100f0b011b030c020402030406090506480c070305070902040b16020409020d060605010f0302030c0306090712090f1509111e1504170304060f0f03020906070c0305 76
    0x14911060480d110b04c8003039030020b032210000c0450303c50341a490405050180c10104e14a054560018007a44e1003107030215251030300c91f40c0100c1040400c0281542102400300748030b00c41c05104864800d201401d030001c0303505980c129041c080c12039038000f10721a484020017101d9659440d030500c0030f50707400c044d10044a071840b504030000350450141c42540c041d19001070403507150200309103030417241384101c000590b03000c0e54030340c800307001a6188107503090300134840d0360046661031a0000140a20b80c4001800007403500402c100107a01d040031080786d900c04800c54480f036003510341c00400c4a41c02401c1010a20091801101c0e5003400120085140d00301c0c4100400b111007a10600c076201034070f554520040c06202c2402807482c051801040c1d554100d0040d440b580d0517419000c0008d800012089006400c086000406002c011581e948030140c90b201100103500d0070340ba2120092810410310241e41c10054200714807c4c8262203078049030740a0b00014115926030095041c00c9000300080e1008407010f00c0b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 770298884 1250 770297634 770297651
    0x40e0613050c0d0f0b07030b1e1c050304030b07020c0901061e030e0a06110d0606030f0c030b0306071202040e0906070201060e1b0915070b1807180f06050a0810 70
    0xc20f00c0080c110b081d8400f004586a0700c103655611514407004d030414003850384414056a90307403101040143c1d04c1c041e8400c51081945481c0604ca00c261540c1c4103407074080c03400e00c000404140e001088404495101e001e0354076595501e44101d051640407844e10307074410b035040700001d5625400780412200020282407480c5100d000d003000c1e001c85507032500d25034880d00b1a62246000c51855071100c100800000566031070528100c003000304070b030007541042000c2940d51401c80804107061182140d00042400d0030810040b20000290303071a03c0040045c0104043d6056048200310240c040d85c00512a42d80000700a040171050607446400444060300190700e1301500240118450b400c050048002007000c3d16000040300d0411116400040825009408900c81c0040e40e03800d20300a00006e801004024060f003418106903402008000300000568007034407080c000303c80002850101800d01a100103184036110441c10080d103034035808564096010200007135104408200525003100281040001300d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 770300134 1250 770298884 770298889
    0x15090f1f0e06040302131a060c030c0606090f0103020d030c0c0e1609062a020a090207030810050102100902130501170d03150522090f0c061e030b040e0613050c 70
    0x103504c0080c1d41306124007900d01c0e4001c0c0300da12103504000e0729200c1240d00d00b503c101295096114a03030307400a81d800060a64007040051100a030040021207005181c0d003000e061f000c02402d8180008ad2103039034100e10003410035006003d442c0400d0341c040a545601c554810440d01b1802c02240d40c00c0d1001e4100000d07416161248c00701405480c400c0d1684030304110300030412900920070a0040e402e6548030f9291602595031815818014074803c18007603a03c4116150080420304042c1c024000108008810721140ea004240b100c1040a2030100103100c0344d160001504040c8a400900d92aa00e4080081051000e600000c0480c9640c501119200c1c29401030071000c84417510b2000827100c00e015406c0c4070b9440c1c40301200600b410360903d00e518410340803480004807441810101c60584200140b141008554560103008000b42d0800200103045d000380c22010001e09100c40041580d0b804203500543d48580c010f1821f4541c4070308031096454414811030300c0c1d4001c08001e460030720950000004d00d2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 770301384 1250 770300134 770300137
    0xe03030907090e0c2206060f050301050913120806210a080307021507020304140604060c14011d0129031005090705100e130b15090f1f0e06 61
    0x6804000040403210b207485040e800801190000012901a48180304510341d2600c3c0307610307050001e4149401c004d084034891407040700c11907400b50050104175800400c4c11508201034034116503003526035004a9456495900e060400c082c4014030752035240201c91041540304010300c1c1b1510f01960003001a06000000c101d0511003c19407554a030701c1010f402d000215005c0c040e540000d4030740101c50403810707906601c50440c801250b58400513070000c50b0400061482d14100e00551f84290344251502e814844010000c001c1c101d8040c00324400514000d4200c0c1095128405464500701c1800402c00f290310403601814000c2c03642d0060a41e028026010194065046060310340014002c1c60b000340c0c1400d084000d044000c01c1d0750128082c51070005540e4070f402d038030580b060415945007401d0388014402c004c0e4450080c640311618034500809200300d5110f449060b80808000d1100b19100c41103100082d9040303030321950003a04100152801983c0c0305110541e400f000000d5180c1c004500860b4050000d076 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 770302634 1250 770301384 770301391
    0x209090a050c070201050c120307020f0705060315010804020a03020a180e06160f1209030f020f0609030906070206070804030c0518040305090621010e1e010320131506030e0303 77
    0x8691080014400540c01040107000900c00d80040c0c8c0c100700c608078540001038108890810260b0840130b00b20001807812301038003010f003108236150f40c11800c1110141c00d080c210488010305024401002c40c066550f58051240150360040c407501b002510358414810001134160f540b00201c0c10502519010392021070349030300c03600386c0c0c80c080c8a018104c01000c0b00d0a07000044240e083c402d4080c140c036641d0342e95004120180d40039440f400100302001100034a020411700152010390001418400184408421640307850411110a44c0302d840600002d4418840c0c506e0060058100003400410409295055011500d0803161402c605031101c44092134040c08035030042c00100c00300b0842400e440d1480241c41e50503511240a060720b6190700c0b480c0c452000c280c00c1451070720900c00400015004659a2480343c0c0504039a07010310754076603a19414180c001c00d4410102c61004060240315480d0420718401d080d0182d601400202d1006503010300c500618055540041e0801e810f4040e28040001220301 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 770303884 1250 770302634 770302651
    0x30d05090d03050a1b0b04031b0521120108070330050d060305010c0809061e16050903100b011707080f0603010605120c12120d050c070c090209090a05 66
    0x481514955044480350300a2001c0700c2030200074101114002c444070f10b441030040c1b1403080b903a05400c00b03003000b4000d001500110004102a0380509000072004100318000d00410070604801c00351500c411007003401450401381814800c8000090841c90020780703078044a0065503250034030b00c0341a20861130404484205821004c048039001c4210344580020150340359211000240142c8a50301d050079201c01032f0741c00d000909036000340284183d0a00500390001035038440007070f0140c4195009140d0580c010204000240d00e4810070007050f0245048980e01c200c001c094510140440c04054010314046a21034001001c291b23846c07010b14070881003240502c000d511102d5907507070354515101c0001001030403250155296040041d032516a102a20b0f650401c8030302400504111000f0701a24142c1d00191400301c2c0d02c404d018400c103070b01d0031007100c05600000b1400704090352075407158010380c450714a00a0078841c1c00000020f020b615035020f80b80b0074170115508034180c0c40310500e04c8250b440a690700b50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 770305134 1250 770303884 770303899
    0x14060408030315180a02090916090302011b230610060c1202120f04170106030b06060315090c0705060906160507050a3c0b040f0201021c0e030d0509 65
    0x3404051441c0f480b08500c2402041c0d902406204a4036401030001600c0042041d42c0100c0e14894030b250103c41c059022956928039a81d1140c034110040c8541c840f440085c2c1805890180c1000340008141003d101c103411600c01718005904200b840b0301e100311140040d0b014000d0b003003c190268141701c4c00c001180d0300d135503500e08000070541314402503450406c0c00b5030651085400b000310a44011014016600e20f00007810f0700e441c0b42140c0100f00702c07010381348000d907640740c0380043c0002001c0da00c420b43c11034402ea0b142c2da00e0f50341d010390348401c640102c0302d1a0f910051020800246003283d90080c1550341c07090f02030702c0f8241c43d94880716598490036555007400b40c1144100c800300c0d038464409042403d019608451840d130300da0f00c4d81e40d00301044514501c07420340301c1d4201c40c2102e44401050310030f0f415001081200d0342503030340300c0d1540708101801c01003012600712000c00079a8401c20207605800303144407421054000c00100030740403002e0701110900900a0b01c5028000c14080d00545501880c041c1165 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 770306384 1250 770305134 770305141
    0x105210d050f070b07030501080c0315070c0c0308180f1804030f0219061b0c0818011115041412030109051308070303021e0c3a09140604080303 63
    0x39211030300301010402e01c014042c420800410301604003a8003800300f645001405504205605041c01120b160307141c083d074480d28040c0402c0340907003403d1f540b006592600040444c40c526042080c6041640050040080802d920801100140740e48243c80d10407900d54040580e42000d021010f6808201003c071011a1000500030a00403c10351360714810510585081490b801c2d90741499048032581903404960303460751032000100d602c2d03030f0700044c0074072382403003a4615442c4c0d54000440c0310703a8070039026000910b08e2403000f59005216041c610740d000403c0d00c010740003134441102c0030101117a054070714945440030307540409008105469403026070240311307246038280303d10b480180c94040c20400e42140c22042d07880c007080c02038000d030032058880e584c050307030300c40c1581d21141c82c071198241d40010002e030030020319648400c001090b0782c03d0403090740589225030381030302c6030445003081403061400000111824007403035611000361000e84282c509140d2043e0061018402c0d180914012044581d0081021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 770307634 1250 770306384 770306387
    0x15051e040f02011215030f02040c030e030d0b0103150b0d05070f0e06090d0807030c0b0901050106051204051002040b0405011b0507030b130510020d0e010905190c031a0105210d 77
    0x403020082111113020406840d03048219400906a0b4800d8595459210a80c400c514280c065135046004501d424020001070410560b00c81c401c01c2416100300f0343d141c80a04040c0d00a410010502802c8039080454550f50a5001156030144c0700310240d1519103000690003034083d16801c40184241c0e560a11b83c088281c0c14030107039078002680c81d940103030311510460000311144002c020f500e100b503842d10f08403d400d01e40040b84807009801100c859050000500c545035020041d070f100702102000440d015115030a110781170100c200700c0d001d1014000100881d5081b1660010002c80c0c070207a039903110014244030046010182c08900074160f400c0040d04201040001400743d40040002ca0041c0d0f6440740391761403038500000c101c90761074925000f01da001c51006462240c040ba14100704001e00080f82c40b9a07a40351100742c01481040c00c00b00248003107003845107610203400590303805142805086410503100041000900c915480b0340c2054070400030403805410190030580021005002c0b50010050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 770308884 1250 770307634 770307647
    0xa0203061f270e011e060212090402030c0903010e0d0f05121302031216112e0e0409080408061f1215020304060b0f0102280f15051e040f0201 62
    0x20030035803920b0320140104110300031a402e01c1c024114900c94440a40d5241d080303c181001941c400e40940d04140d8900d00d00c24402c0c0700315000c903001210010b030381e0340da50f03443c9210500900007000d80661810b404044208000210805500c5460322540520480d03844200ca951003400c0380188600302d1b08000c284213180781c00c1e145049902c01030036140004a8401c00031901e4000c0300c410f410b4180c214000600348901950100f44488083c0c55080040145415403d600d42c15400120300580c0c3c000703140740c1d150784103a18462520030700800500c4820304500b0702c01c2580e0803a0041000501400c0007080340d40306c0c620b5408001d111940400e510a500c0d00c181d94020425141e416a2402281c01d48a03a0a520900c000d40c0308900c00c140014184804100340070f078040203840d140d030640d8400e074100e59041c480d20003020301410281c0b0300314000c18128541a02168051b140003055a4800c00c01303180088003e421017482192a441542d100140c9815504000c12040d40d0140c02120203112100240d4450f85 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 770310134 1250 770308884 770308937
    0x2030d090f080706060302101b0308060307120803010321020a03030c0903080313060f0c0215090c060c0708010c0212032406040602010b0411030702071e0305060a0203061f 75
    0x4a11101c4045070781c407402602c0d0301805040303d504c0d40d10401030045192a092000740d0b40c60314600240c20035426240b10300d07448940f40000c4e091142035000140c07169801c000d03400c094030040d2a801d10140c110b00e40075040b9003003800115a4100c1501c02c502c03502004031051080140503500078540141152030540041880032580020401c1054001c0b0104201c10019070142c2c071050608400034045050803000c9034807074003150040909080c00407050359070005803091002c500070039230401c0d603e41c003050502e0b10304500803407900b200011544a08016010500304101d0300008001d01c864091054200d8070350700c41025015800d50140046038100c1c0811000069001c462480d00554190a400082c00ca030496402400140c0d100c2d5038440450604c1e014601104032030741452811410400c501a4840000f401090030318820040d52400242e00b400c0349c40021600b10080c1c1c0c5190624035580006540f088507224080c130400120418002980c0708082030300c0b0040e540b2000c055228681c03951442c851507 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 770311384 1250 770310134 770310143
    0x50415151701060f020606010314150103140c09011b020105040b0306031e0c190e040b04050313060306052707050c013819060503101e030203011b02030d09 68
    0x1000c2880110003451580c1d8082d180c90386890060781c9030440c000b40f903c18020b03e00c81c101410107210242c9450381e03c01c09a004038000d1604505a8a607400480090480103140314015002d20140070003580c0110080010030021b03070750201220101e003000c4111280a420090004030204000c12032018840051504000c7c0202504c2400058480c5001001c140c45110304040d040041c80a10a1800b0100e0043c8400c10240b00300c46140b9140c9281018140203001525044404002a007048000e008a851000103042000c022039100c100c01002003081e402180e001d00140ca4590b05000c0da18200e910004413272480c48285613a880c50110b405c0e8000a11840b410740d00c551601d0030070703410303c1200e00c2c040c00c48820b00004501c19003065080f48240d404141e000d00c11071601100389044424042d0b05076402c1e424116981e4035a102d0780e01d6035507000d52240c8203008102540c0006c440a00202008480c0201c2c000d1202c1c503032803010481f4240700070500d8400359004002c010003050098000c400d50a00a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 770312634 1250 770311384 770311397
    0x2040c09031707020a17010f0605010f1707020c0a0e010806010501030203221b1d0c13140117010b12090d09050918011407020708010b060a0c0f051903020705041515 72
    0x2e4018a0075200b0b28202c5806c00f9035101d5100640c00101c40c030070b8a00819003481c0c4407071541050b0202404c0703040481d120940c041814800206694020401c2c01882c0b031019080c511030958039141c0f0888810280101030791800345800000f5198030900940f0f0140006000d01441c11404c0c038110940719218503006c84104141c0310140110340c010300500b00c02400110b004d8030b0480a0113121041c00c045c01024904165814481c07102840d240b0f250a8040c0e805401e10551034000f82c1005940d0140509021400010010700200e15402c41c0e01c09000d80c4000c224100e205901c2e85039a05490f44020000030002808122081125140041c80c207504036170203060b80c103c0c0005188406082d00c45400318040c0d00004c107400d00043d00e0b0704110b200000e101c0b8000030018607031030310300141d407a10030440a84108850070110200b40b04c5038408081c07803a913203d003c69072005031500e0b09041d140d00307081080d009070041201c0000c0c942400d000b0f00c51503000011401c0700e4641000c600c0084c400b407480c02d03501000750 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 770313884 1250 770312634 770312639
    0x6090a0305060a090b09121213020a0909051009020f01030c2d08130302030405040c050c01090b06040605042003041a040c1a1602012003031302040c09031707020a 71
    0x5041c080d8900401540301e020034130035118204181490340151048000b40d100ca402044100da000c81541c01146081801c0001038449840d0340c0101007c400020398041100a0005441e00840d40b00e4604103115600ba200300c003404d41d110008680540a002e5000203603200d94121a41c4250300c41d2240d0401401c201d000120030b50904044906035445a580c40b42c0e02011114865400400683c1c1c000140c90b006031505010780d4009441b40224410700d4066a02d40071102840c41c020070a83d00303001041e6008001a903400d0821000c4d00c4c00585400c3e0040d4581031011606085c140503044d00322040030441054204000c000031145c2d0300051080e07a414003104100a201d10401d0805c42c00341c1c2c00f400c9071084041c10a03c00000d0b85000946c000d891403400c20803800d0154403014010301081d02420203810241c0380006920101c002000d064906010003c1005039410380c40c5140441d0500a07141000703220304202c4192030054041c0005042e403000c541440120640540084c100e2900c0940321104255 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 770315134 1250 770313884 770313893
    0x10050108130b01030809030c100c062c01061a12060d02060f0f0d0c0503010303020c190f09091403030402030703080306040f050106050901030b100c170f1605060a14010506090a03 78
    0x510030313001140c00150009207aa420b10381005480d41101040b11500c41c405c46010014103a05000c0e440200700e1500d54000d803c40c12484020914525030607201c0c00c0c640a042003440340241054042e0380410550504001500001c907002d440301c00e005181d08402d9038592200b000160613a94008130f0740078404001045144243c20050417410282c5403007251103982d41c15100f000e0740d500e42608820008140010400b0035400249500d406c1020356460f03c0c84040c400000030010b8141d0050703090300400d40700c0040d1161241c1d0046007014000d030010b00c0c07524160b05803291a0301c07040c1c40103545544a1601440421910780080d80c0050004000040442d9240745080c25140c0c241c0c030035004200040b07070bc500b80f5601802a01c4181c1411103882400c0d080461000e09010005840a000c500b000c030064042294814221038640e2031126000307032107411515800141d610500030459050003502d002c01c2d43c60007140101729918600d610208404d82c20002030045541100e42400d0b480340c0300590010114 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 770316384 1250 770315134 770315153
    0x406021218030d0810060804020d061808030702070501110304080705101107030f03120903020619140f19020c061504140c032202060306210d02100608061005010813 72
    0x1000361940301e0b0038605140e05c0c1e501804d0702c1c0e10100602c183c104c02c002c010f0f41e80f111052941984150000f500c2169036a251140030107401c0000d0070307a20000107101e009900021100225482642e03100a10444000080c1d1640103078824805a54042130050001e450304480400c40c4500310300e444203459000c00038440c40d050241c0d001b99804a03190f04220140b5500100022200341c84407070611402c0c010f40e40080d600c03c1d00603c0101c03074003040b1170303031042251aa821a100e8103050440d15420790601c078094030900e0400b0b5403032100c124406156510b200840b8001c1d903074580140c4002d030009944040408400c00403c07071400ba8481d80c3c40b00d044160403024440700340214000e546075903c030b1034030700000300c80542e40261890940800070300310300045e42ca140c100d95015605407030409503401d940c600706050800884179001c1e1401038800f01388400e5030024410350014a040014059580c0d2181015100c101c2942c22803001c411962042c04154090100c25812040302014400076100316190010403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 770317634 1250 770316384 770316403
    0x140f0c032b110723040c0e09060111060c040e06010207140d1a0f0402040b0303041a0c0a08190f0e060d050709080d12140c0715090204020a020f060705040602121803 72
    0x142e03400a51000400303000c1280b440c80b04d805d0710100201c035020340c000351170344c80c8400100748184400400208145d02c82c03520706e684074003003100b1a10781d410010110b100e40d8205024008179400c1d00000186250300c00101c58080b913584025580d4410240070510010102a000c180d549441c400e501c20300311510040030503c0380402e1015100350381440d10403c0151240c0c060b48901ca80c0c0180414480c020249036807012500030703a584196140002000c0030308103861a00040c11000c404103c40e5000c003c4e518034080c401243c0d40d03500310000c80d84a0140c03102891b143d54190080c070140112448114964440d9800001504152280c6965a00b0040c80c02c143d82d00500d00240c100352426605800c24003841e1903140420702031050610303040c600c41c401e502841e00b000d0010a03c0304940200d8213031a501800001fa000341044d9914030494401954a04942c40522994852480028003e40c45a000d807800c0c1c9596074041c0542c0045510341e038074036401883c00880f80324a4003080c02e5140d6010011101c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 770318884 1250 770317634 770317649
    0xd0b060418030e030c01051c18020301020c070f0e011d04050703021e122107030e0a090504020319170a021603050d0906020d1b030c140f0c032b1107 65
    0x9800c515101450304003024101750074140b10040c06681d8000c40a82c3d5131148001e05240e00141e4446d007030120110250029001031b400d54030004452419550119070342c0192958010090b00095403501c50120b9030a0074800c5400011b40e81c910008081600510103030810302074003c841d0032030703200d40000b1000c000320400c480454a220303400580509207500c14010080e80c0c440030b084029040c0464400c104400558083c0f01c4900150300020140280b83e10030760031070050f1420000030748034a40c0f20700410055a042c0d100388038201140401e824910b40a180c0a0b902c5400031a83c03041c00011351047d904400312075825400394200400c0c41c020480301181c0154005c4004240d8031440c008058030740b01280d00302004540201082c0d0b5480d541040c0545d01e95040c1c1e28820075600c1103400c0880d080342d0b40800084ca54000c0e4a0000d0684900040d0442403c03455003d940c0c07010141000c0541da1000104036800329480c0d070f00034001032821030201403601c82507414100b1840e1001078000d41051041c1d0080c20 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 770320134 1250 770318884 770318897
    0xc08120106110f1501030327060507030e030a020a032904080d140c04050918010e070303020601050a03111009080f0102120105060403151d030a17070e0d0b06041803 72
    0x45000204214002600010f0000340401a804107071803030440380140000380906c001054041c1e052115100f0302030a00319541c9420312600e854103402002d80e0701c205800d4000440780180002140303004221014040d5004080c110350ba440d50707407100c0c0c41d0b41206161482880020500d101c1d4144590034a030304c9a032080b69025034400c0200d00301802c0301d0800140611a807509420415a4a10b0008440549008646140c50366541d044440e440e2030281711490b00c15401c3c90050521040001035000680b0310035001c1c0c507010703a21401031000ca01894840600302425440c940d240e1030905441e0854584510b07c2d04000e85903c80309601d24184440d12000e50320303903000800f185003d0000a502c0c0c05041c0444040e454646561540c1c420751411998060f1066a10401140348011641102e2541c40000080d80c0c1c48800c1c000d000b6003d0099860405400441c0000080301d280c45183c40814940005003010a50700f0581ca03031001d1414004e0075240c0143c0c1d101c0b21130b514482d40a413403072482d510999405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 770321384 1250 770320134 770320157
    0xc01020408150108030304030f0305040c09060605070507081b01110a0b0c1c060b072910080c19030b0901110f03180a020108150d0c060801150c080a0c08120106 70
    0x40651502c140c4c0310400d1904288140000a6401412001d2080c00c2d0314012403140ca8500b0050036170700c1940d021200c03c515041c5e0000785246c002000d003000c1c601030b07015112030a5858020035161140608441524011803014440c10340c06254a1030551b40a88121303031190030b003507a40078941d5505a9001840010106519281080c68840c211841605503401e0048524144038900540034011008000d0558610362918802e5500704900034580030140140250411001010b84600b041c0100300f814084d00061071468189108400c0d10b0640c0c030303d851641355140d9206c802040c00301805002c1c1954039040c0310101319212a029010781062105013980d80e0502840d1185101030381703c19104150080c0d41200b0160380c01a030116072201464031560060b04504c000620500441d003401001c4084460700072520a038000244c1c6e058807207007481035080246115090743e013104400c100811400c030801500282038800c2903e400c60911800d4040c1c01c0c008500c08510050400360007440001c0d5130820b94 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 770322634 1250 770321384 770321413
    0x170102071a040c0909080a12231512101d0111090a0501030b0d1b12051005060111030304030f033806090d02040c020c0d03030c0215150909030c01020408 67
    0xc00c401040e134540b080107020043e0741c4000076406040c0c40003080c401044400c01b40c20f502c640045010307019011040b4800c0c1000103a048000d402540c1c42d1302c222035036040c0c0c1c0082e401c2c00a91410130050704c90007030200c902400c0050000c2d1480e1040c241585868080c1c40b003400800b405013498403080221b0040d1600c60441c24481c002049130310490405041c840e40c0801900e0305040c1031010794200c40b0416190900c15a15070480301240d1080c489011f01240304018800081500c0c50702204890341031209882d0304004682c1c2c40014220a1001c0e001000400c0c0000d00608510101a441d8240030030103440c070b08944090001d00402c944040b015840440c90000e507400421a0740d03420480d40542040c03410301c00b10300c2c0d0038540c1b88001c0c05666101d51a8480e240200301034001708e0002032002c13044044a250050240c60400040c102521981002c003101480d4103038013510a03070500c28071500d580551000c1184100c405401d072401c0e07020811400c50078440a0009201801c1c000780209261440142c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 770323741 1107 770322634 770322653
    0x70f03050c1e160302010212070218190501051203121302040e0d030e01020f12100b0f04050307080a030e0108040c081f0c0e0109170102071a04 63
    0xd0b8902c0c040d41d01c1285440400280301a1002410040e034440c20302145400024050303007080060600c0719921401500d041400100501001c0f0000c0c1c0083d0085101501e180482e609201000c4421180718024580100000d450044070b5842031241d5546902561440b42c1e5854650000304400346580c80d002c840c8250001c00070002c441440e400207580d404002c1102d00070a0800d510a9400070041c401c0d100c00c0003c0400c41d900c4c22442c07a942c044070300c0000f04101c90790b180c4a1004203600b0180300c05413034400041810650b580381003e00300351a2000742c0d27000310240e5101e43d50005c0000d60040300074211070000e09080f22a902c49240a0b91056055000010144030f0f140101517400c0c0c40e002207003155500c1d0601000102c941020440700c04241c9034196020954080c01003050b40c0403c80100f49000c0071400060a10180359a42a0410b0000c0240400c80200c00103100c2801070401 = true := by decide +kernel

theorem cover : BRFrame.Cov 770143884 770323741 := by
  have h0 := BRFrame.cov_init 770143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 770143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 770143884 ≤ n) (h2 : n < 770323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
