-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:27:13.770592+00:00
-- url     : https://prove2.me/submissions/cdc01f6e-ba37-4a31-a480-5054f99a18b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 788848920 ≤ n < 789028776 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 788850170 1250 788848920 788848933
    0x30906070317070923040609062603040f03030c0203031b15011e0614040503010c110c0303030c03040b10211505090a030522140301050a090302100e 65
    0x5488400141010314440d03214000c50300d08511441c4610000281101d0030491070b0441081441c400d100c0082c4903408031803550190860000110b130141440d03074010102c1034503009001800029100b0261815030b10090501c1684104c01055584e90195000c0c8a044c02e002d040300f003000078020101c0806171071020701501d0030418452011410b1101d070107102c1235250801240303400c00d0440c010f80c0501500480b00178682c2180c401490208810305c60007040c2c103000c0d4005280d0307802c09000f0140c60080c20014000d10140b102c03250b00400c0d011619100340c0041c81003400305a4140b6001c82528407134045840c0302d03421913035641c072448003502c00a010540c0c40340d036484010903030305441a130304140c0c160300e2540000d20341e529141082c41c201d43c10390311600302d07841d040600600000104882c10043e03003514107503440f4a800a525a52907004400547c0401c110800004400c51410804c03014008210020811a951000c0550a45081d40e80060068010301200768045c02c0e50360041c00e500244404031401c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 788851420 1250 788850170 788850187
    0x213050108071e080402040e0703051b0103090c081e01020a050d1d01050726060307030201140d0f062d0e071413140a1a0901140a0e040c0302070209061203 68
    0x100616204280000c00140400c015030410b030096210a010230b50041c48858556141c0f1910f6142400d0005070405410b185281c241e846500300340792180c1c108103045c1100c0d556a41c1d01d6a540030f000200a0f00c0f160318654071810a0b010702c00c1e9400c2146a0325640d1030000c60341d0140006001c81072210411081808151842d00402d100e01440307034031aa1500c13499440c01164a03514040c413241d035440300c1034024040244945010070b44208403542820440303444038060244482030300a40b04a08012450300000010051280d013100003140c101031091000e00c0070150000d000c509c107441c3c031026600900301081043c00144200d00b58080200d00d040c1c5802034061000d1001580302920078801000c001200f403016111018422441d910102d0f6503418075807800c2d43c05c0a98451500c4030038450f2902150006076640140808c003421440340b08469070364600504080d01c56480f20041c1b030b000e070f4508030505041c02e000e8400c031703100c4a4004060720100ea84140c03c00c18040000c01c10105140001e00c07081c034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 788852670 1250 788851420 788851457
    0x308060f0a0b07060507120b13111e04260d0f03150b120f04170c0705060f0309060702070f14032b02010b0405040b0a090201170703020913021305010807 67
    0x1080320312072180410941000e0708014020491a10046001b48c40d1000300b008580e607110386420358449945000c2018404035802c40d010340144200c00785880d100c0180c0703151030b0318050f00420a484151100038119032801c0b042c1840c44ca00101c0181160b070000440e54212409070303610009056043ca00802c0b5840404500440b1101903401650001c0000c240c2d01c0c0d510f00300c0c4001c0e40c2d010480500f02c150b20300c0d080e16840f40d500001150f000e250800010803100750181840054003a0101400c000c1c1d0b201c4400e07030f44240fa070740101e4200b01b650150201282c9294800300325030301118807500c6498102810484045460341e0214440b5505210302e860b00d42841140d01d80d00140c0c24844030407882040d146000203429180d0105031540b10318034000030080052400aa10764100c1980500016810714901c010f0f6000720055078504000d2181c14208901294150001c0908901c01e032000c0300d5401c40009000240d014500c3c941401000ca01c01c01d11095124403801c80d0b103c0440c0c5400d280c2e4465400000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 788853920 1250 788852670 788852677
    0x40603050d0e040b040e120c0307020405011d0a0911060a02070909080903070605091e010320031806040b04030f020709060305030703270608090a151b0207030308060f0a0b 75
    0x8001048980b034480856181ca031180c20310b00d072801d135810700030070000c040c1c0310f13403290f04002c00040c03080400b1540411201c0b0030820348041640c00b0300100955619004010306106469000032880c0c400c040008a030156140038003020a680803644000d034907900402c01209800c40d44410003184280c0c0760004e10341c1618091038000c540034000c0142c1c0e40341240103060424031240c00903014400c08101c81600c1e071300c60040108010320081003c5220641040040300680003500301100d105416010ba000000422030085028882002180c8403070016a085a525188115400360811810200244c0402c1c003036041030012445503c191641d07151280d0030041121055002502d2030b510100e0484101342d08824a00140b02148800c25044446401910a4040035001d0380c01003000d00004980d0360030b170070000c0d0340c032403980910040b00040744040030f00000e0552042d0340464840100700c3c40349060002c9550000c0c0c2e60155104070321580e40206100400030b0005070140c00c056811000146500701c200034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 788855170 1250 788853920 788853943
    0x2030106030b010314030c030a03090305120f0115020706350c070c0605030105060715062601060902030702190221060a06081609110702030106171002090901060503040204060305 78
    0x2c10100d541907040007814950341d12040240c660042000036880d04c0c000041d903501c5909484d0120b0045081d2804884a000d00100200403845d0300c030602040c140040c131820705a8007410842c1201c80c08105040341d484c80b6074491080800c01824003640580c01010b5600e490070507030324601100c10501c4008600482d412140300007102d001185000030003548480c1c8000400161400034150350408001131218480c2e414001c082030b00290802e00282c1260300f1401c001d081801e842e480d1880005c035003000d030b245009440c4a680d482d000d40410928042c0c420b890041589600824143c0b14a0a02009011f030004041c1d82c080c415440790441c515810f154624001e40710000b07400e180c04c1000d506000c1e203600b80c001001c180c02011713030f00c160b15208460300c800b122800342021484c0e000103491901c5078070030b1100c081e405509141d00410344400c04a0314041e07602c0074004888082c514200940200d000b01001160310027816001001b0710b5200d00c0103035420900007040022050741da40d440f1494003034a610f8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 788856420 1250 788855170 788855183
    0x1b03120403110c01080408040e0a0b100c0b0a09080f16150207020f01090b030a1a0604080c030601060c05031608120a05010f060212030609090f01050108010f1a011d0103090203010603 80
    0x10142c0321110601c06000e4058080c24108880d041980e0303480c4030380c012801159042c544080016044d20001d8001c0c100550300540420b400d500035000c001c1854181e84016900081918040b6580c074102d40704205c11301d03400c00d0840f41030484614022140c1e5000c115400c00300e0190103800c2c40490344070300e14000003e816120050f40e03020749105002d085408181e800d0f060000403202000028240e408681d0300125900000900230000488801c034020107148190b008040801c0129088100081c3c00f1042c2000328100c42a980e6600c0085800d03039420070004240e030f0018410007109101c000c52140b109485500f0301810611070700b01c40301294508842c007020b4952104010006220740071140409001e0380c1c40603000c0e004143e62040020300c0041c0c0b00d10300442c280c82c0001c80164061007034580054428000f440156507544070b2501a120790898004e85a14110440c200d0011346001100300c90301c10f03160b043c800e0702d4107203581e106060080c031032078149078030307032031040c00591342886044055841484e = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 788857670 1250 788856420 788856437
    0x16112a180c0414120d0525050709060e13060b0a0504020304060b0a120503161704090b0316150f0e150d0e06041e0302070b0c0a11010203030c1b03120403 67
    0x9190180700140c8005940640300908000c41030413804107188407054004c1c10142d81c0c0b103160713905141032064214004940d412040c040030082000c0850385804907a031042c001d0043c0394031804203082c80d200a031429244001c2d0a082000002d640b600700c4188200c004000c0106669a00003003800c0e40d00c02ca40882c0c0c141c1d643d03228001c461811410b0480546240345600e1618186660f5a40d6640f1407a01c51402541c0d100c005202000038401103103424103034100c2215115a5a0103400340604456803101d44240076603da102c06d03110216501700221000c0c8200e4a180b6104481c054640e01c500c0000e070303010003820300306484450711260084403054017624511a941d5045a03d0581101c0c00c5550a41507a00480c040c00301142a100302011908103500b8415850003451800383e18103110380d44903000340348003c0b42030107811102003203504029026080d505441d030950703001242c507484215440318400806102c811100e03001200c020b180400400c080301d1609032400301e030f0410703400304980c1103000400c0c04 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 788858920 1250 788857670 788857679
    0xd030c062703031b12020d0204080a030f02011b0906050c0c040218040f050f0c0c013206121e01091a012d0905070203090916112a180c04 60
    0x14407138880040360f04201180140044440140b440d41014050303c1d0060700420b10580d070500c0c5a04980050281104440007400c0714a030240040e5044e00d0464050f51a00105c60000480d0304211f4202100c640d4030415142d050403001e81d0990001c01190003a440780312000513050300e4500c001c0881280310390064002040c08403c0109a803520b854500d085810710090080c4081c1e420700300d980110030300b0425034555041da0344050040544d0070028104605c06001060b0041050b0b40f1080508040700400d60103960340300c1400f20200215034025443d5102c40c01803151142c0d551840485405840008540c02c1c5d815120300215050031302105044000701c1c00100001044044024502e20450031800460424507480011100c02c1c0d10500002c103440d8400100410310034422621207881c0102644810b0500d1074080303000396603a18901c07012500901c60003103400c0300003070b99405a501090f4070075000c2d84141c20956546002c0340b000e0750400d51000380281030302d60311f55070340d441940c101c0200758035907161 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 788860170 1250 788858920 788858927
    0x50706050301090c1b032723010305060a1e0521010b1e040506060f12011404140606090a0b0a080406060f15032703080f070306050d030c062703 63
    0x90207440c0313040c403545089400701c85004032141100c02d0f42505100720307a803008101c0c80d00700114040791607034039a110300307004107403100c3c08548042c400f0036502030070000311f072220300540807268151100e51f0301a41d40d40382003000d6100150703103011040d0340d5075440c00d80f5a0349501144140d002090092401c54442c122010308140074451102e00c484211031103140b0385d0107032488801d41110320b5070250150751a400080c2c1c990701c03074404681100504880d059915100301c00300075800c15080c040c04c0580c80b10100f01c80158030f014020400000c201140344605619000b00300400c83c0e104020507031308410b12280c005003400b1490003501c0503841c96200d075000ca14061a00e9400c44ac3c258000706400118200107010714a40c0700d041d0b011120007030400148904040d43d00b80b55050f0003000c441814020402c201041541c04a0042e0040d00b482d000c0352019180c2c03140c158151642030003515008416154950082446074a0741c0420500030700e0002005254050703030340c020341684041404d2802117003041c81c040640c03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 788861420 1250 788860170 788860181
    0x4090c0210050f130303020f0714030c1605030304060e12060f010f081612110901090902040f020403020d0b0c0408010c27080607050c0f101413030f030f0905070605030109 75
    0xc0b1079140645850a10741e0605130304d4001001508059003c20700c00c1c150350441c2c084802c900e070040c51080220a21540c141c0d900ea2001320410303080d0080100c40c10110704400b10960681d01e008003d141041d00f00a82103d02400d44002c4550250100705400f04140303092242c5402882084000b410f2503040c040709403605007069100e01c100b68405101622008000c07202d0344252003411220449000c0c250504002034030040c041d05030322074251800000d4070310309503000d21082842610107101e442c140321b9040049004501c0081c0d0085221101c46c0b00168000c00090760201811901a06081c3c84080031400c50320304040f04004540381e03800c01281c11220317600000060107491310380c01406003040405038440d03002400203828040d001c524401c540c0e100313019560b40d030a010030403104070002c0030801001601280b04040040103040000c103000c901100e00090086070140c84148112001c40b004400a0150750301c564422503403141080001001409100010b000e150748041c0c03a541081b810a0480f00c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 788862670 1250 788861420 788861431
    0x10e0105030d0512061002100f05220b0c16140703020111030a230403200a050d0f03050f040909060b04050105100c0f17191206060806120304090c021005 67
    0xa05000c06030302402850b13940382e40001c007036800d083d400c058040c00780d18010040914401c1c0d503091403500207803040c980e442107102d03500c06d510704000b00c018280a1403217409034000107040300004500046420f0003600003400c001e444901c4c100c0040043d40c03035080e20084c1821081003aa0020b00301001990b91001e0702d2921424610051440c240d1544005410392000007500c86986154407031250280103100d01341c03801545c024107140e07900213000811009000d080c81001d442040d800740040f699040543c0e41c80d1b201540402d01c2c83c2440011346060300c1c1c0e0b1704449000c9103c1c900c204008513250400340100c0303032014421000803c03076644220410055038416040076004d0f440e9021030b0611a0390020103083c1030340e080b4074401c070005403034100820351500c4615915143c0707600156030803940a0403107040f41580400d907075038200c000e080400300c400e031800d901c1910300044480010178022715211147c41068007a1004403460256940901004da40684a00380b001d42c109072000851080c10340a06a07011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 788863920 1250 788862670 788862677
    0x30c07050d03020703090e0c07170d1a031507051e04050a030f020f030d02071e0306050408130803090d060f241d06031504170d050109150602030a05090406030605010e0105030d 77
    0x34602000a11614009e015002d40803035211180c040412103103130100c4925400c42d0b10309100760394030080c800036081203120f00d890091140a44d009664080100c100b400b40156039100d91400242c1402048010f0840081000c02d401c20440000c2c1a0b4845e420f4600442c410740052094013101e0040220b09441201000d0203508105108005036034041200425110400289002003600b094245036540e0035802c0100424603000900041c058088003a2480ca1070800340d080c2484d490342e41c02c3e5202d00804a5540d000349500c099500000e039a5041405070f20400c00380043d84001042c00008204d4810070f084000074280f034028424014802c0c10140501d136040052985400d041d00400d50f02c00710180c007074520182c100081010032009600e00070501140f080702e40c0d103926142e80c2040040c042842072400c4207151898915084052141c410b0031507034650040c604003002c8071400c2d515603200b5a8680d512903034902c80440091890b1040c0e9010300f40780d24607116558140014145080c18158924060 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 788865170 1250 788863920 788863949
    0x30080f13080a03090c080a0809150909070807031b0e0102010c03110d0203040828090501020a0c0e1009090807030806090411040902120f06060a170a08030c07050d0302070309 76
    0x3003480c007000c8408642c42e502d070000300c07500c01d03080c04002d020303942d085480d0500445481a041c40465005008010801c54519041c5040c540c651500c41c4a4103111a4000d10414002003c25001e11031070360340156541800b01d81d4515141c19183c030382c0251260703c400b003800c075001150196030911800e622500d041c107040244c07403101031100761540201081025080c0d00040000d0801483ca001c1d18820b4000b2021410004600c02c019000070a12408034000607040d80c00018466200182c6a01d290b604a61085205ca040081014145000a0409841c866034640002e13000f401e038416050050301980005d5110801442d0042200d400607028600c110460070030b200200f2451812a01000001c0b140014455100d1000c100310144443c0d45040b5401003405443c0d6414000c5107180c869101103580d03151803922809450041c602c0c500a510040c0e02550340c070030000e01204010b40e001010590410b00b0680542c0e105490079044e10325580000e82c0110741c6104054210081201030401480e04080 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 788866420 1250 788865170 788865173
    0xa050108100e12090a12290402300708060a050a0b091918060f0f020c030a1b081603020c0f0f041535060c0730080f13 52
    0xe0311207010440843c61000000c151026943d1083d6440040c5000541e1a1204007541041010181c0444007900244800c4000594641d0b09421192183c2d6000b00b19642009941000043c50000712001031403501d4802d41072880b1a2007042190b00500a01c0007c00382840c048050800b0307608081d00d0031504d50b0a0204400d51a550b20080b60f60114460070b03544100301039203000d0310203040d2081c1801c141d5032060800400303114081d0481d00c2200b503040300c00d114508010246038100d01c109000040785800c2400007074019403045030088440f91809811000500c40d80d26542c0c030302c0d03201c9050034401c3c40d14420700070105074040c4108040841c0c111140c0036001201e6010034a060010108a03110b29500c985050229120201010140c1640c510380a07000e110003400f0390810420b80043d001c1101000b6464289010006040d4403803d8980e0741c035828034074243c1e90041c901d0f04036000301030050040180b11100038a0340207003d00b86c032040e584042c000e0408014494402c80050200c00c1d445202c40f0f038040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 788867670 1250 788866420 788866423
    0x10b0406021b01020c061e040b0403050f0d052215020c130e12031e01170c03060417030424020403030305070215010b030604060b0f180109080715030902090a050108100e 74
    0x440009554131982d80e00e01f0700c940c2d084400940f00c03030300304110080f802007500c0034048068020750348500e089458141030405040c0c0d94682100781000016800c11450704501c0c111001040e04610200c10040c102d80c031600410740441100a81000680c040c800c101154505072280701460400888d04126903c5041c03c0d00b0384031521140e1200c01c5a4000020581503149050525440030b81440002610b584509a41c0c41c10141108481403521072001451b500f0b01d00803490a0095600686100680042d0306044e02c5039003004005032080101d0081081c400c0c1090941d1800c0d11141580059640e801d514014040b20809480342c0215403010010710044000e0b00c00c001c1c1520382c105031841d12640c51100203809401d05401000140b40e010411204a401540c050a0752948416108144140341c00c0111011211445001c2d01540b020f00c042050b42c2c1380c0041011040191f02d40420403031150340110b84200c0050f82c0c10a142562040104400c80c0213002140c40c0d4545200c007884200c04000089 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 788868920 1250 788867670 788867683
    0x70915091401050c1c0f031a0d0602090d0c0e070305040b0a0e0106150306090506040b010c110d0b040510110901050405041a030706050301060e06043605010b0406021b0102 75
    0x1032112102150603035040e8052815100c000c0c00c400c0c00c48032176260b0540071114003a0000910000314040d00e080c03807100b900a00640201da10210302150128410b40c0c200064511100c20903550313950300b044094000d423a248441c400c0380740690017a01581c0e281c00da250b641140010646010145400d040c8400101c011504a0700006116404560500c0c0c0c16402c2d40100556840102e20b911040c08020301607806030411802c40d444140304101c2661541c062000b5250f80d48060350000f50540340600000701c00301c07500754103030902a1221f26403911a50354907012079000c1d142611640e001c0c20340325081c0d04041c000e1070881e201c000e07086810301a50700c5c00a130031401b50340650f40c03140740c642948a0050b500b0b4490700c40c0c2000c00034101d4040b1940d0b440007030f000e54000e000741720014549140e42142401c05404940c02c607210945008100740945001450081d41e81244107595003200e12100300c1441180100342c0a003414880c19a604c0d40303007020107071812050701d00c504c90508400000f200540c0c0c011030423 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 788870170 1250 788868920 788868929
    0x20f072d06051005060c15010909030e1e030604150e011118030c03060f0f090a030c06240e012117250506060109060518010f020109061407091509 64
    0x704150300e0f210241d2618282d580c200303981042000c21516000e00000504104502d0b510100c0d00300f03a601c1d40b40310300a48400c950302802040c410351444482c1d0409905000390840d00044140940d100c0d14002800c0800a680941da030b920320010816600200d0f10610074a0401a4002c11080e000d41c1e01c04651030180c034a16012104008042d802d05440c240008088200b0080507209640750004151545082c26186070070800650400100c5610001418400003a0580c90b803003081d0b0101d0741c07490041c045003000d2901e240400c00c0e054030300010140c0c11360003030006035440521540c1800844011100c2081c603d840500f00e070b960090105a03000301544401d00382020282c5d440a82000c0048107850714400440c0100340600d89400340200442e0b0140204001d80e00c00340ca403552000225181c1c0038807014250008034600ca07181d81503001e40d140c080c0044550002140e101160344580c41140c1030710711440380d0350407001c1c108104a6888005080904041d800b507002924903106d000342028054041c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 788871420 1250 788870170 788870183
    0x7021912020c13060816300b040b090105090304030201090302061e0403080406020105160509010c1b081c020f2e020a020c01020c060a021f0906020f072d 67
    0xc902203500d1090040150344400a00004007a04001d15114001c20261050941c54000c001c0259451000c01810b5421120b4011312161100329040c2c5a003004507004c0360b01c41e01444985a00e00006910103010f610860081211504034905410007a003902c100620606264000b000700744010f0f0781104442e815283c05480098079039484409100700f60341d06459500d00d0141c082400020030013030703200a000340c0d40745074000d11450300d410101d0741d4580141040c13078022170030902810031254821281c0c100400d020b8a008040d4020140060490390042d40201f41c844e0003035400c840000750240c445c070100403460b02c01010b001d041458040e841c0d1818807041c1c100b40a075448a45041080f1119001c01180074100465031035800080c080c3d541c1c4a00100980540114188182c0a01c1e000c4e00303441c1400125005000620710742190650140d0759401070840c82550703003900b5000300707120344042c02803c200b142d00e00e030342d910305070410301458990341402e071744003000c2c0c002000c20100d140500080e95607030060 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 788872670 1250 788871420 788871443
    0x16140d1e08100b0301030c0303090602030a0503010302060904061a0c010e0312270d0804060b12061803191817030f0a0215070206060a0e0405120c03040e011805070219 73
    0x1c1c41401c2c00c8a03280c1c05454028400b000100c14031580c0403404046a210f07466140d4450f0b658201a6104c4c01407141150114106100410141c1003090081c000b030840104001043e03901c1e03400c0484490303140301d030300c4d0760b40c440200d501c100b415400d05c200100c4800440081d8100300c5000c514000044004012110340180c150742080405403c1d00302c40c1049552070192038404000504c0286280d20440e070607100e403420a0225041ea00b80407907070300d54041c15000501050364444c0014150104a0724204c00d13a48010896240b190582c0c10001c0c0031621140c3d507080c10183d5804041e84410004d030000840c4910300c0d00c00900e841c0001040341c01c01c03000400d0294881584210582c14242c000c5c0c0403c207907000281c00c200080358007240091040a0850b20650681d440f0f50500003078000803580200300c1d44c841c00f2000860b05840000d40440c0c140541100d00c0d054440840d0145101c080c0c2c828101c0c1c04030766440117840b803814010305502090714402852540c4d21002c1c03000882e00c0f92000a440380c007111 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 788873920 1250 788872670 788872681
    0x20403050a06020a111015141302130e040b010503071527150306050306090a050c0d060b0604090c0813020d0b04060e0304080c120f1509010216140d1e08 67
    0x525100000031070800a48000380c9003100c502e4098050050747c40c4071005150b4012420682c9055404c039a500e000d010040d81c0188400e01d2802503100e9090f2418803c0a48000280324101c0000248524810406c5001c00d514003014949400d019401091545400d2101580c503942e04ca0400c0c10b90f0900d111003564a890f14a8030701a40000c66040b24008010f01c2030810f61268050300b28104540054003115519501c0d0304049440d03a0401c440240180c01560026480f0320304160f001c048035004040001e401c0307060b040041d8899000e94007946203191030340e540e405410340284030f0607802079801c034070314007441c01c03d0740054412135500c80020101034420000c90203001e1b0030350101144a8003101101d039070f561540c1c0695234942c0b00c0854a440f03014000c0500d0300041c03000c501c0c0e03031290b0400c07801455594000300d00c0c41c4003071000030b001094a41d400e104140e01b0301c0d941c42c016141280521004400b50f4400d5400c20b050140000d0b4903404d1160045100780e0011102d8003860800e2060b01e004110307500d1b02c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 788875170 1250 788873920 788873927
    0x151a070821040b0402030d080c040303080604060b0c0a110603040b190b10020f1014010e25030b09060910060e0d0f03050c060702010e030904020c0c0d0c05040609020403050a06020a 79
    0x180740d41c401d401c20800040104211030110b500d80610f00840464920840310f00080394007a80031500404500300902c42040003900440c041c42d0803074030041c4003240042d120300e000c014039000300004007a03546c00710000c841482218100500d90344000d030f8800340380d4a01034845403640c042c0a001c0703002e0051a4002d0100307030041a800b410f25210010840a0404003004d0001c3d41d40b4111001c480490091154542000d02c0e81c0c85001d02c428046d0704201c54580ca40619030f1844a001400405000c0340c000c445901c455007202e034143c007200d2607180011521292802d000801d44024211401910030009000103044034801d00c1049a038686030003004685500c02103414103031407403c0184601d40e02d00719034040540000252081850040c2181c2607030781c0f5110201d099410000810b50035402c100178100642c2031540007440c00c00840021903807138042000104091408604081d542101481e0013441a0b2a0902484008000b04c5805605140c113513120700784c42c1d0100740070041c641940010340c901c91900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 788876420 1250 788875170 788875207
    0x3170705042309100503010b060316030e031c02030703061202010233090d020111030412080406060e0925030215180d120201060e090a0b040302070b040801151a0708 72
    0x4003a0a42119041498020031381000a01030207110f5407c081c02d00c400c1e0300305102a2031044003062071001010704824000e6008040b80003c00d001804100000f00e205244201007031045181074800580d00d1814113002021030700143c0041c10b644050000140250ba80001e01101d1003101141040c280c02e18050b0b5214440380c0380844e00c02441c007000070408001342c041028100c8960540091010b16481c0c000d030081e42c8401c99005103040c50901821080d5403040130919800b0b4070440c030000301181c95002000c481d00b021600444a607001c1c50380300e1205c1070031012440d040e01e41c8000c108480e6041d5030020b0f0500c01c00710703681803900501140c9101120881411102d8410b0040c140d001d80340c040307042800000c520185100059030910000080490710b20705218811410280a88000c540e40d07511081c0c0c030300c0e020b80290f00318840d80b00081060b00c0070303d0041008100000000907100500041003800b0343c003507400f500788814112495088802c00e4070403a02c1d420b80c45800d81d6580c4581c6040070800c0312 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 788877670 1250 788876420 788876489
    0xa02030a210e1005061801032901030b04020a1a040522060308030109150509040f02010e09090c0411040e061201061d04051614060a03091205070317070504 68
    0xd050200d140b4010801050109002141210912140d550b14040c01903402e0060310303d0110324000c00041020920140a0a10010352001030b0304c94020b1101c2d0008941c0d1080c1c0054802c80940c41c280001c61505200003001050f000910820703030381c1005100c00d582d0190344101801840c85881c041c04410848000c05a40c0c10f0589c410003032141c82e070070008a40e4109000340c01c8954a08238140b000707181000c6144089403002002e8144968960751409010040200d049060001d54450003095640c0c000742c0078440e40f62080200301c1c0a059030b04000a45080501d90a0505000c020510154400301501a401001a69040401c5a1400419004103000c0d4040615251607040b000107840c0c13400b0780180614060400c44403052588501d95007003607002e2084801031003030303100041201d04000b03000d000594414200040d03038046039101e40d90a4030344403202c000040ca00041c1c15040640200103c0420f0b180b03048102058980b402c00600244144e008441058845400a100c0c00002c2818540080b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 788878920 1250 788877670 788877737
    0x30d1d0a0305031b07060221090d050105010b0a0e01110a080a090e070e042d050a02070f0b063615040e0d030e03070b060f0d120503010503120a02030a 66
    0x303421035980c0803607030400001e00c91030714085c00100140e454030000720700050800f044036209030b10742c006220f0b0a403640264080c0d9008002d42c40e880020640a1296030300808110007401c0d80e40503a9003004054019100303215041c028a8032004500c00000298540d009521000c11030361082c02c003c1c190b5900100d540402c41c1e03a8142d00c00c001220764400c10100003000c0660f000c0c0141f01c051482d000d41103c240c0d2881190307041d01c0613040320b4030032540c112641080244200600c0e000c460345070a85410300c41082660828590014000c05040034048800d007180c28840d0080884140010812500108585c0302851840c9070b010405428600d2141d4840c0140200108152001c8541581e1a00c01c041621404a440c050400c2c0c11100c02008541455600040042c83d40d034a44c4104407124080c00c9403a40c200c8070307280f503920000d4100509040c00d11303510345900e5103d6160508061500d008003241010b450710512101e08e1041c1c001056480e0600c00b414a4010512074001a85c242c1d2038150760440d24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 788880170 1250 788878920 788878927
    0xc0b070207061b110904110a06050909060f06070f15060806070306061112160614090d0f051c0b1003020c0609011503020108070309020a090b0f030d1d0a030503 70
    0x10a40004416084a04540362280c4411002e00191044214040050b000c1c0080000d0007080d8506960302c5c50b0311621440c000b45082c80000040703481c88100fa0084c001240c0b0005006c070300342c0340a051680e441042100da07510f1040d108000321780784c3c0c0503900c0c0003011007615a07810001c000040a201c0d1190000680030800580c0e20080c0558409040c0c031000f010030302e491303804030740644144080180c040290009003501d41e000000c10020703a020800303042c000c01504250070005a4039004110414107800160003440c02c3c45000141012449005031040c040c140590803226034000302620340700707580303030b4241c03104100d80866080141c803400d2070b481e5004800300c0580a850350158041d0049100d403004595460b5940500182203440c81d0801e408086400e0004100640c42504565800081480d002c00d40106a5010407403802c2681c001c4400280c50304d01c0361405080000041030080c900310010848203103a2100904045072120407103070041c06909044140751a514181d5006592180c2100d070b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 788881420 1250 788880170 788880181
    0xf041e080a0606051804020102061b0409050c0901020d0e010905090910050115020c030c03070e041b080a06230402040e010209060c0115060206010806190e0f0d0f05040e0103120c0b 79
    0x500d42401340910400b8108504003110544e06203c51141e41e060f0001d003c21346940c06c5588081041070717900c82c1100d100b0080410b40e03600e1802054020300107084c080381c8402884001900385009601d01c40100302c1e00a0f04003110b40c1e8040b21110440d407040d54014040d03114000458213003c2c083d000c500c216030409000281d82103081d46010f4540206500740d46140d6064810540c484090301e0026130b065124810502c20328080e100d5183d0460710450441c07210102d99501c5407883c1c080c1d41c1c8045856000048540107010f902d001d000000000c00c041d4908404480d141d81d10781e40c602070800780c010744d07940780038014405095045030401d1500401d815224400960224040c2c441412680e131104200301000480a0000520380e05940e4144c1c040c3c2569a06c80444400050b13070502040322050b2a00484c0d640881c051190070407a0f4600000303445019100c000241c0070076012612841085010441040b44188080c07e881c19294480e051a02c40d854240c8221b4813005001340c050600c0103920140078 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 788882670 1250 788881420 788881433
    0x2a031202160204151a03060102010b0d030809012d0e2d070506030405030f0702040b0621070f0906050f130b070b09060c12040c031202070801050c0f041e080a 69
    0x4186600c2290b007840030380c0840c084800981d40d14030030b500c140011005d0f41c03c059000c0e840990760008040c070000650b01303d80000141c1030348400b0740075000b1551302403e00030b000c3c00038012020403800400d0100e000412283c1100220711a64050302d1840c0ea0342d50103111102c006001d0404505030b5141c1150701c4480111000c3c055070f51410140c4414403a4400004076800c00c081030b6031240d50800091070601c041404180340f55402a8400c0b60b11540c0c0d0b121002c007036511903001d040c80014080d11f2940c074001040c50050484805058581841b68003090520f900360710401c581c040e07030540d2a059441d645003584010090041c840f19001e4041c1941c03000c50407080d100003401c681c90283d0318104940d2207447d4030f0758a840040c4c030101c00f8003904004a030107416106500c26080b9200f9240e03444c103e6070300d44880351031045280100f40113030000c040c02c00c0b480c0e03030074024640c01820b110703a201d1030281c0c455000e40140c8298491491420700a1241c1d6001e640c801c11001c0041138260f041d01c0c815001c1c0d140c0362 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 788883920 1250 788882670 788882707
    0x90305060c1b06010308030c030c0c03030a050a0c110c0103090303020409060b070314040e041103031c060f270c120c02071a16110409020d06090c05012a031202 70
    0x240c048510101e1800c00b100015000b8100c2c1d0700054154503588581440203000d6200600c03140310300300c080110710080e68003080103610510f81444001007030b08040e0881030aa03a140038084040000c0f0084040380322030041503a12440800b42000202200345190a9000c5d005542c0b02581445c54001e00040003894000100f5105101e80d55121410303002115100840c000c034040c1c2c5450403102c0001800003458040c000500300001021241031140c1d031a41040c1141c0c045480c410360580f512003c21109282007092400f5100000da6415482e8444003044800d00000509201c22600e4209010b0b2503800380340152412800800d05109100360240c2c00703566002d9500c12800030b0361000305001030820440c3c041e51400b85039441d012a580030540c8810f6014100b0b00490f65010780d031282c02400503a50084002e005a00c24000401c416113a42808121031220b0380c4118103000848c110142000b083c00300c0082124030720040032403150781ea820704540629141d015512803d20005000d0844000007440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 788885170 1250 788883920 788883937
    0x50d090515040b0711030703031509180501050702030408060f100f09141b0702042007050c1f080a0905030906040618060e03030403060513022e02010203040b070807090305060c 77
    0x75425103441c00b040380c0703070150707046170300c965030400d2200c1e400080c0710381c001c900030074a0801b0222403942c81e48403c02c21900c0c0e004a03454200d50b11807410007080801e006507940b04d540d6001440c1094a40a280750300e070000101544003000003400001c510030080c10201001d8200d50305100c1d211381e00c4501c8840100351561000d00141d83c03440018000648280e140e54012080c05500c1e410141c542c3e00380700c0980081d818806c8403058540002c10b21000c1076000d02801c0e802000144100e940e0300080c0b01c4000103088511141e09074400c00d100724590013820a540210001e400098400b060741811403d41c062880c12a5201c4400100010f0103507100c0031903c0001c0350700d5541c04001d66900c0342500c800044c40c1d401d0360941c01c00e00c000c202107440c4d507200c15032007100c0e00c2020403c89a1381c0d0000f154000000e03142c90703501c09461042002000340701c100c40c4841d0441d00003149903040944400401c000c00500c001c003000b4440c000182c549120303c11b1900107652003000c0314801d06203050200720f41e0b00030380380 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 788886420 1250 788885170 788885183
    0xe010f021c1a0a0e091507090f0801020906031f1d060405070806030618030f040f03050d05090d0f02011206231e0103020a23070605060405060108010501050d09051504 73
    0x751a8021141d070081004441004061503d00b07441c0c601d0640031250003c01c0c040550041c0040c2c068101c01c03038261b0307c0c8a5040360307039807205007810300880e40c0f0310562030781100305107038418001d158407034444108a1350080090b16201303400500942480d440200c5c0380d04450005811440c8901f1020100c2e0100c0f40030300d108980510143d5110402213480083c21211300c2e61523440140800e51710150708030080038814129003501c4c90301e069440c6a440741c0d482a07000032400d50b1031001c2002802824414400c6030815450510f00d401503000000340100c0c500d22016210020406844085a014161110120007828000d01410b2780c1c5040c80c0b00d0440c200d0403900013403401c3e04105600383ca04000c0700e100c03510031034036002050110800118025000582584c061010300c1170002c0704070304040480000a480007014039503035004c500c1c0000c04c1e110003800841c00b80e41010140845a80c0040201381540c4080c84d001c0d0f100c591125844000d030000d1100542a401180d010305081c104941c409881a809080b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 788887670 1250 788886420 788886431
    0x3111909170606010f08090a0804080f0f1605091e13060c0309023003120105012c090720102403140703060e01050a060503010515040e010f021c 63
    0x401d0985500302140c880d80014a01c4280403021401403a0a079005078910301102e90f0400980c0c1d40100a0380950400b001d154031410254035141e0040082d4001c04520f68043c11481020000c59240c0740000e0152511070b00543d80040c02c04542c0680400011030f01d040c001800d41403c030070300081203082100c26200300e411b02074081e400d5070103409400c80d110b9000c0d0800000b00c455100e00d00081e16492030040100640a06107680302c60308102401140041c40d0910000d0352403c00050801030060704845200c07040c03020140c01c0c2400102c4170004040055486504d9986c4035102282d44214034540604c803d4081d080c0d03c0600078001512025501c5001d8042285031150341250348001c0d8000e003014050068600c052001412a510400300d541c41e141c1226003007501e9903601010340d520740c0c101804c0e40e95160100311002e07003a40070700401881d040c0d0081100e4185100962a4420020302280c0030319160368000b01400c000f5405003ca895005170119140c5243c4400070003820100304032018403a041a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 788888920 1250 788887670 788887709
    0xf0905070504060614090d1a0906060118060e0a0302120f100501080a03050f0702040219080610080610020a0b01060e01080f22060e0a08030610050306030d03111909 72
    0x40c8180c4003624910345070103030401e17521001e407803480c2d1111100ba034205070703002da41388001380000da030124629030850400300340d40c42c08241c801d14003900246124104400c1c6003403e1442070070050014140c80941c40c1c03200541300040089080135103079030300094002820780908620b8100114591203864122002e0300c0c8680f5020400c041503407428000c240064101466100020b4094070040c00340d441181111030904100d50009401c0b41c2040126080c3d0000560f40c0c150f045600821a56200030701b12000c1c8140b8808620091010000404840c001c1e000d03042e002d603259000b0000c8180071503119410324119a100d10000f00141e00b450032030350103d40f24074041600f0f554616242807143c220b02e84000615221450f40059200c1120403d42d1742545c5c820103000d82c51814030415400b280211100d69803401c11000b4400310081255500c410844140309002c80ca0f40c002c5628464031600e0300d00803074004500c4030303035240502c41c08080c207030806141c101c200242030304600d100c42101c81d00705840c2c030b540994 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 788890170 1250 788888920 788888929
    0x7030c0309081213080c1e150402011b050a0c0503071a0706150e0907031502120126060f0105011205070c03030f0f0903030f1a0307091e0f09050705 65
    0x1060000c02582c02030010364481040400c51650003044d83c1864860480c164072408000e500c0321804900c56040001031109800450358580c3c001040c100c000c0c8807000201c81d07102e4940c00098002410090b00ca450200201040c00c20060782c0780d0803030161000c0c8001d40c82d183d00702c80c10600c28180a0300a00070001031a8400d0140300e00103440b400b01031490009c1e82e6480200034000c01151042100e11048041105502030212a00c1742c4c00b4000181210707411403d064902c0413035108400d58050042001114000461040d00d04480801d410f910f903440c9828044081034a80c0b1405030320900c981402c00c1008000e40354000d040380d90a0b22040c1406c0c80d02c00c81c580135594201c4034040818501a01400021310035444200f1500030b100c8001480100c0c6a9284192010072805400080c3c03101d402408004052080041d194284111052403608100200751107107142e02c10304080699410b00401010001d0741120012450860200504021120421b006100e41c00c400d03a100d1284140219807401c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 788891420 1250 788890170 788890181
    0x801030305041e030c0e0604110415120b03240a11030c03071808030d0b1f120f0c05071506140f2b12030501030b040204091a0f07030c03 60
    0x800d6a034141c94a0305041409100c0000e82c520001007000b040d0000000c0380402c64128007a001c0305580762441c0c14a14100703c00e0f42e260803200c950081c01040f0802051100c1a04402d480d4003904187c682070001301240c0c001424044075460701405544004e208115444105521845860700c95801545420a075101100c928000e0068140810400724003e03400000203144e2010403854520b1b440f841c8031240303141302d101c00c0d40044960343c40440c029000500351b0007905420b450583e030b5181070b85402c0741111903081c400d5140400b4090b01e81e14802d040b001c550490314441c0741605090100d040070070300007048c0b940701540540e40301e110030350b80301e0791107038035010303442c02c8810540c4200c140c3d040d0913080280741e0b1102d50141d50301041f0080c0e280d42c0c03030751021481c0510b010001c12003401d464643c24080b038000d60341518403040610f8000144001070700927507982c1d001038040d0b90020704d148091410030890304181a40503d144c6803c0d0421000e001040d0070248120748540e024001a03441c113005030240c51 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 788892670 1250 788891420 788891423
    0x60702061302301e0f0a0b010b0306060c0a05030424021c111b0f0312030408030406021605010b13060b0306060307050f03100602061b071b051e040b01080103 69
    0x8411005901000350003603820146400b9040c840e6a1030f03030f114000e41e190000d4030f140c996404007404c02c1c0c01c6a0003030034041e0b4444802d85001602c2c0d8030f4542c0c2c0c0c801c1c00600c01401090f03030703103000400451640c0e02c2d40700c03e0b510441c0341d801c02c4410700b64450420554030340091244101000c1d02c0c80c1a0761110301800c46018510142e170300101401e580f00003507948554011000700c1c04024103800303483c840c50302c00c0050f000b000800325400b003280000c00080c090955070072507450780644e00a205e0403101245100880c0d0780701d0f4000c05420b46a480c0ca18003c0081c1c810094800070038a003e00c40030701030040c10743c008003034030204030351000403e400280c0200039038041d4403594840780c0040c00001d200341000c80c004c1da48209207140c0b09150015540e102d0145400c162580b0002160004041c001c080d01004043d0304200c103600d102030055981c080318074091145134001441d5558a4101e50180c0c41d001105d41d0260034000e2000000f800742d035032400e461480840c0e400344564144070344201c055000d14119030599 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 788893920 1250 788892670 788892679
    0xc0906010e2d03031201080601050901031a0c0906030a050609150f060c01060504050423281a13200603060105220308030a0e0111040504090303021b060702061302 71
    0x202c00745038900c40e007a202207014090b0780700311000909099505000070420480b6102d941903040d418003920516080701604464005c3c1071000050001c030340080d06000310180c0c00f61036080c85a4901c005416507020f400782c0650490008003d100341100103030040c81c801d00d402e540180113541c0d034050603000300c40c101034913680088503400070302002e080840c020440010382ca0300105138030f9131302d40c0800e0480d1b5080320103403648000d80e015403a84410001c409107511013404010504002c0003102c1d014200d00080d101c0d9a0b0b05101c05c0d02008200c002d1501c440074400003029071286181001e02000301d1441c3c11000c031542d10180f1b080c3d01540060b40d421810000c0e0141405065a98090040d0713026441501400680e0910184401602c680074241201039032040001e944c50f42003800c2c1d042c0599006500d00901a410721810008510020b415102158411035002c90f005c405420160024881c0035000700d02c0303078401c4002c04555000050102c0c0070303000c01d0f42100c0f2540c3c2d80348142c540303250710741200035441f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 788895170 1250 788893920 788893939
    0xa021513060918092a03081b06070302040302100507061409010626030a0806030f030409020706060e130204051b0c01150605070c05060f0d0e0a030207060906022107140c0906010e 78
    0x80340c800c070302c8401c0c0804c94805e1807400c0c4d441c1d03290300c601038201d100361100c1d03201c5080000c10702c03150510089070844d41070306046d424076086030300292401c200094008200900404ca0405020981d00000200b20860025604c107042940300c0c2d07030103003030140030791004501003d1184a40292010090340f0081520000d1170500c03192050071104014050b001941c10700c1040034028503c501800144010015140010794401103441c24100740e44266000e844000201c0040008100d070606070034001c5541110001510340d0341c0d1841542000003803002240c1060f0104118100b01d20544c1f0030000303c09104000000c155503190304a503a0311840d140280070070784e6800c0411039402e04101034010b50441070f151a0401c140e104140c01218100211078a681c0d00090040080c950107000740070203003006103051051203003004406540c8500d0a025192143c0580d54161007490000e001c0e102041e90141102e00305003081c40b0070a07900c9048400e0a0320803c20710001c01c00943c051001040c10000c003400c030b544c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 788896420 1250 788895170 788895203
    0xc19090207020a050604080721050a030809211b0d0c06020706090f03080a0501090e0a030c050c100f0e0109060c08070c1a0409060b0c0a02151306091809 67
    0x10790040a0100c0c1c022919102c041055541d1901800241050000420031145440d110488403c401c000220401c0601c0c5141e5000c9040803820418140d018102519140c5840345141c5c0f42c242c00c4990a0400200c1c0300114043c010f200b0001d1610049450b66502040d2081c040d040e1144140c07450040801c906040c00000105250041c0c45818081e00e0001405592901c420a0118070742004800003111401045040345031407203018050300540381c042107074400c1d8200c0b0580c1c507000c44c4009400c1c452203102c81003c2001c1001803040c81940504101c1c0b21481581c009489480321007811004121030001c2d0b44002c3d44211400c604403030483d40c80c10314601031a103400e00755078003c0006640b01d4030042c201081601a00c08a509620610061103590711f160141040440f0003d4101d0007082c603040140e9440d003103000440300701c480c0d0101e5007028445000b0b109241c942c441c0b21404c2da0101058100014000d401c2000c2c8011941000c0304c01e4040b00f42c0e01418800c5440c096002000060b41504101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 788897670 1250 788896420 788896439
    0x1303080901230414100b1e030706030902210d08150102030706090819020c0102071a0306040c09080105150103050105011110020c0f1009050c06030f04020d06020f1201080c19 76
    0x290480d000c0c6103980e82c04d155080d881400c003d0b055025803515500c44903149038030308003012030f030300f6003030741c0582d83c80710140c1950001ea01e400542c400d03401007540f04c050003419507a46102d1400050003110b81c848454960025140c1c079140c11540c3ca80c0414101c2d0001950085070820001c89008140d01031450a2030a680e00e40040800c60000d5500c0300e0180b054001e41d2007120100132044181d13400138041c854107080020f161a07070a400c02101c1070840c28001c154204802c0c01e40f5007010045601059105240d00200c4010fa01d41e40818200d43c00c043c2804806c02095246884401080ea400d00250380c9840054980822050440e20140d0241c0f218054140c020390103803080800d0340c01504e802507043d0441a00d00b480d403403200c03039226a1320030b500010014100b000c001640000d40d41c0509518164074103004030305000f080a805030800550700010400c40d58100c506030640d00b5800c0f074a50303004402a8582c210240a8020306100300e03500300c10030345040c400c1070f140d80c0a150380c0b640d14503060540b0301 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 788898920 1250 788897670 788897741
    0x40b09091806040b040506071106041101030e10050a1b0c1b0503030a05040e070804031407051204030b040501050a0b0f15040b07151b080606130e1303080901 69
    0x141041c5a100c180c02000c450140100742c0264000d440100b07460400e803c1a17030800101828500a104520050044203103000c00c80c0d07a0300540084a4560480c2d5000069001e404280c882200602410205c03034000781c601d6012501850504604105180d414a84000300a0501c1e84600109402c00300400003c0d00c802500c100903940c0600340304100c0d5840b0003003451504801d24400101d0030104044c1f0801808550041e800a500c0c03a000078141029100900703124508624000c260302e001900384d060142c00c02079104808020b17800c0d140c0d9955030b41010304142405542c101c0c0c8035400d100202e4200e01060140250884004084400000d807180c100008908c0700c032071640800006200000d19410b0a4021700340720703801042d0020f881c0c02e1450102d801c44202c0140950344400c9658038005441d4001d401076402501542c90390303503551501109641c0c0c541e01c0e902081c258010b120410480100d00400030030150300c00d444142d000c1d111402030364261340c681d9020303405114030f44411120079900760744034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 788900170 1250 788898920 788898931
    0x103060b040b040f0c030e0601060c1506050a12030813150b01030b060c1e0a0b0a111909080c0402160201200601230306100e150d0507030314040b0909 66
    0xb640d501c000d03010809407004c40000d000010350b41c0d950158132075014040c460b40540302202402140d81400c202801e001c103103020151007070706040e120007810011903000c074014044c000e1404c0c1d10f40f552540c0080e00c007003541d2411000109003601041d0304191204054400c1c40e4816000040001c126860303030b00900040703a07040c3c10180c40388207151b510340300c510051613803600110283c8108c1010f8111004d040e02000c200c1104c2c0d81c01180d0380f0010411030068641c20001c1114003060454024032048403d00607050014405805c200064402e039030440c07401c600f224000d100b0365030034a45040400c42240075003404180b403d2841e0406500540c403c0500c0940d035a51600b41c00b100884102445103842400d8010b42003030210b00c0080418940d0b0b0a48000425004800902091070400c109030007249503441403021100750500482c1c2d0300c1c084020b22804202c3d025050700c101c8a01410003d41d1741d51184030690104030307501138072062080000125000e903880c2c0056145004240c400f4042d246070f00404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 788901420 1250 788900170 788900179
    0x1030f0b0402040b071202030a0e090a11130609120309090c03141801050c0c2104120510150b1206180109021b0316032712060e03070305030103060b 65
    0x3440800355849101400140c00c182d600c45032909044d00d400c0c00400005100d0600307551013070060301111917200503200100001070390421310310b40380c190403a0003400e160303e802ca07690040440d041040300c004103078800448410303988080c42690b03036400314004444115005800070312041420712201d8010b8100030a203684a1134005022402d040c1003654400059a056090142290650201c00c0d001d00400c0d8000e825a041a89051040c00089540b80f50070f8a030a040b0804052001c2282e495000544008080022070103511084a16001d601c0b5022100c6c215a070901d007094600b16041090070f54000d513449500c070985030000440d02c40001c0710004103002e80c800e510413400390b40c031089558164020000a90f0158440c9500d15036880c00c0c03000300e04824620343c024890300812010076050100e500b50035007000400c41350700c20740c03060344505100710003034800250300b20010b0030340f180c18a0806128003a80040100303a58030380920340c40c0d104280c0060b0002c0e805000510101c0c4d515400315aa0480081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 788902670 1250 788901420 788901431
    0x1017241504050d0305040305071d01210636020105031807030503070c080c0409080315062208060702010c020d080603010b091513061a070212061906080d02070501030f 73
    0x1c0000f03102d101d21840c100d00190011034100204030040281c0c0e03028200c100125826200c1c01c0009003003100b01480f80714881115040b95440707804110321140e10584e00200c041c44041c440d129010341104140402c283c06080d0320982d6036a42161014003800c0c1c43c0e050390307800d155440e5070980c1074880342c82215061407801045000000118200010020781d80f18401a140c11031810125a0410261141150040d0308100c6000002450403080341c0c1c0c80000e0204035035149030404041003060203606010b01c12940003400f5804c0b080c003d88182e104580c1a00d08845031560f42100403030980d923a90341c5440c09680502101c2d49030038000c2c1c000607484940640000b84008500000541007542511401e00c00c1c04010006111802c040600d8141c100d0b0f03032074092080c00c0c940000524000d403000e600700c461a801081c02002c55441001500101d290b5204491040c10031b50001c81c51040c0c9561940344d003515113600054070100110380000d460003a40c010380040b625010064003d4081050b1000031951780c0d0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 788903920 1250 788902670 788902679
    0x190305180706080a0e0619020a09030219030209091f090816030e01030501050a0806010311040207050304090b131b11031b1c02010522020d021017241504 67
    0x1c100407001014981d40360400341c00c000c008441120607407080008203800950800c80105191000040d15441d03041c2c00507910400c0201c00c8403410920b41000b580000369202e803d940d40380401454081ea8006c81c0d00d10025114052825528000e01f42110b484520910140f501031010354070400459001c4c0000720314100a101404181307038810710044020941d003a104d100256810303c40c8502402d02950319840280c2000703100f0b581c52405210050001d01c144510518a440700d0b01942d4045510004403903c90391640d08000142c882a03000b00d0180000f00288517166900c2d002e0500004040c10b800e046861841c0e00032901000f510040c1d01091104200005080d03030724070040842c7d00c0c042e10203004006280c1300c0400118100145000071607041505120f0301e44002c1003010327002801c011170400c681c01d1510205490108840c4040d41c0500070b0b0140900d00394001c1d0302070486404028405080790f03a030f40003001e2403907100c0040040c4032180d05041c0d045400c0c1010f140721009040c1500c070381042d688 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 788905170 1250 788903920 788903923
    0x308160507022e09180f090f05060109110403020f0d0203151e090106030b0606070609020604150e030a031b150923060112020d0807050a110f03010219030518 69
    0x10201040c84500030140c80f00340058504800780d004016a1908600092034030443c008400402c425016150343c0c1c802074401c007440f9a80c400a0b18551200582150880030305249881c2d80c024420742045a0a1800341d8544a002c88200c1c2c3c1900c1d402040e1813561081c210520981e0060000201c0c1c0520981584036035400c080d040d080c1c881c80c5030ba02c0b0f070222030000d411050444080940300c0c910740c0c0c0c180f210034070010751900a0f030365212001303071351283e00c44c03804d400e2010141c003c0900c06900301a001a01190b4005100746001c1c60300c01c01d40b100078922100c070701807661b290b83d40000a0000f038114440210040b00701b99410904274020340790910030101d010002c10440f40c1c4101d08851000682c50b80c032158030b17840e0300350381150301c01310b40585119890403d030800442030706603000f0700c60030440b0400030801007003100f0b98050607040b074202c0d04501c2c400c1c039120314006074580c0020700c50200c8035000140c614050084804801d1810640c03501c1d4410440150b02400024003000900720001140c407903082c40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 788906420 1250 788905170 788905189
    0x51f0f090c23090f0d05102a0e01270b031b0d1a0a030b01180f020d0f1505030a0b04080f0c25061b060b030d02010b0f0904030816050702 60
    0x2c1210709954503403500003000111581c0c1e035400380c0904502e1104e00042980828104540081c1020105919040c2c55604880b49040380141c107000b4589072007601c000741d018852101d0501e003a00da45020051400d540012451000d0b901990489581e0301400480c450b007020715001078800c00c0c418041c003882d2844c0711450704142807805400741d030751a03000c020110100ca40b003901c2605582c240590b500317546681240d01814000c6580000610716200d0345228168019040039810200454841c2000d900e11405007407100d042c4010603042011401d450342100c0040303011124000e0061601c0109175a8007444c15500500503a00000180480d0394144074500081001c83d1281004d0f184451610021206270400728060407510300850a060083c50380000c2160480c0c0c2180290701d1000006260020240c40c001c1c11468050041d404680e103070036015044824a20340455203203209000700e5041c0001c0c003008503000b0300040c0c1d1810102d541c9058004004071740104c1490708a01e072213241d402003407100c1c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 788907670 1250 788906420 788906477
    0xf211109040216020406170a080702061b0a05070b0c031804091208040c2301080a15060c020102060f06010f0c0302100606121808031807150201051f0f090c 68
    0x4483c0c00000d021440c041c42800d0243c1071000030100c8041542c9081a580c0e0b02400c0020709200000800c00159502ca10646031000c200210100410200c10b000d552a8a226201110b140c400c6a20110ba0380010600752100840100300850070301d40b10460024041200120700758206c4c2d41c4007500000305400c42c0d0345103070074072450311010002d06181c6402d0a44080c5548005090003036500306c0500c994001914800e41e0000740307420721064070f4014908005000c417154810401d4207a81e00003072055004110300a480707000340c00342c83c2c05035150783d20301c1070b201000c803810f9000410301c4d4003000b42d66004411940029000b0b204941200806800003000c40d049034020b44041940c5c604902c8148100c0d0144151800040800305a19681c940d104000c60101401c449c80f04c100030640c40e20385141c100101030040038040428000210a104003900030076085d541d0710704a0841d0340b0384141c20700804600408941340c1d50b64014443d0b150040c444d00a101042c0010101b1402c1c3c6060481801c00907942d0b420712 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 788908920 1250 788907670 788907697
    0x1205010803091002030a02190201200c01020d090312051308010c050403170705121b03070f020414070f0c030e030d021b010c0803010e070306080307060902010f2111090402 75
    0x101c101904002991a43d400746100315481009002d00d42c507404a50003400100c0040010110061880140c80c1d148400400104030101c1d6000304101000004240f07400b8142a02074a01076101c1c0d2100b218221683e010141c90030540c02207a10b03410f40300b00c0041810f9101680c801c0340c85d5071150406400d480b854509807000450220f424818440c2c0484404841e08280100900e003143c15171310192104000c00c0100701c0e0400100b8119003841c0503a800b003100c0c403440001d036941d400d4145090821500450b2059000c1d91405882c800d0042111400305d0052040b612004003120200e042100c008880e030b0000c0b410040c894041a545031000c2000012000094015002262128545e14900c01ba08180941003000b460315a201081003081142c1c10754110011103440c0b0707542c100c01503015002e10f40c0203110a120001ea42030601440d41c0c06a0381c114804d13611206c044c1c580050844501464894200480041014816031040c0b0381d4007a520301401201454200101d00c4009012130300f1034203201a62 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 788910170 1250 788908920 788908927
    0x1e061d150111031b070501091409091e01050f0a061805090a06090f0311070521160605030f0604060501080a091406010602070833040804050a1d0f0420011205010803 72
    0x13800c00d0152001401082c6400c8001501c1c000c080010500b00a0f20700d40581d481030040354441505002e0306500380a03010300b8807030344075401c40454001c01d030840782101c26880d2400030892644aa0250300112003642c3c8000e0f40d02c2a100310444010040030703240310b0041c41020b00d040d00040c160b0062201030b5009258240c070070a0b003802c0282040c440d80610030161b03000200240826035a440b52114080c00c10030303215000705442d402c000e14048084607406c001e43d0280500080c020f03400001140320f00c006242341d54403500c0d1607040c03109a8606014250102d81e00c0d500284405689a000c2c0520034003420188124059020b101800c0c141d00f80c22101c01a0481e4205020410041180f80000c004e0041801c4565030810311513030140c044080000c480070041000704082c010524103440161034020045a44259281190440441580074007810200b00d4800507401c25022007409110f641c024000d4000c030b5149000000403291041d08136411700418540040c110704980c07003428040c142e40c0e0002c0d41d4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 788911420 1250 788910170 788910217
    0xc0d0209100905070c140f060c130f0902040f060306050604031514010905060f030a050303070311311e090509031204060f11031006030b0d05011e061d15011103 70
    0xc10003c01d0946c0b055a0300031002400c0c0f1002c005171040c1e024014995480c2c40c0c0120b9144003480e1360541e8003000181c89500310209a404003580140200d8201c514264406552000305800b42c42241c441d9079444a0140700410116154000c4141110008032740040c00d00350350460305a00d03440a8100101c42a624420000b207070a03c000890036840c012002481050040d43d40c0e41c0ea40d210040c090410145c0301d2401c3c800c41a949000c3c1ca0340c1400140c000300ca140d10040303900a00d5100051696111124180001103410468030030b86180d54400b40e07080c3e100c50403d0b4031003001e44000340c55001316100c200302c407008088030044c1d0280124450705c404101c3c076800c2c804d51400d90703504a005000035401081403125881c40ca4007840304441e040d00740071601d0192680010406900c030741028002c0e5007411030b0349174170354038150b4080e100250f800001c02c440790304c0c2c0000c50010006002a55500a49800400c80029040ba032004c0315040c1454035041c0321041d000b01d00d056400c2030018070a070288540a091 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 788912670 1250 788911420 788911433
    0x10b04050903040302150901031d03091306060804020409021207090605030c0402030c2d0c030d0509030f0f2d0307080a140a0b01020f010e0706030e0c0d0209100905070c 74
    0x54214401400070b5080030b00b503130005a088802114000e034038450014503440964002d0708906c105400c942d1104006895202900d03031240d11940059205150002140c3c078400350f03920507402560a07a0361500520380e219030900000341030000043c3d0b482400340c40100e010324001c005080103048040d1000c00c00380d2620050501e030401c10b0a07505d100303500600403c1070a03103a80003030700c04c1c0541c100740c0103541c4081c0141a6482c0c03103030321a16000c500b000043c54103034010700200030403c60600040c2085560780301c000c0303a52a4003d8942c004441103040122010180105016002d0002189040400100b1b107201c1032900300c44040199505240200400060b5500441201e9001070741c40014015502c031451240082803008180304401603680c00508016442004859410004030000304040d6401ca4142a5142401e104d054002030030b01040000d104c0c8041445000300380080c044c1c0c1780f040140c0e8200107203903100030300f05414402c01c12400100c920190080500500e1542c0300c1d001c040f2142d04160 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 788913920 1250 788912670 788912681
    0xe0313050310060e1b070206160311060108061305030d06082a06092b03090f061e0305060d1707031d090402040b03010e060405010b0f1f050d0b0909010b04 68
    0x6041051600ba020040302c40c240200c85c2e801101100b201c030940201c04440006400b4220020707411131301c0460404d41190a03000d070400e2881c000d8880359200707d040040f4541c1d41401740100003180c2c020401040c0844040c0140c581c680d0f01c00c2050b241000115881740003100c00e2a0700c40203142d030009120b00c450400d0800c9041004084517003c50819078030402040c0507204090300301d401021203451031100b00c605041aa4074003106116070417102050360500810300c0d8000e00450604110300d200028a090040161540c075040c1e2502ea01d12011801100394010800140081d0b0010200401100014210703441c0049008500c0c2e0070b00c5e00d60740c190500420000340c200000100d40300185800b4402d50710000b1541d0303c1541182c02180300802c0f580883d01401715649035171040d1160b0750038441009019000100e4000041c2c0d1015084818582084030414040780e64803a88200c03080c020100038030900080403841400d010108180e010f44011074104035040340c82000c1e81e5511001702186143ca0b0040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 788915170 1250 788913920 788913943
    0x4170304151e0e040b0d03030e01051311210601030302030d0b0a1d040201090b13090b18040b07020703150b01030b04330e2a0a1704060e03130503 64
    0x20b00d4180c003681e0061480081c0010b1406210f86190601c5440d03565801c45140760707030064411010903000b40740113405404034001c0e01259508150016449240d416041d2291540210458204103800014001c903400b40d2546900d00c480c6062210941e0f000410829000314401c2d4019a9a20074102d040c074111215110003910410100100300a07644071400d200c01c3c681801c500807100350312030f4401030710014495800705c036203c40003081c006c1700c0c8003040f41c020040b103400c110b00b03210700c0e4402c604200391040b0005102e640c01081d42c0200e0086030510114030b600c0305d11401105c4072035440361143c2d8000801c13000300710f100c2c5840e034001c40300c80e50b40341c010013126000548060125488144000210054400d10280d425804822800ea21409044901d00030301d06c500d00d071020f500300002e404c02d80308030003601e01c00356071030031860403051f00b52007001c60760440d0060340d0b012030303a84003c001c2188072100500140d80968685c000a01115130510041c0310000b5400c1c00111841d1906082c9400d0000c40900d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 788916420 1250 788915170 788915177
    0x60601080c0405040203191104051512130501090605040602030601170c0f0f04030f08030718050f040c02150f01061115070503090a1704090b030d020c0f04020417030415 74
    0x140000e0340d107810141c074191001200c0140e100d40e11480f09244003d0704004c201d40180c10642c3d40c0b44203818900007801510400c0d0f03800040c0c0562007204081c2803141001c01c40c1c400c0034200006020160303070500300303003100d124400101d80105c29464450513600252130a8404d40d50010920402d580c0004e05c000641002c444105268548503251106501544200e030322207400c0001c181c2140b0342c0b113400b00d40145921000000102a00c0c2c01d00c801c25400c21900540420000d950101c20f0100703000ca06011240010304140600d80e0000902c0b001d802d141400105622070b403010090001649890107100f45410307140fa005030b606d4500000c028111803030102c03a054100c0c25a045005611480351035200d07a0034101195a0313101e9126052034820701403070143c800600c204080c0c2d8061000c2d070041003103614840051000d8021581050744a072080300640b8090382c0000641c414905085032001c80e0614028001400c06039907000e0301c2d8043e4014040c8011503000024140141544210340c00303d07916003843c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788917670 1250 788916420 788916437
    0xe0319050d0624030b0f0a030c0f081c0e01051605060a05010b071505070903020904051011180d02040213090b0405090a0302070b0310090e0307030e01081302041503020a0b0c060601 79
    0x165100444083c0450a60400d0f40300d042c3e82020746c440d40c240c82d003008006016020f0341503881c100300400201d940500d0030700c05040080011a800002040044001356484003100e2001e421001e48547d0f91505a0078144a003c0c4180840710480c3d40c03048081d5801100a80018989007590744200c0314160005d1101c584180600030100d0880c059100d41e0004c000740024550f280c03103800b41d60705502c90340000d42c80144c08040000b0004003151204440449080a000711007010143c0d245900490b41d030003c61303624010254400d4038020010340d01c11070018000600c1c007900022802d403901d00f6508103505581d00e40840e00e846040ca0300c14030340d0101c1800003034055a481c2c4d60300291141040d200b280b40c14100030000c1104440301d00d10380d000804c603c94003001464070007000e0350f44903004103000b60046616496800c402d540101603580c442c9208a14004061030300b1f0f402c101c0240046600c0420710003c0410100068541c0c2e500e2078007420000301407685420300c05030300f00c3c03030114010310943c1040b0480 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 788918920 1250 788917670 788917709
    0x1090212030310090b030705041e0b03030703120513080d1e0e030301050603090f0d03060810050907090f06030b0411091305070b0315030703030504051002010e0d030e0319050d06 78
    0x2401c0f03c1540e44031000805c215001400181c03034016903812440c0d0061600103501d20600300507030601401e0301070300c5cad0a10000e0040c0302010b84a011300c88018001c1030041d01c01c40c10001850f8400c0f076200d02881c40031074106001c0d4688071403680040460110301caa03101004409900480140200514002000d02c066015012007079102e00040c800c09024003400310100d1751540c010b214070b81c61b950710b1800b224107000fa10f2200401502151240311000d001d850341c1c48450701c02c0b034007402d80726135865030003000068502008000200920003190301e007a40e86100c0440011164603900d400355009a900c5c44000800c88200300c51804050305204100000001e80d41c0099808074845013101d0030341181e03584999840c02001000600a0b10303050b0300d400f40000110406811001400c155207003503c03a444510115070080c4d01302c41029034000d40d81e501003404690b00c0c82c07281d003120700845c1c01b03803098a05000d0940c60f241d07081c0380ca030a03514010550102e26001c042083d440740100801e4130720a1614801e100c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 788920170 1250 788918920 788918941
    0xb0106020318031b10020a080d02090901091812050f030c091017190b03010e060a0522021c08041206140c16171b07060f120c030b040e010902120303 65
    0x401403103400f89444000c1c00c00018028031061f04455001b00706140d0302c40d02c00740640c0c000e6000c030005600c03880d000000801d04a072a44260074482d10340b04e00d5508503c0c460340341c403151064000840700800c603040002c01202c84d41400030714081c1c1d1040c1506da4464100204000000305203100480400800300309102d1803050414007190003c208021030b8111040c8010010054280380103426055820306140005024001a88501c44d40545000f0405070f00c8003000d03c0484000d80340b810095001000d480009454480311900c501e229501b0540301c0c0606e569601081030f001035104d2001c005408034104244103942c000d11070000e042071070881d070515100c0300710465801002083d4543c1307999034942c80104000705860a407610100381080f5102ca1080390042c02ca000528140701e601d0240143c0003d420340611404580c1613081d4030b0346862603403c180250000c104440d5030300105034542654100a455601c03618046540d290b001150b90f85a83c01030146004c0fa826648115500400400100f00704 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 788921420 1250 788920170 788920213
    0x1103011401260d0302180406080606040c08060a1802070f03090602070801050103030f0e01090b0c0a031b030905010f09030618030f080f2e0605070203071212030203060d0b010602031803 81
    0x1074100107031100365801034004088025070180b0b407c289014404120320200045c2c2e02c2c443e0b14201d03011f1203880c0300c200e8100c8000ca410b50f0306580007231340c99000388000c01400c100c2458500c4c41034001410402c003a1205940d40319400f109401254101c0011b02038541c0c10311980c005004084028411949503560052a41c0820211780e010400350042101040c0c1c45110550b00401c804075089403901c04241d8155140d502c107060450200e1000340030700240110070800f10705850740584998540741e103006c00640300b10100c00400350411201120210004086110311035040180c60080610821b05107005072200026030192410f2225240030811148c80030412079901c1201c0200035031001c08400c600b0a02201c0362a890030250762000004205a54441c010b03200c0c05000b1021550505e82d1034481c2c0440d04a0303032202528802024055240045c000e4005507003281001d05000c1035106144c130f90b0404c40300c00380c1001005070400207680c10840d0716151422002c4404034041c20746840c000170310904910 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 788922670 1250 788921420 788921443
    0x5060a050408070203070906050109081b21030307030603060b0f030c27090a02011710140d080a030c08010609120f080f07060f05010e040f060504110301140126 70
    0x35110300000d82000500015690140d5000d003ca40a25031034003169400b404040c0240b50006400080002d82e02e400001c050b841c40c0d501c00c48948000d42820103000141d0822244607445280800078004111010070045104020703590f030000d119400d41ca410015940402c4c240c0344142c1002c0c0310100c0941c0c000c60f00d40e00783c0b081260301e032000981065141c25024041d583c0b107001d110319101042031000010925a0070b0324800d03640c9035440d4901c200342c02c4a88a09842034112a01712110a001e1038070940c44480d13000c2c0c4000e003444400d880c1d9a441d031031158890952074001135240c1d400c0d4030905801071011400342415080001080741090303415007450000420151001482c10202001d00140004640a9012200306650f54031164109040038200000d01031a609103418000038100f04000140c0303001c1c3c0d074030551005a00040e612003c010340006030044c2c8425035203075034280155500b446420000d48459031103651039894801c415603904d6000010042d0141c0011001041220100710100c000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 788923920 1250 788922670 788922691
    0x20f010327030804020a17060f0403020307020915191a09040212010e1e0c040303050714010203011d0f0705091e030a062903031b01090b01030803040c080a0506 70
    0x5010701003105011000549400c00703040c038100303488410305a00c07070391080c810390003910000e0782c00395942d1000e64107100c000180c40c42c40d00b007000816441d0182145168010b40688102c83c20002d464002070302211007a1060011180c102c082e07c0380c2c07800c0c40c44541c080c41b4050042c038131480785080c4d60703c44030780c2c60265005120480010200841e40e42d41c0e05440d0164a9450740713007500c1da16080e40510a80d002d6454642050b42d03141104010103a07400d10034840c4440d109484d00b403d1560382c2c1074520340c0000004440e4010f402462802d480404d101540c020907100c4c0046160400e0f034210480c40c50b4019014062003085a402c122040e5041f1044910042003558080303034203803001100d42104401c403076040b907040c001d0407008024018943c00003540720b8691600c80c98003841c100c01d00d01c0c80c0c100072100582c06030018080038000b11485480c8000512041c400450607a0080c0d0325503019140c260030880f10b0000c00301c148407d2200800d4504003401c410b2000700315840640d16680e03a9a00e009203600b024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 788925170 1250 788923920 788923931
    0xf10050f1c090809031204080d050703211a0a050a06080903070507060302090f0d031715030f0a0b090a030813020a051c110303040b0403060f3213020f0103 68
    0x541004a000c40e21004030107003000803206902d001c1d0800c0d4415036140d8480d00c10396000305010f1b42280100c8080340c6400d0b0062024207518242684c0d5900001019800d01085290500c240003c050309064084008030001844840d035240c000c10300b042102a6030300424840750140190780301e03007011009403119400c0c00401a640d4211342c41c558401d0020040c4940188040082d50320b8140d00a00341032041240c04005070104041488032612103400040d001404a82d03038a031200d210003540e5034000c207500315221802d42100300032034035101418204501c540c2c40b072110f01d03042c032204c1d5103c650050b180e10042c06007000c2c55180102205009004e4030038511004c10440b04540d2090b500100624014001405210881101500090036402c06450b001c8c400c2c2c101028074135002c42100d0954104400060405083d502d84000034510812514502684c074610415907142101803400c0444016182028010410441100301100588003c80c000369000760000143d40d240c0101410000078a0000307034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 788926420 1250 788925170 788925187
    0x6021509010b030a0f0c15050d050601020f071202120705060304110a05040f140106020d0f0810050306130c0905100b090d06060821030709062304060e0f10050f 70
    0x10034819030b290b5414810b50b0000380030040055260f1884c24001d0f440e8400701507a4504043c038502c240240c402c00100c040141030340d23000803035002d540c00440602c1210304881d00c41c44010300c0c08816403c1002d442060426020452400c0c0400400400c0d162029200440c90a000300c0e03250302000e40001c01ca02c0308120000034540b111074290b001440300034000d01c0340c07002041d0104014a105000c081225865030f001054050001400350340d03601c620303a9005040046c1d01c40440762410040c00c0b141030710208c45c2c00041c043d03070100300030360080800102003000900303685010010608194072040c4c1c5c9504200c1040700300f1107172820b208101d80300d0b90744060b503455a080008188080e05100200060b02e0b1000c08034901000003800c07040d14444070906814a07030b641054180901045a03100e0026808a4050108612880c0550351403000610f40320044041d041003046280c101313400c1030740084c650740414021031500e6800401180c00665a542c165404908014481d100b581d00719031188900194540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 788927670 1250 788926420 788926423
    0xe07031502130e0702010f090b061201060b07060b0a08010903050403170c011a0406060e0a2606040b0f1503121b03070b07020111030c03040204051b131502030406021509 74
    0x340420b982000155105840d1661150340e007400362030041c010340c60b0030741d01103145c6503e1041c08425070300590703041d040d41d40c0c0310100250845000101c01b80c55403030f4400043c0800c1c41c03030302400c45288105000f00d000384c00103040c41992902c40c2d100101c540c1c10710300c1c00310120390490700312001c2da81c02074407006540282100f01c07020751240010040b40c540c41c014043d6407801c82e818550284440460f0700307001d070950340d1008598403008082c00c2588050358034010042e0044007003c6505400b03002d0f02020304c50340441411810b008003102d05844100b404410000301080788001d00d64400c012000c2005503100c1345002c25a544100301c07080300c45020000c0c400031001103204500745503443d40c504490b52500346140200c1294020b40d20f42c40550300300008a00343c0c0845d0410340748140c2c2102c460364115175554007044060100a40352003145105080b40b01d41c00c4050600404244511812400d1410314001101c590007210450010464000784030a00c01c19a01080c032003055001d04404003c0c60710b80d10b8000303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 788928920 1250 788927670 788927677
    0x1e07030b010c140606010201111e0726070b0106091212091a040e07020d2c04180b0903090d060e100603050d03180f020108040c170c090a0e07031502 65
    0x280034035000c440f20207060100000d4180c460304080e0b00074800403260029119a40c02200a0a5030b48aa115006440f00100402600410f8007800d000c9810404418000f00e80050b80d5884011480000601905011012850500408141c9804029907261980740495000f245800070700d4038800b00b65209031184070340f10340d070050314903141d000d59a13940c2d0b9020061254800e01c5154402000b03503000845441c00440d2a880f98052a1070304882c4158140300401c0d1840d82e903801c0085080e07207448030007a85c0c40d01c0c403036030810441e0320609510500e05400c00c840392020003044d40d07025030300c1005941242c0d00c40313240c6210116480303d800704101c03411140071070600d01a903912880d4545080310010600600284031055150300ba102040800e0000d02507800301c20311101d019040442030880000154403400410b50301501414402d0000d607122840098404c4c1c0c0c0c200712100c1540900003120561070f00c0f00c1f80d190040d00c0800104030b941020511640c4810051001414028a1510340c0c0e61001031074044 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 788930170 1250 788928920 788928923
    0x3130f031509060f020a11011802010801050603100b0f0c0c040623030c03030310030311070b0307050919180b1804020409051f09141f0f020409021602091e07030b010c 73
    0x42d9161459017038020a200c2e05110303500c00f41e40c00d001027503401c2c841c8949512a52501a91682c82c1030307082c403040c04140c0d440641316100c4041c98400005180c0d100c000036100e9030034064101b56407562400310251400002400c0c0d00c0c0b150f0718000c0104036005810b000c4402c80c000811000f441d906007040000e0604e00340300c0e203d40d0903020001c1003100140703075820340ca816139220341c5031140003800c11480c0316030325202400f601345400c070108085013855004801514a0800040c60064100700d980c011481c0c40200380e020300e200034003090703030125009128003603540b00400642d4000201201400c81c0c580340380c400340c0068040eaa6170454401844400d01a000c2a041c40b0b5001111140304944080000d03c54400306a94981d40000c510b050980d020400704140040140000e614540300b00c0741100030403c4880e108070955080100061810b06400503010300f82100340d402d04241d8490052240d000002000c03030180e00030000c030140c01c202c602c4a040da0025003c0ca400650034412100603112121841030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 788931420 1250 788930170 788930201
    0x3020a0905160e01212a1b0f02120f0c060a0e100302041e06080708160e0102030d1d0705010c0506011505040306090b1b0c0d05070609120203130f03150906 68
    0x11180f05c01c150340107400d0b4520b5106820940740c0248109801501d80122100005824170601c12400e1500e410f0242486003d00d22070030121595038002816840040001203442d048031f8820400010240b040945c20304040e1441d0b464000c411000a1402100c40304903072045410060042c9007900c00d5040c2c0b00a41074841c175101554003412f101005d0f000c800d01c99900024a00741c0000c980c944180c1c0c2e030710b00500c0c81003424002245c03200810f580700b03140c80d01e002d4110b1005100181d0b5001c0f50b40115082c075a6521003071446a00710340601410f080660304002c1c14011642d4010313002490000d10030781180c00c546601150503030148011206d41c451903001400550429030200280030305070036464081e00c40c150100114400c0c420b245401130280180503002504145140c03c10701c0c0c080c07001414050720507440060f40411700e82d10f5815482d4100d500c24010b0b4004291030300030040000884018001c11589c41c2d0906107141c0e06d6000f10800c10107032000351510741c1c0092080080a403c5441d00e10001d04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 788932670 1250 788931420 788931467
    0x9120409022a031e25020f0603070309020906060909040b0a09021f0807080408162f090903040339060201020d11090d0b090f011503020a0905160e01 65
    0x1d41680d80d4000050312484881c1c0407031407641019110044030000c144000c0500303c0340c005c1d101d40c0b00c41244805410303600000e8203650410203070b5901e002540300f07820a4400041c0c9009134010301c2a941002071005006080420540605a440d075504a40c410741c0108002141e950307965401000d0105140300a40120200c14200400c6008003041b071103900196803203005a6039191011a100340c001e07180902138a030204140d450380c66018001c03000003400b030010340c9560f410a07a640050800d8440000b1400401900348085516000481540002c2c2c01c600940c101401c40d255040034101400b90200c000303840d10b003d0030840380c1c0860b611224004030684866019504c0501901030f5119001600d4803a180100c0205501c00c05020345500c1c1c0e001404000100c00182e981d80345052020f400032001d841a6036211180709000d0144a014201070403444000d1440c1d481480114401c0b5080415030605100801c554040f07451326803861703461507145c0759404902c8040180c030036039040603c02c6107441c400d0303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 788933920 1250 788932670 788932747
    0xf0a080703061b0e0d290f0129040e100b1305030c0402070302030304060b062506050606090d17190c0c170712020312160b0912040902 59
    0x10f9000b64401c04484524482552100108a49400100d9800c0f43c0c4202203041d240085520035483d0880040d40c40b403800d2040700c0c1501e4036400751104881c1512070807115401882074089200e010100f0803009160f1001c0c0404400e405c4409000c1d9014200000702544002001408041c00070002405d65080c00c0750b0711082000d02b042c40d400c0d640a81ca010307102c0d030602d41c246414607100704e5140607016405582107850781c4d914800640990b1640703503400340052107828a00380d500c1c006a0204680c1d00440b0210359220324158050b1034008020030b224020622002d9950344942d5007003a04e0036440001d80f80d00a24641e1910610b00444c0c5150942038031084413100043e0700600804195402034864074480380d42e902c60b2540a01c01c00f404c80d2540d03000f8200030042c003001005402c000078802420340300d20b8186207180c1d4006800a26516181502d458484d00c14000200f80080d00850000051b0071008032401d11844980300e688562840c407540003840541019010441610011407802c042c8100c10a5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 788935170 1250 788933920 788933933
    0x50f070309030204092a30120908010506060313030e1315030c051e130e0607031a0415050d020d0b07020c090a020a210e0111030109060e01050904020f0a080703 70
    0x1070b148072401d5070006d0300a102c005e041c0050024211240f950030b034100c100801d1411401e280c04c50800c440030086e212250000100220010316120013a41d4401d49400d2034011454252200586100d01842d000c106006240f20f40303114110041d90503003030004445a00c00c000c101400c0042071080c100c1c034603008100b60002e1490394603404403400781480340c401513110f40400c6080300c1304804420b2a0074402842d5082d03070404480348071035248828000500c000ca45080310b0304010081312040000307a55251a2458a0190340007503020000640382080045483ca449815103192070241510456a80c1d84d8142190307510f486141c082030380285014418203200764081e41d105401580ba0f0f03c20b88510000039220102c501c2503810000e41c035518694030f113441184070078050f45e0f4840704154803610307014440601300d000d00a41d8145d600c65035259551b589800301250031900540c2250010001810041019564115109070081e40407106c0c0703141c000c1143c00184003542f10740d20202d0f580c01226400030070f1200303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 788936420 1250 788935170 788935193
    0x3020108151e010905030f0307031b050601090c08070201142a072108100635010f060306030515100509012409150c050102090607051b030102030403050f07030903020409 74
    0x2800c1e04c640410729254070816485074506401c103c00341d03101380400400b00c1d109036140c006505140c1040e07003099109480380385c1001402d800000401c0c1e154280050701c0d0340e00c01d03480d035800b50350b51000300302c9264101864500c0b14405820103042041620910221180c40c80599801020502810340c1c0c4058900c2d01c2e110503c48a444029030f50004400e0507030141c02008028820501c00107902da409041200a803010108102214800c15001c0307420806c000c018229903040e6400030749030850a43c5001e5201c07512a509400002c00c050410004200103032001525964072010708070900055aa40c02e0446d000704110351040e0390010384800002444145505148400c014040f4000d0003611101c43c1038421459500c00c1d228510303080c8050441003807146000d80090303480355001614240380d0500081c1c66030022141a103c076001240940e0024401c4944c40c030507075406400960035840d0945019091b8021100b80780340704980080d1810405128004000103554024401c20040003030341800e0b4100304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 788937670 1250 788936420 788936479
    0x106060e04051f0b1c0203070305040c0f0f180219080a061e06050a030b0306190e0705031f4d030604020d0608070605120c040501090302010815 63
    0x246064045074800c64003c0c28101e418003034041c030040c0030349826503010071580144000d1100a42040c01180b0300c00e02800154007030080c582c2c0105460516081400e0f05a015a0000c071100820034410002e149652034202c0496071103603910f0140c250501c07250000f070300c5104071078681d9074811a80d1910b034507000310b03030503028551040d01000800e80340c08455070842c100c10746050500b40762540800101d84a07100410700c4002d685000f064201426002c280b80a0381a0b4809070540701e06248945030003c0d03403103440680884100280551841c00000c03a484400c25007036240051201981104a0b0740c0b190009090485c000718a040a0201403095a03940c5d000c1d140600c0044070840c480b0f4118142e60316904020105281c92289161034000812000b54012200ea9103901d40315200010030b48418000900100502e444d1241d1350b880c1e0300b00801000900418852080d0781c180400c0c046664801c9190702600e0782820030000684900094034815000c42503500e07031025102c00c0c03290340503454034159581e08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 788938920 1250 788937670 788937679
    0x1e050702071a0405010e060901030209030141041403040312090611010b130b0301060302060d05100522020a110a051c090303080606070c080a08090a050604030b15040e0106060e 77
    0x80b640e05030351441c4514440c250004000080402d082c2c40d04100a040080341410014a0403c460700801d003501e40c00056203444405200b95005180c40141031441c4108013000c4c4140321603003c1e0714003120864041c10181c07500442d04c00840403100104122009550426104103013109050001044120603008a9000903003000c00c40300c1300c1c40140155041c1110003003030789040c8160715540c50010050345201d240c0c559250b15001000da01e4401c0103014011400901045074607044001c03501e60105640038901840300380e040c0707000c2041c10001101c1c55042d00f890250307480f80071190813500c1540284e03200c0418040c140028041000c0092141d895004400d01c54a0b07001c030404003520181c000b403202801150703403070000074070742d150001c003c0662510400000012507142c00c0114074045e4109000c40c0c20a00000e0300c010f01346170009615006080071194240780a05590345c4401d2030350090440b10b500c1c8420038001d0400d548a821602a10410030000c1140319a611802440070101000e0f15005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 788940170 1250 788938920 788938949
    0x807020604080a03020705090f060f1f02160b0c06040f0606030c15110303061c021503070c060501210602072a06080606040305120a021005040803010e070c05101e05070207 75
    0x59040c110008d81c0304641c030990816655480c4004d100c000c00900c009039600c03051802d00c0d05c514400902d6608201c502580c000c0040180548102c000e142c000c0d004a110208140070441c01f81100041c0503034010380c0030440e4500c02c5420300e0104060040394100070011048c10501117001002d0b458000010011a80c84541742c202c3c2c04011a200d20058807120b801181403032010041c0703a1850342d01c031a2144081c01c504d4039441200042ca10f503030070a4900300001100055120181700fa0b42c00744a02419680040da01001480e400c8440d401c0c02d203500050101d0f8011442d07000340503424480c00400825400c9600c840500035840b1140c400e214024800400c0c0340d0400b00d082414010141c4064942c80401000070b9401c2c047d80f81807239040710b10620118480c244041000034201c0c0a528099441214601e4495040c44410a11114014084020040a4840000400c0001400040c8181901d50014141009618a0440500c4203002a45c25400d110520140e1a40002c5060840b00030b142120078 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 788941420 1250 788940170 788940179
    0xf02030304090b1906082706070519020c030c010c020f0a0803090316211b03060b010e0420030702030d0509060402010207061b080a1101092022090807020604080a030207 74
    0x1a80e42c05c0c011071000461080c0000c01400c42e40300c405030407001071412042d54801c0e01d06101d141c800308480360f070000342c408203031485076500b10700004c08031240c140040c04400f012800840e94800445441604000034400c10806644403488103a01d0020007030802007211780c0701d54890340c2d42c1e800060024042d1141c0c030881a0b0040c003038402c5806460b0b0040e41c8049000310302d046050040d0944400380c0b09041d241c40081c0d42c0203104144100150320404010030000c00040024103d400310400450085043c0907031610700c4c00040901c1841d0052030b100258598413690000c920354007800010441a03860700b000d004d020540050311314410382c403d908541d40301c2e407504c90440c0c0c65904001c140701910101c181200c0054440390281c106002640b4003021002e8a0001c45404e5401d108025903030445584156980401240148107441c1d9090700c1b07c0c3e00121800040c1c03001c000f5000d500405044d0748280540c1040500401c0b80c0c55190010241030f290742d16104041e80740c506401d000c03000352080c03180020b03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 788942670 1250 788941420 788941459
    0x60d090f0308060d021e06120906060102071a03072307152a11190b07030b150909040c03080705071701180209060312030a0e16030b040f0f02030304090b 67
    0x1a03855805000d400c411182820300344444149498500d5107e001070101060354101c05000a1140a20314010501c50800742c001904100031504003849030a100c994007018240c1c50002c480d0400c10b035261034080c1070400e490191440094842280040b600010900d05202c1025aa00ed62052200303040200d10720380b210752100b01102c101e04400240781a00c01690b80b50055907444c05842010b016100d80080e031034804540c14840ba40d048078029044400d000b115545445a400e100c42c0907074283c0e0680401c000000820f0040c080c005102341c4c09603000404010b11596550000c6500c128000c0d21a2914940745440b80560300480b0380c45000322040d00d41c6078505014a040420f4404c05800510b04103409005030340e98020b10041d01803040d1640701070801c45007001180700d182812000917181d04400c002134100034003c40c0c140c800a10080c000c3c0081203454003500c0c0c02641c003952040804030945400180d01da89140080d40c1804040303800643e111540d0441210004104c0340321960100c82103607034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 788943920 1250 788942670 788942689
    0x10e0703140d0e01050d0605030706050c0f0703050309041505031006082107062a0324080607050309070f0801050a0506091311030325110d081206060d090f030806 71
    0x10000a11100c82290306075006900529194181b6400803c18980341c802082c5807800b03942c869000120005034800003c0c10601c05e0080b00710403440581051031444c0c03102507480c01030340f0310f41c0c0c800c82e911070003140c80008100c1c48d90020715002d0141c500000042030150010072882c4140c40e21405001120108400e14841d0f69110050301d4501509007200d549665000f0a20959400b0300400c4501002e0108048680d40d0904150f00340c0c0c4c041140b446601800f1112070419100b0007200d140104203106515011850b660f000b8000d20705140c8139038610b401c4510b01034003540807000c95094040c0114220006400c4948900c1030a0400c0c003203500c40005101025604456141c1032a042d068440000750b038914014450641c0101141c1c141583d00320360031481107082d204201364cc82c480700e020041004800c0a16440d40d011500041d02901c20740340d01d4890700c030301d611109032409035500003240b070f0383c0d4030302030310484980c29108100070201e43ca0104000c4171012829400304145000061051500c811403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 788945170 1250 788943920 788943943
    0xe040c090e010f360b0f04090b0a0c0c031202160212010c02061014010c151103090c010305060108040b0408070b010e090c0f0109050112020903010912142514010e070314 74
    0x40b24682001080240081028807907495021b4040c0030400815030782c038060504c40340d0148a82000d60300f41403841008440c01150124240310308600e031500420380000001c86228920000580d4680c40080140c02200c000030700254072080f1440b0042e441401544a00f42100080d000c950b20750b107a031030b0f40a0041c83e081c42004400d000030b0b0440360440d44198520041e041c8107410752400c2c8980b010302d00d02512580003009101301400b004000ca900c0702044466406002030800308400e0074450002461880c000304003500d03441c000c0c400f190030400414110f400036034000c0101300003561540c0340c2580c04c00050b20350001e184500c412a0b8000d1510b03142040407020140c50f08c0080714a441c006444102c1441c1c203040c2100c0d030034840154591400c3c0500548680300d558001e04000480c1c0d4068000030410043d005003110500c00f0300e003802ca19580443d00c1e0920407000d51503042c1c0307074901018124801d440c240165400c2c840602c40645000409805072071280c04001406c3c0c06034211036039108001b030312 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 788946420 1250 788945170 788945249
    0x30106120c0e06042303010c050c0106331112071b0522020705010f02091908070b0c0a060914100213270203072a030e040c090e010f 58
    0xc120003e9030701707901052084601c0904440e80c034880c0009085441104520002c9000013507203107846c6500b881a8400741404490040d10850300d40c40440b8039041a24800c00031000080100000500a11409064108650840b180200e54441c1c4a4141d0055a4202d801c0c008650001034190014036900c42506c0014141c01405920408007800322a1842c0c09100d40d241c0c01c100c943c2c0415002c0c003420411207503080001d80d0f00c0f41c2030814420746003000308c01e04400c3c41110006004010021401d5012618040b41c596141c0e07000f0801d96081054103000100395030f14043c81a002c10252490900c6070b00020429a206068451700c000103920414803240b190050f4401d041c0007011501d411406e508642201d100b0201c1c070b402900104903071040c1c0b9a2008038248170030a0094001421300302e8040c6082c01d4251030b1080143d070700940407103841c00c1e01510031600c074a51b4020310341c0b19007000002420169054400c55130340382440311500009020340d0700c9014a03400c0b2404503d9007444007001c114110035 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 788947670 1250 788946420 788946427
    0x303130605070e030303010915080a12050904060902210105010c030c0b040507030b040303060f0f03051005330f0f0a120305040f06080717152103030106120c0e06 71
    0xa60340401804020140028015544030184081c2c40c100003841c0070b0603c0c408001020000e0105d8500f680a1b140d224041581c00800b03802c0000e900a192203074400d805082003600c0b043e02c40c00003006840c0c01e4000c500c4003440440c51503408c8000c0100c1e680b005004501058582e620b6400450b404c200900000c1d003c100d0101e0448005068640101e0b03015002c4c5041d0f481302a12580e0340030404500790b0707043e4006610707890705014058a01ca581c4008124000001d407031149959203071a140c0d036050203110451a0b44030b000404c0100c0c1501d0243e102c241840340244503e00c01c0880400d00500b0900080c00f82070061075081090604620529101c03500811200d2130070710f00000e8201c0b441a28204904000041c80002009030000400e10083c080303507110344e446841d000c1002003203103c0f10112446040c0701c1c5401c1c02810b800750002c00072004802d940281d860038240c01004c1101e403980c00703106514407002000043c40c5601c07070b02c280d01000c941d140c00c0c0144032180d28106c500301104a22564041d1040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 788948920 1250 788947670 788947673
    0x809160b0c0f0111180d1227091e05011d040f0804030b06091605030106111c020a020a08030702090a0507030e0f1e030c07120812190e030313 62
    0x94041c00d04541d01c40c04480619825540107401d5074402084038403940d50205103000e5041c64060034400185054581c21841e180c0c68a0740400c4141d20303600203050120381100700341031040c1d0f5501c0741144012036075a41c0d0501d0380c03183c411004151a2441ca046203841c10000e06d074550041c060107049404600381c10007940c008007928020070f070001d04212040c225070311003400007400740c401801c0154016800c070101468890180484818018071200301c10b074603402d4540301c150304401541e040d01c07d0752800255000300e00c40f1844c503060360b10145000464001c08242d014036800a81e04c1c0120740300b552881c802ca40d031900f1944d6240254200294031034268000a500032159601c81540140b82e440d011440c0800450100d0030b29554031440203d1360000a160032816801944201340d54024400031454100f8200030591205068000c2140b144050364940062141250a580808441d00e50507003d83c2030020a0646600d00e0921081a0908003c00744001c440b01006480c4204044680a5001c5005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 788950170 1250 788948920 788948939
    0xa050603060102032104061a2d03070b0424020a02090a1b03090302010b0321300103050114040816080409061202090906370c030903080916 61
    0x303203114110704c01840010040c10b009043d030000f50804a000c00f01e42e060604000090f5040051940c00c8216003175003d600c60b840700309034481c01c0c000d03162024800c08020201002c1000c0c2c0800341c40d038103205804000c01e84400c07441c01441100ca040c10792007055003040c80d1801d01080742d000d8070405604500108009414601d4aa80d4400f0342054002440e101d54041d0924001c00d1040c00c3d00029607072010801010340922421100301403c45c01001c0b424038850b8514880c039a92450a642010003049415070b94540c1001d0400101c41280070003600ea0806208a05c2c0000c2444196074a60800549a040b0b010341400f00b030140fa080001c0c1891310102c40c411210400d442c940c1122001e00801c800951101c440c418503000d0080e030018004110100e004000d203400c00900005460b030444000d09c00b098071503c0444008105000840c1a4506d4911008507500d2103090200e46140c1050702c000701c21036265008410be248079440d206034980360054010394405051812841d04441c0d5070f000e0060110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 788951420 1250 788950170 788950177
    0x4062c03041e0806160909020a17010b0415110c0303030f0f06041517070b0a1d0402030106021f020705120714070f1e120c0512010b01051c091421090a0506 68
    0x1158141106d100da540e0031884120b0b4004141440001d48500d180b20042c0000707068140140321030703154242442d0801c2c8034a51031500c0c5480500600c02e204142c1d124982040c03002000d4545d00900f901d44078980818240ba54080460305da8440c514180000307052441d00388941c0039105800d6100c00601800c2000d24038000c96800e110304001d02c9043d60001e20000b552000b0a41c110707880e9545525404250704004501398844080c40c460360041c0018401180d0000c0d10000068059503c5030f01d1035007491840c0c1c000d11a100e800342140c000d00003aa09030864000091400b14450a03800c20380b400212800381d12003203d4040c1c14400490b50308200040801d2584010440b00d09001030400d031a95446a40d00b0103900301c0049810018800040140f031400400d01c01c0d06014810003070210501a50000300248030710b10382c201601d1685101c0f413090321200e52010011660000003442d007011030b941d2582d41c44045d49440e41c102d06185c0350407100754210740d06503040c1000c0509034050540c1800c082080c142c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 788952670 1250 788951420 788951461
    0x10b1914030714070c081b01210b060f0a0903030e0306070e010503091e012003040503030f0c07020d150501060903021f020c06030103061a0f0904062c03041e0806 71
    0x40500404c0c0c046440100c12000a05e602c6004001c05809801500190361004a5142c18400a40c003120b21454460440c004010890100090f4241c0d81c10009a002d01440070b02e4452294042400f00d04507400044d80300c10ba9009848040c0c8590501003090360b03e2104a079200c00160102150049650190010710317000581401500e41d03c0001080b808004003143d01c2c594000da44030a540e44010030780c00d4802d0503020300000100c3c079501d0161546903881c400900030100f031720380b1540003e142c1d9070b81c00140d6581d1175000341038041d2100c0500740590520400700080f00d54501d00000040d1031802602c201007201d03800b42a241104400e40e8843c515080c07a018088250b00842c0148911031b500c060056010390711540380014448000300c220008000f0a800660003048151502a1660788605440361700c903600440c08508020038803091030b540c500015200300141600000c49041080c080080d106a5a031003450040c1c5401400c85600154618802c414054208401080e01c841131419000300c1d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 788953920 1250 788952670 788952707
    0x10f120b0405250e010e090d140d14040b01080715050304020a080106080f06010803282a021c03080708100b0d020309060709060e06071a010b19140307 66
    0x24003030103804000f020100700c50320301512040d0b039040c0101180402c40e680035028a1a922426140401810b03990382401c00780302c07090028219403904200c5210b0200c9481c003e0150090000624041c40341460401c01c3c0d90880300b880721080089450070b00010740d60100c50460301501820402d0400a8800e5807020b001070344c22010ba0000480e0741030007401460000d241d544000e040e00b41401d00010304003141030300f0458080d0810040030003100180c0c8195441e116054031406100194104240c4000c2403a5100701450211440c21003050034110500c0a1881d0003694204c40e030554141c020703200000800c03001008145814042041e06206004da90f40c00640c821780004110345401401410750803604407280d000d078000080043c90b01c4140680d642050b95800c00306440c0741416400b400c00c40034a000d150140b2000b14a40007400540b6844600507180000b95000550b100c00060015902526003080800c03008040c607040b1620840d0300c03002c410b0808481c54250f8450810803158842d0080001c54917 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 788955170 1250 788953920 788953933
    0x6080601123c0207050304081501153b031603050607050919080303181501060f17090d090b1c0c03140a09020301061e09021308030c070e010f120b0405 66
    0x380b03284010256503005200441c0c0b1a890041c9151030000410b02400c4041c0035200100034000ca559030710354070455182040700660fa4030541440803007400b0710035280e03524660585401d0310240c1000750706c0c0c14081542920802440008444602d502d10303c00103005a000d00d001800451060014104858006040b0310310300e03003010300e0380581282c1d036007004400d40c10010030b12504d00340801c001003c802403040030385050701240d00460024041441030b401400f19038814480d909114401900c0c61030100080350701f05050a41d101076954011315003080c04154000d0022070404000000e94030700b00c0603803030310b001c14425059011020b04184150003080c50b80796404080e220808681e001d1140d051880002100012401014203462031540941d12190102988a0b4034456603d6003000f40d80c520322000d65038400d100c100c0e4008180e60360005500b404003040d60700100c031006c51844111840e11030541d089903222050445020928820f0607007000d02140d10a0000c1d001d4400780e54400e0090059410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 788956420 1250 788955170 788955281
    0x90b0f090102160801060e1b1e04090608030714010b0603041421031609050d06051008060106110114060a03060e0a0b010f08060f070e190b040608060112 67
    0x42141a0803486140c6d440745803c1c00003805605030950b100041951560403544030312405090783c800d84d24107c440700180601120706036612411100242041102040314076500c010355600c03500b0041c0c0480e11046030300740e80901000140115554440000d11181c07a603141c9544042c0143c0419440c0c10050048011040c9042450442e202001503401110350392480c0c0612808111002094010280283c1e84002d008a45800342901c65450340720034001101c0d1100c0e2600050b0007240c2d070041c1c915114020022600e16071000d55001c501090b00001c0c4203032030003528181d03610782e42110000c0d04141c20b40c03030170000709825070000942c8c082c01c1019a000d004440e11403501e003540c2604814038100820501700603880c0204401303980202c080905802034205054014203c0080c4503255100b0160200c15040310010400028020202e0814443c1d44a50b60b20010f880342b402110054049081844400009425030003401c3c00380c40000b00d24809031f80d9002c0c030303a801054801c8590303180c86800c10280341d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 788957670 1250 788956420 788956453
    0xf090801060f06030c0807021207020a050a0303180e09191e061e090c03020910080102070b0403090e0402100318061104141f0e01120f0516090b0f090102 67
    0xd000c000d6011050030742000d41c050181c40c25116100304100fa42d004021f802640402c40356035004c02050810f40e100c103d40001218450349821540d8041c04510340003040541100394840d1240c82216170a42c055620210388075075800031592140f507900801c0c3d00741c00d42001c49101c552054410706000e140c00880c41001040c41d40c00c002e0450301c182d84d54101301c184007210300181d017502101d84402d200c540401c0da2425025955071100038000c00e101000314041c2c0149020440140c42440002c41d03c1e8011802c0501e041001034a0a4010801403100443c034405142c1400d0f2146401605e40d002c020038264045000b011900340d100040821100c036040001c0f01806055250700c503140303503c2d4885003006000018950760500d414820032814030b23000400c560301405050044041e05280c05203040d01070060381c5104919010300e90300f51900d002c8202c15829907124900503c1e0f140800e0b80307082e1a8060690342c19546006580d00ca0b18180900045604450020404444113205075102c03c2400307440075 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 788958920 1250 788957670 788957681
    0xc031b2a0c090901060b0d0f0209090705190c0206090d03030b0a030503041e060c0f0302011107050a1709010207120c03061b020f0c0f0405070c140d0e0303190f090801 73
    0x400d203907041003410a40c58907103514002c2d0401d01c150000c002080c0340c0110101c051080401402d41c07a501c4815442e21511143d045d80c2c1e1127034000e04881940d01e07007500000c0c0503a10040202c407140220f00c2585040900c50064402520345c0039041c41d14088600c03040040720031480c1e90840406072a480d032181c840d29030584240046101d50021078503a800c0840406d400107006c500841c4564425508200741030f80030300204c00040d00900d0000302080c050030120b000d880e0805921120b0300d000620202009000550410035500400045a071408140c290040510900e080140141d2042409100825181980d0a20148a11502d4406603566950141543c0084590514401583c00101b984a4042c88001d80d0500c608000d0544214070320006010741c1c46400c2450300a80d980c500050a0a0081c150034200070780210500c0710b032039100200160f840141e141242c0c009141501d0b00341683c240041a00e201c1900001d00d148444000e45c41221b15003a480500c80400001c07140005a0440038402c8 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 788960170 1250 788958920 788958997
    0xb04020a0e0103200702010c1b030812132f09160809150a0f091515090b090f040318140a06080702060106080612070902120c031b 57
    0xc04100c0307200d9a00150072a901d104071003000c200340c2200402d40c40c1044e13003207501081d824240039005920034203104030301c19980800d8014440c1d1009010043c01114406031480b42071884100d13130641d880c00898203024017455801402d0b00b20380782c00264a6040f820b82d10303d0004901240c3d890540c030510000c0d4001d8000c0d6820900c18004107454004141d01244070713a4803000b030400400c404451030340c505a04500c01081091842d030340d40000ba010b0078181d0448a030464010700b20510b10000d5880302c200512032004c0040d251301e600d100006102d4514050000d40c0000105a001156290101c03400050b000a00440401440100c2034504d00c02e03500341e60000d01245c0b211146c4010307461083c40003440080d00407100303008040041040d05940060f0046c1540e00314078000320f0303545568002c80c1c500e10784020682040d004900b4040b800103480c1d80607080d1001401d4002d2070b030740c44000d030814452206481c0030701800118907410303014200c80300c0203040030019140b040594070310807010254092511441c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 788961420 1250 788960170 788960177
    0x31002160b0f0405033a0e0601092003060d0b0103050708100b130b0f130f05010b0a050d05150405090f010506010f09031707120207031e0f020f040b04020a 68
    0x190603051242403024140c0c805a50000c41d801400c1c070740c03181c03a568000c1d01d070100340011482444404490710f0090941722403080c402d440710580082103401c4040d00f013044000e600361040000001d10203c0d0b9000b039445a00c000c061382003c400054001d1100703039000820a503004003010360800c000410780b62485000f14060006040c4890915498505045000317541c9241daa091a0128110f969150001d10016244403000a4400e50900c0803075144520074030155848980c8540d00a10703c0c0b02c43e005242c80240110f41004661b8a42d00191080d024083c0d0050018409005400c5006142e0388030300d4100001d0318008400302000e0700042d003a01c0044858001c5900000d005c40c004007000d00038181c01a4003428006040d01905400410300200e61101030040840c0960709151004802d003140c00c80394012100300310b90381d840c0c5800b80da5440310380300840d00040c1c00d00c9603504000e05440c0c400b009580c002481700d0390260540800036030340c91151407158455510440c0c00d00e03c0c0d0303e5200401e501081500c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 788962670 1250 788961420 788961457
    0xc03081e01030503190906140304060b150703141e0d110a05090301140f340f021c080c030406240609080613031b0b01241814031002 58
    0xd40004171034040401c080038072150200601105420018110740030480101c0c0584903915401d002c4040c000c2c01e41010740014003206080303c440051401000031502a0301c8080d40030032551a4a005407066a0304001b144003c100000c050144100040259180c907000104142d103041c0f181c04400d0b40201c80400215000040c80c2a03d41420b00030f180c4182c0d450903442805281c080300e102c0002d40001d00c90010b41e031050505440384a290301d4401d202820199200503054a52100640300000750030b441e02c0544103a11071080e1081341071150031400201d03540c448840d5115003208943d0b54002901c201ca5140d1903030784a0300142c041039003682080101104030a9480e1410303038081c00c1c2070869008019180c005004000c03d8140d240801c5a42d554586402c10b06000c00c0112941880240440207000803038880c000140c091321b16003444611001240c01003459420010180c801d2014a0b02001840360107400811540020444e000031580014055810380001d0884040482c3d011032011442d000004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 788963920 1250 788962670 788962687
    0xc0301030b06030d12020f071a060f061312030504091e0515061c0209060f07050d0908060f0c04150503040c080703050a060f021306030e0c0108070c03081e01030503 72
    0xd001d016007000050700500341000b03041400401110000d2035003007925400044140358008000c04071400341e50440420a4038002d0744220030000c1c0d0041c3d455503c595058803400660b450301408580e03148400a45282c4c42514041318034845010881e41902070240c10700c800110741c1868055104813124110f00c0070503c1825101ea40c00322003015002e482d0b50510760010042c180c9600701154507031840142c9509200c010b0800160182c824542695003103000441c4054405100c40c020f80740c05c3d88958152141006080f03001c9034103010510411035945d11281c0406c94800246070034540110f0165006890241c8503080c80b04001103015240000803400410441880700312100c0102410b0341001420300d6074610b490b6030382c1c3e07002d4031003020748030540e14100341280d07090a40c11141160b0a080c082c00300141d8a8034060001c019030b008802c1d07507000f40d4480030744962094500c181700e0522a1181c4090441a84084440c1d14005001900904407031309041107104851520500852003080103551b03034810f2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 788965170 1250 788963920 788963933
    0xf0403020d0509031b0d0f0305030f0a0b1522260f1f0204030f03170a050708010b0c030c1605100e0a12060b040f0e0106080604110108040201020a05060c030103 70
    0x6201c081040402e001d19159550003003840145007080034501509180d1020002d80c42090800000304071841c0f8203403031410107030800060b42c441d10481c11402c40130341e101c0e15480c00ba61000c221050b848030350700307000c0c0c644184400042d01e03a0351052000c45200c0c6c006800b89507018036581e0000300c9110008600e03221000707010341c15a50600015000703050912013001030030390f45901402c02c02c900711403406404181340e0b01a03030646000755000402c46c5030b444050f0602a081e4012101e070304080505804c001042d0040a006540c010402c0380c0c1c41c20f01c10380c038203003055860341c020b90352005943c001004203908083c402c010412180f420a41d40c1c0000380c0c6071008012095401000c0ea0061010765007070740c0e19681c1c0b0180450201c54a010003c0c2d0a40114900306d4000d02c0b1018440340d00c1484e0591a481c5d11500e507110b040c4c40c010301d01c020418113864014041d030741c1c3d0f4216070003420314003410403c850651050601680107841801111005141c82e501c040c1030000468694000010120040060141 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 788966420 1250 788965170 788965183
    0x2070b04150f0b0a05010309050a08070b01060909020a0c03270803180a0812070311032b02040f0504180b0f04020a06030603081611040e010f06050301020306130e0709050f040302 78
    0xb09114200403070341e01d090118090705900e10866041c559250250300501200f40b24407050f01b94896240c0b40c4c1e40c85185400140f5100a0060800140c002c0342c001c90000d10910031900140402c0c1c80e11803c4021641e000c582c201440e12010030010308900c10b440842e04100705800240200070702840d00c443e8440e00001e901401060158860004107104204a00010600505098807120126540d14407070505031840540403100c0c1520b0702c0005030a00b80041e410444050310f44415001091484040a0807401c0e030165005990444079201c0f402c100d1494564000a03a142e41c1440d10803080394a919407200086044039902c41c202012810401180781682c00d00000d48030904040000c41e0554403203030749030b0080002c000b0320035405003051001d01c02e18900c1114014030040080c00f41400c2100c47d06d02a00c100140c042d4038030300341080800d0528040c006d403403013503402810190044d4000001075000c0c1c100d40c540f4800d5400340701004a450f2610340981c40c800c0311042c000d40c10600782440d001b861b051 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 788967670 1250 788966420 788966441
    0x20715090e0103080d0b0907020d1e0e0d02040b0402071208010e0705030c13080105010807030b0f01080a031d0a0303031e0606020d180b0712020d080408040e0a02070b0415 75
    0x14000d442400300007205a1081d0640703400c11861505d401e5680d66540c000d000580300c1d954032071446c1c000c0080c001c0d800a03007810282d02e10b0b0740766078002c6038800c9440400007030310a850b8086a144141c80c00f45050140b035000c8017a00090021440691180c00701d0b08a0b4014001070700c1c003000c019804103019411040550040161080402003860101001030107404003038005a00c074a0000b0b800d81701291400a82c00140c06075000070021542c2d560b151f42d6803080c581c0700c00c49030405004006108085d4240c0520b0490303a60801902500e070950741c00300e84404413515032075132510051281c0041c42d02e4400d191070241d4440c0c1c800103047c0740d816614100c180f288800c3c01c455581055001e01484d035010032004003001c001c0c1080308a5101d040622021101680c10071402c0030004644a0140000c0c60280e5000392030311b03001d607100b42a440c0001c0fa00120102c9014015800c204020480340e0724980380e40b80d110248000040c189a407540c1d4408018000f6030b4113072555000e072503444840060604c107211008 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 788968920 1250 788967670 788967677
    0x8030a110708030a0e040906052404272d021201181401062417071b0606080a030e04050105040218101116140a0602150a0615020715 58
    0x4a15210042e07559114215450040001090b640300c81d589a40c0c03c101041580400305020525001c0554800006c8000ca2181d4008585c2d0b000003031401c10f841100f10900d1100a5400d041440031003110b5200124030045802004080443d603100760001150002d507103040120b540c04d01d080d0300402102401400140145034900780405902c0312480605c074980d0303640301e04902c1b420b0802e80f580c6801400c2641c070010a16008030100100000018150300d00f800c1a41c49101c0414044a154421100c1c02c480d585d0214401d9150124081c080c5510128070701e1007406c3c00301d00c09480d103a4a90800101040c01c40c0498045103828869242501942c1e01501050710218140814265203441e034400f10b0b40118040d007000c111120078188114010f881411003c41241c041d51442d010400102040b8070400d101c0d4000340342200c04c2c0c0e01d82070517940d00302d9000713500400310103190300703980e100000d800ba000321180703a9501000200c407a441211110340705420380107005c2136482c1419450301d20f1407008440042 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 788970170 1250 788968920 788968933
    0x501020d0314060d02010908010c0203090a0e10120507050a061206240c0f062307090e241c05010f0b030d11030423100c05030a0f050d0608030a11 64
    0x1058814a10550141d000c0340c060380350413090700042e9900c81c181e4105259a508100c00e008500307800100500d0002019611300380b81942d12141442c640c5016200e14080c060115020000c8040440c1d014a200d07004d0340c156108266940d00180280310a40e00c0700e400b207001c18020320310400c501d104003401014184a02140e090304449401010100d0315600c2c2d0901200305000c1090088410b443c605996000b9400c000c24451011100302e1850426440c0301200d80b868005a14944250064170855418102d2101e95481d2013000e1122500034514a4500341084110511984d8401d51071200d484501d41c010203a040c054108107003034500300310a02d1060340c1058403100107138400080480340b1610f540307001a102aa14269a07046200707503400002030070703000010346d00984400d1503a0101e0540c1224801c61000091905442d000341040700034045402c140001c644040c094214162110080d01e0f242c1d16000b4885141421107180360411011680042245800560000c05801094500c40b004011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 788971420 1250 788970170 788970191
    0xd0b1e100c02010f1110020a030504020a0f1412010e0d110f011b0f12230703090323071a09150f0106050f040b07030206040201031a0d080318060406060501020d03 71
    0x301c1300114204008218a080e005500c41c28140200302110360f18003010340d61008040e01c0103020780001da03800c1c0e102d211a01070000744e2221841c450b404860b071000c0c40080540d0400c04019280d142021110303495503d81c00038401e402024441a240815941c0f1501006880040d0203440e11342848040c811507803414410398880c05000c444000c5810a9140241ca0500b0100c2e045990240c0314a00e80e003010f041c000c0a602882840d10b0303003103901502a420f40d1a513540d01d01c0032016520b40420180103d44245049403d00740f10b41c91042c03c032080058000c0c60441d05540c1c81355850425a540112032444d0403d00c42c0d01c0905004040e0810b0b43c90075a080d00e81402e00e500c0074841e006106102c2031140c00a0503011040c00c02007aa00107140480e01e0355242c55003801e02030345860003250201d001a1410b4600507035040740301c2100d21800f0002c2c22a01315a03100760b45038401c80d0b00c0a80100d554551040540e41c5101080144500c0380d446101c0c040740240c600000a4901070344041c50700e05150a0113012074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 788972670 1250 788971420 788971427
    0x210702090606070302012d0c08070c0236040c09050105031e0a021003020c010b01021204050d061d03120a0203070c0318050603090f06130c0b0d0b1e100c0201 69
    0x30340107107044900c6562071045280c1a401885120080c041541540041c152000800c840c28007150352015014402400c00c100100ca160404858010105400140400142c100312411820784000e9451044060510303d5004840c0d814405030800268011350401041240340540078001f0126983e00348999410400081d4450300f05028445440004000e50042020204120686243c010f400341224a0a421000b0083c5d4805c103544240c031360071701c0e5540b42d05500c005450943c05100c1c138000c50900e030412040000300800c81c501990520749895101152001c40c0c2c0c044500980304d20015944c4140048800001020080807020700d5413051003000142500030f09120512036140ca0904005c1c040f000c41d601001d101131300410340007040032080103003010002030080c905030030640840e4003d03660044030418051107984e00074028603e00c2020004041804094540725010703140100f0400c0e901400f04603ca81d50000310402104030b0800405641414040032030110364502c0d0118100d105030300080d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 788973920 1250 788972670 788972689
    0x81b0604141203070614090d020a051e0102040b04240305010b0d0b03030c25140a03030f09181a040e0a15090605041b080a03140a0909020309210702 65
    0x294024400c410000c107807590140f04441c0980e41c811800c0114411042d035100300102c080b1141c803014032502d541da4155a00004181e14034960210007020848100034084c90100c6e940c0b096910959024880407030005800b002500141c01c541201802d520304044040e40704000020b1000c041c546800018460204140100c076040031a15802050b0506448080b910714410781080c581036002d40c03500511203d1440c0002031140b0703208685440816201c0c3d240070100d24669038959880628142c081001a0040f03045111001d0305081070308010f075658200c2c045e40b010600107422541e03a181c0c2e148170800e01c102c054042020080d141003080280b071802041d0b0b00e10403481c015041c0e24942c45000e110410580250305c1c05230340b00c174041c0128241480e003100d4400442c02d8101d449102400b001c00c13421800035002c028943c041c1d03610007402c5000c510308241c41d4001d040c41c2c0c08200c07040e00c001c41d420500340015805480d08200030019104071141150000c02c02c1c04c500000d026080000902503602c65400307 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 788975170 1250 788973920 788973959
    0x320041127010908150402030705030d020a0b100803030405061b16030c060b040608010203100b0f070b0718410108061c05070806060108061522081b0604 67
    0x1000716150000c401030320390711031036400442213124040d00f0700c2010012603d901e02641c403c3d011200c01542710010162286404440b01340180d202c00c04509c041850000040c3d0000e480742c0301c0140313542c2c4403442c45003123038021281501d00d940724205100381d003080c3c218080d590711203d44a080c18441100c01d80c80e408a411000a420400f2800c1072401344151584014104d00e40200300300b104660b0f515031503001c2d4200710f520780c00401c41404005544c11003c001c66045c00d0341e910420f80340c00c403203075190000c0c0c0e54060410300c100b090319124000d041100c1c0c200c1001410301008405028a88040043d54540c5001d003d9000d007081038124241ca078101c881410160707002400d20a080e41d6544020440c0845000c414046518041131498140800466164203864003e820394605944840064800b14402d0311900d40025600400005040c411006418070ac4112211400519192100c48151840c06d03045060303c1e4000c0d1069120b1401c0456003405201c2003510554241b0389042c1c040602040c41400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 788976420 1250 788975170 788975227
    0x8070e040b06040905180f0a0b01090b1c0602070b151f0f0e06070501060b1306090f030215162004060b030601080402030f0304080304031505060904060e0703200411 72
    0x4600301d030400520080446e0b10020480d4021982110920b54503002c50009541d420002c500100344543c07180640200400f001e410440309140300c41e40300c40031031800d61050310215800c1c04103070002040d4640c1980150300c0d14841e0105606041c04010b050b207100091002e0b2110706848120803143c02c400485601001c90405003218112180801c400b4130500b10b000707086503e071400200f4407040010280c00c1c46850040e140030002d8891a05503010b035024011064854002c00d004c02c014a046402c0c5490100c90040b01c1c0d0411449032003551000305480c00803174178800c1004a400c1d0f0040801ca440c880b0301c80445051081c2c915000b4890f51912000d01903a04002c070030000201552410401c00540000103002c8030b903039555503401640c480c0c019010845001c05c64202c000d41440701c80c001c00f8040e10004010032555121561020000c1c05046084089030045020002c042034000103205400f9809084841e001e000080400c030445d080c9501d00303116403030705018540c0491804026003151000110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 788977670 1250 788976420 788976431
    0xb040b011110240b0d0b030d021507090e150102101404020d0302071701020408010c0e010206061318051c022109150c010b0109090b180a0b1008070e040b060409 70
    0x4807001c070701c0500520805400407030f441c8002070b07052015008080140d1002401c0281406040400d9160f0b4071132408640180d00c040e0000b0000054040d0245c3c2048041c101841056510445015400c1c0100d402d4011032090941c0d070280c0b9601808003030548801058104500a00803216000790702019002900541c017820380c810405000300040780c0a403001d03110511110fa0480c0c0707003501070351060040d100c6550074105030262640c0940107034061a2030580240010307540d00301c18004103400e101d2020007500d80741c54200c600c4c8004402e8245030240114040c003032411618400410040c401441002150320120401c0c0184649020030b1200e400d80196455803105c0c2c2500099808c110040480d141c5040060110f054500550010001078002c0c3c8800d5a01e560707a0344890100d6852450840c0c00036403000708144541007085080383d00486609001171070200000c04030340000d80f207044e02008a507030769051203105a000000610000c908031018010184c2c103401044032030060788180c004940d180c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 788978920 1250 788977670 788977691
    0x901060914150c07080d0e1e010c021c1109010803040e07050d021602030c090106020718090b0406060303141602040207050a0f0b06040f06081b01020a060c030b040b011110 75
    0x41c18518442c4210210480d11038a212000f15160ba2141c41440000d04c1411b5580070303c540182100311300890001c1002101c10400388008030050f011104450400070640001c000503691102224800c0d9132040060703080c626140b130a403000f2141814500e204a407968010030194030300200721000c4e14070880c40c0f64810784951005417218020000c5120340e890011821a442c110311400c0303c51001e0080342114003000c0f0343d5041c0190180203000d4031005801405080c0118120702c9005030301e4998000b00043ca9040b6511400800c081c01e68007251520703100d01e8104181913000c0c1e010801c40d88044095440d1800c46000c240c041c2c804460000e005a401003402c10078824180914400c10350080103d80081c2d48901c3d10847c5603004440040c4141c1c580440a100183c103440340009684d0b0800c0203180b003c2c00c0000c070b1300d407201d80c11400c90704601c41c2d030120300c0002d8840d0140d0300700b81445450224906140b001000203440700c0110003810000a11400001958002070307442150b0030f0346200146c071201e031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 788980170 1250 788978920 788978929
    0xf12112b060915050904050c040e12070503120c0f070f0305070510060e0a02070c030206070f0c06020d091502031209010f1e06051507030f03020d060b090a050901060914 74
    0x2658592103810786040e6000550406540200c0031041032012204038540e25481003040740f03501900c0c05000d0fa40030964100050400380d20810703004c0d09040403241080035041a40c400343d40300503003c90742c0d0b80020401e160001ea4810000e500020f108107041d040c1300204203241c0d814065110301601200307004244000b03041c0640200c84802d070704007042d244d245119164400150a40c0e1044140c2d010700d410004125170310303a2095400c0350754802403401d102c0d032454080001c83c0c0c0044005582d210282c4e104000041c05040c10304000700015000785c803041403606400f420180c4141e00c811428445145040445607010084034030001045a400c1ca4a460700350f20700f801040c80c403244100c0c40d132600150340c01040c4004814101503034050310900c411a251000d2001c01a00441d2810007284140150000a0300400e14100352409900c0c00600b070002000d0388074241c9000361b224070401080001e4201a40c103004694201800017518052402e501d040c0c0c0041c221b0109202c0d000c0400100303411001a980c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 788981420 1250 788980170 788980237
    0xf05090607020d12120501080c040b13022a01151503061503090c0801090305090d08070609080309100b011d01020f0105010303081012020904021c02100f1211 69
    0x1005400c5840c02c0d02d10f480e2502e10014644c9003070700440d68066120224071924090070341a501000c0182c04604c014a080c40044c00c6490003032a40050454900840385031248040c00d08030161701121421080340600050303468000b806500021f03410030840c081c280c1800c0b00c46e0011900d5142c403154070a030810804400a210782c1d0403040301c0c410000442c17041e20381c1c50340011031114080c4d0341880700c0c1c99540045031308a03152568000c0c04900240440041c2d4604008070f940c580b8003c1c0060351802070300f642c1d44400c480800c4170032295450b01005010801c841080030708400c1041102c20441442c181e800641081c0d4461080f500c0050050020b0703070107900c00c0c440d1408080b8084001e1202c1e5840786009400c00d00b00f11141480e9010088001848103015031009612135005005003031035448540901440665003041caa100c0c0c2441450440140c0b100111020020300d6a0b590040c40e1004590080c41d20f601182040030b4281003107041e01d02080800221034504866000b40ca120004030706042240740e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 788982670 1250 788981420 788981423
    0x31106010f1509181d060403081603020a08010e0603120f03070e060703050405010323090c0f12062703071103010f06180c0e030d090807060206070f05090607 69
    0x144000006141403580780c0ea034180c030110703040b00b0041086040304540c41c50440c802e1400420242c1200c40c0080e00d9170b0b0008003101910760a130188094220041441c0c0042602c0880c001521001000031200888400c1070300c514052074250306d01103018030000c260203010f004210740445400041a442c0d5820002c2c0c03804000c1c0e00c0c160310b449040b01075401c00c8030f82040780c030100400c4040601a0302031626000b255009545030b2900b070708141c108401100104074442e0404012071081d1208964000307100030140c414140031008000061101c0d0910040710203490256001e4181403d441006100c0424225808280700106484205940000e0f202c0901e0742d486a46a60000003415800d002c070660b807042001c1000d0303009000c0c2c603d40003202c0c0202c8031244a403421542c40254032024102803900000d0f00103101c1c0c90843e5149404c40006810300c0d1a2a4040d004500c841000300201c28060240300c0003841c690001d82104d03c0c20740405030200100d100c141d010001d00054030700c525030b01c080c01d072902503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 788983920 1250 788982670 788982673
    0xd050a020d0e101d030a2402040e010e0a0b060d0203060f0f030c12241602070e06040b010311030a020d05010b0415050a031b1d0a05030c010e0a180c110a020303160311 73
    0x1c0b4924104481410701c40705402400315002c81107001d00c1f002034000c030340c02c031640c0c042030203841c0c1e103003400c0d5404184014028481c42c60b11951441050743e40c802c060b10660300b0b2500010f0766418000f08001e80390454030380f028058035958a0400039660040340c52210b0003815103420380e82144803c801803c0c1070114640864860b81c503840e100c4c01c4400b01e1480c038401c1482c910320340100b01ca440400c0c0c0c0c0d07840f078511503003070324040d150300048540c105038015005401c010704020a00010245d5031542036001110400c00c00e030b0b804a544000d03d00301d0300800c0e0050940680d9545428144400b540c000c90080042c20300340721002134481c20040c031a0380130003002c507880c0414003002c200b0304000520f201a1042c2a901014a141512800b840c0540c003000455000900800361030300140010f6410328004000a03901c44084034000540200c100b00348080c0600c40080003a1002180c40003a000e81591015503d00f54081c8619000684001003294100c1030b14002c403244003600c0d0725046604142c4045c000490703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 788985170 1250 788983920 788983933
    0x1030c12020403030905030f061311060c0d031e05010503030403110a03080304060b010f210e010f050103210804080f0d1b0309050c01050906030a05090c030d050a020d0e101d03 77
    0x74590311036006410360f402202030701d008c0d0483c207540c1c41c1d4801041d02d45800b41d840780301d4641e002520100e40c0f5031012001402d0182092000200d15003000840c00310f07000403d4442c0c80030b0500300307a103600c4c2c000b040c3e101800400c060750416020980c0c1e80140d000090500d024017902c07030103070382d907d09101000f15400510159640b41c90700c1c102000e01500604940451070903501d600e000e501420104091401c01c0b5940c803c00142c0c2c0d1205c50140c1145540c41c0015540c83e03100e4034015440780a464041c6018034042c2510710840381035000b400307000030449010484444184000154803400f19151a041806141e1b2101c6160319228000c00044507030060400c0010a00c0100319010303008a400d0f14010700c00d48011301e1851005441a00c00c010007540d000408100040e00d8844c0c5c3c0c0d212035001002c04080340c15a10640010034601041c62900c1d2010441c041b036854005641008245080ca14510f000008451088042190482d03280c0351213083c0720800000d12011108003040d0400300200400b1541c8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 788986420 1250 788985170 788985173
    0x180602070e22110f040b060901120608010c0207240906050f160f0b180a0204090507050a06050309060a0207030f030203040213060b07060614010801030f0f02090103030806090603010b0f01030c12020403 88
    0x4900094075403050042e030410700b10741a130380303041e118801d6160f002821013071508030b03034500446800c4030740002504090354a40022070390039024421500350f00901d4008003115403c050110344603030305400c4012501c1c001184c420040d19403040c201011540c05041490310350044000d038240c41c0c0180301e900780d43c0d0b020310b0045006100030303c21102d04181c010b0805501603114081c0203000c2d282400c8016034658040c01c05c1d0001400e0030741c4031482203400b0314165403200f6255800a00c1c00e141c05e500c0900050300102c00d00510346021700200c2c5d00148081000c518124555074080c040c003003948808818194084001400e548034449642401200d807141046040d8407200f040c4080d4015010541d0400e14142c0d01003042885020b000b00d800304140c5466070301d40e19541e501102100700100031a800005451582c0060704c404080038080c6100c1d4450b1516460303c0300c2406208800109414400d80c10020900380070f80701e042101800311000c0c600407441021142c0180d521400c00c1103280c031402d100050010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 788987670 1250 788986420 788986433
    0xa030809070e0c0a1706100e040906060b030915010305100c03240f090212011e080a030c1208070c03140403080c07030b0c0301150309141903180602070e22 68
    0x131220025280c0601501c0388100001c14941d040319441e400c540c004c00c01e0741d101c81c0038005145090348014070101e549803c030765490060f10a142c2c450081c2240c00701c00e02c124503c061127071040000b01c0c40300366807066140d6100ca0740d86e910400408400d5554905010720010b11941007011448040103602d110107030103070281ca040400300c2c03050580c4801c0b00c40e4003103071000c880d000b2078016804c0f103c0301070201c3c0d0800d050b207050540301c0b51b805040701001e80300010b400c590500079122028001e441e4480060214240800010100022407080140141c10804850742080550058079010300e00031800c0007081000844074411a08050150403012681b152191400140341054a10440004100d07403a540287c11060000b80035030f0305640d400c0c1d20402c080500c00d86c00070702ca442c040c1c000c50b0300707243d40c00d90501e0400011481500007003048a410a0901d0341044941c424820010218079925240c5403000791a600317075001e088881e02810010070000c0800c07031005440390684041c1c160354005641f4242 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 788988920 1250 788987670 788987677
    0x15110f0712080c1c081006050415030603171306090612050622020c0c030a03050417010204090203010312091410032c0f07120201090501032003010621020304050a030809070e0c 77
    0x13070015401c43c0015050780b0030303800240d0840340242c031618140b5046c4000348411b46903c00803041016030754880000442d10780c4121020400c0e02d1000d06039030307100302e04401c1d080c10183d40001080c02603840e0b08000850340300e802600b4441a03000002070310b860301e8000844100700c0101410103e841c44520001a10540c1d004000c0f43c05500203e480c0b8600c55024541c1f186200c20300500450000c2c07004010510f0309111940c03003d0b5004000510b01601c4648400881c0c00c00c0c0c20640d5200e0701d01d680c03038401d01c0e0803000040281c5148000414051403e0001690403481102c8a03000c040d00c96404e01f403044540444544404905580a81c0010007401547c0c2e41d09504620301d40184215007001490144401800c0b40710341d010380d655918641441c5c019006810740010b4035440390007010f86161185070b090040c42c060403042d0b4822005800d504000300d03041160078080010b031441041480b0018000140c014503d80d49400c15001b180d89005409084c072602d64002041c0c54050000c1051084405008 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 788990170 1250 788988920 788988973
    0x50901061b06021b100507021509012903060603011415010e0d03030b0306100e0c0a0c0f11030705190e1e011d0108011a061c020415110f0712080c 64
    0x4542c0301c0b080f581e900009440090711113501513000004001e09226001c04440e902030107140003c103d00300420703041d510343c00390030300001d90014cc0c00350f410003180703004d006c1250000c1c0201e0003131054200c40840001c4403d07028010210032503211088004a034000d00c6840f2030404002c1c0f03140483c1c2c1c1c0900b4003401400c0b040081621901480f40043c5190000207154000e45035001007803201c07950b9641100c8107940c0200e81e450b090000e0200b040c0300150741c2d0030a040d19144039030043c2c14601072042c145842c104540d080395125104191400d42418032840c0300b1000c0700c2c1c80c145814116151020300f0b4128110428a611142a88d1400420200350b000c0c3c6420120303802240780c0c40701c0c1c0e0340d0f10809800c03074005802200f4444010079180c180f43c9468005054101000380c80c8a1100e900d02031580e040303074000c2d07004050049100d002c901c40142c000381071403c400c2120001d004218540070900352243c18502070040c00b400703410348410a10915000b60381480810b5022120440d08088443d00d07040024282e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 788991420 1250 788990170 788990173
    0x714030c03060c0301090b180402100306170f0609010623040b060301030803271b060913050a15030b0c13050607210f0c1410050c0a0315050901061b06021b 68
    0x641c6d190342860232a1403a203420004440c00c454899a007045140348068007200205600c5601c0400c900c4070302c0700c5000307504807100c0092072420111039a0f98281200200300c2c0c15180d00d03000c0c0c00c0020b0100310b0080020380050f64241c9400240300000640204620402c09800450110000c000c11602c540150302541e4038620442c200e00903000311484540c05003081161700d4010114941c01070207050602c050344100140b0302401c00600c01c002c01c02d11006440390400060b1a0b500317001c408030951140122100501920000366800d40d1580441d40201501c3c0001e0800f000510f0544040800d0381c02e0041d00700104407a690303245900348016008611402d040d2200e407907841e0f00d144103000302040c03011403125407550400304cc5152242c01980040e03c1c492440760060221341040041c140c454244918207840860f0348406040800800b256081210724002d0768908901780100e41d01c1030090b604441051600e4481903c004c1c4504041c4004c40e14001c24440c008030703096501a80d0043e080303200541800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 788992670 1250 788991420 788991431
    0x423030d060b0a120506030c1e040b0f0901150c0618300507050307050d02210307050301050d020607020406140f0a0f1a0c0a03210e0714030c03060c030109 68
    0x1c082d03035110f210341e6542c40d001c00c403161112000c080c2d01da080968040390080c01d88135040300c1c40b00491900a11400c040c0790141c549044a00d00d840c203413007005e54043e0152407481ca0414410013052104070180205841609205541010300e44180030240c4690342c00f0105108002c089003051f1f0790422548000c80358408540844806000011050300008002d0300b410500c202d03140101381d4540d07000c107100746d0305800104440350110300200007601c490300391355000b40b4140d81d4048103000440d24004803030348590303001c1040c09000e40d0702106581c15100103e801e0500c030096440003841c9841220740003900503041810004503903550811042c203000d0f080d560b49100c0344000c0e0402a130100756010f000b100b80700051040c0040400e20036000110586044060310341100f8241c003c1c5070144204044000800b11200075003031110300e0481c3c1d800008125402c1c4040c1c0700a546541d11054503015012040b43c500161002c5680c0412058084182c090280d41140c2042c800f4542654400d0040c015910f0504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 788993920 1250 788992670 788992679
    0xb010b07020a09020d02070c08061e04110f0d02030d0e010201050601030b0d1b05031e0115080a030c0203011104060801290307030b220c081b0702090423030d06 70
    0x110803034800d140e000341802141802d020480000750400c20707009254035400d001d10000512041c1d98900581160b50081140b86031134422851010581c14800181c04208001d00c40000c1d0701403040c48850000b224965004103003880401c0742d080d074520010b0341c9803141c100c1141406070003909411110b4800c0c0c1c000d20840d0f554000541c25030362a0341d0b50079044000c51b41080d0106100385200c0a09a03505507641041c0d0741c2d1040081e24140c0c0c225600c804288030f4080f03070400c0603400d204400c0d001c440003450b039a0310307403034054225218280000702600340207240a4503c00c5640a51004510039414030110740c443e40c0b101d40c001c2601909009224540f2402d0f000201c0101108a0307045210380262111890756036084021009042c0305c0b020640c000b500c000d0200d0081641940c02043d00600b801c001803007a01f1410010407140c1c010741200c0001a20b4001c1c00d039603904443c00c80d00e01d19015100c1c200e858885241481c204c9040600d180045d9a0032104594a203102000030041c0c10302e040d50904c4442e849 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 788995170 1250 788993920 788993939
    0x60903080906100e091608030414010c021815030d0201060617010311010c15050106050a030506181605041502030310061d01030c11150613050f0a0902030f07080a0b01 73
    0x42d03c408002070204001000848250704c20b8650005000c400c0d2000f503000c0c24001c48000742650000301d8990404a82032100c4003010503500c00c0d04000340307847c405080c09900070030303a0307084c68003c8038004211b110002111103680c1106136618200c080c04441800c040c1c3c0000a008240500a14000404210041d000d00c84111200e038182c030741062038480c82e410500f006481c08a401c0d14201c415940782084010148403510919008200c0d0342c071034956034090000e008040f43e50040072148a0b880006518143c83e1703d18905d00d0340000c00381d0448050b030850380c100351142e0003a83d10012030021021140c0a8141c4d0110117540642250050450444d8440c0c3d0280c3d54090030381c9002c1c0c60403024043c42038056101790460210351445003081c18a46000e00c98543c1000288041d600c9220460001c0c446542040c1c130402541c1d4049400030003450409846c004641000605141e110607114080e2a065560030711040c2e40c2192a40103e5021a80d50a00c203a141c8913010750582d803d03480000002010080f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 788996420 1250 788995170 788995183
    0x507030b04020921210928050f04020706090f0302240609040311010e010501170708120c0705030d03050609060a05030c2e030f0e0d140306060d090609030809 69
    0x300200326000659032241020720100d44c82d00c08a1180030f500f082010441154841400304006840b070740c544203882440400103081d42c0880e640c100321042c081d108009520f00c041922001c80b020200380c803504001074080d00402d2405845203207800041420002003100e8864924420703001d507801c0e4030310028840041248450505591801c0f940014110310744804101e500c24400d00382005540340e80b03510642100c0404c680302e42d20340e550710014090313283c4105103084480880c0c0b0003021400c0c180f42c0171a88600d914661002030f240046545002d018003441101d01828010342126040c9041003030050107084c09035207041c01a042d401c0881e9041c00e000310601b081e250081c0082c1090070a403030030b2000502d0140b580c48000078101c042c29950180459080300c400c022660b011030b140d00c42100302c40c103d030844040301d44158001e8000c0d6200c11380100200c0c92190900c20920340301d07510039001c1002440342d001c080c1e900c1864082c000081011550000b02c0481c041c0c0c1d00c0200580c0c85d01d421554a14 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 788997670 1250 788996420 788996437
    0x10e01060b0c070f18020304060906052a0408030406141908010906050306070c0f060e010c020c030f0c0306060d080702030d091701140c071b0f060206090307121b0f060507030b0402 79
    0x1c2c6018140705c446145c00864000d0b10820002840350003e46841c411100181c8565102500c02c48400007145100810364004681d0300e10319518040c5007035107181c0e4920403886480c003806040102c0e0f100c0202c4050a032040c0101e141c65100100d00c0c40c00005004034001d0140580706032070504e000ca0f0509000071090310442c42e035121001d03d0105038507800b00320261500102c411039103c54403256170442c21f010f58000d0401e103400030040418900109418206030340042c0e04154805c06020f481a41d0002e812078000c00203942d8481194024201010588075000c006034161141c040d10401455126090b4030480b060610b5190075491030706400c50130f907440f1a44883c20b00c800da50100e41c4901d0514000d0940d41d01c141d40e0400d24040009030f1031810303101540008044842400104035198060002c103a00008500c051482c000310b42e0f03550850411055101c4017041090f00c01c00d80e003600e600c200c0301e9003160072001d4000303210158507229015003400c441a00009042c840c00307260505242c0256450365 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 788998920 1250 788997670 788997689
    0x7080109021012020c100515040e0a0201050927011d0f040201050d09061e0c11030712210e164b060e0d0320010e01060b0c070f 56
    0x804800400b1510302011203c1880300540c200f149006444e010000e400c000750034842c020030540f4004031a10010345045c1c03003181c015402c081d241844a0760100b0030f80203a80c0d0900304140c85079038480208100144503009000818551240c980c840b410400b11181201c9401e5001000c4607007540b181140c0135000c0c1d64562170201c080011800541c00f42014000e1141060f000040003c059107811080c0c8812082d03c100d5041da0000700c01e070142444c09820030b014040c0c18a02d10003aa00c5446603942e00c1158406000001d00b0703440c403941548078443d440c4404d04642000e54100501101d100003c0008070340c4000e2500c1400b0341e5001d005400c128480441e0882d1201d90294500c420202030412465814000c441a50b85c507680c8030702d4102c1415042d07038142e40c13034852002801c0500c0901014001400140b02d81d1450f801c1c1c00009600c0600d80020309480e9051406940d20221030302e0150002100c1000c05e9424401e01080780c1c030307800000d840c4402d141011a010942c0e503031000e04421015001d0810030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 789000170 1250 788998920 788998939
    0xc01030c020d0309110301090c03021903050d1d1f080711070501030e152a041a0c0115121a0903190c0b0c03061305160e06040504050405030c0708010902 67
    0x2c0ca002c3e50100c51201e00a81e8000b6042c50858002800c580d1141400c6450350421704042c17017542807082000d445040c07010001c1c2c03211425511029569120081104200451000d41440b40c0d6540d007121040d080c00030b042e00c90643c07000c0090340c126001d0084801d001841c2c1c000020503c62180c4140350409034150081c00195007400c0046002d82002c01844c9200d00c00c1002c00e0b003c02c106a4005440703800756417580c04102c03e1581401000605802111010090a000500c0390b00d2441145c60b000a0404034610b507211800540c590140602420342a022485040300107032000d00c60440803c058825010311481002c480c00300c2c80100d1044d9040101503000f03001d21000105807003240400f6422504004443c41120b41c0c03418010300081b0b0340e00b410407001209205071400d101d800010b5254550340140305500e04610326042210403482407004100d8120b03001d8549859200c11200646000f40c4140403920701410f289560f60304c0612071060500c151000000d011506108154403140d009028046 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 789001420 1250 789000170 789000193
    0xc030e09010e070f02030c161e0510210603120f0c170a180f030c080c01170c0418060f0518010b390106090b0a03060905010b060c0c030c01030c02 64
    0x10341d401010104d40941c132080150302800802085182c0180c1041d400b50300782c0c0c07400d2074036100035012082044c0603038030000403013031101d83d03540040818003105070314200c1d90128040101341c14060812880d420118500f0314040240144190964640c55054a031030f0300515000350112142001840060480c0c000d1019039022800f1900082c81044041e10784002d07480b02e0380403160303031040302c96011510790088140304204000d10744100e40300400c0400041c1031117118070380003e00702c8032080900d0243c1d0306c1803100140d50354140070240d40c090400c40b00003800e1a04581104c0380100198010406140b1820200080070304c1c000001c01200d40c01c1c0c80d1001002e034603003540024a50000c014401d0f0001184040340183d10350074000c8030b944c02104292104c0c400031201300500316038880c2c0003c031460741042c40d110400d4943e1052a0100c2b0b51150001580725041d091450041803158081640300d01d0011350058400400651440c09080480030368007420040790064003119484511480035821a034030b040e1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 789002670 1250 789001420 789001427
    0x9060e0607031b020f09160311090f01030c03110f07051b030d050904090b130b010519030f0c030b010e0a05010602031201030f02030a06020d020c0c0406030308010b030712020301060c030e09010e07 86
    0x50500c1e2001c0c084142c5d03405c100c0005886071200311580a61840c0d40031a5158160345805503000707440000103a60324140d1b015010910510304044524103068450503500100c0c0d1083d4045001c1000c80307002d040e02d82a0300085080711b5440f070748064416114900c0000010810a100fa207555840203000308140c17014160107a44e2030f041240380d143e21694500d03c00c07000c100940c031104d2043c40b002d616410340aa03503142c84c410103101a04104e0040c00c00f1410b01031120390341101c031030070f8a40080500d50300203014540b421514840c0d8100500f0749420100025104c1c40010b820b500590f10f03a10306014580e2a0741049a07039000c1e450304c03020520100c2004101003a84104220016800076007551400c51050301c907802a41c2c454200d14400a0b40014043c100c800305000000005400321018864280b841d05d00520100c418001e86403107a200101103841c141c081d000c06d100d581030700032081d5125070355284041c1007180b4501c01900031a5840018484030314201c00040e0503680c00d0384600c0440d440d03216048 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 789003920 1250 789002670 789002717
    0xd03060f05030a0b041a010306090b0f10061119060e15060d060506210c011137140d0909091a0601140c0a1b0812030c04090c09060e060703 61
    0x20388419515041051b4058031401d2158080c41c0a01e00200b5200014034107011080001486004660000c0c01801180c3c0842c0103810111007480c542000e8503800c0521246c10010728aa48003e07540028059000300840da420020500b43c0c04c6c0107503544a0b020428640100c0000c48110b43e0042c0c17004550000604070743d20551304440b01074100c800000700500c2107443c1d00c011302c0840b4680e90040008881569000e8180c1c44056800d034003030b040e0451003a840c2440e400007584070401180002d030007022000510200d000345140c0140306400300161180740c042e142c40d0040071001c00500d0383c030302c003044150042c010000c00300d80c007115085203124880140051312401506040c1009481010369014440450180c6200700c070781400b402c40c0300c890f46004404009172042400d200400c421003040344110200d1107146400111b0a007954954070b1800401c014819504004000e03450716070003000803603102d10407038140c5648d925000e0003e4621000c0041324042d5000040029982035045040c0c001e10301c040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 789005170 1250 789003920 789003923
    0x90126161a04080a0b091009050c060304031718100b030c040f060f09050a0f0b130e0c0909031b030913200c03071b1d04140106080d03060f05030a0b04 66
    0x500e0a05445030002d0b420704c0480070b81034520040c0c00c000e024a06100784030341c0c030b0b12881c0075008202c0703514140e0f03c99807100441101c0d03c0c410708010000030141070058440308a200140c16044d0b00520700045035a071100c104030301c61035040c4a103038a9010038542912031a155080000c0040c580411340204000182c4401100c00107a07903110a030018505c01018494000341070704043c00300d00d41c07814204180464007942c410098943c20003143d00c00584480022100c42c040d0000301103146c02000e100b1030300c0d00400034030164000d00d4171410400c5442011000d000d610095445c05120794402d008003650f24001c40480f00c1c2d100340c0a001c5103005c044140d20001e03001c1150300b907503005d17440c0b2040c5500164001d88040031098200140c00c00400546925240901d8540d440001e203007424800c21030400380035142c585841c0030300c00b00440d003441920b041d00008001c20741c009100054541481c60703121000070403044007081c1030050118505c0e102040010070b442001e4010300340c0c2e503256205c014000c1d401400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 789006420 1250 789005170 789005219
    0x402090a0515180d2f130207150501050d14070e0c030103020f102007120305030115030509070315240815150d030c0b010b040501080109090209010608100509012616 72
    0x7005ca81e40e4440180d214040e01500000588480060900c5041d440c050326202c0c202c40d140c10010b0066596850111042c5500685001e00b100902811240f42030000d0700280c9504585200308070b03583c48040001c6040c0c92096808400103d88442070222041d068a80807020030300e4003a06040e4881041d2a00490007203060444202c3d6030b0707980f4003101c030303072401c1000b5000104008010301015240c00ca40c284081b0581ca8104007c0c90092400781c0c51b00d44500001f040079111500c22a00100140c10110071142004201e500c840c0424600042c13101c0b0b03522801005020321446400c13a40d014405c400d02c100e01c2030100201c03841c01c0c4c004004031545400012418003548600c0c031400b141d800c0849078042c004642c12260380b5420a8009445420f05900c0b00100300c5c2080c0c14100140c507260300d80c030704407802c1c4d05001c0e01c1c0303450b415141b401d900c13090741055170040c294000020381500c000224910f40c40d4150007403500011804465500d0304004035a0803109503044a0400c014031040c01c00030031255441c807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 789007670 1250 789006420 789006503
    0x70b0c25050a030305180319030605090a0506032817040e1e0a060b070209060114070503040e060d05120c030d050a0e0c041a0402090a0515180d 63
    0x389125108092440103482a074070100c0749008043c2c25201e20741e0800f0f0180b04401e207009400c102c2c5070352841006a0100d09000703c0c06d450740514000e40040c800b51100810301541c0345042140200140700c00c03541c0a1080c4100000141052001d52103c403402001c540c1e6210100c0c2582c9074424107000030780804200d081d0030000041d070b1040c41c41540340592652910250880c0036070000d900280c40c06043c601e282481c0c0304042214550140c101c03201e03143c0c191050225030f943c040c01a1054042e000501c8240c11000402e10100080031000700180d4480307071580351494440c47c1c2401700071590180c00038000da02440e9072030b0b11155003002801400c10701c80c00b140d140540005c060015143c0556102e4401c0381c80341360143c18582c0a2181c0c0014600984080007089001c83c0042c004041551640d40100e0b0300085040440c0c850301d080c0d8000c1c28001e085c0803119803034002c1c1c8648651050002c40031245554403981443c1c83d080401411b81c2d50003941c0e945500c0e000c1203840c2400d2015852b0341d048400c000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 789008920 1250 789007670 789007717
    0x6030b010905060912010912020f06062b0c140103060b070b01050105160c0321080c0f090310112a2d01150603060e090303070e010c0b0a06050a0501020102070b0c 71
    0x7d015003601a8441c0c4042d02c44c000d84410040d14003049001200513940180040006545601d800c1c014124050310000b005040403042c1104d6510200b2800f41c18408514000315050701c0c1810003910340b960a03641013245599401b0000c0180c007a5140c02007004500348010411984544044d080c54142d024010050808556503004100010ba0003202c986944418040200c0b0758120902c014603030606003141c284c503000460150b070342310380482030018481c0450a00403a840c20818451400880f510410035641c480000790926084841540109901084c0070030f80c62030310110080750345820300020076800081041c615103805081e02c07825681c03040107004080713030380d824080c043c4c3d0301c002007907013100090030144004e094504507000241c1254000c000d206a01c5000004c907640f00000745400f0140c0c2c80303160012030300b648400f84090845134800c000c4c0001c4040c560f12000448104407400d065050b40d65005a0a078001d02c000904030000b810000340b400000c0c000105018541800502a1038545 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 789010170 1250 789008920 789008923
    0x804020310020c010902040c0309030905121005010314010509190b0c1612030e0c010206010b0307170703020c07050a030b040318080a061401050a050307090218040f0c020706030b010905060912 84
    0x83c00e40b4201c660745030f032202010350416118580403803005107000e10100d03000b0744003d00080010301c50366004070080940045015018001414600c018800c140500d59481c2811b6803102a40c5205400320b520308070108820440004500020304c50310802c00d04c0c0108103032203880d8000002005002101002c000102c6080711036000040c4051042a001701c14882c0b680c2d004040b2040c42c4c00e9803603e50f0015a4014551382c0028009044610880b145a9a0b90302c19004032012507a00f4419058080481c0900081c190190050302412046004540e65150382e802000b000d100d1600c0043d251000201c04540860301c685036a41030405a0080c3c4110341e996460b46a14040d0503031001d5540c15500c0d0030250b52030705001c1640e401040200c1e8032601c40b41c10980003d8480c0341c1407040c40b50b11030780001c01c0e04102c00344800716403103a4001402041324242210030000908095400500180510103010034102d00a10079552040e0069569803c0e45081c00203125040e070041e50541c0c1d0140ca444a0b81018034070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 789011420 1250 789010170 789010177
    0x408070e1308220e150906040b06190f0305010b042904080a0b0a021e160219050414010609050d03020111041d01060503040b07030b010e0904060e0c0a1203080402031002 74
    0x1440700e60911080c800041c0d91207050440c0c214491048004040c004801051003000c1121181212007491b01d880782d00000b402032600713943e196005800480c01c5000191a519903140d00c030050345600d2811256002d044049880900074082155024003081c044809100501c910b000c102500c10310322201c0480d903003101c40c1c0240c0d03c00302480d4041c0e1180e004204400c211103400c03005109081d030410420f14440701664280320403a48500d900800c0c0700e0010a00e9a141c2c0462540182441c5803015841c0f201e002c60362074900600340680d040107007004451850340c940b281250900c1c1d0703815400c42d08280401141182c1c4110603401c564880589010b1501c90000a100502e1780010460300e01d50780e08822480400305901c80c0c0c050040520400010842d0080c800b07a001030300d840c00085104900005a414400700c0044640060000c41000100052030740018070581c291000c660410b03c9060406c1444502805001c40d542d4061102000090145d400310742c010340b00030f0513182591082d160b240202e80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 789012670 1250 789011420 789011437
    0x402130e0303011809050303070c1a010806070f081302060306010c050601140109060504030503120c0c01050403021f09240e060412030f020a05030612210408060c0408070e1308 77
    0x700004010803500c0780c0340d0714101400045520030305c000162034540ca40c40340802482d110a0040003041d0408001e1171040da0004001c1002c1c0741ea0081d6110403005540362003c42c0d480e804180e040c200300c200580035540e01172248002410868072480309600340b00c5103420182c282814000c20b205100d001030070505c41d1078003a0a50802031b000407507000740018440c0301c2c04ea001009200b01040f040c00450000b2003141c0240303000c412283c3c100c0c1c0301c6d076134900204e204040b8222915440d201c144010164045210204003005804d030703814401040c03500208580809800800440310400507100c1c40b048242400d12049030150000741e00020b07898100d0600104031000c850203c250b44402c00d446800d44246d001410b4820b00441c240003440c1400342c401d21015090344d11030801e901c2c411807082d80c20892034400700c42d61750b50805071010340382003202036030414082c00c41540100c90000340000040e200351002c41d84410000d00c071203840c08000b49804d500c0039115480309044858003d01150b0f010f0010171034403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 789013920 1250 789012670 789012673
    0x906030d21090f0c0504050717040503070c031203060503070f0608040c1508011d010501050a110709020409060e060319030f0201061208040e1605180a050d0b04051519050402130e 78
    0x10500c0303250940c01403249400446c801c40c50b203418803180a07800300310808d20325015801520692a24203049103140100c43d030080034600400170100c200000d005a12001107843c0e10b040c481e2030389900030941c4904550103598240500c4040812400344541a0b032a0480d000b250300b1521749803617050440240701c60341980c2d4046242135004004083d070070081c440b40203800300302c00e04965040c0400248a88510125241040b4060124219550060050303c00514002c8001c65546507520f58550241c8031500c50000788507061400102141804911000054880b2403000c1c05d1001da59410358050000c60316004c1103660700d00010410388076480610034064004e107011134443e4030b00a000e0101d407100501300f00c000040d0a500b5040250450252485d640a105602510b0710402c40881c5200710a940603640c000e009490340c9040c442c0c1c80c005c90780914011410b554a003648101402c2d403280301030321100801251f882400d408250f1980c0059005403000340300c030750345441c2c0701c5226064400f4034a000703007203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 789015170 1250 789013920 789013943
    0x40203070309300806130c02060603010c09030503070b0c0d020406030f0507170f0a02090910090b06030408030c0708390c0d06020a091706010302010305060906030d2109 74
    0x107000b25a00f2052001d9030f200650b180034000d50040c01c1c3c0480000260405002d08071000c900b0139a100c07619010700120f4072004200740c000c4c0d103c0c003d5841e442515582e000f54030300262080264490a40803098a4110340214070344000c507511685908c4000307220805038801403020382440c404500080009203000d0364041030006054171040101e54018280030207101c0d050706411010402c031002a50310503d019007059165030750000000207032040b5107050750b100e202041081004d862454500c415543d00b840c003001421515400e0009910041c0c81c080e05008050000444e0600440010421248680d03101c50030520041e060301c0198050340c080c58812401042a481e00342d42c40d4001f01c130550070050003070070030802d0324022604500481c02c1c050f098540005501c68940d02900d000b00c018074a0300c001c00044020448420f484d8036003030008030700003070420010400038940300040701e004000041c05030099240c802d01c1038520381a000660b95042d00851422616208a0711a1105060081140460 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 789016420 1250 789015170 789015173
    0x507030b1e1816061206050402071e0c0504111209061308070215030a0e011401050d06090204090b01060f1202040b09010f09030c0f030308090312070c17030a06061b0b070f030605040203070309 84
    0x903201c1c5038101c48e000d41d10502c02d80703011421400a4900030520000c03046004103a608292030003a03910b80040b0b80050910920300c0100e40044014801d11104a940503690b0715403825080d21840145c2d01088482640c04a0f64089a0010024449148020304a60700661106004802034104503941107a4a95854800d032403400c0a014002c18041c034401e5640144d03062400140c010070a8000190400d80da031a00d071011511180c0c0a82da030290400208a9103603524203005016503080d82c1090f000a9442c0c4251014490500988080c0c2e80203a5101d410304050000459444651414a90800c96103060010100e0410070780c0c0e8015044a00c1403042c5c0a0450a018144900107001d60045034020061b00009210380107003903400404c00d182c80a040c8481e4184001c1e400940c9440d2049800000140114035000340e00034000c8035460340750b0b040414000f52603c44c41c18526040036001170302c0b09000840c000e10810a410710070036030b8240083c80c691102c02243c12600102d0320340300400c0d0751701003010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 789017670 1250 789016420 789016457
    0x10050c1509010c0c0213270f021c03120c0e120106090e0604110f1f080f060303030603120d0f1406091f151b0507030b1e181606 56
    0x164114a03d06010085180c13650108014415100d10900c0560b80c44d401e1104000c1c1280310681103074540061299540c60906140d01001191303402240b00b401c01050996240b40c0165a03000c00c0344d0940c9a054210001a04c1200606032104d0b122040008003260504070f03590b144c2c000d290b802400800064101e00b42048141100e106c07076170725035280c0e01283c100000111202801c0140203000d0700c0440036a20103c1c04505424902104101c11040b25654545c0555100c580c040c85a45e01d060250703943e032194814580c5a00c0291840e58054005250121a90480340c00420f060400f140300013402c10028000c402c04c0b640c0c200c0342c010840041c00103004c2e040c41c141c0460394203c441c41d60f1583c0c1600d01624041d20444c0c0c01e109d84410068008114030b40c49001d000451f80e0801400c1a4091080492400030749a07142070008403020060301c030104d10003204004034001d00c4000180368030703490388074007007a14015064291100342a00c1622540c030000861088108018001e986403042201c800303004c0030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 789018920 1250 789017670 789017681
    0xf0209100e10050a1a0f130305060a1b03020910110c1c05060603032b18050a0302010c0e01050d0506030703052b140703200d09030611071110050c150901 67
    0x1042c4694075403080c58003070b040c020849074039086d100c0758503075202400e004892003481603a03c050030900036141005010519038200d20900140d081c1e40c0819400011000c1d000ca0054244941c0c0214201c00c00c0d00031180a0842080100400700c1120b1020102c3c20004070321240c0080c04450310f896407158082008001c0141c59003110044001c0c44c03c014840300000d04141008900c0d001c3c08240c2414441c407a41558405002a440c8600340c101000a81c140183c0d0782c0a40340c000c800640ca00700d540f4092900c02c1e084041e5040c0b05170350f9146040a1a160b03000900005070006505000f4284d0000005104010300c0148a404485801d90600540d65141040a05083c244203101c0340352100c40100d44040200c500c03480e41814554509078007000000030151210020302c0f842e00c250584196410780201004003105d216002c148501e06d03281c031069441d0301480c28001d03c8049624a20350300c515100392481c02c010306034030303089003040d02d8a65414601003c000070020b0822091060002000c401c0c000e4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 789020170 1250 789018920 789018929
    0x910230306090d050f0304140316021f05090d031b05060601110303251b030305090d03090807021507060515010906020a030f080a2d0501120f0209100e10050a 69
    0x241c201100807803c054214490b040007149110f000000081c100714140d0405401e62101c0030407642c5038052480041c18500c002c8406901c6801c03800500806c440402c01c1c00a20b0701c0301a9140c81c1400212400e00810a1242d0340071014041c0e8649044c2c800c22407403501d80c2c0d40d5070240005100030b040000c0050402e030080740400e1003030b030410820080c1150741c141030013100c40089280300301d00320601c500c02c0722100308108414400010850501041c1a0305070080c40c003500301c4900341d0b10341901005040e4222154410000c0c0350250a20407a000351030885034401460540f00d05041c075142d450350780c1200710740c01107d100f403410411032004415542c0c083c00144c05403210740010700707600d5a540c40140c404c07071187e440b00040041c2180010104500d03a04140250385a103060740c45035020140c540b58a00103040300d003002c003501d800c0001890401382102401d0701074220328000c88604141d02070006403000140344503c1c4111003480000d01540420b0118450700b0406619001241880c0070040300f10f045500 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 789021420 1250 789020170 789020173
    0x10f051017062203110303040302160b0403021c02040209090a270f170f0f04050405130b0c0f130305010507031a010905090a0f1d0705060a0509091023030609 69
    0x100301c0c40550000078214420803030412501c1880f00d03440c04489282c1c0709180001c09000110910040640028199068025003008040714541303811248145000e2488065848400210f45400d00c4066071140100540050400340c5000920404100c1500b001d41e41401c040d80d0761156200082d142114414004031000750354958a0b00540b90810700c01d04018024001d0000c804848900341e0091017160810b1300540c60301d5840345513001142c0199005803203258000c40c00d140002f01e200385100c0390003800c290b203c84d089000d80c070fa403c2e10a4864002c0d11143c0c4031002c040150ba1080c405001080d0002c0d8820000070402d460304040080c2550301c0300340c620390840d00c6901d08480e02d030703001001c10090768030984151110b6a102c030940009460b201224020b80ea10b0b088503000c1c40075080d1941d26452007044110340c1560ba44d403003030041c5c600c100b03900140060401d01124603d482c0c203503104c94021080c6e41401d42c08684074102001280c9041c05000ca50265030b50b031200ca0342c2001d0140542c45941d460 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 789022670 1250 789021420 789021433
    0x705031c1106070c060e0a2a0503160312020c130504030f031e0c03140901090c060c110402070203030c060c041805090303130318030c1a031003030f02010f051017 71
    0x48080c00c144c00259004042c40d81745d90003042d8550b0100300c203000154001315800209007013911025500c45814544000e80721030700d1408501400d0000b2040450b504c01440002c0740f03490751301c9005140d5003c2e80b000046014100d00303040c01da61741840208902058a4001440e404c041c68080c00900e0300c010080d041c103061041c40c0a03050300c0d0007100540c5441a03100440c40e0780f0f2484084005100a030224600785014a041c84913583c0150b111040c1c1ea44240d110401d955114a800c0e10f40c11501d600c01084020540c0010f103135414540c024109042c4042c0440341000c4450310000d08080701103d10613030003040800c2c10003200344403130054060b04610301e604110a0a2540070340c0c1c0c403232100400341c0d00843e4030441540c0070103115510b070348101c03c02030181114041e26403030300c10046507039403007045040c2d000c0a480c805402d22a00440703000b001d00fa00800900b9140d50303070541c0c2180c2c0080701c40c0c00350f558610110100d200d6070f00540d44a40034840310514400e0030032008414180c051055005250b0000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 789023920 1250 789022670 789022681
    0x102040e2511010213090c09061107031e02030d080f061e0d03050913060e180604030807140a021c03060f0b0f130305030d0606021606110705031c1106 66
    0x45040244480c591601058200a0b101c10a02a10a00f40342c03000640d000c0d100061181c0b00c5030300c003048110082e9101e20705c00b9030b5500c0031200040c0c02204807007140c100c0101000018900724104c00301d240541c40044060040340c0000341002e5a00d51208041000d4508012200c2e8000c902182d110400b141c0d100e010310140740e04210301030b070509140c501641c02c1d280e441e002e05d80910305440711a40003c0802c440d10107544900340182400780300d4201900d2008000c548052507500c43c03811504551001406142d031303251811900380c0005000c071000d014031540c6020351100d200004019040450300108031210030440305281c1f900c0c81c1d003040010549001414031032240d9001140085901d8140c85a44424141c030400c0810700c110000301e11000300f0310100004214000c0040e0580c8400030204008a40e69000260780b2078401e400c5d0240c1c58580c0d0700007404103a0140c1c50000d4900700302c404071824a0b44031404030b4070700780090200702a00f05010121010705544501140401c5d19004c0c040c20590405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 789025170 1250 789023920 789023971
    0xf0307170f042121020c0304240e060d2a020705180411010c0501022106041a0a090213090c020a0c0b1213050a020306040b01080d02060412052206020102040e 69
    0x40603101a12034181c0408400b0304c0100740c05542d2040802016240e44a598800700750071020080210700340300c4080c40300700b00d6072401804006a60030f00a4407031882c090b07248410000502041520703071103d0030454088203800365102030b18900d0f0300c115001040c85d03d091400704100f0255401410f41c0850301c260030440003032841c900781800b001d420701f41010050014130744075019000d892085010041c030140c0300b02c450340d05403040602801060b14100241ea1109008141421540c03220f01e8128480070002c20040d1a560300502d018000741e001c40c1021a128888442941c0f4107910460043c0c1c4055042800c0c4104140c201000344200d8000901d004400e50a004690400500040d5480c1c52a10498107103d030500a140c003682e401001d131000b62070b1501e00040850070078051042c1c2841404d410100da58000104940a103030407240d0244000c20a0004980a92080c8a0101c0c016030811540c00e102e403c1c440d0a401404030b40d000907840364141a81e21040090040840b0380c020094001001402030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 789026420 1250 789025170 789025187
    0xc080a052a2a010809030d020304030207050a051c0206090d05060406050604051608190204090c080103060606020f03070609020a05130b0301050a1a040509120a1805040605060f0307170f0421 83
    0xc207090030004c1d070740c130407000904500443c102d1504541c000410001059804a07052040e00d4040300c038142c600303480d0300510040858183d8801e003542094800b0401510340003000d0118404002e11414180c0c02035610241440d80542d011201c0d00c2e2a8001d022240c540f60150356400f044900d01c11b903110310a07260003052444090001c0c414001c1038a07243c0c50380000e40d01100c001e4003a40c40300f0700100e524510000c118090074401038a070540b51143c0865400d101080c1c408800440700011b6050140315101e110007800007141c202c1c0d02100a010014050310350110040501c885210001441041c50041c142074800c01066500c08a1401d000020b000c3c80d0a00f40800000c42610300041c3c036515203551914201c40d9180c030300d201000c0402e40b02049540010507000c00542100c84c813120f01d60380c0717080c441540c01c24080e95900c5481400b008000c80180400395034850072314038010300c2c039041c1501e1a0785202c400340c403030702d2021500c682040240034a1141884039100b006504415054030325900500840 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 789027670 1250 789026420 789026503
    0x2e05040803130611030f070e01050415050306030304080f0604150507270e10180c080c0f04091103012117130506030708040308090303070c080a052a 65
    0x282c2041c040140500c40c0e01016030030040d0b1840740d0752410324800e80301401004851002c00501c002ca20b5011035445241500e040b44d00401c04a442e1920651058400b07800003824070790144014403001410135010090613044c04a400050f01ca00c4c201400c0900e810032507180a08440340c28081444040769010300741c030310219110b0103000039483c540034554410701810740c0140811002d010600440c50000c4000900710381c900d440fa59030030342c824510841652144a403082c041010030001410900d9900000c11620001000381e40c41d06854103103240446180c10000c620364140400140044009002489503072148240d402c0c8014180380e407031038010154410a804402030119a1042604510740443d0107068010b08040d2a4601114000c0c4401ba049138158000b4000c0000316481c0035000c0708807405603055a07030f10107110b091910743e031807030303a0004034120304000007009501c51840644160001e401c4600d9490f103000002155002d1900c05e031181508503038085100d8045070843c0c3d00c02c5042a44d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 789028776 1106 789027670 789027691
    0x30b030d1b030c05030706050a0911010518130618090525090207030e0d060c180e0103060f0902030d020a060c080708040b06060c2e05040803 62
    0x46000c036101c0716052940c840c0324001c244102c0100350054090400c4038507040041e80ea507804c4843c102c50b46070143d696001500f0800c10b0905100306001024039000b414040c2c0c1079111b1204000280300c0300d00c036208030514051601c3c0517401074001869900c0d000c103000c01e09195804054520702d00200c805024071106804441d100300551869406400c182c07030a41c1c0c4c2441381748030082d804040c0c240c0500c5807240c00840e156564120b8005d206d44544008030380403461070f40c00f4204905201da0300500140c02901809001010100725044070b03007000010a0b43c48103402000c0041101e000301940500a41c1802003996800150f02c0041508c540390402ca011000881220034010550314900060b04580200d804200c5448442d80c0141008060744d10b01030001c0552441c1401c10f414100624240100115440003481621a00c13401040c90a002ca13241540e14050b1501c402010064603 = true := by decide +kernel

theorem cover : BRFrame.Cov 788848920 789028776 := by
  have h0 := BRFrame.cov_init 788848920
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 788848920 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 788848920 ≤ n) (h2 : n < 789028776) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
