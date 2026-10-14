-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1546
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:30:41.641456+00:00
-- url     : https://prove2.me/submissions/db438fba-a1f6-47df-b447-eca19e3c3b0b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 277877697 ≤ n < 278057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 277878947 1250 277877697 277877701
    0x31b0a020a05072714011a1303050601150201020304050d0e0f04021801080105060c0d080705071b030308100602070b130e01030305030402130c022d070306021e03010303051603020c0d0b 81
    0x130302c00c0c11180c0b00c441440a02d05100f98100da4110704402c5030304684c0080c08812001042c09013041c140d208048000c1c034090700044002c0180840065401d0490b00b218000074402d00c5410000c900302c0c0002d46008002e5041001c11560843c07055a12100b16400140004400e94416000404a0784241e0100c051001d6040c02c030303d42580c100f08103900510007a1142c5141417081c8418580307440352131003007070b043c025910045000180310b5000c0d6040580d02007610361500111200204401003c1d00c001c07000521008001468403ca5400130421a0160340092502c181850003089884e0000c110180210300360304c1001411b03c0403580120700841c0030b80c8030381e9a207003014010310220121f00c0c940d481c805401c04c21000c1200d036001401400100078610445149940c8075a008009110b284440c07100384940388010083c0308030b0740d0052204003821000243c00c407451141004460009120180100f40140700420481510300c4d915088640300348183c03109410b40000080341d04082d500251914522a02 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 277880197 1250 277878947 277878989
    0x702062a0a030f0e010608120717070503090f010519110a0b0f01080c0603070e010e04060509240a290c0d091502150606070203010902040c02031e031b0a020a0507 71
    0x843c1425254550000340089820480025518203041c01c0914550000040189c2440108050381842503400307888159548101e0510315900c0c0c120100395441504124106a5158059402c8135001103100180e9070428800d040c0944002440801006003030103040b8500000071600e40100d80300c4d45545c20403903501d50500103520300d040c031039441c420f0241000b04240003406070000030f041c40360f040900e0003520403200b4201180107408140e1005400c03140300c005100d22206400070429400d0b10b5160600040034003001000b00d10001c0f88220300308008405e9407540c50b0700015038464284d11100a007245000c9682110b50318100c8410705250000b0031050050014540140701c135001d1164503c0284604000e950201109080140c01c00d8840c0c000003907041e0440d2000e4220a2000342c00500400031b80450030380107501d80d488000c1c054071501682d9881d20b0140d2550041e81d015000448850443c41d0318144580704540c03206440ca0258464109100000303803007000345101a20040c22030b0604c84030060 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 277881447 1250 277880197 277880201
    0x20709050c030c07020f040c023012060d0c030c151716110102040b0702150307080403030f0b13090b130f02060702210106060e01080702062a0a030f 65
    0x14010012190900e41031040344401c0009880d084000c0c0d07020b681d40d03581e40c0c0c03001552009141608540150600143c103003066000302c0c185400c02070030506801d03409000c4803262000c07000543c4146400e042030100e8242d442c20003802c10781c4800e018015059131043c0f51125001c8480030740c800c40e803001c800354060200320010703203406600880c9818047c503a182c86500b0950800b80040040d144a154400c90a6026108111034420312200300000c56465071202004030301750f44844001c2e402150300c10300c604440c0a1a204580c4542c6003966682e01546407560114082e0080126240055842e401c4610043d5111840111209180c99000500b402c003441c181150080090060518460740481c0c0d5010801c840405203010340d040305c10ba41d4500080c0300027919400e10000c0c5000c0d02c400320312181c225210560120066841c0c2341c0714130007000d40e4100110f601440c201e41c0c03100143c0004002c02c507101d0f50800003030701c8940b9641169a88041700321000c219a0007440c20031002070b48810b5648203c00c024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 277882697 1250 277881447 277881449
    0x21302090d081201080c09010e070f180603020714120412110a0b0c010e07080c0112020d060b18040903050910090806090a0c0e0105090c1803010f02121509070f050702041b0207 77
    0x3035400d10090340c9408014027072007900502500c1488121000c0c202101c0c424609401c0784400010008149038980d54020001d4000c2c0808888034036644100100d610400111201c00300190504145802c1c02c10204820000b6014421142000e1040b01c120940e0759201444010700340f0b40005549942c0c209a880e03003503074011801400ca58024842c04d002e5082d000c00d42d446190002e0a2031440c0d002d03518451002882511003603002949059004600e01040f400101100b040f101203808200c1040001c0000310f4000890040110f1400c20102800b0b050441c0c600344505041d041291059954895050620310704a545a680d03412070440c0c0c808104100c0040b00c054034007213542c05411340c1080c002c1452000080d188841ca000f002c1074064111a07080c84441e40284054000c1c010a0b0000c00340c600650002000d840d1a4200200041d500007001b00d0080751200340203180304c42d903441d03060055a40d05000600c400c00c0140400c061005600da501400d01f40441c16500401c1f1100c007400024244026 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 277883947 1250 277882697 277882699
    0x1b0903100f051312030e0c180105120106180906020904091b060905030a06050615070516080c0d03050c010f1d010b0d050c210a030e010306080307021302090d081201080c 74
    0x1090f583d180030503450b075600303881c00b211800d000500d20040c0210324900003081001c5035020001c201c2884030b9020010040d03048617010703a441032030455410f0050382a20240c0c040c01c80c101c40a045221009c05194014510031070080400503d00200342d00881c050f80d02001033544c1c07201e58124105c4840e0380715624400208228038001d1390550030714002076100c0d0703404034001e42200d0702c1344045840c0342d0364590303003c2210880c500d411380c0d100c500349002a194041051100c080351007404000501c0f090100320381080000042c42d4240c50420760350192003070781100c9011007041d0b50f5400c2c0c1c400c10910074490280a01078082a009070050342110050a441d6501e40c02405200d44282d4000002c10004034021040411640221200f9901c00e0421007502110302c580c07950f114102e900d40915411040070b00c4000c1c020390b014010140c990303801643d207104421001390418044140e4030f51601e15a40030300800d110081100700d030743d1400d44a0300419000401c803010742d41481c40c0100207843e010880300f120000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 277885197 1250 277883947 277883971
    0x1030605010504050f040e031b0601061e0c030e0406081b0607030c06050a090b04080c07063204050a060f080601031806020a020c1201090c09050108061b0903100f05 72
    0x414032000901d2401988203041c040d80181010400942d541d820164207070641e201141d0311200c4c400c401000303846255840d821030340035540001c00c0c12445584410480e0704081340f156031801200c04110340d0111144400d4040080703401c8860f28a64641c0542ca00420400000b0258082207103500d510041c18464068401e640403c41d180c002038000350a00c09040d04000001076a545542c800741c06494506401086c2c088254200000c00641c0d001418030703030400c2812030b0036182e00d07010309a46ca803184c1c0d039603081044040311090b80c0011203c4000708542c1c000c200d000382450b070703204c02088441d0b0701c40d0400070120700d1188201c160658009805984408246000d200800f000c030008040c1b0000440c001d0a901d4000840c1d04c4610300170441c580748148058242c24451403180d0070300b03008100c0740e0004c80d04d070943d18800040d944200d001e140c0c103072000c5401034507013600c6280344203d03005040780c0004031180c028881003e60303507003d100400c0c0c0c62004040200b440c1480340c44007422a40003d0a410500c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 277886447 1250 277885197 277885199
    0x70b0c060403200d09031a070e060a1e0c141c030504110d0507051002120d0902130504240903120209010345030f0503250815010306 58
    0x40400200e00d50010382600b00310380c4a40c1d030f014200400889144041c40c00d48619142540f1036a4011112022240240d40c1c80c1e03c1c00d00c0c4003000d5541c00100340e5280000807120fa410740e9481c0391040040c001c8079401d040a06c0e100da8141c0b99080c2001c00700c1c101801044041c50711038188280141c0200c0d03440c84103005802641810044450b0100e43c2c0074003902010368640c000750030002c0403c0c22035460000206442482a918541142e0347c0d00c06000d10760080d5010706a0141c0140005100c5c0b000c41000300515080c90f520340400bc0082444460036640520b280750350000b0070602d44610742c01140a4400710007910940c0811548a01c00761047c1b9401c2840c0034450070219a105041c4100a04001d00140c1e4514000300100d01421f016407031080380d128002c4001d1140c039100300c0c10031890244013686500c90074050003c0019140510000380c0400e0300c044801c08018801d0f802541d11610040d4000f44180301c40188411445070725030300b030300170a0555044c40801505000b441c082030209203400d024107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 277887697 1250 277886447 277886467
    0x31211070e1303110f0a060b01021b1002010603120206060a0b0c150901060b0f070209011a030703020309011107030f080a150512030d0920100c020f2e02070b 69
    0x1410000c19040c00600c0c98500802018491509420115201c0e0201d46440340c869107115182c0483d00001c4942078030700380308c202c8554004210801d040d4074101420400242d18014040181d6a0305100402c65681e228040002441c0b40002000841d0a60041c0014a40441807041c0c1d40c0c080d4200701d42c0c415050100c1d552040000482001c84100300c01d4550413500c4000700303240541a15040706d8021000070a040c150110908003401c8801e00850781084aa41d1302c86200060001c510040c9452000400015114602079002140c000050700c000165400c14848000c003d6040030000f10300242170032040c844020380c8018160b42204030007104020480103d410010140810720840740101d00300c0e61041045070003802560010f0400302410702400301c0038130308007611480764101206682010030301c04d2584d09008038001d03455141c6072940200d014140c3c080204811580007086e6000342c0600100307201c0c21400b9542044005041091764180b2044000a401c2001c00d030000f0420110a01040b518 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 277888947 1250 277887697 277887719
    0x70b0108191415090a17030907150e060301090f050f1501110f0106080115090c02030d0f15060207060e010c26040902270906010c080c07090603121107 66
    0x80300c0d41c000b062192040c140b010280c1060b420007285000e00190b00c040003000c0c140424108000b0380309040340d04200c1c010380c9040186000594070320000358880002440001c40c8406501480096030500000645140c0001501540300341c11500300c554a82c03610119a80c801c0c02404d030001013000040c14a403812141c440100046002c20b941000500811462001400d100e10302000101a0081c40350b02e85401d4941d0203413000405992181022401c0003d00ca2417a22594030641e41e103901461070079081c40c1041014086400c94240c0e020b0341d440140140c3c8482800c0c1c078006149917006004224034001000d007001000c074020740d05201c800c1c00c02000180a41100d07480f40c40004600d64540c0781d81034041000c0e030082e900030007890351001480000f00b0a140064494084116070111924041701041c02608102501c030180030500c0702400e0000111610044e00071a04108102c0380740c66134808001b42a00c1c003075031080d100c01400a8603603061650200308070440440740c0c8020701c0f4081c41d02e64034401c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 277890197 1250 277888947 277888993
    0x6090803030411061b01020304060603021206040c03030e28380307050f0d090b01060f08060904110406030803150a030201090b0903030412080a2c060c0a0b0c070b0108 73
    0x84102000215565001071085c0d4082c007020000000715160300c2e00d45000001402180001c2c4d10400c0a8403441107841130004405106a030301c100b000d507400e8590b56043d02c8072560440450380c00700344140211110912807c003101d00031110b4030010806494a4407801e41004900001049130b1100d244040c07102181c4002c261584280d0301000755130b03540b0b05901b181c0e00c2c0074041c040f030000440050048210072841d00503280c50b80c011070020849980e103000030b683c42c030b44603c03c9801091001000961074501080341725032150003009006403480101d000502181c02a4008441d520030110600103496100036294400b90320540da070000690550f0000317001c0804a200c1c10741c0e010b2000452000742d4805100395001000c480e40d810a4106051030144980d4201e48000c100113881c602010350542110018445450701c0140c00c00d1440490707a00340000c82d442002c107101c0520a81044000240c0d42c41c54151050a80c207a0050f01c0e4a040d02d00b91202c44810ba000c52409e03800240c00081c15219024001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 277891447 1250 277890197 277890199
    0xd020307020d020d21030605040b3303100812070c031211061501030e06041112011515021006060206151903031d120303071808030304030906090803030411 68
    0x1c60b8041d45440024542480900e000344000c00301403000700080c0b40d4544486054440b9207042c07043c952540280300c21200704c1101e4551200180c0d501000d240010000d500c561240042d200d04031a002e80308201107a441a00ca0b110720b049840020004200244134990781c80041c60300030740c034000340b989800d90312005c240005055001c02c44a0100c04038020a101c800d0002d000e000c0e0b848038038000c400ac1c0070312281c4100309804241030a0350045400d05c040f07042e80c8595800040001180b50f18014082e081c26014401c0c0a1507588444a101103804005820020304050308600304d10454580002e040080d149030a15040381805030502005030041051503000c0c140b0801003401070702080c00108520b0000702e6039a000d03541101c01006259209028100400d444105000580410014003030b4901208640b4451030b0030a10200350400d01c2498a40c150105002c600f1944a40303c41721141181d00940c0c04601054401200304400d641046100b0300505000000c1c41c21171905450701c2d40103a01c000c1e045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 277892697 1250 277891447 277891459
    0x7050a030c0c020d120c0f0b0403090509060a06030e0a020402030a15060f12050604090b0406050105010306080d1b03020f12030603010f02030124141204060e010606021c0e060c100501080d02030702 86
    0xc03071005d511602119414580246071610b46d0f6549003800b03085a4400d481c00d900040c65a480401c940c144098424000c0340007501c0e1ba81c40c2850140101c0040000e004611040d004007401c06025030b440c0c1c0041c6000d5141c02000140703440010f603c2511052030799004200340a507201d40822840e4001410182c2e10b121420041341540d11140010001c01c107400000f8100f8984405001c140a401da0019060b1802030f00e0030417101d034a44810a542ea1352142c550070020b110390040001150713040c4070003140c031032113401181c010a48100c91681000304075072641d40f4501020040080500c0c013409010030300c10299504510310750414103900700c20701c0d0011101c1501c2c2c601800201a00340300d400080c84074104d0320081a00d410340020a142240b80c02d441c2030350200d060181ea0300311021706120300030403a58260000c004800c2d4251307024a0614040f2040c000340004038030056201e1f11050024001300c20000c0c0036103080e8440140034001c481c0183c11440c0030307503c80200c41140d070390008110355031150101c800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 277893947 1250 277892697 277892723
    0xf210703080613060603050901150f030f0804090e03180d020108070e0118090903090b04060c15020403021e030f060c04050d0804050a0305030c24040b0c090907050a030c0c020d 77
    0x41660292014092034015142900000d1a194140c0c0022302464001e0b00030f02191141c441c1c0781c000c02855000d15119030241131020000100c024040c60f0010748921903c80c1030640d903403040801c0300c136511209489600b00184aa01281c51103058420748402150440010354941d0002490b01034024490b40a100c0f1030810050a680941034003410309008207204043c0350340760041003014220101381140440e03041031011406040c96030030b980c10b894450b0303145265117109459540100c0304400300800c180707030708202c04000b58481809102042c409000040d4050be844024035142200031101d560b0349400403010711103102c084d00e00f10340403184225004950040b80d41001d1850780710b26804641d010704030348000030810070003001030041800071100391941e2000d400700104914140b80c1c00342c00f001c0811400a00055811070307180340c0140c060411a81000200e2010680c002e9040c0c50340808288003081d81401d05900d030240b5940b01100d0f180c1100c0d04040f80c1c0c003003001c035849604000c01014078000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 277895197 1250 277893947 277893949
    0x50105070609140c010f09030b15011202160227011401090906080f0f0303010f03020103110f1809010812030f0403020c030601030804061812061a0604080f2107030806 73
    0x4000840e40d040007007060070b1103035400f0340c59456041e51051404600e124250b8010345020f440d1190840360462040891030360340c010b140301c09224000312641400403030120b00900d01004d101910050084460a0305640c03058010003002172006034000500500707102101402075080f42c80300341190040202d0301102a0684e0050f10803485580204106a1504400041d40d02002a08454044a010507038140b99800031440d80c51384401d0044c840c0b00e1065103010001940b080d4070032107400b8a04844036042c0010062240240e91000c421b161041c41c0e46c1c1d4121801e40350010500740140442e500030800c00d418502c8240d258040100b00199030388003840041e081c50b00a03c603082c001c090080a580d802d6849241c44a01500180503501c00145040000c00700c2c130707060141d090b0a5402d0b40d5864071280c00c0581d070f120040d11003184416030340d00e210419220300343c8411024102a15000380a0f040000c59010401e240004030032251103424003013a035001d0706110032000c6030a80c40d0117141c51304e4244d542c40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 277896447 1250 277895197 277895201
    0x3150a14040b0f1801050405070306060f080702150705090a090c0215090312010605070b07081009230910050a111b010b0303120405061803030a0213050310020903070b040b040501050706 81
    0x1207016400413a81041039524481513900c0c10b050f81c0c81200e00308001d8071440c03011000c44009018001c040b4400b4801e1625107805101081c1d0f01c07082030b00c100c903058003545481051424007915030720081070300800c090515250040c0480b0141400850812900445071070080d03488501c48a065140d4918a0101b48201c2c4217000b29004502e4642920b0a5541d541200800d5a40110419298089840081803400341701e003030003901070a803030b00740041c42c1c604164020004041c50f210080c0e84104181c2c840d00030040c0d4840741c522500040018219100510090001355a802007007041d14614151900c000c1c0207842040d24034001c0c015071030544c0c1c600e500031241e0040600614603070385480b020819000b9208800c02d600d20980c440c030160348803034030b030909840c103441070942559241350024030004986800d02c3c0e01070031040c01d070010003803503140d40c940100e41011003030b1714444041a00021404d405003410022000101400c105141c0f0301380c580203a40b130b0396000d640030b1607041000029005051081907 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 277897697 1250 277896447 277896469
    0x4092319180b040506011a07020102120f0c1b04060e06151309141006110a022b0f030e1903152a0318050a0f14060a0203150a14040b 58
    0x5090461810f140c104181e45140921802010440400710101d1801c240b1040ea011150b043e0028101d10804030890740090304034084004400006114810700751008002680403102041100380400b50404184801e0341d4264000540180d050f0040c0042d03615800100d030310314241340921a031030300e010442c204c132110110790092050310305144405ca1340082d5214418055411041200201644c44200f07499000c0801115419500020654005800c00684c840111b2450001c00c10004200211805103003402190980300d10911004e000c0c00c040c0c1143c24403056060440d810502c5001d0f00700c0c0c8591308522400018052001c03c010082030410540000d03410b6250201e101e0100c00c40070b6806500841250348071000030b82051080c0c03030000c801c40000c015107a0441c003e03010300c6009480c2c0c0c4002101e044000c8900c17288444041c4641c100c1404114095420b004004d03176241801006046030102200c0103a10420500008007d9610380308081c05880006a6012500c1070000700069000703002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 277898947 1250 277897697 277897703
    0x1902060c0706120b101b060f06060203090907020c09070c0302161206050106030506010903061107120f140f0d0b0102070b0a0306050102010f050402030a02061803030409231918 77
    0x81c200c010a61a0700928907070300d488611081040a50601d00411040d0021141c03c000072444030302e401245240040032140120380a9070011440b0032017a0030075030854441303620810044e000031440e00301519107601069081200d510003081d100b101c90340040e400b0703807024200505000007c90070300d017010f0082c48170004900b080f80d50404890b590b000f8030039681180f41030880381c440c0f61600118426000e0301c9030314015030040c0d69610b03441b81199503110003400015064403103a0b4007030021031b00244514007050902c040a5940d03c0c080b40c040080503011000c140c403504050740e01403188d601c9038075158003030740e0000c80c02031404600501d0800050703082032483c0d0802002098000349000d1945c2e09a000f0608032082a4001c03c041c100c2052404202c40095900079415044500600e016141c0704000d4400e5501520700305c070244645400080c03442d4025484a9032140d15507100008148454042c1c59004d140c0742c02d03080f82c5241501100420b0080f40840c2615155a220703480320302103900300080f1286034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 277900197 1250 277898947 277898953
    0x1807050909130c030b0601020618190510110910020102040605250f120e01080c07020d020315090105100b070f020909030708040e09010c1b0b0703140406091509051902060c 75
    0x1c4c0b070781017041d0000011140035025104035404140001c0388640c081c101960010060400001c40141c0405e441081640c250b0b03642c030404080b820741c0280c500c5600100310303403c00801da40741503050030b01c50b480110741d50001c15a481400304110350354020088901c1424480e4807108015990010740322450344058004d0103001004070080100410859618184201c03904c0d524000ca4101c030045482d4001140c1e84621002d09200c0752005061000003240c415100405860070410600e00c8016a8802103480301c0340d5a464509200c00d16001030248400391964a4000c2d1802000351a040820080c10700c0c000c4c010404c1000280d1540e20a1090314144e6502001d40c0fa9100d80d19130300c00c0002d0105582c50b24540d440c065007003040d14051014038074001c1c480300240e6015200350b1110711035228000c08440505483d602103000600e86041c8840c41a4868900068180414200f8200069102c9510108036103404024404190002489039031110014801c042d00c001300c2c804140e66004640d500c0300544 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 277901447 1250 277900197 277900199
    0x2030a1a030a0c1406041503090b090d201f09020f09130f0c09020a030204090608161505190203130f0815090a0203030316022b0507020a05120703021807050909130c 72
    0x62381038101e06411406902c01554944490468a40700c2a0711001d441c0071520070f201c0080c440f00c4081e15000e4600241c41a58103488800c100104c680720010780080010340c0e1940c05008624042c59820718440c1e041d2506c40705860141007850100c5500d9902034000b1404040c0b14040094a5801001070301540401303544400384c0b080050044c0d08180190b0000700c1c00d1030310105a40d1800540c1c41020385050421040039858024401e801da5183d01e0142e00b00242048400c510518048603001e80d00d038560f00030359070364100c0404071150044503000090864441002009140f0b00020a0541c14041c07280b000d5040c1c846903c0b00e80f8042d0418402034041c0004000c11a1502802e4000c208889080e0240e900c907a5443c82c0c8201840581c019000c0042d42841c01644d5007441640500140c5d403018180c04081c0da11603000500140749103c5000c40b507806148144110b041100c8416400072850098030b42d03601380148040d00c4e90046815203070260705070400144c001054000d81104082c0c210000b04611 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 277902697 1250 277901447 277901489
    0x5070e0906060d1e020c0c061216170708040318032112060e101706150609030a060b0a0b16030c0f0c0e010905150306070e01110102030a1a030a0c140604 67
    0x40e42010520184c24061f02c84698038078140b42045500b14000c8400606c26030b641c5040c3c8802e2080034004100801c450b00d40d500100102c002c00640c0603544685072581c0328506807500a01d42d07a1842c1e203044404681e0b020410003c0c00c0d4084803501c0b200300e0b120588490035003e40480b03104000303c201d648118100b40e80007810f034405a80c018003590100341140d05407034881003c004c402c50052a858401d9004400040901109100d1003600e828000d0220340b400e803241c40040d180450f4001e0685900e591003c0c400007a2600d040010b0003404071002d81810148016800410152a100080c1c00e0282d1005504104203240d001e04c510254040c1c070f0092002d8594540c80d1514409000b885a101d2410f4085440702c0641c03881c2c5420450010000c04e001d540b802d00803035505555001c901c0c14400c1c40c9409102c00c500a001542c459142c442c0e000071380003115071070b01042c0d5940380c1c00180030750465030041000c580b0f504600e90036514586072444201d0002004a003030341c03140750b00c642c0d01c01081c00340100403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 277903947 1250 277902697 277902701
    0x1c030c08030a2405090f010b04030605070e030d080a0c0f09171905070608070504030803061003020d02040e0910050f0a09030903080d090605180a1e0c030302030d05070e0906060d1e 79
    0x507210217481e5094a0358560007203034030200c000e020f030302c0c0c424001707020800002d00c40340c0219903c00c80c0e0385407025134181040082494140080c900e40042982c50381048120351842c4a0225544050b1502d4540c0d40c01d5108080c0420009000c1d0018281c664520405503260820600c80306101c207480c45e955016075828066241c11340b40c002c0c1d00000d1500c1010903a803512810a840a0f80e4015103150f281d41c452404000f0b62011040b44181855024490758a608206102520080402008101551400c4502c81d4100501290b0a096603443d26082c006000c000c5450f039070380130500c1c040000b0940305c00e060984035002035500081804200241c820145102d070f411200010703118500500068070388021030442038151013691a40d0740d0000da51800400c3d01d0f40054040d558407800140c8105840c0e0b103640244800c030b03400980159200161210700c2800510403e0b501030b16502d01114007100c02800116002405803c081c0720750b102040440c1d00070850761081c0114dc02e401c00c0100c0d5046480d45200c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 277905197 1250 277903947 277903949
    0x303010806010515090111010f1107060e1c0804170403030909050a0c02061308040305030307030b030d03180f06140f0901060e090c09090a0606080102091c030c08030a24 74
    0x110360080c0c0c000000c0c40c0c20003c070300d800504400a501420010305400440e10542d00c0000700310701c2c4d03483c2c00854484041c588034180900300010308107a503404690400505a9002182d81e0b8150360201070001c0d201c41602e10417017004401c2c1e1074031568589482c00c100c811483c80d0a02640d01d0a00000c0c004105074100e510101107900c0321805000315a10b82e90f00c042104e012218410158000e54005108400655034410080e889040810f0506440340c454a155400445001c00825a51042080e40d440c0030000d00f01c0041c114901448524021006080c201e900c0b144003c003024081c0f4642030400910340c11180011400c40382c00c10711458403c0300403044040965110400303500e805801308156511038142c2d031050006d41d00412079800c40754107001c0e80c4400205401c1c3c2601680490f03000182c5c807270051074000c0410b14000b58031840905c0810900d0840d20042060031000c1410704400039400c100303086059900920700300c1d00ea0751400c116601512051150164602500c02a448070b880c1e0490030070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 277906447 1250 277905197 277905209
    0x103060605070201020a0813080f1b0a030f0809180a0617030705031210120c0303030f020702030604020112022506110f03011701060323010e010203060d02010305040c0e09030301 78
    0x80506566140103856521a4640290040e0070180085000c113058900414405066841c4843d801c0d549003283c0d03042c84107102c00c0e034241d500b2400c0760307c00502890390507101d03210040301c40007030702d81c65030796080320060703030444000c0010002045d18996075583e640074100d0700c4614080040c40f85080020301c40241744602841428500c20340314a21801c400109451585038031500441c5401800b10040411135002001449400d13170340440440d1540e990207402c041c4c944902c003420080303030841c81d01605507803549200349035580c810320460340965000590b10350041d4081c01c00751092109c41c201c0801a1103080e501c040650000281c4610f0380c9280034025140d94011101084001c000c00c0f028002441002e030040c02c1c000c01440140110a4400d11626400c1d144800000e10180e50b130381e410101c1200c0c185090140e001041c5400b10b040028007031a0184200000214954900107000a40c130061995010741050351b900001030400100144120241404100460071340c500201020368a0b44240168 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 277907697 1250 277906447 277906451
    0x905091b0a151403180f0c1309050319020f010b0d0804120f0210050903010e0c0904020909010615050c0d11031804140f0702100b03120d0b0d0c140105040f2105060c090103 75
    0x40d0100c6c0402140d480240f080080080f41032000640c44034003c0c1890f20b005483d18001005502c40b0a560680c0c0400480102d401030150182e2461000d804c480c003015115003d110580344440010710031100b01d4054030108054442014401e080181e500801000000d4100c0201d80401440d150801c0241504ca08124000e00003400c00141e0140c44081020130290015140c5021a00500c3c0c40904540e012498000005119036a414000c04025500d1030940c041900020941148142409110311407001802d0540c22420000710f115560b21803040c07440000001d03400042c101c0e6440e50007034071007006404440034a90405031101d13083d01c60706580f17282c09485070b081e00a280b40000d00450311027100c010094101d0700c2048a588601d5848514540c0c08142d407030201111554444904036503a5018541001503a41807982610743c41e4404041c0506000d800d200800007000b0203804202540e840000380b020070a48010620700b09041045d00600c940910000c1010b541e12010141000380026a01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 277908947 1250 277907697 277907713
    0x80f0106050402041404110c06070c03120218151c022d0d0b0f09070801170c06070f29060a0e0c121f0905091b0a15140318 54
    0x100b2040344180d00c00d42509081c0b1142c0e030381c072500c3d159001611241150070761074a8030300442c40c4503007880011034285003c43d0301554144103060780704100c0140d01000010440c0b5008405040f8100e44402040e06807007a0894220404520841c00a035520b110455161701000359210b0f0950340039402081007100400c2c00d500b041c0403051982c000b1210008010303149945000390410700c200290441400309a048000c05d80f08a855880d4411440c1c86503695507940c050950604887c82d8a12000e884100e08a42c0004100308880c0d80300800c803101075a02800d100c0908103149407603002c481110300070b40c1509141450010514240801d01840344004460b00e41c503107a107030041c48000000c11746592403420301c05e00c0701038010f1100020b4030782c004a010540c0090700c030901005001002898000d0351603940c9800c148094480100001e0b00c1c03848000010100d1942c000c000300e14299254030504d0391880d219450200c099015003102040c59800a22003992841c0c2602d60f145402c524440c207105511615403 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 277910197 1250 277908947 277908949
    0x105030105100f03030c110a030b0702010e0c03070605030a0615050d060603090b01090914010509010b01090510140f16030507020111010c140708090402070605010501110715120b0a080f010605 84
    0x1e00d0806444000340d03c964154110344048913500142401110f21001d16141504241d44c0c0700c103501d005501c81c920f903c0c46440e011030002d0944030300262810443d400996400c120756400309616090b510180381c002c2d03d984d1202074410203420141d01240d8241c05100031a510b15074032000904054015480521400d55241d03000c800b1103040b403001800c00c1503844014804c2d00b0280d040760b0340c92801a20807402c000769041085085900a8842004507955000b40c5512035070030031400c0004000072100c0201203021884080c043c4071074503040100c032100000d40001240400410f542c4002e00c00b41110341d040460b440d024003190311281c420390100d6006469001502014021100381b4201941c4d80c0001c02c40702103010780175410164040300c504030144072040c6140c80e00d00c00352010b14041d85000c6840d514090025180313000200103119540c00451040c0150442000d030307407030020f03400c0c80c241e2460701c070380c4064800403c1d00045039907121240400000314048002541d00b0b0f6089000003c0001e50340d110 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 277911447 1250 277910197 277910221
    0x101701031b1e1a070203150601090b040e0a0c1b08121f0911120c2104030c080325211e050709180903260411060418050105030105 57
    0x10410420025989051011003c108480d4160205000d006410003642e54002800e0403003034000303441d620b554181000f50315a40b014225008203c41d003002403a240c2404c03003040042800070007500303016444403040f01c1c02521851105220b108030070416907000c41640790020650784440300d150b501940390808511080401a0340c141c20901c1001d02c003050034a000c03202c101038000002b038100000f9043c070121810007841010540f00341e510302c40440c1d0b2106080c1c65404080d10300c0281e02e043c038408900300320001c4d40042c41c000d503040d04207640948030740d070b0000f4103d240d550a101103a52aa0110000003807550482140207061741d0101c00c0c1c40d2468090741c00e0700f084609213050840c850809048040c942344050780501c1d001300780c500e0005400758442c500c9040e500452526031b80701c142c0e00d003102010305900a10170400800c2c8046101c00e0343c686600750b40c07848070001d000982040032900d500000744d501c01c4121001003480700d4076104181d24460214000380003d10032280030b03500303020005071400004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 277912697 1250 277911447 277911479
    0x11040605010807110f07060203070507060305012102041b08040c090e0a0807050312010305030a02010c02070e010e060a05030d090302040e030702010f0f0e0619020d140405101701031b 80
    0x681daa0500da64030f0382c02c225400c1601e1401074129020307980c84100c0c0490207003c0c080240655400443c0e0340c0c02c043c58128a00601503000b1420189004014002c0e40100c2c0f117070320b1002d03200146100d20081207000040c000c0c07201c1d002c00038260265810b8000191380110240e0300c030f039002c1c948004125646020310800d6a118030a4560307590032202c142c40c001a01303100a400d1060107030b0100d0342800320084104005890070380058800c5d80c001f1800c400d0055090240410340500e520203044d80398038225601031044810b0042120b548040d20010b000c0d81c80b50b500a0000b440000c08441c0b11620321103000d403103280700d0f01041c1c3c02135040c041000c44d5290000215182e2030f0f4180d403001640881048200c50805d0102012030800c02c03450144401640e418000e40006154414440c1c035a001c5618041e01c0c200c6504580014409550312a5030802c8140d000e4908403081914510245030b074a1a04030381c220b6520510b90341c401011000401800310b0121a0300c0c850344100c5a6003480d41c0c03100c00e41c45480c500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 277913947 1250 277912697 277912699
    0x609060509090d0905060d0209040e0a17040b030a090807050111030604060803190c03021c030f0605030a0218130b090303180f03090118080d020c13111e09030f01060311040605 77
    0x4407110405c01800c14078004d20b40c2c5c0d50699001400c00c20000002020f80b440e03070481070f015071b01c04880c05080c01038103181602070b1503080c0c1e0010b181c030f8545950202c6500006000701140344d50340d160407050041c800c0c00c89031201e51240081002ca204100f82603007039041582c009000342d240501c041841c480c004200d480030780b20041c04040c41070b852501212070f5038564604804600078042c000041e20719180d20a00344861684001c01c00c004410310070800c81d202e55025901c0796120354108005601d80c03040030408014004003014817542c03400e08122040b00042c6000301981a41406c0000c02c0744040b0103035028841049110f0501142c42c000c0e26503c90609000c00003980040100015541c05480310380d01d2000001360b014040f0341d44035010760404816a601d00f015800405c5130020502d400c0045007420041a482002041802224010980541580d004200c07030152580c80300754040c2c000303459902c50002c049078014503280d05614041e103010310044513281d9000c003103800e06143c0f9008031026580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 277915197 1250 277913947 277913957
    0xd06030606050621060324060906010c020d021002010e070305030c0f03040e0a0c21020c0d0908150c0729070504210213050112050705030307080316120609060509090d 73
    0x200f000301c0510034003005d421a030313161080203006913090300d0301e0711781c040031511828a8522a1400109008001c0401008030381001980a9098016902e1000c6620115015a1150307212280030000746e00602004a50b080640f0490100000b0484000010858880c0c0202982c01080004810f5a5a800385004031301903404000d000507000340c1160701091904980307160018117034028000e107031100d1681030b00030f5500d0f98000400c3c501c842d00400404886800515080345250304d0a46010f441d04441d52203649494010804100340421401c2901d81058006602212000c1200315044070040001010380c3c0707101411001512180c0038405a4084900030084c4407201d1b00000b60241e030f09102400304036481020045041503062152003460302130302c030010300d6280d10130050901501c2c022066124601c00e42c0100b024400040d000400e17280c01c610b041c1407062035400f500ca02507e0403404040b100c04480c0c0740c0140010810f0307554000d90200d800a5030000c20782d031103003889140c980307410820b014007042e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 277916447 1250 277915197 277915237
    0x614060d0204030206120115020a05030a180b0301170d02060403020a1227140904020a03020913150c03050601023c070905010e06090403091401140d060306060506 71
    0x204140008000308154104014a0b0035102d40c00606580c0050360144d100ea40804014444100302c254007145211450008083d034a00b9962181d540340304041c2c0368003c0005400600c0003011042c1100302c0540040500c403074070380d80c4030310000c24401c00907043c080541c418031041000590011801134041c98150780541101042601c409408141c0c0d17501e00303c1001007225400141c514030350b0324030b50710181c0a490702152518151406000039080f0403a070b032044000c0410b1200581d0341c4000b2808696060701d01c012a50b40d0a400403441e04403501020b043c044039010303024a0b0420303580c400311304e17080c440d00c04102980300c0d90012645c50101900f070342c06000b0541c482c003010402e1480c00440c8100400c1011140da48040d5a15041c1426a802402e1854440f0300511480e81c800641a078004826100c0115614164800800c1001e1911030104d880d41d40c00a04d500591040c05801c0e0543c40201c01240e80e0140700e80c04000800c030382e1006840152500c1030106151810a00300c40c2160202e0040004103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 277917697 1250 277916447 277916449
    0x171b01290d02130908040806100f080c1504180603020a0f0b090d0311060a1407080c18060c070303111009021507020316060f0807050a050d050606070218010609080105010506040e0403022a130614 85
    0xc560f0309061400dc40c000d000c0001e801e04080b1406000718000300c0b0200b241491441441203420321070300803021070b280b610014021030300254140c030307c0904104d52805903200701e824140e482c140c004c54404194000c010070009012803641104000c54260440481d0554070900110398020041c0c400c0d1042e80c5041000c02120800c03100e6080c0305010081089260901c014580303031030030920354000c80114103100e8800340e904c007090200382900c00c2e09090071b101041c039950009054550440c0300c044008404110380044d03450030403c1300c002d80344600f6601d90340e90311140b0181112075035480c0500007440c2e000014000c2c2c0c0c415400d03a0000002900c41c64146407000031000c003d0000105810780040341030080e0805652001500e0014400005416080c1e50508000406102d01600100710b541c1c1003200400454130b4950803241106da0b81c03220010240c4561804904086644100c80b13800300300b485e0303241e607010400c4440e0f01c0310f02001c4030007441c40441c50f0b035000c05807403841c441c9007181c0c1800b44420a003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 277918947 1250 277917697 277917709
    0x3021207030b1206011701050c090a0e0901060f030803090d0c02010207060f0c060204030809010908011401030f02011806090512010905060103171b01290d02130908040806100f080c 79
    0xc6002c00070140601000c42000c40c61812900364881e8024041760010010301d503500b84103094000341c442c1c0c2d03c103180034510004905000b80a110b00f07140b81c1c208100080c1c8030842980718034041c050841550311482c1d52810036400c650800c0d504001140946982c1003034660040071250072842c0d068018080e124a0420140c03000303000e45c0346000520a04c1410040000d10a100030809103110b949859140d8200c0400140010920f8000d410070340e140c07003c0100c24082034090300d41141e07803201140e01103c8040c401244c03c40300798402c9800da5001282c01251a039004036140059442c241c8407040460700d600c0400382620700c0b030000681503400c100010f00c00306070000c00b03613080303072402c42401c500e098a4002c00d8074100d51404880c0c50356075550347c1c03544000c41d80c442c1d0007e5644041195294105510f00002d18111840d0030000c1c4560490428056121100d070000c0c100150004007480e1500c1ea43d01604d51071380c038110762810800c4c0c42c40f04049504030307030b84008a0550b10300350010282403500b00140300f0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 277920197 1250 277918947 277918961
    0x18101e03060306050f01030b09030a020a08091309060609050a0204230f0a090509060f0403020d0305040309170114010e04150c030b0d0809040c030606140d0b0303120f01060302120703 80
    0x800c2545521011003c2107103405428000d5008401100c120b62442c1019800034802910200c444c0d0402c008000d091580000d000b801250040009940c074114000050405022a040c400c0c09504012025090000070fa001400f2a000c1807814000c0f40c2d164907200c2c08910072406500d94100900128240c00c0e0215064201c1780c000191a1250105180000802c0c00600354044007920342c50b0400c200300a2070501215821803031a82091205090503070b0080e48421545054004141d6034000041c04c0c1480b444000d03004201d440380c1c5803091035003100c03903901070322401a07400700032021080001460000701000c94840c079040030f00c13074110020012049002e003000c4100071081640711611304840da66101201310940c2d109141c000e0780e4008a5041c0b1066070342101960f01032601d000d0f41000301580000312243c103e945862129510044114400020012041e00c9078042c030020600088280b4280c2e000b0f8015210044a140c40340c1e600c4600700d05901c5450040701c18100003002042c045406608004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 277921447 1250 277920197 277920257
    0x10509100e0415030f0303060909020904110a0e090d0e2b08070b07050705190b01181103090105010f080105010308090105161401021c0608060f0711030406051810 71
    0xb194504030300340c140300d00c582a84c00c10382d848410030110034200740e01803040c40c004080b100001d00c4204034a400098050b04c0c000c0c0090700c1c03046411070103281c0740ea4400c46100501039202c5100e519090024a03e07a60301d2420b2002804621203020084880c50600c0703040d014004591001d2201d001c10030300d18501002d030100c0807103c10005000100c0010115240148240483d5495540342c66450070300c180b902c2c0c0101c000c130140a95101ca01070104c2c032030f2902207054031001e070040706040d4441c0d003401c80100341c1d00b00c034241900000700074401c4a240640019040760540b1580301da00d070b501d80300410308880d428440142015402c005190865000301c02900305444400103c0d8106006030b01c038103008502085110029950010343ca5009034a1702c001c0c410828403549041040c113061158990380c2d0703000a00303076105c40f40716000001c50b05482a031107446002c03004010389448a60b04d15002d030268004140d040c8062115840040c45411300721000040c81e02d03140c0d501000c80340300662054900501e1003440b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 277922697 1250 277921447 277921451
    0x905030c010905130e16032402120601080705091e010e01020601180903090504090f0b101809050f12030f150f0d020f0d0c03051203040819020a0b0c03090c010509100e04 74
    0x1400c1b11412250200011070260700028080d0b440704c02d0510241030600070040c03000c0d105021f1003100424150096502c068282014100360301c2d50601070302c450207844036007984a0008501011901c00c0300d150602c00620170b80703603031034411800001640c81714000d005044c000d000c10040301c80306400a8120060150007420243c1142d5160004502070b5401c0304004d0341d0b41c0b44441d10340410080841d645d00e50189120703070f00b0480b032030400c0c1b10465400703003a0b64409103150700e80d41c1c0c41c02441740034000a00181c2411040703c0c2c62800c01c043ca000c03250800c13a19860010040380008102420b0041030000c500300c01420280020020801c01402c90000c107802d0740c01461440c1410341d540c807400c003403404160082034030409a03455850014a44903042c888840214001e1080c403000072009810b55248001800400d08520402c0c401203280c08401070014261509100c01d1082c2e411403540214002c03030702d280c181c500749a0b4040c010755040c80b41d04000758002c926801c0200905206405402c82c510000b000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 277923947 1250 277922697 277922713
    0x518011404060825090b03150a030b0405060c2a01090803090a0c080d05040303120f020417010b03010605010f1218060c080703050f040b0903190905030c010905130e 72
    0x103030100381d030410703000381000c41c0040b414400c0c80070002a08035140307002101200501240c04500410641d070700e02c504a4000008000320751072a00d01070038030609180142c040a015652410100c0c81c03d03a00faa03068680c4d01070b40020a120b0480001260300c0c0203500050281910018501511000c0070135140d0b11a55690b2210f140008403503800550145202000810418505042c06205210a50700940103507010b82079200c00c15402c0740503141200d4050610003101c82d65007a481d800303460000e180c80c0f5402d200003804140720340050340c5024007071000d000802c410380715002454225611402598089000140704a0070f5a00c100c88035400800030880110302080044481c40c3d0b01d80e0b100e601194140d40f41d00c41c3c0b4102c154007244003507004006150030b00040c100a03800090020001d44040c004c0040c2c10000b48810800f0021130f00015403c015110001036100002010401345004261282c0220032010340300351300c5844100141d1380000e21034151105006021802484002c0116285006000f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 277925197 1250 277923947 277923977
    0x60f02100c020601140303120c03061918050c07020306061201180b0601110d050f1e0706050912070b13060605193209040203010f020c1e010507051801 66
    0x7451501d5030054004090a5042c158141d000c50b40750030080d07000f640203014000045484600240d00b080440d415036039603450740008244070130700768002c1c1084441320300c000044400c3c450801442000c040b0070200203a0f10343d00322402852003a098065403541c81040440ca603407615800c02c01a03600c85000000c0d465200b022440a0440718150940318900d04200300b0149581102288100e449480041d181c4500038000160050040c0c40310000c4601011038000a90340e41c001c41c10480003018591951a81d50a15004009d400201e0301ea405030300502d0781105000c10400d05407090300c0e601192800c103659613111295296150410706450494070741ca0002400d4407011041d0019400751403030303d0001d5061071070904800440b450286c00d900b17140040142210300204194514031812100e2020944407800042c0c050004620311510161000419014112000510451000303083c0c2c4035183d1084c000e81283d003250310071a07410003c2070040042050410340c46241d4440038105040002410b00620 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 277926447 1250 277925197 277925201
    0x1051524161a090304051c020a0e0f070210050603030405040e070b0307051312030c0303330305010509060402090f091f0903032406030f0b04090308041205040b0301060f0210 76
    0x303090754000ca942240350104880c0c503502c0c0e9489881c007401140352a00c1c100200f010a00e12050390002d4208005901c0d00b10f41c1e446562500809887d1028206401c062040c0d804c100006c1d500180913108906051001e0319481c000e40e072040a0042c080c0d81040d04d0300d82400090000035132000d502e0b000c3c8c03000118031000c007040a12b0107607400e9600d0644035604907903104500d00f455000709002c245e68000b4a8002071384185242e0361940e15140101307003594054000c00c10402c48101c803203d820302c41d80e812000442c01104400440c4d0007080244040c0d1590322502e071b110302003a41e000c0e401080610025049105c00c0020540150441084aa200151600c0d4243c140c500c5041058002e07200c01c130300002d0617810700a840243c40b04018040c2e40c41c400c140441541c401da84100742c14951602c0410305110002e03032200c000303408040c200388500503d03131170001c142000460f01154103201001020010611800c252020f031828844007070310356400d01c042a2403450000354004c00f1845459114021840c0078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 277927697 1250 277926447 277926487
    0x3030e060c1603060b01170c04141f021c05120705070314131503020a080619050607060501061803171606020c0a0c120b13020120030c01051524 63
    0x200d000240c085c1300c0c0c03000148180c202d032448003c403410b20000d00103219441c80460b001c5880500c80ba10010140401156801034000c0401300c000208240020603550042104005a50307c60303901d1520030f8241c40c1c00d44032070007011036856410982c0c0c00000d42c0d050141c0c00400c0b009006e41030065040403d8603452186a0041000c0900c40c0003001d07040220b00c10160201c160030f980d41c1029418118403110003440c0d08002415148203494994015101da1811001031002d41400740101d9501c0c0424100140902002c1c8100300019a0101040700540360100345a016a540400c034500180850f0480484640140e8150450002d0000f0f41c0000030340c5500c01442406080005000180c103181001036140c0b00650101c071701e04d008140c4070000544984a81070380689803110314421608a8001201d200b190201141450b84200031500c050398000000742030540030b1000240001e9590783c091920400c0102c0260ba049202149079079160201c4a02001c00c02c0c00c5604111704002c04804a40c40030088 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 277928947 1250 277927697 277927703
    0x2070b041719051e04080c041e0603030201090b0a150306110405090403020a02010206100f0b16050f030304112e0e0a0609050a0f12030518031506100903030e060c1603 73
    0xc005440c000c000f1449601e0408241d820316060305040c5084c4e2915202d480e8031701140e100f1503460716107003014140344100d1889c600fa02481001641d0312881e02078000d004541c010384001c402d110008400b1802030017501108900d60140e03483c81861540d402c005446240ac40c4404c0c00002e00000c285601c450f40000d01c43d07030203031b4010032890119000190904001614541c03809021020500184048004e003400b114240c20f041d6689040f940240703403a4294543c80140107015162400368800390000c003842c05035008403240c042e0301000e402003008000c0841c10390040c40c405542c0d1503d20240e035021610702c6511034184070422002a00018052000b940c1180380820a103c800b80006d0814584c0007000d00012210850388504001101c1240107403003500404200c0c00040400d40550714000b061000c20010f0122008540c54182607400400202d6096004100500350381e50910302c03a42d003000441350192681f440780010a02480f440e40d01092202109103c3e070744445840403101c8074650010340c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 277930197 1250 277928947 277928957
    0x80d050703030f051b070203030408010c0c0c0e0f040305030a140103030201051014030709050c13140112090c091112010905090105060307031106070303090f0b01050906030102070b041719 82
    0x11640c038019045581e00f1180d1801c8503d0721080002d45246600d81100800741d0005598981103a440004d01d544615002640715508150301e407041c0316002180612443c0c8142488004252642080a05104c2c111a42841c811a5101280100380550021038100000d0340c00070072641e140d07100c000c1a14800f03900440040c2c0d5618104440e10030301540c02c001410100030007003200801e940c0080d9903140070340141d01c42c1c0e540d0742002c62081d1070703d00111450b054010400721081543c0f5441405024100b6800502040c0b10744081c4018115078411004030542c00f480c2040c1c0903081007a04001010017002d0300c04031903800c214440c82d604079489000c0c000c020105020400c0d01d801405182581c4010300310307a00031392040c0800d100003000300440f2820840180e648a8803250b043c14200d01038a8012006400e20381900c1c2000240720001441d03d05039a0103907040541070319020203140c200e02c00e22070080c00e40540e2501041c000f60643c2c2201c840404282d808504180070405500000b4590a281c034001c00c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 277931447 1250 277930197 277930207
    0x50f04050d140105012c071806020d020d05090d0b220c03051203060105031b041a0a02070512100504172a030403030912060f05101d040203070e0709080d05 68
    0x18024000c0e075015040d41d60280d00501e009a15032810111070f04a080300b41d507482000070342000d20410880c0110440d01d20f03990023803562030401a464070710303000d40c050060203441d400c3c2803544e001340e080f240130000240c410825a0f501c0d464100c03021300e0103000b5600d052803101c8000e168100c4925110480381c003811581c1e0101c4c0c914600b09241c42c440c4558401035000a00401c1504e81e006000c2e03941c0804904000607000030300040f11412881150406d154001300c071840c140d0f603010140d01401b0140030f207808603881c050b01c075020030110300c45e080d804410303c4c0d20613801c900c41aa1aa0040368210313104480341c040c1c40c7c040c07044003502d64000e00b200240e1440e44805104404081643c400c60b43c44145c1c02951230141180c80007403d200f100d018038408035465800400400a00303600c5041c2c05c0329800c00420041c208503040d0401130801c1c0c803803d051140401040340440340d2092549005550060050581c18074080c0244a0742400401c541c0600a050000080d152018070181d110800641c0d151980c032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 277932697 1250 277931447 277931483
    0x142413031e03060e060f060909040303061d04030e010309121421060315070e0f031606030e10140f18030c030316300603080c0604050d05160201050f04050d 68
    0x2044009085c503104e11010315010f0481d4030342008443e4004030a880b160450f68407410b00ba405064243c2c0311072034410302c28010003225555003007064000c903c0795a0340e48001c00c00400440030340d005040c0161021327030000020705616000d0000300d55204070031b0b501217003003041e1411414180704525108006104019080101510301403210180c007803d0728401202c81d0038106d100901d810301000c0840e0007600c4070003000c01c41c0d980c1000403102420b00400704840e0181c03215001400b42920036240e65862144440890001c804c80c054940c84440c06d03285032141c0d0381c40ea6402101d00c0b801800c0701c0c9481c1c0c00d0a112402d00d4500340020448034013102c0c01036507070381810702064030303c4000d4101c1a000c1102e030105079424090000d07441040291032681c030902e090f003000d548070001c1105610080c440c0b400007070101c04d22540828103a10070380c081d10660b1200d500e501000c0d6140c0c130410307440c21210740b400d09034100158018806444541e80c4026201c0c105070f202d0010465502168205442d610b151030028001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 277933947 1250 277932697 277932719
    0x2309010c0e01020a031e0c0203060a06060206070e06190504050a03080418061d040201020313030f05070e0f0a090303060b07031d040605130e100603142413031e0306 72
    0x90700100307100800000704140c80040840f40c104200040c50b0050300303001e041d40c1e4858440000802d40041c16107001c0c0c181a0f21550080089100d1513016000b16000612898000c148206420f00045e240c2ca1078900c201e1401005072408098420501405000116640d200c8000e03c0000c2c503c150265030340e440c01c090b0401858912001040e002c03909101c010b00021060b15041c03c85510102c01d0f81c0166112440180c6c01d40c0103800c44c1c191280c140722000024404640f0f00759404601903015110180c0e100c111300c5a0b403100440c2d020807500360361004940500680c0c0d1010034224001d190000b400c2c0d4903429103044540c8802010b50008024451103070744466210003450340d13103108403000c04c48039150502107060340c40070801500009940c1c0c0402c10100405000540c0c0400c1280c4042026503102d1800b00c00401910500c2c3ea054802c0c0fa51005180110041440070701605103044221a90307448034802d400b1700c0d103a4048041000c1944c480c040000d1041a0344070038807070380c1c401080319420300104c920 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 277935197 1250 277933947 277933967
    0x24040f0f1407051c03030c020c04110904061401020304331116270f0c081e040c05060d020c070b1b01050402061b070b0313020f0f0a092309010c 63
    0x2100c0c140b0300f613107001800320515816200c3c1e641424081603e81c40341005a090804003400d003a000b9040443c207814a541c000e000700006001140c0410045031503500b8049180030048985007d83c2c402c02c020720481d03032040a2541043c41c440118849a0512080003a1080b140c07061840812000b40d420a00500c080c46040c400f40690046580d00500e824010365404055645020301d85c4000c280745126125a5000710800c2a200c400c00d0102ea25a21002459040c040300d00d407080b60b01181c01c040441807482c06107805140c21152202815040204100966001241142001d40e0030040140002030500520004015041c0c15540703840022450f00c0381d47d24003030b00740b80c446d034234100822006990707142c00d0340e50300c041505031054100d50f40b0000307916081c5c03da00000c4040c1000300800c078070302d15008200e0000e1442070f100c1c9800d48141c0b20074080c020b07001000c190303403000c2110401e1191402a911980b9000b9800c40142e43d040b007080340580501d1419910300210340d448081121100c0c1c0c10180041c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 277936447 1250 277935197 277935199
    0x305030a0e06060315090c19030c0f180f0b040c110d0c0c0b181203030a0b040e031c021b0606040e0c010503010605280314060324040f0f140705 63
    0x2c41145400000251120600c0c0407910301017101d800800c0c00202e080019285401018180700d01c04000704a8480c030b1901d40340f004039107151240a0204008000301021021100d50791515130139149000d444d440648500340469130306696038103503407042d0b40d41c501400303400c8401600d5000440781d10400040c100303000f407031401050007818002c140c000703072283c2c0c0f94008862408a8032500c60a400708448492081080c2c0c2a9118007038a8440452410110046000e046030741030030868401c8003400e01c002d442480001500d103802c00d10455660300c44d040000c440078103128000525100231100d2070040d00301c17100e0040650307500c44420000a4146803095003030341c40480c00100300c0e01e17080200003021880140600810400e002c10140903220005111480340c9071210030868201140340b5000700288a420601d5840281d090003043c25403c02042e210700c00c0307120003a100703407580308441e00442c6050064001c94910030281d480300c010555102d400018070b4032072040303c03070083c000940442c40e2130401e030802 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 277937697 1250 277936447 277936453
    0xd0f060504060e0d0c0f02030304030803010e010e0108071d060f0306070f0215062407060c050c1c0504060c0f05071d0711060712020c0d0e040f05040812220305030a0e 73
    0x100401a00407417100b0010b80e0080540341400b14502c0032034118042d0ba8401428400040000702d00105100a40c90584178010340b0518a6a80c51a0041c0d940006100d1001d640d25100546c044d43d02c40300182c540d0203000a00150200211240480d103482411142000003482602d2940c60039035050150328000703c0c44e424031140504000000422180c0b0000143c0c21917220340e801408228020400d0398032080d04101d040080b030141000281c820307071010011103d0360040184040390200000f14010b28400c269036560708180c1071440075164034098500690f070401c151101d0000040d82045054094091400c8451040010558400300b110300036040308240300b020503600b401c0b50700c00074040e580500d051401d1520071100880b810024410483c101655000f403501021990350404a2420500d0040d2810481550070240e8001166403c0d940144005820010f68034400b08000e1956088440e1002d40710b41080040d61203184003008141c110041036003c4108103a17551107201d074402d480411009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 277938947 1250 277937697 277937713
    0x1b030c0f1d010c020310050f010f0b03040302150702010f061d09030a0f0c02040920100f0c0f020a1e03020a12020f0427080d0b040903050d0b0d0f060504060e 69
    0x101c20410410305408904000b03082d2034a00a5507020003003541400564403040001e42020111103c0c040c20902841c0030820f4581400580001003800320303442140c050340507006030581c25080ca0144200a05030904642d2603022a0080c041c89200f080001c1540000c00000c200b241030322040710207001850645603820a0040300f2106d6000403081d0005000340c582a00d8000903440050010411003c01800c22a920580031912440c80b0504080c8410200d0302c0d03508480501004443d02810444210009003a40e0702c0c040020303c50600c0341200ea48001c040d80c080e140c945c0c0805491041c0300700200b410030103640d000c2094ac2440c440c40d0001d092025201c070001038032500480e0505129901d818011303643d0300284400c0c8002e074240c105a4001c43d031106003100110f170806c01c4482d0048400f860300300b40703003c130515007928161284c4140309506454890030800841b894a004040a90604c0d402003821140000000c20780303070702000d10510401c00010b00d4102420b22800300d40304090342906a80c09030107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 277940197 1250 277938947 277938977
    0x30606050a0311040e010605030601030e070602070b031314031312020105070816060606020a020310140105010518090103080429090402090a0512030c0d020c010c030e0102011b030c0f 80
    0x444600032414280851048501d025803043c5100e01d52043c0102c82c80217002081d2190b01000441c012102641c05000c15140709480f6501e0301814412640940d211100400c8203503800c1018550107000360403801744018181d100c030490f409400301c1540d100c3e040050305284d414040c3c020702028005032500f44420940036800a01035208022003d012000042407009000e00c03101000c40125a10000a00003556200406913580c1d900c3e1504034403900988218101c1d02c002d0744180340403408154085081d69207440015034869000f007540c01da81050301d9034000701d01d4440c141c90900a501c92052199074524045500341d00e01c0401d82590030b030001c441d034480c0c001a080410b460b1710b690704aa006a40700036000c0050981103840d400107070058519401d004804401002030302c040c641c0303401030702c0c14981100412a100c4aa44040c940401c203800340f0500424030401080042c00c606000000758101c450380c071600fa0964124030345000944868140d01519444184c030842c45c0390038100804001500b00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 277941447 1250 277940197 277940207
    0x40b090f0c0409150e0105180a0c0308091201150303090e070c1103010906050406060312110604060902040e0303132307031209030812010510080f040308061906031b030606 75
    0x1c0d22941c0b01d01d480e05000340a202c2840b03405410030142d00b00810180c2031064a1078082c1008440801a00440c1031b0020440c0304081005110107030700c44150a46117003550748181583c6c0100311140d4001840b180303011840042481499205001405040d0207103181d403600411b00002602300ca2444203440080c070400d150400c0c4203010165004000000017500e240129005000c0018064030f128180810300091010036841801900d020340c80b00341480c1c01100d0141c441c04001d10b1141e0182d44207030b0014001c141c26520444101713100500215032000340861807451034105440e0044400400382003101007008001c8008603090a91000005003260742011980300c0b501da102c05040012280018000144aa00154040c43c1c1c04060a603c0311107a01254100501c2402100d00a9002d0003801c1c81c2d05004045051044013000c0700c6400d5555a07580c01c07202c184019012503000080d0400890881040284080c060304266400060421601c2000c9158112400c004800c1c146401400c1c84415400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 277942697 1250 277941447 277941463
    0x17040e0108011b08370b030c030c0a0902030c1e090f0f060a0c050c09041b0902090918010605062113050715180303120c030b1f02010f02070b040b090f 66
    0x1540f045c80310b040034a41e080040e0b08640d080f402d4a206040d01003d800305640e111000f00304098003101c4a11041d8000d05650346d0004807001e500c40540c482c03c000000c1540c00039544480a007082c1410059801040f90100c0e00c0400742005526006c10350a01c0c5041c0b044c5601d100303900488038486240f8112010900920440b00b400c410054011301041c00d020080005c1403140f20041c188020034034190401100d480b801d15420945501d0003140091907060f24000c0d25203040000340143c41e1900c4801d46502410302d0703090401d10325522b82c0d03000503d5654a80141a030101600341e4902503c801c03091000300c02030000c0c16071082e80c42515007034005c81d00014681381590441a01807290b0005004203480c40105140141d5244042c1e501c080f08041d40501c405d0800042e0341c8080c01100d82a0b6410b405070f5135824260381e000b03416000c0c1514a403501c40d1008002500900001035041c50080d8903006a07407114006503100300e000e1007071004201036640103e500c041c1003006441d07100850b110454031405a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 277943947 1250 277942697 277942711
    0x151d03010c0516060b0306152e21090b0a0c0503013503030a0903080112020f040b1306030503041a13140109180b0906060903120717040e0108011b08 65
    0x502a14082000304a6110034030b15600141200ca03140f4180c510702080088004281c9d0060f03019000040c05501081401810240780d0071800f2130b0049250b0048812841140ea445200e0721000780990070024180b080200c054000e250f0121640780140e4242c0030744814078000c00400200300010020492402000c03030084620a0800030185a41020341020541c2100203108500000061120150701c590204a28030b21940354500c4507030380c80a0380c040d0211b220348040e400a43d880b40c3c800c2c0078134255102c20b04180b00244001d6408000d88450005c94400360012100b0798000072742409009298068a404014558823175442e140c2081d1040b4503911003841f071052000c43d40400000d0507801100e00e00b02404448110503905400b41d481800074003580460300d4040c00c0500041516814000c040300d603800c8000c0c00401001c02210445110b070740c800349069407540d086000f10720302e01100381c0c001c3c0010300c110f00c040e42d4254103001c40542107405030324000030500d00704481140d1590700001c0742588041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 277945197 1250 277943947 277943977
    0xb0a020c01020c0601061106010e0403020606011202040b070606030b010e040309031103030f030c0a083603070203030c0a03031103040b060d0318060306030302070e09031b0304151d03010c05 83
    0x204030081240a40681507103105503000300000030030100d505c02d05a0380e800e885501154656666401400200c0d1401e035030280058000000141443d40200744c55113100c41101001450b1940e6103200a003c1e8210070801c0360440d0305c50b00c040081c800e00c8000c5034098000d40c00c0780407003410507541c050040d4095101c001c201c0e202c1071100000642d01842902c0b4842c0d03012029982e01e107004d550102d043c4e401000e040c00821410000310300701c05508080c0201408607000411048401c601c0611803894200300494007520040140c0c0006071001d0000d0700b81c0015000042c21010164500035041e40d50302da030131407400641030040001003519a800336400502c2038402140113079050078126089004103a031400104580c0e500092060341c5640b222044a0107039090b0743c810f41c0c03036400c03040d0344d00000c3c0d864001c0e0780d00600000a40e03000201c0e10803460100c1d40f04aa142954031000401c040310900798000100c7e004000b08203011201c5d040004203448201c008012000c103845014040b030080b02e09403080c0603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 277946447 1250 277945197 277945207
    0x103140703080304030305010512010b03031b12040603060602060a0c050d020f09090408250206030103020f1c060209090723090a0803031305011b02060105060702040609050f070f05070b0a02 83
    0x18809002a80c081c41d0042c25072650381c82c080c10050701404007071140300c0c0100000c0051500c4458188a11172210800401940ca804060164100542c0200c18001514040d0100c8503405941c0c0034001c1008000e16140440c0881c5840d1001c0e041c200b00400100507035040544d8207014681c0701d03048540900b4070810058503805a1f820a40d4580250342d440c0741c0206501080c0010320070290007601c80c62004c43c41d405105080b5100034599009180b10007508290140014401458070340b0140e4400e00001c7d00e0a40c200c4113507180c003051a0451882500e92541c00203202e0150700340207001660280f400e0074980b22038041c109080b0404d0703420320a44002144041107030021943c40c81d20358001440c60100700c90b12420b080880404600c0710007000c440540c40c1402551505400d902070042c4a03401e81c02410b2260319010074089031394090007040781e2081d550107000c203090007280b1881e401000170b410b800c155445c004402034440b06074502070f10107020043c0030410000e0b02d0704112940c41550300c08056120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 277947697 1250 277946447 277946483
    0x1050414210f030a06081020070c14181003050d2105070203090a03080c2e0228110c060f04120503130305061b0a0518010e122b080103 59
    0x1044250044540d03030003940600f0200f1f401a0300306100240786032901501c000690b100d09001c40c45280801040c0c0c0c4144401082504140e114001968502410180c00c0f5040380ca6601545107040b00c00a40c16034100c1c60910034032108102000c1d05c50014280b07c154050641b14612912034a01c89210009844a0004030858801d20039620016000380c2100181a26498511103681040340304003032a11851001d00001d8056080483c030b0381801180c1402c1c60300c0003109000103540104081141c200b03201c84e180308000b803454a0300148103201d9031107030404040c4000c03103030604056802c503a10400d001c2c44001d1880408070300301c40440d9030b048400d1503254800d2400340d04600400700408403540d042c90300001800320100f0300070300c41d4008500c1c8074000064051201e1041c0150480c403000a40141f040440c40901c03151520803800c0e050502c06500110302c1c001500009080118540781d4218015104100c0c0c541124002c03800d21150348001c9011380702c10001d03c4020144005402590301c00d441c0002c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 277948947 1250 277947697 277947701
    0x90204060305030c01060611030405010f1119080315010f0503180a02060d2c0604020f0103140108100b0102070503150c040e07050301030c17150a02040801050414210f030a 75
    0x2107510900f038980313580e003200e100c41c02089248580d0010880000c6003110301e610100880d0140d070070507118861484500802158000d01e019201405441040000100141c001c075a41c0d000b0391054008590fa440c02c076400c0c8a034646124200d40c1881102050103504d03980120503294010485046c45074407544807840c2074038003201b4480181d00100c0000c0d0340100c00040f0380080c1c075117016541d000e1180ca2400c1c100f9024203000841304815580103080410010305d420301e5188c0070300105141c00b080460702800150005e020a0f407000b401940b088000044550f018022024140001d00182c03020619000201c0d4650707001003040d0b0451005080000d09100c010310a540c045c100045070400a031400000241c0550f20a0100b036076001172511001958400c034880c0200c20410f0f40024040d0411680180ca12041024040016482e024400496000300c01d1088911480c020700900e14514004038615041000502a01e90101c808082801e61800d110044030340741c00101041a99a035590405440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 277950197 1250 277948947 277948949
    0x41103030409090804030317040305040b0d0b1306061b0b04060f0e060702240103030e190504021305040b0d05060c0901020a020405070f0206070201020313150902041404050d0206010b070609020406 86
    0x14950703e000e10100030f1042c2e0710054020f90740710351290a80b030009004400050041160000d0010f0010042403102900c00406010304035950000840c542c85d401c000110b420300516003030034009503902070820200d40d01100311144a03088009540040085403a031031404800140701901107a11010a10030701003141d400300d400310f0850700a455081c10042e4000b501c81400c03010090b40e13a1200d680510850080c81c2c000750407603600da128000407080344c80500628148403080401560b8901c01d0010313140e1201c1c0001d1000064181e06040e00900744420072084501003c8002d010f255518030010005100107002a00b200d0021000c90f02c42e81d04500407468903001c942c0081d00036040000b404102a0815082c1580351256000d40e9015650040100d0803404129070380b80c0130300328801181c0003003443c010030010507944280340450b9940142e00070505031645000300c40103a01c3c9081c100011301c03509001440080b8928805404554580705d0018624040c0c1400a0704455851a00e03a046680381e0744040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 277951447 1250 277950197 277950209
    0xa061505031b070f0506070807080f07020a050318010306080f12132102010e101e02010f0e0303100b07030e12030d140619050904030507080f1812010c080411030304 72
    0x243c0d0350182480c004041040d8034404403003d100388030124024900640c0744038410011551400000d0741c07462402c598880000e0300040650003103400d01400300d4010300041070718880300f40a01040c041204001401c84030305902c80304854100c8124132407005004580e40070300e1922040e03601d403200313015200441010281d80c8100d480a0702090040e84a444802c0b068011600076210030f54001d03884414402c4c1102091010740018058170340f00d00810302001d00c80102c5030640d200014480e90011008030807a038140180742a03a610100c01c02c100c0013590382044001d485412501810000165006031900e06030244591052502c611501226001002a190703034080c240828091500d280200d0b50327030743d0350548403940510304a01621004030f030010007000466002a010910b15591902e04a6180d0040d6034102c07014041042813074840c98985000c0c04004805403000350004020390704201c4200403d00d05405664101002d00d000c141e001040d40e948075400c0064500f68141e03a100003406c5111342c1c1c00c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 277952697 1250 277951447 277951501
    0x8071101090308070314090709110c060f180a0503090405041713060e0307031e020103180834201914090405100e0114040b07080a06150503 61
    0x1c50a00d9801209113001e11441d413820490300d1102c01405240840890308404070354045001001965800e070301c060722401080140320b0820740110b98807410b03e407080c0c2d1440c101032003680c14890300d400c08118410408080c80c00074030070804281d64154803800343e110820310465031303240010b0511444404242030603070b0403591555035100c0c50b420382032841000d0054000044440030a00c4160030000780c000240d81d081711030403410010b00c5170002030300c6d0301091040307040588549d03004503900195010110514841c09213a80c44041140518980c500d4400400c0915012244111202944083d42c9131960342c00584140050480c0c21031014810f003103e41454004106a01d00d41c2d603905c0003110320003a0b4111580c0d040603a27000f502044640202a00c002d07080e40c0000071190011802a4000500c03180300800100c1d02c10b12503100c0e5025158221020b0300c200903100100954203502c034114941c454001d407420809a03050207106581226004402d100388400000440c20140007001c2c40b003804081c9031a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 277953947 1250 277952697 277952711
    0x904031d0a06020102031b0a0c02040b06090904121e0c02090a150b07050f010207020306181501060c05100603080306060715090f05060f010b0f09040b090705091002031908071101 78
    0x2c024005e6104490a0307070412070180c020b6902c0c1d52208121106542559601540248180c0811000302842520540d010504200315441078980c3c00c2442d02c601c0c05030b01220710104003d50007030038801c12440c5040d03d0b019608041601107070003085044107960107039526030707041d038071100d444004081d80c010000c8045c9a0b100c000a00295a200030f0030954407640c26507480c85415041d190903401603c800941c507400103400540808803c0c008920403002e0081201c5540c40c211200359010002a001600011610360111050210030000b08040a00300401004100d186880710115400042d100b5403207081c0015070001031010004d90001c520050340003c018120071490b0801407903042c20710441c3c01740a4140020b000030b80000445040701c9170851740314649601c1642100084d032007004e92940c0560b540e0802115500c0f00005030b842030145440e082d03611008481003141000f2160403040456004000110742581410f12100710030000c2d0030728402c55200c03001c0540e4468032071044905e0962800075 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 277955197 1250 277953947 277953959
    0x4080a0b15040e010516090b090103200c010f0b0f0307061404170c0312120109200a030b031006080c0607030e1807031d0a0f02190306051806060904031d0a 68
    0x5c40039000b00740c007000ca01d603013411005041e01c170080548034004007a40180510449940680c0040c14031903007481d041c2020821400c110700e40b07504112040780990b951b400c4001001a06442260005001102c041c1d4103514460006607030303041280640c404109040d4001c925500300d913020344015100b60740301041a41c500d1821199600801c511940c42886501c0807285072120700303021520798080c0c17840040e103140c0c00c24201402070001c0354901c0707c18900490210066107503a0b809404018a9560003094405041082500e0043c4040880b000740f85400307403c1015031000521400c0341035059600035101d506905040d50a1290b01341215048541c501030702c4460255000c84501c00c4089480070042c04125100340b4144001440c0022110707401002403102196844128400840c401001d1840840310841d0810340301c16254800c45001e5207600c1071040e0480010300341c260962040c0b0080ca024940300c4001040ca40c409000942403001c02c0d0b4001c0360280754500c40080790b0030050203001c0030750740d1a9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 277956447 1250 277955197 277955201
    0x10f0b0c0d0c0819030222080a0305031902040905040507060305090a150f06080a1e0b0c0309070503010218120604170d231e040507090e01090203070f06020d0504080a0b15040e01 78
    0xd020341d1f18000c581040c6640000e1581e100c10307030b0101001002180003650702a0340036440585110601007002892030011541070004101501a050021819007068908545001e034990402e2080c107081c102040504100010704030401508508166040c1404800d000001c1c503401443e0841103003004808210301381c000a450840c14400c006c8040750080c040510411620380d83d400805000c1d2000100303078000c0b03100001d10b402054120070380e5040b41e5a400060708907444108071007120700c0d0010003072025141420b0800c4690341e900700646400d01d401e87d5000c1182c5000c80b60700e0f443d5000032401100c48035403035002d00c6103011015000041001296000d60b1070350411209104003140b0401c101d5000522000781500450b4800e005207800e1381080380380360203841c0380e44204060350340e00e40a540240ea000c001c200d0003051074910301e00c000c500f0000c00906003003091002030300388072081208000308940007031070440140d0000301800f42610391110308054106030300049a0b0242c18001c1da4080190f040d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 277957697 1250 277956447 277956457
    0x30312010302012705040f02090d0c180e060601030c020f0105070e12190209060d0b2502031615090803180c040b0108060d030c020a0806010f0b0c0d0c08190302 70
    0x1d03214203111004000d4201c03005108213039205101c9442d41010025824030ba000701040e684110b002504200b0800c000c541c203003444840960b048140201e0030040300100c401b41840c66130354000f040c40410000030720b89030f903464050710490405980d01c20380d04980b03100380a9040c004404400920060074000c0005003c10346101e500c80c415140d103110112583c8000440180400c00d00d0743c101d401d0503094007004007244009240c0c1c3d810041d4081e560b800292030201841c81100341001640c810010328480000f1000300010f0b11096600801100c13402103038140080e48070307680c400ca040d800d8080030b10485019204607800103007540404414081c2e004441c2c0e40001511540108880d46580035404000075900c071310036594041014a000b02e003c0d42003020222078128000d00b4110880240c5070f001c1180031405034009600c43e002400144030040039540c2100c014070040c07142501b0304030000d02c0142c490761000076104c180558426800d040081f0300050b118010f8245414440c0c203a49908060007035842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 277958947 1250 277957697 277957699
    0x803090a051603020d0f0203010f0c180e04050a0f0303110c011a0307050d060e070e1003030e010e06030705181c03030f0e12070501020d051014120607050f0702030312010302 76
    0x6003030781c000110382c0b0a1441c0c0100ca40003803400340c0740d403040c4d1626040300c41d0010050b0b800d95282c1c04048030501c0ca9000b80c02e440080741e901d600d08000031840350308860344c03190011002072404000344000310f100064802e03002c2d03402c05502481341c0364929060300140110003e40c098102d000c0f0302200c9052040d440b020000d040003101001c460840300070140c9804e00750140c07507031081c80444200042601603000494803a8004111490f45480305c48010035884129035410700c00f10500000d02c00c02d54801c00368406140d00782000900501c0500000e016408000d191804012010030300301025400001d465918242c00f9184c0c45442558501c0c80d070801c5035088081d0003190408003c040101003a1103050441c00c80040900590714600d903007600e0030385c0028402d5402d590284078440305880d2a100300e0340960401d484180b0303a50f2030000001080382803002039034840d0841e00c0188641c4080428016849005031410654414141d940d5105a0260f100065098031012a80601404203180494180c0780 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 277960197 1250 277958947 277958953
    0xa050403061a180f160302040302040203010b091c0f0b0403021e06090c060412120c060513020f01020d02070603050912071b120512030601050706020304060b1e030c060c01090803090a05 81
    0x1980700e00f454240050b07840315620352014000650140703203019400c03040700e030601d409403816540e07400060580c1c20130307007042403000000179a103038907032a000740c140e1056441c42d4a400b8550865072182d400c050309200d800303080300321001b001408040c42404105001e06028842c905884040d00121342e0350b0004890030245441400b074a00400d144c1981640c00311454852030581824440e61070041f031f0501c014685040c00f40d010354680006030315004051007041242200b545110700741c0100800e03d6400180c4c1e80c15074000b18015043c082c0d020074040180c0d0094140400c140c1c031064080d500d007070b04824907031180c0324007ca806001c001d0035000c50901041c0c024100c0100c030f501e031501c0504c2810038507402082d5074003441350f40144d4208040a141c3c400c0d070505010741028110389916040c7d0340215411a09690398042655040c9420041c1c000048421100307200c44080d01c00100c3d960300fa6941c842481140c0c0030920030841c041c04d4211403900e0364081c6261f620780c01c0c071b12103041c0d40d801640c000712a540 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 277961447 1250 277960197 277960219
    0x10c022d1903020306060607060216061e0b1c08090409080306210607110313061718030715020d1b14070b0705030702011b1808060603120a050403061a 66
    0x15144a016400b075a4008003d880b66480c0d4004000e807d91005c3c5040b502a0780900c44104802d1001070104241809100702141c1580c440752031001d1100740541c0012000c1c60201c1d284d030a61145200d14414070074050170000380351141e050040d4240900f070101035105003008541030401480101640c0644800e80e84800141c00d0051000401e81820800340655407040340002d605600c91140300466510340404d403880e201391500300920712030b001d0f0406004680c0e407100114005c880c2c80106a4003514180185144850845403541c69110380c0304007404218016a207041e0081c000d504441d0440d0f01160100180c51503050008140100e444018000c03d0100758403800012001341103409090388414040040e6440b4002036503076810140c580c100315984c81c4861980b00c40800b80c030703982000d12b64440010078650003024503501030683c0c1113000290041c40070304c90035803400141101b5140b030201446803168513031001225240920b034000b0300480c0c02c1c02081d80803c15032403140b4800c6041940d05074454 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 277962697 1250 277961447 277961479
    0x618051003030827030a0305150a03110f012109050609060907090e1606031a0604080303040336090b0409050c1c061b020f0604080405010c022d 63
    0x254450320000d0045914400060740750141c000000752001001d10007080c04c0c00a40000d1841e641101000c2c00200c0c0d514000d01911003e88002c4000c402d00807540e8031211820341c1c2d10002c08040007070b50140100f000f502901c504c2c1c0e00940c00000505c1e20040701d10002103005080b080601541c2e5016650341c0a8200482c41c1040301081c024443e0a44400820080d45007403060001440350900c0e41d45207028901030101005094490403004141d41d0b500030590111480a56147c11041007406100740400c0008100c140b101000307032a40075805040c10901610000c8520f0f042d5001d00107100c40102040840ca0040c242d42c0d00e0074000d580f45a4001c200041c0e4800c1480100d80c0088406003803035000300c00407003083c5403450b1820314103104401c110f074011103195507810980700c0c8841d6410482107007600590b20b07160b0401030031101c14078000040055080c01d40f10482240f0450061a0411003201039603015034880350240f450f20080211040c405620208011000c2982d6100440c072900180b102d0f1066 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 277963947 1250 277962697 277962721
    0x1060f06080f040b0705040e040b10050f0a0e07090b04030302010609050f15220e210a080f100b0301090c12021c18050607090807091b0302090112061805 67
    0x410b0a05411142980d01c0e0703910b840a01803002011141000410030000c03403101001b13035030b42c1d00032403203282105900d0030b112080e0b84510141d0781050707003c0c072404070030200542e0360326a04e10100c0300c1c95401c0da881d5484030f40c0f04403504010f0342c1056101140020300081019415030119080300e4140d40b0807c00c1da00c42e800c07203040000058820b1344915403813181d01c01c02481c00080d02c03075a0350001c04449002c40b4040c0ca45000352000030500c0510341e00104105000003015404125840c0360f100c80d0140752641c00000a4400203011704882d941c0c6000c40700280d015032016120b030300600b22840a0a03103d40e515142e40c0082c096181c41500015400258040d080d0054001d5500c2c2002600c0ea0001e82c4101c00ca081d0f004049806101d0381e4004400c00440104109000a5015010542c0c80d850b0a60030180700c61714007400755100f040d54515040444040480b21003150360120250f01d005030380e422440340122074100071322101944d581e181c100e0020718600414070001c3e980e1140c1c54248400d54a043e15406 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 277965197 1250 277963947 277963951
    0x40203010b090105180a0f0518310203060412111218010e10030504021906092d14041d0c010806060f0c010c0914010c15060b03040501060f0608 63
    0x1c105106100058480d8003410161800019258a030b4000b01c19020000c1c510a500364040d0385007000d9090b0502035820044402c1c5c01c41d50740015110b1140c00c0c04082582160f01860102060030507000d01350b14881c0c0d4102d801460746400508a50b494103150400a41c074081c1680b10b800410549684426805008038490007540b04101c00582001c03802c0010304403545100080d1410002640003070b0019565000c0030703110300c5045590018140c41c041c4180464100c1450030303186081e280749001c0003c140d101109005944d2404698020b503c3c80080d20394010341510600540601a0f100110b0501506120344614001c111018030415503100c10460650300010f04110b541c2c0c0007144c02d92055401540140d0b08424060702c11f91030b040301004541707507c0c0c000c14480d4a080c3d440d011201032540e407110f1250094441d160042104028600001c2e00b02013503a20010441e00c889a04aa0020303950b43c00b03a8014080310303007025900d01e0203251150083c0124000c0c1d0300180c40c0c1c0760005c0740207445640558 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 277966447 1250 277965197 277965209
    0x50a05030d080c09040603020d060c030c170a1a030118111206060d1a07020a0606090b06031501050408010c0905030f0102090102030414030a0f0615051005220e010e09060604020301 79
    0x42c4291110a01d54020354010801c0a4010b91520400001a2034500c120300002d07029140001c1e0391010020000c060381c004100b003204210340c03401350700341c25091b074501c054000174002000030341990807642020031541c024142c180e055207002028099002000c4030145880d1003140f003103081c94000001c002154020304000c00c11b645c080c9000a401c0e0904600e8080072901032003030703240c90103a04c0c290340355120021210b81005800c101000301c1085158003908002d00a2441d00340074242c000341c00309802d4040104100d411801e04294844164090001c540140000324004d00443d80e03035410107003c0103240c0c403501c2d0080c41000d501240c0200180300b50740d2100760503809949003d02d40645600c6503401d21000561602171400841c2c009039038102030115940c460300d8081122000c0c0c00000c0214000c55104034022483d889041c40042d503c0012594804500d07495142d0749061404224a0300750039422680090880c031002040200490320918401c0311a0811074940c3c1d0f641e2018802030b07001c20720402c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 277967697 1250 277966447 277966457
    0x10902030609120405150705010227010c02060306010305060f15180a0e010b070305040e0f0105180c041707120303020903070611030f0703120504080c070f0e01050603040c1e050a05030d 81
    0x511162810f21194286c4c2c0b0755142180381420314545034a402ca034060300c10b41c1140342da0444506c041042002c40c201b50369109080c4143d180c1c450f41c02042207444000c08560400d0b640701c000a159036101c0c980c01c448c0c2d01000e001c00d2016441c101da05012a4442d001c0e480001c0044c1d512003510b032520326403000940300d0081c1d11840c5a4030300309008445410109046061000603c0013250205250b60041c3c8036080300c1c864041070b54034000603c0000e8034482c6040000d06007900c01c2145940c402812542218001e103802c02c0281c840004035810700750039802200030480c480301c0350402e0580c1500a48030000e01107007540c040d00d548480940ba00e402c0002c081c0c1503134005104180500248101504100d802410b00c030103060b4450340518115032044a040700c4609005c01c4803042180104551301c00750401c03040620b6070754108035070780007550414802c6900c03c0400000040401c68920f403841c004203e6903070321151132000300421042c0088035008040c020346160714000346916002400240c1c1800780d40314 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 277968947 1250 277967697 277967699
    0x60709140a050f180a1401060810060f02010f020403080307030510060801030308040303091209060206010b0909040204020d0b152203030503040b090c151207050720040603060e0109020306091204 85
    0x910400325555812540e002c0a20201d04e0300c03c200701640075201c0c505d1030794006101700380c4015660003070305c040c0c0156080004000800545410010041042e665641088000265000c0e4200d002d01107410320070f810180046000420060b5031001f0310302071130682c2c40c2403125598919150141000c9480b0b02c100051f1841d004002081c01200d00b04d410074003a150120301c03c0c04a861780c81341000f0304480103001a4030714904100b40e80c2d05008850242c07900411803454016140d000030010705000d80041d2142da400504103001e505154401040b0702805004440595900300b41e020300350300300b01004904d561069200310030300c025200c0c0400c00e50340e15844450450b210b0303444d0b0152801000380410140e220380d283e03070001940c40c00c0c2c02d00405181055480d076950150940c0c68070200300035058a00f030107400e210540015450003e4102030040110040c11415145030014010b0201c03680003409461401c03c0c009a00c41041d08041240c0d80207808850346512800d500340e9590600021003044402c09100c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 277970197 1250 277968947 277968949
    0xf061c08040f0815010b0a0507060204080a0203010b120a1106040f1e06140a0c0f060f0221130210141801030506030703080d0c0207030506090d090b04231f02060709140a05 75
    0x80a400c5000c5223281c02c034213001055603454200e0348640c1005009a211155a00031413074240900000e5180566211400d080c10b09034280d42e030520313a04000d1103d0b200b40c0805c1e40301d88500081c2c80042070715004100c00c83d9030303a4000000241d070021110f1048080c0d11404251980190070f03107006006048038aa189c520902422201010011421a44004081554400b00c1c9040c00340c40104001040016034410100d1019404692000c011041502c042c90401000c0706190560215030342c1c040c0d9030441c3e02c05984004032510a08544070000741d000216111100c420800f8050410342401c1e2820401c0c1e40b20ba000709139680c42030384001042c460f010421110b4548003030b08a1800c00c01b0700c0c012140341a031240d65441c1000b40480340652950f10008420034030a80c804803000060042404681c0b8003418200701c25003902d9404504018805050135000c242d8450381c0d00c0c0c08075646840c1d4092580168044029110002510074100013048000042083d4003c48284200c40000601034a81c2c1450720f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 277971447 1250 277970197 277970219
    0x90c0c0210032406051b0a0b0c0a201506030f0106030c0518190e0c04020d020c0105071704031b0515190b06090f03011107080a020105010e06090f061c08040f081501 72
    0x6c0020399090040440b42d1000689035401d440c068035407125115100c242140c4024100024000f0701100b4801c0541407405044000c1007411107060f000441c00c21a42e00d0402003850104401c044803842c0d03207003103400000d010f0100000d1054520860344800d80320700d0500c000700b4144040c2d4a003d1421048009224a0391040d800224644156000d071164440390400090803a040119800038094002420240e00320003885907591145041c10094070b107030030030240c0c0014000d00030001010700c6011140d03a010b14111440b8402050782c0310782283c500c8001c0c511040c02c00b60b025100c1001c00d541480b0700d9030042c44140074046504202030061030510340f04e8800c200340310020704000364043d541d884085624850850082440c240200700c804e0351151509070080c212801644502070800c004410300c0141d582d040281600309460b24015600c94480100141e00f07400e465403600014585007010908100d40719016104840f02054000176103a03480801c0b80e107175058400b0382d8a0f51032000c001031180405d08 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 277972697 1250 277971447 277971487
    0x11422050f0d0c151b0c1106070807060b01020106150507060b060a0504080c09061c1a090c09061c080c0111120108160f090c0c021003240605 62
    0x141044410303080c40080c030030b8105080300040c94005a20340300f40d0303020700c481030a103890040c07801c54040129071844035000e07045030316001080040140107002103041c0407010300c80ca000080010402070707691442d40303049011030b805008103c074954208884003c0c41d60042c4a481c084402c021848240700e5168901201c19a00c04003080303030003581d01c20f4201850b0325041c018080b030b00c4041d1501c6907542d081c14a62031030b02c00f0500c030452003980b030301042229584aa1910710001c006800045c1040046490b0603484038440310324218404082c002003200c10340c80001d0152402005440300e0350725844d40c00c14400c030810310300b0144950f4541e4442d2400007558207001081c802000070000950007603688100d110951110a05c000790385149401400035010a000d002d40c032128a5a00c01d4106142550200016450307100300d0143c20703654030101c88042c1c001d5035050b00c6e283e1700038001900c0d6a51200098010810350445e030141c6070040e00d00203c00f80002544105441c8592501030401c500c0882408088000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 277973947 1250 277972697 277972703
    0x1b04110d0c0f02070801110d0f0e060c130b040509070807200102070b07111209180a0509060112030801150c05100b15040b040b130503060a060602011422 67
    0x8000d400620109403007421809032450351a26100511000d0082c94541240c1016216900d0521034440f500120011101010040d0002141e45400900000300514604070611994003480c0c003044151041c850042c82c00c9582c01e8a40d21909882d610366082e280a0713070182030b07000700794200410140d600640b1310660054041c40d200703400c941403a00c03401103c10820b5254003107030f4010441c001000242c2070419030018041c0340840d48100100440740c0e540785201c40d440c2c40320760002503903410394603940320941040400c480f082190341062606400100022903540701d060052400200d400e0428002a106480c0c06035114000759003460b0607640d032444921140000e20000744c0f242c0002890500040307414800c036040c0020290308607070501110550312012092010020841408600420425101621550181c40307880b180740072aa441041d401d5000554148110410002084100e4004405031800f6a0080c446540d00c160410300c0664144c4810781c041c0390010000c0c03a104a222000b00607940 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 277975197 1250 277973947 277973981
    0x1202060c070603092010030915091b0603091a190e06040201020607111005101a0c0c01090e010501030e010b09010f080f0d08070c0302070b0a0302090f031b04 69
    0x14003504500c0c000a0741c2c8400040780d261005403042c4150000c580d214a090b605a404080703080e0030004220100f850700c41c10030f0503a0382c00080244640000080c96200d04003104018900306400c10481c4800048440461039201e4540403941034803a00038001910b91001c41202092014032880d981200010000b41c0240911000301404a9030341c05078030b1044200c0c00140c02d032030825000090600000074080030910a0411880076421400208841e0310788440340c0000b02901e50740d050120b041e186600c12072080b5500b010071040840010300800b00440040222410140e0841c011b40315880c9070701c203c1c2c809440002c01004694080c5d04a12403e080c18000024562841c20010351001800c4e00101d104004841c41840030b4802008024000c00c0c1450080118441401c0d0007000f00c20010001000c009c040d40c400400c05000704042c00c090b0511004103a00c690110300020025003008004c0c5201d0381030441c8141c410f00380480c202120701040f40038a04450844010b00000c1c1c0315040c2c810f0340c026 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 277976447 1250 277975197 277975207
    0x20406080c0901121e03053a0c090e0a0c0809010b030a0803090a02090c030a0b0910031101090b0703081b071a0c0d05090a03031401120f0311030d0c020d051201120206 73
    0x203225150ba01c080317180b090300c90b96180c0e0801c2084d850052000c00e0140c00285480c4410141804904150540e0b907514640102e9803030112001100e006480358403203a05450307408140700c0c0c00c80340c9411030032140710b055503001010303a14010350609940d04a2001601508206440310108070b10400542d404030031501118007a0380154003081450340202c1c2c451008031030110500c6011103240c016a108603030304842c03c40c42428041e200707001d00ca8151000805d51524541c59550b40c0e4002d01194000f0310b2049890b948500050038081d003c00030445009078021107805045054034614015a2152034020500300d08040004e900ea030b0f883c2101800349101c03a072043c042020003103ca8064144144604c1b4003410120740c2c00d180280c2641c21140c0e010b0000c1c1c070000e0040c40b555544000104480d500011589900841410140c40d040705000c40340c205400000f41c90742c0000010b800200c010702f2654211100b8214025049a840c041e45207800c2c2030503882d9004002051003580702001260004066034900303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 277977697 1250 277976447 277976483
    0x9060c14031902070803070b0126030c0102031006050c030319020405042a080105060f070204092009060108090c0f0604050a080a0303050c090906220e0a020406080c090112 75
    0x5500075200d01d90803400d00c198001250b5a05118010040c10040010360402500e84d0352200104d505005516480340310b256500c1d4508081ca21005228205d03409580d030340c203108040c6074044d5104031102401c0d039a2041c000245103204008941d00125a08040d5045403038481c620000000410352178803031581c09200110382c07641c03640714081e0180c05103d480556a0500e02e044441c580c00624600c080c007280100421068440c0c00840310000788901003c0d98031489480000d000700058800600b004019005400d18013030a011010320503403040399240305917a02c51004642c5004200d030042c003e6001801c0540423403d100b00d2110708071000600760783c10309807588003040d203c055682c07010003542c0c080131001061581610030b45c0d400c0500c1e103810b98509401940414060000030f000a03000d1300000e841900a04000d03040f140f00941e0340391040c401a000000340540d191492542a84542d2801c90005040348001079608000e05010b000750f02c2907885c1110003c48442078600c1503880c143c2e83d40c494869 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 277978947 1250 277977697 277977703
    0x5030a15120312110f0c010b04020408030f07030203070b010e010612151403100c0504180615081e070e0f010c0f1e062d0209011211090d11120a0309060c14 68
    0xe8170304000d0b000c0d150981010100c3c00e413080d0281c1280074920400c01400500d0000c4200c3da0241c20000b0f0259980707000349012465407046410140941980300004110480400c00040c100c2d1882ea58107035a01002d40c0c08402100d1419500c2c250350300840104000d13851041c03100145417a8001e0507034448515044001040d01c83c10488040029000141807100341403404031007120000d102c508200c840c5c1130003401910410411204002e110111002442e080f550303004103401c0ca40c03050315050b200e04008401802001000c2900c030711580300540700d41001c0d4440c10142443d242c122040d4841c00030651a10310543c42c0701005054113400180b100000300d6100d01070b010070a010f80904c240340d1401210090440c10006007038158007401008400c030341d070b03900c6400c04200e21070b440700000320341c0e0000601c5c041c18480c0200e0550008000c0e0500000c1c085901c03107203122050203498008091201d140d055440e400c1c80e10b00207020550022003402032912480e641d083c1c50344a421400e00000d845898685 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 277980197 1250 277978947 277978957
    0x601091809020909060c030f06210a05120c190503070b0711060105060f09010807090f0e0411190909020105090d081b07050d0609050a020d0305030a1512031211 70
    0x149540c8904008086003452014264442410b10180c446420a00100106d40c03001400304600040e02001290b41d0b0394a0702404008800222580c841d65003a8103641c0780c40d800c100710156654050f103000701207420038240445070302400d9500505032104080da00c20b01e05050009040da154071060285200142030118104d025900390b46030300240c1442c010b00546000e1058100300c0c00350906108018101c642d4405580b002003090030081c8a5558202c2d04680b0400242e20411001e2081d40d000100704040f9510070340181d0280820100180010703041c8258032401608034010794991490410003442c15501100030940b0500d4007600d00342151000030905010f0b88429613256500064200d90a0f0203041e51044009046010301422881d05d030000e02c3c92030b4494805407485480c0e068260421505000004000358010401105d2070800d060040003034100301c8141151518092640d00c50307000c450100707003c41c1d0f068207021400600c83d030350465000000420300c6d1801d81e01d404140c1900122103020741 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 277981447 1250 277980197 277980239
    0x501020a021c08031f0803070b070807021515030601080307020105071b05030604060506030f070501090612141302011805031e0a02040f1e050c0a03021b06130b07080f01030605060109 80
    0x943d03001714040010000400e5102807081e500401c04100018008040154405042c0c282200300b981d91072016401c00c0005860007003000f450004000302080b1481c401104c64100703804651050382c8642505a80340700300b08010380803a000384041c00c0000c4850340f4849014008008038009982d48902007403412605076400c4508580b40c0e420880e89040030410043d405140300020b02129140c4400a810458240108420028451002c1d58040204c0d080784400c03454000d01000309182035072036940404100f8508074001222154690b81d028040001e8009a500c0100601303004850405607046a07402031400603000d0080039014405170742d4a105407803c903900e004001c1081d00b0944a0782d0050403002d00c021041e2460030052040740c0381c3c0142034540c040320600f401030782c526007401117100304003410710859100d100748010080700511034400900020310500442c640c5031682d81e0181d8901c0c404598501c000d0041900400c040744140e08070075000507040c14041d5030701d52511030240c801c07100c1117185 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 277982697 1250 277981447 277981471
    0x51506190305030d050a0203060a0b09040e0a0c0e06090709061d09040609020111010c02100b06120405030904061a0a0e040e01020d0e0d08071706041503050f10060501020a021c0803 79
    0x100c0d403138440d03034007805a012a030f62204620314a04000002c03058444c50150341c003a4140492280b40350780302c40d0310000c030201c0700504071a0350703100e90324049042415174010300d0591080c0d980400d80c01c4c00d00030b10b01c50291884d0344400d0f41c80e90521a0460704072a0703100e4074000d00000d01505500c9034940e2110f145c0100e010314400308a1180c140000740001007004400140c607850101c03404907095010495880c080c00615000c00d400c00d141c00021000d00030002001d809001410502040180000013051072000a413400d10584e40c0e9400d42c80f094022000002102c44010401300700218031074a46900c441c0350003000090851901c05003142240c20140c4019101e80c1e44108556004078100300f10201d0140901e400f843ca0301e03000900400d8182c079440403540c0058108041007007982c507900404c14400b410b070000b4035102d549042150752403003143c0c0d4520480c005c041c01c1a0031845180182815204187c005080700071003a0b09100f0050803404610400a81c690701c034000144003e40110f0049000e0041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 277983947 1250 277982697 277982707
    0xa0204060905070807140909040804051c12260a090501020307110c040203100303080417030a231b0f13030602190f120b040e06071d09010305150619030503 68
    0x40a004130714068210340c20b10560425a00540101c803040b501c41c0c100680b4080420344a0385803034415405030303801c0260300c51892119007070441d21a0000c1c401c074500540c0d5400807a2070030f902c103a0f18040f0402c2e6074440c00300340c25048010706480ca0310903900448281d00c0018900b8150b15058220b8100361400000103910082007011854100320300302605904480071441c0d400c004500803407110396484000c060081d03100c0020b05115810345e41e0006807000740720140d600d14248558800520800b403035801200c0d045884080c658980b489801e1144403545a8602c0c850004103a020054002050800542c1010130401000921070005000114402d9030050b07210782d242c0d41141140d02000d030001041000c0d081d040f01c000d651102c1515450076403000d00240b0500d2800119000d45031402000109100d068240007485602050300300752001403d50440f40101400200602410b00703100140c10b030340c0411404170050303c029030f00c1a000400141f078140004001c1e80704a800303070301039401514640c1010403 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 277985197 1250 277983947 277983961
    0x607050708090a1403072c1308191d01020606120127020109060206070801051c0206180a06021f021809040f0501140103020d03080705040f08030304062018030a0204060905 75
    0x114100c080c02c420315020301f00092020010400001d00d10049a21012034000b00d20009202d5401d0700178140c1146405558a124003003240400c40c40c40c0100c000507044480340c0702b9002000203020700b0300205034040c040b161504410800e407082207500b0100c4955031000d00341c441288100c0542a020f814515110101c0c07410b0001400c001ca080d4824020340d0859410084416846404e40c6d0544408449100802c0c203c1c4046845c107400c960b00084d04600001085601c032a003528040308055030843c2d1040100d6220141207031141708102d5180b1255205c803909440e20320150300a44051042c06120805407441540000e0b504141234134146d035500c2081080c041800303030a0040e140d401105030b02e0f0850301e52460340400c4511040303802c0075040000d000302181441c2d105504550085ca011003c03000c59075218004d1644960050360111845454040712800d80c002412906020b242403003031250400a401c3c9040a2a01010741e442d41d05001c1d11090b000180d5451040a001e0a4aa40c0000309441e11032 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 277986447 1250 277985197 277985203
    0x80106090525090b0304080d050c090310060605040603020903030c010216060b090106050a0c11040c050903010b092a07060c0503090d02120409020a030e011a1309050607050708090a1403 81
    0x10032001c0c070581c490541c1c041c42c9a08400d8250031100d41c440450b5595445003030604081c00303000b0b40b808159080a0a211081c0d106401809040a00b20207850041003a540224111600b510032180460000e000400c00f0300e0003a0b0140100000181c10ba900e050380d6459030030b089a011400308161400c0403640101130010030f1040f0f00100c0c4003581d088445506100c4058800d02501e62050100701ca940d18260070040d415500072010080a0030034407066401040180017500074160b958060343c07a00c00c42131f80602d80412214010398406981d0300035192a400402c1c0a02900700280307034840800c1125200140c05407140b4401024196221074032801c01001d09410704104000301700031540800c036040703941e81c800e00448003128450b40f0300603500e0360040c40a80103010a2003150701e5035481d01d0001d50803504031400d4411800401c40d102c27100c030b4282901c40e4040702c2c441c040281859005400042096000c0e5000300b207814064003a260811300090300007060105550004400d9110001009806040070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 277987697 1250 277986447 277986481
    0x30417010605030a02130e0f0706020d02061003030c051f1508150609060409050f01090c0f061202090117091c0309110f0d120e10110a0b100801060905 66
    0x82000740000c0c0d240c000002c1d0345000744c0c1e502a21170b104507025004030130b14540c80000c01c90318040039600c8240f109900140c95860350f10404001d4015504d514070800d1010440c0c0f4424100504440c0ca203070700f55242140c001a011100300d40034407960519940a510108160600c04441400070460712800350003500c4850307881e400045540e22000e0110261031016240f15809002528640c1441c0d49030000203001c0e11440c800070f0014001c40c0810006a40c040d00f10345011801841c040021691b50702140980c81190f01c00c540001e01c3e04c0c1d50b880d482080c1500101000601450507845403465002c000304d01c28416501d0911550010101d003000680d10401c118180e009400c0c100180c0c665a103910000b8841403540c24130602d1195588038070b9a581c141d40101c0180c01407038044400f111080090454492108803074400c4050840c4030002a20035412a861840310b04080c00c460301241c5e6500d58000809000c0d1103052114220205808009102c0c2900404810700041002d003011810b41c295801c007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 277988947 1250 277987697 277987739
    0x110f010203012c310501090209070905010215090309060d021b0c0f120708150a05060603100905070903020301020c0307110901030512160c0f060809011b1107090204080304 75
    0x3c0000c3c2840904810340c2466110031260800d40b0000002c100107246030102e044c040d41c10500185004050200550040c80000d10a42d6004059219030303d05540308089071154a0059005424039400c004086a070039802001d001c00302c030304200c1e030080010001e4020b68260f842da20b0340812000c1f1140d024040c04485e012402d005080c0b208101c3c808152043e86d2164800e01820700341d9a4590b40700c1c0d0420052005218900c1911005051800c01c110407000076941000f1a80c2044085545868401d040307034000d030402c41019500500d092050030242900421101c00e0000030341001016071400e0005140b9200c03a00080c41d40c90b041440c0001d0180c0c1c4409405015049407030062002900000701d41225071034040710603444100f803080c084015510b0203401044100900070005130007107202e401005989a0381c84091032555002c181c4d90888048403080c034855804220841c98003401500205c0c404400f400c10b403508161034400c90b2080c1d0f032183d07208454540c0005410002039441c08050000f0807a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 277990197 1250 277988947 277988999
    0x14040b010b0f041517070f0210020912030d0b03120a1209110a0303050418022728030b01080607080f1816091d0312130b040302010902030105060307121101110f01020301 74
    0x20f1481f00259210b0b40c0224055901b980020518000d03070382c0b4040443c0d19147c207012656034010640e0000c1c003800c05162501d0192081245000091803135500b40c0b25007059903a40d000701c4c4004008404044c01e11240c003601c0044001001c2c004584410848402460090301d0301603a031403034042120300000c01500f061103818418042c084103c200c0f95114010f004040781441c024010b25030000301c92400071100d01182040c0d000e00a8004031803400d614080f2800b40350155285e83c1d031404503070b840740b20403103580002494480004400d5a4040051500074525000c10111104c0c112000c919051408081d03864100c0480001c100c443c845010b0075245103083c50203501e8400c4103559071f6541e070040e81c60020003e00e0150010b60002c2c1401c05800c07071103400045080c680d08050034061f000305000c41e0164000c0d400c00c400550b4a003400540755040b144000020301d1a40c00685800003591041421107041180420b4400d0140c201000f007101c074010751000040c1d4a515004228201c04484421040801 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 277991447 1250 277990197 277990217
    0x4030f0e0f180c0405060d0c0801050108280605120f0c06120109200d050a1a060403150f060303091427040609141014040b010b0f04151707 61
    0x240b100011403004210040307049803180c5800e820840b0a0081d40c01240c0c02501c0440c1010104000da040301415030503d413140310341c590704d46004582c0d2150403205001c0d100d541c0100e400c12070b080c0c0078213608520304603580050402e45903000103014201d416090b540560041c4d0340d076801c0050900c0400e28483c02107584515000e01c08000b1001e00768140320343c1200b99a40c113803490b140c42c2d5940e40c115002510582855603222075001031001808103450f6202902e281c4110f00c84840e485100c114000d40d170089c8900d051501d1070342d03101040300351070820140d11078481030389440850b8640035800141d442515184440c9061131102207009c2e80310321a051040304040910440b00f0b10101c1030000160002d45082103d58039824080d001c1c19000400419940d00c44c0311100c1c00e078002142002d001c0c600013005000580811000d8240308000791400f4102e49070001c010841302e000c070b000504030035035240700c12070a0030750300c08081071030010790842d00021403000c0301c21000c0603501c02005a441441401e00d00d00172 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 277992697 1250 277991447 277991449
    0x10e0307050402271e1c080f0414030703020105190302040e0405061b0f0a0c020102031209010506100314220816110103090b040809010309170c0f030408030a05030a020d0504030f0e0f 80
    0x11003005e601c41030003007800c25003440b5001241003400d00c000c1c0d00b00d0a56556180814501090741c0e11511072461032102c004031445162030b01107a00030482c1e405954840c140886402d281840210700204002415420000010f84120680c220741c4600d0050014248a02e00507074020074280c0130880e2205088010049803000146000c00e492152885140c1501d8507103940c801071303145108014400ea0031415810400802110540000707104210a980c40b10f00031540600a9042d5269040c400c850000d2001c006040b548244003104000141c500e0205144c8201e9141c1012a41c86003502070041c107000a107960034841d04400d0b8488012080ca0200700c40345c81602c0d1b640508001820040107208005100c0136968030941025201e01d820004c89000c001100020802a074040c01071420107014415034401e0002010042d40d044903c40c401070351a1031005081103590364002030071a070350981c0c20b00110580103441c0c0310b810321540c860707124414085d858440240000d2140c80c1d001c1c1c4104440d180c1e480103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 277993947 1250 277992697 277992739
    0x9050d03081501030b0409060501030507150c081e040605090a060e1c030e030106080f060108030403080406031e0609090b090d0c03080c0405031c080f010e0105010e030705040227 78
    0x2c4441102e4a400c140088440102c01410300300c0f072016481801c2c0503541c014000c1d00d41c4014104c902c036608451225030340d40740e4454248602082070300807500c0694100d01107144007005141b00701c04290009511002d20345803650350b03001034109400084022900c1841030501018510241c40303603041c605105042c3c4000904d034800e2003140155007150308d1003010308042c0158041140050000c000740501c50b243d41040e60303110410758240c01035101c2d41e0000601c80740c6c08002c0350260303600031440c03a00e4141032010a81c090600c1000120201030203910342c1349104a03620070038020340940030740402d0040b0b150620103500940a4100c0da10740d00b010350b1140174590440c2545d090242c0c1810503003a107503140200f840550185034006501401940e0704285500f8944001e034444443c282c0f603078201d40d114400c5103030320400240140501441420b0050150350b0041c003030781644a8000f01140e5603103403100086010790708414014484a40c4852010f40e100614180c05601c540b010340c0c0001c1c811840c03400c2402 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 277995197 1250 277993947 277993951
    0x70e0c0912010b0909100b04020309190507051f030b04060605031303030204090c0906120506010c0f050a060c090501110102090a0e0c070b04240506010206010e09030c0709090309050d0308 82
    0x4800c041c82015a0440002900480c1c1e10309802000300006150004041d51503d8450340110f0800d4034081c0d486142c3d1030244280da0150010030000e00c269500e4a4030345100888420b410395987c400c10800041c10b660f0059069001000c0f0401642c0369120244050203841c00e80c00c0d041e04c0707941480c03824400c00740d0000a480e402200110000a50141414154002e2043d80c00003034000341848810151240c029000384100c40c50355070713248002c45049280c40c0850700207890950008940038098804100341c07001074541c0c0da000f017041e11415265681e80d5030440700c1c04071421740829200d54003046650307001035102c032444042000940ca041645e000007032944699001d54460700030300c4400324134407509103000c0d6440d89500680d1680f1794180340c10040c00481d0140c01d01d014125010001c2180d0041d00e0088038011841a0003c14a69003850f024080f002c400500b03200041c4028410115160000c102c140c00401c030811340000c1034001400c00926089513900854012004000d9100c00698450b403ca9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 277996447 1250 277995197 277995199
    0x52b08041406160312020f07050105040b07050715021e13080606010908060f1e04080726030f0619141509030a030e01030915240b0d020d09081b070e0c09 67
    0x10550001c40102c05e8002c0c0201e181d80c40401d40c0120783c0000f001015400180a540555002502e5640e6054205c90622030302200a11044041c0c00c0c140d200078050700544101101241100d0800d0521803017103c1c40d41000900c0e503038641c0500803c0105903c181b05180c2c1145013840c1145942d801c00070002d954541c0a010b9880026418000850400ca0a411788207412902c4490300b00509103030601c80282e40091600356400c2c8501600c180000c0d4022626250400b0481c4007035055a030746510313000d8802d0006000b0354105880060f59024000c000e0921009401c04011300016110140f092201d03170f4030342c14031028642c0b404001517517140c3d800142016a0542c940341c44c0c01810a2480100d0103480c20b014002c14482c0200800344e03008455401c066440703107000b0041000e0564000349001118502d00c1101d052510030484010144101d030020400c94455100200d08001140d41d000010b6100da101020340a03850a2200703004842406043d000380701c09144910399041c10800c0341e1550bc1050001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 277997697 1250 277996447 277996457
    0x1c1e02091c0c0b040e010f080a1e060608030d020c010f0209030c10021c0f03140f010501051e0408060f15150304061b031d010510052b080414061603 65
    0xc00104804294540d01600c803051000c2d403103071780c1d4220f1080d10036070030301030180445919000802d0104000031040d041702e8120005890f401d8031064001c2040400b132400f90380345a102d0301d011401407001c000400c0c60401d4804016038030508804150300311285030043e24510740c010403500900b607500080098000c44200c8111f1440f0190304801e0340740c04444a000e0200061301d20b05500d80d190000034880110046840c14003048071891760203403072400c0440d01c145038400407034010300155105001509940b0910440040c030b0f4050003007921041e8005034002c50040d400300c0308101d10040f0301d03a001600408200d0b50f148030441008005440c815403400c40b400f41c440003000080038070070b17590081100011111205510100d48150007005404010302c1c810b40c0002d540f0071210303420343c140308007403103a040381c2001881c59040800f000302041d0800104048024001107101c1429000581c1c0131090344184130301030740d8900d0000315940b004403001800d84a0542070050010000c1ca950000003c16414a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 277998947 1250 277997697 277997749
    0x230307180c14030c2b061a0316030221040b010303030e07061409060702180610021b04020f130b030108060606030105102f0f011103010f090b0102031c1e0209 69
    0x840d511546000203080744070042c0c03251000032101c10386d0044064400c040380032540c065501040354003a20040c0c8e500c114210440c144040001c0c441c0e0f01070011407049841c07060701482008070046401000352403e50b410f00081c1e0040042540500c9094a0007003100007134070001c2c0c40c201001c0c3c200d051101070644005800114118a645c07400101d03a0b10543c000c02581100001d8950064a288200c8000d800384860685440e141800003a03411f02c0350b400221180d000360001402c1c00007a412080c2118840c003403d0210140382107400601c0d41c00781c904869007948941c901226140383c0600989460f0040e0002c100521046c0c483d18081401d10038941020907051000d641d81c0c103142c940480d07204070301c0d69020b90798642021000c0b90b14407080e107540d802802109804440c1d494684028441c400d02c03003178030401c10813503d031480e040642c03e50720500603a81040c082c5200882c90941140c3d00399a1259078600084140401e651b11040e40a00390b02c085003461405400f003030700402003001c905540b0b007102c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278000197 1250 277998947 277998967
    0x4050f043f0e0f271003060507020109060b0102060105031e070b0a080406060b0708121f0b071a01060203070b090f0d0c0203060a06030305030a0f020418050f0f040804230307180c14030c 81
    0x41c201d03006540c0608100023070301e03041c03030024000c0021105c204d403418140322510606600c0001d159060322001005802b40c0524210070500e00c042e00c1403210703844d00403004005807588184c000303080090a41d4440c014185458134282080f9480368200140804040c0010401300e107030001555507800e01c00c00c030b0900d103803155400102d0112800c032601811452a034004201c100c8008082c0c008244113540703140c81d11001c4030346100060000d0040c480168424440c08001c00c242110240d0440815000d9608003824511041c0c00d01480c03080d80800b003242c1255041c00c50500b04216903200c000c01c40c04100c0c550941e60028000d1002902e0382e04a1038a03207150b4062042c3c207504070390042c0710f603603181c11100034a01e0402c2c010703103422250303c00c98a401d81c0c0020044140201000d1189a1010b1445d1900c0e0415003c2d84840003810018a840b0300343c0380d401c000c5074400b0002e0001400c046052940c913403d80541c0d850556140300e4020041112480359283c1c803004103815a6000000d46e200d041c5c80b0002e8074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278001447 1250 278000197 278000221
    0x201020f010504052505060f160f11010f021606050c010e010203041a01050a08120d06050303031003171c0c0509150301030204050f043f0e0f27 63
    0x1600c0212a5180509000c01c0041c00200ba00e00c0d5002810b00181c810a10b0041e214241c0f018400ca60308088104012a0390f042003100800c0c0d8412102200c1840a01c20303268811030002002c0d00321500f24440c2400c1a61790b8000c0090001041940700a044102080c034151111340224410902441804200800100310079001000c0d0900801c00841d102d29040c02c282c0044000f6100c000032440c0c0c403000220b510b060001d03555090b1a501c030014104a62810490b0b0451b030b000826001c6030a07520000481c0c0c540d02800110b000b0b191600d082480c460441c02c02c041c521001e10031440b00303000c04000481c20ba030041103900c20035046500000030901007a05003030b16a446000745040e80300410031114074020003080081c0d0b060340d0090320104629980c60030f05480614059070003400c042100368050940c0040111800d0340a103502900c1e0002515400f6140000282c044c0150003107207054404d400c0314100b4100500001408a44189114405d003402d5220180c00b140600c9205090350000b88403110b40c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278002697 1250 278001447 278001463
    0x11409180901110a1d100c15020d2406021b120106050a060c030e03121b0a2103231603110d020a0f11071511010203070206010e100803040603020304020102 68
    0x9941d80e5500c000440003001e4506801154a1400710016410340070b0500401c210502107003500c0d4045084403644415150b1550b1050f20841927070200403524500f5250701400c0340c01c940600c81d000600305941c5125040319681e0b00003404640c002401c0c0c0e000c500d81e402c6850b0440e2020340340c401d64001000341080c00341c0295000190010b040c04000904158000c19841c0c0050080da1850691030940c41090748415600c18100d60440c0180300d83c0f141c18208922200054000b0790448404088581d1110084c246420020784200c400c880e618403160b8050180b00d00315034042201c20000302c0808411940780c0e0780500032030200e881110342504410b00039031240b01941c0004108944800c4084502c101035031080e800800014400e0f003510071035138000e1040e80203510895025014050914504611080f03a1401800401c40d142e642101c4a0000b0700c0154010740d4964050941c96040150556461030054003400b510950090100101c0c080030080c2c42c04d4928030703d000b41c0d5a40726400108e15007401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278003947 1250 278002697 278002721
    0x50f041b0302181005030601180b0405010f0e03011109130915020309070b280e010e01083103020705030f0d0309030e030327010f02030702060a0c0803070e011409180901 74
    0x1c101c02c0c684260350418046c1d80324040990b01c00c0e450340c4064010300c0340ca1081c1d2003802c028000500c8140110343c09100d49400c03440451800203101007002c000079081d1b9000034140c294200002980020758241501c41e000d00928050043c0a0b2001a503103281d03400c000d80084884140d404800320705260414814480140307100d150094540303100c3c003d00010302036203160301140324405036000110320303004048100210f5016140c11044480b40401500e640000800c1e2890702e4402c2c5012160005490051040011086a441110b0341d01c6d0b00d406440c040f003035045548241d00ca03140a050030180040d1000380609540b4003c41c04d804245416107010b0301201101c1e0b4107000100b108070001070600401e2075220016200107000b103039064010b4a080c6140501030005803c20001c2a002d414090300401d0060103600e00201008950744a03d52240c00c240c035141c0000d083d4000c1c0440d19a0310500c10020b40034841c000d00d1030079200f9000640240c42c81250408503456400000d4440002948059031840ca = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278005197 1250 278003947 278003959
    0x40b0609030f010f0b0d020d060c02100603031107050f0d0609020a0e040f1101050a1709030d090b011409010b0d0c0e190302150301140d050c1504050f041b030218 71
    0x102620781074064010042280400c61800e4070154240c82c00c00c03610b140c0c1c2900640b03c0c1c40300d5040349d11600080d25170303010000203600c5120f0580e18607208c035129400045000b40c2d101d0b01800a1801200e04090481d03001611401d10000c0000203681c8160851103840c0e4412000114158144041886d04403035070b1000c4000750300c840400c418080507601c032640d014450010524aa4110300055620b030150841c0080016644030006845280890314a03402003020b0b81141e04110f4404c088005132040300104480e24410700380100b14450021110f4001040e0403210f03400107604020380b481542c090303581d44203550b645610f04034200c103002c0c0e100c8070440000984149a5010301070300308184912030344402c90041d19444600202d02c01c10700d050368142c41c8541d0440d2081c450010030801e41d0480400d05540c02c1c014205064202e50350716040c5070f140840d984240d41c0380ca260000f00606a212460303658092800c3c20010890581240034511140c3c00300c2c180142c42e503460f5195490f00b40d0390309440d550094 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278006447 1250 278005197 278005213
    0x1e060703080f0703052203110a0807030801080c0321071505180a051905070905040506190209010c23030d0203041205070b04260d0f0c0306060e040b060903 68
    0x103a2000895100350340302450000300f619012801c40c02c0700d80413691121280d860000011101d40000e03010310010f8001d00d02040f5425801c1c0740c850410600010844441c440022240300701608a050b20f401414800301500d10440d110001c240c49080000407610988030070940f0340c0300044120300b074415254002034206414003a01d91003000400d0255070002c2810304040c250341c00c0c2040015071040156202c40079000000c20582c02c000494140d00d02202c4a004244001c20100050301c0307024802d038024401080181848401001c001d0990381140400c5d45c01041401c08691b00321102d1a07009a228446170340403003148400c0e4411082c42407210347c441c040000e403c8081500364000d1402640200c1121108503a02102515035200309070380140070202050000340422600710740240070b441b9270300004000104248001c001c0740d00400c5203411443e940e80c82010480a18403070107841e140d10741010400c00d400c1800141c500c0d8078400e00184280d480b200001d8641e120074056401d8000041c040354910 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278007697 1250 278006447 278006453
    0x711030c011e0c1d030307050a03121812080903090a0f03060b0906030604030809120a0f0f020f0705090a09080708030f061e1003090b0c090312030907051e0607 70
    0x10b004400010034020001c00e41644016035240700303803128210240c0724103613049003580850503022032040d281541400180109800305d8001c0c0441203c0c103101e0b0351782c250000001441c6200301c403900300981403048440c034580000201100c020404c900e8007418003d00390355508d40814039600c80c1070043c540000c00800c002588048210b241810740c2d2040e1400c0c09140e1100c07042c0401c0150171a19103502d64006008180481d01070341c0c00781c0e00000480c003030711003400d10201e0514155101d0160701001035000004251041d621111402c58101503201410b00814184081c82e03941c081c40c00b890788243c1c611000710307a2241c0070b603015000b0543e00c110000e4940c00c450410700e2890b0411104a2001c401010004000d0300c1c04a0030f080301d00c1d40b2514450f281800a2051090310030790701e503540c018107580d142c001002c1202800b80d0791090906402d4075580b11200014103041c14040c3c00b41100840d0f007801401a03d90f0080391400a54900f0b1703c400c4041241811340503081a055000150000f600250004c14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278008947 1250 278007697 278007701
    0x9040b10020f0c0904020a030b10030f12021902061801050c01050106020d180b0a0807030212010f080d0201050f061212040f090c08070c08090402040b0c0c0324040b0711030c01 77
    0x201e542e03100300f035841031046403050000c1c003081110000c0d4002d04200f024800907640c2422207070400c811060b40600e603074072541c0740c10922a0203141500c2d0b078088490360303a41c2540c0c10403841c0200d111185250030103081960104030b142c000e60211507485100c0b00c2504107a030744100d040c0c4e40d075014044001e00555a503940d002c0e4550000304403d00c0021034007000300c21010395085054049542c29000a4501002004100c07441a0013401c0c0d802010380811405008581007400b850203021080103540100789015803040c40e01c05480c1500042d039042000300681020b14041c125440041581c10350088008140e0442c103096000703410001d0b00e100850003149414901c0d0142d0160303040745004001c11003400b407054410302c00450742310380000c22054201000900c5440a03001740d40d00980054201501c1d58000041600000c00d0300400380e12004030307a0b805240401c4030192134000c1e48601101e001e0001c1da0300c1c0814400900180007100204003048442d80b060f401583c03155150815203468243c01c84200380 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278010197 1250 278008947 278008963
    0xc0f0102070c03060b0108090d0e06280219020a051e09040f02031207080d0f0b0d0326060a09020f07061e0f0c02030d0908071e061104030803060609040b1002 69
    0x5219480e11717010882650244040034054080040100403625964104891402420f09c3c1c96030031030f1080c040f00000c41e041c0b11012040c60785840700c4042100000310020320740502042c1c0b444410f0361041a030030141c1c44185061007642c00c25140c071002c8448080e402c1345030300a0303080901d402520007030400c41404040051103882500c01c4050f12030034a10068016040e0150303600c050b003070100800c8000e02c0c181319a0300c0303400d00044968000c100c0c8041c110000d504a02046401e4020421151490396030b4541d089940c1c0070001a040c03101e9003805c0220100d50207181d5401026601d40c0e00144403469074048a00b40d4107400c0c0c2c012000d10000c00310341c4401910883c00001050380310b050541d9645809914090060000180d0f4025428621500707203c002030700050f6000c0d00d48a5080025402007403c0e000c0c04102a100e000300490345110902d010401c40b8103a0800c8408250b09100510029400c40c0c1140c0d000300085070420340355a440c03c000390081c41790066042d4440341a20341c4d1020680c020503141 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278011447 1250 278010197 278010203
    0x50d180506090d02150f06010e1002012f0f03040807080a0507061d250306050c0405031209010507020126150f120319051b1b01020c01080103080c0f0102070c03 70
    0x340d1080c40a40c091744d658988850181c1040200300004601d84000c00b4441e6100c0d105141002c0c9003a469004103240c0e030030031020080141d46503205c000f51200c1c0c000e040389004424124200c0211807518a00c0880d008400f1207071501c0c1c00010101d801c0c40703c0007064840c1e0170f0b081080e55640e0b490310000a4100d9005120032144141000c02003188a40001e01d810440c01109010781000c3e4002c2c0c0c804c06d12490120515820141450000b101090b6144146482180070504007030b23030f450515080616102610003004004802003000c41c0d05a41e12000392041558203082500e03900700d509203403c2100080380c9005018190340d500700403014458241c3d441c3c0c00c040070342c0c80741d02804074802800740050450300c482d0301d00e03441001704502081e0262420b00094141c0c1c40d00b6802c000131181c103292a025500000c40b078503401b104520003031041c0080c941516040900080c00c0b01511500042c050900c14807024020390004110311030000801d1104240350141c40008542c0c9a080b032506d5000c64041d03000507 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278012697 1250 278011447 278011453
    0x305132403061202030705280e10050a08030901030c0302070b07031409070b0304120207030b010b042301021c02070b0a030509070501020d051909150816090b0901050d18050609 77
    0x40c1c0c281c6007100741c400084d0054041c0007158109400c2c0101d40030f9080c810100d041102641d040c8560040d94070310050207c6031245400c0d400c0090044481d0311190304198860364224000f001640030000444052003420300340498040040202a13009000f00c60f03000c0c010520700001c00c82030706d40c95403006045402551520745503403258502596601c100e40200e0320404001c00105020640e842c0c1c03808040045481150720340ca032203a4658003510000e038004468204c02040c01d200303170b034010b03282000b05005805084280e1291000002d540b44041c0c90042d02201c40b6003507009285200b8444a009003442400381540c6102e17400d0014000c280440c1c0d100110300551401066941c0702240e80e041461304c0e41e0b00c403814840484201e4940381048008138091105102000621009401a0a0f41001c0f540c4809103289042c0b01780b030b0100c084044510701084822507060160300c4000041d161481802c1c6132880e2590040350041000345403e038200f01888182c0d11010342089000102c1a200d074441c2302c00d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278013947 1250 278012697 278012699
    0x70203070c06030209120d0e0d110406030506041505060d03050702040e030f0c25030b1e1e07030603051f0b03010f0209010906050a0e09090102190206100e04020904030513240306 78
    0x155191007031203000700c001408d0a07140f01840d141400441955a02564041e01e11244180c005001c59a880d84100c8082c0c2181c000c20003804070a40780303403075811540b01c000e101a03c1e01500052070440b0a600040a00401060b22010754407a40e000002c00d0510008882d524050212109084c0d00138080300c260703d210b0780246100001803640d02520180015610050a038110366031323200b00c004028810440c02c007420000c003c43c2c0c54014404d6014075840d0400f03020603120007070b11400300080103025105160401d20208006040010b2050240020703c0000384001d1300d2110182c094200d2200c195455800d209000241030f0540c1d0043c042003009886103032166650b100c0965003030007010401400715141e03214880c00f906011001c103070b01a01c0900018606010f00c441040c405c809503c110005034811001c00c5036098516001d40040c00c400d110142d520f150680c0064404900244024100000400d024080c0c5202481c2400a0601400294640307482d011101b1380f50a4502070a10000c3d003001d80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278015197 1250 278013947 278013979
    0x603061707032102160b03070e061e1614060106021c05041202010504030602070b060405010602010212040f02030a050a03031b030e151504060306020d0507030e0303010905070203070c06030209 84
    0x14024003101d50051001e490208020074401d102c0207010075039000d40c013800303d4410217842c590f1481c2c80645081180c55840e4280000020f042ca80c01c82803140c05010300b00140408030600046003203043c5280400680d4900101e583da002c420000c41e4020160491745080300105200402c850f81a10308a82c203c4068001c1150801d27801c540d01b07a07003000030074000c110502402c00f4a4050b1042c81f401810024074203139603507039841d089910180040d564400f10509004503407078a0b010300350042200d44002d5080101c00c9507000c0070310001034002010110091024801c6440600c848842c103a004003d54a102090b420f0140c050000e1f01c0140300c1e80c0c260109041003842c068400d8101f8100f10200074005000c065502c01e0403100050300085da4001507110003051559240501c0c0c018511480c00586c545040030b90f88000c4d20704c050301c80c205150402010f84c2903818000250b03811200d000402041035114544240d003580b00360355002d004c10302d440c140441c1150700368009001210041d02c0ba406d903104680 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278016447 1250 278015197 278015203
    0x2104060b1507061a0d0b091609091527020406080f0d0908282d022716050c0604060e1b060f090a0b0a020a120302070f0b0901140106030617 61
    0x4c1a48410b040b250b060100d072804900c030768890751103000c407440c0043c0e01d504c800c0d40e182d5960003501c185446031350903000c1200c44601030b9481099104240000ca8003000f00c2c0340c2c04407110300c06000d4046a04031443c00e543e00c58001c1c200400821054a10000e40d8020042d1510020030703445000c50301e404c10010b1401c2e400100e0042030700355201e446001d4018818845084508850f0640301d000b4000c42e1042c0080c030b62120860791502c4160007400d40001441401940d0700000c10b9100051410074a10341c5c601e42403590f00d40c1c000d0600600c50b8900340d070024103803418011768004050314030981e004c000170030904c0d90045a6050301d100c108c581d030000c0d2003e041e4008407411507103500083c0030710008603041000f20103020340c0307038009000220150b00d52400c00501d4002c80c0e1040d006078400c10b0031401303104c030743c00c00301040c02c10f40c0c60294034000751074840103440d1824040c000c114124460000342ca903c4290301c181540c0f842410f4500071940e40d03800090143c0564014251504000407207150f4482c800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278017697 1250 278016447 278016491
    0x909030d0b06040e04050102030709080c1f05070501060b03090f12070204020906040902070804140d050d0f020c030f010c03060b07110f010c02040911011e090509040809090c180103022104060b150706 87
    0x803b4002c415801445441c28000b420a0241c01d1180034010003002a0083c00713114080c203102100c0607102d2800e031031042e141c0000c41e0020611031b0413521000d143e1000c07600c1200d2080c5c0e01031340c0250740e0f0501440407440e50700c2960322410b04030340b0208074517041002c60f1008100b16041100e43c0f1440d2035070f800c1004a050b514402c010003034ac0c082106800c805008004200c0c1111942c01521041d02100002c40d05107015a400070300280d40d150000c400007505440341c4c0700074009404103d8100f900d135035100e80c0d91288440c2c50300d20030a0b40e912006030f168841c0280c1d000142e80035000780018803d6281640c00c1004500b1140c1c08280140c800103030344200d0705104c1a5401140d07590410351803400050089008000e00150f9003190104444035a035181d80807118016a40c4184071992a10001d4517100146801203c450425004010540034110b080700c3c00522240213520a207003644071403030010000c2821f61410382d00310b035895001031980020034000e418294003521050040c6c129242403040c1041e18 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278018947 1250 278017697 278017699
    0x11401031d0c010e0406210501050112020d0b250c02030d05090a0e06040b061c0605090105010816090503160305150408030f0c070605040f110909030d0b06040e04050102030709080c 79
    0xc400e9250255601c5040318004444d00170b000040c5280e201c40c502e460780da2860020781020f01104e0407040030400244030355070044c102c070643c0041410b440e5000035010111207102a00b000503440c0414400452104034040c880b1400c103a090f48440c0046015016000c4940280d03c68042c90340b03107818150082c1c0803559007010040040c1211403c1c0401d42408a401410254005a80d41981b03400754551000a05000401101c508041400035003254123487e4150407075070003080174500400907170340c0100751141c00c2a01c904118410341490801206d20503141c0d844564907210344440b40c01400140074504051b40d0103035041d03421110045031030441c03120007903c000f03260031b90400010f440f10340b01007021504140505140e40c0740c05031320385035882600c100b0b84050383c0c04545c0c2e0740d40c6400c100300c04180c2c0d031001c5000c0d19944e945203000d401d207e45a00408e4200e50445450300090140740c1c2c0c1c0c01049402804845001e41c1450a003030410038000e4001319007007000f1482d2608040341c90700001804480c1014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278020197 1250 278018947 278018953
    0x10509010510030222230102100207050139050c070611030d050a050f01090504021807090b07051e070e040807060605040c0f020c01051e09010203040e011401031d 71
    0x4601010b00c110402d0200302941015828400d54440f803040c1640c420b607840c11100c140c0030701420020860403001380010b6959488098044c4504640d03004640c0510f616000c1d90016151070542c1821800b42010404000c00c80750640b00c0c0680a1115003014400741c038a00c945180c084411043c2512588920352000795640c0c0101010012540700721a00680c00d4850001d030303070402d9000c102c003c064880a448450f0340a40340d10030405044c44841502e40100000f040034030050401b50041141024400040b0300036110103000a50814001c03800c400c002c2a10214880d42d501860130440d80300c1c1040841f205007181966058440358100180365400d507080583c030079085803516501c00a40741d001a03001c8900c641c66450000e070300e0b80c0702e102c0c0130f0300e4107502c0d100c2c103440440c5610700134149a034009445061010510140e010158104d0a200103020400d242c5540d5804240c0140e00c4c600031507002d0710070102050001308220001a1607041c0358542a00c0601811048500a881078054020321411540c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278021447 1250 278020197 278020199
    0x3020102030f0c0c09150102011a09060906061b011d07030213020d0603020d060902091b09060c0f010c0f080a02040312081b03010b090114040b03011505040e1302120601050901 77
    0x1000c0b280050204400410480324810021004160010400c40d01d4655150307142c4144840c9580a01545a0000d40710400d443c040c509000040c075030701e20180006000e12071440005007692182c000f110400089d6221405d811608030a41c14064603542c140740b020103524812000802c540080c814080e04d5004044c0c4004100740803c0c44003d410824500e5201030303e0320340000158139003003c91043e950240e1030109241c042401804826840900880040400c41b40ea12142d2480041510102c2200312000d56442c000000c0345458800c10891040703041d407904403803029454000b140c040a40320b00da02c40549607a40d107120901203000718803001c3c007a0483c491120040e148141549940031040c16421407200c0281088045035030402d8000100714800010f01c1500c542c0c01c61080010b12988210041c80c1c5400e10428031071900040c4100c40a8121681c40d0050250103007040d60060700d81c2a8442e01c83d46032006106240c0c40001c502079000d250b09001e15942c44802080320f074140d030b0018200b20426 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278022697 1250 278021447 278021467
    0x11090a0f06050a0f03060f150f1d040f09150c02070e06010c060e0f0703060b03010b0a030c09090f0602030c1c09030f0f02071d090d050c15130203060403030518070302010203 76
    0x1c20b00d001c1c8075400c02d80d5400000c611910500e1160000d4442307000907100040c00344401030400182503880c201440244003060b0311403a52100c040d205401c3c00d4a0104064466078078100150103603100082c601e035901410715941004039440b518240700d1513421698401e41c0d6030320340741c404501a1404d5000840d00f00001c0c001c506aa00321802e101c441c1400c1b104442520020030741005d0311600f0403521503864181900151400b40111aa0b420342194000d00381780c40c690f2901c031a0112841038101954680c3c039180107100403200d0b46101e8a810a0083d5a6850850624502c42d03100150400c03403030f16143c0341840801540d00c105000790340d040d104c207120b1481508c0292041e1001c05090300840c42a48404913001d041c0c003500d0f085001c00241c40d103a16060840c0254281130951615004200f4184608402c2020000300049500400c4483c9505900c130038210606089402c030000c1c0d0148201c0c0d060004046c2c2c15070015100d034174054494050b88071001b28268903030300c16102c06070041c1d00c18040c880074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278023947 1250 278022697 278022707
    0xf0b0904150914090c01091d0702071707030b010b03010503030d0b040b03010207050c180405060a0c02010f1107060e06070f0818010504030206040c0b090a03150f11090a0f06050a 78
    0x44001014114480341c0da20703820a000d0310034122869202d030f203284091101c054002c0040c241c000109080c0085941e0030201c083e030080250310900b100503004400418920350080c403214002d44005044000703900200320f0301681d90202484101d0701c0c1038100000140b1985908280c0c1c4c11b0f00e03002805185010540101c10014000c010380d02c5602c5583d444800d1200d42c0c00744002e017410b0384603802a0500d850070504011024404030b412402ca402c0200400c0001000443c50581c0710403031b031400003050416418124010001300d00750480f610324221100c080c2885a00c060030b582481803000b48018a842d0700c01d15191325041d03400f4004500540d5040d80141d000b20b480aa00905007000341c07004000383c0d50003d0944505540580258010701c060005002c6511140c4001c1c101e40040c55140214400100e86500000e220152080d150000b0032107040300b1940088100d401c80a00900042604110300f030309a5102c507810303e100e0ba840040c0020004540e0503d501203841a40f41e031b0f828412425001c2c1d034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278025197 1250 278023947 278023961
    0xa0c0902090a0e0a090203060906070818070302130b0316030c090216080403110907092603070b090304090b09041101050f0705070303030b0901090e0607120b0a0801090b010f0b0904 79
    0x40e0145040b0800314501c1128241c80d403041c208108042100455030040c9824050050170782405a0449020003010540080b4200e400010705091506022010603c0d03906205468000030b500c580003035120300800c2c945030003204032404120103480d00c16a0444a41e01c2006207407100030500c600103035040207a02101e81c058480800d00382c2610314444455503620445500a4008072003820483e01c0340192801c3c41e00c0348503442850b0b41482034806040581c1c82c0d60755090701a441d12a080b41e100729842001d014000e40d103006074032483e100618141410301b1921f039013150040b0a01d42d480c0203840a040d00c0d11090040c05607400c076040301d4000c4594001155903521505211800c4a01040007100246003004580001c60295500086000c030b1101003010300300701a80712a122a04000c00124444c5c40824269040641fa0500480100058500304003821410300070a0b8040c4540780300160030742041d000407036000d101381d040c0c0e2002d82c0c0b11018010100114058961441001c0c400d8006a04060380100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278026447 1250 278025197 278025199
    0xa0e0a05060411010504080102070c0e07050c19020607050d0806010806060a0504090209150d090b0f010302100c03090503070e040b180a080d02091c021f0c0f0c0302060c1501080a0c090209 82
    0x191a140d101c440c7c1c0d41c2a0ba100380d0742224040b008440c10040480d0241e20756070020000e1070031a00c2d0038450400c045d90380241e0340782207020503480d01c20242150b50310340445034820391050036a820b0502d07024020749100b40488510780400c1c101c4c400103500c0d140c800b00711000d904194031f500d420a070408940a000f5008015410b400034002c28082e424900d1000c003512400c03600b4600030661040a04e45054070120140011801c1c40350f41340180010795408101013007620b0981b801c0403813180d441c20202c0e00d0420b1507219039014041d04c28041000d102035464548618007403204143e950700c0307000300d01c200719a05584c1444584c000200c406e0000b4148001000e4004e0413600141c03c0014410001c1c40c000e210480c0030300403041c0c500a480860a005003162603040f80615500804a10502d01a2082010303040081c0205112091f1008015080c0f00f4140a990060122070b1908030361300015584400d2240040c0c50504c01400005242500150b485a8254420007003000986010240006034020600007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278027697 1250 278026447 278026457
    0x10e071710020309060a060501050a0c02040527250303020c010c0c0f0b04090c020715230705160806070c06020a0e09091c14041205030c0a0305030a0e0a0506041101 72
    0x100c0c00d003041c0360024600800040010b400a42060801c042c11150b65510a506001d001c1c0600d10000390408260203c030743e0141c41c04a5030344d4540c603904203000329a80081d00c03941c56402942d1554403002400007500c0101d195006040d1400c100c41c1c1086200700c0c031000300184e00c03ca00e800d14951140b416102c0151040303040040035600c8054298603d181070704144008500401d041003a00420f010b81c0c4d240c00704c103001624601e4182450700f2007c205000e0040203101c1003902459564501000c1c0038903204624100359112483c9182081d11200c14948000c0c84904003080030800c00740224242c1d0140e161902c4480300781c05250341d408041d40107289014107000c0024030844850710744a1503d440703000003501401846410b05660341c0340e040c00003000342c2000003a40c0b01410946070766045400b51001145c031400000018a4050720358407030810104d4080c001c40490030101a0000302950160310121001e0001c24045d40c170b03150340d6013016000686654809000f040100b4000b0285280440c0c040c07520b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278028947 1250 278027697 278027713
    0x601050702010c1e0b06010507110f0607060f091704060503040f020f041b0f030213030212010e07090501030b06010c0f020405040204230a05010f180c0201021c021902010e0717 77
    0x800c16001904c0690403255081c00e52201c042000c0c0b000506d51024090820303900b40440c5840c0c5030412941101c00303d02500840c1c00d0b00001740d807600103a070b0303101d5801041404000d03068035009002d401007500444003980c0c082c502c01d486843c803400340d03001c1e68202d503281411940d854407404e800d0a402d900a80e0404a15103100d61552a24010f41c1d40ca01364071148510800f026a00003032900c10103c9006040600c14000095020704c40d00d1074100300c0b83c04644c0746150001407144203004100001c50515548105080040c050b01d590300114101c038041d28540e68941d98590055030540e012510090045044900da00018039107540300d0f641007030010300000b844048003000c2511110240070800a610789400c108001002d541c020349014040342541a007501d454482e183e00080a40c4000028441d03d401132800007520035416907021003100300e000d03800300c0388021900000398400704944500040010581c20b166005014610580180d03100030f0088600d0028040c90080071107401ca1514040d240b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278030197 1250 278028947 278028953
    0x5100b0a050306010e0f030d140d0227030c060706020d0b061c050108010c0504050108041104020a03020a08130206090d11180105030f0d0801060503180703051020030601050702010c 79
    0x102405040503162551540c80c2001030004d41001c80c83c0400e0780c401d056003103244c0c0c3d043d00c010810384d109a0881c20581c1c001450071000301824059401c80e01c5565102190640002d1605006030b4099003040c0074911844a44006264aa074074080e000e03038001008000749400900e055000340800301ca148800254080d00400007002c591201a0f07050108448013200c40243e010707407080c1401000e40d14002c01691404e5030010b001d1740568070603181403060460004090003401d041c04425908000e0085540f2862054050b0007904003004580000f89403100040344035061003071940c0d440703800a08035400c0c0040c40d001c0100e0421551803c80d800c956a00361700141c0e455000d2218490400c100000c2e180350f0602003854a8030400e40100100c644c8040d10002036150000314081c10b4502134039000e84c4d40d0b0340e070550b4440d42d1009030325041140d01c24103400200b030240220324540e80c0702d4600300a04c000c645003415a00e02103840300740c0706111036040000c2000c030340c0200c1c010407480e8810304103120460000e071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278031447 1250 278030197 278030219
    0x20406050f1b0d0e040f14060d03110a03020a2003060606160213050108010c051206270f070807141c060e04050615040c08160203091003020c060702031c0510 69
    0x546040204da40c0a100700000d03d4039005041181c043c4500c00c10007100034501135a51b0303240240c4a10300076031140b40a002414410740b000c441d401841e804039650403c251038002d50b03c84620100ba9902018840d8030300d81500248102d007001c1100800a00450b200c1c0c904120103a8802c800d03032840b010345021984016220fa108000411042e00c000041561520802d6800d49401c0b002034001c002003003261401d174400344891a03404c070b541a2442c0e002c030100340da98018200b1001401d010000444020004243c02840c01c1d103100361210741e5040c6461701e8488069030555840c02e0300c500200400e0161411210701030540130000c8400d0305010500554600c04001144003d0310f0a441c65041a81004200b410000810408200540e010491510f42d0b01c001400c50a02601e00360b0702503610781c51140c115201b0400e0b0b400580002305001e00d10f01602e076010f80250311564400700c03180141000110054004000d98400600e0f1010070511804500106002440d00500055883e01200c03c0440c0c0c1244034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278032697 1250 278031447 278031463
    0x607110d390c0b04031a061306030609030314151216060f02010b0a1404180605070302070506060d02061b0307062d0e07050114070b07090f09020406050f1b 68
    0x80009600d401c01e107410403000c407031640c0d0450308406504100420029000c1c6005070030300302404a40540729240d1400054100e402d155a4001d2a401c202000c01030100325481005424465181003200d00381c0240c00400e00c1e0740486280500c000100d0300c940645c100707c007038005040c0d21801030b5140c0a4011070003241640013a008080021182200e80079010340910609001c00c02c12a095a0040e10308008000e0010850719000c0c055600d0315046009050100540c81c941c95100380705002c00d28201030020001d4114403400d45507440340d00045466824850704138281c264019154a2800100080389818010900c803000700c00d2100700144070100d8100e00c610982d042c0e4190010451204110101c800850b4900180340e4140c5002c4000002400c00155034044510a0820354410500101c011110b40100c0c00007500d80d603010400c1101180c1e0080d03943e420b581e820001d10841a407a8602c80040b401103000e1100420000c00000b480310078058080d10909c02c06205800412001c00d850605007050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278033947 1250 278032697 278032787
    0x7050a0506070f021002040f05010f02010b1305190519051008060106030617030c1e031308010c090b071104051015030507020706020102090f06220303020606030607110d 74
    0x2803016243c824076414040000000070301402075003403504000d41030b100c4002a02c43c003410312040d4030f144a2814001c4d0400385007040002c00c2400400443c41d2240098402120903010360316a0300d0051171030008502c2924000c1c0030040d103041000d05484c00c903900030035002c1c1041142502c2c0306800500400e0811203503018040b1035a0100d800f07881c0c4030546607840740c03400b50a038240d0414840c04401480015080720700c06503a00c00900c025100310303826820740c420360542002040a0394000301d00a6015000b00022100030741d200603d496880c248c00107203005e110b100038816507808141c00d0940c0307080d0b00441e8121003201071b122000c42d507800346414070722a07070114031003c03a444100300840243c043c00000c0040c00c0b54002946414808000114013240c20041140300301c1000c40d20034400301d42e032020102802406001c0c9100582c89007000b0390384003011129207100c1c0c880c0c40c0000b0a800d00c40d903200108003004400401c111040786000350f0360071941c225840480821290308422505600c0c0d03040aa00b04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278035197 1250 278033947 278033957
    0x90c0e0a0e060601090b03072f03042918030c1008090c010807020307060222030312180209160c0516050a0f0303080f07050d05012c010807060507050a050607 69
    0x21661940700c0c01d0100040186050000c12501041210301080c1182e61207419440c010300180780102035102c07000344e9088514641c4054040b01d46440720000010401da4403042c0b607503140d40d07401070320851418041c61080000b00b441400b01752011206032640da07015400c000c00b5030fa04c0c940200d022030341e030070100a0350000007981501400201e880c00e00c52010054428640850945007541010307581e0f100b030400090074554000b921428a00301f80d4031031600002020303103c004107952820000e100144520044013803600d403806500302404906c0101e00420382c00381112406503101e1442000c0401c2140030241070104041c14800016010b012421382e06d920780d084a0f0446080c034050050b21a5141c200c0503004c0303140300061010035000004164050801e0714441840d41d00e845085420340100008400064105400440e400c151881c82d00084250340040c4401d00717991111014403400d080c81360324116045601e007400750790710600003007089a00590882c0d02a40e0385545291030100101d0f86100024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278036447 1250 278035197 278035211
    0x909040819020a05120a031107051f05011206090203030d06080d02070e130209040c17030d0f02070b0c030c040515040305120c07140109090e010b01110a15090c0e0a 72
    0x30304072007910100d8046200605051070607075101666108005580c1e0307000740340400c10f5809503101e0380000035814850303c00192121a5407402507582d611413800140d2901095410600030045803241c40d04071201080c80b0104080d05031034100061280c494242c0c0c05000c1080802c1c0381d100d0700c0c0120801003d889004041d1031038003080c000d007019156003082c081d40f40040c050201450b51040300e12440c0e82c0454800c00c0c0394541e8a4003040b520741591001444256146880c1c048180202c040c1c0000e0b06164018014071011550b40c504901c00d803000140310000c0180425074010641001d540e1207204090603a14103078a41001074020b101004440904400c0082c0a200b048400e01605032179050710a881800c110000000c181c43e115240102c06440000304015102d41e8402c2c920a40145040e040c20450350050f0049039000c0c14420030010301150301801c482c8030310100021280c88a84c2c1050800c503e402030100302c84003400b0304000c01e40d030807000d268001c01c803044028001406004181d200184003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278037697 1250 278036447 278036467
    0x302010e03120d02090a0e0a09030212190f030e19050d0e0a06050703030b100e010206011e0b03090106031202071d040b15030a0b070c0501050c2b0209090408 69
    0x40030000d1894020703000761042c45010400e4400750b40c10380108080150301c0b980c007000403420300461039000b94044000312081c0701c100101a40850100c9002e6402c0e686a41e0110545180501c074881d66803032420456992203952038032603a0042004c003014035000c501e038502d0301d07461707071420010f0080d4040c1b4242514080d000c12800b045150002101070402c041904035100006d0b01e04400c91045032700740b003070000710b03102018440d500c005400c2c40b00400c02c42c0101000c41c40241a0090498581c0c0540300d030740f0002c5016214401c5905001c80e01581c068001801c00030128460381024101011540d2100008070002d0201101004072100135030040220a00e003c0d03002414601d1044605881c855640a10001c01d40144c00298004030110032171854030124401710781b610480500c0a0460340b030380820b11802990000ca41f0803050700400c000d0149171a1604805070500c14074140e460600c21414514500c10b2010007600100348160b4070042c10000c0d220081030305541d08036400c4668841c0081d01e1a50 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278038947 1250 278037697 278037707
    0x703090c060315080c0a0509070221030f06180a09020d0b070810060e030601350309030d0810141909020d1406010f050c0304030c03150b030a030f030908040b030907030201 75
    0x1307080f0800104205252000411008001801b8083c0a40c000c20700040160f0700800c0003440900720600144290079070465003012640007980d0805c0c044002401281c07991411100301c1c01d484481c9070325880d158590b03a0a1000a0001500880c3c00080b01d51404000c5410b080220b031140101e512003202034605581203890a440b00d030050380c280041c040200199480010b4194150345100355040359440200040c40d09105000f42150307010100508080358080b804005050140130030303011990500c20b07001003942c100f00c003103444082403052082c040220703100d82002c0b0741d00d1100140041100d51031032000810034821f9034204800700d54002500c81d8a04400788200c079120030000ca0412110706001000903e4541590050030800001140036085458103008450045900461046034244e503407800302240c55030b01d83c0300e10700030385490444d07041420040f8440143c50b0b1b0666031540e241040390740503001407542c128151003a14041c00f007c9506a03a02c40214000c541010003007101d0f40c41e520004103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278040197 1250 278038947 278038949
    0x20304050c06130b0d1e1a0109030519080702060c010b010e09010608070807030b030f070f050301020403050d1b140606030f011e18081303050c060a0f05030703090c060315 75
    0x201400040000f28100460f803524181500c1c4141d0380d9940c1c4003500c01028020304034080c1d40e84820100b4003403070611a0074a80c0031a40c00e1885012403204070440200548a40c0307510f1101518680094000000d8007145080161040703204001050070a2420380204c1c019401074450038444da03640700e29441440da080b40c4203280075402140c0a00c00b960400c00c00074204030f0050044402c1c0401c2001203845103000341c22814048030003034121142d80210071859030350703030005200714078440d1440707800820107040c18003c4a050326002001400006c541100c00c503000400c0107041d00000306c10100c12000512804a10030420896000822040c200714081504008982c0034500d5260301d0920043d00707080341c010308068841060034001620303586102d8040c4080c0e1910200804282001654161202c0b1680c11a0b060303034010b00888540c803c0460900c005d500c500d40c2a01c02090445809441ca544110b00840c0d00000510f07012401802070381d21210031016071f0b001040425200c08034034a030205030b401d00300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278041447 1250 278040197 278040199
    0xf03071403070e041508030f040905100506090d03050c0d120b032b03020c010c02060117030315040b0d0f060b1806091b0c070603092a09022b020304050c 67
    0x41c41c40c10300c2d00000e012000c030199914011178842c80c0c1410740705549005007005024a4013540c1e65071111401d8294a5441070060020361481d080202c1c140c00d403110066801da800c0601315a25242080c81040501602c280044041001c04c102100d5001e9050081d42002125915044560703074103401004103a60341a4074a90095104241d9a2014900c4400d0104640042003074200b202c403485d10124080d20803003078003251640c00c0021034040700f540010074034121101406850b00922007042119101d00c829541c6010f0312310190b058180030f280a03803140d040041c00920032015034182e0740c1c1d1641c3c5803140f9002558004d03603854101c41942403414600d08002e099082c801c4592401000140c180c0304041c1c072000c85440e60b1780d50710641341502401c80d50080d03002c800721406103699040040113000e58100849400d50440d1020310700c404003d00d0003d0100500440401940c10180d01d9002504074010f248244045007a40581d810345000d50b002d948403c8510150b40c03440c1c94207101d45010b888002e41 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278042697 1250 278041447 278041487
    0x6010e1b22120506070809010e15010e13080f03070c12020601090b0402070b0a09060b0d11031b061603140d0209090906060105070f1b0e10090b0a1a0f0f0307 69
    0xb07030000071408501c00d58003c0c82c5041180703064440c00b548500508108a02001c10301c00c0090b00e1108403011810507040754014400401780fa510034440b1a400b4421550007810b081c8140405c2c109400315401450340040036207003140745030b00365845a0b80a40700d000c003d800560001801800740c0840c90007080c07840d280680701507240c2082c640c0d07002040040205120740c03d0795148401c400b0800950031581000800800b0180400880e0600081c3e9160b9140400d00ca0310031a04403804148180c00d400b102c0c080b009109a00b40b032000d52000e111114040c0c2e08a0810102507070601800b00080c0182102c05000000142c480b010f00c0c092080030711014040070381c2d660101007005000e0b039000c02143c6486610010f80359442c10b05250bc400c140c030300485c2018410b11014000305414082000d5644660f081032403d013203403680c50099100b11180501e9468022000c00014081000c0c0300c44040c0c000746080140510307042300710401c22900c0c7c0003020b003225080c0000090010b032682c880e10b400c140804c01d03281 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278043947 1250 278042697 278042729
    0x4060f052a0f0f0a0611090a031208160f08041b1205070e0105030c01052107030c02190b18120f040e090318040c120e0606012006010e1b22 61
    0x41640d00d009008008054070b4440e065160000001803d87c3c40c44039001e80703100700c01c5032a841c21030031084200c0302c4940002d030b040c0c0024929518800381461214510303202c040c81c0700d90072041119000d4000b0b0040d9040360303a1039011911308242c02000d40c003d05005040301642d90103844c000b824401c06522040c0c90070030f424011310a41e5008200e01d43e140e07a003401c4c03860780e90080c0c0c0352010380607407010910082c00c42c0c050301300407040780c0580000311100e02c0c40d4241c452340d8840058202511201c92809044005231200284034a4005110160003207642002c603840075000c01c0507030110780d12100d0691074044000c43d04200f00143c2d004482e030402a504091800e140722010003071011030840711214801d645407444621214000d18040000c14034042d4240100303002203012a85c0c0d82001e0b50154001955100307204c02c2c0038100c42301c1c3c101484c07145000d0609a480c0070350005040ba805000ca8030008000400c80d4400d0380303000000c00b2030880940520011301c00c664694040843c081c0d010350741c20f03044100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278045197 1250 278043947 278043973
    0x1030b100b070c0501110a050a0305030601030b1806040e0709060b070209010b16020f0a052d0a0e04060e120703030507090501030612031805060f04050f040e0304060f052a0f 76
    0xa05001510020300e45406006d030041401890b0044005016249015044800c03061560000046100301400c0c0c130103004030302c482018020854403580000c8a11101c450200d80c0f94a000d8001150205501c408c8848250b142c003141e404030f500c10741c010f6180080015601085080106107140140300b038120b0b0300d09100100c02d2503425140c00c20b44c0203110f125141040c0c400c964803030b54170402030034000e0075009402c800341502c0b00100c2c0060314048215200926980424601300c048001a00e41c0e0a4052040c3c2e1100c0d0f880c800070b01000001c3c04d40c14003a42c0094440d083c042005410118000d640118190801d4480a0010082900401e0403d810501c051024180c044c0844043c10f9052414140d001e5060b090307210740c14180c1d04951317840007001600c5085e01151401078020f4980c00c4a007091006103440400c0b04071a2598155020307500240000c10115000b1801000807015500701189046850049501c0e03480c3c003e05440681e0307030314a030b4032610904204690b5145d100120018910f01c12105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278046447 1250 278045197 278045213
    0x120030421030c0b0a060f08011d010209031005060301061d070e01020606100804050c03030a02010209031c08160908010f0c020118021f090902161a01050f0d0f02030601030b100b07 79
    0x10002620001404d00401c1898619a100300300078001007501c020b800340c40d0440c940c081c1c0018191a04811001d01940100000610864050400040041920507c0210321001a00700101680d501d550b0b07d002c0042c403201c40001003188010302d218250807910b000c0d0005014201e5521515045601000400100d0740b51841c10f01c468109909003654180d480c3d1401501d0640e180482035014000030400d01821501500a0501013004034150384204c01c071120701138500103100b5102d00024640502003880002d0071090111100c00d107242c1041d104d40ca49010300d00751941100302c0180e580d545c00130301104640c203101e00880c08aa420102c82c4826081c0c0002d10280c44402c0340f40c0340348030b8803100041498010a0030200410b0704440c15922110142c0b011240101e9402c1c00b5590701502020180c0848520800070341610401054032100b00c1b004000d1000c0f110381941f00706c8043c40e06002070400350b9070030080d0354025881005c02079030925081d00301c0c0c415026150321a540c4104184500c00000303032a5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278047697 1250 278046447 278046467
    0xb0f0403030e03010207020315160201020c120c100501030c0e0f06011e09080f0105040b0105010207150807030207060212090c190509060d02060a052802030306040506012003042103 79
    0x10318003425a011a000024028403840d90020b5041c42703426103c010400d0b07440221842008132201c4040440c151040681c00e0780b00d04030107901c00c1e0700103149280351034000b03001400c2041040d900f00c8581d8203542644400f120710a0b00183e0f0000c03422101000001c0303400980c590300c10180240c2c643d07581007490000c1c201c1e02d01025a003e140c44070000301023446100e42407010003040303034408440e10040d150204500805040d5000c0e241c1070402400480e00307500001300f50007203d102030480c1d69039501d4002d0480e40c4d104054411300406400f0010b03100800d019001400080c10713003e030040b440f810000c0c007086c5413071181d0b00054050b00c91040c18455940001000000b198010f65401c1c80c942c2c1c03007100260090900c0f0a00070341c0f0201c08038580f0f8140c2d030300c40040d1214100300d00300000c0340e0080c08500c0c092101d481445c0c0005070300401c005407541c00c2caa001140c1102c0107041c00d841012000c0114500d020001860010940c00420204900b0b103551b00390410a01340140352040200294a008104e1000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278048947 1250 278047697 278047703
    0x1101050f090d020f030d0519030506060d020c010609060b091815090a0f02030c0d0b01090e040312150603020c1501050603070c030c1e0311150a0e010f0906020a08010b0f0403 76
    0x42d1184603400e40d00e98098050b02e500005055925000d01010050710300e400c05400000800f403d00c20710307004640030b407040030f0290100038a490b0401c02c84080c40006580a11b541602c25500e81500241c00360f5075000d02e80c0500401c0e2003c44c1c540d15441c050107001d401c5d210304144802a25030500c003140c1181e1301d10485124040d101003240350740341c00014000c1d210328440381810f81d100104010f0840103003000f50640c88201c3c0741c1406442e01c040700440e0122114001c0440151944021400083c0a81c01c4002c045642c0e010106008a540c6500311402c0c00941c01100465000101100c00603000d110755652a03402c40d00c0500b10354104000b284150000030f1400c0c00b40040882c080082c14040e58040c00c9a80d4441416240d9900341400d546070003981c82c0007140070a0070403c4105c1c60000c0800e0b2800b50400512421006907a14980700001d41960340c241c14995590b0308480366485814019401d1541c0552405a590f103407004000b044420141d00c04250344c04113008681148060204880459030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278050197 1250 278048947 278048959
    0x301110301153209090a05011706010302010206070324081b030a1205130915030209070809100b0a03060f0e1e060103060906020f0304050d03110a090509100e090a1101050f09 76
    0x1904843c980c14407404400d81e07403191001041003010030300780d000b540c1690b40c0684a1080d1000049a10366603400c00e02000b130258101c1d50020f08143e02c07a5000b00c520100da0460072278030500c4c4844256a1800c5070b00300078a00d0b00018020700380161444c81c074650161003a0018242001c60f921010203524504011104020000a40740203040940782c1f1a40680200441001034514000124540404030f1104a00800081d8002607071580600341d514820348a80d000380080000c01e54040000707240446d81d0340d5021154041c08008288a40705119100742154400600c464143c40d50034034040c03200e00c861607020b0021310360740c01d43c1c0004207542e81160340c00310300170400c0e80307080c03803d24040d01405054010b07a1078040200014081c00041880f80c032900e5440030021229803404282052040915007008074a6240040280342001114168400300e40e00013002d040b504c0380c2c000f00d0b8082c03095a0503805039108180c084140030703244141408141090038100c1c40d2104902095085000c0d00b10000d06c211 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278051447 1250 278050197 278050277
    0x110c010908100e0705031e0d032304062c011805100c05090d080a030b0402030c070b090c2d220513050304060504090b040b0609090a020702030111030115 67
    0x1010030440c00c4c0140c14028182c8600c2c074802a0079100403030703550361a22403d01c110306440d0b07005806445803c00001c0d1440d10484e0340300d903400c058010808050800c84004d0b42c1c503440902c01c040d4101c56031003400c2e443ca0f0100c076010348400c462420358800d440032440e004510200301c400900005100e82c1d1006900c500400c0c0703040d2015064850b0700400441e82c0d0410b5000c10344400700140722006090035016500e04100000800302408100d0100f15401200140e0402c51031005c0750406404a41c030130750041c01c42e0345115150022600c3c0019070000e5070000b40704880741c50942c00e12000c18019194054a07403600504d05c41540440b01d035000b8203402c00e22651400880c15088a000c0c82c421440d0300107044a40c0e4070307138621009040394001c1c811280179501d8140d180e071039880c040c02040141440108007604082c0e84c90204600020040c006c0ba40240d400c01c0380d0030042e20203009000343c44907204200380c4c0b01d42c507281e9100c0c905401d0b25030314400c000102080c58440301c0d0241464a9400d00c0c6500038900e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278052697 1250 278051447 278051471
    0xa0c02031210120f0308090a0309300b190908032205070602030408071a0315061209010606120504050a080c031c06060905060403050712020402090907110c01090810 72
    0x4142d09410442c00d240b5001080300c10700c21008141c07410b541c80b0707a0780c0103603650b106015551146240300700100046c020355010000c0c050a1401003200d140309011095100c0f8a01503108111a40060100c802000c0300c0200200d811a590116034850035540c8144502300c0581e841d01550301c8010500c0c6401c050004003816190105541c00c10f81603480f030b080701e0b403850b181c010203950b07504688600001392150315400b0030183c101c64603c3d00c06001c1000440c0c2942c5680120100c4900e2099000742c20070428000341004584443d015401400480e0000503482c0c185940105041c440e0700d51180480e05200900c40000d5001440c40c083c2c940101000d0f0b00c45640d00310039425481003201403400c3c510b610315036094980d40c5a119500312903d549030780c840d40d9681c1003030000d14007451201400d2600316942c108421801c459207441c00a00c01400180341c0045080007580258082e1200800503150b0402140000300c200458040d491007400c1140101d4a01090070760b032480007034240030415896a82c07013011 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278053947 1250 278052697 278052721
    0xe0f0c0f0d09050a02241e0c10050601080705070506040b04061b0305090d110706030209130204140909071404020d0f062c0105090403031d070902120a0c020312 70
    0x2041d080864240302414050038200d6841e0100310040c3d00c01d90704660001078204c424884000d214002414903420105040401c84030100052503440c1100800c009552001c0003e2064461030b039a4640001480e04000000500b44e4900904c3d090a200c0304014260110b42c0008540d58080c0c2e02c807130440d0140d90307180707081d401402603030360260048191610103100c00c640607003120744640450b5085815001c06d050342140d110f0740c1544030f5140d541040da8140200e44c4690000d103003541c1d01030f08010010441103c088201c0c0d10650210620017841c0044051914010f03000580020020000703100042c1000c5500980300110301c040c61280da40041c100d00141a50381000c00c002a10010030452a07540d55030f4941c0030301000b880304c4202d1282c064010800105088814141d0700d005d0100aa6030740d07299010b500400024840000c2c1d40f1400d82642c0322410704110090103024819405620368800c101c1c800c00070034004c0c1054840c503007050801441309600100b0b5032800b102c003103110a42601c9040031441 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278055197 1250 278053947 278053957
    0x3150b012001090803090a060b0d02090f18060a020a031d030301090c1b030c020907030207030c02060307180b0c010b04050105060d1508030409050f01080c010903061e020318070e0f0c0f 81
    0x8084030202c01c01c803601300041240d403802c40c0980800d114108003001002b4444403c401c0096100c0c48203004100320010b2580c166030710128003100074908000c01100c0a107071403801c440e034004264001503214441c43e03060081003282000500f4001164035800305903501c03800305001d03101400d41d40c1c4e240c941c1d21601c104400c00751000703005c078400e0580c0b600d070a00600380c140c445801c0c1e009480e1480441d81d00d510070301c01c4070704054140c0da81e02083e032116801c01007150700180c045820442841d00f14010080344842c8540104100c1d00d44980d01c0341d86a81013400e50f00e40b080c00ba80f0886c500001000642c0300c4204071403c55040520024030b580c0700c16058488040f21380c010940340d11000c01c000c03a200d0211740c4001e020341d07451000480c2c5aa83d9940a40d6107000120016000070a9058100005019504502245500c05087c04078850307c4c1c101c0301c001c9030021100e0f1210241c0c0d07000d611001c8082030005401030705003410003034040c1c84c0100342da42c480d42020700140c01001002031804060088401518 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278056447 1250 278055197 278055203
    0x306030703061121071413060516080a0c1b08060105040209010323010303031b050a032703020606040606080c1b19080306040b01030203131103150f0103150b01200109 73
    0x280308490307004181480213411620304002c11124410701d2500c15018090700c092070b041a00d10428281040c408442c0c0d80c12000d21520b0152140c250320b400101c1c000003408a40340e950355030510000040c146024084910000040080311441050103c1500403c0132415280291000360342d8101e100c00480040424001c05502c200d40415070032500065824030b02e0489029039000d00801035803d101100050082c1c003440b01040c820002c0d20034050083e0000b07411110401003603907210801c8007001e01461415030302100140c000c4402c20480d0300d040e110b414080c003030910b403aa00c68a09001d050303e20b032007540d4003440c101d000195034450008080102d02040400c0440d0384413801030510b880c0c0081e4005881c124813503828400c4000155102c0d10030b49106640192001a41d0071054580d00312801001498a81502900c01c00707480041160fa14140107401e2000b10030b00d00c2d0b145041455642c0d810154041145040545120450f81e1141c0013450003c41c00e20305c4c82c9a018000c180a0041101075002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278057553 1106 278056447 278056477
    0x10e0108010b2d03070602010c12050112020909030d0609050405010f0c05030105060c07092a090e0a0c050c0601060e0a0501020601050904080f04030b2a03060307030611 74
    0x5061404043d140c4002c40000103020a040281d00e03005100540e4455103850840c1c0d41c8403800d010908200101044154100840314440080f0072030b0103071040c0c260b640070130084d0b0818401c481c885d9014550800045649000da48081d09080b68151042d51030188440f1032401203019495440000356151131540e804c1c6010010a904a10b200c120b140c03041140100c0c466101d80700b0442c1c0b046e018001c0a6081348000840c04540c1d0100c503e1804202c2c00383e00400c1140c45403040c054105094540c0490301081c010f90844850246110603070841c400d80000166180d00403d812a402c2e030203603510440ca9840d01c005a07694042844bc880e0804000d80010340407e00c0e10010b0410040b01001c074618090303407038545540394101940d411014a0482e140c01d0351007100d030112105114500200c0c1419464138800182d1030b11941e200c041d00701e640300e1710f10640c0c040800c4100c2c0c40f44000d00c202 = true := by decide +kernel

theorem cover : BRFrame.Cov 277877697 278057553 := by
  have h0 := BRFrame.cov_init 277877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 277877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 277877697 ≤ n) (h2 : n < 278057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
