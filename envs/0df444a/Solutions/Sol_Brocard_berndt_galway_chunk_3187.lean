-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3187
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:55:30.40448+00:00
-- url     : https://prove2.me/submissions/01d6eb45-10d4-4268-ac11-0cf4058e365a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573021582 ≤ n < 573201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573022832 1250 573021582 573021593
    0x501080907090f060f080118030302180a030503091f1b060b06070c3807060b03030307080402041103041214090a172509020c010f05010303170a020a121a0607 69
    0x240c3c00d4400003a01c0c643c2e03146d503c20019003210152034850580d01c000403203140010344030b500103240c0e450705010100304104042d40040c1c1003090580c03040b04c0c140d0000440300418104840400c0c02c0541020744418041d000c0d03c0082c14038900000440d103001c040030407030780070410346600c40800c0c02c02c05090692551714502d410b05010311140a480c41060722454148440b580c040d61a035003440121801e002e80d07000059200060342c010034000c0702d400f5201c00980700301e81c608001940c813480807603079015907500740390051008587c4842d80c1e06403809d9080080001107180f800f001140107642d031130309140041200b03000d0071040c0244050264000d0301c0c1100040ca10b00281c0000f0456007001c2d007920b0078010348181c2c1310400c08008040705070000819a041082000720340c080c00c074206000b0000f10b0010441c40c1081c0864400360421030104071180001c481c0443d80b071040d15800b00220400f185024564000941b041140030341904a0b2600c80b144508070134000c40d085202a40040c0195458402c0d030303e041c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573024082 1250 573022832 573022841
    0xf050405060901050919030e040e0a03051308030a0509062107020102040807050415060c0309030b180d03050705030a1104090e070501081612091b06051801030203010305070501080907090f 82
    0x110b0107542c00c22001c10520000800c0440b41c14461003c031502c00c000350b60f0103039030385001c845100344d02035514900d0704030390ba00520402051a10a9889a0303a1301c031040c403610030710181c0d80c0000f42d85038030511411071020303000022107034003403000c880007031310b440070b40060010301c60001401c007211001420900201c10b4054010b0000c2d10414030a0780d10780d42d200c0b01417004803000f010900499101503441042101e00461900e0705a50103032a04140003500c0361942001080260749810345998582034054180c0740074000c0c560211f00601e00ae0103103003000d050080850101901390058140d40d01145026080030004682c000c1c90740c03490078840c0d10703121960151115801d02c101400703e03c04000054482a16050704110091680c442c1c80d51030f60901c400b54024100c825003210b0021140c00500d40c0d17409200b4000c00200125521207a4070891410452a954000d440c21070600d4010700040c00011030209803181070b17500038070f4421442e50b14031540701c0c07074001554802c291181c46c006031003040796407a401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573025332 1250 573024082 573024091
    0x18060402011d03030c120d06080109020f0108040525060908010207111507050f0c1005030108030a12020904020d050105031b030a140a0b01090606090608040b0f0907150e0f040216060f0f05040506 85
    0x7d04102c0a6520038540e401d0302c2031948001d5101c003414a42404941c0a41d02c0150054001c1040f03955001380c020400301d14011950401d411702500c18002c00c112940080a100644481070085d8103104c0107588004a00c030482a46602c100c91138101e21280d0800c01056038a40e5800101b1a2a201d11042616480d82400304142e401190300800071003171507015508a0313041320075000c021480d0240042045940e03241d0303c0c49810210380c0809c80b441d019600d80c00504203101d5803e00002d02540b4010803d8549a200e0803040c20680b01e01150080c43e9601080c01603a076a0032032034250084020300d0306241861325881c801030400c01514004500300301d840c0c0c000c03425501c1d01e403100920140caa08058a0720a0221002458040c940d40010101d0580c0c1d499960445829000c950019898510320058100c0300c04c42c4030000383c06504030031414030385000d0041480100343c504520b050050320020100805511010300100e8895040f400c01e9190740c1e00692035983e02d094204040e00f0586081c40d1201d2041c0c1307 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573026582 1250 573025332 573025357
    0x5030d0f02030406180b1303020c1f020106081212060d0c0b191e0309020307030203241e061908011107030e0102061015050d05010b0318060402011d03030c12 69
    0x6584103c0c00c90405c002991903a00310b042c000d030540c0e03000144040e00d00c00e09012400c50003991042981a00c404003000170611135000040120703980114020300710303010b5a104030507070b6011207034510350308014004407203c03040c01c0e51640443c0c0d41c036034000c507540d40740700d80005006490b98980003505c1c002c07080280014100e181e000070700036420000100d59032007a50b9010451103d42c90100902c050196006e52100343c40a01901c900b10794a800003400d24800130510145552411000070b80c003200f843c02c0342d510001241108181e05204144842d400400409050080250a100126403101c1d480a44010048140288010004215080042c1c0c22450088002c00c00318040d002441d800070030007901c1084644181c010043c0b80c400140801402092030742c0510904009032100241c50380a43d03406003200500d003036070724200300d094059204101d81c0e0408140c0c01203818000140e0703005500301e4440a40314008011101d121000a00b103208100e10410284500500348050031581d1003e05099044d00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573027832 1250 573026582 573026591
    0xb0c06070504030206040b0a12050f010512030c0304030b190e031c050402030a060b0103020f07051c050c1002070827040509010605011407030302121e01061106070c05030d0f02030406 80
    0x140c09031094080d5010095000c0000d01c0144079881c0e0881c05030601c05502c1c034006c0c2d0070411a130210303001c440c001e0354519000144070005202ca4105110042d50310201c41009510f00000b0000c2a6264043c900004005030b00003000304a10014121003481d40c101010000c020404a201d01143e036035104440058207812950061038110b242881906c0c03040313401501407d11400d807560b82400801c0d00500e954141a030900c0380b1074a00410741c016200c4284600000d00400d404604a0181c40c031b04900840708002e000c10940b20302190215660742004e1400740056107452007460403004c18000c0305e08034402d5000c1d819078040380699040700100c20103030603902002030343c44480d2030a0a0750800d004e190b01207000800c0d40883c8407182801000402e0083c40c0050030034000309039080d0510015a80100b031240303010340c1c08000d103040da0705241c018007031424140300d41001b01e4401d645600d001483d900071303c2a080021000d10806000311400034400c15810480c448560b05040300035082601d055a540b03180 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573029082 1250 573027832 573027841
    0x40b030d091505210a021b03030a05090c0a0905070e130c0801080712031b0c0608010305010507030203010e010509100306050a020d1b052505030d0b0117060a05010c030e0a0b0c06 78
    0x3002100c5120614a680110381c2064a10426039144d01030000100d01da803c02c01107465011144048075081c0b103070005581c2e06d0070400304d03103001c1d80c2c0081d2454270307a0b40040070841200ea44078a804801c40c2e000c07a8010034036598464056511188620741c16810554244014400880316804041d21703100d26203480c07050740d80300c031101a624141406003c0060f10002000c0c0086402450802d11155090466805800103a520114440001e5018101241c0800018802c00500707024655102e1098503046056601d0308000d144d4164042c0f081340c1c000c0d0044070200d641c000154140d4000303036400840030320140c2801800b0308020340c8105060040300e45080c01d8001c1103158a10042c0c501c49060b5034550400103a0a8603072445100b10040c1450750a1410f0800c0000307030184090000d40540410000d240003104002603c942c500a07400100106141d08212159503003c8040e0b05450b401c0c40d05000405003481c06440e4109601c082c0d0307030700031240400040e0101103180180750b441003000c1952940e886 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573030332 1250 573029082 573029087
    0xa0816052701270b0f0702040e0d080a020306030c011b050a050d0210061401030506010c0606030f06060b09090f0a0204050a08060108070806071d130203040f02040c090612050402040b030d0915 84
    0x819a180d85021518080304010080034000540034000350340340170611b40a15540010201d600a83c0040d2041e00003441190742a03800148503036020014103010742c51072900000003501d444102c040d00d41480044000c08105e0b03041c100704010700b1a801002c0303840354079183c2400c030754840400b0f85c400014455590800d0a1840368001c903002c84401c1381c8100000c1c0c0122005401924004100a040061510b010342c00b141060040c04000d5001d511005680c04850038120305481c52a0401c1c15400410040003800e6250901075a90051403101400003a4554025841c040d210ba0340c4480e81c00143c1c40c0c40030900c1c600100ea1241285e11050403074208907914500c5030b84505e4210785080121f0800020b003212a06050003500d072540d001003510011142a00c2c0c500c0403030300306480503521070340e4002290701103041a20540b41d0f80059414100c1c505880c1c031800404282c000c0c2a4050059281c0000c1021902c4942086940881c000d007583d1003071814441c000c0a42010b881a80c030450341d41060030722420b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573031582 1250 573030332 573030377
    0x81021051c1d01020c0904060605090105040c0c0f06111818040507121b0e06011701140409061b110106140127090507020f0c03030a0816052701 63
    0x101c0d548409090342c50110602503100c0300402102d065010f88401020300b5610084203a2282d480b07084000745c40d500300801d00c07100c100d058000c82e000714544203d00860726080340c4c41032401580304800201000492521801030088038140c020f0071800403452a000d0000d10424215484080c1c1e0402c84081c0269004901c40f1030039503004d091900b010340107005042003d010300d00c049025503255001d050024407132044000d80c0380d010006270300161052095640e17028019002095080040710460350410701008400000c80a0701880749954016075030401815030420a200d42072154070480c0a03040b00000740c43d00e6901c141c2d1000651802d0004100b420031601002c1324848181d5582c000001c041c0380444030300360b20480340084101c0701d0400284000703003805440e01c103840030b501414501c0d0000940c41e281c00b91034240d09100741c00c20300c00c1889481d80102403640c04080d0000028146204074810b44480c8034624a001c84e40000c0100c549020b55a0324041c05140020b99416002000c280071001c0c510 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573032832 1250 573031582 573031633
    0x5070b160e0a1d2a0d0e0d0305151e100c02060706200403030e01080a020723280305160f061a0303070201080c0c1509010c20070608102105 61
    0x28004030040410820100a40011002158000740b91182c200c090361402604140040000e509c441c2003141130360081c0d48510030341409440c0703540010110244000004500904640110200801090380510846414441c290040c00282e0f1352103603810054060000190b682c2495201c4040101039007200300c084034120f136003641d075074500c440c03003079004460080f80600250340b40d076024003914020402101c96561403402200d8a54a031155000e001d5080c01d022051203519201010f030740c107000304544c40c0a5150340d541450101d81e00c0c410418000c4081c0380541c80585a40100841042080749580c03025602c0d520b022203402403410700404040e0f480c8159034000303000134021008265204881d07400b4020b222031200644800380c1c1815565203804200f01d400c010301d607440306265602d05410141d1242c40d412031001600354503001080031561101140720f41802c0003035110010300000401d40000000d0a280b5507a2510b8141c104441c21184843e20802ea505004407441050001200032000303600 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573034082 1250 573032832 573032881
    0x18070b07120804060b04150905090a020f1c12050c070b07032f010e0c10030603020303040b03040c0b1b07300f14060a05010605070b160e0a1d 62
    0x411001c4400300c8614001a0085900c1d80c2c4494214140c0d81d158003803070280403c0d085160080520388840b440907070344044e05054041d001804d0610150300c1d40d80c10624428000d45080c01002801504c1d0b1b1201c00d501140a840351102d141d2480081d80d0003030041901142c80c0084400d116140c0058403d60b128451000380410710803485400d207295620104080d8012130b03c1424840300002c2601c034251107640f00183c126411000454001e480c0103000e05000c0c0f01d65141c1040400d042d0303800301e50740e8490b030b0148041344803020000500700300ca032501040191002c03020300e0f500e604841010b0b081800282c0008130450090310404a0843c10f241103c0c41804d5003184c10203105200700c1081d001d40c900740c9074140c603c00014550800868010030311030b1043d021240041c2501c0c640601500c08981040e040344003040010040600407440c2310245030b4214a69030300b0340d01c09021805082d2440c0c601250059000006410002481038011141010000b94140b00c4480381d680c1442ca4440d4010800743d0229 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573035332 1250 573034082 573034103
    0x11a040b1801020f030315011704020a031407030203070b040509070e01080c1308032a1903050a110703030201051b0c03040308090a1806050120070603050c070b18070b07 74
    0x40c0078074031000c0c1d940680c90600564009007030f03581d402030459001f11551543d00140d0300781c50303416580c40700d1020b0f42064030115444071070500b50f001400307405080c070015080203542c42c00058203042c2801000c00543c0d00504880c22507694003054103482d041072113090310498182001400c00c3e8000c02103180542016521003140d590340ca060303040c07150000304000d80c540c000e242c000304d50f07800e0800003060700620301000010007440e04241d0395258032450010004a4108180d0004c40400e4819000304640d403608060343c60300c1c00c1031000c82e10b07000380201d842000d104540d00003060613010b500980c083c0c0d4540e440c0548006040e0f030060031500c5025400d402541c410441080401c828001800032450000c1690849942c3e600d5101000c600390039501c4e00c220b6558400700015030b0043e20700071462144045411000266600d400c0d1681c59030b1050105050711139000031214001442260301c01517004042c0315103810310b0320640c2c0c00031045480e1a0b23050310486c0804100001c1d000c00b80c8a103164070101028 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573036582 1250 573035332 573035347
    0x4050723210c07050c1c2405071e18051516030f020c040506061801030e03070501050f01063209040e060403121506030b0d06020c06011a040b 62
    0x400c154040d01d461244040e00e108032078681e194068055000d502251500c0c1d07101d402d2401c1c641d007444c00b80017000f0302c80c0341e91481e0822568185d180e4003000903007281c9041aa078248400441d90b024031003a2800410780f4000070440c0e20754005c0594186110072002c10100040810f4003a204246550003500c0807100d844020030180c506428003103043e190020480703040c03000d080e42c0c0d05132402052070101e0210303029440a002007a810018042074a10445081c4620705000002c24118410946001d003c40d0030281201d00c036901079040392202070510001c807a506d2140d810118020135041c2d40c40320240100c4c40000400600c00c4400c4002d00d0701004d44d442d5400c00c5030032807405903142c0030141502c001c02400180c945545070311500e2150015800a000903107098540208481d031400500d89016240862404074281c820f170308681070b2250f40c14001741101495001610003081d02c04010710f107070700000392041c9990000c1149812074403545d90003017418020030740f07540d0540608c1c01000601c4a0510090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573037832 1250 573036582 573036647
    0x6050418020702270c0405061b33010e06010e01050d150906150c031b1509060c1d1f050c060103080928120c0e01060e040507 55
    0x40348800000d80010310700754142c1e02103080940d4203480310700c1c41040e5688014008640292030b640c40315614541c946042e007450001840e030301403500c1c086081c02c2c01c1d1070400007011040111045054140d1514802c10443c50048069140402d110090504c0000000500750465682c20b03406108141c45800080c0d11107401124540c00914200385c1d50b0f91500e000114402c0c5800811028014900d4041491414402c0c001e14841c030f540c411900300120924028007096012504001a500003558114102c40324104680d5800b0040700c00e01d840d0b450501401d00b00000d543c4420502c00c82a1a010203040580c54006982036040807481e821079190f5000180802080c601c10350b05020604015040a1310050400d1402901b41c200b12540e000000d122900d80c98500400c50110444182034402c0610800c1c00c0da801c1c03112407107083c00c2c030140701041400700075001008101410788900c81c00d00640e0354040040040150348601030046141c500401c1d030803880f52101560700400c2c100d05051481541585 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573039082 1250 573037832 573037859
    0x1106010f051216031101080114090f1b0d02090909151f030b0405060f0c07080403080912030a0302030105090a0504080909040213020403030309121110090609080415090b04060504 78
    0x1030312094080c0302c000101c1038003c54500030156008071000c900000ca090005044600b060304080705003680c81c286208169601e8903c2c40d4000040d4102801d241c982c10359207504141804269124408041195200411590702030181e400f81101c0302d844903241d555580b5216078140807854030801040001544010346c1e45c80213840205415068075225a480d1142403201d0400c3c0d400721407030381242c42400240b1003440e06441d0480d1030100c00310300d800c620303940b403411904c641e103c01000500040780045d06503540a001d600e082800c0000c0e0ba503250720994005000354424004c0d28401e0391004046070349007400d4868944034a070300c54012303881d010840c01003113103003c1d0083c0100d920005961030351105001e03d00142c0001e51103510007203034407178142c40c2490804009080b188200203141c85000f00d0036000203a00c0005062982d4001400000f41c24044041e10741103102510140380090300085101407009016130b0541c50f0f55a803064151907074107040305403180e40b090b5400904240030606c0300d0301c41c0d00719 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573040332 1250 573039082 573039109
    0x1061706041103120a0c020406140d02011b0f15050702010c0f05031005041805070b03061c0813030803090c0a0f050f0d0215030106170106170402060c0105161106010f05 74
    0x480b48842040c40d034a11151780b00341070b101d001840e03e01c1c40c181181410302900e005860303440141954000c2403c046040e01540080186c100316507480103200601c000f640c407180d2150010500d1010000d1030408000d540e12070301c402c41c2c03078519000008a078580706100c2d01522000c655915090a03469030b03400c44540e0405040103000d5070801c01d002406643c0c0d8800d01d00511200c80c1e41d5400b00b001030420b181030603030702c2d4050300102e68204100503580e980c0300c91003228900d0b0245e00c0281240c15049c089440e002e80c0c580d964603c007181e41e0120a008410000d10310460940c01210004a640c20601001500a106150480340105010f1040b880d00c0000069140000751411090456a030000f69001582c00c41603083d5510000041c044a070b03103e0030a460030303200c1c2030b0414641e500d0244000c1443d103031030341c2d0040032900074004201195144001c503014441042c009002c03e0504500303a4560f210714001050218030f1410b04060b0355140415114100c032082110b02d1450352400c0c06004e030340300301e120 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573041582 1250 573040332 573040339
    0x5030a050c0909012603130b0309100507050403120c050d03050a0e0709050a0605010c0506010504200d0c08060114032d07051804090819030f06120203010617060411 72
    0x8142c030300b180c941415250007050b52003040c408011142058404a00e031100089400c5c1d001040603190101e030551000c0c08a411440303030599207075540300c0390505240c14400409001c900780014810115031140250064030b0003010641441c200d440d00c1502c089481c0c1100906540100c0c0e030b101d540d00d019a01840d070100003031a001c5001003507030380c42c581859219004041c080341c1e6072081c040c10b0400741c170454000d48803e0030640050354091b01d0780c0b0303a51941445a0352050342c458400002c044203002c00444076041200b09076458032440710b030190290144450f0140054003110014600798861a5483c0c41000105000c0f0318503222800e0000551001000130005200b200503c40c0c100070400c11140e01c2540b842da01d150700c500e103000840d002d007014440d20610440c1002c000d040410629000c45142100c90442518400c166240a401810258072134085075440d003000000c0780e1074135003040616544200c1c000c101d82a01c505444184100ca00701d51903c03940320100280c0002ea850740c15001052009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573042832 1250 573041582 573041587
    0x4080c09190c09050d03120b01020303060307030807020a05040212240105071119031a060316151106010611060a050906060d05030409050c0405040e01111c0e01050a1410030305030a050c 81
    0x303c0210b4040405c8440450011301560038015a4504500c545c8000075001d2024501e141000784c00070303680c0c165034000901a0f078000100e40f401c56440c0c2d040a4000d0001400542d01d99000e0640c1c0c4d48080403c40f11880e4280000051034440c412020403503900300e20584406091403070381c2c0c8506c100c0340b0860302019048182c41d4130070b00c02c1c0d8500c0040c0d40000d5104001001507036207090140c1c000c4081c05040d49001c0c0e070280c007501405c0d11807003009800344c900c4005c0402c1020071444d811100c0208901526071381d4000c40001040d01680300a503000300c0d44d14401292090784800ea0f00c2d2003214402c4842c00035507080130021600c90328042c900c1c041818040e000b2203082948450400040b11015074079031154880c002020002418180100441c013188400204440c00c40c0c02c0c1419424800c0042c2590b22000308410f0640000d0540d0000701c41c407000c440200018030b00305049000800150701c80e00481064034000071800351500f050202542e6040d80e460b41140c807100d5a510281c08050402c203a2803405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573044082 1250 573042832 573042839
    0xb1302130209040216140d02030c070b180a030c090b0609060703140705010212041a070e1201060b070507030605010e01150e060c0f0706120c080105100201020c1204080c09190c09 78
    0x403400704103149004203003c031b4008a40c80c04041c6050110703c440029034000f400420001c43d00403600c0000c840e8542d51190340d44151100e40d00409900740002076001c1100000401484140c0c0401070540b04404410840303108a4400c20515008a440681d4028001c10460700020722501210140d00d4002c242d40d0b0800d0015511942640c02c03104190403648100c41c1004240060641034044e150305248807110070b170510030360040c002010700d280345010320035442e03250360b140900f544110010a003001d0010740794140c618199071140000d10069841504113400400d2148080310f14504031101c1d004900c00b0890031030001d403404c03c070540b0201d0340410240a074001d40041403012415807840c1030050f020705814480058101584000c440311020b2400c649400010340003500c0c581514005c513092403465040d01000c90280c4620070f05460302d8061401413250604aa2002e03006a50b40e5000740d40c0340b42c50031030a100c0f100b4000c81b0300548901344000060010880e55100d405804050b10f00001c3d060384 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573045332 1250 573044082 573044107
    0x6051906030503180a03140d080105011b0f17040e01090e0c060d2a020a02040f1b0503180111071e082d0c0a060f05010f0314030c010f090b13021302090402 68
    0xa40d84021440d0022403072101c1e03d42d4270429440c0035260908050b04c00520710400007a449121040080001c0c4011540e202409401c51a103854000b2605030a99256100e449260b104902031190002483c10041c00000200002c640c03084903013000f8061508101e2080000130140c0601c8030301c60b100b215104068009044c07904d413000519000750f0020400f506051041c0402c8604244252185a20785041c1100c9801c0000b01140f080b03400b49001601c940382c2c0f882d0302511400d000ca4400580d0301e0400e01000300180200035283d00c0c0c0c00b8a048030000c030b5041d0f050a54103824201c2c0100340b00000c1083c403c0110120081001c0c284602c49101915070b0718440d0400c6540c058046062551700079a00f1000700011405000040704250b034040c400d65140c207c0100038129a03000c010641c2524800c40900038034204150349172000c00400a105100d8000c84a00041a02400c16104003801c440020000b0380b5800e00c001d2001c0d80035040c11211900c8070002c0d0020340041c1c0000f42d0268007006026014078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573046582 1250 573045332 573045353
    0x30020409020301031e0b0106031a0a080c03060a0905030406141903021b0307020f010e0d0b040b25140a02030412062301030b0a02030a140406051906030503180a03 71
    0x114600300103940b94198141424085580c420417100b0f0764000102c3e8000170403600b401760440b00182008a802c1ca046001c1c9a8044849070708540c112203a0750380040d06490004502e044103009034152919521800390b144142c03102100090510380c010442040784910400b2001c1030240e22000080c01e0450b40718100c01001080c04a20000075004240040424020f43ca01400f019444004519201d05940410801d0100124440c14801190000c882d01c2c3c482006a00905074031074881c820307c0c0340625295030401000e0355103240d0340c1181c801c1ca8210038407011421459030f04c1a00c0b41c4240403111001c50035a50300c108003d00c2140402d200004080800c02c40074039105110f51004990801e80485800c01c1c01c10390b9805280c0742d0a518010804190556102c94200e2201c1d00b015950b540d465030241e0140540c5955054194000c80c100b10600c02d880d0b10990040382401c0354414428810660002030329414000a01030760030030480c44603000b07040c8015404000018050305d40503540e9171107051405 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573047832 1250 573046582 573046589
    0x12060d050d03051609030c030204050a020403141f05091b120f0106030203121309020705030f07032105012115092105030112080a0c0b0a020c0f030307300204 69
    0x1076115404d1000700c00b00c1001e9410700850798680010001c1c130755241c0800c420414032000e402566101c001c100d80414540446000d15000300c0220305030250400c1d9582d0f075840c8881c40d582c6000100c1c1e43c2500440142c001c142c0500b40200c028a41d0304520700b40e25080341700d90800b850744841160f1701c0052102090000803102921a0000540c242c03550041c503082000b01020040d669004004440c058680c0c076080e0801e80b103100303000503100c4d5164501360b45036100b400b0303500c0303a020000b0820204040c0d00202070600304d4101d80046e20303c41c070080b40c0d007405d64400307000300c4000030b820104070001c0001120030488902d01070400007a441345590207ca04440f04104140c512500b1503d8808000321915035003082c80c0728138030b8a1480d41d032404060070552003c060303005018a40009a44040034031a6140100c482c1d0006a40381541c01e080181400a6000d40c042141c43e01072800748988080b0044103480c400c0d00d81d5251558aa0004454034210b0408840d100403980c0c00c590204205082c9407002c0c0024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573049082 1250 573047832 573047837
    0x50622120210110c091512011419180b15090108101107020916090f050907110a0204151502060c0a080601140403080310120201020c0f0604090f0f0c0c030512060d050d 73
    0x4104120041c458015440e08604005a0400082458426818810643c48190041300045426000c86018080d014500d81e9818448a400406c03052000e033900543c003910442035400511005882401920340c0c0034402c001c4180c110303680c013076150502504000ca5a40031511310790300d0000ca0354005880003000355000940c0404407880105841d8002d04c61001a000c0820380c0f1090518100004034000f000511110403c42244180550048100700c2001070940c020710900c5a4561201144000482d6114604005845a1129500034000f20b070300ca0181c0503400c088c43c0b500e50140b1040e100250050200e80c1040b10100c00906020180006000694410b24105030341e410710240607601c4d03200c2900441242c500145e07a030070050ba00092807600b01401a5000e00100e0116000211280142d51281d0b06560502c101115840040c2d84510b000c3d50408108000304041d41008950403c40480c0c000c0100340100711884588600840d42584030000070175140441c815030760b81906014801014002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573050332 1250 573049082 573049111
    0xe0112060902090102060f10140409060c021006060504060c06111b15100605090409050705040609090219030201142d030423100b0a050622120210110c09 67
    0x410b41e414010381350000c0e01f40344a10075605000d0114000403105114001d10f89030000308000c5961126000300e04426001201002221280d00d0041c0d07c0d5066641e40c0c41e003040c5080400300c5d03002d000b0b0b0282c3d0b081e107056903102c503412609681c41078010210403294543ca0b078401d00000383c20315420740d02450b203443e00101038580500b10b540345c80c641038400f420514142c440000244400d9900400303442114000311000716000300e65090540c245140ca411040d000b9041013404600762281e90071080c035151080ea0344280003821128403150116076400024002202e069140c01d640007040082c040d0035440c41d145204441501c158201c0c0c10f014500d030070f103400c0d9002c81040144110344840801c4007101c60300c001c03112108042600e480b11125140350204039680c00c003014254980e806100060840a04965134400d941c801f034400c2000c016441c0d203a81045040041210b1400440700c0034040e50260440020b0201e048050f43e8040c403902c0396a0b420700c15450281c51075642d1640a6000c1d03260b1808480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573051582 1250 573050332 573050347
    0x4080609070603060e13061805010c111006050a03081e0406091814130507080f06090601060203160f02030a06060b03150607021305070203040e01062a0f030e0112060902 74
    0x83c2540d020b03501074441e80e441801009031040020005c5640180c0c040f42c00580c800190460400129110402826540c82c10700d070b1b4440c0c0d51704078001c800400100022281451134505188003591450701440d50401d0b203182c0d040000030396540207806520060072480072800c103140201d0a250b081980b1810000300c02d504100034850a2001208449617140c5082c00103038003a400d0031780d5002000d0243c220095401d030090007805000c0c003240c2c01510802c4c094403180c081d44624150381d50400c0e141c072000d80c05000300008145000200712402400c803000728494100040d10350f49540f005098040ea054021402100005001842448050880401900d80742d04042083c44c481c0c48001000034000c1408110060240c4c1d9040c070f85a4448003054800f0550380e139a40c0040f030a500807030340184000040840081090382d0400029100002000780d940014401ca03208035500701508000907200d80845080f8101092158000410204044c100014040008240c6104030f84203907000c480015030100303c89 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573052832 1250 573051582 573051587
    0x111070e1f14360a18110603060d05010618050108061303050711040203040f120207030b0420090a020403021005030412080c0f04140405060906030d05030603100609140108032a03040806090706 84
    0x1044280038170950344114030640d41c0700e496000d08010144110f4011000900981c0d03080c3c801038669130301038000c1c8419a624000c5280550040102c003503100c0c03d0000200d420180040c0462055089056903134a084107078400399000d030700c884815100c0b0130341621001080c0d101c5000450066101e0102d804000c0000c0c1401801c00c081c0301c0404045400c41c02e01000410101c180703031a0041d030041140114248203604494509592044d21070b000324014081083c1215940d0203081100e00958012581c000f4030601205c0e1031004440090103012601c040211051145803e590300c400b51441c080d00e05203040d0036545d05504994004501c6100c540502c01440c10980980c64014a044d1000e0395203007821000030707481e0215042681c0070000040300141c1140d5040217008000200034a00f0400b0584500326400038111100c0000058100c0c10000140540004102d6080c2d00c80e960103541c0e0b04220000200b050300b01321015000910051001085151040c80b1807401401140001e007002894080007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573054082 1250 573052832 573052841
    0x31d0d050d080c0c1e0309030a0b04051b060a050c0a02150d1407051e0405040623121009080403020a09060f0603060608010509060111070e1f14360a 65
    0x203043c2010014005840c1856000030741d82c0040c01c02d2881d600c070480320050500d02e180280c03000c481d03062092000300418000248840c500030f034061000d881c200348510f0003030f44078000200111a00100f003044503242d11031003403001c0c0441100d144240c0d500e4920540000b000b1241051062890800000b2000002003440c824840f424203610f080c14190318000ca4050711078080d6460441c0d2b0907a005801c2c1000d00718110407100500310040007000001e0300c4080c1c01003130031030085014100a0481c0340305e41680c81c00301402449901040000d04134240c0c00b003031083c060304800404484605003484080010390340d07050020041d02c181c080c001112440e11180c0807014199a10407000e251905500b840010390046080b4151130003a01c0b030016030340701d030001240c14911500145a1070301640c507003ca4210706074450f4a0060724000089010059090401719004000c6e110310b5030700519182a034010740c14103282072a14050b0700c0020364076900004100e1220a24401d0000030078030b94401c100700748c4070040e108 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573055332 1250 573054082 573054091
    0x1140a0f050609060121020a12060602010b0a14040908190215160516050a030908010c031103180c0a0e0415050f19061d0114040c0507031d0d050d08 65
    0x800380182d003418004202d1905010382803504004006000801416100700c1c80c0c0e103108402d110442d5109006c7d05c000304a00500c41d580c203522800d1031000034200c1d00c1400f501420000050110400d039140c40c442600a10f80b0a107520340080c4c96040c502c001c54000000b520420130441102d40c0c0268110400a00f0045400030072a420030000052010541c3d4a02404240300010305206a070340344501c028000080d2904801052032040d11034040c20540d00c54440001c40e40c07000028000100000020f50903248102085002e40ca418400280410344201c1801e81211001003540c40b00d07002c00000c1820008550071680d4082c80400a00c0200501625038007141c2c41485000c100c42e0a003030141040700c1d28050040e80900d100807118030307040542c503400280240b410038040368410900c03000a900c001c10034400c021620488503800da4050a02d405004a4801a03a8880349040b084e40e4040d02e040f13220002c1030680380802000002240ca80c0214100c3c0d41e801107004004283d040f88004008280060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573056582 1250 573055332 573055361
    0x6010e0103121d0a060c150e031c0f05010305070e0f070e010e302109210601032d110616051c11060c0307030504021201140a 55
    0x10004103045042540300035115142c140c03100c03002845032030000084004030fa54850a10303800001c1c07280d00032291005480c0710b00010b4283e1203880001c40112001500d03480c180e5001041880c241020600c10b4480b01c44400c440040d02d80d01142c6ca04c0200c9100b60000c40b545d0f448000180113070720301644020f0303010b446640349032114034001e0300007040e82070f03800c12881c140050100f4510903650b809410420300c103568810310040c4440e00c0e8114401000803403401310503001d07002011007441c0c4562601d04400c1c2502449030f24000003801441251031691002004002500b0a01e05000c0340a01c085402180a000030402c054240502c410303000c18000d00d2401c0d04020a0b0090340060f00140358095815400c175982903e802e05024a80c010b504441c0740240b480c082d2594aa040368129002140c40c000155120000c00d40c00e1035415a5600c0c00f903805001c10303d010f00004680b9442900055402880600440d01d100f85445446003900d500f880745402058104080105040480c810b00c1090040c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573057832 1250 573056582 573056609
    0x50f04170609070b04090e030d0509160518161206030309062607050306030c0a0306091703040b130f0b0a05040b161b050a020d050a02310b1201110304050601 69
    0x15002212882548148199181c031042c0411f900c02c024004d0300c0d03246643c814140454604941c80c00d480e0081c000104050803410000800d003420560201d800a820003080c10764240c459041c1485101881c16400c820080c4171310403c03000e10228000e00000f18820744034030403410306000000d07180f202c0d014541300c500c180c909001016441c0d0300385a2a0131503d1418080d0341c80e1a500082401c00e80100a81908469441d030008104441c6074801140c0c1741c01481c18140815003c072008660b4841940c01030031922003400498581c0404402c190f000c00e21521900d005106a5900d440d080300e012a1506d201c183c0d644100300c24040c0520180707501404410344d81c1c2e4890320021001d4901c4008014041461401c05001d030204002000309004e1547c005000d400340e01e1007458040d688081e03184d0100e000c0c24030909500701d441c1d00d19524200a52100114641a070000643c1100510702507400b00c2d13000b00071191003001c0c240c082c41b42012480300d11070344640d24074190a203646030040680c0625007600c0d62 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573059082 1250 573057832 573057839
    0x2030307020d0303020915090406080a0c150c021315050102010b1e06090603091f05010e04030c03030f0e0c040b060a0206040b0a0e100e0f0c060d020a050f0417060907 73
    0x1004803030400341d0446074070512468034141180207000d40070007150040b00f03200030150b065112201034044613400b100c040c000c0603180d03da150388628091000601d0b90089070014071503100c603015401c1680900e0300c1e081b5034040e1b55400083c034000040c0d1207000c4203580c03002a02c51140d540031504020380000e00081c08800d4050010a282080f02017410700c40c0c20720112409040c0d502c2d8021140c00d1000200129160304103401d0991b00c0d1405103980c0482e212840e20120000c4041d40036150482d10020490340c0355507100c0e1020340b0707413452184048080640c0e41c192500d400d8407a20510480c0240800200020300b00c0da010300c02100c0c1d01584c0307540304210500c014003816500203802541300b58806008003c1d030b01c0314581e1001400c41000103d00e0b5006038902c51030500394550001100345580f800310742c4103c0c104c10764a511249298240ca401c88d5040100d00e00f00007080c0c00803c81c40c0c2c068a42149442600d24100c5029049a08484e400361a0304004004c003803400c000031500201000c0c060082c0625 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573060332 1250 573059082 573059089
    0x20a03050f0a03020c0d020601150305010506070b0702030d0504050c0312070c060c02011403010e0a140403020604021011060903070303111201030609020d120309050106120b06060c120712090e0402 86
    0xc0c0d20301da6a250800003110a1160b1103601030b1100d0343c040710210380d011444036002035140c070824003411030141e0800c15030403802446805014121040603000794035020f43c03a119112141c00c01000d65040d40b10401125082858921405212f240070780b02525031940f407141050708090041c0030000035071200b401a1004504402d2349001140c0503030403d1001c0402e144010780381082c52909802a50b0004800041d11402c0029041d11852007100100400401080c00280c820f1051b58007500592041c030006005081410902140d00302c01d0408081500450551a2804a00721144155600040b40c460f0406816000d080c3c40d800300807050038101101c882200410072014400600404c2c2c80381005010340d15102050150b10b5045503c44100d58100080900600014001119150b10386000018564089074840d003469901005000b2030b91109030810003903070441c8200c1d4034913008058000d000007440c0e10041661030f1085141380404111200d028201ca40c1c154030104040005804120043e41c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573061582 1250 573060332 573060337
    0x30806010c080d180803181002180d08091c021c02010228080408010209182a040518161407030c14010e0a0618020d02060d020d020f0415020a0305 64
    0x1080e03c0000800c6820080c46400a400c41034001d41204000014482d1007a40c45616500704e905901c110741c6420401084281244500c0c03891043e080d0748c50301007070365a2400e2440c5407032041c0201d81c800d003040c808500154100c00862100c85100b40390788011404c600b8248030031032502841e50380072480c0041c1900080d403a040d40000414a910420080c020013003043c03500207800d81e421040050b16651207484480c000d501c086040e91090500c1c0300c0c0406201d0448074118421403c3c882c001112050710304001504c2003074024034800007038092002080703689803a288901005174400102d042d0f401d008600d285203180401194007000a10f511201080181700c003100c0703000c0d50501d004204084542000d10610064030440809542040394803082d580000400c2002240170380000c228460000f03c100084640c01e0000941010b0196400005440d042002d0406030900c03d00c0986000c400c0140d48003240c1c45904d48000360394000c1400e01415840c881d04124002c5140010000ba0b003250328040d0050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573062832 1250 573061582 573061597
    0x12d0603121b0804030c051f052703010f14150a0b0a02010e01110a090b090d170c0307080301170102091513030f06060e060121020d060e0f04030806010c08 68
    0x2c10500114031180300000140b4405941118000c0e458545915290046d005144200b602ca40c1010650415444a0320080e15103074049488a915103000030810201c0303600407518080d8800b601c46902c0c0c010352801c3c003030042c4141c102c40e40011b04441132101841c0d10b02014002d04c400c40c0c40488400400d4070342d0b03940403096940c1d0301c2d580c42e120041030324101d014040d0082802019400d1800e80002d109100000d410000746a440e201e9041c0d0700c47c070783c0050902500b00c0c190380c803d451a80c881c011800010a8021082e04900981e15003041903034064a1603003c23110440b4a502d00200400901c0400e000c84000080100c2c020b40c500b0740203030b00064629107a0701c8054180400080d5800340c092903d41c61030300440c2e10624100030f80c1c0d401c0c140040104000d1280200c039401080018440303601c100344560810b000c0f90394000032401c584004800039000203100e80c192030340e990800b0a0b98144440b80c24031403502c60313004442c03618045c44d0040482d40c0c0a05441d0500400c0d60158001640c1042600e522 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573064082 1250 573062832 573062837
    0x305030d2a120920010e01110a0b092103040302070e04050303060103050a06050d0501050613060503071e051e13050c090d0c0b03180106081603060c030e012d060312 72
    0x902c0042c8110a0050940c00801071240250b001c03c1803e408948540d0100d0141c00d80b160400d401d050710041d0350b00c500140c2c00d0121500000000000120000c190a4000b081e0b40102c4600101007000c01c420041d010010610240f004000c000c01c15038104440f5015181068408801c0e0400341c2e200b40d80c81c00042e00007414940c41d0340029244e1206a4048802000001d000441880300760070018000c03d030030b5070074500450600b8141c181c01c01140c0600400c9620280007003071010315040b82e0302114202ea100050001c42c0317101002907542c1d035022815556100c203111003841d003a40f020420007040310b100c187e00da07007906200c10410b604850318107840d4540420b543e20380210186240c00300200d00c03560080704500d9000300510240b4100740e06890024680d01000b08040c5032580ac2d541d84c1c03403002c0403880442c03180c481c1050000400c03580181041b01c555040200c0d1846c841101107013520300340724101d242c082d03510440d03188e040024038114642e006071400c10403201d42941c90784102621240c00d40030a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573065332 1250 573064082 573064097
    0x9061202030a090210030f0b060903030304030c050c0405040b061801080c130e03030a020c070803031603020705011b21061211010504120b0a0b040c080106081806010305030d2a 77
    0x164410b5608103203101e43d402041c091040b5455040a4010101ca120f184500361074a1914021810203c044400c1101c004000b542180c1e1542c1d0101c0c2d0038140b45a0445140c001c1940c040120307100d500401d4003d92040c15000d101d460103006000b40c00121042c007000442d4107000401c480c02d03010808502110084d81d8001d2071680058200001d45543d0410181c2403100000300602e54000364081d100b04441481034a00c1c540c1e07510005940c034041603400b0005550310880c0d8581c188d00a50080044a1048002003080a801403e80e40404010354050000c03030301c00e00f0703a10398040c80b000100118000d0810b04020003400c00d0480711050400b9040248580d08841d5100c1c51680101e065600504a8401c003a01d00409458a01085c4406485500300c00e82000385001e540c2c41e00b40200720326003c20380d03201101d80e86000b42c112501a800351203038a034071400354001e0503441c0040c8101380c00b0794040c50045940b49034402d0100100c54000c00122a030421883c80d2200020a81e5001c1401e02d40d185403d08 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573066582 1250 573065332 573065341
    0xb100807180e0105042a031401050405120a0806130605093c160306050604080d12060302060304060902040605151306020c0303031b090d0506040b010f0b0a030e030c0321070906120203 80
    0x240e14129401c00f1780100223101300041c8000c015001684981c2c8224103070342c0b114902820100090284400c0180071801c000006031541c14980c00045031802d10140105040f50b40364042141c03c5d0058a0505541440c0211468590b00110891083c2480b1515400316241d094901c1200e00d40040c04070780c410400d8007140d402d00740c0300707030000d43c00303000000e00d030640d2250345004c21581c0720007200f603220110f143d1170307065a8085440d106120859030080d00c0325103191385640d50140104500c490890388a41d44003400b085036262418080c40c40001903107091390f2444c0803410080001c09a5111908562000c0c55144080e1408800da9400c03001d207040070125403072900c07101c0c440307801014001508061030301c440310305104000030680d000304d000d0110340c0e40a9888154580441405014280c01d6010410500f10010301c20b9020303803100c409900a80341042403140b4024156404103001d2030b0147c034600744580c010702c094105990070070310b01d04180c00020f06d40030025011041501003800210f60220024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573067832 1250 573066582 573066653
    0x7020c061b0d0c1b0501050403030e03120a0507063c0915020a0e0f1c02060d09050619090c1a0712050415050c07030b100807180e010504 60
    0x144842202031050b1241e40d00482c100802103d09083c060382c0041c41c404100384010b045101c401e09039a010307580c070780c5031505644040d1030a00035400c4550309403041d001c100242e003a600c070140000318203070750340d4a40c2d03006203080035002c0d00c001031861030380400220305040221000700551500150510b505c2d145441d0030143c00c0008055101005c0d000d00035074203142d02e10022a0f80201185e0b29540c80b6032224109003030901590001e0b45a106070404c8818a11b4982d200020454402c42032000740500e103403110110f40e290507170f0170052040f2001e80c4601d05010345240c003484100111810382808005555594988001c504a98420103000354284025240c4518144c4101c4012503080808090540180c0c0d40041195006101323100001c0c0640b03000c40c841078450021142d41d40e50641c01003a0090458507003402c06c01010301440002400d040c1b000407807000034400c1c40000c1034204c2da11260041880013900c1620080c10680c00c2507494682040f0014404013443c0003418000c00c0303484076007038083c1c404 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573069082 1250 573067832 573067867
    0x150503060622021c0f0b090403080c04170a0203070501020a08090d03090503010c09050406170a060e03160303020405090c0316080612010e07031505070519020a06020d0903030e0607020c06 82
    0x5000c02c8500016141c01400f0b040810b8455020101500308030960111021004488424901a500400a1003c1400b0034401c1d00074940160880c4052132500750781d013940d20301c511902074640406401004544c030a5180034000d00d0011f11007800507018405450342c83c10070a11410382c8440c0700f003005241c00e606140c46415860003505026008000709400d01002070084201485090310171b07414400c0200d4680d0b6060024001540c943c001403d00440d142d4603039000c0d0070000785902183c171003880140c0803404110400347c1064000c0d100182e40c0c5003041e0503c011040d0003000540c5104041080c021141d0001010042a4a0780c0c5402402c0b5190180050009031020301c400107150f0918240e140360031004101c030422a84540d420740c41250644003407805031a0112051400b14105011000524055000c16a20070100740305580e10701e1081c3d500c2d107040340c00c1002c000c1210303642e4401d90003c2581601c03aa44601c00494010700c2d080c034003144001c1daa02070303d800d058010840030592000d0481c00048 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573070332 1250 573069082 573069139
    0x2060103082503030e0c0f0303070f060b060f0307110102130501030c0c06110406020c030d050324040516030b15040b09040b090c030f070801030b0f04050a0605150102011505030606 79
    0x820b07440c81c0b5080d0500401412240d035030b244c0d19024200302240c2900d840740a195107960064080c600740599500c5082072525901d000396a070540f01d400d942040d50703800c40201002c598068919131603040031a4014054aa541c100c81c0d51a0700c10000041c07007030390046c20074044032800d01e0086145a400360701110b5000e6000b0005240905110700440c84400d00c41c0500162429a03080f01e0543d01d0030020995103c0541c0c1c03054011400800109a0840010004200b10ba000007082c000b400e1142020408542040307a401ea003488890101046055043c010340c1030940088504c510000e50801490350070b44542d00c5081c201002c00200042c81d901c440c0c01c45c20407044010b05001040c80c050f101240d55500480303071240c044010000003041c441c010171085050300d410691014159407502903100301d030311014005450790b1194030140000036420340175543c07140e03021840300c0e1142815080060700b03445551118059892a0402c00d02060302c0019029070301c410100e0340c1890490302200408400d040502 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573071582 1250 573070332 573070387
    0xc090a0303050901030f050c03040809120d020304030b0c0c1005090109061d06010f2907120f09060309051504030513061d0a0303120504020f0d030801240206010308 72
    0x900081890382080107440d400c00c0c00c3c0c80900203a2000e92000d42116421100c105909200703001280c082201d01010303260820001d055410059500d08641d0b14100c60341c0e40a400603400024180101b015090a06800a0f10219010b04101e0780c8580151581c2c008290140403a9586d40003800030007094120146c1550041d03402c000d030304010f40c07002c0c0741c1414000a0724031714400d0b100002820441c0c02880e00482e030390900c0446040850b01b050b02c000741a00802d4000b06101130008001040e0100c0d1800b003488896147c0000c3c5a802000151541c0c1c1d09511110a041c0b070080b032500418000300d085908450b0001c00c0503000d80d00c0d8a42542d40d030042d0460308422030b0200302c01255182c0c1004513240c1103880e01d10303549513481c000d030200400501d0900005000a81c84400e0005100039a08110381040c8000c1540c2c0f035440c0c0c0030021507030400d14610141c0000700440e0040040581601da14178003005940b41007a000d084489001c0c1d9242010b07c402031100100203101c458036148036002d20380b202c0000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573072832 1250 573071582 573071599
    0x20a1704030e120106080706050304050709020a0212030a09060501080f190c03210306080a1e1113091e02150309033f1b1b0a0506041406040f0206030c09 67
    0x91a80d0b0340200b05c58010400144030300701003c16418081c0303051380d00c59a80100141142400c0043d039402a4104034000029032251805c00701e8000103080c050740c0714080101001540b040c0d0750624100707440c0c0682c490ba220ba00001d8040840c01313004140b034110780307c5074205a910b10207580b07403410280e0265800074018041e145046040d004020385050466441c0d0340d024401680c03525070301515051146c100401d4282101000902480e034560545101d500030b000d0300100e44120b50100340702000d02d540035030f440382d6074030059800c000f5851400d04a03820024041c614001d441c0d404218a905c450f09200380000c070100008482e000704108440800e50740800d41130382d1400910440e102090911000d0452400300c0da82024118681c5108900c03c0a202c45000c01c44400348101c8030b8664071151804c4050750b1007903844959050200540510b0714401d4004018500d030a052460705241040e0040400e50025403d020200302d13440402203100b070301101e2142c0c0c1c82d00e445006851a10036100c040e0380040300c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573074082 1250 573072832 573072859
    0x14190908011406010207080606010203070b0619032409080f09061c0903093807060204032d050a020f060403050123091f110c060127020a1704030e 64
    0xc2d0201601aa000ba000c907142c0c5600c50203000d448001c200d0341c8500503841807168201050f004510b01d41c110300081c0c807480016104100d12074414103140c00940d41804404450440d100404000ba0b00030443c40780d04001814255076000c11a1140300d4849440050120324060a6030343c0c80304941505003501c0d10010003004d070112502c00b42100c1c1d0015000325481b02c81c0003640d17140030708440e8440d04901800c03840d007a248440309041d207100c03100c0d455000c403401c1c84507200046840c80200003841c010325440ca03030808103051769911800003907410401140183c540000040000491102c1e0385e5046611410403810f600c0440c60601035584090004c4d0300340341c054000c511721071241115110086201c00c0065650380080341e5100300c102100380808164200581310762100754491900a1300f803175100d81c50200d90302a0720b4034002c42a0082d003810307000c0400000005521280d41400c03400d0f9030b8019030514000c144054845a1514024540492100009410584100502c1848400082c40325400d01c90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573075332 1250 573074082 573074111
    0xa021e010c0305060d02100f02100606020c030609070b030408030c1c1d010b010c080f0d0203180d090501050d150e130506062b03020c10030e06071419090801 69
    0x8070010300c90200b80380070b000c280300781444a2403000c0303540c0241c005e480d5040340c64403c4403a440307000d603050114041c100780291650503070301401e4001c0450f50300601c07074003011340105400c20300090030700b21003a80408401c1103000c0c440c4058a0748950004540c036229918598640103d119200b41001c80d815107017011980750049074010b0107201234840480040300d02e80c41c003a5080f90310213809240403415404109000031a154000d062000c80d003404581000c031581c021005031b81042e540203ea90310010000388042008009100a804040c6000101da500d0600041c1042c030603900c50031030268640000087c88000c441e8883d000301840c610000c10780c503228035a440b2280540004603441d002d1715010560518100740c00022040340100b0204e451800c1040f003201d882d192102c210150f002c0c1040d080b0301e81c0e69143c4449251041303501d001c00d00740d0b5010303440e40c100b0900800300317001e0288445015148000036025129980c0f03400010200a08030600e06891b200003940c01500c2c55070914911200f002d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573076582 1250 573075332 573075341
    0x18030a050a030f02031c0c020c090f06041e05070908152203110d0306140f3d02060601030e0f06040206130f12060c08042004140702010c091e0306020a021e01 69
    0x1500303503007520030030809c1004001c41d50708240c5030b1060644407500851000e06d481d9004031249070b211508085400000101101500c0742250100082480204200000340342844008690410310000c114507182141403030702e0010101501482a440d000039080800d401070500e030304d803515540c0c2260740d20700b5020340040c0548194004c50040c4880801c00440504101444248421008182101e5190400d4a4100000c3e062084841d40c1540d40707809204d00074034080c007a01010056001d0032851800d00005400e40d6034035400b2050760f0740000240c0c1c2d2540000b00301c05030407a42c1101d8880e0303114003460700e004480749260800d4085e115032810018925850302080059248200303400c0c0300381c1520002c1034800303143c103c0f00070708040e984d00004d840d03413000885080c110342001400018102c0c006041a400c1c520200c40da200913030341d2450b2040940d80c001d1000002040d502c0402890144c520a101d0824004c40c07000400c901d8001c9550a4698024841b2600025001f40ca4515100d00040707001d0181 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573077832 1250 573076582 573076601
    0x1202030a051005010c0209010e041e0515150f010e0a1a031501090605040902030604060308070302010209030c0406060f030519050705220b032412010218030a050a030f02031c 76
    0xd0b0410036001406501a80341004060b4000f8407501050707282c4042c440040100601c1250703c4840d52840c000300c02c00030345140521a014100a2818100340c88000e10b10b2040503107181a00d90806107482041d0b03480c010174800503102840c000c0142400600400c0055241e9040740421815502440c840b00401c54043e600c910741500142404400100042d2802c07800c3d40507400014104103c2808400215002540c0180340900b0008200ba40c0351141d01b441d07000032000320300503500040c2c0b000040c9410004041641c03c100c2d4200081840c003800541000d181411400505440e038000a40402d6440441401c2c4060300605104a261142e00141240d01064444944a1080c42030030ba00500300c000c2c82d42652003080c503040c510b450301e01038152112099030007043c8601124002c2012501e6418812048240040015859240c50000300550365610003030b0f81c0c0260b10524240000c5100012019019501814404240c40710604100d04510864201c2c0410b140810400ea402d03103000d40c02043d25 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573079082 1250 573077832 573077851
    0x215060a0303232d07050618030f1207121406010e240318030408060c0f090d08180303160f1b030b10090209100e01050d050c07050d14070f031202030a05 67
    0x101c03c44500d44e4281c0100c1c80c02600942c020b500081c8540101d03c60350780c1100c44181140d003000024210b22105611219600c110501500240043c0c2900402000400c0d00208024040e07160360f1600040c490360700401250402094031011805900c4081c4148800b0010703c00d20003113281000506121a881030307030102008002c0e941d549581c06c50120584040d10909030141110780c0358900b0040d1319412185001a40000800040e81960b40c1c418003210b0113441213501540340e42129070316641040c90302180900039041046822a0442110303030241d10668024205e2401d002542014081c00608940400c1c5940c0f60b144003106010f0101e003c14801c080001e1030880058850304240b09074003890200d0341d0890b55015032101070a00030014070341d00c0803041c50403d007084201d480e08015260299101030b20348400290001c1400301c244100c0240016500b442c0c09601141d490030821481604405403110072a11101001c140c4034540cc00160750b8070031825500d0f8104074110000425054814010 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573080332 1250 573079082 573079147
    0x110604180501060f020a1212020c030c0f0c0a0b040905090309030d030915061202040e0313180b0303040b190c0b0a050a0b0108240d02100f0215060a030323 68
    0x408520000781ca41b00581c0c1301440c4c0684660140b000d4030301d0102c0c044003280c016024030554490300030030009441081c0405008022421620490034101090980c1c0765006207030000c8148903103201301e01107604503940044e00080301e690301c0c000c550a5000f090b041075858021000c07810391495154010154942c00380020000b00c5140e05842c1007143c2840c401e0084d0702c03a42c1c400060140c035160703010884284c09003090301d140103040c40078441035031a10b42215080e131100c03030314030000201c0c10322941d203545e00c0540086240c94105080c506503400b46541010421758a020f50003000c5c1d20030b044000145501c844e800591b41001e1641001805088803070f81c0344145007120503140c0e03610030341d54070b40180e24440d502e6404101040c000d0108041d0000555048030f01c40018400684900381c68210040c0107568507460155440002410a12070710020303c982d00c0e0f1202840001e90b200080e240807680d140c142503c00750000a4010042c211240701e103a11f104010511144074a92904100c020845968070030a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573081582 1250 573080332 573080357
    0xf12060e010e15041503081309061e0b0301060806062101061715090612120406050703120606020c0904030e0d060501090f05092d010203150406080d0c11060418050106 73
    0x4101c0f00200350082d4148881c178001c00110383c000b4001c0c0340d192258000d002c4180c0d12945204150354203607001c82850f01d1840c0704642004800951500500300491203070740341d5450140000e14801f406040b09218a60000e00c0c1188820b6460380e0384000c0c0f818110394211580d680401031f0075403034405104140f019400700040d00d072200405444a09043c002c010aa00e03403913800030310240e4940400c03000901d100348040d100101003090007a200400140c1d03076566403030704039280040592400640807050141441c0045c800c09401107842e4040a0042c1d4200b03200d0350320b50070f0071102c0250b80c3e00101d40082680101d82e06205840e00700f6816541442d2052000c1155003000c20111602110200400c0e001892280e00440c000c0480181a01c0c00780311442007601d400e90f80c50300326441030781c480f002c051170000e410380941031500a10008242e104045c2280b8039074108003410b500d03000034008005075000545080143d81e00d10586020304002c0000c0740a03403859200c060700402c0c080c003032240032490520811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573082832 1250 573081582 573081589
    0x4060e010305040f061d011d07061e0507080f070f0605161b061b020d020607050a080f0c0c0d02010e010f0603050a0b060409150915020a0f12060e010e15 67
    0x9000d65800b43d040004ca0056444090013440e03580c0e103001012250400318610043c0900a03050607580e0310071250814923101c4843c43c940225648034100303226244881030000c0c107105165901c03200041c10401d586030900c1c60042c07060f120700e183e60724400300003203040303028403540a40340500188038000401854403440503148041c2d406a00e50300003c0c44c0d06403901d0b1007940810280030840e00c0340c280840c0a10645001540200c0c2c0b082070340005030301034100e0b0120283d04000c03c540214860804c5c92805d528110010f00c40c89000b4001e0a02d180e042001c54100b114250454503080018000d03030b803000106c0980203010b00f02544c180000d541c2860003081d03015200e80b1403d000caa078000c000306003040d540d45e5507000d1810009c080c982d0140d50b4094030b40114920200c55110805a00000205020a45049064006495042c0e9045841400810307841070300071010f640702c04414204003189408100420b4041c226a1b00113900840c100000080c3e40140001d8150191500c003403800280d10039002803 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573084082 1250 573082832 573082841
    0x50a0204050106090b071709061c15030215090a030c0f060306050604050d030f030902040f0f1a030615030c040c021f0213030807020103140f0108100504050721051204060e0103 77
    0x114409000e0420208000482e2214100f80000511f0046410300448500107030f00c130742080810117035101c409855100c41840c0e40c411141422404198040c03c0d9013550045032803105407031400034040b000001c1308103940c0d403420150001954015121841543c40d00350071510b0050b544074040c0401e0400780081514a00b00c815141580d8010381404079444082c0c42c125084032080e40c0d00030505590706900d0001d600e460061868440c2407520119070300d805030781c0700801c8400c0c006981d246112008000c14a960740810f1141c0c0060024040b0842e10090ba00040d081100b4050143e41c400e1070038140072502900492907401508020840c01d0310480740c800b0382d2046e44560030071003050301c09030101440021200c0c40502401c90061500140402c045510304064540584400c0740d440381100c0100001720040052182c4014042028001030605903105d80d07441115001d0b80c0c0da009400450401c07840413002c20030002a400004036103141c0390b400e80d062003580c400c3c005d5600050f0794548000390355019019 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573085332 1250 573084082 573084089
    0x5090307090e0c09220c061b21030f020d051e090601150e0d0308061e0d0206030411180609130302030d051005130218042705010b0d050a020405010609 66
    0x40c00c2d2400c88881004540b002c024202c0e4a807011018200e00c900000d05c0103c80064031418003200300500b0b000000d003504005c41c0b8021703402c3c0c50b5900c0c0c08001400c547d048502d01c8060040c850403c5d021a0b009401030080751221508140c03000c03a5000190340140c02540c000c020007071285181d0b156600300e030b04c11008225140b10407a400440108683d0540d1502c0a40c420000d1400c80c401c86003110000344038808c0054140c001600c1042404003900d0001050300380d100c80a98051135001500c0c0215151011080e006881000c000c000501848170b022448000c029000f800e2244800b0826414080a00161005401042c51000141c810805181c08080e210341640055082c19050ba8055024240007082c800c1c0d03180c01c0800018960f110048030b00b94100b07401c0720140e10303150140440069000c82c021254810b030709140da61980070b28031080680c2800700304894001c0c20758081c1000ca001d0010551402c0c0c00403400e40302101445008039200b0175041c401c48060209990751807046895126600 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573086582 1250 573085332 573085361
    0x50102012306151603031103091e0c04090803010626132a05041808030106051312060209210726060108010230061314070509030709 58
    0x31038040c440c500c526a0301e0b4021802401d114031803001d21100c20b031941104003c0300f001c10011640310200341d014000c801c0e400040c0c5000d1401c610303000d1b0a0b182d90f1500070ba00345019882da940300e003001354818840c0c52800c0ca00980140001066440c0c40301d42540244102c0c1e00181114541a03c003c8030750444405020710119801010303182e11204400400a0904c1260302d07140c1c000d00a8a074289103102c24044d0180d034030301d0401c441e103054203000680d1500804598071940100f10500092400341c01e580c10b40fa1686461520364034101151210141150448269001620183d07010014642c004002c44102036460108002c01c240e00d801c10b0507003560120169030002401888400c40d40401035400310100070b625086240c1c0702e111542424000c1c0c0140100d41d40014001080010389002c000a44503081c00d6030091358909140043e000318003908151040075245010fa81c450065040310718000304100c400c00312414100b90140c0f89070f2240010900a010703d030700024500b046403040b80482551207 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573087832 1250 573086582 573086621
    0x80705032104150e0405040c06030b0303040e0a0c02100906050a0f0b0a0b09010309080d05041e0b0609070c12020a031d0303040306110408071404060f080a060f06120c050a05010201 79
    0x181c206034418607036074551404c00c80b810122181943e0340303001d030a010301d0041c000c2040f41c034241340000702500c110a401501070751040008002030703011000040e92045000720009035071441208200c5c24641e084248a0500c2d041c900000c051040c0760b44080d0040c998a90f042004034544081803081d168080c02196001c41e405004000108113900142281c04d01450001852161390b44d0311328168221301ea520300b549a0300c0c41004100030510b141743e40007440901d0011803007152075450a200080092403140074a14030b1020654103801090800d0145a0141d072a40c4005038145002399541c0340c0f1141a80042c0242c0543c00d034464203522000c6031a9005006586410f04540350386c8082e1842070030000300403104020000300c1040030f201950103840b0800d4101080314080c0708201c1550f842d900500250311840304104000b01d0300082c03401d01968859804240321a5404615004004c26030002c4090300127410b864041001c0004c00a059460407651841701c41d48603001242240d00a103c04c42080d04075 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573089082 1250 573087832 573087839
    0x705090103050a0b060403060219020102161704030b0718051f080c0403020901171b0d0308090109080406090524030403080405011b0806031b01091505040906080705032104 75
    0x94222030340c4503500f2400410b8004060000c07661603400b9034001d8602075800306070000c5098041042050341703043c1d07200a50600c586500e580a404003640402801c00201011041030f1514403c280c400440d040a100442d5160050001c1d01d9500e51118210b41c0008a0034085100c3c0b0f84030014501504004900c90b01d8040c2101c81680c0000c40500800c189001c203000010042e541d0031243c41c040c202416281c12400d030400c0c102440c2003d4801d901510360b010032a200390a490b12404034440070f401d0307d044096a1a41c030502801492a82d81c00303003400d100042d011420319040051807080303804c20385001801903001e00f0081d5200d80a03101342c2c60035039000c00200340828403c1502c3d0f031f0040c0c0104000205017440c4c2140e5010305282d5070000022031000307000c000440ca01401040c4130b100c411001783c01d18030301400000740400c07018011426015201c1f545200c0700d620400a030340150035030b00c0d0304110958070740c0242603868649102d224031900c81c1440d20344002e20242d0040100507241050f55041604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573090332 1250 573089082 573089087
    0xc0a06140d0213031b0909080706110c011401080d03060810020c0f0703230f070504050910050c0c0f150703200a09140d0503070206090a080f0d0e040507050901 70
    0x10200803555015003e009524041500318803c0008520401c000b600f106844a05060b4040c0c069020030203443c58884a035002c0703041d5030112584268000800586403265100d0718100b4002d070116210950310704280321001c1914028142c0c142c2d0300040807278154044541e0100e0944009019040c02c5800c000c00e0090460210f801802ca00904071080c2ea601c201d080e84e0b9903151980a0b8000d40e40c0342d400f1440050107480c810b080d1040002840044d12241051000d400e1b55640c1d1441043e01480d41d5600140d05900c0a000c442240001c6110520546c2032039824a0807a41007551500814015400c0003910104d002842559030b409444400c1c8055496070300903402066014040a0078400f0600f505800c00180c1c1c00a00c072a94081d01c89012190500d407680d802464042c542c1802030400410780404207074000169030700f05a040310300340d648000c01e0021802c095020b5024100380c1c422107154140da054080380291100040781c0e41d4144d1414010100419550265032a401140c8108000e201c1d551 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573091582 1250 573090332 573090337
    0xa05040c05070b100f0501050405010f2d0c050d0804020312030c130b1b0102040501020a110409120f02010b040c0c1202070503030a0507060506030105040819020a051b01020c0a0614 79
    0x940c506219041001e6910340070034110080b95003041c0c0000c03222050048914900c0c0030740262100380f80c5182454144400078200f00e401c0e005980600013141300103001907a81420308215100d00488203840a10000005041d402111004480c1c500400420910151190400a105940050080034100c00003c80e04410b0f0380054642a0091810080c0e560705528807242240200361401c40710743d6806207050300d904004c03c000a04071191740100710030052680e0020b48401c034103400c104a620301ca554000001c0c004c11070400300800201a03109a6200709810940302044400135800078000e0b02c030300000304000c40d84841443c0300804c1c11502210040754150040d0b400705000b03030044448160b1500b00023450341d0020510240050380c002041e00410456010706900a50194020703c10340c149503968015a001e086500c51501001042a02c4428800c0202c8000103412100341c27005410688070903015908100032503400b5101e42601620380f81000e00140c0101c4005a4581d070003a00200034171040366 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573092832 1250 573091582 573091601
    0xb091503090a080a18150f020708030f130e011401120618020d152d0e06010c0317130c150c02060c1f0509010e12301e0c07020a0504 58
    0x50164400170090380072140e80240542d030304043c9421403030b6000100040030132000f440440d044507030204004400007003a0743c0300110031640c09403034140404c00d41401c0c0c140c039070180e04801e034060000500400c0c0c50100020950086c0c3c0c0d104c111011a10a95061350903520481c0c00220640b140240d000b075496001c0d040c44804000c2c003280e0200b0184084e03428400c1e075001008541480e0103000590b481a2004080d983c110030b50014016151420f400e031004002031030345040c0300380c1034108401c0512a21b0641408a04c0480401d00c40c10414035401038102008000c40300c3e89000e0001148a1a400801a03500d4010f42d64100d003410080d03007880010b4000300081100340c03159400300340c01e007104a81c9400c0c1169558400080d40d02d88441c506003541c228107941c41d4150001d08100a0321f8001400311020700a40682c2c0d0010101120048620040020721051440480c0000e0042005035100f000100c4026000f00500d5a121b80000e00040c0c814042d0095102480b9282044103007015040440f01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573094082 1250 573092832 573092837
    0x4060209030307060e06090705031e010207080d0b0301062319050d0f021921170c03130501020705011b0609080c0f060c07031d120102040b091503090a080a 68
    0x8003548000440d280d5004500212440e5031030b4500402003540411540d85d11098031001001d1b00c51070f220100b03440e405080112030000e4000c007406002c1d00c0094040b01d8460354000f5240395079600700902d620050803021200da202c2d50802c0d1002070a501e62060038880f00301040360b0014aa00c5513004c02c60b92482c3d41943c002c601622550000d180e0b40ca40002c8613040e0b01407030405022009600c104203e00c40c1c1036802c109520701e6110b0070300079601c0d81104032004444940e4030b4010210982441d0400020f40d1501c940e810302c00003030b250f10103600400945030304210004500c2e04141c8410059031601d01c0c80c01450300180109d150700d4680b18940c07980e03001ea00d02034880010180c2e0941c0321240d482e4401c620003401540300c0c00a8510200d410007240e58080c044e5000c0f0b0f42041c04c02d40e0700525004820010b24000c5160300c800c11890341d20141013000d281c0505000715900e0303503039104040c415008400b40c0c40c400d05e206c0441d0301e4120b03800320490344101d00710006441c0c291003070b03030340d07100c20360800301401b000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573095332 1250 573094082 573094087
    0x301140904020a090e011e05040507180e06070c030f03051b0a03060801470f0f09040b010906090b060d020708070c0f090f020a0e010f051e180303180405040602 70
    0xd13120b8451041c0e04c04e1603612800454540400b46002907805000c0104c0c00c21a880c4ca0104008a040462400305403448100070041d880c5c201c10222016240003090622140980400d00c025a500090301211440c80780d224443c43c0d00714000c066040b55000c4400340341c1521032103200f00c03205410400408403a0010300300010500c1c0c485010302d0031140341460b0168500c039406008042c9010040101048070308040400040031000807140c1e81151038902520301a81c50280c07803035499a24002d6202242001802880c410b1800d0b0410038500d05085c85500d114030320749640847c545215000303076403011001502440c5440440055000254007030481030300c2d083c109000a50008000d0a40c01c0000d1150741c0300da005a41c00c00c82d010040b51f08c0315500a205910403c102540c158002c4000100d400090800300040b9100840c2911b4600c1000318607410304104420713100c2040d0444016081040005040b605c04000d10420301d83d0b2442003030505900814000c0750b08100b45400e411080c2c7c0940702d02070250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573096582 1250 573095332 573095339
    0x117031602102303040219212301050711070b070209040501060506030408130b0a0c110301110a0804051905070311030717030d0c05040b040b0702060c030307020601080706050301140904020a 83
    0x10f441000c0000c4000e4104000001c1c001507280c035041310003440c00d544215103044c5140440034003184292158050300d03240e0003075095044c8000350240c0f190706000100c04d80d80040f40c0121590003810221001d01c0030454421001c046010b000940380c0655409219461030a031158003004114480100102c80e0f0b592035000218007a00c0f020081d40c000d91084030f03aa85c80c2e205000c0034401da1080368000300c02110080c49200e00c0660b1212007921125009550325160740100c5020902414050142c40800303403000602072036050703000e84480e12842c0902c054484041e946d00400e109004030b00c1000d020340d403104909001040362125050343e005002422900c65943d94203021240f8040181d612100ea0008240c00e10a4141801841701d072040503d17020745030a06011030b088460081c3d024092450f9404908030046444a4080310b1010340f02d8000c99440e0b28001d07000030340e6403209000d0440f25010300300700050824010b0066034180c0b1203042c44464800c4084060005d040f6000f401139a01c0000703030b80000b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573097832 1250 573096582 573096617
    0x10806011409190e030301030501050c1306030c02010e0d11070803030105010c2306010e0f060f0112200301030c15020109020609090c0d09030e1011060601030c1404060503011703160210 81
    0xc04e030b1a00da000345881c0e614504210742140c1c0b0081c05100720120400c024540c3c4e84000440c00150342e9682800034960010a038100d004107001540745403903100301201c03410704607000a001489a60000c0880702c00c10b0303c400000c5d40f640801e04c80c16002c14000300540001450070407450300104421035130460506149920300f86800d20a034403100100500a05011024004142d4194420001c2d6035204120b000800002e102d42d141030440c2c0d081555409580001c0021013010300280040300d8205512940c4909052f905141da034454400081e2000702c0b061943c038018090b9000707098000305201c1c10300d8200740a02c0303031600d0002c24010b01032604001d100c02d501603d1044410781400303036481c0100c0540b800d0038400307d540703910b07000c0302840180e14060843e070b040001d46581c446d0081c45c0214a01000510949040d1781c24583e9180700031001c0f402080303080c1d01c0000755049840007650440b20408540340310744c0f03e1003212010003026004013030000150601c1e05002d0004000345c07820b403103110040f010300c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573099082 1250 573097832 573097841
    0xa0c0b030a0612030c0b091218090f010e0402060306010e0d0f05160302061e0c031207031a031b0f0d0c0f0605030f191509020a0801080601140919 64
    0x544602801009000044946101d10b03800742c010040400b015801c42d03200980308032550b1000500600d607950010300304d12403d1200600301d44504d0342c0f0540302e202820146049500f168075040c00348a80c00c000802e6848640e440312f048820f504404d0071540c03100c2d028081c0503400180b01506004e080d60044029454050180d18030307501440b54800f84084034078000e4203010f000f00c040c4c4d050540c2c469090025a580c201103421441c0311742d01c8040c41e100c06041c140c815001d282300c2807080f8080803441d02440c1c10701c1c0d02928403608281c0e404010070b1114111240111621301d80d21a0035901c80040c03440400c40606000140341030061443e08608011000661841c02c4040221440070b80c0200411030407209100341e802408081c00e125045203032a02c036121403d00000d082c2d407803031448038141020f050460340c0320b030820040720f1558000040d1950700110107980484405070010b0340c0342000181c3d520340410a075042c0e90300c18480800102d80c5008001c2418800340c0000d008170b0a070f60011020620a200303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573100332 1250 573099082 573099089
    0x1d13110f180405010b100e09064908310801060611030c030919090c031406010f02060a1508010c030902210c060a1e050d0f0b13020304050a0c 62
    0x6070120a00d424a010707400d41c0e4040c1d2440e405200f2107250b04800503000742c0344e403020b84001d4a80b0061540e54000007064904c0803164009039244200b1a0b01d05400c2c04400b0315003464059072190010512002c81c64500901083c010340051070a10002442000300703288804842000042a4080c0c0c02e60f80040d0780209080d0b224040c683e540d4441004503a03001852844415401b40c0914102084102090b40700c1c030500312140e00c0380341360490b1802c1e001c3c18120250040c0842d02810440d0210071000076008048031594000c0e201d403e5000124550b02ca030b1600000c0b1039065028003d2354403042c1100000e802201501c4942c50510000401c04500902c2021540c44e202d90f00032a01d8251401030200ba10ba18600d0301a0205200040316450031001507101c0007000190380440c4c5e01d10030138004841d50f034940c002c080b1002c4103103e0031511071940030000e0480422221000c020100708915960704450b041c0b001e0030340280701446614007c03800740e400b8651103409102079940050143c0e8441c51014942e07003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 573101582 1250 573100332 573100369
    0x301050d06020c0723012a050a060203070309110906030d1211220b040f033801030b07020a0302070b0a0e0a030327081b06090a0f1d13110f 61
    0x190200c40945d540e500386a2206000c0c00c050454460a0101c0000385807402d020b40080c079510030044007004002c0141308041f58008a086450742480d40e4024007420700d021003940c5480d141404014140750000c10140140402001001d66a002403001d40d80e2400c80015507540a5660306810b40040e05038005210190040c10424803400b4001000d000010341500301301040c02d0188414070036050700cbc1035a501503036044140c424101c0307030341440c082034001d4020882015054515420108070b40318200e5a060f207105902401c03190b540c032042240e8900960740d010780103a114103003c0000f00d200000400d500d07a0149441180b8500d001c020402c00b00880d0300c2140060111207010008001403401c03142c08514101e002c6031454a130004540d9144000a81841000c90015041c100ea5480808540c100071340500042e04442e030320381e488610500315103d075000c0883d107205d03269010323410004207d100d80d00052030784680c4c0303140d41c546140301d0758803c3c5290f4211000c801016019030f00c0c031160300ca0102100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 573102832 1250 573101582 573101609
    0x201020d051609030b0406020702271f17070b040b0a080c0a090504021315050915132612031e010e070507060b1305070906090303050301050d06020c07 66
    0x245030310210381c0d0052901000b140144546140340341e20011040441e0b801902c0c2e41c081e5102c6080020007881001d500130740c081d010300d042d4442006581105000c1e410100760601d556540c0e002014010342014080c45050f50500105009403070025130400c0c1c10a064108896002e6100d845106103030740540c00c6a207078014042a540d802980c0442159800048118070f142006044600a4001003650003200d02c10354001c12750b50204446a00303044001c0c0b19140c503040070055103e001400c240e001c504400d00440e05038171841100c64040040781c2c10302108010381075401e0300e170407040849030701c14105101142603403030414901484100446001d0881030f00503180e070790030020468440f04854181c001c420081c40b00040112500b0302d242070f40d024449041c07469541c40c192410500034081c02e401aa80610000200a076040007070384190b00c91151510f82d40072090f200c40068501d480c41d444000d0000e40104014403403402d110780042010780c030a80002d420020030040540c00c1c00c01c0f40e04414400c00341c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 573104082 1250 573102832 573102847
    0x62319110601060203090a0e1305070906050f06031003080f0d06030606150206070906050313050703110f19140f04050708040620030c0a0c0c060e031b1f0306080d020102 74
    0x5005250050681d8001175143c04014070125003030356114455892442000400601240306590800070650751000a9a401039156001480208000c1c01194065050078031032424a05001c0c0c1201d0090703106d0892541058074540d14400641d03c00248440d540380144400c0e00401c1060250101451044602088284c1082c142e9045610404081001c5510413403e01c20001d4201c0c00c0c12040e1840352800c0c80d42ca54410084c503d2186079688000c140c1c0c805c400000003440400c210345010098201c92001d4614608001c01810180c80001d8182d2912205820080d6180320200010840c20103002c8070b4211440200050031501e04a0b0781c00b0108071800100820050248109110300010000c2450045030845100d4111700009050b0f940c0300500003501c0c00381d1030213040c00e90801d50b03000000f8207106441d00c00007440d40d058002c04500a2250f014500c110401d0440c40155044001e020707006080000040f0000d50022500403074241a9103c4c40402d00c00018408245100790540025940351038 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 573105332 1250 573104082 573104117
    0x6020304021c23030c0717010f0b011b023609060108070b070f0506012c061008150901061106130b0c0705011509060e070207062319 58
    0x8820b58a0040d030807500007034000601560300c0b0241105002d0b442850202204000c185984078588183c4814450010300140642c96601c00e4501e056001000784849041c05600105441003040824041603186481980700315400c5464450799000821480c0c92100021420b4899034044160380b007411600202c15981c3e40400020503003103144440105110343c508034509494802e64041e009140400003012024480b820701504a0a0b411400755035a5503035034000394045035164100c1250403108407040d080400054001c0c58840d080c094168580460400001c1358043c5008003611000d001d01e0500d586662500310317195001c0e06542c0c4844001219400400c0d18044005201a503c071140c4007804000070084854150441c0c410581c1d16100c403018a0b0032405054221783e1800d0034819031200003003008481d08110304464060380601040d454146040343c41d00300500414000c00e071200041c001e0218000215040311a51300c45071800c2c0000f10410f120b840702c641004100040041000304103801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 573106582 1250 573105332 573105349
    0xb0c010f02191701051e060c0d26010303080106030c18060f031802030d0e010c06110910031802100309060609051f0303120906180506070e0609130b01020313030602030402 75
    0x1140d03003d01c200b5962501001401c85501040d6266a004801007004a1034644006903042c1c0078503942a01c08841c8540380043c084403003070388403072802142d107111264030040442000e4181c9405a8402c3e000380c1c00c0c60016030182c000d07540d0784010002c6998505000c101e10440c0d070409030800d43c0c5c42e6000c03908810030050580380100311184d030400040c859400140e17400220900240101e0a14030b00507400400140e03140c003d0380324054030403401d0240503c0c03001e5200c00100040c2e80d0440c0c08106000e1400740c1101120f901000400c030401da174102074000340c54100440203141c0d01a180c00700f1480b0f0345584100c2501c0b02030b40b00d182d005480e2418048201980904074100c83c410340710030302100c1d1440d03c0003000b60a024921075409982c451603001401415008003120200c0e0b6106120400c80c1c41c40c00b1543d030842101d486000841005501c1743c41d03d054411503901e0f510080c180000710b210f10280174014902b4034800c030b0541c031080001e685480000018038000b907020b0280181c4030f180a0061002c00f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 573107832 1250 573106582 573106607
    0x18031207110d0906110d05070f03111009231f150806060301110a05030a050402040b04020705030d0507080106051b0304080d051209030702150702220213120506010b0c010f0219 77
    0xb9040712106c4030800c3d50000c2500c0e001a0040c404541c0d0b190107050507511840520344a01c00790044022010704a0070b103401500203d0b201d4a02c4409107009440301c80300500d0100d4000007103421500c80120102700c0c01074a2107006008810009030100300340041c0d4800c0b03080f50b20560490f00202c0030000345d03180a2142c0305803403600700141c84c035010045000801c1e6110041c82201030725502c0303002c074042d900e403540030b03048080c00a03000b15640d55850903c242d803500b0030406440741d070b410140004c03c1144a502800e040304c4460f1100380c10000a01160b0b100c0180166a288049c030051000090b488020000b0514001141e01c2e5030b9580c0d0401444001070040041624030658000c0084a0040c1c94554550054805120b150398032800d0510010380d10340711142440d030980f4001c0d407141820908990003081200034904401c00386942d80c1026941140d80110060315035000f28004115400c0400000d00f001d01059000198444d800c1441800302e810504170f0040420040ca0028841c1344c0103841c0c0c0105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 573109082 1250 573107832 573107867
    0x12050f0a2310420e0402030c070b0a060807050112021905030106110114162309040c020f0c01270602010c200a080a0306031406090618031207110d0906 66
    0x15442c03000030b035030840018180b0450441c003ca9018403900c80d1182588088000384159034a0419035101c0e4a0b0740c2140304103031400044400481c1080455100e4181110354031001380c02c01519050064035501031a07068040ba5580802074880307003004402c407088803a0f0b035545910b03459504082c0000c0078440c420054075001e0385081000c075015000c14417901d0784000c01c0d00d96007501c0c1c2e9410f04222165011000c000d50440d40e020011800c3c200084043d1203030351400c0e1010014034108140803681c840400c080000b854000000b07040c200c2d44500c40004d007030900e0452186c00c0003403940401e0683c0044d41d00100060b50b58039086201076034030100072940140e00402070040191205606911040514001040c0c29000180480c0090194201c00300854214034101e495040201d12a03031140801c07a50894a4000c840c009030350004000d20340220b0400000040d802c103004110300880303046001d00307401c0074070031148040052032004000e800210741e601c0d80c5251180d8070b020000f40002e20300b181c00000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 573110332 1250 573109082 573109139
    0x30809061b010f11130326030a0902130c0503060f0f0a06030b0a1203020d030f0e0f011b0903033504080d11030105012307140d12050f0a2310 62
    0x2807002160341d175070f41901e40202034524898540401c0700101803c0c0e20b84540001c001200b0412001c9040d032020751404d0090311400421020140b01c04e04550030019084003042c810710201d45070f41400c40f540340075180080c150950749804a0000360030440f29501840000343c0701e40b40321100b801c05800007c01012400402c00352a00340f0750340691556050310440007015910110407002c840720340c0001142c4000310302607660003800044028042c0c00c1030141100c100b40b00c12210501c4500c00c80c0210101e94150743c40000d0fa60060890201c85010014003958a0401180c08201000d20250f52401180b02c3d49010b540c5a1380b24140c0404d45603840c69407400302c40306000401a42c0d070403e084c0d440b0f0140355200790203441c0c1840c10320041401380c480060810741c00d803499000405c80004183e1050103080d100c150150705c18071a0b031400d4074000c079400260500704a01107080d580c03454208003894028041ca4000030345480410402c100002c40d801460189030b641d0404c01d01006c24070b00c48840795a001c9240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 573111582 1250 573110332 573110347
    0x120306050d020a05010503040302070e10081515010c14030a030609150503280f030908070f050f090901020702041b0e010c1208041b030b070e040b0109030809061b010f11 74
    0x60fa0541c0070310500d0f042c0a000030003e800c00d0320901110001c1c042c500c080344041d08140c60040030b08219030240895a209000840c0c6040d280b11500c0352243c60950030189440101d2001164000038448045078001706403250540d50610520140c01010419036002540c1e5140a070705809072414444410f64010030450f080c0308a803400b14542030784100180700e01c000c0b204141c10030ba401004072a006020040c00f041076900305a444401d00d400c940e200811100740e44d44400c200d4811000e188101980003840c0140ca003042d052940c2074a074081001c0000508020541e0045130545400705a4920701021005640c107006401102010b140902032808043c401d03003980d185000034441f68603010510402c1c00006003000380300e20309242c82e040523045078540140d6078a0b01c108040400e032094008a24080e04540c2d45003820302c101e4404650507580d010100f072844d01c400405034040d400d01e41c1c200008100400e055410b0072031108030300003070784000a03244041d100e02404680d010001c070000c40c0d00410030300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 573112832 1250 573111582 573111589
    0x14060a0915050f0c0f040b04030b06030606151603030b03012d09080304020f04091b08010c08070c1421041a03100b16020909010c020c0405100905040f0b04120306050d02 74
    0x6a0b8131500074040755a035401c8030002c41d44140510f52100c2d111200000d03022041007040c50384580500000e4003140c001d6100ca0040000282051640d80c0050303605000c030950f940d1854501c25007450003401c0c0001e0300701c0c0d11300201c2d0035550400502030b0b08620f06100c886c0c010240580d14507405504034010041e18400360381c2ea0300d241c4070150000e03100798504c1c904606156140c0c1d000c0c0701e4283c4e000e00082119002500401d1069019108851003075190551080c1c0c070390700415080348940b1b2240d42d0b80000790400d54505a80178042840700c1c00512850307810592f951502a0441821001d2610711a20340b07145c0355850804e1212141400352039034045c070a0004d642c0c07000c401c52040c0c0b004c84070195107500341400c070070041e400c0c0b141b8080c2d032200f40d850a10440080641c4241425005542520b0300c0008000038001502c4003a1840b0940384810319041202d00307c10b6018a400c58810b000c2d00104542949542d2030a000503070b000c0e900d0f82e21044880880c10340611854009100c155500700240d0010b4000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 573114082 1250 573112832 573112861
    0x110d020c10030f0f06180510060507020405070c05030f04030b090d0e01080c1201090f0506150901111504030201060807060c0b15041d1e0a0b1314060a091505 69
    0x71401450b88410f40fa1880c0341c8150020040301256120070001160384d9801818400d0301603005181103440c00c80801c0c000b1403000c152005a030724a84555241907526424040108001081d5804006100c10500001a0140010300000804404858940d030940c140082030281c0984200c289520a05d02c10808c5078201800c000044001d08003000c0b43e0b500c44442c00501d00c2540010120030707080100104030381446901541034011141810032565030f070102030201007800310b1000d1010b414103211142d10f641c4144402e0151075115015603148030388482010b00c05e06e005a500b24050707510303060f081c003d04504211490040c0303011301d014018034809840d14050480094845c0113003842c1c0b00d0305070100391140d400083e494440b403003804040315402d50103542c036000e0a548580c4d41c0d2220400d600c503003c00004004400f217800c440000826241e0045000c00781c0d80d1000c046400c65003004a2054420003801181e10420b01d020000c68084180c0c686421402c941001004000c2e2801e000c0c8a00c000c1800314 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 573115332 1250 573114082 573114109
    0x40615080106050307170708030d060e010b030601080a0209060c16030516030c260a1101081e0f0717040f0201140403080d0914010e0c13050c070f0305041203110d020c 73
    0x102141c80303440c0f04881811f01406800c485014400041d040c1c13581c0400f94081001c40707a0060704200682d80740c550301169440141d036030340e0008141c100841d0100b00550b0007089092001440d0340d1521110145190500880c0b40118042201703002e020810f0260611054502d6003044074038001c0c0c00e0031603a5004030000180980455128071031209060807030214a04886515160101c03824130100d41307050341303004203004881800a2844404510848146020034100326070104d900a1a65030324480320703043c40b00052034001001482c01e83e4102203005841c030140243d0003184800c0e0a00c04900015004400352145900c0c20002080104040384100c0151600c00007607400104024046041c407109856819103507240a518080000d8649040003030480403108003070b0340c42d110000503044114116501111290a5104104511800100c18000600405200b414aa410a07403110301681040b04d0303a4070210081040e01081c3c1c0440030003008240107800845c40144010001c480205584104144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 573116582 1250 573115332 573115349
    0x70515271302031b2a0705030c06070501060308040e1006050f220503070b040e01451803020609011b0c020103020403080a02030307140309070e0402030f06040615080106050307 77
    0xb01141442c0e44030300481100380349200c10903803035040c982400800551511700444d0000c1d4140940c100d15040480c010b400c0380c1004000d00001824441400340310350181800300d4095580703000100010740800003600203049544510121460320166104951200c1d030400d01c00d004041c02070612601d0044201c41d10911058070103070785144410002c1e181c145980c6c0029a05015150f07001c185540d42c103010f4411a03a503051650890f983c1c4980c0a12010f604007101101c0e000d050002d5041c03506140103030b2030200741c03110310001b8100400c0b01d40801c442c00040070400d00c41c1c035811003500341030f4104000d54205680400800420f030040443c0400c10300c00160b54000e01c0182c00a00d429a07010b503050f20019a00320000c02d0362000c0e078480c002c0d12a84111080404201e2500e444403c100d11201528442c00205c002004c150b801d1441c05aa0400b00400c126850320500904040d1001e080c170a1034040e9105500201d948102034848001c805442c0d0002440e036803400c3c00405c007541e00004e40d0f20417142d000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 573117832 1250 573116582 573116587
    0x50a0801020f04090e100e01020a0f090e0a0209270609060105090a0509092a0108010f08030d0b0d080d0f0605040b030a0b0c0c0d02030a030c090506070311070515271302 74
    0x441721030808002d6200c0071100751030680c1d51449a001034008011040c5d540e994907150007280c40c406d948162450007840d094100381d100203004a0f526034020100d0010007011014507011800c0c2030342900e1300800d98403030801d65000030b1040505050308500c2e0000780034248503040840c0c0f200480c0500c01d0911916104131500c0d0040b0303402c0c200a01000c5c01e8035040b2600f901c401c0702a4244c5404200e10740b210b07940004c008100004803840c12983c01010f4442d143c002d14900311a03030718614050910f03036018980c0714200101110004080700010a80e86680e200041070641c84040c08138100c41460307200c24003039800c00e00820341560b004102448070540c81860191513840304c4a95150310f001da450b1504244c440e105212900c60b8001000e0325030181103550500c00d4008988045071107401c1c0740300711a0020010f100e0200040e0083d1000449c046011007103c2680380e942002808644201030807070501c11000910304410fa4202c10700c080c00812080c0f42480703032140d500200380f8502d108082083e595502 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 573119082 1250 573117832 573117851
    0x130809151314130b06042d0e0a050603010e07050402030a0209031204090b0d1e1b060e1206070c02121204060f030b1504050d0c0510020106050a0801020f0409 69
    0x1480c0964912401c4091045040c1c1e46a10324080d0260280c205148215005042d00c003c001040c001c0d0b04200320041c04445c14940b9201c1d01c0c901000c000643c0e0311003050b0b518141d000050b10521200001d141e4030402420b03d0030000e128030104c500250105010782d04144107801d0312540000c058045500c180e800581d40d83d50410004000e00a8980c2142d040c05420b01c4010780318101e4025000307444540038100305207910602049882c058114005001c6056100c08a000012880c611418140102440f100302140c0320300b504000700580e04035034003180b181d269024060802d111104c2280091a000703200a041020020344501044140284905940030402030585014040030500e04c074110801c5403242c0d2640d00142c50340c814000d4800c0060b1409004110514020980180f14141d00c2e0b4124a414180340a03c0809441983d098441000072580018291100e0142801403001c59000091007402c0000b00884540746500500b020380c01804a4004480c0311022030302141ca1051000841114 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 573120332 1250 573119082 573119119
    0x106140a030f0c020c030d03091a1305060117150415022a06040605090604031d0a0e010b0703110d020c041e1529030a090501140406060806130809 64
    0x804051071080742002c400d4501c0580000e10b85c4007076082102601c403441c1990000b182140c040f004043c1c04000106e180c00020b440308848107412103000300c1001260700d41c2e512118a0200280e01c2070150400403c82aa4a060305000e000b050f40c007030031101a10f41c10a9120b080301110848552a04145d00180300d45084001c89141580800c450310f03211000451400d502d41c403094101c8040d181141014002120200701081e500e01c21517042c0c640c00d8070200000016111a1212001180c101e40754800203d58a082001d00d9402413092a01044c0d94501c1481d005101c100c2d00000030919900401c0522400741c4c010031800e1041c1000c1e2400150107002c0a12816208041c20001c0c9070741d45050900c88a42050f20800c005480d0f012060105459900b000d1070300220b15141c66850b86142400420131541c41c1c0e0f08085441801500003140c0034100088004c0d841800351002c6541036650f0701c0401900405110341d60b4004142c070310b1000d20328401d4550b150103104aa000b03920901d020300c90030041c20f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 573121582 1250 573120332 573120341
    0x90f060609030f160603060e0a0b060c07030501020418050402150d090605070203090f062706120c0a09060c0c1815080102070b0c040b12100b0307050d0e060106140a03 73
    0x8200070116a011001003d01640b1840d9402e0345079100348244002080c254042d0042c1c0e01140c101c82c042100a65401040c00000d0040c240e140703500000c104107026074008200041c002650056000603640e61500c000ca107911000702040c10116401e00042001603510440f50304000c1c0e07501071505a0303410309501d1020080c045503030010552440c04080c032041540c00009096440c100f0f440d918030f5040c1080c100040da0091030010040c1c45500b4510351910004800c02c000c820394054411800e2211041200c040041d003110f0b414506500400c4096806038058103200c000d00c4d1605101e90540e07900d4841c560181c1c214000c007114080003401c41c041580c9903901415007941c8905c4440302c2c043c0c540e46414041c3d0700546080d03546002c2c02012039200040d010440e0201c0d5451045030b480c0560307a884100580a00038603034082c148004c0d00018880e0f000200940c4205400c0e0341c1c0681d96521390b09203c0880780707440500c07480d941c012070060007641e40040080c1c00d03010550030010380f5160603280480140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 573122832 1250 573121582 573121597
    0x100510030b0c07121d0301060e07230304030c02090f0603060406020313050f0c04060801020f04120302071a1306023913020301060206070c110103181e0b0a0b090f0606 73
    0x404c84200382507620303900420491092802c49440d080188081d4201401ea650743d000328914125a640812001801003031315001e00c000941741d010190501410109030354100712806c2e00401c0d24280f150007185064040d4503400488500c41516034200080429035505000f007004240e00d500101040c80c81105c0c40481e1078169100040722051180500c0003030315003103ca420300303020b18102980416581d00600036248002c1291071160700b011300d000d01c3d0070809a40307074030250154042c901000c60241c000b0034080c003618004c13441c2c0544d2016140061541820f4540c03154085400c26000c07819011511114145c0c00c201c1100001d80030f0b801c0c0020311a400c082e00c6042c540c884840003080344d80c00c0710b81e009103040751070740d4090720400e07612504191050809502c00500c42002031051004a40c001d50080d4549000090300072400740040d0340307541b2000388107455038403c4204003000008000da0311100b036602c190424002e0040c07030341450126550b543d0207010403000810030400941c15440740003d03146074 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 573124082 1250 573122832 573122843
    0x7060c240f091505070207030317060103060315050415090201020604020906060f0403050604050c100f050c161205010e121b1005130b0105010e0607060c09090e0f100510030b0c07 78
    0x10040300d854803e040c04054110b01c0c51450620000988460020480030b0407640c15441d00007284160b032408107260f60004061905042d81c0d00c10206c0072403080302542451030801c400000302400c00303081002402901e40f0150050608050107900141da0108142b070304039505440761511500c40034005109030040580c64200c030b5101080001c1800400281d582c000e900030b80903500e47d041e0550920807160254480400419602020b00a45030b204800414040c62140d050380c01c0c069499500c22103502d43c03580701c40c0360302e4019200402400300c20b12600d01e502200c900240032074403014946068a010354694040c032040403d400c00e400c00030901206241345081c4804114500e40010503021a590706141528007210010000c1004d50041116a10382e090081c11582040381c16503440000d05008401e000c20840c182e000000e24940b40d000c2d907007403031a50002a14a103403045000b545800c5441031090180d505000c00d0001110b20b400c001030699400a129800740d079a00614107843c0d10420100414 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 573125332 1250 573124082 573124091
    0x1124030a091202011e0b090c0f0903010914150f010909021206070816050702090408070f14030c0c0a030c050f030304031a01051206070e01110c040e070807060c240f 72
    0x940c0c035419400314100ca10917078802e86640700c20240345400c03698520840f03a00403240344041611000783c0740150125140c0034000740e24144d61880442c2c20b6403c2c895044480c15050300b05100011824070100d0f000704030a03040f540041c6402140c5140b80c01040c401d1008444d610843c08065498003c2900000c00c1a20211401420000790041980344120b40e089001c1d042c60000c62900b40c032940803101100e800504031122500c1e0b6440703400b002e078440c41d002c44a0508450329800000c82140c1042d0a405000e00659100d002d903a07491400d00a5540e00e90f4400e00300700405000043d6445840419100b05485129820308000b011034036520031a00060140c6c0c102900711481d02c1c6803120301c54142d40c1d0030303500c0c6103c030030350072a80c1a51a0015550480425203d409500c2a5407140e00c05090b00c0c200d9008991030112001c0101c0e04503050f1841900858020100a00040310200102c400030110f52600c400c54860580f50245c1c5504100e050100c61440503010b120b10704000d4001000711400c0c01020072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 573126582 1250 573125332 573125363
    0x6100f050408011b03110304030504060305060609121f0e1c0e151e0a0c150b1c1208070206040305132310140d1d0d0c1124030a09 57
    0x201034902c030902c95130019040155000e5445010816203008a03810f807100340c149070400100368090140140410380100043c040d02c01c0c15a0341003030058204103e0000340c01d061280c54000c045c1c2042103003000ca40c0c03d003841100030041400041c22005145503001d9940c1000045100b124861008021564010504000e10040e000440c000301040c4032028043d010305500c04003418000d00400c242c00d4042041034007110080781c0d510000700814002d1003800104180050001001110944000b5111016800c003003020003803144100c64514991742480b000c07610f81407034020360720b4400400c002c041000c0801e04802e04e541c401d000c40094102107070240702008801c5044d207030850341c111a10b846203d51a000141c02c071f02902501214002c2e04541a282c8244280881c0181024000043c0c6c441f80990200c103846009000d00007034140d4a680c0d5801141e003c2c00c15403621418002258880c1c0303030404411482090010082ca15040206c01d601c1d140c5d6a00c030420b0005001956029004014031a6480d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 573127832 1250 573126582 573126611
    0xb04021207021c091a0703090305010518060c0c0d0f0903020d03030911040506030309040209150f0406090e0609070809030d0504030e0307060c0b0402040203042a051806100f05040801 80
    0x104801407041e040220b4001c0f880034215141e042c0e621802c403000c1c8500c1c1700c90600c103c03034000903c00680a4144001407603030343c0e99107a00b1260111b0708110a01c040500754a40000d0500c15a6001040900814207017891480503c0d04d400036403030b508080c400c1a110740880c05002d40b0640c0c0086400401a06204140c3e003005005494844000c075855034040c244484240b03001e108040c050074003d0021405c025010007440025409841002d40c0901c03469052001c03890060010b042c40707164294101d40743d92600b03101500b0228180c006a420702001d001700700d070703685659041e1036204445250000c040d44410b40140d0440c17049000c44002d90b403c000c104028113800403c51044208140c5c03c989007070b5038465040f507811600002c010003102184d00810003524003500515086030040c1280c00c10001913a0301d20f05001e00b000703101c0b4044c40707447c42c04004910b06000d222801c442c0c070b505807928510b400e10020719258040180d400c2802010a41990194440c0c02640c025050303100c0200712150180325031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 573129082 1250 573127832 573127843
    0xc021c05010903030e0607020a0212120309070e06030604081e0403020607030309020f03030c03070b2d070f030902091810020c0703050607300f0c0c150c0e040b0402120702 75
    0xf075001c42d0500000040310f00300041c1191140a00750301403c0701e00002d82c01c00c100310640690a09861081c001c00000503042c860065004091a071300400310030745400c50155020200400442c441d8200c007081001041120080f20080c03c20017400469a00000409039624056074201a42014001c143e640425401d83d00c951030150080f200840a0300a0604065981c400d940251049030024441e000004003a04001a007141c108803002c020724000f16040749000120241480c801c0c03e40500b4045c103643c00c01010011040945428131417000150046500c141014042c40000505010481d03034894083c0300b032161095160000f9940c607283c0711400d650b100d0b951700040d0fa0600035400481d0b0302500415105e10500c0490a81005132001030b1501c80000d41c804c0015040c3c0c1da01da4032070448042c1248140d12168285840d401c101c280e040c1010030b140b44005070301c40a1545002920004580c2081002c010b0352000c80d40494020a8800810040e0180012030542c0ca0066024000c501d90080b65 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 573130332 1250 573129082 573129101
    0x7110a0c1202130216260a05071101180315060308030a02070b0a02161b1e0603150b181206040308090d0201091a071806030501050109060306050f010c021c0501 70
    0x3e41e4854085200d03c294101e1007007008401e5560003004a0b0400a40107610580c0307540209480b000320035858a101908aa10017034030b007800036600149603c208480c44c0015801d446080c42c140100020f80003008580d007174a40400340540300c0e5400b040340702031890381004014550000c81e80c2d40700d0030f240e81110041d41090b2001c64600240b440000c0d040c0c222f601c03d5600305644980301d001c2500142d10380d8424060742c0354045000c040100d07804120361100700202d0003464076040d140d00c0450b00d480401800c4888402c4400101c3c10322041c100080e01100b0103684030000102400d602001e803590003d030800c60511151101c50058030304120a0540044000d0f12801c81001692201140701204a080792900380000741440c2c3c2103286031800d1082c840e4416404000341c1405103480d04c4010520601500d182d120b03500007a00c5200601c140d582c44803555000b801e40b0f0400348012400c140016040704150007030281040391a0012070b00b50b6880000011120440180e0004410001d00b40503010744413003013 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 573131582 1250 573130332 573130339
    0x8072a050d0f0824031905030301141206190e0123010b0708031611010504050c01020d0c0b06040c0c022d060c0606010f11010c0915050a020607110a0c1202 68
    0x8290b10198040c4022a00c64010701118041100351901814140618a980d450f014822240f514160100d070f114840715031070091005584a61412102c1108101d00c801180e01034082c256505031404000589113402c2140441e14080700004103041100074019031550b01e40b69824420b06800150010030070500c1e801403001c114400e80e88a0031a407440b84513122001745958020030000301c1c0140342002041c42211076241490071314004c02d682a080d201c0648064030f6581050303004010560301003080303070a115002c0c00c0c2050417244c9602c540724401001800d1074041d03600d50300340070460341c0f040c4c00c81081c4960050224103182034100044240c42c240003080c0c1c0c05c0141c1c14007003802c94505101a902901002d0000385840d5454400440e140116807038410140b000d0724008441302c10342801544c0c081089580c81c5902a840c00301c0302c04102d034a2a101c1024000704001c1100c020b035000c50003070ba000c0c815051684d041644944070382d1400c81030383d1020b00a210000c0340481c110a0080021541074002c5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 573132832 1250 573131582 573131597
    0x1081506121b090102120a140714011a0a050d1722140603060d0c03021e0108060a030b0f090f0712050d110c0f03011407110d0c0308072a050d 62
    0xc0d4910840348600303e00d450140e4003211440c202c0101c0071005142070283c914003026800410301c0030030302540000e03c00300c850942054401c6035201013441101c100d010010903000241da640c0c0040f607110300351400f031240294240076002003409420401c80403e25401c131503865984180341740d40d080c81295016100036804003040001001c1c04000c0050b207280c2001480c144c50340e2180c90402030010619502103a440d140e6210001c003507501c180b0444070b10311f0140304155482a101d0001000f5040c018130161144401c1e400910104d0321540103c0d0744011381d00c0da9880d5607129042814940310003484400068860090003081400c0955041e6002038407030400c40f02e0f804d1210009840f4070050039403900d0281d00c1f264010301c1e40e21b00400500c0310480301a000091b61010300c410003160590841e074a6003c1942d00d020041703440c0c42003201241c041810325020144034031130380c1e00502044003e0014010000a410000c2e0001344101c130582c2c500600081158035010585044c40c1c0ba400b0782d46210000c100c00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 573134082 1250 573132832 573132871
    0x91c02010f0e18061c08040f09020c0715020a05030c0d14191b0b0c130803120402010305100905100e090111030420060706060806060409110108150612 66
    0x11480d021001200070807001480d4920350421611260051100da4010403171580d20702c10840141c114030f02c0728001c004040d941d40c00c0505d400c0032000c0551141e001c66104100342680c09002240e01c005031540d0794004070314034000c1001249440c4440701c003e4210b010004000c100c9030800140c51051003645c0c0c4030801300c1c800707607040304031140103e004840a01d000705408c1d440b03543c880c48124450782c0c0b403040545000b00042d02c442e6443c88085031070340c842c198001410041c0c1072034078007140020907102004528004040b5444481040060f20003418191074102203862090f0040d1f1a00181045c007a0802c885d1400c145100046034262080a41420808001c201d250303406010318000801c231003803641c2c62b54984ae5610760403d40810000300000d40c5001d100866070391a54020140c190060802040c594181500d140c1040d20180c40e0703078456490142048009090144135944284007421302e08000d07601c003860460661000403089501c8ad1002622150721881103444da406100da010110307807100030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 573135332 1250 573134082 573134087
    0x203040302100b0306150120060f06040c0c06020a030f05130210081b09121203251d04110a051308010629040801050106050c010b04140615091c02010f 66
    0x1002840f098143e000b903070000b0007503c05480c0003484d004061400041c02e910b50940c0d803015034903a81d1580c01d06e42280043c400400d560001d42030b00301c0760489081143c600840d030f0180c15003608001c0104040d0b0049450184107020303921030b00254821100a01c118600300c151504d0404002074202e00c00c01018208160f40307032054103001d100d600c0040700d8442402c02420000e205401c0705490560040b9646c01042c80701d403040c490702e420b03040198150f81e00e0f03091206242c001005c2040c80d4455035501c1480c542007050744081d80d000b501000c0001c030b0582c280c641d40804e024100401c165190610000f5046480039400801020040300a0520001e420f44840b12103090f1070032072013010050f0040e00540721920405610941001100a0407985029507458001d420f48200740d202c00d000c0f4402080e00f5036542028040d4051006d000c5404021120714099000303601c80c00541820b0160894640c0307000f000506504590040e05c0081141c0340c402100011004044100030f812030018003940c90b16100d0031f0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 573136582 1250 573135332 573135341
    0x3150b090f09031615020d0501060912050312040615080705012c210706020a020a1e0306110f041205012a0302160b13050105090c0303160512030a020304030210 70
    0x10000c0003031813401210000c042a801e0b18100c00307881e90074600b0aa810018028801014040949600030450350315000c8060310104413940918041120320300b101000070300100854400904842c40250203440b01e080a070010400c0707101c044001070100394086101c1c035000880e00101c030390990742c51454580214030f04c1400840b403d103a440f0642e40941100c2c95103805260b81407901044420900032004c0030030260300d403031134692200c005070b04000b902d2020f41c10000d040304060084005400100f9119081081200d002c1344005007070b0b255101d480e0790205004004071000308881c111140d45030f58689181d05501c1031a520300325499840c192203010300300070138030210b5121402c00b17403c0b16610032a24401d030701951204102c03814a640012510780080c01d1041c185001e006144c4480035002e01a140150031940d010b4401d440c41c0d80001407040007580c0010850350a0a4111848507800c81d01d45000303860815050301d0200c01910100421940480f50340c0958440c0380a07600720f9000600c0c229000c002c0380c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 573137832 1250 573136582 573136591
    0x30f100608071a0304030311070c080d0f08160513090b0a0806071d04150b030702060901060503031b030c0618061506090f0117070324050315070903150b090f 69
    0xf009002401c90025a00955480360080c10085000c0140745103251165015034001c4541c41d516020500c2003000800210841d01c105003000c40e10984200009005c070003004152403010700041d82e0440e0719078452000d64402c0d03881030703424050007030729826600d0241c612030351224019200920002544180001d006000b020907407a048503001180c0140c284105150794520303042900c44115001c1911040d055000a240c010310329a180d00300210028103185020b0800d544684c10804140125940481110000d88a100c5548120809002c0306810340c043c0038581078080c01a03100b042100b01d03206250103545000031003515800d5488855464014560758885500005c0510100c501824071301400b07112104141400401ca9482c2280b203240c1071400c555250001c5e88a61141c0308050389101c000c0700b04400010a20111414840401e2307840814000d09200742c18140d01040e0704501030b54159001d141c0083c211040b42610141c002c0151004030201802412500e001502108107650064000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 573139082 1250 573137832 573137849
    0x91a01060509060706020f040b0a08090a02130b13140108070e090c041d0a031e1403070305100b03040c06090b070f03120f05040b041e030206061e030f10060807 70
    0x10001d042c1e0030b01855411651080b903644d0b9081204140d12142d035406040180715024500ba900c614210000341703240ca0261007240680d00c000b451100680d121034440300c1c212848440000c0c0b04090b040003c206502070710588280b0303403034400c854003441e03074064100381617500c14801c641915036a144031080d0324400712031540d59074200b03e4210009241542000c0c01d0149400905010401880c01c80380c1805a034040c1100031a5084c1c00240b0300c20100b22100342d041e50f15003407404606c061000680402d1000402d11020169a200000c1e07c0070310200b0b02d0409495805e02141d00c910346454020040c0d209401040c012a100d8840001e00f040000100d40d40183c0c06406a5504040340d83c0645101040154841000b83c8807080e0442c101c582d071140a10903401504501c070241010b0a002d000c00d220b21000b074004821100f8102d01090300041e1880d003119060b10800c12030741c142500b0019901a111584d81c0c507005000e40f051540c2000a05040c20ba0461201000700c20381d0398101a603100c0701481207014 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 573140332 1250 573139082 573139087
    0x16020d0813080d0914060414030c0a020f040e06040b090634090504090c03110306070927020723070501121802030111040f061803060c2001091a010605 66
    0x500d6030000f410715481421004150011a641c60408036440b072038070910b0a0703001c41c00b0401804071188022a280d03001101440c50079209001c1c16807550000034010303000745c8810b080106681c40e59482500c1050b0701c4c01c2541e8540c101894145140d07d0103950480c42880b40da0302041d014070013020b00f0f1000d50a80352008110b040c5441c404002911140e024005000c1940c5c0e0020382c40d01c90b4001c0d01c0d5030724400c00e5040325650451811115003061075601600942c8014200416541c000000c54107030303401b5031030040450440d00c2c0c690302e500e541e5506403102180003142642c10403840407540d450301302000103129641900702030007650321044c51184a001a4a8800303841103c103096100c0740c01010b04a592540c0c1c0c0d800758005ca425510180c02c51680420001406c02c642848409520090301051510a014820700c00b04901405a10b000c0502019507961121840a003c2c403400d210509200c04200301000d04840c0841c003c3c4560941038411020032200010000304121a0354141c4d07140d40c5a060 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 573141582 1250 573140332 573140371
    0xd1511132c0403030906060b0706060902090906011112120f06010f020c0613080f030712021605010e031f06060909021329030901050601031119081003080316020d08 72
    0x30300e0712806030040d818140e0300c8003040b01044407400b0f42d5025281140c01c0558900852604030101c030314a80c0001011407052007024110b955904041d43c108002b407038116000c0315040c114a003086d0b076a101b020a510000101e01e003041480041d441c0c441c0c400303140d41c00302c207a980900543d4000d85244101005800c480a4640c00d480c0400c040c220300050060018211500d03040d48514080b00074807110156030021a01500b081007040c080b001c250140d201a000620410143e0a022246405024144041d06440205540b410040302c00c101c540325841c241c3c443e100c0b40e9120010502c2d40544000604003280104020f085402101c074404403131805555624545580c50b200140064081502491120121030b4070b0280800554040da04400000940b414410005030849941c02c5032094902024820243c0c0a5001c00c0e4882307500701c060800c03868550b00c5180070424031004d80c000074496a404010300010740c1c840300425886607615000c45076401c1c50b03080c054408120454810072650003000080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 573142832 1250 573141582 573141659
    0x302070308181e0906030703170f1204030908060a0908040e0c0403050610051923061605030d0501090b0d0312020702040212100f060e0d151113 63
    0x740744825241003819014103410002443d582d2010f05121440100c9107019031041c03512060464000f071080b4020300c80036145907181c1c203d201994100c0b0b2031780040896502d60300c865a404840c51401240845c401502d0b1a20700540000f41c030b80101485486000d0001e030f441c413002e1254000c60b9401c180040d050038178140b1220758541c001040da04608606020020008a04001e124050105881d05032000c506260600c03484140c00c11040c07811040c1002c04001100d0091f1400103004040e28860041864a0001c030f006403107100a54442aa0746076000014000c011002d07000c4401d02135821301160340e07106044030a030f030405171f08942e20142d1a5513540010b4090380c00700c00750034411440541400300c01d40000b001c9800030752100040000c200100800c40701c143c641da03c003500e5a4000f00d01031a0414070003d00c032070205203c2c14000c1e050f00181d08140a005801e144541d01014410311542e4407944284106811881d80001c0e0445043c0700030852040000c2040c04050345c03a50601407160310340010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 573144082 1250 573142832 573142837
    0x6190225050a0204020a0909050601090b12090c0a0f030302010e01270c0e0c072618060d052a0a020d1b120302091507020a030305030c210103060606020a0302070308 72
    0x1c4509104401c01c2c04010b072a503001400c01242e141d241c03000c80500c0c00d80c0c0c040c2a900020816070400c00480000d0116807030040940300040c0720081008044e03512044000d191801d0780c511254819180040060000030840d00101501d00c00d60007404208035801200342030380c4c1c0070721006000030b030b0000d840c4100001120b8a441260f011744800c1540d107907581080200340006980f03180c1407810000c0c60401344042030b2814900303140e016a02030440d0001e41182c00217805204c00c1c202c410805003076110003c2da103910940b030600181250412a40c200705034032081641401d40c0710701c00c80c40c002c034240c84049100c9042c0c0d0b40b00b19864025002042412004a4140b0b59001c2d1001e4407600d54905071000c9204945002d180c40600e480043c2d548074182c0410101a440440d041d40e4458200704600040e103411881038202e0343e00d820138548a49850b034080109015240102070f0511100d602e042c80b031095088814104da025030000c100703d540310081280c90b4004410701402681c0003d40c1000004c110313100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 573145332 1250 573144082 573144157
    0x20111031305070f090b0a051008040206031b132c27030a020606150f09060a1110091a0c0a0c0201020705060a02060103061d100906021605061902 64
    0x3a03680d265140c50004c03a05050b1a00711111240c0d42d00c044c0704190514005070000b402040316103c40070b14861100400b90040140000c1c021407011010540220392a1541c0c005908185605038a500c2c1c12000500e01e14954030410003150203402d0040b110901024400c625648000ba48682d00e94070703200e100c0403200204031032402159005103510450401440504140742d8181d015240e1030030084108544014814070300b075144502004606102c00001088403c07071070302500c81540350328030058292a1440c83c05c001800d54000c500d01c0b142580c1081c0d00551000d0b1140b02c01d0400d00b44c20340400115000304440742d00980f0410803a00c420140a008000c2c0d04034414411035079015118400720b4103503004016900056170000e0018001c1041d98000c068900085030072081c49900307907825030f6a481e850302c0c04a4a003036686481000c14006503404445031100c54420101c0400e08520300146c0c0c40c101280c00400f0b0032481500045120402c1c000c07a581207280000d51124030320690841c00c440044541c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 573146582 1250 573145332 573145343
    0xb13030c080703080f01090c0909181424060f1905060c03040e0a1109010807120912110c091b0433091d090a0506090105160201110313 59
    0x2400080011000d5000704046846544c80140368208401c01200e56001a04500805414425513103042c581c8581c171841201c454240200d0743c0c4040036000c950703000000c00d0250070b0700103030200480722490001d0a082c14407041d0310004140013112035858100c0e14181c40e03003903002c0140100400f20303150928040040e0116030880710516a0b942c1d00142d0f0b01c0c0d006508000490b000480e007044a00e086828290303100c0d00b000d905010f022003005003140300d80b05040c15a07050100213001f043c3c1a51140d1854542108800803c20030741016081030142000101c80800c001050740410850384640440c988040000182180d04580c4950b5103801c201800241e0344184582c0034040082c14000f00100c17804051207031046800001926071684030000c0c1010b07240428801d0703000040007141c4030760303201207600824030000003940e0700c0b07407141d1070308200c0440001340980c07046400f4030030090320650040d40116648031a0b9201c2c0c40b044403080e4280d810007000c9802e00d146c10310002d82200009050004405d1181 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 573147832 1250 573146582 573146597
    0x1b030b011d030309040f05060102010b0a0e0115050d0c05191e1d0315061525020f031015050a080703020402090328030f050309061305030c0a060f0b0a030b1303 70
    0x1213000c24229014105c40d03500e90303500c0d80c06120075540c0a101e200601c82091b180d0090282c1041080c0c080b54006204d06544110400d504403900762240d8203492021103a1503044c419500a0800281135410805481c21010600024100c9040c001c426030300c048201003c84031500c0b04444010380b1103400451480680b00070440c08110166020f01c25045c079190610780010940c201102030091400400e541104040d03c108000c00044c111080312810300005680c103003050024a20109075980800030170381d0703050300c138001c3c10310009002908900c00741c80f101091001195a21010404c00e078003d48142e07552608070309030500c054100b40e001008102c4000d03040b540fa000d055188003c0c52203170f41840040e00082061284201035100f0590b00c82d000c0d151810314150700308240c4407601c420002e0144040300c54111280030801074240151141c059040003680e140841a0409502411264031000803250ac1c208940360b152400d040c140f010341b50040789600c01d45e59410000d03101c00c68810016000d0140c0c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 573149082 1250 573147832 573147847
    0x801082a2209062a1d18010e0a0c02030f091e060304030807110102040e07082505090a0f0303050715060b030a02090f1e060723011b030b011d0303 64
    0x340100406148a00c000159645481150340040c114100a40032801080a1a2141303180d104500c4802d00400e10004003040d4450340001d045102099058800740c5034407000014041c0c20703901e800e845030b017071a002070040d000c49030b070126181e1040030398450300c69500b48060002418040c440f101901c0d50540140030800b105070006009410442d0201c00288554040111086c0e2000c4008150400f880c000c0d0708250401c49a200390001c004d02e54410007403000d00003140c0f10003a5890810390105112041149400d0380c070000d2080d40094517041c003074440004002050b10b03ea00c0d002040740c0d016500c1078100501540c80c1003600f10a012841070702c0c0e072601d5000c03032a5410134000b140100c041280042c0d40703108020500413254400c0b10360a04c2101105203030440260703002c64a40300c00300c00b1208140e54206626005600c681c420203508400204903811407810481588907103040300000106401f0340d000c0130740c00c805a90113501d00d20300062140800c03c01944200b0b101c5002d1400003002d907400c0c0b084 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 573150332 1250 573149082 573149149
    0x18170a0602040b031e040c03030302070201031b09060f02061006030513050106080703030311090a090509070f0308070302060c04140f04091e02330a090302030d0801082a 74
    0x1540041083c0c4000005000204443c00c1d084403100c202501084070500e002c0c2c40d001c1201d0200d110250a150f00003404e030b021617100e940b080c91840031501c0504021100303004000c001d040c0a0051030089560344d661006881d0001520b81d11503841840003014580c1040411000b4000140c00c01d84011000c10701c6800003002030054402030140d140041004a25504005050320b452243c011840801003180100a032508003a05003070741c8002e240442c158442407401894008194854003c031640032401100b000f00c400c0041c1400303802076003210115110700b91320b1030061145205110420f010104840d40c0c1d410040e842108890001740005025030550301d40407011f0508101000c05190150328250441c54200c0091200201c0c80075a58142d1a4012a20310030841c003182e1040d40c0100410800461849400207401455026054980403504400f0213007038240300b03000300d03200790081c980c2040260b041e03070807000c80c03501c1c01110075400b800c2900c00340880201200101c8190500c0b69211070010170 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 573151582 1250 573150332 573150337
    0x206040e0f06060405030303060918010e010b0f011e08040302011e0207021302040605041701060b0712030f0b1503190c050a09050301090201201507050c0105060118170a0602 76
    0x1400d54190440d514024480360700040c0700400441c840c060a0106100c1d03601c002044d283e2104094881d61450b40300e2105600805415001c0030b0790301d608016036400c3e040410b402540c0001e60946161903610315001c015070f6181a00407142c005010745041032045980f20344140c0c1c0c1c1244c003a0000081e03101005841d03801c1050850454511142c0000740394045041c4000c0400f6540c494000450406062450050641c841c0c0c0c030078003002c08085103007010305074401c1d44410f00406004400a5582c8651700d000e21002045444100101c1d2405a07003081e80c0195025451021030010071091031401c140b01031844940004e40030080c42404210720a400b030300180b152403c0302e020740c1c589a80b60151500020300c20b280a8100034020b904121600300140d80001200184a42c24440d01e820b03000d050b83c5052505036614100e40da01d80c54642800851034008005100d503549610090100d550f4250065500050114810320361100b07480781004000406100d090f02c030941981610321201558807035000340c0c0c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 573152832 1250 573151582 573151589
    0x50a2301080c0c0a0f11010f0f0f0e10020d080c090d020607060b091503011a0d022701143f01090f29130201120204030b0a091101051215030a020604 65
    0x6000740d05006043c0042c5003801b0405490910700407425440d0030720020242404202c668007407121500440340414000e49800441e00400742c4100700d180140e05000b0340d103201050354580400c1c010380220300280e08400869a0020002e44170160110559090140d59400a14180c1d08c0943d20803c406055417104115809089900f00d40700d1a41c069a08045c2103800b45100610200da000283c00d0301500c8424488059640441c1c1824220100c80200d06121010403201034030900500c00208084820072400d4118107020344543ea000300ca0411001d80f1407801c142007003003507900300b2940d05203072500d0300c2e118084a80c1800041428141c036a00c850244400302e504547d4886450903403480380c0c183c030b455401001d0002d002044c003801c06050080ca1700e03c0410019041180a030f04550410090340c0407580250341c00944c0041c24a886d4050300002c1503909412208041c4800d9018125032044058543e015504241c0c8541c03505d41584098004a83d00600c40d0103009101c140c101682ea10400340006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 573154082 1250 573152832 573152843
    0x90203070807020f030c07032901090204030314030601301404110121020a051306050d0b03030f040509060310050c040e0112080f03090111040807050a2301080c0c0a 72
    0x254100b501d00641000d1802ca401825507109002c4281348510028580c404c80c0c0c0c100c0083e50b801804240c0302801203804008103004d00c82c0360000050303036917415070041040320b02a2b644c0042244043d0f0100000303100954450b40064000703900c0c01900c1c51008482070f01105000e01c3c80e1030003186490010141c035007003800794111011030000c00080c04822524400304c02c1c02480c022a6011a411152410b810b07010b400903030300ca50201e02d1100b0319003d482143c0c00b41e4203044034a02007540d02c4500410a034004c00c034011515050400c041020b00b000010b407000214501402800e04d030500040c000d0480004002950603c640e4029401d0001c1d20721405004c0d42c0e203d4421941e640c2001c00720f50000c6c1c1706a00050780880a520220082040d02c01910580d031030104070355a980c1c8840d0452809040415400c06007080c0006e000240320b00009401c5003124401c0d1909880180d07a100c004240b402c200035015482454070041001b19031042038116440340001c08002c1c101503517060640c1c40c04da1441008c542 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 573155332 1250 573154082 573154097
    0x80a18030212100e0d0c140a0b0c03011d061f050d05040b040203071205030906160212010e0f010b0a090c0c15050406050105120706030b060f030a020d1506050f07030909020307 77
    0x10400b2040c003c4c2c1030700804a10003840018515540140a5118500d001d051240000320b0031043c00000c0c485446010340107550300c2181d041510207101b45030310a10030041d58014000c0300c0c08080300591440751103248010724070444204039420700064a20a43d0603901046030400440c6800c420a01c00e00d402980688807002c894609071051600c0c240e1160806080a030740032404000143e0300000304c400c40c8505449454a07000300e44450050034500c40d20095220072a250b000140d25015404244508140381c121001e08152400c41422602030303030541d581006942c0c5082c045a4825089860090300c2d629100b0500c44054880300744001410f0350904a0549820070f10085c042c035405028050320341120515111851441e42c0c580c1e400043c03040700107142d19034004104035035410090700c00c0f000c1d200a1480e52490030080300c1000b50321583c0300c20a0140350850018141860340c60700402e03210a51202d038523052040c036100116030041d4030200e003040043c1102040420580c00614040d6031252070b000c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 573156582 1250 573155332 573155353
    0x90f030d091a040b0a1d01050901091101090303020604080705070b0c030a0f0305070c020f040e0f1507050c100b06040302040e010b030c010810051c0606080f0c0d080a18030212 77
    0x40e000e1100400544450b00c078141070002044030620001c2d0810580380700081d203c0300c0c1100072580800d1658200002d94038100c1009452101034209644a92240003030346d4121403c98015aa030322520300000e0016032001002500207003100300185031080c0200100c900c4259640009041daa0054070020100d070000f003402c41070380e070f00030b1845181940d543c02d0070b01951421001c02131803e800d00b03802030301c14803500c1604559903c1d298007503c80c600c000c500307450441501c000c883d655030b038403201c402681d00751440010f4845417003a02a900c00d41800c0e4080c011500d80d500041006d81500207840741e020408000010041c2e80341c0c41b9441e0085403c80011503c011403004140c2004070408680e414841c500c03080081002c17a400010313007521412540d04030680301101c0301140304100c02c280208211300e00740c004120b68000040c100e66500701803085800d154050782c180034150f901003000070080c0070140100f01609000d040340c10500f0800040480d80c550b07036500050280c7c842481c0030881a00201d81c0341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 573157832 1250 573156582 573156593
    0x7020a0b0d0e030412021e040501170c031b010c140607031409060103150903020106050402070c17010c020c0f18180c060f0d181502040905090f060609090f030d09 71
    0x4038610340042015500345840d0904a8525100803030000344507c01040c1c0c40003d07841441d10000d10b041000d00200810340e1036180455003800c0f49143d8180c503209512400d242843c1c00201d04400c03d00941c0864010340072100150f43d071940c060812210411480403607036140c981040200c0c0300f482d00303544c0411042d051110030001d03801c010700103d41d00c0d0040b80060020803000c50602c036141034011f800061604c01814104d00409a41d00840c0d0b100f03000055205c18080c2d082c0b6114166a02a440340300e100e0700720081d0360b08840d51150800c0c00b5810656290700030f481c1610100c0041c40d0041c1c54165010400e40003801c0c103800403507260340c1c01441440805003240b0308110020f02d40e0016229245005203600c80c081e582e010303a40b520b034002900c400c0248000c4500c0c80c103a00703203d076121035500042204102c6000c00394115005089440e071030100001c0c44c90f440011200e0241d0500009440e00340c40f20014400e001e0030042c0701c40c449218401402f4401e003002c0004010500045100043c0c098643c640b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 573159082 1250 573157832 573157841
    0x803070806040c0809211e0403061103101401030905030d050906070c0b01170708120409050a02091008070509060c0f061b030106030207020a05130504030e0909030405090c07020a0b0d 80
    0x21802041030810405c41c4081d0002003114441001c3c948145603440a1007030060305200d0300b40e1840f084030107040740a03065840c0102a0040c5d9118642c00c2c494070301c47c0b22035420319000464900c4840125580200101440304031060040d0710f061402040000f000d4a40c41c2c610f46c0110f03a441030b4141d42d0030030041c10050601c011703a0011711780d1070080b00300c18950b00c1e04e500c05a8180103410030f04400807000207500100300054801002c012060390795075024010480c1d5690040d2040101d120309180c0024040348852007120200140204009400f0880c80700480f04400010410030a021040050401607581c08018220204074400101994001500883d08040014200c4920a901c08810541c3c00f91144180d85c1550440d240047e02c0b007066000040e544030700380c3d001d6504400c0c0214540a10149500800d10890003070302d8968542650506200740000200d07100903030f03a001407000340710340d25001040903000081c141c0240c1c00c0490640001e0700045490f070015024640004d030f00c10340c1d030b11180503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 573160332 1250 573159082 573159101
    0x60f090a050f06070b2208030f0a051e06012a0c050609010c29010e16020d020303010620030406030912020601050a1206020c0d0f030b090c09010813080307080604 71
    0x12065900d006010214295004144008204540b000009072030b413111704a86882046000e144503c980c1d45906240386192310540d01d41440381040720004807000340501400380103104104100c034282011501007030f42a034001d000e480c1007211056a1500340c1d07680d4690200c5100c000d8144046103100751a10428848199220f240180c4003400340c1d210b0b6a07000802031403119000008030441c03101c180e40307000c0e401400040c0200350400d50000451804041c429407441070a16100c81342e010200e240040e42d0340c510114091006030300070401805401c1c40fa0040ea0210344c0b030300104489040c1c403a40c5041c10350704690031500c006a90750110005108243c403030075840c2c104900107000c0650420300400c1c0c2406160099400907003041d14902d04100c03103a1b040742d044056aa083c6c2c1c4c100c071a0100003c0c0039200319442000000d041c2020040d903071800244060040c0c60711103080340f5000260005581d0190020503803861002200b80000201d44160000d5104071060780c7c80c0c03c490b290a900704412200c4612 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 573161582 1250 573160332 573160339
    0xa030c050919080c240f12150a050603040210050903070506070b04020a0b04180504022101090311070b16050c060d0606032714190807060c02010203090709150302060f090a05 76
    0xd111132001038240e503000640408980016a4811582002d08411f10914069044110803070040010901d61508c01008042c0708581d012105035641e010429180000c1c0c8000e9401903200d4200256140500002c0004a44c06420b8501c0e40b9500c10009001740c1009100b43c03414060382e030406c0118a4800d540d00003915418000742e08107810100c0e42407405003515685402903988401103015580c0745c20800e0760704406140e841201504410036907020b441001400c40c0409e20701610303601c940c000030400100340c640301c1e84800e04060022003240101003040c44141c2d03290060044260240d264000200410a61544d0110301180f40c114014200c554400303d40014601b080300b40c0c40c2600040f0071881c205608100141e90000700c20144508026410780c442c8070100d080380910080104403405003400c40c0c001c403002c01090809120030707800d0740b2003121140302c241c104920501030f044290340188030004112940701d0201d5100d40c04640c1300e510840d050b4100c1da2010865060728a00703040c0c2c06000d0141075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 573162832 1250 573161582 573161599
    0x2071508070917070906140306010b0c0a020108040c1a04170a0c291b0c0a290d020d020c010c11030406030b120109030c14010608030a030c050919080c 66
    0xa02000b800d20409000c1c0d03202c0c285044007103800156003002040d01030a00c04104001c000d554038400d403825042140514001d000c0d010000607010303900403d843c18042d1410142160a015600445031408000c20464044120b41c0c030106402e624121601c950581942c44151b4031420150509050303000b80c061124103910200314140000c64003803001e000c66031203080e0b0310303449070810b0b00700c0b003d404200001302c00405012600c49070b00d00010b80803030007004052068400b008142002e00601c040940180c3c3c030b440040b42d1608028150b1800440102d1050036442030400d10038100d04000d913880f625000e04880d8000c41d011310450310038403507510509642d04200c83c0c480f500203203003a20b0340500c0c40b4480a00d1340d80c070200c0d5034541750a0b030301c108039180d01d8008000803007892502610f0310807821400c1d0f5001c00c8090115484000502c40c0c0c0c0c0903100210010740c108140b40000300c0c06003c010082c40100300e030600c03113284c59440e0340d4810410485180e840380036260406044e586004580700c4003038440c000300d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 573164082 1250 573162832 573162841
    0x2607020613170d2d18020d0327060206010e06010c0b0604050601030216061401051801180221191a130b1509090609040803130303060f0602071508 64
    0x9854410194800700401a01c0700c2c0c0e640c1881c0c008107404000010004c07001d041c02c070325250882c9080c04003407803280401c00c110b596030015800b4502c2c6a5000a4004081d5015000402c0c0203c000110101c00c06d007001003850404d0501ea00c081203d6445900580e20410042c01101d01c11307c205a4440d0081ca000c0758030600c65200d0907202c0d1005000326006643e10700c08030300e8a0744207804036688010855101c0056455078034201c0c0c014840c0440e00204022500000300d01468050942c0b4038942102d180070000c0d0342007503100e00c0110480800824565402c0141c1080c0e448510010541181c1c45a20071402d80f0744844802100c1030040c515004140c940030301900000c9903110000284402aa4440b007004940c0c40c100c0018210580810740c405007241e15503095100c03500003840036020545040080b0349511040c001d20340b0303054400405045007440000d6624041c0c80124581c00d00a10303000c2400c1ba520901e483c4054010740104006070440907051140350040c0154a0001c080e40c980525203182 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 573165332 1250 573164082 573164093
    0x1a09040605060a17210a0203120a0204030c091a04020c1e0325030e0f0906010c0f0816140705090106050c03040f0f09050f0f0604020a2607020613 64
    0x90006160954840108501d52902c00020000d402901c0f0000b2030100c0c3d480c0c04036902d103403002030902c940203800b0720742500103444400e07168540641e4000b1070400c1119000300202c0a03008200700c5000ea804d000000100e8800052400280141078000440c26a14040d080c41030314440c04081c01580100144107922200160104500b030f1132000455144070450251421445084440d00c03501088103103042100710748071846d44030144240c50b1000320410010500081b21282100141e0044071600001c18650080030150b1a140c03051407483c11020b410b41c0c0380000d41e00701030417154004401203002e4007002006d5240c602c00b03149490041c405545084001003056005019120030000c000ca100340d10f65400304160303401380c0084040c1c0c44c0790035268188151481e0780c030f201d1006054185404500340c210410002070281e0203040d441c4885940d039405002c00707540900c0c001000c1001c01400701008155a41c0c1d0403420881c4910007080d1401c201034000d00c4e01d08042c002c540380d2407050303407070000180 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 573166582 1250 573165332 573165349
    0x9020307090b01030207050d1808010908030c070f0512030105040b0a0b070f29040b070807080103231603140d024306020f0714040b0607020d050d031a 66
    0x2407603680c02090241407840100c01a00410000410501c6462024108513401000001d003220149040003412551402030a00340d810009020780030050400215010000e9140144100d6008202020713000c40c0e00c2d602c0525120250841c4400f1000100040c08103240c42e009070f0000220403200700c00494100102da9001d4854010002c0c6100c440aa00404200752040c0c400303c0900d0520000180f0501e0380c10203514000e046500722014404200003610301c0d80500185802010141d8840700710b41c2c21591804149400d8400c44800200701000d0001c0060b410801c0c440a40200f04455054614500d4525541c0d417400b020269250459071031030001541c001404e0290111f24540c84d42030354140303100142003440d0502c05034881640101049444004131070210100c41440e806c503680c2031008a00319072204480d000d089003c5441c491410b20610300340c0c00172001840e00034035003454155203a000401c025245801200c454000300a5240d0094240c800c214420001707940614109007400e00084640 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 573167832 1250 573166582 573166589
    0x100605030f030432090708040209060402040303170a060b0c01061e0501050703120f0e0c010f030e101a060307021506010507030813150e10050c0c06180a02030a03051c09020307 77
    0x40c400c0012138800c81461212000c0d03500b07000c3c0044001d4140244000c0c02c1c280f0442d030982c014039000d400f00707078941400c0c421101103d4055880c110003020040303c1994490014001c01e81d100c3d1a10000b0403440e0701d140040c4054400d04000042180c540002080c5554000b11003480048070f001c0c08000341d981200446000d40d604d403800c5805003800c100a103000706140d5101e80001840c0c01c003204041c0d00001000c0740da40500340c0340d003000d005006c0812000c0d02c03d5403007038041640040704403200007000b40d00030182d240316403d1000c07908a00703880450807982007261400010703403002810202c81d0300a40c00c41600540d081c60441d03c1d0400d03989000c5c00c0010302070802400d81a107084001c083c00035004100d01c20074410300c1c050080c52240b04185544106004105c1309031840c0001080c84505580112032011000348081c122a40d1119071800307000c120011400004d01900102d440140c0e410b0140e440370f140b00c1e488a1b034071030144070308161110716a442d240090780d00d40400000542c1d00000d19a089 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 573169082 1250 573167832 573167879
    0x270b01050409170304060f0f23010810181e0b07020303070503010302060a1b0809040c03050103050c010e010216080d09080a0f0b0603030d05010305030a08061827100605030f0304 78
    0x1301e40340ca00d0060014040425010225031401c14104580301c00ba8004202c0400605180401e03480b801141806811080c032070203da680c40a1204c0700940301c3c2d40c00c200742460004400c601400c105407101721130080c18110341854400c02203844d5041000301c1a03110741002092008608514224402406601c41800b0180c4102c2021070f04180040c40740c0d40324104001e0726240301005990603d4181c21503042040a10f2050741400b8004200c90720a210f80c50481c1c0e0030800a03d158500340c40195084950185032a0450103110f42c80a04151080c61503030092072154018450a0ba01c500e00074040f500a4029a900743c01c2056000c0100300344000d400c2905400030b011b00c1107a10782d580001c1c039503c00c01801d07050013418800000300748003010001e03150315102600c8940302556103c0c1085200d106511884010640c0c0300041811004181440c01030000100454894050f4210070189403003082c40050103a280c5510044c412030070180100c5943c455444000c42c149400e015247c0d4040b0070560a0415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 573170332 1250 573169082 573169087
    0x16030804020d350c0703080d180807030e1819020412050708061e0406050604061d1b09060a032c0d02070b0310050d06270b0105040917 59
    0x1555141c000c0084401c0c0d21481040c8050742c42c05951002c03481424520000c00c03000c150214404281d070f411140080d0ba06005820b0141c1507645441030b5804c900740b21961b07540d4440e049041010f0a070380000003e80101c0c07015844602c0340c5001055203501d0f400742801203031005400703c0004040b00034181c108240e040c80c0b06002c101480000b0090180d680aa10040c0407150800180000410800b05492540701942c14543c0d4801c10751240c0c0c05006542c100b1000d00600040100324a9845603400000c010004119587e464100e8545100c0da440816101d91501041c0010300200c41e6901c00c980304071110460820307100c1000602c0c4c0f8050403082006140c0c0702c0c0c0c54083c0501781440e0500244111144550000303000c1100c9603601e2417402314034000340c8500880070032102406001e6a2040740c0941031603866030306000601c880640340304000c4135000d440d002901c24001c00305207040c10f4203030f6044e245d0f42a42c405081c506030a00040e03002900503031402c3c010201240035958015890343c006554a507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 573171582 1250 573170332 573170341
    0x90804090b01230a031407090b1303050a200a0e070c020f0607060501030312060506040506161a060a0504090c1214010204080c04060504180209070903050604080915160308 75
    0x1c1d002e900c0d20034011421001254001488488140500301d00b0f130103690104004200c0d90504004203805541440100391509410012044400c000300b6802004800c81c18030203540742e13603440ca42648903c0444100c1c80300c41d881e43c0d4008024500380b003450000c4400c01c1816140490421f04503501a101c102089a214904c8055443c0d80580a01440c1c01a108075540d21190910800400003808110005800c1404c20a8400030340c0c05000c054410013061540740c2485e101c00c10100750703c461001d0307601d00648070303401d000302d00c140500741101c00c00f40490725854a400c0c400c011103421560400c2e48124036151000d400b180b200050342c0c05650b2580b4100c60071005504051b94058613101c00706515600020300407440500114103400311841c10b5400348100d6459408100c1920440150003180031201c85030300001d450034480403a000750060820511403a00ca0301c0791418884110341c10788443c20001802030803030506584524400380306601c1142444001c461400d1f441e100303900040e041141510215 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 573172832 1250 573171582 573171587
    0x4020a06031802030f280b07050304060608061906291803061009180f030815040f14010e0c0f1c0207030305060a06020d0e011101020d060621090804090b01 68
    0x10b8000a400074101e444402002c01e10310b60703500442d48948190034091406600420601c000b0245040c0e1201d050300c3d49a40e00c00040310250801031003a111103403202c0002a00708028032981d1701904c0002d010012201900d55500140c1e0302c50ba0040003490021046240c903141c1e070a070700312840f891000e0700715540c9045c001e40c60b181d8090054a580c0c58042d03841401044215003803100f003241e2890f0400c0c0039141d1030201000d18885442009010716000781c4030600003921400000343d110041d400011a4902c140d40458100c1e444440b081e041107640326202444440b40d404c00794010510030380482242d1420354801c0c94a809801624610644040307070055072448404800310070702003012421501c0704080d04008010340401d9a62501440d01a1004912144046001c100c400300350713100d1480c0c0c80d5095004560b2421000340811071550309000802d5040c060b4098000180f21540c0c03510131091300c0100501c0c1d0310846c280c0c3c290400e49802c600d0000034040000340d03411100180c100280482091005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 573174082 1250 573172832 573172871
    0x607020423100e0f0705070201090b0a030f15050303221d070e040c0e15070605040305090102070b070f02060319052403070302031b030709050907030311030304020a0603 74
    0x34204841c14240701c8001d482240c22128031038000b61072024442c035030380d82850544100507181c80300b0b540c400c0000600424018001000003038410b2426254117581c90f503001886c0d810030a000000070f40c5a0035115064409409041c1c8c8410380c0201000d8500c0c90100040d40c1c0e03102d00d03404802c03210407150b0160300140200400c44020000040d80c1c01224182d5075a0744415101118004d02159510b034401c0010b007081e1140d079103159100c2d10741c85029199001088202c03001d983c41c3d00320b400c4040201000180890240303a003e50320a464041c1c450386801c0c000fa082c14051340060403103c1080c44040080f400c00310300b608100d6010785007242d5941b226002c115644c0302c102800b61006013070805000505038400c2426070b11131081a4042c0381d6801e05020503031940c20520002e507143e0f2040c0703242140c000e0400717040d90284000600301c414031a40e80300740b0819100301315a0f281e001e40001e8810824560401d01d4203103030407505800740d403651600b940043c0035a46180102000c055441e203814644d41081a80c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 573175332 1250 573174082 573174101
    0xf0d09051c1515030606150c02040b030a081b1c05180d1b090b060403020609040b04090f06051501050a081810020f04030c15021903170c090a14010504030206070204 72
    0x74090440010340b00714070045244000c403483d40c0340c9003002600144490404c241f14072140e0f18010340540c41d0702000054500c9520702503250048038400c00c00a0501001003110702002e00d440e040940c5940c007181e0a0400340203421400d000084520a4040d500100301c03806000849000c0a4110750103004ca180d200f81031000070440080503101c001c003401160904011180185003d0000f80d8042c01807000500440c48002e40040051002154910349500480131010001d00009002c0700d2a0b1079164103e02c0d900c0007600c185903504148007100e008415241502d40c0d0030300700305142c0f01e00881c00629804005220f030000440100845091044c20b0046000d00000000305544400500e82907141a62062000f25218400401c0c001121007480c5420180c00f04030341c01170411600440c807100e040215014045041021603000b180d202c0001e14030b00307401a007810b2403150710383c0559010300594046070b410040083c40740d130110580983c1e1200c2280c0503244d041d01d4090b210f03030f124400704015180b03255 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 573176582 1250 573175332 573175373
    0x108040f110a0e041b0503030405010e0d080f340210020a020a1409160c03050a090f060c050f061611100203250c080a051b010e0f0d09051c 61
    0x40003c0d141d2034003c01c0794040c1e0f004554020b6501014021001401d40c18416a90183c02c244000c02281d809108200840d102c040d00b002e280800954800000f40c0c0001c0f0a81410b0f90007140903202c000000d240c4440c5d10308a03030400160601c2c1e1382801c0c00180c40240c1d009104146000c00410003d10a00507000d081e98017038071400c402d83d220000303825101540b0320040e0040400c100029600818003c40c9000c00c0501c0c1c0318040074826a40302160242c0c0400000701c207201707910000145c0300150400007070003460b450f40d541b001e048440c42c0003420680111145001540090144000300c80007241d5600da00303440e0b040143d0071454140d409401c2405148159009501c0803040040c4120140c001c1c03251000e40480031928801c1c1d070b20b001e844442e20840041c00000c01441034800749070158000f170071241c0341c2c08180c1200390b0a4854060941d40700e400e500c1070390303000900d9140c0e040c0020400d0701960b00381c0f0300f0b02300c0c00c040c10704020440710b2084d01c3d0131003881d074005a041d0043c40308144140d51100c0350700303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 573177832 1250 573176582 573176599
    0x522030c0204090b0109110913180f0c180b0a15030e06160905010807050d0f020d020309010618060503060c0f1b0a02011e08040311010b0a0909061107020108040f11 72
    0x13820304801000c0240308100c1c910313040008580c40c81900004989801800605418145112114580050040b450b40031111100a026080411074110300c1d0384610b44180c3c214412103050240383c690000e246103419a0b80b9003050300380ca040750345807401d00c020781d020342222910000130060101d015040801031560705000d03210600400f540400b050456262680d210502c0607580c402c01151103201c01c0381c500000800038400100030136aa5003102c234210581c00d6004d4200440b4444a0342268410303034122890340e42d1004200711083d00104800030f00303032065200300059444c0c903011940b20200181801404174001420180d09031002040d900101c400d945907100101003844280c2c1e41d075200440690100c0c07451111041c00d0581d2000702c084040c002d9452921680740e0307aa05443c500742d20305608040b03549800340d901d05502c0c3c84180c500102580c4402090704d01d85800c0c010101d030503c002d6514504010018480941d0304100d0294210303510440c10446810707103080962005480751145640b20041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 573179082 1250 573177832 573177851
    0x1b120c03030115211806060b0a02120a0e04050c04080706050a0216060f0813061b030b03011b050c071805060108092e02040f080a12030522030c0204 65
    0x80a18142ca0b6640003c04030303034802400a03203042d03503603920b4080e0041d000b028900c80e0310b506170410860008040344c10b04902003103540e003105680f083c1d0043c01c140c04001c201c0882140e410045518803040c0107070407910b02501c0010040080d4111070380c041c000ca45038000704204085e818200e40c01000214141c440b0642c403524020540e502c03005080005104441c01c075028000d1180d042001c80b617640c0c440380d10211002c80150b42c2001c2c01400084010103d895200104005000d650043e0b030035403c0400c002d000902c0e001e01194a03d130700e0305000303a250805078005c24800c0c4a20b0101003089081c00e41c3c07a41f0303070031103140c1c600727040b6802c01011407480c0c40c1c001001c0c88071a00010b006046c01d8031640b15aa0350310101700d54503107030f00c01110b1140302c514102c0f81c1068041580b000740d5001c1c90384058035103070303d50b070240041c0c0c4402d83c03200c081070b40800d204030140008a800011034260318941130000d81000d28145181c4d038804841055420303035620301130041501a0b20b80000465001c0c100780300380003d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573180332 1250 573179082 573179107
    0x16050f07140d091d0610020102090a27060f1a0408010e010f0506040213030305090102010e3c06010b0a030b1c05070506070314030a0605090f0a060f0b1b12 68
    0x3141d0411004a40d43c071201199001000d01d01c020a20901407501c80f4a60b0307080d080150060051030500107555007040801ca60703071115004000030300102e013040041d1540b08003400c5901c4841900e1800b51514180c000e22a000030301c0d4072117044840310420010f42080e40c944050142c400c40d400140b0075171078016942320a05041d0030540c1c0701c0114603000c014036500d000501c0281d200e400c1c1c529a07012141c480900009006030090154140d040c400040c000c074104050070f1410780f81950488420490a00066138440540c08240c03295003026003103070340141d4140410369550810b00030b141c801c400224000000b0b901c60703800740c1c0c00c0d0400100751601501d0309800c40e4010788400340b420b58180c061824085a2402d051044424082d4150b803140c08019110618032a01d03000504854100ca49a000c0010079030744440c000382c01521402c6000044d03042c0385910700c0407a41c065014088102d02c80c4e10401c2480c1992080e0b5607113a05002c0d807801e0085400030795505103000d145800300744100c0441c20f61032000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573181582 1250 573180332 573180343
    0x61b010608062413020c100209041b0815061e0a090e011202130e0d170f010609050409150c030b2419090308030f091516050f0714 57
    0x1900d074419221241c031407101d807040c24207405011440c450a5144800c08a00b405400a01074803840c090050800031400c0c280340c00d007031090701202036864021481310010b1600d0b1080035054855559040c5442c1c1c00030101520841000b0026604090300c030b80b0007442c82e1103080171105010702d2080400c10380c41c0100c011038055003120180c1c07400034600f02008245650780d06217480c142d600c1a0b80080c00308000c1c0d401c200140c01204070703c0242503100c44072010041d00c10014420000c02a03112841c0d184408903100312103100090000700002e054400410a40e904040d070082503a5040d6004103c002c240d0401000c00010410b1000c607117494912407401c69a41a8813181540100725820707290504c5c4114a584060a01101c50300c01001c01c11a002c01c40b4242280d100c4100d6840c10407280c0903a4a450380c3c10990000c46507a20403403441010000d456009008890b1001041c400c580010304100403a000301c40b03c001c15a10a010001603003102d200c800e003003941c079120f0b444480d044403040d501c82c00507281c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573182832 1250 573181582 573181589
    0x12142205071d0601030504050c04020706020f071a100e01050d0305070506010303080a0608060f0a021b010c03091e050d0e0102150112140616030506040204050d050601080601060302090109050f061b0106 88
    0x81e0b00d9000c24150362103030150724011741d0054014220341aa8904101c025480700c00111030040d4200110302c00c16041e4000b410607039000d00000103000310300c00c1e401c10354202d0040095038402609501800f90202c03110300316055030016a14800890340c035280560300d522410f900074210780b01d8100004101640a41c00c00d101b031105003414440c1c41d507954100e0381d40305401c0d260381c0803d01d090303c002003150303560f6030180c0940ea612401d02c0080d881000d1082d403c407496524a42c0c00a130721040c821040c1700d1890340351403030102016503800c0160f0181d00e40ba500c8484074044002004054070100700180c5c400c02004285031400044003c40f543c1d5a0b1141c10100003203030b000ca0300281403a0b00d090420318045007580c407400c00503160b8001e051004108600400c00200031644c016400d1201140c151280790480321305903ca2030061000c1c3d4102002d0342d15041d03059200c0010540100220003290b6800310b4010104c8000b620003c1d22101c6100000f07041d40111040e9201e92030090f0410702d030069054009100b103 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573184082 1250 573182832 573182879
    0x120b0f0a06091b180815101e14090402010f1404051305040506070c0201080106030e031b01150828050102040b1306110304050105040608070c020303191214220507 71
    0x20040c40d0031a0340c4c2020441c0319080194210300c60f9041d0304000000304941c4605008802c1e039046486811074100e58100507049080b5400440061003a040c110020364001c0c0c80c100d1b0019081c2c40c241c0c4c0020704a50000d4521002c00a08030751808101800d0000c3c0d40c040c000043c0076000251380c3c101c00d50300602081700c0c141c4030340c410351020650180c0203d80d105002a01a902e42a00c1ea00303250043d8080c00c482070030400244010001e90720031000d0858841c58114130100045100d104001104814500542242019400c10074900c101c02034203009080410780c6040380c050704940c803030420f103009014591009000d40320004000300b0b035020f040303018800d6801e651243c0c0792190104040d2170303981c020f50259038080790080109110142c058100c00f1b42c8030509140000000c0d80c2036003c2820b603003010208440407500c2c50321100b40c65820241c0b25444203c01c1c0000c00103503800d4084100c00c035a0207409503402d161800740d622000c800b50300318425800d40050032aa03029a1b44e80e411707242c03c2c80805c1c81500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573185332 1250 573184082 573184097
    0x3020928020403080a08070c2001020f121b010207050105070504030c0608090606120c1002030319200304030c0f080d060819020f0f0316050307120b0f0a06091b 70
    0x854691074401d035429682c001a8250400c3c0c4016015036001c035001e48000e0034490305540d55400644d0125525440d8844181210103200542002a15010319080b410106801c0340c2c01c900c070681c0000003910b0101e41c2c0c000d000c2d90341200c00103c250080c400c0080c040d25039400c110030440540d070070000038030449124802620ac500d0340d0780400c451980c2c003621b0750a51074211002041c514940480441101a20201961400c84110000480b000e0b1020350310009070304003100308041903100940e0325048000d1035005000c542c038a9003001c00680c0031074120318007008000c002f20f020715105500f0040070950000c1819844861350910018540150914207d81806c01101244005000c140480307440302d952945926100294200003010320004045034200d40651010991030b602000b000d10326004c80307040707000c034282800c00b410700341000c0741c0080c0e103800000e03000440050b09040b6410303403002c0035410300b0510782c0b03604403280c1c0507148076403003810440c0c1011030000403d2703510924414445181c1c1c60b40b12 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573186582 1250 573185332 573185401
    0x60a060c0c06030933050117150403020f0f2b120b0f060d0b090c07020a060320040b090102010f05011203031d011517070b0a0e0a030209 60
    0x642140c14900c0040c0303404000c01082148500907000640001c0c0700d20070030300ba403e11a40894950313000031643c00c01c650100303007482c1c9003540c0b0502ca0360740500000030b000c0c0c03080403003180625600e40c1c100710030760148174150000606140c401d001901845c80c440040d03681a03421808060354a40c68540c1c2e054040600c1c48406184001c01070560039204161b4451034800028060403100034103502c00c1040d04004060200701d01a41c0f404010103480030308000015850715024103100c940e020080000c170900d50208940380141ea0354080002c00caa40f00c1c50082845c40401c100c80d03c281078000b0a00c4200c00001c0b50200726103005501401c260942a8020030906c0da06080ca2800c1c0d880a01c517541c440458605a480030a00c6500103081208841d007403d50009144031001c0d0851f602c04010b500e01a811000038090402898000481110160004d02186037406171122103442030329038060a100040102001a881d01200940210780003821207002d468070160382c0c000300c6410381400c24048400403021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573187832 1250 573186582 573186587
    0x6061e020705010e010518060412051011030c0a090f0b0301140f0109050114040506040b31090504021f1d0d0512070804030501020a120e0d1409011107080105060a06 72
    0x8011a80140d4440700c0d511301100c010345099101100c80300490a403603c20841c00c0c0c0380c09000b8000ac00c03030304849005032035007800d020b824007600405002401d0304142d0144045580c034002c9d2038001c5108204180d03034a55814080d48c20140680c8001d0041100c030100149101424002c3e6048034000c820007907160003c01c0c10004c011410b59000745c0840c1c640c5205108070b511036480ca074032820741840110300e041c0d00c2e0000203500f600b2681c440c030032001000400110050b0030000f00e03011000146c00041180980103102d4546217450b0003821426030303442c070008040d5501c049090b03003da940801c10103803001500b1402064081d4002d0010382946c21b9580b400300700d081c810703e82a041a0844094000071541c40003010b41c5502060058401000c14800480030071801e20043c80b003100561580031400c813400f6600c200307a0740412903114091304904094402c42d600b200345017504102405086a5038011200140c420480c40002041644100100400c4081c015842640640c800300c1d10410450741d10b1204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573189082 1250 573187832 573187843
    0x10e01020d050c03090a0b090103060b070f1203110c06040b01050d02061b07030804060201020c010b04111207050d020a0305010806090a080a11100509030310090c021f060906061e02 79
    0x10640168040216406840e00c51030103002280703004400d49203800102c00024603c010b0f10307081807032100700000b50514591303010320a03003000f01807140d211402c00000d81c5440c41c180c4d00c2081c2c0640fa001a2000e0780a01910a40c00172000c0303880103054940b95a07011840303e039100c900320b408440c0b4014035000421640307405840140a15030040c0b0040c6005410101c4041101e000c05200e06a407190102c0480091603850161001d80055400140c944d00d18868141c00d6540d008003450045141c00b0900e40c510000c2c0f0100c1e03c1c0070341c0c00c181e0040191a030000031615440350182c00750170903101040c40070050342c0c15040181201c0240f402c90b0100d4840042454540c00c46034001400c2e000d04100c006542c03401400000308440009041d40d076907054a9801100341d480c2196500100c0d04004100030031800c0e0100c0350805007010420422511101480103559200000300c50003c107a114a40e503420001140c0107070018003803104080c05440e0f500c02c0050004101c110060944034041e008000d04030b44000f80 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573190332 1250 573189082 573189107
    0x30c04060b1c02031b22030f17030c0a0f0212031302041a0a03021014071202011a01020c0d060b15031b1305060903010e010c080702010c020a0b0c130305010501030308070e01 76
    0x290b40da841e6644001d2500d0580c030464401065240c10100804150782c82c6c00f80000442c00340e845883d0801e4a4a0620025280d01380d06155219003801840790209402c419203002a0a6017800e072407440c0420010781c500380a60403d800c3d1101c001007000124605d030038548a80320720966042c0a60607200e0764280301c11640c883c0f000d4015a960740200301500e014a509486290745007000d031a449071954215100d80c1c41801c0c00d0314140c01118150f4921a424811107102550b03161000001042131030000b9180c02261034018428113424802c201806903030f5020740f00c9101c00401c050601c420509040f035264004562900520404580110400d10054202c80d5502440b00920f07080d1070403c4200b140980209890340d40640da550300000844100b4442d20740c15401a80310541d0524100100a00755040c0da0140421508580b5003080001c0382880c480d80c12903984501d203501d6040311110302c4980a0690f101800070340c00c0200000a054200ca40c80b405100f45503120864031f140c40d001580c1c00c150091 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573191582 1250 573190332 573190351
    0x120b09070201290f06070215030a09140a0b010b030703020d14270a061802120105040b0631110301060c0b01050a03050a02150915120711060a0902030c04060b1c0203 72
    0x140070921600c5d101004100d071502c018403510358040030001080351604100c0700700184c680d0b613803404000c0c050001181c41d0058900d0005100c44003040d51074824014041c400e20103000004004a01f0003802501030300c1c40f4028981e810014034213040c151800d14002501d190301118a444000c04140c00c02003080c1c54100345150082900211643d01c4c54000d040c022a10740d162416101c00b040103030786410b41030a0040120300007141d5414182400a00a0380c041e014620809003903d00e01c800088000041481d0039032100500408032201840710003a000b144d0022400b90f80010010800c5c0e604030341100c0e00b07180618403444240c2c2e01d9a00707002002c101d80c04081c026a1060000c940145804101060440003003901c103400c0800c40c00216841c4403010394020040e08001c40c0317048d45c0c0390003000d80940c000e860740780418860065140054a0700303406031160841c15114129001551002c0081d14000f0401030020064140d07560704a07655504a200c8410320001414000c294180c441d000340c80c000c108aa = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573192832 1250 573191582 573191599
    0x91c03060f052713060623040b01020d080903070209041a0604110702061614010e0f010506010e101710031b03121803080309060f0f0405070501120b0907020129 70
    0x80440003c0400042984420700240d942900000e00b4501036240100082d09841100da11003400c0102c80560459446020b08c0c54072015049030380e4005805c2040a40070708001049803549030105065104558000c8d401480340c200384008c00410810345418280b910742050b03c00e8079004100415124004041040294240004005427a00750010b0034000c0300207000740102502603071104c076031860364000c500305079540d0b5014034070010040c4086442642104020045490003000107080282c442014078011088800e901e44170b81c1c040d9405c8617000803010029115031a19607241c00c095092408110f9045083c400c007002c0d008000e5000c28240d0394001c602c807000340401a01100c500b041c100306198444001140040070039078503001180200d5648024010340d2070b00711107022501801030488010306070240e00f0000450b00100300e0b0307426503c0900e07240001c0c070785840741c903405400202e01e89a070244400080c84a420707015440490010504207100781048144200c00030690900591b0a4202849 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573194082 1250 573192832 573192889
    0x12030108030d0f0e01061712031e130f050a0c0806040c0b030a11040b030601140406090b091314060301231602190b090c1512091c03060f05 61
    0x45070030580103401c803e03c00040780240a50b0140c00d64099500102ca0b4090980c141c05034400300b40094a40e1096100c203991842c140100c1c01d221481403407031224a40a0042e000c40c118a9901080034003c58028030328090702540c40c10a151981021803041b01c08141d0528001400c640c0450154443d5421041e050115464615041c1d050b1340b0062102c556603a44001201c1006010400b40001d0610585029140e1a1400c005007001d001c10b40068140f000c18401003060592100741134050301c05409240f40c8502c60700d80800c0526403801c03da212010304102c1718800c600218400300348200d200724024000e204003c101e0403103c81400034080c003c8114100010014102c510b003001c0c0610607441150001d204a00c0c1040e007040250400311144101c0c0e509002e180c5808021054804e041110701b0226001c0c01d1340d00e0302b601d11955072a1590014103a0000320a0396051000800340003809003850040c0200c090010005d003010701409007011020f6401140c0d134100001040401c1d000c0701508540d1026 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573195332 1250 573194082 573194107
    0x151b1a060109090c0203031005030c0904061a120f1006060f111e0601080c0105030c03040b0907090e1006120c231f020d08040201052b05070206091203010803 69
    0xa0082000d4148400b0610000f8004000d100340060210304c0e40c00b031341d2241010414841400d03140d501c00c9100f9400039100c08190358680350b4042d00f203548010002a000e240380040c3e1a61010302c0b0748664011342c5910070f00d00410003c51480c121140f024140e40c00340a181d03854030101c40303280c0604c40c00107079070130504148140105541081d52402c58200e40c80004108802c10162204610812054001c5001040910820041e8040c141803d007412400d62510400183d07440c000140040d10080c041804181014810f0041d000501001c001c103204940003450401d45d5056144e040f0a07080340303401030010b1040901103034842e5070b5074040a03982c201850205d03402c00e000100e0a50079204010300d00c80324200d41d00c03072280d80114581c40d8200c0c40220461f11003c1c0c1000f41c51000c200600241b4010800140c3e8000d04980b06907076600c040502c00388140c100303072141e1030b07400d91900c107584d2401041c02140d42c3c00060582c0b01d28442c03411151010301c4515501e0142c0004c0c810494164030510100600c086c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573196582 1250 573195332 573195383
    0xb0a0b04120503091f02070f03110409080d060f051201110f03061c0507050405070518101b0c031b120602030721060905060a060e0f0604050a151b 64
    0x74002c600310b9050a0202000030305802060f01403400003180c040344107440d00d80501c2004010080152085903075481c0d5183c1c001043c0321030100ca80304a9407580540704012016042c1c440c0513500710010814103403995246144000720303004407885846c80bc1c005102c0b2030014016400c4903080301c1495824402d01109000582c2c002401680e0b004c02c0040340716440c0012140714520090154006110061400e42404116600940141c0c1005010025880780a0005c5132000c0030301000c1d0340c103190280c040402100e0b090b00382e03600101034a24070120343c81404001414101035034050b81c840c1c0001c0c120019100e140300158800c0e45c4003007108140c5200131588542c095580141241041c0407800c403005803010104101002881c207072641c401c000e2241032030350b05c211903020600f40c4004a01c1420300340e014103007199900a8500c96080d81030090a280c4408050350b0050501910f4070000304d494100b90644107583d841c4a0000907060440030039400c12030b00d00c08450b1a00911003604000c0d07490801040c0c00d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573197832 1250 573196582 573196619
    0xc030304090c1e03021e18090702030f04120c080c090c0f070b160206010e060d0204020c030f0a050a0e030303040206070605060f03061504060506070b0118090213020406030b0a0b04 79
    0x3c09100d0100c5041c501012440c0724404a6400507903900c0010480807845182000e032408100c1c00307100394808598002140480082c0440b0710006c00d95445504a10b103105a0401c82c1303c40d14046000a100315a07004044590342c801d0400e512a030b521005d162765503071900141581e022803024082480c03805c2c0d1b0402440c140c050205050300d03004840c0c503610600c004c282d0324844140c0005503080200c0d40c0c14444640075205418070000c841c1444c0c000034595542403c4040c0c4183c1d400911050380e244100121503440900714000d40d210981254042e026801c140c0c1000080385045c00c0d401d07094034001c42102c0c17160307900904590905505403114401031500420031504508000d03940400366500300400c0744036903410390581c1c1070600c0e007500703000580e00e16a0000380105020711403c8005800040c2c4181074408081c0c01e03000120212961201500d040b0700c010b5040a0610b420180c20b06054000b4030660b040c42c0c03410b2184416120910458100c2c0d4401c92040490510050000c84030f0120041841d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573199082 1250 573197832 573197837
    0x60a02160506210403140a050421171b01050106022103010b190c3801141c0c0f03120519030c05040b03010b0409060e070207060e1201022a0c030304090c 67
    0x4501d0307141b41103400b0b03a200c150300402065002c1360410a9500c8030b41a44c041070952954034410700844c1d0780d00040160f5600350b80d0b4150802081403141f18040b0310450188100d000000d00255945100103511038640742031001d9010407020004007641488401c807812148882c81d01450596504000800c60403000c07400010020904a48008540e101c042100888035014003140d071080d4841921410640a441c1c4101400c00c00004201c45650144420640c15080d11400c00d0005458140044c1924000f0000c001e400a100f0102e4041075240303000007500d205003190502548071141c19180c0d030181180100e0010b000441002409110380c2000481103407604005040c02e0b1504e200340010b410036013140d401d420300030038100302c804558061131008080e0149032013854204518002e4a41a0a0142e44188464040c00b000781d501d548684220f07807005840219140c03001030203080c140744e06400d0004c180000170043c41286c0c4101140901c88910001d00035072a062418244401030144040c8100a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573200332 1250 573199082 573199097
    0x402030f07080616120e010b130612060e070b0a020115060305131b080109050a0506220605060f0603070f02010b01140703030b1504030813060801030b0c07050a02060a02160506210403 80
    0x400031440d000346e121000449002040b80d210000c240145295110344c030411740c0382003540400c00c0c0c4002e0909041800c0d04154080b07418445843c0c11860700c94036a0045030400c5000581c0c0340314a5040d48030100b02d41001440d4110369a5448084096a405a40158105580214400c00078241250030300c04001c1d184403182000d681c814030035003100c420b400191001d410281880040220900249911500103440400e804800c3c0c403204001842c06100248040c0e91280800c5e0b0564405501a140d27000041035240d80c0e103094070004016070340ca20256000740d828507950f03580d2903000b200b54112103085e102c021030070104191411000f50042411480c0c00040459002100750268070040000d14012904035503204580320101f10308080960021007002500070051000906050000d030b03b202c40d0780c058a032100410304101d4145040c4400082d4008000030f070000305241c000c250300320f0ba44081c0c0d2590055945d604288116845008004104426001018001c05c130010300c445070814080c1c40c0984 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573201438 1106 573200332 573200357
    0x609010e030301180902130e010b0904021318050f0304082803080a0b0a0f051005070f0b041406040303060f0503030a0c030f03020906030f0402030f07080616 69
    0x501500e013030082d200b0862440d001006207640091040d01780a6802440400030100700500d200c8035400d040b1540003501d050101244100e0b00076081202180c03103202c0b944020180c40420920b401400d5002030089a42007058100c000d010000440c0d1781c40c1400c1d03503580380c6000c21518020400071007211901c0483c40d00f11b81550141c1c9424021081c1e19044101e4010b031901c10041303a00580c2c0907400107060285104010704030340003030340c802040700424142141c1038803902001a00d028207022404e07001aa40b013001075407250042ea0361f42c55240c0c151302641d04001c011345058000075201c10041c4500140c88505e03100500c4124011898101007031805480b54814003009000d21462175030b55024507000384c040f2020101c000304241d640380f61007100c02c1c0055405413401d900034030a2501c0140100c800044000644840e50014000d80e500c0304401030740a9144441d56082110710500711 = true := by decide +kernel

theorem cover : BRFrame.Cov 573021582 573201438 := by
  have h0 := BRFrame.cov_init 573021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573021582 ≤ n) (h2 : n < 573201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
