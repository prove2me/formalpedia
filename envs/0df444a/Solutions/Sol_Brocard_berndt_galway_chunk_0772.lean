-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0772
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:41:33.442678+00:00
-- url     : https://prove2.me/submissions/f2d8be05-8ab5-47b0-b764-7d19e06265d9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 138669064 ≤ n < 138848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 138670314 1250 138669064 138669073
    0x80a061508070e0a02070309050d081c060f06030f021303140106060302041203110a140114090127030c020607080c0c010e03030405010f090504110c06100e07080601120906020c0d02 79
    0x4050f51024040c50041c5080140c40e400038003c002c26002d0b01c43d03600584405403044078a0901490f220700b0729400345122041c024801c03020340407131030900c1c0a024150340580007140c1c16503180160030703000703820404e680104442d000d01201c03502100a850460040d0301800c00c541c010f4086069040c02c54901c1d0f00044209801000144241444443c500200660516048000c10490f40502e4104000028001d10501750719007c40c0c00400150060105040e1221081846c0c1c1c450303e0700103003211940ca019070307004040690221007401840300c0d4958818000c0c200b0b221003059982c0040c4455003c140d084a0241d8003191550500a04000701500b5120a0170140e489034007080000e0b5407070040d881064100301c418440750500511402001c1b00400e4003400501042024804052058000c4150710300301c1d1107990b00003200e4600c1460b8090440721a0360307085c50315883d1608122400c681c014201414041190754001208000e8458104a80d020702d000503147c4c4424030045040003408054041150300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 138671564 1250 138670314 138670319
    0x703080d023c0d020c1b0310050108060a0e070b0406030609050115080103060b03030c0118030206090a031707050415020703031d090c09040902060d0b0102070b1c090804080a06150807 80
    0x521400c81210310b256018103980f101d0318081c011020f0b209003a5582540e0003010f6081c075041d070704011051041d0300120306440c00c0350300345c403d00e0080360001d00c211764a0303920031004100e4028041e80501e065854500a0740c0c44542c4804044100d80d100758002c0000964a02d010020700080c2d01c41c0b2400743c02e401c581d1060507944420f008222645c107000240280782e807003c0c460f1b6030b5503040040ba100000301038000e0164103142400320084182e409801d401500401c00010303112040271070000b40c00750785611858449800b60139082c101c1e840c01800c4106103e030400001c40c0c040c0c01d241c041c3c0b191104070360081c0452400c5180c010118900b024861800302c000448684d12603940034406503200310309007081078480400d580040c002d44215030b40a904184001400710381440103403c00c1c02903c00c2030f000ca80400d5901c07088124544035850580e20800091a8908030001064100002060007204600d041c140c8510642e4280104000c1c126071055984408a00d81103106101c440101240c5019000d001d1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 138672814 1250 138671564 138671647
    0x50f060f01050d1203150e04060b121c0309020a0305010207110f0105040b070c05120f01060b0a080402040902030c03100b09060a0f12080d0c0518090601200703080d02 73
    0x1400c4000100103044042d500b04c400c078440c0e4003104074105181d0b1070100003a03451b01800c50700c0348141d505072000c070b0501e103e114090811140d00c44950402030003c020030901c0e4180a80c0c0c460041403a0300070162640d00d5080541e0b90300da102c901840c0900001030f51865140f030320810846020f01c40034051640010306405d140e812000b900c048404003030055a44560914122501803001d40103194003000700d020180110303000189290f501c1144200030400c42c0c0d100c0b10400614001c0300e01c07890000300b02c0b200041c01401c0580004440c0d078800b500300c6d81010080c42c0000d040a80c0350104417110384c0c1e942c86d101c0302464100c2d41d041d0401e0003078407041c0000d81031030008048203490380504081c0d0b10181030b110040003200400c80e00001e00a610030042d08000310307401040340e40007140c11032405010780519030251400d0600580185816103800b000c035825203001071548030702a12041c505000d00303a4000042441c100042c40c0c071440312280180c0c0da54030081c19861116001c14410700954802d23030b031442c110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 138674064 1250 138672814 138672829
    0x1a09040c050105130f08070e090102071e08090925051918030c030c03030311160303051e0f0105010f090305060705130b070606030c09020a02030318010207050604050f060f0105 77
    0x310700a1900e10360b0381c1c1007681c3c0c00307140b101d09a0000455038404440059030f10b10103d010002d85501e029030103403985514080c1401c1c1d005846028101c581e01c6c2d48a13003103a6442808000d0254841da1020b0f0602006074009818900122828422110700800f0003403045814424500c6207000c50401d282080d106014030401100c11485240501141444407844800702408a0f40155030201c3e0340e02c40e085e204e25040410b51990310003100460304000075100440d414030180c17048030700c040780d00394807000190310103c0160001070012140d80e12101c40e001001c0e44400011b901c00e000440740440035516241c001404061583c04540820034000000e000180011440c160011100e10700240c440010800c0d4100d4041e09600000b10380300000340040400c24160400390440c0d000b902603514082d59400ea001c207a110741620080140c00410000d81004016401c620400700c68000050a004881e660b09240900c01d45041e5665840345401c3d4103080e400f040079030ba0180c0c041814442c954904004980c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 138675314 1250 138674064 138674069
    0x318120f0313020109050d08070303060509060609041e060902070b01050301020f120601170103031709030c030702090a020408011515030b010e121c0f020106050d030801030803040809030304091a09040c 88
    0xd400e402c40c0001560f200390305003005001e00610311945d01025141c1951242c0c0086411004a030178544001114900000000e1090748054401850100c4803420000204041c280070040b0f8004603003c920400c4007441910301034005c45e10010b80c3d1301c0c60b41c01c01510804059101c1c41c403a80c0100010420310300c0b4103092710b02d03a0b5103401110342603488003001a50034581c52000603c10800d8800004107143c1d12510100280350303d1040808c06840d9103404584034414811150500c5c0e00800641005080010803158060752915006040944841d40d29003036031043d01c8a5203203034116100c1440034514952031002c01152504041001c81c02c50b00001c0c00011841004da072258100b59404c2c00381640c140405801014201c03150700a41c040140060440610070b501140150b1a00d4004142410311083c885425600b580301d030819a8a150707101292580020802c4414080a1002c008191010400fa0000d044005004962070001c603100807a2180c0c1b1039a800e216260900601002c0707203404021105 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 138676564 1250 138675314 138675331
    0x5010602010b030c0a210c03020306070f0305100e0114010306030f060203090709050f01050913050607031a041103160c0b07050306040506090f061003060f08070e010f0609050105130503030318120f03 87
    0x140d4000a003003611f4280342541c00603405000303840400030002d0340310540214038034490700d0030000c54035446000a03c601d46400745540c1401e82200500c50b01003500d02e40d414444d014500492803070f0301e80d5034140001404040850b1420340120501149180034082c0d60b02400494104100502d80a01035030021039040c481c0310700031103200d40490305802941158040b007a403c00202c611504224000400030712040c00350f4205007104101c00509460180240c514050344400030034290786843c49544445001c1c40001c02c28030520400c0100028501c1c18807a201d44850b0300d54a4aa140a00601080e11402000e59200341101410000711586021059070001002d40310f040085258120540c02420103810201d180c1b4071000e800500000005095001c2d00c40a15000749580d0382c990201b00104464000d00011442c0c0b1a0700744240d5206101426420107884c000d07010550b90342000c130b411940203a98080341ea01c0503c00210021700700300701d44007c00020185080c9085a0064801da440c003000d0051103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 138677814 1250 138676564 138676619
    0x6030606111b010c06020c06010306110a05120c09030a06020409050112080703030b01050d2c0c1804020411160302430e07080906090703030509210105010602010b030c0a 74
    0x200d1991042504c1e060701a4020030456680300004a040d50b5031100340320403158182045410030040d503030f00082e55160344440d158282401e84a0243d0811401300410312907400ba4180000b00c040c1c0e81c00c001750403070035001d5100140d803227090101d00c1c27041e1001600301000f400c001411120001c4c000d00111451160903260015609031501c0040700c0700c4c0b0032558014421400c20041000031a841191040203100c1006120341c02095818502d0b205c120050400354401c22103580c0840b10b401540391503903c640300401c000360102c0300885c0d141d810b8004025940da0040130511140400d5010040d02e04c489068200020701210048a0395010400c407c9410102c074090b01031610481c020300801d08007a00c0355940e03901562a0035400244190412514850944035040216212003808510700081e03c0e0190740300e9103440d6644003400001d19001030240503103801c100320400038400c00c0c03141c0c0307010304804d90004c5080d00c4080109898040e0350030501e485101001e00c1044920101c01d01030000c100c03e15400b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 138679064 1250 138677814 138677863
    0x3040b0a0b0603060d110f0a08011a090c0a20030d050f0a09150902010e0a080d080c040b0a080402031911270a0b011206091407020606030d11070513060603060611 71
    0x140351f00041c00b05032604090320f132201144140064000d003143e07408100c54200c4091030700080103800384090350381d0351070101d01700440f81d101f43c4528071b40001500000c00005d40384161441440c07541d4418551030a20995840500001419081d002d42c0c103d080c03100d01380080b180544036902480040308446540c550f495006a0859000d8031860110030401046502c440d40c6d24444e80b030301d40100b21908000500e05900107103c100f4100103840544102c030904d242407100c1e841e019141184e019100382d0389446080c4000749041e014150000800d407040c5042c1c0070807010582402074541c120305220b40c440301c240c40400101e0120705102940146c40440c00b203854201240141c65482d05070070040304031400c0c94004555694030760440880044401014415030740d5100003203840e10b1066078041d030716030803800c00f1700d00540c403030a55020255003d500b41c50180e5601c10000e00d000c01a0031300d40c011140c440c40204281c64161050000070720140c03e140c9010f0340020100e5807265000710030803034486000c0190 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 138680314 1250 138679064 138679069
    0x9060305090703050304030503030a1b02030403030810030203030a02010b0405161e140c03030402010f0518040b0a050a0e15010f0f0c08090402070305130506041a0f0903010203040b0a0b0603060d11 86
    0xb01001180c1000650b9522900d80c2070403503c942c001c4842980103400d10070580010f02c629042911090003583c003660500d0701395035040301c107004040c00c02000481d10680100160b90140000e0410341c47c290000203109010000b48025900d004181003030b01c410007040b40000c02c1e0444000ca8880d0b4415070505400210504143d405a50046080409003c049a100e6182d98000300850041d4000d0f00c804060381a0b00d00c084038a80700d070791201008440c0700007104005041c40d80051a00100003444d418420361140301043c403154450780308540804051080c4000311440c8000c0c060b500c03400780380401b0803010404028141800341200c04082124400c0c004040c001501d0907100100c00c02042550b4a000e1400c0085c9030360080d04c050300300c21400a200103001c2c40e0000c111802c86100d10b584200452003903d503164141c004030100c00300c09000f0007c4138015a170a100a5104038401d0305041102e0801100030030443e206694828020f4000300284401d50369044208424540c0c42400007001c068070030003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 138681564 1250 138680314 138680323
    0x5040615051b030403030f080627070309120905090a05040f0206070516030305120702010507021b0a0f030317070224060319060608010c1d04021e0c07060f0206070906030509 76
    0x5098403d000c00f103004010035501280140300c1c01407954644107151a19003c2202865159281c400060000394425580c0001c0104103030b03101c03840303080c0000c55003442d446039600110081103510001c5c8015405105624041d0500d40c4c2100310150200401d103070980d548e01741c9024042e0f010b40310300d10100700c01d02008000c00c100c66001e00d00c3d001c10f42001303660780360241858003c80a4030b020a500076000800c0e203441485400d200380c0e1280d00401524801d401400c0012810044403504841244404642c0d5911070749401d00541c03203542c03664081c1c0c0e42c05110069054000d880102150000c410a00d403403070040340018204410307000500754039211074001a1801c0031180c24503448a040002c1d09092125035400328080f941064001d024460391264101c171400030a42d441440c0102040405020b4206a80607040380c0550310030040b11200c3d04c2c00b00e100560000d4803803003120380c02801e080c48010343c000300b078180d5451301d4001060b15050a12000d003d803200380c0150002c260f903c01c00141e00b01c00800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 138682814 1250 138681564 138681607
    0x30609060d05070f030605090a050a080a0c06111902030a020607030f06050d0605040501060501020c0a0b0318030c0109020a090c170408160309140910060f0e27010504061505 76
    0x300d0340f20a40e031361000c00b01c0648034030055504910307001c006024464045900488207900002400200003590b03144516900a043c440c0108540001c1c818001082d80c4035031500c030b10740b90405617101e032a001c81041e4140590000d40c1c0846d0400e00075146402c1d000550a60440c140c0d040c0402e10741600141d130002840309134052a030146161441d4401e01c9655072085000e03a01070700091081070386540048ea5a6050704103903e0300002d12100030485103500002039500309012500203145520021b00092964211050700c40c4245d6541e22444210714003284034100418080c4400c0c081c0c2c00020300050005160b0a038410070b48000e00d000201003056550445407855400c03285880346003030314100104106001e029410003410300d401c2d80c2c19580b0340207201c144125513103138280d0304281c2085030444032004c90b1031840c0144881c03083e010340c2c01d0780c440c0d40300040c0480300004401520110a0300846a08041c1d00c8140240d00c0c041c2c0920100001c0c1c0c68444a88070107041c03d1b684d4a00040741d40c089810301d00d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 138684064 1250 138682814 138682823
    0x41202150708071224050a050109030204050604180b011d07080406092f180f0601300203040b060108010303120209010509090907030c080f03090d080c0a0305090307120206030609060d 80
    0x5c00325100c46066041c1c5640502000ca0300020b82d5a04c50050000c02205406998041441542c0030001032916810103540020054030101f03503a0301e01c100341e620384d0342482011200b00001c48010720803a081c0074050b80ea0200b4141a859040c104000050300102001d04081c1095895401c0d64040c8015040c40704880280083c601c2e054050503c0b0349001c0038407a610491095a407074500701c1d07165462140f450701502026012080d40e807100c600541d0f68a44884281d290001204c0c5404000c40300e5210121041c0e0030702030b0160f0340340b805151047c00814000e06560500200c0302c010320111758804070100901114000040c0e44520744001aa12800703583c190382d0b4001541010003100c2c03040854418116072090344c1a14040380c40c5d081d91030f00c540503038000c55900d50081c028104149090001025050f020b105501e10b041c842d24203c0c3c0c00c1080d81c0c203060340800c2c000100180103080400031480144070a250100c26059954005402440040c1000788101e0351000420319036514034440b0196079500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 138685314 1250 138684064 138684071
    0xb040f0b01091a040b1819020d0903030b01020d0f05030c0d02030108160503191b0518090606100804063c150806070c05010f0e060412021507080712 65
    0x15034180c034002e0401c81c0300a045000c64010500c820f82000d00918031111702c02008107101191212800b2031054004040309410781241d0702d078074041d00e000c2c40101040790307542d48045494002410084c0550740100421811588400c280d805015400001801400ca1074a00036581e5292421003860034000c8051016a040c40007000103691040000e421514065806003400c085a81c1c10800d0348440c01074800362187c1b0803505a400020f080519102650068080c14038450f6460301c0c0400c80e00c5000641454140e05d020f402d00084039000c016007980301004640f81182d0800540c4003c00045001c2c10050040c1d403141c032184035410100b11640c044408216001a0a19610b031003822441d904503842c1e0740c4240341001450848206240c410145c1c3c2d2018020031803602c400c0f004039800d103e010350a54155603a0030070800280c140c0c0c0035a03030400301d44400a00c081d00705402c042400e80c003051122802d65200c0b002c0010015806000c6960110301c0d400c01c262960b6030383d502525210202c45c0c80801e45880e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 138686564 1250 138685314 138685319
    0xc1701181d0f0606030d0e1c06140c0d1505010c020f0406030b101503060f18090602031006091d010510170709060f020d02100f060509040b01051e0d0b040f0b01 70
    0xd00240f601e2107520120308880b080801d14505540e080904069150025181141e0303000e65001e4820f140100c45c4101750014108121007145030519105032404651000d00040001c1c4501c114010904500100100030b09017a00d000f001074588141c21000078003c0f246503101065a5483d0b92025000b150011070302409850426850480220f490060000f00b612500440400b940310784145426150301001020340386080c031002c80200340c144641c0765031071501d40b50b10000244039800a94042d200f0307080466603e50404a000d00f044103140c0010201109c0044c0360503884d03550113080380c11141d050355182280950844100c90307803a900940c00d800782110b0000d0100c45a030014118003266090303540c405104010b80401ca8484160036400801a8801305140c0400119607216401011f20040c00280d42992180072944d850401c50301960301305484001000030f400d15421071b0000c28061a03400240031f00140005035419001c00018180c0d50b03009000800b00241c0d2074220310751307581007110102d01c2e40c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 138687814 1250 138686564 138686593
    0x70906031103060702010e0304030b090f0706051c090b010308090102100504032a0201020703060209062a1203040503391605060a121109060705010c1701181d 69
    0x1005007040314080e110303030000a44514418400c1c0c401089031040554905880e54031694080350300074040e0003490085807031001d050700301080b0180040480f500e445880d100801c0c0035140e420580c031083c544590401c0e8940c1c0018038820505415280d10141c0380ba15641c4a20040345000c400e01e0319015860302c0c2400380028140c1103058415400008084602c2074522178a058409020003100240564040242400098140d40152141c410040e02140c140320900b03003800d802c03100c110b0340303607600b84811031030b0a80e0107000b4003401e040900541000c034514101669030595034411518642d141a4001e050000c0c0720b403410300301105003000c041028680f1040101007a44603060942d404550078040c050026441c01c0c40300503951024900d072900d080d650000406403001d4070512025080c0507204011074083c0b070f52840d02411540303000e4400051a000488006095401180710030690f4410020040000d914840e40c0e425605036100404581c600101103601c21aa4060003011901d0048550314100e15 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 138689064 1250 138687814 138687833
    0xe031b0c19080d050a0c0f02120d09170105040305040e090118060b031c090311060c01110c250302040b0a03021201360209070c0b0709031a01151107090603 68
    0x4030700c40350594034048003205003924140325800342d005c04541609a140003258240c4516015180040c000361b02d840c01032001c00b41071031f0a41c015100411828402440200d14010344411940082e0f40200818100790728003801034000c511800c810204644000b81900800390091010051103401e248992051403074014040e00d50981014020710a0503d013160740c0c4008841444a41100e480c0d010b540d078199112100b8020b810500150010010000304010110900c2190003113119000040d40720240403a6003820a40510340c0c841700c034151480b107504880406079201040300e42c1241c2c00501c0703407482400b0408281e40b60748080e6100b01c44803255410800190482c20760b600c90b82e1040b040045050210682040c1410b40b1052500010300701c910040c200144100c4e082409820000f100380c0c1183e4814034000c1c4220350301c5001800b0704e5020420040014401d0120300707800c248840d03096041030003828551f68454802010084031000050043e102030080c14007921380c4060a01c446a100e0403d881c2c00d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 138690314 1250 138689064 138689069
    0x60b1207230a020c030106140d060e0a0302070303021c050d0f0b031209010912050a030e011106070207030c09050403020c04050c120c04050f060c03090108151c030f030e031b0c19 78
    0x35010700060601d080c41e041c85a0300c262440011311040342e0038910300b48414011260820ac0b40c0c2592001180303455902041500141ca20950051a150341145030007130a00e205d0f5058881601302886103d04207580100640c2c4032801c0000001640906c020712540142c002d0a0150341c240c000c02c0a156600010702e80284040003080c0c8903c030105540b45024011480c43c00405044c0c0e410050003030b00024410f5251500d17a00e0140340c00b015025200c00407900700b071415501800582d100744010020808800070f0031009002d074100800c80b45c6841d0710b01a445000d00f20b00244555914000201000c5c17020302038034a5211000d1072030307016203001244504c0560050054911900d044e141c0b40045242903004c03942c114105102860500e0700400056982c078030302500410070200c1c0028440003075141c0e0900b0303101c7c05540755a03026841030981406044114604640c008150500d14040030480f00002151856a110305c41a18101d00c02c81100b801d000305050300c6540003001080c04516207a04002c00c005 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 138691564 1250 138690314 138690317
    0x1706090d0c020109090e070f0b0c011109090f0603030c1002181203070314040504020a030506100503150904020a09020406050c0f0105070c030c060f0f020a030f060b1207230a 76
    0x604141000207076035501004900038001889a4410310031401580c00007204104240700311703011580c031600c5969104c0910b80010045a4010030b140d400090309006000941070054806443e00500d400810340c141e100902c40e82640c02c24501080e000d07201007044480300d443c180142c8030480391035030702140030b50301501e03100100c00c0c0d0350750004080345400d040041045400e180154506420740da801e0b60b0325850002090180c80d01880300103080c1e1102c0c00101030010181d0f40008140ca840d20400c0704180e5480c040b9800c1190500c00c02031340c0a1000d030801151501142c070114542c1c4c6901c00201c05415903000146540e00202d000900150404041c0c40d10050700c030700380c0303408400e00a200c07800ca42040711900300046903991a080400c1c080c11018510034001c0030003142804910003500e0540da01c3c603181c0e0002d16400030340d442801c1d40c1445001c50900010f9800d21400e4a05450103405008400890340d0103401d42c8049858180164000100c42c00840304100300580c4007480c0c441e0300d4012000000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 138692814 1250 138691564 138691573
    0x3140a020c09060303090d0b070e1c0b0a0e1e03070507060c0b010b0327030c0d050405040b0306090706260403020a0204111303060b040f090b1006020601080c040b0a170609 75
    0x20203034030303010054a602c0d242c050103009034440c5e20340f08c8060302c00700609400144064503090742c403103450704801041d030385170228050a5036070728501c1d0400d09442c00601c42d40b100d92820308010400d490203d9081400c6000c9640c00e4070894018030110b0540c4207589000f032552007000070020b2055000710b42c242d402402100c0b140d0309680e8500d441099480708031007501483d60401411a050400400d213501e02001c044101d90610360b0030865546881c041794030000100718040390420141c40c0074003034043c00c1d1364290b000d0103242c1000b2005560b28001406184207200d220480078442d501e1417202000c0700909042c0440d0181000c0c00e001c0e403521178130041a800b0307504081060111415000c00c07104442240002881000d29545a12008040c00184682d0003070300c4021240c80da8903d4083d482d02075000740d80b000710b2400d10000441c00d5078181ea02000c195009140100100c4c032020510a04022081e40e0100b050011070000407207a4449401c52114003458900141240400181d0680303ea0714000c1140c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 138694064 1250 138692814 138692821
    0x6030108010506120a11090417070c0801180503121b0a08041704080c010c05070f0803040906050307080a03050c161502010f18291e0c03100b030403140a020c09 70
    0x1325160700503410b01402c2c0c1c5004200c448004e0412070012a44039020752000c01040d8060100c18901d60f1000b4419a140c0f082040300348070142c0e0a104120744d00c2c08222080141c900256552901c0b4000c0c02e01d504c2250b0b140c04002002c082865138080245c0c803240c40384603640c3d2130341c0c0c0002d4014030381030f01e080e956881c0101c40c4001030f101040072038007a5091480181941c1a12500445440f20411822507082c001c000340010682c00003106803001c0d100340805544c440781804c0c04441140c10b10b41c4003038070030360103510f04200040002c12040703003081c2c051415a54400a84100c1ca143c00c00510086401125512001455103a000001c0c04d40c00d1040d80248030440c5006200e4013900c800d4034141d4100803600780b803400003801504000842c0c1041e41c42c00885101e9003440c910130250211007000c40071200c01c82e450381e456001c504107548816110703046030035070524070403007900c50f801406902c24a14001010505250013020740082e003a807541d0f00ca660300e86c07462400a440700260340403c3e01600040020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 138695314 1250 138694064 138694099
    0xa0807050f03010b2107030e0609070f0b130b0703080601120c08071b05070e010815010605040306090305270a0b120a0b0d0b070201150e0402010c02060c0c06030108010506 75
    0x1101e2121203004052419079080c9180c0000d42c1c0e224030701c1d001c0b0403c0c200c14803485552124a503144140116140061546528010203080201c010031680b0160001030040c880650152000c806031443c02016540b035890405500500601c250004048201c010130104201503201d802148500780c2a40e410b401300d0240030100d4165403100c14000081800500051440d41c411400c07840072454940742c82c0c00b84c0c110fa0700c41a00701200e940220041146840041c40504c40801020b410104c004410710855032405a004085001d1400010190b0b42c0300c03040c2006051203141522605901c401915080a408546d0365032030010f08460540607141c60580010003d80306001e13154141c0380c2500e01161665801c10481c014450844030940c018161100f010201e154500c4c180d11914141d0000500181c4007404d44485001e50b40c41112484e031510304000040c2da101e10a1400603605a51482e2201445078031141813542c0c64201c1a04544040000650b843c015000749015a00a4554144010050300c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 138696564 1250 138695314 138695317
    0xa0b040f0b0f010f05040e0c0a08060102030a090b07060e0d110708010e19050a05030d0504050601050d08190909020a0914010c20031f020a0801080c010c0303020c0307020a0b0a080705 80
    0x701a500040c014111040c070f5000d158210101211341c50494903060301d400540c82100d10654015500c0100810320011f665080b44041da00300340240021400d15a07020402040a10343e0300549e1040040469440c0c02c100e0146c01034015603484c4002e0314543c031610040106561301d140c4841c84280304014000a00b81c406108041c2e440c074080020703140208500e015401148101d0030100c6084c403032441900d01080c0184040d02000ea01d03010081901e05050800310300d0a60103806c17581c401c41500c0d8460001030504070444210442c41c405100c945240b030a4103942d00c07c181e074407152081340000340304291650300080c0c12007910604a0f10100d0079400e00011101d103200200c0041408160454840c42c7c8040204030002040c0d00a00316a03400007042003ca4403400f800303582c0007102c3e401081c02003449800100c5c04d80505840001004524407000008140c000040409010f060b40003642190b00002031085900c203075005442141081e0b5074a12450302513005400e82400221141c011802880c440d50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 138697814 1250 138696564 138696581
    0x2010c090b0a17061504060c0b010509330312070302120c0c130605060f070203010e0f03030705090301150308070308130c18020702040e01061502010b180603070b030a0b040f 76
    0x540310f0424050710086102035001c040c1140794030000d001d480b0000600482c009002a040c1c0e51b035079110a00c101d14010980c240103810052062903c482007224102043c5160006001c1e40101e8070341000710b0b40707207840344a0b00040c12140c2500443c0a1843c0070710400c0028050300d40f1039030849071840c244040c0d90301c440c0211084801c00390407040c0700d00007600e800041030540c6254007c00041841e0b8960010314580d01040d4680b440540115044040d13240038414080c1c204486405001001e015000b03132500c91100802c00401e00c0000f00d081e20301a00c0075884405c03800e12003080310601036100c1c1003285031904680da00320001900f0100040c0c0400c1c025031800002d50380030102103103c90900c00640d8050b01c04e1140002c0305070342400801d0243c5d03a1405020050003c10000164641c18111612201014164800103580c101980115162180c0d42400340f91180c24414900d247c945200003420041c85a101c01e00244000c0103000d074611099115000010003104c0800c2890103501d40c03c0184c03010700 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 138699064 1250 138697814 138697817
    0x307020f0303160e01020708071814090a030315030510051f0609050409060b0d1203061203050d110415050c0d0804082209020c0f10090506070e0d0605040302010c090b0a 74
    0x2400311290035008400b0918104d205005642d14252034080946c45d02d4a250300c65440e05211001c42c40c80c4d030256101d041c00c0383c1650701c00c030170503440d080c00c5140ea943d2032070300000c1c105039a035189568000b510031540e002440d404016100000701d110032440103000c003511100046c04980700d02c00203060310a4600e40848a0310707102d4580181c940303810840201080e410a82e0241d8542544080c2a0f8501407101409445203122085485001c4401400c568240c0c000e5141c8081200d41d410110390000161a0007400003000030401083c001d040c80c1d118000c0d0f40c000e10a07183c180c01c80191464100340903000782045d0200f00c07422450b542408440241c019600505050000c0083c1e03045401700751413100480c44160404c40c182e542d00d04080040f680b0680f03c440e240d4000548003180f000e018030840903c00304640090100346260340340c141d120100508031000b8000d224680300425118802480d282ca908528104014541414042c4c0a00b603291010000160801c4011901030300281c241c6044c00007d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 138700314 1250 138699064 138699091
    0x140303070b010e04030e0d0807030f1b260f041805060105030414010905030c0d0e0301021e030a110f0d0b010206041e02220b0a0b070203060c0f070b0403050307020f0303 74
    0x30030301030b00c510010184c01903040206c84040f01c5220707251214560100341c0b1500890b56640d00c2e50400a1491042d0350300d07039080066022450341141d25682001c403680303400614090001f400b4105458a2402040300d00040c07160100d08280e6200c12000900708450018669100c4030f1160902042122002c40310540880d00c2400805c02188440f004600400c29910000408120603260107103150043c80010f80d07250301040340351101da5400039688141d900e00b50002c0d420900d80042d61300130035101091703c40c0c1e13401011000411400e8280c00c190031700c80d17201705455030300d150052a042142d4010008541201d0818036070911a51000070014451030700800d183c1a241500040c10080345040b840580c1d00020501c44502d00b4110034a00b081a585164800150f00c105941804000e5800d6032190f28130030000d000b440e0143e00c0100e50154016014002c1550301d00d0300c03040a1085009602004d0482812042084200340c1c2290003580a0703070b000d4003180e0750b1500380c2c24216501c0c84102e9101c0c40d026103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 138701564 1250 138700314 138700319
    0x302100905090c071109090d091a04030308041b0603020904050708071d0402071a04050c06030c0307050f04030503120912090609060a030b092a190c03020f070f140303070b01 76
    0xc180054a1040e1041701201d1404034554002043c054069801ea0f0460700310240415102d034000714840c1c0103000000340d0b40490100f000c0b4049081c0254071000c1c00f846801400a0100241d001c480641d4603008070705100a2912200d0047c0250011404035001c1d1340b070070020032074580c0164000c6105088940e01d1043d9a02552070006410605119803030b0850340a008140008900000b0850800400349000816181c6070400d64a0115030596060003180104107000404031004d0440b58418040c1c10b0961f990038140030384800302d208503880035001d4000407400d0420f0840d106c1410780030303424400440e1001c02c681c00300c0c1000b5218668059503ca2800c003c40b40d0241031801c00340c00400424107000503103601c0074000c205800303000c0b161071400c7c019501d805c15072040c00c808901c1d51842040041c600b801c40d01d83c50300342031020080454090024611918007014401c1103d0604905801d00340c40c2d009aa850000d02d00c018140240904645030041c48050750500000b510480d5030403c1c480000ca91 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 138702814 1250 138701564 138701581
    0x40806070e0d020f0f060f0c210703030506031906020304061521051006081509150721060f17030c06011e080105040305040302090f09062206060609030210090509 71
    0x204030b01981d404ca00c85e0702c46501c19070345002c06894582401111207541d1214107006d182484100801415000c182c9140440f03104404416641119854113000460b6291407000a2514581000007452000003405900802030300b50040c5003e50310501040c030003034580c3d03844801d43c0f0f0403d004144540c8007040c442d00305214410108540140540b09440e07007100c0084819040d180e81d030704610304a900c280c8691b03c0c42c02c154860300b075016140c48058041100070f40030450f0300d408080c100700d0030030088074018204c1c00840b07210080c046892000401416036101d00d80c580d444210303c076040903000b0308801e00c07094040100c01c40da0020b0040000e0b0400d42c0c2060524055019808030082075800c50040c0480c00300310911919010300e02035220b440d22036155104200320720038003c0100a08170b10000502c49001800589581c00c0302140c0501c04059030114010602e100c00042d01400e22070400b01300040390303504000400700f070b84d009139a00e410120010200740e811120300e206080d000740c404d0002840f4078 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 138704064 1250 138702814 138702829
    0x17060310020d11030c0c120307080402120316050d020d110a0602030907181401090b100807031104030606050f0303030405030f0a0e0301090b150409020a1707050d08040806070e0d02 79
    0x800d4003100001c543c000242e4000c49074004450040c01e02d20005444d954032101000750030500114200e040b4910714009200400e4900701801c028020701c0182c4403110501e000303001f0b5810040445511064001c07850405a40e281508217001c005402400c0700c120445200344c0b25420b03100000001841c0c0c820003030b03494000030341c001003240107640108000400c40001c602505190041890004100c14004d5902900550010392040034851302d80720ba04071142c1c51b03444007412a460103081185441d50342c1e0500768003516540c4c0300b415000d50006808010049280e00040680354266420656590054107256030792005036405800f0340d2041c003001710440a0a00107182001d0079141403007050391080017227400e4610003002210039420350b008000c1041e040801c0030060030821102803203801307055004030b5071400d400d01071b10a442445200744858410200004802018080e08126402000f41031040240d0440c1c02449118003408001c20304452003046171410b070580c014524601301d03220f0390801440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 138705314 1250 138704064 138704077
    0x1401020c031e150a0504050c0f030d0c0602040f0801060e0c0a02071e0909030302180114040924080601030303150e0c1309060b0a1b0b060603041106070f031706031002 73
    0x361003103040400043d6450052540200c10065001ca218203003494020308020211110b24040d140c00092940207a07400240a0282080d9003842607210030a42003480207403044d43c1020001d600b4110001520300030560007401103e101c22000342c06601d50208910f00d600c40c40c4500d100681c017102081c0328a41c1c100b51901425041d11240070515541c90b9045001e0300d14a13501500030076408160000241802801c000717028509103400c2e40c0c0d140114400c00c10718015401203061640d0b0b50000c03100700c80040181005491031590342c640d078442d500ca2180b680c0340c2c401d000c1280020b081008041040d00400304140649002c0c4510070340a40d030b400e41c00a5180c006011900c40b520b407402c0001059802d610585000c0c100d0500781917610405001e01814880304034242c41c450001040d140c601081c19811016002001150380540e00e8440741400082031083d540115840030f00003401c8000c00c0000708600c240c4511036107503e400702c091000304c607222b803900712080c1d40c0642203580398448294565000f41346 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 138706564 1250 138705314 138705373
    0xc07080a260105010f02070503070b0d090c121a1003020409051906060f0509100509061915030f02070209010302040e100e0c040e1c050a0504030b0f011401020c03 71
    0x704100101a40e4071000c1c80864520300c0707003050700051045580c09604c0c2400e110305400248000c61818002c01ea4400d01c500c2009030300c0c0f00101791031105544d59000f80c0d020300e40200c004481580c03203034820b03401404801c804842ca000c900105001c84210180c1d1903102d0810039400d085560b140d81c080c000076000c4044211294043d07903c102540580ca010006061801082d00013009414084001d0081e803035900058440e20000c2d0400034451650307007200080d5042540c41c00d00a44440000c555104034272078042d2014401458081005081c0415901c41030603d5a0700f400010042c00d0103608034030846c0c1e800ba40100c001c13030050000d810160001410105590102c44218407540c03412401c66503406030a21554000500c907000324138160081e5021810a4030103020302c06040c1e0142c400c030107401603142d410302001040701802140924180c44c020b6070016440340740ca00e8144072492240500b4041c1d281404501800c980d4031b940700044c44099144050b00a00c5088221582c085540360b50f0f080300740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 138707814 1250 138706564 138706577
    0x70f06080c090d2d060b060720010e0307080d020c010c0b04020f0a1505070605180601030b1b0a0210060e07050d090204110a120c030c0909051005030d05071a0c07080a 73
    0x48448104100304c5040070042284800d000078580750031001d40d01002001c80c4610b40c148820004102d15944900045400200c50500c140c1d0032401600c803c088181495854001d1420000f1815004600f520040507587d0a0310342c40d480720f07001910481c0018001900709001200000d005090105c649560114010200036103581d6130401421a48000008940090000f02e45941000300718000d5030b422002d10303208000c00344c4a0300d01d002c4d0303240c4052001401440d10701d4040307034209800c1c03e0302000144001c894a80d8626031360101a60318004010310f00355407441c001001031108001c0c051103001d24010b54038180391400e1030303240c04040c040000069a10a0303030707100014916540e1100a000b000300c90744414192044405010f002c0300c141401420a0605155005410541c030002d05410746c0c0041c10005031039205c01e49030196812031500041c0e014030450120b03441160b005805040024400e101c140180111004100d400030000d96039030030420014014a00020301120140c900c2401c24039090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 138709064 1250 138707814 138707843
    0x30501120b0f0a0f061401120614100302090a0909051606021c050c0102030424090c0e070309020a0303020610060203040506070f1b03110a06051207031a0d05070f06080c090d 76
    0x2000c1703400c43d5204480d015a102d1b0020444d580048640303450444124040014520b031000150440c42a981c0b010712030f1081d04110856140070790f0548510a001421811140b600c030031001d0020311440405648501c01c202d03003425952202010541620032540c0580f04a100c905038280428502c5100ba80c240b203c00e20088820100c02d102035071241e8050308101d160506400a0000410f0b07940105418032814148000c000c11802d0f51000e04841d640082c10049580300034044008015044000b9800301c0c84039000010702d40c0c000b4121b405410940020207503299180700a03030f80c910540c41081c1d0000750030300000000c40d55030300954500c10700420b42c3d03020345414440100350000150f08111134241c06460580440d04000310008040d00b0b03103040c224030b0030b4182d0000440301640100140201521143c03040d07102d805148450301d0040340a003030450a1009480c3c41070b01c500c602e016140050808140005d0200c1c0300c0e030119401416400d40c030501d050507a07030a01c01603581ca5402690380c665000ca48 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 138710314 1250 138709064 138709091
    0x80102070218060f030111130b0f07020d06020409020a0e0108060f030601050904051c2105010b070204090203100207031d0307030f0611040e0c090f040b0f04090218070f030501120b0f0a 81
    0x3d240c1c406d04050003288d900c441314500041c040081c0d030802c08003010188801a0101c000c481181e200903011a90b06440c4031040c504000644600c0d0000c1ca030441c00481d603041801c0d00031122107038108098851844a583d0503003403001c120358010045a150b48840c2c010045410700e440015049401a0203803007002d01106089000703198040c44880c0014200c0301d40445050700192407210341504c0b001d09000c6c0754949110480680901000a03104559402d844011540c2c1044030a1110302000801c0d52102100d040c050b0400111b15100e12030070000e000c0e03214807842c02007421810740783e1004494210410341c0d04d031000145040800c03001030368410440072541e203916112051160594284082d550b4a50600b88000e408502d90168081e50408640d90920317a01c2a000c540b003440b0503100051040307428000500da4210240105154410071400d1020031548081c844140300307480c3d00c0c1800166641d60b08078044112520000d04020006404114141c10306000c00307400000d00b070000714690110f07284 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 138711564 1250 138710314 138710321
    0xc16110301090c06120915020a0c0b010b13080309031e10060b0d0e06070203180a0905070306030212060606091c0c0602030a11010e0d050f0f180a080102070218060f0301 74
    0x2010f0b1601c000070401080740c076900ca610300030040f24140090021080e02d0791071040d0507011014a01c9116004156079034418460402d10000c20381241c0c0c400103035692510385040780c5e8420f100105070300c00c2c01640031030840d80c0002107407807a040c058001d0083d050040b1442c1f080e8014030307840304407a000e040440c9070303000c10034007440c00500400071205940e2010107444000b26005404400c0c0250000010042180d40100c00d41d04065410901413a5040d100c00004504402d0f50300900e00c214940b406000030545e25a210031700b524420b8400720b8941c109000d9540e5940d00844a581d4010300400180140c0d003400e111804583c000d080f00710340e40400c41c0c0d44403203c49c182900202c0059001095280e49a58401c0c0542d01c0f00300740000800407232000000da261202d421102d000c06100d00025031040400c1010100d45412203003246040d2112105507a441019100c40c1c0030030300c205070300000410403540600c00c07a021254010704d0b4000d00702d000c0c103642f4001030005044030b601030707144041c101a0f504e00b0702 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 138712814 1250 138711564 138711581
    0x405060f1204210e01020c090a090503030a0504050c01110c130204030f0302010f05010f0302030a080705030f0417011b080619080d0206090d0c080304110607080f0901090501080c16110301 82
    0xe503026860b80e100480c281112102a0203040104d52504400141d80102d03901a082c4c0c400c1c0c4221605555080f140b0029080c1c14000030107d10000007000403103501c540c80140542d1244e000e40745845118030046485d00a503c0e903c1d00c03070350405146483d1501c1c01a00881c0c0000c1441005800d040d601d40340e50b062039600c0f41068002d07035103c44099101301140d2143c02d005d00198140308040c1d40c00e58002c640e076600f0343d80005020913000500e6009101040050b01d03000212840350070340d2245c4403181c001c4c44210103e0180320303075801c10b102c0342c40e140050300c0a14036500031555200c040355a60810401d1113803500000a0091940d18404103404805209403070b65002c2c113030001c003502d0a00c100b000786059083c80c984010055030b58134100004282c40c048980040c1c10402c111402c00e401c1001803a203104004005001c04000a1301c00d0200b1004030203019940c400b600c850301f07040e603980d0040d0b0f401075044400b4220042c007085041c203010000c002100c0c0c001c0c001c01c1460004200030000c00d08403020030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 138714064 1250 138712814 138712823
    0x1d06010c080d1a040e0703030e060d050c0706200702040c030f06121103030c120a020c030a030305010e060405011503110904020c0105180f0a0b0c07020409080306031603080405060f1204 81
    0x1203c02003403201041040c2e042e5001d09440400401e03614185154036a4140e0200504000c40000d1071700045d5940c4050395184800807400b00b00340d0501030101c03000f56004c0601203a1060801003004280c101c4010001080b50304035004928100566080100500c941c40c90402030569400404060000600c00c50000d0280e0503440c1910180b60300b0030041c0c0386800c528192203903004100002d0103660224802180c50b0034940415195116000180c1c14210505001034252103102c00d00d00c241545600700328100c3d880100c0c0038816858001c20301040c3c4609010390144c5100300407107000c1c0903200e42d005060b0012452540c1d42001c8d4002d000030142e0313001c40341582c90b81e074480701070181c00311121780c0710300303d0307006560007003807919071615100b605c03034010030400791840300b0100c006040c2414620489482d00d600510030410710796107183c00e00f80b6410650b6601d0003403040c1101c800044040d90441c1e03042c0c941049000c1d040915010402859501400701c45103c110140210805d40003160412800396204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 138715314 1250 138714064 138714071
    0x14010e07020106050f1008100320090603011a120f0f0a060509031201050d020a080f011401060203040806040b180f0a0b10030b07080601110d0c0b010501020303011d06010c080d 77
    0x403100c02825124150041ca2203580310011045103581c030b02c0f10051450003a0309026a0540d101400c03112510300e194006403c004038030100c2c0d6100c505035461403400d0354044510103503648410003814202d030382c80c1c1c009680360624403c0141c1149440340150707840b55205421a185455501d007164200902c0840c501210381c054111141017003014028070b548603900034010350a02c0c0c030002d40f03d03221040611803d401303424280c094000f55241c03c010130001c0c7c4040c008503030705c240c00300712403038000c2035200c05420361081000c002181352840841100d0460b030030708008141e691100d44130b100310000050074501ca01d40c02080400c20601041c030032087d5803100b00020784120b0b02036041c03950707648400609003030f5908555103043c0000782e40594405c1e080041c0e86095030301544e41c0380060300c80e6850315800c81410b2282c2d494000d01154042c03951400c031841910502900e0b60b82d0b80041ea601e000c00e01031170404021003e010f41c0d018a2200f2074070745c490310501d00401c0c0e0031503d407036014455108d41d40d20449070740c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 138716564 1250 138715314 138715321
    0x124081906120203060903090913020303040515030906070f0c0201030b040e0a0507080c01020d09090b0a030b09070f0902070b011509091104171204050f0d02040e0606010807030c02060408090414010e 87
    0x313090094a6000056602542c80d1642e8180090741d010001000d4880aa0702800c0000541d14100151406085e0140405034a4441034002090642084a500a4130700c031f0040080d840d03038800c481c02c2500a529071598522400d0030390054020f44018211a50004d40d142c540176200c81c402c12202c10b40c10b0188014100c2c039401c101440f814a060940390605550240040c480c0c21640481e03110b0450300f49050000b820502c4100264a00f5090707480a0302d1090002c092201309000841d40c4021200682c0c643c0085655803401c0704180d003e204070261441001500402040c050118103c110f00d4903407401c40c807079540700c12002003140c0d4a0124014464004941800300c181c46240f4180c0001c000b2004104900308203518a55500c0340e4020207020b0102c071001281c0a4640500c10740704564000c0c402d01008246c030941c19a40c82089403943c1c009491040030803a514001d11940320760382e0055001d4200395641d03031a060b400f6800701c51295009503a406404d0070f40507125811502038072071010342c03035075504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 138717814 1250 138716564 138716569
    0x160204020706091b0f06030c021c030615080c070602070302150c031b28020c03070b03060415180c0e06070c031b0e130204110d05010e01240819061202 66
    0x180d01c14410a04906841810300621170b548401c00c1c22581586000300e54030781c10480807420420074841070202003443c808a030005c141c0581009099840d2414180900412100c0c2124103500c1074031114202e50080240c800802c8554004080f40380c000d00440b0903002d40e0b42c144484000044070314501a080100900c50021448140c8240c5d070b00c0e0f2400310320306114600101c4a4144c6840b20f0380c203c0307107090010f0000640e000f48241110b6070f500a060b11003159941c98a05016030080725214810703490241c179820f0384c201d041c543d1400d840c0c6140c80c1a0254005154400041484070f00034000d202d02d131a207295442d0390310030040a1700ba100b000d52281c060b2039032404800040c2d511720049011080500184070b807034a0135810390340c024107103101d51403600c41500100b0005d04410914000030b120001b02502203540b5500400c1c101c07400003400e88001d81ea540030759503440386458900d020344140161200e05840c030035204035402000003a880c81c40080100d12030000c40b40194042c0c541c5500c004420020b52 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 138719064 1250 138717814 138717833
    0x10b210a140c030402131d1204080706050715020a0c0c1410050c0c15040905090312070e0f010c0c08070611010510260708010507030b030f010e0309010516020402070609 74
    0x10302e210703040d904500349980006c140394141e14050031b541d5558921100444585d044064900c2c801d00b059a114500e4000040d61607070243c041d41007684540c2d40c000400e1446074040f100c1d2180c0008400710606450074030480698845030600d0104000b400949010038480042c01000706040c00542e6210403d6806108080e40721064080500405001003520b03204081400c1d41c0181d8200d038a01c40c03e1880800c3c0d1845805141c010102c92484c0108000c1120400070041c0f90340c02542e1050b0b000740d45d0710a03003101d22802d82000142c01c291014015071321940070300e103042c0300b0b10300c20303a100703a900ba03100d40c1c51919000c0540d1141c0700040300d80e07141020f005001c1c81155040308a135100c92100c2400c05503442441224440c030f0b40e80140e10758440b03c171114404c0c807070a00035050303840003804107042902005010b03102e000240f0340b082c05250202540f0600c14411010f82940c080065402d10010700019034540d00513040c40001c0348510315104005a507039100400c400d43c412000041d40201740d04054135070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138720314 1250 138719064 138719071
    0x10609140f010e0606070c030b0c22080d030218040c1805040605060f03180304030f111206010e06030f0a050601090605060301030f06020a0504091505040509010204050108010b210a14 80
    0x440d1601c0040c40500c3e5200612940410309941c40307541c401040c079000414002c0c83c2e0000d0100c104035428000a05280d03070003846040501c825808881000a0055465101911a0200961001c07440340b05030383c044d8010b048410305580c0d83c4c2e45800c00c2100450203039604140000300007817840c109075081740180d0a0000140c0801d175420800b240c101000b162180c824010016040b580110008000b191082c0e0145103010007141501c0d110f9582e8a80300213130081c03810b0116214048008103214504126a40c0214041100010000c0f03911304038188420b4038020701001e400d4068010000311104040111208091050b8001e008d1585810303c41f40c11140b46804c428402c00f0b00b01700401c04604a16660034845422640060b550748410f08180d030244999070140f03445030b050031040c003020406d2007800000c0b036009032000e010319558610050700300c1c4501d01640b4045100d88005004140080000c0c01c108419080130418540c00c45105146201b002c54125a0168541940d044140c1001c08010b40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138721564 1250 138720314 138720331
    0x6011b03021c031107020d061e09060b010e090a110f0a0e0307050102010c051e13030803090f0708190507080f033103032318030105090705010806120106050301060914 73
    0x4e5414910144484d00c51030a001e4814000c9507406000e10100c0d80c0000c80d8081508625a000501684004090f2411500c2034648038039140c1080c59950003808121110840140907000503901c00c03104100a007480f03d1034800741d02c2c05222010a00c2e8216004152030f10844c1c0f5003152820000040620f04101a04541e04690405854461036500102565148544076801d000c00e400e0605c00951a4050b02d5460b40400400090000902400e80300460003048100140c50700140d03410700082c1c0c0d40c242449140c100354020007107020080240c120741c51002d0f2003003054640c01d5940c0d0381100e00d400c01104502c0c245420020342403100b00d252400d03410107690142c2021444100120b9248040600d6100107030601944d410480c5800081405c10091110100481900c0301c0800314500b14001c0707441002802503180c40c002c107500d00c00009140c021600d0594442030550b990009010501a61640c0d0713010742c0d0748840d008900703554280100300240c005030708009a01003545042194542000c0d14401c3d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138722814 1250 138721564 138721571
    0x2114090a0b0c030a0b03070306090506070e0303040909080c030334080117010212090d0e0306011202040908040812070201090605120619050301111e1c0506011b03021c03 74
    0x103000800000e4250391100e4015031441c0c4941d60b01d08003902800d1207104d1145e25020b031201c04000c208030340d80304c030300e810b030141d4119402540c0b40b01d415168544210030950f4190320900042001d02c0494010704a900d22404041d82418158110207142da0020707540007400b440a2000c141828401e81c24400169000e00e41051082051084c080c052035018080e54800b0751065250b080c40f2082501250b0041a940388034008a151040700c1c20389640c07500c07038444000342c0d040c850389400e4580098104e0581c0c2c01c2c901e45000070802c07542000007c08882c0c8049034504421f000010b07541a0034020303004440b117013440030380e41c5201e02c0c07000505601c0b0fa50004028004103000083c0403188541e2442e0f0b003d0b00503150901210b6a0b001c040b1000950f551016500d5070804543d0b00c040b84000c00681810f964040044218440724180030405009414599001d0700040c0e91501004140746c1141e600003806051014034894180e4000f00044000300003600035a1200d107040f000110702e070889010000c054076040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138724064 1250 138722814 138722833
    0x30e100c0308151306090f02070c0b0307092102010e040903021b03101508070f060c03030f060e130506100602031b03040b0403050a05010f0b060316211409 68
    0x5004401410303000341c100000000002caa200724403003101e05200d001400c10401e040202045405030050b8024554034a0603c0b1201c840e44105009541005074071410002a0394140111a4042d8000525142c1040480540080e1000080c10b206500240007088206d84102c030340005488a1044900a800341d032a0801d0140800d5010485407440701e00300c1c2c0b80c0380d810110341001900d0071100505c45590640343c0354640c05841d016003682002c891000059075082c6a03283c4030300120307051510460010070a00d004400010b031090340b003a141e208c079101c80044c04a03181d89c0121001c4204070b952200100841d841042480070070081e81c3e40c05080903910107040c5003004402500c80c040c03481a90a08040c801c0c00da81c00d40000d005882c050301341803401e25120769490a00c0340d0713950380f4100f0640b195440e040f40708400c4129801003101c10100a460f0a103903440303c810038980c02c484646070504014628080100c0708025078201410601c02d1080407501000320582e41a65400c081d00f07802042d0300881c0178 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138725314 1250 138724064 138724067
    0xc04030b04030309020d020415060905040516050c01021e04090f110f0a0c0209040c0e010602030f070311010b09070306050310050105030c04020318070608040606080307030c060b010e090109020304030e10 89
    0x166000b5407503d03012403c48054404204031010640d40217500c5420110300070140030300300e0041d400700d0ba0b03240d075910101541c0364240000c6403030540c0c850f07a40c1002401000e00c000c0c01003004080d0480320000052500c0031408600b50103200c25280f001c0d1969000400700201c1c1014040d00300e25800c242010454951024114a83e03031140380c0102d00c2c800710110709030f11014010009010701d2500900620645d1505207016801c100e668028032201c0b6880c00000f045982c070000c140d403010440c200403140b0340280c2c0d0b20305407000c540182c1d04e45036039034071210805115250841000d00804950b1404600b040c2814101030810078032034004559a8601001080b0a80d0001000b88004005550040e666240e000c44c500030a414409039490034031504000154042d480355581d03201328025001003195a07103031501161030388248076001d0009101d00340341a01180503640040580201414a00d000701c3d0070741c01082440d24240d1100090546c04000c00c418180c00880c081d898540440c2c0460080079031280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138726564 1250 138725314 138725333
    0x80d05010f17060a0f090b01031101020d0906020601050f1f03090203010c0c0b040605060f060c0c0324060114161505060402030705070b09281202030c070303051e04060f080c0403 78
    0x4106000c5e280d101e10702c8003044c503078402006d140d04003130b44025540e1a824540201c8400d0941107005106018200400a100d1101a000e85e102070340689030356442d00042002c030714140342000e54000c41006500087c503c8101c4a080f1001d01c588001c100e441c4140101400c44650f80b1040003801980101107000411803505250710980c4800c001030369840d080c1c0820040804a69a146c00403000a05004001000580428001803c400701e5070541903201d0307080310380c40d044002003038201c000b0350110b2842e60045451070207000c40c1c0505107042030b070011300c589001d02e441c00c000d0b00c2000000c5440c0c43c84c400c030740c000c11364400d4042d00e080d440c601700060700408a1107040d102800245007180492203003e4180658010103011140100d21000b0b042c115428140503440f080b9025249020300d0b01d032240c00401615a10b6003010061700c0114650b41303003503078250701c03024600480da0b0340142416044051080540050286c0d41d1362903151408201024100102c05030109032010300c00e11081000503005103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138727814 1250 138726564 138726571
    0x9060801151101150e0114030102070206070209041b0618090c020604120c051509190201050a05210108031c0b060702061c0603120f1110090c03080d05010f1706 70
    0x509410500c542c42c0c02c1e1030040c06030542021131000755110000c2c00c440700442d0103050312544260b244e0001180030070035080303100d20302000350400b900b40000d5000d890410952540315010300d180603415012112418448505a00710801040c40d0410460105200c1208a400b50901000801c02c5400c01103002c1d64544000b007000304005041210344c5d030214440e81c201411039034024115030949604001e45044404112418419485050840e8040c00c0140c3d0b940092103406031206440c0401c028800c80d42503004100e0064103c8050a492100700c2d0035401250092440c000555140c11002e41c0300a4403201c45041e601c40c20b0f0410001075456640e0030308803000750742c1c1101d88030758904508082d4150f0008040c03440c05901d1401c0b40000900c0a0601404c1128480b540c4002210080c01800c0e030300000c0c201003403501a888000c1c0e10f64600030992209017424061541e10301e0341d80c3d89985820040e8403d000e16240d46840d40d0040011441e41c04810f0b004e00050304000c80c00564030304144d6603400f0002c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138729064 1250 138727814 138727817
    0x60906130c1d07030e0a03080723030c07060e070b040618050409030210201b070b0c0106060801170a0308060411071110080c0406030903140d0504030906080115 70
    0x90140d000c01108008800007001440c00360319040044940c03050307205808890200c042070805020182400c4040b404041c035075496101c2d10540d03110000304841f0001085012640e00c00703104a5a2480c0f0400000340d0300c10281c288007503603200464685030003550030b403040030200c0380d22900d814004050000e065400391607891902d0b040180b8081e104c103190301c440723030310154100386030036866814035502140c212010840094107100e240da0034190304000c2c00305c0302200810b84405102c0c1035a2031510421000015040008503a400c0f138032941004003d9005042c110f031281c0d900e01c801c109861b000369840e4014903100c02000c400002e2211a107445a111500003020044003d0005200350380c2c030380c44040c4582502c040e058440d1b04900d404485100c5814456205040d9040d41d890382e42d01c10b10150b0b11a01100c3e11840c00d0030325080068000c0e165441c1c04900303108c0d00c1e1100c13040e440054400b40c122440c88000111341420181400703030030310071035030420000c0040b4500184035103010300c201c1c14901c8056 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138730314 1250 138729064 138729091
    0x5040b07063207080421020a060615050405010c05030904110318010b09060d02220c030509070602031c02120f01170c03300304080912010b1c0204090b0108030307030b03060906 77
    0x980c03600003c2c0c0c280c3c40c48001b040400c488504410300ba0300183d120700880c421801040b00c5901c070700e00805c058400c0540702002400420061049521132103013080400e120b81e01312030030840340e0b00000c2c003500c8500c4403402c0103a4001c420041000498145280d918403604000c01c400f41c036010105001010051151b80070750048040360085482c1c0e50405601d01e00450700c15111075200220305000340c443c111070500001d0070b107000726100c02c50101d4020b0440e13040303800440c07800b2850066034599440c0851200e0f2030660070b00031102481c1442801c80d01c42c41d44941e0040c040c0d13041c184190901e0505800210465101580e502a90707200092030001000c40c03030f40002c191700250324040c440da070702d01400c01480000100030b0000f0000e03200043c001c002800c840c88001d00c1b0741500520b00320303241d4510056200500c95040c41902400841020145002420100e00b0100c591980c0d40d001500b80c2c084841a40004104225a589031040c070518040480c09000142015120642c2c0d41c24098120f6a82804 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138731564 1250 138730314 138730321
    0x50f130e0405071a1e0c07090c0e03061303111501090606110604030c0b060607021c0309150903060b0a090c08060405060103020903070b0f120f070f0c05030a030c05040b0706320708 79
    0xa0100507203100058075402c0f5401123468481c200301070301186404a01080e22495000b22a24001c00c0d41440b442140303080900c4112a0307102200d640c182c0b80604e0810340580a56001c2d040c0660380918040d101154010801c2c61a09030024840c224607000c3e04443d0f0011014000000e03800300200c810310350002618205916071600040c04d41c4109000258030800541140540e540c01c84610090740d400f9071140500313541c2d00c40c48410a41310480355800020428041800002d503194864000464050b141d04079894494609038212288012500301007281d55003002000c0c0b80c00e00580ea404107084c601035040038030b164042070380d802860091141c03003d0086800003000040d58165562285c030420101c0031804d04049041c4070b01e8098420b44000b441d400d154005042c001c0c0c1140c5007283c3e1100046241c41011441140117160555081c81000010040018841d05440141c07084600401000400301e000318110380c415206011b08080c000840c2403800c0d0b402c0300e0b0524003079000f40740381003607007080e0b4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138732814 1250 138731564 138731617
    0x9010e01140d0501020f1602040b0109060c080a021c02100e030a0c020108130f0b0108010501080a1208060d0203100204080106050f181527130210050f130e0405071a 72
    0x180c56496004000c0109a20401c1c00c41544c928421f5030003603400300040703c5034030011140c5441c03500400f0003046900b19040d0000d00080020814011780c1e205480c00c079452240400c4558505281d41001a0301010384540640044e108401000c100f2400841c07400400c0381c0c0140040c0c01241019040c041001c0c0050840441300307040d00140341d409004090054106c1c0f50440c06180203001d0356095620382000482d0541c400588454520380040c16100c9129582070101c0302054000d040541100b040940e03e00103071400c0000710750301c8062260250b112400c01c03114078210740c429841184142d41d4040e008107551907a06070b43c040b00340c070004800c46580d074076581140e40d669044405508000103083d0411070340e10316403850801c3d034100d00c0300d10b01e680c80c0c0602683c0c4024030303000c0180d4000480c40300d449200b40184000c03c042d0901144050405004410080c2c12480c294008080074105c41c0400c400c0040904c1084c018019101e006009202c0c49201091103000301c0703c9898660040840010700030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138734064 1250 138732814 138732817
    0x3110d020309031207020a03050306091302360412030506010c0c09050f0a05090607081b030109090203151902160b10030c080c1c1a070e09010e01140d050102 69
    0x1299615095580e0304203603000c165242c1c05900f1000c2c0440c58080400e85240c03001c038100545036010303a50345043d5100d070010850019006454441d110100742d9001005854458542001022920003100c0c10383c8081140d40c2d4a40c3c03110007500d1091b414608010000b050b46050241080581c43c0000750b40e41c5620050f200d017150b0380f0b0081c00d59074080a000440c0d4401340c012a10a00203403102000507160a42084e0642e9401d40700322155400c050000303a1164840c030162030340302881c04020b1072040c5c03000b0120905070340203070000d0114035284c0c02081d0079403d00304035481c1c186401581141941c501082d140d80b50b45e40d00c2c0e0304210a59000134010800c801028420a01990440018000b90401c012041d5610740e043c403007254140003003c800218500d02050421462a000e84010421582041d50040300c3d00e181d00116010390664500c44070101841c05214480e42c40c070f03128484101c40702c80400c070004905900c0841000c01120060100c003182c11840905000180e801c81c500c17102c2494810301a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138735314 1250 138734064 138734077
    0xa120504030201140f01080d030608031204080405060c0604020a0b13030f080f04140a08031908100b0403050f10090f080c07090524060403020a0b2217101b0311 70
    0x4070100720741170024a02d0440c0d0f5440c100c1d58800308503403c496241100f40c003942d507a442000042e0700140645100ea60300d00c09419030003489814242d10385910ba20029103540c00500340c4107101e500090410046081080801e0040d02c40c1180e020300307200c10b500c0500c25030340e000d010003085466940c44031410059224180d8441d0000904a40d880e281c480d50301c1e080e0a40e200b04450712650602a0004804001004a664080380b040700040b80c60b001380750644440320080e041180f8200000360006409070410080c00c003951140300504a448984403030140b51070030180c0c0441a00346030040d00000070303072000503c0c44401c4d071040e041c540b00c101b114619030920040e076000000700e50600c0100b2015918800500f42c030a80c414101a000500385e0081c00103a0089020003034000c42c1d4220280200d00d0003401070000414060350000402a4242000301001c001340d2201d20248205c40c52002d08250a20800c0c0300740b0b6840d0820080b01500d1b601c4039138180c0c0e24800c4034083c143d840366820101c0980c8011100b9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138736564 1250 138735314 138735341
    0x4051009031208090c0d021516050321010b0405060a03090515070305010f0f140108061512070e06120402060a0207080a11090708070c1106091009090b060a120504030201 74
    0x3040c050384007518926003211440d811780500301c01401c8a240c10001482c4440d009401902440c00002c103d2030154019407400580640300c0504400042e4104003c01c01c040350441c04411500b69845251002c030070681091000510038001845242ca4400540e080301495182c04200380b096030500c5070500040d01c800340071503051402040b02c0301e50140c008504031792840c4000e5100c40c2d03550700c5a4809425502941102103841071640d042136119002d40750b00140001e09020004401320b41c000d1301c41d4011000030418650f00400c000c0056000014404c031110281c4d1741618003025003618410401c0020002482808081070004c4181c0c800c0100c080901403040490308907100c5400c0c0118103c9851080500c14a00382d03000030b41c22440b030201c1c180030b03080b15210f01310742c00c41545d40e29480758483d51403107030045000e102102d42c1d903444100b01e6901220940f502e035915400c0c48185010b440b40c45084d68001c2c2c204200b00c502080c3d00000c0058510050600000c0984441c5005c17070152014a10029 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138737814 1250 138736564 138736583
    0x2031809041a132001020703110627011b03080f041103030d050f0604141801020d0516090611030a080a1401030b15040501120f0312110c010609110405100903 69
    0x5101043d4811494129000b989902d031001c1c00d000c2201102d46a000c0e039180144c011a400b0130001e02004038680c02014000c3c0704e01d050940c4800303c5101c0380c1d15032800401d480c0c5002c0701a102543c0000350280b801c200c011240c24aa1b10a49028290700c82c050316aa0340c0080d0030000805000000d12643c0c60b100c001001d90343e035103800580c240d01818089d0b500c98680e074410302c00f007401e624151040302084200310090f500c0c81c2e40c41e07885004100542a2581040b9502009250130846013407042900c22643d400051000c0284510000c0010034a43c00007001c0c000c804003400801d1100109a0f548010940760258583c0d4502c01e0400c040c04081c0c41c072020343c841c2c02d40040108445000c0c0b1500c220441c220862200308010200b2058510a00ca140d2040d100c846011005c900401601c101b01030113410156242d03850060708001300c40300141d032030008410101d6681e0540e0400e0007000c004014240080c85080400c01c480a80d51140b446940d01c0b80500450051069000b80d14820040d0b400c8003154 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138739064 1250 138737814 138737821
    0x30f0d0207081912120e010f0501030b06041509020703182d0f03030c141b030f01020f0a1107091a040e150703020307020a0507090603030e0102031809041a 68
    0x180d9600090b001d09a06402400904406081804a091145504001d07004805a03044006841c6201d0510040305407540f0382c01c5488030f0000034001d000142c8840740c0d0002d455850760505074500b40c07000c0c1c00c16201e141401d4081035440c0215031000243c17a5030410050b0781f40d00901d026240325003c2107110003803e000c14000591f4503c1c402203101450015615050652403280b1381c610382151324000c6c01c05032207000d01c0034403b0030701c2650180b80c864841e02021800500f01a126803420361003c105200c8000110550f58107424144041801184001c00a60070a200a903034584103001d41d03101034081000c61044903d1900d0200480390040c14402c00070411410b800e841003416800a0100f6030041d4144810340e4008400003903601c007107090302041c0c17024549034000118060742c0003514a00c21840b4071114500032410611000004140900000407440d1961801410f041000100503042d90001d00001035280300ba00461003d400c0102c40221a1790765034a400c4801a002342680100311140c80c041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138740314 1250 138739064 138739067
    0x50717010312021e070603020d09020301020304051f0605011707090b13030314030103050a02242a0706090e040303020d0218030c0f0d0605040807081c1a0109060509030f0d 75
    0x12a2441e2855070f080d1303081000300c0c140a139903000c658204126141c0c04400200802446680a49440940e025003c64a51411380000b400e982060724107440350780000142d20180c41c000040e544101e2a01d003030038048070340340100203000d102c80311070309008569002000400c8e40b44905126005090100060b0351030311480101c00c4007800c80742c0401c402240b00392601101d01c50400b0107036412a46d00c0b20040203604565070902c07141c0e00c501c0c00030b600b502421030100228452030b031002e041162100024054800d1405036085070130661000c0001e541e0304015418800f059110859109a505c0501040800c1d100d0780340c11802442480e0085048600c089000c01030800c0c0c088821759021022000c50780b506130003204000c00c41580c00c90303070f591140c5000705050010b0083e0b002954050b000d4421f80e800c088141c0c484409603404644100000541e034003544564000e280704820804400024030840c2041d0301d000601390310458044c413814850b010035143c1050307070100003031440488040242d800401e0785040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138741564 1250 138740314 138740333
    0x3080103030806060708040501111216030318050c1504030b070905130b130b030c100503010503061602030a08060d05100f060e0c092416030f020a0b04060507170103 72
    0x401ca0008110740d01040051500c5419191026000b2040324074003850000150390844104480d0300050060b20700c80d000d03400f80701001e00110039000850480100d014a8010203e4007000011841074040281c1d840c0400c81c00583c207000340d44e060794280351100201c034540c03000e4042c03076100902e145040e400704070034a41d000350008100c510940d030500c04500b03060011001d072440116610b8100032450340410200d0565000a513940070060240c0e1800081c03074000c5904d019030040841c010420000041149040411030700d42d02020124840e111514044002504c0f0301c81d41c12458104041d1a02040c01d035596a07030b10143c1c0a23070280c00c07603c00707602c520080d0000e00441c0e0a85c001c0c0c10b00d0b00c000001c52040112805104482c0c0292592a044100d0208240f9427150406054030389141c400034401c2e41d00039001020307414510714030100e1304c5d161441c0003020854100b41b000115081000d9000002b91a03002240d007107544488081225903070b00c04200c549400d41c1d0740a44150415200010a2201e80c0c00e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138742814 1250 138741564 138741569
    0x90c0203071101020105060306160504030b0108010905150f060415090513030912050c06071e140c01050a41130b0403020901031403040b0705030901030507031505010305060616030801 80
    0x10800e020080c00300c2c016403c0b13400072229a42c154103c10000765815400c4044408404060700b40300e4205912500e481440071000d03000003105a66426204c000d0040400c200018500481c08000c898588400f00180c0000301405143c091034850131161809480b05c0f010b440a4900c0b00070070031861030694901c00380d10b00c83c007505401003000703040045448412041c18001c55030300840100110140e1005001c2d0903441f51200b03039500d4891520081d64802c4a0880d895a02d00481a0018038407070304c10b0076428100c01002150511108105104140d40c00084141542c500b40d42081c641000e054003400112008803545086500320302171008090109502400d0702c01803080311480882c5d01c40d56008201d1240c0e00002e5400485c00004000040380b00044140c10035a41054909141e0f840c0380705542604200001c44807034201044160142d40e26104945d0f2006552600b8811480c0e0f010040e400d61545000d102d0405031210002030458031040704895074084492000384000000e03080c01003d42c102030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138744064 1250 138742814 138742823
    0xb09070e0109051005070b0421020d0f030213050d06090605010f0f0801050403050708031503070e0a0c0c030e040b0303091c050d0f020d0f0c050a051f0212150a090c020307 75
    0x10008a101c2c04c01c801d6114403881ca50312014588001c0f6111851035003001441200c140c0394007924040e620440c030340c5000b00b0070300c150020004d0406da40d501400082d0f40c1c6070810704262051240c4098441d958410b030044134401d440b1035244c04c9450401034041d00c00c0320005401942400000a43c0d02035400702d28088030998040d6801d52902c40c140142a550107403406000128103000080c082040c1500654100c240860b24040282d00100480d080084507403280d19920152020001981ca05000d406c0d007600d4103140032224120556005044c1038817000c0e02c1806180d4075510610340d03484c20030856800000c01002409000032641035140b103130f203050008440c40d000e10011550b000b405a10724500c06241130f0090319020100c40c108841404000220f03108100300c0607481c0c4040f84041c4090045940180b01806400c6043c070103020f88010711041080c0010320420130450800c8403950100e802010141110781181c59449c001001160560004440035181a1601034955000070081005c140306 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138745314 1250 138744064 138744077
    0xf05160b040504060b03040b0402010347010c05120309010b0406030c0807051509061c020d0614030c01050f0a0905060d140612030912010e25120305041502010b09070e01 74
    0x350f1176051701600081e20020102800d030004200198002c4e000444180e1301c3d480000550103080c5065a0400302c071084e9803581584040a8003840d6080305e24450000c40c003070901e507a030300d003243c0d84190303882e001c4084410b02c0e10404000310b0103480c02034100001c0840024024007c098072030030075180d6200c032071041c88910b118845002a039820400754000c450300403011118208800c0e07201344806075110050303000020445009d90106085c0300c4c070140c10483d100b0b1400040c11803c040c0316803080c0103d818624403990002c0d449610036a401400ca4450541d14400036407100e0301c0c140d090b110070701290030071a030110b008a01d030120411150b00c11810084824000364507a103441d001d011407102c151840071200d400801c06c618042c20462848800145803a000080c84000461031301d003400500c50305031103d070034144500f000003030f881b039081c1001d803003501800c0324024510741d00500148124480c0c0e2081261241629a80398001c1d403018040c1d480180281c031141c0303081c40c030041852416104540c0469007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138746564 1250 138745314 138745319
    0x10e0106080d0509010302070204020f07060515150706090c0612060b03070504060e01090b16151b080408040f1404050709080d030911030a0c05010813030c0f05160b04050406 76
    0x10140608800c0303520a001411100c40c0900048615a004640803418503030200401001a103076480100454004400c2242d103c07030852810101f5550003425052903680d58405c02310340355030390000c01c2c2c01c0126943c611541c0c641045c40c03e40b000d8802410b002e08407032814007000480035041900428400c1c1070800400ca00303034460115039800d0100340d03488400175000380024402c4900a403c1c09203080014105240d82540e10588001154082d090707880c005510140e2a000300905070310324088403550800c00340100764050016402c52654050450100880440400d0500c000c0d002143c0240400c044003c84194980424541004448100c01d000d01d113084000713501e1a1040c00d010041c1c1d075400c405041c0141000c502100900306214054450f141c94054094541c1d03010000f500949108200410000e844e04001508107000142001c5045003600d1075100001e5000038080ea0940d4020717188a01451981043c52411000a4a00320b07880001800810481444400303003080312401c6905005c2c494 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138747814 1250 138746564 138746591
    0x10906110303060108071b150c020303040f02040216080a05030618040213050a02160f0215031902071505040506060a0902270102010b0a12060f0e0307030f050c0d09050301 75
    0x54504046a450700244081152580b1030314600e82c01c65550b1420500d80c081c0c9001c52021800d00f0b01c8202c0c4c083c013005a0703400e081952800b800d60b0460079400a141946400e0b21001050f11900c54002d2140f0341c001003242800c06c0b020003c0c000907400600d002c2e101c051100010305a90300c00e2300c140e84a6800b0440705101c0d143d103002d0315840b4030350203421f44110301c6809014201a10025061601e01602400b440c500445060740702d1403880d00880c2010300e40390160040c4003003401800110b41c4100c50400800a0380554041540d0f00801e201c200140c2d99178413801c01c20000c64460b0b0010741041d04203c18002030040004d4500d000340b10032106030201c1a03655989034100e201c0c00300002c01081d28000d02400c4500d0203466581d4504040c000441c1c1e15888500244800045401c50304003620b14017400300502895120341c014006503c0810041a481a09619524010300000400f0402440078201d4602d02c150159100781d00280102c4250020000300500940d0950040500039031a0051595450 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138749064 1250 138747814 138747827
    0xa150e060a090305070b0702071d16030203090a0308040507030c08061506090f04111605060a0b03010b010c110a09060602010603050f0d08040807050a0b0705030610090501020606060903070306020c0c010906 90
    0x103070703040e11130500e0030b0650b035100503020304002c4c90a0298091040d000600c034a500c800d421000d6080e848540a40c0303007100b8070702081d0006242c001d0401d88103204102d640507000501d620340c203400d418004159511480c1c030528002e41c036000140410009900010700d620002041c60042c0e0325448600c2030b4041c19030912580c0c1c0204c0e0b82069000488541580c49420550700c61100014068021403521034250600b02d81c44150309021076180d80721070704211013642c00b44034440680c0b4040707000f40401508440000d210240d11400078021103817521070b03558299504240600100035917034083c003000766140c01c0680208070a2200b41c0c0c0074001c10100c0c545000b404245004c1a8203036484403000c07611103450340310305600002c104540340d1050709600d4020071138403826184540041d640e01c1c0c1e9a0720f00a010b105020122041c40020300510300d4041c0070503a00440d100798413280c10788103141c031030188200180c9001074541c0054002c40c0b001860700d03800c0b4008540034406001c00c0e22000c01865403030301c00301d421 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138750314 1250 138749064 138749081
    0x24030902090a09030509120c10051903020d0f0603050d021006050a03230604060603030e12060f0901090206030c09180103030e0108101d0105031b03060a0207050a150e060a 75
    0x100c55690700066480c00641d0042c90400e0007881d0140c2010325a074007041b803004a08203411b030b6640c4010000d10b00d501e000701080c05d240b00340d454420700308002992680302c0081d952101d4002c0c15004548200c400b42d0703590240802d481c403040284080c541d68100700742c46101c0c00c9040c60042c01140003a405441003030142c03804461000d081c0e03003a01c0380703141c6807400c01944e00144c2c002c4000842d60f005aa04501b00700f40e82c0558007948000411038514900a0700d41c500c0444040e000d1403508415002520000c11b804e5802080b00c440b03892030399141c08000340148107005000394400e50200c280000c07202402c02900d000b1200340c409004440ca21000c040c0700075070902c801000200d0420074000340b544690019900105680811800a9206c50303644c0855410918041221382507800104000d01e01080104442d803106c0250241248040000c41d4031088001c00c065600e0390001281410480f04001410300507402408202c103440000300044040d015240404c512880b404010811250440c80313074440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138751564 1250 138750314 138750319
    0x10305060a0204120b09010204170d0207060c0b041101110d0327021302090604050402040e04060f02031506070c0f0b070302151e1005090a0f1d030304171324030902 72
    0x40c06006640c4c4c081014000034075044065402748400204400106030340c01c08400e00902900d110040a00300a15102055221404102603e00c88001045c10b060300c40d034006400020f20824017841c4001650f540c1103030845200d40e40300780a062810194954030142c0940800c1840b16003c1c410040c03000114181482e000c1e601001c1c9000b40c800c08403082d402405112805802c0c00c0c01c3c56641c4000400700d8101d580711105200d600130420041010501c00d5080f404100e840440c1076060400401c0b1401500450702e030f001d8103001507d0307414410209030010041c0700145072401840c5d103881194086801a00e001c8000d480388004860b090f88035221502d1080d82c10f420290800c0d0b6100e0941040c070f1901034003c050802c061f4102043c00d803507603100c0501c02d114a050105002040880000441d820348a13040142100310000c816a594044101c80d001504550005903441d0809591180780c0302d80760003441c2240b01310074001000120310640111001891903007500310ba0300680c054040c1c9491290003507 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138752814 1250 138751564 138751589
    0x40302090906091e0109050a150525031802061324050d05040f02041103071803080301060e060d05070e04110a020d121e0603050706261b12010305060a0204 68
    0xc3c0e582c4403d00f009900300044e500200710403005403501410240c407581c0c03c0d51603004926031014004168091650401c004010407092908120710010414800b82d15903000c05490341903254400b040710341200c828940003800756684a583d1084100101401d12a1400810280405c9a0740d40002e1042418500240c2c580360315112000350041c1c002d25006108441e08500c4c80b4041015803580d1244050940501040640c0c074100b0360350190010001c05011800304014010a10000f10054140c1341169254284003004540c143c0019140740101d88020360400d14000400c030549510040b40161040c040d40d04001c00050f10300138864510030003c413180964882d40e02200014419a07181136005900c00e030000302c05500d01c0c103e000aa0440c03260804007610341e003080c41403142c1400f484004200740d003400403040941392003048030113800b240611104d942c03690008410381c5d405009030107203200c0090b540790b444000c210000c0c540c1e0420700095400d48281c00004080008501c00c071001c1c2c496804091 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138754064 1250 138752814 138752833
    0x60303030c07060b060714011e0b011d1c06091208011215150b070614010e0a050a020909091f110409050408251101090521120a0504030209090609 64
    0x94042c1c04c14801e140c1e000101004042c001c5000b40300701c1c0c00b070b001c07d075800450500380480f2059025040c203a01400d86c50b15100b100f0301e490ba0485100820040520400c04944001500203004c030f1b070b050150f400d00c842e0000d00303010800105500c01404d0f1882000044c000b4000e0410440f42020309014008048418100361004a48105407243c14081002404680784042c5a00c071003034030601382d00410b21090007145040811181d406801c4104081503420f0203550f1411b80001d4442a010b000b0141145d99540420b0281e00f60380c040718540200034041c00701c40d08000c0c034010780c1c0d44040112421200c00146601e007258455000706244c5281402c111408d003410b01e100b000082401034003c5034424010454a400054001c0c1090021102c541409445490078149040f000c03103006881810007a00150612151303031241480e03840c20301c034440f85180c40c919400c0e200e4030307084c0c00181e00d54400d00081440300301c4985c00030051055a100703440046103274942c02d0625030b0360700c000c2d40e00c608280c114400a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138755314 1250 138754064 138754073
    0x6091409180a020319050c0904230a06090c0501110708120d060510020a03080708072a0204140a0c110607260108060106030506030d021002030702030d23060303030c07 73
    0x20324842641d00340a54101002d10741c002031074840d000d075507000143c4110f62144180303c8140039000b140b030b0b016603900b20a45810747c1e6003082c14900f84400c0611014808030000d04030400c02600f0072490340100c08008038030807402c0070f07032079400e640c49080c2c005500310005140501c2c004c510202228a036000404100124018035040d80d000800848442035952100103803076640c01003e04007060302500038010142c198100180340349402801312b014809683c041c0540142e02000f04128180d41c034411048820780c1080c100490445010041e41c01070030a00146108007101c2d2486001c1d8815140c1080342e10041c070380c01d0343c5900e40e0929100d86074000c05d002614960041200d640c04485001c904001d10032240d80000203540e0a800c0408a41e10003801030213196054811550003500403001451041d03030300400207641d40c0c0142d140b40030180d004804a0401402003042c1e036510004482c00344000601c1401200e2407241c61424a06042c91000105c1c01c0da0401200302c9020769078a4900601d40300c166200e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138756564 1250 138755314 138755341
    0x1e03080901050903070f0e060105030103031b020d080307030c1d060d090204061203120f05090604200312070209100f0306020705100c080906060f06041a0706020a050406091409 77
    0x500074107100082144411680e014007444026041c0e0070340c8065903e06200300d114502d00000c2100303050000400041c40031135040f00000141c1201e03107272403100200c19840400c11080308220010300d00200130050091198140d00824203180c919910341700d101084440c001a05000f80c1304c4540c02c644200a08507040101e50003003800c0074005040464065541c00e00090041b40d005015400141000e0b023100e0b400e07410f4003c25002e407100d002d0500035030400c822150748032080540001c09101041c020340b000c1d504010108103012000400703880c0c4d041740d25a4890300c0da50045208910031801d100010300f90ba41180100c5080e40d0448022881c60340c2185e448100030741c0200c1c0240c0c1c2c18411054142e440c06294044ca551409541d03a9021990034032075070152400a002d0b000c02e00c10200300000c0070403500c41c1d0054900b100c050f200030281206041041e0314051003a03a5000d01214000116000c445400000610841e0001e50314000565910080c0300b011a40007010141e1280369200800d000030310129 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138757814 1250 138756564 138756577
    0xa050d0509070b041d0108030703080105041a1903140312130809060307170f0f06040902040608070803070302060a050105100806210610080f030304030c03020f0d08060a1e0308 77
    0x1c040300c20554591140800c3c41d00a58400c10900240700300c24030005110310011401070189130011420000c999030013034443c5405008940c09260b80310300c2c0080226004100d40d03000600a488c451440e65a90001c9106220600058075594621314058400703210000c112803000c03102c2c0095803080d465400000c0c03034007543d0f100c068622140074480c0d0701e0b16540e240000d42c09160030340c13100340002415100c012903000b8002d107003204440c0c1c00c00c200600c01180088050307202004650000310706005200050003026070f5009124603101e410808034040c507002000300310544c00394003280d07020b0b580c081201c001e0300c05c04d006041e00030048000361142e45000740ba506810401c0200215141c1440221010b44d08000452002c1541d20074024400d02c0341c8000500b05c083c00b46030340581060507590000c1542c80c44050000ad00f08409800300c0310a05200303125095074040103a00740c850b41c1030300c000700400320182603907460310a001002d400224050681b00480d2205488841c41c1100352850322806550b4001c41c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138759064 1250 138757814 138757831
    0x70e040c09030b0106050c07030803090105060f03060403020706050c12210f1605030a181119050108040209070c02270c0a120b1207030506160305190c0203070204020406020a0210050a050d05 83
    0x80c02703c0025100009075100d50502d000001c2d2600e003460422104d101301440842c000c0d0001014040400da010238108261491820290396075200a0222403a05030070040c5070014400203d425440004a0040803201008440f4212015140d07100e100384417031019902c200c010641d038601c80c00070780d0203840a1644545030010008040a0781406103003500503151040300c4c03800941f10803040c10f103000400d030980c090706000250314580c200380000e84990405400684241d04c40700c0000d0034544916241043c603580541445042c010000e0785220590000c8406602511441c0000300900d107002c5c02c0d01e502c66215603400d01002c1103100d600c4001c15095014540100020b1642c0318400d1080000000841c400c8004003a07038070f0104481010038481ca82e0800805040c08180702c60103019140500d010041198000b82018400c2c0080c0c0c60344c8100b05000303410030700102d000240d4a07008620040c0352802580d811008041d00001106c492007100d46100100f94240710151064520f90300080d41701680 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138760314 1250 138759064 138759073
    0x4030e0a09050c0c0106081b0411041d0115020d12050402040902060a020a030201150b0406080a180f06140f0a0c2001020319060e0c03130605070e040c09030b0106050c 73
    0x103400303110040e54400c40700c07102444800138401026442c24030541004082004c0604991700c1d000050f150714402050406102d1a2a21900c4681458001c1154001c04a000d545000740c0d000d44d0348410001824410741c400008049a01007281e8004100c100c58440c40b80d0711400f80a044c00f82e840700030a00904160381041d50356150100503101c405c002d00404403a07400904440c00b1305d16000742912003c00c11041170b80c486010030400d6007001019101a1281410803009550754080298024040c1c04d0b901c0400b1401b001c56181070240c0001055005401600d05006d01d4a200017161000320080e215040c00b1b40303082c030024904410582c00708002025900e01400d00c0094090a04c0340030006c1d0383c6007182c50350b00100740500502c201d00d0038590b104041c0c0b1300340099450704800228010000308000c3e4030040005c005920400c80100b9205810343c008800c0056050400004114403042c01402c2e000707600e0070300000b0560340161f10070380c00c40c0e40c810381c0c000c031036800c00d8422512074000e0902c082e0b0b90b215 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138761564 1250 138760314 138760319
    0x3020c0d080d0c020619060e0402121204090911061303080d0b04150e2d0a0b120a03090f030f080c01020f0a1d100215071107060306050f090c0304030e0a 67
    0xc3c022060001c0c201d6000782460b05010540c031107900c10399115680440d00c3c0c8103040011208000c9000c0d4003680407650208460031200c1140c1c1890361154100c0780b5000001004291001281d02407440d4038021911144100d8088040c440d10b881026010007002c0d255420400c00614501c004201d480888840821a41300400102e0140c501c4202c0401e505c0212003424801e0054540150340d1003440c0c6d0540c074024076005110032440c80d0401791000c40d2994040700144000c1031070381081e14442e00160031103030b0000b41001015243c9032410012400100fa01c503002903405026960141903035007000b0740d800c5840f2180e95041169001144a0543d5502800a800854a00c4029002c00c0406440320b41144107203950381004000c2d10346410344620154080425056070001c0c000080f5455901400c4440e143c5c000c0654442c401141c0e0b0899038482c11034040340440d4141c01001c2101c0c802c1e0f41348c80350303046444200142220300701da0250084105100040100e0300c00e15200c06c801001400410a198 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138762814 1250 138761564 138761587
    0x40b150a170a2306010309080309010c0207080105060102030a0c02040f050c0c0607030c170601020a0204050118060902070816061401030f0209060a05011409040f06090e071203020c0d08 81
    0x100300d8002280030440145514104a800555203980081d500c2400c0004810000e0300c2d84424149040360388003141c50400041c0c00740d00941c0603070b0307015070010b504946030315103201100c1c041c020351020b890050081281c00500c034141405501d004c1c1805070040c5041c548815012614681c410750140d90242e22003400050303002452155a001d0140103869955444607c90090714145014010340c0405280c440d096410303540c800c2c51409445010308040926880c0d4a00403842d01d00080360280d40175107007030000075400003800703195540d5440744602488000d03a0741c1e518000703d00606201511284041100500b000300c21021101014172a51002841d44000400d04000d880c0903041110b0131840d4107078200952504481d141d40c4400c0880f0301d506410704180008007581051000c00080e0b00f0042841580c0759688c0c0c000700a01c111140c410445141e50710a0b0502030000c00203000068014031101007980201100900c1c11182c15800829045152100380405200a01c03025180e0381410b00c500017141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138764064 1250 138762814 138762817
    0x30619110703090611150a0b01020c031e0c0603010b0f030709080a0803060a120c03112e0905030a030e10050405180601081807260d090602060c03060d02040b15 70
    0x500a54803c9001401c100d8080c1c10390340711900484180d40000202031441c030030f46021a9000311400c0c000b040038200040103074548a010303044182d1500130600110600303000c0e0b2003c0b5081b08141400c035100d82545609101051000707028420507240d040203002e030308401e1b500c011030b0461078a2a11590103030f03450741031504211040400302c078981000801d02c540c600e0402d46aa024140c4e4190740e015240d080d07030b28002c1407415803100601e0500100c0d0a14010703955181503003d9440712085074041030b0710040e106030b60700281c60075590128801d18404560f0307080004409000f0380d030544840034912255010003214541d1840760600b080020440400c0d507031200d00c000c038818002e66440001c20f060180016003100f8009000302c0f00c08600c2188620400f0001a84000311217154071224404800c0c51071010703c00e19440441482849104443d26545504c400c46c1402c40341107a082d81d8054440803e804500e00c0f058036840d600c1001c1c29501000740c80e199100040114005000c0c503000d00440c1d03e1409203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138765314 1250 138764064 138764077
    0x315120304140a080c0d050c0a0e0a05070c02030a061a0d050102030a0f0c0219020a03020603010b04030b10030f0308070c0519050f01060503060718090501030f03020d0e03061911 78
    0x1180c1000c5020803120007407805820004408844244095003840001940c6021100b049445080d000180c0710500c03405100c071080c000d0018110303105081d203440d0044600b0f2001d07100074403600d2501300001d46083c4201405e03100036a005015241000d995202c8501420b10103130209101a0b25040c07068072036840006010b0480c2c458000542c0300c1ca01043e00c9000c03511031120b0507250314140055181180d0b8041800140c1041c042441c03100b60340a40040740941c1d00e142c2001350841030020000c44d80450400241c422284215075408542d81c2d11a2010b10b5001c0301d100040509120109100001e0301078074001d94041c2151070464814103443d100c0c40e00d48075024681d2900c040151644409101080c080c0d80d0103003041c44024843c4a142c04082680e582005140310204622a04580c542610027500709000f0b0589450a002958403820012400904004201c025200e4000b41e000c999000e84103120304500002d01400140d41c0c1c0c030400d144018901041404659559488411034900810217000d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138766564 1250 138765314 138765349
    0x120c09030210080103020105041e030812060306070e030705060f0c0d08070f090e06010e0d0501090501051905072304050a030c09051f03020d03140d20040503030f0315 73
    0x9245256005008925002a00c000c003000003100051001d81d070800d040b1030844020200040c000b82e0315801440415505400c02440f1640000700d460700700110b800c00034012001101074a0654942003002c0e5112151f00e00d010f03070036422a0788c0c20011072400034007030070422012440d01d514003400402202e0806903800010000f20701e600d01404102036209142e0035864519080200d01181051031011140c100201030f0350400c089407000d00001d49440d00510b0302584e0007002442000c4c2246001030103071500f00e07415603a1a0045c681c01041031014000c01e8003c0d03800b0348500c0050402da0f036009108030201c400180448200700310009994480e0041c510003540910800d800c510f040c4100c83e402e86402520b10303420004a42c540706142c20a0001e000100c039411984031086108074501943c0c1400310802c2000c0503100800e1324003544240d41c2008071411000d0000c18004000c9001e2280c45029034000c9607015802030140299000c1c1c0c40c07004540240f160b40d0402da03d03400c9000054202c4002d40d0441d003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138767814 1250 138766564 138766577
    0x9040605041506090506270307170c040b01050702010c021504150905040c0c1a040203010609020409090201200703140c0405130506130312020a12060902090913031707120c 75
    0x41540103544c00d000e4031040701d44e549170600340c14410b440c6c01488041c00902400070114502c65030b4040118100810080c2c50600c1c464084108440d01c820389030300c00c18061818041320642942c4a60210340c1000d6050310398400007446078081c0200c06882c800101d450280401000c60840c1c06090803600748a80365a502e40420309281c144000d0b2002084640c0078482c41c8503100700010f0250901451940e0f50500c51002036540d400000d0262800782e2048a169100103000301d8074443c141c000d160aa03000b81c0302e1891800d8079410300c5c2c007000000d042944013070f0000b500a20004410b0b02c9080290607500f4201d51a20001030005011998240d0700c0aa0a00300c20040100304081808402d621044840074505968180d8a002c0c000f00c10b841c245880b00780c1d00149004566001d09864414407084030410410705485a02000c000e6002c50191485a1020000208041503550454210035803558800c0e020703140c0c17240c102c0060f94001e00a6014400f41c041d00e81c0c001340041c882e21014500541e00c86 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138769064 1250 138767814 138767819
    0xb0c1e03090f0a03080304021e040524090121080c0105070203070b010e160806010302070b010f0611030906090103021b100207060b0d240b0d08041703040812090406050415 75
    0x12841006140205002d00341e003c1040000c039440d803040c0c1e68480d805464402c04203404d5440011481060300909500038a000140083e44040b08003850800d1140d04025803040348102c10460400c4003442181000c254141da01181d66103020794091780d8600c03410b10581817000020400d0700351350080700c004006901c0416584284040141c0e504d005141c00302c900e50250030705002900650320350b10344a8080c445000086411a4800d44c1203400883d0030090308051561a62941d030204003003032041070000340e41b0303008e00102404040121001110024419032500000400640180d0014102024996a00f08403240303003103800e02605100710b05c0c51034010394420703403443c0100448103107551960092408546580004007503248800581d00301d2400205801125140c14016040d1080c030f07a0b800200000100f020005c08a0280c0140d40780242a01a012119082e080c3c5e02d010ba4450750060360b000c52041c4100fa401c41005041038076010300045500368407400450162410b00095084446c29610708 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138770314 1250 138769064 138769069
    0xf14070f05030c090111010507020a05010b0301060e01030209060d0c08161d0414030409020408030702100305090601060807051b100c050f04090203090a020d0c080f06100b0c1e0309 79
    0x106a408241828031a1002a03a110000c1c03290100421446840b2000606010203a024109500c4060640c200a000354500070070025100c2100d403d088443e50300744000010a880c060040c4400d4409146072200103030318580030007902a5010300003682100964143c5004500000d4921018100410090821425a080520700c540c0c580d403154a00e126488030b100c1c194180205481e420a030890908003441810201031800c510560380001940c078030000d40064900d90202c0038081042c0225080518940c1c100740c1502546c108580d80d00070340e0443d000606c0010702880040344c00900c28501942041202011580043d05504006100740d00c102d00176295901d8501801411141c0c0f450114103040d00185502c400340242d0150421035074001c00050340f100d90820101a181d80c0040040c00d0480305420036100c3c441150040311403900982403054084280020002c0c02980007121b1014141c0c0740009907042d5030000c1199207101c0c040d81c003030310340039003406007a030807160801d400a5581c031200c8a04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138771564 1250 138770314 138770351
    0x60607210f03090c0902070525050a080106050123040e01060c02130b1e011b030513090207020d06020c1c09060905011d01050307050708040b12150a031b05040f 70
    0x199010107061643c10000030b10410010401c40d06901ca01584815080c90303e64140038590070444407840d5a440d02081c803a108280840407a4130036192450ba09844554a0742a40d4442c0504d6010070307000c400d0f000e1540800620203d00c1040e00d0011400c1c1601e0390ba800b08940420703130007a0006035041078508254901400f109030701409500e020411100c00e880481d41c0e280044061421012482e94801703585e0340910300c440c100d54203080c83c1d8401d034012454094000d07005141110f21604401e00d0101c2d11203030a2089a82c040d03001400803100a01c0360f07039a070029501c0308400301070034007405889507404481c0919003c05c074011900c079100241c4c24008001c210742150b0740841d0402200d5810706413070140105003182c540d0b90a18000750780e80d4542c201a5030621520038020b00840e800100086d0511440d409090a400140b503044e509880b190901c400031101482c000303511030380f4010100001011080064404240d1110107140300d550b500004044401840c010700501c1d03107480706006695031401 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138772814 1250 138771564 138771587
    0xc0f02030c0d050c10110c16030c0b030c2109010e0d05030c03040512030412081b03061306050402070b060f0102060c04030303180210170a11090906060721 68
    0x100031420040a1040507a64030000d0100300709025000510180e02001070140710707a005010f20007440a031000c9801d15800c0d07400000c99000307600031069000090302c001c0d1503110480b900150042005420242014201d034000b80040c1c0c441e0004001018000195400d00044611012041401450040a21805e4408403c07000040341c02881515007080e404c041500e07007122051355200d03140c0c1e56914200d440e11158000101c1642004410081081405240c066900e815981d0321103460f1903802c283c00908502d030f020020b820304d050002407800e05060f20540c54517000008003007031035955000850300700c0c1d01401c01580d9140402080200c581001c2c88001c0d0500400c0c80140054a041e1240c880c15020701c0c000241096140da5121042900e0b6010031813415800610107601081041006010907032040c416000b400241030000340d0342c0c14648594184110b81d510101d142c00c0c0000100081803100800d200e0b0710040c01d0011201040e0300c1260b140d045081e00c403884038500d10b8007d0141c1400c0c000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138774064 1250 138772814 138772817
    0x8070e0906010c03080408042402070e070804060209030a0b0a020414030303060303030f1e010f0608060d02030d051608070821040f020411090301050f150406080604110a030b0403030c0f 81
    0x1052003580d903841038a042030f241e01841c20744900c3c0c4440c5042800384c421a0300c0062488003001c030b05000042560b03044038030040940c003100c00103940e404109003003003c100e0300500400c03c071340000b80214001380c00400c0000002415141100041d41d41c00c2500780003502d10446c0303250b004c60248501011404c400b04010f404034011802c40c9001c0c00000d5484c80b0007004494819140004214410705102c0c040180c2c0f1071042980645603110580c21003101010311554000916100205510303081c080ca031a055150007501030310b0740c0484020180c40c0c50f1b000390f5111545919888011020401d41c10180480c1e0384182a03c0741e54800c1c03418046002c005100c0011414003000080c003000443c400d007000640790f4103403030110740500f011003001564080c0180041c0c040d401d0504000703036414906030f1640b18080301044442441c02040512088039202d000c2c8441c554003840205021074414a031140c2d415000800540001da00c85c0d49d0400414016030b0100c0100380ca8441094003030307401003081d040d081040e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138775314 1250 138774064 138774079
    0x1061403090705010e0d0609060b040b0f09040818060403142401030615050303030a0506010206090d081918030504050418110904061d0c09131212090209010608070e 72
    0x20340000e0b1210828400c0030305102c0b43c451046003940312100548581900100100410303841414031001800703204862920a510b0175000e1011031030030001c0d50502c400701902c00020780d031f11aa03915210b80c2c000c5203510301d6804211050456607580c4002400a940f1600c40409009030400500345050061142046040c8615510400c22107000050078112608010301140c40104030030483c4c0050150340015030107000c00000c01243d040350b60003545c001d590a90071189103554500312540c4529403480300d4800a41911b02003840f215040a0b0b0385e2164610390800a40808a194500320801014601318041100401c0c01c220030315180c45004200c050300925400103502507500c035140c0991155425204041c1500800d0510821f5440f00c05001611000607260340103600c8031503502c208200d2401e100d0030003400003401e1007640000c4903c0c55580600000740c40304c0040000d98030750300501d0200b50003a903141d014101598540080351300901c5c2d00c1c1c84a8460b418100d100805c80d00340900b106019140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138776564 1250 138775314 138775321
    0x90c11061005010f050a090b0a111507020d08061f200307020105041e030605010b07020f031c0c050a02041b0315081c030608030301030b061c0201140a031b050301061403 74
    0x13004890800d9290603854444e076601002207040c1e4a8031900d400003a03050300702150f200b0065422402003502072010301c0c02c65000f1030082d4a0071110b01001c44150340142c0103004514445401002c90340d410003801400721805e0f2030138000b407590080065444000040e1502d90525040c81045602c07160825504050b500d02400c50700080c0280c0310340d120710b200090b1b0048502244110122050019652001052145580d190405102c40d0048201a88500b82d09100388000c2e28000919001030762150040f20001150814160340c48160000e00f621680281e4032500016074552081640a103e22002100c07100010f401c01011203244485521603500e4a40342400f29460005030340d41481200400c0e00a40400c6440840c050072041e0312000151001000101c1080307100036459114010a9981e071106151203240ba0f01143c1d18040f002c0d011030034041c030711102c2228040040c0300240e00c50801140510100c040f60072058019400c040c0000c0c40400103100c0903a008403400c03a4080d207075802c80e0550a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138777814 1250 138776564 138776567
    0x5100e0105060901121a04060e06010605040611030301050d02040504170c0d09050111060c1305330f0f0f09180405060105010306031a0703110301030804050a0f030305090f030304090c1106100501 85
    0x4242c0b8640102c00011b0034001010409590040300840c60301e402076802d9035944420181540e00a402a8000710720116020310440c0000030541e81210b000a110440c0001d079502401300900d0044d005445800503000030780b04210b900d1000b0414172000800408224007036007802801044141c004504101102c1c0c80d0010304500000d84035001003000c0c0340161740b145144018003040d00d0301e51000d0707000059010200c030807032040c03100084980d0182e25a41241300041c0c448054900c00c0d034591541001e400d00c240355400b1002c07409018140800c242035864a034042d00010003020205401401c4002c90508001c10400240b010074010102820309010003421552000b0b850240c80600640c0020040f0008190f14465002150343c9080e0000d65590f95071a41044800b5900c2801240d004c1c2c03041e540d000510380e0349424180105c80c0c05659060600000c102000900c800c40c4149a81c1407000b44000321700d4000307521490329a4400340d214044010980f0458904101006003041684140c3e1a02000281d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138779064 1250 138777814 138777833
    0x14040203030a110c131d0703050703060e010204050607110f03030306030a03030902061306120e070509010b07061d070602010506191503022a0f01062105100e010506090112 75
    0x1c01041c24942416000f0303120207032400ca4000740f5203500c80c030001d0860804039003d5124010034001d6400c07484100c114848520f40d01c4160b07200041c0780764402d0000b040459000d07402820308008041c00503180075030301c5000841c690007403c3d00b0394083e070040d1748281e01031510b2082c0d12910202900a1410361500d039000940b140b01000740901490f0b250070311503046690300411120841191504541d9440d15007030000c11088040c081c580066180048501d918580001c0c0e58048420060825525a0a1265444d010b820100c0201c2e4030035281c0d42c05801c07041c000000f120880d1a01002003580d14640100203080d00c101800f1140500d09010b40343d940084032507100b8060759024800304803481c228000803002442034080c0d84501c00590a41e2b2411000e4001c1c1540c0841c14000442e4607082408c81e00310300300c480c18030032445104d0f05c4c00340c00154401d5150381c200c0d840740164240e9000044981f14071059800c60482c0d014542d546108102891038103480c0b040c098020012007400465450792030b40c500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138780314 1250 138779064 138779077
    0xf0e0901050105160807050123010e09030406030c032c070902090906010c030212030703090215030708010905060402040b070b040615030b0f0a06030609120906020309030a080706180809041404020303 87
    0x14103144d50f6101c2c0a0082d91011580660f038420001c0087c6468000400b080180e02036200ca16010044000900c1c0000710140c0390040d00740344041c5107840c0c81c2102c241c0042483e18520018161a43e009981c50b101603031000c150581d004404c000c20107100c140403401c0800c2a0410030b038052051180a94644a0003030301a4070100a0a055081c030903582011b901d800d1035243c1010f0a0b81c000401c004c035140c0d040e003000040500c01e42e41c2004400b00100c0320821030000b260007000140e088070041000c0701d1b081d0001c035000b102c05030005180580718440c89a01e541710304001c0c1c403500c1d591010701003000710038031030380414440d0041c55060b00c6003180d0300d200c94042c0103440c0301001c60050740811a01c1001e540944001d50b4404401c01c040e00740e42c40e02e814025000b140c0100071518103000020128004421500171032001805042002e509a0310120755410074a4103035101551610007240c0d01040e5040209000c2c001c80d0500c0c1c0700e080300c404001c26907000c00d41c2804141c407508103002c01070b1400020b0b00c95 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138781564 1250 138780314 138780337
    0x30a020a11010e2701060e100c030e150301172b090b2109010e0a02060c16230a0f03080306040f380a030308091009030f0e0901050105 59
    0x103070344030820012a940441912103d502c0034046a10611014107154812582c0596054244007680c0e1a13005480600d42c04a000703400c0880c00c0fa440e80c0c102d00c00c0d0003800406100303041a0a4903403c1c40c0220350141410440262083c1e8000010312002250b5680c4080d51800c000050001cac9010511100c4001c02e145200d110176030110302042801c40c01444490701904c41c0501181d110855550b4001041c01c4c2440c00c6040c080780080032513242a41070080d40740354021107000b0041d00003142e00b440400d902c81c294211280c0244051440441d01440c4010028000800968003d00200c1c1c1001190000c180115201d44c441308010054854440043c40c01c4a400051181d22a5a0320011401500d81c04004014062408005003440440301d070b88140c01620b90031500b850003c1520040d00380296031006603901811002e000c10002c0d101d0281254400321031000c1e5041d10842034941403c0d1036038444114007160000c01c7c81d958150b03100500030021103084802d241e00c1c2d45414006030043c0302d281540380 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138782814 1250 138781564 138781583
    0x307020f1c0c12022104060320030712140702061603020703230903060406050106030609090b0a0905150424020910050f0705060103061b050f030a090c0b0a030f0b03030a020a 76
    0x30003060017400065058007502400350301d0a81c801e1400d803071940c03040c00b42d00042840d0254055061601c65030151003445e900702c0d4545541c031901c00c280ca17a0124410b983c440251503260601c02103088010342401100c2c90380040440f81400c3d00c00c030700c4851040902c0b01c10144107025890100f03030302c0303150440640d070b40e41680000144007061205042c07140310403203601032240707400b88403c0240c00d81c4114100e84540da0304000c4d05480341c090b88160746442034054208644600407900110050b8088640180301c0c3d001c4580d10155a003100d00c4d082001c03141940c005c100c0321a00c6040400840c03811150416203c801c610b0145240e000640c0c81e144000340c04100000070800c00401e01c0701600b228515030b006001c070350036503039a49030000103404515201d14804048242c8441d8450081c2c00b6100004071070b1840f0b5046d507482c0419000117013807120007500c0c4100080e6001030f050200200130300d00e00d0704554010900c100c0e014a09005d42e0b09c2c4004240c000d034010001c4844296010490b65110f583c840940c2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138784064 1250 138782814 138782843
    0x70501080613140601020715080a0b01031d070509130519020301020c01020c2409060f040c120b06031b0310022d0403030905090105011403040c0306020307020f1c0c 72
    0x2018106003030388402c00189803607a00500300b061140c000d4800d080076822620459200e94141090306107032128070012582c80c00c080b500e22a01070300400b03031142042c9000501e8000c544ca940d43c2500050045c61144e40003480e0034001c605283e83d4482c1d0060030420b0480f5090015540c00755554190002017040e030200026440c00c55500f901120780090380c842c000c1d519158109140754485549a480b030260003404001700c15800d00820105100ea01d814010304900e42d20810500e00c40d0000402c201e6000d81e030706d0004075403081e80400500d81c1502607500110a0301d440300526140c28581c07060b040014044e640c0354600b941d00040c0814400c86003503030150b2104650160301264850f20450704100c0842e5500e0030ba10504140080c0003181e000c0d0b07950054007660f440c10301881c1d800c00c0c01003500048001015141c405001d00080d40c100e40304540442000740c1e25103c0c3c5d42281c00c1943d8480c010b8012069180030f05000704400b01d0442544d900034420400e40c424040e010300c4030799600070300892144804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138785314 1250 138784064 138784069
    0x19020a0e031605120f0706050a050c0102041d060a180207050c04060608041502030106050f16050703030503010504060f14100c0b0103050706080a021303020402030a020403080f0a020c030f0705010806 87
    0x1904101001e021a41c508603040d10662a1482601603d80a0000c4042d030559104000030342c040c3c000b12040191017520300b40380e03048440c2c1c0d001c6681a001d206c02004a031800c0301c1d09200500081140410300e01c0800900d0342216140c20014140920400084038203003d50540d5803010042a80c0144c0016900c2101c3e150181c100903132040385584c401e2034940c00103803d075000003102d440f4a1158064048101043d00790310708a0000303004400c0012401e2021035000001d0100030003002004511208403988540d6540e0b28001a51300100c00240c1d01000400481c00c00e07008410150401da039146003900d0600d1040390b4801c0b2000302c0340380704100010300100c260740181c0c042017100ba0004000b504941c0c40b820201d60362600703441101d001881c464006682400c95200b82d500c5c603075202c0c10540070545180c0800010b074101400d010070156013004000009800c28004014640007070f6580c68482d40c0445000e818149520445402a00b011010034a0140301264031401d0f108242001d01850711001e01 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138786564 1250 138785314 138785327
    0x1106030a0605031f0e030a02211c06140a03150f02120115020606010f050712020309031b030705040204033503090a05010e16030312090804150f030519020a 68
    0x4003070b070540201d00c82c4c13003920380d01c1e204051a0b0358485501802540d0300d01c0d4040350359200d072041200050f0001c1c0344110348807000803240c11755000882303a80740c02d00b803041c8134104581d1071590b009855217070741f01d80801410740500c216110760b00044032035203129455a1600c0d03061350024403404032a1503a8400d0310b603181c1c3c3c0c80d50681d4003420721013149955540c1c545005c00718014090506401620510001603015031003481c2d8120001826501c0070700308111a030f5111841d440395075585065000509c5408240c1c0c400300007960b50030200e41641d440d8000c081c420b250034180640c100314001c9004010a00201d0807074030b403585d100329005010710011607102c080c0d100041c003042c0b02500b00000c004144610b08000241030801c25004100800400407002c030a036555200d807041c802c0046850b4007040002ca40901041010104603000c04900b0340e61541e9101403550094210b01300c000001c0d0310074004954031400c1c160405015003800c116a04011858560100d2002028840c49400207003d0b041d4510a42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138787814 1250 138786564 138786569
    0x402130203100e010b040506040504020a020a170a1d0120010b03030703090504380316060305090d050301060c0b0403020a0204050f06011202030408090f1f1d01020a1106030a06 77
    0x12800c40d1a820401d800e505992000d01c0303010100c26200c0000715074180c450003210102d817002080305140c185003205010107900404080c1f01580260611750003c100c00049032500c2703920710b1030640d645da85000310140c104440c000d07101400d020304544420460743c0041c004034040c03051000b041c09000d440c009960150249011468150001042c0d40040640080d8800e003176a001301d500b8412098034484004c20102c49207020140d0300c6903081c0f44056400e01402d00143c1a0001e029141c101038801100b81e071075181c56101a0000742d68104200f26180140000c11207100d5915003d4610752400d02c0007062400b0582c000740c00b1f40e800134081010180204516940c50754080c20a0256290882e00010315180884070240420340700030f074100340d028140c800c4900c520703440480607081c44811818400003102c0140700039040403e00010305002400381d400b0000702d4240341d0b195082401c824420b28407008400011030b040d94054400400003c2100ca135001c4081010348641d034407591400340d00c501030f10040c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138789064 1250 138787814 138787849
    0x1305120a0e04060504180602160c150f09080a080a0e030109032c010c1709120604030311030106051219090515010b030c0301060e030c131d0102031e0402 67
    0x103006440e55001080041480001c9508000703056680d01804140d40400c501044000380100c0b203007000420a41c041d003103c3c1d40c4d480011001d80403550780c0c2084e03c4000d81215601e811000000c1c010f0641c040320110100010746480e104152030107005550725207c0e000300400300c6001203010801241300c1d98100c224404004c0c000d0100b00210304003e00fa07076110080900098088030b1106240c402c241782e0b00070031100182c4d181541403060b1b4481c00550140b000d0708031030b41081001908416070300c181c0418160145040500014100351078040c04445020f076038125070749000e2004005041c3c000041c0d6029941c80d03948a03006944510b140c00d01001d2000003d01420316202d103041c1400301c0000c4a40400c1160085114680d032a89007081a87c04112540b171100c4604100601895107d01074818543d54007408503000040700400080072601c10000310608650b44500300f121961036802207858004082008500d142464410040032020160841c82e0071303010080460308540319451609805c0044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138790314 1250 138789064 138789067
    0x80708090a0311041104060f030e070911030f06011704121106100e010506070503040b0c0a0b0a0f0c1107061103090607050c010f0311070204091a09071a090306130512 73
    0x12441c10300c0902c0d6000f0500d03030146280540c08241400018100e800392500c1e600c4184441e010302078120050944448091907a00407040d002071620540e020b1040300d10340000d01c003500c1703280a07440c1042c900b00040c04c03103040003e0b05484151a41c03504d5440340c4c0164004002d24103500310600c0903140c40b02010984404d5100b240200140316106079500e00036a01840150003030750f640d0b4070030410a4040d50303101a20700d400421080024555140041150300c000c43c0540703c803030040c0d0315000780c5503001f1546442004d40720801c01f40c9079403840c410780b92001460b0518514412016003460b941c0c2d002d074050070040c80507002110319a842d00b04141e0384140801001c0c1c9a8540e1580791060315540a10350041c0428907803a01004c41a0103400751039800303030301a0f1007103042c01081e400704801341c4540c1d881921040a10094152200d40500e101c52103040c03c0c6000782800c9280c0b400192000b01c43c45041151424240303c00c0200e69004201d041d00011300001358200301d03405040150404524129034014800c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138791564 1250 138790314 138790319
    0x30809030307120e10090b090405190e030406030e010c0927110903060105010c05060a020a05040b07050106050901050d020604121a0f10060302070b0f100f030807060f0b030703080708090a 82
    0x7131103115050980d0301030301c0045614404840541d0250594020034480c0d040c1445860a24203103039006a500c203541c0d03004007814410400041003120081420030880343c01c0003505214240c3c140c000c03120301c801003200070030801d10344c4176000703115400502407903c0c2c0f81c080c500c101d002d0103594440c07486040002c041c1004800041110313007403d0352001d00101e00070b014040c00016998007a03200c1c0008150030030042c00103680c5030110700000f03500505400c0203015040c1302c00304410807140c1c05072900b203110304000075496007000104102910f0580c841c0b44035400104854005842d4102a50300f102d0b1070801d1440304400c985410602c038102412030000c400e000c1c00c00c10409a5480301c041c0c2c06181440381c9908007546a9404800381e11800341e018046c0300324440403540301e821800011f40d015003698001c11016455520b9000d0700e0b031150780b041d034011801107404418800389210f2890420380228080203a25101004252034060911000c0c10040c5d0102d030013420301c050142243c007240c07802000700203035a4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138792814 1250 138791564 138791567
    0x3030a0b130c030e060106030e120a03060314060a1b0f0e1c0c030b0c0f0711030f060115020c3322031b1a09030a0503130315021303080903030712 64
    0x48400b44c248603c41d000001440d58020701c1307043c000012a90140c600d501d8001c22502103988041d44075003c05988820000c0400c81190b8640300440401000d00b4907030414400341c40640d2a46501030040c0030811076010b4429401c0242c4822070451030401110050b45000002c40d4402601d20882d45401c15000c0d40e001c002c5a035851409907803082c2e01c030324055203600d4a90105400b4126001c0c01e0104100075034000300b444407a02510f0f2070781c000d041394045501000321a052910031781c0504c50100b01c500b001e850039901406048a51003055a04020042c2e00c40455101030b1541000701a84000c1c401400342e004402008130743c000b5501c83c4085200860244040916841c2440280d400703282c0301205e160030507090040d0004488807910440c078032007107910300500301d81c1c0560102ca2380f41c072420f40e04400069007400901aa1000c00480c10681d0b1b00c4c2d8245071004902c003180c200d44ca14810411011143c80c0c140b22101a01c1d007150580b511100e0310070220b45948900240a0851681c01e81c0380c0b55001d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138794064 1250 138792814 138792821
    0x1020702030601090902150904180605070905330705030c0a0c060e03060f06040b0405010906030b0105030a051f06050913141501030b0402040912050403050d080903030a0b130c03 78
    0x203403007079003216156a640e0001d003003190301000001303600c10001e5149254260b1008090004203d004000140e0340200d21a100d80c40c0140381070864080344c64504000280350484800401400217882829100705108181e01d4010001100150310440c000f0b680003652150341c4c143c6c0d04d41c40d82304040300d56807080102c004e82d985e0754007a002c40c2c4151082a020803a18451110050b2601020b4001c3c94a601c0705024282d11910050207190070664602c4200010f075618000d240c0280140302000805e03d0450400001a000c1604240d000303a10125101000480c001880d281d410605a84d8144014405140d9000340a80364807541c0e10403004014800801c00d1104680040e6218004800d80c106803420780c10b41b00c444ea031409081c007034101c1004101049045039000d502501c014000900c4401c2c076074a0441f1076184030010ba00181e40410203000700b142c2000824404c01c080d0030800000c0c9003500401c0d45e60311000341940c110580300c400101c070907280c003c01803107200a54903090100303840808e0002e008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138795314 1250 138794064 138794077
    0x408010510050a140108150a0e04060b010804020303030403260c0d061e14120102030c071a040f11011e111006030308010e09120301030602091906050910120e0102 71
    0x490050401c00589854044060000c40751400b80100700c803584240159481e06000f400c9000d10001d00ca81d01c0950f6503482c881c0000781c04020400401400e05042601c02c03900010021410f000e11038040c8005640d00105581d84181d0606e405503d580740441d4249039803403500e0348840f81110300c8050000c0c42805c200588010340da8503e081000300c0e543c0a07448c0780c800d440c1001c0340d10342444d007038244009141c1c8101160005000340120354128000b02900b401c90380229441c1e4410b0201094010420030020181110400301d06c1078141681015120040030000c5a0b10046c10b00401982d414004e074007070650729000007220070782c01029000900010b404c101119030040080c0c010b03035411f04c0c680c0c200c0e441a181543d40640c1e032144580c3c24128480e0010b08042c122111324400d01d040141e2843c000e000a50185116400240c2c850686009210302c0c00281c400c0006d00c01c08841061109545c80001d540d01d92004466410016200c101d05803141d00030a0f580d02001811b001001075a00d0b0150000c0c1030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138796564 1250 138795314 138795331
    0x11070b01090b09280216030309021e10030b010e090a05071b0c05010522060309020f09060d020402092d01020d080919080c010510080106090b010806040e1204080105 72
    0x3048080c0300c2040340c05081120222500388140c4c0000e00749905605001d071101c0300e1144010701d0100f42c1c0c00548024032200d0002c60009131114060b03801c509190782000071501c001803c00300c070f10101c1000074044001641c1da4030101a40d0300304041c3c0603803040c021148000c0015050400350b06092103964003400c07040f26800302064100701c6408001c0502032441e003015410044031551242841c00444403a44107145120360240c84035800c00d02c00116440910040240d170702c000070170780c40b03038418440e51507a10038100788542440010043c80c1e0300c4104041d910181e0458005990b016002c000071038605502e1fa4015071080f000c01d0302d24006c542e5a010500ba000709070201e928200e00b10000b15240701c011124801107410241051003521490303500341c0d81c034510403a42ca40c289401b0082550856000b107410718031a00300c01d2420003509200b0721600000d461007003014007480b4206030028042d2000581924044c6a4480000071b90701d90520011801c15412002a5a916941e24043c0c0c00391405459205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138797814 1250 138796564 138796571
    0x504021c060c0f050a170622020904051503030d200708030114030303040309061103071e060e2806060509090d08090a030c02280603020a0212030c03061311070b0109 72
    0x190f10301034000c1da10182c02d2640d5007541c100e140b25215021314406480b05030000f52111280c005003000c64200ea5100940c100016214031030002008151400034007481c3c0404860303400c504d6182c402000316400d0341a2000b010804520186c00e120010700e005a042c0500000415181c04201c0c000300294121190120424a031060020416881c1c0c0b20a40e8001c001c074880d03443c108030300c5000b80100203100b50500141e81c1000503d407141c80d0521a89010400022805a00310080029505c9a0740300042d0a0000344401c10000d00d0007034040f0302c0071591105c4641000240c200304000b03600281d0142c0f80240140e10141401003c2c15034640400301b44801045281c40020041400041c0c41508160503996119600c8810b03003d003c1c540c000894050341602f50044564418046c1142c0d09000303100039500160740f81030101c0024202910b0001c4403c0d020010002d0203c002900b01c26a03402a80441c0c50035612285501008024000640e968010950200e004014803c845413031a0480781c01b400d003403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138799064 1250 138797814 138797837
    0xc150c02031609060b0310060c08070602190809061b0f0d090302070303110303090604030e0402130b0301080106090e060103170c060c030121051203220b0a0b06040308040303030504021c060c 83
    0xc3c4014081211f41c5400c281c2c00c01d00801c2050306c249840b1200b680102c288600d4140c07251144000c0c0c0c1e216031624052000041c116441059004011f03591001c5808003821050811101c030b0f004070300340d009060417450000325102c4000e0700f122040f101000c0d000c50301048041500e2a000e52100c6940c4001d4012520f0613007051f20400000c81200e120f00c0101c0003400d610368840d9000e4504684406500741c006a0031303c40300c0030104403d01440f000d03001c42c607002c1e500c940c5000c24903400e4402c0c030740050003000d0800380170440300c2c04006034003819641c0c01201c0320011407a80341081880e008552450b6000d1107181d092100101001000310305862059482000c110750308c3c4150181102e00d0f0500410799407060228900401c10741021b15000380c001c2450719207607030518030380341c0241b40d45c07040c20790f600400b00040c4008002284035001621a05030f40710341c1800c0c0b6549403040c1e28011884090203040d01d41002908542d07a0b070007649058a800000c0381e04855142c104030303000300b0162015001261094408 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138800314 1250 138799064 138799079
    0x3070503010501091b17070305190504060e011113030b07020102120a0b03010f06080d03090c0b070302280c0e1f120201030c1b0206070507080102071401050105060301030c150c0203160906 82
    0x281032142c3c800c80c010750007d0301c42c120210010b200c010440204d15140504e2480c503076100e80102c0d801070f402640e011880c0403200840c507003128400503444500480070082400350030b0400718040e08072a04000c4400031655a2001680a84140c0e00241c0030728221104001d0180d03400d901031029254164000c012800780001004100e50981c020000c881c0d00510303451010707a00c2500302c03807481480f0702c92070001150f8070110441c954001003021000344c0c100c0904a0b43c05801f40d03580941c5143c000e0112854692148c45c1c0c1d0703604a800c0c1c06003d61810003d800100741c00e0420101401c54070400400d4046d031650f0f008109225644108120b0000b030401c0d0000350741c544101e00c3c0034a105883d80204028010b581d01700318150740803540468903070207140da000400100c02c1c8040c0914a00030070706100d040c0790110000303003100c5058101d01d1066500b4401880400c60300801308080e10401e4000290b140601720081d142d00300710600003540751003010b9001840c1d082c140c0c114800c42d0b1001e201400141d480784103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138801564 1250 138800314 138800327
    0xc0807020429010c110d060b0901060302120f06010c030503090a0b010303080a140c09040c0c120801030c0e040b0a2f0c070503120a1404030b090c0a06210b03070503010501091b 77
    0xa01410304c045d64003000ea0146040900d28005030f10607103001440c3c03c0b07500007245281702c09a00927404680e02141c4164424040058158400100040da41c0d0311f1404c800068080c00c45045d020b0100721012000031103032441084180300c6a03400089102c81503a40c1d19000b400200100c500703640050602c180c100d0804440c03698503000d446c1c064030f0941460060001e0000414a00d4000d10400c0715001c0100c8c041950781c2e5403111800e07150ba881103802d604600300a401d1332101d03408440d04407503200c10070000c204100006034000ca00e00b10042000280c00510315205846465001d0301801d0b154040e28820a903500100200d07450b05c810360314099a204205a22492900c42c1c452030004104074155906201e800210300e859401401203040c1600c0707031070702c02c0308a00c221b50a8142d940300c450600018900005c81000130901d502d4248404191104980c0d4100881d031152111903446444e0703a592980c2c1030000d200900f1000d03008126035a500c02d034080140400040b075680a030460b0500070040f511908 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138802814 1250 138801564 138801587
    0x4081009060b030303040b0402310203010503010b0915090c0405120604060c020f030904050711100603051c1d03071505030609010503190b100b04030503070209250c080702042901 78
    0x100d1f10f459855409102072198030319a80d2900341c0021110602d450290a640d9020008000b8010384070343c10002418212400c500440784a00403d00802c0b03800700c0ca0749102d2074080c10980383c9440b2600c9011000721103001c0c0341c2040b40d004100b4201448450740012b43c00d031040d400780c0d201f4841e10740300c443d00381c0e150901250038a155030010402c2c091107082542016070050716900c2e000700540a091001d9051131803204000c000325807203103010010310070104101d01a01d02110401c1c500c01d40c040102070718004819180036241509100d80c2c031240d0f41c0c10f002081c01001e240401240c680b180304030003800c952080b030b005440f43c1401000402c003400c001515212402c11402645210718454840c0740004a000f0300c1207580201442c4c0218203503151a0161008511400095444050a20410584600c01810180040c0400700b090001250151440510764240e080442840b040b0b81400d01c414400c0110103500a800d05680f007080c5d014540e01a95034503034500c0c4d008031070880640119203000068 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138804064 1250 138802814 138802823
    0x20315090c04060507231f1b0e1f09031a0906040201050d0e0d0c060f0c140903030702060403050c13140601030b06190305010f0504020403080a03050402010504081009060b03030304 79
    0x34002800703c980620010f1071564040c0c01400307410100f80030520031070f0301d595040d200f69810152045c021034030300344090100c110190341c060140404003a41602d100d0500e0f041d4804002680360f8152180d1604034117a01c030704c07030300f600111592204e00b500070341254024441282e080c0303020250403d1800403130204500421245002d0302c0151150740044a090700302c5030b600845a90343d007904800c511400c110701a032032035003030b00c450180c40c0c200d050003c11103500c2c0c13901800040c1080ca4100e080c945c01810302880c0041e0145440d190340000000c24070703500500717800a4101200103004000d100001a9240c0c2812086405c0140110b005040e1340990b071007042d0440c02e40f8102004120b81d903001c0e0b00140d403440c40c003510703060038020300d60f0340c841c40001c0066988001c255030720010300242c0c8000c00d5060141a060f0740039882c01e840d5a8805400788540407096041556550200c0d08680c42082118010607020b4121400c0c0440311a03e50300400101204940d1a480c00c46280f41c10305010056070b01c1560030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138805314 1250 138804064 138804067
    0x405120106030c030807080f0307030b0f0405060a090f020f0c0309120a030c08090d15090c05030a240902030304170c150a030e0c0604080c0f0315070c1e0501020315090c 74
    0x42d6a145c41c0319030801c0404032641c1100b446100b00c0159802e010f1072080440b541d0109500d550784007809894801140d1590045080c1404c0203820788411031007008940d0000d0b00054481d05034103841c0002c0c041c140803000d0074a400121002c981c5000000380903185800ca03042c00400180b20807841c1c0e0741c4407101c030090205801300104408038440c0303805001d0826010742412280d4045680d8070740307801802c0c0240c0b15406d42c4c0740d090400348112220300b28090714007900113080070324a98458061080700c1036a1078075a12460701c803c048030341040d04008141035020b400c40b0303121900c07184000309411031400d2200c114031540a15034040d14200703c000300c2c04103140110714030f0282101c00031009001c50040342c2c10300e8425440725410a0710f400000f0001400ca82d40948100500e40d02000090a03d0354001d510030341c44402e1014640d80c070b45c1255a0070a555007010303000300c2624a400004165544490050202810030f080b040c008103400031803013001c03035032082c000c2d0300008403c0003079500d0251060301d5000d07030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138806564 1250 138805314 138805319
    0x10c061b081b360607081201140d0f050a02060f04080105160f0f210b031903090e09100903030e1c120b0d02041104080f03070201020c0906040f0e030405120106030c 72
    0x4204266448080c1280c290300c10341c00f100001c2072450740b00a0b012207031500b00088500e0391080c41da022601404400f20380c44c40c0c024054000903c1000c4042c0007402800201506608000d0100149501c082d40500640d0319004010000401c5800c54400c0c000d0550030980020f0202030400050070182e9255120840c0810101200302d4050032003c01000501c41880c601e4070004800702c200c0c0c04014820040402c0404018003807504101002400c00040f940761502d001c0001c0d00204640191179120490206a0f51200c0c82c042c07805900c0e00b41310704990320b08003148040c103900d60441c0c440006410110b40c0c1a00642030340720700c410124400e56000901d80314024030b8104098021400f0544010622030003480310f60005401c96203d907a0000e00e41c2800030f0200002c036003e1104074071000c3d22001039810800d954001075115140c1f50a114414007000000a24540d607682c84284001c050b198204400380e08000300940e01d5015028885c480c00114448203c2842d0500490041c1d96110080154552 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138807814 1250 138806564 138806617
    0xe07090602010b01140c01140c0d0f0b06030109020a12020a0810081603060e0705150301050411030906010501030b0607050115080f0102280215070306060305012102010c061b081b 78
    0x2c1106164030b0341e554940000c80b075100c1c40b41e4415405481c002da189580c4080e055900000c551040800c018113305101003402241d8a0f002900c0c111002050050303070340c1100760300440c0c1107075013890176071a01c0b440894418000c981c41042d1a12400028001c000c1e980c2c0c50780780c61582ca00c81c00600340c16130950104107000082d00340e0420940740702080f0454800645540004450640e070040d030702402e000100040000e89454015090040000103006181d4180031610b1501c3d84014040d19042c10744441d88081c0ba5141c0700225142e840c0c02400030012004000001c10910400e8424652140f2600c00c0003480b5503130601c00c558a050005c06040c1c014000943d03980030f40b0003810032880950180051342c2c0501c5400b0b0380d00510941c510780d40080c0d000d0400d04080c04444c3e068000400f0794043e006540042142c1d540404400c1d40c09082002000c05039203000d8016100901c0b0390303600c164081c500030a450360005544d6000b8072281c038204010000f1850303003a0142c0140c6a000340449415140f07642c02c43e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138809064 1250 138807814 138807817
    0x1091103161103040603020304120903020d1e080309030d0f0203100303110a1209090e0106060903021c02040e151812070305040308040b03041e02030303060423010e07090602010b0114 80
    0x641c15040c8607a1002c680c1140c1c6040d500268001000f090f000020401081411031508401301402d00303200a401d811034020074442e034100b25009001c6004200c0e00040086000c41c07003001c83c1e5101400c250faa11300324401d80d4036030300000c01c02035006040410780c0d0000c03550f42c000e4a1082481b60454041c080c5107481c2100c0046c1412002d41e020b0094211070f6010600f1313042d4620741985507440d280c400e40c1c0f820352668100d031030f4821052420b900d40b8005211441d44541424116901141c25424011007400c10100f07031203000350f000394058646138540080302804104280320640880381500d141c0d6a085810000348599a000d92460300080d0700b0106100581006d810407070301900e041414241c896455a1040c0d100d0b810003403083e1004000c001c03c011004d41d81070f541d1400948400d0501d182a80400d50340d000140c001071060f911240c402d482081c500d43c101c0c1111071081c0d401c1c0c809580d900310400480405980b19070004041c010b02258007401405a0307003403040c06a54010181c41541c0142c4102d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138810314 1250 138809064 138809101
    0x50c090418020603040c0501091715060f040603030e010e0f0a03030807120501030b0f010504021207050c031c0f05011d0403031812080f15030c062206030207060501091103 75
    0x4800c5100d1001026843d40382c05144074071b1007041070036641030070b0500150001c042c81d4003100300f1307100c051441c2c00d0300c1c0b801060b41c8561500d10500c0c0a031545030f841c00229280c801c14500c54125107010000424954048111400700c0030a80b240021110014180400d038142203171055088541c140040000074843c1710300320381c04400d40c07519500000e01d03058034a054800a03031095484174560824452100c40e03511407070f401080110380452403c119040c0014502c3e50040082082c000d005c03c9107001d29000380222030043c42d0540104809000151400000b880d0001e500441e503494800003156140070561405d00405a608044225683d1541d088003d8802c004e492844850115082000182020301c004282c5009031505003680c03410042c0744072581c0000b03140c5402c80791004000d07801a00d010503800090107059076030315075502c40103250070121a4440001d05922a02d8030740026100e60503030161082c1803254405120f641d0340c462480c401d031203170000020185101003000c2480f41c000a08402c04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138811564 1250 138810314 138810341
    0x406050f16080c06012105061303050d0e03030a05090703050a110402120a0f0b0402030112230f0a05010b0607020f010309020f03011a09011a1c06051e0102010e01050c0904 75
    0x703905095030b40d0001079004030024a6903070344518010301040380c0b201048901031076000715420304030a2546617030765141d9000c2c0c40c030948200440781501c2418422001c403a00300000c0c410a014095078007031616a80d03031088802c1400300f840c02000c24040000441d0740801c50390071000030014010300352210001c14040c000000d50141d400c120707000d030131144411400d00c28414144001140d1510003020816200c044a0b914410362041006000c0c4010040f0344290098203c5800c0b160a8080f402c44d5000c00500c0000070194400d101c5a0380030001d0000c2d4410740700d0300c40c0000307128036041c010502040e4003801030002d500c000c00c0b02c02070400d54442d5002d00328181c0024031240c2d113014107501080c01c5403010f000042c1c01402d1046415403604109400c28010708583c0b400140040e000c01c11801c83e4020034081900301500e12429400e26003c5400103405003200a00881240b4110f0300c445640240f070620f005d000d9424040b414481c180d0600c56988030b0103c05203840d02e4801030364100310003041809c00740c65 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138812814 1250 138811564 138811597
    0x1709031b010204090f0905060a2901050d0e060603070602011e0509010f09060506180c040905061f0503070f08060307150201060f03060515120c04020d0b09101401050406050f 76
    0x104504d0b14007a81c2500300082100184d00409801d1180c1024801002c08109505003081d403129495044021491680c00e170000a80071105070004031000c1c82500c00020006081142e411031441000c10f04501502e4210211940240d844d1004d03801c0e2103901502844401c04000b030039100e8a0243c1001d503100c51560b00001e10b85905209203804c5450000050f281641d4410070040b007810300e800400004403002400550030b2400000e007480742c5c480c60044100c82d64440003c90940e031a5480c0241e1102d8004541107412147c040004049410890f0300388005200951202903040c028402107010300390240140c10180e040003400305408008440311800c66580b020001030701c400941e1100b01841c8203135004511810704050390129042500700c41c511620300314100c050028400202d482c29680203440140c0c072020824850002403070201c2c00d05170013000220800c4014003440001c0000e0320091009021a0f002807030044a440c0514020003020400c10411801c40e000500c0180c200071601c0651038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138814064 1250 138812814 138812819
    0x30f0303070c1e03080609151c06150e063f100f09060608030a091206020d240f0f090f0b060406050c0601050d08040b031806161709031b010204 63
    0xb04038211401083d000104c402c0d090091b00d150030710190741c02410b01ca404422403500c003800604040d0522110f50804464a032081003040995000410340703142001e40340d00c1903552802c0d012504902161480d00c2540907440d61900d000d40352054414241442c600200c04d50030310750320b003010682c00864981c601e218030003405c80030007d540980003c846040601294505e101c1c0f4081055610304d40204009420901c00d104006900802d00da00b200d040740c501c0b0070340180da410460b000b4411583c030000e0f130504180b420404640700600c40003070b404032901440740a698501940e050040c850007000d04201c1c211104002041c02034000c403008517000b510028110700864001002503100341e001101080d030106905242000511091380101010340c1c01c00d03118141c0342d0364000d0f10701c01c81c010078900b0840400495501440070968088462000c82207540344d081003d000040050350b4020300001980d020241c460303000e039240304d60b07015060308402142401004015041e0310681c01000044566090000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138815314 1250 138814064 138814103
    0x905030a0201060f08030c0d0f09030b1003150c05030c09130515180108070603091103010c050c0c0102030705151e1603050f060f010302090d0c030507060905030f0303070c 75
    0x101500c40c140d400005525141c80000b020700c1d0011703400781c0d00c141c0040c8040303000b20b80c0c04520707000b00341034900c0c180240d94a00c4100b40c48502440d00301812200074441002030441075108d12105880c003036021401116101032900d42542c04240c40e840000b141400403c030710b075000b40d016003000e07003000b40400f408205520744801160421120302d40340c0988020b40304810f0412500c42d01c1c880c040711108881c15810b05c1c003c942c0d14410361241c071003055603414805040c000345140c81110700800030000e100e184c103803020081503600000600c56071409038070403024039980004100e0309803943c004082c1c448000903400416070305900038005d0320f5465104440c2002005140000351190b02a20084044142401d03070040403a5001000c2c1a003800005080c40410360b41c00745400f41a600910b400350b550030010010404d6a0a640c9000f171100903822804400c014020400800b924120343c0c4114540ba516400c1503903035080e400201000e50010400f2925240c8030344180c604845c002d0900441070034078a0349 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138816564 1250 138815314 138815317
    0xa030e060c0f01021209070305070315090b070804150b0112180506010e152704031b11041128031b0302120705091e030a06060303050c06100b0306090604090503 70
    0x424910b503940c0000e01311130450401c10f801d5080088100144046801c5688440e030b109014000900103c0c0d01100303480700141140c010001e01980f10000c1c0000c0d0401542c064289d21051340e04460300249807a075510620201d21500a0600050759586010321801c8015070081001d20701d100c9440c0040c0d010030700418020010a4002e2141c00440205860103040314082548442041c500c00c0b0410b41000c0b00e03850b102c0d80203a0008480702070034145900c480c075050719000500101a1100c0b165440c0b20300901c0b59070009805802410344080c80f03640d1450700003d0042c45164205508007000900084000901c44040a258805c500300068001c0180c6c58222008400b1015007002980008034804140d90000f83e042e002446420040e04014405000a401240004540c2c000300300700c80c40c0b000c15540810103145401e030840d6041015585030300380103240f50b000d001888030a10445001c914090034111004086580c0300c400d16095480300e804110070410301030b10482e03000e0340703941c0c1d51000300b0010310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138817814 1250 138816564 138816583
    0x106020307140c011706030a0b100e0a1517030705010f02030a0b0114090d05010b12160f0f05040c020a060609020301060914090406090c0b0c07060801090c020a030e060c 74
    0x1001551102070516003000d81880000d8030701c0c09a04402e03010300d01a40c12140800c042544094000c1c8a641d603c40031a03e880ca03c850050a503400e05801d0009078024030502405036042c11a21002c940d840280c45e00566581225084810300c4600f41000034104041c0001e0828403580d059a10707098058032160300b90703400702c20784042441d400014040d00e501144030305040c4450a08201038022100140c03030710749000f84548240180d003c014020b080140a500c00c070321181c0010704164071449609481583c5003000c104000b00c8031075800000c6048099034a03610210b403000d41d800440030f82001c05010190031404e00002c258400d440d44500050001e01404001e0300d03540900588a62402000034200b81040d40001280035040e0394010407511600358031071340144c102d0400304502032070b0302c0c0201600219500614084501041d140400354020850030103c5440e582c4800560340c0b01c45184080b90741c08003640016a004030050320000f4080c1340000c0303003c00000c210504140e50b44c00304608010546 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138819064 1250 138817814 138817817
    0x1205030613020418060801091502031e0406091109010b0301090903030b0916020d030209010e0d022403070306060e011d01050c01150801180c0905090a0f03020109020111030315060c070503060106 85
    0x56001d0362907400c880c07145e14018800c600003400701000c16103d4070719050308501c429018540000009a44640509020810400f840703c4440a4642820550000c0c186c40c0f00403981407031400e0441c141440c0043d5118182d90203854403524613441c3c6020840100200b2030110207064480c145410302e82d944100091069078010101d50003d80754010080c10107a4061560040c18414020b09881e1b0f60b01c0b107000020f45005490101e40400a400012000410210b8020490800f241c80a119000c00000b0b507006200380d0b2800d004142d100c07001540c0c00f0030036072500c40c00a002d0640c0195500412420307441400d0040c10464602800c1088081c203441d5000c18214941e20394650403c400003003441210110704404403400c219503503c0c0e882a03441c14030382c07146161194448011a81350041400102103040c0e01c03001d4400d01e40c00b6840d0180c0600000c150580c0860300e050401d00784008048212171280251a80420403510b03003104012568000d5100307c103080c400c00b00c0c0401c01d0340b001c0160501a1030395 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 138820314 1250 138819064 138819089
    0xa020d0b0609070504060507140c040903090e060102030f090904060b2805060c0a02061332040509060106230c150c040b030a18050703060e150412050306130204 70
    0x6030042c40030300302000d414401048010441041010741c080e0540f008564000f40d2084442110070026290070f9544008650040c07802020b9020181c21145400803901518212111692401c00580e180d002e60452009640e804202c1c1c5001446e0480d816039006102e804002221203901c00414283c1c000c11081d001c081180c2049071620781e4003401848018070048640600e03065290206503151903941c0b6009000b1079012a1400d0b031179071800b400d000a052004a4404402ca0091004251070414020000300002035100348640d4142801000d10400c6890020403113a442c187c03040b903e4140c03015940502040c603c034005070342a18030300105194032030013000f007840014144800c1900300c03000e4141e031346010040004000c140c02c2c16090307980c032400b0b0f80c00000c1c0c0c10b4103400314218000c000c0c140051140c0502c040100800071954002c3c001107406008a540c0c8500e1171030301500140c01920085c2c01181c1038040442e4051041c001180e2010015100500b82403001b42c0800c160b0708075030412600c0e07080303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 138821564 1250 138820314 138820321
    0x90118050c040b1c170c011b09060305101a0f03040b0402010207170a110406091b090f080a020409030509060301080604110a0621021b0102031905070504090c020a020d0b 74
    0x42030b008607101e2901c102d42c180c00700e1074100100d038a8080751311030007030030454103e281e10030130709500e41518080200300c0004d0024010301200080c071042c1c240804d0f40429401d00022581030701c05d01c103280c4130b0541490214442400c1140b40c00c00c0010310f00030100c144078101b0000d5000d81098010f580502c4c421001045a41424800a820801140c0203d804030390791031030b41c406e120b000060b00b1000e650000c2881c100c00b0041c1e004500944520b4110350802418102142c4007103010580e4514600d849507200400182c6952110f08120010310800307206030300c040c001102615096025418407440390034180d180409074008030360640c01c00d90004100e500260200700c00d20042d4441090151002c6800b016018200040030303001503040500c20b0045460390042d01ca280140d60304840c050901c41e078282e100035500825250103540100c075400b0003855000328080c07000c0c0160040c2c034065080342d250542890b00f40300c141001040350605000c2144141d12003280940c9480c030100f503485010b0491070080e0714 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 138822814 1250 138821564 138821569
    0x15060d1a030d090f0812031f0b0403050f060c030903040b0906040504050c0a0f0f0504090c020c1e120a0203030a12090c12120207051c0c030618150b0102030a08090118050c 75
    0x10082d03010001d0b94128486c401c03441001c000482e40e00c42600381e03880d408081008003040d840c2a198100e500440030006010082c000009002c0108014034400c40b042591100340c18061800140c451141130742c130500062040030300d250054404040080d100c02d0500382d40f503000800340c2e02c3c140d80e1030001e200000b0700071401c554004a100555001d5003004440880d1024004001f88917034856944900c2e075a46925842e00c0c0300780441c2905490040c219801c004002200020f403d0407140c0c180d208030040e1010308c1d88440c020036140555600180034504000b90350809842c03ca0990400d14405682c4060303103000503034010600790203003420b407290a4544100345421000441507000000940d4003c0a0401044c0e898043c100c41806e241c03440040b480c0b51034030b450040c1301c10540004000301d00f003040424801c10b540407013500443c003d44070b004047e414074241d20300b00c500300400b581c010381042003030810203801101010703000607403040002941d030101003055002038551541140c1d10f4022044034412803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 138824064 1250 138822814 138822839
    0x6031202060907030206040e06041806020a031401150807020f010f02030118051302060c010207081602030c0a030809150729061207051002030c0a0b060915060d1a030d09 74
    0x141d10800403e403042c01d42e0002910b0703000f180319a080303119a5400258041d15603410090210100706070325040e40d000f40c60000069000303403185a00181c0340610f00a46501c80f214020704076010121954403140701c0c0700088490010081c00001944a0000b000e01784907024401c1c600801c0400303c3c01610795042c490f03040c40c0c000e078248004003114100400d0241612196203685181581240e039a9a1003140c0490340e40a4014030380e002d4210100818042100c0b5a01c00c0542e000500c02c406a900c4060200c00b0003039409480d00015048035030500c141419810008000c0c52072012041c0e5880c14000280e0340e504082c1c1800d05a40e186007201c0d5600c20703d07004100c1d8100e070001412104441d00040c83c40400f80e4524991203900e21902c0c1e00004e55071014000e0048440f240301c03180c10740d902a9904d0504586141c03003030740c1c6240140d165000045001154040842e12544004c2c1814a030242d030300c3c0480c3c0030b8401071103a4803e043c0c5107265084a0f550030481e000070718907151a9607111030b11303110341d5401c0d0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 138825314 1250 138824064 138824071
    0x80c1b01031a091b0705030d0501060c1a06030a020a0602030a080114010210051302060403030206160503070c2405150301060803040303211415040b0307030b0105010c0311010603120206 81
    0x1410b0810b440da103000c000210420808010944500c00c1659a502d071102103a05101d12110303a0100005200c024001c000c4010084581031207018030499980c0d40c1c08a41d100b900b0070024042c56418818541c100072030358041d541010000b02180c1d2642503a0f000251800a030350b0000340075a00025500741c075030f90000149401030001d070002c0015070000c000040d46404175008013144590b6107200041c602020150300c180754a4003e00b040d40c48513181c0c64069900c0c001a201405002c04103000081e40504c98001c50f8800d030802e80d240440c1d080b070303aa1040c00e200e580d000d83d0704641e41c11000800300d49940f4800c542c03040c2c0000046009a00340300040c503007150034a800510369a0020402880401d41107446507407580e00002403c401d03003903901c02d14802850740026811026402206220720140070b4014421406402c44007000341c0c2110720100359842c40c55120003000c0124013001009150f01070002c01c821070380a401e080c0000120780b0780300b908441c0a9001100d4294a2402c1d40020766410020382d070b0b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 138826564 1250 138825314 138825317
    0x40b130509150a091d0706030203010612060f0302010c020301090501090b060f151213060507080601030b0402090a051201020c010e030705070605250204020f182716020a080c1b01 78
    0x1180c05101c40801c08403076040c01070418454550307110810b17885150502040c1c04601e1030030350304078588404008010758400e11641e0300189a403000003038050f407244a400115002c91301c0b251441491a80103440070708500e03100741c0e810f550307800104001c26000c0c00750842140c0700344e5400311701d40703428410013442a944085543c051410f10100c030100000607000c90380071042090000a1603910b003a007220803d1082c00300100000c2c02d05003440200e5410101150148000362400c2c00400309110600040380030300045c03564450f12180e010801030034a240c40e02200c00700349002600e0031480e10741040c04d44046448070515a800003400c202072040501090010305041d2819a103407808005c1d40350784120203028007480b04d041113804a01195115030440e60001410003400d44c842100e40500b0301d601c040c0000d4180281001c03484c0213010703280300028080f802d195041c0808035483d2003920078200700034468001d0540c840c0b00701c1a004280581c01500032020844024134055940810390000070b100d0000f06070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 138827814 1250 138826564 138826591
    0x102010c110714030c030f0609071203120b01050c07080c18070903170d32093004030803100504110409020c10020a2a030c020d0503040b130509 63
    0x240c1d01ca07404103014040702c00d0032084200d80341001000a0400407411403a0b075052040c880e01110812010404601c035441640903107c2e0140d440c0c04030f44496014000c0100007400290009000c54810b40c0081c00703020062600307a08010b06201494980130154104d03c0880c0d100c0c072407880e814500f100c42c01414825416128a050901e840050400f504500006040744600510381958100d41e0702034400c15109807000f0302c0940010081c40c9000618601c04002a03a440d9410a0300306044e070100600909440c002050448c0c03041c542c140c0d03500172014101342600d80c83c803410b0502c9010a006080954000c00c2840d40e0f900f440d41d60358010b0b204a5200c00d0243e401d10001d08400f00300c1000383c4007212110780000d80d0382c18a1a042d80d05001180710b01c82e024030f10100f0240140796000ca1000e42008610713040c01203048541c021503014503480c850007000124086512401401e0802c110b02102d4450001c407814140c807004107911075086080d201da5004140032042240745450046641c00260b544000f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 138829064 1250 138827814 138827837
    0x1b2416140106031104110306060d020c060a05090f070608070c03050d0504050303010f240503070c020d1103120418020f071a04021e151813060602060f010f03030c0309050405040c03020102010c 84
    0x702d10307001c02010f1a200c9c10001c21107414202e001d030101c07150140b68100342d4441c3d03d04004940024101a40c4031640351280071002d001680300040e425007580c0b10394903600855035598008884840c000441102003000a02c0b0440c51041d45000e00f034091072080014507101e40c10401c11746030b0080907501030031680a13401d0280200600b00c2c182c000403500346191280d40c035550520140c3d080c07100600029004520807404105000700a40310380d40101040701514007150341907441d8246405540964401010000001c030074807142e5030300500c0e084e040421082e042c45565284c45040d00b03040c88041002403407640070401180b501119001080c40b507000ea4203030800c000808282c2c0202c0380040103245200c0003601e0a046181690341d41c074500002020404003415000f090740103000248102e8000d40701e00b1300400c00f01c4041c0a0904c1c103a40b1441d840d20200d030716540b4211003000304000143c1c01e0245c0c0c05004100758880d03019443c41580907800704610b1903c2e500c0024210380c90007240604004281128 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 138830314 1250 138829064 138829091
    0x40306020c061b040603020d2d0c0504030203071701201914180f0628020d02250b0408011a041505040504080f07051b2416140106031104 60
    0x2038070142c0d40c031460010386541c4040705408c000d041040d00c4d10807200240f22200310805180c484044280c00c0800e0034084032814a01c02d413903e01407404025810b40100e0402d018940f0503030a022841410b03000041036a54558131445207004150414940556001a03810410f410200e10f09210402e02e14205e1020003490800d00b185025030103a0f402d60142040503034160ba507588812840c00b0a00904aa984110891520400300e10b03c0c10210a005031280c403001c0140d002084c6107401c000035030090aa00e04962031031264158400804501210040d42e0210b90440e46c00080e1000c1d01108000040e213508032010400c800e4001e00e0710074421410b10942c110522101c20514044500580740400c8688443c0780c685418014000509420b0b030f00400c1c50030520000165042940c640c40c02c400e1020800d100901185089040d00340780a0004003a0105c8100014401002c1041c56500c8103a20310655a0342c4201d080480102d0052a82d1181401c1c01484013180c0c1003481000206c0c3c0c00c01403424100344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 138831564 1250 138830314 138830317
    0xb04060f030e12030c040e0c0403020a15020a050a08040e0a061401031104081504020907020102071a0717040602040617060f06130b0418051302030601032303040306020c061b 76
    0x8624201612088803070035050040201c3d0070072090500016880c0d00d42045028803581045c410f0701c41002e0038002041d02c000e80f08040f10305880d0060324901d810783c149903800701c100d4075028250045100d074010100109a0502102c4c1c1407920510032656075614000e41c0d10b55002d030280c4001d11261809d2002c20007140b0190342440c8018007800d0100718140040c20789180b0380030356441890305010711208148000075101035076108034822141540c807030f1038809049080340540f0000030242c034003441d0078907200c10591b01065840344403481c100144068186a0f810001020b980c2200d070190049003d012941d0850440c1c405070302da50304c85c0c00c01c501e03041000421780d0700c18203041401018005100366a000c48290004040c2c550981069540c0d941c542440b105042080400c2c0d84c61860301021031458000302a040c0840340e00103008005607429501c43c031451000702c00c0e00e140140f50b509a690700408040c0040c1c40114044d0303c0040e00c0e000007404107428420024090390f03507607541d981c2450b000040c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 138832814 1250 138831564 138831587
    0xc03010302010314130b0604090605010e01050406060809190c03141c02011503061a090709030b0c030c030a1a1c0606060e09070f03180b1509192003040f0302070b0406 73
    0x2006c2d21460b80740c4a0114000704200c0c1c80290106d4140000805e080f003901e01d8075412900140c40030401240d031600d0445038110b054400c5000354220040c8900a0030007405c1c1558981e00442907c030019580b030b42c400700039009402441456400001d45c2400c85002c20054003030f4a10180024858940050f002d000788001d2030000030211a900d000000c40c1d03c0c400d5140190309800075100005c4c0d0300b021340010300214072610086401209050000344105a1007003a40d0041190713944460441e10741010720005004611018088200b4085000c851a6144901440c040000140c018100c0c911801c280342507407807079003001c0240300d0080c101602c1a1100440d07198000200e2901c4004041c0840c0220050401511444480c200c840075400500021184840c090596508910300d200756210034000c002c1c4c0115180035000c5000e241d51a00311407a6004a01c201d16141c1c01c03041000302e40c0c903005541c0d42054a00742c840c6034001e68030804042e01007242002804440d03101904152074900d00508400c00724 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 138834064 1250 138832814 138832823
    0x608030f03100305071d07020c1f021002040603022203050613050705060a031413081603020a0609061506020a050c1c050604061e0e071a0c01050c0301030201031413 72
    0xc001140c00d0b2200c04400701940c2c0c41002e951a580e65100f07440c0030b426400d2035418566801030702250300715000155810380306001403c10111200b50515107200d0900c018001400e41c0102c0100e04c0540600b480248060100e50300c0c010b8855104900e01080d4880d010031580f41d1440d0940c0a2011400000e809980710098001560101c404c40c80c0c41401c02c40030354882900960b002c200c9214198054211104600c0d00d010748600740e955604d010710110b000500701414a02c030800034880352644000300749043c54000d00459080203000e54540742101e02224042e102c003691003044c0040d03880c429131504000c003080e10040221038031a0b101c00c2e44603095050b403e4401e808110812502c0301115400721385254100094891b07515282c106071020b046041e0030075159000c0c5000e892143c404500c5020101080d02004010090408506040040014042c00300a9900344405207001030240240c510030303588505c1180d02d9514510024095801100d04420f2040c83c4408104c04035900848408005400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 138835314 1250 138834064 138834067
    0x309060c07080d06060f1106040c06030c0e09010902120c04030c090b010c15050105030705101e02030906070c0501020114130b060f0a060e090901060602060c070c0b07060b0406090608030f 82
    0x40b442c080e6441d1140c0700f601e0780300318105140021803540101d00c5a00d0300e415a00c42c2e1038000c044c041c103552151400c0310300034030168810000b1703c80180300c1d511801514001d81490556030003c00b00040d0386150990041c0b41d4550001703040021001d0032500c07a50000c0500782c10608160071561052000d80d06e5000c1e000071956100d0000c922070b0310440c007100c0c0752a04909403030910100580c041b4003030442401038034086d1180a20016003402d00d4a12190100400e0791003c4000f034803010703050342d90600c24800e1000c51000f40311002c1959645001800d0b2a849840075141d861728100000e07003511040103010300e2040607007003004000c01001d42c640e4012980803801c03041a03070700c0800081d030008074051459080809105c0c0880c045030800203002c9614011201040395980b000c01071426148103008400058100c4000b1030100b4503000d01904040744150603010216886100c03080250b00808403d55046880385c030b882e1001c1c245480f602c0050084d0307010521001e820843d0785a940d115400c82c038003010a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 138836564 1250 138835314 138835327
    0x1060f05091804120e030a0206090307030203160e060a031203181403070303050c0a0c0201140f0304060203150301141f030213061a0910050a020a051c0905060309060c 73
    0x462021a0300d4064010084a0207081c800100500b0420440d8102c8000f01d015106500322402018036580803240203004040314846a82400b070203401c0041c0c901e425114104000c001607600f80101c6e0414100b007149010000d180c28101d860705280504658003520f43d0503401d0002c01c00141601c80050245d05010507004007680d05c02e8205015480003030402c443e800301d89250110044028814140a6035050015840b0f040c0d805d0748038803490403508045000814898015400741d0845d07040040040802402d10340b403c00814203c1e4000c487c107d4920b1b44c00400c002020441c9610070204d03d00940003000300300c6015550384103c18000e85495015000060a41618070b49426002c2c0615405400c40010b00101c074412800307000d00b8014451100c14030a01c0444410400040c1c3d190444020a1452103952621090758190300100e0f01100b180203092020012960400520702945142c0c090349001ca519401e0061150480350805407241e8001c0050241d43c44001030302c2a049290001c901e681c800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 138837814 1250 138836564 138836567
    0x70809040603050c03070b040f093303031704020315060409020a0905010509010e0c0d020a0302070b0702060906070309110f19090207021c210302091905030d030501080601060f 77
    0x92221116445030900d5008002c000001c1680d2902990540465284a4031540104254017035409000c0042c0640c41c004c101041c03280e00101384841c191040710380000b01c04224411804112600c80c50030411001c0c081003050fa05c240901940214150301c441942000e9001039103500c80440b1011035910042d000c99102d07655503024926859001749039501c20b0340d0b51000c5402400c424458644180490303800040c442000515851103501d031100c07014641011556810000d4200000b400d01f0168244039a0001403e244925805002c494008101c140744c400c0302507213070000003085a0101030900c03403210001041608514a858021a10f12081d001e4100c04200c1d81690818a103605c443c504000082070b05680d4000c0101500076241000ca120107001044000300b90050002d12070340245504684094802064560040380b81c03501510b407080900020300e441c01100d081e1810b134800d0702d078200518030b001c005241c4a0072071801c043c0403547c917080e070968842505110348400e002481d42c903041480d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 138839064 1250 138837814 138837817
    0xd08040314041d06030c01050f0703120f09020406050f010c0201110c0a0608010e130f0f0215180301050f0f060108070504030516150c0503030601030b060909010303020619050403140708 81
    0x2840d250480079195650341203010b00041842034900b00d00914840444c545040100d12050081d8068440700e02c0d281c9450320b08c400c180d10244040d801c0103940c212544495400d40160042080c0c0f10704d010488108500401040707407103d500c86d03072046100c180207005990308000092007143c0c090070f002007546104c1490500f4041441a038035840010010040f802c103401047d1039041e108070303542c8601151f40350183c03491243d8100c20086c110540302c3d191840000e004441d50201c0a1000d80310040c8d18107803046d1310000f50012140a40103000300c80c0c00b104a8102480340c10342c40115844030039410706002c044102031640c09800c407030401a17010009000c29004200700c80c025a440021103080811001d00d03041e44130b50710300803206003032510390100c0c010510030603c540c105e58010014510f59220907005600030225190344540088003441107001d40d030b584604e140c0c000c602a401502482c50b00404801c480502c000110491601d441d041c000480e9020415510522020050a5451441c1d0a10f8844c9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 138840314 1250 138839064 138839087
    0x1091401090e100611030705101107021207150e090406094419051309020310030303060e04110103050601050c0a030c03020601060912110a08030d150b0901020d080403 73
    0x900380ba8000c0c04040c000010060f001c43c0c05030b907541c110048003c4003c585074858402d01400b03941c4180158004030000358003055403050300160750b518002840e03003c61001c0c101007031002d0301da80004400301b041107200075008590b05282d01d0b00c000d240b4401c1001030441100644003402d0581d851100504100c508600505255480103509a10358041d5031412946a01d1000f00410b1203200c401004405c14007006a400700c28000e140200300c0c44001808a52a4001e07030030642201484031000210301c01e581c0300860041c511514075078151401c500b00641560710030741c0500541d1660004120105007906d150302101682489c0104507601c030b0b0b00040f14580524401c904042c01540200d40425406c890103080c05403081e020740e041681e07104401d882c00c45c40c0d0f2040100001e03100e0420000111210105c41c400907005003122089a114a001803035504849140d01c07001e5a29800c031a8100c0c5003c09800c001d06003403210514003045000000d4991403403064207414000d51070007080415001d882800c91 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 138841564 1250 138840314 138840329
    0x70f050c09011202040b06090d060e1f020409060f030b1b070b0c030915010f0e10080d09140d02010e0603090709050732090607050c030307031101050709050109140109 73
    0x60550b140d483d40c840310812900100d00c5180341100c000c41a00f820f5092300c01c1d5140c0244006001c0c1e07002c2e20f512003c0c0c03009010000700c500a06c1091140345004444204160300c0144005072030b1802d158005046503040e810401544590b00d03010400107003d41c80403039002800c40c2a507140040144a09545801141c000400c00786103a410840400c0007403002e14800e42c0d816013218540d031701180c10b00768008020b006445000c0c0714144180003408071f0503440c54008092840441d243d99940d010703d401c0c800454219400901000020004441c46004941d045d882c1200c42103107640e12907002902c4c17900310341d5640c1c0c011100400081c0d04064240000801407004600a00c442e203019500200603192110722980c9111851000c801520003ca4011700d041032140b1159107082034a03410045a900310440480d034900c940a50302009481c240301914109100761034201400700010102c900b91000101040104038601d507040007244e074041314200840303000242142c141050000100e6190807107400001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 138842814 1250 138841564 138841579
    0x71403160602091306081902150c01092901060c0206190f11060408040603360314120a0c1701120b0f13030f0903050d0801150f0203070f050c 62
    0xa104040d00100040305086804480790040c001c2c4d110b003200c40c1800341e0100c551001d03ea0426000031302c40c043c6c4d05240018080001c034440a40c2c0d40641c0d034014007072600141d4403600b4500c10081d1034403900340320710340d0203d5034451003000e00010640c03010140f04540030416602400c5066455100440d10341100e00000441480304508010300b010070341103104030004040c988083c800340000300c0c3c0d1300d00170365000c00e6280c502032503c0340c2180a05510b1111000074441030411240c4041400802c0c00054808842031581c8a000c4c100a003584080c11411901094108000712942000d030307160076402035141c02c0c00a01c1c80003d40044a100e5244101280c004440383c00100300600030405d1602c10b24803442e20709445503503412410407030240070b42c1c00c403800085041001002030300600c502c4403464968a40202451365949826190400842981c40400c180307a0051002c42241844034041c0045030800c80249001168020f40d24030030301038040c0c01e80c0909070740041082824070000209290042412 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 138844064 1250 138842814 138842857
    0x408031f120615080f0601030f06021207020616051216020f0f07080706030b06030f0c0f160605060102010b0d260a09060e01020106030209040f0311010f061409010b071403 75
    0x128000e09549030070421181282c44000340c4c41d0710028414543e042404040c01090740f17140d4a003880c2c0e00020f20211134081e001c1c001c00014150440f11988070380815801421141840c14030b02d1218103103030342d10008006042081480d6520039400203900700e6092501c6060861100034103d09003141c6103280e089501603180c0d07580d04071000003a10016608803106540940d9690f040c01c0d822036440462158102c1c40a00c002a50f41d200c003684154410541d007592803a042241c8005580c51740004003900b0142404410303041448490b00ca0342c0d0b8010802e0000b08070000400c00050306240e01c1c808001c15103046d03142c402000843d0000d4011404062010f240c0d1200000744001c0c0c51042980208400143c5640d800c02d00c2d9841400303001c08894001d450082d05803190348400f02e41b007900d8401a0300b48510044020003514013403280040da9001020f00240710b0341041d2601d001924200c0085104a2400303005001c154442000c07205a41d0380160421150030b64004594214000c907052142c00403195400d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 138845314 1250 138844064 138844073
    0x21f06050109050301140601110708060f01030b060906030c1302070b070503010e0702010618111201060810050103050c09090414060106050d0b06190e03011503060b0102010509060408031f12 83
    0x609884003600d8100e403594464062500b244c481481c080b414140c5a00800c4595020300e0400c00c40c1038102c026243c206813140344440c94041d007a9141012001204010002c0c0035141030020b0700b003a0100d5109030603007428000a81d844000c0d0703212912600710351005101c540c01d540d04440440d5406035400b41d1600d00070380c01400325002482001071083c0d5400001d210103106201d62003e40e0440c80c2143e40c2c1000a9a03490010254050002103103001008119101c036000162180208015520300c129841e2210798074179205c2c80c60b0b001a0600d030914041c0122000107200742c031484081600c01d508d07a5034a41c1007201a5100070b03020344055008501c00421a5648440181100c4034105018000402ca41003440210300c1510400380c410800c88000b021034600c0b86401100b41280100049062040d141d01c40310030108690040364080c0c2d4403001032906580a0045039030002082e005040546025121603c607440001e089801a00e003080c0304070b8029003100c012502401c050100e10342c03544c41c246003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 138846564 1250 138845314 138845321
    0xb06041d01210f080a090b03090f01060b090d14030405091303020601060f050a0305070504090f140a020717070c0b0a0302070308060a060f081306320402180601021f 72
    0xb94850b01050b0407494000c1000265842d10103540f114030800c00080e2610b0b03849854000003007030401c2001d070b40c900142140c9400e0195014045600c06010201003514178942110704a50114402c1d4801707100d212070654500d41d149421940202c4600d01d00086004603604521443e0081707907114000209101c8103030b00c1d600c00072110714801d4003241c0851342c84101c1511003494145442001520403c004800306100ea0002d0b80c210410341020307410103031624003400c1039400c0c004c0020700303031a40c85801d0303070710882c030350b043c058000d441e00720214500f20320350320381d440c0d0b41c0800704402900c0d107000104001044201c200400060042080f51a21884081d80080285d4052078094001a00300004180300303280200148045a01c2034980183d0512021800d5580300e41c01081d2030350542c04155020003140142c01201d030301180d6082c1700701c00c144448a8007401c0c035038180c0a080d0000c40c52000c10006840d51041d51607562150780c4800f042e0350b40c140c0100e2911120800e04026020710802c0e02062901c0d640 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 138847814 1250 138846564 138846569
    0x302070c03060e1e01020405060a0e0102100c02030705070b0307080402101209080d0c0806010516030c05070608090f010203072313030804090c020f030304060923070603060b1206040b06041d01 84
    0x112031342807210090440ca8240e00680c06215440b980801000c4000c600980e800081e00d103060040d594aa170f09001d00c5d0040325010741c480b0016070000140a0104402441440c002d80360590030a03055041446004040a40013000240a03202c0f0300040c0d000c0501030282e05500078035406060258541500e001c1c80903420201d20180701506100f140503003e40585d080d6480b40344183e44e00c600307000c0382207201d100c803005209054041c041c00b04807e602042d8148034240251145031940c84803418458802854044000c1603054075074810310a211126601906082c10a5184403040c0e80c14002400500114810b1900102078020003010000400c080440644216102948100482c0070844021798451144c0c00c1b124449030000c1000a00090342030344041d600382e002c4ca000d1342c030110001d4511204003c4a1512000303980c4050400c10071640c0c1802508081c103801000c440c180b01c000302420f1141040640140d215588031681401d154481600382c500400441031b10f0606202d00500f0400c40d4842030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 138848920 1106 138847814 138847843
    0x60609061206090906010305031e041203020a06050a02040b0f0705071a030a110405060711010210061d070e0303040303050d02070602040e150901080d0302070c03060e 73
    0x18003904403020305030280745803401e00344200300084100814011150340002d005100065010055130309000e88610036900003161080216034034002d5811501c02c1c0014001c203542455400180072122a0190208109507220714108a06a106031301521030000c0040040d03904030580b040c001c20386140a0021f072380709103440c3c01809100c5c481034064143c82d010301000348505a040c0d841000340102d41074400b98039161a01c004210540110503000d40740445140481c40e081e4024000070280c00750400d81044002e4888002c0400c42d02c60b0708000c0c00c07400c0094002000c0b68002e640d00e481c40310004006500b024034590b004c4807140e0060b08000c545980a01000740015841d0014001520130b2081d81c080c54904494501401d1804020043c8594000e00040020f4140450641041d0f6501d16015a031091305040c0b000090040768070040056182503a201d002420210700304100305040d = true := by decide +kernel

theorem cover : BRFrame.Cov 138669064 138848920 := by
  have h0 := BRFrame.cov_init 138669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 138669064 ≤ n) (h2 : n < 138848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
