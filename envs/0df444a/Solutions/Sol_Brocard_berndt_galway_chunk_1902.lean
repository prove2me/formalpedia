-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1902
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:05:49.670649+00:00
-- url     : https://prove2.me/submissions/717cbb50-5545-44ce-bba0-379b88200aa9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 341906474 ≤ n < 342086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 341907724 1250 341906474 341906483
    0x20703090e130212011b2006070306091415062809061b12080702010b060f0711061c0506060405030f01061707120f032a0203060610080708040512040b07 67
    0x409004c12156007211444120340f4280d00003188500b500c13910841c0c1d04451501070107806200c1c207100c100c1c0c0901d0700310201c0b20130000a071545014041c4039581d02075551070140d0b00038404c02a041900c03050a20034120742081e8000c01e400b040a042607030a145450300042218091502544807005000780149a5800741d02c02140c180042c0710b078036003c1d20303101d040c81680102c4410700d42c1c204010100ca015102421034030031992606014051aa21800140300c400c07550032040e540d9114614002e014006442c0085104510a000030903001060003800072150b403400c3c03c002030365500d203800900b290151307410068240c4610580d021542c02c0550202c0244d40300403810702043c01d01d8241c260780d0740c00c441c054070515030001403d280c001103040d1000001144241402c1c8107950348020b0100602820000700115244445e032404250b080038400c40b43c02c110259100c40e0041e20404010b00843d0003c4c0003402048034020004041c4801400344400781c413200e042035550f45079a21500c44071030300a00010765 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 341908974 1250 341907724 341907739
    0x2090406050f09071d100c05060703020406080c030c040335040807032303160606050604150c1a0702010b0a24081306020307050a0e040c080a020703090e1302 69
    0x340a182182c00920300728402484419942d451881c12140301d00c50440a1701d016041d10400c82195030303181c080e400c19500c240d07200c2c0501a2a03081061400101601000a2501c104020301041d544080c0f07142d40040114801580c90b243d90b40c1d480000d205d01d84c8013900200301e8480c40741081c10300d915100d003048048190160034841d0990039900ca40b003107116810071544441c0c8104000f8a5069004d696400c81a039032106400d000008507066901c10601180102000e244000030445588140b00c054403040c0c81c5103041c00d050440740c2e01c18588404d40c010500941c041c0c038030200100313068040c0c0900300b252040030040c03c1650000c1d001e444070140303c83c401c103000400424815108c546412880da140005490003101c0c42001344c61070310000c2c0000810b0300e0003012800c08544035000450264641c1d5030f0391503403940c040384020940790107080618810b50821000c2c249003640302000c10780060392041e005a0342c14581c034094a401005500056240707090404200074070a5541c80302000b98020356081 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 341910224 1250 341908974 341908979
    0x1211a1e01050906011b020d14060709030201020703030e0d0c030c14030f0c040b0307080a0302030415050703090504110903010f140705030103050d05093c0102030a080a0b041b020102090406 83
    0x50444440034000c0341c1c2c12543d40d80000300c942d8815032a40c8060031750403400007116905500460641082c3c0350703065030544e95844000baa2200d08102c4113601170a10b160860685085500003501c40c502e905c0040c0c2007084003211103030155244020305028580c065100f4201036500d01d0142c0070f10080f48169400743c00740d4041a00c55003030104980e004101440050100c1410301820803000f0020407034010f4040c4210200444c25200804c00b1192003402500250b07110b80ca800b40700590a2040039100d000c01a040c00b46000080e0020810700c2074690461f40805e1100c2c81e0000c0c404c0380d000e02c6801e00e900d07608008011944000941c05100c01413038021081480d699000c405039120b21081c800200280e20074013140740d03410b200300c0191401410041ca80300c02c0400c84282d0155044c0c0405945429002c1d80d00301200d01222503496098003102800510308000809a014186080042544590680740c07c01c07582c0301c0e40c80d83d1040c00e00c2c0f01c100c0c0c0080405012488001c0c000c3d0400030583d4003075031414501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 341911474 1250 341910224 341910271
    0x201060e0c0406170a0603080307022d06070f030e0109030809060705131503021303060515010f14090d02090c0711090c09061303120e040f060e01211a 66
    0x100c409507400f5449610050b052030084400c88580280b2894800f5a12800407000850401c0103500500c51540140f000c038000b4882410380024994800c00103000e044012070b6090b0002c030305c903035020703509051004084480142c04d0b03000e0324002e00720203200c0d440c00080000301070308a0403a030300078192501241d81c1c5d03940c3c605040d1150304c00c031440e4003c5600c03181820400b0b8050103c003003001c0700e805c0c039004d41801f604011300a004405900212100d42d1550104490310f02c1400c18210110024a0500c80c0e074042d8500251040640185054920200103610411611040a0241003613130140c00c050b2245001030190303510360441041210003200150f010f841901e041980140520906003502d842c21518008000c400e506c18035a00d84280f0140c0f100001040d4130200132a00c04607691100e0410198036000c00040308e03418500c02400301e251402c02c0c0038000d00b1484860544d03040084d00b81c0c0e020941c40e50f5058042004800400801240c021100700c00c901500082c007070301d87d101c0d844041c0000c1111 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 341912724 1250 341911474 341911477
    0xc14010917121b071716110102010b0904120c11030d02030405090705040e0703180b09010b01030b040e0d05070c090227040b030604060506061e0910080405030f0307030209030a030201060e0c 83
    0x50346110582c00d10201005c0f40450301c1e42d40b450f081d000b503100d2805a40d901c0300312504000090130b54074001c1450413007085580a000d0080340450458407070307200d0310b05a0f69080114003031400130410400c60f00500b10400000703286541d08003070001d08070ba10400c1e0800000b940d80d405800b0301c50113080c030f91000c184914020016503090319019184882c3c20790314000205c00820b110846441c1504032510004003044a1284903400b45000d1800440c0410b222400541a20074090005000c0c0f40b800c071441c000785a011816450000862524969a00450400000914241d081014900d200049102d0040048101c05401c0a40000b44680940c55101007000700c8818403a1aa0903030840c074009800100b041c0d0000f40e011000920b124108072441d03c0411600f0150410104013001c001411580303031404030303000a900c040c1d61500002c20f280c150f540540780c1c0100c52040c00d5519010000c83c4100f40a0b07010740d040441d001d402c5806035002410003e010700010700c180c021000d186008240004001c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 341913974 1250 341912724 341912761
    0x50c0901060f050a05090d0c0603051305030405040b040219020606010f03020703120b12010f0501050a080118030804020301140c0d0510081b03240f01090c0c1401091712 74
    0x32a14018082c10340b03019200c65112509000030070604000880007607407070700e00c1c0c82400350003083c00784211424100301504603030000d422a414044403512805c006100002107406a1b10159008510782d003441e00828040e0040030b903518400e59125501810440e400140240719040907a5400310010440400340c040b881100030240019030180300b40310086c5020341041c1007184000e44544c0c2c1c4018600203c42c00c49401054680410340c03030f074004100615106001c4c3c005004c903007000b0007004100740e48610f03507544030740e03002420f1145d200d00040941d54294800b030704000904a41030003900d4101c14030055940134141d84240c20b441c200100e500c000f00c080300741e8292401d5600810f2103401d2076201c002c0364146420340a501d803240885000014500121180141d8280d000c0a1007e080a01e5100300c0501c05811a040c00751606052062240d40840c0038100d040e04804e0741c81e118100d4041050140c5101000035241e100300d91031072070303042c40440c004200301d160414108509486040107078007004680e0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 341915224 1250 341913974 341913977
    0x40506070503191a030601091514092a0a090501270501120e010c050408070614070803063001060503070305121b100c110a0317070212070f050c090106 66
    0x141001005a00c5a1300041c01d95510301205561424004006890007000340c028000313217074032801d86046121030404030001070081c5490107040c40300941c3c080384285100600456025001c440700b03d0b0b0b03020a003940c1980017415156400c1c0e0301d00c41081b01518100c8507219a9001031542031007038840c1c4c105011214103612078842d800c11801e1905004444052009800c843e0090f90340940003075080b000d01c04c940d004503d07500c1d00c0361503620b0411101e041070b2182e8080b0301031110816030001190490b03070440386816813154005460340c0711100400d944960380d18462038210001a410880344c0c0746070b8a06054101000e0080c050305468100b807540b5001c02c1e01c0000c146501c55400320f031801c1c00140281409601240c40c0755918607940443c58a0700e504081c003610b4190359600700d000e050b81d000d10741100c10b009440082661b80b505903002400019900e50700e180b6041e0b59408036008502c207101501107060140d1140342c542c600e0f07080c28410703140c001c0022503151088803080c4a03035090401c00389041b40c405 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 341916474 1250 341915224 341915251
    0x150a0f151d0f0f13060e0f07050f12070507051b130b060f0d0e16080105150d03030e01110708030a0b040507021b0a051002011a0609061b0102070614040506070503 71
    0x160140305511504602c003603440555071a452030001300d5441071200a2407020101002c6090569100a0030720005d004a0100041006040d0000401101b2500ca0031001000205185c1c0c0d0240e089620f4010950010418090100010141c44902013004480d400c21122005510f0382d04000600311039458035803540011061080e884e422000b04003428400564010226000381c43c01116402d01000d0785808030010221041401a00c409201e81030727101c160054010f0100d0312450010350200300d4410010101500d071034032010505000e41258103981360036410203440c0c0010781b0705205079400454413039621514080014280d46000e0045a000c0c0e4084e03000741001600d02e145081e25128600d1183c1d401559010700002e498440d8001b29810b4503407130b800041c82c0750711070244084418426070554400c0760f0030703c50000c01c2e130758000c102c9030348803601110308681d403e00b603c08902901480d000501030520702303004c1d0010403c000218500c200d210380e00341c0d491650f4004060321140030a80e4584d899114 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 341917724 1250 341916474 341916499
    0x91015060509040204050409050d08070318020904021f0e0102121e0309030702090c0705061302010509010f1806050705060721050a0b030f160e01050603150a0f151d 72
    0x65005064100014001500d130944406c00304003590300c081001c032030560004c020300c4032856004103517641005080c5020b03c400341100c00c1480102012040180c4100401e8000c601103596007000851408480a118902c1c1c00481c5009000104071800c0c240c09030203100d07601e002d0001c0840c00c075006000d00182001c030030a130503400b10409410081c06001217100401c510300241c0c0d00d2a41d1140300d586290209079844e41d8600c0c15504100029003105082104000d1020040c0e03000b109592054100b843c1050004090a84c11202c0801e84c80c0417582030a111200807460325170010003030444c1805081201c0082d210040c00311a8030f040c06643c101c04004401032502411a80c0d045180c0003e1100030201c0c1011b0079100003803c0600a044010b0305a10500069007401c910200d040014000500814515072424011846c5840010445542009411001b2405039100003184c0003806070580303044092030304d0b100c509403000010713070082c8049802940c0d8840000d03801d1000c0b019401028007003511101c0e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 341918974 1250 341917724 341917727
    0x2c01090504140f0105060a090212010308031302090411011404060c030c0204091e0215090105030c0304170703091d1e04060209040f05060411030601020a030c0f0f05030309101506 78
    0x58050401c403801c45002034200c070501c004110200440b403c000002a00e424120104038401d83c00b903002d004003e005000c00148200207030789042c1141d4112988a507203581d150407140c80d08041003002540b10324600d081c0010302541c1660914501d0342030303c941c102182c010080011a00952043c800041c4000e156140002d00c5490000c81aa102a0011840500b159500440d040c0e64140e282e18030050201150207510380805110746c408000441a490040ba41e40020a40d10008198084000c0008085070070054407080090350490101c103011340311481031070b000305080c0e00c9103c0e01d8074556134079101c0c0d148903800003e03141c019188501c003a507903018100c54024803600d00a00036a5000d9003405560a2130b00e0760f001e03464144e500751034009850314200b410417040355005015411203140600c10082e0990300082c4465070711740c0504012910b59092b10f0425001c0000d42c00061014082c03000210070050000003441c0100102e406585d4a140c0c040b088000b04c500e01080640000f81115041100030b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 341920224 1250 341918974 341918981
    0x3350412111c0c0803011e0905060d020616080408030a020709180213060b180114030403090b03100b070b010503150c0d020c0a05010912170606030106030b03010e0607092c0109 77
    0x2c100c81c01c00c184014260340765950203420903809191a884115540581d0512901c40d002c098001d02004001da404e10901140400290410003805190300140001524880d0741c00e004d88240d20104050340d440e29240d41d40d88039002943c00c0e0001d4800d042000c180b98a06014a1046070b0750315448215503a41602081502007500000c061079558641010a00c810300600400403503d180203059240d2581a000400c0c00384400b603207044a01080c0107000029034001450030440d42d07208200341d2207803100442030341301c401c2035404600551800a540410040c05450890403100f040303054440702c0910780004986100115010084010304100d0b00001410640c081d01ea407201040c111a503619031690389508440443c101650b0003c0c400d2141c41030150b02121000506070080e6001c030301c41c00c0241c003103184c6000c1030069006040d03d488881c500e80e1000d43c4aa101d51418038222009802c0044003d0804e040900482e8000c1610b88459411a110600403180c8520200c2c41c2e030882740e29120321740008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 341921474 1250 341920224 341920273
    0x2100309020409170a0212031501030908040906030b010306060501110606060c160e150d200414131203020a020303040615080604050d0801120f0335041211 68
    0x954418440f4041364403a410320561448524500b50f86544690001c0d01c2d211070481c0c01800042c0070010001c2120f2a0503401e20300c90402c1c200410000c00c18074240301c0e07902035078204031102840c140c1e00004ac800c0030f2002a04aa02540c002c01849459038011903110b2115240004e25a204a0101c0c1c40c9041600040440c0301140090382c0304a07075820202c2c56103200ba07034015000460807006110006220300b600c044954011210690703030700c4690795200800e01024401c004580001c3c4642061038489401c8956408107a01c034a20244c0383c10a40a010742c44400000d8440305103601140085501a03c22a8003000d2650001c40c1166160303903600d005420088209940440808400103607480100003480c066841080582054094201c0003008140c0590007030240f203090165540100e210694074600311b5800d0700d00200c2080785040416a8030700c2c8401d40c400059006403000c00440c000361003845c01070388140c201111305103c07014203e4160b52010401d030030642000c0038400c4e03070301003800c0702061 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 341922724 1250 341921474 341921479
    0x151201050f09071b3f0c0c090c0318050a050105060906130203060f10021e070f2d0f180b0303030708090c06040905010303120c0210091b0602010204170a0210030902 72
    0x240d0a45824a9198140424052400c0003e003862400d84c0d48402c0300b002080c3c020503103040b0001c2011030707d070b2907042261403145201d511380d95044514200c0c0300380c04c0300500140000114849101c0c40c900255103c1548c407003980c69520301000704015107440d9500d01c0c0a0740c4010034006241c1c170680d4040c03000703500c060481903200089280b10426901d40021041c00c0f5500c0703401038070b4412408003540d0040d281c0c40302504800d030040d003000d12140c080c0100c000c0955007500c00c0211a4946804480d940c516141c91005030780c2c950b6200080c0c180014800002900e00380c2d030300e40d00c030f210f1003080d14025580ea2000041e8550010f03c00100c009214024165210340c1c03843c100c0311904500c502268055100ea000b440c0708544820040c0140354008007400c03810010380e481040044e01140d4029103d0f2018a03d10342a140ca5540e2501031204180c075019241440700d8030040455a0740300c01900039801f520590000c16066020f807480c558020546520951f0007820070300c01d0942c9600c01318010701e10f50b40204da = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 341923974 1250 341922724 341922743
    0xb0a0305011404020315090307110301140a06090c05030c040b0a17040b0618130b0c0c0601090f11070308190f0504031d060702031209151201050f09071b 67
    0x89002401100b0750100540d4640320300c1c0c2000d0040c5030503c2440c25244181c005d12506102c0c60150003c2103a0306550011a2022400d400c140000c0c09408450421810b021041c0d081c03100751b951030b0340100f08440341d141041000121030700007a200c3d400101c0b03804162003410300040101021300802440c004145281c0325064502101c00d1f104821400c3c0c2d0280c0308580c11004212143c14030b11094080c060410011941c10b103004480120040c003118001000c0154450204150440d40000d48070801591800e4401643c4c50786241c1008021032004450010f0400980c0ca0015800c4404c0300c150325011ba85041c0c095403502031145000119010720b620031956080c3e21a03014246115090080d8031982d10401c484042c0e0460f940c40c515a4072605106030000c00c07881005a80004020941c80c070300504407921340c140000021a80c0014810a8410040015541441e06410f26a0f981078840440f503003140d40800c0030170b1042c0b8074011a9060085140740c000304804084e11140c90a14601c00c01075017 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 341925224 1250 341923974 341923979
    0x801060c1703100f0315050618190b0312030604140c0d02030601051c0b090106081e060607050a0302070e0a0204061b0213020a02011401050409020102030a08070c0c03080c0f01050c04090b0a 83
    0x1613119402e0b50054620300d00c501006500b01ca0140612604110b044070418801c4104107020309401c00c001d800c8040d0030021036581c0002e07410b19040800120070003400d441400070b4118115a02c0d610850b82da0344143c1c0f030010510380340130300d01005a00800c0600f644131304042a80122070001d60018012070b05211041c8991107200707013403600300500c81295200204240410300140224003078182c0248080c025080c00300920310b145021403103a030250f69180801079840d030fa004102a880f035144042d00900555003600c0c14543c001403107208079a440b203012503580d601c0b441008100d008a018900004500d20200c04030081110021120240002c021501011204c00c0a004031b81c0448140380c0540d46031b0804006804c044e08500c1c0c01010180c1e407d201c0d298a40e40001c1d01c80c032a4030080c034140803814001c06c0c82a846075500010040e03010b130700c080c0001d840c0d00308483c080d08141180310241c45114031007040c664060203031f613005581d9860000d0510b401d29607820040c100ca2801d00c2c3e002140320200 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 341926474 1250 341925224 341925239
    0x1003050303043509040f0f11040e0c0306010e09041e060506030f01060339081509010e0a03112b17041101030203060418030f0801060c170310 62
    0x158081c0e8480c14041d140300c503c1402c0e542140e05810030f01c421001d180c2401e0f90103c0c5620b000c031541e0500480b400a400e86004180b42c00400c5018840a4824035003040071624400315402081641c400700a00300041ea1282c55910040c4801c03501c1c01d00107500710000720514140700c3c610036045803280c05542400056000c0314840d942800e941541c1f050303114401d0203181e05043c480c13640700009a0000340041c5055803a240c0707100060500c41b02010100ba94140070340000400e9402c07001e5081501c01c03113100d81d60344509503140800361429011072400c42c00301e126a0f1052041031590340c00c04c0040c05003926030761030a548000742504410340342e001e00c98440758101008210508040b030a04000d03000e01407002d00060020352118048980c415151084c44081103a0b10740f03000038040c007460007503035a50300c0c10041006403500b42404112280c610000004249d0401411002c002c1c16070380300394403682d90b034a040758070070b60400002e0040c2807c1c0890310002c407442401560301002165035031080f01c0c0e0340e0301c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 341927724 1250 341926474 341926477
    0xa031706043b0f1b0a120302031905032a090a091d03070c1206060302040903050a03050c0f0403060b0f09070203040609140f0402130b0a0c0203010b0603090604030810030503 76
    0xc81c2c00c0785190510030094010481d020014480b40c000000b0540b0000a40c0c845a40c0d424600d901100214018a074040903507840d01131002400101003035142491840c074001c0c2d929004809000c1da1f6801d00c42040907420312410559110b1400e091011903d5078104105900350b06040e44083d4134000100a0304810b5106d126915000b01202c250004544121401c250008a141d8101c0c0748503400401480000c500c0344d84101007500d20745c0b202c00d84c411380d6928000d401005107a10094206007400a03030340516812202810106085440c20b0245950344c1300b0280c2d403817048030148040035005001c2030010510640c42009550000b07040607031507806a1000071700d041d00494280d80164030004061140a5010b044a0000e1500c2c1d40362910b40c7d010b41e00007070040202c8100d154044c80e400300f500301840d503004420b20018020030007600e80d1500f2034400180ac490304030b88183c1c003c0d8207103243d003006401c020080381d10036641e80c1c000d840c0320380f181d0303404482c0b0410240c15440445a451008400300e6010310 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 341928974 1250 341927724 341927771
    0x39050a0905010f0e1c05012403030809070806070302030610090503060a090f0b09010902131505010813060f05160804050712051e0d030c02010b0310230a0b01110a03170604 75
    0x303520740c17512094030303141c0d003500e00c0c6441e4688980101500030b030320240b22030340e0b140a484e85400c02d161a80e60700c601c602c1c0352805c240e2150065200308803d00c00d07010b405500960003044d0503646801d4010340b524007541ca81c1d15905c01c140c2c05a10000014440c461140c1c0401045442205011004038240d21544c8840205540c1846a039640380c500c00114034080549421082c11040d081c84681050f100e100402c0702581702d894140420725001460301103a148085104a0340300c1010000c1d40315051001c802020700300d0703580d07d0503220302601c1e1050364000e41210384140c0d4080002c04a69041c00700c161041b40381820100c885116a0215a1030540c0c103106050501d00e0303c1e0018110342c0b0842200400b03507100c1440c40c4043d64503010040e0b400d502c0100d41284c04006c207140c04549511342c030501820f0041c00144e54540d051051040c00445c0a041d04001012032090f40c030050010001500c8a40301c1012800c0180840c0319482c80880c14216a4105580040d00500025101c441c04c26a0140c002c4400c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 341930224 1250 341928974 341929009
    0x2301020c01091a060901180b040b04021602010906170c090f10020a030801050907050a1d1905040c18090f060302150c0d02071208070639050a0905010f0e 67
    0x102508030000d42d040f00300540c07255040318005d08552420076009070340401900340d16010b6803a4640352549440f59000b40c40c075480c015004656407204007083e004d08049504040380020303000076000800c0d920800c58800020401c1c40d001040c0d458183c03c0c0351030350713000c000010b801c0a81c0c1c5180f405140d5a8080c22640900c0e1500170304848441445e00800070101600050b109900350003d01455550000994012951b41e05040c0f1040001c2d108283c0c0c1c403900016900c0d03002500201c8240c40f219440c44000071288103440520043c042241c040e19a002c80030b1400c0d00c0714403402010401031035150071812901051510000300740341c40b81c01140905079610b10388000440000768620400c0303020000d50fa04000c80b0f1015141080c02c061010940d03140e0410701801d4a1800301d240400d00107681e1054032480300820480070f1024410803071202c040c1501c0703240a0002034904801d503a484c0588122800103030240e42d00c424403404c105c01543c2e100d00401d5000100041e441c40c80304c0c0e036190000303031440e9501d03076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 341931474 1250 341930224 341930243
    0xb030c030906091207020121050106110c0301052e0317030412080103050d030207051002220609080606011d090712110f07060902060d0513020a0806042301020c0109 72
    0x500d01e450658042c00c49203075548204604507007000c00380140c514540e0b0911b071403090784c0c48072007060107040c0c07124401c2e183c000e151400008646400c542442c00e07007605c3c80283c80c41d14802c070303080500700c85080f1b9444c0300700c1c68980300c00341c41451010300c8030522441c80c180d0780129076141c1c0c80c0c05503c180b40100c2e0010820000082c0424400d140c011004010b035140b0300b00d1050f6040d650b88a84666101520130141600420304404102d020b016140c0152265501151103840030200000c5600b910240310312603580740100490b8451061440005540c04030f80104040d498000c011150810026503809101104501b10750207a51031081c61401020203a80d58a80510003900340360454501030070491007880100a8079507280c03000c0c425900e116400c40000145044240042203151056a50ba0000e962502d000c02c41d003a0080d01104890500a44a40c408661940e044966a0900383e0300688120a40c02103003101035a108507030070600001000141c18202240c48003030035a10244001c4034500b11 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 341932724 1250 341931474 341931481
    0x509011b050c0a2403050a1e0207020f030f070311011106070903031115010314030906030a091502042102031c02030c060901060b0f0906090a0e190c090512070b030c03 73
    0x1030601c80c03000944030b00a40128040d0380300107a04030782c01413401c410f0185502d0300001903402c08694005c1000b05030410403c40c01a502103e400000c6d401100c040344141e50070f01c02e410b141c0c2400030307e0201165002000b05000d5040d23407a003140404030600c034581000201000340281d46800d0000768000c011507150b80140701e0551602400c070907040810242141d21200181c02c059000002d5075044075005042442a000665419400c5214a0701419048400000ad1020410560b40302400030f80c05612544540100743c41c8600507031055100309400c2501a226220840c41d00c207124006091000f0110382c0407188236070858003c01703d8140c58802680011454907448807051050b80d500c88102d6008121107400c10b03491a0441c050b01017020040b0401052201054450780d0444580307020080212004560710780235902503040407901421181440022006c2004c3e2902418011600395104e10740f555003004103100602c030090140030308a114521001601000c220010360141c0303031421042c0e0360f914 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 341933974 1250 341932724 341932729
    0xf1e01110309150f0408010518011109060d0b040e1b040f05165304030905120703020409050607231225020d020c0616030509011b050c 59
    0x50348052408010340081026900380e5403002154031180c0401183c1e10b44039044141c2000711030099804c400c40961070700c03003800524850440b110001c10204002030160380b2043ca0030400d14080e5620080c0c01c14410300c5899000c9042c2d0b0400d03003135003038043d10000b102602c142e0300d54500840c0c042233076109840d150482c41641494052000d9200f032103a014402802c04045200c402001500e19a081086540c0010400c00d410242510039804030f0300152001060500a00400342d03180041b00c5001c03c142c40b200d00034804d030071001071140e81c154848164051500e801c0c4000825a1103071510710b4000c107840030005035164401c0291080c004e0004001516204c00090032240ca07080303100c03804402d1640000513074080c110440c0c60400809080b28121f0701c503950404015204e902c505242c064403a005200441c0d80041c004244610580c00c403030111004809109041c42241c0154401d40c8118180c0c03c0800d010710028001c020040c9001c1d400a00c5000704450030070600402140e103600000c082140a1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 341935224 1250 341933974 341933987
    0x50316031716332319060e01060f0f0c060b0604030f200a08030306040207020a0e04150b06160b0c040b04180c08060319050f0a03120f0603020a030b060f1e01 69
    0x9480c20142041030b00842d02c40c081350444030321041c1003410035a400180c0c11000c02c0000301e2000d00c114109002d4182c40350402c901d4040c0034001c1d4000558001d00d80100c0c14031030500d00c4502c040b10340320072080b480b00b6141c0d9806410661085504003504002c0040012542034424860600401d072000300d060b150078400c850460b40c040e8291180828000a002006022007100d401500450740140e45103280c2c030105040e0340c215440303088240d048108020a10420381401903651210300d904021844240040180c103000c0c0c05041c840700d5050668200004000107681074014003184001e6003002d5035098800010ba106400c564040119580380b4811a000340c003902c07215040e241424070551a018010980c0c0c0c4914403100403510041174586014001c3c1400b5178080c12140380306035011460107040291141c04402c1030402600d14180024145210314882d4a0540364010074000e4814615225507410344c8000d0f00140c0c0c030145411004d452552034400b00783c600f03011500c5a03240d4502040014004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 341936474 1250 341935224 341935313
    0x80f030d060f0e0f060316030501050601080f071205372f070c08010e0d110a020102060f09010209040615022a1309020a080601050316031716 62
    0x30000d810b800c0c00180c0070640c04581c040d400440c40708169803402c0010b03103010840044a4036912001c40048180003040d00441d220700020788440000d0780b2307030b443c070540f44100c22107104001400501c0c0d03000c04001075400c42900001d4080b40610b0040d001c03245111400451a04402c1d00320481c0e4820f507840e0000d000300e41280400303030000b07442d0000396080e410780555150048000c0140004490701080340341e16441c005031800c00000c0001800d89441c0d69660915428114080b032911728600300c216800150207000d55506902501c000d031591000e1003c2040040c110034031654003809500d281d034a407481020010f184104a1105a8660388006800c10400303007002d00d01c0020580c001c8404060741403240203255030589031b01050590100c3d20030010043c002c402580302c0360b02070002030044c00024040c1d040e120704900303542119001402140c1a1101840001d000b500c442490b60340b004490340140c00030400c15a480712810401d99a0a1400c00074141d42c014808601e00e0034115180010507400d20 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 341937724 1250 341936474 341936489
    0x1615020c270109020f03010b0a1701030305041706091507110a050312071b030f03150f0e06010519030b21010c0305010807030804090b010c0210020a030f0305040f1506080f030d06 78
    0x2505001c9000a0b505c3d101c14080d0058107040001c01c9071001c0e20900440f883c1082020640c040c55840e0704d8020b02c0f5034024070904045408030844080340120105409010b08505401051503241010188600a07402010182400402900f0110400e0244130000c5054030a101070b43d52072020111142694a01502e03020810120032001c0c00c3c0310035440f10300000355405040040c00080c905108501074000700644550101c103004000a000b000c0e00003d00642c1caa401d01600c0f2541c50700011a4217028142c0c50070060001d0486403032000e4082da00c064203903c00604543d000044183c0082d851a502040681c42a07543e41641c402e41035062140d2405000400c014004542c40e41e1140e0840703024074050800c1c0315658010043e0140e000b50390210000d03601501c00510b0100c0c001000e5200c101102c4c05074040303940540046102c0b40b0074443e030340c0300b02c4c0e00030a5482c10326090346990907000051002e54401c19038600c00422440740c104420140c0384185002596138511445440301502c000d86d0102c80c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 341938974 1250 341937724 341937727
    0x615070f050607080903070b0907080706090302030d14030c070203010912020d0306050105090109030303050a062103020c04110304080c0c040e0705330a02070b0703050d0e1615020c27010902 83
    0x4425004011640407541002344650030b900c1e0f050055041014079031002484e8811603000081550308500c1800840b4021410b96006400e01d40c020f6805940a00c03260307840100130000164008940780180c0300441c0090000078007003401d6600c4808a042044213800907900051785114a030b03600d80242d1010f09000e20340349080040280020b843c1c284d540c0130090901d500d90000644140065212400412948240c807000451300502c46c0d07106048000117a006002e00f400c1192a801c140c01549060508000203030724680c3c40d600d5400d080e4204c40c0d00090980194040703889140d03070314051080e20381442c102800340140381c0030400041c1c1070381d0408038140c4500c1d560300304400c80b0f0103400c0000e0074401d408056500d00b80100103c2c101051034211203070701d81c8003203000000d2580c000d001e03042891040703500f0840c1d0425040d00642e1040038424682038030f85500414800040788214507034400303000f401210320b07000c0341000081540b00702804143c601c0981c00d02258002c241c4044142c010860040f085 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 341940224 1250 341938974 341938981
    0x15020715141b0316030e0a0303020a140301051827071409040803060108070c0807080a0e120d0f0e0414161d010f050c01020a020c040f0213030204050615070f05060708 73
    0x110b80c030300004120600041220002c044081d0080d04010b4407644043c0030b80b42c60040900c4c025000350051031103140000e0700c1d411082c9035040007904881c140c0c0d400402201650310800310501401d2030040030810021072482c848142c10b0304002c2c0b180c41d0520000701400c082410502144030000300c86a849200d495458280000300e510300307044030b0f0480000e28112803180e0b80c8910139219407201c400020804900000c01c0b0f001d014481d00075052290003607540e0b0844107405000c02005218100d103052240c0c1101c41504002c0d40140a400d64203151418020104190708000808407a0103c052102006041c01048092440801070104c10341d1141094007500c1104046103403090a0150224103110421400c500058041c40641c1e44141c0b920000b5543c85840d150001d4881c0a40b00c0d040780628201901c048100005000f44d66580081409048040345142c00304809020041c0c80d0b0b54100504003500340c94807054400401841b40100c0481e83d02e14001e1520501d003080040402c1c041164030000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 341941474 1250 341940224 341940271
    0xc070801110702010504120201031b03090201030515031b040f060807140409083001030f03020d0207060e060702061605030a080109020f090402071103011e0f0b0109031502071514 78
    0x346e034265001c11810701c545003410700c0103034018144503404113201c80f0440351703860419506405c80101d2903c01c1c3c0c2c05000b9074179010583c9989000c0060150741c107400c04283e10603030101040110300902c5008201160201e5110f1211084940c503820482407904420401c0c84140900511790181100070f80741080031201c1f9485043d0b0707501810640980250300e9a0350780485150030901800030007580b002610155a40b03103405449082080001c80141c015000d4201c405070020a824007202c190740c5418519103d1303401001500ea1100c2c1040f64000e03400d02001402150f2602482030a0384140300840c1d0b40c0e500c1c090054505c42c8168802008540100124440910241f00740d42c140f1906031009600d0321200d152881e01c0e40f0410b48040d4041d0321b031002c1401c5c5a000c110308801c400440c603c042020a10414050050700d00403040311b804508100002c1001072000118048250f00d541c0006090140c0c44c0c0d200c00c11464003c1c0307145080d58842c03800706030100790003070040d42014088001045400000340b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 341942724 1250 341941474 341941477
    0xd06140a0221060607080706060320010e0d0b150604080a03080108060a0b0d06020d09060c020718021e1b060f0103020a120201020a0b1e0c120f041e06020f0c0708011107020105 77
    0x5c004154540c0803e01208010700c503001131000d140d124804141103094040d048500000f0000154001070b034100c0110703041c1c10300c004181c0000d40c00490085044da503118209000d81c0019031980e420210400c4000761100050018001440c03196403084c84039450a0340700307807600c070020704454400ba1030140c00c50015643d0001d00030702590310800240c0c4490482d04502d0060100010140656042403100002c40b41e011600b0420740c1c02e10303080b01c9428140c0a581070100e00800202c030381e2090b0b4011030710701400b400c4005406c0c0406894500f1501002c43d290103804d20209a903000c4203441580014000c503d07002607440d01a00c40d20030040c4117113078a600001d5444c401d4080103010f149644021604203a01c1124040501e00d52078203004450900c6080c0507401d03880701818000114240010a06001584113414003442d0080d0900c0d1510320780c45454102c0c4d252215048600c55030070030040f40440700704000741007554440c1c0054901ca40c42e000307220b400e54562203e20340d00c48404200050050ba0400c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 341943974 1250 341942724 341942737
    0x3050f010e040b0c0c01020a12050106030e03070609110d050a0b06091e2203020601030b010902130605090d0605010612110a090b09030102092e02070e04020d06140a02210606 76
    0xc000001c140c03115132803407000b4450290010242d5000007003020a4640090002c1034050340c00c5030410142c1e980c2c2c84110100e030443d9903043d855420400000c07010070040c0c3c001001040c0109104214400d43e600003d4920b00103400071a0640c100103040030601090000d10b941c8100c1c1690300d50f04038905405410300d08114050f000c800e0b4040400491050040d207440f14000448807000164a245d803400c010b950b03a4030900c0200c0320508040b001284088d428000d96051018580110b6503aa0403c02c003030712160804480b082e005409404c0260106001e401040d0082496448550349854201c00190175620a80242e2003510401c2000505995101002c8000c0715007801c2c041e45c03148001e0002902a2140006190b40f203030000c2c03078002603c0c01138071488560b01500130013013012200316036003682c9400d03061040310311403010300c0001400b60400c00560502d142c07054600217408003c01c941400340d4082620550302c55680401c6124208800c0d01c03038509440c0c00015144114a08440003030118460203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 341945224 1250 341943974 341943983
    0x41107050a1515270f0204231008070e090106050702120d1b02040608100b01091509051203120106021b040603021309031101020d020d06140108041b1e0603050f010e04 73
    0x8540004000c10303d40d84d44220841c115401e00c6a0507284a01401030b400600960f12812102c040440a03645d00a10b005200d060240800c00310555510007038510f000f00500300700510001c4040b02c0c00554840241d40d004e00459252240c0341c1c2841d006101c0d0101100d007101100381d010301001c3c050560004035550f420303481c4800000250311540702040160105d5071100c080d078400c42c680400611007a40040380c10080c280d0b1a943c440c0d0785e42080038405406401484040740054038184960b0501701b8810b0910740c0c4000840e0315114808680303506a2009074024401a0060090010344246180c0058000441203030103000c8a82560006400750b071481d6481c0c9282ea44d200000802c041c0160641400b040c410002107440c1c10b1039a02e820040c0d4060501720300403920b8280c02240e9001892071a110030241a502e00c40031366526500c82e10440464680800d940c540c0d610001904400e4485120015134001c80d8620201d00d07182d80542914000b600348200941604014050b4402e5100f2650b4403c2c1c11 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 341946474 1250 341945224 341945249
    0x6160204020903030c01050405061806040312050601090305160501030f0c0e091e2e08060703110436021e0d060b0a05070b0105010810050609041107050a1515 69
    0x440700107844c41c451440400b03625420300302084144840801c0c201d100c3e48a5200c2003103480c0c0254006034076042c0803500240410950300710340c0c003c0c5107268070140d880003040c104030b44c5040e1242c44462401c01e00c085c4c50009460010020b00c1996030502170315003010f05524007480040b1303c2140141a20a850b0203c034020110340d030005035480c008221001d0241405c400c0c00300141000c1030701071400310010020f10007124104640416040c0021581c104548800c03010b403400713071160f04e000c601420204440542d18481030002244003018800884c142440d400300007011012415040e10b01149068015040302d03105000180040a000710f40500350341c05203804d0703540d41d0b1501460400a000a802826203100c01091074611590080000c0c240d0030300035402600640e031b82e0801104c03049411608400d45980040003003000b403c0940180291000052000c110100792090118168000960a40b4290b0108200c1d0060201315002d4140d004502c510902c4840b43c41c44502920f41401d200740415841b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 341947724 1250 341946474 341946487
    0x30c030c0d08040306020309060403032301061b05031b0f030906042d0303031d160603020a050408030a200613170c01050c09040b0f03070b090a080a0f0605060616020402 74
    0x480003c46003d107621110442d00d90405066031a0741e910200d900b1030102e403400f0301361105200d014694416012005240111310380c05c00a04842c070454003440043d0500012342d54000141d0140081e1071026050440101400401c7c0005480c0c10000188071145070810030240c5400d44901d411542a60307200e181045015030248100802101c07520401c1490900901c008020164180c000140c041c507900307690003220700079005190b283e811503041d001191400503c104680350194014060405260520a04059444820300c0c15039000e8841000003079101001e003000c131001c40580d00c50000c0280c000384102e141c8451040d40030141c2034005040d641d142c03450b020311603030170780704844020405600a01050600340d2496200c5e0304000d00a030310070743c00c1828807461818070300310410329500700400510b01c10b0b02d880c09640056000e0030942d03410402c505404102c004007003000c406400d1242250003a90b0385141000000c8480c00b5001c00c0c2304060170010751140d1011700003060b00e210f80460f001a901e12 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 341948974 1250 341947724 341947733
    0x1c05120a18060509130b0f010e0a03060615080c1201061826070503010c1209060908030906041104050717070e1c021203070b150109091103060a05030c030c0d 69
    0x410700442036411400444000c01e180c2d030300001034541e001c030950755050000742140290741070b5800c60b0422a0000b045480c82d15581d84210301c0d601071a54050900f01c200c031f4070303901d501041d51050380062840f06405d00c0701c280e4040e0b1100024bc2c1c04800030250b0b6041c00b55050300a01c03e0364042c4544c0c001c10055000048034012114403180c010f01403440c20500c020004c0412400342c83d4603010b02c014034090740d4800a00ca0030180104c0212010035907440070a44c0900001c40c0043c15041c400352003003560fa1006000003407000b40154050360840c0001c04491405107000c54801c48901d264501481c1400280480c41d42c202c0c4440503160014802100d056650034070031980107940c8120705501c422881c04c400440c51000c503021000c1d50099171502120b031054009240d492081c50710003000c55819100151420f40076191354514800c051500041040d42c41e041203043e1000c602d10a41030381d000005010380d503c0c014041c1c3c0020902680544451490840000d444094001229000c0c0551080032030420 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 341950224 1250 341948974 341948987
    0xc07170901030f14091b0f12030c01060e0a052505070302160b0d150b030402120c0d030e040c0f020303150d06060e06011b020307090b220b1c05120a 65
    0x40b82c84000400c401c0c45649100d000c0c100094174402401c1c02520802d080c4030f80000c0b20070017907200c0540347d555080ba0b0b210622002a2001040205500040c0f2008490320000c0c003540c0e006059174141d4070070505001e04810125400500b41c0e62160702c20f00c1720320401000580c88203603c0e82130340c1802a181e8507181402da007400303d10b80c84132810540c803403400310328900840080c1007000c080180400402a0290400d41445168011904035210520020300145000c00019407907104280a488040d0720340e00225904000f000400c4003c610f42c9503042c8901e08251140844c8410715260402c0792060b008070182d20303840b014002e1001020908580d00c007603200c88180c511210380c0001c1c05c100e00c583d101d4105918103420b440b014001011510a24260f40c0010010080340303070010050b20107503140800c800010515013000b160003030105404540c00b91402484280c0c61162050081001c07186c074020450550521488800200004c0308204003007100001d08000503038850580c5540c5015400c02a03805 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 341951474 1250 341950224 341950241
    0xf0906150d02030c220609020408070302041518060306050a020a08070e04090812070f1d040b040b0409050703230613030c020d141b0105030a0507141b060c0717090103 73
    0x510902c02460702c240c01e042c9041442d000805c100f1000f902c41c60141c0982c03045d486104a240c2c42880d003403002d454150311481e58100c10a4002300705594440084455003a010144070550307540b110b0810600096009203580800c1d403810440c508889084c1c068503048000d400f480811503c5940c3ca0300a13240d40d840805241d810051040c1c44207005240e2100300b0b801100c00d040003510183c1c000c2c00b034a0050009044040c03100c10028550341030001840024031040070844d610a4603010031000540700c5c1c0c420f660506002c2e201501407a030440c01c11050221840701c038500704102e000e038140412440403400507000306204404074503c0034281001c40364000803110296104454a2414082140300140045041c5041c0141e44030710360703c560801c0c8074210f0182014042882007000035403004866020707540c400390301d05194140042d40309020710503400003600c0c10000448505100e030024000c00c11298010001007803140780110b16034070410040c4d1500c188007a580c03408a004c0099070b0003504049031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 341952724 1250 341951474 341951479
    0x42904061208091c080d050c0f070302030c010b09150d2306010f0803040303090b0c1608010e07090e0304050904030c0b0a05040210030e1f0605060f030f0906150d02030c 74
    0x82429042c206440583c1c405444a0b100e00d0021260030000c0c0c181650340007101d50000002814454000c01207806084000d1005214060801c154545426200090308103d4020b500950310f54200c0d20741d10342107445090000b80324155200c20002450b80c5003128800c450001c1d11580c0c160b107901e180c4080041051f141d0106c25804a04045010800004209040b0b64030441d68145030740d5076107a01d54980c4a140000f900041101a0a00101d1303201c0700144a2007203440304640260000301284050002c190f044590a0794580c212620720040030402280586086d040401c081742d01440310076500c1c400c900c20709006849601c0000d042c10302a10303810030602e0f0003001d81e00a07440d200d80da00d402010111400c0744224400b20103421524401c2c491361108400d09002000e01128441d01c180c40100d1141c444441d8030703292203020070f181d1140c0b0081c20038000c0102c91607403030b401d0820708030020840040940951344c4c055000c00c02221041c44180c0c9420a0a5404813040380302400401d0400c01a00034054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 341953974 1250 341952724 341952749
    0x30606060a120c0e0901060c02030a0605041b03030f0e0613030204110f040e1b0702100e0f12010f050c0f0a0302250c0801051006080609131401020a03060504290406 72
    0xc03ca030410350405141d03104803140a15aa25031505864810840b14044d4142e03110030342c9540044c0941d48038581060046c151854a40c400004210340301001d504110000307407100103420b00301c0ba080f021440711030300d003201c0b00c50501500e24110a0302000503c4040d1145403214103420032100054120b8106284108a4640c0c9030348400c40f122000000351032801c155001c20780d034190208115020707141e100c0e90040c0f80301c032010040c2c00c0440e10603202892aa5100a18007100445542c64102c001024014040003086135a07004000408682d4010013000320100300300100b002140100b0304841d1001c105080058846441d4668000503040f00038001c84040601f00380001440020315000c012100703107074024442642c40c0c0d101c0318101e400c00d214a802007890100440c07031a18110b003a60f0760098240b144a0310555103500c48205c942e078405140b0032141d500040c11103000343d050050b40081d100030340302841007808440c44c01c0501c0410703108090184040201400d640e43d156040040100442d41a48 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 341955224 1250 341953974 341953991
    0x705032a0a03120206060f1f050d0e15180319030b1237030c05010912090f0609030b0705130806100f140a17070302031e0f0606030606060a12 62
    0xd9101d41401d2183c030301602c0b074640001e405203042c2d201540355103006000807000b0325803035004603404018580c20805100051281081e541d180d0b00c164018401210014004201b500141c116814809040d0102c010601d0505104c400c40c00011600040c501c12403c1000b40455036040303005040084000d40d004c41856114120a000040d8554500e07211924482c6003441d043d507030484014840b45100d03d845180d030220004203000c0c540740c9100c0741c050400841e030705140b81e803540c1110442e00a6400414501801405102804200c0e00060030107170030902c0003942580c480c1c03800d0900081010040042c000f4000740c940740d10b000c280009092140c02c40e1041d04010030a1072514810b0b014240303140c04501c500090b010000c031380c0b5030a00c00c4050210b82301c0c0c45c2084015060031018040f09503042c468018001300685080001e540e02aa000c0945a0014100300019040038140c42200d241c90f80b0450510110707540c041001074001c04122122a42c40c071450000740c4001c0444940c0059191904201 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 341956474 1250 341955224 341955233
    0xe09100f030c150f0e121603081308010c0504150203070c03051f0b0d0b04020a030503040906170a051506130e010506042003190b042c0705032a0a03 65
    0x10314103480700851503c80c020540da50071940b0f91132040c594030010720310a401c24840c0c2056140510030f000314600351900007099a200460100e85a80103c13a0718000251440d03c150302c0c052960058640d020003840340c03404100300185140141d0113a1079481510554001c901070080003142c4c000c50380f0110500000756a8101252588000498015805050090032500600714880c0120a031801010707081c0364207060b155090020b900803c101c0c0c20402141011004c5041000500f000b00150700001c030355241402c2d00d44c00c0380f81682c640903002d0ba0040701c0c40d80003e14041960400000d0030a42040d03555506000130307040000c07903101d9410f264031303207a900700c941441034000c0791207881c0c10754041c404800c1c2a08104244914148082c41d048404e10108004090604500c110440481404201c1c01c10010000c1c0450b0460a0358048039900e11100c00070140c400398400844a69002c040c0001e903180501003912041000c0300c0c2c40c86449010700e000c030000c1c2840c000c07141089007c1e0910212a1300c03480d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 341957724 1250 341956474 341956493
    0x3200306070801091b0801140a08120c010b06071505040201030b330a02060a020a0309022d060f090904050703060c0c050708010213090b01110115030209090601060e09100f03 76
    0x260384042420810481c062035a40c100845460116a584560310b80c88c000b620544503c0c20413010b0f60001c80440e0003e81120100f050704401c100d41c00341141d84045603040f10b802c5600003c11503000302018450030000c205051036220002640036000319096850f0b2004030004c10003d1f814550005042e4079512040741c4800800800e5405820b50f03204103420103071040d0b0036010b0703080080b005920142c002074065100d07402030081d40d0040c1c00c010030b0b043c40039400901050810322a60080b4403a0704d000071032407142001703458000b4400f0381c1c41e681740030100140d03648180700301044540a0021040850304014040008000968211200700500030000500901c000b031002001c0d2450302c101d281c040f6110f407041c800c8902214000030310513400d82c0351440100c044c260014105041c1b1800141c24650318000f8042d50030040d80c904418040d1900711320400100c0310010342100d456510440052200540001d15511802c3d02285c4680d811394440a94688180e820340201c84e13000101540042004008003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 341958974 1250 341957724 341957729
    0xa150f08012004150e03061503010b2202070f0f06090b0a060e070c0501141006030f020c0726010c0e010905040902211002031501090e07050403200306070801 69
    0xd10070100c0721224128807000c9080d40600742c0c4000c1100b08601c602104c8028103409180c1008103220000c80002402c1400494452601201d801000f1115107002e00c16404207000072105403603801002c01c8000050307a0500712941d02c01d540000d0910500824041101c0d003180d0084044089102c0c0346010f1003d40b1035503000310307248400079003c2403c003c4c00d402240240c442e40c8040d032109a0342d0700812109850a183c0036a099580e4054101c480d100b80c2103860712900034020050351091070400000c0440b642d162080c2043d5105028501d003141002c1005000c8030700d680c0c140700300d81a100a4400c00c4020042442c1150340ca07009004460680114038012480c4090701d846500329910802e0106603070360441d0013980552894015040c480c41040480980c8008000b1100300784040940300303040343d01c195040310220021812001e841c1d0ba00151035005040014007502090419a0307001c0c1c450301445c000281800745010003520410b2200740484844070005003203900a0601d024060a5184c0a0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 341960224 1250 341958974 341958989
    0xb0f0a1203080f010b25020907030b0901050105040f051011030c070e010e1e040309051206060301050a140c0c030909040813244b02060114090a150f 65
    0x780010f9005024103100d02e0403143c2e254070340c0e0701e007018211081d4041c03081e0680c0603400070455403001c80541c80b6546580d01c034201c01d4400044032004c1400300000c6045c140d1143d03040110401007845040310001c9070700110b920656207007011200518042d07400c40d24015402145110208080d00e0710840050000b0803180c0000181071140d0b00d41d18082d40705103041362a41030301e80c820324922101400200032154020b02030325045001c1c50701c80300001c481100500c48061f0302d501c5441804a2441d00703102d0b99400040700d110801014001c0070782036034403035401403d030190300c4808101900c140d1801d004070f071b00c00d040003002c00b947c0d45000c2c0b900040d1a00b040c000140d070010408004200c0c1800b50890b0458450340c0c00900c01c080441640465080c0740c0d055048080000c54120102a82600031046000305c0340c001500119060301ca100b03600d45802040c2c0d40d011540000c00411010100165001503070105a440c0030941d078500441002030300100300401c0b10383c031451000140c0441800080c0c001e541c2c11 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 341961474 1250 341960224 341960237
    0x3060c04060305010927020118090905060a0e1e0304090f020703020d020a0816141203090f0604020a180b090106021b04021c02090310020a0c060b060705100b0f0a1203 73
    0x213940a607403c03911041b075880080703400324103841402c01c41b41c0f0700f50380400d10526107043c0c3d54500729200b810040442d400010820341743d581c02c404126082c0006544241448001c11412000780c241030350722b1451141e035986155030f0f40001040e202d4203004850241c0252101440742d141c01c0e15014000b5440b1500a8005001d0340c544020704510204014025981100175a42400307007020349182104060441258104800e0703101041c0ba060174414280b54a2220229039101d19020f100c081c02c0c540d10072078080c0d03e42c10001c1048010b81d00c6071040e005070b80c0b08e0385807188842117403081d0500034003074504029401030780b003000052680d1b4001101d448200b404081c07801d03020110b0003440140d004081002802060042c403c4e9180c018540c0908051000142141e00004040c2044001c80e0301c03c0600c8030006148010010078418640100301107078900b40e40161901550f52036050311a808242003101c0c181e00d81d185104640e0b03817aa0181c03e141802401c412005560f40d00c107414995181c90700b180401e18 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 341962724 1250 341961474 341961479
    0x20313170a08011503061206020409150303090b0d06230a08121b01150f05040513030e0d0215040612050c0301030f0303050702032109010b0312040302120c03060c0406030501 76
    0xd440000500e6190b280e00ca909010441e01d202c1608203c04081517940e000000c1e00e070711302c150035828003401098010f90b0341c0c0c01d00a03240150703000189140642c007800e410400c0040d03400303d0904126000d80410549070703120480400040c1074198851380310001c1070707001c00200743c9041d4900781d03520b58101c0345418003503a02c0b50071645400001c038600f08001c000340056124104030402c400004c1c44240c000040d03100c424130001102c40d1442d00003004841c0c19040611903418544100f40e0056a0801000703001c0c0a03c1d90018421401e007072005000d461900d2051013151550304400040d02445155191119228440142481c03032910b600d130202800e10022071000c4e01074000301c0b41030325000f120a001011443c0c070141c01806000c2c00c0703101148000c00c0310303100c6c0035500c511821420201d0020250b00b81800401e050a4850f0b200340c26110b6008a0140c0c00e10022100850781140c1d07041d10000710207202103004a003442640d801c81030701802401e003040079100940c0020802d0314681e4804000c141d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 341963974 1250 341962724 341962763
    0xa05152505060a052214030705010507020a05010c030b10030b0307030b090a02030616020703030513080a0807110108070e10050906031005090705030f0403030b0f190602070e090d21020313 82
    0x24640340202ca80e1210170040302c081030079580440c211317002c2c1200b1a0700e080c48954605007120404c07140b9800603008803a590041080a0188214111441ca001c0c0100c081c1d01c4001190503050840300020b01d03680b001c1c44490b584091000200441d00001c498485182a8a000713071190800d401c100c0c424014200022075118040c0f0740003082c0c4507564001c2015a0131941c0544040c0e10050482d00803212020000a8104080201224091040310510b44608e468909491040701a024450500801008000265a00481c1440d505e64201c400c184150600c80d025141c0f80702e0300007510b0704904d0000810044079084040b03141220415514088a03982e8414121403a000c02d4070854a021680d0010a01080c13198101e0804198024440d1400070310034400180707050004258104100040c080400803190180584c0300240302c130b03900c8001e40f86418101c268568201112810900024003c00740d40c0801d5a64503c031800e1030321404650300d00b0144030004c0c502303030114803c0b112204009905076214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 341965224 1250 341963974 341964001
    0xf020304050a0206030403270303090b1216110a0b0411010203180d0212030d150f0501051b19050147150708030a05060a05152505060a05 60
    0x103035007000c05001e01c100258200822980090300039801c00c07010a1a51007000c0d13100700e81c210001d16a100000402c0c1c65841c016000c004140e00c4064007a200380101601d01180d03d070b187d41e04c20103502d2920400c42c2d880708203803410380020500c500b1601c184a1610204281a61114000d40c05200310311100c4500c08012179036440b846030000002054040400e409042180c40c0c2c40071a48000e0a501e13160100700041da2441d003114101e4803006444281e040b8036040d41088090181c0141d03107038007455608103400031304240702c0c01c00004551140c00d07100030b140d600144802c8101040100c1c0041d012110745c140a0301030070040c80d0078007500d103981c0042c40a03000e000d03081039040c076000d00c0e07811407203103508418032508a07640c21038030f0700021000420380e0142c080600a2100c40d1280d480c4a440307040c500394000440d00000e01c50340c0201c9418030b082c07180d0740d03c0c00500c03010404952841ca03900c0400229014541803105190b00840c4040e820203130400c41e0114116100744d401c00420402c581e6150400d6152 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 341966474 1250 341965224 341965231
    0x1110306060a052a0d08010602010b010918060506070309080c0301060f0509130501110403030908060106080412020309040f09110a051c0602130602160e090601090c0c12030c030f0203 80
    0x1003020800401c0d01405030f0080e081d020560000040ea800c2d59610b40c08100340301c400360300d816412951580f0403080d04000860f02503c0603100802c1441189400a03165402600400b08a4550950100840c00f410b800c0540900806001c65131605c102e450054124205805a81f103180203249005640381014803030f0200302c4040341440050145400103029420030301900c4098140062980720300070070f0f801d016015824000f80c858503591865810010b1507203c09070085103964000c01e00400210350711444407a00160014040c00d41c2c01e1100c0000d80c40c4d841210442600142005451880b0341580d6002401d0b080c0520782e0707107003114610803c0103140d0507240160b940c880e0b42540c0c0490400c8690100007a102c0c840c0b0401480c00314110000b494150143c1d1001c4016440150403905c21007040088078024040420099814203181c80c4680d12000d050041a2242c0c1e6106080050188541c101a855503042011510a4003800340024064404001001c3c007003401c00d90042d03c0c2102c80c1c03003200e10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 341967724 1250 341966474 341966479
    0x240405071d060d03050d1a040c0903050a020105090117071d040203040c0605030a091e03030b150304020f01090915060206090703030203160c080706050d0b040507020a0f020102011e0e01110306 84
    0x701e0740c030385007004225190080140d0810009101c945021807883c401c82c40300c01d1080e0802101a001401004161211460000b00700080c500c000c000060001440360f40f40d80e4242045034030303003000600403140d10300514030100f811140c010034403500c1e036040441505c044c1c80406d034000d044001d00003404282e09c8155002058180c031004200f20352032084010395007001c2454008a0130862035100c000c00700420644e400d05564030940d200303041640600c1410400c0c081a2064509550024184241800000c20181c02280203441d4030003582c1c0f1450411010309003030700041001141420181240807c04c0c000c04003d48944804200202d0700082c054085a40c958000c40c5003108040c4610038801074035504075455010700308089003060050142c94041d000580d00c1e240c80b03540248002050728060100d00380280c5c5040e0501000580c0465600034850f00440602c044c251a0310040340140000c0c3e884003402100b4807200c056060300d170317000f110823201204020f010403200c00b84003220610080c1c84442c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 341968974 1250 341967724 341967779
    0x703090201200c030d170109060522020706020711030d0e060a11010204051210200306010c1403040603060f090c050a0c050c0604030c06111b06070524040507 69
    0x41076040c00c02c0b8400d03000e220078040e1140501154042454812040300700c1012a00441d102e507108003000703a19070300500b80d001c002d00c01285488040340c5943e8100c12041c40e00c2d44030425a100e81c071040d80403541460f520203000c660b03401d6642000368011482060040c42401902c0d03040c040540308150207414814010032541c50011140d0060b544c1c0414515512110b540a00001503070303030b55440c020f54041183c003005d00410310314224848110350100802c0c402d008110580c244419803501d05499001d90207080600f226000c2c1d05101c06074041113191029540702c005008a00c3c0c5925070044021036600780914040703140c48540f90016502c1d00f110300300005405220784a000303441811440f607880c0c001d0068400c2c40e11011302095050344150401d807401005010100300c6554456125645400551301625041c840c1410380d41c07030040340d44c05c924400c040c00318414050100c103015482924404c0181011a0807100c801c2c540244002c50b01540d040c082d498002541445041810854449034024071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 341970224 1250 341968974 341968997
    0x1404080303040c151715031c05030708250509011b06020d0609141501050c0303010e150d38040b0115050315010f0302070503030907050a0918060f14010e07080703090201 74
    0x106c2d200840c040c115031600c0b5003c0c4e00c05011005002c021560b2000e513235519074901e4000300c09040e0000c040c0072416800150800040380807a0390460681149540c0b82656817a6000c0c0b00403100c40417451050340da40e07415841c1c07890420200754000c5c4090a51544180501c990741c0c3d02060032200d0204140c9520715180c0002450118084c0300d40e40c4588050408078200408400c0c203d107560404d07004070000b01d8100080c02250310011406102ca0302048a11b22143c0c070203560b0319240d0203c204000c0891801282044821848145185990505525880b0782c6403405080c8642988400c0c4034226642c9540f00c04c03109818032480490f4843c609080705080b0200340c120046071034268042586c1d04040c0d007848400000741d0144001d40c00344d40d8020041c00f40714180000c100359001940c0c082c4000720302d4030740d503401c09402c000780c524011500b01000042c004c20122000c0b002d85070540071918100e050b5400441d89602e4140210b008500a645801e0240d40e1020103404071140303042d001c1d001c103e00c0900c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 341971474 1250 341970224 341970241
    0x706020a1a072303010302031902060d0c02030c0a21050c07030b150907020d080705030106090603090606050a03030807180e010e06040603140a0b0f0c0306011404080303040c1517 78
    0x1500300c42e040c503119801c0d62605242c00004502280c440e030754048000010815072400300b02d00f485000e03400781050f040d18519400501704d07100b103030485000705440b000824032648c0240262101d000c05030040d22000962407411702c0c2d00d03047c6030314001c0040c00540206050340744244c040e0307494880040c0043c00c0150964440c6a030414000f8070700c0701c50710103035040d0016907102c46203087d00440154000b03001c1000f50b24006400003000409681c00c002d800c0c00100700c01c0d0342c44100a402c88115050002e40241142400c101803d266080745812402000380041096400b40e0001d124109a64502c1da85480440c8031811900c0684150ba4160060000612030550100446a08070344000c0001440940d6941d800381101584040f140503a04000c2182c0300340000d9081045c2e0050f8070f40182c20603494074088182d5280800f03000305d0304109a134428500002202011207001e0a88401225100e1500d8a4040d540c94a240241c10405500f034020300b9081e405014802010f03540b83d050040c807a80c3d400c44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 341972724 1250 341971474 341971523
    0x305070807060902180115080c090f280512010e03040608130b040501290d0b100314160501051207030209030c040612020a0f0b0d0519020d0603050706020a 68
    0x40d15050b950f01076880060f40c48000c8041d120707410083c1c9520382c2d07150170700d2000c5515012040c041800707200010402c14900031412100702c1041100c0640c4980c14005c0810407410344542449651091151005171131961003040780c0c11560110b824281c02495943e07418240d404282c2c00085d40e5005000601030311b40140042603029009464489101d1519141d89050200a64044e9102d9548070f541c83c00700d800b44111407a429500c9080300a150141030080b824004107090094550310040020030144104103908030011500000c1601c0116180c0d10710948500030071200003403407801ca074400181c2d54042c0c0c055481c1c800760300d102e4030641e5640c007806030081d500c4102d8107030749402580c00400c00c1b41d980e031040502030100d103014080002007a2052122980158109a40502c3c3c180010003c582081c0126140d80081150200301600e0f00c101c607421060100c1344206470305002103140c1e03813550401d60040d4110303400b0740e00700c40500f95106001c0ea11583e10620144c01c0f8952001c01a44824903c038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 341973974 1250 341972724 341972737
    0x601180306021612080604110f040b070201050f12070909060b0307110f0321090a02131107060608061006080c0a050f0708070b04050111190c0f1410060b0703050708 72
    0x1118080302ca25569440c074804d10078030f07007003020031aa2030521505040030300c56141080360340201c9030715041d0f120300040d10a01503031046041780d034000142203085921035801c0e501100c4115101984820347c040d000138017400c00321441e01c0012007075500020309601c3c034002c01040714248480f551458603200001c0b41c1560740000e0740b4415100e503d04e00140c448041008010429490030903c0984000c50b00002109101030946c2006500030030035000980c1d030b240c03004960a0003035407000418429044003540345008658024012070b14001c0c0000322060081240340c407c6202e207000800c030548603a410340d41254251812501300c131080c88800041c0f4010710050500c02c400921f440d081142d641c0c0c4d040c8450b03000903401c407004104c0c3d0052004000342400b800c0546400c0e2404141451200041c2c40c0e0500079800d0100304002d4002481c206100c15420842e00c071030381143c14040082c2810801540d00d201d801c400380103003407400714005039004e066820381e507442c0e52540e60f0b240f60a20700c1c0c0f03c0700c1e513542025 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 341975224 1250 341973974 341973997
    0x11040b130c020f061006180e07120902061303111e1507050304080715020312060603270607020d0905030303041b151206120c05090712091109060118030602 68
    0x4089241d4883d1003009a03a114120000c60040b00c5420601d0080610103404000c04907205000028010580e150092079408601494500b00c001e02c0300c410040035282a4030003075008040010526200c0b010303000041c003501e008403003020044900c0320901004105103805120688150508942c680ca0400700c8400107031001200b8a05227051398407943d00316407099000806c41e600100c4200000d81c98040f017118060382c540013035814241d80c12102032550100131701c1c4074450200007000070300c8100d03902040d4086072400d01281903504503075a4000d07640c107019200d840142c0703c0e5a030b182848501c0f070800f580c141c4001802450545e04c440d502c2c3d142c910b0060741e60b080c10540b030050100702c12020b0700050020101d01d17a02c42c0da602d01681118801c4411541000208450007462200403540c5401082d08545082d82c40000c1c65480020450342e00340d000031456440c030305158418007440310056080c850150100c5207610729031216401940c12034900b103100c0141c0c0c00e0025040000c55030b958003511108151 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 341976474 1250 341975224 341975233
    0x3020a0e16110a140a0b0906040809010c0201030905030c1006050f01020c0d03020109020907020a0209010906260313170606010f0c0b060301060b2a03210603010f0204030f11040b130c02 81
    0x71039640200d413a40704a690090b80d402514400305004000c00301a070002003a1000e0244c1d41410380b10000b540c440c0c0740c0e1007414051504061801c59109510403d0360f42d030400309507a1641600880281c0300d50446050040340760401e0008102407404200c0000c5c407001c16001055001149000c1c4900345007800300c160300799566401d41c1c0e80940c0ba42040c1074462511a405042072001a204008850340180c1000d81c0e07191500e8000d000c0088003200c50b8030003100da4649403e451500c00078051035840b40d10016010004107a00008940740b030b5038884800818060103540403030b5101c20046401001a000d028005408940c6c403202142c0b40d0b48001b40c00020140000c90780549136030452105912410000c02c40f5040c140c1c80707025107014081510326103d0003c010398507010200054681602515181410110324030b00480c40c40e940950040e20710001001043d5121543c80c01c1c0010800032000c0191584040189107100500e058882c906000c50010b01c9807116454030f516450040c40307176003041400d6218 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 341977724 1250 341976474 341976493
    0x30e0d05010c020618010b0109030809280503190f080d0608010c050307031d0616030e07090207050f160e0c0c01051602012a0302220b0403020a0e1611 66
    0x50a0042d104200c200340c005081030f04009400380756410b540320103140c869150210554042c1e9003c08003104581d044060f550b01c801d09880050350b140850884000340a50a160292107405071008010844800320199544104590007101c1c02d094864001000e290448020b040004c6103200940002c10418000003041910b1707070761142c21918a40b0303044010400110400c01003a9041c000c550700461032070381c2d1707002142d03c410106640c0d14010741600c1c5900e002511b1400d00501c01d50241032144980c10840b0212651080401c00030b50000d8000d8500e0700603d4100c407007500c00010401217220305946c2d1a1403107231408803442d01001000c1d0000d061088104030400110301c090003141d00501e03a41d409000c2490303807040040c2c2161944400807031102c2e1103c0081007442c0e802c1e4200c401892041c1405030369030b4260b80070034030b44080d050b4120f007100002100c0451a030390000c000c0c2094034400c0c0c46031370a05840d07502030f070403006040320f003250030354403007604002100e108500080702181c01c00125071640c3d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 341978974 1250 341977724 341977733
    0xb160210023403020c01030c0e04051008010c050a0c02040b13020a080f011d1f03081605070f0803220f080f0d0503040f061e050103060509060a0e0a030e0d 68
    0x81c0804444411580040c010614800d5881160000039002d941080c03604140c6640c00794a03000083c130380c10305041d40d81f0350500840303001e140700d80c18204000300104564a440a0f050280b03c2c814090f9103080d6182c2004c1e5142c83d070050003159628481e50f03d0711003030000d19a080002601000102c5608004000381c8a4400a210700281a8030f810b2600c42e80a50300e0003451842000b103050740462511ba00710098007010041480d960381d0000c48504100010864038100c0701101229a40000c040c40c0001420002061840c0c203030704541c62241d0240c8840f181c0d01d02096032040310074090141140c0042049210180d22004296401e0303049401c0302ea40c450303072401c060006190a40c0602841d8229607216000100c0030320640d001f800241c1049400c6040540f140c415800d003a280c003c00700c0303a0b19180042d100b444040004400d00c41d144c1c00348269a103d2411401a000a442e4000305104050100c0c0c000c401c1030240e00404489803000700079a15264608880e009500d1071100c0d00b00c01c8001903040400c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 341980224 1250 341978974 341978977
    0x8130302100203010b0a1106060d02060d140408030a061a030a0c020c0a0902070c0509042d0f060e060708240118090b0915060d0222140f09040b16021002 67
    0x5c21341c00b0032481d1640702c40c641c082d24100c8108650b11041c1c010300200b1203030359543c2480b0f188194040d81c51f035440750700284100000f400508403000002d4100390070032003001010802540b003921281c50910030a50b0f606000396000b00202d0119840a4007403000441d102100d13440700305030038031034412a101e40e074010b000b041c036000c60b94100b00c04058001030001c0c144400e4600c014010a4107442c14101850075444500007206c07134500d0380e40540344040361901d0385103507500c80508803600444020400001c61806800800700030245c00c0c418002e03d000180c0181c0101e10740c6105402c1c02c00c0d6030809502d601b00d50080c040840700c40c0e40c1401003403c1420240304550701020098450000b002030000d11090400049040040a0071502441c2c07015010080d16458103441040d44000c9000d44c0381c9600d006641c1040c1000c03041021243e203d2000000e49401305645081156800e03180e40e01c10480000510486071001c0390b014100c0c1e8030050205c0e403c0d400103401551103000c42d00c16100e61150b9010104240d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 341981474 1250 341980224 341980229
    0x13180302061b0909060f06070501110417150f09070308070c1e0b09010c08040e0405010b0103240e060a0506070308070906050711040b06040902040609170c010813030210020301 77
    0x141d0001007009031288294080c500308110703941c203080c18a00004006140040f008006030701a0403100050260b070b0f201e400a80e000c0580c45002441102e50205111807160020b21540741c008400000ca00c81001c0e01084008050345982d9842189075a00800007400c850040d0a480880c8a00354000011880d1400030303090315403140c410018454070340b244070031000c0014100355034910000d03c800c10410b80d111003110b6118200b0708040341400e090f82032030601406283c0c05029100440c204100801038103501805148000362402c100000c00d6070340b00c0f540710003961030251003445188424480c040c2d00280711540300c80d00a0510746400e8641c404101c407504090011000f140d2058180140e40d5084410540600541c1c40c0a60400b145030b2541017102c4600010303280100e5807403815a0040c7c9588003100c01800040000b03556035661040700501c40925031098804015180004030410380007c07850f400b00410581d00c414981d1140e011a1000c6100113000b141544910410b490b890070460015600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 341982724 1250 341981474 341981477
    0x40206040b0c0a02041a0303030103060e0c091f09020f040e040501110f030108010615080103060209010c080c160b090901051e03070303091d0705030a02091305090120030403020a02131803 82
    0x160a40504c18002a240004d035030340903100503261924400c4d01c00000b542e0449403c013801141d03500c02c4288060410070001c51080d0803002220400c4002d04011041c414510482e0721100c00040e07844000e10100c1c05070380c0008481040802007000400b448040058010f802503000003440040c8911070340d19688410100102628040010041c0c0242841201300801401160380b191051000d0000d204940500004261590200d040e600381d0348204035010016500c056034030b41e035690401e41c5954400c10420180280810110040b90500401040d1484408090091209642004200100d80700714000c9036a10703000c66690700c44d290386e0801000d0b004602079110440300070706100c0a0380440e040078400c6803140310410b051041050740b000c00c880e80802e20310401603c034a5244001240503030040007050005003407209008003400103601c004504019107032000144062092100202d00040350050096000070b40000c0250904a5201c0031080b615200020350340d46084008501c841841410350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 341983974 1250 341982724 341982733
    0x31205010b19180e094b151005011b030c17040b03010603050703090506011703040305100f0e1c080711010f090201030509070f03020d030302070c060519110303040b040206040b0c 78
    0x18201080c40030110750514500c3c105440c03012071000d003e980c840ca000030026090755140704803942d0a40d906d00c1e2404c240034400e440c00698808100d400141041e00e6060100070800301c000340d45e41c00f5940986001400c4035580700314810300d883c141d914810700801607803141440411070101030011401403010b4080011026103c2d41400e100400f00c07a402441c2006040ca031800c543c0c0030400000c1c0d02411108c820100fa45c140308005100c2e070560149501c020b01d58801d101d4140c001080da40c001880c04042003000704100d41c2c0c0d4400d102d5960300441c071518240e0362140c410000365071280180d158800c15500b003540015600c1c1c0d91090071298544920004c07590340710781041c11586e15004c0c070303a0004950801051101d0a140303280412100303500c0000c2c81041c2490041c001c044c080d40603a00e03810340080d2681449903032040060055806955226010502e048004070603078022991080f40b0418540150308541d02c50351600b14101010b84140d038004414000080d020308421f0007000c004c0c0c0c0200250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 341985224 1250 341983974 341983981
    0x50903060109061e050607060b03010b060d0212150a1703310e220609020909060f0a05070503070806040902120d031a03062701090f031205010b19180e 66
    0x81e84088007500a960040140040030840c0341c0d034000c01d590500323030801030028000c1c6079440083e00408003100c2058100714007050501c4071100540c080c2190a8620340200800d40d40c0c500700d010401240030070690b011040400c01d0024100120b4109031140d00501200c1c90400c10680354102490340b00040e41c014544000100100c2926840030b01c01030402d9041c1c04540e09040d4440594116010b0401ca48440c000510800b40110340e042901f2160300540b610505041c66581c407900e0740e00803a420f04810310050b001c0f41c4950424484d01d485268071303a13140d50850300d030324004403400f45014107010307881602c55991202582d030f0100c4c01d10f2449030081c0144540440000e02406817005407060a0f01c03401c1c804030b001601c1e100411044d6214400288101c0d2090803001d810080b100c0c3e04113812699881c0c8a0460100a181d07071034564158042c1c1c0b1000ca25800030a4900107440f070034004c402d95001c00340404844c038486040e44104414403804d2920740d441d0070520303500304041140c1c05180c003101c0030400e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 341986474 1250 341985224 341985239
    0x60d0207050d0f05040644010b070201020601030b130c09020c16150507080409020f03010504050916060f120e01020405040b06040308040b09210a050606040c021c05090306010906 78
    0xc0c50400d003001d04100307081040083d07010348503000d548120000c0c04050209480c0342500710300a06020b102c5c1031070300c01440711014468045491406682004450b2190000c07400d40c4a01c015070b00e20650503802020035078210703540d1130307c05d200240c035036284440712502c01000a0803140070a4040c04440d200180c0b604c02c1c414005140001e03200c20280b614410110030300144454060b0900c00c20a2820050764401071803403e002c5910a6901c40100c10348040b881845290001000354100c8404541c2807113141c40d060710503a100e003016221006121405070f42082003600402e0458184d24450800c1400c1c0d8410411020964080602521250b58005418022880e052250b40d109200030b651860070326040d9071b103645e2140328900410b07e203103401044a207010b688011a41101d8400c400010640c01404050346a44031007500c8116114000e0a0010344542800e1241d01039505c11030f80149065445030403c5c0798003022041c00041003000070400300c05161020009240209180b040000304a444e0140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 341987724 1250 341986474 341986483
    0xc0206030a0e0c0f011e20010506010e01140a08090c03030a02060105090906160305220506040201120b01050d0207020402071403070c14010f03150e07120b0603090607080411060d020705 81
    0x2102446504800e826640c5642c1c800c1b40b8920100141607040d000e02000a02503540110050a281c00501d80002d401c4a0b100f040d08114001c410a0300e81a00130140c020040d01d0074407140d1240340d0303c840240702c080b004521641d00d40c1d8103c481641624484001d00d0003181c11640540c1031140540e0200c80100b0371414840440e0780d01c92090f0020340424104004500c2d881500342038200109502c81010440c01021101548601003401c065103c40345100c0ca042d41d100c01c0226016804613090680030b10f821056030040d46120041650781d50b1424190080100094100500981c0c0040d820320003440000c264031124501c84400100942d11030009141403199400307203801523000c80c21480008012640c01c40c1040500c520071341801301d200c07a035011441c4074001160703000140104005050090054001d1000440c02012100501000084000340811480255000d0035254001b0300001c400911451125420038400ea09403101c0004400004006030407031103140d042240d0008000003040740810 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 341988974 1250 341987724 341987743
    0xc08030c0601232e080a0b0f0a0612060b070503030103120c0222090c0b090a050f0f012003030103050c0406050d02090109050a02090607290c030103080a0c0206030a0e 73
    0x1040003a114403c80128201d80111a403280c09403d02000d107540040d0350300040102e0701e10410b0064200d04c58510018112401614000001850455100308606040000c60f54203980070340450003c3d0f03d0700c00d084407d91007036400886a84e503902c001180041145000f0b20495015000840d201c0d415800d000603000850b0030a1414020003020aa0042e12805004880540351148040e803640d9880505800342142c5200101005c401c68004034244c05450003800007034000b82c800310281500c0b1402d02030241c40c8000d46a501400c00110902c00b90700c00c814a0000440c50508030300c10f03a45031600c0d0f503d550003c1c0c00840e00c90b04048007411140c201407207a00c00038102121410a14035442c0c001c01c1c140d0a040c0280101c8544800003d0142c0215404450450501800b883c1c4c4c3c9015034100301080b80f40f4019410340641d41070160041c840a0030a400b40176801e000c040a00d1a46180d66042103580026208402d00041d10066005603442c0009180301d0030020001080c003001c2c85406130304025502 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 341990224 1250 341988974 341988989
    0x20c030a020c0d0f0803070c0501020d1505030d02060a02030702010603050607170c0a050304030305090f0a0c1d0105060412021504180506010f1407020f0604080d03050a05010b1204020a030c08030c0601 88
    0x90710340004280c035140c1001c501c07074008000c0d071b80e25112a0b50440e0b4000d070488024002d03600000c1c10b403143c0380242c2e0000a441c0c0034000d01060203900c5108158546081814120040e4030000c04545c2c0702c0b0031a4010354200c1c84c0b074000019410307560b96509007000390496091000c203070061b03000c1d40c0e2140e5041080c2e91080a261070240f81c20280800a04a40400303880a81015034510008001010410030b031042e03000b8070411969040090321b420a50b82080b4040d02c02d0441030401000400705008540c0740c146c40d00101024181401d2980c0d42041b0050980140c3c0e00010b01e00c0107581d80383c03000c0010405010068601000e4190500e511030030341e840580b8144c1000301c400c0040c482258001404001c042207030507126501d5949000141c2034886444220394400c0b00081d000640c200d0001c0ca02c0c00d00301c0d54ed24180300a584180308a01100c1c024401e960f0a40801c201c1041940350716820030354072501c001d00c40364126449460340555002503810606140e44001081110100108096801030108 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 341991474 1250 341990224 341990239
    0xa201503010f0605160f15050108031c05071e09090615110d0806041509110703021501030f330f0f05060d11150a2a0506011710020c030a020c 62
    0x70b0681c0786102804600c5c058284440110224100100341071001c12001903a0010312440d41c444550326101d903c51103810f2030482c2e9803584d0344030f00c140c6401424850b18880c0c541280080e800c070780d5003a120140590003410484209000301d0300c2c24003445040c01400e6680507108440d2440f560243c4000070144406a40303a2110120201c00c942c441100d0b03910200075100894901c10f03410303204500018540010005508101081078142110310180601d10300075400c031951031000d2400d107400105d0030700025007913000441510020800c1c0b0f100510100c50320b4070494581c02d0204007410402c1e40d05035041e505145c0c0710540d0f10518030f000c0c00340903408951040104074505103000020395402c0024001002500046810300c0e1603501c0085c5140c024408202007a039990794110000c060840c00e80c0c0911000030700d03000c40c145500c02d01c3c240d5401070790b00900900585e420031584a00f8060340c24403c128a20071312404884c4201e882c009051343c1200440216100c294031400607061103e041c404a018071030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 341992724 1250 341991474 341991487
    0x315011e1d010902090109121b0b0414010302070f060c02100c05040605072013050a060b07030f03051f060302030f07031817090a1202030d0f020a201503010f0605 71
    0x8014000c80d0440f0f036080e10060380c032950701c40161340c290041c1e8003200f031060f0510342c0702043c0044514145010a0030300c1d2071860150b1200c120000d180241e008040c0713902c05801c08280e15501070341c0180180390241d6410141c10100d43c0d180002c1c1c6040303102820068202800740e0140d17101c030b8011001c6c0b03010941445814203051410040c418003d542021381204905164480ea488241d2851510300f000608080003600300380480c03c0240100303440b6030130280d2400c000080c240441009890f070803a4590fa83c0200807150074030480141401401c010b03c000130207001c9507440c0040c07011100003021151800341e140c0c030b0441c00320035040748001c04100526003003098501008007100e0f10102029841962030b440d21184034024500e0340120028035801142806010800b000441303025880a4401c40417034141c1020302404840030b24286041101603800003804d4070000d525021840181c21a00c003a04200350100d600042e98400b078540c0c2503441920000050001000c1080a01301403d068201b0910b01035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 341993974 1250 341992724 341992769
    0x40803190e010e090c0408060c0307090608060d0602091807030e07080d0503040f0c0e101502300c01090807030215060a03060e0115030605091b0901050108060315011e 73
    0x4102e00043e40714441a000003034a00150806641c00341c0592400c03100e0615009a581c111030344103071a0040030945a00c400100d203403052403800d1040101908400004656650b140080e40040150313130350045c0d8803122282c4c2c1d06208500c1c0f500c034200c08d079008031b40d0485400701103007404c003d038100103016044010a1505160841d007100d0300140e01800c1c641d20900141081e04c020704883e04041083c6000b1002d01ca5000420016442070390780c0d0202d000c00c401741d0180141d0391884105c00d001410310342280303070307100c8029000b04176058410048274542c07814001809890856110840480c1e603100041028010f041e81000390000d4084000b403111058200140054145071240c880141816204d40d00d08818803c2074112a003c1c81040031900855610781c980a0003404040740c883c00c05200702c4c102001c26450801da00440d101c0040e01c038145a90070b1000448107140001c0044d50140b107440314004412044c5070440d8002c02c2c0c6900c0a410040600c406039940303c5039030f80400ca901c0310b685e2644c1c5002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 341995224 1250 341993974 341993987
    0x90b06040f0614040305010c081623090102010b090c03040c0b0c0c13060e0f0117010b21011d060402040f0e0606100210020c060f06040603050a170f040803190e01 71
    0xb6815828500003240d2240d0000c40d451160341c100404039400d0683c1120b0154104035114000e4055142c4608101c003403220494425011401c000608441c448100580450040040890380f20610020445102c44c001007070300d2072400d68802c0c0e00030000208000911a81c0e071421009803114905080c07405d140303045c03e40d070303102680c40302d03248550840894020507004550000700289032140c030f0400680703400c001405040000348501140c0c01804280001440c4041c42420a1408020000c99a0001c0391108c1c16030728000389403480403903698120b81c0751003030401c803008600b13494580000d04243c9041d03c1071000740c0e03030401211504039007011500316484002081c540d0740b100003552411151a0030140403460304503d202c4100800d0b100090040c2c0f020b202080c254803034000a03520b10f11a0300c2d01d0f0b082c402143c0a900c0041d2840e00015000e0340042c107000002083c900020b50443d05001313049950f8001d13a4026400302e40982d100181c808100f10301c030070718008450034900744404031800841c006050b0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 341996474 1250 341995224 341995229
    0x2d06020715030f0b04110a030e0d051b010b06042306071a040507030b0709080f03130b031009110715090203060a0f110d060305070e101a0903100501090b06040f 70
    0x2c2c5512103110030050310700f130b510041003800c0c018818841654000561102c960000045000003030421110b890b440358006030f0714403a10301c560380d031038a05030031601d241c000c11514034000505035480e0704400c00203541720006080a844d80b00900c00d0303020b50315901c0d0000c1c000702d03d89990003080140720900c0810254482040000407030700702c00d0f040c1c1e41c1d107141c9903052071032a0304000e14190001041c400420381c0103451505980a0710210f81d40c050740c200200f40d80b4054002c2d01c01401e403c071042408020402170183d40c000610b100d412034916101c190a400707075606500d04500b1485c012403150140001070303111440c0945200e1040110028940120307072078660080c1251101600c40300c0350350344d44065031312010118408403041c070780302e42034001c180015003410310068032288510400428941d24801c003003402106002d00407030707034280382c80220341c091241115070600e00001805580c040d61010700ca100800c014800c4001081d41c1044d41031001c5807600409140602c209000a2140040c5540c50105 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 341997724 1250 341996474 341996477
    0x100b030c0a0c0b070801140604050f010c2405190209101b0609110102010e0d020303010e07051b21070507090213031a041109041a04020a2d06020715 65
    0x10785040c503040503a400003a28200900e004030520400240c558005407490588802c1c041209000600d0010424070b4050341c0561030b44180400d0321680342c0d40c01b6046800c0e84900c5001030007010003085803a104d03449a000028492241c0320010084425002d1b8081508040c03c81d00460030400508089001d9008401240d41030011230340119001d9984070640303000300e9034040300601503a15585440182c40603890b40e41805907007030544020301500046881e44001100380d005508581c80c162407044040000b03080c130824004104100585175a144230380300290030081d0028002020040c0500d180841e441c11000380c58030b010301c4003000240c0e0214030302003103030320780040543c844505452078000c404c1aa480100a922078204102d590b42400f07150b24460350049000d004400c0e10482805921103080f50000d10700041490b64001440c0c2030300034150024000303800c8005441d10f8440c103000128501201428540301087c03500c05100d041d45540c0060300c0248090064107143c020390760102403000a0210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 341998974 1250 341997724 341997727
    0x90c2d0602030a0f02010e0f010204080115050d110a15030c23070b22030807090e280912091a040605031b130b03071d010f030e0109050106030c050108100b030c 70
    0x11301c414802d412010307440c82000144c880c11440661a40e000703510a108a0b880c65080504c0039044900340c0c003222045560241c8101d10284544e55105a520601174465610a0b04500041101c0c00e004403039281466807a280041d41c154807074405405002101804101941c189003540c00a1400c201a68400c542c421103400c030719214582201410344802c03400c1c01054541e04008814103a02601d03481c050400b0303890340b980c110345a190300d4124001c1100d03e50a1101c3c0604401c0e54500440b501c89004801c01d0000a07640010ba0380308504808000701381000200441e0091048462800702c070040c1e60895804136250515204000d00b95000080c0905050340002c0c0c3c6842c03c0383e440a08448014040286034050181c8807202920b481c2c00c00e80b00d0100190b1520489601024500d0300140f4500b01616008a41404940210003a01c10b8000300302265495040300760025009018100207540b04d842c4680c5c5450500000524195000700841800b082141d410802481e44c0003c0301d0300301d10000481e0703 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 342000224 1250 341998974 341998997
    0x2030d20060f07080c09030d08040501150b04170303061e031204060201060f050d0f08130513050108010c18050d230601030507080d090e0901090c2d0602030a 69
    0x400c030001039100c80c00318a0040000300102002450740d4940710310000e4580801a031a03a00200c0b11501444100a0300350784404800c0a4a0740640ca5032070717015104100124050b0a101182c40540c0130750382c003040d55007101050612904001034514000340005000650031450010002220000c03103200382800112901100d44103a1000d00c03c050050040c41d107516940c0c1da030f8040090080204e845000021140c0c400d0201d074501e441440a1082a0018580000310005440b80071a40d84801d01210800b0482c4000040c1030329144400051282609070010303456252503d000e09444d4400000000c1201441e180c5c46140b02d44841101a2841690800c0b20031800c2e103410900101c182c003031254841e01c84400880075180009489050380c0c031400c10384820b15607030f40d000c0340d4410040807003101007581d8480034410118103201d55a030001001002044a2500e511000300001c4150000e1b4071048000b41403401c9103900503050b22059903181100002d070b500d450802034490050f0000d54082000b8190030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 342001474 1250 342000224 342000257
    0x306040906230618070203071725060606090803040909030516050c1005040f09050a09060c051201080d0f050304030e0a1d1501020303041403190504050f0d02030d 71
    0xc411511503040302d006900c2d5403614000c1101804441951244940c00109025aa0300000c02d900440c600d80040d81003000c80d50394900905401c002800c008042880045844900c4646480c40d9403c05458800022040d040c06400c0d6441d0f0741000003803000341c242c00c200c0031400100320f4044503454040015000c0440ca0708480c0c6202d0308070114600d5020030145401d002d00842d90302c02d0168100c40301d1031075036000402915180204d01c1200704900320113808002e542c1761a080546d1115040744002082d4155595450854061424281c00560042010300c00b00c00c1003545540941540002448503c40580e8018028640000e0704800c010703003c0042010540140b5503030700d204100030411810b003501d41d42c044281c0541850002e0001c010100412402203011540d407a0404d41139014614556880d00c808444240c5040e44400300e10041040e10203031042f80c90100e81c84001c564400340d03078030302c1c0408200101c0018840188115a034111007001a64006041d0b0403041560601848014401c41c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 342002724 1250 342001474 342001481
    0x190b0a020a0605180c0301050610030903020709020a030501050913050d0e010c0f080306101d09040c080f061510120b13060b0d060807030b1b0c0a14010609110306040906 74
    0x800421041c00c02d000d000290070f080c02c00d03500707401040c4d0464410003109000c0500340c9105841c1c41e0380148004641c102d132944030b608040c07001c600a0044886060351a10203400301da004000381c40009503900010712507860200da10a40180b03404c65090014109601c406031983d0a08040c01c0c20711078001c001c41c07180e03400344001102c46078010351101c0d9050110b00f001c1650340e008460041c46022a00c420745e0034140280e94500100d40400e04103131251100200348980d449000c6c1060b1468013038900000307068030701001400318500010016084508000780d548046440340800c491003000390b0f2441c4980c9561000398842c419602c0603010076000050030209a03a10342c08510048424101880400c0c0003100c18020001c14403c600100300203135544d00243e03101c500c240401041c0c104510007064a116035000d11184040b07a8054440c900b010310700d6041d01c2d107070503501e01321285181e0030000e0b103800c0c4080c030890008081c968001d10881000c490100010300c030043c245441140e50b51841002d00107980e0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 342003974 1250 342002724 342002743
    0xc0503122a0a0c06030b01090812090102011d162c0a0f06030803060909010c09031716030e031c0c02121c0801080d020a0b0703181211010b190b0a02 65
    0x1082da10021600c1c2408032003105107000e000042070500c1d2660606504c1866550308548124016001e04086004460307015031000d05007c0c1150749800340745500204000c20400d903220600020300c80440500160859002641e1244440315000a022511038241259a4000048400c5403060707941c0c4443e0090020030981d0f070304400003841c142c004401c218041004502411044035403000c03a90315194514242e0b014030080100003821800c0820001c2c01c02c0c52920514814142c1d401d0500c0c100c0b80202125401400d8282c0005000b0f40c0280341c0390400f40304560a00460301d608808401c3c0d2694081c080c4007040400900404c0036084100300030070240305a0700c0783c1c459113000500c1d04403910001000414207020345150b40c05058090940075000281100070994003182c210300590b070700d40c070903002468641d13407884079000e43c8860140000c4480102448180d15a11014a1540c070740b941e02c3d0841b02c401080074040c41d40140c030354801c802c032080002d08942d401004180d035400c00d42c004a00f05003100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 342005224 1250 342003974 342004057
    0x9090b010801410109080d050f131a0901030b100905013e1005010501210e06160905010822150c0201060509160915031e090c050312 58
    0x60241e60440b91400f80c07a1140ca020036030701c2003809a02c50024940b190600821800481c0f01000801d4005030101c000d0244400b103248209103040d6683c00c40c0a9403103008200203c541c80c001990701d92580c0501c10b02d0b49491041d01c250752400ca40c03e6019148509030b00a641c1848020071036a003c00c00e2105c1c1d14100310750791030404070110f0405009609400c1080b000240c040c001c01c004220848050301c50381f03040718416501d4940301c540b1140403034a82041164141d090a44a40c0c00d00a40e070f208100f036500900134048180315104001d100201513072600e400c120304102e030340010301401400492200140112030b4004400b120418686042100c000d200700c1900c2e141400c04640c41c80b5019407000b802c40b60300b5566040c0740ea40304854a6268090079903200d001c03031290340d0b0a02500c07220702c03036081400701e4904001650108140b0005015950380f400d1450704e40d240c402103010003081701c05080c0105425002410982c40c0740c030103800340d401041c1440c109104285048800ba2b40640c00346800880903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 342006474 1250 342005224 342005309
    0x20304230607032c1605010f0909110c030309250803040b03060f030a14060f090a031d031501180e0607050705120703030c030b060406020703060f0f020f0a09090b010801 74
    0x50030250341c0b03802102a00c14071005203d00300180c0c03940107038a01d00314150705945481449c0c6c1000e044100030841c11078102450001840303010461001000150f008604603c020504804010002e45800e42c04081c040340c03d9080640400054100000b0380e002d131100d1022080d141d03500c060100c0c451403e5001c080744e241c401c8640600c00d0001d20f0366204840c02289054540558800780c4000800038182e860340175952055900700f02283c070600001e0610309544010302b903400d050a002038070f0640d00071007610360010282c004100340f261844840c90000014101403182031207039051151910300c010f02000601c0b400241070b6003000350500c0364010300201440541c0e1242d001c0d0500030000c00c1010b14800c0402e10f4140f41c4038841c60b0440a035001c03500158001c01c0c1c854119030b0382c1409440c04881c900320741a292440c080829140c0d00240074414180c0c5026a120f8543d484000c143d26036950140303101170f03c0c0002042c0a41d88c44049541900d0604c100190341242c0b4101d140130b4400c0c4081c94012a8a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 342007724 1250 342006474 342006551
    0x7080c070f03031205072a0c140f09011203080a0b0a0608060301050609041113021204051f06030308060f030a0203120c0708060f07030b0604120602030423060703 71
    0x281c12080c01582e0090b034420002d1030381404401c084500940c0d03000049541840d000c8a0b0781640d07000031024400c000c0c01103840c2800b640c0c61140350304054118000c02e042800c006052820308e1501d001d52048211640481075140c20125408815004400b5041141440000c1c00f82001030300b21041810007d0110b108031555101c0c0244008016207900344254209000f2034654601b2070070083c0100d40000300000180ba169040102c01c050f5080e690034625020b0014048801001030803600c614003801c0500100f070f0040744459980300d088905000c0103403601c1400c0c00400d51000c0c4d03141c1e004900351207074001000d0743da000034500360780184000d505100700301032220421001310240441140741c1c812541a191036600183c0c03550412280012201a800c000038950341c407079041490f16980c0500540d140a4842a8ac4482d80654050680e00940c0000070300c0308000170142c0d6640e000701017400c580e9210014003140303a210320000c5c05030340030192106030040e020080122152440e07190302402e11010f51 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 342008974 1250 342007724 342007739
    0x3040807030c120b010b210405030901300f09150b090612030702040b122b03020f07060b040b06070609120203030f0109090f020901091b030b0d0807080c07 68
    0x548a000486103800b00490008100742d944101c8050b01d60f2202d07243c1010780c03d103640f910060300700c00c455281c0c000804121200030340c075008903607010707038010b002843c0d8514100340023404a40b143e2034032003090614110b10151000d40d00707041e10294500b04101107203880c4507000100203400c241102600c0c040c6050380815150700740b507004141d040d005685140300c554880080111f44421441405a250002c02a0800601c0e00354442701090b60010305080040c1101890545060052810207840c0b8101c0c0141860500b041e512064503840310349411340c60a18110310b00265070150741c100078441a114004070025907183d40000d40300032009070103070707407106030314140f120140801d02001d40b4810700400b0501c100e2840031003141e00c113052503483c6001e281d28203c0ea83c0000c1500303400c207540c105000700c00100181d543d442d02c0e034002e020b401c80104501d1100712452440d20303031842e1814141031400705205d0b156140c0d00f064484240e0825600740d1203210320b051907901c51154605174100c41c05802004180d04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 342010224 1250 342008974 342008983
    0xa11030703061803140301050303071104021b160f060e2e090302130b060301031e02030d08040204050f0108071404020c03040b1c0b0306010b0702011707110f070308040b0901090305030408 82
    0x841c0a03503503e4245203503178503040625100c02e0040030b425400400c124000715040ba00c0c800240c0304058001841d00c40d01100000000d0181018040a13800540c518158a02512280d10103009180c100400713180c07a254020304008a18411030b80074140400b40f1407984400d014920400440d0b00c41c1c800d0700300c01c01040080401c8050b000c12403260b84d80c411310381d0311801c1c0b5118681181c072000e0b100a1969003140c072500d8280c400848604200d0168003407400040c0c4003444040300d42d03600c540b9200d080c1d040910410040d1140142104070510004004005407000018020210355000080211950400c000309019214600b21108184000034001400380240801031146048500b0f140c9141c1320b00d00541c2099501e5807807026810344c440001400007e80c002e0040890a10504200b2404c800032810025a0301d004c458040c04280c01110450b1205000c1c000b41c081000f03a1070180c60014115070714500c10380201d00414808007004614060b05902a00284018580000440b80c50342d988214241e40c0c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 342011474 1250 342010224 342010271
    0x103110a0e0c03040f0503071e060c0507110103230103150507081302010e0112090614060f0a0e04020f060c0c030c0616020904060f0906051b0403050a1103070306 71
    0x414520a00041911a01d6401d40c041c141d001512803560300c942c2c40d110049240001c040e10b1a0008021075400100c0181100110640c05040c40c8003c58103814184129419a0505c0041c44020811100018180f000d01c015013002402d0010b1904003903000264081c000012410001c40603800107c21700296074058032401840190a011340c2d0f40b0064115084c2400783c540d0100c0d030409011403001580927601e8811809810b260100398561105003020558610a405036601c0b0703921034550043c40c510880c5550b0051040d52038028008031360000c07450390b804030321480304950941404a8210368440e2880000340d180106401d440e0803800204a40303a49603030140c04d1180c8030300c842110803030800c502136511002001c5d00690b15030075a5000d04c1200c62000308112440e81ea00e21203407a03042c44621038450014020f0380c00068500d400c04900d4100c46013068030f070385e4010381444100001400000c400e1421603110440d80d12161409001c00e10780303a141d8000402c1c0ca814503000106500002892200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 342012724 1250 342011474 342011479
    0x1b011b1b090e0c01020a0b0a09030e04020f0703090e10120c05040c050c1501030818030a1e06060f08070b0c03070b01090e0d11030d0b060903010c0c15140f04020f09010311 75
    0x20f00552801a070303132072a4000740109000300031800206c0003032003640940c03050384c02810040c0718451014000780c00c0368403401e4400890f8001280d000145544400c1e08030240c404012034003030300d0424940344820110300780700c2c03a02040340701da100b0b100b00409450000c3c0104400740c010f10181010a4020b001d80c0c21800c00010170344642000100003040341810340307040780c4c5c100e584240303070030084000041540c02c4a5201505445400302003000a1155200c41080c02a40d40702c2ca40b548600d46001c2003660035030751103001c02032103400041c0082d81d000302d520703022242104103050340c0d60745489009003140101d8101510380c10b081400041c259100703400400300980180d05403004120800c40590f01022100520886a03005100b8400b5003d00c075402000221002004141071141c1240000d0035a80041c2e60f00000402c0c00382c000b8108814a50212248008a0345c144070642c000243c1c01c01011004180c2070410b104d4802040070754545900020090f8006803100c0c08542c1c40e8140b007428685800140350 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 342013974 1250 342012724 342012733
    0x100509030f3c0d20030306101b0f0605061c030e19080303090724020606090a09050a0506160318080c1f0b01021b011b1b090e 55
    0x85552804181024103000802d01e410400d5503203100c40c4800c1c44221800350088444540203007140d14104500d6204072019030b50030b40e000c0661042040706801c0c0c0c1e28030381d001e80c3c420b1080c4112036032151001c02c1c000c111450981c85806000d5640ca07104441c60001803c0d0030306020031203050200c00e41119100714030941303540100c91000c2d14184500c0d00c0e50440900055174007050b00805190202480780300f1114003580007200c54690000500f0341d8000c0d02c02c541c9980c002c41c020400000889031a00b01c102c0c002ea041034032252488070194840c080104040d01c207902c2440041d0a00e5650b80c84150000d0300a81214000305241c80d003a81d0b210820398902100c01800c05040404500c00e0003200d40f101815400329540401c80d07a40c3c222030790800d500c0070031103010341c01c0150b1082030300000a02d040c020a050109661546400180c00d0419190340d0100000c451400070400781d810a251450002080c0202d507210040d9080601d07031780001c5450001045901600041c06000c1386d084602071030b020600707a4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 342015224 1250 342013974 342013993
    0xd02031e1209071409011410050405120f010507090b121b0a0c030806060c070603050a020f073504050907020708010e03130b130509090123090105090c1e030a0210050903 74
    0x4041414240306001c4c7d0f20781030618402e80381c2007501c00004000c4141c02c000d406d061312807000403c500d48044204049a00075101c800840c0d90034000da0b5001520303800c03e2004a41007482c1c0403a14821090b91030382c4c484802000c594400e5000000110016199009a46400403104020440422a00250009a00b010110b030300381c90034108996500c84d200340142070745403808000382e020700401848021101e40c28007211141c0e0795518010700c00c1c184034000180b4010000304007042402d030b01d20050245450b502d500e0805904a0030111400c0d1402151004170560318200102c0c0b82c51115004900e865080c035107030322400e0f0703000005000f98140491340b1012460b164400c400c5140140450245001c10740b010820550030007888054012443c4c4001243c081c0098029001d804250003140524003406401c0065041c0c0c03c2c844c682e082285100608544450700f00018030050015450101c0900d0009400700c00d44d60410484c042c4a038042c5c0120907c004d07a0001510a82119407118040c1c0070311500d9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 342016474 1250 342015224 342015229
    0x1005011806060e130605090a0207050601140102071202061e09040606021f050c1902030403060509030306030604080d060e0a06030c050a08030a03020f04030b25020d02031e12090714 79
    0x15102540c1c91507a40d00200b403c504100102c1c082c1c00041e04107010b0b039480c404105622801c040e41d10440140c031001d80e80e000240340541c41d040c0305900035180d10b031a0740e206a915a90228451080300d03c0394031004000302e540d00007e01c25200340c858002c0c0118401c1000c800c0d42c0203900c01b0300300c1040c0031501000450340d103200c266210400725540710402c0a0341151415a00071a610203030300200e00f1140141130180e032400041d03101048441c124090390001c50100200030160040c03986c0305000c0c00182d415401c10201003581c0e1a0060002040d0940104085040707100c0c41c2e120310014442e400702e051840c140300c0401002400103010598400146410101e4039040070400002114040030040d807510020520880094211480c0c404100608100000205215690365405403014020b1400c46050b5000190249082800c9800642d00101c14800c0920303000f1050720700c0b1008020310701d0a80091801c0007001485045002a0050740100030b100c10100001011400c4e544408000d89480001104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 342017724 1250 342016474 342016481
    0x20f030f091902370b0c21034002150a02030a08041b090c0801080c0303040302040b1c14060702070509070309020103060801050c0d0b1005070f1410050118 68
    0x402a400c46001051441e0101c13a01e00c0641c604038140601d2031440480c2013070801691520b60180e2011000840c1051440805100240740c0005420306400101c201c3c0348100100e01009080c19880314501d0f0b094080c7c03800e00c0103e42041071400003d5064408138802d825500032181c1e005a001d8071a0f4420180d84411041c200c0782145407a400541c00e0a19104007215805402001140c1d2410000a22504402c09072800d801824078032001080c1d081707a8110045c0240b00580c171007486c40d4000e0751000c030540c602004842c26079030191804a401c568a102041032000183c8001800b0024000047c05001030070340a540c018180c07a0603200d06480c0d05000703c0c0c1c0d907221400f40d645c0c0000d0003000b00c5d42c40380c000d500c141e910758418100400c02c141e8a217095400c440007154080740301280002e001c0d11100851007030305840030044844241700942540001d1541c002c50134010b061400c0c03084c0310014410550700c0140055000000c4403014038408043c000544000e11401d00107541c0e030340688407190080d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 342018974 1250 342017724 342017773
    0x17030402010801050904050a0204050a05090f0c0f0105090612040303022a07060807110d390b04140105070f111f05071202040b18270a020f030f09 64
    0x9449002e140d082004002c00c1c0c22000d00112054403a81000c1030040e1101d0007018424071190100084a01d04090034504040100da01925941c215030b00125a940d91140c90006800b420700e0b2450312074030010041040c2d4852861108140c0c0c41c11400c200c10958560010402e08803601800f02480b03640100a130401802000d20f1200368114490030b022961148100b65400381c11807400c5136400081008090801016102c1040010180d520756055060007a140c1c9203000500c1030041d40710030701c00060718041c00c00e091000301030f0006134000c1401e021040814030703811020200204000d080c030201c090804000c107682400407480c4103410f406009008620318800409901e821800444c0740c0150304020320004041c00d050081c0c0031030203003110880d44050000362905001c40e0740d44030b00c1e0812005c2d841000e5550148211180403a04103a90705d130043d85004a0307030300e5007001410340f81e07514020041d0141c2031a42c030004030044100110f80c2c01510809024403070710f03008d44d07001032003800c62404a5070004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 342020224 1250 342018974 342018977
    0x6040306270b070f0c060203040b01061107030b160306030b01090c0e0909061902190207091a03031e12070e0a0f1d090a0c0f0915120206090a03021c1703040201 70
    0x10b000245915029609a052850803440c0c040745003c2107948101c00c0360010781d0f0955119140c0001400515041071820300c0380e0002200605060307185503102219040010406100304a003102410b030405d02941160003d9640141044169a154141e9000801203e0b0301c400000d00305006c500c425007440d0900350b000d000090040d00041d91240014107040400030f20304803c0300ea08100c3c0502c541e0018440312035021095020300340481c6040c0c02007045c0c0d00152030144940b012801c030780d00306940010480d824200f01c07540b115510b90300041e00801ca40503146511069001a10412600c0c550000e004110b0000448002e00005e444030800c0c8007c000c6401108082c088051040e15810b03ca90441588040400304039802da8041d90303151265030815034070600c4c802e02c11140502c6040780c2800b54014003503482c01c1030800b0074030b0b01c1101100010343d840080c0c02a5000180c602881d120001440059900a40b4440c0c08202417000105900107829003075902c040060240000102168103c3c0d01440c1c05 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 342021474 1250 342020224 342020243
    0x16050a06090504020a0e030f010218040515240409061706010f14030c3c090a0e030d0507020c10021902040203060d0f0302010515010e030d18050604030627 68
    0x900c2c050000a510610019052000350941980c895070204280304180020b03900150700e912001840c41c10f449405048580b0a40c20b05e020403408070107040018001d04401c07142e10080c4100b40303115076100d442c452303102c402c1d502d400180459105030355000702040b0f4800da90b544c0c80c1c40c00204412070f205c050030300462004502c118010010b16000c4d40d540004184e00034162640d428080d0001040c0002c2c0c0c81494091110148102c2c48082300301031104403469500c0f0078900494602d10004401001c01405600f80c181d640130144082d100c2042a00c01040c81414104520b00380b03484d020755200e800c500024451000e001c0c226280d2440410320100300b0182503114602c944c0e0650800000e50001444543c00130404000c0e000428203000804410a0003500001900c0c103103100c03c4400d2804200500d4184154400c40314690f460018010013117000c3c1b4504900c80c2c0c202c1840c0d040760151250b102070b41c480c0340072034040f00340314655000701c1c2070807a0350b110007030b01091205605042100882001d06403642c2c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 342022724 1250 342021474 342021479
    0x3c0105010f022e0203090a060b03030f070201030f270501050a1107080a170408070b01050105120f070201150e01080c010305190b010311040308032e06031505090916050a0609 76
    0x4070041551075640c6024103c018056041940e0412a01308481600c002d500c490716803403c1c00038510629080c2c80003070b0040c52404c1e001d5408182513105030b01c8001d041559400a400f10517410f94410103484446400e808160401c00124000340b6201c10400c3e100d030352826010400c128058820151000e1a00360b07081d0038040e00d03880b0a141c58012450240078080302c040003500d031414074400300b807103503205025013074581d80b050030902e01d0140160083c07410b00c2402c00115050514000c40c0c1d591140e070b80080803190b80d07900743c002c03400740c12710700c41c114052450040d0100d15000e0704098141690310711800c817005008914011401d540b01954402c00301010031059400107030b2142c00c04480f0240604021480c2c00c1d10310344000056120b9401919800404018000b008451655500318001c41600d04031010b1f48016220f194103c5a20889090640e1460702c00d0f5000d500c0c0c0160001003000500d0f80074107180c001c85042e251403000000b600301c507051400114051030896804400d0b15000d076a0049610b0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 342023974 1250 342022724 342022753
    0x6010206060f12030403050d210b0901050d060b04050115170411060a14070f030206072d090902070b060a060203031017011506120b040203040b0705033c0105010f02 72
    0x43c440b02901d040707000401020010074420000e601c4e0812065440d00c01c000003600d41160883e803004200700310207061803c091156038811910506652003220032204600b01c40c0b40940040007200c01c0b45402a08010000403160180e5404100c1039241e0344482c2584a0314461240b0340322000c6034001c1c01c103c024924007000d41132000c0a026051003c2c02c040740416010182d81d000307508444401c9800e40350210108040590501400760419034504003244040386e46400c0110001190580e0364031104501e070041030300c41c8500d1940340142407045e0f04551307442c12410500c134181d0f02180c800340500340d80c410000e0142d200000310303031007210316010ba1b030205411302d042c80030b031041c034114919000e640340d070150880c8002302281240140142e4640c560040103044800b0207584800d031042e407085205004100100e405596036540c0000d4901d041607682d07513100c0940e0044000182c1000b048120001d440114000140d0716001ca8500c681c085c0d030441c1e07a9540111001801c035a45100140c110000a45400c03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 342025224 1250 342023974 342023989
    0x20a14160609150603050a060e0d1d06070c120b061f05130305100e01110703090b0f12090a2001020c09150411040906150c03120207060207081206010206060f 69
    0x46110722500140b0b80c0c3c0000340042030714580c1e081519150005c020740e034100031442c0301d210000100807015000400100c00d01914900b0a501c4400c82c180344480c01c004a5506c020071584802d40c05032164030741d540c40d11f64a501c0ea444c00c1508844002c0740e007011034202e18094102c00c01c10004c001c0100b4202540410071500c64014100030a0081d00e80100400061002c0c031918200c0c0745428800181c0202084089003500d550f41c440700d00507a020441070f000300e81e00034101c07000e6903400c044d0981e45800042004880b44519803040551007a2070701881072500c4041210700009018083c1181c071200c0d440c0c0030030800c5089500d0f0a01581c0103200c4800c240c20050340d400e5001501e6520a40c2c8103da40001c5800d0310000c4120b0b0704001000642480003180307903c59400940090300c400080e100b12203201500c1603946030f4002c0e060040c1411800030104003501196001503001c0c40a54440200345441007040d00100313105441403412000141c2c0c0d0354070000308244250002440640403440c0b04080c410305 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 342026474 1250 342025224 342025241
    0x50f03040b131403030a2a0b040c05040c0f030207050f010516080618040b070201091401020a180f1e0b040f06030c0810090207050c031506012606120309090109020a141606 75
    0x601c03140034074510003447c4085521800c0b5024a8116203203107000c0c600400c00201d0b079042580300f00d18000c0031031201c0303038080207803a000c9405050050b60740103a8101039182c04440c1c0000c0640358241410841418038886424003810176a46502c0d100e525034000304446c002e094100c8000644020b030008000c80c44000d0003641041e164000025144800c2d201d042c200f844004000405039000106600c02562103000050300c450460f1500c481d96007400300c00a21420315102d141000c003468001c403401c0b10765813801034005210008440350f490b680c410301486040316500c10740010078589528142c106009090341840340680800c0c0008490500d000d04000f50848030040d1814400c98a611007261420080700c01d2410407041e80001c2403500c440010114525a10725840c508640c0340307807000b8514542c62150308101c0c101c513495030095071118403a2443c05070340c40c620343c40404400005455440c0741d0040021902030742c0c0c0c055282035901241030360b901c18801449104104402400301003149503015014 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 342027724 1250 342026474 342026507
    0x90e0a022706220f090605030606040c090e04050703230715030f0f05010504050112110f0f10030c030b0d0b0a090f080a0801060f08070e0d050f03040b131403030a 71
    0x400016007881d0080100f03409240580c0c0000030f100340002050111090028501c1c004c06006103410100865281c1501600d01c80c01282c50f84980c02c20307030740204408000b411610f11001403038605810b200d0f40e1450188816074000ca421005106621140080791a100034070700c0080c4210303854601344618110008440d0b80405031341c0d03100c081c052002401510b2054030186404182541000100b1088443c183e00500403900202c3c0703510300003403500400b00c081603400c0710220320f403c4005001c1207005090600c00c81e1300844400da0b041d4500c0c1c16500234000d44a15a030100950441c02e02030040e00482e001d8050007a05850000801640c0380c1e03040055580e1040c03e01c2d036050001c0360743d000810f400c441d0041002c980d07604010702010303501c400b0588100720545008902c0e802d2982000d4241802c4024a500501ca2444182c09205081041c803078411001421650f0f660380c2c480713500406400c04182140074070780840d0000342c204640480750200c010014003031440d00d0006001564030100c1740007600c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 342028974 1250 342027724 342027727
    0x1803080403120608010612020f010c021806030c10030203150105031003081612050c150f010b030406091e03080a020c030306120c040c030b1c05030d020d140106090e0a022706 76
    0x4d01040d0138000c00000f004da815018003408018410805800301c3e00764000e0401103034290303000143c0c1d5046440d003030080142d1140c07200b1391a540b0111342000310082c0159007041c1c0640710910b03441d07855802544101c0c80c0142c00083e00c4211001103549100c240c64460301070404000920110f18007078014903c00306003940382448040c083d614105c0c2c001b82d420b40800030940206506c852400b003444204420484103003c40000d01d003503140300c600035806005584d211000840050100300d0280d00c140b08580d0040311161000b080e61344200d216003400c00e80ac13030005980d40007042c000140c84c001c2e601d2603100000590b00310355448050010303440b00c038080e41c905c9100d0320f0b071040880d4627140302d40383e00d0340c0341c50b517012235000c40c14028400050324a5210503024050700245038003040021040d211140648040540c3d20800b0381002405403d6840000c20403904040001540701d401042c07100854807141d0304c1c403910782c1c0d0742241c2008a00901094005180c21600340040409000d000146071001c01400103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 342030224 1250 342028974 342028979
    0x20d180f06050304050601080109051203070c020a080c0a0605131203140a030515010c0b0a05060a08030d09020102150103120e131b021002130b070c0302120c010318030804031206 78
    0x14a040202a030040740854000001e10080c041d0900000d805070030090000e00c04c405241d07403469510003d020360b01c1c42c03000c0080040381c0c3c0c0034858150a900f5035002000b984116403180001e13900d565840740b0700c5110711340c40d160025a01b0f001c0d00560301031030720301c4502c0300e00b00d4a8481d05d4010b49010b860304500300300c142401d000068107400080c020213882c950300061907103040044003082002e03254000c0e051003040c180b02400a040f482c0d5070390740070701451804a50390310717007102141048110380c02c030382c00034080821114282c072010703800300601c10f000340d0844042c4000413094144240082c00086e004104400c1d00c0d8801a0148000009100c2e014104a0382c0c100c0180785041241e003540d5500154104410000d80c40c651f040040f00344820522104624004a8512403100450244140d0044c0240480d98800388804401e0a000171900905803800703800c0c040003020b880d021703000c4a1901080c94401000d408070140001242465415151620640c4980d1001d0750802d0130325100000507601d602c0702 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 342031474 1250 342030224 342030239
    0x170610120b030309060a09030204051305030304030e03160602011a011e050901140703110d0305090c120106080106030b0a14060f01050903070906060c0302010f1503020d06180f2001020d18 82
    0x180f00311180b5607101f014050444c410401036600291040141710001c00800d404640f0100c1101c0d005076140c05e081e245111600042800c010740d489126542c88000e810005101e5019003241030078090074000e120000241400640307a052004400071000e00c003070441c00410900420080c84050f00504060a5808012100354095404110101d00080e150b240114090408100e49515230415007000d0240b8036200a403260b9076581724100b207200d541d2407009000d18600c00e5000f003000d4450a8028030485070bca0030b050380100340685000458614244070101d065000346103050082c240280983c00d98a240001113a482d004010200e9060061100c0003030b42c100c05104510041040340c880d002d4421041c207010f0b0840c0e00c581c000c00c8025040c030055105a860900b010001d6942c1200c01c04000c2d416400c00344002d01001581e9840f0a00c0c0754088004d00074108151020079200b64542c2240342caa0182540800c03c072003132000d0141e84a80400d40c4034501840942d100c83d801c0c0c20201c0017180c0c0d00d141 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 342032724 1250 342031474 342031477
    0x6240c0b01031101021014060f010c0602041d0903070804050603180703030914030304030c050d0515100504240501052d031e04050c0d1a07170610120b03030906 70
    0x40f210420a00e1084640756014000a4030100d4402010041112103000b910840040107007690300c07520400d407080c42c1d42d0303000c0c00d500c3c0d041d50b4115101319100c41c0c442c0c64002070380790040c2048481d1000c0100182c5114070000c115421580d003c04120300b80342c0f404040c08000c1e00081c1c4a240c0070501500e1100112508110390301c0114006c6d0b6400703d802d031401e00081040740048501701d020383c00802c010b0003c074403d06101c0003240c0c0199500078483e541414030f0360510400c03d201f400c21541c03032030a11090984609001060703903803c9401300aa11804401803514032a0071ba003050014405a008012540c041c001403d0007400320910900b5880c00701000c1c09414542c01d1183e0341d8001f0200500c406c20719011080814600c00301c0d0035070560b092a88a255031001034020145c41210707080719940c10450000d00d03640768000000200520760411482c094034016480d0012000c035060f0f9000183c0501c1e010ba90f042c1e008a030303a2100500300f50742c01e58550140680e00b03a100d40521042000058603200c490 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 342033974 1250 342032724 342032729
    0x320301090303060501090b0936100e01090207030f03050603070b0705011d01090203030d020705010f060806070f031b180e0f0a0c020111090103020a02160f060206060406240c0b01 78
    0xb0790028003a418000050031b03100103a080070b4103600d401d001030741054880325000d0884000714041880c1c150070b44544500c06100002003004180710640610242800300d0749000203582c0c0f03c1c40000365903a02d81030124224021001d0190000d40c035140700c0b013140783c020390085801000103400d40314a19140d030094812540000702c03c49940c0e41d5000a80350001c1d0204100d0f01c00310034040244071525881e00001e5a034000d40c210100041d60000340b107810000c3c03d600401061030f03220001e05c012541c841403240c580100329501d40110710408224081d6078071030f01c00c1821000500010740c0031450b0ad100101c1d4800d21000320620012a42100400c521042c1411180b190340185040455440d044640c1c005072108680d8900941e03041140003d8203244007019525101da00307180058171844000fa0413031070442504030303000e100026540701080c1ea41c8005640c0d000d90350b480e02201c50340d480380c905010440750702d441826080e40c401000b0040300380207509814801010b41c6010304008444e40ca803181040d00a9 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 342035224 1250 342033974 342033977
    0x10c0501060b0c0609011107082101030605162c0105070803091c020a0c180906050708061e0a0501030c12051609091a100207170d08090303013203010903 67
    0x100301d240b410f04041000c00e80c0050344030020301800c002c0800001c803500810300b00400401d404954680038842441d000c6403480300d503038241da0055a40c5d00b070540050206484540301542420101c01103140940000e80c010200c44a0002030319052486000c0485180341e485030410a00700301074800714104102a60042c04032002030103007411803403440000642220480700564200032110004210304003400803c44400c640d5510300d403c0684817010007807036550707030081030315250505001c25140d1241506200e89019542c400c0b0740711040f044580841100d800203907111000b0181800301e5486500005013105890801020800307072040a1015140f00300c2c1d0648596202c55900c3c48080d510183c814002c0070001c0c4100000b450280205680c035005100142c000d5650208040e0788070710030400d400007072102c6102007a90040c0300e00f6158441040d0490701c0300040008020808070380340401105d040300c8650141210745408401d6441c1c04422662076054840050300c0000310a49003809510b0144e03110303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 342036474 1250 342035224 342035227
    0xc031d0d0806091603020d061509030308060609030c0d06022503030f0c020a030c05030408190c0506160b060d150c0809060c0d050402032b02060a020f04060c02010c0501060b 76
    0x20000082109500400a40c40350700003e0900450603007501004100340181d10f0056620800c0c0030001014001701c0d8070421400b11440e00030109160f100c5c0f4400107507803180d0303201c580c00c0c1c40d450f0400c030b440c0c010380789041e6140d04100c238000c0755807400103a00c00009124040160030729204e10340000349076010804e110080d040220b030401c10503605204a0300d410300b110504010600350b00400940e02c81a001006042c403030000c0000d030074000108152002003921504031030b8401e1903a510500c01a490a2080300c0300f40140d4004500e600d007010641d0105030440c0f00c0314628128a03110405a980007030440c9401c001089a01d41c0410501800c400e01408540000300d01299419002881e0b007600800520715600044103200480e0a40e10883d049480a03000200d02500d85000080c20b00100c022203a015140001102004049816014402c0e03482502512015903900c01c1e01b030145e105e0000642c11480d000c02c0300340300c07060080040e4a03140b401890120100410b682da01400c50f1015004408540b80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 342037724 1250 342036474 342036493
    0xf0d03080906070801061e090e16030e011b0c06020903031b0c010309081c0605030105090a0309060e21340b04030b1605190804150506130c031d 63
    0x420000c0d180c003c652882c1548942d8508800241100030010f800e0588418118050021502c1000030001030040c4040c500381505105000608641d01e0283c040046420100e07141d0217500103200712440c3c2800304074201ca0041151070b0480d8070081d442c0d02222070319428084da01f15500c0c01c00c050f2a0340e184006000080903000c2d02c2d12031034000283c5013241058200340a000000b000803058500b0203605064030b207026802003003a90042d010320382146401d507103441c0c01c01011440001d400320400c2d0103911107084d80d5407200030807184d01111520007070700400b4882400c2c4003d194001003003040c0401d001603c100c0c65040031134900c1040034112100e0f280d110307020300398840004e1541034002004007103219450149141d4a00b01c0d5402c00070302001003000e00440a4210383d02a8084441c90031400e40800c003c102260000b900c05c6205031000e464214030581c00300c100f61024032525006003030050094141c213903041070003c050300200c06054101610740158802010940400c4052104264040d069480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 342038974 1250 342037724 342037741
    0x305010603050a1110120b010207030b0f16090f0b0f0405060a080103023303060a03050d0302040e2811040f0b030405011b0815030a0221060903040f0b03060f0d0308 72
    0x14807a10389180305d502081d042107407242e08a6081009004411400308024240e800140c4c10034445a0028100300d04020400c1004015030400e203102c0c01e10000d4880c81c01c1c420980c00c0318141210b001d04002c108201005010840c00b001c040c140307441d8040000d40c5480e8890006c503c280d0803da03110408a16a10014030840c50700ca06400409103070304400d40c5640145c1058401c07460a40706210f02000e4000002c100161034003010b001c050340d0090304a440700c42c00c0340c00090082d44144a980300030605c1e0008100e0072040e142d003512800301c1056002c0c21094080c80d40f02c00030220a41204030030f500410002510001c2083d0100003000c0d12041191031740340c1800c003075080d04c2c081444c4401ca40c04000b0700740143c2c0d801003400d941080d400d04008c003114170a040844e1400518480203548015511500028a420403e004011100520030b0ba19992036078404a50b41e40128099040c46400308001840740000b00c030040d40d44600020300074400b002454010501001d80450240d0018841000700036406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 342040224 1250 342038974 342038993
    0x2041d160803030910090204020c0f031b06010510121e1a0409021807031e020417060103151104050a0303090e01060521040204020d06083405190305010603050a 70
    0x1010840060340c03940c5030850700d0a803a90349081281080346c4d503607400c40c001d40d144c2c0e80c166500e000f1007100312180c5c81002c4008543da500494400d214010260880041c50180400c2550494101800e00440528a04002d03100229000d140c04112651140715200707429000d4290034905006000000e80c1c205000d4003400340d100f80051040c0a103051031886401070311100341e9019a03210341203812602e511468000c501400d05840d9400090820700c01090798443d0507070043c03044444001030340803a00502d180c42a16941c0074440504881804010b10003407402d07a8011490711012042c2c2c861800703481d139001a40c0180d4903042900041d0322134070705002c032085107110306000d002075040c428104280c02c010050050060f0302c4210300a00b81c14080341c215110b070b8040e2602401028418010700d92600001070342c4001c82d0403008002480d031641303903c1e201e20b907544054110303400410120401e4140300030301c9003a80c1c0c6002c246441c400b00d140c0010102c0d0782031280d01c0145100741c020340445400350404032440f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 342041474 1250 342040224 342040229
    0x7061110061a090a09021c140603100c0905130509160b0901140904020315040609020703020309190302030708030d0c1d0d060e030406021e0a0c06080402041d16 70
    0x503601e440d00030300044001c41c0d01c0c42042259030010300c0ea108828008903440100c2d5501581c0f02c14000314040d40c0f9040c0030075100031100b44605007005416036000129440010907185140c240c4c2080064090303c20954100050914113414409440ca590f50f0100304006202c2c02842e000382c0e03072181440b6503004203115010001100da41d800b50142e081c464500c010344600d000890620150081311050804124251414020300820843d12032401c00414090b8001545420707101e41e24015000c00c800d9014402d41d010f65802d070780114100311140d0300b03018280d1903c208103c00c00c6084900000141d42c10403070304002d44000d801560322064242c08a0003510140444c03041440066110306001040228500480301c004490f40481e01c0d429007044401884031626000d66800300040100c1c1d09500014441031416240803a034602441e00321003d501c40c84070040c003c091000c4428100f0a03180b04110385900540010800600446182c0900302c0c0043d09421011880d00b00407883c4400c221800d212500 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 342042724 1250 342041474 342041503
    0x318051005030a0207170409020d060b0a090902090d020306180111030606390a0201080a060f150210020d0b030c010c0c09090f02030115030c0f0302060a0509030f070611 74
    0x40d0950250000c0e0803404001c0c80c540c2c5071036010551340c0a11900b109114110f00500c114180c0e07541e140d118050103036124013030380b902442c10658001859540c140c01ca07918080035039614540c403800c210fa010080e6000d01510741e48038401a0304200942da09028903030159400503502c0100482d50f0b42d8607030070f4070507001e1510701c125410700401410b91140d030304a820106200c0f0b8040c0ea241c00801741500358150403094400039540c240a00520030400090b0102c029000f40c0350040d044c0da41603035440076540c0c1c134042c02404050100040042d01144c0907603141b40c4032940180c81d1011126510b07401281c0210310304802441d265583e40805080a00c0040b0380e4200078070b1f0607040d01b000c40c2c4507a102e1030743c40d1084c0c18125070764051782010301c0301c0c08203409203a960081c000d004025000b82203030b10055541c00117075020304e420140011050070f080f0825003143c1d40603201074180f450030401a102031700050718103505801004074000e0059400e01c10b07400500402d44a1070f107802c106c80001031905968194040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 342043974 1250 342042724 342042739
    0xf0417070501170702011b021e0f0a0201030203060a031713080606010c03140909040b0a0e0a0b1306060e07031407050a1d031c020a0215120a0f0e0307031805 69
    0x10599010f0011020542108042c40e51515841c500f05d004042082480c450040206659501c090780854245c0443c1c0c52000300c6038011440000341034640d05004114201a802400142c00550003900590b0317001000170580700d4640d5407a229041c0c000300700300d0560381711240001c4603515102a1510803000d04802c400400d0503140c80e40001c0e10840c601c900160500003403a004854000e1030f80f0844110520140800502c0d0619152032a148101911005e8001d4103116404200728030000740410076980201040348551103064054100028103041518074075166000440c3c0015018113243c0680820f0f940021424410000c2c048400701c080c114404104003002a15041b5900ca040c4852640e0058030a10840d84400d00185c5081c0c3d0704208a440a120950320400d866001310f98985124000c0da07603e14111398480c0350214520503100f41c0c180c0c8030b00350070204016200a6018605440712590000b6420407004071103441c40e00540011000118040c1213007418019000306000108002d8400d131 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 342045224 1250 342043974 342043979
    0x409051506030a110412140106080d020714040b0d050309090a0605150f0c0a0506070f020109030f0804170f0417121b0109060912081e1602120f041707 66
    0x151042c8400b4184044080d11020408203036540c0c031003124010304295075450074001c05440d0443e0800306840410105518003200002c2a0002203100c0c0f1485036207034090f250050411190100c502181030f03403517030001c0e603815100445807208507940c00c0b518000c40046890b020200100700c50740e900205103440c81c0341442c108102c07503102c4808020084500031340f92a100c08032104654214081c4401c201c405101d426519410710001142c1107000d20459994030000c000d000a05900f6119204402000522001d9038001c4844c410822950060301c01c0000070400e020790101c22610340c000c00355104080300300007410461080900602d06100c4403020240108030542520a8414022641c01c00c1400d213070801043d0510b042940302040c508d80c808000c00ca818180d041112190005001c16400701d2414000302d104070035003100e140c0060260361070440311640c0b400c0c4480031519405c0c1451056124001e0040c16002080000c1c20110f00804601a15140f070241c0e2400220355241e40c000e80c41d048600103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 342046474 1250 342045224 342045229
    0x602180f03100c031e02030105031b01080402012703080418150b03180d020705010e0105090a170a06140402030115060909110f0307021b10020705240307030204090515 73
    0x2400d581c0c0ca00910016801038402e506801401c3d40d05d08940180c000324a441000c01066800340d0f044e40c00070b4048071503100d0040c0384410403010b5904001d01003100d68000800540c4100c0760805900d20b024071040313500d06180c83c2c100703440c0c00e41d41048808040c003080038020b82040d1210200084c00c0c140d0280460210840e20300004650f500425818950000018a20000f1001c441e680c02e8054001c660413142e00d003400a4455403140a0540000c2e40b90380302c480250f21420903207900c0c840050100564600d05648102040d05080d20040903002d4122803202045192003100c00e03218078280140c1f101c2c60144101407c6400e41043e2400304000c5001c240103541d880302c45101130300d840304800940301e4280c2d540740700940110709400070448400002c00210940c00315901c00d2056284002c426042c0e00300301000f04000c150f9400b00016402032904100a00c0c001c000c040700364818542c8040d1a1000041c0503c940c0c0c012076a281c00300327400050411101e0143e1160302d90090f40d425006c991241031200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 342047724 1250 342046474 342046483
    0x1030212070f150e1504080d03110a0f02011107060b090612070e090a021003020706060803090112020313050a24021e0903011509060801060b0c0a080304060b0303070602180f03 77
    0x1841914201001d038100c542c60040d0790070007552100030700303983c040f41c41c174084071140c2c0c0d1260084030801e0183c800b42c01402d5021307028624441c190340220390f0412005403400c46680040111003002c40d901d401c0c00403a0005814020801c05c1d00800011560010110a0240d00440901514003a44100c03010701c192040108071941903031860544608952180d407080c501d09002c1820107035000720303010928000300340c0650080980340e11512090028560740c44c0e40703d80340d000c2c84840601107128130320950051580c2c0e80c000c680c17040c0301a43d10f60034883d05848403481d00010000c00c542c0305807290410780620a41c2028403580c46045c0f20b0548c50700001c07090013191410700901110b0045030114140340340e030b03400390400c14034481210800c4400036952000761029180ca413060b0105940b0b0f00da40410b44075540f208030303000e00c16090003c181540e241c2d680d40b10590300062080d03c00320355881403114070ba503040c00142000c9000352405611440815140c000740009804120f100308280580340840c2d031404034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 342048974 1250 342047724 342047729
    0xf08030a080115091e05180f060a06020601050d02010c061b180609060e0d14030a090506030906040807020604030f030f09060305060a05040507050c0102070c0e09060c160f1a01030212070f 82
    0x221615041185e401ca05440e595280c0149a00c440300d480020b0a030801d40e000c45200e034560280d0000c86440700e03018071105c882c280c044e040c010b070060001403000b030030040440242e951041c07404211968658440e54111141d0004040c42e403540d440128078070307940c0003005103840385a40d940030442900e0507030080e105020f5449001c0038080703005c40028140c6d0301c14400000c12a0080218900c036500e0008050b1690301a800c07220206030200400310307181c1844e0050303038802c0002c100103103a40c0e15075071280720603500603100c2280e10180800010000641e400070610409109071500c00c1207402800001d414903d075030308200c0c1010301d4042040219915550980121801036400050300e4880c0d2104462034414509200555800041d28204114510031010f044030044540c00d622a103038404029240c00c0169501c0d901700b1002d2040c45c884410140c038400003644159501c0020358855a1514040c1c40107200d01461349a1410041003035046c03030341c40c041180a455000c0c1030080e0078800d00400481460 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 342050224 1250 342048974 342048989
    0x80c160320070602061006170c1603053006010f0207120b04020a0602010e03041707050d1406060303030c0a0e0315040b010305070504020f07060c090f08030a08011509 73
    0x500000d05000710301e124921a00c20041e503621201251003540c1d6807038148070f503c1c01842024001140070103880aa4000d40b24035540303001d900c0700003401c400805c500280c07066003040d81c10854840441c0c0201800d0344114400e45443c0e0300c5440034070440d040d42824510350340c1e4080d8085103000080c1021441c80d40d204009003000c0300c0910101c1001c07407811446420042d82c03d080c0d00d507401c0138440d04d80d03500b82c400c0d8400c03184c02c80b4443e150360040342a14a404c258906582c01400140030505a244042d0b82c560401c0341114031440e5620001a0410b412100075540c100d0040e54482110200784860b45c0d000030243d00444c65400e0a1130124800c0c890f00030250200710044002c0c0791903540038000c403583d0000a111002c41c0b0704090400101014080c40101c41d544110b08000038a81424003d607119400c00200f01400e00d845521030701c001d44014840001005010880480d007003026408803405043c0800055488013100394001e081c400c010307007028441c01000003100040c10b6001000f00d0079104003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 342051474 1250 342050224 342050257
    0x18110603040f15061e0f12150f02180405070e120c04050906090d1b03050706021210060f0203160f020616150c080f1501090b0d060801060501080c 64
    0x250b040c4540150b009400003450103103841c0800f01d51a096402c49401e40e1130540c034403984040d00100c21510100c0d40e00ca9001c07a0244a40100300388207420005010150089440040120f5900801c000b12410090030108207640420800b00b019403c40d000c452680c4140d80812460070040b5004c0d0180c200d003e9241c0c4101c82c207091365810003006121003150040094828005402d02c3c40c811a01c940c2c4c101c9240106200b01c9100c0c481d071078403071401c046120b40e01201c00040c1128540b0304480c079030311140703003038071810340030060340310100101d078446449601c10034090480c40342031160003090101002504001c55006203e80c030b000203241503c03200030540c82500c048400c8030360710101d0011b00800c2851074035489070034116400d1001c4110304400701507601d401044021400002036424060035608188080c40010005000541045d00d100e00964141010008980d031090500050360001203441c80554841c441086100001d000e400040c00c001d080090640c03609001e904020302a103101d550302a101c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 342052724 1250 342051474 342051481
    0x90702030c0109060c0e1c080a0504030221121321050a150510060c0b0a0b030a0303230118090c0b03090105041416051210050f070318110603 62
    0x8100310780107a14003000034000e006443c20224010b02903011103c1c08140c0407009005541b13090800640e882c002d90f244440c0d125800c1c0c4810001e904040344a40c10700008210100140e40c802a42d040e07507006110055130040c1170500c049013000d00140860700401c500344111400e8071900b030039084c2514002ca2034080d0f030010340100c1004801d1119400303403443c0a00001a01030004003c4400d003c005c01c19400d00c1a6203460004003800c0e4081d01c145400180d00301c400c00005655046050340040c00314a0108940b0300c681c0020f42408108002240400d41d00c0007110448039a480008410b0484041c454046601d004881107424000c02404013050780c2d41d8002e182009842d40110015220300307900d060b12441c1051806d8000c00b41550252000401d0000040e4041400505201d6041701c5000456012340303004180b154040400e403102986000d603214600c1d40c1080c80c41342c1e0780305403c08004041c060501c1c21780a82181c1d0011464143d00010000388004120b0110080c41c0d40705054580580e2582c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 342053974 1250 342052724 342052727
    0x306011407080f0f0307090609030c091d07091514030703170d0f02070201030e060103320a03020c09011e0b2203060b0301110c0d11030f0d150801021201050907 70
    0x800c40c0f6401e512110007150f29514622220080c600c50140b90b1103207a29280c0b601029102d4541e54031005114039110341040c004c5401c00d800c1003d40181701d132818030840707800e40c2d255070805400e50000c001c180e560f288131480b503001042c83d103001010100000c81d00c14038104003094481100c0d0101030001a06120142c2c50740700030710100d4140a0000c60208649407809640001079400760300268002800c12240c0180c1172801302e6210304803a4045281c4514140c45034207401c454480020342012103a404000b0401c41c00248079009525101380c5c00b810480100300100645044181c0014036641600940c0c1000c8060a4081d074090343d0500c41d40988405200f0034041068107950f0001700e003045c42003400402c05c88560000d0b0940c0303000314003c2c01861070110660100340510820720103964071212031002031130300420400c0d4102003844c09880c5443c0c1c500b142544a0313408803c1c0803080300d60f1525130b00084040000c00340068981040203516000d208a1a20400300c0b06000700e61091580d10701081e2050f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 342055224 1250 342053974 342053977
    0x613030c0606030308180303060310110904020301240c0b0c09040b03030c01060305010605013018080309100b030307111f05090f15030a0b01140301080a11010302030601140708 77
    0x40d80c414810b1107495100d280003000040c0c00e41d4210340d442d5028411614141010080d01d108070b40140041c56100004d0700c401020301100f9802d903903400c9081000650702d407294002076000c5c1460310300c00c00c0000c441000e081c8450001c650302004002182201100240c20320302803c1d017001c0300084060321814900d0004005050b10004550301d40700000301d919086206410001c1281d0040b0000c003d40c954078001034441000030318440d841000c010800042813090000f4000040218450008103071042c01c40644890500c400d0555441901204000b9078900802c090040e1502404080c801c0c8144500403d559000f005001452844005010140340c0c50716000d4400b00c03114040864040000c012000c0d10720340c130020f03005000314000c8010010a082c690751820042400140152a60f41c50010b1a0000e040e0000c40340d04000050700745002ea00f0f03020000c1d501070460017020700400b2a042ca040703034021042070343c0141858018010131200d80c0e00006902e4891211100d141d03034a00e414035122106 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 342056474 1250 342055224 342055247
    0x30f0901140f07080603070503030d11120103031710060504030f030c02090a0b040b0f150a050913140a0501211a07030e060f01030803063615060c061303 67
    0x14254041088441000c0107a0b6a0003540d4135240d4800329240e00701490b40fa103400d400781c250168010410781414054a034040c10001c00c42c00e400b03908155202041c2003c61800303030b1051700050300d86000034400c0043c9410641d045213086185504451910001621900403032101525a500009290b801d144c040c80c40940c5456004208d0801860480701e26402061041100e5005900d442090820703820a022581d02400000b0209044490701c0085d10086030f100700c04a004200040c0310114594070b031a00000c0070901106000308201103140fa000e070584900070080d1300340d64103050040000c00441000c180202d18941c41c0da0041d5080ea0a15031350000300803080c1003400f8013041c1000b40d00c40c0d041c5c1c00714440d40100b800760b0700c1c81e071210490411903204c213000141c0709003810408200c1a02c0e204944000c001d5101d144407004007031b449503141d403281070682a40300e0410000300f0001000c50030b600640449600301e510904000741040c0c980d0340d50320300034204040030400d44140803d0600480e012000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 342057724 1250 342056474 342056501
    0x31c11070501020703110102011401170705030129010207030b1006140319020f0f040b04050f030a0c121103030307120501150c0b1803040b04060201110406020615130c031e0c05030f0901 81
    0xb4bd595a58080070035a281d207181e5403140c010f081d0045141c3c90180510207070b030558004201030a0444c0481003a010382c0c888040d50541c440c42070000b000942d0f01e00c1180c1300b541170b2101e003202036160610140010034140d8013505440c0d800c10422070428000003070b013954807602c0d1000507216a030300d1413411011f1050002e58542402c01040014104000900400a507174042d81c2c1042800303482401e140c8d503202c2d4188001c280100d24001403100000d070548421b01c1c0c50240102860509202c03000ca81150f0007a16000006882d604001141c80424041e00d4010042d00c5021400000307101c2c0014951001200300034000400400403036035403840741c1141005c05600c81c080d42c4d980c0e544e60200c0c1550394440c0c0b0508025500f00315640459141c170070255012514103401030480c9a640b5415101c14100030490301d980510a10011480c0b802c4620424400140b59140000c0e020740300080d031500d1040c1c1d24021400d8508241c02091860b0348030060700e80250000340700a2058903000581800351519051464 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 342058974 1250 342057724 342057761
    0x2040512070311060406120203070302190f0905030f030f090301090219090b040203010e06010f030f0f1a06040305190302030f070b01050f1503010506070809031c1107050102070311010201 82
    0x10345890022a60500300c0c1d200392114071682c4900b10500c00140620b1207503802044801407031071040d695980003142e011680b40340c01864501c01c07841c4640c24080b102a440700003440000c001c4112900491001e01510007140100001c81212030000d50b00c0c40ba01c00001e07504000401c00c584651400d41045080030340c01041c81e4126080ca9806010071881885030600050070183d00a0803800c0610859068500c6800c0002c220382d82c0100666580c11940b003000c08041d030303848030010390018610903d1040080d4180124041100d500000c41d4170a004a485108440c20070080001800019010003400c20300b100e040388040907810300741d00318041c514049110500c0011007000700905071350580d0588900b00c03002c1c01d41ca2080010300c04002401c0e50b90709200070042006020a24100010340103851042c0070040c901080c1030082800c20341c03004d60030000c4084052403040003541201c0e5810f080d400e5072000700021481c01c80000e42c0c8101c01e12001d03107a02e0110781c080c07003c0d91003034008001c11002c2c0e101c2d15 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 342060224 1250 342058974 342058999
    0x180b011710020307120504050313090b12010209060405042c0601061d03070e28090506160206041203110c0705030f0f121303050a0b0a05060907051903020405 69
    0x11800300418008050040c0400d40d03407104858425a40030364a40da0f581400502c1c1c6200d15001020050021f5406100500001e40c00c800c0c84082ca001900c01180042424600b00042c0031191481c400c00d242c859005002c800d00390f40b141d02c09d480480300100d0b0040b5610f00741840150452140300b002102e0030340752030005240c01c48000742050407116980d4581420000d09807282010f06003050000ba071680000c2d0040180c0701005180ca42c02020303507a040002840700409400359803c0804105d20f4a0b070b116420ac00c1441001d011240c5c1c00484400b20100007401c40000070748403c0020002007140011a91082c061403013640b1000410282941c4140d80790110714485690700024802e4600c13921842c804505600d00104032a031109041c0402464040d141101181040d0000c054203d8000e804600000114004000c0758180c14040c0d526914681010700b03140065400c010401400b404960f42408070030340d40041158a024880d01c81440c19490000d0101c1c0a4891940025404560188003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 342061474 1250 342060224 342060239
    0x402091311040e18072103030e16180c0810060c030c3513050108061305010b12010b04031a07180602300702060c010207020d0602120717060103180b01 66
    0x3130740401074482c0440d508680d84495541c080300e207484203105028100d510310380029009070040303160141e450080c1c03031900a4041e1100000d1005921051549000009118000314140b2a102851717255180450f0030f444d0100450b001610207200e280100303c098032419052612896011800d0355200001840d10601d00c0a041005201043c007c1840d035142d072102166135584404a80300d5445c00b01030005220301d45001034071148001802c494109501900e00201c0c22024481c140c041c0c00039010007601e400c0e201060b089010310580028821010401003400401c15425200a031003045910316125a0344807941160540c04001c0d01c0d0340070401898001c11341580106080703014022582d0b44032002160201001515458070402c106460b9040004a000d81041c10003042550740d1440003503c2c00b400d0745e01044100c1c955a4003135450560101e0301695134501401456001203407842c0000a0b050462007a110046000d84a0760625035242407025a02540283d1600c00e9070300117040448641c1e42d000d8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 342062724 1250 342061474 342061501
    0x607060516020d082805040501020a09170c04091110020303160c020d020907201014071218150c030b0d0b06090a060b0310140402091311040e 62
    0x21000030014107a0010350380c40d0300c0007880005200710780e540c2c1061500e485007480c8084000c060001d0265121001500501080d070203100e0146124800060b6618158003008020022a80080c0c2510000071140382e440100040c4c2803845800c1120000f40e24160340c0340160300700e42c664400f07a811178021b48103200d40c00d4020020f14846c40b80c600d140b015101d404001150840e8000344000e40c407a4140d036000f80942800c8410f01d9000040e410240a8900c0c504d140412010071000c002c0417580c00108604e958000600840000e075541c0035100880f030030107000203821101e1a168040c2c8040d0f880410303440301010942d204044035000301200501d01035250000c00909a141030000110f418204610541d0030124018080c60b0740003624401c2940340c010402c2507540300505240300007503c540f0f01150080400b0011405101101d13600e01d0b401d450402d078031284c09603122845119a1040c0f04071038860701c59401d040300c5600c46c40c00001e100100c10f0b60103070796402140c1008100081007820041411007002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 342063974 1250 342062724 342062731
    0x2070311010c0b04170c0f06070f05190c080409020f09040506030c03100c02031306020303040302070801180305130312050d05011406070201181502150f01050303040506070c030206070605 82
    0x489a200354010364019a070030511001c0c014110328a0304000f80c0401c1c0b03072410b00002121803207401c071700c3c22400b440c809180403481e102e01681a00b1090600c00c070190480340c550800c2c4c0c501d08242d8180780441d1210184000c0b112903c0091200c124007120401502100702e070054400300f0380854031800209101d00c05500f001d49070034011407408011074030620b00015201200b0100500409201a01e0b81d0710340082c0162010781d00651100b0b0145081360880140c02d20060b10340d6500868582c940340c10001c0ca03006150340f2103402e69142001400d8952450050400243d805d07051481d0f0356440b8100a0074501c01541c0301510350b030040e88003098500c3d8011300901500c0c0751900103200d5641c030351000698070402c401c50507a105808014500055005280324020580d1202161002a0b03031800f61b0420312001c1e10144005030415401c841409000040c5282c102d1a000c1c40910316605281c0030950b00d10541c0a8684218404680309080104161741440a581e014000c1a2148403520f40b060240c8401d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 342065224 1250 342063974 342063983
    0x1c0e0a150504090501050d0c120c0306020d090b070306150c020102031201080a030917031c0b04060b0a02070806040c0306020304140a0c06080915011a0903060c0d05010506120a0f1b020703 82
    0x240000882e40b52440081c0301241d04103102040340c900d071208010b039103804270604442e6450020b5000000c21a00e101400000050fa400860705468900c0c113003070b2514004111205051602809020180c002c1c03a42001c280400e0904901c00d01103030005034958042c1e200c24034480c40e1514004152101c0208185003242e11035220312007031980714440750410356004030030940f16074030500050f138101140d440320409101d504580000c01340d442601040581d0241d40080d07265050029410001550401110f40203000d2540a0000d034103159a030b1010322600b40c0300c042d11103078012010900380603125030340b42c640141c420111490804245086001c695442c81820082045100011f4072803001145810b0301d080005410451030782803007000e148203030704481c03c0e81045000380610055500c040081c14010b401840d002900d074694003006030184e079016008640682d000340001d0043c0042d000d541a0040703406e00010805001c41c07600b5900400c100e061380e030704d0146411030f822200c40d0007151610589000d07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 342066474 1250 342065224 342065231
    0xc010906061d090c09060109030510051504110702040506120a0b04021305071209060609060e010801060803041206020c01090c03060f0f060602030406110a020a0f090e1c0e0a15050409 80
    0x4614004400c0700110f40308511a00000e1000c0360500c3d00c503010591040050504041103034030b80e03d4803450170b200f0b081ca01c8040c5a689081c481d000740d51042e030700d5000c102160b0607c0303004c07098080c00d185402100c10083c00380703032940301080d03150760703024110300700890000304650031a0701900344000c8403002030310306034010b003010b0309410281050785c02010710034203c82c0c503048060b0308041c2c01500140310400003a11195501d0002140c3e020007401498010013045d0a8100c01d541003001c19403c40f04264000d04840d401008208810341d80305125032070b0300e5000040141c8801d90340d00c03624050408120000d0080e810504080300300a400c0d40a0f00b141840c8100400c00f40e1106200c00f012910315004e0b100140e4000c3c40200241807040080030108848001a03a0814145a0201d14a014180c1040940d801d0142c024004807006200c0c1e054884050002080410180d002c0c0c01d801c01a138038480307000c2201c82c5c5ca6a040383c3d203036000b00f9001094205881c4480351b0280b2001416600203019585c8020b09 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 342067724 1250 342066474 342066509
    0xf010f0318021f120213050607020409150b03070503010c1b08070b131a040302071a12040f0209240f030a050d0305091908190903080f031b07050604080f0c01090606 72
    0x113140b00b41e51100f90115204071481d8280010400d003600904012a84207803a0170b007040010b211041d110869040c11000071a12a95030400c060400b021074200601a81c135000002691aa220010025140d050402010800c0440c00d001c40c1d180301c0d00302c0181c01c000118080c00658400401074026880c041c84070014080d04d0342421000c0100160f5014005030f000030810300c001000c28605040d580d0700311010030300d80901d0110321889150100c40a96914050203090700c00d50901030113007a40702e4090040e1b0307140101c0b01c612610f040300d010913550b80a6000005000c0b40c81d10104000c400a50b08402104c21a07001d0540013400b40408540360061801010a01c0880d800e52401607044560700080c91410196165482e2840254015282040064105000002c18541c0d001091170385607c2c4111960b17032400c01c0c0b504001124940c85030381c1c6045c00300300c00c50120710085590303034010740c1c440391403959040c0b0400204001d010340f45c5524940e500e0080f030001001110b60005c000c440300c940b03500c00b1410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 342068974 1250 342067724 342067757
    0x1051c020a0203070303050a020c1b2d0301050106091a0904060918062d0209040b090112030f0c0201021e01020409020f04050a060c02060a0324030602180f010f0318021f 74
    0x261021030100c0d40c00b16010341403039001010540083c03900580854033019445512110058500718442c0400c248501c403c5418107083c012103016000c2030624428161420841610648000e10010250003000c28003c2c000c0c0d940f5084130000341031112080c003501202d441d4000003032864800c100c0c0c2c01e6107081d600242d240d500c040d08018030700019031121040c1c58807140c20030213580242d200e142d00a507590b0881c00e140c0e540c0243c950107003030100141c1141a41c5890090030841c600c00d1076106001030111303c2d00050783e00090180300780c40165070040c402034260394140d000e070085800200d0001e0002c0341d0311f01d20350103901c054001c4850444550000c180d03a200709035510701d0340b554043d4010a0801440d9401c41c06030704244081e8008680244207200480c03040c030400780e06900111141600025011b0020f154214450750200013140d801c911041540e0000c1c0c01c90061141103014180c0704d0100132041a103405040b0380c120340180c184220703d02c180c6009010609442150400f04448002001240f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 342070224 1250 342068974 342068977
    0xf0c0d0e06041707260d02070e04020d14010f270b0c0f1c0204060f090f170703080c0303040213050603060a0b062107141801051c020a0203070303050a02 67
    0x4500c05056246020f05107035070901c1c2c8031010560280c070b0380b0072030200040da6507404000f14141c03081c00101030401e01204040c0380c18100680b01c14011503010600038880403500100f11900954101c486c2040300c0e0381e900c0e12490701960030250104a510b41400aa00d0104039004020200e010a03000c6010700001c3d02050f82d01c2a0340200030381203071401e0b4000327004105100024050000751480c49030502c00b0403070710002c001c032640740c500e200c01c1d030085820481150800348080b072009140c100315455074280f854101421201c0c0c8240705040003412105098448144024009541c008440990700e95441c0c5000359070b43d000762001ca0007500812400c4c0034413041c074031600d40101001005001989c40c1c184244015100c0c00f011a42d010004200030380064900019595041849000300225880c001030090021080c8800003105244100040340101b0002d50005040d800e090070400d403102e407032070342040f0381030803c4010818062000503a50300c4281c00001414680340709035018000b5503a0380c01510b082c1d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 342071474 1250 342070224 342070247
    0x7150314190c091401030c021504061d03030f06010e041e050f0601090605040b1c05090c0102100e25030b04030512010506040312081807060302090f2403040302120f0c0d 74
    0x700c91102c1134803607600c43d41002d40c0d20f00c2d0520464042211411650740024001d40b003c0392855509d940341d07488070300c140001c500c0e070f621244065030640c43d0042c005142110024100f504200b0840000c0702c2603640c9601c003130003032042c030740300340c50f000f814408550f005040030741e4070032810090180000c440b503101e4083d14007039640301c0c5e40b242d0600380344c50b030403070035030703000720b02c04400c682a01512030050a80f1845958441c0308087c0051031074030041c00c006800d0160b115000407405042841c080045040040c142d01c000074107500010860200ca00140641885038100502002014080c4001e040d8404098181c0c0c03000401550040d1741d0340d404014181c4079601c0001c048560f0380b101282101d000d8074501d5480031001c0599020740c400300c14140c1c00c0c8019a0002d00100303034042a80c1c0303140d04103403143c03d00c0c8880070340304032140c1501c15413645044106445800003a04000001a08240c03080c0301d10080c3c81510340815403036181c07107100c0502a401084040045100c3c900c00010840e00c58494540c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 342072724 1250 342071474 342071489
    0xa0b0a0b130e030d290a2601020c0604120806010813081b01020d090b15030a260d051504090b1308040302061306090b0c07150314190c09 60
    0x2600c1d030034000c01c140500525404042c1500003401803001026990141e4440461004080031064083c0d4440e00300c45003038009214010985144144a0508100705882c0720020020710080034100b4010401e0183c0301341243c0d5155070099405001c00c202c001c8800944d04c0d0202e803688611036071040011108001c04175400c0c0148080c00e42103c0c00b01e1102001001016102810314209100d61b801050070b81e800324001d842650340d215005402c0c05158003a4a811440b00d00c2045070400100700029914820340c20702a042c80303424212400c1c0002d00711400d010030001d600c0c0054640d2401c58080e0005e25088031461003000341407012980600e411302c80d0402a90b404484040707980c903400000c80c041007803008200c0d1541d0080201001582d22030340540041c8406900c1002000d05000c002010804540e2040b280d0182c14004500c4660011629005881c00d520040d00d4454800358100d025101c200c4851582f682c050003405036103503804040b13001c0090034100a011001001c0011107111245201e140c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 342073974 1250 342072724 342072739
    0x402010e0603130c06080a110306130e070f0b0417010c020a230a05030a02120a021b011209030c03031a091f0b030108030d0c0c110f060c07080a0b0a0b 66
    0x1249150600c05150040c1c001c07540d40304059450751380d20748040c0b0741c1d40021010820700c800300005501a03018030324102036581e50840c1982025400705d21020900c035441c4541a8aa8294040590f81080410000d0914405200350769554001490b5554028003031400c102c0584000c00389801014080d0544c0e00040754024203070384000c1c1e11100c1641041121001c080f080f010810700c04000d08205450920f805480030399a20300c060740c40685010f0b01c0460340c9840f1402030010b004402e0300070601000c42c102823011646041d84080048402c21a080603500000d0700d03048150040c103178003c2102c074a40d1f04c03c0d20200100c866071304513000284242408130303901034205c4002078400003071600008409009041030342862a10798514411a030401d80041145500219050205035036500401040702e006050110442e0a0344d11046444030400c1282800340f40552490740030390301c4480840e6070000d04002a81e2007251a035040c00c1e25840c9491003600c024103100c0100d4080d43d503a104101c008440104501c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 342075224 1250 342073974 342073997
    0x603180127110303040b0f0c0f0607020a0b090c0a060809010b1c0f0f060204060c030905180105060a0e1309060b150a0c0606030605040c030501290103020d060807060c120206040201 79
    0x641e00300d0042c81626094041800001100001c00d07000d010380c5e411038160903846024400e007192401c0350540200e00582d1000c01403021031030b000715648034a5900040348840135641c80d820360740b070080804c04140c1c000f4152440094066808001580909070030320003440340e00384903410085e50480a40ca40200d01d06001d842000142c6280c42010f42e91b8070400c2c40c500d80d90500d031294801c98119500c5080030950b0500028101a40032084002070039048468003003007a03010070101c85040c01405024010600010500301840c0110314003c4030107402840100382445d0940003002500403039104030340e07481c20a00f190b102407401d8003406003403c000308115418501d64100849583c07860400603100d6a60f01c500201c045810f034041d85201c1ca009004580f601c0c2e26501d01035085a20340c0ca1018031042c900342100c003010fa010045400d1038a030920f005a202c400c02020100100702d554000c903600d118000002075559007101000d40c415004101689400504038401c1e43c84550894000307000402000c0b41 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 342076474 1250 342075224 342075233
    0x1c14070501200106050a0306060510110c0f06091f2c0d0807051005150405040b010302060d020f030108011508060903070305130806090c0306160c02060a0e0603180127 73
    0x103000d08400082d0020500e04c1e07441d00071502d084000d0300182c8659440351028003440c1005203811641002c11b14102c14646140355103541c5400384603202d07901c00c07a403c014484041d42c640040e42c107113107030003011070440c2256011202c4c3c0000c2d21091a502048440751440c4008254000c0c1c0e1582940074130300b0039101d0411100300b00035001141000c5450b28400c4c400740001c100c0412440072072100082000a60381043c0d83c0c0c40c040340c0c0c040502c2511690600041100151904124904495064070f016498449007a54180a4000c41c0a090007000c0c020000003020783c01508204520440c4400c50241c181e15070491a03180c1000b252040900e520401034070f0002881071009000d03404450340c1d0b80745099241c4140c503080c200c042d9034100c500d41c0003440c0342c415807400340b0001d87c11402e020f202c4070204020700005409031608550191190101182c0481514051480500700d902d000740440d03940d02d802c01e90b00300f0300f040940704107c10f980b03070140400c104203515102d6041041d903c0803510038141c1310760740c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 342077724 1250 342076474 342076517
    0xf0207030209180708030f071e05030d050705090d0506010509010504020a021b03010f02030109140f1003230d0507060608010b15070c0e15031212130309051c14070501 73
    0x30030fa006205904000404030800d1019140001e8444a003036942e034510b0808600d40b099040310800c04c1c8804a5010002400000440e041410068800b090984d146401651a402100c460301e410105444031041002000308020381070714000c4070250040d9894200340000c170b00407545800c3c050392007001c1168406070410805640f41c50300400200d00e0072208249036003660020f034089400240c0312a105109240c090080503848080d0001480c101d14195404811103103461001078100811a03d410184884482c8403440c0c600c900341c1120320340f0750641001400f03544001804d0321410303d0404003061a02060150011005006080c0c80000b070300c03210005070780d0b0b02c000300485039611000000984800582c2c0d1240c4503e245c0481007006002120906051225580071140b07210b0f420441d008112400b070110b5904402844221205031007140b4054840707018a0300940d41c08021040d50282c46071a12145240da00e10801c0e115180300f072000d50142d0381d80c5140c0950b0340898020040241807440420 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 342078974 1250 342077724 342077761
    0x10e01110a0501020a110105070201090201140f040509010b04030b07090509070e121006050102070503030301050a09021b010f0209011209030e190e0c0c151504050406110a0207060f0207030209 84
    0x141078035110002035403a103003280c1c032641d0303440c0c086400d145410303021010038030070142e010020f40000c1c8074202c1b090b40002c01a08406070f40d1603006e00003061042e4a00c0d201819600500381c0640701c40495619138044103802c0e0030030300c07080b218482402c00103001548100c0e00350003114005046202a92101c00040d900c0c22080e0a0345c40e000020317023410011094040041c2d030020840310f4800203e2500b4a40024100400d03a00068041e500400041040ba2680010017048410800006803140e0416105211403089550302664035800c002a400f50520f42d54001c1002480c241c80e16102100d9840621007a9469543c002d008684142c40d00129800c00c80c421031240142010358019454444445652050081c1c4680c03484060114100d409210f0401030642008240c110f9200f6030315250070015909042ca10b8040d00407a100c60225041207030329040080c00500302d03011390341c8a10300c642c0020b64612207481410000341a5030461b4888500100f10031041d01d8014004030102e0303845442000c1c0e01c4030040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 342080224 1250 342078974 342079007
    0x4051e03090d0609021c021f02030d0b0d0b0f060418030e01110304080d020304030b0106031e0b131406040c030501120308040c050907020a110603010b040e060f121005090c010e01 78
    0x144c0710000140d0b10f004100204030340982d240748016040c4d0042c84035886003050f001c203210750042803080003181c0003c2511203102204d44041a01d0844802042129141ca01c0040040002c001800080380e40c28004a110300802d4404206501103640081c0ca4800001c0014000c54003000e4022800e5215800d00d44003204031340c1c00c4900d025521030348580346c0500e50111714010382005c02e043c0100440c500c2140e00500c0b0924007480901c40c141e806c19544521002680ca42a9a4044001d84d41d01e5006034000000ea49110030000c4600c420910362440300112038640c440c40c030300880202424000e1041d02e050750140c0d034002c401002c1a9400ba03804803001340042d41c42a0b042c0800041c07550340c209503944128030031390143c66002000d20303215100c040040c03850380c8034410610042c880741405030103a408842040021017680c0d2180d00206520341d070050105a00040b10020240d1000d0340019a0304852941c914100403566814001c3c9803980c1508104500180e28030140f60304d1507210701d450f400f090040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 342081474 1250 342080224 342080231
    0x12030e01140a051b0c101b090510020106081006181103010519080d0314070305040f0b180109050d090b040f350109060506030309150d0902030a0b04051e03090d06 71
    0x71044000181e82291700c2c100543e900030a012901c1060780c0c020b01d960900107480e0031001001c10740c00503085d0030712401444c0c040c1110b0715100d84960300c00d4001c1070042c0704403816581c03160354100307091002d40504d01807285200c045800b502340e4403580b84580c3c0c8c504c0b8214540c150469080104000405040744c980c5080700e0405c20000c917004d0030603c61103021950b030380c5000504005403500802c2520009020384289854641000040b40800c0120b00b00b80e9840020341000c2d5482c8284e609140009203a580c91940ca0300340380308100030300040c007050b0b086c00503250821041c3e6510a032076450711a03030007804550400c800c0100051003400d00c112012044500ca2110104181181007605030030b64006984543e45460a6805200c817520486030071000585c051850801c002012400c80f0300782080c11212054001134510400746554802390802d45c1c020155004690b0700d08011003040400d81e000c1e559070213803450303400f00d030100040403801100d45140038604101400c82002540629003605a410988 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 342082724 1250 342081474 342081511
    0x607030213030b0f0f0c0307020307030509010504030f0c05041a0a0b09030715050915040e0f040219031a010b0a0c080d1107080d060603051905040c090912030e01140a05 74
    0x1283c010b181d1050f1006a40e204051070607201d40d050490000d4440d46c0040410014040403a074044211044190141805076440c004180103c419200380d9001502c4d0401740001c00b0100b00e00321580e0412a1000c1310140582858182e06040504882d40d0f00d940c02030801008103c4441e0090103441e07003a41c018107131020301d5a0742d01c600d20344c2406980c41030001040050751246a29007184a4040010340c000f0890805040c1488412195009441080d66881d2140000c085645401c1c0e040020080e415034030000d2036403803803d0019118046010901801e8500021881802c00310a07250010955039842c40329954640b1003100e5503114819618010307489110750340800c2da00c900142030300b6106408440c0e13141c804850030400c85c0d045800400c105418a0140005c0d4213420105901121500c00b0005007a202e40c6442542c0c4030069103c80c4100c1c1c01e00480105014034034400c40301c40b86035030700c00303000c0c3d0040c0743c02450032a04030020201d0039840440218442521991001d0340c010003c800d900e12880 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 342083974 1250 342082724 342082733
    0xa11040912020601030615180f0e0f03070506090c0906060a03060b03010b04030b060301051923090d080c03040c14120a051c110d0e0d0b0109061a0c060703021303 71
    0x220340390703401c4003580c0080010810083d151040c04411051540348142c03150401c600004a42c90b6285c589070000d845402c0a5412602d0703500806c4003150b840100e4042c0c071038407141c154070b0b074001000a03500b9004160000301921000700d0503880b81d080080c030030810b9941d11800c201c1c1c0c50700034070303044003c041e0760f41c0f0085242d225200046001e411401c1c80c45071074030319600d071140e41c0e03150003083c041c000e905003070600c16656030040c911030a140d400ca00110f1860380343d0b0101e003c5014040d8032450205407138024030200c000c0201d4089682849941e902401e40d40380c0381d034801c0ca88400d83d0020003031040110104240c102020600341c00600c000c0c10301040c1c6410305045403810b0309600064030f481e000041034201d540c60480c4101c00700111800c180505008124080c0c0c0c1302c0c000d207c0b001051168149000780b480c0c4da4a0050619650b0000001c0074958640700c003440140820701603007145050014840700d01101c0c034000d55840003031900003015030303554040d4118083d420203146a0b000d007011000100015 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 342085224 1250 342083974 342083993
    0x6040308030c1b070b07140f062413050105090c040e04080a0c08030405011a0406050303161b0b03060901050603150f060903030c030c060112120810050402040303030c0201050c03090a110409 83
    0xb030000e0488176441b082a400e00300b8084900c0e0f4840030f043d41c0401d08503d110900401d00550110580c801c001011140002c03100711104040c18080c2c0c400340c440f46140880c429980000d05884080d90f5402d0340743c0c0c0341c003944610b910881c00780016003ca0000001d0010300880024500c010152030302da0361106251b600c1781c149800594041300c851751036007403250201980320801d40c100c81003290184446860301d40030030303140c1c0309480307a030030f95480a02925410311005008a2b05440460200081c44680c1c800c0000303055001921140d104801038030001540d403600c2c1090701d0291082c4072a002c11021400e0800c101d5031240d04466800c040144102c0950365030510281442401e424050359031042d242c1c540a0410005820482c010401505403001064803c1c400300d070141c4141c03d11101503103400303000c0d80d1044125442180d00c540001400700c01c16501d9084800c0c640141c0e0020b01690300c40440c40801030001300c400c0f00e9940d03c040b0184003c1034581d0381d4515400c401500000b404071141e241c0040343e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 342086330 1106 342085224 342085229
    0x1710050a0f0b090106050f0d181b060806010509040f060918231f0e100c0206151e010e03030703030c0212120c0307020f1b01030b06040308030c1b07 65
    0x500d800c1d502c5101442942c000d0422212702a03c1c24808400c04031440005090765242d0000d80301c1d000f01c641e2030155105840e41410141040c05001c028404101c5007445281ca4007400119212184a500094080104204101c0d00c05061210840d41c1c0034843d6001d01e02651018600110041000d550011010311840480000a9202d030b01a0185441d2010107025190202110b821940d103d8000c4803820b400341d801942d54440074074500f001800d8030541261a148114105503100c00c0e02d00c600550504000303020b0002c440201340356821944007100480c0d40d0749148081c858040085120f00090f44501030b18000103022490051140682040d141001c044003188141d802440f030740d014010207404940c10031004800b504881407049181a010034600180c1503498100b0320221025681c02c0400141ba6480b1000070001a500031558012201c1c1c0d00c1d00b011901c0842400704100 = true := by decide +kernel

theorem cover : BRFrame.Cov 341906474 342086330 := by
  have h0 := BRFrame.cov_init 341906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 341906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 341906474 ≤ n) (h2 : n < 342086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
