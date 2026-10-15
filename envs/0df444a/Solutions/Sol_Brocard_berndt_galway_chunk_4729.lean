-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4729
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:49.93758+00:00
-- url     : https://prove2.me/submissions/52e2ab4a-2422-4da7-b39f-e7f6cd19a2ad

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 850359712 ≤ n < 850539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 850360962 1250 850359712 850359733
    0x30b090304030314070303241e06080403140f0d0b0307051008010b030403021009060c022505130609140a150506120a060308180a090603170a0e030a1103 67
    0x801ca07420340340d1640d80e000d0818424501d8020a410a1208609040c2c4030030802083c0c050200b80403080f0201f030403541102529000300702c0746003610213500340102d81d00014244822038001241c290000d40c58a0103181051040207032002c01d0107031010134070848a00040d90740785010a5040302030b8a450403410350720300b06e588904005001e2100f001070004560302500401a82080902a40d4054001d0052354a410101d40c0c0820071207008481c200e03500740d81c0300c12844009034104160402c014400c001e0943c0c2c0466a1003070140d40443d803241622824402110300820384403038119100a10413070000303200405d803240940f2540700044034140d040600c0c282c031380101818202201c030100c84019100c2c52502c4098000c0b00111800201415540d940700c000020008000300c0003012200300122642c0703555800e00b8104200b94601e035021004450811609002080c040c0d09601c074041e010700fa0703043e0744080090043e1074078004201d030513615008a886240500170100e00d03000007100100c083d2608800b6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 850362212 1250 850360962 850360981
    0x3010614011d010207060f03090c06270b031609030506180d030203040f0b06120d110c040e1b0a0b12060906040203090a2301020706060e13031707121401030b 69
    0x50910841c0180e0010104001050280c0b2100c10522440c0c900400ea14800c0d459200d12481c0319480400002c210340780700d02542044410fa0700c600c0c4070280c21102c0d05480d068403400d1b0f46c04068814690252a0fd458000582c0a82400d80c0190f0b070003c10795a480c0b500724110209000744200300d8400780034500300c903a60940700e88200d07407040d0f5018200481011064440030f0801c0e40081c0b98075088805544c00018180003000b8043c0603a16642da981e11400e82c0c0c0a03071500b03041802c3c100074052400c0c0548140d0700e010118016030781440e4291003103045942400041c0300c2c404680d20011100d0b00000d8954051200c0c150b003076216040c1594401c905848810034007080b132104236010401074109409050018400001d245c40c02c20000000c1d40302003043e461020708903130104904564003a52480104442c64580341840c0d80415105205a004800354601502a8420f10b8288016060300b0001a030400c0c05111628280c804c1464100310303002ca848100098400280416928804000c002480e54407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 850363462 1250 850362212 850362257
    0x2506021e06131106070b06100c0c031203110d020a09140f090402210606040c090f0e060409060606030207060609020f04050909010902030a0c060f020604030815040b0301061401 77
    0x44291000703090650300e1107088940000000c40888105010114034803041c0d9628002e81280e60289411100e1410721108025002c10b113610200305120030b2003d258041040c0307020380400c07680c00503036021240301c810404030001d004c441c0f0001d4020202080c0050041c0c059405049852142d860781b042081e141c00420342901201c1139166441030080c801e0340e01d90f08101c445c00e81c001d031000d007580d0845884a100040c160b0418030900030540d0140b400c100350f40c03501d40100d50000010b428143c000071b0a006d580981c8a1481c003c290301e03152444d020500c640c039103602a12850b40c211000700f080c40d4480300010041d500258007540c6c03490418102007144240f5108440c990f43e50985a41d260500d01024080c1040700180143c281e950f9034070b511f801584043c828024140d00c520000c0801505019001d40004610680350085602c130404000010b60051000c0d90041c070340070107040d644d014042c001406002b064401380d40550910000060706a04c2204503400ca000980340d01e60300b070110000003500b05 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 850364712 1250 850363462 850363513
    0x11d0609061303050c1f090c0b461d041a12070b1204050f0102031311060913021804141308120403080403140901090b0c250602 56
    0x420b1010004000900400003005206003820540c0e8002c0c500c40c01a0540c007007801c014002054880040100f0012076031640e101034180c4002a905020a001a0707400c10544804103100c05581c0c800e050100c20382d030545620540c000c0803110603441e1102d1000925604000d19158000b050420340c11765185040c2c007641c2182104410410000301d01c2c6800c200340000181450046805825008aa844030500040031841d140f14402400c43c101440c150b85804214204c03003280d07902c14410300584a190907034030507826401503100706100d650240001c0d4244200c1c0c400c903a02c03c9101c90a603040c509250003800c103070a66240741d10041070641040c4070544da00301d07946607103803483c5400085d5010f076000e661881041c00360524509090f201c4404078040941543c041c0c0200380c40d40c0c2000205607205018115181e1210040d604050400001074081040d40c040c0350703040100400d0f0710340c241d80c04000b02d1004c51058407080d14100480c0c1d410101280460103154014001e40c0b0903041c464600380002c8540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 850365962 1250 850364712 850364731
    0x140d0f12140c0f04080a08041a13051e03030a03060603050709080a0b090a4b031110060303210c1d01020313060e040f0b030d20011d060906 61
    0x25030392411901074040d03012010f41d4500302814031001ca1500c0080140004aa1240c1c4c072150f03844d07040000d903502d10100c14980c203030206010084c8401c00100030140c181207450648000d60040c420300078241c4160010b18801c2d0f0144004107400500d140d040c5c20604c110f0380107440400c941d4403200300849000d035482c001c82203070b58841d4441d00009210a0041a0300c1110030080d40e100309204e544140c0c400c0c08842c40c0301031644505020301c81024101644442c400007030340b8103a810010151514010300e10081c03000d824001248600c0803409406d00200c90030758000c41081100d00d4076460050300300c00c0c0308580c001e4036640d51500b0600148440c41024041d12035602c491060010410751404c03001e9079000803604501040c09451103454102c154000500110348410b81c07080c1024003400308440810008000070781c00c204400900c0d40f004a000c074148903491412840111140705142500c40301c1c504c0c010060741c13a01d800504074440c00c000e805c504101c4c0e8030654185465080001c0c1c0da40c0d005850b509203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 850367212 1250 850365962 850366001
    0x30402150c150604150303180609060c0807052107060f112506050411030d090f060c1b09020702030d020114010b090d0510060611032104140d0f12 64
    0x104140c00e4008a41c0f040c401030022401c4807a564003040000220740c001c401007220414142100c4d0402842c06001d0021850890070092500c00002c00100420101030003860300002c010007804010f10001030494a4000c80d810a240d164400440c140d12400c0103852851a016281c1040d1003d802401061490086030608114541c04c51903903400c46d0628804001d00c40034a5800002d1072402428419401741c4020309100310f0071018981081d06980340182003001243e024496070401038100000c0da0300c5440c103079126680b240382c030860b004406031190000385982000001d000307005030000c040280c42a01511203a10400c40207900307803440b5282d401405900c4030018401080248050118030350010074200e10441075450701d80c201101c00c060018007d85074042842840c0e0407046680b41c2e900b8400055140074051001d1481000524030703035812900e00e18001c00c040c40802c41c84140d00010540940c3d510605c41280640400c0c036401900001c600c01c500c084c12840098800c620006040050314007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 850368462 1250 850367212 850367233
    0x7060e0f0f22090308010906060c02013911010f05040f090b01050906191103040609090507020c03071d0604050702100b01180f030605090c01020a0f05070e0c030402150c 74
    0x60104030801c1c08080340c0282c044407520b09940303002d000039072402071302e40e0540c65040190702c4054920300d410440501500e0444000140d81c08140844200c09844500d031804c045808401201544030711407480c0d042c0c41c00d03104d0302489018508030b14661000d0721032480d0710080c10401c0d5028003c07481400845031502c5810024040550822a4001c0d81458a280352904c564002801034000104c04d44800c0400c681c038101c940e4214060b205950800c03030046003420300c2c00400504c40b0003140a00680d00c0d4880000c40c0016000b04852a400c0321b004083d01e50054640c0c540c03890981d0304607408041c4052840c0419002c0c207013407007000d0150100d9809404a40560308000c409041a243d8480c1042803d0725201804d582602034500501001e040314018145982081c40c2900c40150403003203260800b0f11041c0e481da0300040c0303080e013140d8010094818070189050082c1801020b41c800c00a014804041000c0d400c40140254802ca1007250110707403419070303046450390074040c141000074940d0000e007518 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 850369712 1250 850368462 850368469
    0x7060302130302061207020f01271a010305060f0105010512010b1602030303092505010905090a0f0c0f02252d120302250e0903190207060e0f0f 63
    0x188090108554180790403556940411484d50200c1e550b0751607000f81c2d90078401800e506000c00c03204038840742e000b4000074112601280500301081c208500000c6264655030030420700800e0403481603104002c2004961f07690401d182c660b1011921071403000c0340c81780045450740c014801d860712032000040c1c0c030855a007131800c4003c0d1a4807c60f0b210402c0040d0101000042e0740c10001148034960b400040c103030119071a118005a02c9440201039101d189040041c811664405070001c2100c80c03c4880c001c4984601000d08001c10083c09024565801c00f84600710341a04186c0c5071066001c2a82241d00005000c000d440901e0100c0d01402e01010030301e407082080200d184818140402c8458800c041c03415034a4142114880a074051a15601003404010034150180300f001c200c020329000c0c04d0184100720400828112290080a490388020008201c541c103080068911840c01945501d56400030008065035440c2507106120015040c1c1004214506028040f03441400c1d020301055400c910b00002c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 850370962 1250 850369712 850369717
    0x190803040816060905070501030f0b0f01031d0124290c030f0c07050f15091309140c03061602190302010b0604090203400311030a0203130e060307060302 67
    0x1044408440c182c0850101d012032283e00314044c461802172952518020024050765000c3d61800c2c40680707070a00030f41c0c45854080e00c0c55085d06007407030002006d003510940300d549911011200041580b804011700180c071b4144c43ca46081c0010081075032a46550341450f96400c1d005404d21005600b10705561b101131030095006443c03440c5062054901f003200d90091122980c1110488a5181c1d00c44daa040046040c0510880440c0006860f031032003920101000514512a06441c0c5000d4829031010140300c60696020a4030950311242c2002103242e060303452a40c03008082e403035904c00d004642c0444d07905103030450034500300703201a0090030001014400d504111320203484150306554032038903d1651907841000400c0a001112401a12400d24082d0030025190030040d80b800031804000422913040e4000d0016881001e4480e642482ca4480c681118480c9128214000034070001c2075082850380c0200c05440715001529083d00c00d01da403999820354400c000d8850a0309038111103028841700d840b9400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 850372212 1250 850370962 850370977
    0x5060c0d0809190c140102010209030a08070206090409030807030e03030112021203130f0f0b120c0c120c010b01030e190f080423010f030507081f080604141908030408 73
    0x203448111000f8003154010a01e0700904542c16642c2d00c02c04d000c1070712040d0102c200280284021410f140290020995802c00c0141c05040c1041c04100039003195500030880b480520081c00034000200a8a00642804019200080480d05152142080d148004107070780c1211001002020501019000e00906c81004125980640020080440f44070034080282000b001c50546d8000d0b03c034035105034a074003005190480b982889c2c04001030b01c1c1a40c140081c01d034100000140e2140e940042d004a903140c540304001150103540c02189140d502d01c41075100318910301c000e032403c0c00a000c2d1a03803103907201d400980c0a480d100319550440c4c0c0104d0042c904d42406a0301c01d10790030b03160070303203404c2c02f401001c01d00300d005040e0012090006d0010350f80728002010108041c10140094205100041c0c82800000c1c05803040b40c12030118ac10042c4581c20300c00c8010200b41090711294101800d003c810722030450700c41d4600d40f1402500744603102e2001c0c40c024140b60062a2a07003542c607a65507807000d56119a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 850373462 1250 850372212 850372231
    0x41a03030322021806150307020d260c180a0b0d0c0c21200a06020a0239010504030f110a031208011a13030602030a09080316080105060c0d08 62
    0x81d0502c0041c2c0302c5910f02c03c041078004006140a01d066420448221038050381484008028401d0020300c0c4c1c0c00040c40c90300d4a60905000c10034401c641c1541020119828010b03010308524000e002c441c842a800070700c040210316000001083c14801404031400c0385118614040b4000c0108010042c10b56104907180c10b4640b800380000300591f103480e80304c201d4800100c44d8180601000f58800c43c2c2140e2020012813108882c48120b400c03d0010300d84691204002030800354002410204261003844880b4559508917406031141e000603040d410f10503003d86402241c580d0003000701980358040c60664049030340c03003d0794024403441c0c1d60300d40c04d02d8110584800d030045101c80011001a940d003161a000d09403569036810f4030741c54040e642d0002c81c0054000322100d4820800403508582d669034102c10380e50480405640c0e5101c0d001d15000500440101070010b010100c140704418000726001717000340100380e03101c2640782d803101c081007030070b118030749101c24251320891aa4a03c00e01510383d05522000ba103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 850374712 1250 850373462 850373521
    0x415080f0607081e181002040b03090c0a050a1404020d0501080f0d03050c0a030e1204030f060615080115090503060c0a03230403050d060305011a041a030303 69
    0x1801520300c0e1620255400c0c032560412010004020303071201d030aa5001201d43c022100c03a04400385a0b81e400c01c806810142500150b1028242848041080c0005d5102d4024215a40c6075911101030841d042074495111500428200728001d03c0d00d956800c050b03070700003090340341801e00c2c104e4031035032000e100d203111504103130284102c0d02040003500c540340c000d00040c0054800207055500301c03070510f1403049144040c50703c3c0005002001840c0010744944c40c3c0710f41400540b803103540030141e29150306900100b1903103000050210400c401d0450078080c29110306401c0c00b142d510b40c00109054a00709480100080800c00100402400b0034160403c0191604180381955154008241003001c100d5100030090400103080245aa0500c100e20b19000d52519000c40b0035000d08141c84419800781025081180205003409180303040e50001d0700440c1c2c444000c01411685001c00000702c0d0341d2680301807182c0d2a0645c0c0ba2000e4030182d5100c004500010003461669171150001001c01c1041c100031001541031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 850375962 1250 850374712 850374719
    0x30f121e090f05042d200a0806092406041e030b07051905090607050105010e10081c180b22050303070317151503090105010b27011101151802180415 65
    0x5080031040d030401c2c2c6c1c16060b55101c042c5030016198140c080c00c014040c104100801c20a04440c07118403141001c1004c8282110841d44002080b42c00342d40c009056078079011880d10038070624200b6240450340304400c0c6000c41c0d59186400d840034000da84005100c0186500f240c800307644514001d0906860013065641054102c2c1c49640c00c549098000002042240042c0b00200c2c081040210040a00c680180b410004c8050640d1005920340c03848000c1c03003e06034011000200b00035800018094800100391a1501100f08600c6654682e500411101176040c0200303050601000b280c11503901a11400c41802d1844441c0c0e070303103444c01001c0c0d105203061400c12580c81c2d5907503206400b032212807502e0542c070f90500284650850f0810390104001002c1008281d401d540e00010440011070080d2480745400c034040c2c0140c988103500d1100ba00203502e404400d100c07000d40c07200d400007540e8645152103010b6501410078003c074461842c0c4007a20700980f0801030100c1c60281c0080c0082070103041e141c04956503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 850377212 1250 850375962 850375991
    0xc0f080d050603100207080702060906040503030304052d1e071a0d0b0a240201090b250503060109090b040e030a02030304060c0504030f121e090f05042d 67
    0x4800381815110380c652052221900d0100304009106007407410451034055503030303501d03a060311a19030000d010302c0c0c0124420049554a81c1681c2c000d05d006001c1d0b03903032441c02c1d1601d81c0c0c071014014010b64004141980c1e040102004440401c502e125980003498040c03240c0405054070b10f4203292036510b62040750004241c10140030810303040c080f54101c2180e228400841c42005440700d030b4091b140244041d0f07404008084a918460103c002c2a00313644070541d200d00022409403008070b1001d0218201c440610540028418a0700d1507641c903810105e03118481c0020450b51403000359041400183d00010a0082803030b0f5070b2000e41c0002c0010400140080c03810702c2141150015440d1201603000030080005010313040c0205001c04010786025071419042d6a68240150340a907030240401c4415040c1200ca14011000c050620310102c2c145070200d5007004001304448070b5801800318406040720006081d08083c05606a0400d00c010b4448a8024031203000c40880004000800d43c01d407100c080403040036 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 850378462 1250 850377212 850377217
    0x30f0209042f011116172104051002010b0f011d09270102130605210a0b100809280605010803040e0105010e13020f0d3603020703030c0f08 61
    0x2403814100481502c0340001d48411000800140d55410102c0c40c004026102c0c02000243c1c3c0040d80c800002c000320140f5a460030000da218101c0c6c1100d107040c07003010800c0c3c00000d0004c03582c0c101c5524200c0320396108120300761017280e10f105802ca014a440c03951590f0140710803032980341000c601e0b038041400e56000906100c8040e20351070011540519803540f0090f22880c200100340c0450003c0d858040700040e0b22496229030310850003001004a44140c161610852503650350301c60a4001045003802a06a80200801103903103200300172451034000214010901180704848400180c1310400d0755141c8000c2a40040a08084030368401c129103000506600c1407034080c103101030041da16103003001c8921010306010b800c6a81480140e030f8030740c0240e40d80c14090074041200440b025884195814210388540290005078004a0078124401003410203001d82c00c0c0711403050074079417116403664040d484615080060140068024200500200f400b444400ca00386202e581d042030f2407502030b02d07901101e4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 850379712 1250 850378462 850378523
    0x6050a02091509100809030d021806070c05121207060f060b030a050103290a15050a0e0405121608030c0f0403060c09063002070b07050a030f06030f020904 68
    0x624003c43d90040340d0800a00405214005080801450a08008081d543c2c06a45401040300b41c0010b5035560b0001407030000005800d0103415103443c2c02140ca88121041014007440c2d0141020403c401c1d0494000504a01688000000ea51410101d41c4a00c001740006c41310b4401e07030782e17107992000030040c00c4100118801c5084410005044d4110725140c0d22010b4182c0d4003040b21015a000c004080802c1959507400c0007108500144c08204180e5031040e42015070310a5507c0a030070040002d1481100594a00c240d01c902c0907919016003078444105580103110401084495a8000b400055819401150400e42d0000403604201c001c040d40300f05540b258200303c80e5546c4400424002d01c0d004a04003000d8400341c10401070481c0c60b01d0180d140c40705141003010f98480401c89003c04074100764116500c5a4100100c0c0c05989407007280503246a200c1032003680004d02c0c10700101c80d0128148134002c06d483c2d00c02044080d40000e602000304e03500f8083c1c8281da074507406d82d0440d40c0d9401d100314426001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 850380962 1250 850379712 850379749
    0x5040b0307050a061218031e11030408160e011202060d1e0204080d0e09060d110301020a0905010923010507031107030c051504080a021002070906270b010c06050a0209 73
    0x5407070404551000b0f4a84a41013001b44404101000700000d8100c686002800107501981140340100a0f048a212400a00314141c5000015022031a0200861001b400c45000000010803d54403001c10000c0c130424414201501a5081d00d1801860403400400b0381c1070314044041003150f128000c25078649030000c8491a1241c1c00202084216014400f60751854941d080c038001444181006c18980600100303070394855014242404104600404480000c11001c2c2c021510740310103070310180100c40140143d50104202d441d000841000302e10400e4845941400c961141414410054a0700e4101c0c070400c900b07010340c6400b92500d4010810103903000758042d00c0c1c5024400c0c80c180c140160780901e8904502c2c00c4100300824081084009074040300c0e654162940245481060822404c0c00f03016009108190b04007040006c05c0c2ea41c40c940c0031200301141c10903040c03901e04442c0290455000c0015a80810420601d02000c52030681c40b10354400848080540380103062030004880114400c80712a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 850382212 1250 850380962 850380977
    0x313020103140f061003110d0902010e060c1213051002070302151e18060a020a0c0501110606101209051b09092e0c0203070b0a051005040b0307050a06 66
    0x556070300d8041c04036072035102c103403000c500e0910762501c25502c80014503d5000d548034140d4203801c2c501c20782c000d00d9011603924003541c4501710007220102800c90f070481030740003c41d1203901c0c0034546017140848001e001d04030000c020605c424041c3ca502d81c1c0006d612210b03004c0321a04001443c0d21290780800380c244555000e4924241144100a03040102c074040d2013510740c040c450079032071440d04100328041e1100c60590782d4443c4110304c2c40d85005941d148030070f034102c1c10214104e202160001503c030300071440340300f01c403076116241e400449400d0249000203c01e0b5010f00082205410901d039070010404451401ca00201c035600740c0e21043d60741c4c4031022141c5911805541d031101c002d064218000901c1141c02000b14104480b0311550347c110143d900c0c2942c820541d0700d00c02c41600144004540e5003440d001e020030600c480d00a51250041d0005076494004d81002403445a0b05100781489942100c0040703542c0c50800d0305000040c41c032403550b40d40503c00c565001c0b6440d640c0e0002140108002da682d0302 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 850383462 1250 850382212 850382251
    0xb0607120c0c0e040b0939060f0c0613080306090601200c01020715052a0a060605041d190311060a021e0a051b0309090403020c0f090121080d0203 64
    0x640c98900108030300c3d02500b10301c8440d0090111590303101601601c03140d0f0200356540000031f403d906c140b03958030f8903484030b0009404625040e0440141c00003101d100241d99440d914507100b04492058110010700001301003001801a1810541701c540000c8189414490010b0000503002c005140c510084800d50107030b180e1014035a410050075010704450090f02d010312108020140c01030003035800511000f10703095402e03e954601c80245900b0f99089a0072900c0d202c0d100d0414900400080c0180c1e4041c500f4080402100940f200c0c82c41207403100741004001170421404100d60f2070362000c400b201001200c020340c0c02c50301010004107000b03010040340145d43e204503003400b44034100715041810710389000740200090150881c0a4813058644402c05045001220416500314851498100c0e4031856450030300c0103040d400242e941e0a680f055070980f1090780c81804004500c9800d2007800000c1c0c10342810108400803100b04480d0280c0304100450819510a80180503604201c03070b240d42030030004c0d2041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 850384712 1250 850383462 850383473
    0x140a030915050c0604060209061303260325020f0616080115170c07061b03061208030604020f1318061706060d030e0a090614040b0607120c0c0e04 64
    0x15884941d0304003945071244443d040c1c1d80701c0400070405046a030380802d410415844000480714a103001490090107652a80f420701483c42030b4001e00081102c61008039400312107402d007124003e02c58000c80c00801040540b1247c1007070702910405046001e0926030303003044c0d6010000c50707001d201c4d60802c0350628901c42800402446d01644910b00d05040c540c848000b25401082e11640c0316131081c0c0300300c125901e540c42003090740304486004080914001c08001c41000c0c001000030480d0040e41e092201503501d00080d880e1000e1844050b20444080001c980280b5140d4018480b00608800c000d040c1a12082d00030300030081c95020034401c900b65400b2034000091842104080c1c01c01e0300e07510f40d00758816a005540d800c1700411507030003054100d14800901d070040c0c50340024150000c2030382044a448404d40400f9190f14440d617a40302143c03071000340300c92074503014808616a02411443c280401d54441d40c002807040002901480b100b0500200442ca00700c41c0300b005080f100280032900e040901d0b04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 850385962 1250 850384712 850384739
    0x6070b0114031f0c0e0d060b03010b0316140406091401090b03070e040b070c06050c071e0b0f1b04060c1203060b0418020d0614012c0d140a0309 63
    0x50600c82d410548985540e43c41d1000f0020f0084600f40c00002c402c001c80c502580c8540050320304690200b031051807402084850b0300160028141507009001180b45881407640e1803c01c181c000c00712083c9000c0c2030001398100000340645910040c00811503940c1c0e0001881111005c1c90401c41985002006216004040c0150011140240c0007000600e26202503034641c00e1000d04001c16049030b250100d40c106128004021080e81c000d1010004e07401d00480903282540120380807505d10a00b1201c0141d4031020300d0f0b0f0344107205d401812910301a610210340381c0001c58010805280c0c49c82c90000d10788074000741406440584425110f07c00b001e4020f003080d44a02c1e890f0382e000400c043c1000c400f030080501030702c00d8030100e88003610102140d181c0f078103202c0044d0254114003c203a07481c0c0000042c2d03a00c011403950540000070780b601700600c4082c0c41401e4030302881e65071244111b080300b105030341542810541654410301603082c2e5511814000318807404c1210804040c1e0000c0d0007413300f440302c01544201c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 850387212 1250 850385962 850385999
    0x80415080402030303040611070212011508060c09090705120f0a1a0f1201090623071e0f09030816020f030a2f150a0f030504080d050702030906070b01 66
    0xa21005601c0c1a0380041d98030300c03009000800c06921007401c4640b0341e1480382a24802d950003004204600641c01440c1d000746035000449207111254540014045804120f8500a0400a4055141442010a1004110300540607500f0000100800b9071300a4682030881c1c01800020b203100c0d024201090300105031240103a007020040c400450701642640c840054130000304054800c0c0e164200e0702a40c0702d0044c483c1c0003014207100d080008207580e02600710348105205403a051141203e44036080110b40120006151004078030f145401020030314090400c62000100314608140820f80f241d8810303545030404440305201d01c89a900720000c6203000d80810b8803480b010340080981034510f4a81120040105100108150f01141c1c140c0c0c109036481c0116030784040103805124540404507038001e5a6101d9030113040000d00070001c07500d80c40d1081c081d4a000310f821501072820002c002103050010031000e4040d005500c070811503244580c40740000780c12014051240c0346019031410b198001486500344 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 850388462 1250 850387212 850387217
    0x705030405010e01030e1515040e0703051015030308091e0303060a140105090603100902210a141f0806160207141c050307051501080c03060105130c031503080415 71
    0x40386c0d00c0c1c5000700207208039504008103c4200c007901d810b0380c4940c80c550700340380481e080380c100007604008090001c2c81d5000c5911400c100c4007036014010342c1200b01c468410804042130003d0b0003c1000c00d10803000c10f50041d2581080d01c0000300d08a0812202001c0102c0500d116000070080040c3e9290032540003000b406900041d4030740342c1c0d00100003461b45c890008010320500002c4080b072400c29100004401401451008550760750400151000484c040a006940780c2c2e03220000400060140c02400307503d46000c20115080d440c4d58019200030303500c4c200039510a04143e100010324103010010355010b28809000c00340c3d2515840c0000b41003429641103006a45501e0f03070b5003005030f02c80b80e480b100031101c006040d48850b1010329025003107100d070020107421072182684600050100d41610f604880390b100440d280c1e19480c4040c980c03100d9091280c036921004182146048003d0350b0800d1454604a00d80000c40c3c10f0682840d0100c512a0f401c1600e5000d404036081c00618003180641803d10050b0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 850389712 1250 850388462 850388471
    0xe1f0314010b0603071106060a0f0b0d0b06030a02070b010f03020904060c020a0b0412120225290105040507081314070f09090303050f0103050714040915150b090603041b08030705030405010e0103 85
    0x602030242c00ac0302403250321801c64001581081558242c0d2250f075400c3c90080c0029501c3c240680980040e4000e50416942c007084840005480c5800c85c11140843e540580341c0820b945d170701d860382c20080c101da03500c82007540982c41c4610001071200e840d003403041c3d120340c0707034105c08103242e20300103208100300c003051000c00d88100700042c442d1181c0429a03400d4500712041c0b00c911501481d040c601a0841c68101c03020340103039280515080180c00701039050b00c0c000e840c208038942d6003480032103200f4802d41d5100d080941140303150f004600d8001c00240300d040d10004441c0b00c5507403500f000d2800003156011603120b695a030302d01342c101685070003400c0e000304a4060340045c95045465180e15801e8034840c20010715a6044000090b40703031500025096500074400b180380c0311003060031074050070041c000c2000301c03150000c001c652610700742c0650300145c1e000f402050650ba25982c0c1c813158141030200c140d100b038010a400080541c0200024000749100e44041c6468501c1c0c000058070030a01d5a441c40d05240c1803 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 850390962 1250 850389712 850389719
    0x16050d020105240f03010617011e0605100c0c08070801090b06040606050d0903023c120706181e110a121e0210090e1f0314010b0603071106060a 63
    0x2550002403820108131078031000d1818080c006401410180e0110205c031040f003400d084040d80c10341c400211229414440303042e160000080703100300c1d0098005d03541d1003031090f000107a80901c25400701c0205445400401c0900380c581c02242e00d00b03031325940420043c3c1e4542000c0001c2200c000e1105402800950b0240f2041d030030400f024182c2d005e840343c40850b10f41c0d1105050305051003000004500020340e420034601210154142c0c086441c03094040314000c0c015003142c1c2002d180001c034000e041d04109144da0801032141d0703d110103458400e110381d01400f0b0401000021070400e000d6060045480c1d20505400750462070301c0c064150006070b4880c8651780c0200700704032109025190205c1198000001901d00b010050040c001d44481400690810b0710044424681c542003642d25080c1c0c4e038070110404541e9510128904032408216114482d1030444c2d904000203100c001d40103011420b40030011070100040c4001c54840d4104035640710029503103250010401c1e0042c410075030450800d541c4842e50a08 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 850392212 1250 850390962 850391011
    0x513090b0f09031905030f150f120c060f03010e130302060f0402041515020111130e0415110d0605060c06041101210c020d0203120703090816050d020105 67
    0x14a400301e20620900010030031241401180c0c040e160303410203018500d40d00000288540c00c101d441d903c1c100300d00030100b066501118151128010020643ca521030001030511000108641101c20742e4814811400c2d500d84d2600040e000c4445071520740f945a40c54103d054030380c03030005400c122000394000100c0340400e50120304542c0c041d500d00c582c81600e40359440400c1c000c0c41c1d2100c400300304800c6020007144c0007070804180785103c100b0354002d101350000200e28809912a0701045040e50980b28420001d00f07044400342e42d07105001c1c070300c461011400d0021f02d00642c1c0c80d0420907814104001010031080b0100c1c443c00001d0b0005481103070400c0b500101c0d1a0341e4043c00341000c0c12140010b030725028160b118032603050307922100759401106007807226418030140c07103103420810240c000e0280401c0c0491000007511501c01c3d40c1240d034030399034a0b0301c3c2090f0000c1c2040281601c074803004001182c0c6c03001d0079201d03000c40b10307100310000c042d41c4104610080c2180c02c0170f050215410700347d00b040e43c54044d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 850393462 1250 850392212 850392233
    0x30c030c0f37082143210f050c040324020c01020a021018020d03050906040b04060203030a060608150405091006030f17121317030907051309 62
    0x140350000b03105102e00715040c01c18440c0102c4680c10000e084456003a02250720791400c0034000d0111035107550329540c660b4005201100321039002d000c400011524070306209081080d000781c0c401c00d41010403085038840000c101072003480c54214007040c0c69841c001e90b8100288522a8000081c1c2886400c1c641565252187c85408828800304a00d401000c00c88500d00ca904449448a0707000085680c0c96103e540a501e4402e68054940020300d0f1a4804803111803104180b00d000d50300801041810950f0751b800c0d03503250061090290802e0090101045410384803004001070006900150323124641168403105642558218400300300320340051201c07081c442000510aa8000c960118040d80e400400750300e0f1200303030920b407005c503802c0030b0b4004184a0700e010101160760041214003005a150b25100e08144250a400c0300d5400c0b60400088500101e1007a880c078091192042c0f00e04080e0031500726840760019903400da4071b40c00000b0101300c203142c003481a81c2642100d000c24450520b40362280150311 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 850394712 1250 850393462 850393543
    0xa14090906040c0306050406140909030301030305070201051b070306060e090c030c1302130b04060f0804022b05060903030610141218030d0207020f03010b0d14030c030c0f 75
    0x29500e510004400f24001d4000c2c0011b440054030401007243d66802006000030b0402045001788106400f0540c43c0b54040704403070503a43c1648955140003415401101c20703a03c1881520b0307011821603400900c2060600076030300114003411001c1802c2c0e0800d050b42c00795507405440007500358801d01080c0c074143c03008920070031484000c0765052000140c15841d10043d101d110f1861400c1496038a011a50040c002c01a10a45a06a031043c2e00d24014500540300c0b19410303500a9030003511811440f011025419464604561748c4244003981d01c45c5a131441d1801c070083d0342d4603869800120420020703040804000d0740a12103444e002203500d0307841da0301d516144100500c940c0340010500018164182d03e01c554840c508021080b41e5444820003501d000039001080200c0c41001d4100d40308a461a050080721001d000050124a5040d016074400d48681003d000c0806180000d02104003240c100f0300284c003007001400c000c1c1100d82a4802e0090408040d40160315210480c8403000c02402c2400c0c1210441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 850395962 1250 850394712 850394719
    0x120210020a0c030b151302040e09070f260d1d0a060914030309030f010e24180f010617070e160e181f0b0301060c08130306060b0a14090906 61
    0x680c03510040c00700080c110303002c117540107030407110f9006c003401c56a8010030407120481d4a0303803102d4540c000302684810312071061032032904c0c1400c0c0500000c0f0303900c049599030081c09a030980c4552246500182820580341210300844c03401002c2d12105412110720051091040711092540390412201420207800360003050b8a0b00901201c0030100e0700c0400441d102e400004044402c001580d00c1070302d000e021003c445038040e0180085203140721115a81e03182e50445040d007042c1040c3d40340095498010140454000726110f44044004411403e100300c40103042e0744640d01003c00c02c44800a480d0000d250321100c04602414200028050086175801140d2510715002c20080d40c2030300042c45e148101c606c4141381e060b61905010320084442290302c1e400d44203051660703407030341e86082c03025450200b4810040411900c841c0440082c9041d802020f500d4101c420034100c840e00e0f612408207c035000c1d000306480020001d52610040d4210410342800710b50030b41058a04882c04021039003070f072805400d0a02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 850397212 1250 850395962 850395983
    0x80d050f120712050a0509030a050c0109050f070f0b030403090501030b030c090a0606020f12070b07120507031d07051507030c05030d0204231c05100c051e040b1602030313120210020a0c03 82
    0x5200c0403e4014200301303a08402121005403407111010c0e200c05992040c0300c52804042c0002560300103040c1030301d1055806841704038845203420010b40c040d0801c0c0e8121541805425070340b42c99070352003040300380c02000003081c0010342c1401d00301d01902d8890301c400090101c0e481000c60903480103104040b41d803800ea000035095003580343e802003542c4544450f25141c1c0800c3c1801c007044401c0e135240c0e020000b03091003c8048154003140b01f00c82c42d01c0300b106006d00703900418280460004984103000500d125071103450f0907814919551500e50541d009440302c0080d80e41c00003410441c102ca400c03d0104004034141c2c0c12043c66411038000b801c048120720100b83e001214030600c00500405000b900500c06d04c1e9007042c4502403030604020444e41c0701d400016144030060001450b010321010607a020303100a071012740c0c40c10203040f8500c254542d02d040b0403030b858403040011107074000021003168010100701c600c1c030035140c1803441089407031001c0d08005c1045600c2100c0d02c5000c502860485d008980c0c0100c0c6900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 850398462 1250 850397212 850397227
    0xc1816050c0109050a1208040b010611160b0a0306240305060d3009180905070321030b0609090a05060a08011107060501060801080d050f120712050a0509030a05 70
    0x2a0030303004000c54080103510f8000c0364401e02101140788500c1038030592800c60015402c00782680c0c880380546025001340c201d10010b200a81c0201040520070300c8480c00c81c2c05501c1100c00314032001c08a41c1201d0032003140800c0c0461030329014060400945010101c03060078140d6800f20340e0394101c1c0314825404041d25640400c896403034640107001071030b0300300c480358500b41030700c0b4019040d1000b940d46c0c81d01c0c81940150038610a40c030811a1303109803400c840c1c1502159820207030502c09002200c1e02a00c003030003181170003c00640fa043d0701c4000030070300541090f806060b280340501103030040c00a0701c0c040ca0041084640d540e0325103140c980d00c07000900703000171181c0703500000c81c035404a9030300a074070303950319081489510507550000390110342e12401007400546e8030f6981c21a1040c80038410b11401c1d80c444c00c03051110360b0040c0040c03d00c1c81041c03071466040500340708108040040980310707900401c0e2a21300704008010980102070380a00b00c8d14080c82103080c4500341c40c0e40e070b20520b603454041100126011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 850399712 1250 850398462 850398467
    0x40510151d04050f061603050c040506071203110708030105190b041d0a1503080d02070b010b0403060f050103021c020f12060f010603150e0702100504080c0c1816 71
    0x1401074007500e140142031221510701056068400d807010340d001c0c401c0d070710001d14a02e8000740280c4900c1103860512100d04200d0310036405020040c00f00f401c0141c00744404611a12004042c0401c00e0254905003502d62100c9009811682070203180d0b00d644070200101408202010b0490b07044410984050112000c607010300c290401c1c903900080700e03140000400217112a0114006285842114000c1d01030303441301c01c248000c444281703c4400e00740015030360400124802001911100c3c90340781f405480c081d004da540c100d00355001d030441416017001142c02d000b4000244144851444031a0040100b03505540000d065003801709042d008241e0340b0400b501c110344960a100ca0a108080d0810300d000c3c10440f160fa49800c403c903412410038082e80000203405100303005940300c0a600e900d001000c40d0030075045555400c40104124294441c00a000750559042c0c480d00c0c0c4150700030341e0b44907100d1030000f2000e810442003c001324811445100003031012429a03200b907411145100c201920100c1ca03820a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 850400962 1250 850399712 850399751
    0x807080a080f0106020a201f020f0c09010e0f070c0803090a170309070905100305070905180d090b0904180c051e0310020c151005090a020423011107060302040f060206040510 76
    0x448000c030199104080323441d40010b4403034900140355068034904036401052000b008000d12850440c0341d03100000c103e080b04100d034180d0304a5038600d090040b591464403401d505510540380c410856004400b06000e0100b100e09280d00385c1d900c03503521403a50901c1d0038955600c501500503000c09640c2c0310085685d1f01071071601c0760011580030069a00c100c0c0e5440401000707000440c0c030091200c18201c0d41c80305d42080032451000030080e40e1628240c036404c20b5000c410642000001d16049a501d40c07201802001c40c607102198a84618125042c5134245030a002c00070002c01d000101c50034106004c502a961302007142041c140f01c0340c1005031103080401e10146042c80391070800807c8a450802d0001103103401c0c0c44042035803401d842c11803441d10b5081d00d201c200d2059104140c50141c0030400800c09400c068401c20032014140760005100e2580c60007a810701c0607503885000849d600040c200000764441e6008402400703107002030251342ca006c3e02d9590701c9902000030302481d29a6214440b2401700c40b00c43c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 850402212 1250 850400962 850400989
    0x30a1805030f010f050a06030f0b150607080d142208040e1303020c150f030a091401020d06090e0307030c03030f050a06080f0d1b0807080a080f0106020a20 68
    0xc03500300405003002c0074024503695509020701c1d820031002610940b01070090400712640084010402441034a030041075190140c801c0c45040c3c1801d464100c0c5644800280540c2d60081048a9584441c1405002150504502412108250701c100400355002150754105a10552040160103c040c0350610080c4196040b45403c860502c0500c000842104005148030340300341c08840c2d4580c4030004103d800101c0d03681580ea451000c01c54045c5484c010400755410801300203011642036440e40e101e2080c1040f40034110001d83d408034041d408982140650702c02401c00c0d034420042042501c484a490340702c4e0f10005014081e0080b066070401d1300c07a90184c202d40c44210401c0140f4100303c51070304040e0000e03119165880c820240c00041c5020b001c00c55880001d03480e200c0b1081525548103042414200b80d90503114008140602c201262401000300740c1303451103a075040564034080205031481039041e045103045500c503c02540c0020a1510410b40e0304071603802214170f285d003000010303007182030b1200d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 850403462 1250 850402212 850402219
    0x63201210804090c021501030c061103090a0602014d04150207030204111305040f020d02040f170d0f0305040204090212010509190201050909090717062403030a1805 72
    0x1400040900182d4080c21040303503130b80d09840d84d9000c64004100e24600c00e01000c0d082e00741d240400c20a240c00340c26603c0d519010a01a60b08000c10400024003200b0f0590000d8090303519141541c01c820904055001c804c050f03c415601818599802d101e5180000105268a09a0601d50308042c0faa0441600c0c01041c034412019181c2d4103c2c1e100a46a00c001e1201301e01880c10990341d821881e10713400a039800501003031000140180352008000107803600b070000042d5203500b00030804e982d104600040010340f000100503042145442c02d64104510442d03200c00d856040070000160496101d4104040e035246842c0c0403610b61104e00008000380803280c1e0080d40720360320802001002c441900114480c2030081c081d200800c81c04040d880d03445161070710081c0010000c11844499140c0a080c40d50803c80100858403007a40328041c3c1e1600d2400c090b1080810b51040c1c0801c0032158900c0c18001c1000800b45600c402460240d012a99a0089440f9002031020203004035408c079403036008c11001010010f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 850404712 1250 850403462 850403467
    0x1050c1f0e1204080d09051008100b0d150f06020312040203011404030e0405070807020c040f2007050709111611130b031209010f0f0201090503070632012108 69
    0x400307122603a405449013894502480d00000c80b128020000305e0200c4d800a401000c040c0328045040782d056800520400d140301c50001e021a0800030a80944180a58410005a80c421166495110310515442109040000f04092010f2039020050326241080990000c0c084d0304d851000074094056102024a5154004100710901d0351024000100c490181d40410064a890b40119901003088520f280581d001c90344001d5182420350000c0811140340c00005610f50940341006005510160140400c020200f4103000f80082030210300000c1902d003204000d6160010000c90341402500d421140c5803003602000818071821108500390301400500c498070140b401e0034440c009001c1c03600d80784d0091045111040e603500d0140c0c07c5036642c641c16100c500d038034000301c5c10071640300d0002e504060131035407980c440030001f49041014001452003060040381114482e00b941c2c1010802d040c0740341e00250348601e641200b03912a101103056440200c0c8111502070031440c21180c0042214006042c1d0400 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 850405962 1250 850404712 850404733
    0xd050f030703080105120f0303070c0501090512130b031003080706020903060c18040b090a090c0e071e08040f021003021201090b121c0e120f0f060601050c1f0e 70
    0x12003081e041c0c030421250040c0b215580c403c000e940e011f1410300801694403c1001c60850350003010401c85031071162002094001f600c0d510242403020066281c40f03040004900d4400c0b0401c28030141000d041010500d50840c0b6008a100e1004a01c0c4d100c06071031070b400042e0110502525030103d40541034007408690301c40c01c02c80020782c0e07a80d0006913514001d61071030803408600c0c9002d00540040110040020308542c07100d040c081d0007000ca403c412501c0040c03106001070000341c108200351040c1910b0329018000c2c000001e940500d0129206004100070b4034408000003e07075803c0d001540550140c540001c80d140c7c102c0240d000748140c1e00b8803e281c2c1c1d02c071000080c401c902501300c20181e01341952500c00c810304a4600d184d8522a42d030b2510503490440c52000c090f02c0c4030b11001510207000070700f404403071000060300c1801c09221415039852600500c0c0d02150305a001c20009410810a2134250701d01404006401c2c1c8503200c1c40741424260304034106030440d1900a0f04181001c145050540f0340d03010701c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 850407212 1250 850405962 850405967
    0x2a010e0126180c01270312050702040c081e04030239060a20010f1805010606090b1e190203041503050c090d060f05011e0e04030e0d050f030703 63
    0x508a88040c0800e25441c1802d5840030b0101d001c0c003410a068440b002c980d071030561601e03848901c4600a180c80002100008045452640749a6000c90140c03151681c4148030700512044d0313200c603001003090000f04c8080c0080740b031208400705540e03d501f440f9903410780c0301c0d0316080703081030148880c0901e80d200700f86031a0703250311004441408940000424000b030a00309000c1c003596004100150f0042140030368070701c0e5004416000c1e0002d0400b4000002880700b601c2d680101282c51505a0b4402d14a506520300d0410009204849c013400750343c01d05400040c80e0035966013040c481c0e400203ea02d6500b03155005035040c40d40040d0341086050320462140c101c0c00c445e000b5500d4015219402031031607652084613a00d4000e124083c020740000e400f6500e001680300c20702c514a0a00c3c4812100b03140c1d580079120602242d40f16044c007031702400300403803003941006000c5204480136801081d856100074050100290b0800105007560714181c52011102e0a2403c02d2810724020300b82d120500c5c003000a40604140c0d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 850408462 1250 850407212 850407287
    0xe01050c070816170d050a1d030307030c0203060a05010302221d0a200a0e0c22080c1c0f1506060e0a08161e2102032a010e01 55
    0x2c041c0780c0c01c5400100c1591a41740d403004915140740200f24100a000702461160340c0008003280300074408a041241030012900c1c51f84040b40a50009810880b110118a410301c40d0720340112070414144155410343d0001001c040b940407005984951185900c0c004001035004603400d0341da06011401c1e0400002020358075101e02810499000c02c403510103a208018640449010340d0b0040e10411b10142001d0503034810744405410880c0054003030240d0207000050f00301d6601c44401314840012000d207440201c52a00741d0440290344a001e854441e1500402803400301400700c2c0d040802d01102811a04000700e000d03085900010030b2a05041010480c180c2001c162140f609095841114880e92140341c01d48444040340c0d5000040a000810401541c4c0042200748034241c08005d10402039484641c1021060316089015400313901000340015850300b0321070a0741c0c1f440b600034100e040070310261042a085200001c541c0c1400b002d042c0900b82644103011181c104410220a0f5030482d916113400036221 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 850409712 1250 850408462 850408469
    0x180608070e0919080d15080f15150612042402090108060909031206010e1810050a031a070c0804031406091f09050f03030c0301061407030e01050c070816 67
    0x2841002d102c81402e11a4210882c91183c001c4d5200e41440d00064810003e404100c5003d4450050660085a0018244058600703541e0b088001c1580050741260110440c130010072100c1103180303c0e100c451035901c540045131140f01c4421080c011a80d1280750400c4107e0040d5904a042c003031210030318034400c880d0b41c018440f0107001d0301c0311343c480c0e6220800c10100020850303000d101508240304803030211007041040c5401117014140f1542145076480421030400c0201055a0b002040205000c403100540d02203502600b401e494440940703046d51120903500b42c10040116940788007a00103108648110f414081a0342d1000101d41c0d03c5660f401d000700c0001c40c407d10508103029400220b444d1041c00224a01c8035a40060400345030b0010390420340061466420070380d100c4c0a90729408203803050a0005601c12244001425281d50504000030660800d03107200c0320000d1010858003001c203402007000300c0c103584240f9000c1e030348001e40802c15040021940c008003d600c5102c14000813103041485403c1503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 850410962 1250 850409712 850409731
    0x30309030b010f0510030905010b0312120105040218150405041406011214160918020a1103090117060613260a02090f130803090109020a0608070801180608070e 70
    0x156601ca80a5203c401e003144507065000707102e0036410302e0140c02034008504c1030717006900001c2d408021001180c01e00342e003e03116079040c0f00c00007224444c50801c407140d40d000d08001c0e1000c42c00d02e50703881d40d146001010521003522821034550101442c00441c0120385c084c0c60b02820521038040d10b141c903200c000304180c50680c04901d003280700704c000074980d10884050309203d42c3d01c0503807034036410103030092000e03a400c2c0081004070b45080401e48030b4400b04900480d01c0d40860043e036918451000514107001d400360954560000c00070300c4060303039026084600401505441d80722940f50400003440c584151f80206211880240c2d00150102d85080000740413000d008445041b120007000d0280c650702c1c0711b00000c0d0b00c45d035440e0120704820002080310754003001d8070800c002d5607890364032410416001100d5406103691a12101421810000507510003000c403414144400e0800510141103800c05008a00113003139a4100c0009402080d000203000300701e0f01060715251a15203840c452414411580741c0d40 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 850412212 1250 850410962 850410983
    0x21030a031e0f1407052803060306020c031b0f1b010e182403060103110402071b0303020c012604030207050a030c0323031b01021312170c0a020112020c01020403030903 73
    0x10070601034800c441c1550610343d04500310301c0146c0310004c642c082c481b0102d01059030715000840040d02c10320040481d0340c50078000f5034490342c11200c103071030031540c0070780300c0f04c81ba0010001152003443c00584862004c5c2c525a20004c00c020200049030514011800b055001c01c81e64075140724581c5079044540601501a072001c1e03940c04148041c00c121004c012201d4140c0d10400042000c101890444624441d00900251401600c1d07160407901c02c80c0e050140064090b04101002010b0301009840704440083c00c0031424110754181c06004d40824810b1001c549504000260403d482400a08054407004002000f590b86a08200741301e0744850104440840b4100300902d0355410a5101170603612400008516008140c00142d64002d041d1420590540d000d018149501d001da1000c0e20107042e801030201030401c910300b80598001c8801c0340c100840d140c00c2140c2c102000c000b00b903081160b502802c01010170300304582c034100280b15840d14080154404a0040200350307120045c6800c07a4082c010040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 850413462 1250 850412212 850412221
    0x305040b10060c0201051c05010314060f0708060f03070b130807171c0c0b190b0f010207050f01051b0106030c17030421050f0c21030a031e0f14 63
    0x10011030b401000e0110307950385800c60043d8440d800034030103942038002d0642e801091803401303020f565082c0c09c1220400b0300010b80f0003038030700c040021590040c020b0030012010301300340302d01402c0f40c5c2019148a01034441420920040d071002c011000040c0301c68105140e81d407500c0403648003001c1d01409031514074016210000381710b80c01c002940880310100000f40a210882c1824141410407500015081c425400e00220119000c2c0030f440f0310410b0218503000b419080c2010060031640c1c1110454800c105542c00c2401d5640d0014401302625003da1382c4850458070580183c61601942c416500c52100c80c40f9007195005047d0800c80440c2c0c0f0070080611281c0d1120401424501075903604a480c0c0e0084c00104608184102d0036024030a02c0312070003030f46c00c0341a00e40302c1c200b1000c0f12110703689901a50b0b00f0300c01c606205403500c004c014000c100340701c00821409155100c1c4100188801014ac8546101c03440040c06184148482d29003502040196403041241025080c0b4400c21014842c80e8400103 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 850414712 1250 850413462 850413481
    0x6080c010e0604061812050109030905010512010303050904020f04030f020114180f130e0a02012003090d030219030915050f0a12110708030901060b0715200301060305040b 75
    0x550241070028011400d00d41401000c8640d03003ca2810790940d00121365000a080300f80c0003591415600440002c1052001401d01414501995018070704201c0c00f0404140d0b044448031280f419243d01d4a8a60760301c0091400140180c0180d02c00402c110100140c00001c000c00d107202c0e101424401e89071002080d5030f400d942e002c14050804d241f075030a013101d41d40402910f00040d9510241c0001000c0f46509007000c102541102c0403240341410550004000d00150368000c047c0b2251a122042c40d0382c0d01843c2020748a440f0300440d02032034001ea050349070b104201030092101340c4076102a040080c0c4030f100f442c100140102070130310451104007000360052440d50321600846403043c072091103285c680290703554115600076200e6110380a450383c80f5844c013005401a00140300e00303405003032101d40724140301900c41d08540d999030100404c6a0100403010000701c0f6180301200250b0b0b002c074001000b014852016400c5c00110211910542c400000072604a4050703200038025400307a40c2d052425591103025 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 850415962 1250 850414712 850414727
    0x10501020d270b0c010515040c020a0312020d050f070e010801030209070806030a050d02030a1107080627010f0212070206090601090207140303070908061b1b01021c06080c01 76
    0x16000014003407042d8440c104640c0d01e01000d00c0a50100c84805107030360742d8030105590401186003c65035158001e00c00b9a10720b81410303622058003100c040220f0302d25000060b6503418040401410f1000420460380c5256103a419180b025291070340c05d00ca103140c41c503c009010a0100d8624000c04d1080762440c0c1c180d4400c82034141660743c05440c24582d80c54206064600880040c5420b41c540f0880307415000140050240802c4114950010364981c0d001c2640540900e004814001441d40410400c100000c40062500d410820300c078820040310754807082d8003212025400c4090102d6003010b100305080a110350040c01a82c1804c480030301140c8404500300d03180d5005840c543d4803a03112400520500e2129030050009030b205000810075030b15561000c40c00d6801c00c607208000304285800030024000144102c552080044403080d00f0690b51a1844003503000b002e444640d840c02c85020500d64030400d50480351401002071883c041020f03001c81590213040c4e580030f104c1090140100e401c0b03155000306003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 850417212 1250 850415962 850415983
    0x40e1b0702010e1c0506060a090e070e070504030803010806060f060a080103080f070501150e070503070503011203090914060f010306060503061c1b0807060c050c1009170c0901050102 80
    0x6440c0382405079001101d07a190320b41c0f2070a80c0100704501007070100b4a8440c0b41c1e8405413040002d0b20740c9250000400c820601c1031740c06810090300b442c008100c10751005c28008103550800e504c8007041d89401c081200c00d40102e800081c06401c0020010070344c9070000035800e10881c1d0403200341c10790004000510110b8064000d00401103030715000103000145036000645846001182001d050405940b107807829101140c1d11031102143d4101c052241800c0810400e51041e05410401d1850401c03c41c004e0040c8014481c20f5468083c070201c0030201743c0f24504240092101142c1070150010b410041e401c0f01d00706403910b51250004e2800c00d50154020702032601100c0742c5880f25411552514244002005100072020f140441c0410190010300200900c10841100b5802103001d141020803e80c0382c600c20350052070500900401800003e213000a030708091150a84442c9120194808190740c0c15503107410402001106200e28000024001285010074501311050400f5903695001079883d030801c1c04 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 850418462 1250 850417212 850417261
    0x906100f032406051806030412080402060f0a050d0b011b02130906060e0a06120c050d0c0b0f18090f010b0f040315020a080906010b0a1103070f0305040e 67
    0xc400480daa8000c0d4054201601c0708420101c0355041c010804032498000c0d004a0701060001c118009083c260382420070445500f6a42d59113507041c541c5490380074000d1002d540003084050800a01151a04019212001100302000c3d4440034180380140a58006c45241425585000381c00807c0c0e40c403d0100901500c10301358824600070854007030246858901da00590b074240c4420023140003940f207104540c01400c0100c080d0a180c03c102e4442d00c1910307a00e52046000f40c0110302080086112140448200e81c401c841480155440e450180110141980950403c1c1d2010854003c0001400018040000c146460070080041c00707003000900d0303005035800d8280a0004005220000b4406d000b8a0700c65856402d10b41460b640b5503601502128024604c4501600464295402608a10440d420610302c001500c41036050803405142c5e030080441c044c040020803a00e41c0c1d00b0440510840e2991500600c0d01d8001002a00300a080c6601600c01c42c1081e114403800190703500445078078005104c41c8070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 850419712 1250 850418462 850418477
    0x20d1706040e010b0d03080601080f0705030c0c10060e07030e01050f06040c30050108010c0c030e010905150301060f0212041413051509090114010e0403020f0f0c090610 74
    0x6000c01401070101c1061150361350000e480c000d980b8009900d140a00c6903403501954548140018012070000e0004031412005078144004c013a005000d4070340c852020b400c0f190322088000d207a245407280003030340038043e103281c01c03c0442d5480c100c040842c031030b20054a0a00c40450455005400c0754403c50703540d1802ea030601c021802600e019045810744440b945000d244000382c10f82c0d007841c0c0b55181c50032141c0d00f16080101c0203819500d030060b5801062150001c000000f10180d000d0400700d0014070003410014228070704802680035184242c06800043d21030a070807980300b1840720b0540d1003805640041101080011821840059006064040f25226a0402d4508004140c40e622030743c500d1a444584010100d00c0d0354620721401e84520441c0f0410702400c4e000d40103120443d080078081d00302907410810502e4188210804c007a0440f0800e01450701140e42d5070a00720309040c0b101480c0000e5003c0c640d1451500240028581000301045501c218079850b20001c00491807031084041c0c0200d400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 850420962 1250 850419712 850419721
    0xe0c030a110a0b0307030b0f0607110405180f010207140c06040603020703090e240402270d2a0e01030f03082a0d060506031b0a181401020d17 62
    0x1a00c24141d51024080c08a104040d01e40340c04100603042224a24000303603445140c1e0b54103203000d80c04c80884110a848662605c04a521884040088482050b00a6454002041c126038125010086800440003922010f40803405024080c0d442102c09403a10344000140c1540001e010032448112140109290b250500d440400d0703000c0c2d00841c0307040e02406003502000030303684145130702c081c40f5011031540c104540522015a43c041500c000c44036010b24814050b2440e9586030076450307011000d119000443d40789400f40001c210f0406044020b08040078881404d50036600b441e200103481c4411130100000c503458000030480440b00b40310250400c1901440d10707000c40d018541480d0807101801c490485010b1910b030011440007031140306840582c001404046003149403003102e015210032504d0500c2d5090a50240b0800301d00381c00505480b0100040500456014000840310744c1d464800205000399107440e50080350504c0d900d200c0c05800b400c541000d5a41c415131455074111607003403200010f504d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 850422212 1250 850420962 850420973
    0xe1608011e03020901151d0307060c0f060903030204150201020304080f0a0314190c050702152101090902040501080a20031618150602070303180302090703090203010e0c030a 76
    0x80e0098003406070a05000c40581c40d8200392501070f00900341070340100817007a0001404000700341115001600c3e5011400255500404c3d111f040740c0b01ca18008480f103507a82480c0c20101c150751801010030340382c451500105501900644112482c1c916040f8441001d014140d003070340b00c04c0b20018a100b000b009480041d0b04d10340c015101c0009285000110940e414050a445200946682d06042621b201042c04800c2e0385c02000080c50b503070701e4480e04028032540441c240d041c440d03038aa01d114001103026089a907200b0500c031950103800034003040d9540d40e544008000c060300c010981c0a54149000800e0000340014111082e99015484440c160380b0008980d08121085030001c0d0b043c05501c00c040c012484c428071040c0a40711080d2000024460250124221504070741d10000120300c04404000c1190085240000c0303d8242c1040300c030351003042c800c1c4070f030624080d000254416004000c1c8a08540e040d4809141ca078070940c0200600800103007255510600c03c041e46da4540e000903400c00c0040c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 850423462 1250 850422212 850422239
    0xb0114120625090b0f030c04030b070804050c2e030b0901060e040b010804020d02040c0e0d0524070c110607060f020307021e0309010e040e0a140d180e09070305030d02040e160801 78
    0x1c149002c448c205a01c81e96207525410068a82c6400150308005001c01e05c5024010120708000443d02c5c611041d440c10124002001c0141111007446891100d022807a40a60881c5401c081c0051400d48503603120400601042294205140160710b40101d95400b540225126401aa001810483c4117070165003000301600926141508001071140b641c445038403076421044101e40300700042c0104141101001070f114a02040c10004081c0c0c1406101074280c102450502042d08078286a911500310750106229200e038810042000b4030345911086107075003a43c040e500412080d420703070780c0b00d111031003825a0161031021081c0303c5401c00c02c0820040e41c051081e103061880d001e03001060310720050341c0d401e081c00e4454200783c1c1c2c0d01008450821036580300384000c0340c582105041c031903e0442155258151200d103070003110346400210011034040c0c08200861801164000100e0b6518050a01c0103000b07500f241c407506076006d00103000702d50380012083e82401080755903074481e10142c3c41c2401c1c615251 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 850424712 1250 850423462 850423471
    0x3020129040b030f12120c071703040c0b0d090302010b01030606050d0f110f0406090e040507060e0117010321050c060f04020a1a1c090b0114120625090b0f03 69
    0x41c13196981040b02c4e0034091020110f85400302c00c0f010b86030755aa4050390301d8160000c009061640b402c129a40c0012903d840184080b03038074800070740e2240c2d59441d0580102085400141120364041100c0d407030300350f445d0480903203144290b00074003074440c9142c01501900c1060051801040f018000303003102c2005581301d0301c1c1c0e450700c400e40440e00340740c4034404204c282d101000060a82c44000303824002582c110304007100a003d40101202c0c03614003521150780340d6805005802c101300360503031079041c1680b2a0b804419142c01c2848903030307100d5035246001c080f0741c2c58010f03440c3c100012084000c20414019019206003c0e180009000340c0c1d034502a828600720b00051040380d01032400000421a20480d01d4015001d10460346816a5119803900c0c41103440f0341d01000301401c40c10540490009913104041d541111111140d800b200b00c480030010b00540c05030320700007019105441c00c001140004821000b6140034481c0e060340d107409080fa080361200c2841c01516004d4204200300701000c41c1c140001c44c0c1c807 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 850425962 1250 850424712 850424719
    0x109032606150f0f09040c21091a100602010c020c03030d051f06090602100504230316060b122b05070c03060209130501060f03053103020129040b 64
    0xd010b030007503007450150000c4c8010369a1100c082184545800c00d07124811020100c0d04150340100c00811a81040f00c3d602e1080032445a1100030b450100282d41c2c0102000044150320b900e140e1400ca208404200040d105000041d82421028801540082601403c01c03402501661400790350911450180c540a000e84041c403600403120b00886582000b440060842903813840c401d5807a1850003407400150300300803031302e162400003071000058069a10250304070340c10380c041c1c0034025107156503400d40c052a4091001e004e84203001d003040040343e90140314000d80c100c0d05401501c251301d50300c5588e08400040c07a2042c0d003100d414250b502080b007200f18114143c9103021803038044950f071076002103140c50348202c0303116402083d030b08058a05a1190400b0a4607400208030741d61410100500e1074181c44248024940e440d804148030000780112141d050001000c2009200125446034100c3c0c0d032802d0303003038006511b0407200240b1003594643c6c2d410005050b66040100080a03400c02c0014030041c44031550 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 850427212 1250 850425962 850425967
    0x40f0b090c16081e030106050d0e06070519091e0512030c061308070f0b091c0206130809041a0909010b011d0103090c0603020c0d0305010302131e0905010903260615 72
    0x10703840c42200440c00303005150749540d03c60508452743c90036550003050a505035006441080003040e4004c007501d0b600741c640b075403030305506030384c401d0a0343c00140783d8101c400b1b40b000c0a4110305c0b52018004c110021100d082c0c03000540728803203900c016141c0c025684941c445400445c082580403600c2e2607100882c0e0f0081803102d01d440891742e10340d01482c16803003044401911074800c2110102c3d0074010021980c9014103440c1c2c42a580300002510b980b00244031a0414040110510070300c02804140c5894502c0036004000810171009904101c940b807d510601c0b506000c800901d490030103000f011991041a11a9145a01328403014801ca22800300018109640e40c03207902c2c0400d08045005c002840203480c0144ea9041e55601ca50034001000981c1c002d150804004000503115500000e407030aa0001002681c41c402c020480b0340e429048940601807810303e0b021200b48101980310010261281e124180300094100741c42047c0145903c0003c64010004c000911b182003c1c2c104040c102d482640e0b462 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 850428462 1250 850427212 850427257
    0x12080901090b0c01050a0b091306020a02070504090501023403050f0d051e0a0c23190201020301140d02031b0415030812070e0a06051305040f0b090c1608 67
    0x4202c1c1c02841d101c03c1503039143c006000400c000c5114860049000340e031050150b01e044d1189440c410640100145840c0d4000762643c009031003032000794042c02c0c000b80b00340001d003110300b03001e1b020303400501e440d1100c3c8403d02c495002c1e80031000c01040c00300300781e10190310100441d910f0688040e0424402c0d001e1404080042c42d405019a2003828801c01303000b4900202c010440d1000c62000b0402403002940d80c3c0b900d4484895603400811b814400d4a202c104032080003540714030241c0b00d020f5000184048884a580b6104441d01034000c0d5050300c0c00303101d06074010181030b000c0014500550720081d400d600303c20110000c0d00c1ca211041c01c038001e0042c0010400700210031190a14500716402542c02e1000800c0106105501305131351500807040d0710344207504442d03000010316141203510800050010000344080c000c036101444200030300006004105644401700302d40081d0103110406481001044001a40108604151042c5e15980184100c041d2a103030344e1140c00381d10084104596180d04a1050b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 850429712 1250 850428462 850428479
    0x40b130b0c2121042f0913020301020f0a0807140703050d090b130201031b0f0c1a0f090f012904020c0105040501090b090c010c0206071505091b03071208090109 70
    0x4442d612110450349032a18081c28080306000f442c0d481e815045003415040350703000ca042884105e007110200d516103900d40b81c3e01642c0007410000354000b07406500108401010002001c0070f40720088650303d5211955507480d4085a001d100100d130007181c150244031480c0441d21500c058000c4184e01d920010300c402103511600c6c01e14104885607401a160035032103000715607150044140d035041c80e42e4942002e1700c0d54240034111624000000b000c100c031040202003031010364010851080c2002e0b1700c401407420300c1d081802a000d800c0741c80007040e2003207807444c0c9001c080c140300b41c01031040d428802004440d202c1c02080c1c20000d0701c00701d10768032540038807032819204420310030107010340d224900010703034002035103080201130f0780c014003841131608200c0c034901c250b0340c05c840c04455150341103a0085e503801003490074580b1035030864080f1a80030f14040400004040004100e1908903d0055144120b8406000c15a541c0041d00590f10606c1c211070390b00c0e0000764050060140048141454140d480d210030300c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 850430962 1250 850429712 850429747
    0x110706090528110f0d0c080105071121090d05061306060e04030f03050a0608010c0f09170a080d090203060a02130501050a0c11040e03040b130b0c21 65
    0xc0d282070704105008140d41828004000500b42c0300000c500300311001e600c94010000a2118282c000d2984a504044036a2a40d07810740d903040d4007481303031604541c4680c246e07402001d0494254011030100b40a00300440d90008505207400422040c00111002c40384030041d958010840a0303421000740080c01c0d00080c0706009031841480c1d000c49002c42100c950030904266082640940e540c05281018400031940c0091302860444031130801003820f40b14416150001c204c1c03075100c01c0082d4600b08036226050ba21010700000d00d485555040c3c80b0039161304480800c2402600d40105030780c4400702000014040101801e00c0c0209031500041042d842c4d000700341003001c1114040132151b80000c5204064451a80d4540075007001e180180c00c181c2040c80250191103061400741111050000c0c0d00c9940e559500060000782c4140140d0f0b071100e503a11400318103604480300da207100040c00000494440000d0044e110300d080ea540003000030421900c3e40001c2c4e500c0003840c0140d40c0030100240180765500528 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 850432212 1250 850430962 850430981
    0xd0c03110d0201050a2403030e061b0303070806060a090512030712020303071409011205040c030c26011515091517060a1427040627020d0303110706 65
    0x1203a545080b100c981c080b01d05840c0c02d42c01b001c0007121410321194203031071071109891741401d140c001507030804002642c6000b0030314590318142d800e0449820400d000720165000c1c1a0580381d108850f03c403041040500d0040040c01c1303000581110080010703280041406005d00c840300d083d285010300035280e10340703030002c05075011025032b0001080c0050030340c2c030941d44c1c81c00b03001c1c0354803080c1006284c0b00020306070b8041d480100f03d83c545500102d001d002000c402c804c02568800100350005554a402115208041050030302c0b02c44142e284c0300a01c14180141c4056044400a00c804207041c403002d00000c841041c040000c03c0a541d10211303030004480c51202840000e03844104078800440a2140a004000c22113409a80d200c102008208407001e0b000b0000d80040720750101908401c0b1103009100401401d0100200316070050005010070369200c011a80900208000050100c5180e0741c4042da4501c8020340001c21110b603c0d0200388654080f00041000f0107600d0f142601d04c1e26540300b5243e40c1e11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 850433462 1250 850432212 850432217
    0x60e0a1d06070201091203090b0a09060b120c010e0301050c041a07050106031a15030d030b2b0204180b06062b050a061509050d030212070b04020f01110d0c03110d 71
    0x4000103000c581c09103010100307110300e014003080840b59500c20500380041d2000f900f035511261608104013640d0800c0c1d0600c44042e020ba604e01004420b51903a03100020102d03804144c69011d0206107082c18007440c1e120b0140d9103c074031701e890300c0c10750710707007102d815071000c628044100f4040180003490a004d608025402091003018510600c0681040c170030000e440901117148441c41041d035034601181041d041207c905000846450b9100494072100d5561502808800300c28801070700c3c0420422800700c8540203440810255a4500d052030503246c1107080a0940f030140000a0181e2030f010740105488004205c0c0600506030400b160750003507498004100546440f00e0410486003240e1288600a0030900c03600c6148000d012000b070801c0503503000d5940606403441c20081814002c110b08207400d02902e03c00360340e030561800c1c01414071005607412441101d003c0e034600c036550b1203102c80d00490090200580881d81c5840d1003900e030000c0019041f803d0008901c00c1c021444801d100e112040b40068 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 850434712 1250 850433462 850433471
    0x813030e33030609060f0117040204230901060602010212010e04050109120201051614040b0d0209060403030207080c01090f0e0a0f020f090405360307020a03061e060e0a1d06070201 79
    0x40c10040804402402e09021b4405180c0c3e09090341c2c2d209040380406500c42e50265031035108d50010902500b15141800a1611000d1004d01c0125030f03007003c1881003038114020865035888001c200c3c00d03446050b810201c41c0542000502842034011302c130340e4000c3e2150000040b1180d03140d40b4030b000c010304903c205003d0303503403901045814240469900d2044445e0300c0c15821500040c03c04c480d150007140030b0300114400104010100011690480d04407240040c43c035902e46030380b454000d540754407500605008c0d000d400300001465001e140081c007500e0790381203048032050400e0b800d41e000f000001c16800348903444101124182e11a840103180b022205071240d66182200000c1c0419280007410003060b0340d20a0803101725001608040303080340c0030044002042d8001e4500306d2407660280c20b001035413003481400000108009030340320904c41015900c16a0103900c400800e08201c070468400c444689141d64001034024a403075211000a80c5100180c1d00384040340d000042c0f40600031039000740540e554 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 850435962 1250 850434712 850434721
    0x5070201031503021e010507020d0b4302010906110c0c060c03030403030902031c081e0402010f11011104080313150e09060d060f06060813030e3303 65
    0x142c0901c0c4200c00d100780d40e0342021440c5601003992404501e510241c3e548160440c1c4000d40e1162084400541d001070022180441d80e061185140384180d8014685901020b01d0b2031b00320096a10459003480c00d200034140812289003520307540c810501032039045542c0c030041d00000074880d201d840c0d01c5440382060300c0d49400302050340501c0d14207102005442040203112640702c01030b0010840307504c00c0d41850045652019031022918120174110140800030290031840c00c5980c0c0b14040500c81e40c062414088410707005924800780321030503100640040e8090302000090f0f405420408481c107450400000c64500300382ca0042c803500305412051140e00001011082404891880c1000e024420002c00c0c2d581d81e00980a00481100b01d031482c004d0b01c8030030009080c0d40d148891403100325000103042c01074400c03c240900080619000b1103007c00c81c01404511000440e040c00040558592559091107240c18204059522040b00c40d03e0b051580350318964602200c0e001c02d600581c00c641c07049440b41030 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 850437212 1250 850435962 850435967
    0x30518120310170703110a12081e030f160f0512180d0e13050c04031403040b070501150605040f0e0c09060a0909200703030902010c1e05060a020703090e18010c05070201 74
    0x307000b06c0385449281c25041c18004a04900100c9542691021110341d960f10000a244900441194841e607040e501004020b52281626406481081044440102002e900c142940c010742039031920300000340c05000e00e0b0b0601c800342c502d6680110f546880e451441003205c40d0a40f0700f005548030300c00011302080d07003000c580c1803100654074007618412080c40b1701c1c5480b4014035800d019034480900185161120390f0060300d0140100d0340906054001c980e500e0100e1b062190203003458040c1c403100c01c0318074000041c15030300c07039000c0d24140c2e010300b00304060301131070155021410100602000500c0c90208041407490360355000070580c02c00c2e942c82d000410b6140840349406c41d080e4481c95040d08021080700c0080c4e040840445100c40d500d030500140080c001c0c00101da1501c0744c4c100003031809052031002422218a5080310f075090780304e8021641303182d44140325101680205a00100841d0100000344000656414490352046814450030001c8000c0c82d4600d080d98032003d803034004203000284800541d40d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 850438462 1250 850437212 850437233
    0x60708040e07120c39020d1a040b0906060907200f071706102616030b10050105090f040c0c08030420040e060610030f0e0d030518120310170703 63
    0x2201c840d01c10300c02c0b01e9007004d1034804c2c5d007800720001d10600d9943c80840401802c040c40880314550307107614074454500740c5083c5074002d0041e00c000c55144120b5001a43d2450f081d841203101e001190741e0801d150a0403440281a1440b08156643c180505a42414a00b0003089190300815285a450710b80c0b07250f101543d400c0c0b90000e03100c0c0310030440c0d00009204488c40c0340100c8598103642c0f01d000b0540490000e449003002803400d0a0f0201c00a413102c0007003408040d800403805280c141c9105500c15075150010b45452142c40040c503080f601d0808041090710309580000c180d1021420301002410342c55a8076034190b40101c03011a550450700002c000c08019841c40240914404c0e10308102800043c810075545002c018181803040321740003003c100882c440d0f0481da507070001d03040c01808020103543d42c1c161500000410354000034503010004840b8605002c0c412680a1b850001c0c1030707a10380000da0401c00b030b44014400c01c2e01c0701e030000c0d000806c0000d070200380c030700821001d01070300c0541d08500d400d11110 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 850439712 1250 850438462 850438517
    0xa023105010f0f180801180209010f030312020a1b03020a0501050649030504090f050c070605070519270b040e0402181306050105060708040e07120c 65
    0xb00038000d01103010340e045440a00e1111203410300c04110111803184000030b01ca55000b00311254240100065410811141607125501c2200c0c42c0740c0981e2103a041c4841002c2c00d100150000b601d90403401c41601403513000340740c69100c41c82c05c030641000b41ca00f11481201c04c81012070050b40042c42c0c01c2d0600c1001e100740c0e608407404076003440d13078040c3e40c82018400401c820f802100748035441c0800c202c00c5103c0c861820000303c110489d2086040c02e03060250403a0020304c0362032401414460031a1005406105061280000c0c2c03103ca400c181d07094031064020003004080344180075003040b44007045048241c0950745c007422640d6030aa50300c11242c0c1030900807134400c8442c2501080032000c0c8800703070901041e201507656801c142c05442c0d4481c000103009100c88035000a080d5440c0381030200d503e032100c0112800c6402054140710990381e440a000040c4500c031006040042c041c04203103d21510b150a05402c5003491070700d41c0203503003402008800c0301d421120140100d4400c1d41c0032500080d4482400e00c08 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 850440962 1250 850439712 850439717
    0xa030c1e03081b010b03061306140103080a050f1c09031b0804060c020310050703060501230d05040303090212010b0f0405010e01030f02010c051504060b030c030a02090a02310501 78
    0x40c00d25542d558091401044081d00c500840c2040d510358007842544006221700c401401c1340c03024207003a942c0100c012150a0250f60060400e90f5280c0d96030704c00c010a904032540240500d24207406410216840e81003503d403c0044dc80821081c0320200b8405040c0e120000680c0d000a00300b006407030060601c0c01c0c010828891608400b15107004502c40d076041c0d4088600d1410292018000c5100080c10040c0460030310032003a05d07003010b00c01e100d503041d408202900c40030307254134140092100f4280482d40b101c1415080561341008102413846442c0c00c0ba5030003c1c4a800c02003050b003440e600203203855035039207041c8015a5450000d80d83d1454075010120450000b03440c1080154109681c241916205004c003a10b654102c0c0408001c5920801e6529005500a015070701251000c49600790004d40130349080e00c0c00e50400c010003925107000320303070341684120042c01040da44030035509002100d0002000760600c81c0c2c1c02e22010040c0110a0311910303090072500300c0c0c13016945810b10400d00c420910b8104904 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 850442212 1250 850440962 850441019
    0x40b0a09060e0d0206031003051603021008010f03120e180a2306060307180801060612050c22090609050402040f0504080711061e0702031002181e0a030c 67
    0x42e41d1100c0002d243c1d91a010b407032203556560380491032044101300f903000604034491040c0003103242c0d40440c10b80007503030700c00c9503c4c0441c088e03154001c866204082c00b804030906941001000001c0c5c802240c0340c1c109600381410103807540d90300d0029050080440e803194142d000c3d441004a9a5850b200e8007218901040d0314445a4240d055101c0c1003420080405004020000104012034051149905100014a16001c645460700c05180c081c1200e4032400001c500e40e00002540100140182881081090701e80c5080002d08800c120449400040b00590071082c98400b0420000034003908000e401401e2012509003460310511040313800714502c0b00c40c0f80b0316000500001503e14400c80314616081448a0000380302c801c0040c40500c5480c00701003000d071400a410400c40c0500000d000700900845c107849402840c0e1103048168840d00310080100103051502134071b14507100c2c0c110416000850f40340b00c95a40620003040b05d0102c50340003942d13602c0058100304030320b0740341840b00103041003044210f8a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 850443462 1250 850442212 850442237
    0xe0f07080c0c0706081009060b0a0e09041101031d1015080a02091611070e071b02150f040b2d0f16050c130b2e0320040b0a0906 56
    0x5480700f03c2d5000d40c008204003080072414171030050104d100a0403c020080005a03a2808030b035019900c0084402c0c00300d0100c0e034844402e4070300301003458800c507000038401b02d03c6200c2000440080070109218903110a8000b68207610820070065500e4115007030b60b0010b1280407091501181c0ca025a01103100c60f0300280c1031100584881d4005500075401c5403107402001040e0006440340401d00040c4241ca10402d01c00045030b50f41d118205000b100d0944408043c4140c8008130b22980342c117450045c3d04900c00488124203170340600010001c20a44d100302030f0415072541e01d94074850b8402d042c680d1460700045891004c0107174016000040e03100328051103140c260b481c0c10702720700c60007182003d010441140c600c41c402d010051010425030f5400903d610154501d20312160000d000d6006c80c580198034220100322910008102c4600c40d0340032104440109106a6048028194003041f40203142c5d05840611010a51500604050b10030141a00d84030081030100030502081540910204502182c450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 850444712 1250 850443462 850443487
    0xb0316060819110a03050c070b1b070f0501090210080f2a0c150604060806010909062003060114040509161b03050d0608010506030613020102070e0f07080c 68
    0x100840c0c52a0504004a42d0b402050100080c04541c6801100f4100074040b0300c0e0f4039803003005181e07444403510200403070b407901107100701640540c007801044082200003044103c98104c843d00102e90300c00d030340c5074a0281c00f680c03241542802d10000f160305a4403041f03803404601d802c0360b80c0062a40031b460b01c02c07031604c0e0605c002e13040700c0300160440c209109401c0b840780700e11030781c030300c40c0c0c0c840e02e001d8100e160b82d4010010b0a030f0b41d1540e0446076030991413609400f28043d0b103403500510045446640040000b80d0038880d20358000c0604800854030030b1f82d43e10030529404002403400021350f5181c08026105c0c50000c0015049210402e800700c5942c604000a00107682c5489005400251000a441080c00444411b54600f504051108a9061712041e40c0341019481001001e10949509080c00840d9803001801c0c00e0350380a41e5581d40c140c1000000540d82c165001902144a00505c110340c501651540c56044030a020340347c4a00c0603480400f0010b410790130150349500040d003a000c05280445502c8032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 850445962 1250 850444712 850444753
    0x3106050601050a09030f02030309041b1206120b0a02040e090a051b090103080706090b0a0b0f091e10030c0303030509160806070c0c0503010e010b0312210a09050f0c040b03 75
    0x6d284075903640e4500290f40b0304105545000402500c100210200514268a001c07401500030340040d1482d0340d1100c07106814080c00d0210307001c0c410484d00f20343c4a40da80c50191100145090b01d8958207010015100e03140e0b030700490042a030300c009411714050790f0414900340381e2881000c030b00f8030411544030301040e00c4071090391341107903007142c08691558500e1401c08003505810901034018440c54017800015180da81c84009041400c513102401c04012805100010310304603403959a0702e01b0305064120285040d510507505c0b40b401032021101c2601e81d0390785101e039195a001030700042e03540e40410445440c10403420300d804185d601400c429510300000c25a44036002003440c010000c002c2408410010400d0b0018041c000050083c895014aa5002c078000c0c0008a4407a10074807c40c00c042c64100840f004071003400030100c42c880100c034094424604a0703540a010310b041661b444181201052060211412003101d6070040d06030b160b56030b0100000e4039a850f418600c80e03005140242490301c2240c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 850447212 1250 850445962 850445969
    0x3010e0103030e18090606210304260a0309030606360f060b0307080c3f040b090616120b0f0a0303020a0b1303173106050601050a09 58
    0x510442c8003c804010960307101d11099054105088803081c44000480411828401e03401952a00d0754100d41d411054011040b4451140e2960070811007031040c0c400081c10407480804d4041001c04c04404041060300d00301540005900041d107101051003006454082d542c014841e15020441e100780d0101901102c40300070950b070380c0810f00780c401b00c91401c255030000090155648000c01c5404c0d614500c80076264011112600000c07000000103802c091800182d41c01441c40880d155512504202d4051104000c5480c4000c10608224031030b07071045150f180940302d00e1155140451906015400910303110f0080c01e032035007005542c070440c16116800400a0040e801d0400c002c0f4486400390003042c1c04499840050f500140885008401e050300014502c01d064880c1c13223121421f42d101c0c0d42101e8490031810009001514145880241d425990704840c2c0210b40000429030001c01840c0c4800d4250f03901d01410f0075040c440c0c6005040c005a0b204d45588044282030051401d491802c00404d214018017 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 850448462 1250 850447212 850447217
    0xb0c1c142208030a05090f06041a0309120c03090315060112020d0905010203040807151503061d011d0105010b030f160905060a050304020306090a0c140d0c06050702090c03010e010303 80
    0x1c461298640c0e4241e800001842c0c00c00980e42e6411019800030601e90100089038000c9890000d40c480d2400c2c034400301ca04544c42c46051303112006c03912003c0d20050f0b1010f40201c00601c24100003461305182a4020010903500d800155555410581030504180704c240340f0400000c84c400400c00640d8100300c1c200c11108400c00010380d00c44602e811f540050110720401740042d840401040104580800100201400750101e52200d075007034810103046d5421441142141900b040c004c000044481c0c1082e00250b0042c50110001c214200442c0d0131160507802160240c2e0726444035500c90002841640d0240043c0b00a4519511b0200c920848585003c1d00540300814002881c440592146406002910005000075511070000500900c1e6800030f0780c0580c481e004041c00701c0c1d400003001408040d040d5001100d60501882c20a040b4210200305040c44d030410b000e0413451000982d0b020443e406800c41c0c0c0c96580d22942580184090840002d1800c000c8200400c01072000c504032042c4141100e9152 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 850449712 1250 850448462 850448497
    0x2903070f0b0f07120e09090102130303050d140906010501030c1e180b04030804050a06020d0e120a050610090c0c03020c091504050f0612010b060910090b0c1c14 70
    0x110801600c42c0300d00c007030181415013a01c80101e141a40420b141c20046030464203070850f62a244003180c204d2181050800440d03020150400000340200c004e000c44141c110000101c0e410000c06070805040c003100d01d0055030b001000103000759030300740c07040c641c00140301d241c000600058031000d8602844101d40c09014810150741901c0360554040000002e08004d241142d00c0300c0d40d074582140340390443d000e020300c00e20078524045a9544000f80560090350170b96681e81e40402e00a003444022011242c0c4036030507002e40740c09a4042003082060b503000746100c1400030759a51030000c02c2001c03200e078046040d04201c81784200d800400e6001030b84452013034044948000d01c0c0c132010040b240c400141c0030905c0d0040e003440108068036001605291107680c0a4998040c40710180d000d06080b11207000c0701a50021040c0106c900324203290100d50400300041c207181e501ca0381c6546043c0f21039040b4109004003540404801c04080c4d500c00741001c13490300203050032018080f40022102c00b40c042d02d245c940c20729104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 850450962 1250 850449712 850449727
    0x9030604020f040e16060f0e030a1401020f0c15010519180b09070f08090c2107053307020901091a100c050601050a050616080d2903070f0b 61
    0x140e6001c4403c4c940381104640040c0704c80d0782e034540307503c00e54890540440c0040c5031041806002e890001c50884d0000c000c0e108001490b95094110202404501000e645c24040045040c001100400c0054550741c0286415000c1071810441c0c08016000b0032b0054555403103e81d044194414503405807001c010490b6080c0103400200300c0200491b000c0d50b50f01181c0b00082c401c8842d0070400b070017644092a600c0c1c0c00030b991007a000650b610440300300c185e00030700710300002103215102c0f00c40018991001000e45884030b0740e90b80001d60300c4551070040906003d601c14051400e00c0e1040701c1012035240324148034100402a0000b034106e030814440e00c029244c40c0c2c1040b400541d03d50082030451540200241d0391a003410380300030180440f1410032169031007120004540d40ca028485102203950040086140504c050288100181c110004651403002404994016100c90143c29281090139100901d40464003121034418882601c03164000d4000d40f17018003129413604441010780e0403000340c86603107800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 850452212 1250 850450962 850450969
    0xc0909010b03011d0d030c14220618060c0503030a050a0b0d050607020c010e0f060703090b16060513051b030a06020f120c160f060b04050406061502010209030604020f 73
    0x40a041c960ba0552070304038030304072040a460b4000402c07460b020855018000220054044550010149010402c4440102c202e1503021005260401e602040c00102000055010101607500e420680c04110400340c420b804c4900070035048014000c921f00906e004649855054132031202820314903080b40c5440024941c02c056130080e200a400280a018001c42c15080564440d1015a0781c4001130103115198919980f1640c0d1000308c0d213900401100c12a86004208030b01e41c2d01c840811401e001c0400343c0041c805459401801c0f00707409204444549100c5890098100d400c001c2c40585000322000c2e8200215000080808041d0544010104241c0e581e100192601c1c007254001000c0c9400010302400c52041c002c0035000900a00c01c4140d9070751241075001e0000c6c06400e07800c40f440000141c80c2c42c0482d840c0101000e000e030154900207070045404010506942d811201521096291750b030402401081580280b103503000c52000f18200041100040e80350600500068410a40500620200e54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 850453462 1250 850452212 850452221
    0x32b080c0405101701060f050d0e1e0d0f0804031b02040204180e06010b0405030d0509040f02040608070e010809070302091b271f032003100906080f0c090901 69
    0x2c070040c0074424035000900001c1628490440400012030391500019102d80a0608924441a680c8845003000804811040101001003100c0c00d144a030705a40001c402a6071488180300e601e42d405020164805680500030302e00040910041043d40803c01010030340c0f000c10645620f48210700c60280076445d00005000c0e0041e40c0082c440b104880007000000781c201d500030b0b5044400310003910301da0780c2c0e514007103003c0740218400d070794258020068040c07060707208c1c0009100080c0c00034400603109903c05074400403078100e904201d0100e0f03001001d10040d990041b80000c0e2020091030038030041e1500000701900d481c0c072880001c0c06195550089480b200310a000b500c04240e04076281a100e11034032203080c4074004202d80c91601e80c800a030f04034000741026460301d240905007059100d0030145c5a5822070080c14006094500d4851141d20881c003003c0180055000e0304c1314030b208410341c034200128001160107940c0300780c0c02540b0444520031310b58804658148446021038600303c140d51072803178050141 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 850454712 1250 850453462 850453469
    0xe040623060f010207091d0c062a010e0d03020a0e0415090c0201021204050a0b0115020c0f030309040903050a20072603070f030f050901020a0803071814032b080c04 72
    0x43d42441c1c0300c55054510401108a001f07840340c1242c01440741c031010f101c1184104003400740b007181c41480d460031707640e8111910410196103d000003988011030303010b203050100d000140400030f0780010b0700102c220783c0807450411058040b07a04000d5200e18070b1b86409440f1451045161503600c0301c031000e120134000e50640d10780d0347c8401d12680c82860946000ea80b1102c446030100c0e141031002c000411110030040541c0450055030b0002c0542c101e403e020403c4980801c000103074517200411403070b2800d44984c0582030486102c1c0d00c0306a204d40e00007030041c00007220b491006400c0c4619403084d0800000002e01750045401038035144004a224010050113401c0b044856102c5200001c0c01701e080010f0180040f804134040d42c0d8419024515030300440e95489489002401a8030011051001c10134840003982c00078050f040c40300c901c0701c1517444003511448a5102c100510303052102c00e10141820b01116070717420b2829080203818411000218580034182c0880310030080c0c00400900f40045200440303015 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 850455962 1250 850454712 850454729
    0x70c03140c120a030608060c1606110a080603010608150103060203100b070b0105103e0d0801080c0a030312150506071506051909091a010e040623060f010207 69
    0xa002008000d80816404891043c00007480c0900010f40501c010030818024110644203e01d0000d40b210301c1d0001181c048410b4407415501c00903009513594800040c0151a070035200d0210f03e280c540101403c40b98180d100315025003101402c40004503110b0041c5066076805071b00142c9039294410020500245504500501c1800107484011b00c070644040b941290012100d6071030000c0031420450b00f10103800382440642e41900b004038500b00c41152806002c008000c54082c03003d82c800869882e000c8040f400c200130510a0006012082d41405410403103201610038150252540d030340242000d2104c20340081c0665941e03500340002c0c116a105000901c00140314544440c40342c208040703d008041402c0420502c0c0c10030004a5003443d040c44000c045420039000c41d0f0500c0e2050b0341d0084d0141843c11100c004241200300035038201d940c0418080c2000c1015921285443c0c41c01d4000ca442d10403c0007a40c8090b607900700c03022807242420560001090720948034980703c5100507031405aa68200454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 850457212 1250 850455962 850455973
    0x50a0b090709060503010c17151306090e010e0c09130c061713020f060d1401060f110f0604080c0307210e180a0b120303040305130e070c03140c 63
    0x30844000200704003902c5080104000d010b80c1c680c1054200d81205d02010b0101e00c4100d0040d0580385114640e65002c600c00300d0450001700c01500040200102c4da501007091981c1380401c0c0403200b100c0c410b0801b620a103400800404643e6043c2036070704c5032510800352140511342d0015144611b20f03828010055805205100d46030b46444003c0c0484601410142c0c1c0104603000094101034184a4030b48404e030003400305550f2406c481c05100e030545c44400405159515030942024005040440034002c10407595512558100d40e5401440200001440e200c20f602841400d40c4a080105a640d0010340c0024030550300ca1030701030343e1800c60040a001500c9410910581c40456000c2c070064282c1c42e90540da8203111001d4035080104d5070041d0018405205079520006654184c0c036401011440c200038658212100500842c5145034400c03603044000070340109500c090b00f600350b20040c002c0e20700c1a04c03162151174038001c0280041c072442d101900b00020f8600c8050500324082c06c0f916941a008152613 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 850458462 1250 850457212 850457221
    0xa1a070519121b031409120601031e0b0a1806020a0c0512040e01150203120103200d030e0d080c1501080f0613080f09092d070e0607050a0b 61
    0x41c01c8150300c1c0a64164451a020003040c52245100c003400c41e03031031582410983d69a413400c4a04980d55540b50302d42d074508009800242e5500c0ca078011200346201e0090550b513041d440c011400c0340340486200e110104460b49800044c441070b000d10ba210060340b20001c0d01280040034a0a0b285071100054141072000500c00c1016030711183c80d1105501502c100c0340c5102c1b1010b140c524900c101d2203081041d03686407006004020104244805014003071040b039091400c422403d09110f18281c0c1308440352099010800d06102407206500d4092500310307281c081110003520060010a64901c000d813240c02c0400c0e4110810095409032018540c03148103c500b500d13080c0c421010004428001c481c528800c0d031440100c014030000f1100d02c14034440e14014401c60407551100f01c10f800c400000c00440c2800d1100c510140c6031080b00360310404d0303105040071800003803072070001c981c030010681500040c0004c0200540c0c203821052180c0f0a00098501c02d5903903045081c1030b424241d13121070080003500c1201c10710 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 850459712 1250 850458462 850458493
    0x209120102180f0a03030806031203180601060f0c0803071103030c0703080a09050a1212050a0606030c08040c06051606020a02030309070603050601140a020c03010e0325020a1a0705 79
    0x1003242051040301c4090310b0650b0020032504040316a00c80e079000a0042050000130b2040c114541c000c032000d070440b03a01031021202e4002e01d4004844c0074406860b400c1c14a8192a01000020700405407410284224031188400038804101034030040c01440c0000081070301c5e14840c0c61802c4108800d039007900d441c1c1c208149103400e20752213000305400186080c0086440c40c8090300c00e0395007040d4008001e04001401307581d0403040280c0b00c9440320520101a000d007540d814a4043d840c07003a0000180001c40c00e0510030094103e8042c0d9000508025440d001c01000802590100e070580d105824078a44a0740c0b5915103250743c4125010050960340003099140400350004061801082d440d0151415141c542404030101c5600310b644c540012001c0301c100d100a041d41004116030013980c4141d891040408000c242951079041282040d07510001d40049400050303c0608005031000c062010070302a2900051910f508500440683d4408035414401c95501441140d4040f50702405442d00c007114400c40c07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 850460962 1250 850459712 850459717
    0x1003230f100e1e1b270415050708060123131412151012031e1404050f030c1306030501060f0b03181204080f0c0d030c0b07030209120102 60
    0x702100c0c0318605a0350340000e058800c0f440d24060300d00090950381c004118113060101480705103500000c0350a5000b80d0003181304008001480c041508000e40d040519184594200402464800c1031030030b42400700a0360b0202c00350703030044800d103011000c581c82c900703084507114049481010741400000d000f007074000440030108119161500041c0d4054420024041002010100c5145075007210701c0764900c0080420145400c1a41c451945800390348400340702c00010781a801c19070100ba0302c4418002e0b50b13115a012201c604100d41b44c081100c000c079800305102d900603070040611075107150710090220b450030807211440b050b00a00d002c0c4540b000c01e4594005080f28041541e16500b40305c00800d10b0031159030400c0480f0101034119145da40c500c0320002007502c142c0c081c0500ea001e03c20880d4003681c03810015001801e10708014040b168a124081d6141c400c1518036140600b04e01c00c62000403e8001000382c840302d400c4280d81d0f80076601c40000b10028481c4031a55070380040d401c9044040f40505501 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 850462212 1250 850460962 850460981
    0x4030606050f04020403021c0c1503140a0b0a0e06060712180806061309050703081902010e010b060403030807050f040f033309030e0d080703081003230f10 68
    0x1400303140c400008043c04203034802d502020307411452242e090701403500c40205c0108181d004400e013140e80c40d10340280a28915100780b15000181c0c07a54442580042c0e02019150040c40548081040d0201d6002240040d083c81c0305441410010400041140d00d414080f0f0740e409922612000f110400307850046d02001408511800d011448000890307000d074006070140c090040200304000d40014603401a020b0160900100c82e1030040c1040000000d04110140c40741103400c0012884090003418001d0840b4a0000b01e8100c45e81014030030704060325500704503001d40b9018074240710030f596210021b03503091065144003024030500180000d2000300808801c0150b91003a10680300007070440a80118a0b26032039400030b0100c4021100700c0110760302e43d20503804203100b400c0000c2d24100140c0002d2603d00b1000d010754602c400018403404042e4052034860703201c1501e0030200d95039800d5890f000d0820800400a504043c5680c1512108120401c2540715240359031088405c18036843d460000901a48072 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 850463462 1250 850462212 850462219
    0xe03190c0603020904180b09070602210a1101090302011a0a050d02100207150f0f081510030b090c070204060b160b150904050f1605060d0f02070215030f0106030209010c2301020403060605 82
    0x194041071091011400e00d904451500d00e40b203433903458140c1e840c503503031168221300b0a009680c0e1809814440c280551451280644c000142070307141c900b000c1091444134002c5900c05c161022007070041d65195540901999010748041080c12440d490680c903014090b00700046011804c0d6101c003040354001201d0f03c074044c6540d00c4145901148400395103c0d1810f803508050800d00710700c0d039031217410b041c03d4078900c1008901d8042101d01c41c48020601c9074000f42d8203a00660000140324065080501900c0c00610b417002116251030340c40301e41ea14012000d400001c0c8070000c0c041c04560418412040f0f1800043e00404143c0301d414285440c0c0e6840c0d11007004109a8001c2140740050410750101d2241100c0c070250100d2328020345242c0c064024003186002c0c4e0810f990920499016071a0084035405000603070030002d60301d0500f841803803109107059002c90300701401003000000c141d0340180e000c8030f50340d4001891410a18030750118032800c1c0034101c51440395803010800106001d595080002101c20031b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 850464712 1250 850463462 850463473
    0x6070c05150a0c0b0c19050408010e0303010e0c280509120c060706023a050c0301061205060d0506090703140a0308190902040603030e03190c0603020904180b09 70
    0x4500454803401036904203404141e00b124100b012440000804c0c3d40881080030480c0b5009101c003111515801581c038400014034042000c4c050280f0034810702a12041e010300541c00d6600d0001e03464513011008180b140365042c0481c4000b813010b13414110a0061180703002c4a00c0d8001c0102c1d0080880c2c1110354100d1160b49582c0070b41c2052900840c6071810b50501910311894205543c450b50060b5011025a02c140e500c000c80340d84d100100700c2190207101c0b155910403900d100c03003201100140c900260111814043c01c000402c949500001000a941c1120b24041215070310ba1000a10700ea43c0d40708081c0c068000c240c02c100d41c660700440e8a1090700e1040c0195030061aa10301034582e580080c0c040200892128404146032110b0000e044000b00744541c00420001441d07400301e425a441a88114089141d907121082c05180174003c02c0c0c070300d54042c0e1103061480c145454100c40f9119038403071001855400504040c00f0340701c641244012803840c03400f1444052044ca031021015004880d4820f0b14000c2d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 850465962 1250 850464712 850464739
    0x6180b0a050603060d08090d050a1a06090106030c231905030121240606031d0a0602090a051203090a080f030304110607050a0c0e01060e1f0e06070c05 66
    0x129006031507010300094299660002841a40f50a1010a4886000910013011a50b0780e4409a070409841034001d070090481d10b103442c03850a52208032210104205508203c9142c070307400c1c100390445690745401301d20f008603c1015031b103201c2403040d00c20306a000b644550640c200c0030801040410003000321a020000842c408841e40c1c0403e0040012008108086560300d604448d9a038140700d0180d11071100307004003525603591450300302c0e07441c01000e81c848004002050309489001c500710421480c02c1c51408003010ba968032546144801484260b000c118519561a503ca13324090030010f03016441031a40c0100140c0d40f5042070301c41c54030403a840d0720f011520320f0000c200249803c400307030001c5045455a50790744130600c05659216130000002d1140d80041403082001e0020350740500c001c05c088600b0300307140b0f81c80a80160402c4050001c0c42819500036221545040c1d0000d00f480710080002c041c103501102e01c641d40400c02c50b8030490206144043c80042403c440c1200c02c21180d210b8070080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 850467212 1250 850465962 850465969
    0xc0f08041d0106120e0309040e07080f0105060f100f03150807030f02100314010b0f120408030708072f0c1f0206011a0f09040f020307020115080102070b010b1c06180b 73
    0x20407945c0a52180c0050000700e00d203082a0b0488413080c50502c00362021180c03210b079110b01e02810041c051010340c2d101d6050045a06200f16101ca441c0d0082e1000300c2c2904000d9005001c0002c0c0c10840d000302740d59014042d5040d01902004d101400f042802e50350b0407662400e0801c80c0c9400038000364030400441c0000d12540d8020300c10b0358810302c0c207207111600e142e10b071081c00c9050fa042148940031001081140b00c4c0b1103065442420700c15846017951703603240e0905000c010881d20005210b0814080702c4a80d09004540c0c01004624090302e09900051114911b417426040100211a00d80c10080112100002420000d1011102041a42142c689a076191400740640c2c0011410700c040304400c00414400110305030081c00442d0001c0c00c04036130501042c281310100d07802101e045006035525000c0303540c2c80c056003540400a0400100942c108889510340d10390900d41841100003002e000102c0141e841c2640c00500948503000d041004403d98030044c514072406900c003240d014515000b109032503840c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 850468462 1250 850467212 850467221
    0x1302091807150804022b061a0103110d0903090e04030305043302070501151e05060325140c0d08130302070b0a1701120302010507020d0c0f08041d010612 67
    0x80782507031040c520307813920740a01031072103901d240c0c02c0d020342604100e0114004034600340101103031140400103540c800840844992080c001011410141481c0f0380c0e5003a00505400c3c1c42001000c1c03640000c9140b9185010b44880426501c0741c200f54102200300424503415901491207140908031a8800950848110403079984a564100c0c0b04040a07600140003d020f0b8080d0000328400ea0000071710300901c0300300903e05641a80301022201200c00c0f4280952444001d040003010240c0700d4030b05508103000300f4100082c1401900074400f5090b290101098801d251317540307042d160905013540d580380e289580c0c0c3d12050120716200124038810302191480300110004c0d0340880e090740c007419010341400307403c003840d0b40300018140400c6807040800c108007405415450080031105d4905042000300d14020b403d5980007403e110554200c0382910300b105070000c0c0481106030344807040500f0b07824249040807460165400c5900e6444c00d04070a10022402e291a140c1a2601c1d5242c250080c01501401001c0c1c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 850469712 1250 850468462 850468499
    0x170a051306050906071116120c0509041101020106050114121e15103204051002011b08010e01061103070b070305101a0a08090c0d050706080f010501080f1302091807 72
    0x142042c41f003000300040d00e0a151030030f9441014500c1286079240001408a401500d0550359041084110406036070240b10301001041d0030709083d610721906800b001c0c0d01d4007402d10101e10900d48280040ca5400080564106161441c440c0c90002d00b000480c1c28100d042c0000f5140c0100b00b5102d4030341c000750145148035842500000c0c08844c6841402d41d008812200f1103070b002c50414140000325055586000d003040d0720040c1e5000064444504c0550300320135150390080410300402c2401400300c40d41e2464179905480040c00e054403a5401034004a15501c1004d001400c00412801070011207541900580d0040c140714000065041e1100180740708068600081b1805c29000c0004c0c04201e4041c0812903030101480c020f45110f075800d07201041c14003103910000c540c01d23045107100b48803071900310f810030b5005894120340c4490b83d0b0414001a041c40c5015003035400c079417141400100c24142109000807202d41c040c01000c1281410040120b01454800703503400580900440480e1005082141c070004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 850470962 1250 850469712 850469743
    0x60b0103090f0f11150d1a060714190807140f0303161701080c090703180308060d0f050c1c02090105270c09040c170a0513060509060711 60
    0x1c42800d9943c94100d00038803e0100c5166040c0c0211080e10f5403049280f0040400702c5040c165a901890111000c480d001704142000340c80b008442c040076241e010584030038581c41007403070040000c582019440c0903405131800880300040c0c00c4150400900da80500070710b80c4617203140d0745c8841400d4080b540b2000820743e86030417a841403001a400075003070203041c0030303032416814589040c080c84038404420320401d0708041e1003a88031041824840c182030b02e00310342c01000c600d403c00c101490040c0b103041540c000d00c1c010b03003005149804503220780c0d900460040307a00e900007200000c4503044e1400036240c0c000b4142d50362180c1e83c9007032152041c181c01450901c0e1564010100705580e07003002c0410007240c0c000c03002510403e008480305000807509031407450003514002909503c0740320800030402503504100503481003101454420984984140d10f81d600844103040c0881e130b41c0c0c1e840005000300c0c140d82070040c010608101c1405401c03040460141d0180c1e03020742c0c518607071402101409030349103020208070700b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 850472212 1250 850470962 850470983
    0x13171603180602030a0c060f0603020d050105040309150f03020a111509060105041a100203130303030e0712110d03050f07060504200d0305030c042318010602030d02090f040606080103060b010309 85
    0xe082e070784002c0d0540c20306540022a281c0303a4000c109653300b1900304450507075540c000d200078944c21114050081076502c5070035042900d046d0300180030481010944c814580c000c203040402c14019036540824041c00411230f0249072000d00c014071186c0b81940d0303916060050780b0000c5510304050049d0760303152110444020203445038206200c001030360341c0c082c1401c5003c03c0c01002c2c01240d441603900b00860082d40c0108a48100c456680c2c106061603011030500700d081c180b400c00103280310038180d40520007196a03450b1030070b16041c281d6040c4551900041142d1002030b01d04100405644410f01480c083d9100c40c0c0e1030500881c081c404514610385241d17124441c15200000030784510001c60384646007802007414999103022044414003200c8646810405050341281a400c00f5000c960ba8100150424409540b5004001c1d4485c80b403104003001182d0002031402aa031620034844c40703040d0025000704000350f03803220001c014500c01e020441e00e450270481443e10643c424017072010259000804c544 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 850473462 1250 850472212 850472237
    0x3120109050903120a02040b0f19030b1c0f06020318071721070b010b070b150f1309050601080a12030209030c010e0418150c0813171603180602030a 65
    0x1003407900001d0040c5c0001d80c00f0000482e01040c05000b409880d85100300d1142c075225140d0402c1d1441e50314840c04410540740401342c100030358850b400340c8191004070b540181020403904015403000e031004c2001d000d05000006011902e11540c600d080882e072a0070075a40c07141d072140c44121642d914490300030342c00c2d442401c3c180c1c003001c2d00e103041c08000e100180e502d43c40c24013945d441150022099100800469000c00d1080c1071018002a25a020521130903101002925800241c08506a0680c06005c1e10301d07003607454106500c9a120341c0e11584c003d0101c40b2550380d140030f040c1d51901e440c8411918103898940c0000b085009000380c03040d00200070060800c4a0300c01d0011265840009540d40d80186c8445405449410080c208075155010f800c03031305046450106198141ca40201800080040810411902c42c401c8250181407a9120003500c6035181010308024081c003d44c3d008370300304100300030310f1410541c011160f140e0455054403603818259807070300280c3c0c49020380010341020410030013011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 850474712 1250 850473462 850473487
    0x303042006040306060801050403081503060c161e052b080712091101081602070302060c0a1e021528030219030605040e0f030a0c05071703120109050903 67
    0x484404101074011402c1c03d80c1c984070304090310a181e0004071565501c4044c041032590200c00c00340e01c0002e19480c0c000141c4000d011a50b64040200003502421021542407d42d002c10b001103103885421588840d480d036000300100044421103003080306c5920803d00c0781a81c0e940000c0321140100c5802d41101014a81000f040d60343c4100100000100300d03400180441d004810302c07910000601425075020321202140c0007602c2c07018041c1c43c5501040d82c40c003401c0c0181307600090180c1a2641540c000d92143e1607446400e03e002030640008004100041c0740b10f409010f0344862000740d90084a02141071810306003d040c00d40300b42207a02c40c40c5002d0341c540d02400f2040d1700d400502c08015180c01860500b042090342101032094903004c00003900c1d9030b000c0005290600442c2a0913a80a0161081d0000a400d43c0c0da284985040300c0c0900c06140c103440240003050140d02c000300203160f1218606031a8106094880d4042005031008010b020f00100f1030381100d00c2502d21a03551203000310328003403962000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 850475962 1250 850474712 850474763
    0x1214011d03040e04020a0f060e01091a0d02070c08150f0c03070f0503060d05120403031101180314040504090b0402030f06100b0f09060a0c0515060d080a050c0d050405030708030304 79
    0x40e60080c11b90880041e00340c041800d03110040c019661364051490b55000010820a8181e001445903018140100030020380801140c1b442c220901005070b40303140034680354410790016803250089000c1e02c0c060240d0b10564200e0b00c2e10400c2404102c440513681d03201004071501040d559040003038180510b507100380f4020700040d03400c03440c01002c441206c0516503071540b414403450100710044070003190400c10550040e03010039004400200030b101c0c1e801d041d0004010183e0304000541000010a0814150700406040b24090080a0010f0201c80054184118145410354049000e84110040000c4690f004140d50b4000c00c0c3c20b25510710040d14106982c1026007000240510b5080c0802485500703603a104010030b54003140e40c48940750321945003402400d0404541000f85a00f00c10400c02089030b0b1242c0301104000c0d030001c00702d5150b03101c203a400c43e4a03014400348118144a092448910b240d00b10700039100301d03003080f82220049500c0e0b0030072a4a81c041620020700c6200c03a0303030111348001c0159a2 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 850477212 1250 850475962 850475971
    0x120305070f061d070503030f03150a030803090129031005100503070e0117071505130504020310140d020102120d0e03031305010b04020301050609010c0203071214011d03040e 76
    0x146825401ca2a15074004503002e50f40c0341c4034015a0340303241e0820240c0912041c0c00a2500706c0256003840e980c080846568032005201040f04880250042c0c0e50343d071480e50307800217107410041d440d880c1d20301900706500800e0600f0152501c80100590b1802c903028100c0e60850300381c00036001d442c58490004042c005840f003d4820305111030030020100d0307252000c0000c80e004042d1070f80c542441d545011050b440951500701150080c0d000003409201c640511044621403c1d52450400d0b92000e4803114034030b002041d5000140d105000000b8000d104804030042c80c10350702c120b0300d507480551031a410080701d640030303040c0203001d0b0b004040c4400b4007081d150003078000c80307400700008110406840940c600b580d00c100e51100c0c031180207440a0301804402d20400380c1146003950214a15410240010901e004500d080c1c0d040040d000c40b400110b4a0a00050700100706a10000149104030320b40303500c01c1c0104691020b00d03586014001c0341c1c107100c403060300606440036102441c070302400c16440c910020b40081 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 850478462 1250 850477212 850477223
    0x10b040605191b08031b130627080a03020d0302090112091110050d0c030c0806040c120c02010903080a05010b120c160803041e051b041b020309031612030507 69
    0x70400070090712402c8480850b10440890b6624508620b803c406c0401051444118402c280410790032a552214079005541090038261140980c86004c846051080744440996100c142e41c002103d90300021042c0c0d1051194095a21022400000320228040d207180203000841c00d00e00000c0540742035002800c0f503802602174108a02091010134216510407641c4800604006900c08060995214010030810a450f041c070504014400c001c202e01d00c09054580b240d0340d1a14101500c030300941c00101040f142240900c014040b41001170300074444804181c011514410000702c950303035584520740c142d60030b49901d9401c002180c520119603c8004201c0c0d0707203a070010020301200000303851032560220702c00d0782d00c56505d14040c642441c104204529601194242d42215000100c0104100c4e40e0b4501146030064804c6e00d0500150144c10403105492006180d64419502d40c1e0380800200341071203094040304c482c201c035824080f05240b07041c4140160021345506541c00644210018810f050091 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 850479712 1250 850478462 850478477
    0x18010207120b18010b03100222030305040501030e06221a010f05040605030c030c10090b27090c070609080f0313030305010b1206091308031509010b04060519 69
    0x20302141c0084015900e0039200d0440c03032001c0240c441c0d0f420405007030052400c0000d1210b6900580031985d030300c0c0d00c42402d25402d900403a5288101c0c01d052019100001e41d040454511580c03400c0241440d8002d00505001a0602c48403800b0720a002400d140102c581c074161b143e6146191a04080d90340140401319495107100b500d40300d072041580c00301c9020b01110b2000c1c0320000e140c00c00700b000329104c1d0760019000350044610319442c1d07940131440000012003a11003a04001080d00100d0701d441d200c0d00700d00c1b0140c00200b04000303046c100802c41120240d0303400c0c0300006000000200144100110b0b80c0006000c401c2101a00241c5a5004500540c0c4134503501428810fa44400e0f00346600201c842070703040c0090106610500d03516000303e0b40100002400d45e458404e4900c218000c80100400c841d00885101020802000c416115250300c95044071000c0d0701c5c0c0c14800d103041c4045090381e82452154080074000310300c940340c83c4100c600b154820b480305440d0031070700e41313090191080a42030364082c403200 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 850480962 1250 850479712 850479719
    0x42904080304061206090501080a0201270e0f07030605060f0d0b060a2718150b28050a080f060307170106050405010b040f030f060e0d09030b060405070518010207 71
    0x10400b9202902c040d4403505450070340700031814100c4406034000c030306242c01c05004202d05100880e0044080b50203203080c15000303200100c0c180d182400406140003401415500280010310b481c000c40c050103115441c983d003a00d450300c04609540c440c0c010355512040c1005100740d11451407004180ea00d030114008900c182d142c400045281e00302100d1034002c96210300c1e441440b10782c40e90450b2503060355880c1d560b660a0404c801e00c83c4040300000d000100903540c528081503a0064280c0000409a903181c583d0b80c0c514080f8400c84c50940c6869541d01031354219031065189000d402610380042441c2c0e5080181d40d12400101511038001e0420780c2c040c082c122021506526503100c1039041c90103c030001c24610714020900045400590004172220000d00003801511007a582e900c0490380c00c0510b41502c400b080c10484001e00b8600007a01d40c91040000400c51190000319031340407a80100d041c2407440d82d498040c0300607508110303107810006508004498034040c2c80020144092011320403100781d55103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 850482212 1250 850480962 850480979
    0x150309100606360b07020a0b13170304150f0c05151b04030f0605280b130e0604020415031b14030f030315011b03030506090705042904 59
    0x4041d0403910000b01030709070807082042034001d00480c41d000c0c000c0c0c6144290000b03a5594104090340240d030300c0340310300081709015960303541c4400d4003408640403102c1c0d40d01844400c21998241a11510801400000f40d40e0303000000401640d00304c0740100031440740920511012222084000e01d004107000c1d1240c02000031403000c009201c1380701c41e4841d0403440780c01c11104c01400c1902401d0200d003100c1701044180001114404030010340d80e4442c0340442c2e642c46444112000903007000c400c02441200c82c0104034041c201d0340010150b090140ca5202007030408903240c00a03540c4400e003a01156011002090050805134001128000503280701440281c803a5280d4244031041c9a440d04c041c401005c0c03c0c002c1845001507651076010850050842403482e0000c03540346d010080c0340780ca405895011a0091785d004400c6103051614282c031261902c5560328000e00202070581d9140d0040b110680080d178a00d02034002c0381c0942c4c000400030341c48401491380c0d11147d0402c0d030764449030041041c40001030415 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 850483462 1250 850482212 850482221
    0x507060c0c08030d0e10381002070614040302220609110403050d08060109060e0402160303140c03090c040513020301151e03031b02220207030e0f15030910 68
    0x8401100420039040c0c2070000313450411100f1b101c440e414a00b0030707141d804065103d10b0610040041c0144060450000144034480c0301450b071460b008000c000108080715030210b06402580c42ca6100c40140d11406007100d0224012400000d40000c2e92980400d001c009501c041254404091070106006468181c1030b400d55200c16101e5501c03c0c40468180104803040c40000c3c4c20200510300609a40361100008240c403a8621030780052001c0d030006110f1036281c2d50120346580c014595011628011841c4c000d0080c03103070286083e04e4020b05030100f01d214840340110390160006100500a02449000304001030070058402300c021021070070070a005803002e01411140f284c641c0b129108452030043c1c030307075040d410700d2150414004d81e900c01400001c3c1c118400060274080c8074801200c0c5801440861001c4005800780c110030150140d40111071403041e0000c00c200c51007607035003004a80f0460144840310340c3e42d1501c0b83d4061120040b19031200c0c0ea040145034441f10080442c1d41040300e58030b002003201c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 850484712 1250 850483462 850483477
    0xd08060a05120f1e190f0b090111120708070c11060c0a140105042001080a0903110f0303090d0c050316080f040e0f07080609040b0c0705010608010b01090605070507060c0c0803 77
    0x10b003209540f5031300f542410711510940d03104540745450384400f1591401c90966400400a200c0c051001c04a2004d00e0254410445080d0210200e5a1004c5600c2c41c4003d04100301c550b14005000d642c001480e07648102c280340b4003154801c010400024142c1c0410000c0d40003d00540c06600c2202600000b0031034103030f00e5076980d910640000402e42440d04000d80c260050001025002600c80d0751041580d9000c0740c00c0e0352204060000203410042131a0458800c8140b07800e0500f544191100264660008001140200651011645400708600c0e082e1464203140340c0103441904103129250000c1e000c031782194445803181c0304961511f5100c076508021030f0002d800440351482610208024103443c07144050304a40c8a09281c0310b6443c102c2c0c0058045140200000c203c5165880403455440c4000c041d1008507500100900c242c070307100c6200fa8003c00a040d201400100104000600c0318019004c41c1c019940140240c40c0302801c060b0252122a400700c0111240302d642d03140051400c80510142211 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 850485962 1250 850484712 850484743
    0x2040f1404080d050708040317060d080c01061410080414010e0708100c03110702011d18061003050c0a030b0d0b01092a020304031707050106030b01080d08060a05120f 73
    0x39a006003e4503022194010110320034800908240310200360400741d060020b048420322551681d441d44041288140301c81d600500c0010041360241002c034044d00710f4000c0c2d900c5040c000c280d8284941c00c008140c440f024407480890f001e440030170041190703440301c000c41030a04000820204544145079241008650090b5040d8014101100c129140c500520082404a18040c0300703464684081c1c822038800c1510003418401c4c4491401c0000c0611400080f868038010181e040e00408006191007072101114054801c0780381541ca290228000d1080318003500880e82d810741450740d2418151300600210308501d501c102c462000b0b00000d010020b00c180607001c000740100701035046442d946450000080301c5880140248600296654004141c0e800c5a070080781c1011f100340b40391295046441480d502400301e5081103401300c1880040347d410f9040310024011510584140314040307584030302c19640254001d0035003c0400c03083c5130029441d143c03c032180d0f0564208020001d980c91805a880208500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 850487212 1250 850485962 850485967
    0x5031b041e0b1c0207110405090304180908070f030504050303180907020c060d0b0f040e07050112060e370b01020d03050408121e010e04020a080f070302040f140408 72
    0x40010300007001c1d0050038140b08282c18161100b0b0110a20104860041001607000c1894401d00c4000d810b4214002000b0f08100300da400c00d1142c0c9501d039031050084102401d00760640c41c200c08210301c5190031158000005138280840d95441c440854038008054081100512020525030f50910040c0385510000280c61682150b1001b40a0080310062801c015500700619444c881e8998404444c020201404006400301c0d00c4070002c3c01000c88080704c3c0d9042460014032075410000025000300b940c10036290b40f10401c041d0240002652200e0003a0011a00d0440c0070138000c070b16440e04484901c4020100b0031060282c03040841c1440c0c000c40d500d0f4001629400950003550701403004502a0106140901c1140f17402e1700e520041c1d00c1062003411801c40003600088982c0300c40740c1d0440d10703178412035103540c01540e461000d0b50b00c980741904c0c264400c002203000015804000244070048a6009004d08215840c503000c1000510340060769510031a2901100c0c41c1508400da04207229500c951400b68 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 850488462 1250 850487212 850487249
    0xc0c080a05190e090a0c0306120f020a1a07080a12090605103609120216090902220204120c08010c1110022104031706030c0d0305031b04 60
    0x5204140d10030b0008244681c070000040a915040c01150b40490322540210b0100140340003100200296400b59024101851100d01046041d684040c40356000f100e00710081500d48944102200c2c00804061074110100f0284c00080c9005010f86403001440c100f034004094007a4840d425030300103010444406980b0010030003070540a1900314080d01d4142e01c1c0603803100d903280e00242d0003e485d45068804c481200c4065050082c0b640280e811035074802300c0f44da860084800c02954030242050040d0307282c00700b00408034a48182d40b107100c4c0240d400a0461085503000b04003941200c0d001c0f04001e4429400700804501a4040520082d4581c42420502a15460400714508546a80903241e040002d140b20380f40d05640b000801d011107001da131100503610617407072140105400d100c0214100c000000300411061503000381c0b8103009210000031404150352114101500c0b80c0b554600c0a500262034001c0b840400d01c240051a80000c003001001c84501c4a01d52605094129074883c1c1c0746601c42001c1803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 850489712 1250 850488462 850488487
    0x309030e1e040509030f1b0f07030804080c0303121603090c1206050f0622090606090608010b090403020615061b1c03050408040303030f020d1e0e03040e0402040c0c080a05 75
    0xc1c1e1322455401c045c6040c85002d13440007440c1d101b600d4031040341c607500152001c164041403280d0411070a90f6000c9130600c1d0364a1505904e035402c60b10500c03240e806070010700001da0801004071103401c4d00c0c0c8003206003a40c0d04c09402066400e808018481055691600200010800d5500c0809051503064507400031b407881c9007581c1030700c4004203459a024007c8003400241d841c0d041c41c100312071002280790110704c0707407070300c0107900a002e42c040181c030503410280002116402031b8415000d0392000300c028070004050310144080340c5016200103006a20601c00203e0301d0021145614085900070031030744c07404c1175a0743c03269070503101280042c0c07198001e0b070b070042c5d0b02071741c41c41d0314400344085402c09015610700b40e2103050044c051440081e050503291244021200384560455000d041c100500b001240544000b40807200c540b50006041740c0d1800304480e411440001c00d4404481aa4400079103c0e600d036402c2c0320150110401401c180300340886007100141040b0040c06030710300701e5620311392641442400d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850490962 1250 850489712 850489721
    0x1801050406091802060304021c0f0b0703022a032217070e07080a09291e0402120c2106070f0f0c0c0f030c030b06030c100309030e1e04 59
    0x3103440d00380750421808043c00405100c008294045400c15141d50301d60022501a440140401d203a070030b221039010b01008400c0d05a0700c602e6000d0000c9164690f00d86030198220300ca0707442660308521000400d100c1d1101000c0d20302600280e40303821f813410700c084265007100400d504030100d000c0406c40b00090210370b4140c08480340809540d4000d207411403810291a400e28409001c0b60104510103000a00c40200e0380c0000022aa1100400f2240303a0f044144d4184441761a041d40c84151044002c02e40350340d02103540360b0b15640001e078005401e450340c2d401c008000c080c510303800d11a80203130012820f25654801c001c5000100c9200300d2444021210300042c2004401000d85040c000203120074030542d503001d010203114200070300b080d0000306828109010000d03a20b0f4410b031801081d010010003044014070645080706e20a502d22921900c54400b056218001a220603400c10700c20700d05082041d129801580943d400380c02c054015450440100d40050440682c18520f0f0022150143ca00c0c20f05205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 850492212 1250 850490962 850490969
    0x80f011512030509150a0201021c06061407020d060c02071404050c030609040212120d0f0b010e0607321606230c010c0305040201020f0303091e010b1801050406 70
    0x990520103003405010301c440200303448080d04100011803031000644440704901210780500ba03030580c80e04800070009004c4c0d03000c544113241c3e203c2800e01d0138800c00c01038040c0c18182c440c103860720541c80c0000300300904d0640200c0d0003a0703404000800600d0100b1107610903840603100e036601a0a1490801c1c501581da0800f800b001c0d4002c502e40700800426459038008d507600175208031200d80c16501c8500014107500d00360702c0c80c18002d0042a041c42c4401c040000180181442c00340144090000c604030380c400c032060345100d00d01090302e400b042d803800d01d4024000c080d0144607115844050f001c010340c2cac02c0500c050060610903c030040314849070600702001000c4c2000001d0031054400350a00d0b900030b1940740c0301c0c0322503c80003003450010480c0140d00010754900171107000003004544400f010085c09418140c41c00d07400340c018503100c040e08503404400c80340b2811401c8010101924641c0007005031781610804407403c3d56842c035800c1d003036a0b00c0c4030329141d8615514545022950401c0d0800049039016813 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 850493462 1250 850492212 850492241
    0x1090c06110705010c031e050315030601050607032106080a0605011509140303120a0212010b071a18030a0309060c051e0703020a1b03110114160516080f01 68
    0x1c04000d4420009a250b003500c00c2072800b00c40b000c400d460b094828000804050300e00104190840c140305610a005d940300304107541c0c500e0200d0044109258442c04280903182d0011320812140c0c010a004800c3c08000f00c1e0352400c905c2d406100c0c1c1c400c0c0c03800c071212508a03a407580c00019010041c04130a0003090f002d46401d0000801400d0f60f0390026110650707034802c802c041a2658944120380d50140291981d1020b5103508001524241c010000290302503e855090030700441c00100d040e0b201e50003950340035603005c00c0d4580d00c02001350342e40840d450700170804c184900e0894059402420144042d0808002c00c1e280441e5000c8640b400400f500c00010383d25003048400d0004160740583c40600c440c2070706540d510079903200b50742d0038128200003000a000e048000d030900100e00003041d0b08080303030850b4081c5001ea4403107040c007001120101500401500500002d000c10501400f881880103041841790048410001c0d868401c01403980c03c650011850b07400c8814480b003d080203001c1c61101d42c201c2e1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 850494712 1250 850493462 850493477
    0x4120306050f100203130b040f06092303010f290f010e13060f080a110604050d29090d0201050603150f0705070828031419091401090c06 60
    0x40100340300ca02128242441140c43c4680294079600038011504009683c4880080042d2942200b2101e0351052040044070304014034001004e500c1562014251184001028510220211141115000f545099030b05550711581400c41c141c283c4140282c101c8452021150949480344400300c03900d8000c9001d0003004a04124945a81d01950111010008030b400d90049080c1c000c0d260003e0010380c10250300300ca41c411020900c0000040c0c810802c41c40740c0b18110703160211500f0300446005520502e9041480d006159000615011840d9542d11103031404106010b4407072000c001215041d10000402e400c51143c102a90f542809565801041a4010320243d01d402c1903c1950185c001e10002da1b2680e03000215042c1840b91045030b100755041643c003a211381c0a044007036482e04620f40400c00d02205010f00f5200f1901a00075500360850f242c902d4042c540d03400c0c26071400c482103180414483c96950a0380c40c0021810132611100c12881000068030381e4803440d148203c510b0580100043c04600d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 850495962 1250 850494712 850494719
    0x40e04030e092811090d0c09050108071802120105040e0f0a0303051f080a060903020f100f0513030903031d040f0e19081602010e04020a020f0705060a05040909020609060301060804120306 82
    0x440b01291200b20381601d4203861451b080c20840341c004090303001000b9860801000186c071010010381542621080c2c0d90742501d03c04d480d800039080b0b200300e00c1507035421612400104401e2070607a0203658070b05418001e50702701c400703140d0400e4100815051b0450119030781d00140721110b80c0740d10340e941c0030711640201c40341541c1c02c2a102d50381e02c0c245400024500d07a2038801181c1007600c2402801a4014a5011603605d008000e800342c0c0030304124002c0888103464000001c002c0ea40d5014550005038140e19a0440039080d03071012640c03811041c248400401c4080c0c14070009486900c100050340141c1d440004010420070150340c02d00081d9000078403000a4808200c001c40d007c1c1e0101c0305034403000c400c654101242c510040c2c904280c00903107503134001c1c070200346010b40c150041403044840140f1000e5900032030b203038000c01c07200c0e000710825800013480503c010720403038201e030380300d2401e5a000a00c501d08003170f04c00b000901f090340f09800500008000600b4041040035040b0b00b80f60100307107404c044c010b2506 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 850497212 1250 850495962 850495991
    0x151306082514030a11030102090a061106061c0f110a0609050f0d020622050402070f030e01050415030e0c030f0a110604050d030305130203070801090203071505040e04030e0928 77
    0x304131070160040d103084010350480c0d0b5095048840000c0060314020035940d035210050010020b50511040a019040000b040c41c40c0c07402d0180b10003000c410380c604124066071100c55101051440896200e8141d00b445549a5655500000180318a41e90300c480982480c1c144140c410710b00071898000e0460066020040ea11801500e41810101c448000381c01c41c1d54411903142055644025003147c4001905014441d4404041c4c182a01075111060900b50b04401140d1510480c890319640c6031051050030960380c826002802014004000c4902004c4070400180c01d1108218020851b9400200c914040100c0400c0b5126411421100142050702d0140821200059500020304050b41e480c00503160702c01c0d5605021045801400721040c81307031148441c030b00800c1c0350302c0242c0c42032003100380004e40c0100714540c50588419030b681d164202031030100707131800c0c00f100a00120700340003e0700707144081910385800f02d62180300500d40f440000081c003e18602e142042c0714040c0c0328541030482e0000f4015 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 850498462 1250 850497212 850497223
    0x70501020c0d0c1a2115040e0a05060c03190e03070f0206310911071707140d140c0c09220b0105041415130608251403 52
    0x10545052000c066907150036900fa1101d5040303042c900c104940e450600d51110005000f22001d02c4140080c614840b548040055604a800b4058001e101c5100d0001b8180345e080300200c01c99102c01c03540c2c81001030751810300b4080308490035100701e05c0200070041c06503810051020b45203900714007000000d4240c00d1b41e548910034118050205035603410303280115128401103c41c41e01123418034904400400580700d8117402143c03c3c0240303200082001040321a041c1c8101f03031110041c0c0c52001c0c5050748654421600001e07110300d07144454801d111000102e0806081c0203031410428010b03005850402c0d2014021000f101490030340b420341030080543c01040095031b040c07072040c212a040030030303910764802da1a800d412140c40145081001c1c81c0340200300070500c0e081c1c1611012a014020800c121185580d040b60032155070641c0e0990040c44515400c1440c1c03400f4100703010480c0800c00c90b071201000c91402c00076400700e20b014441c1e0005402c5c41c9903451541c03130150140c0c459204803101c04000090b50b44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 850499712 1250 850498462 850498483
    0x50106050909070b070c180e012301050d05070e0a060603150803072d03110709090c06030228110601090e07050613030b0705030a0e0a121121090a0807050102 69
    0x34800010000280f008004419005205a1fa080714041116078081805800060b0001540b50b081100481c810290207a5540b115442c90300a5460f903840c0c6010002006101501a52240140310020850303a5103882840d01c02c200c44640821160b15090009044903014071181820030354803001844449004000c94620a0300003401c00071109103810640346a107120300c140b03401609030000740c0081642181801483c0c0b2284010f070b0b0100c41c0d0380c0d045142039400ba010000c012012481040c80304900a0703000e043e900000001c0f0b05011120401c403070565002d101c15040201c0c249904c05101c40c1c00410606002d0314121006001001ca000a0740d41c2d6101d07c1c0c085c880c410040414000003404c2c45c106c900d401941c0040485050b030400400203002a170050785d802130404c0c101620324498000009070b900805a02c400054482c2404003c05c03182d007a1000c41c01c000e6401080308260588408c014200c0e11034490f420080e9445643e6405c00001a9a40c0c2c0200334981081e0002c00c610380e004038080c140c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 850500962 1250 850499712 850499729
    0x50c0c090c03040b040c1e080f0f330a060e1803031302012102250201090605090f1009050f03060112240507090f09090c1703071a0405010605090907 65
    0x91740b50740c50400001e42880c3c0081c6c2141047c40a4090500200c118030011a01d0744000c0c0e580314003403034407003d4a581d412540d40145600903050398508403c1c4005400c0441031310000c4e01c0c25500d6000310060f40343c900f03480c1660002d8460b2824000d0300c80391850550480e5620003031010128542100340c0d01c902008224020858100c24585c040da401607071401e0200c0032402c051105070720001c88410017500804031507501902d80f081d040145280140c0c12400080d0141c445039140b91521004075403982c0007160540e0000c50121a881c002e480e261520800c90210782c94280059050106208141d074403078101521940c00f480c01005120f1114411350350440d000b00d00c0e04800d082e50700c444144800c80d2030300c2c03084080c5040100803001d60301000c0c0105580e0f0307490901c12035550b00c031407207800d603140083d014000f150344940800c000b140640c21180c890003400250f074200300094807500c018001c500184070001d1001e904104c00c00900780700d00c0e400f42c142190324410505106411603505c03201402510329 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 850502212 1250 850500962 850500983
    0x27020901181e02070b0615030a05060a0302041b031109060d0c0203270a0905040803070c030e120610050301090506070c05071502030d0606020c0f01030b060f0a050c0c090c0304 77
    0x1c1600e100e42152114071a40d800b0080300d181e40d110000000d40c40300f501660443c2204c004070761b00d441c00d500180401001c80308524115100c821461004080180149510003915800013005072640d0081c40c032003000008000540541102c4050140c82415244030b20409041218014a68446d070035200f0b80304c4245400134036110303002001e9145200c0d04500a00c0003003c01071900450f008810f280c109680300b999401c400c07e54a03406503040e50070540d4001c2003940c044c8000b440c898422a08241d0507806850200b040ea06210003060b01f00380700050f9584150090380401070b0449110044500804058000300302481668030351030b851360300180a03402082034481d0211306000c2c0c04c10204003d0001202c00030803001e0766040180d56a4071500341001e1483c2820700000f162400850b6400800102401c82c40c0c40080c0740300110f008008504010f82c1c041000e10299040c0ca0503e40a0111440e460b11116900e8072200030ba01e143c200b2100040d8402c44004040081800341202078a8105d03a001000c0390 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 850503462 1250 850502212 850502249
    0x10204270204031b08010f0207030503070f0e130605010305180c060d060e100e1e06060a12050c070318050d030e120105041506060e03030f030705040806090127020901 73
    0xc040c0c0b0a541c40589448030760156204400d211070300810840b002d500c000c015402c821118041030340a20301001e00401d40c207200050328640105201030001c80940382c143e031034668a50008038280e42c424030400741540c1c1c841d003e0015503003503c01e0310780020b80503103209640c0d1902c03508960381d82035205150340a15004912080c201d035043d0860009043c0020042549160040e8040707180701061140481004118010031903840c2d042d81e486882c2c0f104c40b12072804564843c028004140c0c01010f950080041c1884d07210a030107058441c0380e00030310001440c16940c040c141001004183c9d904481004007400d03503010819a95841c8065803030583c103041142070385003001c00160075901d00c0d40c10551036508045c04c000401c91020610034400c492128204204c5444520481e1075032000f036103a5802d0f50041148035083d01c07680001c5d5034031500515003280f0b41038031034191504040c07058400b00c0990b0745a40034000b8001c0901460a04425031649081583c095900050307800181846a0301d403030f4029590700d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 850504712 1250 850503462 850503539
    0x60414030a050102070b1909020d1112010504050d0e0315010614090907030906110c07090504021f08010320030c010e0418031e09030317090c0a0b0c0f010204 69
    0x140d90075030020003c544500e11400e14405010003122218040140074001203c150810b01c2180c0d4055005070002c4051080c65607001124040c03e920668448180140c01c08549001d01903944104d00c140c005d010300c00301d80800034124011380f0083c68401d030040e1801c00100d080c14481c550444240b85041068644115150310760303840b400081030b40026041c4100180c407900b5800264110f8442c003020000520441203030750781d90060a0310b0508503000602d0410032000d03590001c58100e80020003070076a86100c0300388010210b003104d2178000400c10440041050003407804440c070120079004440d07480d40136913200082c0c40c0c16034140d10505102c400300c07034401e064687c2d03805808060310155421400c0103c0f428040c100090b2500c103460300606142105100ba803240c2e15080860381c3c90f84540403941c0c1085480e4545c1c600042081940e0312031514280f006075254071b4440e0007880c1898175180d40d007a6281d6542e090150507805002c190f0f0041004020005100502e10745120400c00000d002d01e2011800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 850505962 1250 850504712 850504723
    0x507030e0631090c0f21090b04140a1e03091509180b1521070815120d120f060b13120c0b0d0b090c0414010e06041403 52
    0x200140c003802c40050641d940e4201e80c40000402c401038000c60042d61000d840c01651840d9540d2000140170481c1c01c50164021100103180300d0a203940c0c603034030166107500902100c016080548036901d50b902400103200c6003d103203284180c0d000c0f000e030904845d036881e040750107907004c020001100644003441c000d052045100c2d10140044110506405200103c0101000004e000d603003000b0b40512100c0c1407160f03580c07042d55503001c00903210040062501003000425000214421400d180075403200c0e00c0001809581441201c2c25140c00d019130a244690138285038072b417450140901492070280300401700014280c44c4010300f034540a01c00444041c0200090140203104d5072410b0306140000c070710f1901074809040c0c40c01c0300d100240d01040d6900602244000486005407014600e90001d100030304a041c010000030035a05008a1242403201c00b05400c42011903420302220800f160520034041c2110030340b0440042481d2003407074820841c00094440c8520f2041000c0d010303910f203000c000c98a06000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 850507212 1250 850505962 850505977
    0x60c0307051903060f0e19020901110102040602070f0b12010e1911070228050d06060e040f0615080c040f14091b04050c0a0c0203010b12011b030c0507030e06 69
    0x410421020084000f401a01c16400b41c0c030328a07406902c0100e41d51045030119032003200c2400c0961680b070121503101c0000d40c07000b5841810040c109656a00e002000d00052000744130640c004c10b00039260502c10002d440d45a0410032024404001d800307080b15001c060141598030007482062180c440e10f0030603081013801c207048003c0382e04120340030031841c008030042e140c418020303943c0154030b41034865001204050800140c480c603001c0c0c5005d000c0c5d0706040805145042c8143c0c0d00268154489200d04230401c000c6030229000c1d02c036400000c0410196024400c0c1149003480c070b42002c04d0a0054098451005140c0310f4011581c1c0c21121038103101940000d41e210107001b1444500c1d0410302601074803912942c203803012101580c0c0e0b8444407400c0901c00d0520940050a44500703103480444200c8030b00203800000d0303916648581d03403c0036035036400084503940623040c0c00000305002c00001c4211a0140b04804070705140ca020030110340305070003100b25030260781d0500e07210b0444e101040005013280034091 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 850508462 1250 850507212 850507237
    0x50712030b0f12060108120304022b080d020711040203060a18090819030c090b0304080703031104171002030c0304020603040302030705030703080702010b0d0309060315050301020a080412050903060c030705 90
    0x3e46080c0710314400304060f8160350600060700d0003901c0403021610742d44026600250407031240c0269091020201c0c030003001010b03016000390a4140162a900c4094001d50101d61009900045640411140e401100c078014070a4905506519007a00010340e888074a10410709001c5d114214004c45500700d9100c141841d03841440c0e144c8440a0300300716440f000e0a000f001740824a00b02c000b22030240107030001301c100c030404d02400c0c0c44c665603955400c0c1e1a0300140b40840038181c03610607080c0f148040c80050005002040e40e40c4101ca880710b40854680390a10329a0b0350410320420510004051b12811a940250159600c654a4440b4074049156205004002d0603d01002c5100c5041507480780c001401050b45a0003844500d40c010200081c0500f030318001000b0891416040101c0360080c0c11650450a007100707480c55007030303840700030a081e41d0020079020300080c001c20400c000c021a0514014002d07820345010f80c00d00c0c0718000466900c44010341050841540440041d80051080003296005040d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 850509712 1250 850508462 850508479
    0xc06020f0c010b0a0e0105030309060a0c0b0f07030c0305100519080d030207020405060f0d0b130804120606060f0e0904080f070516060c050c19030b100501030507050712030b0f 77
    0x703035440e500804030700074403601c60b03004840001100084044680c0c143c81c401805503240250541c20404c080e8012141c1105214010035450045440c00b80c6c0c503849510a5540110f0900c0c000c40b00800f00c640e40c400c80380901d0325240a100341ca840035200c03401505c4043e900910719000038840c8450081507648184801d205170100c0595107689038001d07140d140c0c425a414400b41e1a0002000100d1031175081554000351403143c0900850310303901056820180107049040103044a0307c54070380907171103500803844098980c0e5000042003154410100145460329280503002c2001c0d90042881400f00026031140903101e0104042c4603042040b209805407150419503a01004e150080d06d64a5030440225074000d40d9000088441c055032401c03600641c008090903045004a04100405118038105040031000480100010348246000f5000d0030700060f00499080c070341000141038410090060003040402e0118200140c2090360418005803241000b0480d41400808102c4005450ac125039100c40380 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 850510962 1250 850509712 850509727
    0xf120703030e030d06140d050a170f0706020705070f05010c0b0712090f0c06050406090e180d0c051b0a03061a0a0909290c0c0a151d010507020309010c06020f 69
    0x42c0d03400081103c0d084410208485130a0702001221f15200700068800d8002c2007107100001d0085c0f00b0360007034902d28142035080841110b00f0018982104000310b0782d642d40010701c42d003401420031212000f80700e001045284581050002050400e040c80010004180e103004907060b14010601084c0409001004112180749802c00c40c00184110a059405484200c000305805101e4000c5900340d843c0e98803102c40081c5031858900c0110001880003079103269990406039038500600018400ca015555116030304106400c1503406c208030214003616408a6448041154561031214012650411030005044000c94044800d40300300200855014403e00004200c0d85400da001c000d05c10300450740c0c11018011489801c0350402304440e926044800349000400d803040c101c1c010640c0f980310206a60b410000c030b0f035543c0c0d2140300401c2070410194540c92030102500c141c0500e41e88901402002303002a00f410a801f82d120f108944200b410414840da21005110403501116143e4411543c0517948008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 850512212 1250 850510962 850510987
    0x50f0315090a02041b030c0201060503030a0e0301060509180d05090f210d0809010c030204050a050609010c060f020d0c02010b2d0a0f0503010b010c0305030f06010c08030a0b120f120703030e03 84
    0x10301300745d100480d14105280280c00d20500c5003000742d42019004600d08040f5903800d492500f00000c40981c0740d92103884c0424180c40702e40155006d40045696094010050302c0c040e1305248080701c02008201084c0003407a40e80c1d840000d40645400240da0820110140101e180701c0d5080107401c11b489031107520560b245e860340c8200114852480d08000300404c1008800c120241d100341e10500b43c0c012600a02030010745407600042c80c0804050500e0080c0001503602c45e000d55201140340403425501107040700d05070145005039048100350f4402048400c28007400140307a8219104080d0304086107a605144840300c66101844100e401060002000c0da103504d102118030141c090035009500306a1502800d500944811812982c036895903420b5a44074621303614850002880c6c0f03410440e20074034000105500c00029801401d90b208080b03149100101805002010000d5002507640404001401440041021944c01c0d03046a1030f030360f6440d06401c0441c0980554120b03540140070014902c0e54001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 850513462 1250 850512212 850512251
    0x1f150b030915060a08030909071e02010213060c0317062808070608040b011502190f0203060c04050a0317090901080714030a08090108130c1509050f0315090a0204 71
    0x70b003071245042590740c2c18144000821035100c2d20783e4603401884040800e1500010304c0e81d1014591a1001e01c08000030000208600100d00c0d9001603580018801d2039914003007001d0700500320608144180107182c0d540102501b04070110301e40700c0c004110100300260340d2902e0161a4440c6080e250419103620040005004c5c43c038490381c2034170703c124030000a401d0300510301a88916001410300c030044c0e1134a054031103480c0d42004c9040c114080c0c2040540c0c192264115054214060100901a8140351046c10300d0140b01820f9004405401d0004000a548105075001900d900c0031414001800f441c1c0380503468090800800e600440c403100101d003500c0002804001c9420601d41c0c2c41f182d5442e001819107500803000301920f1200d0070410000e49500800810b60481d80b201c0c0000700b990169200c8074184034a58026220341022440d005e4042c80e40726500c800070b000d0860b201c4800d084200000fa07510401d080c55003413954041d03170006200d04414000028103540251051210740e8654862803540b9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 850514712 1250 850513462 850513483
    0x4020f090a090b03030703050309011e0606020d0c05100b060d050a0b011205060a151b08091002011a0103050c0c0a03030c170f1521030301171f150b0309 67
    0x300114540000e001829001d4003440040184c091894511075440880d09588001e0002c042592110900d03000703040442243d01c0350502d0032100082c80c0f810010001c0c10322001000349410007200090f800082900400c0e4107407100400240080e04100341c034082019400b6400c03000180c0340c907001c204100600160007603250b041c2d090307a422001d51090070b031840c111181940c0c0550403080c852024007011075541c80a104143d8907003882d00c03c4074041041d0080389465000d048801800124025850342841000a24040b4039030001b40403807580701c0540f08502c280c188080e8100754841000c030300d55510700021075250207400b401b40d40380002c81e4100038018103440c6128100048000c0d0014154001804560780180280324107512a61202848a0b00b11000c031201c456005000c510415005110001c9900243c050709002c4d6440e980f510409410100f24020302807007513000300b070415114000b91902c005110f040701e8000254040d1110481c0e82c40921504081c401200010600007600400220b20130003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 850515962 1250 850514712 850514719
    0xe010b06030c1207050a0c0605131b0f0b0903030d0b0409140304061d0321090301020a180e09060a050702030403201e0604032003060103030801030515130602130504020f09 75
    0x6602c44c00f078119075078404d0b0800e800000351440d200364001070316138000641000082e0b200307080080d50b50305d459038502c0000c04668281c46444c3c108000c1c21803800600300051582c800c16a06260b00e42000c60340300c0c401c02050f11105595a440104166125030044000c550071101e400c0040882248035036481d07025000d594007080c82140161000d42d0f0f4108404031428024016092400200041500611480c07140a282c110706101c245000e40b030910244c10300410b265100d050506950858140c5252160800c4490f12141c03010420701800001e4195008082c10320006038956401c0c004a04502407600000d01203c0c1e83d00450713209c00760216100220040032a90391000303032840b4186801c104170045001e80c101100b03101c00c20110300d802c2125043c00804003100122440100c0000f4101a800d0708110085100c08005209003d01001a8031400b9480181d00c0540e05200081a908068410004141c5900003c540c824030346141040001014090029500d980b40e070301d4107000503004010303503502 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 850517212 1250 850515962 850515997
    0x4090b010b0a11011808090a0b161a0403020601030f1406150f0a060e0f04061503051605030702151306110d0c0c080f0714060f0a0e0d020d030e010b06030c 68
    0xf11081c1031095055099504900380c54070f1302c00769140c1d00349405c0340040c1d07030b4006148003002440c413104400800701c80b00340c2c060118141b0464640300143c10103030403401001983c00e20070440080e800023036483c103407038103c0a80106220140341048000400c034060390380c14081c5401b40305002c0c0701034160034003c540c03c507901e0786140068001c4c4454ac44242c400d120000d400c0b140d1510301402e0800407002c0b0704901910208806845806030200300c201000300705c001942c0c5004001c42c20b030800b0381088001c1c82074644a8038605040c44001e40c3c82850342c0400e0712a0011034003042070010700355024000c040d8440301c24004c5041070800002160450ba40003640d084c00c1040d40d1110718840c2810074000c590100110f030411403040c132040c0300c0b42c0041c1c8e01103e0480c0180e440c6081d448080003401d100e100710713001c0254245006d10341c91050362440c403001200c81d88169114041e6a402080c0300400c07141602e800143c15030b450703801c41d014200b9500c0140e08980000180003448145000030403100000006402c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 850518462 1250 850517212 850517237
    0xb0d29010510090b0a0504090603120806010516032006070207080c0118180207020303031006030f0603020619180b070c1a1608121905060906030d050904090b010b0a 72
    0x310054009a0b800038160407400d010b4850700070040c1c01a07540500d0300605058444920b44202c0b00d03036400a03554940f181c07841c500c0c4140d100c085641d102100b0f1034100e0800c90848c480d00d18030f00fa0035100801303000d040b200380d034010100000340412920300031040f2003a500301403802070345a410303a008420549c0180f00c9541d00c00d502418031404021054400da52400745090540300d0f110340b00346800c2050319001c104000150b0b8041020390f0040c101d0150f020f52603841d2031000740803203800902c40060305040c0b25040015075a00c0c4140d07042034401428805062000300c03000c44031040340348882d400400d041c000100d541f5580c4000340424502c03c000f00e0005c01c0c0c50b664030200ca0151106c3c0d4540e03a140800108a243c48039412407500c4520448200f42000c0c11000082e11096040301d41510040148034440b600503801c0c060145c0107581620605418241a030100341c80e0440c00b1890800e1210024825105440e158004545981c0045000341c00d56110b600e814581e078084800070b00020034020008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 850519712 1250 850518462 850518469
    0x90f0c03471003060905060f0610080402130e030d0209040e0304120807031701090207050c040e10110912031c1109091807090c032d0b0d290105 63
    0xe090300c1584000d04000040c500301000c0440180542c5241c0405640080058102d01405540501c40d8000e0417582c60300c18a11025907400911292048003502c170300114264100041780d400c06d0301a980320070803126003c00c50700500781c3c1ca4404400e52200040c080c60a40350f0303601400d18010100c03000c0c400f0b86045401113980303025500030002c14070000c2d086200050000740080c03000078420305046050010b490b000c0c2c5440c190076800342099580008011040000920250403807503002c840800c030705803490381c0e407507580d800003c0c005180d00e0b0740340310710000d2846410545425800050000509001801403261a5089111a600c80c000896050000b020550191000340c60780c1d1400c1c03500f0502d051040000c01c00c0701402d071400c0140807001000010209100c40d0000d081071410120300e841d10508001c084441100103200515440c811007211020629180b40380440c100401150740741c9610f002401d40070611030010b0004000c0c1015500134002603590785840840061002100d82e62001403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 850520962 1250 850519712 850519793
    0x30b0a0305030f0319150e07020a030f03050c0f03101706011d250c21120222030605011802191107080a0b0a0b120a06090f0c03 56
    0x912580040c4100c81500f0160400740d94130017555802084189401d010302c404540e09400a10743c41e0403c80c10a01102030032400268001c41548000d00342c00c04207880040c01d04440d0b007111810180c40f08003051108907428240c0d070b01e580c41001101d41d40d04144800005030380c805d20074100842d0081d10f423000c42da4004540c4904035032810045501070140140d6405001c04024290700341440b204814102c14a803c9500c9885414a41c6034410349003401e0500301c0082e0700b0507000c0e103488800d031103584100a07440011240e5191080102603101c2030303614078041090080c01c502081d0201b1000d0000103020454200d241200c56082410f088003c0180c00c0c9000d921034891140d0080300c0201c0491000c52085088003584070381c190980341c060f92980007550a0586500050700c0e25144c00d001d00c00700c0201c2e4491401881c0e02154040d0f00350b00245651030700c48000303440103810982d80304805002d001322003540c0706449074401d411a682c59243e16240b2000000650754001d50b9082402c41e035080a11000d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 850522212 1250 850520962 850520969
    0x1c050c13090e0c1c1b0b041511032110080316121e0c02041b0c0204050f040b040f30020606090f0604020c0a140321040b040b070c021002010c030b0a 65
    0x1010b0400604c2a16079601c150416006401002a00310300064041d03901806000640a100100141039101c003a0040003091080030500190308104412800c0d8022403942800a480e4000c00201c0c80e03540e1044900321840d1036010341850b020015203000c0d6807082013041034074103110b40c2c80358010100c1154203c996506035540301e02c030a0388043d800d5005901a4902547c41440180040344a20140c41c0c503412003542402c100020954450660b4214075040c0a1298800184c0d00396604038502074444000c0c10344080c00c0500b60350b03054000d800c14402c00c1402c0e2403141440200b9005070082140c40595004075100400c0c0040c0110804241c0714a86211440d0082c02d07613010b020180d031039500400000b50310000c3c40f14564841c4010480004045001820710100004060b580f01c6200c070041d02c0c0308286040308071960740b078000c2c1003000264000340040d81141d040050995039982d200400d40d00701024200107507110300061000400d070355054010645081142c2c1d0700740541c024001c140a501c001600 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 850523462 1250 850522212 850522249
    0x2070b010e0a020d0c08181516051605030304031101140a020c0f0a0b0609060102060c1624050106020106090204050604150e0d08030f07051c050c13090e0c 68
    0x200402064096940300754100e014050014545420f944111048a002805840210b411901000402040c85400080150303040010b071203200800d00c0c081846003401803880203990403440f404c1440034800d1f0162050b2100c22141200c6410003410120303078940084800710300060084c4200c1310030031018061480c1c1c110032440c50f0006525045d0310f02029410a4404d105c1d584200d03032407030321400700c10000d0613034a46c040d8507110b2480c24003070107002c83c60000801b03181c195806601400132501030355007100c2042c82400110340749489070b8a000c186604922090200310009040505814805980454101c80058000304070301940c94589409a0103140301e85580418280000c00184035200c060350080a010700d881c0c006810480300040115000c0441958012808420070114401400109411035400c0c1270660512903000304411107052541914400130f500c0f00b0100d0360490040c0c0545402d48810492040c07540d0300ea0346094014003210a0310b050320b05c618460b40c041400c150b60b00620b90541030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 850524712 1250 850523462 850523483
    0x15070f060b0a0b090405070903331e0e01020408190c09110c0d0e0f09090f0609070602070e010b070807060e190b010e090a080a0c1209081b03032502030102040815010602010207 77
    0x10348a0302260f404691100e8281e12104100c400406214a42000404042040071002f409174214201c40209050308031aa10402003401912400030344017090080e1500b040328006030034a8050743c070a40c103601200c8580d0414800d1003c0f500444064403085032004200d40303141180c0042120002003001589800085134085030740c050401c0b25120b54072a062030700301e40e01c0145207400f181c0380800c100d4002c811608440828407029074140084001001090480900e55041a00340429480b41c031000a0032000000b409008010454001d000e1902c041c3c015a801c008000a44041b0011401c0e0100e450180000002c02e6620301c400c800350084240c00018460074170a0343d50200980c0c04040c1038000e1183c0f0a0800d80090210724072415030b9903450fa10381c18903c0c5032076441c902e4405d0307080103003810448514a40172141c40000560342050301025000c04080e070714001043c8602400800030350554000076010980d2000050700140c03541202c64045801d0ba40c4540403801c134001c0f03080042403503445 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 850525962 1250 850524712 850524743
    0xb0d0204060e090f01090e0f0d0908100c02030d090615090f0617030a030e07030b131e111009090f05060901080604030c03081e071d15070f060b0a0b090405070903 71
    0x591104680642d50700071541308e00443c0303000900e0040c640f003d003000512044002d02441c401804400980c0b00040000c0c0b0641d0101d00020713440303024140b80c03400069039039200d603414080c030754125241d1004002d140004440c0c0320f00d83e540140846440c00785405050050029880300c0020020411403200c00142d8100030501108a016060076102d84a16104100011010414030189036003d40c810106041034480546854481c010140c100c0407080130000d00c1600128150001d4510040c0d411140000d4003c45c000d001d5940c84850b80100e000c032480c003801040240300f13503031000e8040e0300c0890319484607030790700e1510310f0f03450100300e400900241c1d40d0883c2030b0000340151002904650706001000a0301480c1705c054480c03e00403a40000040c0240300641500f503d1482c2e5905080c80503954512800c420170711403540340c440e00800403c80c22011300e1110510000f540520640c070401071000e01507960b20007502c24140c1189008a200c0d51500d80811011801600c81e04201c0c0d50014040300c0100c1c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 850527212 1250 850525962 850525979
    0x40608041b0509090303040606120201020a170c0d05070c0b0f0f031e190e071d0619081623012f150109021809040c0b0d0204060e090f01 60
    0x34049803801c40d07611000c0b5055540441c450301c00c0307100340003d5407603103418101002a114207601000d03004015a1210703001d81da021985061054010300310400000c0222035505c1d4901c900c4c040103101d402122a950b45032548003006206250042c8810801e6039103d50411200d0301c183d10b4060881d000400005000c1c00010010303540c00182d9041c40c00704021b00d0b5100c28820201101c5082a03c8208040c0c600780d180c0601c200c080a1004400405920741403401401c042c41404040e224840c20980001e03280d6a07542c507240361010b0400010709401644d0f001059901c0100401d003600c8400504408038440309400c2c20a25a48107014465078800300520054980b0203402c1440d0184210b9000c0c02208180401d0340c040c82044400002d0a4032480125282501c040c1a040075000310300400465107207a086034001e50840c501241c20a0460700e540c9400e9a0b80b240743d0b1300060b40c5003804a0f011480d8100303075024108a440394ac90711041707042d10300d0801c641c000e400c4a2030300100792050b0040c0840310 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 850528462 1250 850527212 850527233
    0x50c0421080c011104080d0809030f07020307182a02070e060d1a070e0f0f0405060d0c0b0a3002090d080c0f0c100c24022d04060804 58
    0x2801031141910b400c20003030700300e030a46025803d032904a1400140c20450310718100418003c00c40103103403407181410502c900503240d03c2046c190303240540020071280300303554040c0f01000c024a1011212100100007200c0c41c0003070140074070b401c07600c6104041d8004051204100344600c001d01c60780a40803903411704000b03001e909405040c65030000748890f041400150718807a130347d0440c9210240300d102842c180b100103120484140c4168040c1480310411040b1b0303182e0f512103500c2100b0482c1c0116560390350501007030280c0c0c0d046402400e0b48880c000001078144a00005014241c02c654440722500c01d15140c01c034001c1400104c034100c101d40420503200448840d405052980001071804003146055190f004454110300c84c41e849a801c07039203080d00b40da5010018000201c20a80d0010002c0c0700501c0c010748800420351020707004000d2050440f050031034440c0c03000f00c0c10410550464564407566182055081801000c6104401c51150385400002c048240c1c1d0848a10b50703105682c6903115a6020b00340c0303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 850529712 1250 850528462 850528529
    0x903020d110d0f030b04020c01091401060f1205011b110d1b03031d030c010605030d030902130c0c0b0f090618073b15060a14161212050c04 61
    0x2545d030b08501c402c03681d185d000604200301c1800c00418003100c00d040581000c0c00c0790302d140889a24201c010131000c0b1034241d1610899102241c5904040c540d030410f50b000d08550303640c2081c0d1107915400200e61581109560140e03070103040448000118515040c1e039640e1700d12089501c807550860f4484002440781e000001024405010016100006208140745411004410303042d80d46a0906015509003001180e100440740d18081c8a8514107030007040508082c01e40300d840c013070f841c1e10400c2101740c080c8910131902c0303502c0544e040040ca4024909013002400f69010400c500500000c14141014514000707030610400000c0e20070319117410703c0b10509603030b004800490808001c603010a20900713201c0c1002081d9151405c4039262410f000300d11010100038030a14800c52050000c0003c01d94000d0380d50340c9020300310310019601c6125a5aa1000000d2580000e0264007814690b80e0520b030b100c0140c89010b442070000b84035689a1109031109400786008002c1041c0c44402040c80d201c0c0c1401552031607 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 850530962 1250 850529712 850529717
    0xd0207020f09010b0c061f150c020d12020f0a03020712020d05031b0d09030305032205010c44061203041e0b0c060118020409020d0903020d110d0f 64
    0x1601d44610100350141c2007644000c121010115116542c0e01062001c9603114520748400300d0400511310041c40d420400c0c0c0203030080c40c10340f644920f00e0701d8001d80352490752a03001070110300c0038002c0c2e1800c000c40358804405400140604100c4104920002030032811850341078001e00081420484003030480c00801c241030fa409001c0d01c14080c081354050008204445800780240c421040c0c01140601e085100c10096041203450201007002c2507001055a80154416604101d586101c210001c1c801950403c080d10a51a000c2c83c400a10b03000340e014003400010303108802c051070403424140c200381392000c0080c00d604600e0b5020b04c25403070a078410650101740103256207044688114407514582203604080441c45640310004400c1c1621880340380100b02d5500341d01d1900450445107500e031070041c0301303d6002d100488030030300344034546806030350107415494001c40d110503500344510054101120b0580241c040c0b0340208000d035100e2803000c4800700c402801010302e030142500031140b080400c01182c04 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 850532212 1250 850530962 850530979
    0x306090415020d0e0a050c1005033601060302040b010302070c030228030f020906120c0d1104090813150f050a0512011d07020f19080c03070804080c0603040201050d020702 75
    0x9085860701c5031003a01e400f510011710301c8075074520300240380203140b0842d00c0c0700f0a8146c120250560b80710003204e621807a0745489010003c455480c00f00340d0452051480c100f20480025610342d01030544c00712044a0007128280710003e00503006400704d12620f440581807815051050025081810b4602402204040d4011040d42d8400880d154821150003c541c014480b0800200703500d4182c0c6c580350000c0c400c03a02d1105242117050011f80c1c96003454410f42c0900c040319018070038458001344005000704060b0080c01500400d183c0050b56900c8404010480c1c56100700100380050303140c0344d1038403103040350722111000c8a1000c01540c0c40e4010705420820040c0401c5a00044100b84401034000c28628504000c295119035668116520013850b54045500050807144040c200150003c0802c050702070320340c0c15813090300b0400c00324851969007028500c00051004200040c1100a008640c0780300d0950360241401d104018961109076400782c009003080c022080c00d060301354001c11031148010301c0c440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 850533462 1250 850532212 850532227
    0xc2a050c0909030403051b100e030708030c1f0605180a0603080f0705010b0301050f0c0901200618030903100f1404061e0603020607080a02250f0803030609041502 71
    0xd1070070341c003210420115003000c01d04200304142004020b13a0a2015074001c0a103a900170080b4030401c01418900c820484000b84801144c0c600780180d03809401180141c903510074a401c80d0030b036106001010700c241204150382141c0407030324a11601083d510001e024070b00000d020502c100b8030f10000341ca01c5907107540c0d0b40c5000000500c030342c006008078000000541c0c0c6502060500318211180d541255000c6d034100741c04c02640304454015a5405144001040d440e41d07903810048a0740c002009214603c802d40c2c1d2190030001800080c4184036030740700c542c1400003481e400b0085403603006910249803d80c1c4203400003c00d12440350410b25180040360000503030a80898564141514280c40a548840d6120450002850603110034100050700308000e1001500c2e503804600180704447c0090705101d0f01140c6400d046200303100320420f89685444503503200385c130101e4a1070b6805c0c4502c507202600540d42000650f0420200c1580d11500004095071500d680e00c0e00e440c0c511600452648607001d50800a44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 850534712 1250 850533462 850533469
    0x110303070e130c1e0c05070911090409050616090308160614070309140109080d2301170706030e03030721230604020702061603021603060c030c2a050c 66
    0x156a000d5540c2c0c2c500d0401c2e0144c04034081c0d03500280014104000f65000340038080f030400034241c03080f82d6034040300140c002c4945148844a01400c4000c2d0f034400e0400e502030f4240480014814080c844464980c1d92040800c00d0550307060b5660312009244210034010300507582c50752031110f8141b0340103a2000c5210400151004c514280481ea54008699102c00f07210600c0442168400b250f0582c400800514040c0d8480100350300600d840c1401403515192440c10240c4a58442c40307041e661901013420703550b10348038624010170715000d90128034491000005903ca102e030090046100300c62000d1855038480c00300440e00b040380f0400c440304111842c0001180c2c1c10041c45854000440100c50040d100028041008850700260015200e80d00501c840c2001da62000205e03840d80440c41c02000c0850315610b400d0381071844040045140c07543c0c03183d00006000560300303d004000e40507542045105684141034440d0303a1a05070700840e2460760004d044110030520030451034140900100d6412140e0324000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 850535962 1250 850534712 850534721
    0x5100c08070806010e181305070f060206151e0103110c0d03150e010605160f0b06040b0102070e010b0717030412090b09010e041e0c031a01110303070e13 67
    0x8200014210100708508103900081d0150081c1007403030f1100c51042c41c400010b80d00317480803542c0078940365410302040030000050f1440e0103e541c04015680c01d55030300c0880d00c408421030720800b03002d8010350001901151030728002c52080100100300e24250004400b1036042e00c0d5030021001c2c113155403031010507130000082c000341209002540c01403100c5145000001d0503529503074500078004030408030500c441c1050202650640341689861503c0302041d4904188204050340040e0248100e80081801d000c24035404c40d10892054030b0a20064080d04012683c64a151082c0880d0000344001801400c0a40000300f61042c007038a03204404000c10f202d1441c0d6035005560888001e18540890a602c5400101100080ca110140141424410000a070441c09280540391003542d4441030452564403850140c2c0b20301440108c1080034100d204c41c0a0003c2403c4030090a019040000550b20742d80700710080c29180560358007850854a034641d0540d000712011040d0342e80540c100c1000028003807107109 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 850537212 1250 850535962 850535981
    0xe0303070213061502011a0d020d120302071110020a11040905011103100806090a060c030204030b04030e1908100c09050303190e060a020307170f0d051603020307090e040510 76
    0x100140491904240c1494a03584408907029039040204910070042c01a408444201050700c5c000d000038144d01c000303019411030007401080311f00c5011508010331f42c1540170706002c601c102450580000c000b0200102e080c82c403802076005038002d031a5032001951604070181c29040c0a400840c050b003da969080c291a5078000a500c3d8035030200803c1310203c2102100c2d4000d007042800303881541085000c1d00c0d264844184094062a180d801030f00780e03213119034104c90046402541424050415240003020b1140980c010b9228910041409400101c1540b16404032601400207250000244c1036030001b030329002000740140050071100184a850900080c10481003400d1409250300801070081c10841e0350045847c0196411310500303027200c1e0000102c41c40c154021100000c0801840419103a520034030310701c680035680200310440c00c2c41c06508410f01940c0015a0901c000400050450480c0021110f85000070003580301000200300184109070043d0103203040d9610901003411801c103440c0c0072078 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 850538462 1250 850537212 850537249
    0x80a120608010603111c120513180b0a060519030513050307030f110c01050906030910060810140c070f2a09140f07050a27050a09020306100e03030702 66
    0x402125600c2c00e034040001c80c40c2d001a14440c0b81e0400d4036400201c7d01503500080078010001811980c003c191a201401800095007100c0101740010300e4001500c0003260756801070f1284240402d0490041066802411103520441d05c4101171200c102c01a00c40074144004140c100d0440e00c011074030034001010301c0360017030310b0312020000034050040501514080101c81600b022045040c681e80c0b040482c0e81000040720505c0d16511120300c0642845c80d600300c541034481c45c001340040c1510b00403d401d40e5441703e1a1041218440c0c071101f000b94034208950810010100300000b20000d1a0344400c01c03611400340c1e4240407148840c26880d501d503d020103c0b0003101c00340100c1007100200360300a082000c005800c1c2b440c0603040441080408280140c5100c1c1408004914495203911602090300001d81444d0350341000956010084401c04450241d14050b036812400422103a00364000ca0b405a08081d050502d001e030700078011140300920801d1103506010030070294015a40f24203d0854400003038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 850539568 1106 850538462 850538483
    0x20a0609050c1e0103140603120c030f041d0606090904030f14070c080c060711040209010e09101701140103170f0301031b060507080a120608010603 65
    0xa8030060740000450314102c000d26103d4085544600081c2c80411180b0388001d030440d0001000c13102680c0503030002c0ca10000d001c04c2800108032502440090320308000e100004070020b940140d0000c40103881040590411004400c5141d40210040701d115140c490070802156203042c00600150500c004941c03410750f6540074050301ca50313104503020041d50751600f520740505000b08034003031030b000381c422440a1560307414104111a426500f1465800c0114072000407c006540110201c80c100400f5100e10f055075140c042c00c060060f00150301c01107005050500601c0d640b1320540c580036490307041c046e00d103464603050f204150549400c400003001c1c56204200000340d521840d40c913454030f441e00000000a02c032248459082040c1da60561400c0c803030361000229040c3c000d01c00080c1110b0000c1011100f00340c02400580d422001e018004540160b81c1c903001c42c03c482c42c5a01c11703035800015 = true := by decide +kernel

theorem cover : BRFrame.Cov 850359712 850539568 := by
  have h0 := BRFrame.cov_init 850359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 850359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 850359712 ≤ n) (h2 : n < 850539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
