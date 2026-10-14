-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0811
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:56:15.754031+00:00
-- url     : https://prove2.me/submissions/f18dc45b-5079-4f9b-a8f1-b26292f39392

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 145683453 ≤ n < 145863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 145684703 1250 145683453 145683457
    0x503030402011d01170c09030703240902090406020f07051f0507050306090115030902040f02070b100f0b0a0507080d0501080d09080709020a23040609050d1104050a061205030712030203010b 83
    0x140485c002842543e946c40c0b01c115501c54820941d03014040c000000041200c03540082c0040c4140d0305042d80d0048141c0001c0003182d0302900080e50100c0c251022502141c020760080481e00c0300040381300e18002550f2145481d1038030758503c4e400c009845200b215001d100328850550070038241d1a00c076103076081c01c40c000b40c15044c041c02440986031100d02d0884405000794440c0340146d070301a10a105603007030b40300b11000070b40014100751501c5010720000b5246454001c102015100d050000801482c00e107001002190006030402d028083c3c20004034003c503207a040034101051074443c001c00c4560626803640e0070f00b06074282103c140940e034a003d100c194404550441500c0c800d10f001030b200c0f0140003003110789110800001c038080c1e644803501e5100349480002003044d05ca017511111700041c0c0c3d941c10310009500c1e000d07000e81045c0340320403c403115280c00d410081c0c00c0303220284080350054a9060695003958468000c8400382e1001071510f0402001440c003d51500303c5040c118115803412081d58514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 145685953 1250 145684703 145684727
    0x31005060d060525120c050a0f03020306060702120d030605032a030304050a03142e1509050702030901080a0e0c01050c0102040306020316110106030309060e040e0a0503030402011d01 80
    0x10544880c00620020081c070340c1c0780f500449142a003060f194841c0005010001c4c0b9078444001c1707600b00f004080903240100125501501142d691805520a91400714000d400c05407400303078003040070400d00002d030740c9984460030101c0d030303c4c000303018070a0a103d005021075115901c8a4040e400190800038012840c0d203507400700f403a6110500c2072401c0e8842c0020b0440c400c1d600000c0c0e011181060100511074104440661f061316181204c83c00500c145070001c640c15042040c0d01d4000048000000c80c000c00c0d04005e408a969100c0942440d0311044e0350002d07114110b030100300690011550501d90740e40311010f80c0d003064600008004038000104480d8171207200c21344c002c0c140071000540c44100f4500754100c800441e0000c1c0119180d040044880c810190b8407420240028012100e010201c84188185411a41d142e1a0001501d28055058886a0601c84216031182c2d803a001001a420240411058039210b20046d41e524075040c400989011010785e008a40100580c2c0208002d903004001c17039803c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 145687203 1250 145685953 145685963
    0x206070509060901020a02030a11100512040311100c02010509070608040b010509040311010c020a020a0801051512010b040f02090a0e09030a0302250506010305010e030909010b090303040b0f030105031005060d 91
    0x10f02c0075040700507031428400c10002900751144003080414070110100d00c8442000807151075214000052080764580124681c4000e038620110105001034041c1a8001e04a040481501c03c50540041003000700c82c4144040c0d40941d441c6d10810000c0b8400344110000b8290b9401c0c501c03184d06064444282000b014010580a500f030071000c80c1c14103028001c80a48066030308028061030000c07200c000d4440e2078440c0101c0c05424410000b05070901c042c002e03103203d9040210542e082c00100320421007030301500010303080356560340c01c4904410f450354001d08145003a480c40c0541d40b4550710090081154513030b44401000410b0311b06208180c10003008903041c004162501507114960144810342900a208020041004042003d400c110003c1141c6040744d000e42d0082003400c044500f080c0e1203104507081c0c50351002040c4018029124100041d2031842c402504407410a130b105d924000c40b540c084d0900004586000c4010003003071a04002110100e51000c2050019041c160046060500c501200500c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 145688453 1250 145687203 145687207
    0x609010606021f09080403050115090b0f1e18010e0c070f030f0302040b0c0c0411130308070c08030a11070504090308040b0604090816021f1413092a020607050906 71
    0x40f22031800c1e005900d00d16000382c0c14584d101c0c4e4030316045000300009222610a4150803800003030800c41c0b80b1400f5100708015210441c03000c0990200300040002c5d03071060289000700e03029502143c880403003c00d000c05100b0301100711035040001c18025503c00070182c646082d4208141000905400649254194141490400070480b40c4007030b07020b0300a0b42c1004040c42008160b40043d044005900c5044010990b01040604000f07600e014080c41014806040c0c541820340400018100c0300044c4803007800354442c0451551903058042c01c547c8a0348001d00001c0040d03501d107840400c180b1803d0010700c0111820807865a1941e0040c094440051001c1c20130640d040000b03003562602d41142201540c480400c503a82c109503201d00d14507031a00c49060380200d4101040e02120903003003644d200840e12070f0325680d070f035200d40780c6400740c3c9a4015040510601301b9014001003590450044c208070303940f4510801c24440e101c20160703900c0b5090703030b03140702c2190f0180040c4200703117801a0071180e2107241aa1466 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 145689703 1250 145688453 145688503
    0x17030307022a03010c0309030e0406050a170f03030103030207030209010608090d05180909010518070509130305040909080316180614040302180406140403080f1308030405010e060901060602 83
    0x1010b40d9101000e80390154240403010341403990560224100611907240d1100d0320b4a103900340000c41e1200e024403500014101c400340070300400d81003d056160080b00032a00309040c0c2071085403d60f04283c0c001ca0150f03005107028411440d00c400700a015007040e1600315080c1c07034040111a80c524600034064103000f400250b1419021030091010188540a1b0528a03e0300b84445510f008003001c5410302080c03100940741d08a00391001c5020000c580c0f0040210700c2c00d84481c0440210381111520417414130204020000d600083c074020710060740e000d420280d80301d142030500340403118200050b02c410005428171030880f06c41c110500c1c2c0c040d6099031805d0904c03241b165018030050311480c0c1010703500064400c604c2ea51090401a010f01c1184190400d2000c00001d081605409209813030080100e5a140e000582054800030035950095440511405590701616480b016034401d880c1920036035156010103552010400043c0e4010a80b00001c00001e450304000a413151014402c0c2c2e4840300301d4003641 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 145690953 1250 145689703 145689763
    0x20c010203073f0206010801050714030a02031509010e07030b06270102101104081204060c150207060c02030903061008070902071104021902010b04050f0408070303091b1703030702 79
    0x40f1102401848100e0344503195850065036484013442491090b41c20100090542e911506c0002c000700c40d0f9078419401c688504410a020f500010440d022403503c07003006100755510150594005c216291600c0000e00b000c100040c10f44020082039400740600b00003440c803802c00040300204002401c800c1c0780b010310401c00100c0c1090317050a00e80044500300f2296082c880030403001041200e4100c01143c00103441c201209109009a108240103c1d0a020b40307100401d40c1203064290034000060700528002d0369503280001c80d0440041500141e1000c94032124074201001502d4101c4200c0f890004403d15040702d03590794030181e02170240f4294001c20038808200c2c0001c900141c00300002c000f5034a4031500b0710116000310341c8038030900c010760030011940550300b054800c490140086c0c0101a54a0381c139500d4010056000f0081241050760318100400400d5029071000901c4d404401618589454404556058488416111919001001444681c035000100d41200044c001c019030030340faa0103100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 145692203 1250 145690953 145691033
    0x3040f0f08180109090903020303010501080a0204150302041412030901030c0e0a0e160e010e010f0e0406141503090307121403010305030706060e04050c040515041407020c01020307 79
    0x81c03401e1000715200720741106241c2042c01c861000c0c0d890790b000b00c0d5658142800e40d4074a6a014016030020030040c0900d520035030807a40d00c103540c00c42c0585015910309032080c000342d0002e80d010000e5800306050041c64071400d00e5044280d400c4410700300c6403101d400d540da1070b88256880c0b20305055a83c200007900d40d000e5800c084075a1030040003003003001d035141c000c01030851040b10300c0c2c00840c11041c9107000ca6401a15481c140e45010380d0b80f0242d1500d600300540310441807140780d10900070229042040c65866008006c050040010303183c81d02503043c403e009524200080c1440118410700811030801400803c0d61001074100861004059600c07a058512080120003d10801d0b0004004401d0043c000024422180f00c1c28040104903030310b180d5612805003e03100144960050340052f111407816801250700308202d000c1c502a4401d107400021f084486801c01915003c05504c10050b0700c513014803850300e0700c00c402c3c00a140741280c10390300c9005200b28503855452001084c05034800c61007848034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 145693453 1250 145692203 145692233
    0x1c08120610021c030e0601090902030105060303030907030f061b09080706030216020f0f03060a09020a0609060f030504050319021f061805150d030c05070b040b040b09060903011509050f04020603040f 87
    0x1528502e507110400323000948a1800e0036406503091102082c00c0341400412a80704800040c0038106039401c41e41c6104c1e60103100941640d02c1c540f180b02d0101c900d6044c2c2c005032485500b64841d0001a440c0820040c1403d2030b640c4040c0c00c1c1841484100c21a60b90080c200001642c1103a8000703c0c1c00315400010000100c0d4000c01f60144140380402c14040c405038008203e8174000c94494a4940d56124121049051800b5100000d00c94111000e03407035009800c40c9030440c0c07117001664200702030141c00c10150b0350b06200e1070005074030181c10034400004040000c0b528421442050042504146441041851041022604030744d02c0d400600c8140c24440b2248003120000c03c17480100d40320b4200104070a100070b41c10382c0c050050340c000207100415a011513007101e0b16480403070b080501d4544201e0094001c84401500940c3c01c0040202c207a90a10980c181c010048404014490038540668125180200726202d060440c1c01030101596961080d01e600c41d0b40460660030000062500d0040e11503815 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 145694703 1250 145693453 145693481
    0x2210d050408031e060f06030907080f070603060f080c0d08040b0f07020f0a050f130603050f060106091e03060902010e090a020406030b040b0a03060b1c08120610021c03 74
    0x18240010002c0c0d0710011405661404650074604070180c5144840e254107581003648114840c1521045040c800701075507120100401341da89080da00c028545c02c0040e10320044601e600414800c0c001701341c0601c00d402c0903154204840d40c01c141880c030150b071344112f54030000384603502d5014500708221840d03085a000e040b28001040d02c8e5440d00c010310445400840c0120f01c515400110761010b03050180100c421654020001040c01005d0300a01800c04240c21142d042c0c0d50f11f89601001261040241e148c4900d10b54006054070341c0760800003800390019030412500a02c480c043c0140c80d02502c0c02020940c1d4001400140040c80c41c40103030350170701c0150f9009400c840b49100b0404002120360182c41140d41549080c0f01280c0c80800b048100c501c0700c403169921400305041480450602c2e4000c1118040161122031551803c0c120170305410000c0c0340480340c1c0c60300094040a03600c80c0e200401c0e00140192011400b108401e8800b80d00e440709c01c2424541d28201c070744c0244101d0722a0b0800c1c00759031401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 145695953 1250 145694703 145694711
    0x415020712020603341b02090a0506040204030c0b0a0201060f060f050f0d05090c0f012307030905030604050601030606050604180e070f0303090e1509010303050a02011b17010602060702210d 83
    0x108a12030512603003003c50f500402c1c44030030038034884041b803c003020701c26500038807401982d5200c0d00346100030007002c1c0c0300070380050342404003200080322000280d02074400c40484d40d85807075a0520003425162281c12400c1003c0201d0400c02071280c10040c0d41090303107842d0400c251030300c03c01da100c10b038140145d8000000080c145003d00c46240d00204030120040c0c01a82d0000c02d04c1900c100641c0c400000721420005440d20207403803080c03038000c140170302500741c428608060b00c655100c0c0080e01d40001660f0954060b00084010002c000e100d200303407401040f0070f540c50350410b403a110000c0f415640c0034406031311080d15601200000c000c02e01181c00a003000d40c4801d114980c072400c00404601c014001c1040d600b07050030120349607000c24292050004401000021107a0855808035400e8000c21042c400795900d802040c0c011a0035a58880120b55140d0b0301c040030200b03a9420140140c1040c0e0100007503422140502c800681d01050944201c1714110803529907441e41d002c00c41580c40350b6030850b00f0700c0d803034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 145697203 1250 145695953 145696021
    0x70210050a0f020c060a050912031b0706020c0f0f0109030b130506090303060a030f0611030103060506030d08060a090e12040803093c060d0f020415020712020603 71
    0x1006401080401d41c0c0b082d580e02e03140c0c1c0040c1d03910080400c85650002d824080180c0d001d20a40043c070250201a0441e0700c1d04041300c80c0c0902e1034021005c004020703003841003c1c290580d000c120200042c1281e2004008206c2483c021800e00d40c1c44480c014081e0748030300031081941c3d000e088484010351b80403411014503d0007090801c0e0301c01e90720104072640c2c000d6402042c18090004190b9004400c02015041800d02d1907942e60922036141004941e580c1d146d040c080407980c400d1010f035000358054a404a402d00d409420941404507034943d10040c010040700303106079510b411120109445010000003080110340707800616015101b102072101c24400500071030002804270240428000070346000e42c0003111005400405071815042900f58003130103503c0117014200500c1030b01210b101800b003078a042108401601a00c4c941c1162000040e00082c04100d5080b001c5500c00e907510152014003030250900303444060301c81032604041e20503800880481c0103c4040a0460000d205100f083c002d5405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 145698453 1250 145697203 145697207
    0xd0203120c0c090408160c0f081c030203040b0109050702010b19060e030d020a0303020d0603150603110105070c171c0305091603051009140a0303020304020a08030c03040614070210 79
    0x1c4200c030000d14078020b8002640c0241800000d440c066640109a03c0c1020740814422411154500c1e05a074680704484001a48460041801c4007401c1030b64040c03c0102c9015104800640c488031000c02014410810480400e0008100318191b60b00c0c0c01c0c0101d02da4482c448100e001d02905010203900c00d0718500c00c41f500b2450720380c50108507107854480c14110300c5080300309a12581c03041c0700b28016802140c002c07030010b88640c6c0181a6200c41e03000000b1034035103940f144940400c4018549040c00d688041c00e000b8002e074428280091002440c00625004090351207169144240c844e0441b1064420107001c040c00b0103211030703207046802241c44000b6220210006000d40000c0c0c0c0c008041e4054228100540f44d1410b46840590750014028107c0c40d51407092503006014462081c0e8180ca94052000c0010f070062001a40c014020307940581c681c00c00340100030180780c2540c080c503c01d900400c03809030325040100a65003252071a00389007419089500b440310452007286002940522041141d12001d5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 145699703 1250 145698453 145698457
    0x12091e08060907120f020a031e03030e060c07080715140412030c051909090507030e060a1406061b06040602040905060a0819080d060620150112020d020312 68
    0x40e95100894455071a01c45800e62900041d00402d1a08040d042441d1302048103072200f4081c0c180301400b0103400c0383d130741c2d25103503548020b151600080e8500100ea2a00307160341401136039824010715000d441340d4140780c40522800d21881400800c81000410312000b881451b16808030f45034070019050181c031002404680b51304004072022121440b05002141d09988248039030803840f880d0f80c444500e0007007592450001c4400c50720742001080841040418803070300c1406050300801680c3c0307000c54603940340c072100b50400ca130050811191034640f0040306040e8400803481a0000e07800d441050381c0346111004c1010910325000d40c581203101e0b402c240800c0004c0c550041c421265030301c0d41007145450308010000b140f0264400c421465000f01c0080c0f0744600f140c02e00314002d611600b115854403c0d101d0044051b91110f0707218101091b15500300c90003e48242c118040041d40140141403000355071900c0022564040c001d001d542c1160b1038100c4d045445180500a1081c2c0040403181d03070103240c200000c000d0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 145700953 1250 145699703 145699709
    0x6020d09050307050d0203040e1801021905130605120426130609060c050a0308190f090308011203050a08040303020f130f080703030806060307020312090304030b15060712091e 77
    0x16205d0710750845c0b141c81c408010f032404c0e9464070b4400c0442c0d031280c410f0b446d84010341c0041945195800c00040c0011002c0840c114000c003d02c0d00c0d8140c0350120442d94a0946503541c0c41001400320800c429000182038801066000d43c1c01540105110500b00110000b90440e020302d81700228000b0b581540640d440d0014412520560b54480820340c0b500ba0840300c00401c800c0040c142d030b0081002e030300080c2c0036a08166101c4a4021100140b140c504003c1f000e0307401415020800ca0303560701001c803d05500c135024a000d01a054600213080280d5500200f080c842d0841c41400c20a01c140401d0402d4440d404039001e4200481d591500c80c910320031030300070360001071203441c14020501000059852010850b4400c80340c254607210510750380d940c1400784035840102008118081040010000c43c021802c05000d48600d400558440381117140408401c1000f4200383d1010091448012007561500100d5401641c810296010030300015015942d0300141c1d0012080402e500f1149107500c01604c00745012 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 145702203 1250 145700953 145700963
    0x2100f180506010807090b2218080d0e010b0102100b13060b090112060f0b1c060e0103050606030a0b070f030e030301090903120c02190c0504021605150601081306020d09050307 77
    0x31031b40c0c0c985403481200c078140505508071481183c0b00440c1c07407920040c2e034040e11042d000800d0180d084080c40d80417020300001240c0e0503034041000c4414844600c10f18121300c2c8000b0017001041c00500010f0b51301e90100076a00c5000d0b403280c0c0105025122540d00400c00480c2000501407651141d5541c0d0580e00200c80d0140005e04621031070301030800901920080b289424040120340707041c0100c0c2c1c0701d103610a00c0d00940038051909100320005441c4039030f40c01001072015089007541945481428960050400c1d846a400b48601c0808605032002c5a600b10a40d030804aa2481403994103801804001c607103002e0600000c40000744070b80322500028142d46c030076a40d28000f52000e0b4990001c990401160100582c0080d075442164509810368011040c0075600404a856840e40010160783c003540c0480c0200200b00c4c110020001e0400240c1030303800400305401214a04480002c20300d040051040f03604109010f0002e051010542c1110301440d0711171340511144009040003580d84d40f01403000c6135 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 145703453 1250 145702203 145702213
    0x1012180618081c06050d050309090a0603050c01031802090106030b0f0303030903030708040503073c1a0601050705011a0130020a0e0603071d1002100f1805060108 71
    0xd4001124500a5034031a0b000c81100c1c18070404803000341d8908040c0414401c1d65a070b0706004a0290b4a102c0300300030141c4104000c40d600d085002c03d02a2065024150303501d07040c240070302400000c0021540b40c0a00c0d60078a40010500d84034108070445201809020b504101014008200503a154020140072003060f10305c0d03403030000300380c0526070341c3d02c0110303016407080d041400803a00140c403c400e080e8211b4000c004903424005113031540051030080300c078001140b000e95101240c00310000d695110803d0881d41c010902125284c540c4002642e00e400901d0016a400c40001e070a680541d0079154440c2d000802000054004c1042c1e00d81d5540c0ba11b1480d000c01c692181034003803800341d2000051a8500400700c0240651243c009001940042e21503200740f00e07100c2c1c7e00c0c20b407a85800d800346100c2c030840c1d86c0302001c14041000c0d034280c0010381401c1c14040d5440c07030089203c00b0b800040144ca00204900b0000b0001043c1404000a0242c2050440c2c0780d0701e5417002c8004c0c01000035229042e16490340a5403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 145704703 1250 145703453 145703471
    0x6030b09100e0309060d1104240207050402041d04140a0501020903060a05071e02120a1d03010e15090f060f09060105040510172506110a020f10121806 66
    0x750759021300c1200c0c41d400b1804210300d070078640007074121891040145038000d0800d41c40d040038003100c81c00400101c2400d99101600d189456040003403400800040d1000c42c80c2a08001040b8452080454228424589100420200420400091180f4102d4030039180e20070f44a00c0c04501035403200700300794031902c01e140215030720314900c3c81a203002d01000c2c0c47d01005000c2c1c042c03441e20948034400d070220030360081c0145414004130314401018207003456034030621120a01c3c1038690003904d8035080a4000e0b1326184084242c0040001d00d8181c0000001038820140e07248881185001031006a090700e41c090b1500b489141c20340418207901440d03d100507120f2980e00c680a100031900125040010010111410840e01c0d5005140fa810801c402c42601e204c140b01e10f06c4c00303910451009007201083c907007442c03c004081d8007000203140019a10007a02c0b0490040c2c000601c2e10104984061050703198100010301103002d647e0108001c0c02c8403a050200100e604107010b0440201d440c1654460300f840521 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 145705953 1250 145704703 145704731
    0x2301020a02100501090513021201020c030403060c2303070e0a0306020703020307260304060b06090d150f0e250e1005090a0b03060a0c02010902060408011b0203040b091306030b0910 79
    0x80b51240c8031000030100803584035020001d01d0009c0d03c0c94520715560811440400302c0d0140003d101460203a00003041510394404024110200004082c85148045101088094074142101d4001c484e52a00304500d1400f24001150690550b00041c41c4a1002421904041d004405404807600609400454050694030312100e1611a0000c0a001908000150000e0302e02c0c0c3c05000d040201514842c10681090f0100345446240042910703c04110480d00d82032200300e0080c111060b00c002c8050100c1c09000748150740d43c0a007514003407170401101d0014042c04d000f40241c0c07002002050061a09030400c05151400703030066004013030180d902d800000310450268040c26240c00f1018009050035661449510010805901003100315500c0301c80402c09655140040c2018000907800041c2c0ca0301e900650450144080f02c2490035908180420808011460160307080c40c501070f691030031a110000c2643c40100f0f595000101013184e0841803107508140020110140c0c90180020061502c1100380 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 145707203 1250 145705953 145705961
    0x50c04111315030902030a0308040b060301151502030c101b0822051c03020d0b040c05030133020c0a0b130519031a070f09030305072301020a0210050109 67
    0x40c6410041d80071001c010b00c205100d40c500c1860098640002d003124103500107401c0ca2901c00040c0e000491150510040c4a05179042a800803801c0380208582490050041c0801c0f20300e1203244282e42000f180700704510700070320468552002d004251080701c240c03c600e5034000c0030f101e0280365268070000195032440d401100e2040c001e034483d45100c44180017078112902101407440f402c452a01803102d18912f01102c4102440c104620340e1005070b142c400070444002101d0501140d10f11613070404420701c00185d0071008881c1541c0080d0404080d481c1250b031046a03180d071505450000100e030600e50144158003203504100d0560446140c0039256a4001c102d4150291000d00d04819150720400c0115240c20b610f25820380003855011500150380b070326000c1415000803804c3e105210724004000381c00e07a000c5481d903030304030346401c0203440d880c1140c40040c000d0142c0000180582103403040382802c0c1266500119030001c4120007990743e24803e0304002d403079608610700c0d4850300b400c1c0300c0086080318013070003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 145708453 1250 145707203 145707217
    0xf0415020a0e060c0106170a0311010902010804030c0305091c0b070311040501230703090302030f0105090d0e010c1202160503010902030a08090a0f0306060f050613260109050c0411 79
    0x10342c9441e0340e0542030811031503a0202020106030740d41d81c03c00107054550001d01110018800d40030302154656410080d1000341041307809000e5034900648540140c1e003020000382c004c1e405280c0110301c0010f51401703803280d00c40c2910060740141e21305108148681808069a052445041e1100140c1c8034080168160340c66260112035080d007d100c140040d5115010f03a65281c0e182100301426a190030542481e0707684400401d0780041c0c1c030990207000b0341c1403c000e1907402d1003405000b00318a1a18014958495005903160004c001c4951408034860f8407491581c41c115411800241048a0300c0c0c5020303598460030520000100d007008400035203460184104440c003078000c0c01a0900c2103890780e83d044a0b902112000d60f02200c0716074041401039a041803580690b00c11840041c0f40360520801d031641d00707084d9000324425a000c0104001d80b40400f000202101d13801c0c0c0842e400b0b40ca13046d1079000030180d2444400860341c40e1404c60000d10100040c031f040030a4040d501080014024080422359100c0d4070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 145709703 1250 145708453 145708457
    0x9021c051303050f040e0f04051501120f080409020d050601090914010e0714030403121b0c0f020a0801240f0501090b031f060509010201060923040809030102030f0415020a 75
    0x142103500400c0c000c0f4010540c80c0030b01803446150545683d021000d000042e15610002240c1e8001c000130070104210481d10b001c20b013927206411391301d42040314a48010b410002003402c1c500151400400c030140007650054040e040c0299120326500e00603030010401141e046000501c400030002c0e40f05550b100340340c0540e800d4080d0b40f0407a0300b044030218414101038a0350703081040303981c00f081d8825210340146004c1c1c4d10903070f1080080242044240c0568904400840c02014040c0c100720b40c664002d000da4000c1c0b0361002d005101c4005500001d51241044d903c00e00d0300e5400c0c94036030940303102000103024180e580c0516100e07041d510b0311a8001a0b240c036008070740c04100860014040071070b0210296a0181d5007600e1010f10400e43c03444000708901c0b40d0300c000c000c00d40c045800c040540e0207000f450050540740c1010010340c1c580404207003400400029210400c8a54808242440b08076005c0751700510703000d8000c0d980c82c10684404c83c0660812101610840c55682001c024003440d402150b140c60803603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 145710953 1250 145709703 145709731
    0xf050105060409022217060106020304060e01030b0d0b010b07261b010b030a06050f06040507020d03110d05040803010314010207050a020f030a2102010e0703050601270609021c05 78
    0x907401c029070026800610030160300206081c505c1c034a040c80000341c0701d903400ba00285403034001154601801038000341c0940d042400180b121a91040b0744044040092030041078000e12500031500301500441d01600507684400045010100040203001083c1703c1c11000c25145040c5440c41c10765000c28282e0449200d00300a00703011189915030021190f0b00c0b2600005940714064002490701120000c1142c08a407148200850703044000382d00d690111041c3c1c0d00741301c0b81c940071100075124600c1054200a040d59414071490042c0700c40c0c02e0b20b0075603203038040402960030703e4240f034860b5030424401200d05400548402e203100c207041c002d0fa0f14881d802401800007106035401c0007250a14440001c0d0148540250080030940c4291300c811002000c1c06070020402e81c01e04000c0c01d544c80e1071885280307513014400c10800a400064440e0441c2e03d100d0a03403443c1c407002c80540c40103850704890710964604088020a0740100d1358011300207840704101002440c0190b419420507164111740310690b122031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 145712203 1250 145710953 145710959
    0x1021905060402150f0408010f140702060c0d060f180e0307080d091a1003020f0d0b0a1503080a02010b0906121504140706030501080f01020f1c1103190f0501050604 72
    0x603801070242c2a40400e0342c2070030411313281c601c82021b41203680054083ea441304d40a0b10500b413280714030790f00310140010b1004e9618042d28040e5441d8400381c0555003802002484684203121035200c800540304209003142d58542d01e001e50340c10b0001141000651f189007031203501d488900001101c0c00c2952155a032030410102136801c81c000c254884054030440c003034940045d41c0f003415840b6503100704100340c5c01116041c11401403201468030840614051000040044085601d64031650703400386040b40302140354070807540a10303d030480760b0784010090000850b02d501144c0d010741100e0009101503412201542e0b034901000000360381c43d0041916508503d4402a00c0000d42001550040c0032f01d0601010a001104441c40c004640d071100c0c000a544000500c00c50b0024091701041c1c1480300000d43c141010660100c4d028824000c041140e441125404001304d44181c0001d2b00403141d408500c2c1c0c403450020160703000081d02d001c065010700d28012602428099500c079442c1a18030180802c1e00f000d00f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 145713453 1250 145712203 145712209
    0x50a26030c07090b04060b03040f12140d020315030f03070501050a020304030f08100b0409020c1c02030901200a110f0d03090909170304050109050f03030106140d0905061501021905060402 82
    0x304c1a0701c02e130010345030400410301081007001940607e01c80e04a940000c1c0407030038083c45e040800c0314000304006071080b07402d81410303014041d154803034441e000040c2d0701e403140800312841e54010903403035402d07008140240083c1c20b4040090400035000300020b11090742d841c1e810000301e12040f54001e011840340505626018440c404244e0300400070b81001d1401a240d001c40650b540090b808200495000180050b078402e0901070090700c8051200b00e049200311103a00079440c2c0c0210302059042000b01030421884400c0610b1001c020708001c81a501204000e083c0302260520001c14940a4040c803610038020b424168041600150140c0d01c0000003428104410082d051401080d5001d070b949894042c001d03175a420040d80507601c540000505100706241c09820020207003a909010303001403004100740c40d00003401401504240303d5080c3d80e00c9414405078010b04900a0240962140c1070800c00301111120007600c20202c00d0b000c03112010031001c0360305100311803040010701c103802840220380141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 145714703 1250 145713453 145713461
    0x3030e010227030d180909020a0b0c0604030801291b12030103020108010e040b131401020c01060501020c04150e06030a020312090436050304050a26030c0709 69
    0x121045002601e080c1c200c292a40e401454415042c44014900d12010110716041003a06241d035264140b102001044072203030503100640348141d01582d601e4200303242c115a20f90000c0005807403413074211521007100b03864540c2c0d104c00484044021030386c0c11002048058800c226086134103a0240c609000001104204900c0c0e08580074070740c141c84208084621110050146809106c0807803040c503220740c55400010b01c2e0a0042e844601c24640703510902c000300300c03594150707580b01452903101a0303590a645403140701c0206019441c4561b501c046609009000190000c1044030b50036400ca4a040c001007007004101c440e14100b14600c2c00f00000e04000807010282d50685c032100080550702c0b0010242c01003820101421005114032600042130200d03490244141e0300882c01415900030221101c08a022408800080c0302403d01500c83c1c00380108102007040700c015002c06006c04804a964000c10072401100a10102c10380342c2c00130002030f9188000080d598107104107401040750a251100b02d000070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 145715953 1250 145714703 145714721
    0x309020a1217250615060206100b04050d06051003060501242c030a0b0f07020118080a0c0f0203011a040b040207112416060b150f1b24011707030303 65
    0x50703505ca43d911244001c0c1102541c0c02014503402921003403034200302c2801e10750750715045811443c90503c028000c9880324881011200d40c403140018240e00c543c0b08803c4d8404290b03000409079400c101c004219590402d0480c1d480e10403400c1449410800d0400c00d41d103112450340b03d400380c0c03014290b00303035426400000c5804051402506844c1c811400f0b0719407038004c2d80708490900004c0c2069052280c0035909210301c88014101e501c1c80000e4840ca540c51850030b201e080380900800c1040c0004106101384003191607001c031307030080c020810341403544d84000c5800d500560361031246250070304000c1d02c3d082c54000c0711001c55200510f080b50851040410034458200604e000204110f4521074a000102c9030050085004812840d03941d01c1281ca0028182d90001c038816004204460f02c00945c0610441901d01341c0c1c0f00b01c03111a40b1000c021043e28044003445c81c40702a41d2140060b0305440620124a4161044403080084070a030f80780d0031244044150081c180180750301008003000408d02c603a02c40c10003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 145717203 1250 145715953 145715963
    0x5060913022d100c20010513030506090c0a0503070b1c090b0417120a0b0103020f12010509010803040e0f15120c01020106061404150309020a121725 65
    0x1100000000b0070650850704291296a11031034000030618010070019945242450500064100e07540d6a28000301c800031000902401c10300c00b102c19a000b0029551001c00182014001640d01e041c41a80c0b880207030780707a00c142e00030001c00c00403505100610b10300360385e0042c006100e80c610b4100d0b1001c46500c18141d01070901140c500e58400c5246600400318901c6c026000c2082d1814142050428011410041450b08408000012441080c243c0c890b502401c90100050104000340040c2c1c0640714a820001100f6000505001f0100e064891315040c0d40080d199440070380e0f29000d000b0b07a00d11071170041051120082000414440c595508a030340804004148913031428500040b8128158401400e01603800c008811416564240b040750020140c034034203002d43c0328500d00401018441d601800c8003141e0050040402036020b904144412640038048542d00f0355900040f000d101d1011030200c48400c2c00c08107468038071883c0d10540d0741620b00c48461108501c02d4180941103480d00c00c030129a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 145718453 1250 145717203 145717219
    0x40605040e1506030f040209160813030203040f06081f03050a0f060605060d0e010c020c0f060304170f03010602191502070c0308161e080910020708070b0901020c040506091302 77
    0x1030300c4a00c041c43c043d1100a440b460175003028410054245401030050065100b00d40100c07000030362003258250846074941038603116801c01d0808074118403035030f08951140f005810000808a44c4000414420815511000d1407840a06e40440e4400b0880c800034029600400382203000c10407144148041c0f0340b1421001a0042d0741d18041641600803d082d068001e41d103d40d0030720400c100b8001d0340c200f500d045c40900044003034200007494a069170440306025001c007200240400982c10744081e00015070820f220346550300340d0100b40c1c29510034040c0701d0060090012411840c01c2c1039030541e1841c1c0e40b0124a1404031040c2c0080c5c402500000350950300780a007800b0010204030201e00400c80c1220b02e11a0710b1082c852410320001300e814a1803003180002a040d080004a4202401c2da0380c52102211400540201ca2404038901083c07604050702c17902030080002150800389005185103003003a000d0355010800c00c1301300310440d1381c1111215040407005c0c000480262070103d401c038406200070301c120 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 145719703 1250 145718453 145718491
    0x15060305010f060503011a03060c0c03070602040f0312080912070204021210091103040c150203040305070620010507020d1112030a02180307150f140a02010603120302040605040e 78
    0x5003514001c4502d10140750f070f500c60500060400f0701840b603501d07a4160b0000c6242d03580e903000ca0750311440201ba907030207158041840c0c3c070002c60078804c40b0005a0004402c0d500c803502c9011081880e55030344001c9628544016400316800d00036a00b0511894801024109006c002103030304000b03900a038422039200c2c1c1e00b04408081070545001650059043d44841c0300c0c650b0910021800f1548490f80d001d54078907040c01004001156904207c0c00d48203400c08052564805040503880c5002e190030080c000e0060b0360000c10300c0b503403000720b009002d007204058040d240070b400d50003400c0b241b09680250040c0c1000e1040034489004541d001b0707071b0032201c0f000c5800460341c01007080000d070003d5821045040d00052884d043c0780d0040d400d028100811400780030042d25004407000c48100c1200f0900920140382400c521141c01540c3d122448050002e806588030b030030300030090003003a403804102d4040c100c004100e03c84c03d01c02d201365420381e19207845070b624041c10280d2000120300c00601303180f118107040c8914 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 145720953 1250 145719703 145719713
    0xf020109090f06060e010509030c1302040e0405010c080a020a17060118140f010f020a0308060303040e0a0b04050f07020703150e01090c060801120201090e04030c1709010306080316150603 82
    0x2e1100102c481c100065103414010000c0500c00c8101c42141000f005111a24403070340d0106001448100480f021800c0485c0440c0000c043c0c041c6d6846100080d0307042c0200030501c2819004806071180943d100000c940da03103d03c1c07034200d0049482030000511506980550005c6051056070402814100782064000c0302c0c0c10307200703080195003040c1c039110b030000d500132603906000b10000410642400c00a08160304800020b42c0c558001e82c0c064208002035002c6684d41d01c00384100c6020300100000c0080f42d03d02000444081c1490140c201d005610305000544a65000840640120b03e01c1c2d0280c28805e1554503502c03002100003906c1c0304c2180c1d86d48a0030760003100912031020b40c603200d078505003405442e10320060560307401640a912003400091070580140e038442084420b070703030310000840959212400e0466441210b800010040201c041d036500e46c2442110180003128000da0b814001580c40c0e007c043d469004001030408841d8248040e9000542d208001610b214602c400000b1440c2d40c039200c13 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 145722203 1250 145720953 145720961
    0x111030c0d08060402120c071704090507110a05060703090c0f0f0f0e0108030703050a0509030607031a1807030903300501050303090a0306150302040213060f0f08040f02010909 77
    0x403031a56128078207144805801c05030443d84a40112000c50900d5040301741c070b1714440c0e40103004d00ca4441c030001d0700d0b82c01c00014401c040303183c809000341140c903075031141c05030381c01040c054508002040c039540d00c403030003500009540448182e202003e041c2581f18060160040c00c02440c04a41012240902041c18402e000d560402081c801e01080d04447c642003030b01110700c0480d080003101460103030050004100001c102e03444e0300e50510300507036102c07141003040f01c00d40545041c8130b9141c0500001c1c8195a40c0c15000401c40050074207119a01c80806402c021200801c004110410b40c1e183e03001960311806a441081c00500a080002596a44110150300d24400da040c9440302051041d0300b0088000520030140908000c0d40110714098a9000003500c00905110080c2001d031100404040c548078000500d005640c01381c01551180c2c05542d8415404280e4012a03000039032050081491610903290510290080d440d240c030355071525203550383c241c82c10315000c6c0e041c040c41ca140069010250b201d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 145723453 1250 145722203 145722217
    0x605061606050c0301140d020607060c0201151e09020d0b0306010e0f18100903030b13090605090303010b1801090e18010e060603100b0f03010c0203130501080c04030f02011103 77
    0x2034400c018001880c00d00110341000d44001d4401c8018030060108020400d03800316559400c4030170000c907001c10301c002007040c855804020034580c18103480403840d580540115450010000d80521010b441c0c1007085020210302c1d405901c540b02038134082000003800d900604640217a040c0c04504000d9010100703207481c10aa220442e40580c40c0e081202111603004100e411950071406c0c4e0013000720b03c0c856550740310700d01d404003648250344102c00d5042502a50110508400c080c0404d00000710035600c0344c0c000c0000410544905003001c001503600d51010040304d050711105084d1605046400c0190908401022540d5062010302c0300049601c80c1000c80440c0700344503000840414801c0c17240392600b910030780c1782a10140e43c000d0041c08035565000c180c100f16884003282c00200d040002e400242d00403810850340d80c15510f404d10022940da400300050a040d900c481496440300d03038070300c01120808022210402c541009100c02d00008844c83c001c0000780d4014501054040c00d25080241503900c865 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 145724703 1250 145723453 145723477
    0x90b13091a060a060905040c0e150c15060a170102130b0d0c020106030b070f0201090c0b070c120c0501050706090b090304151b0605060d120513090917030a060506 71
    0x9030048070800040032070341c2c0c020740598a034001145820310180ca014030501070300d44107644801d01d81038071074400c07009401c0c44040240082607001c0c2c0018083c4040d80454500d09140c050440140214071074180c41d180a228041c18400000e4641611804200d003444c000840d155000c0021984880c036001300d1307001802168031140d55441c102034a0b04220341c151210442903904000080003c20303200d10910750300407500e040c810900c400b0508200c0c010100600020071080003a43c0115409401a0181c40b0152059440350802c0351601c0034002e43c41f80424009090342d00e0740e4018825944980064020780d840b520000c9003104d107130b83d1003101c26a4212074051a5a0000c00c00300b25601c2400b07610000780c4e80a0900c01100c01da030b80340c004010103042c9000b4104940b540c01103102521081c4084e01155003100507501d21444e0300c040200540d00221240c0c130380c8070640c140810410914400c180304241d00403010041801c1010030980e00790070080440e85002e42d11000001c1517101c040080c05e03800900 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 145725953 1250 145724703 145724723
    0x20105010f1703190201021801030504050c01050904060506031306150e01030609030e060307020c1513030f11060a050d14090a0308060103060807140a060c0b2e080c0109050613090b1309 81
    0x10466245a42c050100c0c1c8d24101404e04050001051011400150700f090a1070040c0d625000980805c0c050710b02540000e40281002003005840d0781002d00200300f0501c13561060003a181003084400104409008110417003081400400024442c1e034000c42101c3c0c4203041240c5d40070160000a6500d4100716859005600b04295285031403404034042d51a540c2d007641c3c9181403400d40f4010081e04480f901004101d035845034034460a005400202403c0d00310020701480e95001b603017500821682141007182d208608254418500d02c0d440c6101611502440f80108200384403901e00710380c25a009000c040c113059840e4401304442d00c052010502811803941034035807580d1107009024100748254840410844840b0905000030a28094680c200080989003602e140e0015460303090038601d60308400f09403800503c005229440031800901c5844241c940640341680c4806000c0e02c1c1c0b15100d000c0804400a580500090607203070700150304240e014140c0f81c007400300116020110760f11000203441070001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 145727203 1250 145725953 145725967
    0x9090c080f01060f0507141203041a060405010b0708090f0a09020403110f180405030d1e0c110303071b081813020f0409020706090c0f080c01020105010f170319020102 73
    0x48071000d580100102d01d006610450300303020003403290045c2c4200030b020f000e90703413613000403913104108024401c071811410a60300c0c103052800500f000c0010440c2041ca5100c0c00001d043c40c0341c648111030498482e410900e19080440d0fa42c0f2401d540912703441c0f40d01451034090450039468140d40580500708071040140e4490641c101f01079600e0100780c40394401c0c03840006d0140640c84500c880a814091075102e1a11a02d851414904601642e860085030510742040305805042c06540941280c2401380c4c100503072002034100f2244101c003414440040d500030000714424520646051b607405d140d500304188905030300d54030000c0f16070169540d059080c1c2411604402c901d480c114541480114000852a205800f41e845040780194030410170280e9010800c0c4050000d03582241075204d50180c0907680310b070346503060301d401d040e403e004041843c4505461454594014420281a03440b03200c1c6200d0b49a161600b074840c05541000007014a010902428a90300e0070b150602c81135020070340015888501c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 145728453 1250 145727203 145727221
    0xb060a080109080702150f07030905040605030a0f0215070f060b0f030609071e240206010b04080304090f09080a08040219060806090603190b06040f05040308010b0a09090c08 76
    0x401608902a00e9160041000000d40c143c001c48046640c1610100540c0078519002c22050103200002c000016001401008140d84070344244140c1c0c00446007080380310380f104140b42d500c40a0000c002c010703640100c807070800f42c0f4100d03409182a81d0b100c9102c030329000003035550103501d26000b0303030440d200c0fa00c9405144061400304107040701500e0a034020840c500e0f020841a94903c024030a50418000041007080300d19030180781c1c4006070040881001c6115148114a108801c560f880d82d00113010750380003c141a40c0420898040380c2044000754281400c0166020003000a1035005c041140c0c0c0f00c0d201400180034101900180d0080c0e115071180f4a844d0060000e81001f11400400e10211100c00b0b1103a02e80004440e60000e0040e5031161080d40c50b01c01092908555084c0c0000d03a10040000c1000c01c01d0790020f00384900c0d0161001c0c00b007151150003500680c1c5007501c005020428031001444045e80c03402c003801c0160794902d0209070aa40c1d404545040321a14015036000850394020011440 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 145729703 1250 145728453 145728469
    0x4110301090c02150a0b010c120f0201050c09031f020d0e07060210020906030f0612060126030f0403030c1b0e040308060a030c440d0815040b03030c01090b06 69
    0x802d00e4000780c41c108194180080c2c81d05402481e01d00c07255a12a4034030700e540d1044000b1510a50711648102e40280311182c00f400c1d40b4074484c80c0e40019802c00c000182118209002e88032a004090001d0240c008150414945103208031098030080b9420b20010049030150b00070f600b1901e13a6600500102c0d4200743d002421311022202041c001c9004000c3c40725070381c8402c3d0449511001342d4110340c51079141d403000a26465002400b46c5400e1289100204107484d25403000090601d000320700f501407090000b030481e102e000c6c1c5a46070016020901042000c64000c47d8920100f41c4520000c400c002401c401c3c1c840000c6898029031b440c080d0801c10402010741149855400c24030807240721001710703e15a617001194465029042d0161400b0421310800f9a00e0b03201e0104090640360f0481c4101d000e22000c000848010f489118140b04944800004a0107140c69034028400d10140c03400d02d000100500024004811101b40c00d0304c010070806840750001e1140b0780c1c4c1a40325107000c03141c60410008102c904 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 145730953 1250 145729703 145729721
    0xc1505010b03010311130504060c110606060301030b07110102070605160512060609010e090f071b150213090221010b090904110103091a0a0c0f020c0f040b0411030109 73
    0x46864140140714509600c01603034112a801501a00b00e11110310100c0c030f1040046458070030144c14042400200032050300030000c035130055940d0b5101a004008082d9071074200352100e070f0b0810070420061011031000e508040c2d01034404d007401d08485c103204a00301e089a21051060320201d0723a075010700048602d0b41c46140311307502052515900344070703114040c2140d850380640141d21440c400140c58220344d01030028100071160051031036100d803502c9000100b00501c11a80c0c1000100c0c103070b0f066285034400b2556600d0040c0c00c10300c0c44180c49009843c410084d8045800424420345403400060f94500900082800c15101b60b80c4541c0040c68114030000c0303840607044280c0080c0244900150b81c0c540c82a5070b40e20580040310003100032116801600240320004002d042d4920301070200d482114803418803401030301f201c4810090382c0b08403c4100e60340780e10082c0f14030050b00f004036050510301d0940c0795191040d00003400000c0038240440010105c0714415100703100544040010003400350a4030840383c0d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 145732203 1250 145730953 145730993
    0x605010e0105180702120f0306090604022d0f0d0c020606030f0c01030b0d0203060108071d0105180a0618090311030a050702120f01020a0816020a0206090111010e0304060c 75
    0x3555052400140c3c01604600101400041d14000112030030310030058113118119400b846a51400403c0c02c0c5c510076402120b180d80602258004141d1600b4580708a400700c20b0a240010308080f06034480f081c000e41c3c0c0305451244a101132240480840066000309040c090b022400200c1e40700250019003080c0c1300405081c8203410003500031680310004a00040084024a40023480119500005500141c0c0c081c029426114442c0080781000d0001148015110410084480402c039041c951081a40034000c9a0300100c0c1e04880000c43e03e6203080083e0011f02c1c0c0315010401d5a21182c000c03182c62104030b10381c422a500d80540c0c4051503000682054404803c40c095890002c541c0340c068258412100004d0103041c0120b01448242c40c02e101000140207240300a642d504c106041c000c00c900310a0720920580d200694541c100c50340000b41d24900038bc0d0180019041a0049005607204c680342c0c8041c4d410b0b5529001e500381802c80500040002e4940d5441c1c0310719007410b90034010345244424640a903 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 145733453 1250 145732203 145732229
    0x2030106200303180304080118050601090b031b0d150501050a170c01110f010905100f020a02120a0c05071701051609032d0c030b060618040b0a0b16060501 68
    0x50303801d0120031a5400240402440c8082060702c01c540d01c0c40c8a160310002d055441d0024a61301d5505044203c0e44050144085a0003640c0380c58541c400c03206180701455056010500d0b144203c01c0c0c0100210720035500800d440c0b5040466110100500da9440302020303039640e81e1300140007a00c0c1000740480075110358007081643c400410744650340c0d81c01c0f00f10418117004d000303024130503a03080c100641801c10100000901078803005182503952690355141402c4414140b132550300c0070140c0d92095400c040e2060b80244030380401800f4003000d550200c0300780030030403c483c402140400c02c1008080000d0030481003c0e2503442104210a0031541c019002109501110a0450a50398003100d6041a290407403004189046020300007002c6010444210380d010409641c040c09009140c01c3c21803c490091420700030b00da6958080203100d104401907420040c02c00c204184160906502104500c20040e04018401d912445c100300c8070b8100000360100504005519010046c0c0340c05000c1c01003100d01d01d082 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 145734703 1250 145733453 145733507
    0x60e280506060d020a050d1410020a0f0f03060801090b0a051609060e130c0c03090b0301050303121008071503060e100902070c1a0711030a02011b030509040f02030106 73
    0x10344481024000c2d80c440c00040a0440a550320b0015150040800500640d1a25203510b40210100784800d01d4078a10700030007168926043c01c1d03001300c0e80410061703550842d5492050200f500d42148050b0f0203003c143d0303243c40c04107154400b4800c03113018038040c9455003120301e00010b080050700c80052180210704c842d82c41107040d01d17811800d560181c40c070500300f4481403014800418034221120160400382c03420540e008058a40001c1c4440e041402991841030704c9480718408a202d2101303104003600b40c1d104122484006c003018500d59004155080240c1034180d50702ea056240c486190032140d40300105004440786c1c190184205070041c6902a4150703c00c2c50b1520100107415407600c00c000016030001039210030082058130700d03c09000c1a440042c5030a0380707860064001d41000008a0700981c8054504501d0701e4002035a51078603505a59019100c9520803180c2d501c0320000c0c0c01102401010300c409210383d6201e0044200d90f04895100584942c90520014606039401464600c0c20601d06020 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 145735953 1250 145734703 145734713
    0x506120d0c032a11030f0706050705241801090305120a020904060602030a0f14031609030605070806101b0204180c230a0f090b040603060e28 62
    0x36031442107003000501c10400c0d0500f5114802d88000e25a08000358516002c8240d81e407100640401d030040d9030780075407241d01409265072040302d8411108280e1086004000040c806e00c02001185d1160301a01e0305441c1c522501400302000059000c0e90750300e0082004101d0104035511502e1a11010092140c10041c0d00c02400178400c4074103002c02e0592090020381887c40b160106c502400020304100501e640d2403100944a0300000404000601e6000c100d808c641c0c1f01f03a8080030b00b00d040c00da0252544e1164070300324400c141900a18414019424000800300d9400c1c85494490140e51700c1e81903080c64600204082c440e10201c4800511122892203600840c181540210380342c0d0649002402001131900d0205100741460003e01d445080d1401103445140908910050320307005000400e03003282c402c204000c04000d800707800c4010040010400011100d0b0b0855208420090070003d41142c807600c61806403964084906583c2c0e2002c8804410f03980740d441c0c1c0304140000c55440d544080415655 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 145737203 1250 145735953 145735963
    0xf07022116060e1b1c051e0708060c071b0e060d050718020d06080111070303020307051902010b0109080607120203040206041e0905070503061f030e10020904050612 72
    0x15079410074040300092410080103603c0051074100c06400c07103c0722130303508000c690504031040f5014020120403a0490703902c65000d50038180c143d40700018000c18902011060035981002131000400d108003600000c050205021060140440c0b00046613a8501402c2c039043e0154030384100110744100000c00c00c144115000c129410420031100680e4501c0c0a040581c500718650300000c0310605005111b81542c03074075500502107495101d00600070715a0324584c0f20300301c3d51514a0f01c5042d1000308500c0c8006807107030b0300440c2d10104600b00039003808000030b051000c07070242e84200c2d00945e541d840011619a0841c500da070091034a040180094034018a0040c5402c10500c5490304454012004c80c0440d80c1e0201030b100640b00c542105c8172908034a20711101d80700aa0310880340028541008921144d2007202145c0c407d61001d00000c0d50440c05084d9040f0300c0811400e40d508161740d41c0d8800c0112034003449181d624501c400c90160320340c419032041108969010740004c0c414050419138900c0507001142c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 145738453 1250 145737203 145737217
    0x120c061e030209030a06180201081303020601051c0b040c030b150a1e030501091a07030501080d05090f03060f09010b040e0a080703051c0207031407050c1509090f070221 74
    0x7a01584458203003000c81c5c0341801950000b001e550811340124007004050840c1406113000340d03a0008140c031143c0c0700f00350b0000340110190044e003000005000030b0400d80e64200440f02007003002c403846040f507110b60140130010b039401c840580b8490401c00038056143c03445034010b410f0b4001404103040c82d1001824940b468420b400c0305000400d04807052101d01104a4002c640000081c0702140311445c0480011458900107a03081a01e0f04c00300c0d0103d40b19200303860580f2030a40c002c12280c4a1b0b01d00554040e00009106070380300031001c05881054609200743c40c00748104542003c00c1e424100999802d40742006c2d0300c940504e01e00360340580b0b10a40000c0460700785030481c5401d07a44100e2403c0c1111148984595580da86070010100007000321140d00800d0707070302d01070395a10400c06400d04600083d407250305400f41c2107034000d407541c10703035442c00310510011548030801c00d0341782820b040c000c80c0000f0012600d001d800300034101048441501801490024103d000320030b9000720740d64a4900381d501400d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 145739703 1250 145738453 145738457
    0x6010e10080a060906150207060801061b0804210308090d02120a030e071707050907120506120f0105011406040303020304060302130909050a050d140a110109020a120c061e 75
    0x1011031490b051907400b0340060300310398130148072482d112146c4100ea14601c840c0240148103140b000900b41c0d20070826a41a98aa42ea44040a42e1007140245c81201040c0d800d80b85224100700014007460a07040c81e03011101c2c501d000a44105560402078415080180228010740244004150031780d0301117000804058446441604e403080c0c61811802401c00c0c0802c40d59130700c14403501299902560702401c0443d003c80e070172115950b4880382441003202d81a40e41c500031401941c03c9001406d529000b09a100f800644840c4881c92010416032030280e513605450301ca03035901c0005001010041c120848086ca082d1402c5140503d07541d0001d5032031040d071107000c003015404a00641d1020b00744049400a0201103828854a016818401d44408808004903050311941031510716450080724946000c0310f88400c0c030342c1448540c007400c0e07030400c0700c00c10441c03102d550350100a001690f031107200304050003642c249100c0c0750071180341c84140a00345400ca8800e0298501d04441d4030154254121883d64440c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 145740953 1250 145739703 145739717
    0x2a0207061101060801050f0907081b13092a0b040b09010c0512041d130804050d02040b0909070503060f0c07060e0f070b0910090b04060302130305070303020a060506010e10 75
    0x41405a005080030b1304403118a50034901844039801105140b98020101c1806661041d995821401d980d1002c80031008881002030320207a01c580f4100c882544501c1603500041451601d660342e0300c203000401016885941c00600d2400101200c80894001034040c28412515050820004019502580085504221305240c42c041040307801e005440c401c0c2a1041845d031625114500b0a0550028131a401d42117000c0d000000c40317031440d6261100e081904000310a01d02400d10741800103400d260078050ba00140c960104040781e8a0700d5482d244620514401340000c1403c240415040c908080e088011000840060241d14500d40080700c402c00e91040002419094004100e820300d13402d06075900240c0200f640001c5e403a55140c00801e8071303080c21a041400c00b0b4041805076502401b60140e80b2040c0010f0005218503400b07036006040c0f1240641d805013109940c0ea9078280b81c090fa40c1c0080340189c20204011003040f086004040e0008424200740c1d90710301000c000f040c600381d41c80c46228104569 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 145742203 1250 145740953 145740977
    0x12040605100e0c0a081509040b0c0c030c010b0f1017040303060302061611010c0c0e060d050304030c181107020f010e12010e07050105030403050f0715020703032a020706 74
    0x103084004004103554080d0078908401440c1113a0005082c41c004115050002559040c5010070403106c1c0100800410054032680c0703d0186c1d030741009004048081e03040254612401040000d0328864048500108805c6484030034840300100024259004e00c1c0010140701001f80c00c09a036151078043d000d48520903554a09048000e4401a80065045180040c4c00c050a42d0700c503c00003c250b000da5409200510700100450354403c600001a003036a01100d01448030b2041255295045000100400404030440c1c45007070541e4805c2c0d001300c1b82046080410860641c00301c0142c0245020000b04010035200d0881c40c1001784268017000703103e120100d5184600c1d80c0140582c4503a000040c00c04544d071440e1200359402071440800c000c15922a0304000101580314078100c0e40b085515503131f041e003040701d030f101c1c0b21456400101003201c21480040303803541c4056007840a480414080c2d540480c5940e8010003202c031403040c40890b038605120000440007a1500040c42da000c0700d205141c284090a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 145743453 1250 145742203 145742221
    0x50706020a090b071a09030a0c08030901060b04060c0c050613060807120203090d110a0309050d050a06090c0608090c0a06050a120609020415050a08070e270a0f0212040605 75
    0x1480d000300e800c901010500005011842905c28100010f661002c0c005031256034410303a0764080c00c00d810f00082c10798800c41c00020040806903030031402050012a40d541c80b0312006105070031680161002404d015008030078000004c440c01d0081c42c0c1602c4c154540700b081d501d80f2841540601074803003400401d00118118500c60035a809100c00c038040115101d060214909403900700c124245c1001402600b4038441101011030004002d43d4180c55240c070705460b000c03e001080c01044c0d01540c0da4041c261541c004200e10303003d00307580c03540300da80e00880080c10041c0251451001a205403130710740c441c038000070442d100c154042c0140e03249828540d844090000048510f03901d54211405280d0601ca40002c903201190068801d441c0c907012014458045200b086030345001d401801800910340c0804180c0041c0644d908110501014040c0c8006a000c01006040140c145503500c1c903948515040024000e034611400d06002c1e1065070561030102031003c0803802c03060140010303041c0c9a550000c105000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 145744703 1250 145743453 145743467
    0x209130503270907030c09140a1a0f0307050405090106052d0c1f18051c030209040c0c030e01020706212307091d040f0521040305010c0807050706020a 66
    0x940180f25562500d000003005010301041c0340d0680c08101200c03008141da84139480c4580125a01814044029143c500c01d21021101d07e8200305407500204001c10306095441c00540c8210010348440b6038451030002840814881603011200704403043c071003000f4441000a4110703114000c517100c016086800d00100301a8418040315196521a11510810400e00a4403c04504500c4e040c100901d8541d8022503c811809400041090b0001d1740814500d402481592141801a14005062400a4001c10220303550107105002054610301c181081650000c0c42c44001c2d502840907003559450700001911610b030780110400c000b0340005403408035503801d070f001c907243d000c002c4c107023a10b01d188048040e03480340e01c10f894540001e4101c00e00882c11170b8842c20074442c11107038100041290354454882458900b036480040b98070380128000e41c22410130881c980003a405400450a55507440d40c64500c0c2150700140702e22003030190110410410300c0c1c215003501c5d500b6401490160380ea040400040380c41d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 145745953 1250 145744703 145744777
    0x5040309081f0b01020109050d0c05010b0a090b030c01030b030a06200301031b080c01080a02090117100503060609091903050c01050703020901020f070b090d110901030803040209130503 81
    0x500c11100400c14518202c000100c0d500c04684080115080b810012800e8940100c000b070480e0b480b51500d0b145851047d00b418903114041c070000940300e80380c400040c1492001d640080b1400341c641c06040c02920703050080b8070751001c003428100452802000071a440d94002c0700050b200d566100780b1450111880d0302d030481c81d221030f0340f24165250b8491404042e01400d00342c140b010040c00703031310100d114000081c4444144005844489060f6613904611020b03600000445042080c0c01c40710020248210844038019080c5581240196041200b8507140410040c0010b210310500e0043c03150040c004103c212036002450510a4500710600341a540341c4180c07423034006550300c0c01e010400e0455240d40a0041c2000036801e598040c1040c010255552215000300c640c0080200a2042e072494050340315404103101e103000040303820f5042c0015850060907801030b10b0140e40002080308600d0b210401c0c56107d49007264060b940b0a03a42c4903960380340a9003040d003054580d10300c0441c0c00606404501818 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 145747203 1250 145745953 145745969
    0x10b090a03140f1605030a150b0a0603050a0c030504020901060c02010c05030d090c051207050108061305010305061e090615040b040507090e0a060b091513030b0103170301120605040309 81
    0x258212169540b41c00c612612500c501500ca03001c40e130814180c1d84401110001030040c074101c1825214550500d0140c9186120340c1c0d55000700e070141d5207030030614034020280398500207503601d040c080232015210351552402c10986000c0170080140d49400c1100d06480562610700c80c1a013040c801a1070074484424090040c0c0f01c040740c2040b103c0e03030a81018000e54400c02001401941e5035050121601e010b0192100d980c20500050010754421580b1035402a0010b14291003945211072240850768280c10a4038503030418030420154440042c0b107c41c08101f0003230344e0545454030511031505c1c0c1401800040c9141083c0b07071840d04503903c980000480703140013401044241880f15000c0d00318007445c41510751500440c000118032442500c100812141c0d480c0a0134a400c5442080000b0060003010a64010b0340500c000e01c0c4400744500f02c0006903114101c0e03488594150b0802d080101d800582124650700104018400401500a10340e02140d00107000300b65500c941c0303001d03034490782141c0050351 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 145748453 1250 145747203 145747223
    0x90b0c01060302131e0b09150a091104050301060501090518070e04141801051e090106080f03250213020702030f01020307030c030b0306010b03070c030207050907051c14010b090a03 79
    0x2a1341c1c269a0000c2d40c80030211030225031140907440c4c00403d42d65400070403030340001080b0005521041125205485440003415400400d465001d024205d9200300b9500b25142c0000c1024041c0742002d208080140c142404c145e1071051924001500000d41e0041d03102124542c2000704441c2401180303102448003004105012100510b044c0c1d0a08000444041003002c401440003e02c841062042034000da6174040751240e00020380c01c0c111030001c00a0880c2240703668845001035090001d00c07561500e501064040c660380e000c0c1422a180c00c00e055407065899500206550340140c4c2c40010f03180846428030009a01c0355414000070b410851035001007502035000004000500c3d508d64809240030721035032000c200170310007074013410346d548400d000b224960300d002c10100760b619000d00092889140701e84112462903442d00003141041c401964048003185000c105410101d004a42c60040304c2503040c002c001c0c3c80c0e040115040c4a00c018800d040c86e41000003082c031016202c1d00304100c05503800405c100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 145749703 1250 145748453 145748479
    0xc01060503070e090c15030106110a06090507030209091b042a030c0914090403080c0403050114060117060904060b040905060c03040204060f0308030a020d0b1f020f0a03090b0c01060302 81
    0x50004208403415441c4c0c2c0212200381500d8070305007407140751a074507001d010b5003140c0c03c0200075074a1044030070000000c4e2107140341000c001a801e02803c10858442d01c00361000610314810300c290010040c19400042e009680341103032100c103694042c1880e0170100d5000c105200c104103042141e01540340d110490b924900d01e8004483d0b0990808144e04141e5611240c81c41d54440c11054001c0004085551001d00000820701180c820f200203600700365004e034400d2906580c0c1c0d6995084074145800c407141c00c0c0400007004829030700101104e00580355034002c0105407400c1d20010b040c801d0020802448182e40350014140e9440b035034006101c290f4440c080720380d0b07424080c0c01c4240c242c00440b0102d12032818032034045a9031900341044411203521601c420705503111100c0580294100b610036426195035580001301c5982c8500381855030310f14903000002e041d03455040c003c1c1011000c0d502c45249034082407043c0c00080d030100c00c3c0c0c4110380e20341d491162a03a98014005000d0080707940080d501079200d110030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 145750953 1250 145749703 145749719
    0x4090509072102090402060a110616030b010503010e07180b0a09050f03011509020d0f090b0702010c080709050103090c0f17190b01050d050109120e010921080c0106050307 75
    0x2040542e0500007440b5921030304210000604910301200030340040d400e01c0440c0050800c20050305401025040c801403000050012528090003228000400d0008104405042da09489a00560a828601140344d581024810040144040c14040c02c110244a112110401c262a0000501401800d132642c501d078048004240d0171480c02503030700c174a0103040c2141040c5414030450b80f0309c5541c9000b01c49010300e40341615000350060440390b40c2940d03c0c0c1c1c0024801e8a100e229152030144950f040b0003280c206207100070f08540700d45180406101c224030503c480c02d42c000c019801114024070300410240d6807841d20340f840340d103207134414100d03106900d8010922440d620490510241003104035501402c500300703a0340c203184800308050021008800180403c0c05d001a15694850003000046900d08455807060344409464000c840010024041e842d01da69110020078020800480012500b0a207d03030a6880702c030550704000c0200500207a546040ea8003900140000d060003410b595440b541e0300c070f02d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 145752203 1250 145750953 145750963
    0x528060e01080a02040815090109050303270c0306060613050306010305030703020f01020301050a0909030c05060c0c010608011e0506010212070f030801080105131e0b13330c0504090509 81
    0x80107020a18640002d40796990a2003514115558000201a80c4248002c140300c1114007400380c511075520b4100721008550100000c0d40a41885580e1110031000d007544248002d02c803c004694540000c408240130380d40006401e504558115032044c0d941c028090090342c10b0342203500050b0103014050000060010120180c940b190007030302a6001a5030045a0758200e02c824080d9036441080c400090103000720940c840200d580c4241030060002f0226241c603444d01e0011244070074054800180044107000a0140000603c007102c001d02c202501c0741f1985807c2c9240110740505190f44800048450780b080041116254a510a41d03540318103d08180c1c9210384008025004500d85000000d0310040501c02d0510031840194243c5643c01e2584d038a03441c1d0340d00100081000741c041c0000b000810030b25071146007c0c00080450011204940c60000c442418266440c0b030642c03116080000031225000300640005a4490005607811024000f0384550042d60030074000d640c640000c11084484c0029 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 145753453 1250 145752203 145752227
    0x30a060905120310031211030d0507030e12040911090a0902030a1803200304090e0f010b04060e0f0703060e0403080906060f101b0f200105090604052806 67
    0x90342c84240764925640300510056501140c1c00e140c0308020408a0000b071380c80a6201d451b4170b440307a8003060015001c0d01c1d5400c181003020807117603a04240b046842c1c2503ca4040c0301d44000020703148080c01904050540e004500c102848a0307190907800b9520034031a01140c001d03c100410a01c9440d0f140c0303076020000c0d00110f4001040d41d142900c0c00c00b68071000c0b80a01c101c1030341641e50410361907404c0882d031421500300c10b0440c1d440c0310074400490200d00d10700034226082c0b10940208600d1304902c003003500351200c0e0306000b0301691620009101c14040c2070007480c0c3c003201481040c40c45880b201d40450040003254030009400c00c0e0b000c00d200c20598440c41060044e10003c045501980310a0700b04079288800010083d44224003441110701c09000f032902c6000d1031041c5e00c2c1e6043d0010b0030340342c500841d414100b08880c0c54910301d40f6604801c840b000580c8420100386480390414950001066083c800c3d40642481480b00607000300300134669055000c44040c0081c01c0303186490303076100301402d1007003004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 145754703 1250 145753453 145753463
    0x5030f010509040b04020103181211070e010503070312020a06050c0405040b121c090f0608011d07050d0203151305060a080a05100c230909010501110601061d030a0609 73
    0x2a0000815290400440f4040c907000304a03007000340c48540c0150001d01045801240e00c2c2d200101070008161000c10504412115445008110762030400c018244805a004444c01c41c641c94014080c580300022800c1c10b81e0761110203014601c655031826032400c1c004500040c0102d041c50704012540551070007800c1201c80030b94050055480701810402244a07080e80038411b0303445100c50f40c610920584100c038001ca02400e2402045807034a0307030300200000c2e54002d440481d03503280040180c0c0c030300c1241c884071015098501c00454240b4070310003400303489080340c003200c1d5a40102c08142032416a000c07410b05060020400d403a005180f6140034041d1504541035446405081c1c80010790741000300d80220304691040c06040700d0300c251400d240080402000301010043d0443c0d0710744114489442401c2041803d460043e12004017508002c1c0742d24050308018104482c4140c2084102d40002e030003810744040b41000840c1c05800079402d00565002101c050f494031541c5141000d105080d4008074400e0700603 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 145755953 1250 145754703 145754731
    0xc05130b0306180c12041b06020f0a08030711100f0c0f0c0f060204050904080904150b030708090c0a060c021003022b0b0a08060711010615050904020d020a0503 70
    0xd0340400c00c2400126080d5030410480366200954100340310016074001c02d00103000d4140500800340340c080c0d08003242c0440307201801c2400c000c020242030820a0042a207031005000c00790541d00740300d8482401c0c41005007800004008030310441c2c080c209624055014204489004100d82803003800751004140c0c00700150328250baa0460107110300510004902a034941d0000d513003442d61038085401380ca00f003d64a1690a00021a0035951109c405010728003440d126515111007000b004201ca050510202c12140710701000c02160540c0025070368014107134200032001f80c2d0f03500c040c0360404ca001294030b507202c0040400031454a030070101c050100ca0080d5400690155a00015001ca100d03120012330341440c20000746940038030002c2d42100c0824084e4020503031314540004980c074003050707822240440d0405402c0100c0c45520a51150701c07a030800009105407890400084c51042c611075450003003000c0003030180005d0310355804807142c4d140c400b2070031540d03110304400c02040c43c0c1007620b0001c1c0c01c00d11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 145757203 1250 145755953 145755959
    0x108090303060a050609120703150e1c030507090f0f090b06040f0e0405030403020a0306051e10140604051003050f070e011422091e06080a0212100c0513 67
    0x8000140e0340b156101415900c0c030181404104086900b02a480c941e01640804803200000414040b0314002c40c07184020111043d041404001659030000311701c0901d51220151001c0840382015014048540303040c0054103464513107013101c181810350406000f0003106c25002036240ca0700680c2c02d023210a0040d080001c1d100c154104402c910032486901d2130640368410078800014091070b0290003901c14011245842c0e41ca901103500c4041a500c1968907039501c40403c6454890024120801000e00101c1d03030b01c43c40d01201a11030b45d145800791045840c0303212141059901c3d0030040b2006400010004d20301891f00c5003000317000d0001101d0039070b000e00940300400d0249001710301d079900b9440140c540055090344840314050940000040950002c00324a0b146103002c60201190041d0003065004100500c0e54180104c0f040340600759480c2e000d1903c40108100f000201d0501d0021703504a4102040c1085c1403685403804418289100d40d0600d08100d00040c9500800201042c1e1041e041c1460080d035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 145758453 1250 145757203 145757221
    0x8070b0a09060e24060d060c11060702031806030708041104060902030405060406110408030d050712091208010b090328080a030c0818030d0c110d030501030606090b06040312031d06060108 82
    0x10003030303600f46c1d084030300300c090500010800d4000d484400c4403850080c803044110b150007842e1201c1998500003503017000506400750300c000003a80c1c1204000b0384503249141012403009204d044010130107403032620000c154030318a940d0303174210030010b003414482552682003505210b51100d4040d5030441b00c0518010040c0710385010340e0240c804a40000000e5410a0b0a2451400252030018860020012551008100d410b82c500c40e000c41c45008a802ea0302000e40c1680150000c88181c10691031507005001d6041c43d685c0020f1a001854009002000c0002d610b00440d9602008500300a01544d800700f401289158154010005d0580566400c685511040c0c107612801d40c40000d0002e158104000c0d41070845940e4100d45004041c51501d0360104140c061411304260303094130802e0011f41c64100410620135907006c1c0902074501240c0800110180328001500e9108910005003a05c6841c290304038003a002c0d504c800c9070f044070482c01c0c456260b4a0882c842e1500011030340e040c0460400320128080203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 145759703 1250 145758453 145758523
    0x7060615080f041b0e0c070b012405130323010f09031e020a020301020a030209030c10051e0408031603111606050c0109060c080117060408070b0a09060e 67
    0xa08206180511620f941e140c945540e10f180488051556080c0c6001071507200075440d40344510990004a0b0311680185407501c408041a4021550740c0900c89020b40030707214030000200c49065030700700160340342c100404201510381c1503800903240316000d60b0325100c1200300c60700350440b03040d002000b0019a078181c0071f080304546051501a000602d140328040a1164034442c01340600014011074000301482e81c006820380e071100201100103900815038065038182040948003441c0b084500c0300b000064410000c00c20700624401c0c506005020551a01c4480c4040448006c2d0140b0307020360703075551107004480d00440703202d1000700e0004003441414140c004010070a003000503400c130b003012040c074a004401c440d1500848a6019903560707801d100c0c000100e540c400c2510f0a41191200800303076140261b80c00c0c0902d100c00359403070160011410480007642d901d0440300c0d590380c001581d50749525610f040100a003c040401401145800728502c0c007110000b80308424110320381840c603d52017002d91400140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 145760953 1250 145759703 145759711
    0x20a0906020a150209030c040504060204090c0e034908010b090d020906010311070b040201021c0203030601030908040e131b0b0301090f0902091f06140a030f0e030706061508 76
    0x20341e5540f0841241d00150340041c03d03003401c02000c031101c080c00c0380e00150071644190b070101d07001540000d042020031660b000319260380781c1d1130400d05000c004000107e515402c01014280c080b4828140804201c905200346010441e008242c0050b440030070307110654038451003441e810118000c0000002c42035068000c940d402c0b2005840c4840002560f07081c8074032588090f140c24189a00e03043d08620041000c0003410101d4014032211070310742040d0001905143c102203081c2c240201d41c0030010f40032500002100c0e0014800e10b4005040407050804030840d0090350060040744048400340300012481c0034010754507502550701d04031031380300380c00c0c04016000041c441c00001c04800c1c401000351200a6104c42400c1c1c031224404540800c403980003625941c01150440b001498501101110101490115010b001107040681c80c01460003641341d070500429400c0d004140d01c034000803840c02c0711604a90100c6142c0c4046984608403450604058100c0c0e00501ca51100c150409100c1070f44501001c60203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 145762203 1250 145760953 145760963
    0x13090b0a080d0c031202270909061b0d0e0102030703060506040f03021905100f1b170304030c0602030a020903010e0102120103260a0c030e03060402092e09020a0906020a 74
    0x1481e40d140e816900d003040f1410940c1030040d50142012a41001d0008000e0701280184c2100d04001400581005008852000303024030405c0040154084000603580d401c04101031940f00654454003040e480ca1142064464000b030602550030043c1c0c1e03054000d94060207458a062080546650500c1202d0195101e102c0108510000070800b60400712400f05d180d400c0c00c106c59a641303859074040f8280e9401440700d800014903441da0320a09a50000003964104400c0609402e00c03580c0380c50301d4a45070b81140c01030040300d038000041000c142c010484940c7c005d6008070155102c0c40e020a07444002c2d000346290b20300075400d1a10b001c07240c80c07040c400c40d20f410300707610168251642140c4980c64144a40b582040c40811081a2940b00700c0942c030182c44018215665904240d20600c2c005003c01460109240240d006000740700040c0c0d1400711366548800485a1048484001ea0002c03216070500046100d00303495004021540c5040364004141190482e260800000d560344000c03a5503416100011b44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 145763453 1250 145762203 145762213
    0xc1c02100c12020f03060907030e0d050a0c05010e0105090c15180d08040e061f0f05090a03060509151006090b070c050301020a12110a0203090d051213090b0a08 70
    0x108031a5680c00124140c0d01d91030010300700040d00002404980c00b1104800c510a004000c0080b985004c4860948c00b0781540b805101912108542d41d507184400044403083c01030100b68030305454030072440d500d100c030340201c020b22202d140409540e00800d01900e05007514020003002d00e840b03080224000c0395528405514515101403070b00b4100e0004010792907144d2141d003601442010600304400740002d0040302401000500b020407c100040f814010201002c80c06984680d00306c94100c049460031b641d85040003079450700c6410008151007007a410080031189043c0500c11030b070000048001d41c0c0f07000007060f09610303100d4812094901440344607040c0021103102050100700485005400c400b48a416a8100c081e20340c0d00003400c0e030304075200c100001000003906100701041c0e4000c040d200403914070403030329043c5814030007500c9201c0d012020740110400700401701001010000300000e54408140c21340c4072074010840f103004081e1031040d03010050420180d02c9091034126151802c940588000700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 145764703 1250 145763453 145763473
    0x9090203150718030602090102010f180209041407060c02090705070c0303140706051807150504031115070b040312060e0a2a090501080903031003140319050c1c02 71
    0x440400d00040c0307070b082040000300001c0451441450700401541c850b0401607100c04440d4002800c56071040c110103955070402c000c5281d120f81d0140d200703414039019101942d8540d211b0500400317121a001109540e07100702a00002c296a00400b40041c0600c00c5a48044503129400300b141c40d07004180c406030800340000000c10010703008008a03445101407030059070400b0f040c1d464503c1114806c841000964100010314009800240520005808110300720b610410803010300520742c0c0580c2c00700404945c02400c01d00010f9031481e500362092104107416580e0341a0510b0b00b41300c0d400d420303107040380840d501312680100e50415011f85404c1c0e40003414106015521000004090003080b407041340019400580508090032084565401010380e0b10b414400c6407928000416001c40240342d801c1030340081c030904c140348a500030110201c2c2c1e040150b1401c401801c065241c218401c42038154110702600c1c9016400340c1d080b0026004903601d10081d0f403010001190600d0f51440d03e4a402c00042e080740e1500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 145765953 1250 145764703 145764733
    0x70803071502070c05091b1803060a050708070c050c030a120809070b030a1d0d090f0e06030d1103041206050621120d060315060f061130070f0c09090203 67
    0x4154400d081071f08201003e40000c503c10f8a076800016201a002c5a10080c0f14181c18100442904456440740400051400450040150300701810800070401c0211202c014031500304540104040700800381c80050850f4500b00044c1c6800c4c414100106200390002480340343c2c04600d41c02140c10104a091959865803004402854004101c81e0410001d01c240318400740c040001c0c010348540354030340c81907850401d0241c2d800903d59070301c074181e2000c256003013200c980c4012695030140d907118101304424100011010b402c5000b140c020140111001c500c0b00b00b030024a4100a001c1e86041d26a13100c0041ca81c00040d22420300c0c0200c4019690003030201e400b801c1880801002c020a4410b0001a003c0e101e0740d42c09011001c5809041c80c0035100c000c107112000c41794001800900b561300784204450340c840fa4242e22a081c184692400b0035101c501900c04190340180c171200917084000d2655240e04a141100c0d0b0208104400c2d16000000ca00214075841240710709107039250004d00500340c44001e8615 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 145767203 1250 145765953 145765969
    0x19030b0403140f160501050901021602090702010e0d031a0906010507200a090509060115090605030702010b10120c050a0e1c0b040b0a05060607080304150e070803071502070c05 77
    0x2c400c009010401c00d01400b040c1810180ca5116404024038114404e1400c0150135110064010080e0b42d2040021a021001310700c004080140d06480c0d18400390b840883c16030040070003085c0c940c6030f0700800c8400100c180d815400324005d0b18840b05500c0f200101081800b21007141194000e01040c1d0420040d07020402c2454110030500700082c50001c806e045102080d0044015801100059281c5040c8603502805000450140100141c0d000c107240310200024000d000c03034482c00c001e200c0c0c000f022231181c904c00c1d00300380b100102c040c00d140b01042c08050014114460701c1100d149152030059407101007841001141c2007000c95030340d1161f031015110104040c40030000c82000c41c0d24060101d00000034005800b440c82940140360309412031170305114803c1540d000620051245800304100c0c00041d42050640342c00c075800c8544e5030003907905071034604010603501000c0031540c4181d150014030004000001c0850a220745000003440e010305840d80b0a9000e05100240009030b042170600c0b2500706a50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 145768453 1250 145767203 145767227
    0x6181a0f09040b10020a0317040f08030406060504051302011701080d030b01021c0305010e0726150a1502010b03030708070305090a03080f03040204052d0712050c0919030b0403 77
    0x10000900e02548000a130214003c40b078142d0140e0001e1996a09254107d400810b2045401170f01a92a2500c0d655140c400d0011000c0201b88203408804101805510b52044000e0700300a07000308142d007070944c40384030036810b035103400c0b030010300030202d00302144541c910300504a58400b001816a07510001c410303000741a00c5400342c3e0444c0b0078400500e400d646400034400d1840b6032078400240c594100250f400100500400080900001d480310264000c1411905c484e04500c4684070840741e1140718280340c0c0e038001141c5d200e0f4440081c1d40c021485c60a000c00c0328842c0c85d09500200481001d103428513480340501d08001d40302d10700038005140442c0c0100010840c05400800c6040407e44955400c08150810b00260203001804420041117040502c1580c2d044918203084012038114100f6820300e01c6070001d05042e08081ba00081500b4a00400d041c1560f0200f00c20b0600480c90b06004210083d084940000c1c03050600079030003400c20385880740d224180c030780180f0301e50290754a40d10140c40e1050151 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 145769703 1250 145768453 145768459
    0x7030c02061b060a0218060406090608100b12090c0f011b05070f0f0f050f09060409020a0b0d150e0405070e0c070212032a0d080402060904050106181a0f09 68
    0xb102161a00806000a6128802c541c400580b02c04803096855001a681d0f40e4841c0500810001442200e82049000c8200e96162030010f45660758184a500001140d620106075104049502101945c5548503584102444002c032242c0c00d0003941007042c030382540a84280401c01501004440d05041d0703403100d1500340603808a50f071442e41d03070401310203668496100042041001100348095841d98100750000e200495090708a90200e000044174400054a240e110340c5d40c9220200c110340314006032000a0019083d825202c0400c020303800e01400003040211040340700f1b042c0c040344c100d10610304c643c060b642103001091070909000da0041078110181c46003a84c40c50503c041001a99001c0c1403034512408040a1500da80c08000c2118404114a80c0640356101c990a00324800e180018001e4402100d49010580c0340c9950010031154810a483c3c0c9401c1410000045150b0340c0088942500901d114901510706076a501030384450440d10200b85100401081b00d030140002e96405400011002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 145770953 1250 145769703 145769737
    0xb18060c0601062105010f212418050c090702120a1d03010b010516020d1e020a0603020702011709101a1e0a0302090414010903030b090c07030c0206 65
    0x80300510300d0403100b60b220100240c10010801207242116075084000b0080c408140060b5040003244008140305010790030862200c0c202110716124103003520619260021600b0190070581038000401007020080f1203a40d1b4145910390220b002651601440c3d243c0003005030114007520001c20984c4d0b48050715140031885911003030360b5044901c400400c010764298454816000202c9190a0b4078119540150300c283d140c0400440180d07001000c5444500803e01000c528808900c0040c4261801e10b40180c12456101e030b103a4088401480559541d6000302e070713011303003050f5078020840c2648580f01000740024a44030b11013410403451100309030011900c405603000c3e000b016088000312106040c66201e070050710b200d43c0c451420301410300c07001c90703a02803118890707001c500300032680d01413446c0300080c001c00c0c0300c0b0009400e0000d842d1a095440d8440e0000380b02801260a00038050305040d0440c520031a0704101152140b58240202d4020560680b6900340014158080203019003060030118415592 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 145772203 1250 145770953 145770967
    0x140f0705120309010f0e010c0804030f11060a0b01031b090b0a050418050f130f08031f06050322151e0606080907092306031f02090f0405010b1806 64
    0x124001070b600c501161000012145200c50341c05082e521207403034000560749080d06000002e64007012440d40107800d4142000c4004410004903100c21140170032203403601809042c000711001030340002080300f06c26607040c0000d102858021100748008929480414002242000003040e00400b808951100703090050a05a0b03420740402909001e80b00840c85943d19810403440c1c0407500c200d642c102001103244102d1442594070380d110807008410180c107414020000540140032a0400d145801c010840225110ba89103000b82c070b240c000756011144110b03c510b2008403e804928004030035030700800520141c80540720790400a03d0821030606158801c0043c0142c229140e0040c007008001541d00d40d01146024040503080544680110341d846050801c0095507000d800d08000c420213188482078410f07160800003c3c50002c2d40d030102001505600b80d10b94044031706501401c1d14040640701c10341e4858000341080100c034000d010b0002d0100017842000b81c0c01604540c607040126000c0c1050346010701d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 145773453 1250 145772203 145772233
    0x3041e08040b070b0109050c07020d060b0d0b07020d1d0402070c050406120b0108151803040909060515030705010807030b0a05040501090518070e06090402041407030b03070501140f0705 81
    0x70040d00005902540041c0b600f013081640182540140710b18402001705081070f140c4e9128600c01c590019201e00b44001c41030b01403120756400103403d28001000b01036035580c689402610220102e0b00040540100354841050070b0040c4410340c1e0075070f80c8100101000c0c01160400009400c104c400782d8418064080214850310303544910405031486009090303000c85145815260464140c01881160304031211a01118003904501c0f5003000c20380d880905151048044145913000340d900185800741031410506c18051154021070294400754854507807100c3c15000e0660f910028450240001e2a500c0082d660b02e10030340c403682c84644028164206580e807680090140c030002e82000b481b0030b41d160140f00d800d0b401110384424034100e20015010042c90160700495074900108020301510810002500f159690b6110205000307164001360a80c0c202150000c00400b464101d0324081e22a50070041250340c0114040700104d503da0383d441d45400496060110075402007a0204c1e01c9100701461084048 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 145774703 1250 145773453 145773457
    0xa0804050c1003320402040c020a0b1005011e2001091406010602061b0403030e011202031e010f0b0405060a0e06040801151401081609051e04110901020303041e08 71
    0x2a82a5004203c28141413424445000640c00c00485405501500034802d40c442c0500c0f50701640441e1300150441401c00c0a074203060030098014144402c80c001c010f4000150805d140946800707030b8540c1c1c600703240c40c0b207040c80b4035403c1140c12011030a0b070751809020031301c401d07200c9950403100d0001003080c8804d070380d45c0408070212280d61121134000000500000d0750410041d980040c0300d102d02e280301f0407805544441c51056000c00b80420000ba03021401a9002d2a100c4001070f40b14041190340c0e140400420184810140601820441d0803000046050748206402d0994400103440d5250900e49810440c080c0e200300456030512202d000d0340304907581e070307079000d040141580c40020a04014200350b07196500d00c0d540045d9090070149c0d400c5d00e456640304c001198000b1560014140e0341c02c2001040d17a40e070340190b0090780e000b03021101c10021682441da01514040055805005c030106000031001a4081c81c1107030350042c1e000b0700015000c035488000c0040140401122012460565107509140f9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 145775953 1250 145774703 145774729
    0x712110d050304060c05070c090203040609080f0705010e030f12041403040f090c030c050a05070204060b0a030c02010b03061501051308030d0203061804150f1506020a02090f04080a0804050c 83
    0x8100c0101c1000709000c1d050081c00c1c44140c0c01d180c047d1070b140c0540d445109009041c0078440b0816804800501001440e0348800655500402816201ca44007800040154840c0d40f080340e0550800075242c2c5000000030a59841c4a049082e0600742000e4034860160900c0080040e12046401c11801c2905c010030700080000e090411900300300941400041c0040e15810013401d01010300c2c007050006120762100c00d0744d045403810314140e40d40b42c143c2c1c00050050300b407a0b00600b0340310702e000a500c140507401d0303030140340c1245003a0001d114844800c000c05440710320840d11203000c081030892441d000e62080c0e000b09025019044c0b1204040d8079002880d296410600134140119800070900c5401d10300460349100f00c080b4510203c035545003643e40e10300304641c60600701d0766190f105ca03108115640c0541000112288003981049006c2d5500d1b4025507515003844117034090160100030840d82041c4c80152403040ea00036240c1483e0229502003164a840010016a100e000360750001c1d200303a842506020103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 145777203 1250 145775953 145775957
    0xc120a02010c020f0f060c03060d0606090f0c050909060d02130e070303140711010f0207030501092604030308040308180615090106090501020705120109021302070c060302030106050712110d 83
    0x54100600b4000c0d00d46881c90030443c1e07655011a21601c940f0400140040e4001140c81381e5580702d44400700400c86081c2403140091916042903000300321301c40310354041e14001500d0703a001c1c031521481110541d13091003459200350308101610005151803c0040141020900c094a0b00c110f1041c3c01c0e8610f01140c0084600c003042c2e030450001002410307444400000a906c000717400340e00d401e036543d0f1201080310b00c40c401d2a0510074940d58402c0400c0c000e108a90003946c00500030301450900345010028000035880c0b0b089504640c1a003819500c04000a07501942e0381500c485400340c172181c500342c5503c08018103041098003417883c0241c501005004081c0901100880618500301420400000360340c1608504204030300b4010400c0240c3c3d000925030115a810b8940c039400506100056024040e40c0a01030b4100038408002e40c0170082c582c1c002c0c80300a0140820000b0726480d80411810307884203102d144000361341402901c02040d412889240821958103201c422125410445410004180c0d41140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 145778453 1250 145777203 145777211
    0x90606070b0c04090b10050a0c0302120c03030610141806251502130b070807062d0209090a1d010c1815020712030e042910080c0c120a0201 61
    0x104680381d01450182c480c040300e00c40f11280340000d0090548c0079480e100b4041048110000d000e060003481f02c02203a036000880540d0b00c001c0d0f0312000796a82c0c0141d03407c50080c181840140041071048090640d2424081c800034500484103d00804022040d00d42ea40d0240003000b4030320001000b00d080880300c10852a00700240000c030f04003000e0b42c10f51044504405c50041099525490f40760102038161940d10300c1007511a9142c0c18443c0742c03400343c6400141020319014100034004108040700540d4052103020403a030100c03881c0d051050b8060149a55040044000450400501030b000200100b10b03040b0507034601901001000e080d03841d900c80d214003141c6c81c214006800406500518054010f00ea11074080e4048880000d55502c0503205d1a401440f49041d010f04046c4100040d004084000308144031680c9224010581c0c3c0e0740c1c10040c482012400c00042c10309042104035090b00c010030381c0300c1c00550307522190340f4a0309031f10000d0900428042e800f0096265880e10015103508403480d0300000e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 145779703 1250 145778453 145778459
    0x507020c010c020303030115020a0803090705030609070b03240409080d111908090312040506010504050a1509020c101a0405061c030c02041d1b06090d02090606070b0c04 74
    0x180c00c0c90324003421981009401d6880c0390140e2400800c07a81182d09803241e4014040c000c5c40704030301301400b842c4001d1001d4400030600208500014941d02621011030079920039807034140c2000e42d90030281c0725050301303072900748006459207003918020135030070b411311841c9a0244010301c0000d08a800504040310b1428000c100f80c2e46022035031081a848102d8800094070b02002900c0c058210320040c03904000b044480d10000b0402d92090041d030340200703120780040c4120f0500d45426520b451003406000d009510b49030001d400036005000386030104c5461045916014100f0308210040e40c001150321b101407185070408000d0340f40c14401c0728070074848a19a0203c01046404100507283c000e002c0c2c0744140d0140c66440c4401006800c849041c5605003864080401e540c408500904080d0313000d42071081c41d00301c0c8104442d8010460018150b00510368490102d1480c04000d0b15000f0524200d40051080640c8001400e0070a0f4003a0402801450582400555a41e0140011007101c1e10504038901140030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 145780953 1250 145779703 145779707
    0x8030a02160909050303010b070201090302060309060106020d03020a1d12070602010906060e040c0b07021f0503270309010c060b0d0507060906020304051e04090813030b010b0a0c1401110d0507 84
    0x20b071800b50410b110700481038540980d42e0006008180720300e01c000030328004580c09045410003c5a02038000e07601c2c0e2500341211512603d00f40314001c0035000f8081141c4a5074130920850340240e182e07407601c490f44544001a802e4080c0b031403049a0700301600c6405281c201100300190402002c1550011400f00b8081ca0281c007503440d2503110048000280c3c0034030000032715583d034203000d507180c1258446c0c0381c100303d00000351131655800305180b01290640d56803070850362220003903200310a41d4000b1441030031007101180095442c81c55000741c0d41c006001c0d110080d0311a021103e16240140703004504407205600240408002c000f003107a441c1c0c0407c1c400c0040541104003a40140389a001860400f4501400714003090800d07030001c1e10001c01402c41841d00d41d19a40215841608400080e441e5910200d80c0030524107503020a0315804040c000001e824468030040f5659070b5415603c3d10741c81001a80c0d0300240c402d0344038650006540706d50f9003510202e504006008160340040020070541004400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 145782203 1250 145780953 145780993
    0xb0a030f2a03050c060c0c09070210020412140a1106090d2109060503010f0504020f0d091115030105031002070f0b040303020a03051311010e010302041d040308010806090c0904020a08030a02 83
    0x80c180680c03070901950140c8007007c21503c0c0300040640c1e0401d000d07a21220f0480c2050012624800000c0c400306000c0381c520391080c0c2d6003200c18426901e0641e1005407114a503500c1c00d440c84020101980b952030194241040005400813200140c010400803070181d440c140e4000c42c5207120307508030744401c1c0e4844c80242e1120740e0300700519190505920395410003400100402c0301d801003900a86e00000c03400b161138101022160031103c588420007040e00c00c0c0c07030720f103e0821050446c0d03403081443c1d0802050790f0303100d103007141d0484000900a01c1d00300100b1400101035005940300303403201054200810046400340213010300c2284642d0b40144c1c6e4a03441c050140440708043c040c8882866100d221400044e2421101481d1640c02d00b00091110003180049001e031040d50001007101016511164002c030040325458040c030311030384440409070b032076040c055070b5500125030424a40c0d21190003080ba1703040c0786594030380050001c0c203a55096a1694015031460344100c2d00d0200603406222840054206849 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 145783453 1250 145782203 145782223
    0x3100b040207051b1c0b06011b120801082a0d050304080a1406130f03080c2205090f0f0103060f0204030b040f0c0e0c0d05090304150518040b0a030f2a0305 68
    0x2441c100000a55246d00301600c10040c003503030501c840c0f95a528292180d105c11000080d9025016013400c1102060003440d0070030a10030411184070300b4445a4207a2200340340c182c80e0341202c10003606400c5500b420804581100d030380540306400100f001060600080c0b10350321542c1e00903d001c0b01141e010090720361500800130000c41e052510324500800158000d1500003c680d0585490465030b190024801038512910f5605840783d04808418100400c12480e29402c0f40c0044844491030740c0d8a881030704840104580719000d841e092001800010b400780d02103803d0b40520702d00141410b0302e80e5034480025006580075561580c3c01303600300c01009003030405000034007402c0002c0412070800c0103400303074640107a451845006452341c000401080701041a00d0050118004030f110b01002010040c0242d4010003a0000ca150300c400303040d00909203070241d107a005a024112074050f500e56210381c00700c1200e5030000c952410102450718078036240007071090b4000041220200074a4514981145004021a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 145784703 1250 145783453 145783489
    0xf030a141c231f090c18060c0506010b040e040f030903060c11060702070e070c24090308010e07090e1f080d0e0108040804260a0c06090b0903100b040207051b 69
    0x200e500c0c1d0201880e250f00404407035040e580424003000310343c029900b81c1002c4180a1050001c148005031131603001c07090b12a02d43c00b407130a03185580d0b241d444009281c0b207980501940303401c1c030002180004060384000104c06000c0c0c90588101038480c1d44080c142c44242c0c0030b03000003542c143c03480003a0510034000a43c0041d481e000608102d407800504041c5080014004010f20072100c1803002481801ca461a0350300b564008640f20640d01c000c034850007419103140c25000600709500104081e1140403443d80120510b4448405491030b1886003002c03000002c0a10b290000c0c0302c06242c1c0c0400c9c1100071000905210005401124003031a8014000507081c0c50303d83c10020359070244004900e55404440030741c1e40c4090712285904c511144001c624500d410441c4491040c401c480007804000101c4200f80c540c250f6aa9460725aa111511024091a10102d82c190040b040107a51a8034071b5000145c1440050005030503c0f0680d00d400d82400d1060300c2d0b0490044044940703807042d14000c100042419691 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 145785953 1250 145784703 145784731
    0x3051b0a0621110c03120709060207030b01090504060e010507030b1314130c030f0b01050a0b07030206070e0a05040e01090203100509030a080a0213080a02030f030a141c23 75
    0x9000460608103080319019450b95401c44403002d00c80716001c950f03401400d00105d9035101c0c25028405450343c41100c8100c0094003910001c10340302e00c0803854100702e94000f25191303981d0b404c043c41500200400f03401124229510007060310551820701a4902c140d1003602d000800070a250309004048031b018042c1c02020f4038203901d0500d0ae0b042071900c00e81042c54902c50750245051840d02000d4440c0c130750806001c1c0501c1000500821a120003428141c550581e540c500c05a070302e21b0f00b103045018400c001005a0401000140c0e41d511030340200c40c0301d0400130008200030359101d0214040391002181c0502c5651207071051003e500f810401d0301226090494204898580420b000740c403030146040c600304008580e03001c26620415034060380d41c0c1c1011144002c02c40c0d40c0d40d089035a507400c0c15503400c0340640524844090204004004c0d6103044030107031202c90b460203021955405580c440341802a416400c07180150681000784035120003006c002d40304002015610b000e1041c22680280002030200c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 145787203 1250 145785953 145785977
    0x30106050703110c060f0d0b0a18020a031b0c03021504020102030901120603080d0501060e010e09011a0409020307180b0405011205042306011505070b01030b1003051b0a06 75
    0x310004890416801d460204115001c015905080c2203161807180d601242c041911031300070840e0300c010840784c1f0001404000d81c02d520024403d03803034414483c0184c0e00c00125402000002203400811040103245070000315114441c0c920088250107c1101c400141d50540070010150100910f2001a54a014402d482e02e001e0740002d41e03030720403819981c0c100940780c0348005145000303805c408003075980008000e80707511a14000b000140130034482c0c030000890110081b0141d5018981606070954054690701e4540c0c2001c442000c8440f0107009200028001c010001e4100510310141d805100281c1d90401c1d0000d40d84000703a61400950800740492008000400980c0e07081050741c041c1701404500810700f0740c3c3d40d080194101008141180c0c01d40544c9403110b1100c10013003082d40c103036034404990000000c40d0100807a96800f40b02c0c4010120300c03ca41c018004074072402100e55101a012050084080c0c0340d07502d4906240019100800030404040b8000e80f51070201a544098840c51a0072080c00b54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 145788453 1250 145787203 145787207
    0x10609060e0703020f040b0f0a081f051c0b041a0c03091b120d0801060311090d0b13080403060504031b0503120c040f081b040b01021011190203031b030106 68
    0x41c0241820303007407660001c1c2c280540003170341e000e443c0107049a0680d1510360950400303100d40c079405643c01e80000703990707640001e45410481e41c1d20a50045603013104c101603810b2105000000c08041a1101684034910721303000098401d40d0f04a200f02d1290100e07128243d44040c4031190050050202c0ca80c8040602c10400a83c1c400070340d00b0351889200c1410541d420303151021075466040c80c0e5542d10b090080707613029000c80d80c01405880c12210146c0e010411403408201c0380300103006070400d0551003045841650302280b42111200c0d0440e40821080750001555510201194440c9e4421108651540100418160000420480c2450400702c0300c0340340c00c0981c0c4030707512440b840704551b141d0061000821380152140c0c4c20340b009085041000c90380907488014482c1e07642c6603100b8079428840e0403880003d00b41050301441c00700d81c1c0184c0060064204125000300540f80041801160704001d10a000c41e40440c1c142c4448903407801c0d0051a40c07070402001c44800603800d20000d2010407010401004219 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 145789703 1250 145788453 145788479
    0xd140901050f15010e0a03030302190509010c080304020a0504090b220b0105040c0e2d0f060a0c0809150901020609010e070605070c0e0f0123030705040e0309090403020c0301060906 79
    0x1004240c0f0b1058010203c0060b120801c055400c2500003c00b00004410150168010810445100300b60b916032415104100e4640c4150911a8009980e48808400084401000e10b81203480107088c87c650b2912100860200c610700c5d00c040c4c9910f054201407042c3c10100380d06402000c400c01c400585481403d80341c11f6010b54042c8600e500031381e07071070412380690b502c209040d0030940b8004002c8402144000154070f075080d02c4115a00030000f250444c03500701c0c9803159144c00081c20107800310f030501ca80f100003a180c0c1741c09410180d407510b40811551409035280340c0303002050302501140c50b840b400703007400091a09000425950b600e80c0f40c80c26400c1c2003100002d03020304884a80c505255500320910b4031103041030450b400300c40300300d4950303084c803108590000c1c0780b41c10f8582b0040072902500e0f05140081c0c07518044141280c1503048410305000d80e0819400001a00d200304088a01c0c000708400851410401143c0940050300048114901071030203010300c000070140c9020501c0000d0030012800e44203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 145790953 1250 145789703 145789711
    0x91202030403111003141501030c08130308091006081501120f06020a02010207050312011a18130e030a02010b0112060e0109020903160b0405100906050d09060e030d140901050f 77
    0x1081c504140e0340e5002d22a4200d01802d004034881441541001f00304ca86d4800f0340c00d40b0f2180840d040c9071070740042d03074820981980b00c1c0c607c04091700311010f0180c0f000d64034200080d010a2150003241c5003d0340c3c0c40b0a038051200101281c600411000b5a03194142103003e4041e0081e070a50700d220103240011600006154441681020005a80300d0b1104c0050f0300a105164000f0030a00000c100c00c0b803003414805805048030b01d0080d800301c024241290950480c0f00b0504c41c0d6072000384003a10700b00c840c18000724515886000000002e81206c1b40e090350b501d150047c06090300142c0d100d1900390840c0d64821520141595600030920100d4105600c00401c14014021004019030101c0c00303400a90f0108806100b420522004204090f00c070813107845c2c2c5501c00d006440c018402c0c0e04908540d10f204214503000c0b142c8681d102c90a041030b0640d010064056800c040d16402c0d15421000c3c40104184010412034004200008061a008010ac90035800081014540c1e9152808000d103050310085141d502c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 145792203 1250 145790953 145790959
    0x201030e19060603050601050d0503032a0c0105060a0f060f080a0b0901030b0f1f0e09010609020c030421030f21020f030739080d0f09120203040311 65
    0x40c00d5244414a481c00c01c0d01956221516400c8405500b840385035407188084d240510280d5080e40c1e00d070414001a10007020340245154001c20000e80c0022220758210380c0540000a030350082c0b0120904200c96420601c0050300d182d5444090040500d80710002000801d00c81411549c51490200d002d0148800503017402c0130700007120b0016520380d0580c2e00000c600c0780000d001041d00d50316410004030b101070444104480c1151180441c20741d1800c035100003080075480c1e40800045041c4003150503000e80160023007000b507403215404a81c0034a03a0001d0b01c50540c422005546175072504000201d02e4840e02003944e01102c0f90030b80c810200c1d072300c0344280101c4034603030078242040b03c901c012220302a5100c06850310050710205000c080d80004c00000c5008440c95655526010768441c15603155100b640a2404045070208407000802503808403801d40c2405000c0060070315001c0550081514000d0300350041060380c409202e8200301c0c2084490007441d62600c02581440d0940c0e80e401341c4041c0c4c01c004a84 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 145793453 1250 145792203 145792211
    0x30f0b030d121802120109020a0e060603070c02060c1b0a0501110d030b06040e04050d031a03060601110102090d0b010501020609030a0e0d0c08150604061d06061614030403050610080a020103 83
    0x200ca91424032660403500d44c0601805082d10211a85034001c0298000c04c0b07125040040002588012140303420303000b81001072040385192244e82081e10030070705080080380c1200c0309002c05d00c1840e20605c80210340d81c01f505405803030100208104040041c250b080756060007241050115030a50000d004a1060194100000e0f21858000000c00d54011030340101c07010854032003000200072010881e034407881220f0b02c080c41111500b10b001515025065015600b5034401000a0100d40c0b19954107006000002e000620304900c41001c181d50440f1181e0648034031034280300400055074100704075540020000007541c148603404400409010000795410f105030702d142c0e680c0081c8551042d4010091000030200c40181302403507840941c600c021203140340301c1c41c908000010024102c892800c900c6441c07091205035652541e04204a903040800d5100d10b04001d40328410004140a0701d90301c041171400c00a58541c3c2c95440d001d468150f000386071019084030744030300700b003035a00019414117001d9090070041 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 145794703 1250 145793453 145793471
    0x50f011806090f0b01091506090501210b0a060914120d050702030718090201120209130f06090507021501060f080f0403030e1e0105060402032a07060507030f0b030d12 73
    0x40e01515070f00401034480340f0100f000103080b00c035951002a01081d8030703400083c3d40d07944110035036a020380ca21076907022030310200510b08666111110340365000c0020a00103500c4c201d49010480015051700304001046c503c00e414895100f00c146910400e07142100d2007040d90011041c159100d0072225440c01c11b04c02c003c42c076070b011503805210f0040540003100c0c11400040788000c0d20400351001030740c2a804944404030180484c4460b00844410000c042e00c00503508940704d20140040004c07000d031220441d940c020100d403825450066500842060303004040c01c0c00035440403c0641810ba01c80300c1441107034071032140802d4110343c080d5400441c0c03070540c10070750303889090607030107802020610b0015000e40e00d1003103100082006019282d003c807400030802d69480c3d4007440b003207101c10369098101003608002141d500104161110b400e0091b00b05041c1003038902d54a88090300e400f5100b400100f0389030800b47e81021028801c40c010040300320700410000c0f11007800901000243c03010780d00001d44440f024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 145795953 1250 145794703 145794713
    0x3190c020301090321050106020607050f090909010b210a15090b07050c0d0912060207150203010f141f05090102071d0108010c080c090603100509040f050f01180609 72
    0x1051905801a00900c40041c6619008010b12031500c400725048082068071500a0281d108403410303a03216030010141c4da16004000d5465070465002c4941000041101000540f0b43c0c600341c41c000c03000341b00049074052100c0e041110030b10306920b0403449501034800710701c200c80700064480c54041d0008181c50107032a0b6881003102030601d0b00b8002e8924031210060002090340107008048103200441517a25004034140c080314214107910410200702100f81129002c04c036680d00906c0220300c601c0d201e001014a05a000781643c00981c1324a40800c48071204103c071701e4010411501d680d030100e6013200381c0000c40c03540e8078403620140d0442c03003002004145c04209900811281014000100403428000c5403402d02844555017400f40849650801048400840c080c2c07000328003440d030f0317211068148035290b414842281c01c0144800e00c00c0f000000005116115001d44901550041d42014003034013582c280285803452a45907030710f16a07d45031b8400004c4030150002441154000000700308e0520354181 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 145797203 1250 145795953 145795967
    0xe120a0e01051b1e010b03151e070f02150606030703050a1e0209130c021c0314070e0f03030301060c080309120316080f01050109030602090d0c0803070b0a020c0319 72
    0x1a60f0444031100300d40f00c091a03400a444405410400c450100507581080040c1c00d0710a01e000041d0198481c2100d4a07180c2c503003c84060303100340903003027070065419080526650340c2810780d810004114120000c5007441c0d4144803c00000c2d000080103c12402c00b040486d917640f10040c04141016074980104103510165001507600401c6504078a070700130f80811024000f90b0088011510645c04002d2400d0940d82174080c412052410381c0140c80d0341038440303804801c00100200200101603617011681040c03010340e215140585070b141e03984002d090340c0354144a490352910700c3e440d00c2a401400100951035001007288100f9a0002640ba200d4681c48990740c50441035030ba1800d4004400b20400c2401a480d900c0c40c80210000da9401c410350711060700d05604443c007809000d0004406080c00c0c0b0100d00c158000b0155007001603d001c0301c0d0181e0341c4403145860482d41040000380c00000c0c0c14018044819071054110f01e00c0c0d041146440c0302059403a40d21712861840c402910b0014030415030b098001d980c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 145798453 1250 145797203 145797217
    0x11120c04050106210b0303091c05160303120506030606060a02010e0a0305070203070902070201021c0c050a050d0f0503060a03060e10240801051006031e090b01050102010e120a0e0105 80
    0x4030038061035071224006485204200354800d114074070143d922000341107034050241201c0f00940614503252000c000d100d03000000886107078010911001c050f00141080003407855000722468a0201181180b500400c480b079042c84551506082006210309541d004c140184c01140840d64641d40710701440341a800f40150211240f15802a41d0040041c15007040060000d01c0c0308030300b650f506135100d0103808c00700d0048820103030050707008030000600015560500041140c0a061144c03181140791b44440ca80503a10b2000c071840d8012801240203107402543d20306c2800e956003800c0d821454918042100308241744005040c0b2a200c00b982c001056003884074204d41c407500102403000f800010060102100d2034000c0300d81f440d80d0310a0002d00d000d01031007034074091945d20082c1f0501e1842d05004030045c2011682c0c10001e500e0b0304141e0302984c0c1d524412f0100c0f00e0300c40e8089041c02c1d8500303000a405c41d00808507102c401d0b0090f10000a044000b1002c5641c0b02d41942440c0e0741072064040102c8050003070381 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 145799703 1250 145798453 145798459
    0xe0d0e100c150203010602070806010e06061614010903080603010605011413050a0906033f1101090309260d03110403060c0c02040c05041409040203121b060c030411120c 74
    0x1400b07410040443e0f00290306a505640032a20190341c1c5441c15544d4070f909101c1c60240c03074509030101e019854101300400000079851001c4801e0180394a03080488180c2c4ca0941026a540320304000805800c0724820340d00c180c080780208415403505001920a00000325000721400c80000e285d00d05002503081c10015100113402442010b85501c0090000e0049000030707100210425aa8550728898a0b51301c0d05082401265a54025440000c000c00090341c42120b03081c40401d110b103064143d42480380114881c080d65030815400d1600c5010008043c0c0303480e110050345030b5650401040d0b240018076024581031450001480201e4101ca081640550380006020703509140e0f007502a598440c6405504038000c540800c840c410044055900388120300c42c0b400d0748401400d8865991800500d41c950082c000341c02e480e6451a09141c50300c3c01d5104500b507844400740741c010300344180b0040200e01d03800094499101c0c9182003a0711680004814118105c0c402c03c400d4001255964082c450311a4066001d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 145800953 1250 145799703 145799723
    0x6190510080f0f060901060b0405132007020f2e0c0b07030c0f0206040c12030c020901030b040b07050a050711180901020c010e1504020d0f21030e0d0e100c 68
    0x2c1e108543c0340c03444540e082d40c1c540300c0c440c003160b10043c1c1881584100c40f17890110038601480c0805021040c031404c14580c1d00d41742c0c5d500302d04910400886c002141c10340542511981c403d03040c41003290b01c0000902c40c0e4007030445c0d41034940e0000402600c440d1a11503800c08000b07000d04901084810640a2130001d01e5000351600380300380160180c2200d25840d009071640820020064812a5102d90455000e804043d80442c1080110070011034240c91901a1906851102c0c0c9074011480d800400e0380201c0c0c928039003104003c203000b80600c0e0070b0380188207132510502d81807080c04000c2240c004c850010b4070103c070800c842c1c42d840e55100340c0ca91109070745c4003440c9132500e00444504d00070f4000b00b408000329424508142c5015501160010007a007581d022210151140d03001d100c264401c484080f104000020350300070114541415a01108454060640640d04061030003002c0c3c03158459040b0f000e80c0607100022a081d00984496110f0300241c5408141150004d01242c211501481c05003841d284 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 145802203 1250 145800953 145800973
    0xa08100909120f030b0d0b0a0e07170f070608010905100503010c020606011b052503020d1103010f0504080a0e01260f13050d0507030905060301120c080619051008 71
    0x2000400c8945050710741c48440c20041c03c0081903051701c1300c8540c81d50380310100c04c0c400c00006007408040d40e002040c1e21030001e02d800c0c210310300038500f0b8881c1d000001081440c140d500c0d1090020004074009144200103032071840d10b4400003610b0300c081801010251521100010008500c2000600003042c0040c002d100c42d4403e9000603440d0303641a1190340c0002d261110340b9400c490307200c80e40080946e01c5002803100d01160303800e42e000081d45102900703103051042d10000240e501c9001803100d040c01503010f800081000c100301421281c0f02d0a081c107040741800c04020100d4000d40546081103030508115820482c4440100d50001c03a4a503519a03000003034003180285003041c940213104038241e544101d03064841e0440b9035480340541000030516400020103410907480782000d0801c4610900300300410a4031880000c1e81d98000341c01c01d9880c8245403031000180801110782000800c1524045c0455080c0f2456400c4862403c0b803042c0c240644950108503070900c4d41d865140145100403c1e82d1102d02 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 145803453 1250 145802203 145802213
    0x12060b040f0c1107050f0f13061703030708090706050712020c09090102070b13020d1712010e1f08300c0607020d02071202120307060f02130902030c0a08100909 70
    0x19050f58440c184a00800032070603003000320030b038250424000c001e940b101d4444000c00945e41c2e0040d100148407921400c0000d90700d40e00207e403101e00e2034180040d5032a40345c02c0307078000e00700400280740300c0e1123501001c010001d2680040440e400740350400c1520b848500320b04410b914040940496540102240042207800b40d019400b0b0002c00388204428504d41c0c6400750344079600038080d00c0180d803141c07848003064001880604540c80b00000f8154940c00d000c010360b411801440f00360310210b061b201e22800c2003682891f1000540300e0303060714440c0008036410309498039074690b914800280302910707802610100c0380c009242d4456005410088d5941d40d00c0c18090300b40c540009440300f4015101c0d5a401d800600d0011401009031000491302c06951f1f0007903001c0000822054400c0c1f072941c001081400c0211f0300c01d01880036000d01051002d80c0d140c2214200c5078410740c1b943c2c4a200f40c42d10520a00a16031900301c216107400c001441d080089413900d00d02c21002e110154000a4154600515041004 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 145804703 1250 145803453 145803467
    0x1141006020d0302250c18090b060303210702070801020c01020c070b040e0f0a090f050c030d11030306040b0103111303030e0405040f02040f02041706040b01060912060b040f0c 77
    0x15003594240c54400c0c09006064003640500c820718102d1310b420300030701d010040c3c0b0325285d20b82990080000c3c0ca141581d0b882d1440c94040264200004039031503404a40c00c0c000803482c60394028609600440c6084402d0103800c81280d0f517682c040d5040641c1d100410f0f001e038420040304001e49058002190f468001081d224001c0d800081544014000e000c0c0000303800c088003041c0c6003120084005c0e41e0559a40c070398840401d2500a04402c4416034032405240800e4100004038282403283e4010440240d00b00300300b41c507141075600d48004100e0851010688440f012088c4c0303400c404141c90209002c2c0c901401030f0007400c03411030420190030000c03031021410445500007004980c0a511100034003c2c418080c0015150104d5001d0100c0c1c1941e00004011304050784036401500f2000700041c2000d44030002003102555810150000741d22260900040c0b00c00200f90500401c1310b801d107441031a01c1c00a51032400384041c6401b4005981c2e0b10480210b83c4c480b50080c00360484080e108101803102c554004e4200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 145805953 1250 145804703 145804709
    0x150f0b0d0b060301180902061e09090f06030d0e03150c0a030c020c01090b130803030705090f0603040b0105010f02010f02270102010509030306210307050c01081f0b0705011410 77
    0x4241807021042090409904990582d41c0f48101000900e5554120324050124506e080f60008410040c0304500140c000c502003d240218200694270205003080007828a00a8910306580c040042800b5544c1e8001410060100460803c3c0681c041d01100107401d04a01d00c0c148030311101c00b20108101040c58600078515540a43c604018072900350354120f07920108640c03c10b001c01c02c4e4007014088000068050301261000c0c420350144261225200c4c2d045400c151007000214a000c6000c200f00c3c40c20101030603421074141c9520f4114609600e810010f000188141c60610801801840782d0320300c01c1d000f4401417610450150742d10029040000b880c00090000c0410122210000446941c0b0600403e4000d200da80700441c00c5403142410480c020000d200da141d4041c0c0c2c082041c0030b03001c20a101518283c0d000340003814161116100140142c0b2009200d10300307980c1e07440d140c0f01c104000411510b06507030700c1d54111621990a850b155005100c0060448809041c203c100b201c96840c40d40f0031015 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 145807203 1250 145805953 145805977
    0xf0604090914060906040f03050c03070210030f0b190b0306030f0a050a030f03090c050114040e010902030a20040b0f040306140103020a080304050306041202011404060203100e060102060a150f0b 85
    0x515680d01c55416143d000565005002c140007587c00d50220748188007a001c0c983c03100040d2403400c001c1c1d81c0000c03949a541704c1107002103511400304100c0c0034140d20602002e1041600c04440100c0700c00c10400420309a8081d0080f01400130000c18002e49040007201d006103134101c11101c0d0710b182d50804954035007a0180403400030b0000c10703d40c0307003162090181c140e0303595104060604042c1400c00560310380c0c1281d444a6405c1c00e007400001f03442d1556040160081403030380d4006980b802c1624081d401d803164040701d4549410b200c080454085070070340485045440e480c0786284c84031031513680e4214607c100e034005443c580c140b4030400070304003451004a040744d100315104401d05035a43c5206403070707010703920426038103170400d00006010800c21040f00b208403010b40f000050300d00140801c40b003481070030390b000e031806580407040001d900c401c000100b0103040100c0f0000450710b40100001d654410003090071000755214002c10404107c10514503024000307000c24145401c1c4c485c4002c1069402103881106 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 145808453 1250 145807203 145807213
    0x90a0c03051c0e0108070f110709060e011203020a0b04020604050409030e040b041506140c0601180b0f0a0b071110031a09100509090f01051602060709050f0f0604090914 74
    0x110b6180903074220a104032043e1184521640c1e0141d054600e00c1e034042111042c803c019624210040e81840041c0c00b420303c0c92000103500e42001220200500140c0101e8518001e822440c404690006645403c1a0344290301c1c4400340c3d158408210980503075032144e0b4102d070500c2d0f82c0d80c042580284191813014000e031b500704181c40100081000399001e88420400a910300601070007000e1051003000c007601d80001610380b80078614020286401c40c26484a20422303080c6907500c02c5242140109100c036081141c104030f06201c03420004244610621034070001c0140000c0d07203402c1140102070b480030100000d0882000300e4142101802400140720000040712007542140401d1070105090b17800f40600706a0074941904040c14003034a940003420302c010900c208605030f440d40009005443c842c151031008403881c1d034142c00010345043c40141c10802400903181c2d040c011031b1030b202c003012000b07001100c00d200003d40320004581c440c8a00d410425109042c03140d24402d12480080d8600071690320b00c2100c03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 145809703 1250 145808453 145808503
    0xa0b0601021005040b01120203010e070e0610080f01170a060c08060103110304050304030822080307030f0807080a0c140d1d031804020304173105010e0405090a0c0305 73
    0x4003c07980102d4009005050301e80060152210400551252600c0a000010b0b0072620801061030300380d9640c05034011960000801000b814140b0340c2c2c500030103007404d040f00d030b0b402c01c0900d81a411b80140108105586541341da0322080340104001c14030181c020b0710820242007030507401862010216031050129050080346080c41c07072038100b00c922594100e405103060905503a6003188035401852001042c50300c5417540000900184442030090610300e0083d5035500300c0b45005020f5900f1000d01c0018040b020b020800025000501554001d82c1003800080d51589a03109403502500c4070303241000b5800126014017150441d40c03050440340300c0d000016804480b0054030f00da40c3d216041f802107000c02d017414440d00d1424260081c5070098400e100c2107960080b0180e00403080d8203d030780f0320401009440c8104544121441c40345890050704500000d0b007600304400602003100c1e450b812401107962707400085c5040c0c414040d55901030360011210413030944d07905040d03550b40b600c640c00e0300300c10000407070394 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 145810953 1250 145809703 145809733
    0x9080609030a0c060b120714010f0903030c0b0901020d0e030408160b0a030203060a0302120c100305010b0702121c0c050c06090a0e1b030705041403030f0f0c0f0a0b060102 75
    0x40c402e081126070702c0d0141c00e01141d607040c010b0304101070000d400200656901d00f40c194203011202c0900141c49581190180140004000d000920f030303904140800c800042c004079034450b210110240d00b0400e050b40d41d0700c607080c01e580244101000340145600e4241e200c420410088010001c480c0e005c011210240f490b4140034190030700d90b00c2818294101017103042d01d00c83c042e401555010900400c401019645d80c0c003c41c61a418141543c1c030306420540c0c01200d01d16007a19a020607140b249000c000960515140c2ca501c1d1181090180c80f82109514480d4620340400000030341d00590301c1c01018a508181c0d020b04503d03290002180c4900410391403051504280c130540f40d400c1001441c4e03071801c034648040303100c11000103482e00e03415076140c80c1c410048100c1040118050501079032240d60350b510b0444030000340203603038803c00d101e608204400613140f0300c100f0560f6035441d000d20344541c0d580c0031004130034601004a030911806001d0407151109001e4801003442c8648400e8080d1002c0710024190 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 145812203 1250 145810953 145810957
    0x1404170708061e0a0b0306010f0618061d0d05011506091707061409030a0809130905030a050c0a0506130b0a0b011409150d05040507170a0f0206070609030908060903 72
    0x83d01410583c0080c40d540c4a42c0f4152074190008107801d400500300140307202090804809070040411075a88000802c40d01750300030320080078584c1c1c1101400505040c101c00901da17450444c80320244138081400b20455980c0c11a0b80440b0a60180081040f844042840030303441d0002c0c4a00307004102800300001e114040b04241c2d00e90018044040d00a89007882c5064900c0d41a080c0d0311585800140b00001c0e0030b450400c0b0200b00203010741350068a41120108119041103492003068500c0d04241e9100000703503001094071101181070501a031950141d000c482d03e00340030210090680d00c030b800244500207122008015034a401500009820364441001c0c01c180e0341c4494001c0c0c000f0751007171445038114400750003802d64880010a0700d2000311060404919a03000424822401070740c1e202400104001042840e004000d6846103904d8203403140c00745516403c00070b00c003a1680b079a07010807000315070f2040c080f0355855070301c20410066024541401004000c2601541c80d00d442f56002095500b400001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 145813453 1250 145812203 145812211
    0x60f03030705070303210f0914070311060f090307090506040b1002190c051e040c09031a090c04020d1a0f1302090a0909030c17090a0506030403140417070806 69
    0x401000c1c0f1525642d41291300390302c15000209126415485000da04d000740c0101078210f43c2560000c98416164100711445680d8013114040a52000e2130400010705110001c110f42c0e40c04503542d6440c1d400c922000c3d10389106001400340e0500851601160710111544001e000381002c0d20304010044401c1e0501c0044000e1078403100141c3c0c401a0660f142100c83c48691b5003043c815540c0d0080540e941011035640880112101152417110109252358105171181166810143c98480310481c55925186490b0300f46501040c810700207075001418000d81000241522900944115514841074005000414440303803c5040c0c59601010343c411861f2008000c03030071103002423101c0509608400b001c00294000c18003207030014548c50000074400200c2c0f1a2140841c0240c44070441000380e8030341a2171910005104c01070f410f00c10700041c04542c403612091816a0004d40322503699480b2814140d8440000f000d200d2501c2d000001c0110703104440c02c1d0940078090001c0304803507419031a044000d4950030116 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 145814703 1250 145813453 145813463
    0x71a01060318080712030b030d050c0105100b090607140d09330c020111191a1b03060102032205040f0203040b040609140a030503151008070e060f030f060f030307 71
    0x40000c3c400b11701422920202c141890900060665280c00424200031074260b01401086000c40c1b1240950402c0c06180d0b84800501600751ba890b040000104203070081d4402c26001303910202e080020800c16816200002070380e00116640c0f805444001450b80c440d0f4054190020301021001c020158502c80c21500781c0c0d03901c91028041e2014020481d100f80c00d9036416810030a079031700b049034900001d00500175a8000c915040032041041d00304846481240b20034240a140c2820800c5940700705140040c25210b00c2ca0000c0e40c2c0e98075084c2c0100c2c43d41c021701c0c400e502040811184002c0c004e89500d01201251404c0d00c0501607460350014034022400100c0d009000c4030451b10004000400ca9402242014400e9090060004a1340030641c42e2191317180044003c6080042440042c90b00c0910082e110710003118044681024180010140f81c00034291100303001c04807040200036510300003a10015210340a00541303030702d45400c007000e10103002d440d964080d034995880c21140b4140803044821207500300d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 145815953 1250 145814703 145814707
    0x203120109050a021201030b1006110309010c0602090316060809010204030f0f081b0601080c150a080702010609021204020a0b030903030c090d020a0311130c23071a0106031808 77
    0x718014401402c1d00510524109908000700d01141501c000550701a42c0901105042c5240c891007000c20801250070030f00030300c20919120000180004100c0b4042082841d0040401d6000d1905030041d000e00c400107540f5001e1075401700d000c0c0907030742584c0e4112501681c407102a5203462010a00700e1107640005031200356890a1080403500f44c00d5041a11071084c07600c2c44ca80b500e035815151100c0c1c4106041c2d40c0070782141004000f24481000400c0001008950718040741400c1d01041281303120742882c074410b220b6000c0009020381c0c000e510110041c000901c041d50390780840ca807080400a4122030480c802d0090303d4020500000601c00e07684581081001075281d81c880d10321070059504542c0c1c4481e40030700c1901d801c00c016268000c6103002984140d40c0c3c3d01000c1e29100401c0070031000034034895400b0740350500c500700055214203a494400b2661446582d0003e034004030000714895403801800203140c000324040b00f892244d000c00e0481c0c2c7c0950341040036006004410a0303909070060050105101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 145817203 1250 145815953 145815959
    0x201021b10030b130203010303080901050105010f1707030603080f070b130201170a060906090501080c04090809010e030313060503070206010b0906030c090d0c06050a0212090306040f080c0f03180102031201 90
    0x40d83c4100c20150000302800701649840c0c40d03041c2640d1090f0400c0700061314070340c24024009000d00405001d070500342400c000310000410002e0038101107500000e024100c2c1c80206e0400c90013a48003a001e10307040001c5550302c05500c0c5408207143d21400007110500581000102400ca542c01e05c7c0340c080c2da059647c2500076040600c50092600c01510581c4090707912400081e0400ca10320402c40245070103880442d080d0301d0b0110585c1030402e401d00c0f4030b0180e0b04204040e4005042c003800c8400041c400d007001c801c0d114180d008070f8914011801d080c105254101d0b000301c1d181360800080c40c85a210740e4200c41d41a82c0310000c240840c003580c1c7c0c50540005082c4046401188aa8040c00009074080c0000c0d8914201c0e468502100a903a400340c000328800186042c05036a06120440404885030b0816203008860b00102e503980d60000c1c0080d00f4280c043e440c02041215990494808041c44003c6480c40e5003001c060907100e501144400301d001281440880c4230394008030503110651100740c510f03085a07213 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 145818453 1250 145817203 145817207
    0x6020f060c0c070b030405010b04060b0a141b1f0b0607030c03030b150a080403030b0109030507120215041d0112240605060a0306092d11040e070203070201021b10 71
    0x954140a660f0050070404148080d40e0400343d03200e20302910012406100304030910040381e50b150842a01c80174108091001c0342d81015100310424110f1500035664100701104208010700351007001c030305021f041081100c109540c620414a0500b08100300007080301d42080002503c14044001c0219035201031410200c0e00990004500002c00b926a040b0000703601080c1d102948410040342c003042c00507040c8002d155142c4269803404d0400e090010070582035480e40c0b65101843d1090000c11034070780da40002107441d0307003500d02c4454014090960300e803612802d0305050643c04810ba080c03040901000000d0b081c4401c00a6003107280c03c1400511400e80010700b110350340c0e01030034070481c440e80c41d6580002c258440300014208460b45960020342d844c101601101910342100415528448800d8020b02c2c100d003800404523410441c0704005054415001401450b010340d07400412521050b10030401c074140c0200042216500c01d902303031106004044018034002001c99005600624980507100c000341c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 145819703 1250 145818453 145818457
    0xb060d050a1103061c0c170109051b0f060d0b09090f010b01020604020f0409050a02060414010e03070b030c07030327061b09140d060509070626040b15150a0906020f060c 74
    0x602400c0d40b54001d50711843c40c90070301f0848040c3c0306041c1c1e5582031580b00b413000c2031103202010700421071341d4613843d54102c0c0016051010020001d104010000e5010760151555121882c2d11201402401c2c4516000f140607407280d801c0e01c5080115400c1c5002103c00b0b41c40841c0300351207560b0050158070003000110a001c02000c0886d421035840c41140810b00160740c680d00548001e2901c0d601ca0442e54004030001080a1501c1c044103000c0d510116040c05501c83c07504c03c0c1c0c0da10101080303180c0d4a4a41d1030400f01c0242804461110030500702e004c0107484d0f030042100900416000d0141803107001c04500e101c98801e540c2d40c00000011b403013104c090080c058280c0d040c0f1598000284218000c0405403244011038200ba190b00e1059800040c0c1000690f400514004c4244403103801c0a9480c007100305080040c075402070000b80903003a4240080c1d1040740706c6e400c004c0c14040144c400010304c90341040803991680711001a40c0400d040304000520b0b10310000e0f4080303082c0e24071005010507840d41e003540300d025 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 145820953 1250 145819703 145819759
    0xe010603020a060c0b27100507021204050a0b03061309080d0c18050603060427050606090103030807031806050906060f10050409020309030405030d0203120c0301060507030c060b060d050a110306 85
    0x6a003201e40c4403400c51003004003100b54803503900c7c001200c1c00c1c0701601900d80007000301d09000c03410f402e02c8100f09541e1000c5550048400c00305803556030b640c6000000702081c103030401c42d20f90545000c80600521100b007019055900d4010010080c104030a802030300c003490f20640c19550a0b205c1340701802503041a07409190810005007000c40c0c800349a00c41d001105c504a0345200341808810b9124041c06020001c8507040381058403002019411902c00410080000300b80d001415246d1303d50281405149072481d1103a50003c004002d03030b060442c4040d0310741c40140c61b29032290131039590800300340c508845255403c0c0c016840301d40c40c0c10714191071500039400c011b0482d9420702044c000020103490032f101c03a608007005503000d10341c0c0745a88850007510341ca0140c42d00200d80130500062206d650400210342d4140d0301030620490100151400c034000e091507144480d0098000300c3c46500d400e0701900a04e005269661080c012140760140110460200300c03110390341704400661042800f41100380365602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 145822203 1250 145820953 145821001
    0x3090d050c0618030d03020316080402010207032103060b0c070905100504090b0f070c02010e090a06080709020702030708061b0c0a21020f0703020f01030f0f0e010603020a060c0b 78
    0x504950140042d860341c11806034520a49041c2d841c081e042d02e0184000e442c2c0600700c0c00e00b142507092403031022200100307a150b10300a010b03445002c1410f580c02081900300440d840003100000e0111824034030500c85a60034188003280c1085408604400c0c1c601c19210260914001003841c43d240c603c08401800300500310030002c0b59a0180850151120b01070792600b1409121422098106247c000c810782c100288180d0400ca491501100103030380c05051050080c008a44813000c07922080f41d841c00074050b03940441f0941c41501000039800388550080c0c00310a0088045c0c40a266441c540161030f09400c5642d00242003000d048241c50350314120240168990800c12904031580c141c1d00c8109580c0180200220a080350420b010701075030411141803d0031404010301441851075012038403ca0002c40e0645c14075454450408032a01c107a44020021248880305121309400707400304d2802004240002d901404154401250550007460300c040365076803002000402c0c2c0e03150300c81340518000100d1220300b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 145823453 1250 145822203 145822213
    0x30a21020a0f0f030506030303042d0615050103150e04031106040503070213021c020c03090a031a070f0509060a110102030717071403061903020d0309080d03020c03090d05 75
    0x48244980e101074001a8400e448821041d46100000f5050400c5002000c0c00c060070300041180c5a01c1c040141c1c2c1d00240d10008040d81c60b4212020300382c1c00101c0310b003580600000c411107881400080e4010720211201026031031170458076100110300781c8002c98072410344288035040400c030281441c114568818000d280c20440c60401d904100e00700002520240c4113a4804125441980380c8140016080c50f8046805c500d001c842e1408018810042820401c0c80c5502180000c3c001d0018803c0f00d001c00c4000f030141501a0701c07841d1507040035901d0401d5580c80640303000005c10b900d01031408044c02180c6600c80c50f0608402e41c2c10440c6591040c1e8800c0c04011000c6800002950240080c40c00344071291245801c0304096007500c2e920810080c48071041150307411200ca05181000103da80200064400c901c00380c0104c415182c2400d990342c402500b1511018001c010f256000b02d94205945910f4242c0e031401c100090304030240e001d030104507080394104006002151800052401c092032007582031ba8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 145824703 1250 145823453 145823507
    0x40311030f09010f030207110405180d051c05061c051c03021803010218131404030c050f060411090403030e070810050f0c030105090901020403081c140405030a 70
    0x9030440e045411031000340705000c01e900d102c40da08030702c1880e8060740626046050100131f03284e0743d898440b0f045085015035034030b0010902c1001000e141419609640c4215100c0900180b0000d0880c2e00501c0c880c014403400c01d07459441c950140c0907050007004002e0480b1040c520481e100c08448000c100d04940d1407180702e80011440c04055846141c1e43c16540340186c803290581c0008459060403200548242d10400550030152a03e0000180c220b1003940e002c03044c10820000580280041420800109400c004000425921802c1303540c0582c81401a2082041258140350f03881e201941d009040750062000c84010342000055241d100c2c0c0039180204108041d40c1840381003040c5034104092640200c02005414481340c007845800a0300c03010100d1aa18007400012070354081070042e070b03105140400c00310340c0341172094058070040d40d0444048d03943c490a0100e58980c0001001a605016080619107918400c0981040b88500d8100025519000c002070085810300008600035405c0f20b2441c20300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 145825953 1250 145824703 145824737
    0x3080a0813050115050112050c1b010e030403260c0d0c020301090209041112030906160302150a020301030c0512100b0102120408030c010e0d0e010f0c0f050a0201030612020105070b0403 81
    0x511500c808041d48104c41d141014001414402524490701d2458100410700050042c600100d0300c2400502c840900c50045040c402d5000d001003401c4c060300c41c44045808418046118412040c0c1e0b0b00c01c1c0203040e030320004080c1032101e40c0110844182c01d0340000b07240e030354100c0c0210104050184002c0000801c0002035001810300281501d080c3d90404498207000c40508150045049203052400118249820800054018481d000e841c12100610101910825000f0007642e003200c1090700000c1c2e0b0a04d0311040c203030300942091105807036040b050f40b000151810407062034203001c006140079020303541100403d400504500343c1ca69045100d0034203483d072030300c1d00107014102510224024503500c460f07860303000f400d4800000c94959940c102e0061744d26550340241c41ca403219002820204e0580f00f856906649014a5500c050608442401c402c02000380105124030030600c03d0702c1c01c00055484030142c3c0c164002600000740810010403141d030100d41300d0041a82d10034840e103031058170413070f0010803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 145827203 1250 145825953 145825961
    0x50a0512040606090c1107050d020a181505040501050102031e0d0606120b0a0b0d090503040906080a0309061b0f08161b1a030103081303060c0f0210050103080a08130501 74
    0x4242c030394503036881c0148070785559400f1315240b0407903525055200d0002c9910395900d1351424415107110b0b400502c020000c54455601034001800403104c400300c003280e083d00c80c501030301107040740d1001f20042d058007041c01c0c5058444e980c140e80040c1e0086003402c090980307919100801c18815441d43d8428860203c00c43e09034002c03000605004c0d42d0709441c5d0029001c11600391000031881510542003100c0500c410190001501c14180b25000003142005403810401d0952146400080180c0d003411804103040c0c1000809c3c1c0c40c2548a6503421038216602d01e01220800600100d00c40c0c1c05480044c81c60108000400c0350032502d020f802c0c3d191402d004240c036403014084502044a204982040114640b03428400840081c6050810700010b00c4002440032010303c41404010460140405c480018450340c1040303001131540840100009400c0c440f000c0d09808a05800c03c006102e1001c000480c019103004250480c0d07481403040b414100e40003004d035480540201000d9809a120100e90089403003401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 145828453 1250 145827203 145827211
    0xc0a1706040b0a061709300405030118030210150515040e01030c1701020301060c06090519030315050402160b090a170a08090109110f0102070b040f08060106110d050a0512 75
    0xd61260003400001190300f048001008950141c201c200c84e140070240a001c0c80c1040c480d040c0b02403071107d40d000104202c07800356800158141d8a44910380d0304920701c45400103825406038084544031254800401c0c15240c5802207000c40365a840d0042140c1e0a0100300001041d0400ca600d03803c0c02c5e1111010810b42030240c0c001d8448224580003040032005444540d140d18404000a501d19070400070080e004045d004001424640e071451058107100c0140061009140c00305148103c44880d400c0003000390101f10104058103c1c0351800140234903207031007118070740844609194070309285615a09440e200041420070b02d8020100903900140500c00010709107282d0843d11070707e40d016101c0090400300000c0c841e4941e40c1c98124043c004c2200c031011860305110880e02c40960211000040741080043c0d44408075001d0085804184005509030300c2c001d484220048940f2030707a03240e83c11691034400040340d10701500004c00001c41240300300e00070041c01100341480e62411509205005502ca0211 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 145829703 1250 145828453 145828457
    0x60303072409060e06070311181314070804020909010b030a0602180603040c0810020301060804060f02160506060907050f18010903080712090f05060d0e011508060702060c0a1706040b0a06 82
    0x10000010303010310480d241e02d101c01509504049e10090441800d4140d00304407842100d00c6541381580e281560072280f801120048402c07107504240201621064040d101280705400d010005090f01c1c90510401e804100c0080003822600000e4448000a40c8901d05030b41a1640551408034180c0341d42d401540241c0c4240d030340c4140f0b14901040c80303091a00b244a03100c00180108010460550f2003200b081c0c10503000107001894070340b0b808a0700000d115024100000c000e48500710028084007284191180400366400d800d075540f400d20481e081c1c803861041035401070301030104200e80b03221043c850000070018141008600c1c1c40392501c031016042400102c071003402007100c10b00215403144082c1c0041079a5000701001600700000900240a010342003c260342d0b856182c01002d90094100d40e000951350a4102c046903203400d2420345a01046651070054410100801d45a8450740f0484940301a07566614901c50203c0c10300f9441d103030024140300c1d40700340c0392000d1203015614543c80100414030741d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 145830953 1250 145829703 145829713
    0x2030d0503090114061026010620150c0717030c0712020c0f0607080403060207062003060a0608190507050c0106050a0e0c03040c030c08030d05060303072409060e 71
    0xe2610709454104401949003c044405e0002c02c2e15031050300d0011961a0401c40b214031020034242c600744840c00d40743c1460360701150000508035080b001010300b40364104825181c004040e0707991503407001d000a48001c40f803c58000142d08400c07000182540b20f120307242125207800184d841c6a025002a581c0d1400c0010016540d003c1040d02c4418806900882c0080c020072507a40b4000b07062120a031200d030f40288000200901000030724402c6502640e8130100454590070142401c80003070600b01c3c0f02e0b514104000008142c0f0382d800000b901d12544e0300400704804141402c0c4115031000c0058860015031050452102e04590341740110303445040243d491070b46800c420751007a420743d2266806a405101d142506103d4142e61a245c90303800050310186a81d652194600b100498289a10103448004103000114060901200401c000c004d252424030141e1621010141c41e4415800300401045d800c091030110751126445800b000f010501700040c03942480e0301c540c01a600c40065545542d080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 145832203 1250 145830953 145830961
    0x3020909010501080603060f0c0c010203040f03022104050409021f0e0109050a032f100206041106030108030702040f1e0e07060c030807111204030302010914300702030d0503 76
    0x3050304031a0040c41d0920704610142040800300b625800040c0c8500c404400d0840000c3e800b05241c01124a1000c408008664078503090030301d104d0618205d181200140a40702d0002c4100348090b030903941c0000c41c0b61030540340901d0501084014252640d040381c20130141c4d021030081a070140c01c0b00500a50304e03211102070f00d0040d00010104080e0b074008901c0b40c50008020301c00f0544160b50700c1140c04100c00c1c01000b4524403800c11a880d00c03044140c46d404102a0a00d01c0620b60104d20140228400d03500c02080620300c03410405140001d001d80c0d0110342c024403010b0090714180d0040e0440c01d80c4001c0001e40e00c010f00303a4503030700101c020002d8003000e074840030382200240b800c016100045c41680303014045c0d1403031958020000c080c007030450020440700d0942c0701503031001800300c62222050300d201c0030365482d500c1c81c01178081d28034410103440d4050b08a11640741d841000c2120580d02450311100c09484454034491108a1a800f14844070100203000400042c0c40411560102450320b0b11015124a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 145833453 1250 145832203 145832209
    0x2010b180f0601091a16080307051804090f061a090c1c0b03030423060a090e15130c11061305100b010206060d080c0106090203090f010506060d020c10020a030209 71
    0x81c00340c05503040000c0c01c0010044540340c00b440c0400d0310a60702029031b5801030701e03204105403d00444081c1008a000050002c603607001002040200800001c6040035005001000300301c030721481c0042d0402c0086115000001c9180c4e2000140c10b84682000500480701030114000250441c0d034405640000924481e003035191480900c0c00310f038811028403001e0303201004240c681c0200e00c00c0e4082e03080408505064503000c507461034448100913010710b8540100e408001c2481025102d180c1c03041c1c56210200e0030480141144410344840904410840300d0801071000c000e0501505000400032301d1410030f5180700c0140700460083c07540c2d00340259004102d04046060040c000c910154480c50038000c0b58050b6004106250b00c8034080f68601524082824144501d1241003003ca869500e00440410281030940c041c60140c00340d9800c03035503243c1701c0c518460b0888a080e601c407540a8010300c8141c0a6206540080c240e0b00319040c05d580804040042800076078000c1072000000c00e0300451b024240c0d003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 145834703 1250 145833453 145833481
    0x60411010e04050c0f03040c03080a032304020a031704090204080f250e040f02030307060e10230711060408030a1104030206161e03050c010c1e050a02010b18 69
    0x25400311402c025500b4014413649a40c4601d84140c501d890b4048001410701400811440c0110b030000059645c0b40b0820400a0007812250342c80d8031b05640c107210150012002e5002d003882150b0262241c07a440c0d003540c0f00c26042120490490340700c81420400441c401d14940068070003881000014003a4000344e8843c1d6092000e1500701c08058021391094000c100901e10407041100c200c004000c81d19180e90030f0255802d03107200b40281d0180300c00039120341082040e03841390b198124140d040c3c0f10f0708600ca02c1814186c1d80035a20803042c015840180801c060010801150441c1c103a06150005483c2c65500b581080300884d030645542320040100042e10565002d41101d901460103c2d0385440c5c110782c001041070140624051101d81744c640c07100100000014003c60111140302c940e24409051b2500920552101c010300c2a19402c1003107038070249010702e504509010b045181001445004402101d00782c01001c0a0002c541d04d48401003100d844100365000040312001d00300d005860704207c452024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 145835953 1250 145834703 145834727
    0x604061d03030a1d130509030904050c1c0515100203030a180210030b01030603051006030510060e0c031f0e0703150b031503070b040e25020c01050a03020c06041101 72
    0x42d03001000303901d82036a4080900004080c00c0c016240341c081d007074400300b0070280c5d104100e407005516220500c41a894000054680b486084805100340d030f840c852014564010035170700c0b0440100381c281d1504840749036041540d0084503484a01326404502e00041ca01040682134613000d40c000105026001400d4003415500181d100741c25603044a1a5002c034070301e050001c08240030541e80e90700098083c0c0c42600039900450704034088980c20507102007a40001c0080f44021100c0d4801c414000c4644c4665004a404440081000e292150740392010140e440c2e00c01048200d40ba036480f40d00e000500241c6a40c03a014010b070b600c0e960414036101d500035044070404200044041c400140800c5640c0b05039049942c03010100c0b4002082c03c0003400488d00d8650070350003141440a02141c00300b034041d0100c09080c03081801c0c0d08035103429140511400140d60310b10314540016000100c1e014800c3d402040240758000640c9401032038a0701d40300310341e4144601518111804800740910743c08031744c2e202c00c040d012 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 145837203 1250 145835953 145835959
    0x1204020a143a06061503090b04080f2101030c08010510050f0102010207050105040501090b1e0601050703090806190f180f020a0b07030e09010e070c02040e0c0604061d 73
    0x400c001a0004401007500d0410000d03108500341d020120705840d0608900c08466410380e5100c420302c500e4494080c0104d400fa90954982c51004802c5d09446805403404440c2c00c8020034800340c1310b613120f0702d1103a8005801083d420004001109010f8a40c02d0244201e020421a030341080d411440c00320743e103a95a502440c1d050381001e05109040340ca01c01c940c4115141214180e050801c4c01004ac0c1c064014003902030029440d181c20030051141c1900700d07406180c49000c0707920040e51482541c01c5038010b00e0079020030b480d540100180d440d5004200405149001c0d04280340713184d80c0c2d805e6003403802074101c50b034134820350300c09207071008444d90341c015018001141e08013030200942c1d600c0f807d80c40506000c000f0f010503008126001c10b41d01d80240d080b0280c004c20201542d915042d08018041c50340c8001424003075100140000758154180311428003c00d060b544591040a030703a020030000c0c01031904005001e0113529a00c159559494004200911045d20741c000c0c0f045038400012441c0925154442c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 145838453 1250 145837203 145837229
    0x5010e060f060a032c030405100906020a030e0d0204020a110d030e0a0305090a080609061609051e0301110408010b01030510030c03170c0706031b03060f121401021204020a 75
    0x141d19a5480180c40e05500c051400103000c0e10380100b111003404503500340e002003c2d4580858802d08002000a0003a00e000303480040c2400c100d0801210410f03007920802c2e00607002403500354002446030074070503000c400045c08800c1a0340c2c44e80009040340d0044091802143d040440300f9809a81407000410030005400c0401804141110643d01d4806aa1004003000300c0011942d80956409051901402c12030049a051b480c00e401419547c0c0011786045a101303144151940107180305204150503580064000c81c1c210007a01070314200f00c0f1712240e8140d410f540321010344020b00080c101501c014802ca500208001400303400144c12584050446c184034003044406102040703551850004aa60201c0554521041c48082460340e005900c038a0240c0c2c028164000781c807613850742000216440c032098180c031021116170280d00304c4615115400d144020380404020b0080801116880d60340950907250010650140050881e402070328103c0c107540307502003407005508040750223401034504810300341 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 145839703 1250 145838453 145838479
    0x8040608151f300501050102061018020a030209090901020310050307140f03160e01030201091509061101021c0905070b27010e0907030903031a010c0b1003020603010905010e06 77
    0x2e900101c0300c020a02c18840c004040c203460002c0301c01c1401c1004103d2200350b8010b000b061910003d0642032040301d00501c9040c0200e4040c14508011801301c841c01801c08446002015109000e134000008040c245582488015900d450303c8400c148909a1040010f0344d83c039200c100ca8103103581c2504038902940c44807070148280210030344003100720781c01111074841c5c85400300c0019141220381d07810001040f20a6034009403022407403104030b060b40c1c803d880d1184c2e843d8840d0035904020381340340001000030304218070400c00c0728001c100004044490300005403900c5a1340549504540d40c0004030300c030701c5688a50200500c4003d12480d8050501c0d41c0e1074925140c44d14035013030400558690410110908210b03d0150b6070700070050070480d15001b91070003201313240040300580100b841100036008a824146881034040c010394401c0122803050316a42c1d0002c001d601d8101d40e044000303150528008040401001589c4c80d007000d10700820003428081803541c1440112000c40801400a07805190414441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 145840953 1250 145839703 145839739
    0xf0d09060c02090c030c0403080a050901120903081501020f0f030304020a08010603050601062f030c06090105060d061d03160302070e060a0308130e0901020403020f0612070f05070804060815 83
    0x507138104684040752501d940725040740e241c081c42107900c018803000c4002401c210583d0440302030280113400343c0700e010901004441450950300e10b900e000340040c2012b80001c5130040300140c2e070351314560b06104a840700c017604200289000c061002d00c1101d580003104010031403a10000100182907040020b0011a1441d51001d41d0780006007d03980a206c10b1503402e0340380300e484400202058500c1c224800c602603180407080e450ba84000e200318118001e80c4005800d640e0140500c500501025001e4508130540e07480e52001854a412862550032400c4103010940404001401040300e02c0102654180340b1031401030314001d1181d100b41c0e00300900908101240d692400c8042c01c0301e0b044502d10780c6d2180306200207060240d268000c880041d85400c01d018120034150701034801d0764829500d484501c0840002c01100d070190402d000c402c034500500148400d4072400c01034407240244d00f0034504240541d078030750200b0b070015040880050361040c104101201180503500705410142e0300381d0b406070101110707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 145842203 1250 145840953 145840969
    0x138040e09010b0603040309030201031a150d090606031208090f0606150c07030c091109090703150b03010306021201060c120809210d060e101203110f0d09060c02 71
    0x580c0018440c400e00090181c4029000b80c890500018512a6a40780915000d070205805000503400245000021084603411035042c401030711000b0905104948944811007859220140074510b0680341d201a1002500500402000c0d604c601c2006409100411000b000385400030850301095002140201e0901d001141052b04000250780c06107812010324010801c03031041d010620030390310641c1d4001007802419540403090350f800076020320500302c09a00c04c103410f019200040340e12804540100354140d020340d00c600c007161403c003003008c1025680d030076140464000364801d0f5500c030b4001800c1b030510b0110102c81409040700e030030301c0500c04401c0d40740c24a003c1c0306280700ccc205001d48000450007048003000904003510042c02d4074074601c014100c1001c0c0384e80142c42c090f01d400f07040c4a00402c1c4144860207a42c85801c5a002c0102c020f4a0100248030010700000c2c2501072103820070001048907403d1042c0c849403180710004150490100c00000c242030704070350100e801c02c1121404000141d0703440003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 145843453 1250 145842203 145842209
    0xc090301051e010b03040c17011a100e0d0f0804121a090a03201617030a120f09060203070305071403071409030c0d03080103121b0204020c0a0b013804 66
    0x5100ca46a07906e500d010f0400c0c01840d00880f450140c60702e13609040c030605401000240022020321700a000b800c134203100c19a0308c503072108000719030740181c0e540071810030a8095140e18021901c403030001d00326807100d10107a07001d070700311405104091070f62606000011104054220414062046602e000007001d616031085680042c00c11016262203d0718a40a508070041d58503038106451004951805829081400f489400036002c000718103401c1c242004000d95070710b01e000341c41e003122081c02c000503640200b025410030300000da44c03060100003207100d0f88051441640c0c55200028030342401140944406000b5560b0030000c0410000c01000701d03400f03820b500740e04000c1024161103251000000341041c414170319003504155520744d81824145d1052040e41240d0241c3c0003180d00d07089032a0b04035144100c41180c60403401c452030200c0f005041030360082510042c040c06841c05884140e540d00e500c40020382c081c4c1010100411092404078070780e0801c521030100300080c4400d103154240499075900130741c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 145844703 1250 145843453 145843469
    0x80f0903040303051206010306051f02100b220e0a1a24010f0e030f0a030f050c2a040e07080d050702030a0b060303070f0b010f120f0210170c090301051e01 68
    0x2404106c90307034025009031000d0400282036207000501d0808461004082200403801489010180f035103004891141e80c9611101425103140d0242413480d040a41c50f00c2118002a01d54035941e1103040c880a2106202062003426003071001c0c2045024401d00e40360141c029681c070b081500e41c0104200403020035820f400e50a00700000c1040e0302540c02d503041214500718070b80500400c416040c0c818001306444420510903120b0400c00c65004074110350038020070210083c0d030351003010146419243c11624551096a880102d88521065070114040d00c1c01341d2502c030320307951000405012400e01403000c25030300f01e01454407609104140d00026900c14103590080c194103140008200103841c140200d030b072020340296049190000901d4606517a9030300b4410754407400d03451480460b102440c0440f51010030b03044100c2d07030003501c07494080001c440078920307100081c407064440c0e4507258101c0b07050151140c84c142443c0d50b180c42c2800145400e441009100c2629059000c0c0c04140e424160300549040d20255 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 145845953 1250 145844703 145844737
    0x31106130e06120a2907090504021e07060c030612030c08030c040e0403180501090305060a05060111010c0207050405060406080604030c03020309040615090806070203040506130509010303080f090304030305 90
    0x4000030888001248a0343d03034031400b07401504414000300d6030903d801041111240411110800000b030494074040d16aa40000e0641c94200070515140d0003510601e0841e12000e5610325134244005c0d440d502c0303107500710b48103506c03042004041501841500014200c800440b0042000d91b80d00601c08a18890014207144010001c00e606042032003e032170252050f001c88440b02d08050030040d010905028404100407844a030200350345d4030803419002101d9210300281010b866522070b000c040c0400621603410025510000d0000d180e0034000c20204802d01e40103800500c0c201402c3c042a00c0c1c0c0104907034000c505207101000145c0700001e0303681d4020740601d0b03c1d11501a081c50100d046104018010354040d0600b000403a4003210102158003016250700c910224954031503000d6282d14003100e01c40c0258005210030085801d101004214000c0c45d54240c000c0780d500d035030004004101c2a00b095000440100400280e100304400c00798205504000075828140b85030b600909501c158aa0781000d0840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 145847203 1250 145845953 145845961
    0x1503190501090605041a07090605030c0d090c0914180322050607060b10080603100b01110d0f2d030c0c02030106180f05010e010b07020a150801031106130e 68
    0x290b210141c9142d00480078400c0307007070034104108443e034801c0d603294003001c6800103d445940155110ba0448209445803070a555a1100b00380c1d5940001170344400480e103400404001800d03034141580070741080d880010740e052208044d00c64500d00200104148a9007521841b40c03090300005680402c1c035001d50301c4c403c1444401d040d411028850b40a150404408070705203041040681081e40038101c01d50b8480c089100b83c05040300c0320502a04c050f500768203d848480000d102c43c2d0004100c0000606000185041c0e003c5150f01d0044101c83c0f100c0029080001e54142e140c1c042d150000880c8500100c0f881103960001c40384170b2001881800f802d143d5140941e00c401c174050016584ca00b03030001c0082000f02c1d51800442001c0311141d5a0781d80203803900c04032001c102524031449051315200b40c600407403603081c1b00c64990703180e0052030141d0b40842901000985041c44001e8100c000c8259a82c40c90254950700d0103100f01c400403085680f0610083c4014031104070b680d50140b0461350f501c00500000d4039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 145848453 1250 145847203 145847213
    0x108100e0106050a1707080f150f070e060f09032b08010608010902030a11072001030e030d05040302010207050304081b010507030e0409061b02150a0b0306040b04030509120d08150319 80
    0x181681310407580c0c008d0042543c0d45079800700307010700c1000f0100b180140c5941c03070942c1e042100300f0890303080002c16140501d01c021401e0640280a031480c40d1900145403003413080010345050001e1a03241e074410945680c61600c0120b1101954005400341440d00f0716506103079014005c408140548400194040001040b8083c00c4e00403202d030302c0c40300c2d642d141e40c1d21250404403500030190300c110800b0507543c21403041a501c24403904102017541d0028609100418a4107806400c0151090f021513409000343c0022880030300c0184020002d04004054036500001d214140500c4560082c1c1400b0041c0861008203400031250004204201c03400505960300781f07040c000415050300781c81551854003000101c1c69400081c1d068400b203440c800105c403686c402119506844000c065542c041d005040880e0028001d400c80070781141c421b0a044e400c14072100007003010a0440c1e0540340071030b400301c98007070005a046456903405c41c800d031150380003803c0d150010a503502078100160f100744240c004a00c0a210f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 145849703 1250 145848453 145848463
    0x180c0304080a021e01020309010b0102160b03150a0b120901020a0801060819150906050301060501092612090f0405040c0b0901031d213901050108100e0106050a17 71
    0x400304ca0202c4120600c001183c003d40003119410701c03942c070b040040c0070b4940c0005859018080f2007041040c089080c40f4403500e8a805c0541140307405480c1c1d2480c00c0d0182d0382c48120b01e02030200004030b161250150903e840000001804108085c1d10400040602903480704031181910b02c103042480380e03600c500301c8400e00c01140b1000701502510704440c0f040b4840c0d10b8050300007111400b46003805211340705c10070903089404510485010820b108410003020002501c00c0040c000c1d140c204440c002d05102d0300c207003024501d0118032201480082d2903000c03031078515007040498038192800c0001c1d1070159101c1d2065001805580350030280400d0304000c503842074200010348031400200d80b8071a01b5003600160781d14901540c1081410544a030314440582e150f05482202e401090343c105003030801416000c898103110040024100b849140341d08045090103002e0017003158070010000c00b02c0d00c00b81e9004a4110140d030161590402c00100525952000d0640a42e0798a090200d0800e0031208494582 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 145850953 1250 145849703 145849723
    0x6020a03020601120c141809061005010203190818010e0c210d080a020c0307050f0705100e06031305160302040b030c061801020f1e07210f0204020d02040e06180c0304080a02 76
    0x540411001c000d40880d009c20100e0080080303004010009841d0750040e17880740503072403003002c0d201200b0700081021071054a103540c0101030401d050184e901c0b003c404a0070348900c8441c2001383d5019000c40e412504180c50039590120302100c044101c3c0390202d81280e1038002c0440c4604c200607640000c14407000d0307203504030b440c150300c58007c803aa100740603d84551030b9007841c2140521802502400116030504014142100501e0758a14001d0082d41042001c07030b400c0607112514100020540c1000100d00700318030280001581c60080100d480c2d4030410056400c000c040c24001c2d0007000901ca800d03125001565065028094901100d00003000103d02d030504e01440d01c509071040d884400c20000e070994014050000800c145c1e14036a4680112200940000e41002c1e850400218440c020072035400c41c142d1514070042025103840c14440ba51426a0003542081d0381145465040c00001c0c5020030602d40000200c242822541c94404103c41c500d00000780007626120000640305900c82c03091102d0210 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 145852203 1250 145850953 145850989
    0x150e0d0e0f0103092a0e130302070303180506040314010c020c061215060a0504091514120f07060504051201110a080406020d02030a0c1b1509031806020a03020601120c14 74
    0x1080e2039404461104017441c82082c486940176004100d100018055004203a50141c00503d4418a96a07040310310030050301d10b800c00d6240000011800359540030040c402140a20b503812040d502040406007164070240204065610103170021025445060554203080d070100030002c0c259483c500f1b01b880800c40d41c80c205500c000000b508080443c2c001340a0020f031102d4907001c2003109618060b03205182d490f4091068a0340080000000301d1402c2d40003030100418541c155440350695420b458a007007559000a00420008903080c050340c02c2c80440c814940d12120001d2101d940144408a8540308945070362003004850400101440207d4044032091134000808565071b241c2006010020040c0c060350b40001511040307a00c50002055a841d1281604080d007000c460714203058040c01400b2445088080c0000019400711040400c1301034070060002e42c021740700b00040f034034000342880016003080146c08018001c2001003003120301d422003a510600d41c0700c40c0e501c04070400504490010021101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 145853453 1250 145852203 145852253
    0x120f09030a080c190b040b04020303070f0308090c0a0b0315031c0302030403080604050411010e0f090906040501050c04150311270f010309021c0c03150e0d0e0f010309 73
    0x108000c880307001402048400f078142c49658006003400c10350034803a801d02a052071292004600400d828420b001c0d000b0340300404032407400066540c1c0c1031510040f040c00360b0229040404001d000709040c00060158041202d50b45d103030909214020125000151400102c0c00c05041141141d8404103c5242102400b0041100f05803144d100100030754400c40c2c084000545650101d01d4505150184a001f035a025008003007000030440110380300b142e1140604ea108400007a002020b45410404501500c0d00c0800b40c542c900d46410403a00350380c000b401c401180c04007003000304042e41c204002d04002c10b540b49400300c1c46910b0074000d98154028000d4032035071080c1c0c90000100189046e0005000d480d829940425100b0344100150b0131a511b04070081d4100001c98480303216810040d0000c07040a115041861840d605ca0b2926000f691a10b441032030102da07070b8881e02804840c100842c846101191170075030003c14010300464150700394007022038140b544131114441000450044c00c5482c0301260341c509 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 145854703 1250 145853453 145853473
    0x51e130905090d0309050307111c06021902061b03040305040b04090903090e070f11010e15070201052d100b13030b090a0222061d070305070809120f0903 67
    0x80c0040c90306a074865030030301c00c82c2c01454540c2d010340203000e81990000080d5041072002e45410b5420b5074555801c61384801100d0855926903010307248000b005003c0e4030300688815807541014000581c0d4038504c1c00350340c000405c0284408030080c020f24100c0c2c00300406034480d1200c0c64181c550340500e1f005410700e20008640818002480e600c0b4510441c065501c00380035564909803007100b00025100c1d0341c00100070b04074480d6110f0042802c94454503444000185410256a03681c0c105a44021442c8040702d0701c209010030940c0c24041c80d03802412020302c00701044880142c3c0c0d01c444580300503c038110303a040d40004512040002840000b00130710790b0010713038422129a02d0107000003d40000c650031494400400d0003d0000507251103036690240423445460451040a8101c01e50480c400010340c2c0c030f90401281201700585100e032040344080c0d40c0c0b500c9090000700582602d00c01003102c01007091050070480d03840f200090424200030720320f000683d0360b1220509421503101d04180d0310b130140b0400c1065 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 145855953 1250 145854703 145854719
    0x11e061a0706020d1805061e1b0906030109020a1713022b030513060e0607060b0a030606180c020a02030c09101215061203021b13051314030901051e13 66
    0xc05ca03254030400a131031003940d806002015079403204500410050308a400903078a40c0160b401034481e9030050781018180f00340000083c01305e5000f6080f8144107034002c81e080349119006640703000070000c0301d440f0010902e40147c4044a04400f07100291041503c11010b6400001151019525040b01580021452a1410060810340c4a00c0012740c00c407007086400036081c0d100d2041005010341c000d0049107003042c0b0b9202c4401409060301000d901c140c03880ca0000c0080d0340d510590009148000c1c2e8034495580c540e09010803101c070348a518043d5007041d0307603a50059401003040410700100300c0300c0714411340700c01c1e0010044040b5500041d0300410329440080c03d12401807001000d0305140712041c010103845032800000c0811140d0020003507031002560f00c48401e09900c9042120341c0c0076000744500139140c0c444406940f4103840120b1020b12140d549000e1100f10031401b00310741705400056281c420004c000030410320404207900c204403c1105040c1f10740c0e21034001c0b504650383d219000480c181d03e0b244030b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 145857203 1250 145855953 145855991
    0x20a110609030a050f062a0906120708090106140f0d2d0203010513080a050a020c1302090102010c020c150306180c190207050607060c140c011e061a0706020d 69
    0x7900340d01c6c1c440c000c009812075401c00030030140c1c40c0b10040034000d00908590100c400750448000140e01403414800348081265a16103a0312540349039552521340e040125070603003100c0c040c0e00401600e94501b55840282d031224106021816015a50140ba44000d4240041850034071b480c0707404003241c9880010082000318010980d49030085000b084151201d40074410014150a00100003040a01c00010190300030070142c12445900d0040d90360540304d100001e0022314406038a5255036070301041029065034244104003a07501c0d940010f014600300000090440352056240b0410f5180000020b81c041c0c40768416103244042090341c41e001c030700b0321603002052a0002c2440e501d00c02c881d1700b40c00203941e00c00070f500e2080b20700c00b400040c0344c056945c0f10500540100620202032020f0288520002c511602c01000b41015810001410b085079031032001e240b4900d0141074600318200081480011070400c0d140d14508801a0040c1c0d84620794600310000e80078010368902002d01e00f07080f600c0c1007000014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 145858453 1250 145857203 145857223
    0x1020301151416020111010b03072c070e0d050f0102070803041e020f0103050405190c15020606060d050402010c08040f0906090903120e0309060f0904061203020a110609030a05 77
    0x1622542d029201414030068056003005900500040700440c0165008294541c0079450b0107001250b065034450200c0d01e4021950f01004d80e81c081c501d2040d06510341d100030441610407001e1421564104520300402078045050001d11403841d0082c030b03100700300080050014802c800d40c005d41d1078001034100040b0540003104c00b51500907007608040d041990421401a030641d00501051006142500460090000500496003842081c01d12100605041c4c1603c3c0781910411400e4005030802840101c0c2c40c1c40034a00034250b601000c24800d895450b01d01f0390f5050703110000c0000f011b40d5940012580c045540101038510400001c000c03c07240b0840c410035041d1400c0c070780d00344500769480241a040354480c54015000a60701c10070171080c0d01098000403e04000d8004490030300100c003000962952103081602c0000303200083e00c220a0515000701e800400b406164000728040a40f006921103440c90802005921180740c2c89226a8486081d943d40c643c0c05011968204079614000d5500e2814130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 145859703 1250 145858453 145858457
    0x15050706150609080601030b22240c0e0d020402030a0615030e0706090608043005030402100807020a08030a0207150b0406050f10110a060c020a15050103110d050c030102030115 77
    0x400104d008000011424101c3e503120100002568a00c1d5800080c040384482807020400b0300012900403035145000f00c121100d4148104600c2c215095100d400c443c0002061400e004007020000c3c480c0d82c03149030a1003a103806450250740d83d5640240700d00100794a4020305120968031894a44640e45544486448013001d0125020745484001c00d841c042c2c0706105420000740154005000540d915122000031066007558807585641c02d1341802c800030410303418a00095001c4104010b52a24600c1101407000d2810107042a00704600b009458100448000d8007020b000030218038100d00540c11951400e40107400c822115441e20b109070090288540c4584c4101d0408001003020302d0018400c1d25283c8005100c0c0c00e884500340303c180d0f0744001c08080e100d854015580404d02003a05406103821040b0036601404a4400328030340060905000015428090b2501c00107000085a0b8441070342007100856909d5201c0c2c42520300b003440c000100c1c83d0303d90994008800001c0c00300b09041c03080184101a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 145860953 1250 145859703 145859717
    0xe040b070f14040506130e0a140c25110d0c08010e1b01030c0302041205010b13110403060506120a051c030b031209060d06180506060c07150507061506 66
    0x620100c2d0340e82a0b8096240d0b81d85000c11080285140610050a416001180d40b80c1a03903500c144520000104030303241e0301c0341e035119039000883e00b080310300250b40b00d80c0d110940c5042051800c000152042003000c1a541c0c049185050004e20210460380c0380080e0f001454400442160b2a01e00c16007a2207128040140d800d001e044e4842000116800e44a20003a10807404c91150140044026054982c501c00c1032682c00c0001050079102030449000d0385005e03000210f1440d4a800c00d01069084224492020302d29041c40398081000440c00c135011650002408501a110000090f01018000c0b080d2016403107441c103400c1c2080b0303000c14071000c0a10302000e041c1c0c0700320b001041030301583c00c00ea40203503054200b14100407003030f40f449001d0b04070814090034280c188170611076503030201c5a090b000040c03040070141d0041d8040b9202e00400754070003401e949190400c039035150199510316840c0506128034100304002c048440c810020b440d119508910180410b286030b0121070500303480d60042030001620 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 145862203 1250 145860953 145860977
    0xf11040c0e030a0818190303140304152012160e09010e0702030702060a1205010501170403080603010e03070f020f01140d05040203070302060a12051602070506070c0e040b07 76
    0x5412019039003070302402400d5004a0b541c1c400869601424140e0644550080350105a4481010021041c094070401e001800e085044c05051064031142e40c04240c1030400400000508450200c0c1282403070900100f1400703c014030002c040200da0004294041020404a0160001c40b1006001d0110760411200c0f0510703190044504c00c1c0c609080315041f20708a40100407083c0340c0b25070264001c405106407410038409178000f4415910082c0c80c0400030722008000911074a00703101340703801420709027810b488070201c4088214004000038800341c24010303a640042c00b00d80b401e4100784031000800c41929031b17408082c0b0709124606452181a0300450074800707100d080e5401074000c0039115207819a00740c02c0c11031902c2c030240900070003081260107000d000000001a101d21014040c2e041890315540100d403110a582170845034020803502e2054108144071030300d2500410020306603581a038015980d001c407414520b80028295000e501d24041c11000c101c28400d2100d0003030301401141e078400303002043e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 145863309 1106 145862203 145862207
    0x230120030a0504031104050103020d060903032705060109090809090709031a0109053301030e1b030607080106140d0f0c050a091a03070305040f0f11040c 67
    0xb03000314042c0100803082040020368903040c5c84c204503661458001401700301d141a0054529642d442d0366005040c0f00b0781003c00030001052000210a83c3c55080030424002610191414013030980082070802c118024101e0942e00403c02d079017802000c804010038102c018242030309104050b1400000105d08107031182c80d801400d14804040d41c980b80c0403c007595002040c042500050031036920b81c28008aa8002083c06030f0b4072004500581d0742c005800400c00019500d100d40300e0240d0a07000b60f2288030329103d03510415004c1e01c425854504041d524140e081c0560700214084030020584401180c001e0a801c100c0e00a0100c0c4101e4500b4030203080714200c0d66200c3c00554001b0744040400c8e00801c0440c0104400000300d261391840380540240d030f020240200c0100750700c030780110301400107140d125040c2c29040351800246030440d02d0060781d4204490b00e81030080781030403511725440d8 = true := by decide +kernel

theorem cover : BRFrame.Cov 145683453 145863309 := by
  have h0 := BRFrame.cov_init 145683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 145683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 145683453 ≤ n) (h2 : n < 145863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
