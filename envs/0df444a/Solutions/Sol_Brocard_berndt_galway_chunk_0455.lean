-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0455
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:54:25.72669+00:00
-- url     : https://prove2.me/submissions/eb07748c-8d33-439d-a9b1-1c5e812ebf8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 81654677 ≤ n < 81834533 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 81655927 1250 81654677 81654701
    0x1b080a0803130c08010e030405090f0610121e0b1801060c020f06040504140901061e030f0317040804050102120f2703100b0301060b090102060705030603070b160302010609 75
    0x40c503580b585110103a405422410503510700380702102c00074090400740f064400c0d0306040c2c805991500d050004200e1001c4000d084040d0029112040c00101d42d282c0d40c4503810b6998604006117843d00b000c0313502c2c014005244000304000204c54010009e1599a084120070b44021203000c14100d00344e035040d4030780710020b01032140018141240e420040c1001c826004041e0070081c0400c0c20540e60700005410703036070002440310500307540106111044200b4011407025040000038490301811010801c060600d01e8030004d442d032074080840c401418003c002000d40880d8404104d0b0207890141082900c560161242c24014420740400880c2d0b004c088064410b80d0a44207010303890200541101c0d800706010996024160700030a07068101036508015640031780c6003940c0042041040f0200301070844490b07a1000039411010807010020f41c0c1c0c045883c0c0c0c1c0c4100e035070034856260b49490700403900c0e1450940144495030380c00140c454a021692a004032400d02c82e038005d000742c6031039464a8040e58400702c116 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 81657177 1250 81655927 81655943
    0x82e060627030c06030b0a0b04030602070b0907050d02040b0a030b01031b06020d080403030c020c0603070315050f06091c050304031a090a110111010906050f060901140303030f060d0c031b080a 84
    0xf4403200e1702c02d030440f080c01d034002028000c0c02600c0343c4c41c02d0100d82c45a482140c8413540012220200700000c11309607032060814024007100b500d08400f0400c00c8021000003440b5594440710b681059440e182c0c490091600190350080b50745c0c4900d4059190001038003040d6150201c480001071862000910065036845c0703503206440c60710340d682c0980290003400ca80c8020340c050b511000d141610340300082c61041c40150340104100e102d12500d24110085a0030140c01480340301c400100d56103c000c00c40c6c1010105881d41040c20000307510f03540260710014001070460000003000002d1045056085e070380c0f0000110b6064031520fa802c2501e5490202900084c80e043d5048203440c80d941c0600c1c480c2261922201c004141c0d00d030f0568609040b80c0c01110340700740015454003130091a05164070303910b015103420003100071074240b40d0b00000e0307981c00000c00c1003920b048442c0c00200c0c20340340c0100020046900040704c280303980d01d0780751560100c007076620100c41680c24200002210040000c014640d80d0700a141c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 81658427 1250 81657177 81657179
    0x615030d050a03021225050705030a080c04030602030a09030e030604030f0f050405130204061707141b100e0f03070209011802040b0409060503060709082e060627030c 73
    0x1512980c002c140d054007495070034003002040111740c0038002e1080b42c1310404c001c807291342c0c0e4080c0c40d040c01220844004021060041400240b000002c1f03425501c051704002030703580d17528046001703103111719080106918004014404101c4107030f004241000c0c03194454030f1180d41c41d0b800785990781a00302d501400041c0d0070811658258000c50284000e0300980c5010340ca820340395000700c3e503140c0003590070041895000400f0016140e03c00101820254038a900c007000d8201284d0040680c0c8011401d131030706040009410507500000031540490803114010b65003680b00c6050070074010500515110518001c0800c1180000c40100031964010f0b07000b01519400c1e400c21160002e030100341001404080d90801012400b01c2c500341c0039000410440f8408650203061034103050034044081d0144051000b00d03401071007141c2c0c02140c0d074a209800100d90000f8440e41d882e10045001d241c036164018949040703070201d074059100c0e01c1304030b0124500450640e0074003100030f030750000f0f001c03817101501d20102403c2c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 81659677 1250 81658427 81658453
    0x50915092521051915090c082410120908070506070905030d050a030902030c191419030b0403020708010213060201050709030209010902090a0801020d0e061503 70
    0x60066041514684021500e150008141815100342116400400c1c82241d05a42d0301c00040e03451160300c03102150511407420582c01200ba601a6200600b280c0c42d200c01801a03000150038008004186060b0241b000007017040002e4229101600d0046108402c003560000f010854034020031540c1c4050001d0303c001001e000200c2d1000d02040711395002c103071200c3c294004189120003408400780134070083c011a041c001c0016054000960086021340c025009992000d500726054035400862400c0100701442c4c1840080d06001080494070b0b0300543c9070044540b040b400c001c101c4155a40c0e0385038006405100c0e01002020002e06052180f804414001880010b5030819080d810522a00455062035120040d55083e42c2007620307446184000f030b580c100f1696a0901680707400115500303040c11070750300716004a8103681c2d050040c80c004640000300501940c44452400b0001c2c07101000841d1180b00c640c451001500c00125410201d1046501003220a609402c125212400040040079044048a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 81660927 1250 81659677 81659689
    0x10050103051002070804030b070215070c0b0103031116180b0303090d1e080f030402010801050108040203070e0601020a140f06010f08030702091509040b0f0c0a020c060c0f070608040b01050915 84
    0x1c40200c5c0d0020080c8000400181c0d48003140f400b034007a5801402c00c6a0344c802c1440c0c50010000e06ca2801c020341e8030340302c8010690014413a41560340500d09119000d0118114500c2c2800310301100900010034840018a1840d110407451003141052090020402440c101a41c0340508040d031a8031460101000c000111300c4d5550b1041d540d030555840c00c01d50724507210030b026500204020082c11200108010464ac0d0042680d805050709007440d0810741000e801103580d501403401044d02600980000c03c500342c0c000c00c15400030a6000700c200e6803500b18020002d40352625070303100701c072240f2820001003042604610100f081c1e80070b0b88000c504040e000e8082004801c00903000b461060901d0807116035a0700d0f00070749240300700c0c090080c520160500d46a101c00481006181c80400d0500740301501020b9404920a29074060443d0715030b49031510b884145080940a100d074110501c564a0001400d5030013480b070603c5940101112038007aa6508280610f044003210080401e841040520410349400d03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 81662177 1250 81660927 81660937
    0x150302040b1818101406030f0a0b0307080304060201200c03071203060306090f050d0e0d060b0f0405090706030606020a0c270c030f0b0406050f12010f020a030203010810050103051002 80
    0x18070000b443c205816480710043c50a0b42d261081c0510020300f03012182007462803104050342030301da052031850010101d000019018281806454444454140641e010415880900040300680350303030f076030f8881c4082d008007001059101108540c00041d85e03410506010303520200c102c0c10107545005500c1c0d60301e0f8451505e000441050590382d04e0f0210114645100e0302d103800c1d00c19102c1c541d0f507210f1402c2061400305503003104400c02c02c07001c0c82e2803660b89038051113410741540003401040344444440040d90030108240b213650040e2070801000885000051444110788107901c0c20444140c492004030303242c040d000c201a11050b4000000c00c800c03807414907081484000d805501d0485141f80118205807041408240006078a4180800c0382d042c0314803d450321b449048408121092500340807a410b41a1000110310691615200d0000310300700303410621682c40b20740d208560390240d6640141c0250800e000d040403521500e140d50000d52101c2c843e6034162904400109191104039502401950007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 81663427 1250 81662177 81662179
    0x2a030801121707140c101e0309021507031e0206010e2208031e01140402031b1201030c0503030307022d0102130e0606040f03020409020d1b150302040b18 67
    0x30b04071051811806200030702102031060041c000c1400e00101d5207441d01c14807210807072080d501e0289410200ea00400049004030040e00340603081071848805030010003121601035000010025025003003003030a0010303c3c00078480d031111440d0101001c2249440c05400850202627400440144498075a407020b00303520011419002200c820b40041a00000511141c200c070b0212000c0140000440840e900c03410640004090380500c1d0b142c0718a03d2941d510034a040c80c021079001002c103840102d0811030710551010348580030b40d92849a054925003034002d11050720000c9034540702050610340130046a0140200381d0040c030200c1c1140b001c002440411001035607490a504a51001c809030030700103407a0418814103614009031038120540300180f4001c0c0030a1140500304010302500310b10a1400050b80e4066500060100c45440403842d010f5110801901c0040f0406880e4865119881550b090b2101c0d5544214101c0d0351290a8013640a903004003605080148460041910401d4180e206400 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 81664677 1250 81663427 81663443
    0x10e011401230d0630020402160b09030904051308031f05040f020909070207060816030f060801050403020f01060f06080a09080f04080706050301050d11120304062a03080112 76
    0x106455020005500810600b0809619040c0070841050074071040f120804030401603140103589110304800900301d0b074000910456000c289030600c907403411400d00b080c03a4484610b1038032f130070013030342c420b941e5004401c4042c82281840c0c006145000d4074a5407d000d02c0d44544003e0450300c800c140000100c401c5d500090344400100d40019080d51180101001480c00000050303a0303040d40b00620030095001098082954402035042103003030b82c461a5250701035030034a0b8600c0c2c46181e4050407005004480c401007206401e0600c0456660300640c4000e01552003a004c4030f4032180302511031420713901a8420802e01c0717180614204201c43c042c609640d07210300130700e03400900c01c481a0394102440c4c2000c40440b41c0c2410101e014410a1800c01044019220a082c11070441d80340900084010f45d4001c0014000c0920240e0b00740c1c1c170307150068010f10100225054030381315501c805004104100c90080c0031030011380f590a00420502e0710500100c1c09406540b2030640781e003800300750070101c00c2c0c07190121506a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 81665927 1250 81664677 81664727
    0x9090902010e030d0509091b0f030a0207020d080a26070c0f020a031211010e060106030207060906060e0604060b0708091002030c0106060504030b160801180b0604170105010e011401 79
    0x16409100d4034071341c000c65440d82c60311141030009120f00958002c0ca021100003c445003032881403d0031098a8001daa181056650b81e5103548440c0c0181c000e104000b50008000f440b01c0c001c200c01e01000e4a4000c5150b0b0340c4c0c5944000c244040c2d03102c0c2c0801001009201c03142408194510300c203040d10381daa2401036095486500721070f03000c1202c10146900c2999101c450381428078419038454000d640740c51114000b800980d244090707841e2200f90600c640c009060b800101c050802c0059004906400d070008002c00c445552180182c00a00c0300302c441e00c1c030403817078101f020841d001e8100035580324641140c2e100e4240050b20301401a42005c18506000b948002d00404104400900407880a0141650358940310340c43c51070030740c68006002d0301a55440a000c1c03016401d140c0d01031003190455215000c0e4003040c003181074166000f846415078040d005a000a008100030580c50903c81d1100645002004a40c0c3c0e1900304a40401b07081c041c5550b1000580c4138144c03150710421481d4400303510781811351648 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 81667177 1250 81665927 81665929
    0x6061c0e0a0c0e06030d020d1e0e04020705060a0507050406020c040f0e0313030203010f0504020108060904151505100801080604111c0f1a0108101104091e0f0603020109090902010e 79
    0xb000443c2d20034040345045504110550406205403080c0c152140000d20400c401203101810b2190340505109900348509150400d15115940d40940080d028208554425086c181070761164002c0300c03803210301d40c1080d0110301c006104008481c1114030b0b0b40d028140442142c01044003401140c8440811162680c805030250308080c0b000300240b41c8241c00803e251131952042c10700b0344045180640c8a80d15110800c005030341c0200c0c5180e030040046908a85a03034031440c2000700c44510075030548071070f450107618001549009020301b083c1d0b41d0481d030044403e20784800072601c6500900407880f0316004803021a0006a141040c142c10010051070072a541c02c2d0203501c0049001208402c0e10107003140c0512105003d19000034180904261000c0c40803036041183c100d030f8528100d4080b07141c0968403800986045036450654014180e0100c00b400f50107100c0541e0311910070001410b030480380c6081400022107003944603c40880780d040c2c54940c0500d14100c40007004160b103d1003a414000e00002c01105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 81668427 1250 81667177 81667193
    0x3030503131a010603060e01050603190f02040f050307050a08120f072906040e19020d1a04151a0609040e0d030e0c0102010612080304030c1703040b06061c0e0a 70
    0x1002c1c1c00c100140c00d0561415a004094603e1944803803101034103000107000f943c85203411254010f566040040402c28080c2c8104014040385203075400991020402040b2251702000c03600440b0000c900711441651580e040000f00d2001d44901500e642c0040c10000000600e07401910740300d4140d80e02a81400c1650311046044031280c55a6071300f407410100703d200c8407040c0012141d00968241c404110101003144003070303941c6d004484030329107000000111a0840da40c1041d00112258840c81002c0060000403040300600c03070a4a04985411004540c40040d9125206103020941c0001400c8814209503040c858030b80c0c0240b801c617401984030080000b1907072080284c00c10f002030319600003c00a18100c545402c100d40c031041c203030443e4141402040710403c400f64031801c25410412a13980c07512180740c19a28403000d01e0300289042c100d03030a98820346801030301452042e80500035000465842d002044098810180031541060799645914103441c6130758088050f0004100c102c8000f080b107519400c01d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 81669677 1250 81668427 81668453
    0x801020418050702031903050a020c010207050604060e15160c120c020a0b12010e06030c120a1a040b0414031e090406060507020a1203020c04050c1e130303050313 71
    0x51030784031490301c10080070305807145550150161002d1030500d8030021440c89644d0b001e444e403a08040d210000700d4110f010a9040b2422140104000c6641c0c0c019460a6621044100d4059620342c0c41c142c00302001d400080b407651f0307800c80c1100c84416145c1d28070003400322107002e032121034082084410300b80000a0100717030590140040b5456030320340785115104012303004200f40c208210a507400d0110143c03000042c00d41038150b030407440c8048003d64422000c0b81c40d040404d032401c5d5010132004544012100003040d40c1c5680b90041105075040444456000c010000039140100740690f5100001e022441e14a01200210002b600350f07450401d892205a180c22900300f010420a40c0004410305c131071426106030001410641055400e0518a13000681f0003821131042015291081c04403204151090210380b400d032000800800050030500340c400d2b240e40103c4403490f18642400544000c0d0400b4100750b0701c80e0310503000d070000305504545d4101c41503000644401c4284640940d4400081c42c0f21306584 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 81670927 1250 81669677 81669689
    0xc0706090f11090604060b040605030a0906020703081008160b03060a05030f0c041425110d08090c0a0b0a110708030a080f0a06060f030908130305030405120111070609030908010204 79
    0x4a81d440441c030070803950f2600a041d40c1e21607807521904103c8207a074a011b640403901e090405503100d59600d6888005461028001084540700290b03900030160031020050180081c01d1210703030390580307400300c1c0355440f504e1880300c0c404518000803c002c0b00d802040155800039020b401c48044a9a420104e0715084030041c0b40a8260844581c080c450300f028800c030001030000c42c1d803243d000c3c10520038102c1c109401c1000010203010f0345441501141c0101280b0a00440c0c101c101ca420000303c2d0001817803000140d41c001114000c0380141c1c0500c1c40c121038603105680031010480c1c41e03c1621242503454001070307112007203540030702d140000340d0503030510240c00d5609280c0c03140c50061a08810307007041010000c216150350f0745009003d01c0255406966440c481e05281400a20a103480c00c0080840c041c1d0a0030280b8122010004400c000c0d0101c0508100c43c4252412000f07501e20034411801d9814544002c05405000c2c8041400305a180d0413a0048600a09004850984603200e032420f82e44540c0106c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 81672177 1250 81670927 81670943
    0x140d02040507200c01030e0a1205070302031e03010603180c05060c0f0a0615170c011d0904060b0102010b04060e0604021e130806060d051b010302040909060603021e090c0706090f 78
    0x149084d9601800741c510490050f802504a01c03406940d030315001712104160f0401c0000c04289501014000c0084a40013400081d10701c8000340c0d4950310594990013400358a00090a2440035079020b401b0f01c11500349c00e070380644580d001506007010b004460b04808850b84c840d03c03420b4150320113042d05000e44440140606800b040c10745e207080400902058a80c00307802c2002200e0b03410324440c000072402c176140c264240b03000c403260451003280d54942e403501c2c00002c0e406903c2900740410010317158449514a8000e8000b400000040c00400084940d03500c60020003082e4075000901614240e801043c61110160f0003441d80d01d41142e8120310341d00404100030500e011458248140b0b003003041441c0e0f1004040740c0304070b100142e076034a492b220707654101c486030b082c201e0110802c4039030300036016a000340900440401c50b01149040903400ba00091001340d0140d8440b803619030800d1000c80c0a0394211001a0510616440343d04c40564160f000c013105540c110340c0c8003503000009442110086041d4090449 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 81673427 1250 81672177 81672193
    0x106180b1b0c0d0807020a050a05130e0c1c150216060b0301020705010c0c0b0a1a0108090a14010c0e03010204080a0b040305160605010608151f020a0507090e07140d0204050720 77
    0x6101481f030254200d144254070005c0200403659503051f0b40324003038081541c0803a0024081896518010144040640c00850a540d6010f02030000f04c0540702240110340884e0400315900b4400308034424001c01c090800c007142038820200c2c2698204660011014000500c1c000c119250b50f401c41d41642d80c0600010f49a054010600c1661009a50051240c0c18100158a1030a9000344590114080c0b5410b1112100014500341000d00094040a4000410002504021506a0003001401c1c02c070800305080d180301481c90b042c14400d41c1c0c103443c3d520340140742400d03594440c0c03c541c0100a104a0801000700489528005411040c00881d84104404519941401c0c005000c8100080800c0d0004c0600c403401e0445940e80003c01480c0c42d2120208490314000b9070342241000074030305c4080c1c00791040010000300001c8551043c031000c441a42510340d107a0b02c0c0c0c1c00301c80720024500d82c81503020428240000152600754091604002d85007481010301e520303080109003201c03400b019001e6513007006070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 81674677 1250 81673427 81673429
    0x901020f07060206010302040b030109020406170106120b010506070c0816061103090d0803070909020304080c07050603090601090b041d07030512070803010e0c070804030b0106180b1b0c0d080702 85
    0x5045900c8000501800056060020081d6100c805100180c803071603d4210100700c5480039401003034200e0300030f002484215102d00c0c10001c059184544010150720b071040000716500b0710034030201c290364014030307041daa80d03e810b04011880d0800901640c400307a00d0040020b03030000c200000030200d007408140003c0545030281c041e00700341d00810131242e540c0040090011541e210041c0031045039015003415141e0b159240110360254440d00040c0d4468400818403050180c0d0710701138224010104200c0740c420791200309100306400103036042c900a51241005101000700e035005500c0b41c0001034000540c8030800480240060f0b403150208103030ba0040c000a1050000070300000701442c1c098003c052400c0c100383d83d080414481481580d094042d41c03000b00c0c0c00300400c442110140c9420191040d00d480c3c80382860308840500781b0800c03020172281b91480100c14401b00306a030460f4402c144450a0180c9001c401652800060554007076002d51040130189035901685010400d010718401901ea200c00c0c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 81675927 1250 81674677 81674683
    0x151c061d0703063008090612040203070b04050102100c0c020d03120b09060a0909110d0804080c0102150403030b12010c05090f030708030403080d0f110d0506121e0a05010203010605090102 82
    0x40c1060548510300d01138418180004240e04850420a43c800a000206400c00900e1801007001c0c96610038000680c2c0c00c0031800407500f56009a008505403041c1035601d0444481c14441c51040a0143c1c000c0e1403100311002141d4401089030100307003000100020190b00141f966860310300106c1c0031803801d0710040702d005203610509070705c404140c0d04030f2010b09201c00058031080700c80c41010303981500c1d020030000f00700864501804000c0054102241410130740342910540e00b140c0141c030314038883d01c0d0710400c80c1d41c07000507044080b4480d410004025110740e1000c90141c0713021014550811600f840c0ca40a00c0024414526004c800395211511090700c8020020040307546080544250311042d401d200401f0040111001c40e80e004e0781c042e584518482924020702407074034014105a00e40456204400e542c08010890404001d0303042103903544440030031880c9580d211005030141e016207041031703103004001650411190980c0407680307080d1141d95982e007640d009070444000103e0100b01804296010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 81677177 1250 81675927 81675929
    0x507050f0105010501080a020c030c030301120b10030b0109110903060a020408120906030703050601140c03071104051b03090109050703060603020a060206010e16091805010311151c061d070306 84
    0x40310090005515000000f07222036406044140350075400503280240e130703208204a680740810041500d48940c0d58240040c1440407900e01034401080f00000200c84003000100744c0309480d8840c40c002610790030015a01c00814010848020f80e01c2c081100000c0395804111452060f10423440145c0e0721400d05400c41d003400000e1044140d03020091003d80803a41d1355800f5a54001c08a2800041c00d41d00d03500100c80704507514042020040001540400602012004042c4607000740d54120100640f10140421030b1022160401c4040d40455007005d05042c450085401c02040c01c00400d180c3c111303403a40c13400c1c042540d02c2252a1552000100b0071400d000c104580101024006010789606d0315041c9620b00384002c1000c85070128400c510f10f15940503003400c0001c0c0211411903040484029610801003000f8001500c000218800e00e144070715200c480740b2030500d400d0550b81c3c1080350201080710803c00e0700300c0c9100100e407203030b0011aa030b40c48081d001c20600401c04401505052911028040f00c00b2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 81678427 1250 81677177 81677203
    0x60f0605040c021b010c1b03030e0a080a170409020f030405060f0907060c0c0b0f0310090b03030703050d0b060f07031704030905130905060108010905011112060607080c060403050705 80
    0x1c20070403203907464000c43d1307400e2004403a0b00c1c131003078040211340129402804100b0050440400030140c041c1c0080300d140d1502903034030913100d42c0c5519510100b0404558114030035040c00c0d40c000c81c00080040d2840c44c4900d01c40f10b50201840c101926090b14a041c0c0e000f454035450440004001c00040c000108016038010783c030001c090140d820300200407a25000703140509014403648940403010010107813200ca0081110099540d2a802d06101010300359100381e40066440c00341c503001242985007445001410000200158078060280c0d400391403980003600c0c030000e56170352a0303510b01d0340e40c03030b03440c018020080040141590703803081e880e028040070b01d04909184011119403c000000e9041310849069540444010700c2c00010345a401d4003400b81d5a00040c010f003e4080005001c4805400200040388588024880d0044c2c01c20110b28074001c1555000891804401142c1c403424850000c0c0b103440d00030f0081c14684405040d140d4134003001914200e00103900001c5020610000348219910100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 81679677 1250 81678427 81678431
    0x7080114010b13030b090a02040c08040308070801050604170f030705010e0d080402030703030c0f06060e1803120106030504031214010e0604051504020310031709030f030f0d02071707060f060504 85
    0x145124401d00700c2003940002081d6801100100b06c5004041003800c0440d0f60044c001d005507442144010301f624000c1d00c04402294080d800700d89094024451541a0307040a40000c0c00c00d85080d280000c0070413868a007402c0c0340145d0100c0d041d1030b1014801842401d000d20004030b1700d11240003910b4074018186000070101f00e40d4809002c0103a601107074207012217401d4500398030001054105040100c8401d071004080d40c0c130304036000502d820340e20385251207142e0240c81d1001c0640301e110102d4882c03142c4001d0300e070080c45040051200c98001d50090350864040d10700114250308500c820070454810b40092502c600b078860040044812030303c40b050b48608103a03000d00007428500c0e845102c0d41016000d60340321701c4d00400014003040d011210f290086804c55214054016200c404403000e0348118541d60003401032145da5000c000c000802c40c1c100d003010755502c51400c0398501203d402034005240481c4c45454100c00000b0002122024101d164052500000c4101b10200000b08940050741f149004074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 81680927 1250 81679677 81679687
    0xf08030a05040524070c090501050105070b0a0c1701081f020702010813031e0503040501050a0b030a0f06142401080105030c010806030a0f14010b01090f03030f090807080114010b 78
    0x399204003a101200c40c01d03a0401c103104a441500c4000441c0f60360081d40d070640c0480d401e024004180302d241c0c103d03818424100401d0342c03584011102031041d0f420161401e02c082e008508100b146500c08800c1021754070300032100601002640300105801c0c0d110660590210751a248000b020080c242c0f055501104c0461400302c1d1170340041c00007a402000c2d4203404034032030f14442c20b25000d095960f070240980500d4a444224402d406800c0d90400e40c0c05544661900700000e264201c54802d1003941d5400400809802202d82d40b407500d00140c1040032918240c580d04811080300c10342140b10701504012001011141d1805090b00c1600341480c42075040003034000040040c1d4801145c9803422003028a4100107923517481c004030389400d034100c00080801d42c1024036802070080003200703200800041f0000b07010601c2079000440f01c1c442580207500a5040d00401000024080c81c200100240a800c0c40300805503541c5500c0d0502e011a4031800559454410110303403407162040c02c82c054004d01604034108 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 81682177 1250 81680927 81680947
    0x90804030b0708060114031315020409230412050c15040521040b090604050a060327031205090a050106080f010c0504080705010c0203070f180c170c0306010918060f0803 74
    0x1b480303075901c010307080c00d000010940c540030f0403124480c081d800c2000f2221480140707103080000d501a12405142c14901445880c04cc5140b2070860f0b0015007800104415031901e0710741c1100c08504104080512030b04104103169105c0170b01018040842c901120f00300c130301c1d0905140f418500c1d00715143c2240d40d8118a452400c4103e0300c04d4038140e62100d043c5980356141800031488601c51900f0040d80071f8854480056a5941600119540780e04098036070b50f0604c0741e415400b000300b01d14000801080303403138051005c11105980310380e920114043c1218007484858507490300315072043e00a44080e0708810b9080781240c1090280c406100101d141c52803a1030303e0001103d8403015117006184c1040000410b190541d5420407004d4080c001e4605115100c9640c0c1c0806003148115007004105181000c071664003c0b800b40108012060b0000105000c65031020400f80e02a40011319940c14022040300116410403442c400800948a0720f2000401905240c92054040d02d241e100c46004c2e1f1007003010801c5 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 81683427 1250 81682177 81682187
    0x32b0e0312150604030506040506100b0a09090b01050720030d110a0803040201031113060314010501020606090a15030b0f0a0c0516051207060f05060303180f030c04090804030b07080601 81
    0x2c0300d000d03499440204400c04001400070322807940041c10601c5494184014814040798039409281310000340e8030003983e250032407002401040c0903c0d001c1f92940e44104502c1000390014010700e0070516050307190548a560b581e03e0380c40b103102900d07413010b8044015080d030305040000f044200c00c241081c13a1004100c2e004580d50343c41e6031a005100c003034084003003800c59001e6000400c07022000c3c3c4980340c40f01205500c07036041c040540b140038002414034100d02401181d05200718161041a4040d0060741da803002441002c24003c1c6c401c040560342c44240d880910101d008401c051407244000311400c0c00d150303002500c0c0c0b40c4081d12400b0307094544140ba0456070740044c03c90f10b803080c54200044e003810403030402d00e09140c11030380d000d421041c2c000b81520400105500c08003084580d203100f0401a2103000500d5580c0c010351502c60451180a60b4402c0d852503c0c5401e404a448020b044074600791103c004101521040d02d01165036203030105083c810441c3e00300207994096403600c3c08a4240c6802e50000f48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 81684677 1250 81683427 81683431
    0x11060f04030f1401090506070f0302040e0f04030e030d02070e090f0d0f0302070605010b0901030c080606030a020d06030215040e070201091a060d0b09060a0b0109031a060102032b0e0312 81
    0x1100180204070b501c01c0100f072954031140003410600805c50b582c002d04169844850407521040000e080f6401900840d02031320a5606480060311402c02d0707541c48042661b14180e006d4029018810282c860011659040101c0101c1c4400c550161910038039080140d09000b20142c44058543c214600401d41d0410008915a0383d0910b40341001070407101c490241d0092042c0364014084a040a0000c01c680308040001c25030a41c003030fa801c10000c08829400c40710f0202c01d540481d400182080821003106c01600a051035101540e000146907640740e0006480038501100c00c81c900d000840c0402440f9030307001f48154440768600080c4540403c5a076441c001110f4005880f05050180c408100c5035221030003500b4a076540f00d04054141e08240e4030712507907818111001e250031820302840444031b52040419400700da500030441c1e1504141e03580c11a07400c8500078007090441c8018003039031a01c084d2025255020300c0c0d1355284c0c414891401248541078448440108242d0341c000c0083c4445d4110602640c0c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 81685927 1250 81684677 81684683
    0x51203030403300501050f0103020a0207060e13140601031112040305030c0403060f05060f0d02030c04020a02030909130b0c0403081206040222150809060414070b0a0c11060f0403 78
    0x8101c0c01800306214403035160300c3d0b1480440000c6481d50b0709600542c0c0258161141140d000d0303088002c100c011016841a6100701c0016000300b03004001c528060b001030381a20030010f0004422206480480080302d00100c2058011a861810300ca0300e035030140300780d158070a5510795640c540b8807002031005881ca806400281002800000585201c0c07814055401865101000303001e80131404825102802043e288035120707941074924031044e803919503201c0541c640c1c0600a400348805100c1008025080241c000c2c0550104000110300c5503500900d15104402c40b400e52015200c844c1460100c80c01c0003000c4440361281000140701290501e000e50307200001c09582d40c0c2c06503a41001060290092260900c1c0762218403100312a200f41c20070041040c0d591000d01c60803040c25002d0200c6441505440415180d0000c001180100d001405a910450030a40c100d500e007590ba550341c13881940c464001e4400141c100305002042041c8101c8000301c2c8003044550070300b08120403038948403901c5188001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 81687177 1250 81685927 81685937
    0x17061e0601021203010b090f030601060c080d090b0709081002030606031801060e01060c02030111040605070206030406241707050310020d0b04060e10080a0b040f11040c0207050406051203030403 85
    0x14010780c420455003000340e00e50072020b9101e580d00d01d1084580e41140034102d00c501d2104508014609001800b241291030a44d240c6195106c2030b00d8810b125808a900b040619807210b03125008200070020103800f600c100e070346450300d003441d01003881c1c203112003840c1c00ba120a00401c2840301c184d82e110140c030380121007400c00b04c00f2103011151042c0141059407000d143d4448201c0001901c82e00b0941c0e5542c0103000b50020321011400d00d80d14080c0744594003645000c11400d0000e1005814801c010b103a01500c41d05000900400746c200030351303440c45903090b44041109408424062081e03000d1000030344104180040507114208800a03842d10201079000842d80d902007200180b201c596041640304880c041e004100c100d4070750000d201e210b80c0868036521403000801c000521004005071816405800032400041900c40d50368001c86507030241400d890707441207030504e4141556148501d010601c03850300180400d0b4940780a010076104650700040c80303260841070002402c00048101ca42c0141d06140c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 81688427 1250 81687177 81687181
    0x301060816111209010906051608091203030f060a06030504260412140c0109030305030f0a0603050f01052502120904060314070320030c0108041502070b0117061e 71
    0x44a0941c190034030b880d020320a88802c2c2e40c2c0c40c8a80d1004101506007031b6103020b02e681d10703104195814881c018010700043c2078042d0300300c042040d840181a07000c1d001051020b540c2c50320b400183c030719081645d4441c201d600c21014001d0510780020080000d20032400c0a100a107401e03100c214550f2210203e20b070b020000300b48440b108030000c100300c4010780b0000c014400c0d0b42502c2c0c20007042c0a03030002c0d030143c90b9200701d40559040358080d09c0c44000326607242c0d9500e403941d900e1540702c01010030050009a0907075203810001c000140107125560701014000d00015061800e50a882e1031120400c107502d0f8204e60740032030600718075030104180c043c0340d094195083e6141c0132103011030000c1030700364800f0f80a40d042c0c030b0703015014401c042a03110841e4000c60240f9a124a02001620b444201d09040c1c4c1d0b041d404100c01190782e5000d4801759034040d004070003142031007100c0e4010100b40da02841c01196202e0801c8010701c20b8603140b27080400403a8406004004038a0008191842ea62000c282080d4103c10380c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 81689677 1250 81688427 81688471
    0x5040f1a0a0311040819060501080f060a0b0102030405130219031a040b1c0b04030201150b070308090106033e0901061b12030b030c01031a0409020d02030a050c011403010608 76
    0x13180c00600e2a0022200d958854405540180d044c000040b5911401c240002506000000d0000a0980003001400c00c6032540b15080e0010001601401e056000500000555944428212001060000c0096555880b18010303200390003213840440c003850303d0070b0242e82a03042c44c1504d242d1048020340c1c0c0042d125640d4070000c0e600340c1594240d8820005070805590800110003245801207100ba00284030f0003a603840c0c0800390103628000e403640e0320f00c09e000102c0804e206900ea1a0000c001c840002511900c0b0b0300c0380380c0b0004a04441c0c07018400e190886810750f0105120030418402d2500134100c08000130000900310030781c10720900c020040341c0c40c81421308480520410183c550f001d0752030510100840307006400360652402c0f40d4420b001d0700111607500d50184c000c51359404c0c1c0d4954103034010107403041080004d121003181a03070071100c10742031180140c070100714858000d8060fa0080108c00304d080001400c0c40b806020001398404240010070025820071076068000700501d43c0504404c200740b0b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 81690927 1250 81689677 81689711
    0xb0301050f030705100302070510090203030f1b0105010f060905030705090112050f0f0106170c031c020102130b030f100f03030f0e09070806010806060a09091a030303040305040f1a0a03 81
    0x207000b4641c08060400c9172012a501540203201d031b44c0c0f10740190b0b101840343d1030604e802c461100d41d01030342641040102e00000e000d00d100512801c1c442c0c1c25003022528184902a08690302600103072084540c4601c240101e07074201541d24002c2c4002c03401421680d0030b2030046182c00c1c4040c0708100040c2040e5242c48108481400440d980c07100f140304070780e030030103002510b00d0182020740b080c0c0c42090f001b140c0500840501181c00311958901034004d1080031039031501c841e444104003981c401155030900ca02c0d030754140c501811400030203001400685a0419250404000202902d19403404a841d0004c10030080700d14410310880c0d0701400d04d010107159600c015030b00001e8a882c0107600046a00402405c0d076001018940502800c0c0e1f100940c40d5100c0c1c0a010300352180f1200314000c40e00d00b44c41000a903400f5001003400004211607001d11142d48000300340b80d500240c404401051011400b8000401070300ca880c4000c2c12004902c48049010882503461072140664003410942c4507002c4903450381c0c3e48 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 81692177 1250 81690927 81690929
    0xd1101050a1e020a030b1905041505031b04110a02100612030c17040b03010305030d060b03090709050c0c030a08070f09030308040b0406090503030c071421070f08030f150a0b0301050f0307 82
    0x5000021715129048401f8805822801510301c01d902e0800111441c07620100000295600a130060040703ca040940064048910522640c4141c54900040e0003085541c0075040c08460b94005080c88020000d401003600c82d5074201e900c1e8115a00d20140210354000c03040c588240e0802c0b1a400da010030514000010b104541004090000c008000003c01000000070800003410140820105441d4802a041807009132086180c03940700e81024000d20f01b0310381c0300c0707170b00021124480303440e02500c4692541190081c02142002c00c0303a2400300141c943c0c110100481d0325855191501c0c1140c15039401810403407010740b01a010306001030019080104030350181c0c6000c0c0d08901180c2d100d2800303ea0380c0c595684103200c104c0f40d1800f8081c002c803118000142d403220b510100054807a0705000c1001945050b0040e031130540d1f400756805102e80100c2c4a000056004040810701141d0514241c081c000348101d04e8900c0c540241d82c0741c4c0081020301451f0040c0c0341136440860310355160030320000c0040c1ca400c8007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 81693427 1250 81692177 81692179
    0x150a030e010908040306290f010203251e0c0b0901020a05120a0f080c03070509061c060302120f071a0c03040f0f050901030f030309140d1101050a1e020a030b 69
    0x6040411401c3c040d21101800840c0c2c42064148052000e10001440c108035000c941845c403a1141c16150045c034026051050b0007a040c81124208600c1c040d810b82c41c81c18181c00220422140031003503080c4080c00058000c041e042e50900d58000089580300c00300c61455100e24982c00b480810000c819a100780300200841b90030004555902038039090b0041594442600d04010901640030861007602a4080a00c501004003d46096540341d01c81603a480d407101da51564003039801c000c00d008141c1d00c00d00c0e624042503590030001e80036080d4818020f046600d40c90307289295010b00c0c4803c0311a0000a4494241c0390340c2d1000e5401402d40400c004540e010b45440701e4194003011030082030001c40b441000d02154000c0008002c01565607040c408200002e010103420f00200b8007031440424002d4000d040c0e2a80b240500762422603001c1011810074000c0c41294000400c01220440c81220901680f9006a42c041041260002c400d000c0f41811000035850721189802180c82c52003180264440640044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 81694677 1250 81693427 81693431
    0x706060e0906010608011203020705040e070b0d020405031515100203040f090f05010b09011b031403090109051513020f031212042109030305070c090e100e0a02150a030e01 75
    0x2010040c41e40c850509004902c00035400340f0000508101c5d92030b0000c81c0b9034054010b401020305001c00c1c4809498021040d1400c0d100b42580011840b80310801000701c0740240c0070040c1c45178207210800d82001032180c0b0034140a084441844100d588481004a40c480708031105200343c54010426400c6015031340c0810b203021003900002400015030740283e40403e5130781a00300b01d940c1e220801c0b20070f6030040824003030010f6038401d05e174505101c502e07140f1880d40e80641400008010140004a11903008a44860b41079464030a023404000c1c0800c000d007006043c4080d2000d4502c0c05900c040d102e03c0c47e00078081d1094440752900d1400d518148804002c018490180c980c3d501c4d01d035409030200303500a480c01c4a90b6028030040b090004014400400f02121070b560f1840d10302d155440841e001e82004105032088621100002402c01c014410000b0641101c00503103440310026044100f11544183e07182c2c15071b0001c1594100695071080d010140680c48003507180c480000c17000072001400c586003442c0c0c00f0340c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 81695927 1250 81694677 81694681
    0x1090314090a090c0306082b050c030720031005060f01050d0b030307030e0102060a09260d090507210206040b070c1509170f06180a1703010905010b120a020706060e 72
    0x940c150000740503504480116440d40780c803106400c04185c40426008c00741d2031807055070f4190301d110340010301c00d401d010310840f8140340d442d40303030804642041003215a00764450035056003142021310409000400c1c1038010400707440c00c040822590304205a1081c100320001500091482e015481520f20000160440f80c80d000711345000f8141800a0859502511483c0c00040d00c092079030290043c5103610003409610f900210015018892000c0181d012608080c0800c04a03a041886928240741c0503c0040c10458988500c60030600b04a01048c070000e554000b0b4000907840b01c00c112030842e900040315580d104e049040041c040d2041ea0422014156225840501c0703c0c3d00c076810400f51910009440340503900c060745a591007140d8100c2c0d0459802207070000741d20108000404440000d24415901515015035030081a80009424101d042e1004001840041040e1048a014102d8445054034084904910060555000307081e40c81d256000600c1004001e800c0d0000f00082c880071107203114034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 81697177 1250 81695927 81695951
    0xd0e0a0e0103060905010b0d1e0f120e130207110910080307060b090a02120f0403051e0301090b01020309011704081e03040b09070b09060c0f060903041701090314090a09 74
    0x58601341d8403c0e1219801d020411405150424103010807962148106d9051220410405001c8000220650f01180a2202803000c980006160084d0b042c00382c0e542d1340740c1902d003010054040a5420150b80c1c4910500a20700001c3c1c02005446c400d042c205c41c0340c4c440d56140d20b4021035070016a003001c07105000114400d030400c451a00008c030140c00031140390000f0380e02d42d4402030803805010000e01e01413004602003286c40d0ba00d080b00f280c000d406890942d2030b000c41202c8407410b42d03160104880c004100000104902ca4580c814411100001d102452078103c401c00000c141080140c0210038640805010808214000c400c56400116181103040c280b10074141c10100c40e0000c450584501d48510f000a9040802144900c203a52811740d030b03d07080002da1000e00c11143c01018040d1600d114039140c1d4000c4443c1007110601c6010100e00a641d29418080051680b00b0388039414486030707040904072000250801d18007040d0071841a501919041c0d01800a140d00100d90300007503106107040514150 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 81698427 1250 81697177 81697181
    0x1a090c18060a08120301230904031125030c050402030f010e0c1c0501140f090705070203030409090c1a130603020d0219030b0a0b09060a0f021203010b03070905040b030d0e0a0e010306 80
    0x101c54901017148500d02140050180c90f00641f59420350107860030700000e00080c00f6003130800d8903600400c1101c28520002e24441943c0075141002c540003010300c6802c004000b8a0400c00c00505030a0310158103505100d08141c000407018000d18071101e1085c40050900b910240c196515170850724221746d09189a5801000213010a0140341480074a45c403010b2914244080454450407000c1c0400c440c50b60340d5001101d0540000318203e0303150008110011307100c0110f000d140316060260300c44550b82407038030b04c42c200c5003c103a04c0c0c480c05403501440684401041c8103425000c8988a0074050b9480002000c50f00003032181801ea10046025440214102039042e880040a4107090b1382001d18203480301c00000441c0200400e8562080c801c10100c00724520900e8180250b401f607004983e45200503000d081d0264000360808007035a1404410004e503258170020300c10080000382c90411200815402003600ea0084600d240c0c1408060607252000e5181d0025100051044a9485420b0750312842d00b040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 81699677 1250 81698427 81698429
    0x10020a0503010e150112050604020c030c10050609130b13060c021e0705060301050609030f0604050a0c060914040504031e021c080f0a0f181a090c18060a08120301 71
    0x60301046540011101e014000500b250a00c05031105840791b24140d4561014080040080d908070343c0922141c040d9090800217840c002c584000500156200000c801d02140c40040015115485803018001c0e40100d65031400000c0c0c0d0008440885135842c0f030141402d1101c9001c000380030300e140841c441c0c0002c0e404038003001009070024a42122200f1401517a68a49660040d02e034880e81c10001040585440401000c1020001e400e0b030b403112240c0c0036901d0800c0030498050325140c004206190400036030712103502c00b82000f070030712641c0c40d82440b02501030a4070b4501c00d240115954000300303081c14015442050410100240342c4081005103400035294501c0c01000b1030128812030880d072200c2d0081007020320600803030440e001d082e5281d000100162960000f915001071380e41c0d44d20704400d0a500c4e00900103600400e8140e01c0301e43d0302d6203c245417020052030795181c0d4008101c4010b2940c2d41c007284c01c9003110a40030302d101c0c986401e800a400044140e110014500c13031405101c03040015100514 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 81700927 1250 81699677 81699689
    0x5041208062e090e330d03050d060e01030c0608060102010902030105070207050a0821180d1a07030908030c1b10050f0a0b0f1e18060406050103020c0c090910020a050301 74
    0x1007419030b560b6208a0038030200341d0f101c0100d000b040c03c0000400c0c1031000300130445c0b000d46080d400c0c05514900490218200300505074005840092000d090b581c0e203002d44001484104c075401c500c1d6155458600180c0c59078001c141c02c10601e00c012035401d030f100350071071a40c0039001002040203042a5070f01030b41c1c1d00d25a208071402051090800143c01c100418800c150400c041c00c500b020342007142c110600c60f400a0350002c0035001c20406c074440e07a1121825400554868a00c100c20400640481302801800070002d90425043c600010700081c090005c2c0e031380008191400035200c030101c2a2044186c0c80103440c400d401d10440f00882c07400202a08542e0145030b441c441101c094070360860071029a0403444103642c101d245800900c0160503c244041119481c42c0b40c0c0660003901c02c0002201416825051500380000e08207120007403401d4840d041c02407009081c11481e00a812201507110025286d0ba544105a81000102480d07010301c841c104020413080c3c00c56494040703031800342241d0401c2c0122 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 81702177 1250 81700927 81700937
    0xb0a0f050f09060d0b041b08060105010e03060601020c0103020903010f02030f04111507020d1505070c02090106030612080702010507050a050a03020c010908031801030e07091a0405041208062e 84
    0x3161641403200c2c48500071030001d040380c56a8080d60b16103101c40103002e4011515509125038200a500c01d030303003085001d0000d18024003d59458280010260701c11103102074841e400c02d006002583c3c0e000034051140c030600b820050303203c40c44017002900604405d203010743c01a0000082001c3d1002e41c0c0140d0348234500c54001040381341d0550301070040a40d882050340703a0b9041c04006080240c175020605030031040c8107401d0707259002003800110081c0c840507201c01d8041440c0c84000000c41c604041c00301c2c0900f11619041000714500782031524408080040039048100000d1054256440384048480841c1c1100032240e1400345894290360303d80340f0000a03001401000000300d829072013101030004a4099034011400c00200300141c540400c0c0d10300000c0d060555500c80640326038420312207040182060b5800041030b006084c50040c0190010003041e100e540341100304030014002113412140c040d124680300078296110700104040d1070100c031488450305144c03440110f03028030a81c6070001201081e524 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 81703427 1250 81702177 81702199
    0x303030f050c07020d031101060312020a140d090302040b0604030204020f070c0501081e1324050f100e040c030f0b15093d030804060f02070608060907030b0a0f05 71
    0x8007100070f0168500c02544801c0140c40030000c0f074481d410b400502c00b00a0300000c0c92958903650b107828001003448171b20168000e00415014400d0360341c0301204444000c0d001c0c1285900c110b40080403005d0a001c000c2c8a140e481180d03001c151070f0141990065a4003410455940d200c50f58001c0c155004114211160107441c0008600f55204514140c0150500800c5605660945008e8022488014202c0c003003d8244510b00001c62440700d0700504c1880004d52030810010390306c441c00281c0340c00038050b4101703608190501200000c008241030440d2885010f444540d1280c0c500f01c00d100c92154809015090029141e1090004c0b0b1405140180088000c42c280b5801202c03c2c0082801d04880034284651510000e60000020810a04801e12500c201d052800303001e002c03003907898200390010f40f080c0401181c18401650400001e41c00500d181c001808240d140a000400100f00107000d03d00030204107001c6424103000e42c0008108503001400035003c02c0d04c9602d0218141038510034103100702007500c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 81704677 1250 81703427 81703441
    0x106050d060e15210d12020c06010e07090e0105180711030304030504060306080a11040513020306090703020102160b0a050d020d1e050705041d1503060708010302030607050309030a080a02130303030f05 88
    0x1d2200310306003050b400361072005c2c039540c41560f94a220414041d0020340802100701c04020511901307028280045201e910360421040c01018500140c0002e0043e007130303610040c00290b841c054251400f400490035150a941c0d892000c54801d500800c034242184400300c240000c0640140150059440e10307034007000740c071799511085a6104401c200c00f0340310305190b403542c0e0740c2e900309a004154030169a1840f4118a006c41e80801d16160382110443c000b40c01602061003190707418498940c2480030a0302510105052002c04501c074030917000f02c1018080c0014082d14486159015202c0c5100041030030088203010421413800c6418203122805038a02c0d000026000c2070054007541c003600d1801c2074503110784200d110201d8182c2d8014102e8074a2207401c542c000c61550702001a036100d0340f810784d540781103540b541c4145440d180d0302500c00c5040c05800c2c407c1000156000042c2c0300400031614010802d611481c9500001340300c0c410300c543c210000c40c88040185501600542c2403420191070801607517407215 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 81705927 1250 81704677 81704719
    0x5061905070e1306081b1c02010206130f1a0406060b030c04030305090402090a0807030501061d060f130f020c06060a12020d0303060f03030905010e0f03060106050d060e15 75
    0xc824001081e00e1071910000c600340410080a581c0f410540050665105d403029072410509100141560408501400070b604140b0f1098a60380304085a000c840da2203540042d4a0705001406181c1c3e00540440540074041603581c0e44c004035403c018000d0705803c0c80c0300502c590190440d415030700f003420060b00140b400c0b13400044a00c40c0300c0e0104054281750540e5070481d40d55000c04403141d441038090200c114260340d02c5503584000c0050a00400c9458075514000b400d66105500c2540c0d001c52080a01101c40f98928100b0b512030f0f400c841c2200d00200c40b0340052410320b541074a2422040c0350000400b1201c1056005262202004084a8207030350754408000403035003071b0b000b0764011001c454502401405c2a60a0005c10780c8a03003000300305291030711181141e400f2070b544150002903e80d28104030b5541c00c11442c091a400599440d41001e00c0980440d60b1910103106d0007003003000018800c0c1070840c0c250b10110180002d2a0141020300300341c0c1d04200c0201d451020284140d02007290b10120b02400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 81707177 1250 81705927 81705931
    0x2060403050301050111010605090901020702010f020312060f010201140906220503040e06010c08070803040c0608130809010c080c070806070216060c0309080307030804030306050402070201020304150c020d05061905 94
    0x50359107925503801e240044410780d48150101d052507403030b00e9001c5125075409000510401c22500016101c101a000042c5901110240300c4250f41007044200e40041081002d280e01c003c05450140242d9a42e10040340106400c00c81c4403820704c0d4142c10310070781030710200710f0701d009038564000125141c00e0a00405800e0303146420040265004000400800d030030140c02550002050409203400a030310b4440c1403490340800002c441c11000041003204205560b48140064000751034008043c2c94095114502c3c0c00b88044040c141b1107002c00c003e41160302c100b2646100590010b001d50b141c813005200e0603620401402042c0c40d5001e00c4000a903141d01c0001c1454014800020355444d2a00c2d181c13090340c103480000015420007424841c045109481080201003a62180d5a5503010745081d0500508840040d0031081c03040e401004801d004d40c1c0d0000c1aa0141c58142c00900340440c91283d00b5100e02e80580c0d0000e401180424a41d41480700118115220303011022040000b403c080c08000121030701 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 81708427 1250 81707177 81707183
    0x60f06090b1813020a030308101703120619140a240e0f04090308071116231207080105090102070c0b03060a09061202030c09040309060c261801020604 66
    0x1c41010203080015110641d80016540120103e10000da401080050f222900705601250080c014450780f05c000041410091518a100505042c02c03495410b0304c07032041000659045910402183e20ba580d4050351041c41c060301800d01c80880d0386c810500301c0004c2c90522443c41a040d0030360000319005070741903508042410702103540d0b211001c1d0001713680d851400910250068101184982035450701e115440d0914003036100c501c61443d080f00b00400c08014842c41e80315a8001c81e05110700c61402c42000f505880080c08042d003031661008201c00ca1851480581f588152040200040060081075901c181c514010082c01165920b418a80c240c1c070803840000e2059409180421030100f07914091030b00664010104032500b90717030b1a080b02c1a10942d4004000203131044092038214607042120086459058036200b0140c6419140541100050b2103648184400d0080e81d0701081944802c0044032088491500c0b960340400d0074600b0700d9048811880c000d00c071f090596000640c000210389e84141d034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 81709677 1250 81708427 81708439
    0xf020901050708070c03060c0e1905030618010b0301061508070302041409040f020406090c090603060e06060915030708010611060f1f03050a050a02180c0711011101020304060f06090b 80
    0x10b41e40d076002c2c400e9100d02d5069618250301540400010458020f680003901c00b65151060a018070042003054030400300c02406082c4c9802080000c1c0d100031403051351000020020003000211b4036a114050710890342c28507895407800e42c000c101c00200c0f9080d41c6030104d5a43d04da000da5541c20809130100d204d680280e02d4540380c4003580d40038502c1e0880a00794000c1c0b10345452888440240d02050070fa44003500603682c81e9858680780c080381070380302180c0c1c0e00030a030318034003440802d103002540d22210a0103041903009040c002211034481d1660710301d40e0208110340c0030580d502d149c000c8000305050703420f01800001075003d281a517651040000c0e2640184c07a040048041c0c3c0d180c5641c8850910881103605807240c100c3d0100001042080c002416400e0241c40038180000c040d1041108001003000c250002408aa0a100f041a8450162010303e40c0c0b001030314002d03080ca000140c0d0120700c00e021050066000104100420140b42c2100c2800307500d0050a100c102d4880d40c03d4016142c1348401e40f50006 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 81710927 1250 81709677 81709687
    0x9070306020a12050414010b0d0c0911040b120108100605060d1e02070803011805100311010504090204060c0c060906020a1b03211803080304031d040204180f02090105 73
    0x3034003640c0105510a100d0908240c118024492841610401c44040d224003e0f03071162088081801c0c000d094140008407a01e58025100c1c2ea601161002c050080c29441640c0704000d5840318005805ca4001c0c0c2005195103484082d103614100c2d60941c24013810403a40501c0805280c130580c140691000c1e01d00c001d000138180042c5000f0131000b8202900140354044d0b00c0040d032203910144d48000c003a024002c0040d95904e6040801e9410718111142c590403401b4a000e04101060464107003040035030794044442c403c200c0ba0000102c549000e15000401014800074000816640000e944c1d10b400c0d2141c0403458a0310f5a45500740d0700740000e8440d4101581020f980e081c006150350314146000d04d101c00c1e01e03e01c00c0e80c894595151440d00ca00c544000204804280d100541d0421088104143d11698840041d400e680c0c41c00a07600025200074140280700c4050481b2039001241c0d034816010150086440c1c03035443c0002244a408500b101c5201450511003c0940701240212007030860103031506840c0c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 81712177 1250 81710927 81710933
    0x1d0c0301170124050108010f080d0503090c0a06030506101403220503040303081801020403050703020f010e041e0e0304080604170f0d09060506030c0f060903070513050103050f0303090703 82
    0x491090681c8401c5950b07582d400700369103452500c3c118105000602000b00c01404c0000140610f881030300a140c40fa005607404105030303480040c40840070780051602e583c89403190792003d890407014500081d4841000c0710085030465144c0d000900c00c510454a1000032585071805403040044c0e0078076040c1102c02000000c200e0344080b07220009601c03602d0b8424060b890030f910f610341160801d07002140004c2d4143e092005051841b5251682c1d004080021460a89107540c0c442d034803096480001d000c2c8180f2140c1050680c0141e0a11240f806d024000348007000004146103100c03a09411700600d114a000e07100c401d84280007040d04d00303a4810300020501e94499880e864100c03d14a40241101d220402405601031149409001c803540860800f08134a010791500300b0030b80310010f200f68020752103000e15040307551301c0010402140f04c1c15118255903074140030100e828038406411194000344a1803a0b201c0c038040c55402941245c0c021020754043c5280140c40307548a20058903076484941c4a41414804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 81713427 1250 81712177 81712199
    0x80906040209130602070819181e030b07110d050403241b08090c0405090c090c090406080318040b1f050d05161106130b0c0f03040c1d0c0301 62
    0x446641d400000707090b041e0383c4c0c514050341d01000c0201d81c94900403600c01034101502e02d4414102805051031030b020000c43c0c012a807038240354825521204100c000340e00a0028460242c0055034000c0d190440c1441e1400300a0900a4a80702c5801e55101e021072580d1000d2242c015035003520740c031a0b0410020361070307110001103040140b011542e03444d554002d0010b6041e0001c100012410722074451414625000071031508100213805842c0c001c904102c104902030b000803680e0140803800301e6201d820790300c80003d000541c1c0614412107402034502140802d12240c000060b001c0045503201841140f480002400b01b941c120340241901302080244070b010031120110300c60070021080c81c10038107084800080c0401e40c1c50076122034540c5210824009440c503440041200a01440c0000704518280509054110051501d0180c8200352100c00f0800200c403600485d1040c521100c00b650300c03401d00b400c242040d01640d11408082c0c018094490041d4040c10b01c00d903218074611034416040d680303000c5031410 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 81714677 1250 81713427 81713431
    0xc080604150b03190c0206040c0602010903141602122107050a020621010b04031b0e010b1b01090303140114090c07050c150c011a0d03050a0c060e0319080906040209 72
    0x203a44484e80ca0000d408007618821942d022a06600401060410f402c03d4088441c0c2e130b0b00900e0842e410300c22610082504031101a19145030711001c242e07603080c00100001c04c0c1c0002c04000f90b00c109071200540010000042c550440c81c00c2d40d00c00201315924080c50f04d143c1c490240e00030525007181103500054600500500900500c013813222031040f00c41c1c0c1410504100076048820000004201801480300858002c8040e24041203601d01d01070409000b96080901403080d10300e034490006031182c21807800c21103060101000c5000740311079440b614014001d498078182401c906c1c080b0303d0001402d006240f4201026003405403640305552a05403003003285900400054034907200d042050900c5417141c1e0503401d142c04071980354984402203101441d00b920048502c11100100900007003040c0d40e990415140c02581c0350402c01c1d99000002c9040d10b05514200c0c0180119261410318058500b001c4010700e209589402540d10501d45d0040c141c90280060780c11603003035030200c40060014206100f4407a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 81715927 1250 81714677 81714691
    0x2030702100906021618050c04090e060a271106040305011a03010c020706050d0b0402070209070c03030b10120c090f03140105060a120f020105040b0c07030501060503030c0624040c030c080604150b03 87
    0x34a010f803900d01c60425942f40502140e043d501c90420002c0a02e4607101b4040d094900e458043c1a4040c043c496165880780d10341c018000e125501c0c20101030b43e450900f06ca00555109000b4000c031028010302d1282c4134002d42c01e07140070394200300d694002a44007080840c1076901a0315501c0c1401c29140c1400010300100d104650000e90800407c0b0240c2d03540c081c0503100e03404540e90144840c6161800400740ca907104202d03400b80c5a02c0011610040d08500820a5444400000620b03c2e0f554601101d003a20b191340400d081928802002c42440074080880d0480761030301c1c009102c41d484240521010302920302c500709a4410844541c0c00065984002505d0540145041400d02c0d84500b080102c40d0301c00c0d900601c1c540d11440d820810820280900001024120f0195041c104039030704075902c070740740105580c4001005d1100a09000079154116240c0e0002078820008054030743c10180041400907810300c0814104800201545094052901c821000b800300000003803610b225080c85810180c100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 81717177 1250 81715927 81715951
    0x2070201050714301215040e030307170c27190504110702090f340e030106081906020f18010f0507050304060f0203070210090602161805 60
    0x5030010444030f1200f6810b03a0090300140c0041032074004481115041002d4518090180031400394000e030041042c0c0c2c100350541440790300543c0c0c882111400c01114001015070192800480081e5103500101651140082e5110b1122441000002e40d03000c580480d2030350f4140a0800c21f00000d0015010100c85d543e509040c0714002005da80300140070100c413a400104403054594003000ac5103414042c6044003031640a40529044031900480c90400c00205815211950840450b4010b002a0400341320a66680659207845004c41080300c03000d0f5a49a181c400a440c145545503585010b114810440b1100f5003b0800d00d038954210940028490308240c4200b0380c20b00214004a50704801011300b840e00800c0003800c4000440090510900c0400e81000c00c04140444000074200104a40030b0f5100d5040503c090f01030403504900d188074010000750010f0801228000083c0c004c207c500c00c0da410341c0c081da04806ca43c0a030040750b4860700c1c4140d21005110010342c84400e034040d4002a0008041524 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 81718427 1250 81717177 81717187
    0x503060610032a09050d02090402060310090c050d0506030114070810080f0309150a050405060f1b060402040507020d0503010306020f040305070f030b100e07031e09050a0215040f06030207020105 85
    0x4481126000900041407000310703c40007240164030003a9880500030480e564003040c00990007192440c00000d00003030060200002013600d1014101e5400000c15103190305104001c0304440050190300200101d00e4910704140c003182640c60103005000c03403060b4446045207a6604c4140450300e40b8006810001d41810390351001c2560031003844a01080000304d0700855840d040e00d024401f0f2201200100c80348907505102810606a010040301c080f42c40440380d1031340b14003910301c100a09200c0c0003201101c4640551a406561001080c0140b042e402154100308070f60b22082d05a03111000405440002407003080180001a1280c3c050040c6250a00c034031420a61242d40303151070090590071441c00280d01c42c00410070412503100a50307106001031a10b425052804010300100c140103000c0400303040d290345031210010904603441d804083c10f03407001e00151829081c8580c0307400c80440242d0060100c854102803011920302198201c41c07201c4080744e9030a1412404500075045582d00700c0c1040403c0003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81719677 1250 81718427 81718451
    0x311150d0608030301031a010602100c1707170703020c0d080a110301030f050c0f0607030507020409150c030b040b010203120907050907050a0f0327020103062408090304050306061003 80
    0x11501c00030b00718000045980b9411030030005201a0000004540c5030881c0340140201079012466202031240310002003400c4002c0501a59100100e1080341c91103d1514100301c03c984d031220f0070009500203040020802e80f90182d00b1802e9202d1620b444c1d0b61913211f18800041c50b0f10590b103469100804410004001c21100c005081aa200782d20545200342180402c0c01401028082160404030845500000a0325807000c00c9031401010805000d0100110303240e8290340b1141c001200c02c80c1d0100f004201c00b28100c0c2c00000810041b28880002480d100a5025a0038148146410702505070010750514103a901c01514640c3c1c010490502e900484100050703986400d00014001d400035180e0948030224140d00070100061843d40740101400c200c410070b800303400d403445010b611a953300e0801034511140010f9014003a00c2e800004441008882175400f034400b4100e024501c551655144500e48800315899034900a80c0201d40d81764101d90007050f485d1414040724030822845040100b12540403003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81720927 1250 81719677 81719681
    0x91a0708180a0816051b1305090102090a0303050c0f06040c050913080d09110105093003040308031506040e0c0a0e031c0806010f050d1107020a03060f05100311150d 72
    0x7901071100921007400813420002c051048030740b40340c070002051101d21071b840e00146c0450001945c4a407a241d9980105810750001c0d0116041d0b168060010400f2a540b0719005200707520083e07411203580540502c101ca010404503407140200d0704102c003805420305140400500550140c81a03003820041030340d000c000f86280000d052402c6404100042403c1503040c2106820361502003281007010030400003286686000320401da60385861784481140c0c0d13901c00301881403112125403400030720010500100b0005c01c2c6c0c1c000c6104030705010b00004041454020301559015501628202500c00000107103511517000107031280e000903140100c000d111203004641841c2c0001c2c410440c0c04200d805024404d41c1026003142c00480c00c2c038040926001e0820014542e000d0820000162500d54407284120003141c401d42e20020340007801010402d80d24600f203002001e0306884026000c1c04c240009050682480c4440c0840c0e07045050407001540c2c0c141003009030140c0010609025200f4494002d4140c414 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81722177 1250 81720927 81720937
    0xa0515120c07020a050109150f021e010204030510050106050d0b040204170105090d0516030804020619080901050a060f051903060f020c060606130b0c0a0510091a0708180a08 76
    0x2a001d503030b81d00d494014132611001a801240c103004980500f04020b00f551031036401101903503c2c003031044c4660500f08034209582d001c011301008a0310070003206c001d441940180100c030302c80c00440e10918200e0040740140e990910038980456400d002d058481507254000004405008000610302911003480c0401500e6904040035117070342d03c030b0070000001401c200200d442402c0b414458245505800e400c0d422011806005007040b0700440840c0071074460506590f800010810600c0b00100070b81e800502c1c400c000c0f51180115030070302020a201c2e65035841a031080da040c0c40041d50045003008103004a5403807903030150b04199102c00740000490030710711610400280e0710b0805030b56200700c5c0146500c0d2440203030809118000400036001d0f032141455119048415403542d07940c0f10300100d00d08601380420340c0b5000d0164016503111003001d21007548084840c0b4401c2507017100100f206e03c448889a64119820b0700820020300114420b28030111903540b810350200c0465898100039035072510b040e000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81723427 1250 81722177 81722191
    0xd02012f01180303150e010b0702060c3003010501020a060b060d240509060907032007030f3f06080f06010603060e071403180a0c0501030c020c0a051512 67
    0x40340c10b00c00201641401801c041c5c40f200d481241c0310b1414001400c0c140384040c071a4180910000980784d085468920076600d040718803a00b45e690044405c0c4813001d00801d58081c02007018040005264401103030760036a81a144113038010040c2008503610100102400e4031259403004090001c2c19050b1950f02951410540b030400b400d031200d8518040c200e0032040c0343c01491040e107200040114a0b120702e10070a074007440b5483d02281c5080d8014000390740710001598a4030061000504009060f00700e100000c8401c03156407070b0050341351254040311062080e4000340041c544a4010380c11080c401c042c1d142d03200405100d0008505a035003503081e00d84008445042000c0d00588010080c06405128500042c030101d280e80190749088440103140200703802c8013001124011002c00d03038000106000b07005c1845180102d5a000300c180c00d2100c006400351040b40e00003410302103408601c91000c910100c1c1000040c1401c01319a04003c204103800c281448580f0003080d003800485100000791100c54003c80c0b13 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81724677 1250 81723427 81723461
    0x60308190f090605070b0a0b1203090f01030507020d080c040b0c070807080c030303040807030903080307020a0b0702190b0c0d0501060903060c0c080405190527060d02012f01 76
    0x2a2110300a0100360181419409100544a003000010f810a084560190384100c0061482d65440c0c0c2807801410340d1581ca82d00511601c1400c0415a4000003c000044040307902c03654031544100110141d400c22500b42005802032084080d00c64000c05480d41c12010340700041c3d05294403090b80c5625074022240001d0a076000a03010042040107216860141803404094041241c0030408203030361f0300c00580020501c400001e43c840078907204602d18030140d680700540d95668245068001c2d45d4514803481601c8843d0200c002c55401d07400011843c0c81ca1041d04945074010341b598490244186d80100070b503021200402c00043c420358280b0600e80601500e8440380001c0703007903050900482c1c6028000b0410302a044080402107820501a01c0032503000711280d032a01c03150502c102c1001c0710503600280d0807120740d0f490b00106441500a01900c07500140010015a440808005845421640107804070710754031a41e09503815584020107010706130340a030040344001c03406050302312040b080503955125 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81725927 1250 81724677 81724717
    0xd0819030e0c0a150e0409033c0c0303090b0f0f16050d0c03020903010e01271e0812010b030a051f140a030b01032303040e1504060308 59
    0x1a805108041402003a400101031868030103001c40c2400802e80280004c1c4880c44030111059807150040c400c0c44e0402900600c03480c145450003401c42c2c840d4120a01a85c2000c0ca01140c04070700600d19180300c0d62416520301e03160020074400380c0303580c1c110aa0503801c141d10b50b2005804601410300542c000c12070000d2020b410328002000d0080c3c0d28000c0c0c41c5d44829411448104e007a140e1041c251813082503040030010b0095030009040d4000d04c103400400c6d40550801e60384444921041d445501c0b404a00d1044422031441050420700321214160000d00b8032140b00150030444d211500b44ac00c0040c495122545824400100448204402da0041c09286000000c00c01001ca15000f0240c200020285003004103c00c00c910b1a18111a0b0062a003050681d151b007414aa85081f0755900440d009410501c0c90b50310781c03d00036000d40102003444898410200c000c4000a40082150704940454984500f00e48903017121030b400000e079502d8698099241c010100209901e0310041c1107004400d44d90f04642 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81727177 1250 81725927 81725977
    0x313050609030307121d0609060114040605061c091406150103140403080c190c0606050603040206041206090c0b0c01050106020d12050901140106090e06030a17090d08 73
    0x100400078a1485035030020700078006010f0b0481c8492480300040807001c00e40c3d00f610405000c1c0c10700711402902d61480340d103061005404000c01c100d41660490000c4400609003030041c0410b032026441410381085041004c401d141140b051100b610050f40320707012130446501c0d200c070500040180c0440825402c003c05202d403080076500c40c00c4c608142030a06214050b9900400844007000402c0034040c0405d03a40002c020070000c1048810003108505400d00300003500030014000840048200c40f501d18105004c00c16180c0340741580e228a07401400980340c2030404045031f107807045d0460101c138540d84451a40d0009519109520042e05000c3c070425101d280410020b0300703403101a808002990440c0044012596203c060441c0c5004038603008201364450908250040c1110841005144000e50010a80360360102c107540c00c554600c4600f004a407220f1080585458560700d00800340242c826560041c110404041c00b800703c0020702240640c07695480e50440b0758802c0460740e08100a00300d201d40d603 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81728427 1250 81727177 81727183
    0x6030f09060c0206012306030f0901110310030201020601050a150507051507030906140106050a050f040510020c10030c05090d02010c02090a020306040c030603020d0602090a080a0b07170405150702070902031305 92
    0x4840444014081b140300d1420203c0c11620000d020007481400c41000206e03150000d401c0700d020f80c011030110940d203151052900350420800d0000302c0c014006d4000004030791803c19008000d0303c1c8801e9004c2e00006005002362525030103031388101d400e8007560007101500f00844001e64400c68058501040c0c00400d49800002c0b41d003d0040b4034003807800d120051151907840b405039181c003204d83c1440c50b40c17100f140800e2030341401107a001c1c5034083e21041a010040703034042a0801c2c00441940d60381c000080d0881c2c01e40036504032054280004100f0b01c0a030f20315140c401c13800c620031801030420005140446d00443e40c22202169001c881d84d4000060120f64103140c45502d8000005250400a8070705550000c0d038800408000608600e40200304100180d4900d403110700103003250001c40d140e2100920f4190f88581046404c00d010441d4102d1800040740031102240c0700b02e50200240c5407020403c441c00c14a100003a0810f021841004000b00380210288011406940c0400b120031050304c9900d00545 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81729677 1250 81728427 81728459
    0x132a050406120b060405060d0c03060606020d05071110110f01090c05030309010801091a030706020a0606050a060807080705090303040902090a050d030804062304110102160f06030f09060c020601 85
    0x118490102e1204080b034145821640c001808903000b0400da120000065007010380a0b030040c105036145000001004202c4d0b00c078001319000ba8090703444d80c603c0707803806640900540c0760140481c810a40603000e00d11b06007051b5004000d007810b291a1754004104018a804001c04a03c0c2031a9500c0c452201480b020302040001001c0840007940b61480d0000001c040d0030061041c1c980307858445402480900c00020286040038029048840c03003580c41400030350b681d0101000f628034a251075008600f500300090a007080d160240ca6221468807010401c50703028070001c11f080100401440054943d54090004200429603200c0241c2c485060108024085010f540418468801d0340d1003071000a8002c9422580943c0061300094043c5801141038035291004000481d125040f404010420113807003010240b43c3c4080e4202c501c024900591100f40380d841c0d00034141794141400c030411207240b098000184201c00400c01003103200321a41d4200655210f00030755001b60700310304010b0201880b00d103c092 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81730927 1250 81729677 81729689
    0xc02100203070504060503040c0504020c0604060612020d082d0a031d190309031203050a0b01020a030e0d0218070801060809031903022d0c0106050414132a050406 71
    0x1071542c01c1803a00a0300c54401c030721402d0280305000c00010705002040e015080200300c0030300255500e250300e42c8400e407254011601211100c0c83c2040100d0f071b44103500301c1154025805000da041480a070b460742c2c51160000d0a011301d03003010204400c491511138140000e4450045094262104a0320038094140d4015281d92694103105900ca4114440c0020b4042c01015220006140300016420300310b075402c0858202409002610450203801a07043e80418400c10f001c203400c01812050100498070b41440140240001e01c83e040d1084103032030b025400350300c82c510043c20b0281314140a44001511003048841d00081040000100f000303903080b0203065805075450010b986042c00b4591211034019080e89940201603001c03035a4001e0b414014420030342001d01ca41d0344038402d00700c0c010031581781d4006034038030640b942420307000241760400c0d018007003242c0c403581c100c40101d941c3c000200001080307620003540c1141e42564010320480744001c000841441c1400d44903142801c00d41448143d41155202c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81732177 1250 81730927 81730931
    0x7030c140108160516080301060203041809020f280b030603060117150703060902030a1a0406050f060927060414062d1206090d08010e130305130602010c0210 69
    0x1106042d00c0f03500c6070403003140f8108152030300d0304d010040e02c48040300700c0010443c807000400800e906030008050700c1110500c482c1d4015040035507040c0420b40d00d00080094205030040c11803145d0f8a402ca11079a21081c0b1121114004c815088070545002c4090744115030000000041c020326003030078000180503108141600f046410000c045560b58000c049104442450304008181070f0342c4a0f0f04000002d20103800155204e0038041715000c0184070421000c204094006a28030380c60420b4011002259001003010101d07000510038402241d001c3c80d02c0030381c00a07001c003030155010211101c04205003403a0340a02618944441400111407041a524a641603901d041041035601c4078404003041580c15401c2e000300503e900840b22070036400400b1644800000c8007802504000105544a9500f04080f56516180d600c0180c2e0341c400300703024002c504542c100c005001901740890b140c0a03d8400d2910341d1920101c49a1031841c240e181d080000103075100c0403940000c950400102c13036006000941 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81733427 1250 81732177 81732181
    0x7080702090a0501050109170a140c010f0f0905010e040e010c05120901020f07021306050901090e0616020705010507050a2009090c0906150c0d1707020a0804062007030c140108 77
    0x40c000c7d45062040820780d440f00d40c611103130004140100b01d030960380108900f501c200d03000c1c8410b807035403042c0c0002070000d0740604e070002d0b071a44924889000c580c401d03164080340d28108001101c0302d1402124442d045030300c034100001c14000074400d8203c0384015554494848008040c00700e0030074005004204541c0c010303c0305000320008401101e01c041d504503610a0b10070444001c05c1c01411a2b43c3c84944c0c420605400050501d94540201800310b1002d001ea5510742e0300d0110016144036884a0140141d0150302c0074005075000741c00411080740900308541ca4216103684d01b10a1840400280c0c1e54400c10025044950515281c0542c00c460a40060a50b212075030300816801840144014801d0303011040c0c540210001c0c10803204031600b03000c151101f00e43d01440c040c00003050081103040c1a080c00d000a203045201150140c140c0d90f1104135240342c10701c1c3c01ca0444416540420740401044c0701810050264010009030000318410101002c8036403070030300820344004440f00c1560600c15080d003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81734677 1250 81733427 81733429
    0x114070e21030c030a09061128050601060e010306050a030b01120804170318040203040b04022b060203040201080705030906010b1812010c030518070302041d0f01050f0106050c0c09150607080702090a050105 90
    0x44402c0009e080c14040504500c4c41d1060036100f00e10300c0c0015180e80200c5001142d1250f028103040345201c0c1c02c0c1c90074090300d503441c401e202d4140c10a1201912912089005000c0004100e019440e55070050030820700b0992980c03010460603900c0c56107207449034000150111a6680e082c1c40142c0c2d0f9100320340440c21890306440d03036030b00742c80e0082000380700c3c1c17105021250020040004540018500e007100041351602ca2401c0e200a60050b5400d038007040041e000a544540710300308903072107038003860090001646803451440094201d8480c8c650300801c01905566a80c5a040720410300038141e00020034072080c105409401c485014040796140a00c038803a6034501c1d075002615004407035050303d00040c5104c185100401d15142c110039141d00d405000d100c000e54000540002340501d400c240030903c5640e0381e07201034443c1d1050f45d5441031541c114503a01c1c0c180b482e0110700e80d60301942c602c0390800818180d0340002c0280d0310803030081300c1900000c1030030800e46c00c00ca15155402800c582041105505042c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81735927 1250 81734677 81734683
    0x3090d030c0f0c02061e0309060903040b071e0206030a021206010e012003040905011211030d0806010e0a0515040905011d011a130905090114070e21030c030a090611 72
    0x40302441445a201e0b50f4004640b180c404403101c4900300c82d0301c2d50185504e1360f10b1011941c8192828003c5108500125802c040007104035412a009507029600c0c0c141c044e5120700026480003c4d4840380b00d045011480546c80e4203009600c42c3c031400304010381d503020f4054464044100501314904101240b140c1e07440c6640c21605184140303032103080440445480608561451046410020840741880000900e150b8500f5460030841d00c070301c00b5140021510810300d65100b8004200c000018120340124906500400c0c02c11807100018000440d15500e9401103035031200d0408002c2e0b002480000d0070080741c8000c0c400c440c00f401812403c0034990000e103450000008060060f442500e8001c12207088542081e8201c40e6181280c4c81c00f051016501c054900040c0f07030071205030240d5400d003512681504c41803005103218000588035504040203035800e012503050703103e104104d007816120a821001d4401c01c003800c51120028001c2d40c0d1811080001082d1148a034000414440841c001c45c85001001c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81737177 1250 81735927 81735947
    0xa05030a03090c2102090a021c0905031b0606030706020c060403031119030c1205090a090506040b0607050a17030906060405071403040f0303060503150109090f020a060503090d030c 79
    0x15160101e010521810042c03401c076520b84c4441d071120081843c4288184c0c210304d030031501030f00071190588a1b0361004a0030007a032040e031202c02d041d0411071701900c00090b00c0380e0005250900400849060800340254440c90784099020a142c0d40e001c8030400c215458100040806001584041c050707803001f07a40841d865003d540402403c0c05400507406801003030070414076144c0100744503d948566482d040c0541280d5800e0420742d401d04032860541c096900a10450f408050054000c1d40064a4070030f004004004c064403456110381c0751800311031980e8541000d4014180581c000c2d115500e0146800b0b52569848000444c15100038000c100b507000e070101e2101e511171001d50700420305660b00c42041b128640202c0c1c941c00000c07400b0090100b1301042c3c8404070001442514104440d61b210340405030356444244615158140d110300502c079980c03807500403e030014460700c9500000e110581c000ba078815030720307000003000030408401c011505004202943c1e20854505042010403003d1000030304900b58 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81738427 1250 81737177 81737197
    0x6021506191d0703180204090c050402040e180a0515130206030f091b100c060b060f070312020702010804020f01090b040f0815090c0d05030f03040f020108090a0503 72
    0x6950002022030315010018052844491040c00000303072681c80208541c00840748030704002c10900009100603020344145012940d40c55003031110070b0300035420040a0b003030202007181e404007101400a503a48850014002900f24a00341a10130f1400d1a41600c1c01006241c0d00c0d402a4844510710300462004920b96000404200f0446229951400303014601d09400780d00a4210000000304010704440600c400d029521641c10340300402003d81210702c014002d041c0071a4011203040021600354010440210068410940070400c1c3e5007000c00602c554012100c180802c50000524104140d030140c2180d4100d0060403045052591580008080c101c0c000c00c000e004250740104501c20703a02480c0d402e8010b040244d2966540c980380e4600c00341050003407007210b1051183ca16002000c20781c00300064441c00c102d0009106941c2c0f01002c20004884000702550781d8042007000784500d40103103004510903809a00700716010030302031000414691009211400076040701d0041d00003d03001004480348004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81739677 1250 81738427 81738463
    0x2040b0903210403021203071203020d1d07090b030a140705090703050c040603020309010207060507201b040c051303030503010f0905070903140c221b02191502180a0902040602 77
    0x24006d43c0f02c0c070350311403440d025140407203041d412840241d06400901d0803400810007800380316131148105103d000032074035000300b5400c09002032294519a512040249030020b085034201a8252189207880c0e0b504500000f05410219050104c0e042c42d406040d0000140c2c501000b40e441d208142c0d0b05a40203e004200c1019000004902115400d4042d02c0381207030400810065070608c000b02600f052007000c1c85241000960a045520541c04229403422003000d0440e016200040300400c4000c1095840302c40a0100c1801003160300c06184040c000518481c2d1103c035a01d5041032040b40007046507078000034466041c0b10070403203400c1d8800104000c890303020b01b0500c0c450b04101c66180c14055140701203500440c001045190030b02480d85400ca00b1b444103402007145c10804900960004041080c00b40075a002a51101c0c3d0200b030000e081701c0c2c0c0360103040246003481440910303100317a9024021118010300c001141a880d1701e46503000c90004d1090200031840c00f458404043e4840f04201040030400c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81740927 1250 81739677 81739699
    0x3031b030c0a0807120f0507110c0a0504050402030708030d0c020601050402040506070f03050f07030c020f011106160203130605030411010203040f030303020c030c060708070905010903170304060b0402040b090321040302 96
    0x14000e002d20742031720500c1002484a80d00c6200e80b07030014032040301c0c240c002a0440804142280c40800c0303c04c9200c0e0041d15100c240390401c030030f02c409424003a01c02ca070548079004000a15000030300141440144071400451104411200246070000c10381185102c0c80c410002044540d0f2508200c90081d40d20012140303440a10b810280e40d18010403d14800201000032200c00f091740c050340c149071142c803c0328041c65040340d03213004440d440240146080c03507900c048049004043c8619408140e01c10500c112850154135040c1181490041c2d4411404104003005010402c0081c098002110b4021310042d03044c0ba01c0d080b114030b1003084c1440040c06244c0d0000c0c68800032281801211100c9041e40210b42650511480003402c90310211050000100c0c0c81c0c80101b02517204d45540e40c21a40c1011080e2080c0240611011640e800039104880d115561440c00034140c46d98000381c00100070b10b144844e100c04210b010300d401c12480d80d104110544044807588003600c03128040c0d42c152601036401052070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81742177 1250 81740927 81740941
    0xb12040b0a091506050414010e13050c0406090b13050408030604110d0606020a0212010e070501081305070305030301050a0911070f0201090e0c0304170a02060c0c0a0b010803031b030c0a08 82
    0x1000c0c0b50001a11844001503a42c040c1d5480d5000b040c00ca4000f52810444801e60054044d2407140c01c0c081c810784c10a011010a1402440d80301c01e0292a01541c00e0b034010700503590000c0c017112943d07848604080c0d242c3c0b410f4590351a00d09050300502c1426a028405845d007650303041060310006002e04e110703a95604102625401000c16a40c00c400d004408004550310741102070740d41d40702400201d01c150310002100e222902c06008074130014112500924505042000556450034001c0000c404080400600c0e0003099040000c20011401480615501d50401007404010010790300f2440c03086080c00c02403590445600308407231440d038000c11414489804c0e803004032519070f2290301920814590405100107941828001c50140c0c1c8030b01e12a11001403a80b484101c640581d1030b6460158006034001028054080010f00c001c140e40700944050b02100e50f10b1080c0058280c011443c554004020485001d0a03800c1244148420012507400c6d46802400d0000303d1040304410010040360301c002c2403034 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81743427 1250 81742177 81742181
    0x20d0209090c060c060108060c040b07120e03030d0606260105090c130f08101802010e03010f02070609050106240f020319050702180105010903020904020d0503070b09070b12040b0a 79
    0x110b4008200c2035891050904999640c0802c0c06000107030300030100405e6500c00610300320307003c480b401804036050111580311295418002c01d12030041c42545045005a0380e020b00c01011149480d030000100d103410407100500d802002182c10300140400c0400c04800582032103c64115603084480040310303559807450507494041c590303800c0359400f0580404105008043d815405a814180490b807110480743c0d00001a1541b0180600050100802d00070240d4401c3c4014901c0390f0700900041010b048a40b501d000304e07403120360103969450f034030310466081280a00441008040800e00024401001001070320340041507071981051050121081c3d40032b034000d0003600c08401c0e0413aa040c052110805002d0301c10392000c4000c900c15203084e00491841c1100103074513070581c0d0303040e960300030900c1c219400e0202010010b001a07901000720166100094810001040018810f250b50619810080c0c0c40602d80f81c80741d0401203603408240400c000511810f451594480c0d002440d14200761030754020100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81744677 1250 81743427 81743443
    0x90f040f110307091401090605030f180d0e01110604020f1903021c0506180d0e010c0506010f0806070e060307260a020c0706050c0d0807050f040f03060b03030304020d020909 76
    0x59070401008100c9515000807188049a5002c405540030409132001160b10801e0b501901c004284203001007484801189070807517105402c200f444242640068a60740360141c810140d00004c0c0d008801e541281d6071001081c0092281c540003403403141083d50018407842a080c0003a4000c0c90035400d010152400780c08260003c42c0c015203070742e84500b1102c0002c00c2c01200400e0076609803080d8008244840f5044452000d20b4043c20003a2090a180003021200c0c44043c0342d007203040020b018040d07008140180311140c000d0108038121038510745811045230400c00028404010b0045c40d4082104680752102240c1c1c0c851317400d01e451020b502458000d0f022107440905420005210101000704a01a030ba00620380048500c0c12900c007036640d85021900e500c03c1200102868120100d134440c0c80d4060426640c0180107410001d08151102c1c68051480d00158800008507400c24800c10900c00d5038883e80240d101c0a50180d171851a10342c001c1074022107505402801740c1006c50003d88082001e1017058 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81745927 1250 81744677 81744701
    0x80708040609050f0d020a03081b030f040f080d0503040206130b03040b0907170309100905030615150a1707110d0804020f01020a02011d0a0f0b030f0c090f040f 70
    0x991200e88503a07006107042e03900e01440b40580c8440c11142d00500d00290160b01241d40180305099060a5540300d910a8200410501e9189003515505800c01e1040c00034060203800356204680383d03071804031145842c594640c400c80103500082a0010031690080860364015015214144d581d2201c1400800844507940011100c05011080c401002408a040b6020f50644400c0300c05031610b802640c01446030400081060368010441c021460405141e921140c400b18102200340c981e440c404070707042c49400c0f114042080700c00150607803580740281084244a1030190502d0030940d0480028040000581640c084180348000044040b031040c14000312004007602a95403139024004050440d4000765400c9100b50140030220302e05500c005030003541c294050b03503484202c1e404c000c03030303070b0007440301c400010350441c0010b280030881110a100e8a001420903060442d40c0745850902e00d004c1a4000e000c2e044944002c0003000280d548907950800310304803c80340011500002c4c04500c0041688000b14 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81747177 1250 81745927 81745943
    0x1b16030501020d05010816050f1309030207090f110301091a1011010501051530070807080f040503040b0f0d0e01060f060201090201090905060102030c0a140c0d020307120807 76
    0x2104020042d0050201000c02c2141440543d0726405051703210700507000d195000c9000d21030200521303e000803640400300701c040c0c82060024459080d10742078590309013054001d42d00001080084030040d200e107800d0b00b041207804001b1a0642183e10159220621400b07071b90300c1d00c500801000c41015002500011001003030032040502501026000318098100c24505510b001c00002c0ca908040c480591401c210056540c40c00110610908000c0c0b91006407440714808403400c983d00a0144200714000e4007161901d0b560b42c03030b0801c00140005001400c6840212002d0f06000000c0e03800401e0f2420b0780e5444070181c0d110104000340600c1c03801003800d007844481c00c0c02104a0342403810b502440540e0444541d40b4101a220304080c0e080e10b00840d0000c2c0080c8805130f0812001c40076500494100105205403881e0040c2040141d18003115940141d40010412500840c44e84080028040d8480d00b603581581c880d1080d00000e8039011240f0910360300d4500380403804104424042282c100369440015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81748427 1250 81747177 81747179
    0xa0b0405011d010c031811121203090115051903030815090a020901030605090f0c030a02070204051504050601171902090d0501060503010b09150f041104060e150a051b16 74
    0x22540c0a08132400d08500464908181c404e400400d40400081050308181608804e8400310144512180014001c0ca02d41c020724040030050b41140e4000d40c05245500300100d00807031040d440c0c41c0400d1096201c13600c10368107403801c940c0510040782200104d82e01400c1003600c41c2c0c0c5541110302d8942d41c00b003846900c2b0100000300011801158013030040007400383d0382000396a03200c0051040c0c03107805072008218a41c1102c00154042c0242c8021a4011244627000d420000700c1ea000ca02654000d948150100e001c83d490710615040a1040c0c1d41c3c4903209103441840402c50590a0f07100030800781c00045d00e102c1019251000ba01280c0440e000017001801200004803141042802001a4051580700794244804140300d454880303500c900801580f144020308012001c1080998800619010780080d1120005004c4c030600d1000383c4010055522a9421500003030100032188001070b0607040050014044403500075400300542d00148085c1c03802030880710819074098545850240b40410348528080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81749677 1250 81748427 81748481
    0x41101111203040b01080c061e070b07050705010507140a0305090a1703011a040b04060503060102010603140a020a080102070b0f0403050405060d0e1014060103020d020403051222080a0b040501 84
    0x2c41c810340c0200e00a8803142d0302c61002640361001c44800d160b0081d8103100c1c0280e0b84590440c1c5a0b40501811080d0303207000e10f282c3d19000c1e8041c00f1901070b03011450200d221001e100e800c0c01042e51201d4180f4003d00c0b40b00f0000310840d52402104008001c00d982c51000459441003044400701c0d16800c854010320880c60b40050302100d610900901010041b180103149800042d403059800392010861950300380360514504407499040184824119074840d100007005c61406240110003100c844050410b9507068014410325107a29031081c0c1c0161720412420010034100f800044e0800408040d264a6451301d007400c035968000e94204592026002400855024943c2c0c0500038084200040c2d48038914424440021100300154072070b81c5281d1079000809c076601c01e40c01400803000318000141001d4503a141d40f0302c0e10132800c850403a2814005001200c0310b0310400c550350540701000c40102228102400c3e140c55582c0420020250298500820f04001080d040303618017620015800c000810102 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81750927 1250 81749677 81749713
    0xc1103070306150602010e030406030207051903030b0117010f050f13020a02030405040e1504060e0304170102040e130f02010f111501150f02120c210a0e040902010804110111 76
    0x71140310301400c540b00f00050428010f0103800d00c004d806601660604c1e141c0f90054020394001c0408840a003c2d10b41320845000d810902c61894034042d6800103003503d540e9001403c0d2100d20380701340000680c4980104011402900314405072541954003021144613500451003045e08504d401c91100d00104098030703125070000240040741d504079414004401d0307040c481d541742d00824203008034800191001038041941b64000c02411550340f411070b85001c0d80c178026025014005400e4082c01c7e50005820441c1170304c1030707500c50b421174010107916082008654812006100d01c00c0000e0520280389182042d090140d190328210520140541c1c9408514584020010409004822604c0748284400854a106201c4030300141c80fa50010050f80c03103103403d205060741008108500d14814480000346c0b043e400500000400800880c103038458950010140038400f500800c10701451030800700101503a44400640c0d00660014500703c005294070b00125088111494450180e102c3c00c0c099805090380b403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81752177 1250 81750927 81750941
    0xf0b0f070b010b0d0b2b0309050a12060f0501180b0303040f0b210c25050a08030118020913050601030b03010501080705040e010501050102070b03130c060915110d0c1103070306 77
    0x84e00c420002030600c0800c2000404030705c65003040e1915040c00d04414925540d8200c11914080c2c18200c3c01503950b200014612180c1c1d4010408908003940143d04200c4580254012650140300034440c4c0d604122450100a4148442140803915100d00b614981c900340700300e6001c1d0040e00c59010388503844282e034501c0f580c0440305416034041c01116440007000318503011400b07140c2c001641854008010007402c509466440c508500802c0c106280340082c00401604600510038140f080e00c1c3e61405400700000d810b10f4034904005801007041a0081e40c80b90311141e608001003800080c26103540300103c004214190886415618220002c100100c000030113400f1208111018010000842c40a0b42611420b2160a0142e48482c1e800e01070520000e02a544c45105a40c010709614041d4450815000d525403082c03012400070701050011543c015480c031410321440c10180101c01c00000140c0c0d452a040291108021000d0100c10030030110300400078409070300508031210755459040241c0101030f0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81753427 1250 81752177 81752197
    0x306130f091101110d050f0912011409070816090f0b1003050a0c0c120509060c07090b0114180f031006030501020d14090606150c06040507090e070f0b0f070b010b 71
    0x10782c80803030666013001440012145c1144d0b41c01c1d05000020070faa20b007541000703840359440320b4a0040070380544000d00c81c40500c00255204440141818040c41c0d00f0105c080e00000895081640c695540800e5031600c0421100100d4001941d40b5042041344010011942d8031a4042e801880400503103a02da004180903524482c01005103c105a100352101000c4000040c1111041140101d60ba8010009409603070f1002c0e2441d89003c454241641c00e10099401c6a0280c0e60317103c40005035940d200064200080307841845915201391510144021505144114443d2500903074454482c1c82c244071401c140c00345680c0030b1050948a15155000c0d40040102180c4145030185808082048604081c05010644054541c81d20b6071400c0c4440007400c4214855450f00c02c202000c0401d608009080c40303103010304007400d00070f8280486102a5590044050480d40c8010b1052144c80031020700c59084035403404010303999420608011020b80900c07900a01110824030000070b484040c00014028580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81754677 1250 81753427 81753437
    0xf39031206050f0102070b03100b04030803070e0d02010e0405071101020406030b1005040609030b061801062313060c02031018030215010303050405121005070f02100903050306130f091101 82
    0x2d1110140103a441010b100d560043c1e1100104004000800d070046800442422010210b60341712003000c08e5030f0340958811146140300008005a45510a20140f11035030100d901c2c6040030000e0300002c05a032035078508903105540d1140440d203541e018101c40c04071110800c0080d03442e2540d501d8043d0091a942d1402401440303159400031055204200321303000d43d000c0b87c641402050654440000d400402803025070480000746c01341c0c90060001044500901e425a40c074402c1e08003107405c1d260950700c449104003040d04180034003001050760507042d00070740b41c09241c8030030040840e0001a152046145042460301d1400c04504407000020071041c60081c0203400f20f4580314a014441d04d07080b80300748800390001d030f0300340010310082c9060710008201845110841e145c0d5522241914201c2d0019102440030414600300766002c4d94040c01080c0c000802c8a008004622850714003604520005100b24840c80026060307900140e00b5174009500000c800d030080200705000d00c4e2010100d1541c070100e50100b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81755927 1250 81754677 81754679
    0x1b090305070f08150705070206040e010302030d170705070501151202120a050319021c2601050f21011e060b0c0703111813020a05010f39031206 63
    0x40e6500b000100320341800e001000d07010203800e5807440b6050b000c0c2000040010400204015988803405000134201c0da001d04036295265104140c600303401140352605001c0c10448540031307400088d0003035500881c03500f02143c0d20612423420500515000c10503d24540c0071042c0850f000005c140e004a8640c030a8440d442d134150b0b07130603256681341b54207000140320340c0c01001150090031007113410340c0700703820075004807018000c1000171014540200c3c7e080700001034144128940c00448085125800e0f03030708240c2650319506200c0401c4c00c6c2034002c030905000340c8140d070080e4051510100c4800c000e041d8040200f0602503032034010030030f102400b00803025207401c1c501c1c0440c0d0303c41c02c203040b56608403058006101442c07640c0e6030300d41c1d00b40c4400e07400340c0e101d18031070f0402140c0000c0720b80d024803580400c110410041114030410028400a0300001c0c100000401150122600220080b01c480701c1654002c41c00d1036070400014800f0b01030041a9100c20807174400b00300300b5403c6008402611500c0c2c00c01c2c8505 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81757177 1250 81755927 81755939
    0x2505030c0f0a120c020f120c330f040b04030506060108060a05010206150312040605071a04030804030e030309060a030f050a0b0307030b0a1103010303020313050609060f09041b09030507 81
    0x80c031280720026201c525080e01070040c040c0200e02d0040d400d44040c6c20290740000d0200050804a64245044550381005840d50940d00d01007074003002a500b1120485c0c0c0040c01e1080c45082d5a03a4100000101c00b4002031402240d00d2601c01d6074014070140301c005079141d890f441c045840c0c890039103505010a0000012807007514211046600b43e80b0180e0041800e42d8803022000c0d402501c81e2030341601070140301d0381020b0340d07401007004002900c0389444456a0318550f14201007452041c84005200702031440606c400250f010300d0035500319401d464130390054402003000a055104202c5502d81c8610009103040c10782c3c0c0c05801001c2a120144401c2086640e400d601000b540c48521603107a258020040c244001079150039995044001650000350000000701c90714915842a001540941d1001c80d0b01503807041851444000340400341c401c03906101070403020440900440c210003124078404030390305c01a074450f40d110b154401000303418440c0e100c1c10000f000e0030030141e070b00041d5420700840c1c1d004994 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81758427 1250 81757177 81757183
    0x105010911030a0b151803060109020c0d08040503090306161d01230415090806010b040509060d020102031606050a060504021804150f03051c030c02122505030c0f 71
    0x44030303181d4030115145543d041203070780013000507118440d4003440c201600345120a20380301808110300000c1c8000450758110041600e072100592102100900403c503038400c0b51004100d8403503d120a041c80d0390300361114941a401d5001e8544101e8152280c0b40c2000f0481d90100d85144080c00725884800d1341501d00840d031400a403400c04400d000c2800c908142c0103202051030514440d0400c1c1045c68140f90300d50010f080c1d01035a21641c41d0010300a16004c0c4507960082c00f5050060070b0700d0039114581481c22000c20481300b4010003003445201c41d41d0014082d6402030044440211062002d4139007034003546000030042109075410420a40380c44000b1500741000d01c00c843c0b078802c0c5511192050f481090811000e020034000000341f008140f100016010800c41c41c503c046c52043c0c001d032035100c903441c0180100a00000703034030081501300075000800366008a0341d100713040190314045584944440c6444080070141c6458100c841000300da590501001201034103540981e107080e5400c2e110b00400e460782d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81759677 1250 81758427 81758441
    0xe011b110a0506072411030103060603050c0603042402120720150a180803090a11092503060b040602100b04141302040f050a021305120a03080c07060c0f0201050109 72
    0x804001c0141c1401162130305100005101c130030390040460781132141c4a118001f0b802c00c0c1d00845506441d01e42c103204010040c00585848641980d1450841c50103031580c0c161100b0b499100048140180d03029500a10203404951199000c0b00c44400f89040c1305000411f1b14000b40280481c100c03a40240184d95100402c0c2d40d5031f03081c1400000052921004060001807032414000c00c182c00b05400003000040c0e4070704c055840f0b0003ea6000e400c03121840d08150740b200a10410303071413082542074100801d4110100c00c0034510703480c0c0740c3c1614071580d107418181d008140f960005441844003040014900f64001120b0303100008044007485483c3c40f440902065a00c54a0b0b016552903105000400046100c0c030340658a900050020032042c1c1d1041c41c42c4101c071400d440720700e00c0701d8001881c01114180814910000c110548004088500c0c28a0094450310241001000c2012010103e1004061201038980e11034100c81e04100d01105184050f00c1000400c0501000d07509180000030000c4240c49050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81760927 1250 81759677 81759683
    0x250302151506031009090f140303010b0301090b0301061a0706060f06020a140a0605040b04020907020f030a030c1701080304030c060c08190c0b0a0e010e0105160e011b110a050607 78
    0x25054490080400c0701c1c54000421000c001d00a401d40090340c0205e80c011a58007d014550040e0400882d00f0442520b04500c19180101c0e807040004001d0550f2071001c890443e18441d07000100190260002805030205034441300400e1060340541c00300c01d2900c0010b09549200e20f80401c45207a6600382d42101d0305041c03190382c0250b000108104d01207089070b8500b00d4a842c103102601c6025034603940d0002101c1043d2020fa17801c070079460030842142400440281c1013401c80c0004c140d80002420017076500c2c0304120140c0c08040d01c601d090400140a00000d548030101030105543c55a1130f0b04c1d000e42d4a81140c88280c40e2916400c00c00a00c4a02504076078081980201005207020719801c055050154298007410401520507441d5020611045125000d840362640105002e80c9000d146420b5509c0300603080f4440e4940414001403001031070341c0c00852039450801c3d00c180f01c0c0c0200103948800c10740007000f2480d842501002e04000b0214040003a41c0e1049030501100340e1140c05200040c011380a0007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81762177 1250 81760927 81760951
    0xa1b0b01050603070203070510020a0306050303031006140708070b0f0615220506031005010e030c0a030b0c090603090102030106080c043204060806040b1b0a030506040225030215 78
    0x41c080c50408100540c0e1190060040341d1600400b03540340e514124203840341180d2141c2c00315804034800d515004000091004a000314158105400e003141044983d2082c802071205003800c07003a0303c0c52100291580e081c0c001c410756450380030398113003507240300003c036010b0070843c8860000914500d40a107a5145846a02000130b00701400d04000c07064109039080f000c02c1200e8421000a4903540d4900110310440c07246401b0f400c16480c0000142031240710f48200e6100303130400303080c960740c1d9203640c1540002c40c2d40100c078a843d170740c84070780b071000451041c02011a0464000820013a9042054000394105c80e25a621441c06907140103040f4554003907801900134595444007022400814a4074813090040741c01c047d4200000d0200004048034000e602240303090700110b0400090250680f91540d20204400300403a0030683d5800b88542c91041001084c01d0581e110045200d940740c540c1540d1005500301c0315541007540c1000202d508240703c07107045005208041c09516043e0120303102c00d0080d00e1324001 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81763427 1250 81762177 81762179
    0x40602030a080a060909050a15050714070c030206030f010f0b070201270803040f03030201060f0b0a0f0201060e0f06042415121407020d0504030b0f04020609030d050a1b0b01 76
    0x1c00ca802401c042c0110100d15200c40c8082610207440c030405081600c1980100009103a915041c0050000200000e020514000800102e80d0b04400099950881800401d5446240f07250680701200140c1002c1e412540210070070540d011132450f0141603446403508642c0301a03540f81d5180c5940720354131000780000c9900061124006460541c2c01c00241c1015a415419407500281e03850768109610201d00c5e4107103c40c0420a058085c030641000d080081e10b032140107800c5c46402e04030b510401d0821000c01441007102610580300390b01580c0035040d514000d480c20f04040700c48044000003500e0b401c0c421031800b0140388800c0403100d000305407201090f4040080714541000304e4882070750210503000344240010718a1025601e40b08003a45003031064620000b43c100b280e002442c2041f10070260081c003008000c14800304805000c0700d5405112503000310041d613100d03c04207084d405110344140c0c0500c50a031101041c150000080c180c0324415a4408101101e4903072a82c25592021402801c0520b074200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81764677 1250 81763427 81763447
    0x27060112110a031805010c030b0f030f0601052b080702090c070b0a2d0213050d05061b0408160608070309080904200c01050103120f020c0108040203070b0a051b0304060203 75
    0x2000104203000c10340c1c0303064201340e07403186429140d001d189080003940d18013505007545013901c1030515061058000b4615880100c070b10964800c0180181032058200f11900304e81204031518801c100045003510640540540c41c001c016034000d100c00324440d04101c0e00081d4000d9030002a039881a40181d641c0300944c41d4640740100508102001d405078000c08402840b540e640b881111f00711054041005030360342c00390020784002c481036801c80d41c4591590384180300458800940e0a8100f255860450010003990300c0014091080f544a00702ca401815051214a040b0480040403205261900380d0203039200030b421000c07280c04400042440c8030034803410100b410aa40114021000d49006140d085000100c1c80d149800003140c011540e91554010b03c10060994540c040740c034050b041140107094940300103511282801c070400d0420400000140940d03504120a100410003c40030340d650b107a601c04010b01e284e022407170610207503404140072807e44000104a400302d406641c0914200b0b1900b007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81765927 1250 81764677 81764681
    0x3020a1b080408011d01050a0504020907030213120302030c060108010213030b040c030209090607030c02030306010c060903020703080f090f0604050303040501210c08040204140f01050f27060112110a03 88
    0x2a00a44501c0c20501010810322401d21034112285420042e000426800444040c250381000709020755a501b0481031000503241caa08040c0c211242c0c0c06c0158807440041e02441c004041980301a0710308407a40c00340700615070044010b01003442c140c8280c58a81c0c4c1c0300c4403414241e202d0707801d40101c0040c240c0b0702000859400d0100c590024858030914100c80d60b2900044e0b2080d0083e2142291504101c0c18010515050f1151110540e0140041e41c114a03000b40060420140e01c4005401a62101101c0c0c1c00c05200b800100040c55100c40b040fa15a2120b2034295181d13040789030418040c00091800e00041d103860401d035811103c00a00451034181410011525060403514514a031148140001140040c50180441826113560b40400c149031500420054440c582c0d034a045c404032030814450100012245203040d141c040d80c0b90501240c2840c00716031005d0176600c000080100c2d8141016840342c203241d0090040900341e80d0703000c0400000401004903030450003c5150058104601442c20707000c2d03 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81767177 1250 81765927 81765977
    0x254011511010f02040f060912020901050607230d0e0114030c090a0b0a08040309060c02090106030e0a140a050c0a0803031b04090e0c12011a04020c0a020a0f060201060603020a 77
    0x25030010038143c208910460590300203030060340c4a20034001d410302c81b86510080c040e0050642c0350425609042036000302d001d100044c0100c82c000c035400501c000600c80c018205c0c2c03481c606484c207101211000f04400c0340e01c94031110820380000b19202c01e00c1d0059032144605a503660320122080d40345880f501d4043e94250700c014076035a041a00c1920014010700d64901a09070036000b83c98480f018605460010f00185440d0403803420321201c3c541c0ac102680381c040509054030b01600b03000403001d0310b60ba2401c1c50100820b800a0880c481120032a80541020a10242c100d20940c2180c0d003c03220b10701040721480d090f000f10703006c43d8824000614414a45018100c0300d0580b104800c0c54103490b600034001350380035207a40c5010759010b00840324590402041039032040410900800900c480e0207081e5403030844d01030045115680111304800790000c24400c1c105110760080101d0540c90383d6650200c0c00c0c40452107600050b51a080000401c0d82c000c1c0203c2d032188003a80d49049070000d60b000c2c0070002c85c0310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81768427 1250 81767177 81767207
    0x11040e0f180a051501050604030f020d0602130807030c0e13200a090209091501050703030504080909040309061b210c05060a02070510061202540115 65
    0x494030340700040c2400d1207202c28443c09070014201c5150412442e144060701a441180070f0f9400708810000304000b00041c00741a03078101d45c010904180350612038082d0207400c2c004072401240da030f00050b580d0300005418007124841c1a201d60782c295900000130760104111411131220450329410000900c9003604506060300d41604041080e000a0210b80d80c9040c40c2c104000b07169002038044c840b03241c40c0e0303226548001c070f541100305003880f1100001e01034082d80070020141a00e5201090400180d6030584150101c0a8007505940c50036007801803900038180b0400011440c550494a10701040640d0b841045070400c24a01c0082111902da019510081e8904010811600c0c404400604144a59400303182c09000241c1c45900604200317042c94000da00844915240038020010300c50b0013440000020b804940c00005080e040d034078048208488404540150b50100301c0302854103460040c0b034800380c0421500d0101040404414482c00f4082c050742c40b1a401115600f81d91900c990b01c00f000d039a80d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81769677 1250 81768427 81768451
    0x50c0723030a120506030a02100e01090801020a02010915060803040608070509032d0f06010902070f120f080108060426090d0b09120a05092110090611040e0f 69
    0xd040240e80d0440c0c12841540300001c40550380b0001c00b5005008454100c1d200300c0281c42c01010a9001455840b1800025018800d03007141c04000d6a004002600003003c82c140295a58864410020300030b00c604131088465800e610b002040100c8548034200c25110404021031515041a8040c1c400711002800b440c2008420841c0c1c4030b90b0788080c0704965900b1954002d090941c0d0843c102004984840101d503410380d48840d41550514100080e4035044544600c0010ba9500322130038905043c21260002501075410f4601032404c3d00e601c02012030083e00c69544420b502c4c3d0301e48040c81d841e05000d80d0050b2001086c00300028100703019000c040c1100f2440d600140c0b400c1584000703d540c00c0503030344090310014910400c04c0b060f000c1c144000360080244c040c03c14641900c03c0703405400c81c01024881400b074611428000d040003071448801c1d011403440c004484443c211032441e10041c01802504680329418110482c03010403101064070141d481010304c02c02280c4d94040c1007140320f5002444594000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81770927 1250 81769677 81769733
    0x30f030c0409021216051321050303040c06080c0a050315041523030106231504090b01021005100b0f0d05040b0a0501060206060d060207150509030a0909050c07 70
    0x5409100900501c0d0b505402e140b140e00d000441c035500709607085405c0003800001c000e9007500910110510b01901d40000224030100c0c0c1c00c0301c2130800b026000200400501c000014042400a02c1200c07204440b015a206c0f80566038003500001031340100800c050201d0414404030703c10011003134513111184406040064541440c400f840c0030009240d0144022014041e860070050303103000340c503401d001000d034001d200389840c1810011000c0e034080300d400c0000c0850785045420390b450003a92544072841d15001900c450b00c401c2814000d02d442a4111301620452408103541c5000b400384921070b50400084401d203510746a5901c080364820300c036500c0800005c01000054403014030a55011b140550880da00320314181610008448060f040742d811342d0300200030003402d03aa500910000c1d240d03000c0c9001da15040c0503d00820610607440c500031400781400108502510004017800407050710f0307a1610566030741e51b1212411140162a8001d22040401003a00800e84a07915848980201c446000f062 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81772177 1250 81770927 81770939
    0x10509010504060f0315060e030c0d021503040809040c03051503011e0f02070f08090a301401060e0a140129070609060615020c030c10020a08030412110708030f030c04 73
    0x311446400101c0403802300e140c80b0445003810810850f4280c0300350f85c002680c081c8c46c3c000800c03035041c080d4280503a141c000006800c1110450a0f40c803204c5025106210000c010040030300a004211130080700300e102900704070b00c91718050040d0800503800b01811b804401061080c0e00142001d90705014440380c0800031800000d01030602c00d01001c0c06803000035147c4c80c0700350420041d40030395801410100310601417024642418142c400d40a04486140c1824031040d207450174a0b079082100b501595403800c500065030340c0503d07101a00c2800346040c1040008011f0320a444006028043c442e074100b40000c2c4062141c100c14801100b1242c40d0b1b55a81c2030a9003560b6040039108160400c84100e03845000400803480c2c10716145007445684d0015000f400300600210b0b0b6508004901c06109921240013040501c1c000d100c07886100c1e0b00000130301d0380c030710706400c003603d0480c00701307400600180c3c1648011001d004041443c600b074030b074150061840c042ca4030a4246140e0405070200200c001c081200080e0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81773427 1250 81772177 81772211
    0xb01090f030515010602030c031602010905120601080105061207050d020d051009060b010903020d030c060608030703020f070509010e0403080a0b0904060b0306060402030c07230d090311010509010504060f03 90
    0xa600c00c10040925601c500d40c099903ca006900c01d00a540c0180b2a5407440130300072054651400040a0541117128603000490f8918101d0f4040364020014584d01045940c0100b03040b0706a40402000784581c1d101c2200f4440304104c160402080c41e0071207482172200f891b01d0684486003500090044000003007688440e8144100429034240180d80d55020300100905805946507200f005d080120411b450758002c43d0304207000031002030401034441d195100700300c5035034400c1c0040c1c5880000c40b9111515440d010f540c50444c0b110800c8280b00e00f400c001058503140715400c0c141d4428240c182807584569405030381031407000d003580d0841521030010f00b006032500103055102718020200032800e100407000707050034010082e0001d40a80d00410411880f00d10388001c95403607a0b030020010621081c1143c2c503021901d120240c0b401d881c0030302c145a0301010340c001113041c147c13809181d64100c41c54111005550314401e144200b408548107120030082c26016222218006265040c040f0b05110400003000f4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81774677 1250 81773427 81773429
    0x209040e0312010e07031b2001020406090906051c02090709050409030915110c060d0e1009050d0305040302151302090108061e01080c04150e04050a020f0904030c03030b01090f 77
    0x406001607500422005101301010f0390040b03600c0c1010401d0220070000344409074007800008042c41040944603d074240c280340c190505100f028000c544454440c10020141e0f2414468995294144000801d151606901000f010070300a5a4280c0180346035081c060200c03001031000e01400b2010000280c951228011014024840e0b6650504981403607065035100007050b880c102088080c0000500c860b5000600c0080501c04132419500e5440100c00080a0b082030b10180d03185015a8003080200c010b2500301d0300710320b44110290b884a98070a80210100e0b1030491340a0011791020380020312028401d02100d404c201c0d801240c00c09028250081352a0341e00a92084d00f4503800b100030007402607580a0381248a5a101c42d215482d940340041499941c00440800c500c201c7c0e48414030920070f1484c040c00801805a891642400d2a0504102d610b680400109070301170782204814480b18940380e85418429581625241d800c046552422001015103100c0309040c0071a2080c04141c01c0c0045514034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81775927 1250 81774677 81774697
    0x40504031205130303050a230603100614150304110603040807080a0c050106080c0f060307022b03230a110412050106031106030106090b0c0732060903100209040e03 72
    0x3541030604c0c600101100d038001d10044040d0318000d0901072400e00b00d40c0d04618141e80c0740f000d090585611001a00305070280c00a0ba040301d02c0d000000502504451344c0c5a03114508440ca81100200303540b20151034402102c0082506032050361444c128640076004d55001805060a6030070101241da41050a074041103e00c404144049008070400000340641c0c1c020340300c600090301014001e8400b040150340c0c4070449510403140400002e014500c2080740003004000c500c11000c01c00460322071064a880941e4034a00005e0070981c2d0381c0114420b1a86584100650690242d40c13070743e802034450003d21a08c5c05841c40c03030404100000c1e42040c900500e2045500131800007403c0c91852600380b002d0100e002d04903004001c00d1004000341d0f070308607d0700760807034a130502c004e43c0d295159181030381003a0554106030710540d891019901c00300c2000b110382c03544800d56000d0f800542c03084410451a0301030300510b079515511502d900d02850106070081d00c24594080c1c00842d020307a840b8502c07412364101701000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81777177 1250 81775927 81775951
    0x30f05060402090a060501020c01110102071a040b0109050606040302240406050c0c090405030901080a0b10120c0201060312030e03090a03050102120f1006080405150124030e0c040504031205 83
    0x1000c02c1d4906180c00e00d800240c0d01e14208a658038200000c1d49490f0744080d024180400403c4200082178290100d85049a102c814000d27401e80582c616441a181690706641c0103003014004101c40741a44a11801402c005004a08003071a6900708100c246180341301388410b010040b100d400a80c2c0d0b00700030f0006444e9589402e81c60704003031040580307001d10000d54a0320a0f0609020f1201188004c41140e074840c6007883c01a030b0644e07800c0030a00290000c0407455030015004004040d401e54050600c4550582e2004248547d10b40a0022800d0764140d010242114540c9003180b4405400f0394416419044144196810a2615400201b2582045e48203403003594001416445841462413816407041c1a104010017600f046807682e8242103d601885081c402c1140114043c0002000300c0280410001034411a03076071507071480f050b01a1120b240403040c00303a0811202905002c0d006000d056042507004040f05180c20080101401d0040c005405201c54034040d4104020540a8548280c900c8091 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81778427 1250 81777177 81777181
    0x110402070b0c0c16030804030803060d0807110901090902130203070905040504150c140d150909030905120304030819030b030a0501051504020304240e030706050105120102070302030d15030f0506 85
    0x202420100c508601e05607a0f85613002c20700c001191101500c0c241e070f0f04980c1d0a0703200c1d614500820309500f05072002401846002c1901c2080010b070b0b002c6411201ca0580d102400d42e661203602c0b0094a41015000f0b61100c1ea03160880120045a03025641c054800e1515138061540c84004c44c0840320140c2d016105100c0344903010a01020310f000c0e0a01c1054145800014040702d010420a28005c03a1010040c0d07617100c1001862800c0c0558640018028505041200310b0311850040c1100c4601d200d007500483d10088894403803e004015102100c1e041118145807001c800703a415143d41c0da5140d842c00f895a01c40d070891040d2410800d040000b4480d01c000109801c0034000e4548800d040080c90344900d004008020006100c07920300a4108034000704440c1440c4003100c03220240c821800741800320b100c042682e10500c1003903081103040b40e40a6030906800b440510b007035030903441101d40c042d026030320401181d2005072603544500408001010f1521a56840340d6030a60f020030501401e80d2564000e01c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81779677 1250 81778427 81778447
    0xb0a0b19080f060c0304151103150a060203040501050703200a05060702011b0909020309100e070614030708040b04050a02030a060b121b011b0203012a1b110402070b0c 73
    0x109151003820340b8014a064640000f0200051200a00040c80040200311a03002032066030811980032082450350742e100c2c9400c0304003030108140c4c0942c407485030840180024442c1c1c00401228140c03401a99010300d05031143c2c40a44800701411a8422a0403104450600c075203030501c00241c2e114464400b034036607810080802420344440c02d465600403c41c03205202c007183d03080789003c000c03119042c1c000b503240e40d08c80b0140c43c1494002c2c108204c5070b909011b046400c0d03034004151007042c0da4003a03d9207954420564040345250004a0340400490941c00101d008138160341e00c034940c024818000c0f2400e440c0554003080c103042004034211170240e1910b402c5034152424401d01c6090b0b46111004110200d500d54482110300d80d250380c11414014201904800000503131820014550060300a008052900c90380f6491880a03000b281c410060011400c040c844c07094684200745100c83c0d0b007400061072551902203d030100340f0f0b4a654440d508200020010700c900106610408079980e00c140c0b100d201213 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81780927 1250 81779677 81779683
    0x10b0a08010b01050405041d01060b130906120615030501020c0c0a050117180c03070e0703050f101802070209070306060210060e0a0b01140d09110a120b0a0b1908 71
    0x40c004911a9040800403402640c0c0302e400e4404440e41110045541c00c2210158000c000c4410b44516495007000c4010442c00c1242d80100303001c1000510740e042841d03a80000787c0407520385024070046000b10000c0700c00070403680c0d0020180212003460b020f0020303036a590740030700320f9100c4580307207510360440300340414940761400c3e00301c008020a0900b01c2c2070141d005280c40324004006c01c2200d01c080d861600e807200070010400c5c000c442d40b0203000c03519025120400d5520038507080341c0c0c20001030700380300000c3c03200c8000c2d50307401e4051150405806105c03030516010708103880c40c401000818a509001c2035026999014015004014545001130001c0c24000024141240c070b9003091107150501d881004100c0c058440d040e40101c0100000440500c80d6004a88020030201d04540288000c55162481141a8003000c8070314450800301c103c911908061202c22520351184034044c0b81e85100c8480440c1c0c2a8a8061717001c0d110140000e0074840c2ca9000480040007071480c042c1104501ca0f0601c6003071420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81782177 1250 81780927 81780929
    0x3050108060a0606120906110406120c020705031e0a06090609051c09061d0301050f10051e0927010c030e01050907120c0803040e0601021603020303180609030f010b0a 73
    0x10002c01d22000d41441c2d4080c1c0b4040b06000030074043d6a13188800e9003840280e61000e0550355199608540d55507481d08000d00194048100d400c80520380074980301d0507030002612004549028000e0b10982c403130341000c0758003c0c110382c141c2c40750b5000e01c10081c4c0000c0c1c018850545aa4800d500007c0d101001b03082440c03074072500c602000c11140c040b0210008003600446180201c807105d24004004a08194103140c0045031210010703019030034841400403441206c1e010900c00c0940c800d11444a5a0f6207007003082880361a01504844000286505507604000500c03540c8084461090a04030031240c02d1501c01a204031405c030744903591141c8507500d00703915002c0c00b4a8180404000d1206042c040ba8079030303c4600e42d11a01843c816500324242c10002d09116642c010b00510b01660380300c6550b41081002c40c0000c0300d4160044c00b074000c4003085403103035041800949130081e0056082000d1a00c6181682c074a103c2040c0c1e0118082c891900d2540d0100054603281c00300c1c10000c1244034807032003032101328265 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81783427 1250 81782177 81782191
    0x180a0609061425020723030607020606010c03052206030204090606050f0406030e0f03070b0403090816050f040e030313060501050a060f0315170a02090c0a080606090307080a030305010806 82
    0x8404107002c04114020b080c1d407184030303409000d0442d0b103180d000164a085001c0d40480c081c80700901b9415100340400034442c9652105400340c0e0710f103540e00e60040340c890704125209408510400390034000309103d00040e140315240d80305001c105440050f0044404601039100342c0000750000703801e1100b4041c0b030040d080144085d00700769080860b02c501031589130144e0300074101019070b18280480c13000d808005082008440b003056903556442170504034800041201d058000c206107020001d540030300081d40f00000401940c4070001c00b4105010000c1c40b00d20340818540c001d444070305014400704148000d42c020306c02d2485e4012403032102c0c40c10f03409a80b0b0591202e4442c1c00102010007030780c1e4104c218806a0a20f5180c000780c080d60f0104000a010003d40202a006205001065109100180441140d0700843d0a08a20303551890b02c40d036241305941d0000001343c0c1600107d082400c00002504802c0c6004041da101e6a072128103103840c082c510340050300003035110401002040001d00a05410100b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81784677 1250 81783427 81783461
    0x110102010e0307020d020a05120307020a0b18150c070b0d050a0204081c031508010f0506060c0d051e0a0203130f030305070f02030a060e030a0801120c03020108180a060906 75
    0x58070180d5449000d2000c0190080040200100856440c4a004800360600411056a55549036041070b40c3e42c01244c000c90140d4245800401c4071201081502c81c1c0c0d81082407015100300011091011188903800c400007041803d00c85148070b10814498040980203010055490b19000d840000540c1c001a00c50020984108001c0c00744400c04907e940305404a0300e1b00e0009200d00e501c0840082449281805004c0f05411000c40c0d51401900715448074402040184602c0d01c9140c10000c441c45201e41f020416448141c03040c000c180550044e04052650403514020390090302000ca06652201c04c246005820000345407050340102c280d000d01030001b2035000c144960441d58013a0285c400c3e0075018200404070b00c80c410841da0104880152a680101c042c8900021914119501e0700010120004506014004035440ca4143c81554405d5046144150032078034503001514110b4001e444a87d4100c10003a0f070307040300f0300d0070031000003040d104502c0000d4405080c00d0500450b510801e040c1283c82d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81785927 1250 81784677 81784691
    0x21602091b1b0c030d0309020324280f05010e0714040506092403010609210b06030f121c140117010b0405040605090106080303010e16031e0911010201 66
    0x7030010165030a03061020645503520031880c1c9424944111100000c1e45031007468100000140d058210036005442901116810219004144074030f48402041018443c40103000403048800100407807840d0b104e89948585071041040041e080c0c3c2c1202e20420112600c81e001008a03540e03c042c095070146c502e180443c40d13441c001c0413040203032095204084c4540000304035004199078205c8640220f140341d01c1500101c3e017040c402d443c25600248114000706d070742243c00146405580c0c0104030b6010b40900c03100000c41203a503d4142050b005400180c05204d480081c4500b5001041303078031818840111410f4845214505201007400a0b0540800660034141e000c0c04d00d070680c80703559056450850b0503880c410300b070391001070040c041e120400c0e034043c3c1854180b00070b100b40750748810b002e0400c0e40001d100543c0c8841c1c902e640d902c82072040c4881412800c00141c04000e16480510082d801c1d840c01141600e40c42181000d0040340403d40c14902d81d070303500500708014014803800d40b0184203000134031642c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81787177 1250 81785927 81785971
    0xb091c0c08030a090201050c16080705060901023705010b03010b010f0206060d02010201110a0806040b06040305330403020318011d04021e07030f08010906030b04080c0a0602160209 79
    0x50b00016103031901898450002d0030840e80208103482c00e0300d0190088031084286480320301d0b442115489850418000e00c000420141410300480f070200308182c004040f4890411220360541e40310a07402024040300348002c021045020721100401c41c0510000703e50010108101401c45840e00b860034140043d5503a400080c40d0042041c03a40007408480048504e82035000507809440d21891740e106c218800100b441550b40c02c0b4101d41c0c05150190b400300892543c000502c00c05100e117000240540d481142403800c0000304240c0743c0051041c080314108083d000e03400c42424402d05940c1200560008514114038405581203148080750902e80311390441492000f041100042d0140075014076000111034086011000140c8014200990034a9440450f401c00601d014100402100002c0d901c03000011100c00f00d0190000b40d940118154040340c035140d1f500180c9501000d001481c41c0074100b40031307010030918805080d11b0040d210056030a090544100000400c00504600080d03110f50342c40b07071b18 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81788427 1250 81787177 81787193
    0x110c060c03130b0403120f0c08060303040812070618060b01260a0e01060509090307030f03060b090609010210050a02031806160e15040f0f05040504022404030b091c0c 73
    0x210360f410510f00890340e115824102caa03815001c0c0403112403424003000c1d0001c1c0b00340c0c0d841009008155914801d01d41c443c8010591288990712a1504030307444104400003880400001382040d501c01c0c440050b00325141802c80d2020004081f003550704a81d901428034440d60020490207008002000240c06005201075602102c08050215481c15990724580b54010809502c00d50251400034100001031408840d01c542c0c0358000c1d03104078002440385400101050090007103e003910b03a490923007804c083c40001030060742d1304600440d50443c4140c0c882c500f4911714610a207405440164005603480c5003000103150a0903908103505010750041c0204250001d80e04004d8414429901c1e0890190043c100064015a05882c9651203000002400030321308110038480030131a585a0740344103440b83d990080100316041103602079080b54220084038610740e1b1100380f5030180d042903442e150801c3d0302c07900c1d0314200000854a0f01e01da9440603440700c500d8004a084111506050b01d0017034018a000e5031501c1d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81789677 1250 81788427 81788461
    0x40e1302090a110903030c0609010e2b051c0509010c0c02030a0f0501060b040e090601050d02030c090a021611031c1202030c1204030201140c0a02030a0e04020904110c060c03 76
    0x582a42da40f00746010401500200d07030352540c3c01800c80c0d8540ca40c4e07152094035007030305039281c444940c649580290213407008620142c024800d040042002500d10803150402d41d0049280b070100201000156000c003100f03224092162a01e20000915107003072400282111800340760030081c0591001a0070050f0382c00141e00341101c1d803103070314200c4e64407031442c21170b0140507143c01c2582e55400c0403901140444904007814400d6030034504882190740d958061003036104030084e000c0c1d015000318590a0460504640c2250001c88503a0b005227400c3c801c0c04403034a24140300d40102c47c48120b4428140d054603040284460054143c288510b44080c140009040180307802140488550040300040604003600c050710a40e40d400c074000001840e1130b107030003402440c010760b0001e00c01c440742c1c0114048040f41026182da40485400039458880800c10a03128200308105040d4096020440707240030351528001c400300d156112403d03076103910303450249c40d051040003061190890824400c100c803181e40158400303 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81790927 1250 81789677 81789691
    0x80f030a0c02040207050303240a0b0f07020d050d180b03010602031e070f030e1824041506180801020702011b02040f090b150d020a06030e0a0606060302040e130209 72
    0xd074407100a1020501034021003001822600001c0200200304513152140007103122220f151007a01450701042003d041054011000daa400c05d114044441c645c150052010a00042000d0710a03211540d40c2c07440c000074101d8000014803642c8030084801900d000784009485214003150556050540083d0349002d2031b4410010f43ca001c0702c0c00540a40030b50201d60495410036038032070040016080182501d54003d000741c1c01140345101600071014698181030054800c80c581d282c849612417226150201120282c50f4010780e96180c20400d079004503040c100601c20350312203100300e0801d131000601c07030605684000c640341d0041005000503170b40030700341180c5c0500c00f42100d5041205400403900925031a4281e8040902d000000d0040c088814000e5101d4044c03602224044580c90051068640040c41d0082d001800801e041c0822030198100c0030041140d6012100300d115184c035260103484036640441c1c04654001230070300840b8071352840158000c80e01e0340c0d500d98100d0943d01142c2d031a94010a02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81792177 1250 81790927 81790937
    0x6180c09080a0b130804081f1b11010e031602030d020d0e04020f1c151d0c0a0302121302040c080103030225080f01050105040b010c050a03032313030801080f030a 71
    0x44c2500401504035500319000035589071540c0c1c844005940e00d10300701d100c45040c050072814040118449005d01003030761003052410306400c000d40a05461a0381c8044139030b881552211400c010440c0c0800c05005540b14090030000720030a6030046c9428510008414401c54228004515074503800505610f0000c40035203005980d03802e1551308100c94020703500a80840d8210b0070031500c4240480d000700c07000000d004004d18120380d0351403e100f01c0c4480712295000405200001031019203418011b00003050503824054a031442560809050b001c00712440520103004008c00001c2d81031a1045a038005102c1c03e0181307484d4110b40b8060f558155103402841c0f2244802085c0318a61040d08007500244180022242c00c030248002140c068502405924011844d02081e584198490005202455000800f401212682d5103045000d40054000c105c0c072464604010109074a00820711441103660040104d004805450f00410541c0180d003d070b030450303102207000000340e0340100031500101e00508003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81793427 1250 81792177 81792181
    0x2071e03080c031f030b040212030405131805070e0114060a0e060a090e01090c02060604020901090b0d0603020618010e0f0a090e120c1608070b030f06120106180c09080a0b 75
    0x712005048501140c142c00090320300005c10005420760b0103001314402c0700c04840801121202541e24004c81c8280c56000145d090311014001281d480a103901e0184880310120884548030345241045a0340f11052800252004010601d06840b42d441c0000003110300a142c0b21140c034004040c0e28081a100d849048001401e005c101c2c014032a8000400c07102a10648a40c4c0da04104001082500310b40c1c0c001d40290310000e42645814400c850201c407050310b07820a6241002c90280f00c940000354004c513540d03610b5101002580e5100060510102c0141001412a00704800105100e55080d43e040c041d42104501e01040d0ba00d24508800340c0c0c1b9030610009096001070120b901d84400c0d2a0b40305d810b00d000040200390b4a0700071031458042c031503003100440c3e00caa03680070340c0c3da030340351a8850307c1c44196041c008148000744242002d03400100040550032500c0c003010070b00d803c40d645076008000070381d42e00350b51451520942c040c80e8084038807401e00591092034448015220101510010864503030980 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81794677 1250 81793427 81793441
    0xb0a020c1c02031005100611060a090c0902030c09040b010203072102010603061109011403010812032d091009080f03040503160606180e0c1e060d02071e03080c03 71
    0x445407552503002011900703454080300c1290004c00b019110b800d0203055429000c2465401003207451844c0c03402000428117603903540c9064000300380481c0c0450f4590400300d80000d1000d043c0c0003039030180d000c4208690341c0d004080700700011981c6120005056410a0102c0c60204031000924035a51000143c81106d403d03443c10300328010100d6030402800d840c50542c040024004120250001401c203886071400c0c1409240308078006d0000348202240d540c014980307040e000d803401c00a150004098002082070b003201e511403850038141c0c542038221801b590000c1000c120030402007220041c80800c0c08000c6e00c0c015488000080c030540c0d01006010000101050030003900b0400c40782d81d80714242c0060700906152505401820092098200b00700300190390554150884c464410104040001000c4c096800d009000d8800e000b1400c40c4241030b00000080490740ba000c005101d0100030320302c01a07440c4003528000440c901c0622507140c9191500c00b443e000a500488015000669503000d16141d980c2e640d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81795927 1250 81794677 81794719
    0x50609060a1119110111030901150305060c0a0207050d0819082e090921020c0a0311010c06020c010c0210090804051e060a08010806061e010f050c030301120201090b0a020c 75
    0x88200c4e20303198030b424489900020300b040070314000d00241c0c0091003605541e680c150343c1104c41b40000341c01c540001e004101c0c103680c03c0004100004e600c0c016a2111551440045c24201c113002c0d0684401c00c1c009046001d6102030308003007a844065041031462418000c0e403000e03000141c0c0021581d000d4400d9400d2004220780e00128005040402c41400700c00c2940c980f4502c0b400c40d4159010040f001d2074040381c1401e00214111142910103001e41049a1442e10360265000740c00940310b0500c2201d6140b0004140540010f03c0c081c0301c3c10001003101214050001d10b00384080089440051a0844c0480020b01c1041100e044035012140d04509140802d0810b40704401e60f460507600c03000010745e041d451134100750201d04903400e0320305840c1c2a9071000c062021003000c0620103120a010b03a405481c3c10f42c05000e803d515403015280c82030614820000d583e14580c03081c0c024400d40840b20030707148210740e031000c004000303851f90362031480c1000c0c0148000b070f6840e845801900d108400585020048003501 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81797177 1250 81795927 81795947
    0xc0201110c0a031b11040b010509120c0312070b0109050603030c0d02010b1305040c051c1e02030c01020708060105010309021c0609110402090105041806030c03050609060a1119 77
    0x601590707205818980c980e41c0e801901021004034000d00000180a140000c050300b400b908180c1c0e0142141e0b0388801c0000408144c0f0355241070140500000031240c0b0b503403040f05487c1102c41c00801e00500f00100701844d00b641095600060103040100740c001401c40c19400e41119401007000c6120703210040040e007140104085070003c3c1c170840b41c0c04584d9507030541001e0350042c016034100040d00a08040c0e00b0944100b01c0d40508141100c490400c414142003260380a104041050a03c203c507c0d0b0b56079400080c685a41012a00c5150750303035205518051011102d580d000f40010400c06150842154560105214103070505030f0b00e800c2c40041d921010b00c01080c0000c0006909900744107454032400402031400301f5035075081440e520004505151003101e400e1401611110709140c64560134203e8210b01400d40c070b10041d120b040000c0054404800c49000d944950090400d51620a00e158504003008100d104076900b0140c140790b5040c48401114103d2011266607402c4008250080d9142c40d24 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81798427 1250 81797177 81797201
    0x90a030b0f0114010503010303020a0f060209120f01050708061e01090510050a0206010501180b130803210a0612030509121b010905030c0a06080a06080109060b040c02010903020c040c0201 82
    0xc003a040140e011640d841040c141c9848003202c484420300a0011103190000740001005a4070500c808400300d0602c3d10440191841080f026141a26200100f980d4000c1c0c00a10710141d0b00ca1000c40703101c2d0000303000b05540071a0a00e03001e2124070385007000588684403480714032108102106103061507489607644002800c03000c5d01d00d410348080030500428651100c14004014080d180003c201036206200303d101310041a0000c00a860400c4880c0c042a03002c40c0503440c442442180c0021786030b009101600e04992030300c079118940010544000d204000040480074401e1801c0030600000402e405814000c1b5018a022511928544003007140128071090b40c4009109240c40f0700746556151405510401080e6540700e4026910018196903c7d42c41d040c40350b001c08401424400c192146012a42c40201e1020124a035075446500c28211418100207480d19a25115111302c00e05144c0250001015144000c0010a13003607240207440701d001d19007852103a911000e001d040c0034400d400c41c20080e01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81799677 1250 81798427 81798443
    0x30603170301030b1b03150307120605040c090e0d03020a0c0b01080c030d0201020c1c0207120605070e0d0201170a02041e0303031118040207060e0624060405060f090a03 74
    0x15404a2010305500240320858058100d080010600c044442d00740c24414074981030b040c10740e1103540c00c00ca846420b082c0701c90b0705031065100000e04040d02c6011b0860181c0140000189814281006804c498141e08401801c9081ca2025081d050000070301d80d401e20040c0c5001a1a4078000d8000c0303d1041c0582009420055a03200100c1c01030804203c914051100300c00f1205865907580081c0d090303001c1d07010b140c03c0d1070b04003081e00c0f02007440d060070440c0207280c0ca105460b00581c40d814411041c8891072026142c5a94400810152540001e000304881e14221070b4900324540590000300782424403041c0c04450108a00491259101a01640c014081e0800c00c440c03c0355010104447c404818842500002d09041c3c040d0344036040303041103606441c0308007030160090002406101c0658005641240c2c000d6a980c03141008020600240307000c0c0042d05100c0c15503215124590303a0904240300c5c91b41c0310716002c100400c0f00c0e0f82d8903012030b400820320054068541c0303d080e0000701200c0441e0300241401c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81800927 1250 81799677 81799703
    0x509040204180b0a180c0e1008100b01020601170a170c070308070516210512040902031e330d0b0403032007260a0c021e060316030603 59
    0x320f40d50151030b10540c003503841001580b0600d40303402ca02c0324070308a0142207480d00203001c2c00f01048030304019501c240c414100041542c4e959020303901d4001c010690b110303400c0d612850040e1540e07040c002c00c0e0050003500c5002080c240392500d00d0f900c80c03002d40070003007048490642c108070013200350064900003240340094982c0d0b0356a03030504200660181004803114019041c0040030141200341d034a0603a6200081609031443c0f51030700980015041c03005030342a00ca6080300c04500440c080080028212141c0090b8880c1809001013003079a808410790000c022703403d010842c0d050400d03490344841c021006112403d030f003d00308841074440c0c494008c440e00803d0410028080c0400b07000c416004510039070781006007107805449013500c88d440c11401d1111034010007440300804c0c2c1034030148204200c65000c0380100c424041d210f44055100740291170205208402d0b000645c80c0a2010b5200c0114920f00d4a41d10049840010902e1000900c440c4001d03c0060401c00002d1185c1c0c80340000d5580a07004442c08 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81802177 1250 81800927 81800933
    0x6080304060f0801050d170f0904020706061403010e100903090302060a05030414030a09050d02030f01140106030c08090729040303030204030c0b0903100203180a120f020d09050904020418 82
    0x2841894120003190f08000000b400d070918441800744241c100003008495422441400f00039800520b40d01d42804062150201d07540e00c1d4401001c03076500c40c0d0000207006240660035504241040390383d030701c642d00d000440b083da650042020600c1e41401600003400b02d8041c90144c03200100390300081e400160209003244c1703140d0842c0055010b24012442e0501134542e03003110596074824220360b4000960001020001410f000000700103030fa200405584800400c0c0c1e841d40d0031580800c40920b02c41d160040104041a0117106080407400e0518007070032149040704120b6520041403144e0b2081e075040e90385e000d1011103020ba1420301e1411340e0114560703890303480c100100070350843c1c0001e031003805524034002361071030000e021a00c0c183c001601a021540c071015042009400003001e10364122854140d89100140c01d0000a00c007510411041c2d814030038000000700f902105900c16801e55020541e501c008940201e28a8202ca8088034104c103180e48500c0410082e08130707240d0340c0441009501500c020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81803427 1250 81802177 81802187
    0x6040b0c070804080c0306091207080307030603060f06060f0e0f09040c030507080f070e010305100902030c130e010c08010503070b03091e010c020606040204050109031b030b0f0901060e010501120f0608030406 91
    0x905c5204508680980d116481d1980e182c0a400c0410114610108001400160184040d5900c030850782800140c099694813080c05032222140c05450581e524403040c041990800c040342c250309210310b0507070108101d074404503000014004640d4400d00003400010108440034548401840d40a419540c0b00343d03440600e181d135012014401261401252804201c468112015a040fa07411100900040d1588c40c0803e004081c9200245e8160142000c19070558951038111600f0f01001c1c0400101c50704100c00c80f03800c44581080c1c0c5000c1203101401007220f80d40004000007610081444150b498035515569440c21502142c214400426a41509690382041d0b005103803500c142d40a0342c540c5c0da01c51041100f2880b89019980c0460300074101840480d400d9420b6078401044d00103541d03c03140c2ca92705d40c2d41c410383c001c403003503519441a2010008410000c2c0661b800611031001c18000a50501c8000b808441414201c04109542c800d81c0009005c01a00028001c1800c034050301d981315144da800410b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81804677 1250 81803427 81803443
    0x9030506090105040b0609060a0b0301120312090201020d1101020c0d0909050906060307150302071b05031002070b0601030c03090c0906080708060c182e08070f0206040b0c07080408 79
    0x151401000c000515066042c090140b040780d001502000035a14001080700b0601c0c0a4072146e0040384640c1c003c030300b90100a0080d800b0708284615040c002d155840c00910409d1100300003101141020380c0840180d0700001c44c28590121800d145d1020300001e90064020700a00c1c242c0d034024444e603140710700c001c0d8200041c903050300d2000f442800f040d5503c11086940b001d0965142c0d400d94840c0c4401c021010411400074415900d502d0003501d00701050325101c080c02ca1450000e0400120380d0410401c615040085600d0600440819814620103841d100941440108420305040c2c54032000c8104900c294841c019441d4031652038058643c0724410038004043d180600c000c0f0344a1310030046181640001d5043c0b1078019071001c9031a1070301e210040c0e008101c20104041e0894040310b10360f80c030080c1520144c1c5940c43c2145c20602c0101004100505094018050905000464410a442d00d6020406d181e000b50840901c00e4031743c5a144095040d071203140700180c130218010074003084680020500032 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81805927 1250 81804677 81804683
    0x30c020111011b08101a030a0e0d0e0d14010f0b090105011d1005040b03130c0b0f090d021c060b04060512060f060105091c0308010f0f0608040602190903 67
    0x81d161100504035600b00c903440f201ca2041409980f038822440c52080511a50090b00c0b40f151042c143d0381d610403081c81c2c4074000f141c1e4410000205c00c00c41c5280080c0325a0898460b46002043c00b41c4120310041c2c040c450305201d660295503134040382014440021241314001024000030040301080c0102c1000815464800c24407943c644030000440350b1140d0031020380301c0c005000400c00310341c01808000550a00305500da00380802071000040d41c45000740034512420800080400c02c001515229800003526000103604100038070000341ca5480200a8520710702059501420b9030610340006103e0b401c000900301c1d08017810712511800c010054100c010b1026064506000d2142c0300e2081040e00041790040c20320942c4140d000882c44400140595041036040c1807803460100d0400101d90b02c00644030740b00070201c07031042e4000201980315205600414a000b200d0429a0504022003a070425a105003402c2244520200741400700700d60495200d00c80c20181f20415800c1c0110243c1a11118481030b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81807177 1250 81805927 81805937
    0x140a03030b030309030312060a030209130c150807050a11030301090902031509060c070c0e1003050c01230a1b05150702010b0303030609180a050f010e03040515160b04030c0201 77
    0x8000346040020a0315458000140518140347d003200c0d40e80c603101801071500c4da004824010000c09038441410b030700d01490b1011041180d151250512005046032544030100240e0b081c3d613100f01043d4003e24850300490949000e5540b194070720400c0300c1401502d24010028000000001003844a45d405514254800d400340c130301001ca40005e8183d81581107030718103050303000a00005c405507090001008000e00c40c1c4200d0140c1501c44020307a002190450b000e00c10009505c2052041c00020881d00d4110301092030019008021551904000403a59003200c0c0d0454003c00c40032100d82c060344502d1005501d18054003031450303590030300c685d50300c00c2c030703151824140082c20224071400c0c0f060007440302d800405801140780d43c945009000621000401c2803280405803114a120b0f0303d010302c2884100703030258005218221402c51624211403100c82207800c10390041100b04820b4851122450500c00c8444040341c5500c01c040070b41c40104450f41004010161200802040580102c402c1c614a8002ea0711 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81808427 1250 81807177 81807191
    0x6060603021903061805061503011e090510060f091802040905061507080702040608011a010905030d1d01030221040501110708071101020313080c030c1f03110403140a0303 75
    0x810b0f0212070381c40c01030322004c00b4540f00720920a105ca030030960300141c001d8807980044801040382071702a0400e800072000c0a18504115003141070710302117003002c1c00441104000f03030700700320708003d0f11102103108000c00d1001400c040c88150f801051454000d200810307c109030300c0800c049000080d841070040000152806010900b00d040c2004ca00b0714081d0700985c0680391520549402c411030b00040022a03109440381c00126020501380550180e0415100b4690502c140d080300243c0504002c7c1c112902039807141d01800803560748510044140d10303100030100200120302004802a01c210400001e030464158951101001c107581014032950198000b04201892010703a036010748034185c0007418540081c002c1c040408c0710252480a02d0070305004803444c00003c5030100e2802840c9070b218610707a8022010b1341c1c40d035040034460040400340840d80b03401ca018400c0001c00001291403032036404c0503920000d444440698408139070240d03403c40d0380103c0f0015501350030b6a40d030403080c0c1d084000a0401003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81809677 1250 81808427 81808477
    0x8010509060415020409061e090209010f031802060f0703031401030201120209030a02280b0c07060c08120a050702010b010201060e01060c1e03021507090302030c1c0606060302 77
    0x42854000c0003100301a1125031203540f1100070769415001041c144603820000001d160303185108400041a0113a05c0303081104421096414040c581e502841d00b02e40104110b40140e030388007519000c03075400f0b42030000d40030320344030138001034031012240082d003194000810741401e058031406051405c1c481e580030b11048203821400c001f000e00030320000740403940c00c00036403080300e400d0340260040041c080c0403100c52403030517000584c9200c80a100703501c4460540c0103904400c0400c0500801030070260704024900606402c11a41d521032a209900c01c121030b1281c11400c000d035520448229070400003841c0c9042c240704050301d00070309041d0382d9080950310b040e200d2106c42d4010701410b0201c0e0416000b156a581c600f800a9944405c99101250343e40700d40803800c0d03114000352200c41000c038000d9009000e955060000100103200240041060000130402000140d0380056484408070081d1110b950034034942558142015014500400c02401e1040103c0c800f0341c150b01600c41050441c41e0900325060b0301c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81810927 1250 81809677 81809681
    0x5031909060509010822060204090b0406050d0803061302030f06010e0f0108040b0601020106170c01020c0118050d030c050a060e0d0507150b0102030403020a0e0703050a020405060304110a080106030510060801 91
    0xc800c0c1c401180c4240301e142210360145940d01d0303000e01c0694006d40726039640034030107032116001c8404a03902540840d0a000052261182521112050307408002150074440060150070004400404648000000030155152440a0300120f041c010040d500c0c3c1c24051138103041c1c1c40007184c02d00d0005019114104192030100d00407440103a040e103d01084d52503903124911102c000a04171410766485a0b000900c0344c00c50326090940398120f5016000c00c4108000080c280380c2c031000194104a0034103031000f145004141c1000c2102d03000c81e5009199042841c085e902a0a008005030582c0101c107007020501600d0380082107201222003c2d100c020082502c15500c81c018500d01829642280b0b000d00307184461a40702d40100103050040328103166995002810515194001d8072800180c0307c207008031641c0500615030008016201941040d0620000c2089404003d1015000203c10038102405846111f4020b01910400c0000d01c0002e8072424a00e90f10070400074039164151416000041412043c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81812177 1250 81810927 81810929
    0xb06040204030809010f030612030201091406010b040902090114040e07030608011e0917031f060519230a05040512060402030d050d02120a061403010510060c110a0305031909 76
    0x2c22103c6007050842001151013001031410441815a2114080b580c0d40d12124440c3c100c92180c4d002255140c0c170b074034161007020071003c42400b880c0d0080d40184920001c00301a94184c8076500e80068540c1420001215641003010342c3c21101c890008d0b02058034900407800e2442084140c41c02e22042d40c4e1041d8441c03c9a10101c44501040c01a0418645000040d0040349050f8055003150515401c1500c2c00541ca90054488000458140f40711407419445144080001c5c4640d081140c2003411103440304609209811010081118086030341c400c05a04031074002c40c1c01c5e08045001c3c4c6034521030101034015405070040754461850322150950b0f00c400000c1c140d00ca01c0d07028014000b26000c0100c1900d05801c0251a41d18064090004107450380c0c243c50002d2040d64000710100700145850f245148800e001c10031903020740d04000402180f00a9a40c1e0309086075000d1804043d40b40e264109622800b481c0a00158050038400000060140c000003510709007000100c07800910350354000603110b60070a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81813427 1250 81812177 81812183
    0x20619020d382808010513020102150415020a05070c0e070e150d020313060c1d01030516050c070b07080405010801080a0b0103081c05100f060207060c060911100c0b0604020403 77
    0x1041590f200710300000980075081540030007000a94584039514030382075410480e28041500c480180407401d640c3d040100f0b902c1e811035400317421050304068589084400702c0800d05000e01da000902000d03907034818011501d8040c0c04c42d114551150b02d54480b03480e403203400d991a0000420b88144040145400980c890145038445107183c5002543d440180181d00010000c1c494100d500d44064082100d5000307030b4020f5840f40d5a41c80441c0c911003020500d040c2d40344042130415240000300248032540704e412083c005000d0400c01e0300d0b07200d00141c05250040340d030024242c0700da02240e6401003010740c01c050400d81d04262a8582030360f0302d5451540d030794100581c02428035482d820042000c90315040c001c0c8034500744040840d190300c8a07041600241d44003641c2036601504101c4040102e44101e6207400003501d403500c050840146488801031078080700d101c0140103103613194020740030407144248003e00701c400580360210043e0b11600203010401c0e880d40640702184a1000034444d85418030849041c1c0364 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81814677 1250 81813427 81813439
    0x3040501051c09210306060c050613022d030105061507150612050c01020615030a0209060301020c060c03040507080106050d0f11040f0e0709060303020619020d38 71
    0x1000d074040c42d511480001251401e540d5070450207011500c07403038a4100030b01100b551180107440201c00141141c20950054013001711a400000010344045819500480c2500900721841c2036400001c2207100d90b41c2e4034403500000d076414181d90301a06420390400d1141100200801d070399110a00c449565640d001d0b00c0c1c001010001e03600020421141d070400701e011258000341c041d0321041540c109014129094519901000c00461550b0f410014243e00c400e952074081c1400a0010201741d5480c605d01000b44a030400f600010603c0d242541541c401f00e4180080303d41900742504002901d900c00e54040d5058098101c0215180c0414068801120000f921900d0075100710388903105c40c602000310844400029040f1454a9074460181121011890301b001907082d034001e660741d18100311a0f1003404c0c06414100c08001007031b0041001c1d070340090f1401d242c0c414000c210703246000a20440030b40c80c0d03140d4686100e503103ca0b4040310786000b0a042c1c1b03207540c0200c05264406000c42e00900036040c0d038045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81815927 1250 81814677 81814687
    0x1050912190201060803210604090203030f09010c0204091101020609030a02030f180306090c04240e0702030c060f01030b0a151512050f16050c060601052104060f0605030304050105 79
    0x206400c01140501c120a20000900c6a00c4004c000d04503030040c0c2804014140c0f01d20140741010684029980020044400b00101450340c0c0c0071035284e00514111603007101001ca00090740c3c4e4004d90075040300c1d80d8020b00c00c200cd42d20910b414014402d8598025005105520006091410000840701103952540096044c61204840501c6940c41a600704a01850741e030004045a00c0420905001d420403038050490b10250340300f8402115251042581450b8007d20f120614052102d07108040d2030264195054940e1110341c103078554840c510801c4000e1240e2010420343c0c4281c5d002c6681603d02c18020751140b510b0b600e0f000000c0c0c07200f282011004c00c034820703c02c112101d000c8080790344104c0305040c4030114429044411040710021141c200c505d6102008011a0380c840c884800040d412030308141d810000c81d1003102d552400010481414028009143ea4051280100358132003080b07111803000540c50030b403a088010b86045040f0011003414508081141d01d0084103a070240d64060f03445038201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81817177 1250 81815927 81815947
    0x7050105010f0b25080d0504050606090703060b0306090a0e060906040303050a061d0601111002070507060305040b071d040c050901170105011b080904060f030c09090201051902070509090f01050912 86
    0xa2240d4130300c03c0710080f104012000007151507000d0341d4490307170090f00540101c0c43d10400340a40034400605280815180140c10301c5040c5001d42503c1d00400c007074810341c0c0256241c006120041001c07002218180c41800104560304500260880c0310f075110741d9082c01681c407148d101800707664041c043c60312410802404207458040842c55144d01c0181403401505500304070a00b581042d00d4640ca070510340b84c000542d4000d20204100800080c42c0a20302000b40c1c1c601170f2244448820003070322610420040e0003001d11021391000307240d041c01c0401402040300202601e8050155800109854003003640380401908849010740d000e4122441178480d489560042d005074511808a10f00c2114222414801403800d03071918400c0e0005402400985030800d4254100110305800681c031150085041c0883e120050340d020b810749451428203082001303406040902070b03083c10b003160401500482c9842c2080210f01c4002607418034403070f4240c001c2000780c8649048680f10380030107a201d18111410040380f054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81818427 1250 81817177 81817237
    0x1201030206091503130b0f011a0f09030d080109152102120a0f14061003030309050c19050f03010b060a0e010908070602030703111b040b0105070807050105010f0b 71
    0x1204038000d183c0c8070301c281c1024050000b500180d03014004d9002c01d0451101300003a42da2080e4100d41491070903101585454070082d1104402c00c0c0742030818401081d801c0203a403000054545110004007540c0c1102000c481c018040e0009115001040d8209604070b050049450524420394030603041c0d103890901c8d090000c1c0c80300490020102e07000420181c0a03010420b090041c1c0c52094070035242e40f10818424100a10f14030701100ca544075681060f4217000c64108010301003000c03a42c0c1400c012480c210305060042c02c114182944d260080b140265408501c1c098107414000d46408603030481540c0014000d05003200e440e00c0c12150000e0040040d030040500450280c0c1840304145032500b15181c84125190811005900c2240540e1010501108060b0848500c4900a03643c1d4018001c08040c100e8141866884400b100c0c0103075034443c00790f4005d911400890b0451074010322071075640e4a80d0310f8070714000c100c2440f0340615070213958008030701045180e044521a0750001d420041a11005c041000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81819677 1250 81818427 81818437
    0x2030616051309050423060f04030903200a09020f0d1a1f120b010c03030903030b060c070f0501050f040e100e1302010e030d20010617030a141201030206 67
    0x6122082c4240305610188101000252403440f0f03002c5000e0034145442d0f4855003106607500749500501203080007281000034441da014040320f10b4074203103840301e04082d12244032503080500321460a61104220350700c00070018400e80e800360b078429421982c0701580800c90003011b401201441c002c102111801c80260880c0f2103501108094000b0b00d65642e00160207807005904000031b5000103100050b001e03810481030901c280d0303450400d012100d031160008042030719102004050640d0750800c07206041c401c1d405403400c10b90141c911551524a603480030349d0b49803248920503000150042c04181b9501c18400d0f01c00700040c2c000c0082c1001d00700342c20044901c500500910b10514040000240c0740101083c4074010515120403e606107418000100016103520742c9034082e501407040c4070001390b400904e440c20344010b05400d450410007a032085001d84070692101c0c00d411858905802c0d540c0001c001070a4103000303038072650fa02081b0f101c440d45241c040c07400301c07400b0010004010009400c0620040c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 81820927 1250 81819677 81819721
    0x71e03020702040b0a18180807060e0f060709080f030406020c2404030303020903010b0f011b02190902030106110a02031002160212030306030c03030702060d0b2d0906010c020306 78
    0x81161303401000450b030441c007198040e0041c08800503104984c0d81c1a8400c209615016141d0f1b041907007410b44032140103106285000303143d507070f0b200560078030f000050055040004540f410b4031203d0410300802482e4800038001c107199070040094400c2a03110010480b0b0440d055a0054034401e1101d40400c61b0540184401c07110010128131014400400b01d80100040c6100e42c034010384400448060508680a2455407400754000d800c009146a030400500b00b0200d42c0d60071403400b112401d01c0130078a04a40460961008110880041120001900554184d078010b903101600480314450781d50f03640b070401d10003a4060708804080078805000d0340081040b2100381701aa00350200b1940403071503044010700031010541000c02071064610381400340790052001203001358180500340d000990315204075a00c242031241d44122102e0305483d5442c180c01400b10f0044c0e04010080f10404000c40b4004421465200e05061000601558081c1c1f404039010342d0050003d1580e0b0303640d208061481307041416a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 81822177 1250 81820927 81820931
    0xc0f0c0b212a1309021b0a0302121b010f09020f03060c07170421030e0a0303080c0901020f06040b0106020d0c1208060a0f060203040509070507080f16060e0f06071e0302070204 77
    0xc2a03650420f4020380b0052904080059680004145186242d07040c444140fa81d074004020405c0440e50000e41030031142c200ca0310540c4d40d282101d500ca051154081c00801d1254289840091416256400f0800050007074a481d0b003181d8204c001c043e1980c60840360180310050900519002c1a21034000c00f03048000c0d4410b07140b4103615040500500e0381c12020032055481e03504254000c1503440034000c1484001582c4514101d819a9800f800042004140040b0107102043c0e0240b0fa038402c00201562800c00b03000c5c0c0304182894205402c40c410709000c0c1d00058442d0052044045100c0c03010071003901c1c2c008106e00d820b0307405000101d906840141607103620807407405020503032a0040101c50000c0c0002d8000f103a5462404041c404c0c41000200440c2c184031051103024041075620084039044101b242c5c0d0a55500e016002040c1c80215040000c0c0c2040c0c50f00070311850518001540d140c102080804507030a0707030344d1072008403401841d05002c001e0140c8181c8035801214005c0e000740011a100802c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 81823427 1250 81822177 81822187
    0x80a1e021801080c0a06020303010f0504020d020d060e0a05070507080a030b0102070b0309030403050609060405151b040923072f0a0605011a0703050403030c0f0c0b212a 74
    0x110101d026080e08400c00c00c2e041190008124640380c0c02c0f2500801b0035001a604561420104601d400103500c601c50085030000760084070b00e80c1c1c40d030440d1201e1145500412031280c0f100c00e03041d100003044072810b042500d005e011840f03150185059844c960b0740040503d203420202c8030100d01821840d000541540324403800030900c455140051031080c04080021610341d03207181401882d0000207004800c86401c940c007408040b5001040e0040d08607154000c4000719200c06900d4280d110404c2c8103541d1100012032702290315101a045680b0240e4044443d031074801d40c0c901c40c007281640c107032520004a07103e18554034480f0704041400300c054100301d142c401e4800c0c85d5042e06040614003d42142c0b803607034500050240c2608800210142101c203510a41003c038946d4014026104070b0101600344107800d02030708208900c4140c981c40c51540f00f01e1282000f0f903a00304032260b5030005150b02c0340021488104c20716829001050ba4490400c280c2446008000075400092004200080340c0d400241001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 81824677 1250 81823427 81823459
    0x6020d0905070305010b0307050109050603070c0812040602070b06010302090a1403030903030d0f0606020a0503040303120905190606060e0607150212090714100509090c270901080a1e02 81
    0x110010041d13000b400041900e081300c8040601304140c603040310b8140000d03030308203001030388810381030701d911403118100803580f8003050810715201e0040244200825403403404100800805802401ea41481130305c90010301c1c0c45600040d826802015a2681c00140c010720400c11000c034102e150924020250640e80740040c001d003c6810f55100c1881d029030f060301e4150468813002d091080c1070042000344040c0035070400e00d0b900d4580700c2c415448060104146214080000e60260344042c9200390b0044c212040c5000c98924001290480c42e0141c4605103800800504503005034108003040c40000d20079842c0c0500c5540c0c0461242c48011181d1000c3d60901610000c071030fa14001038040d44521001b003052a241c2503046000c250403004080c01080f45030103210301660010281d4070040c5007114050b1480d6150050b10002d4003902051041071b4001ca030280001030481c010868881d03a00b43d414509d90380e2260000d566a0f00124001411000c0d00340c050501c0307055000042e04c00c184001c08000401c12801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 81825927 1250 81824677 81824683
    0x13060f06060804020901050901050d08091f020604030306080c1c05010b1504030b060303070809010309170d240b0301050d030512040b01090e0109030e0f0310050112020109120f06020d0905 82
    0x107009100410852010f0009514091103500c1c01400c003100d4000c01d40d8184408104c00d056103a00040c00502d010402c010299111100c0c0f1440144501c402c0d4518101c50b10000c2d0b0b80c201c02c0d6400d40210303244c000d01060445022816480042002c0c06485201c1c0740c2c03401c083c0c0d01034040003098845540c1d5800d41812641c3d032890070300c119508100b0781070b181c500b1410001f0074030002420580c03003940308105040000d00b911003a101503500900303000428a05504140741e0100059804080341580003c03481343c0c1104590000314400840313801c9203403491044031000f00300032841c01400039508051004014501d8418101c0c02054402d01c4c05504010f600d46440c68166801d8030210b507800051001409007171210302c200a45a01088020b05c113059541d01e0240c060b01090316414060040c01d04c01c0359403a1020800703c1074891208008100b9982d440e6102129104030790b108a0008480d0600041c4100f035001801c560541c0103000941c0312901c59076507000070f61020f135823050303c00e84414404010400074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 81827177 1250 81825927 81825929
    0x5130e0601120506070903020f1e040509031801051e13080d050738060f060c0a030212040e010608070c06090c09060503010c05030c09060c0f0708070b1213060f06 71
    0x500b41c8210b10790304500d8058109030004000300204000500c0800240e515207151000c8080140c0e681780c191150942400d40301d01c080c11740640c1080c01e00c000d0011005000008141e9403a040c0400b9011480c80b2004403200c3c0f00c0d14800c030600001001e440d0703283d4032041000306140c00e10701f4000a10196901c441a040603122040d20001c20703004109a024032101b0200140c0e12104041e05140e00e040c00342c80189448506000f802c40e074260a400a00c854403011032010354200000c05c02a02c1752521013405550318884082180140070780e0040300403416941080e039090701c806540e004c5140c1e0906400300c801c80d400034240000c00c1146c1c20300f1400b0414038031400700ca86002d11f5500683e80e00340b403901000d80d03049a0000b40240e00d46041c442d103c5611006680d0030002d40d5040c00c0d41c1d0480540010014014401c005e07109002d481d10030010304e800024400110be800340140c0b44419640c84048950703014800e03812803804503010004e01e420252602c51854280700b1702002400420b201c1c882001c480032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 81828427 1250 81827177 81827189
    0xb04050a03020c010c030f03050c1b03031e16030e03040b0a020303090c190504020f0c070602030a02060a0504020906010c05010615110c030712021318060902040c0c030905130e0601 79
    0x450101030505906110088a2002c20300703241610401a680040082a00e001c428082656070b8001c00c603c5c001d44030031207600800c01a54001d941809a04060b120b61050b110305a05000206c2c111000c0c620042c0440c0c40345074000800030308100c00360010b50240c00002071a807070a000801002c1881c103100383c0544004151035004640303e1520041c040d2a141d500c0c1c1446108080c003403c400000c2c0b808424034410f80d84c0c19280507071261502079403901c89000704000706c10113005914000c200103034000007a00d040a025070803100f0f41e40310328880c103040301e0b0b003518043c0d0001c50040002d0700c1540a09140b61445108100008a541d40c500003149412120300d11440001d040e01c8100040c203200300070b060010300c0304a0107085100e282c000a2038210303103140e10081c09403450800740d01c02540c10703a104e00c080c03075407141368001c03074a5035450910014034410304200c9c030071032420a2a084076441004900c7d0000c3d455110903041c14282000c20130700c0701c03c030070b124020603864400c00b52001c1b40a004250003824 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 81829677 1250 81828427 81828433
    0x4050f0d030b040e0604050706051e0f0304031205090703020402030601051b06010510051824030f071e08060f13060806060423070509060c0a111207030525030b0405 72
    0x9440410044c0c40ca0300040600b50380c040b2080c0404540041071582c201c0b806403c055a564250702c02c800d0115803e540000c1e0114000326a0184044482c0d004602c2541300782c0c1c0d201200312402c049041150003d8500c074410354000704040c0014100740d401143c11940c141086410043d01c1110380c40d0300c607040554980e60f44c1140e001000b050501c0500c0d01d0300809241015800c005800c0b0f90b5450030341142c3e00e0640b08107a480c0362622003041c0c414907007012050305011180d80e4a0410903895070300030255200c500040403a01034a460b100c241c2e081d103a1601483c0d80d10b2281d5150b007400c0025440303e5400140d4000104490b00011111038445c1800821420001c0c20b0245000020001180c060008402c020781a007102c00b00911191000c41c1e078080054282151900d062034007051150051560030802071040d10030390400d2182a6800d0040c0a500301d40e406c803402c0b41c00e45c00076140c031003611000f0202e507c41c200d102032a84035500e6042c0021810001880000c1c3d680d111200d2443d0191002c0c0d829030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 81830927 1250 81829677 81829691
    0x30221192d0e01020a0203030306090c040806010303091401030b09040b0711010e01051603060302030a1704030c06050327100902040e0d120e060f0601210c0306090f0b06040b0304050f0d03 82
    0x940c00001101a000090024005d504034a03000300b40c9a1000904c0f85100c4c9169800003210701c00200103690103014010200c51513503849183c0508007c03058040c440e2204030300d25518525600ca80100c030070701c2c04d0150840b402c42d1110350384c2d48140e041c091300324002e02090007805a0b48410034807603075240b001d20304008143c5051520042c2c4000d000c1200307401c00c140c1040414005a100041d4404056902408004442e45140341c8031206020369040200f0003101c0501c005041c40d408409140a107400915106080a016941140327124012482c1a100e80142c030000700c1e044926408801040e0003d0004114021124850b40c20000b0440c0704a0200381980b00040000070706108140096055800600150600c100d00c41a41c080040c141410466502d82c4a100d9110040340e881888e00d5004050005840300700015010700014050002e08524004940700051031902941c0b400c040080d090914080c1815000503460380300034410360740380c81141c10040301c2620410100034941801d03640080c3c06 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 81832177 1250 81830927 81831017
    0x10605040f020708070b04050102070209012d0311120a0605010b04061101050108061605090409030203030a0c0302030f01051215011806080a03020c0f040b0a030b0403022119 76
    0x40e05407511456403a0301c1442020b0008a0400458050300e8010202030307050307616881c02c0781c0684907000d00290400328a41c0001503201c0c0e85003aa241440200305c0c030385070013111001c001c07001d80c48521018060883c2d14600c9411070030411200c00501c14000e0598022510300e40380c43c0d0a0740c0c0300707a01001c124480058100001c1380d0200c1c61181e18241c0314000d00c501d500d80f0400703581daa200030706000c3c000d41d003101c0c0c0030030014003070000c45800d01006003040c00007240b5070601a442c0e40040710155107a50401c143c44c0c0c1014803d200b03e83c4500d20440c9140b10f00c3c0d0070181400540003804075240118402c017a4560310440081c101140217020201c410744032103880714120b20a4619513403100c0c607642d00c90203a480000341c0120f0fa0001d09042681d1043c1c00484c3c00001801401100c003d142d04241c0e840c0c008003c1c46407000c01a2310460281c0c00300c80c8940305a41060300010b40c6520b405405000902001071080d11460303035a0146515031801100c14003080240000340002e400c10002c940c81c0040400d20b034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 81833427 1250 81832177 81832181
    0x6040809030c10020a08030a0204030209091522080708070b010f030201020d03020f090411040504061d090d0f080703110d0b0102150613050a110a090905010f06050a030507110f01060504 81
    0x1903008141c515030405003500e440a5614045d24030028075141001c03000030b58140b8a9410388006640041c5103107081d0506030007041e122a442203403100783c1041d810025640b20b185c0038003032211030040350340c100c020056034440400e1900300a10448041303400b04203d001040d08031001d24080e18030300800305c0006145100180c5000c0c682d00011082c10b0043c07142140e1181d41c0710a0351120041610003284507000041c50b04454412900010b6000b03203000001300c0c0741e1004c024041500407115204161a895000750203a0f540c00840b0450001280340146040c80d074450300380142c20817068140803070000f42c54807600000d82c02081102d070005954000c0c2c4100380d0f03230402000b0651078034140200d0080c18a030022484083c8048409881281c031040410805001e603400680e01c40800c941140c0c0b035408110004203424039034403ea1b040242084004200b040300c40c682001143c40c0f03520f0342c42c0740c041012015000f502000b0144000c2c4070070a017150800c1c4001780325144880501000004800e4100400c11003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 81834533 1106 81833427 81833443
    0x30b030111090f06040e010605070c0f030b07030518060c0a050f04030b1902180f120d030509190c09051306090606050a0b0310061409030604080903 65
    0x2040c02140c5000c0d02c4100c00031079982003020a8081000042c0c05a030160310600c1c00c243d0010818580154001d00c107483c410072480e59a1030360340001c49015503a951060300d40550f80d60401407081d5141c481c0c01ea011007450882a010350f8207108896460300020122003400c00001000340c2c28500a0302501c0011210644642e51661245800300c0c89240581d80b064052801c400103943c100d103640241c901c260f0325541c07104a8203034a541008030392280f000030726401c003504c2e2048004010007401595902042c989001c1840e051101c450ba00c0c140c2110101c403440c0c0d141075011400520400f89007400c0300e500d03503004941e5031100ca50f10312800810743c400400b41460542080200141c40d00301c0b00449030100c2d002c2e90215651004050ad511049030f450002e09030702942840514001c0d13448580c0d4a03800e002c0d0504003808070b0042440d004083d20f040d9017103074002c0f602d00458030b81000501 = true := by decide +kernel

theorem cover : BRFrame.Cov 81654677 81834533 := by
  have h0 := BRFrame.cov_init 81654677
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81654677 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 81654677 ≤ n) (h2 : n < 81834533) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
