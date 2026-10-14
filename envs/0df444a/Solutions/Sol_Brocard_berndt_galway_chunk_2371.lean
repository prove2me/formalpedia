-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2371
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:30:49.456619+00:00
-- url     : https://prove2.me/submissions/bb84b695-c8a9-4baa-939e-d7a688115f50

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 426258992 ≤ n < 426438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 426260242 1250 426258992 426259013
    0x30d1506170c1c1b0309020a05030f03071704090c0f0f030506092d0907240905150d09150609110412031106090c090c090d021201090b180118 62
    0x8003d6111440d480d001d0078034401d0303840000d540f400849500104010810010010050600300b2401030001003000f14451800145694404010780020b42c5004842e643d01603c00c4c50080300d41c1652031007484003142c007140a0042c1c0b19804095075845000e44d1221600402084010f143e0400303052811090280c0781c0c84010200368001c0042145c00201045841e003445054040d01001030b444890b5014004480d030080b44440407119140c0742c181e21010101e0028440c1c0e90740c49130030008541d404000b080181014030a0305851070040347e24038100048081d101c1c0aa8403032401c1103502d6100d11216500c11009449000c000d09007007542007104a40310102160580300d00d002d59400d0304042090300f410035110f045858090201a000d0310b0340c0d410035080a551701e40b85110703001d215540401c000340004154105852607024020305000c41d03a00315800341710240e0703c0045201d07259521501040c01003850b0a80740b82c081d4110000e800d006500503541d003400c40d000c0c440390401080c0740c014004d001c605010301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 426261492 1250 426260242 426260257
    0x302090a05040213030c1d070810050f121f150e040215090303070609031b050c010c03020f0f0a02030708060f070e0f0a143f030d1506170c 61
    0x50044c0c2e03a6149082420700d402080e40000c01c4151910342c0400c0620120301c0032440c000800301110080d80303820b00141e585010840340030b0581861003504210307078504600108032420001d404039401d85101c607060760405d00f8547c48a402d0003a9084c4d09603003c1d91511441e140c5101c40f503200700d1301c176081081c1c4500403c00984042d10501c112000340d0400701d81c49085132103405c0018200d070f98039141c518000014028080c2c080c1e0201d610030300800c030010862911040c00f140d00c400a089580c85410040d9600c0c4440041901144140000805a68420000c2c10590010340004100c3c1400d40e02c101864084560003001c0c0d19009001444090302e840c506080d0041d0720b505019a002740e4402c0420203540981c003c0036446541c580c00003400821031900300034209025984811201c802e0100ea1042004901000081ca080e1590410041c0c10100480555032a01c0b42580d02d00360848407030000f41d443d55103120740d0080c070b2a0003c124a54002502000054030400100300038944400e014045010310398 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 426262742 1250 426261492 426261499
    0x10206011503201222120302220915050411031b0c06040b0106170702030a12090f03020309090a0b090c160b04230c130c210f06060302090a05 62
    0x1040b100110341005000a40a03c1d0148251160340e880361190100106441034101903c55548045040114900a28046801102081d4802d40c0f8410850081d480303401314a6021071280c0c1410741010408020000070b0009240200c2c083c85d1030300306216041c0560340030600c12480d0004100031404000207496000c0d034600440911144900c0341da407058443c0360100700c0d10740501c1080104010440b45e0b00d906a4025540f1010f0002d0345a0b40c201032100107403101d40260388107112900741c02e481505a02140e44aa05010030400e0480c1c1d901848500781403c100c01680002ca60000c00b4207001da010b69100000b0407041c000c40300244040760710200c000c0c00140c0c0110001840b4540d24803050103600d001c40c1d005019054a03d014100020740d03580100280c2e0b012403a02c1001041094001043c01d06204c00418000d100c0c01c7c80601c440003082c3d607400c620180004851652540c810100b040c01d0f0030503275100c01241441310488444103d0344950089014188144000c80042e141c0c05900c0d000e0700e4058 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 426263992 1250 426262742 426262751
    0x20a11011b0605070f0f030e0a12050f0708030103140303010e1303050c0f010902030c030d17060d0506240904051c090b0a1706040c12020304061b020105090c010206011503 75
    0xc9104215004200601510140c142420f010391303a83c0c04000400c0c075020a42c0c940f6017044848404600347e4012443d03000070356219a138003102249056036110340d0340320541030440c6040c884042e165440c1d0014181581c54000c044010824410072420b119254040000038601e907604121035003801030001341080e1006040b5500000815001d5002c4510201d0000200d90143c0340650f1414082d00f03988400300d000380208451003046080000745d5070300040c069110b07901c050030f03448000d9207078180c0181a0380d0b1144008840c040810302c14815540202e4002140c02000c01010704166480300341c1c80c0c06140600511030800010075400704074070390b001400516031040c0b818050401c03100f808041d0440c1c01c2900e070002d90001140e8001c111551803a00d1303d0101990341e86c0e05420001115116549080030403400c5a015040140f81d40c0159400351080f8000141c0b0070ba0351000c42c412007410455880581e54a801f40311020501300b100c159840da0910040c51150704107094080c4200100040170300341501c5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 426265242 1250 426263992 426264017
    0x703090503031503010b040204120507091b140706110a0305010f0e0f0a06051f0201050a02042702040e150f0d0201140a171312110307030509030312010905100501020a1101 75
    0xc2d045900c08031b000401c02d545440c3c41e1018603000d800d41820480d0180b107258000a0152468010300035120342845400440c003048038400d86002070705084502d0518802c2001d00002412481401d815202e18045c031915951040c40160072030340306800c80000c810000c44104003074141450203643c03144c10044141c1454417054000b00c003400c1c0940000d6441490b41d440001d200e0040d601c465800d04481c0d000b800030b40c4800442004a02c2207000d511503c0c0341201440013034007580680048031a00d1018014506652840700390050582950703044074102c4a0008041c0d50314040741d694607000070454030030000f21030701d45c0041c0541000c054101548000881e0524425001d000d4203400f10011040740001443c00c4001c007145400048421680380c43c64801382c1038994450800e44041c0e141d40ca0046151001644054a4942101072290350500c000c100c032071081e688490040f80281039007400403a071800c1913180ea06801020340c01c450304540c04004440040360040504104010085c280048101032 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 426266492 1250 426265242 426265249
    0x130204050a03060207021207090b1c0c05060a11031306140306090105012f0307020405071106040b0411030a05070311010c0c090209040b2d0d12121e020304020907030905030315 77
    0x1d07480c60101f103014211001400c03030038907000106181d00495443c04030724140078503c2243c01e180600900f101c1040081441241030071030040401c40400d080038405900265110380c42c5d41d22242100001c405081800c00c800e035080600d40002890f50090107041d8585400810100c141c1481142e0402540000544151220416a021120100c500542001c1d880c0c0c16681d0780350300c0040102e009600d0840080d010a01c110081c000e422203c0028081c140c40d56194a08c3c2450050425110602c54108000c91541c08102c14001d00c2d1003040901442441e42c10310380d08030403410207428184040021803d000891001c115000d0b10229600143c8820105000c0340c014041c1c00000350300081030248d401c070700d1354010350304d05c0c0b040360300440703001e0310100703400038041d8088000340000c120302c964010504941e0f0145404000400d650003000582c140c0f1940b0035824810390380d08500b041e960000030b000941c2042c0094680c840424102445012020b03078038140e5911004144a0107201d07800c000403039503034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 426267742 1250 426266492 426266509
    0x4051c12060803040e1003030f21050906040c06090506070201031d0a0f05071a09060c0a051e070b0f0f0a090b0415030507030b0306061c021e130204050a0306020702 72
    0x65104040112680b80d001ca01e60b00c0d48180904118000c0d201c0008011680429030601500e0303042d600d10001040341c60040e21006640100440900b081d0100110301c1c0c3d082e0300c01d4510a0f90050002c00c400d00346400e0942404200350400c5040008942e41400207840d11001c440803141e0a1070b00040d050041995985208900c0c07079841890701502440c42d041c0152056082d00c100d000b28181e4101c90381e16580f0303040440307055200c001030381d41c01d201d50011481c00e440901064000c410544501d21401d130b4580e800c00c880322401ca081007034007051450032000c04001032405060710540703c80c41c04040c0d540405003401100c1b04d2030f800c4600001c40248035803241700030200412400413055141e07501c1c3e255140b0801018601c400c0042e1414001511251080c040c1c10030840c1c0203400f4203a80d031280c0307081c0104125400e45040500400c10350500060b00c600510004281038114640d0b440f2034103c041240300340445812201c0c00d40180024400d664400340d030f05040382e5209030016940c0010b480440e00c2e00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 426268992 1250 426267742 426267767
    0x9051b04021213020a08070e040b09010b0d031116080712080c01020d0b01031b080f070309020619032f1c0e06010f05010c2111030406020c0906060304051c 68
    0x2000384284a0032103c2c10748188806071089808484c071544540d0415650795280c8500f554120414011401248804101c960080d843d1070003c901c1c00a16000b003030104207000002c0700026011240d10082000621441040724699003096540c54900040b1a503500f080f401400f40e003100b1003d803801000707013a50844075114000c0f8001c3d51a0301840d800345000704020341582e80800d04002000040f2540142d1b50001c400498990f4051034403013510007200154020000800e00d952400603d02691f100720262910104010a030341c1510107d110007400c0d164000c500b10100114240c13400300c22840b0310681443d1280041c65036445108001e60680400e01e8205201c5074245028000030403004003040a9050303400c03406400f903483c0e03955030045600d0340c4c0690018006100c914020040c44868220b008030405145ca41080c0c4201099461811075203c0c1c0d10000c05a40102921000303401d00715290740d80800202c904504519041d02e42e6070701d13078040e10b50035001450890250b414040c00b030403115128 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 426270242 1250 426268992 426269017
    0x521060709030203070e130f0804091d0d05033102060403060203040b0c130501030e0109140a032c1c170405030c030102040f051c082a0109051b0402 65
    0x182080e030005064640d040c041a40039001e10b00002c10283c4032060001e00070f03d0701d5180303484503080365194280101c2c0310740c40460303618070100070000310303041d0714002c81d003190301844c12880410031001c814034940202c03000c00e072062101c1482040b030303444080c001361041c0c80d100441016910b4001d8100c4502c01e400400000e601c40701c0801c0110900c62241d014600c079501c58030342c168254441d50b00200c0706001306c400c42c0c0d0381c81c2001d840500c15035200350030880b200704403040042008019960390f9080c4001d001e06044442d4041720000040c503901c10b14865041144001c0740c180e109003400348034041040d400e44d00c0d00a0240d00c901e00c6186a01c150f80d14040c0da00015985010051100010f004d5446031081d2486442854a00d0910346410300c00c95003182c07000a5039080d581d1070107090084804611140c0d02e10308062400070303400b240011000700810031070003021007017000011a038400c01000c1d11135110400d0b80b52a00c0707400010303030001e107120805050210a49440342180d000801034414600800c02 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 426271492 1250 426270242 426270253
    0xd06020721020c090903030c0a030e10021c090816021f050309010b22051306020c03030601120213140411040f060f0206070f0503042f01120908040521 66
    0x200d010003000c00c880760950340d09490b00000e00a08101c102682540d40c101e040c1c008101103503450301d110b4014258650796084c00f107807182c1c80d02812810403801101e0411a10b40015032071030031600304c0380450504200c0e20f00c10404000c1c0c5440e0841c0038045d85801c3c1110900c0003810302c0a40d82c403466620002c28158000789000728112500600c0d5070004d4602c64465030802880d229030b480c15083d001128403030501d4026455003451000c5018080103001da07000c15001c1c1d098107021078000e00003400030300300c03000041d60b40b800d00400040070842c248810103900c40c41030010b15141c621120310481220000050b044000030000001802082d090b40c1e0b002c041013001800003240500c0c0c40024084070390640380c0000c1d40e0160003060780c50748411940080000d90107030700540301a0140016540040c000d0034004180d0004181c41f004214003080c0035845d08500103c0040c056911200d0143c1ea207003540b1082c401c1001c9591900e0072800350b802014401c04014203810340110305d1070b408181000066080f42d8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 426272742 1250 426271492 426271523
    0x7020a061104030b071707090302060715090c080609060a0c12090203011d010e1504030906080c090402070605060321071115120f060109140f010c14010218120601050d060207 76
    0x401481c8030046c4400302008180028281d5070060759044100d83e0003804561601142c0c0d030b1014100311200c04207103003055460b520500030403030890340c11010782482d000804032030800c1c40506181c07541c0203028140c03460401140c00705039540000301003403000c140c00011881c2d441c1440024050301c1503064006100395032030b20b01c81e4401c1c815008880440e041c0f0f400d5803920162980d03000802d0794120380203070108040b001c007040414401c1c000aa0310046102d522418682c8000008042e0703400101c05940032070301d03441845510f103020301003140b410212070340c3c1030040f152404070f030202806490390141c85010803404e0040c0380d440d143d0006614100d801103541d035030038088168801e19139098400340800752072400080d170035500411041007510300b04000450028041403c01c4840444804a54100000045080c3c00140c076284c6035001d00c4a01c500168032900260155004810804450f44c842e0b41072280100000d0f00c0424040d042d0b4034182c03807650454900d0300b0140301038071510b01d00501c121300001510 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 426273992 1250 426272742 426272747
    0x605031c0320301b07050f1603030206060d0c06051c0903110d080f1303050d050907170106140415030f0c05090105091e07020a020307120204050f07020a061104030b07 73
    0x8960483c441c40514040b641e400fa07402c102c1c8108481010b100c800c3c0440380e014402603807002d401824480e4040f254103103079094005040c100003040240245074815400d00030181c05001c61603100701c050b289140c3c0c0c2400c035211b9420b000528420203050107000a084a18034800440b14018241141400d000102031407400800c0649214040440c1e805114084003000d0b02c00c0700d070b0074022009081d00d4081178840c07048820145030034640440130f00c00c0402a00c0d0101915001c0c2c00c1c4250815809040b4052030801484801203d401c1200000d902d006803d01500000c0c01c0c1d54016160140c600217031030009200f848002c400340340c0000e0b010060302c90001c020050540401001e5613000d80c0d0f02442039030b80c1e109100700000103440903a1a410740410260322000148001a44003406104a0302c03d058641c0100341051500d80202c04002085420003055090500500d6001303182c06915405600d03010300c00a49800e0348640081c0f005d5120344840354101c0c0c40301e0a40c0c02642e00050307482c50904040a01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 426275242 1250 426273992 426274027
    0x515030613050c01050403080405130204030f1109010617040611041220061c0c03110f04080f06010302090f090a15090c080c0a0b0913050403020a0302010605031c0320 73
    0x44074140f2a9030b4910510394030a000b0764084aa0116005081500704010480344003140c2403404101a42800700101049907207141304191401500b9284448081c1c40510100141c1600a801400300e030840038850781a00f0048103501540085001030300800d00406801c40380300300d520048401000c9000401408101e10420069406d40904030403400486000d2240c980903484c4045086110040404403542240e08418403600702c03480c001511000716921800c0c00c0e00322043e145c41c180c03008a01801034100c10802d000d1088912401080c05624603400a03a40c110024120411500c03a400441c1140303900708911308505500c51043c0b1424904103210700b001f0062103d050712442c000420008801c4004102c18850190142148500310700304005252030798040d144568000c1c3c05040070294420080c030a4a000d03600c294040d06007502c45084c0242981d1440d00250301c079410400744a040007400700300c01c010805035400c01050b0040d948000410700100003100c1c880e0700300d0000b20030401d148007003130 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 426276492 1250 426275242 426275281
    0x12020609031e030a170f040305130302120d030b04150b0c011e1b090b0a0f0210020d140a050907060c0501020c06180f0c0603060f031627021c05150306 66
    0x172001004a803070700402a50010607200a10303007684400102d000309100d20b00a04030002d00040701c2050b541d4039804564090300b049495911078118001000c10729038980140050303504119002e01c03903100049000d001c0329a807446851882c0a002520310010301003034024000404e504024070f4840c40b03000c9071000182400b0840c00e10751100c6c000c007400740e240c05001d1003000d441001c80000e040c0b13944854141e843e070b580341c42c851055101d0360500c00e4181d09039000a01054544407404583d182400402c0c2500680103440d40c05000e040004000ea10f900025142c001c80704540341140c512290740c12710b58028400c03200e2141c014000c9004200340d0703080503a1826010040745c0708444880c0180205a034858211050040d07010004001164040c60076625120a2810003130584203403004140c0140707068105544070626404160140001240d00c40020301042d800c0014154030300b00201082c0c0c091031207c503503081c40107507941c000f1403090100c102d441e010100001c0c0480320785003041896252618000030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 426277742 1250 426276492 426276497
    0xb0a20070e0718150203070c090c0201060b25030c0506130b07050412110307170c0a05060a080406050c0c0a05030706060f0e0a020a05090a06030c031512020609031e030a 74
    0xc00c15080c8149001c11680024400004142d4100a24000b504c0880000f48007144814044403000c113244050500050607204d00c00034980310000701c080e080d940309601980b0040014130030030581c002110310301e00710045e40340031117040510585030627601041c1095020308944038040804c0409180e030207601c0b40250043d0b100107201d998036101107800e4440c50017001c61120301c82111900054403030051816008001703007035403003040d202c5c8030200181004030a841a41e6004c004284040e0a00130b0a29001c0c1505950780e6180c0800244042c000700300c0588002c0c5101d80e2180012a0f12020f142076441c070030b0f0100c068403074083c11820010360320b4003c000c040e42c0c0d15143c1100042c4c2c1d421009904400c8600103090701304141d554403000303c02900405250300c18003404000c018106d95403154039001914140d1000240280403d0000f01140ea44542c18405110b00c11000d001d24560300d06c0300c45880d6030481e185503444113840c0103c0d0034a00c40307618005c42d8904101ca0400f64103000b1000e010140760303d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 426278992 1250 426277742 426277769
    0x30708072c040609021c09061803020607090801150e04030c211d010f080c0d091203050a05061e24030f0c030609040308070e09040b0106030c0e0a0b0a2007 68
    0x2440054228864089041c4210800c0c540348084070011f40c021818517401200c002404c45e00f9078298264882a003982140142c010008000c0019045104030f0003a0000a0003008424002d82514225140368090b96034680300300d100041c101440355480f100b006910074075200ac41c5000d9030300c420000340d1268500001c42c840c0710b03c4002c0f0030304012400d200c5003416903510150340c5100b0310a1b1428040580700840c41c2c0410040d810007c10503000303440c08203108880329040554074400081c101c98002c1e01d4680b03010b00305000d00620b0f5842c10102d090580304281c9011060710840300055543d80d860003450b800c2803540c110f4401c10b08031003003e503100e40512042a40541e0f41ea00400005100490304154840018000b24004c24807501c40280c1c058940d0070724040c5141076100184c3c0400c030440f030032154660603400600005505010b9500c10682600700585040340e08000903410011a005e00410210003066001d22288901c1c3c00216000c282e96451340c40000d0040b1640c3c031140c0c28011240c408014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 426280242 1250 426278992 426278999
    0x1050f011103030726090703060c02010911060c0327100c050d05031b0c0d02070f0506030604050a06150201060311060f091002010e01020f03010e010605040506030708072c0406 77
    0x41c001c1c01c54200341c0601035450b60381e0b0300c90242d8904074503100301c41e0043c480700c00321540d0f07403240015540510300b441c00134070a43d891071800e0001d80e0b608404107403c59041404d440001400420700341c5101004440c01c81c0c0781d20014480c2e502d1800380260100e1160804803440b040049000c46008803c1c0082e1103c1601c2c110030301c3d06882100344103c0080c030643c0310304201c800741c520030405580c206c0c0110348000f408415244040c4100c2d0017001e0380c041c0c6a00048003184201740c0400c441c600400c8130b21000c001c02c51804000803068000101000d00543c1c0360744c0064000a195030006c406843c07412840c0f4403443c5851002070003081c1c50b020803140061103804c24505480c000069603a000d102d0302c0c0c041e00d02101c0006000e5074012503003401040d50340302c4964002c0381c5828009400b00700b01000c00c8035120340c9056078039510404182d10203000c0c0882080140310300e4440c0e8040b40c4e8014440e090105194640541c1110b030340347c89800d0000e000c0582d0201581e070b0044140c0c6800080d8080307a00f0701140780ca = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 426281492 1250 426280242 426280247
    0xa0b03240901090b0109020903100903051b010e0a0f0203032a061b1c111602042901050703180b030a14090705010309030215010905040b150112090f020d03020601050f01 74
    0x700840c0c040c164a0006004004025047d0000e000b5410044c0c01d6903004200010403000b07031809a14110f0104034085000800220010f0200c1a050740e900002d214000d020700c809915403040540c05004071400e00c07aa0001e649080040350700c03040040c0c0d00c45043c87c51070130184c04250082a4136140da405282c01083c03004a240804007491009440464500908038082000c440000950300c03403601d17140c4501c2ca400c2000b480c06410010210200115040e0040c41040100e50382902449005460034010403d5a00a403403041c1140c802802d0182eaa401641815100e100202d030350001070001d866404600211424099805907480b5082071160140b50111110720300030884100213582d100c517004021541c400e400ca01c07a664000c0c0142c1d619003820207040300040e40240c0101034029240c2c401e00c0300704411415041e13807000e0300503003000103854601e0008050f800b0075110710000540300d030100c40c180049901c0300005584c4c010680780140d0040d02c1c000c0d442d074009101d99845688200c140148550 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 426282742 1250 426281492 426281501
    0x2030601180f0509091518070b0403050303040605100b160309080c032104050d0c0302010f21020708090d0501200c06041b180e1207050c090a0b03240901 67
    0xd008042c1110080e0030881030160200b4000d00040c103d1003942c240301c225210010f1246c0c0110b1124840c0350b82d00500d04d003560714003240703540710704400b150030841040810004010790742c105501220100701910303100c0c034843c5040300c180c020210f45140022900f61360000c1c2200b11642c0362180e190b121840395a10320b09038680088100180d056004031041000c22800260f90909070400750140508041d125004210300c00380c954400c1703807182c0c24148140217540c1c101e0519603202d411860700d00f0f8200c0c0302003a13402002c58490f40d1141c403281c01045520030401154266464130300040c00a120700072140c204903010b040c074030300e41c2000c000301c0c81021742c504c11150341241c8107410100300818558450b682c407268ac0b42d166058800c5064121803022540a40a05403107001ca40760003808140007a8980b4444c0c1003100401101a00080170090940066001b1640c1c0e240f0401c11603c0f8902d941e11001141c000c3d00e2610f05040e41030203108800080ca52544500c01403d05d00e40c04002003940d14044090308a9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 426283992 1250 426282742 426282749
    0x11031c0b100c02090c190c0b180d03021309182015071a25030605010903020108072001020406120908030426030f090105150a1401030b10030203060118 66
    0x2d0b00b954481c005424131034101608015415665031034204030110a1070014010307860000000c45000403c0140079000c050160404c1c0c01d1006160454903c505080d0781c3c100744c00c0703c00280354021441680b1410050b61550080c44022000e03c86440a000440044112600112a10703c4a40380ca035012140c449403a000415001c0c20103006502250407203000d85d044410201d8100b020700b03000f100340c0840040f00c54080d1051108180c0080e01c001e038000410071011041e00201407801000b00322985e4801d8400c422a5020300707150409403644101121804c010410b02e041c9030b401c0c800d404500440c15801041102c035195603003010740d02c0c0e41415606403201c10b14043c02004041c404240403c121081020740c103002c100ca035104220f14890b0401c2d141e001100c1850040c1c07031034410442c10081c21b015242e07215243d0020142c1c00b41c1074000141c80c11045024000030040d07da01100c10300e0340654850f4140c541c0040c00c0b444840616040100654800c803117150019202c240da6040c109103011540d020b8 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 426285242 1250 426283992 426283997
    0x10605011b060e0d020c090a09020907080901180c05100311040b0c03040e100f0b0715050a0e0714032a060a0e120a2102070b090111031c0b10 62
    0x1c01408800d028010714241d4070507500c166940d000580490010020034008181c150080e000340c4180710104100f00350001e0403503640c2410030800c20700607036a00c52050340c42503a60828100d19150712507082e006200c000da00808031101000303a00c0034000e52803482411100e0032940c00b0342c046044d4808406980500e0300300c024920302840240148941c850242109030054421a030a01e030707407001d2005074403078140c0700004103900b40b0106014a10881c00e4100240c6542e040c000c1c648110350759030100380c041817101800c11b29503800105103990303519000182901030703680403075240c0c0b616501c506081000100c5218442d2152031408030203c00b0000b00c000c81000100e2014101c401c40d01d003484100e40c085040310040003c00c00c15100e0a581d0030400e851600b4100b001022a41000d10f07040c920780a019500050013651a140060103607030000302f24080d2074203400750648404c44070b070050301c00c0207010300301034510700010518440d10f204c079404260302c543c0c000d0824011894070340240b00d01101d8001c2421300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 426286492 1250 426285242 426285257
    0x415050a0e061506070803040c0e0c0301080316021f2d0507150b0a03060b01031a030c040e070503070b0a08010b04060e0108270d0314070f120e060a020301080d0201060501 75
    0x5890250200d503100030f050140c40e061400405566040155000300d50456003801442014403840d0000c000b1203078031002150010b451541017480c132540c3c901401c0000010384610450080c115141e07500855002040c6c242d6041c124052a803026010710800c0310400c00c1d5858040e0740c5044200340340580c4004c0400d54682c2803a0803160740318000d1100320602c040305001c0d140c40007040c69441d880c4410700254010f401c0040c410310040001016200b15003a10513191000c107184030019030b0003140403442007004a40000b003440d86220805d0500000e1361240364980128200010817400c81402051079150340d0b640c07011a07030380b28a08030120380940d0041500042c541da6002003254043c20080350410406c0c00e59400d4003a0441001c0c0c07072442e0340c0708107040f29040000700b550400d405004095402c0d140c0d0320112102d140c004401411207044400c10410000d20704c0c1e403c0c503014940c0c0e100c4800c0e41d03c0102a02c0702c3d4900711400d80082d610a203e501c1581c402c0465401d005407045c8254820349030165074040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 426287742 1250 426286492 426286501
    0x5150d03050a11030301030f0b06031f020a02070b07080c0d050a140a110109031e0516032a1a1f1514180f030703050601050108130b0415050a0e06 64
    0x220a500414020000e0010710382a90583c0b44040028500852240505810310021403520540c01c22024182d01c1c0a07a01c10180407015504c1b2091012440071520401a180c0c003518504901e4402c2d1540b01868241c0001500400d00c0b0301c01c401888a090100200c84a2240340d10085031684200801180010700c204003034031030105007034000c2044141501e030100341d01080c82e0b40d150840d1a4040202d02141ca00e0303549031126500c14000c809580c0182c03e1190800351682221342d101d1415090050410403900407881c601524464000d54424401c01c0d1181c00004928005a0b4242081a03030902e010701140029010954201c1194280c501c0680c1442c4541c50404201d07046e05035010014240540200c01075010442c81c406840d12079007041c1403081c10103440080c814a100d8100e1041d010f174001a00130301c0410300000301c1c1d6044920a1801c94030380c0c0d544000e03005801030403010003040a480142440280308401c0b14016a05d40403500821903a11030b22403080484102c1d541c8080c590700301e0400074 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 426288992 1250 426287742 426287747
    0xd020613031a0f0a201207080105030a0302030d180b0907060909050402031504170d141006141303080301030620160b0405150f011403030307120b031e0a030305150d03 73
    0x4410b080d45c2001c002000c3c52810030320081d035007014414071084280b650030000c0b80d9501801c001d0042c001540500002801c64600035202d115240202104548501d1529050000c04144184d46900012002000d0418450554a41e00588940c0e0002003d103900411518205d02c03a250040745e00a00a0070364800d500c6480180c2c2200a100b036a8941d040d68124100c19041d10080c83d81e00b0031301400044202011400b2503030254080c0104140c0302c4024020b10103150008112060b112800110a4603480070300c00348601c0040703a4000034000200807000008110154020b0000380072030070080324204159608843d040c1c090b51500c1c602c00d0300201c00c00e07008215804905500140203005a8603038116010342d1100307826098440e803480140c00d4004009012040e2010142d484045000e1461402c0c00f4000400c1040103c600052407a40c1d43c0f500c4455a4081054405e01c0c00d040c04e40303c09a03102c4800840d20b9908600055001c242048000b94400550300288188180e000304002240c54594408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 426290242 1250 426288992 426289001
    0x50105190201060801020c0c0a151722060f050f090c13140f0402010207080a03020606040203070c020904060b0424150c06060f031a0615090d020613031a0f0a 69
    0x20040d956a40f80c0450355640038001000400c0c0d00c00c0c02400245404024020408243e82c80b40240c0e03060034400160459104a0403014040c11a0000b400c070b444bc410301041306404441400b82100b00310080b801002010f81144200c0c80e4901c0c020000e80e95000001c0c08500811201c50f44103030001c001003e01032900000b1202040c14007440058100d80781c1c0c2c18055005401e982c0300d0020300115040200310342c0d04100d81e2015221850150039507002c680d40107541c0d0600544a680320b140c000c4000742e13035244510400c0c05210740042c0543c80b64205400d0002c000c0418540042c0034908203401014800340c4402d614000400c401c5000300c5039890a90540ca48104d41c0e001c040070014035003640c03408169a8061140988113921055212910b0352a10710320582002c2040302c49001c541040002035541d80318844000340625160b19990303208400099070880784010004d5100c0c10200c0d0360b002c0c0501d11202d003429a07200311400f071040000307032000f202c00d91800c8603003030400b04211700082c840c101140c20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 426291492 1250 426290242 426290287
    0xd0f0f02031209010203160203280c081207020106050604120209040f12091401090e0411121209030d0203070b0103112d0103050105010f120e07090e07031506050105 72
    0x60340e0401e00040400b484040069903002c0e42da80d0080140a680880448055103406543c0002c5285c01c5204030454200d500d059806444003040120b00b1500318060780d01c1c0d500741035020561959403c1e001d0440100400c040d030b401401580703044400714041c10100200e070141e84203030399800b503c080c566007040302000340100100c440c0710400018100150307000307101011041c456107960000e00d0a200c141d48080c0680c44000341048010f030301c104100e00c01410b4682d00141c109550400c51404000031480a0750038114242c03040c03117001e02c00018102d99030094920f5400c110705a07440365500c1402261703030713028500024200005082c010400900c603e100e0081e0100041c0003080f40c043c02d030300c110101d03851012600c030f040c007115881c000f650340c0d151052501614003400d180c5101d08410308000c003d032601d07000f40ba0041c0e0b9654034010541004000c1d604c0140b02a0101b4030025a01142281e21a1200d11089801080920f0805488650303401403078150380040c1d50303040c100090b0006403038a5201421 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 426292742 1250 426291492 426291497
    0x10e01140c07051c060c2a050f0708150915070c0c0b0315010e030a05060601050f0403050f03090a0602190602180d140d05090916180915080d0f0f 64
    0x80008440c1c8418201604040002130584c43c0700589040c110306981c072041d60001002006030903480b02d5080d6075100400b4400741540c0c0381d60b8810b14035040745044030704503152000d8800c0d4440081c5920f4000351804030080d514080d80416146c500206944800c0c4451b44400007941000040d092841404241140390041e88005542d07580e80710744000c0c2d640b040d80d822041403084d1943c00c92558001245520114040d4000c005e07031030154540c0741c1c50310000f404803410008009282c456a0f050401640d001e5600902901c494000312240e8607640ea100c0c12a860151101080c00104140045040b0701002c0410911400c0411155143c100950004450a0b21404006140103480d143e0342e0146100300e00c21548500500e00a028107403070022801604800c12000300a958500d8842c91039a9810906040701b11181441d602e0040c0c03002c6001501c0d00c0803002a00c0d100141002d05900041c611212800303001c44d240da140c08400d900d61081c400c1100106003554040a15584103184142a009452 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 426293992 1250 426292742 426292753
    0x902130c050d09050606210a02132403110d030206070c1a0a0b0a090603020d151b020604020f090105060304260a030209100207033f080a050105010e01140c 68
    0x194142d003c492041c58203440d940e100204100d507604010106c100002c54681c0341c4440c0d00d03d1a10410760b25924646c0082c01122854102c1c00c4015031030300100980c0408115580c11400003541d500020305407407009a484900d100750304c01160601d014480410b64260703000c1d20480d074409106840c0c040c00c0d00c00844101040c55a03d07400101d031100b40c03501a11600001080303c182c141e08224290310150803040d1034601d030034020030069680800ca003516071344c8040054030015040c00c18000400149821492107984a6402d1900c26408107882d480f035442195408401d14940e0309100c40e9110074011190044400c001090108266107501c1c1d090f011071185142134605541c88405650f082002148007007a00401d091a0902e0036080d60b011012445c40240121032440d00c034206051070800e0250600103003031480903156000c48682050440d00300001c0e19160310001001000380700100e8280103010300e0b240000c561036204004112015805a5569080c0104c5025054560748440b00f010307540e01c140c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 426295242 1250 426293992 426294007
    0x601090902011b11030c09220503040806100603180f061e0e1f0c0903080d0204030c060c06050f0708070509031905210306031f0b090405030301050109090902130c05 72
    0x200324241090710310489062041300d0440e000c0c10b203490342c504500b0784190303482c80030040390b000b6030070b40c18200c400140310041d0000071071300b4031078110300c20342d040302c03000b802040204450844c031813640ca802c48015607001c01201034840e07500740d059079691200401052210000c0c0c00416956048052050005200a805501d106000e0404c4031207000220703a103900200503908550103012800510103010840600a030b4040c404003d010752241d00006040420109070302000300d0340b17503068402a5a10900402e0510723203030300c1c0c00b82c100501c4010450b0304a00b440d00184421544c5140305000360850384440c2044c0e2950203080d141508480f11068052003648440500319001d170b03c107044801d0240d00030f4500e01200828a1219616060707240120a13420002d000700341d103000982040c2c11030f0500141184480824546010b00301551049610001080900091020110040d41221001d880d030164065482090308140c48802c44041d51212040c0e201c09520180f5070801001c280003480c0c21841c0000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 426296492 1250 426295242 426295277
    0xe0705091011010b1c030c050a240c11120d0b0306010e041202070f050415080d0207170a0804030803130206030a0e0c0604080604030f110a03020f07090e060109090201 73
    0x7180c501074000030b210418860b81e488020300c030b032030890041901d05880419614400322010210028000c08100418501c2801c0c01801e00c005600d00307138807110701a04241c41d83c003054208a40c0e2114516010320b0850791000d1302d40141e1880a0441004000c4c2112012409095207640c10014a0500490b00d440340c00c80c60743d81c2405070138041e0000d01240742250a003403c0844a9880c00c50342041907500401d800d02910395800356500442e0812200421020000110001010481e038444806417040d6000d0828030703070300450003030f06079001588a81c900040381d142c0c1c9591a2501c0c02c0c00782034500200020320104210800440d40302101c8001010340c4003095010400e264800c0350380d548029600c43e280002c0c01e106002c40700603110215080743c00c09080c20b102c00d440e2240640002c0070b10041d42190300010780211203800711038140209950b402041800c019442d00c200c40c0044505008940c0d010030b60701928031640b800e5451610013030089078280b01c484030007041c01000503810700801e000849024807 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 426297742 1250 426296492 426296509
    0x618061302030c1201060f0503010e120a03020409060e04260708070f0506100f05040506090f060d020a06021f05010f0509070c1e030f02010b01271502280b010e070509 73
    0x9070b488000600c00d41f50452000d103020f05034110070b2080e4103020301000c2c4404002400d112a0744111034190b562001d1078000d800a1060b83e210502450808000140200507022000d11aa00903d15038240c140142c0d986841ca00309500058507415080c00500041210000034224140c45260740020700043c5031101d5240a00803240c0908481c03036680140103003203811041500600090720188604c4c00c000c00014501000101940d05054a840015502c2d6a40d0240c0c110313a03a402511210105884010094a40400783c07410548460103020607040c0018507c1040e049402107054426040d04040030442440700140841d02042801c29030701022641c440d011480107100f0202c00c01c140314180c0307806086505108403500541e45041070002c1c459802009503a112a4a0ba40500c405801030952644050a41d04251009848400590140c42d00043d80e006c20307581081c00c2c004c0d81c0d81003805070005103102c81c4006100d2042100108040c40141081940100003800d0180c10720882001050500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 426298992 1250 426297742 426297769
    0x61a0901050c1b01110c0a1404021306030f0c020601080d050c2104050108010815160c0f11010201050c0a210608010213090606031a10170f010501020618061302030c 72
    0x11007900e000080b9030340e00000920060524400035100001c80f410010307d869031507100740d032901c0010854a40703d42c1d0701e560440e100d11302c001102c5902030b502c80d06c004008140c041c0d80302600701d14180742d4020350383c00051164101d4403550010b00c0b40100118003200e542c0c00055007040e080c4684101400680b002c00c2d2a1018000c1061750036848070724042c00100070a00690202d0348a4222001070303041002054001a441301e582c030300c400f070b1034294031508603808039611030040d02c21956200c0c00d00070022801988240504264020304c596201c60410706014401c00d40c0703034070110358420b40040711142d064000c0c86004c400154005989170f07a5050850076607110140d52104900b204400b408100504d00c9110302800712850104000d100c5611643c4501c9104055203105004da030701600752481c890040c0a02c980300700743c04e85000d13040404402c207002400b0701801d8050702030b17000001c1c281041c030000d035810048000c00810054490742a407029101c0150410380c1c16000c0d15801900756182c00d506010310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 426300242 1250 426298992 426299023
    0x1811160b040501060b0301061b03022a10020c060703080601141606110a050915130f0e07051606090311010e0c1905060403120309050604120210061a0901050c 69
    0xc40c5403514101d0b013102e030710360003100c060401840113102c040d90101c0c08095500b0040c2c00921050303101e06090f4504107800c1410420160350301503401d0a5820002088450306068601500703000c0741c0f81c026a11108500c0c6460341201d402d006141c003180c070602d5042d41102c010b06060984500c010792904c0c0c10390000c40e1303c05640300a42c0d6550204403280c1f0410b200032102d60500b6080404904006000e441240d5000b4401c0e00c03020000c007159000d40c41102c61a1000c958828a0140d0300c104200174071859110b80b50400b551030002400c1d0364012803c0303400c00c5040c0c4006000c082d680e43d41d0b000003400c103030400f901002000c2080a401690034032400e03103111448001452540d400c0400c0042c5140306d00f42100f5110040401080386032655000e44017900e5014484a211221241c0100c00510100e0380c0a880d42c03144400344000e00000521600125185038203a4122071641062030050f25040c0c0702e250740c007854071036101c9841442d00c8003070101d03800145000340c500341c2440b10241c9003c1254890040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 426301492 1250 426300242 426300263
    0x50d1d0d0609030809150a020f04090501080c0102060112020109171f150501020c030706030b03030c010903050403021509091b120108011b080115080a0f020a020124181116 75
    0x6254000c25440d502c505c0020003031041c401142c00119100501070b1540340401c5e0040f0703404841e076203600103030740c0030b0251003600300308541e50b0702040c82c0c0d50002c00b4142030140c0661000452021a1410a000b115406031540c903070302864410002c6030440020f07030101d100e0161050740c20308800c1a80c20000b52050800380441e404c040d840d41f80f6964032040d4062815540000c0019109480202c1c80a04a5529040016074244401d010901f50b1103141d0030b6507121351814403950100740d00311001c0c009480c002c1d140180d4000650410107032a224103088150300145500014800ea420721006840e5078650040d03c40c10000300c459810b005202c01e80012801781d45400780c0f0448210751000401e00070b0b9085c80c002d16031b5490f040e078818105001214010800c502c60000034a01401034006040040c08010110b6560089010081c020a01d900210b021a0384040c03208882c00030301c9034084280e03214840201090320355402002d005226004020100820070f10481c80e50390071802814150502401c1003d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 426302742 1250 426301492 426301511
    0x1c06080706020118060e1623091e0712060b09040b0d020d030e01020c0d03051209030c10050a1b0f110312070c050a081c18050d1d0d06 59
    0x40c14a801078000301c085a241c00e1040d1003094100f0b81c058140d981220b0002011456840e10038140b0300d0001c03182180c0301c20080300040520710420882803510305010405d01d851315071020003402e884180c6c0e040c1e42914011240e8004007901c804035582201d0907061044425101102c004c06a82c4154000c0314040c01c04140c0e05200e040c236002d490304010040300c0c0190380c4085035000400308504008003a0802400901c0300703211b07900070020002c060740c0050020030034003814540245158000c1005034120104600400d01c204000070580f1140943c0c0005086516020a100001400010300030300314591103e03000c00c664000c06221411059040d80c844014070aa2000544070100c1400d60603403c3d8000c2062180c41800400c0140d0082c0083c030342030781c1d4a81c0d01d0810f60b107001c050440160404e034000640782004030383c204018200501d1103005014044100821952008000c0b2000d4065004800000707600c1e41314180c116240b075180f02c260664408400f0200d030540318620411100c80e50340e8815003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 426303992 1250 426302742 426302759
    0x10603051e181e010b090402011403100e040f06151503020c0c04020a0206040314030405060a020711040509010c0f020115060e01020708030316090b03060109060f020f1b280510051c06 80
    0x28980440580c5e5046c15810543e000800c0c1d44100c400950070140040003045c4004c2c1c0a0749901d008080c2c480744405103041c1800c041400c01e0102c1d00c01c03a0094601103150101090100c11602290024660390031818111103094000e58030000c1c0c405410b0051101d550380c56551403005e070283c0e8107554010000b43c50b02c0d1a0181c005010315007203c05004090003000005900081e8295100e402884056124480c078a0118a55000400d400768424200810894802e40552200740c5c2c8060f190f0742c9010441c03e19100703a00f295980740080a00d404040707000c2c00154001c0070340d50821f181c184101c69196130340e640303a181550010307030301200120f04c0d03003000b13002c41075001c642140903000500b401807550500b540003900480b200d01c5128144507415003c1800c8600078018403112030384d020242c9009a140c003004024412203124454441c080c400c100e83c13040c15035003070120524002d201416080605100401510400c1000e5080401a04000b54221001300008000ca8040c507007801042050526040d0f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 426305242 1250 426303992 426304001
    0x30c01021902060132090a0902091f03021e060705010609060b120402131803050403050d030605214b03180a030602040303050a0305010603051e181e01 66
    0x6011035110b60014802148601400c000b0000c0f14210b42890254024204800184a82a85c1e0380402d0701420000d8028403030301f255000070301c00c0750780001d0760303407504441d0554501e0584040440c1703070b1000302480141030801000d801c10b403041d4101c002d102101400104a680081c000b200d059464240802290540b402a880a800e40b4450b06040c4040d05c0040140000b0081000c1d104101104050210600e903610000241c0b500c10301240328521a420050a56030007480110b0349441500c015070f401511a02c101800c0d00c600624080f040004481c00b04166004020000400d0250320061140c100c105280c0d400030a1211000030b50031207500c81880582c000c403654030300c0e40c1400225070008101001c01282d00000c502d000951402d08a030003c60035020450704002d0600d480014040141500103000c0e18101c03040380c1d010300c5540e0700d805044050f90400e45812401c00520a25a14a50622080550b21410701803034501c1440c0591044c80c83c0081841d05c030801c0da4603244001412503403e010307 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 426306492 1250 426305242 426305287
    0xe0a021210140f180711190b06040203010e010b0a050c07060c021c0803010506132319030f03032301030b090f03090a0b07050a05010606080a230c0c0c03030c0102 71
    0x4400d008501c500004c00d0a500c5020102c0341005400ca00080141c1d0140000c0104188103030704031020002110b0700c05040303100d4013034180c503107900d103c0c0060301c0c0785001d0080b01e060b90b0b10260000d02591030400002445d8000c19100703814000b0501c088141c0310020014000204215514441d24900600601c607481588140c84140b05443c03e030a08042524681141e04540095420a5942e904030040c5100d00c4441c0e080b1901c2040f00300070407c0c003c00c14048031201402e0445481c540f00454080c29252b55006e40b00041a01109003100d0000c64000c0d8004a030b0380d1300e80e24507001086005151020008003d8004444039a548801c1c812038481c1082114a012210700042d86070943c0000001e111404601c615038141400050350000c214007480180b45803039200f0024440c59480e0107020705070180403108038003441d24000d0f000d50a02e940c49150990b544502070341420300e445480c01c80c9155400280c44000c0c40c400d8090704442518200010410000004001600e84ad219000380140c0140c2c3d80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 426307742 1250 426306492 426306499
    0x50103050708070e19050a090e01050105060c0a120c0b0709033507050f03030702060a0c1b0f0804080a230703050303160e121f0203010f0e0a02121014 66
    0x608203c0f00540011504004400442e1074000c540c0c0032040d0601c4404640c1c100c1e503044404564001003841440c0c0008104059103030003406583c0c0c803002807005e41e00800703030315690540c8501000c10101d81100340505845200c2e140c404981e03a020f403610842640180d4140d000203c1040040084c001c4220b1456401e8520040680d9000c90b844a03034043e8003c00c01c10303840d50b81400240c01301040300c1000100700101950003a02d8480ca0003030030180d00c840b41100c82c0c1000c01d0402055098080c8200300105404904919401d1498029240c1140072601c142084480301410000420003590800000035041c0c49002c48100038085c508595003211002e410314070a075030003a901400001e00110980fa441030722400c0591969281707d10440701480704114883d00200e15803c1d103001c21002040030100940d8410590b5a5211a88205801c9100134420403120590214080c8001914414143d8000c81940405402d002074550400c0d05000103403500000e142c02000204484440c012038894200c07402c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 426308992 1250 426307742 426307757
    0x1005012102010e061917090d0909090302073503070804030f1b0f06080921090d0b0a06051014070809120f01150b03090a06020f070605100501030507 65
    0x200c40c00100c500040c00000d042c000c2081c0c5465080e144e4406440641001c0640b020317004008100140104008103040b801030840e080014120200002c0e68100c1d010140c1e0300c40324190720380543c0200070909a601141140604580003929980306101c08019040113102040040b4113080e00348800d01036540600d120350401e004510100300b440040d101141d0308040d0010041c0c2641c58031404608a0043c802c24110701c00304085501e5565040031001d40350a1f4071881c81944516286550319510b08410b81a80b01b21003075400034400540300039103114100500811200c01680e03540c8143d480c0c007100c0359003007681d0f01c110401881c03920340310846c9074041d282081848040201801c25861144000c0640503000000d49900181c44843c09288910501e505039041c070380340d280c50702e8084c000403440840c40701800c00d80031502d6102d1404032405108648010a01c000d15a034402003e03400c1048251075490040c050240494820b000e2240310b541840181c61166060070300150403280060180020003812 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 426310242 1250 426308992 426309029
    0x90414091009020a0510050c0a05100c08060d1e080c1c090b041a070f0f020906040c0503061002030405090103060b010327140f010f0b1507030f1409040e100501 70
    0x106042c4406a400c03d403007640d018020140181c60074824a9846c0629100340012641400404950140c40401100f400e01c1f420002433012a0361080a650080d0b101100c002550000b5005006205016004451960540107503807161303203a0784c00035000e41140f81c003d0f2220903030805202000c140f14407400d0802081d0b00b800c1c407031f546071680980d00401d0070401402c003282c2f101c20201000c0d01d492580c0b10040d020304014901c0c2c16109946041c0080380581031010215441e441d250090187c242c0c160358a1500310766034001005020001a81101c080d808100004222174542c0311655019600035040407500c00c0e00d40d000102154804900c00c2120414a000b01c0102c01c10428200005504591040c1500001c50400ca00f009003041c50501158a4000b4075560007405803c0002070303080c2119803441240351000c201615216500c80100007508030558611414045d2150f405540d18180300c080c18009040c9c040340445880c1200b0741c00c1980035000b102000b980b00c0c003585014110b0390b21814880e021 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 426311492 1250 426310242 426310249
    0xa05160515030c0304051507050a031b020c09130f050d27151e2304050102031204170417010c03200a1209080301030b010605070f030e0609041409100902 67
    0x2c041c2880d05070000c00404030301404020408454840240c1500140e90300301507401410940c8950895004642052840c000c070100907228900b82c695150040c0031454610303001c01c0500100101200c1c100501545942d01041c010f400c240c64807482040144600303501120042c20150145a01c54200c1040343c41e8241540781d0740d100507040b50b0b041100034104c09605e40042c0c440300d5450000001d140542d401d48081190312041c0d0402a0f2005010b40725010300e260101c2c0510f200d2401218096403007041044885608142501d5100c1e000d404124220b10465003581d45680c0141e000342c100d1904010402402075081c460403c3c0a0003a0404211458031104609010034a05400486020012800309031040c001d014640d00d00451110400a1400c60314041000703800070300050740e124412400206100f40548103c4d030109401041034444813515540845100a03105286500242c06002e10251501c44d07000c1d4140e40001c00d680d002251a00014441c54041340740c4107030302c01c0c80c200803110b00541c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 426312742 1250 426311492 426311497
    0x6030317091e1f24030f1e050d0309060605220e1501090c020609030708040b070606030812150109061707090308070b06031504020f090a0e0a05160515 66
    0x4442015882c4841c0d15a096410041408100344202d01110303540c080448a5034000358103000790100082d01ea143d1011a482e55144c14000206812110070545020490b009005e9642402020a444015603a44c1d01c03e400e01c29035542c080b020a440318115000c111517406020081c00c0c042e5211560b00c02030107182c903c40300352199a283e0165a4a1104003017800500c44440c0f800d809070306020065a6900c2140010817031402d003013005007d0400030424940012044804285d040f11149050900704004070303420364070036a4211501c50341c540e800000140e216018059446010721604151701c0c0c40c1003003219884840401d6410040e0130710050100342d4101410601d100c04070241520b407583e40039015210014aa000933146004c082200c2c010814880d541c107110740f0080d410383e802c84498814000943c8010303a030003540300750154904203880c01d01700000e0394801c0c40315030042064058071040c1410004514000e40e075540103003000300380c880703007201251000b03101c02e96000c130b0786c0210f221036101c1e2030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 426313992 1250 426312742 426312763
    0x506090412030b04110c010e010b0901090c02010b04110705010507020f100b0406030f05100e011125140708070b0a020a020d0c05210d140d0c031803030603031709 71
    0xc49207046038100300c0d0301c290301c0107262100c0508100038042103107803101015000614180c080750700385560100c00840c18018030400c40c0303000e04080096401c1449800180a2124a010440d940c0703000070b40c11a07881d405500486100987c2156480b0b00c1420b02600b0340d08010400c4d41954043c1c0000018180300003041c0071024154100014903028800c00100a0030075584054020826a22580207004010a901d04c1d0301252900410480c101e620026013030316079503001d080002e80c0500c81c8403400c441d5000004c060060f80c160400c80d0304400d66600c0c3c800d655000103007205620000c010703c1507420800c4450040c1200d42e80650810111000c020f60391b01307282c800240107030305103256102002110305103a000380034020030000c09001080d01035440b0b1140f02e403018000f4850350342510015402b80848041955219004c00e04e0403540b109520301520081c14050101075494415441000c000340528030700714840d640201c0c4c00b910b9414005c25024500c000c491243c50458140803030a14001010b5250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 426315242 1250 426313992 426314003
    0x170c090d0507031a060a09111c0e07080304090f15170a080a12050112020108041b05060d02040515030c120c1b0a0b0109060b0315060c0f15010905060904 67
    0x210055841c00707038200344180d0b10081039190000040440101880b0402e845280241d03504040c00340d65560050683d16100c00001c0c180108114000007200100c2e2040c401d10b01c5200c0100740b526080d00800e103000311760390107218943c101103404d11045050340248503071721441901c280070080c009020308040602a1180b44603540100d0746002040300306102800da0250400f4125407119003494000d8031510b01464a0440030707192400105051124401c80d074601780d0107030746082c400d03030b81c43d03031600c034461000032601042941d07591001545940e41c0000340469140180c025850313914042c00d02011000c4008100121241407003004869120041901c0b40000c10601181903601c844c5104402481480c0e1a203c50400e401c0400c240d03d40e00240b1440e80da4030407a0340c0b5100d40e9941e1014011107040e80503200b051042040403a60700304800203c080030310b80092039945810012002d0030301e001d442105200907230700700b262403540140c400032000e40100517941c01070040e4074003130000804059004000500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 426316492 1250 426315242 426315259
    0x130305070f110103050a0e070510031401090203010302181909110a030510051303270504020c1b01080705072a06020d140f03131104060609030605090f07050909150106030507170c09 79
    0x15864826000910944c9881010314580cdd6100c6004030003952003400180e00950b2a0b10442c10003840d58480c89106040a0003200b214400d000c503680058603503c4001e0750240085c1e03070354884c0d95a80719601801148190010306103081802034000030345000600100f0200e56070841640802d4020481d054008140d1100030200003000800c0e085a1070b031604601c0c0c1003840800c065500760b07000a080284940c003402141c0304140188011255141d0807600300b80004c206104140000c0e6184116611075150951042c04d038100b110304200400645610442c0164000d41c403c0c500c03d900f150540d40e055029040e841d01e001030b440c050040b1480058605104603001943c402c003032010b4040c001c841403000520030300840359110001056a001400165081494000440ea803803a00058840b00a400c1d940500605441d00c0304021281c0f00003032050107240941e2904020300020008003a001e04010740300041c5c1ca0400c590001c010715250880d0307183e6550000305004912400109491a0709002c49000c071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 426317742 1250 426316492 426316519
    0x80c090406111809060f0a05040e0705090f0403110304030804180f09060501081006081005311703240f13090218040308130305070f110103050a0e0705 66
    0x1004010062000c20960000b0988599102206120840c6480101c4000e5071641341c1c10100702c001b9940c4400594004050001042981400d800609a040081d000c0d142555034400c00300e2004402180c0c24581c0021040c1044101900304000c52030a2080c1c030011410700d81181e80b154401c0c071540c0128036603402c0c0a007441000b036815420108915240a400b032040010f00e15040014120a000f10344075400741040002c400301842c880c21040301d0820f030007401000c06001e4500c0040001403c031281d450005115461002500601081e005500c0750040765004150304240041d003041442e42610088104144000032001d10305980204000d0102484c4040c103120004909080703101d03096800007451240311038070f480307958040641e2900a440d88100c502e44aa080000001e080b600140415031000205500740280e940600c0d400e8400d04210b03141070000e4441d20340c0900710001c201c5880c44149403c400c0745d41d0502903240c00004400c424003060405004180d142c1080380070b440d000d0411070800c030b07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 426318992 1250 426317742 426317753
    0x41406090d050a0b07080601030e1b041d060915040209162309091602071e05060711030c0a1413020d020309030301061b02010905010302031e07050c100501080c0904 72
    0x101807a541c80011901d10394054502071000744030884403403020a2403000064801d5000e4061102004541000b41005070224245a0701360040c016416030441ea50720751206003001d05500200c51800c40b035004000c50320342214240d2030040c0216400480324000014080186c5503540c0c0650400030300c0b0900c3e02c0c012150f103c100c0b600b00c4008500500700381d0302040074401c800079000a01c0d511405440308803c030b40c2da024503c2c1d01501c1048030b18006a0145c4030400500640000c05440052540d40c004800f036a40c81c006032103a04120001d03110103c40b8100d00c02246802c10020014000640712102500e140c68070481a44600384800c174010040701c00d803c1100346850f41101c0c0c1c4010003041c21901c9042c681070495486c0c00074060000485c20407102000700042d844862003402d54140d5665400c1410503004402a4001510000000300f07440010040e6a0b010382c9111f20946969035002e450300301040800b03180900194040503954548001844a804082500940e0010684510005403600c2c5040c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 426320242 1250 426318992 426319009
    0x1d010311030a0902150d150506030412080c0d0914191203110c06040c170601030c14010302070507031b0f081009150c0f030e030c0705040f0603080d02041a04140609 72
    0x500400b03050021b402c0040852035400b001c2e03040b4540c500100784580300c505011207488191000b40c920300c2c001e19405581031240c9441a408031111514030b09106035000a0001d803888d01008070f0f84c0c00c00750304042c80d8500c000c0003220b800c07a01c40c2881f801014056103e0100c0c282c6029848030030103840748c00c010041403401040313813210440c0c04200d130301da4070701400d00c0d1040e46094002c90808810083e24003403424800900385041c0d0350000354134051185428030b040c01c40c004000c845130506400344000700101d402070040400031405803032108000701140900507a00c2030290400700382e000d600e4500b4090b1801c00180d00f114200300c640c00007040d01407070519406034142510301d003d41509118003002d006511815484241000d610300b8011f10704541496901c0340519104249182d105400070004be1030f06e60004803101000d1900024590344a448090759507014507400321851342c001078100a031001410040d403448001220a038103181c00c1050703c112003580079965502c40d00700440c0c0411503540c1e0502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 426321492 1250 426320242 426320269
    0x4030f2f01091415061012090f060f1d0106081914070801020d0b0a0806060112110a02060103021009080d0809010b0907180e10030807080f04061d010311030a0902 71
    0x100e0416003c8200340e15a80c0365041c0f43d48542c0f44a00c1c4000c62201e04085441c4250b080454a8201c81500c906072250020807101c60142e41c0009030700d1920000c18554404d8424041c2c4001c008a0940c601904098103443c03030000480340b580c5450020000007a000c01c10308500841203504152568490034404072180c84070040040754090300000040c01141580140703080003400f10107001a00840d4100300b040c003454030681071139410060005e2407562188410400340e8809200c00540e01d9030010050685401804291016910900050041d4900b048120810035420324243c9010303400c2c85032280c0c80300440c0c401d20301800039020204580100a402c07110f01944d02900d84100d034038252000a000050900c41c00c81405c01d96000031595120400700248a09841402070030f4051941d80c8a045a0b4001207040c0c034419810b001001090451a00030310081101703942e0030740c080130418400da0b074028403c40e00e9030601d0300d42040020040741400c1501e45c80a18102c000030100030700d00224086054218 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 426322742 1250 426321492 426321503
    0xf1605130902030a23011802091e1203030709180606270e070507231902031c090e0a020306030c06090409060914070f1404051b0f0304030f2f0109 64
    0xc1c0449102c1121a0742d0604859105101b0684c2002009148049200d127891036038001001c85501d070b400c2d0803c00c0041410007009032100054841c0e02800d03c0c15a08183d41990001e13103d0402003018076540c40413a041c01c10008030030081680340c1140075020b19101820b507400080b821580c1407828460030241c1c8024100300c54110642d10b4614002070150b03100d900110b986901052190792140222115446940076500045c20004441c00c106941a021480202d0b407501c05c418255406a440180d2100c80880f0364684c2450b05003400300380d801d400030003000ba000040c814400c00103103035000aa4110701c2c45043c0e6001e50380380c09503004240504801080900407504090200c0e041080304100b2513460210141502c500c0740c0c0707a07040302c25488124030800003103108940d41445546002d9102d01d40140000c640d5458070414103941354010b411484245c1a1003034003004000c141750300000e140c242e84003103203024521611642c050189842a58540041100980c5084002d900007540003005064001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 426323992 1250 426322742 426322781
    0x32d120403080615090117130807060603110319080307270603180c0b0c03190201020304020a0509070507060f1805031306030501031502070206070b0f1605130902030a 73
    0x600703010b0803407a01911024040c0ea0030003d20b2030b201040a05075685c40d441652030803503880407040c2c0c01842c10703000b5007004144a031003800080010f01440080c801503114a42c0420101c0c91820301750756411101c2543c90003504062182070217105005802441036074407030b456645940354030000720307600329400300ca10b80721500695103240d203c542100e000c000c80b83c040e54140400c003418198680c80c1285010000c0410a514070144011316020010f0685007141c001140d0808100c105090204140c2550400150b5800410300c400e50402100b0f05029000075079203000c440c103003a04020303c0b5204000018040c1c3c4d40d10300c0c0c3d0151103031068128444068800e8003000098569003021500ea51007003078080d800c1c0f1480e14002503081c0c000d0003428100c03078020311b00c80c0d107d0541d100400065481700000320380c040b200300312410015188952481c02400780d40746c00303901858502c0c045860079255407040307418050280018000c0801d0f900d20202034502c81c0e0300250701ca803a1254903070f02820420400072001c1101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 426325242 1250 426323992 426324001
    0x180a09060903020f0c010306080d030216020a032009071d040b1203040f1a0403120201020705060c0c010e0f030306010e0d1a070206150d031407021f020f032d12 70
    0x1d80013401e42e03600d1041e188030b1000c0f00c006404440c401e120b9400984c20403009000003030702030303409442010502c9100b0040926258000340080110b6001143c0c11305004a144100101e490f40400e040714044d200b0282a003807080e006001614400303581407241420440c4004161503c0d08410007424000e013072403082c61480c2d0300880d2130350418001c444000ca03401d0b40004030381000c1e022090b0241c684115240c80e190454589034008410580f47c0800c1d59000c000d080c000413000c1101030301c01d000069105860b00084c86403070303081d5510303840f41141c4c60384012031101c182030f00070046980150007402c1001e495855400803641ca0382d24860b0181c05a5036030381020708484405007045204a8480d403d5603031990703400e6106032010342d10310003003038204500b035800300002805001e0500428111200c281c1c2004040c0e8001801352540d80011800c0540c1c03800b00c10000394040140d0010b00c84510301860801205607000c464185494807002c60094031b600400380c2d24100b003000c44410b1401c080b03440c00715241 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 426326492 1250 426325242 426325247
    0x120c0902360f030114041b0308030106090303140a0801053a03080106020a0c03120e030109051606030902010c0b0a110c030a090f030317060103060f0305010b0f060306180a09060903 79
    0x14514280c05907140742c45203000d620b810b1060055601c10382c0480111030715940c641c40e826030310300b004000c2002000740c0d021021410500207103000f00901d5481c03012071829803400629241008134a403c03460018400f0b1b041c03403030300000b10a054a40a460152000000068000c05040c40d000d0381e036034030b490100c820104c1c24142c50304004070a000381c40b00451079a136020200c2e80e801500d400a00021131410307041c000240005941da000825900c0e06850001c1c54400090071181010421038807584600550311000e0302002030000144003e007030401c20910380d0340003e4030190190200070300320101000040d82c240e00a070f01030804003c02454140d240c03d44d01e24865626440b0100081c0400c00105c400206111000c1c181800e8a906544084a100380900654641c000103031441c1c0c107141d183c0300e01150729070000380c100004500810011603404454020f0011940300c000e4214040d03070040042208a403110004c0c2c0c0d90a07440311803205411354031090040014581920700030101c40c1441a80300c14076030f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 426327742 1250 426326492 426326587
    0x10219050a0b090c01020624090f10060f0509060f0f040b280e06030402031e03070303110903070303080406150311030105090604030915021006030605010609120c0902 73
    0x24880c0b6060511600ca011035a680e40b401142e0060050b44080c00240c8581d481c4120740541c086282030031803170391280500040c5001d03c01c0f01c040745201c0c9400c0c100a02c0415601c40d50f0018012400c1031844040444001070080c41680091030154100090032440701d0b404070215002d90503540759160302c0c0c5480d0400d608035070f446411501811040c40d9030159480038480003004110360705031140c40d00c100d80e2a003401103540000b40166898000c00941c400ea074510000303090201e403103000c06103507903614510700601200c0c925411076030520740900c90804141c800045410039603406081403050b07a0380354501032019000801c8201c07200c02c0120300c000208001b070307842c090b1606002c8000b80106d6960a005950710101294090300188450710300700aa00b0703900103007070228040c0344152400000c2d4a041401541c04980c01103d8079595a0700401c0050390140048bc09421018600040e580194580c0203451109001e010842640002e501164452205c0f205a070000344900356503105441140701d00428 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 426328992 1250 426327742 426327763
    0x1050111070e0c07031e12091509050d0329011107150903020109051e0907020321060108011203050f0d06052107050a0b07110103180c2105030a030b01021905 69
    0x241b046514141c0381c41000a1004102d6441d581d004181c1400d50144c4040d0940c039806850401c4000b0080c1c0032424240100300443c0d004a0003880782080c43c40c1d00904881d03d2100184c5002405642c8145520001414000c81c05017468035484c0e0407041c600450500070141d000c00b0008041040198010303410501381c20499000742c84400d2040d0340d4000f884500e40c1400c0e16040e42520b02002c6690610f03042c040c0b1a0071016502c100c03414100c01c002a01d44c209901c24824682203441c0003000060340c1e001180d40e015010300c0c09901c96000c1d2903a406000c43c080c1805840000102148058081080354010002010000c208854030240b841c0f2080d100031414003200e000f03000d00304c0007107402d04103030b0084001c03200c0240c16245004001c0e1100020034101e410420704241d2185940403a0740e8150f040d1700d10b006e0003050305211440c9040d05200c40c0072420140c4100c0c20115880301c40c040f41c40482901c803038904c90700340840c4d4130340d400c00102e00300a0300c0c0c4445118118010348580c14420001000100e0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 426330242 1250 426328992 426328997
    0x403080c03010803160305130603020705010c050f120a14010e0405010c020708070b03090102040909120e040b0609010f09050901140901051f0c1110030b130504030801050111070e0c0703 81
    0x840d00c9184a204881c4001d0003203192550080000d628940041005001c05901a10b080d0381461022600c01c000c4480300c1e400980029000728881007801000c0c410200c60b40014209a45002590301c05111140a90000d82540b0a405030000b0742c6407081e40c101000103000314400c00798542e10b07038601c103408840035503064a09600e460690300380c0900000d00041a694200b0040c03841524008620210b07500040c88004595000e000c0000c07080d145005086000e0305c10418240340e8a143d20740103242004d0501140d21441c28900c0c910140c0d194041201d000b07000a1901a400c40000030080d00c442c2e117680e10003030300001400000101d4811882031881001d408480010007a44d88104100e0000100080002c0d40c04c540c003403940d00319000d204480c8100788140c1e1005040c02c640c0d8002441c1e009010820f04c00b19444245841035441c20129040748501c402801704054200740c3c4001b00901d5050145605004c051203140130410707000c002080041112700789000c81882d0000c80080c45030003400c0100c02 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 426331492 1250 426330242 426330257
    0x50d050c1608060610051c0605030d080c1c0b0904200f0901061803290a0519020c0c0d05010c1b170d0f05040308040b010902040501090b0a0e180403 65
    0x1d4810001e418001120b00300002046140c1340c003c100700d94001401c01c074030103102c420005101040508412140c2040940c030000440615041c1854241444403e1207410001c4410410000034200003d86025100c80c407480b0090a19074003d61004203d0851410b40c0702030044c00308801c026a12101c2060050000c00c4104615106400d0002c880780d245610b90f8010110742c01446614460b0b6600280190440301d100206175917500c46d124220320700c95a44c40c07110144c4c00310701040c00700c440303103950003448801007000685000c840e81d10746c0e03649180d41d0b41c04d019000100a001e4035000c200240c0340310390080c842404401a440c0042c02031082c0c111120100e007131204400140305044580c06c1c51250000c100840045111881d038290b81c0c8075420762640c080e070796240003030760004034800c2d00c1c0b06510a88035400380b41843c0c1403410411105910550754140104010300c01c03640e02100b050210b4840c1004941c079400420000e030f50020000d0030540e040594001410740303007926070840a000d076000c0c0d2a8040f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 426332742 1250 426331492 426331513
    0xf060801060914041131060c0b0a0908040b0c06060603091504030e12012903060a0522030e12031e0d090203010e0307060b04090f03120912030914030a02190609050d050c 74
    0x4201b82064480d40c00071616407115031000c0781400b410380340c0c01140a000001c2d00c400e036649485558206030880d03400000c010071204000581048803d40001085031170506510700064031680c3d904900f60100000040ca802090400d409616121859200100f0f10704103000c403508128007c080250040b6850426401881c0c181c0020155038a03601d18050302903c2580c2d0f914407207002801000e00144101140100c1710304070f4140c0c606008080900c256924400480d083d420040000c070b500e0310400058104100d1102440903a0b1005900642102485611040c481541c1002450200d4021b9095404c1402034280c107a400700081c10258880d803402c0144592480c14841115071040008024041e00c45184020a01540c600d00d071411060002041940e801d80d10b1070114409840c2d214046510f40341c001041106850b9002d007400f0816004509242c541d0780700a580d2103041c044a0003d444e1910910140303e0141c000d407513005c2c0c004d01165101c03c01c80c0402012544410348515507409503a403400c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 426333992 1250 426332742 426332827
    0x801050402070807080f0d021c140708070f0c050703110310020906030c0c01090c031103070b07080405010305090709020406020d080901050403080601030b0d0501150f0608010609140411 81
    0xe0307422980280700c942c20901d0658039159164420b20034036141500034801f51305500060b00003450865400403462104000f604402400d4442112801c1d000e0191041000700d032075403025141c0c0c0d01c5140780c684503025103000807007654003106001000c2c0141c059044040144140c3c07480c02a0354034000c3c0c040701c1400104045030000c0b8001c0c400304a40c0b0441c10000302d284404086d02404206003011300014517003000e40c0da5100341030341c01c0c0e05c21680b0300c1103044051030910f014841c000c020b01c1c01608907840d120f49603550f00780520883c00740704c0c145030780c8078007041e180d800030042c1c08094110440d0840d66240c03198070280d56a45428030540015640b04c000880451040c060a4041c40e41a140c0100503143c0c400150080d00104032001c0d04004e0464205010410900640703c07142c6442d0014801c01d800e10b011500c40d40b035107400c01000c0c450703090010011035a008031144111011070380b50200c00c21010000501a0140d088400881100031540d04100342800c072880c60a4a4040d50102c038400070b201c01e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 426335242 1250 426333992 426333997
    0x906010f05010801060c031d0d0c05030105070509030309040c0207030c080708011b05070f0623010806090607080112020a0902040b0d0f06121716121b11100e0604150801050402 77
    0x1440f0000304210070b030b140040d02030081104100c044035041d1a80d040a000840c402c5c03272540e0f005442c1a100d00d58100101d09081c41400c1e0030012500c1c1041c40c10f445c660210b6640d20428004c603001fa40c2e987d070040030440c800c0c0104400345511440d43c400f003583c1c40034850b94410a9001d203981070b52802a04000c0e0801e843e00d0210622a50b4a070103003407580c1a00c40c07955a00c1007003c10782d0740d07603107400c03480301300207a03408907101404021192668694140100381d0b10f80b443c01040c6404951108007405041c5410140080c11201003224051500c0880d1000c15100003050f400034155a002140104071110000040d040c4124286d2040211082619580f0300751040f9208259110345480582008200b11002035504494551b1203246410764401c02c02400740c5000106441c0028481d240c052103991001c01c0c11034841d000c40c4243d85190340b603140c000b0003403003500f4001c0c45440b00001482d900f034012074a0040540e0020310f02500c81ea07960030710074001e00e0200c1e4a100010341010010900d0700d8107200303 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 426336492 1250 426335242 426335249
    0x20903390d11040e010e070f0f12080a1803060b0f04200708070c140a0e010b1c0e0f0f0f01110a030b01090803161e0308240303030906010f05010801 65
    0x2103010100d110b41c48028111000c00c600b0783c3c00c1521506040705a403004d006807048035040c10000c00d0310f145469583d424207007880d0084480c05c5124001000448410848002500e81089600d41c0c1ca005100c4107954040c12020360883c501000400002130240b00da226013210310003500d032000f0403080e034402c1200316001c05100c90514a005282c1c05001c4d0074460107054080e10486200b8680002500c0c0c03c65014007a900c40c10b5440c0c0d01518116903404e01300340c020010820406520015410110a018036002d081e48020341521200607044c0c1c16036503074110500c558201000c1e0340c0f51180034844140c0750041400e060741035114084090641e41d405124040362032143c485480e0519107a00303405c60240c101c81000310f0420180314404508400140028002c440c0c01c4c05041150003034910b080b640342c084500c0d9100c0d09240b00710100ac04a5086080703941d20060310000e003c104403601000856684012100315050701c001710410900400001d513107030590f000c40c0f0f10050071aa0b00c4c001160401424003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 426337742 1250 426336492 426336499
    0x40e1602061602030702060408010203011e0608010b07020126060418110607030c15050601020c0103090222020d020f09030105090f030d231612060b040506070602090339 74
    0x100010301080b40703851902181d00561050782d1500540780c0002d091500305030408025079500000402140c20810401ba10101c500b021202d5910300d410405850118144903daa6809000402c9011a840758030740014011001050001c59044041e00101d0744404403031301c50159145c00b40100d649034440480020340756202c4c503411a00d103407510901c102074100140071414450780c1c211102c002024131300d0700d00e00e9450200c0000380317600c0c00c1c00009140040c404030b09418540303800d0444002d622028094101d81090704102e005100c0c1055480300207210b841042d1440c5031005c80c3c00100c4803c40b41c010540d660f000c400030300140c1c40341000035884580c840394801003039000b00300314441c8031059004003030700c20079110b44201c002c045041070b0b5054007811103a400f502c1c103160b200e01c0d41d55500401c1c9000c6031a0b00d02800c00406040c0340c15070065200d1801250720590010940004100b03450701211051071002e0b041c4d43c0c00303002c0001c014004152503c40f404403c00410302214080103078074985050307003c004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 426338992 1250 426337742 426337753
    0x501050307091e0e0d0e0a0303050d0e0a1407050a0f0e010312020a02040614130506010f050f0f1b0f061302102d0f21020307170408040e1602 62
    0x41c80b0034000c01c1e400210402c21001c43d43d0814040400d403250744480103140d4040c01800700541402400380388903e1115110348842074040c40402c1c4e00c54165030400e1050079000903407d250310354240c50010019402044000c58905001081c4004503c9004407402680c900b48100d80340c0000b84600c110038000c0c1c0c50100180001000418002e2403440340b08281070060b1210b404e9950041800e607001a017101c005d041c411042041c1c02e043c000002c10350700f004100c04208074200380000901c01120034002c541001008501c2c0c3c01050000302c00c549400811403040c681d1070800c4012034481d84052100080a4080c80341d900030050004100c0c81e214481c00300c0302000b059100c0d82006206000c400800b03080100002036140d006400e10f071456160300301081400c00a00c4c81640040c80c00c0d07991034040081101014090008100c0c45040c5420b0071820b417005138a81e96202e2007225034100850ad01c0710388485e068180414091960700500c01d840c0c400040b010240d580c281c168410400c00a42100168000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 426340242 1250 426338992 426338999
    0x5060606090a03140a1a070c0201080a0e0102221509051e04090303091407030c0504050c0f070620040605030a09060e030f030907050901080a0b090c18040606090501050307 75
    0xc8401030010000c01001021026100d845031400010500d0310303a0080d510003040300d81401140070701c014080c20602400041454983d00c01869804d08210007414460814086010311900303411494501d11804021529040014004040c080380c100c0c03a83e000100782c034004603a002c039203081000b00403c1615807100311442d1509202003048102200403404001e0b8500c2e203019603850244010082c040c1d1340100c0c0200309820030011404449004d4ac580303910450702000082e0310004042e04813202180c3c0010550795081407142c441c401c2c428071283d05c0300c0024103401040242c0d40301d0301d00310203446281003110741d4071069086188141e02415012070f0042c400100c0c0002c0a40044502920880c000b060490081418619507004403800d10716004002c800c00003890002c1060000030310080f10b10f1511545052069500c8089540700540342c0711034100051a00c0d14200400800d505020f01011009441181503201e0500300790b40454800e801c052000507000d001c2c0c01820b0594070010083c0220304d28 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 426341492 1250 426340242 426340249
    0x207081b0105041a1803030301211a010303050406080a0b130f06050a0603020c0f010207030f0c0f170316080601020c1e190e0714030103060e0a061d0c0a03050606 71
    0x1003400580c1000310400c00400d8140c640204801603400c442e600f540c4a4a0b1030044841d01d02d281c25995000380d10a00041004020f8a040caa40314075446100b01056030480c18154401850303d500c040d1070400303400c00001050f81c800c004000311281c603501e0804546034000784000313030f03170803609820b0340455842100710203841c407030303002c445c903001c034100d0000c0d100d40d4400c04201e1040c015808103001c01c0c1d0110707500181160910080c804020500002c61400760181ea01420203018814507034200441c803031000381003203030b40004210039a4006074600300350050043c2c0d0740d9055104442e9101c04171464000142c0e054024050640900c0050300904a10003910050000e004840c042440c414607040d580f0308003036210600c0300c04c52408100800700d242c50070500504800d8001a00c000d040280310008601c0c03420125040d01e0540c0c1d0b00500c041185030400420615028900c60050700d80383c58240b04040c030182080901240101c0c42050b07505504200c401c12004101c81c1c030000e481d079084078001503160b14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 426342742 1250 426341492 426341533
    0x1406190603050c120109150b100e0901030f0203070b041e0509040b0a0507090909081e040e06041104170109050601080c0904170c030705010b1305090d141c0b10020708 73
    0x130b00000000802210680342c01c0c103c9109200c564503c42d9440c3e051960504080b0b0b104114a08a8100500c0340100c1c4c10110340100014032000d030410070351b00140d074119038090000340e0003000145243c0740c5441c1c41d14100c402c0d1600308901680030001c0ea410024090802407115440740741c1114510311140d80e00c26003000036010007018007040203c0c256010510403c1c07442404050340c050001c03252596000150141010580120340c21400c0003070004106892500005552101041d64003040c0b0344200b03100101c15015540008041c18a45d400c2217009101c1503104183c900e000300b085460301d903a5030624945807010503070101d4000b50b103400010041072400b0004116023411103c2180b501c0b1000741c0450030350b0804607086038181d440d80c0080101d880c00c51503c60342200068410031150400452465540740384602200c103204468501c01082c02c544402e40700c0d2021600c0e03070316000c0c02040031600c004101100c1c3c29840784411000001e84a4070001d0002c055414010080c8195003c0d49074000024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 426343992 1250 426342742 426342769
    0x909062a03061513030b010f0e161101090204050118050a06120b04112814060a0f0903060219030f14064b120303010b07030306031406190603050c 64
    0x20030f800c0003120351010140d82030500541c01041c181d4015410031040305a03c54460380184c0310001c0701f0080c07110783d10b4903528040d0003101c00e090045036115801900341c05010a100e001c2e40c001c0c81d1000014500d540e00e010f200600c080300c081002256141400d03441100c06a0050075050001c1c8018080003921090300683c2060280f550074441101c5400000c88000442c1d0904120207003000705e05c0140144101d18002501c0c4d41030f05880000c440d10301150042c000d44001c601008200c0c075441c61000c1c0218109000b443d003083d07041d50394034405581c03c6800080502e58400003494031401c80f030b01041030f20900d000781c04041d03044202034440604000302c00d034084100c0c6a0f10103c0c00307000c4e0001108644281007407981c01d0701040786200340443c0070341c2c611020360415010341d408110300381366900003000f00c90542d001714101c0d946074509070904400802e5141c1000700801c1c20f0104113001e10000003000e40c418021071742004a1303410004d03103a60a4480d5480024002d49c07001800700b5480c5080540f20703116 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 426345242 1250 426343992 426344029
    0xa032001060504020403140d08041121070305011505060304020f040903110105070306090501080a0309060f02030f120105090709030c05010503130b0a1d01140a0f0b0909062a0306 78
    0x7a5282d0700040d003240d001d50f10484074035580300e11078000c0e00428032501a512840e4185081d0a20301510b0781d0481c400780c142c40074440c544040a079140c400c80c040c03000403c00320303040c1120840c948030300d8854001c1c04060076116240c4101407001400345042d4088900c150303400351907414240703000e00a0101901030b10320201c0500000c80c0718004204003d128507481801940d0f804103500c2d2401200800326031041c0c20112045d00481e40c0b6001107500610118100c8030030b8030340440f00e070022400490941c0152000760101000000b40018041e180000e914182c5004440548241e29020390a540810503840011300c0f201a08804100d658041c001660303101081142c1f800b54400690344102e1015021185041c02d540d6640542000f50032801d0072503046a00703000204183c22400a80f03030310b400c80c003c01003541251902068605044982c00c10b011070940609042d007a0b00303100c040c458680c0400c654007100100c20724402c03040314100101c243d08505100b0784551441d10750101303202d410071100202100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 426346492 1250 426345242 426345251
    0x6090e0715020f06190c03020304020d140f0f010203010e150d0f05120408031c110403060b0a030813060f020a02090103030309060b03030c0706020f010605220e0601060e030c030a032001 81
    0xd07610f030611840b849407458210318a810b842c000c1841044548071100c003010180f0500400c001612412144124a80c000c9214015640020045c520b007540b5918404076600a094080000c02c1054010354107940903000380d0407c65554203485000395102080e41540004231038044404641c40e10410150340d80900d06980c8200310f0943c0320f0851354055400002e403039100084418200031440c071181150400c40d00180105003402c1e81c0d42c81c0900413804007070000b6548071840d048a42c0c5040314800116840044c9a84801001c20840c0703c405480c45160041110100410142d601c08a01c04642d164020941101c41e401c41d10114000c040e00c010403512a80e850940c071302d107076030100041d08880b0442d00c0100407490030060024101105480c400c20310781e0401c41c081c8041ea480c0c00c1c140030706502203031013040b03040c8108400c41d0181c00380419543d110b0069000104040e540710600308003001050b000c840211303102406045e5100701e1000003400140007130311807560100c45171060b40f40351110f0000204 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 426347742 1250 426346492 426346513
    0x90901060b0301120b090d1d0109080a080a0f090605031803090d0b06180105090708070210140601200615120102040e0a060e01030506010510030204090c08060406090e071502 76
    0x56802a000203c41d889280141c4c41040418600c1540c0034130380e20050711a500150300003134070607601035040c800003480002400e4181c0c2d1049500304000c4c0714140071030f0a02002401c0c9108642c0c452442000010900c2d070b00c1441580c011951442180d00d1580c0349440c60b41c8072501c0040c101c0b44040b80602d54042000800c4050b81c0e03102d100c0c0380302405100c81411505085042000444040c0d110340c0005950380300400056841181da154081003d00f000a05603649010403070400c40440c28000401c1d140520b244c01d4608445001803052100b80c071403c1d000102a0310114143d507248814002c10741c014030010702c01440c401500c2c8641e10b0064030060b00242e03419032690a9070026048188840c0c4014200201c0c13001c0d42c000d0074010105600c44d6541541151600b07920b40005015250084101421200c41588603504580091490500421002d4034400d002403460390700340c1d5182d20450070a81c000c5003c2d08688501c5040c10b08460091072000e203072241131040e03552a1007280c002e6004000808 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 426348992 1250 426347742 426347759
    0x806010b0a1d06031e06010e400b040507050708070201031104081509070f0513021612080601020f010b0f0d05030f0406020601082503021915030905010b0301050603070509090106 78
    0x40d40207120450000201c00d0700b01c0b0750481c0e80c00c0b0040406c0d041044070000142181c9441120380c0c103900b50048502d140070748904100444c11075150b06445140c28040c0c8107070f46a4141c0c0d101c2281954111420b03c09901d4200040352580107401d0040e054500401c12500190300070703805202c0074000114942e0401c1d80c0c07035002a0a0400c226020004000300c0030030044550000d01c02078001d4990030031508846070070f00d000314092042105031401d009a0000d8106146940811442c540d42d43c0411221481c0b07410590040400c2000d460090140c811a146000c08103410700500059540c040c01013441300d8004820890800002031301902ca03408108082281260600300602c05804d054004001a51500f0b04841c500300e612010301500c086000d9000c2031007203042101c0300489804490780521964082c0301c1544806072944407900d024070410700d0008064047d08006401e6005030020408002a00306050136588100d803655810382044c501406146420f101d41034208082d00000503400d9142e1101 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 426350242 1250 426348992 426348997
    0x5060703061e030b011503060503010c0f030506090f07031e06271109130e0633030d110703050604030c0c0b090a060f02030d061e0806010b0a1d06 64
    0x22400080d0300c0d03078400e1100521504607545040c1100141a40c00ca2450326510100c21041c01035200741c3c400d00030b0b400b1415110b03070010303400750000800800c4038003080540603201101c0840424042410700c00010014507154140602c54090344420f07441e1550350040c21401041c0513880c64101002c40c001c00740348092144181409010344940e6010120b00001e09180300100e00315041c440c050030820745d14410b4140c40c0507522145420341c1ca6803a04184c80e908079028003140345511415100d2242084034040442c2c0d01a00001c6039080c01d4a03150030482240f6040041c4080495095402084205031240c800c1907041a21400d141c1502c900e141c50b91b54890400c40103680540c0020b41d60b0821078140286800f9440062042d02141c0c2d15010350300010130f165040c180b0920301401040c025005c0742900074021550380d030990b150100070043d11a82c9007003030b4070506824800d1140f01c2440102c1d480000240f228181c4d40c41d8044641400c0f14504210380c4d19040c6c85241c1201841c900310400c06840780c001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 426351492 1250 426350242 426350251
    0x6020309030418020406030e031309090f08070b01060f0201060602151b0a0207080c0a080d0810080d021c080408160602210609150a03022112070308010506340506 71
    0x3c0150740d4a203848001025910003124049094200b0070840003007680c025000c0342210074200010418404a042c02c40003840010389c003400c42200041d002040000390a00705041e41c5090b03c407181a9034542c07908030b00726540c07805401c0150344210320192400d40d1040030306602c040c10110b00e14540f01c658081200c0c9030048002c103c0580d010701d8007401040010b200480e5200000d42d84001c1c01440d085200c0d0f84d83d64104114000c2c40b42d82000304100035080b60640001c0c1150400301d80207501c0c4007000035647e44181c001c00a40c10003140e4007a004520a030010343c0a40e400c5220b50b400c215905550318074841219104075116582081070300b11140e0004211800c1d8081000c16a0007884c101d801e121075450700806641c4003001d0641400380d26920210320000b92501640d108100308145050104642d25100621010f4810001d400b607140b840140140f4002e403082d520003650f66603420074040c460045440c5245a00b020034001007114410b00f00705141c04a008281c0d1060402903101e00d401c0500984 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 426352742 1250 426351492 426351539
    0xb061306030302151f0b0309010e06070908060603060f07120f050f0103020f03060402360c030103140304080a0f0201051c0b030c0604120201051b1501062a060203090304 74
    0x285410401400c1580a5002d4103017105c64818418240071a5500b044030302a0f0210700c0c0012011a101c100e0961100940c50020411260503007018840903210528900c202c2c4284e02c501380021740716041c00300720113025400d0b03905040125140d0b840180c2da004c105e6500c42201c545d803460f8440d20704401e03004950081c6a040c410480950460050151400707070f901d1001d000351b00a01c00d2000603140c0551444203000a810500e402d00028020100d114884003200c1c10510403070024403100107903e000842c1241c1c4200c010039070500042c0c18590f1a4000c52191840941080d2807100c04110f90112101407203105140c820700c0c100310028804695485104c00e014084d6032400e01c5521070070100070341d521014046405904141c68140c4c0784c480074612100003410850040b481d800e0304038100101c1c03480240158203a619141d1000888007181c2824840d031400a010309a4010044500740d1a0142c4903440c00c890030100e0083c0d0b114031001e584040c05800c86844200400600e1070001d500c145080301e40c55 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 426353992 1250 426352742 426352753
    0xf2d0703061d010b010903080a030f0f020a110d0f0f141201030c0503010204290705060103200d030519020c03030a050c060106030b09041104060306110a030c05160b061306030302 78
    0x600c0b681035400c084060ba111580c981400b041050303030807030421403c89a0050715035a070b80c414441c044010b810784d0101410b4660a0a980510b47c900a4001c1d0910044650b55a02030602c6021020750701c0e440300d00140c003c1004842403c406511499207002c0d5500241400c4481a130785010101941c0e00c42e030150503c0072810300042c020044c0e02d240040003031004400a504190800c7c1100c4034960701080040a85140c00341c003000c200d240541601c0b02540c02c4829256650383d02d04220001c10f0741c05034104003240c0038001d060351a241140d107204a480d01030756900c0c2044c0d04000d5180c65041c050581806520601404000560b01040206105201f9655040d203413044a0841460100306800050601d820400c0020558862040c000c0d4000d82004ca10750009910002040007032000c1c1d080608030a0515a082c4642c500031001451202c01c103580070010003141502c00c131081d005070201e10707a013160190308079400718828044503030300980014011482226040d030701c0000c0b10720961048000d40c212 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 426355242 1250 426353992 426354011
    0xc0109020a0504061809110411030109180308130c0f260c060304170706020406030615020f1c02190b040516050109030b07051c0209120f2d070306 64
    0xa44590401841c1c00c3d034080c0280d500300f014070010703007426500129130a96102c41690900c1054140c0090038100507108100400b07405220000ea94000d0060310042030600c0c0008003072040b8030b81c000e07a900350582d4810015403203c1600c62180700c14144162928500a05d01061900e480001030004000d88035400d6100c9840340d1040c0d54180481114001780d0700800c40450b09501c440c4100e0fa4800d9204929450340d17280d040c492443c47c0500040681503510101e40490f0b91b42c2c05522503401e4441c00220341e44440e80c41c0d0001ca03540c002007175600001d6084410625040c1602282520a01c002030042d1041c0e6203040840340301900b0108000c1c0c61101c2e4050a100c00d00c141030112103c0015200b161900c05420321001905c881d41d07520004051b07841360000038540030f10070006d0762409c408001c0c2840b0072413805a13101020390882103405101e1440038034003080510b000900742d4140600740f0080c0513400c0c00806000c0958201c4c1c14a40140e42800c440029990740502045018510407040010304525 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 426356492 1250 426355242 426355249
    0xb100e040c231c06080a150b360f0a05090a030f050a05042607050409210e0603040b1b091809030903010c0c05010b0a0f120501020f0c010902 62
    0x81075540801480580a22140e20820301e060911511040b0000c0c1995088802410400003226080c210407540c682140401c4041c0045200c022481c0104420355801c2d0305a0001000c803400018500d0740101c4441a110021610301300c0100034096046200e042034031181d29034846c065040b070308041c4455000c03007080b4002c11588951a04000c20100501440342540e50150044030882054020f0280110307801281e24800d2088a011303200d400c07229140040c11100c0410703900a0141c00c4916801002d4000c1954101841003480140d00070714030440c81c1c14140741a44a00d80141812400c010f0a0540c1c00300c5134848100550240f481501400c074245404046942c110081104950b01c80c5001c0240480c2c55a81078803130602c502203240b19484e152a6000e41d2807843c85034244c031607095420605007012080d00804920241e0780030700001d11001d541842003080810003801a0350b200804175100f07116003d65192803071441c600c82c800051420444140003103d0b500403408103840d80e91136040d24411803d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 426357742 1250 426356492 426356501
    0xb0303040e010f1706040b09010f09080c0d0e010e19080d2d12050702070e1003050c0f10050c0309090c1c0c08011205100c020d0f090f0e0a0b100e04 65
    0x2251359072819101c00c0c848215203400c4041c0c0041e0060030b906c03012400c0c03090207500502c90207402c4074041000d1207441c03a00140f59008041800d110307010713032840f800f031481c01140c0400030424140d5a000b000420041085081d1031100b04010250b10408404030724503000b0040c0140340b041c5ea88070074034064040302c050308070701000d03440b9525006a00850000319a40180c851840d800d079401c0081010368403046c04a00d86003a42e03002c403e1070990b0301e0a000014101c0c41c060300640b400380d0306584100c5040d03000d02c0020b51101002d6a00030602d8904064860322a001800c1100204015617103000c005000003850b506040e14800b003001e800148a80300d103078034800c00c0c20300807181c45010f0000e001c220a0140c0003031414860440c220104204410420030184144001004070320010490484c1941c0025030b202c14030032219011407400f401101c3c1040c0034460100c125000c10240f040c0484c00d00104d030041c400054910000c80d07481e01c0c100c00c1156500c20f00500040c2c041d030b68000022581d03008100584 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 426358992 1250 426357742 426357749
    0x2010915091709011202160507032012060f0705041e2d030206030a020d09060506091806150604090c0c0507091a040b0f12150601080f06040f0b0303040e010f 69
    0x2c20007008400c250780d80214111050150320800103854190300440d020313507110342581c001c06d0342c01041004170400605100304400100c0b0302d0b002c05c2e00000340c1c1050010324400541c8100040e8030080c0018058400b100c0c3c0d1035408545482c100e41440d55618068886500080c0607140701d00e070307082c0c051207184000e01d9410341202d6250026103486c2c42c40000341c241d2400070300010380160000030004041d41c07407a4040703e0b40306510090821407901a410000000d1806407805441800c440001c0345085041c603030980c3c4100380000280c44a070b15400801c0c1081c5c204200d2071a080002800009070042c801d2240d5601012191034a41d0341400524000b27081030340940200c010340e442c0101c042c3c00c2e80c0c00810500d05040c0309607000904501200c0019540a00440105610094081216547c60f401180c81034000484c000349902076110300c0019a800301040741c1405d90f5026000004d40b05143c50740203075035079051003000082d018400d80007003400c42d842074100042e14441d29004005051035140e000c0c005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 426360242 1250 426358992 426359033
    0x2030316030c0806010e220209120604200a03120315060f020706140f0424020c01050a08100902040b040e0c0903030a0f09080a03030b010e031b100201091509 69
    0x180b20114018000d801c014040c24104140c600d01005e5503211400c01001030360126002800382c10001a402019500c011015030140250038004901d0120006045e030160341d01041c3d810300b550116440c0c81013036108500d6241d0000004134004003266680040300c618811a13030300400c00300700c01d0300030b0b0130440800d0784000c040005001c042404103902041e100140c911b075107040c902c0c0e00740700b0f1401801c0380183e065040540b00c0005001410700c03028803054690002007840b120711420b4524090740c03101e500115040c0800c03c02c00c800d00210b4070610a03c2d621098988861000c99102d1200c05d040347c0150300203840b5180e0009051081c0300445010319440020020303240d1401c0c00c0f020101e900ca004d1071707840d8410302c0f48002c0285402400743c0b005d80301408070b071800c5406030582c0e420001c01420b07199500301d0100e15410421100360501140310b1059840a2540e0b040c0664140207100c202802c034a00c01d0304556803003407030340001201081526954100c0100110b1071442500b441d070040002e41520b01c85 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 426361492 1250 426360242 426360251
    0x80d1b0c0203190302070e0705190201090b0c0705150702010c1107080307231b010e0d02090115020307060e06100b0c0606060313021305150a080714011106070203031603 74
    0x142d0740001c070343c00d1142c451581e400c0584010f107001e0740350840365008540d801228504002003030f0341c024094540680b1000316202d5021041c2c409a080300d90469005e403a00e0a100005040c0d042701c10b0042803082d10420031503150950045c500080f80d03605845460041c1d4440440c0c8503540c0e400141801121089001360403e18030f4115403560b01d218880009040c2c0c5034510b03031640151224100320700c990703441405071101d03a04140e146040d004c02c180107290100c0c1d4000031240e40c40c00d0803480200f9480c0e0203807080e140c1c0d03400c10001c1100b941e41c000d521401c62100b00684000211940902d194220f0504020700542c10702140481380c0040130307042a800e25609000d00c1e03540703040c0011104d81152094580f40d030390f1380b60840801c0c006001e20303101940007040c0c1888000b002d4039940c04a480307098131141d000d51000d024410010701707518920500c0c42c190b210f81010702900c0242c5100c2c0649050504010100040507400f550070440112924005604007004200c015284921072100c5154603240802 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 426362742 1250 426361492 426361517
    0x9050108190209040203010b0604030606091401050d021302090a09060503010c02060c070303050c13030308070e04060f063501080f031201060f1205150a14060a08090a080d1b 76
    0x801c8400e400c0041c0c840c101e90030101c3e00355207082d4011041500f0103810641c0d1181c40382004405010a4492000003e24100b9035400c00d03084114a00c1c1a1040240b110350804546d4003005240300c107202d500c1003503603400c200c06000d40d0b540300d04010080501745000300328245040109821104020440c07400d5401c4101041555001c0303104842015501d8240001c1d00c0d100da9514241500515070b9072203415040d00c4010040c035400c218813500c01c803099510388603c021000e05100c00c1d41e0251103804d2503045408018809103003e4600c5108180743c05a03610040016071004807042c00120060300c40d400314040042c0104803060003920754460030000110314000385400e000300490381c144141002c202d0100d1021891501c11156015003c200704401d1080d81041c08410000c0815001c00512600c50b0301c800045003011404482409000200f040341003604244080e1904a802003407a191800795244010000d66800051301700381ca94104002504d407002035840c112030b50710b00f5500c4184805001d009 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 426363992 1250 426362742 426362773
    0x30b0a081e1b060f040308030a050a0e070b0a2a260301031a1305072d080706080907080a0f022106070f230306040c0f050406050f0408011509050108 65
    0x3030807a074409583c055070780d0700720300c406003070b18041c0d50002030450700c000061100740326080c3c0009018030880c500c100b08000005040580c0d90950340f084002c96102840a21980340c06250401221843c200345c0360304012060111001100382c48504032410301280c10303800c01c685a03000f42002a85118902a0314550560302c8d0440c02c52075646248908501080000b003030601e00c050326845281e44007080ba84460388070b03c00c0038034030180c415641014080040b0f2007010482031030300f0042110000700113841c002c0d003011000c480c426001400c0d01c100d44120700000409600c20018105803031301544142c441c92070f49104100d4401120407050f50030610300c5514443c81e10000c1015500000f80d0708040c800b0101001c0151614035002c1c1d040044007001c0110350314040307a071100461107620100c4003001910700246041c2c400d2103200104d5000030b4400d00c018003c1901501c02404c0e0001c014016904140d95080c3d99803e40e80c03000c8100010351070701c64003080b103114036000307035405414403001801c003003480841e14 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 426365242 1250 426363992 426364033
    0x160201020c2d0a05031914180105070209091b012c030a0f0804080607090332030c0a140109031e140408010207030905060c0c06030a1409150702070311010f030b0a081e 73
    0x340b85100c0f8282448d000c41e03002d542103c95840c3d02424000541c0b0b04200001c3e1940c3c100460f065103c0c10800782444250b102c5c0003500c12180c6081003420745440780e84041054412150441a018800c0054460200303445144803a04540b10700419613503681072101d9103060444c090001403c1c07103010442800026030310a12403001100c0803000c07605400030240e07810070026136224045002c3c080014480e800e014081805101580103001102c1d5000d00d40c26018200c6014a4000d0009000b0090700d0320400d0700c5981000011481c1d10305084c14198103101d06816a000ba0f10180300c0da9400144401059044003403070008007011a041c0303050400d407980b8181c840481426440c0310b244000300290415404d030b4084240032810310b05140a0f4500720702d109030b880c41524405c0070509108400540040c1c40002c001c000e51740d01141d101060b4401c00010741e10552280050820316880307485400c0036490b4070b80404002c02201c8020300402072084e0407001c0c2c80069000719159600300d000501310b2072012030302d03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 426366492 1250 426365242 426365257
    0x7060203071505100f090b0306100e01032405100e0609070504090b010912030203040321021207021f02030406141303080906040b0304060203160201020c2d0a05031914 73
    0x81000c1d59418281c108081541e040452910441d0b034001c6466038091707107e01c100706000d8080342c2e41501e50013206081ca119034031a00000c6140c510041c0002000e50709062881d0241d808581c1d95039440203410403e4400032551001301820f240c108008000e0a017036500d42110003074840c1c690904103a00d00030450320460090085440d182c82c013688a0b0391094030f44900404514100c0d00c01d07005070b07140c02522030f4014801541d8080c80380c03205072928007001111001c15084e54000300307103034803010b102c0244980022100741c1c3d00100c60036808400d14a444910030001d602a405190344600303200015180d00c0300000e07010201501403064001c0440d09120481c180e0390000c0e40e450302c860089000441501c81d42d000741c01c0000000c03042c0030410030690055401407102c1c0c120188004915a4120b0803400383c0c2e00c411181c1e2b80030410890244e0010700b00759074003080c204641900d42c040c204c0000c4c076002c0ca4140480c0d00340c0c4000b800401000c1183d44d108000c44052401000702d0400100c2054907014291 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 426367742 1250 426366492 426366533
    0x902030c010305090f0601080c010305070207060e130204030b0f0f0c0403050c0d2604080c090c09120106090908071104060e01060311041502100605060a140304050f0a080406020706020307 82
    0x9004c04d07070008082003038000040d81c0c04100c3c0c1c000d60b1510f0070345486200454509020074200808100f009001049803c04d448039540c6a0180c8843c0808100c2c079a111401200380381e031360822001c008680840c42540c4512840005403000c1c0c20f1405a0a064800040002c3c880b44030a0200b800000c802103182406148201c134200c5030030381c007424201e540c00c10704104015017110058506200341140c0015008852901c81560fa40160490070311680c08801c580100003c6020480040700e850101d608000360501100001a0740342c036030700d000d011a6048441038136601c1003c550802000001c03803e103e0f100000744d5082c48168500402c00d8882e0030107002c0c402c01e1507102c03139036050054002c05c1500d006008540310424017903454000a07444075840351080181c141402d02c00306250131f0850441d80900841c0c0d40e10103003400503403001039050f0006402101ea9000701003100020400c1080400c108600840e441c640d654a84040645030130742c558404011341d0801d00070000405d461250360b1000c1d64090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 426368992 1250 426367742 426367751
    0x705061c0b0415080a15050c0d0504110603150f0604060503060603070c050715120e060c0711060409140a09031b021906030510090504110d030c0b1510030902030c0103 73
    0x40141c0f0b802e0000318041000d250703000903007100c001503248000e4090301e00e030024804440000c10640b101100c403203807072000030805140c00e03a440380e00c6030758454001c103200303070080c42000000b0b0465441074440d001c080420200d900340c00c3c6007551841400d0841180d105d450f280c94840c0c09400e5010041c005440780c200480011341581c001c801403480c0070741c07240a07a03c3d000e40318129030400030f100c441c00710b0004805000c40c00701402d0b140301c0c010200e1480070040c15030b9622040100b0095100403401c8034449803030650f5000c0d0b529544081d00c080d0606035004608074081100e60749250307100516582a030b50801e400b10000c650450a691407140705000c0c40d1400e14050f0001c02c0c0e40c900e20f205035245d01e140c04030001034001e078180d20080c040c03c0d03440d4a001000d96120382e01000e44c0d101740d8011b09a048203003120388051078580c0b181c0080f0340c4a400d108500741120b8540742e2501d90125500c01c220700541262142c9842d0503001d40603200e480742001c10802000d900840d3380d0740901e04a01d030515984 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 426370242 1250 426368992 426369011
    0x605030109020a09051b03100303120c091406040f0801090203010c0f0903030815120c01020f0706050906221404060609030b06040b01120c020a050f071a0d0b0a12050705061c 76
    0x6c160803101c0f117940c0380c20300c907959040c801b014000c58101484103030002000b41000710410f0210b8080c3c10704241c890359611b01d1850070100d00148550000d002c1c51380c020300820001404944e1000031600604620000164400381d80c0141030954942410510410015243d40e1601640101d01142525014034000341d090751000f40e44080740d582c04400701d03030000402a036094039540c0000c461019100a03800d80711200c00c6080c03200d554640320f0081c000400c0050004220034100a0043c0242c100704054500340621944104000000307190484004440c54151240c041d05190140c600105a24070348001c44902e503450303c0d40304050240170309200e50f80300c03201d01c0c1e99a0702c5504090320003c0c907850304010b000350003036001c2d6644ac140cbc60125128011259074003101240403030031004503002e00420070348003201401c4800d80342d40406810b200050303550400380c0c16a02e5004080010306404011818100072904001b0314103c42948281d100c3c00d000c00140100c48034004945050020014010422240 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 426371492 1250 426370242 426370261
    0x1e03120403020102071a0a2a0e0a050d0506040c150e0d03090902031306150803030609040c0b0a090e090601030206191202190809190b0402060705060f07030605030109020a0905 77
    0x201640945440d203007a010090720a001b825107401021216000c2280070703062007149540700c111000c07001c3d41404a224401c0110f01401c0055081c103401811000190b0300d620004101540300c26040d9010780c03041d81004200141500b2107000b410030382d0000c940b4802c002c100101041c00740380c2c50a01510341031540c1300405008a450348040c0041e9201503441e131400b03002040480c0980e481c2602c4080c14043c0d048548283c4403800000d5941d9174024500d959600b605000c5140000342040341c0c00b4200007400652b040d619005010564610346d140c00d9124544030403802d90314805403001c181c9410507001000180d81300400c0f28201642c0349a079804907a00c120003607a4410240021103511800042c090185004903113401c00700c840591502100e60310b03068030041e070300e840340d84415100c0b81c04150103801095020301c405030702c14801041186003040f107a40c0c80307043c030506480410245400300309015200c0c0d054010000948015402006104041d0700085c006180c14403483c5a1a503590000c00e0310080c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 426372742 1250 426371492 426371497
    0x503060f010e13140a06060c050304420f0305130b18030309010609052a03041e0302100c110a30020a110111030706111b0604051e03120403020102 64
    0x444075400700b0080da00004004aa070704c08540000c441880d200f000b00d1210b00a5000d404c4840e08030700114200f9082109040b610a400c0c480785294030855010740b01c0c4403180744082d41032869210358500e80048107400103480005600051030615040c01c080024089070740208891141d04000c401040f80c4505031a803652400984409000740000800c000080c041504444110782c2d41002c00c00c825903442c8155407080000101071603001c05a9501030843c401c03244051600175000b418840d4a0345d6401c4140c845110030240100c1c090f801001c0d0f104250f000d00d11070186644568103010404a08200700c56484034181403008000c09601d60754118002804405411500040d42d50391910344040340010b543d071590240100d8084103000060103095104201c03164880c90350600640c10300c00c1e1a0390b190b0240c20303060701003a034505050100054007049601306403401c200702d0300602078508013400d200e41400f2403a101e145c0003104a00440000260020880300601c203009008146e5440341c0c0f178100d02a2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 426373992 1250 426372742 426372769
    0x30b060a0c030f50030c0d060509010608040c0f05010507141203040c080c0d0c060c15051f08010504020f0910050402070605160311030105010302070206070209090c100503060f010e 79
    0xc4513884000d8161a0040403001818000140000141d400301148210707840540c041c0704000210034004607109580c40000b4050740c040200b80031030f4141d241c1010500c0e0780c0090348007000180d1001c0c01e220038804040c0c59071014160a601d44240e00c1d0030080041e056106407140205106101045020080b00500003500056840343c2510399905181c1070900c00d41401d400f03018194005c1b511328000302d1600700c90080071300d6401801d012085280c07160a0f07500d000403010660f40045142c000700304810451281900c0b40c0000c0780c042010114580c0e45c4260038110390010142c903031500c3d0900003d6900c0c400341c0300d4588001c5594400d0340d61000d0501450860990180f9040741c0081070f40030400c00d10f900040e216846c0786503107429080202d0f600300c1c245c0d103c082010202c01401c000500c481e501c20780003040040e00280034949006203e50200325050400c50b0480116080b640c1d07420958907101084220052f01c92400d5811400c281000445940d8108400d50600510008c0c406080d100c003400780042 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 426375242 1250 426373992 426374027
    0x70c05030708030c0f07060e01050a02210a0e060f0d09050307170909070507020a03060b0a03140102030a15030b0a1e020703030902030712080f0309071205010b01030b060a0c030f 78
    0xc03542c0c0d8103140d83d882d0410b00e03101e441070207a890000d004910004040c0215034095540401c840300350760040d1030561020503801c0031400303003003885a50004403240202803182044080c951340c0803245002484840e40f181c00b2881140e040280b1181404a802519000022071f100060701b00c0041c07074100d140d0302c5842401071540c5690225a071030b100e00d100c041c0c4403101041d81e211a0598450a08842510680b000254040c0c00c0c40c1092000ca121584242c903050000b502d00014251a608c414501740a800030010840c0e40010401c075041050703000342940e422100150031103007801c3d41c0d00c41d031440038028a00f009003541c031103509104102440c80511525842d840c00c6640d02500c4c10000c000d4443c09100782d00038400d075500010040c035640c00003001141c201e450706080855038038250000341d1000c0c10300c44080c4507642003c1084540b00c02c1004545104000000705520064009801d40b251850458030641e424005244400c0e00100350610242d454600005084081070b4241c50b052400280d2461 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 426376492 1250 426375242 426375253
    0xf06100807240519031b0c0f150b06040b0c0c03071208090604030c0312021c0f0e18070206010905010f03080a0e010309061d06090c10050310031205071a040201020c06070c0503 77
    0xa1a82c250380070305010100c0303102075010402c8003441541c211084950052031036050062a00205145448031030070160b150f0b0b400f194124000c0009440c4d40c200d40c000001503740003e0a207504102000f103900f440b082923000d010514075085102641500c1400064108800024001c00b107940e40000c45000c0d41d0701001c86c03800280c490510f40050400701303000b08051b108003c2000c800c031001c40608200d41955981e00c2c0c00d00c080010080b102d10030807400807604550b8410700c0742c01a0000d0291184269443c6d4000c152540c50210107405445060b4807004c60301401e680d042c000308081400b00e40b0b0384151030030b02441014040c0012001081940c0d0083c01c01841d041c000360b1000c0c0404200b52144000404940c2c250700c80807422512040403421180d4002d1280070700000d0540030350080d40d03104101c00038078a480c5039a0740713a00084990040e15000090700c0040ea03001006017aa01c0710061145070f009c00c0d049858141c1c0040d503079105002e409440b400004c21700e5010000a24100000792070050140c0d0f1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 426377742 1250 426376492 426376537
    0x506090c0f0d020a031407020c0901231206060a1401120c02030d06091a04062303240105010f0503040302120d090c03060204060305061005040e070c050f061008072405 73
    0x18005e1003919606e840f401441b1700418601440040c0e01c05004000034012005a442c03c3d50380c002c6407080303899018542c8149800c40d030543d901e2141403484140703400054015031500700104a840d030140e8000c0c00f0500060110407030f01e40d034043e40d038920360202c215002583c8888041c081e0b04d5401401c0c809a801800d220000c140c21603950001c03110710001c0c012801001071940104416603903140a445101c15503c4511880302d241420301e00240003000d0291405802d0242c0460820b803028010400490a0a40100701659100c0c02440343e90f8442d1a04509500f003d5800940f5000100c3e280c00c021100454a001c030314010f54005441550320240a440081e40d03843c11401a42251040c640440d1078440062142c1c100704078540303110822a50f0700c0d45003d00b0a540840c3c920f4019001c0b104109140b243c1d5400a4010007020204526810080c205482e242880c041c2e96541d90b08020ba4039040f8210420920070031000d6000040c119a01d5504a8580c01c4411511806605911810a500c2000c00b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 426378992 1250 426377742 426377747
    0x303090803161202090102250e010f03030f030e0613080f1201090c0201022803150b070b0c0901021e0a050d0504060909050423011103190501090506090c0f0d020a 71
    0x1e0000543c48000d103608a21800500328001d1045080c0540c00c000080380c400008150b0040c0c26000c3d840350a80d03065103411440e00e80310003d8103c039a400c14114024401e15401c87c1d0001c0c071600c0507182c24022489084241512940b0103010341c0706099088400714100852641035a0407030017040c66480d140c4a0007200565111000e200d0164081e1a10300110720007072060003201e0800c010b54442c40c40b15174113019032803140c184180122003019a1000e4110782e0411101d02c0100504400201d26201d854506100b2151200500002010203042106058590300440c04e64250075424070100480700900d982c5908005950800503c00e014040e000b003881c40c2c1200242080e55401e581d8403040a1300c440010007118000d550150074950310300d616200d08520b8426a1044854240c000308284d11928100c00c4140c00644030304d291885041d1280715116001d1091a0051440e16000d11140c20b105000c40e503511406441a524040005200300400d00c01404841c2c4002d070b4600219a10400407900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 426380242 1250 426378992 426379021
    0x10122d1103101403010f0e011d070b07140a062912070501120b062a012c160e060f04050103080f13030c06050d05070f090501051b031209011b020d0c0303090803 70
    0xb0a9a05209c039204c49030310500010b0010305450700120014039011a54031400910320b01c096821000b44550804817000400600805410740ca80005c150002d29036001d01c1d081009444840310b02a100f1503008514042e40051814100c0e4005c0c240325210130490b4840c0d0010740040140d203904070000007100015461b022854010310043e003003117480d000070070040d0b85081e92808549100051441007081554142e90403662601105100c2258441c203605100100c03d071540d54002030303c54945e03600f004518102800310200319078080b90100110340c11035a50794200d000c1c042001d0301d10100403c101e6041c061030303021000a190840400c058056803868010180d611002403d00003604080c003003414240986c100d80c0d401e116035190b030820241040e0045030a9000114604190361014803020790554051000300b2204803849104002031030300f900c0440c251130300c400c0140c46040d2000c95110b40343c0d60101b19840e03401e001d482d1400d1120b0140c1403c40280288200140400e14000180b2000011140d030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 426381492 1250 426380242 426380261
    0x70c170c010b0334030b070210061d040f0f0209090708101a01110313090605040605090903180414010608160206010510122d1103101403010f0e01 64
    0x24050120759a05040c1c03682c038802c011100c010001005400b00e0304005202d45131402064201541807a80d030f89071104e02210561b0800c001d03170066010300403024014044e0310050001c000009201401d114441100c0c000c00500c00f418071524182480200401105491071581d001031014401e4108542e80540305c032502c2c480c1c08124070078030485030b19414140c0119482c103400c06003c855401101c40056641512141c0c940d44140401c011041c0c001c800020b4400141c000400009891410701051008540e0190000ca04c5030010408100c266070b000000c542e803408080d208484564645800b00f000780c030080d0f0321080e03c250014000702e003840e840385103207100399000c59519020124102084e0b071511400e0041b6500f080c1c906103524040b9014640c030b6151070341503080000e080c1851050080700c5030400300c012a00110141001b0a90a0703250141e00481c84207401e405182d410496695440008644070700800d10440c2c0c10300c0c07041350303800b940f02c00904405a6028410b41000c00d034428000c065180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 426382742 1250 426381492 426381517
    0x1d1606030c140702091b0a170105090906190209030118150603021f020c030a1112030307120c02100501090609060b07020303030c070f1703041203090c0608070c17 71
    0x700312218280c0b040e90020205519200c41ea89400c1c0c064081c060800001401340002d1094248041c00e9400d17014001c00440c2030590380e0b100d40160302a5a0569108107900207417007440f40034240075554802250700c580200001c000c214103a1030701c502600c0030340035400c0748603419442c0c4000f0030740885900106c1d0854902c80c0c0300030b503200c140141180b402c40f001400041d402a51115410710341508541c5203c80000240c011940004448030010340b5040032440103e4802e42c40310041416428170004e120203294500c0055821490007040c01045503907240034811700d99444541e0394207814003d000c604240d54010700144000d42e10794044001030f100501c034460f071f805e141080025000307040209513084140e000380910718540341d40c8046110b940240790152119006040c4800004c1c00550f4400e07482489030344899104c2c50181016945560140e480000703141c18441c0d1200000d001070151426504281800000d9032107480c0202c81d04110208020300e440203201240c414001c0c1074004c3c1420780c0241 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 426383992 1250 426382742 426382751
    0x4032c010e0409030e0112060302030304120204050c04060e0f0607050d08061002030f09060f040e010306141003120f0201180503040302031c0801030807020d08070b0a05010e0709091d160603 83
    0x20070a120480e494000042c000801410403400258072030341d4140c0a98103800d07804100035403030341c0001c3e0540d40641d212804003000000c075441181004e000b4694440b003545012030409141a40140c180c50501e004c00703105503007110456035159106c0040c0c40819811004803490440d00030340140c501d881c01d80b2030070700c10f549805406140d14400400c8070006600050400c5c00c2450300c03018002c0d1034201443d0041481018000450341c620380790310140c000c5018480c0032400039248a030780903442d000a4010300d0a80c008050034008288905018040c0400ca4070f1300c5031394202462400c034010310441c01504031204483d000c20051050000240050300c1c002c40030fa540014000e091080303214035140041c40450902d0b401000491502c0018140160024003511400480f80d55512440c0e80f048034200d07a1096240184050f24150b4800c03507003d01460b004c12001e5050590018055800e07a109840445880d5070044000d0381c204182c0329507600c0003d0842c2c0b005070900ca0b05108510780c82c0107245c0042d240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 426385242 1250 426383992 426384017
    0xb1f030c080907152105040507030b1003020603040305031302030106060f110601080715020307050a0f12020d050d0c0e060a0819051003060c0e0a0803030a1d0606040504032c01 77
    0xb003402c200b2185000c15a001d001031540c802d48240d03000c1003201001900741750038a0400d111600440e40f02c3ca128601070580315007189080b03403d41501910080c0c070240b1a45080c40180c40b460200e83c0c010b40c140c1000c40d1282d448404910401d444002e009402d5401d262000031481d4101480c000c0d000d0291702d0781da030f008161950581d95401d00344180350207680701441c1040328024680d0b1054009046205603850800152241803605036109001c42d04190744140f5401801580000311038411000d1019004401001070300510302e008101c0481500303a510346425080600440c401041910007804403a1143e810344030107448200d0440b1110080d0400e140c142141500034032070b85106882840c408070300345085440d110b0040558106c0b407424041318610400d41e80e510f43c1c040200074482d29006698920300568040180ca25103141c89450030a0f048902010000206040398400b01c00d070340001e082e90b1141000c884030980c0141b100745620040701000c40b54000b0081c2c0c4080403400b80c0310208000340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 426386492 1250 426385242 426385261
    0x150c0e030c121b010507061401170118140c120109262703010e01150b091804030507020d0807020306010605030603150c0f0c0a02090109090206030a0b1f030c08 70
    0x103002c000380300b240c000c2042001d102c8162a0195002a41850150b081a40503982c600844103814500383c40c2c200b60000400c0341c4103420154485c400307808030003071003c800c04a0704039a000701d044000900009503c451600790102c10008040041c40041c049a2188080300d0590300038042404240c44442400f08280c50001810700042610000100294600041c0144003080c1580342911104440009050400d00350307001d00850b800050400c00002c1d1030300034030380d80b44501540740d0b12000101c0011701800d90590b03075160940418401e08400e003515959a0300e400c43c4c06100f503003030003540021103104d44030a002401001d40701c2540309404617107075a6203131641911f25010407200341d0381c19480b49034124a800b00100080742c1005c510b2001ca42444802c10700b150058001d00c07080140381d8401070b442d40a51070314260807401080e40340c2081001c490305401241180c0f00c0140701d8820300d41c49806a0701079031221041d2100b140611a010070390b030401098020301a20f64002581e000804000104100c0c08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 426387742 1250 426386492 426386509
    0x20f0a0b0a05090c0a141c0b0702010e06060a060e040207020a060c0c0602150601030b010e1002030d110a020a02120a17091f05190912030f090602010b0f0d150c0e030c 73
    0x300522010f1703614070f007110301d241c41c0000740704080e0000380c1201c0300d6440041d245440b0064521613008426103280510b002800c45038119004842640b114007805000c0c0c980c42e4071041543d80b1450f2288030803c460000c02c01900c04d66200a41256101030005030f510360145c245602d42d40b05005100185a80720340890765022404501d80e100700040b404502598080d6100841e08031041c1001d0a50034404000162046102d406581c056000002c88000d0a1041d00c80c070101081c507066020b040490322a0002d648203141c160090058400ad0420b040c4403504202e11074000d6441180070341501c3d00505403000301c0e007000d001240110003003034000f074910319013094820391404c140c0d40350707030820000d803056400c855115420642444034808010904010f2101041e0b02c0324082c0c0c131003030003413080e580006043c1303800c1b03038000c0d01107914018280c0e901d580c44590b000303100241280d10080e004924180110a9a50310140003103080c80c3c82d02c6821625004001080c0d28002101a10034500d0044c00384030207030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 426388992 1250 426387742 426387763
    0xc030703090909051b03011d280510050405030d0f0b04291504030f050d0809060c031b042102010f0c02060d0c03020f03010f050307090624020f0a0b0a0509 68
    0x5400c8035214902c03514026544580904000b800408c19224070301811201c6001a0300c0d022585d0401880c440d284a08050f000001d001c44100c114001c60650716140c1e21040085400c2c035803140c0f1000404c2c00d01604000343c910400c05c00ea03040010b4047c03621050018008864114080e030f0400810a400c600c1c2c04c0c0708483c060724a0303d0004080c4107044100403420450520810f4501d4041c0804004100c00028080d9220300c15401400d2140d007181002d0702c90b0b0340003000c52509611102c10000303650741081c1901d0f00000c0d052190351a641d0034101041c01e90240b500061404107000803a62003101d010044000039034002c2c0c0b180c40c130050040f0b01c12a1928814080a074100c042040b6150702c010089e403040760079031903604d8014103014107a0001c2070b40e42e000b070f40403071580c0d10b0140c4203010620701030114000414038100e040103401d02d042000450403908100500700b468102c59040c1d0f500d8000d00c030300042071240600352500f0710014a8422030410081d0f40c1d81070514036010000300d403540d0010701c42400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 426390242 1250 426388992 426389003
    0x70b011518050915060c0d0c11040603200f09040501290a18090209130b0106030203060a26060a06080705060a021507030608010c080703050a061a1e0c030703090909 72
    0x100d0f074400c03071419484ca2402e41d040343c029508000303050100c42c1c1071248460b480840e9550341400d41d1a410620700309107800a490740b145242100c2080002c0c1d0a9001307020a0707951480c035070704074031707180b800030310400a86521981c204000c01c0130881048010b40c054181c411030580c0c050303417004400c1c503403c14144400c07080681103106c10741c0034410585841a00303c08601d09180c081220116030703010454680701a5041c5200802106130b410820142124440c050902031500314214a01000010300d0780d007141c03280c143d40e60840b00154100c100c410070942e00c2070b140f003c01c403403150510210450040010f0b101e41155405a007001203454540f0008894840c1107580c01043d0820001c03203040e6600354040d18a4041c0b6989802c00121400280900c0300d01e81e1140c0c0710890036182480010342603d80040116040c02c0c81d010040c401315a02c610383e016100d5103554400d44134200c08400d61100c2c0d40d4010b491012940c0420b0382005641d00000800100748241d0b61b0046803950742003030a069a4544000521 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 426391492 1250 426390242 426390259
    0x15040c0b0f090a0815280906092111120711031c03090c0b070b04110d0b010e010314060903090609060f0d0507080c0a12050705070b01151805 62
    0x40305031014007030001100000703031a901e4814a44005a1010360b00ea00456458002c00e040303d48080440b94110340c0501e40b01036954206200386880f20080c007450b4240398516582e12026000d0104030743c0b00303000e00c035484061068054031103800d42c41c4030203240c0500400580380d400340c8410b403035000c1500d41400101040c0325090171290342c1d600c1c60a402e04c90741d894040c0710b008060904044107801c1c601c5c10f070301c40744c070002110030312402c00401181843c2c0112240203020404a000200054440356009800440307000c0b103a40d180000a2202842040203000d141205002040c11402e4004040c1200c0c03181d11100c084103880c1d50803944481045074040284d4100303010003903032410580004d18400d00002e12851406c10009131800320341c1c00c219140c81e040384d615820016402e401011240c0c100c0c1c001161ba034106501810010959102038060912464642d404601c1d040d00403800e4800807070f4850600d260540e1100c1c2c2c10303148240d010f02d40702c0006210b014416a94425000b064096942c06071002c403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 426392742 1250 426391492 426391499
    0x3020f0315190909030305061c061a1518040e0303070c020105071205090102010e0705101b08040617072f070f1202040e0c030307020114040806070c0515040c 69
    0x101440d0311541c480c0e80086015420841503840016060301a083c404400201c28203d801c0080489100a2003180240d400b996401214401c1c805c075030381c0b119803210000c21068905494440044003e851558111203180e80a0f042c0c0c444102c040c1c0f078609607041190f608c410100c0104820b82d101c1d0221041d00c1d41007080820461449009406076590040c14064640946130f500c3c2d804805070004208001200441c21100569080c054000406902001014540c0c1032100041008280203400d00c18405036610955802e0714150115a460360442440364440d655040b0103848000380c04401c8040f03d5074100003407011405402c080030003d502600c5100030a45024100c0c081c9184031000c00b13514810340b24001035442c410b119030b0002d001c82c040100001c00142c414407085c1c84158140c1d81040e0404001105681c900200f5904e60a0b02440d003140300c0c41c0448403401062003141c218115038015070041060454000040c0c0702c140c0d200d001151000c0780400e02840d200d0100b540c000309260030030141003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 426393992 1250 426392742 426392761
    0x510030b04080d06080307060207030e180c090d1202030301081e030304080d1e0608160b0f13150302031806060109050f041401140102120408060a1805060411030105010603020f03 78
    0x1416100703942c0f0301c000341c503d0725804400c2c13440d00113000442d0304a80009180c2c08059010034030406205c002d441500b0800c140302c80040304910002c1a5000492002c256104903176503405864051326007118200070112010f5070f00030f440e40d10900a100c07292080003070722089200c407100e071214011562000385056848a5071b40704440c2e807207078080891164551a00c9400d6500342030440440345241c0b040081c81c5c0d0715004140b41011a030568030390b000010b010f410000400c00008070b540d0708108500c074a540b50a00664110103611640240802c02c840e001c140e17603041d42650082d4003a40038000340e611b9045001ca05180c0e80d0000b241e0942c0043c002600400160420309120410000004e002260441c0030b010040c074034030001d0780200c84d01e595070709500c180d070b5030140445110741501a0313515182500740100c0c0c070f9807002c0113000c402a0696a0751400d0020107052803a203045980103042c1c03545820a410a0080b556240700314500c61751070240005403085c041d1003150700700c50032003003460f0843d9a6807940 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 426395242 1250 426393992 426393997
    0xb0c07050d0602091f020705030c03030d0c20011a0d110409080d021204021206040309030b0405010906020f1e0412060209030c0a2705130609050c040608030702040510030b0408 77
    0xb128403d400b4030040c0304595981c1e8150001c180d016015030a003032220306009140500745d5000320f00903000a50161517a850202c2100e200c01881e090100340c0580c052002c4500c3d10310a1440d90101c82d050441440360001074000c482d40c2c5146c016103007040c62414081040c1e007000c403440146480c403403000b00e0040781019004544440d000d5031460703080003d041010426607011850941074851040100811450900722880c40c0240d030400a00c42c030b14240d40c000e0001070460001030309100c2e1260005003082002d4104508031a84000c040d5256010004030302040e422140310f0440a061850702c04145103910801d031411036804502480381c0c8075084e2102c02c0258401d45001d9058050003c80d00c01070744688511100038800e100d10001a049100b410409651035403511026287c20001401003074040c1501c50300003a604000000ba035402c4528000d40b50050b4810855046820928005107000003c805043c9040c000d440c00d0065607208070140d2358012007800001c02c842c01ca000480c011980ba10302 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 426396492 1250 426395242 426395269
    0x114012105070216140103060f1202090a0e031201050f010809120c0a02060c160803072105071a01091a030d030c0c050a0c050f030303070206160c21090b0c0705 70
    0x43e204c0280d140708030090111180e4018070400410551600103a590504c200001007080c0d43c4244941400d004a90885200090020f44900c02c43c002160070f0040a9101a028420090031695101c0141307208120291003441401d2140d0001c0700000019401004014401c0d82d0b03c1c40501a0f845034141c0d2078459400c003a1003181c81c0d11038045201c0050301e45d8002000303c0501c010040454034803140c03000e40d90301e050b90454907040e0402e1000400140701c0041c201600410740c07401900300c180030741c0200c1e43c902a420015150300311405072140f07444140140c0b1070503034580e82020710032141810560400c00459242580e010f90190a40045031032107684201074890051524ac40389143c1c0762101442c04800c0c90040c2d0300001e4100f0100701d50f203000c0c418055100b01c25000780d070640c07a00c1d01010f521100020404000420004200031145110f500c14400465205201c103483c00888011010b05003041d00380301d00807940041010a041c0d4109040d9a014001d000c01000c0007401c0c0028000440c25146 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 426397742 1250 426396492 426396497
    0x60d1b03020402031005100c0302030901030f02120f0402090a0c02070510050c06070503100e07050d05060a15080f100803040b070c0902031303030501092927011401210507 75
    0x210040016603441c002540a0394820054681c0541003208011080180390b10f10002e2010204485000940100c29652600d4003420001100030b1030440960103881554540400b0119a0080048181540038518012402030b241135001e5070780c04030240708403034464600740050382c09050100484d20300070015031a104018540b041c10034a000341943c0c60300c8000c0e102075012800100400c140354a032094100c00504078a40c045106003418040a805407142c119500d04182d1108009001a1a0350015000a11312200c003610380c40140000103110318070581d510035400c10f03110042103641884101c1101915500360107580307404e2815500400a92214500300d4000750448400259043d9a102642c42128054030349000601e03c0c2c9001811140c0580060b80558500070442050301182004a040d01000844609251003468001648448400e0a80c00c000320000900d002500c181071005040344c0211041000292121005590fa2100c110406d1b00e010a01041c801c0b40155582100383c000140c9e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 426398992 1250 426397742 426397793
    0x2071101230d0e1912030c05030601051b071e050402030717040302210a0f0f02060606071401091412120a0c1b0c0807050d050a020d021c0f0614060d 65
    0x4801c810b0404c8032240030004c2c2c03111300e1940a000c2c4800c85054400284081c502042070b00303162500038041d800b01a045a04203d0046100b00503224018504040b5403e07060844a14a99a2414103c62440700c2940c0c0c15810405100086604140c001d0364000d003172944641c1640c0020310040700091070028010f40c118402c56400c081c9124003070050391101c0002d0042265901c04820010380303000e890401902c10044120020801c1ca580840c1c2c0b250004400c82d181a596059070130300790f0303400207481c0d04c102c01da500c0c0803004000c0040c641c00003110510380314160380041814445a0986015000d5210b031800c910800094007441c0c582d000032400c4085003010190100682e1491307003001d4034100100d50307014405a017030000c0c02e020820440201404c41d1821030016269032142d84400200788003d000e4103422400004555504180c401c044027036200101d02244181400001c02401140a5442e0740c60000b03050001c1c0c00311503d41c1d10810019040050415080e55100803640140203030000d0310424 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 426400242 1250 426398992 426399011
    0x80f100b01090b0a081e0621030426160605030f27010b0a080712060c031d070905060406120f02060f0a030e0714090a020306010509100302071101230d 66
    0x83c4010f0121207020781d0342d09203145004460004202200c4203d030101748404420000765a840308212181e0141c500c4568011071a000e60f140d140d40241e401617021030711007584640864038003016840b0740d201c403041200d49924408601840710107140c01884c000070410000070317440325501c6e44620741203001c1d4100720703600110300c5141c0300d40140700f007000c038026035183c500e5004203180170112180500700d40c03000f820107240703001c40308012030032080801000359440e0035460040b54000d80c00a80480000200e04c044004d001c0007140d22802540524070f1098600000700d0b0180c01d140c480c030780c1611030082210601e040c0544400c0c401a121201c2240d0002041150405081000018000541e183d460204129142c0e0140c01d0401c050ba4024900f200c2490600c58681da95000b85141c03ca42c99140c01079072a00d5401c012102c1d03105068030690440d20400305210242d1f4568020130000c0c2c0925600c0b107140e140d40004403070000705940e0785410080200d60043c0c020020b4001008000a0250002196100c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 426401492 1250 426400242 426400259
    0xc0b07031d2b031e0914030106050a080a0c140d030509190603090b09060417180a0b0705190201050a2f060117010506010c0b150306160306080f100b0109 67
    0x10020b4592458074007882e40720105034004140052242016500c010030003c0d032200200925034512640c0340f40d80980503500640d8400b0350155000d0032303001e040d1100c216210742c803446d501c45000e0307800c070303160049054000340c17003036449003800808400282000801d003c2ca48007240da5030800000d99600941c010607071500745d039000501c0d9000301032640740864903601d1420900740140c80148440ea141c0c002000f0080001c14186400070040c6482d116a5200c1c1000180e19050000c0a808650400c01407000071443c400c024001e8151603114608862110b09546509094003038800310003404034000f8880050014082c40d07502e215074100100c4980484130b408815900c015a02c403080b00981c12810042c407058584058407000d00c407503400240701500f05100000d10440c400c80000d001c0003180303800720380c0303080484030311030b07400c01d40241100d1142c28010300070541e00c5808204c400100785014000280d408001c5000311107810404040c11595014401000144c00401034040c10000e80c0740c00420b0404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 426402742 1250 426401492 426401539
    0x19050d080c100510090b01030e071e08030d14150d02040f1503060606030c0504181e02030a3c0c0e190303030f02090d0f17070f0c0b07031d 61
    0x901c8084c20404242c9001a1001100c9840c44c50324105401e104d42da03090b450700055058100c41e01401c0c180389104141c050090404000c3c5c00c010701358003000560a82e01c240075085200700074203000d00d62905403076580181d5404001c007688030f90000c0f261854007001d4074150703002d4602c40740d904001040745503151304a08038108040d041100c100b43d8440c03040c030000d940340c0724509031643c00d0b0801a1a007401c00b10610300d42d031030038118103082c039481c0c81428065001d1140148481c0e02c076184190744030f0512000241c06005454150352590b1500740e610168641c6400308a444400a2004022108405008200501103494481d01032241d1602103404030340f20000340c1d80000d50504c8808500b0790452400800b40c0f03400700d600d299001c0c0184100c45031503417110013120b0b8142d8000514800d41d0340e1803422000016040e07a00b1000c440700450300303a044c001d0780464446110b12400a5031490fa8a0b108103000b14001c07214050f0000d02d506185000345404905040d5404800400560788100d60854829805 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 426403992 1250 426402742 426402751
    0xc110a030308190213031e02040203040b040210020d050d020c011d0a030e04060612020a0e0604080d0e030d0801060f0e041515090b090d020a080f0c19050d080c1005 72
    0x707545001080f50340d20341c82800410488403001c09620301101c6a403803e050342004e00010703004c0b40b0b44c00000c0e400c11980300b03032004000391301800a41d201d03c2c00d4204040d110030116000d900884503200307940305071480403039007081488654031200d05094452000708003d4101c00500c450a40d070b10201000000c0c804a07024010140c800028081032405190081150042410030780c0a1400c010007402000e0300801c2e107001c403000752580141c40b0140c011080328100c40c24210550400400607011941080210310724000c01c4450b25041e58000c03400d414160346810800301e040001d440c000040c000b480c400c00b0340c41034003000b6284c0b880301104a1310000b8100c8001d038001041d408005141004040500811b00402d41140c1c10928041864000316102520a00b20083c1c4600300803a0300302c08556a4007401c5000c3e001c040102e60f10050f104418070368910401410f503201c0e0f481c044404500000700804001602c2d009800611a13403015135036041e90741c0045418400324020303011702001d1000c0a01c00c2a208 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 426405242 1250 426403992 426403997
    0x4120521130e0114060f1c0b030c190308031902030702010204090614010f030b3606120705040507030e03070b01050a1d06190803030709230d030c110a0303 68
    0x140c1c0504000d2100801c9107034041440c40c24240010041c00c8550003500310800e01c1604d1095650b44a091460114407445071001c500c9080700c00011001c420592045600c004285c04031060710f491507007001803100c0320200c0400c4904d00c800051001404810146810224280140a00b58400300c0c000d01603810440d52000103030341c041020070003052035020b0140140303407112440030f007480b00c10b00081270704141c0b01d01c0100345504ca501d400c017141c40b03003a614090b0b00071380215955520b40a5002880e0085200442000142d2501c0410f03903619142d40d100440c1e0605074010100c113403600b01440701603c4000c0150381455621410803061400600040101c0c5114090501081d0b05042c104446e00046801c171f01481d40791031102d01d0040281c0ba8102d90050800c407201488064410740859140c01d040e04a0b5003217001c003200780032569401803146010f5408075482d11200990400480c07800c0f5402c60310741c540c00f80d00c5e0080d02011034055001d070655a8024401ca41c240c00000f00440d0703c61807182c1c0120700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 426406492 1250 426405242 426405247
    0x4140316151a0906010305060f0604060504030b0105010207060c11030703080d0b031b0a030f140d1e02031809070306050306012903010e0612010f14070e0406060504120521 75
    0x207807038800c0c070548003891480c1e00c4490045242c000410b1038414001c002c0c0707051603500c0380840c46075599940c1810b04868020301d80e43d5699280c007401840c6070400e1004a504041c03040020889600109003603080c0e400d1641c9860341551103032190364040b58041c1c02e180e0140510a808030110320303400020304001c2111400071071800480d1003490f18005080e00c440034107034010680001c8039681c800248040303940000c074840c0c0c074813070500b4100c4103441c22003041c441502c251b48605010360b41000c05151755441da180503140c500c2180c0403ea03100e1140415182c2140001103104903240b41c000080c41d0408114500001c420f07464601091504900b030b000f040f0b00c1543e40030045021041c40307840002c0103031495051810f651500500480c1d454024000c0303881030b00216034080c03908800751b00408040c1c0983c10140018840c0c102c04005403a01955001c0001c5c0740200401c1d12400c0c64043d480888035030750344041c0340c240307044007035003059038034240c2140d40e8000d078182c1c000d08560a20407802a04440b084156 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 426407742 1250 426406492 426406523
    0x20301030305120702060124090902160203060f040503190323090c010509090109180c0e04021008070e060c01291804150b040e010c180f0b0304140316 66
    0x404281c80145203004551041d0700602501d01203440e07a03000080900440d0b5452200303580c0030727514012150022050302c1d01c0498108600210803095500e124000c0c0e090380c081d5160320340031401c415400c44018205600802c51401d001c41d0b1503050081500c0c0b5480d000030000848070134070313000400b0849a540f56041c900c09001c1501d009200401c01c0380002d003415460441042c011550390304052007080c202035602c1d048484d410b01003010301c0c280141d00004c009643e03525404802c542c1e4009490580c0520003215040c03029500030741d1414000c00c45030f202c80700700c880104100f1409502110141320f0f40c1d500d82842071940c40d40c1c0541d646210010f50140311002d01300c4824403031508032000990308004440c03010b020100d00d042da680704202c040200301144503580c18011a003d84180e0080144a41c60150041d41c0507612060000200d0751000b00460b0560303660759420f0400d141405814034022013000401c002400401221130004846015203041095441d200c50100f00114010756200d8650380c1c0c801d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 426408992 1250 426407742 426407767
    0x60e06070e1c0f0507032109030b040c0f0314010c030c0c02220c0302250c1a04050604090f0e0309300105010b0315010804030e0906030106050a0605090a05041b051c020301030305 78
    0x34000c107084609821f50351012400014007100c42c5104c042c04144105c40400c050101c011070785000b41c075036509040403c41c1d891625010301000d40300860015441e000c81040014841c3c051008030b070a5964500304000c050782c0030401d4009100214443e50740d5141c044a00e030b04a10b0042028150450301c0043c0c0303a040b03d500c0300b05010030410000280a010324680070025400b0a8200140d40704c8140f2855100d003801d40c000340a00c6141c0004da031003100031070000b0b00c84c2201d8201c0d4500b01800310341841a070307200b43c90699503401451203895000e1404501c000301103002038501861300d4100344969071601e6146641908454081e040705603012000010007001400b00078804401460a103450b00c014a01503c00609030300300a0f84c554415181c40c00403540d155000d401c4900500f00042240700c200c2c0d034034940a411644030308081405048401000100d40c50984100e118032000b40000200c001500340d01202c0540c4134000910704e03c004c40103183c6442006101960280d031003525155920802140d11 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 426410242 1250 426408992 426409013
    0x703020316061e052203151a0d08090d03030f060f0806010602150c070320010f180c05010c0c0306061d0c0921030409050a0207060e06070e1c0f050703 66
    0x15000c696038222002040a902500310f80b2405012868480c5003007048080c00c170001c0c515803001e804040752203680b0140035029030010510014450440c41c500d007445003030040d40304010001421210082c40424158180041c1d124500b5110b8580050f144903160014404c54402c0d4200e0000b00040200611524104200242c0901114001040c0100c02881c1581a155004024450401000c500001010b00a83c1c2501101051420074003011024090b4640280459504003100c5400c14921083d031034141038083c9403031a0883d0705078074840d042c840190f4100c04058012200c0e050f02c41c070000007046e80e47c45244094800350056660940c4103002404070264050301c580c3c20100c0810041d0f0781680c0f24070341061401c1d00d070006810f00c40e0480c20804e003103020745c0e842070314100d050404000000f40e040d0f0041080c684039400421180c4034950350380c1d550780c108036041d001050703034401006240e1506085641d08000c09503d0401154055130b911005150103580889055001450600030018450031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 426411492 1250 426410242 426410267
    0x20a060203181e0706030903140304050d02010516020303010308031e07030506030c010e01021c1e08060301060b0301050907141e1902010b0315150607081b03030f0a020c070302031606 80
    0xd40d440c290014042098a030300d540d1142c40c060640e540347c080c0c02c05001d001c000f9208064440425201d2406050154a034a038540c60007006510304000108005504c01c00002c502c0e4881c0d00642c110781c03d40c0e481c1000303a0b101a1030306510113a50301c1e03a80621252150762a214500320303030740460346040000625240c115905000c034103100e000700f4400c517241d03400105a110780752000404509001000000c2c1d85640074801190240b480c0781c03007102025034000b0b00840c0100401c0d0000c01460382e803104425860f0100b0700441e40d110300c0e50700129042520070114076062034024040c1502d840c803440b02020001020300c01a0f424100003186160007100200003940000220307000038820301c980840040c0d114400d210041d9440700d03030319001c07070004038030312144455000e40a4545651200b41d401c0607500b83d0480544000300340381803e000300c080503010040d60302901408514031031a442e4100220302a410045d1400c0041c850b0020020240e0760401c84000c0000a0040e05030a05081c52002040c40c009101c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 426412742 1250 426411492 426411523
    0x11010503010e04030c2f01080109140105011d10030f0b03011b03110405120a0219080a0312150e0621030f0309070305030f030f0106030c020a02010f020a06020318 71
    0x30041210a0055005661050380741c6000e4503000424980403402c0b8078080301443c5203400c0034403e003103026042d4682c00b010850907205c2240703981c2d035510b81d0021350308005070040c0c010100c00010402c55000340d40a00c072046212003407401c0199040c0c00b05440d2412040211b0000b600d89802e0951003940c2d201d001c101c2ea070b05030024441459164040344202030540d515104140e50b50811480171000c40b029075000c0d05005050045228070b03c02e0741642c0c0c8922210607031094a0400106802d4007035070b174084c0c0031904400090221018107480c00d69170020300c00103401443d500c683d06284452500101a406443c5040c03440e44541004000e029040c1a83c041030f04401141d445403460280001040e07940b50032441780450780d00d039903a8401505140b450350005105120201c0c1442041140d0700c00b56115035280c001e030030070581e40d510003102a02e50500b00000903030403070014140035510400704503076500118012144400b0090361000b00702c0c0d01c1140e44041186801c00d800540440620989100c0321000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 426413992 1250 426412742 426412747
    0x10914010906050a0302120c0a0201180c0e10032319080702040515060d0903030c0f0512090c130e0105090d05121302040c050c060108060702031206040609090f110105 73
    0x1200064150242800791006002d40400c0c0c4a844500c0ba804444050b02002502c20040c10420b90030300d0396400001900c005075081044c1a0f0b0108041e004c107130711145e04241048030007445c1159440843c2c83c0580059a03182900d000403011800742e00941c210850400514159503c0c5180214200030f00418500b50703034030311040300101117108082500c0c0e4864045800003000e0701c0341d5202e80c80640300319040503085880403448040c1000d65a0192450354000d4030184880d02841008450310b5407980d1041d00031600038030a241c090140b9610b090b900880d10b034104c0f0013041c09100043c480900c0013500003002500d0b00c013070343d0509800780034698000b44000f000380400f9034500c078050003e004a468084003e80003e000403205140744035031002c0c09401a0040058006140d0020400c0d4015a62080d0920440740005071190780040d034940300e03100640c090b60901c000c10781804030750740340a4520780c0d1003610383c000400e80c0041441114490303480340f41028400d200d6840c1038882d41c0198441c480c10310806 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 426415242 1250 426413992 426414029
    0x121006020d1409040f0501060206100b09060426011e11030c07030c0c0308031503010e2a0103090c0816080703030f030e2b0e120d030b01090e0a020301050109 69
    0x3002c544100e260701e00c0005501c0714500c00114000b861a01c01420000c0d00b04400002c0068001c202103010b030400300c03d4034140c0b680300c00440b5201d01c501c507203041d004802003108001d0300d840030701d540d10102c02140915a00050f9a0010390a4502c2c40c5016940b01d8108401500520f40306d11651640a120514481c2103103000800101113001358000601400400324401d810441122840c1010350b40c4501c44689a0401003400185042800d142c0ba00035072070180c000d860088006000486004090183d01c05600c0c215000386207a01506801814140c982e80304000240800382040c018020781802000c0390b2654454850400c60310750b000941e507402c10344040c0b01007a0701c0b0030b03528240101d41c200495030344854409a1328101000e0034030084e50b08280f200d04000700e550629401041d51554400c17400c140d09000300a8a030500020070004c0d688820340d043d072558040d402000f0a2901414070003c0242c1d2103c4030322681c0000c42d003170800b0560020040c000303513802c59214005401201400c41c041041e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 426416492 1250 426415242 426415247
    0x1f0b01031a060c030f0a090603060605070c06110c1e01180308030406110d1e05010f1d04050c120102030402030d0e061c0b120604060f18110d08121006020d 68
    0x12281e0030070300580380000c0e90140b0742c204000315131785068088509680e43c8101c4800418442060095800080c00d025000038007603c0703101541c40d001d0f0840e951040c03040c54818140d584034651600c1c02030a010380000d800a66607011010041e02c0500010b4108070941b040004029441d411512500307590301c441c040c40480c01100c01d49910070350244001411342901180d006250007000101ca0302d0300c0c140607541c5c2c039880c2002a0b25561104202d8240041c0e603c070107007615030302c1c424018282c0c10054201000405000c0341040390300700d4003540c1a01c0400c0c00c10341c0416086841c110300740199a400006000850030100800300b4004c10034503121140402c088005451031040b04070020081009503020385420005510505076010001c0090b00d07000310201c0820340b501c0041f98180d4031b50346040d901d460b98082c5402440020701d50108003a00c080c80c507540310f000d4014a0f075401c171740044d40d007099000002c50500c0285401c2d020301300709007007900c2e04600482c0d000041d43c00c607004540001040701c2d10b203074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 426417742 1250 426416492 426416531
    0x1507080703031503240e19080904020702030111040e240405070306271107081c090813180b0109230604030c08190b190b031f0b0103 58
    0x6a1501e0302094102400d001410300b0403144c0c00182403810502c40151941c102884a00d018802c0d800040c015400780140071620340b030058060018482d543e059840004640000800b0b450b076004000600f0540c064010a084135021310480f070610800003024402c115640401e9a800317000031403280722401c0c01000108801c036146074841e00490301c40010507030442c06a006000900b03404202440300c4030b550051600c110020404820541d49007600043c00f840d0340d1001c03141c02c16000b0740c1d41031410008024000d8810301158284034400d61780da00c0764001401d120001c3c441e01c009410310000c420706000c0d49450440702c40b00800e0383d061601a00d2041660048945402c80d01070383e5890350700d610100250314a0181d54186036901c484009408002c00c0399102000d0107803104442210144c01195041c455014081480a1702e1800c240001801c40c021b403640070200f04840810200796002ca807808070b40b034416203401451007400c03040043c0104941a00c10f544161800340303400d20800100f58001a0b280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 426418992 1250 426417742 426417757
    0x1214011b110109140c0a0911030408070c0807030c0e0106050304030c1b081e0706050a0c11150703030c030f02091305040f02031c1403090607031d01090302030702150708 74
    0x11185400300c070090350703083d80000c420ba9040038075403080002003a010703600e500607078013864810752414a010036102c3c1a442100100400701a400c1d02c2d648454440e8050754000380700403240c41c05508000300e48808140552801148280101c000883c100b810011800c0070581200040010901c200404a5403001c050064a9004a4182d003030320310302c030344d01034000980e81c00c482c4e924400c02c007001da4a2000c00004140c0811031900782c0c0d00040e00c40504942511403010700f00002035400c00700320041080a403030100043ca0080039180356220f000000c100b02e400510f4240d012980d140c070100e4243d6014007800c4581e4805c180214a0482c2c5800069070b8502c1c401c44d66070300150b9500004040202114002d04115001002c60350b104c1600401d03181001071b81000800040c1c1100c0707460a8180a41090b03070701415501c8040c00c8151360f02c2e00e045004141d00050700109841094070440881e000384104d2003224000e601a640ea01164014800c01d104110040f6110344420401003000c19601026260403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 426420242 1250 426418992 426418997
    0x60b090609010c050f070b030114090c19020715020a060e19030e130e0703061a060a111f1a03070303020705011404031b0e060102070608060607060f061214011b 70
    0x100c800f9410654501541c2c500051403500c03a082000c9803080e00000594101c0d4061a040038070030b2076200c1440a070503019201764140c0d520510035000c8080312401c040e00c40c0192413048980985e238070b07103102c07900d00f2800a9030b00240c1c11400c681014403156011780075540301180b0082811110785c00444c5c0140c10014005001c0241245103942d850b51500354003864a45829814822003142654242e140e2085100c202c0d802c0b46003110b050410500380082c1d50329030030010700207402c0c141030203c190307168800d026400b040d9001d22100e548210040f400c2d240500440321030300240a041c40c00c2840742d05c0001c080d842d88607a101c46801c02c002036001403140d00341c07102841c5c054403000e2080809411801160002014803001c08100418903d01a850500725490640e1295860300c6003030040e0b8807034030113000d802c001840d01c100180043c14507100034061780d40310300c1c0c000070b07051403a1580601303d03182a049420020901c0e99450306004070072a103907100444a030001c01851600f903496108000522812005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 426421492 1250 426420242 426420257
    0x3040204231b040801110c0f070308030c0319050a0f0b0105030c07031103071a16030905071715090d11070806011211090703150b04050d06050a0204050a03050d0201060b09060901 78
    0xc1002c44401d540080040c1d000a0040302643c100d140415040b08140600310320855802c80c54407203000552400f1250460000340c5140c444064100c22640010a200700c1d00e04020326001c10b4030300f40e1003043e224048d006400554040c0d003c0804080d62111184a81001000e00c00d1000341a00700d42220507103513040c00d242d40e944403044030050860141520203880001c03464007900d10442000c0340307184903000402440c42e0b03030594000141c049904011024141e64845882444152604903101d8094100352049981242103100301c07aa8052044400341c01e90340040c5c0d401c19101c0d03003180280c1d544810312005440f401e070900100581e03c00701403064100c0210406049020b01441c504c80d160200710141561050345001d0f20041c0160040704039282070a180703494001000101001038074113445c1d0040802e054103049481d0180900b401401045500e43c0c20040040c1c035607a004100310042d0312580281800c000581c001908584503070780180300001c010080282650f540c03d08907405c0a50900b4003a0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 426422742 1250 426421492 426421531
    0x20105120a06270b04090312050603031605070f08010b1c0314030a050603070504110f0f0903071503180b040f03090b0a0c020a15090b03041401050a020304020423 71
    0x10050b1100c0d0380f00b484901c01220300126810341d188000908198420030070300001c8229000e01040320515030015000580c20b0741c4c1413110300015005540c21010003030842e42020f201e04280c0c400c652072421304591951040000b004404410f414038030003081c828000b00a1400c01001245580f1864090303203605c00804140b52003054000c0b08001c0e840c400d030a0905131030b4030303011a56000514003a542184a0301c9140400039003840e041c0100d6120340e4238040e425007001158101c9203150f410080f00b140c0b40c4041800000a55101002604001c120741940400400c04124014080740d21550900e12820391f40069180072075003080821b0781140e03001e16281840305850900703c0c1c020711030750400100c5030000140c032120190f11045946c510390088511518042c1d44a0448004001c520b10000208040c41004c1185103034600c040d540c070078080c8440b40021184812a00e003114002c07120301450950210512003503007040c0c882d8260381300102126454490721060b030201a1314005142e43c0c10400303800302c4103 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 426423992 1250 426422742 426422761
    0xc150606030c0a091e03050f120406110a0602131a03090703020f0315040c1d011a09011205070801030c081b0906010c021e12030f07120908061810020702010512 70
    0x20001000d440481c5c085003204120b06070640d0243d80700c1942c085c410681c00702844500801e040100c01c03d41403d1611301845c1c06025500c100c60883c20380070300c2c00707202842c078049031107400100041e14103484210a01420200070b0307031081078032103114543c1c032509100300488844c2c009218401c0e070750101c1e078190f150409000068540b000081c10b0a0101d034040041c08200008111141c09036602c0d0140120000e01d100d1408034084401d04c513409540c806c03940301c60501e8041c403004001240041c90601542c00710a6014000e6a900b900c903900003508400040041c08401c40d8540d015042d003a010703103a4503a244441400e10790304503002c1c0d8421030f2801d02041190b8016804658180d501903d031812040000075020000b241c0248054041c07855611107050071a000b0046807502484e20402c1820290f9903101d01c02e28a455084903401e02c00c4890002c28514001c00c4041c1c800d106a60104560001840c0d186051407200c04000d84a03030b006101c40d90050f0f82200503107040f280904045040c1e5520440079 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 426425242 1250 426423992 426424007
    0x2030d0f020d0911040c1d0904050705060301032004020f030403081008070b071a041e03121113090c0906031505060f0a02010c02061b1308070b0c150606030c0a 70
    0x124000341d031500410504100044503101c0108401729400c0259004290b0140d64089000822007508100d8001415503450009400740c0c02c5805481251416915100030a01b61f61080e003068071130002020b8038140301007403070b400a48506010341d820350802041e00071702d44050001078001030520030000c00003001e081c6201504001444148211140700b42d854108100a90100406545003864008003c8680310b0002d242401180d1058054481d00707580031807001908911101201004004030321400e000f0b180d8042c099121b214210041d5450318500c0b480c9100004952000000764244210b0703016103508415031104982803801e01040b2025401c008c0440c0d400541c008607807103c4045035401c2e050071805c02510000c02190020400241c0a041c00c2c0e0b601c0b03000b1207600492000300c5071a1801c4409078000f40c10003c83c124a01003030144c40e807245a00b4640c0076008030700d822002081610840104000c0c0034011080100e0a102c00d050140c041907181c4001000303042c00000000d24004000d203c0c41d02d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 426426492 1250 426425242 426425257
    0xe0a051f1518021c1a03100e150a1128030e10020c03040b0403050a02010815100309050c040c0e032b0c0f0510020d060b0307020607120e0307050d0305011502030d0f02 73
    0x10030242540d03003172201d074120541031034900a00c50780501290b099518440c0030840307040e042c010a10203940c058441d144d103100400e1010900d032075038409a50385600307102030b181c4000c4a110046203045926400070000742c4d008580802c150070320292004c1c40d003004c245c4038080070001f04051380c1d5041c268081ca00e584642d500400030000002000810311402041c2e1701c0d41580300342d80301d0100f82c440c400d12108280c5010000c0742e0004c8142c1d03141080500035408945194407400940e0f90600c410400502203810840082003c9035019035154410701d000c0c0580c0124441c102c4189290b149580000c0f011002001d0403c8103200d01385094100b800b41046903108001c2c4e004007280e02038030748480c0301c1c0041c1d0050426098118144900403139441003d100741c0c2d100300038a5000b01456a00c80300111414a10114080502c55440c1181806044280020305c103040c0140c2c002c00c10894441401421241d0581c4582c4030b00407004a01c000590b808400c45405200c0ca15001c1180c1903100c481c040240b08461 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 426427742 1250 426426492 426426547
    0x1b080c120406020405030c06040f06031a09100501020c010302131502120f071208070f1409040c020a050f0f070306020705010b120a15050c0d0e0a051f151802 69
    0x700820401c41d03800801c29180158255030f4004481c80a2040c0c0c2e0040c1e01410201c021200420b1040c94032a074000d442000e494041c07402c5500014000c00d0f40d014003078a070002c200003e0881404296010481000c1010702031804600d01b0722000c103000c0c0601500d0164003041520404001c0301b90307201304640e041a000e0381d00c04559030548a940e815041d8084907044402c00c04a840c0c000e0342d54010b142d4648201c5450b214414500d1495004899002c3d040d025500744d40804d000f00099605e032032141036504107494000f003030f0200f007600b41245000c00804489465521041c4d80175030303008011910b041146e41c0040b01586801340703458558050801c149034135401807081080b2101203140081c0c440f004a014016a002401d241d90006017641c004035034185440e54100204000005641c0c460408800400140ca061312034694500e800d1095111012600210300c008904c10f5441502c2030360260702180d001d0500017440d0101688405401441741030f50a507010512000380d03150fa0100b130181c3c1080340c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 426428992 1250 426427742 426427777
    0xb0d090602040e09070803040b040522021909050303070201021e010b09070f03050702010605030607050d0605090c12130b07110a020a081f06143a060b041b080c 70
    0x11104462a1042214034000c4e6115140c0d00082c030201c04000c40303041d9102c0030300482c070706410581403240050581034070060602000300400c00820681c4003904c1990b131585070300602840d1a18000f02010780e00d40040348240c208202d8000140e0300002c603800005035140e62800d411002d00903207070041c006c40c014036800001d0f280c10000b034281d208a91440f500c01710380b010001a16960307012822220360703024164041d446203000c110380c1805007025140640e41564041030700d9854201180329880d003034515200d40c14011403034451a40203050450f90058004003c40340c0c008042c2c41d07c140c2c04501600c9232040c054003d540040ca181c1c00d00485111680141078101c0386da50381c0700004daa585941d444218404c03c0a00ca00d44000c0460240b4812990380b4841145107640344405c1240385544400f082074180c450072030500103418400d4541080f200365021300b40d0003102c54208242520301940c6e40900c5540750008059511199510000201c5030603c3d10440d40e540e540c20720703170350b83c8a55004039159a5030b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 426430242 1250 426428992 426428999
    0x622020d020d14040f140a0c0f0812070305040303031109041404020306150936070e0f01050607060506060d09060501052404060e040f0e030c0111040506040b0d09060204 74
    0x1a800a155010344075404210f5516154020b08500c0e4054034010700c406950526032010842d0960310708460348580d41034070a03004e25641ca0040e424001d611a50800410384800c200d650f1040c40041c0395000c414081ca4902600c5680041892003103000007424103542c6e402103100d1044450944040202c00f074803c000303a41c400e0140e0003021004a404a101e0b1040c1d20004140034407108002180c010090501d0320f49450300e0484070b251001e40c1c000180e80c00ca01854141d0b001982d1151064044070407009040901d040c00343c04982c0d400010105082b01092400401c819221001141c07031143c0c02200001e410344668000910034031a00a00c401c507942030003002c10611040c0e900c001d04079441240d0b8410000e003400c00300819403c400c0c51030001c4250a12040064034040c0e100640400d41c024400613820f480100148112520125540351a074404140e03c45122024410f00a02140c200146420315141c9400106d452041d0f005444c0a2180414400844101a00030307848030340d4400b0702951141d0b103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 426431492 1250 426430242 426430267
    0xe1608092a15041d0603012004090e070609170a121d1c14070305061905071103091512040b1b09030a0b0402010509040614010e030114062202 62
    0x22841e00052081d04800c103260300c40080042103030b0485101d600c0c012002d0400d16003040c01904020300d01c6416540b148801c091008041c00a415600d42c0003800700c0d19142012407206c12502e450520602c640d00094080c440d1581000c103600c1102c2a10340c205203070300011400c05e0b041005030030b80200581c1348000f56414440c0c01c441e100341c4c403d0b03c0e401170301014007100040040a40264104180d00d030302e1100c109000c5044400c04400c0410070f41c00b1a44074170355980d41c81d4680041141c20301c02c111064070500c04540303903034000c06401c0407552601d400e0f9103102c00f40094480c40785580c210311a42e803404000c1170750485802643d01c8945405200382c0c061820317017002c86a10004859555074802401403e060150101c800e840b0050800f60090060340569500c1c82036803100070b00141d041c082c0074003900c1510741d41c0c2e02840c0d0240505010140c420326418001601d0a0840001144030343d0604461042041c14019400e038800e0040f41c070400a0500c80c80068895004180f031b07011028000250071000d000c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 426432742 1250 426431492 426431563
    0x51c20090402070c0620031809060d0b0c07020a0504050402092d131a0f0a09060605061801030c020f060417041706061306030819050903010606020708070e160809 71
    0x5443d4102c19006c6e11052024945a11802800e10200b5a980b1000000c0d401c04404003541701c1e002902c1c0c8200150507881d4042c8203001150310500e400400074502045040c4a0b003c0380c010f000a84060229080c43d81c00a0f20240300141088202803203540c0000000c0c81c0e480c0d840054490b561403108850030300a5040e920300f80c0d80039043e584110322144000c1319550380c0d0640c520544103030f500300060b52940055440030300b090f000305032071044d210034002c681c95480400809850040c5182c50031107515850015043d60900541e100c02c1d500810400602c04001186060307010b5070183c40e60100b012546081710341c0740907541080581015140d0075014100e400214207018000c01c450448003d05c11241c0707102541c00318000100040024854084085500c00740040411641d00340a800c001c0d180b8046800c40c0d12540c0200016030049804005c202018000c0102905d00d5072240c42c40361500e013200d03002d03030b0f006a0182c100308003060001a51b0040d09002c0e4181040c20542d0040d41d44220f400e0480040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 426433992 1250 426432742 426432767
    0x110d0b04050f0705060706020903161205060a02031902070f0c1d090703080d02090a1e0303081510081008060a0b01080907140f040e06010303051c20090402070c06 71
    0x51095a502d940c1d00007002070841c0440384010155464802d06079608000794004251a5805105058541d41a00c060754120400761070740820f2080743d8640760074541d127010009408000250320400601601a5483c2c0081000700c8144001507030302d8600e0301c1c00e824a010104c0d0702412902c06594045000503012413100001c1041900001144d00d40d503106540311010780c400240148420042802c600c1d0440c4c001c0e0021120040a1082e201d9546e08501d0760305042c04c0b02e55211303143e4a00c0034810150010451138000241542031640b40f0003070070200380381905c251001018405c1e00000540040400d0000d10050700c544400d44001e4205009a00041c0a1a418081c00301b003c0300001040442d00040c2d480c01c0b1451034404000c000c038a6014840c6a01e0301481d181e4006440c2c03104900b00c50010001e20340203521039901c40796144064416080c0441c54400c0c1081814100b15100a0540302c0c1406400c081e9200c00049903a1361303070900050028458000d0050840300318040c0010340701d8111701000b024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 426435242 1250 426433992 426434003
    0xc1308031605071502070306050405190c05120114040b04020a0b0c0a020a1e031203020f04030c030201090501170c030c090409060e0d0309150905010608030d200421110d0b04 76
    0x10b64813001030010a29102141c4401070f4804101080030640c59000740d9000790081094460801e58680c1c0100d2240c0420826103242c105010f040009013000490311100c491074800130070042c40a134400c7d06002c20090700c06815120420301080c25990303800c02c000024520121201e03520004c202c081502c3d402d8114041c0c0c42a8502c1d500003a00c40d000000c48250103181e84c0130404a541540e8412101451228541081680c24032103800b40313000c4c2800400c003031350040c0c44250803107195100041110031950001c0b4104141120b081032a81d140c12403150300b01c03280003140c2d034496440c0074201c040c600602d80710700c1d880f42c1050084002d010709a8000c4580319114800e440708503500307440550659841642c018111041c0c07407a24482d083c0941d00c4074503918419000032400e9a91101040c0c6180c0010044908480c2e403940c6101035054074a48103040e040a1001440c146860316000d1052003001d00c04a6020480322140c400c10040f03d141007070114040108002807030642820011880e510489003101c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 426436492 1250 426435242 426435253
    0x40f0e06060a0509090907050d060e010e03070c170a02041a040f0c0215060d0615211101080a0e0f0c09090105130222141510080c1308031605 62
    0x91070074030808403032060003162281c62400180030141321003000c006014502038052804085207540d10710594000300c41c0140d002142c404800700740182150300c600002d060b56802048102c00190300c1d1908441100d00700f0741481c50343d000c0542d043c2d0400c0100e000c002d45c0980303070030075040703081c8840c0c4000341860000b82c40410800c2c1d200000f40c0c04542030705048001582c0030354403d416040c0030741021540010054031900400d580c50703460409454541400c41410407a042062008240c00040c40c50303070648000a400d15080c40ba251050a03503150640c85041240b03501c002040500d03d500080c061086405c122114054001c60b150b0300c03011209401071041c440f80303001c1030450381c0502810740182d0440895803c0c86459500300000721442e40100d4101900d0701c445090b03000c265100e54003006001003540010380c6003103034003141034180802405110750802003150640980c001c1d04203610034501c1800d985e5070110320342d484002c21703a40c3d848410180300028213000358016407154084610310030b10450340b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 426437742 1250 426436492 426436501
    0x40303110a02010e1003090501051503061e0a0506060c0a06020426030301090b010216030b0f0906070906080604060e130c120807060f06080d021e010612020f010212040f0e 75
    0x1d4a030554144003a00142404a0780d070341038681025600703803100d914100000c4030050340d50b40300e00351041114003905c00810091802c0301400e090000551003086c0e010014401040011640c50300c1501030000303000715613160002010360300c5103022a8505c0007080116034014165282200c0a503000b030052a03031108682c0c00f400c00403219070030f50015108810000e9070841c0e081c0719811009050012443d4118400c0442c030f007480c0d921043e1200c01460080c0b600c404507180c0f524032207a4010001d0300c4086950f021404020866a006a40070f01b9030703086190400e8140c40d810001405054980c02040803000c0400601042c40015040441c901c1e00c03800310a086c071035039840d031650300f81e41b84034000d88085410442140051002c2c1d2080c0f4140801303460001c0e00e16202d0511929000c40a407100d805603014480d6a01150303460b641e0404943c440388000e100c0c582c1840d00302c6084401840c4c000b4040c2d404a80d0500540c2e000303001c8003130140000c0001c2074641d0340e12060a07201410f14405c000f00b00ca054800709 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 426438848 1106 426437742 426437777
    0x70611030f011a0304021003050415140f0615030a0903031811010201050f060a1802040b121501030c0c0f1a13020f0f010c0311010608010c05040303 65
    0x81c8940c14801d100e41c00c1c0406842e0088140404e00030800141c3c0c0d5014040c0e0721301d07403903c1c2c08580740e155444e0024511241404241c03400d420403007103080c60402401c40d103204099868103a04580c9800c801d00100701d803001d90001003600104000342ca900a240c0164800750710030f10b400203110014402c010724010342800d084074400607043d501c0030a5a424002d20750001c00545401c1d403282444000613900e86c941303110380c210a0003000e5000c0e100780c5031781e4151070040138100e203401e545000030800134000d224111940710100d82d20401441c0c00c4d510900c20382004546d90303226012007080c03030b8441d060240e103c43c500b11070710150080181400c030059001c4ad800b40145180034401c60200d881008407036041040034034003915120030a0500f50381d105484801c42038150030a40184e50650303108902410003074012120355824281c041e1503280c0d0100041c0103c90207680c074030400c5205190b14 = true := by decide +kernel

theorem cover : BRFrame.Cov 426258992 426438848 := by
  have h0 := BRFrame.cov_init 426258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 426258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 426258992 ≤ n) (h2 : n < 426438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
