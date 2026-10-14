-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3300
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:15:36.947997+00:00
-- url     : https://prove2.me/submissions/65aaf030-c983-42a8-8a6e-09664039ae1e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 593345323 ≤ n < 593525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 593346573 1250 593345323 593345369
    0x40518062a0313050703061e0b030a03030c12050103080306010314092a0924030a11010c020d08120f0a06061b02010905060c0a0204142509081204 64
    0x12010a801d41000307800700025103410316000141d98040d480221400000c02103548160070000c05400468200c1c1c2c0c1ca000b0203d90452500d00c80c5034035450008200856046d0710000f82d27842005070f0008080544400d400440035208000201242d04840030910240d6101d180040c2960821030307040307000a150140940b03007211100c00d42402021210083d00c0320f1204100c0c1c441c0c0c6500c0210b40003154407000f400f9082d040d01e6604a0502c46c2030303400500d451403400400c13000c0c00c541d0140e0031103219600c00d2080d100840e0185244994561090925101081051020600f0747c1a101c2d0003030502400800c5140d01a030404903641d1280c2040c1c03030250025038521400b94203e41c80e0707018280014003540c4c041e540c0d00f081143c2c509200c500506210304a5551507001034601e50082822015a41104528100b181882d000303041d80100e82e441d207a81c2c0ca1600a40041e007991740c892000b8035040e1884500d54145009551010142c030343e41042d00e41c29000400c2c005d40941c031034840c21310b46029041410740303100c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 593347823 1250 593346573 593346601
    0xa05070903031d010513090204170d050f07061103191d0309060d06080a0f0c06170c0a0c08030c070506060d03050a0f05190c0203060a051501030e0a0204051806 70
    0x250326840300c2007140b002c0403540300c081c00e41504684c10700c80c0401c850300454000f401342d10002c2c280e4001c0581d40360309081540c9075000052080c2d506079440b0303441500c11980c00a090303d0345140d9060803551610b986040c144089d0441e0721002e8400d10001040c011420880c500d280e076840e001d124103000c04034030b110a1701203c1e1501040e480284c0c10034410001c0a1070504024044904403560105032903072514403850030841040d408403121281040043c08000b07203e041d8200070180360a2641c101070360f0601c1c68444c10320040c0390021590f40001c62200107801884590405900401d40a4881c94540040d01d0703a6400104103403202e1052400241440c42d10000040b501c560651381d01c1d050641e54041500d05500300300d00003003448028040f00414042003d040c5512050541e10100c2c5000940103041c1054005441207121a043c8420044091303540c0070071030301c08803081c640016040c120410183c14411000d10081d03100d4204800c1c085141d550f018170656071140e0000791140b0752244c0d402881c002d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 593349073 1250 593347823 593347829
    0x2805011d0702010b100c022106060424060804031706010203090607080d06060e12030915250c030c0501030507141608031801230105040b120d02010507030c0201060f0e1e0c030a050709 80
    0x20b9400100040c15504054010cc03c400c00300154a03101808201c0c00c408040015400003400141070b0350401c03061540c07010702010000020b4541c44010308048000030b4403440ac05280c0e41c004d210014075101041068402c480b003100504104104068851000500e1407900701840b038480d075101400504121004003c681500d00024490803e901035111481100d40045d1020100d8689a1072500745003415100c8003c4c15038414554950041d086103006014a400354100700c0c10940342004221010303400c440d1145540041e0004242c40c0c00104403114010049076a0080c0300d2200401032001030040349040882e01901000240110502c04201340d02c1010718590280800200c800104943d00f055802940341800140c469900100b00e944410300c0d04440302d0681c80180e65a070300308402554184990705003820f10f880280803c1c1d240c510680105003881c000c040700f0b088007402081c10039549600e10b400f41200e5000d164414503040b0b00342010b60b08108c5403104410f00300b1000030b01c0c551040540c0703420707 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 593350323 1250 593349073 593349139
    0xf11010b0f04050408070c0b07030f0f050a080a0e0d02010b0301240911040b031f0e011511100e03030406061d04030f02010b06032805011d0702010b100c02 68
    0x10030880d0200b2010b0003010f4000c2c0c0c0d94000401020011403240340f40100a0311001c1e1500381c0e60702c61340c6401080c0480c3c4c103840302d00f0400307480016511a5800001c4801c0380f80c16107402c800350f491310300f032510041064039112200d91140b014000c60003038044d000b82d0781e2a0000c41c000c11083c00c100e807100020120a80c81c810442000c0d000500003456103502064007150b071008990305180d21140e18004981c0107646821819405a6119030650000f29900c00540b00341c010a0545524105022000c803000b8456801840030700c142469180340c003005010107040c44200280681007049c5d01107620307035200342c41c265421800d00d200070540003101032643c4412250001c00b90280d644503113044500c1d030b030351210402c00c44d500c075040030700250340d030364086d501552100014000507c8820548900c520441c0c41c414003d5003801c00411018400800020f0120340103162800c0daa6509482240104a04bd95559201c54402c1d401c5440c00d1b0300c1548070200510a07682c1401c0030b9000c40c0e03602c003442c0480c0001c0d20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 593351573 1250 593350323 593350339
    0xc120c031b1f140406080910091e03030b15040f060c02010e090a090b0114100e03060f040f060906021b0316080d020d11070516080a020d210f11010b 65
    0x8141d00000501d1000e0101840c01058907601c40c3c07103a40c03182e44994450780000c0c1e071a0b0140854180c1c144440000300c0030000c420012680d85a0b6128400845940c034810750300c50b00d083c0d130403c1c5070094205c080202d00c010210b4216050b1f849084065402c1801100340c20500800301086c41400380018881c0b41350140c5270f64510058034001c014802c24014203039030049480711001800540381c0b020490203030022602810011801c8000c4c0200038094082402c200010340343c0011107a01c000c00d80e281c000440b2900d4107e96502e9041c00004212a44001800310b46021509018800140d014000f0868441c3c8030800c000d68070140942c0d01d01448868180f003c403041030075000500300100404100d183c1200160070950340005103000c503096980f0191407110000345000800800b40314a940550a01200c1e01103c0d05051050b5503581000744020300580140c2424014408845507401c070720125056440c000d441e070100d00070581a0441072500c049000c0100e8502440320600410410321005003c0310 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 593352823 1250 593351573 593351599
    0x506101a030703021b0c030d0315030615031202032203080318010f060315050105060c03030a02030c190e010f260c040b0a210c1704050c120c031b 64
    0x5060740041e140c0b01c24982c2c200107040e080b030b200701024112000100080c0110704410030030300d030404026484007801c041c9052030181000381000d9400096941000000a85000d40d003400308100c141c07500007030601c031a0000055941035000008185142540c0c0b121050200000e4049646409500004090900500004d00055810701030204000c580100110f10b165021560130b0440b00640c10075120100340c04104002038120340102401024155586468107000c4081d4503101c0c00084e140d0082a85c0000208007140444c005440f400203a160811420311622078010300011442e103180c5000c1074144003404011070058000240a0300c0740071f88011a884480050492264011b24880c40800280004102e094036100942080c05203500e400e041d12510611181c9400703940c1120711103290400d00c0501500350b1115400205103150200c4486580702c030715045040c100c0e480d9206420851034510800f6103800012140c0540c60280c041d01c000d00004043d95807002d03100006181c0040c200c1c0c3c406 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 593354073 1250 593352823 593352869
    0x70612050406110a0207090506030a1214070206030a0218040c120b1807021501080a11010c021f05091201051521010e0a120f020706030e1f0504050610 66
    0xa1540076229440c0000c40301041034000d98203820000e820790050380052410b1045146510855400c00000c4005110f000c202d5940e2404112843c00f5520401a040341d41001e0030160b0420340352890f90080049489141c0070341d4441c025000240202e406032041e1103007030302c281002c0c030402c030542c0c0540d030383d0741c5074079010300d000c1d8014010040741d05410181e90762082818202c000c0c140c5009403800d6000e001210b418600b208003070300c810381200b0040e812860102d000102d420b04607000f040c0082c2008940070b101400050b01210603156482c4a440b44001885a02507000c2d004040049007120742c008800d40851109003256800c5076482200022480000c44074a0020800c00c00408c0d400021035000750201d0030035080d0f40d481c140000080c5d002e1045041001030318003000740305010910b007044082d0b8080d08025a14901d9200321014140c2d552400350800c0c4080c0070343d848668070341e468128010fa04a8100d0028001205c09480ca402404041009815100c1045044401d01e0704019204803480b554 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 593355323 1250 593354073 593354081
    0x201080103020906012f0d050c0d210207140115030b011406070f06050411010507080a030c05090604060503040c050418141504110901060806030325051203040c08070612 74
    0x40d031390601880d0380f910303019050308480a8240d225060540c51401c1180b402d030714070b4588402c1c25041408818404c1070803840b400950480100018a403089000c4007a003074120100241e01c0e0108000c600010386a0244114548071119444800000f002103103601603000001c0240c60000402c01540f00c001002001000d1010782191000101a80e192258136980c0c42228000d02d10110340301a12501000240510780c21292003440082c00c04d140780444698a50800713118040d1001d050541da0308141c4501031084041d12121400030349866500d546920b0044e200c0d4004480480741c02a01c2c80340820207007042d000300782030b0740300003400d0002035030841e51100401e0044106600700c912408404141c1e1200c1000c8050046000d070440b071300d100300440305012003128160440da0a000c25101441250380b03000040380c0b00130401c82c2001141c20722580d940b1582c080348282c041c1a5102d07a2030703100340c40b1104d607000314005c80c410404e50101960712002c040c0c81c2d5800381b1a900c040781154030780301703e0300695401c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 593356573 1250 593355323 593355331
    0x609090b0f190320090a0507120c020f010605030106060c0b040f0c030c0501080a0e1b063709060203120c1903051504060e1b0c031c061202010801030209 67
    0x3000c001d40c40c16034045560140d403500c000060240c0740c039040003401000d410b942030150480d00c2800308803031044045a201140076040c600721a0752800014681d510520800e44120003e05d402c1c401c0e1110110000d42e100030801008840d540b80400c0003410b0b1605105650480f00c854850340f0103000c40b500c03140452100204143c07046540744100d0300c001040d491003100954807490400021a04110004180703450062481030140c0c60520700d45000c6800050782c0c7c02c034090515290400b09058030102d000c80c020b100790302c4070314400748194203079000c404c0c03c0848560803211a150600c03103d078a81214642200d10411016800402030358964500700400b05510490b05810311b4a0040903000d80c0048409a04240c000259610244031401401001e031344c814441c01c4a041c8040d40c1050980d0010060140c00b10300003d03d03403181010a82c0b0071000b500c40010888007920f483d500381a800403d800c40902403a4100b0745003d00114403050000448101c15030107039240c0051780c2c00c66090001c140d601030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 593357823 1250 593356573 593356579
    0x30105090114120f060412030e0a140c060304121103030408030105010c030905030a03030906050604020f0f0c010627200d0e03091306170616050304020f060c1b0a0609090b 75
    0x2c0c140c815140b4100303c410000702d004e0f0002c00162600b424009112586034121604060a12204002070400005c101d46003a403c140c0e000c0800748403050780703450403403207041c415040316000c010001030004500403038900c8000e030384170104101c0701c00d40e0941d01d80c8011940103003000e6080c80103120f03a51213001071050f150310030b013841500c058940001900e0082e80c01d034209c0000f0748640b0701d501041150b00580741c101d202a201035040000d0300034521414020000045050000442c418901100035081a0f000b00020031f0704088440c01200034250b02e1040344a0400e102d400e12610a5174030021002031042c0000511b20107003820481000307000501840c08071012148030911020300a540e4619401d043c85010006c001841d0386020021a01c0b0554110700602c44c1c1c0050b401c204d4108041102608491641d15206640341e5941c03000480180310000400c0d041030010a005000311800914041c0d50502004451040030402e01040185142400380d107001401c007417010810030b01c40d46c101c481196401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 593359073 1250 593357823 593357839
    0x1a06013c3f050a0237050f070c0612150e0601120609020d020a0e0402030108030f0310120602181210090525030b01061704171b1b0303030105090114 65
    0x109101c4401e4401c10342d0400070969000035105d50030344085c0d1000d01032111504403018891100300381c1c003a40064200d46082444000030711441c80043e000c0c115a80035034410160744505483c1c181c014058804e0700c00c100030740d81c07900002c0031584025020020403101040e05540b00c0e5914000110f41100100c0d0007003648544448000c43c4034200c0d40042d01020b280c1407801a110600007400500c804c42e11840325004610400041c07200800100840e410f08000600b640da49448102c1040390702d41c0703039a10810750700780201d030358a08100d0700d50010070304c0c6103c2640d04810040800100310700d100e00610f040c5416071026090701c64015158004540090180d020f44103881140f90740000321140e0349030a05140b640b004414801c0144400d14140500710504c0e006e050405e100c8083d000481009e000a0300024482e10201080034403002102c000c035003406c0208082c0242e0034903682d5102030340c004080300981d0a0340740c0c0b400f03802c0000660341242d030001c12250a0764600708034035500c4240700000396042184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 593360323 1250 593359073 593359187
    0xc0d05070c170115080d200c100c1514060306240a050406030f020a0614030103171c0915020702010c0609170705070e010506071a06013c 60
    0xc0044c0c0c40050450001604c00001c0c443c038001c0c5051550001c0c1c04032080000011008a000040c0224000344265010100400110802c0e500c0702d04647c8001c00c480280071070001100c83d2034100554255014107003030010b8803800b0406495550407078210480f601b0303c81d102114094165a401c0641d40040c080600389a15040464140d9190340c00030f80e82500095035003c1141003a5034440010034040c640b600026281e040d00f4403880c841032002410036200c003980303400b8a260080c01c845520130343d0364014518448114500c00a00b000a00c162070310350f20008880521159402280c114507030503562800e000c18944c0d111030040054510545030882c1200d003000c05891200003c090440c0208000c160f060314003100100715100580080380912800c0c4034220000b00c00141d038104550800038000c40d2541e80300c1c012a10000628040b01c04e100380d90140ca00d820700c00100d07000001d00948e0700c0706e08041302620107413041034242d9a901403114200d8415040c131540080c5610300318680700519184180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 593361573 1250 593360323 593360351
    0xf08060f0a0b0a0e040212070608010b0f0d020a200102160339050d020111040e0a0f0606111b09010308070f051e010b010206060303031f05030a0303020c0d05070c1701 73
    0x8555040f9000131002c1d9030074442035141074080984104160340003804d10341c0c1440700081a0b44410320520600a6011420013502c19541d0203688220f03440c0b4600b15111100c8c0c16006114982292008001444d0001c248441900c18003c44180c414444010083da00c41903404540800c0010f01d080c601c0c040300040708a000841c1e0b11007000b01d0400c681110200061418400d0805165070300710025a89442d0185886040300c0007602d04840040200902a541d000d01c0030300a06104039400154600c0d01ca800b0440c0b640141d01200450440403c807483e04000980b0001d40f9090314605a91210544004000050030403004100c03c51249000000302031450f6a01450300c0c41841034600302c10b00341407081182110034800c00d01c10703802c248010220390424401003a20380c0b02c0685607007105c0c414140f02812a207800311922004000180844450004030b00b07005000350403000e0ba04042e800307914030418403d44502c0540c1c28294200a01859442c540061610804500141050b9039500d402507038100318 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 593362823 1250 593361573 593361589
    0x212160b21090a0b010806070e010f050714030c070f08070506070c0807030c090e010209100e010e031005071808100203151809010b040938090f070f08060f0a0b 70
    0x500d00001c1c403d800041c54040c1e404001600004584d62021007004203441c1d00a50f516215102805c3c4000d9409054004036014450488050052000d100c1026604030380000141543e10155094500898503208103000340c526502c01d800719940152401d1040d8540342e0024400e40f80f0986818036500d50b100d0060342001c049600641703140505100400c401c02c4280103000038100c0e66002140740100405c0020b40881490b0030010400c44c0001280a1a034019004061808030040071205024417103c80f00016000403a040c0000900445000074004080d040000503603044002904503401c050100c00002c1d000100000503542011103442495200c000415081c500c07020082401c0b8039002c82c0d0b82c3e0a581c3c200c409103000d1864000200041001c50300c507000e102d0200000b402c410034000c1910400342540c141460700c00d00f00e684c1403000995000846d64980400c8006442c14141d88109040f100c9456200c2e0482640280700011150016440300303561000c42900001140345420000c19410 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 593364073 1250 593362823 593362831
    0xf01230301061706010f08040c09020417070617070c03020c040203040f020901050f0f1306051c120813110a18020d110f0418110d06030212160b21 64
    0x2811000005005981c0d02101c403904440300c00312064014100381000a201d105a001c201c4108940300c0c005c10b08001041d03185034018a101d100941d1140c1d01c51030011035444084241140620408100007119070040341e0b615441000300c0c411400f2a038400e402601c00142e0310104804502490740030801c642c1c2d071440070b54021401a440f04030459600c5c81402440d01707040e00120312415840f20000034076070b98040c01c55000303070040c0e07541c25141200c45160000741180d50800da5110411030f02540e03202c0e00c21082d025030340b8040c2c5a85241d10400c204141d440a40503580710081d0308003041c58a02140800740c08280c100e00240110b1081541c907900340320345480b1440003007141900000c900721740c20118003c14400300d6025040303e18244d810640990710744074034419105490415041c1e5503c19071a5442000c0d180140040d00b0358400b00c0560303501c000e28080c04100d120703540e0102c0106145900041200304200703220140328135241080d101240f00c0e0448088450f040e2041c401030304400308107828030707405 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 593365323 1250 593364073 593364137
    0x6040c0510140a0318020a0306091b0608060d02031c050c010c1103040e070203040306150303120b0a051207030f050706032706110403050307030807080c090a050f01 72
    0x20a410311040000c102618400c1900700400300181d80000b07604407045514003c460f080002d007010300f12002c481350311820240a5808498148000140a15030304810501343c810103c000c00d5809100080700b107600c082c01620005100c03000000c402e407c0100444030103500003002c64185904d00300442d41003440021020f00007420116080301030800902600280c060075040c81183c040369681d24683d6401103105a11140303104501090046000703200300e501540c3c00c003000b400b1809003a50041416182c51108500040718150303035104241152040000c6510001c180c140d47c02c2c40d140401a001c202c052040f01c26003c3c03001c0020011f4040105011342d50300c90700103405042d01e0003030098101d42c1c01c1100140c070500c40ca44101901c141d0b40e1300040207550b01030b00004180c1580040600d1500850308000c0c180d20001940030141900600c0f0648110300303a549501c095994844184001e0003080355103508060280d0701071289241c00c8410140c1c80070185080c4d2044a220403640100d40c5440c5a4105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 593366573 1250 593365323 593365343
    0x1505070c0c1203050327060c09180f0411040b130f050c03090d0f0323091e032d032701140f04230d030f060f260604 51
    0x108030310400720800511a2000c1c110860010342c401500341d1000520610800040c10400310302485071800229411407030078210354203803501450208142d80710641d503500c124030500700428103464078508039101da18807074080c209980f61a90303083d518240c4840302551003170b1100341c028640d480b0fa00c07003100d066420b81d0000c94507021550524003110b60241807030701c14030820010400c2c600e00000d0a001c0c03140b1140707081402420748200840043c41c0f1a14006030981880340c0201c020040f12300e101780202d10a00503580404036140b03044802540f07001182001d500248507801d10407895459011106001034141410490400c08c00441903000b11919000b542c0100044100580403030005003c41003048020008001c18103081c00e4402e43c000c241600e10300701203000a00300080d607041e64805008050f88410410f58075043c080d103810307001042c2c00c006842e00f2849038801e401c42c001e480c101d41840303114820702810322400924201c04410381c4011a0190071100e80e4028042010500c102d0040c05458 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 593367823 1250 593366573 593366597
    0x1b02030313030618035306030f0c0d051009080c12130e2203030c1206030b1f0b0403080d0c0f02070e090a0501050c07020102010b060f070f150507 64
    0x801210204c602c1c0b50854808002c0980009401c0544440781640e640700c14015060110002410040008428400d8000041045c039011461144a000180b601403a040e807030364485084c140da0708210034000d0310541c04181000c0c1e41c1d0400e01c0070b150019005030152484068000404000d41d8450003084900c00c200151040c0c0841d014020102c1c40d8083d100b610745000f06d40414061141c00764002d080c100c820a001088a00a4107020404503800103001c040d803007116410007400910f600c22059010405210032111890018030480c2d054a6000f60458020746410080040080b002001407080c115084808500d40484401800c000d6110300758a030b9480b10074403146002d985c0d08444160074408010308400e1550b802080e0381e0151000316a41c9c886903983c52091031b152100400018049501e04000e10480c000d84900400c9aa4000e800a01200c801c90f020b0001502c58824501b141000c280b00903030018100081241c0d03024001e071520b903200074011003c902281c00558803800412070041d00d031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 593369073 1250 593367823 593367833
    0x2061b18060c0c0f0d150c09150c060b060f0d0c0c020a12020f06040803030a0c260912070b01060305060a1d15040204080312090a1211060f06010c031b0203031303 71
    0x40c04500415141c40c040c05400e070303031100c5406d0300810b04086103c2e1141c4980391490320800c0c41c00c004250102e000b07400c0790607105002d40603140c0403c080d074a942c00e04500400600700041142c00c0090084400c41c5003214001704040285107444456003040300304d018040140e9101036a0754094a041078200342c1801040c81000a0784800001090190401b0f1000b00005440403040e298010036142007c24000545082106c4901d160b0114002146401c0348026141c1206c0324503c2c820707003503681200d02c009510504500140107111004101e100c095005110709441b0b074003e580c2149001d1300300c500c0c0c60380f00c100c001103064109241c202100e80c1c45040103400034004150a6400906640c11840c1c142040780c020b40b82d101c0c40500d500a1042c42003c14040c01c01000007509a541209071003000880f1424014007040c100b007034000c07091169001003407003501341c41d16081c05900c4c140c41d00642c051655805840b500030115511110441c1100e142001da101440204003007010300d08050001800c40c948 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 593370323 1250 593369073 593369089
    0x50a1107030c2709080403060902031204091406030a0c060f020f0a140d110c010509060f0307020a12030c0c03080405010f240e04050d210e010207020a0602061b18060c0c 74
    0x981d024444c140007480c8042441d5804841c00e50380c012001151000543c00405d1500701042c0800c0b00900700007130005160b1000798031031641e12032542000c400603200c0700205a92068020006480c42c541298200403d9004004001d0b000e0385a0050b40d0070320651520b6141024426070082d2811140c3ea69014041c0b6420b1100741c02103e05820030303a040f200d02c0012959540310145007107040c40303000544102d90b0b685079800c2d5000c8441c0c507842e1541c0d03468107260003901d483d40401c0444155940724400f130202e0b07000380254503001d5401e0b0307920707030704070311036860407255014040c00c19074040d50b0b10011007807051558011944c80649002074211640542030784080310380c880d0b0b4084030081c5082d0341031000041c0041409003041c440351522500c044040201c42c0748650f148075240c6070543ca4426584040c40b81034003d0208a40201c40703008250360b450800347c1c0c4405044a1000303a0404403c442100142c9400161116030200503130050b1a90405010510301d5000421140c030913804424080329926141130 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 593371573 1250 593370323 593370389
    0xc09130213030b0f0f0a0e011104030507060e010503040503030703020706090503031608010609210503120f010501033204050c0312030907080106061d010309020a090e0606030d050a1107030c 83
    0x54040c1c65403500d01e00f0485d0f01c1c2c1003d00901407079030312000c0396001d0302025000100050850088607607900d90341d140c59652151144900c40219904034040146513018034242c038030941c0c1007000355240d40d448180c01c41c02980500002c07121140c6d42e10307150010400420246d8031642c030702e58410700d800c171450030080c26104050b8040420031650f48401d11094585010b511034000d100d01000f00343c0012840d01d942180180c91200020b0038145e4100325400c000f6100f000e040300d20a1700e007000364905030f103080795030120100240700329089907283c0c0040c81301c9090070260b403142c050340981c1d04c42da9441c40040e08203003d10031075405807640030007800103400091007140002d16114008014044c5010406041c2c0c012500d42603081040c02d82d1404c85070390003a0011100964024149140a42c44100590041c0402c00114210348a924002010303030400040b44003004070903448041c1003030713802d8904550510159064210030b018004c00080044c403a41d0100000d402804040c50340260054148091811541 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 593372823 1250 593371573 593371591
    0x203010e0a0501080c06180a0504090308011401030b221d0a1505060906010f0504030b010b04170105010609090905030c07060201050f09010902090601030c1116050a060206010302090c09130213030b 86
    0x20344417001e5542d40b81121800034440d44940329041100c0005900c00020303610007604603081c440e1a030100350748903140b681070b2200e101c07200204d01030031401102110070005102c0e4112100442e000100b182001001030512503400000c26800c40c03d0000039484151400c401450f6071181c01c683c01002905110391100c0101500c0401040c50480300040c4544801761043e410700414031100010340307101d43c0403100510703001040040d40d0b5035110400581a4400e2140c40800e1907140f03480c44110f41c060103664102c0d071240da80c1c081c0035401c0c082404000e05e20843d04030380c0c0e48010002c59424800c14000b1400038040d80c3c0000036035141c150075803403034807070000c190407143e901d4491f8200c0141d46080005402080070318001540c1104440c2c103541d6044400040f206a105580c40c513451031040020a9058420035a11030380103640d00c0710103a942e1352007804000d6000035440c0c000740d0074803034141c080c6c4404c0c2c40042200c007140e060041840200e9026080384000c01d4005c0006006000c80042c415810800c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 593374073 1250 593372823 593372833
    0xb0a24050f0409020f07141c180e091608060105010305100806070f0924200309100306030b0709090606050f07150e1f0e0a050a0318090203010e0a050108 67
    0x1904072402103204501809400b030344d0214075481105040300035a41c0090740250035111814003845101e40c1d460603014010b4041c2e04613242030031018454414a001e5218102003821900d081c0040c4c3c9009000007000c80c2c5030351207076100007031100d04481e9242c001030001c140904012350500300014269600184001c0101440510030400442c0004090ba404030743ca01d480920084002801c448140996206c44030b069400c81900b548a0800320081400d08400d071030310352505c40700140003070031030560030303206459900184400f0b1514209a0300f07254684103035140000700541c0b2a640e00f04206400e9800400089401074188903e10140c030550014190300d0070301c113060400c031104e1010140b10f02c81c40100125900303801004000c00c540c009010380c5180f00166021420140d101003490741108001c580c8881c1841010500904081098403da981282c050968500151802d8500080c1e200d0700300350322684d07540001610700150ac0514040c2501960300b004509045154805840068104803025008 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 593375323 1250 593374073 593374087
    0x1e0c020f0d0e040b12031207020601151b0507180b030a08040902070501090c0b0a020709050411010c03180b091f091202180703060806010b0415120b0a2405 68
    0x1001503980741001c918901202034404110106000e8080040b00941220a200310700400380c01c0440900301e41e10401e1070070105581c0c0e0010890740c0d01001c1c418115502c071009041c0145520a54000c03000081d8098007110048181e030310585081d413a540040c041c4400446164007202050003000240c2508900521440b070b06912040a030384251300ca004c07420b6500055643c100b080a4120700c0d0070f6034001d801c29010795075030b503000219540f040604500600500b100820307048660311030640250381020000314200c0f1207400654000003003640582c28400d5049205550410701042c040c0a000280e944035210010b00d414001200c1132070300408003481070004002800380c2d1140501c81110980100e000744440070380003041e1454003202c40b5166050104c4100606541c05801050850b45010f0894041742c3c0d031032400d000c09000e180551130b00903160320740d240c0e68103214503441000c00032605000100d41164200141d11041182e12441071b50407d000c81d500318a40c29842403014480a0802e14580300f0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 593376573 1250 593375323 593375353
    0x106200601080312070c0605041b0905010305060105101b081903140610090503070b040503060903030f07080a060e0406060303110304050d060905120409151d27011e0c02 74
    0x401403201004c0704003400044805100303104004c0642c0d04520108158101810b00310b60300b8400b910035420f080c061040010700003100c0d214107812281c2050190030765034200810822250a01b1900c0d00420003141100082010504907010b0300c14031515039030340d650b0481040c030240c00407403027101e10605142107250445042424015a44040c00701e4004500d1105c02c807003560b024405401c40c0e42c00d031040c54000f24800076a44028815900300310100c414a547c0c3c80d0849a0b48d02c0b040b1000307442007441b8004114054050180941c0050646a02050700785d03d81408072620b040889013580d00b00e494050030418075410203444646403240c1d0001e0340c58507092501190b0340841c410300080c0581c2d9030306001001e2240c180124030a440d0f51000c4503a4903596021607002030301070b0b215052000f440100300000c19401c126100340c0031100744400e200b41c96881a4800500b0340302e540d0207100c50840304246002c10802881026003000d182d480070108180003040f0360003140c0b08400070700103640c0f081038421806e071 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 593377823 1250 593376573 593376577
    0x20114060a0e040f05010e010e010608211204081b0d03052a0c03040905101e12020907110607020d021603082a031605060709030803010b0f07020901062006010803 71
    0x203a00304416804c400c9051400c035004106901c000d0903194a81440c500c00c2007019000b120845a0542c1140d100b8840080040c0b1041d40c0280440341032071007081000312000c40040e42076403290040074118104100c0540402c0003010802441500740c1294482072040390b054030882e9004a06468000c00410b42c140020400391101d035075a035110540469244401c420420032500640645842846076040500320146400c203107001c2c21600e007a1500003c14459401440082100c0b0041e0822066804a4007031040309034020349441c04011030481e072040040020401c0340d0090109078020079a001854000a090621810701280f140307030051030810124410740145c0e24414150702600c5440300c0c180071825003003905500c516030113010201e008481c00c068015800000c50142c010754005641e000d008564500c0c1314003004110a20600040c400034407044043c200d06407207070308103510300142d6400180c50390509a0103100041c44071101e40c4050041d606d02c074201100c1c044001c203001d50412652545178 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 593379073 1250 593377823 593377831
    0x9010b071b0b1e070609080403032615012c04060f0b1b0f0a0605010e0705131404090c0f14010f020705041a06070302070509090c0310020313050607020114060a0e 71
    0x80a8103c59a00030301208600300c800c02c40d84540c0410034851180362041458015100030390208294501d910b2000d0b00040785461140d0000c001780c0070784d071707100120305442c0a0720b00140c034100201001c0340704202c0c1c080102242c42c65003040c00c00742d903410501c08010a4410a400c81d549209522208000088040e0b0070b0701c16003995958100c40565801e90b410303240407150096900f26205603026503060050701d602c038074140e507844000380c0c03041c0d40ca50350141e4142c400c02c0728401c0c0207849460104440c0005040110440c41c1c02840425001002d0303d40e81c1c038540d5160010440c02c80c59080030002c69413400c00c0080740c0a028240101001c5a802019445600e103115603130040382c4881c401c9160040104940317101c010000c1c20180c4400003818001c1d81c9840b2070042e107004410500c0450b462000022b504011007800500822443d1100701b03200c80a90000b800d103100308694440d460340041c0e0203009003440307a002076000141011200c5800c820715180540304078002c101082007481041e040001e010b40c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 593380323 1250 593379073 593379097
    0x50a0605030705040603020d080706090821010e06031509100c020c0f0904030c060209010905280503060603030a11030f0a020312150d030302071104020412021503090c0d03030b09010b071b0b 83
    0x12b50881e0305200001c0c00d483c11008114810004050b43d204100c1c00740c01030b441d5400302000180341c3e01e880c1088036409090f01e406078140d1040804ca461100e07501851070b4018407940945c1c1703442001240708000d460102e0038540250f004051072035410700700304006980318081110307603a00c1810140c07400f0307042c0b0300068405480543c0009161205074003e41018006210103132054646041c40e0b5200c603201c0e102c0c52444095000c0c001000241c074036001550700e000f0a80100503500c5d0603414241a03d04450341c81c1e0b46071583c0030a000e00c60201c06074201400040500750040d5540d039500309146010352400400095110107564401c0d0000d0f1075006512400f140d040c140141d854910341086280350b20f03c0c0300e4040c1d0003400002e0100d90340e50003452201e012442900d030b140841c1070000070304000f404111a1000c0300e5003d080d601080c0e29120403240b041a0090800180c24000b0b00e020410201c02600300c2d94105000081060070040440185910030400515404909003043c0400c3c41502c00c2c0125551 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 593381573 1250 593380323 593380327
    0x711032415090412021204030309030605090d080c0a09180203041b03050a11010e09090c03011109030a2402130f12050a12120905060612070e0403050d0e01050a0605030705040603020d08 81
    0x1800c140200310006141b00211207103900d455803031030000c11101c1d076400100c5d078035400c19012920b2031100161340c05895002ea21415015a0307080d0500000ba0060f4040d00100500c034031002031000d82d40300061180c46c50044000d83d5030302c1c16041c0b10304405000b090021040f441c040c410004518041455504258071051026103040b4100040300c62410003c4c0aa51019508040c005260030008102c900e5540c194001c0c41080b100c000701213250302821203001e4140d041103c0724400100c451200c442e580d2540c1c1c90380e68040901c40000c108036002104188001400c1d810140202d4010f0407000d07001b461440d2210704802d100f60395252f00d03119140d40081502545000c03a4030418094254002c9010900c0ba0400c440841030811a60341d20040e03906c140250210700a1003030800c40424540300303071014841c0341e0f06107803910f40d030484250740106080c13030320b6076624907070644010740c280551130241a0411000c95190300340310426040110f00e030300442c130681c40d240c42000107031541c544000310700e030704400c1180e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 593382823 1250 593381573 593381603
    0x307140604060b1503011505252013050a020f0d021215060a080a06150203180f0d0f0f02090109050403120c02071a090607080d060e0c090607110324150904 68
    0x166003401060b5a50318040c9c003c4286410086220368800d0301e950040c424140c04101900c14090031044c1d00042a81100c40d0151044840004e500403903007208403140e0061038074148000036007030350304000c580a038420f80000301c3e0180882c000080c1074100d007100003000704049c9400c3c0094058880d07540c20340144010003000541110080c0c2c0120003c1c040195405054800380300003d40329071001e01d41001e90002108010441d061208620500c41d2014003a003001c2a25a00d601d140c15034005000c4506524000035140182c17110100d5a000306809100070600741840d1031302510100703042c404102e215144c480251085a80001c040d4201c0d82c10345102180c0e800c041c1d8041c170041c0309104403590458000103004040081120091595202035501040596200c00044010000a4400c5030301c55000780040400f44c609000101841c51081e41c0d106641d00b22000400d05005072001c1106130410300c5c404004103607031100b2149512424141c2040741000355000010004003000e40041d0600750710f46548 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 593384073 1250 593382823 593382827
    0x102012a0306080f070f0e01080a171e04090e0c060a0e0112020703200a02030601050402090f0d060c0e010309050d0503180712030f0518120307140604060b15030115 72
    0x40103000d1a80a03140c0302d02200d01280e545650078450306e00404103001c0d0020719403140f000014161020080940a02c3c0354984550f186441d00e100c5d000c00000040180f00030f80c40c4000c089001c95600c034580329803158500b40c0321404444a039010024160001c1401ca409943c800040307512030900e600300901c0c013058000048485001949001564500c00510341050540001c1005480303c0700c0040000d02c0e4010341c0c100d40e2220b003411300003034040c1c2c003e20050000740340a802400721100c02400e038111403880603000038040304451805485040e511640c55007019840400d19203100d00a080a024415a641c1c5159941544034000020001c001c00800c00d5132403041c041d040b00c690103a0444454a07261000c1d40d8005030701c82400c6000c14103c0c10520783e07840c05002910403083c01c4018020200055005020b204122010b4240c482d000030406180018015018200c0c12000c0c040102854a0a4038004e0101c0c3c1208204a02c1034034194010906510b10700c045a05643e15890b18203842c040c4801e003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 593385323 1250 593384073 593384081
    0x6060c03140d0e0f010207210c1e02030102130501030b15120402010c05160609120312110409060e0103150209060a030209040f090809041116060e0312040b090c0102012a03 75
    0x92003d0702d020303d400019a489054000d070104901840c038503c80d076241c1441010300802c0502070b10010032100c2200d44042102c0e00034400400b00422100c12140749140c2c002400c982c0216480505103400f04424001964103100d205101e40d000e981c84880c0c0445426041040d0044240134803010a01000040031a40308a00d81c04030154000212051703d9035506041101184d54064000007924440c400110344000d210303403083d925055110750000d1144480148040d0500110151400c0410040064007070b820344601402050304110203040d55044d0326121b60540c0c04c141d183c1c0c14190050298014654440342240c840321180d080c0140e03a80f01000129010f003540d10b911032800da140548c00001c2c0005d0700c0080080400440c3d0400098618106c0454180100701c0d03218880705a15080d100000c5941d400310781c000c10800300301c82c2030144600e072600107407608503012602c0f115840305001c1041c0c010020542c10950074002072140e034005602040828260341942090543c0c1000000c030440e02942c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 593386573 1250 593385323 593385341
    0xc1816050f0729040f110907050301170f0f0f070f05010e13140403050405040c03150b0a09031b0602070b12070c021906180e040f0204020a050d09120306060c03140d 72
    0x6481c5584c945410043c0b07250b19501c0040e91000c1e00d00540c02e1306481d141c13141502c40c0c0c840717860b07803070640e424818030032a0302c0400c1d4030800140c0f00340c1102c2c20002204105452007088514000c01c001d44801040c9802c18003290b2003944e0300000450b040c06180e81244000200f0041698814121141118004007604100c000006aa42a42e05000515074010000c02c1500c000b03071030500c0203041440045040700c0b0f400c801c001420480c03075824031040c0345240003401d50f81c61501d028280d0946907103071400c03c00396000c081e1380200d242c10010025241c041c44114000c1040e10340650900200d804200c0300c80d90005c11a0b01004a51400039046640b0701402e8401c103003840f50f05031403030b0b40c440700080d103070701c00d25203a61103440c401050000d08640141d440600c41c40d44000c000400788083e60034000130303410401200040c000c0902111b40708d80c41e14862101058054040702d544a800801c024088490300d81107281000641c4846a0100303401440004420b40d10071101e5949000500c030342402014001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 593387823 1250 593386573 593386643
    0xa14070f0306020337021c02040f0e1003080406030b01030e01140a060b07050304032306071806030c0c0f062004050415260c1816050f07 60
    0x240c8044103010080d40554400c0002a0a4400d0715135440326202181030f00c58010b2404d84500c074440301816600c2c5c3c02a1074408864550404000c00c1020a40300380d80241c0c1240c0c21032010328900b00f2016451404c03050300300307141e0050074081c3d03815510f604c00d84e4030940c05250141a221400213815034402d0b4440c01c012a00c0e1704c002c1000800c840c1d042940504240c0d41ca1100509000020940d1000c00d011920182da0000c020740c0fa0a00e10ba451a40d000003480c80707211881080c0740c08040340c550031711401784540e81e035a032103401e24154452000f0002040d82c203c5d0080500d01b500e02c0036135540004004d840b82e81c00100c1058210120725004028141a03684581c02c506540c800350191411000a0310076141d0854041c884a003220a01c6400b6251520480b5145c44a03000f11403d2038800300c902684008940040d01c12499001000c40c20200c41240612802c1c0c00040400107811803030520048002854904a40b404841c45070102c1580542a07019101d5040002c0081c0c2020040c0e00c1905849054 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 593389073 1250 593387823 593387849
    0x71509151106060f01050711040b03120c010e07030b06010e0325050103060e070905010c060e011103090c0d1101050a09121a070203030106050d09080d09062702030a1407 74
    0x1640080866058000d900807034030481e004107031681341550990a900300b060f0f403001d0400c411034a0303602c1045c11045901d90032950f07503080e45400c0c1e1018040c242e241488002000c0d52100d03020005421100c0b60700388600707160011941400041c800e80f280380e80000003443e0031180e0310684000641400c04c2000321480b2035512880040b600c800825804044030400d803010407010795224100341d044a800c49403080005c0300f0036024071840d0300030300a0405441c0108000901e84041040050868081c8000d6402110010040044e8803c04000c081c02d60071040c1c40c132800b200300b1903450703061064655030b515040c40b40c0030034000030403482070410320010048002e650404110b1414003040802881c001c1042a0314544002440940000b007124102c0d500f0340e41c0e0b18500f201c0034190000902883c10202d80b80382c000c02c8094541c40c0940a20600c0ca4000c1d50001038140f8a0000c5001640210312142e5408040c0c070102400744e030340820070302c0503984c015140c542401c1c0720b624030728146040c0f40c215100c0d148030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 593390323 1250 593389073 593389109
    0x301090309080c010309120c1b09060e01091406061803060c0307091d011a040302131401082802041d0a03120204081c2c090109050603071509 62
    0x40125401e00b01c034640015115000b19110044041d40c0390024041c0030707402d5940305440100d201c1c591032041140108545080e8001801102455079055441400d46941310b201c14008501084a81401005420320400252185e054a44103031031001300755a2007600d02180400440805250717180c0800c0300142a61554034020100305002d420580c2d10000140c3d5180000c0380071044400030602a850800710314805a10744150700b074401020408060b404407003400000b0043c3c84426204502c1c080103003001c80c10360615480c80c3c40341d410507404a01d540c1d00c08031014010301c140c9007200911403074400c0210701d45036460010501030300706581e0b000526101c0d010003400041c170206405604503c20380d140000b2554821040003a4001c03070203042502c1d04483c0c40c0f038208644e08496980d00c02c3c0c0c0307810288050300c0481501e0142c0c040f80303d401c3c42070380c0d1080c0116800c1d24103c5182409809100010045400c0040200c0d5039214203006501c00c102040708280d1101c0d000344442c50041c400d4000724900200 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 593391573 1250 593390323 593390327
    0x50c0a0b0c0d0606051210080703323007020906040204030c03140d030b060a050a170a0209190e0112060e06180105070f2a1202060415052205030903010903 68
    0xc0301b0590003120900d19804500280c0c4138020f100c0803502d290004008160031502c03940a5541841a100ca41e41c1000d0403581201c00c05c428007130343c1d400c54803018182110441010203511004030505865a0f805640300000068001003900d4040d90150345c004010784c0e40310003160080c800d5400113041a00b21010000c100882d544002a41c05190b00c1600c1c2207944420b001d40940e0450b07280717148d010030140f001c04040c1d44103d01509071b080c02d51401c202c040c400400500403080040c3d92024849800080c4c0d64880c0c102080800020111058150300c82441d01c078006c0000481805240c4084008080b0101400034907000450002c80102c107543c500d081c569040c0b5108008140058119401d21001901460003080b001d0a400302544840510300c001c024800d06004501e40d0000c0d00d003612582a40104515035455400300e034868000340f090f401d05040c8172108502060b8800800c0d41082c0403c00c0791303469a8411440c803030840c1000fa501c84501e10308181180030f0088459015031800411006150b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 593392823 1250 593391573 593391577
    0x10915030c080706170709090b0d06050c340809011101140f071b02101103030c0711030d120c0e0607050105150111061501090f09050a0507050c0a0b0c0d060605 70
    0x3813140e1a50180d0041200668a203028200c900001140e4a40c5003080f5201040d0481141424020031008109076240c2c1c8000840340103507101300d982000403817001c41d210545451036075201a04500685804418502000c004107800340040090b100810305c1c0030140d006156603218110180c0003407001540440a413401c0c1802100c5851000500c0030100c4d540718011a04507100701c010700700202032039840b6024045462030504d039410030814943d0380b41804a406201650003035840c205002e03a142e000b0309180d01159601ca641502c246c0204080b0b54107103810849600072480d603c070010039002c11010050340c2044841480075001040002c05404101c0d042d400a845071521030300c031882c40380014004445000d04e400c1982807d40c84580481d40ea010000d845400c014814903103d00d085803107000c03207400014668030000c90b5944510902c9079034013042c000d48d5400040c2e442d00724208401e400c40b1680d10a042c02020b08849504800318810070754500499510708034141c0c0a004465850000600075 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 593394073 1250 593392823 593392829
    0x1509020a0f0302040b0a180b0a020a050f01050c030f09070b030a02130e0c0708090f0402160618030f08072f0106090b0303071202010207020a09090201021c0503010915030c0807 77
    0x9030401800300d441c60091094409640d40c00000e04e01301141d004041d94541c04030036003101c84003041e0000040c0300384128000c0c0000e2000b5406007107950319501d0b019103025041401903110f40d042c00d04111030781c00300c0001d0780e911442d10540844030b074580d01d0440b41880007a8000b42e0741594000204141550290001d00465112826040600782d4800b400c000e28030701038030048212441008140080f81d48907014201e2400001d06020038007404800140c101d9001d80381e200200058400d413003046c042d403442240e40d918a0304510a00c0800f80e90703401000c00c00da10140c0301c2030000e85000300c2d0030030b0310511907000080300d527600c1170188201d8401044003012803043c9408440d800c0a2002c20711030314500070881c240c00054000d42c1030413050707a10411906181e90404007159400d10810300941d0f0b6100d80d440040913071100002d900b200742d00009040c06c11501c0c1150148240705c15509000d640a4100c904458a40c48001660441035410440006081d8030140c20312241c444003040c00c060208500c412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 593395323 1250 593394073 593394077
    0x305040f12052b0309020f060d06030b0702070803070b1806040605161e030506032e05070e0f0108100b03090601170732040e011b0c0c03020d03031509020a 68
    0x20040c00400c0c00b00c1452050182e484104864940c1100c3c818002d810442c1203610082c81e41c0d4a04090001144140c0c0084080c16110358440800300248101001e405400c20903510140c41094100501c2c15945d110b005402807101c1d8010300090440303807481010285015080d42a05c030a0b0906050038000390409542c0c40c10100d200540c1c409050740034240a00194403403024000508130f00780020b40082c1402440c07160180104040d400e01d1f0810303c0c0001104401c48041007586442903c21002250307002481c06c3c040c042100080d1205540c0d104424000d11030919003080300c0d42d14160310f190300d00015440b80c0028031004c81404200c20001c106031b4141e8002ca241001d0819840300700643d034400510800c4129025074940c0304004501820411001c1940160540c400c0001c00202e02101e07104440300751581d544102c3c00a07070303000818064150400514003040754403001d454440c0e4040d803d12000307100e00c130f401c43d10904242c001d8101a0000c400c480b00d004c0707029a1100b48001039401003480c000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 593396573 1250 593395323 593395333
    0xf02060d1d1f020a0908031b0606012a0507081605040506060f070813051005090a060815040207050a02040914060a090b01060315151d24070305040f1205 67
    0x21090014074040c0d90015406194501c000381c2c0c18800081d1300414101040055070200070801030000c00042c100e2142c07a034a007121090040c040142441c10291402d410001280369828810403c410440442d040080c985564030070f052070074614060b0340b64000c0c01c0034014407240d00ba105240c000350004881c0140d4003440980ea4050070072240707201d218074107400164244640b0020551080240c15a0f204040e4245079440d1520000b520340390152000c42c0028400090311949400c1c803043c00760042c5507605100c411401c104d14556540303020182c04502407503010401d030043c0030701000f0118450380c000d4002c0009000301d08003c9901c8542000352001c0c0d100741c10100e6240d4007503104180c100b176000040888164281081140904034005400c484103414100105030301c0d41d452608001c410403a140d03202d9030030a20340034418040d03500001912581554050304084d4101000c65034020210304c2e0391a650384120316080c1d1303070381c02140c010441c1410020b5003c82c5202c80100300310303607440c02801190 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 593397823 1250 593396573 593396621
    0x209060d0807081b030f03010311030106060f1220120714070b090c040608010209120304030f021011060a0903031d070e07020f0f03130f080a0b040f02060d 68
    0x30900d40144000301054010000440403403a070030040c1042002d00c0c004100e0034800c80e10203e00e1070b004a0b1609618180010040007000000e00c51161191015002840014500000541101e40300b220741c5092069502d6110384455140d440701034010b024401d0312944e040360604806240d007048880d260007800107000b02c0c0c0d11034041c40000865909541c0e02c5450f040e0b0680d00c00b201540050000003030791250103040b484587e41c900400020707141490005072100130709401c100102e030107098040c2c21034104110600200345983d040c400d1b07a64040d038100764a07101d0f84074111813007001808040c0e0540900c80c103200a01e4483d40190054500a41d020311442ca491080d50080c00d0707080414820650002c14200b1406c00302102d0168443d466006880b000318559000314107140204a8404154100181150b43c0d020030515120140100700480a190fa050440855071000c100502070030083c0100000340c00c000407201e00c0c4600c80c0c2d000e44500c1c0c64200a540b064040d00c034292000e9048503070440c1003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 593399073 1250 593397823 593397829
    0x3091207032604030515040b060d0b0a27030302071115180312070506010e0a060605030f0a02040302060703020a061b02070515120415050703020a090b0c0c1309020906 73
    0x154181c9402c41c8401090420001070800ca000310350a501c42c0082c802d10000010030401e10481c5c0386843c00300a485d00501c5d1502d07150001e024024085441001c0801000c2c0200f010709121070350242c820500044d40b2038546481541ca000001c88024032142281d00c060308040e032680140400502c100740c0e0903998102c150802c541204254a5503100301014841e03070403d60b407500100d042400e805410307540c22440400300d072880c41e44140402d075000d5100704010000c2c51980c64181d0f5000707141c10b0b400c000b4141045001005413101070003900800c1206008600104030b50741c1140e00440c3e0003810295500c1003071074040d4580c41d440b8004d4903058646a0010805404a1402105507210b507002d0442c860400301000140101540440403400061180c98440f03481c903004a030165009a0402038280074246084040c0c40b00142800e04040c01803003589400e90300709076102c00740c462241c41c02d030303c45401340c0d4254904000d21100c0d42d0f0009100c03d003070300381000c02e50141c80c8050003076a030344543d591003000f8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 593400323 1250 593399073 593399083
    0x203010510051c02030c090108090303070827070e06030613030801060c0303090203031206100c02010914120d03020c190c052709010f0f051302010f110708030912 71
    0x38940c11081d603100c64190070744030318002d00001c1c420f01e181034001402089103208a0f041103030522105840081c0c0b014081d030300700e650070b6406a01c6000640c50f602e404003000b03050a20151280d1f001924410092078100354200d40d005134501c05200311050f04c2d9a0b0040c081c10325105450b424024014203005c5440c0040c5412400207954060302c0d000b21591a2070000c44241c0c0c14480d0a90801da80e80748103a0044c4e03030500042c09080c444103420075039400e0070010096560303441c007811380c04e00802090f1000180d030003100301e40c01c40b814520841e2560448501062143c00d5503850140c190140305510181190160301902691f8000c1c021513444490840d0110044103a501c40a0309124441104200310301c1d20840c5201806004031301051202982e0211f61032a4405548603495030f5184c1d0030302c20740c0448a10540c9c50f0300c69402070622160030704c040720380e86075030313806001a041122810b5010032441c021101c4000b0800c8840c1280d80103941c4c0d8508944a0b0490441184078002d1a101a4060040028 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 593401573 1250 593400323 593400329
    0x703020a0306080a200a1a09030d05180607020616140c03031c0225030819020405100c06181b060e210106030204051f060819181b0602010f020301 64
    0x30350717450682e10716041c0b00e0400d40307903a5105030b101a80c220081500c900005d9141058110601503613240c04480e003c060030072641101c5030080140c24045282c807401d0600c1d0941e0070402c1038420a990300700c41d00124285100b110341d010200c8444160701020841103078140d800c0d00240c48261030f07a0007045400c040c2c0700d00c02d0b0080ca040c1c1803440040f240001403142d00414001c81c18a4a202e54403412103101c0d03051040f00d031801d50214800c01c007005410010016008030241e041c160440c03400e41070070300103a080040e13140c00d42c040050207180c0030100301d007540c00f901c0303070002030140411070240600d8070391104103680b0b0300c0c04011218000d0008115002e03030562180d03101d000748141e250442e8540c403500c40030004070000055648034100040076844900c1a00c0c06200008440d40f1a0340c001c120b11003411425034402010815928200581c0b1203441120042e1005890804101c010000203030019900900030f024180000450210324203007070401c994421111150000d00003d203000701400101c0c00248 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 593402823 1250 593401573 593401583
    0x10b06040e060607020406030b0f0603070609090203151905012d050f0403120302070311070803030601030f090606060507030f020d170c12100f1413150e0703020a0306080a 75
    0x80018070024140da8003035a401540a46002d0030003080d40c00080a481e120391054030755602c1001030000c8048540c5025512402c1500142201490064020038200700d500c600d403116907010002ca00340961550410807002d000604182c0b2100b0074020300071900b0076903c2000d020486400c1450901042100403106104030044200b002101c1030b0004d982c19440b54071142c01c1c0401c2000080005599810a080d1340c0706540d4005869207501e00e40a403070082502c0784804260301003501001401400000c5a82c030820a2030f005c20750920f030042c508040c2100410007042141030200c00314910740d0040c0a007001c80c3c06a541c2c4040d420342c000059031184020000940003c07000c6100c03c0c101210039400f16040b004640115281069102c0c0221502d402601d0041650301e51181c10065848050740250103000081d00507400700c03183c0400208280000700c01040d100340c03039143c3d0f411014581082c0c00024035002d9100310052510240040c0254802280b00d1b022a252440100e842c1c0381c000b510303414280e807007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 593404073 1250 593402823 593402827
    0x100c030603020612091c0e0f09090c011107030b0a0c080105090f0f0c04030b09060f150a0504091703040305030105030d0c0201020d030b120304090e0609030a0212070213050408070311010b06 83
    0x1269844e29000300520800f02c6109078040801c0341e0031800d0b40714601985a40d80d225070486440c007000038030310100381c42c50710500ca16001d2026014007c48d1070301c0c40b40424207250010f03501d40e00d116410700c180c0390710181102850004000940c00c0d10303000b503030f0030400030b59406449a0701c2e801008a03040e015121010b60004c3d010000b184e00504402e46600040c0080302d141c02c0642c2c07543d881d444100304840d5150107800038818070202286840002d900100e03440801c0d00e54070440c00128290b0047c9110740342c881d90302c4d03102443c240444001d05400317080d90084050f42e6460103060207000743c0e200780316482c040e01c00c0315040c50080748520f400c445e001c0c0c1d0590161400c881001401c070040c0c03242c03401c02a071200c2c00d60551a07c11f0401c10082000f440823102c04111100031a05050601070700421241d100c1e00104034440061341d022070040d03040c040b211b81c401e8580207980003091050b410150070039061403404c8144401d01011202505116100390395600d454038600a2603400d0b20394030343d0600d41000703003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 593405323 1250 593404073 593404087
    0x9050307170702090a0b090a020a021f090506070c05302a01150f06080123090103210201060b03130201030e150105190501021b010c14100c0306030206 66
    0x30446504849001d286061401c10b80142c0015a0f44d9030140d03010000d443d0b44441041c4941004580558001d11211045040c0500044080d464508850040460012003a080b61341551a5845021082d42207002c42d10b2918005074007501802d800342c425a118440d5010900004000c2282050020304040c400b04124861030141c8800d50462084070490240141d0f0000354491407400e0515102c100382e0010030100d01c1a00c0038010441a500a8980110f0b1f01005004041d0410a010304581c011655225400c0019076500411421160000d901c9448070f400003041c001c1d088500040c0107402c0c82c060480c0c1c1c1c0f0b0007100b6030899055110354502d44200f400081d07020401030380e148c504035006040101703541081040090505640401408000403040010301107030500c41c040802070319010050100c0749080c000045d5451100040d4001c2e401e2446c081e1110a911545041904a80c800c041c540e1048503281c0140d01d80711030007005001c440c039084c0700c071a03030510034010302c0e04403500500f00ad890140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 593406573 1250 593405323 593405333
    0xf090a0c050607020f0310020a09091b0810080118030314090a11061620030a0b0a0216080c060f07020c0f2709031c0504050d0309020112060806150409050307 69
    0xf1440603a44560901100c050588040c0301c0c000c200e007080b2030f006940f005846400b61440c011a044030301644d261850000c00e81150300121800d40e1901d040010950b55107071907543c00e14840780c004c4000395003040c0d080d4242307412030041e084016102c3d072401d0104400303900582c8407420f0100c91164070b035448401400041694480889000342d40681100e1030a07010780031801005501c1d91088076203440403d03041280f540b0700010640d1280080f03020b020101410789039603100d00c1d005407160b03030400c1e03001495a4005101040141c46c00e54401c0f58079440752450304605454101c222503043d103030000080000c10540c40490b240d0010007000b81030002440c2200140104070b040201052a0150100340030f5112255002d0410700c070301e0041c401140e5401c0d4481c600f00c20548284044054507080c00107100020740003040e201d420002a1800040340245030004948031908000302c0545586000008202c3c241e0100c0d8052080040881142c1c6a100300c000340b05c2101c407124006406500203003c4100011 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 593407823 1250 593406573 593406577
    0x140a0e151e030901060b03010501090e060f0d0f02030c0a0b070f170304210807090311220c090e0603061602030c01021801020d09080c010e0301140406050f090a0c0506 73
    0x403900d802150419007560080d081c5540540c07014050580d0200400c4031101c02400703540301031b240200b280c9080d07501d40300028003020454040c01c08501903200c00560103480e6280091603010303009000b00500c403064142450701000035802640030340529000360b5001d0a11010200071991000c44040c54514a521503500100b2100400c0fa01a0900b131000743c103900c2454091800343d0b00651000300340c4140c0381c907480c1003e0010003072281400140d500304518a40c22241e64022240c00600c00745020b4178003400101804922802c4221151141b045003c041007940d0108c010075109880d05c1565688403480c02c51665000ca07102030781640880001400c409c1c194151130300000c100e004890402102c600e405003640c202450607085680b880a400700c0c10f42e4100040480c00c240d40c00c105201c44c0c1010940d581340c0d401628003505000d070610f03490340359031025849080110081d2131400e0807814245003010241c64250313907240c0c0c41024600429280e010210714110712a40c40a1615121403401050100507 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 593409073 1250 593407823 593407849
    0x120a0201050405063118050c0d0f150e0a1d030a27060519030e280213060311150d2a020d02010f0902032505060c0d140a0e 54
    0x13078038013401031000010300c80b000003c4411445c881e2411641054079543c0b505030150080103a59050405010543d660041126400c142e03085c8041100e56420318100d0140c0320010a84040c21000c2400065446c0940b030041e000705805017060240701031040013100740d25489007003940e0b039420412801060302d0146900f2038004420f80304103c1c0080d0a0144d80003850595485400031a90003d0b038011103004441007540e60a0b10b6007010170218a00c5000b03180e0f40c0c01092114202e070741180707038902a50000b61491100e090380c024490310414100b10500c0c400380485100c202c50420714581c4014807898080310010721071001c10822824000d158500300060302240004243c404114039803000030351203034424020b1801481d00200240c03001a04028216083d59051041031850000741400598010840c10141d01942c03c0500d80801c1e01444801900c00c0ca03400036a10241c0082c02e441c42203c04075000708810f6440d100c460400c0300e12500140c4600c91030b169000001e6a41040508500c0c100100d1400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 593410323 1250 593409073 593409097
    0x2100e0c0a080115060c0b1b090a030305040504050603030702090f0c16050a050c01140d0209121504060c091404020c010b06041d0109090c06050a120f0b120a020105040506 75
    0x155030900404504a1019500904901e945405240c2e0000310780402d8007005102c18034212844086c0fa44400000c40700140a8903445180541c0504010003120300382c400c4800000d28480c085c6d0350324640130741254070510545000c0e9040000103a11881c001c03040e03918550300a0480c40ca29650203101c1c0401400080c40100500301c24000c440c00032003200048081700348110010314103442c542c02d00038a0019546103290401428400701000c54198106417006840d05203070168540f2000000591001c41c0d100d4008003030710400003203012040c1c4481c281da002d40d00a00040040a034524400c4400ca009406a540245203607a0b410940f410f0a80c01404005100c8000103100d44100001540030b6020341c0c01054074510031b001c0c41d148204001c0c040380c0100307802d500030003030b5203959a108680301c86948103010500101098150209005078080c5590011030035040010001c000035020040c03140303240142c05450801e070b0700b0448401c005842032a554058540c0d50909180001b0801550301800300100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 593411573 1250 593410323 593410333
    0x1204060c030c1506180f060302010e130b09130311010213030b0a14040b061e0a09050402210106180e100203070306030c170606180403080a020c0d0e03070501020d02100e 74
    0xf81c429030b44500340140180c61071202c070f00a5904820015200c0360403503c21228039010702000183c1e0000710a0b01500401c1e01d0301504000e55088030001404034008403500301c8180c0040120350b50b8580103100001d0b01c25110358040c10242401e5900f00d010b0f1801055140b501c00740c0034408902c0182036650700c840c0e140008111074000f404980342e0078400303a80c1211030000c11001d01aa40c030b400f000032620440c201c40d1880001440c2400200481030921505200b2550b4402190540d1980d080085c000c0740001403108071140e000c0012802002ea5104680d40c0c0640300141925811443c0a42c100862000000700a5070403040c80b410029400503000c1c409265540c03100100040c010300400740107080d41a511803140d05086106800c1480081c00c0c1d5204000c20610000c2c007070000221580c20540600d0083d0090f9a04510301000388518142c50780b852080303010a081503503106006c01040413055042d07a10b01035840d001640e59240e1441f549000d030b00103030300c0d600c01500690b2100c1e041000c130400b161 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 593412823 1250 593411573 593411603
    0x7020925020106030c050d0c03020f03010216050c1503060303070b100510020708070f15051c09050c150a2106032109050303040302010801050d321204060c030c 70
    0x48203861084000050b03512050104148206000d00300010902551007011140c0b85a846500f802500d00000780701e90030446805600d51425810b44200101d038041055440c086405c041d0303070b144070648019100350300c0140c54400030240c1d841907030300070000a401503084c0200c2d41d403203e042400c000c1424a07400700304000002d10342d8451716241c0402d001c5402802e40c0d86e082c5034505041074a5500720442c600d03110740d410000c117500380c0b01814505105190881c4ca8051046c022602031094403ca0210300c0d081103c01424000c01045410f090780040300c801c140304801d820205040c1c0100c91040010070000c0f400610301d0320544200c2ca881d07014207000040c0b200e480350364040112001d0100d184006005141010405400000c0c03000034202c110015400d1910f5a4002001040705014007030041c0c03140c000100410181c4040d2240e400441480b018a1403408001c203002c2c40c000c0c8500311941d104442940e440400310804440555072140c0d6040c004071555181503c1c405102034085a4950000703c140d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 593414073 1250 593412823 593412871
    0x60d0506031519050109090809010f02030906070b010e060d0203060106030c11060106020c0a1d070e2421040f02060c0709060f0512030c0c09130804090b010f0f05070209 74
    0x103910a18040030010f40d101c2da000680c0080301d4050b0065000c042c5044120400300e140d40d01a2101c2480904e48251001c510143c101d066000712664540c10040c0800c0100030000d80012503070680e4039005100c40c0660781d00041012101400320081d41640148005005251080d0401d0408407518201907148600300c10026141200c02d03400580140c1003c04500641d03e4841803000003800c81120109250a1040c10b040c800c01004d4920300c00e103c02402c0482b565180c4844030103049404012002104802d800a08413a0b07000700c080b05215200041c0a00b627203801803a910780200c0d04800e1081c03403020641e00740301c22948040ca180e04035125044000a07141030707901503040a426404654001c41d880c14061040210400d5000c0c4126003050150201c042d000050800f03000008030740000c200e40301d29030701240c00c00070000c010341a1500010042029000e9410000900c0000c0ea507000010300020301c101c481c00100e44644002410810049001d85011014140c1000e5000d50f2203079002c00e00119 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 593415323 1250 593414073 593414113
    0x30b04092f061804060e040305031501090306020d0b090a1e09020f09010f330807120c02011d0601030b010303030510210c0605190302130b07210e060d050603 69
    0xf0348106548608219849040901640700204021900c2c04014200369030050f00030301008002d191101c54803411043c5071f80c441c408803401560003800031950750400c050400050000c0007841401150f980e0080b1b41032000d40d10032005032039071504840700900d60b0f18510b07402034480c80300c050764440b141c212440b42542e100300d2882e0003403104041d404411031829025021102481c18084c413510540800900316000c160950064228286002d43c900e42d90900142e5900901c80002601281f0703204044035019015809541e01000c00d00c03907040b4000c404040c503a503545c0709020042500c101c0900400c0068040d400050f00100d5061040800c5a203a203483c5100c40e00e41180c82c4503048001070003170280145049480c0150080307180c52841c00c1e11510005851482e840908400c1660000303038684002942050080038001801a0316a02c10450400f41e05049281d00c4042902201441d0036111501803414030604d208054599070070125054807034402409c005200d640c060040700c521090451030406 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 593416573 1250 593415323 593415337
    0x130b03031b0a0c151707020a06050a06051e0312031003081c0f0b0a1205100615091202091801090f03050a1803020904060507050d060303050a030b04092f06 68
    0x1000c042810b81401c0d14400f8a940c4203415803580d40381040c140c0d0b03034441c0311101e00b104424002082604c0e6010308030300c0e0207200000600003502d003c040c08a030780c41941004045480441d0780f046600190000181010b400782d03542985684200c42c10b451103010000a103138040036101000709450350320345034190320358000c0058090ba9030852181d0022174075984a9483c08483d8100308014a0540a020910a80d042c2c01800c08140c51210140d04000d01000440d10110711182c0c107100385650790500540007000da11245001c1000c0350000b2464095040341d003110f65400601c549507a484001408041404446507282c4c90354079400c030000418503e205040c54203109983d00380c1d6a100d40040140300800310704041c400c1e0305c440ca01c1040940c1e01d42c00099040354001800080d40d446d2044259141d228032981d0546003030400070004145a0003601900400d45d4a0b2018441c80a0f0441080110388800c00000c10403090202a1001081c169881c065036201c6030144943c00385c1001c00140c99600910 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 593417823 1250 593416573 593416627
    0xc020f030a03060e01060c1a06060d0227030d0516020f0904030c024209030a03050409200a120204091406030c041413031701180515130b0303 62
    0x104204400c0044c4d00390380d4010302e0285450b1301581e40c240c0e1542c921000000c44080c01d01c040c680405c03520340e140803c84101074400a01150744040705d0000700000201d50102c05003110303c50004184500300840c00070b0030504c441d5140341c5071451101d000003130460f40410983c0c100592500400072500c8400c900c81c000e50103920703244c00320b46162040100600c0c510103070350314502520119001c01c0a07145c1100001031007010303101d17000c1302051141e0049801880582645440707500b002d0001d140c0c014008000f591f84018050040d1007000900c1080d25030160469003444d2400c0144c05c40291007440624450300d4000c102600d002c0d6140c0f4418166680c0b4450550040c06c200280320440c5010840d102c03020310309039020300c15110706805000c0304400042c1504041c1160501d000105403107120107011126500480d02801d5071030702c00740940307965403100d4002d1131860000407d00c51800d410040c10815001402c000c41c5000240140c4090045c0c4912a6050b20041c002c002c44030364602d17000c1c1e4000481c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 593419073 1250 593417823 593417831
    0x302010b030d110309091b03130506090106150f0903050f010f060e01030209060105180301020f07030f081005010c050327031b0f0405070c0f150c02061303030c020f030a03 75
    0x40c01014104030386104480140009042c000a25a00200540301031280480d420151580c546070044054106502007001854001007041051440010145061030245007211700580d40c51040340d08941d018000d5031224105a054880c00d144a58261520141a4982240d1031aa2a6503103441c0c50043c009103521651515800000c802051003030500805060001840c40e5145401180d02e003030000c1c028038100000064040c0ca144040480c04000e940b01500840d0368100d21202c041c0b40740c020420032000110344240b5058030504c19111540a1150805501e0310f040c544001580c03404444d03c2c0c221000d000c140203c05143c2014400700e04072641c1001c074280c520071400101810401200080c61800110020348959501d80c0b040700c801188050b02e00251507125840c040d286200c3c0603030b005281003401c3d104001000f140d084403810101c058039003400031548048091b6102c0c001102c1c000c0c8102d102c0b0319171300c020078480d03003055041c10302e10f0050318604108074646506682c05501640701184d01d03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 593420323 1250 593419073 593419091
    0xd1b09022505150708090c011805010c02180f060a08030a0905131d060f0f010e0c0706020909040c030b0105040221100806090304060210050103030509010f1209060519050624090d030201 81
    0x2080c03100b01c50110091800d500e4200f40324a40c40964489c0d40502030400000d07481c61801c6403039207072a02c2d20024210425082c00d00e002942803c07040ba04a81003405403030303e290006012000001500c0031440b403526a800e010b81408240088800c00c080d0110000307448141c3c203e00c20041480b007049034403140c0c014101e1450720143c4010744400c00b40c0104000f14018004100103003040440384d422007000c400c0a0b80e19090303801c10380068010310500d20b034806454005d1004000054000c0000c0f80d125468400b10b503a6a1410030049010b180358503000c0b202a0702401c80c0c00b540c00ca0340b0980c40904c035102c0000e2945c030f548601d86411004c550014286d48002028002c1e19010044038240d0b20803ca0248000c0d030544e41d0050540c003c0c082d81c18180f0081100300e1000c94000c501c0105900395000003008454007906210015013426580c1810a00c114051216080c1040c003402d8403d2070050310040c0d40f1069035118000c003d4a1844070020001d0502c030b140d20943d02c0f80a002242c0d4080d5002003043d1071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 593421573 1250 593420323 593420341
    0xd0b04050601020d08071107260d030c36030b100e0105060702060a0201060e090d0e0a12080309250611150a02090f0d1b09022505150708 60
    0x41c15003410340d40302c20b1a4941559000e02035550044c054070f40f540c0307004007107801945070208076000300081d110390158010907204400484401c90707050400b180e86088100d1000c2d012940e444040c0400500c0c180e03070702c2507000ba211140034400d40c4281a0b60401d501010300400c03990390203030400c68400c0d40c44030034032410104800e940006041040d450983c03a51510303002818030321138200002c2c01140045402680ea9000398007400013000141d090000629203400480e44817051000d8190100b055000d0754034060070b002100f1000e0301c41d8101444292800d940fa204020380004005082ca03120302d13040c2200c582d001c15041410315400000350110346003000300c040c101a1070b075400501580e1014a190143c0740e01c2040300c40d081201814016a60110000440c0d00704c990701d0000798004a4a911820800c00c4505040c42005020000241300c261030302c64220991207401203604095040482c0300385103c03081000c1540ba1407103071040325245d40c0c0d80803040c0040c8070708843d001c0201c0c1d43c18082044404c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 593422823 1250 593421573 593421581
    0x504061508010e0c04050402010c0204050405060603010c050310060c0510060e01170613290c04060906080907051507150f06060302160b0907180c02070506070809010c030509060d0b04 80
    0x203401e00078030000902e03004403036079202013840381489986c0320000301d01564044c0d020710b002c1c1900504240b12514060911503610b2505848160280d803801504411081c416800c0d00d000d4050070b50942e40c400d1501c8011030319880d010300150364900811014013501d600501c542001040300c0d5040007010f6240552171000001641070400040d0030000070841800d00069454030304c90391001240d4ac107030014201803c48000e01c003c0402c040200c1c0da0a0103001007102024000721100c9072b459000070b64942c0710445120308207441c5040d00780c2c402501070106280c10070700050311880c40302d0070904000d44c60703da01c0002610a40458141075035198108460700860190601502c141d080139450320400404d51188450314450103095a18000c02050203003d0902824000b1300580344100c54407031100d0070300742c010480180040f025105e42c800c0011541005000c1d1600c05410841941c10005001c005503000d0746230700d0044040150030440e0140707950b034050203042402103e0100107200c23500c05050008071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 593424073 1250 593422823 593422829
    0x30e0108040b0f0924150307290910050a0809070b07061107060207050d0809070b270310020d110705121806121f060206072105040615 59
    0x840a038007000007041102401c1500400c0048102d20786980d12025a0305015509601030300b10140c04c9004c1940044103030340b1034001c07620f15400510b0b2010f4003040541d04c3d05948681d48022034100302c0b01c0220407400031001c00b20031100013440d14041800740012807068030107040201081e0f0214a40c004c0385d80c06141030780d11050550090403160305060798050310740146100284980d0302d400d0140452020315082e501d606502c21000d40d29400305141c07060329600c40240c0701c000200b03040006180b103080010303100708a850f601035241c50800413103044104600101c171a00c041a0980801080d552402c00010745103540c148401615a101e000b41103041e83c90741ea0150f09151310500400002c502e001c03580e4485280b40f0100c29582d8400480041a51407810103101d50041004c55034619107032495048510901020b004802070344e988814101d10301c44c59001d0000103901c44e400041030a409024000c2d08002140002e403190100d00726000143e50040300c08070356a41d00c03400341000700d44d41500c00c0780c06 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 593425323 1250 593424073 593424077
    0xb040305030103063e040b04060509130605100e040e06071110051005091308040905010303080906040507090b060903030d0615170a05131202010501180207020f060a021612030e01 78
    0xa2004d9a0a4940004000380054102a80700c405d44078181a0b82c48200c400800d5100d810036102c99030f920028000c4d0700301001c0b8900500e41c0c0c401803141d404143c0304801c1038800060400900c0c002080048421403000080c0540165560030030000d0039008000003441840d669841034203400148100c1414100c028440020850030002070203c0d110b000c1517904242c40c8243c500e04403581d6a03a10b07010000020803800b80c2420400900403546d12104d0300143d0683e8080c0c0c40340007c40c3c40f00d0f40c00c5075a43c0720071034000e00590008041800448025048007070343c2c0c0d900030606400c0400ca030b00040e041d0360007650318101142e0703110410480c6142c0a88460b82804da1410009506101c20321040c1076560003c1c04e20841c02e40c1c5c3c10006896121100b2501d000c1b51304500d0000c4021910000a8028802030241c1c003403000c00c4000e03962016016008a40c1e4440d03019044034038410083d018800607070010940d0b04203601400c00e1039400c0c10b0510b4135800041c01819000451001d0b1420090b00800440440c0c0341 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 593426573 1250 593425323 593425361
    0x2060a05103f03080112060605060705210f0306040b1201020d020c0d0804030206190207060204030b061302041202010c110603040c030b1311010e03330105031903120204030b04030503010306 83
    0xb094011a5440c1142d4041c0c0c504040c6d0011480d1400c02041d641d0400e550005010440109020740040c85060380c6220b080076110000340201c40315218042c1d0041d0000d4801d0030070004000341055045048001c0015101e0741c40101c44d803400304d0a9070066461205542d42c00b180c03180c1c01c2d81080000c50440d11075424044150704280d20029101c0d10b00401c07071000c040ea8114207540803085541242c100c1ca07000300045450360b44038a4002d0340140c064840a100d10508031060360201030a01c00c803030440d1802103040d40d13801c50742d034010744120311100703c2601d1447c80c60001d451030742c546000441c0b20303510420300701107e41c3c00c40c60001040c20001d0310f40251320307a01505e0b8100080c1c02441a010b000780074240116225220b00000c0d1502c1400e00c1160342452807490390700c410964400c2211f01281d1034034440300582c0e8a40080c15541c040315002e2100d68022801d1960100303000f1840b05d4008681c40c400989000d0701c98075112003201041e90202d000400020040003031101a120b00c80b41403802000282e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 593427823 1250 593426573 593426699
    0x906060901080736030b1008030a1b061518020a05070624060302040f06030b0a030809011101060303050909090a050c01050c0102040f17190302060a0510 67
    0x8151440c003d040b6003d0241d90703034214010b99480501d075055580000746845000c148400203906040540c0b10440321a0725405c0800e4040750044030b60426079903260300440c01c081c25070400b00c4500c981c04020204802e9440380c00780100d41e05000b02401701d20603141142ca5103190480b040c24001203070141004a5106120664a2507070000071288082d800c401d0100303001c0a11064560043ca200902c0b110000303088100240c503d42540140044652514610f003880c0e0b0307512000e600342c664502c0c0e0703654041c0c880c200c240006030b04400034205807241858032029048619502c18210786d103c1e00203070301050b0081080341943c0b4041c0707507644d0702c840410060001642c1e42d5442d140c0e0750f500221003905200f00412800c0c8108400d6040e5402414000945401c1c0d9540d80c410102070320614410180e0350094441c000d04611025402070303002c13a81a03009000a594507507100c1c00611020b02035800d072580e200400240d10169a0f1020ba035003061843c104200000808140c03091400c02e419041c510019201c00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 593429073 1250 593427823 593427827
    0x150807030c0e01032f030102030708070212070b01180e030706091101050c19020301020c1020031b030403020c040504080a0e0a12060905030d2a09050a0b09011107060e0906060901 78
    0xb1004071001402c1d5080d00460380c00005c4941501040c034250190b1012041060381c5510243d19401840d4540035100301c1600100c141505100303494018051402020040000c0c80c1d4040c00d140c4100400030b00018005041185682107620030710703084e550141c03178011640520482035802d0035040d00c00d00f00a4600000c01e01940d4451810f100d0700c014840d41c29a5140554500f901140c4900c0d51070000c0c0d80c401c5040c91402001844801005000901552814510460144122030150701c410742400410382085004c0f0100e07a2004004500714010380745095801d0303e841c09040d0044d8421850b86403240d0400340c004090002d09600c00e4030465070142c4c07c10a10403075501c09201c69420620114000905041030751452184c8404041c1140c5045443c0d0801a1840c1a242c040200114001205e100c0c03407000b1240100300340200e41d031100b503020f420010325040c40000c2c40c5c8408181411030340b00031035071032417403c00b00300c0e510820206588109801c1146070800e04103920140403140b00c1d0814200c0000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 593430323 1250 593429073 593429093
    0x3150f0c030613050402040f0f020c01110c06040b07020f010f02030a0b040c050d020703030e0303010f05030f0604020f0904060905070f1d0f07080c070c0b0d050106031a0112150807030c0e0103 84
    0x10b0340d83e507540d514045829511560403035040d8a05200c0140004550f0694007070007548101804940340d403038928100e40f03028000003210715548003840142481d8817070391204040d81034040c04c3c0a0540c410710800f00c9400b40d080c042c01a204440c034800603264500b041c030a00a0f0b510f01c100662045150494101070b55410a0075207040c074560081c01a150480c6103030036002045260840c1c0c00c0c0d84804000001e5034509060888103079072040c1c055403c0c0706040301d82c0643d03a580658000b5031241d0552050045400c1c500c5607103034003d01410010601d9541500c0700740c10014a6045100c4810242000b840031070141841421000c2c00200304000300d2400e40785a00c001003010345040c0810011002007400c4c60a500152114190000e2003c00e0281d83c8120000a60748800d84404c0d086d810704000146403400f0f44640c2801000152004005c82200030044a00720a020001d01c8aa030390b800b400f401086a079800070000e0700c0b60341c004284030f0342075040c0208684900d41c001c02800852100600c005a22804 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 593431573 1250 593430323 593430349
    0xf05090405210f0c070602190f0210140c15091f05040f0b1303080f0f042d1401051501050f0c19030507020a05010206070e0d050c03150f0c0306 63
    0x9241c4a0100c14038448041c601c190100e03d2050003021511100042d000b0800d0421100290211015001940c81c0d290b2401051900600002c168400400242c18908505c03416410286003140020794111409501500607aa802c06142e02030200751002c0341a014005820114000c0100184007804030b4007c2014038441c814184503484a0101e401c003c0f98101d003400b1290300074812091071503c2c40c1d04d13098401e50b90b4416000036007178a020545a40f0a403800900425070034050104640e06d6803208031101448036005206a83c1c1075100310440d030345008441082d01e22549000842064000119081d80c001400c20016076481e0521020a07a0b0800100c0ba202000348034500d40703400c4480415800c00b82c01c641c04544040500d2900380c10944c3c080001c141c5548200c038000600d948610049944c2e00048400750b02003a01300c100e00c1800d10304410628103840c0300300d0845411405110100e41046000c80400614070080b40c14001c1c106101410306600ca2101d411440c00d40ca403100c00586078a807600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 593432823 1250 593431573 593431603
    0xf080907032027010510080105190803160302010b0f0901061808120405132904020c030a0c0302070608040c030210050c0a0309050312160b0903040806100f05090405 72
    0x502c00660038810104951a07800082544000b0b1640790703000b004801c2d04090a000000e158000407845141450340c5aa48004136907603241c1d26030034041440500c2400c000d4450300703416690b10005000760200002c0902010401d04505229514600a82501c812055031071250781d5240e120825501c86403412030442c1c10614162284240f00d00e038444c169465a007155030f66005c2c890700140c2e111034903001001100c0040d41c00d04100d90100c0140002c0381c00300c5201aa18001043c0c2100c0000c03000701c00e461540000030801454240340600061856002e1184032010901c1c0011480901d50103104400c010007490811444c2c0c0e282907600c6001d00c0006020003840f400503509510400d0b8411000d48469030458421201c14500743e0601a003058203134031030b59100b80314050020f102d0b07070420410f51301030755606d01201c00710001caa40e419110520061180c0c48520040c84002003000042100701c1c020004549046082410303c0050f070010220354110900494101050000284000541d00306410100d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 593434073 1250 593432823 593432843
    0x118050d0f140d02010911010c0b071107050901090f050108030f0403020118051c050f012d0908030106090311090106020c0111120c1b0103061206020a03020403080304120f08090703 79
    0xd00d800d51070705201d11807802c07181c894441400340c1660150b02000c44907000b114070801e841500001103642011813003005010507041404036407014010100e400350240048180c07200d460300d03000031031201d540036802030300d010b5150301a1442e075450340c0c407845014118140c040d42c50030300408400354980c0301310b01c0000c0c100700340905a07002c801d81500050000e0030000305103281e0302d5821a08000c407250440015110f0f03004818949464642c14481c0c1440c0001e06461a034648d001c002c03148143c024101d9000300290740b2082010005030780341000f0340c040c00254803210001402d604000000e4445d804255001c1d030712050040c4000358001400e10603109003482d010322041041d508007410095101581012801c0c0410b09007015040881c1c1100781c040030a090303034a040001e40c01102510622f00c02c00b82110403070400d02000c110701d034000389416003a90502503e8141c1d80d650b40c00305075204035025601c4101401e13040030030a0348071038103001030102880d02501a0810104041e190250351100038060811 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 593435323 1250 593434073 593434103
    0x80706020d021603140310210501050c0a0306120c270f021b0a080f070c15030b01080601020604032007030209040302030c060702070b040611101104050118050d 70
    0x140d01100da4040791010155160788103603e011080081251084000c202a0a070040070b15500c1020303a889541e290903003034010741c0741604013440b052065a07601070700c8441e1800b03c40840c60902805000381c0b50341a010340d584103140c0c002400c0711f0f03450b0400711640c00c00071803640100d200e9840078002c1e0b6200400c1400000041343d100c030440c0362010f00e5641c0550410400364169149075010340402e005804030195070164030b9026a464101c00c100041035504180a030a446444074406404814071841c0b5410700c054858003441c000340031007207203180026201c0840345019680309450f030b50044003e0004009034142a5409090315000207440710307400e04d201111f00511f0740200301d881d00450700640000d85074105810300a4030b030b90281d1000a190300c80da8011404440c400240401124500f0175524201414800b044860306044444286144101800c2c0051802c1c05c0c4695a008003020111941c3d66162400142840444071309000326084118010402c13030300e400242d04d40309680300d10300e0307488490 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 593436573 1250 593435323 593435333
    0x60a0c030e010906020307090807080a03031509050f0a061706070f09030f0c03020307080601080a060515061c052214030f041814041a040503090d0303020d060503070807030807 77
    0x7036000ca0300301c150b0800365058180b00f410303030003180201d041d95150381209448418240c3d440321a03220342000790b440701e00308002092003540403450b5015094511665140e803289030f8419140151440d41d074484602c0305025204400b44150802000a0000070010300d0f000c588031034039024020400c206004a01c1380001e40c5500c00c8045602441d40280c103190418010308080b604107801e40000c074042e00c500303180820303010310000b03100303040768540c100421300b04005540d078030003806019100040e0405007282078440d50340e503040680040104c0040380361503240a208030b1015038a0140691181d0b40b665219000c2070b001308200c40c481150051460000700254940321455807107180c03140002440e010502140f500110302484254006100d81030142028480941c140400c080d03c00070f00c180c0c8400c1201040300c1141c070780d40703a0040c02030065905040f40e031404100424282c0030101c0001c0e6002450000c41c015512504026010541c000c1071514204225181c0d0b031034031804050020a000300fa040100301c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 593437823 1250 593436573 593436581
    0x20d080a02190804120c0c0b0906090603010603091b0503030d051009051602070b0a080609100509090124030314030a06031a220206191103070506011a0a02060a0c03 72
    0x185800401c140da10700c030b4200421290060300c2c100c403180702404104002920440000e0071042c1c018010305821843c00300d440800d071b4000005950400030521040030250354800107103000b00425180464582d0b0a890020940d20441c0360303403404200800002d004680b4008291201000711100005054a4113140886854400e60107001c0c43c604007410041e103010503184014480e440c58088464031929115501c845005000c2c109000074aa640000d00510300741e6001600183c0c6c03990780f064065245d0011074080c034000c07100311506a4494010420300c4d03001038034030007140c1d5102e003400c00881d0440e640248500b1172442c1c4208004c5c00440440c040d0b50700f43d801100250383c000082140110108588214540b00321ba40f100702481c40200c084124071728040c4141025401030110303142503049402c00d5802e100d4000c015003000151490240440e400300000d104807030181000348455032418001241000c84c19802403120501800041440d540001c0d0490300109d2201c4045151040c54008034020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 593439073 1250 593437823 593437837
    0x4140f040606051c050108031c02121f0b071208062b11030a02220207080d021e0c10090812040309050906010c0203060604090602090a240c0201020d080a02 68
    0x5181c1040020320310742180050902503503444520040400c41d020a00458009116030039581e00201701c00e05a4032402c2040518961034210014203017000c09603144d80c241421101c030507520504085500d41006000e02d40e10041031404d14407894000c849e590580c4c542c200b51408410b110009021402c10307540c551795001c21030481440341000130340300003140c0884080c2d510281c40d04c410803040c150642c14041142c0c00b1058010340030b204114115040002007a400480620190382e0901500002800312001082c1f4035440c0d20340961681758803040030309070210101010602002c10003600d0040500482c031258001420707040000c81105500746451302d482810010100381c10980100410140c0140164050750403d4444440d43d6a440300152040800300344c029504d94000b000182e41803815070440b0310014400c0d2009030400000e80041441d002311038012001c1d4142040b4003d5016942c0c1d29804105c0e151342c5131542907040c503600040e417607000f42d600110422010074002404450150110f0b005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 593440323 1250 593439073 593439079
    0x315030a050c040b0f01020a0308191a09130201080420040e010507080108030301050a030b1306020f030403230315010c0b15090603012c0114190b030105090304140f 72
    0x3050005241403a102d96459010500c5203162070400c180030f0401c1180d1000d0008180c006080306d1489403411784200388001c0c01c02402c036013107103100d41802155001c1c5c1024100003a4400564101440402103054001402d84040005c0541d640303003d030703920040040e00710b43c20021030b00403515902c00ca241560041000300303410900b071032030240414205500c802c2c402c2c01e25550701c000c285d0700d030b180140d1207200a00c80c1742e522501034442400810307041e000040d01300d003020085c2c0c0c2000100f80d46500c16600112984061803001104000a054001403950a1070844421801400d0303a000b5080c1d500e4007000c0d000e500752035003041d4420702c141d0003289801c207010381242d03980c9030614000c0d502c001c049803581c0c91240200a000b021070402e040500034000142c00c52403600d860b0400c05a08036203410604280207140b59240c94203020031146d03903107203240525807104c850144c41d00f16044800580c4c07a810121030080e850320b070401511060110690b001d8942800350907604e1705503140051001114840c0d0175034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 593441573 1250 593440323 593440333
    0x7060c0c091401150e060306060a1809051905010303090b07020102010f110d060902090607060b010c0f0303050714181c0c08061608040c030b19140402031b030c06031503 74
    0x81080b410744020b4121403e50600754441340303600b41c088614103030307440c81560400300620100708035103040009808043c0981c94159180810381c614107040c0c00b00b66201e10201952001482424810a02604000326660806001d00d5145a4008200500354820804121400b013954400c580c401c1d00189252241c000c070a00c0840192012080264000b1118105130f914103000003502901c2802070350f1045200800c841d041503125101d80700501608030141d4100070074560841e0009940c02c030300d4140c4900030b0b42c2c0000c1c181341c44180541500001240d0510b0410240020080c0b8510401103d1480c40c0690310214044c034107010103a18103046c260000c0c001c00c01048041030100c00041c24900c240c10030f2007103c4503907450740d5003610728480c240d038042c2c60030070780240510109101108403a0000320440603c0100c880340641c00ac1115000700320101d041d02e0342c40c180029490100070340035100b010082c00c0320585881e60000703030b40d4411b1011540d01600b8003000146503d0010708980180b6135002e000d5403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 593442823 1250 593441573 593441591
    0x60806100905070c0c15020c10080603010506011b060c140a0201020c060c16080325030b09060301021c0b190807170604080702010309050c0a06170f0907060c0c09 71
    0x35144160600419080c6450000022034141c0300b0300c04071040640000c050780425090812400c40c240c0602ca5403015480b4160951442d13494a9076140d14903155582c41d0201c0381000b00030542540d00282100f4100310349407254071681a20640088030031a8130640014441c0d1403150152802d03c00035a003003051200210ba50000203406400070081c415103442034610680e18001d07510000e00601060b2500090b02106100c0003031321100065800100310030721040b1a00450200ca1560640310614400080c4c44d80e040e5a904d09060a540d500301d00110025420304a20059907901d88a1201942008540740c0c40140020b41740c1c44100c0c513520040582c034100b4292142200383d6910a01e20640b00d8a4482103182c40f4401c00129200f80129400344142c2e2801c410303600114050700490b1429200741c0113000900000b0341d5250480c3c00240302988880c110f084a0f280b03d910a035074028407500301208900200840c0c0c600224030f18050f11054100b035043c4000c281881c0b84a00321580041040c54500715400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 593444073 1250 593442823 593442841
    0x110a12020d090c1e0e04080f0c0a0f1401050a05040201021b010e04020d02040501120c0f0c03210e0c191a040b0a030b15070b041502070b0c0d1d070b0d060806 69
    0x411103e001107401303c00354666407460000041070448024021100900c8084150180b4100078990030541c80c0c11280c116400f40c031035403592a082002196000d42a1081c0b0005d0b10080c0101e035481004860b040049141a0300043e468200c46540841000300800c100a8681e002d89806603600714050021516443c101c101c0e24000d40c23240c000d007404140c0288044683c050180100c2840c05540d907101410012a4501035a120f151042c0c02c41c144003030103090301505c0b801a040d8900c2e85105400120b44403078081080382c180f41e140100c1c0c0d03010b5140c0c100085210b4140c1070402007103035985000440c0c11a80100c25440e80d004d0b0390000188400006041000c103039240c2c21811010f181104c40b03410307452080c0d1460b0014454400c00400d003160b40000900494082c016103082d01c0c041f100090724200d9147d071000020181101c08680c0f203c2c1c04144908407108602c203000d000900440714440c00c013240c200715543c030113180c8604582080002643c007040f0083e5007008005108910499095081c48900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 593445323 1250 593444073 593444099
    0x70c0609060b0111030f070305090406090c02010f06050f060f0306010309050d08070f03141f09060605070b060909070b03070c1202030a030c053c070b0a110a12020d090c 74
    0xd49800038040183c410300f0400003004803040502445540c81c541f1000356402d4990750003403034085506c1a40c54200054100660042c00030f1418283c0c00000c2402c14000e00c42c003200c94a42000380100c0752145c610303207a0b48402c400c4913280075100c0d614035281e03521000100d000d000011002800d502a800740040181d4100210a0203441545c550300183d82c8980c03001c078200c0d031440c16980d07103064541c0c003c644251009100000c20180c070007203058502d51035130324035000d40c0c1140e4403590010b100018400184500348242e1604600d04544008880c00d2020809a4541d420b00840264100c00404512440c0c01400d81c00c0d00c0c0d0344d1090007405c0b00c6150100203500c03504542c5080300841d04042c01d041c2c43e40d200e9800c882c2440d0414240190040285c14049840d0710307122905150a00f901800760b40041611024292441c0b141405044600e4074011207001e450380c1d640c0d04089a030051003800b028540161110210b820010b0300184ca520b4000600005021207000c0644013610b2680045114154030007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 593446573 1250 593445323 593445341
    0x6030204180b01090b090a330819030c02010503130b042307080d300605100e01021908120f060109080604081b030c0102040f050901060305071403070c060906 69
    0x403074074210fa0fa01c1480c0c4003500c0c500c0303038050342c030103400c500085d42585d003070b48650a40902022122444625112030100c1d400d40700d0008002074100110412006070104400701c0000c07201110b202e14400f481c1d030081d05400c11004024140400400010440042200780394100e90b046040703006da0b801c00c0c0c01c04040f41c0207003505070003002403030800720190003400203048401c8904071070081041e0100385008a400d00056444c0000080c070b0b01800040c1c0500c00044024401b0300c00d48001001840e180030031150707049000314a0240400640d17410f031607a800bc00c2914001c004043c01c8140c000c8140380408d401c0c4140c0d4807410b44480c400b010310100440014402c0e110384400c4c0c030390700522900c403850303142d440f00100d900030300c41c11081001c40d50250500804c04910307520001164140400701146030301b6604190418040b91912000c10099071900c2c040803401040f10341070070055400e1196004040102c141d10f0541c03c40780010206415a2240c030100d44810b81000e41004603510614081024100240c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 593447823 1250 593446573 593446583
    0x6030a050a0813050105120a020f1323100207090207032006060a0807032a0518060901061e0c08041508090d030501270902090f0f0c090a05010804060603020418 70
    0x90341c007180f45c0d4000d1003118030142e00c2d481d0390700c41a582d010403640a9802540310301500745052100201d51015000b1030000f81c099000030003c5400b210900284502038492064414100c05010074030707180e00450700200790703280c2c06000750b5510310718101035440440c07149584070741314490851a1125980426078034050f18084038600c40d040d50721b011250740c0310114040582070810b098000d411a94034020400c01000b1000d1078402c1041d03903000014440065234580760244032680c01004902c4c07a240d0701c02c0b03000d00040d051038013507070b40d0003642003d080c2201c40c150001d00c02c0070034001c0e041c001640c00b910b008200204a105080d034901200900d800e0041c0c0c1e03040c140e441084000720705540070380200d505a03442d600b0704030412403610107050b43d01185030b20710002841e0340d541c41202603200d000e8032b076100740315407170141186007001c2d2203801c44100c00410701c5124900a00405c4001d0f6034484061046840928111030ba03910b0380d04101c00202415480290700a25003151110010381074280080028056 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 593449073 1250 593447823 593447857
    0x200c06070b0603011104140918010903021005060604060e09040c091e061712030a0905060103082208070618090c0e032e02030a0e0f030324030a0b06030a050a08 70
    0x101c440c800150046c0d000700140320301d0000038001039081c05440c40d94045807000588420800980c0580e085894180c41900141c2154444003030110241c0101c5800130010f5544d58075241c03500e84000c140740380303a596152280b41b00c4000300e41803207946441d04000d4684044100b20317442e00f483c04a9000c0056040001040f8106100041c0841c58141114086001d02c40a82050450608514602d62004140c4010196140f101b100443c0e0100100c9020354072030904581d07188a00070007540c40803d40c82c0c0742c040b107140c10030b0f0038409142e0110310074046450a05140d0042081141c00b8103444205801040c044c514004003900c8540e0f0200809154140035000d5600010b000803078050482c0704550400224081030070700d4024048582c2c015a40070200901c001000c00090320f50508040480520f030000350710202c11302c14540b404851100d81c06181d906003500725440c0c980881d49609940002400942d211000125140c5003444013800055029090f00d44115844c5015030007608550100c01d204844 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 593450323 1250 593449073 593449091
    0x190e151006090602011401050609030a050109030504050114031e0903090d0b07030e0609070315090f03080f0606041a09041407020d030b090112060917040f05030606030d200c06070b060301 82
    0x61040254906c0020200c051076800e02040c0032681e442404a103405202d0000c061010a2081c4911107545200c2e076a001d6889240000041c1038010444451210318410010300c02c1d1980500701c250441d40740003690100c0d50740c900a00380c2c110301034100ea1903007000c0c0c10351080d4100502c0b140c02c07500c15030f102e0b201000711051121806682d0403086518881c142e103d01824804100340b0962007140040c00680482c000c2c040d56120044520041021400300d1a940c0504c00d001c40c124142c0daa101006a4045046c03502d002e0141030903a2402200717081c0040c000600c00c4060301c440e045402000d0300b2040c01c40d46410f19a000135075800c2e011803a180000e02d4801042c00f50310704620000d0485509042e2020542c0c40c64075081f0061251000403035113468042031021002c41c000d00504010414030900407021441c2c18285800d00b82e005109a00c80d030001c0c604415120703000046140e03158070510720821070042c4419694507010f00103540355403081012680608208844080320b101e40740c03e030000c5c4410781e1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 593451573 1250 593450323 593450327
    0x1050708090a030804150606050304051b153910050708010626090d1205010620101103071d130216060f090b01060503190e1510060906 59
    0x10240d8854003142c0004282101003481641d040d034010f40101701c00b444400d0a48041d208845150380110086240803082101f400824002c012003e04603400300ea0b064002da00c000360240c2c040480400f41d041000c50a440712410301038540400703a150803142201c4484600c450314510307442c08a003181c079210b061400700c03514a9502032540645803c0d01d03a5505a401c0c280182c9503004100e2401940203200c81072100c038080d881c100e00e4003903541403016203840c4814520081c8000825040011403d0070b02004000140d030046141300c00b000c465503400c0303a4403000c101d03282c1854081c2d02d10f49103180c1060546000c56494070011030103001c040c0c840c0441640e4424000c1800c4000ca8401544480e640c581698100c0c0107030000c00340c07141e085041600c00342869407800c0899040f540d011446a40e12004d2408007c0d80e081c2c0c4d540508502d0416609525201f90052040300e8403441c07080341c160710782210001103201006100d58441158120340034a02d80009401e903050171a1041c1000600005000250b041c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 593452823 1250 593451573 593451587
    0x16030507061b1b21030c030f121b09060230040909030528022a120d0206100f270218010f0c0201020a020f0a0302030a03030204050a0501031e0518030d0b03010507 71
    0x207685502c40c01406d1030242c4066407801c02e8083d00d40709121082d1040c07007100c090391141c0c000c0d41405c100480040315030450300800070422a006034055500c4003c03c15136a1200707040d00209264402e21000b44420b00b001503100500565001907050742c00c02d03040008050b04080600307038580c07007480c401c004449240b5100380044800b1408a0140e0000c0301c42181d401e4022664000000e9200006030300448484082100314003580c0200c8515045110b0040c3d40980c14400b45800251030aa880180350800983c080d0b9400103210b070b691005402da00707140b0b00f001d0301c40c10003002c107140810841d01c5507a03411800304103406880401d0300041d104840d5410640c0074130b100c0c0080e560103a000707005603d820340c01d00922003904520389034050542000000140e50401038500c1d4540f180d40c015071690703d01001d110300302d640340c1c01290600d0309100d801d5150410000c181d41a14141c201c0c00702c3c0a413950010a6010032803681801c40500000610528245454000b651146c00580c000c010558465000700d902d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 593454073 1250 593452823 593452889
    0xa050d0905090f090f0f0c040507030915020322061506091d060604260106080a0b04030503060f10050901090b0f09060f0d090606050316030507061b1b 66
    0x40c61000300b007041050f20407059015601d60110750039400c40d208840d20f000095100c002c8154003c502801ca18180f501403a07420900d90706080c450b60205c0d603103405a0310703030340b034180f02c50580d0100004400800ba0410024102002003184c0403130040c41c2040c4004d800384800360713100d050a8180000d1000c1c0718800134812a545240a0007140004c3d8a202c2c3d2843d1000d8480c551119091001007400e2107805842c0454004a4440707583c80740d510a803450a5800b15842010203030828901000811226180f465106074149403807036881e0358000c0021210313684170303031215007041200b44049680794100300100a8800242c0f80c030940b11355103e80e075031014400c18216210380403050000002d40e007424000750011508075031499050000354200302007116506a070645299486210400490900303201044101400d40208084141035440302c0e6541c542c240700311001c00c603400c8141403c0f400d41c5140342035066400814010810034441421040c00303001e006401c10090048022980328250321101610 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 593455323 1250 593454073 593454079
    0x91605060a11030f032a0903030307080a1b02010c02010e070302031c050d1506110c10081f080c030706260c0403150504170c0718140106020a050d0905 66
    0x1c0c140d00792404803002c940e025801c4207948802e100c0301580c444150083c40c0b0030140e043d80d030040280d40401102403822808054901c200b400c0012a009840120499600003100d04080b00b45882c0c441a10f0005d0180310310401006030303611400580c055040d04031000891030766000b8001240c4099801d51581c070301c1d2000030341c0359000d1041c06014865010308442c942c1c0c00c81c20801d060000e0724044800b950304004554850b00043c000612201d030300620940d504025110040000c0e545000124076000c0c030011140742840391000000782c6007943ca5043c1c0803403c008854400d10b00741c0e200704280d07840c020011010b109008400300400c2c0e25101d113400c8102c01c0703816000034019100410000460040c05402024032080400c000b0000c00c1d18420390b50b801e0340401310b002625186c5418071420560410a044075801c030704010100710460005682030a0311030044159030884000079000006100340381c0000d442c090410f00001d5055000301d01540c3c4a0300903819600d503c40c1e446c4080340c8100040c080d06034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 593456573 1250 593455323 593455327
    0x617100b0c011a0328060e06090d1e08180705031207061b091406190203030906070e030c04021606140106020601050406062012030c090a05030c0901030b0903090a0e09160506 76
    0x1071145c0d00840f01803d128010b050024070340d408020b0040c144801119200d0265111005102c1e242c0d5000c030f10000200d074880124000309013480d900410f0903002801580440c11840c00e4254010010302126009100c018220b60644124901c0028030341c004180131345100346480104400150a80703002e22985030182d80b001204c604004008400078001d01096030849400c1c0315407211146030500360b80d20301203160001c41c1c41c1d140c80400c41d49400720007842401002010a50038083d078400050004602ca0106c03805603e8103418580c0242c100318260025000758100480304440c0140203030f089060b20380b00c0d4240c86403a0b0f05c4030140b00540301313113204120010b0b08503201501d651425201d50b8000300d00140076107500c0701180d6100c40403908180c920205110300051041d10320300d045030481004041c06d4014041a00842000805803001440058040d104181c005040118280200c0c0c400c040001c00f02030b11140c4984055400001c211401031891095400c83c0c031a0340c0c0051030301c0c404c031500100518 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 593457823 1250 593456573 593456623
    0x303030106080c0a211415060904181e0b0906040f031119060204050301060515180114040e0a0c1b08130b040905040302160617100b0c011a03 62
    0x200380f95015140560401c0304110800d003581040104600d00345076a6900882d404404001003090281e001d086500c01c1c0000200148131901c85c03170152111050100c40015140703080e0b0303d0031807a1070383e450700080102e402c0b4040c0041440140d146051081d00664840840303580e2900520b90f2039405990141008110207a03042c0000e10809207441849018401c3e00e1341d000b00c40004008412840308122244d64020806000700d040c24851341008007011100300902c5001c2c1c201c1140c5500c541c025a46c00346010b224104c01e164012134080140b80d1f00040c0300c41e55560f0307400710501001c1040d144594203030302b4203480d00d12442c4102118204041c540012000390806030340c81038469481007014012054134001c0009072100c82d46c0152005110238500480c007890a03140090611800c500301030b080515041051000710f40c0b22030410000000f54501413025216a469080001440e62140c2848500051610f20a24064010260101d450955035001e81074940c1050744903000c2d81da882d142131001404038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 593459073 1250 593457823 593457841
    0x2072904110d12032403231e0303060a060306150c05010f060801050f01060c0b010e040602041a07150b010e04180606060906080a0b0f0f031005130b06030303010608 72
    0x40c29800004000042d03088403591044040c044448000001c80d076a140500140c00420383c541002004020045030303483d04541c0c91605250300c000400d01380d41003d00300e403650398504000541554182e01c00d044044a0b038505101e0f5281d004603426070040c02c00c100001003840c040d015080079160030303980a0604424034002200c04c04102c7c0c005031003a649503c3d40d040b5100840c481d07000602201400850245003d9004082c0906d041c1d104c441003200d078441c04008a10141400790558604152814850302d490400001030701482d00039910038040c4103a1001d001c0c181074024000c1c01e2080b40d000f003d96081c0700c0c0c040c049400014810380031400203004481d040ca016401040744140041c00c0380465480303616001d040b101540c000c100401d60182c0207104090700f1110050340301a800900303200c20302031000402c21a08551a800380100104081c612040c2e0f014056841ca0790641c0301c4c10421807410781e8000301002101c036001e4880078140c1e0049a01ea080100480b81039429548442409480e10811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 593460323 1250 593459073 593459093
    0x1050901021509030720010206070807052b0f0603021c060608010e010209090c25020d12050a11190b060d08030c120108010c09090e01140a02072904 65
    0x206030441c090700c241001c0e100b846054081c000c15000004580304e5405d860f0480c02466080a112003600d000c050764a011303a40000d50f142d002c1d00c01d24190702c054907010b0050b1618014420b140010051000c0030710100000c0c003004480c101c5404d01c1c244035140c007404c0300004540e0b9a01010350402d110014100540c130b411005055602c1c0b00382e0000420f169211001421502642c3c45544a0794001840315041c0c504003040070b4103c400030401070f141041d039004404085026421400c1211004811a010740d91a440183c151a402603250141102413080040c0140d1283c0241c0e00801e0120140d025a64000a4401d18110150064041d040c1d81920703130300100d00000f06010b07844031031405458001140100078601035000c41f010a600c803242c100a0300014441608400d02680c5404209442e041c3c0c0040c00008803021840c0c009140712030600080d01500388000b100d43d4495114080c40303803000d07031580100081030040d83c440348403214940d0b0b424406803c00c03a1050030341e2021008031300846e02403e1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 593461573 1250 593460323 593460337
    0x8090405132607050708030301030c0f140d0312020d060312050703021902220b040513080909091e0c03010c03020c0303153d020f03070f17030c0d1103010b090105 71
    0x20b10242400b400781e49151401016410117840354001000410402501c00c03103107806010119003012011703081814070b0034035810303600499203e00c66005011083c140100104004030003803000c2035645145041e05c08024000c40c3c40100e076103540b403040d4804050320650030f0315103299141e8040e104c9030050300c0d409040200e4ad02030aa9100e51200000b160809040110a0082c2d02d01c0c02d000c01c5119200c42000119407000340601c9100d44050101c10000c0c800c00308440c1c801d10708503405003040e241d41a40d03501e40b107410028440400722401755013401120004203144400c030120028842100c0000c002c60aa000f550700004107a170003400403602590b2580201200803001405294568021030511642182d070302038461890148022403000044105070110480c0c56540024000d00a601e003999035684508040039090b5241000081e04000388000644480410140303007d8803420081000c00f4180c0c00780700d5407040c1300e10380392203591810b0086068034101c8164003892401d1120348030042d141135010007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 593462823 1250 593461573 593461643
    0x70e0123040803040e010806060d030f2601080c130c210e120309100902030c0f0d0506010b0a090e040203070e0a0209100302041707140d031b0809040513 67
    0x21002140b440e40803c05030006142c16110800703030b035150003105802c090001c1d20080c064001c00b2180c83c0030a8101a0942d40c820b66883c1c5680107168450112a84030038401d905410440700d03100028043e40c00080210b00200e0891740c4807001c20241800004030f03510040b40742c002c1a1209006002c0e070400000102c0d181c00307a0300000c40d4036112002e0003402c22581c0e14034800808004018000c10003410008642c03601900c920400c03610a407500004e640c0c0c0ca02c2168540700d510007034248c0900c1e444412406840c15071140840c0c00c20b5864680507542c43d0003d4290130002640e00c0c00001d044038480c0f010300c0c007858002d0701602e040c0c4e09010507050440801007001d00302035003c0004c0541c070344803a0301c2206d40b2501c41d600162100d0500f4004c0030751901280200c181584420414000d0380550305180b400031000320350344024441c5e01e1406030703000210426114a84201c540d110707002d10103007000414496104503001c0016039149903180e00c15003444000585000d8007030041c006020140306410410220324 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 593464073 1250 593462823 593462827
    0x904030507050304030c0f080607020c04050702011104030b010611071401034b020406050d0e12070c0305161809030e130f0c0f1407020a0308190206070e0123 69
    0x203440342d615580c8560300854186a801008011300c01c80c02480c100505a40c2000e0300041c280810002d60b50000448423620595464010034001d500075440141131080d640700c03540c1c44a6032410912811031092240401150484600c60f42e0b900c0d011800806850b134001a4040001140380110024082896030990002c551555061b9180c1400c13a2080070052003c2c548030a81c080703004016003d880c1034100200140140070910400d07805c40c00741e440340c550070440080c510060b550050720341009418114400c48002032600d062140c0f0a61040a0340c0c06501102d03850034a05083c0071081805d03101c3c8007040c0400c050540b040c41002c2d080350703800d0390007460301075101465580000c04852503091100c80341a6600c1108a40715000c0c05200c0c44c0b407005003401c008121109a02521503142c0c41d800026009000800c0c104543d207034040300b806107400507805a00c5110010f0305141408000242070058480c48000441c2c0c94415110785011100680d65180e02c454aa2520003045c07a020f0440c111005003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 593465323 1250 593464073 593464087
    0x150302060f0d0f1a011806024201090c0c02100e0a0b0307110606040e0703020904080f0d09050606090c0415020f100207120e1f20010b03010b06070b0609040305 70
    0x80c000c10f0012200300704400c241d20311800024080c0e900c040c6c00d07001c10002c1c24078204141c980104040c080e010762980000360040d5403d840003046002c03404101d01c03003001380340108540d4090b801d045046c1d5125040c1001550a040001e66007028085c0009600424a80035032921611944094a00620140a540032144c0315200e484080d001241c18a00040241c0800c0c1c1c0440001c0080a4001e0743c01d403801c00201503d090819140d142c9800302070f0003500000082000c00c02c500007241d68502c8200e40003905c03840d400c0380180107021104000d6505100d404080b800d546000303441d40e40640820780c2120301d8130303207054140b40c0d0f2070f00360b1484401903000d0f00440b801300d000c00303000140c013007610460016910512841d0400000c0f0505d407c903410441c5000c0f90007480c1d150600e682152548640381c00400e003552081c11250825400400c0150010480074500f404a05410140f0716003c11002484503840c84414842c01740505003015204c00101d070040b48590a00c601c3c12600310b170182c90964a4148 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 593466573 1250 593465323 593465351
    0x80f070b0904091a04060b130212270601080c01200606041107172a0a030c022106071101090c1806050d0503030f15030a060c050d0c0e0301150302060f0d 67
    0x14105c0c1d080e14082d403030b81450000b51070b141c80c46002045e4015000c5040006060007584196401003600750300035200301c0200d12407820401c44007a000484001c5038900c0d03865010468580c2040110140420800143c510314540307012200d040000d54080106110f0b07440b6000c00001d44001d070207207904e1000801401001c20041c0c1103404090008044c0c0a82c0e500158541660075440c0e00917500700c0c099a00181c40a07201d011890b4a5620b4241c9008152401c0600009403184004403200c0d44c03030090000d25082d02c0d0700128031f00e441080306407552026244d4250b80030f400d03100c4c00c8100612400c0b1003007007070180d215854882c2d02442842100000c0144d21440898480014041c2c1510a58400700420812030130f441d4040e5400091010b540071b040102502003666240302140003001d6645486400000c40d200e041525080540201d0032720001c40201400b510715074070402042c1c004e50170326515407000085402110b08a030380c040c14803440c1c00301c00c1540042503002108a605a26180c400c0303920411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 593467823 1250 593466573 593466623
    0x170903150402150a0e1e0306040b0c04240e0109120f0c090204030503070605010b040f030204021e16200907080c090a0306050a051b0316020f0f0106080f070b090409 72
    0x19017a15555412000101040003100fa0580703542c0048084820701c0350729407404a01543c016038030042c00e9165881e100096580b5000b1500305000325005440182403601c44800c124841e04030035240c0b00210414900115468181402801c0355a45074481c0900040c08134581da11482d0301400d20010969101c00521060fa4429401039445620215054080c07203440c1c840c1d14011301c603014803146400c0ca00b0059030062041440b0192244c0e502082c41d80d140051400052401c07040701d04469650251041080b01e09864808155511381c000c04074211903000001c0300d40c5d80c2a80042054210703940d41c907021104140010505000aa418070040f0010340b10059508041d43c81007402203a00e28001010900b160002848a41c04010040c5013600700d0100b601241d4000c581c03168a003400c0010030500ba460042d02c542824514464138408441142040d40320505692100c0241e0f085001a50441541c441c0e0314020200d00d0078041115023041c0c90f007a40110641031141009500000450901142d08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 593469073 1250 593467823 593467837
    0x23040806090f07080d020c011103130f090e0303040f020d03020703050307050a060b0108130201050c07050a08030a140a17130f050106180e061501031503080717090315040215 76
    0x796015000c0510400400d010450203000c548000381101240d44500942d030350090000c041c180550403462451404d000d0080704e54040c0003641000040303564410782e07880c0b103c0c54800d428056150020351101ca403408822640030399006a013841c0281c100d0340070071088071200ba004030150b10840000100150092001c0c1003503130301070000303406800d46500f012000e40721103021080c1004481001c00100d10a40e035807005a0b90340a18200391500c50f050b8165143c401c5c284c00c6240d1003148900001042e4030000700508801c00241e4420601c8038211400b64480e0040d00424070104101e215015043c00c0c0b50703a6819030242c8a564a45e400303282540703c988824904c0e040035625651a00c0040c029a8104003c1e401c07400500c050400c400240d000440351101000b07084801600440f04d1561a940c0c40f94110322039940c0510090389000359245090b50880e0b000010403503080c1050080305582140002c2078031800788001d0b01800700c2000750086e02c030300318034002d008a80c0304803602c0517070741c0b20701080c3c000d4488 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 593470323 1250 593469073 593469091
    0x108010905060604060612200f070507081204090b0d0602030903120f07090b0309120a051c05060a09090510050108010606180311100c020d030503180a0323040806 71
    0xe0411107050032420140000c210500543c2044800c10007698801c100103001040381a00103000d046080251054000c6200418011080070034200c4890450100520000d031094003185c1d1501d948450054a401c29050103070b1141405000c20451084103800c03100c02000010245459003020303a444000302e80081d501d1401030b520114109054101490000d5001040480c00309814a020a00140000c9031030082c100e5000d00030000c03e804030720402140034004d2408030810b0b00ca9604490041294202840400340241780c100a0304e00503002d0300c00c1600503200500002c5090f8146a850350103007240310b108840c0780c41054512200c8070514480c084c01b03000d401c00042600e5243c2140109400f0030780c8003001d081d40341c0f4007007000040c0031800788142001c010364110100895190703041d1071241300f14502070740084400392044101079205008610030040300460203000c1d1341000c40d2544c0c0300c10185000b00810001551400003114a80142603041c55591500780b030f058442c181c03039081c0101600c40c240 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 593471573 1250 593470323 593470331
    0x103140307020904141e120c070e0f07021509030412080d0f0b03120f0a080417030106080105040608190303021b100e0f15070e0111010e0d02010b031f050903040e010801 74
    0x46105c2c81405014120780281000194820b42d6086440e1102800b078205c2646140000306114036860500005d001040059005d00c19031401c0c1c41d001e500b5500840c2c8600040c02111365005441d078100300c8141c001d03512980110b0a083c14a4500100c401c019107042d40e10318410300090141e04000d0003014240d07503180078042480d600300f40625103403c01d080b03591a6111018001e5154444008d000e6900c4842c1a1810144607115414003000030064104410100c1c0303400000071502a40100030395040b21010b90b0100081e40c0d0303135000543c4400e42e4822600b01060510075000210388030350040d002c0c015902c1c20200c500310486002c0b52600001740e407100c104548034040100303e03500501c0070b078903200030000c09400d840306a00785028425200506031020700040300c520684503485241810024031069008001805214074060740d106441d58000c8015801c01c0d04400c01405c010401c00c1050344e96806001c0032000802c0018041c0c0b60081c00e201e04c902c414000050fa504c1182c10860081082c071000003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 593472823 1250 593471573 593471603
    0x102303011b0815040e060f0915070f14041706040c06030608101a0925050a050a0507050109050d09061205071205040c24031409060103140307020904 65
    0x5825600120300e0005002140310400307030301c1d60b00000790962218a64040b201c02e45500000100107203010300240342d182c41400100a060144208428080e00c0200d048603000410b505007251219001c03110302c000105841040803105028a82c1c050b00c80c41d100b4804c0d41800d860f0a45040c1030303000080290042d034003000c240814071507412000805011645400c2c800070341000c404541e20418005140074035584c498110000201c004171003405600c00801c1685941800d0345199804405485c002d2103001c040003200c0201c2c0d006074111400c82d150307074036010309080c55400c0c240e560b0380061105071415500c030780c40b0200245051100354a421059112600350340c1c10103800074020139140021030080c9141000380204640c000803d50340700442c00d04007149940c0d451074003540c4056143d0040000580440e04820302030205a403580d0300c0b4103199010069501c3c8820a020381c04c90a42d03028100b50401e50041c030204039280420b0f4091500c0300210f0303180aa0527400310390440c1e8102c0d000d40c1c3c0460942c0c050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 593474073 1250 593472823 593472829
    0xe01200f0a0308010902030115080c070614041101020a0506130f0b09071502070308040311131a0118030f0209040827040c0309031d0409060f27030c03081023 69
    0xf01c1d0140100c26011425507040c140200b9282c00c0381c800900034481c0101c0064a4a41200200d03582d1a52200040c02258240700080d84224000e0714116804443c0300229000d6503c001113219010b41c00400810b103136140d628000b42004c0c200042070b03945110150100e00415004041c460040300f04600608c1b00a2401c00040800d8104200d80da04540041000300049003240040c0d4080d290081c0d03c0004c60b24031800010b0f812800007080280700345c1051190011180c481100d00c10054080c0c88070b00310030345100030001000907540401031030f283c2c0001420016041144515a0182c0f08008103880c00e500c0001f03019511941c1c4512040c40f043d0030440b40007600b03181c01084022169814144446c1c400c1b0381d40075200981080d1002c0e00c1c1040c0780f07103050040d6215040080c0a5402c40740801c0b03c0c02c0b52407090806011150a00e50700f2001100f000100d11407031400500515030550b441c50079911081d44d00320341c1001c0207400750b0201c1d260444040307485070704441900e0001d0009103284001e0090b807414 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 593475323 1250 593474073 593474087
    0x405010b1207050d0b210d180e04060b060c0619021206010c17070602090f0f031002070c1a0304030f0e0f0409020301020706290f010e01200f0a03 64
    0x2100400e00010710a441c00080c10441242c1c00020030300b085500c49100c48503481c01000340180380d80d88894854010328104910007900c0000b95442d0054402042002d48240c0b07108103019011031070515400020010010040905900940301e2080840c42000d8000041c83c95007040700007058580114041c8100e2500011a40001c0340040100303609020417140140810000104a80d0501011550660420408828448130003081d41c00d0a6114100340c14000000c0d00019a59400b509c200314094541d8944643e002288640c02001098546500300e42800607401ca9034049454180710103011512681031000d07012a24020081c00b502c03450203060052420f05040c59010500550312182851070302c0704004030345a502e0a440210700d03002144042402032041032800f070f15003458400007801d106100507452409061081e000c44a01c0042010002d65003407030701580d80454400103820301b29501902080c0505265420903150a00100a02a040c42691549a0080c0d000051400201508528 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 593476573 1250 593475323 593475329
    0x1609060e0108151504261504020d030c0b040303050a180c05060c10051312170a0b030309030f0303070f020c030a081309060b0406080633041a0306040501 67
    0x3500000300c035039040002c2c040382c9014000d514500710500c0c00c1803198480d80754513452140154103996039241d58000c100420390901d051400f0050b1098018914080e0000784034100a0031004544003685486c2d0070491884505802102800030583e008030102d000000442e1289010352000314092030051148800c4541001c80f2001c03a0508200610210b09200144002d5410035910680d84029400d012491b008500f1200c01070641058200428285a0f41805400a114490100c07040c0300d045019a5203400c016000140041c51200003808080c15800c42c0c100007101400b074a1a02d8903e034007007820f150000ea110019130f0700c00414084540e6101440c504282c4440c80500460014200003a444880740900606191804550700c120041d11041038001401c03600c800b007010380d940c0c21481d2076a40040c0b00d0f03140800c09800c0000c89904104034401804440309051205110324825011020010382860303da04880c14403020484400340b1140ba000c12000070b008640b00d28050702040184e4805030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 593477823 1250 593476573 593476577
    0x70308030f011d0a05180a2603040b0f06012106031b06020a020405090321010806101410120612050610080d030e15071d0f0f131103160906 61
    0x10840c00303030a000400f100c9402c041c4080000c10552507945800c011200001030103030050060b42602010030902d0320742000c05140c080c1040d55214141c104100c1d1900007120301030810080e4000059406268581c00e03607114805041c500403a41c0700c01804140b07a000c1c800102d42c801d03034902062050200e18401145466200144d41c0c41940c2801c20007529035500c100000d0080e510781021030417140d01407040e90b848001c8212040c0043d0341d100000030300c01d00b00b8802c45006000301070200d80d4400c0c1040c164020303501d03d48036100808054105200503246545064401c0242c11101124140070324002c1c0b2008207034121603607116034444c0c2400f90030503c024000c5005101c529408100800001c40c0e16000101035080000c0d120b82007081c11170514049031114541114020200310070300b90413204200c14003290780d1050364655054411700218100c6c1510255002080195403040340c0781c06260603d801800080210b407803404680520402e41042c1c60b203080b00b90b80003034000c6c0110707400290b10000700128 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 593479073 1250 593477823 593477849
    0xc03060b0c03090d020d0605070c12180303120e01021c0b040608070b0c0c030d0305041e02010915050c070902040302010225170f250506090901060f11070308030f01 72
    0x3941da070300d21038004564050305081c840304c000c0d913864a03d07403014580c00c031201344031a283c88000103250070200e81088030f002a004502c0302c44039100302c400500c02c1ca0003c200c25069030075510240c84600110114405158807560080c035072030004c0c0060190141c018501030607500d000710301c00c800c4c0d4804041715030080d0f107040801c000303054001641d2011505904890361f0398030020040b039420404400a4541c16100381c042c000302242d410ba100910460090ba40419078030081e43e0321540c6074003040c40103030000d160310a080c00b43c0140803030414503441c1903003095498030b00c2d8404210304001c0c40c0ea22a001c100d5000c2820025960103005000071307030b9036030b0052081c0445101c0d110304034110719000b0141c0c001e40f15a055100c51400f0441540a000100200c401c818848024080305001080c500030505c0985603000816007440010344580701002007005505a080a4085540e403803c00c03051070400c200d01180a49104e401e04c260000355000744002981c070302c4e281514414611060380301c1c3d0122001c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 593480323 1250 593479073 593479087
    0xf0d06061107171e070e1006090b030403170601020115080309010908060c030412090308280201061a180603010b0406030c09060c0609020112140118110301090c14040602010c03060b 79
    0x1080700300400300300e404080018a000301c03080d0f00d000c0e00d41c1c00041e594106c800034008800014421003049401c45d54070140c0b44d50b19200620002d000650b001000b081404003209203414840c910b40341c0c410018400020f904001c0e80146c2d072140071031350280c0b0031600002050040e5580c800341040c082c0c00b2000003800701d811304c04480b00c1c1c644070040019140d60160501007203460700c1000b5800086810540e981c2c4c8601e030980c4950345407400852900381442e8600810f00b03071540180140002c44500b140c01004010341440020210390081c1e41c5940b100081581d000d0990741e03628007550103401c081400c2d5840728101000a000c84000000810500c4160340c0c00b00415580710501080703480d03100c02c022030502030303600c0142d40700101028000e01071410711040303c02205064042a048591548141c200382400b6841c0d9011180740c1c0c2c80072015038404100600058505412141c052906450048181c8210220000d156000340c4c212100503512050710940e05c40e03040c0200000f40549180903450516 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 593481573 1250 593480323 593480369
    0x15020a020d0809041d061f0b0f030c0906070803160206010b0a0521070c0519111c02040915051e070e0415120506010f0b04050103020f0d06061107 64
    0x602400100900d0700060b8003e401d84540e046030300c1421802c880480f8081c140003100380c55420803514540c5050780790001d0381154240034109000c8440146400380341017070060454081c0d5100400e04a400c2d0710412241a0540b01d81c030040035802c3c0145111501e034180112102000c1d604407541008550000e0014000d103e10070040f50280105030804075500c51170b42010807910603080d241c9090540e000c004110a45070402c141100440c8a90700303592500880c8225603903114200400506a120500101101c5092032152120385051030304005001d0391960b4000303001d880c00040112480f41e451014000c2c42d091a024040c0c0103180e103208104540044200e00b054000004c01e04810491171089442d030300c4d2182e6000481d2805170781d40742108192140d100d15850302d031601c0304962500c19203000040112170305c0413440c00d480102015618003442e2800460107504030102ca4103a802c010029000e041c50765202e900024078a50300ca9440380c1003000c07051400c2003203650000c01103403c001038143da080303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 593482823 1250 593481573 593481589
    0x170d0914010b0a0b0711210106150306080114060f370b070b040204020a11070b04080607080702070b09040204120c0501030507020114060d08070b010b0d0c031107150209060a080115020a02 82
    0x10300b80c0307d840c010b2980010601c0388a00203104201c0951910801080e070308010500840c0e80d007419142030003c00d5440200608941c0b8100800c0c20003280c600104409150003442c446813050001c295048840003800d600c800d803100000480300c1030085181d40c505002030071480c81c1c01080020b100364140807440d119030100c0c00700140020300c40e45d40003400d5003056000c0c0c4199000c0c8030240044a210380e0300d41e40303005415445401a0f990b00d2050a0000e80203070f100d00c505a2194285501400b08145045640c10040d04000c440a500c60b800b0301001c24030f4000e05c07001d456003601401806211900d81800035045403005448102164101007490010f44000e04140da0004401c3e112007600d007034a401d008405000b8400e0040220000f10000226400c030100038250140130100100300e03c803107131881034084030465a9145026441400442c01140c0415541c04102c00046009480e00c0101c01c0081c040b540010b80d11408503842c0070040c03003442845911a11060030a0009061201c100d400181c618 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 593484073 1250 593482823 593482853
    0x90703110f0f0d083a0501030804030b090106091a09010f05010923041103150d020a231c0614042102011820010309170d0914010b0a0b07 60
    0x556822145241003000c42e008803171800700260701c60600d00480c80b0700040c07406400c00f603014a40041c00044040000d0520456040701d62100e9201d2402e403440d6100440d45400428500301556503060010303115540d405880307500003a00c010140302d05440e00801c0521281a0059240042c054405010790398100316400240c404500744a45152004c010650800c0b0400764441e03009800c1105600c0c5100021003e58001c2c2c40c26211400140d01e95002e01c04640c040c620080c0d0302000c0e0a1040142910700180491080140320028240c0c15507003004c200ca038416a42410504201e6407001418880d0910480040b0b009030a800a0681482c1d200e07000c0784000c0c00c131510848124441e1503100d1078000d50080c40b260111110300f9000f8402401d004034103a0040f1030041c42c110f86400308540d11341c400c0c03040041d15075104181d02480c40c80440951000e41100186640042c2d4510035000030030440788040004980d08000865036003074480c1445807541c0755034042180d04500b07109900000b10451294818 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 593485323 1250 593484073 593484079
    0x90a0e1905240402090c07170c1c020f0c06090a0302040203070504120501090b16020a0b090a050106150219050a110409020d140d0203160b0901060806090703110f0f 72
    0x2114941e0511508001d409003880a52a0103290941400d500040d6480d00c82c3c0c1c0201d42c0340e40c0030303a034200c80c04100d03104044006190101624106190a1a070300240c45162000c0003155060202e00840d418108420346881c070150b030255801c000b8880080000c0d00c1410402d44005043c1605c09000c40e101e03818030b02000340300325000710010700c0080c0306a082d50000c243d04a0207880d2807015041c8240248114038040d6a00c00408000034690800c028080307072010082c0d4014201140703252210601f8100c05000b1038014003940c00088086402401160050144200c8548060501140c0070b40742c8010192485981481a108803002c140007003017059019410452007031801e810324000a00030800c1c158000e40c40140d0400450a004a4218004103980c0c03500403213003203842d5000c0982c1e80340104a100c3e916034481c854000d0002d11405001c542050b1200c00104482c1d4661135106c0c10404120303175800c81c42e840507004000340491101000705400003035a202a882910902044021290302030481c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 593486573 1250 593485323 593485363
    0x60504060b030a050a0209220f05010b0702041e020c0303220302060703050c07080c0309041d0a1e0c120c0603022110030803100501080a1103011206060f06050702090a0e 74
    0x161440081c1c0490310f201d8801414890703c0c0d50230840c1b0b641ca80b00c04c0d48812061628140e4044a001c09a02c286816104481c4280d400c1c03803070355420400503041100d03500800300700c1070280354202059800079028220901001d19104d03e408003400704103024410740c281074981e1205050f0042a00410300ca5005900307403074040380744d07500c42c0d40713044807807040b035400501c802400a40e940d103510010010b40756840c0d04407400c0c02041c0200500c00e8a660141110f08240d41240d00018000b4804440300c078220032884040c0d08908240e0340700c0348418082540f1140c46201e07800d200001b0088100d40c4400501400d08085040468540300a1071000490814584110500000c161f00a106802e15801194010401d564a24019515011000c3d141c8100d901003007120012524420f994002da01020120080301410f46c3e20348821850f4940342c0c05070a42e800340d80c4a070042020919a601d00001e4081c0780c0f5a07540d0341c8110b105225004900400340309155203071511000034400f001c02d0000c0d03110401c5403915 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 593487823 1250 593486573 593486581
    0x70213090c1d0604050402030d0c030311030103060912030e2109030703030504050139021c030302071a07020a1220061006020a0b0105091815060301060504060b030a05 73
    0x10052a0321680034100d403140c284002001004100d25005100b1603980ca002e85841d103406000c203458065a00a40c183c00040034901458400c1c2800158140a864041803540c1b400d03816004581c0280c000fa40d0701c9441d1044401480b00071904009800c04a140400c03440d070340d0503002a202e00c80000c07010610040e05501c40c09614294040d100300b20303001020390301d6040c0d41c1d10340500141d20500c03507a80481d0381407501c407400d1000603080e10b0b07004002030f442d000b141c54140781d81c0d650080010790890b4850303e10070641c55030b14a0103940741e1110784292001a6a000241030100c99500400c2c140095042184100b18403150301081400149610a03052a800c54454030151800c0e01c042001e5200140303050b00d9041d0541c40056520701682006c0003c03014503032500000c07a1202a0000042c003829005c030010803580c1459070341e941d03000211008000042c49030130103850501e034048107181c0c26200c1841c00d20005240c20b12500300100000c07103080242c98a081c8140700680002404d040040e40d40d80002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 593489073 1250 593487823 593487859
    0x1092102100509060a09080c0307050a03060203070201020f04080105040209180c010305040201110f061012030801060503220f0c0821030402210d0f030618020706090c0b07021309080702 81
    0x2c1e443e985001407800341c8132094820b0040c549000c500c0307607081a100e041e11501032400c0100301074059030380c050141c00c1c01701d0454136060003950026020101311365080042c2409414414050700281070303420000b00e1207081c01e00400c07103807800142c9000d164028141403d50300480000f0020052202800e0201e001e9407180010b0354480700d15545442e48d4000c05030300c0c1c0428000421400c0c41034400410741c44c4141e0b02c0300303c00110304404410041c0442c2c00c000c01402424080e0019552008200700019025070101b0700740f1000e802c07100411281da400100e4000c04106260103c50050801500145443e02899041000459120071290072000d000004901551030340030201c01104500c2e06180405800d000182e5641c0780202c00100000305e140c010304450900c6801200c1c21243c4203007120303500c46400d5681600a5101d040111010f55030b81004070001625051020003e000d524482a2200d4031030050003800c80c080100a030020703203821488000100c0300015140703080d40542d43d82117024802602 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 593490323 1250 593489073 593489077
    0x1107060e102007050a0b0906160c0506130e0a090b070e060f030906240307031203090b090f0c01050c1020030112060e06092a120c010921021005 63
    0x21085601c103148082c900c5400050440100c61065031052812036840c10502e0301c0c2d0082640680d400a420084a0b127808903114441000300c3c018000104000c0c0d5410001e0703241c2c0d000018184030360403020340800502d00346290f031642c4510740c24010b22034082507594084460000030007400a000c1d52100c2e015603600d400065840500d10440c00503a04e06003120456502d1208488810403c079141c401c1c030041e0a0341c03504081c01c462000c2c006280356410350b0b60f44451810b900d0341207001c0503507800e13409010810005a407401001850b024041038140220302c0d9003071101408282c0d0600c4803c1129408010001443c1d40503074031807400000c1c1603241080410f9601d216003030403036004030b404000410b11044c00b03210240e40c18801e410030000840c4070081d25499440444070303042039400445141103045060720800300411482d46694200e000803000040f610858403003000644e9000b4159011956003124003140601107203644001a1400f8054017040134611100090181d210017800550950050003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 593491573 1250 593490323 593490347
    0x190c230102071e180b0a0b07151d010c08070216231c03030b0a0e13030c0309081b0a0f080615030a0606090b150f1204020f1507031107060e10 62
    0x100a190903102130610001a145000c00e06214415907a00051000081e40888050306e505ca880070000d40414800744005118187d9842c0e410f204a0f400f4030800d030021f02c46d44015041540301c0201e18108070400a2038174010680b03201d07500c2d07800c51050143e1802901c00c035a01f40c0010b136200042c0d03074903400441e800c40c01c8030a0f4114542c07100c0707e82e43d0801d905600f145110903419540742000c00e95400302071401c80700683e041814010009129070200307102e0140d14002e58020700308084402d594007045890b1100d22140300c0c0340d40a02090b5200710785480004040105403001107442c42a0510411a8980324064400120420f40b0801c221442c1c2b801e101c040070340341c2c0203007017009540e98070314001d0064a0f010034031911517401c802c15103411100c800156641010301d019203c1c01d01e0300e44000049081009031041c0d03030006210445010aa451004821420300c240350380c15103a143c5882d01402d0404801c002e21840c1d0850001440855030100ca291000081103c00764009030403031070140c4841c43d00c69 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 593492823 1250 593491573 593491589
    0x3191407080321070c020a030615180903030b030609120c1501090615080702060c090d0b041212230a0f0c05130504150902070203190c230102071e 64
    0x1146400c2c107050503d41601c2d401d00d8a180202c03e130307526460116299a044c120007580103143d00810300110300140e0104c3e9040d00303051000d0802075100c41c14001c40348007902d0701e10685034858100b1010590f2602400d4038030341040c1d00030030301802c0007401c0d81e8440115004c1030000d140007043c0301c8800b100070444005c040784261104101961100150320241c00039015000e141000202145c500038032a6003c20701c116103940c050540b940320100454516480000070f20f501032f0800004501140c17418031558000c1d8865514046280c10000c40a00811a0f01d140d04951a1400c1d960380352003084241006916108032400ca123541e9500c2121350020144041c0d80101c0d24602106201482d03001402458a54500d490002c4202c2d82c1c1c40420040e074180036125090302503a10001c01101e503054001c0d2005c940300074192405119188202e41c0b210620090a40e46100c00e52030400030b0b445040709103400441c08941100300038880b00000303540c907030f103a00c0761400352000c1c444400e000071038410403103000d05218 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 593494073 1250 593492823 593492827
    0x6040e0c0706020c070311221d060c12010806090c0409030306080616090f082a062709090d0c11061204051009051905030f0309030c0c031914070803 65
    0x592843c50303176100d09000440d0030040341044034041e4501000b150455840c00d1140010130a8800440701c007400790105030a85186100407036958501d024072056109442c403580d00c548804c0c50360219004005d06900a94280e04107400f03008800c800422004040703002070300c0209100310b1502c0c0480003017100390b00441842c0103200512124184802d46080b04a415903120310005407600000980b80e0340d180b107058006e40c0002c2c2490700c45001071041c1ca0b0f81c1d01c00312004c41001c19503440410010781c07207240250078640c803119039a0301820700040c241c0001803060300c5908031850079030a001c0d0b8446428601d04244105000b00504200320785003181014903014000316212424400c405801000584045949016101c401c0100068a1140c1c592044c1c01000902021103400b506000020075450261a1b034082000034009851120001390301420b4000015030303a410b14025101c0c107100c0300200c01c512035000708120a980b0b0700000a02d0703000355044805c00e064807204d080502e2508a451340454154000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 593495323 1250 593494073 593494087
    0x9020f250c060f020c040b220f020415020d0201090c0501081803041203081b0712090e0c0904051003111005070506070f0810050105040b03060409060608010e0c04050606040e0c070602 80
    0x3118001802c0fa07885602102c1c485e0509600700800d450050094a4102610115418203030b8211007000b1010810720000003031260815038040c05a9000c0e42007a004050101e0031586c00590400c0092854800340c0700030001d0b5001d0b95111800c00f0014441c481c10048960f0200c0c510403441c1c880704210920400c22260b4039541d410719801e94842410003038022032849000a00c40d05056490303071a44100405101d85000c0300b40d81d501e9500d07685510041c040115000d0007281200004190b2400760350190030303107a1a02607040410003526001044521410204001040001c022000c40d2460443c101c1f0000203c4d40c040800f203401d4056450041c01520480050250194001d003017030110300155a55000c41d5900d030b1407500904a03a51042c0c0c1d0020f00704100410a10001c4000385820080007000071545c0d0034030b600d07504e06070780311500032681c0c1d80d544070002e0380c4454081104210b4008251014421840c003540043d50358095840781000e14442440081c88104c5030404450525074800c20440d21100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 593496573 1250 593495323 593495327
    0x60d050709090e070807030b090a0f0c260a030509041e09020f060403030f0305071403040308011e080c090c070f0b0601030b04020702100e120a150609020f250c06 71
    0x12603031042542e090b241c00c225100c2e400001c50307000300f40e99494000301107a070701d07550300d01c1540b010080034080a801524198400100000d980100d4a0300506c0d203035844604254103e802c3c4200b0103541c4880c0384002c081c1020340100480c0c1010b00c6501030070156103880800b004079001d440c2020301080c03940c1504034440c0040b41154040020070b03009072040c0c00e48401d6a028840d01d40b1481c040900400c3c51241040c18991103500300726440810b034600820844468074001e011504240e90450208158500501c20300c94149400c03803c0f110500e400d5400c0307034503050403940c5900c50441602e001d8140880052908484a01141d4026a0004050500100b42c3c14000314400c000d03900c0d00e0000e4100450710101d442d05000b03441c64960001d1907415204c1102005650703031220310814030341007040e5041200d270769401070000f0380340345010b28843d150162000b090003040794056001510306a105102d45114045000c0c1071f1851000d114440358008202c01d01010b602030007920008119950045020400325 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 593497823 1250 593496573 593496587
    0x2090403080417162630040302030309011406060a0c080f040807030605010801050f13030e04020310030b130b071808010204090e060f0103120e0105070803070c140a0b07050306060d0507 81
    0x41d008080204008403910305d00b10840c0c440c8101070b8400b1005000135441c50040c20050205100c0244d0b10303502e00034002d55500303481c0c0d008550036405600007200f00640368000780510b03450981744901c00103042c1740900018245001c0d98410300304010b604001001003181110890701c4203014070385d545480720b580e400c86551b54549800111030b400e08020001449510502506025040d0f0410740703a481e81e500340340c1c01ea50000028084d0204031445442201c0d0b40c0380d920086003d40c5d40b40580d80005811400c1056064134043c02034012200e41d4690341020809240b00c05170030101078030b401199074110403e82c0444800ca900140500c0d44000780001d4030343c2040c0c0c00310460800b45070545126984401c50201d910a00340b0014106018650045165030300c140281c07a904901410050f0a1038642c0c0c560417050f1300304842510210302c0036280c200130310007520300e248039141d41c05000f4100e80e00c469480d10303582003010300010203100012000c20321955039482500c0d00311401d0300b0100300c00e29142000401c24 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 593499073 1250 593497823 593497867
    0x1030201120e0606060702010512010e0a23040b0405070e0108010f0b030a030f1107090501031b08120702100c2f040905211605240402090403080417 65
    0x450000002440d0030101070140036401c00b001c0003d0300903580d5100501040b0390040c0b1040381048010030411080b0452487c00c10301820385000760250901e072441d505421500502003c451404030301340c01c0d800100610700e030198050350000038510552034a140151812030a40c0010012104290000c161040e05500509100c15124000c1c072458400000381500ca032110070024002421168140744031718028202c1d5514541c2103030448004e560790304140d9084840c207070021640c9000500038024010000015040a04401000f07841000c1101071600001d10400c800240aa0704204c0310398400d9024400000742070742c00c01060421030384401140e0f82107102c1103200014100418080e0411800c1c05c1c480c0b440c141ea8080014660105894a880c0c809000755601080740001004008048080b07507600d180c00030301c6130008100880d0b6070704120b040da04058010040c42e242103810440984c0e10851125001a0941449107080e261824911290400031060551030340c1c0010f0381003c8505564000c42ea1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 593500323 1250 593499073 593499077
    0x305090301141509090f010f0b0f22050601140304110103050f060d080f0405060a0504060306050913080c011401061d0a030c15050c1002031e04020603070c060f0e030301030201 77
    0x40707151041044411030409680f09001030030f00c0040f0aa0a0500d442c0c81c43d0007034007200c102c84110341141c0d90035080d29200c03501540c480d612841c280b02c090405a000e4005080d00b118a0980d9403004000d2240030320710000401a0552603502040d502d90042d040c142c5002103007940642e0300d2800d03003400c9100b40740120100c0e000034502400102c002507105245405064000c20940d010344444e00e036840f43e500450950800c103c810800085e55545e82d17801001e003000e140c0c8500341c40b946051005000c94140381c1c491400740c10440c0811108030481007500d880306034885c25141d02d4500744002540140003010340f402200c0c9440d400420003c0c2c0081c2c0160507907040c840c0f415080301e008014031180317115038840203100400400c03041c00710400e41e00340003020312114a0840d09204078901490b180c00c1d40c0c5440443d07030560000902c00044200303683c0603503c8050703860004060400360301044440c88020f08803c00c00c14060b034000304101d29070300082c0b100000201c0502a400d00007218075202c3d0f00a10040740 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 593501573 1250 593500323 593500331
    0x3080403030e18010509060112060e0a05040c060c021c0305070c0e01080f0a120813060908090907030c140901030609090506010e09060f010605070c031b03060e07120f02030106120305090301 83
    0x101d0041c42c0003580d81625401b801d4910107813140030040d039900d000d061a51741900e8072403201298242580400d2481010f2a03000450a030809081806144666420407020010b2180504026860300071140c400e540340000303c0000795203142012611030140410081a0740078940000800c0082000d00c0e5059a00c4042562070403107140d1042a42c032005240014101a2300d0031201d00100d0040d000355038080c00d04400344000e001d096480303104845c201101113131000c20200d10041d441c1000c600d26940400c141c01e040101425491015040b111000320020120b1000664841d699120b500018018070031103a00f80207400951601c0764440348240600c4000ca4031250008508140025949005a8000c00390700c0e000d9080c41c60840300c551003034a0544110f880c04000000041100120305504010982d4074003000c0d05520b09035054820084078100c9a6002110500c4a00d005445c5032010560180006200410610100e400342c90b9560020135012045c500a03401d25030801c005080d0441c007100200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 593502823 1250 593501573 593501599
    0xc010e0a0209090106120609020f060f04083a0207050a0303030203091506130513020d1235130c0303020d11061303030509011d0a15020a0c0f060603080403030e 70
    0x44d0885d10103203d414070f0130038030002c040040b4203594004c0764040e00162211842c81c12490105405a00c07851f50381a4029001030f040100341000d01c80109c12007296030300f2101003941d150300c04503200f010078150190407181c4001704490324001c10500d4024103000e0622078110381c5d00e06003d00250001c03a01144503000b02007400450400700134119110320b000400d540387e80c0c0152a9028005d1000401030310b007241c0c49116000c0541c0e954509001800d01c030f0460461003a600b00c9004200c010207114180c02392040c040c0782c07142e992410000c1880040c042c140c51600d69214a565058031b4040c4d2030241000c480e1038404020b040e8045a07084064803161551048880c0d48904a503807004100d40b802c420103024a2120002440707500004d400c20907100004c1041009401da640c51410b4550300003080ba80701270b01c0807042103000c000c0034a0010741c03010300f18205449620058180c940358100208140d070202c0c0d0780001c00c41250300100255800149071621144c51b03160141218130304444107440b5107046c014030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 593504073 1250 593502823 593502841
    0x1c051618050408041e0b0f0406030c020105060604090905030d06080f07150f030b0409020a06030617060405070303050a11060a02040f270f0e0307050a060e0a0c05150c010e0a0209 78
    0x1d140207039840209289031900d403184900c005c40140d03c1000d078500f51207030b001900c811200045c048039076517890455034891410101030300300c90440143c8070659040204000e1180c2c0c42d00d0551703040b111000720116003603640e0710b000c6040d88074110040100518101c0081060f60001500c0c2d5460800c900450b00b06e15110304804603000d904010743c200003a000c1c00c050228a01c66080511641d001074004a0890407950016040d0011900500d00080d030342d40c1708108120140d0312264150a800700036104600b800d494080d1112003070300000e000c3c8040020701c1c0c002d41b40b0904020050040b09001d41d0440e040c0014a00042e501600c100b8000c047c12100c0890202890400324100103a1010107951031120031104902230700b080c0d0304041d00302c2d0b41d621401c24405801e00c02003840c1c5109202501030640140303000f50803191100241c000b0780c0c0c01312840500054904500c2401c2e900304603001f58480340c050043d40750b58071401c134240d49154288110032902c0d05000940c0d84446108607101c0c20309960345900 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 593505323 1250 593504073 593504081
    0x402031905100f290d09140c0a12050703020603130822090c0e0906011803061d0f0709020c011808030f01080d0c02130b0a0b030414070b03061c051618 66
    0xc1405803161299070082c19091400401111145e81d001281c000500d03192802407001030030740d004d525040300c00c0d566694585600c610000c0c0c42d0002090080783c04503141c142e0703261000e00000b0300038000000442c40210240721401c0d6481d62050b070360b913a240c18003200c3d41001300026040031260001d015001c20006898000c070500c4600940d40d03031141440e968108a40c03908040c003150b044c01b421032450203d145140d820080514085c400100d044284144850000011a400d01080b50020401c9855140b0013040e1402190003100300503846007404c0458034010000b407a0092200c0001d403c1080800c000000950b1080301c80d0b004108090f80d0b1001071a440788520b000c0003000502c1110910014981046030b0140a988030390000780703051138080850410303041a0000750014402100308020007454191007000f40044902505020703140401c100b4150201405851142480c0c1400c6030a00c0100c1080001280e0418112183e119040340d0720200b1442e28040c1129501f598075600f1318004003030103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 593506573 1250 593505323 593505359
    0xc02240421210c0b090d080109180b0c27030c0a030c17030c010614100201060608060d05031c0209100309080d150f03240b09060402031905100f 63
    0x200d111100b03410b5042c480c54a060019409042c00719040c05400850580345002d441000c1c0303a4010b003040c0d030001e1805046420141e0100003414104a01c21000d170510700007041c807a641c0810900b4440c0c580342d84c2e01c03546000c5c6108212110006e04070300c0c0c11800e121044d503000c0100981c1620007203143c020600041e40c40324000074049602e10042081030045620742100d00c54a01c50590b810a03a82e203c0302420f61316182d1200322a02100c003060619413400c54500d41800025000030070000c0c0c6030a04c017030800300300108403d220b42e80d00f8411078280b0205000311110206006021151032400e6914000203410150f9401d00454000c1e100c0144c00f4040d22904600c00d810000641c105007510710b50300003400340d1194202044a84040014441002d003081c3c1000d1403013002c00e0081c0c40c1c0d848090007082e071451501c8562880c14500100c069480b60f0714901c2c0c01040580c2d0260352035172968501c20144014203c5000d410703103800108074204c580d80c419070301900da5070410404c0c40c80d5180c2c03c003100004451 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 593507823 1250 593506573 593506583
    0x30a0c0c0b060f04020f04091a0d05061306060e101a04030206190512070210050c1215010216170c060903030a080717010603050702010c05030c0a0c02240421 69
    0x10002c82e18510b4141004000150014409850048400c1e800642504964000c010194940c52084080010005080300303821042e02c00710949075458071403580d00c00e4007400400d46d031140ea82c402824400780d9000503002d0250010f4042d094103103001110448450b5110b821404a80721824503c1c24140000f21011290010070540c00c0600040c1e203440c140314518101d0003480700400c4003d4544594501c46440b60220760003034801d1007110b06d0b9400c1aa00002e104010441c810031a15160711241c01403e60048000f8541c01d01c1d02c0c954600503444c02d00d0030170b01c0303512940100c0c0380010a1004514011a181044019500300000e01400c0c00954010042c4541d4142c20a000f62035249106400321648117805241c91141d802011644074040c490a030044030000b074445c001c000300300e0703024054104c40805915002d8654505881c0310b80c0140030301c2080c0010002094805000d5550700790448501180312084070000b0a4020044851607105204504590380d0b0620b0070510252143c071102d111542203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 593509073 1250 593507823 593507843
    0x50103200d0609230f0717060d061a120102070201090302190f12060506240f0f13080f070f1203020109050a03020c0a0509130b07050408030f030a0c0c 66
    0x840351265480d00070000c42000a680c031000003e110459004480000049030304441142c400e0b402c0211000b0002048441581000c101340003140742d02a00000da40f812540c1d082920b038540b0800100680210741d40941000e04202c06000000c0f0f0031b0f8010340000c8401c6801071714031802c0300000d41c20303401101c074040d01048050784c0070400350400940848024201d1050040020b403100000c6c40d8905554200914041076500b03460208441c52240e5500b0210072a41d000000d252450550784a0b000b4540d00c240302034000c02d9404581c0b124405072010100c14605d03498071090603500c0155a40d829110368260341c42185240414810041251010b6071001401d4403080c0341480314450005e851307003504030215961080220003183c4103010415100c0d10a5000c1c0110b181c1c114200140c0384900e81190b44210011018003002062289424841d25803080c0015990781d0381c1343d803e50360b0340107692100901d8000055440385041c0701c00001c40c8290342e014000c00c2803050003042101c0c81e007046100200b0048a03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 593510323 1250 593509073 593509121
    0x706140414150409020711091005040209060d110a0201051e0a11210105040b010201020f070605040309030f05030301080114040f0308040516080c030c010c0f171b0610050103 76
    0x404811074110740060440708030600000e401030075903401688100403041e40424082c0c10071684e0b030f80400c4050000c860150311030524110000003042c09124080c800c0e5400282c2c0100341d00d80606580e168050b150f01040507002038103078088a50312212500005500c0d14002481100c10600200d0072034081c0e01c2a9000b603565400004010310034461222080701c010b0015440303003405400000481d8101d524607034420351404c420311042c0ca40e40042903040d64010301c1440802c1481d6000c0c1c4000300c1e0040000314494841e4102a07810705030503000138042c424916407010522100000a6041b01d0380c5900070010b00d40c00200d5118109070544004000c0030b401425080464800c2c444a81c11902603000d4030105050410380041c020042c0c0d210b000e040e001012040c9903880c007031001501c410400e081070807600705c803a130714210300c0552510020000e01c0303c1a040720400074403000b9039008011010f1603040411000ca08240e9a00088805600d22043c80001143c81c2d442801505403034800840c4403540900 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 593511573 1250 593510323 593510339
    0xf06041a1306050112020f030d02101808030c1c05070801030210020f0118060b0904080913060513060314070e0c090d23060a1a060903190b0907061404 66
    0x400646141c200442040721030012855600c50580205903d0002114a00451040c0302010217008400e6109422608060891030380214045054810020300081c0c0c0440000c00700c1703003200c07450002425904001c01001055400c007c02025141000f001800c0b0303030304403071822009503602142e8010001d440240100014100303942d010241e05524019103419054084d40c40303007100c5240380100c9440c0465890300040c00341d684141d4850b0300c01035407207440b035180941760b44003a44504a001c2c0d00039081d1280365900c080481d4810b001414000f045030170b005e940b040e40840504100d0000b6a12201c0310706c0e0602e00700a002070340e80200e07003031145141c8160703440c64540300d4150800c84a44e50804686120745002070396081507502c0540d03082c1e444420034203442110902c2c0a01c003e01411079185403218145003078000c0c5070444890002143d6040c0d03903c8181c0d02190801850380c040c62840c5051049003c208407e004049200b10806011500c840317039542d500b107034641024001c610710048200700901c0559 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 593512823 1250 593511573 593511623
    0x211502090d06020f0706050f06182215090312111207030e0a0c03080301060f0807050708130302040f09060c03090305071e05030a0801061421190207140f0604 69
    0x2c021411131402e000340c5803038050035180100c5030b071040129100704005d454a4000c10030007491f545c0425091180c90040039030f444010307040c0751000d46402810816810070040300100908130108039010300a9520a240c003038408003584040e110014100145d8000f5103030403e065030911441d21128201540310200164000d240c0b000c1e40c84120300620440d00701047c0d140603280c000b107105081c41c0b0396030744c500a8014400414a005c80d81089056001c1c8454958400c4c261a045030304200300c03d0762a1218410fa0140185680c0001d41243c1030542c0012901d105501030b55034240102414801464080011000c07100c4a0307034010045032080c1701610200f8510fa4070080d5103445002d1f101038044644e11100e103590400200d440026860b400144461940020b8004d0207048000d9510b007000c800d60103660900e0a503964068900301d07200c2c0003485040f030300e000019200213165000c66032030925040c0900221f11501c8080154070038003c0642c0c40840010300e242c403854010200c1c200024000d1000030101c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 593514073 1250 593512823 593512837
    0x6051509011b39170a060507030b130c030b03060720031b03070606050603100e0a06030210030209011b0b07050309150f1f06081807211502090d0602 65
    0xc0a40f035602e050300d9483c5030444084482104400b006250000904036603192069007100f808075040018620110034000f90f01c0850340d9000c0400700b11550742c03240840080410300c241c941c2c426142c00408001e000e0950005000e990340c0c1e0b07000e0040011000902d5901d0b8026691400041e807030f07200600b04140032124038041703454020140c030724005607400c3c0e1b070b2125801c40300b00704100d410004521b01000031f24032541000304401c0d140303682140b4203c003c1420462180c41466041414200043d9003252140e0000d4040c1d94010211804540f4100e0001d00a40000d0442408101c410500110007070187d44655070071035202c483c4683c95541d1751001c403200d81001e0501e0f1814403842001c183e404540b600b50b14410004882164003c3c500281e446004090120380c4200c854140e4509021b10390740103258680c402521810500d8819550300c07420700e0310426038001d1090508a000284020f240c3d05640700e59580a50b00c81140c0c40c803004958070807482280d08413603000748908017010000b001d58016000c0f07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 593515323 1250 593514073 593514083
    0x423130c0302060a0917150612150a050106030c0201020309070501142517030906010e060102030c0a11030c0111030301051e03011d1626070308040906051509011b 71
    0xd055895021500b590000c01020000c588400420304c5102e07503003101c1510a09582c00100002000c180e01c12080c080c020300030301d00034000070f030f00c020603174030104441e444001880402121900d0078824110003000c1c20301800b400a424501c0820080c2e00c14001e40e8080c602180181071102d29000042d20301c40310207020304070b04c00da013400000c0f0420520003115504080b00101c01a0380b42a038900b0221100042c418146841400e001b8030020900c00140d1906403121403842d0f8445848030300c0142c0c0346001e8040004401d2080010560410007101c0a00e960f2040550480784210340b0200152602c4000d800c1d518a194018001040f9918001d80c0f5105249002508240403450f0080400d003590307080090125680d062448246401408104a01c02c0f040740c01d4203001c0f85418107a00424040001700c04610351f105034040d03012803040074800b4800960713010404640d01c554404420f0080c0003d072150394452000c0b8140c11600d80311280c11030314540c505075101d41c1080c1c144403800c120b03480e4000041e52 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 593516573 1250 593515323 593515343
    0x807021f1a09071d06280203190207081612060f060b160c14030a020108061309030206090d030207230a06020a0314060a141c06061202042313 62
    0x441d200c552030750340120350f00c0c0d44104400d0360554031001100d50440800740111003c0011400f112118200d10720300040240ca4a03a0700190000203e240d400ba403801d500300c11426880c201e000c2e0f60006207010031204900142c2d80c848640062a40c0b00030403600c0f88a5403124003402140010340103600209080c5140540068061f490b1481c80001340c002c00c800c0410b400c0040c40a00601c42e000d0b8408005080c031010720500303154290042620f4031150f9800906018a8034040340030b5030b65002c25502003100024080204040310708000355140001d94007186140551246001c00910074004c454940c0e40200f0450070742001c24a2428080401412255040c010910540b000965078002014000304603900414111940341003400d030040040d00301c034460144003070300308803481c29000f60b050f1500e01241c040004120308009410040814900205050715000d40405c03640302c0981c0f1461601d00070745040200403c90302a550143d85207882c0001c8100d5001d0001e01486403030b034203500c00148034001c80d44c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 593517823 1250 593516573 593516621
    0x51020031903050906060f04110f1602090112050a030c020f04060b0903010b0a150507081308030703030516080415060803120a0b0a0f1e240807021f 65
    0x1400c54000511003200e1021441c201c0c84696410301480f40c0011816010b044c040c1040310000d500c0d16604040c884c01603071140c1c0c5100f80c00700c42d1402e83d00c0c50b04049a4140c0e50300150381d4440c1240d6565117040348140001c4001090202000e9200100d03558408010800004181c41c1034842000006080764008000550b108440d1254010200145a0300e08610744a8000300100360940301d42d02c2c5113500840c0c80030f41c1040703010007204a401380b0103440c1c10010786e541d107070742000e100d68840c651000c14100e003070300000610024000000d21801e07010395800c00c101d1710750114100450381d0b04030400002a4142000c140803503d410115141d070350b4a6140011a0f03030f40d880509046070003101000c031841c450041007281160340c2d402282080c0704200c0380c0c81030080c10100c03d000c0c901001e01840804861429110860f024500b40e290050800703620003440c81269a030206940c400078044040005440c400400c000d24000184000c890191440c1e000003240d4010320b030001480000c0004c1c160b509c0d409008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 593519073 1250 593517823 593517887
    0x50414060405060a0e01091a19180312090608091506040e07080703120302040b1602060d05091e03032403070504090b1807051e0301090c0f0e09010203010510 69
    0x384110300280e21903445a80110300050a810600c1d4010041004072052317144100007000304a482c0070902d46800040e03084540821515140e81e5a400e03240c0d41d200440100602c800c003440030b209802683d4400d00c0541d1150812624408255440211b41d0310042c0861300707580000030318950244c4050320005007200c0c800c040c503140c04415031080c10315412840e02441406140e020340c1d0100c25050030f081d840d261030800003d9040c4a0350b000060410440d2031901d00310350307485003100c0400c01d4006040c01142001d81450381c442a510003200161004010010302c0c0d0000807043c0e91160300050308407044102d40e6205101290140704400303515000f0882c002c150b80d501c80c41003150300b0b4003414038485540381a549900851030700b068102141c3c0e111050420055640542402c0380348904000c1030004039401e07000c02c0c00f500c542140103144815401010170b036000c0742c0c076038041142c200c030750402410b8490601d110b080780300c20302031a80c001892450500d0641d0103a9003007919407080030b501208410000e601 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 593520323 1250 593519073 593519077
    0x10e150a020114070e0108040f0b040605090d090b09130f0603030c020315012405210a140f0a150306050c03240306040b0907083a05041406040506 64
    0x60481045004594000216424820f1400d51540b540702848181031409002d40b41c0c40141d20030038100304840c00007800304008801c6202c2c6990380030f045100d032400c0c680740c075001a02d0102e4500c8450b109105090780600d200c1c03441e000849200383c2e0405d14100c91a01403101400c900e41102506a49608000444051900c5100021070090762071b05071140c0e0610425003000802c2c007026a10500301c0d401030000800c41c85000205143c2440c04601d0180000001c0d01d45004154038440c078464406101c2c4900444d0f402c0b83d030320401c0212810000d8140c0404d4944240c4410740741e01071240c14160016054054a5124411090041000301d0301c0070f075240c1d1010180e5070211180a00c140c8040184501d41000c0007032090605000403610318056200b401080c2c0d1014010700141c24406030b82c0c0800c0c0c0d039100a00003c00613183c02c0302070740e64008642e031010031000c40700485c0082c140c42c1c4030b80c00d410640c0903c020b400e030b41c0500c0d40d98a20701440d0a900602d00b0001c1308600b68001c404000014486e528040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 593521573 1250 593520323 593520349
    0x12150a2d0c02010b0111060106121d01091e0506061c08180a0e0c0a0c0303020c0a11030d0509010c031d18040b09010b100302161a011a0f0406030209010e 67
    0x90100303810140e098000c3c256000c0d4050799040c026002c01d4004613010100b1032a065580c1481c2403003481c0850307007504000c0c01c0c80c0d5010804010b03020180340354110040d04a01c0d05140550092000d03170041c0516604c030f4810301040603010313800040201d10289004c0005c0c031071101c030514800d402c240183c6c48200c2c1c20703400b046102d6a40320040090881c0b600b85162010b000785016000c0d076000340b40c00342d401c1205110394400b100030401c2c0450201c08050207503041d500d20300300d10320483d41036904074a41001c024800f0600c8034404d01c220654440194855800c6442c0c0c0786040c2d4851408011a650648120724042c0c802100b450340c070445000700c0e44503110410080c00014000014604281c182514160b10143c661802070341810b1704080e030f98a903080110212010352030300580d124103003041002d02c50100e407001800c54444200c2a2201c0741c120340c89a05a64500c000c6c0d5088604404180c040c81c481c10b94014803002c810b000030030016000b58007820110340103040120200d80850002840416050 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 593522823 1250 593521573 593521661
    0x406020303090715050906030a15080d031a01170406090b0f071707051b0307021203070309060905010801090f0f0e0d020d1403040605060d1403070212150a 68
    0x2004001c02c03000100700c00c00003031551010003a54254103000c0205a0322415003d40c0c043c00c000004243d80c1e8000754005624264010008400241c84550080d100e00201c2410740000742400b021142145075040e45010481e8143c44041c0c0142088480d00c100102c01003040c1d031095603403c10a80071071983d611b214840c440b154001d15080c80d0140d000f8002c0042c150b00840c40e81240c03001c01c580150481c084810303075109040726521300e00c0113202003482c61141c401e00a40018440500c0f5481d0308000006d8801d96110341c0f81d00040c00d45690044602c1d210314400e207400907202a0040050002a9014081604042801159400819000300146c54482c052b001f06d0b07a0020a0109020340e0500c440c102c6518217141200340d20891034000c440f24000500041e145e00d03591001b0990960f102004d1040700c960098584650032220704816403170781c1143e402a409900449501c50051801040d81c52440e040f5052080103922007440c0c810040c4000c800f0742c003110304002c445220300c915801e48440040d03592 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 593524073 1250 593522823 593522827
    0x509010b03010603180f03020c2e0509131406211506130c020c010306061d0621010b04050a271508030403080c15090a0602070c090f140117030a0e1504060203 69
    0x100d030601c5001c04a004070940d041024a05035528041c0300c80840141000354a4440d4a540300540058a1a40941c04801000d480c040038600714104ec0501144107032000c88044600c020700d0003402d060344500c07104123889900420703850b02440381c0c4003002036006003010f04038100c180714450382d5008860210080b00c0150b40320210843c0d880d80c1c0b5000b0312029120a20380500088074030b0702d07210076007103418800c07600ca1000810721440002110840341c05009100c501d0b02030659507800780304d00603806030241a00624500348049480038905d00540b03134207000001c1d41c4002c10290b0400700001c10700114070320f018503007210300040c1d43d000400107000658000c06e44a55100c46140c031061a0103200352602000005450410650520200d0000c6c10203800c601f025a0310562450000d1013007003543c1001d0705540c6001d8480100462580c4140c0190305410008140ca91322040b2003642081c00503d6180f03168010000080c15070f01c84c489440031b58602400111900c81110210100c82d000394001c40c00503840 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 593525179 1106 593524073 593524093
    0x30c0904020411030c1308010c1706030a02060d0b0a05040e0a0b07090902190305150604050d0809090f0f1303020703031d030114070201060509010b03010603180f0302 73
    0x4442d03260344d580c0341c03510550342244c10688007001d407010f14100125514005104541090700e054030f43c0b1802c880481e07240e41c00000c008244a8040c05040b560300300607160a40a44200d11803d00c0115059900d1014003186610541c800c0f4491810100c2c070745100c140200b01c4180030342c0c10588145d025503401c2c006444014003035009071541480011451500403440c5071a0303045504a0341c00380280d03101c01c030350308502030384507003600342e2013582000708000c246800d0000484030307403180400904054008000910030a002c0350304000c4990914200003927103e0704210720f50700064240c0017401d04101038a009540c0c548500000301807010106070f42c1003800b100307501da00f2003405c001c0092294041e076080481a00109842040156007420804a00c5103082e00d4007906903502d40c003446086030f00e041001c80c050120040c5d48062003090824a50106256420201d0300500a80080a6080c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 593345323 593525179 := by
  have h0 := BRFrame.cov_init 593345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 593345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 593345323 ≤ n) (h2 : n < 593525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
