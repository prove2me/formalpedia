-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0893
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:31:49.353718+00:00
-- url     : https://prove2.me/submissions/92b24040-250e-49ab-bf24-92d9aa1f8572

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 160431654 ≤ n < 160611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 160432904 1250 160431654 160431697
    0x30e0f210d05070309060e06040302090901090b09070602070512070801180309120215031b04080a0203061608160201021215090a0902090c0d061a0703091a04030b0606 73
    0x80c0c108400e600d00304840c1c003411015165103801801920046505035503820745d450705145003a500b192031400c11a902c9076007840000010b98803410100d100310508000810302d00300c1454150003000020f00410066000b00c40c0510510b580014003034102d6030210745c5266031003170341e0008600300400307900546295401d0003845125410804190400c4903c039645401003150b480210340400d408201000758041c8018240169007400040503503000070764184270a000405002030100303c0d50240e4040c00b26504004078400c10f600e002e028599002c40340c0d1040550010020000511f4000c0007000345000304452131180309a40e100b541615145014099060303941d0800c4a054403482d50300d0242d45228aa41500154081c50311b03000e4200f480b03a0150200020340c0320816a190304c1d400401640707400b80d9072204006501954081d624441030495042550b4a140c40d0034004c04070b81440c0c00c10384410360124500040710201340115400c0b030b81c00c00c2a642d200e48070f100000c6c00034031640300c1c0d03070031700a0224480 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 160434154 1250 160432904 160432939
    0x3030403090e0a110406030b0301021201062604050304061404031b030210030c020c01030218030a0c09060b030f0c0904110a081812180402040518060102010609090f030e0f 75
    0x400c01540c440c18001c02d02030b0f40d410a0501641c028600c40c180e8034105110800c1918000d0300002d6003c20020000760408034007125401c001e1200b42d00150010300c41041034a814001e4403800181c444042104403003d1500b40c035201d45e0303407246200b88010041c600d9920b1100281540c00e480296a201a42c044004810415910683c0050006a100300d81039803d0340c3c40e280c003c0c07050000c0220180c000d0300601d190303000107600075041444505038001d0441c010680e40d503001e01c20009518400c19401100c00e05080d0003030b0881d080c5070041490348208100b40062705200a160f15413000c0240c4449990310621004100a81212101c40b03082040100d802c2d407000e50886442c611a002040e1500c903c446400c182c140d40301b8140b10f01c07a004c0401007015034080b0116071900340e0b11b558080d00140c030307040ea81c0c0b000c56205449044c00d000e0a08801c01402019a4280541001094500c0d4188024525500c8505045030744440007000c3c005813040551240d1100d00000e840140e0003000f80c650020280c03074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 160435404 1250 160434154 160434167
    0x6030c0305100f18021003020d06080102190801050102031e0702180601030e07120f0602040b0c0709050702060105210c04021306080105030a050a1707050a03050d0b040e100b0409020303030403 84
    0x1505440f0f0510483d0400499180f151003544208564003020000041e000d110340d108034040d0f00c0d820544c080261b074943e501d80d405184001c144c15400141d4401030b200441002d08103000c008410001030600400c69a80d002054541041200303a00001c0302402d0700045c1c07814410208020f401c070050303885441004805079400340c031800c0c0c21303281400032040ca00e080d2a00c4640c18040e007d486000d60601001140d018014041100e10900c2c1c0180350545501e0380c00320b95044079101c1101c40c1d020980a1003100b066014064006a403800200704075410f00c00011240e0408110390b40e009000e880189000000402c000c803655100900215030311664412560341551103409030700c003ca00910300000c0c0c903060008018803c260050007414440703071b06035a013820107000c450720012000010320201020030404d1020040442c030075102d0b01d03580c42d00150035100340c41300310000301c0c499894005410004900402c60190001503110001080d1101200040c02841c040c000650544000300c2040101900101c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 160436654 1250 160435404 160435423
    0x503011a07170711030115090207020118240e0a030215090a0e011707120b091615080105010c0c140a0314160b1303020f06090d030e10090303021f06030c0305 69
    0x13000256080041c04c20b060a07107030b0309902c07649070202c4400208040c00c85a4050304031b452051400703004803000743c4003500c103008898000410404074001c000c0c200140c0c0300b1071401300020030708240c02240707101381c0050480307081c5100c040d00424a00000c0803d000250040b43c1241e10024171705000c0f01c0d103403a04980c40040901600100124035076140d0080c0f000040c0440803074407a215884460241d43d80c690075003510161089846100307071240b90f100140201410000b511602484582c084060880101050303011381c441c1d07051009201c40f04001c030f0314a54581041d2040c207890002014050b001252503001d00b913001402000004e0b50782d070b2150002060303440300004040c6c02c0c800810344400d24400e0f01d02c03c21101403403a408241040006052848185681090081844d810030714880045910b1030142101240080c0c1800001000d41ca018100c86180391801d1400707800c0281150740107590b402181b04940da03103148036074844420388100e4100c1005990300075002d2801135940d00e8010b58400840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 160437904 1250 160436654 160436663
    0x501021b010c0513181103010602030a0315080a060e19050c09010605030f011512050f0a050108061e0c090d05030c120316030b0102010b0a14010206060901060503011a071707 76
    0x1c840009698031900c151003084c104100c0310580180340c44201240051040822401941c5414544a44800c0c1c807002e94000c0881350059070fa203840820b0001c00302c440c10405a80c1c3d00030607400600c40b000c1e0001d07007074424544c0000000381c00d03118400520b02d0f200801501001c0b04215941d041c0802a000c1500020003000b0b450f903540c41c0e40c90700800c0e40d05020864001940c03d00e080010444e41807240d042165503609814409680034014401c2d4045d81c6007110a11154091300c4184414410184100c500402540c0701428890074601a980200c20414030454003861b40080458205940c0c50100c8014020040c00c0395440542c61514980340c0d00504010100c5019468001c03110400003c1128801c108a5007001714411880f0f03001c1c3c00a141d10304286045650316001e414013503c540c040e45001c2c2901800d980c0102000d10002490514003d10a500804032500100f08403070300300003030303a041d66000c0182d21011103189102010b03500403242c001d850050000c100003c41180354004102042c0517 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 160439154 1250 160437904 160437911
    0x28140a0b0301050d03120b0303030c0903060f1b0901030605030609070f0e09030a03020a0302120408030907050301110304020d021215010509180d1b05010f0501060e0307060e010e04090501021b01 85
    0x44801805450000f40b10f140c0d0080d5440105000107071281e0040304182d5010003000440c964603202107072031070b0030403a48a0f00700000021210f845103030400040c0d6128441c1d42c00c4100d2440c250340e400c0d0154104082c138585880e00072030718699581c081d80143c809410042e08442a03440e14804880d41c440caa40b00e44085100d403004082105d00310404501e1017284214019880c040150340d08500951100c20b550041650a100d4542d014950b40500390189004007000e680301d09000300820700f003d400d944414401c0e03250004407103218096206480e40705404482031180c0d80a0390004ca4490000320740350b103d150044181903981a03000c00007582c12780740c082e6002c503d6903444000254009982c0d002180303a03a40407481c055182446001e0395142d13685a04108940e000b807a40c3d42c203007541c90600381c10a0303040d00c6100605c1a1039004809005440c000c07801041110719151010700100800034007036040040c07005491040380c4858000f024115840002155101841d0b60b24140100d041091a040c0c4d509 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 160440404 1250 160439154 160439159
    0xe010e0f030714160605070303020412050703020316031502090a030f120f0c02130f060512010f0b040207020604092703030e0c0102060c0f070c0f030f06050105041a28140a 75
    0x90029818240d180044c2e18003c44030706000c4140c03941e07000341400b141016001c10000c100d0822215900055910440092015a007180304150034104080701d601c6040311000801c00100d920103c48031840c040742000103a9501120010070401007143c1c0014001902008146080108400307905031100c4680e611034201d19031501040710352040984010b5480b43c2d0341200110455200d611020340d18510100004645944030007203441c1100e8003805509a95490010031b140c2ca442d80191003030000308031011403400815a00284203800703180a104025507480c00082445100c04410341105014468240e03861030540c60001e010700f004641c0c1480e10b000d03101d050b4005500025801e4010200262080e04000854598180300d402c4020185c44a2501c4040001c0c0021128462800741d8041c1804c041e14140c1410210203580044c0d0242d40142d107003074050000b288807070046014405046607404107131030611142c0781300c0221880150a003020310f8500010891450542c503154041d080d01e030304000740e9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 160441654 1250 160440404 160440443
    0xf090c040606050304110a05090a091b031e081608181917031c0b010f0e0a050609190605031b0304050d050f0c011401030c140109090e010e0f0307 64
    0x240240300b504081003041c0301150002c0c0c038880030329860a1000d0000716100c0d40d9100058060101903440c100c000340d40b030f1921000d2045a0b5441c4c4120121003003403402051665959900102c0400344081c0720f002c1252290080050752011501d000c0e02c0d00d01c920312206d1845c20002c8542d40082c00580304501014100f00840c00c24400a11103406400110214145818035940c0b201c5c10040a12003203000400070155a801c090500035184540c1c0c0600080040c000c1c400540b01d21807090102c400c2c00034681c610b41c416a546800314080d0f070400e4607030b16201c201c40001703d48004101c551104000348180f5010400319403180295220344840b4100390a003807961100c00d549440280c3d40501940c000d00b5000911500680c0244548200d0f4281203243c241d200c0c00070382c00c490500b203c004480121800400c140110710341044007500031090518010309003200040c00103101c0d413082c5001c0c1c0b07071116508540c0450070350000f0b51900d080300644000c0d02e11603c0a98a81d801600111904000e0f5009100f504 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 160442904 1250 160441654 160441661
    0x406090504020a0b0a0210021c050121031803060903080406060b0408070b03040206120108160e0c1e21011e05061824130602030306030a0f02040908030f090c04 70
    0x8a8000e04408400d600b0040405025807151111720b0035403050024100c540758041c401003031040e48034207000002068066600d02070b503e06a00c847d043d68480c41c100002c503152994010640c66040c2480b0100079990b9860008403080c50b4000340043e4038105c121418580c00011071881644101010030041e61504516091070266003d440d80a41c000720061283c560044015600103000071b2080b801c1c0244e855a000c84524260008002038020303a031003003c41e503d031030608800b4020480e069101071404040f410312600a1011703030444511480605403000402d80102c1c0c0541a01e82d6100112410230580751089210030f00c40c280c5244003440e02e1403e88551580ca4009271400207088900d041940441c8501e128a2030180550026030308403814048071412202c200402c022401e269160081d08505400c201c98a03031101301550020010042141d4011548180340c0342d01a500c4814030304140082030042c0141c00d00100300d020000188200040e0744c4103003d11a00300c4104a864601a60341800300f40d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 160444154 1250 160442904 160442911
    0x1509051b04060909090503070c030c03060608120d0504031815080903070b010b07030908010c08070e0901080601050d050109080309010b12030a090e092103060f030613061d0f010b04060905 82
    0x1c102640a0121140d00d4001110f8035000344c0449062a80c0c5480c1d0f004271410315417045071604003207a810810884140180710050900384040c020305501801401ca540c402d055019210594031000034080500a28008041100500c0c10301c0038107444041c40032150300c80201130000316500d074000425185001089070078041d441260701441c1d92911442c02055040540101c05100d4040000318005500f4410745609005a07a60000241030501c40070784018205103d450040f1034207801481184400035000c0e0440b2400e8860001b40d4095041140c0107012044c001401c0400020910030302080541000141e034a04031824000c68050b42c420990f83d1103942d46180208030803440803c00042d01c090180e501201d6101a18500741c80d40c80040c10300991074528030036001e4007000303101040c1004040c092515500350300524072418410010600c80121b0f02006240a0b100c0c00711034850f407648200c44c1d002c0d180142c01c4078030708141d03c00f40070b0203030140011083c0503500c2e00701c1c0080c00b9005801500d01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 160445404 1250 160444154 160444157
    0xb010e060f0406030b0607080c0a11040207050a020f0112021209060f0108070905070905040203040f060f0c021005130c06020609010f0515010c0302031e030402100806010f030f1509051b0406 83
    0x3400f45018415000791034a111803075440502030021f0f80125000c44018074946004102070059910b091900c924481e892540b07440c020b510521036880002c1000801c02c100b140c0403944400544244001216440000c04200c2640d50002c0384810f4600307010320f22039020718008016280760380d58001c4103030708035042481500b00d540d00c030400811070304505520080d007164452030a103890380d491710013145c00c0e40e10954044414822a180c10402e01040d84107600550a44100a12061048120007556003100200b0003440e80d58540c080b441000d00f0034018048030341d028023041c100c0356440380081d488a10407101c440042d400c2000540010b001841094803446100750302550004142e0011562102c2c40c4408034158801009079544c2e604449103035000d480d903074041d10b641e00d180c03500c1803103001308031120300c88184188402840850383e082190120070444924000405001050940001e0445070701380c10b0780040001e401040c408402c0c0c000c9481403003884c50301e4400803550f0403a640b40e03222740e1048070b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 160446654 1250 160445404 160445407
    0x718060510020d050d150b0703120501091107080d060e0403110f010501060c15140108011d0604111309020907050304061503030e0d0c0e07020307120302030c0d09060e010f0b010e060f 80
    0x114502c2e10740d000034200034100007003104090b200c914050747c0c5d40c00b100c0c0c190003144031203081100405c45402624003412054405002d02c0490f50060302050045582c000e00b0010041240c4024640319880300004144212800e2032a04060030044d002c2100c10140c40340900480000d40b50301001402498120f4041703031b9034160311404603116290441e8060007402c05441c1c40740e500c00c500c200d1490816000c0d08485000041d502e50b1402d856080c49502210a8201d40081c0c08010100352019100c881519003034540c80701750016019071800508180400075070140300312052025241c0e0140245224600c03518003003058000c9046c240d030b2002c5a17444028000f4485803041142c5060401c1c0e074030b600324841c040c884d6055032540c42d81010080f04494801c016800400d01009004114000191004190034110b01e54185080503d4191003a1541c40701c0300381d10340300c0340d804020256020303113206c9105e040200014440307068600e0113403088ca03a806000801d0503451012030710f0a00101c4100c403419000f411f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 160447904 1250 160446654 160446667
    0x402010f09030510020f090406060f0207050307030c14150a050306270406020d0612080a020106060f0527031504060b01020c090414010b09010801050109180f0308090718060510020d05 80
    0x402c0a94441b180050b101c1c4000d02440480780c1310b5004540103440161291403440070440c03c020304d0088554084d41c841d83c00000c0400104007403403c40002e680694001c0c11900240703c02241340c0c0254042c107200441030000d40c01c640c0c260b21201440c040c520403039240d009126141001401c605003050690780b00c0080d24042400105c85500038407071560030300d901064003030b034600c15421a001c0710781c0c0c1511007a800081048a131582071151102403c2207003880e450300460302d50014081d00610f00081260350201200b50500c5804001c0102e007180c0060844545101c0c840301600303c250150341c120303203503410009003035019030000c511090b87d00c6010b8146601a035403506e50100003556a2a40040c555032480c5aa01d00e460762058903001c3c01800b4004070349540360405060881d21400144100b015502a906000801c1e94800542060b0107260a00c842c0e1107003d40780741401b1080d03128811440503d2100740a02c0e4068201004580d07040711505854211070001f43d03180c3d0b40c594400000101c0c00c2042c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 160449154 1250 160447904 160447933
    0x50703020f030a15080106090515061911210a17090a0b150d0b0405060906010e0106050d1409070501030b060906030103150204030210111b060d11210402010f090305 72
    0x700c1d10100c050304c9070f51122030360b8000301c0b4211444d503005100c5103910341080258000c1c043c40012580b100079a0708515211841b00e0310020442c1d44912401000004210207504000402082c07000000e5400110780004c0d03113410005442d8011140400414041c00c2500403004000c4091407154071504060700c0034503440c0c2d030b8411a0000c000d002050b290843c040c041c0d180d45440120041440c0308034411540e41c00c0c40c0c00d00b1880c040d80101002056800500141301c03200e001407540741140e0a81c240a03031113440043c03111001e8640210000d01030341d655020880c1d1007100080d03840403140e013038a040122159840c1030082a10440e085030b40c000100f00010000900c030b4418018540c012018014113080d02da50020b081a11420406400920443c944940c00401070009082c41c14031100c5800d0580d00840c0802c02c80e000305001d007184c0c42d0340d4050800c4480d510804441598940491048800c41d604450180c1c00c1030961702680095036000940c00520701418103d82926003082c01480040982e00d003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 160450404 1250 160449154 160449161
    0x10201060605220f141309020a0303030b0d021930020114040f0b031e040308160207050d08031608010f03080a030b0603040b0a0b270702070e010f09050703020f030a 72
    0xa001410b840c1d0f40380001400e0302000c078500003810b140706407058248800f40800001c0d0303102c04404040b19207406c00035001650340c58840d000312a4142004509846800001402d0903e81c50020f9040b00e0300503c1c8000710b9244041c00f50540c0c182c1e0920070891081100d610042d0f0040c1c2e074a860402803400c1c0c144000d5805030f041c0c1c0c0e06071100b48800794945515610140c404c0552503002c03031003018000c81480420b04140810440409900750201c001e4900303928010101e0a0140c01451078450072001240b6061090002c0c001a140c0a84400c910350080c2c40c00180c00c2c0d1045941c55428401d00c0f00240b0464800c0c4031070b074102d480382c41c1042150350031a00d41101c0b503808000e8a00c10300d0303035442042c4219110100650f12490142c3c41012036440c0c2034040000391102113828074031510a4412303e408941e01000a007001407403c0c44040501e58030380105a1402016070040d400120000000040b504510640342050b80c0c01400280800e84403100187d081e401341310038080d078001050000411410302ca90 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 160451654 1250 160450404 160450447
    0x21c0e010806090603071a09030c010804020f0120120909101214010212040302100b041806020313050a0b09071a12060f040c0504030302060f060904021302090402030703050411010201060605 83
    0x1000e407040b903071340d9030541008050710b041442c02004000c2023074643d40ca03051000780c48200742800c00030094030345540001d40111078006c0c010b040c0124001d02c0a0401201014004080051011079042030800708204205401004565202d034240303400140c44006807040d8107084135001840c035854940d0380e070707a50b001d60300b120520b5018665080c8480101d00c9052112a400703180650094141554507480748415103010300800c0e0700072424000001c404009002e100244c05400c13240060303c9448100b502440b800e08800080d1030303482420268010721000d540c0050140f421a82101c0b4050340c0c820440c2c0c072010402c048407607260018010b054180c2246002c00364406002040000343d0351250002904403102c0180000c0025000704d030a00130942c04104080d0400c1e01040b004030700345040c40004403540c50042009008400c03a011411940d180307601542e4090340010015902c80c903129000500404040300c00b03607060043c103041d0080e130b540188207c406a07040703950b0795803070140b41c540440381201906 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 160452904 1250 160451654 160451659
    0xf0307030b060d031b0f1a01050310020a02030f040902220b030a020d0e060705180d02030a0f08070b090313060e030a03030b01020f0a05030a081e0703091110021c0e0108060906 77
    0x189480410a6617903640c4a02d100d00b818200325040c9017007291140c22842d08130407101800f02d005000c66540041c540203d044185409039031801c284d14102d0460140011645c510030012401141422042e0040d00d8030000103003002d043c6107000d103804410651781e4803554128600810116400b049a50010708034560020720100759a46820303032603071070800c6c211456800201c02066440e00305051384102d003604881115030100c40c1074142c0010740c0b1244240b0000340013030b880c019064100031184081d950401d4001c03400e40007030f00d0982101030700d0f42d000e07034812040704030b0f810400301d002c0340181032000d00f0903000f6004080d020b8942da0300760000d04080541c035055100d60030200c0b82120702003000d50f0400d84a00040d680b80da5081c0d202900449010300617075500c0000300c0b200000d00f01503d1202d40e000e8494600442d25820b2414000c2d0040e00e0b14600e02e0700074900000c9011056000030702d03001107244c1d03600c2c00c1481c82103950b800c840c41c469411090303001034200381c08200c0030718041c0b081c1e58010070700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 160454154 1250 160452904 160452917
    0x2a071104150302060318010c02011a13140406060807050114090904020102030d020a0c11120604120c12050309070b030c0405060d0f0504030f081f1e08030c03090f0307030b060d03 78
    0x101c3c1c00048454100701c500062100c4120304a240c0074100f801081c50880e854002070210012000e0001b03807002e012004107004861641c00c2c030085c000e10380c02400401070045440f011500f41810110050800c80c05140114442c00b900080c00f5441034041c010320f01242c90040c1e00b01201602080751828018105904501c814007160044d80f00c0d42c8002c1c003010503182c03030b5808500c0c0c03145002d000e16001902c1c003d100e00902c60354400c00c2040450318070b42c001e51040d040c07608040140c03410344048422030740c00b61584038224508100c06030400c0042d8041c60461086071401a0381c3d03400000513120880340b80c02c0c400c105000c100440d06040b005400340f900c40c03441c0440d50031540042c20302100c00894054000401108014004d603421002c150380000f0000505010034046240c5c4081c0418144103940341c08042c1461a042c00e400802d20402501001d0b01b9242d4078450440d14998940000c16680c1c0f054240070440b100910340050310308100c991040920703085540381002c011844280d43d405400b403110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 160455404 1250 160454154 160454159
    0x70c05090138040603020904140106030e0f011b110a0c0b0703031a01020d12021c0902010801060c020d0f020d020307060302030702070807051005030601090306020d0204090e0d0c110303070501052a07110415 90
    0x24001049c03800781c2055030700011504620080035150804440d020b400c643d1510060f54103440305150449400e54035030524030308610b40390008a2812494000241081e200d404000c2004500c1c00002c200c464040c7d54107200501c5042c40240e01700d41510319180c0507912003600034540c01e0040607460314a4030240c50040c1840806a4048074003034503d00e00c0c0c82a543e46640c000119070700215042d024045600d000e56810300340f94089542e091407107002078807100d006541c000840d6240b001014070300390b007d416141d4a40e910000900079400a81c1d20354054007a400022500c40c6002900c00203d503002030039400c1440c031800041d1482c0d4000f5100e2410003441312000300200d4801c0c0010000321040c0303600160303102d00c0d04007a51b084410403281140c50b0341120b8600307100075600c03040c038548260308004001d141c1c0716014006455441043c000600c00d501b80000c110300060240f1409003889801c6121155410301402480c84510854034020a810381c3c8081c50340782402c0c44d6100c000e00e0301c00510504106074 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 160456654 1250 160455404 160455431
    0x70c17130f050301110a050d1d0f1b03210a0c02120a030f0825030e070815010603020c10050c0417030310140a0605070c05090138040603020904 63
    0xaa6034100c203000719056442080142000d00c110007182d00800d080c542041044840100f0302d2089088155040303485e0712a2510b001b4014000c0810540030404550544454403003560b00c507415002902000501d01c040d1481d103080c08601c8285401e8a19030008000c80e124440070b00e02c5d00048582c008001c580705455005841b08614401c4502e120001050030103a5441c00801b480d80348800142000004410300c40424500341c08490701d215905828005100d03144000c0707004024224510455100d0070310001102c07500030902d002c192502c00400300513aa202c83c01036045c1d104111302482c90354802c20056a2001c082c0e0700140d00060b0b1450321518041e50392076442c0d408820740c04110919040001800850482c080c0e20f5401000303405103410b03a10005c08009942d05259100c4d8106010001501c4000c00402d44500e81c06003000501c00300c40341d6150002c0320001034602d0400b40894a8201a0f111210300054083c00da01c0011030701e1904d003609082d001c4019400001096401c9600ca050041510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 160457904 1250 160456654 160456687
    0x90c080a0510051003080901080402040b0406121709010207172a1c0506010501030209060c0703050303161107031202011e200702030c010810030b150f0108070c17 71
    0x203028000034075020214102c1a42200d1024003164044a00c00608000054140b01910121082402c0c01c00450752680046405840c0400b002c0798043d181c031502248200b401940d160380c0324040d000c3c00c3c5841485045c0b091a500c600545980582e008600402481d001e145030300d02c680b0685c0041e42c03150300c0340e07032061001e81003a401d64004a1f045002ca686180c01c1000c0c8002603040080410602339410352152078541c2410b000e02e904154001a02d250181c90b0308044030811540e403011586920764a040040d2260801d40d0000c0d25818414189011503100762840081c031a030030409015040d1a6544094026403074074400c0d403e654a582c44480126051640580440e841140c0803c0e4040320065800450008114080d408003042c03000b01c0140e00c00141e051a0510282000841600c0c0c58071401c242e0902d0b07520040c0080d00100030403400008144038a4034003907054174440303c031080c410010740c0c601004660402c00101081030000c041030204c114f2640d0590484401072a0a000040c0c20002 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 160459154 1250 160457904 160457923
    0x30519030204061e08040602030c090616020301180803010b030711010c0e0901080714060304020612040609030806060a020c0d1110020601030b0a110403061515120506030601060f03090c08 82
    0x400c1e40820308105680c1c02040012041d86107407400b1581c02c540703600c003070102000a08050401c42c2d0200004120b5140c0314111111600010000707501c460010342300402510000034101c1c06075081a021040c510411641d01102560000300b060941e07080c2400c03e26245c1008120808102c814600400852000c0c85400c116901c2681c07582081101d8800740412640182d001e40c01e142d010328000c000c88805400d01090320401100d40725680e4a40d8000130b001e80c0603034000c06461a0841043c40100301d055440480b07032034800c2e1a01d001c19604c200c100542809044010030143e040041c04440c3e91519004c0d5054061040c5d080f104440d01c2d100104440a042410480259011400500a001000740380552161001100703204108801d6000306c1c032409148001806140c5903040014407409204000300070704068444034019110741c001c010b007a0b0a15440c81c603c1c0c40e1030203010460300c0c10301080c41c5041c2ca00684400e40380c0b5000712720441c000e1280c2c9100341c8214241d003001003401242070040d07002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 160460404 1250 160459154 160459157
    0x30c120d030c0f021506060405060310060207080120070309081e0f010b01020c0607081c0c0f090b0f1b060a0504051006080c0d051c050c0c0301021201030f030519 71
    0x915040c58000a01160100c0310b00d64144500804420f01040d400910042c0c0b034100704011000325254880450110301803608200d60001c404002c001d41c261503018504120740b6240d00b201d00302c40e81c0768101401c982900600203e02802c18901c140c03985110130080540d50310070f00d01400b655a46480042c00c0c0304d85a84200e0410a440a020501c19410840503003d1202d110003041241100c40010350b9903040c10020a025440225001003840400400d5464104c082c1200c042d065a0f510440c900400307420300308102140103541c281c0c503103d1042e400b42e01510035a111103850301d0038001155110790043c5680141c08010040c61f410031820901c0042e0040219400102e41da0a2030710b0038504000ca0b01c9880c0141500d00703001007002c44000904400812003c0e0790b00901540c0c00d0420604050015000c0341d07401a5035481302d1322807a4072a006080c01e10403101911100e0003c50201404d03445411055280d4072012001030001c03035502c492044016100303090a910f803203608507499100b450009480340 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 160461654 1250 160460404 160460413
    0x1060303110d05040f0608091903020a02090a14070e0301020409020f03040606120506060603060d05250f0806010b09030a05060103060906110a050d09141002040906120c0311030c12 79
    0x4030210410850702e402c40703030725081c45802c0034142031004a100b0210712501c4d0403c030400010442001050064424820000743c50701100b82c05818041e58401812030300703e005828820000b80c1266580c49003c1808401440b01c1c140e503205d54008882101950000c15419507007008001076402c014401044518240e200080d228030342801c196048a481e42d10083e0103a5111074040000b80c3c0c0030684961000707085907030395103e803a480c0114048040381000240b1390300c2854403160048103007040105440c0d002180204485888014000b070b16007140c070420700d15034030800042c480a6180d4003e00360b03031a80542112040d0303121781c5901c2e26141d420391060b0f41c4213949068050500540c2c1c015888040032241c003c51130a42a290000c1007032180310b0506040c1075a9003009410009072182070f450184901045400e00e0000e107002c0ca00a42c09841041d000a240810006106003068400d03012580c00484107220b091642e141c0d0540c05284443e099458041c0b503103850f2290359140070030756050401c48000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 160462904 1250 160461654 160461677
    0xe1c080906070504080307120c0c120501050a060602150406090b010e0403140703080609090c04020d15140a051905100c0b06010903110d05010b04090501140c04030c030605150301060303 81
    0x541405000381c01202000b801304001d1111080020485040c04c2d400110358455003010b200449d2078551607000108200455000000e41c02076090f51185168000d40080180b51108001d550842e5414803890015805c8840d403000550075440b04507600c90700403800420113118945e103049120310243c0140c00b990001c40180006d141d0300031420591119145201840c15809032805440c40000418040c400c0340c9200009210740303402e00c0007102c01e0303c01500a5444030f4003401c40e10060700092002c56030f03070fa151034400603134a8020000e05542c0c08000d0000c29603242010305100c2d560600064034407003420986c1c000511911584110750341400503540e4925848454034002901a0020b0075507070401100a030248040348082d454913414510444000c1d0304480720745040c601500303038000031035403003440e0400001c240441034004007150440703a282500c00f41e650300002c078480e018a0102034a901240030081c000070303490307600c15034014840505c03901d900a50b10340020700351251508124001422141078 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 160464154 1250 160462904 160462921
    0x3040c150f02030f0c0115030b0601030e070e16091a0901030c020c091f050405100e060108040b060603060a03080304051609020403020d020d030311040e150105030412030e1c08 77
    0x2881049441e1508420800c52a80c00035500c0c05068440080c1c1000020b5050500f4002d600040c001d0b0b07000300c520b200640e83c90510924036030088039010701090500f202c035070b0070850128403041610f6800e203207402c840e02c94500e2041000c01501c1c4003018008150300210b043c1200b04c122030f2903079000e14850f580d100e24800005050704c0f0994000010f40d0f00080000751a80d80d014060f99219001880000742410000d01c180c0e07500140f54031940d0841d26000070720801c880ac61000401b95410340710466200c1d15148011150500103c801400580f0080c1c04141c2c01d107812402550800401031004d40306a41b80d442d41c40560b8802c1d00e044410b948030b034500ca40c40801da0700c00400140700b2002c0840c2010300e16000310f440541180c100a21841d0391780c1c101d008141c0030341d00080089443d000303260341302d60311000410000c0800f80c1d0304601103c44c900402e070043d8422802c40344529800382940818000360942a000f0f8aa0361203512014003c030b50f00d1594610300e100110543d270b9076940e250b04440c03e0051a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 160465404 1250 160464154 160464179
    0x90411030111070b040209040501021e03010801060b12010b0306030c1e040c110705091905100806150112021605010507020304140306070507080a03110739092003040c 73
    0x3102e0358108820711000010a40e00701c0c206602c16010340c0e9020781a076451804074024170484101400d000c0789111810030034020380000c0d50503201c082e0000c11034551281d880c07807058002c0003c481c0342030074000014441c0145c001e02440d0440c0002d0102c42555982000103900e0001000310901c1802040a03440070900c0d05001b0190700010314140b0141c0c2c5060f00340d0f283d4840241d409800d028505050204820524020820850714001d903c10001402d001003c0490f40250b0b02c50b425a80c850b071404035010301e001c00305800072040d05841d41e401030040700c0421406500007810700e10320743d11604102300c0820400e020749846075034143d0146503124100215840c900d000844c8860003030380054200021190080125620207411240c202d450715801c400480142401d100342c02d002960100701d10003000303185140211203000f00518286404031142c114000001a03001304010300090040400504038254030055072207070841400009154a10744840f20796009580171250441501c80800c500c00c00c0c541d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 160466654 1250 160465404 160465421
    0x901120b160f030c1209051e1b10051608091201060b0d1d0327010806030a03050c010f090b01030308010509040503040621090b013605060f0904110301 66
    0x800540701c0401c0da00c001040038240300b0b0315030241aa682400c10125029080c6000f562002000c02d0140c94070030b14010752518403107100074014035030701c512902d02c1c2031020035140f00060346041868007e03100784d810003094004480c510f0307082c072004104d00d00c0000403900d02c030510035009524083e42e420556060010001e480c440300141d507494500d0900a0075040c40403119051440c42003c5500c400b00b2200c100780501e03070407950903a840005285002001c00480e204400c0b0301541858801800304401582c0d07100048500c031340d064110340610340020f80214003819603a51250000a162401c108400e03086990b281c00650300180d00d40010410943e01040f900c1c054241030301c01881d42c3c18156905507072800356009000500108001070302c501c02d181ca8600e1032407440c0032806e1009100710309000d0800042030040c103140440c8100590540c5500c1ca500380c0b10780b0103026019046800070762545004000c040c181c02c0d4071041120a810307507035562007031087c0154090603103998084000c50401d400c481000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 160467904 1250 160466654 160466671
    0x15060605030c030423060702070e04080a0f090807230d0305031308091c1101020d0f030e0a020301020c0d03180f06020304050f2a12030307050d020403020901120b 71
    0x14109105059125090342d4000841c50092a01c0e40c569243c6107220142c4e06156030408520004484a610800503c0a02034140fa4081c1d40000d034403a800248070040440e40034102040800030140748920409214080c1070181c80d0a000e1243c55104003400c0c29110360115481e0910f1400641c04030f800322000501e5840b01712022910f00e00b080e03801405601000b084c3d40c81000f031851445d024014400200d0b41c200310010000c1a0315458030000c1800c00f10240000d442c480c2158500c00d2a9500010f40008407008030780720896042d0401030100c000e08080c0c21031120034020f0410340801178034240050640c4460b90720181c400080d89840040442d00e042040c1030b1440300740c811a40c041480312a078011600d40262016a59a40c3c0f400c1561408107816010075a0b072241c01012000302c000b008914006c103a441070402c0d0200b4400c82000b444008281440d004d9800400100d008140103100405a08038046009420140c3d29000110051002d0340b01210f43c8200d81c41e44000c0040300300740c4642c44142c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 160469154 1250 160467904 160467911
    0xd0501080c032d1509060604060509060607020a0317040602060a0c050a080c070b0c04050f030303041119090608010606080703090b010612060902070c15080f040201080c2515 76
    0x1000003c0e590100b40044111030300b1110381c1a0003911150308400c25548a0b0012969504503021800145480448000303603540118008203120b4a0b040c060013003213602c0100704500076103e036020030650358080e4000705d03030044140134000b0010361464150b02503001c0010003540c8483c0b030814003a040c9180148042140340c41c02c594840d006812600b5141030300100d1405003603e0f551520000258402d0301e101411500b83c100800114810b808001c00503a202510324500ea994900c0074196a404145c0b0010131102d62403541c5002418141110403c1d101641e824500395a52015080704443d05a00400b419945960082c02044d40000b400c03501704116181c10054840c0a4403103003008401801500e0401c612401d030400628038503000440501003078a0119601e42e2913103401c903412100b6104c0d60b14010405520141c94034000c000e007500c03c19140e81002e0351947c42c1da00440d003040000348105d00400051044801412051200e05900780b85070b000c1e909aa1010b0130f1070944030b100c11901a160505 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 160470404 1250 160469154 160469173
    0x510050a03120f05040503031612020703150b0a12060603020405060603040b070e010e030706031b080c03071b080d050411040c1b112205010905010501090b0a02070801110d050108 78
    0x1c1000b0311941030700945069080c0011051040b5058495540910b500d4030020078110700820b00a41740340c100d54850b042c84100441e124800341d840e10403600c0041c0003030b200d10a144217410b04503000103004140040400c1c002c03130741701c01002c004e10100407015240941c0d1a102441103040a100d0303550026400c0301c44ea400c41c9050303910200100c81c010500010071070030300da4015541c0d01564185540c118018203550b4969200c2000800501c04603194408a8494041002d1028002c841983c09030104a1313125286a07988803050740c070780c028100340b010101102e6103a400070800349005170001c2d04401002203242c1c201814400c0e0480500300341742e413255140840203950b481d0040440001c1201c10f100e50b42c09880d1508048554000320020f5a80040e80d80d4503061511090009941c42560040400c04c4242d889003074003c00c85000740101d030b010a01c00c150900c0b0001441024003c03440c490b00c101d030811034464402600303403216203884081100700840d5446c2121080e02400e800341507079030020a081d62 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 160471654 1250 160470404 160470413
    0x70501020106150e010201060e0739020d05070f0f080d0806030721050d08101208030a0207060207050a03050910030203090616110102120412030c0c02120102120a0510050a03 76
    0x1403034a4201010700c1308144110016034002c0d003001c00100071020f03002e04140f0340490302802001820f18800d000d201502e010319214494110750200d6014503508428008a0a44c280440c034142d2400c207403040d1240010000d00c107154106014007401c1240c0c80c14041500d004502882c1050760000101070103d50002c00410b07441c0001c1c11011254160194545880120501c41000d001c00d41c1c007070040d020303038040c2c5600d541e00845040d0041021003884c0e0a0076541c0d40c140300a000d03a41f04001e080c9401040401d4000301150090010240034060040c034040c210340e5014a807141d1008114041100811f092002e40340c0402400a8000309081c1945940791080142e501c5400052805000c40f0b040c04240709402d20942100d4050000ca03c001c40d0f44854680030440140c10444040b0340500c40e1102480d0300742d20070700501001084030389450010076080d43c200500030380040020321056600303021404003010b410a8803401401803400020310340c01c040e4007801038200d0542109001c0d0380600f10410028 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 160472904 1250 160471654 160471679
    0x6090c0c08030c040b030406020a09051804030f1e11070b09060318120a08090c01030c0e010c02060903010603060617010504050304170a0b090d1d03030a1b1e05070501020106 76
    0x107a44451000c2d6240d884007801031150061760001168030002000300000c00c40c0641c000c000c0d1010584031028100da072101082400c1c20300d60b207100c845140727081c04640001d0103241411200c0a56090003072100c8002c0c101c444140c001d00d044c0744005403038034034000c19042062149901030b00e8403242d1036203085890b801082c00c610020740b0704001012602e0f0f00600b0603105000b42d407510100c001e00c0b9685c40b824814020884034081e5140301c1180140c100d0542c107036019103e500a8040d894880003403031035141e0015190101d00d00d1059070845020080d0080c41e0f036082c840d00c00510700c100400a03209041c04800003048500b014410501d130300d400184000b003400041520300f101e4036500340c0c18011120301541800c18024034001040c03002d07450700f40040c00c0c0020407c21260790459841020000f40c2f01301e024800c080c0e107200190903400030003910320f0b42441291091500551650b00d00400d15459507210601e0302400000c02d1891260103070343d820044144101c00051000348024400c0710304200381c0c0702c1700 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 160474154 1250 160472904 160472927
    0x2030703050f0f04081c02011404120e04050115140405060910090315060302030f151f0b0a0f140910080402192601050f060405040309091104060306090c 67
    0x140070010403000003060024044907091003030010819101e6039555211035030380612418101100c036070504c0d89100b02d441440b8500001106005401c0e071030310307240c0320700030b001c00c2c0c40251404101404090481c2e036156401500d000f4070610a6645c41e0b0302c116103005000714042c1d011403181c0301042008000c0c030744d24a0b058030b9456208545842c00d0801c40001a10140500d6000801c40880380c00c2000440005030310001c1100e00a400391411140050303a0603880b07078610030400340c5054601c80480c404241100c201c00030b145000810944e411b07124642a10709800014400700010101c00d18003c0003503000d000c0d0303084501e4900c906400c1020b20070000742c0610b0350036480300802c0002c500040c02d40d41c44076050481c00d411009480802522501e0071410b031041d00211045100504205c9504000d05118951049400306080801602c5030f10401010b032130301410940c20020190070204101c200380c480c0d070695010010a01d50341c2d500c0c20b24090705507952948080c40840c40c00c50400100c0740c21800c98444c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 160475404 1250 160474154 160474157
    0x604020c0309091609121533060801090b030718020f0408061b0406050901181806091802060301030b070306050306010e04020a0e060d1104061206050402030f01020a021207061d03030a0b0402040602030703 89
    0x108042359100409841d04038440d598801c860a200501044400400420540d1080c0d07485803016a25240c151041d00c00c110304130782c1c040d0301882c0d0410054444d660b01d00a180320b18180989089500315411400c0d801c00d4201e202c1d650000c030f050207510404411001d07001d1020340c000a0406d40b921a004d08103025400d486410700169103015100040184003810181c408400d45403071075080301c183c0d440100036a01400149a16001d0181c201426441c014001241d004102d0b500d1a0b0955850360740802000e0302c0e45060684803900071641c0d070303400d0040c54042c0000c4c1c0100d07000f502d000d0040124224465200c0310154140301d041c04a80d4540c12440c103140c03500000c4108120740301034081002001c0c0c5502c208a4417074100c02e25010030402d0340006020398000c800b00c0700c1548400350000d00b01d101d05c2c40c5100140e030060b4030311303250300a402c1c01030000ea9015000004104e0520a800a03485210560100e50780e00b000041211a00701d80c403420360500e50907141181080d0504902a56074400c1042c080c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 160476654 1250 160475404 160475411
    0x3911040c080c04090507020c0603040317060f030309040902040b09090607030506010f090608040f060f09061506090e18030d050906090f0d140c07091b080601080604020c03090916091215 81
    0x200c910340200000c544031234020307040c01d9903403802d07040040440c40c000740345001c06654080800c1c1c0514085c040c00f1020300d00100030710300c0c2c0001481040010001d0140403130b001034851a0080700303980e848240501c02d43c50075001d403c042c030704008000e007200c4000b0b0500307042c032400d020803001c0290310240c001c05481280c10610307510303116800d00d80f1031480511070040000341031440c0d614112102e6008031407020f20414060201181d2840b03242c130888000e004400001355444410403549291a90958100010341e18152061140c0c081d000c0c25a030080038040c54541d1540d00317100c100101081004d5002140c140174002c024049032616466208840030b41d010081440004004804402e0031110161040012210b4041d070750040341c0003810907100300c190f00c0c407500407008498a000300f2405114580584d107051003941c807407041000a42200001c00c402e17100c01c4c01005d040f500d400300c105014840540c51201114aa05c900800200c0140c121584003490100328070001101914840c88040841e100030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 160477904 1250 160476654 160476661
    0xd0302030c0601030c260309090c0d0504060b0a08010b03060703020a090503012a050406090306091401020319050a0e030f1e0a031401060504063911040c080c040905 72
    0x40385140610310707488059000706400082005280c440800494000c2c000301c0314080102d1062001d40030581c1262041c6400070001400d032480c05540e6103600030f6098440350b00740b80115400c078084070001c5404881c081c0d9074040200f41c07440c10001200082c103502000380840d019110200391500c001806030f105064001c80c40b098000c3c010b2030110003401003e80200324106c21100360446c00215075020b059229031061114041911480841e0290385260704d420050038550741c1c901d001840c0c055002d503604040f0900c02d004c612002e000450055240d000101c0340301560040040440340301421252040c0e103420304030b40b101c3c100132041d00d2039501b0410926403101ea0b414a21030301d40c0c9200f8220080104005400300410b50550301c03000c01d40e0b80c1d0003007403c400c0e80c031010245d51610880c05030801282e00c1d95a0b203402ca6400481940d5403075010709138500c030b070080880c810341c0018058101b03c0d0001c0c9288043d04040c2072610038180c0740c1d603480ca4581c0003800c080301c1601061060340a800066034440c0d002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 160479154 1250 160477904 160477907
    0x20c0c132304021e01091802040b03070c051b130e0106080f030c0105010e04080706020c07090507030609180809060c010b03100e0606010804082b0207030c050d08150d03 74
    0x11180041140e03807680200406080142a9811201240716400304403d52524a0b5010b0392107a0014040c1c445921072800d0014449a00083d01a429869902000301061145d805405103000d020681c0391f841401ca1649482e900f020418440000d903104c8440011949a95002000c2266001200001210039881c00024094191500521040e2082e03081141400000200520350010610020006030340c9610000b1011402a64040c0109506000c20008034807a507008012881d01c40702202d03c0d003590b03111428241c0c0c00c00c451072000710380e44110800640000b800703007214000840712100c90010940c1da1700c1c40d06008079000903008a0010408024406003540300c108450310040031607074081e001280802c00f07003c3c420440e940a0081201042d130650203a0030f02c0b8088c03542304000b5800c1c2058404420f4042030084c0540307507984880c04584a60000c00e100901065009543c0c540840e056818094900400d4840103020490a8000c0260b05a81c40c1000700301c07400111002d00000455040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 160480404 1250 160479154 160479161
    0x60a0c09050303040608100b030601050703030c0c02041401050112110a030b01110115030606170c10020a0c03050a050105010e0106210b040216021201020f0d0b0303070c0f060e04020c0c13 82
    0x1c140c25200000380070815540001500d44105d45000d401040c140d10744c05c3c00c90f02c500041e02c4180c081401403000d8000a0f010340c104803208041440d0003200c0d42c80c150009000d0b80d10680c0c3d14070000b92018010b008550b030010400c4038003407000c881801250104205600a8455525100101641c0d0305054400303a10854940c184008110020b001d0058215400d10b800702072444100d031041d2030644000307007000041c004070b041511484003424a045010043c00442c01c80d41e5114001c5010304c40e40d0800082010000d840614000c00007070121041d0f524210b0700315001a004007002c5d41c0503500400c01030b94001030000c1c1080c4481c94446a20b181e40110101801d0140e582c641d2144c0085802003a1500344980390104500846061560080640030302e0b00300d100e1210300515540c401c00c900b000c8841580c120540e41800a42140c0ca03241c0d480e1580018032031540c110501152004070f0800c44540d00207040c03001c0c0c20080380c0440c6481c0c14200c1c0903580d51741115046010300042c00b245680c1c2115a403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 160481654 1250 160480404 160480409
    0xa0807020f032706132c09191103030a1107090e1c031401120c050f0f0d050703050d020d0306141315090c0c030206010902030103021005031b0409090221060a0c09 71
    0xc00d034500c803900c9008030400501c400c14109402a105030682d960801e401030194001c0b10380401401401d6201048d144e14a140d81c00c0985036451032040342d144a84041004010040d083d549100a4107126160242883c000c1e6014510b50783c2420b20303400e0204808110103245540010004000e41c11101c41600503244007c170a030b40598040e4000907540313002201c030750300403031046180d00013082d10340301000401e0303140c01c0090750410074181a0343d00d00d091002e1424035403805403003100c0c00b02c0d584e96585480c10841c00c03c0000180c200001c034615a6415009010281c2591084079400460303100201f500c50010050140a25843c2d494181c1c00c0000d0b520410b000c0d020b020b03818031880741d00c003101815001c5101412001442040000034618040784246d1303058aa0080051040103040720080351950009840030604800303200160300c0312500383c0010320080001e840c0104130040349004211482c0c01c080400403071030a1003c040c00014001042460b8020501000001c0c144107040048810b51100e4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 160482904 1250 160481654 160481677
    0x5160f090f030c06021005160507020a0b0f040e09070803070605060d0f081b06010807050909160311040c05030702340311030f0f0c1012020a0807020f032706 69
    0x100011062041d0000d007041a95805d0702190011400c200c444030440e60308403403010418420010072000c451160700107082150004003041c0081da21860218a542d100b001020503901000404108ca58408842035500c61442c801800600f49080b0440d5100c2c4111a0f0040c01103654800041c45552500d000506e82e9401001701128500d43e458009095844501d00c591040e8005d080e03081504400103003141a902d014020b040c900d4034240034458108000340050003903004481203c603da02201c0c040400560160990b034944103109414001142c0202d0b0400c0f00b000010400c204115800081c030101390280200208003c07081c8481c0091034408032030200000503903001c0000107101d4142003204491400310240d6000c3c0280341c3c0c46030380e80d03046c424040416400118a0720454600940c000211040743d04043c4400161901001d01700d1340090311801c0842c0802043c4150180d040004082e2a40e903400254070380400b000c080e850312145203012580b100c4203001900c00507211036045c0c0c1d81c1c44099 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 160484154 1250 160482904 160482929
    0x607080a1107060e210d0231050405060607030e0f010e0409030e0a060207060c060507050912031e03100308090d020603041a0a0621230102180405160f09 67
    0x142c580a401380c242c8040d1450140b050041035564031071071900c01425a09000d010b64038100c02003103844041d4210103110084a5685065140c032030492403400701c0a022102c1c555503a41d4109001c0004950f0302500880c0211428404503000a8000b8128a100002191620009540d5000480c0e40c000d4202e02c9507001030415809a08142c5c0141c0004403a6a040b5104a60542c03101d10890b81c8110707600c01e10300003841200c81080441c1c400c3d070000c1e030001400c1c078080381f608041901240b4540383c801c842002d964800192481808a4841c9100f100c00384a4005895401d0042650301e203584030340409068103800041c00c680641d54000040f507200c0d070180000391a0b142c00e003072541f003020300001c0c800032501080c4001400401c05108107420f0314601174040d9020074049100303c0b91055000c604940070316810b42c4100c88002c0070031107040004a01c800242ea50000c400d4000d051070200c40c2e515028504001c20320000640703000d80200c00516502d001030b002c411030304044070107100c907601500c203000a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 160485404 1250 160484154 160484167
    0x1202150a0c050601170a0803071803030503041a31060603050309010912050d0c05030904060b09040b03030c0a0f030c061e14060a05011101060819051e0607080a11 71
    0x400c11224031440d80140e05841c40c603070740c5500f403151096031802c0d00d0030642c105906d0a000030302080040c40e0440082c0c6031403c0380d080d181c818100c0c0c111464000740c0108070003004001c10040c5041c161044617968030300004807800e080e949410180d201ca42a60240200380c040360500c0c1141551400c00b03980c0141003031000c0c6a480c10f0154596201110340d6000402c846404a00f8040d012514210b072075014004000804198000b01d60241400c48115010702082102207040d5499015000181a030080060742d030f040d00804100c1101e8180c10040c1c000d07041448000c8802c0703804a44440d080b5001018040b039000540340c22a210780d08040002d0002d40340040c2d03103d010124070741395091424070200400c02c03030700020b107070f40c40c4800101c803141d902500841d4140200d500c6500f60002880340d034400410307403a484400c01d0341010b0000210884000351000303884140b010130004800c13a03644020800070030315540071b000c03500c2d198000c0c001e0090041d2540403d6405010b82d1100300e24102d881022516204c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 160486654 1250 160485404 160485407
    0x305031503190c0e01030308040807030e10080604150e0c090402040b0c0303060316050609010f030e0d08060913050d051617120c0a020a03030509070f060f02010e010203070503011202150a 82
    0x3402c451056512140075200450088240a1261305a94150711404c4c9595610f5440000507440310390f0032002c104194480700007548031502d07014104122505c40341401c0c900032007888201d0391100004c440d0240030403400c010602c1e1400f8016000010b1140c0551b440007100c000c14040c0c402d5078000003580b50000389107100898080007035405060114160b80c481484c12607070950302101405400e41c0150704012000c8030350b0140c202110940014203012429a40d010803585c02c2013404d544800200c0d00c0c9004000051400403081640b241141080d00c0c600c07240c60301c4941e07072051014182024054009121202000d83c2140641a0390303205d0103855100c054049400340c103411042c5268081c07010000802d681c03604420603100d8005007580141030469650328102c0251402801c1005540135107000171440040e8119084058641d5440e04840000000c200a08480760301a988007582d00c188244010194420f0032281110a40c6100e08841d02c00e4ac000111070358180102c0c0043c141c0d0008000e82c01d00e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 160487904 1250 160486654 160486693
    0x30c0a1b02030f0d02070603020415030203060103270b010515040e04080403020306011d070c02100509060702030307060e060703020304031d01180618080601030b07081b0c03090901050f0901030305031503 89
    0x71302c50f95007510030742590750400f03a043e03005901441c4180c0300201d4600d82e540303100ba0f024540c004014034000c04c0045c5031001c10005d03000341c0c14039041410b200c41304083c140210500d04900400090340d80c030b040400c0000d01040319011f03c2c0a4022074800100115003401b03034413016a0040c503001410358180307513903c2c40c1d8030004412440c14004500c041000090a1a00031140f55052a0300174002a0401c1c0640804039030991110108603032101c0240217440258034104060321000d072150340d0000f040e1040141d050310f000c0000341007a00f014010400c010011b40e0081c940c40c41c80d40e240e155a600c03c644040144c079a00544606001200c421040001b0195480b600b00e252034010a001456469182d0a800d600c4050901000c1d00446005000c140d58034480e45031036078072039560300c003400014181007518480c980c07110300c400c110740d03001141d582054500a001140140012174507030181c080720f100814446401488050b05101012001920011030000c01101410300101039a80103c01500405081d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 160489154 1250 160487904 160487923
    0x60e0703140d110303060a0b03090109060f050a052a0711090a1d011112040f05070b0a03060e13060e01020412150c030c021b01120f0e010f02030c0a1b02030f 69
    0x1c144070307041403c00001004036406103101410443c016420501642c04541c0003034001a500d650390700204022920310320412031043c0401c000498641441e603039070350950b20b020b00914580c1c00e00b0110101d6203444180030a00314000e600142d521002503040111600d0100c0502e41d401181c120100302c0303044210b03031101c600102c0252820140981703000805080314501106441084010007a07503507000788101c00140e11030711910052608044c44d541e103070304119880d800855410b2020582c0802d03107406000d400c014004460340301c9260300c3e0207204060074070b01d9900054040c07541c411800d0b40094081d0110381c090500b41c601c3d02c2e8107000900d080d000804000000d03c18039490400113040b814401d008801007500158020020341107002c214451008013101203d05202410300101c1e4114154010042c05000a400002c3c458000990550a5414a2400043c0c031403040040018a080c0003041d40c00c2e40701c0f24074143e044c011101143e01000c411810000e585485400000e9501000024001c8c50 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 160490404 1250 160489154 160489157
    0x411010314071b050703020a0303080f06190b0a0c0b090708060c03040506011e0f0b030702010e0d09140307030804080c0109080f06060409051510150912060e0703140d 73
    0x1411a000789100300120103071400000103140c49104410a40055524160700307002c0d400361340c00c0d01e41c1d903030000c0d0024405600813804180c004081080c813226200c682da07880345003600c080e6030503000e130300308003019143c01d008140908138041000344032a0300c101c404940306a4042914102c0d03060031403031640e4444ac5449050500e2048100007004c000203902500d01480e403010040c01d999003020180c414101aa41603504a1070302c1900000d1103aa00c102c5a01c000d000d500c0c0100c0c1c0d6814003e50090944480080d06641b0b54001d444c11804541c2c002c0308a81254210090b1850303203204013001a0828600780d0014081c12000305020690001c0440c0c0041340b0f80e026200c2241003076950b5001621140306c080c1c1c50405410000000700203050540011800d248960300352810210180fa00000c011801d8034a10000580004140300c6c0342000807001c0e280c2d56150600010301c07880c200410062200d0102e004020984502000100c4402009080c000d545d22076810354141c0d10059200d5500c80c9035090100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 160491654 1250 160490404 160490411
    0x207030c06050a0521162a1502070c05010e090f07120e0a05030a031d0604030c03030212090a03110c090a0c0203040e01090218040905030a03090c1706150102070501020d0e130504110103 81
    0xc40e07034043e182c401d02030894014030f662038031086684000401f142c548256502038000000c3c0c15008000d1000b001518031440c0c00005080c1060001000045c00c0300080c0d0003919100148844070b48a900070b0b65000496150160080d45d401058001401136049103542d81e00c1941002410044c010001e0581181d96903010460300c0200000c0d43d8580304144140f0105411210210f00071901c200c4008072070b94041d050245c030381211030311440f03900c1c002120400d109030030502c04a010181d11070590b50a001c4850010054281d021000039141f8401803d8a403e1503958404d0340c038003500a00503907004140b40829800b596a44240f2440030754480d0395001c04082d044604552249400d1055580341d41d0018015400c1c40f201e0702e0198010408030b1403c1e900700d05480c00000e41814100d04490062a0000c042c0089080490002000d458180c5050381550400b40050220341d03070001d00110b401c0d51510300105046090307800710781c07808026400e0029150415080100b4420301001051010600ba82c041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 160492904 1250 160491654 160491691
    0x90c0809160e04030c060207080d020309060a05100b07020315070f09090c08060f040f0c210c020309060706110304030c0201020d020a1e08040503010f0902100207030c06050a0521 78
    0x30012035180303018098801182e2404200400c0c0b01d40e0038400b42c1340c4100702c0140b400c1166103c5c0203243c0c000960501206030000b00308503c510050000230307007148102034148068248080030318081c4002d8000c00200da031022408400b0356038100405080501701d40540b41e2603042c554002806c0e26140104840440c1030b0442c001403c0b041840380719046c01c03250740d0320002900c0c0c010810050850440040e580b0903221420341c3c056030113a01c2146030a1110352039040080f00303d268418506c4103000d402030070480c5048079031508560080201c0380e00d05401c4070065640ca2503403a02c08028290040346986000b008030800007010380105902502a0003602140d411565142c0201c0c3d031210390410081144500c1d80241c0130028200003504d6141d0303c246101c90500c0e1b1120086800c440100d070b0407070500c544804820040d13081049c0b0700e0034600c03038510162035050f040d51195452805c0300e1213244208140000c18103401e41c0300d0300a5400c60f007007000c0500f9070000340d14480045500300741e409a400c90b00c400b001c03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 160494154 1250 160492904 160492933
    0xf0e2e050f061005131403010e150a0b0303030103020d030c1407030305030a0524040e0307061811010f020303040b060f091602010c05070f0b06010c0c08030c06010509240a090c0809 79
    0x7510148600308503c3c840c5c59080000d18825030384003400e101d41543d240c0303c0410712940d05000f8081e031401d000c072103082035140c24001101624043c0c42150b000350002c00052000d600ea00322105403058040c10030b44810020391a1080d8103501c40303500290180241030021042661110080d40100c802220502454440180c004107008440e01c40c2d038550714140d250311000c2d044c19000400a19044000d40f410300c40540c03188000c0d200c4d030b43c011501c1c401280366400b04100e000b4100080c5a1030a20300724150070781e40580696603110242024061003803207000180199107250407111400b00103810791015080c280c0340043e20000a12490003d542828000490548140203440040c2e400c4000d03165010300e191148515600094212810064221410030215240e455090001c0c201203001b10ba560082c6104507007803510680109100380c4a01d01442140c04600e110202c0e19481c070440c10b00b9990710f4100140100c01c3e154040030040341070540d00c0d0501c0da000464580b141c00d00809503000b800034100c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 160495404 1250 160494154 160494157
    0x601140708043f0c090e030409110a0801061101180308060f01081603090602091504081b0a03060213150909180515100302060d0e010f0e2e050f061005 66
    0x148240b103040503400b1100e40361014083c0c0314086003c0d84c0c1d00b1031900e40b600c6502c01550b102288500c2c6a500010703003080700c10040c0c49a0042d041061480d942071034030b0018000d00d51070b0b0600c500c500b00810041c030407110050031360004000d5102c0c0d4202c50b28200c05880e0180900c01d00300c0b0301920480e141c6034484000c0d4059020103225400c018800c0d01082041003080c5c3c02400005020740301254240003903a0151070300181c0707864885895a0707a544440c03805c0c100d1072610718001c042d040f030802c1c04148001d5548403a210a01540d501020150301c900d208058070803102d0040c2e0095420000300301d1000071940e0803410800940c0c6681c6d005010341d88807514400010f07132002c070004102e540310b1a40d506501c0b061140c42e5030007005000322041c080e55290000f0b80b940e04480710410495958042e07480105000744110707013042212401c00e1001c0001204e0094803088480440c402c0c0350040340c2c050410560084002d50860034403401003001c2c0c1030150020360011421583d803801085100304a6200d18000c2c0c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 160496654 1250 160495404 160495469
    0x2321220302030a05070f050a0b09120c120c151f1d06061303050f0105160c030903060f0204090203090d020705030f0c010c03111507020c060f030f060114070804 70
    0x400442c94404070940803507181d44601700688001890342c000c1400600705100c4000824001d041405041c284056002d082c1034810320b840301c0d01d2104000c000c600000200f010010084050000c030348a43d0084402030920200303040200c12800d40703400700454011803680101d001d13071031071003034202c1643c580450074010704186a0611102404100003040ca1604000803d80480c000c1c51505403680c3d00e84c4c2d40380c030b0700c801c031000d00d2450b9442d0802c00403810781c4501c10440111039403070320208010003514043c1c900c900900001e80103680703848a400c51500150101c5006000e542001c56591400031606c0e91603498807040c650050107860f00003d40c0d1300d00002d5003021401c0e224040c0643d0b00d560340040d2807144451108034140060300310701c2c6114040c1031100049a1201c08802400703842c0c64075009007040000d5200d184550010f111082004040c0029690702405410740c0f11096129a801640c0400c40c0c0c80e03c800340790f080000d0907c01c09c007142d4003900450f08402102c1c0c5000c020004002c0400740d01c0f8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 160497904 1250 160496654 160496657
    0x309030203120406060e0a09030305070806010807030504050c0604170c1008011404061a070b1b070b10030c0609090f1e020304021f111c23212203 64
    0x18052032503600080e81c0000d4110b071107884c00007100d513036503001c00302c0ca00b1085485010166440c2c000c7c4d0300349a0180103c981c88411450004803034035000e00007910840010702000205640c038000541088802c00000394101d000500322a250b580c2d0700340054064842c200d01c800c00d0b004000390007072a81420b140000e1203503e16110f80c081a8203042080c0c00c15507810140d180d0ec182c541d04000303113494030100d256081e18821000140d0b90511401c005e54a21005408021042c905041da96849030f00182a03483d9540e01101503a02e03500c542d1122100510140c00150070074504550006100e500700003d182290301c1c04074144104030701c0000c0352044405410100030b11070303904041c012008103075a00666000388010605030613440500000140005610030040c042510200d01011207076081260314103000102c900503841d5024101d0050220a125016454000c4130005120306500d40f02d0030781d07040d956030008080080540800c00c1d03070140c00944441c800d00c0a000703880440141955041c502d0550903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 160499154 1250 160497904 160497907
    0xe0309090402010c03050906031036090c030803100608090601120201030b01022410080c0f010c05120a020d030f020a02060c030703240e06060309070501051b0303070804120309030203 80
    0x107680040d60380301510a41141040410458440305030f480c8405180205640c00040a100341449419105400000d05640ca0081d44204a5a104003a960810b940c403080041c0400c01e0b0280385030518103403280c2d400040c0811400700402401c0183c10b22a0001c0341c000381d841c290642c54100f0f401d43c5900003030081200c1c6a00304030300c21000d03500a802031200090184100c4402c1d4040f02d50340c41155034100c400c415680d504e41e01307200f44d174290411b400d4050103003003024001ca2032400c00000c011007a815143c5060014a0382c140c0c0502105100c425861000345180603662105030704002d450b0b03040f00d01c2c0100482d2034070194116122030b074420b0340c00ca0b80b6650010030883e03c82078000f00c40740e000140007404260b2948410181c001c1ca1454400b04802107415a001c03450a010b00c2415a90009020301e0050f0403e2040040014000411100721602800d00c2c945e650541c103202c905c8812031206080701c0344000001d0206a540c00700c8024440c6000c0c900d01000840340c250104c0c02e40d1260200a0f005030300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 160500404 1250 160499154 160499161
    0x602060601050f040e070e0109320604030503120402040507080103032705030a4d0f09090f06060306010b040e0a0204050904080a0e220f0f060b0c010e030909 69
    0x21002480f036881407400e6141050740c0d034000e4041000d002c880001c00101529540745282d41c2041a440c058807802551606810b040141c1d02080c7d50b408070717003402c0340c41070001c0c0d1a800d440e01011507024607004800c3c0c3c2d036940e2002820000522056030100d0040b8604400a03400c00d01c101c0c10726069135456035881e1034032110b040703002c040c030a03650488889445150100203095582005409015031086092510080bc0b88185207040d0402c1d840c00304541c5090a01c009803080501204500004511540c0001540c40c0000c1451909804c1d11150000c1c03a010600080d10360000d1800a900d845c641181c107260b80c1c500a168843d43d0070b104403181c030103040c0f100b885118082846980d103c00c5007080141000d42e01d000245440070b00380d8080c0e8002500080f500c0c1c16951101d04401b5207081650200440201c0805050001451070b0200e1202c65451a1a9040f016250815a039003074140b0800d108043c0c881901c0800391b401880e031303c071041d0301e0704d00102d1940d2004800c0c0c03100d5103401400001c0c03568 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 160501654 1250 160500404 160500407
    0x609031e07050c0a0f06110309030a260f040509160905100216030308010602100c0512190f0c020c04050f1303090e0c040303030e06061003021804060305060601020c0a0602060601 78
    0x20080700003120903002e02c0d031a01d0310039115040c0700001003603e00e41460110f032030110060014910000c010015400070042c0803d9501c0009180800c660b104591818198804140c60a00b0b9400302017400c5040300060b590b0394043e0b518025009880c0c0481c0c0624094a4180300540c202400c400703c0740128194031010030440c0342c01c00c03100c60514194010744680140c00b90621344d98150503001100811070250061021607030410031000d41e00590350003003100751680070f0f0103819801a080c1c0801c8500c0c0d1034000418424901b100f480a08242d8002070103000007000b401c00250005400f042c00600c20701a104500d45440c0c040c950151a6210540311107488bc0c2800a10540d4808800c0d07007803085e11040000c058411301c0e55103124100d41c52645441e80e0451030020251754280c0b00500b003a5102c0000c0c4002e81d51103000091206004d03090042e52401d4240c00a401601c5c0307107035000c0e0310a00e021000000e0080202c1c9442c4240302c02d89c29101462014001c01c1a0a03a00740a031400507444400040d9055 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 160502904 1250 160501654 160501657
    0x18021807030603050a0c060311071a1b0c01050a0b0a0302061903110a1106010e09030a0f030b032409030412030509031005090c030609030901140d02070803040c080609031e 75
    0x114076001c15442e407079881e5903141000d5054203d94034008507034104811545803003862103140070515003a2034007005883d509112404240101c00f0300b1140710128a030300c24000214004003500346040c0d40c42d4001409c0c1a030007000201c403000f070b8280c24065000d00034034040c0000001d807076000b0409804c0044114140423401070108901080c1a6507401d040810350100740545a4554550707030b84204400030000140c28248183d00902400044c0c009007c03071640088180c030000e074840d00d04142d02140c2d6440803000780c1003000c0020b4040c094081c103440d00201c100e81421223a000c180056106840381c12041d0741d2441a4414071b80c001502c0c441d00f0002901c1400244010400203017165102241c0c00c00c024101e0710141c602281640c8181e0405965080900c0043c0c0d0101208e8003030b41c200300c41440041d21002c421404070050b0040052002c0c0020526070544002c02e0300000c00e40d86a150516043c42d50b000c02d400303444440e1207171900281c0c85410010032994049404001420244660700e1603000d50f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 160504154 1250 160502904 160502911
    0x61302070f0605090a140114280509010608060112030827010c0309060507030903090515040305120a090f0b0703120902030f16080c0319170c010f180218 67
    0x51007584101e1501080c010b0003401d01800e40d4002900400c07030585880c2c2c4400d1017541004c401641030441581c031025441101030350003180500100034003224511503444941d48118580206480c000601c000d10005601a200340e40d003e100701c0b0926621041c640b003801016102c01000200e00350002170700b030b00410200e0004045621291400c0c0038258a003a402d4600c011030b04400255034108000a1100a00401d0b4104440c0d043c00c022031000c1c1d880060581c4828040e85000d001d91241c0c14580c0c00713840342110002d603004016034134610350020321009039500c03002d18500021802c600115011000d04884005c03515424600d6103011269a425192094022001c0b6895a07481e4111005a10b09000311541c40085401074507820700c2e0405103100d0720364a504164190743c003078007580040c0d85001440c13400700c580c4440e0318240b600d51031070050840b03614081d0070140e10201245010211805400840030014810000d2200201c403078261000b29100c0c0c103029522110003114103045602c3d88500303940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 160505404 1250 160504154 160504163
    0xa08090109150305100902030402030c01032003100e0906010627080f010507080c1606020d020c0703080703020114070f0e060405041a0f0409030503150307050a080a12020606130207 79
    0x200c855980d144411200b0441c403180c1d0100703888200700914242c20290240250070a04170450450500d500400d540f0000000d040b4180340d50350f49040c4941c54130550310241e25454030030071907030f900c2d040521507100703411441440d155880110104202400200b01e541c1a01c0ca00d82d651390401d80007803002044101190f01c40e072081800e902c0c003c18500c40a0042c81d154002400011032541006007004000c541d008014103a00103003030124582c41501c03010030351070142c0c100328050f07207459a03035007564024410014081c00c68800d50038000b08000702c803400340c8030301030084e0001c11140104007500d123a50081100e41c4400501041c00380d00d055400782840c60646d21000e041c142c10715880710301080131134281d20241c501002c0e40c4501081e4603e4012800a20954203850501510740703541c3d0013811600000d40030b5200c025502003131030a140c500f080250020b1800030490f02100c1d90b0307480c04c40d48400d02c8040584141d0f40b01e46074480440d00001d00c0702d014500141610960b0495248001c00a411041f401c84 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 160506654 1250 160505404 160505417
    0x140a05040807021201050907050f36040b0106030c020d080711150108030403060609060f170f07270c0509040903020c060a03140106091a030c07020d050304140609030a080901 76
    0xf40e01c80524403092050002d0000a1908042811516110503640302c184a4444e040c050b20f920384404004500e100c2001c2c031402c681c90328108203641410310fa031140d0311a0342080f030100410700842503d440d040b20741e1a10100082d258056041782c64442c900710205c0440c0580c00440c0c03030980305603200c600b2001e1250503206000071a0600110307806003a80b05980e503920200d001d0050140d1803142400801400d00f0030001341d032901c140002165403a01c070740d480d180032a50000000c02c030180701c044800c04911040c1c5280350b443d0548201002c2d00000c244030b03880500f1642038108c0c0d00c0c5e071148009440c900d8846031308040006003008050100c4081c11008c6004040800d5441e4443c04d01034002501d084d2000704100b2003c514403155088168003034070410484032402c009407448c44043c2824070a401012680d41c0d1b45104541d88944a07441b0300942100c546d080c4082444004030103002600d450780110000b003600f42c401c10203103000e411a2640d264002044140001d2000c40c0100702000046c103101 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 160507904 1250 160506654 160506667
    0x50607020d0209040b071b0c05010309020a1a070b09010c09210f051e070f03030c080403050a0c0503010515010219050c090a020a030f06031a0702070b0f18010201140a050408 76
    0x2e0f0a4480c1610110780340901d400c1404042d41d0811030001500460300181190000d5a0721101c0140360075102d4079040c1551045d0360720944d00c2d285031134405003101c225010b8900c09080529400f0341c0c800da0043d82c443c0b1a41020990012041c018512100540c3d900d1074001ca003040c41040c103200c03034004a05000700d0103840c5940012105c1c00e12800403406440500302d86007154454000c3c80c68020000b040542003050180714000c441038140741074079014501000384601e54a0b00308024801e94101400070300c650000202044040d00202003a2007040e0001d02c46502e44150148400e941c2648050258101800c135400d010510b03c8010001401001183d0752914024003050704108191188220710f44c0010f60701260f030390940640314030070091123410400d41e0b1540e06c2d5441502c54003926000c0544080380032840251003001110080d11500c030300c0c1542c3d8a48036407007c4d2164414a00074801c000c07c0c1140030750960041c42040749286400c580c2c82d03241c1d44d611800100410700108101c500718000d01c101c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 160509154 1250 160507904 160507909
    0x150b07111c110f0307050102060408030402150d0b030708010e0712020301090c0611010b010c0c0303050307090b0d20040509040f052406120a170a0509030f0307031b0507050607020d02 80
    0x42005290240820b901c2c40d072950070501540c031071824401400380d40901801c202a90b80020280d602c150403c140c41d440e52034520000d00c44800c1e0a80c2c914210902050311007410301039610030060000201c048643d00b5594180044c00d940103c040c1c01c805821404040120a0100916206081c401400090051156a1408444885a004840050503031400803080003424810343c84940d03400d081011100c80d060741c1d290307600407030383c00000c1c01c108001c4082a0098001d10f001c20280c98107018494603102c010b6101c1e0000d00130304c0e00c55209640e618040c0c0c2000b02c08001100d041e2140070341083c2c80c541e566140c210b101070781c0c0c0b1804c6603188501246101e80080b041890118100b140e40380d14202c4c1000b03420803107002031803141080300b9004807012000050300307270316504125400941c9942c1c80c2d1003203101c01d07034140c010a2515900341c0500c0c0c021010b941d002000030b00c0303d244280c40d000070819511202c2e0000000022009200d030380100824040ba25000000c0c100c3d0300c0c4000e2214111081310b901 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 160510404 1250 160509154 160509199
    0x70e0702010902090108030c071505070c030506391e160b0f0603100f110c01140106020303090304060309150f050a0b04140402042a0f0201150b0711 65
    0x202000140d42d2110b2200440c5800740c0d500e401480e02c50011414a81059030080c0c0764181485454085510301036148a4a0b000f4020b83e48982e40102c517086078550b40c0c0c1060368491508540c2c0e019012005040400c0c80704505403103880521502c41c10320000b10020304171a105a00c030500c0501880304030010441070b2a041801040207001450080195007403038603041e10304a001500c9841061041da08010007610009200704800d5140a000300c0e031a280d40080c7c500038a00c0c2c010721001d110b0300103684507000405402041c405044440c0e503145503a6a10012a00c90000f542d071621180c000300b0081100380e100e908141c145901600340c0d41c0d801111506400115030340b140c02c0b2440030380c650b401c103c1101f030184112421144103682c2404202d61034009120480350003000244540d0341c17201400300300b48084d411640d010100212038820a10390f81800743c0b44031031100c45400103609025a0351048070740c1300c0c6400c0032030b40b16058880c2030032444d42c1c90846800c8440c2013640c209401325450100b800b042c00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 160511654 1250 160510404 160510411
    0x1060810141201090c0909020f090106081506162102010506010206070819020d0c020c0613030b0a0e01020f070c0f030804230a090603020a120203150c0d151712090111070e 75
    0x600004515147d4414441d50782010030f0074038842d55000e4010021590001841d55102c105030b07408282c2c4902c0c0100041060049a1a0f00f00007050040b0540c1000040300180580c803455006440840140480407170903207200712a15070040e007000300171800c2c60f0b006041894200d040c4032100c40c00800c09403100740403a00001041c041d81900d8486a800c12074041c0100300407107009440543c94000d2420380790b20003035000d20000780030211082c00a41c4d000656441140600122720080d076940800358401c4500f504520001d41d05280c12440004180580c00020000c8135071203074400303007850f14180b15107461b10304210b801d040340c40c21040c420049644114080c80034150520002401500310300600404081c160880c4400480e09400000540e03400030380c0a82074070503498045043c0d41c40721080c046500861500c1c0c1641814030f5501c0c041509848240019940d01030450311002c001816142d946013005882115006000c0000356120f500ca5605118490402812101203584c0c410001881c0c40045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 160512904 1250 160511654 160511669
    0x3081e04120305120906010e01060e06040b0301060c0c08061b03040201110d030507020c0d0807060b060d060f0320010c0b220b010603061e090506040b041401060810141201090c 77
    0x2001d180941202d030f082034000c64171070b0060115604151800040c00c806000c1c1d84203014080144041c15560322088501425840c141e40d512035946941c007800701c1403a14000c80741002e02450114041800090303040c816505c00000d4444d0803c06903440220354409001a410050448000c025452042040c2407001d407041d038001441d898035000003803d00480c92038841c820a40c0311050b50109006105a03103826820071000612865544001195482403000214031103090070340014400e50701241407402c4a01078001c143d410100045030703005030300150a20501042c903001c460f0012802d260703007041e40a40e0092031480602c4159940030141445030400710360031500040140710313242d41070141800901d8080821100c1c16481e0f8203581d6810014040d01d02c00700d03030300c0c000030b210703a6121340141c148854090020041c043c1080b5049074484801d00403940810b4070075000c90900303480c03600e0030750494a82d174040c411603010020412540202c8070980344900e6490300c0c2d1400200c0c5070144500020441c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 160514154 1250 160512904 160512907
    0x5070f0501051807060c0203070509090c03060106020109030e15070605100b0d05090d02060403080f0c130b0a0906091401080406090602270415090c020109080c100e0703081e04120305 80
    0x3c80741c05501d004d4250b000081008425134040c00183c0f0005030401c00d030740d07003110500a90740c0d6001400e40751042450125906103e8240001640c54041d44040c1404d4001d40c3c400102203c2d01e424400d40c1007200c0d0303021b404084c0400a0b5001f242003540715035000078442140035100f595441c004e0300075802103490303030038a1903890b818441c03c0d400401640a1040460020380b1403407a1644000e8407280d002000000c4800c0c414000404052071181150801e00c5410180c91009841d02542c02581c4c0090700c10344041200020f021075464060700c520f004407414071040203103c10101004403002c0d2805041103034103a4844508100281c8140064280030500c22040d5a0241401c40d40381001c10328541d0076402030740707003d4060380420511030f04c80c0d0541d040e005010802c0c030041e0200301e00500340b240000d40040e401040040503c2804121a034103103000b000305100c2200d018032001c0c0c65801c6840f004003611410002404401100c2c2c11b0004028414400642400d96541060240d0610b0f4081100010380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 160515404 1250 160514154 160514191
    0xe2a130f050301090822030c0303090810151202210c1c05070303080903120406050921040e100e01060e010f0e031e07170319050a02030a05070f050105 66
    0x60304034042008000840c000d00050409440e50149441204022070412580211440183d046020860010750307008000c02c000710b54a0030000e10415150046e14121b0050803100750f1242e004c0d004800920100021380d0144600d0030b440b29504012052040b07801104814135080014a00780102d0068110f88001d0000304d0340e40820040a08108a01072407400c00d6440300c0710116000040c6541601d41c5414100180e481e06030003545903001d45c4511146542d0404100000c10038242c11039400f44000001b112400c0c0c001100e0742e140642101c3e1010100c0d041800b041103c603d00c01403072a0091102c0007405542a00d80042080e01d0409800c030387c02080f42c0e10541400303540d0014000d02507200525200001400d032000080c1c40340c070703005c0d100c0014035520211a9194041400380200600b00e891909010191615007207840b03420039444011002c070544103000a0074051000c48042d0810395011b07502d0f041c41d50000b0345858100722070544140d000241700c01d00082c4244151401440c00d154251313102c14 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 160516654 1250 160515404 160515419
    0x4120506070503101203090e10050f0604080604060b010905150c1005090a0b0612030c150705070b160c0f11090a020a050f0711090403080a14010e2a13 66
    0x1402412040c02c200c010410800d400450306501390566000440c440c18040450800311203403080c42d040802e998480b0001c1c0000380c401d8140201c221203040c2c40b144114203110080210b2409984603030030003a000840040d00150155020840003031050511861068440e03010902d0740440070180c058400002a0050001800300804681c81d00c1c0ca401c03d004518220f041c40f40c440e501407000400060040d00811103541e0f540e1131105075000d0040c2205e40f076401100005555814607500b54184407066004203501ca48120100c85003980c020302e5100040d12402c220452076104249010100025480b0080000341a00401c0c813300d0b0007110000001c2e44218104841c3c1040902503208140c0b040140d021101d410009079a0074001c04946c640e25070b691800c16001c0c1391030307500b200d60f40031f16250704010803d07070010905805023449003020440f10036003030f05405030040c0a0107000300344030340d0038001400c420030200c500005201801c21550500041d0101c800c1907004494031711164a03140c3c0040c040744 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 160517904 1250 160516654 160516663
    0x302210403020f10020f07080d06180c03060803030903070b090a050a110f010e0a1203110114040512030609060603041505090c01030c08060607140717030a0e01020f0607050c12041205 80
    0x407104210b045146c10711b4064011940c1c403414500505900307010407003003454002ca5200d8001444007038186410040a5080c09004001c0307211218003003031030440003142e5101d0000c01e480c881d5071000010b5241000c030381c40d0200d07000c0c802440603455205070540e040004006001d420f5415124081c90070003425140c0c00c20003807142ea0b6044904015003440b01c0341c40b0340c0c0c6003032030300d4211a107049661402109070b040890300d80c0503440b40fa201543c00d1002e032100c414880325526101b80d0048054070b8007540032540c1c110382d0348000e844180d400b04c80742010400c2440c25400031138000d407243d03880c50a500c0c0e03c1005502a81e00450b102c94845e004042000d403e5601806aa03000f40301505d46180903181040019204e030245643c0070786202808240013001072000c000b84405080d9800c0200c407081a600c00040d42c907030000c0c01190020310460702c00e000e69400054124020307408034010706810398075034000310780940140c508a0030510500341c41c0030710031a8020040003d44003a00000c0410109030400c02e141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 160519154 1250 160517904 160517923
    0x31b0d0306051c060e03090a030c050423041509051b0f03030f1209070e0a0b0f040b100e0604090e070509160f18030b0f040506060103050106020309010302210403020f 73
    0x403400b0068914020300b180c0f0303141c004160322030000586000d500460501c2d60091015103504000e4840010080c441d01c112010308844044030305021850039030000400c24904610816845e0030110b0200300003407038050402c1000d1000d0b802c0040c02d40c00d651516803400081005940e0b01c282c9840110100c0d062a0803160860507055005603d02210000c40449a02c91000d108120401501c040f4503002003d21003040107040c400e48548003818941c0c008070080103074285c0d40d446a04d54108413210740c101405070203401340d0002c1803082200f00e4200e00b551020302d40038115502c260200004500d001c40351003106031003100180200001d0b030034a020701002007400380c4659295050185103450059010210340741075402c5251420015520307040e0050003407640c1c1c100501a801240c20010042d41e8540303e80e128500450486445880d00300047d011104203000e2200107170000c01030b446865000c3d40040c140c1301c201034010320110494017003620190500f40d500f20016001040c800403c02810801c0d01c45 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 160520404 1250 160519154 160519159
    0x1806051609080f03090f030304350a0819030b040c0c03170609060105070305070602160203010b0a0803030c070507030506010e0f09010b0603010603050c0c060103080c10110708030603031b0d030605 86
    0x43c03850084122590720b005045046108201340c00c590f13021a1001d00c1070398010904515405860b0201541d00c650114950400b00e2499030640c031070169a920002c1c8141c0c1c07658000d0040c5142c000e810101c40140000b1041c5038060545400d48111651250700c030f201c8824041d681e40403040203c0d840d0080c4070148000003041b114415409025103560380c1e50007240c0110090802039610f2440e864190307410301032240054506840032403c0500b0014070b8230324804c0700784200d00802190308a4410810042428001c140c065031081c030000f0030b05001040200700300d600520441d0001940d0b50754032707031605009800500a014045080c0245111401c1e840303070300b241180001340000c000f00004031300d2600051180500301078492010651000c011003c6500c11020035098410301d68603030800300d140390700c0a0703061011442081d034840d030188800c1c441c220080e10403808051034502c094031240e01d5070300090030700c4d5814002082401c10003900541c440c3c001445d00000341c43d00c41100c61019027280c0c43c5a01850 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 160521654 1250 160520404 160520413
    0x1809230c0109030506010603090f060204090b0f120d030507030e010f060e0c0a0c020904030924120e060c070201050f0403030909150501020607111c08040b1305030d180605160908 78
    0x20004d44042481da0543d40549030004526859080a03c0000e84640000c1d09061000401240c2c400090b0440c042400c0c0070f80780b03041125109002c0c03190480c4036010400e01d40d080f00903442180c0344a0340140b44c1050244ca03001c9680c2a51607412802c541186c00c5030727500c2640d50902040151000702c0c8d205d520407407200031507040c203615410240c108485040001d206012034400035041501038120703031000d082c0801c0750400c10200300399141c100e00500344003003010411281c08442c4000f080c0c090700c07a40e44008000707040c01361104692080c60303400c480d8040303041c400d0a00040586950725009070000318017030756554030003a240c122680202c560b0a401c000d03450092590511190741c0000b849504520b49180420001002208040c01c00c1040102c400151001200f107141e0300b94000f4090b4020340c010649005030f5140e181d00c203044095160402041500240312146085c2071035841005900c0300b44580902191f0103a841c802195011960005010560b81c0c0a4145c03541c042040805070030a1030052 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 160522904 1250 160521654 160521659
    0x40509010501031b0305040303061d07110303060d0b06040e160906050904080909060d02130e16030302063412050f0621280215070201091809230c0109 66
    0x2501040c0704c02c400203050315040401e0405200b42c0c031903401041d00ea1440001240603045c10301c941e20f4103030780707400010328a5060b1035000c0c1004001c99000301801840b804032040d0320350b610606110004c0045500580c1d80b26038070082d610a00103182c0c1c48142d001c000340c4031030906074030b14102c1d00c8a8100034040c2c5040010000090512001c035440d980080f103640010b95100300c00500fa60701c00901c000e41201c48010302e03840b6018107411196003082010159a041c00e10b1002a12600c2581d1101600603405980400d010300514180c551010740c8800311a85070030b07510380a040049401d0004540014405c0d00c880200090621600b50410360a4114007084d01340100001c000e1441d8880000080d0762582d50098a04800c000c1600e8600d02034000740b0b02c6031001d001c40010300090705002c1e0702400088408840303036030003402240ea48035816100c143d166400c0110050b44e252112500503901581c840001c1d011520707466606000000c140240c65034204d064045600300a200c4c00c810341801402e0409 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 160524154 1250 160522904 160522931
    0x1005030415021812031e0c0a17120f0a0606031b030b030708060a02090a06021203070f09080303100602101503060513140a02210d080417040b04050901050103 69
    0x80440005207107015840d4004889180d0941d41c000c81d4650303101e192a030280d200440084080d00d43d0341c50140c1044000700300c4982c0d00003a40b0400702c150305035800407508000062003020070408c1c0c002d050040301c0c3c2415900b0380018480f01054914002c55a520000c11142c0c0545010744805046503280c2407003021722a0340800721502015504005041d11484071225680341002214000e006070350407100b860900c0c0520500039440030503241d0080c1e28007800031942d039000050707001d80610300c44045072440e40d803940c0444401803161507600400450580015a02c40208040c600424074140030010480c42e0003c040e15001d2214102c0c4245410031450f00045070014501c0001c4079000403000c1016561884061000300b036058004001c1c0c065520a00b846610000300151414401c0d03800640401850200c0407000304c42c254210100d500c1499036071600c80c858a611608503210b8260f003440c1c15064070500d64030340c0040d041001c180324042010841c0d4a003007003016006000070300b000c1006483e886072 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 160525404 1250 160524154 160524173
    0x3031e02091e041b0c021014040311061306180e010b070602030a0219051c050114130902090a020a020606090403091a090409080a031a031f0e0105010303090510050304 73
    0x4001416215840c03403a400b0761207a41151004000242da690320812000f0b1001e44030b41c000200680c000c0302c0b0140e0080c802c502880c0300d036554504c200c440906203891550790003000c14a02d180b41d50001c100740700003c80520960b850760068802a280c000031024484103040c0190701d02d52080d40d8208908004001c0003d02e1422104440c1e04260096501e955201d41e85019102d0b45403521a05a0403151500c4500c2e40400680101030030700002e403014940c0310142d04155a0203015400354003242e00744240031490040c0d03010006e040340b4403000c103040450340c0002e02501b00489080e00000d800241c50814198140006644000b00300d51b0584c45041039100101003020500601389000450072540e010481100152442c00c10010320501c0107840b24030703050507a90016102e950220707003001207031615800c52000d003814072940a4002c042d05818103021000000d080d1204403140c1f0b030f80d0700101c60381c0c031401e000755406103000e5114844090300d440103101c000400b0002c1c205c01c014060051000280e003804 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 160526654 1250 160525404 160525429
    0xf19170c0d0c02012a0906020d0f0509032d010e0f0d050a1e200118060b0118090501030b090d1223041a15090613060509010303031e0209 60
    0x400042d00400088240d0040860110441c084a07a04102001101c0482c00a2010b55a0b680d0362003280340d500d407410b913a60002140396002140c02a000d160311244500c000c2d1046010090481c0c8071284d80030800c40d400c0d0039024150102c1440c080b541540d000e000d014124009420f8001041c01d104400c88040d1501a49115503040100001e0103041d110b1040c1c80131040422606c50364810211000409418108800c02c41a59121008d03441195004184281d510395840452190f00c0300c0041d950b140011300c05140301d80d06100f80d5115000c41200c400002502800301001e0020302d40d411400c240e506100c00528008055100d0500112001e074040d030300300c503a0703003002c500400c49180f58407580000c0e1180d81010014200741078100320a220b03c0071801460048000c0c0d41c961300b61101041c0720100d803040641301d40c0100300800850036a08140e80115400c85440000168181d00c03070b00024584842a031050740060b45034a00c070ba0155854020b204e4800d000b03006c0440c50010400701048480ea00328 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 160527904 1250 160526654 160526677
    0x21305030d2f0102070506090c0907030b10080a060f0909020a090203040309091a060c01050f010f0803071b030f03050d0b1806091504060f030b0a050c1207050f19170c 73
    0x38003a40310241d0250155aa120740c0501950707e1407800c0d030b0010755940303840c1c90301c988030340d050f280070031401800391240740030204000d0301007000045640d10a446084014005c2d45650342d550000064000200307031202d02030201804046072140442c01040041c591030780055450038170401c24400060380150501040700c20806020903400c4045190041607201c080646170450000202080d90b004198403035071241c2813100b8022001e03601c900080704184018004e0800c01d61082068030045002000104003455911005a9040303440e40d69070541c01150050440114001088182c03030b044032030040b00981d02d000d031801d40d17034000b2201c40108440790150045005460740d00100c0d40094110342c0c0012005c4001c2c2060244a58032000311061046030701c000e940403807505e0b021030b80041503800b42c0c9002c1c03040080e4107420501940d1180f13007080d4010b04003900340002001118080c01c4a031001e05000710b400a01801e601042280241c1490b25010503518a40d161404110888040205450151849 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 160529154 1250 160527904 160527977
    0x903030c0611040303050405031006050f040f0908070602120906060d061a1e0f180a050606070b01030b0604050115020604030509120304120302010b01020d0c02060a030f021305030d 79
    0xa003040c100a040c0d041d08002c454100090100034150014004c00469405034200c8a8014540e00c84104640070703400743d680d00030040340c0007a0180ca09070b000030000b10301c5102d00203800c0303002d40e40c0c220b02c543c00300d141110700310703008582c5403100724030064001d900404620291800d8030703200c000580703074802d00a0004c2103150307500381e00c2c602130001d2411002c0709070300030b800e4480280c101208407181c880c1c454846445109190694855810006001142e0301d08401c0003c4094446941700700113002e00403c11a0450001e21801011405024115000b10302a40c1c40c1349030b500f851000d110503a80c0503084103101c2800c0ca00e040010340d60009181e9840740e01481c240e031b1201000d000044142c108901c460031316110215010039449840e528070381d101032094000b0004d58600000580e01d0300070000032500825070080125001d0304043d4000d1001a0262400144c2061074070f68203012038000c0c07040d0b10032280703003900240004e0070108a84007001d1000d003840c8041c0036110100d01040d04490b081113404044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 160530404 1250 160529154 160529177
    0x6190b060a090504060510080412020c1306030507050f0d060b0609180a0b0d020904030e030307060e01090c1a0405040f0603020d03020a03140406050d05060d020415090f0c090303 78
    0x41650014146010003800c507a5034181034400200882c00e907019441c411860304500144500c0c142e0030500c410000c6885586041da034075102c101074800e13200e4914040d030068400c800150380c1c9104e495030608440700c00c005195070441c00d00360729100c403d0308103c2c0500b40f030b4000040d03596182001032545c190711040100d00e80032124041901c601414440b02e41185c05203102140c01c0302d00c0c0322181e1103038045241c104100c2c09e00d0360801c0307801012101c01030340048071030002c240401e10075140709000003030240440341381c00303490f0b610b940c1103039141c80e56500541d541d191740104021180000038001c0c01c07400400b13409400394400e40360a41c843d62060612941e074680c480d15118007a50466001543c00401610000c1034904001e501c030484600708400040074135601d01c000c000d6007015141130710352035501c00c1e00f804001c001c24001004058407095225410020480059899020f52040304410340348000099141c01000b105590144055400c841c0c240709045034001d80c8903006070b040760742502e8250b15080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 160531654 1250 160530404 160530451
    0x1807030905060106033306181208091002010b0603060f0315040501020909160923040e010c11030405090601200d0302040f06030e07060e12010f09030906090806 70
    0x484140c004046000e900b000013201c1da0154001300e0b407080c410031241200c210300d849440040000081c180d006c0000c81c5070030701c82c080c42410341c40c01e5013481d44d034880103d40e100c0014141d40b01d58401c085429850015a5140343c0c00c000c41d455000c2111400240300c600d40385000142c090000601d068000e80107050341f100e8603501040f90409804841c030f084040c0f03080504040e4042d41c0b040074100e000f10070b0040400e1006885a41a19594850b50303100400d01d8101182d180300c91344050300c030104078421006c2d103d1740380c2e4076485880040c8480c000002011740f030f0003102801c000344000e20720b00c240d081840708015a4440c21005a840402440e00f006100901074804104604507108100e0320f00c1038528211120380c05900902c2540d0b03512610f4030469640e910b086083e500151a520100e410050f800c0002e503018102c80411148002c1440341c0c0004072041440c02c4400c400c05c01501540c0302c80c0001e0605800c20251005400ca62034a03a2590303090204069035001d0240940000e94240e80e190080d81 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 160532904 1250 160531654 160531661
    0x1513050f010c060e0d080c040e01180b18090d1106010308031b03070f090f150e0307120803270312060105190f030c02031602120a05011416030b180703 66
    0xda010008000b41d101c00785505a13a172000c1c24244000c0342a0101140840100c0015038003114100c4441e00c0b0307943e08000441000c10902e1041081230303030700e80360b0320403640e0b076040d80251803810760b0a8845190314000d0344603071402c642c150910050007035071200080c0a0202055140c1565000304065690b0f0310303030a0341001d02e140040c44507902d10301c000c41808445a4003083c0c0300c0b4a440c5655a12a0854035610b1503001d40d52948074260a940403070402180031802113a05030155000201a109034640c0e40b00a0070842c0700106080303c50040020411031310040d03c941044503400110050355410210500c2140e0380d2080003611507110303139004000f403410381c801c20441d0842d5080040c0317030014061844010305019403100300100030a09012060f480c0e030348000180ca811090041100641d000c2139028402102007244842c0c6c02c60090313030849400b041090007108c242e0b0308101c0e02d210030303850110a400321103808804d0740010181414407000c01651103207060302504142480700540c94850410030f4006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 160534154 1250 160532904 160532927
    0x302010606090b1e1210090b03030306010c0b1e15040e0a0206090d081c020403210f0e030709050c1902030c060106050318151005090402060301120c0807080c1513050f01 74
    0x41e24941040846e400d072070301c82d2049070240d10f03051050342190000c245d01c0703001c101c40e00c3e400101d280321420b000c180034821060f084408a50286001100581654102071003259641e490b402c501583c00c0890400b8422030020404400c060410142140d000070701900c5404082031007500c03284d05590a0001050441e614034803100d0b8001d0504000a06c42800707500300e88000c0c0c82142e054090030700343c540603040710700000074103030790f12103400c52000c000f940c3c4842910662900b5116402010400a17580c4c0315050090120062541d161954410342c00d010074011401c0310f045401c10320103001000c000281c1b5905403102d41c02c2a541780c3d680d61010402c50034212890440b1071041c070351121200500000c41e240500c10607135035002d40380c3c2c40d90180441c844064400940141d410001003102c0a80c01c89140c21051041103803070b0400eaa51000145822503035040400302d40c210b00e0480c804c0746030540c20749150b041500155130400d00303280944200d4590922541e40100c10104a00d00c2c143e2050702d00c0c0c0740 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 160535404 1250 160534154 160534177
    0xc1306081608071407210302030405060604020f1b0a121103030105010305070c02042306040b28050a0e010e071106160504051008011403060c0a0320160302010606090b1e 74
    0x2c4030745c0c40d420100c8490b00d000c24503454034008400d006842d20b101f130084034800d03074101c0014000d035111042400700075440398149d280310401c140034050705041c8059010f040e03480008000c128804c0315041101039421b0221201090206121030b11480c00804025a81101e1090800040d40e135103001c801e0364a04000c038002503000e41f0f80b03298400e0340c04c2e54608a016a1090700d05900d5940e41c2c400500044a03007200440c1d5103c00ea20f088e01c0e41c4003d80d080e210341c01e0a80d6454080e242503490000c83c400703200940004204981090040c0072607180b41008991100b510300c0d100c0d0036518450308041e202e80d03015000380d0001101500e8488000e0003601290000d000113003103454914120500246842001c1c001e480c44101840400041da14000608500030101c2c0038203a464422241c5d4141c0041c600c1081503d5079502d01c0700010805180340000e045040048010480c44000916009086411942040c41848001c0b5000d01107841d00c0400d5a88020b0020804184055005011880350146804092 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 160536654 1250 160535404 160535407
    0x80d020409200c0a0b04020d060606080708240f03070b040803070620030705160503030106111e03032404020c0708070909020618010302070204050c13060816080714 72
    0x80040d15580081d000000019038120b1845140e06804914031031085120001e0b4005020740c400300300d50701019a00244001c12076610501079584500c01c0e0f034159404030000c01e00744410003a416422031080c0b41c0c402028188102c544142d030180b003207038480d4680c1c500c0c012590122076220a071820404117028101c150328507602c1d107968200729956580201c0702164021f0030141c040a0880500b1480d10747d0b0b1089549036401c50b51044002c071502c0d001760b040241c0018583c0310301e402069003400254042d0501c2c1d074806000c02c043c2c0ba55145000d0740d040e079141ca02107414800c0101603402000317032a04003d038440b00011180300a00707010b02d010390076100d25912502c00204a20002400148681111b40b0300056512240d9186c41020440b8501078010790450f00400c54001e0508501070031a8180314141801801c0c08902d4022404985080700e0941550310002440c142d01c0d80e400351024010300c454038144007540b40410011032540d408280307480912141d007004c03c03000c074091540c8018140d034802c00103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 160537904 1250 160536654 160536659
    0x10902130e07170424050c0301050607051005070906030b0f010918020403050f0a02011707080402061b0303040309050406090c021e0f030c070e010e01140d020f0d11030f01020322080d0204 82
    0x1714900c0184951604842585243e50b803002c6400d405524490316030051091300f07680c0303400140065503205480c1196517020343c0905d640900c405202d804d003c0c410300e50303c0d81d0380c242c1000c002808a48101d039036035114100340501c80300c45a0f031140503001502c00402900c0c1d813038900e00507110080d018980004185001f690390200e0341900c00200c660b4100c2c000d03690744041d544000b0402c001c0c01816201c0d100020f107404009005420440b0040c03207058039501c41d440c00351042010342c2c0d0854000769000c60014500072010055854240103010140444c85400c01c200031580074081c0d40c070703074401c45400c90403540080c0341007070300800384075440800014909484e6110817548110707494044034043d017110031094000101303400f03055001c00d1b4103903100300c1c0200d0030000400b400c0181da6144c83d50101da004641001c82c04513070320313080100310302c03a8031810341107156903041030030582042360019000d94260b10520420294151800ca1400484100d0101004d0780d440d43c00d02c016980f00d607181402e003c900000c0c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 160539154 1250 160537904 160537913
    0x60b0c100507090312080915070507060c030b0d020d0c170a060c09050f04020319060803070620070b0702030906190f02060115050a02030904060608010e010902130e071704 75
    0x150042803024410816591008000d46108045010107002401040c1c1015030740c1e1301a13203189810071290304c203d4541801041c0c0341c01c0d02040c100c40c0a00000c0c40403070b94804000c400e00500003000161f00302407100d200c454012600140b001d00000e44920010120341040c882c40d0a08070001d04126140c4002e82000c2c012003e54500710408101c0d03400c1d1030414281c20b114452107403035040e180f00030411540042c0020030840070b504094043d4414840111b2200c40c0303c1c002c0d11500c4000c02e8008086d5032100c2c20341c18500708030340c0c600030011032000c0d440c11100c1c05110000100c40049520110000c0a61541369080b46903028031001550040c40024030200480707000346881b11402e2042d520040314807003d4100300e842d00c10031311990000c2c0074015405060a030052001d020280c2092040741c2c240f07500040060140c6e41694081808030306130354018090300d880c902480d0f025281c070410035460140621000039103643c4510400c003144041c000410f149900c41c45640060200140c1402c1071030a10303042 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 160540404 1250 160539154 160539163
    0xa0b0f0301060902120a0c0804030c02120a120201060b12070c0c090609020301090509030702030c060931151a0a0516060e0705010c080313080c100515010e03031804060b0c 75
    0x15410310f03134001000044e500d001c140200c0000041c6541c3e0008d180d1241ea8069480034030201040382c1c042c03403031007205501c00c0c0100201660107014241039400f00c200d00001900311030803074124010b100c0c010444540a241c1c06d00303110703170071640030310300600b0144050070441103812480e0010881581028400240404a5005941a00c0803010f00304000c0d25500d5000b966880b80040003500f580102080d000107203000d402600030b498015020852038401002a000c0c401c80f1a080701450280742158460144103c2c40b80d1091104042450b0300100d0905010000048144210f000d4240000601d600460f01c100183e90001103201c9050100700c8032403810b00007401c003030360720002d5030b1040e1039000545600c41d9403580500b0b60801d8041d440c1d5202c2402c1c01419070403c02d001d8038201d101b00980f28028a042107800300102820000007200e040844003800294801c00340581003000d01c04803002555404400c0341c4070034003404040100f0761031010104000d032403180d0050101410228a8071401e034008034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 160541654 1250 160540404 160540417
    0x3051009030f0c12030509010f1e0617030f07050705060c0a020306070503010609090504170723031c05091618061e15020313061e090e0a0b0f0301060902 67
    0xb1103001101c40c1c0c0b1070007224441c0c4001d6000d0070022102089012450080c3e010a030404032400000c40d040c41d80014507419910340c15400b5052458490500c4a0100036229160241503c0364208458000104099030390307008548100d560614000398802c2004403c000e20301c024031014049503241c1c0c0d82104015120b401d0f441c402d03400b900440340050440c81c410400c40307040e11401d48842401d607003070044217002801d0051085441c030056400301e16540302c52801403c2850b00c0381c1c2d49202251800015261260215160b070b40b0aa442402440000212010840705211200200017469903800700024a05000a0301c00f0518240303405010544c1461003481803501c075500d40302805810380c2e0305e03019101d01c1c405e0f640005802500300d00900c0b015a030070252580400b8288100c90a0070213070b0429012800c0035070301400100301c810814010400f4142011034508211b4204210403070f01d4114a80817030355004086600302ca9130b0f44964040740d991000019544034025000304100c80d114040140250301c0310 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 160542904 1250 160541654 160541657
    0x31c0b03011802090f09030f0c0f16081e0a0b0703090209010b0a0f1d24030118060503060412080c121503010b06040303020a060203060109030503132408041403040305100903 76
    0x21000110010320201060f4003070160103001f94500031141c0c45121003070f00000300140c12800341e0380f080348402c2c00c200003020814003018000d94105217880302091801101140b0301d010140c046c050070004110101d40aa1040c0d0886510f000a51390b00f50218018140b20100a510010b0000041140586c100281c04480e1081c4c542036110321421909403454044285081c03107801018880300154201001c60030007d60700382c414180e030441e80c01080031003030300242c0005004000845165114030142d005c4c09000703100030307070141070142441c1d00d034150100701070801a428450f1241c007040500000b03004840341d081242e02074442500340403111004101c4040880c074480e40c00c1408081c0b035407400e0000c0300c0440743d16800070034400003d5030318800a500002c0000b4180a04c5540000200b40144000c109602c3c107000300d0b9000f54244144501c0301013050007011800910207001d42019600000040c2c0c10581003006a4000700c2c240314014a54816900010420700504000d00c8440300346d5001200890701c03d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 160544154 1250 160542904 160542919
    0x2010306050d020904020402071e0f0c0e06010c0f020f030a110f0111070e10090603050d1206120803060613080a03080604020f0d0b031203010807050a051002031c0b03011802 76
    0x3141c0c1005030311044180043d510000ca000442c00510b051390041401501c1200c0f8070074100345514042a0740c070301c0030500b50358034500030240c003040002080120b40a40510240c611103030824100091690a6403140200138818004042080d580d88543c11603c010005045500084c80b519050103200c987c580014011701e509c5e28041690340c06015410b06c0800500001e1000c149003112410003140040c0030070100103041c2c0c00116114203103000d010090350065005103024203084c1ca004201d214295022100700c2e00d4603406115004040f121340e0800c1da005000e81e5100d80b11000020042d1007642c403040014208080001a4210302141c10880580280c943c01d14079600d03c0e05201c00c0c0d215200c6004ea141c00204406140c080352640004003c0901408540141d443c40444060640c0282c115880507403212030104494038111140c0d0010704419100e04203444100d00c0080e54034003030f041c00f1400418800c140000d90b03540316131000140510003402441044204145040300702c041040580c0548030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 160545404 1250 160544154 160544159
    0xd090501020313170301382b1506140d02031003020310090803181f06080706030615030207080c0d08150f0d03140708040b09010e120706030b0a050d060902010306 71
    0x5131607040ea81214031342d08602c0d0310400307103d031825105130000500102a81034110240405000c44000c0c103000b10040000ca851900140101c04103540130319160701185e1b082401003502c003110340402c074044605c2420300d5001c40c90019a03a1110780500d0a400c99028030100420032002440c401c0b107400c4900035816206a40706102c01e00c001e4030210b00c000f408800c01040840c0e401e590801149000550f0181652300c40141c02150311042000d11100d95000758864505001d110002e212a4004040500381049043c0c5440c0c0441c0840c1d000302e0b580d4041c5980801c54800780710280b0222000314884c401900da01d54400500580705c40c0c3d003039035064222030950f00514041d0400d50301e900c0d11504002d0510901900d0707690100e40703030b552540110710795039010b000340c4d00003503200c2c4060310140000126103900c0b20080c41c0010314414903843e105100e40032100640220341c00200301401034491618000ca0000341c01c0e804200b6460103544007030b801a61540fa01024802164010a032061003660148445c65 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 160546654 1250 160545404 160545443
    0x6040804030b131e0206040e100801150302031e0a02150c1203040f02090403180806041103030703090b0d0605090103050c0f06040515071a070906030509120d020d090501020313 77
    0x10340312032008220448680341c1d0b00406134800c01007820584001c0030503140c0790b1600c1403000b00c03280c00d803502280a10482003d002c0c5000c00e0186403807030300d44003904a01ca145190000390f500e4480408e424110108a040e1b038004d01018008d40c900c00790054401c4a5120703182c010a02c0d258441c1c800740c2e070a806500480c04010740348508480c01150041c034400721380c02c42d9800300520040050b00071401d107c1c280c0d59001e6641c014001a200400800018103098901801d0401000c070900c0c000038800d0b003041040f07000107074002042c02c003500d0480611903196440d01c5240c80c003c1185400840d0311042d22000001040000505544c0102e415900804a20482020b01103280554000c03c0e17400b545100c0710365451445d5002a180641c019401d210720010340d481007460110040d01c0400000f00d9140d41400b00d0ba401d80203150300031031400c004002d4a0482d22840b0b003d030181212901d09103400140c1c10004140c03d4009460b4560001c008542da41000d050200030b541201c030f0f046658001c0c5020030004103 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 160547904 1250 160546654 160546681
    0x21c170702010c11010201060f090b1e10110307050105161b08030106120b060408060702060f0108070501110a1202010b03011107110f1801030b0f0114181806040804030b 74
    0x103541a1079010000d010303030b41c9141c4121300d1604064110340d651000055a40100c44060005000ca1800001da6a5926041c0a0100750010020485500e8040c0d148284e44403515102c510510603c2d290411164104001e815403140301405016036003007000348941142019581d4002907143d8070390300c0e41501e0b100d01c0350303880d80000c1102514400007030004104040c046c03468160044484e801c00949841c43c00000f0360207421903000001254011800c008609404101c896001402e501c0940501c1d0f04d09a00590f50380c03014001c1030b0400141007410040d4010400000c9500c0d50b0001906a4004001c50000d00820340d14001038803a40c02c254040040c03801001c12503030616000003045041700c0c41001441485c5411a84940d0403500e200c0300003502568807041c403406948141c51428690404c07000c2c402d04800f06030004842c0201c01000c03403080d82d030703005c2c980c0e179090300a074481181d2681c80c4109000ca4501d042083c10300e42c09104204803c00008000810580c0c0c0f003440448815190100747d031104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 160549154 1250 160547904 160547917
    0xa0605090415020901030608161409390c1501051009051212030f15060f0304121101060605070b010e060306011e0f0306140115020a0602090d021c17 65
    0x403480a562a40c610b910b040c0c00400c0903103410306000c5101d03907613281024600102c0c0c04850641c0110b0b40400d00545042003654103103500110b4031000503041103804c8511000d2800c2400c1d5954256142d2402100c841c26100c8040030204240c081c0c41d80703280d0050b03a40380c1e0184000342042d42d20b00b400120381c605d0090000802c04070346d652100d021a0800d02440240c2150501460261103203005000c422281e2100961081c1e04d8400c00002034108000d000325051031000072a44920024020022401e01003c156a4055003250b42e61100c510040001d40e45140b0400504d1140d5080100210318290868014401c5520910700c0512a07a41c1e03034100a01e076070b019210765074141c0258004202c1071440c1580802c14035546204002d00c1c95542021003a00803483c1e0044505c103495903050040b100050f5052401484481e80380010700c00c3e01d1900944400807454010300c400c1d40841c41fa9565160603035410466680a481480c0011100d02c103441a03250009089640550300310a4001480b02401910359 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 160550404 1250 160549154 160549163
    0x106080d050d0b130203010f0602060105031b1908030d06080c04050106171b12090f01090c12061d0325030c1205090306070306171b04090f0512030a06050904 69
    0x10701220b51050000b800c220f507065540400d038800285203c0c1090300c000c1d4003c000d140403417600d82c2e11b048006810608164052031090700310b94001c41001940725184660440d0880d01a003403052405500e94003a070742030b0842c0c10b440c4008907040e9815203a50740b0410603951180b0495441111860400090b16000d0140c48005420f0b508008481403c000c20160880700104481040503541b080c442601c0d0844032101d0391504446040c17103410103007802505019070000009100002147e182d54203183c51a1203a0812880c1e030201880a205079640800845100b01110489480031a900b1540e6608401001c1400108d111030f9001590342c151480304c5820381c15120030301140300c15102c28844038003114034402800800c0117190b104c2d95062061500c201c403140c50015840307003040d200742c04915405440c00790950186e8840102c82c00c80b40d0034061041e40880300410340322814174100700b54407803a090080051081e552445035034100d54003e54421601a0020800a03698a041100510040c0d07070262 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 160551654 1250 160550404 160550407
    0x61205030a0309020d0506040308060111010516210501080c0906091003080f07020d0f0605090c09060d05010b181603050f040f050f0a08030901050a090c090e150a05090106080d05 78
    0x203010318001d41091200c3d90000707040124280d00c64842c9400e000f8105c804400081082d0200b0005603008501c840740d40c0c8071807000708440d07d08000103031410350b14020002c0900514901080d00910315a030084c1031044400c200348a5546d5445000c0e80d90b0a0520056200d00d0401d00003030f4103800c0c4a00031a1040f00c4150782d002c0303018a151510000c940c40710300782e203201d11410005600561181202501180d2242e003030a034110f806420b10724104d44001d080c00020307800c501082030540d03a80d440102d402000454a000341ca0015207015401040031001c841d0700501320004001986d03400c400b18521490781441840e0030107080300030490803100100c1c1c01c1d807080480000414041020100c96800c0c5c1e600c5103045908103850000e480d0b2900c2c40100e0203d843c04000020080300440a00665400040e490003e01603031459585100200840d4011200b0903986c4561803600030340208400121690420034580d07080c10300520036005040c0c200d0300c2e48015030038a90009420034000904040d0245240d07501c0c2d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 160552904 1250 160551654 160551667
    0x1080106050303210c07170909180d050c070f1503180b0403110c1302071b060206010302011d090a090614061c03051e09010206090c090a02030601020f0a050d0306120503 74
    0x1103103c0d02c406004540405c0044c8824400500180c2c41c000d000c0068040d06516075600c00308001440b40c00624445954215401d841c41e600d8000440304106440c2c6e062180d103e00c21141018a0202c0e02d071700c42650300700182000508191000058030301c15400d99014024194010701d0840168603007030000700b200000e400040d02007845001c0902405041d503054481c41030030130001465545028001c051550b40c0050381c64100480e024841c403265940070b806805803403030807802a4440d001440080c1c140060443c00030008003107691240140341e80244171185030704026640200900c807645003242c00511b4101136480d80070840c11a039104080c0201a200c4503100307280c07503c8115034560b2003281030040502210380d0010a48c2e501100e40450141c540d41c49220480c00289441d030098120341d05600810960741c0e03d500c1d01c00820b07a000c040d00c0005a540d40b20300004030702c0d1075803c2d00101d40030b00460810070104800031601013510704d00c07942c0c248003c98440821820700072481000400da5401040305 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 160554154 1250 160552904 160552957
    0x302030d0c03080f04020d060507050d0b04110703030e150f01061115041202010204050901093c0518060406050a0c1817190506040c0b07030206060d0c08070b0301080106050303 77
    0x1845d500038405010081c144805542c0e0740151030040c0c40600120b60049040e00401c0a0342c49185d515040c201c4085c0501101c070591310700d641c8207428014042585406030100030850402c20b04c41803c040504a0070380b0300c0c1450101c401c0080a0080000081c2d00d4600080e490900240001d80f1002402c1c110640e03484660310403481c01c00c4413103c074065540912000400f559464002c0e03000384200240410607904018240380c412021a0841d10a02804541a02003c03c041c00c03005159081c14030005441d110000000d04d44480c50f1600055842054204410031410f40c00507130045050000c1032201c5c244425098031014010041c1502c100e0651908108c007144407140d8954034404081941c400c030420061a8141c102000d03415a00c90f8454800e02c41042100c4103440000c1c92540ca210b030400314181d070000e4070740340b0182c0300a00c92050901e003a401d100e071111605000f014060200d0b80007035602e15440805800034451071045510340350b000200303800c0201c00c898001e020001030b07d0340390181200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 160555404 1250 160554154 160554181
    0xa0b01080f040c170c0f010305040c0b030402031005070c050105090c010509130e060c0a17150618090712052d071119060f091203020906160b010302030d0c0308 70
    0x181e80c0c00400480005032031219403004c1e01501440b00c0948011419034052256466000782c41c1d504040c82d00080102185840c105030f803d949669010542e65125800040d02d4005c00c60410141c40c1c1c900130500491079040f007000619640b088009004659546100c140ca403603020403000c0c041070080160030030a01d040781140426454401001800e0b41e2285403503450000111001140000d0000d00d00c1c02c89034200ca8a2100e10341140d11394a164502a5000b01e811800f480400d40a6540801c0c0701255010009050207040ca0290443d01649400c010040503910001000d980c0140350402041d00140780c40c07550bc0170351404c40c80004610020341030551510000811400400c80700c209000001c1c0c0050080c2140030b81c40030b6500094500c1e6003800402c2382c1c0c908403101280ea00d00f07103040c00060440402241c21040300d060041c1c803261002d0202e4135502c650541501d00403201c17032000040040410b03226040c1c030b000750120b9000041c000810345011401c010b015001c15000030005085981842 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 160556654 1250 160555404 160555411
    0x705040b04090c0e1902192604110f030703020f061e0408010911060310050f04060302041103161d0906120609010614030a08040b0a09080d050702090a0b01080f 70
    0x1000042d00300d0094807000b010b4540d030f0b00106180090354045c00354a06503800c0c0030003e0000403904529002d040c5150b02c0c800c90403025110140000768a1080b0042d03044860403465058400202c0c081e03142074905400103610802e04a03200b1f0400d10840923036405c0002c0d061080da5800340441c03919101d1001009000e4011400c0444041032890040f80e01c6400640944002d200d008000700c0e60a4952800c000f0207440401d0060094200f44100702c2c0f400c0201003608100c0700e050b0b070300d042503590300008a4080c060f19040a90854100a00e401003460000000c2d441281410b40d2600c10900300c0304e0450310b025a14810700031903155107000c0d0300c0c98903000e207103da0032480c0108440c3e00b08806d810030a042610480711203500e039548000800074100d0031880103d8000301180602480a02590398403100e004034014483d0703102c00030541c5403001d07002d803108001600d204800c55911a60344d44004003550b01c5000100c1c02070000700c1c0800d058910034042e1146101051b110403141c1e50716140e1743c1d5230031007004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 160557904 1250 160556654 160556659
    0x6200f030c040302030f010509060a0b13050c0d0905030408010e0d09090c020304180e15070207030b060a1d010f05040902061b120a090503060c04080303010e190c2106080705040b 78
    0x400c0b000005a908122210800c0c0c8400c001003090310b403551006082c00340003000340581a0400504001e2030b039501c1c01c2c0050b030308411980044c482e120072082c10603a0141c55083e140c000e02e4101e00e401807000c00000344c8203c44c002d100030700c542e0078aa41a0340e01c461581030030b003002c03d40303078001130286c400a030304030f00b60f8903507248100e0b801d065072074000c0e5010782c488030300f400c40700c41d981e1081c44074210051054881c16011009518014105a80002c0d6115100e100c050308441c2081b002c00c03907664616214000409030b0a0741c04d007040410044118050400380301d0800303406070f600000a20b600b8640640081c05400810f0302e4140700880c03640c85115224030203468014015040d00000380c10201c000b80c5407110700d40d501d8403102801e00b82070614095000e064070746046030034841080040400021217042d104040c3c00903003503490f44a8041c002550110003d1a00740c24840b40c07400356688001300d00c40703082241d011203500540f0070401c1c504850080c090301180d5004441e051103d410150082c5d400c55401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 160559154 1250 160557904 160557907
    0x70b070f1509060b03010b150a030c020f0607180806090a0303020703030b1305070e01030522080d0204090c08070e090a0506060d06180b030d0915031b0c06200f030c 72
    0x2005841c102c40402504845443c0d6986040089083c24820400050003c0e0f4100303c450907004049403890084040c04020991500030a0301c401e842400880b88074002c05044a8045c20030302000780c003240840b00c86202c1c0c1d800060300091200c50010f0854003d448100180003040c001c0d881c110003941c0000c4040d030a05481c0c0f5040c070540c1d150110961040b030502e500c00034040c01c10400007000329a0b495052030405043c074051105505030070405007411907503c140035640c52418035002c9800c0c0509001003403800e01c041400603242e0140c2e044080c09130f080c4e641b03009080c1e6805006803607591200c01919004070460340040c070600c00070b80c0156002390009000c50b0130002c03032281140c10f0311001c1e000740c0c0050451980049007031116004104003240120007810048110040080c40c4025502c18402024080912820598000e501034070b0800101e1415a460b40c40c12613015050104c82c03541199442d14200450740c001e07511404d040103000d40c0b0f810070f80c503250152821510b9a04041d2507007610150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 160560404 1250 160559154 160559183
    0x90a0308071808031902061b1801030e03070c060e0108041a2205030717040b1813061409010b0a050406051c0e0a06050c030c0a031a1905090108070b070f 67
    0x1800c0000d082c0c403440d1910030445d000ca06102c02070614101410000040c101400c0d114001284981607032380b103800c0c00c40f4100c001210b2100403006841c2420329100603010008608080c020880c120405070748046c0c41d80601c2a8042c40110b544030300c02c0340c01402e40e10058503802c60382042104034036040b02c3c0c500d50050300d80306a10f401c2104d40440100c2228182d00000700c2c030042100d50300140d180e1400d482e00c00d6080524004040f0340c40c0c4200d94040600903100ca010125035502c1802444001c010f042c810040d0f140c49028400c000e101002c000e40c800c00d0480000a01400c0410444038541c01c40d58070a0704282c9081c90544464110441d0440709603242c9404481c41d440600c6031607907010049008014034500c500b031001c1100c1c40501007200e2004108104800136080404030741c0e1813281440c3c0000d95103944a03a0b42d20010b041d03c031250b071015101c2d22482442d220100d0b40029240200c449964a0340d883c21a140e07140c03100e01c5909030b5820305110035000f00340709100400449010340c00340c140c80d58 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 160561654 1250 160560404 160560419
    0x9010b030d02010213080304031101050f2208011b0905042a0f1b020604050f040212090c03100b0913050307050106080318060c0705130204050411030f090a03080718 72
    0x4004075039100c0141e50100300704141c0707800a142d0720024030398180078524143c19030311921490081d00384d00605000f07000840100c2007181401b11a1720010554a24a0780c00e594102c4084101e02480740035580e60070103101318009101616500d50030402600c82c055030604d80fa05120140840b020300050703800400c082e0b103030710f110444120402c801345a40e81105034160b042c4040c2c1230b680d600044016003030f54550002c00680365507007107074250f80c3d04840d00c4154064881c0018040c2c4201c0140060242504013845108040020007a840c400120191003000e502d9400f2002181c4014002607800041e07400800c04000b84540c85518660040090700d28104268842c00e00392802988407600c25440029080f4120010000f076040030f6004842491a00d005030300704503501c00c202e02540d0720640030310300c00720b001104603812280180070140040c0840300481c0d8144405410403211900e00707280c40c10001d4112000440d034040304070f5258a40140503101c049023160601c40360746008100c080151404102c9d80c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 160562904 1250 160561654 160561663
    0x1401110619050c04080601030b0a06030f030f0f030e06010909030e0a23120c0f0316090f0b042003060406090e0604060c02070510110102070210091409011503020309010b03 75
    0x100d00103020140580c44035120403007110740090410343c06040030712080c03240d0f51000c0f401d9411281c000003181c0e0252103c101c000001c003407507400103010040c0f01900d5000c0541025600d280310100303445a2400441a60741641601d112400d42919500a90014806000c69a110000d900d01a24186800030483c20104100070b00c5038010304a00c4405561443d040b8080c588001c0c201035090301e040b600942c2494401e540d40400f45da5030347c0705510005080500d51000c000345a0801301450b00b80582c00d5881800c1ca000748070800c4164612418401c101203a407e050040c40c03034491801c104c1d4414200145039090042e000604800c0e40251108070001f14a1000e00482c00d0100001002c0c2a00c0c3c01c1529045044403e40c0d50300500b1340d04240b078200a47c0c0d454001007a2400181d0410556910075011708a0080c031803100020b41c0b020400c030300111a540d004c1000c0040c1d0b5008031800011040c0c0c1c604101c1c00d00800d1140c40c0c012032903401c00780702c50352082c0c0186400c4000d942c00810940c52450009082 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 160564154 1250 160562904 160562911
    0x225210c0f170111090108220602030c0a09080d14070c051e040e010c0806010c0c03060c0206070f02031e09041404060c0e0909030306010309080f0a02010603060501061814011106 78
    0x501042c01c040301c16440c080c410440010200140107141110740e10018002c110f00810a0b006244c1400501c2c0c002110148120b0701c03240e200704215680d203002003181d1102d0b0050300b0650001040c10f040072403c41000110801c00c504262140c030350584210001a02d5540060070440ba885c003190f0000815031202c0c803807100b14105c1c07450308208028607001071004503200d0412416080e0304095a803e001070700b10340740c950801c1d428a885245200c4c5400c22076202c0034158070052100c3e15100000708620b0f8041401c41c0140e41d956100c4030005048141240d1381d014612070a45001080c0346003280210303465004160610014201046403500c1000580c07542008403400d0f00c0054540e10020381c00b07036110900c2e01444030100d8040301141010300c40c540e5a80001407074181403540e620f049105110151064072081214030748215543c210001c3d0090180940d44811511345080400208609010b02004030b11041c24401c5a20a0b9162a0112604c0c051200f0911706010400810400001c01070048920 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 160565404 1250 160564154 160564169
    0x7050d06020f0c03120a1a0a09020a030b1305010303020607080708011512090b150613030f08040302100527010c02010f1101020f1b010b0303070f030e0a060225210c0f 73
    0x60310701074000d07805446405c034900c00307409421f10007075500e0b03560114068244c482c1141c0040c0c95000405054005241c044180c81d84a550340c60b9000d0764001130703004581038034442c0c0e0a40303a0075101d0301416034042506440c9100442c443c40014443d0344c0000b0031240c2180c0b1140760031001c04460f40c0340d2104544d40a0401e5804d40b048804100340c290740e8007414130040800341c442902c0d143d1190016041a2443c1c00b00030030040b246c8403c2d40c14420050151409540c005040c1109038450410251175a40904080c294483ca0586c4034046078241801015201c2e1060715002c0312050705a0044486e0018522960240100c84c00004030f01e031b8091010741044070711340350955642e600290150145c4451101001282d030f040c00003000b160788022054646440e803191035015241d240c3d02d070548403040518605034003c80b84400000b8080e1b800184121000645c00141180782e040d1400c0101e80d002074000c403104c0441c880451803407000c44d01c4007171021038010700201c81ea4945889080d40c00354480d500121 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 160566654 1250 160565404 160565437
    0xa08030a1107050d0303050606070206190e030703020d0807050a060203190e01050108190f02090a0516021c0f11030304120807050301030c2c091e07050d06020f0c03 72
    0x140094000d401c0c070055a28001c02080120b1500340000c411002901c0010101520390f0b0110700ea5072581c6081e1207243d40c3c000e00345926048a96501c8203070049d60314a40001429900c00403d0b40d05011510070156070f00901281254013290310740c1d80d442da1194801315060321130120b020f000309150b80b01950103148071030500c44074a42c0f9048001c094652661007010390303900d054010407030f40380c0000d410700060b0803462417036400d015241441c0d41c1010720340c0c001a400200708030400000880c03d0303010354070402490103139001c40b500c004000c0340d0300d00784100390b00e403a440b120031a42e018030300804181c45001514540bc641d291321880c0e2083c11038205403401c8806841e156081c204480d0042251780c0d020281d890000d05640c510348a840c002100d038032410b4600f02c406240300340b13009001d40180344859280359007005241000030b5807996070500c00044d0407030a9840c0031442c0100d0804550344c400c441c0020300c40d10945841d522460001e6101c90314589032038030100007040c1100c0003440a011280513584104 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 160567904 1250 160566654 160566667
    0x51201270501080c0405070203070b010803040e13030f180305010e0d080f100504090609050109030815010e0922020a0303120b091603050405251505030609071d0a0803 73
    0x515111410654021010341040018001c00b100012413200e080021100420143ca61100607421031040c200c0c05000031140e50300125640d1000802042110032040011600d50b8900c0f54580f08c8100d140b000070000f495400c14400304520420300f5891003600800c41182c410790380d589841c00c503100c005d000348058010400000d00150007645069000c01c13805081140c030f1034901d4152080c1c520742e008a274465941c4000d5401030003203030341c820030969620034003c2244102c81e040c042d019100c1110070f81c4402000c49840b50140d4880e0b009405280805400c855213a190010014140d01c034800c0091030441c804407144016958031200c090040d40280c40e10361402c90340c07040407001c2d902c6090719503000701404828004920b0540602007401e080c01e01e03000900d0340f81c914140b0f0411550800408680300e6000701900c8101c4914286c10440300c50110101545240200a89850104845070707070f40301c070500b400512003d01030006003419488100b4000c0c4424407050015850b178035250019949a80041501d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 160569154 1250 160567904 160567949
    0x31e09050106030506060d020108010b0d020f040b070606050a0b040902030a0905030a1101050901060e0a02070c0e2e05010818190c0e060a08071512020a080f0a05060d02090601051201 80
    0xd41d1b0020810350b80002690915000600001c40610544034030300300001e101c804d045050345c141e841032110008096655640c808803808581c2103018151480c6180207000a2580b50809400c822030b200ca0a5003402c0a00d00b0345010001e4000030088040182c9991010300003d00074001004140565100e030001030f20480051421203200621104140e03143ca5814048400311048031a8400303000c00001d84e0300c55281c640140c4681c560740c809a0740240c120300788030107803185290000b0752a20508540704600c022101400029410b4030603103000c140300380f01140307107680590b100c801142c1d1040126104c0e03801d06041700c41d020b1000901501c00c001125010b0007010071104030690040412112a0315090401d846592545450f202d002ea400e15050300f00c80c065402030f001042c20881c000003c54817010840c8000d4200c210488504a0104030b600015010420b01d20075203024034800340401d0801d20300340e802c1c0804800701904450521509000c2e14401240e41c0b00c44038003a01c181c103070b4045040d0114a6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 160570404 1250 160569154 160569163
    0x60a1a270907031e03030f05090d2304031e0b040803061008090c01030b151303170c0312040204060b0c0f071a0910051c05070905011e031e090501060305 67
    0x154038581c001c1d010400c0844e224904c103101810051002d6441c00c02c0900c0c0c158020a1044503001300035080008102413107501041d032074824001038850550900168520150300310201e4488a15013034180300c00c0c00828440e84e21000035440780c070041d85550a0356210610400350481d01298403910000070400b46080880003065150034904061085041c0306104903110007403503e41c181056a503000c2d10b00c0c0eaa559441051103104148519a0342c0c20041e500104140c549000a5841d24040340f07408101e00c000034222000280a040030b14140b90714040c070580b5082c80a0800d980c030036121031010420a407c0c4004100d41c00d40040145400340d0f0400005017040c503580e101a280401950000005031089402c4441705541250141000e5015500544003400765000300905180084006070f0203244030b90100d4081e070215100e03080065620300c01103e0425000c00c4641d200a40081510b441c14040c4d00100c800050740d0510410103000b00054104484494205660b940c0d104d000420900c0400d00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 160571654 1250 160570404 160570411
    0x160905010519050303030a091b0e09010506010c0807241b02070608070504050609030a06050c0d06050904031d0f03100f0b12030301050105070f0203031314040608060a1a27 75
    0x3002d50101490200001d840340030080a0b00c000301d0b00d4240d0801040f241a914011108a403e02c0c15256038881160000c9104101c0c0c01030741d15803a10002c11105c2d03008501c40804160b2141425141c03c0316566100b080310705098010146920510001c00c9408041c0a0b5040320440080c90521040f10414003e2030b0419942c02841404110414410783c00d50001c101c50070340c0c0b010748102c0c3d40ca0010002003443e0804401c0054109442e020a00007400384080044c5910b0122080c00d10189403180204140113000341c138000c003c40c5140320b0f0b1040c0300c0840d052801c02100000c0c4070005a40c002c00c0443e041200701d000644c0c0041e07071400102070041c0749120384180034105071142d4100040421300180d40c0c0c03106000702414880046441c6040080d0185083c030099400740030b8a8603a8030160040000880c980190b407074840071050b1485450a0601c1404110b8001400405650303e0b828880ca00501c01c02042c1c10b201d40c8000d00300341240d1241e021070250050004598501c001c0030318040190f500c07028 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 160572904 1250 160571654 160571689
    0x70605070203010f1104120305090607060534030e0109021315120210030915090b0a05011706012d0b030f0601021c180306180203010f060815091609050105 68
    0xb0140703078400750213404c5d2019564600d1120a460307d80d420261014061110901e0380283d00090340d40410400c0d800c0725014440c11403140c8498400c04911a14207080f80c0d1a410240311290741c001b41c414402c0d005070706c040802000004004501d90041280142030303258020030152581c901c1d262107681104840010441140b50070b1246002d9400100902184080f0008040d1669243d200b400320b1610b0220030900344203010803140c00c0390324041d0030082045034040c00151611000007000421300403035a0308504000c02419140e0708111180c2c3e508040c1000c1052102400b170240b4240c3c90718200c1c400080c1c051900c040c3c0d141e207400b08010b4a0580001c08003030441d080704404040004401280e00c1000c0c2d01c40c189827403400700003072454017008025070020705818149070102504400b605c5018480ca4020307070007403044400c200c20003003d880e59445080c130164410340c070003a403110354490000e0f0052604020f444121036400d442000700c09040c0c001c1000507680310010001441d0241e03040c04886200b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 160574154 1250 160572904 160572911
    0x203071d0109060c0f0305090319060606030513150e03120a0b0114120a0216080d0b0108100608040f02060403050d091a0d09230705040501050f0a03080a02030c070605070203010f 78
    0x901030010b01c1c500150000400703541200c20301d0001c04d03004002341c440160016080791414001142035800c95400d042040d5a0940303440808104144a802274900c26441c9140d00300041c20543c1e107048460a0454034910b55035601d404403804950140014a03c6001d8000c0404550501955810032101203440060500440c1c3d2640450010f0700e42c242c904000c80740d101c1c004142d90390001280a440b40515017101c2492921500c1304000c0500041e00100796098410006030b041e02005480310b200617030701c02039104100c490030801c40344118940d6501c98442c0302080d40e1460581c1c0400d066401541048601d500802d0f0100000d5912980600c020310410708100100c00320928174010034070132804201441ca03140c0d25000c00f844091081010780d01060070004d0810f1400191b4241ca502582c000e043c031540c1030000000e4280380080643d40001c0000340342d031080c0c03880d503070324221994096400f680c00d40c0824420802d29003001c0c0400c00003020745403180c60390382c6414810903003110340c80e902c241c3d2003030315 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 160575404 1250 160574154 160574159
    0x140306090a0b040201050a0306030c030804170606030c040902040207020a03050a121704110105070506151201020c15071b0303020306132003180f010c090f0602120f0405040203071d0109 81
    0x840c40e40d81c0c0c3c11903020b0900707556075100703000110007800c0c6940026181008140c40001042102d6000704110b82c0c01401d414a05183c0c1e009040e123641c4240c0300d1039815444a4040c0380e09142c00e5000c0000180f00401c018a003110682c0840e09821940c1d1064480c1d4000c00000b10030700910585102c141c4107140381075908652403509808ad5603101910241010300d495043c00300d10b900035411945d031127802c441156180c0c5000d41c01d503071025030f80c0c0350304038052019015900000f881c14000e40e81980c0e1500d015044513035a0740a1501403050041401702000500e1603c00890b140b80706210104500035a800740e0703a441c061090001218820400042e0986020320116041d95944040c0c4114064000c9250750303500c41c1c0e01e40c2000e60403014811400c50080469156640105501400d0840e2560b112201d5495940d000c1c10f1001c81d80b0301c1000003517008504600005800003006264005890f171541d410142c442c408201241c100300c0f40400420074140300042400580c07082000c101c902480d01c0c110590 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 160576654 1250 160575404 160575413
    0x3040b0109020906041e050109050d03090326040306050402010315122406090b03120a1706011e050d1b0905040207020a0918120e090c07050109020a140306090a 70
    0x14450440710681c04507803100540e9801c001c9030024048200e01e0354036800c0c41c182c01d01079034506104a40c082054101d000800d4284401c00c400c2994158854540840c515110a400500040381088210307050983c0c15511003800405030010718011a00095039113420b03c0050112042c14055440e18040d0030390411001c03020030074000050f075100c0207005a54510301002c000b035040e2040b605491904004022405010b1948400c090050840803034690b0081d0340001c00061141002340000034801a001c10202000241100e4000d50189440746403010096405078a200805110800003403000940305415080d034000c02d80d130040300c82c0713101850b038813003a1004c0c000110034415940100c1d00800e4101c25503a036610316800801c680c003405c0c4200d200310002c2c1c50b045152500121030800d000742010100341d104514040e8400c0e0040c15840c500c2e100c0c50302502c03054014a0088981e507481307030003010060301e40032403c10050140b11a560305400d020300402d410170000502000c402e90040d900b400116 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 160577904 1250 160576654 160576673
    0x5030105060f1c0513150903050a1805030a0b07030b010e010203030a0f06030501050f0702120c0606010809010e120c12030907030b10090204060c020a06080601140a03180c1403030304 80
    0xd5600c2c040c140c2d440c0f01040e071103100c100120380e401200c549000108541820300070924428070f8441c80441e41c080b400c61401d9011284112405400910b01f07220094a5a000d07602c07100c0d54150902e40018105d0342c0e080002e00e02014142c0c1150344c40000ca0920070b41d84d8060184202008003402c040d0091000000000c0da2400020704090405848520084d03901c0003a91003403000e036400c08000c1c03100d890001f036140c00300801a180c00005116800c051041c0041c941d056a807009449405002c0545031100110750040d8050040b480075544c1d000d8140880e041000316003002642201416150200b4400b400e080052002840d003080c01c0400401441207404184036040e030fa4082d41e003d040380c844504155a0808540049402500c00940894016003082046000910845028041c651908000c9501110a0700c81c24042001c031581c01080c410307100d010b1f0111012524000941d086020256100c1c000070340420341ea8110710036001e014840e844807071201c610030150700079841d50402d40d60b1300f80039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 160579154 1250 160577904 160577917
    0x615031211060c0f0403020411180d0f02010f03020d02071b150909050a1805030418090f0b0901020c070e0901050108010c08070e13020414030d08010617060409141c0503010506 77
    0x40200010341e08880c48085045d500599000b40040200c81c148078070081c410780c0a2442610041d43c0307841541080e1805d07001d05455203038084921041c41079154015600100c1340f0341407000f4150288074183c01502144007030502c40c3d01170403115907184201c009100764060b0390b4100300c03034214413100d250680d2500b10b040b44040302e8a1103000101603507192085002800b80403000e201000c10b9503200c0051000c00070191050b5100342c1d000c10401b03055124220203c40c40d0801c0105000d06405a5070302007900c2540e5280e000040d000090f00e810a25250542082d080340c0107007007140c00f600d040c0101004244240e501410b003c100801240c042c41c02c0c05401c1c4d100050041e810010303e28080660fa407200d9051942980403840190b441c0c98881e01c0402c00c000310503440c40d0081c80b400b40d5070b15805200e00b88190488440d602d41c043e03c00000140c40300c60001c0100095000b5440f41407e000280300310747e4000410141002815007400400f01c01c00884150450340c1007049070500050100c3c1e66080c0031280c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 160580404 1250 160579154 160579171
    0x303061c051c020601090b03010b0d0201030b01030f060f090f151203030e03030a02031806040b061c05060405030309070920030405010e0f030901030c0c0b0112030903061503121106 79
    0x5104540350580c584071180c501c1103012401142c2c1c0080c442d80005519050b10320b0380c00706100407030031481414200ca90443c0d266500070200d40010303015502030303800340098000604d00822211140000c85045e03c000350f00c0311000c140074020401c0942c10f580702d0114004c520b0304080c01004111141111142964001c0c000044071303a4007402d0826000e0380c0542c0c040d0208200752620f070b1501c0001c240094200b1221143c0402e40703490300780402c560118000d40300c1c5901c03141e00e000c50f85901c8103220340f447c07000712300e85d441d1140e440d0018003145d800c1200c103114a118800840d541c1c42d00c152002d090044542c0180706060031f100d00000d48241260100341c500c0300c2000d825803282d03254204140908442003415800307004a10002041540110040840a0083e01d0500804507001c1c42103500981402c00039000261400c010711400286001000d1650b029191204210303032241c490078211050380100c076044102c080020009c2014451b5244611400c40c01c203210508110300081c0d0322550020074521 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 160581654 1250 160580404 160580449
    0x4030503030c091305091b12150a0f0504080403140609030703030207020d0b040f03080115080a0b062109071211090907080d09090b030303060d0b060105070602071a010503030306 78
    0xc009441e95054103c203070032004d5050226042a9200584400159110454003100700380ca0a13041d0805102c0e18400b01c400c0c90041c6400b00381480b01c1d8200c0d40016140c2c942c01d03078aa59040e04803840301c1c014203000b103000e40038280d070311031861a12800041080d01080100c8d00700c1410800030007800300541d015160981409030382d4013014400071301e0380700c0c0700040200044d41d020b00340014007682c0c425202400303109803035140050340c89401240e400405004180001000030b40040c2d5030402c150400f01c130340400581074904150002d52a01b44403034000e5800d0030210101810480ca6880810542c0024200c039074105504442503140c501618a111a50702c2c002d844c0c280200c1c048120412842006100803020b4070405611003000034020030885c8104c580607828040105101e24020045034003601d00101503c0b66038400341e0740e21404901c028805070510805111981c00300d14180020500103200d07042e0051030000d241e030b41c58150003042e00000d0080d4003e00400196454011098918504100794030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 160582904 1250 160581654 160581667
    0x100b0d0b1f020c01030c0318020111031312050d030209090708060a030803090309031501060c030810090f0209270c0c010207020d050c0a080637060611100204030503030c 74
    0x1c1c5480d030035031015040099540c8801e1445503012450341591507007668144945070a000003101600c1018000111b0849680a008015806400510130303125402058a003000f2061008219145c100d600420036062a080c80c203040144c180030701200b0480c182411402c0034040c0c80850000d2400a01940c02d001014002c105144c1d13841700044001c0d640000d800b552444c10003481510394200100e202e004e0f10070498402c800c81e000240c040e041e02c03005d86e58009980c401d80c42c00c50b4110009009942d0162019602041c94051400f444c01d40a0030f50002590b901d095000b84a40c0300008240700d000d001110401000300300925040d90b0b00000c4500309103461b80d00030880580244904400217500c0544503a04208100d030202c0c40c075080d61822900440c006680fa0b080315110601292403052441101600c0c02da4000100352103031403030b17111008503c42e48242d8650701080781e281d40c001344040b511405424800c0001002000310441c00300c00190304291866441a075640405491912001c1380400d60 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 160584154 1250 160582904 160582909
    0x2160e070c1b080309041a0d03030203100e07020601030c06030b0a030213060f090e01060f0315022104030201090b13031b060b061204022b0f020f0301150905100b0d0b 73
    0x107030804503280858041c00b1950f690421642d80d030180e050030740035034101243c424180044205200760f11802a007840a0b51545a50840c000c0d80010400f28a6641001000ca85110951403031407042500340c000f8501c80d415402c101c03042da04d6a611500415040914920150b16115100b000b12581602c06040c01800e820040020f40355641051140b4008408005034040180e007001d4819480b1600800c0503540b58100d01034110a140000340034240a104086c103284050b84c0203101401100c0050640d5403100d19102c0074000040e41d003540107031344440302031090001c2940c0c1c26800c0302c400050641d540b0320940c0e010340300741d480c00e41130300a42c3d020310750301c20601046800080340c444008100eaa40d81c1441c00d08007008881c00d6a00382d01031180107149014428584180290b054601c00441202c0384885d0390f107813224001030700c0032a044880c440e41c3c1c0d40d05850902901204451210f681201c990a00040008443c40102104140030b02200200001c05000701102c041d06115500440e0b416500f001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 160585404 1250 160584154 160584173
    0x90a1101030e01020d020d0606050c19060b150702040605010807090521030c030703080c0a1d01020106080f0102090405093702130203070206061504060f0e03010f0c02160e070c 77
    0xc0c1c031580e42d4000506103105c0341c80b540c001c04543e80c0d404010030a130360315144119058000d2079a44601c0e544030b002c51015a00048000209881c4078480c08140d45c0d0040d40801c0301d0b4004000e48450040000c1028400c5191500031071019140030b20300004036217841100241210454030a045c040ca01012041d411510089040030100000c107048075030781c6c100100102d540b984402001e500062a440110f14492194011105545015910507111070560440703800c84035280b0308640d042d59620000000c00d00b0381840f0703902d0000c600308001a1612201c03814441500c800a08026864100c0048080f06020322180403080704112880047c007489c07110102c030315800800501079403003031480c900d00c09100401d40003148107984aa084e0380c416140c0c2801e0140c6402081a0880800b00a00c414042e0300e108020007240c0c95100e15008a00c1c00c0040086800c6484140854245540760440c04135025010402c118031307030b04e04441d440720b03061424000c1a01408042c0c820b40402103800c0000003403180d00702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 160586654 1250 160585404 160585421
    0x1050904090606031a01060f050c0a06180606091d060105060a030203060d0f0c0311030d020a02060d1104030606210818060720030c0406030b0f0c07050a12031103090a110103 76
    0x5545c40c0c01c544d20005c0004e058109101d480d00048034032085c0d5240521840c2a10b4492030340600400341c482c0c8a6403031001900100750000c0101c02130b004000080b4825005400040070110000154604102c04150802c02500d4820302290310030801000b40c0c1d280c2d07030700301c512500c0b40e4540141c032900c0e090002144c0728000e20018141c01280c09044040c410203000c0641103a100b114040e0303010806c10145500c5542d20481140560020f203045809814444000d003c24101503800040c01880e10700300700d040d034006030015108c10781e0701c100c24070a030030451800c940e2403900700303420712150f281659070501c0030b100d500100814545e4a08a184150b29514140c42e00c9691141202070a80c03d21404a59603208207528144030348904075101d81c003404c00d84508001e80781c1100342c00a29030740780e40c3c40d102c11020140907001a03900400150000c204144000d406203482243c0c600c0002c0c5042c04000c09556540e045150004010401d006400d034001440e0500603034045030800c086904100113038000e0101c074 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 160587904 1250 160586654 160586663
    0x3030103020f06070b0403020c1323071803080d0b0102150c0a17090105090607050901091a040906031a010506040b0901030e011506020106030314040303080601140c03070b180604020105090409060603 87
    0x20814041015008282554014020781e504040304207030210000c2030b542f81c8004c01c800038000307000c4583c840c0480102c49620824034209840c9155004480c0e01c0c4044040d402a02c0d241c1c80817804450090300c030700030110045000d00c02000300c1c468411070609503907000ba06980f0001d2000800300c40540c00345800c27914003086a9100001d0b03141244819010b89400ca807600100e0103810300151010340540c06440248078180d5403c6a03050411010404948000fa9a205e907483c0038000000c01500034001d0201440c416481303201c02288059502039044010b8010911464050206000861042e011f0302c0342e04d5000d1a0118418090380360b4680104044884410904041523020524a405411100840f4400e580d016581c2c00c84c2c074100c502e00c0c003c600004000580320004580c03990311958100550301400c403009403802407240383c41480d5500901d4100d8402942d0001c0094840d00307205101c0c03150f06518050161490140e00081442c070441040300d2040351703504044030500610340e000c000a150300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 160589154 1250 160587904 160587923
    0x1e06180302090a0204092315011106011203020d090302010c020d0305130b04050319110411040f06090608010914040605130f050705121506101106071e020d0203030103020f0607 77
    0x784101e034043e600c43d0081354106810011f0803140401002c1d8922a0754020f00c0b4403000d10386802030958a010482e0740801e041041e994450000075806008403402066032040c8a00d04034920b14010382451840c01c4c2040c1405032a0f0405c0001d40d8008205078a134660444000d8500b40451905680034051460705910400d028a8003180001c4e80c40000d00c10354104808903802c807294451070300c0c0605d01600c40200428211206040641881e4012136400195800d8050409440d0b4250422601c1c280d409540010031006042000707507000041c0c68050214000140003840d00416110a200000b8200901940c0d5800000e010141150000c808145e8416a128110245ea0424550fa501140100782c0700751041340300c0704040c050000d1003183d00003414a0b1070010360f961904003c600d038a521585c406008142c3d00010040c0e000b4800c41d442200740351154000846098822421451500305140540d0710070b503100c105e141e40001c00d607811a903041f00c4500c546a0390402107480b500a080008184210 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 160590404 1250 160589154 160589161
    0x1120212090109020a080705060d0e0a080708031b0a05070b09030d0e0705090f0412030f09080d0c110f100e0f06070c1e0f0303020d0b12070503071e0618030209 70
    0x1010f40081ca503180c02180d00300c092646802c2c100f41c03100191311136998400c0007000f1007503107403c4035000b259411028401340c3d41e9032185512140410b40c0310740c500703c03050f140000030442d02c000d035440c032885100d201d1903541341826031040d0301070814403ca040182285410500090105804004480c00c0410340c01c018007451002290840e030b104403a000d40340c411000c41d00000c200d800c40b001000c0c85642c0000c01d02c1c40d0301030220340030703402006100c061000c5162501600404200c059000700b900e140168400605802d00c42c900500460740c850701400076400c5150000c046500000703050202d0445401c2c00908503844e92200e51030602c0000314800036008101c1005429034004480501050280b25408404030352010381224000101c03200800341c090001d41040030038440c2e409444007510b251030000700480c0160028045000000b4010390310351050400344945e040500c80324004000340e69449085c0c0850307080c648520b0f00303035000740c50800100c0c8201c0c119000100c1521401180c000c2c09601c03035403c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 160591654 1250 160590404 160590421
    0x16080304140303070201020309120709110a080601031e0b18091f020405030303070e041805070810090b01050f060708040909030e030c0d0204110f03151009030506040201120212 77
    0x3041482581e8500800c100c149140382404021035401d554143c0c0903500d00008901000f0703c1035943c0b0400c0903648038010021688414501c24000001110600c040d20340790300e02c4c0e00514040c0010581d0341010b007420120208521812030080403070b00a46808501c0088001c0030034100701c81d03610784030201c4000c1800c0c42a00788000c1800307852001004074010319040c0d01211030041e80f055100d0f054140d40300700000381640e071142d000f00c8800c9400900101d404250016800d035505210082650590061642080080010130004d00f810070300e0310341407140090b142c686c4040203405100e028014448034034014101d03512001202c08403039100c102940c41c0c41d101d080210007420000e4044000c40e00c0405102c0b102d180c00034809404010080004604114039400d0002500981e01e64012554050005003a0b4900d00b401444c400c054007111442c5c0c07030342c030354082111051101d240035092003901c003028000f2401c00b1490503446502800e1a01c0425001c0c00140020b11808071030300c000e201a07805222820 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 160592904 1250 160591654 160591657
    0x110708070b15100203041412030a020f0d03060e0f1b18010206070504030510091b030602030a0f060506030a020703051207021c021c0c060b09100312020303060f060705160803 76
    0x8042c101415a210108581031000c102160142e050150340140001c1040d408211048000000d01030708440d00416500b01c6c09282d81c1014682e20056000030303a5560b2413001c02c02413001c113984c0074070701801507a203401420b450181c1c003e00101c0c180681c220000e5450102c0000a40c000e6000c20b890640d2401c3c41c0305400c05490740b010501c1d0050140c203022410302842001628182c980001c05000700c80c0f42c11120794020101a2800c5032141180b456038000c0e203400c50810001503000d01000369030380c68102e40c9041140c0414041c01c80c3d0306d11f4190248a66201c4000f542d0b44110f118800607518102c40c00c042d1924003401c0b102148151001080008082c2c1c041400101d4030000e021b03126001c440c108080e038172181d44500d10180f050344c0c420a002000d101d0312842e41c01c0d03402a4000103042c0304900100700c0c5044129076150a1201841c001c004100351004c2c007155180c0a480994203600305500052040528007010612925004c00c900c13045c0b2205015100318026521381c40c0c110569513208445c1ca9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 160594154 1250 160592904 160592911
    0x1227120d020c1e09070c020406080708060a092103090615090506180c070c0e01060c030f0203040312050c100608060601030b0103140105061e0a021507030c090504110708070b 76
    0x180602c10996016040200d03c100046007440c03100003a510300e00080c0420071900600320410042c3c0200b400000d84c0383d91040401400c1d030300d00904600c0d81402070681c41e2507006059034803034515200138100414a0025901502030b10092409034a52a048045000d000c6000700503066500e014443d09180b00ca05030240c1c1102c40d070755002e005a81d10903041108060072800e12140303207540100040c50088014008000491041d816030704d4898907000004c044030f20903003008d804a52186598014990000c0e000b06d8100750500c004c41c074140c115580e0758403018080d0041d500f0701001041940d01d0540c10f00460080718000d540401c0100c0d41d44203090356828007601c002d40132a01d428882c90507940f10f800751041d05140800c080540783d280c102801341c0303540070b10003c407040035551030707111310554a00005180d80c444582c0104404071090001050148003d401c2c0400d040c13800c1544850290855581411a00d0460b00081c0c04012400514041d105030f040c003c10500c40090392408203d91446000d00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 160595404 1250 160594154 160594157
    0x512150612010f3309020901020a0803090a050609060c0a030902130e010903120b03030301211407050901060305060108130c080d090801051b03040b0703140106030c020d021227120d 79
    0x210000000c92240142c1004c0c19000055120240c14480c1c5030241c3c008100c4904103204640d00341c245a15441c040f5003083d105118160001c5481c80300b44401000010b40002901014101d41d0620441000c401d00c00c410a140a02d0f45801128040d0358a080d0f504c115a034000304248206200e803005035000300400081200443c104008081e03020706107200b001484000540110f01c2e40e405c00d103c280c0a0b840e10400a100c075021015202c000a5241201c003006503c0400100209420a0100241c21005802c88030401d0301c7e18041005a81c0d01c00c25454000c10030402140546010b42811903075071a5540140f040b41c80340c82480c3c245617034092040000c5811184c02000302e41c8803404146060004400d01c2d008640301440402d010503440154550860720f18240001e00404683c001008150240d03c00b6011030b644984003a4016010b019024201c030051014100c0d030103000300c0799000307400b851034440c1d0310f000c1612680c24100c010200096004800508401890840107d03055071303200c20941d0301c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 160596654 1250 160595404 160595441
    0x60609010f050a09050406200c100203060a060c0510050921030106141c0504060b031c020304090915181205180d0623100512150612010f 60
    0x112108112940780c10707a03000805080c0784501c1c10542002800014006036925a5607401d8982c24001d28603224542802008095417144c20b481401400c00b8940c502c20081c0c1801041080320b10340d1410070210a603251414064013052042c24003a141000e912514450986420188040800c00103030600007a07002d0105c603002c05140322820f00c45400207208520101d00034800202c07458601c100a0007040c540503610011385c014440a420943d03130103640c107980b950f690b020103a0041c1401e10041300c040c45200e40074180c104542e08020758910030751054402040d40c91200d034040100c1d822880c5080181c0c100306100d0742c43d518422041180c2c24a20456043c4003548044640a000e041500c8420101c0c82c5d2104070119400c040c002c250401c21411144160384440040c01210043d40070350120496071600038503888e010048840140700750700300c1e51196021841450300c1c560b00042c0000c254000c13440210240c1c0f82c21000c03d0100e480850304010355400c00341001d64030252584881c04000701d410815 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 160597904 1250 160596654 160596659
    0x9030d0305061003060b040b0307050c2a0d0506041707060908040602012d0b011101090c030204060603060b34030c050d0c050c041e020c03030105030606121e031b06060901 75
    0x6400300c405506c20240000c0341400100003448901003d903921a4003428190b140c40c55884070107042900384088081e03540c1110580e0140490071640c80f107020101554414025000da864141c2c0d10343c0001c100410010200c00c0c8080c11034401c40581e421154400410300141205107445080e070340090007090010340c80e181744100304441d2250f00b40a0301c0d100402c405150314542d05074102030200719040605200d02c8580c00507030590309101e00c50116018a91000b2054103500c10807040d1041a4007003010503051030341c140591180e2004841208140301c20750100065440340048a215804081d0006404903ca81006140e00241300c845418415004e6031000f40200000391070b1444160809030081c0d2200c1643c05060906902101300a5046a101040c4002141150701a030340a051248000d40002c0b0042105040070880c40343c00140444031110705107450642180d2301e850b005600481c1c9000c0d0380920340b00440038000c0b0b5803407591000901c0f00100c040c80516941c0c6006030b6080c0e0081001c04d000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 160599154 1250 160597904 160597907
    0x609060103020d0f020a030c090213091109040902130608030a0e03060f0105100e03120703030b0d020f1003060308270111030a050c0c0d05011b17010b030405010209030d03050610 78
    0x5080c1666401807103d080c200b080d448012480600c034008a030080e01c140d0f400300114418400c41c0b4020603400302e001d6611100c04c0f100f074240c510903600c030720292400e040030100302c225803006a135038a40c0305407000201e03d01c00307000050043c1151f61002a500d840c1c0b4038003040041011000300112103c98840c0180b00c484074043c1907a84500702c480003005038107074005000300e02d0014450144c81d6120315021110100440009040032088008040c07120400541c0e4820140c0500178446a440f00f258114a40083c94011a80c11498400d40301d208000c001c404001c07030f23800b030342c440005580c009100b2921024038151a8009441c10b6400b046907280c88c1c00603035080c0d881400d8210b0768180f0700000d141450341220090f520340d00101e07035560090044111100e4603071101503222800501810002c201c002da101524552840c1d40c49160080015012008000781c6110bc03180d4119011800d40d19a0383c2d8031410030900a0040078003a6a05014003200200d00c40ea060300813070b008083c215140f03175400321590340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 160600404 1250 160599154 160599163
    0x1b0803040612050601020f1c11120304170c0706030501030b010e0402030c09060f1305071107031e0303061706090d050903060f0709080a05011a01030606080f04030e10020c030609 78
    0x900c0d00046428889004102d401d40200c0c2d08800180110340e0f001030f54481c2d09050602440c00ba40410403200b20050f9a5a841450203040f400004040c001e5120b800400ca4001e110051000d03222200701c01582c0e48040300e01046a0301c4006810564110680354400100604028070060301c84205450000c0749220080c07140c10301032a4010700a20001880d103091065500c001040303180e019540c442c881e001500d500322143e403c1ca00c5004001401e284c0800094103e948982c80910342d50301c29402403000078140d40a03107803258214901001020464139048000d003006801040440408600e0b03800d022000241c09401906000c00b9030700da1500905084500e406441012503040c0e0012000c1500c480c915444140c20420b249082084c1d01e07140c032807403407900d00d070402c0454450b0340d601740780d0314520081150868000c80034a42482003a00d0041c00500a200262032116142440340c0031504050050032103902c003680103091f8130800740032001d029498450b2484040c2c0a40625400034584043c00314 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 160601654 1250 160600404 160600409
    0x31e12080c0307080a0609110712090303090612061a0903121e0306040b10170c03060907080702100c090302010e062508070501090b150901060f0e0307030f1b080304 72
    0x4841c2180c3c1da0603000c580c407200242c0000c0029554a9000c0352100c060300401a04120b06a030740d698400f0710346040c44500962400400c20010340700d10500000307500090b4041102c4051a20030400044410000b00410065120f04100c0c0341c2e039055100c0b4582c00c03c002c2c1103882c000301c0c140c50089401e11030807103043c030641c8034407504240702d40c04e0304600712469000b0b140c01c00380260000415082c205d0100b4030342c01100c0400d40104102ca80840c803e4031041d801e2980c48807000c000c00341541407200200d4007540001e4142000d0204042c00510303603510070800d044c2d01c1403054070140201c42c52402c000d00844403c0c04142c1c002603030369444110317034104401161312082c2e80410780c46401d80a484c0310521005940030803a01411b040044402181d400d025425000d409111240d649040402603072401c11a8a500e041c06600708100400071240c01c801003582608807410300840000417413000905100744c070b0304010295984012268140440c480c0720710708a01d000079003d004036441e0204030b9528025403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 160602904 1250 160601654 160601671
    0xd02060c0a120e0102221401020a0f050a15050709050405100504020a1716030501120b07030b0a0b07060e010518060105130902040f0e01050604020c12090109031e1208 73
    0xc01c6020314280c80b0b01c200c40c5090841200008480c200c0c01c5850303003079034045410000c401c034050300300d034101c0819006117000800801c0003084c40c10006c180040d4503007503500720103032940c02c40071407400c1446000c4c0302503d01c9961000c0c0c40c0c203000c140409020001e1030203885000003d16049004a894205407107014000c03000018070910040ca02006c0001a5200c0290350040040c0ca12460001d134401c2c000140c0181071100c400000700404040007070407940140d100c407805529286102c0c0c04500c100d03100703c1d041900782c80c0c045814048503011840912103948440d810440005030301040c0400d550045a400845000902c00c1752500c0b160300074443e0f6040c0710000709400820042055107400c01c507041e06810102004501d158554002400320ba14100441c902146c0340c03400c042c3c0d01c0d1001e20403564072020403902182820012694133540308100501c0054050000034031a01a0b030050420000442e44074011261403003404a9045c0700c0010080204c03604c60b1908000f100c6607000348207541c440c0040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 160604154 1250 160602904 160602907
    0x906070e030d20151602010b010507200109080a0c03050f0c09190609183c060207050105011d01060f0509060904090c0909030e030d08190f060f080d02060c 68
    0x1d6941001401051400c040f24815000100c1c215203280c2d003030b07070300c0380c0300c031240c000841400e52001034292441c040300d55040160401201c40002c1036115195640c8140959401d08a03000000680309524941c200d50114416803220303100b00000c88054000750b0f4031841c2902c0150380d41080c0d40c3d40c0c5000d10084d0720781c004102c90004442c4000785007084068400305001140f9669688031210417a01c0d4004030044000c0c40140c031008bc00580c003481c4c901c01240b0819040640d400c02e96a00011280c0d01000300341c2d1079020031500501c9078a4050300c092a800c14020410b6581d40c17007054066000100d6002100d81c0114000940309004400c500d000300d0340794541070b240501c110304102c1c0ba40d2102401d035501035038912540000c40d40c03002d098005009a0040010541d00a04024142c40c2c20404114480ea11440d0592406036003c1e40080e0003040c4200910f265000c050380140203480b82007512207029140500004090030b034170440004564402b4141c03001d001e880401240c880804850b0010700410 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 160605404 1250 160604154 160604177
    0x9022d070b070c02090a0905011a0a050d03090b120906010e09030714030c010c0908070f050a0302060307050d090b06090a02070309031202070308040902031006020d0f0302090609090906070e030d 85
    0x4001d04100c0d4461803a16048504003465070014585440c252450518540e84410385070400c0402d205008001c0c0801c1c100c00c0c2d0444905001a561340c0140c02898000d0083c4490f0108140c000e2070001e0140c900d004800d40c0301c400c070014031f80076020100e448490900c1000000070360502411169400f902069019520700a907079110780744804009102c00c00355120400a4a60040084c894011440040d03a030b940c7c001b510f0516442d00e001e660b500500300383c1c0c0c404802000301d0780d1201d1103082141c0c1c0c146c075820780302e0399040c105543d10301426021542c880c0c1000700003010080721004a03481004c0c112509142902c0750880b0074102d000f00c00b4014085040000140003054012172401a00801d0b03204803111580c0303960b1105881e030010762019a00c1030b004014020058000d1130200090041c9100402c01007100c800010800c0d01d070284000145070780001c02100e1602d840033141c02c1044064180b500303608040098a80c1d4020450301900018166802005546000b18201c2c0d060182542c841c586001c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 160606654 1250 160605404 160605413
    0x2210417030709050d0507080c010504180507030902060a0504030218060f0d06021b01050f09010507020718020d141e10030204050901020403021906020f030909041101120609022d07 79
    0x28005007640381801076030040044d81e17944000c900f43c0160710810190450b00c1c038102c8200e16012408060034140f000501040c0f2580c2d0000400700e10381d210002d008070b25134940207015402482c180f503000e504038000140d02500340d90408001c2045134400c1e144d8101c01303104035207403540811003a9603072035001e40200e91090103441c1c154110071082d03015040052030a080c2040d8050550002c400032089651288100070603888441000c0368807140880007408580340c0110300944402241c000c442a4920501d0145611091641602c211640c44801002000305002084412a0b011103480803222407051a52080c00304241c001c0c2d019500da4001b584010f811542080050706008242001c0d41d0746c00e10000001d43e454004181031a42a58007007240642072800080c1000e0b44480d6001e807a0340100300c0f00d01c0580714810381755070058000380048140004140100c0d1940300d80c400308050701d42090310110341800d40758024041d60b14000307401c2c903a41034141ca150a04150760001c1c5054114148540c40c00305 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 160607904 1250 160606654 160606657
    0x30115090b1801140301050c0a0203030103020118030f140c03070e0a0f0905150712090f0305030a14010f0f0603330807030809010f020a050606100311070602210417 72
    0x1420020400400d1001d05010034103440c0090f401401040f80f401390b0020b8070305081c4a029000b90303100d406249003c80000d0081e680340300c1880001c3c10005084180760300304200c2000358000c0d40e4040c409040c0e41d50241007a044011403000810303818020144182c900d071038001610b400311214078a03050810307560200403070020040c1c41c540000143d00d80a08100140c800c3c043c003200700000000400c000d08040c10003c090003600c48668042924200d604004280321048108449516140041da81c0c2d0b14030030303004060603103090302010180341c070300021440c2e441001d030460036108103000e2041100c1e5611002c50a84040b1085000c075840203020f003a4004058030201460311030f0700d070a11034203203aa130020145002042c0d4402d5813498008038581801e0740c0d0140142c0f150103400c1c0f0082c40602d6040e202c0c00e03101d00c4060701c490311a0012038651141240a42c00c2602100d4600c4000307030b140c000381d040241c060f520142990243c01c0701488031340703c10f404c1c00c0110b0340500c0e003081003401440d81d1010101c0c100d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 160609154 1250 160607904 160607921
    0x7030c0e0603092518140609011d0606160c0602190c1701020408030703030506090606180d0c08011104080d11060a20040303050705060604020a12021e0f030906010503011509 76
    0x881e45001e2002c43ca0700c0c0076844c8116524088000002c1b00e0480304001343c000c043c054101303442401c100004102c264816611001007850090350000c258031403074005546441040a1030011028001230b4800b40201068194101d80958090341e1085244020080b80c183c041440181f0101c1500390a00c40e83c1c0681000d080d4035008603000526181e103481007030307240d900802012400661900b080260506002001581100081c0d443d03d00300b0100080140c2400d1485070200d008800326070a007030a00c9800180d0304010810309008001c0005444001909680300e030040d56014402c08524240d81441a02000407040d482400b41000b5150710b00028050281c0001415049910200c3c0c01d0010000d03c0c001c00003540310b61543c42d0b40300300e185415805c0c024000c201c284903610603c0580d0099810200707400c0a0500840e0046c2d03680d0020034150f00703040d60701f03014031144c0c40046032a1004250020096026401c03c030300b190400d03a603900c101402d0b0348e42014859211050341600308100c00d6941c225001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 160610404 1250 160609154 160609213
    0x10807080c12100e190c0c150203060f0402130302030c0901080d050c0304030804060504080c0906010f11030f1819030c0512010b04050c0a09050109030f0b0601020708010507030c0e060309 82
    0x10f616542c2e071510a5030032040e18400180d20380d1031030b550300c8840755100300c003080300d56070921054161107503c0d076105070ba0b01405142d958580010000e02a0741d510741e1107084001c0d00400443d00d03002c1141103a0780418507400228002c1c4600c84d243e0b401d502c1d2521255048030390610041c9044d418000049074107410114130407001d40700c10310000c40003c14402c091300c054185035560360744440c038228100c0d20f00000109407500500c8031005200f200c0e40e000c0b980100c1100207080c4021000100e01d003107440c51152001c0700040850105030801710045018072280f02940c12540c00308132a22081000407440c0c001d110081141c910b04008005030306044050030008400c06000040740603411003c03809541084840d14146a030011301c00d02c08640100042024000a2814110890a580d00d410310804004005012450340d030340010302581c82084800050f04080d40280014208408081d020708042641e09022810084801e0581c4c00c000003500e100d62044401440700c200800e0341554091035011070a039 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 160611510 1106 160610404 160610431
    0x90504020c0d08060105040f12030e03030301120314040504151502070f03060b12031b0606100e0907020c0a0b03011e080706050307021501030b06010807080c12 70
    0x1604040c0c0f0308080d41c40da1100d1005803400d0007a0b901021070f231500f15101040311a032008003007035040c2c0b01c1e440e0080030311011810183c49010034007601d004104002c00d0480800c1c0310f00f034203030582c450032001113142582710400315040e12040901942000405001009481c680d01c0c030804492495101600e1030790300b006a02151761409105c060319040d290701001041c1e507264000c0c11400f040c0030303044960300c00c22018440c402c130289510082c01380c01800b0004c0d40f2400c20841071000703010b40e5a5110322061800040059141c4081c04007411481803484034a10340c0c4640c5004000b8100440c21141c580d0301d4a4501d1010031400b02883c0c03045021061b04100c4200b000502c4d005403501130400315180c0d503c0d400e0807450300701c03c000c80da219045070308000070501c603a600402d03004010070381c1c40d4003484c0c0c0ca441060315a00020303500a0164282000419a0a078800707000d16000b6002d1074a44 = true := by decide +kernel

theorem cover : BRFrame.Cov 160431654 160611510 := by
  have h0 := BRFrame.cov_init 160431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 160431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 160431654 ≤ n) (h2 : n < 160611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
