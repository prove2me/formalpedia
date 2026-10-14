-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0797
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:51:30.453384+00:00
-- url     : https://prove2.me/submissions/94fe0f21-2cb6-4e2e-9387-e35cacdf9eaa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 143165467 ≤ n < 143345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 143166717 1250 143165467 143165507
    0x8011a0406121112040c0501031103040c05040e10110304060e0328020f0a060603050705011b03050702040b060a030608011a2119050709060b0f071205040b0409020c060a0207020105040b0a 82
    0xba150a0a00030f00305a4491f15010919007a009a1000020000ca81c030503034204240b88503081c80d1109120040c0944c81c084000c0740600c1e60302080d0030401e4010301021801d58100759442342005d04000044079094030907091a5031042065101826912a03518030030080b0302210040e0250150302a4244aa590100305541c05400b0440c82000302a81c0001c06503401a402c491050b5120b00054408401000d030000740701c44604d0280740024441c03c01003054074400351001c1030038001301d0041400f581000180e0400f04e0303190301060181130000d1084200549021010032003861403080440d100d80d001e540c0131a15200020000a0740d80c078108003050340f48640001076070941030b8504015850360914041c01d8041420040001850444002a522070342003001001d86010322554813051400c841c4580300c428801c003800b000030040c0c04100508003d0055000141c0e450f06140160343c140345001f002040345030b10502c081030150764441c007918251801100c4290303171000d00c92402c0d81c8004242c482e196032a4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 143167967 1250 143166717 143166721
    0x70512270d03090507050d0506180c0907050304021f0504030b18030a050417030702010e06130506031303080603070b190c020d08071a1909031202070308011a0406121112 74
    0x60b8158444002070b40103034203880c100c81c0c980c0e00b0004603940c6404041c00380d51000003ca01c98021025004a560410200b1174640240c0c103404101d46400c00c072a0706001c903001000b04000c0d42081504441a8400a509a402d1402e481c40242690046000241ca0b102000e4001800310300190448100481e503442100c0d00c6081030f410003002c3c3e9000340035107183c88952004941286c003001003a5655903038144c4a20401c81c282c0000c1c400550000000a51013000c078010025a58072003200075070203034803900c0c06a80c41100c40d06000d461032101a1550303000e44d2100d04204100103251080d2400e416040e082c01003d8070700440b00311000c01c41d131a0041d6200898071155001c1100b10002400d5151003240c1c03501c080e00401c0b40b81800d0032411280021103002c41d0540f00e04040701d5a0040200d01d100c2d003091079881004140301403c9070456441280403034018070050210680102e04414424800f1107801e20f0242444002018442c02500e5500069280c683c0c104c0c4180410050b00c403003070704800081c0018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 143169217 1250 143167967 143167993
    0x102190c030507061d040f0f050a05011401091203200f030721271e09050c07030e210a06060510030e1b0402090d03030207030807051227 60
    0x192114032044502e40310b91400025114010443c0300300d01140ca890040c62140c901040c80f002e00740344003054014036a03507244c407038208046219060294500c80130005040d8105829485001140c0da403850512034a0031042151015004440f40c5170b6601d85482c4205c0c2404645818070400d9002800c810b5000d0000c500e81c50403800000351034060b025880310b045002121160300f000c1c105100c0c039880040d00140000a5176400d036007400744000d401e000c2440060703640301c409981c0b503030342d0f005030402c100e0005030308004c0010325010b000e800c4442c0010031460000c856801422158103401d5060060b40311140004c09050b090a06006d6050424259070045401c0e1600000500290207030520a1010802d042e0756a0310900c10302d1005810440104020804181070004550141d5000c56010b502000000b4443d02c0d4206031048943c4251400760701da04442c039001c5d00c00d140040c50703582000402d207c41c0d412441d074408203680068110071460840111003138003500a404400501d41184a031003d20210 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 143170467 1250 143169217 143169233
    0xb060d080c0d080a060e07021e160807090506010503060a150207150206040507060e060d0e010906020c0610050105160210030b030102041e0f060f080702070f030b07170402030303010b0702010219 85
    0x2003680c1c04c03c020040e0584814140e4007503941584d460005034422041080d041c0344c10b00e90a107020340c3c1101200e00c1e061001201030b030403141070f0b00245416002041c0c02c011a29240c0201031f000002402c045046142c00c2010500000151207034580145000c4d103d00b140900901c4070340b001e4605140010642094200081c0d0307100820b43e412201441880000a80d441c410450440c010b8002400c00d441c244285d64101e020340020408683c00e5507a41c001400064403078401412200c501d0300c043c042c5444c010b1049050340c540c540c8454140141041300d8180c12402e50503601c8920b030b0488020440280e130301c1d01140101840d440b25a010341c400103020510600280c54440c41686084503c0e60031504c82c0a4035440d0f03601481010003082803845240b0410f0302070602143e008400f0310484202554a8151140d0f40c001c0b688291749a2050205001c1c01c1580040780a1141058905030001800d103613001c0799a81c032051041105030340f0041141001c683c402e00c101002502e00b02000340d1202500c3c200703110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 143171717 1250 143170467 143170471
    0x4062715030203042001020309013608060106081b0304080d090b010f06030b0a06081e0c0904060803130605030a0b040603060b010e011b08030406021207200a0b060d080c0d08 76
    0x2c10324004544202c1400c0c2d05d0032050040d03501039002e1802c0902001c010f4404079810356428105080892086104101603484005401ca04034140c03903107145400303045420154184c000d4400c2000d400b04200d41d06000c28201d001c004507141b035095803981d42d42080406801346000d542541400d1200da14144403000d402c05060b0341c09107603044609555040240d02300c8003404200c54011789204020030865010b0030003503610039540b100805491441080c00f010542084030303100280c08001c520310041e401c0c940b1458018108104c025440c016021154084490aa02c00e15040040020004002c0540d94010540c2c508014009010403916840d200e0058907011400e81d000460030a05c03841389610038407007845020140300c0c000c10504c4c0c0725100c01c01c95502c01881074401607004c01190444202000d0b02c03d1060120f0307034490009005c1d02d041d401034172260451046031a4852103840300411041e403e0140c00100071a0000401e49a03807411150b00c5c003074010030305401d001d110b84c01e240442d04070100034 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 143172967 1250 143171717 143171723
    0x10080d0c0c050105130b03040204060b0304061407111b190602030309061f0308090312070302010e0601051e120f030412060501050d03050a0509030703020913170406271503020304 78
    0x803401ca072190300469050082c00c0048102030b004034002c02004000c54015a00140050008685d660301c40b200340c07940303038000d407400c030f802944d6440a0001c010b10719414541016542c68030215101500000350ba580702c0489881040a15000146100c0d070740d081805201800001c2c041100302c0d51340c00c40603499401c126407000040c0100000102945604511962410f44010242010508544403480d140d0001c45041d5018411014024500045e10001d04203c9100e940042500003220580d036080c20410b900c107a00500c1030401500070080c00411881107400c040d42d45600d542d049400c0507203080c0032000441154040001c02060703d2031140c0da4400581d0240c402842180d903200d09201c0c02c3c00180c10082c0c0007030700610a000c040c900c030790001c11001f00001c1c104c0e90b0064403600002c114040680b0302d00c00400803031986104001070391803400c0c500c800c11540103060903d406006030070085136550048600c0c07010781c501503011500001c50800b41c102c80b800d25a075003002540280081d44181c0301a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 143174217 1250 143172967 143172983
    0xd1403070e031c110307240212010f14090601021009020604050a0b120714030601120b100207081203101403030706021603030e010504020f0105090f060706020d0c1b0b10080d0c 77
    0x20015000c0d00100b2590800d1f03120750001e4501c040d80c48240e1034110b07112210781d400c0f0340801040c601c12040040040c06000b0407029201102c3c60000d40c3c0b1408084595158002c22940080200c0e580c1c000c200d00000c080703500f90204000401d031000a5451241d900140c0e400f4402070320100f21400307440302510034146400480c904646906109580025808590011500e420000101654811404400c0b0000c0c020340115120910034006000c842d0b00182044c016841540c003000ba20104001c4a030201c5c4582920500c1e5007440c444445a20040e4011485005001c0314117200d1342e1402c10850303103641d800280441d203851050100c0034141400c51001d40019007401d2444200c490180706990186034010b1140c8803082c0d2030780041d111758100c818040e91002000544940d141c5500c401402071511400c40103aa03112404008030860383c40c0c281c1e807030401010f45004020b031600c02148414040d00124071011640c2e825078407001c15020743e0002c84040c0110021058140d80010050480e031784142d0074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 143175467 1250 143174217 143174237
    0x50a0203040204051305120d0207061803030c0e0906101e020609060a051e04020316030303140114060301140d12210c0903020d1a01031a07020d1403070e031c 69
    0x200031741074422890701800d1500110642e40150010303400802d410b45d000000541044541e4641d034044a1900c010758582040740c9420104056140c410b0b107403100f44500740b0009841410b0080303008404010718030750045505600e4940e10300d005d09910f004000300608106101041c20301c0081d150041580d0b48030b8280320383c1010602e0300b00503000352441070904407058110200c4205112056510140090f60103003d081c5461031a110310080f1a00a1400380d2008552850000030f2940850016817107000d03c01d092110a20090355200c0807a411105940c07c41001d0f01c0d4240c00142d841c000ca8440181803c80ca9025250340c1a00b061940c10b0070381101c104451400c3c0d01315500d400369003102b69001d0016100400a100501e000d41650140324002c0c5000b0321407034420020108019402c3c1c00a580803481c004039241c01d4441d820300c1682c8601ca034409002168001d0310050411000d2400b1074043c2c3d400440090300b841d110f400034400c0d214000301180c2e060360801ca40383d0802800e0f00360040008821001d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 143176717 1250 143175467 143175481
    0x20a050916030f1407030506010c05071728020907091e0501030f0501150f050d020d0905070b0c070902071104050a0b01030b04061503090813030c05120d0c0615030204050a020304020405 81
    0x1c26182c007803481214001c0130ba60b815000300c0c010040200810b05002284882c0c4021440c200024400380c0035003e640c00c01025405100340c602140c81c00d014050728105410400300790400030103e482d0702d50503950104c050300c0703d43c419282c1d4402c0f41c1203001c0000b2100046d11074180e0341c10005080303840070f0324108200f0790072407803640985200340108510900f2000b15240020300c52600204441030074504107003019013464a580c00d03030740304159004d03100f07485040a070280a014040440201100c810340c40c5051554280240c60361310381d1082d10010b50b4003040c110706000607681c1340178000b0300c0240300b0045841c1440c5414000c02d5814405030000b860109401003c1c18540306003030a45041c585044100b100488044014000c0c4107402c850304103003800711900d0320703001d0070054020354071808020b4469801e010522160700e14441410f50f05a0010004009890f00151541041908010041810980c3d00224104190f1940c002900145054100000d440081e8050760140c2d2007100c0a0041e612420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 143177967 1250 143176717 143176721
    0x120c0b01090e150705070b010e07170907060507031b0c09180302100209030115031127240a09020717030405060f09010915052a0403030804020a050916030f 68
    0x3500802c07030b5100918801c43e8102c0c0618440c0d000380c00345406407600d078040d90340000400081e0301030002c1a102009020041f500304644840c580d441840e40d0116292a00035107603540010701c1249c0501c000081d450040c50701c20028400d042e0243c1c03400b0709960741603141c400300c00d10349440381c000610f281160200020f000095882c0c0c0c490380660040650386e50b1704001c1c1000398007402449a2644d0b03151250000c1c0e1781e01d4103510000f0750069245014500002e000e0008a404070001702880200c0c2e100d07060301406080803000d41001c2c00e19100034001c07421400444e0081803a4a00d03d030f10824034400016160500d400904d803052040400039401c800040b00c0b140780d80401d0320018034680054000800300c0b03a21050455020b1000b2002240140b40c40d05c400c074032039180c0040035814517110001c02c007502e510202e102ea15405c6003010b10010075800150040d0500617400020b080003203000102c0c00303540d900c905100241200401102990a090b080340340c11101c050007a101080c100410140c00d28014 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 143179217 1250 143177967 143177981
    0xc090914071404060e01032714060c070308010611010914070602161d19020f0901020d020a030509040e1e012304021c0f051b011404240c120c0b0109 65
    0x1511445e210f003c1c40c2c4010750140c40c4404546d0190b40c0880d280e4041c21460406d40f0f1400d5009502d00c1c40300c1c01c000c41203941400c00091403c456018100710b1030001a40c0980444d044514a19044c00031411221042d4050036403000c014281195509d42010481c2c4042231100803103070705400300d4101c2160320f02030892000d0740e440349109000f00920905103020041543c01e40c000c04500c02400480a0710442c401241c01c0070100314481ca50204465085507010803200c403d0046030300003040c054150707035801484c0344280c0c40514043c40d2146401c54811300c080241a1030101e815060444e02c11850340072600806c04c41d120140390282c1565080200c3c0c5030064201d0040d0703005800c0c4040f20044001482c0c00e1951404111000b410701e02d0b0b1748011990a00903d2403040e4401202000c601100c00014881d070021102c90151107000c01c003c10084200c00c100c0141e0340180e45004410b040340354010f03030f00d00c4100342004d0700c403800c040c6403203000642c000f0207442058410000300046036200c4400004403480 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 143180467 1250 143179217 143179229
    0x80604180c17010e03030f100305010905030d060801021219090b13030801060f02070303030b011407110405010f180b0a080703030503010306050f06030c041a04020c1f050402010f030c090914071404 86
    0x101b080401c400c2521030f49099030000001c204220065500c1e40c0d01c41c21150645011f80701f60308003103982103480340c1a0044000074001d28000390305203070107540d0380040401d01400b440f0401501c071b028400a42e051740c0010b00d816030020385180e020300e00740078103440e268070f12041140090041000424600d000b0440100d000e0701d00d600514515055907400d40081c800319800328148840c226040118030125401044118428007180784108441c400340700607140c068001048079280d4400911004095140c200c1c01e83e45941c2012401c0842070313010a5a02d6034903001003800f801030070408000d140d0484011812030f84a290104160b940b400104425030724107032211945070b000994000741c1c503c0c01d0342140c1d08544102000d9051040304030001001c99204290035041c1c1c1e001921080701c503014800c40440840c0b0324280c00e11181c030f00707640024041000803414078103060340d5850b03203401c86100e28000707000380c4042c6004000d00c0c050812008000301c000c480510003d080d4003201c0d0713680c031082e106807421100c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 143181717 1250 143180467 143180473
    0x4090509060f040305030709090f0207150e0a0209100b03040f110103271104060f030506060303030601140705010b1c060b031c0e031f06290a080604180c17010e 70
    0x5403a80c4c00c403020360020700040208650060080313200c204500c601002004040001a0303610114034002c460003492070241d80e4050314008003211505004109102d1039035040300e800c0d489595440340310004c40035a402101036000c0210820003000012014662100d0080c403005071010400801103095400d58510710301c66034481400140480107a803041d111052003240d214058100d4003012800302d0f06250f0000460126045041007030100520407a6000b1409034061465407602800280c540c4d00c142d2a01d2000006c005030f01030a000c802e500c45001650010403103245484680c0c084249040b40352001e0b1122413409520403c545000105c00701c0c1e100c0212040901030f102076005403240c0f00151030113501400303030320020f80c0b416003000002d20700d0307060301d610005015007030040365482c1034041c0d01880005a0007a00401444190b8000d0b00c03a140c9051420500b190b1328070340420b02821740e8031003101c21400c0d0600702d1000c0040b4080280243c404151810315810382018040d403c1c0d41c0b8520340070b90913030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 143182967 1250 143181717 143181721
    0x109091802010804020d02120c01090801020f0a0e0a08011806050901290d0804080303070305011a0d0c03061206050613110403060b12120c010b180601030c0e1504090509060f 76
    0x9400751081c40c4c4d10a0004003504400300c61900800c1106c0c8400070650301c250402d58188642d581c1000044c2d0260032483c0027141803000f0f4009086952140302046404c0c001950003908840d50348141504c0504001d00081c00440c0c89558400380b140c5101e034007110541d041100183c1a62814807034120101c119001d044103d4401c1c15003080718200c455005900142c46000300c40102c2d000400400007450300340011552403a090400034100d070010303003001a00041c966010400f01002c0402d07140c1140074004000b800c02d21011054004090560103d0060310300c20442c1d10900c501d592009100d14800d541d01102c000d6551062030450340720308111400040140010b00c00f08109622580c14070030007910303010090a1800007980340c486c082e2801001d01d2400030b55019080820b00035201c04c500c0698000b50180740a0555003407203200240383c6c50406550310280318100340320300404409003001a00040980071003c84d41d0b15154440c0c0a9040340a00b480c0c04519400c0c0d0002d1090f204141702e0b8085100c076 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 143184217 1250 143182967 143182969
    0x6030f06090402030309041811030a080406031a0a080a140111040b09030f190c0b0a080106030b0420130e090d0815030601120b250c0515090c0109091802 67
    0x508000b50081c0d030140300c28403140c40c554440f403052403100b19550328070482030042490450000b10b0b202180b280a0f0b0001050034000030852015030f010340f9154100840c600522291400600c07508000b000c1c0d01c000802c0c0e000a2a00c4042044040140140c0e1400668070354811501c0c240c68141c441090014403c100c10004070134010043c0c072200308010140c07400f508070403003080d10706040c0500034020b8880c401d0b00a420403504901e00c40c020003680c00310390700340b810f1002c0151401c00c0500c1100c0c141030b281c4810301d195a4655010001d002c00e400c00980d21207100d0b10a40541d6003101150925942d40b00f0307404129140f81c4031135103108080301002000c8181c0c4224080352101e01c090020211245118007040c40340e41c0501c44240039290900c150385800c0d00d24200341540d03c00281c4403144640d039040b411380007454162100c410140340c5081c8103104517800e15009140c50ba4542d083c281000004041c48112000400c0900c070f609401da8070440f202c0c0e1a914218203c1d004002d58003006000c0c0d5a501c401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 143185467 1250 143184217 143184229
    0x1e0603100b0103020d060303080108100506030a021314010801021801020a0f170717030601030f0c08060405100806040c0501030501320a0314060403030c090f050f030f0f030c0c06030f06 81
    0x49840601d4007500f84501d20381e0803020f031b40e03040e0011804030b41c2240c01801b00700c404109202c90075445420a1103d400c0140c08030b501e44140789806801802d082038808091344d503e40100c00c12006034440c034840e070b40e555143c10303000b5044500b00c00a40d04001010070f04079840083d02086a82d0800c8402c02c03481070b1603a81410640c030681602c400002e09108940100d1490010100c0d241c00362140d0725603d24101e00018104e41c0d407491148140b0b45041f44483c6510b6100000342e511100c1a180018103458034040301c0030a40c4542e101201a100720f804100c1040b1699120300c044880c280c9060040342d072102900c5004500515800c00d06942d554a9003100384811403000120351805020396480c02d84907107503e20300d1080200f82521540c4000300740300401d541441103070200d21451038040c00442c00c14005500f014407038418a84102c02c0164082d085a5052040c2021001c610085501e800400c443c1c0f08c0e240c0d000a281d00001380204c4184203003134141201260300c20546540700c40d800b03585131010804 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 143186717 1250 143185467 143185481
    0xe10020c0d061803090608061005120405010b042408123103050607080c0310030809040b100804110d0308070503270106171912020a020d03081e060310 66
    0x2a5003078441500410302c803000c900f9804028001d50741c510b0040d060a5001c0d0490130060450390040f001d0040420760301c0c1d401303c15108240095100c500050315203040c11409080000100b81e441441c0c0512011544014103d544001105255041c4e55980c1d4855040c0c440094017501c08a085003040b494002a03498428405c1c0c80300c000b040c14412101c20303090401c0b0220a50021103ca60002c014055501e40000081e03074041a4a4443c518520b131080c0b60000c011000c0c48000e20015000c144c01c0c80079500d0360803407212503001030708162502102d004003c040c078009460540d42b02442c17980e000c1c080c0c10440c082d540d84a4041d2076014007078540030421912540018003180014103c0c00c00d680c0c141703881d96000000c080300080045890707400d01095440042020381c207507076182d0003d52900940d034a04040390014030b42041100681d074543c1030040e030401011010095000d54290008020035800401160090390760090300a94142c030f1552075088920183e40541c1d25a11048010369009880d0300b001b8 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 143187967 1250 143186717 143186723
    0x50c0f03042303040b0c0c09060102070510050d1518231e09070501030f0e0613022701061e020705060a03020d0f09050f0601060512100509040b04030e10020c0d 70
    0x2c4000880030740e4031429a001904014943e0100059813495840c0c00c01400040001c202c4aa001500300080041e59607640c80c440c0d5806590b429220f0307050203004605507012440082814170200c1030101581a1840e014050104202d03090b0031110340001444c401c40d1000a05810220342d02204800c030400c6ca998018032025001081c2c1400f210480000260540960321900080446a0901001400350780c2045460803035149810003007605250700080740743d08012050040b10b45142d44e40041000344880651303000c04409550400d0030310f1640c4200e803504940060340c2e020011044102d215106264503104080140e00030041800180b4002c0002c00d0792070743c02d080040c5816409034251f0305440c9030011000c2c0b04c5980300340300c2043c0070742441040c50406170030010304180d40c10300d000a4605e01510000a900404e12400940d0220820070848043c0c0300003025101103203000e18000b80c1d801422a8214001400408001d0060500c48540107508403541c000c0c20040411030140700414880b11010703 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 143189217 1250 143187967 143188013
    0x30f11150a03050f1506070618051501231e220b090a05040503030f0703060902030903030a0605040b030709090c12050f0105150f06070501060e0c0d050c0f0304 70
    0x420000010304000344052031003501e0206040c5840c640014150400070200e0a5032242c1403d040740d1661084112074159500007000035081c0e051000d8103090005000c0004c2840c864404600c1c109810301c141e040c100c0340f03048018400340061341e0b03551001011940020340c011b01500c000e02e856101c0000b035a4580301d4060303c2c4071038490f06850441e00074101c02488000241e900c01d9500c02d942040412268001d40566082c0541d007015541d0594a2000070002100c86c040b61000c581428400e40200000b00f540d060b09648904000785681d03141ea0003900da0300d400510b401000074103800c15000d45608400014003918a03240780c11328440180c044140103c5100c040003501040300d4070450700c0507440c0d03401440244200c80c1804503141c21100c0c05004d00400c0c0d03440c007140c1c02280e82d41c40c100b03020000065072025111441c034038009000d03061307580207185140001030810110003090b0015200342032641c5003e220588400c240703501e075446100e4881003070b45020000039002c9504814803d104034029110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 143190467 1250 143189217 143189239
    0x80403110f041503060b0316050d030c050a060b030c0a03080d0902061908040201080901060305060411010c14010e0c090f280606080f0601021f150b04080d020f0601030f11 75
    0x5030880f50307084070410300e40140f81400e205000c040d100d02d18038010260014100030f02c0c00c449548980e0201d2003814800d130960642c0c031003014804d005031015903a00408a03030b08540c0600d003140c003a0066006641c02031040c025a078840d881e0884031102160780005c022868106450508406040c9815003a0f8100e0740070400003000c00090b1030003410070003441e502c84605040c0303880012b000000c0a444d084203171781080400d001003000440c5898119070b2011000b40e00540180040e80d02030406400640108040c001081a1803419080440300c40400c4041d909051406810803088110030340701040500c081708001102600a03020304c4010344c0e0404850a2241d40c140140380907680c1642003200010005000d10101010380c02d0703074642001090002c2e148141c04500403040f00000801080392554582c901c1001d00e00320b88840c1340180101140781691a078031050300ea5910744001c90404014403410f4070500c1070290118125050702c1c0d200050f020301d410151640780c4503c000c464041d0f40140e640e00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 143191717 1250 143190467 143190469
    0x42f2d0307150305010e041101030f0b060a020a030f030c0819020f0d140a02070206090f24070b0c0f0318031312150203060303070f11030304031518080403110f 70
    0x7009000740380880745039009440c0340c1001000e80340181c0c80b102c129101c01c03040c000050301c0e2500c2009165400c0ca80051143c50f54030506018081e50511075030003030380028102ea18180d01080c64801d06000f034441e0384000d1520a0704508842c60402d440000a01240c04a0310118100040c2060880c81060150500840364003080ca039a0042c24007031007031039176500301000c802412141d96134001e00902c0118149041a00803901d10304c64030080500c61024045200c042d0b0f070b03413541c0000010007281c0302e04100100050392500f09a0180708166248003400340050040a00441150303a00d01c4420400d60840d1941c1500440348100010030314170600090100c140c006250030a510011318030316503d1507012170141441d060000c0822140e19081d40104100096514000100d528995101e185204000d00a05280901d84650218a40e05004c005000428400448845140c40e0110304007002070801e61701849100d5180610002c00d00f081c14401040819010001c07105a0707031000e00300728454941c2e00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 143192967 1250 143191717 143191723
    0x1f050c071209060f0f0c08031003050102030a020904110301080c09040c0306050c030a1404020918011514031501050f1e040c111203060a090203041406042f2d03 70
    0x1c010300d000940180301040150381c409420309545031a4104160410200e1030010720a19400101030201080080400d0140042d0f1000310011070b0030800854072030401c0480300e4060751107242c40c01c2c420b506080c0c1005886810400b01c0b4100d40d900360041090003c003405000124500400540340600b09040c000301096460282034071481d10440d2403a81c91030040802011520740702407018a404407142040016195690380e182c110094000405070300c203d0300000c501401070000e002500920118000a05040311070112030010011000e48440c510044580b0500d0402441540c0e489004d0081060b0203080a0641000c0d0f0040305401010000d403c0c070204065950302004c440000f489002840c825903801e000f050700b501c070700c12603042c95428031100058101c5403c0c040c0714121a8004042400c1101d07483c090154001d010040d50118549401c203004850a000c02400c0c0c80004c14083d44040c4102d404c908800c000010400f80402139068440d10580d01c010b2090031100094244032050761340c0c20 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 143194217 1250 143192967 143192993
    0x30c14030a0309030f020a05070b090a051504050f030613030305060f0d03080406050c040e0402100302040f032103020c2d0a050a060c0203090a120204020405060705030304060606021f050c07 83
    0x20b4801280520307261030000c20394044020f6150454011103c0e0300002600403440b4001c030b03403210039040d80710311514002419641440c0e00c85580002c9052005081100364030203030084071402c440e898220584c141c01c0c161a140121044081e41540075001c4000a010b640400d42024000e4600c0301c403400b0b52001f05040260462050f00400c40c460204820014039005865010900f801c045007041d103044181481484081d00c000d205075a070b418416030381482681a20000c5c0140c40000e585da90b80c81c280020003e00007003d007001028040b1400d0541c0c1d01a0080392680c4038a20300a0101000040c0c0c241e0320703805410b0480a1000703d80f0740c00119400c04019003003c0c1402040601a031030b4062400f80e003142d821002c940250340042c0a4052507654001b107440450300300403040704a007013080c40003400034456034105603409440070130840c050000c000080d500c510701c03ca104001094580c1c10581e614407a40b0489219908088a6509040c403103810072500a507020081c0c6052008a549000112080c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 143195467 1250 143194217 143194237
    0x30103050312180d0804081e0a0905041406040209040603240e010b0105030412050f2704050f1305010609020703050901090e1e090a14070f050418030c1403 68
    0x80810030481250b802c00d41c82e60450880b071407950460701d10707044880d140c0b40c15004040a004180c0300180034068403908940c0011030604c03202c041c1070418950122103411070205400080d100301004126410107205001a0900702030b5000c030030b56102000c20000c0d501400b90282c00a45444001000071b003040f07100701c18126001e0110f00c0f1048035006000c11291641507203641a07040100b82000c40e6000011640c10030703000800d210b8003007d544020740c0d1034400d40c04041c20400d00002c5072007448088035480c2ca0480c820060220b2500c00380130412082d02c000b0f445168800900c403020032a032428141e040d40450f8400c00c00440d40c1e583d038110700d070202c0c1c11264054020070f100260b030500c0e940e1320042040107081c0c41d03920103415043c008600115121030340400844452240c0c0858003100c400c120352841940d00c4404449000c8941030034680360760003440b40d030018010101020455150600407808400c4042441032440a03058508468a0b00c030880251382d2034800c0c5141c2003031100c051000f007021a507 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 143196717 1250 143195467 143195473
    0x10f0c03051f0e070509030f070b03060a060e0a0b0901030e0307061b170403081509070f0201050702010c02031213080408160b180d0804080d120b03010e0601060c0602040b03010305 79
    0x80e094005003a50803a450200c041e00320b00000c03e2100701044481c6581241e1145021619840c941c80031038645111064109178a00c0b4680e07000030941000f030003d500c07800042d6440210f441d6500c00c03e6500d44002c49200e82d11a14020003070105000c08000f030308550105141c00304595440403003507400c551020342c003030360415203a0007086105c04000700d0040c1d41c0c1859180030401c0703080d003039904003804101910040c00c10030480f001c145800c2880c0d040c40182400145642481d05152002400540a6405800c0035508150001e240d483c010321444041e02c00b1a00075601c1c0c18010705410060400003010f424560117080303042004684207a000d0005821540700138403400581d03a201d000c43e000ca55005400d001c00811401d0840001801c0c4440080429566a2922025880c20030120b0080390001c400500c14100100e20640c0e103d01d0094100c100c541c1c0400c0046401418142aa840001c1e0032110354402001040070300e20541d012200f2074041c1c08014107254075513032203034901d80c403c0e80306595942c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 143197967 1250 143196717 143196721
    0x6120f06062a0d020c01020a080c0709050c0307020607090b090108190501030f170a17060102010b030607090608060d0c0b030a090f080a0305180d050c0c0306010602010c1707090e0405010f0c0305 85
    0xb0010040000d40c000c0741c4c0010044505100300003580c60304c0c4810004c0c29030602207541c0e40580fa00300881c001500c0d40c0c030003d010b03030b15203004003160030b4200b11401c8005100d1000031981541c00340c078808050700c008a4a282c03620100c1401075030010005400c501d0944001c4134401c9215020307106050182d4840d00d02920703c40640c0c1014690038280b01e03040001480200702801071107411a05402e080c507101c9900d11042c1c3d854000507030042c40910307070407034050082904100e5440e5001c2e00c440e055800940300c5050946500042c000c84c81d21240004002d0380649001f4041d848910380559401a48450302007800c481554500c6138100b41c0c0c203401c031410000800c02c00b90070382c1c05014aa038840309000e80302508007040000c060b510322140c070b807450601c500014907040c83e00f018400800c0d05c003000b5040300c05550352818024028052410a80006001450300b00c40b03000484054a004440907a18904a40e040481e000c2400c3c6028008407542d41d038603048044124103c4c0a5104480c4840d00c0003d414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 143199217 1250 143197967 143198047
    0x50d0c03050d0e0603160e09010308210408070201110f1c0801050105030402030c0f040f020c0a05010e0a051c0e040c030f0b01020102040e1f0b04080705030c06120f0606 74
    0x2040320031144050001490140e071051315024181c0340d2204030400003049189040038140e4110b194500001d401419600000c03041c0034105c0c00030410000041d540360000141d00e11061030145003940e00421405041240402641c801d4010610500071241519071048080e4034a5141c0982040c0106e003000b40409194809a00300c8042801800c085c00c281e0b1862405a000985075924850541e104031aa500003100544a82d03206102c0d070100444115a551400c200300755807081c80c40d6046801d0741c00d080c1d080344c2c1d00701e01107501c24415902500800035504604000b603e4540b00c8000c217010010212900102ca6a803406a0000100303503450004524480080000640b500c0c444a2415680108000c1204400c2a14070316031054850300070b01c000560b40c400426018170550711940015001181c0482c0000c0041f82c2c000c2214030031411a11003d0400c0c05002c140d01411608000c07580f03048000400c2000d14100380c5078820300040105140038a060402403100954180c03107078081d110f0507096030513 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 143200467 1250 143199217 143199223
    0xf05070f150e10050d0f06050604080f0708030a140c010f050408090307060e01050406050f0c0a0b0109050f010b070f0302121b101109010507060e0d050702010810030203030405040213050d0c0305 85
    0x16100e4181c400360f540400301c9a01401030310039a0302601c0110b80e145141c03414510140c1c0302d5805010028001c9a89565a030b80841d07586049152003482805202d000040c044000000c40e40c14444c1620750100c4e0000c9070542440e650400300e10746845540764280f109600d90306224062103507101d01c41c01c0d61506929000d01d4035004503034000409101d6a0720308000e560b83c20100351011a10b03240b503c65a44c4001a405401e0760050620324000ca00c0303000702070002c100e1103001040c141e58640b03004000c1c0381d071b6582d54414880000c0c0b1a150804008021348401700e14401151000e1a010340122990800381d0802d042c0654005620346001e8103101001c5206074009111203214000340d04020b1244210251005000e8880d9070070369414880700141c442d04005003038100740c8141c1000010b072003940f61107100180040c1c4c0464000c074002036400d000182a07220b8000010156900a8021070038181003405210095104110501c011001c9000010b555641e19040040b0144141444d40340c0ea441c600e00301e46 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 143201717 1250 143200467 143200487
    0x30c03050606040c020616200a150203101403150a0506040e06160c031106040501050106200d12090803182a1c06020c0105070f03060308070f05070f15 66
    0xc803c03404d00c2e88104500d40c0c0050000e03003200308600e5010100d005900f00b95160f003d0700ba41066000200d44810491000107e00100e480303000306042003100600d145d49104a03c41120450400c90032290244209650840b603c0a001c0016045803548030100c0030143c018181228800c04a0751650100003950501d4061080c00c2c2298000a01450610301e400324900581d080703851081013409040001410301c140801640c01c03144000307440b44e13805c0508205028140901848002c5002c24040151000c005c06005090305280b50151540928010003140c00c0c1c5440762050300c103143c44562800c08503400070b0056000d10000c450070655050f8405400b4184052401d4840107900d603c4d40c4540c1108800d0500468030801703c80d904061000c0c00d17440300007a425808080c00350740c0701081204045134154803003400398900ea11100041d07401980110181c56403404000e01c41c88003407000c0000140e2884040d00d0040c812410707640c030300e501c0d40807200c070030b0300640d01c13031145500080c10041d03415800504005c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 143202967 1250 143201717 143201719
    0x303062121080c0702040207170405010e060702010807110f01020c0f06070801080a06050a1805060615041512090203060c1209060c09010809010b03010507200f1e070f030c03050606 79
    0x10070000d415000c1c280801c001c010550544000400301d01315555541214a055400fa11020011110300091001c94200780a1b4901165898065008510300541a54051941603465820f1603903122021500c009042c0c2d01d12140f40305400030728a41041c203002400c01d08036040d0050402c05810306c02580390074005051142480403140041c00300e240040f40441629400500100e0641c49100501004081c00050b03c142c403035086020b40c1c104038000c1031160243d00211800e903803550b4547c4242d003840c4518804d03082242c0560440714140340c0152020301000000f200000384001ca15004179003081012075076226050ba000410403858a40703443d001e9084520180180200d2030481111070b0303907208040c0c04c83d0611621600042c0c859209400c22011560042c0081c80507080c021005401442d044074400940170b03101014080010000030700c00c449104200c0207003070322403031702c04441e1680000400c1c03480103015004020070038843c61074902004500c20703a00c5a041c6803031070500c1800c0400113071181e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 143204217 1250 143202967 143203013
    0x1f120b100c0b040c0905010b030f3d0504050a020406141e091c11030d18120f061401180203060a0b09040608060108060702070f030c1203030621 63
    0x45030110768000c0240040c1030348100106107680722820f26190100c11948203c011508240010070a200d50380b01031402003204003441e1100d611051503042e481d10409824456a080c14030750207131310568028104c044410000c810300718968941000c00c042c0c8004650100c2c3c15a00040e0411000b58480803080c101c0e11301e00300c1542441010900818452100d00c1308884618011405428607503603403855003a0145442c80305490034a16140100d1701109640400384030340104040020000d002d1092041c000034020300740701290307040c80c0c4810a42144000f003607a041000c840711000080491003821105068400311015941c074141e84881c0700cac3c1e1180c0003114942c0c01401407208940311401d000c4203032002008015201c1c4080d1000c04e0081003203030300c0302c0d055114800000a8499022600da40140c000750309864071291555030307184840700544001400c4898840c800c10105850300c00100106119140200f262965012044c0c0131507110b10801040d500303030b10441410401982480c1c407141034500c0c03113 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 143205467 1250 143204217 143204239
    0x3040b0609010305030f09060c0123150d06020714030a0305010e18030a031d010204030c0f081c0f02150c03090129010c080705070605040305060606090906040b1f120b 73
    0xa402d0700c9001ba06052140e0020125404045544000036141441c0f860740c020811141c03005e00140c5800303d106070503001e41e400303903003c60810303141d803000180001d0015002d90a0a0541d5865200075801464280d414bc0020154140100428002000d08a8860342d0103c0d0950400c41c2c40040c0590180c481e1a01480000041c00340440202c103a80f1300006900703000034903030740240c110328440b01030b60301000c00303948005008420031490301d42100503135090142402e040e07511411100d990f03407160190b003e48841802c28500e10144243c2c00701030301114070b00c151030000c2d200b800079800700380701a100b00c03040000110400204030000d00ca0049640b5031300b100399860400341c09055591080b01c08040b8100142d586102c4240180072040750f00d069070200031501c0003035580c44018007580207404112428051400440c00c18545141620702e0984010708136101a2558020080140000d60415420810009a100d00038041074041922281c01d034442240d0220918503400807a0102001c061082c4442d4803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 143206717 1250 143205467 143205473
    0x30c0b040f090b0a0509090f0601090e0106080106050108040b1b0313120306030309060f1107120c060201020403050c040203040f0203060a0506040e07080303041b0b1c0501080d0c0209060409020d0803040b06090103 93
    0x21601d04445c020f075142d248607116210420700700004c41c0200384480c407a803800007903101c1aa90001c1460084080200101038031040c405003aa06188249400103a410020601251501501c01e410501682c86034075110342c0d102c40c5e00c0c0359800072158508445100d400d0314042c84184c40d090b00e01225103140c100201030566034041c01d42030050149c08104a0b400e81d4840c942401000344507409004a0708448030317155240740d008401441c100307044403149010400081d021b0f005000f5542641d40c0000a40210b4865900380402504000c005450701c0343c0300b9802c0009038900707020083c0105158400481d10f40303002ca040c07209545e4204640d0038130b940035003401c000750040403040c1c0707030059800070b90030400345002c2d544e0002009040c0c1146040d0351001a842649040120301c40c0c07505404030905200680c3e880030555120300d0800b00d40400b05400c07903400d100600c0c10714a110350140c001000000c1808050b000306003182032030300c2e044800c0c14001050100f440000c034a903980c05401103c0c0001035605640d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 143207967 1250 143206717 143206729
    0x160b161209301106070609060b0a1205030a030b0a12030206180d090b0304020d02100906030c0f0518150d02090a05030c10030b01210915020a050a0513030c0b040f090b 73
    0x1000c081c2442c241c546444095581360402c072001d031900048248502a42070900000031300361304074417030720a03114075000181d840d0285004400b06a0024041e41c20680034030740646c050550054802d90000c043d0740e020500c600b0b078440b1400071900950041c5450718080550814000c00ea5102d4070441d0b01000d511210568041c2815060341c581203030150304e03500d41d032010401102890000941c4019814413404c1d816920104410440e840c541d002e00603813080200550304080c00c605a00005002003200c81c801c070700c800102284003140075044101e0702c1c4003c2507100c01600103400d4651411b80006422141b454000d0b2058040c0c14200c001d004000d01030f90019046e0b0740d02900300814562070b15001c60407a8020b50501a143c08400380580c0141907210700440140422402200c0342d40a910710390400400301c8c42542e20361442a00c4039450801c0e021819249600103903040d1107524011a00840002e5000825000602c01c4224640d00c8074103014800c01c034565590045840c5615040918001d40d0300e01d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 143209217 1250 143207967 143208059
    0x6050607061508030c03030403270b07020a08030d060f09020406210605030a0b04050d0807080601211a150f160623060307050102160b161209 62
    0x401000580045541e603142e510410681c481070072800b003c1540004d10304003000462195219603522041040f801c541c0d101e4002e030b007a0300e0542d0281042000d008070200b4500030641a4002442540c01780c3d0f032a1466440c41c0d20004002070712681f01c8071708102032114681c0c210090424944194105802c000c00100f101d800d141542042c050042142c800111007584110090314000d41542c801e0047d504210380c034070001b61001c591a01c50b60301c142c180c5501c034291240c058840c5a483d08040c1c2c5449004591702d16801da030486010510146c030003001802481007010782d038179140c1c4618069540070b041000d14010315000039541c150800212a205580e08229101030b002a0000e0800e0600750400d0303401424440c00c0c1c9400e184001d01070102a840750726485106001c01c604940300192aa001240c441607161600c07081d035180450305100c0702d40640c1c042c04140540800801007055152903203090310030018260004684061020300156000f2140c0e5514400b00c0b0a141030024200c0c04090385003905 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 143210467 1250 143209217 143209223
    0xd020c0109050f24010315091509050706140910120b0a030b0714040f031e0209070915030b0310020a0c0209070f02100221040201090b04080304170105061003110706021209010f06050607 81
    0x25239080c8500b041400081c0c0000e982c000d150801c258581403a0055443e01c2d98017980b00403541241080070908611001c076410078001910316400360052550680d0101c124080d000d0000c0c0d240e4046004a4448400480055014000c410200c1c20566009000d1800701d1003003988901c81040300b0b200b07000060b202082229840010303095a0a030b002c0281d00303505404071000f940090240280720744960b001007039806540c0217141201c40c00c1110001503049905005019415400c014040e22a5404944c00792400401c41d08204884010030350005500304001c44150010581000e0741a0201e035040080007124400c6810440c0b42130314100c142910b020034116401000b003a11400203045901c58a4030760b0081071281e6819031600d84074000c03191650014040e2694206030001c440344043c50502034280201d00180c611008044000001c402400c02c280103c42000000c1000c28001841c61004100020080b01e21991034145141c1e051300307403480c0b6040a00c11a003010402c1c00030b5603c0740708640074164 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 143211717 1250 143210467 143210471
    0x6091106040e150103020f04080a03020f010209010c02150c15090f070b0403080a0e090c0a03180309050d060b130c08091515010216030501090b0703110d020c0109050f24010315 77
    0x790f50300100c010b0700c1000360311241c0500100300011804030010702d140a9621070703000e540040e5407460b5003a00300d010b00228507000400d036811010160604244411010041881e018a403101d0380342214640350021a082c41d1207240d000400030001b40502201030b081034284050040c00b0303c0d040001c1c11601440c0006000e00800144013500030f4041c280d42d480c00c082c090652030041c90000340c615020b400600040300030038100351100380d261440c074034007481b0075501d42c81c0d0125403070a11007408501e00103540704071070b401c0e41c506a0748070b10b6803250105410030f0079040c00071134002c800c0e02000b4601c0ca0050718015440d0302c20750100e040300000890f9254003130b001c200102c07854244070300100c1c90301000a26180a0181c0c20b4804414071a040d004014514040d0441461a0300c5409044045500c5484181d82c115820300044681e6101da40080004011020000c030f88028161034050601d4114054012154807150217450401c02c43e810301c0078242038a9003100499850350f06c68110b01a1104e101d403600d16 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 143212967 1250 143211717 143211751
    0xb0c060106050a0e150c010e1912020a050109110a060804051c0309140a0605060307060539160b09090619080a030801060e0402091c0312020706091106040e 68
    0x601c80c0d0f4041050181c010001070741e120007540e05c4445a03001200c01c1403554208062100c41c0600011034000108007880804440da4007901c40e01c00580c500b11a400031401f03040401c2000c11ba09000e01d084450180302160380340c911110800250b0002644510f0901040408000c041040071800e6a000c00d01081e24076004149488210010440c95200400c04410ba49201065100004c0c08865442c8944c000f04216160041015a908000c1c4100000034004119160303041503003c0741c80314a4a0603007829150710301c40f03020b40da0000450200da281d4030b6000a8040020a1019601030000c086071442580707007a071410007181801000601640c0545180a810300c1c82420490780e0b100205110426a0520103003454001e10a080038031681002805642c002c8085182c81d00c21a8600071004009226040c1e1310404040b04020001c0d041e402d0001c0c1e4840c42c160303814580024100f09125460020341585146441030030102d0201805010303090510060202d200c1080700746401c0701400c0ea161800d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 143214217 1250 143212967 143212987
    0x50f1005120a18050309091b04180b090106020f15060609191205030c060f010b070b1801020d0e010f0902061c020c1504030e0909030915130e01030b010b0c06010605 72
    0x1e03152401603450007010250f50382040c804084054002d04004440995180e1160715010513409414034070080d906001708410800d800080c03000b2904030816400102c0c0004c8400001000800b09911150160700b015404070b40a5400748464100c010000289980509020000c0b903114010020f49600841c0c90724445007a0300081c0c80008000c10700d541d440c140310022460500d490790001140e0126900c030b8040490044880718084a050350760045626007400c1c961f403a003400c0600c001c0c01034071070f62590390540c0201072803c3c001041c1e00d080c003076008903101040385a11401c4540841c8042c0003036182904040069450b0030443e94101014900c4010440d600340608000b48251001e40010b445105201000f01c0000b00c829442035019841340f141e0038580d0401e001e01c1080480e0083c80581003040303e140240b40010b00c1c284820440500c244c1031540821a24480002a8009101c4503202d10010010403121910540c09003043e00d01c081e040003001e04000c2e07a1050107018040038003402003140d000c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 143215467 1250 143214217 143214221
    0x9011805040203040807050706020c030a082a0303070e030715271e080102031e1515120702030a0207030303051b0310030b0a0e0a150e0d02010501050f1005120a 70
    0x2a0034010000c6580741080d16003d0100e40c810102100c0c10701903054005032650001c215101c208070090050300004419550b409241e03071083d500c011540c0001c40c0c9840300c0c49910500c00d84190107242c01035641c2d0400403030140c2940d6403c090035219912480b418004801405002e40036045141005035541c0121140c00e2020701c400e1a01c0c0400c0040030100240d000e90055a0241c400c0400a02070b00451b201d403103c80c00c0c1d100440d120612000b0071114076202c0d62410390301c2c640c002803d005010244030500001006101000c50fa070340c50090104200075084404c0300361a405c51040d000562400d44038410103511042d0b5480080d05042d40c5d0400030745200c0c0000004008101c16842e02d565a103440c0f071229a14a8550100f136490345084000078012010522075095114113850041c464003079940d5036081d42d05558245100a261150701188000d2001c000030208904590008a00c641c107010a100184c1c00e07002c1058881c29440e000d0380c101507000360454401030018442e1038101c7da682c1c440c0f000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 143216717 1250 143215467 143215469
    0x20a030e06040f110a0608060d030221040f12020a03140304170d031109150306040b030d1e05031e090a0c14011202093015070221090118 60
    0x46005200802c810011142104001103120700c0801c03100d0380c0b0203c1440800d416130701460000c52042004110a4541010015400c0d071089c41110460489140c0c500b00c050315200c2c450308008000b10f403d2241100751200c1d90041e04000a20766603001032900041c3d0f00d038440e4800070b0700c41c1140981c107a030708070710034411200580880303008103104403510840c0e40c0e680e20981c03440c44c00003440c0108502c0120760350022141c0c90034000700b24101d40744054061491541c400341072654095940c0d110507115032001d200040c0c2c41490750312500040821509803400c080a40b41211003081410020020b154100d40081d142443d51241350000030b035502028103203406059040a007030482d032410001681000c8020170341d003c0b40203917100050b100c0c458107658264010b00e5500e5078450f00c0d444000305d04c614140f41111001c82009044a500c0d421308120505007121010402c0036545d820081180d900d40404c807041c1005015010101c8c0c0ca2410f005011650040f00251410001705596203d0201c1584003290 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 143217967 1250 143216717 143216741
    0x1f1a04020c060610140f041410020c01051c0608010b150304120c050c03060108070f0f0f0519120303050a18020f060f040f08010204031109070f030f060306090302060403030f0e0a0204020a03 83
    0x603545681b059400115500300b8401c400354884a020f000d6101c0c24106448660303200f007600200030079031450b401590306420201c0d00030380720090064010035400703003030240f60010203060000080c1482100c0a0080c0e0144408041e141b400c3d040050100107040071032400d0005400349010f01312a29207140007800c09207000340380c030b50500c105000070603400c101044000032505040f403020701e025078a1440811140d03452184c1d00001041c407a04210030305107001c0171a40c00354040400465035071240c14031001d0400b00c0c00d00354000707540c590800142804611506145100d59690854581039a0b4000748040300482851800703104003140c0c15411020000a66024103030301176100020b5034036076440c2030003074001c0d2000380e81141c0e52082c2004c40e0b0800010450080002c3d6446101030180780400f98003034001061074805076039840000001060301c0b40b01c1c44600340d110398050240c80c1014240101a1440c6c01c1c030028180c0e01e403400c219401140040c0c40e10807a41d045c0d40240e200d01031040705800030002c0700041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 143219217 1250 143217967 143218007
    0xa091b050f2a3f07080d0606030606020a0302031206040b0a06050306010201050705070b0406110c0109030809070b070c120203070f1409010b040b090904080702030a0510050c030601050703050c1f1a04020c060610 92
    0x18001001580211023074a0050340d0401c5229a03c1780100d9846207920805809a0010441c030749440300c030341401e5684141c0c00341c0042644000032012030100b04c032550040e80010030100070300c0a95a070a00401e030b0090100d241c46070810320282c682a002c0c0030040c00c0103041e584c2d80c26a034124100c4010950f0546282c0d030008025401603420003130901c4030101e5840d0068082e650340883d140300100c0651b07403c00d4108010701942070401c0c00011020303602c40c7c0b0699040c40b440e4000201040700c49034400c080d10305030032944c91914100042c010810f82c184c100001600080c00280f0120f00001d00780c900a8004071085041a140c41c101324080f48a85400a901801030399844424800002410403050140d080200400d640702808481240403e0b240c0705e0002d03500b00400800b0034031586c09081405c141e107090340c400c40c003004104640c00040001d1030700c0325511100042809203000d03044001c0303100192403d5107050541c008050f280e441c0105550b2207480a4005e02c03482c0c61107110f0300404c10707c901c1ca034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 143220467 1250 143219217 143219227
    0x40515010f091103040f0b13020a03060f0c03290d150603030809011b0807121a01030f05010e010b1c11090a091b050f2a3f0708 56
    0x104211184682c01000041c60408100c02d00c0ca0940c00b048900c240d80000b0001c12803003890341c035076a4000001d810b2141c0e20300904031100151342d40b4480034004501c03801c400242c8600c0b0000c088203035119034015405252a080001c070080c2d114913038010325401704828074468159204c0c0010200300049101804010301444110300d407011a910034003d0301d0180d21603000700e17903a00c0c0c00d07642a0759843c09808420101c3d88100d60a031400740302229000740c01420400e007a541d07490206400c869841d0000744141000c12282015940c151003040014801954240503a41c103040500000784018032609070f40090004080e01170992020111700b40200c0d41c40240311040c9003c80c8001c01d034100e512058442d10341c40d000000d1106a5204048441e4182000d56846043e2000180c4980d007002000f442d221100300001c040850a0f000c40441003d140a40b00c510703c8400480d0521300b500000041c3c18082d401140014217001c00601d0140c0c0c0e40c0c84200b1201030030145506a0035074025480d000703045c0403000c1a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 143221717 1250 143220467 143220479
    0xa09061404020906060f0405010e01200a0b0a29010504170c1509030604020907020f0f030c12030c0f0901030b100815090114040b0f060318010606030c050d020304051501 74
    0x603018020360080b6041407a0303445900400c200da105080e05400001c00400c8108100e500401c06010842414106043c1c000c00300d0399507942c244140e910142c0341e5040031100408001d8690f4256820400580341040a17406651600d04008c143c86040140c1141a440b00700660b03100d40b0455025060f06000c0c030b1011640304030402c0c0e0b910320b0180554400d503a104c000101d20582d01042c0c0b2042c6800800800054443c0d400b4000710001c0500864110b000e82504640c0c408030811180145465440003560b450300d80d01803460a0100030460958107070820818031080d0006001a0764031000b1021106aa1302c0030b01c00141e005005010003d0740040301101da81a440b80c211843c244618445810017850180c150204401784500340617464440245600b52041c030b060030350201c0421070000d0a42201d203482071000079501e400458201d200c1c00b040403030701401c2d440207010350b07401001c00d400d050203905400324004d0080c0c0103c2d0211400583c2c0840010207104041018080c030005401c0c11200360358540c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 143222967 1250 143221717 143221751
    0x60412030f02060703020702010c0210031116020f03060907030201051c11090f090601021e010f050c07150506010804020114091005090a1215230705040302100e0d0b0a0906 75
    0x2507081030142c0225000924410700034000c490344168140d40d144000c094990810107541d28102114041540d0782165045262a810050030716a0074503480c0d030640480341c4100105502d152000364040d402180501c003224000203003400590b41d0900f059910740f1000c0000e6110410850b5450901e0350171f10717501e0003110001070010980707810140d40d0410542800420710040e4102501c8560040e4000c50041c065004008001011101c43e0340c0040740801001020f00c042d60410780b10443d030b00000080000400c401c542c5041903400d0441c009000038501003001a140010050006e4148441c5001581c00066120203c68003094000e01c40340907a203403014010070b1074201d0b0642500845450601040d03451f030300a18a03076000d034000f4900c1c140f024100c0d00c0c00c014003108035000701010441300b03000144400012405100310110b54516882d14594010000d00d40103140d5040203020380a030381034400f500c81b80c41420011b6040400c0c0f50068550f0100d500c014000500b020345158600400084044140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 143224217 1250 143222967 143222987
    0x110c070905100602030309070902220b0306090618040303050402131529040308090a0b042408061c03200a060c1b060509030d09060b030f0f03040603050606041203 71
    0x41c402c07204440d229501666244001c0d101500f00d41c3c05640c0400464641e40c0003001c024038000c031080900000c030407038120031a195400510018102004005540c20039415203644403104850024010b10071107440d41000700d0150015080640b2a4002002d54481c00100003c08401c100100100c0e03500d040b035011500000c0c0500d0200c241c0706c10140d0031194a0440b940141062405ea403031410745584e440b4403940d4030845050740c00a0a0010000c3c0140070a406032001300329410001040c84910302041d140705107402c103e0010b011040c4180040c54552001c14030003141c6001c244095051281019500c03810301980704130064400c881c401008c10400b0a610755260312416040c00f80742d481c1802510764000d1003500c091400c2140d60f10718041415500031903041410f080980f464851890751280a54440c58010703035400d6202e85402e100f9083c1041036180107000780b00a003002554650780b550300c070300c01c6208400030141c0325000301d107503542e511046a00030041c00c4074451400030380b850050659585 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 143225467 1250 143224217 143224231
    0xb070e12061902040f06080a0f1407020f07030c0b090a030b07050a081b07030c0311030d090510140a020702010e100e031b030706081801060806060a0b1804110c070905 73
    0x1d048482d05050081c020744040c2c071100449641171509001046941d043e009044684e01525055038041501c0184034000c0c6814a60002c03030340e00d00d840d05020340b03090136a01011040c0d07406100c042002c1003505244605076030410390f546551b1001940004c8401d0025000944018146c0e001c1c00340044d004001088030f001291102c50884e55540e10701055046014005813003004e081214100284c4130707444080300240300b4100071003000244d120861a6800c000da5000c110350380e80c0300300024420200030b800340344811045c0a2040d82100705040900c60380c050301c580901a0045142000c581c083d030380501c031110703000d0288590064081c40c0244400401e6840500074050004c2041702c4100121001c600d000005d0010b01000d0b16040044034820300042100d682c904400300302107100b080c2800b07684000c00780b22004000c503052031340400c540c2c03400f19405041040420000581c803240514481c0b8098001103030001181131142c40080340520424840c0744070703402800d41c0490700c0703034440e44620f0007401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 143226717 1250 143225467 143225491
    0x20405120114010608091e0a1401020a0903021203090618090903181003140403020601080723060f090603090304030510050c030a050903040504020a03020309060a06030f0b070e1206 79
    0x1000226080b207500b80c121002240065005100c501c0c000c071140e0360401c0c00c0d481110003a52001c2c56008101140110620f92600541e2294040c00b03001040081d00220050085107881519240030700807002d10f101c024007482460a00902411060060b540b2a140c0075041c2a034a600c4001c00c80c00151300c0c051180e01c140707221004602d41400004c241c030f0088140c841444281503d01040011840340032052004064840c180700d04580d84624245003e40d1184d00280081e504014203282048500d0300407000701c42180e68942e00084c0c500c00c080810310016160140d40e2106031200000f14464900ba0380e400c248004144581c0040c000000c0c0200ea0144007910047e600c0600c5070400d841c82500c000420301018000314904440a600240d04141c4c488101da107481e91f1400410f080ea080800300d40e01196001c01089007c11060128036482060800d00300b01d00b031704640e80c00c2000192800003070b040003103140026400d00d001d8210031992500042440354018103e00c0d030f20b43d80f0402150304030042d00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 143227967 1250 143226717 143226739
    0xc01060914011a0d020706090c14010f03090c0506030c1b0a03050304080a090504051504050f100b0c07081006030519080307121404030305070219081603030b0405010603020405 77
    0x562103200384041e244042040d161280d01c1c00c0c0300340070482c080ba14004004801007083c10020309580c4014a0110b214403070104030344c034041c01c100880000d50392140891171820220308095030307405603104c07804901604000442e03207510705003a140810140c00568124000000340300c0061009000f4089071044a078050451440c22511152603580c82080280429018000b003000911828050640130701a460032255003175840e0b001405980094801d44107550380c440039035000e03040c40d006040d8442942910a4814103106444072240c440314441c0c06c0a42d032021401d00c409007410300030800208030724005c8849400110f04400e00916103840120f41a10940040c0c0500301d440d504413154691f004691182550358081e01611543d07224550420001d5071840c0f110ba0040b801946a80590702a6800003190300c1d00c054007034074202e400150040310f18090701966002920101c01c42c0d00c1c0015000e00071a400050380b606030046d00302c12160540c000e040c81e00204146900d513016104461044505601607 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 143229217 1250 143227967 143227979
    0x11010207050106080616050c070b0a050c060109020c010c020c0303030408090a17010501061e090509070212120105030601170d0e0a080109031d010c020d020405060105070c0603060e1e040f02120709020c0106 90
    0x2442a034507821022782141b1001c00050348843d003e802d41241c030f030071f0052a08503490038403030a1030030076008100696030200d08100100000d00c90040411010b00040114885c4107000a40d0780c0030080004140040000390714602c0d0f1112128400240044a185041c03803805942d468080c120901507400027820003a0a20003620240d041106120069100c0d010744a0801d000d200b14840c0081187c070640c40740c03003800940c1c071114800521105015031211512541000205400c022041c2d1205006600b112a003c03003845c0d0106d651890780b022414041081480100800c06801352076010003440d511f403106410078190807000c81444441d141c4401c2c41c03013290030801510340c815405406504522203074840b81c010305060b4040340e007040c81410302604000c007580d9a00740b0484d41d80c02c4400025102c41c410003001c0c10071000300e5005102403801003030004451031410140c020042010b890310a444084806645580d891040030400007010740300025103c03d030040c0658800d060203040c83d860800c0010304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 143230467 1250 143229217 143229227
    0xb060f0a020c0108150405040512160c0b0901050f03040c0b0304051020120a02040306020a050c0c0a050d0b04150c0e0a0f06080106080703021603030506040b0a051011010207050106080616 82
    0x118443c88140d58800b640d545c0288401494000c200311010320502d150420041c0d803c10140c014100000c41e01281010a1314011091020980c018800c102d4140700700216603800000b950039050712401440d4603a034441c2021103081e00550301c0500c5102c400000e0000740070012a015002020402d4180301c61085d8030004498900384a09243c003408c0c0500060703041d20b240080086e0804c401c0380002d8101612038443c0d82c205e9014a002c000420740028050a1000084c42400d2000f8404c0321807000840c074082c04110f40440c01c580041118208800003401c201c0c05611904004001c110304001064404901420900172154450301c01c4c0d42041c000642810303d80d80380e0082d0b40a0b0b5a80f0315450b442e01c501503a06a001401a4050680a00c18409256107051071540071074040d99020031942801405d002c100c40c1c0120035140105080c0805000303586402030b860b501c1c003e1a203080a0100e1003450f0007402800307030f804018069420b0841c002151b43c80003600c58043ca010150b00c0d11520f21041d01550 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 143231717 1250 143230467 143230471
    0x3010e0f090316030e090702030a09080d0e060703170a062d1208041d01051c02151312060209100f08040206070f0501140411010309020a0e0405010b060f0a020c0108 72
    0x302c0d84200140003165190b05440752100307100c2d003841c490359202c500006504610440e00c19005902c0070400341e5100e50302c43da90b00d00404402010744508019003000500e098121001903004034000a068000c0501c2000000705061504411001505280b594031014011901c82d989a400c860542460a2851020200588a12600e045114a1802411480400741c04105490440c0284000a121417104182a0760107040710101d81407076040c84100060709003d03d001400c07810807510802c005032282003240d070708004219003543d03c48440c894245081c0720b442e08a1011101c480e9801010898280c0282040740c90071030380368185055003201211504800c501103c0008c0d0700f0380101c0e0243c102000146403050050881240440301030300c490f0b00b52407900c40304407001c0c0c1e1603804100c24090f004200c07a0025501346014030840000e0740001d201070503240200401c95420501003801c000c000d52101103549000780000717440d85150143d80f00f454210820002c00342c09180100700f04c41d171081030a54 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 143232967 1250 143231717 143231731
    0x1701140a05090c0f0c0604060c09260f010c0c06050a0b18130816050c01050c0c1507120807080a0c0c06090204150b09040f0605010906050a1b030503010e0f 68
    0x108245180004201c000940030f090480b045800b0040c86000410300c100030000105513500030101c4d0704082ca0014110b681ca03400d520704100454400b1f0045003441d440000307400c01405284d16802a8800780300d800c007124554554000e40c80c01921449250b0002640c02001e4007a14081025039152203c80b000d448048110030380c451003900d01c15120300046102281c00840e407844004060175149d603144440d1f84403a01d041b80c40ca140e403242d281040782c10420301c20382503400c4c6440c50070309410200e8159241454148a0711034030100305000c0c0303c801071500b90387c296a04486841c185048082c40034001010503958140082d0400d0005035207082e2500500c80321444568603448502c0c5603407a004010312051008030791142c6c4450000e41041183c482c203c001d403a0041001b0341d00c0b01c0300c00070041110751580320505002e0924000b0007040c0c2c0c00890b410704441460a00c1940c13018680e00880e03444502485051907902200c004d141895800800b841c143ea0098961141ca515611071810400c54101d13084 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 143234217 1250 143232967 143232979
    0x30303040f140109150203040210020f03030105040902010c08030705040501090807230402130807051305090a021908010501090219030917090a0512010506031c0c02010302071401020703170114 84
    0x310014482110300c0c400c072010b100000890182e1039031041900107a80d081070101076000b000303120a610b000c030541c00c078001c000d0000300300385a01c03104d80944030301051203290700c982c0d0764822070010769000f491030420459128603c0c6590303103042000500141c01c14082c03e400520580808514040d0001d00041650a205554034003500c01d00c03c00e80e91004220358042d00641c09000380d003c070150014284000c3e0a1400c003508555092030b00f4442040a4401c40f04031503030420060004104002ca6450b80068040d2606031a82c0301e1005200d800c0c1003141d000d07030781e1580b03044000901e0200c0d66000e011518039500d00100d4203c0241421001d0b00d603080030142845200000503030024900800803e0320f400040c101c00110341c0d440f40040c64907400c2d101a00340ca6511002009070b40c0c83e041c04490b15550802c009100e01c491b56a000805c0050030400080c14154002200401e20405100c58120514102d0095694606a00c0c00810a000340d240d00c80c01d1740c041c1d1002003400c1034444e810013103030744002c0c00c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 143235467 1250 143234217 143234243
    0x705030702031c090602070605010810020f0f03220b0609130b060d020f03100b0f060403122a1101080a050112030309020d0206031e0105060a0804110414070201090b0603030304 77
    0x1008010008003c602c14445a488501500042c80c40c0044c110960203814000350310342c50302060354104601804041d00aa1042250700c0d44e1504a0301510306a004d100169512035599008a8481d0400c80c021621800c0300e5189400820900d040054483c1030191100f2405803141490b000b160340c00410028111983e01001444074281200d80440f0f442c001071480f96203140600c08241400c80024004000070346440803042c26060000c4074040005099074003900d800d203143c481030500014022072008102441c10142000309600f44050021600d00140c40f000080600c0e0450010032015802d9000c0750350040042c0429140340f04150403a24100058403840a9079501240206245c0908984c08501c0456840142c1c0703401c40690321640d01100100e80122103104000c6500905038001d07841401c0821816248682c4100c2c1d07280c11650000d080c1801c6c80c00362001078054a4130750849070703407010200c00300406541d054214040e40381c06180007603001c0c0c486c02c061607107074481100c015100c1111502 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 143236717 1250 143235467 143235487
    0x101a010e120a060e07081b0130021605010c0801030b0c09010507060c0509010215100e043e030f030a0f050c0105070309110d03080109020a03060e090102030a05070503070203 76
    0x4850201c032160072050302d80ea411103654030021158030042c00d20841d8441102804010410004142c00104080d68803003840b0003000000e03c01035107803a250f6900c050642c007108a031000003484da0305a28110505540b04c40d42e2188a0b801416020f4003900c0301d45c20406510200c6015904241c103980e04051320071140c0e500c26901004603032002d407849042000400004000c00c003e441140e6036283c2a90380e0b141e6511121000901d0507404084408a00900e84240040e0f44001e0001c2c4040719080c10408509035a80c0c2000c104903403800c001403010240c103000b040d40c0942110501251130f140c40c5207040c880d000180a02d50f8031014008605200d03441000f4090b039040c0550310301c40c1400c296107030291030240e2940b1050b003569000c4d00c4140110f070312550384108200c001c20315112043c0c02560700b0304050707007640c1b0018001c01041c85003220095000903039400040c481c0c4c1241303002d0000f0001c002d0281c00d00418150003580b0484e850031320b651801c07021032225032046048030f016258590046007000d000d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 143237967 1250 143236717 143236729
    0x15010b0702030607140d060f0618060807083301031104030f0209060d050703140616020307121812020f0103020702030d030509071505030f0705090307032909101a010e 73
    0x9003004417200c205000c2240e0b110b81600400000d4040c00c1c2c0d060381c103d89000c0016210300504004480d20071444d540901c0300d203512540f080d41c05805403802d04601d4407408100c40064401c442c000c143c030444110340840c40040e02102c0e0300e140c1420380e010800d14544204107103550103940030003442d0300e5003514860301615008003580d800c448005c0c00c01050a00c66910305180c12802d0380122110000c18800714451a03062181c16484541210494507600c5101e50007034a9204040008056100c2075000c400050710600340c04650304803001e14040210340324545d0304455003001e902240b054100d12280c001c903500c00e009442265901400400c101100360f042035004c0d04004080110794070a07100000742c0b038492144c440a10012503140c0c15541d003401c1c14201745002000344040140300d81000900c0c069100000c010707007102d4005102207003034075003001c6c0f451656000d04002c1e143c045095060002c519008105004004d459410802040c40c00c1a2400340d00c001218000740400c3c8480d2150150342084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 143239217 1250 143237967 143237987
    0x304180e070e04050615100c06060807180e0a2f04020f0702030610080c0d080904050103050705030d020604030512270304060f0503090319180815010b0702030607 71
    0x280041050101100d1081c5440019486410380841c0c58090000b4000248460b980048000c45002889401c0d03802040840882000b001c1c200015800c01a003131110681c840c1002d0285903081d102c1d0117a880d050030461202c003000000006141201d6140d000030005008941c032a4000c03040d08200d4240b0020000d01001180a0b04007100c41003174044080d921440200820701401c00381c203445030301a00503d03180c00300080c1090b00c90303501c080c5d00b48030f00040040d00300301d46202145e070401c0d0039156151140b658022040354035002800c000c00030003001070100d0130304143c0e6000c0e07084448814401d50100c3ea608420340d0b01401281e02003041482400c0041b0301c180d803000c001c42d8085402c0d103405050315642d800e00c800c54034007078101180c00c1c44500c0e400051420342040071314226045090800c24292644136143c0e500d43d80304500f2040e00740302c0307004610858a01c45819190224107a44461150b02d07015800d00c0b5598a100c81000411a104100161108070b50060010305840d6510081642c41a000e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 143240467 1250 143239217 143239259
    0x50403050d0e011e020604030801050d0215030c0d06080706021204060906030b0402070f060b0307150503130c050a0306051b040303050d0905030412081801050a020607030506060f0403080306100e01020304 89
    0x4c1c0c02801e4a03400c1141c3c50020f80103803158002c002c1440c19040c01401039406800007880f0f2840f520107003000d65102c0750102038106055240c0780d529107035003010044501c81c000704040901d04169000404100c00306207041140d901e5002d03250406500da080c29410b114500070b480c045404a007050000f1442a4030030340550744090030062a140e91600c0d104040344d9804400c80c0c5841e242c8140d260142418402c0b40014642103e1a000036801d070a0041d1007404000e20070b5146090219104040c0121801070400800c0058810040e8580368104680604002c80e207489901c08001c5800b000340200c0800c950850f40c055450300d082c01c40081da40c60182c0800001a1a144010312012808004100810b0780685c494098203940b071511000704600006408486814400c0a00000143c642c01040720341d440f82480c03400103199656030001900c0e42c00381184040203e140401c002c410440c48000031405070030225a0701038181031504041300c5071840c8912190043e00107110400c00c13480c081c0240130010711 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 143241717 1250 143240467 143240477
    0xa020307080f0a030e1614030102070204060e1006080115030f0f020d0c080606090604120c090504150b0a0503070b1303080a0c0309061b02010806010e131a01050403050d0e01 76
    0x96a459500c0da50b00601c562082c00000010601211034151041c070380c1c858403038000350441c000e12500c0b81c00c00381314502c43d0051000c07008a0a41260f507081d0304850b42d8a500800820101da160b2001090303880040344d28080e07000d1074080104d1000d0140e10850304a41301e00034055540400300c8401c038040c0c28141f08a1120030f46a2034011443d1510340040c2c20142131006000800980c030a00091036044060700c0039004a00c10000a030071600c40744e007198141d40e80c040c0454081061460700398644901603014180b5907140100784010002900e54850a881c2c0c0118140319080c844410007802401c540b00da2945640b04460800204a00b0000740c216580b001d90100010366032038684032482d9103c4600100007500f490350860405802c1044840501403901d4844968064480e001c00032550102c0d000e818803d4010015030136a1040b2030b003c03421140584001442c03403651241d200681100d00e2209101d211168098000754440c8069604587e002402022030518084003030b2000035a090700141004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 143242967 1250 143241717 143241727
    0x140609060d0603030503090d09050a17030c01060608010e070e090406050907050904080a020601081911220c08060609091314060c0a02010b040915150f060203041401090302150a0203 79
    0x1140ca8451a001507020342c49040e030301d1030041e140c14144442e031301c020710501c402c026040c00700b5207070b02c06003500b6950a00d0302c0840c554204331042d455030040c0c0080001d9582070020100d825540040003e049440c41d40703c0250030346030f030703201610403060000c4030319004290b0724000f5011030b180b80c00860b00004080142c4030354a4658010441c085003c075810b49000200280c4451081d42c10480640103020310009022900441e184106000310040800f40481604905030343d202e54500c404a105da6484241d0002d0300c240005452002c2d2142021400114050380c0009082e410120304845c4812402001e6086c2503640101d00d2424000342201503551450400b2400e1412000b0007500b03002c3c1b052443c0b1a501e510348000b000342903501d0700000c1801a810b0005060009021400d0000c004007180b5000c04d2010f801d01c00c0c01c150010030792016a075901141c800040d826004402001a1030703004100503034000c40c1c1801503030010843d101c000d412420311000d1000d0340c071010024250042e41c078070603a0310b40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 143244217 1250 143242967 143242987
    0x2402070905190b040b041a090f10060507060f0204140307060f121d03070c030c050d0b040311120a0309050c09040c2309180d0201090809120109060f020307110714060906 74
    0x10348610301c0d1f10750708000c001e08000d40c91a107070680551100440c440c0050078507101c0c0414010b041c5a1044005000c00450f8130004c11985070804000c05402340c50031500c950350f54150802e48840d004940b802405803e001140041c8a500c031100300031042d84440c090210340110340b1005040940600941040d0750380c26102c401000d03c0240080e0340900e80566141741941000d4040c0360b0300d80e01552007030240270900d100146591200d5980150541004c82c00c440048500780e04208070040c184542940020301a49940c4d0140d0040c00454060002c8131030304a50712043c4110420b00355009405034101000c10400102d884003071000819103c01075020611000010400c80300090301d031600ba0100103051440b0704401040045c4400c18144000d01c515541c94813648080e108000a140c02011240d8880041c501c00350040920303154000401c114030a11021064029002641c002c000540c0840400c900d050000450809544e080303150100c000941e00c04012182c0c0c003c40b000e9030040e106001c00085 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 143245467 1250 143244217 143244221
    0x30e03010c080907080604020315060d0c030c060e0102160306022a0a060e06130b0709030b150a0f230112051005010f0504080613030203042402070905190b040b04 71
    0xa5941c035210780d51181040a00f507401d0401540008030154090f104010150f070f4001000100050741d5210003030356443d12804034401c02d44800d00503141d6400000000b08001d070b11100722044074920756030703042904034040049813140a4003440c101a25011917043c401301e11580d004140c4e0400e80521f011400390f8149902c500c00c000c12003200c3c080d41040d052141400081c0c02035150048401c40580348600e400940c01d20181d882e40c0018208801c070300001001907006001c1180916003001030301d500c2d1314000c0c2c0d5981c131420703000030181e0040b9a4003400003103464200742c4010588182d03418020600700b601f141d20101d01742040e0381c40d0400920398008542190f07075114480c01448120001400e090030309001501e2041c140a05204114007040304000d00000440d5554000d80c0019881994025a0400701d02d50700413604100c00740303d6aa500060f01b6a03003460000b044039040c2c1c00340c40100c0d50782c4a41804940c01221220303100d00100c08075400c0d0400079130101c0300210b002880059401544404682 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 143246717 1250 143245467 143245481
    0x305071b170102040602070f0303120b22060815010503061b0f0408010506040c09050a030b18030301240201020f25061b1209020105071203140c1b010c0516030e0301 72
    0x2550b9500040902c09180e05001d450081c01d4a43c8210184034a56600144840040d40d44011a40d503540408130300742d51914064500814001010f0a141d03450042c135000801041c4100c800741d00c10800c1400c40d00c84052603550490340000c02a010660350342c05c00340c050f0b80004607145250801082000782822480c00504040c042610000503035250050a2100b280c904044600078000c80200c104825980c5000320400e49a0081205502e44c851629200d8914011640020396003c040008203d0304000d81d1280b891505000700c6051001c44c000d03069080388110030300e400d50000104051a82580700c09520881442500490194441315494903400c9803015040509101011022a00900c4d4820102d0302801c040c0c41c01004007081e0760f80060001c1c401d0b104004e0000207102e40c0001070314001e501c0880c44c1c2422406120141c50700c203564581c942d0058040301403a014420042943c000d051061120901d140d85840345001181c113011317903801c8141c00ac12002c008090030400e46540f0203025483d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 143247967 1250 143246717 143246759
    0xc0c03020a03150c080603030a0302090f0d0f0308010b0a020a0314120108010605031b030c0d17040602060415091713030602040906091107050601120f12020c0301050a090305071b 78
    0x500c0800c90a0f5042c01d403030200382140100721444081c4555503034003200b10303640300b0000e040040c2d5490400c404a070720305140021039a1310104180d510b40c1840078591182c640d00e0310035070b2200840da0704c94030000d006000e101035900059204100c00400a400741c0300d800d0303011f4688082c182c01d01840c44403140071084260800e010345d07510f492040005040800c10781007210904040b422022807207a0100780c1e80d01d114001e041c41150003000d00741c18000509004114214031860796542c4a0300c600300a50f0319803050b1030403501d840658058044c04000340c03107141c140662064030380000c40007c03040700403c0d070040c200c1c01c0e1161002c3d03c0b00000003041ca10007800248001800412401d1428641c0001c940400b600d424000904110560020300086101410b448100302d00740345441d0103050481c81e5450a14000b05884547d40790400d840ba000180242d8241e0110028041c540d1540700c01010341d170100340000e0215906100d940d000500402c03060308811a0301c3e0369000c0d095a00c0e0846c400300e4104031051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 143249217 1250 143247967 143247983
    0x1c0f0c03060e070303080a05070504031e050c0a03020f0906120307110a080105160309030c1703040b060a060219081603050307020d0201020306060306040b0307031506141c030c0c03020a03 82
    0x104200a107500030107058040322030103014010b1540d00e0191444200400003007449695100040085000e17030300f664041c580016107d20b0a000000c4110500045030205440b540b20f002d41c0d0300c015107081e40d061015a90302821440095042e1414031650001c06000c1c3c03544090408001100c210003000a081c00780e002d00421540c1000e200207000c4244000d400c4140f459040a0420203080503007060711030280942e1074009400e0074181421501141942c1c401814040c800320102e90a5000d10b001d1801170b40a80c0580300380c0d840300d008001c5039416030300c680e60144c0c1001c1c0000714001d2100d882601110b001b00c0358070303282040b403840c1039080401c001d00c01c8011402c04000e00c88446d80c100308941250b0b00c0c90001310701e1030130540009003090000501c6a4859a280c0380301c4111600d0030301c2104000c5920107902000c10a6000410000d0b00d80340c00f845020000d170484142c001d02e8040708003805036100d240505013071009500d003141c0003080745401f0785000c01402e400000607115010400c00650207032002c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 143250467 1250 143249217 143249219
    0x13060e01020d05150d030c1e0b06010e120607030c05070506040503031801060f050607030201020c0d050306030d031803050304080720010305010603090c0501050d060509090102070b0619051c0f0c 85
    0x82e14102e0b803003d091606200342046010120307480ea851300060440d00350401e62000003007858000000c5220009152401e0180030680d000c2060201050303015040c07d8a0300c000382c140400c04d0000d008072640b02406903034410700119170150300a87c4445402d4103e4a40145428170944034a132411106843c1190168000010802c070780300c20320105600789241100900c4843e1904000515445541c09602d100d0a8001060801c15000b5411600e1402074076081c0d90750030107107078000b40480e0421151140a401204100f154041c440e00c5041007000c9060400a4400c225880403a466000240f048940341c2042251a01060110711240c00407104105c40840c040d0040d40010250303001070784074005040c244011000080d500c2c041c3c00e400c0d11001e1a00c180c80c2e0040c01400d4000d0905039100c5508000a0400e000c0b0121040d00106999400342031004000d071030742e809000807000c01c11b8801ea41344c9070300740050185162201d2416420741c10380c407450300760b400291100301100700140c40c03c8030b1103514488 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 143251717 1250 143250467 143250487
    0x4050d08130b030c0706110910090302090631061a040617070203070f0312060f05090106020304080601090902031c030e010b0f06070305030414070303050703081006050403060513060e0102 82
    0x741c1d140c0502102d10105007141090507554001d03000e020300041c4019180d52032184080306042c00c0d55180e110041c03c0000030240850090b01140c503a0106030300404861001481e00d04059026644908907006c1c081c0c1c03107000b501801d01c2c40d0501080f25a1420f500d82c1c10010b03c1680307220403403580c1c0b80708441c01b942c0d0f10310782000a040e10100c042402814060b103002c2003403180d00401650144d0743c000c1c0d01c100c140d80c40c5290407200c00100c4014506003034507000010400c0d00002c541d1134203807401912808003503604d0390810790f80da000b24424407102d40e12200051010340358642001e00b2052003c0c048503040005001035a414005100358980080d503100006508801d007401041400941925000003180c10000403a00398441c4030070180078004004041010802c401c0715180a41c412402501c00c03c94883c41c008117036500141c1e041d00051070000c0850400240040003c0c01c41d602d5445661a040c5181e54041c0030701070050103c04159054617459022070f91134025851400d1412000595903401a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 143252967 1250 143251717 143251747
    0x303050a0315060c0b06010306030b07020a051506280e131109070815030a060e0303160201140a2d021903090b2205160f0803030402030d110304050d08 66
    0x200525070000b507601d01002a550000b6042c00b40c03a4104480100b00d41d600401a4054611644024994001c8504005003542d011034600b024510031020b455148400c1911074505031010384115610603841d422020b024130350404210340001d0300c10442d440c1c0303540e142241c0c03d803500300701c0386061f101c05440c04034020080c4490203411802c408581c090340383d041030003004256200081c03441d00030f41c034000c40c0342c0c4075a078081110114041d4001014000c422200c03954030b480c0c0c1c1060712140100c2c41c10040c1c40c2c0d03031a0b0040c0101ca01900d40ba481410095840c00b2001024210940681140e4111088408071888801260314401419100f015aa0304150100119603010252240b0105403401590500154581d030035950041503030b203d21017196101480c2c95040410800c80207045d4811048100c02e07151a00790310b00c6c01c681c00405105502c5961f24180c2c4e49030711088400a5268220b202c10300d00e05405102c01c000480c184008503401c064960340401c580c0c0c43c00700820381e1f80c4a0007007a11581c0641d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 143254217 1250 143252967 143252981
    0x9020f010206160503070504080f07030204050f0c030c090607120c0b090708030f09030129031606020316060e030706020715020c0a03030b040221071e0c021207030204060303050a03 79
    0x288001c101600d04044040d804500c680d03000f4003080303000804925018031410594010341460000d68101405043c8195a210034602c8103d0246060200182d2078007201410284515540242c0900e1960ba443c01100c8a60140c1380d104c0d48440c2c00d00a41c4041061004580c40341d020b15281c1c0369400541e0300302240d031080000d000d20307242d07840a002407150503804030603906010503010b0307059103810407040068050a007900c802c00034040078040491603030101d510940383d0f126080d01a5840880c4030f002c0880c4401e04e6002c0e89016034805c0080c1d80800704180718a000b90b9010300d40009407120f41210083c2980d1054500303464158011640c8000d111000b20604800f00c00044c0c1113207070072654141d144d11410761030809800e25903a4a00d0f00d030f09840d1768045031100408009800080701246092141404d07003610810000b96285003d02c11028809160981c105010384841c0080c0c1c041d40c0c20050390a82001281c80f150080c03003030020060b10380303020b444051403286e00d500e41c95070f8400100030200d03485 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 143255467 1250 143254217 143254219
    0x6040b03031306080a020f03070c0303110306060301030b04111c02011b030818030904050c0a02010f0515040b06040803030c0714060609010b03060409052a040605090a0506031204060309020f 83
    0x20401007644103030b80c4040c5041c02c032100c1e414081c115a030303048200c1c0004d00814080c0701070528000104010345601003c410592846510304008880d04440e5640003400112406074004d2000c000505c0850003003007900354410b1140041014000e509001300d070410705030030101482160709080d48800c640e00500c034552091200102d442022071309403001825080090911494001500e00b4400340c20428001c03143d003500c000d4001d01903030611502c00c0c0170303560107010100d006500c0c0003448100700e049400343c84c0c050900d960700c0307000300304520b030030000108000c212107580400101300000d826078052026520915600b0941c644440e82c41c00d000c55007050501503501c2940081c0c04000c0140d0310b14100c541580c0c042030a140e00e0b580c0355030100d002092400400381c998814030780041079084900c100080480c0302d28911584044000041c84140c86940c052940e000a8000000302545070b04e82c003041e4018801000c03211050b0f090401c084155005401c26000640c0380c160500c107600f0120b0002d010804 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 143256717 1250 143255467 143255473
    0x3021c0e0c210304050105090102150c0306010906081014040f05040c03142e1119030b040207020319050c060708031b2a100f050f0105030f06010614040905070806040b03 74
    0x2c40c040d01c141c483c41507000e04c07414000302084808003a4401c010b03100345030f445040d0452543c1001032007203409030030449902c0d000460600010a8083c0300d81101e40c000c444103a0814101030601c0380300346c04c02c011840ea10b50040d036500f0000d50020481d0061034040e5015041c1da98a40f400c41c2400c90070074003100c1040c06d10b039004404d403100390014201442040c001000c2e01d139102c0c46244000c1c40c0540f404120110005c400406c201d8050000f001d0341c06e180d401113440801c2403000c81c8043c03106a0240600103981504500321000070201d660160440c0b503031041e4103450b1031343c40060005009400500c070540740b500c2c0c007008100c0400c0860360b40a00c0101c044481d9400c040380001740841452203011154010021040140741000c000c0021400c0d003841c50301c0a0100e10001140a801443c0c21101c40c221002850000074040c03c02150010720301c054000035000c603030b003800d9040d140c01511042400c04c41000300400113a4a400344206405003d030344e0f69880381801c04c01d0400054506000c4024400d0b0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 143257967 1250 143256717 143256769
    0x91f150f030f140c06220609060c0204021c090f15050c04030206071a0702010b1c0503070305030903040b070309030510060b0d0e0f0106090624080703021c0e0c 70
    0x2d4901d00c260758800c0d5021901c841c12461042c0c0490a2060014280341c0041020820345010519240d0031000c3d909500e010215041d40daa00071180c0004610881c0d0220302c1c14030203003001d4105034008081d16480742440d20b0002c080038031440103e80c030380882a40c641035410141810840068003400c203011065006000e24148041e1800d0603100b2444001d100b0480018040100820022001102c0c118020004450700c0c0052001c0d0107008018003192040b0940d0b07203900442072445170000346c0b19401100940c100700c1c0660f41510241e2015007006030b58401840002020400f0790f00074541c862080c0d4401350510301d9031500c10716022900c481307110100e05001051201c0045036091f1484101c0f24003002c608039002450080c24203001c0507542d4515402e012000c1510011501b004040300e501c440002d4a080d4171802401102450114480c0014441070116980c3c912076005011800d00c40b07440c3d00c0b0203003842e507604012211314000b2804103400c200c444034141d150603c100080e02801140c1d1380072030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 143259217 1250 143257967 143257973
    0x3040f09020c0616020f01051801060603110a1b0b090a0b06101202160f1103070839031c14040807260f0303040b1003030f08091f150f03 60
    0xfa01000705078252a0700d80c0341e249072010380308000e1a244158080020881030130024401c4d030603606030300e02c8800c156007418400a40244a440f82c080160303504100e140c2040c0b0050011210b8203804403450308020410680302021610180a26028840c00c00003000c1c006c00911701804100c3d80103080e01e03c52241d200d08888000d801c82c4403c0c1e220034140400607560900900820021000300a0207802860700e215004100180740420703010307510045003100c3c1c20a0381d40c00c0140da540c0c07600420740b200c0030300c807014400d40103031010404220040001190004c0300030030010074070b000709503512600aa00e101402c0d03014030fa08034044e000b02602c0e4110061410f810250b140384d031030042d80b007152850b2003045c081076241204610f240e03041e40b50f0101a035040d44001041c0b0359030f9420546040e1542e48010000c18000f00b140c80800080340e40c56190440035a903003400c16a40003500810644403800342802d42c40110760f1030599072804010030900000d8245048110407100c40c0960414060790b10246c9050001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 143260467 1250 143259217 143259223
    0x318180726010608072307141204050d0b04050709140601030509060105030703300903060b010509130504050f0706021b030d0206130c08060411011704020604050d080c0f03040f09020c 80
    0x101c1205418186041c10801d00c2c40300500746640384040070f104010480c10304119940038500230142c40d09084603000c5000084a54141c4030b070784120355014a121100f10300050161003450703809030140007901d4159544170150707804d03a502c802091a100d01544100002d640c1c240c0314050700410f0f5100102120360405000c241d81d07005902011b414480a401c070304821515220a0301d150b0b0494034010000c0c00d14180010704900954003048500b1428102e1280d51948110241c4891050080000c46800f0a080c540c0c0700402000d041075441d4000c0c0c280ca40248402040504c000f40030039802800b00488018101c9a034012185129201342c02210b1102c5203035a002070400e41248003002c48685401c154900b0040d10801c030780c4030311280c2c026281000b080c4035840c154141401d01c21b880740850742c050202c0680e0b002108580c025071000d000d00050115040480c00b40307054500c10341a1034901001910640d01d0300102da059a441c56000040510001480301032400080c840b01c0c42c15810424509801070f2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 143261717 1250 143260467 143260471
    0x70e010509030c060406170a11040605070f02120304050a06050708070303051801060e06010305060f091b130909051204030f0308060a030b071e110318180726010608 72
    0x410080041104141c982e0148004421400e0084c040c980c2c80c1d6a415002e04461407a10815508504440015207464024012411103030190003d407441e1604200041e28980c0101c1c20603a003151080c00310340010b0f1188400300b061a098400103544891501d4100035041c41d054004000700302042c0841c0000030716483c1038030100765041c2004156550f2780b0030130100801260850504941c00c040c000a200c00c0c2e0849854003d50080e0703001c0c4050b59495050140710008962031541149a8100140e01c00003020500b941140c04018001e01c0c040c1c0850f001c1403240d243d604142c1601341d480745000204101001400138800b900a07005082c54a103484845240303002440103001d10145100254040e9281c00e03001024590003880e01d00c0b9820503040082c04071150003603140c060a0440000c40000d030190141c002c040c154480111314020b50503454841c2d64401400d45504074031307030300e04000700e40c8100f00c0c0031b44c4107441a0b81c90301c0b0f4420700c1130703041ca008507032280004103003091b04001405a40e500401071030b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 143262967 1250 143261717 143261719
    0x60105131505090306130c06090e1501050c010f060510080606031504090b01030318080f0d03180c031208060f090609070c0b130606080c0f10050c0601120b0f070e 71
    0x1e60407591003010740d21071042080303699040c014041000b00d02410321720030003403080c0680710f4004819115201901d0001c42401010800380c054800142000c01c0000003049a0300103242150400844200d11420b4402c80c100318000344d500d401092086042c50621070b9818082440d18018606084002c0340841c40003a000c022440c0e8028410f45c900c0c0c843d40c11150032164840740c1c252003076030350341801403034850800c0e082100c20061000004d5100c42c001003641c111040b01022708495082440250020201142c0c003401c81d004100d00b01d4013040f10855200001e40c09058140701c901e0b2440c9000380007003801803071107210708804802c01e906a00d841034030603403051040e51150b0058503004021341b40c070f40719041c0c020041c5182e01c0820040c2c4074408108114644a074005104064680706000d4940309104600c80d00040c0c040040b038194078004d100440b0b14002c2c0d080080c83c0c142d104002504050098004065801c00c4084410410051000683c0e00c2840c1c480300700090708202200421550000c8512 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 143264217 1250 143262967 143262989
    0x4020d0b070306030c03210309030f030c021606080f090f03191b05010c0e0306090a020607022205011505070302060703050a020c01090f050106061b0209040c0803030a1406010513 78
    0x5070098083d50089001c0c6400404941d041741da03034a460460201c20f4017844c0c2c5d603e0410402003001c1e5019010f180030311545915680140e000e4450100d00401030070418500b18414828889004003491541a020345081c1ea21040c4610703002d1b41c1080300002c00361520650307906c03503c40500320b85008415240b40320b2a10308001240624200d04892680d0b458540710451449844003900700001540034a04c0e01e8010b8952002c420102010191078030002c8070b07801b005402804c40d0340b0040c580f100041c030300d80b803008000000240d11030050f40403035034168500c04915a620001401000140d50801031245a41e150407441d10080303940083d121500a080e42080c191150081070b0406500e4054541901d0044d00821080c1210f04001004507034500d000d0314554600080403410350308c110102880443d0740004248884119801d002c0204401031040c5c0d10004111804201c40310144011800340003802c1340807400003880c04503114521000340000c1e042c02001c00c4175007100114617503504100c480544078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 143265467 1250 143264217 143264221
    0x10c0302070b280c0c0b13090c02030705070f0806100605090f040b1207090509060702061501021e0c03010c020718020706090f0c0801180f0b06040e0601061106090604020d0b 76
    0x51284412203038804058003d100da000200c0c0070380d218a40004da280103d003903441c45592406402002d04c02ca100c8005a144140c80900c0f41903441d81100511400510440345440d9003034882ca8104841504081c0102c100128200301c6031008010351b40c1c028880d4a46207051900c0e002c0060418452552854003d102e01003040080b03580300c1e0f01c2046116406070a0306c10600c81d40080756203c1c0c20300e000e940c000920342800318812803000541c0c20302c204042d03001081c49803101c031b44001000940719411811031081400c94500c070350060701092080c0305600c00410724103404104040c00d4030203802d059800c5501c49001001100727801c03424034940c20361a40e001a542c00c0c050070484007070400890301402c05010010382c0020400140d124004841030324008000e01e9644141c03042042c218500090401011803030b962004c214031710540d503013146000b003002030009110400f05003081004d03442100800ca005240e0360000c1810f100e160360100c0c58402618a5141507400541e902d010080054107030300328980 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 143266717 1250 143265467 143265487
    0x1030b0f09090f061005011e0503010b0f0403300c0c12080d2d05040c03080c0a0f0305090a0f051503100e01180e0105041703070c0204090602040302010905010c0302070b 74
    0x8583d40309280d1030a460107450600100804404a485403500046101e40c50f10004003003118801c01d20340c03d507030f05d191569207820200d10741c54001d9550409001c1c000c201c0003002619040e0786030449030031810b511440985a100710b04803500c55102060034840d03040c7c1a5000164900c43c00c0c400c2c1d45a4103c0c0161007525414042d41c01e00501c1c1034003c480380342000c00c40d0801110700d4500c03081384001900f410100a059101020b44000313075002040c10081820600c0000c170420060009480308000b03c174400482031700c030f240120130816415404034000141050305824188004006420359a902e0844285440d02203040092a29a5001074010201c046080c6c21103c00140c0000c007000c0e100e640b0302d56110030300c2803203a4500c0282d141e900743c40c100e0044c09030704041c09401d00c81c07500401010515000190b0f840ca20750b000403c48810001d114802c10300603a42d40c0f165104090047c4801610381e1704500c009024502a900040e06201d2a02c070100e0010b42d00040c01400e0304c07040598151184d0304c0c0a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 143267967 1250 143266717 143266723
    0xf1401030816081b06070906050a0807051213020901090e03030c07060b12060a0614091302120304090b09010b1606020703030b060c0307060617100213030c0b030f0601030b0f0909 78
    0x755008022040c00610440c44050b4a081e0380b00502ca42000c0d11070303d844011b41a03034000b46601c1100085681406080c140740d002c0c10135158800443d0074000c0c5829100048661503490895a001124450302d03141001e5040c00742c007290150456941c104001c0c00000c1c3d0340d1b03649010003088011440ca00140040410544d03800024100c9005841000e50385c010400c01070b21402e0448140c03080c01d282490010344085802e5840d40c503007001924007c103540707906500c80c003030f8019088103981042000749258000581000208010002c8480004801400000b0844401b20691128480170020309ca4030900582e0078858485842d8031030320043c0d840f4036601c3c081d00900201c0d03010310750003403000ca00281d0744d403804030007400c13410300c034500070002252510828034240e0a085501a000c0e40200103d0351021216802006080c0704c12122102c100d5a130b584035150102e0304d4025103070541000c001c1c040b208850190450b041042400c090001040036004142c0c4403441c05252441031512102041c2461024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 143269217 1250 143267967 143268007
    0xa120f09050706080910020702150d0e070602070306060e04020a06110115060804060e060106050d0c2304030b0f2401050d090b090c010206010308030f09070b0c0c040f14010308 77
    0x81e06840c0305660311800038040010071102c86105025007180d1b41c640c0c0c1c0e59482240d40499005110b0802c00490411458194100080c071410856498968503118002000728030001c00442c2c2c01803031103e04600c1c000c415200943c1c400b42d55006503e040c0710059481c10b900905a8840c1d03d841c0b5403019241c5e80d014051310910380e2500c2050681080402c070264455601e52259028503070030b0100d190090040c59480109100c2d090005400b0321101001c40b0458001d00c1c2000303454035040b404a8885500000c1564007002a10000f0f00001010030810105005d003651006100b07030104258584848061051a030203000b5140502c0e59091103092a8004c80a1700d00c014a4161308104280d5a4504592801000e41700c0201600c28560300d8445503100280d960305884e44036031600d085803140201000219030142c50a01c09000b41500481c1e1041070002800300742d05c2c441c000b801c030712a40c01d00344070445092a01d1001c0307903814000300f914602a08603406044a034448222940c0710b4000b45100182022 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 143270467 1250 143269217 143269223
    0x5040c090c1805100815060c0f030306100809030301060f031b08011403010e0a02040f0b190303030f0b0609010f140f0d0501081c08060607150e070b0a120f09 69
    0x40c12076100089944403400b500c0140c4000d00e46425070380c032907040218005084042400086958002803070f203810074201107102800144c0b8180c10855404170381420b180600750140d049a10101c1040b80a140c02d1800200a41040c2080c0d20b00e4103044401c20388910050150030103004480104c0e4060a1080d809415145ca21000050604003960700003004000700b84601c442c0807013688420000d0b40b40601c50002202e00400080285114079424070000d05890411107100300d40c0d0700307042201e03522002c000504040b000004c0700d201606510300030302180e5244150f0400310340f420301c003411240c43d46000c0f142082424242a010060500412030f086445031034640080c0d400850800c0030910030b20060f0100d007080300424880c0341c0c2c842c2d0055684025603000201c0c19620316a01d030a051b40104585500460050413041c50010151941075451180c0c1c12002c0745542e4404035186660010b002c11000780000d801420716021042800070300c1e80c49442107003184107903a644000c0380c0303401395400344240c03d038 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 143271717 1250 143270467 143270471
    0xf08100e07030b030c040e030703030b060d020a05030f0a0b09070810090c0c0501050112020d230a0c06230a05090103090c060e100903170f070605040605060a05030109120305040c09 79
    0x25010100802500c0c11002113802440b408005982910301760041d41c600005402c021828181c0544040b4043c204051106070092402c01c8110707800c248030300090408400c951142640c900300b1440b404800c41005080d00c100f0782c40e108007400c555448104144d00700d09185000c502c952120303040e078801e6060a030701070081185401000050320f50005450319074107000e4802000244e9a89011103070301c0b0030004000f54402d02680304c01c0005240c0e03034400c2c400b0703070b00010716000035200e007442c040d28282108900792810300701c40108004c034690100b00e10f02400340c446c00c0816007220380c42604811b80540f503021401d101010505c464143d00c6584070058840c0c106d05a1241c131692402c0103000d008000c4880c40c068048103083c520711500070071114040703d83c8030700711075100643c0700c7c18200f403500401803001110b0010400366010072001c2c026030707003e140500e40005060408404000240700d00d44d100c0303800780e4140300d954000300e2003100c00d21100c490745050208299840b442c10303150342c00340c1d5040701103070314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 143272967 1250 143271717 143271721
    0xf09060c0610060f0e0f0402130b0d02041502030c1f0b06030408040312050a02280f0506012c0610020705100e0a05010302160f140a081c020a0f08100e 66
    0x1c9503500741074200c503c29103800f0380304280c2034411600c05420010080d004034541143c91441d0403e0384c0106611a00202180036080e141c0090480c80e030700c2420414081c9401040900c00790369400010038405229000541c40d03c0310790441c072a215145040800a1910745440400d042840d13500405040b5100411065891400d4030f84080507401900003a102540030419040590b4001d00c02c0751100c0e20190014000915514415580c011760b888040102c8010201316000159041e15a00c0045204401030300c02503040042c1c0100083d02d021247c8044903540644c1d0100292074031425400860543e540c070912203740f90180e280c407403a40e20442c5c01407250301d51007100780d03031000c60180c000400b150a20103c0c4d9540004405a000720a00054144444050000051049003121f128107100d10710307003203410b41201c0b0160308040c0382a0003906d04d280c0026035401c90208981c803160405444100440c203114803104020901000002a441485400004113038a012402c2d90307a0018034905821500314 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 143274217 1250 143272967 143272981
    0xc030207060c0e090c030408040b04030f060c080c16020301020702061216170c1e0d0905061f060804030201090803070e030d110d031a030a050a14070503030f09060c06 73
    0x29805600306403045460402c01c98041c92045211420408004040089030344401c03050800f16070010b807040780d02d910108000110320601802038401180514505000040d40d401c0c01803d0394501c0c15900d0402c1541c2c0b041000000d100f200752180440c600007040c14032201440441d00a02c500c8802a50002011a003210000505148180715040c01108201d00320241d850030b8a1009000c050307000b0000348200080d2040344498094402c0c0b040ba8405800c065840075003040741c5620034040d20300c85584404003c01400400c110082c1c025845145454102c100c0d814802e0030b6010900513041000ae100c030210341170510035080300301b036243c00c03c03c6160760342401034028008080b482c006030b002e4003520001c000d0b43d0340541a0308800070002c4014200b485100e0804500514110300c52a4048454000480c102e460030001901440c0c85a4000c1000d20314908040e01080070341e44003050281e0060000340038a80b0701005403142c0807940340225854410b00d00c0065410c0c023401c849204035200f440300304090 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 143275467 1250 143274217 143274221
    0x90d0c050348030307050304061401300c06050f130902070c0501260c040314010b0307050a0b0904020a030b040f0518030702010c0f020409120201020c010f02120604050c0d0c03 77
    0x40c1d0300e421450705081c40c0070950401005401c0c1c035482c0c06541c00500c0000c1050380154011a4418070507480058040740008140d8000071017a00025103286d0104180d404072049030004021400c03d50070704403000742c41c1d552a205400101c0c040c0d08100440812842d909110540503522043c0c00440c01d4022a81c803148250000e400000080d25991100c0c1000034140d406003181540b0342c4100001c20000c400e80280801540300003030800c0074825030410000002c00c0006001208035450b0000200d5040180c00c2050300d03040150b000240b107507034100750420035075012004591501d402a640562281440c100c160300a02c1031804035504642088204075103540b80d070340518450400300c4000e0100400301040c1d103680340140080240460400c80c01c2d10042981c40c940040d200e4402480401c1c20a15940c80c3d90096400071824030150390046050320440800380109440030310424000c6007404041c05501d4841040540845d0046a42d80f001c94805102e040444080403420f04040c03001d49152040280 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 143276717 1250 143275467 143275537
    0x5070201020d080601080a0b0a051801080601060e090403081308071401050106030b0d080702040e030a02061806040c060804020103090602160b0c042d1a0903060906090d0c0503 77
    0x30050040014494490b8000c9000500590042c0d41d001015030301d64110070020042d19030019409688080000b945690b80804003010b00360441d00000603500d4100c4a84c500201038210800348280c1103c5070b64035455a01040760300c00d4051a018025440b645c2c801c0c43c494609103005071804800144020601000001c0c00030403900f1131000308182e83e079038039003217049506000080c4d5008100d05200804200740a0180045030300050001842e1420b812039186590301a413000030145c1c00c5072082001d031044660b03803060006004030180c6014541660360030520007c6001c1d500a012100e8041425640320340e2000c42d00d203902074021075903400d0046400080100302c2d103040310350007071090000d00304246035415941110001070582900741c0213000c21032501890969881c1d00c00c403e0031800216132a50501740c0255034084540301e603460500106040c106200106130340c585500c14002d22540007000030316140c0c64a200c1c0f4010f1401c0e200c52903c1810f511400846031601c000318506540310400e0417036078030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 143277967 1250 143276717 143276719
    0x5072d2102060402060d0b04060f0e01050109060305090c120a1202060a0b01031803050a050d02070c03121b150f02031914010b07020108100e090105040c120b04170405030706050702 79
    0x229140d9240c801265101401c0740e009401c4141440600c0c0e003c41a0340004019030002840458903e440e03080c19907000d4034030303485402e224144c040101b0040d60490301c0c1401402c000c3c5000d001a16000d1169980c2c4c040c0c2e0740034076004030f110745440748807482c00740420700d078455200c1645605620200700083d41e0310320a5960075212440c5c00c0314031140b90301900c60444000d2700c0c111100340c00c100d10b03201550580c200e440344006010b010408800c0c200454401400220b21400c005c011181c210705080c941d071000c824070344042c020000c8840400400c14a0700780f1120358090b610034070780040700d02c0f40d101a140c41da1020703c2840c004000d1000c00800c0d996005001020a039041001c145001010990390b40203201e103640d03c02c002c06c102405948188141340c0d06c07040616134643d00c0d41d0f50f4003054110b40303c00c44500900ba5907540902c4204426094490010061894138107180c003501d03102c1815189024200424888403041074041d0b0050000950f401003070010240d039605540c0707034400380156005a40032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 143279217 1250 143277967 143278013
    0x3120402150a0206010b0c0309180103030807090308030f2d040b0601020d090b090307030c060c110405090d030207020301060e09030706050106170a09051c050405040e07050105072d 79
    0x465480c5091000b500c0844003240e004104503444c1280041650303000061104003030200b08151f4055440e80b80940c02d40c80c50403402c0358210f42c5581802495050050702032404c00c40c214900304041140c40054940200c1182c0c11013156072622640d2100c16040d01e02580a40c00305c07542070607102488118214171842c041d248045465460000482e16000080c012102003104120140003038013840025001d481d40c054200d075160340e101e4544000b03400c4c41e03510820004080748103039800c02c00302400228102030152018041400e262501a8482c8000c0704d9203000c1540c0440e03584250b6400b50048402004641c0034540e0b2400d1110030a922540400d00036600075042c0000000c03110b210380c1e09200f54a1b132001813144503445d40c1c10004050303c11060182e85912600030f600718205000400c8a04040c110748443d5510f6181c801844140d803880d0244003141c5d00509030801c1140d0708201103c2d461580407a05804046121a503550002a03580d081c0d03a42c2d4050110380d00800001d40d000311b0080018501e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 143280467 1250 143279217 143279239
    0x70f0504050f040311031204080a26010902130b04030c0602060c0304110603040201121a0307060201110a0c1407060e010e0906151c0f020a030531021203120402 70
    0x500096900545400b103410346800c0000f00420700c0740010082040e10721044d20718164032448100c0094070151030075501e40c0c6d40040c5400145412a401c442d070007011b001e11503004e000d100c03400c1012070414410484650340001c1c0d00900828195224005045d01c4d051080e04c0740d8480c207015031499141d008203409403107024040340c600c4160707030281d0788159400145015040554418041181c2010340124144203515081c0c000071001801551960105107003000305140f40324040514240e8250b11000642e454580c2c0d02c803903002d034482182c0d200700541c201007000b0361092400d00e50041c031500f84039801e0701403854040b5941e64861003042510109a0b50318480d460f2040400c841403130107440b2603902440b600c059804004000002d084094203980c403200d00440502c401800303840c000c02c4600c04480d800101341241941520843c1d402c8081080303810100348141c400f400380329485180d42d030780306502e000d024811943d521040c1c903411580070701540d498040a410f210300e00301081e00c0480c420410514 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 143281717 1250 143280467 143280469
    0x20a0b03012603030411010c141506010f0203030c070c030804092f0901030e012405030609060106020a14010204050a031a09030315061b16030501060503010b060a180e09070f05 77
    0x4400b00c46112850007662464607590f0720820a0b01d190288179040c050300c507211402054940c0c14403440c881159010b0f20180300c081040d58041440242020f051021407600316100683c00011740c2e602c030b14640039196030f0710081d080c200400d00640d400107046042c001800300d40c8241503000403505404104948901d4000445400f8071a0f545a411580c9510140810801d43d88250006015607860500001d0580c410312a850303901072130007010064a9482f0030080089007002c01c0030641c82102180908404d5040c80d50007925988280c101401044440400003183c0c1020760440e801444002d2010781942d55925002c007585080c020b84019401903d000211504e40100c203e03403040440305803000e01c0070071080410565400c0742c034901400b0b1148003d850301100003041800c040d40e00820000030240c1c0ba601c2e001c0d082d00c5c400d41145010744d05142c0c11400341e4036140b007652440d015a04202c041c10301c00700d07948094441c440d07102c505594850f10034130100110229041080d2079040c9103a01406458034 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 143282967 1250 143281717 143281769
    0x60905061206010305130204180201020c030102031e042f030f01050f06040f02040506030a090c06090302180901180602220e0a020a0903050f15150a03120903020a0b0301 74
    0x103141c2540405518000a940b580300750300181d07104c44075140480c810803031034022804649030843c2c20350004001041004c150b41c0c04029020340e03180704034000d501d90300d81500803c209104640180149150003404107080185c166800c140c2806a81c100824904828260f1442504030140390341c0240181c80110344031450601540384a0099103d403622692184803c1c8402403028071190000355900344004625907440000460040d0340c0064041a5600e40b4107099034248032540c882014003504000410050300e07556900c110f0074030500c164603217075924815810b0241200902c0030141c038604a40e40000c02c80b1a0703020f040e403110b0548001c2d072001120183d402d601c450600404515410000001c5c188a0550b001808000360b103151100c40702d0b527680d803110310b4480802c020221a8000f100a041009220454241c0c01401141c002001105d210041000c00c180c0f13010107000e2468128001c0c0300300d8020000750000b1540944440350082c1c0d5140f070100c00350401e028009111010706006105e4114030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 143284217 1250 143282967 143282977
    0x11030a0c1809021206011703040806070e0109030b1801060602030903100c0e0901060905040b1f030b03070b07150506010f12020304060b040603050607140a020c040b030c03060c0406090506 82
    0x30000480269040080c0740700411580c1010064003038a42c6100001602c9856440030980030f040024845941003000026140c1400480c3c4080c41e03105002c1001070717001c0050280e0704140d00d4280200700440c8040105d030000910380010301140114001c0c0880e103400e1284c0000c0088502008001c4687c0701c52049850740308242c00346502d50b0044c001d40b1107180440c3c0c483c0c03424542e282404020000b02c0c0c400f00709001e10907484000850801e220401180c18903008036020f1950480740c01c0041048042c0215102c00c0c00031000d010181c1d200034192098070b0810600c0b000d049040340e9151500268500605000140001686040d04081c0494525402007000d17003994901500c83c0241072600035091002900014015144540c035081100d800b03894074072810740130310301603001341800f0310701441d004d010340d80d4074a9003003c001c2c82040f211040690110384070b9400001100c0110304203400c1d80c0040d152107000303443d40340e05015181c10b00210f00010b4006204031461038482c80310503a0790341c080140c1c5000e8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 143285467 1250 143284217 143284223
    0x1207090f1403011401081609091208061203031602280f031803060e0c0907051b010603080a0806181b090d0501140105040609151202010c12080411030a 66
    0x8400060002501020000c4a540d0010b0300000e040a140d0012840e5107400f0790102985822494a500d60603681250810107440007950502c81120a40d030b602e10040d40031503140041201060100e40076a80d04507c1020900c8440112600c03070800c24540c0e14001c0b4099070203030252180c08005d11504241703c19170041c0341c20807070008503004c40645542d600308d00d02840c12820001e076954102d11401000c034002000d58010480019454119100302e4034141a1000c520b1241444e48100b20696610404843c00d180d1040403a10440031800702040c0500119000205618004a0058201d6505c480c14500c148802c803146090300603080f1010b0840c501c1034400d100042c0010450541c00c9900f000204a118000303441d5802902d2561603150855001154044005031070b0303801041540361a001d0078014180031081003000440c2540f201075020658450f121a010f03d0a40c40e40a682c051070306004d03080e0f048404048a854580401851680c0882c3d080351310f03e041950184050a0006822901c258 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 143286717 1250 143285467 143285489
    0xc0201150f2102030a06061e0b120a0e0c06070f1e0f0209070c0203060f010e3108040b03100302030d0507020f0925020c120f03030a0207020402070b0705120709 70
    0xd103070b10024802c007010440980e014428044d182d0300107032943c031410008219002c0d0300844501b0029400400c41c030103600102c43c100c0c080c00000c2071401185419070b00624084000150500d4a139002410301d10080100d540c44000481d2036000e016801c520303840c04505c030301d408c0d0072042282800340b6000f000d10080908140160700400005052002c401c5400c01c110b801d01752400e010030760000345044011189050100ba51000420461400603109138002181603180d002a0358001d03006035031250504800e00d03020316100d410005215140048501030001505e5059880c60224450500c10215202c1207010303101d05070340340035210300c68410f407580b040c2d005007002e01c50000c28003003002654002d85040040070f07080b01c0174100812421206042e00c00140c000e088004900c20400200c407026039192191074003c0211b800f200407010081300d500c00d111032001601d426650021070024080c011000f0032381c440b10000e0008403600540034002208620001c0b5100c2e6654800c1150500744911031180500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 143287967 1250 143286717 143286749
    0xb091005070f0f05070e0a09030f0905030a1b15051308060f04060b0103060b03070c02010e09130305030c0702062b09050606010f02010b0d12021006060f050307030209040c0201150f 79
    0x801182d0450000f03400340c3c1c1224000c0c1d0b2100d40b060b00c1d14030256019003086070741340061800c06402044845203040c1508200380480e2621000c2602c50700d10100003080006072140e49107034080443c202c440a01000207162a50040145028090f41e101c114800e1140c410310340c0014281000213641840f03114903e8515141c0c1e169981c40101030170151070b22605140d02e8010200d840c18005010b1807040320565150030240c03407640005401d0f152906d081602403004d0341c082044020003a00e00100e0664107107480313543c030f503240c0384428a203018643c9c000b5480b030400544840400c40c081040d0701c0119801e10071101d0310b0840d00b0031204a5001000050040d0440000641c0960007006118002c2c90140008204c4d81c914000182e11040c4828080703e1514041c2400d40b842035040040000009000718208503a81c04c019014140019507044581004000400218072074441e8042e1200940090000c0c00408095100640a8664a1003a00d113000c0c06120004030000f64074003c07401c40303001c0e0020503801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 143289217 1250 143287967 143287973
    0x70f06050403031202090310050115030615050306010908060702030a1e021b13020c1e2a0d05030c0601080d03090b0a0203071e05070303050c0301140f190b091005070f 73
    0x1c1214044002d041070350034000301d03106ea14248505008902c01090028003581400c8080f100710099490076000c01d860500c040c0b203400300c031140701c000a88880c20000c2d1a569080012620030f9156000740545004030810308c4000b54000011b000400d041e900c0c2c1d00301581c0c2e640003d00b00071a40c44043c00040e8009040706000300e011200920704481c02900000161902c0340029059911841522032258070859680803214080b0b40c12420000c80c036809082c41500a4001050880000c2c40050700a80c50b044201010307525040018190b650040c142ca8075204d000c0401030b129002481066500e0040010100c4034a1103403041e0b480c000e40c4011191616202c1100c85030003900024020410710001c1405c1d9000984240c10f8810000a03541c1c5960391540140780c014180e0708042d2441400070000d10040c0490742181a03003420003801a10419030300c80d085000108400c1d181c086054201d10301c0301000c01c07280c1e4400010409007000340e4001301d08050b03148084580b803060703020150508022030450400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 143290467 1250 143289217 143289227
    0x20a050f0f0103151a07060507020321060d020d080a030e0d050406050c120c0703030201180c0504020a1e0c0201080609010602121608030f0106030f0905071a1e0c070f0605040303 78
    0xc41e9902c101d0f0751103920b448144006034802e0b0044040480745c80401d0742410000d03280241d6600541d207101842c1400807040c00c1c4104d00040070040300b01d01c8581000511641c50b100408001070350020304240c0549154103001445622200784480080d040c041500f50742e050024a44039010115034449240c28030f0b0810484054000341402d40050184040c41d2406942c4440548440c1803c40c0161801e2450751030040e0848507201d5400307009183c884500740c04900044c0840048810964001d03a80300c007080750490f40140c80410041070303102d004007254061035100d1080d1440c203100b03803180f03003198035000b003000042d0409101f40780059000c008140b0384841100302a00f03404000400c50104500c040e0340701c10301504102c8912014050000040000e26810f0040107084111001c04000c8071109440e900d4981e8000d0052041740c4103c4080991003090394822510300c00341c1d03140b0742c00f54000b00040c10a0b060780a0705103617a151041c0e080228401e050035698504441d19505c4d481d181a14503603003510 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 143291717 1250 143290467 143290481
    0x10c1d01090503060c1c0b0112020f090901180c05030f010614040306052a0702030a111c150b0109081b04021207030902030127020904020d05030d09020a050f0f0103 72
    0x4100100200001040c3d00c081140e030f0700802401d641a500c40280350300c8200022240304078440c0140c200f0f038816440c0d0340c00040d00400203809a401503514290091040d038207100f007207025074028075024000a15465087d0005010480351101448190440c140440b0795010580c0c002c07041c121048010007a42e805008440e83d004000708405007855925100c64048070011075982c114281a148001c072240000140c0d05c024010304500709040075001d801080e0340e500600360040c03017590702d070203000c509035100d1030040b0808540c1045005142d40519054054401520207030341010b040c6007580300741e0740c0100c9008048d620500028444260804002500c400040b00c41c6600681e00b0012048031321180d03500f4511035442e41d10046104c20350303032040c5800c455503511940350404101c42d00240c480c1c1c0340b10018003920f0f01180c4081181e161400003d800700404100109a44400118690a11516080f0178109402201d00704805956001071141e4800c03042c900b00d50109200a004021358020b6200d08 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 143292967 1250 143291717 143291719
    0x40902090d121107350c1e1806060a12110a02250b1803070801020403051015060512100510020f010f1b0c0809040203040b18010c1d 58
    0x4407103004203448880606058040303850004180c00745220042600f0050040104428101c0091340c80c0d441e5514803084515914101d10044e103a0141082171000308101041032400619600d0001c0c2054250340d0b446d0199075506004080101c8061106000b00c401c0798800c0c40050300d0b161410440d0304044607139a900c28070aa000c00c0e50b50f00b40c4030014455901500103200150010401c0d90b080e01c160304241c001041464070115842402840344110030740030390713400c0c0da0000405080d844007000000d0500510f40c11800c01503101141c000f05100000a00c0c0101a610309420426101b0040b6a031a40841b9070040310b0120b4401c10500d4409a020000c0326030040c0240d424084090b202c500080b0b11a0b0820718060060740106130094120100384900e0b0f840305c031911002c1149240348004c151510410303030285c1d400d001c020a0f0f038100384001030003102e1661030010400c564a2510740b4107000c0480c0705540300c0000d00a0322502600440c0c0c1442642d0550f4100d4580c40d50659840082131240c4580034156 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 143294217 1250 143292967 143292979
    0xd090509131505010501030509060402010504090c0e03030a03050f0108150705070807140f0c091509040507031208010906092906070506010b0702040b0907090608220303090302060a0c0504090209 85
    0x18408100d4000b480d84070101c000340e000c9419454900018266600541a282250010402c0c4401030381c2290449040f5041c0304000304a501002c4019660314400030341c4107405000001e032000c2c415034103910140c40b4030204211031480c1e907241c1809917524045c0c26150303040301291002285010740200050800d0038806c80780d642c81c4ca081617655084a8800078500216940110f0803060352000a01c0700441c507400540d00da80d841e1038036008001d101100a4462030252411102003400e04c14207201c40805580c00852003a81451100c0008100310000d206540c80c0300d01d00400407484244030700841040b18041c0039440d85482e08030741c05142503803800b951a03501640030003502d0b00246003409050300078076184465507103403c22030050206a41500401c40e200b2a810010440190740025460003964614034001e002c80e5501034003d0021101d24007005195000255040101a4160850219140b00781e0030342d0303d50780b2015501f0701940c200d02d8a00c03020a0b0240010b016a44550780a030a20740300050035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 143295467 1250 143294217 143294251
    0x70503030126101e090311010c03090503030a05131e03080106050c030319150b0706180210030c0516080a14040f06110304030b100312080112030c14030c0a0302060105030d090509 78
    0x842210304071003045007c18070303140030412082028410340c10314051a0600b03200a03145a80c41d15180c0c40011f101e1120341d50b84801142007000e1140d500c4405951000d1145400c50110000301224440914201c001980c80d00011500d10311130402da40c1c103071740444011800c5890302c0d56002940411085003040017995a480d010f0005c1d0420004001420902001d07503a40d64142000c4080d10000000881e600404190a200503111508501500849480c000800707014201089416206e040070141355810600040024014030a0042c048000c03252110118100c040c10034040070b0141d03100c1e00308505101c42c0100403442c060902c022410060406580c0f5003612540c070513285400541d20350b0b0038116445028000c02810000c1c000f81c03e01d050034440078543c1361804650320007014100080402101d000788d00208041040c500c801a0301f03040070f40e5190820710315401c1e40c8440101041d001072003032600000385800c021031994400046540c91540550814040c0818001c024003800c10001d98524 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 143296717 1250 143295467 143295521
    0x1c0504140d0206030705090109050a05010903080d11130501201914030a0203091306030803060d02040207021305060102070e04020904080a090b0f18060a091e080307050303012610 78
    0x402944540a81d1b182c550300c03042c054000502d030b0310143e00305a010b217003404401e12841c2c1c0c000c2c601608403070f4084210f070343e23400c80c1c460903c0c098000e44400001410000c6021022642c4540d061025580c0aa0f9030052044c802c1c142078105404d0001d17041000e40140c40c51040c8405244510300d00c140c050401c08065035030800d0464910f034450001440140c1020900751110301e000300308003602e541c00040a03c0014255140c5018034400617205912a5044441e02011910360750159a605a00200003452180c440d40c0c14002a020440300f65005000728a0f022440c15440001d4600aa801a004400d141d80300d907941480360b404103004109201c5000b00c0000c4031100741000340700c2c44001c40951030329007c00c4401000c0c0192880b8070b65126010910010f12100e83c000c110350121016074801602d01c60b02c0400400c039461098102600c2800000390100602100000850480d03a01c4c0c107400f100b81c3e1484808030503070300e880c041000081c6c200b0801c403200200182c00c0781c0300d180300c00340d5148007015103d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 143297967 1250 143296717 143296729
    0x2010b06040305073b070908011410080106240e09070203120708010806040f1103010c0801030b010b03060112051b210702030c15090a0b0c0c1c0504140d02 68
    0x580100c03442c2d84421300502406000808040c00004919191503000c040c00d00c01d04a03c880c260070146071500803100040c100c0344203c080a0007408010002c01c5101400760020100303000446a401c00388800d2100000c454005105250031601880c4010741700050550040114105a81e0404104aa02214201c560340e4460540c1d016880e103800969a8061010b07a070308034454020142c0090045100040040c0400803890b2a4003651050100c41c24040e036180c40c0380b030f1044d81544990503610305004000c00c00d42010701203069138010198040d207607aa85c1d4103250248401c031351035400a00008444002c10007107030480c1c2d40014883c00c000141c181120020095a000841d0a00c9909100c11038503201040c0c1040f9190400c0031440603500e06174048103000d5a4080d0b01584003143c1606400141c0010018030007080605c1e131014951045080191903070b41c81c1d03040f40200300e49602031000458044001040c0511040300c8588810f0b060600d49500f890360308080b1442290061004011080181e43d40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 143299217 1250 143297967 143297969
    0x8071103010c0203030108010c020319180806090a1104020403030f05030c091e040c0207030c06120e010510030317060904021309020409260705070e090a081c0c0305130303050702010b0604 82
    0xf0ba0013581c903585410100e60a60b09096400f0b421b5400800c000000281203228941038031800341007201e450314910718480050350440e84415041d0181400f80201c2c4c00000c101c002049018030081c1003101c002208010413072080d844001c010400303e51501e200c65024a0145034003443c0d281070700e0b04140d0010041240d031000c0300d01003520f8402c1000c0c540172034079003442418030300c54643c4020300803d41169600200d0080c14011102413004410140011403281c0d0046070403204150000c0c002810815504516499903000480218082e0070340358031928608005644260001000390340c0c251034ac0d4007884151400171001012960700c070414940980c4850181c0620144079520440c0508024141190001407100c001d03c4000c17020450000410000500181500c4141c40d8442194030b80c15070091404610280040c100c0801203500e040504014401030340381c00d442d403802c2c4514800400200c0848504441c48202040580c903a003010a10a900c00e40c0c1c031a481d03000004103600350000080468000b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 143300467 1250 143299217 143299241
    0x70e161709060a0f0b0d08030613090503092b06180503071b050a03051b0103230a0b0109080307110a05041103060a091103131502071407060216030807110301 69
    0x1c80c40920203042010b10811014120f0010704005e98000f40d03000035001d20100700c003e0a908400700c041110380e510481c10304042c203820790041101044a281444d102c1c0c000c03050061184065042402e041407645000303880f010404040580b803117145d42c0d1168010f08140c507110905044107201e0f8400248200700030440700e40201e0503030f00580000c040f00c2c041c00340340740c10040c007aa5184208000086000402c08943c111480b50000c035001803400490082c81d0b171003501d410040d46002e990050061001c0c000d4080c0c0440c04061000d4a0048015036000f0860b00c00c0f18410b50040120760086200006585200c5038014031404411b0798880001d000d07210011420081c003c0000280708092805c3e19210f0f00070300c01084144806030100c40054524040140443c40000801e00c3c10010441c88426100e04242c0c0040119140c00817401c1540c004500c00c42640c00500c07039070a02081003400091041030081d020040746110b035041d550341b00c2c003c0e00308007021110182041840c8009907802c0c0685085812 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 143301717 1250 143300467 143300473
    0x306041203060317090f0f10050d02070c03150b01020604080316020c040203010902040e0108070302010e1201020d05040b010302040b0f090130050607090b030103080706050403051b011b02070e161709 87
    0x8120010001d4542010890078454000c1c5000c01f0080e84900b500c80501d003c0a0519544410707100030503001038480c2e80e80c02403500e1295007010003003241c140c06030314030030300724040c00c2094040100040e0b81d101001e4801826a03c800c3c40002e0400418681400007400d4a106030341c202a1180041000d907002a007108001580100c1e041c0302500714214410300400c0044011b0001b2482c40e0006080300e2035440e210350040c28190520035003408250100d64020b00e62000400a40c5407906280822400a000c100d1040d0306040d9400c600b0700e44110392110280008107c00c2161746070890551466642c600700f00c00000014194041c00c1d46985080c200613401a000340c0024903200c5402015007499402c614854076040c00103101080442055440065100c0000506500c590130300ba541400f40003024245401c40000754031501206400100201c0c40307000098100040682e0240c0e114003080c002c007030301034071424002031000306000103210380750103a410034401410003154510b0301100c0888400b8021740c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 143302967 1250 143301717 143301727
    0x3010b09043e1504030f030302030411041a1212130f0f03080702010302030411120a0c05030d05030a0c140c01050f010501050c0a060c033206010e0306041203060317 72
    0xa508040450740c0503095200030074024080105215400c10b221000740d004859418401e60a649124101c4c0c001e9074019145841c459140d10b8020083d50040f5812034848070f0301ca4000703210381414003e4240303400300400e01c60341e0940d03490144441d115105102c0c8510b0301c103694040c142100b007070004103e2003801490048005003045044190364580d5404080c90306081c000420201e2424130903205c010b0f80c2441c000d0b94980761810066080741c842d06905500030fa2644008540a0f000646242614860403017049410740e100205a105d403810f4003000e0100d04d0030000205028034942c0045e07542056401c091020004858041f411a00054100e0b801e580d500c00074003404900c80c0350020300401091030060301e868814294551181c800b9440141080c2c5c0b202607510a043c040d8020140503015806231a00941c04a491080c03070100d0800040c0240b82c02d4000b1030b4482d40300300440c0341c860501400818041e107a550325003a88003582d001035000c040c0c3d01c030004400107400c0c5181d00702c1c500c45404000e40310303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 143304217 1250 143302967 143303003
    0x10e13020a02032101030804090207031e111006050a0302090c07120507030e0d03050d0209120316031b0203070b0c0c030607091d10090207020a0b0307052a06060f03010b0904 76
    0x8503082e400c0c4c0000540302c18004000080d1600c0454081d55007080c005600c03100c46180c00e0396040300805da90038124580360340143d50305502400c192605260392040750382010040e0301190880d00b0500585030032180c0c0d4034050016080c500522034020181c004460324008981c2c0300c0400344410385509800040000071444107042c0d010160075082c050481d40c00c0c041001503a0701510034411304490713040880e00820009484e95500101000d007218031802c3c0c9a40f110a06414400409222401ca0101c0c007091807034800c610076a001380c44d50f150b000c0d0040007802d0402c02c0540154011085011240c425603034030301516101402101d00460b110b0b25071400c0117050042d40b0410b00c601219505584050710100a8801e0f520f40b40d01c01100c0300280c0c0140d03520054008500107003825003150311948000410b122400c0d51000c01000c40d02c0012024440385484a9100c89900c0b09000c1101441c1d48410041200341c5400d0014480c0758100600028003007100c840403403442d110866003514099076003400074000d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 143305467 1250 143304217 143304247
    0xc150405090f010b1902150403050d060902041d130c150e0d03020a031409040615030b030a030509040f0b030a050c01021e06220503030a061d0411010e13020a0203 71
    0x80b50030312040400560400301801014003641d00442251750b002c20228110030f000b444200780e40c2c04460000409031406050140140c2e01c80e40700030780c4940c030b02000010212924402e64080e502a071111000b83c0a040c140306010403c05044000b9008601d01980000f92485a00400a15411401d002447d50940000c0c0030012883c070444c1c050848406103200181d4081806048180c1c941841208502070031307100c80b134a000d49028030b0b070002e18101003c1401058901c20043d030700082c0e902400910040e9050513190b14002c0d03802000300c2c109000b4410304d440d180e000807805071800d0900044400000002914202c00b00c00c2c03d42e41c036000040481c650396814001002030030000002100c030300d44010342e003903925480101484861110a80e03054400e03107155200d40705280d04401181d40328101003495800400443c03040c140c0f4210310560440301101d54400c4140308940000c0129207071281c0c907005542c80c05c052006a640b1005003680c0006040c5584098010440b141e8011902c0790101d03548000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 143306717 1250 143305467 143305471
    0x516090b01180e0f07030605040c020a1e020102060a020d02070c031202010606091404090501090b1e28020c010b1504050a0509010311010f0e040513061505030c010e01020c15040509 79
    0x1111010b0a020380e50041c4086500441e02840d5040c0c5542c035107a046001304280e41000c1d86c441d040c0300b400a5032517030004000c15800d028000c0642c002c1c0c1c88030540b00c648000c0f000b0090140e0401d0000888611080e406080784841414025190500a994a40084075150022121105074015416120368244134080c060021401c02141c500e0415107490314010342101043c0c4200e807a500301030200202034000414255000c444040b030741c1080d18601c00c1c1d40d48003554035281c0044200c0042d40c44840c541905404101025864420920340d003c2030010350321004580042c0d6403910036281c10f50321070090414001d0410520310f51241d003800e0412103241c9096129a01c5940306400500200714000b40c2e0400403c0d090802d140c1241c085101a14104600c0004e25031080c40d000070440508548001200b02c03d200d031408010450814140c0511000039000d500d030140d0080c0c1300c013002075014600407000304034140103c4019525060000380200e4842828610410000c2030400c52404c04600880e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 143307967 1250 143306717 143306747
    0x8011401030c15030f060f0321080a0905030903072607050f0105090a0f0305030702011e02060601080705070503160201090f0605070b060d02040207050604021e0a0b070516090b01 78
    0x4801035140d5202c44a001040d03015030840c500d218960401001d009600400280d41854070a0001c90b6032061031000d400c9182c44240c80c3d0b200c0b40d04149000e10440a41d1240c586030a03103c452990319203601e0400140504402201c4c030b8031041094600c1641c04000080050040c03c1c2c94814501c01c520540500b04070300c280103252075121260500007946c403032442c024880c400b0318090303850b2192400019400241503010356540e032305010b0080144000031004004060003030320b81e0509411041842d44400d182d080400006800240c086000c941c4607017101a0031540070b1402c1c0382400c00549981741985d02088141040700790910b8218210358100e03400000405096118688507860300501400510038400000e01500882c0d0001d5400e9607110380801003190007030021500e0b020a0301e081070b40d81380306503001c0e4031400c650105012003101c80c00128080d0031010b44011046442c002c6881e0755500450300c02c4401380612840082c0b0720b0071025180c0c004042c00790000c00c880c0c0a110001d407103001c02607512 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 143309217 1250 143307967 143308001
    0x70501021b1b01050403150209060703020d141903110d06090905060108060702071505120112020f030d020a0602090d0b1e0a0b150706110307090503150402030c0d1403130801 76
    0x102d45a0300001514200c0b50404a5182d00d406500d4280c002407040c031064581c081c401042540915500180c281e103a00c4546d16118070300800386000301d00030302480b00024405d1808a03580900288250086e0740c2c4100890302c07a606000c800074400003650804c2c0c21441400365078414606c00e200b003c010280c01072814401030002410010380082d101c4145014020a15081c150b8203003000e441001180e0840822a81e8401203507190503140320a44210708040e41f04940b10b240c0c3c1561480e020440382130500e45500207111354042590384001940124560321350200b030f50302c1007101043c407950147d4440c2c46088450031040d0110081c40085420140c668800f1614110518001c1c5d2140d800e207181c030142c0d0001b8541c0b14544e910f44030b005049285c2200a1041c0301209010303103213400070906410b55100b101628052001000b444d119120100c401a504d58000d026106090030008000c0d100d540c064001d84807032001c9600081e195a11204070131042d003020038400c01c10f800d820b00c1a091244e00f40403007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 143310467 1250 143309217 143309263
    0xf060f0f0105011407060c030b010809162904090207030f0206040512030a09150b04110c070b0c07030501060b09040506010c0b06010810050406030f02040c08131502070501021b 77
    0x1516000c0205004080c144420010110142e021010a80741903d5003e1400e0001c60700054008000e002a2000c00740820b074070f41c010410250000c1000c07201c1d8444803032090355243c2b929540c031102c074002c0403601ca0807480c07c070700f11141c0860030304c000c00c003130700c1c09040250f515071142c54024040b151030240c55003150804424040020f01c0403039055000340d203100d4866100d80310050594000c1c000d1180c010719010400c2c027025807202050308118007081044504000096044c0241d522034450882c00c42e40b03c0e000480c0c2030180b83c105802406044c0100b8003282d0b02152250749250840300d40317800c500c42d100c20104d0029114030b003a0285a600000c20302c0c0003580380d01666038907540340101514080c14440300c20002542042e20658102c01007000500a1150079074070304100e1034010603003c0030380c0070b9030810410f02d05642c018030741d45001d9032070f070605100e814165072506500303a211280071220554080112901196003400984404002c2c05243d0440c0104564810b00c0c000717412804004410707030f80c85 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 143311717 1250 143310467 143310481
    0x30412050316030b0f090907080c06040e060d0309050a09050f13030804120e0d14010f0c09090911060d0227060a030203060a03050f06041208010302060901030213030605090f060f 78
    0x850240c1403824200072070851304207000220614010f40d20319422030b49800c00c02c0003403180001c60300100c03086801554000e00111003404081c1c070803401940401c1c111000030440781c2c102107100111044c02883c0200000d0385440000301005120b9010103003107600ca009010b00b019003400d956411041024805a0660455030701500320322000300054107100104204c2d40205004d00e04210f01924028829189a109841c0940d01120f0f03542c6280281e40c0b0b801016060351004c1c0c402e0340118071180d00d40c1d090441c6488001ca02610f2042d4003103c880700c080d000b855168950034064100507045101c056129802c540c0d004111580c60381803030403841c1400c2c03e00d240c07039101d007000c9a521850038034001d40d5071361782c0b1808900c0700c20b0143e100030254800e60000750b44200d004200503004900c44d4600d1501001ca01030300302c426550a000103540318404002c081d030b0f150b0003070b4020b000203145107041000c030595030f0b2208812140308031050400354000280000d4a1a414404598010a812001c030350703c0c14051 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 143312967 1250 143311717 143311741
    0xe07060e012c0a030501050115180503060612070815091b150903010b120a020102101103340e010f0507150c142101050d12030507030b03030d020304120503 68
    0x2802401c00107015560800d203403543e0341000e01030f617008030013400325586d18002c0301548480450094000380220a2845413440101b4801c000c84800030001c0c002070300c0d8101004107520044488482c00e10400c5800121090140003800d8128170710310b040c400340d24103a00303410b0a040d48212005651034a42881c16010b035200b411b01701045001000c01c03529005d4070004240148a41c5260b075500c00158141e90b58902000200590418402e900f0b03030782c1c0140c16a6005094a0542a01c60a610310510005842100e2241c440791041281d0702e4150130045a21303240244005200d04040015291580c5281c007942c005c420780c541480d003441c02a24040a90b128246040318402981c50301d20344070f10410020a201e0b03480035640f24056025955501190306041101104a480b24507207080070b0390000581d032400b03074003040c5100d8100010341508540040304038000c050050010060503038400e0004079545040002e0b1202d01640341f00142d90341803d040c200120340061060b001040f10030010007206414203 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 143314217 1250 143312967 143313017
    0xb010303090e071e0f0203091306050f060406020601031205040e07121118060d0e030d0906050a06051e011e0c110d080a1d18040b0106141e0d0e07060e01 67
    0xa10b0210701c80ba151490490071f51182c6c04205a0004440c5491025001c042e4010001c465045807480c1202c1c0000091243c00d020fa44519005600f1000040022580d100804104c2c00103518210345025220143c0082c1110103988100020718000d0240c0001030484c820990900c010006407030514408042c92601810501c561500a107404164582220102d03002040031401d2070042c1c03501e54101c54010030060005020684800f4200000704800d03040e1881402c090f0307113010301400d0341301c001d030005071001c10302440c030541c10000840d0546030b0000703141c1091f440d0002070f5074411400c4201400c0500d12070741840412031140419805500c0080c5c1d224044580c624402d081881064200403d0760036144c1c1300050b0241c2050104403000450302c1c101240c284564032804030001d02d641c8480044406040c14130100e0030000d4100900702e26609100300504240403114402494010061111000e5518010424000c0e5000500c04e0000320b03080ba203c020007880a182214800c0c00c1c041c04008444e81c1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 143315467 1250 143314217 143314277
    0x80a14091905030f19030b060307080406200f09010215010f03030f051e0a0f020d2007080a050c0907020d09090203090a1a070212040506250b010303090e07 68
    0x514581801009000d1060703a5030382400400454a622a4000307605c0c02010301d8103090f0010b86083c2080d2000c0ca084400d407030140d41380c0c3e61500700700d5440d40d41c1e03100141262008016420504860b0f070480d50051002002030ba2011307049076880719501d000181c42d000041d110f4112103081c460051140d412541a4441204d80600c0c11030f04d0590720402c191120722030594528241c1e142c04405100c2c00c440d1400910781f82d07405a540c58081c0341000c0003203880f0b68210102000250700c05108060840800700a0b0307441c600e40d0f409079400c0f680e4071030350741d8640501d0040884003500a01001402c03468000781d641d84c003030a030b40050410540f0703201d03008040c0764241c01045d082d50340c0400404e0f207805080040008559104aa5428418541d00c41c00035030b140854241005101e420198180390303230300340241c404403207019160a0900420954212501010901840c04126400032000200d50002c042c58000c5000ba01d5080c0b03031500308090000401401032450081c049283d140442c1ca880300001104540c00c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 143316717 1250 143315467 143315503
    0x402060a0f0c0b0f04030f0e0a0312020106050612040516030809101403040b010e0106021b04050c1314010815010c060c05040b04060801080c0f0a06030504020f060307080a1409 77
    0x81e1503503064074071440301d58024210401800421540d0304003186164000e0b070003622075098115081400701c8200e80860071381608101a00801c00c001409100c0c00c0800c030501e0300003c1801c03902c40000c03c004d5040b81c0d5081d2651400031040c001800700034418020305c0301100801104460a50301c5250340d500c129154a402030361420301c080411031103518214010b02208040300d41d03c2c1071030308050030000c40a010360352544030514000582c00b400007540007120074000d01020100320000b42000003c110007012468200d5007045074101c05d520380386844010704410400070f242d038000c200c001041d002004007003c511000114201c0e10aa80251441200540c0000c02207010301400504035000d02a69200144821000c40c3c049903540d040500141612070b030008481d9801e420a040000c107060001c406600042400414001544030b50090741d40940041d124014441895001c1410740d4070440b1403000003803142c1e0074801620400d02034041c042d00300c00b08020301420142d28840d11000103030700003480d0300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 143317967 1250 143316717 143316737
    0x70305030903072328020409060b0301021b01050106031a060c01200a02240c0d1b0507020f040b031b0111011406010f050403051c02010219180e0402060a 67
    0xc010800c4520444d0721032201d0035403c14030043c40c0d403003261640c0d040001c4e01482c0513a984070480b804480300821911a003c100c820815000c0c0030040050013020344807551100902841e80c4c03024001041d030262049009206c0d51080c0d0b0b00242100c8c41a00300d0b6041500b019102c4000340c0051b030780b4000c08602201c03000d40e66100080018010295030010440e191803414082420610702005404c0d8492280c00340da5400702c8541040c0801c59140002d907000f80d400d44046140c08840d030014112000140c100001c200714505851218140d5070501c10002031000980d400460801600d0710304620029901401090004000291a100440003010032041c1a5000075140d078444d680c1074011a0103035000b0060713031605940c5011041c0d012900d15000c51070600c00140c85074494000c84e030840f6007003405894001d44080c0c0324082049080d000d10210341d0240b111014040c0500c0342d000500c0c8060b11803440328021512103000c001c0151b4451361810100305d00300300240c4c481c0d404030346510790f50345001c2c0d07044 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 143319217 1250 143317967 143317981
    0x40201090b0c0723040501030602090315010510050a1709060115050a090b09031009120206130b160c1a090706090602190219030303020a1701081e01020d0c020102030a0f1107030503 79
    0x55039200801754041d003400000414880300340e004154180c401d4090b12140d0300c050b89041c1c00400c00b0300c5800e03000381511804480f4a0322a2018044103050362404004001a92042e010409020344e4030700e4050f081400100319201c10302c0c0e00d04610f140242041424507907070100c003400350324552054060529000a05801542e01801620f8503580c540c40d080102c0f418a081c101c1d128140c4461040152040d2004100f40c121101095040782d42d00010f02a819601d0341091a0440d10030300404091010170100d140001c0c03104145d54142407558900301c1034900d0481d071780514040e00d582c001014440c1410090007250b901060350703803000715201c03030402042e280c910105907804868202c02c0d40000c000c1c0703404410150b064000345045072841c1c3d1100d0000c85000340c0b45c80280828410030700c141d03200321028030210320030300c2028a4160702c8400050801000300e01183c283d42c0c2d1981c0e001c005075400010002d0004441c4104010641c0c0e120f410080490a071103020003a00ca051409420300c00d01000041c50 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 143320467 1250 143319217 143319269
    0xf0c030905040e0f0d030227040212090c0411040602100b0f0301061509050402040f0e0601020f0613050f060423070b0a0309030e040e0303071404120b040201090b0c07 73
    0x600c0050410003424161403800c03603c401100101e001c00e40140d103158105c0c24820300981d01d401040c402c004032000311215000d41c1130685400125041380d0203000c020701e450041c50b01c00f8490801032000c0c1c048081d6050820080340c89400d0303201d0354003d0030b00007444059800035244d00410500703003001804546810014400d07002030700c0c8c1b03903a040d801c040f000f0034440343c10521032012a826841c1c1c030307900e01e49540421044c1d0240c0d0044040c01400020200500c2c4005103a4540041c0180152008010041032443c20006c2c203c66140035400c40030008010003104019807209150040050082d0b41032507502d4138400c05c400741d0600a400520021200b00042c180218002401d0070320380703556540c4500c40c0c003030040e00741443c1c10380218014001e1034a0f0340c2032038002c200e1a419210061445d5a80b081c605465004032420140410181400301142c01e640b001244013407140114122003003454a0300c00100003884c10b80058144010600a039401d0060020740d0700207070b41854135240e601d40040c08a001c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 143321717 1250 143320467 143320469
    0x10c15020c120a090305060703090321150305162c0709080a05010f0f200310090e0106081e070b0d0e1c03060b0a0207030b040c0e0903030702010b010801060f0c0309 72
    0x702d40d40300003803c2e51015402c41c0c410801c0320301c500140c40e803594800800307904032504454007501042c0c520312112907a90301d41d00c04504041e05031000141000c910f2080100e40505600704446c03503841066a4400100c02842c020014103070f0440c0b10001c806090210521840d100700c84480c00d005c1070000c03450140c040c20b00c5d100913100360001c440b1a0395003414030740c1c083c120507038a00c0d601c94580f42e6a1066540c00b401031900c1010f0600ca20100c880c565445100d1780d84c4014010f07422200207907000300361091503000709803019220f000082101030074109801d00f40320540c074821a4064680944a806901c00706400c01160303a40b8410382d450300150800075018044495940e00c2c0340c003420821500107100c0c0001c2503803c40b2159002c000d2144c07180909246403007014a90009070b801180100005020300044070b5100c3c0c810280c14264070364810320303032034900c2c002d84403009103800110401524035424490f0307618803082484c01421551521001900c000c220400d5101000701040c04a8203250190070844 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 143322967 1250 143321717 143321743
    0x18050c0906071101090605070302151012060b04060509060a0b03070e040c021506030313090e010e01230604050c030106030e1c05090909010e07060f0c050703060e010506010c15020c 79
    0x381d03072209070b4641095004201e0509502068070045d010031070502c21400e403041941d154000f800004a01e510786101d00c500102803c8000ca100e0002094408030b911824030301502c180000305004801400b017005540184d048a800b9082140800040b680d0348142c101c04c07504a401e00581d251101d0a0459040490865482d017003402c00c0c5030383c0d18459000030903031b8184029103e0440310761140e404140c3c80344200a080070765011490014000d6000950110b5022041c9200004442e490120020b0075158400f240c14200c56000502d0008a01156010f07503000004550411480c40c014412191502041c002c140030160344038006148203204201d280d882e060340c008580804030101e14010b003581d006020703040c020031182001c5000107005004503c608a40035000d000030710706240341252081c0c5a54002400c10000b6a0b000c00490070038803030180070b140142030104040140182e044d0940b00041d01007030400c440c550039074000ca0740741c213004120504084400351392506213007042032808520650813 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 143324217 1250 143322967 143322979
    0x150a050d0204181d0606040e0a021809060a0c1403060103020c01050103150f02090a030305070305130e0a0e030702030a061a03060a0b0a1208070308250906080109020418050c09 77
    0x4a8a0310201c0c076140d0f4402c00c0a00e05008040e8030805001080304c00981100081c1e0104020492034505600701888a03444181220707803010341c036000541c00ca01e00c4420340341c4005552041c441900c3c800e001c1941e0143d00104c00f03100103040210000d060304807911003503d81442c003001240707252b0700c26012910554080c40081c821561241007100c0e429548151201e11246081010080620507000b56101e081e0010704d010000d526584091303070300d580011400c8003009010411b00d00c0e0307090340c41003000103001e00755882c4040380b800042c910100c8402c1741c0d018419a0090020710f0040e9400540061560751002d40404d031000500c40e007039400740e058920b2075418001d0404120520b0010b1740b144481c004101c6980034907654030070b03000400b05800c22001d000f40f08100141340110b4010026180c06c40205000c846030034003114250200c0c2d02011840e070000600c58001000159882500207001d0310700c00ca03085240038584003070502410304805008501e25210750016192650b504252100f00c10007502e4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 143325467 1250 143324217 143324219
    0x51309090c05010221090906041103090604020306100b0904110d0f090b18030304030e060d0504050307122109050a020312041a0306090403050309011e0e0c0d02150a050d0204 76
    0x1070000300c54140941c80c014495000c18070490401080c0710702003815070310981482c1603151030501003103160040503d500991075008620303692402c0b10003076101e00058406020b0f00c2c1401e104240c00c0c040003034051a140c9003034840600c04480228111005204100e9000030420a001c0300483c090240682148a40740b07414107503104c552140d04004c030100d10035810b00006654004444241c3c403c0c44440b04d26030703407051001a000074041c2c2c0a0040590005202c01c0c03c14031607007051030580e034040b60100c900c0e42000c240c0d9401c0007001c502c00f840340400d030b007016115402042c00300f00842d00b03442c008420385500d5038260300604c8001e0243c820384130f8000d0207031440460401240000d0398403505c50605010951044400e001034100d090b24010b4900030605a0305490740d0b01c00f101d4942026040c041c1c19540e801802d071a0410500950703031102c040c004082102c09140c540c85050460511189003d1086901c03104016034a142c1014414604051a00d4840340700f0402142ca602591007903a030940c1c40010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 143326717 1250 143325467 143325473
    0x103090f0b0a0f060506120c0d060b19080604050403081b070c060504060908010b010c0201110309040501030b06040b0904170a0212040306090b0915010314010e190201020601080601030f0305130909 86
    0xa003c0d04102c1850500210b030781c400c00d206481c40740e08480c51a0544240100345c650a0081c01092480c582100104220317840d43e0701680c2c0c5074031402220b81650304076950808e030f143c2c0200d07005520100c111010406442c240d01e0103401560000c118030480c040c44144141c18074450004e5550703054015440307951190b22544042c1c00c80d80a40100310205400300d00005213040d05003c0d010000b201079540075107980c242c0e401940c2c00d01e505041d00c070190206001e080e00c01d4455208860086004d0000c42e02303d07003005000d1108403842ca841c240d0241091108100219085040818003002027496007590b40c200100300700d0030581c40c0328000301e09044c0085d001043c000c1340d400810310f081c05001200e88903100c60343c00d42d40c1d5540c0041c00840c01c0c00d4003c0100b0200d001605c50b0714010340d000e800440e100c10070a503048d042c0020021011003010642034034a0941d40e0400c04140035004010081c0495410b40c1c035188401022441d000781081800a02c4125074140d070707035071100280308554042c0203a0101d45 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 143327967 1250 143326717 143326721
    0x120109050610050a1d040201050405041814010e15040c17060108120c0a020f0a0513021e0724060312200705010509130212040f030e0315060103090f0b0a 67
    0x34402c0040d84802c04004505441e1030724501c01100e01e0030490720000203201d038402c0d001160042040e8140300040c400058180c680c0c0c014076071040c1200041c407110100c85e1034000c00b80f8522081c90b12442c1c1c5803201003040028002180a602079544001000d207681e58a044440c0c0c0c029038008040041c0012680c20503400d0000304075050780d4092055411919440d0408409406001260503056200d2004031025080000341e02a00d4000500b0804601d0b807110046052038040845000c8401c3c0d00003100b96000c80d5070005004c2d00310188050341c0c54040301e42c40b241021031030550000c016010252141710180e00c1580200001c6500251348006c160005501500460200a040c2004030914aa4180c004000300d04a015110141c40e9a801d144005040c0110141581c610b00c0c00541e08000c0c00300d01e004480c3d08580310300d220301c0105030401c2e400d140040c0906694004036000342e114100b0403144204c0d0500352940404c00f07190003c0c1c1629142440c41084403008000781806400d0380c1841940781041e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 143329217 1250 143327967 143327971
    0x21111306081b0102010203040c05060a020703060507020d0e030703030503070810050406090509010c020705060301060f05040e25020c0f06071109040606080c19031202031b1005130c0506091201090506 87
    0xc0b001440480a0b14005900b81e1004031801400302030100818082c0340b0744403000d040c070007007544100d681030f03074407a03840c00c040f030740c082d0b600c0030241e8040940f04005603404540ca010024054028003c002c0c5940d4002d0120702001e4201011700107400d001492009000c0040001000d0060060003500d80e581c805400800003030b906051294201000c1041c850700001d104000c5840141120346560f10707201c82118014090120710041082c201310000381c4000308048a0f00a015418030703801d29010800c070803103500c0044007001c400d40d00212208402a920b03c440000b03d28000e851030707590744a40b407400a8441040180244d03000b8909818041880340e82c1d8442415240d40c41c04840b800d22008041003603021038620170002d40c0100e03680900c00198000d0740180c4640003401180e080c243c03c0311900703400080308109480290b0110400b138241490a000390364200b60210845801461651104190115039000d564081c2000150026103900d03442605c918504441008106180b001c1c64026156201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 143330467 1250 143329217 143329243
    0xf08030a0b0114070c05010516050105100e07080903030712091a04020a06020c2b05071e0e012616090207020f0108060108240901090e0105012111130608 67
    0x182c00c41c10a02c5851400c54013075680180076071150501e00001192164401c2c00d60381507500040305443e001a000740669400740c81c1803240c040c146410b216003451100802402c00c41049017220502c02420004012a41c10400ca031400700950030385e80304840054403000e000101030314800c0007100324261145103040d028520840c1c48108171a036840c0201c0c0d9600303001c24010b41c00001e512002c003414142c0340101d8090b0580d8030b401010107816494950130050640c0c001c446140d90202407001040e420401000a00a03420708003110394105003094801510700b03240505050501c1600c007025080400c1101448240d9a0318071040a807104004c0019400c603200881c06070345052180d003099801684010b129090680d02c0301c02d280d80c1c4000d031101c41032030502c4440d054207a11904003001e40303079480b01c00e01800321480040b80c2c496050820608550050384803d00901403c022181c000c068416034885013a007180ca010000c00038500001e82c4c00036540c100c1700c2c0551409000250411000c00c5504a00c05 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 143331717 1250 143330467 143330477
    0xc07030b011410020c100e1203160c05040c0c0204150e090309030708010528270308070e09070f03061e030309060507050601061103191d01140d090f08030a0b01 70
    0x6440d910a980d42d41707444200f81e91060381e50500b4040680715940c070b0280003000502d513611400c685094141140e201150303407000085102c69410500010a0424008003003d681c20000b04442c0039004140241d038a400034402ca49074400c00321507030340551011015124175001c42a560500d0740405070f4a60101002c10300a000e4401c00007501001841074070310841901c490a04000030301d480c40c4c21210b204070840c40b0091744c2c3c1c904441e114401240250b4400308001c00048100c112420040c08544009240408120481d1030188154854048aa410401d10f041c0852103040080c03040e000740c21107400816080101c8000a40101c1b03e10884104a0380241c940c2e464464581e40116258402d0060280c090380c826001004110303c01c445802010124000303403414050080300ba107041846003100305000499030700c10b20042d440118143c9500003401d091414001d0100011518540207098074081425903c41201050280d0300401c00398043e48100c0e40340d5240b81c003c00400c028141c0040c6540050 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 143332967 1250 143331717 143331739
    0xa0605072718140c0f07151a031b0402031012060507030b0102030a270e0f0601091409010510231201050d150b0f04020403030203190309030903080c07030b0114 70
    0x8080e07102d540300000101000f2480c40d0b880158001803a484240d010808080400c4802d020800c4481c0b09045841495400b01c1d01000071001d140703140d070f46901c0300d0340300e500500800c1c14030001c229102d0304001804e4078050303140c0d42d81a11002e00c21525900442103858000c00303820800c0040c1e030203103218200c5c90b2020006000400c004981e00e010745903078100400c19100c1115001c5904400d50f0400705004600600c07241e480c1c1503131030352000050725021050702c613a10503c8000d6801085400141c074110006104046100001414440c2c7c10f10030180220f0f508400c00a1840c0704880703555648040c541e02d011305d55203900f01c03403802c0d910420810740200940000800c0c0da2820545944289400079114521725505481d120024031119906640c000e0b84014810440d4540c1d0015000650298001d141c94120340340312000c2c2480515106c108240c9071103412000240c2000c5001c0640b604005410384a41e402c0036142e28100c559000505883c2240c1e00004a54803142c1c0c42c5040000d0554035100d400c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 143334217 1250 143332967 143333009
    0x604091b0611060a06061b060228080106020105060a030b04210c060b0102120409020325020106050102060117061603180b15010c170703020102040f090603020a080f0a06050727 77
    0x4a850340035080026145003a4294005c0303060200e047d40750300841d8018a0f120203000b01d040e031034042d48220026410b4031302d03217030f00210f400c540054010051400207000a24018002948840d5240402050060400c010401340b003000042e486900c104c50750071142030002c1210103499088140c03821100103051030f1425080c1e51012821940b541d90110300e007810030b82002c1070351000c0e400c0105418985007151000d103014540401c8003581c108001d4000107a0542000002420150140c1000b40c2201c0d449584181d803801c0021041d41c0060320164100849039452800c40141900e41111001c5070112510300741801100d0b1010780c021885401e888003504141c4006540031099000082c108819900182c0758040c0d013a001484030714440d100040c98292030380c24400315040c0c5a0024108250303115070920031820861f42c240e01800c0030758024070384241118041540c410300030300b009140a4071140032031400350181d407010342d61010194684400c1200319000b80c5441a02c0d20402d40160740e904a44050b0f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 143335467 1250 143334217 143334221
    0x10b0717041d011d040f0201020c0a030303062d030b04030c0f1113051015050f1305030c0303040807050112020412050a0611040e0c03090a080c0d09090b01080604091b0611060a 77
    0x8a1340c4481c0d0800d2042da52615020311904440100380c0c1540140b81800180307680c4c210141e800345100362800610541001445000700d4a070820000702c8041e1102d109180401c4040130301e0881c0d5114501c29119515868100ca00f0400480d00420034194080300300100111942845407034082560381150302694196804262402611180d040d06500407052000c69801c00e90405108000e0620745d11344101d60b040120282c1c00b492001c0e854100a40c0148914034060000c0d03c41410220020742c24281004040307a03d802c0c0c00d11800b410301c0b1b02d821009640c1da039690141d40040820351000e80c001070080c1042c0303844010112044807654505681c1c0c0200c4170310780d81520140c1e16551040103865840061102155002504041343c520848a084001941c480c005083d5401040060484403e6480c03003c1e0608407550808517405007040c0103c50140d0303000d100ca80e80710400f00e070007049144450504c0da600900d030601c5a100d02184010104496401410200e15003294004a6a4a41e103030030441b01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 143336717 1250 143335467 143335499
    0x1909050906040c0e030d020601050301060b0306210c0402070b040b1807031103030d06060f080703050c0d0f0b0402040609052d090a020409060e0610080906010b0717041d01 75
    0x1510600c6880810345606282d8004809045242000181040c0d0000040d1030311491114200c0181c0c00f000040c00182820300800e0b00030844140d016045080400000745801d410b20109896403001c0c0b501401100301c00c0081c072503502000340045556a04608007a041c560080700d013964001840804178001e4004040d80b00e0050a000c00900349050030340e600c03401d15400b00c003409135241c4070500920016012130300c0f400b07004152603120000019032138140070304132000081414007490701e0a0100030110144204662842040f01c0c3c000500748503100f2014002c101102270309801910100d400300700700b034111103800c0a452040700c1d07800c0311100ca000d05001011903c0b0203904041c000b01c800a0440c00d24049550b0000306006016041c2501c070000076044504c6640f10910520070a024000f03135042c00f441c0b568940c441403070300d1074540c6403a0b091282c0d40e02c1c061040500345400029010140a80c034294039000c2c0d103044100558035a503071b403007002c44103031208401840403d00c000009010108065006 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 143337967 1250 143336717 143336719
    0x20c0a06030e01021e0301032904030c140d0201050129090d0213150e071e202d030c0c090c040b03130302060612100509070807060302190905 62
    0x20260611808801801d00c82c04030503103564003803003c00e0a00007150021140c40d0404809551251b145007004000d1000840c00d400e02c0c8204e81812251225241480e02c0d413281e05030411850b000a0751401d1103140308030324080450303809000840516140e064018038101c07204011140500c00d89180e000d454107107055000010113600300700f408590f0600c0303500c45181c503000811280100c11000581c0c810385807405010f8802a050780418001c01c421056141c1d0050068a0680314495030502c00b201500792620400041c80410009288454140c0101d103d90056460a85041403880d400065002482e41c4010040341c400e035514034003546000040ea0501c14040c002090002c1900003071242c0b500025110b40d050710810800440d0a501c0b080040d8050b100c40c1e491400312100b01c4c02c000342001405000d06120b800550b032003c0d06c04000207005a86030581c0c0c0c000013a01d488100d89186410000e6100618900805400241941c1c02d40c2c05403030030383ca400f56038038010f10030014101c41c44002c5001d03071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 143339217 1250 143337967 143337979
    0x8010608071407060f090c030302010b0a14131d070e06120f0312040303060302090106020303071106101a0403020a08030c1b1c1103011107051009020102030a2a081207020c 75
    0x3c10046010360700301044628011800040c01d503070540301c16041c0364454205a026039150504514641040c4004030010501107141c0070407080d6000001d0040e00d402100104101d8981c080681800405c5800280c013950050440740f046076103080041180c0307070845040d4440c401008030f070006074001141103241509144091454040c100d000040140e4000e40164109a907940300840140c46002459018142e00d4000355101c0c07500000080032240203a602a40a801c541c0501440351b00d0055640b0540d1074400220550744221202c0000600466002a502005036280007a01a2012000308015854042070366002c585c40ea19101959250950071030708100d146200001429405111807800c51013502150300b60700c02140020f0039130780f454803080400007000510340200b1030208040d294114401b00306101e903089a40000c0e40340d02640c50b04000b445074880700002805035003555402019941d040e81e0910b041a420001210740040700d4101d0103604150114105500020b00000034602c02011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 143340467 1250 143339217 143339227
    0xc0e090307030f0210020a05190e0102120a05160c060206090c1e0102030d0c0f020706020f0c090612010c0302070605060405060d0303020c1005040602070209060a03150b011101020703080106080714 86
    0x1280c0340c3d40c07101002000c6029005158840354800d00050110305130b9070b59540e4854050f5103010380c101e65204c23902401d11410f10401c124590b008a0340c0c00d40124408251611188007a40c1a21640706503900d4a40d5980c40204450401407a08105000e503540d541c01c03250240d60720138031035903078246c40d5040c03030b5100000c0d140c1c1c039126803107944100c180640180306a0781858004211041038502c0c4860150100302010381140c4070a034104808001040248005e09022811b0044c46845640c0380c9521400b4a1303100d00013401c2174450744081102c841085000b0003146255550040003904080030803244282000c02180359480c045c050140a1040186410107408140d81c0070740c029400350320a00350b14010051983c003000314500c00c85110b940920300160f541c1c038051040054040008004c41e116404205043c00030400d03e00c500070500001c1c403000110105440c0050714042c591406034222980005051410547d00c0341d901030484009803505242502c2c1d6440c00d48008000c2d00390f2103405081400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 143341717 1250 143340467 143340473
    0x512071104020a030b060c010c0e040915020a020304030c0e0106030b06040b0a0c0501231008010204083007032c0d0b040614090607020706050304081204050c0402040f030c0e090307 79
    0x8000e04108090307042c0000c45e081320401161302ca40203142c0c0c180407650b64120b03d82d0165000304030700c040c100085604012503100f559541700e40035841e540f0076803010b0b404204840082d0080003140c0140d9013018559050300d03581d44001c2d00140b002d000b0b40c40045d0404460002a0905006035410f8800700001241440703924074085130f440c61601400d03038056480e04d11228612482489004a50080740f011400c80c3c036050400038203144241e88006440e038810403040203200b202046040300035000040d5019070030382c5114042d01940ea544e1110180b048005000c1c03040541254035030309000421094211010091072058040709208840c180d00420034071000c4000960001c1e0386d540c020f10810001419072800788a00295001c212a413494980c001c3d03041c072070030741c8d0100203407001040c50f17260541c82d51520f603950241c140680308444003025801da01081c104242481032203a14080900304540303a40c0c1c0c401c1c0740f9410380c4840c403041d03400c00034008011501c0c0340b200c1c2841c6d22400948000310300e0205680c0d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 143342967 1250 143341717 143341721
    0x1917010c090b03060405060d150b01081f0e07300b0a030c0504021b0708032206020c0621070e0406090213030f1a090705040b03030307080106031d070806040512071104 73
    0x20300040d40440391100603000240c142c043c8640f6103202400c0020a40315500016041200c00f406ca80c841ca00012060300f2a370a2214000040e1035a010084a654540640c2640c683d000170b01c540841329903036100c2220b02074911800e0486161840014403d03403e04009001e8101c0d0700740005052807220500511950800703400400598050341c5d0340c03809012010b100182031910a400003410b542000420360041e1243c080340c01d120b0403210710903e503075610741800a95248401c60300d5a0050501107080d004081c3c900c000400e038400f440007200407030f24014400900018141703108904c281c0c501800401c9000091084c0c461110514500c10059411a218101c2641c10354004a50210b0400503101200f8200000c203401401308100410602e4100b40030131007035a00d001040383c0250b2042c01000903103075000c41094112126424001406008503040c0103c12034101101d04440c850701a0004400c440080c4441c03280e401441a01c01030030400d9140c4a0303a100f02d40000e08200d111841d980342d14640b903 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 143344217 1250 143342967 143342971
    0x6080903040801060e01061403010b040302100e030a0b0105041104060c0f05010e0a0c03020901120b0f091e03130906030c0308220806090f032104021917010c090b03060405 75
    0x1000c4038105075842d100c5a0a5420310f812024600380024010450b203500441d43c8114a504120003d09641c1841104c5105005901c00039105206808540510b54010354403d00100c0000e8180d50b02c031010343c10410120035083c4109070003a4507100c2844c5c003400d228020368060340c6c11542c6100e0380c0021034a84480d8284540003d44065691303111054a41e2001c0000d032007000d10450301a680d9902d54010420b1020b4140d000486242b1300c001c420f000501d050550503070040000c8001241a01d400001500d0304003551807401c41054450031808a202000010380f4005c13074000100107806859041c50410360310103210040c4810744216042c40002c01900180181c8989918070490b40c100084000e0841c4417240d202c81143d400c840144104000d00f0710000c4140d0513500010741c503058612281e001184c2e003d000600004200d20040b0b01156550814010051001000703c071900340c0b10201c07105035021442c84c1c1c0c1c10a601c1d00304040840ea020762102021145491a864110754a580510002d0440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 143345323 1106 143344217 143344231
    0x1140c0306060d06030b010902180a06050a050c01110d1d0105060901050d03030603021003060e01060804020a06030b0609120304080d03140106050a1407030e0f190608 73
    0x8180480303820041c2507501c0359440d0f0102042000410b0356800040c00340840e100000741064264018000801540d902510303110450010004e0a64203440341d4000b08006100e802c401e9406640980490900c500011600960360140107815a02504071854181d0340c504241010301d80c441119603602d079540000300100e003447d034006011840144603091090340b0f5007110104143c400c8d0080f40080d03a01502c55207501008610103400783c82c01d8020321403040f0816000048051291892901858000d4030700c4604508281003200070745015401142c2000041040d0300458983c0a00001150700c004090340e155820070340654140380b07905005404040c141142c5492aa03140d540c40340c11907540e4103080d0f0344d420b0003840507545209001d07100800d02e0000308511080c03580184d4100b0903244111195008802300000b013005100d284040300d0890710200c60b060051601542c030032504101 = true := by decide +kernel

theorem cover : BRFrame.Cov 143165467 143345323 := by
  have h0 := BRFrame.cov_init 143165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 143165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 143165467 ≤ n) (h2 : n < 143345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
