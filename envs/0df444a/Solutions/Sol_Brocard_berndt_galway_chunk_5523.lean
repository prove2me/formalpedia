-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5523
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:08:38.36502+00:00
-- url     : https://prove2.me/submissions/4cc2b341-5836-4617-9f5a-6839fcc8096f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 993165467 ≤ n < 993345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 993166717 1250 993165467 993165487
    0x61506070201051c0c0f09090203010b16020112020c0c031612080d20030613060f0b0c0f0703050606030d050403170309010f0609150803040b0d0207031710091406090a0b0105 76
    0x14030240c503940c0c0e0759400751842c0301b0350004048a0903640080115841000140010000e2038100d6122081516100210380c1d111b200481d11901c1c010825100e880c800308100a4010011800d40000041181211091001c8034450f200428070340c0b09448054a0407004100020342c40c4002c1c0c5104000b9040028803422696a4200002199041c0f1180c1510001c2002400e2510080000401c0a00c1d142004090f007801c002c0c40381702c18031b070069003003081000c43c128199030020011242140794007010354204036645c1c5009030396882c06446030f620a00545a0f60800584514152012650440e0480000c40302040c080b96580d40044d2560100d552540100300b40c83d5028020340d001404c00400004184c07040b0f404116028205410000300768100308410081441d100050307aa0410031a0001a40d03064903141c10355590702040070900340b16855000f000840c1104038551001c6581d410760a015008c0a001c29800b0340b0030032a1201e500541e554040707071003c08964030140003544181001032528035031303079 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 993167967 1250 993166717 993166721
    0x121508060f1b120414010b0a06030e0a08040b040524070303180f05060a0b041a06030c120f06090601052701030f0e0123010b040608060a03020a17061506070201051c 72
    0x445144400f41c1008280820440e05a00d089942c00d280d80080007205d060100140300c040807403041d00d0405444103048510184240208040a40d004004507a80c17070f5222203260558115200d0b5600c9141c81010950180c9a0400c146400030180007211349030484c01d5a041d001010418944910014910480000191a140c2742c1103528040d4004007102d1805c0e140d18000c1e9441c0119180c007a50800840d5000e4000701d821480340d0741c40803201c103900d80e500d09803a040540105075801c40786100c84824802034000c5105400e000e0f4000355071000e12940ca04e40152601e100340b072000c83d6104e0020340010480040b050031038208000515020851814a10443d402e0300e5809000100c0c5965901d04e40607008244c44c8000318202032194413a01662408031481d8441c0034501c11002404250000034119644595903140650790007003150501c152565074209543ca034091284049100d04004240303100b40d151120405000000d0816103040c0c800d5004507560340004004c0d00c912426510005203181d818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 993169217 1250 993167967 993167977
    0x209191d011401080d090e090a08070b0114010315153b03120f0d02090a0603050601120e0c0f0f04051806070305190b060910121508060f1b 61
    0x9040089608a02c0d12500c06000704180d00a1a2039807003659012035540e0043c8101089030b07807400c4000c1c801d5581c09261414000700d110700030140c0c10000b847c00100205109414144c07081c2c0840f10031040c1c00700c401035080342c105510010f1203001e00941003000120050310a10380808c01d1401364031030a001020741c04001040405081b82d114101c0c0a40c584004a80d414403010104030002c0501d005e01800300503461040c68241c01500704d00040001c1d88110301d03012540c42850260003000d000360ba0b0f481c000d008242c25143c032400101c40c01c92054086d01203014174051602080007620031030081c0000c10800c4132030011110707004410442c41c9980c43c0d503244a030520408141c0d46054210700205081070400720028111000d0525010602080003480070703082c060003400e1180025281c030003100155242c040c0484150744074400e52101d55156611144214211032600300500810007a86c602d06000041c50181104c2070744000700061811814105140d00a848135004e0b41c502e00010f200c3d06030039481 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 993170467 1250 993169217 993169271
    0x3c0b04150c0f0b06031002090901030303181403030106030e03130b03060d051b01110a05190812130302011107081e0403080a0206070e10080a11091c0c12020919 70
    0x502c104213590a05008803d00042801000c614000c509030000d0394005040c000901010b5560103902d2022080d100c0810300641c00c40a1220340d152078641440d40da6209024110002c1d08203450303070028000000903a0310104200110348511030408192018980008000550150106000d140400c100f400580e034100d40c43d0104050341c11401e000504088960314100340f1591018480b04003080c07020543c1942c50303a82d0810204600d03224103204c134841c0140700c60341c0b00094140f0240300d503402c646036054142d03c0c484e030000d020f03042610070108900c2c000e02401400340360040000b03041c0000300c10780307112109140c82c1c01c13141050340765140c029860300281800009a44400e040c03000300d43d000b0785030845003081100c0f04031142514410081120030090602440c043d20394004101407880a02500d207180c1000e05041c3d8031152450002c9030849400c2401e64081020740c1c4080f0b40c800a54a0001065401800701c51003071310380b001500d59050b1100103101c0240d070707180a00c814000381c80710034003100e01c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 993171717 1250 993170467 993170483
    0xf08030d0b01260a111204110306010609170f0708070f08010c121d1b13020a05040302062b06030b0709030302253c0b04150c0f 56
    0xc0340045000440d000d00c0c4006061040086114581c000024441d00f10b088401000c2141c0e903e036903101d140500200d04c00a00200c2011038070310f4003444d0621201d48220b00882d001c1001d207481c0c0086c5520307640207008030400251034800038040300c40c08807401e0300c3d541c03414000c9602256100c64a0740c101501d44d00808002e0300303d40810044451000c0c1c0040c01f6013041002001590450440a040c0304580c08000d100591140103510000318003c40500c0440710490a0740c0c0315030441d524142c2481e0445034128800c61140c07503101c030100c40c1c5e07100303070390f043c2500f600c42c2d80c6030508540800503140c20810141c0303030b4032130540800302510604002d80d00b960700c031101d0003091550440c41e0051030708400030203180400c42e0112041010903400202c0d106400001c83d04400006140300011200d06829040350341400803556044010504680b0300a042e0300040c070040c46030f40311000003124054828450a035071314005000c18003500c04403010880800c001400d1002c02c8a11503540d1001441070058143c607002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 993172967 1250 993171717 993171727
    0x21203040e0c190c110307060f0f0305010e010611120a020304210210050d0204080105131406070507120e030d0c02010e04090f080a020102160b06031b03100b04060f0803 74
    0x441d05800c55030031044003400740d81401c1040304810030358405022003208100f800c0034004248031000503144604400070702a600c0003921904058540024030140d80d0028014541d000c030360301e1107442114161158071103980d0484e40f8000007212089840300d0120901d0107003010140250741000001d00d00d41540d90003071174480d0719044904452003101c1103080c103012a810f408900698a410b9880c4c42c80540d03040180c0c50701d2600c4000c00c002c4c0265081282c03198600401e014410010b00300c405070b20382c41092010900b490b298641e07900c402080e50b007080428404c0c44203200103201d008050110b80324500e0804001c041404c0003c0c40d101c100032020001c40d0190802c1e20955074020b5508203807440a07503050000195560700c29007000c0c80e424015050300d20200b03114203104e100f0f4040f81c510071070040e0170009140c1d25040c0400e038044295034084c40ba100b0783c9201e07000c0d14810101d4a42020703000b0058003079014040c031780801070000c80e8070303182c0d00682d24000482d001c4240026070003d0f0030310f100116152 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 993174217 1250 993172967 993172979
    0x40605090628080a0b011a030a11040801060906050a1d0a050604020d050103080901120e0325050703140705031b13060e0c21090d050703030b090f2202010e041802120304 74
    0x141c030041e080012100c160b16007c4a0700f04000d42265088809600002a840300d03150442c03006010300e40000ca01c035400d0075000607181543e80c0101082e01c03c00c8403050142c0c3c1d07880c041d0502100c103101403019a1a14280058500c1001307074000c6074000380141c80503107002e0703030448941c003100d8098104841360300c00450030804c1c5d035078850307014809250071041c100105807010000d296203000b00d5030b2243ca060300000d08550b60b840e91101d40340d01c49502a048485484c0c8a1030701695020501400080621400700c00060314a030002d01a5852115460109600d21103002401070f0700d1025105001010b8607150002200244a1030052060f21300d403034410745541e0800f21000320010402d18070360028020000707128800c8030101e000101e03a0081c0c20416602d0030286030650103401100c0f1000d902c0008101084540c06202c1b00c3c031440b40c0700080320360b00da4040c2c03001c0c2060070f106020300c0a80040c000c614902801d0406604c646540c0180c4917800c13800c3c10441d03001424040901d1084541398101180410407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 993175467 1250 993174217 993174233
    0x40f06030219031a0607050f01020a0905030f06161d1806190b04270f0906060b12060f12060c0a02010b0102030307020d08100b0a0206010311040605090628080a 70
    0x70241145010f12040261010f54008844c6038406903205500025004003000b4003040300c0344000c0b0884009540701c00070244003808446503845064002d000b01e44107000740d61404034900b0701ca900d00c030082d4030014013403100071240070400d4030703100c2070b24172059500e101181d8488131902003020319481707020a1860700c8410700400718020300c2050003002c950b4900b40101c081ca02c055609441603404004052045014003c4805000d9502c1c07900c001c0c5490781080c400d640c02e81009140c240503890501c0113540e14039010155100d904104841c40d034000b1b001c0f40300d034a009190004480d40050030039441109010240d428103034207842e06040f00303600240e07105e600360302802280d542000c00d001850842c07a1240380652242008122007040007034107400030f60f01d013005d1007016000c0c181074030f44a44c59100c84600607643c2c4c042808140c91070150503200d0b090b285403c0c040c120a03200c01500724025525440c080c400b142250f02c00c805504044525044c000991402a040007410031f8402010282941c0c100001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 993176717 1250 993175467 993175507
    0x1406150a140f042d0e0108032205031002041403010b1c211211090f0105070503071415010515040e070c2004060503010c020d080705040f060302 63
    0x401801442545110364012415006071158421181c2d540d03849415840220311541d00300c0c910501000780f0f4000d954464441480f8120008000d07040183c1e2128000015604240b040103040ea001300607181c000042e4400d0000e542450004103440c003615000000d0070301a403c0f0a074024a58042010070014072310042040341054150001c000f043c01410204a0071120f0303240d4055441d48091800c810042c5160426010541d6410041120248403c005200610004e9516000da080064a030542503409044505948006001450a0351402d005440c0e5810410b0103550b207010030b002ca00081981c1143d15109801c00c0c201401c158071281280000904042c1c1220b4040c0d030b00c8990030459100740004541c04e440103c4d1006c00540ea0b4003008070707070300800c00c6001041e41c0a01c8014402448210070020707070352101102d05002907901c80e01458203c504240d5070a0060303204a40d2030070381c14068031000d42c000141d840c01c45d2519485080c00404041c00d64071180000b83c2c006008440d15111115501e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 993177967 1250 993176717 993176749
    0x1902010b1008010e09070306050103080901020607020f0d030c14070f05061e0c09040f0f0501080f0c0303031513020408210306180703020c0114090d05040b0a0c0602070203011406 78
    0x1050901c215400030020081402611802040280070401418003042070100850341304a0034416076840c0d03d080c542a4100b600c0c000d0140c407031200419a02030001c05c0307001c03500b020307000100002d40001000310040c0a582c0c4c000b10605c0015520300030a1001c10008056290180036103607160100341c81c0a0340b1f0000000e2092a40c0b1034020a645006580c01080c42e4018402c4c2e040191600084c6c0009401031001c80064004e043c5441c402200190705600311504a444000903140540440b1900d941c80d541e03c09075955164000300000754500c0c040c4400808118800b4001c111031001c3c0311045c0c0100e0348176800400756944a04494801340c0e030a41303011042c03215802d081a0450801c500403400c0f070114445c0b80f00c2020310401c00640e02d0352296041d1030300c046003400244540700743e50303420440360b10081d078034a003003406000e140306202401601280d04480402160606d458101c001c11140580248001c5035901c8c0c0030014000565003d02a40901e1b24403401c00c0800c506200e410000f40159a80140d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 993179217 1250 993177967 993177979
    0x7032108150105090a0b0a03090203010f0c020c121e03040806160c0b042402040f05090c0d0e0a02130f0510080d080c0c0601030b010e0708060a291902010b 68
    0x492005454114500d407030301c007030030200d0300d0761a54400580407200c2900b0901c0b82000208160703285640c10380062011034000d6000b0002c0b600050035087c2a2844041440050780c0850580a55410209080b11640091005841c0543c0c0c43c8044200100c844000103c410303031001c00d05010320141480501d4121035460b054441c6800c00c0d41e00681081e0340220041d05020381d40c0300060622044500031003c03024001a010f00b5070340382d40400c40081d0820f0240c0071080101c060082804e0034024001d0b4043e20034541064189203a901048024003114800701400e07001c1e200040c00107895449400e2100001c50002081b072401d030b240c0307460071218020706442d080901c21204100791a40402c1046400300079103030a45840c2c0e41c0582c29880c521903450101d0703c600c2540000410300c2000351300c43e4103a540d0400c42c480b02d511000c0c41100c28500030781e1855406a4030000411403100012011b5041003a0364038501c40c40c0030140c800f090f40382c114400c1c03131040492040c0d92054466080c807509280725030444d16 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 993180467 1250 993179217 993179221
    0x4230906150d06051c0303050609270109080d05010321090b0f040315020c1902030607030f090210030b01120e0606010c0f1202070612050f040b071107032108 69
    0x5941e0848a490401d00d2020010781100d0300851500600013800e0007801000c0003480c0320700341c80750a00035039205400092500001c1001d5241021626000700c01c58102d451000243c08090080000c0c04c40d0345140a640c1c4130000d00000d455070020303042c02442508000703120b41c0755042a0700141c248503c81c0c0c04890303205404184041d0410720503000e40b4561000c2c03035200c5c40200c51013286482070360805488101d00d903120040c1d801260700200074240d0031400f51400165040302c207264401d90b0f0a4001c3d40b6402c45000501230510036404000920989a001306805545402048181c245170301d0100019489041c01c58095800c05228903400900341410841c00135284080e98450b00301402560400250302d000300103003c20942c04a1040c0d822030360400a0880b0010061754500c4148500408203105903032108001d41e880c40740600c520750b90800354415a4444e5a6407015000080150303003408145114407803030100821100340a94420064462010b21002c850b00406804078215010000b00e002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 993181717 1250 993180467 993180469
    0xf09060403080703180c030b0702071a07020f04060e0a1d0a03090312090e1503060c16060507030f0204030c08100b100f090306050c19080c040e060406030804230906 72
    0x42d40941c030040501d400941054070b903d5058a988071804007400014004101100b8000300c0c6a07682e00813461602200c85017540c0b06c610031082c0c1b0120001c150901c40c02e000103800f6090500400100c1d8100030030004090391918088030000b0b009440b15801950703902030f412944900c011a002512a04030b004107640b0a20356001418810b081c00020078400d07007907460f041c5060040c080d04028140c400b41681440c41c0c01d00c0341d0596141c04a03000c51203485404082429500000b003150b50078441801c0340100882152120b4001e0000a40343c0ca0405544030072400c072a200c248050006548190035a84404d4a0950020301c1c0921181805584c645030412549403a075603d102c51000307004a00b0200c080116251083da6401c00d65072028000c981031030200010041c458000b0324107404590300c036417540317440554101c0700e044048401760070700c100400c8240546100181c80f03540c840d1004101041c90743e12a07481459581281d404850620415200d00f199101e011089481008054404800701d00e0400 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 993182967 1250 993181717 993181727
    0xf0b0a0b0706020405061204030201060509060a1502070b130503070e01050f010c050111030a0e0d09080d0c020d050106030c03140a0b0615070c03080c071e15021c080f09060403 77
    0x1104610300e003000055541e0802029806680090000a00d101c0e120b19004401d21800c120840c0d080300154a003090100b1141b421802d464028500642581c940e0307820124042c005003901101c010962148001c00501c4405810050501030302d80880c0f59a15881c18050500d044103a030070104070141440014400b0b44c0341c24014500d201c4003444c0229203805a82041c9004290510451000b600d0000401094086a80114596400d588111a19018000b0003201c0366001401000b0683d00914200340d6994417a18450200314002061008102c100343d48c2c885c2110820303441128400705144081050264040702c0c41c2c0800c80d0303030000d008038042e655075042c010100140302c14440d962400d5100a420100b009a40c1a03543c0109503c03442916420304040381c1d040310034801c425100d880d90100350345101600c4000361610303550041100324245643c000501340704214031400c6224103480c0550f00c540d0b503480c0c1c41d101600c0c0e0312502d240e42070011154010450040006583d940131206000c0080c0d802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 993184217 1250 993182967 993182969
    0x50702010e120609030d060621090f1502040501090b09010806120c0a03050705010305090a0b1f0503011e0510060c11010507230709060b0313020609041d010c0c02150a02011d010f0f0b0a 81
    0x30308000200c482c030b2b0f441c00c0c10030800d08080181068030b0208050034480c000d640184107440c401d0f01c07107207a00b96603030f84400801e2192100450000344040d0115245041c84842c80c402d80c04108103982c0170600311404a002e40b805580107440982c011070b410440b40d40c1500c12180c019159a025140207080c90722900b1610303001070814862201c24420a039070030703043c0a0741c00c405484010000d114828200c2c40084240b4240c0610040040c500800700303400c500c1050b4144126400e81c1c55000103000c8a0b2901101e2400c902c0c0d031107042c40820070030080003801e130803100104841011540b41c9000d82e0b8144c501c0c03514049422054440d881c0c48002e010b030000440c15a980201c44d5840140c2c80100351010411500500f11141d4025013030580c400101031000280000920300c507802084500401441261500301301030019401c03018001d803400451100000130608006030340004110f1245207007840c00d5004c6070241803160760755603a510f1112080039000c2c880c20904081d01c24060b2000072400554003400d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 993185467 1250 993184217 993184277
    0x4051522080d1809060b03070e010503060a03020405190c110f01090b0a0e0a050f0106170a031e03060e010e061f0e0f040e060c0c06010f0303050702010e120609030d0606 74
    0x701c010a8208121141c0c280f0003030f061200c0140300c155500c0c50400318541081e10440e021405180e0000015441282076910a08004140e40c0040d4a0740d001d020081c040540103814400406a50802d2003400d801010b6090404c2e9807420244c50b10420031702e0078000b1403002d1201c0c2c2c1e410b000300c1c10081503140c81c80d20f4200081140000e80b40c8069200c3e94542880c8a000a182d030140607140c484092040d03100d281201c0203e101e1081c1103d031000480d0f150b403c0c0e90b10040100d80e00b58000c00c0700101010280041c105241400501c0544032074140c0d182444c05d034401da109007641c1c01084128104200748250b01c81703044801480f019841400a8292002d144556000c1e10500340005000d540300d410012600030308006986c05411300100390301ea280d100c5020fa150030710070340e00001510001c03d801c400850f501590360b41d0800000340c1c011600e007100010610307032025070002100040d100501640d4042d000d51001590f13a1031400201c1020354601c2d600842c10700800e202410070710700b50300da208483c802c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 993186717 1250 993185467 993185477
    0x3011502191103030903060a0204050102100b09010306091707050105070f0f080601051c1803030b0306150d08040b18010813050606060c0f0318012a1704051522080d 72
    0x8080b408a032a40c010305450342c1d8144a660244030308242d85600030300517a502a426100440c052284500c1941d4034a0403051700700c0d601c10010000f18259031b111911503071140200d40c04004501e0360002164000301016640c59641d039045c05091171f00144800145c110505080324030b1201841e024065400c000c0c122f90500070001801544c0b41c03407200d2403400c2200c54030b00c06c01003030705954151001c2c100b1b5010200d01003858804011813910300081d285200e00d4110304402007034001001802129a4000c10845490205101c007244e1038a260b0007030121103100d40c2c0d400c2182601311000501100c00900200e203d140140c40c8100490b0010401c154042c006035900307a035a0104925580c501014800c0c1c20b0301c0b5000110b48a204500600c03e038150401090340c40c06607424002e0011158440e180410b142c204010444c1e203000508402c0980b11100700e62180103040c560742e2408903100403501d9190303010706400014610402c2c10549500c0d245d5864600d4407030b07000d506000c0060361750030412610340c0500c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 993187967 1250 993186717 993186743
    0x1e0a09090b0601081f06031b0309081e070206040e060f0a05010215040804031406040605090312060d150f020d061502282f091504090804050909030301150219 69
    0x80407040030529004d484c05c1d0304a0b03400d544510003001000c000f800709131860301440a00300a00e20070300030116001c3d0408d103403510b040c0214a400e01d031000a84030803c5001d07000d00401c009680c03440c001c2c000400d0800c0100c0b0b4649021001c002003442d08145031807248200c2a024070050b68005210100b80001d40b08034681c41c0c95500700f141d203d009540c00185115010b10048494500101d10b031030055105900c01d1141c2c1c0c0320302c46007640324010208501c44040031780001901601c1c144105011540c090141c2c1c2c3c0108090000b0a02a252078484203500070f0b80000320761140c581c2074031840005040301d101d1811802c020100094640c44000c00c6c40b440c009860b203009075030501011001d0903440e841540032914403070040c90303a4440c242030301421712220800c082195450500c554118440c200d01d44007400794441d4a02003200a000c0ea079016074240d030040c00b002c5280c0d218081c1c0b9070700985203000210b0300c0b0740c5400d0000a5080780f03030018008540240c0d0b0084051041c0c0d800701c9a0300c0d6801600380c4404 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 993189217 1250 993187967 993187981
    0x201030b030d0f02060708070c0206030612060109050117030f0301060509031c030b0906041e0c12020d1a0a030b040609080c03031305060601091d0c091e0a09090b060108 74
    0x1602884440e6a49401140303120360241c0c3c1c000e80b008040f0403250f000e4070220343c0c030f00f0400d4070403002c01ca030f4070700100d81c1d001010f800503e007010065500c050f00411290007010310754201b626003003090300a40010f655410062150b8440e00491020440c0a030004503c1c081d20005400365600062080800344800031031800702554040c0f00c40042107650142500c1035010000004000d418080b902c54016109900454401e081c54010003844040c03064403042503c044201180050100301840e2040046040b24020103021900040010341c003845d10100e005886a05890a20074120222522130809000200005441000c0c0260b206801040000f0000780b41d052507141885410b0b04200103000c000f00b040000714040d80340e00c0055000d00b0440c0c29a030b40e510015100800b050080c40740e42070107900512607015000044a5102000049040c205000540860182c0c01004a0802c1107070290602c0209800d0a0100710300a009800007804220040d407140034064038064986410464803000003100d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 993190467 1250 993189217 993189221
    0xa0512061c0605011805090a020d14011104090e0102031b0a0201180b09070b09011d0f0d0821010609031b1a091503040309062102041805060409030516020103 69
    0x100c1ea40c6200a80401e00c0396280c1080148001d006902d240365504040c1014200207100740307441000110014103482910340c0130030035000301120742120700c45404840051640004c0c0500e503480b2560b0b5035525110350a101d5207030f056804030450321646a10510400c0752103105280e83c200422035401c4c02d160b5075851590100d0140c40040a4804170804904032581040007603000c8a100396002e07000d0300c0c10103403204e018200f04c0c0300303034102907001881d0780300781c1e080000c085040300c0c41000005240c0202010f8020210b6405030403d4001e03107940b48041002e44815105801580e410340408840c52025130400070041c0090050780005040100a048403188102d051000d42d07010300802c0fa5240e03013413101c01c03007031249951200103414080d003113071108203e0007034100f015240510390585070904400c0c14403030304482c44007100c03ca0a207981c80c80705c9000c0303121b031140c070003000607052050a00d456540c130440c402e026103a020b45894012464134180101095201d429120380b040108240b0070201c0e414001240 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 993191717 1250 993190467 993190489
    0x261203040515010f0602100b0306071b021302130602010905060f0a2c0106090b1f140c0703030f0c020d0b070507060608010c081308070602311a0a051206 67
    0x10402c0312080080303152031100802804035455a401c0760507a10a8007650b0301035504000c40207030558012408103042500400300100ca0100c0c1001844a00f012600041d4083c81c16013805800554005030082141c0c82c1c041e48240a442140001c1c06103200c1c80d920795542d20b9004120307161104408010800d001030917001140001e810040744066080811400084401d912001c0202586007040000c1c020285000b0003d181e50000c00850040510b1000c40c0001665184160108030f4015080107900442c0c5000c0c2124619100080030080d08625000e0701c40b4958458070010302c8154904000140d80341e230302000e5280e03031106035603100d070f01c0f034281c00c0d981800794000c02026103050400105070000c05500c0700d104c000e0140d071070100f240c5a101c40c1c40c0d00c94241a10142c2058000c0040c030b804250b96130002d150228034401c1e80741181c03111089e2081000c95100315010f0310304001d54104203041079000343e201030201c0119128609812a54083c105214804000000b042100001000c0780e40c2c584c401e103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 993192967 1250 993191717 993191743
    0x90d030207020105071a0108061f05061303050a0303090501060501031b031d2e060b0d020c0c090c070c09020c070e09030c070803270d0230072612030405 67
    0x101c094204003102c036071b14024040c502240c8558000201c0c1400c2d1402030713103512040700d4800c0074094100020700103660f001c8100c1008410a803c00080000d004119118120340250390000302840d2910b000703425581e84c0e41c04503041504064607140301055000074041c443c051401c0010b80c0c0002882081c114090303d10701c0d50400c4c002c00d000c9216120001002c1d075887c00850030202030300c400414584041b501540580a0342132001e200a131007540c19a03008007040e440740006c546869100c2d0002458205044800c88610b900c041469420421940c0543d0086d110780700c03045d4104610003070b8055a1b2540c9220356403e0351400b0012940c1e042c02441150060084103050b03c3e82d007034443c10002d5591b4010504d0740307041042e00c601e0080000c008920740d440504010121001c05c030080c1c0811408004491044d0b011038820003001261000080c4041003501d40390307000d8142180313800902d924200d81c808406400041d44211909040710120b80701e0a9203090021035912519035080452909000012034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 993194217 1250 993192967 993192983
    0x503070822060c110601050a0b031b09130617061b16020409080a020607020c09070f110d03050604060b1921090605010302090108011a0f04020d0203011d0c03090d03020702010507 78
    0x59001103910100d00070490a030350f4205d849990742c031024004204098420074010b84c1e402d1020403130000d076800595000c030403002812414400c18200041c0100e540c81c1c00d2807080c030758031841000724040009408508840d11000740c480c0780b40881e024484052103501c0c0301c02d006030004101038101850101c041c5410f0300508100b1601c1d0070391904000340e91021892902610503e0700080c03000f0310005201c0c2d400e407409420a52180c555550035105508459070010a000044914a40d034401c100201d14400c5100d541c0811607003804001d000494080d83c1201405800422407481d0819041d4241e00700f25055140032900f9920307603002c50102d074a202d5071038040c15050400800038024550403041c10780703000701e0b204041030741c0e1484620700700ca15014a411031a1004004408249050502401c1840000c4c201601d0705034071124840481e4000d81101c18141038418810b60000c00c01528594400007200c03085240d82032000c3c0d00d40c1e5030b942c80c920510403d0f40000b0204216446031050f509407660142d50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 993195467 1250 993194217 993194231
    0x20301120507120503160c050d030201051b04030203032d07050f1905060a0506010905130219020a05070b0a1b03020c13051e060d140d030c050307082206 67
    0x201403440316091509441911607100301003645800c283d00c80d94840c0c1d0100c02540340c0850600200c8245218050684044030044800945900e5070421800da8034426400050a8075000c030900351840070221304500442028001440140c400004a402d4170b50841d8807040d40035421803200452102d0066000943d15012802104100300010148010303066082910100110900c040343c82000511014203185c1c003200102c0c00030407081e44150340080d018904035010720b0b201c002191168000d8030082070180e84c001500e05801110304030300d150501880c80540403c0003d41c42d4190380c0d40072405410040d440c001110900c1c1ca002700c2c0551000c80c50181080215480c07801d000c3c1d151402d0021242c02161000c03207020034102076100780ea21070307500c4403213202c03000c040b181e9810481c801c0140056006810140100041404103c40400034802400200703803400003404010141c50308000a101404018000d01c40c800e82c012b19102e0b0b04c612000c59005802e011110300d051362407088603001d0009031070301c40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 993196717 1250 993195467 993195479
    0x617041b080a0606060f20100c0e010801051512190903050d0c09081009030c0614160809030d0e1e01020d0b060f0d18120e090106080f15060d020301 65
    0x82c203a242140100d104000e030300d1303480a080d101115094592000039219800d0188840c0e0070f40800d07c41100218100c0d80e030220f6902564040f202c00e100e10b880854601010301d4030301d60380178462078007402059613102d4a00e641e210f460920780c010303c80001911800100024104560a101200503c11090701406524102d080180c000d61005100c6c1031820700300000410804e000b06071540c1240e03003880c01070441840c1114040c00614035038030100e00704820300b44007101044483c001e400300c2003213070f00740844541000300b83c0141211011110714180040c0740300304a055038011003952403030751a1b1100414800d58414000e42030500c00032400402074101c407030880051a0540c082d0000525050080091704400f00c2002581d000d402d000d6801100d0800c440d41e2080541d0304104440c5c0f03008400814000301660b1103002e049072079240d540000d200345d103020384035150101c4030f1401043e090422881c0c0d81440d041840d1900310007410903403a0790080481d5111038171349404a41c40d400c51000210748950b1120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 993197967 1250 993196717 993196723
    0xd17040b040e0609090c12030d1508071a07060513210e0d0203060a0b040b0607051005060103020316081f06020a02100215070e060d0501031208100617041b08 69
    0x401000c00c0c2c0c19035240020b0b20b60030404022030145800b4001400c01d201c5650030400000d483c0d080300c00d4903004c1030200788101aa03034000c418007100a16400449941440c80980c98041107501660b010000e0410b42c00010b02e40700d08030380100d0340000e004585550741c000441c10240b00a80c00030700090144400c034802050109084040d50321075512954121010404c000d10f20203000006940350308000042149020b25620039150510003410100b02d44440070001100c42c0c008010543d40d980000713441821031413041c899a41d2142d02401d0441c01c2d0b040c40000b01510580011091050210500220759001980d18800c40442d140780340442166854410003900c800328540128042c1c041a9100c00516001203400b200c460828184070455949988081f508003019044c031036040101007210b603882d482c0038010b4501941c05401206051103903031070700420b02c0d90020209500c81840f5042800f0441c0d0000003c2070f046500c00300c1d5602501ca60404c10151b9481000d0644080e107500b90002d0700b9203000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 993199217 1250 993197967 993197969
    0x91f17011d0105090c01022d0c04090506161404090903140a0f08090706050a1214010902030402130605150d29130203061c03180f08010b0103020c03090d17040b04 71
    0x42d000341e4100e125485c00690740e51072401c03842440b4980020034812010a039103481810402c1c1c0c0811034209425480105080310b030406003e0f0b4994104c0b100b004064042070031141c840c154186011814040c9400f0804a1802a80a985c5149860360301c10340a040c03040c039030310702c0c4c02c004c0e04455036540304807000280040381c45400a1000c40c1601c1c0001d1000c0701f020804000b2141c03140c07034880c640150148202d0310080d1410000d20095500d402015510504002450190951880c0140d80c1c0c2802d0042141040c00c40ca0b85032911401d1080c144066101c00443e0010800d0050f50035448001e6020000c005e0221910a0504100300941010f40c0b00580440801c11260a0391005c00f2446050740e08003da210844140f50400540400d1200c0c1072004100c0b401c00c40e00a1a0079400c0170451440030342c98258903030002403a946007160a000f1910280303e1510349003000d081c11031818540341c1016441c3e00940c00700c14407510010200c41c00340b0160905401043c101c0c41c01060741c0c0c0340c0382c0c0000112134002e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 993200467 1250 993199217 993199231
    0xc1e08040b2116140304020d02090c0d02072319060c140309010b040b06030f06090a0204180b010e04180609081903230408030609091006030f02091f17011d0105 70
    0x58090191880c04c500d00c100d0303000f160041c219074817103202502071060300e46010700f6610004000300301241e03c00c100c610141201a10980c084201d154459040c00e48113446040744014640100202c040c00070b503448039034003080d5407106001c11140e04500c002c0c1d4505102c1411060583e20000400c1000d08040d44808030701c0d0000c46080104030382410a101e4a400112141808403d03860042040c9280075203060350300a1030004054074050700d0b1115a80e610038150000000756407035000402556030000700046030200d0079102045040a100d0314a100d59903600000340003155202c640c401400f9100c011580c1004043c46080908a950000240104100c80350005c1d07008600c00148506002904418080c541200031076081d900e0b0601002211800905100801e11921418040740c4601d40a0b240003076019407150340c500c82641c01032180084006240285a0703840609603040c2144a040c802d094844080c070050032082018500d81c010260b920f41110061901507200b036407541c054000c1881425 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 993201717 1250 993200467 993200477
    0x2e18050315011508010e0f0c1b150a1b1805030601060f110307031d0d060c18170703030f02010209060d0e16230109150c1e08040b2116 59
    0x4080b0f03002c8541450a009192114070f241c40072540c0c0d241100036503038020300303010016850401c0b008402d980800c070b5841c4a419540008014500315200c5290f072039442941024103020500c0407050802e4079a041100580034001203082d0f4240061107030109201a000241c100d802a5844090150001e21006d80341c0f4009400350761161222007011064620056264850444004090306030804014511003865041820350b03402c403000c1041350003941d074000200e07103072820720201034440c420b02ca650780e410060240c0c21458104000ca440000e0600840b40c0501d4400300055404000324064429800c4955019001080c4181051801d50041c0f01c01301c0b141084907902c14108124000c0e20700d50384107810009021100e84012200304a1a4811815051401d032001d0b40c0c13583c036207419510340340d070501c0b000550b1a5203002c1008003125066081b03280d504d1203028200080c0d175030450288164028a100348002181e041c042039001191540344186080140035146002966034100840321010503000039 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 993202967 1250 993201717 993201749
    0x6080f0702010902010507021516061d070e0412020f060c031006111005090f010207060b03150c041e0b030411040b1017040206091305062e1805031501 66
    0xd80140700300c424055040c0c4070641460069020402c2c020079250140340511800c00400317880c10348000704071440601c1100e0010300210a0015401c020003080c000611982c07022205015600300303000006da00c17691242e001b409001c1c0b4034108034104641107c503203080e48940300500030174011a8018500c1001c1156060208954441044950071550302404d64584c101c040210003c100c1038004660190070f45045031030242c4548000c608981c00f040c01550708070b507520301c4181c1d145020311440c019078040310000040b0382410640c0035402d11482c45403443e188900002c115400e189107038100014459001403e80300d10b094104000c1c203000102d403035403046184c0002462189060201c9507440e8849907195121030610110960318954040d00c1642e000d1828401c0000c10380d07d5203c4d203030640c46a040d0100d13460500006200141e94140055810066041841265140d11020a290988852405c44061000c80c140c0d0140e001050304810380501071082d2542040c135001003000c1c1220006084c2d0342000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 993204217 1250 993202967 993202981
    0x10030b06100509150906040303090f24111e0a03021510170102070222050a060302010e010503150a060306030308090703030c20090f040b130c1a120106080f 68
    0x84030302181031a002c110240446000d80c1482c840c481804905800c0491a00030000c00107a1035030410f41c000c60020b11168020700c13106001b40f0907400140441044074405044048081c400c4800b040340040812940781c80e48121010b00304008800d140c00e0071044e050011030a000103445107410481a00544104000b0350900107415564511802640c2c28500c442420a018080003000003022411159020300602016136202e1525840c0a00e4001d0b4480c61505581032501c10b5800c010702c1151102d26003001007000d41d80219555030541c00910f0220354940d0340980c031500c00c0206d0003515400ca0303078921001c02c00c1c98059011405481c0240c940940594130102201d5481981c0d002c0180010003146416002590344c03000b51801c4000401e0406444009801040c04014111040301c40c200c0c1e800284001c1c42000c905d1250400b09580407a03044010315200d500031400307188944a90611a0701400c1d03d50b00310502660307860b9482c20b0758080156901c0000800035501942d00004d880301000110303400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 993205467 1250 993204217 993204229
    0x70b130506070807050f1b10031b0503040210021507140c10020d0f0902100c1412042120010207120813050631030213061a120a020c0a0b10030b06 64
    0x7c020ba0601038000e10140c0c2414000b06034582d00c00da20506803101264008023940c0e401181001140c0e036600c980301c0c50140104140b1101c3c81e907a0750199000402c2c0000d210b800c0001c1c66520072140d082207411102518200d16003842120701131022400b44043c01c00001019130000c0450303541004c4140030800c00500c1160850751110030083d4000007170403c40e40f40e540620b07030001045003c0d160081d181240000e4580c200b80c01154030520b071500011301406024000d4000700c00181c41005035000304c1c680da649608034100840381e0220b8184102e0801091070b0f108101082c05010301441c40c52841511785842740041e0131040d0441182106c20340c0c04111414010145c4403880017558000390800d108001048521684050b13800e820305800b0000710158441e44810707200200722190000f9014034010412040c0030b82000c071103100300d40421950307601c0f0464009080e00200c0a0400503617500d03407102a141b0b4132000748001843c10f4030301400c00266111025045003100e0040b0b84207080d594600007040a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 993206717 1250 993205467 993205483
    0x30801090e070807030204050603071203080103051612030e041b09050a060e1008040501060b04080f0106050f030304140f0406260102070c171204140109080a020102070b130506070807050f 82
    0x383d1a402036a0400c0546050b40100d034004001406031191035454940c40c24040c1110603041d0b001c81d1241004004002040080f8844000103024990040781417980c0702040d0441460050308011000308220741c0f540da00e0f070045142442104814003200086500501621501c1c0301e90b074410070410703a00003049405020340c0d00380aa002400e4034820135225801b968050005801504c0755962941c021a107426040010005041d401c2c0051030600c0d11420160b095811a0b004280181c141503000a0541c40001c15542580c80f00d61013001074140040129800032003607800981d001d402c203480080c0008030030801c2d5040500d089240400201d000c034485090740308441008004181e1500c0c2040b0a0703003440c1d2031003030b10400e55013a14540132185012803c29000758106200c2003040c1d0700382d1a055a040100c4a00802c44040540824421600040e468015602c24000f614000054041400c820000000d000d05001000642c865610b410300005540110b001110f9a04c03031013035082c03a04040050b4001d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 993207967 1250 993206717 993206729
    0x3070519320627190b0903040302030316140f060a2a031b08070c060207030512090c0109060c0f0b06012006040c0b03270109051c02190305091c020904030801090e07 72
    0x10108100d0350b1704000b180b0001c154003858002444084010303540cd00c010700e15580c2c0030740b24660b403603028101800005c1c007980c6a8800c40e4809088201401d01c0850602d43c40011203c3c00034499100812030709100841004070f0000c503c081e48022161601030744039000041001001d4050440e10780c500384c0c1c0e00b071019103018010841410704c0b000054490340041c40710910a2030210b041c413800f400745034907000c0c2c19520806150841c14025616513800019500200308619000e0610450340d21085242c1440700000713044050610700007401640514040300c1130814540061860102c0702c00401e403030b100140c40440c0c3c5442000000a005525581981d0285c241180b40f08050b21b0000c58000302d80d242c610a100265494448000104005004046c03d20105403541c0d403071001441c3c0001d003882d448881d000410080c00b42c013034020a5021090703808a050642c1c0c0c580030711202000c4103585048940000f90301c900c0c1e1030100820980d215466a04a4003683d43c1417020b0086c01403003c1c3c0321320141c0914 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 993209217 1250 993207967 993208003
    0x80f0f150604090204091506210305030a090f0503030c0a180305030901030e01061d0402090702010504030801170a02060a03140c160f02180903070519320627 69
    0x441c0c82450164407a14800b40700800c0012041e0459a403c543c11041180a980559032868208504c4150001881d03004200c551901800c12480e41c0c0a06140009800075070090360722000b80c1c04020382c0c0c01d0148106600001166203a00d03041d10101029072002c1c1209000070081403001d0900d51840d180101604c1d40400a5030a200c440c40c01140103140d81722504032250340303d03a00040d149040c0351100d581d1054089000000b0b140c02e0050200c0010082c0444045a14000c00c01000c42d5001c0401c0741500c0d90340100c2000404800c0003d89484800e4101a40c040400140440303401d0309640001112440c4030384048966550310800c0c0d44a001d0b0300c0340d04248141d6151044c00240d0f40c610307500303105403008103035200300d41514410b45955a8110b51f0451913500002d0340340f0900c0420080b003000c07040840f44200d943d03c1070380e035044075006942e030716070400804000829040c40200810407118082c42c40846181d0701d032003083d400759603403406040c10494205454107134003000041100000345010482c3c5c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 993210467 1250 993209217 993209221
    0x141503070e1303021e03040302030118241413031b0b1807030f0b07200c04050a020702030a0b2208040b0f041e050a0b090108061002070807080f0f15 65
    0x3031101c2c1c006481d00304030114000d50940d02c0342e10f00c0e10801146044024030045440381d0844c41030508451100d2410100d41e521030702000c00140122504180c8403000c01d0000b8003184440042c280500380030406860f410606104204840380036001484040780680e44614208402410480400c15074500c00b5007604083c000003072495951300800798000c00c20108076840c00d60340c0e45981e07288204801d03088980040003c140140d003a4803846801e442d03418006000340502d1191031440c0e8032000b041840e406030f5250300009018500780e50544106030340140507688400f2032440c3c0f03440e0819003240c4001c0803110304901420503c81c400414141164008a01850503080064903081500802c0c410f2451210400c004940480f4242055030250301d070100b10a180e41c10401001021005504004901d43d024020144aa03030300c10100c64000005860707140c944011080203d05042141c3c110071030500c1642c00024451100081158490042d44291a0601e40109101c1d88038080d003a01c9180292a01c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 993211717 1250 993210467 993210481
    0x5130b0c18061603020105010e010803070f06060b18040c1404050f0a050d0818040e0a1104270209060a0812090301090c0b0d0e0d05070807060f141503070e 68
    0x400c1c0e1003000c002a202400040c00010b40c2980c0001121402048002483c0c8101034090107101d01405144255256543c1008a1035907a40101c10000e001d007030220300d80c035061201c0340c1d0004010301010024269200c03c10425022000c072911100d030300031403405c403d000700144604070040b4160126a21030707103010315100402812455150305c2551004c02018006017a6480000440c4158850f40d01251103418644440ea000054803281074001d42c2491000401200c02040e06070b006035220140c5005503074a0340208006001803859a3f503164a60241a407040c0b05402c0074550340c6200304c4d00c0c281243d85240c1840300742a11449407081c00d5202101c20804440032101521100c07070060300000e41c50300d0380c1d180c0e601880304942c0701c824010070000d07607004000c4040c01004070454008006004031003211000806900c00e03000c001d03002207000300d414000c0100d9a003101c400350801c0f9030700740040c4040342c04070036040106680d44841c1c101044803c040504001c00e108048a45405801c419a40c5e254 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 993212967 1250 993211717 993211741
    0xb0306060702220509101b140a090801290420070303141006020c0d111c080304110a0e010302030a020409060207060c120f0b030601090c090e0c0d05130b 67
    0x4606418070300f82c00140303408240b240d10803180f142585000400c4e80005000e01e10302120252662482d0590000d180f010400381c2014140c002d05603058000c0340d5501029408464400c5c1e00c0d0040d1400754200901004c8801c4a08034a4100d400614424003940c0b000e9401c0104580d850941c4030840140c9440880c6002c090f14054100c450281c100030075125144440f0070034094049450310301c403488100080c40800c2d0f040081800034a8280e07000d0b000c3d180c8546903002d00e0801141c040344503240c0004039581440c107207001001072580c40400d160712400d061500060b0300398110368941c054aa02c640014048025a54490403250042c0142941c40708903000d101c0a488400c0099507072075001c001c032100003038003485503580400312a6034400356000d001d0b10000a68004500c050302850400d01c0865140d68041050307030456507004000519080041c1e400d5072000095800385122a03141e100b0840700e603013200010100006c4c45c040c100425aa0444041080c85442d1360203006800d5100c00070b04405404c03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 993214217 1250 993212967 993212989
    0x51f1404020f07060923030c0714010923030f0706120528060302010f0504052b1a010519031509170406052703030a0302130f03110102070b0306060702 66
    0x14669081c6070a48544072081600c03183e0200706c8002034a21001e08600484800d10200401e101001d1442c02c2c030746000c104c0c1e03030f501103014201a91603868180041d0b6030003030740120001c1c9040c510083d0a0341085242d860070303502d50107919009000e09946c1600c2d0200101d40503013584c00c1d6450310b08000b800301c00683c2c01071100034024000c808c0c5e000c401480f0a41d400801046103840403a0100e04281184001410205110005070a119092009028540d00c52002d0f1000360090391030300c070380030454040c1080103104030b0078040e045100350b03503814512052124105042c0c840c251000c1d4274888000c00726001d075007000d02c0050300030206040c1c01d80040a83d80c028051980c05000828480c1e81100c42c02c1c1440e03449640b00d0303000f0640c00200c3d000440340130440c210076802250600c80c070803d5084040385e224482e0803090410554006031881955241c1000702004e4400440c0405000b03849107020b807280888030318403c0c050700c40c448000441c2076000084174840c040241101d4109886030f800d00c040c420358 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 993215467 1250 993214217 993214237
    0x2010c1202030702130c0f030e21090901080703050f030406270e100911210403020102041a0d05090c010906031a060a081e06090c030403020c0310051f140402 69
    0x300000c0f400741e40c03410804600c6201c172080c00102d0b40010100a004505403083c00001e040c180240e09003000c101145549400c04a025120031003484030b80707400021b00c649101140d02c414130000210700307408005482025a8880c0c8101d42c2d104596040d81a0340f4040c0e0f20074031000440000c85140c0200190071840c404071903005400c00004c0e03c82125444a50b0221020003002444240801c80e07a201c900030410080d2514455500c4c202800c5161110a20b00c0001008440302400220341098803d504960080c0704034100e503001ca1016045e40d000960240c1e045850321800c01c008560810400304404ad683d21058482504452400500354042c004020580041c0c8000b0308050005440e0303a4010300180d00160307191080e80c41c04564140107055032166003440f095443d8208071440e2a4400055085041c40c10351546950b56403400300e2420040404950309801600c1c2d40e8207103d800c80e0041805081c03000c420388007005508101007446c1d01d4034407400500e0007000e10021201c0c20035034014456910 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 993216717 1250 993215467 993215473
    0x1703042909150705061f1d010b03060d0807030f080c0307320d06061403010608013f0b0a0e0a0209370b01030203060904060c35060a0302010c1202 64
    0xa82d894003420302600b240c1c000c0ba20134100c404140942a03008003c0050889074035487d031900d03118180c203030015030140946583c8500c004040350856031030f070410003000c40d404940311303607500d0080c54010304111000001c240410742040c04150164520f0055030300c112865a20001c012141c10200d20500c00320a001c00f00313100e40040c81c6040002480003d01c81d1074038a070310101c1c2c440c0c5807160041c0480c101a464100028003031006001d01903000c3c484070304545050814070005043c1c070000c6822480da40d41c0ca2050449903240030500c212070241c05890080c00707400040501c1d0b40d03850f8220156010065000881d82007001080c2c01403400041c0150041d140c02941c1d03d400946480c0242040100090405c1200110030312016140c040d00070724004407800e01e011350450800c84040f80041602500040c4625255142c03c46035910500d00f102c10351024001d038400807464141980300000342e02c0391030940e102080000404a0a0100c040300869034181d485044924241d251a0740001c00b002117442180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 993217967 1250 993216717 993216727
    0x90406020c0a06150801050f0a02030601090b0711010306050334080a1505161b0213150302031c020a0803071704030809061f06030c09170304290915 65
    0x58003000b684210038414003000800710302e20352510380300c89059402030b12241c1c101403c0200700c1101d92410ba4021210b0000540c40c0e071522030050b20f040c80c042e0002c000210740070481c58240542c0c6440880680800c3c0c80401c901529403061507110701c9003400054070b14040d51040407070340032180b112208160060010035441900d622415040c0748a41e0700a40d00d01000c0000000341244a100340c0b83c00c5003500e40d40c6409601501c0d8054003034142d45c0843c0407800004c10004003551504290003039031459a600800941036049465801104507001c00da00900c1483c3c0001c5024403911804041000c0a8005041a0790180d65028083d4001082c480410400c002d8540307a2000160f81580154403d8070717010b035a894128034451a003100100325181c40d25055400c2e40070452880f4080342668000d14020910800d121002d43d0024843c1c0d000d00b125680070300c6c16202912004c000f400a44802083e100c0800c2c02441140700100c4200c0c1c4072042c0c80c1001c01c010952450a030944003040801410903038108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 993219217 1250 993217967 993217987
    0xd1a040c0f0e060904020f1c020c0706080604140f090d021501030b040c12060f0b01170433060812120c071410090201030510120b09010621022d09040602 67
    0x29800200c00b00d104007c0200c0d40c807920005090442e220258107c3d4110304000c0740340c202c1541e501043c401d50080c4601403011078a140c03126040780190031644183d0210500b0300c0e584e40072503908211031500300e130b010b603600405401c1d10120b40300e02e9144c0003074031000050b425074460060a15020f0000c442141c00540001011030204031882d0141d4012200024621055030310203041d40e000d00e40050402511002c0e0035503004075019000d41040d00042c070305098080d1140040f00078044902c0c0491200b084000b1680081102e800140560f00b8000c01d8444001151025400074001d00609160740e982182c000f8a14590300e1000c0c040d80ca01503c4140b00020104116905050f651028546050b0700c07041c15000b5541c060003910f4004080c03031143e040c01d0b8940040d40c4900703840d2139001091003400748040750b41903d00350055400341c61300b00942400000c118088030300d0680d4011040f80205da4480301c0010b417200031600d10386002c810795005017019503c14100070b140d0000801c12070b103840d030074480101d01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 993220467 1250 993219217 993219221
    0x105120106120f0b0f0919060e120c01060b0a08040f0302100204120204060803040b090d1403130906240503040f0b090c01110606181302060d1a040c0f0e060904 70
    0x5507400b410400c403001d00c00e400c0c04c3e141c1081c001e00b0000c07000582c10510690700d5001070380e0128950044484049050340e440d000b005002210f61600c034a20650808100c0e501e1502c0003000400040d0000f04801aa03d03502e451041c024440f040c40428400d08c00078010503990800e40c0c4107588248181c1e8002290508500700320381147e000080f007100c0300300d002801c40c102441264040c000d07a10081d42010324140d0940b200303114102c142c90240240f008090104040008251003000815064a1315070310014800200c4d01168030644004909049001a54141081e1100c200015100c030000150258040c140c540d548040c00440c1d9142c0b81c2c46100000c200e00d4902d50340a003030302601030010343c42d5260005181c4140041c401050f604240c3c00d000d683d98403959406114040280841d11a98564400c0030343c01c00d10200c065001200000ca03101020310550100301c4103500c2070280306907218403034140411510950388601c089030400c00a260701394098100c11180d035800908261400e0880004241 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 993221717 1250 993220467 993220499
    0x40e070801030203010b010e031b03030903030c011e0b0d02010c03050d0e030c0d0302121501200d0305070809060c09190b0a020d1e1209050a11130606080105120106 72
    0x200080c8000014411484c0c00c0c000c1d00b044110900c0c01100b0740e84c1010010340c98130590b0884801c4000340c4103d01c003003a00d0500907a0307942100203040d20b84070303807801000358040e044510380804450400403102406c0340300340c4142000030001608480d1640ba00358010744042c00510000d5092110038400c0c011a41d9250186c030044420b08005175485a075100c01e60703403a0083d4003483c034050500500c003841520715022080342e40802c81e18803040b00c01d4515401600c80f098509003010030a03000d41118070914100040f10000001541d03020000c96840324000c4400300000c2c0c600072015000000406d9003641b206000d40b5003210001c1489603107181e00300d15500407100503400708000c4100400c02c801e22603018040744502d80d91600340711181144500780c44442c0b55000e5003000500c24602a08005150543d22034052564010308907039007440c890912600c02480303101038a102e0b490550004503500840d001e603038211481501c680d2460b0f400c0c403081100d88a44685802142c3d0358610000944280794503280b0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 993222967 1250 993221717 993221731
    0x30b030708061f031212020c0a0c030201141213060b0907051306090b0909060f0d0609061a0607060f0f0906090b07051603080402060f030f01080c011b02100c1b18150614040e 76
    0xc1e030344bc0c0385100142090003500400b200d5070205000e40b42503038944418995010b03ca8480e0030510180514020b4000d0100c601c600d50803102090800a41d00d801c41c4c014502d14a40c40030b08074626944640803141c0000d02e01600d03044581c10f0010782c1072401c0c0340c40415080b200040210b00c1c6c0940f44400704500d900c40e00740030384d10b698542201400784071140c41040343c840d81c0c041240300001c0010001c54200d201c0c00da0020103035a0b07140300300038481c0d039154010078402c507015100f40b02c0c2060300c0c280070000c0c040303d40d000c0e92000b020f4400300c1d0000307000d48115500b0044101c50b03c4110b141c65202601d070000c0c024001e98100008128500c2140030728002144a41c60b240c556080315410706110624000003048100d05205404400d8000300c88140c11005e8080d50440f00e40030000005001180d0103894040e00801c0005102e48c07101c607034190180601e043d1500c0301807045101c1c204aa01d032007a030311031000810840f442c8900c24041188034440005204251098451900f07a44440d10140d10b0000c0741c1207 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 993224217 1250 993222967 993222983
    0x70201030513170a0e03011127061606140105090c07050304030b040b180708070b0306041b021b0f090a2705070312020f1507030b030708061f031212020c0a 68
    0x46180d50001760318200c044007a0020000103544039103508140c400c1420b00d1964252801c695031007510103518240b040709000e842140c41e00c074411544174005000701000c0f91903030305140b80c44004525101c1141d040f0f0304028003c0415803258140040240e20500058466000801002c000711701c1144c4e01c1d45c02144181c00e220f02038909800000c007292121141c1d200c294000340c0080080ca031000901009803183c41c680c0c0d55494507080c0014008100b100d07010311480d0070703c80c694003426802040342c460082101a2440305001c80d5410080e0000d010f00104d50b00405d801c3c080340e0310b0040c0340d000d0050000d12010910071040100008180712903000001c88280d071121405000f00f010745040704070f0250150000b41401318401d200b40762941c612101c240e102480c02800510400e119407c040030350400a0192450356494548807602c0ba00b0844210b20480d540480b030182c0000317481c40860441e0b800c005140329107006500215000351000c00c2d007000d115028003500c6442d840c1400072928040c855500b07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 993225467 1250 993224217 993224227
    0x3060a0312090f03140c03030f07030e2101060609140307030f06180602070302071203050307080702101508071d15240c0c0f150c0a1a0106020c100507020103051317 72
    0x8179a10700000c50080302d000360030501031421008921070507900901c1d810f080c030701d2090700140c0c08950780c0c14003c0c1040c1440c58040140c008204410b600110954106d90b58000b101c0d03440d04400c2002a440d59000e03501a80020010408646510003140035140b02d0350300440c41c4a202d04e400e94048956034401e94001f68005607440c101901040000000d21075280b69120170f903040d450182090100901c08400c1c0801c090000d01d04600c241710400b40d40e03540390303003c0000920082d294400c001d01d0707000c1c0041c144142e000120f500d000100c40c070b04940594124411440d44c41100640b5100c1d910040316810898903080c039129184000e00300101d041e10b1640306500c171410140f0127403520710084074860041070039010f0420162541107036851444c804441f12075540c02c0da40a503071300d03185003190003078400c1246030740031001b8880300b40c00f89048031415402c590300840f0200800001102c0420048007003003040113600d00550007500003175400700e16258512190150350b00c0342c0104090390342d450000040b00042d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 993226717 1250 993225467 993225503
    0x304090c020f0d090501170603070b0c160b031b0a0c02040f1b09081905030c010515031006140d0f0606080322081002132c01090203060a0312090f03 65
    0x420300d09202d40ca4004c01c05464240041c25400f030490701751540c1c103a81c800207095a241042280018100640705590303a0360004e40050325000025507001001a80301d400045150846064034012009201c1100402c54240f01d404000d61068100405206802e0000e07000741e42d030ba102e507a41c110810800401c0004c0c810f14403510318008501d02c01c051048030700c001d002115001a4001c1040c131040300141b03e050140c1043d03841d50003506c590039140c3d0b01300310820118400c000300c03400c0c900318142d00315000351722210202c40607a0058090305200050459900b00549440808204410b000310016110101c041c0c4980f400e136890790308110380aa00004d03c0c403041c21a040300b43c0e1201f414400100107600c3c00d0901150b101c2d4640d481c200401ca402248500740724011901d0b400082c20100062203202c1e60f03a4104050f5403599200c5001c4003a40385000180320280c03402180e110303d01c000c001e465910300b155078014482c9203034507041c4208080c0c000301088040c803d031001e4000c1c5006920054811420300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 993227967 1250 993226717 993226723
    0x21801031a0105030d0c17040315020403030806030f1506060403080a1806030902090426031816030b070f180b0717090a090f0b06030f090c03010c0207050409050304090c020f 76
    0x20b4400f0b80241d015803aa070440d80d901404041209074082e61780815402d80e848040703d43d01031a00003421984960700c0c052400c0b2450f0b4011b00840340700c1e458146080d521102010f44a40f50b0310410400c41d0030002105004101a005282c1d1006000b806581020f48030f40f40c140c4141c0140c0d89500100d8241c01d0481c8508802441e020020505032a0600c040c0c1c10aa02041c40300001600007005002401d03140149000d24a142c54041039180200c151285000400d488004035070710f00c0c50760355002e1080c9203001522101c8061003504d402801c120020385034100111044904a2219002c022221090f0b4242d140c2c114a0100109400e503c459291451818148282c0060031031241d0311034070400c000081a1540116041114580d4000081e01030b890f8590201400590b94404d91251000080003a01c0200e407a0207402028000304480d000c5074481d003494221042c1d010000c0150303000e0041008a0301d81600329011040c81038081e681000e80c0e5a010505a40540c04c5040241e04100181a4042420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 993229217 1250 993227967 993227969
    0x40b071706030307110a1e1a0304080403080306031e070512030a02062d04150b10092714060907050406080c07020d0b180114010302030d0c021801031a01 67
    0x36a88410980c00d08100103580ca1007640001400e561402038200e8907540e03190011001000598224007401200012440100c1800e00801e080c0328148800000c0c2c0c4050704040d03d1090b688128100e01d41402c0da1200440d0350001003180741d042c07054080303500c80600440e0781c1440e1070200b44001c0080d54244002c201c505c039403150543d52f0a600501c120020340c4d60021b9290303080b40600b03000e20810030704c0d03505440619052550700166404910705000404c4450201c1d2240b0007020344040200c0d60002c020000500300d0424140c0014240d00e130240054032820892200c0345442c1c0c041944060071b0740c001d0b00c09440b15900c0d031040c41450322080014600b00843d2180d4031852618003145001e08004e03000d0716040024050104842c4082205e000710b44484c4511802160410f5141c4440d2618400148424100308020a49542032004540c002d9030710a805a050760750003405030000301c14030001111610440ba90581c4d100884111880e00c0221800c96a80a140150110707040c00150800d445070322001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 993230467 1250 993229217 993229247
    0x307020106080f0709051305010905030d050601110c09130c080c0108070c030206040f080d15230a0e04050a0f030806030706090b190e030f0f1203100902070614040b07 73
    0x1111050341c0e00c3c03460115072241076400c02d000c002000d0315000f58070880d010355118014102e40c80c01543d00c1c1803000010203014852495001400b5590310500110350801d240d42c28004243e10032200c0c184649848449144d1001403410441540d80c1036483d030017001c08041d84001c0300c07a000700040341d407107580c000c002d1684040d8500301000d600c40144d9009583c1e01c1d0081018007184044400241080648400c441481681b8001400b1161a029540b171425811384650084840310500480d070b2000c60041a0131403000081040c100030349000c80c19608404020000c49090003004001c00000b520340c05441d00b034601070b0b07540c07088914010f07081c149415410340004c1c040c03005060042040161900c11200194041032800341191080d02c1d05840c5060022100c43d498024200d81d401d19680000c0e105280c1d035002001c841c0784521100c43c00c905403100f40c0c0c440390701d4101e6030303014040c02781540c00070000140f01c0e0b10000b80c0c000c01c804410180c2038041c4e50858082d06280c0174441d00c103910210b60b04510403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 993231717 1250 993230467 993230473
    0x510020309032502040e0d0809071d0901060e102c010302060c011b0e131812050c150a0509070e16030908032a0306060405090c0904060b030702010608 66
    0x42506445660303008002040070a10080c103a03103d842e100880c292082141c1c041d105011070310f01c0a0784141c48000400d600700c00280d00e940003400f540342c006410011118214000e1011804c80e0000305c001c00401824a905503488400001d004280340c141c0c141310391000e8480c45040e030b081c0404c00002e422204e60303031442c5031309071062812304144641c003a50440380c1c1103400c02da665274501c2110740034124605680030084158194000301c0c40d00702196041c80c3c0300c2111803080c134021480001007150300240c88103075214030383d000180000e1a040e80b0690f00540901f007090522846000007850266201c00c14250400c2c0d80082c402d00c1d48003400741c1c0c0e412103407000280c082c0714103003071303120540800062a07048141001e04580030741d94000e03804600b5917508001450303920f1900000e020241004149008a8203407540001e00b40d181f1040c00742c07405010f000b00010702c0d1614000820550b604007401ca120014000c00c001ea4050b5078a00c6044024080c10346030329141d203404580a030840350150b10441c5150 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 993232967 1250 993231717 993231721
    0xa0801080d09060e1908010605031e071e0807260a11011d09180607021902060f0d020c0f070902040302130c05190302090f010c0807230a080705100203 66
    0x7030300034419070251210f910300401d041190314001142c000c81660a084021645140404c0f100019046071090b02c10560880f904240075a80c1880d4015030244010b003190081e25040c4295070301000c0580d01120b0000319a0030f802d40785c1d45e9035420b100c030b40d03400072040d052051104a400401c0c061805c419000c4200903000b0280c050302c2d01c00603920210b00340d904101c60a80101b980d040107840798020440040c004843c40d140241c01000480a080035100041c4a803800107031505200088010b602c3e002c02e103001c4426515a420312540341c01010600b00744c89418840340d8001d800c14030107000c0075030500008180c1c6441a048445c02c000d030580019445500420080c00961a10510000c6584042c1000a140c211184040b90300b8040c031420044042e4810041c07089640c0d164024010311032049402e1030407070301c03020700545081c41550340060820380c0078803401c804194000005505102600011017003e01007a000504080307000710100c80b09030000c100b0b042800001c1089900300221200f00714a14 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 993234217 1250 993232967 993232993
    0xe0f041103060d1e05031b0750010f080112021e030111070b070203070f0f02190b0c100204060504050d061112011503140a09081e0a080108 61
    0x5880002d0506015044060440c41040400c4803160301c4048051185810a04a8601140c899210020403103d00740b07039a9000b000e414000c9410b034100c511661071072055100200e9011290600d444100012005002d904850a124007000c07101d80b042280305c4072a80a0000005040c20544454003420488910010300014654417009481503070100c40c00e0040320382484007091021b00710310605805500701464481c01126210143c0801c0f80b00c2c11003000c096484c143c0803641c034028404023401980142c405400441c0328400c420108900282081541100401420980d021207600c2018024000106603003804006e20500e030b18000c0c009e203350b10341490701c44020036901490160714420480300034100e04105881c0d2019280100c1d902c0383c15240c1644044d40307601ca40c824410f2480041c41e0080b42c0114910030701c071710103504090982c0e0592030313281c40d0921802402094012509140104880100c0b6030707500c481405c60702c0000301c6140c0c1c4c4000c012001890340c80180e0200e403c1c0c0c0e214007174040103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 993235467 1250 993234217 993234251
    0x120150a0e0a03230d0f050403020f010e0604030809031201140a050409050d14040e33090a15030f080304050d0804050d03020a0e040f0b03070b090307030807031e0e0f04 74
    0x1e40124000d001040410315000304d0444c418001131414403840c003045c1e014440150b4002d280300d1030003078081c1c61201c0c1900e08902d0a072200075540f800c10703030042400240024012105160090b10030030460b400c1154180748140c00100a030000d1242c0440301c070740034083d4a80406241c0140c04180c0f400c2c8070a440c45d503a50380e50380f600082003005121600c1c01c850011850314040e14024040001c0b403048505150f03544410101e00005418540030b101d03070501d2507004c2082d841c9075500340003400d104240ea907203c400f400188620720a090581403a20303000000329281c440c072115441d000d60354007507803400c00745032042c80c0140c6140c03260140030041c2c2c00c01020400c0030404213040c00490401603950408407508070f840080d140e411a500502e0152000b8900171280d101c3d201d1440182d0450303810f42d4541a495046028401340558550301501c02880050303141d4010b800c805109081071a101d5005120100007500241c10150000e860b9032200c0c4013a26181c01c3c406500351080d41e007004040e41070014048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 993236717 1250 993235467 993235487
    0xf1a04033c020a120f12180f0b1c0e0d03053103050d0b0a1d07020303090d21060e07090b09182a0406110106050604050120150a0e0a03 59
    0xf40c40c0c00d0584100090105c0000c42009039a03010114072240d2510500c0600182503007500000c040108003008941544c2004040042d196905005070502d400510320349101140ba02c840e2103000e494020020941c1810494000c000742c2c03549000c20355103804000400d4031100c1214039103441c1c0021025030385400212141c050141d80518040c0ea0300c0c44d41c1e011610107064403428480c0c10281e180400504450300b0400c0c0c40040110742015881529115001c03a940c0c04160b5418801c4d400040c0c1c04000c845c05410b003e28034002c07200220074540100171400c0100c4c0c600368800940c0c0041801001501035208250704068450701c10428205a010408509110100b546607a903030b46440b000b244032202086c480c20200140c844040110030003aa031085156000740c407508020821402c0d0150340100c0c18000c21003035500250805042038030b048011200c41d03080e002d1034100c03800f84800384e150444051125882c015008040d090701400d21003e47e00031210500d468030481e0b080114035600196200b60b02075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 993237967 1250 993236717 993236729
    0x50a1107261906020c060601030c1b0c0504020417070e040b0f090a02090403092303031e250309290904020c011b080c03010f1a04033c020a 61
    0x1030440101d046880c68002001d1140c4080c0c88055081000c20240c0d4009120750540801916001d0321450019015100d13035030546ca02084c43c2d10085c000340c0041c51482e11101b0300499200440c15a210f01180499001d60041c449420326042c0c0d010348603004000302001800440d54944d11131074292190080010080c02820b4840c121a0203c1e000200400175440c11940082c44200141071074a4042c00c0702e4268403607c060041c2604a8610303000c00084440c1c040c84001c1c0c00b0350300c4c141d008aa9006500c546003400200f20030140006504440480340b00068200ca1301079000c1100628100035140c2d0985034070441c00c0c2d40d00d00b600509000e5852000003404011180501e403510f505000103000782c05103038688050b80d8a040c1c40c603445040d070301011810024041d01c82c445a41c0f1081c02d0794100b0f10090003401200044540200441101c4500740345240004810783c17410142c40e03540e0144003400d059004c0d0350015081c1064507200c3d20010b0500490395041d400604081003070b9000c540ca80000d40310324 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 993239217 1250 993237967 993238019
    0x12060c031303030e0d0309060c051e0a09080a06061d0606090d060618050f090d0f140409020c1605031923030c0304031a040c05060702040f020a050a1107 67
    0x581c01c06019410080c3c0042c28981030318950f0f8150b24005004004240003940d4481c209882d500c10b00740100125071000455804030910b1740324051444125501c0b41e5114400c0208600000401c04000d200c1d0f8400d0f0b5100c4c040204032589006040d41e402c85075000031091841e558800d001c3c1684e51441200c1941800340e1700450703e0350060a207080108401e5000d40940d02040013001e4100200740d01c4244640e09010020245803a1402d4003680c03403000b08006d1003c6001c02c0e00001d0014010980ca20f0a00300e021100c510300364403445584160780081c2d0140b1a00c0d4030000041c03840301c614107400e101402040d4010705228140c8180d0f81c110041400300509504150142c0344440342002d00d55072611601d010841e0368600d5500300c9180c0d2070b0720911007500c071105488164550704c65681180e80c062500292007840407400e01d410010395034030200c400c0780d115039502c0c915054101940050000c1001c15250781d600d4002010010304580780c91480612203400041080c00b20302c8400240c000244403180312 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 993240467 1250 993239217 993239251
    0xe0618040309090236180a0e0d090e060111060a0f020f19080705090f010503070314010905091006080d0804080c1603020f0d020906060306060904090b01030212060c03 73
    0x10580d90402d194021103c0c0d503000160f00307400d00440340ca200c00c16411172000c040c005260159071a801126000c00355031b0200300c24000142c194000350700342d50004415480003809410b01c64465141c20b070a0322109000c0390707031b0103c1000b841c204040e109a00080a080c400789102d0524042c9880d00d4004107800c0005948080c0030040070300580c16581e60450a09010355034040040001e40c1d860700c6800504002410301000a408601c1032054035048c0802906c50051400102e00561b808d8000800e1030040507920b40b1044112400c60102e18000c000c04c140000ea14101190841d08009509080f405003070f04044042001c008001901c0101055600c0d0401041d2124034048100c0d100344209103a640c1300d07e400f01e00200d080708159804692003250b00001e550740da48144030b443c0c40798542c0650f1022031000001c001341000801582d1100000300140e2401120100103021541a171109a650110090061086091140d4801081d11184005116a1404a81d0180c25200013080804400c3d00000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 993241717 1250 993240467 993240473
    0xf010c02011803290916060503191a0a05121b1807080a0f0b090a1a06040305070905130512070201031d03032a0f0c0c03120c06010e061804 61
    0x703208026540c0700c581e2001900e5071444140010741100d4030103841c013115001048084000003442c3c3d03c10300701140860b409a01c4e12030143ea1039003000f403860b2320448101d014031640500600c58030f40c44401e5190075109408640c3d09025900740d0b20b0b00001d004e41c040703000110501d8000145e8041407075001116001c1c0031410030209080035024061f00000c444124140311040d03401030310940c031414100302d0802c47c0c2408118480152042d00350610781129442001c00e49000481c1c000ca156070020010400d500e04000c0c0101b442c9501c20b40c01594650032403501800201214080d45802c02c4414582003141c070121303143e841c0c03101071144040c00c5d02c540000d03190341107900a8100c255080e100b04d54030302d911800c18000c1a261b6200b2a0024202c424000c892509041114600780c0141403443c3e42d41d04184441881c10b40d80e501c120000c0c1c3d2144100700c03a000540d40c0403c02c1d24500c41030400c1c010384911140000600c0c0080c1a0050700584081208104060b05c42c0b101c01014040348060605d01e640300c0342 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 993242967 1250 993241717 993241757
    0x1814070c02130f020c07030b090303060a0b0a2109050c150406210603240e0303060d0609080310180b061905070609031806030524060408010f05010905060f010c0201 72
    0x109a40c3e0682c004502e50621840201740e4004036801010b40c014107a485020880c0c0720722003100c030154440090101408844941400b400320407071030342070002070b101c42c44d0440007010222401c080e091a07101c1d41402c08219007400b080908070020349001504088121080119024601601042061085904001c402d429900c400203c40100d010090540c41e1b05004042440c403142d14244944488a032a003000468800d2a68441181020f9030541d142c1d070701002541c0c40318203019030b0300079219202d450100f075171720000714054604c0a03c80c40c802850518214586501110504541032a041102450b40c8800003102d15004244040d406500708909003641c580c0620203014018a00e05003440d0105500103130800b1544951440038000d036955080201c094400c1100d04444285012542d1b006c04d145c40807030002c11080042141e4100750f1680c0c000340c2102c1083d03d0b0501d4098507100100074041e114410950404c45c00d444150344401d8110000c0c01941040d00e00a040080c10050450501801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 993244217 1250 993242967 993242981
    0x30509101e0f1b0c03020a030818150604050105120304090203270a05010b06090319020103020403120207050406060806010203030711030f0d090507120c0308071106041814070c0213 79
    0x9581041680d00c565865001455000781000d554905070b6088840c3c1c07402500d05450301d650582c002d00400700d440e0780490b9040c1001d00003c41e402440348080003c050288246c1d00d0240039901000d00c1d510340700b000c00c002e440069000d80c0c01000101540b004d054000310844007940c1e20243c0c050307a291184840b20030150350074492040f103040ea0408502d43c1d0702c3d000c02e0a01d0614002d0001b44038250440c010000640300340c03c04164076a1000c5502d9800301415034200080782e005040060405070303a40c40c0c022003080107128410058002210031307c070b5881c0c80c1c0319100c0a0300341450411403600d00360340080d581c2d01c0054011400d000a0b444c0104015400b0003c80b07050241c0c01c81d620f5100c0c034241403c80c01411000030708a941c0d01a148003c101034221405400c031643c3c1180540c030403c0c0c13070b54841c20342d954040d040c01d444003040346c014030140361503038030041005000bc1c240340742240c808490300d0004c40702c0301007aa1450300b48074014810501c3e402400b4180842d0115141156203412541a8004040d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 993245467 1250 993244217 993244271
    0x302150901230706050a1503140c0303070b070206010e0c0f16020604320604030b0a0603020438090105010f02011b051b03030408030408030601231903050910 69
    0x1c00101c26405403090010f403900a01c01d050034051601e80100410564010351000d020030260980100003007020169089014090301040d079026440c0440820b085610440c01591850841c80034855803581c1004001e004008100c120f004030300384280b1101c8180300f440c400c0c9d00442808103510144201c50107200410aa0040038142c2e40e03940ca90040000c01352251440c80b003030010340081d00070180d4003440e600304824000c000301d01e040d05550702c0c4219928064041542940c1e2010040700603103961040651106252a12040d4481c402100a0320901150380c03850240341c5075141482e0030348404044030b040d16070074204203101c002814822401059003035154003140c035050004000ca6078100c40203082c1080006880311200d03022811035541c0348000e89000b0414801040000c1c00f00715900059504010149404401d41405010304000e140700c0c6401d90031080301c0040c4002402c18a06040016003406080078402441d01e48003143e182c00c5c0c0c8a6842866031340300d0705082c64034a0040034a05031411 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 993246717 1250 993245467 993245507
    0x20c090906090c01021603080703050c03030903030406113c160c05010c080d11070609030f02191106031b0d0e060106210b0406080a0b0618010302150901 67
    0x2921080300c03a92071400703890481960190756014403d41d440403070340b2455440c0d207648141d040751440c0d8418a45502c0322909408101c0c00b03000500484005000450080d11220011900c030b09103803d0803002c42d203900002d02d2046404001c040b003400009025a035401710b640143c0000701c3d501c6001d0461340c1c414111959490b80c000505103c56201c900d00041400b40071340c0e00900302c82d03110300065070000068000038084107021700c4054814901d5411001c884c490040c1c00c02d08107201c2e130f507c1d2030035100440000c902040010940681c0c1940c10440c240001c42d594040001e039100c0c41e2941d18203191100d0301c842c042d050010009a5a5030303460910b450122103141c038240d45140b40c0c00c09000a1400d00d800c0300e00d901850000003045031040e0b407030402000e1048a9803c10030901d4902400605008040303681160701d841000441d41014030840d030009004100f25002031802804018883c0d00210700645915148401440540c40320030b10001104a10a2a5a620010300380141c5508041d0212400c0d0f2003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 993247967 1250 993246717 993246721
    0x1909140304240305070504230909010518061509100e1e0a0b060d09020a0315060302040b03030a14130506030a0911030616120b040216051b0f010c03020c09 68
    0x8101c1c502c10510488400e1014a41d541c550404806545055500100146041c401403000c04100c0c00c0f80c091000842d64032420200250300440c880540448810700603954030410031501024940d0581c240384240400b410039803070004440b03d202280c61600c02e015202180c001110508582441d90140a03038540101540c500013995095648010004031400310602d0702259151546020301c1d4680c00b030080500381021540e41c80c0740d00420340c0c09402e903846806c600700080459074501c10000445035070640480c2c99802c60041c801510000c0012900a0340204040c148a03a07200140d100c03d4004c401c040c0d0307a02c00710407806080350b08843c1c1005500840000c28040c00e00300030740c031842016104040a03110284400201619841e0441ea410884400c194241000310b105980034595041c03040000582d5200d80c1011500300c0c0c00c520980b01440c04460305640900c0700030444110b405628114500000c510b0001040482982841d51818081900300d544200760080c40340e20040d140142100c6054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 993249217 1250 993247967 993247979
    0x1512031e12040c170f06012d06081006050405032503051c110a02034804150303051e0408030d0b100f200c06040311090703051909140304 60
    0x32880d07611035220b04c03d500851900c40d2000102d074a014109190340a00f02d0340e880e00c2c1012007031301d9880d1100e0501d03140070b80560044c00000d03032040f00071b072500750784114044c607050806180b00021034104406108003444100000d5600080c80700300c440000c1e50170382641c0c40441c00e190100050b83c00003482c40c040c2e4008604904a05175070900790200b140d035481c1c011100b82c081c0940b42c2c145c0950194042d000602e64000c15030100d14401503085010300104000b403c112541071a64003001c2c10940000e0041d0303500c0c055031801303002e03444c200191201c20076041c030701d0366401170003030b101d5641401083d49002e5603050703002c40f44509a9000b410380d032042d00c0e80ca40303104008030028070b06a54041c1c810340ca0041490b482a1003520580381800090300d4804c0c0840c001e008480c16000c000c48420381074401c002407856a502e40001400085200d401845c0c1d040a03880100840300000a20503810146400f04110b001071074040111450b0311070007000100d006041c10300c00060003086080b4000e41c8400100040c00d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 993250467 1250 993249217 993249233
    0x507120807050d0807090b0903100b030f120c070b09090a0e01090b01060c0501050903090d0b040f0512030f010b0a090605090a09053105210418051512031e1204 70
    0x10400340307035841021036611080e03120214010882d0062701640310b68841c40e4059170b10341c080030b0500c800808881c0f001802e10642072410740c100c900d407503015402040540c9a40c10800030741c0090140c9105146c02c162038800803409003640140711403020740e228401c41380c1c010400e602041842c2d402040d1244950786a04000c0c10800070080100d80a620340b0700042d607081004010340300c076568010b000607086001c0d0b0320f96001c200780c041c0080c2d9141e28420010000510200010702034900402003407522840c0054040003082416400b203002c2d04801c011002c8002c1d400000032013a1000360a10984903509400400e46076030081d0403851620740741805000c1051003180c004c042c0c0b200a100040d4101500d03a00d010151284004010110f9010806101030541509001d404510b4060480d07400c1903902d4a4010800d068028400d600540c0d80c000d01458000302100302d6013000060324800802003a0602d155581d00c01d2407048400d28030f4141c1561000c0b8140e1049034442e160382c0007400c03150704203030514241c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 993251717 1250 993250467 993250471
    0x2060f131e020f030106150e1306121a15040f140a0f0b010201060f050f010203250b07020604020d1101120207060c0e01080f01120204020c030c0a0b010605070507120807050d08 77
    0x110800e1020840f80c5075181c14000c2d9400c1c0c4100f88030619100b8040102036440b40c0c107654910b644200352800c50240340309280b140800400442d400410031071100e00f44410700c900d030440c0a174410941e14007040644e020b1000a0010420b058034000703201040c02400e64000c2003070a41d8800400c1e0000d0510400b5510303600002800c0d061014100040701c00900164201c6146128018552841140401c080e00c0e00c4400e0a070002810300540e440d203182c0744100e020f0300b00d1348444603111421599030707442486420002c442c1e006200c2e000801190400d5000a80104001d03d80203100d00c101c9030001d030060340314100440c140050301d03d080d5240c4446180080203005400345850000c0d080b140301005542c8501003440c0240e000010580c2c1070303403c0170405c01070108408402d9801640800c0440e5016004000401d44181c60701c02400b03405103a4603010501c0f00c01a40000100031092104201240d00400c08200301c0300f10b410101204039091400009600640d0405031140c020001c80f0a903050308148424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 993252967 1250 993251717 993251719
    0x1e0906040b1f020601060e0d060c0302120109060305060a060503190c0f1d0604020403020a061b020a0e3c090709020a020d030c0c0b0406050415050a090614010602060f131e02 76
    0x402680c0c030b0351b030304481241450340c01640c0044400040c1d008600982c1c480c0c0e50005070b6140151500d1301c4103040340c04041d0280e02c140700c55076540384c0c1002802400d10081d604090050014455107140c140040d646901e00c07043d6564064064800034100041450100018400b00c11141c200f541c1e50404c2d0200d191724808030454210354800015a80e15046c0708135401c1e40d50042406552905152045481042400743c400d000d5021350701e04c01c096600d0080110003802d00c19080c41c01841d00f4100460300400000c1308140c0e1004284052040a101e201d6078507904900030511b590716508c034901d840c50071126504c858801d510001c0c1c03e01160790702040c21600c20b522601c05000309110640e00301c40440300c00202800d0b940150012800046094004030f4105000b82d040c01c050420150800080340c0c0c1c151010446d443e070b01d24a20b001c01001c3d01131402c00e81e404d502c07010683d45c0351030380103503e0b80c900502850314000752034000781e2021000c1c2e2400d4440380d0403000303800034242d4950b08281040c081c1d00d426 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 993254217 1250 993252967 993252973
    0x703210314070804080a020f060c0c2109040209040b040c0206090d02030a0f03050702010b03010f05100e0c18032514031605061c090804141e0906040b1f02 68
    0x4541c60541041010b01510142d503400c10306a40700e0b150071500740c104c510303224114024044010240d10003000400e000300d0000461a99a43c2c0000c0000e182848232100e003002c0b990700100004a0348010f0007a2603d4043c140d402580d544d012400003401000c4d108100d0354094501511f40e15500d83c000f80d0136100e481c000003212400f0b041550b00380da5174050700f090340740014141e204540e000340c0700740c11854210045000109a48286c90002401d4682e003402a2039400e944008210891441e013891000428026000186034200803000700302a10403050503490120341d03846817004030b8404120f03c1c0c10040b00c22103203042600300d0711024004074500d8441c100301d08074450240d030210310b030110712420743c0b41101c04008a001d18100600a641c0c200c003100302e070300074880c14504052405e1402174601c036070f11500d10b86580c5c034185900010300002001c805030003940581842b5044440220008442403030071906005180d8603103002a0260041860543c0c0201c101c0701d02128541c007000e071185601803a9025 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 993255467 1250 993254217 993254231
    0xa09090f05100f0e160c02060c1b0105040305120c0a080412110f030c040c0909061d0c04030b010303031104032f120a020112020d05090304060f030b01090306020c07032103 75
    0x2c40003ca06a0300600d0129416140880c4a41c03641c40301c89410b044050501200c01c10b01030300064620b80010320010400c0c0c00100030311a0280c2c005c22441c00c6030f18242801800c083c2035803107035551010f840e003440010260020391441004820072032134007a03650219025664036258500000c0c02c40203504121004511202114007078604400f050380f05d00da01400401050300e07418204405022644200703810300c903e180c008100c40344c044c00703090b01400d1095a800703240c140d41850104a040000c1070302e9070741b0b1300c10b21044c800642c1c001c035082e046035014076000c00c0d03989aa542141062041d41d000800320011042c0c100071541808401807440020030101124642c0f1900c00e000421a01c051840d81c150401d8504000542c02121a031400c0c011100005051a00c00f103a900221102507440d08403c0d440424208a001c1c3d00c191484010800f82c6418000315180c440040e1910080d804010324003900810700c286208001c110440c0210340044590503074240380748440c400500100d445900081c10002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 993256717 1250 993255467 993255479
    0x9030705101a060904060e0703021b0d08190e03070c03022103040603020708070204051509181519050103060b18090a081b060408031e1009020a09090f0510 68
    0x301e05007010b0044545166858640d0307041010580c0010010b65000d6541c0001013607641d20f1025807031081d0300703c0e02c006a95511454141c3c030400c1150f4a1400d080c0d0040d0300019900341e02840c0107402100508020440020009541010f0003031403076407880d54840070802401380926026804100da0098078007112509100706443c0b81d460b190001341107079500c01c0204010440c4690b0040c0440350191a215003451010b60004051b102c050b40d4492000305544981d003003c3c42d10301c0640b40c000c03002d8440030340c4602000c092540c48000d488940600c1d42d00c0e43e00000c0f5034a0b0012400e1002e0003040c00108a50f60b16458403c0c001c0c00d0954416021703461100402040165040146014280c10401821401080d0fa00c0d601e10b94007100c0c1420340d04001e001041e00c14401040000c2c0150f1080d10a25142d00d4504003000c984544851507445050840d0f00b4008a1040900310344191544c07088050f940715002001950740100a80c03080300c20b076203010441840b1aa85500250081a005080041040c0c1c1e5075 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 993257967 1250 993256717 993256721
    0x120c030a03020c15040807033b03011121060105181c020423130201140901050f0f0d0b06040311150f0409021809070503150f1305041a0112032001050903070510 70
    0x403040002080009d41c103c10300c1c018143c5014107c070b0007000030418035018900408103810010a007944051014804005101c07aa803440e03a00540a02e0054145030704d08001c50080c135150340b08103001d821f2000718145070128007a5a503103515001340c018030120042c0f02554221880401b6802c44c07150300303d0003150780c0c988484041c40c05d484d0140c0d06c00100070150054004198031010250381441320400480c1c45030820311019040c58280c51080c0c94940c4014909541581d0040703401520980081100380001141c540d18040c02940a840807600702c50301c2c03002c840e098459680325018421010030700140c0300f44650000d10b01e0a81c85a40c0112084140052100904068810748007180d0188001003c9442c04202c00e05002c130000c01c00b04c03280005001041c80f00c52071b00c0034420700035152010442400f000d0700720038441110054a08006e50714004d003030844030000c0b0f8002000c101404080c0c030b604903e660100d01c00108044002c002d039007031030074445a4961090070122001c1c0541c07680d0401c1c100c424 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 993259217 1250 993257967 993258017
    0x617060a0c0807091a090a030b1b07021003232d01030b0609070201020d021603030b1f0c0309050a0f0812030907031e0b0f0108120c030a03020c1504080703 68
    0x16468140c1801c1c1051541c41e222140340c5d0303001030f504205100a0b1601d03607546c1481c00045015060605981c241040f40b9004400c003106800d900d001d0400c038100c0141c03591202c465400380036290005024101588000c0240000e901c071540100300756080c04401d01003010240120461605040d100100d00c0c0344030101120700340300c040d104161200000300b05082411000c0e5000000b44001840d2001014610b012a00a140c80e8198007007900403507402c01d60584034806040c0c5c011948039103281a4010100c0f0f66418002c4030f4020000c1070305180b000c1500840910000d4040100625000c64456100c0468909188222680c0344a92035008940c114820202d2303000b61011405003c8403815901c64114980c1f850305118902e400302118100461a541d640e0b40c002d0300c90411040711541741101c042e01d05a811103051403140c0080240903103034100041100c501400f64100507842d5070b8000600e03800c0c42041a113581c0b00048800c100020400d0420081003110b1203604c5080c4849020545100707140c40d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 993260467 1250 993259217 993259231
    0x807240c1809050702150c090f1e041104030602160501050c120720160311120712060e150405012702010c080910172211040617060a0c08 60
    0x500c10701c00c000c1e56402c010f504c1016401115940000c0004440525400b201c0c19079910301d000c80c40400c94501030049042c0f0610485101c468200307007100c080e10140d80c2e070400c10310603559440410440d1101d0402e550040da00050219100c90540c07452048030860f4001c101c400703500c2c150024500d140001c0036102244c6030fa00b05040c13a66031745902170300c00a620303041101c0300e100c0e01c51a200c0400810844000c622004d44031401c5032501d18640115105800942d5900c40c04050807a0b0b20380c03860029000086800f841107800445a003428440014001000d98000b00e01441040c40c5030b61100c42d40d02401a44508020441c05000001401c00c07040c0a2400d403003402c26505514002d90b111704034422580f0f0081d10103520f00480c250008031159040c01c00080401e020740f080700b41000302038a03140d40c409454610340f2002042c3c01d0345c550040240030f0000f4010500806483c4003070b1281d034481d8001e09500e440e104420300c80c286609039a002c003100d50040e8981400c6940307040510800540e806103003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 993261717 1250 993260467 993260507
    0xb01120c0806040b010302070b0a180605070c03020f011e02090607020d03020703031b0809060c010b100f03050903130b0f0405060708070203010509150a020a030b13050f0907050f09040807240c 84
    0xa50510a2b8090a98064070a40c0040da81d0760301c50100325a0701c502d9004c1c003200d031a0000d0743d601740c1c81c0290806030380080444041c1d16050b00c2d40d0001c1c12000200314506107020300141e44d0103107040001c00d030380503035200a9085240582d01208140d00000c50702d084c3d81c02a141c5940b030303080c03a80c2d0501c0c1341502210018419482444481c16030305080e400351051014140000c50507040c83c01c003180408448102c881c0008e0401d116460b007854051203032540021034000034502d4002c15440d24009081d032485101d5007060700080340c1100c811580e041d64040c0000924031a62403407141000800d503040084164802e5107010040360302054001007040e43c0c5e04118064208541c0d901190703d000390050240e100c1410340313841d0055180d582d0704070102c20700110308070001a2070810703044160410300c2c002c095a8550b40041401d110380d50750000c0e12640c480c0b049804000701c2d07507036141034201801200700c014100305230303042c0c04072054120034a5a40401070014007084503d03000b14048075010200e00d02120314075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 993262967 1250 993261717 993261721
    0x1005070203033c2d1e040c050d080c030a02060a0c020c0f12030d1d1c050d050411030109050c010e1005091519090f0e01050303030a0b01120c0806040b010302070b 71
    0x30038032000c010740c005180d00042103d03c1c414110f10b840560f04004040c0d12541404c208951044400e41c1c0c40601d124080f208911403803d9030700c1070000100ca008440c0300340e0203251020704000c0000103c4540d02408001d40e40c54520500003c0c0d643e4a060b5034504506042111100f05c0600c002180019400d004141400e031038940e406000555008084824060104100012010b5a0b50245078000c402502c00d0001d409580e81416050030b54031071540c54680e18070456051031a5022040c2c85034100750031400105602d0354a040e60400e10010407054040d400d1072982d8050110129201031b8100e02a00c2d80d41404003d28200010405040d10740004180107002d040203a062941c06100c040307400d100402c4ca07141c00c6501e0742018040d0b60900b4000140311020030300c030301c1060442e080010200f160031508a9410040083d8603030100400f100c3d407080c1d4071180c0d0003c581c07282242030010f10304403600b00081c00c00b0b000000c141010440d481d41c0580e040c40030700c001070351007072089912954111118030301075 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 993264217 1250 993262967 993263071
    0x806071b030e0d050705040e100612030f0e13180201120501120f06090f08070507060e06030606090411041e08071505070602040f090603110103090506070c05100507020303 75
    0x107000058072588581c92000c1026287c41c802e010f40301d03001f03000400d40103c08090b02c078140e4040360003001034040d200d400d1800098104080b24182001070400714101e00300800480c00300442c010f0303000b407802e050907001e5a00d011420a1009070034000c1c1d98040d5080300034403e010070fa50081c0714528810752000390100100e10b4981000000a12030b550215100c0318540b06c5c000c2000c900d02c1c1c00d55103071100003066010444200003440c02419141031403206110110006001130000501081c042e04000418031b24a0b591503000321020300c010540310782c0315030300c0355140d0b40d081c40038128590340302d025010046064800090000e040707030385c0f0b40c00b4010b00030041c4a08039130540205600f110095000e100c08141d0404066100c0080d04048000107502491030804940680e1481c0405041c1f45c90030000e5030200d5404960b50f640b1507050304002e001c3e0107071031900c1d500c4c00950800c0200303240d203004103021982e540800190700403440b0002c900c0c441d01d52090201c0300c00030a031710329100e0031010844003044 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 993265467 1250 993264217 993264229
    0x603150b1c02120d02010b13060b03070509030c043e0d1d0604030309151a040c050408060c030403020633012016210803150a0806071b030e 61
    0x240702905002d440c1880000f024134001d441032594016075159201540c1d24180010f0f00c1c020181d0344042402050701d4a05201010710010307045000308100042e005032651000c000c207484071000504100404865040c0404012028482e20b64040c8110003003591a6403400300d1008141c1c0380114120324084640054030300500c0d00300040c10094144d5000842d042605100141c4a58001d8401150841442c9400e84e01c4501c0580f801441501c0c3c9144119011030125507001d4040f0180d0700020100354428040d525170283d50301007507040c4940001c11400044c0003020318069813198080700c1160700d800d422170b141c11550341c1c460341d80c8001c850007100c0204245018240201c3c410b051802c6408645100445080b480310b0580340143d00960781d114550ba80b41480400501c18580c100401c990741082128011519030b0000c0d00c03030340000c00460304d204480704c50880c803c207000b0050748400b50394030103a039100d9104407402008a01d00c0c80e40041c0034146940d40007516541550790404041e80308081001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 993266717 1250 993265467 993265519
    0x910200d0213080706090f06090e060f0109080109150e0c0303120a090f0813060305160503090115080607030b04020a0e1c0503040f090e0f0d23030106030603150b 71
    0x1c00100003880000300c00303c041c0818006041559141120305044c10104103c4410300d900c00b0702004a034500030000304191800e0540c00a50851b90240e10032400401281c404010b0b40080095500c0c0010641c1040100c0e0802e081c05041c0b60780c240300c500f442e0b0603c40e84034043e0405054041c1c0040007085002184201c001c3d6000803500c00c006561700d0507486544d840c905040d03040f41e140b48001020701c3c0b040c402041a0004001c54a0140180e16060a416643c0d440a0ba080701c1481408404500180740a40114440324078072011490181d580f0003103140d89000a48180340842d1425102d20494246402102d44100780c5031611700c9041400c005000400b80b0480c100e2841d48000200180010002d00041000703109014803422524200026502120b82e089800b8200f544001102d10392140d02007003000607020302d8103251040314840d000742c0d20340d281500d20707280f20000000000b203080c2c2d81580c480c600756401140340c04d0084d074054500500300c500b0203400303d602070445441b4011800041d13401203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 993267967 1250 993266717 993266737
    0x6140903150a090c0b0307080a110901120605030f0706110114061c02180601030e0a02100503060613120c121703090a06050103050105040210020715260910200d02 71
    0x20f66030000391280c1140304150380080346012400824060803aa000f0141a0001c0740030004202020000380d0b80e00c150f2003035080079414050071a103540b50b09820355010300018032018003502e03c40c1d0315200780709460385006e0080c1008a6907000f113040b0310000501c5075505580c50b400c83c1c505651a50030402ca90340360b08080002a03401a48a1800183c48902ca00301c007405034458650100d060500024090f18135000101d402680300910311405642c030081e400c0706a40c0b80e418016900e403261408180c0b83e10032444144903801000b5000240c400306138207000c1d200390007a41044038003900c48a02141595901001501c6031660080c0c80300600058001180c2082c40041182c2c1030f00540d41d104000d0b16000d903c2610140d542c0e40c10002541400040c429235a401440500640c4c0d0070164840010f01c1c1880b03180c810006030526191000c07070500301818200b01090380100341c4e807030941070280da00c1460f03103a145451810510480d8070780491908041040300248020707414100554401c3c4004c3d00085094 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 993269217 1250 993267967 993267971
    0x140327190b0412151805011b0c0b10030f050708060f01080c0906220b09160504060f1701141212070602180a0b04140306011a030604060905090706140903150a 69
    0x10620f0154034881d5040c0030b0320502280c0880807686c03d00608603a010040142100c485401b9154415400000d0108044d0300c40c1201c0101d442d41001c40c0da842c0c00380d8000130060400c151039501440400205401100c02d8001201c1203940c5031840802c40c031200780f1a01c400c551001640000c985849040c0641c01100900f41c03080000d0902c42400040031080c01148609556919400031800d088070030540c81016564004a41110507000401611940c0308200400c800018a00105440740707804110426942c0d003410500e503126405140701c0122904810b104004d10720384c6400680001c81c101ca20101c4600e00030341801140c3e19284040d511007055800110000e2014440c2540c880300030300050101030503801e481d10b0901c0440c4080c044c5200304144282c0c0312800401035001065203050940340390380100c07a11781e1901008113028200a8100740a414142001c1000f0360400140000440d52183d13101041a04004104581846031142441d05500100482e411702c6601d0102246c10004100300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 993270467 1250 993269217 993269243
    0x8010306022206091a040b09060c070305030304060501050117010b041710020f09030601090623040902030709151205060708071b030801090b0906030604140327190b0412 74
    0x188100c2607881e03401120105950000070711038042c4400705d005104021403a042d103843e091403072102c0d02d405002d4180e4450100041c0d902c140c131b10244500002594028100d94607401e2074581100540003d00541e0b000a1888158a0461106a202030304840030b4007086490981003605444080d1051107504d04640304900d0001d00140e290700c02480210500c2c1c0718251102008420541401c03c1a07010b01c52040c1044018401601910440c4800301414404400000004004200680000c1101030340c94015800c0003c2e000050343c10442890200e031010445c1151908501d4140034030303031480640300d0303440140003c03102c2e0301a0400360b070005241c3c00c0c45840800d010720f80c480700401d04081100014040d40040040e81000d020b40780c0f07640c00440354142a0301d800400720385d43d2400240042c0846003481140300002c0c0042c4104c90740d0000404090f10600c800f100420381c41c4c80842c05841c021209005003a54041c54a0380c01401e80d032001c00300502c0c203403900080043d080b903008019504194100f030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 993271717 1250 993270467 993270517
    0x21309211b0c0f0611100207150509010b130c0503161407030201021312050613110409081206030a050d08060a150e0f1e060c010f020703020f0c0a05010801030602 71
    0x800741490340719045a9440034100030321901d0742e5200c4d074012014800031007581e140030b440104030f280941500c0700d4010303140c6109040030441c1d2103088501c07409036440c04080c070003011810340084840400984082c40900191040e900840d41408640701c00642c0510110b0550807c00700081141001454040b03804604258100a0359104503012405070790300060140d0410040341040d00204042c1500848580c41500c03100d0325010024040e60000f24841c004c2c0c400c101024038102d82c0c480b0041c00410248009150440055120510710303807000c0100350020300107180000300d0406c031a60040c0070701445850b0003401d5071400d0024090320782c403800900000c9003180e22000d0080e0030445940d503520880040d0018460882c3e814002613000d0000c17406850760065040c00c1e40071103000d007503d08542e100807100445006102c440b900f030000600001d4080705140d4001a210310b032923304000d1742c141c072110200f08201c00d0031903c00d0740d010940c1c000040000c2000d950280081d441c265480040c6060700754 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 993272967 1250 993271717 993271757
    0x60806060906070f0503190906050708030114120f011a0402040f060f020325120c0c1206060807060c020910050a12050c09070f1103030c16080706020a03060302130921 73
    0x91b601c150465480c103140c4966908c11101401440f00e401c00c64500700305512503800e10310050090301840212040307505525210703140b0b0600690f00740b00c203070b4903100c2d0703940041406440b0400ea9940c061100002ca60399a00d0184221021111200100c1210b0303440e0450986101a400440d0401d500081c05085401007114900c6000c29020800d1140107500d2490700e40c240c1100c2250002c00c0241002e6100300194128920005440c10008403414000d49840c00c040940403541200009000e070010000e58103400040c54080c4034422500d108465a440340c0e10181220341d44203055100702e1074141040700c1a281c400844055000740166010719001d40e0200d1210101500e00c6000070310910403014003036601102481100b408900618594245890550f810b0300030388540c00b00010008103204200f200b036404482c0315550041c1d040d9260800702c2805802484a407006901480301e480c8030b80b5521800d4421841720320340c0403100c0360032041c029256082c400d1a4885143c14401000c1948003052500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 993274217 1250 993272967 993272977
    0x709050615030c0406120c0c060e071205150106140f070201110f0609011503020120070e0a090c060302090102152d040618051213050a06020f0601060806060906070f0503 74
    0x40c5648079a10b43c0f800d10010a001c46640f0307032000c1035140c00341c20720300541c0c000450800c040c9c01c60310200301a10074074100750038500c0340c0d80014040c0610351143d40c1006000300e44110b103090b100c2036031102c0781e988100549500d00068941c101d015000c0109506030758002015098040c010300d00b2448406040c8086072a107a00e01761600c00c0b59208600300a0040000d000701c00d2116503e00110403a545160700281c040107048155813114001721749000556501006180e000380191500c0c640c1c0e0b17003005810f1000403c0d0680054903108000b040c04076050f400b9000300c8001c0101a030090000480450704904901000f030400380b25003806189040710b041c0080d50312204404074108110ba18240743c170b0403600b02d41e51100390302c4078483c0d9181c0d40c0011071004107216042c1d40d25200030541e80d0002a404140c1c551b8960002e66001310440804903005a0000d01d1201e041e9018080720116600c2d404107a5290204a0300d003684010108003110715802d2240180c444540300b542070781082c41a580c1c8450541e001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 993275467 1250 993274217 993274231
    0x303131811040605030f0a1e0f140f04050c030303070e2101020406030b0a2102060307020703060c0804021206090705010f0e3601050312090d020d140d11070905061503 73
    0x1009005681004010b0540c100380f01e41d000308484003682804002e12200e002e804080786139204090322708101180c112900380d50700c0440200052400ca0703601240a04103503025103441c49990041081c0741000003c680c0118101d0316406400585a0200010303079503050030712000100310300d010b00311002007400030344003500c05524045955804503080c0702c501c01680c0e100b401c14aa41401c1d410070f444640101c103c2807501038030441d949541e9000300780d01c0d28070150b200420741c03860040400c001c140c0c81710740140103e01c00c907580c420400090801541d03414095a000105401c030030300400066020700c420000c10000ca0800d01000d00f0300700d0004a400c42c0700e6203580c500001890a00c00241000001454103c2d0100490310065041c0b9010940c0d07440c0b21028a100b14500103100b0800b56a80c440e1a504154020a02407507080241782a070b0f0030740100201c5c100103105403200c0340661401001441c9821000000400e4424584513030710028102c003911300c40d0082260030303841f200c08100300e00441c0f01f130007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 993276717 1250 993275467 993275477
    0x60806070f09030b0c0a050c0712030e09042004150f06020c100c02090402060705010e0c010801060306050603190e06040f0c0609060c0b15060a02070305070503031318110406 76
    0x381815000e400d1400058941d0100700ca00c010500003d01c0000560f030b006410102050784036090517405403603c0c410111400c02c14407070503c00150609420002c2000644203540d03000c41d011255060010380203007501c1c018521980011000d1141d06101c01ca0034081000400208410030120f04c0403c4080321500300d00e8a200080b24188002c0d5010809902d47d04c10507201c014126003681d00052a0400105000348603024110200702955116400c2c1d44407103422000800c980c51142c42c144c0d50b21016504c0e503501003203c1600004115019200d148111400680391a103980d0300d02001864a07201502d00b40d001c5da699040706100440100516489984551041a00341d807241c14440b10000035580078004200c2112000d1200d59031000c44031142c40d03030204506482d6202d1403019825286400c40c4140c0001000c142010341684c00a58281280c0c01001039445158403081450f489200f0b100420015090340c0108000100031420030a400c0a2000000116104030f003042c00300035801680404000341c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 993277967 1250 993276717 993276721
    0x40215040602070e0106090e010b03070212040602030909180c041112040308100f06050d1d01022a0c092d0a0207140d0e060d0b0607080304030f0f08010e1306060806 72
    0x484a204d00340c054a2141060044039103012420000080305025100200c000070010480c00741c020007000d4040c1c098543c4a0340c0700d94888000035a00d4010721004e03803160a00701c0109071120925408020006403050250802313000d000d041c80082e103107258070425400300403c904ca4005110030182da0295200e66035486a074140a147c4481c050040c1c1c00080d543e0668440410000d81c010302103d460300b02c33030100030070070b103003034804c00e21440f804500b0880d083d500001da4080d481e041204400c1004444013070a4071a55002334136560b994002c0304505421130380000200d03001840d200071401e404444d034029002d6030814000d441c503103541e0549481116540125000c03040010300c0348811350202a40000306800c0d0821b14006148c0e0384101601800344400081000eaa042c0c0c41d0060280c0c3c0710f020701000d941d00001c0c5402102580101c0b4140c00107502d00720602d01c60341c0725000503081c20701181c1c1c03811610717400d00301c94101d441c07405043e0607600120000303620001081802003000030003500e03000e0007580c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 993279217 1250 993277967 993277979
    0x3060510030e0c09091515030706050717130810050f091504240213030302241611010e0705211507020a05100209100c0f020904021504060207 62
    0x3020115060916080462a0000450009070010100000c84901c02c0302d03202d02003180e0a0a541e503540e101980c01c3c15080004c01080d490340070443d0075054007150003096445e0001c4500e40150017001b00b122150300c0650040041010103010b00d0300d032120242800580c1d82c0562480c15132514611890075480e181080f40c2003442070301469106001300042c101d0b00101300c05800302031b500100300412040c042001e06408845220365440d40303070076400702150f5413003050001109011040c8811001071007180b0031200044011016413044980c09007051030340b6201d0444144030300c0e20024103602027210655200045070b600340200c3c00312984e0140502282030420043c030210303880c000800243c60404550501c140000000c0c0181e0700740019074006902d4440c0e50b4100c0c00c114803c10050160711505104043d00d02d2158010110343d0300031070701e05034000c48001c8250361011450b0710140894070320000c000094201203d0303583d4028070090040750700800c412160259504031fa0800001603102c05018031030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 993280467 1250 993279217 993279229
    0x614010909020f0d08120a0e1b1905090a0e0114041505060f06160204090503030702061009090201320d060e010b070c051005070803150103231f03020d03030605 70
    0x1000a091324586403260752a21203803007500c41e07603000c8100c40c07150400003040a0555440885130341100c034282c1d560710202c010300b10714059203400046d1068038508940210300c00100154811105c000c3c1600c00c2070781e00e07071260000500c0300c060f95a065540b07403040340c0b280c2145040301601c2070f481042c520701e02c10000003503007040301c2c002000b15000d0340d455525407000c2e48c0c0e80c009031a95150310710403510240c1c0b25031000c14003900b914000181340c1c0c80007005008480341c0100f002c038030501c19280c0c41e008140c2e540b14100c040d0f900318203010340851414070891000c0f0400b01d690110403001d40303c42540d01803412420150650003400d14020940d03554a003403010610b0700d02c443c0d004140040c40036003410304548030341120208602c500792040c141a020b0300e455074002e00070b039080035811407a00c685a20700b003052951070b141000540341c00280f91080b0b05404151032044003d11880082410009540c0c682d02c0c400c0c42106803408009031480701c0000401652001419528540300380c1e0b01140040ca442d0a02076 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 993281717 1250 993280467 993280489
    0x16170106050901090e03040506071a10060c121112133c08060f060906090907060509040204031407050301052212031103041208060301090803010b07061401090902 71
    0x15906004080100355141c40340341c0d054441540e8000742904200650f01d240d4804c03540200c1c3c220f8404550703c810311402088252402c51001c1600419540d242034510318440e00c0d02810011840c1300d501e81010400190f1070311000041424900d0018942d600c0c131624203400745010402d080c0c80007070001003803006001e450b001440d141c140c941c0690858651a0030300101d20b501c00240324061a901c1d240400c100d940b400042c99143c098480d00d0400ca083d14006250440d00302c3c0c0510241c00100d011410140b6045100303603c140701030300400d410a82c08445951241c40050ba10075024000400802d042021500206520500030700900d0300c1c0c90285400c2d140003c0062202e1070006401c0303d141d076509526031020301c3d8480092050700c90070900a4006000a81c440c11078500003100b04000c010740c1005040e10300d00d01e605d580c079459580000f007500340c52084c071005006032000e00041080d00c0d0650f0240200301c2c03195002142e441c2901c0307404054084241d02c034803103007030702c6e6103500041d8101014260 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 993282967 1250 993281717 993281759
    0x7050615191a09010e0603040f06050f070518030718020315010203041805040317010909051b0a030b040218040c0609050f010c122708150421050c16 65
    0xc601e1031410b0149120044203070030300740700380c4000903080700301c3e030b104060703c209a42004100396101c4c2028200411040c4581030115009480d00c0d001c1154250407218291159407540e5032685422071400b07205a240da44a407500e0781500c40e019020400c5007040c0c1540d00e220003071100050702c0340b810302c1d210303600c1c0f07444004418150b400170002070040243c011103100341d2031119000444c541d01d42c0c0c0b504a6a071429085a072803c44048400490650055000702c2120380c05641154244001100e00d07007482055000c545900c010144420000900d0001200798443e0004000c9002060700d80904130349200211000c55600c2d40900081c000103800481c508003178082a07400b0010200b5280010707200541002001d03000d0b40091600081c00e0b44611110750f0780109660301007902c5840f0301022032100d0307498040c030200ca000c1c41030080c000c1c0e00da0b520b0b1a8031480e00030001e900104610282030b031040503c1300c00b030401c10004100d200409507040102509035001c2041d1004401d04d00f41800c06520201241c46d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 993284217 1250 993282967 993283009
    0x151412070f09020901080f221a010303090519210302013308031606020c011d0105010504110708030610020f0f07030b130302100e010b040905030703031103090601060e040207050615 79
    0x4000800e640704400d907086024002c28040c0d40c00203062040414a101050300176278007050340084101356110080c1000c81c0c0d410f50703590a0103017050401035a00003560003a00f0541703880d14a81948140102c000c100c940d07000f4000080c100380803400381941d10300c0405600002e01070008030010351900c01c0907604001d05414000d103040c4100c05503c08001042c01780084d000c107401081d4900b2400003075104240401054400141000107202c3d5140640f00912546115511b841c5140c400b107074a0a04451625a03c440c0711403542c1d83d05420404d0305020007016500314070450960f881145000c0081c14103880c070600042940ca85035140030070000000408125115060f0400e6400198002070744503010740c801c0340045007944450920900400c8000200e552007414420f50406200d0044000c1500c1c074041d6400b800301030214038a0000c00d101c01c0c1c803104280d0703110f0b50040106030320400007441d000c100140058030f400b860703441350741c50480b05551000d80810301c3c3c10104400d24000d8025080054a1428 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 993285467 1250 993284217 993284221
    0x210702120708070c080d02071a04210602040b030a2007030509150c010c05030f070c080a030203060a0e0c0c1605030c060904090c060210151412070f09020901080f 71
    0x3181034580101ca00040c52844003151042c1040003480a1802425040003161619030004000944d03840c0c0c18031402c41d81e4840068069090300b10708003103505441c0e4600c1c0910484035819030000c1003a1124030140d4443e9030034880882e500000748001d40c001c01400704045010b02100c0d00c07040420204840381c548042e002c014446c002038100e41960050001100d0340d25000381d01c245407103402e100d000c2c81341045500c1c04001c3c003c40d540050185000741d404a0a00c105582d4481080d500506445409400c048090144900e094429001540c3c41100a0b1212426699540300c85480740401d81c0c0c4507100d11004074040284030f03810042540b0b1100446042c040040c989004252100000d000c0240642e80005850701a03403107541088806940c0113542d4100d9075640c800094803117114030105141c5604007842c020b00c40304016124010703601c50f42110740c418404001002505a04040b841016005d00100090f5900c0d03102c890600501f00804050703640c504030300005000200003032000c03046078040b500b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 993286717 1250 993285467 993285493
    0x120b0901030b0105060a09171608070605030f0a060302221a0901141c0b071b1707051515041104030c050f19080705011e0e010509060f210702 62
    0x2d00d5078116072042d1400c603928070344040704603024116504002d104108066150b600c10100240030034030781000441d4181515140c10056403280f00300c0c4541c1000135014008500c504006810441c3c100710b0b41100020015507e602007014901c1c1104010b1101c20101d2a800011100340070b0480c24070f060821072003681942d90001385990406020364010410002d002d0b28103034440b0902c80d421880d8a0004007032803141850701d01d401c100221008030004d0303504032035220341ca601e10034030f2000241d0114051100f500c444805101f036400402054805114800d210419403400105990040303d02c2d10a0800c074545c004203200a0310f066200d400d5440404020403c080b90440c80d604003694400c42d14490061139040000309104504481000c41018442001a90f0b0b140020310404640c07003a00e6170203041c004400d16980c00c0b15000200e00102d170340e64204000941c802c1c4014440701c84001c190b01d05000d200500340500381c102c508480008100d0f10800d61450348100385c040c0d1b000c45244000c2c40c0c407010204c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 993287967 1250 993286717 993286733
    0x100608011e0312030f020301080105041406250903080d0b03120c0705090a0e1b040b011b021002012405040b0306071b08120c03040b0a0c09181407120b090103 69
    0x480083d0411200260840d016071080d040514a8150700034199100d586402d489030081a05540c200c1d80b4281051004001420104055119500204000701c845a40540c00303c1d142c2580c6480d2020003005100c04400200000041c11005964540028821032400203142c54003c032940e04580044050286034003c0304000b81c040c06403507094401136a20307258008886c02030200689044014043c03050701e00400d110b4001d60740c0e80440304940c203000d9020134034015900514038118890f072898420311000058140f00c1d01c0032000000a1000091a040c1d5000700a102d042d41900d920419075004002c210510b001d005081070140100c0140226041041001c6d201c0b10420014440364003c0751201024800c50070142c42c0e050740060700068540ca4068031030075155008841c2161000c1c00d200104050080c2442086050059038580c010038130304101014040003000d170000c448194a5001010a20b0b03110f003a014000c0d1840d88078113801d484501c50540980d40b00402c1c1c107005400d00801007004c560f81c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 993289217 1250 993287967 993287969
    0x90803131403010b0402040602060a0506010503150603061206391e04030804031208180d21090506060a1a0a0e040b030106030305041401051e13030b100608011e 70
    0x3100e40d030600400240102c0c1c09855640c49080e401803010800168058010030210300c550200325081141d5030f281401561640416207020702c107090103000c1c6030070301e0800c17030300644d0410401484440102e10008480d850a041244d007540711010100c0d800c0317000c0c042410440c15441051201423800308104e000c0f41000d02444454442147c00000d0320300c0c00755101d0b030449010356041034107a90b9454681c1081007425104c540c1040004403090009201c64007026100d40d00b210107080a8540800c400b90121888443c03010303940310003000b030414802034481c0c070312450451600c02d4010300b0480c9004010446246d045911038244229004c02b4a018031645100316510002241001c403001e00c040c2e808070b4020103188007020380542c0307044004424117400401070422078110082032503208107600011640c9014407000c0050f40020042071900e415440c00c06406810344203007a4082907940e98541045207401503800f20f2210900e000103115080c2e00c00402030240040e4106a80004100c030b0380506e400301c81d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 993290467 1250 993289217 993289229
    0x806030c091812030711030c0703060c3c08070207030b04032703061107030e0d02030c030304140915180a0f0c0306090b0108060d060e0a0209090d09080313 68
    0x1111000030180300c168020320001c000c20300c007110507543d02c1c01000381c07860b03106407030820100d070948640b040c80000010454100d0034040d8094004d2500d0742c3c0d169005851107203103040a1000210030071203030f40c404201d050794969a00110000c40050042a50114280e05644d1010029140c0c20048a190000b84e85000c40f9403200c07494105a645003070403507108803007905050005010440444c5540502c1138042c043e01c0c0105010080c1d04520013214a85204100303004003c1111800b440f051890301d10303032070003403240007805541c102c06044000a0035940250043c001d10280d2406411550521001e010350141010031040101c4d18039a0000702103000745100c19410b50410300001e08001b00c2c40d0400c0791140622242030084008195018024103094015080303510700d070803051002980f10b110b403035025003005400825001219121000901040503004101d07200762a42100107859827641248908014000b401e0118440c000003019031484e940005503590050200d0340e00d00540040c20811180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 993291717 1250 993290467 993290479
    0x30603020616080f0c0d08010e10210c08030319270c0302091303030e03040b160c050a0605030f070905102003120708090118060f021b031305010806030c 67
    0x30b55841c01c0001c0b072248501000e50558081410342c0d10385030014240e40290910b0f00e07011080da88403a542040181d04491910030701c0e101040810203003102c0803074001c55aa4034071040340d00d00116110540c0d01412503015a0840e440003081150004242c2440014501130a000f404031414440300c0c06605143e0340317400c40100441102e6a8200001e105400c001507a028000138400e2604a5001c040e08181c0d45007600440d040401d105128070f40401101c080d80d0107180e100f0b04100705440412176034515450308451030400d018010405903190480400200310a5a40d1907581c0b40807040c014490002034075500c01d00446180501075070b551815402c08a85580c940550b90101c0c0d8020108150341d41e20a4800a00002800113403514000058510544d2151100c0d1415211070245900700c0c3c140b4540b012540c00d420402400140254110442e15a1507035400750501601e1801400701c9980c41b05d40b41c08035800001c00180c00702070304c031034680101000d0030f041e5900c0c40c202c3d012039240d0009181440c495030b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 993292967 1250 993291717 993291757
    0xc0f03050d0207060905100f270212070b04030606080f0c040216020411090f030d0906052b0b1e01090504020c070b0d1a09010501050d0b131503120306030206 69
    0x40701a9040d10022504060140800f48140c148152950540c02440e4035203800e001c00c8441c0c4000c0c501a9481c000d440801c07428480c034151600d0303010392403c423004a0b40f080003607134410b9011004004601c0601019400199210318610740101110003d0348034081c0c3c0c0d0012300040c3c40030300010941981040041e1703405a510a414040e0b40d00100711200c000b503001d0b1405842a0000d00c2ca0000341507d4002039800f6000110441c04140e074803801d40300103100207001d0704d2040c001540300d2406402c4018a01c50340381c0c85690a01030343c92141000703038003d2000954400103160203103042c900c40070000a201c9092042c0392107a0000819041300b60150302d0045400103500e500c00070040103e00000e205907209903459040740d480401c040d0031407000c04610300300d0f02c1281c0e080345d10301180032a0403100161541482c002072485c940c40940060391002d90301006094850040345802d006003004c0e08120b9818441d16811072502a1001c01c000812a0825140800610040e2105000c4403107070f518820400c9404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 993294217 1250 993292967 993292987
    0x10e130302071e03150b0904110307211709060412050c06041d060405060d0b0a0605031f1d0a0b040813230d11040b21030405100c0f0305 60
    0xc44080d5021403014a4100f1a07085020800303070ba1a029203126035407058081340500403036170560f41070f154119403010802010600040c00700d0301c003200004010307064800340da130380c1c2c081c4008543c000c02a40d02805041c00f800d10821929098020b0070000d420f10250910510714003082d03c6c0d004902819100f4041541d01c00184901040356003039545000709078a5a46480d980d54000b020b0a010821400310401d102250046c45e041c060148541c02c06060b803074280d0403603100e000c4400805009411619928800070030241c03010b02c0091204075540124181e418400381c440812108800540c0b045185101c801c00703071500b808208030107440d03041340740350701c0da07483e5400d004809201e00b8142034441c42c040d820021b60941d40d010141900414041c116000340b15803402d2121140215400400d401c01c9401d0b0b014081c54903911100392600050302404000f0b444901c02c2004143c0304110318500e62010400700002d1800c996491840390280c81c103041c220b1026990b10402c84001036008050020100304101c1d4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 993295467 1250 993294217 993294223
    0x31128050a0c090e0d080106021f090f03020c01090609120318170109141f05070509040524010207180f0b03030703110628090501021b06071205010e130302 68
    0x64990070401d40182d4503640c1c04150003c140c46560a6400d0013030301c2c044569280100c000d141240c0e1190082c200d044050611103100050500c0e0049400d9526020b40020540c0e040d03602440301e00c20340040c000c885200c0005010104a0341c080300c10051207403410300001400d8045c0d081c10913030508208a103c0701882000307003035600507003100c0800901082017004032001504a45001360189400c001c1c1200f14101e42130321200c4010f900c0c00c40032108140300d1500084d03032380160790100d8203203401820400101e0001c0c094440640361000091444003012a07001042d80c50f01401401c00d000401c0324038945155a00c0f20501854002a4240d580503047c2e550b920301d400c6a0300521008050701d5441140d4070b80a80600c1c1c66032004126881480700080d150b1480d11444030340303904030115005140d40e08207503031000b030400d0700f80c02c030350954091114010126044030801c0c407400440300a0001807911080042405100c2040d0915090400004001004098844681091107000b400705400140e080c00e901d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 993296717 1250 993295467 993295483
    0x7090e010e1b190806070e040b0d031d040c1403130c030503030708072c06040509040c060e0103020f030609060d210801080109120513150c03112805 65
    0x80d0750042062045042d102030001e18241d0701c0454481125a0103100411180e201500a510305580540702059250340030700e52641004030700800c045420081200883ca1281c820441240840c03601d001d03a0300c100106991600817403105550030030800850810040806442003044807040780004041507200780000900316016400000031855981e580c50f0141e82c950040301c9210000791544042007280e13114809001d0101c1640c0c203031030b640d40ba5004060044800c00340d44254400710400001070f003a150b4150880c82a4000c1c82c03d81103c0f860000040d180744900c99556040610405c40c120f00c003400081500e803c04000e44002059070f8401c0c010400060181402610b6140140b005400c4d03202c1108580462100c682d42d007107001c0e41c2c3c803001c00382600c04103030004200d680040c1e200041ea0b84030301e024205008500c40d00c0c001741035584c56698414400c0070036000005281c040e103401415003044826101c0060386008251407034500404181300c10100006d00c40d5420075070080b030140501042552 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 993297967 1250 993296717 993296741
    0x609050f1810060e2d0c0c1606021e0601030b190f0f0c020c150318163b0a0f0b0603100626010501080726010e1302010207090e01 57
    0x201d00e580350f920019010008031580405007940d6800405d000d0820501340c920b510301c13184000d10325140c1c0b107030703028584c5c0040f82c541c0410700c1010041020200380c0300d0450002c043d0768001d40640b0f00761511816031304086040551465118030010070015920000036503101252051116503003421252040c041c203564640007540600f08142509100300c25030160320a4100754003250701400c0040d0a00007020316411a6501d465014000250502d00711024400103400d03045c03e03103464454041d01050741038440c1d0000c0d0350307400300140d80310920350000109407011005000611142014081044501d840041940103580d03207980f09800c0c030040580189009200c01400b03191a850310500082d0080403078071560b0001900007a54180c3c400002000c00c40d1030882441516042c3e0030f10b00191480703d0f01605020810071030002451048a14480c00202542d403494200b04551518403901d00c916005440102200708005040d80180c0e000244682128140b440c041051503521079034500401000181c0c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 993299217 1250 993297967 993297971
    0x10022e091232180d2f1c020f01020c0d0506251b020a050607030503150f010c170702040501180e03040510230a020307060609050f1810 59
    0x1c1c0390654020140d401c20303200100d1052101c81d862900c540c02407580142400522004010812410200003200400f4510190008070341610a940d044549003000d41c041088842e6031481500040a15500c0794180e441140c4501d5205150031202ca11030602040007481500013107410051a4000c0c40b0078020386000900000c0c4105e12030800311f459407412520300c1c00400c00c2c600342c001c104180c03c1c40e1440c15642c9591301c1080b01d8002d17812203c0d40d807400780c0c00c1e6403081440b031002901740e40750340c01802003d1103a9985174403130501c1801c0306000c0c4d4a500c103882c8540c00003412100c250741c2c003058a010143d0003c03025400020f40039101c2c040d074031580801a40003810400013280f61009500290507512521070104503100380a181d29403a40614000d0f02d03402101c001d401241e0038400c1181600c000491450321846801d80d421114855100c50750074030140c0c0021a80806101140c802e19004100d00002070100d8075000d91f010741c481800030220321801d20300c48060066403104100441848140105c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 993300467 1250 993299217 993299243
    0x109150f090207020913030e12010b03100605090906070f031d070902040302090a050c0306040b1c03180b040f0902070f050609010b09060d0c0e0a0902090c0910022e09 73
    0xa1031002c0d41c480c3c0b8099000b81c40820205446040300c03001071008a0b01641c0c1ca9110310426800c11401105108061199640310300165519036400d00890001d01080500052040d00c7d00042c0001c8400c020100709594100750b04100c11b0a800013004602503c40b85400a50540203440d402014007a4000543d160302c00d904000c10390345c0041d4002e01c2a030740200c502c10325551384c3e9410b900c1074840c00c80d02c08401403800c1c4086403c508081d007061b45082002400310900b9003001d06002c444251441c000c1d0700051841b107031036250141240d0010003810a10303000ca85804c2c05c248030700040c603290b8803d012115500140c02c00510a07034814403200c456200040c1c5500d814424146c1b0b0180852007481445040c11102207030103403074914107000c0a02d6210007403200940c502017622a0f2100c005007841d50071a01c44103100e0059452034043e40c880c0d00c8502075a80c4404024083c041441c0600103800d096510003800800a001d0071450f11510a84a00302c421080000682003406401d001d403005141c03010800c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 993301717 1250 993300467 993300479
    0x151c1a18040b0a15241e020d0e01090308030a09060b03010e19050c0a060216090204120201030b0a081204030b0c120411130c0e13360503041205010b01030902090109150f 74
    0xe80d100c05950386d8034078032095506100c1001c40d41c142c031190800350380000d03401048a4001c003258415014141031032100c0540e02c2e21001c699074800c451465243d60744000107820008688910f04030310714190001c0001a90301145179607140300559008090300c0c8010501003c210b070400905c0c01c13440004c1d04042c1c20341e644110180d5a4180c44242c48205024401c0c04501d00f1918800e0301c0c1210440c2e03030030007100c5090fa00150004c0030545040c40e0400c0959601044440040020f10110b00182c00c08540d100d103107040060880c0340246c00090456030030800c421103042200100d980103904640b10303500d1291303100002a807010041c0312100c1ca0505121400d80429001200c0301b600c3d03c001c0e542c0c000c00c017610081d0b440c11115128070b82c60b41a15a416249061800303c070301040103c0c1c0e07540c0c00000340d10894072854a180c00580c400445031444201da082041002e000380c0b40c003c1c2e000c2c02d0034062022258006041c06074140592039070180d4801560541200e41841d15000700038100c484c050b031603102c1c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 993302967 1250 993301717 993301769
    0x1706131103010305010c0c0f060f090501060807080c1504051e0d0f1e030f030e0a050703060c121503020f0117071e0806151c1a18040b0a15 61
    0x103c42039034154078001d0742400d041c0c0511034442c0916400450310000c4141540c455008203144603222840559507180c1c0300029200740300703d0020701441c0e0000c0041524004100f4030b81590303071500314000c40c02111070440745610f00c015502500d0702141c4400e2070050207101c0844009114001503404170a840614040c1324800e02101205409100394544080052845c5080384283e1080200001d40341c4c084455003030b1003a8050344030078510703005030340ec6407580d0303124a1315042980e0030549445903102d2203448000d400c01c00c2007080d241c441070207000403800d100e000c100c81e08583c4000703030042102c8002441503070b1142d0500c08140880b850f00c000c03541012100248050155000c001520f0042d8a00c048180d000b2001d03a0f100e141c1c0140710b0003801b0311000500b0b505812a158191220401891044210790603005d0000305d60981f50701c0c090ba1070840004c01154101c4101030100a058040500002c509220f4801e54013440c09007000c25020040550500d0003255030340003003010305001c08560000c9030a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 993304217 1250 993302967 993302969
    0x2010c08031f09090f0311070f1403010b031204060e0f120d20060c0a0c0803010e0717060904141c020109050c01140d1a1002100516170613110301 64
    0x159034840c80e0143c45684580403a944000081c0c480c020405040c00024410b548580c40003604406031402995140c1071034041c5411034000155000018a0b0202141002d114210701c40404034002e042c003083c0070003e10f1307051182c0d004bc2001c000c504800c90500340c072070040e228a200009060b2030b03d80703a402034460303840d083e160440000203840300d40301c0704510800e00900100c00400708040c01c2241c0300c8071070114580e0302c85000782d41030008a02c1c0200209401c0c07000786009041500c021071551410007001801c000d0607440f41d1000c14007000910016440f9100384550003a80072050035104105810158902000c4d1440c10480704042901107010340d6040d0491407040c0d20880c02c54500403100801910380759200b03104104810814041c40514034113940080901680309404100e26440c107102241d00c00e4404012a40036a008490b0061001028411503510003010190b408001c00c01c00300042c800e00400401ba0344985031040800d40e1380c0d441289105440a162008108103c2a914410229002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 993305467 1250 993304217 993304261
    0x3f0c07020a0b0315010816051606060e0906010909033002030a09030306081225050601171606051e040503100905060108030708120403020c030a03120b041506050702010c0803 76
    0x1110160041175401030030201d01036007c0300303940c1c40e24415909080303500c5e4010004e8200b21844190668001c00c045101c0e500161541072014007107450710000c014070708241a4081d0300340614020051000c02e9100e00340074001100081500c107031100944841c002c028084c0110070b2142e100005116001d4201d42c0807070b408600c00e807824080a545e840d030b85502d44540090b4154103110401c0240303409411007155800c800340d03003003030310f428429581c43d034501d4043d00b42c00c100c038044000410301400d070800b000b448403181c0560300156552420a0340080c450b0080311105e22001842803280d03050302204074141c802605001d002c48110001c000c01c01c00141800c080d0a81d05ca02940380041014040882140d143c5a04103074003501c0e00d440051a0001d01100800c1038086004811080c501c5540038020401d0071400382d0b6920281050b080c070908219114080b0041c401c6141c03581080c1d4400c1c050745550221406400d04d01d03181c426900050302d0302c000e0050002e00c074040010810000c502025092004168 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 993306717 1250 993305467 993305491
    0xf0708070f140c070f0512010e03040306090f082d070210140708030a0507110610030f0204060503010207051006050409050604060c0320120703020906090d14010906023f0c07020a0b03 80
    0x45d4401c4420300300c070270120f03040079a504200000d002080480e0840e180705846403000110790486601d6581450300014440b08000c0891178441c401041108106051030004071091442c3c01001e07030011b00441c43c0010b41c00706003c629000c0c1003d000410060b505c00b1034019541560320300c0c0194000303000f41411502d0f1404242c00310603208103c94001101d62042c81800c549d43c5005c1d0854817086130b030100002c1c00300d0384070b600c1b0403010425807001e00113805c680748a00002c050f80b100c600003103030aa50003070b0000e41c01503140c5000a804180002540f40d040307178101a000401d584902c5044000c0c000020920030701c00383d104c0035540641c0104004003401d111800e030103442903c0e4094118103074400c1b01d07900c5074050018800e980e900c1c0740947c8240c203010301c43c40100c409003203208101425200361000a803490b07039000c241c00021010418900100042c0620344e1180068170310071401a0b0003c10303d507481840402000510140c20398411145c089400a1542140554400e8603040c141d0044492180c494 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 993307967 1250 993306717 993306739
    0x601060906021b041e23090304032306160206101404020903160f0f0e25021203010e1f061e03090f08030f0708070f140c070f05 56
    0x140c03180d00e0510544045501500300510b8010003a8551142c525019501503612195600910520fa4000c0407144154901144c1d581e80c5840803264941d6007201200a40f00c50402c1054809001c0115003eaa5000254150700c0d4032101c1c0607035101584141000760361203030b00103024440c40c052000e1024400c06908a4805075550503071101061010b100d8020303400035407201c101c418a0720713402901d01d940d800340440300d0307403810400b0f181041070b5203070300c0940380580340013052240e451450445005041d500e0100416070421903444000e0780da0410840458072030251004500c18801d00014801c10320b41c44416889503150a206136091030150340680b0383c0d040440b1103c04110f200e800f940101e03100c40e140c0b49188450b20390861000d2441c0c0c00c0c558200b59440d11101e00041d0240025040e142c01444a95240d1410f40d9000340008400b8220a042c07200d00d108014441764040241c5030302e01c0403846c10307230804940710550342014060300e800c020080c01000c1e404114404020000da0403282c00301c5c0c510084e8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 993309217 1250 993307967 993307979
    0x606150408060115122904020903060621031809150f1005120a020a0810141003021908224115070e0607060504080904020c0a050601 58
    0x40c800d0788506195a00542c004000400090b00d03003030410441800c0c4891311040c41c5074610100e50440b4075421a40c2d0f18006009049828007007502c0110b0b105460441c54814803030002540c90380300401842c891585041c07064020307031602c034600c02006e1040003261f85428054030661541c09610512a00698500000541601c9250340b0314001d00381c00b0f0b00c01c10302c00718043c052000346154642c4008c1800804c0001c4e8619420f00c440e44d03071058a05840040e00d55100d2000240440d1001e04510344030200b107403060040c89440c920030106e45504640d031030501d4083d60403d070003900841c0c00004100c0c81c08081d211440f07410200d41e41c4a0714222009058440d02320300000e5a40a0382f48028240c920041d82120a000c000100c0e1515104403c00d0902482d10540d0740a4045400544110715508450600041244147e00300ca4111070035090040300083e0780b90200e0040d0080700c60103040760703840e0303008102803000f18400c941309540b010303009660391001031008550300c906d03d8800301e03401e01c5108000591 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 993310467 1250 993309217 993309259
    0x3070305101202040e0c10050c0f06090607110715080610050c03090f0d0c030525030f12090306230c03071715041d1903050a05070c0806090606 63
    0x76030740b1640100e901101c00d038003800000c11500c185450a40308042c608401c0d0f50310a01042084070166451580d94030603040054100075040b94001d10640c808001c0c800c1da00404100140c0c02070803071034917241c1c0d0852144414900b03c0d0f16404200350000c4c039008400495401071520b40308190594402201e00ca07030080c202e440348580c40c090300250f0002e01000a80c2e00e402110410340800060003c00c0c01c04864072854032040305035008480c00e501c450785240d040c0c2601a0f002d601005101a403044640c03443d11501c80383d480c1070780003e203440a007141c0220102e0181d10f0301c00140d50008030410200f01003500e903421080c50b54411445905803000000c22180543d011a032150000d940c0724042d264008605104011015100d400c3c2d01003145640c05590702e80d84540341e80748160030708401c4c030041b1107215242009907440c000d81503503c580e4a8240401d801c201219114841454a07603901c809a081c040e80c40d850640001ca03c5009100078800c0801d00000c01c103014100c00c0b038006000290a000d0803138 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 993311717 1250 993310467 993310469
    0xa1a0105011b080d09080408060a02071406010b16080c071509090504170703051204061b1e1404120506060a050909070504020d110a030603110d080d02070501200307030510 75
    0x116402e02001300e990820080e40284081a208000103030405854901084c14520207c40d0300041c15808910601807192403d840f00c101000c2e00302402c01035062010382002d521a11501c04008100c5005180c200304400c0210f40b0702490039810341c3c20b00f58844404240c000280254200024a2001e0103e0840d69900c2058000c40c1e00c4480ba180c4001c00300c03841340040d04861030907400d014003484100130040108584034411441024002002c07002420782e0048400c0704403045042065590b6001710b2041603140030342000c82c0c142011908502c1c034001c8160988110740080b183c11800c4113914080000001d0300c9409a0401c40360f40d6100f540f14014030480000c201c51803040e9074028002081035044c5a40249108042c0390000b117040190411030040c81d42c0034040e10400a9511742c420010302085803140b56000104a1761011000307201c0e02c4d181010300440105600860b40029164200803007540602c4070010300400c801a000007040c11510745410032910480864200700008480e83c2403121810 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 993312967 1250 993311717 993311723
    0x501060203090904022404090b03060c0742020304150b06040605070606030b0114042a03272607020604031104060504020d2003060d03110a1a0105011b 66
    0x4480e690342e84c01b000340f000d5201c0d1940100c00100003c2d8140010404024005401502c8000c07500d0541d00e0140340c51700340b0081901d00700302d07818080d0400245100d501c2e82e040d01d143d1061100031111030003245940850340785030150300c43c510310f0300310079040419009580b286000384101ca00b01904042a0410358410300b003003075440101000140202400f660103071031498000d440015503030351a9178130b10448a0003a040207031142075041e9044401d2505005c5d10141815814000035030100201480100050107a1840107054440b4a40c1c4034050074142e240d10743d2880f1190000441051381005900064001d4505250301550002214125400000c0b5460141d001c0c01e4103107450300d507803521108461410032107a40140c90380000180d40e500d034000390a140d40080b000149106000c103c040380300758018520300012509004200716580c84421048145426042000490802411460414180301c0001340000c010030003001d41445c414400b03d061302c000707807074040150280752aa4491407502c00001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 993314217 1250 993312967 993312979
    0x60603060108180109080c01050a060b09061c050c07140a020603010b0d02160506220c090216050a0c140108160f050f0708030f100605191101140901050106020309 71
    0x200d0015481000703803541c010a91590f0b401c000c00307040c1c14a400d48002031000d0711500c0000c11809440602880ba1980010b507039482000a035181c81c803510f03202e00410600502c19000416403164000c0c803041c900d06451030b4494100006c0c901240d08a415402500041e2200303030004d4000410800c001414a010940044c43ca81c01e41c0c4c60108400360a5229010b5400d40503020300c4030152001407900010111445100607090798906a0080c40301d1881c480b584400d00c8070110741540109080e00440829152007072000743c0d4510022009074131610714540024003c1c8228442d400030b020ba5035020105031100342e0404881386680714011600364105485040c003d940801081100e1401018200c0d0008624109141031840418411400707410201040c0c2d03c51400004004240d48248100c541c04041034101d1000142801b00080541c050700740786142e901202d115201410340110304206400005600a0002d50341c1e04822001e88441a41c3d4401150f007060004600c15001000b500c540c1c02000c0d2503 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 993315467 1250 993314217 993314221
    0xb0105160605060a05060c07030b150f060f0f0f0d06172d030703030518010e15070512070e010e03012310090c2006010609051311030718050306060603 66
    0x2400004010280c0f00036440148980d00080d02d45848018200d500c2c040009040751610f0360601003590003004002501c1d00030b02e00043c039403655455100030f03505c0ba4140c40b0252501c4c2c0c0780e203030300405104205641414550119105c00d441900038002c01500078821000c0c440320303039614480b074500d10940c947c020700d6802804081000c041c0d401c102211008004000c481084c0080c04180c0c11580310740300a4002948600401840104502108070b0014031200200032880d4142c0341c6a449000211009521038a9031000c100070622038410b41d450a071103603080b61a64148914042c20800412803a42e0100d0700324008100c4500d010b1141c0741070001041c1c00c6002131160703400d06919200b0000c05160b076503003e1207070109800b1024850201c142100b925200785642d82d02040054000d500701c40203025034020001403008540c0040400102e500175900c0c168105000080000546440e002e118180a404401c000b2455440305501c8482d0100d02e1600c4412625042815140e04c0c0448580e50000c0003000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 993316717 1250 993315467 993315473
    0x140601050d05070923090c040b37032304410d09090203070219051c0f03060806090a14031314040606030e060720120c010b010516 57
    0x340f540914a450255210390300d0b603620040d070300c0440d801c51801d003400c0c0f07402061a041200c501a009040f210310f03982000e142a202d98070314414540c800c8610641c01010102c076050750b10701c0302c0a0000d0000042450351118900400415042c0f812244082c00450482e960b400d07402d802602840e04030711408407a8a45050010783c0f5a6100c20340c00e08a000ec0e00c19501112020361600c15030402080070700720022440c007004019406030b8118172411441003050000f203540018401c1400184a00c00c4c00804070a410400c1c00c1910055056980d055411440c044603a40680f40c52542015a141085187d849001081d980c1c1803c4035029081c0e4031486086001c03c2c405107400030348034481821640340c00c0b42a44038a810008c0c0303500903229004061804a90303860301b4060f600c0a00f0325413804208520280c800d090707a6220140c020302c01d008026440d0702c0e0010140615092000a00c03040315121034201006009079800308446000c607501c1c00f281d1501942c46001102c41e660281c810802d6441a6a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 993317967 1250 993316717 993316721
    0x5010b09030d05030603120c070503060c1c0903121401080f010603150203041b090504020108070e0904320304170a120e04200a02150709180b030f10140601050d 70
    0x40c1101b82d01d40b0603010030700040305104004080c20400718003c5d00f00349d882c0000349450640c0c007500040e0016401c0c804a030342220000d404019507182c01d50b010074501080e09050700d04200c040c50410f121410916503800007035000d0f22140c12142840c086400d04074010740101d0884d0b44070301000b04030f4000611078411680c4150041c6401c640250b2000807002d07401850321250000b507600c02c82c507198880040009568101050592002490515a060342c4440002910200008000900b07403849055101200a04d180c0c1100410300300380072104100a084090550f02e800910407000c000210b0022090900c401103411601203501c1460085054100d610070f90b0044094104150407684d9a181c500c05c5420b8850050b4081760224150b80e40c07080b08010003410f01c0d0440700c044080824040031700c45550341c0152814111042c181d52000f6000c02010203801801e0b203588040c1c0d140c461310454a14a4002040c848080c800724401001485000c401c04001d404040312140e0200d40b0a0040703a440101d90303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 993319217 1250 993317967 993317971
    0x2070c1512020d150609060f051908070e04020313050613121407210e04150b0702030f060f10060807050d0b040f091b0f08101518020d05010b09030d0503 67
    0x54002162010080c040c0b50511046a030001740020060704080102580007540d040c500c6601c3e24115103440900401107c3c00d582481c10758007000304c031200150069219242d403a40307030740005106564904040c4400c24182c04034034001c0e2098012200810148000d114a08009a80c000400780258100d00d00642c0c441504031002e600c803090410030301e00060312039030b00e1f40990004454054003d45d44800000d01012841c1d94642c040e528200740111100a000201f03802c803149400f0403562030b260352000c6820410f4803000c00c043c0c3c0c0309a10a00110400c1a8080e80c496502061a00510340d520941143c038902c00355040804540200b04500217502c0079045034041c00350291001ca454031005a00b80f00b296041103043d11400e290305456404440310912f45801001c04144c1200d1007420904069251500c000c1c81c100f845581e0380480b0303122211000b03204010700b00103000030301c40303145200b01902940c0b0030f1400b141060300d404000b1170b0303203030f951416240c40c006c02a0007000d00d116000380940c0c0315800 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 993320467 1250 993319217 993319237
    0x180902210a050a05100c0f0806061308030c0d020d0816080406060b0d0c2304120212030d0b0a15120914030708040302030c0a05090f0408040302060c0102070c151202 72
    0x104688180842e42c104801e1512a10a000404c850741820603004110354100341c081c402c22a4424140e061144c1c4900001d8018008507129550741d000581c414a5200056005826600001c289000d0b143d0010500d01d05154054080d2018101c0181e8100c50b13050044075600410903214400c80700d0544100c1c40340e42d000344220400207255444e6200c03016641c0081402910f040e48414007064214ad00a24114882c06e420100c03080e0701940505080b0540182d00800314450300d2999070303005655034080030003064036000040e03a90f207030b14624459003c1c0041c40c0c0805c0c00307440c880310000341d204001c0c40070010a036616076034040340403111111040946003049064a01843c040b224603c480780610041c60120322443d03500e5965451441410706100300c03209024810111024200041c0d01c408120795802801013800c100e0301e603074900c0d1004d007501440d040030b900528089942c084182c0158020654980210840e4906035907541c050301e500000c035081c910000d464018200c182480e190040c203040b0f21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 993321717 1250 993320467 993320473
    0x14060607170d0207060e0c0a08070501030f142a0f0307081f0f0801060f0605091005040810092609130b0603100608070e0109060f120e030418090221 65
    0x5070382c0981800341d80114500f545c2459442c41050462101045030b1560084e00381c4440c2c1140b4501706d241c1f502c0e002140310755818180c50721215414101c89a00c500c4500480082400042c00c1110ba0000244800709102c05035151180b119a190300c00b28044c0d07003100c96141105807940d51040c40c11903070f802e8041d1061041d83c481c6c291411408440d101a0310142c038141c43c060b18070500d004030389402e41d0b01c1580b100c900003488400a02a05a02c5001c540c3c054000b1703240741c5040703140c2c80001c0315603219580c80700178180a01ea0070054401134981142810501a003c090b400d6030700c0380782c01c240c0c103d040021215144001c00001c440f60a09a032a68a039242c545400036034100050045191030340304851525030a015140300f400304d2034208580366002840c900d8100140c0c204c0d60006024443d02d070003010144600755281e24132643c0720f4010720a81e0109c881c2c09000c2c10030326541c0303150340303401500450524444910440d0a0705500340701d4000700980051012a540c984003441a203012000440e03500a40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 993322967 1250 993321717 993321727
    0xc070f0204110306040f0b0d03050901020a1202010606030c020303060d0605061311031008060103080307120b040c030e010f111c11070308222a2102041406060717 71
    0x181e164440c418a05000e050502daa07403400c2802c02044400e00d6002c0c400043c50700a0b030300000e45444c0144415540c0c50308203541da80c1040d01c01070303281401495004024500714800c0385c00781507044d00072104582c1c490710b081c04003007207049059031240401c64040d900056076407491000304d40540c1006800030400350210200c0130350000003105403148255499019100041444503440c541210074009001b610013808840d41940d80751340c110303c03000c0d00c83c3e401c00c40800712001070803091741c0c000e000d8000c004104000107420a007001c7c1c00350403460f0429145501c0d04044a014442d14094081e10200040708549000141e2000e1502c0881d503000a40d021030761600d60700c4400d030f180e40040030918001d4079500043c3c9802c03074030008003558054070803000e040400c60f03440010308840c102e69000341c07a844d2942003401000785413080c840030710740c0845001c09006c150401c20003021507159144034004c1d1414040c10b222015030ba2120072040c1d0b0704a411050400c2840b0100d04410b112007104070314514030601d09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 993324217 1250 993322967 993322969
    0x1a0d08280e0d0317060a1a071103010b01120905070509010303270503030403140a0210120e03160807050a0203060106180906080718140c0d0e0d050a0311090a03030512070302040308030c070f02 84
    0x311f030742c05083d984120300107100c20500c0300b00b4040c8102901c0c21402449640181e5000030242010500350081c155102c59401c000c100080c441d000160501802143c01e0b0760392810f0041920000d112241000c10408500034269440e5015a0301a910007800540ca4a40303183e84a83c805400043c3d02d0344c403801803106110050b60713000c05207078500300103a85070b5010301d281c00c0b0719204442c090a4a11a181d00400c400e035060340100a00d100d2003034000320000d444030b13168140305041481d4100c1c025410701521001080e1740760046c044401c05020400da551905440f41013000c110741e1a0701031900a81e01c049003c222090f0003007183c000088814801080841011260041d408410b9915140e0300c0d0001c503520540c2c0b144d074803444800d4070781040181041d002c0e02501078214030a0060040409da16010303071505120b600310481c1d040071006070070401556641d0500400a4010b9000c42d003100a4050214403043d1090003a83c041e01c0d04440744518584800c20140003680c80b05204803088840e501d118805 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 993325467 1250 993324217 993324239
    0x11060a1205010609031205040f0905060f0d030f17090c060f0c16030b132d02030a05070f0b030c0a03020306220c02010f1a0d08280e0d0317060a 63
    0xf0b1015848508619046281c0443d150145031004410000309000400c4800864000c0d502101c18580c03001070151100c001150014600c01c401c6908041c84c0700715034003019480614610700c0142e030b40e902c0c010362060940906040b041550681c5080c0e001c50718240301498080020101d007031120300d40c6813400b0b40c03540c03c8900b008100905802d00003070340e00d03041082c861009000c07035104c07a20701114a40240e1a130b9070b548a00c14003081203071007143c040000d00b1f05039618081c007016441d0014201c1d8220b00061501c45d13520750107401074207100ca0380b40d01c001822002c07080c1600e00600c00403503504d0504c0d0008508034003e420050245c0d9008a4640c2001d42d0a80b03003094907181c00e43c110102041e984400070000c0e00b51202c0c01052a04549052100b280003c6c0300f4403040b0580b041160056084034880c10710310305501480030108100245d054940103100942500d500d944103403519072a00300c422034010005554040c00c0b010700411041002035441c29044020594402001404443c0007910303941c220711 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 993326717 1250 993325467 993325469
    0x6080604050703031e080411040e07030804170708030f070c0b27090705091201090212070f140a0303030c0c050f0c0118050d08030a0b030d0e01030b0d11060a120501 72
    0x16503604402c10500c245940540100010816095040720244900e038001701221001000580710a812406035105695550031403e480030002d0210350010b134803418582d9055010744110b00664140304841001c0c440d01080e003a0845030824042d50510910307136203811855000700340440e940f901600b00801c0508400001e8a07450350b4182400300750701503660510b414103070410000c40c480d113201010010b840381d00408499207400306030b60f00190903407042c1c1014007404c40f8281c025481580110841418040080c910f02120340c02d068036034900d55290175040b0825450315480b5009a00504140f010030b021703030081803800c0120706e8040c0300c440c0c0580310275003844151407034140590800c660484640d80e1100c3c00082c02300b450741085441c00d10b0100050b80c002c580c0c22004200c4040800000e440190744d520040903890042c003030b150b480e40c0c5040b008184402038944e460210303103850b0040c080c90501e4881c507111240d06c0180020210910403c024044c0c000c11400c0c030401c001207500303020000035030140754 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 993327967 1250 993326717 993326723
    0x8120106030209090601090506192313060f080f091c021015081c020f010213050405010611060c160807110109063002160c050f030109050c040c0306080604 68
    0x40c0c40f030036010100260742002909035030420045080622030b5649820440b101c0501107004035000029124041d620580c4414031041c442100c0610694110980c0c8018801024014a9002015103030601650000e00c402003800c009080c1d4400905403019864503c1d0704525a2002c03551640d85080c0940d82030304101a1000042c1c00611110400040c98051640c0340388203801d00c1100c860900901d83d541c2d082c9007400100c5100d030a07042d001c0c0c8074000d00002d0820252140255541e03000303024462464090ba2094500882c82d20000041c441c0c85000c0000845504201030301094581480000282d0000b52010340e100400c0691400044c161a0040c0b640354424402c0308a030762000400545840200d520403024404080c0c2900f04440c0060780307140e00042c0740019103600c0b184001c4102c000340607415407512100045107038001030144402007282111806c03a5513014807526041411300f40d80b00004001e000f03a04c0070924410074030301030b048411a1461490001b8a50385d5540751a8034000e81030380e040e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 993329217 1250 993327967 993327971
    0xf0f0a181514131e14150f0a02210c0d090c050406060f1b0f020405041506152a120f0e061905070201021e07080c040e06040f0812010603 60
    0x1021074540046283e10140c2540b080c01400560344841c00224400c0f40302600012107410b00c20f0401c201180024242c4508130220382c08581d101101a5031040250754006030100351100240d034000c954000c44076909510360b00c024482440790814905650080c0c80c5016907601440300140e11078051080d881403d001d65400c480e0301d0b1a04052100700d941c00c0c0c02442c100000210203910840d00300202e42101c06415001044101240c1410000b00080410082d441803c100500c000c3c0810b014602c02c44000b001d0040203019903c20100400101d2880100d003c40d002c0071140c0b0300b21807550303030300509100c400560640c0782040f41d4a01040741000c03c00000402c2941e4100c1170100e900907480c03a4998001c2e01c00038035200261680e0140a248541000d080000020340711045901c2802803503400c1c02c40340000144440c0400b00103444070041c0c0200c0f44c0d10701c01c104a1140c503151074020b003105400c600d0082d10303964032a40c9541d031079034040c10340542e070300001003210620304102400366500a0115940c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 993330467 1250 993329217 993329231
    0x203100303090815010b0325080105211f0b03030c0303100609050303040b0a0309120206090c0603150405060a0b0d150b0c070509090a050604080c01050f0f0a1815 71
    0xc06428400b40d0340083c000f82d0300c4030303107012802000302c0034160651324107140081c1c072941c0d0060f00781a80b0303401c0301a102c068080c1d50142c070511900f024078035050321401c503409446098154205983c4943c01682401907601c504494440c84690300204980100f80890128444031010042440c1d0303441310420070ba19510010400403042d40c1c13844910060041c91804039441e0303143c040029540e0045005030400c1c40070005401d103000b4029488122010707845402c3c841350403c0e265000c2c2d00c072030084545c82c7e454010305803204610300d80b81c0b08907132003080c09500740d21100910009101c01810000e101a070000c031000c03000300e03501c240308000d09020112010042904214403048070ba0800c21030340300610501e81130100b50f081c40004100d24003504c0301900e40709825941d2207100d40c6000000c580142442c000d5100f0f01050140e000c0041150b28400d0b40213104940301c00d8100700d244101101c05036501c003104408030f03510700030300d4004541450400c40a6445442603440c3e080f45001e00e50304000d42c840d80d60305 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 993331717 1250 993330467 993330473
    0x160806011a04032402091906300b0d0b0f01050a14030a02100509060a0305040209130507030f051203090609100203010f060509030f0303010314010e07030c0902071502031003 76
    0x800e0399181a9181140c1403500d155909407004180300402c18284200c40100144c292503035041c3e0340b010030002c007000c054034004a100d01101c0c91a0040000040703024404141001411900360108907102c00003a0308160110f8001c8018200001215848400d0f640c0d0140411b100460090081c2ca6075070380e041055140404224800e80c0a5101c0c032400003404040d0303045c507600414121007030764040e12166292000d4000881d61480340d078a42030361024020410707100082d41a4000da2041d4401c0e11031082e40d46426030b04040860035540002c016501c2480e06100142008541075056449041100e078080000d003840107442e0401c940c1c80c0050b90001080154212042005d1419202c40b100210300d15418500007642e16a0711b40030b100144440042c012607541c0b4100f01c4114a02a41001d0360f840703584a01c2c20102c5010740480340c1c0c1e90356080000c150070f540400705d9200c2c1121f0740180802c0036680b40c00046006500050781c1684ca5508030000019000a00e00040d441100c04203030b0841c043c4d0443c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 993332967 1250 993331717 993331739
    0x2150a090e1b4609090b030a0f06090515040213290319060518030306090106030c02010207140309010210021305010c0c0b0406120e0f0606090916080601 67
    0x808401640001014020000000c44211095010520283c101c1a0401a101c08600d030b08001d52140c04143c0c80400305100f510208021012a01039442e50416959a880d210554500030406545a0050200e900000300340d0703000c0e408928841c070404640c00e00152600750400b400840681c440500c404c042204514108410a9469501800c204100c0b4584c030114032804003c1070526070b0605102141c030b4070300da13420407840070746062642c0a14590081031802e48080c0100352a4055105202501c40001c00004400d0701d01c1480c000d050120143c1c64103408030042c00d4800741090665600300705043c04501020f484140d41c4a0410056a4800f60b0600080c03402c21034002c4110a58410b0004000001e000c2e04034504461003481e009900c00102d0920a5803144991707c0300c81801000640000c49680040401c00315407856401049401c244074502030300c81ca10214080419049480020319a1400a21503500400014201c0c0d4042c0039211003030040b80c150750401c080c1ea80c8200010802c0010760 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 993334217 1250 993332967 993332971
    0x30c0608060a030b0c0304060e06250c0803091c05040b0d1d061e060604080c13021308071d04231c200106030302070e190903030c09080303012102150a090e 68
    0x248004020522f000780a810381c074060014031240c0181d0a5091030582740c824003c40076044e409c481c0d000d13038030300348524104e650b6030405000710b072118980412030340110700500c00c0d0340c1104c42c541c00441c58003c50304501d00040c2172240000e0081640701c10b40c45406071040000c1c2e84206150381c0301e910b103040c007038070003031610540100b019100d880c0070441806000c002103a0424140f8003520301701c0c00a02c9035075000c00a40240c00542070191a90400081d80180c0003079240c9c100d60801504441404201d658409060000c9034040c154083d190980032040c1103808142074a41a0202600e0040c3c00b9103840006003002140d100e8005a10b11a49085410707411020f80f2280f074640c0000c110745c2c0c0c55554081d4943d1a580700c1c1c1e41d005400c2a00141280c500b03000c2c41d50298040e50010411001c50345400740062048c245c040d03000a000fa000406c078a4400400c49043c0d40c102007045a000c03031545000d6441d03440304201241c01c071440b04005900c800c000d402801075103017075846816020303046c464402414840 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 993335467 1250 993334217 993334241
    0x3020312010b1908090a47070804020a051c0201031b170a0609112a030f160203011a032803050d0e07030308010816030c0608060a030b0c030406 63
    0x10400700014881c03090b140005009071313040010242e80e40764121030903d00300a0001d0030f00701000300d0103d0038000b844010803080c5900e402c500808010311a104000460001c0310103441034001001c03407105401134425a0b0f2091004000340d400c03a46603000700b984958880d1a50714001945a0364004540c3c150180b41380c01252a03455100e1050f01040c01803480440400c1c2c0e545202401000c50b40e0003103260081d201602c071115040c080f501085030320610503030015518041c40c2881d01c16550806408600800800004a0003141005595048854241c0c400e85090814000d800100c0d4016242802803000c402c0421065100c0f0106003014142010000003030400201500385201c0c585c6050040a07656054043c03a01d291030b4010714550000070301840003194101d00c00c1050000825503c0b0754864141c6004e1003d8404442c10108250405d41240c040113200d02a1980c040c0030562080c49100c4e4000c50003811100516038980f039203040e0030005d482c3c00301c02c580c000080105021041c000d10780003040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 993336717 1250 993335467 993335489
    0x9110301111b01140a23090318010f083705060102120a0807030513230f0a0507030212010b0907020106090c171b0d0e070905100315050a180302031201 66
    0x103215040500b40e85008150404d000da45402c03500100011b41d44d800c10302040004181ca09007001071013203035260801d000220f010f1455004180055104490040c64480da80d1182d007281d4417010004022480d14410340084580843d186085e6205842840850214403020000c4d09092040c002410302a54080543e56024100881071000d07600a03140c0740e2040f95898001040d031202c1c00d950740c11160045000e0b241014a071140c1c030407414102903070341d025214541110030000e942c4c101d0700d8403210b00241c00740c01c54019420810240c00c2507a85400300d00d0f43c41000155811001000451480058401e10010703035403100c0c24170840500f4414804100300a00b0148000b03c07410b200904040401803064400e80c440a0a02d0000e440010503640302107440d4000f88032040014103600ea4a0500307220b0807010341c2c08e00000c2480610844000d10030303680c000c0310318025001e5844a00002d4403002d4049a4101d6403401401c06100500c601403050398482d6003c1c550300c0e03460f1188260941c006800c402c0c0c1441c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 993337967 1250 993336717 993336731
    0x501050910030317100e1f14010c0204090609060603031e0203090f190e01060507020f090906041b180f1a1e0a0e180f01090803010909110301111b01 65
    0x181d00407450300c240b10a84c03401a0219500c45104d0004c46103035901206544400409100054a40e00542c4d44031650b284402c0c0181a43c400e80403108450380c000e2540465505d245000140c107068012488081c0079500100d0a499143d036070b04101c80c0e09500c1075000501c00c014503e00c0e4000040601e030300b4851b9100a40c14680c00500084002030350304c1050f4841e4000e450030820f400030700081b03000101801c046543c02981d440e60301421035802100e0891148144404a0205180001c0402c2c0103008800040100355120344d40c240600b10b400302c14202419905000003100201c3d414205864694844041030600068501000341c070b40301c400d408a8015221051403441d19045d5541d03034013800f0303710101d05807a032070404220722100d545c00904944070480100003a810402d21541491940d01d8111040c40e01e131030b00441d08a4946417002000320700c08100402c5840220341244001c58080c04401c501110a80c001a0860300d43c000050300c060340c0440e0000420754070703440e0f190000c008000240200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 993339217 1250 993337967 993337973
    0x903030207080a080108061522091704050f010c0503070803220501090212010513081e04090b120a0308060609040219032a05040b0c010605060c010509120c0613060f0c03050105091003 80
    0x49c12140c5110346019049034600b2444844030b800c078140007500709011808031081c118800740310368010701566004014100400c20760794452404112100c1d04003000c1c41c01c0c0480c0740d03030310f020580c4003a29010106c0c1c60000c414500c40141840c000b06644184000a4134005620500c60040c548864180306a490b1204002c04d03940c00d400c030f90300c0450b4000041c540ea0807802150040e507010f80040304880101c08940407404ca031165002c40c0842d1b90071a8903d20784400030b8400381d56440060030003400991141c0204a80d4104803001d0014034000900150504020b4181c0360401d100008030b400c002038a80322103056080c400e048040015a0740c403007c400c03800c2080c002801520503440380e042c4641f8000703420701724050294040c07000b41100919140d540d070392a01c1424043e0070141c610a0990140700c1142c51a00640740032504951034690103050583d03030b03d00d0204000251000c040c2e0308261901d1026070420f100c2e2117080c0800d0581c0e00c000401d941410180000110010047c4900c280c0c0c0410034008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 993340467 1250 993339217 993339229
    0x12060f020a020d0c061803080a050109110409110403060c1707080106170a0b090103150b01021b0103050901090819030b0303030601020c0d0309120c05010f02150a0903030207080a0801080615 83
    0x812100744c103081180b4160343c40d0801c01040f2403402c03030042c650050614400c156001e02c06500401000302c0a100a90701c0b51200000c854802e0707109854103000304801c229400c4ca85c0c1000c1181c5c240301e880c0605160341da46071501a00e15444500b00041d040c451190145201d00031059086042854134416940c109580600044c505000c9148003d04940005a075882c56801c449400c3c400501612515656403034005001c45112115140040c10159603003541c1d480050044c0602c41d036250201c5103035070038100540003414090701c080d44a54907024450042a80e500c010800c6402000d000c1013007005100c002421203007520a503a100f0f420800038080280c0c0e0002d1100800d0300c0c00c9400c44072007012031500740d98800860303010108409481000e8414001010302800455800782c032a0003282c01085022600c80c801c03007802074000d8000e1004244440819444280039900c00d0400601e003105c641c0b9415203c0e0000744e425400640c3c00001401403c00a0003003a8000909150044031130720038600140d1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 993341717 1250 993340467 993340483
    0x11030115080c0906070203160305010c20060f15090c09011205100923090102040f0803070209070f02030d06080609071712070201122f0c03041e050a12060f020a02 71
    0x2200c1c3c900801d035170301507545c140545040e0180080b0401d10140d035919010b03000e462441415000301b985a0080810702030341c524010016403003030000c0d00243c3d59018111032284c6c0c02500900c4a020081d50101c0280c40310a841ea0181c90242400354607444603000041100c0202c1c90124030301c5061000f0301c201c0c2070740248070700c007a169205808140141c0e50744000481065001d54590000003040c00c1c4600d410041d4028002d8a0f4142d0140098913203520529959104024000f50032080003000590038a1144102c400c2c40c0c01b251040c0c1c0d03d854410100c103000d50b0582d400200c0d00b5000007080c07000d90041080703540020700d411a1415450051102103644981140b0b010314072002c0001100011684103440c400c00111200c1d03004c0011b40d00740d0714010f80510300c0402c074207201d030b050322400c03800703283d11074146c511720210030004501c0c0506105107000004111031700c00d404040850f2011429548004946028080e84134181c2039030307489400c0850999000310f15801c05a48104800aa0554046860700c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 993342967 1250 993341717 993341719
    0x11d220c05032503140a150603020405010b0403030c0312062c060909031b0a0215030a0b0f100e13020705062d060f121009050c1008010509091011030115080c09 70
    0x6a01c0140c0303c00312908100e0031441c007c28035210300000440b0581e0641c40403040d20700030b0300c081103680c1c2c071003035280060721a0307020250214075100c880f000080e100b8000742d80071b44c500e40b6000c14103940e20441c0b001c44401a0300602c0807480741500c0750040e540c81c441410351040381211594018146803402c1d036140d00c54041c01013600c0d1310150f541d02584104000c60707500a035010305100e01c0c80d115490b03040e0850f001554aa040e1038202036881c4098a4011103a4a0782c1400030608000403c810000351083e40c600c0724403507042205920440b580b84100c0c406012014000d80c00303010146003800d42c011140e00424845402d428280384044000941c0c012001d034400415284066840c0c5001c0000b20161601d03424a8020f05c150401c4d040c0110300340c0c21801c2d00380c0c4100b044031180c038220000c00420070084049800000d4844c001045030b8940004926040f01032541a251900d00d6854203005403000034034050403140001004200c5000d00d0300828014049030300d002c4c2c00500340400c01c03880a1150300402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 993344217 1250 993342967 993342983
    0x80d0e240f040b0f072001120e07050301020c030712260901090c03200103110f1e07050c0924010e040e07120309050306011d220c05032503 61
    0x220900c503003180202c40c09883c040c03202c0c54507603181400c030102d5503201d00b800300e641504102104a2046050303141070200c004c141c40301d01c6182d482c1a80300c1c0090020a10500c030b036200b401400101c648007803000300440035040e0043d5680d840e190400007170104019001004000354806c4000444801241101e10005980314044060700d0300e12a00d4050111884094544849a00d0010402c0010a03044803c0d800300b02011105c1d846d091b005400300d40450112801484041040c84041c0da4040f0040c19451509404d5500861010b040140c0b6508011400c490350703804440c034035403245030100c0216440656200340340407a50904528400b541ca550203428140702006000f034071a562240c100d003400038214001c035a00d440d07480200c030f41100b10000f01500880c110000c00305013410041405410394001d200c1643d44d0841c0c0000510b02d454004105c20802c103c551802d2400e000350400b130401c0b880c0aa1803002809041104050414030b2403070780328484800c40d4210003c044c0e105203082c001c44c0c0d007203642 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 993345323 1106 993344217 993344227
    0x20d05030a1715011403040201050f040306020c0105180d0c0c15030524061c14091c03200c03040f0e070201150e06040e010e07080d0e24 60
    0x40f1a0000d1200c148000c100a0304800842d00903206160161a00d800442c8012454101c2d400071154650001441200700702c0034010203402c03030103034400c4500c1c21300d120150b141c0c1d58104a44000030300103121416410320170500322641c0209011014140c00700641840100107002c1101c0412160390150900c0310a600080c00110b09000050706151402c180100b00d0030b200980c07041080249600c4181460310b420156000354050040000200424110b01031042c174540b05d007000010426140250b08a2000d4950450407441905046440e5407010001c0b04642548981e410003c1c00490000c03000a510410192091051034540c0c000c00401810181038110b4200c82d208843d00440701c0c5000c6812032615034001408075040ca0000500c40f1215054941460070f036a00051094103c45170046c24076800002c540c4030010201d030030301c0e20000c07da01100c080c24030000340840d6005010035 = true := by decide +kernel

theorem cover : BRFrame.Cov 993165467 993345323 := by
  have h0 := BRFrame.cov_init 993165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 993165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 993165467 ≤ n) (h2 : n < 993345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
