-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5245
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:13:41.878902+00:00
-- url     : https://prove2.me/submissions/aed22c96-610f-41b4-a54f-022ac5a4be7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 943165467 ≤ n < 943345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 943166717 1250 943165467 943165493
    0xa0b18060304120207150903020603040311191703040b041403070c0b040503190507060c150504111201020a080705160b010f0f0b0405100810090501080d091e090b0d0b04 74
    0x9172083d0f082c08581101054001d510140d550b40e2a484000d041d94280030283d00040e00440c14004414407400e00e0040c00c1c40700d0b4441030601d840a4141212504100c403044c80241c0110700b5004082003807202103140b03a001030754040c4d00105036210918100d07a00614511989001401e011100a0045115003c40b0010702c00c9403022011078000180001c07a8480e000301501000b401a1f010081c02c1005c035000780000001d03070780180710382000340c26202107003003c3e141e044034110f44428074051184882e107480241100136064400c003c40c284420700501504450000d844c180a0000c040303440880e04003841705032f201c200d134419401140340d607407601208552512401100500c0c101107001184032081704054400729040103040d903844c5d005420081d03640150240c0b203516212404080031500c4001401110b0090032484010810307140c0514000302143d1a680208180c80b07103051002d8450481000d48030240e4082c240001560300720359000a001501a450040017804900d003000300340310700c0d040c81c44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 943167967 1250 943166717 943166753
    0x51e0a050411030c010c140c060c0105010e0c070b0a050c0d020c060601020615060913092103050a1418071e0314060402011209050304320f0a0b18060304 67
    0x5069182d81c0c040540340d41103501d1403400541c0c3c0c0c0ca82800850210001941d00300c1c1e000081d9080c40074924046030855100c800144420f80d11030004004c00c0d480c0154036544040d0071900c0f01c0c10310110355104c407003208000e000b540c0030a84a82c0812510071000085514001054804664511b0307404031151300c443c411288103005d40101c0d400104206031460159915000080980c3e1521030039608204001008244241141d40e41d5040000060f41d1072a1010f034030060962040c4103805206c2005080d64030007450101024102150140c2070414001c07416080b0340010106001c034080c0041c140e10b498455030002c151144c2c501c00b904c81032461484640d00741c0f4001c2008c41c0c00120f118103243d58818003900e00900261080c500d03c254403445d5404010440d2046060f40e103400d43c1e404502ca0200d81441c0010107e245c10070b035500b54010042941180340d0001d50308c0340c80c0c1800ba040018903584640c031841e030100c240000c0012400c0400c000f540d02c1404010401a12400c2030b0518904220760b81c0450f0b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 943169217 1250 943167967 943167983
    0x120c12090d09170a030503090a14030705010b0f181e0a06050a080f030f0a0c0c06050306040e06071d010309050a030c17090a1a0c0706110706090b0d051e0a0504 70
    0x8190400c18014541c3c5290504008000d60202039804499503030000705514201e0040b00c00e050005181d1001c200c615a000c40000c1d42c171a1410708040e400c4440c5005902d108802035092000d540d15840c07a40b04a04c40f001c40c50f241c0c1c03940c81e03c2d100c2801c2e4142640d00c01c50300c01c1c41003c0245001660380801c09071b84090300d0094085031a054025660b01e00d00700410070030b5109000c1c55004180e40c600610400c201442c043d101202c003030785c1d500700c80111900002c2c08500c000c4100006400d00f403041c483d9441d051001040d10b41080300c000b0b00007100100c19a048844035420785480380c0d0198012910321795110003260744080c0141801805040c0802040b64111031081c1c08410303004d200380a9418600300102901001c2c0d02d4005103070204050311703d181003c044184401c1402100901c85000241126101c003190f0400b5001d42c14140381150b040081442402c9074240301080020081d106461089100000d0580f81c1d2a58000c01440144111070016065000c014681556420060250b0712401c40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 943170467 1250 943169217 943169219
    0x2b0f03020d0504500f06010803030708150a15051c09020118230a0b0d06031202010204140f0604030203120a0806040902010c03031e06030c050909070b120c12090d09 72
    0x101840c0941800980181c0d40e01007249161076580c0503c04040f082c84804940307200c040d55605c582082d809030700104440d04040100b095440d001700da8154008940e05210000c0d80041e000181195201d0180481000d4402c5654164070700031011030720300c082c0304624000300c05002007a810250400c04070403800141c0158181007050f44103161072060740d0510007480e0510b10a49550716911100701001035210703100d14070016141001c2c0d002440c950320b42c7c90011803054218244200702000c0100801c046a1042204200e01502c65a201002c00000c440c6442c0131039031200091b00c10b010700c0d00060b505000e404100c550300800304004006c1450103455100213596202e00b0003040794250755011340421035412445000034400c1c0e00140b078142241400900000c19840b5001c11030b40d554000315426901200c05103c50710b4081c0e51a85e106c83c116004080603030400c119510503020320140c05640d200b0790004654042c0811080e1541485108040c030325030312303000c22132999820036004440040b03203403240 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 943171717 1250 943170467 943170533
    0x50303011e0810020a0c063201060e0409110424080610030636020310111e07150207060b1f0c060608060f04052b0f03020d0504 56
    0x140200b20b070740d0b86000e00300404060078404080e601c0402060100094440c0603000a0411301c0380c000524241211a42c400c20b0745440c00c040c05003a10b101981c4550f65000400240c0c1d40480191380e8040265004070340590a807400302c60702d150704111a41e100d03041c1000101c12002004500c074040c800c054145203403d03922100070780c50307000c190340c001001d4400c0000ce0021840c1504040d0b40303080c0f108141c004012072042d8800540c6011702410351b08942d09000a410741c82d0400002e003054464000820040c800c880385010b41c2d2090450869500c2c17241041400d410340440255aa0383ea040219440343d08a5681594025031022104a82841c9008881c0b845818020781176140c10003042c2152030802e000807030a54180f84200300880b8226210080411049418400d650151007403644180e1142443e01c2c00c039003008803940903101a080c82c060901c61019008103201c03480111030411010f08110401c0840c007a2240c0040d42011600700001d200800c648188108840c01784409024254101d8071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 943172967 1250 943171717 943171769
    0x406080c0a06031802062104081801090f060e01090b0a0504180213050103020309070803041701050f0c0f0d1814060c09090103020f04060e070e040b0f0603280905030301 74
    0x4044c601c15584600201e20041c10190018041d034510b04160a00300210105040d00280003203c049a42c454042469540201e104c4c580c00e881550908010b9012820090784a8418215200307a40800540b800d00b58016402030482001800120040d50754035007880901a11a41c020b01c16002c00a45a60320a42c41d00b0b2144280c88041b043c4ca201c00076141d00c0e000044000c2d40018160742090b0054034000185401c0400061000b840c524020b0200165059441800c4401c014140c00030394645008106c0b446803440d0841d40303025080a116910f80c5074152040004000d2030035152a404950035070001800f8000f0f1030511090004001c4030007035500c260b0518481d0049001c0950441d000c0c6006000502c2c1c8483e180400c81d0010f0f20004509a4400c81170310381100c26a00800401d01c0c00e12000c00d1810207004001503158107032074400032009010007146461200410b90340c0d400320000c0c0302d01c01c14040c041c081002c01c4003080080c070060340241007103030700e84c0d10a20a0940504025451004c004005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 943174217 1250 943172967 943172981
    0xf030e060601030f0605030109030c1401020304030c1205040e010815180a031b02030610180911090402031618050f040305073f0e041401091107020406080c0a0603 71
    0x840050300e090348428005402400d0484003070b603189500d4035800709868400348100d00310f5600070390f5034006294880c14902d41d8500d5200180b50141d0040040001203500304640c01c482c0c0b64060403030340c405249280c00700c0b014000c40c4c20034054001540d000081001c1d0002d1550038001500c6502c54a94881405980982804000d00d0480380c001c0c000c000c0202c0d0050300c1c2e9000107440b0240f0320304680c0e516400030f410302004940040c0000c0301c410007400280200c1c1c1904c450709298070f42c200604080c039240d02a104003000542481641110000f40454070207209100e107003803a090201192988801000d40f404c04140e507417100e80740c50000013581040b448201103000e541c040e110302d4074080041c5c6a0b0080305454204040c4684100400507a0441e80d904420408240c1400b041424020b5540001d041e1030554940c688524180710799014540ca0a0150740c1c1140c020400005580031900c641b40792500906101952040c50440d00055040000c01c04413422042101d91350000c0b0b40340d002c260212164 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 943175467 1250 943174217 943174241
    0x15050d14070e040504031b06110c030a120e15060612010308031906050901292a0102032401030e19050105011d0403120b041b020714130c18030609030f03 67
    0x281e110b0245401c80050003d0000310700802000c1040e400811849c000d661003040c0185155000086c001c490940c080d2a00320303203041c1410144043c20305d04025035600d02000c00c2c03100e90541100c0c0410550f50300c1d0381c219504107084603001020b541c0d42c0c1c00c0100c0c0942085812141d01030740100d624101080510442c000d40d94020a120036590030000b04003003400f4104d5601080d00d9041d41c58034070340103010300902141c807025409070308098446007200d09a0010400d0203071448e801842445071030300d89008982072034210916083c0384500c01c040128042c000d000d102c01114041c07401c0d40000d50100310301d5215020f005600030320150342c0c4e5842c541d4241c1100d40404c0000702000d4003040010b4031030301e05d810b1481200c10000c184032034100009011110300d41054109020300d4440e07100d0301a0113029010040100700c22484041035070310080b500401000341d030b410f20255201c040ca291980140e9a0000001c40540c03812a0743c3e07100d290100042c420400103a000c9040c5c06c200103d000c0c840c0c0507000c0d015030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 943176717 1250 943175467 943175477
    0x30a0302070b030604060f08030717270102122809080a0f03170c0705010606050c03090607080f070b0907090c091e0b0307030b0910050a15050d14070e04050403 70
    0x480c00c18005910f40010f00403691060f03c4e42c3d00041c0d05048510004040d0502c40c02665403901d8074034058003540f80b04000f80d0303a410014480c0e840c0510b03411100050014601d10440d5500c07500400403402c01145040c0341002d21008161780c0c980700da040600d80840000d00c0604034680c00300c80d1050f6020341c81481100c60380c0d40b00d80700c4080011b0380382098802c0103100742000c0301d0211200303800c000060006ca0340380c0306000e0042620f200b1b106090081c4002494607003007144c43d100300201c01079141c2c41088403403401001c000071501c08010100c4100ca034030118013900c00381ca070071051914551488007540e2300c4040c0e110754080800d00004c0c2d4400d20784a88d40342e40311078409234903111540080b40a00c04c40155100d0f058140003440b07a40320f200071485007401d07540c00981d034480c10081000041c80640340451480c0303a075605200e640c90f601020400e4503e081d4000398803500c0e0a608849500c11200144540390a090920080105045903540948500c1e00da03020245141da007808100d41d0304a5000c1d00040c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 943177967 1250 943176717 943176719
    0x120e0313031709031b012709020c0c0405010f0501020d03020913050601050c0d080a0e061e180304030b070905060306090f19060f0e010f080c0105210906060f030a030207 74
    0x2106800381c403012190b1051040c3c1001d103004000b03810310590ba6a110111108003540c80820360380b080703032065200050340349600709010003150140c0a915034064404100e5002617014a4000b040110501c2da400081c0b01703004541c0c50350903125481c85030b442107a0251286000f000d0006009000ba1001ca01c07025000c0621811100191005401b01400d401c1c1802010003540d907024a00344051800010380342c03200c0d01c0307a04000403107000302e03190b100702101140c00c09003e00078440307400d5601520700c200c1d00c0d01004045d15025082040302d000c401c880d80a520001a0000801107c00c45092249610b07455091540d9034a0f81802410b100454550b9800380c0050001050360640e103002c036800c0036848000d0841c3d07072100000d100407140b16401c0f50311012061402001803004424401e805010b040b00f0b10701e0100d24020710325999007034152030395040c0716002c20700513038464080d41404012011190284280c0c20240040d9484441c1502c03007501544240c01440d59508001503004136603a4903900902143e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 943179217 1250 943177967 943177973
    0x30e03030f0402210a0b010524030f10050603040b1005060406050a0f140c030d05010815130828030509162102040e030a0305090c0f06030a0e010c120e031303 69
    0x2800021006180c200101d4003c14040d80d0100681c1203400d1050001b03c009506040800128007210441e071180481d04211815003401c071b0030b050707a4010f0b65414142c461a1104c00c950405480715410190708108044100002d1250307407600c40380680b01e1003420401e201c0e2514240116445503000d500302040f403c10488210034400c2e004103ca82801d8a8004c203040501e520700c1c0320541c041c80110189a10210345e100d81010b051080c1401000142d0040c081381d40e0411000c1c807002c1d0000c18822240181410a80502002d18100c0d006840010020351903102c607280e007001201350b80000c28000a160400248892000044d00340d030101c2140a000c07801c5161461421003080d5598961802001850480300141c555003d02c3c010004008003954503141a00d01c0102114001041c1c480507501250200075203440d80107280c1008141078901030768a80d90500d40b84043c2c016002aa02030b58609000002072541c094000302500d20413401c1403116401c2c40d900305640e80100e810348410900056010000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 943180467 1250 943179217 943179229
    0x90302060a1106010602011409031e030901091203050f070f1e0908070b070317010b040611010e0a0506010503070504060b03060d0f0609050c1206100302130e070b0a030e03030f0402 79
    0x12664407850b016a610b180b80506900301002a40204c0142c1e4640c403603007807030b01803000c0203a03070010545004500f80300c046590207444800b190742e240240c0d00c0000201d081c0d040c01b034004201ca103400400100000e454000d004006150466020200c61078210104941034441e549148002c4010344d01c20480a20300700084803000b040c0168440ad0142d809000a00c8803002d1000c0130080c011041e0b0f160303d17400f02d800e01500c0600011011400c0280031130040c0000c1811400390f40a550705803a11100c200c4480d900c80b8010855003140305068803804200c2070400c040040e40a040c0c40c000d905880d45159514140010788185018201104900341b00041490a05202a0710841c0c014441902214203c1d15450211012844141c030550407006250103541400421034042002600040201d45000c005000050900b400000d110b203460348002c2c14641156084007892525a10a03255840e035180c02d110159880307001d20402003420941200041c0c1c0d8084180d034030980f00907103d24096581c903420400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 943181717 1250 943180467 943180477
    0x3010e0c01180f030507080c01020f0316020d0b13021302070803010306150f0b09030105010b04080c0d020a050a0f0302030d0e210109080a02010c02101811030111160c0f0609030206 79
    0x542c40000b50001400744801191000440c0520050b1628504141606081a80d078822480c1958442807851540741400001c581c410488410035070880c101c2c5c3d10015925071601d50010b040e030000001803148481d00c01e045039408030b108030341540400d642000c1800590141c0d00000e0326031030090004001007055500501d10700e07070720010715618594540210880482d040d0b00250010b000204d44400541424407071180500400c005850a0514110307005903202e1070810341500404149649200315140c0721900006400001c083c884519120108504055041c0c23000340d119228140800910502a60783c852581002030199010b1508844190441c1c0314407003010311040d981c3e95a1400801c41c80000741000308100d5001080320b40302008020300e00780c95481c03101402132508201003660a13181607007414213a840f5407200d11611050307002a0050454080c010b44141d40012242c4c10102c4c2c0003000800103201d05062070b0216118202d18250740140e0103064041510b20354280098504900070740 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 943182967 1250 943181717 943181747
    0x90f0b03090703020306070c061a0a03080d0b03030a050a12090b07080415060f0302011206060203090103090218011409011505090609060705012c030f0a0c031b081803010e0c01 77
    0x2002c55540c0d502103481d190003200d014000510f40301c201c8041103214020f600480d110004482001c00741680000e464070341d030748001088c0e010000307541501c0c04175503000300328594070040039a07484499494019125511801c06000020700f05140b5800d00381041c8101500c25802c550500c6060b640c9400c10303110502e015100382c0d483c4e22801003800d004d81c0980100c1001c0c04c2c2490811040500d0761001406552000380100b00b0a030610300144821a030010a03204494002d1070003113400b501a0020540c0c114088104c070b0b00312215000041508e120a142c0c406814200ba210022186c0e40c0f4085407540d50300c2c060380b07100060010071010f4124a80200542854980201014941066542c0741c1d8210740386810007260341c102d85036501c000540154810310031010039002940c6002801300d00c4114034410303101c40000703000300d1200003400c0c18400c60b84040280c12115100c480c00d012802c11401a400c01d40c0171030380300d240f6206500c2c4079003010700803600c0042e10b07000180b0a0208030b030015103900e00b50820310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 943184217 1250 943182967 943182973
    0x1506020718052a0d0e072c0f100e01080f160e07080a0b06030a050105011209262520091b0d0f2a0c15320106090f0b0309 53
    0xa6025002031141740f88100c007100052801c02d18140403081d07642070342c400040c00c3c840400305a08901c003007050915400310524404466540d5040da1a80c0c45125a40100e000d02e0085c6002040c804d00001d022203008445e0f004072105481507084101c01100785000b01c40714840e01c0c6001c01e600d140900b103166000902c110003c61344246900108950303400844008100744c0d200c000404c21541c00503d10125601f500505014010050b100c2e01c1075120445d12601d00500d00c9807110808168201c2520401e0808120b5441410303680142c4020076081010700390b6440d10302ea103503c000c0071080140d060703545001403c065100d5481e103175101c140010415a282e1442002c201c4503240c44150f1003440c0100000c404005030034500080001a081c0b04009090f00d201c004c2c00f01e4510807500048005409988088130041d4842e90130340071000f0b0110060544a00b5480c003074070140044071100600981c0c11002c4e150b4810b40c0e601c500c02c65500305144241c4590321400001408041c0502c4003e40e4419010011 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 943185467 1250 943184217 943184227
    0xc0304170705010c150b060a0201020d240b030414160f080102040e070c0302150a14010e0f061c0209040c1d070e010c030201020f03070309140c180a1506020718052a 72
    0x425042e508c03046480e40141d500003203101c013200003031240c406005201603a207100280c4817003898484224a0050140f00d907804000a41008280790b440501420038405460083c50100b2000d0100d500c0c0e07019144580001c10030204100c1d01c14801e550031104038009500707107522108030680f050000502c1c260118040c1090040700d140989017603d0048429880003d24004d01c0e0440701081700701a00715550407020101404100d502444034507410840c1103034101c489800041c0c1c01c80081601d0040203420000781000c00084c0084040c01808407041040c1525560680301c211040032041200c20b10041222800402c100303520441030083c510b40300340001494092100840000c5420485039100002c0e202d1020004000c2400001780d070b5485403900400c1703c101100c0c000395160191840e40841600203100294000209400c04001d514520b1095605240c681d50000c0d2500760758050303180c07041000903c43c602d00207184a03052040341200600301c070000c2800d00d1a078280d615503030b8001102c075080c84 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 943186717 1250 943185467 943185469
    0x5010f020c0909071a07080a18090c0503071409010c2306010e01050307050a180f090f05060405010c0e0f0909010b191d070c02040b12030c0304170705010c150b 70
    0x1004500400c3c4190040603554941a40a244d1901250003111280e00c10b01c00c001c001075801064484100c080d090240091083c640c041522500076404540b4850900c101da030384003500300300114041c0d00c541c0d8030450045a1046a5203040c420b0840d05400100141c0c0504081a4402d04904c1050f401062050209601c60308543c5085401c2c2c114110301074070280100322624081050328010070064401c00606480c2185544100f42c002c143c10f0006500d0b0b64a0401c0200c00760f00040040d54030a07180c4440e21041c0c200580c2d144400c0310115401d40c03074552460b051034000d1684080300c401c0240541c40250050044c40001c18000c2c11102c2d1640d2111881c030099524030100c0441c040c80350103007901302e504c0e0001503030300703488620300141c2110400703000c1c050741030740c0012150314064040e54042412810b05002c01e09081d498600000207000102c1c549000e4280440140202c0350800a0704401c800c00e4008039868a2007880340501103950a500c0c140060520008095403a0154074000b070510301c114 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 943187967 1250 943186717 943186729
    0x903050d021218010c0f0f0311070f0b100807170712031e054009020405090a020a0806091003051504030807020604031b0816050601030209011e05010f020c 68
    0x101c0400d840b20910340801200d00c40f2103150302c0001100300d001340a94100404042d00c8140503c1c159400c00500694002040f80030b0f4100c4c80c0c9108c03c1e04d001550b100d18070f080c4605c1141460500300c0b8030041f401d000c0f940b05030394580c5540a4036004030140150301e140c807680c9689000e100c4404491401104c00c0007801c0c0e06050355071501140251200d0820011800c1e001c2d02e0503000c1a9485c5c01d001c402d03c4011448a1900b400908103070490322041c6500282c4c403070003a0190740381584245c0b1070403814000308043c4038030380207001100e2003640c00802e5611054101001e0780105d00240d0000307080a80080c1c0c40385051100c0703035040748040001c60b40403074403615050700b02410b80c514a11085140018482050b80c01010715603c88001c1c4050249130425540041036074510007140300050110003601018454150104c541d1192043c0042c05288028640340381c0703441003480141e10440301c10000245649030485418074003040d15004043c514144030040d18120100f544075011407280320341070809a2605 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 943189217 1250 943187967 943187977
    0x60d03210c120203090601120311010509010e070e010815040c15030213062303150d060f05010b070c150e0306071d01050702150c031608070b0601050c100903050d02 72
    0x3804041008240c0c100c015041510342546070200c1403041042000c1d0f1035002c40c2172070645070703003800300f07184910340b030904460290400d0b6215580303500e000244043d680e4158028103640c24040e00781d4130200c0d0741c0d200070a000c4909210b0141d5135080403240d2031101403e00384145e1710601c11522080020f44549800b00d038072a00c480d00341c020030340c00074a401c80c20300551003100007008113152141403000002051030143c0818040000d0410001c0080742c0861940c1d4414490444041c00380e00514490f400e110014020840812002e10306d00700000c03d01d494501e040f00c518a41100a5941180c81d04448101394580000c442040102940d0f0004150781c090211a00404696a0348112000e02620348030b034100b8101c2102c0d0600208110a80c016101e242c04102c40c6107a0212440e10303140c06c01485402d51086050300460f1002c0d0101c074904011503080070f049e506024100c150194ac0c0d456005507a280b040141d0009035520042003007070310902603004070840341d100745002c5082941031803001040c0c0e002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 943190467 1250 943189217 943189277
    0xa0b0d0c09090c150203192c1e01080c07060b04180507050609010c060b0411030403051b03090a050409111c02030f0a020d0b1e01260705030303060d03 66
    0x1901804818003405881c0c43c809000243e0f200f1010040d0100040e41d2849641008500806644c20307481001e070245c2e401031400c071140d842c500b01c0615401c175a425a04000c10125214648107568000340c40c90094000300d4488041e11014010303242d806800203141c0014204403170494a40001c0480b680359402000c140001070f80401c81d40c000700d403414508000c49600040d0145c0e800303102c60000c0d607074801070203034a142c0c000e500041d1141c40000450084d10a01e14102d180d5040041070200b01a40800101041820007000c000304001442d4060b44a21035000328076400180c88078203001d03d1515912a0403100e205046407802c14414001048244201346070000848650310b0380002581018411000c080701b0010251045d80002d0340010740c40c4d90010000b80c014807200000410b0750b00040b204003041c46c1141c0440340c2c0d540e074440d20040d50324000c0b820b110800320f44080300382c542c1c0701c00640d20056a02c014080c60071a03458109002190b54810b41c2035081062030350b2044901407805149100c0907078 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 943191717 1250 943190467 943190471
    0x33705011e053405223803010b030c0d09110a0902131715040f02100804032c040f200c1b1206090c0906180a0b0d0c09 52
    0x29214840000d1a01000e91207030b0b03201944101c1000c02103190a420034100c050341005900e17031145814810304896200c2c0801099060780c5d90108264102072092074549400d01c081c219241d0030265a003041e109902000d68071110107100601401040c00d01440c2c0c04a00301029031305122980020742d054850382d8200fa964800d40e044d45880b81c0c14001c40610181003c00780135413030311605900f01d0000810030701c01d9500114001c241040102d00a002100d201d0b2809503a400344c0c1d083ca130908140701d10100358102e11414948525910b040e0068901920854060b00ced4000e40700f051010f10040c403040c24404c000d1710a0940c0d03c40415544a105e008540c9480200010307420036541ca40e0a030f5510101c0304e01250520500c052002d4010004180d45600c41c0c50741c844810503644804600c031101030380a96501c1e03005810822507030100010710092030842c125040b500c03e840306418010101101507040d2110405480001c48070b110a412211542d1030140080300c0c55900c42e110070b41c9000c0150000c0c3c0041c0c0e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 943192967 1250 943191717 943191721
    0xc0a17091c031214060d030e0a170d030501080303060904030905030a0c080609030c0706050a030216061b110a0f020312190807050a21110409020405033705011e05 71
    0x60340002c01050340448103d080040300d940240a860034000100107601c0b4040320310500040501c160011180c0e83c0000d88080d02198540d102074107921803000c1800308500c035080164101c10f210340103007412a4480000340d49076848000c180704061100510a800b803000f0b0b81000a07103600d040090a101c00d0090f031201c0c600d1410043c007541402e1003e010016540d2041c0250a03034214085581d100310340341c50400b955a080840015006030168040300c50b0304600c01d160400911401d50856044009064002d0201c5040100240c5520040c654841000e40c401100e010004030007160600384940010700301c511200b01c000762a40103a115058800326962107000065500b07801c01c2c1200d4000c4500d0601c0c1e8103103074030642c00405542640481e29a9075808070183c090351280b65000000705d0b4500c03a150342d562a150101040030b54040e10802d0b00038441c0c01c10b6200418050a14040c03201ca1511450051003002440c820790f280094909603955540c0300f2801358642c1d02e0981000944040c040045454 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 943194217 1250 943192967 943192973
    0x110f0a0206060a0b04061809050117010f09080f0a0c020402030702010b1c0503030c183a08070f080c251d0105010305070c0b010e01030204110c0a17091c 67
    0x100c107002e0119401840109020702c05203002106071803c1d00c1c4503180181d01d6001c600b007a40c0b40034040c4c0c0e0125020030700e403500205901504010190028841000a008488080400a0440d50881005800000d00303104100b040d03c1e8020007016800000c0c50010381c0e204082d000202240e000f50f44140150303668101003849401c0405461004089100c1c16042c0341c0c1484d103d0513240d02c801401c501362800000f40d034003404c103402c0041c038040e008090000902e880310315008143c03440c030f0001c140c1015602e1013018a0f002c40c0c241d00c42c000440d4080407040c1014081e54030701940303c0f0304000407110411705005414040c6010003824038204041c00c01c5250030b410300810265603c02d250401c4801c0c00d00c00c503140540342c40751580c640c1140e000f882c0c000750960361b80204840306524800b00922441195000050444050040714140c1c4d000300c07400c0068000d200c0b8030880f03910403070300580d41903044071481c0c0022602c00304007031065441c4c485080d403400d00d060000841d07040c0b840c24070020000c1680722241c14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 943195467 1250 943194217 943194223
    0x130902160209160e0607021c0605070216050f090c120c0301030209061f0c080c0703060209040b061e090105120a0e100216171326031602060904110f0a02 67
    0x20303a5a5610f03031642d58a51004040c40a04400207000c1c0800081038011910b5040c942c8020040d107004040b080c0e0700d42c5c58580041c0005580100062040e18172115154658442d0b050454a00424003810300003944280152080010407481c90030f08141b0240c0e8001e00c116000074426000d214035581e40391305600c10450b0040c80035103003a006207507401000d1030341c00301080c1c0e000500c40f050920040d8400c5601d4400c1da640300d4124050440e014440300001004907070340150605d16030468003401030300000760034015240600c1052005030240c40c18100340900c1504020044d040040c503155250034105410705041c1c610645c3c04d44044e60b51801b10090b4004148000351003141020410b61408201d0101c1c103034980b50303610028015503c0340200b0042c0c40c810348102d0700b40c11141d0701191203866960300f9544902c0840d00c411882d41401c1c4a0841d0107110101c1103504120b40314035035150003180b91f003d101198100e200c4880d0030a545003507040c4103192a40103404012a442650369690400e000000d017 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 943196717 1250 943195467 943195471
    0x908091c210c0209090c13022109030415020703022706040905060a0c0e090907080f061006050306040e0105090c0114030628030f0b0412050a0207030206130902160209 73
    0x107071160404050a02440e4003403010080c0700d4048485100355201d160780c040c14110f8820b0402d510110901c0d150745203a200c0d8000c0e0400c003110007512031a500c040c0d41030042800c012030f0b40c8c41581d0000c000a000003040c03001940c87c2440c2c0c40c41140c203035a460358040303840c040010011410503c1c03088000d070000101100981d1b4800000d507400d0080300c1c034035a942d940d122000b03003026060f2a19644940c4100b84101740c0440c0c4444001d05040050078030400e5036403110b8190042034030170701601401014202001801170300130032400c40d1128105141c100215001d8101900070b540c09a1034000407501c820090155902880904000e8030440c1448400540031030803609401080c41400d00c1000042e55841140e410001e20500000d0031070040707011010851211a00f000b805100c075207083c60140186280b0340c40c401d501c00c0501c52a01a4014004c0d00c4034016040d9940c0164080d25042c001820308402a1035078a003400c0e0720000c056240d4010100340d8205922004041101c16241c1c4152310b07017141500c0e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 943197967 1250 943196717 943196753
    0x905070f330c11061e030412080f0604090809060705010f150302030a0b130c090f14040b130c080d0206150607081204020a26101e0908091c 61
    0x2021505150724050400d520145020345900d807924030140c0a52a484222034000c040000100d031454035007082410309030015541501c04c8401c3c1c2d0300a0300014041d015041c000c041d2403041d00d4aa5407404c0400c0040c16002e001141c022400b0300c0f90003401d0302d0b484082d00009101d08008a1085003100620044070b0100c00c0b06d00580706640b404001584000c240c1c81280741d003011503031500e40e03511210408101e40a0b18020000d8500b41000100030b00250b02c107905041001d801880b02d04500c014841080b102502e01900d13100c0890081040c1c055a422140030040c45840690902d40e507945075a070915050107a880c01681110041224a200b540040c003c405400c658090800e04030751a0f0600a016240484000b0041c035000f050a55071010350b050020000d5107a8200403104021680a0f40d9914441445091240122400750320426020b00014001c0c240350380ea00300881c001c0c40ca005004024010313038100d00f04005600c619100c0920515108207480b102c500d0209442c1303400c0710005004e000813 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 943199217 1250 943197967 943198049
    0x80a020c10080601200f070f060201050a1512021f020c03070506390a0602070b13021e0103091407030203060c19030b120a240605060901030905070f 65
    0x80d0507a0440340c000600603a04c045e4540c130240c050380307103440c05000340c007110b00034880d038140040d403074410101c0081950307050f500900c181c0c0c0782c105600c0281d801c50130313500c800c3c400c041d54148240d22020030717808100360000345407c00c20741440c0c0300d1820018498250100603000340302e01c28000d0400b049124010b20060b0303111858003a0358042080541f20342c8055410070641009242c1071004c54502d000b80e2900414251a01d000032860914003c0d440030000300d40300141c000004030040d14043d40008500d40280c004801503000f4940e12002c43c40403400641031640e03c8031b4400115294415070400d6101010003060082e0441c010140381c00c00092880c0300ea040c0030400952501010307542501604118180498529a40000580ca2890980791141d15108603070101e42408281d00c0da850300d0070700035400021001051540b0400b0b507a40c50003072503000300040020000715442a03101454841c0500b0a03280300030703192492080c00103620346c00800380040071181c102c2e01c145182410782c1404209100307 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 943200467 1250 943199217 943199221
    0xd0c08070e15040509160e01090c110604060f06080f03040314030309190807150504060e010c02060f0a0e06160f1d040f020f0403080408060901020918070309080a020c1008 75
    0x34810141c0d542d031002602850711500803403101c2808011a5903a140c450454000c1d0b00d880d80b26103144100c003480b440b80b0080c1003d02c0b41400701c2c01150381540301c40668015165541d11502c1d02000741c5040418007070348a5135680000b4800b401403010b41400d80201d0301540d81c483c5582801c2c0c3c1003a01d20745480d070142d0810400d0000c5410005480c804100c01c44406540c00c0c07915060508090051401c0503042e0001c940700341500b0a0300e54807807485503100e1b0908010444401c01050300701d81c141d160300710141c0e204401142d1503020301c2101e07070792207240c0140100302d810141c0c0302c0b2400d2040c07d4460059025041e400346520913004140e0014251441ca07010b403032403a00e0711140c04489441041c0700d0050b6590f080c82d0400380010f8040303900c00310301c0e40c601c6d0756115980d103003844156205200300c18990007040d011524041043c02140c80c1c0d4080100011070000f074040703a000d15000301800035424141c2d00d00c0c1c03190001d60450050038032220341c1e0300a4502c036020201406512140703c00340404214120007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 943201717 1250 943200467 943200481
    0x4050c04050c160f0602190f030e032b0905031305090415020a0c053414060a022a091005060a18050a0b1b01020304030e0d02010e0d0c08070e 62
    0x25112015070b5504600303803540040c1080581030000a00c0603150070700004a2603247d90502c03141300c039808010354031082201e00c165000c508850500740f14444981007000b10100d0000441d1015184044040e07113001e05285003090341d41120098441164160404642d02a19503842050030008010a0760300c1d401c02c2c606a030701d001200d1034010b0f8241c0150f5010075417014191041c40d8100d107050740300d021660355548812003240103001d201e0401c0e034102e02e03400103800481d00c80781007a0202c0d40ac80714018440c04401d01081a103400450707100b011482071806400c940c15410b41600c8161071044100c2416104034800d020760440000d0042c0d2030341c14640c004001907100c1c00122650f95829140182d4002c5400581b0420690140d21480d03010011180209680c082d007801085e582c10401412030710300d92200f40c441c1c02c3c0d0208403000b40100d02221007460700d07400d00e1109040402d01c1494041560145440011118100484d0030340710b05c5d02d800000d0029407410050880940714003407000107a880c06070 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 943202967 1250 943201717 943201741
    0xd1e030e0a0303021612030605040b0303122e060513050f0d03030203190609022101060806010309080c0a0606030c0803040e160e0312090108010e04031215180504050c0405 75
    0x5401020190f000645a05d482000180444c0da41d0340726000c8407400703040c400d0003009030003140240c034030892030300d00702265500e400012109094411034a8076040d41d84c3c4904e0f29407020300c080450512440c14802524800100f5000202804042c2c0300d090f00c3d03e01c52101c4903820f0301d95802c0306014400810f0004c0040d07481400034616581c0c14500582e4958a45c04029800c1d140e04c41500c00e4142000303408501002c2c0c940141c1800703401224892901d004503140d0411000080c41100003040d01040403880d10351090f00021521409203c28078075090403100d009180203c8a441034404550b114014810400c1a0020300c0c0103020325001542012b0900030403982180002e0500e00700801c09004481c0800e000d8524000081001419a8441ca1040c0303090b1300b0076400340602d140010076150000c80c00040e91114030f805681c05a89441450006400e140c004182c2e043d000c0001c000703400c2c40020082410711188445201c210340110740d03030400b840d01601c0c02890b02c81d00d51180781090304014200d0f40344 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 943204217 1250 943202967 943202983
    0x71d071d1005090301090503180906100507081315021b060a0309060f092402070803130c082d010c05120a06120648110d1e030e 56
    0x110740c040481c0030240d0050b246840f072a1441034040d4285a610f205005000c0003410754200a00900511007500c0c00030022000012a034450344841604031034098284100050003880c2d01c40c0410034a494888101d070083c1a03e0340d030041507160100c4152100d4a903051082d04030480304d010121052a5801c80003807624041e031146d0302c0c200342d95150b0303e200340407494204041080380720b80304000c2c02240741002c088090701182c5040030424100014218003500c1d00c21142001e810045081c00c580b100298800c100e03c500f00152280b4580d0540468040021b0040e110308014107081d088c2001c2054540c602030007103641c200d005503494405801e040a0300030085441540314120002c003a5901c00c2e10f40720041c4241d8200c2c81850442046140421080c0c0e40030240c0c030800e80c142d001080000101581800b942c1800180391010741c6403510411000f0941c00600303440c803508244903941d54840c4014945041c51240c6030004005030800010b07402108020754140a451a0a00071030f0a400580d42c0e03101c3c1c0c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 943205467 1250 943204217 943204219
    0x41b020d08010303082d15100c05060105010c050a02120606030f070f031205040806011d0105240309030d0f050406110c0622052401060e0d0b070c0203071d071d 70
    0x465644840d04044c81d000301501d41241880f2075400d02401c0c00c1f0300c422030085968044c040d440c0ea0200043c5c010049081c81c560f200008180c40ea0911300111781d03080d41048102c0d00d034400c0080038001682c54810251084407484001c00e0a0b107055003c2500d029400e10042c0038a0b00080014010031005000550a41e5040100000e902100a808491920031980a41c195000c0d540012419261003080b0340c081c015803021244d11a41c0301d02c10070401d0030140302c0c014082e4210214480c9581c41281c0a9580010448140c074105440081801c0680354034483d5264001d560302c04000070010076116401c0303a1090541424201180e4000751a0313a008060b0072507210840070034101007110741102d00f4403030350340e1300a007500c1c0c1140c1152402104000c1d4044092010003041340003040c40c81c852145118214402070812000e880703d034681040c0004090f0030b0208025240c200d0320090780342088145c4c01081083c641844d43e1507501c814240e500d4024003a1420041810400002d80311145c10203184084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 943206717 1250 943205467 943205491
    0x60509010302060a020708061005010f08061e040e03040608060406080105061809070302130504030206150616021318110d110906010c122d0c03080a0b041b020d0801030308 75
    0xb5181040e486d1903c6035205101d00c1c8600820009845102c075104030031a070f000c1c4c85884007540c06890a943d0900129034a640111980e010b01a84a10340c185c50140034001400000722440910483d50844c0c1c0300d50000400300d40914148017807400c09200d07200007000c1150003003081e0b04141000844107500c0b07002075031100800fa40455005107090014200079035004200d03080d42c0f508c9207800c0c0040e0000b03c8056025000e00400505440c2000107500d180b00b81c001e002c0d40c5006600f00f140840e490000c4000d0744c01030307204400d420351001c6038811114070300c072125500384010445148c20b0381d24030310003514a4010391020511000080e85003080d071207090380407030b01e0140b55a80c0d40d0040714054a00389024140ca2014000c08100c280c21408504003107a0f03035a082462056490324196402c0c01c2030215100080c200f03103544010034802c040498000c024642d000c12104603b000141c01d44158a54090902c000c4c0305074040d0240c0c04112031103a0000c18200301c030141d85141c0f03002c1c102000003801202100c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 943207967 1250 943206717 943206727
    0x30010803040b071509030c020429060a1215031203091703043e01020703050a0b1003050f100f0e060105040c0302390f030d0b01050702090a0b0a050406050901030206 72
    0xc03904050004c01c00d08003140400100b030300c80c00d00418204c1040d000780c0c00359142c00061695085407070010401441c1e005100541141c010083c484180d00c05074115080000030700003010301106e203008042d200300c40080c1c00308a4034103600f01030a000d40034051000a00d864201c0c0900001c0c2c20358040600803400400c41901c9030344030309000441c2c50208a5001c3c507011000805080c172500e80e079a0394070254070301c00141158030501005980d04c401d94000a841e81d80107000700d0002603a41007039141c0c810713400b40c080803000b030341c0341d032064170b0050211840e2030b454000e501001400032043c41015005207001009010f101d43d03800d1029101d20042c01418081c075100c501c8a02041d00036011a480310401079411182a0342d01e81c0740c140c42c00314040350009071030115261400c40800002c7e8000060407403102851820103d0b800890090601418481c107003d014403104001d80d80c0c59504500c1240600004164a00a00b08000020f41d82c0e410040c0706500e043d00a0026898008400d41075a9058915907030310 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 943209217 1250 943207967 943207973
    0x1207020a080304061209210305100f121202150a0501150804030e12031615050901020c06010e250810170d030213050406060225060c150e0330010803040b07 68
    0x1910031214585960880986102c4d98552603032281d440b5908881cac066000b00d444031030015109400c0c0c45070380848100d454071134001c80d011018040c06418940100c9100009901044c42c0c103000485141400384d6450700100400d84212810b05100b41d100e1900600614040d500a00f00d405100341300d6000e20441d07040c2a42c505000c00840b4920181c10001c840005040d03d041701c60124a5044001211300704804111034540500a440392800e207e000b0b0040e0340e00b40142c080c1c940c440242980324050443c4410000441000303030454802c485980c85c1c81032860041c2180100e512698071100e60f03268100d42c0409803240104107040e0a904511700940d40d504030301407616400348180c024550241c84e150340000c1107a000102401d2603030380d2401200a002c0900515107050388548108000b0031a5460703140c001031420510400c5c01c800c440d10004010540d0f03080f4504c0c5d9000000d440304140d542c04032204440f04200c0b45900c440c800028030b40361540c1041c0b465610781c021481222800800442c1040c20 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 943210467 1250 943209217 943209233
    0x4052d03120a0315091b1202070c2c0a0e0d020705010801060f020327011d0a1a2217010e0309150d020d14360a051207020a080304061209 60
    0x4054240d028000011a18480300b15a010006c80c040860020f4282c01c1c03d4640d40d000307071a00140c210924400d15803034100d541c1000400030306046c030800400e21000720407100c9444028011660500009220748043d681390b0700d0a0352008542d0159485080104003682e801501d2505603151303460514140c1c0302250f0f00342c0c03440c0610051480e00003e00e5856984000805502c0000c40304240e030b0700c0d0490300d03100300501c010107050200c0c280c000c4091a070521a600380004e51000e81c51001110074a455035001441d50140364036021660900307103102c0100700c001c01e0444010382c4500c0ea20020040405072902032070b507070b10503505590301414a0f6901e44007000010410754451800180c425981d410a00c04210020b104200300840c04405c1d91020429042924400602070320b01200c0c2142d2a45e10b40e071882c1034040609480510600c81c0c00f8807000000c030b080c000d41c40407003a170310182516208244100181844507402680042d482404100012903000000000c6042407800000354281c4034209142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 943211717 1250 943210467 943210469
    0x3060614030c0105160203120a090b04032d061a010207060f051e040321020d050415080c0919050405060609011d0d24060b040f03080d0204052d03120a0315 68
    0x545402800901154001c900d2300401d41001301e40d40350070040d6200c48105056002d01c0c04045d042e848a1040c0004518a41c0104c40c10740c100744013042ca1320710480d82d4540c2078a6080501d2240c110f0014010a12540c041003d007007e08660301b0312812100303c41d10010034a010700e4600c001c0c101c00217042280380784c15640884001d5a0401d05400d00381032000c405154005010100100521402052064141c0b062065401f034030b078122146c0154074805001200c501001902c1c4454000c02002200e5050740c4400d1030f441c5c0000089800303c0340610f0401003004841c0c0c001c08880c001e0004010080c5c1c0d503032380810b048102905010407000c01078042c101041114002030401030001c40820318020008000304c0b2045201c10400740d0600415868207401c0d001c034040ea11980da0078950b9076409100140c200700203040d50700414100181010343d0392002503010b21240d0340784040b5007400f143d401c0e44550001e0384052005400d50040010711040c5140d0240d0384182c100c000c0805589110510481d051000b42070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 943212967 1250 943211717 943211719
    0x60203211815041e150b011215030b0109050c0f0307020a2013060f141503010306050708090703030203071e0c1511060c041203180b0403060614030c01051602 69
    0x15260716a14081c0400380b401958142c0f030a800c400005203504610080200000da4070541007074003140d0590f00c00001e803600020b02414800c00a81c0c40254110740d216000103091040e1044201c3c0d81b950401c404890720681107003403500e00386000c21603260b9040d011610210240700c0000d41d66907401d1780803410804400340041900c040f240d400040071000320018070070203100b10b448140c4014500c01e02811214184540d50010100050030030402410001c214683e1401900c51003903040a00040034045d80260000c4809642d20402d00c0301316940640d116a02030300d410010000d10b4251389000c0d41c0c07800f401c00028031001b840306544040b440981800240250f009490140d20390301d4034401020f00381f24400301000140c8402200095100014005020348a2117925920b05424403004142c1a00001029414082c10780003407448006060040700040866010f0103803100e040d0710b05803042c0e60085d40a80c0581e40e20800c882e00d90b03500883e440010340d4090914541e602042d25052184d00000c580103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 943214217 1250 943212967 943212973
    0x12020a08030901050703110c0d0e0d0b04051006050315040b04020409080703090302030d030c1d04060b0d0e0c0108060f090a0b0414160c030903260a030e070602032118 73
    0x80140350105404c00c50080075144c07014485003421000c450f880d805100004207141d8000340200c50000d000325401c0302c24140160400d17000000d00e444001d02c40d0803d8504039020b603c014862940c1500600c14800680400c402034003520004d180d07178590746000030b40040c00f0459030002280071551598800c00383c41c1c0c2e10000d01c685a45003400e02910030344691200740c2c02802402c503445050b0340b10344a261186a450340720610b601c0c100b1101c410803580c060b01d0343c2c1d800c165074607400300c0c4101800700030b000070035540034011401c00c0c000e508890904d48100002e9041c44650024800e09959941110f20a250152405041695000d07a0800641034440c00507810519120016014040382c40400748150007241001420160004048984540e02c400103400140754031004d1000402e0b20b804c1c111414507080120445182011000e005a4040c850b03010100c1d64640c504100f1071001d1003420002d1815001640c01c01c400c8544142509640e140c41c0d02142c44440000b810034529408c00d590152260021 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 943215467 1250 943214217 943214221
    0x60406020d18050c091012060b1309210906080105190b031f17030f031302031606031b20070806040305040302030601080319030506010c05060a0f06091812020a0803 72
    0x40f86445105440034a80500c80f8400001e04020a540000003200c8281d641103040310042d032281801485c0c08a00d00323610040c412280c214a00803401204909030084202c43c03010041c000f5541820040d520208046c089041010004a5088004141143c00c155401d000c01c11801c0024090055070b900100c40c07151003c000d000d03c0342c0710390700485c41041184005240e4580c80c0c04070001540c440c04004441580208100652a0040c41c051354120011121040200d0480c0c0d00003800d1140703403044006001040c40d410401c2e40d03814050034000356002d11078140309116000c0b00800c00c0c1d0440c803d510903a07008441050740b50a0030042400101200c10a6500c28142494020004d5109120a91180c030402d4008220404040102d484078070120350400130310401103070300b9000b0b820010400c90510031188044c001103403044c4441d80c40390107265000142841349944641c115070140c1c0212904903c1c00046007090b00580c07001000950f0403540011180007101d000f00c1c5040e06140c0010500700022003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 943216717 1250 943215467 943215473
    0x409050607260408071505010b1819060e270702160b03061918050a15050102070306200a0c15020909040b06150705060405061602060406020d18 63
    0x3452900030300081d036550381040300c0c1c066004551545485080d55042c018804240002c001340010100c0d10312a01d40c04085031850b280800c1100c1c42680203002c0c0e0480019070000c208075a000f1000300100440d40700e090141d80d400d40b4031202070240506000c0c00002003020850350340343c0c500e40009500c8005000003601210700e00518441003a00c038000948290b4184003545110012401c0544014801190840c0e0f2100200000c00160b007600001501c03036120017166180c90301c000c46200101d1000045054203000311240f04a440188202000e03018140342401180e9000c41d200c3c0440390480b0010645a15032050002d0346460a184c134000c054000070410f8802c1c1d0054056224640680100c0c04101c401e00a20300c142d10407440f050b5481001907001800103070742c48100980100001c0c1590000c85108880600c00740e01106060707a240e0300c00403c00041107020840c050740003c501e6401a00f201e01480301035502c0802400c010065030700404d06001664080d0302400c69941c2e40355a0860712080c0303003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 943217967 1250 943216717 943216723
    0x2307051b01140702030304080313061b020a0b18150402030721050d050f04061209021302040e09030c0604080d090f0b0403030f050c09040b03070306051f09050702100e0c040905 77
    0xe025440700702c0c000300004a03020700200035248110740090119243d9074400300340000d116103c00084500340d03654012500700c003110003003603103510743c070b680082a030303814281071921400400400581c610100c0d401e00303000300c1030b000c10511404c18a541003000e05803920f04c0000d040481d5900000204020b04225180f1281a000781000b114000c0091f10710054102100301c40c02c0c441c0c200b1410714803004002c03c0100c80c1c0b04844110240002c14400101c0155540c0012a5198080d03d0b000f041c0c0c0e004182401410703212503c040d00040060025458941c0c0c2620058640d1802000504504000718181040d4042900310480495001551045200c00d07494451802141074a00b500003c1c68403c0340d803003d00040c4070b024051400b8820f06810800c01000700405001c50052081d0140a0040008001107050103124040c0030307240010341500c18030040340318511250b540f014045509010a02100d0b07a004070f0007150310040404003041540303003004014604584c40e84a07503003143c83c006d0040f052003004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 943219217 1250 943217967 943217981
    0xd0204080f0c10030b03070501050a05070c0609150c020d170d020a03150909020108270307060c27030602090406030f050109062d150b0c1506042307051b01 68
    0x844a50a04429100c4104c04403640e6126968040d4002d83c001d0019601403409080d46184502c3c2c0b4515082c00d070b0b9201c21400e100340d4010004140b8403003080c415501e94590381a075580c001e190808010b01160001400440070203809810b450b648040b403142440c105049448c04051410150742d52740c2d007040001c00030103501c80d05183c0391000200c045510035441c06002030007034059441b00c0d019140c0182d154002c0c3c4415468000300c1000c112480300c110402d01c0a0700c405800b0b10000160741440c00c070040c28403071380350040d480300c0042d2400c078550720440303045084241c9800050051300c492205c0042001810150000b40c41c0c04103c00b900400c0060540011441c40c0c0702c3e8800f40a500c403c44407803d004402d8501580180454500c034202d00d40e841d51002001010450048000c2d0341e075095592956030001110f142190001402006880c0c06890300c540c118105a03403c115001504038032a12880c40c09442545041c0a500810f0711940701e802a608201c4190310f4007405009883c101c40e00070014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 943220467 1250 943219217 943219219
    0x131401060c0606090903021c050408011406041401050109140121020324060a08040f1a01060f02121b151305060f0c041e0b03070801140a03080904020d0204080f0c 71
    0x40000208440413140145128207900d9001003212605620100a04104150202c400c00c2024000011a64424010b0000c2c00c00f151184817546c1c02c00209000566600c21441882026810010802640e000b14000e00f1034a5003412030078a4094407004072032401800f40304981c90309441100b4400d2545660086005122441c2c428960b07180310030117468501d4003022125032140041c000040054001c0714801d07806445081c0c401c0c103030301c0c003941c540e85003100f24004c039003416446034014000f4030303080600c000640005000030440e82540d1080c070542c40c0316142c44030750000502c001d18510400200400c00880c80a0310303c410a0b840d1280c08200d0940714020152406d1149a007c240b8010700c10401c0390052059a00d080d18003400c001d2000c0802d04518640e60010444420001d20400c0a10295000310b456944500356075240401d01010100d40a0f44035118454988081001036058400c5507110501900c0241e1280e8440c0e40301802401503912000c414028103121000e41030b030225001c400400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 943221717 1250 943220467 943220471
    0x81605100c05061f080304080a021206010305031b0138040501030f0f0f140303150105090a061409060c0d2604060f02070f03090e090a03020c131401060c06 68
    0x9603a044940048618001d081c58200c4008186010140c00215000d9045070752001c44a660342c070b166070700d141e0080e4031000303850304644030301e0b82145007e401c80d0b4038136100c1200810042d4110b0721241d88920880c1010b0701c0700f020f410040041c03601c0a402004030550078512001e0b40d2a140781c1c01c1580100540140b264a003103e001c0d407080c41c98607200d00c9041c0e030380007030364221002615034402168002501c4242d0322841034013000c0c00050108448803103d5500400656200d061400080f014995540c2c022414084280103c3c59a5180c021001c01244d80743d00c0c0460040208800b003036400d20581040a4014200246107501d5990002e002c801000c0c03140d440510103040c0d00955007401d5a41c40e0030302c00c80384450020030003180c25a04102c0c40886042c600615160155596800e1004048421804220f02500400140800c0c405c0c01d6400601207004e4100302480340c0e4000d4982c07400c0d40c946445900f00c1d0108041e0003549034030034001684400324481c4196180d40000d000c048890508a810718 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 943222967 1250 943221717 943221739
    0x9070906020d110601090b12070902040513090534170c010f0903060c030b0d05010b090a0216200d08030f0717060907030b1f030b0607121404081605 65
    0x35104000c3d0740085654080070b44844d0b401e000e0180041c100e1401110781c40b070f0400090a65944040c00103070b00620042100582d514030784028400d4a81c000d06c0b8182c8403500c0c040e003680100d14089812207144c260030b005140031030b54840140e00c5440c1c48145a000103404580c010800740c0d0501c41d1040660140c000f2580c0f0300902d07a00440e810882d030021280001d07c2110100001865038100d45400c41c445c0c00c002c2052104031000c551038002030032040e52146c0d101c012081090629a401035041003900c2011f500d840070680c0400504150000010640885040e401c0c003105a00707080c00d4555035004045540007441406c0900f5550819103071050000303a040e020400300790044115003940414602d41058983d1000108424510001d000f0b40615031224000c00c83c0e6522145d16035080340b5000304061604c80c0b090700007011121141000b40c0188010004200814400c00c2c032000200c00c54075052440c805a00151a2113010b0f03075000c003600340f1a412098002030385245075036050b104161091440d0b5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 943224217 1250 943222967 943222993
    0xd0203480109050f0f0a020d0809060a0314060a030c051509030a030305090d051c1802040e010509010609021c02091504080d260a1a030f0c040b0a150804110907090602 73
    0x28403c07240511700701d90089010200500300654410745550064441505146064002c41c044e540705a0040c0300003680c0300c054442c5102407002c7e4a400c18015105010401c0c1541c2c3c6510410345940a0984185000001c000c1c5400d501d00458031100d002505803842c1344594900903026180682e02d0600901481e02e4002c241c038461000c2d240d00050aa000c080442d84004440740104812810880d0705914840000b0140e11540102008244a80c000090901e080075045003100c95941102c40c02c18010401e00903000b4032441c0d050800648040010f82c6e030508400001c1040ea88a280d403e610800441c0005800c40d01042040000c2d0b0b49844804161500c3c80c015404500400d010404109403400441d042c412a640700ca00078080c01c86d218034a900c1c542c000030340782039000a90303040c80f54880d55050050303083c18003440c2c4503540c0582c1c603030600c141800c90002920b9000c2641c8800c00114400250a20540c860f1100e039060340984008250706080200500340200d60181d000580b0811321005c8030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 943225467 1250 943224217 943224223
    0x309100f0b1507210806010c0f080a080a05010b181302130e190209030a0303090311070b180a030201120504030c0f0302010506150c1518010501080f0d0203480109050f 73
    0x5941d4840c0d41380510780d03880300015510000043c50548270035804000c00b100141c00c4100411500c4640c0d00e03111041c2c0740075003400060b134405030000c445041080c400c00300d201d41c41c2244d50345011812107000c2d08901c0384002c08030003406001d880c44402c20150320002603c6014030080c601401c6c0c1ca4604809100c42c191984081e40b00e5548004d030540d202210b03c1e00800e11a0340145601803080ca8100d03d51004a1200c40c500840c0d030b0480003c040c0c0000e02c120380740350f0742107210705454000e5410070b2641e440c58001902c5c508402407a60203280e01d40340040c08042c0b060303205041495101001d90162030042c10001e008110444040c0c1c05000c4640c1000c002070409815603400f42c410078001c111910504000382400880600700030464524100f100441050a0003914082d00c2c01000801d01414220000c17440c11080d00411030a40d081000940013000d00a0068525910a51014040d541000e940c140b040308000050075100d003c0c00d020a20301000c190040b80c0d070580a141280d5078107490000c080c1e1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 943226717 1250 943225467 943225523
    0x1a010609031b0f1202042408190c060f030e0106090e060a0902090a11211006030608030f16050d030f0e06150f13090f02090a020309100f0b1507 63
    0x2510443c1040401003c1c05105a06211a00c0640301090160485820705c0360a030708a000c0c02c0381070580c4d103002e110043d0200503002e074200291781070601c450015180d020748a4414082c0c2010849078250104456000ba00041400b64980b0000c00c4441d41c1d4441d15001007040752204043c50045030041840c00d0034034002c4a01268004003c0b1703509866481810004111075110401034040c10311a0240302c1e1190070f80440c01c030302010012501c1d4548180710740c1c0010800e81214041c5032405034184440f05002081e1410445a650705603907a010b0a01c0f00541c1da031007200000c0032403040e11002c41603a940b5801c541050084080e0900010030707010661926860100c9540041d1181003030511007038a0301d0b0799000d840f220060301c2e1000307a0801808840c152140300c0000e544212800340703504210f0610059066110f80800421030030340c00d010403c1034030b84c12f00300a454030071078840314041c1c2d0002c10b0758400aa501001403804858210b002800c1c3c0c0e00e5000300034251100301401d013641002403100202d80d5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 943227967 1250 943226717 943226729
    0x4030b06030f0d1b0c0f090b1206131e03110c2403040201031b09150c050c0f040e0d02010609110a0804060207170d02090901080d090608041a010609031b 67
    0x3e0740b41d41d6200102c8450404186100c1424505134120012a41e441180c501600c011901c140407107082000020640d458502040d001d50b08070b4003d44110305010412540210041008040002d03003410000c3c00490504001300358000003038644810540c0100700d00e501d08011301c040c0c030b095205004c00c100302c5ca83c40c0d00c400c9440380c0a001480160b1080c5800841d4407910506000a4006141901381c003003011480100340450354601342840341c11404404030440d2038140c0b820400e0b42019070b031950b07141c0c1c1310707130300f070079024000380b4540e042155959000003120840043c01c070f4100c0381c41c24000901901061140c142014075100c034104000f02d800040340d24070115610b5032030090700e0300da550030003c0d4401c00d4152894070080380074142c8515a074004040d04d5181030000f5840381c02c030380708001c45d482c41a40303c0201607001c424520041c030340080c6490104c1e0312500744504555610f0030071100e420f000808d040940b08024002140d1307a5082030b0760000750390243c00e440e03410140f0710302242c0030b00d64940a88 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 943229217 1250 943227967 943227973
    0x180a0204180309060f27081c030b04061401081509100303110d1407060b0406090207030e09150f040b0301060f030b150f040c03022b0c050301050906060a020f0604060204030b06030f 79
    0x10241c2d86c454115105180c608504180302035982d842e5580c201542140044010055280b2510b0f01c1e540c9801560b8000d601200d04026580ca052038003603003a20b10700303401c07418402c8030700c0080c003610920b00b68030800b88006401801e80e4a010804851400f496010480c046903502c0c1c800340780c0d1080090100e02d03143c0c8988a0070780d451211500303407249403c01d030412149203454941541c159111030103241d000340409074026840700310600d8080c08402da501e02c0d039801198841c041101c8141500c1403802d00c414151000c9241d843c92402180103444580109a050340c00c0400001e0800030b42e07052075081f24010420f03403a04d5294035450350036402c41405490391000e0a42c203070348514039060740f0142a407400c2e800e0061421a01b00d00030071545d41d018041100c19a034000404244032164080c00141070064a8030610f550304040020300401c0001d0041c50092602040f0484154004c2102c15100c08040c022a03596140a1401d540a0341c840c0c0011101f4070004130100c0d8443c00c0000b45d12a0034003040c005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 943230467 1250 943229217 943229237
    0x13110c011805190212010c17070c0209150a0506030c640c4202070507032904031209080d09110405090601030209180a0204180309060f 59
    0x89042d00e64280800b80e03403010b115415817540620034072030711000000a4945c0080045050350b1070503c0321000303000809100040c9030210060b92100c001075840700c0c80c41002d1960301440310100c0c000103080e0300419005600001070040180c08100540401104211071319400402d80c0d2030600c0724451011a0084082c0c030344901196400513910704c041c180d42c02c0e4404404107280026803402020f070383c12241c02107141580c018040c03000c0402440c004c00d940c1d1541d0070300300e03400e0081c2a00b1800419042400401c0c045411403415180e90112000c0c1a0008110b40017261a406c100320481d0401e0b040341c00d13407003440b03600e01c1e28204d24208140c42141c01d91107440c5924101c1c0030000281c0001c1904484e41c0904111402003545148034200c922401010062207043d96202444120380001e03040744900d610040c0100016518903d00f158000300b0031002d1502101102c0c40d5600d89403450000a41c0142002156a41001d19101a0400c20f020743d0740c04003100d40d100016603042045085040c00a9030102f0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 943231717 1250 943230467 943230493
    0x1f060f0306020a020c21060c040f06110312011d0a2901120617010f020405030a02060a020c03150a0b090402300a0b09070e0c041413110c011805 63
    0x40500340725549401515481c0172100000780740100d50154030002c2d85003000100100002c2003080329407111504241074500b5041108005c6492810300c18101080880040030007403034803d02c10764101c4844000c9180303131075844a00e200140c410640c00320586101c41e000041208603107008400c0030000c000400120b000c0d05003845286203200301200c40c10300ca01e6010341d26415080d4401c00300144801e003142c850710103000e0140d50a440c00d031030320141a140180030900c40341c2d4020070003009a6504a9126a4415815400740d0500d0b41d09010181c0c1030041404a1388603c08104003944101c0e0080310400a5854542c10415031035000c5d90065003201912101450b403580b6904143c4800d440403036441060781400d00850301d00404803800b00d880c15046400e01c2050b1400704907030005000c032800a48054601307c110700c00c2c103000394450f94207691540b1031101c01e141c0307800800e5115420001c5051054095800342c050265010030110b90056207411180403207489103030400440700d41d010340a00b002000341c072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 943232967 1250 943231717 943231721
    0x2a060a1b051905070f02031b042909130b0709030215070308220807150c080106020309090a020d020d06050f01090b030115200d020105060d0201050712030f09051f060f0306 75
    0x20301300f1540f00c0c0ca03083e10580540e400b0082001e84c1c1f18942e80310680d5820210600c0240c0e4540713180300c071020b60b40f107003100f0307401360038031300b01d00c4071801c20740f10140710356145400682d501045404c01b81c0034502680a0088041d4000c00700410340e80260341e01180000c4100701c50502d032081c0600a000140002c02242c11843e0b40c80d03442e4000103000d01c41c03640c9160540c4031070b002076003e40f000f00ca12609810440368210903900480b07040c100c0d24280040a0f41c034100e8040e4030392007420080342c0716030312a10004802c28425416a225030b040d00e40115243d2030000810f800410b100d00409105807010b5808541562041300303108155060494030740e0459280c443d02009a0300040c001400344000e1a00c0319880c200f04c01d010004a50810000748002c0d03d03a0030002c0c6c03c6400280c55030b405640c2c0c01c01a000584d070008102c0e0f5070198030039030001036902c540a080740201000044a05202d081001400910800180c05103607484540840381015640e8000341c8101c42981c41000e10300170480004101140040d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 943234217 1250 943232967 943232977
    0x206010b12070c051024050301060f090510170a0b0a0c27030209100e06180601080603120c030711090114090406150b07061a03032a060a1b051905 64
    0x180342140c1c188900c98582c10180d96a000300b51b4100002c100e08002c21944d902001402808140c0080040f9802c1c800c0b03e400d4500113004014140707231920080f0300070350b1030250301c03000400705040031b0380300c840c85070340c07403036100d400643c0166410030f09100071039403c070042d02c5888055440c0382c6640c0440f01ca014803032019000740072011444080c42800000c09600c411817228843d41035a01140b40b280d08000070011900c2015155030700503018820800740c82000305903404c1d00300c88242001c40e540d5481200091600401888248403e00081394020350307110b00001074500c60b07100e402e004002d4100c0305c0512054000034030603500240c40c500f0401415040c14407455404c203001310004100d201e0111080420500b69034012040c60400040c41004e1051034803980c2c903810500d21021400750b00040029030f8074005d10741003500319042912040820801c4019030760240c0c0d401410359a540c0350447c4502e00a000c860011003807440c070064400d604600c100101c03a440021200700c0d400c03901008204803050703000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 943235467 1250 943234217 943234223
    0x19030e0a21020a03051207021c151e1b020c1c03051b0307030f0f02030a0c080901110a0c0503010b0d480303020705190302060906160f030206010b12070c 67
    0xc11a00800403650501010080320501400300d40c1d106100c8c818806001500712400340d0b440880c0050300f000a100c90075039040c5811100c00805c030038010700c1c4900b407112480c3e4202d01c9294075004040103a0000501c000030140300c15000d0b00c1c0145c01c0081400080031a000c02e0a06080c1004055000607004001400c2e04003c1c910080005881804440d49198071060342503000c43c1d401c035900260f036580300c82007030501c403003600c040c5061030350b86400a410701502030f0f03001300004d0740420b501d141030344502d007110f0590041d1822110701035220b0400303052521050003954040c0d4249004a075030b50810081d080105075000e44284283d440104004181203404140805011001141201c03103800070700b07400000802250480c10503510314980640b40c01d00d1540424010f00418541180241c280f0404408482e01510500d40c1c60320700310005012403281080c114245030649074040e0902220000006005209808032900380e6245c03185110640203100300181c104881d00005040c0c02c3c41200c0b2240101c0c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 943236717 1250 943235467 943235479
    0x10f05191e09030302042c070f0f0f0e061239130b042c01060504090908160c03030201050618150310050c130b281119030e0a2102 57
    0x7e200c9541981c0e0040052860801002c40c0183c2106603081d80c1605400c842d982c24078a03202d10014074050041620141400300b80704e5a5007009481c0350086102159400d40100184e60304d40600350341d28100a030030740e001c0414440c1210a42c07110075034402190501842c0c48150401c1013103041c00da40c02d551010074000c1301b410340d01c440000c042c94030402810141403240da21a03020b441d0003142d144203544002c020f030141005013004000898000003101c003940c0b4a1500800e41034028102280030348621002c400000e40da40c4502801c0c891a80c1003403003681c0c4240d00034841511040d04100030000400710010461030014042800d400003d4061010b13807401030156145049881080400c8480442c0d281e00602000070320b0b541003190400d04100980403608026051142c0c107140c120341000c840c0f001d402498418507000c40498003d2400e913039000800e404507001c20f110400e00c0381c000764084508030301059070282003101c10710741802000b0541e4980d400e10706c1c08007801d079a040801c2031115000d070307007006c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 943237967 1250 943236717 943236719
    0x170109050f07062c09040b04060f05100b07032102070c0602070f1202030a0204050406020c120403080d0b031608070906170a080f07050304170c01020a0803010510030e010f05191e0903030204 83
    0x1485405c4514480c50044080175520702c0d1508080c001c1d107000c9030403203005514240422070b0f0303484800c001d1401e840551400b9901c1d45202d2034182c500c1d950100b1403007010f00301129410030b4194035400404e0700500c02c00e0300c100d047d503481c401603a075105030b405010b075518100601031010302404000250002c6c001812120b0780181d81d004141154400c1c0c07400da40381600010341816160701006250340e94084800510701e01865511020b02c58044d9007a0603051031740355403440210b03030740820a00b4041800206010081c5507528201c0c0d545880714410600442d061045c00909216402012141001048050240040340d9500c960305940014030841c8804000c6c00030301c0120f0420005440035040d8014201550041d03130329001d10300403d0106090455200000c9080000d0050068904680090b5a040d050014020040e0302404040c0380070002d03586041d681004000e10340c1c00031401740d0b0358140f030400005c44800c10901901d2124a9070300b034105601d40100c10002c1d141d0321241030303140039140040c141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 943239217 1250 943237967 943237969
    0x103060b010c080d060915080606090a0605090c03010303030605040216060903090f120c0812190504051f111b1c02040510081501050a0e040c170109050f07062c 70
    0x360002130b13010884c40d42e07640d42481802c038540725000050090032004646207150034004c955a0708018507450240307460034040380c0382300309640086020341001051607085203061040800300d90070900c4103400090800c10000340c2d5080510866145d46003104010110b4070440d02c07088090034603030070700310100b0800324400a0320b82100300c0500054051008803844605c00ba0030301c0f160b451503a401c900b14035000640910320050000049400c0315020701c8503111035141c40310094602e40076a03449550802c4968484c0700c410780034440c5206190304035803101d010314110181050b035a4021804420580c8203001032400c458941719000030030090502d6040e03178085203958041010381c0c4003079524640448910b00d050100312418054105c81502c0001060398940c944400542c518001d4450170100b0309110001c50306105484401c980644180c4075640c80c0110454903c40c0280807521081e1128003a141d0040500000418510112140c0d5130b280301c0381ca0400041c4104d00c100207485040400f52045c00c620755 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 943240467 1250 943239217 943239233
    0x3030c0818040f02090901090203070905100908060a0e06100302220608030c01140711030d1a100e19080705220c020a06050610142a0d14120103060b010c 67
    0x59000c3c81c0740150b212400ca5086c8281c428060300203415103401441000a400c4e400324103d021100201d41c00d0b80024042e180980d034081032078204880381d024100400002c80d003c1d410200300c260380c10003211020380c1c0300da421010820003400020360100400c5000700211140c7e10803105440700d941c0c400070303245555811031459075100491003451651100b0007941c041d80f4608440b1350185250a000d419440d010038016200e03c00c5500000000d45e4801030381c9620301030011400c2e031840e805000b5100703032000024060540540786042900c01e403880d0640108901d216104c04045070741da44000c2c6400c074200020043c11440c2e101c3e488200b2008050b0f00d00c900401400740080a900c6a0081c00c01c1c01107500f0203c040e81c074010000ca000e07510304402a003030340d6806048051500710411105450381d1844c0303141c20000d101510b0800d189484505140c0075900c010a411541c074603240c6640004840111207040075002d0f907a00c0b140c6928042e0300400125500d604400d1108d40b0514001e408640075548840c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 943241717 1250 943240467 943240481
    0xd0e0f030c060403060e0f030301060e04051e090c03011b2c06070602041a0a0509281d06030105010819020411030903130f26071703030412080103030c081804 69
    0x5449611b035280d590f00104140040111085003001461942d030500b07101800583c0d4840c82607019039511030004d8006a00d06d910340382c28002880004080c1d00741007080ca9030718040304400038460751038000081c03520031f610881500c00c0c13006603c8000003190422600d83c010401130001ca0aa4020500324076071039911000280031081c480c80005844909122081c515000c0500c1072640010b01049003414543d04001a00d003904411076041d502154480045210751000011210b05c80748641d5000c1003046005401806901c61100e0204840d542c0c0c1c0205406d82d03000b1b12514505030443c0c006010314041002e0f000038040e00141c004541e2031600c84070103002c1d920403165195a80c201180006101d02d012071540c0003440b060b000720740500e0801c888002c45408000c01d1001200714100c038440840014131079032009004440403011011049209141c0300c1d8011501241da580d0b4100c50303d00c41e54081d040460503260145d880b1044c1d00b0380f566565242d41d1044003115401c1c04800d8480c040c030b6803a401040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 943242967 1250 943241717 943241723
    0x8070204090b1e09030301050a0b090d02060417010f1104030f24090b0703090c0b091804030509010908030a02060c03150901081c030b0603060f1912020906030d0e0f030c060403 77
    0x10890b00301d1100792031282009480402c0517041040100714560b980d80040c8207840344842500c2c0e480f104080060083d0028a030000c0d000300e004640040d04200c0364261429214001d03000b4841161508000b00445004100704d1040341418001840400ca00180380e0708440d205004001c000024002d03510308440034560052513076900ca6421400304003601d0902c82c0c024040e81000d00400415541d40c80b01c4a0701c41c0510400250081075543c999a02c45882d0010030b24880355944807801c2604000340a540a4450345021800b42c2c000055040400012944c0e000b00d07540c06408a51500c05000103d42d201410807141149800f1410282e580c40e8101c003030082044000414046d02d00c0350748445041d801820507014589000e0090429403168000c4950055080380e082180c01c2b0410002619030740d01840a1060781c000410120f240b5964048050384140221340c1e048555803480209a512208031009000096a40080108504003000c0c001c024000040030b942c0811408008510304d600715600c00d03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 943244217 1250 943242967 943242991
    0x30c12090f030f0c050c120a0614090712050706140f1207030f060503070b090109081009020114070515061f0e1002211c0903120b0102011808070204090b 67
    0x444201500035251400c0f40c080360410380c151416070b496868482510307440160085040b5009514172500500c8000d0306258468000c00003241964958284410110741c050f03400d1045500c01302d841104440da607a01c00d0f9000c0c0c010480c2a08054045454100d00740c80c80c06004018001c8100800c0701d20042d00f01d0040d103040c0034040d40f80c030b4480201034904801b01d10a5161500b4804d0040303803008a00c01c02914203103403d0310340c1d428480004031610b068a91100c4035a000c3e0701541480500036800c000c603050300176a6400503030590107040c16502e1081d1080200740e5440242d16515500055090300d074800401898815003810019415401031485058000052007a00e10203105203862450980122000d01c000c040c1c1e902c0ca99001644c80e08000c1103101d96806c041070485080c0c1c44c0260521400340d00700307028441802a4034000c6c1c40365410414801045050030b5810203607510510030031901413606c101c3c542c108030b81600c444081e42d0083e40207a0b0090384035204140451403103992103003e08841009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 943245467 1250 943244217 943244243
    0x31e0f1c050604020301050a12022817061e0a0905070605040302090f040c0303082509060305090f031603090f0e0f07030507020a030e2808101803030c1209 68
    0x10004031100240083e2040f48144014003064403050591000e59001c180003100c0c0c0c6040780001940300c600354440c00c0d0181019010b034042d10350741412440c225510700c010200074660307220031503071610b10403a524242070003801d87d180c800c00082c5c8561900002c1c2c200c4002603080c0251106070500c20320f03400000200701c00007420811403d2400322942e0080c20044d200135203050039a00e80f00da000c0540b1000d4100040b58020805042408480140c000c001801180503140c5d15080602111201c0c860313000400d10703001c0040c68040b0041a10040c20030500702441c034001c40c00c2d40d0085111840308090301004590a0081107c200c0020a50042c10201103100d4241c40e120102080350031000b01404201400d040074005582d400140c070300212903240c02d010540d050501e01040e901800041114a40d21282c079200c82c10010030061a8182c94180c0c0540e028494074590b00c80c02d5954102e052901e43e242c0340002004684650b22510b0502c049240801c14940076616403800da405070a0165200460912 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 943246717 1250 943245467 943245517
    0x240303080910020405060d0207021309050105010302091303020c01180902041712120609040204020705100b011b0809040504061805010c02163210110f0f031e0f 70
    0x21a02c0c2c001009801503151500386404260307180551048400d8168010071035408668070510506010070700e180082207000b400b41030080c041e00003072000380e01500d280000305410046409000200a80503002410303955001c500446050b26082d8043c02c0300e28200d20045240032a0b070000304014480e503c0e002d80151455003500b41041e02d25421080c404d502002510541203a40e400c003170f0f10950840714414581d81d9030011801a1180315802011030141c03003105003540e50164803003498000c081c0d0718410744484c40e107003803250181c0440d40603081c52014016035403a132400c1e8210740d0b4020303c60080031800740e0580c90f6400a051114208464a944071001c0c0c0c1c10995040019041040e6480755a000440c54010640f84161440c80101030f0b1210383d5001015045464060500b982005032010610b022040c500914494020301600218040c003212041c04e0b0800080040c070a00c210409180b4201c007a01c0402d01900c0c2d134080140c8031500174807200100c0c800c00d03c007510300138008501450010640007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 943247967 1250 943246717 943246723
    0xc03090d170d14010b07150c02030708070302030307110d0e130609051e0a051003060b030a12050d05010b040b0f0309011b030c110724030906021305120c03030a032403030809 76
    0x1801038080c80c07030b050190001080c207001a0113044187c078400043d64a0b0519012420352240b0f01024101c601c00081c41020540e0010085118544980e1000030703c83c0e914603c00e484071020340700300000880e1001221140d29040300b035060490721a5500181941c0d803a5901e40a40c0d1003180c81e40c112001804c0c0004003440c0301c0714615488080030320200914544072019410b039601c5800007410490b0755803034201e41501e0800081c40342d10b4000d281c0805c490788440c0300621550000000541c0d01d414400002a003880070030650701134803003285a80e42094a480d50324600b540001309000c40c150b49452001000710a0784283c2170b5500031541c4e002c25150300c000b5018045900d008254034099000382d070108020030700d90350032420400000c4c8052550542100c011400b03025880c2000d800300d4400500130007002c030040d03c00d00403900240c4180d50080309060b807480d1603c0c4000c09954064004008100c504c910982c012007694103095019184030001c1c84801440510a8100301d010503090760900482800c20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 943249217 1250 943247967 943247969
    0x306130b07170c031f0905071715040207022e1e0c0305030a0b060c0a0309151b082104110a0609031b031506050906060c03090d170d1401 60
    0xe414560310b110002154100100c800400c0103810040c040041100320b040225120030b064424441900000d4440081d48024072060303400038003265040b4100d030b80007044681003503c107104d030a000c010240020420302c000b139400544100c0e4025403491484000880c030b0040c8822441c114124145c5040418201420702001c0f00319420344884c40d607000e5940305600c044070764000307a410305d0860b4407502c8904809002d003448402141e4004008260704640840002c1d01045c0039010740e5400c22035641d41d00d0516076052030098484001503030b10640501c05043c40f154050824031030f640141c50b0414480b4005d92030880301d500c026120f4000010b0005011442296202c0514115031510100f403400c040541200c1c00d61000401800d041001007030b8044429840c10001c2d0303084000a1450390400e00140024400d0f03003d428820f002c4080030660780d0034200203840c081c941c2c0000540c60000740f5030411198820300d90003126410008050408008800c01c00b42001003080c003000b2030340084c640301d440c001e1541 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 943250467 1250 943249217 943249231
    0x30b040506030606041a030106180507171501090e0109050f15030d0c06060312050c070b0913180212030702030f0a1a090c04061815080601091107020306130b 69
    0xa000c01d2008581d004180150000070455000881100200c112a84001240c5070700d50f2551030540d0000d00c41e41000e0b4400c1c002200070000700641d9940704c500340c5400340c060441c1c0e150210000005240d01c0700a1113000d400d44014100040e81d140e54074440c042c0690240c11007031100740c4800500c004034111140e40f503084950712144810140d83c041c0480d9464000918075410480f88030514800d04c0640d5204102540d00409400c5600d20302c1800901180d200d00f003501403d208007003002448038a01d400b42ca05001c0004d18001c000030300400301001403c10701031508007600c07018400f074005039030f81070303800545c0c1c00200b000c0c6868803072070300415003098500d10005096400024030b202c00038042e06011800d000c2400c04041440d207941c02c10a10b812558898603030003500c0d10f01e000c6a41007804480c400100c0d0a0304081c0400c003602915801d4446241c4500281030b84010b005208000c515084940b042202131601c508001680c0c00007440c183c0260b450041c441c003440c2006c828050b052004650000c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 943251717 1250 943250467 943250471
    0x61409010b030619090e01020901081e0a050a020c0604050d02070e0c030103230a08120105010f090911070807060522050d0f0c080d1e0e102708030403030b04 69
    0xc5028070408a03403000400780b501c6000d480c0400003003003146400d40740280c103000404120300c40c55096050300030b40c0324415441c00b08481000040d891010044543e0006085280e0158203484032440440905005007021400c16001d200a010500301084594400c90044c00146000d2025103030182c105075241d00200321003000700d001c1084031441101202e04407648003d05140a400d84010f0b05c10f5080000e10402d0240201d030210014854050085c059010580b400c00885076030310b50045d555050549010780100742e5100041002a541d980010740c205001e2000e94500340090341e4510040d88001c0040310b5142d95032040c040c0d040c4100c2c4101001c0d40083e01041020031050321160b030307a540040242030400074440c9848070324071710038440307040d03031943c8250800d8031920781c01e500001408610b6000350500c40c2d8510b007201c4c800c0e1140a48402e404c4090701401920240419040160a59450700c0c07660f0b403001c0e44005c0e4000c0d003802e2102d4003207028100b200e440741050b203402000c0e1540d40070901d125038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 943252967 1250 943251717 943251719
    0x20c0a1a1602040b090f100603091a0a11040306470f09010803070611090f010815060705061902040501050d0203040c03060e0a210c03050a0207030b0a06140901 70
    0x1000e0400c803888026a14988103032507005200040180242e8a40c5030380007080002800080040301040c94020a5210121030150b511800110100c82d00488080c02c00700c09055501500c0c0360f51540c45070050142040419081c81903040200306511552040b10340d42d50300c0c4240c1000380b0b1441041c1d942d8401c405100c4140c007110009801110340c00d080101c1310112101c806904a985a0704091040800500014069a5146901c1e5103a03005040140d072424108000081c41440003001ca80103a0030042c07003003403240b4010004650029006014414890069805207641d07500c603c0500b40c120f110b070008104503c0d00c1d008440800c49502582d116650051000b482983c1c0c0000540f132405100900058407980c1c0c6040c82c0c1803205180d407000d032107075103000b14030550204085103074100b55006103c2c40c040304a20180c0400400c51105402c0e00146031200181c00007071056008000a1040d0710490320000d40f641c5503901034a0054450001d00d070754a09081002210607400000042c3c070445143c1c20765 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 943254217 1250 943252967 943253009
    0x41d0a210509100302130f15020d200a05010e060402010215061012090c15091703071113060609180203102108030a061a071a0c120403020c0a 62
    0x240240b60b1814400c10418011504841c860b50540b45820780120710a00d54a40e0384c40c3c500e80220b000e0040b1203078010065110791000e800003400b544820b00d181c1d14110b80260706260481010f811207840b146a00910034841c0c04540d0074044d050b000510b04000d45070030304140c40068500101021111682c01d009804c00440b6695107200c1d10300c0e102d46081c021000c00d13400c00450024050380307000a1850211000101d62020030503080d180d00c8a00e521502500c984030094100030209201114465a100304207440c009201041600380340c940c00703010034090022540f401030a03038403e60050400100251803c101c443c2104141c188100d21031001146503052411036109028050302a020114490041c041005501c00701808207894025003d41e03240c1c10014401c0004c0c0c0007901c95140c0c0840700001003191150002d0480e41c80715440072950940414020303210310100c000a003500c0007002c0c240502d0810039440927281c0d1046100c1c0d8080c102c0f04501030b080014201d520782080760350440c00e0100c83c0324 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 943255467 1250 943254217 943254227
    0x30f1203160801150c021f1d0301020715020706060b040b0a021b01081b0d020706020306211b0a050406121b081902030f030c060a0c05030601090b09041d0a21 69
    0x880145250000c100c044a001194101c0500c01c070241c0c0c0c110040c0a80c2003010b9020701c110380e90545502048c50540604001c041c240d024201001e050342420409038045801d15500074000c0b80d1150002080040e0b940740000d00c6034025170b202c04058540000e603900910742c18030180d1103c12507502403042541081b40000d01e1800c004180305000e40d41141603105405245080d640e8160f82080d00755941c880925200c0007a41044c0d035014004c0d884017003c0c201004658501c12000f00992000b0048920b42008908507984144011038005559880c0800c0da45c030b40f070041902608400d9100c0c08802c00b903283c006001d24803c3c2e02d1125011100000380b1450401180340113080d402c414900303940b5542da000103811314209000f0f401c99031000144040c520320000c80d4403071242d903c140003002504801c00007901c140c03008a55079070020702d4581044c80146c40c503802402c0401c00142c00026a522014600006410b02c0315440360554001100b410400503000300c0e585082001e8512080c0c64685a400905 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 943256717 1250 943255467 943255499
    0x6270c030d0f03050618060f151804140903030708070c1208061e31050f04141212040503120a02030a0b181315090b060109140a060e030f1203160801 65
    0x11144449118440855440c52003003007061191080032035a4040c00c2101c0c5a840790700d02b0310580281c0c1040545409090040600b038820368050010b10315581e1503181c12101080003c00340b50a000e00c090341c91011442410401510440507120780202d41098020407840d02c00d15610401c02d8464110350307140c10f03103c0e03054082841c590881280103018034022040b005501503907400d48642c0ca440c3c1040311545042850307900a6000d5200d40c05e9221035400803035200d04180c1d1198001140400c000d0810681a4042940c4140100241c905050301d070680805070810640720002035a401006200140e40d551240284200c01106d00042680040c09800d2200800a084610040c0b00611041c240031000400311102c031034011042289510900e040301012078103460560014206550120b20304031404100412070600501160b035441c600344048540340c1600500c41e8143c01404c002008001082010075000680c01d1643c589a1501220318002009071040680801c40f8040040000c055a80382c000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 943257967 1250 943256717 943256719
    0x3080403060f110903120c0709050a14130305070f03091806080705040903080c07140319080c040806060f031e0703060f020a0f1206030b09060406050906270c030d0f0305061806 77
    0x94031160808261418034aa80d840b00b841141004200b14002f10305610070f604880a4180c2045a601c654821040b48914084000c010800410140c000f1800c800005500349100f072501c181000d44403a0010449010590010b01c81da841d00818002448148480409400d01788c5003003003d0140c2da00e00920340e00340507000f61280c1c0f500103819418480e03220700c940059a079440c11a070380e89440c03c1c1c090f000c68101c4210f5500099040c00420640181d0800303c034101c8000d10000c00c0c1c1c0e6203c00c000c0000f884c0301801a0703941440f03050106ea00707004a607440c0710000811500a000010314509040c0123452840e1080b2a0301d51040050020140e085042c500000c215440c0c004444145004101c0007000150409040350300d0381d004200003001c0014017a440340748121424055a1039810415680781000d40d403014103403240c100312400854003011001c0c0c1d80301600303044881918140d00460704155400c0420000145403850111096805005042c1c220a05950304041040c2c00b81a040e40428050a49 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 943259217 1250 943257967 943258003
    0x1b0c02013e03040807060f08070813020405090c03060a0b12030703090e0c1606020901200c04020d060905041208071403060409030e0307171e030307080403020703080403060f110903 79
    0x201c014081c204195000b420405045610594846c28042c040c442840c00078400a900c050001c2c07240c03031160507070342c0c05502c2c0c03081c51801080c00d960800003d03203030003000c0c0e03102c0d4032030540060403030f030740030007019015901d0b924002403030f41010424400311001600080c0702c3c41e0310030441380b00001e51180d0b40d50111540c11240340740c0b5446450298003184250941702217101c10807680c003424425940c0c000e0211000c262994038100c40301901081c8040c1040244455035003040750554010b081603002071031445e940007000034100e5118921031044031400d84090b28200010082110a280c000350345c96002890703410503140c5c141e4500031040f02480024011405a5291803100080500902102c4002c81e0004c1c140c1d80c040da21040c0b070343d03003e282d01000e000300351080445100b484014034184000188006014520310354403450141c40e035900c0a0822400c611800100102140c912070240c8040c41c4a08004555100e60f4040503050b104094144580a00708114002c426070b000680103941500c1020300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 943260467 1250 943259217 943259327
    0x903030403140c0109060b2d10050d0203010f030b0f240409080a1101060611120306060702060a050304050706030c1205040519050102070b01060c0b010b030a1b0c0201 73
    0x501e000ba4064901590320039803c0c00901c1003041840e80001c0c90040e004c0c2e40d0f040c00c01c1d46038480c01300d00b4000343da03a0314200742400e04042000e08107040400c0c024003250420903e04504610740d2000c0381c3c0260f100305210588400c042c010131809d40c4517280c101c103400c01e4800300d41c00c04080c440e069400d106a14003c89100070545450341d1501e8014004c40d5030012140794540b405800c014004030038600b00c50005520f0070b038000c10403e014000540308004210700034128003c20042691596001826030382d802041404090700503528030b001807030b1800c1300755580c50b143d003001d140803490310207203400003c140343c00c2400501329190f00202c201042100040c010580b42c485092042c00c14489116100c0c0400b2744459280034410150010072b880352140c1040600c0b030b03984000440d101554100024415182c50004209038200750002e1070b000101d000000880400e080d04452450030894000800324103101d58030360070740d03802c2595500d01000500c0003d11400c607250419264203220034403c4c50503868540 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 943261717 1250 943260467 943260497
    0xe0c0406030206120a0b12010e0709021305091b04120605150f101e050a110c060301170c09040b090f01112505120712020c0f0409022e12050903030403 66
    0x4001b21801020704a0040b0042400c0d90501030180502c140903d0310840c40001546000e41c4200c406100c06101c41807485401d080030484800b1000d808a840300340c502c140c924180c11003200a10042c21403500300303010703117181e031800b034043e070318001e041d12020012040d0b0040300b0b03264a903800110910131145107a0a5401040039914101d18082d51074224110a410740103060b00007008004860650300c91500c084452032005550780b03401d120b03240d00400184010012003070604075403006200900c00350fa000100c0d60005c1884103104440949051380c0c80b03802e010b5112410b0215880c00e40656000307210003200b441ea0314520380710750b25560341408a24040021841e00e44503a4000d01070307020042d505441c42c0b1254100d1107400250060b501121602d02c0c001e0301900004007152a002c02400c8a2a82090041040020041c55609903041080840b90452030b4440005212029200c210b02d664150300300c04008100e00129034060060138604001d005e0b11110000070380b50300c15411f1801e038012480e054 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 943262967 1250 943261717 943261721
    0x30f0903070f170c15071107030c0b16080a0503150612011a1b0a05010509060919230f060705070807260c0303040210091508060109180e0c0406030206120a 68
    0x4100c0b40340a00070fa1718444c0b00030080c10780890140e500e583c0c0b05900c08090700300c1c2c0381d1203a080d48001080542882000c00040c0c0300da0018200b52003020f0141d600368203544d00c414400d076000d5806200007034030000800c17060050180385e14642c400140d0b003103410045100c080752846601802854155200780c1503800308210a43d0403689190440d404441c001031030a28241d5990f111000c0403078180d4203000001c1c480f0f500004806102c0c1c00d4103801000801c9040101078402c41842105450030303013500a032046568140002c48000094050080004041d04204217043c681c010b8141030420408228103008110404282c2e401141c214007003000c416840e05000c824030b42203d59a01c030440c80414004132160010001d144918002e07680343e50380360380151080394403c2c9103000303080c00003098140200c070300c40c8103911036a03105506051200c1c1540e143d86071082c0400b83d018050541076250b40e101200c076003050040388101d403011303141030050508541c00100305000e8111207a180c010010001440300034a5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 943264217 1250 943262967 943262977
    0x360605031f0b0603060a181409101d0a080c030405041509060603020a0c03030b010c050303090d0e040506180a14040b0412020a0809240f030f0903070f17 67
    0x10200d96000780d410612101440744016008415441e000010b1028103040c01102e214040c0100f00500103402c12158482c020720f4842040065031743e5440a85031b000f82d03075400c6070103950303240024400d01d040300c03a0f035900348e034030701d0701e5a003408181e60b00b42554106e400140006600d40c444801a1116042a03800c1c0ca14041e65005076481820050701d410f80d40ba800510400b0345070702d00814004140c03a5181a02a8441d039443c03480040c145d070f0305800109100b941302d16142541490b240307805519586640b4650381064614ac1516004100481c4a940d000b01c604c140800c81614248103d2038038100041f4507501a00c620b4002d540050001078a07000a030b031204040e4580122510794508060400b00b0300c04208a400300c030101c002c070030542c1c2c6c12800000c1000b0010390180c012480d20301c40505001d4650701012048108071130603261005003a48050240105016408416840703240186040f42005009004000e0744d401c2003200c0000b01328084800070741641c12803e042c620443e00c3d000d5040c41c4c811 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 943265467 1250 943264217 943264219
    0x20030f030c0403170a080a0f020904060b0a0324030b330132090a0503010515040c08040506071812050705040f0e03070b0a0b031510360605 61
    0x2001041095001104019005072402043c41c842c00302220641071020740b00d009907000118000c0400a2404881c54000013600c1508402c050304083c0e16602180a40b14140c100202201012031504009a4107100d0a629501d40a5003500030582100b10881d060b400350201420107842d260010760004004840304e00903202c0e90300000652040044010425000d213080f250025540c4607008007190144500042e840d6074a0b0f190050751070241d540440ca030f5005c1c056541c0c00200d00d90340050551b60a1140030320488142200c04040c86d001c40401c0121020140700c0010b001c085001d10010440009145030302424506000c400d000c164148081d194405074861104a120072100c0d40c03c01501013000da00b1923000f55014001801c40c031482ca810740301c000780340c1c4669a009101440c042501805007030381104120800103030f03a03042480840d0801f4411418080d0703485642003445480680c12501e40c004140b000c041c0303150703c000034103040301035242112460800001c003811601081d000da8031410003004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 943266717 1250 943265467 943265497
    0x16030b10051812152502100905011b03021312031b1b030f050f0f0a0f080706050108030408100207110f0a0f15030b041a13020d09080309100b012003 65
    0x819046211003840111200480c070b42c0200c0304280c0c1d05c0c01d001c0c882051074803103130007400034803403c41c00f5203000b40159a41607410b90b490340c9110408000c420710702e03040540c0b6a40c000d42d60304a034481220201500c0d9100411341d81450040c3e0000c0b90b44602c08500580c44584130801c504440e081000c10302c4039424050f0030250341d0940010410a08684a400c8030344110262118101e481c0b6900b6100d80a8584004264000e035070003000042c81c001100103103912400d4110304040b55611440102c071000d800c100082d0384005014803002004100e81c13000355400001c1589030024035610414000234212001e4011145c0d482c1101c0d071641d824505101400d40c102011030183e54880008000c0c00c121814040400c1c40c10f0000d0030305040c00d0103002000110141da10380c004541405114108410610f0703030844603400e10403180d0300c15040c007844da00c05024241d241d80f0380c02c00703c0105d401c1105030f0351615401480c008080c49a0b036003081c5006c0da080c0a458010312080348403046030741588140031003058060 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 943267967 1250 943266717 943266733
    0x440702011d04050a090b16080703020c07091508100204050a031112010c0302090f0a0806010b250507050a060509090c0c031303120e010206070e04050a021216030b10051812 75
    0x707035896000c111303014041c402d443d003035890790207c000416100300c10b038800080391000050481800b0703400600441c01044100c8540c0c0d60380b032440a04039502c00204400b1031b9805035040000080800140401c0c42020130304501e803518010010300e104100f07110041c05444040110929075039a403d00401c0780c03500f03100a010000c2c0e0a0b00040c006d60005d54801e01c103a0345040550f01509000d100502620302c40c40080c20184d08148c0007543c545c1002146048019a00c41c0c140c1000007500315018055100f04002c1180d60704150400800300801d4022404002c024408000b85230766150501d81c11000c9110241d5848010a07095415031140b10404135203138503040c2d400070801030701c1c3c8061401c05172a030350b0b82541d401c4000012a1201d005071600c40c0040c078200885c050714642036100b25040b180005006142202039102c414000c4030440c1c0e04c0d03220702011610510002c0d098000d450080c5011030346800c1209146101811034010120746410b03809014040c08805e44a101c0b0711400c04d00400202c540207 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 943269217 1250 943267967 943267981
    0xa0c05070b27010b010203031906030c0807151110050c0d11041d040f12120614030c03190818060408100b01082e03440702011d0405 58
    0x1491480c10410b41190504240c400145010f20481c0410303507050f800f4601d181c03140046803043c90940d030940c20055684180010024841041c00d400420080c80a45480c614118443c01001141261802130041140620346501f4000c946010356269032003002440b616204088181c0e4098104420451480d281036010f04000c480054030481301480d01c00194420030400d140668641950020314400359003000d8000100e8221700f80041c130303c452402054030602c0082d0f9100340d03402540510240000010920b0392420140700c0c0f02402c6106800401454080c1c83c03158800c4144101c0142c00380c1e1021034501e810802c4590300310155a0004c0a00741c58580340e21080751034201c55115420603038a0008202055409034045501c80c160380b071103100c1008044205519002500003864000300f921100200c0010b920000561068140503260304000d252842d180680581d00d448060301094082e9030070b1183c0b0712a0342110030f601c0d4203180800b074527182c4a503070082d030080100b00da82d441403e150420140b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 943270467 1250 943269217 943269241
    0xc06071a250c111306030606082803031103130302160e190f0e010203011e0b0a0c0201020c030106080610050603041709031504060b1f020c060f120103050c0907090803030a0c05070b 79
    0x60307070301550741080381a43d1a000c1a55034850799a08244103031208a0942d540340b60381040ac00481d000f802c001c43c1454290b241d0004a51045501075240400003441e0b1003031540c104840c10010b1300608240d20310509110502d00b840000178490b0419489641c0a800c00b480705411001680018032414442d80e10071460040c082e40090251341101c7c1c0000114000c1d032651040400c088071400000e140c50f00c4118542261038603a015810ba06500c0f4440c09604d283d00c4c00d00c0b13024010b00c2d51601500040c05c2ca100c68087e00c5105500c2240310b00814414440800c10a41c98808480300c422000c55035031103504042410488440440410f080e074036802c00044c0b20840d0000c0082644c100c9034844c0300400c40024200d00d030750350485880143c0c0708110302d840c24104040142028440d00e082a410038900c0ca09518900070240c004550903000720303090041c1414031403000340e084a040d0038401c003c1c504040d84640e407800000c1030140400c0e168a280c00c48d40d40588101d42489800814001851400c20b000c5c1070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 943271717 1250 943270467 943270469
    0x2072609032d0a080417120913060b03090106030606170c040c14040618050a06050702091504020a02010e0609060f0c0d1e0209120105090712050c06071a250c111306 72
    0x100c6064004e240e413908000301e110410185400c0f21396040c05108ca090052200d00380c002892015a240004942c0803400e00142d407240f8111700c0041031003421450b155055690030307440468400c960000c0c0c0002d142000c03460942c050303010b0340c0c00518906541005c40f408411103001c02902c40c80051f0100340f01d07070320444400c4540c4052102c007088940e14000e01c42249024407a402c005141840108014941441d43d2034108141000360a81c05001c800001e049920031100140540e54852900c1030010040c0261944041a9005000140350504401c10b1481c1c004116004100d00041d070541040082d51000744041c0c101240a5250103c442c0c1b104001d6100c8881c5034480c0200414040c4200d0050282c20f106202c2040034090541c54481c040301d009103070403821510750050f10152100742d190b00020748051402604507180c4594610424480360b80302a00c0000381103590307448441c000a0200e064511081c2e2454582d4020320300b130510f1620149130391211940006900303d83c904559286c0c00c00e41c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 943272967 1250 943271717 943271729
    0x70207060813020d060f0e030a0203090109051c020d050a08030a0501140405040c0b0f0409050c09090f0601050a110f0a0b0a14061c0f0602072609032d0a0804 69
    0x29a07860307680b80e40984044a20000350310041e000d5512000500729040145c020b414084041010f000c824010340c250340000554500580c008075004a00b5a40322680c540180350560b008444041c5611074018001002d000190044c20041c12038403c000d0200300c007080e0a5000b81c0c9030b0b500c0b4104414002c014040a1248011009202d00d0001491815105503400307203500c461714040d00c5117004000300c0356810580c20b1400c4e042c2c0501000910942c80d00546109204080c502030352282c1d0081004014078001c1c00c0703007440040380030400503140d030080115000180700303040000305411601c800340c0c40e020403501c1c9114103020300c40076002041001803600380900708041e07081c41420202852811120f40840d901a07125090004030000e6443c074411810032640a811110f40040702a100c007410303a40801d2085402011804007210014041d810803055807161079022072404500800095590952062100341a0400c20407a400c0a00890009031717001400000e41c0d58400c464100044103801c90b108407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 943274217 1250 943272967 943272977
    0x1e03010905061206100e070e03010f0c090b0c252103030b0316030209060312040f050a0504060b1b071a0702091f0317090916030f0605060403260307020706 68
    0x40000b43e04046410751091549007200c004092400f4440d20407218050820000e01aa001d8055000d841c00e000c0c0b80312100343e4030300200c1d0303507422200700809824040d4460a46444248840c03500c0c4080400d405204a00300703482e04081742914000c44003004403075808094030f22008441e014201d1084541008500d0003510200aa41d040f601450303103a40400881d02c0100c0c164882c14801486d0000e02c0396040180030301155403006000ca0300b019a81d110340c200c800000b404007030401007864850030b1107010708001d650501c00301d407400408092a0007a03940050913410321103802c40000204020000c0140800c020702c038008040600c40e6540c42d40086802d9014010390000078011f40d0410390010b19407222340680c000701d04d2654481c8082114500c2d03070045080402c201900103980c50007262070141c0406221401002c114000103000c803892028148050ac0c1002020480d0383d03208400d4400301d0360081c1c1103402450000c0b10384480c0c8d004040030450750040c080b007840b00032640065000c0503240161a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 943275467 1250 943274217 943274239
    0xb074e05030622020f0a020609060a0c050f03040f0215180901061e02030403060c0801090c02061909240501031505011a0c1908180f060703051e0301090506 68
    0x20480d258481180c4854101c95041110150328015184007070840c19925801418180c050210410503030080d2206001a071201c424404507040620801e5088504401c08001c00502018054002d01542000c1c4c2408140130000506002e89101015551a402400c0c0800503c0910000d0f016070031051040c0b040e49000306015003a42004c8101c641a01e603180c075030030640d80061001c040060181d42810701140418000000091a41c0c000c12108080684444c074040d07050034040d01c222001c4848400440d402070742032100900448022102e602103032380b03010030002520b0410603034100e40c100340c0c080414909880d0241424007580890b058900c0b4a0300460400c56103103500c4256013080c010409032280c512450039803101e156000700b959050030720607a00e590b440c0041c000300c2181120010303121325000185510000c103915042403107100d0101c3c1c10303065804150300421020700075140b00030b00b88040001e840903600c0c401842843c141c4e108001030742c1d80750b860303203c2d143c0030344401e684840c095007419113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 943276717 1250 943275467 943275623
    0x108010e01091e210306030b0c07030e0906041e06080c1509041503020603251b061508071508010608010608040b060f040e1b0a0b07 58
    0x140450090700003c4180406450911010410030980030031904010007030051154502d01054010301c0b02856203000580720310390304182d0300c0880c00502060b220700c82001500e0000342c0091440b6030039401500e65080c0c640e54140402e000707051004110103181c0b00d4400c546074100150f0007560603590170300165420181c8a006000d00008200301d03078181d004d800c0c0b02030822400c250f8401001d0003404540c1c0c1c11305690f26008a6183c1c2d0096a62607004141c1120b80c5840c080d481c04032000750200e505c2c1c000c1d0b81080702000e190450710011401013105440b20080819440304040304800b0b090142d0950340c4c1e041e6600d0342491503009408841e0080758080b000050503d021f404680c0c12100617841c2c1030410703a1a95211952000c004150541c40001460590000d4545214401a5080d59801883c00061041c025803901a4211080744211100182449210051010f440c102540690380703004514035024001e03000d44580052a40b0207001300386030848000c2c0e28128910444c6040e0009001c61100741c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 943277967 1250 943276717 943276721
    0x6180911031603020f01230c01090c06021608031602010509040204050432070f03020d0f050c0c010b030703020d0209070c020316061227051f090210020f0a060507110111030108010e01 80
    0xa03800e452247c2ca4220400000000038005082c02ca10010002801c01a517076200d11105070b1035000740005030b000c000e40010304200040c1c8031024001901c0114200102152415001000c2c800000d0402c0700c04907200d249912603406480c0030702030080082c080c40752003840e0307080341c2680c801c0021540011140030050004a5884190050020b90b45030345403403002080c1a00a54050058417440b195111000d1f2904441d51288034000c01c2001c0c10f8650300d10000c13011a0079200c3c5d58100e60312a030031004003040160b90ba04110358409605481e10300f42991240341c280c41040500c54065014050041c01c0e10680b404d59410030242c5a8a44030603410408052410302201c01a4138240d02c40078400c200c0c19a610700e0182d280580c00d04c0350003141c40c060078100c850311042c000c2c000c20021081d00c03010044210302e031000c818075002c1c0c1d4620051078850880802e140e03407070648242c05808540c1e41c40108000610a42090f001110000003d10882182c1e900c2002c1c1d591092040710400d5180c030b11982900380040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 943279217 1250 943277967 943277987
    0x21003150b030414150610020616030917040b090112050702210409180303051609090209060c190309050d050307150e0a0308040c0906180911031603020f01 68
    0x16041041c100008036030305510280080c1c0f0000655001005a41010407007402c0c0003020024408240c00c140d401d003c5a1481c0144420035508281d08001c8554458410700070070104518011440c22664282041c03a5440d114401c50303149400500490038040b00802012400307800c0c2e0312141c440044441c180110344081c0c1302c0f8401a007150110f00880c18044c40c8070411072040d00000780c64140c0c0d8080140481d41c0316035810903009040c0c1849003e154051141560005090400386003c6801c01c00042080c516400303604209540424040320750f480d40c2c015201c0300580b07a01110184014042c10141018500608a0000b81000c902095a00344044d00d030540680c0980154140380c41c070355900c12801c0036091b40000b0180d179000c00e00e40b01c81081002c495041d00988401541d03041500380403c000301c03544c0003c807009040001c10405d0f0340307009100e05030200900c83c00040141d003e140040f40d540f000024164944243e80c0d1201050305981c40a07001c4034401c9030103568141d154001503414080ea = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 943280467 1250 943279217 943279241
    0x12080901080a451415070918020d050708040210031a0609040e03030f040c05010f0c08090a0902030a06050a0e090705220f06050405150307060f2a021003 67
    0x340c401c660340915001e208900c40807400c3d103810002915031000c2c2c00f9030790100c1000d484080b2005080d40041d0403d00c48540040c8400710300118034645008007400e4a8030320322030f03282030400c20508550510f800303505407071540c05503410510490034131400040c0680000e13078003030b80300c1d4181c4000c2d0401c06000e0f00c10342c160080e80c504200b0000d102e623003c00505421071603003203801ca902c2e0581c11281c441305000840c81000106c0a2451178102821f1100b014041504028140106602d01020f442d400c042440703c41382d0b0140045a44100c00c20100c0d4801015900010b00341d4008021303c6a9600990840c1c000d03104240c2d155001c05550f034604801c2c512094070300160300e0700910001c0c8860705112444000352282c4003414004140115aa00100c0d000c2c00050754085686070814012403401d8040c5940240c1212811101f5a0841c800642c42d01d0071f901c00c00c41400050b0208400346030144601c8050005004d502500002c4e407004c0c481007844003441d04a2207034900954100240780240704040403414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 943281717 1250 943280467 943280501
    0x51e09040b040b1e0604030f0303090b0907120803041a01031202121c090311030d02040f140315150d0b0a1118220509010b030712081c0612080901080a 66
    0x101a12100c204c01900118080d0480c0040202101284a50201100880c429540090b804505040c001948500588500340c59001441c00b0000041d080301d2a01c0c006e0340103803070250342c0e440d50b1410a441c070b0919540304030846080d000000c1805201c018540309001c682e0261000c407084c0c9560306202e84241c40092180400304541820300145951100203134a00c2030a081c2c2c0d24102c1c0d81c07089461504041c2c100300002ea00002c042c0041d031940c1000b80c2c020484503000030000c18449000039225403403804004040d206800000e6641d840001451410b4007004d042d21178031a03503d0400d080701044c2243c1d02c6403042e0800048501b2044490304940058004c0d241d0481c101e26444104001880352040c0b032000d4a0b00c0212907007034807417a8410301740290703100c01c0001642c0901c00245400c01c03032194424014161011f0f403104c00305084000329160030035080020a00c4440000900000b40395030b4115900c02040040c14204000b9050010301c0018808d032a40d84090382c4000360303403003074441c0d00c0d0030800a06 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 943282967 1250 943281717 943281739
    0x905150603070611190303060b040e040501140f04060b01090b0a09170303040314070302010b09010b030f010605031909080f0c03030a0513031b03030b04150e090c01021903051e09040b040b 82
    0x20013142009003480781b00c4c0c500032a110742e4940340322100f508280c1055002d80c1044050000300203092041840101200b0310314002854002c03840c82e003e2200a001501554485441e144107030301c80d40440c1c0241c150300c1c017126120000180300408100d914010707006490110603420880c030f0000000e132889180d0556404c00d040c80000c07458007180d04411070480941d900e5040e0b480b8039075109610540070b0043d0340c00c1c0d00d4803881e08405506251030103034080030074003504200b0b01c03089804189409865821041012840024034540341449129800300c43d11101c001141c8151400d5000c4000c602a203d80c1d09c041c040341e2a1007005070310062241c1d074000c021601ca02101001d1500c2203e111000c0f40c002d0030001442171049004c00d044e16075011010200d04501e0000b8091100e20220480c0c00444042c02003400302c0741540040d654888204ca11800c4445900d58002003500c681c0480c0c40c141c43c50390321490300072007a12034001240c1050150038466400c0154003080f07404d10748589004028000d015500c0d038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 943284217 1250 943282967 943282993
    0x615031113020d0207030c03080a0c0504090b060d05040b070f09052407140303010510030e0604060b0d1401060f1d0f0601174002040b040905150603070611 68
    0x518500d00c51940341d50240800a540b03d11803028003522806619078900e000c0141c54000e28141000341501031162900e400700f020301d5440070580c1c0c240c0300d811000162540c6494005a050700487c070055842c2400c080170042007000d5580300038015170940c0c55200341c08006071002c1d1030f5540c2c0da0103030a4104041255020315001550100c03501e400320034aa0b18030b01705140c0c0b2403414660240e0f00068640c1d02c0000100070508101079006440310032441d04101c0d800174400d041d0b80300d5001802c05821030341c442040082c142e54240800c4007032503100032849001450502002d001e0021882441000d10541400090030042a072980032a1405218090020344d11405003000720200500f07240e04201040003440d07010080f80f200b40d8092245030710b400681603009201080100c2a801d811070380d22002c83d090540d2022444008160360f94100d60104020740c0c940d0208008041103c406800c40c444d240060102018101e5114080d600a5041d105140d03201e036010744ea050081501610300ba07010351045605 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 943285467 1250 943284217 943284229
    0xf0615110a0b040218040507150c05100b19030c030c1403100e0c030706090504050711070308090607020907030506090a0e0c15040e07020304091415010e0f0406080a06150311 76
    0x100c548020704140703121704c0020303080c681c01c5412501141c3c40d6100000500c07040c4940c1d0480003215005241c891500348a03070f611240c5a40101655480c03c5880380500c01081d40e40340781186042046001826516a0b28101240408100e00c810f4950420212000c10355441400702010341040190040c02d1802020024000400c40b52031f200f0b4203030140c0400340700d00d42d0303003404440000c100598a41c0816410310040000301d5401910210071b00c0b22804031411095004160703c02285d402c548403988500308100411800d10441d00d00a501c18540803c110000381c06901c1140100800c1d680308031070703598a07180007089452188a464541d48820000040d5140100780c01c4103007803941074042d081555412301420114000d40d540d00250700045410700c0060058802d48055619a00102c2c4141c00c00410500c0310383c3c410a03003641001100284020b007030700c610450950000700a0320401c1406c2e03980d4400c1e0340f04c0407805022502e00781818040c202a0000c0b070003410580e508100b261028400003020050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 943286717 1250 943285467 943285471
    0x4060503130c09020c03040608090312073504030e1801140d050a120210090b01090903030b0d0c0f090908030c0a020708070e0402040507081005100c060f0615110a0b 72
    0xb04841400404250410340b030010b00303803480407140259101c0d414004041c000d660024070303100243d80144240300307240254100c0550020f003d418808447c0390745038001e4907015141c02d0702d0b035541100e15500c410ba070301071054480d200c0d50282c2c0d80c1403030b415241010407a0400300a00c42c4c0c160b022203400144510900d4980c01600201c00412101140e01da6070b540c281011550701d800d0740c12085400e89900842d40600c240059400d144904000120160b90342005502040c028140c625503543c4503e81014000c0d40010350043d00100307060100505860541c068814074000e203400c0b000061000110b50344103014100042c2d0344010715900350380d101c0f680d0010076003100b080135003144101200022040f0040c094107000d0302c0ca44820306120303c0c3c5401407100f51600900003c0c1088142c50802c078012480035208070942e442101c06100b0b9181e10b00044a80b85600c5d0740291000d403420356a00144d85917a07012004a410400000400e15170300002034440c0411070003070b03803a590009a0313030800007038130010180c1e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 943287967 1250 943286717 943286723
    0x2060610030509150a0e120f0a0804081b06060f06040609140f1f021204060c1103030409111b070e010e0a091502030709080708070320041e050c0406050313 68
    0x6061800b62580304003130020152107910300035030b4580c0110340c44c10092001500310114040120700e40301903002c0e01441d520403a8954410080e000700441c0030041c1490444444000056002c0000c840c0039a486441d00e105139109441003219454000d0715081003000e4800311030780c1d03032180c400f05480c4c034482c0d20241c0440e44d04650b00c509130380e0907030191f41d5035250045900c00902140943d04642040068038000180420440300c480600041103200ea1010100c80c03600c0c1c2c03003c100800f5143e0794001c82c2c5907000325003003142018100030f80c1101445a410141568420403208054800b803142d0b00e560700d5020714060704100c040440014042d4044202103e40c04c0448003800151030396040e1246028202040000c2a900790000f0074024400d82c0301e03c15001910161f405861402d15001c13401c1e960b01a80d1000402c0308100149801004000344280724003844050310034400e164020380303900200c0c4002c1c5c070b913071000034540030206511908120948003943e219495a61441d204d40200c505116200a021 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 943289217 1250 943287967 943287973
    0x91a0a030b03280b0112080a11011407030b15030f0609100b0d240501051b0106051008090d0512040807060e0703061d0319031508030c0d0e0102060610030509 69
    0x741d2001d03640d04044426041500c1044001510f80d494802c07010310060340610254071510801a021a1031401100d603260580c1c203003000c0680101038864054100c00c0203407510701c032000f0204400700350550448003414104440c01c040040342c80c01c0501041c00b00340c1e503c1c81c01d251110005203640c1040740505420046100400c1410340d9a01103400c202e911481c1000e4106840700e54504d1904000c2002250a0110301c40300c9440c2400c05000030802c3c003130014150902c9050022000907481e0039801100074040c05009581030416180018250b00b0003540c41c0710040c800c1c1130320402c1c51446000ae039528101c01c01c8041d003042c1c0b21038880d50301d1900103e90503282186d507a0404080610108242d03070040d44155404070343c1c204c001032000b075016131144c440810340d04100f100050074040300c90800424807040c2000a0000c119042e11207208141d0b4200c01d4181c840082e100c541d1180000384244203282650310082030007140340c012a11154203850341c45d0801075807103461891038001d4001c564409090411 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 943290467 1250 943289217 943289233
    0x2a18040e03040311151c0528050c160c081603110f0103470112020d090b010b0306032b0c1e0f110103020403080d0e030d020706020a091a0a030b03 64
    0x441d05660380300070764807841c81c401030004550042c1c49008481d40042d003923400d643ea54619a462000b03403030b201c101c0c440322282d4400000300e003400c815045d00c42c0751403043d500c1c40c2740c402549800c10812040740199206c40c410f4103110f1001d9158003201e0400e40c0c4c1e101c540c170f01807000780300309203e4109086408135052603213441c04148040c40c9030544c100b03514951150100c103007a4045850000300303400c0400d80c80e603030103214150384030b41d070040c0c5903000309500c0c000c006071307105c00603010b041c010040100c004007420b260f240000340803000c40015600039201102540c084001200f80c00c81c840d400410f50000040d0041d83d810402d40c01503000f4010341d40925a698000c4506042c4c1010030389800d28112040224082d040d418441655201200d000c400c0c2003c40c5018199103c0c400a0700540013025022030b10f0702c3c01032a250303d00380141c640b4420001030640d11610580381c028081d400a201380c000060019000150000e00e407000c4443e5280e03400041403900390061000c50241c008130302c02c10740520071800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 943291717 1250 943290467 943290499
    0x60506011b03020a0309060f022802030d020303190501050a06030e07030c080304060908010606020a020d1e030801050909071a090a120308090f070302060a05032a18040e03040311 78
    0x44805805129078050034802c645441d000e450001190001000c10944518046510390001a0140cac1058018941841c03000c10ac420180344064081c802074141c010203901c1c0a895030000082e5000f0b01d0702e40d00b10031584031252050011a1024407905034442500001001114060b910201141c104d40d401e850a81d07442c0e841c1e04900144a5000100756440002c0c10484284e0140300303000940f000400030321000d440c040000355101d21200000e4130402d0300300e00200401003004822146c4800d200904200c0b01030a04000d480c0d800309220b114020075001000480c80400461603030181d030404c0c5c0f00c00c170240315032354020381d103540140e21403a811110703005011410034052101900c20510907621800035240104400b401e094101c2c280b29541d071700480040c00180e4600003910840121803030001d40325520b1902c40482c41404d01d010040800003001180003100d011401000d4021a80303a0210317400248070184001c031004000101c1360b5400c01e000600000f600d202920a8050300203000040440d1100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 943292967 1250 943291717 943291757
    0x1a0d081b0d210b03070806070f030b0d140709050a0618050402181009050c0702040b011b031409040c030b091501140c07080f060a27032d05070c1a0706050601 69
    0xe00325030b0040e442107003002001e650068940e49d10100620b02400710103001030200d2072560014200a09000801c16180c84c0c24508008101c014065010306008a0401100c518000c00b12401111003480c0d809085002c01c00d100d004e05c034061030703001c0c202503202110324410f83c40d4000c01410510315960030902c00258602240100341c010440b40400d5507841d4231500c10081107070140107800e410f00152070821040414440580b0448542508201032054040b11100e43c4611445440c0713503007d441e2041014005038590f01a28000c0000d0310018403d03210380b412408546001401c403070000f08001c040381c1400e180b81c0c02415442640c0e00032500c200317850708051428500e0720b1000b500355a0188040040040c128083e02010012101c8005460b40a98915041c80d0304944400b5050000580c141da407504610360076403040071300302607407159807010400c402070207980200c0d820384600141d500d0110764214640d620742c840300c2d01c5104040c5000200e69440300545002800743c1d0511101c1242c0041200c401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 943294217 1250 943292967 943292969
    0x1120609060905012c0112150612050106140a061101060905070809070906061e11030a020115050a3206070c06030c08070801091a0d081b0d210b0307 65
    0x68000402d0382c0d030500720020b84042c007508100003010305c0424290411004c641d105410f403040310401e10350b00d580700c1c02c0858940e44901d40114450349005400243d10b45404910841c0d14400e00c004e1000c81d07654051780c4481d0041c0d00881c0e0384110101010000c4500078912190340164250000c110b1a94426924080382e004440c903601055070202080000d1205010050180c0035800c000c00805051400c0100354900016403601c00450340499010254002c07440c2c50301407151102100c0d5140c0c80c44500901030302861506030f014105003000860a0318203054100300342d03851601c0c04c2c0ea49000c05002c541094840c0c00400c40c0740451000c1c0e51074252a17907130080c109a4010500c1d04020b038601040142101c00200c40d1004001c8181c05012801790700c042450304590b207031040030643d1034041c104000403110103001a54800341c00c00440c000c01c03a100010388140b81481400b0061104465200754035071442141190002c1c141c24419070f0480703450340e07203202d40381d40382d0900041c01c42c401c030082843c0c111070b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 943295467 1250 943294217 943294229
    0x1106160e04140f070215040305090103050414010504110301140103260d0e240f010e150301021b0706050403170a09080a060e06150319020414240d030503060112060906 73
    0xb00f50104944650100300d0340070026108500f10805142503207000b03000d4000d54180c02c0c10503407a00086028400ca070009150002c044030001c1106c0e0416181c10900e200050151324065400c00350300307803100c4840c0c0c42c0460481c0e0700b00a0102100c04c4492511440c0d41041c504802c41e810f080c8450038020b850b81c4a018880030741c81005084c2201898000d440da8070f400703034103250107080b101d0802819001000340181110340d0401141d0300c54461121410300a456520000d0301036102096000c010720b200014208454865003c4e40c1205803241b008513200d01c9a408082c040540c4450889d003200c20910050900180314070302140380503110300050741003001d107200548100392500e181d600c1440041c0503140d000680105a544115031900209803950f804201461010300f11001700021b644807500320071448004140c2007001407134928a0742d1a0340b442801000168504121402c1143c240600c500100c10f4041d2125800d5980328801140e843c0c00c01c08441902c0d82d12250001280340c20782c0142c40103005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 943296717 1250 943295467 943295491
    0x1a0903070606170d0c060b1903020913120c02010201090803010e0a0615020c01110c18041104140a180602040906060815090403050d060f030609031106160e0414 70
    0x240781801000c0e02e00b0758102c02401c41036000f540801e40c40c0090071404100460410085130186801c0c5240185601c521581d00461164000d0b4149a0076480c1d86042c2e0303100b114008200e480d0400d9030320741c5903107140c0001c006074100240520810b000303004400019205100100715002c680e030300c042440c2c20030f0b400703452a400c0000c1030049204e02c5008450142c204a07429000c0100658402556404c4070f070a0103051101c00c01c03140d50b0900d001e2100d0507074003070068414056030f1442d0b001c040b960030701150183c4544411050000d141d03d00b500850710001c1e6000c0d9111403e80701d03008920014510208192510a00b290040f8001055800640001c05103034000107821860820094103540e002000814002041c416004c1e4694543e142c40d40c00c9074040c030b81943c5425500d850a4014516074105040300b0440c003030000100034044d04102c480358840d0781c4480c880c1141481e8196a8a030640780c0000d0340c1c408051042400b84114040145644002c20205a4000100101d40301100a0303d22441d015 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 943297967 1250 943296717 943296727
    0xd140906060d23070f0617100501050702090a0e0a061a19090b0d080c010c090909020901054b0901030305090409060204050310051503030c03040504091a0903 69
    0x1101404026404142620700c0c2d4011002641c868240060950300361040f034210f8111000c07543c004022850180c0003d40440341c003192513071000341101c500c245108040340491000101d1b040b1481c02e5480844506842d16400c0c5a240c0c0d00b0440c0c00c140051800c2400ea03518413088601038800c100d84550f00c1d016804c00299103000d16240c50b00301a204021901038800c1e54a00741d030b003c80260b04d07142100e04400c0b00142c554a803d0008160172555800645040c802080d40304c804181980802c5850055031523203a0310356601c2e100002510a059400303907000301c24400400c03590918018148013214280c403448000030b11074071110060030791984805550124007280b241c1c5e6004111818100710000c89103481158555640105a44510140c0c54001d41d1920340480130450a601910003906005050720b020192080d100c00c0180b0040300c0080702e680600072003017814180402150220b46503100031714501803d0500b440003500b4224011105501350309580002c2d011f2080c2114065240040035680d98 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 943299217 1250 943297967 943297981
    0x4060c0305270a06030902130b01020703052a100c15061a030105091e2e03060f0615050f07080c0d0809060a021303020f1306080a15020f0702150d14 65
    0x4043c10713004202030519095a08000d641e451022844d000c025000104010581d00c00417030800040703500090a030322807462018404d44400b0100e03100700700c00000e00110a00c44a0401c056684140c0142d0045582441010042004840d480118541d084004146642c2c0d8a04403420061403021103504000040010302040c54400070031a0020070034480300c070b200c1c4410b804da0b41c410003002d0010a8660320a880c0d6900342c01ca2940c01c8151202c03901c140304021962400c0a00103400c0c0360502401c81442c181000c10303c0c0d120f5001c0c40d90348460580d1810f0522000d101440c00580c070510040e94401030074008508225030801050030a40141c2d56100d40b81e04060400070f1500d20054445072185005010b900041000a0409030850380c04503040022510403001043c651240300703a44c0e803074082c00d1900c00710300f07520b00145508904e403003240c80c2d06401c20300550050481c05007585242c1c2001d020071080300036240510303d11043c4c5041d00346440c80d112002c1001e404840e414140e090021640070100109 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 943300467 1250 943299217 943299229
    0x1020408070b04140904050a0b1e1305030d0e100905150a02031303051c1b0e01050315040908250c0b1303060f0f0e0c041b020304060c030527 62
    0xc0820b119641d09250400403045080714500308141e000d01d11460018003071100c100403620a158102082c1d4026052181c4010008844d003642200769150b03103000700e0300d1086102c25003520342c0d40000165007441d416000c440b0151580100210702da126200e0031404808a5100d044d020504c44c200915082d00e0300070b0100388071a0001e00c4140c0e034074414010414220000720054031804d601d89003036a551038140003c9a851130410070103004a920303103080c003c01c518400e07260080a003156101c442c1302004c407400468262000315007a50229000ca10361140e0741c14035070030102e1010310a00c01d482c00c003030003600c1107080394100200152408074124040780900042c10521000f03070140c0e00d009498035000141c2c100e04a000744c0300060002e561141a03010040c1c45078072641c030080c1d0340001881000d269001d03240da180748030080c5134445e074604081d041c40e034035255000d40c000b400b60750080d501b02460304409070303103200036104150301384041006150100300404011540e6040800c01544850a0b00414485 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 943301717 1250 943300467 943300469
    0x606031317030403032702010318140106080f0a020625052b03060e070e0609040c05091008010602070b0c01021c1d07050f090604200703030c0906050706020a090b0406020102040807 79
    0x464800c21040300080d10a00c3c014600c0741502820042b411408600010500600030040035003a1640102442c43d0200190007003400c0714601c4d000c5801059417030400325103d0000c00c03030096204800708440c020000510350349400b06241d030024440c5402268540a00b0080703000c3d00c4003000c1a81d40101709d06100d0031032039629002c945140c01c000d030743e0030318103091000d0201400000620812140c5a003456581030100c0c1c118002c050418808003041c5900500141c204c20084d0307105481c4000003032072540c4250001d43c120344041c0e00401d4130b28a0601d240000798000d4012001e01d540070828042801107041c61201340c8200c41710001500308440016144040000c940c0601d83e80011404005554517800c080301018412503908403961201000513009000311110350b48103551881d6012240311002001c1c10009010b52420302000240040440d6941140e00076800070400c18800803022580d140d002d0300340b06c80e460030a50702c00c1e5210300152880341c000c3e5000100503900060180524601408458 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 943302967 1250 943301717 943301741
    0x1060503010e07050c0c03070f03060b04091e17070b06130507020705060c0c0306040305270a0e0c1e0307170c0304140304180605040506011106060603131703040303 72
    0x2a04650405062a0b04014003800300820031a0110b94820307100780900c901014010002c08490b0034035a240340050450456200644600d8604400528941031900564081a030f11000b00c82c0500c16201005400c0f0f9a4140107940840c850f049101000c2c0c1c0c250010007085000e4803002915142075410410346020050360035071102d003000203001306103800013180030030b84004658298841200e00c829901d0007002000380f0354103100398024030080c55005801054400d00c090b0217600328110340e030f512410300010040703840d400200b080303410003401071030b125441e4016028441c69450a21000c0d61071a030704038424040310b08004000244a030840d004101e07000404914080744520340390001c224502c03400001d0015000350207d00b1130728580002072084034050060400300d41050f506410101008100034029030703004901c0c210100348198000c1c500310550700d968400402c100c2d55600300b8426941c01c082c10311440c1103204103000000a00c40058100d401406840355500e130310b1316090003426203044030a56 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 943304217 1250 943302967 943302977
    0x60609070329120a0c0510020d050d020d060312020609010b1e1018180c0306380a020f0c15071202190807021e0604050f030a12170106 59
    0x1d402d030540344910358401c12180d0000c00805600c1c4030106100340c030440c1001c1d20034040e4072910410408003201441c1aa03509560021404a209900360f036289082c90f41c550109034144040c211044030340c0c00400c058070141001050407030742e0395660503421141c50810740150b0840420058090002d20403c260801e04503042d04480001e51400c2281170b6452401c20f001c2c540d0103002060117030040b4004580d010381000c400c01150b9440842c0141800c4680030314458509058000c01c1c1d05d8400d00a01d01a585200c070031440d140030118030001962201111181004044415240c1c0b140307210703024001c038506c1070b005080c2c0f618485000909000844c10014407400496612500c410380300400d894030316500007194507401070041c40507881c0c0001841d02c803201110724600042000a84406421814420380700006064541001c20080e600307607910064000c0f100b84004c01c0341d4640004513018082d0003500f030380c010300003a40751038030700c08056254000850311079540d000ca425800c252650040909141c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 943305467 1250 943304217 943304231
    0x90b0d0f0521030c1222030c1a1006030b191206050a0204030f0b07051612020d030506030d0309030e0405010f0312080411010806041401090e0d020307050c1c0807050606090703 77
    0x2004ca502d00940481084c00d01040700000d1074403018560300c1210641d07150304540341500601d00100003503104581241c8210094a603a1908040c02000c0c50085003647d402c3d84ea41070a25808800030200001c2081c0c0c4851001d001c1000c8040f4044164003820701844007407940f011500300074054032400ba0424020900c10031041020412489007080b20a0f441051090b0986171190100c0b0b103406090750088a4000c440b640030104003414004084800068098444140380c0940a408941c411102180c044d008801e0103ca814800d50060031300610a04040e0010400d0002050494500742c0000481000701001407081c040078980c000404181032030034104924069440e8015400e1703090301e140c140194031000c10a555620742100104526207152fa402546e0743e1038544c4003420040301344003030a0062900983d0a44d202004079a0342c0364200c0001c1001c1d19100c0240704c0140c095403c40101030740300001074000104060024010035019200426071411f1610401003440e80142207030040c9854042 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 943306717 1250 943305467 943305481
    0x30c0b0c0309070b091507020d0b01141315140103020f1206030111130b07170a030b04050106020d0e09040c17070311010c0222020c0a0b10080a0309090b0d0f052103 72
    0x4031101b0802d001105540c5401841c4042a545000c2d0040204140d01180020a82101c04c81c0208000c0b241120285e104880e40400358089961003424000c10156029041c0300d90030106800710140401850014034042074030701500803942250400c0340da00d00b050f9080c09161303d024058140101e80c039030041d41c40c1201d041b012100a050700d21455001c07038008112442449052241170340e8401c01408442e43d80c001d650f100400415008000920444ca40400420510302c0083c1040054402c0d03240ca5101d10301081c10019075000090040713401031340e0f074100460031034020f8003100d4640c0c1b60b8a00a00703c3e181103213048817080c0b15032550103040012030584080941d88004100350011440c40c00c0c0030200f010981c81c00081d100e40c020440c0c282c45034117915000c000709541c800e40b0502c0b00e0b02c104001c05440b064202d48411320071802400050038520184880b200d00d6021048400c002040c2209982c650b0b980c1c0840240000c0c02500c3d0b81d0000d56034209542c2c000e810300c2c00b0514013051550b1452034016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 943307967 1250 943306717 943306729
    0x61f06051b0a06060801020a1103040f09270c150201050709060f020109061503051c0f0503100e0c2a070b07020102070b0c2805060403030504030c0b0c0309070b09 71
    0x9048118111004560384020074818000d01803015041141440800e0300d0701c00d4203010f580024840c1002906800207050038800200035102903905580b00400c64074600420308003d403c81c405051988018120540c840311016a07203400c0b07051144c0e00c4210344270b24121104040071400d80700c58007564141003c00c0103160317102c40800c060340c485040c403203901e131003d001c1240100030320000107280038907185840d076500e4030b20010315003160311440882d241150300501d499140c03104044000003040e164070f41890124025409154050402d89500c0c2c4070564171902100e40e05d405a5000d420f4550010300392059021403440e12003101c0c0403200b01c0c001480c07105c0c001c070741c0c50009100301103504034042006811a0310a1000c8230003002d40421868955421800c4552141d4a03d84840d0038142c407401c010794120346c600c104200194000004e40540d40d6507071426006042c000300210300f0024020b41d50720018419030344160060301864026034691800f074821520b0801c05410840329410184808100b96848d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 943309217 1250 943307967 943307977
    0x90b0a06050109052e120b011d0103111e0a0305060d020f011202090603160305070f080c0a03140403020d0917070b0a0e180a1107020d111f02061f0605 66
    0x1da4000d1240c0d245e0f80300045661a4409044884c1c0d0a8404600411548055403001103c1881e00070000d11480300010344d41d07100da0300904210300254000b000b00a60196001e41541d03101e92420502e00390001400b502101a400f20020040303c0203c0c07229031555251142a52240c01030ba0344d518582d00a40014549541104050b41001001100c0414050a54049d503940700070160455840e0304003032210740140c8600f6489940000c1c03030140042d000600c43c0c0c1051140300401e803241695619164964010b941c40410031f901403540b0780542601007420024110b204500030b5000e003240c1c00b14000000c21141c10b6074401000d00c0ca406d821684c0200001c0794075001c07502c043d0743d495a0b40080e440140c400406038061035a021010b49548a140030341c80c0c604501c29801c0c0f07070041141c5d0819000c9041d6501032190040d4006412041c031a00007004103249003404003005100d2070300602c1240c40c4210a45030040b02500581002060003800d004642c1101000d81c2030507640d01c2d856080c13074001040c80c050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 943310467 1250 943309217 943309219
    0xa02181f032019020c030f07030b0c09090403030c1407080c1023061c14061b04092409090204270215090303040e060306060a0602071211030709090b0a0605010905 71
    0x5180c030003d00d0301e802003000902c810800b9090f43c4881c00742200c0d0503214200c901c019951080608001821710300d941d011a122084010650081c54650340c8089005010765140407062281d083d4200030301c42c0c1000c01500c2850300c00e0751080d948001c0b010b03a07607003410b13000708407215000c1c1440e584410b8200350150780a138000444480200302d0760f03501c0c000740c40c050040c1200c4000c810380c521700078180702d0007040100d090140642220056100e5195050201c0d00d5000c10300d0f00781c4c405102c280b0108440c1c0d085445190f40c601202d12035800d44019103011031840d64015040240e5503440e00b01142050701400d81005500041600300b0a40c8400089180c0410000244203d000200200cac0705c0e116001030b40e110300e80140031a0745136512000b0380440c10b0f8064034150722030f126000000d200c52034961035240943d15140d002c1c01e0404d10340005500c0648213840c044504500c10940101651400c0090800405e5542c038042844500c038204020600006030414002d1410300200b4012660044040d004a0f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 943311717 1250 943310467 943310497
    0x90f0e1e19080412320703033b030c0105030613050606040b03040506061809152a030f061212030c09031501060f09030b0a02181f0320 59
    0x125450800c03010720680d08000d00540d031160b03107041440b5800142940348940440b1802c1d038464060884140c00b2584140d1020f254090381c2c1c02c1c40024460070303d2080c0e0062524527622042400d801c03100000c4200721400c1c081e0903151011006903d0200840501c10710b0a081007461030510304003282e030100381500e103c00c41940700d81c0401c01c59100c2748201c0d80240315040c0015101d041610b00395444440a641f100d03c00c054040d0300b0300170f2210031585030f4060388103540100700f0389050001240f82000004d04520300d4a0002010020040c0805a03481d803441070342504ca5a64a80050390204810f03011704841d01a0f15010203802c03081600066507140803100c1040c0316101c1e9501200c2c8a854800c40742e02d5600350152804041c00000b501703003903a060354040d840c0d18100e41014202160800c0071803001801ca11140300124514400c25801000701e044e921244900300130302e86012030165035440c8500704072440e206080200d0a503041c0308004407240580d084111146002400c0c0301640220150380002c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 943312967 1250 943311717 943311763
    0x1b08075111280f110a0b040b0703030b01030605150c0118150b061c02031b03160e030a020907020f19020f06030601030603050601062a030903030507060204090f0e1e 72
    0xc02c070204180c2c41e490303120081c099010940e10700310b0300d208514070420f03005500159003c586d0312078450960f403d480259624030309060423038600728043c03d01c5200d40e605151b0b58850114554560800c01840703c0b400c8588182d4400d040c0e5406401c48000400303903c40510403084c03c400145034071000540c0710012486c08201e1007400400500309202d00354602403038400c08030640002207015005180304040100d41860f810094650400301448120755404c515058001600d9242c0c1c0603003054104403c0145c12204210113990200700c000c00240e030907801607400301d02c0501f61400104480201d2645194a4040d00c0c505076021640b0501051401841144c8c04000070b515030348a80d01480056410108445855070b6803c0e000e400c11080402144090380502c5640190752402d19601c0a00355259490030482071858400300d8207a08401011100c9035001c1000240c284514051000481c0340510005605952101101e1600008062100c05a501c81070340490030a00454442d00071000000c080302c00c1c0b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 943314217 1250 943312967 943313023
    0x105070509011d0916081e06191703041502070803030a111c020c0d0503010b0a0305060303070b090d110d0e0f0303130906031b08075111 60
    0x410551824284c22403165400c1001c5002002450328041c101c03511030301860b880d5051800c4040c85c410b00213600c034000120120340c89040a41310a194070807502039503002c054071607000703401004142c0b442c42c50316070004c01c003031100f028081c420010560072400100f0340c0f24900301d501503e03404000d080311401562400700304c0c0b140002208843c4415500040941030b0030070100d0000003074010f182c04042c00d20401c0075102c566802001140e040e902c3da43c03d080d0070706030100c0c000ca000d0304005180340d42501051084070001015405074a00800483d8040d007140301c00b080b0004c242c0007034801565a10340c0300301b028140300d503042f2001c00800310054031024551091b88001c82d196210f4559545800e0f00041d00020b003d004961000e01502e2040c0c620505241554101054041031400b442d98143c000360030812942001054010004540b0034203d00d0030303041c8101050f5090803e600c140200c0010380e071210045041c40e20100c6209107141025a000c1c089200c840b0742d5003500070000305c4e01d900d82032080021 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 943315467 1250 943314217 943314257
    0xf030b0d02030307060603120e06042d2408060622050d14010605010f08010b0a120603060504030e0a0609120c090618060506041203200102030c120108010507050901 72
    0x540c0e8000c0c04a0b5540c2c901e5141a01c005c0c02030788400d45064504e0159103040e144175581955540744c004010341c3c1058100842c00c3d55a1951181c0e541c10042884001344020304c2c800e81480040000f18031352a022104510443c4400070403482c0102013068803004c2040d00d58808003521341403400b03040980c2e1107440d4110001d120100f1600115800000d40309024204891203040b00c90380721800c8001d1101684c0c40e001901d800b0200b441e8803004c143d0300c50060042041e500003038042d1030b4041c50402c40c07000c007650580003260102c1c0c0003940c0c1d458031502000203040d0800140c48980e0803c5d2140c80105150400040115681d8052441580c40c1000ca840c14420803d800c01e0180c9201d16041240540e1501c003a149804040310b0803d48506206000419182010a0380e0444840c48182c40f15204641c0d400c94200548100241d0b2190b0842070002d04040240f014500c00c000250410380d6a8440340d0742d000e940780c0305a010040d1a0b044c401044812a401401c2e900b8069003801c100748852082080009 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 943316717 1250 943315467 943315489
    0x30b0a0e010f0e0f0c210307060c030f050f011401050c0a0602160218010b04090c050c0d0e280b30160e030c101206090203060a0e070f030b 61
    0x14056080c002c1480d585441d6520044041212104640104040460b02512402c000000650040340300e0340b5110104071800115600e00042c0c0262841d00013035030b42d09002c98000c1403082d00000e9980c0c841040d030348154407842c1e8100701003003040c80e465803414000704203001844541038100603000c201c1d1091300408200108603554864006d540700c0d910004282e1014140c90f601313034860040c8c0c0312200182c0b925402902d040e0307000c40780107615090820300941c0c0a440880d07007100810104005032003d140b001e014001c9102499520b5911821010003084688182c40400300000342d1254401240c0e075030200e040c203003101c090844560300d5000a8248000040682860200e501c828454100340003c811600351310a40c0c03101c400c6d00a10022003012a041440c07500c80e550558032910b50300c106c42c41c00c15040000103103d0316144c10070464021014058884541c00340046a401006000c002d10b08070745104050301c00805c0c4030382c1624014400610b6140000545428035644a031040d40c240c8030944401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 943317967 1250 943316717 943316741
    0xb07020d2402072619030b061c1b020d0504030605130b040f021009030f030e1f23030601020618330609062103040f030c030b0c090604030b0a 62
    0x15100c000d1400c4c88018544026500d81541680e0f60031309a12425540c1514420301c0b08801c2c0032a078210711803094000304052128640d102d4820302541c00c804498040400401d92408004034004001c544801c1540503e4040302c1d081d904110090504c83d0f5200050700d040f260082004a01c40d02c50510803009100161400f9040600c41c01c01c110a1101455103804000e1003a640c440070348260340360032583e402d00780c04010140800b050041001c6445008203a01c0b01c00c0c003d10300c4100012910342c41e910002d415400e000895152608940001d203040098104141e0101e03a407450361a02800003074a800009000f40105607019108041d052810001c8400410f0504008425801040c850020805580d542043c3d90698900050386504140ba086c0d8019800507002d4880c0318108810989101d40855420100d4801440300007400841c034010400294000c0000290003419801c00a92404000388400f690000800c480d02860300c420040b41c0407a07030041036a02a80c2c444002400103851204402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 943319217 1250 943317967 943317971
    0x81b1207080a0b07081e0603010b0a06030b090c0c12030403030b09011413110315032a090a1401090b010e0a090b040e0f03030f070c050718060b07020d24 67
    0x108aa11000034200310312030088082d4895984c40300c208071038001c0c049414030001d04041c2d4284d107604819000746a00840001c00100e94884040041652242554024400a621070701040c00070304100303c0d5542c0040490b00b00e2468404561400d9a0740c40708844003200c810f00020010381814425808225407040c0101040600e5070340d01303900240d8543c3d42e680c0d627103e140541041d42e502d80452065400800343d440540303003190390317580c4040409a03400c0081509805800764114005c28024000c01c81031149070f401c41c0380042040c00f40030828500030b00c060035261400401c480c0d4400445111030464080c0e1101041043c00000102c50503104920243d0b00a00051408585c42c1216040884085016141004a0344040c200e47d65140e002c480b010445030000c2001c140466074404ca0319a2002d140e0401d0141d0800f2a92401c0c546000c0c0d50080360006410320301e004181f211805005c006140c0701c0304460804940340c0026402d50800f000041440c1007181a220a0036400030840e50700700201b00301 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 943320467 1250 943319217 943319219
    0x2010c021c0c061202070f0209060103021b06040b090303090c0906010507050105180111070209190b060403030201021809040809040c1808010609110f0318120a0e09010609081b1207 79
    0x1400c402c8440c0c0100400b240c2c00c3c10000d2114207851080e640d00c0c42c1c0025081041801c01c0e02404190380c405000380f810141c003045504082000e080941d6141c0e11003000400c810315103414800480b9601400c80100da410802c244401e8510000d10384000b2074080b103030311107183c40d64401a0754a00c2a608001c14039402d150400060345019a080050311080300001c2c8400010400342a01e02d00c1548030007517000383c0c10808282580c44241601d4441c8164500c000b410829081c00202c15402c150700880050390009070305050401c907210506030f0540c2c00d59880d04181815590300b1214013450701001d000c0d03962050454442480f4030701001156070110900c0a58945650301b650107032020340100d01d0314500f0300074444800301005044420000c2c0c2060214156241c100ca8003144458036000d483c0203101c0c8001030341e03428001d40000c0110510700d444120080021001340000c404050303000070140b1103680340030004141d020a4030590b42441004a146207244030000030b00c042c03031803c0006018428550 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 943321717 1250 943320467 943320473
    0x810050a0b0d1a0105010f1202090402070506090a11030726010f05010b071a0603060118020702060d0506040e0f061306060e011511161401052b06050114030402010c021c 74
    0x1a00e06030141071183c64601580e01c0b20010f480070a0882507003c0001c0c5a4401c0d059140f4195002c1c2c07030100401000949040303c0713900c40a06d03040e016150369456401c250100010424070520500c42301c4025809010340303e15000b45004000140e480104004101d210014030700c040c02c0d40a01159214203c007004a54ac44e240011503c4c0c220312000c56071020515266661007420400d1203119100050003041584e08200369031015951301010406110340034022540140d481d100548480c90740220002481c0c0b0b0070300d0811040e02c0d9058403205942c1c120076451807144402046055000d80956110144043d0300e1511000400040c2d0101d00000310000c00840c240141002450b54000143d0380c11039040b691207400d80e103800e680c000703040e07151102d00700c1049048000038902c3c0c411300e0141091810903090188804e5040e07691002d40100c0042c100e60047d190b141481042c018100a01e00070394000b80c840e030b4607800713440060006030511082c00010400c650701c10b030340d10000c100740100c0c010518510345 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 943322967 1250 943321717 943321733
    0x607150f0219180620010f09021e01020607080c04030b040b06032a010c030512070e010207120b150a030807030e040c050309060a1505030f0f1002040810050a0b0d 71
    0x21048400c00791a0003410000c51040710045078080400f002c0c0b04660f4034010741a2841d8622180c000b00381c0d00b0000190f40102d60030f00c00d481c02d01030307506000700da10f03282d510411180717100700d82c0c1c050541162600002c101d07036800590300354071920a050103000382c2c0701c0710003052031400b55901c001c00c0901c06170100300400020341005d07406082c055049940c54104080e0f404601c180c1389020213035680c64654040065841102e5003d105c6010b8208a45084001b42c0200700380201160001c01103641c0104172405968104110401070a07148904803031458140d442c1c801d2082c02400744001300340c88500f00b40840d500da0083c03000855001007002d58030f68640c40c02a01100608a44500c101c1c5440c0503100f1540c06001220f201c0c4c03000e003000d406140d60b1149448010500d030900d402d00c0d0100e106000c00c50ba2010814502000e540c1d00041c001103080401c00791514500d9058800458014031041111041c00180c4e1000443c0206000c68250345280245009082c141c0c03810341e00c27403182e00728042840611 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 943324217 1250 943322967 943322977
    0x20102220504060504110d18230f0c030a0809030f0d080f01060206040b040b0703090203121305031c0f0c0602070b012607060e01051905040e130b060607150f02 70
    0x350b4081c0040c9aa0741c0070007040719601d60301c003800b0702010030003c8070b020302541c80714011440d10301c0f400c0c0000080307403614110001c01c1425401003202103844402c03140001c01c07030b400d08030250800a0075284802d07408a07841d2100d2000040404601050360420341d036050104002c0d00244000700c4a151210440c01004a102503c0125080c100407001044039807010801b1403003540c025104048135103840d41c0300c81070340100800c030008142da90810040141d80612413041c5000741403040a49400c0240702c600705404840e40907a10030790150100320f40000228600c90303803081142c10700550b880740720b030403d03681d442e0103400c01088103100003000700410111544050680d610010910b031440071400d20001c2c040f00300e1502d07071020380c44400b040224074447c000000ba410010324005041c030700c031035801c001e080d82603015072030220300c000c18117103c04940c450025038880100880f22510f1354090310344844020010705128001c580c0003506d03000344000f801c843c191180801c0e4013044180c01101d01e030f000a4003d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 943325467 1250 943324217 943324219
    0x9020c010209010906030225150e0c01030b09011412280c1e170717030304110105040b03040b061f03060f14060d02070f0b070e010905060423010201022205 68
    0x1c50344c0468428464400e903034092075411804d507107070847c0001d0200007200e500301c102c51400003030071880d6890450380143e019247e8450010007211001e60000340035a1440c0030360301d011f0010f0000411103140c01035140812101c0c2507480d98040104034201904050300014449400602034441c0140c3e6481e043c412807800b4010b102c441b01503521004c0c00c0481801c004401450000c8003102484492414410541090b603401c040b5040f0036a1031380c441b40c0d0100e508100281d00c0d000401000180583c00b852410242c90034070b040341c9082d00b8407450ba1918000a0805002405d003100007520a86419401080c4070108440390052002903c0d0003c001c2d210a0190602d0300c01620300000710012003444100171504010000b906120b044c41902c002504241e01c29601c0710540d041c4036002c640c00301b05031405107401d80e4540c03e40c003442900241040016600c500c1c080c40c02000100319280111240c031080703c14100d4101001d0040400407400390103a40c507541c400c3e02e003000008404242c401603420403910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 943326717 1250 943325467 943325477
    0x5070317010b0d0b06090d03030501030b0a0902030604060c202d0d0e0409020a0f080d0f0519090b1b070f050a26070315050901060f0506090a09020c01020901 69
    0xe8000300c0038424103080c07081000e40201407141d0240886140c004140c1c00c000a07007494184a842400543c204107041015030110380c0e02d400500503c441d0305074865001c22a030000303025004599000c00d40c2c0c0c0d03100030300151600d6a2800d40008091090300c82050340682e404050a04400000019499242820382140f140c40d00c00182e101c50b0705840d6104040201000250503030034015442594101c05024126074415501c05091340180d50b20341145018291850102c030926051800c207038540820039174404240071054103a1f8504070340c01011030305c000303181c039160701041504401c040d03800b2074072034208a29140300441c0340c14980b4130b105482420000050221520b59640b0400b40c00760007507078054a80c20100d914020b10180303a40843c60549801d00a840ba103035840404001c904050360381d08122201000411405c40e0400c0e10f00aa03038000c10024002c1000d00e01d0480e100c0035041d0301d44152409078602040d4110a6600e0038403601c000c008901d070139990b40c0068000d143c000e501806849021407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 943327967 1250 943326717 943326737
    0x3010c030c030b0427060e06010927110f01051c050a060b09100513120c050406050f3319111b0d0204020d0903120605040e0a0204050403021507050703 66
    0x413409000701c5c0310060040c20514074a40300300c81d80c169802450304040c0c51582e110303070002d02d080d48200300e414024506403200103494043c2d6449086c640c40041003125040380304030701c440c1c003007481c58902c00c4c98020203c0b0542d40c100c0d208401600d050142405642e050403090210320180d088a412807031042518200130050035482d900241160f0003492116038110780519205000580031340300030142d10300503002e80145159030b1050060b007401c0c0440102d8041c04e00b240c0401127402c0038042c00d00900300c11201907079216004e0700498543c1d6180001800b04421307040c9256600c2192003500340d41c4000195010b07986220800c0c2003403003004140010800030f9400c1c0c1d040190805c2c00702c0c0c50034404a06c12034412841c20443d082158514200e0fa05070707807142d230800c085145c082e42d500c16120903900c00d172140544400911240411509250b200c0790280d81130140d110782802012460706111a07045074001003d840e1810700305d21b402c15145050855200410034080c82c0c60700070000d003d050344a079031502252 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 943329217 1250 943327967 943327969
    0x10509011a0d0303380f0f04150b04030803040c08151614030114010f030b10050f040b0a0903050f15040209090a06051f1403070e09030903010c030c030b 67
    0x72401c0940000140c1074003031007010245401d000d1818001d00038600425502e5145464842d1800d5211240420306505a8112064103146a0318071090000711400c501d03035425503003c80e0990b941280d907a0b1050790b4411b103c081201d40860841e02400249240c80d45a60b12498a49126481540c0a507020012200e0004003030301d00156440d07503442c0e103880c40a03080d140d8001304254425140104400e210100140171011144a0065070003004000560451701c139950001610f0414071780e0305041058280b00da1501c658443c000342002c49400340c90700c180c0c1c030030404019030090301407508107104011000a070a190039511250301c400303032402142a1080440d0200c7c00b29078411982c04034840d0b03941c1e5200010054600074200b56030102c29201901c00f84141741d42c6403000c5a8046980750a2040c0002d004d2000c00f0514001002501d040898805104c0400340042e60b2050241b06801c2c0e1004405c00055940314140b003030703070720251000d0003e104244002d8806030113445020090000a40361040000c45 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 943330467 1250 943329217 943329221
    0x71704080a0507152304050d0b07030c0c0c18020d02040b030708100e0f070201090605040506090c040e121308010c0507021305040f03050a020a0b0108061b04080c01050d0908070f0501050901 83
    0x340900d1070300c411030001e410810300d0031402044039000300c05c10b0050100060341c0d200c0c00140c60080d449221005124509110040d003141c20800200040155004030400001d28107070651082c0e0b90721a140e0021a401d10101601a10420b07400710702c01d41c0041000500d03928000d0184d4000c0c0c007186c81d03840716556164080c49050400d84105070207140c036440440c52001c860b0301c4182d0407208900c004590000340f6101c00040d2202a64200c171603510100c200a00018140800f0410160494082c0042c07607a030700c00c07295202450320f200c0c4810a00003c454000c1d1040560410090030000000d028250364150040c003550014070b000d030700400542c0c0010300c107107c0e140324147c840c591024404281600c0c584040341c442c4c10001d00342d400c9d07119019000011a603084c1c800c50007050ba1500500315803412002d00700409980c214100750004042c031003401032100108080c408406d080c83c2c400d49400601606101501585201500c40c001c0003440b08280300a030081c01c10014000d900a121360389501c11604d007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 943331717 1250 943330467 943330499
    0x90b190608031c0c0c051906020405120a0204110c0303150a0512070501031a010c06050a0f0603080904110301051e0a09020c0f0d02031303150e01022106030105130602071704080a0507 80
    0xc11500041843e082081f0758203042c002e9540241401414261a94082540000c034034006424541c44040c65004501d0a1b0180300c40401580c4500c44c20f025030041080c2e6680805030004079a04ad15a540c0c04080d16540103843c02000e000b020303800101d07107441c81325031030352154002e250009080c01016403102040394410700070400b0681d0303241c1c00d04e83d442c1c0300c1c20001c01c4090030f44a642611740b803400c40440800e02920005d18010310a00e0f80d292402e40810044803d110002582600140010440c07070703446488281442071a165110005d18030030000a0301641c00b9000000c3c7c0f24808610a10b100b0300020b114039009648000700e1300000d9071400243ea0b0390040302040c0d944d00305000d105000050345410b88030921041d84001240d00c074520101e07642603030007402041b45100007e01540e4600c03410b8000036600180b041c0d000304210b040030030782c004035082c2c5ca9034058043d580004142c8104440c1c0f07840c20000200c0d8402c2142c44680380d14900784c4490f56002c0c03d41d00740c403900c0808a002c6881d0300c0005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 943332967 1250 943331717 943331723
    0x1106010609031e080f0c160b030112030c1e050c010206150105340c0b040803030c0a170c0417011514060705030d1e090b190608031c0c0c 60
    0x5050a0b280d541d0750301c43c000e0311180904212620541d0300001528600141ca014000501219122408804144e24012102003144507009031074600300900341d0411308803815510401d405c94800500c90505032880d2042120040460030300c28140054101e282114400e44c0e0b2240003030340d500c03101d1403004aa0700d21090b2000c1480810101c903a50a642c0100000c20686802d95902c0b0b6050850209522200d946950459804ca008400610800c4442040d1402505003086440e081504006c03405681c2c2c04001d100c2c08201400044551040d0300902c04a040d804019042e0032a91070b200c0c01c541c045400602c01c0e4440b01c40e1203402d20850413010301800040c10401c14040c0700088c68040c414107142031030b10050350040000c01c040f0300880e070305100610f44000005e0000c24610950040da24900408000e41030a1030315000c0d50038002514001544d420107524a41070a5000360140083e00816180d406004280b200107028141d03a070105242c0000d04104071400c00c004400054261080301d582c01d001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 943334217 1250 943332967 943332977
    0x15090c27070e0a0305030c0f19080a05090f0319020f01030c0e090408120109020720010c03031e0903030518010618020309031204030c050d0f0c111804080a11060106 72
    0x12015803160303016006500000b007492009555a0300c617107080d9885054580455000103117050302c0020104540004000404e00c0060013040079201c0304002c0c0a1302c00800b04000300015035403100d595220852468071401010b46030120364040c80e003c0c100d00301e5141240604248003240c3c40541c000d10881c021128151280304402c10242c042248488005008480022007800a081c01c3c540041d0000c2c041c0c07400010042c1e4628280c01c0450b018103500c030700440700001041c0f2209259038080c00b451211a4182408510740c040114084180000230080500c0145402c40e80c209159268212902603126268007041665800038a2402e0324802d0090b005001381e102140088040303541d0003107a03c08081d1040d2401e060031000722521141d001d503001e900080c541849142444020310058402038400e051024800c22004800b07040303084c1e07100300542414902140208140c40d00c44ea80d0400142e0981c007501245800d1404004c0341d000350a00c1c20006805840d1046501d0b00014041e061b6182a190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 943335467 1250 943334217 943334221
    0x6080703020904061103040b01030c0b25030306080f030901140a05040e090307050d12050a1e020901020708160f06080103020312030711070b0c0111070c03021215090c27 74
    0x2844400b8402800c02c6802c10394a403903825112403c00007a5000d80d10030407150110794514102403c41c004290000b1586160401c9802e482e0a1a030781c01c111078880f04071040d03000300b02038281940240324950040082d8011110390209000300030008000b81030007601c40d80301140101d13200882c98060420403c01180041100b0b010309101c2281140c0d000c440b0008980c500203141e0748090501049600c0c1038042923111a2a0150344600d0140a9225101210030000b140c40c41f80c2554032103050040f080d0000d50700090002d03140c0d2080c0b26100c0500540411114910100c01840481c10f4141c402c8001c101c1c602c0001140e07040c45410b10134122900180100b0f600070400c0c030140789552000c0c0032941402139000c041034035060240031410040c49007200c8a9192202c0c4001c042c2980d101d4040c1d080320040400030900003134102c03c0d19505881d016a08001c2100000c03100d6441d0602c18142108c0c005640c1040107441c0d8800149480040c3c011344032036198189404d500b02e20101802815002c118000300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 943336717 1250 943335467 943335469
    0x18120c1b0a050f060f0f041715040305091912030e03060705030408030a0923100603050319022d010b04060e1306060513021902060603060a0b041e0f0f0608070302 71
    0x3582c1d092180c0001d042c4c82c5402140d0290012590244140580705000420204a8107507054003034680000414080c018810200c420b41c81000c4004000809126010070b0921450300e40003e50001000c0c001e070301c60710881e19020415140d40e66604105c0000b01101d256400b90f04011949034003501e101c1d00c69600b951500d90ba104440d0b0801055079807a280e8460322200498600046100c0d00e501905d208407204100c0d411090615509494100046040080800c00141e001048408029010031441041d490f628030803410041c0000034200c01d4205200c0103105056103030741c42124200004001c008900780c80082c0301c1543c0451181c52804403c03d400181d10711200121845054490310002800507140c030001241c00c00b81172041c0100700ea0200f14000440c003c0014606406860300080210749440300000341e44002c01042c403403400e80c46282d0030035180c071181c01c411240d4008060494901c0d501c016010001d24148500da08080d0404118041c001440e1241800303071000500a071a143d81190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 943337967 1250 943336717 943336729
    0x209030706020106034d0a1805160f0818070e09070911031303090911220312120b0924010f021b0607150501030b010801110a0818120c1b0a05 62
    0x40b148106e1100c06101c10815641c4043d040400351440e0070030703452022441640c2004607040100340880c140a030002d02981c3c160041d40e1425112114a8070610544c0c540c94847c00c20050170100049620a4440118041155402451088181c0c1085600c1150340d148070b03600b0b40e841d035160304460349410800300d6494508510b0848110303000c0d0600c80b40b0303a40d549404030200c40381c1d2030341c10248400100d041641c1c89800f20000502c6e0300c505a61784c41172401c6031600c0e4130307400d08002d10006012400020052480080e00100181d14000340b10410500d46400900c003400c2c13640210740c110236000c8552040710740c021400714008880c1d40d4014240c003402c40860070f10071045600394950180c42402440d00040840c00752454030703480e034071012540b549140303002960301078180c0201007164100480c5d10151110750080c0e8075507007040e241031885510b0303160b8a52a0a11039003404410fa0007008042c0c040303150328070010429050480d0448000844c601c003403408044405440903403100038a00100560310b009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 943339217 1250 943337967 943338083
    0xd0b011d0f13260406030c080f150a0306140f130510051f03080408060c1c2304030201050103020913021f0e0a090507080c0702130f020903070602010603 67
    0x9030950b00c4041e1071034107a8503842c00b41211100303e101c40050180060359043c0a00081c861181c10080140d0902c81c8005801c64001441d0010781c142c25440126580d43c3d030101d8000868000c00c04012a1640418285030090100e4491082c0468113000ca0b0600284035000001d49420801074100290a8054280035082c0600080c101c41c41440d00c0e60303110764503111040021131050300107594941c0f80001d082d050020003048800700301418020b0009100c0780d590030f160f02011002c0700142c0c1110840c0920905641c0311030300c245415174038080000309501503102c0d6042c1d80c022103030442d455a81510361000170b0301e80300d802900400c103840041c103450390000b2070004000c2281041e42103501c0803400f00c0d9550388a98030005410b034071241400560740d0000d14954100c9104100c140c50300c861500442d900080d45601040e050ba074039203c2070748404a5905803020a80014281c0d061555a03c5c8001d020380014001034605884c180c155a41c8600170807144901840c03c0b0042441001000501c5a590340075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 943340467 1250 943339217 943339223
    0x90312040201180807031b0b0313081306170906011203110c0603040b160f0512041a1006110f1504080909280b03030306060a0903020d0b011d0f13 64
    0x3c42e9690407007001101c240b1101603d0a03400904501c2c0c1356040c000d00c8413449450200c50340107408002d000941d00e407002c80ea4460300e080c54007032011602d46050543c030b200c2c5800c1c0c800d04140340c100c0881d0144d40000d00c001c51016642038014651100e041807911075a00f845201500140408000000f038050611071102003a01001d448440c03060340c01140d4258811201199011000c034100000340e5800e11500e03071201c800e46040c1481000f00c49015001d032107000b07200e180c00d0352400700060801c108c0000074140310b40b818040c60000d04007242603402401c007038012000400d251004010710440002240e0250856040c001c00441e03504c1d042c2c2c1c40410700050416110310104011101d49071300c2d0406407034000d101d400c200d105401c040401e940500200546081c003074508018900c1c0081d60000240d90f00803908a4115994404046080c0d03154405544000e4202200078480d809010005c2165412115800764042c5031301e12050aa0048000c21250004818800408107995040ca228002c4c0082e00c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 943341717 1250 943340467 943340477
    0x2070f050d150531020a0614130603020a021b0a0905180d05090111030a0c0311030d06090504030e010516061a06030a09050c03151b251a090312040201 66
    0x59606038000c290359044503103004d0fa00c0080c544003c060070b00300400c4201d003010808200104525030004920110a101c1c000c100724920341900d400c15000d07811608070401030041021683c0c0c0d90341d0058003075002404100d0160044400d50031400441d407013104050b050081400840c02d050108040c02001c002d00f201400c9074100c0c2c0308600d040001c00810a0940ca10b8440c0c546500c140c500040210380c0540901c459a0400d204003070085070400541c062241e414109000040b20501c140e80c07842c01590a0551200e041c03040004000d50b05d540014096806540c989411840103001558184140c60044c1400140610303070101140740b40e0f004c0c503c6220b0000f20104d20200729070002d00b43c0d4009039a0703c2410b42e5a20070440030000c0402ca0348540d543d050740641130075403d502c80e001d49203c00034000011108100240b2628525110407182c0c11149003107202ca200e81e050400310781130440800704407405200300600700c103000030342110f584c49400c0c141c00840c40c2421540c0d50150945001d4002ca051003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 943342967 1250 943341717 943341743
    0x1d060a020a210b0a050607050a03030911150c0d08010f060e131d012403020d0c0909050d03060b120a09060b06041d131a0c0f030f0a0c02070f050d 64
    0x1609800d5a02d03021480c03107008616100039004205140d2480d5000b0352080208010380c800060010825000403078150030000794508681c202052044400c0781c00e5503000910008130110b2209034405800b0442e1010f0807514030042845090700e01c4202801240038080b0668010490f55201e0700785602c3d03510000d40140c0e0030a0b03a2010020640b105513101c0203800034200394040205000348158884400c80c19010441d4105a4a81d122001501e002c0a406001d403501060b0901c43ca81e450b400003024402403c201c000030300d04000b070310390a4800f500d20019040010020f140502003094032840d101046e5003000c43d85a80a140d4001e1400c3e2004031140ea4482105c0c002036540d01c80688010301641c21410245008102d00551541c0010013548a455204d105031000c5110303024a014849102d0360160140e880c3c0404500090141425103d4103038000001c21600300041340807580280d029040911161390110816a1a01c415001d83c030b04921241d10100010302d0304025003601d050040100500c2c02d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 943344217 1250 943342967 943342997
    0xf1803020c090903130b09091614130305030c0a050d0c0515151f0912080a08060d0804030302011a060a0212090a080a050c1815060706020417101d060a020a 68
    0x2610303086d44241e4080c000421902da241c1810201c0c5640095110f6032502c0364012804041e042400740030000310981c00201d1007002d200790411122000c2d45e00002200d4a54840c40417459460704d50400484d614000c1952003061381d40101e8410489030780c0200038100c01c14103020074110341c0c800245010742d40c40300703020000220303100c40c84440000e100640c5507030540c502050015101402c20b51044e4a880381301c16141c0040b030800320a40f940440c0c0e03890018540e4480307c0c00281117203100c190151075584009000020550158040708500413403000a03504124100300700003a40c044c0f80100c0007d40c00800301c006002c01050b0081600c054001c10011129032104502c503e088a004000c44541d80f2510300e40741980f41440c0c8110303610440300e2170a0941d1920011844104000ca41260300503940031940301c0c104011a019200a8140c1428600c104034050381623135034500a41e4400c540b000c1c070b00301c151040c9011255081601e800c2078802042c0c1902c403810030302c000b5070100c140c540800099002007201c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 943345323 1106 943344217 943344247
    0x302070b0c0c042004080c0102011107050a02010e031e10051f060c030903080c03480a05010615170f040803090c0a090f1803020c090903 60
    0x2407451141d44c0c01d030050503c3c562002c0c800380081804260007500040c01c4824501c01da0091050b419150248043c41c4181070001d05036400c03404085c1c015501074121400c0136140501190120040c08010806040360324055031400e03004603101d22016146405800c1d00405020030340e40046460084d503244078065440346105200340e0701c43c12000d140c050300300c150096400c040c403150b58280319204951294000741d0500040e04081100e1b034004111007003c01340c80b01c0c001685c5001d0301003401c40e2400c1c11323004442542c150300c620402d80c000104280542801001c0c4255581000118584007501d202c1c6204c080041c900740a0041010319405603001542050308807822680d00d44540308900c0c1051080c0c001c00750400512070700062782d0603d580c80407100340d65803001044941d1106056500b01c0c40014000b070016440400c000802c0c0c5000c09140e034020301040c2c12285010f10503029020 = true := by decide +kernel

theorem cover : BRFrame.Cov 943165467 943345323 := by
  have h0 := BRFrame.cov_init 943165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 943165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 943165467 ≤ n) (h2 : n < 943345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
