-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3144
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:47:20.618992+00:00
-- url     : https://prove2.me/submissions/74417709-05b8-496c-b1c0-86e6ea78f151

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 565287769 ≤ n < 565467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 565289019 1250 565287769 565287781
    0x2109010507031809050f0a200f041a09190303080103021e18060405090109020d081e03150a0f030803060f150a03020903060f1e0907150e190803070209 66
    0xb03544a04038034a0b6a4110f642c040740d000c5495000900440c1070482d1041c050b550701008404485003864014603000d0280d030305101310186a80100030404150409509141c0e441c114100001e080c002c034030022040114400f011030a0000c010144c902c0384045017100c0a2179510b01410500e41804080e000b0030340205850340e460031140702d002d40f284010b4860413007040792000e02143c0382c1056484503c198242070100703c075414140140201283c001b803064100418560310300ca503652001e04800002034000c0c0f10074100d815510044c51150002051003000c6458180270803946100d123400000c040c104018051021440060559030701c10810395035840910440300c00038545450760068230f10090310001d00410110f0b450b4019120000069080322a1511200c08505050380c0c121800740d04400c034060348104107840c110442d90011036240030b4802d01ea44400503692408a208800e00116404180140103800c0a940d542050144002d140342c42074103241d4010389912400300064030860900d000320f95 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 565290269 1250 565289019 565289027
    0x32b0302091005030a0608010b031203090c03010c020307030314010b271009090b310b06070c080f010905100b0112020c0a03020607020312010603110702090711210901050703 76
    0x110140c001044401c10007003502c0300411030b510456280c40800c4c101003000a00c803a050085800c0e80d80e000700913140c03103c036005503175100760002840c00c201031041007500340443e00c0c00c0c0315048410030568069561848a03003400340540304401fa141c41c101c070b101d40c010403050080c10b0075205011128036081c3c02411311a00c0c1981c0b081d40b40c14000350302199440d9403034109134012201000321403620100340b1100101c0410080b400c001032200b20303030a03041200248031014000c0711b80c4200c45031540001440c041c91b00007203241c43c0c00c050402c440c003003241082031109031400c1210380891440c0d00c2c001c3c04900030341e90f1450b4403180030a480140440d1101340c500c00c00c0c0e0044420114007181c41c482151907400c0300d064035035282030512041c0e016000f16000302d10358502c080221032050300754030f201444907486c2c01d04c102c00601d604c0b112400750003000e100600060b907810449a001e80e00743d44e207a5020020600b1201d050090f00c40d80c20b0394400c0380d102c41c0400c00543c08150f6020310000d003002a100d18082c10103403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 565291519 1250 565290269 565290277
    0x302210313080601060320030723070807030e0d051f0623010314011a030406090b040b150a0501021e1e070608070c020603060d02010e040e1506032b0302 67
    0x14001210901c000c81d400c400001c116040b600c1a0358148045281c5440800a181c07010b04042d601d41010000201101c0c0aa540b020607100c454206440d158103a444c0303d1102e07000301900302d5010100140d000d0a1581c003495852152500b15040482a44282c0d14260740d80c2d403558150810071212070a0345a01801a03105000904079509964460342d1041000b0035080c6000e114180804c0c5048210014801340961050503103000c5119813081d211070900102d1190001001140c41c19100c803174842c00140f040c00d0190155110f0700021515042004500400140d40f00c100e9016091000080010340ea0025610061411074449070000362110804903081070b03005a0058204ad4802c0e01e00402464000b844108440c00c84e5641c1d283d540b030342c0d0310440f580c0308243c41c0a94800c5007800480d4091a2500328a15040d105045c103400e40c13003a03107010606441802c0c2a04100340c100b850003800a00050400c940d212000302d001e0003a14010b02d03918101e21080805810112050b4003003646468000e604a0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 565292769 1250 565291519 565291537
    0x90b03070e09040809030f070e0a0203060d030c0602070210082a09011116080a050105060105070c03080c0c0a090b01021c050a0f0c080d02031f0320010909060e04170403022103 77
    0x143d900030045d1f007078a41e0385054a2203601000305051002410340456032003070303030300801005002480c0290f0b02e4030120707902c1c0880341c0181c80042c0d0801a03000181d40d00b841034500d43c40c0ca0345480da500c0c50506141248106030804516003000c0c3d01411010029084044030f20018090034800446c0c0d0104d42e401c0d0ac0e05000829034103440307281a41c040707840007000031034040691040001740075660b01d038401166103014040e07009014258103282800054258005446150480070440d54500c450f41d00080101c2c0c07043d0f1007a54074a580b200c13140400c0d64144450740c00b84181141c200540c440c0c55400500d00e21031422248101310780c05074003049140c40b0b48940301869821022590321807a0034001d440c025803003a902c010000e0b035402030410680400d0410001201e0f0400802003080d4801c80d0010010450b20a801d81001500c85001c903402c4400d102d06c4c000b41c00c038040043c0f1686000e150613400d140d10038144010050b414031007080103a0740e4410303806401e1181d00e0444500140e41d1700151031400b034a202 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 565294019 1250 565292769 565292773
    0x51e120c01051f030c0611010f050a060906090203062803050f03040e220305090a1d010e310602071208060306060109140405060a0b07030906090b03070e0904080903 72
    0x50010501500058012440c00b805083c8892030a00440500100707488014400f20181d00100400c1c1e00980001044c480f6040000c506985142c80c2da908541085540c010110703940c0030144001d1455100700f00140001050452850038210000350703441c540d13207000c1001520780c4d0600445980c92960100001c581c44811642103c02b00703042541c8980240c0168030b4101c0b00c21001074440b00005540900021303221203c005c800e89143c90480b1550f000b807002c41d4000c4c0004130001218031303190003000e2a00c449401200003550510780340e1004943c018017496074864100b40984c40745244c001c60000016500b081c1c84501416901d080d90203400b4095000c6c040c2c070050002502d149070042d41652060b50100c05413007a0b50343d840d006540d038020318010310810080c1249101b040341801d60050f504001e00419901c0c1080c0d84502e03012440d40180812400240000400c02201c0d030402d051708058401c1e214081c0c21460540c07030003082c200e13140c440140700c0c0304404081420b0060b8402110700c0901c010342 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 565295269 1250 565294019 565294027
    0x3190504030507240c030c12030b06070507090e030a05040611120304060f0b01031503022e020706020f0106210f020307080717071409040311191202010504051e12 71
    0x140c01c03200f08525290140c1841142c0c043c0482c54442c2e41c5540585d035043d102d189190a103604e500649070380c010010410b0595a458001041d500c00000d0401c15225100924280c3d08114064050324407044031014542d106100d940d580f19040303030a844c107071562031400e001c00781d242d0000689030001c01da03806460b03590000240070034400d56420040c1da040c01c0080601c05458480e00443c12600281042c070b02500414000348010300d4074000c40c86c641c1b140411940144880011311641c001413100c200b10250f80034a0041140079014001010320407080c02c02004034600e00303a4650703140744a03182c0b56081122039124203401c0041b03070518030f4041c54014084486154039460314030340d02c128601444c014020fa4184440c4070b00700000d03440099610084c241e250b00307502c030414001d4400e400341084003440500081105c81a50801c1040a5581081c0400314002c03080d0a0050440050145150071a41414100408124001021100300900e0241007003490782c503140a40c10020300140410042100013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 565296519 1250 565295269 565295279
    0x6081b0406030f0b100926102009210307170d060f180507171e1303020c01051c02160b0907060e060a030e06040f20010203190504030507 60
    0x5844900061500303c0f007044040310704010024041008050040014484079061040b10802e2160144420002070b060000209041b00142000c4100d400307981d00641d50041300c45000380c0442c0b220110401d0f11700c80c40c0342c4052040071441c403041441d05200e21032503840c40703140501402c0048070715071038000d1500800c00003030126011055208680e8009410300700300b0045a180d8411a410040314010031540800c81c10b0912082c015040003002d060600030b000703200c0348400c0443c251842c0300d13142c484005068608040388001c0c0110000c0c1c00700c040f2071151191040041e4001980202c4140c09003001034032900c070311b40903140001c1800380d140c5102c0d00110b41c0b00d140d14020103501c051031b031042607217060980d82c5034921a580c2d030b820310607030740000d802c4444094941050030040000000c546004508510140891443d0034401e0320100d521009d542254402c1c04462100c0007100d9051000f40c0c480c03081c0c01ca000030760700d000f03003580c08103d0074058803c160182d000f40f048500070b550210903501c2a0340c0e90 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 565297769 1250 565296519 565296521
    0x60d111305010f141f030908040b030f0a051504051005040212060301050a020f0d020f040f030f020310050105010f050c151314011b0c020d02060f0d0b0d0c06081b040603 74
    0xf0f1094030a403c840c00e5020800086545802d848030502429205118030060100f041c0000c04001030810b165490003240003050620b00204082c002400d8056907905190040702203050009120707895541c604001e00c02d01082d14070800b44203030800c41e4040791036121101074400490783c5601c490360107840080d0b24406465411030701c0e0711619080b0000c00280c2d03600c000b0f080a9204411070224030710010410708800e080107502400410305283c504600305600c0c2c540c110100300050b042921a2044040c8a0b0118501000365000c1e00650b400d0034401940341900181c6004003500200342408004101c85800840400051183c8034000490307420034200900101c84004174900140c5100c20300c000040314001050081d41c034140d1017900c0322420b0740038111302140c0c044e503550b000b00c3c0c0c04004003140001594503140038143c0c100a00d640c850341c490070120b106d41101c402501060092001064900121b4140744000c0d080750140d080c501e03956540d001c89a241c0045040300000b0b9501c010502040507541 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 565299019 1250 565297769 565297771
    0x1033309112709070909150c03060e0c0f13061125230a060210060e2406070b04080304030f053a021803190506060d111305 54
    0x50030712003107580860340078444402105840380010302045200501032200003191550b000301180705440d80f15460308141002d0354500c540c117549600700c40c031040c0728290062190082c0d001c0d840c1010007002e45003440750400010010541c144041021801d50240d842072011201e050849060b0041520341b50000a020600c900007035280c40d2103491401c50180340c0d50030000200210b00b0300888681c0f45041c1540c944000c9142c00101d0807094614140031a40b9031a41d054043c03c034036005042802a0038021004881d8035a00c46682c410940c414054a10001940000341ca8030a00d4400d41011061020030201c1c42803500040c9008544010401402640c00242d401036100f03584402060900d60300c100c8150140c07515240800000070940400e0403003000d1040076a0081c03400c40f050500d0400041d00403600b02220180b008007160308220100d01d424402003849070100f8030701d2152500c413602c40b20703520400100010700a102488c2001c060160419080c4590340000b41100c20609440103500003800e0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 565300269 1250 565299019 565299023
    0x1050c2509051803040317040902030901051602070e0606220801020403111008280e0304090c0207081209130c02010c021506060a1805040615020f031201033309 70
    0x40341038081040d072076054903012803c004201c0210f0619065444400803030700d05007070035404084c0070440000c448a140c005184a018200c0000540e07141078065128008245400d2030219040f400b42844803590740d200d059044031003034504503200d15a0741341404c4840b008021b00c0b1a89640b1840000b1000015001081035901c20301d400310010345000140081201d0700003214003c20800400a200580f000380f10a00d500d104049001c002c503078110868040350326a034820b50443c0c00c0003c080c020510940203540c40c102c074620041500c10b161000e40b90721281092060180c0540c00540440c0340c0d621420103032210765004000300031103020140081d0003031001d64850009070080d20307404d130b00d100d44800b5402c0c03007158050480e91410400c00011035040600d20f0140e0700e010002c00c000300305621544074401c0548001c000c0d001d9401e905142c045c1c80c151280d020180c0561080002000c60143c5188990460b42c0c0401c40c00c0c503a5000440340c003500384180d9419005103280d00c500a072401150f41041030000c1c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 565301519 1250 565300269 565300271
    0x219030606050313020d0204110d1a0315010b1308061603180308010510030e0a241b03020d0f0c0306050f15250c080a0b060102160501050c2509 63
    0x195a01c0d41a00c4034041160790b1961002142146009800c10058401003984024400a02c40c0044484691076030414408040020394070049001c1c00e510b004032403542c003081100203000c0d1040c0441c011030300c20014051607040c01030208907101300d08048980c030740140010300c056407094500740101d0948103d5055020700002d045c0500d500d4145484103081c8100c43c2c040e52a031001d0703800d000c140012410301401031300030181e8078600345099090600c10b00d10124407480c8681d00301c1c40107410340c40d0403416010303c40c1e180714900100c13074030500c1003210307480408581803c01584803405801e00500411841140501e0f0504100002075001e03030507800807007603644c03c407103d400c100d90a0040c85580c040c00007241048140800030080c4106e405055001e00588504000d09052007550b188620648558044030003540715817204c40410005240099001b8000c0c4001c143e011200c10314603200500c00d00c601414030900143d0741050750010311002d8a50345203040310510402c0d1040911400744028443e9004517 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 565302769 1250 565301519 565301531
    0xa031506110c010503061206040809010e011d0f150d1506031a04110705030a0f02070e04050303071107090929060a15031404030206040507060e0102151504021903 71
    0x240607240c03144400c1e05000050160154500c0156110350019052a501016440800d1101c180402c80c99114500c601d11881d240d10928002400c1c00040b07200e1141804850001610701c030b4020998803d81e20030445060603040c2a41020a825006d003181c2102d040800180e401680740396070b08429911100b203126849240e948110840840304800390480e900d0300c3c00e01c1400910710b020b4200608410882d003015142c0b458a503917040c596032000e039000011402882040350401c1d0140800b600600700071032000e18920305913403016240d120040c802010302c2100f094440a841c0c2c10080c26000d040d610b4420000c0d41110f041c166542e4001d88a02808907000c004d4240007401800000c1d40114006090728482d2414002e4501501c120807640a08040e6070311184003900c198002c0301030144d0b000e600036000b02d0034035040090a01045402110a210800500c42c203140da002030360700d0640311030741c0301400e554403952440240042d50030f11a950040c008a00b40345100c001409483c400c03030b030070380f010005 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 565304019 1250 565302769 565302779
    0x7080d0c0807080c0d0504050c091303030e010204031119150203131e052403010e0402030610180b0114070c0e0f0403020304051002210a0e0102060c0d0b030a080a0315 73
    0x1c8940e0407620b455044c0c0702400b0301d4030b10004035080242c1042c864805d071410041400045454840c0c100e85454054100040580034190917206182103039100d10003c2d86001e041d40c69551b0080f07541c504241c01044041e0584908104000078000a45050401000b60346010302c4c0003940ca402c90209880c5051101030005084031206500c401c401008100110310305261104000e03005400b406240800d000480200d50302c1c01c0d5410046019140b800703c5000c031801c1078010300d843c0090081c036090b90518003500610104c0d50000c07282021503903600c004100d051007e00102c410150a0300d50501d400804582d0301c0070040031041ca0b0007510341e0a00540529903424403a8031f07909009850140250700f04200074081410102c80d500389440942c0100c0b2011150189100390005265034561404d500102e29040d4050b4070581000034888244000c10382ca0400d045014440e11850204025081c4c2d51200a2990346041c4080341d2080d8204a0701074888110000290140110f0064484807912102001c58 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 565305269 1250 565304019 565304027
    0x912010609150302090619090513031106130b060a0f09091101080c040b18060a020114071805100c02030a0804031e0b0711030408101509020906030403080402010507080d0c0807 77
    0x40f40c0c0c008004410a4031039409100d41c6011103031050103182c0a041d0040b070112154040c4500400150041d001c0040b4070341030040113982c4c4a901c01d80300703420042c14040300c032905450000541c2c1e0072401440300c1d52242e00002d44020442d074844990288100c0f40042c682ba101e51040c0b040038052001219400e407031100450b403044084030b4940f51580103004c24006500302d075001d81480c0e0028200320401545443c001040d0303401014001e0010f0703454103c883e43c0f01381844c48103a0490b42d80d091a02c6560b04080220704583c03602c0c040c2c540103107500c9a200b4180d6109030b00c0c010005401500381c1f41c10304a0f078142030340315230320600080d80e10f1004000401525100a940b0311038090300f085d00401c0300d84400c40100c07035100980c210510107100c280030114801605000b840c1640c283d400c400607070126282400400004584d01c8444421702c1440040000c1d00c1d1203080743e50103a07252510fa0382650300c03032006851038002d260000c0c00c00c1001007002d00e011080740c0d12a6083cac404136128098a42d8640c20115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 565306519 1250 565305269 565305311
    0x71103060708040b0405010603021809121602061c02030709032112050601020a080c03071a01083706022104051b0f0306070302030601081b030f0406020912010609 71
    0x2500084680000030f0104083d00d034140d400a21031400800c0c850790382e8002650144210707000281070055041071100d08a020030900707400100c0200480d003803008400405102815184c2c0c0a40611000100d8003441d0808501408482404100454503800d180b071004043c4d2111303000403240328118047d09000391707100d60142d200e0090141d480e10034001844015001401d0040c2001d81944182c400703543c0082c0850002c0c0980b585200025616805641096113003203000c054054008910b000040c001c00c0000728004200e420a0801300c000b10b0900141416206004100011040011000c90040201d150001c0c1710030800b0009142c0784c070310b03400400d11402e13209640091169100c9619a4400c01380c240492141c150018161a525044507020a0519408170741c0040008c2d40001000380660300700006130740008014203e001c610101e01041c04480c48003a01411500c4501c40000341041611f804a6414034000340440c4000304691030410301816180c005e15890364204524490300c410714210795 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 565307769 1250 565306519 565306531
    0x20313230303191d06191e0c021c1d010206150906040b191505040303210222081014010302040504020411072607030203220906030807110306 62
    0xa90b00d0b6440e00d81e42c02c585044043d1900e01c080c2e849510380c00300b030b02d0800c0030480b884460300f0140000e480c0c80848910012400015541214078100e54502c0848a45151508000080b840021140c15044040e45400c130100c40141c0c0c8a0350040005024503403290b41d2042480300000e017204800014801607883e07080c2140c11000c104922001d1960601d0301c0c1104a0300400007400c0020843c0c08039003c02e03c0306d103001154010700541e4281c1003000949101d8500b00440e8640340450070141956401410200e254a000840c51684603100315429142d80c11102254082419081d100300d850b0a0302e03c05581030f1045440078000c81c041c81000c800c45001d20514a15201058602a801c2d6030800000300400b410580c8c1040da01c80c03008060802c640001c0407101d01404081c1c02120480380d40d00c0c122045140d03d03414040c0144050740001c0d400200f0340c0c01207541864030310102c0d8490704240307800f84420303400302e2481803e001000051268070401020310a00a82e03288079102d03c958145582d0319819a14 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 565309019 1250 565307769 565307773
    0x6030c120b07030209010e04090804091805070501050a02060c0d0b09070c0b22030c061d070317090a05101815080a0603021f050904050709080606030c10050906070602031323 76
    0x1c41c20b4549082d03404a49030351310944c10581465200d23364041103840c26084080d0034001482c8090603c0b00800c00a4020002483c002c2c0c83e100c3c01c8031000352190b4001d895100070040100e5070301c0080d811500190b010050140c000c0085161000c0010800340c0285803d0b40c49444150104162940000d11010f03450744c500c85104a2840c5035500300c4002d2420001660b001d40c3e5641c0d444c00c0c0083c121103001c02070400d0001801c070a81141031845501d091041c20781c02c070f60310401801549880c5c0220000c1241c108680140441c8404281601d414005041e2072000d1340d8914408035804100b01036520030290b955403501019907411151070101c0382c2c1c0e0f010196200001c19030185248038a075541c1c0001c003519180c624100303421140407805507102a102e80000c41d20014050100740b00c03c03c0340561001c41100100701c02440100401d0101d942e0a00070810000300280c00812a00d41d00100d4506c154420802c40d92413400011070300c0c044440320003c441480b1050094048010030010720400a018100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 565310269 1250 565309019 565309037
    0x30e1506011409040f0207050f06060d06021602040906201c020a120f05060f010e09071d060409051b04030503040b03180f0c191d070306030c120b0703020901 69
    0x5569044960811082c001c408104458140c2c541d4021440b01408443c030158581c605d5141c110304020002181d03005035441081001140e60341c250701c0c0144c2e6900708000681d10b28840003040b81c00801042d003c0e407c00c3c1021503500c00c1003000d6103c0001d401581e81011311480a4101740380c0c1c01e00c18002d00010f00d103441c0c0b0101c2500081c560042800003101e080c814101c002c004440c0301500c140310044072001c0e92300c10412840f030234280508802c0305c00c00d180100751755032440001500528080c0c0102c041240b044441c0030201c12520140031841c00081c0602d072103030b60f80c5c0614400b901d0100e40d120345804103500c00c900e070300f200300042d58152944500954106030814001c29000d400090103101c1144000c0c1c1000c0c0c1420b41031040c040c2900411015081c2c2850f400c0034400202c4000d0901503290718172032003c00c0381100c039940070b10422034400d41d003080702d85840794101c0191441e40c00c0508081040b1400081091044d450124203c0c821011381210741d60b007070002ea040b40500941d03280807c1d040c5c6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 565311519 1250 565310269 565310281
    0x70b0c1002031008060702010c0e04020f0a030e071e150c0b0112020102070e16021606020d0806040605040e10230403050309010f02030c04080f030a051c020418020a030e15 75
    0x14000d1940658440ea207462070640c1c4505a5117061000c0c1c9281d005070759943c11010301c2e160300803507140390722106584c00d41c501501598901000d1103100d100e401010303070310041140745035400e00040e4000c014414040c1050380440c0078144d08001d885c070234110031500821614409031f010b8600503640c81d400140c2010907a180000400990041e00400c030f045020f4030401085840c0c41900070350103180890170492002d400d44101031314007a000c200c16482e1010414040003501c2c2d00284480c205400761924000945886003c03c024002c247c002d0741d440360801c80000346e1640c00140305a00c2d52140030b0b080c48100060000e046034207000041c00c0399440a4580003501182c010002160030080110000400d903030342c003218200700d03041650040f000030030000d81041103c200b00a42d0008821101c00b4500d4185051030180541c460403101001d0886038180e05141003105a05680080c007445030307070040d40d5036003401a8000394003010740710012a140540b06001c00200140d40c2c0004000d41a500c15191505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 565312769 1250 565311519 565311521
    0x6060108040b1810090204050601171902091201090c06030213050d0f02030d3203070f1106010909020909060402030a170409241a07020112020c06040b09070b0c10 71
    0xb03004103080440e80e840b0410341d83c002c2000e1140d4a50003000020a01d00398410002512405045281000301075461541f008010b1306000b60000030101c1c0b640d1034544000a03d43c00b0f40103c60207154800c54180e048501c266040d0402001c0300d102d025011080380c0ca4035410303004c900410030030300c40c11042500c0600c403030304040401c0d000c510302541c640d0180d424182d00007480c10054041e620700182c612008050075410090f0420600d403e40300c6e09081701500c41840301051302008066208102c81610400b5001340207041500e142045001603d26a40e100c0b001c1d08080d14618004070301442e80407001038072016020440c80d0180798018064008202c0c1c1d84c07245460212001c41c020883c040c200000600d000715403284c50840101e09004050341c440c00084c4202040e25581721142e00c0030480b6071b8070058400d400440d40c440342d0900f000e0101c100700b50619802030084c40798080d140c0c800d440c1800140140c40301c46034403079904041128540c170344442a00256011714000c1e18425407082c00c0d00c900b1a009 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 565314019 1250 565312769 565312771
    0x305010803030c19050702041503060f02070b04020d03052206080a0b090a050a11040f17010c14031320120c2101020c011112010905040201052a0304060201150806060108040b 76
    0x200b03160603406c0c107806800080848400051203036040702c40e00710800400506000b10f000c00900c0d00c204600b4107106442d0310108a000034002845034240b40040d00805004a069585d0781c5944820200c186651580103d0707a40b0701c03402000c1c041541d06000664240d900e0181c07107850354001d40046002d481d988004000f0b032101420f2500202d4031541d001544c11002c070050030042c16aa041200140d1170402c108050502e00d8030a081603074140344803581201e82106800348609071004c0016920303a5042c4107042c072803000703640c001d20600d03030708008541030a8100321080f85650110303504030078046c00d0701d82c3c1d541d60081c80d05180d40203001030040c040c4802c0c0800c2d0445640100314001351804603a05410783c01c480720a842030780141000700b04c880301c044440405c3e030301421000104010505184e0006001c50107203029080c4158030101c03807003114091802c64900d49071010001c41c0e403180e4a540010b406003500d454144864800c00c903000a41140003e9110f001e84010703161199140c545489003803a04070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 565315269 1250 565314019 565314067
    0x100e060a03080a020106060305010b121b0d0c2f1009020a0509040f0b0c03040b192306011101021c020c12130e01060507120509010e030303040c060305010803030c 71
    0x451140d00101003400c0700010a41841d007540000b07545403d00c14060111803040e08201c03440c1d80140300c1781d800607810055054002e00151912288400701ca0801045441000c1038038081904181c030f032620f11178014007003108444401c1c41000c840502c0b4007030380a017601c4091281d40b5560044645c0300b0300034034561024400e5400600030304070050f12480131441c107030401e031340403a45a0b20401040c0144408101c100780c20241c010ba5031440c600b404c1d00c030b1b14440c1002820a6070100341a624a01542919900041c41c101100001628016604445281d00e080407a100b6012440116502e200c0050602c03c40321114039a103030003105203028800c4100250400c48040ca12440382d610840d40410200026204007000010700c1207400f820080d40804032581039014106008003401604001941040103040342416031070450b0301c0b00ea607000103c492040310074189803d030000200740420300c00321681d21b02c1501c81c20345040c0309503642e4441d155a00e200c201e035590089c400a2201901400080004c0c6203060 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 565316519 1250 565315269 565315279
    0x30221060f0405090c010816020a02011805030f0c2b0807032c0f0103060305060f0c0d0c0203090a05010908120f0409051306050a061a13031211010b09100e06 69
    0x40365140105084072400e5500c54003690202042c5d5445691000c07599520400341e0f52080d40d20300c816200030b9619800d500009050140f1a00c40c80c2c501458842c0e05401040010100c0d0202440199070b1511514040d000c180280780c41c5002141c820810780b0000c40d00d0300c0d003410035030280722541c644130142d801c07016049040090150740e02204586081c01310380914094103a04103440303443c900b040344d035811010342e0b030b41070504210b400c0012030004500f4641c0304940c0182028540e030385c4903811583c0d2103050304c02d180c1540ba00c0041070b1a1075000029144544040d1220800d1a859900545440781e0500c6103903940c0c0c0c05071a01c02200803211010b00648610021407d00b41500c901844055400440d40e01c0303e00200b003503502040c41013038050944c016441a200f04805418403101c0c5659218907000801003060004500070361600c01e5541d03400941d0008044111030f006440020260710685081410640c20180084414036001c11261b00440400541c0f40080707150066000c0c040318000c02080d409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 565317769 1250 565316519 565316539
    0x60501140a0603020706020d06030b07020f060c0d02090a05060408010c12151203050403051902031c0e06180d030c0210030605012a0b0c031017030a050319060308120703022106 77
    0x40c0014041c0274051031050707519030b40c20f181014000b031030042a00300144030f82e40b100040c0200b00403e101242c5052075900405a519910b0501103030340100340364406074011000080c00540980d042d40040980c0005650312226016040000002d5035442e400d940141c0300d000404000c600480703032001604602c01d041490815030f80380c44513400c10120004102c0c000d50364200c483c046140a010381800c0120090701c04c4110ba07116540202021a0041058010407001504d080352458171181500301d0b500060255820340640d160003844410f04a004a008040c007404903080d2500a000d404107a4006a46841282e4039144180d15100100380d913090449882081e03031400b01d1010300d03000d445075001c11080e9607a8204003035441c0120110f40d01410f20014403a24044948401108aa043d1016442c0154490302da0201801d5826a51180201c10f585031107000800c01c00000e0183c881505002810b21444d503a501c0e06609034072990a070084d40f10703c00c030044603a1000008025420850250001c2c0718 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 565319019 1250 565317769 565317787
    0xa0b0105010f201b0102010219110a06050c130b030c030601080a090b0403271a0310180b0307050d240b0310020c0606011b060c050d06090207060501140a060302070602 73
    0x140c1100260001001e4001da144c654046510380040040c80c48284021490b200030403141022240b14415808e041200e003003a00c003040c0c0c80810140703c015810010070041414005d01000300c035031042c1c4401008014001c00011550104820749103c0d50b144c043d01883c43d961100112200c500003080d4400c1160344851140100700c4000c02e1501c40c510a85805455854420914038881f0f0b0030342c0c0300d801b104502e10f41801840000c2405800034008040e180e5200d45880813003c004910380c3e0001c0c0804400c059050b8000e0380c80780c0001b03081e21000d509640000340c540051155098540501410014140c815141c50000d807050242000c1e00d0f0842c0001d640001030006801c000002d20703501e0030382da00459002c103036400510001350403d03800d0a108412426450300d1004003840c9a07006007406545005185000380500103c560100e00103400308109503d40b0211070081d0000fa10541d401860200041010604a00c0750130351064020003c09240785446c0080340658000a030440300103400707000c0568 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 565320269 1250 565319019 565319057
    0x20907030504213b0604050a0905060d12020601060f02120f0a020c040c200d021f11040f080c220f11161e020d0b0c090d0803180a0b0105010f 62
    0x2030052140c06840100a041d110310781343e46600c007413103620031031007044104011346c3c421806500722882031201140c6036032110f0008000c100045005840a02e054138903080f00c640c0851000d05880140c0c49a800d25108000e080741e0341c2a2007040c03415448000c01400044a042e04050000e444061044818416003071000ca01500c03014500c900c0440d0524150a0512400c094502d50111110f00240070104104900a6940440162501751500c54441c0e03141c85c02550b401801d00036010f1445030390368681d240b10003001c4507550b00c0b40f0540f5005884002c003007460021492141003100340c0e070401031100000507400003000590100a10240d0352070719080b025400d0707800313800f819000e6a90300d00986014100441000e6455141d026149041d000040060342da0010046074030707811108184441d0780d40e9010590038031440c0089944000840040e8082009032002588500014000c5010714001e51b4141d665801c041107004281603405001407001d035104005442020038685007512522118140d202 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 565321519 1250 565320269 565320317
    0x5160509061b1c020604020f010e0613030803370f0f0609020c011410090207140a11010f020d081902090d1101020115050306041115130302090703050421 67
    0x845203401102020400c0060528440c0f80b8024074009410726191a600107141400e91264581c180190340d2001a066103d40096a81040d5510441d58545440307003041c2200f5042120750a1889980c02040c52100350450380c4120010a8a103000001261400f0808064091199900c40d920b130344035041c40740844036010b0140244080400140da138070401d4185801d540484042c240008000818400508040200d103021640001801600c0d20340c18500031003403009200e6020b40721300c0b600b140c2c14240041e40b0745c0500d842c002600d542601d80a00740e8241d0711100a05403001c00300f030440002500151031084092503a4800600041c9400798072000905888c0720088140c51040e821155010740c1d5070248034000f0340d083c110317481d410100c1c41c110000b590f404000300010460061914003101326115040201c00b0616080e010341c0d100c00c1703104005500405207200580c8074000d2903000ca140c1c18003921406010f1500f048209100c0041985210a9184d032603000100b001030b43d60780301c0700440c040d440032 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 565322769 1250 565321519 565321567
    0x18060e0c1507120503240a0b03010605190311120901180302030c01050a0501030c0302190b16030206010506090307030f050307080414120c0102071202120105040609020111010516050906 81
    0x154940e101c604000c001c0c119483c4150041c00010014480030440c0b80607007005034081c0022507a94040140003082c0c8a449941c040018841c0100c000b10f90160420013601e54010401441d1451651050048041d1005070400c65a02403080204900c0301004198550744041c8030800480c2c0190914031115000c01216029001a0408240c00504001c01c2c0078031500980040c400380301a504640392840e5145191200034820300d80003070040000c0103640200e03030007001d02000550f120110700c40c0e0705c40100e20840d0200c2c01802807000100d9070b07140910580704100b1f800740040c00d0143c20350351610001d90544c90291800d10040c020b20b00003410107401003025221a130343c145840c030490003e10000302e4511600c1c1c217540d00140f40710b0710166400100c50007210800c1301c112040010340d0000c41c203a0003800440c100f0319401d080401003400000e03080804503a10030707603944409050700c0091030308070340055882a03142d500c000080d00c0214401c8010b0311845a0090400703103449459121640f04030780c3c032802 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 565324019 1250 565322769 565322809
    0xe0c0915061b0a0309060f050306100e090a0e01060902070b040807030203070501051f0b0a020a081303020d060504051212130312090b010807170712260d0f18060e0c 72
    0x2110704150f48207014000800a6040c4000600c0100701f014107507000082c500c5004062400303c1c01c1e0820b206194001070704a02500d510740c103060a1407254068000c0400c031007050340c01c0c00d800141c1d040e04c91003181c2d41d0720b0b04050005200c0d2960340c0c1c1c0c0f2906902a0000f42d0451000740480d002140081c81118050542c144a1810b059040b000170803c880345076100c40c8001c1b01c180f052070546900801c4500c03000d50b100d000956035211001102d150b030040ca07000a504481004c40000410035a580094003d038001c404950043c0e40300408010b0500c20a1125100e0107140e1010032128842c06544841c103500c43d081140d01502a5640d140895016000c01e44a010307101004102c0400c0c103002d07a03006442101c80c0e0800000000e0300c3c00b035913041c4c1d80c8101d400702a80c0c000180c05001e10000d00c051500300040c1c2c6500340030585403003551660400c0c0045d484003490030107a460030682c58480d907803000c1c401c100008030070122900e44600802e0500f65014450042909840c001da462000743c000e541c050b002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 565325269 1250 565324019 565324033
    0x10905010f0906150c020316061214010609030b151e1503071b050f0a050313080a15051905070c0b0f0405071205030f0a030f0e0c0915061b 61
    0x141075104800280e0048102502d00442842016120801030000d60903904184029203440e1001c00e00d04070782c4110701070b40e980603004049040ba50140e61b00030300342640c00003841442d110050340c41d41d208081c130580011400038002000040d03641c0c40427690100d0071820a0004459240c04a4040b82c0d60800e01031000c1103464403080240b030008d00d11160071160a041908618050802900704008071020500401e00c0203040020403408025145070136246074181c0d90040000e180c580c2d40d84d0002d441d508030301c00c54800f0100300b810000420002c0c95802c0070046041c62001e504150051401a00c40c81100010341e038035007040803290044501640c00c0d0b03651001c0325800d500300031007800c0c005403641d40c0f80300c4880c2c184800318400160788820745114403c1007a082030700b498030520f1441101c502070601c00c4040703810200250142e001c410301480c090002c0c85070048420340b2903203a00321102415400580d6a012400b5410798081e403420210014103200d02c1c0202c1c2c416404201951038a0404850307004034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 565326519 1250 565325269 565325279
    0x30406090e100e0a020d020c0114010609080a0f06110d140114010c051b0d290105030105040c090c030e01020c03070215130915050d0f03020105011703040b0706110301090501 76
    0x1107066644585030a001c0c1e0251030800c0040740d26844007a1030300c0d101070780100d80030500c2c070a168125840080c406008210104184460994505092007071001141e05c940000030581408550b071403c0c40d030b2000c11020810f0307550f500d0748000c0c425445201d4620b0030600c140c19200c0420b2080c203044103103c0d03401b401f081d89403108510100480303c1034141000001101c0310001440040c009591900d25030203d00c001c84039201284042d94010341c0a0034800c03a40c0b00301c48034420030150051400b074030140390711003580e21101410700f81c072815900100031601084080049203019132210f50a40c800d4039010071840c00381c130516420398114604486c400d410002c0c0140440c94042c40b1107107010700e00f14400303041a0791030703405928194a034810060b80c10b40381e080c041070f0302e10000c512401502d002480e6510040c00d07400c100291559440c0d00310059881c11001248069024004d141000e200c0c030000d600d0207080425010940c0c10442c821182d0503140d008a845400c00103001d103003e0103015600042940c900 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 565327769 1250 565326519 565326539
    0x30f03080f0c0408150604140c0301032102100c11150f07090308030109020d020706020f0316020c030c06070c0906080d031a010c02061b011a0f1905101103040609 71
    0x2400080c85184100300070400c02c04007103804074485030700d85c61200301340d6501400704025124000030260540028010070010500b0403000d18140c078000c010413500241c5e0301302d000c0c1d04c6441600203c03001d030b84000050113030a541a045009680c0c0a403034014182c0002103c110302d8141520048034070b480600e8100005008030301510350744005507190003040c6518545580072184018010400d0454000075001031104490301207840b4a03501c0310f0110b40c1c2c0c40707a0f280141c095400c2a59031100345403c8151562000d440025446051600103002d004400c040340108662684418003c584c500b02da11800588900644070fa43e0042aa020241190505150700201240e60355551003d802c0c00c0f4280c07501240c3d9104242e0140168141c070079582c0c0d45031000140750005100300600320151300b03115000303c035503000300d2560341122011307518040400d9076102000003c0481e0900c3c1e860b40b005030071040245162042d00e69044a503981800511424a480314606550098100d0000320300350b031104008444034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 565329019 1250 565327769 565327771
    0x1118210d170f0408030901020c03040b03061801050a06200105070e19030b2d0c130e060d08070819051e16120215180105180c19030f03080f 61
    0x590340d01200e28600702040c8038040350b020300050001c0c0c2021000801c090b000750b0441d18000800c40450f921a0b0b0b899144102a60080b03c4440c081d001d882c1c6d007803042c56188505141038a60080c0054499400d001045502103d01071241c0c4c0719420700d800b0744d00804428401e4500500890343d40c003e0320840380d001e03c081c104a0000300d0500d1081100d00304041030700007142d55081250035807003450074101180021021426a01100c0f1140030010504c131403d010b020040c220683d404004111403956200726102d040c40c11140725800c801c008030080001104003004208180c82800303002c0c201300e1420b400450a041c0d03040c607400812400291040c0e08080c401c105419443c1da114401e240c603625445100714010032032401010308940110010b0301d14002e10081c070985419590001d55450310029800f040a49202699119480c02010426192040341c0c106407a201902c0202100c00010f8180310085450302c03019060191580808000980e0b492485071016010340e4030300c0f00e80d09251940408182c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 565330269 1250 565329019 565329047
    0x305100b0603070206060103090f1a010e160210090311070305010902040f09120e03070b0c011506051207080a06031e02040c02010b030a031101020405032505041118210d 74
    0x14002c003c940381d40040c00e550721045c207180c04140d100036440c2035400030340c421030000c01c007010343d0075509141c1040102c802e04a40742d003410350701c581e1182c20030708507107400c011120401a0040400742401e414941c00c03d0b0760301d500c80c0c68001251840c0d118400d050ad00709402c1200c281e51201c2115095180c0f6000344481c0380f400d40720400000c00c02da951117209a42c10b958060601c034482280100d40d5400380b04490007440c001c0412070f40c5464070499207008000d04d0070380c0078110310b5804010800318811820354910f0283d2a000c00c00035107e10006851900c00208100c0300b0584a02c800700c00aa08210759202144400e034400d000d8016501c100300075110b04289640c11680751640300f5565030390025100d42d107541c06007401501da50031244014064400c68204a41620031082c000d100c500d40e454080e40000703d511040b40d0820384a9080009036130603509400d404810034130102a00740c5510889540d0002e000b041a55440002c66141200818000315601941c0103503107081d4241e600050080d110314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 565331519 1250 565330269 565330279
    0x203070e0901050c030151080a1a01141c020703110c060a0309030e040e06061806012015070e03070e1b0307022113090b0d06050705070c0305100b 64
    0x243c14403c0c0e00303003201101c0481d00001059501407c124101260345460903025900d40d21781000b03000410344d134138a00e55400c0c2000043c0404001817168030309200d2164204481e402c42c1400716087c100440d1810f5140e4050000f140d810020900b01039403c040408130115205400740e1143d0b01400c018001044201d10303a080c0303800103030b2103071b02c16030b5602d0494440c40c0e114180006c40c903c0c9410116070781350078000701d1604107140c400301d00319901001844603c21102100c100d406001c0319140000e00b40016141180400c00200142011841e009121480728030043e040f105a0b0024603005070300322805031032a00100e25203d0a030100341c00c003400044041d001a4103258201d003000001583c10040b40c000c41c0004000c080040398099100340403440102c0c0100316180d24040701500c1040706a8003514090794012215100040d005003140125450504020701400c420101c54551f81b010b098000c00356002c100c020841c890002ea1940b00040255024100031f007291520884450b0840d4102c41910740f1030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 565332769 1250 565331519 565331521
    0x1501030507061e2a020909070302030c0607050d12110d0504150b0a09051f0308120105011d1e10120b03012f160605090d18030809030a0203070e0901050c03 68
    0x1130b003181181300c008030343c0c208210041d099449161040e0890f42402540700c01c42405201134050002628011b6034000c1701a285035103a508104034151140c0c1c640101aa0410845046100d01a0b04095a1014000301c0461070503c091208072082d40024502c00016654500b44014460385045290b58a4030100c8200044014070380044e07104d46452290f54049501c500024035100328005415400303007070044014404e203407245800e206541045441d44248406075000003660f40c030039100b92011440c444070303100e0404008824460070300128200703006000c0c220f00f186500ca0b15850386145621034680d80d0030120b00415210350040e900740d814003d1080c0e04044500710385a03145460b0004103900044201c00c000510300740ea8001d405880022010f4800d00c03d45d0b6410b12400da00a580318040c00f0b000c0c1c6030000c40c1018181c070090307030009581240042c00d000a200150b404002806201c500408540c04070103d603000a140c0f01d0550000f1f1840302403032041c004410300074091280c200070240045c80c19 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 565334019 1250 565332769 565332827
    0x209191e0e07060306230f0612070e03070501120c0e100507200f190f0906051212030604020c010b0306090109030809030403050d030b01050936040b0612150103050706 73
    0x4c3c1140c1b0081861281c112036171041165511621380c50343c0304002e03210031b4603039891981c4d440c41003100b100c204c0c0120701c0f002c005442c24507010805009940058681c070407055030300642c01005100d0340003081d0502c89170040c84202c5075a031050700c0411810b15a5001d688609600e0301720084070320b901c402c503043d0200c1c1c4040882e44d501c030046254400340a440e0100502c0920491070407000980d03100c054070710000f07071003c00c40c1441c68010f02c0a0f00c0c0309862140d1806c44000f03c660340d0380d00c1c211801043c1c910502c08100340f0b250980050034100b1500c4000300f0b41041d62400242420000e440d9504260364134400e1108042d04524415840000540514101440c680301c854075002408020310425a9510421549e41e00800940750b25200c040d10004200b0900a1001070034480100c1c151145040d102c0108105810960218401c0e0340c00090160540c560009018000e090803c0d03165581c003030a02101075050320401500d0003180100014496146888005007113900c80d045030f60001040d215000075 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 565335269 1250 565334019 565334039
    0x30606090f02132c0f0403030c0c0c031506050a080d0e01170a020a14160b0109060f030803040f0b09060609010b07050615010909020a12060b03040209191e0e07060306 73
    0x401ca521004d000d0b1884d2418640c000100098440d51240c00000e4006100d0b000c0840c0c00002d00c954401c3c0c90401c000c5090070015500228180e8009040441d0340780184002080005030041c844600500450303860f85a00000301c0181007900004002c3c0d111940c20a02e16500c1003607100010400e0030502007c289560040401013801088480300c0b540010361049034030b11414000380c1d801409000c00752502d250718100c0a00454008c0b045c0d482124020000c22030407100e02c03a160803250841e1490942c0c80c07a43c0e45600c040e40000b00242c0d580014200084003156145070344500c0b851106000e081d2034a013500410515031410b8011401c1048144a06400690300140031a00061000d000151044807800100c80d0320103980c0002800a0012400302c8950303070000904003100003013074000c0c45195103c07141c000007400215000307980f05080c0400700c0d54060301d4a03144e8aa0080151020924546101030030718014180c42c3c507030100c6a51760b0800c0d85005003d000c520017030301403403800780860b03864118481 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 565336519 1250 565335269 565335307
    0x6053102040f0e09030d060b13080c1311070b0f01081b131805031308010513020105070f060b090f060102010c0c030207050f0102240603160308070303020f070c030606090f02 76
    0x15198400b2000070036013900b420802c5d59440c01601c40103000341c40d104c1200d03090030740160324042c044845007c0c0100d4030200101d000c0c240b400010700340449420320350018202030210408800080602001000082071001d10700610036003840325002d02652419400929210b60762441c0942c03d80307804c1005a82c0d503a011a4800340070b40c4038601040f42e49a407070a0448402080d030b8010321a11000500c8440703c0c081d50005000c84035604000c000d25078449521442c0c1f121304001c02400074008121100008650100d5041854043d12000400304441004115080d609884503594a1062000c206983da42405078245542c1e01e45441901c0b90314603940030755100c82500402c0d02c41c400703200800b00e09910801c2132403d4081114094080e04290310b0911090180640e00c8501038041c203008000340380c20f8901250304a941c80b035407040c40d24496460890094005200c003403015501007014201040075910350002840c09114006038407850071008804035400e0100002e01c1078014024600d240c030300e1000b54 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 565337769 1250 565336519 565336529
    0xf020709021e0903010b040905160e0f1303090f091b05131503091709040506010903030807050a0c050a06050a0b0f0607080d1b0305160c110d0606053102040f 69
    0x1510f41050302c0000b030140503954010f54000346049951010b0050000e1490810000710440b480c4980c1c84010745084035900310381c0c00c50300d0141140071812046600000701d80d114028500050010b440380e00c0340d00c1301c0d011544050032180c1c41c2c003c4144454101c0c6888144442c41c0d003411860820b071815521945a083c9c4100170f0041c0c15240c2c4120054029002380140d1980512541220407080c0207881040d00404032050040d031400c03000603c554021580b10702030700c3e019141d995445d40e400b0b50840e02680520300480811035100903480018408120403036030b840c4900d102081510b8140400001c07034410041a5208010359070555103152a040b046030a2a5003200c0e100d5940d20304191628080c006041d010744843c41192904038001da4190300c0301e406015400f0700c02048810340c94003280d55141804000d80495003890810146207010481041180d01c9103001040c4260344100203540c5665911390f501150390800f00714030b51503001da400b0788080d1760907840441c105810190120b114000c0c0d8061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 565339019 1250 565337769 565337827
    0xf0f0601081306180f05070b1e030405071a0c0d0306211703010b0406350612030d1a04090f020105030403120213031b060f0f050c010c0f02070902 64
    0x3070101c107401400889200c298009042d00da40d161100c4080c1490034150340c02c0c041c5807c04a108028a01210f0013803d00c0c2181000390340c01c0c205c10812584c406841210944510a030008a410071009410082000118100d460300704c2642c180f424641510440e030101483d000061018082d03240c0c80740355617551242145c01650051801d0700045110f0881501181c1012000091900300d540041083d00c0305a03680d070710040c042d0740070040d50305803003450729020602000100c000d040d000f000032a400003004240c1d0322806041c1c1085401c1d507204043c6024926256452180c0000d00c2c0a005113244509840c10400101540c449035011956194000c0c10000000042001e051041c1361441140440460441d07640394015607801c0c500500c2e1000311502d02d0b102c0300714a94001848600c80440310b0359120880c41d001580700444134408030000380f03c103000c4140042c1112603004d101c0d0720020140d50700c03442d40c658040d400c080c0ca0205560f21a01c0c04600400c07441100342c0b03c0000500383d207009421 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 565340269 1250 565339019 565339051
    0xb03160305010f180e0a0503091005040f05121e010630060c140a030504030306051e09060103020c150f1f0e10120b07031505030c060a020a1a0f0f060108 67
    0xb030162044017180d40e2284036800381d00c3c00384000030009169004c1c01f20b41c1406001c1e00c115090720381d8080d031b104080c103840c1800070402142c107001d04100124007522007076844008950040c080c0588101d4035450550399a00c07c1842894007807450602101505200d030384007010031000b4004081c42c031050040ca07c54640800c01c051900490b5102071031080500010344404800d6001002801e08417030680019003044e600042c14200403000d11900d450242c3d04c201a251018144000c00c1d0003d8401c0e41015800c0000801e104401e004400c100040305002580c4c505001c81c0e07010311018040d1401710302c001a4810080280e03941c0341c6035000c030b43c18030036506d29580e54085d2001c01c28401c3d03402280741c1000e0407514010454041c803403522584050310100120790309020140946003840c081d00b6010f91280e443c0582c02d19140c030240c0041807040c812101c0440d2036a607150891040464072107582030030f0b034062014080340e98070b0306640042304004c0248070b480e00200003081c60380c020745603074200c0c0c03105c01d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 565341519 1250 565340269 565340309
    0x42019090302030304060f0311071208100b0f07050708300d06030803100605041505031005060c0f06071706270c1305062d090a0b03160305010f 63
    0x40d410030003503400400741ea4a5030b540e90070141220029103100c038000380c0b500755950750540b07034201074410080e080304007081c2e400200c03001907d0314070001e00f0f003144481c0044c02c00268003000e03600900400200c4484e03252600054648503150103103d400ca0070090b0000405e1045d0b43e40021000c0790b00b000100710b50030200540410714003161088803650360300380e814590003200340840840154024900105c82500c01503403124200c0c0c0d45d0040b4000c02c0c0fa40040b560000020b244200090341e00280e0340d14003080c100c0d80e103100088a540c06038048034803503000031003500680c46092040c550b02c030220381444e00e4600015461140c65400c003c000a1080c20302d1060b0b01d201200c80120220030901100861109040c444000e085542100c8104204102207c0c40421581400c20036500c6c01340b10300508081c80c0d82007003a00c080c0d10000078500d0201220074007100c40260b40d5072160303030010240b03100500d44c1c3e82840e400140120b03040c5514042070600744001003140b82c030060001070840e0303002200c9001c040c000d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 565342769 1250 565341519 565341527
    0x16060c08160206130302010e241e04080c090109021c020c030c0a0b01170a050d0819021201030309082a0a030f1a0f0c0a0e060c010c030b042019 63
    0x102502a400443c04280352401214000001041d24002d0702c81240b9006c04108000d950746a1480f4101002c0005940600e2240b03c1c80141a1800744120743caa400010707031080045580065010140c1640404c4143c0b010703003044010b1034094141d039030080d031402d4103456241002c3d116001d40c490050764009110001c102d424010388045510210680d28601c81508001e09920030a01580c1002c0e5180740d08034000900000d600124554408080c10b6002c4840c4019100c84000515a010345500c42c07089580307540f440c2c802010720640c64000104ea81d41142801003c1c64465000100503500104001c0c0d610500b0014075100441d60b038401c004441103200105070060b82550000b081642c40c1520074042007401d650681005503000720b00300c000d036504007a55410741000e85406030328039001c0058040e014411504880308500150032249001380d601e1009084980f24943e05c000207560304940362203460f040c0144003220680c0c4c0120030f0480d00b80348415800703200c0c6030140c4c00600c00c0c0d5040d42c42da0f1406 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 565344019 1250 565342769 565342807
    0x702130209090f0907120b0a090f1401020c12040311090c0c030c030403020f030105070c0b3105010b0102030306101d0901030f03030b0102060c091e0603100816060c08 73
    0x9401c1c1c00c4607080800000580c83e406070f030113a03007500408801244220440c86000e580507001034000e003050b00c2d40020341e0010000b06a05840442c510300e45540854680100161002c403080c2c00181c1e00c440380705402c1c3c00c0c8440c003191049404810001080411a030402c0e8911018003154040e043e42c5840c00c1000f25480382c240b0700480740c00082031550811a02201070f0040f68020386002c140040c2120815080b16400ca0b01d82c0003051002da913050200b1003046420754858440c3c0154440c5056805d601c10b06842c0780040a10920304201c0a072040000a0041343c035801020b00045095081c4440060a02c400c04003400d010042003014540081c070300b81a03080e44c41071025141500c2540c42c0e040885442400b804142e002ca410b0501c1e08140e944005401807041c0ea034101142c2c01c202007001000b0401100c0e80c10f90048852a0420303c0c0e150741c40d00700440c026070460b003019018a15102800d420280501181c0801c08039601e4104681031300004d2449410341e001404654076125008100d1844003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 565345269 1250 565344019 565344037
    0x5090a05120708060a142d0103210201090b0606070501060e010308070b1806130f2406061817210301030b090a0201170a0603170706060501021207021302 67
    0x11519184203a07060046416016510410705485196440041c5501503420000038034040d065480001403042146140e2240c071080408820f0b030103180215003845881c0000c1c1c00c1500c3d03040710803007005009049620700a094080600080c803d03031003242c03600000608000d1096001f004005a5003040100c02e602c050041c042d00301041085503183e0803c0f00144e00a08011124401284007040c00075164911000f0703080140001408140d0303441c44049100041c20030b00326110b1505507001c01c000b0b030613080c1684c010403020a161220090001d113000c10398820b0760069050141c80e40040c54410b40907202c0a0a5809480f519003c000e038044a091500c0041284042c04040181d020323201c200d504401507040b40c0c0038a0070700c20113482d041607250b11040c400d20000e001c915000483c0f2a0b00e031940e180c1c1507021070840070002c0c0305596600e030001003410000c10b9140c01400004d050080103d1481400c020700028401020f56140384440e030031036882203141c01707807203020003030522448010320760104d8417095 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 565346519 1250 565345269 565345279
    0xc0c1a0c060103080405010906170423010e061f060e09040203070308040b0910080142030506180402010917011812030e0c010e0609040e0307030f0206131205090a05 72
    0x1683d80c0c1810b41e66034016001d61800100d4400d40018618828031000181203001c0c40a08407079180c60351400850070380c105050a0b540c81c035210000304003a007031240620307140001c2e002c0c0c0300500e00800c298200d00101c20b090001455120814030003147d001d03440c40b580d0402501c856807203482e1400002c0c50035009900c018080f10b0005030114000d1840c0c0043d042d00e410640b011050010046426100d81c10240240e1440100c2d1f205030011b00128030300440740401c49590610a00c2d464111400f42c3d800400c941c8030042910b0b58140481400c040242001d07030100b5500d0a41c4074242540001d00c1c0951a2041c8041a100c80301c80e4048200207500800303241e18039040600030102203150000d408105905001e012914103028104c9003480443c041c0400324050391030a200308504c41c104500392300034400d4150800c1e0344102c076044008040004111740c9000f0b40750b004848414041c006d02d4501d008000701074407240710807950009550ba22554260744014289142c450300c1010110b805c01c01c0a178071943c8e200d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 565347769 1250 565346519 565346521
    0x19020304051b0a03080f0912030a1823011404090513060c02070b0912070f031b150f080a0e0604151a03280605190c0c0c1a0c06 56
    0x700c1d000541c0550850451860207441c51500c0402c0b0084440344000380c1810320801c841c909007085200140348900c0f006028000030364a8a0542d441d41d045455003a000c2001d00765580c280e4100d0304040401850130389010b40418265020624203407400c8812035041c00340303120504c00f5400044064402914440100700014038081c2c0740c1c10520184a44266411898030404102c3c281c03010500740300761030804203510302e02321410080c0710f00c407403003c610800b660140c10008912044008480d0b402513000340364010044500b0282c0f039900c490142e025040348645286081201900119008055052801d107020305554024000340a0102d03c0c055101c18050078003040104003003600a404403440040d400c12541a01299034524022658030130399069000481002454039000596038a52200d903040491001d220342c0c4081c2920f5040d07880319418220005800c15090740307449140124001f0346462824082c0b5500c0d8000042601e018201d003030040d13500481500300c2d01500712003100103240111842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 565349019 1250 565347769 565347773
    0x501050a110d0e1206040c03021908030d020c0d08150f060c060a0c1206030507181d03070201030507080103030c02210d0306140603041221020a020c010e1c060519020304 74
    0x101d1642818058820600c41c00c40800b24140000e17820303c0303284d1101c101c09a080c01c1d50200040400e0900c0f06142040b07020b58041780c0c03501c0038400350070000ca62000258840b072600030404c0c00d00300705034010f00c20801e01d0400c02140b0035040301000e40649080c0ca4403c00700344c68a0104006220704855441144508424004043c005520020314400b00b035880c0e2000159072095101654014400940140d02c540030a1001c211190141c0039500c0c1100c000003190390b003800b40280000c0c5d05681c540d5441e0808940f403403e5503058000d095100505281050702e80d819940d025000344ca100e4406030180d4842420700440b50039014514543e0601d08003141e4840d0786441004000c2c120750b000f04d4a040700c10307003100d20306801d02d071056030301a59103c1200541c0e820000350072186040090418040c3c0e514031040c41ca1401582e10003000c030541650301501101c50880c0001d0009100425028040c644008802d03800200b01c2c20391194040d40702c1c10120310380d10f4641709480c111140d000b141508038030010034001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 565350269 1250 565349019 565349027
    0x415050717060604123f08060303040f0f0305150105090403030209010c05070b04051801060c151e1a0108070e0402180406092c060403030b0d1502090114130501050a110d 74
    0xc0d00b10000b2000300c03840180c041051b464200b01160031590441d0310070200041c80c0110901d0780d001d080941101c1c00d283d03070361605102000f50703a44561075480b811a021300c2484011301c01c8840056a840b81d43d00a0351501f40450b4500e40014005410141d0205018049a110301000e541c1540c10404a51029031581c40c2d051059200703110303051140404c50f0f40034400510035005030f0704852150702c0d02c01c0c3c0040e403a140c244581404100c000002656078481f4222001030910b82c48103030716161000a43c1d0307100b00d13528111031051401c460381442090410408003d07484003001110403400d480243c0c903100c0c401000c5243e0700b0240340d4554003504203040407a604509901001d500b04400503440001c003010700a030200315a03419080110f079000307000081c000c80d0090b0000c48107008040c0c51504452070b662136505107030090081c52084140c00040307245546d0307444075403500038461181840d071500c21030000c1003280341c01d148699418480045a8449003d0045140d0261030b4a100d0945683e4910054020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 565351519 1250 565350269 565350293
    0xa170c130f050f0301050103171606050103050109060c031a1302040e0109021819031b03060c09030302070518011404060b0c01090b010b090d060e160608041505071706060412 76
    0x601440c0c166180d5002c504c0c0c140959412a030304804050400000f407001c100d034650020b1400f489007185009007400151441c81094004c0d802507000142858540c5044400e940b5100d00031000c15040c4a00400741445403000d401d01004d00301c891010000c5c1c0402d01c03001900841d88600512480c41000040e200150340050039a0071980782c0c0d16048805274020071100c070904035590000340104000500028422003618040020030a03508050725540303655420541c0c00420443d0001403070700408004140d01080004040c0c030085030400c4810802c1d41c11142c103000c051288101c0c072020390700c5003901c40d1903690024028020078125666143c0044104a01802c400e840c112440340201d00002001c3c3c04000035900e069500400348140300e5802e0b01c4080151030a514941003501500410848550040610b040107208036125085549030608000c2e2200d54060b00c840d0f078a41c2004100b1100a501115070181401130002000352500c40c032005c1000c030f00440d0042002100c25070b00b154184400c1f40130b48 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 565352769 1250 565351519 565351529
    0x2121f170619020a021b0613030818040c0e090a0e0307200109050a030209041a0921133305030919020f061e0a0c1401020a170c130f 58
    0x8400c88018648010381248a00380304d400041e0001d03020031504000d100c2c07408888000080500b820410011464103020304154011564a0800140041e903900e609001056140003260204950445500e0141c6440c040d0b00c0c03014030440349940041c408100030380c0600c80601c448000c680c1c48010a203450b00410307000350100100c5644000020580f98030843c013407025038001a10044030395185a0a00c52440c1002c0d1040701d0700800c10080341a8205010166403084800c00010300b01c0e210080d08041c44400d0301881110750303100c00c100d8010117840c021168030032100c0d030100940b80c032524007245241d9100300340c0300c0d4941010400f40c0d43d030032240c0c00341c05140600003083c00c1d6040c002444040e42c413848441400207411100d28442e5601030b01c0c010000c1d240094120303411401c10044100f955a1a5100f0066900490190002042841090140d203840c641c59007000310706d49913280c13401500d5410580b203890081c8041c800020382181000082e0794401c1c00c000740b0401510f441c0c410581107101c0c14058 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 565354019 1250 565352769 565352791
    0xd050a060510080105040201140f0c12361009090e0703020f0d0f26070f0302011104030b0406180516030201020d090f05060a0c05060403080a05060402121f1706 70
    0xc180f281043c070449005030307416150141e45412419900d0b04036001004018002e0500707000d03101d440c09017031040701440a00d801c207599443c1c08007501045030001c51943c1e425052151100300c40383c0046540040400601104c102101410303022007103a00b6159a0002e0f2103150500e4040b84400030009440c40c2560b100303c0341440d1100341003091151240e038550307024210101c1b000c1c0b0319000c41e80c00c000d41c444c0504004105c0c0c0c25545a4840c500d1654001d13803040f0b4111505e801c10303005040d820b2045d2034090b010300e01164035051860f00c540c3c20700e14006c1c0004d4401ea1b5201c00404101404e1404210482e5010741580c00710303820101c648110245500c400d83c003600900c54091f4059101340d046ca4255507c040c1c129084500704001e0081039000526001c0500810340010000b00d041000068415880303582c4170101850002440c0702555005032155003d11300501959800e4240510b2456103d030182c1c8002072400403c03103204100d030b6680d42c4070384034804920210039000000490441d209c4d02c00241c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 565355269 1250 565354019 565354051
    0x602011e02130b070f1a04021c1e080c150103081804090209090a060b010e010507030e21030a02010b01030c0801060c06060e090a022706061308010f0c0e03150a0b0d050a0605 76
    0x291032456082c207c40007540100c1b01548282011744c824850040103020f100c0b00c184990390002d070030100c0b441390b90b025035800c030000c9401c02c50540d081180ac03003101305c031201c0c45250354550380d14441e25001d00031501859040505100c021602d4aa001044d200c1e00104848528100b800c4203039115000c690069030154285401e1f41055401284000810b040603914245480441d4400f2501045280b5003294040c01241000031041400c0400301507208038000991350f030b80450640a070031200244007103070501d4108040502901d0300941c0140c11243c0a05107201c00c0381641c64490000c0505420600340c0e41c00c40c0e0140030442d0782c001805400107109a41d01107105220342c400020051001c1004c24640f54414000341050409030040c150981406031320750b100d1034442d1800350a440c540c090402196548108400c991580955082c0c5045806c3c0c0c007903d80c00c07203010080250000d006000d000026101c0480c0d00c02621104100c1801640010658010008920f0101c0240509843c00d103003600c1291 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 565356519 1250 565355269 565355303
    0xf02010e0c090a090503160c210503120916080705130b0a050d03020a06060806040c0e090606060a0509060c0102030105150a02030403020f0409060e0c0a0602011e02130b070f 76
    0x15a081c000754002d000c108290b58006122000c2c1c05a40300848a6004c14810300000c03164654484940c64410b14104040505000440c0c0c04007c94155a144100c100da022101098000c41168401807621541403119540c041c1000d10785444c03090780c020a00d540e01c2000070940000f08200003940c0d0304580d00c80030050700340c50703131010340702050f01550b404041e00f0302c10442c510f00001101c2d21548240152011901c030fa4072043c0c2140c4040c0d102c9400b540081c01048100400340310154064280c1400d51110342c1081c0043d2a82c4c3c05009100f280600c2e0006601c5240d10300400a235039024200500d21995005036610540c043c3d0420f12545001d140003405000c22880000c040d00c80314900c81d0b00a6060514540820040c142c00d181c0454001e655142c00078041082d0340180d40090242000130180348245206000303078050035521080c00c591500e400400b10b61080918105038031000000941c0302d64100c0e054481d50b0001e640800c0c2e0304000000d8000c00c0203240c284030362000c0d00130358142d20080141c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 565357769 1250 565356519 565356523
    0x2071802090307092007061a222a18090207021c02060f040305030c0f0304060e06091f0c05011a0109060302030a0902030d11061003080720030109030f02010e 69
    0x40400281d040c0c000720f00078050040141e1050f040485000d0b01d980c61045000c0d60040720341c0c0010f03000d840c41515048807070180e085814280840c8202907503400c60f11007400b6007824840b0b0402440025450f19075211021010204401420303503841840d00302c0303207400c0000010b00500d1b402003180d000543c613888001841034840c401c0d80c2c0400d402620741c4541c00c00481c441c144c80c0c903003c0402c9078064010310402c0c510700b810301c0160000d540324034011607940d440c03500d015243c00407040c6841c44c3c6074010030003070100541c00b030701a4040c003000707880c02511610a1000154001401c03d218055010004c02c07a0003090b62014031030b50640d024030003c01940f142440020b102112000314180421b01d0b000040002e144294000d51380122250700020f04110150700080c01c0c2064102500e00190003000741d2001d50800f88079164021403405020090300b031850f503a40d502c41c010820064010b000c4c441140b0714480c500046000403643c000c008110003926413070040d1404000c040321030019031038082c3c6820050302c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 565359019 1250 565357769 565357777
    0x10917070c03080a050d0207110103153803100e0a020325181401091d0a0902190806010e09012a030e01050a0906050708040b310302071802 61
    0x507050688003415034a5004884d4803400404d020440d040019843d10402c4e48040e26140d4810600003610480c1e040c00101500c1110081c0d0704c0303522450030f0800002161510001c00c4101d00342500440440c200100501a9802c800c0c0300c5042d44000b003044680c1c2c00e0096003c090f205401080700d929110041d080041780021106908100941d4031114400e030015020030195950914214030603401441300110b581c160303580035140000d14088404610744c0c000012002030070b028000d03500354064a00e11010b8109015282d500001c2d50b4118080c00c1d5150b400d400101c80402243c2c07100f03130750341c0c0c0c3c140d240d900c0d4400d11070301c410b03070054401040703148106000e0f407003525411200c0c1ca410024540d81c01054007030303000c0d82001455030303502807124607034028060f030b5100e10154900017a050641c1c0c10704000385d0314018500f41c1040202e90810000504411946401c4000400c90014412080400c901c0340714140c010b426608100003000410140d00160701d605480c0d0201090070b90750a0141d50600b40d0003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 565360269 1250 565359019 565359023
    0xc060603152012150d120f02011e1a060c030903010c03090f3002070503071d1518010902031f080a170f03190509060402090c0703120e01091707 63
    0x442007210f5000480411801500504c0c4d951440d500d0b14010030004a8510003810125034010581d1200603009800c05010380c00c1c0103082c0003e00a0b0280811000b086d031184075003c090f015681e203c400408071a00100c2001040041c1c5841d03925585800d07175039a41d4100711841480f80d030802110a003424441d0090804040c3d020f0801d4220501c50b83d0350050030320034440880c03800098030703232001d0280007402503c0b068030380030380c01070100e036400c003428541000319581111003041c0c1217500c809104a6100c0c64681c0c42100d801d0b0011680720400002100404103484022041142c20004075000c0d07010390040d801600c94501c0204142800c1c1b0031828150090300c20f010160708510040d00104031441010180c41e01a0101d0b1403a0603c580b46450300c81e001a560284910348191000b8504e51807403141c0350300410322200400ca90300c2c180c2e00290750000000e000c041c241c0e901190300004c042c00741003008814844a0024050150305040050090181110507a6411041c8001c002c80030301ca8011503201d01c0e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 565361519 1250 565360269 565360331
    0x180213050603040609120306060818060f0405032106041b02060a020f040f06110d050f04052701091b08190b030a0c0b12150a14010c06060315 62
    0x145000c04216290300024000d41d4019150b00a100000b00b413002c00d2189080d06071400036801e410034200511030000100461014481003840705018080000d055500420454a0036282d03521441d0583c15400ba101c5a0084e881d20001e00200c0c221885041502c0341c102568200a0041031501048800300b61008e40400342c1c00c42d2000c00c0146055070000c000c05e204c038444251a040e0b0311800b100e0014244e50022000866901c003081c98000140110080b904140c90503a08004034a20a00c403d403040d40300300d034495400455050b801040188203001c50080c00c8010394440d6956025039800740c121262000ca8614015840900c094082c1012a000b00e0520300001020034003c807680b001001c100070a141d1503c108100440010300104142c0054818541401d8468109080d0261003103009400c01c000d80004400188061b1074a501c030804452401c05002440c400308401621a42c1031550040e0415041900100610000c2c0d03900e6136045201074020041600d100c0744009074001d071107440d01840 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 565362769 1250 565361519 565361557
    0x5090304081501150f2c030f0c01020c1e06030a0f0c09050103110a0806150f0f1210140918070b09090c0f0f0a0e090a0e060c0c03040303121b05041802 66
    0x1880c1c0e041d4108082c4590794102401c0781c6c80b420009151044c40c580300c101980c01012090040e5a0500c036130032076440c046d1103041c2204000c04809000c0e00341024054007403100440059803005160b00041c1003052440c400304081302480000410104203800781030702090070f01d012001c5500307e050442d40740040503501c03100c06032200010000c0c4101001300e2002e109000380b042003500b07001c0c1c01c0101110b000c0c41c16000c0d80c2c0c4110290403c610000100a00c200813015a03080243d0255248032100c0e098003212503105554030f4485040e101107808030a60700b18412943e022481c80c03c1e5034000c1c04d08410488000c6100d50ba900c6111070184101580032200c4101440720341181255500a45150811818180c507000d4142e40420902d140860b8811071440e101c01d03034806c0c028024000140c001030b000050742d00e04444034005e00c0d5284914071000b010030250350f0042032003032890b5000c0d4801c050804864000c0d0130704140001c0154015016021880720991205004003005100300c2d444201c0d00c1c00c0c49008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 565364019 1250 565362769 565362797
    0xc09150103090c05100c0b0907030b150a1511060f101205010207061401030b06031c0521040303051f21050c0405010f090b010804021305090304081501150f 68
    0x1411060b00c0440d000702081001042c41e98403002d02c0000000296110307503941859081c0700d5010a400f80c0540e038a5000140305001180030585141e5120f134008051404945d803070350100d103c102044d4000d1020f1010020016074156100b40c8104110101108803801520b40c0c2000e0182041d003a20600c80c04101070704104840e01d52202c1660340d5501410005040c816191180300070341d5203440700000c0c217a61210046c81084001a9940d82020f0144c0051494208416a84c4110548600c11100307004012840c2070300c4500c1c034608240341c0c8400da100c81c0d1590815241c0a006018180c1c1d4884d51408060141051020705d518a04100e440c0c15009607030254110b44065444100640d041c0da640c0a41e69100c51036403240e00480b4000c180106200e411645009038801c21182e0310030340603042010301c8007444050780d82c0550180d11030b25815400034098841c070a084d8514819035011103190301840108502c0c08001180c264101d8500034000c0021b9094590105e03001c0100c0d840ca480030810601050035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 565365269 1250 565364019 565364021
    0x31d0105060306041b080f0102031b090a050108100807150e03160e10051f09050402130b0309030c060406060e1b1804200d2a030203041b0303030902030c09150103 71
    0x30f0110740300346840d04981d45461501f820040c21814961071b6a40000500c19080194040307030304550b00c0c4c02525802c0900080010b41042507622403035041006c4080410f03c080b0600005000400800b000c86030b15039030703c90340040c12800c00008400803032444c081842060074049041d400c4c055581a812064504003441c422540d40b01400d03840c0455505580400c16031580c804402c1c00385c3c4002401060845243d02c0100800c5413600005d0240b40188000d00010301c0820156054400010f102526039a0749902c203441d5003e03000d014081489480140b01c10321240c0d0b44841c0030341f20304080004480d9a464150b90042e110719100e40d603a04820018040040b00c0101504900c05004102094a0000515040d0444100c04225075003402c0000c104840040b580700c2c040e070401003140f103610351031349003045da04203981c906a2284c1071540010000b4200f210f8005459a201451080441c183d074030390a0080061a02080490082c85030185d41c2d00717180750205e0300354494010120001112004100114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 565366519 1250 565365269 565365293
    0x5090703030c150501060203090901080d2a0c061e02071d0a0608032719210c0e041e1214090d0b220816081207031d010506030604 57
    0xe1030301802480d00c1103441c0f0060190f24024003442d0b008546600007401040240c41041e40500c00a80c007040e0f04103070340c0e0342158050740d038404840c8400c03001c2c1c7c0c01410104210b844e12180100010380c028400304c2d070150070801400056000a080c5600303542800000d9035100b40c9070107000d0403211100f265080309041d40404039484000c052000c158030340d03242d800624541211850000702c2c030036002c0a40b035880c0405880d2040070001c443c0f1401000d014500340c480d0310000c0c007030103c04d0300080c642c03000c6240ca01f5450030a25035010300010700312640c40c2c0782c0302e070701c480151000c48150789d04440034852922100711004030143c100b8194814440c0d5100265074405404018a00c01d000500c040c00b820703610481d02990700d6010f070358202894a86011110f0010703040c480c80c86048a0001c0c00c06000c120f841c81a9a40c0c0001d1b44412050b400389070a1041e080c2c042c0c1401c039509001002d04121003903906402a001000b6807030113115020280841560907140c0850f016a0180e00040000f000718890880d49 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 565367769 1250 565366519 565366523
    0x80417070c0311190b0301031209120503042103120b0a180b0306070503010602060f130618060506060708030408090103150f030507050a15030b03010b1206010905060405090703030c 79
    0x19031810300541c1c1ca030150758009900c10340c0c04202c00500141681440c500180046209056a041c842c0c00c5c400c0c1179903075000c107010140034000048a6400240e009031407042c044c264803035422082c1041c07840d017269640d0181c0107543d5032204098940303c501c001b800c0c4080309140d042e12003030403071003a24006c08010810107003050340c051a032004c0040c00300c080c0c0380074085070701240102140d2141800c1c00e06107001c40c0a0a16420000304000400400b68081180f641011071413011900707a071203904440c01c2200b04540058009850030740f01c81c042d800419503103614a03110b10b200384100d07610303802000000d008059001d08031076000c20000c1c0014100720010010319205040001d0700c00540002031808040d650030041840c000e00e03c060003440410000e020043c041250144400c6003003644d21034000c1c3c02603006c1003d050711070b1a802060381d02074201080c1424040c1c00c2e07410411030050b40d0791b502c0d0301c00c9c890f80401a00c0d050120301c00e1305040c017990784220034030700041a016280d558201da07052889481 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 565369019 1250 565367769 565367813
    0x201020705180906010503060c030412090512030a0e0103060b0d0506040f020715050109020a0c2003030d15050402090603041209050303070b0403080a2702040617030a0207060c030804 80
    0x40800c0594954000707452450702024503071110720f4000d141d00d19080b0181c00c858401e80c8448208401d1040c403008070b980c456030000c01641c2d041f0011805540e8140c2d244c00c469800b1407500e861903103810303000001d000d80d140701daa04c514a11650300010340480382c81d0b0182d412542001c101880e02c1940503004a82c2042000d040024911001c0c5400000c81e001b205080390601100010000c40500c0c1b4024680500060309c8110300c1d08401c441c018080400503200244605141c0c2c00c000101c402d41c1102c01444e0001900b680e548291001102000340f005d1b010400c00da06907210003085908003031095030710300003019000d240346498036202c41070170002c40c507914000c000144d107020422ba101880a000c48030722440b155140c50406142c0030384000300080941c88003502c4e01e843c01d11800e4000460085421460f441081710b6030482c0042406000c06410402032924604550701440c00f0010081089005a60a030f5880d592503110468003180c5903a005800101100302041c00310304c5440c0c03244091107512030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 565370269 1250 565369019 565369033
    0x5090d050f0d021f050127021e030105040608071203050c07080f03070b01090209090a1e1401290a050a0e040e0d09090204030506040b0a060509010b190f1b020102 71
    0xd40d2501d02001d02c0c034000300513000b000e01040a1141c14415000d05425860140520742c103005000c041e0b80003428141551000c1800c0410704c460644d8101c900c8080c0d40350000c081e40c0400c1c0401d0300d45600078031800340142d213400340c00141c81c00c010401e44259140083c10725a41082e82c1c03000c43d80c0e500440301c0e40d00e284c00707140350000384140c0802000040580f15406182c0300c00c040e040c2400e103018160302880a403401044400c01a6450382401b41d4401880300300000d8072402c0ea0360282d640715541c02500c0c81d01c0d18090302c3c000400c0c07240e20074904072191a0502841084992140c03084507804040c002c10720070050000c0b8420300e024401030070600413a89414120600b0903800101502e130212350050a070780111003003d020550146104020b45050b8800750f283c18a1070741c802e81c0d1440014805000d942c103440c04900700c0c1400e03400c420014003000b4041c0342607585400310300704194012541d10210750b800e00d81d15040240a181c0c241c1900c138168540180c800b0301c15030040c0304411840310403411406545 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 565371519 1250 565370269 565370293
    0xf020d050c030f060a0516020a030f140705060a0b0f01050a031a040609020307020105090f07090207020d020907110f0705180a0f150306060b0c0d180e070509030c040b0105090d05 78
    0x460100e480000d83d005110505000801008a600c00b4201640b424404c03881d00c1c200d2a0001202201c040d403528009002d84000001111000d81d000e100003591040003400f48188040084c20364010040c5400400901d2000010404441003402d075203404188140544035040740298410b0b558030a12240c40900041518006012142141c00a0034000e901000f80121a46d09100e015800307030f00f000c0144240f41c082c0e1055035943e0100d215040c403507a0002080c004540b58011140c42069024024080a040114014068034079004040d000707445003516441c2c4140c00060008100c80025000c1c03005014a80d54205081ca4002c010401030741c0c4520f0380381c00d603c8d40744c488d0780040c080f080560300302d0398290f00e8090280c0e041948413076040d18061003114034200c00071038940c1c0d44840b981800c0d11140400c0841e180c00302c00c03d9000581d5815171004010406130040000c0128840440907100203046070010003080303400a1218500050052000345890308141d21b5103418580194203c40c0c51030044 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 565372769 1250 565371519 565371523
    0xa030204090504080316020a0b0c0f0915300411030109050a11010f11060f041e0f110429060405030f070e1b1c0f090f0c080a0f020d050c03 61
    0x161801c03180010008100080c03034450b00f500d6505806e0030f102605102c28030b078a4407425640090055800d03a01d000807035041e810300800483d900420086c00220605142d02c2084038181c0003142a42541d10021014841e80082116050100400500b140d9695151611421043c01130882c92503095984d0300d070b001c804202c0411040c5640d07845102c0104480e40a40001084541d4085680c1c05000c001031603a0070201002c00c1050f03000c07040d00e032040e4641d81ca6044c115032840b8000c116595404807284210280080040c4900503640100c548a4070180c030b0005100807074418440c1680b0501e6032880b50803101e908820700c1401c41100901090605e51502c1c0004d050145214807460150b010120030403da4000c844101c0d40700e4024010368030010051126000944144280502c5148541b40e00c02581400c0354401c458000c01814200044070242c41c2070f030583c01d80c1500aa0f80400d00b41c0c000101420b001804042e00d59010006680301002c95003806601c800d2008200e8080c022040c085c056a281 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 565374019 1250 565372769 565372771
    0x6091c09090b011418010f0f08040609051606050c210a120e12030906220f060908040803070203070b040f030605180303090a03030c09061b1b06020a05060f0402150a0302040905 77
    0x100710b098074600c285e284000340c03000c440c20448000b0b1002901c0c030705030044d410081059005130000070108070020700303150050030000c41d6444401400e0041c4004100703c3e41c041c020b001c04040e5403049a56820001c66a00c03000f00594030b10b0410441c08100e4180624840c140405502c52901c002007a0142046c01d95400d000e00c074155541041004402c000741d101d02001400e40025094107900c09030030311501c544000110381c440242c880b0399803242004c2000450b80c0700507081034000c0e80a80d120354a8900c229180e45c4924400d034402d2281060100b81c00210b102101d084403507442e40c2882c454550740d10a005002c0c01000c40c000403440c0702c00c20858050600045124044a4024000803000c0d40b0f400b8049074401d800c6a030402c000305005024058100242c40001903418401343c190900d140f4200030001464080d00c6011885801d0002c0d0340350300001c2900c02c20b0320503001e48001da51405600c4002d69804c441c081e6106d4a8010b070b0810b240f034140c006001104092038094501901c4003089816140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 565375269 1250 565374019 565374037
    0x9190809010315120209060f030304030201051b03130e090d090501110a05010c05070c151409040b040e0601050102010f051003030e0d05301e030901090c0806091c09090b0114 76
    0x71800c1c40c400210715203600000d5002d1001c89445003c1d230010b070046036803030089000081c148140000c05400741c0c00050149a040178000040f603599018140858424510341c2c4160f16280d038550012811a402c0400d0300c2c4072011499840e007000d28581001100c150a46242214813401108200700208101b070107a416012000e855085c1c0d00c0d0480e20348401341c0035007a40540c0121191803128082e46500540301389401800c001c0160300e401c20741000400074084d100700e03030f40c0c0b1514000c1c24406088001c190135040300ca090b002000700800300c88250703060781c0c001c80d13160030800075070101480042d006681102144002510110340c1d40d6403960303442d141c120290314804203000007121480400314141c59204102c40301d01c2d151402c01d1940a071080562404525a156508001c000942040802d6204810868110808103880c6035103007011902c58500381c41d91161406560000c03808120341007007032905114943e0f5210001841c0c2001c120007002c01d1107000b1b0401481c110316200d409000d02c0a00400a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 565376519 1250 565375269 565375289
    0x18010608070509090a0302030a030f0e1605010e040b0d02061b1911040b061215040c03020912010e0d0f02031303050c031c050412050705091008010509190809010315 72
    0x50401003040400c0c40002c4c0211036503407200303002e100001c1e808400d0754403a03e01400d01085242046071544c000d030002e0301400381c4038410751040c04002c92020001a041340c03000c3c1c98460303420750329105110170b1b1943c244403150414186480c40700103050031f000402c072009601011a400b40094800b4a041506505a4104a2100280b0794052060340038a00ba08600d04640030484450440041106070040701e20601c000bc02c09c0b0005100746103281f004100c0070300c006000300b00a5500f020040d00a42089a01e0350003078560b84200100084140301c2c94020120034030051001d520402801c0b03030740c6010752280d80d0840c0000c2c804030b03c3d052000c0c548240a5842107000e800940c5e00d02050618240e112441c05a441c241d180c803004409802100b220252b03158054090710368007a40c144070345440e43c00e03031045400c114100100404081220a80c10640c0c440701c009001c0c940750a1541507a8952551040ea6240341c01c40291001540c51001071a500d03406040120301055400028003460100f94007010b540 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 565377769 1250 565376519 565376533
    0xd060501081605041a040e070e0106090e0109090203150421110d140f0a090e010b03060a081203160e0a0303030203090f0a1e02010903200a0e0603060f18010608 70
    0x5000682d60b20000d41000c1d81c0030840180c04444e010701100001d80e000f03001e155901c17080000d4240c18082d08001d008203680c1c0301c0d6030303594400c0014940102e0344511a00d09909030004102d404080c06100040d0750010b005059401d01c152110500b000080d10445030a82401ca01e81804401d00c07041500b1141c041e151b030800e4028641c40c09060409001d208800c001040c2c8160480c0d00e01038041d07881f024500c840369910b45000d144162184219a00304e40b00703c2c0112000040d600c4005d100462180c1c405450084440f0342d540c0c0a1a0b58034414600d0200150092001072010500c0d011183c2cad2000003898041c54201d950404a00200300c0c80d003007900065000001c0000c03803d4104410504010f42030000c01801409450702d00f444500c140c4031103847c240341c0848105684c0f148103104055a0450700001c401032144290300300000e881d194440c0280b01c41280064544a01d500e010f11810300640501a5940d400d0114a05500c0061459466010a042c179a142240900c145400340189800915036 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 565379019 1250 565377769 565377793
    0x30d051e0106091a1603120f06090507030605190e060a09020a02010531140f03031005030115060e09180a05070f0e040c090c0527150322020d06050108 66
    0xb1010504d45011068104000c800120100050404901d80c1c061900c2041d48100d509980017505e4130b02c0c5282c0802d03040900200d02c0d000e071130303000364042c8050392420004181d0715800e01000214003520741035610080001001050490380301640c0c44940240311030b10352078584941c0800c0340c101c00b07502c40050f0341d074000300810301c007001c4085003c0307000308520180242560003c03203450801d000345c0146100440b0449050034517080201c08001314040c01a603481749810001038800f131407a0f11902d4031960030078010300d038079450640c81c00d010f461041c9d0711080c40ca00c6000a011a040f0098000340141a1000c6420008007040c0102d801451140014001c030a00d41100174100134040e421040300c076208001440f0000781c248481000300c030350000020403613602c0d280d020b550b9400703919190188803190f00e424107070700520410000c0480c1d41c110388654807404010321410300b40c0021910a841c5a041c148900c04040072400681011071008003000500280340d03a2300d0782550000e9011000d164092200c5040c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 565380269 1250 565379019 565379039
    0x1701030809040e0606060409020f160f060f05130201051608041805010e0105030a031211040605120f070e0d05100f0213080643020d030c0908030d051e010609 69
    0x884480124014041d034286140040d466124030f119104505038004ac040d442d540c01c040685800030310300c3c10f41c00d0f485040c0f41402c0d0106040340d00c04545080c5840350f0001280703050300c2000d000d944100290130100d90036078010b4800b68802010700409492100b010400260000018000f401c000512010000700c0d01d00d04100352041a000300080c10710500047c0410740b8000740b42c04101e41c152520082220107044044002d00f000254034139144400100070552a80180081800007550b60541c10315680344c3c580d44071404029201da0000030341d0a407440b98107142c14114444900e0281068070140400300c103030700c000c45200d141e07280c965940202d175076285d648403404000e005007482800780101e441d04601441c5440c8070011714007480f031640384200d0410030f4580c5055201140807084003910f106002806507913080c0101c1030800003070400d16084c4e60300d40315802034011074510314010b608041104003c0700c081d01000f804010400d419600c0802c6829408a6160081c00c0980f40d42141c541485101d0b1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 565381519 1250 565380269 565380281
    0x71b0803090f222c150a0b180a020c010609060f083004080604050c030105060105090d111f030510060c0b13060e0f0c10020a08041401170103080904 65
    0x240c410721004100c0c0c60114042d40e0032035660b101000002490944e10199801d10b40d9000061408241103550044403e0f1800984220b41e07403000100c2240c19612810058183c9080141d4990000d0998070010800c0c1704c0034681c2c68100c5040c042c00743c28000d2040040b4211038059000c4401c031501e80c1c0040100394002d48400f809000018090300b48a04991594211050f0917841c00c403180c02c040c1c01d4043d03503113001c4056402a0482500342d440c0390400c0c0c100f0300d90790040c51003154425460003020418130b6028030111840040c0c06002079000c42d40e907844000b014051402040c2e0041c648030060099803600a502c402c2d4451143c80010701414800c1c41d41401d0302c05034120380c0034000c5a41245020130104c004072540010880e0b2420300c044514640a8044c1090300700800b11441b95128405090801140c035240c0c04209030341d07111a40000c020201d075541080d070f50180034000104014006841c80d0100400c5020060520b0070240448040c0d100841c50264000d880002010640c0b41c0e4615050040d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 565382769 1250 565381519 565381549
    0x5250c06060b16110102072111011b0b04020d0b0705030106020c010207180203040620090103050c0909130f0b07030f05060d020603070c020d0c06030501030332071b080309 75
    0x883e0820040c81c82000003045840006801a00c10185000440e8801c0003040090601c109000c48540540b0309200071420801904641040e1100000700032548510300000c03101d00c5442240241010940740d0081c0c110010344144c0c0c125272005140703004904070a00300d40c00303140300f6a2031369034940c5400d030000e04010320040c860b4115000410b0410000d00126408610360303543d0700c0c005903a078559192030070040c0348911840649040606091000c0c8100c200a81b1080b2070a032002e0000e95109402c1140511440c814164003d014001060104ca981c030180e44c2c2c054403030400309402444688407111415412184400060f81b55400e03500030302454051140c200b1000e50303002b100c1d002c0640c000f60041c0001000c600401003001c0c00300c000d540e2445200c0c040c9039004040c12005580703540d80180604002d010550200c0d420510031500c000a0f601e2400f450003404941d6000408000c0d079100c1c06a02185054a030955001900413994080d1300b5444002d181540040d07940b440d81c1d805008000600c1524 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 565384019 1250 565382769 565382789
    0x20f0f0105090606060a030f050123090f0c07051908030105010e01170c0307020307201908070306020d0f0f0c02060901020f04050d0c0b0d092d0605250c0606 69
    0x28000d50b0300c8001111500454204c40168442075a428118028008120b04500160400d00001130340c3d0080d440b02d507031410380003032210403c80000007440740804003999107616a40c20040052a030148482c081d0000c6031244064035007520040e05100500403215074292880b550010040207950703000110721031f4650003030800c41c1c0421000c820445a40c04e004051046040001002071140ca10034821160a41da2000402c2c2214103070ba03000320401e019440072a03000e41e011103a00c0000000d003070749890488030840000c0c50203d04544c1c0d8403000e9041f003480134401a4940132645072400e100e010b01c034000030015500280800705000001e241080142241605920412407141d00741d00001c12a001e5580a90741d10007030305a2031403c034503103003842d030b01c1594550301c08079281c640c03c1000e07004501c8050181100013141ea2507142c2d640090714440e4481d20b0445509000c0710005841a081194001c0039200c00c40c90308031049043c40c03092112421500002502980f030a402c0096604c0380501038000008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 565385269 1250 565384019 565384021
    0xf24080106061d090402190f140102010b2d090412020606011809050c0f0408070611340305160e0c04060801030308040501020f18120f030a1101110406020f0f0105 71
    0x702008a1070f4414815034081c803c00300c00036056445048220140e56100210a401e5559900c014403c0078024002ea41e004003589512100c990b105010f0080c005000404071140c5c00e44c000040341c46c51002542e01e2882c440007600b400342981c2c841d0360346c034400e034007036410b48103040b030f04007030090810300028010b0707062003541c0148118404c08456038009644100d10009001d4850300940743d064001e004a20307514010000e0040b4440700d001c140441101e0301038640000804210000035107030b81e0404c894201d584800b41c44d10700c102000005540318108400d030121402c6072692a03540c1070000100d40e05c1c88844480704200f101200d44449207501140080c03142c1d003007504040d8020002101072002500300505030b170120303080c8031013036044441030012880b0655469442c1040035150004076100d15115150740c010000341d241000c550103042111580245240007039a00c0309440c0030407070082030744680d0360f520050b44000040d100100090680b5070020005003611143c400c2c0b0b0022003445840050741071034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 565386519 1250 565385269 565385297
    0x12290315010b180d0b04080408060907050d0b180d02010b0a06050903150714130302121c0f02070b0c03130803070b0613020c011410091e0f2408010606 66
    0x8060f280259012010003081500000001d000e800703100c40d029120380f0002c2d092000700304101c0020401c9a5591082e01d5003561811030139a102d50303484c030030140c01c1002c01c86800700040d85000c186911003039081418150711240b140c803503d450800402c04025039520644a841403820342009001402c1c9440d1941ca040c0320b06001c21b464280302550101a210100c0c0803a46880c0941c0d020801d4034501d0001903210f07400401c1c40c200454044c4026402542e030104c011320f42c250302103580400380c0824900224000e07600d480455102c406a50740908500402c00d010880c02513002c020540500190b00954503000f0260140e000c0e40003540c0400080c0d401001098005000c400f541580a081222004012b480c45941c03180a48101d0304001215464500c004005107100811a8002c142c44060560f4050300c442e03018048035400300421001c507004041c20300c407800003038002d180c2c07002c040400030035072003951204ca4945000d1406180046c4100340c900348010076003480b038240184500d24107107451039600 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 565387769 1250 565386519 565386539
    0xb190e011107290408030a0b090f1302130e060a0b04021e030705071a070206060433090612170a0f0e03070b0409020d06051f1229031501 60
    0x1007000180782e0800e900c0c80701010303404030083c6403100c0d0580d10308080034a0603180180c800da20890300340032100d180954842070b5040c6030112a1140341d100f59444110f032034604654490700440c0710100c1c1d1108481490014480c410b0090402d00c1801d00010310f00d82c100052020165080c8003000e0b4016403040c0107610700c2c4c0465000c1e80101141d241c0c0d40958a40f03c07420103c0f294801d0700000303031440758104000000c039440010041d110f81103a500ba1082902c0d1042000705641455400507414009021007460f401c21f8050500c0e80d502d00f072107505800c1a5900ca0b5801610300c164000c40e804003040c1d41c60010310903a1450002036800190546242a40c5400c1c060729481c10300700580100a604c03504084c50781c50800c0b004000d032054207001603c9036a079155040180d4008031004c1c480508000d40003950707043c100942c0804004248201800d90144a0225080000c10070350026040e03c0b20f0080a4284540700861456400f41c50342ea24220700c00b0050500d8105c149050342d092203040001007100d6421 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 565389019 1250 565387769 565387777
    0x190204050108120f0a11010903080610080c0a03021605060a0912110d050304060f06030602090f0406050a0501081e04030c020a0816090240050904080a0f0c0b190e0111 73
    0x6905495405440c3d0032031b1291000d00c0452195841c0c4950324003455040600184510000c480742010300b680b03004100c5486e41c00780c0798103c0d00c1601340180007456002e50007508000000c0961096601c40c192141c0b4689a02035404070410307542c03a1400001d00161a00c000c400b5034103400d01040c0c2e0b550f140c11217603461100030100030400c14044041800c220060304192800d84003424103011903920b90501c88001d5214550311441100b610840d50080c0c1814042d90b0f0031918003c0c40940010700c0c0000540c1d00500041c50b801481d28150718807105022114425070086001c5d9440820310304080c418001d07110303840d400980d081c0c0d204242c4d03081d0107581e04075600242e5400000158a404841c410799010030110103034581542410300b688910380a1a80148042e0b040d5014644003569440341441020581030790b002e808903400f04140001107000e4594240824100c0c03401c0d04002c0c6d140d0320f0b2011006806c3d21070380359911711075540f101030754101d00800e400b051100000700007034642c00c0d0002d210707885 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 565390269 1250 565389019 565389037
    0x4080403060b150d050105091003020d0b06060909010306020a0e01080115110f0d03150902030c030103060b0303121302040606020c180c0903070305031902071406160519020405010812 80
    0xe1aaa41000203484070f4250722801c1045140790b0380c9981c1000503c4003d070109009450051000e40f00181a8080813080c01080f82d4024000c40303c42c8003581c40e400c5070900000c2030907801400400c0a440c4549601040390300a40c020400140ca030782c141c1c080117251080c002d1200d41004038000051090503d08403000d003800d840da0600d88807d80480740c100d1306052070302c24890007500030001c4070201c1e550980c009940c0d0080041076101e085880c4e11180b0224002903801c41d0f607414040c80103200181660b0f00512503844010101d174284040d444009052000071103072180910004c14400b400c5040038010702018110303500240031a0045000032070003020b00042d501c142582c5940204102d24551800c030380ba602c50140c242c407041da40b60700b00035540e40c1c0b148408850318400d10340302d400300300d2000c00c00303a00303035850000f90f01000c41c035120401480d50400c002905031481341c00254400030b1005c11005003100440e0120710441d02c0e5600400c811201d050340040f00a40004442001030a203040403a0f124003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 565391519 1250 565390269 565390271
    0x1a03040b0c0c01090203010c0207050a12032010050a0903030b040b0303090f01110f032205030d03021c05070801081e3705011401050f15090d240c080408040306 70
    0x38102c9a003243c050a50b1440182d055403030310900d243c0d0a03901042582c280d403020b566038001e041d42ea4010040c401402e0380050005051a02118010300001d49034042c40320407241120380100301e01145208561081d54800303d2103544240b52420036405000d150042e01041710100868822100401d0701c0784140c2c0012480744141c0e00c03019689a0082c40700548440031b0104860711401d003030f41c21903900d40c066065120800c0707694810184164040c10440d09880018018008a490400701940650008044001e8082c00840c12103003110b118402d00f0720541c115075400d0201e500d0080303258184141342000360380c1940c0c1c1c64001d8981200001d01c1d0605900800303041d500d59600102207010884059500028100c4452000b13014408150801310403001b4205035845166603900411000365005909030750040c2070030384c0d1121303d02805405802840005400f01d100c1c1d9490340d94003c9110602c8004140000f203591203011030810b0361264244025082c205207030359040a03250031109000b079110040020b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 565392769 1250 565391519 565391527
    0x9150e040b190f030201020c0a0609030809040f1b030c0c08031503190503070218071205091c020114330301060e160e030606010c06050603011503030206011a03040b0c 73
    0x545801d007200031220103440000d42c29640b524082000c2c0700d454070083c2e0041c444d40654019900d0400c003420b0484665848170302903240355a843c45120742050b40c509610640d9050100e2908803a406031240c070003141c2000340c3c03036015049405003c031828441c1000801c180840d0560024a4640445c0e801040400e081c040440c02500001c0c0b40c00f00301005035000100600118007042400406040309030f200310b502c41c0200c58404e202c0d5440041c1125076200141291300c00b1408000594407a5401021001c261504030158050461500384144140b500503036650005000d011484000329800c0082d40341b13250b0f01c9100c002031903004030f40440290b070307528a0498013000140d074003580054018420008064058500150001c56816044801c1004240303000c0d001021803070080b1b00180300384030584562174011000e846120003840000c0c049a019035031202e140940b0810550514000c41c865070042c1002d41c14220040d1410054030318a00c1d00803414818000094050004036501070001c0e1115615 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 565394019 1250 565392769 565392791
    0x90b04020f160c0b191d0319020108011d0610030609090804080c012c0a1206061502010c0c0204020a03142502031c0c090806070f09150e04 61
    0x9110710290481c0c0140c1c009180454080000091210325002c1c003402c4622540e210004041d03071095108400340401105000e88002d03000e80311400c0d0100c202030102002e540300d034010034a420311406141d501c210000000100b1581d10012143c090f09a52110f80c5c0220079502100d401c400b40540224400d2014202d04142c19100e41e100c0070041c0b0b03860b007040c04076242506000b4816801802a6000b034011440b00d01440d500811103c110300040c1c4a07042c52410000086e81624a0780300f9030780d0340c0704100b02e100164800c0f0340c01c0043e845c5401054001061460300319089000000365001c0001d59043c07035841019a80c000070b1001c100d54040d1805a60380100001c110000c00c1c28280c040c0112303040c1e03014000852400c00003805d584012140900105c60000c4003070303907240100795a1240ca1120a41550f02e03040c40d9401400d240031050401c228940e4560003204e0074840c084841400250404540781c400781da00854080c000e211400c0160711500391000300401021301d0046503802217441c4c0703205001e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 565395269 1250 565394019 565394021
    0x2202031c050f0a030506040c050903060606030c0d0e0d0816021c0912060c0f1b060c09050306070e040b0f060a181703131a0304060917071a0901050907090b04 69
    0x340c0304215001c10f0740c0d408041409001840d00f6104c1c1c0c0d02a519001034030603081c3c020380c212a18181c00900a0103595610030400c800d030ba0006055004c071440034800c141004100d80152003295050901801e000e20705103c00401c8140c4c0145000c000d01002c0306028192500410b06100c1a80350021b0101704c104190b40948410030a580200c0d410054020000309000d41c5030301003180d0326550354a503480342d83c00e01403c45a030750385450b82d5103616680c4141040000c106070710400c2c0f45829400c1440305180d0720701c0044d080400c00c88406000c504010782042c1280341500c80c218011908840d1325800050b108041002030284c0881c00041c0702800da125100700c0b4003520454000e0440c2c0c03100c410711001140c40320352a608900e10803500204442408100c0b441ca89201c5d072851100d01d20200c1c00d5035a152a004046d080564003074480f05214443c0b50142c0d0460001803204901403000f502c10611035140718141104002c0ca00c0b8a940d1502c410f00050030004100d54048544000c00031841a00c8071f40010 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 565396519 1250 565395269 565395277
    0x70303151a0712020705100e04090203010c120f091e17040909030315210c03021c031d240d2301061b02011b060c082202031c05 56
    0x803894407241c568088515544000800c0761034803441c10141c00c00c004490599072100300b0300544d40e02c00d031482600002c15228080c614102100248040350412a9401007421074924035106400101440c106056400850107a4042c1400d0f60300300b00308440300b903182c0313040250690f00403c10654051990070184100c900b0f0345400d5a09103129641d455a032520040d00421007000c04401007410000d00144080b62014a08220b415143c4c0c4201d0603203005c01541d0b2800c103c858112120041050301001588070000d503048100420300b00a101d408280c1001740c41c0b0128141992102d0344403c0f00d8840c2600c0f09030440403048000150742031007418402c44a04507004030140d003e01d803840d1659032000c0e2000030320065024030f40c41e0b65000c1c4698039854110761001c012484808019010fa030594010351081900c00b000c41007100d543c0d06132a04903642c3e07000760ba02e00001c03000090400011f020103d04140c603800030500141548082c0c000c0b47ea40801e44450703035074103a444544104000e01c070420780540211 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 565397769 1250 565396519 565396529
    0xd020a0b13151e05131209080607020703060501050907090302150f1c2715060909050d02100209130c03090b07030e070504023c0414090f040807030315 66
    0x804030760040415904010300d071025507807610304400c2041c2d403c40d11092050500840c1d070f28520411903c1d96450f860b17615121050b0307a00402102c403600150080701800a0342c0100311560240076000d16505003101510f0060700018803c5180106002071240c108000004496041c2d840c100c40c40c540700765031100d41c090b0600720f04a03072100003000f00a11514085141c2007503601e21080080786e244602c0b9040d41604a803010128800020003040400c940c2c0c0820600410f50040200d40540c071621007005849010b00c044400b40d000c480031903907264061003140c03442c203103410013107080000c401d000500028a01c81c28240d0b0542d600c006a8035a8801d800c0b0120058011a0031030050501650040c003c002c15240b50056000e600408a960f2405000300c1d00c4080890591210005e90004900e01c42200503045404110140c000e089040340341c1c030084d100520192521070054041c10091011040d002000f401c00c01d040325041000103450382c81915900354162500240090802000004030b00300c0b9009 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 565399019 1250 565397769 565397783
    0x60b130213031e0302030d0e0106030c030b2a0405040b0d020612071b0f03081807060e0405060607050316080d0f02091009030b07260106051b0d020a0b13 67
    0x18221400720710440ca14200d9120b10100b4000c0310b030626400d41007a8281100a005070000c111301590f1240c03941183c607209801000006132035aa03903441c0715480000758800c992501501007040340354200f17040741c5a0398a140035298400c0c910441890302072441540206481203503541412002c0351110452100455406003c0c9035030b49212407141c4180a0003141e030b40e80050520400800c03542da0b1381c15034203101030b840fa00e100b80c810440e94041c0c449500c01088404203520130803071a80c806204005039001080a030b01c640710048201000c0c041550b4000f84164042d440c1041200002a40001183c01e130388000711182034814018074210a09200d00303608002001d05000c40c4c0c1c0c0265038203600500c18100103d03a840501c1043e03800a6400804521019007045401c00005140c180a0a440f410f511201d408010480340000c107469020107081e0400c000052000c039402c00e0340d04125100240051030344004004044d90b0540096490450180007004002c6002c04200404201d000800036241c2c0800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 565400269 1250 565399019 565399027
    0x9121a0703091502040317072109050f03061009021b010606020102041d0411010e030313030b0f01060908070b0702010909092604050f09060303070b0405060604050a0204080a060b1302 80
    0xd000700078218682e02615044000680260700307074030300d20840301225800203003501102034110f84109150013500c001e6800c8502000c00e51103c2411550303c0900810580314110f0380e500f05800c3c003102e001d4481d83e5602903031281d400d01819110010042088541146000d60380301c6010561724054141550020255030030034102044640d01900a0000c1e40c9090414070010ce48100c80ca008a480681d00a454807034162101780309948078558074054544003508407441c013880d114600001d400d0030f61080d03804132407000a00c0034645001d0541c500400d228980b0712402410131600a0b00d0303032154403c0d1a07400c9000501101164004c41c1240300405c21405d0400540d20b0300d0401c1c02c080d46d18115182c3e814003c0a260705520300021043d41c00f0f441e006000788103405103040c00d0000b01c840c05448564544000c0c4800c40000d980c00d00414441c5229030013030b0080c0d042c010280425102e002d8021100d40740180700c2405101000600008510340103000422003050510100b00041180401a04918000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 565401519 1250 565400269 565400281
    0xf060b0a08040b06090403052205131509050c160201090308040e090d0f09090f0603060518010b01020a021c03090b04060f0908010507051606020f1917060109121a 71
    0x3940746102e036001d200c07052115a9000108480494111801008900140b25038400540d00c0342100da4121445400c455042c2c0c0c49800244d8104a01540700d00040d0712104e0441850703002c610440001c1c0080c43c0248044c0c20124410a942e0081503003145081c2c1070314407002d06681c8610566401941c0006059960390340321242c0c405100b10440c0c08070000d208580344540020b01c42ca60328030a02c0325995504070142d0801010750040e0281c6601d0303083c1c03543c58150100c0850560700c01e41d4000c80310389100300c00c8008184034181c2561002441da90541d00443c07501e00150319040c8046104070307038072000440c2000262400b0740740403800303401100070403d01040124140707401170103040c00b624079078440090003661202c0b854261041101c00302d0004105002451400f0b03603c1c0304040788507108103005420614150301c08415504101100c0820100800d2680801500820b80034038080100784104110718140001806000c8940710307190204501d49940c809110b00503560219040009014241030300300381c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 565402769 1250 565401519 565401527
    0x60207030806010f0f1d01020109080c0304050109060e060406120219020f07050607080f090a031b180509120c0106090513350f1c0f0615080a0f060b0a 66
    0x3203030501d000c80c043c42c40500061740a1007641c80c0504040e81d801c030f140c800e030341c140d0114034601444c0c690556403201041c4001400c038001030b2642d0909c150065407141d103004001032460364a58004000e101030b18009020b1500d03604222400d494080c2040800302810790309035402849401001840300c80c1211342448041d0740800c10380408584141250300c03a5458034104000340c403030303581d00a00b07003841045000c20031015680500b1614000410625000b5600d841b4400c0d13040c140940380180c5031b40c54105100d0f081014081c940c160160788810445881e240907404c3d42c44c41071a10300504118007007040b02c01e01c40c094000b08043c1c08401803d122504103c000800e210320750f44412070310003c09032440001240d0740c12061142c0703408092240c08a25082c80804899884048940c003020340800a9508000b05c0400c031030002c10002500040c107443c1010150b04440e00d60b00208900362940e40080f012540c084000c1e900882e44050001d150317070201143d50000d00c0250b0040c0381c3e07048041140d14049801c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 565404019 1250 565402769 565402771
    0x41805180a0f110909010903020c12100507090f14040c0f170a0209060a0305150306041208040f0618171c0b060903010606120c020a08160309050301050c0a1d01140304050a0602070308 80
    0x202742c080340c1d15002120300b041075a41401042c2150740c1d1042e80d038414118030b40d4200f2508801c95042c036403c010b45441d074540d03079040e980d04050318289020000c580d15040501c00c0041c544283d1030304550014850700e0051414094201c00d03403280e00d810010440000550741201d80007000140800c2e078568011101501406045a54101d90340710b1940e156040d08020031503600c0b46900c0b541d50185a8845c01040d02d01d403801030415600c034030410b084d030340004905215103070440703030240208148518540fa0801083c08106101020300b01e00b880400441200c05911450144000d00040f50040701e103400301d0418002c00311842d030705608003040050000d8010f041ca9514811a08043c4001c107100041a80d46100138080148901020008803540d81d00c40c0310720181c4580b0a280100300540d1b90b00009003918025101d46a41007400694001c5041c3c00c1158142600040c85200d003000320b40d01c0003e0300c4c42201030104840ca55000000504021050041468040c2e01003011516040305081c002c2c02d03000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 565405269 1250 565404019 565404023
    0x120b0f180d09091503080936160306081f0f181401140604020d0207061b02160506090d0c0e07030605040b0402090d06180503041805180a0f1109090109 66
    0x118160013800001d40303425450f41a40e400c58080351600c142a4140720300050103a000d118082c04c01002000b03a55243c80c045401280c0d5441c00e04501c0c00e000d04102080d10111480c00149440d00b6420014181c3c00f0900c09420280f60100d13940400501c901e03580900240300400808a24090801d210540b0710722802d940c0341c0c01071032400307a4240001203060885030804e002c0500c132402c10002402900d02900100340080c82d5a5000d81000d40315994102910500d5048602442d0010101d01c80141d0401003100d00822115003010030900c0c3c0340200d2010f116450215001e80740880944050010b01c0d1011801000c010301c04510901c1d101c40c004006007064045c1d10311403070030504030910320b03d400d00a540180e04001c00c0b0050064056844800404805400c11011340c810004807001c21014000303000100b840b6404003021500d41c0f80403000302e5400401c62040c01c07000c5404010041070008507102c586a10604821541d0f01c581003031900000203413038240d4011a46001c000c140501134101c00d03040781c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 565406519 1250 565405269 565405271
    0x2090c0a0305130503070f0206040e070c06240b030702030f0c07232d0d03080a1407120507170106050d1a010e061803011410120b0f180d0909 62
    0x14903010402261842d0500000d0103d600c03c2c40f082e4045541f1042c6402000d2004228a03d031039510b070703c07032404008200e4501d00403500c00c1c07002c3c9051190f41e0091840c5128080e40c008000141d240000001902c64022415481008000141d030540200100c505c60007002d100c880e05c0342488549159a03551300c0c000c01660f0000c0700b10700210488544401112888010155a801500409400c40803981001d11a8030890503c00351111034a480b1300040e2114001d60f1034008902d0038a03d0882030310310101d0f2180340500a8420010719583c030001040e50301f21801d501082780c1e200c21104a4a600c104114018580c50110000921982040040c544418250300030b1003444800712000c00c8201e441030040380407800c9800005420b140c003000a220040810000e02603d21440002c42d084420303003e07a0210342e00960060000304081c9100e2003000381b0345102c140390358030b0165842d0185003c01400560201c0c802c1d1010843c81c90888104040044c0381e1012202007401903840141f481c0120711800d4107207 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 565407769 1250 565406519 565406521
    0x9030d020408160f06080a2409091a0c09010f020f010510030510050106021b03011103010e091c0e0405040f0506040507140f0f0609010c080c03070201090603051e060102070302090c0a0305 82
    0x14807a218a130340b085031034a072250361296581000c004054110b540542c684082c1c400d040c3e0308805000e40301c203406010f2039100001d2000c0c1a1400c1d82c04041c0c3d050544d60582da00d0001c1040820b02c0c102168600b410a18100740840c8002078282d00e440c160600c0a040c41d400c2400300120640e1090b020000c69001c0c80c116010801070f41060004c9410a00035040180c000e680b034090101403200c8241c11411002c0c00000341d040b0780030a00040c50f0400e81060424078840010b0180c1c58204105130440d85003004c1f21400c41c0c00c900030020b054908d10b04481c600940d2540005004d10200041140600d504402618454a807a02d403d54035048580554403004070902400b00440c18801e20724100c0d10005800c01d6101000f120401031642c1010b008039040200302c1c80640c0c001444500501070046c200c0c1e0007903031150000d20000d0400070542d004481014900310410000c10280f2000c15941300741310080c44856203030704004070306004c180c0e08040d4024104c0c005208402070b008000b0142d40c03119a80800403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 565409019 1250 565407769 565407779
    0x11404021e03070b0a1808030333011b20030d0906051b0705031609360201120212100b03060a030b0a1b030903031505030a0b09030d02040816 62
    0x3058035076200d9800d503100304400c4c043d04018100a003140c2c034045c01c22851100c0c50050383c04e0011030b00c0d0000b449981011081c40b118800d46180c0310218540c074040104403104000354a8444120790b01d4050402c65118030240ca4540c40891044006421141402485102509203410101048080f074003c0c407610805d4860240700d600d00d48280e900a0340c1d100c0c5024803201380c80c0311880510200b0754050145180000b0345513010000d81c0b4444628000c00c4042c02c1c42c00b200402160440c0d400c030701e000d02207900f4510b04024075510724040c040d0051a08180e0303084030300040310340580305005a0001d03440002c4803c10010107554943c49580c09070710f1071522684580749641c084c04151070058102e04007240a0002585d079006480d48200881d00c000303410100b046000e007007100200b0f100f41c042690340c000303041030550501460340003a01003d40224480e140034080b07a0381d8002c001000e003a40a0500c003240304131500303008036820594522000d540380d41c6c540800c03684400c00c0b00030b04100c050701c2900000e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 565410269 1250 565409019 565409059
    0x33102091b040506091f11060c13180b100507060b03030f030c160b0a05071b02130b130504081903050609070f110a03050a03060f08070501051b01140402 67
    0x1c80400071004807814249844280003c0350000f50000c4e500070059944074240c02e006003441c003101040c42e640e140c2c075005280f0100c2e00341a00a0706100710712004004400300200c4883c40352046400034104021b0803015a0003900040c00a11803283d0310444d410100c54059501138040c016141c0981401c000ca450f0081c00c060340d130301c125201031760344c00300c20320029621000c104e000c3c110326481010442148031b5241d80e1200d0fa044e00b22400504240d4590030700c06010b6100071a400c101e100d59031075511102083c0c0010792001603ea03404604103480700c030340c556251541400401c01480c000018441d81c1801e01d40050503400124494a502d54020011060144079020342401032001401582c00340d02d95480494002d2190b50b0110288072060321020310101e4100004840c0c01c0c000e81d602ca4461040b02c01c014142c400580c0280d80c600b400d0b501c10700a2407401b050340310481c1e03001d007071055031141c50100152030304038403904a02c11035107010407402251000ca44094400d901c2211072103030708519903824003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 565411519 1250 565410269 565410301
    0x5101103100e090c0105030c04090c03150e070c150e07140906031b0f040b090f010f06050901171008120703090609080c040b030c100207030c0902070b0c03310209 71
    0x125620101c1e50b00703e1303540518011500325050b031140d585010b440369902d40c20b44141694410019a03200d0310840c0c4c4282c01d901020140500318213060481c240034000408054a182000d46021146048038400c0e6200f03030301400c0e104030b0340d40c2950384007640c60541e400d811480c4000c250280c002e00001801500d00400c00f40c50021341d00c0c0c880c44400c8560300a001314008102c44241c3c01076900e4001c0c505980c1c40e000010f02c13501da116002d400540c10080943c0242195070300060a2100a00951005a030801324548404c5962504400b035680c0d100d03000b0502c140b240d4089041c0e8003d41e012700720000d05901c01416818000e499240314240e50f00403c031a009081d03c107156543c4c0045806441d68034042d008500351000041c1100c0c59020b03107000050b04602c9204854000d6408000704008002e040080840240869201103051400e81d80711006a00c8000784651203880001001a5005441c0304e047e800070f105e040714144401050420650b1802d43d1176400b81c0c13144910800042c00807181c0700e811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 565412769 1250 565411519 565411531
    0x108010507050a12150b190504051c06060308040303050a030c05040b04060f0215010f030b0109020702010e1011030712030b3c0306090303190b0306040f05101103100e 73
    0x10b185444144081200e00043d803010508605440e003c02d440d85c100150f043c000585007440d0b506540b18546040200100d07442c450010503c0000e11040182e961035488070400100c045c405541002a546043c4000744881c1e040200390080114020050581c000064010b40e4a40d4904122091f0300320402c1e20175008911a100e035141c810001841761500c5000d62014100c00341c011201c950700404020340021400340c0140c80390100c408410024807c2040da145e00401040c4421468001d00740c00003401c0d41c0d10503a0441c010a502840d24044501c00c444540882c00e0440c1981d44a003400e1811440c40181c044010001070704001c40c049030307403600180b40101880843c0012090114bc0740c0c0c0803259815410f00c100079818204c0b04ca00c1c00f0380b4284034480c80390001501031039580c600a91200800b60400703c0565900b0300e04800c0c01140d0718000382d911740083d085036030100c03015035501e4400c1c90034005401010f00f450511540c61111001c40e4091800f82003d8052003a88a444190780400340d80102d130710f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 565414019 1250 565412769 565412777
    0x90306010906030b04030f030b100e03010f060308030f06011110331712040f030c06231b010c02071503150b070503040503070815340201060807080309090108010507 72
    0x201740040d000b0070f8a4680008503060100f1000d21050008010914540380ca0000c12800da80b525914038003032045130201031500d8000c01400d07085450300030706400001c2101240d00140000f203002680104000108a10306808032680c1031564041c00300a030035243c0510388000200100d03013103400d0521820004205030304603180d91041c90440c1c4c248901d036282c043c0003a240285661191511013000051000e0842070480302c00b454514a05105151816030040040200b1300e1100c3c220b0240c40d4141468145a5040b500d44508a00205101c0030032800085007041d880c240d1680704582d00480e051003110903000f040c90b003900d002041502503030114440da00b06004007003404e00c2040c40744d07009010309a00680440c0d05003500c44000c6450078810ba0070080715944071500002d40c00c0e5242a10540c051506040c0015001003000ca800a80581000d940d003212044803d0381e81440c0b00754450f0004020040840302103d9549c10956180e5011052140c010360f1900004240100305024140c007904140e9a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 565415269 1250 565414019 565414021
    0x506011d0108100b0d060311040b10050c0304050604031514131403070f0302100608010c05030712090204151e06020a0f06021201060e1c05190f0215090306010906030b 73
    0x20044404510040070090f202d02d54000100380c040980c03019000600720003000064450850804001c0a156071484600c80c03410300c4800b0354540c44108020014440c00c0c140541ca8820f034038061820f6018a030002d40d086140898008144681040c4180b40d480b01c0c0403040000c1c0028400071007010400303c40c080303c081c44210901c00012001410001c01c0440c14003902d050028680d47c40c4240f107020b45041e001030707024a1241880e581d46124210081110314000c000c0b1440041001c2d00f42d000c01007405050100d400d0307115070308080300d420510481d0f60040042149450045034226014818001c0403040300c0031003004c0649038403440790340040d504c094009000d1400b0700e559601c00c0004840b41214455024801030f072a1407011030459001c1c100301c7e11a51440c145003018401032401c4295080000c80b004d0841101003030300810071440c1c20040a000e5a400c202d0f47c14a00d00548460000a4008000300c4248402d090824094000504101c0c20342d03401c0c3c3d0f80d6030301d80d0b01a0b955074000030f090300341070034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 565416519 1250 565415269 565415327
    0x1208040206031801020403020409030201020c060f01033c0305190e0306010905041e0609020f0103050411040f0209060c030304031106040b130609021c14010c051e041e030501050601 79
    0x1110311001c110f00800094500354880e40030405580002d00e0840241c1c3d0081154442c04006201e10360780100004000890b644c50341e1034100700c1080c401d000740c030f144e1800311202c1444105c9401c216500594001e0203140683c49207402031541e44040e4611520301540c03003113504841d100344c9100e8050300c03009006040c0c07030342805a040b005081c05041207c2e10b011964040c03558901c1c448a8000d905d000e0080001c50721180d0040c0017544480201050402d481c280422001900e5030013049440203065600140ca4940d48151800a00c2100c0b1541d0340b00b600404c001c402c4601c0000114070407407096403400c03800300c0950800307039450f01d05540007040c20b51903000003052104d0108085820744d004103c0801d01031000d40220301502240c8550003411450000248e00f07022441c641a1400f880700002044441c070301180041c25030107401001103000700ba03001202e000f82001002d54001d803401052402800302220005013851045110480d940c4d400c0100042980d0b000304014003c1c8010002241c0b220038941c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 565417769 1250 565416519 565416541
    0x8040204180309230112111e25080703110c13020903070801090f060507050d0603050604050d0509010e010e04090c08030c0c0f130b180a0e06100b160614040609120804020603 76
    0x1225841042000d11034402c0c6101c849008c80c2c0300552417010360ba66250700514801d030303141c60081f0b02c03442e240006d00e1400c0041c84078030444000c81c0d01442d00075904020054950700b13181c012031840e81d00c00e440c0e00341001200d040394000c0111401c21412218825071ba114a00d007a95281d4201900c400d403013403e1500420340c140c100710b82c0401d451034054074040c4150307885809c60390341b600b0a4070b1a92011040104000c0204204240e48143c6d0800d00d052010b00310009107100c404144803070400005003200c3c8840c1d150354111000e01580500030180345502c03250055030383d40146010280d10300c942d8a513244242004d4910702070f41c18003d04104a00954682013002a240003284550032903a07040300204501c41818070386000d14000c07000450b444000c0d211091522102400001d20f192802004101d241c0031101103407007140d0044029020b0340498103000c0b00410b1503d140a0000d5010b0040000304070480d440040c045205d01616030120741440b50468105a00b118001d404c4981000400c10175030360 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 565419019 1250 565417769 565417781
    0x9051e1605041809050706050429030610050c030729010b0901050c0a0b0a060f0b0906040911211009050609180a0f080d0b011e08040204180309230112 66
    0x14001300d00c2c1d01180d0364280c43d0003101d51020001500206081c4844802d10001c0d00c001105103100306007980150f5081d074414407015188521500302e0a2a47c1040b901410a55a042c0a1141502c4d1102002c0c1056402945880300100840e060400410000e00840740307070341c4c144e80988500605050a0301d0041d80e9030303440102511024070882401c54000380154414a00c28040000003040b114134111a140082601c0c3e00310140801041c0940176980e15518292011158007000104440351130192000c40c0d0300c240500030551200d002000d0141ca024501d4290243c100d89051000d06592920150120340c0160740e0207500011450116100b00020412428501c2c4810203450303d607162503441410101280104588404c80810807008140b8503104207500c5180a00b0501220103210b1480c940344100c10203103a007031022002c00305082d91155440301c8c05522021a5641080b030759800c000d0a158424814000b01c295240301c0801814400000d80100e280c06840b044d4180010351a08009089 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 565420269 1250 565419019 565419059
    0xa0f020114090409110910060e06130302060c0319111b03011104090905010b0103050402030303040813030209040f060c02010e030f030915100e06060f0d051009051e160504 75
    0x40144561800c0fa40d81c3d10610110300e02c50030b0140b038590030600a2041c07016004000b41c0404210741c004002c1160001600320b92422308035481c4da81c81c402040e041444000310b800113900a080810580460b010010080100d4070240c0c03100c1c8484250080b0440c4c1841da640c00c1b0010359007004c82c400004c4860304c4141040c40c0c40040000c5440d984a04c62900c2e2034002c0e610a40301141c84101e9141845030030320a01e6040303a0300303180500003407420790003013660707444040c000501c1448000341c422010000c01070004041c0d03500034500c00f0f56040a0811400da520303c0c1030143d49941c44c0402040c60a401407240e10044101d00d0301071810454800380358a21038000030035000040c040ca1040e01d1200720304001c010311980c4018840d038142828400d0061201c0b40040c084c5000e00030411008045070100702c00e40c5c0280c0396000021442c0d0303a4a0000190303a801c03a60282580307a00b03100900c00b5045881c8d8865241454050400c6110380da00c0c0306500b00403190b01551030100d0001c00c0288180035043c520034510207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 565421519 1250 565420269 565420307
    0x909110d020a11010e070f081507050d02090d0803040303050f010f0b0a0c0204060b04060909062102030307060903030203090c01090b0306041808120106080601050702030d051c15050f030a0f0201 85
    0x20fa01c208050a68642d60b402c1d07999500070300411b0241507400a0b841d800352403c04002d000d1324124a40322418040302070013403018402c020072400003c8003180c040703071509103018004030036500c55460020201e0700700351070444c0071a040400003040080c00c611341c28101c500b03d20340440c81500e4030000f90b0f00c0c0c0c0d0255401c1c800300821866440d000d0f840d0381c060b42d80108020a0a039641c1c615010000f0821403058100301c2d40142805810004220303042400454601e00c00c0080c01c0303220302c5100281c0b0314414400c0060456007803074101c1c828941c255020f14441c054003c141c8251905007001180c003213583c0d008040c14040184042401428594081c2c02d54502e04030040340c1d0a14141c580f45a81c0d080f900070038a4a5800c10014050a0f43c0130949c02d82115082c2005402c2c501d0650009484000060307402c401c1000108a021001c0e135078251030380000045600c10045d2860900154269010750300585015802c001e608081d18100001c0800c510781c0c20405a0b40001304e20387c011508a17520801c891108 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 565422769 1250 565421519 565421537
    0xd1d030a03030b04060807030b150319021c06150f1215090f20010215090c0907021204091d03030106090b0304020f100f020f1f02030912040609060909110d020a 70
    0xb004100301d801d024500484003009e540c9040e00007130701ca14030b090600e00e000790003a03819940d8a0907a0100c00d500c2580c112442d40000c0c8544078108442c0c6629400584158200718001c1c6445403442c40d05010340f0b0320300d1206100d054480c101e910903150703100b000070310154540003142004c00d002ea0003a16028840d41034980080696203035600003072040510074901c0100142425034660701008a42d07030104e40c900764000d0603d005c1c945142c0b2001d6143d0400d0140f05280d001803149403003400100043c2c0045a0483d071100d8652000800504000e002c4040e400142c0343c55590550001041d24100c90260381e9420b500c6090903c03400e0175400250080703811001d01d40390740410350b451610304000b89a8580e03481c3d910001c4408001d180c488101c0411042e504000f8076550003d04a0143e0103c0070154074026030b070f9440f00010700c1d00d05540141c0580c0ca021011030040f40a941c4400440c1c101c035000e035500011217440703075008002c40c0c0b184440820a228200042c1700340d84c1250300505103845403402d00b0429 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 565424019 1250 565422769 565422779
    0x90901150b1b1c09091b0302030a0b0432010e0612120f0d050f01081b010c05122d18010c020d060e1b132c0d1d030a03030b0406 56
    0x3070580040203070200d0300c940d080f104400951103941c4100500d9000414090204280110181c0c012046106400c0540000016040d141c0c40c0d00300c61803400006c0c00400003100d000091302c200303800031031450038500400c08400d0103e8010384280360586082c1100300802d078542c24108200c01d140e101c6082402e019104000e610701c4a482d001c0c0c20842d400c280c1d010780d07030b14203504502d048031f4005240454a10031031005000081e800140d030100c82010700626009101c080c40180e5090510721030003002845000708502d0707041c481001500300a28103103000b20800c1410940d0754488840292401100b031010300007000d0204802c035a102d40004103062040400404d03801256080049140540e13450b42c4a40840c00185000c0209000b43d0104980f541c03e1000003400150303c5021540500e100140c640320300036000040d07008110f044840c0001c0c08440d4030440b11085403039040307005440d8045641a80c00420100d0a001c407040c030020010044c2c070982a0303640d0180c00808440306203e40180d80c030880846c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 565425269 1250 565424019 565424023
    0x1e1905010e04061118090c09030304030807060516020d050307050c0604050a030809011a0d05010b060a0c02090105090f180309030109050c032506030e0111040311090901150b1b 77
    0x1020340440c10140e00540b4150030f003d0305030760701c42130b540b00441000c001d1445640c01350301c00341020100440d0020815201c803010b40c0c0540c05001a01c1e540f40c080003c0c00010005084010801d440c072984050126503500c2016030704500403d0164005604001100900e5900c98001140d00100900307000d401c1c01c4052018510b0218121000c03621544104880802e2541040155074007200c01c00c001c0c0070540703d010344243c90103d00104540201d4503110300348100182900119051407000c1c1a0540302d00d00560024420380c005a42a40682c08190001c1001c2c14410303505031040e030203e99101c0c0c03a501d4610400c1c40d0000c5020b042415404140134401c01c5540038001cad144000c2c0640014616440b600b410141041c40c0511441080313552a10843c81c0001002510411121700b410000340310f8403180c440c9400740c609110000011000014084100311000320751f010b0141c6c2c00d0b103006000d07603102013014bc01c90300425102c100000001c941048a840c40000030181001a1500d071781a01150148941c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 565426519 1250 565425269 565425271
    0x161701091a0403030f2d0917130e04030813021f20010b0d120509060d050f06010c020603012601020f091e0607290403090503010e03031e1905 62
    0x2889500c1d5009110515074036000d000800c1c80701c818200320365409210080000104002c10140083da0350311200203040070365100162068010129010041c0260f120006651114416481320900114089810703034010905504c116450f45880382c80792111030060440014002d0200c3e404000e0b4005c401110400140d101300c1c51a00391114082000703100c2884400d069400305c007450380c0c0c0c034200c800455a40c40c0c490364440740c1d4012a80311380710a211441112580702e101c495a80010000441140444482d44054030a02804494000341d40b6241d0044581c42d42240c03020754010030038401880f000511341500c3c0c01c0041c40500040f2003140580e0b490342603070482c43c1c0061092002140c4032003c0e0504081c145901c80120b9007071600403400200081d202c1c002d40e02c000d04841c1e0340d00d04001d84c0079901c1c42c54600201d0f102d81d00c40901c0c5028a0300400c03001e07440c001c5a000b9401c0182d200c1010b84000f06a074005c004014006103da4403108040410040051034810900314004400c4000d41030340c4105 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 565427769 1250 565426519 565426553
    0x601030f0209150c0f0c09040201080c1b03070c090c091401090e09031206061e0306010c0f0507150c0f02060c0c0607060e1203070e100306050a060c020f0316170109 72
    0x440d00e9926104c010741c141040c03508045041e801207084061076684822010b90300c9942400c0244c180e80b40c2c103001400f140600b2181c0718882030f007050925640c100000c00341c159244610400d0804a4480100801b959058003e01010444510301402400f5031103000c1840c1e10011324000c000d80c2d5070740c180c030340614609079142800c0da000011001c810b20140d01070306600450680300e2514210302140c40540c00d50819030140b050000200104c3e00c035030720034030035407003600d0b0043c4042c40000f0443c1041c60b214110f038403811070880081031800100d18081c4440c0a40c40e6001000d8000440c00f640074004141d0019009040c1801480d464905030b9a480e4040c02d60031380601d10009031407800c004150b2510300c03c40860880a0000d1080121403988812000f2084005440c8900014040d14013038001c0d114540100d40e014003145000f1440769400060031071154021518080c003580d40005154550404800e055a0181464000d20040c80f061500e2440d01410350000500b11712a502c0e9080d0b882160951 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 565429019 1250 565427769 565427809
    0x50904062d0f1805030a0c0c05150a080a0b010c060509030d110a08060105190c110402041d1e01030b04080c030a120509070e1b040f08030703120b06030601030f0209 72
    0x1002c82400d4a1190150b081c07140d101c0c2410072801c0d40c88036980c9000b078104030010030680b100381c2410080e8a64003107004100183c21034100400c52000750115402165086000945600c0020070580c41401444010003068481314121070250b1210000f9120080628041740700c1045038041111442c0b081180b020b0a00080070341320b400e040001011808081c14580c100070050180c221209680030ba140000500390a000316011355901d881460405408100c9130310901c0404d00007180c08103844003281c1007803a40285c51190b0b66071105030003251b00b007040d0144049000c000510008500360000e40e00580542e002c0d5007000442e2006070720710f5120801403400191440b0950f08464800e0188540011045014044403800c040074a004828010060202940f00c080b40c12029035040040b24050118010041102030701e4204460343d80d40204021000100b00342c5c1d0310450341c6800d105031400b106004002070719503213903040118050225901c07806c0e805942005403804565a55003421105100001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 565430269 1250 565429019 565429031
    0x30702010914010e04050703090f03050c0d09031533090515090a18140a110a06020d030c0504090203040501050103031b0203151e10050910050904062d 66
    0x200040c001c440651249201c01d1854241088603a00800c002c0d100d20000c0d500002d242e613510300110050480814040c00900c0040e0100043c0b41d0b00c9002441d041ca070030f00444d074602c40401070032901034075544400740080328074030034600440e9090b030485000035a19000032150a010800d46000c1e007014040c45105800383c0c0d5804000350002405440e40c48002d21508552480d0100085916914018800481c4903a1104500d070f050074245160710885402420001c33801103907014966448404d01da09031070a114100741e10519250001c005c2007076884541c06004503001e6508250041d0003001e51030b8090103800c1c0804541c4c2d94151000c1e40c401c6015600202e00340d40b6600b0007134401ca4216207000100100c800050015807000a170000444c424510080c0545e035803180d8034203415440d600c840e005441801d043c0040c8200c0340d00c07884140c55080754085103585500e900c00e8002e10061203100e41200d005030015010644a0b4405c06196038511680c4162030021a0340c60050b410782c0329100c3c1d80958a05c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 565431519 1250 565430269 565430273
    0xf2205090d0302160308060312040305010902030105090a0305070b0c0415021b0406050a1e080708060a0c0504140d05070305100c171027020706050723030115050c0303090307 76
    0x1180c48801e03815410304601d810800d200b50040003110340009801c2c000920007003001500c0802010700f5020b4944910354a03151240b07080c501030100c4100507442503017000c002c5408131b2400b2412071851581034032801e151500e01e558405d44e103107009054186054082c4400140c80140c0805203112001580c00380002c1c0c40c282800c029000450820b00f40035a00d040310900403a00c40c002814283ca5101c40f844000d40c102200684072041580c001132082c1c000c242c1c00240e440c0c03000071500d01800c0301020911040710450300407200c5002d40d10030307a4a254140c46407445d0302d050030313070903032140b103002e00140d52003d5100e0302c0311403500f4010303070940c49550741d83e084801000f607002421050450944051064a00340b81307149913501c14550090601e24480034501e03054642090340e039502c015150160071f40d11022182402d4005140c00c44103a80400c0b0317080a00d441d04149060250152003a905403d8116420301d0032111804406800c007a0902c001008484640c0390100041c0d07108a25540045690301024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 565432769 1250 565431519 565431523
    0x23041802041506090b0c030418060510030b060901050c101b09060306032303161a1e010306020f07140a0309081f0911040c0e030f19020f220509 63
    0x40780e4071020b80b0b261075000c0c001994002d07078140407651600d0043e510703a40b00615250840c440c0381d0201c3d55003040300503420440407203070700b1031021108210350350383c08600c40c2c0e5000e41c00e9494810760030394400003c11034402c00790300440103480d00103042011a140b00d9200a1090100d904c80c51100c1080001381c14000c0c42c80e5401030300c1030041c0101d407905100035842c41c0d598100c0440a0103070523050308840c3d01100040d14042003130391840404044040280400c5040c41180381041c41c60415540050000092105022007103002411103980b0044415a00c3c5858000094000401c59070301d8003801c03c400b0001c0341c481e04000c4502d0070b503040941080c0c50346250141c003401d101d0384007121a41024103100340d004a1144020303402080110042000c8200e0310300340d0143e40494407200c2c2d00c240382000580d480ca900000030851800d0650481d80b00140160400e42e680141720301068007441081004801824010845050813402820b240c1044014500b5500302c80c0303200560100040d40c17a020000c01c000c00b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 565434019 1250 565432769 565432781
    0x100e04030905310c0909051b0706020c0c04091e0c09060b2206080c09220903030b031c0c02040b0909100522021905130207020f0a0f2304180204 63
    0x341403c20800580c0c0c24134040c205644602c01d281c9840e549500107401d0003400350003600b0001610101a0f035503505c2e0704e00300000b504041d800340a14402c402d4000074a041034481c2c91459a00091000031840d05080c09001c007103850781d8100c50081aa04002074408524058000940002c03a030032034503994089481c03001e002c1815aa8811031440d03120400c200781d0002506500000c401450594501c0072101181c095011040ca0040003152215040200300c0b440d030203411001c3c07003654107203c92109441015079032219240c0c0b00c050701c5103106d0410040c6006040c02c0340800e03c060004101210090001541c2c0001101c510405401c40c4e802c3c0030564015205040d07022070b140000d500c1c488010312000481c0c2500b008000d00660a80ba100d0b00242d04036070f480401002d00600001d840c0041c1c400400213504070540c01c85c007030307000004e00036468506034201d08142c64011440c11400c9280c900f00c403541c40d150305503c480e1201e1401c41070410b41c40d50300950366250100304501503d451031744180011245 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 565435269 1250 565434019 565434109
    0x180a0804091a040908091e1e090a0606020607051305090a09030801120305030c0307022b020d02190813080303070c0215070210080912070b090114100e04030905 70
    0x102d00b04e00070f40003440311016500c0300304040d80e01058000114289400146400a5080d030044c8114203864514600c0e03041000034107402c0c0d4140400d5101c902c18001912160302401c0c02680213280002d0b903480c4601c1c040c081440c1e4610414500f40c3e40d62003c1a0607000c10303218554401d0b140c000340b900b41500980c4960041a141e4920b0354a500291070003005408060300d44810307294004007044046101b00144040201304041d011450176414070a81c914100403421140540544145580f265002083d01c0b09039448a416084240316959522400e660213076032541c0103c280d00e45c0114801a042000e588941d040351507046c0743d030b41c0d41d00410401a16118900541a00403c15280142c03640038035000105d88504182c84540c89041c0007a01380b040c065410806410040785110074400d042074000d008110241c000c001d8070200b8564030a00740030456213032440f5143c0c0700f010400402003050141d441406403030300d00002c1c2e88820005801c1c00c40c2c00e51855a00c802c01c090800511203240c03901000e40 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 565436519 1250 565435269 565435271
    0x5092406090c070f080d0209030316030e01030c080f06040920011407030f03050406060803071b05030f0304150e060301090f0b0a050d0b06180906040507050303070308180a0804091a04 80
    0x10700c560740d1041304c1d441054010621803010801042a0650340c041c2c0751468030090035245c56942c2400040040355901d4000d800044041039071082c1075009100b140e482d05069504e00c08165180c04130200c401c00094007841c0c01a07660300940e40894242081f5144030004081d055500684620006116547d8150141d20b040410041007000030741040c1c8a0b4200c01580c14040358690b520305264004004941c40300e070050000182c080204003681800025545000c1d4241344003d80b40e8091660741c0c100d5130480002d66100700824416055890949134240410f40362104030744aa0a010864035007003a030000200507112605c403141200d080c0203c1c44107102c140c3d900c41e012071070400000c050f111070b1903010b840e4a1644001c5500d68503290740c50350320072408002442813400d01e48602da50315001200c1c152031900038464080380b9850044121100590181e8804401e5241c40400808103640c920081d0100e102e84003405000501c070901402c010a2603200000b81032000d080f031702c1c44402e10154814812 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 565437769 1250 565436519 565436527
    0xa0b16020d05031317030a090c0f0614131e080f010e07053303010e09010b01020d0509012003030a0c030b100c08070b0a0f06050f1305092406090c 64
    0x1c1540442920340c00918401100c0b4480c1513030030001d407140c500340000c500080c0000b041115520261b0045031500d48194030300d080890b40c882c1c2d000d0b002403860180200180c0f07621502c80340407000c1c5020745000f68a8091044580781c3e00d415403d46191040c030b0145024080b45020080d1034001c1c000b0380c0301081404001c0c001e0280a54146c0c0d1118944d01030988203560f4805402c580c921000a2090511824075900780c10a410600204454009108024040ea841c13400622040c4060080c8071030040107800030658000c2e403120688594110302d4089040100c1803110f0517071440a18484030140d44210003a50f524140b00c1400c1d801e0700d440e515007000345406c180c2000d00640b15800c21804090052500b8440c4a05502d04204c1500c5041e2000e400780f9000024440c64090307035401704000c916410010011580c1d1039040c41002080d40388447c0e40441005017141500b6a20b4000030303848014281a11121340c5d10000c40d048a40c0d0201240b0201c000100c10008036040001d01c403908516200c01003414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 565439019 1250 565437769 565437793
    0xa0f0e0f010c080a02030c0106090e010e1b090c190c02030c04060e01030602030a110a0e01080106090e040209190c020a050f0c1509010e040f02090a050109050f0103020903030c0a0b1602 81
    0x90300c0759200b0300520b450030005080030414402d05c00e0f50000c08209000380140b40e40c0b4800a8050300540c0c4039003400b54038010b2100c01503040000c3c117005031003104c910340c6034408071407041000c06030004096a143c40d404110070902820960f176051100911912070000805841c0141464004086000c5018a01d4140140075600c40317402c10310b0443e54001c4e0056526501c006181014101007286185140008078069a9a81c0c02c0302401090704420381c2c0b40c0d170071030380d8407a01241c842a00380306000a030701c00080440c025043c54240c450380400d803210014074001d4000354040c1110000d0750b401005821a9888204000e002d00180d2390102d103800041c00e9004030030001401420720441c8042d0003940000d80d21a041e4010722226030215002001000303c0850800254041e5100c901028403440380d81001103007030740c000d00851007502c030b014040000d00c106120065000354448948581c1c184414805800014010455040c509204905046503800c00e8007502036608007a070f0f9a10155000345a540714 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 565440269 1250 565439019 565439027
    0x150f060c02120f0f030406030c020105060a1511030313020f06040b0318010e06070f03140424090f1103060a0e03120402010e0d21020304081c050f0a0f0e0f01 69
    0x154007034046441d01200d00008640300d1510462540c60400344c020040b03402c0107100048094400c03198542c8013842910302500e403c0b400c81d003003281d040ba80000b41e000c09020f16203c4100000500030941030480320000003000e9603103142c204942c0d0000080c0d44693310811801c0c440002a05084151040b0b8181400d00962000c1404010306da401074522840f818103255100750820544d00e043da0080e60014140748600800700701c038007555200840d081c070550008007142030008510554029003203003a0400520084c41c00c030180111040b10342034488941d28086030a03226041000f9108800304118200341000745410004001c1c240c0c51440e1a280c3c050503040c00c0481101c030120082600c0d21030a5031a840160b401c9205094019084600d401c507480420040ca0210884001b00c0c280f002c0c4800c0781d440040380d07244180d004179074213500641c0c1031842c1d012041c00c5002d0081d00c1d40c108207081c41c0c0260343c94100c540004400c000000d44005d40c0306915074009080740c10501094482c4802c01d00c103c40060 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 565441519 1250 565440269 565440287
    0xd06050a050319170403120801060c2f04180c0f0f03080d111305010e03070b120c07020d030e010e040b1e040f06030c0509011d0a0f02041701150f06 65
    0x2078500f12200d1030b02810028032a13a83c00c030302c0480c020142d4543e5140d00300381c4e03000341c620f02004000c01c448000104015015090300341300c581d4000140d040c1c001c0c2c0102c40028510080000e034201c014205020001550b850003a40c9103140d28503403800c8450f03407a0402d00c4130080150700c0103040c0d45280c00c050202010491045041d650800c1c0c0860395901c0e0a0344510091000500c582d010b507202180b03540d501c143c680340c503c040329400d0340d80f050319445510405032103810310300c2081e0440303804204800a1800d1303500750329400061400c0b07050070000d064012074092400640110000703254881c001c901580c102c060f00c44504419a001c000085106011904604961126400812030410703040050b40c0c40d034009420b105884201400000c0d45c07407512900180d003600502d84500072040010400c40048841c585051820160742e02886c2c6840111030014a4152024201681c0801001c02d1703000000c281c0c00c0c503a100210000bd01d4581c512104440803032135030464603c1203902c000401000d580841e5903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 565442769 1250 565441519 565441543
    0xe0306010909020f06180f060f090111070308070f0302010c0305040f020402030910110a02060609043906050307033e120a240503060f09100e030d06050a0503 69
    0x2584010703400051040d40d04500c2895214100240640840390000d00f544c0d034240701514600000c7c6082c008009450041034052010900c040c060b603001c640c032600032483d002c051030003661003468070b03611040203651050078140d801407a207103900010150f09106140e0540301c079103001c10440c1000e965074a42c06600800281c426074010000c6043c802090112040448180c03404221100e06031004440c0c913000342c413034440903004850001d002c90422060040c461988485418012101500b0304100d1200b00c04d4107500d0a800000c0f403000048160100c5c502410f200e4840c10389038540b8181c01400c1e900710705041e409201072180401c68058403901004d403030030420010400c0c82940c220041485001e40c030392414601070b4070800c0c004101d0315a40040e1051861705020080310785c100003680c1c0c49c100c0900c54030b60194041800503015001100003241c2200080060350380041c200302d060000d503912404840001d8000048846840a0301c1c45443d00902c42a24165406440c080009440303660010704 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 565444019 1250 565442769 565442771
    0x1409010b0a05010c032d02070b040f0519170715020f1f1514030c09011d04060908030a050609090a050709020d060308030708013f050c0d03020307060c0e03060109 71
    0x30740c1014064030b90b807840191901500c1d804404115801440c1c00140b100e0b0346e01500803200702003464800201140c00340c900421151003a14035084c1030080b60362107440e010980c010358003004144500d8804100e07542c01c04d1100248900d50805014020703046c0d215409100755403140e071040404400c08980b40e18400d0f406030544403c0303000341890340b010b8203402e0790412500c9035600c4040f40e508050b9070b00c0a01d85000358102c83c5001e41480501400010a025104108400c040c00381c28a90900030351071307803140c42684049608501e654507003140f07030010342e80c030610305440e02e0030000d442c03c01c0c031421988660301c00010041d0940a884007511501d0760701071050380740e40004840d041d4122a0300040000c56008130202d42d82e14200d074000700070041c2801050b54001d600704048180398444420107140c1c41d42100c82c0c05010030f015403060711023804d00c0000c60303050261b41e61604190b900c441c040d003d964003a801543c0d80f40e001e031800380101c400c11441c003401e1000e2004900d555880000380b02c1e06680c03030050 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 565445269 1250 565444019 565444037
    0x2d0a0506041e050412080105011e0507022e0f1704050a02090405031909050609060d1b050711040207030e150c03190f020d050d18020303030405011409010b0a0501 71
    0x1080103401110758280885103902103002c40802140d01040c8181d00a8280c86291044c1c040b0448040c42e080c03150b5800a0604414201d54841000c1c4c5c6810407030340c5080c9179140004660100b1a0941e04d98110004551104140d500c0c82400412a06640e00b06103400c0c0c1000c650018043c00c0600150800b900300148400060308004013004120316858004040b03c16614062804a60740c1d07020a1110b80302d0005c2c2122600c906004009080640343e00030445820180100140f1250b0380200f00e41c3d40040c0c1d00c0d0040c2d01d0701700284031414a1044090b03a601c69a5030084c0c104600e000c05d801c4105401039204200d0080402da024551003a203403c100c0e204c0034122014504c90516014841100e41c16000019400500020510074845110015220105120911402a0b07120000c840080011820800c134151181d0003641c020f04c0d09442858500229a0941c0c0220b40703907400440e411901030303640c4c8400d0115458903114041c0e0081c4144000e01c100303c40500454045117152180c64140540c41c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 565446519 1250 565445269 565445281
    0x1b0b04231309120807090b090102011b0905030111040e06040b060c2b0315050f0a0305070e0103030e15070b040809100f110118110411030f2d0a05 64
    0x14015400824004241140c2141c90311030a100918205104a502180d100c81510841c1d0151200503c910a151103911011b0325040c0f60941c950b124076015411035690b49000c4120758450064003400d51082d03a16002c2543c10701040c0740c216619081c000802c0002408204056a00b814803a507001200351004a600321340c9001140c000c0c05400b020384c0703032030003042c00c1030600e150b400311000c0b15240c0301ca1a9814907201244143c00311130760300b694511a0f281320030301072001c0e04141c894808484400b13402c0d140000e0b940c0c0c8039142020140e4115412a0035004010400c4c10780c855070340b2941800888044004018171507035000d040c03203100001094488036000143c280140141038072980071010300110641485000001d10508109080001050304900107000350707981403241460301c0501000070105021151200340c034840d60000d05561090f1119480143c107421400658001c40c00a4868403140c2421500580505114000e21100100f013040c100640d942001d219900b10300007038000500f076281c070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 565447769 1250 565446519 565446569
    0xb18010203090604080619050c0a0c03050d020a0503010f0602010c080708130b0c09031612020f0301110415020c0f06030a020c120a020a0b090607090303050328091b0b04 74
    0x200341d07801d0744000040381c001750780035001c2030941c400e000c462101801814201a002c040350b0064030000280d03401408102c065074000c01d00d15458a000382001030602d0301c80b2032107034242d80c4413146440c00500b01000400107880c040903031402400d0280000e000c03003081c145009000c0400100f8210401c8101d0b8042500700083c2030008801c1074104100c2e600c0340c500501030292039885108230500a214642452183ca01e000081109540002c030135440503814a400b000300c034045c48007509600d5503a5881c841400720b0440c00600c020580502002e800724030110002e03080c011003190960040042e8a1400419035a000c1120b50001c5480300050b04ca165402040386020b403d8261090200c1000070400300c41500040e010382100d01c0b429088001d07945400600c0c7e281c00c42a5035500101b480c918040c00001e000d00040d40c6c0c4552042c00c80741001c10442580c0d2030480440084880c901d584004102c20701c602403924603000c44042d5042d010061600c2214a1a8411031080031800b0f41e47c09510f8005401c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 565449019 1250 565447769 565447777
    0xc070302041b2a050a0606060206060103060e01060c110d03081b0f0a05070503071703010f090605100c140a03050a0807052712060f0a0b030d024210060201060b18010203 74
    0x41c1100c0092001b484d04000034820350017034901500c10800000c040b98881d00501060702d080a0801e040d5901e0100300307985440602108680100007030083c0c84e26611035000d640c0a0794041c1d40e4440c0641401c209098081c000b1580000c1c0c810400c2010f40107030520202281c0c0c3c0d43c2420f00e002a541da440b800c1c01170641c090080014046d80c1c02030512101e812460006e14140ca45000c91444a03540e070360210400c41c0c070544149c641040c0c00f0001c1d14166405111038410090060310300d50350100000c0310842c00e1040c03520007103002c80d2001c941a41c15551040c0c0040d070102c007900f8014580717510742a0b41c64508842c414084d458000304070359600180ca403500314001c2150701404981003401c2400040080c81c80c21950480c0c1c4518003a03104445250001740880301072407580140c01d0705001e44e0390019008260007200009150861103082d01c00c802650000004c5491280c0840d4a06003000e4038501c080c0c080d4494402c680c145541402816034040403640d2084102c0c01500786898080d00613411401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 565450269 1250 565449019 565449023
    0x614031501090320040509011503080315031c080601092403021c051506041203050c0304030c17010506040501080c120705040c0210230f04060b060c070302041b2a 71
    0x2410400040c0341c000b00c2410008100c02c1205c0901c03082e80c3c0d0360010340c01c81d0b030705004484a04010400400116179004015a08500104440223018000901281c585045e42c4640d40030380c25180c01039502248e107c483d80b500500309107003940c405442c2c50100702001d10142442c0003030340c83d41080c03802c0c940c0c001c0d0304803511450b20041054460401a032048010b280c115001d81c90308482c00c00b2011a46840d46c100c4095a10707040900781010388a403021221a00800f600d2007048c4020480400400d15050842004000300410321500a144100322800d45001906650085090100500004c5070106800d0000c3e401900c2100b103960300354181c1803502140d40d0145d0b0b00146800c060f89902035000c41d54035201500000c0030700c4a1441403407480d181010900310210f4094014000c960464803079481507400c01d005440c080394156800d400100d180d03000650075142c0303a00c480010005c41c04c103070040c0c0548650034400e1018913504520090721080600b000c40343d1078003107e510f07030058428466144046079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 565451519 1250 565450269 565450283
    0x61819051e06040504031b060f111c500103170a02070315090b0f0a0e0307050307060203100e07031e0c2a1a0601030606140315010903 59
    0x2041080c07451a010301040707849041401e00100240590600340a018061070341940c65141c00034a4000c2803219460000044620a0b150701401249940c980500000d00c071040135625a0341000e00e80c010001c1d4102150a0406800c0c086d21100d1016910080d907c810a40444e05d51007000004881c40301d003c105200003207050403101202428042c184c21181078a20500f20012001f086800c0c09010303024140ca40c00050740103000600c0003d551468184025041000c04034003e50301c0e9135003032881c107002c8906004401c0c200c4100b01402c0c23054054003280e0a4208007071440d004841c0c407107548a128291000d81600c1c2c0000100713010728034031200c0078001c00300808101c03036a0a001070010041c0030f1072602c84c803001c00180380c7c803d18250148074144001d1115110114828610030b6405c20800300ca2200880c0240042c40d50b02c08684500e8880300d03901844002c00b00a403511100140480e15a60414010084075501000da000107c104982d0030403220500d141c0412079450049940c2e0080c1d400c014504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 565452769 1250 565451519 565451521
    0xd030f15090b091e060f0a080607030b0a0603110f030c07050f0a060506041b140d0204030303060923010b0c012c0d02030319050c0d0e030309011406181905 68
    0x1000ea10100b15400c0440f40010a9210941c11680050120380180e1010b950140850050718100c0200256410040d05448185940d0440507081440807101003000c01d03180d0100165501d880001440a0070860034104082801922005180d0140e80b00c41031401c2800008141c9502111017aa101554841c0855000c01c40310011742c0e4491b80d4080c4202d92070703801c0c20f010620900d8a4012481e0326460952344952080b0003400071240400b41408a6004072820030500c0d001200c1800103001035802620041071441c80c00c4520000c0310035040c0c082c242007100241c000c1c0b05003034030104603044482d900f12181d181c24180c038a0500506c20300c070355001d204a4400e40780c0101ea03429581009803816160070b070b40200f5203086060b6147d10045a85840c44828040c1d817240030340d4158400c0742c00c810300c10300480c200b11902200310704640c511020b37049648d0000c02082807a40302402100c990380100504011281800740106542100a25850181401c5100000c000100a10740340040e09580390f42070090f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 565454019 1250 565452769 565452779
    0xe0a0207143f030612160f080102040b07120908030a03091a1b0a0e0a080102040305071a040e2a0d0f15060c050304030501150608090c01020d030f15 65
    0x51a21a030245500c0002c00c900302400710310311007410b4192000300b01a800c002c5954a0781102c2203920061a450780200c89019007503141600300441c00240070701248401d8000d0600e003201d5903840d055402445181e00400042c402c9550711015104090b90000d2003100c1c0c1c441c0d0160580350507501c4d8112200c04d02c00441c5d1040c94a40c190080181c00f4001c07081e0000c0ba942c60002071000c1003044031080c0c1450703000958164401e502c1d0008011904051a2000b04015000001034401700941c0c0000d0140c0e4000c603081c814040140070480062a80c001d0000001e140e5450301115401144150300101c1c03e248009241e080c107401ea240d2050356050040018041c071aa0248180d81026051000b010300d00074143d04000e90754443c001c40c0351010a5084a0240340140440f01007c40c460120780e10b000c240030000c0000c40174041c0ba420010011124000d90b424210010840800240516440e51151242864a1740c01103038422404a00340360106504544a403c0d1018001640610f0100108118000b40d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 565455269 1250 565454019 565454023
    0x2607120f0309180603020a050105030912160501050412180305060604050c040506191112160503070b0a0f270303050703180b09150105180910090f0311060903040e0a020714 75
    0x4c00e491080320010603254840c001100d950004562940080e0300c40b0390b514601d030144001070305003900e850f0250341c1c0c501100c3d9642400d503030302079504031580c0701c40d0003240c404103406c00390000e14008461800d100440c82c42d140c1c66565030000d07005a0285a8600c04103501c080c583d011200509006001c0d1503031143e1510102c1240040d414041c0d0004034440007103900c40b04042848156030007110451414228030100401c0c09041d0100c0440e441c0c07008000c000c0000d50b001001c0c9110b0b1681000000b001641c1606017410798001c0036481e4004003c10981150440a943c01ea00030203401d0315000440d65691802500242205c00300c0d0301186a03489200c8040005a845843c0324102c041c09541741c4041021001050343d42c00e005144e88000e8041c1d40e00100400480c1d40c6520540200c200c90052640c501c40c20121400c0c1d913401d07611000710310081414940c01c542610441c9900707400929452a100190640320b004901a03081c41c1e06075800410140030150b01038810f01c58104250252541180c80240c2d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 565456519 1250 565455269 565455281
    0x403061b0807050408030702041116140709020a0f032d0204140f01021905030f0d050f060f1c030203040b03070314070207030203120a03152607120f030918 68
    0xc00040e003007000a03901921402c10340d4100c42c40d0900a40c10107000751708100c0649403100084100200502803001089a40390303d9900c0c8500800340507a16a01d015081d5043c0082900b194100d20700400c640a01542d00c00f40049030310003680780000d40c0303004810184000303d03409580304012440c1c05c0c1d404403660036280c3c0104221041706213460210300c02c00c010b100410618003280380c0580c000c10f5003429001000600d40c1d504501c52400d40340b425084105000440c0c1000501084040e921410061850348480080c1d030482c0e411618240b1440300c8500083c40b80f0100c00d480c000c1051040c3c000c50030503008105407009044190305403a00c3e8500705800800410303000154124040c10000420f03600360000c6000300a40e60003401030700d0301107540008403c2c503a01c042080c50400d956070340e6144040c1000e80c0000094011050810000c0141142d240501c0524000d50380e8030b500010070030042c501c58104100364095025418114151050500760f58803071300d0364004049400f8003130306000c0c0e0044e00c0c1c0c02a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 565457769 1250 565456519 565456571
    0x9090a151a1b030c0a06150e0424020c10020d061e09020a0e040e0c0108150a030f0303020912070515040b09130f060e04060b10050703030b0303040306 66
    0x90580c0e55891a10812650702074400e180180d40030001080030615014505408810400480389007180031180d803460007403140c9041d2500d80c0e41d4104409221030070081e650007040300790440d4049017025145c00300c03c1724402842d0154a404d121242c026a402d5030150340206881c18141c2e40c95402c06501280030354042484240c2943c500348002c6440285040b03100d02c06640749140c20042da040403041c200952100e80000c0c103001c485d460000341e0f03956a01442c1c0610102c900680000d46200001403c88200a0046007440c05254482d0600d0b44440392441c0c2200d4100d004800304401600381540244220108540c000303c9014240010800005001c4101c1d001525440c089448001034061503020b540601600e6403400c202800051604500d05069000c5e404000511900040071a20072100b00e035010203281c222207403c000500c40319116210140205896055041840510003030241c03190000040c00c0c10340d515541d9540c0e84041040d0350146502103410402c035500e406401c40041e00341d600c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 565459019 1250 565457769 565457801
    0x10b2b0218030d14071214070303020d0606080910180611040f0602060c09010c11040e0d03050109020705030319020705120403060e07030201020c0d02060c0d2f0706031109090a 77
    0x1d4040814400c210460703569851803006801c05950f5591001d5100c900c6c1d000b041002040c500c00031103240390500501c4080d10030740b00182d139601c040310b010003070f00c15030b51000003849500380130440c0600c0d010455885908401200140c0712102e034461043c0b964464a003e018149880001c02030400b20100600c2603400c0f401c1928011666500c0813692150308464100444200f8014991694000d030f04000606100c0c040000038440c0e002e021070200d4044645991a541c071440170890425010300c24103015110240b03066180c400e15407181513613840f02400319404203401c4207400d6204019581900c00d010b0f40003055030040040b429004415801c86c2c0001d41d180d615204403900b2005c0c001075504203caa040e00a000020181c0080066902d00c12006980102c000c11040e03c2c4040180440300901034507031500303080d0f22001c8904130024140700c1080715944150b04801036100d4070020b421421140c091030b000c45c6101e110030903000e040c041c0e02d034071540040ba000c0074040701e50416000300300340d1815591 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 565460269 1250 565459019 565459033
    0x50f01090c08071509150c060504060b1207152f010207020a0b130303080a090c0e040507080a0b061504030206120109051f0e0432070608010b2b021803 66
    0x3050104c0744048041c00c0d001c640440300c1000003004207140802c00d00800c2c10725000c0c0401c9a142c1d10203035071b0b0454046039280d43c2c0d020059610701d4500c00001411035518000d00e844d9007080195a983c10a0442c18003d000031882c00c2e45041a114421035150840800701e41e070885681003c40c0d000c0d41284104911880c4031031710228030404d1000c10303194000456500d14024a195031800d950241d0040c0000014507290003002010840c400b281000506540f00700405c1850581003031800e001e0320303801001c80b5401c82a1380e480070415000f00c0b113404c83e0003183c940b81c10500001201403144101d500c02034000b140401e650841c0245002524100c0d007030144180b01c0f0f46e030782805440e0031131081d5800d046c43d41d042da5010f000c0c80100c040200d50142c8244502d101054011008220358400da55070a01060b000030201208001c0c01d00071070005003201d05104141d94108030030341c451801441d4401201204180c0010503218080d030700b13600a000c01003070456440404448007501c24902c845098044c3c41601 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 565461519 1250 565460269 565460279
    0x305010305010513050a030e061e120f0f0403081302121e0f121308150118021801111501080c0415030c03080f090303040b09190b0a0c050f01090c0807 66
    0x405130710003656018020300020f00307440c0c0c0e00b40c0301202c20420041c3c000c1c01c00c0c040800c085040f0246120003612085e02c00d5140c60701c0d0070005c039490100402100c0d280510205108402d60985031564016900d4200054030b982d6105092185480d0000041e40c001000e92510400070400f01e04041180792004032060f00d1a640058183e07200b07070004200c180395200848070441c002400000e44800035286241c0c1d54440da48010b84c44c0b0301400e2001c10703e40b07000120010800c08000c0c2c0c0c00c1030100c108091081d402d2600c001001094040043d80850501170f20342210a1600010322040044100c6a03000100c1c9507110401d06941c0c91542441e18002da2038a29100740c1511004048411a80d010741e4501030780d825503640c100550010116059400c03024041c00030340380e400348081d0020300312201003e5115940081003003e1412001c0c241da440c810703041010311581c0211000c5800c0c2e1000ca051400720110070707140641c54440c03100c030114803070b510f800101401c100040c800c800440703a13033b0411125055150 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 565462769 1250 565461519 565461541
    0xe01020d05011e0501090b09040b030f010b03101e02070218040b0105030c0d0503030c0a05040f1202011e0e12071e090507020f0601090b010311120405010507050c3a03050103050105 79
    0x603014131408141085020050030111800a224113400600081000c948450200340390841000240c3c0199448100c10416400e0030450301c0e1520070b000b10184011901030380c05691440040281160b2507400150410a40d1074a020540325810368040002e000d140c58141005490006e0003000d04c00d0007409401c071007074500603c8040a40b50044c020b5032460326200803464039a400780c01c1d10350a0280238880040c80952400c42c0400422001004801c5101240b00061034101c0400d01070400d0722030740d15403404542e44000316005101c0300340e0710074003c6844a040240f070034a00d58490910720905000301e01c4c440400c00400b00858000c15014065912020707402c1c0c5e1284c02504030b07580d0660000c801000741d0746294021030228113041c10300107160f804c18001d881103937002c003403c00c000114400c20b002c02c111003481042d600c0703031491411904180ca9071000646501003450811400241c1d0000c9402203044ca940980b43d1010b00c006210480d611214050007814092000390783c02e5203002c0c001510321001c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 565464019 1250 565462769 565462829
    0x1b0629130b09360d08010b0f07060b0105130f14030c09070e040f02030f040203070609152007081c0f0c0b0702010b09010602010608060a02070b16030e01020d0501 71
    0x611621580c2d490b41520755200d0f0940c411480140c2c202c41e1040355100e801000c0c201c00481c8940a40607030034034800c000d80710040c1a444540c030364400304003004120920b01d00341c0d0601688500045081d0340310b0401201c0c1c0e07004100b0300008a289108000400d1362141402808992075606004065600c002c1015103619120b032225820110300300010340c400f407044880c45000b601c028000540030141d401d42d8800c98000300c520407081c05940c030900040d4a4200840001051603140c160500c900b8420052201410021301c142803100f001c08c0001c1e1081301440d0301e81030b020001e0450720103698412041c2d5840c45501d0b01f45044d40d005101900700c0c03621801003022040e2141d00c6d65200000305a9440140c200010a504119507a510b02801e442d42e0302c900380790082c82c00740c0c0003003107a90a00c003c0e5810000082c000a000602c10040d10000965030300900d030b8800f032140c008181c5098010303c00d9018000c00a505810b5510000b468950394401c1d500143c16285580005007039184180301010389070103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 565465269 1250 565464019 565464041
    0x606030105010c06180f03080a09050705040f0b09100f0b04080616170f060307060518100c05011103040b01050102010207020f120f0304030c1706071b062913 69
    0x100800040c41039501500d20030300c8042c4110380020b000850500c10075070402020204032011a4100e030402c041c564021617080d042240b0003010010000c3c00e50b205655040139100d0240a1394a4103020b00c00e142c240e52105080c003c000d41503005a280032503015200e5030032400740340140240c0100c085004040d441c151016103100b02d0080900b912200745a05c003414260301504208144c1c40402d0740400000c020080c00b0707182800700c10302c6a082c001e08050070180160403010400c903081c400d0031301d2854118507004c041d98050f82e04c8202044c44540482d2041c1d0285d001400a6007801d0303c172000341e40c40c5001144103501a004d08800d0741d0700d50004900340d00c5081c00c003a5000c60104456400c40ca0a11750915a20940030210350800a00d1706030f0b01e0450b0829801603440520308202080a20f896016425034008220081c0002b882c0180002d802a44840c01000036401241040c80030401c1d10b91145020480880d0003031003c41c41400d40c2401c000810101500071011a42e6000241005000c0d800b5402 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 565466519 1250 565465269 565465279
    0x1305070b0924030406020d0603060e151302030604022716030b0a030206030415020c12030a0c0905010207090c0504050a0330050f030c0f160b130c0612150803180906 72
    0x1c0ca1384c0d140c1c130010b07410080d00d040d1300f00d40e10b007400000600c05124041d0a441c901001c1e088800d50024014141302d0014483c1c64031411294034100160390101d0b0700ca80c810350440350455404420102900c4040403c60305050604041080c04054103a004c03005440081a541c00e104650b18001804040009031000a41084085c400316000070000c1d0280c2100c101c1401005082c034480300600c80c1f070029640f40c90101e143c4000284102901c150040369900c001e00c0c142004003605e0b0000007995420750b4420250b0441d5141040420340e44100121001407400801d070b0800261682014030030001c1022403450005503c10044402080031040d4007096001506e5650400b443e940c0e20300207e1748000c01010790090100320101038000b0720009450303039070201d82840c80c182d0503a00d8005901c000242009540f2030454246e28009011001c1401c00e46d2080c3c90300316500388001c00702c40f002d4503a0488419880e40301000210341090000050200d070b0221030144007004851000b030000701d00e0203949898200e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 565467625 1106 565466519 565466521
    0x90111040f05010e0d0b0708071803150c02010621081c02070b07021c110114010305061b0903030a031509050a0218030d171305070b092403 61
    0x1140c805d0300c070125a501c0c1611605030030700c402405079082045040000302c00d90312901c0d81c8014031940c0c4160342c602e1621b83c41c00308122600400c0007039a0f9442d1101c40c1140a10501589003114160365050f444002c00c00018140110041d4098422560802030240f01c42c44802603209412081c2100580754070640c078085210703100c00341c002021580025282d4050901c0d1818101a140c0380f810081c2502d00010026800340011b400744030407910b05000000240100410f03401d220b0003e030345508842030083d482e1000a07000743e0800c0d5030140c0c0144880810180658420380703034040403070700440945558900741c1c400d0700c0080711210071154010441880ea01d640000c1c4800038802140a480460701c0364800030446d00801554100c104101c4000c10132152904001070707041600601075030f198584030408103215610030b110f014050f0180482c1406980280d035440805090000700c0a0b07d1 = true := by decide +kernel

theorem cover : BRFrame.Cov 565287769 565467625 := by
  have h0 := BRFrame.cov_init 565287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 565287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 565287769 ≤ n) (h2 : n < 565467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
