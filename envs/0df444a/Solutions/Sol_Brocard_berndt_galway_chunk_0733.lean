-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0733
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:28:26.397493+00:00
-- url     : https://prove2.me/submissions/0161c303-47cf-4fe0-bcd1-62a9921e8825

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 131654676 ≤ n < 131834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 131655926 1250 131654676 131654687
    0x7020a05010603080c0f0304050f06070201050c0a06090b0601053414030705011104060504030b0c0f0c2b1205040c0f1d06040528060b21011401050f130306060308030601 74
    0x6d80c844c1c540c400c0c08184031695448014070300d84101110b10343c3e901c10f0340d440162001d01070b84039012245d0040c0080d450038817a9603040405540e00c6101c1c0110310b40d03541030042d0307120300514552424542001d040e00301e802120002c1d00b800c0000d204201e098a5060741e4030010149100c40d000704a0f5000411144c007009400d015001400504070900e074141420110028000d01443c44003504589680c000318940c1003044017100c4400d00748103000c0b6621502c0c40015036031000904082400001104015480140c0010f5141000d2a06039250718484800b2195a4040c101c00f51040e00c032414115800503030b2168081111000f08040401c800d40518a0701400b5071003a4018420360080b8140b02c00c0100d800c4907408800c024100c41402803882c0c3c0c1966081b90002c0955401c0000c60302c0d0005072900e0165035a003a409900180255010340381e07030722070034400502c11004051501045091207644036214100340074155a0052100701c0810503600c1d155003058a910350b0080e18040030000521a10b0b5078406e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 131657176 1250 131655926 131655943
    0xc0703050f070605030f0f06010918090b0a020a120b1801060906080a14070f021f0b0306010b0909040206071b0902040303020f0606060d0207030521061e010207050907020a05010603080c 81
    0x90900d1390841c504041400d90160005214002d404040c0000032080e81c01182a0009031048005290308001c8031407698004182c00e21060300d106200d40c00050040520f402100e016144079502e080e40c3c1d00c1c0d0811030b103020704000007805500031802e22020a0300d450314600b00f402400c1c199240700f803882c50b06801912212018100c958414188000200740c00a40c07100c0c542c2091543c982444690f000e9202282807155120b045d00d030300300c15070f128401e03401c4464019085030344040b0140c0e9444c1e43d03070301ca6100035803080800080d044020b080001c0e000d440c012016040903405418900e91035440c02c05020414140c54000350303102e680c041410300605034108422860358690340020007583c01c000c00000d440e0301440140e42a8aa0005041407c06100300241c0301250000003d00f003c4074200d0b4540c400ba0350048510394003501080c03008944020103003044026a010603005044424200b8003404010380005000005501c208031000c8002042449420f000354010102d69441c0e00000c1101030800704007 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 131658426 1250 131657176 131657189
    0xe10080d05130308030f2517061315080d020a020306010e04080d02030103050a0c15021e030c0304080c0301110313080304031407051605010908060121050a03111218150c0703050f07 79
    0x101c0c607500c0c40048c2c1007a0124419035200d0018216651614001043d2504060910300441e04010300d048400051a0034076007a02c8038001500c03082d00fa9000c00701d030b4504560300040e51541c4008010080300c540484800d410a008540d210318229201994509a038400e03031049440380e200c28016009d00000701da40a01a1031802e000d60600f0581c484000d683d00b40d401d0b24485030602140c40b00c000c6120800485140212080699444079510402c5944608407118418025420701d15110000000d0400b180d2080c251586101054a0180c4a000c5141c000820840c18015a6890b1284e940d01003005007010912440003000b592409620300c1c280c4034166445541071040c0c050f0244a880c4005c55507c0c19075118116007010381c240c8a0f558001c0352004a40030b000380c000c110f44c25041c507a0107014446d07000c466000700c032010540e10b0b0801c40c0a220b400010001500c0345100300b4294980004002c1300100020b110714102401c132210a81400400c1d4011035066100c002d03030b5000b45100340544001001c6 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 131659676 1250 131658426 131658481
    0xa1b050609010f140409060b070507080105090304060c020316030b04141f020c1509060403020606150403020103200d09030305061023070b07090e10080d05130308030f 73
    0x20000043c001c07080072110f0000340700031504800c0800f0590001e48004100500313003070140035940c10303000c1d0040c0e1100d039003510140240240840e614005000d0180611560030055251500e0010100e60302c02120400f02e0341401010113040c081c1b80c070b03800070102441c09890141d5140c20949402c2c007000200380420360082d040410851007010448a65007801200006c0150781e40710820012410300c1c070b000413610810325640d418800c1071180010305901c1644a07408a500d40c0c1c44110400c540c2d0010380d241c0f015087c400f0401440194400c1d0800303144408102002400420071040440080d00300c0c203000c0e100305644214040a059160242640184040c1c0d1007128042c03005038000d00010240c500c019184454001c5504c055850404503070809412000100c00e5003005500100380840a1080740041810384d40400d0b0041d1686038030404595a6100030007050701c00c4401926140c1105899400448005200101281c04030303004611420b000c4804800320701c0d00202d020340c4090741d02103404403801c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 131660926 1250 131659676 131659687
    0xd0806040e0d020d050f04050301020301060806011b120f050d1a01090e040b1513050a06030606140a030b06010306051f0306170312040809030a11030607140409020703020106080a1b0506 81
    0x680204440444601d61700e4000c0c0e49484a4100a00b144119402140c041d0b00c000000100d085d031000541340503103002d0361003010414841e061a6060181008090030f182c90840c180c0c04060301135040c50940322140c0c00c040c0c0c113000b0081803110880d2030040b0072013241c0c0f0b140c41c0b0800c850b40e44444103c0141c21220300d00300c16418541c035200781c0308000070018610328561348520203480c0e81e80c2e802c4045554182c04103000c54908810200b01030b002500c000c660060801c0b80110300407506804c454681c07403001d8a05a1000c6c42c1d41c840000b03012010f000306051540d2501c0100e803070b84554005c1c160b2400786c1d42c0c1615a13643ea000b0010100c8459500c0101c1140000082905070900802101e1441d9180d00c6814020f880718202480103104240c41660700d8880c3d400700000300420442c081f2107910046041d180641c2c3d902c60706680001044051010258003080203012818682e8040c2c08624020b00c00000c0321602c0d07070800341c94810032040030798040414601d80e140e004030070022034001e403005407203c0d400d14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 131662176 1250 131660926 131660953
    0x4080604060207020d0c0308040807060c0b06040507200a0c090e07060507020328230c120a0b04150c0c08250606090b01080a0603030e09180d0806040e 66
    0x40001030300c0140304a8001034000d00b50b644800307002d440981c1000340e4061659a030f11348045680d105104084c598000c2c2030000034240d000305003000d040c1342c001c805040d40e5034032401080001c000c000c1c03080003408491aa1030352030043c003074080e40480d14540d006140b400400c2c00e056090700d0311a8030504144c0d0411191729009040861400708032695414455207a032a24400641400c82ea00075a03960b41d02500e8030f982118030010815005180035802d511158010b0b85061010442d800c0c40d40c840b150301c5540f1031449400e04281e0a1200e8510b601a180c40c0c0580d41d8460011410958056506000340c1d280703012114198410410010701a040c03d00501070503039541011030082181c0f203070314440140300c14000c035014407252500c0580c1c4044200200d90300c9042040003405140c03140c4d40010180e50010321f4905491040c4001c0d60b4151311601500c0015201700090031a006001002c010b01d03654800e88190b4040090403040e16940d2180c4660386000014402252401001201e95074052044207144 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 131663426 1250 131662176 131662183
    0x906050a1502011107030c0209070e01081b0715060302031b03070311040b10091e05090c070302030706060e010501170f010611010b0303040906090e060907150c0218040b09030408 78
    0x315001411448402032212406a0041220866084c40400c00044007000c03d1b5011001c03101c2a0b1089584050704e440d0314404442030340034000d20702e01044c10400412144042c400303080501581072404d80e8500312090f0b460354500010b8040c4103043c1500da503c28801c61405103e15081c249480c4030900501408000107903854286200c060003008800180030f07a162225040500444c4003d0190301e28000c03200c400408034a503510408855401c40044c08154040703d030076180403201d00501d004441e454580d00f402d0107500404003101944000c02c1a440040d14901544000b483c0c1100c0120066240900240504816030551420310b0306190402c0344a106d03840096056815030f01c0c01d04881f64111880038010940c04140039403512001c10009103130f00d11a00500c082ea041c04030107000c40804011141d9503a40b0a56801a003a0130000003440507241084940f03854050b079181c000141d68aa0700420505803000a41b181028592400c0100380400039200340d401441e102c00030b40c030b041d16142a6a0300c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 131664676 1250 131663426 131663429
    0x5030a030e040c030b030307150606020109020102030d0203101a1218030a0c02010e0301090503040f0602010c02072102040c050d0c0801060f0e04092109050105030f010b090d0b07030c0206010906050a 87
    0x119980d104035510f090b07403180d88030782c1c8009005011a592800d140c2840c540442855440d007400c01c0c14201d02094203031060180080440c1e060700198149910311030844065013004140c52005a0700c4240026000482201c0000490355103141580d1a1411340e14003200e0040100315000708150003405000042000080380c50442c5503182c0620410920320040301d003404001000c59056080004240070300070b02000a004580410920b000b040707940b008284e00381c9548030072000158004040800040314400c0d281281400c07003404449031205c03294001011201c9903203120380050000306100d0b41041d0144108582207500e810515271561500740014800c1141510150807c01c0300c40c524821529a40c110300026940001a241191b0207500c560084000020148000681110380081c15500a00c1124003e01b903841070101e5580c01d01184405903840b1207800d64200800303501c9103000c02c0c10701c0442c0d40500101e90b00031810010a5100030718089060700f0561145140400400c01d41c0d503400c040c40c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 131665926 1250 131664676 131664679
    0x120301180207030918020904150f170109021e01020d030b0603070f02100911010f03110d05180709020327060f040206120124030b1e0f03010f0b090105030a030e 70
    0x41c2e0b0344060345401c840c558029440fa039100e1241d030324044000140398000d050a01c1045e14200000c43c42c40c0d106500c11100c0d40310381c40c0f104540303040034000c0d0003101401507445241e02d8004640300440e80e0116402400780c1401040202d82404007850329079040c81080c0c4074540c149001e00c03182a5400001c0c015200192841e000d024200c500001e07100c1c001d024148508a44074000c001207449800d081fa0900403c0303500e1400901c0600c0400303030086c000c0c4034040b12008a5403949052020400340f510062030050145a1400182500c040c400b030000c03c501e002401d585080036840c0d042200d814503d8040c2803d06110541000300c130400441c10029071300e548036030143d003900b00300c1d01d4a00218140e481048005910341d0381311070012500c4140d91707042d070200225441022006090010040f02215050030105d5844092000d0550019801d212105500c5000611401c144291100040e00f10340414695800701a15100030400c00e10701010344c940140003d8000e0071010000f554000c0c0403820011545 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 131667176 1250 131665926 131665931
    0x30f061f030510030c080109020103060812120402060405030d0915020a030210020304020103020f16050d0503070e010c0501060807060e030705010503013204060306051515041211101112030118 84
    0x10b030780503e41d44201000f5900080e03c091601d8407500424060b1030f00c1c607400d07800f1a080000002c0c0401c4000764240244507110f02203801c01b041c01554841e40c07800a0804d0346e0141051001060790303903040c071202c8100003450b00d8007541185020700c141040280e0400010a542001c1860804070303801084021a440280c8001a0340340d0390b40c40160028003c0c03ca02c4403003410041001300115090400d403441c0a0f0207841160401c1d00403200403109032000b2100c60b0001a00412921500e5000d0f898031012188100c001040254841e140075141040c01c4d480310000a410302005080d03414140a514042d00e42071030103914542c105189400340e1800d9580c02c0f0204869604c2d202115a1011101c1c05202e000910034014550b6031f04094029041c280d4004200038000040189107240140461071a9003401640b10300f0a03140000454880f940e2010030340d0420004003202000396036030161141c2c0c0c0030282d11003d81c0c141ea1504c1007498542c05207011011070808000510002c5861449801ba1031b020701c202 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 131668426 1250 131667176 131667181
    0x615060a08060a0b070302030a08010906180b01030b030f0d1404150507050709110d1b0f12020409050f19021303020609131d0c01050405060307110a051002030f061f0305 74
    0x1140c000f48041d88800a0180045044806c040c0d0102c014044151281d403004801c3e6202c0c28210200c414603c00c03500d440442045c010840000c1d500160542e04c014180002c2d2501080e0100b0700300300745000b1410040d045114900111034020303060410100d050b81003641000d00f4488a0b4001e480481e01e080180040898108100b010400a48001d041c80241c00d00800c0364a40381c0342d240360003480708803902c9410036010031292061103c52011030710150391103114541341580280c039158401c2201c40d00c102c0d001c01000c2a8200301d409040e01850072544462240e1400601040000c0004440000d83c40e004010303990307404213100089000e980e012241c403583e5a072850001800c406126005110f22420091402c4514928480710480703a0302d0001074802d8010481e00440d0244564012190310950074004510583d20602d01d202854120b0802c0b12060000d40d2543c600e440800701114002d5a0004200544920a00000c64105000b91603c2c0f41d2240c00c84c1c1c1307032030040328100c102404250b5503600 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 131669676 1250 131668426 131668429
    0x10e1e040f021201030236010603060603150501181706010303031d0a0215071407060908070602060f130506010b091311030a11130803070209010b07020a0b0901141b0615060a0806 78
    0x880da240381f02c6084200c8481414403100c1540b4613400d01c56070300170070b00e401400100d183c064040c0c000c10400c4448106419428403005460202080040c6120400721800104140310b04050303c0e821403000b04020300f40e070340c51842c008003900c8010705607040f40418100001d40c4000b000039140c1805504a694101204103601916028001d00c0d001600c42c0c08828030300701c4d403580041a10420745000c1e03074602d22525291800c11f9558260b510520006034084000285d00d100140c06d03068000b07904841c80c01342084280c80b41440c12100303821071041c1c1c1c000001e1944151801c5000446000020a03082c04042070900c210300c00c902000f01520300311038454130340d101d400303406000f250108550b2544d440b5a60b41c84004007aa242c000c42000c0780507050020021640804900554a580394000d1040f0040d50804490b80302c0f07600702c224003c2c1401504462240e5550154002c0e04080b01080c0401c0407039482e00c02610714110010f4000704c003940300007981c4102c54440c04200e030076040302d504011407545c59000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 131670926 1250 131669676 131669719
    0x806070e060d0f11210109050108030904050a0212040503130f210203010608060106090302130b101b0503030a2307050d0c1b050d0f05030108100b010e1e040f0212010302 74
    0x14894035513200006102810100c032400062113120810a802d41e5a81c1c03641079510460b02c2c207028040c142e41c014403613a0380c030b860503801065021103070400c0541072600e40c030403049500030140d8044410b50008103092504030307240c07150400206240f40d402c2c05843d152a410000c4c0070189150280b072000110f004805545003500018010700162045540355a511140100440c0f082d00049102d01c1d1102c44144a0781c41c58051aa44440010300702000c3c1040c1c4007080d0f600d0391420f6074903804015412a90004590140007440c402d040da50004214003102104040d01000c000200400642600040c0282d0f00e03840020384104800d00d40d40092940e58115054070110070f0980401e100c036000e002c50504000c2c0104001d4400a500d03140d40071052803424055503940000d0040d4030301544081c03905040301d20542c0050f110307101c060510820f085122808a01c88900b8141c0c81c001030b6605030000e0f9143d041c107100c0c010041039034580450610301d000140410500042c031010344a0000010605401030058 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 131672176 1250 131670926 131670941
    0x110406120b0310020a030f0608060705131809020f01020a0c0918050f0307110a03080306061b0307031e0905010806040506060f0304060b010e011704140c0a080102040806070e060d0f 79
    0x2400c990b0b801c0000f40341d52000e54450b901450000703040409890040505000700019103400d5409010079075210300048520350410394110080c0e0282c3c140000d004110021600348a01c10303a00c001c903500c42c140c0148198090341c1c0081e076046500c12809c010104900103400c001b503442082c80400e011903001cac2480f01d0381c00c0784000504079011360307800c100c402c2d20300000500030603201e01c0c00d14840842d5039041002c403220303a200241c41c001d000c000281c000d103807c4005201e842c400003201020000e2820303025143d41c006400407404a0301c0d0301c41c000050b000440030301c40c510440d864403003450703810500004c1000c000504894000c0f034962022401565514058803642009002841d88030314250030507002510a00040314041341c43c1c0040001e40c0d5201e00b5201d58070b80800a82c07040070381c56654507051400603403a000400360141120080381c41d902c034084075008101450000d030f299810032500d14102000034020206000d424540300312031392121010780e000c903072303c030100000d1440002d0388078400741034078 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 131673426 1250 131672176 131672179
    0x906080708180f07090b04050f0a020a1b08091207060c060207020310151415030c090a0b0c0a0c08070303020706050c07090504060504030f030b0108061e090a0b090a110406120b 77
    0xc1c00403c0142d4140010000304131600a5014004408254284011100244e4140d60000d032414001240da04141d0000c190040c4503140460740070481e00f40350350428021100481d000800042c0d04045480c200c00c180c0f0340a100480502045d41c6494000b6049400714900104082d03004100d0f001990f034140f01070812019401c0c010301042089240300d07903808044e8021049064895241000c0705c2c1805514008041600b03880725140d034803843c0c81290190489066264070003091480400c41e0b66100020780030030320442000b030079040054600016071500b641c0200d106170b442001c0c1000440d500245174070890b60070f410055555803032035031118100b000c65008074503214246001c0c40f0412600382d101e00d200313900036980c0d040c52000d41c00c02202504c09003124580040d48003400300301d962030300c90f1841c0b080150304c540b544c0003007100c9004528a40c104a610b5882c00e65250401c000710304000c59800e60081070b1410810810b036080e04032031407601079802810108004104035203605985a4400c40381d5000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 131674676 1250 131673426 131673433
    0x4090606080106090b1801120e0a1b080604080d05092803080705090a030b0a09020d050105040b0c07031e210507020c010306180b150c0f0d090608070818 67
    0x3290301024114040a100b0403001422203000020b0300040741c0d0940c2c016080356810038078040d014100454039200b2088481d140180d585207155000324041000396038851040010607008003a100c1c4445018203954000ca00a810100402002943c01c2c4129044050000b00000d41c07910750422151401d088803280610820b400350b0000e01c0010300000c0c802d01c0c14030944d40c85000e5a01c030340040340c480c01240300c800c4d080b031206a01030002902010116034400d802e110b00040e01c4100c0c1d000982000e80c01c11048d66039944d220184030902c204415195444090000701520704000e50740c0c000c0104001c04000390756481070306940352513070b40b03d08504400b100707031402e000e80f880640c240810010101a10060702501c1a429a550903500a02405085451181c900804202680d00c054050809040d100c0c0d408800a000c90501301c0758cc8000c1d024040e0740c90b005098922810003107500d000201d80f00c0300c0900000342070070482140c0c420141c680c413541c2032800e818507854900b68101a0701514039001c22a00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 131675926 1250 131674676 131674679
    0xe0f0708030306130b0f0f03010f0204170609010204060503040b100308030109020d05011403030d0504060213080a06060605070b010521030f0c06011d0408030c04031b05010f020714010c0503040906 86
    0x5030300201642c0607030811594424541103500d41c0b0000c0711180b00c20b0680100241031010313031a11b00743d4080e0060900181c0049501c5540c3d5854130100d1340541c1152102c488410b41080b1030b84420420154000010b0000314541800d10f00042e0444c080100000c0c040461040050001d0540c000000e00840d4460364454695031180c03011400b0f508820880c2e55203502c0d18000085641c40c0d0054244900703800f43c09903203098400300682018100c010001c5d03c00d241c0030044d445400301509510300050080c880a400300c590036181074016180720746c0c400340c20004203100c1c000c00719144459690440d08200c2e1128070440010445401d101c4040e441c50320203001c003299218006031032030010040440c1120030769203280e8aa25070341580c2c0f003441c03032242c00759100a400103000407044070003590010807009680c0c1c00c00d0b41d00d640e003550f601043e0b498181170308074a94ac01c010340d50b040840200780340030600180192a00b001e2500100c440490741003410440c40c0c68004040c00b0b000d0007101d020300840c0c0e60911095 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 131677176 1250 131675926 131675939
    0x30a061508090115050a060f140a030c0206010806040c0b0a0c1b0f05030307081e19020102190809100b040207080301080115060f3002030a0501050109050301090b01090e0f07 76
    0x5000495640d0525400c002100340c1101300c41c00f0080503600c0040c9058a202c2c28448100d50100115150009004a2020000e5070182000281001c104603a03008140744a01e840028142001a8011032195108000307000025014804c104142c03008545215251241040c0440d021850391300f002d8581c00f00700b200340d4400c01c2ca4407907980035194046140040c0e0b50796002415076922500c0c0c00681a45401d000d200d42c0700f00d448078180c03826044802124102003d004492100d0381100b100c107000740c0e5002907420509462650098191901410702803c14581140300c0c5841e540c01e0707200098007964a80b1070300c5140c0c1d41c07035054500d516009086503445e0340e100d02e1010700030810501e540080c40c9400b0300001e070980c0302c1c102030142c408a1703a417041c0c600e1a59140c1c4650030030511081da20032500324800114018030303510140d4819aa054000f180c55403501c00054142c44d403642200b8002d03410709401a002c640303032403c03480c1143c441d8440042c03042c40d0400144c3c24268000c0242d52a8000c81c2000030b0078 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 131678426 1250 131677176 131677187
    0xf031302040501050607050c1201060308031006031d3007080c0f120703030510050603160905040b03030a0c0c080a0f110415050d030201110a090314010c14030a0615 72
    0x11a882078400b00116600c030410442c1c58040c00c44001c04a03403102c501c645803410030b0200c9408081c6510b001054040d16a5100c59132038104030707002e49401d02032a10030030180754940554030b6810154a95840d41c50030000f120360711002404030401107080c141d0150b80103890351000300121a180724040c25100c0c00d003481c00e505a60b210044000c164401c012074004400d001044001644040b0641d60345000030310f5070240c01600c00240003400d509840e032400689915018000c5101c0c90411101c481c0750200301d20060146e090b66002240038074602450001591000400c64143d01d845040030780034a0020300d08806041e80c0c5403c4403a040c00341913608010044d454241c3ca4541c1d01c61080c3d02580c00f40d8600780000c5032040246900054181c0108000905212442e001c0c624041d10011503844d207400c20b825265440041060000b0303100e0704082060041c200c50040010b003022009002c14080404000c0c1040101480a0313010140040440c64010641d07106e0002030104401c040040f8000d0b407400f825 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 131679676 1250 131678426 131678461
    0xc0f060c0406020f0c06031803040302150403050616050a0e0409020301020403050102040501080a0504020307030b09011506020c0f0904050705220e0706030e0c03100c02190507060314010803031b0f03 87
    0xd8454804c207500f1446010a4542419502030105400c40d511080d4030244825843d140503450300040002001580302e14441d00c03a62034000d4402c9940d44c0c03a42c9012271801c140107141040351200e04c0600c0107142d41c403104648000d203407132401041001c0400c00040042c90700300340080d455817001400104002041d0013034002c48100740c9981440d6628110050251130b404c49000f1751681000c041070000910b06d03520a6003001804000107010042c20342540c032030614a030049005079105196041d5076182a540789881c00f001500c00ba02c190500e0707030781c59583d0400c0d4003407107100b8610701501050072206080120b07400303d5a01028042c0f0240c0f82d4000781c64aa05004000c0081d04207080141c0b0307401c0000b210882010040c0082c807041503486d0f0f58000900c080601c0808500a041c0c2d2071a0800d84240c10042c03240c000c0002d04845440c1020240c02c580d003c180300c55042001c10f0040007034450100a680e84180f80341d15600c1c0c9030b12540c088410610604410144401c80030007404030301d0381183c5d007007034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 131680926 1250 131679676 131679689
    0x6060303020715050f21040b0103291503160303030522020d020d1502040806090607080912030705070b1503120414120a1a04050106050406030213020c0f060c04 70
    0x440183c2c40c1d0458841d4000034048820110740104601012044010014284e030190748854086924068519203200c0d0002d075000d607003040300704c0014020f101680904e41c003d5102e0a81006003401085107100c030000000f0700081442c1245406407243d61000e0010f503807240609510410060780340c1c54090001c2c8015510003400b1561061150740025004000340003170b0390002c04544201c0e00c1d0b6420048103000d0003000302d951500700c1488110351a40350001e000a016004054001c615208900302e107840b00c01850182040844010712031032807801308080b440310012136000d603943d50341d40ea070994082c400d802c401019080706600300300840841d80881c0741b40307080072810346d5100790b200f400000e0a40120701402d81018103011501d01289841e4646050b0100c800c0203031407100701243c50b1502c844086085909a4491207010441040300030712911015200031207041000c03505540100da0b4440140200684036507000850240d002030030000b2420305120f6030120303512850036900809a5422510416 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 131682176 1250 131680926 131680933
    0x130f110304031e0c170a0c05070b070b06060304020d031b12031a090108100b030c0301020a0c0312020c060606070201031404052409061b040f06170105010816030b010905030a0606030302 81
    0x12a40791041341c182d40300c5508441901041e0481c00780004160384094845000d00000c04280030003e84140000001007404407010307a02c40d140f5051881100c20010714103407140004000700320059440c161054503040d050f00c3c0000010145079500e5812030740c0f00384080e000901640d071070148564140c200140070144078060700c194800c440c1c1401403400c0c1c03c2c000c541e42600700e114010302103d0154044c1a00d20401401c65104010040110b070883e40071007080c0700084c0d1994541000d2582000c48440c7c00c4009000442c90501c060002c1910348001800d400e10a07240001c00d4015a031103500300504544000c500d0740d10318101403518665030b020a4a651242152803080310a04c0340c4500c049500c1820110098001c9941c9e10180302c02d0350686030a18040300300240408640000026600c0c00175226640703446a594526640004160300140c2c0458100851001007007413201030b8254207031250405040105129560700016543c001c5a504500d416100700e4040b502030203410b400000443e8004e07020b4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 131683426 1250 131682176 131682227
    0x50307061a01020a0b1b04080c120a0510050703020405100e0301150f0302060c01021e04230607021332060a0e0f04030318051c0e130f11030403 63
    0x800c10701007100701640d026070084540300011600620b801680b12078600319400c042c2e10980c40c0e24003260080d4201070304036400f111040009041950500460070581001000c68400650701d49994288a03010348441949420102c4c040502070303015078016141c000c2064244040b40c10000741041104900503103c0d6007040ea1082c00407180c441d510059400c03800540c3c48071030a6400384030b0035a004019400e0340d0b41d805c101c04400d000d911000c0c2d07801140300c004a5551a840d0030304103c41094030090f140e501c401001510f40082c1d403003000300c800d22541681ca030540526000c1e4254014480040030b014502c4018003d00400c4801d282205003641880b01c1102d0180c5400c420701003200c070280191860709450601140525001d90009a41310b44640740c041100c0442c01c803002200703105028112039036032065000101d040400c0c64107207020103044c900406040328860002d0747c0204103071a0441403d40d5448500158289500030240c045d00001480b66a03040514000b03240030310b0b844a013400b0212a041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 131684676 1250 131683426 131683451
    0xb0303040b0a0e0a230621010e04140615130b0603070306031707030906080c070f240b011202090406030c120507060206040f0303230c03150411040306090206070c0305030706 76
    0x213041042c20204061010400d46a41449030311303400302d00d1300c424000001e48421a01c1010b107e0700c41c041e0400841e00c80720343c14503240041c511000b0424400150b04004c0c100200702044034070301c401540d011120098001e541280840051160070b41c19604007400100f0806100d41540201d42101d00c180724581502d84c4001d030100c180e0080d00c40090001d90b40100c1003180750301c01e0640d690002080e61000b841d14605503034401c181c000c03040e01128420354411071500801c8500442042f01c1c42c01107814842d000a280008203000c4010881c901400e9000c19503146d10384507075100401031070344540b13103941c0340e82c0b01d80c600a100c0c0c07600b1008442c40c1c41101f9010814030310109245018941c80844401d645a0941d4141d001e0550340c1804070110303001181c25202001c501850034044c2008104255486c2000703082e45003a54580c124150003075081c80c520b071082c684087c04441c11690007010000c0c034500140700103003070340c03040c0200503102c100c00141c04024050040003c201e2588164401c0065842c0e155 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 131685926 1250 131684676 131684699
    0x20f0f040f1a01090f050402030c22031109090a0308191113060f0509041e1404050705030c0901030f050708030711040501060e1f02100c0507050c03060115030b0303040b0a0e0a 77
    0x14100004013282c1c0700b0486c50a241e0095500030304500e1108e0b00302003441c3d50079000307004111f58049550318541030400070312805c54080750554000741d610b071045180026259039241002480101000600360000f14800300d181c402c498003074400c9909000c981c83c2200c064000d0780100308030b100720a81c03101d000516180243d00d5640d00c010b030754941d542071131810401c0100400369084101015411070701c003040c95213105d01c1001c0b0040c80c0905030040c0c81c2007a0510524100c4541c001e82e000c0c1d40b0401c4000300954904003c941102c0c2d110034a031a65000a140c05800d04005030f00002c0f00c0d00c004109041000001803605004401c103490170006680d070744000715400040261441d41150144201940302c1d0090322403241d280300580112a014104501c030740c0c084403c6044d9560000340c0104110b010080203005812450008800521095041400940340850741100b074030140350b601e00000340c05407414802c1d10300414150741110744440020344050480014a98107903c00c0c501c0810215594816a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 131687176 1250 131685926 131685929
    0x40507080a0f0b0a031a0c090d02090a06080111070b070305070503070507020d0c0b07050c0603041101110f070e09060f07021e01140112021005030c0304020f0f040f1a0109 75
    0x26640c4551944481110100400c0400c1d00106100e403200d018150035110402a50000c2d4443d0601d03600340c81500b05034580d0703c40041c241585540e4100407503445956034004c400021a011180c40409403a11049400240443c0c8e0020100d542046006410326070b070b0001402c07446000c1c0d2021901c0e5610038004904442c170490f802c0e404643e0030300100c0c140920500281c00344602c050040d004144840d1038940030800341d40d102c842081c90001c2d100c0d040207000d10418070070035401e9922905509003943c1d0008614440071030a4108007403801040ba41400410203140d580e1422010b54a00d45e44a03086414400000c507040c00c102d10403a030125960890112440e8400d1020381d000d00205a030010b0b030459094118141b50040d592196400000070040201142c020031a50440b010350174120b106101c8541c0e841801d0300d09019091007004424001c81d41100d520590441d8000c0c44643c5110014203140e0300b50181c0340d0400e1500b1a403046070704880d8800920540c44008000c4c0d0b07a1100c2c001162a1b119a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 131688426 1250 131687176 131687191
    0x21b07030c0312080f130303020c100c1101020705100e070b07080901082a130e01090c030509070315110712080718120809060f070c0303030b010c0503160503190201060509060405 78
    0x80c4d00000704256041502c10501b14401c0c5009860030035a041024982140c1e643c000c05405c0e62400c0c003520711074121010942c1940071500030350910300c458855a480340f05404034405040c0d01c403000600314070028030903240908580313200383c2e4540d10701e41403525041d003200c80d81c540814005030104a10b03049000c0c1159100b841132101c2809181e40d0b9071826155003110144502c50982c81902264103420700203194041c3c0705424001510a100303403001016500041c240c0c0e500d9400111050000c2807041c6030200081d9a4140301080000600040300840e100c0c054000e05208030310104006040e90210329a80200504da0300c0408008801100f400c0c41d03803461090491030244d240030000000e0243c00580f80c0c8030002409203080c410300040581040d4008441100c00545c010014000c240d014850020580d0003840d02d11086415503940954a1040c00180359502c4c40031084442000310400488445070359803840040d0389101010b0180c00b8081d14080c0c04d105400440010f20f1070f0810b4812644039550 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 131689676 1250 131688426 131688451
    0x403052709061306120807060f0c141608030411090c0306010215040f0218010611060106090b07020d0227060405100611070806070918060803030604021b07030c031208 73
    0x40c1c0b501004400501210182d4000d610742d000016400c1400000000700c500170400d8642d6681c4610f002011030f4410a0f221901038175000315109170640c46444031400e131441d982c0140d81c4c0d03040c04085c50a080300180c80100b407440000108010000a810400c4040c0310949101c3c03601e440303020302403c05003c00c590040c0140e124081e006071240a001181d030300b15000da0903805804c8883c4d0003181c1050410145600070b200d0060041141950000c200402a04441c024103d59410483c0042c250101d6100d2040d40e070300007080540566444040c040c10065006210742c4580c0303030000e06c900d40c1500c4088400800250100011618107081c000c00307210303140400300b1010460074480c0541e14550540320507000c44c82400404169240d08001103030154150b9151000300d80c1c0340081354100284000750416203181003000800140c07000000b6250080c02c112000b580790704080711070400044030262034100074810180c00205100540f003d0f04c080d03a02840c0001c0e000c001da0901030301c1b102401c1c0c40d03c080010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 131690926 1250 131689676 131689681
    0x1403060607020a0302130e0607140f1c0504050708070b07080f0a0207030b070e1c02010f0f1101021b010c050c0604062703080702210405060a0c0b0403052709 69
    0x6000d40003048994801030a50040c26102d401040382c510b5004071000000740d50f03034000c4078008400c0103890380c002014602801444094001c041003030003860814a06d4040c04601007018a07080000e10380c29180e0000100614036084c206180e94840c03611a42500733016041001c03c600c03661008643d00e00b900490310524040c0c0e1169451119417000d1580c40440c020420040005075042440c13600544182d075810b00c42c40228030400c03175a011120440c0307240345880444040140d070803503945242e601c101d00740040d900101c04010b55030005880c051180b9035100040c51032081c00031520211070403045078020003c00c03c061805441507c900d45a0802c01e0340b103040010002282c94000c1d138100602c60300d2003403503445107100603040e01c0e2441800301c0c0440c2c0e007101007103015541041151103010005002c01c155420b01185d0172040e10039405124041e0500040d111600c500440c204040b10340d00505440a80c40d2601303004050341c0081c02d4000c801041c2c0c82c0b0041d086021ba500000d05140b00070100344aa4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 131692176 1250 131690926 131690929
    0x20f07080a0201110d02040f061e030509010e0706110105010902160f0606350d0906080402061b030c06010b04030308010e0411030304060e1305130b0703020c1b0f01140306 75
    0x64001e820828115921412541c2d441c0f154400035200c440f9110304050f0b1111304014070b4600c1c25020b03400c014104040030412a104201c0c02082c806488468180021251919003029026103041019507049206901d00018030310b61040c040c0c40210402e400820030341e40c8501c10001a8400d11070b50151143d240e241c00c00200700c0d55400c0c91400d921450303001926a680d5070283e81c6951003601001c0002c44400d0041411045034034410310000c001e13202038134151031082070140103120743e40665010006d0600c002021901d85c1d0b411107001c0034a4480d8416160010700b012903407548582c0101c107490051500008040b6010b0040d9029241d02d5110486240c2c00d10f80c0e2507240c1035004100340e5110311090140f5003175840a00c010005019207541c0c2185003607104040c440c882ca42000c440ca855807601c030800400e01c0d1152180500d03035a1100c411f40c01901c80c0c002c120080c4c0a005013003044c034065000f203e10301c825102d1013211001002d0b518013007503900070001510001c03030710010359810380e40c10000a183c6 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 131693426 1250 131692176 131692193
    0x51506040611070e2401020604031b140a06060503070b0301050112020307051e0c010614060304030c0510021314030a0b0610030f06080303040b061219030e0409110a0801020f07 77
    0x203030b5244004a60390180d40b51111101914260b41c484c00244803101c400403446208448804910b1084c0020705050900d40e4008010541d1298074070403d125481d03022040061000800550407040d8046603400b21550500740020700030342c8900e5200348102c000002d050341001c01a079040307074170503102c00e6003510000318008080d5200800700c20410504010020303240046410482201e00510641c2da1903650003602c990840740c06030410f01580000e41d880003100c1d036500d011260f000c1c1e4540b414014010352441e000d85880314a014411280c0d001098841c0e0240c0b9003a4008103c400c0081e0501040b52030b40d05050301c072522401e014160b0745450300013800358201400e00641101c820301e400111801060400c20855500c0c2d04800300c250000000d00c428040a5005590402c3d0100d80c40c0404020720815a0b17612100c1965a448010400240d6028180240c5410144a9000d803061002450614000c15080c4007081c0440c03159808010101d000700052082e6000c4011000c21b0302d181c00030310f4543c2c1e203d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 131694676 1250 131693426 131693447
    0x30b070e01030b120a0c08012007020a170c0306061f08060604090e07140a121e0c06030903080f060d030503060604080f06011406090d0f020409060203190515060406 72
    0x505403601906542526400d0780c551130051588040c0040c20140c1c41e00401502c003903842419680e0403c0c0804006807600c01d0580c410307a06074014140d0380c0c003692001c221117031099032110911085078016020209070110342c440039454100c007560034a50300c003420002101c0700303100c0303042c0c40c0d00c0003e5620f5038445c0601e09040c0c004800810150600f40d462940300d05540704080340200c02d8110000403c030140e01150b0401501008980402041e0309200c0d02d041c80f20007844000d8807040040e444c0c1e04046454030003540f00720741c0203a8000380d000d485141c050050400c011088001401d40340000703410070700c1142d65a005920051900902d415191400c50396600040c00d1192300800400001415850030800e8100512200d009020190300d022610a000002100c0d41e600440040011a1036075551404105c641540b240504440c0601400460010903003000c000b07110314400002c0c40070404005045950705404103c091003103035100200074110b0b02c9210340d03154000000740700601000f40140744a49 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 131695926 1250 131694676 131694679
    0x8070f091b09122d0c0e13080d0204080706031406040506030706050f09130b030d050a05040501030c051c05010f05040905030906220f0501030c050309070612140a051e01030b070e 78
    0x2030408401580c03081003004050740e155008080d10240c207082003070514110300101a0400f50a001f440c3c4060081d1b100403000900520b514000a05220200d581c0c0c0e0503070303002e488044222084551900c10150042c015041070807003030b1180320002000b82c9003074040c1c58401e040240c040d1408a1404400f503070290411401c0800c20402030082341e03281e890b6130701c4107903c0d010408400b04881480d00309041c14500341444076001c004040054841c0a034105048908030780e003c0ca40000d812070b03612800c50349406a00442d081c1c090000b005842e0000d80e5802c0719058916560400400668500410044910440b17008100e80c00c00e0080906030714214002e407160f544482c503c050728180d100440f54040010303130058121101c01590500180d685441208120221410040e14509107049125665801c1d4440d10301001400e83c9080391511440e000b0404030b61080c965174205c1d042602d00400645802c9480300c2c14066640000c2030300c108045c1c5070b070303048076080305500829480700c95080719440000ea00703c9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 131697176 1250 131695926 131695943
    0xb01120f05071407030e0f150d05150301090203071a04050603010b0a0210020922020d060803040302040c020c0105070609020609060c01050a05091b061308070f091b0912 74
    0x102101215004008118403008000203107842e00c5031024144040d560303940e403080003082c040c00d800030f80c004e2050015040e0450b5810b110300b609000081341e407142c4070003110b8405004121a020200c09c0d4100c0b0703024020805410300c2505080051600702d0350181310203907241e403101c1010000034403103005034010303840509803d42c6860740301c801040c420b40c400c0c0d1101c00c035480002060b0a0590307041c011a030080704204000d43c9440c0f01c180c002580e0003171107810000c5079001c8600604000f0942d42c121000c0c05014001030000550741c9000035181e401c144800d0340158101044014014404200c505801c070050f119103040100c25100c6000500205204a8001804005021060351824058203007264544000316a0303240c04080a41a10780207450b0010a6218580004101001600a0510040564060703449900480066075a007040354000303071040c098904042043c06c0200001d100b0740c0c007141c000340000003204004c0714006400351280c20004841090030b104000c0c68040e4440810300032000d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 131698426 1250 131697176 131697197
    0x20a11030f01290604030804030204020a030f0c030b0114070c12140a2d0803011a0405041503052109012111040f09090803070c031107180501140a090b01 67
    0xd079084500c4241038104901010540703444030425100c0141c0956030a80703810341070615694034090b403409030303000080c407464001c20a4410507204e64003c0901041c01d20041c071081d1403070140500182200062280081c0468809a0165a4842c11100115880344104241070f1514040e160310188000301106c6409107461840b9900c402085030301091380c003481100401c0d220140c4051880103004408084811180c1802004540f82c0d10541e8112003199030160900c18201c070480001d40708940180303600034940321180c0d424505400204055a1049086807000044d5a45070104a002c2007140f00c12f8100030006070f4500e52040d480f240b0030312901e0b0107901c1c030300080d00811000c0d101c4950304a4003030600414104004103105140740010040c09400300444800f544810106100081400060000d000c580c0820944a1490403c400c0c0001040d1003065482c0c10a0010040c0c036000a5800c0038140400405c1c8005010803981494100425034000f041c500081000580414030b880d41c14050080349 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 131699676 1250 131698426 131698453
    0x109030501020d06060906030b0904060510050301020c0a02030c03060f1501030f0509010b010906050903101104080613060c080c03040b040602130b07060627020c010b060a02030714030307020a1103 86
    0x30700f40182c0716000110301181401d200030f02d50b40307141d07202d034080508088007080700b0380340c0580725600690003a00c0031a0544c0c03680680141100a54440d81c0c0640c40002e40540900010907100c2c1d00d60b1084042d103000035030316410146e0310803045c0d40d21a054051440480ca5900624080a07403140049c1400704120510310a0796049030f20807120300f40165101c4580120a41c5d215010001510302820814102041d403000700750b8a100d00d2203035142c1c60b541c0b4159040074101043c01d44000303040c18011036080d4504500c00744500418068102c80c200d0800034845019402038440a12035074808200d1400e507600d940b52440140300c060f20581c0c03940d03170070008a03400c20000c0c58244080c02c180c1c154140d903203ca5140c100200c1c2c00903402081c4210020403403040c86440c1c6002c00e0007400c3c003c0340c0961103030040e40002d401841c4034403600b58001400660b084000b6008005030101c18081d1210000d84982003003241c3d1603200886242c0d00580145c03008100191042095503d076000190071901c01511100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 131700926 1250 131699676 131699681
    0x4050c040203040609050c0109080304090908040504090c06090b0304020d030c060f051303021b010806060d0204080105070e1906020c1207050607080717040515030c0904060e061002010504021e0109030501 89
    0x80f01a1a01a21038007400203000c820040500c030203500386003001c1e010f8036000119403a40180d0080c6c0301400d854010030020b0107410002e5401600f8000c1c000c00494500385081e184003c8140f180e0030100f2018140050218111300c01d50740f1564002d440140341e02826030381110404103441003229255540c150010550045106151050107955180110f200c1ca5050180c5401d01f002a01e101c04074048031948140d0740d0202d40a904240156580c5856041035100d2001078007803a00045a55031070002000710259100080703141c0d030582501c01e20305101403440e025045040c079000da040541e0100c0c0b540700381810500f203071102c42d2099200703076108180c690001070920390081130161010b0b100031550f102400080b020710541080030192851902e8504000b2494003007000788481440c1101000080b26100048210341c0455001441048210746901002c4000b8000ba520310b801240f003548a00301142c01481034a0007190002c040f503805908851142d0441090010114104503441c800007002034802d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 131702176 1250 131700926 131700931
    0x606020606040e031602010507051f0f0e030304170309010216050c030d1706060331030e01032304061409030403060b0117160201110f03100501111504050c040203 71
    0x15405800c4908144040005a50b0b951084040d90b80042041e610b92210b01480303211030076030a09000f902c0701002c3c00c10500f0084401c08480103042065509261000c2c02e6020101c4903984070ba0410030b056002820b02d0b82c0303000c1210002d100e00700401c5c05003c05d0742d117400034642c0010610009854890860500c0c6030182ca01c1c0c4084035198084c0d0700000d410314040c1305000c00501607241144890907000290303c19110080d20550040302c00102280c1e00c4040b020010204500d04054003903086020385540c6040c2e0003084054000441446c07000d00158464011281d07000c00405401134004854240c5080006014201b2030f6840e80d10122940075078044e2070300c940714080b8400555112031850a0210594890000b050b040000048440c030300011841c900c0b9410101c04a00388605d11107218007030b40100500c6801c00c0b8607820109500502c1c0b404540294402d00504021440d00c0ba0741381c0041d00c5c03160180010961681050f44034803141e000e09180183d01901070780844000101480105e4103c1c3c0c4203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 131703426 1250 131702176 131702189
    0x61701020909060301050709090b060712020303041502030105101404270b010915050a0e090903130911121b070b060414040804170a0215190309020d060c050d06 70
    0x10404907042d10b000c04545a0012080d0000d009034a091400244208403034007500c1440d9030740306136483e901e480e484c090b01c00d49980240b00b84842401d40700081d640b900115811541c00d179500e0401064a80e0764000d807412a400a4401814000d0f100002d0714404d283c0029000c1d030440c03e10000411a00700300f00d02d090346a000c0e50703507100070700c803850300e407083c0d03000c0c404c010781840941002040b0b003100c45020003090301000d20301281c5a00180d03104503880740031482201d42c04501d50050180c0020048010f00060102c2c042c0200708582e20031307400c02901c089116510010509000c0034100c06045101650b02640c401c2d07110807100881100d58400e5048003100783c814140100401060f0b041a22620071184c41d01c9030803055900d425903560400e4400c50084c1024120b4485011141e13003030030018080ea80364014a244005085082141069040718002200d410a070700701c105d401b06c4c024030501e0622038000e400790b92411244d4841c4400b508843c0620010130a08103d840380d2501c652007650040d016 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 131704676 1250 131703426 131703431
    0x30a170307020f06010501050a0c050309040507050904140921040e07020c100c0c050f040e010207060c02060c1201140d02040e0a020406090b0a0510030b06030906010302030709050c180301061701 85
    0x1e16120003403500b03c00450102d0a81d022500510803681c011040d102c20013403503d40f04500740740a113002401d5000301080d180e000b6041005001110703401c0005000310481c151404c00c820084500c2c000c600143c1900c2940b815000031020710347c0a01c0304100e00c2100d11865419038a800d1740ca55071080d212000f00c920600507005a0420201460840440c0004000c03910b05500440416140d49401901a1180d50311480101124041585440d04010152402c0200071501e44000b41040300242c1055030340d100060090500095203e00544151404100c00c140b07000c03256800c10055149900742c55000030350014505441000694840c0104043c03a02d0000c06019038420520501003503070002d40103444130758144108541507484d0700f41294211401101c00d61120100c0c01c0303083c0d00070810f01285c950007030800000c00c0700034040002c580381200e1090b0125580da0b656400000c00b141c50035140303040340341c8042007a4050800301c10162940300000900000304d031540e84403000c540c0c480301c1c490840940d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 131705926 1250 131704676 131704681
    0xd05220309032003030901030e07080d050d06060203041214011b0f0210051303080408040306090c0e010b030f06040b19060923030601180609020406030b03010c0c02010815030a1703 79
    0x21a18100050010420041900415a10f001a4503401020207450425685401e41c00b02d0003410040e504c01000c140c41502d85580c84840010002e07406640c0e10344000e800c0000014a2603c00000c03602201d09940c499a4101042d94940c1c41c0c2c181a20303510106507403142880d480c04200c110321094428140d03114401402c2c07001030041e043c082c4401c01070074440c0c0b401d8100118440c809201400309589441c051140e55124501a4024090b41c1c0024180345d1901c11807200300220000c25405031910030a40713100d540e980d40c001040501c8101d690340420110071010643c6801d0503009242c1d000002840300c413091b0700652000b0b011700155440b4000040945408000c195680b0809418081441c00d040c400d00c0021008280d86100611845440f1011103d14115000b507035030240e40980740491007075540c0c0703580e18401000b4090070010a0300c030307519020201c109c1310700401401d1103456040e110760519a1311448198020407aa2580540500a0f00310940c0080c0448007455941c021074041c1c1505ca0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 131707176 1250 131705926 131705933
    0xa0e0106080a0b0324090f100914120a090b030408090607020301200307030e191209030f080307080a051005090c070501021605070b040602070902030c1c0618020f0d0522030903 77
    0x7200040c0842e80e1b20380108000c0d1400c0d00000c200b120f1412070014011941010502d000c80246612803081000d40c000e600050740869818401056a10001d980e070210258a410405503d84000e50f0b00400110307013004000f03018100703100a0060755000600000d41016403418981e54645035a4000c40d1001c0000704200c6034603014411b000ba822007110090040b00000884000003103d8074001a104c21f0000001c00110303440b445802015580c4071082100201c102e141c1260b05805c00c1d1a880c01003001c003400985c1420751031003030700d01c102c42e01101c02e1440e614010910100c032001401401c0802c400304984404900e003400104500741a80c519510440d0315410580c0c24000390b5004001c0c0d0400030081003000e268002210001e03165035810040c0c0c2d075160498003800504c5480c80303158100780b141c0610903141190741d0000c0119000c21081064590b08100b04004078071624040c406d80d1b0f070341403044404641c2561f000310b074810811042d4094038000300101d901405003000e030480000340314040c2032080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 131708426 1250 131707176 131707243
    0x120610050909040809040e030703050316030c0c170d060b0408100905031801021903050307030501080102090109030b130b01080d020c0109060e09040c0e0a0e0c0a0e0106080a0b03 78
    0x821015180c158188251140054201070016002400382078021807121074070b40d110783c0043c0c9285041011240c0d14001480c000c1c00c0c07a08110303038054662410030f84132400d550003400b841003644d0031640c0e5025024000c1e620a1507801e601001c03440e00e01800d1000d4441494103104a07005401429881c07529680f17054002d030b1401800c5541c080d5a0350601b598000064400411f40c1c1c0803150f5400b00ea01c1045080004078544102c9079254805440c0030b003005818950400025405641745076001d00a0341e880d44c1d41c0c18241e00c0b800e00b0281c00269080701c1000071a00c240040780d04218007030804403a408c207c0d141c04840c083c080c3c0100782c0176003008682e0f066031501007088510f5000301307007171000c089407400001030240e6211138251030140c0b034a0000a010002a500b009000c0c0032206482000b03801d0140b8120300400010240070aa440385540880f094500101751508035420800c1c26440d6a080400071581104054040d50341036440d00f42d5040c15035014819828180102c0ca6400d0000c845902540e20 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 131709676 1250 131708426 131708449
    0xd0905150909040b1306020703090905060a030206040603020d021b0f07060801080c1003020c0706090501021501030b0105060903070902040303030903030605240c07030b09060a0e1506040f0b061206 86
    0x90403040244500503226a0001c0350b100350000388544d07a80c5c0e642c0b114003050b04070303500c40102113a01c001084010960006072900640f511020100a6990303000140560342e051030001a52151050108124461198001380886640c281c00942040603c08502111206074400c0d10040d030800302d0030b4400b608003008148020041d510f8175010552410301d100b5250340c0804003042c011092201c1003415207010386c040b1403041c06c032802150402550b40e6402000000c41d406002d00500910720a02c80c0c020348450018140e07900000e82c401281d18007070811000c3e6010705595a018003a201000840210910107130005601070384000c9210040d52400500312051ba40109200d2152261098802c40085001d0307451440c00640203030343c44400b95245460310b5150790004014140040410102106c04240f241c09503c031103906018054420b0f00003a2204449800582c0016400e0000b03103280c501600143c14a5415801c002090034060012440c10761000d0010303200c0c003441100f4040f05d0b0420003005038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 131710926 1250 131709676 131709709
    0xb0a0b09040615050d0807260d091a090c1e030c0d0507030c0e061306121112011e0c050a021b010302070b150f0307050d11030316030c12020705010507150e0d0905 71
    0x3071034419900c0508d1202c1c0184480007170742c3d40e905d1700900c04200540105004601d81080781d8904d501c5c1072066107076920038941c0e1042c001c443d502c245424402d9000ca502003000c81c0280500000300b00c1d001402070b480c0d040d11042e1042c0c401c200000001c50781104869024002161085026103460800d00400e030480840707903103000c0c0c5003200c200502d000e0b50903a910701a6104002ca1101c00001c400107481c138403120640300245d443d24034006244e9161900707090b07010310142424403684200940a407218041c410404016810280c00501103180041701668000c1c0141401414a031580e203441007050001c03203ca43d180350307840a81c101c491801c01500c00d03402ca001c030005c124907800c000118000c0110f0701c00091809548005443c00c1d95014015070b14406201038511003c40601d060050007086450030940d00000c0b01e628804030f40e803011800109640040e11210314041507542e540d904000594202541144d60720003010905600340000c182242d52651070410880c01d03c1c00304030103007a2250020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 131712176 1250 131710926 131710973
    0x5040e07061407170309010603150b040b040615050c010e0a0b070809060103030f030f020d050c03010e24011d03160609060305090a030e0117070503040b0a0b09040615050d0807 77
    0x1c10009402c00040350340102c04c807007031a031240c40c3e102ca00c03070250050741c00062031031100340003035003141702c82d070340f1400151340c0440382406454541c40c28042120181d0082070a0041040661802180120300404400802c4800098404c540c40c4120b0f003044100f08046480005210038000b40039807021000350002201006040c1951640c1d8001d88180143e943d071909151b19822522080c2d0070a40c142c0fa5025100d0344144000d14200341c1e806041d81c0f09002d1450040e114101148800c03a14140300e0a0b8680b89184001241303124000640d00011403441d498180504100180d945031000d0109013503c0e58103000c01c5807284c0c14501c020707103858066000321313041500d01002c00140708000164003642580605003101603007071707500042f18810000c0e41244201c10f031201c01d0042c030303d0380302d40154030031801070794000070702d4540d000444280c0320100000b40d0301c02c1c1d0ba8404030b07012514590010b4800c69080190a08842d521004a0201040313905c040d01c0b0809c01180c1d00c070610204075240a01d01d0041c4602 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 131713426 1250 131712176 131712187
    0x23103061107110913030f110703120801061d22020714010506010c1e08040b0301060c0512090904230a0807020306010e01030308180c04020408030d0b01081e1005040e070614 76
    0x1c9003522500a10203410000302d1510312186900482c8d252254001c00000d80d0700c0c10b030f100c2c104a44e4807404051043c0018120741d000180a0f4815a03020010844090640c5130502d0020700300b242100003034203034001e200850313040d00d2258080c600c02000218070498805c0304c0764240360403103400c4420082070141480040d601081c0014810a00310003040e10040c1001c24030389090814403404e0141c1d80251102410010000c2165600001744400b003610400880b1032074400d51f0b940001c280a0305440c150040120004540007a420020120306500092200b58030100c1d9440b81500d80a1700b0107003501d03c0d040000300101135080900203603001d850160b0341c52051b9451998000e004200052507981c0175080c01d04402e00400c010b110001900d14000d0041d07498035240c04500c0d44070341c0300b00b00c03d52035075203003803000b0180e075004944440c840da0030082c20044600c11345103843c40048005044200c02611420046440d5541c0d00c01da80f44c0705582d400412110b03041c41c2018100480003c1c007542c02e00024802d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 131714676 1250 131713426 131713441
    0x10f05091221011707120c05010507030e030304060c140304031a07050904090b0f150105030610020102040f0b0c0607020309130906090b07030203070e01030231030611071109 76
    0x5254034020350396940c036a0b841042d0003440020080012500100140c1200002850144040c0729603210f01c0b048240d465060369445004640394034140c00801030540510f0400856000ea40a0800030303000742842041c1580050010342503a0043d041007020a030004c9104050091084c0b02c103941d4102000250318043c15901d401018041c0c00016524a02c03a4200043c1c9451082c3d054400d0884040d105012401b1365103008840004c0884400318050290380c0007039070804104980e04410441038440364550f448810501a962003401ca0160640d90204000641c1c154182c0c0a00c000303017a2244c9035901c0c1c0c0010402c890500c84080c00c000e046500903c60980165181c03607008614002001c80090000014034207034020b04894100606010a117104000949400d030300110b11407461951083c0101101d440103408902440528103c110740305185010610f510038072aa00c030322100b0190001d0181e4982e242d80503560300400701000540041040002c11039800d040c1c090707001c421982400c0901c0c0100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 131715926 1250 131714676 131714683
    0x10b0d05070509061207060c0b0c07030c033203160f05030127050a0b0f01110705040504050f0a051b01032703050415030506030f030403020603041b050a0602010c02010f0509 76
    0xa03192207400c10720041070550703554480381150f05d401ca1080d0390002d0b039109405031030100302000581c0d000841c040040c0010040504036004180c3c1a19170200940e990f4904884544a210000120002182240340301d08000300060f40f8804440700140da0300e14181d0f0301110f041c905540420244480c0140255080340c000c0c083d1b034103540749144001d40c04001c04070300045901407890000303103d0303240c4000e20810529940206085580c26200d040084c911540111580c4c0e8801c1c4461950340c200c282e06120031720341500a00d1300315004104690864541c40d6840e410300c00100750481d07044c0c2c0000180440842c0c1104070f00d8641301c09081c20000300d55444201c00b02540c0100c0c00e07070003c0944140040805004805440243c40314400c2c1c04c001c8114100090002e180c01d451562003481000302c0141c044600004840a9a40c00b42c001c034256122995081c0c0803c681c50301030020810400000f042d2900c0d200340d04e0340100303030541c004513142400d240046e007140c5c1e240025070503003070410081200215001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 131717176 1250 131715926 131715929
    0xc05030d080c2514011d0601080d120605190305070b03060901032613030204060503030403030e0621070305180c0a051c020a03080403030207140109030b0702030d1d010b0d0507 77
    0x207a103040643d400400c000c04084464002840700610812010b2240d10550003141601020f03005d001804201417503003a9102d409100740c20156018803c88000c1a12030b5000940e103c01d80d150126100d912800001e00c00c5950b20940f0f001002202d40030006e0240800641c00184001d805651545c00c0c01000700310b0803141408003520842c0d20b508500c4802134a04440e1031840341c03a40320b0342c0e1100c1320308a205619070070034881a449142000c3d4049442e10b0088201c17001ca981c191100042a8280e07002d101c00e541045020a000034280c0c030f8a0401c880d408581e01d8403070000c59600181a103003009401c4510725540d80107070120340c0b120800701600c0c1c85200c1c054064810403500300b601100074030300c5440c000b036080300025001016085c0020030014820081c1c030a4038801d8083e82c103e5501c071060520551002c02105e40010302c0b40004001007022a078001d904011584162498a410340280c101070361000c52504490090b12802140301d14420f21842c0c01c0104110340007198555540c4a07182d465038107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 131718426 1250 131717176 131717197
    0x60206060108040f0b090f010b030c0607020910030614190917030a060902040b070506060d0b04060906020409020304050703170a05040306020c210301081207120c080f070c05030d080c 80
    0x1072001c141800400780390f00748041c0e800003101103141b5000d24410f8454a4030b00a541c00ca609040c1204818030b008101c1030b0b0b00107409407240d8181181ca40811078a1000075240080514201101102050590080124248000624000b04c0c100303611941304404501c2d1440c0c1810307180010b01d9001407018011441c80ca122176180c41c2c0c9980f26201840c00420042e84201212407000400007102480b40002e0b05c5058020000d41c4c03000c1d6510003e11000d0820b9180003081c88900f0b20004002403269880440c401c0c0c0581401401e05849413000000c0340c2c030a032410f03521544002c00420400000110b0103480072106100d203030400c28170490240c2a80240d0000404942d000710394000100e000b004217404545c030784413121080786905036510708298801e00070050b05014581407410004001d1007218001580800014464001004219408a1301c400c0403181860b080110060b1800b8000c05000c20f5405039140b141603a141508152a084c4a40a06d02c24003920740c0802c000a40030700c0c25038041c1c02a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131719676 1250 131718426 131718437
    0x5090f04060504060e100602010509030a2601060c02040b01030b360f01031202070302060a1b0c09060e0109141803090907110c04060305060c07030302120f19060602060601 75
    0x10984001800340a00740c0041d900249448000203184000219083c0074031220003a040c40e0700d465600485c00c1c2c0f8411140102640d008202021000c1e200d0461007040e5101924846010740c0243d1100d1f82c0d0303c100382d004a000400031402c18043d031078a8820304045e0304007403d00304510100c00000c5480c6146d0300740740e640e9050494400c0035454006244400c00c144000f503948225161001e0005640003081c081651a00801102c81e89190300000c0e0010540380c0060440b41402c81c3e134001120107010100500e0b00c0c417030740007220400050000e0302c00300141605000100d9004d003072a42618901c00141d00841e01c2c10f081c40880c0f10340320100522550800440007040a004c481408124030b0351040c409a10340040d4000d023000302d640e070303c0130407507a5441001c0d064a9800c2001d4003000242d42081c0009409074000c1b001150700d5141603c02070070140d20a050144c01c10760303904001441400100d554010703030b100050070400e004140c841440f10346d81d4600d400f0040309082500080d078820000382124140f18 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131720926 1250 131719676 131719699
    0xc010b040504051e010917070c081504080309030c06010b1804020f0f0703020304150201060e0105030c03070e060a0506070804030c0e10050d080c0a0606061404060e100c0c062d0509 79
    0x5000790841041c42e500310205040d0450340c7c40c84054564407040c400e8503154409000442c0780c00c80454082c0744c904048003070440503100d41d2108039940c2d00c00323000503640b840f08000e1102c03168020b004140c0280046145c658a8056940e04111210010305a0500c21807041181c03a514011410665840100a04041c0d4891240b0700d0140d2540c412500071701903401c0e4654008840b00d038150403680568104404a201c1640c0c1d410906555216081000b50316070800001840060203804001e6071180d03009007800003580c0c0d5400421000e91101c10195084000014188140304404000d00c00038420004294500e00e400d071010180d4100d1805294071441e001d141540502121405607000100380c28140d4030b642e1140e01d400e00c0208604e10448000c030700031042600c112000b101c01d580c1140c6080e2a620800c010590400c200e443c043d0042000340200c1500305000b05010b903082030060060ba44031640802c4845900621040a080f060003081d403001d11034620056000c1d042d40c140840c00d44e86210141c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131722176 1250 131720926 131720983
    0xb040b07150207020d15110301081b010e060406230705030d09020a0e09010f0f0b03190c090c08070219020d060207020109030b091e0705011e02010f02040b0c010b04050405 75
    0x28803600c44003075801903041c4100c17000c0c80032000c00c4000340104900c0811544800d080403807000d0109205600050300441104882d1074150390709580200414036200040100242c0000c0e841e400540040002074841c0c0e404280010040320001100f2500c0000d460420f9100d0781c0d40c6580784104180092071030349400f02d01046450b1044201d01404c1c0d40c40030700581e4030b0031700d001034000c0c0301704810b401c20b03682800c03440c042c0e42100784507025203420060081d041d03942c1d40c0c80c25000306680b0440d0032180704483c0c1000041600552150346039024941c3e0300c2100905104c0d04c001d1404041141141c8412245400d110059554079031110607541d20040140e20f5481074001079541c034010f0f91002e000e5a10101c00c101c1d6580f03010031400c004c140c0c00c800700440000c0f2280019510440c1d80200b40c082282600b807810590a880c52500c4603070741c0c82c4004100140481610f0059070402e510a50b00c801d00400c81901d186000c0c0a0841c2c0e150043e50200128034154551566404040c0d007a445030001806008119 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131723426 1250 131722176 131722181
    0x20607050312041202010f05070e0d0201050912030301030215030c041716090b1008041208042108010e1303020d080a020f030114010e12070303050906090904030210060b040b0715 78
    0x842820303050302090780c50703e13040c074100350b0f1503414501005500e4690b20030490000751203554000c00040d669885048901c0c2e05101803084002030507418000148050350141d658448400c3c84131210314003468030303545548148080d0305000d4482140800e030a104120048841e4010744080780c2030000c40707405081a05600030308002c403c03059041d040e8080c0001140e0318035190407200820300705652451810940d500203c5941400b600c000301442410f19200007528032400c0b0079038201d070140c401704108141120780d015000c881c4107116008906000c00400042012802c055400074003820004422865550001d48800c0c01e818204188507580001c103c0040d100e134180c0c0d40071205140e200790340b13513110810700304a5a20900b0540c0001c81c1c00010317003610304020b01025030844640c03005240c5e01d4103554040c1e8003074110301d4034075030486428840081c0558034281030a00483c06a0081e100526100c0c404105545041e0004c0e02c86040c00c1004005200907c5c049808068010036501204044110607601 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131724676 1250 131723426 131723437
    0xd0309030c141605120c100318050d0906030905100c050903012c010c0804060506180109050a0e010c0e0904020301090b0c2d0405010503060a08010e010c090807050d0206070503 77
    0x60364440c0740c000076540c0c00003618844a842000c00031079035a5503103040001026890500e00704541104190510501700801c2143c107047e15414041814500a004c0410f900c0041c4800c0c1d9056101245c08503405412441c000c002c0c100c07919040c820340c6e10300e0303e0322581c03070f0548000e2418260b07a81d080d0242061040c0d007503400c1802d0040092140d0f1180c20031789000c2c0016000ca80c2010324610b030f09883c850130144151841700321280c490344c4481c0e841e51188c00003094010501a0006100640030541d02d14100301c0c61b000e081d0341030b8006402c0c10322001050842d1888061110640e1500703a0b401456034003c070090620810459102c0c40c1030b6100d1020078090300c0381d640014940825401840a009551030141003819030b2105c002d00a1449450f0207481d03107010301d003d403080f00c50030801449203500c247d00443c0d20180c0038081136003160f680c500143c2191180522903266940d14402c4504280c1d00c0016800103100550040083c542000d0000381a402040742c003e20802c40003d1000030044144191007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131725926 1250 131724676 131724683
    0x3020f01090503010213080c0603070f050a03020403060f051e0c03220b0405010507080a15050f04091202060718080303060607051e0715020d080703020c0106080303040c030204110a020d0309030c 85
    0x541b1000b01c0070b030040318032070a4055244180281d02920446060441c103032403140b19917680da04018091711006952641c4001500e40c2019000c200100114115008403022000d000340c0008051905102d0310011244050904000096800c10f10801c80c146105903a00302958038002d14070280c91888286041200150080403d00c1d000100006d001065120340d100c0d01c20307600c0710581c2d5610106e041044070811100780031130004454051080e0700b0945039072483c4170400307000001c540c0180d4550300010240070a020b0300503403100c02048a00c40d400417a015909680703000c0080304a080c101902d88900009200c140148004142b4009210f0100324507406031810070080c03c0c0303003980804807940303401141c02903a080b100c1c00c0300c524480c58030000b03021140403510b40c1d509600d82c41c0c900c0110080e40c0700c1441c1d81d01a640751040400d640800b0710046020703a12602a502c4c4a034914818402920317504200080c1101d0244248400c1d5034003c241031201000a03d40000c1c5188035140c15640702e1000700d00036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131727176 1250 131725926 131725931
    0x2a0a030f0c050d0f032303191a060910090b0a0206040302010c090806060d02031c0305060f0907080408070c0914041419060203100e04051e0706050403020f0109050301 73
    0x511628603451a5618011100c4040e11034850050000504070554014203003016900301d407000c02e10500560b0660203d500f02480c50380d80c08003450140b90410f9070032100340c0700c8000c0b440c1400348907481901c0c09035243d0283c0300405401000050101d000340741c00c09000d0011046805600740c401c0c00d65034083c20b1003041407511400e1a450083d5642022034048026600e8525060101da01542c1d80304115011100145055134582c400d0001d9111440012600f501c68490000810703501040f40000e01900b5690000c0c191400d0340810042c00c500540050040c1c8407582408a92507004a11944c4a600f0030a903590320002460200d200d04e845a014000051400c02e8040b2060351454170940038a0099016aa610402e0000162140000020001600d039550300704800600581c0145900c440356102d241192943c0704050000c003103044408503402d030041c504a80c802c1c01c2c0182c84200504d40c540051450608050001d01213210381d00005c0d1080d50b00340e000f201c10ba84180c800d0005418054001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131728426 1250 131727176 131727179
    0x305030403030905090f0a0b120f01140f040302030412140a0b040213060503061302060d05010308091806090103231015090e1506030a0c0f06090501050a022a0a 70
    0x585980181c001180091000300c8002203030b141c1110514000c0b0000003081c000e80c1c6403501840c0080c609082056000740c1c898020781c50007841480032500e820303405da00215208c0a80007602c280e0100040100c01e0080710304081c400031070f43c0001584c0540713910070f90002d011411402c19140b040400d40310081c4900c0340d14000820841c039000e00c02e000b507200703840c5080608407040c284d00c282c94050041300e4055000070000f401812041045c0740b202400500240e00e8003400e030724440152502600203440041000407980100c0c14142034089012901d0198501c07681480070000300038000612001e4403840c9401d0060341c6049500601d00f0030100c0940442da0210b10050000c405480c802c0f04851001e2a5a2400502c100300f90180030340c0e0071055806000d0f000720030300581c0050b180142000e030301031042d0040000066403550301070010780a66141c04041500d030400003005200990409810403c0910061a8230b640000c2e42c40b54234075160b950103600403101a40150310043c2a60201d41c4154201070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131729676 1250 131728426 131728433
    0x709020d06051002150403051e03040602190503010303080708040221060603010606050405010207030b130203030f09040c09030f120516061d0a03140a020309150a1d0618060903030403 80
    0x4180220b41c41a40e03820703031000030b001060740ca41c2c0350302d101c201001082c080010002403040d4014108500600c1c20016009403000581100303810486044807603940c00603035511118100a44904d564903d03142003440c560540e580103141c010050203140500441c1404101150b50340ca01d00382050b900e60115040b0108110009a42e41d03070300341c2c1c007030380a03500c1c02c0000715516100c0d600703c800307039141a001007180e103186640b1540c01d10b90080175140807041d0000c10f1001640c0520044c130140c20f00160041d00d80412000b00300441c1c0c1245103010a000c3c101c00100000380d0003c91006143e03411078100400042c1c00310007a01c06116078207070090000161260300080000544c02071242d00015590986c243c450020126036a08004c01c1c0540400c01d84861015071903208402002c00408900c103580c14225000003044020340704040d107800e1080040350b4900740e95880151125401e64400100008010440105038240f0640c1c2c0808062013a0701c4205449840d01000c41c1e040c0b00020f030403a5691541ea04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131730926 1250 131729676 131729681
    0x100c0f1a0609010806090705060d06090c0903060614150304051c05120906010b2512050414011e1d0306090a0308130302070504050a090209013b01060e030709020d 71
    0x4485501c51100302c00007140a04000400038401d120100040c007205040c44100803840d040392103448800ca80740c440120307032100c1600070401c550103a503c440c2522815031419400b070b40c1c11a002000301103030a005090082c0d03142c440c0c42d0300d0411001a81d0340e4039180da085c0035003003511950004c002842006008210300d41c1c0103000700507030303007621013803850940390404115101c0c0d0080c0f10341c20b00361000380f084401041c0f94007500c61039151112510f110960381551140d46a113800780c080c201103480032404200ca404141c0892030000f800346070000104070030f6805003000381081d91400040148d1400d103070b036403042d070f0300d051450310030009040341d0603840c104000c6540c0c2c0707508110880001d020880442d9a001d003c40e040d03c0310079410340107051054240070912004040c01003035414110740768800d1002680760b0700c0702c2c0c90281c003000e403c5070503140b600314a983e03500c00010700c0740064040b0000c2c04404150134001d41415561103150000b01c241743d031800a481c1c000640c0040030141d2001139103140980d010b6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131732176 1250 131730926 131730931
    0x70c0507062102030114091e090102040302011e0207260708030712090608060d080909042001090b0304060e03090907030f110901051902031606060311060306100c0f1a 73
    0x20000498000c1d9215000c0b00f41d01080c424002c802400700560485481d0003019254080000701102250300a100100900d480d403d60303000540365030006052043d940e00c40ca01c0000c04075005651044184040341c02503031851144100e54900c0c0038a00d4440810702c0c84030103001b050301c4400441d2042501c44c2c1c1c0b59034896004210440b00e00c6413200242c964580291251012541507071220724503955107405129100002d26002c65240b4400c2203a4219036030350703990141c0103a0080f01444503850900c2c0245195161200380070b0305015030b030001004402040c00c1241d50060b805507010545034a0159503520f103000c0e101c0704a40c032910140c2084059649940444140ca0110805000d04e50501a0000240c4541e1501c940011001c11115081c1c01800000f03111b5603040b8412640b8040f85003007011001d4406441c2100c1060310703240100107114080d25403c00709101260300c80d10b10b080060001e4040021441008184030750b44110301c00b07000d15407283c06007407904105208940c214818100e028880308 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131733426 1250 131732176 131732207
    0xa0305090106050d20180106080901061a03070f090513090804090606081e01060f050a09030512130b0901021c090e1501020f122205060a030b010f0309020102060a05070c050706 77
    0x6995a4010071b1400744403880d1034880440804105908050040b0f880c90b000501e216071540d02c1702c1001401540c0c07034864070301d0109084282500e0f41040d890007020155914946020045842000d0007960349816030050141d80031000019011003614200c2c0c7c25000303950207034007110300c0c03c030000914682058000c1c2c8143c4a404000200185c46014941042d03403c0c0101e0000400c0e51640c030340554015402000c403074403c5d0600780c032040d90769981c0a207000c07042c0740140341c88400410440070046100300d180014105210020f0304040f80280001c2d510300c500d80502e05015030f247c1c1d0851500e4000c482c983e000d0400c3c00b4503049540703008800300c0512001d25016070300520540e07001010003900031404036a240d40501e103091410031105806012843c41c0c0c86caa080c0341d60101e200003020380ea480c0040c003800d0700070748020070359180a00015020610490380d82062505040782800141c2c0c0c0420300ca64004054000003440d0b0719460b42c212100111204000c0042c400c8030004101c0c650440c0003945030144 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131734676 1250 131733426 131733473
    0x50402100305130609060207021e0f0301110a050307170702031305030a030c0818030303090a050f160b0a0c020d050105011a0c0c0402072109050112110a0305090106050d 74
    0x2152022400c994080b41c038041e400f00002400c1e00056010303080b4001c0603019450141c10000b840e000210f0208004c1071441d03044e00200e03422580c41c241401540c488101c00c80c02041908400315400c4060300c1481049810030030000001800355015401c18140410315071442021440c004801a503130341e000f10140021120b10100000322468000342101d120355144d50ba046810305da9507203506440d0004c0311507081d400e0155075981500d44003000038511178080b000007018032903403d081090a1850040c0521415040740341c02521141d0417210390340c122010441d825641d0090b40108440c4148048002940221000002000d0141c1500241c0c103803554031171004101c00300485800c10310701c240c00824100b600315041c0c10f0000d00d0706a01801e00d00b8081e410f2400407002c0d5601e004c4408400c0c000318808912407400510207541d108601c2c2810554001c001c000c01c60f40740e6020203c07401060011000c00d901d400014221000a411131001880080c3c0710342800c0c800c61800340c20000d84810308440491 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131735926 1250 131734676 131734699
    0xe16050310020421060b041e0608010203040b04030f03060f030b070e010509010c350a11010c051b1203070e0114042d0302030a150e1513020411030901050402 69
    0x85442c82200c08a540725106000e8001d40c40321000001c01d404a130540b03c25a45104156450701c40c0e00950200200550510300040b203080c503210110b92a50300310101e10b038030500401c00041c034091680c0340c006d901428415048809044128041c0c903403500024a042044c4100108120a80304100e0280c003041c1c42c0c809002103000300444550007845500c0340080c00c28007800020641307000020306d50402000280d14400001034a0300d0281641d10702020808500160780400c4543c490707503c0d0004070b181c0c0001d000e0740308200f10091035130140e01e0060500301440669000581c204001c200345200141a4280d00c902d402e10000d4605c03102e61800d140032901304213100f14884503d90443d0151100001c0140120300c1c01c80c4025080b088015400152000c5a800400540d40800010001d5485807550355214080e40300c06000340c88070680b5000f03c0381e010440900c80794000c4070885500200e401d2a03461079590130700000b009410040ca106001d40e20000620650307503030642026100340d000355400002382 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131737176 1250 131735926 131735953
    0x80309060612070b0d0209040c02210a080417071b140f030307030e010507151e0e070311151317030c1902040f0e0a03120c050904050a0e160503 63
    0x285a49071680b4094001e090180504841d000180480307900ca00d00050030100c1020204d070032a8855412000581d005106c104001c03243d4080f00b40115080110642c20026600005041c075400071340010310310030003201e03484190300f8840c2c11f840302c49400c110102c2c0541d45581c80e0492090044c00740d014080300c01c1e241072101d810f000840d400b42000c003270001d524021040d01e04894102c090070407907040180402c581310108622208984508088010010b035030000d40c5407241d6080030390140400d80d80e040042040300302c80045032410861341c1208180c1003040e140c40008928900c001c0e6940d03840c1002044401d107644a0030a140260384a45405004aa1441c070541703681e40501e0717501c180d9a5101a03102c01c04c03280f86c1e00358101c49a2002d00080b54001540c200350082d01c6220034820001d41c0140c60400a06501030740201e00c0b00c0c00c442c0100074992403040018018880d08124038001c545500110b0341104076a402034601710351640030350b2100b02d802e15007140310f00d1092280910a1003a0140f42c04107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131738426 1250 131737176 131737189
    0x5040b0a06020303130201020a050303010303122d050604060f0f0905070201022812020a050c06060a05010914060f2703060f01030b04020d051603060f0c02030f0c0304030f0803090606 80
    0x65079141c0d00258256a03d200c529a002d0f01320100490443c050060604002041000510b000e03600c01d884248400c070036541404100c07049050246207040201e80c810b04940c5c2240e889141007020a0b00102d019a60300003c9405086140e021070308151044100180414001c05a201a03560b10281840151100d0724104d080c1d02034100a0110451900b0780c6841000d810712145181c0c4802d07041124103549403910140c01c0740c015411800100f00c0000340041c00c440b0902c81d4a1f4800c00803100703c5012814000002e0840089020300c60ba400d0603692201e2403996024155040c1c81340c118100c3d40d81c2c1c0f1600700c81c0315900c0e6070f4024642d0004d110725160a620b14010507124841c43c00100c00740226807031900c812344c9100001e401a80c00502e40200c420208006000d00242981041c10101c17900e8958508002140c0c00d003140d05282500d00000d03100da00368048112032203c0114084161207441500426080d445030f40d0008044e420046401010400000b0280d44200d40042c1613401c10380d03440050240 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131739676 1250 131738426 131738429
    0xc020c04141609050904060506011701062a020a0f05090a060e07140715051e09030a050a05040b0c01050f06040b09010611010209031902103b041505040b0a 68
    0xd214848000241c5a600040b15640d038109079450305020840d9208041484903509a4090300d146840d001006001e50b0003070002800014540000466907144c0300e0f004002000d0008903061810b030502030402c0d03800807200f10060864004000c00c034000d55441c0e0702d203521401480781901a14581c0000b9003088014882c880403180600000c800035a2040d10803941803c00355002912940e0038070004022a003100034141100d0700b220380c006400d0804040f45210458207084070b020b6102268100480310710080140d8207011282d041a68540d0f802c00c1c000d032500d014036006480f039140082a04a01f00b0015004140580043c4007448200d4403004203000c181c5004407505c42e00020200b00401c256445101c4045100380c0d000300040c1003507101e40000b404c1515100094088007205000701c029458040d40a400242ca9801d1800c41010002c40d0088410003894070800343c203100401103001548003102800740ca400c024400c10280c0c401c506442c2803000940a440d0140c0d00e00b505140460801e02c10a00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131740926 1250 131739676 131739701
    0x130608010c0c0c050603060d1a0106030506040209010c0b04080912210703050702010e0a17070305100e0d0e0105040306020a020f011104050d0f110904050d0315060509010c23010c020c04 81
    0x443d0303282440203111030b60b0301c040c201d950018145050b140109002c00480a21170560014404c003d5240600c0201501c1010300070500c114410012189036a8200c01e1003035500780d03c07900c001d003a90398030f050800c080d00845849903089448500c1d80c4110300e402207140140805519900b1024030000e902044044c000e43c0d81c000d011900030840c0e400558090413030041c002d04000e1000100030344038082000115560102a06203a0040c0002d004000f02407080e80c1034040194001c0011100e03801000d5541c03901c4500400500600600000c026481502100d01954100d0015991800c080000035174074040c80748a012030394a40b14942a5a609020403682110802000d41d01d01c00704586034000c0341c41040c6002c9a900b41c4984cc208002d4a4005059200d14003403000380c034000148140180c06c1d0756040b003408014803d1100b003800405e80040a43d407041c0350a01c0c00060405440c6041005100c011451409884806040a0382600150004880b02c0b00079405d98144c2c40705141070001303480804080d072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131742176 1250 131740926 131740943
    0x4030210080a0c09030f201e0f040203100303110307080412230d030f0605040c0507020a080303090a060b0126100b0306151c0203010303090302090f06010e06030601090302130608010c0c 81
    0x43e40411049100000c0515001072021f014000c214001288488140c0104071984101c1c2d906039454a0680882c4152702e500b41c2e01035146281c548003105403000341e800001e051084442420361602e2080041e591081d030b20070000f541e41c40e00e0f0240b40130712a9000400316905a140d444030603403400085406950302400d07500810f48a95450340c15405404480c0311040303403a50706c48000801e0360711806945044881c584409580f2945801880100500b6030010300c5c042e031080080c044001000680024900c1c1c015000244240a01c001211103002941c810903060080b6032044000e41c5442c40042d0054404200705c00082d030350750041c8042404202d401e1a8014040b0405080c6840743c08001c0c1000c815502045500c0c10580750381c04200d030000e030803d50006803450310503c1141421302e0095005510404030901d90300c2c00302c0008290610120456004210110203e21640d000e0041d074000703542e00511502803940f040401034002c11162084028560030030001e2404d00d8080da0001040075004400e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131743426 1250 131742176 131742203
    0x916150f110c0904150c1106060d021203032509030302120f0708030903070c06050f0a030b060d02041d06010306030201081605040906180e03160b04020604030210080a0c0903 76
    0x166551100188120300318041e44000910340d035a0401c03c107218910401c0a5180b00d10351050001c01c0b2142940014240710500541d004800c20005019911072401c84a280c08400540b000c52078000c84100110301601c0088284040381c1d42030078085240c4000e542d4402402e19000c1c10842c3c5200040c030005e809a048803c83e15401c030000307002040d550243e01c1100e4509803c1e65120100c540c000c0f2080161038002045c0c4908126546024000911642c0380c4a810865204100f07800c61098540e61800d040d56410351560503114203003a41c0890743c40e00800c540312503035001d5864031444146400200004501c000031450340c060f10448055a80696a01c1c41c01d580b03841c141c0342121491400d15050000170b1000085901450203102c0280072600201c82c003e1104100314820307504000e181c810b80350000e000080310010040d075142d040e541c01c82044004d5403200e0010039154400d6130806900090f0300741c02083c0040e00504042d0080c00d000b0000c00004210344001c42d1402c440d40402050742040011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131744676 1250 131743426 131743457
    0x30112061d1905060105030d1407050f0105010b041a12011e0e10031b0803090103020d14180601060905010807030b0f12160501210e1005091615 63
    0xc00164824800104201402044915001e20303010101000402c40a40004124040c8243d600402094008002e902846480505101600802d01c4080540400d6800034420b0800500ca05200481c00800c07441d610380004141c2c59106000d01c0104064445000c20401d840e0022038030070700c0a100c10f101059080c04081e0401488800c9403414060300034001046001a420340107000c1d810703031f49034548418514681103215180b11b10443d400c0045101041111000100854021039001d00e0016a1038401c862002c000b00307804486003a030b00d950b00c0c04014000701c061511202d0000c440c030803251140e81e01c10b0201c917904a1405202c0c0040c01010200300002e01940240445041c02031881455020110105c6c124000c580b441c0700041d40240065a54051001041005070030207180c446c0c00e191070001c611000c0d5542020a124032a965850040700390410301c010700b41c0707130781c0044140494180345080c1e5641d5075410a43c800c8a100d4540000342d00d0340e107450201c60588054070740340c60100f500346 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131745926 1250 131744676 131744681
    0x240315041a0c0a030c08090c1002120301120c05030f0307030c020a05100c0b15060712140313020a050103020327030c120c0618060a05060105070218040302010f0203011206 75
    0x30411120840c1d116024100c1c401104000c920807010520002e480351800c00c1c0040c2902c000c03402d440305101c240820b10010490129462140301c005a46841d521000441e0880c81d000c1c52546010501e400400082842c1540041c0008414003404607120f03620345a00400da120040300d0840441035108005001c006405001d1aa81c2c0c00d000070103806049a50340701042c80595000e0b9940c000503051100902000034052265401141500003100780350f0f107440200d2124420084050014a03e8112460901c1d1041511900500a80c10003985904051340c2d4200c400c245984100e205614042010529500c40d2007600e01c103074007a200f6004d0f049003100e1401410301e0112074411306800100304403212102d02b00011404900c0c4401443d641c1d650803003246041090141544050311201c44520040000000f1503c0d002150703079800084035140c01d00140c031603102d03000001350001c1900402c00e05c4c0c1600c60104602c524080d800038000b0295001c807800c120310003401003061400180c80b1b00e00100f0b8869 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131747176 1250 131745926 131745931
    0x6030504060b0d06020d050108011802190305070806070207061b110d0602040609170106030201050a050a03090f0b0708070201051b07060902040501030602071707080403030e01170a05240315 83
    0x1401c00240482c071102c0440c2c1400c90003001a00d100b500024400c40c0000944500b1780100328010003000200703100008419000da0700032010344101c0d40c0c0c004040004003c00820001103a100f021210020344d41d20940b40c481e46c08035910009070040e071000003105400303003034403003424003031030004030f942d03004a07a981c01c6420b01241030241c005003c640c181000698601c0244080d100a8407900461841c1c0000038200b80c4440d14074501c5039040040810050741c1210941e04205d8490a01d540c88a0401d00700720003d003204000540112004071000046c03020707640e00c181c001c5d41c2d030355239040d116074030301c1c5007a401d0b22000c3d502c42d40300d9000c000001781e280610034003800800b40b140401083e00714098000606650083c1c10030313142a68000740441c200524107141428466030f4154860178a1959199010b0901652001409000084618100d43d0b0b115010ba1620b407182200c1c04046414418462002030604560070000c0b15005c41d00902c4924100c2e0710040c5201d03008008003008903075801001c0c1d040710007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131748426 1250 131747176 131747183
    0xc1c031b0312060602010e0c03010b0d030311070c0608060a0914010e09030405040501090f0507020d170c09270c04051f030608070311010e0405060d061e09110a06050406020706030504 80
    0x40500324481d02d80c2a018180c0109255030000c203c0c0c1946030b00882c205248200454072903031400c05214400c1d01d80880141486405003000906464000c0b150582c41c4a0120001d0404c145100080380c42604901c0540c000e45059652400044d10b68819408489a8200703000603640c0000042040e0405003000f554409021400c0d02d042c01d80d14008901551020b1b003056041c9511000100c010800c1480b40c0e507403260080c07008044a8a07140d1004d410605180400e854450071400080c4940f400c4804589621201504100081c1001c121406010b00000c10303050210000101151004ca4464103480c10b03100020801100340c43c00d40502c0d800e103444070100f2418991610b1340052010004e1146400840c094100c420048081703800051100c0c021400581c40b803440d1100b8030825449280703840c0186644880f000440d41c91003801c1a40342903401e04001441800e01d94013a0803c08076030101c2c41809019a0071146040d15040b00b580c013401540901c100683c0086000c000f403034030070f41099030040d01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131749676 1250 131748426 131748437
    0xc020d050f010e03040815012103021911090f06031209040603140706080f1b0a090b0414031e0a020108040309090603030f02060a060501050a030c05040b0c0c1c031b03 73
    0x32044690342c00e40300781200c0c1400c240c10200702004a030505010b4443d041070f10701d511111642c1800c11401c41c503000c9403011288082c00800000405000704003000c40c50f1444444000d0282c89441c002001d1258028264024580f000c08035201c1c00c104520710307001d1580200503100d1100d800e800f0481c03507003000c0071030355100b5113400e00000810181c1d0b20388013000d480040030b04201400d0900c00307000c0d2840540613080004a01c020401c2040442220703d00c00100401269500d00d1401d0342241c0718141c0360450030b40407500250024040e078041400303c3c80c1c0300c000e41c19a0500b641009840d00c0c3c10700341801c0603101e40c01a1a6942c0150702c1120003981c040c3c030a042100c800303a1540c02030021201242c001314081412650070103d410b404000316a4402030fa0b41e4140801c60500300000d1560241e40608000c0c1a21848030036580c5000c0c10075103000e03107a143c0c0d60548801400d04055a9100142c0c005070096090030b02e0191031020038402c00c41c503203406841350010744600506042110070140001d50070080b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131750926 1250 131749676 131749693
    0x1020d050f0421021c0f061109091005010f08150f030a0602120a0e06091b21030409150f0605030a0209061306080a0905060f06030309060d0f060b0304030c020d05 71
    0x980e150360203140c3c0014580000006144140300319904841043c0d404040800306900010300c1c100400c41c602984072102280c2030f048900e142e40786000d070b541c1940d440303d07803181040079000d018808241240c41c2682c0b28034610590140032f6401035416204541c0895444007222100d042c91004061012406003c0340d203d03500b1922488200c1c3c20036408650150038600c00d1120039409400380b0800d002120026000c5801e00f50001980e070000300c0314404070f1054000c0b800e00302c0da0703500c0e008002062400d0914080e104500841644940c018001c0003040d03032914020b5141482003180070016200c641c0810040b103818254103682a07000149820000c1c0d408101820b420703280c11020b00010f15500d841114420306240010300f82e128000c002e011003a150039a4040814000602c0e40e401440340c0000c001079454a0001c00d095100e40c3c0407050704188002100c55814200747d10a0300d8001800c003003081501d4070b403080c07000f4920050700c0281c000398603130061102615000401d0fa0040d3b100384104d0700e800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131752176 1250 131750926 131750939
    0x304140a0810150b030601021005070e060c07170307020a0b07060b0406080604050106081204031103070e04140d020c06030727090c03110702092802030a09030f090501020d050f04 78
    0x61501007100304925200d50303001c1d100d01080310020002c4d00070426034a007036183c0100004e580b441c14a1018400a4980380410f00c40d9018a0101011380340290800d42e950101c0041c1c2607030b03848144107a0181014008100c0001032021064400c83e85d402800b0707402d5540b8201c1c280070b46400000094134000c5c2e440c1114010303680d0700d101f000c0040c2000005080d0a00c0e250904500312601503002160329004821042d0507a280d04003242c4c2039941c0b100c540c03809e407503d0070f002c2840d09007250054261505103200f48414055100c001402507401c0a0407a10f4010320040d00300d8980083c0e03841d40783c0100041c000f0603006802412400c0070203078107a40210788840012000c4440d0341076640700d81342160765083e40408043d03141c0030700c2e40e06042946402c0d15203602079004c00c8022034000d190003610646441e168103e0b6606100c0107500c2d445c000425074032410600c0303840d0002e240200d4220045045811008030060280a86000716078050f0090001e1024113902035441d070b84441500b082c250310420011948 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131753426 1250 131752176 131752183
    0x10503070e03031908070e010e19030b0f10080f100e0307021009050307050603010302100c030513031b050108090d0516050a060b012303010902090f09130201140a020304140a08 77
    0x90341000c401c06140004840b00140c43e01703401409001c104000c6809001c01c42c0d801404088001c0000e8031410040fa601005c4180c0c44010707900000c1803003c0c2c0c2d8040c09519103e070140e081c0111150300500c10782c582d07281b81c000c1c0c1e01c40c204007a0041c540c100220b090180c0d107103940a44003a000310f00540745000030f10350005000d1000702c0481004140725407800d00050070200202e07030140000341d500d1482d42d4199000130354488242c5071801e0400103a04112002c26220320305407a40b00c0c0c44c90f00c40014036622482d1243c0100114484802200901d0600141e00d620880002e4051116000902442d4002041c21142da912510501c0340b0180300c0200c1e00001681049204d032020f0185c0400202c000d070b240d000522811181181074000d0070100c40c0c4a041140580450741110800c500c0140d8030380042000c10185071225005662149664081060490002c11168030861003640c8400c060241c2c0180c103101c90081640000c0142e00c1070005200c94240d0206001010400502c2c40020342d40e140109841c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131754676 1250 131753426 131753437
    0x60a03051009030206160c121701030818044b06051c1208060f0406031202010c02010509070315020408010c02030c0118020112090f02030304150e040507020606010503070e0303 77
    0x20707940d07886088a0a0650500c0443d802c03040901c2810300743d030200350000308001e000d158003400469800c1e03a01e0000030702841001d01c0d5100b003541c0304146034ae501c1c01e011000e40c0090102c40c94001500c0c43c0841541341c0b52040ea1148055810250710320340c204014802071151800c200412500520041a624600d482a8554400c0c04100208005092506000c00c0f03100d80381e04504484600051000090805400c64180700c805240144040d601c01000880c110071040220b40c00c00e203440c5010042c400010703102201c180320780c1c000b80101a03a181080b070072501c00b140e494919030408101800004e00c042200c11031400c0300f11016091070b84403194242112003d60f04100580e00001d490200e0345401c1c00381201c14641c817500303008000000c0d00041e1284103052680380c2c0c160b03540d206650400c080400f050f40d000ea00901201c2c0c445171100301c1d0041e03038a26407040d072001c80c61011110b41d030342c5064089e40d031103084180c2c0034144a443d01801074841c0d070806002c5000340f000f01d075907880c4e40b0b8608101612 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131755926 1250 131754676 131754703
    0x13006060b03191d0706080a200703030c09050a06030c12020a0810081b06091f18120f02210a03080a0c081003140a0813030b07020f100203060a0305 65
    0xc6018003240107000844191141d42074501039a1405080130141c0850100d0850b201402d2680c0030b80d5506410f000200140d0190308030201014030b03202d010101c1507028189903071107500d040240301c050101c140c509141e03600c05c0641c1310110003001c1c44441c0c0b10b40c201042d80500b50600e01e44581c16040b1440990f00800e000d8030000e2a0142080280c010340104030004003600b00150903d580800c41d01d880745071031341c00c030140141702c00504900b080c0c8030b1003140c0c2c04070300341510032020442040d50001c01c1c0c109070480c540492070344184042040300b1800604603800d644001aa84041c2c03c6901380f15411100e10010444419044100940c844c0e0900501d02214425620300c0d24600c0d01c151a4030071600c19046100400414804101c68103280d00c000c0d03002d80750410310349201740502c1c400e5079180c804400c00007060440c0104150354041c04210000050f284917503030b50462941d510004a94440c4060000641c6a0204002404018540c0c0c001d541000707015003c42c801c10b84070707114a80341004d800444c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131757176 1250 131755926 131755951
    0xe06070206160206060904240615030b031009080408100e060c0405030a1407150201050126061b040b0705030d0f15030b0c0405100215013006060b03 65
    0x1042a414468103501218030712401c81607518042c0000d50304c500040c00710340078170800000700d02481848007001c5400e025401100c2060301945624a005d0140740c8105800a0408081202e840b03010740111035486101400600303801024444d0040603000310901540c1c840f10070040031445060501080e03c120b01e07010b5020440c0503d400c4810724008004258200c031110602c028085a0303004070b00c940700c003600050700c06081e4081e00c26890a190f255071000d207140042208d152803068064010904a40c40540700100702d10882c002c1410b803080b102e085a41a410401c0021043d0011701528550070031045021802c080d2903001024560384000b00075030705a8030100b003051a90860b4058450744081c103d40c107002d214103130340c80e144d040c82d800d0000400b0030890000054040c0a1002910b008020042a20020303c80403000a0740b5001001410302d0f0790040c040000c900032a40181c10300071407144400c0c0005000408800001028603010308481d00d5440d0340001480c1070750b44003c2d50203140d2401c0b25 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131758426 1250 131757176 131757181
    0x11090a0b030708060409211101050a0614371206050105130608030307030207020301020705300f0913091a0603010c080c030a0c090b1201140409120315090e06 69
    0x43c05184006102ea0720840c10943c0440008031000710780007410350031400780307005822031204c1a1a0481c4080c9070001742e601c0c06040242c03c1400342c0200044910008880c4800d02c405400c1c42400c6294207041032941000c40040440c1c0c5035490503c00010744a41c000000e0b140d1101c010005049000505444291b210b200500c03140c9490842d5030416003010a08101c600d2401a0b01500c90000a224805046d07010030b5034029034a0a40441d00c1050b801025150210300c0045000307020b4400c3c071600d078041040b0105c0d150420107a103084a9901350502101801c00c030480042040821186200c401040d840c0c403030080010340b82c4814802003c1c07112002a4052414906240c2164515120002041070031002c0c8031041f00c0ca10100c03500a8070541d0085002c3d00e00c0c0724161003610f959809141c030003900044800503410311440300703810b0310740c08003000e031031000c40c1410007041d2191030308060301e80c7e20710201c085400c030300940c0301e0507400c1c08501e80c81e0315007543c0f494094211400c03440b0508054000808 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131759676 1250 131758426 131758441
    0x51605010c1b150b0a05180f09030a0e091801020a0309060c1d04090503090901090c090e0402010503060d3e040501030b150102030904050702010c02010e07060c030311090a0b03 77
    0x7a000ca441082c0c42004031003002c107807207641c40710200441c289507490b0740c1c0b40449100d03107403c040b00d00549405840d14040990540030300344d203440d0807030f0000d1044031003401198059070003004580381c009450b50b4500c1034400350b9082164140d00609581039444420200d0581c507002030020b4070085915407000165040b240c1050ba007a1344010b491002044002c0c18070340303503002000b021951400700654001410b011075150940c594445c04c83c01a42c401004030000170795a00d907802c42812140c841d5110240c0075666400c0c00b00100007510000c2c0802c03018400544107081c0300180454030f0b4003079580002525140200c13000082070b40128048049041c2c3d03044d44065425050800031844192070420840d0304d542c4915140e4680a00f145294140140103010329038820810741b1104640140304101c2400c0101010b402444d0140002c1c0141d400c0482000c0300c288045482e004a030507603100c00c20304c03240f182c0e0300f1001004034107114140e100b4103004080c8c8507119000e92074081e203045440c080e0360341821803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131760926 1250 131759676 131759687
    0x14070e0103061512020702190306060905010501050706091506080a1b0506070210020709050f01150201050c300907031e1203020304032309040606051315051605010c 72
    0x5150341854100502002039015802c4400340a80c410324020308440119802240640b00b01000a54002d051001d00041c00c0001d14901c0102c074410300003049620742d216040000d4030401d00c200b0303010a80c00c4c0030b110049401034104400781482811003054810303000b00c070f030320454642d6040720701d195001c5080d030020400e0801041001c001301f040b40c43d01540c81e0a00140c00c0c5d10550000a0282d0004540106d10b5802049180042c0852000602151600c2c4c40500342e03580d000d00c25004100c41402c090ba00d41070042c410b542c0501e0808001c1c0b841c01c5c20504031a0020035208049403242c201550450142c00c40b90350380b150041d02d522001d0003151303195062612030b0800c404014a40b851026070a800020401d003031265408609080142c0c0700c1d507580c2015907001702c0807a02c0c080803c0c1c0c1d404a0195440d00c1100034401d140c0f0446003046a10b40b01c1070210740710b004e002079600015400c400c0034410b40010b5990b210b151203151400c0c83c6051020041880e0103003082030112403a82d161441e8801d01078102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131762176 1250 131760926 131760947
    0xd08060f01080610050c031b01050a0b04020702010c080906040b0c15060a0b04151403040302010b0406060e060414030c100207050411070201080f0916030302160f050303040b0904020d1407 82
    0x2481d24020034240540007a440c8484c00401c0d02c14004006802401c482051007030f00c604e80c03100710400f40e11500301e07110315000e001d045591b11116840c10b960340c11180f80c0341c420344503825010396070100c9800da141d0301c40b14103500c11124541e006409120014905d80d10100818001012101400544510b03514078580d00002600052203642500c2003804500314074800e44080300d508c903416501d41a0340c3c1c80252402c2e50b000f6035408018400004002c1070540540028200080a440400840c1c0d5500c070200c0b000003040c0071466003d0000c2000300021400796507400341710100107003500c2500301c4020004910115040081d400758112540400680c80c2c01d105001c104006807480b01c0c9484c215600081c4062801080d225491a00c0d00200f6891a020003400152617031511000d451282c807400e0103580c90801807501108849003840c00300798280c400303102c217045074000380045003000c0c1028001040754218a1045400c1503083c0801d40c46c10003940200c403c500c01d0301d03000258a0400440040041307025 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131763426 1250 131762176 131762179
    0x1503030e13020306010503040305160b090d09060f0c06110c0d0815010201060b0d020304050c1327020a181e05180d0e040e0a0602040807171209061b0d08060f 69
    0x43c0f0403c80c1590f0401c086952081c2c0c545041da0342c0703c007440300c45406034040d000d011f010300d008642040020400054a12906582c40d101c00d6683c66807584220350300d104c1400390b00d0014142140302000500760f5009000000300383e000c120305042502081343e24004843c80e03107200280c208400d001c03c04103203040c03030040d011080c4004e2000c05d062400900e451f11660aa0146860b0300000007814443c042c081c0b00b040d141c000700b08041a0050707400c10343c0500740c1038283c0d0b8641111094480100011a505006d40359409000301d40003900d0800a0b80ea54118a4583c9080307230303111000008185048681c01c0903099801c40e0004643c209250030083c1d0070852017200e8560381c018102c03080d003140c21540500c0c0c2a8004c4a0104038880b04c04041810300f070320401c0081c605400410081501200811800160303a2080300390004c50829507030090fa6102000c28001c4501010080701120341800c6005000805000009060b0b00b464440a1890b01221220b0301000865207001d01450317181014807040304000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131764676 1250 131763426 131763431
    0x2090127030807020d0203010e1f06030213020a02070f080318031504020418050a08040924180905300408030412020d120c050c090f07030507031503030e13 68
    0x180360006000062480c000900080c101046210456441c98400340e451075010b0b009028a6034a01440b9584011624035410407140c6443c42c0e49030003101d44640003c1366001802403211400b142c4408000394403102900c011402490b20120704000504201c4004104050040d0340d00c00e02d00c1c209103003900c100442a4800d40042900d510a03c0d0340e0482d5681194040310006009540c03c1003a0804030303c1d26100424901902840200388141c0b0340103002103a100e4030301809282c4007000005103581a0705030241175541118018442111140340d03600020050703081c00110302e41207403150340c50b052440344c200b070080213a40283c0e0001c50840d08001a0050b00c180703007608007820044401c0d128002c0703010f0b0b84042c40c0001040010740d6a0130041d0100150802c141d550520382000000307080f01e11003801a12184210006250281480c0701440d115002030394210311640c407060400c03070280c035010f000314003010f880c0d00d44030a20580c0703d0039580c020f61098039502c5492081200344440e911190071744940407807 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131765926 1250 131764676 131764727
    0xe0702011127060d062301080f071d090c0d0606090803180d0b0f1608040308040f030c08030910051006080c030414030a0504180504020a12030c0510020901 68
    0x581c907041120034280c00621900c01804480d01240305809100d0038003449500b00440004c40b40d00c0305921b540b50000c02c00c81d0b02c440b081004015101400f042d81d001441d180e01d500042c0a2a103d052648002c62800d01030316020401000010209101a5a2000d510360700240c0c04116480d14403965004180900780030001910342700702c0d56140d02600d4bc0180001084200c201d48683c6c03500f11000d6800c0d8490324a034000e007003210090819241c100c6e4107142c1024200384c803060030750142075403501c25941642c0d480c541e079955070394103280740e26410011014001654020400103101c4000b0f5032207400420000c10121700e8806403d000d035135000c2c2000e158141d0542e0305128182e0b12114079680a00500700c00340c2e032520b49203003c0d00d1140381c03100306c14030310300000c1407240426500500400440d41d20880700c3c100c0303400c1004c250041f69020b440080d0301c81c8800c04100100317041041b119043d54000d051401c1c10205c65186c1c0b03410b01c1440744842d9211540002c0352102503800610020300451182812019035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131767176 1250 131765926 131765947
    0x9120f03050c090409170a050403030809121b19052802032e15060801050108091e030909040609050d02030a080c0f070203190209010b0a050409050a0b0a0e07020111 72
    0x602c01c14030f00c1030040f5241c2242a080c00ba01240c50981c00182e12069a5102000100208103400500046001440ca01c0100700f40c5100003a6500d5024405c0400368940b0380c4800840c1108035040408120501600020740c0300803100000c4814524000e002410305041e504040700200d10041c0180d9242d41003248015025132800506110403d61703c0c410f188110010012202c2075aa03460845010a0309007048855980b03091580101100d904e030b121118941d80780c500558151404550680590340f009504a0301402540c003183d80310749025090740d16000d450350100d02144000c44064034030984a40c00c81c02044810052303110328000e144065130a00540d030400600100d80500045030401000c90808402c414010845407841c0e03004041328164203800614900207501e4140c16449441d081000140d40b0001d4000c03201c005078550f40755031605003482c1c5241c0043c10080e00300d82c0015540c3e03810056944810414801908a15007254294a000c020080c01c2d105000344040c42e4001c1030104500d031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131768426 1250 131767176 131767201
    0x10e0907030f0221070305030705010c0c0302150a2306180423150115030501050a150818060f0a0e0d14070302010f02031f050d23010f09120f0305 64
    0xa26070490b007000b5008a800f1040d40701041c00d002c4c0021502071001e0001c10441d0000040400c103201d100240520100721030207940b14480c5c031001501581000192084003111003400b99403014401d140041c00040c080c4600d11080d03198200d40310740c041c007041444810b1600340202607100d96250508286c2e403a141c2d0310000c84601184044910b02503c0030150022038052201450b84002c01c1c99140466175211000380c83d6100803d10321380072a2401c4008107050070607200c98400c1ea41c0c1c0c0702e4103c182d2001d400c01241c1062008102c5034055140380d4102004c80c00600410f405084050440300070340c200380e2170701301c219001c004a1080039400307c8d9034240c0146e044800d100f01d90515120030750f191070f12030805a002d8601c175098296014400001c200140704d291803000001c0c940343c2910b020041d154001d101a1000e0342c40080e01340b00251410740441450102c5000040345517000109200700c0b003c0340700c01900c800f500111600c4e100c440507000c0d0158007180e00940b100741032130203210604140d2412000d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131769676 1250 131768426 131768453
    0x8010e0304120b041e0c0510080702060c090f0d11100306030507030201080a0f0c080106020d170f130f0804061115011406160b0f0c03010b22030503030f010e090703 72
    0x108003d4000001c3c18842500707001c4460000300c40700724140008528040713200700d515000d0f861090300150090402c84d0312480c070795071241d04a90001c11154071800e54502464014480c8541d00c41402e0740c09040f5070311400e0002000700c0c4140c1a88001101820030040e0b00412903140748109403030240100041003001450344216602804e140c1615110b0512201c040d0888040f00c07030b82641401c0d03044450a1f40803007040e048410741c1d400c1d1140640840c0003200e240410040c0050394a03640070200780c82c0044c4145168000d10103000380d0140c00440d686809840f681d80d401901d82d210007040402002c2c0e08581c4036602c1d110850054030050300002a11018008180150401015460002030701600c1e0401214010960b180c410405080c2d64078041c40000b8049804003c100d02440101d454007007000150b80c1a0b40f00c4036034090400c03243c103948610620602c8940114031718200702c0000492401d20056016814190b14940250305105d42c160213400c0140c860040b0340d00c205020400325410001101 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131770926 1250 131769676 131769683
    0x4091b050a0f0306120b0a0b030a020303030a0c110601060e0406150807030b0415090605120a030206010e060102030403080a08100501020606030705190f06020a050c0d030c0807051c02030408010e030412 88
    0x140e810302d140304038000d01d40b41d0080b410340520143d4243c240320300d61361440c0c8109243d240501840750b10409260302e4500c04038000750140d100740b02044002d00b1541124000b620b81c0d25100300d04604403400e803841d02c1b0080e40034402040140c0031f20811410540142c0d40900124584601c0448041390300800003c00100540f0800d40d480e1503000c0c1503a40d5412110b1019042c3c0b207440c070403d440b400140001e0071240304440c440c0c1074500031281410070100318a241e481c3c140d0003512190703180102520b0b522400900680c1140020040400001c00c91009451883c1d8581e480b070040e4900070300e03a401c40728100c0e00000e06540c0440100001503500040b0003040c0c42c804d0340c0300c1003c403010075507040060010b60054503060300302c1c450100d11180c0c0040c1c81c08600c0d000b542112280708883c014405102045000600025003201c01c0e5004503030309000800e409441441203942c4100c0c0c840300f0541022058080c03000503040010200075400c001d0040c8070000031304001562a091405070206501c028125004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131772176 1250 131770926 131770937
    0xf060d08031009060b042102030303040305180d14190b0c21040b060117060a0e1e011403150c031305030c030d0f0608010506010e040b12070b04091b050a 67
    0x580100d03480c07000d000043c40d4505044c80319a8485141c0121034001d80030b0000400c0100c0003d11442c8244440c7c140700c241c01038040d62858450b07803002c46055010320f801c10204003c04242000c1525a050a0f40e10a4062081a601c120944048600341450b01200c6540c00d09000544000715210750001a00721a600d401644d5551410000249108102d0b6204d984402d850040009111003115402e10906090b640c8100c040c5801c1007916980409131880d60f04000c0c0501c0501c20f06104103485074200200b02c07098a1140e03091151803585080c02d80000a40030b4507041c0c07040d02800c080250f1000124000c0700070725949014001071100d404000c000c116200400840601408018002c0b188003606c001c003034a94503c000510700024103450500030403158545040082c6000e0f0610030b25000781c0c0165039150420458808010141280f0200d851303001b0b540301e00c101e04d00602007000710002c000c0d036022103071150f1501507910b045415940108040c48014041d100c0203d034094100c8089502c41d0420 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131773426 1250 131772176 131772181
    0x311010239120607020106050607082505240603070305061b13080601180b010c03030e1002120906060102010e0d030510090c0e09010f1a0d020c01020304080309060f060d0803 76
    0x705440d0108854840e40c02000441c8800c42008020a10318400c0c00103030002c0c4015952401402010300c200c03000074042ea50240440c241c094004442e1903500d200d00310038140d421105440355404c0121501c005484605d690250042811905000381e5001e8000c40203000105e1541d141c50b92140e00007428200044c1d003c0c18100d03074021502e41a604600d03d03e00d01c03004825111010300e07030356000030f000d41000d5140e908619511b480c52402110700140060f0340320407010489990540c05401a420f03104818000c04110340c21001c3e10b48041c0ac440015041c041e4241c1c00c03c0e010742c5081c407030043e110604690400303032040d005d04800034607401c81c03a509203000650355441450800102507140c02c02e002260070a107020980651000359504418006c441126a59907100d41c0c110350810a8452003400a9a90841c4440c1140368006061032200252001d480d18030300c001c226089900449044512500c04018070002039010401151702500000b2090201e0a24800040180411035030090806800200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131774676 1250 131773426 131773513
    0xe041704140d0f0c0611150c0a0e0102011d01020403111c0b1005030706050d05090705012106030b010306050f070c08091e10030c020c030a0c120302071a030103110102 73
    0x40003d9954019000325003180c0c8039500108040004a0f000086108a00254160002c4080c805010340b00030f0f020240341c004002c4060340d10b1a2071585250541d5030701e04164a0a0b0307040840d00007560050360005036903a09600d4507250304005018403502900030b82001818404214580c698041d80100c0c0e00c0c812561020340800903a107007a080941c00d030003601000501c0c0d46d001000b4114091440d0824850307035039600320741c0c0d40da1401441150300040c44800300300000211360403401c1c603202d000e56002c103c49480e80c03112a1030103400e03441220b51031b80c4d68017001800b030781d00380025030017141901d084882c0c0c10690f1075146480c000d420102d803050642030070306402d1415942c140c100c045000340c26000f100200d15806802000c0ba1030038040980543e83c403a44003031801040100d52640d100c005040500d040280781c02c100540302c4012000e500c40d00c04081044c48840750021001c00d0400c500e65541d43c15854040711807041c48017024159802070b108101c8181518908100010032010600e441a0719010f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131775926 1250 131774676 131774693
    0x2060907081903141309321b04090518010e120301030b100e0a0911040c12020f0c03220e0f0f04050316080403110306010e041b030c0e041704140d 64
    0xb010980c070001070070000402d4603164202560351f82044960201e030f407401a44030b1161041c100300f0311040ba85050001400d0001207040c845070070350800001801c0c0741d2900200700c03c50782c003030785c402c04d10212003501480c21200c00d0040c42c1c4070b4141d85014020900320b5030005038003404180801084001808002442483c10210100c02800c10000c1041c650030310341000001040080c01c10b88180740031840a003903d04180c080c2d601120a80e0351406020301c2c40000d10300c0250400c180b00f0311128002c00540c482038004102900141e00f4050b840500403d03c5217100b000380020b6807011240318444802c0100d0307909516952544002c411000c15581e03515441c1c00e9043d8030070100c04a44c0380300e00c1c942280920503100d0180054a101e404a54a503030401c0c8101503480c0001d214070300d01051b81200103800108440068a9160026070000a200b601e96840d400b800d44550848078550f420b0004100c24840c0d244030451540c2505c1822500c1e140c1441a140d170b03c04076103100c082c064402e07840d000381080090f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131777176 1250 131775926 131775937
    0x402042102060d060303050a0801050603060a050f0d05120a03050115080403050a09050411071a090303160e030706030c020c1f05090303090909010902030709020f03011517070206090708190314 84
    0xd01c00c0212544910b8040c09a4104101588c00940664004107850411004490080c60b004100540051a1800b0032011008a41e45c00781c0004483c002500024030070401c2c0c503a0b2041c42180c003034a038850180002e088a81c164032502ea0494122451100340740c000003425001501440d1a0b95185a010819504666960700141c0c006141010441850610300c0107040c10303d1268014005092914401d1201240c00f44c941407000d41081010501013140581365504502d410f0601800e08054000000d0400b800e90f84100c002c2600c501500c13121030b6052100f04004031044901104035403400312032030801e1203143e141c01c0500030000b4a500450383d0410640e80280310080c5014040c0c500100003902810003198228002d100c0d03c200802c0c00c5015000391149a40100f01e068216840c0846a60303840030300c0c0c891403043c0f14180031300c81540d50540c00f02c21f101d442a40c00511a40c04d0140c1000c0c5000c000d44c2c4990891381115001c4210145925181c65000e0f40500e8880b00e02c40e02d00c030000205101c3e0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131778426 1250 131777176 131777197
    0x321203130905010501120e030a0e13020d05100501111005070e031605030f0604150c140a09080f0d140a020313030501050a0f11070b1b0d0501050a05040204210206 71
    0x29040c001032150410307080241a14000c1e60381400c0780c906200c0ea00c05944400d017004005803c18040321107540d225144410f05200024030b550b0911010040c0c1078201e030b12460488200c00c2c1c441c010480b003c41e1020740765009100030329100b41d4409104001d40c0c3c440c058000146400d6442c4c40104160901c1141800c0b20700800405460480507230510311110f402c4c03a0710400c0d000c0c1c0603290790341340315410100b211031080f60071061040205190300754020090048034400c130280034075040303101c0e8452514009080040a207440d90340d10300e410304100600c2c01030190364101c2c01c0c4d4046010250031a9001c00c6e41d600031014030301483d0302c4540c29041a82140180b103815240308285410000612105401541c040e40c0b01d0441048040443c1e4042c40944003c040c1c20400c520f82041071030000f5402482042d401200541501203407115074940001caa803140c0c6d65622000d45803030050000380b601c280c0000091004680c110b1a00c1d1811168043c032880ca40d11001c02c80074451008419502c0342000c1302c2d0f142a5 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131779676 1250 131778426 131778457
    0x3040801060e0402030709060e01060e01020102121807140f040504020d0209090d0f0302090a230405091b030c09130c03020a03030917010e101505060f0301321203 71
    0x4460880c0318600d0b00403a0140c0c400c0c442c10300c000812503002d02c03a0310240c58400c2080640740c2c0c204032042d2440920ba48510b81190340c01c201d118035500104111f540180f2000740b000514034a01c0400c00c4c07178903002d50031640f8021020305401841e07a441c002c0a0400100a0300e0201c1c05903124000a2000715407403101070740100395117003040034080700400c281802ea41c2032b464003034103040c005004908034041c2c42d010680011000c80e0130701605020710105044440d003a040c401c18010202d0229064410945107c2030552010b680001641000b003422541c03201c003a8003c2520b82c10305c9000070302424016002c00200341024901000303000840b8400c002540d009071030182c0c15a941d00d4005d0a9013201d125180180c0400c8950f44c80c10350303042c00340e4000440c1d0000208080f0002c0c1c51141c00405252400e07041d4800711180000322511501c3c0600f60350648505665100e40c0341040203880140c892180d038240354203003042004070104039504d0001102c0d040d80c0144120340b240c3c000700d1031441507422030b03480e821 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131780926 1250 131779676 131779679
    0x10506010e0d02240a0807090f03080d0e0703080a0f0203071a04050f0109030203070c0815010306020903010e0a060515060313110d0f24060b0d090204140901050604110f09040e0304080106 82
    0x1074100e402170800d03e00958446c0c2e4141e882c0082160f2208460159054496034a1410800b0030035035406040240160800000d071080c024041c00c4c07400000b60701c02c481e05840070a6100c00d00d50441212404d94146001651800c40f0a50315401e100d00e0300402d0741504400030b004941409420011007111903a0070008001120741070030003a503a50060300c03040b13401002203e030100c0c80e4207011556526001c461102044681d084d6a0f82c403019400c0140e115807d90369450140a04140800c003250301c650040d080040c1c82e0401c500e500c0300d90010003d1281c014035007002400000c05440341d0300142c29401918800240d601c0e1800603000804440d005010300300f50400400a11031144d00050b5141032140500c02001810080c0d0002e0740c100d44180f44481d0024061100040e1494101425081c0b0040002406115400040117841002d544c0205660364400400c8940d007442c0c0f203030503000803408160074207056001c03000d810310b4440c000c0d01d04e004585501c0320300da20000400544014002c58030003805641d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131782176 1250 131780926 131780989
    0x13140d110601090207120e1504180f0b03030a050f0706060b0c070618030605090a050f0f0723240a0509040f0608060103030810080304060f02010b0102010506010e0d02 73
    0x10009440340c94041d000d49030000494440030b10171070f100c49900080840004240c0503060320f1840e0203505a50700024110900000000100000e0001e40385454103440a50016200e035011039121207008091145401c000381c5040d030300001514207400302e41c6031003942d0300314441c1000c803035015500004045c0c41c24644041844404c0780050140c8803407213401c40d50840c0d0354a02c1100c901c0307034041112103965284202440400c0250b0091070f40840075004a0b0203c1046544480c07818100071400880e9801c080000002940d042c02100c00800c80300601d03054040440305101c000c0c0a00301c0c00540305842d418a0b10036045000b0803c10a64000440c2e02611911104409419503200080300c44c032482c81d06011000c0c40c019403043c1c8041e148003200910b442ea095a809681c09000504890592440d41d0f80008007100b00b04020310140c14035540d00d0032401c140b0000682542d0094030540d042d6414903040002c140d90004c1c80c2d4180140858000755600780900214400c01841100c007c240310340c88049059a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131783426 1250 131782176 131782187
    0xd0b0604120201081f090f1b0306030506010e07050421020409060204050f010306030c12240c081e0f0714030a0209090f070e04050a0b040507021f0e030313140d 70
    0x4036000380c0b03c13601c07a9542c51004449913202640d01c401c0d4011142c0080c84003420139401620501c070300311000503a003c842440c003194801c07910350900019454027030074003c1040c20f0044900600e045001c1403c6810110f002400c0c80c003503030048108000f8840d0304c0c0700d180c601c0610100706050300940304103c9a8505e0034640701075031241c0599405900181480041075103e031051400b240e421003d841d0780c49041c0400d08290042c0c2001c290703034242d8403909a140d241042102d82e00c51840108000070042c0c1c0030780003d0a1400d00400b1185902084581d03008032a00b261269039105104100c030185950700c201003920070010040560814107008020059444190340c0180f0107c40b00302c800500f581c1d0303110700110404108070703140000501074517080f501d02d007000e411094100001c14008581030314040c001c5411640200c5480005034812038292241c083c0741c4c8001500c0755201c0106001c8000c071104910390300d01c0003a00100c6031202e1090350310140404412201c01602e0400152910034503042e200420 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131784676 1250 131783426 131783459
    0x30b09070f230f03070c0c0b070302060c09061e0c1506091f0b03061f08060405090105071709010e071203020f0318060313050601060c05060a150302060d0b0604 70
    0x2003038400a6007030710031811440e40c048561855040c03a1034001d40401c0c550141d080900404148003907001d891000907c0e9403110006441300000b0292a1035103420000d16015028020040c5000e040102c10081d44071941100e1f185410b50211495a503104036005296100e00c18040d0703400e00801c07500d1009401002c6446010f00d0381101c840300c25840c0c20800128503000000394600003030602d0020040b5162110140d070388900e00a2462141c1c900c590f2440c180200b00499002c0000d00340000c1042d03d04e860320881d5000902280200b260b80740c0352070080d01640642c2011005941e10302c0014200c1142500070030740108050041c0c80003560384000c150780c480c115640481c0540281c102da6411301c080081600c50384010150359010600510090103102d0340060020600e2042a103500d001140c01002094020041e60b560340c1059280317800c05500b8074002034401021b85080c20362002c0e0208803403030540e003a6a01214101ea0b501c2945225a0040c0041d10805030000c0d008100003510300300d640c40c05031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131785926 1250 131784676 131784707
    0x201090302150708070f0201020408030406090305240c0f0d020c070303120c0806040209030f011113090501140111070905070f0809060f0a020d060305010f0204050307050105160f0201030b0907 84
    0x982c000201c50051128030070072078030300c000190442d0003e40d015100302c046003088106800018a01612003140609661113900302001103074150000f003041203810080c100904032542c0045040c1942800c80c00c0000c68040d18521048071f003c5141412500d04008440c0c00410240b41156141c1b0102009902c8004606c0158041415400d6007000c4500714000d034524100c09130f80300ca00f01d81d82c0208000080d0442c44c0030542611071001e610742c08490910507100d00c16400500d840d01c8440110203803c507104107420a400503400c0000402143c0d400d80140da440801c00d00f410350310718404000041c50300c9e10b9644080c40c44d80c1040f007131082c441c1d081181c4030b110f00c50700d95070b54003d948d40c185110354483c000d4800344420a000c800084001c1c1c3c0540c0a002002c489d4003010918554030b480f0b039400d680d038007520f41296960019007009540340c01c004200040c042800d01609005c41c112200b521041e0b4004040e0004801c0c4d5180720440e0320030b41c05042884002440c807661030824100c020080100d84864a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131787176 1250 131785926 131785933
    0x606060206090f0303040b0c07081201050a0918060f090b0703360b04080c01020c0c0f0a03020105031306140a0b0a0e010803040b13090905160902030c040e060a03050303070201090302 80
    0x20350004010540203520750f204401186152125594100c2d0400b0050015002400901246000519039801442640f4058074441ca095044c94200114041a5845107201d1460000400b40b90346a00b50081c1c2c0703c9800507400280b200002d000c01c4060440a035004145610700000c00c41c440341c00d54000c01c000141d00c80c54030041c46025050703042e0850503542c84440d00c4050301001e4001144039a005900c0343c4511016420300c0405910781d42603800c18208480c2c1c41c2c000c0c000e00c1d00d160422111030700e01e038034013110002807851843c2c002030031522010303084c140403880c50301c3c000d400e002894003d14000b0000c012800e44a1409040400040600b099418400ca0b10b410001420340b0a1058442c180d0b02c85001440c903286c030b0010b0041c1c0c664010043c40303640f0070f60101d0010300d10ba840c0c401c500328280900094440082c0741150608920659001048424418018040910031440546094a40c42e180b032000c140c070355100045200581da4801040c82c480001000051a4107402c404e200e14840d4085 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131788426 1250 131787176 131787181
    0x703021f0e0f0607151103070207030314070309051017070306090e010e07060c030e0a0308070b01080f06060f0f090109020c010b0406050f0d020d050d0c0b060d0510020f04050406030606060206 84
    0x4010900b08840100ba034000c000303100c08008940f1107030031140752001c803820000318260b140000240c0da4008403001e6001d60490f8904005058100110351250f821300300500c0d1501480f42d40103801503100d8003d241c00b44442222081c1c3c000d005642d0140c0b550f0035024040018605a80c1c024060580e60154010050800301c101d08503400502030907002c1c0101c8400b628445060140c1140c03503084044050f410003110313888810044d168034a0344005103000d5100b0788da5560960800764404034069008540c290702000c540305c0b4080000c07407880e030001c404844070b01c1c1d01d5407a00c0000d00c004421344082c95000c4540c2d00005040b200360b90090082d001000e0083c0305026800080104a80261094607046140300318250120300d807070800070013450310007800001c503030143e45c03145483d00382c0c5190b080000c2100710301c808090042c1e1030002030707000360215032110013601c0c0340d070b02c8035102c0c4108003c810090b90041000d5030250040f00940d8094100500304100c010341c0c0e41404400741c1f0b000c1c850741001d4000c100c003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131789676 1250 131788426 131788429
    0x2406110703151d1614040b12010903030c0807140d112209090201020a0b0406022701080609070c020d210302040f090903170c0d020703030f1410170703021f0e 69
    0x2130040140b00c81c810303805000d92908880d0b25079a0407003142036500c00d03900c07c4601200d235600b01207112000700f003400003e4174065070f15014041310524002d01050183c40008c00210b281c1c094200801d04405229694076410303801b04101c048c10f50400c0c0c21482103c045290b407040003010382c01f91200c2c0001000c0d4031407641c0d1443c1c1c0b101160008000640103030003d90202010412220009800c01e1190fa0b00615040000d1000f1344c2d83c1100c81840041e03030105481506503581d000f003070540c000350202c039106882d08001c3e8028100b24036021f0000c0c000e411001c121014001c5003d1550090025041c501101030101d4400900039445401885400142c041c0041411480c0388520f003840c5525031034441c0001e004242c07044034890014080050304070100b1021503444101c1c009001210322948001c1500d07910720101d00d0030389091070002859940c10310708001c07141d000391150004942d2a1129150300d20781d01110141014480d0b000030f0b401c803540c031103c100f040380610740001509069035541c0e0701d0f0708001d80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131790926 1250 131789676 131789683
    0xf0a080411150a0809210a0e0910060c050c04060f03061a01020a240c0509031e0c120c0a080304030506011514180405040b06042406110703151d 63
    0x44441e810001c00703104180c05103009034034081d0881c0740402100d40d40b00c40660500b000d056841c1031014071950225400c03581e05d801c11300542102d1002c894170009c0e8a0503100500e81c52502c0e01c00c01c070810603411410400d2000911480000c807201a00a10a0035100d9a0040d505030303581c4811070744245008603411500100361100c14032120144d000d42803a040076240c592209002140b500d1411001d200c0030044038080380b10b40080c1c441582c40c2c4035190302e8210100b60820401448561030003c00c000800b40c00307140411031510700704007112007500c3c0d07161220086141411165506030003452645021641c01c00c004050400c0380d1040080710701607038860410406c1c8503c0e017001000400c81c001c00500c00c3da840390000d03015060481c3e509034040c59901000070207444040d181919003903981014400d09045c10700404c5078140c0c02c5a01c00d928010741a2080c00801d202d84179400802803000741c8852904014011f4800440d04910480d940b10079100b9142c00400050801c2d000441146100d4540d20700c012 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131792176 1250 131790926 131790949
    0x804080c0301140c3601031b09091503020a03140c0315010501030c05121608100311040506040204180203010f060806100e040209040612020f0628050f0a080411 70
    0x1500e0080c038076243c2400182c100d40040a2001d480308802d00c500c00420103017407041d8070390f4614103012110f0055580c0007400b03e07030210090320010b01c41205200403858000000304100c803214240094251401c141c040381820b2507402c000d50003001c5050008c1840101203440400c030075a001907450914520040559034110080e441404450400c01082b2941c040e90001201c004035040540c50505c852029900c00c400480342580c0c802d034011215600158080c455941c805080304040c00072070700f95169003280103008803103288140e0301c99000801c503440d5078040d0f0303004042070804801100001c10700400030b50002d002c0c011804805050004409100d80780d2a0302819010349100e4148404050494000100f403100325003080c4c08104a5603543c4803842860018668a02801d50342561131041003001422886018490b00c03040c0721100d020a0303940318500010034240208a03000c0080e850036200c40c0222240a508030383c0c0440c40c1551250480c0400d84124426040540e4040c10101003000d10b0045 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131793426 1250 131792176 131792201
    0x608010c0f1107030218090601060813020409080d060b03010311010f17040c030512120604270515010308030105010809010905030d0e03040b210108010603020f0409060b09040804080c0301 82
    0x2244545101c0c1d0040310046048a5a94140c410b003580740c0d004191000712032035810131a000c0460800100000602c02203000d040c2a00d4048960b00b03040c00418009000c01e24083d20540d920104401005141000c4840c0114050418403031a070750351800840700d800034442514111104048820035610440410114001d1511100c00540040103150300790b950080c401c54a00b00c1e0400d0100c0841c3c010005c500b114138903602c25659070400292500030382e0501800b524040d0382401ca0900c1104214410000d100e903460210a542c10200e0130f05500c0c1030080102c5003d503412400c0003106100c2c541c001107041e101c003038032400240d4441032802401c1303544903070001d07042d0b0700705012202c0c01c0d401c07941103803030301602d91800c40c4c2c28a07407a40040b241e00c1c0d204452410b8007070f442d0190014807410a4200c680140400c0707000300300300c0303185402081c504c0d0722a50020388200d60304d83c3c0401c208070b401e030b000b0f02d80020080c2c44100c1901c7d043c0380c1030707050340d10a0080c100b00c1d200b1000070991030300e01402103081c001c08 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131794676 1250 131793426 131793437
    0x1606020f0321040212120c071a07060207150e100e06040b0f0604110c01150f1206020307110f0a05280818032b0c03080f100f08060a0608010c 62
    0x22802d0888900020203401240d00000b50b0704400e00c80309042003601d40c04c01410b4180e0380d03140b04146c0c4a0386414490392100d00001080003a100140c0320b00401e8901c1c6c55041200580d94403400c0c5020162070855400303034841d480c60240888404600054400c03404281e41c4e074108210300c805501599100c0b002ca40050400745c000000400c82002d0b00c110741d400103009040440c401954041854581c0c000042040f0b132695103900d070094503080c0400e0a0003c260705c1c40c24084a0342450521a04a845a0001381c003007900000030600b0180311f0a0001180341c2e036801600c0c0c6605400d06031540315900a00260390500c902c80924040c070702c250380c00c5a01d00d0303a0062100f22003401a40e44400c1070f040251a40511210510040320300c0d142030028194046403c11150700404100041008401315408030304101b095210a0780300003500040025048160040c0c10f41d041d1b40d40c44003241002d1800d0308002e19040d000c40000410000028400d4052180610140041921610150300700d036006941c801c0000c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131795926 1250 131794676 131794717
    0x6161e0c0b04080d110c030109080c010c090b0f0a1e0f080f0705070609020f0d0c1503020a0507030c110a060905030f03070809010807030b06040b04031a0405120a03020c1606020f03 79
    0x103000d0940000400505001d844c400880c6c08000303401c440750380d18103458038a0002000c03d900c6e8401c0c882c8400902840c1030460115040544000d4a0301590050880001c0001100c0302014064108140d5445044124110241c7c1c10003000b0000c2c84107410b0f48010480303140215800c12520740c10781e4442c1c80c80f039607480e0401b2481e03240c040107040c8040c1c050740c028040d02e040480740e850b42140c1c0c1000701d001d1095032440e14580861f140b050307520194036504041c418402152b0107035001c42150305c3c1c0c07501454109400113a038200b803510030b000840d019a0114081c4000148513801c01e413818210b802c00c1742562040d03828004050b88131b03c201c0c140205441030410000f511980254002e5070004103900e00090059a00c40c0414415400f58002003400d0f94080390070010004034a050700710300501110040840c0c24603540721540c5401440c10745c80c1107600466086000c5100368159903600034560100c031851210701c008902c210406014480040c0aa4210f6109400f0008129010103c2c1007900c1403e40c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131797176 1250 131795926 131795953
    0x10504030323070e04021b010c0e090702010903090302090405100911010f02030405090406051b0d0204030204110c0d03050c0c0105040c031a01080d03021305060d0501060801051009030206161e0c0b0408 88
    0x390f02031f0b0300e181000001e09040c032000b007000f44170710403000300192100c092109a101c100030725080d00070850811a03050203540c00010790702409210803298190303214840307a159864402e042c468010354000525252814410920000113841010301c03a085c1c0700d010105c6d0010304126100e100301e000d155004603012000c54006422940610f5102800002040030400c010b2904003280c1d103d0044207164a80105d002d000f50f190620540313207031074441410207192104540401343c541c00c42010a1081c0355840d00010342440195044840701d1b401c1c20000c018038a85031500f4400303520240015541840301c800b40540004c00061298141c4603404020003480c0c1c0341c0071040b80654060400c11241000c03c0400080c0c1e5100d8002070709140881c840c000c00c456041c05001858000305a105911840c0b20724204280d007500218050240da1b01680d0b500d94401d04010040e070340003000f9a00522131704900e2580501c026500910000c2d1034860100c1104080d65407029046900682c0100f611075000904001d202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131798426 1250 131797176 131797181
    0x6051c0c080f0c120a0b0c0a121a0906060d02120406050603030a052704050103060c121b050706060b0c0a0524010b0903070f09020a09150203070b09010e010504030323070e04 76
    0xc69104e08a9010f4100e139039401100c10070540d0032540c400008103407240c5050700009060310002082104000d541c0400c05507607064070101030600d004031016408a1015211001111807402c0c032030300b0540d90381c1c5404000c04026503081b5805d940b003c0c5000d0105019140110441c1d80d00c004a41e1900d0030032490042003040c03007444502c4110b19403a107105c5505a40ca40d402203078020b60181c680095485400b40c409482400c40c207501d6841d00785801602d01e03c140509040ca000c8040030302d0029107840c114a004c00c02403071180c2003109440c0d07012801c6114000d0005906001e148104103640c0c06203e1181420740042c3d00e01c1e14441c000c0850b50050210100e00c01c05040300a100408550610350b07600d685445d050095003200d10b00036000214800c059412075464001030244034855544010401002900c134014210028aa9884000894080c82007500100402d1401c2e05c000c00103800c05250160042074615149d411554411019004102c400d1014a10480998032800c145c03401c142e041100 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131799676 1250 131798426 131798449
    0x1080105150915071103060103080315030a05030d0606170103020f06030405031201090b01020706090f06030b150a0c031d0d0201080702190b0103020108011a07031206051c0c080f0c 79
    0x10220510050500c0c1d512018001805083d019006a8038143c030b00b00008480c401c02d00c0c440c0a54007aa00402c001540075003265889003d03a9049503001516000203402c204682102810340e12011444c071102c444950701050072114aa00c07448a15184d104c2c18a100200910020354000c81c11121141a414a08019640944100140c6e482c00d50880325070141c13213000307800049249907188101c1a495030100104000f03030000382048082c10b03241c4804c4510941c0c5d1030281d8410144c5514040341d207a202c64ec9403030090040901040d031943d010f000028480b2507034441c250006032081c604036140070401141d190030414080c0130281e0620141c0c0055030f036002c0c068060342c21803240301e9940d03103a200720820701e0442d14480c1c101e0480c0b95245d400014049141030f041035a480315414a10062031a0080403103603074552505080e04030640740b4545000601090b80a290003070800d00075084500191404245c48900c43c5000d0903000d130302e54807043e0703803040ca10011002c1507021500e00d400c6450100108075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131800926 1250 131799676 131799709
    0x40e0f090601030c09050c160b1005040b030709090807050604111f020a0f17040e040203010e0304050a180212180d030e030d09060e01020408060a050702122d04080a020406050402070201080105 84
    0x10724003e0584500d05100160a9040c0c0c9c040100f1018446100148064a0300410044a06100c0f1324403500003ea01e511081c0b01c6c07042e0080d80e400d041ca00300404107043d22401c6070000180c03007803440d16080041d9441e240751032141c818002d00140308903064030540300243e1495103900a141e110b52075a50318581e0800f80e02c00b660a0031100e114800c0d06140c400c0100050181d800c2101014100303031040c1801d656480c050300025030810b010500990312480690b100300c9140f001100c0409035000d0304070740284615088190a81600070401030314030000980b441940e2000e0b011145400c11f0028105c0071103640a41e4100b0f00d4000700303c00e1400842c40e400011038940241c800190303094070003081508990007a8014202a0440e50402404000e40c1c03140b10b0340f050b41070024219480d411441803c00d44600c94002414500b90302c0d41c044a081209101940c4030043c0c05c100da07603039445044096035055030b140c0c01c91160b400c180d00481c4a08240c002e4400042d4181c46008159003001c0c100848085502c0303210 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131802176 1250 131800926 131800951
    0x60d0213090c0c0b100308040e101815051c0323070309030219030b1605090a06020d080f010b0301060f110105180f010e06010311032812050c0d05130b040e0f090601030c0905 76
    0x12402c01d40c2041d81c8003000c2c1c400c181c0016110450f10140c50354180941c49144201c65000044540020800341440160350604d420410d80c407880204203402e0b000d809180f20006004101c100030150006036035010740c0d0007240d041e4503003440d080c580f40820000e404004c0c520307007645010070990041d0105c1d1864940d0300741400b904040070a004210705012a41c0f204005034400c0d00940a25600000003079000390100d0003407050303581000e022803018030040c480c050400c00310f5400700c207005100b01c0e400c41c0d44400b5540280400c2c20411015078000b07440c50a07407403031402030b046007442c1c0c040705125500900400002074802d603071175030303c9440c05890740c02c0c07089405000700100e91206060f250250f10600400c100e280b80101d6035070402884000c110310f4180144802040800d80301040000c00a118400303500e800b541d515541c08440010303441070340c0300c84500500841c0100b540f403a4010303114840d454042044445699086440d07988400a00c4090070001031410180444107443e000f04c0e6110b120080c45 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131803426 1250 131802176 131802179
    0x230702060304061a030706020d121407020a031101020c07142403010303120908030406050a15032301110a0c051c0f030501090506060d0213090c0c0b100308040e10 71
    0x4159603034011036003103034110f44d111501c41c802c0741400b5044810413016001007030840e090003406176031080104485014810070141520503075009400691000c840c00300c007030205080c0390101035620742d0707070807000c501084104200d4100c1200510945070480300c18002480040c0c944200c440358500c814401c160006602106002e00950300c0a140c90408446030b030a554a41c950b080081c03003e6102541c80380c2c1c1d030b41051884000b240254060700c1c0c001d900200000f03941d4640c0c01c0460003c1a00b11b0217480b042141c40400003c0c050484e04000840c0b0005403080c2c8102890000b440c2210500c81c05101400f034203101c2042241d02c0392156245541c480c0c801c448410300d1008485c000b071400348140c0d0002071501506140120f41c9401024010680088103010740d09014001401a01502422588196010406070346055056546200409041ea82002400700c568401880520046030a81307180e0b0001c0042014000a20040c0d0200d075040301c0c40a040c00e04021641d1900c20b0090f00c01c1c010302000ca00c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131804676 1250 131803426 131803429
    0x7020105071b0b0604111210060f1d0a0f0603061a0408060c0f0c06040b07020d1701050d020103090b010b1306020304050108040f030309020a1721040e0702070e040b070908060403230702 81
    0x10203134081000d040418a1034590b23403d601d51305140d048007081000b00e488085200d0b41210412070601035288880138203800b0307840450207070010740d1302090342c02988140014406130558040400d960150070001c41000b16100c041300b9904c41d61082100c1ea9005000180d810080704000d0489281c0c0714000c0e074a4501c0944089262031b20981e82907950416000a026804e9010025a05d0800301801d01c0c01c2c0c007034080a00e200500c401441030324000e0740104106811a0320039448202500d0340701c02c2ca40821750311607178000d1040e0412001c031440f60742d0608002c40c1c0c01e800002601d045410503511005a03945582e03c81145000d080021001e054540c48550b0069559030a090060201810070154813081001010320b032680b040f140c0307808103038201d4070400e4002c00c2e082104d05564844005060a485c1d4010803850070b8250fa000b648a0350459060204004072a9200e40c09420656039081c0c105448004850719400256402004140e80c169000484c4944800008a034030350343c088181070142540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131805926 1250 131804676 131804711
    0xb09011107030b0a0f090c1701110f0a0306050d0b04020d020d050607030905160609050607140d11060606180405090f0f070503120406050409051b0c030307020105071b0b0604 76
    0x4008650325401e241c20405640c4c1903104410072000b607090103001e5900d080e1144541d005142c042c020107298141c00c01805440250040403c050184c0809562115407080020454101d0ba8124000900b0030030005414680300090f001220303007008450700192600da003080341110844100300c0c2c00c56858440900420814030282d031007100356441c04070b81082c0d10701d482818403910807988181c21820030014044035074884980c3c816100141d400c107603900d003c0c0c1403901015203081180314042c41040018151540d00c804080d0035203000d00102c2d542521070b4401c02207140120800071700e10a4250480c0c04180c60990019604040c070341c0b0640310440e0146c0180c03400d05801c18100c0e1100da02501c070400c21420700b04466064154400c0c07200f4181070601900a20520651082c1071b408c03038031440450041d502e541522000c45011031443c83d41c8802c6898581c0e22034008549002c09540303084000b42182c1d0007002d1341d1800903080e545100c0c117034100d0b03610703c0304020025000b0f503002541c40c0b407006201c45001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131807176 1250 131805926 131805929
    0xc0b030403020c040f1b0c06020d0509030d0e0102030c1909030206030703020c070803090306060d1a1918080a05070807151401080f030415020c0a06031b050f040b09011107 75
    0x80e40601070f00300e0003c0a001c01d5807104e200300c03050689055804400c002c0e912a1a2400d02003600d0641d20515a40c20104064040d8509881025241100744250f40e0b000000809903041000703018450003106038107803800c0b800704035107064011f041040100c0060700304500705405054103051021190b0b071690049185500100d440c240880e9000521b80c081e40c1d000c116050060284100841c0361842c0a40401e4541c034010300403a0160011300c00ca00100583d4002c00843e28015108e0754145150000342c0100380c100000280c40c1c51850500400c0e030251481d08244491b54024101c20b00e044004d400440f07065000380000d50328450103115100004841009202c41070312042008a1904481003460313880c500182e004007044da00507141d54141c040301006075000c0760b6400140121030351441900340d080c40c40e440d007020390000c201140480c104c1d070150702200140d100c41c0c0045004103407503107003621588181d070071014a840045c00200903c250403401400034690600d070082c550032844203d245084540d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131808426 1250 131807176 131807183
    0x280c06030506011d0d1b080d0206040c1502060708071106090a062301090209041d07080717070b0901031b050d0506040209091902090a030b060a090c050409090c0b0304 73
    0xa0708140701c5a50382c05a1620350340c4100f6211400c07030803010300000380240802031004082e2951103800c10070070502000f50000030000c0c181514801c1a02c03032070080d00c50208440c02c0b154010107080c003103440c43d1076000c15200c42d1855002000d00e0703200c094058800210080c494420031448500320004440c081c484070f07008a40c400010030f50200e02c0d281c0002503608000c4107050782c8030b0b032600300c40f805903101e03034030300d044a1540170011798420b4460040340261103844100c441c1c2040c4814480b03900303400060001e08840400007640d501549910610f07a0104003400c0319085540414018845055802c00602100da0141000a030b80d5026030f0070000400c1603010403002041c000301d12612000b100340606540300c04100d804520b4002c03910001103c124014200e041d009040402010b403e021a0381150030484004011a0038203685c0c1c81d00100c15001160154020148031000052041043c09011911446a1109804c0500344400600140705e40c040c107550034120400c002071030b05005001140110702 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131809676 1250 131808426 131808431
    0x8070608010906140108010b09040209040603080903010f050603100e010b0d0f0317010f0314150126010b06031315110306101812030e040c030207051e280c0603 70
    0x9402d510380704890391a44641201460700001c007405aa20164190540390044200d03034440c0c2402d0301290090050118150700f0510304030b0003106000656014022000003100240492224a04d011064500548065405500145030004004800c0e080790b89180508000007400f04040800030301c520034661000d840b40381b84000d209060580c801c04009210405142c40300442d4505040302ca100807041c440905031110400c1e088520f54018410030100705840c04031001e495071142c680080b103140540300105c00304444200e10f0b00c14641801461802d013002003d150859564581c407003250008194100d460849187d60305161b40080e12034a0a11010501c21540700c3c40c0c10018890720041a803008001d020303d9070000d69184000c03084210640300d61200c600c1c0c3e5041c05140580c0c0303010051b0090f075841810300e80130007180c980c140e01034980c0c1030142045a040a1115480400c44540c131607400c0203e13000715008120b13030851b9040c4d0320b114420030a8500d081d224107480e40003d5211507084640040d4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131810926 1250 131809676 131809679
    0x130b0901032405160302030a0e0f030d0605030c13050c04030b0f060907080912090103020906190801061407021c12080907062105070309020d030c1a0105010215040501060807060801 79
    0x500c00241444503000d90008005600b4841340d44400c40c0108120942015000000104451000d81140301051110800c48502c00180c54042e9101e401100f10160a903142a600003002d19002518024000c0064a002103e005c60118500600030007482418191420400080010800d0740355030311414102011030306506040e401c0002070f01300a00421b040060010a00000f82000304040303480b086500d054550761042040180c000c0d000d10728046a0000d0003240c0c9058110640005002c00140c90350752041c26070322185c095440c9058406c003102002000c1c0400d000506200c41006440c6090070128864400c055540ca0100701181030350400151882c81884150841002480c0161100b41865041110b006001c0c1c501280402c181c040b0043e21940440c101c0ca000b6071015072042d401030600612030080e420003412103803000404590a98548001c071b1003c0a40b051801d041ea10142c0c05040c0c07010170389003810403120004c2d0040d6015580c40c00000396620041040e00028003260711344413900d6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131812176 1250 131810926 131810963
    0x1e0702030c0d080a080423010f1515050a02070e040f050606030c0102030a0311070c0b12060409031205041506061709030405100503041a0c18010903020f130b090103 72
    0x1076003221074068082441d10300c000945a41c03d86900c81e0282c0350034220756071181442c031401c41c1418500035034556400300003105060190003d0500d80c1c000c1c1401d0040c1d400c505025203d0564030721544071102c120101141c1400d10400c018490310000e441140c10141d19840810704040c1c0503641101d2800545042c1c85c1005011702405520520131805080b0000410740007175140d2107806c1d04c09007015512501c041010130000151981e044d006045a00f1464964176220880c0d4001c141d1500441c00e9480082c00754682402056000c0380c1c159180903112400e42168006080068011640f6a00030400e070b80348040180b00e410010129030303440104c03c968100b01450703d288040d0140702c007034108020900481d101d91045440b03c0401e868840d50700e03540d0b070030825480720f0004031108d02441264144140106013002800d08138001128940b0035080f4500103642d05e8106100007504521f0050204031540b510b00110f549510700d00ca030100341e01d03221000042001800341c104903a00b086503200001c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131813426 1250 131812176 131812183
    0x50d0b10030914010c140a090308030f01030b010b09060714100c1e0c020f0603041401020d05010609060f02070b0906220603181e080405041b110102040b0d111e070203 73
    0x203043c24840200b2254140c02d000600c03c1540c4550f0420241002906003800c07441901e006004640001c3e00a403a410a0a282844c50300c003807005a4070660840000b00c2c003083d680c805c0740c100890090402c0e03d08040c584e2005501003000441381c199008240341c1d0603a503a2103001e0801c000085030f407100c2d40f5500c0d2840045c800c01040026808100030250284010b8981d90700700794020b00100c903025101d07a01d40c0b80051406c4601c845060301d030b500101d40140403001e15080281138601c0c1e034035034008003900ca0004442d4003080450400069002103030801c501e0b5080070003081c100b540904900d24104c00b05001105820105481d50040c00ca00070701000050350501c511402d41488880011072440e454a402d4000c0e40e104101c180010201700780c0200f0400001c00b1200102405401401003c0c03a541d004500381a000c00c003c00407611000803080b50250600c206c400b80d5240c0c502050501c0725652094000b00943d05500300804d8007004078059000c580700710310038100001e59102e030781c402c20352060600703 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131814676 1250 131813426 131813453
    0xf24051b0705100506061308070602011d1c02070902040611010e0f0d050306011701030501140f1003030e0402040305030310030311010c05090103050402030c1002030a0201060f08070501050d0b100309 87
    0xe10041440800000b42012881d00b42d0741c50f1040011495403608800110103102c0c5000017018075100200025140c0380200e042011164160001c106121451485a501d140744000b080e0850b001441e042141c41703848020058071103105d104803002c052301c1c0d40e1544102d900c640c200c2408680c004803003506042090041890720b4444001400c40d42080c06407050f5500010118401806404000510103134801c0f2843c0400302641c5c5038201155075a82001402000d28113580c032500302c459000105000071014130700c2c0c001c110300746078491001e2451302d04850389000000c081d076215800b000000b020900c10406140128200e80458582c03e203075140c09046c0c1c07071a10200b0015641015101c18803590440207940306190282008600c5941c0d0703100090620225012680d4062020200c00000c00e03030000140694135500d40080205175103400140c0c9014180e8440c00c85a81e001403001d020f00d521070030140280c0007030b090000c640420444001070f400c09590f00d00c000080d035a60440030a00c0a10040c002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131815926 1250 131814676 131814721
    0xd060504020a02210f0a0f120f1406010e0a060509030109120206060319030827010c02011d010908090d08040905010b0910030c090603203c03040f2405 66
    0x103140180542099007903000701e00c04c4809000b101402e0412080c022303800120300c070a0f044410064035041c61010402003003100c0c4a07045440b2907034001507555000314007500701418001d002124540c80d0841c12501a13002d00c1e102da40554803001c020000450020780da20003140f59401901042c41c140081c54a8510480c2080381c4101c0310104440c0400d802c00283c58010080081030070134010281d8800311125440c200301d4100b07601e410142e40405a041d88190005890300718200c44010010f1285401d80c0c03201d50f000340c629501001440158540344140c5101144559559410036a80710460381c1182e400342d103c680d010300b00050310343c954541030358490140c21141c00c0402c8040b40c107100c000e00750003903400750f003090580d01c0c0300b920700f400e03244004044c2904100307400c07540d82c0580340c00d251060012506e14004006002d6492009226001c203c10324103010254110b0030343c0e8480c1c0750385602c66006070b0141c8602003010407540c000090b0300120203590701c02002c081064103103002039140a000310043ca0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131817176 1250 131815926 131815993
    0x30a021c02090c0a0215130303110f031006020d091d06120a120e04050403080f04080c010f0f0c0824060909010306020310050f0f060c1e100b0f010909020d060504020a02 74
    0x11241400c1007c10301d0f26150140303070001c4d9003a400c0302d240d0450b01c600c2109410507500441080803030311100105005071032a9900b511884401a401a44d06c0041401201c40603170840703426035400c07180030064990210004040100850b010f0f00307050b00b00742840c08107076804070440c46500d0401350001c1031101c03240380c15581080705191a440061600f00301500030707404207040d0001310f01031160020a07204010240c0c4000c004010b620341040700200500480010000d040c40c541c0c404540c0550480e6108120350101d41c00074041c01d40900486265020480c0d90003402842001d0302a11000c1c84a0701952041c1001a52420440b044503070701c080c50380c00280f0645800c0c000024a4031441000749846c4415940c0540303e401c070421003400e00d071241e151004490294400d030600780000084a01c1462031010042210501ca10f0911000c100701c0515a40440c11507801000208960360007400c16140d04580011a10b44800024050f60302120682005922a8031041ca0202074000c001c4040e03150031101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131818426 1250 131817176 131817181
    0x810050906090a110a021e030f030609040602040801020301140f150d2c060f100b090f06070f0c14010914060a0c0b01080601060e010806030a021c02090c0a0215 70
    0x8041010007094035014044480100324021001d1304070300c1c03d144440302e0694442c803144e034000b5502e091030040e44034260f800011040e0002c1000c0f08454101002003681451595244207101c00104054012501240d00b000002450031080c4061800ba02a10600d10000003560b0703300401003522803441d52003090f8054100c0407001240c5e0440d8088140c4140c04950307908100c009045801c07440e45255400801e216107928250307c0031581c0c61044008004100164031008800d04103510307507005044810504000c00d0420f1302e00441c2140403441c0042c580e51a0001581e1000503c80c1002d900704c8a0a0912030244102940c400b02240040000c1c42d02080c4a031030028000000300d25020b071180101400608444010b01c1811001c0e1401e030000b4805545594591003e55640c0c82441620b0015080e08000b03801503228100071070081100900400b00783d04613400b0441000c0d2604074001c07104009001180058031403070310b0580704825010300d058840c03e901d82e02a08141c030b810507d10006c100b1008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131819676 1250 131818426 131818429
    0xc0f0902120a0c0302040305100902180f0402010507140d09050102100903080408031506040303050901020c04180201030f0e0109030201060512010b0913060603020603090109021e031515120d081005 86
    0x800c00d92140a080e8007043c1c01c1c8030f2020540c02485140c00150840c01141880c030360b1002c164001854191098403003a80318440b5981e103088071070301503440342158000080070402540c40342c006442000d011f21391600c0c42c1007000d5113903490304501c05014008102ca04e4810003c940c0c042c070528000907e408418031001c1450b41e401003034002c0c02440100b95140c08408a07507840c41c40074840121800180c040c3c1d42d0346480c0e06018049401c4040d40c41d0040c8101580202a800c0500600b00741c4403a03000041d01e00c881c0d0703600540c058010840c40c01107803641d945c0003080c4620300340a651443c0d03000fa000040d400d4240030510104408814a986150303040c0040c070b6a441d1100e80c0f031254440c01c0340340e400c03a6400c183d13b02800508074580c0301035030100303011050000c014419480070060a02c21038110151300b4480201c0b00d008405075440a6141e0004013220a104644074986c43d0702040c000d0410b0070300c90300900000d94105551020010329400034070400152074100e800e49801c031030310720307282d041c264903040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 131820926 1250 131819676 131819707
    0x31202030c1b01060506070302160f0f031e05070b091503090703120e18010509090c09070e0a050307030b0103052503020105071a0109020d0c0507020904061d0a0c0f0902 74
    0x2000d1078280110319402c00405042075100308082d00c0c000300070980c3c074059828025174a8080748101c60322000e80b03400000d0115a0244100300320740e4030310f560003032003461902d4410740070310b190005140140c1107011f8580011400d0000f6009003184144481c0c60724004402d00c43c403001d110100c889560390030411300004050002e540001c499104512030080c07681d82004032030b144001d402030703074200245040505501703400e911118181d0300190b80480d041da40d208800c5a0b038540051740c0c150810418400301d00c0c031a200307030454080514050301c103078001da5851010900e01442a84150f4901c540040140308012003400446100d008000c0742079000b456048a94001c54070702c0c40000e0600c60000b502004000b02d4040b01e10f91030058070003000d9035607501d070341c543e02a51000001c004840d00d0050144c1c000750141c8241e0b9001500902016016550355a0b810002c2c8060011042042c640c07071501080304104204c41e4440500c60200c3c60441d81c40e02c41400402990742c0c0005121a0040c007011604581c4403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 131822176 1250 131820926 131820937
    0x821130e060307080106180c05090d021c0f050f01050709082d06040302010903020c0109181808030c0c011b021c200102030f01051503191413031202030c 67
    0x1110603501a12400002850901c665000e18095400c1040000d40354840002d00401ca1041740300512100c0481d80003241c0e184a00044140d10401c40600107000d820003010481c04c100e08546620200d00043d12012207103800003034102c8543d406490381c00700108c428001c858202d1618280040301d2410504119240c11205882c1c010007150005003503040105081c0e903800340168a0180e92450801d418000d000c0c0400460583c00b511980064401d0703035203d4580f06044800220341600c00312003c1051801a209509500c0031480f601400c920120b00008000e42c041d49001408560700c100301201103003500d446020004040c1794800a181c41503402185c1c03034501888611900300b10721140201542d584503000306d0100c07410540070050b60b55200550007140280700090080320185e985d2810440d2061605c59458140041440031940084240b500388c2ca20740e00038280030484521804190301a03110407201e45001095101d488020315400040340110040941d40561651405483c515440d2051 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 131823426 1250 131822176 131822189
    0x71205040305071a06010206091605150f0f0d0501090c0c02010e011e020714030105130201080a11030a020a0807020f0c2205010b03060a080c010206040213090c082113 73
    0x2580001000c05104404807103a980d0f0010f007800440c4002c850400300302200700c4069003d1300c110b10200d4007507800015640e981c0c41c405180003440300e0a100c10700c0200c45000080f1098900248200d8055040803005000136401101112703888032003008035201a80c0041e840080214a480340b9000300541c40400d2180710b94080c01c0c502d0003107502d0401200c4410000407201014071034802c040859a501160303200403141d1200900861030b1602040500300c5100741c40031508000d0004114005500494925034850400d000c0000d01c03500710080c002c100d0b40101c0c1c0460023141c3c00104840c0ca0f40c2c000740030a4208016100500c404952101a84c3e40d031402059000d1090f05c58226211000204e005000f00d40300102c2c00502c450f59560750b004913075810945020744115000306010802c20400200e14003d184143d004107081d480d80d40a20410030740c40c0c8140d161884c1c40d0030302100860904440d03407000f4000c0500034810180801c0e888484000c5510080e4900d4500f0860705840d110400900004c2e41e24 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 131824676 1250 131823426 131823431
    0x11b0309050c010e030c0a06030e0c031204060309140303090709181502090312071203050105120318040216030207080d0e03060115020f0712020108060105040303210204081902040e060712 82
    0x13040340042d02c0c1460303172000c0903440b802c1518041902e0f5410340140b01e000140304200e480c076003141010161103103106240070342104800d00040041034440d81084d107003217009256050b40b0104190a640c19640111070420841d0320084081050002c2445011810800103030780405148055407500d81d94040b280807007a5207900481c4242047e41c060120b0a02c02c026060020f03503900540c50804082e241c81010180400d10703010000401d41840039501e034070140181d015500e008403581200c030610601703900080e001a802d000035070031800414200200c030350298005001c2030386442e11552034450111005d008008081c6908409078400044c0c403030650b0840081c0d040c80c0d408203c4100c4c030344680c0303140144051261070000100c030100b040600c02a41e000703036203449040d543c00380150341c01d1080e0f01c4004c0004440e05270219040c0002021420241100c0c13401618099076061064985020500200e4183d0202c2240c4030841c0b42c14419020343c0030400d07000c0c0c4281d180c120b102070680c501c5000010742054 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 131825926 1250 131824676 131824697
    0xe15030a240f0912030204060c0b040501150602101505030304050d020f060f0a0905030d0512041103161811041802070f0803071205150d1b08011b0309050c01 69
    0x2811403407000d48004440301000220405540701015104803e0152a03212281c0d442d6001580700b4004c980c01d40d401501c841000740101d41d6150b0034140002c20a0b903203950b80d02d00d070201e241c0c0c3c0c05411400403c1594014520104014450740c1290518041044071006044042000e40ca02006039012103104403880b00d200d0901c1d001241c1501e00004a450b4881c1700007401c400540780d10400341544c20680e0380c864202a1301d076001c0c2b554428841c0f11040100705c060016121131034440c01e089501134032940c0400040581031011901e4100c3d046119441c034008060107110300d01c4068500356a41d81001400d020319a81809104950b100e0340c062a06040718800e13007241040090b8046076141a031008110b803840110342080300442e0000d85480001410f0641c00403041071103230107401d018107610440008101c80b000e00304041c4940e500404c9441c04007202415622501000c50480200a5100085001c03000454103103d401d9081c801d0006252814a84402040000600311300300c0c6020700b0141c042c0e0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 131827176 1250 131825926 131825963
    0x109120c0b03011e270906180b010603141006140f04080304030b0a021c051e01091407080702030906030c0415021f06030b06130e0d0206010e15030a 65
    0x1682904484040e8200000000f14101d4845182c1d02c1c04400c04001c61300d058441000f0729110b154190380342c001300c2c100310320340c02040030380da02640005102e5103001842c01d99203524588161422032043e140e20041000400074103070140100d4103103802c81c0e0b405181ca860b004214440b18217146c0151020031900489140c00004200c049450b002444c1e1403031501c3c0c0781d80b54941e5580c3e42c0700b8082101c003160000301103030b2000b034a802600c0d0166103109007000498a1232401d0001004020880f4401d503003101218450b5030044c00505019100307520303012940c0c085004500c21003084c003902d0f0104200e5803404000000e80c1c00300070755011100c101c501541e26103922504221a01507908206602c03c1901c4110346c0c455000201c50800c40100040b064140003030040310b000b00e0300c4501c8060440070003100016114904642a050410f440042c000f640c007007285c10b1245081e00c80303d007070409a484600144084489004d000c1c0d40555400c00714060008000e0200346c0303414020310014610280d0421140360b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 131828426 1250 131827176 131827193
    0x30207031d032b030623010f0201062c0705070c030308191d060c0f0f03060604080316030e042901210b04060b07030503060d08070206040b0a0e03060402010912 70
    0x140c80c40c3e14500d25000000c5141d14048000c0e00b080407a2400724000b480050040c08800d02103598400c0d40d4903200c0c00f80043d03070340c1201483d9031411075513191008110300c1c83c4e40c0c1c44480c00ca58101031001c4032290050703102c1c61400c0c001c3c005200b070140a0014100090f17400450b601900d0b81860400d5042d210701064540c0c107000da00b0070030760003410540e403035603040f1101203a1001e01045204441d40c90b2210324038000c0510900821008860080080a100e0741103030004681041c00507044c513207003c0d41c4643c8607045130048900d240c2c00d18035030700e5440207055108084400b1202d04a07410840c10300c0c0500350010800140804524403110728001c0d40850f0300a02c4d1804e10205402c41001c48035510000804c0201104007101e44030b10715103880803a84910203000d07510f1503a03040c0c44492441e200c82081110f10540140100d07090340d17003007040000684400c000340005000604455484841c0c511f4040c01c0400103418a80c0642e020404100160380c1c400d043d50204c070041d4401c000900c0c00c0d800c100a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 131829676 1250 131828426 131828443
    0x2010201180f080a211b080c0d020f09040c03020705100e0a06052205011e110306010507140a08030612030c060c180a0308090a0b0a0e0415080a0c0510030207031d03 72
    0x4045031008080c07001820350303005a000c500440f2601c941c506c07070b4018192482d0106a400c215415014081d035400e00340319078001c10946144a1005091020b03050010b000d0300d1080d00d034200081d4022400300c0801c501000120003030621000103028000c0c1c00586035903285091700c000f50010f511740d404652207039440311021300c05041c0a250b8a044210a04100b80a00341003408040340c0e400e0070b102441450241d205000030303004d40c412100c0c81c54860100440e02074012a038103503009000d00c5040c00058500300403a180b032078480c2c0c043e25100e00e405810828205100340480301c0395081001102c070192004a19954090b01440c0c0b20b030340b18a010510380044121a0854580150404d107001c02400114405000326a0046900ea860a510b590003140e5600821014601150380c420f111a007038136240c1c20000e1810540340680c814140e49403203942ca00300b002902980e0b0001303104801d0150381080070a0203c40551410709500e0310742e490740e009150218201004000ba00303500c54112403030f80d051000c1003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 131830926 1250 131829676 131829707
    0xc0d0f0314040b0f0601020a1109070e090a05010504060609180c050d0c0e1c030c080a0302131502070f120b09070306141e1e091606030902010201180f080a 68
    0x140d0514180c83e01c40c2150710252015500403004000180480d8800590316904907440409030846d442c1d00b01c00e00241440c040d1101c1c0c02e101d02c08503a000c00e9111400c42600c80d0f6030300c3c4000318a6515103001e12040b139130a0b820000801286040034099212800d0300c603c2c0030116444005150a000b01c02110b090148200000e2814140341c807010700c1c0f95026003c00117031401140c1d00d120000012080100300e40d0410801408107102c8649100850401400340c81582e10f5806c01528000c400d0302146d00b0600250003a050200b101400c5101980e8100b04c2e400c05003400a40011825007000000203688040e03480041c1702e1040c00e400200c2500007441020300541c0e128909005000401c0920141100e040740c0c442c0c840e02c02043d20303204d01d008001007240150740c61000c0301d10803c003203111134034000c00c01000c0740024490200d04004483c510310b20701c4000e180a5400080d082c00380c1c800242950110103d660107000503d0101000c50320103054103190b103911500066845c503000d0025540103100c40041c2e07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 131832176 1250 131830926 131830961
    0x106180503011e0f09020d0209070302090d0c0e0a060609090c17010b0a120605060a08060402070b0705030a0f06150e0a09020a03150605120a050615030414010b01050c0d0f03 76
    0xa0300c109140020030080310a4584080c00404d40300e40048084406450780a544007121480c243e001d0b04101c0c1801d900b101e078600c0c0142ca40030002d004191668840d050890b900721b4820410006d4240f50494103030495100001031284034030341714004000b11303142c6c050455120303038a83c18105818003956007451041c010350000005981d5a0042c46403940102104201064465201141280862107002c06452000307058a080c50b0300e4540403221080b00502007a04141c0c00c100200216480c481034500c00c0301556039803a560324120400c0026200e4091643e200c2c1c0b4100b203400d0040c410a03400500003041c1c00d04e010f04581092000081d07002c4420380c420a1a40d1002907843c00d0300d64980c122101d05800c7e250f414107207139a10348003201c07148183c8400c00405202500802c00030700c029000203070005401043e041d080a84100640380d99803040d10121002c0c1c0c00184a15034281086c051084450002d00700642404080c1c0f988a4540c142c0c50311102c108500b101d0780e03244589c00b0b5030201e200c0500b901903d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 131833426 1250 131832176 131832191
    0x7060e0d0e0a230d050a050a02011e0c110301271109010b031506040503011a0a0608070801030b0403090f090902040e06060607080310030803190b090f010618050301 72
    0x5a4482058104440005041c5034800d030090a12140e05011110250741094003814081e5150041c0c2604505040d130042041d851600401e00030401822040e000d81c01030010700e081d5200242041c04444803581d900c00317600310283d0b192504004200c50142d00560b12480781000d410019004100e86144079114032441c00c1e11191020711000b802551503c1000d00c0b0981041807400c002000200344110401d84d0400c2000495040e4408210020010060b041508154aa50000f420f5800140803600c1c1c1d1a42d010001c8030760314240a0503802400d444c03c4c4540d007400c20381c2e4000c040752414080601102d003448003140c1054070a0b10100d00501071020083c200310384502000001c0d050b480b8069228609258480d1800d01003c140e15002c2d40e00140340500d414035940e0380d400303242c20080182410300c16107400000070410f490015032240c4074912200e200b035942901d0000458082d001c0060003284d481081000440916580030f0541c1d03e03e0800c0099001607031785045103144a60005901542070080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 131834532 1106 131833426 131833451
    0x31c0e011413030e100c030503071710090c1812050a0c060306240c060203090a02030d11010c020609210706051e0c090915060706 57
    0x840d40007414540385100c620300b1038000e10900b806000c56802c250384146100c0401c402181d0024002c00c505500410800d40310301c00800b0303c171300003010550503401020600d0807002c42160030651480c00c91000d4030320702000d101e00c510310b6003001324042801d1b00601d0290f03186d40c0001d5013007032510310381003032203070350190500081e1440c0c0035850188001c906240301c014040c003035a03100890428584826003485c80044195517850011424a8411282d40002c1e03036207009411000250f00e81c0c407034607402800c105003414001c1d411300c03500705940036940e0050704840182d000b14008001c1308440d400c0c00c3e80c40e254115a001c0f07030b03a0044a071803078042d041c05c103030020401c05029110b414a10695030b0041145d601303036030b12401d000a9404a40c40f51840184140d0300010a18107281098a14004a03028510180805980c41c0784420901010b407030704e4099803030994125100303100b03030300a409 = true := by decide +kernel

theorem cover : BRFrame.Cov 131654676 131834532 := by
  have h0 := BRFrame.cov_init 131654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 131654676 ≤ n) (h2 : n < 131834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
