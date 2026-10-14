-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0429
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:45:56.137874+00:00
-- url     : https://prove2.me/submissions/6fd7e66d-a597-4f17-8212-f73430074972

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 76978419 ≤ n < 77158275 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 76979669 1250 76978419 76978423
    0xb15030a050106030504030e1908030d020d0c0c080d0b0409020a03050c0f09070e060d020c1905010e0601050d0f02121f0b040b03071701060e0a0c03150b031f0b031512 73
    0x809543d055555980c201a8523042203203050624000c2d1454100300b440001c0d610100b0402048000f07031405015072160075400724003084541c04c1c41c0030018080d4032071200000640714021540194003c500002d400b003c5030002c40d004042c9650025000241c0d1a07010050040000b407092041e141100c00203105540b400511042200c10ba03401408683c5801c0c444c80c00c0c6c0340400140098021500c001418090040d16013450440c03140f5410894054182d01e210500c400ac0c054000d031192070000800d1254035080c0883d071803094000024000300400300b907010456070744c1113036446883c0b43c40d0216a0a140c2041170343c3c034581c1c034400b0549111803504007082e1709400c00b40158000c0da10003c029004842c40d0071004c01031070018040c0c20035075560f19031011810248195246010320010200065480340c11700c005402c40e000112821000d0365054010400180c2000c1100c0d8002080c0da40c0c09810103002c2c1000d141185203411903845480d0202c100107010503040545001003030211025921000c146882d65 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 76980919 1250 76979669 76979671
    0x1006030b0411180a09050102070c0906150309150506030a050a060f151202090402180103080301090c0516030311041a09190e040f0f0b10090c0f1d03010b15030a0501060305 75
    0x280460b8207100c00952440b40c264403840e41c11b0700942c009443c141e01c43e52582212005074001c0d041c0584d99070b00600040c00a0030702901903080c41e007020000f040507500c84c0001c2800711444401641e4480c400280c59032810300c80d1112040d48030040703070315125081c40d00383c014200d0103d10340541c52619104040b80805035507901d048030a15500404c41080c2a000c0c0300c00c204005001303a801c2460501200061542d8001d0385000714003485c1d034140c032035040401200a444114403910200301c4240210b40f034840c1044102d1160301e5043c100007541c0c000221030b50015004a81c001c6d180380070b01348c116016210201c001000444400c40e0800c44100052015041006542c0907800d494088800064000703403111032001c41032801ba0008428090540c0d90341d0060482c03c8032076211001d007601c41044204c00c0e5001d6030b1010000c42c20003100103406104002c005042d00d03070074031208041e03003034130150507841c294004540210054002d03804100024404501580240c1e191003107140343c80700010f0000d100303208503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 76982169 1250 76980919 76980949
    0x1614040b090105090402010c170405011209120c02221505031504151404030215060f0102121b0d09030b0c0a0914040b03010f060501090b0405100503091006030b0411 72
    0x1540760380c0d0a1400388100c00310000c0c0100d05019405180f440440c061010070b034031080e491003d02c2d03955410503000516584a08243c07000c2d442c00d058040700010018025015051402e00c0c2042804059000042e003400d0b069049203c0c0105158106084021a0708001106504804e07458070281d82d80d014184d5841c100c4000860b1000660003050001b41c03001c2c00840c4100b200b000c04125020300c00049c5100e19000d03542100541d1210282030000d41c100324016038006030407200c4601000740c0d03000103900d6207007100700308a506400140640032800041180c0501460600032106407651861018003c040c3c640030075145411000000342c0c41070344407070894600000320303a640c0301107178507203210401241307864480707503620036100c81140d8010344092003003030840b2408040224996282000251441410343c0091821803c100030900040c1c5540c1400407030a00c0c030b8030b00150760350f5500c0007046c00e0110300030801a0300c0307081850000510200e80403642c00340303002d00c181c0c0007039445000400000321281c1d024 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 76983419 1250 76982169 76982179
    0x12032e060905190902120f09070308190207030b160206090606010504091d0d03020405040c020601050f060304030207030f120306120f03030b01090b2101170604110a05031614040b 78
    0xc02d10003400c08110344000d95000c084099070441e11003e00302c2c10b0f60040c41c000008520b05404020781114007029a58118000d04090a034207801d41e201c840240c0310301c0d074100380514441c0b00340140b134a01c2008400b00440d00294031040d18100034945110060b02034007094018031409001c40e50303a59011801038016101611a5443c1502c1e02042c54054282069000c40c01141800f4070301846106125416000310320340e600581e21400d200c1000200d030948491171045600100060010f81c8540c0c05c2245400811280307140c0f40e541d28a81240303003c089401c003c0c500480b1000a81c00c12000550680000d8003030b49042c05150784508000c0001d4a000704080c061080d001c08100c0801d020f5404101c0304c44041c076000000e182c8a415082040c1d00032103410b00340c0d042e00c0d5003034680c4003a81c5d651503001d0060540c03030a440390702d160850345e03507018058005042c503420300c00d88800c15913424a244d0000c2030083e080e00c2159069146604800340c19200700f04142d900d40d2008001c51520344903a000d003840081c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 76984669 1250 76983419 76983437
    0x30815090a0204241b170c1e030f04090504080705030a03050403030c081608070e1c0b0a05060d080c0312130b0907052404090603050f070603060f12020312032e06 71
    0x21085404100b05d501c1a203014005120b4080703610000c3c0020048085a00d0080c003044074001c2030080d8007208022441d4a40e0014003c0c40c0a05040f201114201e40080c9030220b859140d50400010700c0c4907c51000346948070026060b06d0098054200da84141e000e0703101040284641903080c2c80d015400c454034540001c9101c004000c141c0158200e0342c00034003510f0086815110100498207420945400084112000e00c1c40c8003000b6800c0300c01742e03005491803024002030034000046645880b05410040800b44040b6a074203041da820810380e07c0168501c00b0b808424180b81c02d0708201c1002c1310400b07841c15244240015000f15000820300c0440301d01410410f4503041500360100c0382003160b04500e010040420001441d10340600414001c0c5002c0c802400609942c180c2c491b160040341d0340143d00349401c0c80b00811103d02d84d22007207400c8601c0b89940d41611402ca04c00a402e003894070040300340181c0044184240c00c02c84005c610014140903009641c2a60748443c1150382c1341d100e10501000480da04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 76985919 1250 76984669 76984697
    0x30112060c090906060207030b09070806070c05030c031611030c060a1b050a06020415020c0607080904090c030c060909020c060a0c050d061401080105040b0a03030815090a020424 78
    0x703403081018a8031440c0c0040110b403140415803e95a4980c400d1005030322a003414001d0000ca01e0400d9084080744000b03140c414603200038551a248000c0006091250381200603041c09400c0c403c5442010703a03801500e0b5960489420100815025002070360429030b0b00369180140d00f00000e000c407105000808403401e043c0309440480d0343c0c41000c0e00312001c02e070484050000048042010002e054170611015840b01c0c00c2045104011a80344032907000c640c00790450b08a2516514204c510a135086840c3c29a11603021001c034001d0600000700401141e45503400000b480f11910b075a000b903c40075558004050340d242c0308101070380680301602e0718903080400490610842c0340d00004800c01103040060134000d04108500c100ea1a540c072404d03482040f21108902c541e40115080d015040480c1d0801140e06524041800403241d8003004091012140201c0c03a54081c4500401852500902101b66032804401c094040e40151203035060306815010b0051aa8240d800c7c1c5451600007031341c420b00d03000e03001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 76987169 1250 76985919 76985921
    0x20d06050a0603020307030501140f10030318080303090c03070b0a090b0a090302030a050a0b070903030203030f100b1303050d09051507230d0f02030307020d030e0705091608010b03011206 82
    0x140c40070a01036520940000141c030140021401140104000202043e8080d004c0d0380c3c00c100200013941d403003140410031440c01c0c0d8022800055942520300030f541c00c07001d0708080140c400c40e6040139203c2e01c0301000700607a075036000500001d260026000c5d962400c2d40c640881c000741c06601c408a000c40d03800c1c8801d010340700114010b40501d2401d49004282030f07540c1c0d000b003401c0680700081514250810000c400a01034182032980d040001403405ca0161032550324025268040580f1b00c6c1e20311200000410501e0340c2000d0280c0c013030800e000055580c0c5c1c0b24a5220140c0c02c0152204842a00800c1464400c4d01d004101c00011604003900c01d008040095481040c503600c0980100d5141581e68104d511a6226000c01085100104014148948251005401150702190b900c1c00c6520401c10020081ea021449505000c000d00300455000c203441c86450400785950001d60f00004408100240240c0c103002c2d0300b1008180e0f0300d80d1178041e601c07a1414231040c8000d014007a50004003140748000541d007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 76988419 1250 76987169 76987171
    0x152007090b0f0603070801090b0d0209061e10030204030506150d0212101b02010b041e090c09050c03070f031802010c080d06090e010b040603050c0f0a0e0109061809020d0605 76
    0x801c0030b80c6000c14540041e1054000b07450540015010350010300c590034152094021902c8210780748245000158006406060b0040c28907018011f07600c0e01c10100c15890581e48000c2d030004001c000e800d041000000c0094205200035105840b5070760116503803400c03001c2030311400c82e006040300004e2401c0d9000d00000c0c500d450802c1c41e20f4442d20500d84900041c5100d4001100f0f01403d644290b50007079200207080d680326021562140c0c0ca00354690a4051094021922018a00c00b0109541c002400c005c070544005074032291241c0d041108010103880c031680158842d550a4603036281c46010440d003101100c21041c40510240d0006080720b01640c0200d146858662041c080649420319051000e000e4490035803200d40f8081d11660460168282030041039a0708030706035401c010382461516100c0e541c41c8210103c901814507200610b90a868660484002c1c107811032403a089541d546901c50010107042c894054001c041600c0c1d014800030b64004d484800c0e8004045010031803260b02e0340002840 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 76989669 1250 76988419 76988441
    0x1003020c03040f08011506081015090803030a05040c1203090306050a020f1308010f1e05090a0b011401020c090c121f060c0b011d0103060b0402070c15200709 69
    0x110030720000032554003540d5041c025044d200d00105800703003079207016200d400541d0020801c0c464103400b0002d01d0010402c645085a282c000240d622014000007500c06079810307084080381d800000200b040c000700540099008610484140840c543d031842040904404668010300282e5200d808002040e80c0b500110b0f00901d01e04401490202e48072040b14003540103024003c010300c0160030410034840203204018010704050400c2c012000c4844456544410035a8886a199603c01c0412422402000740840256000404842958683c0c2000c07490080340c11500f40107100318090740c5c50b203040c4614428014001d01360041e04090100031003900d621070080060001103d030715010b58175003c15025640041111780c503003408021080c10000c080c020140c101207003503940030011003034031032030003a525044035081000000d840b8140d10009019115845000c0d00c50002d105d0007003001c901c1170034407010b03a00c2c0c0d548820341184200091080107414001a14003640c1107440e080040e54420b0b041030700c96074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 76990919 1250 76989669 76989673
    0x305120c070b0a0201051f050102031c0b060f0301030501061a030a0b0d24050907030201080103081c060603050702060703050402150d0f0501060804200604090207050a05011d011a1003020c 82
    0x16890b101c251010350082c501e0480181e44400901501c18071000e440d80100c01d003c5c2e848290389003003a001175642c1c401c1d1400c1001d00107034203540ca030301d03400e80354000101c0000041c0820703503511074090074a5454000b1300087d18203510f061800500b1000d0008582c8946151440c000e04590724000500014880c0101d001d820840d00c0100e480041c0d2510382141820000000002c91001c1c0c1d8a010310894000401007803c550004030240092f0fa040240c040c116036001e4801c6a1f94090203c1942a2034140e1109040941c1448008500b0680580100f840390300c9030350844102e5a0f07140f10403010f84a00761000380d0030240402c2c90000c1d83d0403010090500b8408400042000b50b40440182c04a030b07800d92017000001c004405010800c010451190000602c01c5041d00c1e00e0032041d00040c0980c45548541c00c0d10542c0001d40b0020410280000100250031100030001003401d44c0000384c02000525449101b0b5207400c4510440c44040341403001046405804501d00d403150f460150b0095200b04543c590078 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 76992169 1250 76990919 76990933
    0x409030c020d0c080d020f100b060c030c011a0108130b090309360408030705180d05010902090901020a0507020f0f030f070801050a020a020c01031113030804080f03040305120c 77
    0x36071503680140c0405445041e0f42d400f060704e1300107003a003442d90034149001103410000344168150790008242c400c012191900281d004010310010f03075903115480c56400e0301d01002c62602c10018040d406040c00020108082401040d000c0044440f00030071551650f80c1201d6103e41c0b000318030098101030b0b2042d1030b20f045a01e01459003000412501c078000440e1248000c00043c2400d0314100355403001081811a0b0301ca1320741c102036541c8080c82c00010040000c2100c04501030000000c00d06105810303280180801200c0713800303400c220f806085c442a003603008001c1c15012501d4074505100b08d8103150f2040d03a916051889030b078204220702004100080d8003411410800c2c110713550034411100310501400041a40700e2804143ca400c1d100003c1903907140606c1400500d00c41c58004c100c1c3c0d04000300901c3d00051120905031011418021400000665070f5001d40210401981c64024025544c49404540c1e11646203402259284074502004120350060341d6203107c5100c89102804a0308400c0b003c0d03e540c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 76993419 1250 76992169 76992173
    0x9010b0d030f0f0909020c030309010f0c0206040f0201171509090708030406030f090209090a05060c130608070201090605090c01170c09090a110315010f030501050603131704080115080102070308060409030c 90
    0x76a0090f10000200790230000074004490024811070041e100d24078411720501184807000ba4403800020b00c050044a020111041168401c8640c002060b01500e11540c00781020842101481e1540c00c4c030358010985a004a0460000004d004080b40d00c2c0070011840c29040c58801c9020b030044a10610b031181e210b584950050340e80000c0144529542c000400071201039040c100c1c074044029080c0c44503600c08000b090350a00ba003250100903034600303040280039074403400030480c018001e07e5009451245401c2c20710000d81c202040e04001c282d000d03619000b40040d210140724207a0b2040c2c0322980e850301d00300001ca1141c100301420542c080c4d40c4480008540c80030b01d80c254080d40c4211141d00410951808842e0b50f582c0240d000404e0800328682003066604200205a15100290007000d000c00c81050b241d040040346030159078480741007416191180d98a0031554044c01071001184405a11007101151404052080d907510b0740c1c243c1d613aa2201d4a809050000508002406070b04210340c1d1014440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 76994669 1250 76993419 76993421
    0xa0302060c0102091c02030705010e060c0a0b0601090611030d150f0303031e0b01020d110c1809010606020f070308160803071701050607030203030402060a0e090c0309010b0d030f0f0909 81
    0x3141c481d07880c0000d079480c0c00ca00c00300300780211842c41e005543d8440c03203403070b0000d80c41c000380150941d20282000401d480c10200010814000c5145500c010311407074a1030010007000c07603c0c03140540801c1c0c03110b05d41a41c6842c0152005a44000580007542c414800308400f4031030b41d0810041000f6080f50307001d4150f141e008102072900250026404207448a8601c04035215956980010303100c2c0450030000f544810340001e49aa03411a0480200804130700301c804500002d00040c20b14900050404d80c411303940301200581078a085601e45070552a01200041d09800031400d111386991140241c000e46065a44512054003e603040340404038000001c100001c110710300460060301a615604a12178400d480300746503007816081503009003000d03c10000044d8000043d203800607411a191501c504c6206011203140c0c0d000307005207500440075814800101320800c025401045064024002c403182c14060001d000401c3c41c0040009090703e13040f0221500c9200b000c1c401c124686004140107550302000341c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 76995919 1250 76994669 76994677
    0xd110a0305150f130b0a09060609150302030d030204031a0c19110c0118030809030102070503040e1801050f0f070e04020c150f011a0703260a0b0306100b090a030206 72
    0xd414801c00b109104999590500183d4030500d030b003107480d04c0f014643d6107800120380701030b0400c80000e03207950400742017000395046800603180405c01045220100040e0150111051006a001307000355680010303410300c24002c442c280c98102030704a00c0e01d038294416410f1480c0042160030516024000300d0a15030400c4212815030020f5a0364041c0e00a1080101d07003050703015420241449941c40d10060241920340000c4201d80e040403441ea214041000031038061306c40d03504000e00c41e003c0041e000c183c07a0300812126004800e80e4900d80b140e40ca2008445080300c105450003450034201400082d4030440c840b854070341c0404140b9003850090303a2640030402380d1f000704481c0310003074111910145200803415400c96100766000306011f03903549448012251840710310645861070000240c1c41041c94007520b244030301840c2819080788103400940d4144010799080e94800807940c00e010b082655440c00060650090b40501c402c60b8404d0719011404625500422099030046c3c03503601c0010150751458050 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 76997169 1250 76995919 76995943
    0x907030b04140103050c18130804050307031a010803030415050702031b07063209061306180501050306031b0d0b0f070305010e04050706050310050909070302090702010b0d110a0305 79
    0x582c0a550440c500a810035080c019680e00a41c0103844400c0d004c1c1644804680103c0030085d03000c54514542090700b80c40c810354100c2c0c0d4061086000010400c840f02d2000301462464280c42012641c941121640b81e1000fa07801804000f0346880c1c903008116160300503604116280100c0345071044600c4455a4003003108107846094005800800c4400d41110540c240c0c024640410226211003840d4003109100044400341860404202c0785410b8071500304881a6424a056207803140380d0340d140080040200c3c045c401c0c1e42000306a000205940107105603406440001c000d040c2c3c600d184507242c1c2c50b03000c955280e1944500110301510110301c80d02c4d240c6018549000410010380351032600541950030607030050f02e2a0021310100700100340d0100b9114140c4c0c03424604180c0c2c030b40741c0c0f44080c01809960380050340d100c00f403075051016141000400c03a007100d1007510801d115646038001682202c00d9100c0c0c80d90003030b00701c146d04000036004030300070015080c0060030300003026101c1e21040d1500038503000d4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 76998419 1250 76997169 76997201
    0x4080d0206010303031104120b0a061a0306010e010504030203060406050c0f0d02090316030b07050304080f0d090606090c0c11040f0507022a0117060120010f1d0c0907030b04 76
    0x1407091641c50700480391141001b090741c83c50145030140403c50380c10406801740c0705000c6540030818004d40d5400520080a1409402c003040c40c0e03032550110203078026200e4a011590542c46140154042d90540701220340080c040e040307542c1e40c0e4444a01921340248201c40e201000c014150511010310302a103800d8011010043c0c44200715010302d440d014400c0c05811650b1514442040054402d0301c0f51035100364079242090301d80d1200e1406049600512940c041110303800b2802c00f442c403142c1e502c10382c017060084109000f9542e442d8800c0040341d00505203400020002101c45000c10b504a40301c003294074018000150b1030303008140800844d50181c42c6c0d100180c00c00d41c021100150a5040b11f0030500c2820b00d042242e1070500d0000e00000f20000300e18803d18a0703800003c1d4942c0c0118039607456100c00340d402c2c981554903503416500030719001c080200780901d004040070002c401030321b40751210640c140013050901d28090400202030b00c010021020542c07100c0605000b5220381c0644003100880f290 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 76999669 1250 76998419 76998421
    0x117070203040e0603010e07060f09030c060c0b0a050603030f0a0c0804120203061012030e0f030703050105091218090910090803010f080105060d1101111b09060109080c010806010504080d0206 84
    0x40e83c446454005801903100340e040c45d201e03d00c01040440c2030000c50b1100d041c92038a0480d001010b031081000fa50000c1c0c03481f4002040010030340c0d0442001c04003184a014084026a900e41d4004101c3e041a119160541e00034000c1a030320314140c40c01081200001d0809141300100c6a6440c0210b80c01350300105840031304001d0b0181141000c01a2540013002005803001450500004e40200b481182019040010814902501c4e071035102812503010300141c1524001c0b84c484c18007602030802502d0b8000248181041043e943c4010801c1d551000340030b038500f6046420010070400484005460184540204124a900315525118102d80c040c0310303055054580d0301d8039454000b040403581c000255a41003404000c510341c1ca0300010400c42d0f0f4000700d1380c4001c411000c0100c440c1400815911143e1081c0c01c40000700b000782010040c44c0c0c90085500294a50718140111107000c004d2140c950380c1d03402606202400d6010340c20013540312806140c840d003403541d21144caa1030420081d84010150b00014 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 77000919 1250 76999669 76999679
    0x3030e0601031703060607021e01090f0803030105090c130f03020306010905010501050d0e01021c0204090b060c060703020a050f12070201060b04050d0b09011b2703080a0e011707020304 81
    0x40140810090554040c0c5460742c07460b03e661400c0c00520002680522002000070301a586440c1a1828aa0058141016500c414a8450040c40c00060786408a0100b120004907030012841e00000d030340506003e5400e59190100f0301601001c090040c0e210340070103201440e903075503240810800030200d1000ea801c0c03c501e140140f504058068202030302c07142c10a4014005a41c1080c110340b82c80c0c10f003140014001d110890340318028080d04004044440c00d0500c42c0d40d440d000d54018100b5205080e004100310340750001004164820a00b468066401100024503258001da000e400300992a080131458450a04180c40d0320f40d0201915003890000d44051004482d424172030f21000e050314400e42d9161509150015041c4c60448100420741150030000800b0b0307a6007900041034203801c880d902c80c1115901c4a015002c0c401e050b4040380c107106215590240d859544018500726a01b001c0100d00d0507040490031100f000c55148001c0c103014402101d2201c0a0000c0c101d244550f9442d4081d40e02c4500709 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 77002169 1250 77000919 77000921
    0xb09190f0209041e230c0a0e0a060309060e01181e0f030306091503020f040c05040905010b03091005040206030f0601170106050c0d031104060e28180905071403071701090303 76
    0x14800c00b811085c44401ca8501960f0310100d416001303c800504145c07591000c40048400340401617020350001c0652400280385609504001c641a1252109009c092a400261343c00c8400410704c010300101d83e10f050201003003181400a865641d90342c292844081030b0380340d00e032071504e11400c00c900213030351400100f12521480c070402841c003044008e090841c902d540c000580341c102604496104994070361031002000c0c0200c0c00c40303009140041091216680d10f050303035141504115051881c40c020103a0340310ba5440540320f001d10450b40240014195100c00d0f0b5141140d07000140140d0611003a40c00380d07000c004104000900a042a94415540e590300180c0f160800d109007400348d0506040121002d0711000c12010740d402e860161070710301d0001d030085c400030302001240700c03032040b0031b4100306c01c109404020390707441c07070241c507a80c011040354144802c01200442c0d2440e58050916007103040240805065455074003031100c0001c04803000c0c2e0380c4075405401c04114030404c0e040240e55039801c110803d501 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 77003419 1250 77002169 77002181
    0x4050105010e0310050c0c01050a0e0c06030f0c0711060316020c010e030601090b01141902010b0609130b2704020a0f06090b0f070f080a030b09190f0209041e 69
    0x81c6400454021102c011a507070710340500383e2400e659256400102400c1c1d07a14196040400d40e18000e000a08011174668020701f40b440c4000b00301d00551003580030a04221084a00558280d013001d0042c0c2d1342c400b00c031492600320b0036048500102c50100c9203c1c035903c81010314040c011600c0b0001c90780d40416000392504449940050511442c80e0441c6115076000c1882411552140300225580820b03000480307544500c14810304480300d0100d50785000648085210342ca0713003019002003000e03240d000200100e0b4045c8102641c1d01404c201003041c1300e03091a810006c1141809020702e44044030800f85000480c01c0038100d80a00d02400b000c000541ca4a00024401131a1413211140083d08018004008600b81d00841e1614140003c15200440344142103c00380c81d00424010640850f6142c594025840306203040002420002020352901c3c0254100f0302034900091166074801d0b811074a400540401000c4028003039007446220110785440c00349405203203c807a0040316035052080c1800803216 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 77004669 1250 77003419 77003429
    0x30d02011a060d0603051e060603070b0904090611031317030609060d1a040309080c0103060b0d0b12030c0102070b0f010828060e030c010c0804050607080408040909030509040501 78
    0x810140500c4204100100494a50034142c0d1026501c8040740c400070058895a0b0000740144185128594045413050901101e4070030103007910566150041050780d1002d09000f60103451504001004452802d0fa000d2080144159004908492070707401d503280704d80080301e04c140005850100c2100b004020143e0400441031a60b0a40c21402e180021644121004109074000c80c140480b540612812345081d1000300200140c1034251307d06843c00400c0700c5424032401c28107214000c3c00600310360190003200c00355004148807a003014110142c00c0060449003860340d81000024100c0710072101c09200402c11a85c0c030078009a0f4480c0c070341c03400074030124000b0a11149540f02200510041c0300108044070902c04180d40d59044c4901007084111084202c44c4c014295840c1000c0b80500c0b4001001529405034598000c000301940100142c40c56101110b00415503048400020070560280034030503045409154228203180c0c54011700002ca4084101c16800f08030b000c521200c461401d401a58090300c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 77005919 1250 77004669 77004671
    0x30c0411041202060d090501090303050c2d09030f010905120c120304080d02070308190207030e090901090f0606180605010509090601030e0a08030901050708060114070501060905070509030d0201 85
    0x15815012600c0c503405580654400c59401c4030400081d561500b0a995105420100401001705241307049402414104002c5000c641854006800500000d060302c41058071080c6003504829426004204001034440b1740d200b2490a2061440380d8070100480507481c4a910000900351509041052a0020452481003035640c2000038400d40000440c22104103a01402c020380c594a40c0e00d42107c05c4c5c001e840202e500c1c07604c08103501c0d00341a0b000d511035000b21803410b0164680050030160600380e1040c2c40014010401d0200c1460541c06c050090680c096101800001c10786416910714600c13100c2480e040da111a1034010a02c04100124000c481000c0c03041e804000291038440007a04034050406014454410302002131700c0340c1d000c0d400440e0399540c04015900b20340c00901d86001c09070010303103c0388403030361a10002a800e37038000c00c0b80e9406404141c403032103c0d1724420203c680c0140d100c80000c507055500c9140010f000f4603103018071070180711a5190941ca83c8114800e0620b07090b40c2d103c07004216 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 77007169 1250 77005919 77005931
    0x1401030305120721050703050105011e0c080903030705100b0105130603050406060e0a090b0a090506010b030403030906050c030402040b0d030e040f0b12030c0607090f0608040311060411030c04 84
    0x20303004801c0302e240071400d001d000d01c82d95841c0d0b01955155002c28102201500d40066500520000d9009a11079045524100103503601c2c4d600444a03a082804c01a550b40f840504440049009a00b030018040c840d40c4111300c1d0800030008a415a08001412280c945c4010482528280580100034034043c0a182c0503040006d43c00b294901045a840740100b0705949102150500c901604000d0191540519080e180d0801141e460014481480107403411110300700440c5c00d400650040c0700300c040d000001004243d007001e000c00219407000e4003c03418950b54000c454005100740c0a034070304c10034607459015100e107811300601041d102404401ca1040c009141417200103900300b15403a814800540c0d00080481d01c8038000750040c040780719003d034002c40d141c403503080e03081000008103590705180e016100c56032107210701510302c4082c038000c0c0e8041150301c5100340101d2348940c440d264018083e251032130381813001c1c42c0424100103040e2820b03a4001c1121851862034241002803d500b040d00392000c0203c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 77008419 1250 77007169 77007173
    0x40302270717010e18070609060311070c03020603090a0f03020606010908030c10020d060308040b0403110306010b1e0412030801030309060906052a030d02070204050105010807020d030b150a080a140103 88
    0x40e003405001d0302d13030b020032903030049454040c1c580d2030f4070600c1d21013200300c0c0c42943d100e4070301509400381481000d00080c14252203040107902c1d0750544120b694803030303103d45d070850550b42081801e0300020300520191040082d024007148865100f030504034000c1d0003800c1207040c42030004003007030142d4106101c0c680c020044a0382444e130024240480040b07200c0e0050315480380b450084040c00e080e500281c10440c1c0401c002c0f4040500c0e000500890703201d00118038040d0480b01c14152200c209108908101b14280110308010100c924013070014040302c10154a02a00c8032003040d0203e2403141c0c150002442c000040c401c05404c0031800c0003800003130418900441c44e2040041491041203407988100690b03d000805419404911114a04000095a4440c08018030210094000840030f9200b282080d000007560750280b0007690040c041036020342a4804207180980c0a041c5080c08280c1050384003101e11300e003081d0040680008080da603101010350800b0a40041510f0000c801810424405001000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 77009669 1250 77008419 77008457
    0x150a020c010f021606050306030f0c09070c03031d030a02060c250c03230c04140c07050c150702030c0301060b030601140c0106090c020f06040206031305030403022707 73
    0x280901e0152022801c0750302c102e041420914071001420701200002c60380a8001c1c000d188602e60036000c540341e105000c8442a60b0f081424006508803145074007090303005108421a16081b406810085403c00290f4541e250078010314038401c100750404108420603580c1808540d0b080f02840082d03504007410510080250441c0c40381c14101c01c840ca950043c108440c5105500c0115006095a48906d102038030203502c503800b00028100600500c007a10560b445c10788500e200e4000c004880050b00d0340d580200100c680e0085006480510951038070900d01e40d10302c5254a000c120310101c1c03540b98000b03481410718005402d10068400d9050a0040c0041c103240340581e42d010109190101d40c40b07031a180342035081c0c0300d0f800040c0302d65400c180010642503510b4218418a500503400c5401c0c0c110002c0d007081c0c036420709403002903001c2c01c2000880c100c0d1402400b50400e25006009881c44d05580341d00103a0421a00c00c1d1502c000080c40252100c800000b144c91035201c4080e040020002613000c00d810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 77010919 1250 77009669 77009683
    0x90203220c09020a17090d020f0123060319060605130605030a0b040309030b0106090f0602060702060c0c0f030d0f0c110607050a0e1305010906050a030201020307080309031303060b150a02 82
    0x4080c10f40c00f0031040300030382c422070040c40704040c0c1a0300c8181c1414450f4005d521116802c1540015103e211001400c483c3d0500c2002c42d0400810089005c000810149110082c005080d81e030b41882601c0c03c449060719000c11000410b44140000201c042c604000c2c05400f88410380401c81652400400b040140c501140b407d2803030f5404030382c40519981c0c0f40b8098500c80745503000501180000000802c0036500a0403c0701510040e028900f041a9981c130103d17502e0b134045441c01c00503040800400c1007007940c40040d21036441260262803c8014180e440d51650b040b0070f0521903074a403a1a10000000040d00c10504180c482d440d002800349040700341240c0d20313000075001c0c408001000036440059842402c0700d03220340200a040b105050000d808403c0681001c6c0135210161340340643c001035a10b011040c9200b226410f030081c2d81402d401d6103684405400007011704d013640c041082400d4810004a50402c0910300c1074038006260b812150501c00c100c00d002c40124001c2c1000c014619841d41c00080b94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 77012169 1250 77010919 77010929
    0xa1505010c0c091d06070908060c04050d0f030306081f0e0607050a051c05010e0402040501170a0807080d020a052205130e070305030307110c060703050f031807090203220c 75
    0x801c1c0c0304890300804000489100c0c8013600e83c040c3ea424020156400038107442214401c1045a0305904c80020105180c8140c2c800c49501c56501d0803888002b0341c0d5004001d06a17802400c0006406507256901410108001916060b8400211201954030110320501e00c0205581d00107100c50314100101034501d10458400f02c003481800b0446500002c0100384103039451420a07018000765130f60b511000000c1d0030507102244a1420980082070540d0400b44401c440e001c03036401030540c03154a40300c211f046e0b0301600054416070810004001106411700040c480000140d50303256403200030440c80d104480140d0044ea490314028842000160348000021030402c1ca20f17180090070503c55140c0314a0320780142d1000f400c6000c01300802c4400b50b00a24000010010708040d21034440008040188030320441c01d000b0040b450038010300d40360000407000b440d844594201011030b41c4580c4c40402d80360001681c44000400c1c0c00200b00408524120b0491400103051401c0d00c042140701d80d50750034030b1b12890180e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 77013419 1250 77012169 77012171
    0x90901150b070809030a0606090e0a020a090e010905010501150206100b0901030b01030e0a0602090a060801150e1903050d0e06070c0e0c04030605010b090a0b0a0c11010c0b0a1505010c0c09 82
    0x6002e00b0000301c403a1204d005007180c0f100399891516001400345031103840d04080c40e00d90504030984010030140e48080d07000301078114050500d10420010308240b20011001d658610060000440920a00b4081c001c19080070b0002d024181c5c000303180c00030007400d1507a005201c0108004601d6814140e4241140c24200407030300c96080d0004030020142c5203031100302ca108095412085c0a0309500400c0d503030105072010349aa684880003564846000e100c2c00304065421116240d0807441130303010380d208080003404507982c079524240d5450b101409400955041d00703c0d000911059030040840752611105a4034182008030944860710740d4000e80c03040326015644600083c5049424034110f4014541c450001c00965864030101d171490b81110701494014071503071601180400c03101042d98202c0c0000d0350b6407090350769250368840241110901690603c0f100f0451000000d04c0f4010040c842c003288a0009800c0c0404059110201e0040c2d000505011040c0f5592003c90420130728101611403c01d8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 77014669 1250 77013419 77013427
    0x40e04020121020d0b01090605090a0b0c12120a0c0305071209050705101d04021213031205070c060c091503021303050307030c030e0609090402101e0e090901150b 71
    0x400c019000d6074000c24001e21840004c440806115962020410701c03070070390303640741b003141c407a2000d56040c400c1c9414a0351000d481841005100c080c03030018800780342c06600b91600070321454410312294100c1d0740c0d60302c080043d82c420021901000c1c811604010201c1c6024001818802c02c041e00303101c0c0c01c251000c5038030740720b070540021b000040020000420b0058100484251401d40003004509034260550240115404400403880c0a00a0b56a005d08540c0c0400d119100d90147d0f1100580c540310417818440100b9a0004c035140078481c40d0311a01854a440c0705907110303072500c681103074052100d00080c0100c0d40380903c440c29000c1501d4040f01007034140140e851020480d00564200130b0340c4001c00c5807200148002c2010381c049000e0040c0c910a071205070000340440100329290040204054000c0d107102e000a02503d4100192a4620b10500344421603092440546003000030743e03090a40402d040c001c511011f424200c1c1ca01c1d07408031201c8000c11040c0303080c070202c1164240900c50801c40102c089 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 77015919 1250 77014669 77014697
    0xa0603020c0f0f07030c0f06140703090f030606150801030b060d11091e01080606060a080a090f05010c020d020a051b060f03161d090109051003080309060912040e040201 74
    0x301d03000c0710703640c80212901c0d2843c120b02c5950f10012800111080b9101207400612100310070b08560a070341441c2c64101504110400c2600d554001d40d2054040040d81c40000074120740d210880c102441c050200400e465003018a04250ae400000c1600704000c0c01400400110b009040b0003900818211045181c1040b80d00708003850201c0483d2096100e5601c0e020f0025544261020900800c1a07907541541c5030381c0c40e03c07c0740d220081100e03d1a00f10008000c0d103050141700e08166984110070100009000445031030702030340211240c10843d41c6030340d604101c11380c1d142c040051000340c980c2480141211421580c074261641c4e412484100e03e030742c040124041c81d5840105450320050301c0c226854a80c90b00401c5100800d03580c8150f0b601041e43e41007041c580070000203030200c2220b030162505145910f0010a1030003020000d0102e4482004004040300203858100210f0140e02484000c101e681030a100b090308104c0e00900d0007210301010401040500c11041e68103134041d0302420482d4407040c0300 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 77017169 1250 77015919 77015923
    0x402010810050a1412070b04090c05041215050603030702240f0f040e0606120f0a0605030706090e011205060a11070209070206160203040b0417160b0a0311090a0603020c 74
    0x1d80005500000f03000c00404c07180d41c0d180b00c0b02c4019500b103541440302c408008540e07403100d0550040c0040f84d10100010710455045401550a1620b50b11b0802e00c0c03d41d45804440904220349d03800c071401440c0804502d2101003a000303007604940210090b501e401c4c1280d000600e00c6c6d089021000c0c290750b03800c1043c0417001052042d5005980c2d01c0c50201d035600261800052035600900401c183c9101c0040445d00c00d0500100703540d603169907440d08110644403110844a5504010400464140c8800010840b61818000000284040c5e00c42d03c0c911810104d07950a8010f050b040004507680e00603c0300041500000d207203812074038510b400142ca5000c0c051244251040c4000079400039460014000400e500058440c818044c000c80c040802030f40c0d8400326103d01c0386205000d5013500902091004103014507104071009c20f12805c4420ba8100d0034080911800c050b4003503881c2c5140851b4109155804d40240031102c02010205072815101c07078002480019140100e50415601003444a403412007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 77018419 1250 77017169 77017201
    0x70e0d060608010501030f060507020607080609150a180605040b01020c060705010b0613030b1501200c03060a060806092107030e040603060c020c01020303060307120c03140c1503060904020108 84
    0x1504000b8803981d80c581c240290340031043c00c805c03032380185031800280d000343c4086501030150b459a40c8000c82a00ca1004100d0341c94409469003081520321540032070a59038a0001100821003070210f554810307000240e8004403189680087d00650034000862126079011030300b414004c070101c982e00d403280740900b015801004110f46150b084a80003940b0460f1046403042c04c0220b070301c00c400c1c1901d940d403150b40381c484504111428501007945800f82003010703058041c000d011070302d2680443d0120101a40003a2810034207846032403031259a07070018449070700188409a400020704005045030200c0d40e45c1e54003949103110843c1c0c0300b08004a0508101880f4600050071880700520a0016586a007840001411b4809401004d88101030024010754004800d0b280f00305401005130010a180c4407201c0c0446107081800caa00d03e4900002000003140c81c0c8030040018403401c01007031404001410702c010f0113951f038640e602017801031080041650794180c0e550390266088c6422941510762038440088540 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 77019669 1250 77018419 77018429
    0xc031107170f0408010603062301140103090503120124210b211b03030306040513020303040e010f060c11130e03040602010506150408060a0203070909050f060117070e0d0606 76
    0x110000b400104c64005411040681740038440400413541580000f442d00d050680e5000401c2110500400203500b04211280f2004018100810307a24840d96490781942d010505404408500800501c801e895140d15000c445070550b40b003104452500c60050051480c00c48403041e008002c9000f4613a9040a070032a158081c005448030568078003084078016085005ca00e8034000748512000350b10380d500380c0c0000d1180020f014020303504e95241e02040c4800ba042c01404058003000420320400182c90400c01072000f13021482514a95505080400400d11402c0d40880208180c0b0940b00c00030440258101d604200211882206681c0c542a850082e1550040c50206404003040001d181707501134108130707c69001180c810400650b1031448140d54050750103098219880390001480d43c03482580115080710084c00c050301d0303880d03454415100350355044810300d8041150300c0030322a040d600718910b00115100900c1e155210700e080729004020030702090806100301c0d001d4040070244955075004c0400381c4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 77020919 1250 77019669 77019697
    0x9061801031b08071101051003080c0102040e100602060a02090f04150510030b1507050a0f060b0402070f060f0b090601050d0e03040602010207050d1805061803060106030c030c03110717 81
    0x2200b1440503002620444c2e07000003286400d0b480e03404420040c030540340b0503034850303000b82c1c0c01e03a0031521500415000300b5042c220710343d4204030100f94410740c040d0310f911442d60040d501c2c0c00c642c2403040080c00e203400500030001090040c060100c0960b03400d044401d6560050310009628450f44100b11010070056002326006866030806025140e0715070484a00c08a050b0341800c13031071250100400840c800c038100134005401c881c44d8140000c0e00102c030070103168003e07032010440e100c1c6440040c1c22a030184100b1209544604004000c10a513030141209580248504115540c56440801c80c180b000034042c03410032400148040c0d08118651040b165521007100b241e0321192268400f90007076000603410b8804e40b255544243d003952260103102d00d0303058100702960091b07252909000560308080340522024503450005d00213914200001da000b009165008515038109107009401c03900000c50394010141445c1041801c21208811034040d258000344000307208404c850400414050b0712032202c140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 77022169 1250 77020919 77020961
    0x50c07060e010203090d020c100f020a050706050409050601080402090a1e0e010b0114040b0d0c052107031a011b06020408060f090106141c1515030c08030906180103 72
    0xc00780560245202d040b9401c100c58540181c1242039aa52541480b01c540c0441c1004050b0302491252032101261499401100d04d01101d90707a400781425802c0e001440003d4010030108140a094040c42d82c112000b070074804414107090b004070711411001494880e02a8541c4152000c0300405480c01c000f8100c00e40c010050441c2411302c46c0e018040e1030000c280001c1b603080d200304c03d040920044408954140030443c1ca82030043c0400009004050300017818040c00744101d03400710718100901c80b140001c50508181d240391a81010381150500660a610000ca080c0d0741501e5903085803004003170415039241d00311212458178012019111b01e410110060186c08180500c0302c500c030b540c142c06220000c1c02030121a072101300000016105856840c4d018401c1e07100450010120000703a44110f0140d55280d0785036041d81e01c1601602c82e22919a040445038030300400c28002d16107902c82c050703c800f1002e176142115020002d4503074003031a0040b00c11200403a20b2a001607019521004480800301c16464030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 77023419 1250 77022169 77022191
    0x3080c1b030304150203190b030709050406140c0405030714060f0a0c050c0f0904020907020708010c020f07051203030403050313020907030c170f0c0a030e0303151302030106050d050c0706 82
    0x282c0d041aa421244805140c4969440240c2c90080d244988031090004249800c10045040901030a00086400d4040c90a020031102e005002d4188034901418020954240c9011000340d061002003011814007010700040c4034958002c51100c0454150545003400503034040002401c3c4c3c4203042070303c448200300048103040d1680041e2021900c502038001c0d00c5500c410701e4140300d080c0c12500c0400b68881903079000500145800050301d50820107030320484048546402c40c0508460180d028200580d001c0000e14204000c00c00107103000d041d0645003186001c464100d011355a0001401c020140100070000131001c04030980d141c03a013190000c1c061841400c111402400415942c046400000e100b00b404420340007403000c0c03903400340e43e045140d03407010380d503068034003029400c180c408508058607074400c810a14001c002850181101000443d03581000702d00700200840b203010300d1541980144010844c00e034018058616400e1041b2022030703144d4444044e403a452094401c0209564a00900090 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 77024669 1250 77023419 77023423
    0xb0a0207030b070e0d06020706090c0f05030f01141302120d170c03060a030219050a0e0f01171f02070b0708010504050108010902130207020301150312080109021603080c1b 75
    0xc11207014032070006440c0c84544048900c0d800c3c0300e07151500300c0001c0107480300041a03039000b00200750007a031002583c0342c1699201120b0048a81c050104004110414800b80c5001e1003456903511186000b00612071b40d103204110a40c4004000040c0001990412421754035150364a20032015414140e45121844a5010741810200b80001c40a0308900c00003400e5030204030200da0255900400c1ca00303049246608200d806581d00704100c18841c0358080010700340d22403102003c0134200081605c10945402440c440c42150b0581c4400c900d1301c04030300030307030491040414404248517101d55982e41c1501501c200002074880d02c0001400c400d10481001080340d0303c441624183c5800711000d026a07640d13640380600b0794a140340d0182d88803d492014403c4a01e0130ba005101591018002142810440020a0300ca62803076009a8402103010801c1000130361114006001d099021411410514081440213604d4030031034009041c00103c00100b40c40c04884000e44e040810004a1300706a030494544183d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 77025919 1250 77024669 77024683
    0x907090b04090e06070c050a06050c04170a06140f01150201060e1501110303070e060304140303091006080601030c0303050a02150c04061202040308120a021606051e0c03010603150b0a02 81
    0x3c40a0003240c0c0407485080c422041143c0300f03034128005001e500c149464650080c40007800703d80c8456420407000a81c010020300c8034148122407030240c42c0003240c90805009844400e05041d100031156001c010428000b0712046040d02e0417044400052045c0032002d81c014040c58010301110318000c010000034050f0b424030b00c01044400c1e03032181680c0c030828203801e81d2404180d4a02c0c000c12244c0303090b0308140c2444ca01540e0f2280c0135010b0605607060955100d815940166001d65103500904040201390000b80540c100404400d4014100c0b50700d5925410484680342c04001c041090014410070041d02c20000c82d04c00e52020600310040d4108210300c640705c1da019104250101b07400600c4454414800c0c406e8804403a0046513844c038010b100400c900070070074001c0c00505829820320442660300e603502c07030300005170740307c1e92000407a420041d08902103118038803900d4003003007100c41c100608240540140c0341112640d0401103103002900003414855640b40c1c201420560001c240c0081d169030016841c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 77027169 1250 77025919 77025941
    0x10504060f21061d0c1f0e27010e160c080706020d0c0203092425080d1505041803030507020a05060903130501110a080702010912110301060b180907090b0409 69
    0x1d03a05151005d0602183c280c4900d800109804026001003800d4040d02c10500c4841000340a010075218485040d034445d5101e421a00582d030b4a40014070506600d000c0d15a00920f034103501d081c0ca00f0684000a1596446a900500b04800480c540b82040000d03010340740d9410001201703104403003440c00002e40d2904042c0440b481040c0c0f4443c0d004204a0b034070380701040c0b0300c40003416a103400f01c0e100c44080c07d154006c0100d0340014a5000711000b1511404c054a8206144c1c0c2e0b001c96042c11034401c203513030719149400c034910891a00707a12602040680e80800c910681c103040c081610354424600b6030a01c00c90000180c454010384081100103d0080010318070000c110302150b070095280c1c0d004480841f165080321555a020021001c007107440c21001d00031b40380c0b051500b9404961280700c0652840d682c9101207452080d10503042c00a443e0030f000d14000380060940e02d80c1858020407200782c0e1456009503c034014280781e0b000c070358941d11480c40350014100d5402c07001d41d6280d031100c1543c0100b03000c101c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 77028419 1250 77027169 77027173
    0x100309050d09124214090a200a090b03071a04060507150606050c0105060301110702060d020f030f010602070b0304030801150216081005010504060f21061d 68
    0x880708124003899a41c41542d00c00710142c0b103c403110b940c0d034901107190080a00032020769582000701402e0070b034000b0000c2c03002c101c203040201c2c12420032000503219011781d541c2d03c2d070101c0d2003013200150000820000040d00411450f000388440e00d0f03e20200f103200030031503030072043c07080c3e002c14180c0f40da401801030b6410079011110307116034810541440d09011800c406503013900b080304002c8107100b50080c020b10780c011200d0181754907401010354110b44035540200003050340810445000e02d828400c0903880072041d002841004803020510200d0300c02d0071170092142c40045554514021640d0544480710601c0e00365070f07600d003800c0d110811030381001d100d5840180714080c00822003031407010079070b4011076145d115161182d0a00f00d0301103611142001100c02c5101d401409200346c02c03080052030051814101800d0b180b40e080000d403095442c140c104902075410007104001c82d83d0342c40d402c441140c000c8210380c4a92440c1584080e1980700704000503040c241080e081d011724500942d4550040050070301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 77029669 1250 77028419 77028433
    0x40e010b0301030c050d060b1c14160b07060b030105040c0810090819030b03070e0a0e030705030d0b0613180b010c021e01020f01050a0204080c06042d0510030905 71
    0x810000300744000d0000400b001c1d0021000c0025091011110102500c10800800d000d5003034008a900590444440c0369004a015204424060007501041143c00120b014200f0b1b80b042603815210385050703101e11407003110001005014040160320052441c1c0d0014000e1101c1d08142c10040005000e0317015039820303402600c44110400d0400d1046d4901c680d444030529050010900550409150601e517038030901d0b1f151084000d040d502446100044d0015954010345030a000d05c8103803c681c3300d40c900c0d5602ea4001c00c0b01c0da02160000098500d0b4100b0340c100498814a1034000c00e1550048101480c4219104403000c45c2400211081081c05011890200110308090340110f621011207100a50031010848041c0c10310400d2031405810000c1c18012036403208200c848103030071954100c800e401140c4c0d0224043c041d4510921402c00114012911035003003d00b401c48880b00f079039422071058000340c1801c0c1000203403c60009518000c0400920721081c9040d01c0d44041c0180502c844110345a0007191 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 77030919 1250 77029669 77029679
    0x20409020301031e0c050f04020405030312070e011b080c15040609020103050c120a09020a2c010f0302130c120609020c0c04061505031503030a1707050307080a050402010e03030d02040e01 82
    0x15641314071a40c000c80c9080d1401d00d401c0078040000c074002c03c015081502004007050f10f885c10001010040d103002c00808051a244c0f0740200000344941000341000700180039001241601d0310541d200a4000003070694805105007150302e80f0010b4040e0640410581c801c00003403020030351000070810b000381c8041c849035072842e10892462045c13083c0a10f1008030203010030090390440e80235010007031014020b041410744441010f02c100c0142100040d251841c0840b44000d01200113180d4010700a410700085100e00719400110b00c4144569000c1400da078818402c42c115204103c4200e444000322000c00c510703501e035500d902c041d40c00300380001d68500c203416445807281800c6c46410126801c1d80c2100086078107100040b9060b84c4003a200703400c3c543c030880800d0000d039001e10062030700c00681c3d10703185064954000e004500c410020b10002c00e0010910400c07014982007065540e1011050750001602c4c2d03074520060340d0324040354001c540c040c8404030b1448a51f101e00e80c001d005584110b0b00041d000e0380d881d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 77032169 1250 77030919 77030963
    0x4051519120e010606120c020a020312180904081c1103070903050607020c03030f0c0307150501081c021507050c0d180906030210050307110d0801090b091005060d020d02040902030103 80
    0x28894000046c0911a442a00d4a2070b0351090503415101e02c107231100c0a01c10340000e03151003003006507840864800110b0510001c2c0c40700964500050950b0864090300d0591100e03107250041049100c0c50807190074819804500030307444903045480458446d0b44a042c010401425420240000c541e540300310404140841c1c000916503443c8400100290310b49000e490130710025400c0f000702e100485c03105025001c0001e00e007003164950340c403418100003030540c0341807446484d007800700b11100403040703000a03103101196003c541a000200042001c0d40e041d1902072044800f442000d015601c1c501803d0f4001e1030071980841108020030441c030041c4840782e20340d2041c0d01210301074400254000d608880d400600c500400240d40d00c130f001820205244589000708038102400540b08100017030f060700040c4098050740c8501d180b916000d60743c0c03030382d82c0c87c1480440c044d544840c05001c1c03083c203001c40d10825516141c0c044541c05e43c6450015501c495903000460b010f504280401c45540940c50030782c6107030100c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 77033419 1250 77032169 77032181
    0x206060423010501030f1d0309030d17010e04030903020315090d02030a05030f060406030c080c030d030b06090103050c0f07030c050706170a05061504030f0b0a0c0504051519120e01 79
    0x21907000003080ba46490019002005a185001980c40d00d4a0030745d05c0c6401c001c84c8203041443c003000075590b01d1260004040c10941e0381081c950502846a0405610b04207810b0480d05541002404516540b00c41c10b040e5042a100c1c2d00003980742c8607541c2180044041a010349000304e81e010104c482e0707140070403000e980324040c03030070081c0000741c042c000601c502d0b409030740050300044003520002e02142c49481e12280340405801190302a03029048420050a040080c80c03442107072860b042101c0b0b01b01d00b0003c0d50901c01c114200d41010344a9020840c2c0c01104000c688507284421000c0d0341e6040e191402030180b025501c402c0d1624010000b000500d02e00070210240d070a00500690040c595450300d00da0002c01c0043c080507040b0300440d200203058600c203070041c4080c6018100c204452201480c010a02c08801000107094504040000760001c2d003100a4800f5103204803900c01d18005040031028040c01040c00c500c41c40488407032800c2c032058108007903c880c80540c010070b005440703009000f02d0903920 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 77034669 1250 77033419 77033471
    0x9010c02010318050a050a0c050a1203050702210a03020708190b090c0406140f03010b09010501030902042009120a050a031b1209050a052b0507080a0302060604 70
    0x115896a8800562083d4014600c50703038500301c6442c0404070340c1c403118038040303117501e007201d0b01d0b4040d8030b900003480000c407819402441c8c11200b1060b55400c1031000d000022000c0401070900034085151401c665500300b00b040100e000d10703022003000504034005503443e00d149200350007600072508046a55240401c5074442d0022200150150804503030312211051001403850f8103c0c003071464084c0e41035846020324401420314103004c54400008804000c942249006a0b41c440e030314046000c03882ea00c0e11498281100c1007400c3c0022031840e2400410098030402c01e11501c40c0080000740c402c0134100001418440009644c41405080e10081e1a5aa4962446c02500070380c8026401400688a500c1003030940661400080e64401c466880d802030f0501008010040b842400040c081c9090080781200240380840e4520500b2410003c042c82604240c11000b40c8008403042e220700f485404c00c4040001c1100c0b000300c498080c1203060081d2921815948030348a03034240304500c512100000d250755100b207 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 77035919 1250 77034669 77034677
    0x50f03120304020d022205040b06030d02060a0506010909020d14060a030b010b1c02031312020106180b03120309060f0c03040b061908070e010e0f010b04060f09260c060901 75
    0xb480d603400300a145000d01c1002c90340406c45d00109220351030f440d502c600c12070200c0341c0301140324201362500815820780104040c0c080ea01c40e480e4001625400038041e5000301d0034000018841d15101c00403100c42d5800d4004043d020300002c3c0111102066901444900c2c540e14039241c150b4840703004111291105200281400030741c400107015007900724008207200d8202c0d15243e410f660f5020034400a0703800c100e0b0300c401e0341c0c2c1411400b04140b200020740b1808400062000b08011402d004040b5816041e0059641281751b64024501c1c040d1030401c107004511514004458807403038120744040d078039042150a5a031003d490004100c8220b1a14260790080341d1186180082e695100c0c18040c0703803a10003001e118444910600010b079001d0070310111002d484c21280d080410340c102030580c40f2101019107150140b401d4440100001c00f58441501c0640d000b034a881c4186100c0c1d010220b0b40c2d0f02c600e40200440090701440003402c96590401504480f0250060b00e080d01402803c02646000e4424614041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 77037169 1250 77035919 77035921
    0x6170a181401090614150103020a020304061b0c03050303100b070b010302130b090a14130201080424020315030d0c08040909050a060509300d0c032004050f031203 71
    0x1ca0928204000c0a81c0304000903420f01c940e100d201c03c2e680b11000040d92901c120b42480420801d113078000c44d490700c003804c0030342c40c000318088000e5980c030591180104100c0780ca41260082010606041c0304148c1040e148042c2d1134132414020313120f0740191104440e059404000081180502c1c7c01d1324050340d001340c600c0302a0780c82c2d40c00780070010550800e107120207584c584d460341d00340e51100000783c003c0018800000c0c0c0c1c09401e080c0b91f01280c201402c0071204040a084000050381d01c108660350155104d126404d200245420780c4890b1480000039102c218000310402456660081d03141c0c6104d84104e08803908a007001c90180c9051240c0900945080340c100070502448035543c114a0b180ea02c58012656840d4140c0c40c1ca07012a401611b81c7d080c5c1c1e030040c0200002240000001000700704164207203a1040b90140b40ba03803030910807480b01541e645d44921584884a0103035005502c5440d020070406034292611501c00075603402805894800d028806d20f000c02800c00045074140310200701022451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 77038419 1250 77037169 77037173
    0x9030503070b071808070b0307021905070609050108010305060604020901020307050d0e1807090b0913060b0a03050108030a0207090c0c050109030905011206060c150225020f010c0803060f01031506170a18 89
    0x1e1540001c09c18829031140050008092030341c468211030301c50084025110160600d50020b1651000e988954100700c0180700500c081032010449680024003200c0c01a03440c8220b400503410340c01280c001a026011310f0140c1004150000240e803213044048820b2404100c200d07079411034903902652000001080c2c054240a080381c00c1006080e4600d00828010b180034145142c1000d03036a0f036802484410700c0c0843e20515003078041c0105409010b2090196051000c4000300954850b4284603040e40b00362940f540c0c0c441c06026205000105400c00c0080c0310f10764007818054050300803171180c3c6000480b040241c00980d5040e20070481650300726915046200b81a031100c1543e00b41c03012806c00c000741d0030000b01707a64041e1070000010070f40c011414103140c001d80b401003040114148684c00d041c040008051000603003c8d5080b80c0e40f201040301d4442c140030f4040f00403002001041d83d1a50a0704c200f010224181e600310236850402d000c0242c809401c1c0c0e03202034004065039100e00003240d81d000503040340700c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 77039669 1250 77038419 77038439
    0x180a051305061620010f05010b0406020604031b021002031801050a020c0111120a020a1205041401180b040603020d1a06041a0f03010f080d080c04050d0309030503070b07180807 77
    0x3d000441490114050011040d043c0108901400c119100da07543d003031034010114440c0901401850400d0080b81000c0c41c0800194030781c40014001000c001440b030001d042c04224400c03040d00c0b560083c191070080d000e178000c041d41d25848000c1e8450074031581c03541032600e5840340b0b080f1031402800d6030103008540c4001e0010b4505a03c800c01580702e038020088112410609400900003002c0c190340104500071480c00e10102088003420140108802000140200588502c50031040c5400786040c0101100003180c91030140482e400040d441500003800141c07039545a005480e41038100101007000d10340603610820488282c154240e00100c09100030040380e03040a501c10b225048009130545040c24510b12400b441c2e00036001907413420388200c8144103a4504110441e0940e4585c104211103040103036103a545e07030186100e4684a0725034545e403082003503c0340c04403100441d0f00c03401302d9071104914a405421604100d44d4500010032000617100204000c001100c211282540940030b52401c02003000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 77040919 1250 77039669 77039701
    0x1a030309130e060403030506190311010e131103060f06031608091e032a0c0f130f090b07020703030507062c0a061107080f0315180a05130506 62
    0x291080d03a100b4091a400d4010b0050354421886944c00081d1490040c04000081e82d0310011034604041d41501400000c0c036807043c540801d1000d081c10111640340b58006600c03480d40f603680481403420a00d492210b0750820703000d18000d030b034101c50400c0c40315042000e01105010403550604040b03460103206034010300422030250484000b5007a11410350320002c0d0704a42c1d81e80a4819040d5500000e2440445221242000500d011420f044840314503100105517851548030360503480790b0f407912240380155860110100c8184060102808201a8103403a04000d00b2011015510345035480c0c00a0320390f51011501c2d80540e5451344443c0c0c10000b0070f4a4200042240484420b85078451f00205004400000d00075030303070004004002d01d40c0065600c2c03c83c1c141c443c422804052603006100c0900000c0b9007209603a54031015524003500c030354600c1146624003203506031680d00051915203040a44450b00e914900c1903080c0c82c8240f00c4e5844030003d18450001c1520040d05d0b541040d000300d200c0c1203260440d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 77042169 1250 77040919 77040949
    0x50a02060402040b1f080a0b0105191215091a030a0c0306050405150103121701060e010c05070515070b011a1206130e070501170610141608040302041a030309 69
    0x5140c0310058903a0017941c440d034100c154404180c0c90800c00000c40c1c402d010301160310b0710a10700142010011140c14582c225120707941c006000c540b03080a070840a10f64448101d010141c0c0c00c5001030f5a441000900a00b03000040d08403c070303600070307103071304a424000741304010717035601510305044246580c03200001000054811141030103122801754144620008083c0a9401103603100c003050089000507042c072890880440d8002c0d0080010000150000314800d0907030402c0c200f04408020300e20345181042d034140c001c00d030f101d080003503170545529900000c2c02410f4440c24081d840e60740c0750092010400524103070260440d404020080f5600742c400384841d0012400780210b020980102441015501d6082e03101c1010fa100c07160030402507920440c0900305860b40d0034105c0b020b09090f000700e030300700aa030320b400000c0c804060038102261040008036042800e1b1104030340d480301b149241c04030341d5520078401648218106010b0303140d09524690301c40c0542100034019490b02c4201c1c800d001030407801c9009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 77043419 1250 77042169 77042179
    0x20703020a030c090b040e120d020d050f2a0d020901020c04060b03090d050702031b010c050f0a150203090c1210051009061a07030305062e020607050a02060402040b 72
    0x400001601c50705109000707580b08a03240d10000e401d0800510882d001d01c0345030384c411814122212400f03580400d41205003600505c2c0c07255036049051442001e8410701140700c030700e1498001044512000034903030b00d009640c00c041310300541203903400700e202080d904400150100e104102d4200282c4282d401010102c40600503100c0c43d0680c00b0004048a48a07880000308101c000200b008640c424008070048014500301942003030041c0d004a03645165441c054900c040c0b00316000502c9078000c0205d040700079800310071908005444030910380ca6440d401003c9070320380d80341e9240c070000e90b80c45c0c002d8902ca03180c0c480040c000d8080d20010041d030700000c100182c42a0048109040548400e8003903944149074a4010107581890b119900c003c8a1456011019035001681c034040c070542034100300c51945030036290200d140d40390600002e0300307919001207004803000003028801c080c041c00250a45051b01d0303902900e4055413041341c1a00c00f480f400c5040c40058000c140043c0041c98540e011401c1100082c00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 77044669 1250 77043419 77043433
    0xa0b0105061309020c1c030c02030409020903151e06120a0b1f06031b0305040b0a020307091d07020111031e0907030503040b03390d0902040218030c040e0d0f02 70
    0x803922003281d210220181190f080801a540300d1b454104102640c41e80c00c0c5820000d100440030025103a02071401390b403c030340d50005040f21031540c0802410140c6241103820360014106620700b48030300902d000c50b80c10000701c54030005041e8507003d00100c20320622440582103080c81a9250100108001c00e1200e00041d441406210036021100e028041c150544001549403a6280106035003444d4148240425040c40108030001c0d507010303c05600b01100d40ea000d0380366201d5120640700c404882d00b0241c1200507a410015041140c090301038041e44850b0000c001100d90840040d070340d880103d8414074459a2884000c1590070502012603000b207000007660030407034072952190700310b0707000d940703c0006450044140805a1070740303688210116020710104124062061415000765201e6001c003090b8600425004048041900f06540140d401441159944d82030060440b5034200c0705540c60113841070082482c1c41c2e080c24464030400c2007400307004012582d00714504840c080001d125440031806003903 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 77045919 1250 77044669 77044679
    0x1050112080310150c0204060803030c040b0703021c0509040f0903020c010c0201020f060403030207120816050f0904050f071202090a0e06010203040b0c01051602012a0c0203070308070303050601020a0b01050613 92
    0x2c04c01048915580e120412070f20b1500400065450383d0704a10350700d070030400500114000c400202c408035010340d00110b40300c0790b0b12b05080c0c0c100340c00c6401e0001c000f51401807115580ea80600144cd16007001c5800308202c580b003050520450f014a0f100030096031200409071219800b5034141035103244144120b564880000c40341c582804401d0f1b4044012a4020840340304000d0544a800b0446409140040ca285094883c40f0400c0c0e50351f8818a05215001400025407100002194480b030f00c09002480b40341171007020040454002c850200c0090500c800e5042c81c3d104038002c6a82c1820300800c000052400d01024240185000e003401b4107500c02040005440c0140101501160703504c0d400020b8549031a0240300c404c003950450744011139141070101d080238003c00c0041c0b0a8013604031484080c484260780141c0b940041e60b10f0196041c412600c1c00130400c0200c800801e0910300c40d40e000e0003651120300059036a4a41c1d1000204900880760042c052802c050000c1d00c1200b0480058038112a611 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 77047169 1250 77045919 77045939
    0xe09070e0901053903060609060c010e240105040203070909180c140d1101020f1009110913060b0103060911030109060902070804060c050102070605130507230f06040f0b0a030b0301050112080310 85
    0x190f101442d2b50f51144480c003824a41403007074140c0e4005596210501c410320110740701100c441409014400e6602001045c1d01030b214990510103007541c010104460740543e10295005600389500720f80e100350440007c60b02031001c250400040f4405000c0a00b070ba003182e0396907900701c608000300d9811403041d03680902c1172030030402014445000305e440010343c4684604203581d0580c541041c0d98090740c1c4a5083c80f02c3c0180c42000c00d03003090b411100005542d80c90000480181000707030301c258001400c01034480e1103402104000c504881602ca01081843d80c0c59500c141680540360010f0702c11901404100f082a0088142c0d22050340300e032000502c0c1c035005d41d5036042110016102114840807090301c1c24104a420407109000d0512030881c80203541402e0306841e00000c18058003070160014006090054485000b51809014490701c0346581d1034440310241f20680241c0d031643c001034144000310806040c10705c280d030f05860301e040c0341907411a03840e00e0706803050f40b01621040c43c003007510070f0004080220b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 77048419 1250 77047169 77047177
    0xc0402071416080c0a030206030a0b190902040e0604060b0f031012060b01020c010206040203060a0e0f1522020f010507080d05010314010e06010f0e09070e090105390306060906 77
    0x52000c2c101005070901044500d810700a03004140035681020052000d6650081502c1c4d1003a5603c10100e103c01580e00070a0b00c8400108240310380300c20010b000315824910703030054419503000c0100603519558060800098680d14411090103030010085000c600900700e0007141c3c00342110400c07424403035551141280c04a060803050301d2140e552140f078404c40d0780c10b21810841120034401810582486c0c5c0020b521030801500d012902940c0d090183d119500520401000d4103d82003039801c881d41c7c03a03041000d40e43c2d00303c40f4038540341c011030304000601440c07031444506250003800b001400d0070311800644041e0f00441d4152035840050000207407580d46030184a01071442031900074840078000c0307511070a40b101002d08440c1c0e6001180184a0810300642c40001c50f002680c401c24507866000b000d41c10550700f03400480154103000f04211040c0c0c0c05402c0301d40200030710443c5588130003984200c2c03140c460540c0d0400511000c08840142016040c0001e503030800001041d45160551090000c0e5490b48 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 77049669 1250 77048419 77048443
    0x11150103030201060e01080c15180d0501050103030905010f050f0d02040b0a0903120306031509031103030406050106083301020c120610080307030c080307030204050a060507021f020c04020714 84
    0x34513a0014001a8100d11401e4014400d0710001c22840d000d15001a24400b9103481500d00031078041403284e0030101205c00d00c61f0b8008003800b0941b000005007070181c041e041c00d0000341c02043c0d03005000507030740d40325908140415010340d44081c1001481d0b8440d00c50396000302080310b005902403001003406034080780100750426080c0c4135090f03150324503e0301d462902d0050000c40d0926140000400210b0074142d49403001d4010240000bc40b555985011340e200a000082e419151101004202c00c0110340d60100f41a941c99407070305240741d42d038016144200030108007640f011140c010b800034841c202091180c21860070500650f44000c0043c80400d514a01c00701d00009560301040c03d1100b00f150301d05030903001e41a0300014501d40106618003801782c02000400810308540000000c0d0060700c00c0d1b040c2c4001d000e005044183c0141da5a100924540040c142a407160110106002011002c0610000c100380903030040e02c540f041002c100030082d001802c0a650b2140e0b810a011221101440751a110b81 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 77050919 1250 77049669 77049671
    0x31203070915020319050313020906040204170a0507091b030e0708120a080a0c0503040f1403040b040501120605010905060d020d020f2205010804110409120e030d02190311150103030201 81
    0x103480c0341c0748403040d2945c11410521108000744800d240b101c101d8118003035019103051090351038003c01303d4000d00c01d41d80020348250420701d8407600e9110101c0c0801c0c8450261007100d4503291141401c100300c0d2040030529501d00780241480c0c100c80c2c0260060445c4135107200c1aa0005552030003068100001c0001d00c01c0b2420001810360f0060342c22002c000c0d0000c400403000c104110103104c000c1c1480c40302802c00f602c0d08408a2845041060040030300600d0443c540030760f502c1d50350711000c0c0c46064000f401143d020919484a820340d01000340305400031903405a44003038400c0d00c0c040602002da0f100701d000c40560340d000c0140258414884c002814140036404a080d0740d2485d021030700000d040c1d15456100441201d000400050380c0c070950b23182d0400d4010404c2c81003498894001801000d2302e020080500b610341d4291600203800081d1910440e00980c00d880e00c680e0480c3c01261260308403010962952420b603050000b00b403103000b40906150880d030443e41402e4114600d14100e607000da00c200c00627 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 77052169 1250 77050919 77050927
    0x215030117060103050a06020f040f0b090f1c0602031306050f07110a0302100c030609140105011806170603010b0306040c08010c0f0509010e0f04060303120e0a020312030709150203 79
    0x241024001d18610003040e002e00860b50465640c0f64076207001480141c41c60380c012540ca4200b103084001c41e0002c00c44100500d100350b03074840c0815400d4105020031071084890500c84101818144503410054511004a440d140c20541e0768074020740024000302d007043c0341080000d0000d855445081d0007042070040b1140e00b880e20070310003841344180030342c100c5098001070b0003840026000a41d020302d20644081c00b083d42d070940e6004400800382ca60069031824100007016030008403071051241a41c500b030381c1d8040c0718614860f4180768030026103e031700002035500b5441e010800840a819402620080c0003250700412503001920f00001603c040d40e400071b240700e0810000c4404d1284045040c01c0c0c1c14105200c00321100c001d4800e000d108074032814015444509083c595508042e0451024000c0041140da0340f03c4c2401060002807050200000340342046811001d4400070300824020780c0240100305801e40e0f007044503115040a03080b102400261030000c100c180310f110214081d800742d64010354407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 77053419 1250 77052169 77052179
    0x19050301060b0906040306110d0906020a020708030f160204060b131401020a11010804020a09060611161203050c01020f0f0702010e0904030206010911090306090307020a0902160609080702150301 85
    0x840c1e40e40d40c40b031501c0344420000c3e100b464641c1000c1d58212504620000745030b00d4070f100181d0592064054001c89545440d0510b02000300a50117410102e03416400c0f12142512410000c0d41c902c10039a10b071001120921a030818500940910140144003410209406649005070701c1d10350480200f4800c2c003444a9028809a940700401d41060403091000f40b584036119141c5c0b4800381e501040f0789042040d001300140542d10f41c100f86400030304a01504100d000c1e9905802891310120b0461482203001e0980c02c000485042280c80d0300382c48440711010221501640c0c00c0d10b250b400102c209a00d0b540a00032101460916005001c1c02040b0030364040d0342d5401c0f4400108400600b500040c450312480c400c1c440441c0e030014000341950142c000c0000e015075441061821802070908030f42d4036114031420004001d6011003c2c2c00d06510a46005d101e9035102d20282c000c0c0d000f690640c0f030300c4d598241084c84c0444c0490f00b01e105051b004550151400d980c075000b0a425172060180107103890400001041 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 77054669 1250 77053419 77053421
    0x13050d03050301150813140a0b0403020610050405100905101508010501140c06060913020d080d0e2a0402070501020d05180d050313170c01050415020316030f0b19050301 74
    0x3900e03044c6490320003002d16200c105040c0c900c04201014201e0301c198030000c02e00000c00c01c56545401d13081905207015180c0340c60000d41d189000c9441c2d801e0304a081b1000a80ba0805004041c0910200d070600c140d0750381480305010003020000d24450354400942c000088007052003202c20362017031060359070503500e40c1400005001c0b031003002c618049182c0c0402c804c000e030350710100d042c64220408540314151912171401c07580c5050390160000c0c0d84001910400c40030484048000d00c007800c1070001c14003882d600c0e000c015484020303411402040e040174071241c0104450341c1c04035034041c02e0300800040c140fa440380c4400f400c980010100720525540c3c0c01c20b0060700c445136901c0980300000b883c000c0030020002800100580405407029510118180c00e080410800c2c0354480d08900140704410348071482800c040d40a48829103040d20707101449010f80029250900071070384180e44e0b4803210021043c409004800034000d5080c40040c41e5aa4510110300b660340c00301000021a0701c5901703000301070410003014 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 77055919 1250 77054669 77054699
    0x1209061b071109040602040f120b06010c1a0619060302030414160501080408040909030503040c0501020109080909091e0c01020c09060d02060a0201091205220305060a0213050d03050301 81
    0x100d0000c00d0003900300182c000710001001180556a0300040d80f12840d05201174001ea4000d11002885070101045240651000d5000540101034415440e21389000546041c001000054180d02000e40030b00a04200601c10903004040500020705070700b035501080758000c141c0d4101c1e00019400205105c117203c20b504500440b1405000a001460096162641900094402c0e80c0c14414040d0000d001e000a00b01603d0003003016050900c08251240b5000781a507004560840d079090b0703441c83c0440c1c5548144101e0481990002d2240d01d000c48036001c010b05404010484501c4e4851003030540000607501c03440110b641c0342c02c0004c00040c0c6006001a092403640c020050160000104000c0c140d500c460680071a140c066170314a5a42c1c0d50614101d002d00101038001d860843c01000c00b070304c425840302c02003203884810711304160000e80041400480d4074280c403000c0d02035441200866200c03d01b42e8024038004107901c070000111a40c600c0421522460510f050300801d401200411100c03004040e10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 77057169 1250 77055919 77055961
    0xc0a120c0f02060a1104170705120a031103181309060e0313090b06030705070f0f0b0402121902010813020a030f030f020304030f060b18041506060215041205120906 72
    0x14800149448926400ba0103640302d90312800080031100c800e1f0000070300c014006400003401c80385c40f451030000000d946000c0d6000440016540071140c4491141c04400d1b100920311801200300c5400d0403c04119800020746400c600e003035610144040015120700c00d100c01d403080140515100c003d16621940c010000d42c2c0204040c80c10400c00402a503582c10480b580300f44982021038480c40e1900304404107448000c0010600306003404500c0a01815400c410700c194400c0311882d071031070780c10b50784592105000703250380c11890340e000c45074001903000340c60722607003c41613441c00c0c240c6150f16000900c40c1c18542e40185d44c21410030304c1c42000d1541c40310980009911a000840c44e2610319501d10442001800d006030010380d41c0c40f440c50030755035066007945400d00050240e0086080c0b50800110040d0aa2584060540b522030000b80c4d690002c80c00b14a8011241c5d0002c9aa68840d100d19510316541040c0b00300b04002080220761080c18a0007290096014100800c89854520168400c0c0020324400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 77058419 1250 77057169 77057171
    0x20418050c040b100e0910171c030b0105122512060e06011e050906030115030c02070501050d1806050702070801061a0318010608030c0a0312050603060c0a120c0f02060a 74
    0xa1684103c0d000308140701700d0b240c161406600340d500c04d4481014401c60b5004003d1112203c076a880d40880b0029060010f99444402505411203500055080301d004410070f601058080c03141c41414060a44500d500a1074901c61b420300710741450303c000140340360314a042c0114403103e01104100a1510900016110205c102007541c2003000010f490f60b0400e01f220358a00c03100d1080c2c03601480c4960f00759500c035903020704000d0300ea58650741411348140f008485000004c2c90542820701f02403001440908450040e1261450582d1011200000e0300c010a1068044410259824006105c500c9945d2281d00070703078040d210b907a04014200d030a65100343d1000184000004241c0007a030040d4007242c2e0410f11142c04500e4401001840602405965011038500c0c040071401e501c08010110300b0f84480c034843c0d41c45001c1803d43c14014000c81308182d5403507403d54000400554111520401480a22170600b030580b0380c1c95144100c03806444e2444000301c00600b8003007003909610b404110050f007100f44c20038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 77059669 1250 77058419 77058439
    0x406110a0f021e090c0901080a060f05210d05040f06050703020c091330021c03090f0602070c031e12030b130e07140a0803040302010c020418050c040b 66
    0x341c0840105000c40064441c441540070a01e03402944900c61000362405003000105181661968a06070440c00c031b1103022900200c0080d803150100d1003041c0589600d065800401814001886a48480136a8060107039040b65040b60359034404001810400406940b22583c46040c800c03c014989401d505c104203001c0305004c44000241c01141c280c1d0502015075840c04aa81c85c81840c18004504180c041c3c030300340c00d41c040d81c4a0b000c0c0d6919040c41070305003804800050345507040304070f80d10704110b01c1100040343ca000c42e20328114441e8000a0034140103140000104449486840880c0d0040b6411500c043d150981002040814000004850011605040d010080f91103020091005202e036900b0969200c1090009645402c0e40b000302c10009181000141d401c5e0540307a945204c68007504000c20400030b1501100d280c2580101c00303440c1e400011b1418a86540d005590400b0b190804a03030240d19a809894541c030404003400195026200070308103460b00200380310446010980d00c0340240541d007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 77060919 1250 77059669 77059673
    0x6020d02060106030b0604090e06040c0f0605070b040309080f010c020d050306060304111201020a0c050105010e2a090d03020c09010905060a260a03090f060201092310020309030406110a 81
    0x3003081e504640650402103405850500001d00744c0c80b49810072400c02d480e0807480c866031000080d0080c89184544042e0140944551030108005154412000016001c11840d000504054030440e003051290601c06d02090700d03110301c507040c0300c40c000380c160541e9036a81001c00026410401401100c0c07041c104185181021004213155100090014100100f154616051500d4000301714400703d8006008540b41d552802c401481c20300380441c190380170340c01d040c000703d4a00c4648075024010041c06260700c0c84840c1d64846840c501111014090034484180a0041c454840440c10034416100740d0140c07074181074180412140b4007042c0c2001a00c80e2804040094948800c014241070b5103075036560a00c20099440a1680c80d18445031020745800343d0180e1000705900201c0c102c06942c8402180f48820703407160b204a00300c490005016002c40021881f00c04001416801c4408909000b03050f03030030200032103024006991054600c0f05940d80000f8040014592010000d2070318046807001d00a41c460903 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 77062169 1250 77060919 77060923
    0x6030109020c070308040b09090c0301050d0f0501060e07030e1009050d0e03070f090c120504030c060902121e011a06030106050a110105190e030a140a050705031201050a06020d02 78
    0x1400340e40c140590008145050900803c109001181d0140090365240d407220b10105080d0800d002550094a840011a80c0c90140720140c034140e45016240c070310703040001e8450300c500340e403101400e40e015503031144049500c407141c620382440385043d900c02080c4440c1c200819860714440c1d0868841041ca00b0340350741c0000b031007c54840c102c03414514040b0140120200041d05268840e17000c0c94006c042030b080040ea0101c00d40054000543c5903d03100340c0b00c452868004180c4108603401400a6418525140050016404074030001e0001d00000b19180c06c42110314a070424454080340c0381c0140380b41800d100d80e4240100d0f200701440d181c2008548241c4400710301c841c04103005510602c030740403400c0c003c20b5210700c81c1e0f101003000301e034000c0c480350501c41d0b658010f401c81003403c610203070304041d1511503a2a0020886001d0000c2d60b0300e031004065092002102c03a00f03c0d10b242e0f4101f050401101001c41c1041015150f103a404654070440fa5150104202c4140003a50010056411110b4007003159500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 77063419 1250 77062169 77062171
    0xe120c10020c040e010f05010506071104020d020f07060e010b0f130506012f0d110c0904020102030d0e061503010c020303010902031e13150605061e120108030c0d030b0603 75
    0x4103480301480d941040c44180c0c140340240b03001e950810300e1304090022400d01500f2189400349500010441a40c0b160180f045900c10b403c0040d0040400009540c01410310fa8010030700072000355001402e1082c50900c0d40015172101c1015100280c54200349000312100384140e1034003141c215206826501a00040340207150007400d18640c030744e56038001624a0340607842800c25030019090b80c1c0c038141c0c01180702c2401021644007a01652082201c0c0100607809901c0d55200d00302c0c48001400c46200c20703801c000c09564002c00480c111b000030701180540c4e03407160083c03404441c1c002020708151715181e080c0d02221f84003a44810f00c0b81c1c1c1000d44003400317a40c002c8201c07410340d2142880542d603980c81032103454540284500703c102c4107000f03070308101403444040d521440c818814001840d000f0303110b05080080e03031003501030f40e548840204050102d2654200c400c3c594207002c1414a410001080071480007400309920460803608006003079441000280401c00e040c04c2c55007401c102546d0568086681404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 77064669 1250 77063419 77063443
    0x10b03010204051003090f0b040c29040302120c1306030302060c1810050720040e01090512070f080c010605090a140f1816050a050301270c0918030e12 66
    0x82c6d54190002840920201b100c038198000001c0c0e04103041c5440c09880c02407803407040c4544070a144084000002240ca082180500c6c1c1001841c2068190307020007003079000791054103071640f00e0301d003480c0c80c1503c030310200076100c0807202c20010b0400d14506001c0c0c00c19a004141070b000030010081445100700e1440072008012007031b180e8022420320500c0c00d03195445404800b420142100d07456015902030044640c0482c18280c038203000041030302016074280e40c500c081c0240ba43e08001021044801c07102d0185c00118010002c582801080da120070402c2c2c1e2200c62000c44a07512041d0030300142c20240c0300341d5045030403640108050030020280c03c40c600740280c5454801e00c2d004020500c020a1034109400d52030039013054501100081d491303045900054407072940202840500011145018400c041e181940b01404450004c901c3c10104001008010125842d041c1010f01241c00c003142c0c45100300d48481f080c0144a000441d007009040c184903080c4252160039845e2240c4200b400105030304014003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 77065919 1250 77064669 77064671
    0x708070f0b0f04030503131d0714090109120b04050c06040e04030c15020a0e0102101505090a1107030f08010f0810050c0d1e0c02030415050a091a0705010b03010204051003 75
    0x1070203001c08411a44501e0340094901e06c000304402d0b084074110303000d030411281e04405440b0504844141c02c0c05a00e811940314010603268040c00140d4070000000341071901d0145020303880e15072a0700700300080b000c04000c01c1e02c0c441c10480810007004010000d0101c0c4282c122500380c10a45000e00446528200600c01030800c41c05180010401c00c51100320201c0344800002075481d4405990006c104101d001c030814010b200e14011100041c07080e2145040c06000705007010130f041d090909201c0b0030000a81140405036680d079440c840d0303099000290080c036110365200b60300030480b248028420901a080400c2c091200e0008004040c800500d1503150440d08400cc14a582c0e207003139201280c0182064072204504000714084c0e41c1d02401483c0d80d400f1881c41c0204268400064203e90340d00941c010322440f408140c0b10300504601030005003120060074500f00d1f030f0719910f500d0035800c10003c0c2c0901a440c83c50114a032000c0242c00e00610201ea03d06800840c00c0c6071511000a0344a00c2a07604e400c141 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 77067169 1250 77065919 77065927
    0x5040606050d15021608040306050402150c1509030c03120901110a0c060515040c030c022802090907030501020d02030106170403050306010e0a03060e15070f2313030606080708070f0b 80
    0x212200c04100c5c0e19040c3c000d0001901c9079541d042000241c07a003290304034032038194407204050402d903034000da9100c0f01208004000c2000810170303066129001600310031252205026080c0c10503010801000da401a14100518074141410154251620740c0c01b9010f80c103000340705140c40305a00240036482d05410030000f08442d143d45082410a5901102c096082410842080140d5401d50807500c103503410366007262541d207280040e890001c09045000025424085590300c0075291138440b194200070b0f4031044d288820754a0b07131800d01f21b82c0000100f481058001c401002415080702c0700b010301d03e030341600040e2285019a0010701e0b51000074040c0703040c4042a0342910441d218410382e0340c042d540c801c0041114211144001e07554108000e8041c04c007919080003e200b11303105d02d448030340b11340243e01c61040818054001c01800b4048800a040514082c00180f2078080c000da81d16000790b02613400010010b041035200c906240c8aa00051460303401071104200720031046841c001141c0d13104c4441a19 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 77068419 1250 77067169 77067187
    0x302100f021306050c070906080a030309080f071208060108100510030b0604090203040b100803030a0c05070203060f010e0714030406090f080708130611030a08061c0605040606050d1502 81
    0x20300881c40b10040034600154045400c0d0341040c01001d05003600000c0f0f4120a07a1807002c034054525502484825410030f0502d480002e001c0d4001248040c41105141d0502d550010030340840c2d00888000d880c0780c02055203180d00150000300d8250409428682801c0b5490406041c035070002140c840e42d030080c9940c4c0000c140c0781e0700c0707036202c4d0841c1c0384010002e80c1ea0380d0b900c102400c041e4005a0b0280c03640610072003c40c80d202e00000b074210490b0803440c051811035440b80e14110042414026810500c2010400c50380140e8040c8102481081580d48612141d414198106032812000740b80d101800ac0d200c0c0311103215811041583c1e48503600010214003c42245003c180510607504020906500810a101005901c0000d054484001020011820713034400085400c110141e15404107034208005009449100d00c9180d0fa10800207401e5203080044105003200c110545031040d21420b544006200422142c4d001d40c000030700302110281a10001ca48a0b42c3c80c0c070420781803492050344c0c00586000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 77069669 1250 77068419 77068421
    0x1d070f0314180c040f050105090a06030302060411151b0c040506032805010608030304050d03060f0501030504020d0b1f090903051b0705030703030c060f15090c050904360302100f 78
    0x110f0102401c203120320082000b800000d0131003801414425018000000e0300122a0710030708084a07090740c01020107032580e4032040c04080343e22074010f4005062a42a8044800c40750007002d000981c0340c0b10840740441408001d00301003208a81038030840c240b4040c480f4564001650b20041c0d200400c1c0c140780b0311840d664041d282440500010215400c7c10400500c684c0c022001c2d40c421401501540c00c0d504403844114119520b500031008008407800701809594460b90090740c0c09071000e015020300c040d458564001080c01110104030300440070750103a182603110b18005005008161090145a601d03587c05841c41c0140d040c56480c1c00c51240c0f20011114040080d04000c2102a06a0710302a48a060003007000c030202030161141400d20002030314840c040d00c80c410403507094121112045082034142d002500f880200401008001d00c2500404c0d0764030300c29840c030394110340e10700041c20040200400380403e0011148001213207500309207010070340125403500b000880302c8000400d0742d10402150 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 77070919 1250 77069669 77069683
    0x2131b0e010509090f0103120503090706050307170411040608210a0207120503072112020a03020708040e06090105060f2a1507020f0a03020a020603101d070f031418 72
    0x3d0303400724148080c00003603010810f995069038011000e4020806071400265694801502c4031691580400403c0041903c00d1000d1a0006140c0c0742c141d1100700426142c400c0000d003514255a10f8041841812051078248502c4005051200160503031080b8004021415040018603030711035480025402c00751842406520040e24400f0481460912541061642c0340c0104000b221011001000307040481c500a040c0202d85007995248a403070000389041101030340010380c06100307140e02840307007000240d156805032024100b03588017614103250000800040b600c060b0301190107000100718011400f0083c80071100040c0c40d40c10500410b81c002c04c1d40d814500c80b0035030b55400d40c0c09540b803403140751001c2034082c501400c52503003201e40000c50040340315107030140c1280007000740c1c0c0004448001405c144000d554400c012891815600c0c0e0f030780405503140c4107034510038070007001c0141c200701c0010740000c06007401468514003080581d4551140980c0c001c1c01400c0c4442c08124807100d0300076107070200088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 77072169 1250 77070919 77070937
    0x609021201021c0b330408030c01140906070507051005190e0105090a030c0501020d0c0908060f01030308220611040801110702030a0b070201091e02131b0e0105 70
    0x26069808100a114000e4001e0300385025000300c0301640280c01001d034010350130856801490001000580414145690305204001840c00580d510008241c2002000350009100c010040c50b5a030000300441421100d001e411000340698150500041c00310009006500142d5420481c2e40d590460030503a1034210507244000400381407008000e5801115032040ca407001100c8818040c103203584030803900f42d0b84219070160b040d9000e803e00201091041ca44c84031028040c800040c40c150503040b48105440c0800304103c0460107070712080003407210401c0754603486449a01b05100c1e80d41140da0050103001d028003903c41c1000c43c80d215030a882d4030001041c0f0310a0340321503b00000c1071144181071541d0024443c03e40b0350751a1188401d450425881214000c07030740240070340070b125025038801c4a0408064195030440d961000358000250a9101d41840c000e0490600e82000840d0310401c94050940c01c40d5054181c01c21220081d606408030071100403480a080071700011f0983d00040303036180070b100e0305 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 77073419 1250 77072169 77072179
    0xe2206030303021206030f0607030b040207020409030905010824060a030e1618060e060103150e09100605010c020109030212120d020301050306010e070804030c15020c010c021b01050412060902 84
    0x80001016015802000c85807000204130320650b5034603082644a14143c241248660011000621054401e40c0005603240f00104010f061000c15001301e400c03551002012000302d00b4401d0144041d40e045090990f104040300c481c090f110203580b440c0d602020740e42c1101c9000c0c04000c0360b00201c0c1d5000e03400c001d500c2c3e0080001c03603060001c0d4000490304800c481c81078070309540300340d2090300701c240e1075014880c00d0b1912507000c07024944480f401100241a07500d9100c4c1013041169020444940c0c0041d094000c108803001401e4010780ba41181c02101c8040c1d100700e040c407005901220040c1d030040b104408994040354118011088540401e0504503504800780d089030300002c10301d207074000641c06541690302c141e04903031540e80ca400450041083c1501d054021a41c0c1d0800280002d10030f00500401d13500c1800386105280708000440280d03000818044401d945403500c50400c03550400420048a5070289196a09441c03800040d20b2071003940a9920945100c8a0410611803150840a0b07003aa01403c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 77074669 1250 77073419 77073431
    0x4020607150b1002010b0a14030a0b070f02060105011106071809090309080f0102040617060604170303091501060f0509040e070e1005060306090f060d05030c07050a050901060e22 78
    0x140c0c401c014a202d6690900c034010400300b900b4998414400c40c0d110940103032400026605109455084000d5651040e525101c1c0003402000a4a0b588140340114003c2e02c0e94018084c2046019090140503004141000661041720004020005806400060710708221000105da154040a07404164025a02d90350504003000205548009003800301e410700001d0f1006500701d030314074500b80c0c030440c8505c0d0000b590080111001c128184281900404010505440e01d9a1038403c50a0490380310b621420382c0c4c10200c1004844402400007440b000300e00a4060b14560411001804041103501c2d51400c01c44045101d1020381c0310340d8400c42489000760304885189688804088910700c04a4a002c0c901c0a519000a03407820410150790040d8002420214180d4a104224600e1140200003a910912503205000401c40c2400209414403a440c054a80d0905000511800381440d602c00340c02003030501e004022241d80504a0b40b04607a0884445820007592041c030000d18245d20701041010385040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 77075919 1250 77074669 77074703
    0x1061409060313050a38010509011e050907030902040c0c080f220b03010f060504080309010f260a0605061303060b060d0c1e050c0606040f090f05030703110712080304020607 76
    0x3031790f042414072246881c2d0006c0c1c0711040c00c9034584003081c401d580c1c10a03038000050200402a408005550800071542d40780380b951140003c424040c19038005012980e9840b0345015410030b40101f01c1044824204900c20b807a540d45d903804140b03c1c61140c130603400030120f00c403180e40000d00d4041070600044051402d0040e19243e03c805140c0c028801d01400c0301125000140a900840179242116400320203035003441030080041d03034041c03210b025080811070002c3d4140c04610340d03204100f078402c0880400b2052460100c002c501182c1c0d07d9001940308440070700070b410200c400540054207503544828080340110030040450b5950140040c0d01e800581000c00805400740d100e8154060a40303101800641e086003100155aa0b10401c00b6005031500000e0000d40d41d800d098020b215081c3e510480005c010b0525120107480150071039080b82c03e40c04c000f41e60b006056004100c1c4c0300080039013025144980c41c010070b11540d4000c01e80000d220440120002d010355858400752280a81c1003100004605011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 77077169 1250 77075919 77075963
    0x3070501020d050f07050f131e031101050f040b0d0b0d03020d03050105060f0d050601110d020a052401060305060607061a03070b2104060b0303040e01061409060313050a 74
    0x1c0d01100c00c252401d0300080c040511440050700034152a00d03891f240103140e810606542d8006031003203100b02d200650010b045101c0a12401842c2191607070702c00300d0381c213500d483e0443c0c0c00c42050140c10000d0a20800c8484454002160100c03081c03810a00e5440c002c6004ea000540744a0b415258424903c000b00001e02d600820100c044003110340d81004542c0c0c9803000c0010601640c2c6148007500001e1085040f086001e9100503081001414101c03040001110003034604429608560010f8001078400360401a04002d0800003403c101d004080d06564442c000003254414400d1804264440c40402d000383c45520840e0101c5410071014000703490482e18841000e0326440d21240640f007240400500c081010302918810820b000d0403025011301c0001e001e4814070b02400556091765500b0003210b17907680400041c00100305050f40e8071030030343c0b50050152801400c4000030b039245000300500e8685a0720101202e51001180049424440f01400c20038071301440b41341c00802600c90f8011001004001e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 77078419 1250 77077169 77077177
    0xc031609060e150405090703080f04030506011a07151104091d0114070e01110102040312020709020702010c230a030801092702010c1505010e070e030a0c03170c0307050102 75
    0x1640d8400d00c8069079031001e06208000441c3c048110640b10f042d540164503142e0030480e003000c40c0b902107454046d00d0383c4418003140e10091100544c680005020003c02c0b2040c08418010903c0c170189443c204084801d10a00f4400c8140040c0460a000304440303070301c4001e504c4105001c3d6150a0503480b81e03200c0702020002c00624040c1c6034414214445d001484605009032210340f4090504461207444040c000d488a40c5074920b82414400c800c2c4016610003400d2001c3d100941c010034203100c2c01a4048406401c189603500320a600500401032900944d81281c454102c086e804402010700c51404114150031060800302e200305c901482c2000d2081c0741c2d00400320f5050390844031b020018038460903009a203550500010b084c00700d40c500000300c0907600038952054842d000380751074640300d001c884860040702c40c00d801c07823a0a80c50000a05c441b00f94451a41c449810f4103600901d2688010303181c50b0804102c91100030540341101503c22082d05041c401d4a0790107400e442201c0d21a2207915190f03010b500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 77079669 1250 77078419 77078429
    0x906060309070e070905120a031d0d0b040503030609010806090604080a030902120c0a050a050a05040203070302090604030b15090106021f060902040f03110f01091e030210120c09051c02030c0316 85
    0x31f01c24001111400460702010195254588210300c1600658580300034441984e0310f030744606115002c4000c01c4482403c544124440c40c09965207213003c1042002d01913040e0045c80c50741d4480401c110008600042091700140c003c61700a0712040b46c800218007a00145030000e4006454002000d06c4070b000141007442650211000b4125a440e101408a01d088621519902407980c5034200090308041e4011604089186009440c0440c0140410311590280d030080361103405c41c030104140c5040121044c940e602d42204c08034815450040001c0d99602c8a40c480240000b43c0040100594501c0c1d000100820200b50227540b00c17640d8403a00c0811003003500c0207542040c58941c2110140c030b000c0c031180302043c0d0140c5030f5088960400c036001031034804000880020401414010001d41d5803801d0f06d030145030066070b9030a1000307010031166080d00d112007031003024410500c8003840240d0364002c24091070750030740c000303056880718a00009181105005045405000e20140c2144c0007200355640b0b030950b1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 77080919 1250 77079669 77079679
    0x2060703022209020c0c0301110a05180d080711030105040309092301080c09090d020601030b042d030f020a031e031e05010302011706030c04020c0129041503020906060309070e070905 80
    0xc2101030500d809d17a0b40028000320350100411031000c3d13890140c000b61400c9a000c3c5e0300400d40030040d10105405e05d000714003d49042c1000300b44803007001403c00031503030340b00c806a009010604003903502401c07400170f50050002468407800342071248102e080c440d2210498803110b003050781d42c0d81c036443c6880d858031520705c034015108030000038120100020182030425495000b010141e1a6031511280000050800c0b03603150040210351480ca0604001d038425688154031014030b00504d4500507005080e2060300d0381c251b41100c1c0181d00400c0e002070010f56034140c0107150507178900f8441400c8000301140c0641e03d200f152403004092070860320b580007505a138802e880d105a42c090161050340c0300310003221440d505600c083d44a604a00746900038020800d403040020580c09944414072094556401103840c1d0001141100042e502d090700412404090702d044031300d81c441c02c58002c00c5003840d004001d240510400808034000040400c0700c0c034005c10f03a94a0840c41800c0c100002803903401c5c82d1264510503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 77082169 1250 77080919 77080933
    0x1624060501140304171b060106121407210203040f03020c0118060509010c08030a05040c1208040b0c15150406090b0d03030903030609020f030f090703020102060703022209020c 77
    0x55020755002d1140641d203154031801c0d0740c0d8079600c01401c1007811a011010302c0081c804048010f0780781d0f4200404910345009010b4560410703000800c0c0115524403000014101842c1388031400c240c25440d5001501da1808100c0b00201a810216580601e4084a00b01c0c0c8000200000d200b80d60145100300c0e8406c3d42a9080240580300454141104210803400718500c0003003000001d01030340040c9403200c0b042c104881802c0703040d00d4000241d04216102e4041e240c1ba041004100300d229248000a407080d03e0000f03001070032a0710784201c64081c0c1d0145423100304000944280f00902000281ca00641d0100180114030704400c8034000f04080106032401641843c8000c10740720002c1c01110410715014217038440d140c01e181c40c11009071031500c2050301071558a00001c20040c2081c00109801a034442906949041000b80e40d2171a042c002c0c020401034100c040c1c1403006030313404113105401041c0c3c1c0c60050380340c0c8809000891040c6131001c050355424209000081d081010703070046c010300c00d1181c0941c0d10f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 77083419 1250 77082169 77082179
    0x506040e0411010807020304060c02030a0b090c0a06030e03070209062b0510050403140304142a030705010e0105030406180f02030d0e01080606181c02090c070b0c162406 74
    0x102c140549050000d60005d10007270017410f1181c41d0a249042c0001d048500c0c900494803100c4100c50305454007590364004041c466410300380244240020a0185801c110024204503540c0d1640100003000f4442c010712000700395281d80e910100140c0f900490460b185108000c141c2d10201c8520074000c661a0055a050a074040240e1003564491501601d070f401441148940c450003d9200800c111818010b10015490f112001c1007481500c2608600c5c801d2600039500802880c1e2001c0c1d500310b44a80d0090b0000e0040f668010301040500c1020b00302192030351502e00c3d0000c050b20f03002200c1d608040c109030403d4184142007100c01c521a0081d805e4542009004a08a69200000724254041014800071403110f041c0a40280582d070120407660788819009000100340f04902d100501c80da9120044001c00d500d1700b4041c2640100300e0300d0003d8038103503c554800200e00c10080a01204541c0400c0c3c901503002000c0d20100c543d540058580e500c20f8a1240144026500300503028420b864244040b031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 77084669 1250 77083419 77083427
    0x60603070e160c0201050c010609060f090603080a1b080f070b01050301090b01170f0a050a03030510120213020f1216170609060102010e0312090d0c0305070f06060506040e041101 78
    0xb00600c1030764001011296120030036906110500012810400200010a00540c080c030401c1d0280245003400700f0445c1c501070070280c240c99039411185100d4a00001080081d0302d02c0105c0f000051241060480c0320303e40001401c6181001101038200c041c0014406000201c11000380713030507032041c08130340d0880c2d072105c0515088550514009103104464801440107180c2c680141641100711400c440e5031100303100d0114100b03c2c5c9400102c410383d110b44450b40805405001d5268081c0e84040c041c21a03900e00500c00155075a1214003030300035851701c0304c04020395505404458040294410803075466100e150302160f00c81c0100c4202c4c8051800590002c646485869446030070442d6124450301e584442e0208041d0302005000720b41550750301c0d0312400c41c0c031340144050b00c1500c880c40400640c074500380c6030342800c1c158821150400c0200900c2050000780d00700b000d4443d025040044c403031502045241c00c00050031690042e80e4003c1c0c000ca07001070003884600c0703401d104511403030786141d52500d8440156 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 77085919 1250 77084669 77084671
    0x507061206080a021302040801021611030102031e0c0409020309160509240a0503010507050703170f0f0403090506041701200403140106030206030a0903020105130201090b0a090f08060603070e 84
    0x2030200c0d041002440d025151845440300f40700d840e41070062800340d80381c00f2340e42240e020126001c0c40710f03d40d16010007440441000364078400801c1d0001d40c070318a03112140c28050078000004110703074124035001c01c0070b000e0b2000949014082243d004c55890400000700c3c0d964440343c85060000040c41030f00801c980c10448410303801010011248140802182d800d00c04503042542c034180c2042e800600007a80b66403d0003614007900d502d0712065502d11039418010001d0300341c84401141503010406200c10940056425540620405000c203100c2d02c5520b0308035825003581d842075a00a10200f00407130041c0180140c03c024001b0780e40200001c001c1030000009070324030141844681c0c0002c0c08100085200141011200d49a0f20000101c807034413035001039800e82007999400c24142d0b1326100c9204054092017520741011a440c81d58a0701259940000c03c84c148501403900b032207101107074003010980036904220150008442d40d01c2c1c0142c442c00090b41e284400c584540c804d205800f40040d802c0c5030204e0702 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 77087169 1250 77085919 77085929
    0x2d01090b09060601090b04060509010212070b010519050a032918160e040210020a05030d051e09100218060d050417130905040807060e07060905041406040b0d0f0507061206 75
    0x4074100b6281400270b99054118100007070560160032100e85030034943c00000c00c9260f20402480009505100c144003d50281d55082808029480d205002555411000c0c004999001c2590342e500b030f50842e00740020f08040085580c84903503540c10b00a0f801041e64008041000d4002116400c51002c0302469071001c841c403541420999800206015007001201004c01030003070700407188400060384e00d003442c5a2180761415041d0766103000f800001c0d41c1c0351031401e525030402c01c00c0d050035003001d204054807815a0702c1024862a40040c048403010380e01c4101d074096190041001d9160361052448030040c0c50116070454181d1b1103018909058040c01007510394608140c19464030040c00e1840c01c100808014009444030002448064005130b00b074000c4080e10200326019082c41850441d0162031121b141c1c000c40c1c41030f41001e400500b442880301c01c80303610082c119808a200b504010104071205101c40018180703210340d40012060080c002120012610340d40d8030540412000e02461003120b11502603 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 77088419 1250 77087169 77087189
    0x307030606080604060f12050f03030c0414060c0606041a030307030804060605090106090b0309010b12010b040509071202060f1e0c060601020718020c0c04020a090501030506122d01090b0906060109 86
    0xc00d101f8800a200b008202070310800403501c139564180c2050749550070884507203120402c00982407112454500105046e0b800a42d4000c0c18204c6000000e921910002c0c0064003541c2d40d45d110a4200300a03c034a03000c000ca0180a40740d4408050500a141400c111010b6800b14202680091075060280001c0c3c102d5401d41d45003250f090030711000680300d50010f84130096039901ca0b044d01610355280c080780d2046240d120300000e001c01c4120240000d4540050107a070342600915401c0003101c000403503448610341e0460b400c03a40d4071010000b045682c080c10000c03521945003c0c1480000070302c1c0f0702c01031a04810103c02c68560b690727004012079450380325000d280141c0042425110301c450751900a0f060b01a480400e59110075118000314040360014226280080c209103410407080d40c242c4103031500403109958040301c50300384481d2a0741da212108007440c0024080c0b4180c1048640d8104034942c0c01d42c08100900c0348030168241604240f6080d5490584c900914010512540c02000342c001140e0b04510 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 77089669 1250 77088419 77088449
    0x3602010203070b04050c0301060b0301051206010f1406041d18010504050307290a05011d010f03110102120c07052106070315030218070e031603080915030703060608060406 75
    0x61a400c6080f00544119950f02c15411020400d941c01c0c054130002d0301152099070313100c0d03144c00704200f10b200264000d94510780003000140701c3d188251640d0302c1038402d186d8a83d5203140034000807030b04d24440c82d030203040c0c10176046c00761401101c134150845001d54402c2c09091320700707081003511500b214003d40e4014940c0d40104040000030307001c6080c10303201d2103800d05110940344480c060317425034107000c2b07d41d840c5e0a6610320040c054108250281403494410304131585c85d031b41c100403402c10703150710741c2c08007500b081ca10301c0e9144101c4c1e10030041c0e0800d080d00c1082d0140c451031203501569441500d40901072290404004441d40ca0b030715294032400314403c880080030640c131a04c0c0c00b03030000d010111050800c038554400110268540421322180c00310590341c1da40b064900203c0082c1001120509540300b84c1100a4020003601c107002d00800740ea0f0000c0900b0f94482c45000002e038090140110540c0010b404400c01080c2d0b501948481c040302c00c0c589603401c043e582d0004020488001d0b001c3d002180c400c5074 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 77090919 1250 77089669 77089673
    0x80703060506040e06040302150907030503031306021c0f06140d02040e0c0d11150301050d0b060d0c0312020105010b09030307060207020402090a0305070f050901180519360201020307 80
    0x50007107500100050f000240341a000e403105410844122025070240c0d002100300f03010401c41c4049250701c0364200001c1c22542c1d04680c0e4083c0c4030b120242100c44000b03441038020040c00015411243e040c18404128400c001104032440003070b010050394801640e00d043e02c0001c0120f040341c9596030b450401084040d030306000c1e50801c0024081e1440f01c00083c4100c10200f81162140c4450b807500314095050f140240682030708010700d4080e0141c918005000506c01044240c50319071150302000e5203c0e200820f2030761044082110010070390b00181c00140d8010002040c4003c501007826101800e034000c0c40160f89078041c0516074480d440c14a0b80543c0f0030000b100c0420303603039409402b1080c4010400b52a0082d401c00007115101d06800a035586c4d04072a808102d4584503a03a000000c01c0b080d910700c0b00317a614010110345126023000c160360341151618001849171100d42e89001c4400c5101208109604410800344c9110a40c01004070180c20f1203006103444001d8940781340341d1994140d00952600521ba = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 77092169 1250 77090919 77090921
    0x105060d031d0907030f060504110f0309010b060d090501050711190303091407050a140f040b0d14030c0f0102070b0103080f04030b01031a0a090201090303080907030b01121b08070306 80
    0x2c044030300c1e610300707030042407015030340c0320f50340070703016001950303020446007089010202140c94076417055100f24603261303a0404411501c4103031100352024803503050700c075903034101c0460142c86004240303940220005100d16500600b680030085c2140102c0082000c0d03520a10251500801280c0840c8280d0201c0c080c52212020032401c0003501e8424940841d0380d11156980600740b0012441009098119180600c01410890240030041074001038045c42500c050010410450414248900a40d242c82c0107480648406160300b40081e072248085400800e03181ca40c58030381e00112050701c0c1500955520f41541c3e00c050080d01d0b1041d0f040b5031307502c50a03403a550382c038100c0d40d11030304881c50b8100c01408000701046c03890020500071401344083c2d00345290000340c1c210551800420030004286884010009030360f0041e91041520f80c103040a2013651211603040346889807580c002889281683c00222310b4460510400005511491003602540505070a100081c591401180d61a51000c041003000c1116 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 77093419 1250 77092169 77092187
    0x18040c02101e110a0f020a080904020702150c01140702070612020c0f070909030207090e10270311060702030f180d06050103030f140a050a0c05030c0f0a05010e0105060d03 75
    0x10407084003a4036080081c802d0a441401c005050508408501e1404880c1c028030031020080461020700110085650707180d501b4059160003502a0340d01203030304411034031000080c00080c0c054400c4641c0303801103400c0c1140030300400500c00400b92244070104844500010b0080160740c0c0586803680317481c08010400000703401c001c02444980c400e009803d49142001d000f0316000d483c8400f0f011982146074200689015141c0cbe004010181c50020032440070341000c80c0c0b100440e001e41c1c601180c480c56503804a403611340e090039002c1040c2039000c0d60034109a00001d440555140100544429550f105401d85e268011140c03524803051041100d01c801c032404440e02030308020000d148192191003a1596021540246c2040303010810341d1500818554205d01b4110304100d001074031615005800e84020030b00d00908910209000d081c410030310420205200340d0f485ca2081c00300301c544c3c00f101c2c03410869403410f907000182d9a41d440c00f09e0f11441d00d0010b00501d8070030032000d000c00365a9041a0303000c81c0d0500c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 77094669 1250 77093419 77093441
    0x30c09040c030209011518060507060513060e01020406020601051c1205070602270a0308090402090607140d0f020114010b03040614011e0509040b04081c050103030518040c0210 77
    0x80c0750001c40181d403045104c0380039003a01a0403c00503945c500c406030654201251721120080016010031125601500b100c01640e0304c0600401d09403188031340300c1c61034540c48400030203043c00c00007001c40001055010780100d401075400c031070340d0741d0f81d40041c03180700091040023001d04181250b807000480c605d44142e1184480c6841d20615082168480c4001c03608603018070810a0790351503003c2824403000c0c02c6640008411100c2403011440c690f9009010311800440c14003598000c10281d9065842030141c88a464109a901004407000714207580c0f030380c0d0102c4008010a203420740c241020f510501c00c0501c0f01001300107442d1141d09100300e001042e00010421030f403c5441d584403500c05c3c242d40290b14002d100500348406c20134422940700101c460241c20503401000c0704800c10011810301a00f85802075080048a44d0340c00346208944c1da04202100c0c0042020309000000007010750180041c4048810210256000350b070703032070402040d03d00c11401080164481141c82e00004003da20102d0383d20 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 77095919 1250 77094669 77094683
    0x180f1303050f0a030f0b0105090d0b09010b03030d0204050307060908030f0d02091201060f170c060c01090b0705041e0302011707110d110f030309071a04050411030405150105030c0904 80
    0x400301d1903202ea80d0283c021440085e8407048101c91a10090090081d12a0242000d40c10241d888001c6480c40082e11000340500d015076001c16100e440a510038038160001605a0341d89002246550707000e0350280c45828001d20ad0448001206407160301e1003002e07154440050b520b000b8542100d000c8a410409015071030a500304807140403651096208500e26002d0000414681e14102d0f180044180c2c50b440030304480740101c170f520007200002c50a40380020007265129114121030118074010308442c500105a40c003540c092152098101016008507100341041d4005804000c154480c805084e01c0000d0100b13071010440c038403039502c10030000e501640030b20303004044d80b09680b0b510385401403200d50080451640ca6002604020a00078100d000d002100251703c1d505041980580c4c1d15010702c1074082e003d01c0c20302c0c022083c8800c001250004c00740100180314404000300070200c29401a04c040b9094410120b81284c003d065010840c104c503002130103440280c0902003882050b250082c4115980 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 77097169 1250 77095919 77095927
    0x1e03050906160507080c0102071a0d061e060c150f0b0a09020915040608060d15020a08150d0b070c0501020c1b011101060e040311030d060b09180f130305 67
    0x341c0c85000107006208428101c07004034035040d080160070031889070010021a04017200c035448690300050b120080710840c800310b4641c46050b480000ea58029031002508203420710000003043d8a07840c0300d05400040105400314090f80d140802c1d140309c420490001d02000d59a41411950a42944104044e8124500c003040c4040e008000071010301d0fa5800004500e940401e40315024102100c1b40e00340d600220840a150a00b480009042110300a10403449441c2a4030403000b000744001c090a00650300c20815912a030607030002601c1c2180807a1104180140140540c8282c81d001c008541d0841d081300980c0e006840b0440e003250802c01c0c1880c280d584d99000c010210a92608001852030035403120502907030090900300060070729140614682681c1c0c1040024041249040b0149402581c142440840180740080c0c0d80e003140200307540e005500e8500742d000110103640c0401040d048108840e4800300b0307104001010740c140401d441101100103205c0000740d030115500c0f5800b103114020b04210f414 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 77098419 1250 77097169 77097187
    0xa08160203010c080702010b090103050c060708210610021f02030a0618060509060d05060f100302040504030903050d031e0e0a0503040b0d050c0a0e0d06110703081603091e0305 77
    0x2503c0300d002c400e400048064040050483d42031040040c00c003421a1032420780d51450b11019640c80d0f800d40e03003522170f110005444081110000403211941c3c03451080c030740c404841480207000300d8021158103020f0288000e040300d40718404580b80d00c14156031524849200240c0054500940000b02500b0959503925000300c0c0190240745891011102d8070008203141d0705007401d21840344000340086014511056a6400003500451b106500c841820701d440c0a558901c214000001c01642c00a50014030300003e00c0207069102030700f401580e000b04100da0008442050440c1240c40c0069090103000401400c1281a44184c000c000c2c1204c16108480c0401940d8a40c0381c02e5601c17a510200d800300c4001440440030200c0c0c0100c40d0310061020340d240c18903500300b00142c03407124043e0040303100310505000d05c41008040e42c044007410032560121a10f4010360300c0c0c05031120000350f603440441000d441e60051454424002c1940550b07100034680d02c41000300d80b04083c480b945150840600c40f050003040c40e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 77099669 1250 77098419 77098421
    0x7030e0c060c010f0c0905010f030b0409020a0801090b0c1602120106030602120103050c010207050d02010503100801050703090201080906040c03171603030204031a0c160201200a030f02030c0a0816020301 89
    0x802c0851030000203608901d80e0000044545000c114014821201010051aa0003c030321000c0000c09003004600c4c102c0710400900180158000250b001b050503402007100300056001e136048600c9202000b482d610740e4103066103180101d421000561400309240d07030050074407440340c1e004401010008680e064683c0c1d942416600402d030444c007403201c0c040c010000d000d02008443c2018400f070010304240740c00c010102e03000c0c1e1301c1d4990103414086d0010110745040c030b94480b994001c01403400200031178209080b004002c1d120f00e4500ba0b0000b44001c000c15950b0b01e0100344140100d0740705c00c01c407a40c0ca03e10790301d55609088021005091100a000c0340c170007242c40ca6510415588a91303001680d0302e0a600d03220a405001e20b07842d5054002000c200401850090110b030100000058514110700d96071004861220401ea0b40d005010b1001340c188004103000206100e03018400d450b54042000048000c07a52401482c082d400540c2c0b01d80c00c2d03980032404603002055040000c0306603603810b030402e0f0080b80c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 77100919 1250 77099669 77099677
    0x4020604140f0d0f1203060f050904020609030f0c0f030105060604060819061410030b0310150b07060902040b0105030408070f0f02060c06070e01090303020304050907021905030307030c0c080307030e0c06 89
    0x5142d000003914180c0800594103140031183c000c1d41407c000644c20001d4900d10140700307000ba9805068848082820b643e9842c095442c0110010304492440d01d0b84407038a5200d003280c03140b00c0e0242041e03495101c1d041c0342c1801404e104020140c40079060074038000c400ca814810103811031040c03a0100d200325038190028024038018000c036045084020742d00d80c060110348902449402d042503d407400d030030200d43d00030510140c070f0405c804d0046428840a14031006039500c3d6403001d421200c4c0050102c08208240d048100070b04d0084508010120f07906d0015207180c4422200109050403c01c2090000717441c445419080318011460b6480c64607459000c10500da0101d101e46015510000400c0f0f44c0d80ea01240c000644c52082c6001000c0a24594000c1d5590086005252081500c603000035001807007000740d03860001d01010804590107070360802540700e0380156041000241405508a60b07113000304101c4408640c00b5409600c5d40c0d40c1c002044006109800c420072680c020b0003440d981d150b036030402070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 77102169 1250 77100919 77100923
    0x40c0b040e01180203091504140f0609010f02030601020613170a030504050c03160b1e0a1d0a030b0a0209120303090313122103020c0d05091804020604140f0d 69
    0x44074095042c005008010300d500c400c1c01100b0750040080194805c40407130050782c11400c4000c903c5958481e807614070f88106003900301000301d00c143c4100358158540021202d01400540008000000f006040302c002c1c0d10089490314056408840400d6174000c54880b1051580c0c092054400f440d40f6103010111194001004c2c880081d07240d00c140818418240049540072004800400803031207004c21701040b0044d10302c41c88034020705c082506c50a203c44074541000c41b034595500f03196a44d2164001402d0f84c8500c04124113052445064120170b0b042c104013081c00c1d00c1c6c100382d61209559071801c1085c007a512007440c8507003081c0c0300d03a603d052081003040a1030040c0780000c0070319258440e40003ca072244006a000100091003070200c0c2e404161303208240c0c0007410350401e031001c3c0000c840340160040d108400c0d00701c0b00f900c500307091620800c0d489030280583c520100e90032620151001d9082d9031120b010399010b54001400c2200700720705401d10040d114203007400f80405000100600014100c08810b840c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 77103419 1250 77102169 77102189
    0x70f0305040e06181b0c010905031e04060c2003061510020606100c020a08150703050c0705070608150402040308190f09050f01270614040302011403040c0b04 69
    0x2042c0a2045404903007035111000780e03102c1400b00b0030300f1409201c0c0d000c0076000b403a210240c0101140305a03400c1c2c08603083e05802c1d900a0204500f10714180741c0c0c9078403001a17020140c2400c80103103141c0059400322402c5500ba0707900c4800c040c040e903c0c2d00b0505c4401c2841310381403041d409a0307904692018085244a4504900720f000b811a2001c00c0c40441070825a500045400c150204201999240450101d2642030300c3d000350f140c4028804a401f41c09140c000d10380c644103042454505a81e502103051058102d0354050101d40c403403040080302c40c056407800500a03000700700140070091180c600316520030344102c240c40204008034003107422603000390001d2310781e41d03400038280c0c914181d080e00012812160340b5118540040d824001001c60886000705881000301072a1170a0030b07807186620811020448407068009910041290402d06552050381e000c2503540308007a04036081c400035070b011260181c452811003814140c410b03040d42d00c01031044440c02940d20001c6108003415010b0005802c05000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 77104669 1250 77103419 77103427
    0x6061c0c030e0d030204030825020904050127080319060b0708130e0705040e09011112041403030106210608070b130902090a03060b0f031c09080a03020d08070302070f0305 75
    0x100490a02e140c54001c10f080c14010002040020f0a6a00311740250090404d5030b41b00e512003500304030500240200103903000f40408107100604c441036011042e580c01c005c100301c04407041101051043c6c07690100150642c8403c1c000580001c0f41c2840507081140b0426000074066255500408250040742c0b00751120b820104e0200301c10f031100c43e012406880b190740131115034600600c1c001e0080c0f2540c000ea003d41c04290020413402042500040003138000080ca160312241c1e01c2c4000000080c04450696400c004080f80e088020404411681641d01c0d075503400d030390001b803009030b0440740c00440c0c1c40d5180b040c0e65040008210200344281c13401341401040d8290358211164240a010b800342e04071801d00c51041140c1800c035540d03003441c24112580280e0110700722801070001041c00f4a4001056054010b44144040c103103030050030005401115100d120380c654440c042560b1341c49068400a0169010030005850140603e035500d41c0800c440c88d01600c0d24403603545424000e00000e4049001c580003103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 77105919 1250 77104669 77104691
    0xe0411040f080303010509010302060d0209060d0e06060405070206070f0c0c09021b070f0522050f010f06030908030403031d0a06050115110c130e0307050c040b060c0606061c0c03 78
    0x71005801000300e00300442c115410718001072510750062200a1041c4800140c452410206405549414500074501ca848403c0c4880031406407503480c03960b1940e070240000081aa180500c9214010f21282d8010025503035842d5017612012007000300e82050205070310300c1000060b8111749503005422401000742c5c40d2504003040d01654110409004d0150300712081c140008034103150141e0840d0000c484181c403084080c80e1062182c3c592035503021400b818001045012201c10240d41e04903901d007042440d449945e82000c4045820040c00101100c000b0004140801d01c6034214818500f54038604054600f82e40040c0f5141c01d03400041100d00544402c010440200f6049000d40b189a0b42e080115407101001c404580303450100000921030b0400c1039001c484810a0351001304100480000c690740c580c4641012540c0e000700800080c8a141000351361510390070301c0010307a460401d4803c0103010f1270311410100000c50b080704100321404035a64106100080315401a04c00380010f075240050079003014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 77107169 1250 77105919 77105939
    0x7050f130501091b11030915040504050702151005090a0203060402190f18060c03030c0504080a031107140a030f0501110703030b030c010906140904020c0f0607080906010e06100e041104 81
    0x104d490005124a905072807040d000044102e03a41d129089034140390301e0b43d0b007003005491401103030040c9800c6454139040003401d0b900080c1081582150b1760441b80700c0e039100101c104000c00e03980030345034000013818049a404803040d0040e607000080100090704102149101080040c05200708800003482d135060304510a410400c1c041c0c0300700420760b81100003414404c01915084003414010205507072030130651400e80c070031000d40d0054095031007034410703404050900070039540850712400301c03034000c001c03000a090f240c0154803944584054000d80015186855a115031500e002c426141c0d5525080b06102c5c03210007400030030030280300e5200080c0c01d003508820301d440d105540041c1030512400d83c3d020b000040e0811090031003502080c04090383c544031a004100079010304840300c54544140900a11141008141c240c0710348d813550b44806032039580540c1c00355900028440c00c1c0c9901c0c20000131800354103000a01203600641420400004075492010504031141000170150384500820140413110013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 77108419 1250 77107169 77107211
    0x21e041d04030e060c0c030607020d030608030903150417040b07060507080408190c020306010b03011509051c0609051e010b01081b03040201090e010f03060f0e07050f13050109 77
    0x8003502215186003580c1c0203000100b05030085881000003140b454401c039420055039804440143c1601d10908192402943d03a6810500c1080405d04017100482c04820000c292461090000d00602c02d0000c0e900740c09440d100003500595042042101d20302600d0190740080004180d83c4018550b1484d4034184481100d002419100c10015014140800b003036803030301514407403a05154401c0e100321610406032140c11341104000c1d018020b0100002e00683d1142c051812510b20800102c0500710100c0700b1076010006014559000c0e8440c6651410094000b03440341c0c0d203620801c000a07001c1082e8490070302e01004a030b080c0c000c8000c038260084e2003110a00171080485001c0c00d1020351410070440e52104605180b02c00090800d000c00024190780c0b141c5940d100400391120b0700300e5656100c9101c1d000413801c5010542c0c41320b0500700656160340161182c4101280140013a1034018101010441d40b01d195048840d4044010641400c0b13078403141c03140500800d8040350020b880c0b107200c800d404a400c9 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 77109669 1250 77108419 77108459
    0x60c0b0705090a0b03220f02150f03041101050d0e01051506270d0f062a0210111c0204050a080d1211070b0c070c0e060109050103020904021e04 63
    0x70041c4407500081d1100c000c0882500c0481d100c0640380e6440c548840c6c010040d140c120041070208203007003011f01200d000000102c070b00076038003c1100800d94102250a1080c6420096801c03c1000000c000c40c0300308402d840384d6803051400c18034060070000804140d4020a80c14000d41e59141e050100b86010a240884200810f0700c460303080454001113440c1d0384012100c2984451503000c41d02c440ea568204c0034110440e401410f5000c00345090502100815000e50704001e4440300246c0b0021128a20b100064961100c1d0300030170562064401080141440b031200b031828541c1030103c1c0d02400744c0300440d01c01c01061010016103079403400082252621403584007000b20740001080c0e801940e070002035103072050b04041c8080303015900162801504e2140b4a4050181951001404945c010403c01000841e000e102011042d5440348480140303454141c400501280d0150001c20495000341c000d00000c02c0020401802d01680d8003005d01c0e100d00542d0200703264100003070144180300302000d580003001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 77110919 1250 77109669 77109677
    0x2010506010c030309063206031603020f0a0806150a0504060e06010507170f04051e090114030102071a0402100c050709050402041503060519090c05040c18060c0b07 72
    0x8100580060110700d0281e101a0070075842c0e8103c1c5060015581011f0010700d01d100003807106504500406110400d2414406070f845262404074000e860009082041d50710340070b045442e040e256030300700600901513034080d541101d500c18000800301014449944514860f03078100c11035241c0b610410030300c0c00d04c0d90080e512444c41c00d0018010249542c0b0201e600c410282021b170707640c0140c2d0511003000c1161414100300c1000000b40c20b03c035004031001030300031101c003502c000241c3c02c8041c00d0b610022143c900c4058006e15564010824420403410300d40c041880076000600d407020945074840f20b419504d0103010310010507020b000450814200c4054915954603100150181556451f900d0b03007900e2241c0c0c41c41316180d030049003d40d0342d140e0210008500d40d03404110190741d030b0300d410000f4090131034040d50015424074210040c0701840c081e1745103a0364440d90408109060004010051000e161180304014160031b1031070b82d0314824070000d8040c045135142c81811900d50324000d04610340007481d4100300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 77112169 1250 77110919 77110921
    0xe0706020a0803040b1f0b070b0105041806020d0216060e0d09030c0608070908060a09060e01091109041a01061e0f0e1219030503060307050d2a0e16080601020105 71
    0x1c529801d00740c80e0050b070300c48414401520380001e88540c2903d240c0203120306c00003481c80000d2102d4224010204070b4030848580600e40e0341e41c01001304403240512103821042d21508028006800e5038001c1645a00c246401130400c1c101000e00700320100000d800b04c0e80c543da950300510715074400b0810503400c00041d28000300320600b1541c5681402c8180d00c20394003800a40710103d05402d02a070700c100f002e00000012503009203003000541000c5d1401740400c0c1c0740c0c80d1801001c6941a0f80c107015100025030080e6040c0781e54504903003030140b229001881511b0b107891085444490f02081e40d1024003e003250386c0c6081d00e50012005e4442c406086030f494009001940050300f4013140c00c0301c00c1c0c001c40842241c0c980300703110780203140c0f5080054a031440c07400c0c000340040c11403c058001c8003441c09003e084e0111200d86031214280210311020365400340811011300d80340304e410402c0da07005810900c120000c068a0030341d80d90020300c9100c000e48801415516a0b04103001c410361040200e0b910003024070080c005 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 77113419 1250 77112169 77112173
    0x409020a060c0201020c120c04060605180f1207080a050615010903030804020a090f0606030605040c0503130f020312030702011a06040501050c01110304050304230603220f05010e0706020a 82
    0x4005007441280d051003450140c2105682c020312000d00c0c000300107424054820441c200403621000c00084140c0705618002c070200d103103482042956800c01c0716a100f044030040c0e02080000f805545034199070b1080c040b0031014074812080c400403008002036030081800c80820702d009810003000925066208071880302c5039019aa01c40c170f0b4003084a4050030108610313140c50000c1650b0329210307002020100e01782021000c051030a94084811141c11f950100b088075162020001500c0c0c44180d03c10024105101143c022040344d110300d81260b2086019900e0110242c0c040380c20303c4404040024001404020404040d4081c06075a1801107000e07141c103c42e012400c009103407801240111410040c001c1445c03071000c1c109501c4070000118007420030303880b07103490b180c07040e40c3c1c2c0d04c18050000c3c82c444215210008804103800764214400007001b1138107681d00c10320b141000c1154403402d08610804080303514007113180030011145a0713000c0d1001184500071125042c1c0750100d240c1c000400c55011221b5080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 77114669 1250 77113419 77113429
    0xc080304020405040602070b0411010917030406202a061306120f110301061103120a0b010c1b0e090705030604060506010c080a030504050105010501050304080703080c21010e06040902 80
    0xe8410350454001906803501d003407000080c081c05c03000a0001411a0501040c441604140e280d10502665815405600c410b5103105d15216000744c03c0d006e030310038407051040501540c42114048080000300d503024203c1e0613590300d4422064401c2800342e042e0010b0190000300c50380070007542802620100c0c50030040409010b503540b0684644001c0202e860001c00a02501d40c21102c5d8010324641d05001409880000101980c000e1050b200400d604079540c800c2d071800401541c20b402c00c6081101c09035520040f00502402a0380801030412040c00105000120b21003807201d4083c6810300a03505460800e1001c1803481c0000e003444005510009040050341c0d00056000da0280e48110080780760f4a5050068440c203142c1c2c40018114080400d04846d240d5066100520943c00f8034001d0010b41d07600e500645503448281c80290851a04020101c007080c020505a41c01080c0d100c40c0510f480540b419078046142034041240b50302e55036030010010489544c02198011100316010804030860b540015 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 77115919 1250 77114669 77114671
    0x3020a02030316051c050f0a05060a0b03040f1a060414010b0a030f02090d051606080403050f0307180b1b03031e071106161d0a1e12080403120c0803 65
    0x20118070b101c800f0044003284602c050f6590700e5101249002c0c5150004003a802600701100d107100c1c054101000595007058a02440c0e000304070181101c1e00c01c508040c1c6404017503100070070588180003410590b00004a001e16100c080048082c80f0070f040b401c003030302000b081d205002c1417500f81003004001881501a100304444d5904003e080000d0418031900b00714001c0e000d41080103912448808410083c000045498003004800c0401754200070344810080d180e904c0c01380d07170113400a0401d1094010006603000115000301007805c0440c1c1943c4448005038940c0e803550802a50701c000413461070741810742542d0b103101301c20782000038608501c3c0c101105404034108403121416a0070840c08200040d010304d44c0010b00f4404101079403100e00d003900c00700c0b11410b10800d40340c000038034981041c0e110300854136807038080103001455980e820340b51511080c0b0103441e40d0300c81e981d60b008150380002d406010041c50008984106c002c251240d2a5042031407085402d1501c140c1800a24903c0c5000a0800d200f12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 77117169 1250 77115919 77115931
    0x11061b0f0706060b0301091e18030c0812041104111c0c0c06050a0213081912020c0303070609031403040804030305031306090c09050702010b0603221a010e0703020a020303 75
    0x28980381c0026050a2020f041c03a0361005000260000001c00c1d4220650044010b400780681d0344414071600c0c48c001e808a440c561203240c0c1c0c904c14101c050f00043d100e22030001160f401070746041c0c10081c0346080d400c00325500351800c8a007001d000c01c9008150505010385049260b414158908082c0d2002a520401101401e90801540d480c3c00b19222030f8065403580f0306a5030003e80c20401c07440c0c40140306000f5400900002c941043c01e02c800100030b24001180700e1700540140307040d0b44030f2020380d03184d08101c0811501181903000394220390b015074908002610b40035010303289c04035049801b403c0c09004102c0214013804c0044041042001080b41142200c0c00c0b030364180741c515a2a51038105000da10701d0465401000c56092540380300c01d00542c01105010b03200c00000401841d01c889200b60300b01c0e009000e015400c18001e10003d00358141d0006214451202c8440c0407103507010703a40d20130180c801400c1407400701118007801440080825144682e1100746800c0861400c0f08020010303640e40001000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 77118419 1250 77117169 77117197
    0x80d030c140c0106081507030b040c0e120102160f021206010806190209040e0312060a05220204051c03030506030c090a050709090606050406030f140103030c030509030601030311061b 80
    0x55840b4000007503200e403000f020904103071000c0514281c0d4966080c1c1c5e0a403074400003e401d2140815243c540741c850b11405100c681c64607406005010240580c403454240031070841d5600f03000c1e000c400c54160300001840d6110b14000d160070451441041800c6c0e000c1074210f402c036808003005102a0800286160b000300c4048044102c00d004116150084d1191070a099041400c01c04041081400040540b01c41c81021805140650f81ca005000f082106c6105299000e0079a1580040305c1010205410a90f025020090710f00340e207801c080740800102400401c2c9030602c0044a1061550500c50070fa04550118040d0040551440000d80320480c042c0030341818903969404039074894001e07401e55000700b5401106201450346c0b5180030340560002e00c10400401d05010480400801c075102e503580108254916000c1a42076440c203e5400103911000c40a00030100320f180500c0e6020810b560007584259610030705005094409410118040c02d602d034910301c081a1148521012015035901c1000806 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 77119669 1250 77118419 77118427
    0xb070b0a05010e28140103151b050d1503030507020307091103060f041e0e070501030501080709050705040315050612010216030e0f040203010b13170a0204020703030e0f07080d030c14 80
    0x66070348911413036a02089086103030250a02d1804038800c04541220b000d020182c48005000704c070401942c01c452881e03040030324141076031014240102c01814101c4100d0304006a880041000c801e0b4002d01900103a0100c1c80110b1090210703d0700b00000d20242c00e40ca0010300c241e914106d1544c0781c41c00b01425291040440c00c02c200d845071903a42c48601d00d04620191044401d442e807050b00c00400f0601881012401003a07004182540a4010709040b03d22003402803141d030340703003520100041134060005010000300304400004a0000140c1c407100503a250000607407420078000f048581c0d480c12141031016401489001c0203003a13030340c010034215900350501603500d084020008101009800840b50301c80e10100003c14281c3c92138000c0c0c107151001140c01220316440b4402c5400720b85a01038070360455071003042c032180141400d4018082d0a4460b080c08a4101d01002c0700d941410100300601483e07500c100020082d8407020449100f110000d41810001d282d01488002c20705203118405484070b0200003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 77120919 1250 77119669 77119711
    0x703091103150f090a0213020a091212090608060105190e030115050a050105090904080c160b070201020c0402040b1b0c0301060f030c0501020715110f070b070b0a05010e 74
    0x80c10484140d00c01010748005403031401d89511101c20030b842001d085200b441c005000440005444900a0f400400c00203070021200c030340001950248801800300501c0304000220007600d07074203211b0700078803079441001e1042554100070040d04880c2e0001d0104207410f0140203190b60400304440c80924500d000d94484884001d040d902401d03c1000301f80c241d0f02c5c1a0020342d44000d56a00390040c0d80c0708a5008081903079900045135240101c100d610380c443e000c1000320380061698801042800d00f50019540e1a00c0041d00a8151350025885060b1003000014020115a4140304000c81003400725400c6042c14149148554207010710088000208094050481200b104010206403000024000d00030180c580800e02c5c100700c2244022901400c0207000400c8030b60000c1031480c1a0743c50b0369281100c0c421500c2085a04900102d4a00e1083c0200e24a0109040b4188614005003542c804426940e9420f0701c0e00d040000c00c01403038000240c0ca401c006000e05000a40f106400100950710b2080380c030020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 77122169 1250 77120919 77120933
    0x61608010504020d090c0611120a02060c130b040308030f0a050106020d0c03020106030209130210140304060c2102030711070e0106030b060d140a05070203070209060114040305060c07051212070309 86
    0x64401b8107150300c054800215240d20000c00650880c200080d07400004034820340307008ca800b50144900168101c0c5001407400c0c0c1c0488064405401c0c00c0118074401952500c20105a512540081c1c56014001040008001c90030356442e400c602d500c1d004011941c5040030003502c40810001aa0410200413882d00515200b5009a009150000c05207100d40c24030b0095001b0010205a080703004e0510341444815250050307162041c2030201d40c03103080c51503485580e0300700140064a841414803442c81f0b001030b0300446001c4440703414030300d107040140d4a003862580078200c00c0e150209883d5691042a051201141038013003a17044411605000c514070b60340c0d800058440c0141c50248280c28901601210300016995030305001c0d03054400200010b48502d035003244c81b0f10405c038020750048030303580c00700d506035109506100c42c0c1100d5941960520380c0ba5910141840b80070780f8421200d40b4003050850074810244588041d0070791034070450307251917001490040d040c1001040310041c1555110920107002d01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 77123419 1250 77122169 77122181
    0x20f061b160e0f04122a0209060307030f020910030f0c030b012c0714070c060807030603020612060303090a06021c090620010908040b0324010207031b08060702060702061608010504020d 81
    0x950415049195072006d2200006642c0c0c0300103a200340200c0000ca48035080224807401600c1d000b1415800814030f0380c007072082211024203e698000840d030f2000010400d4181282103143c46044401c49082c5141400305c9000d2040c0c000345008000344044c0d4070045548903252540400d450341100307080c1d0b900b44056480c61a01da504060140000414804101c4201d4640081e28010380700c1d954140c6500004900311200c0d400001d4000d80e08010020f10b041d42908125800b4200030103e0346065443c038042003000009510400c05070b484215420b45002ea540d00f4072018074103030300d020207500385403000007003101e01646a41d901c0699071343d29035010000c0a410801034150030000b2182d03155544d01c80909594130485441c020050030b945aa02081200c0e0100410244141d005051450940d100d2034814079903c1d0345034040860b030510000d000e040034040603115071541d401406a80c540420013a09100c001844024500613001e10b0f200c01d60341001035a4103448080d10b0041c1c40b8984040400d0007841 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 77124669 1250 77123419 77123447
    0x60604052206121b0609120b04050c0a150e0405090604140307061d0d1409040c05090301231305070b0c030c07081006050a030f020f061b160e0f0412 65
    0x18103410641c0521400b00003006000440d0000135513100c0e80c2e000c0c103c0d01c064141c09151684204914000e01041d0201185038009000d2401ea03140d000060000888501160b8880f11a01c00c81003003559840c2e8001104500110041c1c03424021403a0915440341c45480090004100c219030312025080c07100e04106a8034043e510440c1041040c010303045100300795003410354182480c0f18489001407020700c11070b4400d0b450070f14410040e06180001c000c000207801e680c1072110030440d003400504041d0351f0901a04010b24480d80c101c4a031190940c500900e0040024918040c9980340e0102c2c41c0042c2000890404540200b642640c0720030000311b07920b0841c0700d10b009060b0300303205007540841d1001001c00c5a20140d080e0b1b2504001084d5200700f0320008400e00c1c40041c0100c010200b0180140c20150988011580c004003a42c3c40c0c480784400304003416004415900507503000f0894505520703400d21005029005914806013170b86051426207100d45c0004000400155005181c08041030103002040710b124 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 77125919 1250 77124669 77124689
    0xa0903080a0302031b0c0a060c03110d0203040203160f060309170a0e030705040903020606040b061c0903120b0306060f040f06080f01150b041406090402070b060306060604052206 78
    0x94400c4900030042e420517a01c140101c1903441e40078103003460f81c1048500700c01c000c60140411b0989515080000c00c2024900000e043d1150301104403540740780b00402c8c1c404640c10340182c8906041c0189850a00c00212108030b44402900030300003006102c00c204100ca40c24500450741000303e14202040e0b000c01001440380c150042100041d00380c2110b405165900c0940403202000e40d59010007082d035200010280241e001100401c1590405400203070700e8045c06000c641c9400341c05c4500380d6141300068140964143d80301d00340c404060b84000102d030b8441801c4020712002405e4000603451f881c000d03190320f10844040c56903500503142c40c1c01c81c12500003210000c0241c46d80d1b50300003075140d20003030015184075441c203244400032049014094060381c0b29544000d0402c0d09290390b881182240b046030070351001c014440415555141e00081c2200d600c51420790001d801d121090500d0254054159449900140024005525000f0342d4910540303828940036503541c02201084014905074100800300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 77127169 1250 77125919 77125927
    0x30f080c03040f0905061203162d0c060f02010b0105160c03080316081006020a031809050109230603032502060706050402030601090501050105070209071701060905010f02210a090308 80
    0x10149591259105250540301d59804146207041203480342704403c0c0180c0303502074081030308010034020f040101c00d9034501c9180d0070140d00880b0441c2d08120390120121030b00702600a0a1005950103c0c003402c56017201d000034000e800c620313400600329001d140040c034911524201100e040c0b01da0414440000d5410010042d0740303050401040319900c1424151402280403080441c010700511805107048610702e5000e0241460b0301d40d0116241520031418200100c01d000002c1a0041c2c01c4c46a14000c0911020008035844825411006504848070200e20600c036041040303883c0d2008030484159543c40d80c010a0010130044000e0628161031401941040f03002c1901c40c2003040a0740414082e44c002c5045a81d140e988190303210541340300f4010390f8000b8105110203001420305000003a00010b2034180202a0b1801d12049000c55909138403200002d000090304100c907580110300600b080d030091024146041440d40d51509100304012a1803072400d0014100c2c10913031007005454060f41d40030b0b07110765032 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 77128419 1250 77127169 77127179
    0x32d0302240405060604021c02031003110303030709060e010c08030906040209011e050d030e0d110a06030209030309130e0d050301080c0904030f030b0f060f070b10030f080c03040f 79
    0x6200316007500760a00228190300c4458066288210511a07036002c801041e817a40d41c0c8090002079000440105100405480c1c2d6141d02e0b03001e40059407041e0055034440e24442d14500781008028200103400b0700a420401c18045500c0c5d015822400703644050810300444070030b040040b00e400401401c0500145004000c4c080200000300f0074034042c1d40200c800030b0703403a600e9013110712806119089500000d48054000c0110b0f082c00f0036991447e50290401c00e24849049010913284a02090708607a1404204421040c92800103208005004c0ca0320782182000a001b010079582d00c103840b100c0c0d01c10954022420810304070b58000000d10200d10042d54286000701c1c90140c081e030000c0c001c014150166400e400d105c0e0070202c080c10312072030b0540d8a052104803c43d10a400520589029076008078189001560b5030b1546001450001c4d1864940390340c58405080c1400700a02c040d1000002c4000f11004002023441ca1049540b80c81d00440c2403aa90300b0040704940c503500c1254001003400c151100c000407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 77129669 1250 77128419 77128423
    0x30e0a080a0305030907060207060f08150d03030212150a1406041509060f0503071407110301061202090f09030a08090102040e0a0902010e040b13020a050702130c1106040309032d0302 80
    0x3000792040012101b400d620b41000b41d8030740b6024019800000c05d42e040c94158a8071801c04141c206100c0740ca03803045440700c5c802181c01c44151a10a81c04640c0010350303019020030303920800782d000c03c071003c07194201c3c0e50800000742446504e00c10401603000405500c0004c1c0e95400c1101c008041c204604640324185a01c0078240d4049845010040741d0001c6000003024022800c680c03141601e036480c03084003000121151000d4120600c240d41201100600078403030b4900748111009030070034030050010301380603104105030403100030101914955042c2c280f080445e0000240c60200c01c081c2800025542c40301c51042c028051984410714618004092142c5010380742d1001301494000c1e83c84040416000741800144c600601c00c154000c51382095180402031954042c11112506140c068900382c02c0c1e400059500c0c0c01001401040c2d681c40d1a0341c0c0c80182c2000e03181c1c07002c0408001402e15440c140d10b0140000c0041c0c4005001400035420003030020040d91480c030301030220140e455542545600b4001c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 77130919 1250 77129669 77129671
    0x40204080c03300c0a021201020d0b030307051009030519090303030e01020306090105010e0a09051005030105010f030f03080703180b04140a0503070809010513031103060c1204030e0a080a030503 85
    0x501034040d03101c01d140300c8000600a0b1014061402c0800c85600e4100e1003c50158840841404103001d2109044016500e11610b0000307584030000158645000c030152208440010511030b209510030024a0006000861000300003501c25030001103c070501c1c1026a19445009511003124601002081c043c0d9048900601034a0095070200320302c03036400c180715080b88000c1d500e00b0340c0130035020300400884d8031410030f68080035009050418241d59850000050311000e40341010700c0f40c82c40b003040c08907090134800c050040c0007207403403010524503503120400d0014135140042c0800a420001440641c002c0c0c101d0020b4015804039a0340c120b0300c41c01c19030b406030b8090b5030444005c400180820800900003580080d000d800001441ca41045955960050380c8520f8046051000038041c1400303011003a004200154025000d560040c55600101401c1c003100070300303082c400e1a051100c260300c1e02030b00b080707242c0c0070303600d410401581d2006100081100805502070200b42c4500703081c80e410142e1000c051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 77132169 1250 77130919 77130943
    0x150504030512030906040b0a0f0f0b13060b03010b07050304051e01080f16031a0603070c050c03060f0a0e0a15020c060c0712050a031b030501030218011a1804020408 72
    0x9288032116000c2c0400c1a88400ea94841d40d6034848000309022580c00450b00d0380020009000203008030301c0c400d400c01603a4000c00042140369440c1032602d018141000c04440e20030101c1e50820601d4145103810000e80010b0044941d010b81c04240303041081010011179003c1c200007080403941c511070780d4810300580000e1701a940041d6501e0042800800da0442c0a4094003414150a108986a220480052204240f6580b0000750090f1030502a110300d80158020020f69589052480c85401d010749040713000e0384618001e510081c1008484201c0309081b42e000140150b0101b03501203555401842c100e0708080141c20b0b01240f02d0200c0d441c4c0076643c014030440c210f04d0140d44140e9540c203204081405a15005411800c46418140390b1600c500000c040390b00540c28001a11072a94411f0311f4a03649403030301180820783c0c0c0c50061041d8902030840701040714041c0c400070200d604085401c0d0303403a410320001501c1c0850100d00182010400c1c01028941040035100f1900d032580c81490f142d88030804400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 77133419 1250 77132169 77132173
    0xd050f040e28061401050a0203041706070206010e0702071203030b100503160302070206070605060d0f060507120c0905061812030a0801150c0209060a050d0507050a0506040501020a0206070204061505040305 90
    0x403840904400340281000c0340c0d9421030b01d0401013100401541c07203601545000007140800c010200e01c48900a0400043d0021000103021038030302035602034902801a00085159402c1a04000b01158000b5056040d181c0c1c1c0f5031003c012428525050b400f80034408900da03031041883c0c054044055014020314422040d42c070886d58490701a0b03001b03038200d01c601d5a003c1e400c40b00410403a0302207413042e08455004000035065220041d0103464a841c20b100d1440c0845040c4c0d11201804000c8d51f024400d08504032080e6005c100c40c00c00440e000c2c000c1d294034032806000e460041811110400303840c49006003d03c020b00144d02c0c0c40c003296580354480d80140c0c11340c008100c54000205418601c04406d9103021000d48514a41048507000c0050048005007030640c806210720001c140c1b41c8030340305012030b01b522501c01003884600300020404147e485406c054000d042c03d00042000e41c0c0e0020740b85000e02d406580880c1d6508503800420040e1085800040a0201e201462044c0c5c6501400600480c0d000d001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 77134669 1250 77133419 77133481
    0x60319230f1b0a080709090f050a0302030c15060f1003180c05040501120b1305030d0e030306010305060108100b030613020408060106021b0904020f040e070f0303110a050d050f040e 79
    0x800c009140d0f0641c000c0701d1160307101c0c8000303102c00b0300541d1180441138080d809000410486e41e80d05440c18403a1141140181c2001c43d800400d0001040b0842c20f01c1c1901010040a140c414041030355101002c01803440382140c00c0f01254030a00a5021240150300c80c00040748030142800c0c025503404035442401e0046103800000a038244020102510b00c507486560031030992030743c1c0c416107403840c54518161b4031740c0410490880309200c18841e180400c03500b10091340d00d03458003c0001d01210401000306061280010800c049c0d6003559040d0001e4070b0a158403d034581c0c9070f60300440e800a00048209400707a10004000c18082c00006980d4101c0303a103a070803216001d05201008c103800c0410b0940c179411106140200e00107117401e0005101c0b00902900001320822943e0b0111702e00391259020400700041901c080c001e041e800460800059009002043c5409070f81ea03a042c1d40754154030608040007404111008440000c2c011a0300a0501c06c40824003400c10045142c043c403880070095440c3c01720f042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 77135919 1250 77134669 77134723
    0x120414010e160b13030201050d1b0c1b180c14030a060f21020603040f0b010f15050c0607080403050408030a0e040e01180b06010e030319020105060319230f 68
    0x3e000ca480103281e00c06a07001440c0b4503030064903180c10043e000801c0c00d49600801401c0444076001c64021056070303940c0204513074142483c503050401040e81050004803e02e0078400d10b441003030f240041401140001074441900d41003140c80e02050003500c15120400400d001581c401303508407905480c0c0b6001441d07071003a07880000d00d41030560f1510b50454014503141140140c42c0120256a001d03000c0c0500c0700101001d0307928004401801d170002070751348042000c11f001c400141810040800c3c41402c0c184c0c60301e07008101c0c0070769440c00103142e401084820b000103400c0600c580c1c00c1c1d500500240040742c3e21380441c01c00103070074114401000c0e8000c602d0003054051452050254902204c103420380c640040b0026103840501041c000e1607507044c40940c1581c10f074551010401050050515803418240319000903000303080d07500207820540710354030020b580c100a81040416032159980440789029000ba40a0030507107003245c6440a022900502d89103110101001c03494aa084040c2c0100d05202e030005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 77137169 1250 77135919 77135939
    0x4081209010813030909020f04080105040311070b0a050405060310030b0408030a0c0f050a0e211006090b0603010b160b04050a030e01030516080c040305031306031103010b120414010e16 81
    0x10031000390010b0740036442002040f80d87e900411101c59020201480e050300e1f81482429100c05036403c80c001044649840d024100511000d4054090b60030658588404010020054080c40c00b401d403203400f000020a61071020102488011b540c00a90a00d140c030703060034156602d402c11101d5860050034042c28021180c864034641320000713030a8840c03605102e40402c003100e025903901340c00354201c07403e03844900c054450b075040003412000c0c500040c446030900c403401c00240e0340c940e405000403034102000100113564980c15241036540a072601920380d40c50009007244100640e6019000c500d109090109200c1d02084020019029441d50f045e03111a1400440441e54103c51300c0400b01d4007100110103040c441d000c200c0c2c120900303602550516407280c5505007554445484800d0f0403070024010406583c040c0682840c01042184403400c41d80f42400c402000e00c112041000115110800102005080d64040c0004006403000300001c510034261507658003401c4034403c450000c404000203101c01d032 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 77138419 1250 77137169 77137201
    0x40305120a0c03080403030b151e04080d0f030f0207080403020f0306040c0909020111010c0201020307080a02040602061501110a0c1406070f0305030903070b131e0b041106040812090108 81
    0x32980c0d00c1440700420b0f1401c03500414003a00403030815494000f40000b40e500c0100314090320300080340c16641c1e210210000c402d03911520204140596041c8802c00c110000403900313050b10700a906040304c00d0300315030100714014010b50010034101c610102c0c029082c40900b9010304180ca1003602c84480003070502c401c06a0390001110b000701450340b090b001780036007152600510302540c410b05204942d203060504c1582500c00303506007900140c0d07000c020003038903561002180f60441003101c011840c160601600946400c0000e08807400040f4a42e8803942c2a440f40702c865040300114410382d80e03041d0040c0307410314003940c4da80301c0c0310f44081d0064002c2c425498400122200d1741e5004122000c260b007a40e03030035549031300300904001081c001480100f0202c2d41c230702d141c20300c0f419840000b080712020341d00c5d10080d00d0741c56240d20801c4c0341d0441e8112000a01496180b600550410f034120440d02079440003882512640c0c2240d500c6001d94501e10521501030400740c09507040c00d0b211541e4560b1760307004503100014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 77139669 1250 77138419 77138437
    0x504121b1202090604110405120109020f010c03081b04090f05010303180e040209040809090a090203060f27031c2a020312070201020405180403140f0d0e07050307030804030512 77
    0x10030f00c01045003440e140d4800c1c007032400c05080c03160400742d036880003401c0c02001c3d81c00456135075182c03500401140740615020112000900b0110110708081c2c03002011040d0040007000b8520700c15150329800126902030b54020314500034280061544d100100010701028402100480d00001b0304c054101e14001c070f4402522048214860a07980310f808018600d0005041034544030001c000c2000d1541f69034011500c1405000c0002c42c6401541c4103042c608480209041c54071007214051084159070031030003241c0e480b042414000c141d51081262411442600c0c288050450242c0c40ca041c0c50078244c00250b81d0021b02a10f44c00c00078640030000c1419402007002070016041002150003500c1490307041504035240e4400141040e0712403010420350010504d4451028200790308000405502074150707601a8a0410141e0600e110300b50000324600800314080c81668854402c00d410079410417000005000c0102200d0381c4503501e050068280e807150005880d41e000700051a403074405900100c58a6203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 77140919 1250 77139669 77139679
    0x10609060515130308120709060c1122050106020c090604140f040309120303061502010b090601110f06130201171306110706050f15010e0303090405070504121b1202 72
    0x642d60402409140d01c0040c50882c00d10031201c0101c08100110064080540409041348031400e1440d005000744038243c0c0712904000030f404c030260000e4010260b407400c0160030780b20311032042e4441a21400c81020903008841003880d142c00010003590025040c01410700c140c600381500d489d0030050006880d4080d100f0903c00a00070003040c408009841d400b0303440303070180c0b500914950b01c0790a10300380c10301221740030382c00252501002d101600100b481c640a43d03d00b4002000755214502c042402441e00601e12818494008002d18114109004e21480d814209041c0e800602e01880038003505008000c05a0029001144050100300450003c5000388000320200c1215502030f40c0301030181c03941e40594502c0312030078083c001c006649400303840d001d001101071404032031801c80c8503001d6401c90716050504100f03034500030740f505072008004c950788050140c40c041455660820103482c81c0c812640848030740240c0080c0e0909001940e402e840c0794016100200c40816501c00d914a800e40070014065400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 77142169 1250 77140919 77140939
    0x30d12140606040323120304060507030b0d0b07020111040807060206100305060a0209010c02040906050114030c011e09032102061024021f020309060f16030203150a03060c020106090605 81
    0x1c0303000c117890503180300000c98403803840c80c801020030b90411201e200d80c00c040710340100900040003000e0103400e501008900e000c001d01d5261000040080382c1d1904c000d40418009004151910700c00e4200007030704018580d00f652364543d5078000c10ba80700514842d400040c014071022542100e1810166002ca80c2c10500404841d110411040c009500001d140390502c24003140b007000584650042948140c010380d40007403250f1512501940d18908055028843c0d0000031103802203030b8022481341030b00441a48850700400740c40d5401e8801d02d085400113028501e0300078900700400500c0d0701d03650761204c0c03e50a855181d00d443c000720211211502803c0d90340a8444002d4440e100010a00c804055040c4100d8030034a800341c16211284c0c40c4041560300c040d0b0000200402c011f0b0420600b034002404200041462034002e0380015814500c900c42c1080540000100c0c02c5005c2d004210401100014043d415255807807401400400f006940b007800355007001d40c00600440e49104500c206c4030040c18030005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 77143419 1250 77142169 77142173
    0x40903052203060606080708090708030f1606020c03180105070c0510141308010b0d0c030b09030903100912020a0c0b071703040507050a0807050d080a020c030d121406060403 76
    0x500c400070107001d01e020507420001000c94000c0c0510741c01401c840e129440380742890f940080405100828110f1142e0040b641002011400401c84501111369a2043d841e00c41e8010072002c044c2008202400b454000b0580349078480c0040700828070f00300070070b04400c00e078000c050041d04d5070302824001410700c014034202080182407145c0c012068141c0ca2401d00f4421083c40b2484141f9000504601c00080408100788803045d02440744244414044030a402010f04698803200c64000c0d502000f000d16081c1d8003c20040007040040e59400b90b0024152030380384510804400090450100598402060584d000444c07800801d03141c06e940d07004101104403a0810b420914654080b02080340d10901e4003041c038510720312200145000d24451409411900c0c500790411600c110741d07801103082a08105c0c0e003044140e950107081c000803039010030101c0d00c0304000031b0280c0c00c1140c100001034050003942c5c0410400380d480701d1400f151b0301c114501080000200500c2c44030041e011a06941c100404020070701c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 77144669 1250 77143419 77143447
    0x305030412050109020409060507110a0804090b1809010207031709060a020f16051c0906080402040b060c100b1906170a110c030a021e03070f03050d11040305010b04090305 75
    0x141c6180910008600c89150398003140c2100c6103104103981c40e41d40e400070b10003100d5201c4a81c1340801d11035402000c2c1945141ca50070064422407181491056507401141c00b66180d4141c1c070515601c80144a003500d16000d06214040d501c155400c07400900c07200d40000c1284046060180904400e00080c4000e94030410524025808044034004454041c462440304441030803208101910900c050116403006100018500c0110300c0312a00340007101000303000c0c1d03d5100c1c01403684a07404460100318281c3d9240031074110320441e1078404181c02401c100c0b4801c04500d4100449a880c01d03078041c4c40d82d4912070034024490030795020380350000f01c00007039840b03101003541030582e0803050901c40012400980600c10545512441c080d40051708045651864a81c0600c504c0001459a041400b240600700d28010744a1242074002021884256908028075100f03074295140691000e404200183e0b41d55006450b82e04281300c12200c941c00d0640040c581d00b424025801000d034551500c6060003040b481c001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 77145919 1250 77144669 77144699
    0x3040f0201110f100b011e080601050d020a0503040218091504020303090303040e040c05030703030c12030e0f0102090a0503011104121119030204050f0c040902220f080d0903050304 79
    0xe41000060b151011032010705200d1403070b03040c161400411244403460f101c03c0c16141e50311211818420005200c0076000340a02c20051229a40d19060f100360b61030b240103845c02d00071420b0210700e451002c5404e22013580c00100070350040b402122448070091000081125100d400c580700e2055400294070b92040c1e858201c14160014030007070a590a012030700c03021038910f4109500800320a07217a40c0c02c3c0402d01c10000b100e0310141074141c0190500d00c0c19a04c0141c03603171a4802c0010102e0207032443c50b174682407196002194010128042e01e00c03942e220b07a80325003c0c1d000a00e1052140700030040000382481e0500c60182c04c070300b02540030760805280034804a098145514140d84003024206500c0241e91002d4003120203403400f80d186900c840c1180140000c071080100300c1c40410400c0d00a200681101b5000c0e03e007118074244000d0703a83d0314140c3c44030980403140d1403120b006041040002c00c2e003010360100f84d0269004070003280d04400c4c00a900f10ba4440080c80301400c41d1b0400c00c0144000c090b119140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 77147169 1250 77145919 77145923
    0x18120a200609120106170a030203040e090f07081f02040e0c070f0804260a0215090f03070803041a0a050a031802090a0911040905070e100b040b090a0501050a0503040f 73
    0x70700b80300b50080401c0310b6105190740303494165036405041c031544406140107483c5101940060170120041d54001c0e69030321031070054a04890034034000405010301045070080c804510301c00e0b20301c01542c0d0410390360396449000c4080c103202212541c4404410242c400c2c0c400b22040c844071408a6201c005103000c82ea401307a1011389640b1818000072002c80c8004008000a1800c4200f00c0c40c0402d19843c200b1919000201f1040c80b42c00801000e00943c1d10b00345a0402b501c501c174141d643d954800070002d40300480000c1c0700c5070917000e505000100080c000c00608121901d07040720342e05c4080d007000340c42414860104640041101030121601083c481d900000b011500c80480da6007800803034000034801941113886100c01078441c030f58107041119a44007013030048016501131054000c80c0d55010780700e50071801203402000d41d00f00007a070300340a59034409008101c0f100340c1070f41d5aa154003094550f54030542ca00350240508139000281948544100c1e212880e840d039071142141c5030b079951081068451041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 77148419 1250 77147169 77147179
    0x14040b090703050f0a150204060e0f040209040c12150b0304060f1401090b0a0509070c0f052508011503020a09020a090b0408010c020105180607121118120a20 69
    0x30202c002441007211140c1c86071600010401c3c20759a207045860300c00401c9030540624014030042144d250010100c00000c41c04503146101143d0000100c1c00a0094106007944503040000c00300318036400c4038101d055101c050009002c0180030310703161a4404154032544030034100c100000380200b4a5984034040ca01000c080c041001100c1202040040c442030300000c01040d99802222540c0ca00901b5500007020141c4500340e0030f00d0540400b40c460f00206402500720b052610a9000f082801d2007803040c0c001c140c0c103000398041d083c0512600c130303041c4500075a031071503180c20746082505080c40783e0b8008481e03000705051a021f00702015007019410107401002440507071400401c1c03100c86600908050840040009168442c4e100000e080d180081e006421070100454241d405000c081f83d100c0c0c4c085800c1c208140c1031421000448010040d070541c1c001e0092010860a401c101d41e0404002d10f104200c40c601541c01c41a49070035103980000c030b00141404280000380001c00000c41140e649400d000380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 77149669 1250 77148419 77148433
    0xc01050706090606170f01060501020607030902010c081201170a0506040f02010201150603020a090e04050a020411120408030105041113060305131a0106140f04120c03060c03050f0a14040b09 83
    0x15500702513a0281e0041c5914001e0460041340301c050800422070032110750750081c41040c1c90040080c1d02e400010300302000f010b132903e00050559005a080f001d101d0b81c0608010703580c40300259001a5002c0a005490008200c0040c02c0c044d04000110030039101d03040301c0908480c1d03c0315030b00c0303015011071018100e065540351540d00482e004003031000c4009018907100903a03502c1a4200040111015030019159241c02130144070100394002100c20400d0790603030700001c00d0380d50f01443e0075290150740c1c04a1445200b04041004100003480958100e500a44007031084c4201804070b4100c90142c000c0800e00860981030412059102c0e4100c3c517085160201d446d20f503030000d5103614040071507801820244050701e200400c00c265024810310403141c4c0d4000000c0c28141000354035181881f03980724142d0355080481841d0180a2141d4102009580c03000f01000415840c100c040c02905088882c400c0449070071001032a4030360300d805140020900844005126582d1780d64203d4550b401500807803003442954 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 77150919 1250 77149669 77149673
    0x30a06061d131118010e010201090c0302060708160302030d1503031719090804080705010503090d12111c11040b0a050c030c06100807050d1e0302010902060d020a140c0c0105070609 79
    0x34010920400f140320f0303c11138281e5050026150300c0000158504681c0351401170004140c01a0f495000daa074100d490703a5881c1060309100025020300310315a0300c840600c0d0308940c1016000002031420071101d20051140940c81004075500620074400a808964041844420510301904556016100e80c404040360642c1040c0e60301250a2400704440b03400703000505004a440c10400440100302c00d1130002d1841c540001704986034a81010f0038000d101d01103428403401d0706290421209a801c3c05490b80d20383c03071034600303040f1440480c89480903080c1c0b0705041001c049560300201c509481c0075130004c1c2c6c540109103070126080d61007490b0f807507014003082c08032042901041c4816801030503203482d286001400c0604e9581400c1d91a0320040c8100b046610300c00000b40480d0303034030940000c2011070549412190034280e000d4044800d00a500c000300203145210303000d40d9805048060b14a0ba43d14518150305106502700780318841d00e100c0e05901003250044150f01c11801062841c2c0300b5400455059500d07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 77152169 1250 77150919 77150951
    0x40e07090c0c05010b0d051e0a05150106030e060105010f050f12010905010303080702031810180807060237020105070c060305061003090b1f081002030a06061d13 71
    0x30004290000b0028401081444000d0040700345c061022a4010a800e446564150b5100700314804d01440001c0b5040e9807504150910003180455000401d032402c0504800404485030304c02d0043c2c1011901e4450401416000001d4040c1642e8040e101c4002d00c0e41440c10580740c1c0d030004174514490020421006503414201c080c894000c1140107000300303d95041d850060240b0340014100c5086620600c5180c04e042b08030080105494000e580c00c24104d44400b0b01110480007044842000102041001400c1100041c031a411034625509990070301e00305246100c01c25114024214041081c03000342180310b50604200c9104a105040680c42c0100d5039480b801c42404591050021941e20803c220240c146895484603520b003500e020840e2458030f075a03c2c40c07052400f400d0614a0801041ea04610004000080340a0007980c8102d030510280c04001002a40c0101c0782402114108000050720f2401a20385120303513400c3c0001902001c142d4018000c2000926038001c0d0300c541c90b0449002c1ea842d075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 77153419 1250 77152169 77152181
    0x4050303071202060609040f060209040204080607110607260c070f050d031802031b0402090307090504050c0303070c090207020f040e06040201030509060712090501090209010e04200f040e0709 84
    0x10400c0c0007820084001c00213801c1600090486002d545030a04000000e681481305102ca00d42c03103007005881c0c40c00341020400900560700141c07141d100d05400c1c02a2150090740b8940e8204960040343c01d1035603081c1e001c840c0080c8180345400b41200c58845031051000c0c10a10b69840700c0d004a43e11704041c042e8554608001d80c1d450240c1e41608008130040d40507516002c0e010803c5001c29410b52018010381c04240c1d1901030424074400700035070f025404107540d680e40491f00720b00c0300103084503a015102c0d10601e00515003958101d8440c4500581c407000d42c2400301c152549141c004803200e0900c1d00d040c080c40701a50200030101c2e84100c110442c0710103a602c51040e015502c045030000d04c041c2c60103200150440700c2c00340071100c0070f43c894810815403d500c000c5d4620042d9541c440425800d40c5443e060380941003c4400a600841030f1001040c0c000701039201a105038042c0c40c091041e4410031604080308000d800101e80c102501c8002e00e81c06051a8014006441084088800d01a6a00351030011521 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 77154669 1250 77153419 77153423
    0xc110a020105033408070813030c05120d0b01110f1c0903020301050c0903010b0a0b0d020706020c07030305030919030e12100f020301050109090b091503070b0f030a050f06240405030307 81
    0x208600140f81c10b54401750301580305a240c2458006810320004403454003149103c000e08001151031150100101030054810300b6100000203601e40444030034203005460032071241c6001524030300446883d200001505120704401001421100c488003120001c100d2800f080e50341071008401c0e0000058409104e07281c40b40a80342115504e482507002090b080d074684005007486102c4142c0d003485818101003c0f42d91b9070b8185a801a80c0b50b10a03c0d1074806401080f0118030940502c08000080c1500103005604c01d02648068450034005000d008102040002018000480200360340c1c8a50a10659200c903803462807084a9152641f950104295221106290700c0b5039008001044656049051003000c0e0006c00c0c41803101c02d04038000b25840000050451241a039112581045914207003c01b0010b08155140c540e0303903580c0442002442d503c00e5a040300c1c03039841c050000c6d4420f440345540e9805054010001d0752101d80c1000151101c0080729115018810200b00002d01d81e9410002880c09034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 77155919 1250 77154669 77154751
    0xa121a07020d1d2215081015080d0305040f0506070c0510091a06040b0603100608010b041211041d06060a0602060108030a14040906180c110a02010503 66
    0x503640b65004141403002505101c1c080c0085421100310380d40c1002d003003294001d12000060142c4000b081301c001c3c2c01c1c0c040141d41d146074012804641400003042240e2620041c84040c0140c00740c010b04410700c043c0520440000d80c1185c0a14540300344250069500240a8030405000d0f10054031400d09210064610101181848040e101041400d1000e41e132121034110080010f41d00c19165580012001e80c09925001100c00006da080d548681c021400d0b184080c00c0c16890b4580f6610503903084034140528000302d2a820300005d0340700090400c50b803d40d030740390060803c40c005035641c2240941440c03e1569100d03031603800c0c040b80294a0380012801c100154020320b010f00f007032010305c0900c2540e03400040c01c540140c001401a0200001195002049403424402a5030100b00e43c0100f4040d0f41c0045801a041c84800140c20758924440d003148412201e081044140701e0000391b81d100c00403400c040c010f4100c09540710156002e24080c5070b2140e0394008922311170705948140d034400048284200f01907 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 77157169 1250 77155919 77155933
    0x9020118082b020a0201032a0503090613020f06070609060f02071403090901120f150905011b09120809040504060504050609010603030203070803180f010b03010b01020c0a121a0702 79
    0x31112a0b03141540307082000401100c0d4603103900c002134440e2000e20019060545420025404406058511101c0324a0000c40e00c00455180c3d401407a50b481074034051298440c1d4000301c0c44266807601800310351540204072401d0759031903406108a80d0050b0405560403680c500b0403030049401030151107074803841c00d440142e40704018604490403409002012645e6801880001c10a880c1c14213070a056a04003812180d40c0100351402e400110301200000f05132802051f03c0f030182e00101d400000002d84940c0003480010101003840500c5585001102c0000350000c0042150011715003440d030f40b1074010390310340b4a8003580402180c2651407e440441d0140d586104100a01209120640c1c02c8080080240501403842c0c84c0290b81e030051303a0014001003000004a4a0541d1206040001d450290151070f00101d580c59005e008001410140e03000c1c1d400c2c5080c802c907540c4042040701e450400100002411b50401c6c0c816083e29045a0381150070200c21040114410200c02075107206901c0c580c002d000c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 77158275 1106 77157169 77157193
    0x60921150c08060a0b131412030c0a1b0e01030210032c0d02030a1e09030b01030b010510030506090a0903020c1503040b0105030c0607060902011808 65
    0x140a00e00084050349541150b0440d02c40c800866a1107203c81d42d80e0002c4040e8403c070620703403c1c000c240d00c506101c002c0450180e01500b61014140e1100d001c110800070340380da4090318420b041648404003a20400002000350300811101201c001902d078078215865038600c0c2d0600000f4403440d40350700340e192400e1003036000400350010108480c07115104813281418034040d808044503e4025030408004403070002045540e20039850f82d54101c03840001032a1242903020341c10307140030801c00d00c070000007040441d06441d0207140035109001c859494001003007030350f030320181c020030916044c0000c0046030342d101582d0580c04003c100d0007044404d09881c0403410b00c0c0c00d0203140c59015201000080b203000070708015600c1a84242a520880c2e600c40e010550360f440244101644a203040103214005025608101600d43c4181001d444000b00124040100001500f181c40103510622115074 = true := by decide +kernel

theorem cover : BRFrame.Cov 76978419 77158275 := by
  have h0 := BRFrame.cov_init 76978419
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 76978419 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 76978419 ≤ n) (h2 : n < 77158275) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
