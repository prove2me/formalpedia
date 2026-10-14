-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0500
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:07:44.698905+00:00
-- url     : https://prove2.me/submissions/0f89700b-8821-46ec-b7d6-186890f76dd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 89748202 ≤ n < 89928058 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 89749452 1250 89748202 89748227
    0x90114030a0c03060e010b1903060b0706150605090a0608070e091e0f07050a120204030605101403030412030c140609161e051002010908030a05060f0a1401030c 70
    0x201944a04106040701e004103040c0d280c0307402007441c100e4009006000d1480250403034520a03030b0f803030070001c1c0410000d485600a0204031304140e61070b01c0200303051b0311180181154602070800000d00b00c00c2071401104491036500410240321050111004a0f5a00e5401030241c0d1402c0c981080309850701d1900ba20b0203400013000c1d80d400140c0c1c504201411050200442500380104080d04554031242c0003d40800420b03905680010b90801c89100200d00480c4d08030030700352a01d08010b00e82540e03a1241030803200c0641e40c481002134070701810003049030494041c00c0d0220003200514506072410424007044200101c006040c07010100440c41840081c08800e16520380042c190782d40b502d0301046050321440c80d55042000020000701c041446040311000c2c0d5080a902614026a41d0505041201000240d10a1000c56499040c41d4000603044001f030743c058a6140c0000c1114180001005020054804c504d400b540003004100280c02c02403051032402c860030700700020341140b039010460b00080340c4503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 89750702 1250 89749452 89749487
    0x3011a0c07030f1101030b2209080717120c0f040e13140609010e0c03152e050a080a05060c03090a020414040606050d080409110c010c020d0206010801090807080901 72
    0x80d44402130219181c440311510209a038100701c800c103568108200c11110305400110141180300c049400041d541c081e50581f4019080d040c24030303c0f075982c0e680000c01e480c07086801c450004511072030030750000359125421101c0406642d0420350820000070035400b0390310401a035100414040741103068032102044240b5004030806c41c8490b50040c800b55101002e96102c030103503103402085a941080440c001a04000c0140a007600110300c204038a4940405400f40441400fa02009803060925410880000301d81030300c07082d0071514240c20852190400c0d800040240c01c07404c0260b00240e0b0209445510680440f44151261a158402071034078502c100020b420918150f5558191715003200704600c07030303807146800340321444c2c4850601455214580005000074414002840705401c6604000110140074440c3c90500c0740118600c0c1c20b603500b152101c130146c5c110605c1c41414981c14072a048c0501000c400030b1103180c02541d03c4440c0c510a580c005407160710046040101c1d81c1c441c0d042c40b0400d042c1d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 89751952 1250 89750702 89750723
    0x20403060c09050907230a05161407090c0f27080105041707030c030302090301090f0b1801060b04170304050402030c1213030c030f1404090606030b0603011a0c0703 72
    0x240700c090152075490081c980308200d4140000c010600c9010310702001001c40d41c850300d00c16490482c490b81e0f60800f103000c0d02804401c0c8040c2100c0222070610f580c40c24059011021034400801d0220f08014003074000d040d4090030820201da2060b00301c81030044000891134450100c1103011600c481d2058032100c9901001da24a000140c1100705421244c0500e0080d00440c031030b11807030880c01100d4030a0500c01400f00303131038554100100b4041c0e0f014000b14000030b030000c1101102941c504904201200048510107001030600444c20540b10318482d4511201e00208540c1d414450441c81600492103280c215044000301c14104c0f103c14001e1343c1c020540500155140d0400d00f0a00105400104c5003c000343c4036400050384901107241d5508020790180c03901080a051034074200e4400203410701d040207102d200d040328114005018010310041c10125400510a41850030040580c2c0344800c01510610301840107000b00181509149502208940215925220982c5a900b444003c4d0700c00b406d2100c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 89753202 1250 89751952 89751971
    0x21010c031107050706080a061a07060c0806011e050409060e06010f0206060609011416030e010219020f0d1505150a150806040c05070203030c030c070608190b010302040306 75
    0x54012010690080d14280070000440404100a004842c40034090b640203036001c2004c1400f0300f4525410038004140818896290000540703101200085210a80c0c00060404140815486001c4603610103103004165801e1140000380140900e4015080d40c070700c250344000029000303604542c014081854144949070b03449228000c2d0440c100c881d68040361803515100700301840403030040d22844008001501b019172602c011191501075804103c80c82c8030401c01c00c103000402c0d01246203600d02c01d5860b02c10032002500020704000600c100f224580c1910201c480040e034901c00c01071190b94080d9000040c1c05407600b056101e00d030540328902c00503481c6c00140514040960a4502c030a0000e4820a00203903a07000c00c442c48014004d01200001d00000c045041480c1640121101c2c0d00e1501c0c11074140b01090700003d0440c0d000d004403c0700c071b07407001078411842c8405101500c0284183e040c41c01041c64038212100d080407984000d8034000303690f1001101640e001c0e074160340c0610742240082000540 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 89754452 1250 89753202 89753269
    0x70f0201090b01080c120d0518060c031305010905060a0801050f0307050d080a0f0504120609020316061d18160311030108030c0c10090603110405090408070b07030b060315 75
    0x5d014080070702500303210301c204048110015000c070034400e03140e8842e0b10b0403c1008803c805041c034075040542c0814100030303049210104101502c01c0550380b0052190140c9000c0001d005803a1542c4014065401408a1065150400d0a0754111482901c90200c1242d0510000e0b003022099044503a000a01e41c0044007441000c3c0041c200188141c0c41d1001c01c20038041d000d5420b4010741c440c03046182100f100c4000011601d0300300f0b50800d03102074115880801c1c0c60f0380ca1502c0c1e0030150400c10004409025000340c04000c440d29100c0ca4800740c0311000c010a0115400300c0d00680108106880c250380801d561415200f0303840f41d61415007210303003240c4039612501815100d500079444189a4800c110140f9007900d840c1209040c4a4926110908120f107000c009030701929264a0030701c0c0001085c400041c02d07446603480c8505c41c611401007140d075104286420400c642e0b0150941003014601809860140c450408484d0006c405800314140c0c00d8101d00040d00c1c0c4540003a01c3ca007144503841d02c0304412003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 89755702 1250 89754452 89754463
    0x4020d060e010305060604020336010c0203090a0f08070b0f0d020d0902120105090d030c020f061e0106080f060f030a0f06020406230f030702190b0103030e0d0b070f0201090b0108 78
    0xa04c00c00540d20103894900400090f804251143d652113002207516102e0658014080f620044540000d0381c80314000e14921404c4508078810720001d41c000240b40003441c5811003050004e04148c40312040000d04000340f07590f41c3c0181d40038032410a030000525009600f149400d5545130000e51400703650750380d404880103015000d1858224003403402107030108548201801140d11402910f4002d2994010660b000c50280041c1035044040d0700403144401d54114062201521480c10500c07074180501e003600100700c001105921a000f0403407440c080c001e08400128400d034001c05e044070305c01507105009000900386400254002c121b810b0800359072007000141c2d00035104894154503201c016503000046070010000a850b500300101d0100031250604225002858002001d4411204d103501c034103405240d0035078103400c192801200030300100105079000d4051042c50109845c610326052283e80e950124600140042081c4485180350340b01c0036100358004e040c0c16800c59503078085560b64802442c2c807403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 89756952 1250 89755702 89755709
    0x60606050d050a0b011e12061d0108030f0304150b0301090f05060115020303041e0b07080411010e010f0c0503161505010b1c09051f0c030501050a05060a0302070204020d060e01 77
    0x50300b094000ba960700241c0c400c40e0300b10782040e16461920080c01c0315000124040e139610788140040c4d610b0450000031b2510600018205500900074150780e200950b88074800140d2000c2070300d900802030301c540b00f085032058036003190740304040e5040640c030070003003102503e24072488075015881c101c9030340180001400c24042c001c0c010002c1d141d090f40c903068503641175440d0328414009613000b0004603002540780a590000350741c4010801407140760075512000e2418054920200144840c0240814801c98a405001140e03013400c2010b81a5141741c0041c051915184000d01480082c1c440c0405020050007142ca10805ca21180701c030100440c40c11020b28603c0e0390008500390b03c1c2900200344004000200d41c4910041c20110006134082035142e0068204410b00301c5550180c0002001c4504400c91710180c1880303400d0700482d50b101c1c041741c001c5c201c61050b403041e44565250401040651548004c07211103e0b8903181c090398a001c0e50020034040c0c0b140e4079004040b285000d000044508480c005541607 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 89758202 1250 89756952 89756977
    0x10618050a0608031e03090a240e01050106121a06040b0406021c0c0219051c1a06091b09120609160503100b03010f0609150611070e040c0306060605 65
    0x211602e61a500e44e0b24004e0040c0a840215042c085029100920010f903078031441c0e06044a0002c4420b03918401840303e4200303601e5005000e210100d10b414028020441c0c040c801c10001c00071585002e000514000198002e50300e155920081450b41080509040142180c041c00b1640e4036070303030ac202d403000d668040d12900c00180036a100304002c41401c41b0f82210340c2e1100b0394806850505c00e80810a075032205821400c200f100380303440043c49840d038001c1d4660216043c1c0d01c421810843c0e040c1100310318120902c11030b0603144081040602d50b1800500790700590f19800c218500301c449241000300c0c1c400c0b250031503840040d0304d483e59101400000d810344646200b00648003400741031181580d1011060145030b51642014503054000328103580119000240200041001c0e4154001d0204551070780d003050684948a00b588020002c105800701d0092040d882e0211001d900609000d0322413034130b800782c1002005500c0214041c80700c4815140302558001c80c0400129940f5080a4440d81c071020042c2070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 89759452 1250 89758202 89758211
    0x50601050406140a09020f041d010306050a020a02060406150b030906040c0807140d080f19020d02030a02032208030309010501050a0b0a02060604050c130b0405040b0907020a080c010618050a 83
    0x340f02d40700b8040c1440034503010344010fa00f2800e01400c00061342101d03039086100c21060100083d0a84850055011004003160380b094a5044d0704103202503500007009004654010041d00c05100c0e400503c1c00e40c895005480064642c0300c80c51420701a00039031b4000e9404410110500042c80808950740d80103034456036038401c0869403240d615890b44070360710071010440148030012a00e42420f0302d03465400d038820415117251100b45010329901350040180340e414500340c445136010150f0108064680d01d50a40025410802d00b40c1000750b5074864003100c41d048003100762480c0c4000100d030407400094840601541c0d203d1402d2900c5c140202000d02c10580f082c41058000540524040d04403903d40b00c1c103034050318450796480144006080042c200c18520881000602501c0100300d03603c00241c45201c0c40c1d41d03a00c510741810013060351840300e5003500c01c50f102014400c030180c001460194655100c02040d4407040488009030041c44640c0c0b00f0004500000101982503003e580490300c28a8540010071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 89760702 1250 89759452 89759459
    0xc06010503011103011703090604030602090f19170c040c0f180f1e030203030a030e060c0309060402090a0212250f0e130f020c0c18070219030318050601050406 70
    0x50a843c0036040741c65005504000520154140c0000d5842441510341201d180011042c00304049900030307032054a031180d0220306034107540b80800e10b030200888120340303281e04001240e1740e0456406561103403100e081c0b4146c080d8000030505103c8108030080082c0b0070005082c014002820010000c802c00300044d90040c25030760100101d1098000b941d0346281450412420a800101c100003100c0003400501c17111400040107179800c1000307042c1c0c59001e503000302c1e20748980218030f85000000303130107100403090510802980446c0051050f62094040300c00040076100d01c8940c800a11550703124406540300790081200c95140044921100c0c0501002840409010081200d0200100008000040407105031182c0d1349000b041829a07400703140300000d008400405c6190032a070040490858036000101d1030360003443c0c03080c08070f5034540820800c6152440d140714025140c0e968001007410004040c9804010705220350320001130008146060b2407540300307509059984410074440c152113181840c1012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 89761952 1250 89760702 89760709
    0x109050f030f12030919031d0f0d05010e010b060702030d030917130501090510080a05190e0601050102070b070c0504050c0405190302090703060807170127020301151404110d0905030c060105 83
    0x10000a406a80e00040c18a000f00108601d040234060b00f64007014000030800c0a0340d880c00407141540c03044000040090b00c8613505400d40b040111524400c14040c04031030050389012031500800c07043e81c90700050490443c640300c1d03208404400640c82031500401c071441d4000140e542c00c03050ba44240c03505600390f07981e4820881101c0e184102000080e00c041c000c5600f48617650840b9400c00a40300f0f02c4191211a184803c04803011815030355207962001c2d004000c03558041c0180805000808401880c0c8001c07900c89281e51102880360303034002c568030400144650b40d4402034502400c001014a90f0710f403c44110843c03001040e000c2030388258059000b042d4102d000c0c0c8184800c0b108024013030b000381c61400400c00840ca02c1043d101855540380e20b0b800c01c1480190b8001e2030394080400c641ca1580841d8010f16084801e180b84e0704858111106c2d05120300c41003c3c144001c0703e4400c840220740c10400c020a00c2040c041c0c0903a0003180c074104900c9008109000c406080d40d18901310484900380ea8a5041 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 89763202 1250 89761952 89761993
    0x31d09040f020907021906090606120206040311210307050d0806030706030e0f0307031107062606010201090602130504050a020a14030408190f0305150109050f030f120309 75
    0x28101d006090854006007402d11805600009500581e98005521b456444e5007030440442110400d40c2d440e6038604012640c800c40c4040c1280c1d25079440e081903103502048640c0702d980005001c821455103559810382d035a03d4074125841d10780c0b180000c0592000052aa644c02080e403c54141c0030303030441110042d108441951140170010000e00c40e0900e0a0320907030090450081c0c5203428000c500034180480e000700300401210f4860f03900c1450002a0115450501d0b00c03540044007000011241685840e44042c150958201440b01c007004130380710f00c401070b80140600c2c0301c01400031b03002145684451025403248401c540d030036201805269203104012040340305482621010807402c006200945003200f0145500c640314403020351801980061441c2401c603c00c1030756000600000d07074942d0950340f60240c15000442c266118101555040003c3d0100409018440c014076409400c110159000c1000407003442081061361851606010407101c00c4d807017110a04214460580c4404420084566 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 89764452 1250 89763202 89763211
    0xc1106360307061407061407080106020105060607030f0e1503150a0308030c070c0305150105101706010806030a060f0902030708070303090302060d0204030510050603010c0201060311040c02070b07031d09 89
    0x10b4028181403160039290310000f000882650b60381072040c10000b800d90f118460300001041c1d9000c84914207060010080b1105810020859061209025407521941c090351141949410020198414002c048680c20803291b141d5a020100c4142030702100d448900460107040389010000440c0104800d101081c1c2c030504c0002d01d4420f04200042c00c201c582c90190411900c6180070001c9559030b81c41e010318010002d00e1210000d9a0540104031500d407140003956124090300b0000f680080c2c0c1003a078030001c07400400c0702e81409201000580b040d075091000801d010350140f420410b08901c00c407100002c141c001710480c000c0c416004042500180001e4900450354181c3e00c2c5d420050948e400e002154128801078400d05800b8000072000580a011555003410003c00010300c1d85080c80c205400c0d900700c001180b0942e4035160007400815000780000000c08420741f00800c4d00a20044200d15000d01d5500603a11503002060030000c0582c0b0070510001c607100a0f8004140d03100380b400b000b0a0800984 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 89765702 1250 89764452 89764459
    0x10e06030c0a03060b01021903180509060d030c11060703020a0b0903040e07050d0f050901020306010320040b07080d0612030801081912090504050106090e0a02030106020a030c110636 80
    0x202d0400c001045a00078003005001841a95003142403400c9161140510359800c40c04118002482083c80d4100900d900040904895109035410018081040d16113030000c05410003070035051040a1102210a054a4100140c0070f5075445006040094131750070520b0085075031001107404505025000010b8600362584070040100c15252008241e4140e486a002c01100c0c40d1642003520801000e0311441d0b200e0b0100500143e41d901d0300c0400102141c101c50070f0358a64484660451520700c1941c0242c409807246140784941ea1a194209102c0714001e601c15035048505001c404514001c0c8401d03024502403081d1561103941c0d80755a8201d8481c060401042c070455100110315001c50b28103e42d0302d1203c4418205014085d44a0b0040360596000341c0000d804038100500400540078101c83d12940049041d10442c20341d4104003009480d0901064040c04001018a006040c000802c1e01280100002015282c1e948207900c4400c80f11521403590030700228030381d0b0a01e288035010104041c005403008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 89766952 1250 89765702 89765719
    0x4080405010813080711030115081b01170a02092707050a030e01060821030c03040b0c0c0a0303050a0b010c0506040b28061a0a120902010c0503030f010e06030c 70
    0x100044540e842e004180444038a1070003040d0300496000760003032414a020f44410303811111134030141800c2d511500b00c4500c9070700d051181001004800300d842c07469429400061103510301d00100407214044040c0481c00f04030100b200f8004000c442c0d43c02000c0042d4296002d41002c90301c0b03910140f01000401c07240084e07421043c0005c40d10f91142c2e005141190340c5017400104404580800703421682d1070341000f03407158048140c4008051108401c2c000391a104030a01d440c51410801d80f6410b800040d00c0101001000000305650b40318400c26101614140c1003100c205c034a5600f00240900401e850781c4004502e0f158052505500c0303151001005c41d0040e006080d25120766803100740c42c0800410011140c003c0e01c00705181c4c04030040724401c0100e002d10380485d000c2c2c2490f0003034056850220301c0c0b010300c407020000c0206040c0c001300d0070b01a03c040201e0015a18140b400140c0d1b002051003002001400000100496110490300d082c0c184c44003440224096543c00b01456030b030b0a44082003d5016091 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 89768202 1250 89766952 89766959
    0x915010302070f0f030305011e1a16170405010818030313062003010509010b25020a05041d100b030c0f030c270609040206120621030c070e040804 64
    0x294005202d500d205001800852409803a400507081500508400007070b1210300411440d0020b042e11901d40c182c000c1c60425551511068a800ac0f981380c6408009600120710010341d000e0038404603000907040b014420b03004001580c0301c022540140a094042512003000c203c02e14546003426000c100c258005500c0c40e00c1d448008504c40607a0b0208960003a260b802c11103281c0760200788007005654401d0702c29225410002001480401604012940501408002d905500c07a01c01031001274000d04851614000c0c0d400400e0400105812537500b0500b010506d84191310f038900c41c81ca1988444003030754812500c10718440300b92652240c07519410f0340070b00c10740046440c203600407892004d40201206e002000500100354401c48010207a20705816118180c10401504003515500a074119001e86813440c00340e0000c2d10500801300c1c696000d031141e100081540d210f10380b043c01442e0707540c4401c1450491007456503649612000005603940540030000581100740c102a40c0195400303084203040030305 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 89769452 1250 89768202 89768207
    0x71410031d0f0a0b090109110108090106030818030c19270608030c0d020705090106120e06040501020912120304022e0201020403020108130f030e0102160b0a0e091501 73
    0x910020402180142444144201d074003044480102d50100001d808440b4050a0000268000424510032030341003644001c00525944441c075500042402d20000c0c43d00c2c2c00c020701d401448103800082a01c8000225007400d003441c40ad45200c0f488041742142c824082090912400700c98083c60f00102046804c828400c061171204440031001081a0903102810710342d40d1300007922603d602001c0590400107050900c09001e001440c0e240d02e0600041858501c1e0030017184a003641440703000f08010700c5802d0614004904d03000074411920040445901d1b04050030310074002d50207100da1a200d9020b4501040d90300d0000300f43c0b42d000440000b441815030391160240041c2e050403c0420640d59a4400f90301c196524040040c40032444a500058440e0304510005d050a000600f844d080b243d44194081e001400704030072100469454500100700100803001030b840e011071403091810801c641d890120740c20349004060411010701d03a840c1c0590200140900c113001d40c01b500c19100002c0220b4000c1c44950 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 89770702 1250 89769452 89769461
    0x203121e0a231201261f110c03030a0c1e09090c1d1003020702032506090312030c09180f050606040815150607060e10110405010c02030304050a03120207141003 70
    0xb000400c0b00d0a005098a507505000c0c86032041e1b0140c40799012030888440051041900071600d61803c03d20313144c00303101d9465990100030300064205490b522090740092242c1603070002200422000c5110f00e440e0000a03181a020380100c03008203140c02d407400c031480c2c400c403810f5150340b92036003440b40200051801d2105000c2e00340e090409142d0200300800050710204420405a0024104680ca44000304110102d05e2081c0c1d024804204094a040c004249051038144011a5500340000c0c201030742d40040d00d4000c2c42e50b000004003500e040c42d490208680d07030007600c2c0400030003004018990f149410400b00e40124003864005501c414140d440c1b01d09030100040d04656009d209510300b0016100142d015449020102e07046134450070366203400340d010010285564900d407420b221412004003d010039005511901d030400202c8240d003c02e644003441190040c00014220244d803545a090164400300c100b4506001449600c00c0010000c08010022074000d100800342182929400011400b40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 89771952 1250 89770702 89770739
    0x3050112020d0f0506010e071e0e0609030109060509100501170309060a0912080405100c030e1c0203010507030501080d0e010212030601030213030b0106030c08040203121e0a231201 79
    0x10607120302c450046081001710070b0003001340f5913030059103181000c4000e004540c802920140d03002250480c19007540c20011a070780843c0300340c41c616211020340d0002809415507800161100b441c0c501808a40305020480080f0703178152407024003041c1d80c0c4100c1e843e00864503081d42e080941050110400740d180c150010040c6105500d402645192941100c1440c00030000c030071103254900280820060030910140c4046851504200c0180281c9840260091000c50074051203420311a05900c00107891141000d00103030080c008010501e0800805070081100b805101403034400c0c2c0e952070090510030011440d070040182d0107084520410440131100c0d07000549501c2c1415000d00c007803042402e0300b00d909030040d401504404070301d524003840038041b1401e00e019a000c02800fa41040f016840c001103003400c0f0812003d0980d542d034401c001c2034490406420f8003c040c0f2a00284445000c1d50129122192164580c035181c01c0c0d5249030141d0300c1601c200010b03014401850001082080380200d44d100c0380 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 89773202 1250 89771952 89771963
    0xe0f0103020f010c0b0108070608010b1e0a180311030601150507020f12060f0403140408070b090301060b040b07120f17060f030d0504091802011227030206070f03050112020d 76
    0x9000a554502e0705d118260080c02140c0c3c8582c20412500e036105404600404d01641c40900d80324110081000098002c442c109501c2030000c2d6107100140314000c45208400c2c1d0f001e500d4041510703440e203003523a1090200642c0c440d02c41c00d00040354200d4074100000009036140c540900d0718005900b44104c803c5040403d90b80300301042540c5100140900c0640e218075801d91403442039140900d80500401030809000101000034403051284202c00202c08040d10322092006448141e40ca0001c1d002d000950080b5070200e601140c00659070303145070060180707140324005044150b13a0f4010112481c0040f0b8914400145904c1003031941ca48401c00d0054000070060000f00030922150080b91500414400b0040090000a03040100051600c0b0300780301624075201c1c01101c140d182e0002085d40d0a00000d07032205135602d24034441002081485140c01c9019445c801c4078001007801d020b0344a04003110350030042140c5280540d1074611030f1240c10705075490003200121180380350b003e10042904d604001c588 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 89774452 1250 89773202 89773217
    0x501020d0e210d02161406031f03030518010509090c030403091e090e07032105090d11090f01030503030c0708090301050f1909030206060411160507050a0e0f0103020f01 74
    0x38103600c980d102e151403503000081c100f250b411400249026201486500d295080e403105106000c0d0110345030702041821100c194598842c1803404480c40c1d0300e440b198500d503440600000c101600300000e0180300b09441d0144c07000175403010055483d4440d1f171a01d15400340b100e01c00561034002030750140d6001402441e10400e1603440300881a458540c2c109500c629000345041085140d07003034010325004408842c041c2004503d1583d03644a5680c2d20104404814401c9201e0300715603100c1c4003515141880144283c00251300e03424034070501c1845607082d0f8080c0c10b0020020340c140d0045420325048a90250045145954040303003e209600114421203100078204943c1581c0d07038090043c64041ca584d4601d00d0401e007000b07034404044483c0c216044070b07010708040320480031a80114001340d11101c10760f00030601200b1503140700c8840c0b0488502c40010030411000d001440000a114415940240c03100e0001d50340341ca01d4040c13480421145e803600704182400503c01410030344900300301031f58181044030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 89775702 1250 89774452 89774479
    0x507200c0d0b19200304054204020d06020f04050d0c060305072d1209051501050d02060306040b0402070807030302090f061809091c0305010f0905010501020d0e 70
    0x1501c0840464055031510714000c203001410b000300303000c0711690071014030401c0003803c2c00b071428102c901044099040d032100440040c0901c60148145955459901c2d0284080c0810701d42c0075152250303488081d8101307100c1040d0228580c0c441081107005076001080e000300640d00d5030710034000c2d5110980280c0d11a0042c0b02c0016a078448240082540c1e2050f55001c075001c3c00c0880003800c90f60000e1204041015419444943c180c020a2014240740381038150383c054000d81c1e6050f60104203a03451142c441d8504201c140600c000800e0b821100035050b0070046050340d03981c1c02c00851503071140313020754844020000300320140782079841504102c0010b07001606101d0341c0e442d203030b401d43c0001e4019008683c0006280d400c903d0110f00c0f00c480e803141103428174186032824803002500480b120304140245100b00115107284410420b22007040000c0821005c0410310703c4000300980000e01c1244d1020f031112034007150041860050078143e400c180e0041c45040c0201c141250b06113481d14a040e00301d85451301d441d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 89776952 1250 89775702 89775709
    0xf0e03272d09040b04080309030405060c0d1404060f1206030212070303171608090a0501020310030c0801200f090307090212090a390f080609010507200c 67
    0x180d0003065001c4480c102180040e01d003100d0300707440c1c2000e80e1007805020200700001c1d0502d519075402542100f5015180e82d2a90442880c5100715004903911100c08510b00641550001d0066030141103540c50f060913090600300c00e80d042c016801420041030400c14850403051050b20381800198000b54007081d2103580341c002c600b50482c15480400c5a80040d003045c0149500500c8104860100000108880c5040490186200b807042045801c2029180100f5401c450030403202a0190300300b4000c642e80e0a1010403648a03c1d41d62000711010032082e180005c1142c418810340a02122009000640185680d12107909905c0109042103054060100c0302d000e440c2004840041c1c4110b650060f42d40c3c0b403140f24103e41c4480101aa8105c0e803107000c1d8100042d502515894041015541031420350192a5a01400e43c82818110403070400b01d02c000103410400d07500c0e140031645800184c4015442d1002d50500384c460899840011641400b241038008074070003045650020132105aa80081040300007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 89778202 1250 89776952 89776969
    0x906090103110703050c070e010f050d060b04050f19050910091707050d11010c1e03061707060e061912020403061401050406080a02030c0607081b060403030f0e0327 72
    0x1d80010b040446d40441c0302c0c00801441015008100000d02c80f98036102c0008100c00759401410300800300802203208002c030b550025040740781c0040092101e0701c0c000107140e40305501100e00c0f2288000c43c0000403601510f40c4181c5024800c00c50203801d01c102206040c9018049a410480d0190750010302d480d03402d06220050042280b250004d8091030955000091001506128030105030b49400c0d907000300d1540000c00c0d91001c40da00c075107003170300c510031980190700510407a4000e0107031068800d08001d01c404007080540640c0d03401d840301c84000e106c0100b4415a0b00442001d014542010641149028011980450714206a00f0007510b41a102c0c1d8030b02c810345407181c4450702070303540d804010700c0980303440d000c2c640c090b100060082c00944017940000b90385076001c2a0050191400007000700a02c65450b084444050f00285080162081440300b50356035501210181c0000385414030800c050301d07031401601c1424810300010340c20034515940f411003812058214013003100450032900320a8603903850 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 89779452 1250 89778202 89778217
    0x80a020a06270b06031903020f010507050304051203090a0f06141f06120207060203130606050a05010806090603070e070f120b060a0507031202041202040c03050408090609010311 78
    0x14105240d2107140403001d40d031150b5009000d080e4550010507800310b000c550107890a40082030480340392240400300741082e40415056840c482c200d4450070034990001045000e1a103014000c01c41640e071010200c51901054600402c107800415200d900051410055a0000aa44181d51000c081569043d070389503580001282c0f059101c0031403001c0101403606080c0d2000710880300101000355a110f05100d040f881c014541070011030240154039807501c5e4199000320780d214004664a09040c000843d800e00600c00031034000c4d0400f1400f007220b04260b14103200301c80c01030b11481d21070340b100010000096402008543c0503c0703000000200120a0300c0054010440b6884d40c4901c0231803494010b02c0d0220028400c0c120905000001c0410740300d21040b41c3c00040c2614040381c4650b60b03072504071400c3c0a0340c03018007846400820301050101e4801c070785903802442100c08100071403070400250305646007160060440541071051120300e0034504001d0120500516002400011051400c0c5041e0844d41 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 89780702 1250 89779452 89779457
    0x807030f020c1f020d0e012c03010504050708160e01121509030e0111010b0319031709010606031d0a08030c0702030303150f011b020105070305090603090a021504030c030816080a 78
    0xb1408004203030103001001e0045c11a00d00040c0002203440040d040a04401500b08103901d002411091070080641403070031501300400034821810242804d95a440341405841c440c0d02800c00020300c8c4250b1154071900300c49815001d034640307a203403420501121700c0c4000f05444404c03010b4100c24503410103204680300b0f640b00c2c1e15002c4603140c2000c00141200456454541d0580c9440c41030205079600113140c03d036404003010040441a001e18088500482d104940803910305041c083c40081441904440305941403039504008a001001d02042046641520181b4a070003940c0144041a0208029540007815107407180c54540309901091071a03208407559142d00c41580d01440c40381c901b9a1810449190074038001480500e0010380b11003551020308002c2c1170040018801e01014083d400360b45220340020102c81d101d01c0c0143d24140c603401080c804a04c43c00c1d2080002e505001c196054506603504102003c0c215801c5940b11360b03440e0705c208800034443c4119050040002c1141b8010800700440d075 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 89781952 1250 89780702 89780749
    0x90607230d05010e0105010e090a0c020307020303190212180f0307080f0a14010b06040b070606030c080a02010f03050c250804030f060606090e0c030612061e01050d0807030f020c 78
    0x42d081c40113050068004d14108070f410b2200190a544112840e900303d841c03000c000a0040d41000164030b944685d400084d050300004c503180541c040107907241124019650251000c41d00f844850001a10949580c5940740b501102d079110310307041107081c4c0d90b103000b4054100c030100c40e10307056101d1410171204c0c4203954a03407124600100700252240f030050404021002884640d0000300020558000c43c024001a02008103024040c8052a0031010085d60001d058080543c1c849583c99201c1980400c183e000c14401e5260358a0b4a10070b10600303215216031b2400504004108506040e0503140303480c2000c01e100d0b1040f503c07001c01c490b01c0040c80154807400820f000c1e150986000070643e40907501540a2020300e40080007403505142069a110030708103042c540d40e5881d840001c0d501640d89260041e40c0c4035010410081c0140305401400c010701c0280c02070820f0380e82d0300411103401d000c00720050200d1320520902000038001c0b235610203000405d0058900d0f0a03030740c0c40820500703c11010180d6405880 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 89783202 1250 89781952 89781959
    0xf080c04092a0b0c01200a09060c1502040b0a020105130b130203010603120504030507090608070909140d05210c04030318150e09070f1709010905030c010e070e090607230d0501 77
    0x14140c01d4004425110151420407101c200023070900041d51081005001e1401400300c00c0180148110524803d00d050454885440c0d440c14411900540ca802000d5840e00d000b16288411440c03450a04650101d0a84110760b6050119900502510f00480c0c0542d02c40d4000b000050300107521440130029650303000c2d140d030320f0f5050140c601b07145030b44000000c0d40307484004e0141050100354403060b1103006c1800310f03c0301c2291030714840a05500d20580d601e401040110009164060010007468103010140c610304000204100c6000b041644e8415031804100000c000090080030007e2103208011003044a0565030b0003c0900c0d801c0c40c41d09400010881d0f4035541c0380385860800785401c810640350034107014031a400040d1080b03c941d800300c5109203507600044d190720f601b50081d44000b54060240da0711030405c4025240a804a0700d002c0029019500380414014000440d103441000100001d140c0f43c2c031031410075102910540c52740c09802e0060080300204070076400050206072669100022150316 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 89784452 1250 89783202 89783231
    0x181515010e0603090303011202011103130915050303030f0405030403021e04050a110d0b04020c1e15060607060c0c0b0108060a05060105030705180f09010f080c04092a0b0c01 76
    0x500307940c070074461081441840340c280c80000580e07041d5582d0703070790160110034a1700040c1c46103800d588415510b80310000d01008403a41d0120002c080310ba054405200031b8440d1001e464005d521030181d02d8060740148001107004400703e03d0150084c4c0140203980c0781a84940124103485c0c0611851441110000b000c42000d080c588075080e8407046291040088881c202d48000c1540305112000701c0c0c03251a00c840c0000c43d5039990442e80360212000c02c88000c90708100b000400d4800207070107604075010300140c28680c0d60146580500c1140300501c49407502e000e07a82c0d140010f01c4400d0f40c19040207070680c401c8000900c40288503028064600080410b0302d0320690030300550f400200807504204090040c0b00d400b680101c103940f0074103140804515074030030a0340403520410b0401c5181c1e0b4810031450000401c103900da8104416584850265808804003009000030741c1d00514004280c0001030808007043c600f03264140101100001820510740d64601c100300c55134000d5082a2030503591001c407140480d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 89785702 1250 89784452 89784467
    0x301060e04091110030e030c0a051014010e0406020708040b030604050709050f010f120501140907050a170a0b030a11040c021c20031206011205090618151501 69
    0x4086400b4020544166100300007014010304150090341504a0300c0b440c24045e40000d46060001012282c8600b0364240903a95404002000e40746409155035042a90b80d06006610b1a061085d0b103005559180c882414440d9500170700a032452542400800001600c40d00200000d00111600b941c4a00307081c0c08000c2200d0010300f41c18140302c1c00380c0e000c00c03003a2582d0700741e540740d48024217160900c2d00102c9401c6da40c08085840d000007841c9010008110b8114004c404020000d0603599220b881d0303035902c1e09440e20f200308c0182d40c010980540254070200180b103101070740050840400305400d820240440d1418071145821030789031a85003c0c10b807a5040030304c20101219000e1000301310154400e62110202074160f00c0080401079030b180c0c0b80d43c1460f86d04100d4164988100100d03956420780180c0c6040012042d50410300103130323203641d19501c0007855000b07030340c0114110406402982c580350070b8003214100954103500d06008015082c103050f803119400c203200703c3c4880ca14030951545440014100c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 89786952 1250 89785702 89785727
    0x4090f060b031003061121070306080312064b0604030b0a0e2401030b0109051e100906080c030c0301090c030f020a0506030106050a03050105040c02100216050d05030106 74
    0x5007051003045042c690001900c03044a80241c0f001806c0440715000c0401807041c0b12004e01242a03070801445803421019030f40748a012030b990100409070b128200d05841e0320400c03040344034244031580400c0c414a800146450300010b08c0030404000031040152111062408401040c6104500c04403080400c1740110907080c408220b8541e8a01421560b43c2c52424502500078001c45540340c2c0c00d02c80e20350f0100141074007007000f08616102c441c069041c1c0d1200032024041101c45411180c00041c100c8501e0007014041d81501048418040c03c071200004201700042c2203805903a0340d0362000695006500c2403402810f2048058960382c1c40480500d03242511710900540a6891f00100c100030642c07c4101500303503075001090380d110741d40500002d20b0301607040d0041d60b4004000000020400c2e001001054a040c05480600a40e0307622410032044640080c801c10260300038040d00040c00006600078102e864010310b030000d20345540c0c0c496610f01220036041c032011a4002005100807a000f0f40030003100d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 89788202 1250 89786952 89786969
    0x120201090b0412060911030f1b010e0a09150e0108010f060e0103030503040b040303060509070507020306061206010b0a0909022d040b04030308060f0904030207051809060105010f1404090f06 83
    0x18145814441082da0010f014068601544c8040e40020840c908903001caa40070010120340c4003842060015480d501e051801041103011800d801c8565400b42000800700300340200b80d00c940c85e01e454414070142410181d6039082e01802c2c80f010400391000d10029000e4683c0600015840c0c4814402d003084a66a400946110700d12000410000b40d006040b664833540c810065040390b01c5500d0f05401400843d004107038041d804030104042a41d0010161402074006c904071072040d125982804181104080800b4950304804018007403075041e400107000350040ca1078441101c036907400f01d12040360040d03136544400b10b105105041c1c20341541604610710341030500b0500e01e05844d124076120325100e82e10001f0280011003000901c595a030703030001082d8007000741521001d440e01d03143c003c0d01c443e10303800f80034451131011a40b041403908981480340700300302c040000c0c01c4503400d01d40107480c1c07851405003d90801081c1c0d02c1213410040e448029000800303071310b0787c00300300346203050071200641d030164120500 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 89789452 1250 89788202 89788207
    0x21204080901120b0f1c0503072d12030c020703050a080d0b101706010e0405040b06041b0e0d0f080d05070906050a0c06050a020f1b15071e0513120201090b 68
    0x103207550b0705d40f007041e1449000c035100300600303084080d001c46171840303035002070b10074000464a0b0042c004a009040c5c0d440050641d182050ba1390340880a51030001500080c09100d80300c0c0481c2181402070344820f24545c0709004444580c4d07569034485141401c00d8804a40000700070400b40e403140068040c0010501c000c48a007404181181c10003001000e801031040d06c64030350303503002c42e040e64000c0c281c5409200002e0b000b40814902030500c1245284e05940c0c182c05549001035400300b00c0810b25454440800d282da511045401d1542000800414401d081c1c40c43e0580703500440c0020343c0318005110b00c0190540100c1c5502d04048082d1494500fa48030340c00f031000400903444100c1e030042c2c1042d003050b80038a0001d6540c83c0ca000140080c0500d440010f010100095502c40724498175401d0324800380031008440c0501c2509a0b82060f22000780d030990046882c3e8040130071480100158003000c2c0040d8504107080c41d003241c2420700003e089920034441e6040b40703903100c419540e00080d5140500b002e6500d151 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 89790702 1250 89789452 89789471
    0x50d02010b0d03210906020705060a060605071b1203080f1f030b090a020406090e0105100f060503130f060b19030302061501090806040c061107050105160602120408090112 75
    0x40740c0c050b9081000381082144000c901c0146540301c0382041c8507030b103080b040192034014a010303002503200060607030f51440303071400080b6040428040c0e901581c4541c2d0320b85041068681e1541c00351001d07807100001010540e1004180ca4076903500760202c07035021303640c5c850882c18201014540c41102510405484803c46100310500c0070b04d8440001701c6c0c0d41708004410715680c403080181858500307107000703601c039080c0003000a00c0300710350b04a240c000d0103600003003140d0b480b003140c1c20245102d54403800140020b21041000500e0040340595409005840802e56510042d6110302c07070402c01140803100c86030384003050405803d1080d0f82c00054001901146030310303815520069520900108101911051a022406541d209040d100020315012084a8076400c00780303820004100380c2d02900001074200fa070701d5056100c0001d1820b04440741070f1522441d01098000d498840840411700b0b48980e5000c01c2190f03110081f04000c907204a01941d0050784600c0d00d10001009072202d407640001043c10150b041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 89791952 1250 89790702 89790709
    0x305090303070c030c02030609030301090b040b030a02270108010504060c03020304030917150a020316090f0312170702010e0d0507050c1003060f080313060908100b030c10020a050d02010b 82
    0x803600b018150a1800c80260545022514441c0000009406009030801d0203060940000130318180ca80c0c3d84401d200d0b595110302800700310754041c11f04a505900c01c0ca41c00303015080a0b81c002031750f0b03000c00325454030b41e880c80c0b403611b11071540a80c0071240f00d039500c41c00c1000780311b09445183e5030004586015031031810252001000c0b583c45018104c104034582e007584041c2041000320004041c281c0b0040c0680d4500603030b82d00f009400442d40102d49062000305000c0107846a0f40c00303804c0e03503030704403290445c01c1c1552507512050350301e0181c0d00c0c01d0101100c10805d107508407084a502c280002e0f400411081c00c6a0320b468101005500b103d028010300b07100f680001240400c0c02016403809480c0c4580c401440c0c04220007426565010b103488190b281400700e45140080f00801e00b030240b954600c411150f650804640ca82018840c0d020290005988810400d806800c4442c910b0750007421a40d1800c0c5c403000051181c03094504880141c0d22024100007044024030040340c1220441c00200070500540020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 89793202 1250 89791952 89791957
    0x1e0c030302060f1e060a1206020301031112100b030a14030310061d06032e14150a0c0c0e0702030901081501080105010819090308040311010b01052212030302091003050903 75
    0x9504c401c044007030020720542c60703001c0761310020020a880c0202c640300a0a001000750300030700080c1c1c2e425070902812495030030301302030031035180054000038080402101543c0c0005c0c1062001144e1502400b141c03000800c2200c0c0c0440d0005000c40041c50b030301c0c10f100e00300001a001650000c07003800705658440541284108100a404009450361130b50303503403038404900202200c042400d8100300f01400598814000815207815901c0c030614140008104404020b0810b6849c05260a400401c0186042c4188580100c1030200d20030000704142c2501d0382c9075a148840201c0c1c1140c0140d20100302d03900c5070740e40940701d01e401401c0c1c040107600041090380000d0860205004d020b040c0030313100740032072400000702c0f050040c1c00852640c100b080d8540f91500410101c0165400e400154020301c0046051a061203004402d00d01612410700d003100440c1e8000c0401c515100c408031002c0d04850000d80002c44c038020f407804520a0b500141d580c3d400e0010880c3d1038020000312000c05192004012600400204 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 89794452 1250 89793202 89793241
    0x1051005060f090414160207080c030615030a02032a06090d0206090a090501091415030a17120108060702070e04080a031505040c030510050411030c071e0c030302060f 73
    0x40c0690b101c031060f003c80c010780850113a108030000d951080041d04c480c01450202d440400780e09407180165140446a17840341d401c4403c0da030540009002c145410840c00e2f003840700d64805404d40e41e0402c2e50303400007810144202c401000c0c12030781030b198008500600c070300c0149a5400326101b90a10002401090000b46440070080c09003030005500080c6554010854000741490749040c031007980c442e51603502400c4515950724010710031101150260840d0000d00f00045c130080d001b0034400440391101c14071008105c0b4198003260040080101c0d807503001e414140030b000910700030300b09802c02d83d100030720b091110740c00b461001c41010b06101c0050114000c58000c0701007841c005c01c040b10003040001e5204610303841240c0c0285003003902c00c5181c0d010740005128800c0f4072200310166035a0028401a03039000900103103136041c02c00008082d554024050040344d4001c1d001a401020003002d1648091988401642d0030411081c00b00704044c3d0420041d03a1200441d505500340f8102040c0c2c0b000b41092505 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 89795702 1250 89794452 89794477
    0x60b01020a0510050c040302102f030901200109050c030f030a020318130504050d120c0905010507050f06010602150c0f07030c0201030f050703090c0509010b0f13030b070f020105100506 81
    0x3001c21706030007400c41a200a1a00104a100301c800604e002812002d00c061304036a054a1140c0504920a01c6080c0c01558484a00242d0320f81110180112800007111a0381042042004d1450030400024803585040d103101d42c00800c17080c0d0341c10303040500d4034488d03426004c1d880d4020403004030782a43c040192000207200e0545807019020b90700020b101054034500240103285004204400d00c0310000d8003014504064070380301002c0002c102c916080e182000b1809001c511907000c10040742d48188000c10449005400ba02c10344144c140281e8101f18003a03001400580c002040103100e44010610550840c10008201e0b00e030030284002100e0034059900041d00740280d901c510415a4044d4000820280101504000300d1400301c00180c0103044a00c01510704050390a408900f070305000081c14180c482c192502e40c101055603031403110b07544c001d082004a081c0a13030000000500345014050144000d40c8031201144203180300282120001010100e0103c03c010040001740c440d107048610001d03280 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 89796952 1250 89795702 89795711
    0xf25051c0c0501141602010606080601050f040302090a050f09030c0a0209130b09031308060f2e09020702040b01180303030c090810020405090f0c0315040b06030a0504060b01020a0510 80
    0x5900391034a640055019205509214211441692000506108005e1540c005c426911002c4049007240c019024050200744d00c5004180790350f0003500604205030310301a50354a41905c0794085800c440e019242050300c50b03120320074408569042e082c110f60008104005500746007050105a0f641d140c07042010780600300a1000c40c40351098a088e051b4840c0d00404e580c9860708002e20000e50300d078001c840d6003209203040d80d40441d00740d4001c286d950050445d4001d0180036164004e41d8100310760401c101d030034500c019402e03a0013190f580a240d6402010078030801a21181180140015601241806410881982d5160011540d1040c0c41c01c25260145000500c80c6059441901c40c2034083e00a50028425010718516031031082d0001d000b600d0066965200c5500c3d4a400c08040c07244c246c41a4155410610000e035058100112002070400000c00c0404d80121050218401c0d900668184410584800030403080c09218041c0601c015020f10003480c620901c0c0d2203181d11407540c014075550803500c6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 89798202 1250 89796952 89797003
    0x15051b120411040e0c01080105030d021e010209030a110f0603090d0e28030203070906050102031b0c1c0204050708190216051507110307031704020102120f2505 70
    0x11951107880702c040c0600200544010314000307907a00c01014000500080d00305001041b2800c0100c0d2241c08950103030003d015521100c00b190740360520503007240580359801d005206c41ea5800b0007041002d58003c40c044801008407400b8421a02034140005000310410028000700385800140030301c4410880c944020b0751500240080c40169010002a0b030b104141c0700322074140658200032500b26882101107500369a41c8080c00800d072840ba10565025030070034072005010710000307423030510a101660300f510200840780c0c0006002000c41c4041249116066845c0382c114200ba10a03103421014900381480c9602d8000f40c900703070080d8140d1042d1785440d004600b02e08424400e03a008910700303034000d0039130f041f0034280140302e5a1070008403117501c0003c03c120105642140003004684203250113a49081c800d00800201010301400540100d0441c0310750405802c86d6018a4040c100707003e92440d40641e2143c0707a400400d031501550199111035a05a4811400180000340e04c44506031142400d001070001d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 89799452 1250 89798202 89798213
    0x60d060b0301020409020d39140a0305040203010b0d050d050c010605150a08010608040b06010f180305070f080105010e060d260415050901021f020d0915051b1204 71
    0x4080e0406501580041004101c20b003d90700a40201d056012080185040155907100054220203091407820f003101e14181405130b614148584d080300e582481011a02c45586424040d440701e040200000e5440050004628080c054549840400c5800c49501c24032510f035980c60f40e24900102092101c006043d40048100303400510080c20b00600035968100d4814050b003d590104107050005181c0c000080762060044d58058021904a8071740100e640c0c07480019604001d0415488040c4007580c414184003c4120900d400030b0351041d40580f409601d848000c00000c40c2d40e4215002c1a410b120041c8680c00e8035074200ca5001e00100c40e4556050030701d041034800a078458400040304841c4007400c1200c6101d20000f0001c0391480a42511030000720f0700106c8150194031445070068000000c2601303154005034100750304200540c801840c104049410900300c96a800c400c0f40c07030140b01c1c40e84042000803841400d5005c0300141004003c0b601d0410202c086100d14241002c1c1051482c010906208 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 89800702 1250 89799452 89799461
    0x50a0c121a0a0b0a030503030f060a080d080c070203010e0a0302010e07060804020d110607030801031e0f1b08250e06030a12020c09090303040501061401050703080603030f0f03070305010605070b060d06 88
    0x22000761601343c00c0342d00ca040c900c0c0c4980c021141c0c0325800f01510040352950424040400445010f4809402041004507003280c1201010b8030308000c5810600c036132405070350280310b000f0010904800070720b01d075909450041c4c01d4910b40441460582c0040c00c00700103494010304000da1050f411034002c0c25400043c0b074440d05080c18995502c0d04a2004200602019005486070703059a00540002d0104030030400c051038105c0e4205c0004200c00c1e07a41030140009043d0300d5031441e080e014000d0f040c1007140c681400c1450310080c004c41c6040d0b02041e90f1121a01440109600007a091411501d59507240410210380d440d146020010b003451040a04030130324502c00c0c0b0165003118001003001e403003801d0446029549800990301640d0f59440c1c68400100051200d10b00d255811701030f110b15042c0162503c082c2c0344100003c00880e01800100700c2c034004500c540005114522151203001d480f4145010000c0845005821540c180102080101c1c00306682942c440c1d4003c034210781e00c0722994990b04e40300c800790 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 89801952 1250 89800702 89800721
    0x2060717060604031703040c050402090d0b091203090309010305090106050603011712040f08010f0b0a0b0d0f020706060305060106020d09140f0307182306120a050a050a0c121a0a 78
    0x90901110303180041d000c42c5c0066000301d018030b8080703c0960311941004102d04c00c1c100585e6000408100000c0016072000f000340c0c0c8034032050283c8081500c243c104142e154011a50803025810000e041415136070940705a940041d010402001000e0030000071440701d12040c040c124180003500b0905107044401c221244852212512086e00c81d5620b240110702d2204a0180810950a0200000302c0c02401e03c5514a0b8030703002404443c0302454800500c0580d406901620134803030702e44190088184180c0003c241c0103100d250002401841c505005090800c10f03000441150002c8401b02d256a80c0442c00307006441c0200014040e880b41d100001d0285580f25000582502854000003071055503c0744611803480c28800c02c1c0604040b4410b0440500c0c0c334024000e80100444005c14030358240f022b1004445005501151545c107400d896143c60240c0403401211654801c00190702003280c031400d45801404044080310328200d00d0356960360b40d00c00d50100142e045100b00000340d1303082000c3c2c0018824 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 89803202 1250 89801952 89801963
    0xc070303111308150a0b0f191a0309120703120c09080d110c03010c020304090207060612080a02070603020306090f091006030c170304030c0902090a03120f0f0206071706060403 77
    0x8060f42c2d100801d0301e500112010740c0c450030955000840e107030740b240904940c6040042c41005d101682008000c0c031000d018a800f10340b40c82000000c0b80c00301031070320440141c080c540911902d03407601000081c40d144001d03160f001896428408640006c2e04086102c10b07203065142c0124281d00b0b0044100c83d0015a644007000170700c29400c4071b1036240d80210035507101045d0741096070300d00071508040c14244d445d550b001400592080004110070801503010b004524891b000125090382c1d511405401c40100f58020b99480c1800513081c220103404000040c01480d1904007581107191400008594080082500f55000c0c442c0d00040d42454041c028584c0c004240f04042081588a052454a90445004070000000c142e2120b42000000000f5a000c0301d0340034400042040c20842c2020194003e280317015040629440040000303151000595908a40f60359400d48030103817410000c10b0182480b8000f400c1d50010010300642c20b0b400300c012102d000c0d0007039504925490f035101061f110f10440c1e0010b00b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 89804452 1250 89803202 89803237
    0x222020f030a0e06010f05060a1409120709050a050f160e12070302040b090c07080c0c061206010f030b240f070302010903020607080c1b0307060f02030a140c07030311 73
    0x14140c0c41d4450321804443c0c0040307801d5070b0707220140781101e18014014154000300c2802641c1c02144104d85060030b5400840d080da0a0003204000f08d10308800f04c90030900e494202d00c03000c0c020035045115140d8060340036001440f49040071420040c5101001c1c00e00c0d0f1528800c070800b92002401400d4000415a018000c0c407103d10426403019211602c90004134422401c0c103100180780d103807a104850260f800c1410451500300c03980e5640720a503020580c5002c15008850004c85503540d42c030042c00b00c80e90030601c04425031030020001001549070503040410b25142040d200402d032181c80c000c0000145180055140c640c494141e250180a00d5240740d4103150001052800c00d6810742006c15071074402d8088403080d861b03c4ca4140c4c0d01810450f115010350f40140034114002403288161410198080141e070703d0001c19444600c2540c0c290048488482e800005102810910344030740c0e40c880d003900b80300030030030304000310780c804140b14050000d41010b854444c400286250300c4112101441103010020 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 89805702 1250 89804452 89804461
    0x307020a0f0f05030c0907030902240a080619060e04020403060203010f030b09030a170c04080303090615100503060402210103030e100c0f03110106090606020c03070f030222020f03 79
    0xe00801c507014401050034948000a42814001020107440500801c0b2100581c3c4201c012001450f4601c810307607020350380c010540d120565044524142d4014a085240d8901110307601511140c00944103074011a91841c0180d900b40a03000d4540c1502c0c01443c00040c00849071000030041c0c02140c1018025605c00400001c4045504078840c1c12644030755001039155403040042c645034042c80b290400032034404600d001e05035110203040369008100200c19070030242c032650980e00d550401c130350200b4598001c4d001d0101c001160000200502d5080311084003104a4010041241c040070300094003030750f00400e000c0d00c0440b000e404200e10314000300290301c1719a90b90900801c001880320102d07018010b0100c0010140c5c0c81a51820740564114111201c0301c0256903080303800d501c0c0c08442815555a40e07a012410300741500922004010340c1e4000e20022000504140c1040d09a82c00021310200d00401003005031070303c1d10305000c500d504a02100d400401501804041d00c20006101130703501c4004100b2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 89806952 1250 89805702 89805719
    0x1020607080c0304031215060522030c090e070b071b15021b031903080f0106050301241416030215040c0b0a11030f030106120507140d0e01050c032a0f07050307020a 72
    0x50400360302080140243c0341d003494181c0a4ac40c2d0500001c1c1143d8102c04080c1b10140e03551300040f070f40c03034520710448100035501c1340030b21100d82162a0848080c0c2040740d080307501c0c2c0300c2d80444001510403404154000b0f010071a0195803940c9103290b0603004c03000c0001804141c2d50622274900740354070b11103041e0784c29134083c900202045402c0700c50042040d550300c0085610b620500c15241a19002c941d0703080d104d68003054202c0515a582585001c11603c1107914004103403140240c5511030074034148080e48441840d003c5e04160520030340d962804c00e20020040820320800746501180c06840c03031103644910380c44046401c07a00d00303a00701e07007603100000310182c00384400001581225050380c0c580780140c0d000c0400070b050314010b40b808400147c0515038400080d203503100818103080b10290010300d40c2c4103080450300f074890440d03142070000c00c003108002c10582c0c0c2d04040710840407d20000c07070307454103425003800c041c0c001c01880e4881480c010804004100d020400c8600a5030000c08100a065648408 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 89808202 1250 89806952 89806957
    0x10e10020a0f0c0309060c080912030d0605030613030c08040801060e070e100e0415050a030b06010206060d0b0112020a270e010603050a080906040e090c01020607080c03040312150605 80
    0x10400000c0b030304100c900c0070b1481040c0c200c01440c0d15030b807500a12840c3c004200c40303019034210141c500038420442c02a403651410100c001240034200030396100d44e003402c0304104580e03485d480140690419401c01011130070303210070b4400b50b03940740c14500d0802c6c125080c01c80c0a8000d6420101c6958a480000708101c528402e2251040010341d48103281c2c8154041030203640100a0280d4000c581001b005642602d040e0f0059000c078040941c5030186a0340e1600019080092580300390f07114010b5000b0300c901560b051080da0350207074041d1140503804000c0d560700302415805200c0d1091001c1c40c521050215a5000346d194010700407241241c14a00c21007000003070030f220001c044c1101341e19181180c07007218410f004040480f0740042c060310b00c4c01016121f6012540c051405a40d120701c1c10000840c940c004201c83c0c82c0185e20050003442480445000a0f10386a80680080d06018000341040051036030401100c0e40310f581817421040c0c8098050407240646002555902d03d008001c44c046200c5900002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 89809452 1250 89808202 89808217
    0xf1418070e0903070b010b09090a0c21020309060c0f04061b0b0a050f07020f070e0411040912090506030606041202030703050d0c020102060c0f031b07061107060b01020106050102100b03010e1002 85
    0x2045d610030399840e0303102e01640c802c0b91071050700108540000788040001d503001d0314840303815040c148610204400c540580d9612150b032450042d6000c0b00b0b02204000411005902000642a00d0702d01854070858005030300481c4960002c0080d64420541020a0803000300d040700c1c1d01421b003c500b81001c3d40c2e40c5000e46407c650728072001d0a030038005107400d40f0000c1c0b45410200c400e0007420803141002c1c011485580002e01c00e413141b00000d5404015034603079101d009069801004c500c000800c0c80e01d00202030510603480188100001d009100c044e549440c2103c0c100c60524451502d50f0426102290410030107a00107000c2c1d00a002031480a00e0b0032014610946200740d081e00c2d600d698900303080b1101d000300510300c0c08162090000442207000c0f008803100c140c1880c403c1e1824150f00381d9505080d11a040034070200c680d4049096020040d13140100b1902c1002400244005420140000e40d518444c03036440000c9502e90396201c0c56510b0a61103140000560310586014040301e895802c0654004107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 89810702 1250 89809452 89809463
    0x90d02031903090c0b1c11030a09020a050d11131b03050604090506100501030c031512030903060e0c150c1209060708030f071b1707110d0f0201030f1418070e090307 72
    0x2c4000c4003417807248608035052541f01c5e9a07604540303844881c01e005101106040740c002103554404111541e8801c80e10070100c0c8030b00307280080344901710180604840c903001d032043c540d410000601c0e880308003442d81036810555031a000406a641400060243c0210b00c0c014100d030003003505006690a560000c901030324003e0700c083c01800c0740e01204508450082130343d1120b8505115060281e04091824014518002d241c4400030584907180d071401c49040c038090002991199103918043e081c2030b00704089039801c40c413a10303041070b0042850300e86038050b0401810400e400080c42c0205903441c0300c10f9034201d982001003e5107d01d4120b442d13403500f03801902c810b0040352115070b08000c0d00004000c5064015446145106000a01700c200c00d200c1d00034110450342260b0000461401343c1b11502c0c4010103600070b40c0d41320000006030002500715420719000c0591746d402c241100300c07a041c3d40d02141d50000c41c1082d602c4000a40c800c0d4032801c01106801000c1501112014000c8944001005d001c1045c0150f = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 89811952 1250 89810702 89810737
    0x6050108060d020a0e0a0e030406020106030302060709060e01030c0201150b12130f030503190c0507060507050f04050114040801060617070306060e04020c0a0c1d090d02031903090c0b 80
    0x910030010310500400d8000e50010700100c080c4081400c1c6100c2c5e68200b4440e582c01314045008040180c1150401d411460040c1c0d504c2c10204141a8104401504840300e41022008207080c00c6004010142e00a2290706042e100d9055108141c400d41c080300d9440e17508036076541c0c15a102c503000000faa100101010441c9000d0b000700700c4041224103031080c4568000c7c102000d2042d41d54064a21350002810b0050280c990101d8540310a0b150160303049000841e0750306a911070452510004541e0087c0c040c1c403c10400b803242c000720b85108421036041d544242000c01c03102490b03880d800524801c0d070b04071240035400c0100c00580749802241903400b0200c030101c66466a03a030321004500322640340c1300d03260000d02454011041414a58020407034144624140c078207081c0c207510703500300f1a1015402644d082c2c00342c8068142c104130840711144c111588002511034954490fa0080d560700a1621609100e041851300c2e1003164080d03408040069409941c0d48c404503594520003000e030300150381c0b090504c2d20340c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 89813202 1250 89811952 89811961
    0x91505032802010815040908030117010e1b0d1a090d0e0d021e030109050309130504080306091f0b04050a060e210102091206040c0b030708010603111c06050108 70
    0x8403295880312100650101c00d540e0198004607845007010786000310042d29403521402603240d502958480074010f00400d43c0ea545003080c071103d8480161400d01e441c3c0d141c14a1820641c40c00f0802e0312052000c0d0300f104860580910000f900f15160704401041140301070455040801d6008005200b0b40c80041500c11840c80440182c42444000162940c082d240b0241c5034010328108420010321a0600c27028074000001074086421a40002d07070696080e0300210f8021124a4541c0111080c9081514140224101a560f16a0358000a045140300b81102000039440410403404164502e0f0118040f00e007260307581000c104286d2041c05114058420080302091150081900c8001a40081d1a88500c51005200003c1070204420610f0a95408001d00806903950b80c41e140504800c3e0000703070505040c03914010202c17505030fa2040b2880007060042200141d00010b006044030081d09010510b01c45044200261341710307103400b513900c1c10401c0c190a51800440e41c804c40c2642e1003030f00c581905848 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 89814452 1250 89813202 89813233
    0x9010c0206060d1208070504031209030c0801090c0515161a250c060608010212090f010902091519060503100902031b090402040e16020c0609130c0909150503 69
    0x2150000541240e64210001030285e00c9841d1403940441c0c5458403500741500c1e55200d07103960040c0e1900400089e00c3d911705100344007002e41c0070002131140c0002004800101e03503c000302c0e28114891507101c0e00745110000807a465600840d0b400001c03109107222080036615040e24060115119221000030180c00108041e0098094409a4407202c40903164400500300480701c0c406000e40440d5000d86985000078103c800740090110307201100e8032154686000b000300c515210340c1182c90912681400200b0b805a25101e040580140141040402e1301091402240402c03040d50b0071800640c203143d00000e03a099102000d54083d900004041c040c06076210150401c0e80001d076541c1c41c1140040681490503e0759000402001c40080c00160501d580d078145007408820031240364070650f4403465401509503040c40170485040c0304803802810b00e058240801e603030b626140c1031007100c1d55440c102d0b821007900030f0741e8000007004016001d01510045a9590a000c00d40b8840c207800392103249400040d506 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 89815702 1250 89814452 89814469
    0x20609010b090606030a0f02030a0c11010c0906080a0209060307112505130b0405040c05010206090303070504090207030c151505460602010902010e1207090209130509010c020606 78
    0x7100145601c010741c84031410016150300140c034035120580d070354904050407c000d0000c1c5100e1490044002610180c0802c0585070110100741c040e80c5034035108000741040d800004c03007001d4411516020b40c03290359102c00e0740020702c03481e00d10aa100354044208489181c1c02003080c01801c44e65400c0c0c44604801800c10b84007810326084600500080341420302c2681007482081150402c140340119200a4400114080340c8007500c081e1040b403c141e4050190756010058240c000c189500214610310309444000c005000318025018500e80000350034080c5031148095011341d41e007003160b110004c84000300601c0100394450850480c00000c4800061501d002401d00f14040c502000f001200c62881070010260164540b2400419243e81a00d101900001c0007410144c40a0703000042d03124054000980310190b0114103600c1480f080c18000c001150102c1d14404640740100c1c0540c80d49810704c00110381d080214202d01c0307018501030030001060015000011030a000790266100303030315900c0a0013280f8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 89816952 1250 89815702 89815721
    0x1b02010828050103260a080604090303060503030d0515030a02010212090d0b10061b02030a0314090d051e03090a030308090307020604061e02012d020f0c0a0302060901 73
    0x800d80340029101c0c80c044080300c0c008a0070159400d000c400c200700e444045510070b8005403119003860f6244045020040c91001c2190b81d52001c40c1d0070701c448000c004000040040c501c44c080d90b10740b80301104044c020340006000d0304004065981380d02d000713132500700100802c0341c81c0940c540c1c5140501ca114200440d0150741030790181c0c06007105e00f021079004c000d990300050701e160b0080c20308071030f05001c1440010054000c1c201102c425030044e150181c010620000741c003040c80703c81003001e0a10b0042e600040d08040c00340c1d26040c016030400e4103e03441019805250202d54100700c0184410303042140105800003101c0d10000020380d00410030b03500c00d540740542049203411042010342480460f003c0c1c11015030044205040340d16101c840d134041601c40d042030744150080740e00c0640c0380142110900100310a81203d03c001c11003e8510f0500010900c40e02a1400c02070f1041e0442004055150301120055034031100040d660304d1200040660b10740300e88100750014040d500c04514094018005c21216 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 89818202 1250 89816952 89816957
    0x150501081519020403080d0b0102070608060118080d0c02011107060801031b051e0414270f0717060c211512010c02070611070b03040317090304061b0201 67
    0xd519403400c40c0c16010003501918592503040c10701da40c4502c550000b000510302c203400f11600c07032180c0c0d208031080c1e400e051395841c107641261005100c0b0aa0100c4e401c0e905c040c2c2441d101e0b0610010b2001c5400c48222a00442d10038010125036000792034000202d80d1015200303985100c2500080d01c0e2940e01d510786401000300041c80c080041010594010f080fa503505420042154a1695000001c1901c5000d030301f00d0b0b5240030421000e50361850700c6e10555150010115001402c2d180c00d580000030594041443d80006107480f1421000013801c00469824441d14000c4032445500d030110b80d07130000b1290440c0c21151059000003010139410b5425034034103620b4042404900040c80b008828904401030085c00f407444480c88003140743e5100701b60300c281008a28000150310070742080090814600340c100c407040c4003c07414002115580002c2030b0b4121039284110f5516600c3c0c610b400c45095103d00100e40c3e09030079035814490001c00100090007103d803e500c075240c204060300110303c01c03540d182501902 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 89819452 1250 89818202 89818213
    0x50405010f0926030c03030f01030b012106020c0f1009060506030d020a021e06030a0504030806060a0e0f060f0c030a120b01050a0e040b06070f2d08210c0715050108 72
    0x400c3d8501e4820807507001030f00d0039a41849841d80740a4a5900b0880700c000488114100401c1409000725809002d4840070800d09031030313a00b091500da07418203e150000d0500d9400a10a546040180003850022155000707a8a03071071640c09404001d0080c04505032001850718000c900c2d0b6103000104042070b41001c1d00900789008061b000c1180e00b07280d211580c1030480d078500c030028980e03031000c2c01140719000c1581e00051509260900501032280140201e0256100b086000101a0031101c418a0380e13404440c110546009071002c944e01e8002e02c519181c0112001c6a03444480c600400500149401940c511407070700703d00c0101d0390035202c1c6185c1560201d0410400241e100d8424280034107090400760000c100c508000000c40e80303650007480b00f607485241112001040022486984a401041c180c0301e080069424003070171601100e20200030640340c000200503406c1c400100084420524130b507004c1400b494018070182566002000c04c80d0b00312010742c86005039140310322919050380c81071002002c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 89820702 1250 89819452 89819489
    0x30f0601020706080a020a09090606110d08011d0406110a02030d0e0607051801020c1c02040f060b0301052e1106090a08031602030d020f070c12080d2307050405010f09 73
    0xc00951003487c030780c01000030003000407a0340300d001e00405000349030580c1c4903154448594451400d0402015003401045291401001403004080e16000300420103c490071083e242c0e403401d20014514110051150240410000c0e50981c020000d40000301088206001c8411040b04a0381c03104400c03526000813031414001814020b0190215554040b4180102c0c1e459611980c005603064148c3c8052440c400007100c100c208604090090140349618104107108040c1005a40001400b0501400380034484410300095941354001040740c85403000803078078142a500c0790005051860345c81e00d40100d44552000706403651000100054156000000182540c0f0341c40d8228141c0b00840c006902148000e00161003071862a20040511001c016140765030f40301c162410184070540c950208503003080f600c4030500401e58200844802c410301110000b082d42061002e003100c85400760405410744403480402a8090300070b0014415034500b6290580c8100c0b6170142115011407a000380b800100380041c0c1c15 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 89821952 1250 89820702 89820721
    0xf09060806090609060c0a17010e01080d020102040807032406030b0109060b0c06060f03101a09060319060b0406090507030f0f180209060a0305030d020301090606030905061503011e02030f060102070608 88
    0x800c691006490708204060312309440701ca402c842a0040001055603100402110b40104803c01d42094540001c1d0309107032030601401e4640440344006000001451542d8078102000c65281d036061859031002c206444d02c900f401d0200c00d100b4000d0b8120396161010101e400e11202050714082640c48004000a540c0c1000f400031040e8118200f64040c80745000100e030000d110b015200090036010450452408003004204141201801403802900302008501030800c000400345640da400040c0801c1c08203040021800510a5500c00c0c8656840c0000f032141181d03041e08103000e0a40340e29030502c501044581c11200b00c4481100e03040c0e0b5120b42c1240c440050600201d01503001d0070040110b0a6950f4035242d0074210fa210007580600c2d19800001448501818401c072400b504241c942007104901595440fa13035000045d2250030b22071411039609566a4003500324101c1c04084030780c07119202042584e00006900140c07100c440841070400010786952000500303104442103903698024644032242c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 89823202 1250 89821952 89821957
    0xa0203042103021603020f010c0f0f0f05070f1214030c0901031a0a0e100b03190207050c03030f131203020c0907021015080f0c0f190f09060806090609060c 68
    0x88002d1540034018156000c842142d003120041c040d4028081511003052034500b1502196003500078462111404013a451b40800d5102103031043d0704181000c0c0f001c074a0705842078010380000a201c0740d085200a800c00a0242002d80203103655220702084400003228081c45003c201c810b0348039207006001c2c3d11210341c882c0d00701c0d03a264041c2c0f110b40010704410300080f40b2941100d811200d902c0a0b035409000d05807a980b07203180000e00c50301031242d0860501944848160045c58080c410254000c40c200c014048140701d080c0d0140c9004044a42e90060442000000e41040c581140030040b041400070308240d04030086290164141e010340f4403050401c3c1000300ca40e1000e0508000c61264824103104142648140012107001e4444100f40c1c6203445001890005002c0016400e50411b06000040d5290800380c100801000ca83e000c0040750f141f81c0207140c1040c1c80e030120400c1c101e0804001003859665003c1d80548940d1000d48000d9500c19201644e20300d425102503000344c1c4900c0000d0f10340c82c0400007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 89824452 1250 89823202 89823263
    0x6060609010e0f09010b0c07060305060a030b15030f1b040603020310020717070b0109180203060601050c010e010204090204060f020619090f0204020307081f0303020a0b091e010b090a020304 83
    0x803c02c00c0f0f0041000c164040e8098000d407080103030004014580503c200700400003050140f900748540d01d42940412039007090740c8401072035181c515000c5503420b10381041204000301e029040380c00402d24698603aa50706107001085043d0415a140e41c002e6040a0007550103407a0041c00030b103180d001060100c402507200c5c00c02514030340c08100b40c0c0600008000d00602e500d50103580403080c15410034033b8090407210348503042141c400003034441c0c03001a100481e100d03074402c0382401c05a8441001213040da0141070984074400440d440040c0100308085140c1c00341040c0e410b20b954200c141c2010314002d0741d0f10481907400a0703150011110f14021000d060700502d082611840700104d103607036a5408201030760800d84248020900d04420481941c800c0071441d9105440128800041c44c503644002c0d4441c0044400603000c1030b02c8030000380350440300300005081b60a15081c0b441c0100c8007149064003c16800f81014400c500c04400f08098000c0d600030b03207002b160484501c4084078132201290040b20070055 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 89825702 1250 89824452 89824459
    0x40b0a02030c070605030405070504020c0a0212030d0903090312050304030203181503010b0304031d0a060305130b13051b060a03020705010e19050c04021602010c0507030503030a02040e0906060609010e 88
    0x1120100b00d6082c0315100090449440d003540320305042c6016400c3c00c507030b038000354000c51041c046040022800a04248429010b48031605008050a1b031541188150207000c1c0141e410310000b202010340c4400403404a86c0101c21000c21002e0010044510b44415038014006a1003401000c84c02c0d802140c41103a040070003401844100400d0b801101280c0090b4018080000040100014107800000900445140c011000c0035400201c000400207560b0b8011581010391f01c01c0000e4540e0001134144140c6500181e03042c1c09880c0548000c100f4580e031640071641c3c0d000380040100c00801640380e058024170003e20060074010103e900700c000350003281d42500c1d15920344015903040041802705181d1200700350075000c000e0255040c031900e4841e560590300e000e18810002501c46d00010f09551071080d50911f000078401c4141c0c10080d14000c01d540000d0500d002c00420b00400d803155500401c121001c49040c1074541e40d034140c0c1c46403541c3c000c480b460b0300704074100142c440c0e640c4142c125005502006 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 89826952 1250 89825702 89825707
    0x9060a0e1018020a020115150c03030b13090311010204050a030f03031d06090c090402130b06120c0a080601020f0a06050907080106030c0e0c03071407020402070602030f01170d05040b0a0203 83
    0x21014041d04180d551004a07009070f0001e50200c0465083c051345540404110407100b0040c034103400103030f2891000092108200c00c1c141240700f00340c420b82000075004401025205610351481d10034008285600044000c52000b003030a620400c01030003030b02c00301c0c3d200604800b00503203140ca6425141c25080c40440c10595240c0040c0c1120118801c00203510000c0302c010700a92500e4603005180011241c0707803910402480b001c000050b43c4072000d1001d045c1c4011408101c241619000c6407141c0510441105a000740400300102c461952000d00f00103540d80d038800000740c880700c00690301c441c850010038140c0e41081d16110007003542d540119412441500807207904d255a540a582120001e800c2200d540c0b810318001c1012040140c200b64000c00002c0d012840d50410b004060003d45400100d0001c00001194150641d0b59980c15a0021034202c0c0044d0755031302c1c00310b441142244090041c0c180c0050b1403443d0320083e0b0400101400202002d40742c0d540f034903040403480d01d115005481c6480461004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 89828202 1250 89826952 89826959
    0x30b0a0e01020a0f09060c0506010b130f080109020906041a0910080d020307021201050c032202040507050903010507020d050f070f05030f030f0106030504030e040b0f04020415030b09060a0e10 84
    0xd10040121003e2551007000d641c48076540201041c540b86c0c441e808101960354001d02045001c141c182c1111511000555548a4000c00d001021440d03400f20000c85030304140020f075400d06402c0f10000300d1003169a400c09640c0c4c41c0030401102d0300e034202c4140c030714002c030b03c0170321941090403107030fa0440307441e01880c0707400380d03440c00c2c02417800d100851910016040400d03e8011410320000011425210304003d00880ca0712049050f100e0000800b41200c4520b40c514413120501039102405c444d03a0068020b00051038046c40103030156110300140e034041d41c40d20000400ba1407000c20020808403143d03443c549808040a140380454014030815502050f55603030303075000180100014110701c0f80002240e5140e1810b0750242d2070840050340010b050600702810840060b82c0b210164191210840b00024850302400c0440c0062008888894025100280205858030045990b00e031560966030103114501200003403142110341501e002d9003000c1502000d024001040801c5d961011144625480890f503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 89829452 1250 89828202 89828231
    0xc02150406030b12030910050304060f020d0b2d04110405030a050c03100614270414010605030705060301090c110a03090608070804021503060a030f050f010b0d0b01030b0a 75
    0x80c1d1041c40420703a212543c402c242081410511301c14030b01340c080c600709003079000828410040103000c441001000800502004803943c000004041c445d0703c210741703030400c0b500680c004010842a561198062103190035642183d0b900340091040d022651450858025061001a01c0c4420304203005050911000c10151030810544120f03170302850007080701e0032014051600301803400030f0956207642010340c1445002002c203410710451a080c3c90300c04c03080e0303001a0a600e16804400c0c00301002c400d84024013050140c100c21030020044220000c00001c1c0c2c0d514200742e902d03401480703840d4002501b40010056a09294807107c1e0855180c10094292250348820780d08100101c501140400c50500c014400309520242c03065220380d40d0b061030f200605094001908107000380c0c4011522000c000009085511403146040085602560101c00204589001034581c0284007890101358030b40351800d0301a01d440ca18266616801101500f4203900b15111108250001408501f44540b200e515000004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 89830702 1250 89829452 89829457
    0x409020c06010f050a0f050d111c030f050405030703080a0203190908060106090e0a1d030403051b0105090d03110c0604030615060203092d0a0e090c0d120c0215 70
    0x10030100c007a104a41c1088030b10640090982c2055000b04030400045c8901e80c03108813540103541d011a5603040201d01458688410741c5000b5440f50400c44107e200b20801442482070b06199100342c4a03803400c1189081d003103a03070707024910885905511404040002c80c2000d4001c0c02c0320101d40c819240350501a0404094120508101078006003ca00e001c104042c814400c0c1400344c601d0f03240401c0c3c0070b4604160a0242800500380340c3d2410380e10502c10070a5645440304040186111064039242d07540e038100f80b0f440d0045a070802e00c2004184e12801d066610038012103807402c20051a4580b90920740d1000c54a60460342005601c40c4107028003882650b517080d02820040d4031032070010070f08085c40c00e5840c0a00155500000943d40144440c402503a144680310340c0018841001401001c0c0696075840028900e07030416411003043da00c00704030500f6000d902032113070100c02e00310b40340003561038244400c2030507428014080d4600c000301c18071803e1255440c3c2c0325090004040710440ba600c100d40c645103a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 89831952 1250 89830702 89830717
    0x172a040b0c0a050106060e0906011209060c03020903060a0b0d03110705060415021c050f070f120306080d020a0c0e092a040b0a050907030b010c0816110619030e0102040902 75
    0x19400355803200104802409a0340146c4901d14140400074505804500894400740c07685041c0a0700da114883e10740569400380050581040007070280e80301e055805002980040c0c9124024090200017451000e02e9003d0104120f001419941c1da1250913182107a14a60500ea41c00c05070058800c00541513603144041c0000c0c0003e090302c096207a0b602a4041c2c0b0f8407080c0b0303156410710081c22074008455a00801602c101c500669610ba44d2000345d441c02d54810100050010303d00c0740c500b900310441c1685540b000e0140c0e004401183c030080c3d00400f00761390340d50400e54001c00b03030400c4000c1400095503031424250014040702c100c0b00040110500003105214080d1211000340810788001818906030007001c0082c84107442854000341000c010510041300240303400140354944109803442d03481054200b05480d04071440a41300c0c0c5404d105080b000d0308400e001d58041500e407091400610340303142112200306d06000e050b1016441100705401821a0ba00c0540c141c0d5400c0c400000d1002443c001001c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 89833202 1250 89831952 89831977
    0x601110607090501110d0c02060f070605040c0306060821160f0302011a060f04030602180d06090b07030c020c0f0a17011d0a03020714040213030302030307172a040b 72
    0x1050400b400100a00340041c2d8600095121b07065003104907401c420266801c40e01034035060b54030041681604224450060300a0400381b4060400050119515090040d00e20520041c00180c0e580c55440380d40e800380d400051141d00003c01811190f140e600000c1980d0305d4002e540c00199011510398164507108182b0940c0980d4540038466100781d91404039a42c80c1c54211080f500340520030300c00041078000c038000148035650005000d152800780085141d04144000c1501400e00440d00e040c7c1c1c0503203640706044078050006e00100e01464020300a10008109030341c0200300e0301c202c0d981084428000c2500030b64200e00341110101c0e00c41124215207980549406c0085512003120f1100ca00c481204401040c40d46c004841000000b03601045800c02c0f00c0c1201042c00c0144000000100284900c101058100c001c0c01000400c142d00030016521a640139124448043c40345101c1c140f00650880c0c144d140008202c6a003040200d56040c00c56814210b90542c41c11f040d203418a0854540c0486400000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 89834452 1250 89833202 89833217
    0x91f05221d0a0b0405070903080705030408030c0d020d03050103030804020f01120e0f0c0a080601030305030c09040231180903140a0305220309090b01180308030106030e06040f06050601110607 84
    0xc0c080b54000c052415105603402c205d280f620b840d000b403a480c2e0312300000300450740c001500c1c42482410000d03100504030102c1030781d81d600c0390f00d000d8550b00c0b01110001030140c018003104103111030003841410f048179055202e003401a0758541c20002e4004000d00d03941d06000c03a540c1c03018030b501d04a1152a42d450300d4800100320001004005510f8840030800c0b403807244050301c1c1301780184c003000304401d41113a030305040c155125102c0210a000c03601030f4621480d001440800d0445101404040244a0f20800d6450644240302d88001c0048100c0703900620355106e03104c00f44034141d41c0c00d83c0d014610180c046c0c6441c15650003030742400201c40e4440101c11000070f40b100c080c0704400e00b020751126901c0300e540c22072401c021200cae9800f9101581c00d108040106640c3c5e0b15182a0740d000d40a91070348200c0310001804117640341d05d0200d009401c2806080000381c5082062032407080005507043c007880d0810b0348000801405da460f0000b902d401800d150400c100c540708102589010031003a4025140d58981c1c18 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 89835702 1250 89834452 89834461
    0x40e100501090b030c04090809040506010c080309010f0516020d08190204080313120309030b270f01050601050405010e040902010903050307030201060617160f020102040812091f05221d 81
    0x180b505c84e440301c02510030751400d1148000a50310b8421240c0142d425540401c0079034a0f0030058030300c144075100240c1603080000401036200c50650041e98011510141001661541c110b0b1b0844e00101d4a0300c0c02c0581d000e50014544a8004c1001c0c0358450648aa84808151110740820581c1c100da07004113480c0c0e002003040880740480340002030141072020105202c000143c1c50003441048a0722000c0c1007010040e020844021140d440c009541c54002040c00081980b0345d02c0c1e44d41e0b4207000140e030143d9407174103002c0ba88541c490000c80e000c9500503502c000b030311400041040020710441604038113100c107892000001503400d10207000600e02940000408074a44000904a1200750800814040d013a004016440682500d100040000ca10345130100010226040c2d00a1050b500115464810381b245000110603260051800240680b8040709520004401000754071440c482403002c21014001d4002c100c54410500055a07211150341043c2076a0702c0c0f03e40640c408403101e02209020800410 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 89836952 1250 89835702 89835709
    0x405030d060906080d03110409390206070906120209030a2a21030509030c0613030201091a03060925030603110306060105030604020c071707050a06170402040e100501090b 75
    0x985c254860f05044c80b1940c101d1404000d80e1007140220b0080c1e503920054600040030092941c0700c159100e0401c114a034046481e02c1c140641c030401b2100051280b100041e200a1003060201d049a51907140c8145440c0c42c454500041d402c00904207405101d40b45203000443e02d22641000c000400d04041c8040300240303041611980c10503004007010b59003600b110402c40014031055030a81d41c1514085441d81c00e850002400c0c114100206640a000400c42082051404c0c2c0040110ba2007600c0b50f280259803441403c1140b01c924061340301c00d40c010300c0080d00c94103083e00855840000b011000c4820180143d0720412000c1c140d0f55000003e030384103400e2040010344a28103440400c118010328042c50400c0000300300b488000c104c60b016070703000f007080041444204040c5c405041c00c0081c00b07402d91a0281d0081d03031b80041e44203035441002c5000300018064080d031100003070000c1001c6400a1584c0307a0302480003902003140540c6652040c6400900080c025104460191602c00c030040360303004081040 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 89838202 1250 89836952 89836963
    0x6040b1e0c27130204050a050102060402100e01020f070f060f03021201091d010230090a020f0105040e070c052112060409020a06020a020a0e06030c090405030d06090608 74
    0x1000d036401200001e02403007040007810b6a2241c10540081420710355662000b8808081824465800c110b00701c004500500c580d03005071064910594400d85000d40d50801280d03221000c0d94041c0d041011a0ba0907980366100c0d15034065948010300444000640ba1000c0c94a000020360100588644a01051082d80d40c403041d0016040e10600d825810310f600c2440740c1c0c0b8814010f00c694030006940d40e00704010450404031200350b00c8403001c021503c1d0981100d0044004803210000d0844141902e0703150000c9600e030701110f0103030420034020502c1c1c1c1420ba0a0115040c61407070740505100b01804001500c0b803080d65203d00c95105033b80d4074401c21109140503441e100d001c41c5040c142d9980d0110440c001c0114403342c2c1c20602603038603140100c0e11100081402011740c0c3c3c002a4101c080300310003040140c0c00160714112a4402c1d03030203d60290340e5079002c401344e020030350764140d0607007201c103210a041c80c2c0283c0c1d003600320b40260248c900d007049600d841c070300300d40850f07108000d050740b00d110800c203084041c8032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 89839452 1250 89838202 89838241
    0xb060306010f080303280903031b0c170a030f0c02011424060f04050916110c0109030f060e0d210509120d110a05030402130b03030307050d0e06040b 65
    0xc40507510ba007091107068a90000070949481041d0380d111410940b0311441c0c0804007603d0420040103181c90600b00280504170302d90800800403c2c1c41d411516007481202004030b0a034001c0c0030710254100112a20505500c40980542010b840c2c81340312005000a03c100c3c060405503400002e03225480d078481c0b00325000700814580d2541d091200c0043c03140d0b0a1001001041e0b0f0440f41182e807500c542c0007211b001d018940001e60000b00500c1005503801c4d80004101c1c00703560741d403100c41d076091103600c000703035150050641103002130440c02080002442c4200b282c0c80543c8a2000812007501405070b041c03074104482141d80004c0c6001400d0b1402940301107207480c000c08244028012480d14083c01517642400300c0319000184400699505143d1840e800f0141c1d0300303031012829580e41c199010007000ca400580b070503842040c030842150420071a900c0b40071400903010300518195566241f0540c0c82c5d03001406180c411039294003004a500303805003c0c813445035100d5a490b19890808040d182c0000c0040d40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 89840702 1250 89839452 89839469
    0x40e0105070905040902130c030e0f0a050d080402131e0e0604020d02010e0d0b010e04020112151701020702120a05010b030a052a030d0309050105071403040803060301090f0b06030601 80
    0x10300340100d09500814010507680143c0d80400d5010391840800c100714a40c0351000919403810310000c00c41c59041e0003451280030301508840600c0c00303030400d075925a87c640c032000306154818100c0c1240315024500e015809400101007505107000382c5401026203040f28030040700d1880000305108440d10b54410241e105014a005202c01e241c181c1c00701da100e448640001c1d060190a03032030140d4903921006000e00d0190301022040c030310750f921031003071810000c1500c00302e010460380000311000400e6445104d40c0681814000c030031251401c0806030041e0b0f0100c20140140d50200508400b41e2682c001802d0b181004e50020b102225050418508403800302d281c41d44030b500802c03101404140d00141e00c520b1070141c50141e407480010084284200c13813030302050542602030803071a0100d440e019802035582c14082c100900caa1750b601e000455022610001c42401c004017840420046101100515400707100600001918212515000002071100d00c049602e01011400c110042c1010720000d4010541c51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 89841952 1250 89840702 89840711
    0x3010c0c020a091a0612060913082b062601020403020916120e0a0b01060203160f0c050301050f090f070b0702010507020d0b010b0a0201050105060906040b030702010605090a0b040e01 80
    0x950005410482a01c61541d0494540a04c40c110740c45989104000d01c4c0c0c000c15a075551192104981041d1702d044130344503c2004c0f2a0002900c00e6961070304004295800011a803602d190000b440c07000c6c000903681c150b80081c0c009041c06c001000c0d449400c01a01401401ca00703840315007500c0c101c56203042c1000808590040c007040005031180103100d0b8108007070100ca0307041200001021605405219548900203080042c40102c000001c41c8843d555401800610b00c1a03894220a0380d0b20310504400301001807920ba00c44000ca1b4008070b42e500194841c00c000111643e40b54002070a68100752540045648000d050100742a41003004201e002c01c0f80000c3d2000d685003881d04401e078001c0070303006411702c80300044c1c0c10215941c90308021800c640c850000c036010750310351000700030607004401d440340590310f802c0000c210341c6800d20541e1501d45004280340d10305410050340e6052608040c001c4002e642d201e01340414240c0da4034890521444008400043c699601c0081005541d1880074000d49070345030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 89843202 1250 89841952 89841977
    0x109061a0403020607170d0612020f010306060f0f02030d0c02071d040305070303020c0309030a0b160908030403060c0908010e16060302160b090a081204030305010503060702030403111c03090503010c 87
    0x4280c107507207549800079916006c520500300581c485101d00d555141d1050300d4048003040d040c221480d8041d5003802990b100030032282c0f2000640c04c40b41d40307020b8030340460240b248001d201482444141515041c2e4811b80b810040403059440654540c07441510258201c110240044002a40303005482c4980f01028007403402c0c40d0320040c010b4880c40030043d0030150001602c5030400f20802c101c900544024040f120a1000c508143d1228241070710207045103880040c01d4a005480390340303540c06450299029501e00f81c610764480c802040050890410b11001c40c50009a001003031240b102d80b001c2c400041e000d1603180100441c0c103a001038005100f403601c14801642e0181a15285440566002d41c0801c201d13110f900040b8640440040000c048500c002200140343d400f540d40315005604c280c41c03e1020342d803141d0806d51915411120070780181e00a0101308049801003290450480020307050291003008181c5542000c1000398056010840307044d0100031606013449071140204003032030310341c100005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 89844452 1250 89843202 89843209
    0x9030115080705012d0c08042c06030c090a0e011401030807020a0b0307020a150209030a0c03050d170f04020d020a080d021b01050a03050a0b040204080609070801050f0105100c05060109061a040302 86
    0xb0784d0b6445030800030061b1080081205001c102d4000d0142c0c4103a182000c1e10b00741d00b00014a1000030130321030308416180410841c0c240051185070410009101d120903540300b8070014001c100c41c440d491123543d2202c0c000e03450b540c110050f19000c0c41c00792502031394541c03d900504c140c045042d8411039000e94100104901d040e80400c501740391303690141c16100c000f00c41c00701c800046c0c01003000a6501d0301803920480108042c044007141100d1041c0d007901d02da44401401a14104411152203051446c00310003c2d0b410038074181810742c0144001c103134407242c003100d401050342443c1580020b03e103036228201074150181c04002e1000c034480c00c3e0507207404512030800000d0044c014443c001d800e140e101c1012984016254002d1a0300080140045442d2591002865610395040d0b07000c07017143c0075010002c5441d22060060b14445c40804081d251640d00c1c000520021200f002070581c10031594500000000e0030520582d402402040c402050103805c00310b100c40c058440010302d9080300f000300030800c0182c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 89845702 1250 89844452 89844527
    0x80d210219020f0a020d0b070c12020c01020c0301020315010507140102120403020f010903020c060f120a020702010f0306060504031104020c10061406090a1e03050a0305070b06041505060903011508070501 89
    0x980c4040358200c1f6403a030100c15103c0e84c0100740c00500700301d4009403241a441e4002002950304200f6402c4540a01c0140c082c58200c4c8000d4504000c0006100d6442c0d049501500c01001482d200303c4070401025110640c06089812402c1c0e04840c14008078180024594104000218102020020011501035607406541d50f4454a640b034051040032604034913030480482500d220580c0044c4411031850102d90080080d402f5043c1203021480d030700001c0d80303114840d1054006032603c903103c0342c2c034060464580e000c807081455002584182c00b04600d142c1c404003400070002c002142c40000c00c2d050b040c09078034a00141081e24150044a0034404504941e54408900d82201c180d07485141566250042000c4000141c1e00702a007984070301310f00c0c6410542c1c000011300d01c041c02410500e142d6120002000f0540c3d21016086e0004070302200140414a4000c0040500c220020700020360002d10450134000c2c809031784d00c5a50b15400c150400c1289581001a40c030480e0301d810303001c47c540105076011100300d4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 89846952 1250 89845702 89845729
    0x60307022a030f0f010e060f0105010e0f06070b090705030c0108181203090a110109060c021003021e070c06170a150306090624080d210219020f0a02 65
    0x1410034080e0040760442400c46107078000e5025058a1801c0c6200409564920a407060710340250b281c1001c0006d002408200640a03403810321080d1080e900c1e14004503031444052000d00e44c891907490038503400355111001025410320803241c0005516003000c0c9142001e50540c04903000c0d070415002498942e900000743c580c0040345089085204a480a01d43e00d8078607280100301c90141300109000b20041c0015882c0c015500c610b40950744004c0304401107403c0c28051003180b0100300e041b985000140f800c106113031075805141c9401804c29904407080c042001ea119420f400b010790000f4204148001185246d0160102c0d00b81040c14550104501d01d02d101c0c001c1810a00d140d8500c0300569055003c3d02170342c010b60300004203202c081e80e01d0401e00d0040c20b140600340550300c0002d9000b5410103400c0310020480d50f0325805001d0180d0030140a4505a41042d800140070400c1c91410b0706285032031000d0f2807a10520300b0f5054500004510191819406150303114596001c0c0350240010b9030360405c81d0201 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 89848202 1250 89846952 89846983
    0x103020906160f080a0c0c0f05090109051f06030f0b060f090907051207030b0909060103030212091f020102071b030b0105060d020903010524060f04091508070609031106030702 77
    0xc0b06007810031103c110220440100b06000000782d0b600e00d65400302d100742d9801d0040382c1a82c466581c644220b60340560900c211900400d80000400c8508150340c8583c7e482480d0041c03280da00c54004980f01c002e94044e80200340440d42d51140c0c02c850310704911510b0302c4840700b40c031401e10b800711071364142c802800340b0110b00344202c50110000e100320348100309903104035200360303456041402c2507480980a00b001d007011034002d40c5040001382004000088a504032a09a00075221000c4015202c0580754080c07600d0640203501c00c100c0d03504001a110445007040c80756800180c4401e11450015000001481003592030038049800740f0105030341c40b04280c1120021210700780d0311309203008050040e00038845ea1340e0741546030004000c00400001d4a440800e440c09003403001e0001030408100050161514103009003100f400248142104d983c01440e034404103000080e00650748000390b615101da140c11103800180783e08410010030074002e580302c41e241c0003211124103500e416000203642c0e0000c140389480 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 89849452 1250 89848202 89848237
    0x608160905060d11011202120f0901091505060d1506060f090315051e0f0108060105030114061509030a062004060f0e04020f040f0312020f0a0f02060f0a0201090309050103020906 78
    0x40391b8043c105440f28141180c9040d52240e035420118850034134101d03542d13054140700b0000580a003506106602605a00c8803103d0903160b01d030300c1210024500200020782180320090303020b021032800704101001129a1001140d41800d11000038480110b061b5030105002401c8018000181d281100700c40780c1d070f4812070000d031590314920940c40d01005000e01c0c0e41c45800210078012841c00c40a0b51905071400302c41290800d90b6240d061508a50400001c0d844031101703500031641c00e00d420210302c500385528070b240c0350824030b140c000030f0b0800c01f03036800c01c50348140c1d11504d101704600442000505100b0300100c45060619105015102900146030101000310001340e00c3e00641e100c1d8140c034018100d00000030348031a21100007058001c528001075680500c150600e90060b840010130340c0c20404c0890103012007000580d01c405500d00400e904a9020038240003500d0020070b00c0c00640388038040b940c0003042000c3c41c1d00740a0400084e03900003604240c01009005016224007040385c13040505020710741c8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 89850702 1250 89849452 89849483
    0x4080d0e031306020109140313120f12110111040308030f06130e070501020601050d080915270f121b06040b070309030b0f010305070e0403120608160905060d 69
    0xe056120321506101c00000c401000b0503c00d0303055104070810740c0b0900046210101c66010180d50f40540a6544010044440b05119400000301e60b00f2119126509501c40700b546a80d82c884113a8445030a0000a8810f170040070445409000e41d80d042c4d41d125500ba8605429504c0350a03083c032008100d094505160004100f41d03450301280e42c200800c5007841000a00509511703103444910502ca071a00500c0b40720004030b03040c0361444070b90241c1030b40014080e1400380c00d0814402a1045280502d400080600c00041d02110060401021200b602412500f00c542c0e41d04000340615034001740c0d1f00420082041011000c00001c00c949000d0342000c643d6141c052501c0000c0051140390410700810714041040c00030140c0044504062368802d03001900b82359110302481030386c88030900c030107001035102e03400c10014034181054031900980a4905070f114003206040c00700940365250b000880c1340e4420940d2032401c00280e00390202134040400180021705040380014030f00d04002c0c5016200910006250303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 89851952 1250 89850702 89850731
    0x106050910110a12030e0f03070605040503040f08010204060f020609061b070804090501060207060c0c14040609050f010305010b0406050114031806070c060c0804050d0e060c0106080a050c0904080d 86
    0x180042e2088811075a42c41c100b49004852900029400b5000c242480c0300c06401180100b001d020380e020001c001c5017044e0f41c40d105d0101408018200342d4441c001004003141c0c0803c40e003a0300c0b0280041500150b502c070f1800e407004200c2d80380581481e045400501c188000040003040c525003100d80312903400c84180c0b522a010700f851240500080c00500c00203400181081c464220354103d0b440d075003d0301d008903921a000d8401d00e040c04c4000303004181c15074061200c80300b030421000707841030054000107074140c0fa40010701c2141d006840032202d800101c001081045000d00400e41311a20503a01480402d1515001a21210005c8240c0007054400300000e10140c0b5145040100801080b00b00e4035075040800020b00382403a0349000b950f015040c09080015503000e0300031140166400030060040c503101d103004854007801c4a03e01584000100509102100b003401007034040e01889000d444004100e2402602c0c107070003048468000d0000b001040045601a402e4820007242444041981c440c5041c05 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 89853202 1250 89851952 89851967
    0x5040206090d0b01080601080a0c0b0c0a02040e030d0c03060803090405151f0221030a02030405010b09011d06030c010c020603090106120f021306080c120c0306010b12070302030106050910 82
    0x5681c1c00035100e44102051103403a04503d03040712540800d44400e40d03240d60326240c5500030180c1c0030307004100480c02002981d1240b03008129071031a0070240c803002076a5a000030300341c0d60784061290f41341d07001103902481000305114039a5003400c14101000b29070703e00141300b40c03240509000075100759611350005141d00074681681c40f02c0f90340140b4174107000c41c240440350b6820708460100d070014416944011598090072100e55455200c1d003003014110368800480002941c0004e00c112041e540343c51000320300b0341f6890600d5000c0c14000e10090405c2c0080b400030604108010400b034440e43c090281440d80b660032a1007002035580688940e681e0355183c0b105640940043d6100d10f107860345200c0a18144942c0b2844000d05a20880d00c0c0748105802008a8090b111907016200f51074000c0c00054070310340780c0442c120301c40b0102c01044d110080d0000300002e007854001d0b880b0800c004400100b05a04030020a01c0030b42c4a441c1d0b003021400c40d418148014801e008540e815401104405568100720303004014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 89854452 1250 89853202 89853217
    0x17070f05040c02190501020408060a050f131b06050904110f03040206160f081804020304170c0709050a050405070501051603051606050a0c0806030a05191112011505010302030c030a05040206 83
    0x749181310b00081c50314a000b544540720f070030014000c00000ca40c1501490007401d000e190700500038502c03a01c40341d0060f074030032030009811158102400224500c0a800007030400040c5441e403a819161100001480700b81d03481c007882c11180103410040482d8401d84c12055a8005805640003521022084224601089100c2c7c01505980a01c80070804001560004006607240e068485040b10508030600091340021b4030f0080005d4030606140440443e89005080d81c130380240700f2924030565502c40502240d03015507140d80420303100d10412003130010810490000300401e107440d918101c818905421001d240781c0c4020f0401c40d0005900316811103102c18041150340106080015040485003040240314103400440450003000016007949008504084a9071b0043c01800d0f000d40d412103a95410080d104c42158a440005802d501c2a101c0c0750340d40400001000001032146614040c003010748900380c1c80b040c105401003042000c000308039400d4079000302e582c001c00304284d01c403480040c17810700440c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 89855702 1250 89854452 89854483
    0x30a171e03010612050103020906120102160501050f090a0b0c0f0d050108150f070207090b0307030b040308010e2505130504020d06030605090a0f0201050c01140a050117070f05040c02 80
    0x4941991861000001c6048500c151124000603800c2d01048054580034400a0b60060700c1c10002a030a04107000c5180410402700c00040c5000c1d083d80d081011800c523101d0a0316160355890401000c0891010003131b0300b2060070f07401400d010a4603034590030a8000146000c1848002003020b0402c22614820341e1555040d829040c07042c0e6031203183c000e94032800c410780c030400e200710000410f03600741c50380d85180d0003982d45602030140281807964110141c02c44802d19605403044e49800404140c1503074901e401144695103d00181d454441d4500700848080d0862080202c200104902000ca101c44c01e00d94440e40d044c0b1945441706452040c4c0034201030385c40700b03820600000700940d10114590090f002d403407003400c080100d80c070b035468801e682d045040700040104400c40700c0310300998090300181c040c04203d1070001c030f40c3c0303100e15071404003080007a50980d00c000c4d05c440041c400c8401c9082118045d5404c0401419003a2a0008c0241310002c40e106940c0181d544404808040d44203100c00070840c0c0c120b2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 89856952 1250 89855702 89855737
    0x624010f090f0b03090d0c0203060105010318020d081b0303160818070e06030f07030b0105041e020403061b0e010918140c09040e03040e04080a03020c0a0506100f05030a17 75
    0x5968031005503008031170700c8985028a41c0c110301064044c10301e41c01e20b542c029004100680c00d201c015402811144124000300910309410350040c3d482362038000303125201d601901d03200d82a40c2840c085000c990030188180d5002481009070225a05481020084d5203103002140c64640040224403500d6000c111300f01800380d042d02252000c6412903040c040c040950071180b60048d01d4010076214403050000600c4030f503074040100035600e0f064000e01c0781c2011030303401510603996124403c0c04070b034019401210601e84414012081413002d1096501034492810301850000c03c00740000c0c1b85000501030149486100d55070500c00c010194000144050810a01c0c162820041c0c443d410315081707100300c0c621070350820b15074180e40c0b18040142c8048603101c95040d54135840b2031341c03055495002142510201942403002d0068650104803440c0703001d009030007a11650030311407032421420406401030f4a004589560400141e14006541c040990304150441d0007216015150031051094503011000d03450074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 89858202 1250 89856952 89856959
    0x11409040816140706020a0302070e181005071806080f0c0409060b04030501050703020f0409020702031005011202180c0d020d063210050904020901230405030624010f090f 75
    0xe80014100b4840c2d910125041139903100c00c1283d45603c42d050050050708100c0c0100700100203035185a41080c2c0c070340c1502d20f800e00a840a1071030b26041c1480c0d084920349540c103001284c2e0300211400c440740110b40042c0c080d54101400980b01d0040a0902141d5007011070000d0394420150054401401d103002061000030340c2d54054034041d41090100742c81075445c240200b1026406032085400403649007030b20a003460700e0710040e540250840c1d001603815014454035102d2903a9240b291601809440c0e81d070911100490060044465007646801c940350421070a0102054520f0152030b04103890b803c016a40c1c078030340340c2c114014000310b0f40312003080d460107521800e00040f2403c2c43d140c1030710f090b01d89070f0f04082c2210401829802c80c1c4540e4001c284104a100080c0c1410f8000740b000f00b4060400c038508040e01c01c1d0080d020f507a84d40700d04c0c004250210b42886146424480326812007c9080301d1100c0803410452111030806280e10941401654040d0359040f50061000d40e00804900208240e035958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 89859452 1250 89858202 89858213
    0x509090a03030b1002120a1206060305011e0f140402070503070605070810050906090702010b0909010218060f190207030503030405070302010f05120705161e0b0f011409040816 77
    0x50028124080b034109004000e580c28195500001111290300801402c18504440001ca60050344104100201304000500000141c0202d0b4024405540c0000d8950b25080a9291722507003030ba50300f401761602c40810802c540d82c000d07202e010b075240070b01003006121071240007900910078000010f01c10300000c50303e8818064a0361219110f5203c507121034070642d840301801c8070030210a01030107a02081d00d10106440b4200710651305d40c002d020740000195040c03a00000343c00f00c0000c40d40d18120781e400180c5000f03021203544810a500c0c000390b03241030030a40d4004a0344401e00501c4c1c90200740c11807218034844540d1080100000560708201a40d9482c102800d04649890040c00203a02148041030740b000300511990859a65441e940c1182c20760b0b0b00d0b2a4401c0b2041ea210f04c07120403a80d050445042c01113011008000350355841b201d80115001028507020082e803100820481c42d801c0078500400c4801c403c9040c510041c0421180b2806503034075072400e28500e025009126a100c0d11410302c5008215 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 89860702 1250 89859452 89859463
    0xf0504111f05030c0904020c0f072405070204090c0e010306020915070201050910110316060f0213090207030309080d0504020301060e060609010c080c121b0a0b070513050909 76
    0x4416034441e080708428800080040c840c400410300050000c1001800300b041090203014002d400400c0036207032141569002e4035007a4055682851034200381c8081210601300540440c0500c0071000e43c1e405080040c001038040e028230749001c1d00031070302c07210310b40100030030a80340c1405402a00009011540c40342060300c029040a01c1d210b0003142c0a00505114000740300a40300c400d80e05a660914000c4034006201c18140d00e40c511400740810954680031441c01072000e084401c400d001000082550f60078218180e5513001d0b00c0c00380b107900c100b00c0111610381c110590707015200180f4000d42d0b1030100f0b180840041c484c945014145140c0440e0000034107440760007140c01b4500840c000c1c803001c3c1d160760b00141e007441e00341d0718150b00180400c00300c000365000e82c10001140f03028502042c1002443c550460600c0e4188003d2180f8030b10008590020b0380465003100d02c68000d400052000b24515619880c1441c1c014111030240031010800e403e001100c14905009042c014100144030b04001008a0b03695 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 89861952 1250 89860702 89860733
    0x31b0f0d1416080c0103091502130b0f0c01060f0501091a09060409020a111b1203040503100e0607050a050703031e0606020105071202070213110d020301082107050606010806040f0504 80
    0x4c1c00b070b6007100841503200c1c2c020003000d1a00103264640e011f162200c980001e502190b400501e005150000045440f106405072207803c01608219558540c003030061030031100b45400c000ea50702800d01003030085980c400c0004c070030340b09216090030100d22091700b501040e0191000d40c3e680003c00240108807603050303030040c0c1a0724400da20f84101d441110041c0c0358481d03200b1804452060452656681d2914100c4c15200c1030314821400d40345002c0d01ca13000710b800c050107620420072464440c00f51301d240312030400469500c0281342c585582040c800c07810040248c400c090024040545918001e80f1604511854010150804404115083d99210064040d120032566000482c28001c0c542100206900131101c502d940145107014070005114000004d0844508400c01c0c50b10034812070f24a03851501c02507018010032001840c07640081910443c4c01a000c0c44210b9840c0c4040c00484000303040001d480d60001c90909003042280da0310808503004100e4240044c448909100902c03090203482540d10419 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 89863202 1250 89861952 89861969
    0x150108090304080607090321020a02010f050c07030c151e0f11030c07030303060602030f09090406090209040807020406091e09030e030a1103071502060103030f09170c031b0f0d1416 79
    0xa0480d023030441e080340300002c4980360242c1c120034240401984a40c0d103e400c4182241050713420b110412003a1840c11850341c008480b070591071402405503600002c0f441b034105200d8901105d1120040c020034030002003046420040c04215245580c100d8004c258510b280d00c6076500700e80d02e6000fa048070b00d070b882400e8031085d40428501395000c2a601d2020007250b4103414410081071403c51600240700301844010401d0351070301c2e910b103d01c5006945802d9414000da0103912180d8076401030b40104030485004e58001990245072014816190032030181f00d44000034000c4d00000d03032042904054400c00d4000c01302aa03d80200100c003001c200d11084c04020100098003220452516000c843c0000d01d005055800560b1080004000292082c07400c22205111498503038011603480c09903900060f54580d00c2da5803500100107800044c1401c01c02060088007050b4903e0125040c0c41c0400c0840d0710f0341d165640104036015400042c401c1c0c1d40c0d103410070482000220382092000c0d0088207181c0c0401e0103420305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 89864452 1250 89863202 89863223
    0xb04020a03060c02340b0d0e1905070602160504090f081c0b0d0201230708070809090a060510050a021228211e06030305041d1501080903040806070903 66
    0x400c2c0c80001c5c00c50303600e10960202850705041e6003e040350007980881c044030761641d110115440003032210000c5110a4041e44401d00003e00e00542452501c0c2c00410441d40038481d8020514100d500e56001c0f10717000d41e000200c062041c10302904001710054050302c1c0d41e20000351445d0305496030311034103010ba501e000200a0701240b10100114844118000385c002041200760000200176051921028140090018500002550f6180d410f0700074050a407043c1702e010980444500702207006952086040c402004107074103010001c1e10000300c0c1510319040020104010951600812000b009114030501c0305440e81c0c034518070f90754690081c0150140e4514160701882500707000d15401140b2588020220100550b2041e0000007400e004221002c070342c0c407003031080340d10400d14410f00010b14042d50741c3c1951541040e082038000800d100e1301c003801108010400c00e0890030038030f102c241504246000903403521040c180381d1950081da0881c1e5031a000340028444050380140c007a038110f1744256141071 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 89865702 1250 89864452 89864503
    0x60f2102090a031b060e09070818070b03070e03010903090b0a03060909050615030607120b0d060c020606030105011415070809030f0102030103170406020c0f061b06041703010f030b04020a03060c02 86
    0xd80e00b0b141c0c101b4054000c204070002c624100d0080c501c8990101984400f900d03410386a075003680c50441c003a07000300c0c5503800002c240a0115408000101c011006400030301c200103003a81d000300450038030b00c5401e840707150105009850511a030094002402c0075803090204000e03d040c16501c49100380c0319007440181c220242c1c0900d040206085202c0e000f5a1100048008880c0411001d0040c2c014131681c8081140c030000e001031402c0c0700d065064401c41e4010b000601e400030904d800c544040c0c1240800c00c00c1c24041c0c440d940c0d02c04c0402e042e44c011985c0410348500e041c2c906040c66014460701c443d4103000e00001070003041015030245040303d000700c4405921154052141d0302501c118081c03840140c00044483d540b074105000200c0c00312501519840c0782051140f412010114480c3c440b040c150000350900c41445454200c5000002c034080d4031030300d59458000140050f541c1440003c20b1001c140001a0944d517401e600c030401076400600a01c1900c00950009403903154081030304070070b8004d500e28030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 89866952 1250 89865702 89865707
    0x40c020a0b0c070302070909080307170105210705280e0f070f0c0501021314060a090e070215040803061201090507050607051c0504050307060f2102090a031b06 70
    0x54964001e500320110751503289440607940e00a5900350103610071500c0001c0c0c050130a108000701b40e40030b116959260b08080070001d05140f000da4201c1025204040140107036601e0091280824044881c000c809241102100b82005000d0384141d520505c04802924541c070640d0b440601c1010b45e440e07849095444000c441541d003801d9030805c00080c464030004a000e8010100b0026418444c24000c0010344a6038941c1c2c00d80c1c0c02900c0002171619002c10401505030103c2c2d00801904003200c00504110076090b000301420128410b075000c074130110010600d414000c1c40740c50030003400814440c1e07145ca0320f403c020761513510649959004040c0036004191204044c4a40c41e40c02d44d215025080151504d410071643d40c20001041d51203015100300030007a007501544800701521642c868136111441d1034205410710000740c0c048020302c0241c491618405911580c3d600074100c04001d8049001d0003102103400a001d000003041c1c01c40500c0102000b8089003104140c220020508810312054544004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 89868202 1250 89866952 89866963
    0xa030f050f0f1009020d240f02090d02010f05070807050114150307090b060c03030f061008070f050307030f020307121d030313050a020a060327030522051905040c02 72
    0xb9880507401c8100c80c0088002c41c0d801c51070a4600080c0194810700d640d850f032504524004083d02260001a1000701c108000c2d0f00400d4261031050300c0860070800c03000042106501300c0721009040088038001400120302071001d4814954200c41d6a42d2141030034900315000709100c0c081e4081540100000a1020041000c0d4201d0a1806409400b10b2032401007118003a20681001030b500c600f041c0441060000d0804c0514414031103510004813a04212040c080300d006d02062000030080d043c81040380c102c0d00910f213250004001e2512580c0c950301e84030114010001016403042141c000018480c6082d4000e003202400b0421000030008003810101c64000c560310300c00500c116420a2001800405501c000701c00600c0c0100242c4e00441001c4e0300081c400750590300640f0101c0c1e902c00e0000901508544055020315150200e0b405801480d10098240d000e100c1c540c00900901c1c00c1c205c10000101015440185170262001e070703e10f0303046031503680c06130410b0281034029450308500a0403184002203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 89869452 1250 89868202 89868223
    0xc0906030d030b0a080312061302030c0f0a03110a080f07030c0210050406060b031608010b0703080f15040e210a0f1107030804030b060906010f05090607110a030f050f 73
    0x7450342940101050b0060804200060743c00341c4001d2001030104d1041c00180103038000c10704012241e141810412044080b503205610701a4814001c10484582c000100c81805101020a50315851090021005414139200c00da4403801c0216402011b41e4004e641c440c00b96070b60b1071000d9140d9441c01800c40444081c100401c0040c0c3c0800b50300d03240c00d11f03182c1c0700c140c1180c003800d0003140c207546030f40a0340d100e07900c20340d4418205460060445500f66005541c2400740203110030f45460500c203501d0040c00e2140251000b2208070701540842d804407000d542d940074103200908188590390705c1440c4c1b207403507074008142450000048071001000040200c101c40841c0394540382c030030901c580604125401d0341a01216400c520031500040081030701e24010740021032003180f040c0460b10b089010301000034005030896040c02070300b001c269105a00581a2030710b20000381d54181e115400c904040801000701d1341074541140c18103138040240301c03c1960060b5114090421207034000c6e071241005955480c04034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 89870702 1250 89869452 89869459
    0x105060f0109050f0a0308031510050c120d09170306031e0a030c02030f01141501020c0102060105040b0a0b0c060702010c02070810051b03070c02010201051308041a0c0f010c020c0906 80
    0xb1010300503850318020340c0c0800b4030054642007440c0e84035a1144040c1d801598000000110785090f01098a00344005000b00c4200d440d01c2414481c5107004e45507205000f07e00c2400340c02001c612005c1c0b2462a900610560750000703840100400180d00c0b041c1c07198410343c1d0341030013800341c0000000039070a150b540f1814034078014020042e01030306071404c03074101c550309d8812649400350914400306a40240680000000e404030004040e0070640281903514a032801b0343c0d07041d500b21081c07102e141d0b2b8011411074112a03042d540400c5021070100041d0162082d90072002d100100031911900b1210001507603440b03041030b42c00811058841a400b030b40d8a58607842441e00341c0c1d000c46008200c0a046070051600841304248142c50080c074641e4540d000d400460700c44002039080854102503603824040d003074108001003e09900442c01d615048034900ca40d001c0c110301c01c0041501102103551080880d1007103140c4d20107498424104102c000d029125041944006201e0f03000401c6031031900071801406858001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 89871952 1250 89870702 89870717
    0xc0c050a03050303041707020a090b01020613080d0e0c040e0309040509010603020d0312060e04050a03090f120809060c0a0b010e0f011d06040b0613090f05010303020d050c0106050a030f050105060f01 87
    0x190341b09806544200e040c0c10600205000c0400142c95080a400281c0003080e808075030007004030700083c40d12500420040102100c420280003284900741242d5800803a00004100c5125060001c0d00e421034004110741c000d441d00303000407403064000c0046c20360b031002218180081c0d1904c07110142620b0050001951000300d42c0c08420000340540c41c0b2140d1290f841c1c2c000310701c0c155140e0314031b440700d40110360a440d1600507400c80800c065110303002c440504015080d0b0081681000110b40810300a2400140300c060001900100c03551080150740044c0d200804407111000c0c5032412500c0b218007841914070b44095140401e0381887c000384082e0580b0000e01e002042001007030580c03905010b000c2c003043d400c607950b081295800d03150500101055008002500b903e50301d0705c94000129404038001101e0180350100500019602003086601000c2c10318009440740e6450340d841e401441d15a2105034494000400082045004041065410b00a20081169641d04010300c078081300e00d00150741c001100c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 89873202 1250 89871952 89871961
    0x206090d030309051605130e071202041d010b01020715050307030504082703150408070b10080604030f0e18180a050604080c010509072709060c0c0c050a03050303 71
    0x32100808614020701c0c0218101001da110241441da211300403924840040a0900850400f807080421944c1d0141040008011901d066038a580d281d002d003c1c9100c000742011001d5603a26048540c143d00c01c050020310850110050600922022002c0da0140c0140000019881d09048152100d461561902c524660f25040100c00403c4c0050007120090001c0c0031451f40e50003074011010f41c114407070411445aa620604051400d1080d0340724000d4640700504001c0014000300503101c2d070b0b60b40880d40c0c22702900c0d2924040308900f8240c2000c4841e200310800c00c818542e20252841c0382c0c90003921019841e0b4548030034413000c800c000e52030000e0308200c9800301e030010324260601aa0300301c8940a480030035010350384203810641d09440648500c100410001c01d8000c0a104d000e400942c1200241a03107460501380d407224104158401c480031007407107850b040100f5660082401c0135408402000303000c2d50071002520305d0843c83c90a0f200303110f800d0340215542c1400b40390300e000d40360808020740c10b43e0384 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 89874452 1250 89873202 89873209
    0x1302130e300d090f0605040303050a0204180c260105010f032c1c090e010501020a020d0308070207050622050a0501020a080c10110304051b09040201030b01020c090c09010806030109020609 82
    0x7010a0080c2c0c101d80d200040c1c00851078004001008500c01c3c01c002c2003a041c03508008055417006006070742218410482000420002c200e03952120207030000125070131140036800c0d20a034903480d500d04c03806001d07020f101d01d070722240c030031124180e400907207500200381481d280440407240a258241149000400070011020396414485500040f00307044801030f04a440c40f00100050390450740c0d012480b900020b0041018200d00280908028802003846100c0f03900010301d003002101c8045e051045400c04a01c0c41c40c0300b48091405445d01404041e520400784201a180e0500313002c4030015568490030100319490007503144c4003140c005a000b009481c00e00d07184c01410703030721005a0141c1441201800704c03507a001c074001d518140801030300355612450305081c00d43c00c180c0c1c08010408040d00460441240e030b51841c20040d0010340a10307001801000100042c0d00d40b0316040c0d140c5911081ca4010031515140b040028841c40d075003030707071205c0290b00c40109050070b0b6060050002e6101a05212900c800c2c20b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 89875702 1250 89874452 89874457
    0x2040f030813081f0e060f0601051606050f09101a01050c01060f06030603021e011409010c050a0606060f080105090a051003241802030c01081302130e30 67
    0x1c0d0b0b044005038041e5580d0050b03031401c01e1102c09202c0b03191201c5a0607103080001c0c41054900b8070900c0181185191841d01070600684c0100660b06005000c500d0131484802e01507071040450340420200424240500c0001c4500c00440f140d0700300b48a42424140c08803024044c01010340074011503052070079801801903c440e049103182d0340c030b03a40d6034040005001086482007401040603807000100c45066005110214a0750340005215210006945130b450340d020000c0040c1084e1820b00d41c4e2900386440040714030012a4101401522400c41020700307011040e803000080390f2507611800d12243e160380040da0340d00c1e400d12646a1050b070110019404161642001d5030040701f2900942d005500c942d941e0b41e0b0000120b00182c0d00e0130038600e18501d02441845044404a0f2215080f2a51042940007035075803044084d010f13042183c2040030808540e00b0505902505a00802c54016194641d00800082c0000380e9065098071502500030300c284140c4070449101521340075078501045800f0070468182c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 89876952 1250 89875702 89875717
    0xc0201030e0102070f0b0603120c07060507020d200a0602010b280308030907060206010509061309022209060b0d020d170912010f150602210c0303040c030303050a02040f0308 76
    0x42d5020080200064041c0c600c00d00e145200d15410f5040f401e00340d09051403c01ca1018440e00c2141c01c201414101d48001415000c03034856107007495841072944085500034805100c0109600c06411210b0130301d000020000890600542e82080700c01e07642c00d0220700781e600c0d4000c0d05410071308001a032040300650780e403c0141c00551200e03030302d800382d038030b40c1c90700c5490303004079056103a07600000824000c10b17030f051001e2801003500300c40e8403d050400c4400155019251210140341079603643c000005c64036000c0203c000b00902540e42d94020381c41e0320f070080103054481d4007200c0e01440c00c0d0003602c0a01c0e00501401029401506a0380902c2007503450140c0480741d042c05900104041c0105202c6942e011151603005a00c11b001043c2084420501c100759101d44483e01400d141501060140680c0003440010300807082a07450300000900c0000c0940f84035980d2900e000c0c4c04000304000500c58441d40b542c00f128440c1d6010031583d5220103811080b8003d502941c04040104a81000400c01141c0a032520 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 89878202 1250 89876952 89876981
    0xc100e010c020a0f180c090b040512011e020a0306050405070801030b07030b090403030204080114070827030c030405030610030f030c05190c060e010216150c081c110a0c020103 77
    0x4841d12080e52960200032517101c0461201c1c1da2548020400396030103506c9071004a400e0080d0740380e04200741c0314a00e0007140102030041c10a505102c042c02d81c25084490b21541d080e43e1144402c000300c1c08500a07602a03a41c9401207401c10000141500340380c46014803030251a0b031190002d0f420b540e1141e030b420a0107400482019101c4400b00c219649065516024600c6508c0060351980341420303050a462116840351905200c100410000581081400754031244984c00011170080d942c1900700c00e03004210141c58a40b10201c1c0c4072900e06000030042033034410440c100c0380e080d42c1d111661845040f02d40001043c0d16004088003000174080c00403c01c050303118105858100c8405403822000c8143d100c0d055504251004042141c0e54200641100c80d04082c80034110091a10041306204000c034071a0755400e102042c103000045100c2c00900030300030b03401911145d0304e440803006038408600652070340340d550b4a08182006040000402c0f91414051501c0e01c1c01d02c0f2207550015801070003241c520200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 89879452 1250 89878202 89878219
    0x122a0c0f08030a02070b0903210601090f03060608010e06010b12060a1d040303110a0203090f060f0c070602122b0e0a0305340b0a1e0504050c100e010c02 67
    0x15011101640c0f00700d80c402001070f00e41015090500b00070201500c8400b06400070024000801178406140010318058040c0d000307541c5543d40100d031424003d9000308895409007002004020300c41d0003050403144000005d0000b06000c55995840d18401c0c07040c00c20fa1201003000f0078411800c1c4d007120303a1088004001268503642c0380000340c03041100803c00507031f5141d11400c0108040d09403140e140c03504126580103040c10b11100000e9624400c09120b21b00c502d61a02044500f980c407082120315201400c0011031301c8140c861b101544d10301150248001502440e003041002c80c001c082601d1040340d0b902c482c002c45259024111415428000c40078a1150711000403450f0804104411400300d0300c01e594481c1d0f2a800d205440c4d80c900c0f0501e41022000c0f440010340845102d81d04600100c95822080040d016283d06030b140d4010060390413520300c01d982142c440c03081002c403640070a110320300807c00c0e10400200b602c2048140225092041c1c08208110082c8410303520800c2a90f002c548042c040fa003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 89880702 1250 89879452 89879483
    0x90303060f09020a0306091109120a12021c0c12051b0106060914150a14160c140907050409110702060415090803070f020603061807122a0c 61
    0x24501c10840d0081800e07160000b6100c80c0c102d038144200b41c004e28040d80c5c00c005403100c09440e038145114041d030071441600311444a000d4a14240f0801d0405980038040007036045805402079120b5614590385200d80454682e84060180544081101d042d4803503511010b05401400588480d0401040650141d0344080001c4140d00309214050103030100e42c40388a0311078600403202580c440303496201d07402201603002d2600d49070980d0050310110a514100041d074151207064991450054991a1008034200703000b00b018000048043d9040d01c540c4118041c0b900000030620030910826030704280000d000b04400c0120311940d5020442e112841080d20b4a441e01c1900040c00c1500541c00c220a141090501c3c4d809568010032500300804101c400381d0b05000340b513103818180c00c1184101900491340000011056035030402c45504544141004528504000c0c1c0d004002e810102a045002850001150707541c5074088040300103070001d08400c0b400160b03140d00031111102980d030111b603450041c40d00b01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 89881952 1250 89880702 89880719
    0xb0f070f0f030305090705010302040f030f020d061a10080702070e07110102040801020c0c0a030507120c05030a06090302010c030b091906030c06020d090f06020a03080907080106030506040204230a09030306 90
    0x40100b8040d550101d124203100032a1070920301164412818144100001c10542c4400d010b84800c480d001883c9104a240c1c60000c101c20780f0620500400385850000098030755860041160752000e402c0d03451121544c130944042d135101200741c85501c0035074000d4408010019030000301640c098a40d2501d0541b056040051074203a82194200d84801d03500440e2000c06144200f141a101003412074609080c103243d40c440d507449140c240100c0d0071040164000c0e1007440f9200070340f1802040c0240440740c5490701401c05200a200d000f804500550a100383c2c4000c0510a0182c82d20510340207200b80a95100d000340c040380041d400a044003450745404001005c6060115414000c050b507401521b1a024050f81c018101034440c0c00a0f61103840326441403008950004951180035410300b048420307600e46513091482d06016610507120381d03080c0203001c000c201010603c18003442c8252418800e24582c03000c0020380da4008290302101d105400d00150944690342c108000041c02400c4c00a815500c42024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 89883202 1250 89881952 89881973
    0xf03012306182e0306030515060d0b0c1303050a020114030c0a0c020f04020c0d020f070b0d09140609010f0f06050607150b1c1b0501080a020a030e07030309030b010905010b0f070f 78
    0x244010170380d510020010f2110a01221907a8150300502c000b052400c42c0002d10b2074100444080d04041182000440c119a41c5c000c4600202104007942143c07552850001d03a40d2200617001c80c0010074504064100301d1022040c0c90080e0a008050360900d1180d6800f1150b0001807003092303900c41200095414a601c4500c000c1c15000302c170901801514081c014043d203044844003002050360301c8841e081240042060995031008441e8401040e14a590b003003441440c43d003c3d0000c1814001c2205118081c24158003d1f0901801c9031000d10100c2c0404041130100d442d188120b0f600a08102b03c0e1400086241c6c41c01040e040703414030006408002040070031480e0240540307403104003450300c000406226a200345240b10900407003813410081e05090008044480180501c0d04694001c42d072050201e000f42c010301c900700188012140f503140d9a003802442d141c4c1520003940c0c8031104000214401d01342c2c1c098a4141c50810444500d855885614125a40d014441c2500e0744002c1003806130010750341c41d15 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 89884452 1250 89883202 89883289
    0x20609010f0c0602070b270c0f06090415080c010201140403080c270405060402090d12020a1502300103320f01060503010b0102061602030f0301230618 66
    0x1851b4869280801c00c4c1290190740451411100c568000810742204c0e00203140e02c243c42d4159804188240d044000c514035000d5689104d6029080040308441c01d040c106501c0102c40d01c4c1c5048804020000c4010390885400c0031490104640050008022030b0180c40303507070b4111050b40c0d007141c90000b0701041d110204108804103406050340742480d101a142038040d254010004850451510860000107149002c008170010b140714141894511041e00902080a0b40c40d00034120480703030005003000c100254040c5103503040035074000340111022111504244802800c86a429116908545444d480e111882041c8040c1e000514040280b02c0c01180070911002c6016000b41058401200241d09541154000c640260b00d09028607219aa0004126812000c0c0e8600f8a103a2001c42d1412829441000240184454004000640044e6200c0c1048000701210790000c0ca4100c1c6200f0064a0301c124424003016401079641c0035881e02e00040108190b92180c1d0400100912148900340d1002d141003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 89885702 1250 89884452 89884463
    0xd0302040303023306010e13051009140a021305150a080109020310030f0c0e0702060709080102030c09040209040603150204080f030406021e0f070b0a0e0d020609010f0c060207 77
    0xe080040540410800f208180300090151078005004040704801c14480c8072020345060540110700c4990244000c84404280030700307415400c07a140c501060140c5003c0e82c2e400000074845000244842a2b1300c40c41c40d00c0d88074100a0320454880e08503400107900003007040c01c2c4460b003602e000200b43d0313519480c02c030303d04003010311964840c010400c0240805805034444108d01c1c1c0100100311204508111110589030302c120011032080903400c14680003134070390b0800b0076095815810311010980005020b0303c200700c4d030365400120503245c4940900382d000c2510021070301d00c1c0521050000f894207401403c1c2d00040904000340080d0307640c49403d03a0080120402980d203a0000d020f00940b0018071001050540c000029440c0610b0618002d64401024003507034010043e46041080c4d040c4140030b01005140d81404a449007038880829200f558014014030010811500c000002c0c0d00700035a10301c02c0d0305d070010511070401d01300000540c0d900d080e0b2110102048082d068610000e01c59201400646001c0c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 89886952 1250 89885702 89885707
    0x200102120702210a140405030a080417030712110f060703021c02030f1315090803070e040c020a1b08060108030d0b0a030f11060f1c050c070b0a05060607050d0302 71
    0x1020040c0c2000c4443d010740403540009100c40102e010a9401c44000c007032180f514290040a60340c0a50890149800c0543e060040141920500c01c5050103001560303100e015502e1005048845a607072841b400c00001c00608200288445140c000d8a0006010144005175403903948112041d5082030400c96018001c40e07401700340c1804007410001d0b0b191201006000441c55414013440e000900c1400403c030549515a1103003000411204044818038518000d90600140d44d462914a049401c2101c50200140381d102011041e40fa040c003403095006403940107041034201c1030b100c0d2418102d03105414500322491400000e801e00c0c04200141c000c1c02000c028517210000d50500d8000d4445203d210382c400d0a082c1020300100d482d120f45240c110b540902c46680c0786030880007041d0f080c0200740c9662001000461016040e420564500121480180003003111340c0c1e507030441c80518000d105025080090318030000d019402542e00c4075170000e10040c20141021940c1d80e2383c40c6021000c1c145440000c0c1c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 89888202 1250 89886952 89886961
    0xa1b090311010201020708090f060f0304060609050604020f1623030705010c0809030a180312080a05101d041a040807060b010f050a08070e091e01090203040c0620010212 74
    0x251109040a11000d00c0217601d402c0b015100d42c00c181c004c0c0320416205801c444c0242c250356a07520222800700d4080703c0b10700d0f06c1e40b0306410090000c025910074404d1050401d07001440516061080703d11042c00210018101a14100c403c0e032200340510701210f08950354602c51120814269105009800e031000071940c0b03110500d0b0079820b640b22100c14000b44480102841100d886c044140c2d41084c0c4d551a0021108411000c0f48139605580c0d400541000c0c082c08600b21050b41c4016591700c5440945818080c50719070321b01c081c00d8070072103206a100702c1185550980440c0c2015030401d400501070089180b60381101c07200105102e50554045039038000c0000d14208001c0c1900400c0c0c00d121090919400b81e24100c0340251551050001c4003040100740c00005510303502541c8050b88a01c4094200d0801c5c1c6810101190540702003408101e0b10700600000284e540142c1c0222440340c0c0d402038080b440caa00e841d20585403143c04031025012410340c42035000f06c980c401d02c0503014035410403540b4900c42c10b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 89889452 1250 89888202 89888213
    0x50304110d0206031503011a0a030210031407080105010f02060712020d0b03010c020f0706030506010905102304050a1e050607030c06050702030d0b0303070f08030705070204060e1506041505030a1b0903 88
    0x10700e4003000d600c0040300d00501c44503a89c2c00c5102d004a0782c060391700030204920b0000440c0105a44c0c140821000140c800384607101da03019840d40e050300d200381c0b16072024bc0354100080c0e039074250860742480051110034401c8010345460700034004200110324045031007692040045d00751000c4e400301700c005900907a01492101804c1280e0030003050542400c0100d0300b00360b0b00003800c241441c01058000c40d003c0d10074507174051094441101d48a241102082446026841420140d0151090354858041f40320b021480001040c4201114001038000300209442c101c1400300513040243c0560501044940d02404251180a440d105910310f501035603449900488020444884c02d1b030650181e1700901608000583d640d12044c441e030340154140e5240c3e40c0300e0604a5841c8200300c4001c0d0828200100011001d8910b80411b0058294418216020090301d05204142c011485284c1ea0b16406405014171704c0d00640c011a0440307a2a00045120440d0181e0342070750744c51011011000400c00b4804000380304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 89890702 1250 89889452 89889461
    0x90f040b0c03040b04020904020d0f030c0c06030213030f0311030a08010504050708070206040b09010e1e0f0a021e010306030204090b0603010507020d0e091f030b1506040303050304110d020603150301 87
    0x103400004034158101500d4041390f846000780000d00400440780032406554a4020806801e64804421a101200c80c50024a15403101c0d004841d94900301502082450007402034842c400b81d0107621414240c5541c0b01c7c140d00808001d025020300050391001c80e82001e090000717020a4803140c0b540b445952511041c80121507001b00b1100030400d8240034408015030100d15a5041904042d543c17085032241201300c0d004040c11158031515104800b440c800c1c8040744009205a031102401390340414642051b2140c071000f0611000754803804084040141c001e0004109014903018075001890700c2d00ea41c081811504003660603503440010740304104130b51400b40601580801548003805051400074800f0340034502c1c1c1d9442c540704d803108400140710080c248590050700ca003416416202c1c00c0d500d041032000c801c002d442002800c02d0303d103107400907401c00b28103c1f0220303640340e692140b0b13640d200d441e0040760350808507420b41e101001107000ca016079030f150044c41c0a03031128020400c1c0780740501d04050841c6c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 89891952 1250 89890702 89890711
    0x70206041401020301031101032003011206050a050606030403140f1305120c0105160303020706181407030b0403120f0e0705031b03070504020903101a150c0706120605090f040b 77
    0xba03004000501c006025200a819521005e003000b0a45030401d40d000d1403035022500e940240030350084000603a028003038440c80c0072039008031020011500d50000e082d040d00c0381242c000ea0040010000700303000911940c10440c107190385048060411f0049c448075a00e580c0428180f200c01c0740185c005000d10300e8012004001404030100030320b81e2052b4500060a00d0141540403188000a00c0300a070a240c000e030110350703500ea44200100300c0f910410015003c40380707000c035064440d0343d1481101c010440c3c0000b600c405a07034005d190351001390f460f9601202d0040000c0b42c1c0080d95903c4440303010326800c0d1802606400c154980107801c80d035041c134051502c1d024143c2228000000701104804240e200410b5600a49206480143c0e4807082840468601103810f004410407510307003000c0810104582202d1031101c001110450b541503205075a100142c040c4401c4040035400c50a0104046809007020a8540c2e02d40741c4046605541c5000061190804072100700c01e40c6903c03030420040109404030706078030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 89893202 1250 89891952 89891993
    0x7060905120303150112060f0905040b070c080919030f050615010c020f040b04090c081513030f0c030e03070803130b070812060a0e04061a01030501060c110d060507020604 75
    0x35454200e1140082501c80e400075418021b5241c117100f252441a0004000f4040342040325102a40c0c801220f0000c01080b03805440d4003441c180400e100794803600c2c026041d0340c0c00c1030f000c5041140e000c040201c0801d58003042c1525608800700000003d05014014203814000c0c40907110f0ba20348201401170142d50684507034100801000350800594403041068081c69040d40d0014409155a002c50000c106100025001615a0720002441d8100003020b03040001c0c07004c5070000300d844818140e98207980640d0000c021904964503104503610401005201c94001e2404500340000c480c08203040170f4854000d0580c40e000000c40c001c0c404a2a08540001c1002c10000741c81d10003540c40d1603000d40250000100344100302d0012a0b8075580380e10400d4098031100c078224a5504082c0b400d1002003550201164145802c403540500350360181c4544c0e41206c8041d100e07907580500c6552644000b0f02c00c50002c5a00c901c0e003040708008900c05115140c464030701c6400504032030905050407207000d100464031055 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 89894452 1250 89893202 89893207
    0x2d01030e030a050304110d05070305010609020a050f0c070e07050c1203011a0f0f040f090b0109050907030b062205090c1e0702030309030a030201020a090503070e06060703050408070609051203 84
    0x80d600004201c0320399107107500d007a030f0300c0b43c8807071510f5400804e1408010354482c1d500ca054000f4480c000c1244d00440b0b1254000300b16003580c0b4044403040e80030703003510840810f0045c0001800705144200a048101400043d41c84a82d12000d445034a0708042d189a000a40c0c08580b40103140e2082080c000c0381450440568110340c581120842c040c0383c0c600558010356004910303c802211000c2c05e844082d0800800a82c403907446806101c1c2007a118841c008119003022080c03420b550054441e00103549001d02480c15a951302c00042e40a8002003074400d40080b810080016550324110a42d1120080c0780300744a41c551a00301000f000c0c080107000104100b0041005281088100203000b011060020500d6113689550000a04500404450a403d405080210381c2010780c10b5004cc650021140c4030401d52940700c0092580d50380d824050303a034400c203e460100c0d5841c5080009000340c00c0c4245055403420b0380359001281020255404640030408142c020f102c9481c2c03491116400f103a061000b5030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 89895702 1250 89894452 89894471
    0xe010305030708070201110d05030a0f09030e060a0909090507090c0212071e0204150509010602030a1d1f02070303030506060c060609040501021b03041e0e0c09060403022d0103 77
    0x5032248200c82e0000c0074810000381060459000c2c01205108481c900282c490110195502908540c0304a84d580c214600d842c0c212620f00f03000d8450a02001d80507640c02d082200518140507150b40040e98080c1400010300c00003400c00790034000d00407020b1050000d0075180e0b20704881c1c05c0c1590300b800022015500543c00c0c10088004004c20b0b10240f540006060118002c3c40003050320001c40020040d4103c0d04000e400c41940b9202c50300f040c1100c206444d1808a80e1303940703200301d80300d02500d900d010004103002407824009212a98000b2441001803021035814806050400c0c400c2400300c0c65805a0000d9004006050b0544181c40e801031042e03d60170328007103240c8115030301e441c2c4c0244a540b19212150200b030030f02400350f064a11884008810750498070030295065526000b510400640f01120040d901000402d0380c40c4000300c0e14400304070311550f01c5000c0c913003050390460306c0d00a8020000788400000b581d80c0c001d82d15225014521443d20008210780907290003048100c80c00d040c14208205003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 89896952 1250 89895702 89895713
    0xd02070e3102011205270d0203040e090106051011061b0901030c02010e01020c0f06060a0312080a0e0109030302070605250c0f0512030610030b0d0f030c05070e100e0103 74
    0x6014015000d001145a001c1510040c0c500f00900d15056110342e15000c10060b000c440c07a00d0516841d00d03030000c8810305103d001c2803207039100c0902200400580007032104000c40400220580c1e0404685000818a10b440d580030859017042000c0d0300300003540c42c42503c488003900f0300409400003020307021481c82e0221440d591141c0d1088002880c1010b40e950501c44c0c10354405c1d481030172600c8130300b8029503951900040c056501d01c224104c40401d40500c1c80400c14619100d000300040340d5014000000d00c8580241c10340b0040c03402489070800c41d40301e01141c2403084082c03140300c6559100ea100142c8403030140c1405c030308490340101103820740220142c012811b02d41c4860141c248104c5480c0c000f08258040c5000f049529541000910501c2150141c078100c02980b400b0307501c2200e0a48446a03d81203d4004a0641e000e0303042c40c0d5080b40d0074001100c081000c1343c0d820f101c220b010782010b5119042946e503261824010b0f07405805842e0354801170080b81d03641d1140c110001e215240141450b941140c845 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 89898202 1250 89896952 89897011
    0x1005130b0f072a080f07090b1c020d0f03030c1e02100b010c060504080306010e030303160509060c0610030201110c0906041d0303010b03040501140c07020904060204080d02070e 77
    0x3a1443e0840c0740b40c107071034008030119468501015031550351070954400c041903441148441d4404640128400031a40980510071460303450f10080c82e10070300071089021003d41885000091f600300d18250314020101d24882c060100e814030a50b4005640707108407000a04140b020300103440007860606148202690003e031120300da40034580b00044450031000161881c00c03402000074101420001040107100198015610640080e0bc0e200d845410b02000c05460784030464100f007584c092814a4210980304001034100040050969413030105200ea44901d800400c54842d02900c2040310284110350380140c480400014000c010250b031038a100010b458050001e050398001c940d1041414800c140c0d0449086920244c0e0041e203031b486d42c40d030b10701c1482c992044805039455801d203640e9401c01010050128452180c400a407800c0104a82c02c001042c14080c1054403c9078080c04003003140b200600212480c1182d1703400504010746450003580645100800002e804201744040c5a01a071140c101b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 89899452 1250 89898202 89898217
    0x3050a0308100f09020d0f050c070b0a0b0901090516030203010b120c07020d030906030b1c1101020705031606030e0c100f05040e190f2d09021005130b0f 67
    0x908000350b81d1481c8601c201c0001a40c00302c00803c500480004030f041c0c00d503008007040889580107004480a131403010b002d4030803d0f41c615224a1301044a0404284117000c5a500101ca01e0390100701c81d144140028121242a001120541ea681040c080350303040da8100d88074100c41a0409500355894600004500c2c040d0b80030700700c400c0c21a03000103540099440100c4511507402054120984800c0c10020a500728034000c00012926022105450f85421045410a4007200442495401a603071745d102030351482c400c00034154450702d00c02040075541071000e4850785003049182e9110721700d4503c00030280c0300c000c030000c4850307040300f00c02000a131220a1104911141401c20103001150118111260b1107540c1c4002d01d10440d103014050340003009031011000340201300061040408040a100480d641c00500740e420200c005440c2c0201402b112a05110100b500c7c000110b003039007900802c000320076981041d400102c0000381464020380e40c072806006800152042820000d1803680b8003010710541e42c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 89900702 1250 89899452 89899457
    0x3080306090610051b0304180b01080c040e04030f0512011401120b03070501050304051002040f050103060504140a0b040e150f0912160c12060603120e060d0506031c0509100903050a03 80
    0x304080c60706501081128000d0202300c10303c1d200061405110401003038046501400205600b000c81c48034a0510182c034265104802d10501caa101d43d6000c0c0c0f46881211003280a000092245501c4404105517140c000c05440d24819132040100000600e101030311040c11030a1880c1074403400c1c00d9200020386000359602805d0841c1e40e41c90307604000345400d4600300803544071400040c8c003090504654900d0000c070781080c0c805001c4291544100000c2d00d68a45031f0801042e0b51100042c1c012a079900003040c50840078000080c07905a0414850034070200c6402c40110240a4003072000c0b101d00700c001c60380d102e810b480c00b0b450018801c04907070100f80300b2004641c0d00d8440700c207000f20034801d141039040020440e9110b2000f01e01c3c0145030640180205100c180e50030081c1140540e49240075900c60500d1080040040380b030320000219000c01040e0240c02e0a8141c8203c1e040140303031201c03400d003046460320b0946549454229a80400c5030140c50145c0d4501040404034003040080c0001a040204c3c95050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 89901952 1250 89900702 89900737
    0x140306090705090303070507081006031a07030b060a051206030309010203270d03020d17070e040e011b12112104020411030c040e01080a0c05010c0f0b010308030609061005 75
    0x428200c0b52402541c0001c0c2e80350000003041c20401000250b0b49040302c403500c042d1401e150504181c107003228031501c4068041c680401d10b090050001581ca00c3e400401d40c00d000560039020404110706410010f0840042040081c1c00c0a189110041c0d840c1d011100320011490303c00d014000035224050070302c02c01a1903070340360b00c01d601000303240041002054001c0e10b00074440e609414000c1d500e1719000000c50100c1c0a402c610303200801c2c90080c052003141e040e00e4991025003400305120042c4004c0f8404411950303150344103601c984001400d0701c0d00c0100c1e6500e01194243c180d0001007101d5030300d1000c01081004000b48649265031500c07a10701d40600303500b100c1300b0760f88070f001240c007a00d24540c1956800400200308070510781084054000c1d40d2a403104010260303207480450741e07280c00202c0c010309640e0707914108120562054a00d9000c1e03034824846922004003558a42200e01d8086c0c0040381c92100c08401c001f117904001400d80d5110034219454007500300e0302d0001800074490360345054a1400070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 89903202 1250 89901952 89901961
    0x9050d05030712020d060e070c0203070b0c0106030c150f050909040206090409060504080c0f0604050601050d15020a050414012c040e030304150b220b0d050d020d030b0114030609 78
    0xf0301c0c28090711120b81d40081d582d50054504100061005004036000d107200781c40440c00c00c61003080c803c000710b07502800030100e10381452041519030304500d5030043c2541d00d420380480000c030b2042046006182c0e8900048004041100143c071424100d00e1600400a0600000d22980d0316400c200380c100d60199011369840a85202040182054410251056040c9024001002402002416a0006041556280c0a00303112060321417000350b07130150090303015400521941c034085104070803440c4940c0c4941c0050748520024800e90f00702c0c0070f40d00d0204001240401810042552061070181c0c00d10300103c07401c4428011540c441c4000707000d003440010b5044262a603403266440f1240d04d54001007140d4a07450103251491603050302c00c0155810a080460641d82d9007030042426143c000d140320903000c4081e01004250040c24140c0d080d40d4130a8454a0702004540c1c00e00c1859640101c1c1e0340a00075402d50344501900388c801000303d482c10005406804d90000d0504000d580e0403100031500030078241c0301c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 89904452 1250 89903202 89903207
    0x123010309060b0928020901050f0c0a020d0503070203101b030b0f1e150c0303040308090118030215091207110d080310030b01060e060316021509010e1009050d050307 73
    0x202c48034801d0704024440140070741581d420303034480d0691207090640703440342c405542c031780c1c043e070058032116808900144402c3c0c100170606409000e07104140e404645840c41c07941c0006001d000c1c000010b50b5941c000103801d40650805112118140212220500c580e0f0001c9152035003c2084107002002c040c0c3d00c1103010640e507a9200180e0200800400e42610080046105002500c05c4194103100c2d501040012a8510180c820b50780325244003030155046666644080d0fa04440080002ca900d540c0e07140f10443c8c002100c403d8185c418029801042c50704030324030350180d8400d0302501d2402d05031300041035140d588111b00c0441d03280c2544040c91004409500c800b180d48174504070300052002001100300b1202c0828222600f044900401040c2d0059070ba6440c1510f80c005480c141c9504501304000240100d14900903000034a000e610444030b2004041490407202403040d0340c0444565101c80c1d0311a83c2c0c0304200180c600140381c1c0c100400204405645840d075a0074544106000d00401200242c001030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 89905702 1250 89904452 89904461
    0x92304090602031602010b09010b0a0813050307030305071205040210050f0c0a140d0f08010b03070c020d0b06040606020c100f02160e040201030507030209030d0e1306031a012301030906 81
    0x207900040c00e42d140e081011a000c03c164954000c80010f618162483c00c1c1403078511422070480d85520001450410029001c441540e07008101c550301c1000500c6440000340d0400081a002d4002d980009003400c0c0f412004240e400d10001c280da0301c50506040c1320150762001c000310900203003401e2580e44c4110030342100e00c03140030380c10700f005550090710240f00c180f01645110b803041034055070940f182c09640030303000d0780c48a80301c3c0c08003000203201e54018401401020001d54200c0b1050802804500e100d50000d507601c28008030407140c142c582c1080c08070034109405410302801c00782c001f41c840e002140010030800e800e5040c42804200f1922002900c07a8002d00104403444480464440410b131224a4094083c4c0309442c100c4c00a8504400614150301c64801d03074404020003006442041e10802088a1483c1c40004c4d065004c041d40000021007c0180302e8100258441c60780c00e130080480006266140c241603101c1e8840c0000002e80d19800c8240303503480d42801e1000d08000035001300c642811030080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 89906952 1250 89905702 89905721
    0xf100807090306150302032116030c0b071107060207060203030606070c0503151006050319090201090513051b0903061b0403141608010209030c04090f05031c0507092304 74
    0x14500140c049130040c0100204007681c3c003d4044603540707441c8110941d811a40d40d01c018001034414440860b20060050b00070444602a01d03000c00b801040b80c4902c20840000d41e0440003081035000043e20b29002800003900800c018005403008500c2c062000c2d40b207100040c9075034841c04000030884100312848103000c01410014040383c900044410a04820f50025a441c0030558540500052100d104200700ca206410052103520004c1d03e4204c843c000e400007410403411711022000100b07145d15016414045d203901000042000c0c18040740391200901c0121680081e41e07810400a5116100001c02940140f130f032491500c0900c0070142901c0c800e000d65000103140e2403102040141c03400001030201c0d41e24103414800c240035503031030740241e00303e10a65144581641041d0300d60b035403c0c58103501260040c0c2c0a9014641e0a001543e909411940f01003198140d0303203c5000d00c82100d0800784030345580032050341418070b2554140000d046a10070405c2402d0200000c0c0301c2280040d8a450300249a83c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 89908202 1250 89906952 89906963
    0x13080106180e19020d14030307020106030b090105010e010b0703021f050a1805061501020705122a0d020402030406020913050612030f0307050901050708070f110f1008070903 76
    0x569201c48078104403506120700c007014103060901008000038049103600c91004003119400c0d0601e4a40e007406000480402d06480d840c070082c2029401c0320f0140700451180d155940005152400c515060803400b402170014050b50303150000610110038241d85c140d041d0340c0d801c03190917100e0045207070480c9880b01c810082e0f040459565203200707080034030350401d41c040c0b10700500034444901045507070a1b1030740303080380d01400d5a48000c010400351009100101070b00101881650100c2e40c860003c55a101031450007968a42e114443d000050f0501510184903c0d100841026200000c480000c814144010000c1d01c101c0c1e0000c0802d0030014240c0c12111403d0010306942c000340091000d42c002040700b00c0e00300340a004003404a09200f01d001c011510110f8a400020303003161901202101e03141c01000106040c000100803460215507110090401640b2800d40b15a010110b80f81c009800c0302c0016015000740e50115403442c441d681d954841201110b54a42500150303141c0380c1c00c51302c824013644003400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 89909452 1250 89908202 89908211
    0x705070804080106090614100f051b0304080304030b06010804050703060f2322020901090504030e030a0602040f0906180b010e180f06030a0209010303050c0a06110705100c09030206130801 82
    0x141d00c4211b0304140c08841c1c00311200f00c03410312460240309419403007400150016190901054042d80250302500808410514030755400c080c1e040c17514134540c09600900c615501c085010810000c0703802050b0341c403441c280380041d42420641e4490f50b640c460b902008000d961544909000070316585c0c0b04080c01c190401e080400d61312200700036401c400c4160b49442c40b185011175050220650041307200c0c07901d94003504104507030b0320b003407000001070034060800c41c1001408a26015140d80c108400c4041c0d41c081d280050350740d41b4207040c804284056038040340b00b00303050440401c07404a2144441001110a8501044d072149580c01201c00351150551903900050049040b4200703408217100da4030809254500c05003030344031242016910100040001d5100e1403580c010320000c1d21075006003022000110803142d880d0099540c2c2c00940b0103802039114000d00100341e41081c41010030a5030041211184100642c082d40f070030081001c5100e00000c0c1c00b81000041c0162140700201c0140000c0c1702441c000c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 89910702 1250 89909452 89909459
    0xe010f09030507030207060e01051605030f030c18090c030f10170d03050109020c0d11010e0303040f020f01030903081b04050402070b100b18010f020f01240b030f0705070804080106 79
    0x824a8100103410782c018407070f031b24007c102540569111151140161030300c034200382400810404149402030102c0e070501043c0450841145204007030b5005080c0e0b09040c03038680503d02c001c0e424100e05200a58030803a00801404002505501102d8020194015818266680b0900c0d402d62034159441020098a00031281c0600000454403409061440c0e07024005641c0e2042ea07403003640500c0b0724280d210f402030603400c0f07000b9000306440c0c0c0e05414050b002181d020b50300300183c1e085400494064810210300c007201411449c00803a01681141c003402d08001240c80340e2001040008000c0c83e60700901c000c03000e03081640d03503603509403030080c02c0040c001d550790342082c0b4140010b000c041d195120030007004040403900641c1c2170b09540540da05280c034001c074182408011108045512222402d601418030445e000c2002800b9013000416039100300c42c91030b0302c032025602c1035031865070280700c4240c024410300801021410645400510394038005444c0c00e100e0403c01e0340e038446c0794031840c61580f8004000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 89911952 1250 89910702 89910707
    0x80a0c0c1205041802030103110420030118051e0403110c03120409150b0a03020310180504050c10090e060102071701050615031303030f06090f050906070c0b0a0e010f0903 75
    0x1081130341c40c01c0280580589200d00c1400c16800f0a0000614003220000418035506041d0b0000c0c0d02840e03c0e413103005603c03401c03254507001a402a0481e04005020b800b201041e0f000e075002e005c0e006181d1000400b10448804a1a548104040c0c0020204800300d140c1c42404901003140402080c0004c1c280c0c1c040889a0303d40d03030050780c003a204034008141042961105d25060240f0142202d00001e240c0d49010082c1750308800952004010000308554250041f41d032840740041c1707090029801200280da410503080042c600040440f40a01c900b58000c10340c0c460540c0145420300310f56030701540071882d880b00341c0141d04005007a00654514074500e00c401144800c15000540179107415291940ba5003144290300404c3d1004907900c0c0c951a000707030403200c0024400c1d800350b6030f95100340d600020b040b5122400142a00e050b0072100511070f03242c80c14005420360501c91550020060309000a81860b0341d0b03500849980300800b000b03121992034403a04280642900811172117100c41c1c1d41008440441e2401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 89913202 1250 89911952 89911957
    0x106050a0f0627051210050702030c03030c030c07140a15020316030209030c1c0b060a0b0a0c05071a09040f090b0f070507020d03050a1701060503011703040b0a090509070302030601080a0c0c1205 85
    0x150380306604107c007103521180044112040e442c0740d07101840c40d40c0e643c44903000c0c0079440546002d1384108100586d40110b05203288000261403880003030039408003541015a003060a092000f1407aa00c10003e0015031100c81511002c0e094460038050380340c10484001a0409512000958004040c1304142004154000e800813456208560b8001240c03588000d00c1040d10040c0105c59202c581000350041c4140201c0d100715455109100f1644101c2d10740f21004d031030004906103000c100d02c01052060b0645418020031074800d01c462410408410140c48001e413454001d0049443c0d04c09910100f0100c9215008868089030050410241c005062030010050341c00403100000107101c80b100490b43c602c6900b9014100d1b209540d8490650f4200b00042c00b000c00210980000ba01c410803002501050300d1000d07020b9603060b42c580040161400c130900c001341100030712101c00c0501c100104041a030700300c1ca6094100c0c0319100002840d4041072001d4175403424000b00a404180903010040081307510200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 89914452 1250 89913202 89913223
    0x114090a03050a02011e050403030305130609050304051003090f03050307120501030b0604110a20030c160501171b0306041103040f211e09050a06020106050a0f06270512 74
    0x7154110040c6c454902a440c1801e4000e50001407001c1100b040401d21942100e6000744102e41a501303000c07110303550102202c13142c1b2070850385c9070000b1604001c07510700107640d03994030101801c0030b1054010550314440f6125500100809000c008404505041d1080003181d094000d024000c221550312406c0c0611410700486045103d40d05000c0b441c5503e40020041d61120700454884130000319480313120031041d4a0030103945199100900c9010440306080110381c4486008100540d00700c0d0400c2c00040c03100f400b00c0c10440070b188000d410b0212002d40d21104401140711313080d03c0d81e181d480300c0000170702800c040d80e510300c1514400710500c0700b4000720040b00c02850f84101d0b42d03440034881c004d000603507080c41d034880c1001040600084482d280942c10f10340c50b100c4424038140c110740d234071400040c00e07121040e0080c40060b9510a400c1c00f150a0001d035240140400d42e003c54051460950010701416146001c00340b0001c08100f182804075506003d40c025110050944000d1030200c246981e94003203c41 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 89915702 1250 89914452 89914457
    0x6050106050711040902010311040e010807090e031b030412081b19020f04090b0915091f0c020a0c1205060a0212180a020306010906031109150114090a03050a0201 71
    0x400020028019021150741950014007071100940b20f0040000400c54a00c0680c1816142c07074040d030142d04804002c0001d010040d042c10055410f01e484d40c0c0c5040c5194100d603501e00d2030f04880002c3c0ca40c0000a6130308891075007500c0c1182c3d000c001410750450007681e22006941e8040c6030304408209a02000e80a42c1c0d54030710183c81d8174000d4414865442d028243d0401d05515032245034405403e081006104012000e04040762190742961f4980d410034040301c00c1b00c960342000c0103107160b00310340f0a1314940042030940140441e0003414442d001c040c2400391031b201160741d65800c080201d40240b1140005907000903a03802801d0791210180d8500803181c400300d5541c05107000082c0c2074520b81c802d07a00b405030020072410042c0d03640340c40c2d2004100031102c01c0429106113841d20300103075000c0003040d0180402e07100215100345076140006c190340076001000e11940b079000400100c11220700001281c828240307082d003050205900c01d0980c500c41c00b101c40d5081b141d01040030091000000328011606d20070b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 89916952 1250 89915702 89915711
    0x70509030f010c080106120b030303010305030c060c0703080f04051609050a06050603161412090102070c050907021f0b1306060e01050304150b01051204060b0111030a05040e090102040308040e0406 86
    0x40307018221040d448110022801d410014071050b445190010502d0411034070005900d082100000d103545c00c268070484282c0c1c0001001419990240305468000079045185130a042080e6805031600c01c002300f2282c0504061000501448010060441e00511103200d400c1910345901d20a03000e00307401c46050444a060a400241c3d5082c61000c80c2c0c46456810364850700c58070b48540c1251019000c0d8845079554405100e000200034004020341c0c05000ea0724001030f82c0e03002500c3c0a103260310023a40400c2c410451001004000c0342c0210301208183c001540c2e0000b60507204001d00000c0145c4005d0035000046079040c02c0ca103030380c80c4e8000403e035036550321354111306142000110740900c801c840080c400d040d07072071465003214800e030130a00b04176005042c02c50925407030344424403240c0400c80e0203446030ba0b15a08101805e580010040350107181502c05503240000810713010700300e03210781c2c892031505041d224001140c01230b00b941503402665008801c40c0d07803103079a00300300c0d21204002e0f075050302c11501c0c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 89918202 1250 89916952 89916973
    0x21f0903020316080309040906091202030301140d0807020405070203040909032106051c02030109080a0c02090c0301060c031b02090f010e011401091401021002030a1d0d0c02220507050903 82
    0x1488200f011503a5640040d0b00e80f260100607c4040e01803000b0407610b00d03071a03424100000303100c0440c10340d0051080d801541c0301c2d890414203500040700384452034012800e45140c01d01180d044401c90f0110307a0103440101e039a46410104030315501c95544841e10052418a100b02016400741e0940315100000b1109602c075840d00c10007030110340e198480c2c250f001c9074114011801d040150111044180014000140d184c660b8850302807a0b401003c0c540001002da504403411440c1000e1065040241d0f080054115818030a01a00f59660128040c0a00540403908601d140d00e94026100c45c07035000e405035185090140800c0003154003801454050f0442034004518107500d940d0342c8801d607a05940c1c1d241058034000300c42002c55404a0348a0440c091800520304604d12800210700030303d610b07800043d801c503a00d910400903d02150b10010503800540340802c4640e802418641e0041c2c048482040024a0340340102d90006542d408603e01d90130700f8100540795410801801c9007c0d020f4080e901c20442 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 89919452 1250 89918202 89918233
    0x903030b090f19060e0a0b120604120507050f0d030b120109020f040507050c1f0e0a0b06040506030a06050f0406050f0613020313020310060920070b04021f09030203 72
    0x70032141c810081070641c0c005801001401c4020b881040404000200b40b074842d08100a004800c07100c001541e621200098600e04211f4a44003451110402500032030915640311244090000c0e007590400101080c16024450700340403562000c1c03680b0301101d820317860704940540035107011482c588c850903182d3309848910b8418042c6501240e8010441007540302034004100c0203050180440b0100507060240c05895a01081000d080d240c103401c044440040e003c903010b090307030f059034030f016590303084030090b14002980100361540100c41250041100d94446012900c1c1011010000e484a801e01003071042081c0d025413036034000d07801404180712555078503e1103040000700b50741c495003041d2001248100601d2a602940c0c00a01582103d15042c0c04c68000a00d48101c40c006941032694481d0104040c0c0643d2051b9040c030941c140030a480e0308218041c45405015021000d01094850000202107580d07a4a2544540c814424182c001200c040c40007003820b2224002207000e4030a54072241a01503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 89920702 1250 89919452 89919469
    0x1207120314040b091c020405090c10030c05090d1a011e0906051e040e030708040e1005130c02010b060c16050418060908040302060a050a02010c05071502090f1002010903030b 76
    0x5441c05030642c54145603d051110b0521011340550070018004241c00041e075441c020140280c48007001482b0300c0b215142007040b070151180b0004103140c5001c0340c600c0f220f174011003510311281088680e18504a40307030034120f003194440c2003051a410400c000200d0b040707848010410301c5030107241c1c1c09a070b615203075026001165821300480343e02c80c110041e802d0903940075805000c1d003050058004140880b90b40601c615641003150100d81d600300204090004c0081c045501d640310022107801e080107403418012982070b0703400c110810308050704c50100b00c0c0501e000750003400c42c00c00d003d00801e55a080c0d81d121280c40380707021404d42c1400003c00200040d180303070900481941d041a2000030040700119540e105c010311610700e003183c40040c1031200101507a6400045d01c8248c2d45500d035a0740d134401015009003110b8900082d0414800d00b03005800c081646074540540c0001c11250040e179031507040c0001250030160340300e40e607408042041c1c00001a94190448070a03a8803d0311f040c80101004010070041e0b2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 89921952 1250 89920702 89920709
    0x30303070804060e070807090209040f0911060705031201030c0303030c0e0105040b090a120b090f06010f090c02011d071401080603030304120c05010606180602150c09120712031404 79
    0x448607400301d404079142d988030301d21400c001e5040340d03001075440d190282404d40760750083d080594082080032041c00d0070f0007465000f61100170100040c40320395458204581c48204001d0107444003060aa041000400480d0401c0c00702001c445c0c410760b036a1400040c00d120600080b40024103180114141a004440031030482c1416100c40d410241072407100c1d007050f001100c986505c0402502d00081c1c0b90100c080305020300d802042165851f00c0c008000e140b0b030440b603444a817140d03840380d4010060007035164aa0310a6441440c8080307404c0841c8032040b40586400450310002e00300ea50340501b011000050800d044422100004030001070302001511480000c6580580503081040010009000381422400341829424000c030000d201e40c07a03c030300b1540359030041008101ca44003540080602c1e1140b41c0c0c001e100501c001d000782000c1c00f410f03640085c2d0140c00b1000d61180812041c207540e40b010310040c911881c0c00116860180d642d0030010007501c0c03d00c030136000b194003150403a280250001c2214242d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 89923202 1250 89921952 89921957
    0x10270e160b090f090103081305100c3206070e0d0c030206030907030c0f1a0a0c0201110309151b0c0108040807170703170f01050a06080a02040f0e1503030307 69
    0x400e2401c81d018031140e004052a5034410840c0d0030380101a9640e00d03a90f400f8500520000da190b280903c0a00114002e6802081c800c0080c0141c0e520780a90007c4024243da41c8980113039035020000502e2407903910b00d100080d40c1042c0111445140d1240000c4480c0320300030760f548450b486c51900061121140701d001020700f08010300001070001d801d2210055400c00751603c11140c0c8190f80e9218032040015a030003103030503200043d00070445c1e200600501d201c01000c0803200c51030030404680c0500381c45c00403c1c0090500041d481004030000c006c2c006e88034296006000b40d190b40030740d4000d600c1030341d014650703016502d4039002444607541d0001401c261a1001a100c8031407076115922440c0c051303040800100c0c0e5035591100c1d840d00f10300b180c1d806490428403d8480e414020002e0a0b54880e0100044c0140c2082000f44010001c40d552843d9940449269041c09140340d03c500030048007070f01c01e6800c4402d049081a90000304c82c1d080028441c13060191031000e88803504800101901c3e4802034842000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 89924452 1250 89923202 89923243
    0x31e11040f0e011b0c1b0b0301080d08090d17040f0203030307091a030603070e0a0b100504030b0a05041502180a08060106080106030519020d0e0f0303010603060504060e0f10270e 78
    0x115801100c4040001d6004c0c12000361f5070b2140c140c0859403090300002d02c00e030000c2540400c11a0810582a00f005160018103e10541d491006001c0401c1d041d50110b0030f441c000104043c0140c02541213413840e005400c0e25900c0c13800340c5005e04803007402e1040704a01d1015050b440794036041602078030701541c00100680019480c0010140c01001c0c042d203000070a9640d240c5c0c3d140303182d403840e01d04802c040483e100c8a0702d40303146080010000748018038200f2054244410000050350354841c2000000c5821401a165508164078003003802d10074950980216203100d01007504140000d820741201c0c034a55a0700c05603a2205c00031000da540640d900d03d00c030105403c00740e00d0300c3d429030082d080030075800f0740024641200c0000035192280d400c611304d03410382001005000103a810300800c00580025a014889107150003105190b44500500701c81d0011300031004035802d0b02d0703003540301c100030065242c8503a07081000580580c47c2400c002244200300d483c09214880b4001c2c00f140850001c0200c5501c0c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 89925702 1250 89924452 89924477
    0x611031b070f080901022404060b030a030f0f0c06050906040204110c071a0d020a120605010302070503030c130e010305062202010e0d2d1b031e11040f0e011b 69
    0x1540e44c000d03013040f506600643c02040c00c00c0000f403550082c07641589401d29400d08040c01c050088542c0e900c05a07012350862141000400c0d0010030300c3d007441034103242520141910001c22500780e99200320003840f1a09040501c10440000103901c3c0c0164003c44042048010144160b00984144099070240d80c0184100f00708102e0703000e844990004600602c149050031074100601280e21408100340410701012165061012500c1442d01405086c00c003145018070036190140d40380001000d0504079940020321440c015048600d4100130300e00c3c1041c0c0e02895850341f818a4594104458800d0200e00f500444496000803200c4940e00d141c040c0c544403940b80d030703180074080d905d10f11443c00e82d50480b1b0f242426890651100b03280000b541c0c3d91005580902c824503050554403403410f00c1d00040c16031a00103101161484642c0c2007004607900040c2034004940c507000d1b501c8040c490b0f54640c4145805504111035440343c00881d81980d040c0c0081215032403503694400c50410602c4580c000614900c03020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 89926952 1250 89925702 89925713
    0x806010b0a0909050c040b030f0a0e030405030a2d032313150201091202010c140a080105011803021003020a031b05160302100504030f0206070e090c0d02070611031b070f 74
    0x1d98000705c034000010b107002e403200810050b03544203540b2488144040002c20542081602c114244200c15002840c40d0502d02000640d942580041c09000c041a9030121605594000e65080c0080d102a0340118480b5160070044c0c030ba00031701c4102d400c0d140c08511083c1c0d20540b42408071000000720072030591103241880200080e0300403a02d10b8030305540d694107503a8041103c00081c00511100e590001c5400801d082005028021500040100000910070340c40c115802080e4241507a500f840c015070285048200c0158110007507101a4208407400110103985a05400a00b011f802c1500c007405090385030800203143c01c014a2200d000104107100b80018100024076030710300c881c00f0b40f04941d4803904c204000d0341160002d88044011400303000c0707070509040c0c051054a40c413540d00e00f800c1c0b40713200b00d08000c140400002404034a03680800036021101c400305506440e0159009107040184039445a2101460703817041d1030728820046521000700070b0020b9481201c51a070341c48031640c070301c140142d1703510f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 89928058 1106 89926952 89926961
    0xb09090304061d1f1202070b0a050106020a0201080f07110709020703030b031b0d2a03030e0d030512042303030a1404030804140705060a05040806010b0a0909 69
    0x10b410366135450224414080304c05444501500702c100100d03042d94002041102c014801304400e814030a0820015100c0c0102000c1003040e030342c84502c1a41d485200340802400180b0b00400642103000900c4426040441d5080054104204407412414145950880c81d0000e5001c00c542050640c5801000c07944031065014140d41c1a01e1240f6450080702d80c03d04900411004800c5003c100041d0800c800558a4100d90b100d102030100800c40010060722082c1c002420202040c01946403004c0480d403520ba040d2510752810042c038108910040c0018401e03184071140400315140f00420380740c0c0c40020140c2001850b5245040d640300d40449404c400f006000411000c10400047e8004600c2c0fa0401d070850161042602c0d490b8019180ca041c40e00300580100001c035101030700b00c0c1c002010700140c61a40d400c0d0350b05aa01e840b0716950b14020102e43d9030015a0a950800200310582e00 = true := by decide +kernel

theorem cover : BRFrame.Cov 89748202 89928058 := by
  have h0 := BRFrame.cov_init 89748202
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 89748202 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 89748202 ≤ n) (h2 : n < 89928058) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
