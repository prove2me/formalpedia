-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2667
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:23:17.77798+00:00
-- url     : https://prove2.me/submissions/ca41114e-0fc7-4be0-99d4-4d310d2521eb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 479496402 ≤ n < 479676258 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 479497652 1250 479496402 479496427
    0x11107020906090f06130b030307060e061810020702030109080409020a031a01050307080612010c20010e07090c21091101050a141e1204060c0203031303050717 70
    0x405801240641da1480225101e80b50402c0141c0c071400500b10b450400340e07940410045804940805515165030b28000841292001d20042c00c903c0d0081402141c031144100840346400d0300101410201e58509101c6000c14901180b02d62151941030320140c0ca810060000900515100341c004002407000a80012500d81da0b4000c2c0103041c0c1c164a003081503650408590601c00b0310b900f804d90003e04200300003900e0034003c01c03403c0e4003d4406428088489244a029800c444203c0406c0000ca444d4042840a05085d40e44602c20044040c00900185c241500d066a48180a00400300166100c5c421b02503180d205246d000c410540030311014001c2110348030100014143c0740c4054455800d1008101c840e940910220744101456507520a0300c0025803a0022041c0c006001c0b071010f00061200392616a00c450020781551540d04203840002d0070503182880450f07491600e071b901950002d208003d68000d404403055461070701810312690707488407442c01c60420480190b45604450000c0307900c0d51b6000c5c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 479498902 1250 479497652 479497657
    0x70308060a0905041b0801090c05130e010f0b150a021e010f06090c030b0d020109090207080405063f0a05091606020304080d0203160821040302011406010c030f030507050c0111 77
    0x1700c40000000180c6a400c4035003643c0200d40041c14040d44040104810f0510081c136031581c5500290005900e4408100705003541c8101002410103903d07800c03c0100f5160609040d44450a551555442c14090500181d00c03104422006440e15808440c1400c00c800b0030340203203881c400040c00412285449400b450020b00140080600003442e21500c81e4036801c4c80d1f4002d0419076016107588132038600d0004600040d504c90841112000310502001415440e100c01405d022400c0041503c248140c403a51500121180010741200075a94080c018001400c0d803045030300000004004182980c5011032945061030a0003501149512010300140700c40c0d01101501c1501d41d010706845407010b8a840072aa603004002c0601030300c0c407115811742c0004000c00d0007000003400e0400664070308d94032180b020444410499017640941d444400340c042e20640092400e90102090808400c05445510010542080307050b01c24241580d440118003c1c0d03000d0416a82c00541040007030181c6140082c110f122074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 479500152 1250 479498902 479498933
    0x5091b0d0c2a03080604050a1d031b070b043c0806010807050f0d020111061509070302040803031906080a0c0e07052508041706071101050705070308060a090504 70
    0x500501840d0a180741524000b405056050f945182c0c068072134504000007001c0280800c0d48056a038000c0302603405015440c3c251030090b41000e15283c2101030661049032080120080094202d59400c1c4806d11380403096605854044005ea410300c0046051044540600e4501090903000612880702d40403840c0e680105070786600c0c060303494a981e51416550384400901425502c4540071030720800b82e0400321346c1c2000b903d005140c10709802c0510718a0509050040c0c1e009290307244906002840c90a000304426003000503443c04500c0c052a0072100d540341d000192100b480e4421600885000704125004000600000010340e00414000c2c54241e854000310b10072100d842d50280d0000351803a0040d401e07104c80014000510780039840301c1c1e500c0c07040c007941d10b98120f40c807004c1884081543d881c100038944400e4100320003409142040300c0041c1885495040b600c0c6146e0410007040046544041655003440c0c1c0341c04c02003a07a4a07448002032000609412180c5454034120402003407052000301c60004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 479501402 1250 479500152 479500187
    0x12907050d110106060905120102040b0310060e090708011e1701140a050423100507051209011125021509180702030f09060c071403010b010905091b0d0c 67
    0xc10b114a4052803c1e030b0914825400410160300c0e007080706080600d10020152966800149072039107441d524401a042510840d40103104901d00f84130311500300f99140e807116011034071101d00345407540b0000c0140b030050140c114020b8114400d400240a4034500c0702c01340450707001414502c05400100e900900d281200ca4695420000100c1c007480d400384606805079401c807a2007502c04170104441d40c0d0b25179103105010344071b100e10700c1f04902c800454406ca0f4001c4105035038640c1d40f6000141402c1d403212000d042950729074500305424154041d000201c940706040d6001040e14041d41000b600e103007070700792a4003941020100705c80305d24404014008095002c012509001c0c849880c1c410f204281c01d040311200003680c030030420040c5c4114014007400b09054010922890005406002820718200c0d03482409440f480140098540c5000e00560f50503503020f00c1c06803000c80c0340c4400141041c102500381580d11070210514115810000220b0751860010002406030740c8220038000d040d68007044401c0701 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 479502652 1250 479501402 479501417
    0x3070c24050a062903070c06051302010f020102190f051c20040e132a06111603060207030c2907110a11010207260c01020312012907050d 60
    0x2e0140d01300c45010018001a003940b100b90591040d502200d03030004e4048406c5c840d04450600000d0b4441c051540b01c0c0c00c0d9260b0001e01501e01d0310026050800303030f04009042d64018050301200c44003003600a002120301c0d20b0510004035a0880540302c074130444001e00a1454004986a942401c80d0090f9140a01400f81805440314034016810b003400340c1d01409442210410110350035000805801005038060729640421f0007480e061a00e5a4038280d10085018407460b600300990354012044540d80310742d0b034001d8600d032280500c01ca100a801741c04000c1c0910740c040b80c07880c28035100c0c41c00706034110f07480b1507410206c0d03120516900d0003401001800c40c810360700c000081c5541e0320690442280005490007012552515900c0c20b240202c4402454114400c90340c00145124005000401607821000309055022020303012a040005040c0ca40d8150744c401c0000032a07550760050100e0440740030812002468041c8401c0302c2d00a03800310224005600040380c00800c1c400c011824580411543d01c607103c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 479503902 1250 479502652 479502659
    0x110d06030c060816050d060f031401060e090d030f0b0a0816051903080706090b07170c030c0a1b1a0106020c0d0206030a090206090607060603121403070c24050a06 71
    0x1a9140710840f1a8003815001340342403071800340504080c00800d080142d010032216140c4941504d00c0e8440d41c1b0968081034100c02182c8217584c01e125820103400703019850a580d140172803005580c1e4401c080b00b40105661400400d0708030b181c0307500140c51070000a0052050710b54502d030196444d0031a0800821403c0c542c040020549801072244d8404080760182c900e1580c1b442d1a2080c9070740104409803440358684c000c40c40001c5c965070106101e290942c031039518050103d511748480c2c00005003010380254081040c0f00001e0740810698490301158684034003801b401c141099a03041075280c0041c2140b003250b100c504419840055541614442d41c2111205441342d42084000403515001940001c420804158581c500d900005102400600704a1030941c401000c5421548000d60680703819546400130300810802800e80c41415010f403520884d02c031040c2c1502d050500c00600020f0900203288003400420102c90700441c03910032079010840c28103110354288009850200d800403903052901c600030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 479505152 1250 479503902 479503907
    0xd053a0908060a230106030204090b15071b1205010614010206040f03030f150e01030c0b0a02072c09010b03071508220209090a02040b010801030222110d06030c06 71
    0xc00490785404020300454885425072030082c107070650b552040c00880b420400c10b03040c41281c070310700030b026035030340103990340d01c0c0c080744004490300f5074900b40c4a0b041054110410b5840002618507140d0850305082c0d998209001c11214804640e00240b0b905041880141c2406410f40c0400211103036140010400c109031801280c540d00e04032001400c6400a10b50702d00481c1c800d9004a0901001c020300040303514012640f807182c001242c2c8a6500303503001c00018410402c81100c55030040c06c115854a0821340002c00107911481a0b00070801ea03160b03190510b02c0f00e010802c01540d602d40140e00d580c1c006003002ca020700e0181c105100d266000e442220400144a82c02e00c003441c091109070343c2c546000b0303140d00e04c0d0041e92180440c000401d40841c41c1034000580d40788040140034025400041c61142101c0c0705000a07200c003820944d061103138032401003002d40c94403011002400c80314081503208500d0988000c0c01861418001c9648400108617213010262542c04442038034090901c901000d95100000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 479506402 1250 479505152 479505167
    0x60d1506171005010f0c050c0a12170a090b030c190c0606050f0604090b13110409141b280c1b0308040e13052e05040309050d053a 57
    0x90f03070f0014020707001071134500784030f0742d9030f003034080e02c548143c80e142c4001d01c000482a08007904940d41c1e6000311104407040014410100901c0c50034056030b6801e0525041c2c0142c41c0600c0c0c0d200d50a02180008009a400c60985045480e1405442d101503481c805c443d44c002c2c01c0f1503426100b22421460150701056511b02150f003c00504402010945010305048844001d04130400d000354110b0346007051514904024002c0c4040458050a07071600d4500c0d00c2c0380903054443c06e40c816a025440501880556089007081c0c0e9485017468031000c0d42c410700485021607680c04c2d114900600001d070301c2402c546690244c42e14545601501030142002040721441d40c03841103900c4014440c3d0805c000800086159016440c1e100003002104046c9010750b0300c415042c242101008200d45040442c1105e1030052042041e03403e40e03500c1404c0040e40303815680589140901d014851003204081c0b800310800c00304220304108241d504030003080394100e4110502100c1040420701d403c05681d2105034040398440e954 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 479507652 1250 479506402 479506409
    0x9090203012d200307080714090105040e13140c030f0c0607060b0303040e2502010c0e13090804090225032f011401030c050102030711060d15061710 65
    0x44030400b030500c11600207100e01143c074041e00ca12200b00204076411840a5031141305503840305c40301450540c00040003109201040507c1050a0140c4503490f40d000c0282c4041c1c1e031407c07010080e0b1b915001d080000c0711701041d00c010064842041100f071101404140407036030309815000c0301c210345c186070b5050345c0398209482d01ea03030810b40510403103001c12695002101060b4015054a25007078580004150000003222046245403000701ca001c6812100307110300241c04558402048030b200e0000e8014298001514501d108107005d05203082ea80c02c1c10350104490603031041c00c3c1540d45651390707046000ba4000980c182d044002c070307003600c0d16000c400d11030340805140d0542d81c0122400001d001e620407914181d2100809413000c0c1d581d444072044c00d00c58011800340c0c80015021640c91480c10950600550300080d04540041c0076480000380d15a40c42c2000d01030460704151a034508010002c02082e1401e510321303e02e095070000042c180c0d040060090200700d0f00c24210b003d65200043e0540c020581d10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 479508902 1250 479507652 479507711
    0xa110102010e010903081b040e0405010204030203060c030603150c041502010e0625120207061404050f071401050903010f09030c0605060405010b0d0c0c0215120a060602340909020301 80
    0x40000344010446141647c0312661041614201a1185a0900c408038112001c8030160740c001424015860104101c1da07001410346030040c82e501e0402c02003900d482d150803840c891511010042039001d071442003030b540980085c0360190b80c003226a24000b40138104d22000c8401034010b04010440510791016903000c082030300705840841c40380c0548110f03100d5041c203012240003582440110000307450fa0207149070345122a08003a0b9503007000d04241d41069030010006d075040c0d100f040100420b03903075110b01c610300700c0007420800d0b10398a08030b01003409410a508100e4100e4505610101050b0304490300380001401000c08001c2d96860b001400101c074001e01a800b003684040c8810040c03410f1640200d05644803501c0d08048100d11540841c040400e002d9698a4508010072050724142101210641c0b185880d10b05000103494103001a403110050346000d07480044d500c1910450348001199000ca01c40b5072080d9000c40780e40e40203490001c080601c4124400d5007042c030514070782c0c9115030746501c0110561 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 479510152 1250 479508902 479508917
    0x50114060f030901090c17010c020d1b050c030d020616030b0a0b090d1704050103270b04032003190f08012102090c1b070f0306110c0a110102010e010903 67
    0x1525200c07841d802c010042d4145640b50340c031250002e05c44d00c1d41c250080090400214154078000285800c1d5603840d4041411944403240f40f00f04203501040c601c160803072049111590340755504106061400300b50010340c06105002c07121008945c00141e061041c0e440b84442ca01c030814020049040c0c523a4901200c0e800b000842041c03241c4c46803180200340b0010000e03c1c0000070400d9a031400700402004c1c03850441d1440219080085580502401c0b010900414580010721508040001400c583d60301c003911200b84c40c000101014000c0c008600ea00032814010b4800b410914003c40e5240e01c030ba00860a0b00c41044013401d01e4030700600301c01014030903545170340d401c42e820180d000c40c481d408418940c420f0008140604d015031030750720a01d0b0081c00301d144110368071506645a02c00c0303a014520080500d038086041001004611300700fa00540c0e60103800480c0c016000c0d80c1509244c018120040744074011450312804011116110301710540d4280c0080c000009149020b500301e404592001d4081180e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 479511402 1250 479510152 479510167
    0x130509010b0310300f0b070908030f031503100605031603050c010c060f0908090906060a080f0405150903091f1218050706080406050603030301031104050405150705040905011406 78
    0x103181d0450161509500b0000d504100c0350302444c00d4140510589031203900c0c1c822101880000c420303060380020316081206000e0b103030100c6a43c0c3c074071900042021802001c8045041080d000d281c07041142e40003402c44101c0f110103400c80004003014841c142c444d02c6065100d15181c01d00d06546021250404050032821596000540d003040140e60100c810355510f5403071203882a218400c42016600a9248035210101c110912403c80005030030644200410300200720115445140c580d4031105250030050310b502c85262092a04c40049400f1a1002e1842c0070000345042c004041d20310031104544c0d14400c480d04842c0c142203458002180b4000403030341c56a016a42206800021a42d81c0064242d04500050f499040c14056990030100000740003c0c24030050088500030590070400c1140a1032855255170f94a08c00c1666082d04a80280c0d03e03440041e00303008050103000b4001c030002420611500e00720b40000c205601a000d15185a4076000010038035843c1c11800040440d005043c184c0340810 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 479512652 1250 479511402 479511419
    0xf2409090c03240213061107031101050f0706061d0a0b031b0a0e0a1509360507061107060201060e0c13080a0821071e0201020f130509010b0310 63
    0x715070040c0e228030454111503011280262005140c41890042c5d16810030b4240700c0c000b805460410508841644511014804540c845040300c0743d064003420302c20307aa480d0344000140f96002d02380000d80000e180190001d60039a0301d0300a400c5000300444429515900c4090450450b81c031407440c0d6416510404d000d80800c00e200c540c024031003e000300025121655202c04000402e401c580c26144940c90344a0850558400c0d544c0c0c00150500714000e004c0741416000a0703040750b0800c9a416001c0d07101e40400e500e0300107006400d441c41e81d04102a40e010303588840c0c0241c86482080188a003920880f400000c29038418403c0d4010780b070200202c03c942e515042040201e54002c10001c02c10070280b00c0000820300000c01a42003030a01c504880340e103071036005c90a0040c01045046401005030048100019190300c0101c101c071900100c140004900700403a0124028000c08030310080a00c070004000c41280c0744644004101d45013101c00c2c4402e6a2910140300c41c9010a03075421303014000180c1c0a008031300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 479513902 1250 479512652 479512673
    0x30b010302180f0409060e010e071706070e0612071715130f060f03030210050109050f070f0201060816050a0501020a080f031510080405060c180409060f2409090c03 72
    0x81c0003000840d04100301d4560404171880d440d040c09041e0349d41c1c0b0400300301c4642485074000400d442040c020043c003c500000d40c40d1000107000742c2c104089001c11164699810b0282c800d284a05100c51031280381030302001d007008900004141c4c1c007845136000240703251000440f045040002822141d41c412107800c0140181801440381c0d0000c90321100080b40c105900c41c03c000045001e0780c010000c0d10121080b910840e8410307000190b101e410101080070030300880d00d91035044117882c40c3c00c81a002c2c01e03a900301d004009a03000802e280c0900d02c0d03400c542d0f00c0002d1040085c0e07a82140c10171306075a41c4500585c0d0b10f1000355030040050340c050002c3c0c5003400c0d0440145501c45800d04079610b5a10002000603a04888180c8401c00319001805200030b1204c2000321a40c4002c41003540c500c0d00100b000d84084400c0300d1000503201c0c0da1501a9013040080300d400080032a20201c0051003604910600e4488d00d44803d08041005240b582000031a2082070241ca6445500002401529821a1684a903a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 479515152 1250 479513902 479513929
    0xf1005031b120f0a180f0302160b1e030f0c031b0406080901140103050c04020a030209210607020703020f0405060315040804060f021c051303080d060303030b01030218 73
    0x2041c504085080c05090500520602001c0b40000009181c105002c441c1c83c0805010303415441c2c42c15250554103000103968040080e04258102c000362420314040f0b260002c0041400c945000e03001c4006444120031002d04844141c80140020099209100c100140001c4824550406000c404a03100040c0480150b800c413040544501c00c02d503154110382900d038496408000041c01b1030080080c0210284182c288103944504012415455600c0c0d146c2c0d50000d0aa41500c1180e0004401d06894001e41c1254034045010300001915007100000040402c0b0804810400e4014200091902d0f4804070340c00741038035401401c1d03c0039815000b003070200415000701441c2d010711032000150103054150b28081d12841c429a83e0541e154280803000342151096117100003554043c0b490109603d0025141080f29a101c1c40e0158441c800f204801d2203200203580084c00f03a072800075000300c0444132a00000141c07406a1400d101b054005001142248600c08501c16015034840801100303107081806030301071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 479516402 1250 479515152 479515171
    0xd02160608190515091501080c0307021615080c0a1b0f0f0b040212150c070c03021c0b010f0303020d030507231c050f0a0905070320040b0f100503 64
    0x101e226502c03140481e02c0541d40c0c008030a4100d600c6010901d400402682d00020f0541010121500b200002c0c09652018200702c41c1c00c400440011003003071082000c21100f0380311500401d0f02c2d680d64001910700e00e0011840310001011140000c0198161500701d40b910b40301c2d80d03103441026281c0d80004c1070702e07501d49200711403400512070f4040c04030b401c00110703020150041080c800c4606141c810080c4000a6039820b99141d0404e03200c400301070160051080d40480450036550f03484005241c0f40c5009901e5800c020f50007507841c0b00d882e4010350001034180c2800c2c070a4080036481d0340c0b40d1800c2c1502e552244401230041e0b1140c2044003980f40b0942009400203400d0500c2c500d4505810f5540210035804110232803e15000b1a2140311007860000480d00010306072801c11503401c02c05080b04402c030000301403040a0b07480782c40d082d08100e02002400015070300401100380410f2207003d6110b84000c02e400051060382425100d804030710384621081100c000007030211078850311a0b2801c1d02c0135000280304005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 479517652 1250 479516402 479516431
    0x30703030c030c1208070e0108060f0409020d05010905060a0c0215061e030d050a020c090106080123060d051e0c0d0b0406080102163e040e0a060b030d02160608 70
    0xe10f880c061149013007068542d0101c6240011004260049544610b4108a9202c06000c0b8980f1605819140d40e081524041110015800414284900030300028034039864003000700148000400d00764001e2210442c1401140e01c00381d0100d80e10340401014400140703601000c20360380d203081003900388881440004c00080002e0180040d09019004a525010800000301284140e505111050312401d0480d0a03481c0c48d414203400a001c3c00050094848134401c1c809062800c10030985241c1c600f1000a145c84da40b02c0d4000740c0303800035240507a407c1c1c05001c54602e82c0030b110005410460300c070b8071405a00e1410190003403801c80142c444203600c0b03600566901c00100b940102800184001d0042001200c0100f0035807800c0344401da201c0070388041019020030555502407100c038203545c1040615010030515450400001d009056100420409101e07078030194003002125003191001103011400d80b540c004040f441641c0303c01480c1556048180c84903814000c40d40a1505071340c003c03055110402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 479518902 1250 479517652 479517677
    0x50108070e0117100504060b03220302030409020a031508010e0c06090117040b1f030812151f14090109151103040303090f050406050303030a1d0a0f110609030703030c03 74
    0x183d4800e06840c251284142d010080c403007810640100c3e8000e01040700701d2465840c100c04010900e403200740101403996100340e500014140300308103031005024041011135503012a03a074050b0050840201050f0045800040002c00b180c042c40380d40300001040001c2c0500160700c030200035041d4090b40d8501c0c148001d00c150b0841200e41c81314402e11440c031030816094103040081110082c40d0400e0b00c039801d546042e9a062001850100a1302e50500d04c09402c01ca051712405810f841140410305180d401080b00d41d01888500c00b01c0d41c5103a80440c95449002d0f5106034010704507414801c4041841c04100d5555041002800c03091280c0040e80007480e045086815002c0600d003150300951055000501d040400c1c00405940c000c26401003008a80c00c018041c944404a03807240002080150701c1c07a52140d85022040d00b09002c800807400c81c0c01510021a20762803c40404041900d0503645c08038506032410701030420000701c41001c400180101565844d50354201d81c00c104500044040003644502d81c2d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 479520152 1250 479518902 479518937
    0x71d0412110d210915050f041e060f0c0215010b03010f1205010608120c06100617250207091505030c0d060209091e1003080409020d240303110601050108070e01 70
    0x8070075140f0070105444540c90321000e05d001d462016000c0714031038070070344103000c0004d44a01602c4810106250b5095100c030300f03418100018036446018030085818605100d02565000c11100304410022102d190340780d03268411072240e0f0000740208104246200b00034040c440c1c050b000b0740d884511620003c01c0d8251074203a030f94140031206920500000000c00c1c2203607140c4040c05841e500404048008400d507181c020000c0618100d8a031042c0001103102c046260292440002c002c2003856203480f15040103c4840203550340c80f1481040d0380300b072034003054114000000200d03e0032550028000c0040e50608010002c107819107032000c40c0e01c0c40c0e080201000d16101d2000c800d104401200f0f036070300100e108900c00303030541000914050b5590035008060001522040030340b0b0a460380d5600058440d01d0308044100100b040c42c10101705000c010b24a1007800c0d2a0b1a840d200762403007507603a0891201c60048036542c0300001e01440d404545200f0010307140d184255107001c0000c00514001513541c0c8200702c113 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 479521402 1250 479520152 479520161
    0x150303090409060518010207120507060b1819050103050d0e06121014031606200115090605150a030b22090201020d0e0a0e09071d0412110d21 62
    0x44541d540c644042040c070703904602c0c81089158401c17000f0740c0f030040150384048001455600410a0100119000c03007409603580c400a1070050280c02203194000d07400f59204054812680348a1034200400701700e0113000540190380c12a0f030b12800416003d05950780a075803052480c400560050000d102186c070803200710300410f0141840c01600790125060581c4a0740101000c80241d0090303001201c8581419100c004050444480c1e01e444040f403000b048150b11500c605100b806c42035801d1002d94103d80318001d41d01411070703004240410070980d4407402c5c407801012003c000c0c01502014054615028000d411030600300704010300382c3c007119440100074448820720038040c0c0c00c00343d0340e400c5500071540c042110880040c00380c00d0041006040c0c00020340305000c0c03401440402d550300004078a544200300318000c050005071516a2400401c3c089004d1160001c65095841555405660504038000c0c244071001000c0030019105101420405640301d048500005201070840140c04c4c4c0d5482c0079114 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 479522652 1250 479521402 479521421
    0x30b0c0c060a0b10031806050c0d0e0c1c030c060203090a020d080a032414030a0605090607090614090d020f03060a020a030605100816030e06070e0103050901050903031503030904 78
    0x1c000448022043c180702401001091540c1070624001d07061120540780054180616849040070509948001a120f018002c0d940109061800c241d002c02800d41d000c188401140015105861540400344184188003214940a40401c040503140c0001c100303950011a03006c64800202d980c100d1041c1e0109480c0070300e103030b0162003c0401054050f42d1503454058000201e840301130319405080f21620400071509103100301c0c42c801c0c1c19000033307030f50a8800f8065007030401d800c08401c0056103442d11042d0340b0b400c41203c1000c0080d0f04040301083d07031409003054003000201c0e60b03e0207081841510a020400380c103900140e9206600003602c201c141c0e420042203100c0d44100401684950072050064280d0701c40741c0095115002c0c95810150070b5034000f02d80d0b40c2c410309a1140e41240c03c0e07a41020340c000c160450444c2803500601d410421826044944075200c0d4901303a82c10085551101c00160807a0000d1741e01480c140c0007000420040d51003003444581e22040102903902d003410880c0000c08a408410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 479523902 1250 479522652 479522671
    0x1b07030e0a0b04060806030a021309050111040b0406081609091a04050108070609080111030a0903050c160e070503100e0603101a0414130605100b0a0c060b011404030b0c0c06 76
    0x143c14404558030a0b0f601c1e800440507070040001c10381030350006807458080d150207030750b96a0399129141405401d4200ca4600320042012580e80d40c2c43c0e0301c40003c0c42d8407502a4030007043c1d2a0b4003048103070000c4e524500003000c1c0d542c1d40075021410185410080c4c0144c41a15408040030480e13004240e540d0310819000b4080d4000030143c59141000150a141542d0b2003158941d00d00500d1034034242c071850031290b0041d41e407070001810040ca46070946280c0603000700c2000760310800d10751445440d40608210700b524002d4071701d4100d0b0b03511480200c8191000322503800c2243d42c9110f081002c6200c00b07008a400110040c290b07104a120030004104450500b440300b15807003103007003c1400f941070502c05c0c0c24000d407055602ca5010b1502004a90740c0c26070804005003001e03030700d50004000a4603040d01c0400381484c442e17602c0d541c0c142c240b80202014002d1209071522391908a54003ca580a4400030707040707000c2e0911082c04c1510b581c46603104110000c041280d440010400303950f0145091100502c14503660 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 479525152 1250 479523902 479523907
    0x100902030709051c05150705040b04140f040504110f0f03100501170d080f0a0f0e062e05040e1006030f05060703020a09140307030c1d0c031b07030e0a0b 67
    0x40100401030203c01c01a0064003513034165140032600100d8031400c4100d000104c01441c1c1c0f60004100e0300341c07186510140400c4804a000329040c442e03c00c4070981c110040301d1a09800102c1d00800080382c4041c1ca0051518840c2c0c1d101d500507041020b80a000d041006020180c81240b04000ca03040c0000801d00c0303520541d440c0700601003241a201002d400c4100d00380101503910301128080c0a007507014026000d80c0c0d0011000a01c5400749800021260031660402c2c4940660840400c0c0c1d540010b540089071034882003004031691400c0c40c120103102e50598585800c643c0340a05100003000c40b0451411039001e004045919002103000c0d010040d40308a0b82c103507003401e07542401424000b000d0074800805004010182a803640401c0310b400380c1c1d05011000080c080c040740080d2034440305600c01002c11040041c0001c055140b0490742d41030108145190926586000142117503100488025400041c0c0c0051b9040c5000c605015202140c400d0409103602582d241c005141e28501d64071001120100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 479526402 1250 479525152 479525159
    0x3051509090705091803071e06020706050124050f2811120414010e010309051204150504050604060c1401020c0a021305070801090f0627140f0609100902030709 70
    0x3800c0701a40100170311000d03501c03001658025600e034425003802902003603050307003594600800800c800240c01d902140440d40c442d003520740000545024800c00f07a0742000001e00540c0424441402c075440d07886540d4551a00e60308800e4513509401c0310307503041c0400800f0310789072403801e03180884039064203055145d0313001a1451030103c526103851000c42848046040c41f08114404458140110b080801d0800c50440b040500c0100d00074010f0441c060101e1249585440c01c0d0090500280150350b0404c1304c1c0c8042881d104001e4071540306a1142d01c1d0441c00c10001003141620074a0041c02081c81340c03041120351004814481d09a03003080c65109015040180d2270021450505003002503402000c4051005280500d4040c0402405110742d102c16a1130740003200c40803400c3e03404040a0850001d000e1101c00324401031040104000301c0130794440e8580201262890040e8110703d2048108004008803560340304113001e94100040d0a03460740343e520000204212855002844c0b00b14865500c542e2031524 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 479527652 1250 479526402 479526409
    0x60908032a0f0f0f01110f0a030b040b06030f0709090908120a06051008010e1e061201020d151d0606070f0c03021c050105070f1b02031603140c06090d0303051509090705 74
    0x4c1d010b842030700100100b01049a5111f40e030300761485d90030345050005a0250800100d406003d0408240c3c0e40280c0000802c41424609003215010745402d42c2c4903007030030b511903030090100d80901001406401d070610102000149409510364002c100328000300d40d4503683c00200e05040d40d150303e0000800e03000801803102e40d180c18406640305840503142081f681082e049685a404041c001324018621a000340205800940490303100e0315501c0000c003c1d400c4024884509181240524a107440f45c9a008c4100c0807d502d501d2030098400a0940703140c218280d9032080840c0d40c0310012100300c0c05c68403000005da55294001c10446903081c0c8440b401c010280b40c400c1c00c44900030480e00074070a0312040e8010003503020340400d540782046d15400d0242030850001a2410000940316100c00320542d001104222403d18000903580489044469041d446400c00c4518000c10031000d401820340481400032074400d411054106103075a1304420440c0500c404100360900444040000b50b000311810811b906 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 479528902 1250 479527652 479527661
    0x906170c030307120f0e3a05060601050703140f19080c03060103020c0a050f0d1d060d0f0b0d0302160f0308090d0206040e040c060908032a0f0f0f01 65
    0x10000c5019610f4440c840e622100f21002d050750b49401c0110716444020091300917121100c3c0800002c2c42c00184150048001c80080050801400c3c440d4010b0031505400300b01c0031210701c1440c1c1c0700000d4509940c4980044506401286095040151114030f052503020b4140007004580c8147c1e15803a0740c1c0402c081c9000c41249000030540811001c10b08206554082c4402c0c2c80e0007007001d00c0e002d603460921240503440c242f98080c003d0400d0040e032507240036050002510141e1030341c403520341084480310100181481c20b000340e02c0541050040140f2072448507180e101c503200035080708000801062031404210018010035040b805030b0303c0b94a001d02825900002000280f0340d8a201d0010582140d540301018042da00c4007600035040d0514036002c554443d002d83d4003403c0720012030207951410381020114180d0b240310300c0c40270500c0301d0f0b00400d00410110454141ca83e0b0900100b044006c86000804c0000062850a41500038103503403c00361541071000144982204006143d904600c130511400c46 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 479530152 1250 479528902 479528923
    0x301062f0d1403041101030b0f2808150105041806090b240a031104061a0405091302010203070b0402030111040305160806090714010201060513020a02250e10090617 72
    0x15003040c000c200001721000b0060170500020320f80440e0644030391000c9400304182da087d42da03101c1d01c0b02900c030811409044900310f2190445044054441c3d5500310140c070752010700d81d0740024400c0c0c0801400301d8281604600c080d000010f1a0b408520000d0710f40500311102c0660480d14031501c5000e20142e0a01e000260304500c40050311560741188140c001209460369120003005005025140d5100d03944035803112001344040101a0980d03034032007244140c268407a002c1d040c030a102c484003107607514600c07035450b08410b81d0607001540340000b0b5845103803d101380100101e0381503407210340311204207102c0c102410003036100e44010042c440b4103a004110b1410346400940cdc182e8841000c1003800240028417204035240311000014540c46400103d0161086030080d540009030550300c80c035201c14990003080d00314146e0b030954480014060321240d4404014810428101a02c001400401c200c0c44100d0b402040741d002c94030200740c0d1403002030192070450380315412403030f0500240542c2c0d400520403074456 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 479531402 1250 479530152 479530187
    0x80d0e060901020706081b2b0504020901060c0501110d021c09051c14030c0c0c01020a170d0209091815190e010b1201050108010b04110301062f0d 64
    0x401e007202000035524103452080c1c004010040010420800c21306003d00300707600002d4102682c0ea650303441400f15401c4500c4000800403412202d410b185a82031148502036903000300020516440c01c2411181c10110040689955690710300c140c3d500041a00200205c40d9540e2000d42c0307400b000d01c0820000b4110485000384603080a14820001c0d40100c0c440003800001d000c1c110b4140c1800700308403505031030804401c5a4000c008140507a05403580b0140c1a0410101d04071090090f140c001280c071061040c00003094014504c3c0612107040c95440549109010944014207101550001445515003622140b2941c04010581c682044040c40090301b03080194140784030724209202000000340d040c004030701000755280072940301020290045c070b00c3d4a9005040d009001d40510629000b0708080c0715509196280800b803030028100350180e120085015107006046070b00e4000141e0308000d120402816a020700071401048120104406422840b15401800390010040d4007414522000015030076 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 479532652 1250 479531402 479531407
    0xe121f0e030f040504091505010303020a170a080105280e0a05130302031920010f20071b0b04090207120c150b150d1505010903050a030309021504080d0e06 68
    0x51030b08038040300c04441081da40052a850581010b0b81c0881c034000305080d01e1814a400001450f40c000b5423210a940503c07e510620340030856008803a114110305c480208640f40010400c0303140c54803481d80c2110000c100c500148001008641200000303800c6075198000010a01100c0c1541d0710500d0740c0300f1000242080c6081003a20040e41d0b074024000c00c100360203401050149402d11078610f40440c003003600311010b5844511100a0301901c81052064000c0d40b41001d800189400f9503d65102c042a0450080c074000560326407052400802c91802840c1e50700d0200080c0c1c00003100000d2008003c000b10060b02c0300c0d035601e0f007548030600781c0383d01c00f0411804240c4c28001c140304500c1d04a000c0070f03403100000c84c1c0721190086452001d00380910840f040001c01c00e44a941516001500e5504013907401070412501e0300c0064941c58840c0c0800f034000e81c00085010f0001e802139110b40c2000d03000405003110030140308041091548140c00ca2599600680202200da941100d04c0c144074000445a960 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 479533902 1250 479532652 479532667
    0x1002030c07080903101e0510060e01121103090a03020705010e0105190c05010239120a05160f0209180d20010510061b0302030a0e121f0e03 61
    0x303455018040016100120000d07404030301c0d0f6010044e132800c1c0c8000400a10007000e000c0e480d41c0d403500440000ca05003504200009800b101200044816109140c03106004803c0c40001100c1904c402070b42059016603540011340c00244d0030010707511424083d001080d02811914000f410440544e1040b814004141e000700801d03a041000c0d42d000d81d00e403d030840c4c0b450200c40c00072100d4000d000009086075200145075000c101186d0916080c3c40321540040181c02048103070007200b10300025184089402c464407002c61580310300c004210402030b518000d4200201000c441700001e8103450101d03648145064064114202004040c0d4014001e8030390480e82e0706005182501c079000421960100700c2c88010010b03030031501c0f00042e41110403c00003007202d46072022408081c0c491600030040810f40c660312a10b002550350f50207002c80d95040d40a1414282c81c60300c00e584c0e0546002d000d550002074004103400e05982084661070411904001480c0c0d49a81041581120560303002501c0c2c907081041503a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 479535152 1250 479533902 479533921
    0x32101080303160201140705090a0614070809181e010509090c060c0a20030f060403020327042a0f090b030a15060201020414060a1b031202120405100203 67
    0x141d43c4200031a0582c856100346000c101c1c01401440b02000c002005c01086c40700300d6a00001414000f501904c2316041180c64034025200300359041c0010400100400c01140010901c102426503040c000e08203481c00f00450600c08081001161051500c140d028500500e000c0882da10300c1c01000140c92852060a1900945448001c405142805003030300064810303401504010649200307810020007243c0903120701c40115034100d951001e601ca446684a5040e116001107a514000e9906400940c5040c0d00051741600c00012185041c0042294405021050321030340101040000740ca1902e0300c02c01500c1401403050b800b00b103150341c2000032400e0243e440c590013101070f0382a40c410800558036550b458600c0405032440301540001c0442c001400110140c05402510550f45500c000c0342549070713100140401400340d07642183c001045a10040d00c14085c242c0703800c10711340c000d1510015802c18107200202381e0740000b41e04840d00040a0070031060140c2801203198249281c4419855130400c85980d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 479536402 1250 479535152 479535157
    0x61407090509040b071103040308070203011121070504170105040c0f050a061206030507080d0206010e040818030c06160c09050405070611010b0901090c030e0a03091e080a050321010803 81
    0x500700c8143d0004a172445001d04403001201d06124100c0340d855850380350802054020b841c040340a5800d103a9030300d400c071840c0070a84801b2520900051200a1880c140c44009003019119100344401048046502c4ca062988030300c820210400125580c00c013840c10800c41007041c1d1281580008620007485599a86e0070404200d4299140c1b10006005207800a801010071381d200604a114400c8005103006020500b4403c990880d02a1803450b0b07601c030241d0484035400c075001441400100310f640a0501c0603907024034401d1000d42102e1442400902007074640d0b228150001e030b5040b04c4d0348454108400301211001421101701c0c00c3c403041c1801e6071102c0d07450886014000c107000c408012060340b00c500758081071300b0704001410381086580d242c80c80001003000700300180010342072285011014400081040034542d140d82c540140c00d19000391143c0800d0446130b451a840004030000485410400c5008060380c00340d00610b540d1740c0907041a452071b8014141180000101d80010404070001206 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 479537652 1250 479536402 479536411
    0xd0303020c2416180617011203021018020a030b06040c0228021f0e01030f14010b090d05010e0106060e100206040f03120c0c060f09020f061605030403061407090509 72
    0x20a00740a070496020b54003a1110f1100700c10700182807400082c0703568031406d5401c000e038100c40b4126040c0d0300c0c5c00c4030354046510f480c000750150788401ca02d407c0310159544030f1004542841c9400c2c01c1062603a0010b815a04954019200f81c54018140030300380c5468412a48001d22900040110000100034029522500b64803410050310307400c600c20554841003980b028409000b0302c090410f034101071024041d10300084195002a2030485980492501740c4510b4070204c0541c440f4001d00e0313103091110f82150b4002160141c0181d20156030f98001402400b88041d086800030000c16482c2c00c0000040c140340d18128210700c00c2d040a204500b00f19000310b29150007030b8000b0107881840c1d9184c10b040e00c07032000c80d0082103442480c200b11052165400401d075070450b8495103050002d0080e401003001910314040b0060740c0311114200c0000a440c0020003030480c650504032004a001e46611498110f0b00150300580c0c00c01e48681d94003401001da80111540481103040139102c075810540840c000c024000c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 479538902 1250 479537652 479537671
    0x2010c0b04020a030803070302120714070b07030b03010c0903060f02160602031b031e07030c021002090411030c041406040b070204022a0705042a0c0f020d0303020c24 73
    0x300403905549500080030061a0070130070850313803401c1a0900034000e51003247ca40030500604c070046000c081c80f43e500200b42420051403507080520725202c0c9400e504001d00f0680a0568894011440b51028021300b0b1130ac8840791510050645181064401e0390304040c078106032140304102c140e00000c85038441603c00c54110000503103d6458011140002c07402502c01c8803008000b00801c0750103c5081c0016203983c0c1c61035414511074642a800340d054071154210760001d40c00c840d50b08860b8415607400380c2040d041c000c0010850185140355082198015a09034100348400a024414244401454001600161503441c03801c0e2030500c4041d054059868024401d9400190000d046018841d605c0180303070038244403640c0c038008880c0d1255910000d12074203015904040281e091500c8000c5080314401984012100f042242e40741142c1d00d80030002c0440e030602d003006480016031034000341f450b5458482d80b00142d440406d08040707860251101010f1483c0c1400070400c1400102c0e400d0f00b80e0300f041505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 479540152 1250 479538902 479538923
    0x120109020a021908281704080315011202040306050f0c040302030307020f120d05250b06122a040e0604020f011119060f0501050a03050a12051213060608070302010c 72
    0x3072819004d0752003421a48207030944140c0b031406400544070221a2000c0341500c0c0d050030f080700498a407402d0f0008640140208409100060401e28000d0320b0402a1105142c42c0c0102e94840c0200350890f0800c0e001940c182d651081009000c030100b5442d113402080e1080d0316030901e8a1640001d540c0e22a0f140002d015a00d14071400142e40ca40c260380000e600d41d0801900c3c0e29904580008040d500200700d811400351b81070120400444100030042d041c10740200040745159513040c103001c203146030601c00c072403540702d21032110f2043c040341044078540c00e81d00340c035014040c2c2d40c0d1004c01c02558403205140c4441e40200d0305100050355040042000920300703003000c3c10030310410b00d281410f01011208150080c0c00c125a4041040481d030b0050f070b0168116803040180366243c206000400181d4080103001e544551801804603018101885000c1d0701c81c9001450082040c84a10405200b55100c03542072822482c288200801e5004820240c01d190000345550b5140d500001c0500040004c0607060700c1a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 479541402 1250 479540152 479540203
    0x20901030b030d03050601090902040509010510020a1208040b060604180903021903030b0909010507090603090c0f08030304060e0c060d0209040e0610180902011e11060a02120109020a02 81
    0x280c01c0002052001001d44106114003200540942011191640024001d12001c030b0401c001e80b00766416502c0c05803030b440640e824401130218001d03403c1c809030158030654401100144960000d02d03454034083d0340c0d800342802c040c6080d03588070b04040d2100e40b040f6020f1206104401d02c2c1d170300200380c010041c4000b00b001c500341c0c00c050341071059440f00310108141c6001d2210a06405402500785200c1c207581d0200950b5a10300300500f00d0b00141c5400c00020741070207003000f08900c03070717040000030300c0c0240060140281da0f950420051a003542c0f001005400c00310812003030022500c501030b4140100c40203003c02003200c40c0000c041d40314002c0180841a40411100074030b445d5a4020100d00d02400c04070791780390411480001d00382160703104080c0d181601100301c0070904035034062031071460350684424109a02109001d008201d40d1618030b000c10201d60b00d550804441017000c14054a0981c6006030350341d001c1166808041c8050f08000080c81c01000190703400740d8006031420000000e0861410700405 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 479542652 1250 479541402 479541407
    0xf070e0f040e0304180204080706140903030a0c03080a090b06100306030804060504080706050c0a140a0209010e060f0316060305040507090f020a1704031718030c0706110619020901 79
    0x5036152040e0458500200310740207190000c0100240c0e03281414100d00110303003840c80310a0748205d00803201c40e038100e07240c10003003940240d83c000384000200141c903051081e01c1000c00c2c5160020302c400e000140882005d082030503000140c894108146c503d040c0603a1110780c40d52841a20040c101ca40161007000c04e5041c00f07403003980000091503215580c00e66895494000511a41060080803001c1c000c0c40320005a03e8010422500f0404888014140d01c10303030f0b0303150031661241c4005076a4079400360b5500d220060b07440c00a07460107400200104da40908041091040b14819401d081d4001e500451314842440700b0030121000704c0b006440d001c50746584034944181041c00e0b50340031038460707410007880c0400348000b900a8038200301260345180700443c0444030088100429940600460322005043c2e0394000d41103400e0303601c900501c041d0100c4484041d04289181d2060f2140c6c0c1c034580002c181400600c2d40704c6018602080c0322001487e081c1460a0b503040c038090212180e210003540083c0d20300840c3d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 479543902 1250 479542652 479542669
    0xc1d0d03120e030706050906062202030a020403020316061103040f21020306130b0a0204050f1e18091219050d060f120c0905160507020a0e040c03030e090f070e 70
    0x1d21510030b4030340740d0741c4e0380c640000a0078056802c0c1180c2d0050500141f4a0b082c91450140180202501420380034400c06c0403200075400030300072882c90b0790208404405030310308203c1c028114000d10f070028445490280010514500b0030145e80194000b000200050380c4004080e03000c0da480c06c0320020200403010006800b0700d2000c0002905130240384c040010340400203041c00344841c0140050a4141c0d00c0910110072440746010b41584031103c98121012800c0140b0901c5c4184050b1550096074030304500000e841c40030808007100700d949040d0030007007014428440d01c03038021040d0008600b06046811000a050001c1c6c84c900c080000101e20680850701c55041100101140780c41541d41c00d45035465030000202481d0181c605440003030000038a0005881410710411784030014640d00d0100d82422507442e84014802d030382c400c0c3c1c00880440c4104081d08818000c601c44c01702c0020352482e615002d001c03008400c00040c802c00d01041000311100c0c551301c546034445a03034a030000344410101d00150551 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 479545152 1250 479543902 479543921
    0x1008100221010611010c0c17160501110c0f0307020a032406060804030e1210020f0d061217030c03131509060204060e06190516060f0c1d0d0312 63
    0x11490703000004141d034101e40c03441300803240032000303200d400a010020b603001c0381550300c01421014803582d001000500e240150401c003802c0803984003c02103030b4a030282518000715002c804048001915088850300704401c420640c0d4100145041000f15000280d03542d61510010b012400c1140342e059203000e01c0f40414403c104049000c021306a19414000c000c1801101c045020980303042020405280402c902d11020701400c0003050121402101c2d14065084900c41d01c040d24400c0c0000c40c20400300e8096080500300c199400640341c122820710340540c0321500b40c4240440020828842031170b24140803030354000c0c2152040b9070482070302e10f00411a000301c5030a0707025480c0b80c2082c160400c103041d00200100e42c150b076544403801c150b200030407000c1c0c814a00003a20741040d01c40c1d0032102502400181c803125110b200b0a0f6000c4200c1d803103030000d40c3d0405040c40040ca40d5a003901c2e03681d5800c01c2100880b074044101e0010f003061030703401143d1464111200902441b4045030b58030078048030f0380c11480f520b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 479546402 1250 479545152 479545207
    0x306360312070903060e0d030f09020904061107170c06010e0c0406030c0908032802010e060414010e0a0302160e010510031122050328140309041a03010510081002 71
    0x14506c0c843c210548600108101200290410510602001c0c20340035034145903400506400c200d84869503002e0081c082c0040c040c024032000e11101c0041002d14810800c280001e00a007550344407040e8045090001c143c201d8462280c4140038080500c24810640d81075400ba0b08000490ac5041001600e034015250711100d5107100028480070060804e28403001c4800c00a0300c11007241c0d8403c241a402e8a40d850000c150b10343c0641c0c0094081245601030f0708860040c200000342036264403a4207414800c0c555400d4002da8000d0302075540c001420300f0b400c00103024002c4031518550400000940c2c1d08030a00c054410142c88242e0842e04100c01411501401a4600e20f40c0044000b50710f2019507550b1403044038401d005454a00c0ca40f0001160403004082d0603030115a6012482e9907014a5a00e60541d000400d01c0144800b0b040d40e11a0300c11b41200d8032080003900c41c042d088408150035290002c050080400d06d840e07040208100c001101e013040aa140d2000d603d540f503165103c074040051802034000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 479547652 1250 479546402 479546411
    0x17280606030b0a051e010e060702100206190506060307050a02011104061709070f0b0d060509180607020a0b152403070f050403111e030636031207090306 67
    0x800a400d40d114100e848000d40e19038441c695980200b01705188000400303020200c0d1070b1081805580300c1c06040120b114028481030810b619500800e00380e69001e507410380540c0c0114144884c1010420261511070f401d40800d00c07113894203001040a0340806801c80e001d1000102c0d2002d0140d00030340040c05500c540d00c208070748035660794800510b465a81006e400c600380a42011408241000c101c0005031101d98184002d00ca00d04030300b54001d58081501b91401d15070340da401051035960400388074001c07241003a01116400080d4a1030741800307000b0303003a4400e56124004070760000c0c06407040c0c1c0d42c3c001c00100c51007180d141c203035002c92190241181e5100d00e100d00702a00d41c81c000e010202841c080c6034203903641780c0304d0104054280d4892145000c0640540040e901040e00c4d1320700042c41c50840103080340394182441c0c100001c6442c1c803500f520800002020038850b00d200d0140150101c1e0600343c00c0800c0032681c0d6840b0865501c80c0304000d4048408240343c0009003506006d00000e000640c2e1184c000c00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 479548902 1250 479547652 479547659
    0xe030105041b0905090a030e061c090b0105090f04030e0d080301080703170304030c080a090b0c06040302012316021912021903080601031e090501060510172806 70
    0xb04141803001c0e111100007419602040e04121441881d10801006000f0604202c00d91801c1d180348061000003680308104000c0c0c84407042159a119041120540c008100b0f159146804034a60805801182c065070003030080150001d40000381d03031b8000d905400e2207041d1007101c102040b40f801b00c002c0c01401094001000003208400090200c1c1180d004005901c0a552480d04810f91b6100c1a103020300012440d0a851000c6108507004000042d0181402240e4507a00d88101c21580c00c4101c10788610707040311003000141602800340704d03500d05010401501c1d0401a01082640d00700240100d84801c4100c0c007504582e80c004c201d060750210034429101803405042c5419580d410b0451610030040c0600c0949900000c11030b9620804076507da16910480d9640d03400444c020004404501c260490031081107050003281c0c4103a50310700e030196001045442c00c00e404d0001c11080c00444034100207600c0701c1381c03514000c40e5040a4205940040c901c40324403446a0b9960800341034510002143e203081c4000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 479550152 1250 479548902 479548913
    0x2040510020609010e06010302010f050a090e04060b0a06030b011202070f02063c0a08090709151a03041e060209061305120d020601060e030a120e120102070f0807030e03010504 77
    0x89201c0c001143c002c0c0302807070000c10b845859090130701c0003e01103403240782e40d1592140214040c000c0c0780307000d1400304600c2d41c0c2c414498001640540d010780788942d8542d107003496410000c001c000500f000d070406004c0e1440c40000201200c0d103002e01c00c04050b60114851040000340a0007008243c1c000302070390784501c1181202c5001d4041000d030581195541d0341c40d00000c100c0941340881c082d0344070104500b0314201407001d40d180580202400400c3c018042e0105e01c40109228040240002e4002d5100d11801e00300030680020902071482c2c1c000c0c1003401000002000300c1c50b42d407601c03007043c0008900c8041c180f8001010303000f004a00c9600c0f11011820145070401c02c00007404a0b8400c41300e0703502d504040c44180b40c4409410b82d07014010f81120b401440444d000e240d008040c0312010301150680e01d05a04e84410700511030b401807001450342d09000c915407604141070001201c040e0021031030040503503510840700044540c01089148086604c0d010315019540c0582200300103030090016244c1860704 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 479551402 1250 479550152 479550163
    0x9151929011d0603072a110402030a150308031504090c0b09061b01050a0f0e06070e1504091b0212180111030a0e040e0304050a180e0f0d0f0807051c0204051002 70
    0x10fa041b045030501821507443c0c0c480700c0b9250b016800910008120410100380406075000800c07a01240d034480c84800c1c0b2119080b8090801940982601d9441e424182466800700b101400038070b2060703080c0142c210206480001100444102080065441c2480b80100f12103016070601c1000b82c05441d5120000c810064104610034007210008006900380c4022080480b03841a42c0030001d50b201c1800103140c28000e500c0c1581e41c0100408407030449143e403420a50350392050b045404440c0c3c443e0030704c890341903400300c080d5900501d90010380020340084501000c10301482104e100f007002c081104000350b90044a805500340d01d2071045d41d548640010018103246070301c01d0014000d42c80c0c50320b44071005101109031002e5880041003845040d140c6090002c0c60314003464004d548a40da9100006008010808500c0d490003203000307850070914500d400f130480c1562281c048140400700f02003007581c40c8e126040740c0000000102c058000164000110024011504802e420002c0684100102d507000141d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 479552652 1250 479551402 479551427
    0x815240d0609060b010c0f060504080409091a07090303050d05062d0a05120d05030c0c0a120908030a05120702010605121b0a120b09151929011d060307 66
    0x8084c4103480c0a034004413420700700408090b160301d2510712514000395031500b00b00d0304a4000c0c481c13903090980725280082220b0300c031b240843e18062801e4083d1000b042180100307070300c07203081e080c14241c4600d1510042c20912800d00d0034183da55a550000d070190b0f03a02d42524094003c21402c604070702b0784489200200080d422165481501d205a0000700b92510582401040400781c002d0040c60b41d502200391200d402c007074000100b03500c05001606d41c018003044a51055800780182d040c60907207000c000342410340300d90020340c3c1e00e400c10050080c400c3c4e0018110f42d603400c604c1e0341852030769550701d000300d00429254004a80c0320920007504515040000b40d040d02c0d00300d108a480c400c100030403040203100080c91107004c03e40c0c80032088410200d40401812540440301d041134a00014030481940c04d00c84045840c000400a0444503400b00352452050000001070400603041080080080420a40160400904000c844140c00485c03100c6120110082a4060802512030030001400b070002c81c40d6a8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 479553902 1250 479552652 479552663
    0x40c12061d0601050307090c200624060702151b0601090c170105040b21010c030c11070e101d011a03010b040b130b1c060815240d0609 59
    0x401580c581c00490000c1c100c40c0001d0050086504e080224000b80c0900c100000600211014440e10307601021001034004003c0340242c5001e18000c04d0924003403400980810070004050b14021032501e800b401c40b1205c5804841214503140032001c60061480703201541030002d0141c00800e0300c64034000841070b0523255041c0080c810355048000448004484001c920203800000004110506156011141d500341c00b50064841c40e0284014503007401c0b1411060080769034070b00748800300c642c2c1845100d40d101e0492814001942d040c118013a0388400328012500b4580800010681d0001070b9034000c401803c0e1108402030f14131600302c4080004400b403080001e03011024910107a90914034088038141c032500110301e4105801e00b4624181c64229100f21034684451000118200c00204045c0600c01c0304820843ea08140c14400328094032201d92010b142944003c2d06c440d8010302d030000e0150b001c88003070740e0a15801d2000c0c080d1402d5261701c003450b5030440f01181100707007480b580e0b0700030001c480d0181 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 479555152 1250 479553902 479553941
    0x40b07080912072102180c0f0a1205061e0f130903090806060301090c23040203010e060414070f1101020702041b030e0303010501050306010c0203010906020a0c0c0b0405090609040c1206 81
    0x4415111100c032807620001e43c821090300d070400c000850a0542508045912140c41c10491107840280c29503100120740313000715088000b17401d0032031041d00804cd40301000392038030348402c41041410b60b0202c00c80705020b031040ca200042441c4c03540f69400c0301d00d00d0a107008010710448103542405810803e260082d03101600030340001454500301400f032152140c3e0310900901c2c505140040c03102c07440ea02000c000d250506d44138401c0f042503807a40050350207440c51005c0e84405003000b004220032211b0203203c403040c00c0018010480040d4214400101114450410413840a248441680240b0410800940c0945032080c000ca40b0301c10b42501085c2981d440c0c404008046003a04640d80d20f010900c0340500160040000813402d5200741349080e4482e10142c00070610071f030141d50343c406903009080100c0002d03040200107014089420340c0b000c0245400c405486c9854286030118106040c01044503000b030003240c01103001c100b00c0e4990600206008503c103800865146014005800b40d20403041200c84003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 479556402 1250 479555152 479555189
    0xa090201080a0b030304030330050a051b090d020d121e0201060321110d0e011413030b06360105030105060a0510030f020705010c090803030408040b0708091207 70
    0x14400c0e00110f40c1c0c010300560030107281d540c04803201e0b940c0d64581c00c94a002c0e20036004401299000780d0024840d07010300070440785044252a01100d03801400c500c1c44541d035560b208040c001203030444481c403c041e0b0300400395154500104400540b0008014a08800c0c500e6540e40c09900082d03694880c090f1014079224006600e2003207090b180140030240003403420007000c866a0708007508400e0090315605112101c0c01300001100d080072010f40c4c0366408200e00ca41c244119603031000c04489a401e1000e41c0d14109481081800807110140c000105000565004030f0595503805444d140070150420071807480380391030242c2c000305015141040c070a42104138004200d82c83c040c0102c0b40b055002421285c1054030b0304007003212002040e9802d0050547d40c0148041100c60384c00100680342c026400860342f0680080011f000011941c00050701d60414020b000005d414041246d040320b100c2c00d04c8940b00c42090803c2c080d1403003000388140c0e0080c2403040f0140b40603408103081d4100c440c0001a80c1c0c12510 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 479557652 1250 479556402 479556421
    0x90b090a231014181c03090f0b120c0f04053615090601090f140a09060b030c1c0609050405010b1002100e0f06071701080115090b180a09020108 63
    0x10f050040c0791480300207000c103080b420200c1d0100e1000c50310003003a02c0340c058000d0300460940300791654107400140103000140044070481c009100204002d0424030318001c0f140454082402c0098003040c28000002250841c411102d829103002d800001d00c00c2d0b16401048441c8140340b00c2e180040143c0380c4200314040c8000d03510008540c41100c596000c1c1070301813980030812140c2c4100818250510202500100703070a4a400b482c040584030740070318611500c4220040180d4844a94442e1180398240b22003031109070342c0c207016a90440f41c0ca1107a15107074021000301c1c8160300e0580b01e40000b001e00d01000041d03c80c10036003140c0c0c0078901503c000c00c48000001c040c8000e0015110520b40540e11505424024010951100e61072000910503110165025410716041c220151b44502c0000e409051034543c0d1090501c065005080e0031000300141d191a00c3d0421a440d0644201c011a40d07603a40414003c0e21107440095001440c40144e040c40c0ca8a11281c200400200400764005602800010380608 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 479558902 1250 479557652 479557667
    0x1809010606090612020306240702040e01050403090303050304060207120c021c05030a0e04110d0e06090604120c080903010608010e01140c0d050c04080a03030606170601090b090a2310 80
    0x5681307580708090200b1651801d0040e40c80548001e4105481a429141c2400e4060074940100a0380300099503580840c0100401d036040e001304106e450f4500340601c4000f0b9000940e140c200d0740d040c10a142c07640d5841c01c20b00000c1c05802e2000e0b00c000310080345110080c1d40304800d01030b118800c82e142c244100b404240c54000981c5007000410381c1d84104034a003801d0380030300c17542000d05100030000b240c040614000c034030440e04144011440b403500c501c00000c402c00709211187e0b00c0504100204141c0c0382a444107000d0f80750312041081802115680c0606004401d012203400410150080c003060f5031307a101c1c040c0244141c0009810313552800e07040749448003031800301c3d034091550f40150314104601c44066000503c0098400c00b800c401c10000000c0e200d4052024040f651f003c0e0b1000100e191400c3c3c4050705030040d480400000450a208004c4980c3e000320020068402c00401c1545943c10407000c12400c051541105003210346050002007502c3c11040d6500700e5050a45045c01c00791a07960040d00d501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 479560152 1250 479558902 479558909
    0x6060f052d0409110703091d0109020702011707080105090901020a0c140307050a0309080c04020703020a140f0304080303042a090216081b070e160804020a0302180901060609 76
    0x4000441c0000111201032850710704150920300503103460303524915001203440042010300003a40c0419103405140d04024020b00074059080450054407400c41245103280c0c05015482200d91701082d0380b025644a001180400051100c000815003050130025008803024411030b4403a034100c60000391680d206009031020a25a030301c2c0e414000c0350640d10714003800920115030f04944014008000494010000000868002e0300d4070400c079410107158906114601d21014003a900420005001a500081941000e50084070303001c1e09140916545050010081c20340207207210204010841503808401103009600c1240135914040301c140100080703207021191404070440e080d40800c519456a00107004015030421200e0003143c0701c4e9100c07550760b04503241d5101d01a00321002040144402c1008801a0044d200c405008d46800703104162091008004c420130048420040b6085448a41244010b15402400001c2e4094003003d481c1110104848500003076007004000a90740d4010903007034096 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 479561402 1250 479560152 479560177
    0x50a201c0b0f0f31140f04080304020409061a130b01021509030c01051003110f130c03140a02130e070503241320040806360106060f05 59
    0x1d0801410801140e001ca1292075030308100c039551410200d126800028098507165200c0c500b6120316552540d0403622620340602c03000401c80c0038031014411b08505180d1051b44410050391343c0c0d0f62403011078007510a0b110010500350400c02d0381214099080002c0303003460810355135840150083c8035050140d60302642c80342d01680000304042000c50034800020350007170040307084030302d406075001a00d421a6012a100590031505510902c01c10014402c0340700462812124040803c803440000381c041400c00020b054a180e0303502c400580c0303c1c000e400406400d0040c40188106240000540000e5840450758200c1060000004194210301c0c0b20100e000c0c0c015550341c54115a100d02c80403088421007110501d91040303100c1251020350301c0d140307203014a080d828404650710074000d10500c1001c0300c403d0307241d414404c01c0c001402036450010780c6590007181c2d400302c0307400700d038000c0390409105560f1100340c0c40c079048408580c07094080541014048503507565480c0c600130001c04044a041c090031048032603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 479562652 1250 479561402 479561419
    0x908070605010b4f0f03030207030b010905160e180a0e0c0901080a02040513140a030806010906050702060310030f0b06010e0f1003050423060907060302120109050a201c0b 75
    0x1451131011070b030010325024206400c8000b03448070a2200f03101040e80c400c0380180d00080c0d0900030030007005200350042c800000309202504020310b0018281410035242c41c100001c00d0715019030740c0d40315007400c0c3e0086c1080e003100107613041106503440981a41c03044107010b441546c02c1e6004c01d0a042c0b081c64104e0300e90300d02034580160b40398200301c00750401920900164005282ca00c002c81e40700c2c0c26070303108a2034200c000c0096400d03e18028003c42030084c0800c1c140018130000f04110380d000802c4405140e411a000c65407a40c80d043d2100c040c500d82c0e080500b51403010301d07100b0100038188000e47d0040e6001d0b01c8010900b440f4008100c41e94a40c00c03002500920841059924030340a07401c0b083d0080c1c41881200a10f0900d1411030121035407904903010264046002e00110100621040c005001c052905501d40110035036030302c04402c410b201d02c060b403540e0386000550700d80c1194850501ca548011602400040120058003250050410388881c0414030a4110021516220320701c00d07140003404040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 479563902 1250 479562652 479562757
    0xf0e04063314072402161103120405060d020d020403080a02100204120b040f140d081302090103140304030c1d060d020a0501050a0e04020c01060609080a03080a0908070605010b 77
    0x524940802034602ca403402e00d031384c1c258a982d42c1e9002030b05001801086103030f45580b090030960f07000100340c00c2550113074000c4030165580b96900d108450956009949241e61800c41c042e0b000020300c105084001080d00c081004010031000100134450070f20194215032407103400310032490403480345100304001d0000c01d180560001d2941c03050280c0c40b078050a920b04014820f41c88024101c45104e685413143e070805441c400c859a081903009810001c0c0b508030303413500b11181e80803541c0c6020600002d000d4007000c00924400d11010400c0b94055684000c1044106580c2c00844805915000000e102c8c01c5041000038904e050481d60140c0c42c07500181b0140ba01c91804006480c07981c4000410410040c0c00114110540c03500e0008040d0503e0b07d03000001d40b9482c04200034034019658004481c182c100c00003400209520a000542115600c00c00141484852400300c903544520030005017850300302000041c2c8251440c3c00b501c0e81c2e02d0000a00c408086540058a021110440c0914091300e40c0c0c46089 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 479565152 1250 479563902 479563913
    0xa0f12030309031e05030916050d030804021207181d07031101030b090c0403050f120307140408012309030f120703091407050f0d030f0e0406331407 65
    0x9400302c5019040c0301d5400c4580b4101c0710b0703800e000301d0401d00228000005011707020204002c41a000c40301142c09280a0f4100380c000f6050000504c400740802501c00042025540c80c1815600080c8025003110b00d2145d4801e034801810700700030070070311100b0301d8507201c40e014a9081c032400c055151013401803c011410350799203420402901e28141e0401d81e4480031100541c554a550502524200d012942c40f54039510300b0914201e01c80105900d00d800c01200c0c01a201941c40540380c10120905114000915401d2002c0e010300903588440000e41c24002900d041090600300c1c003c0306144290403a503e5655504615624400e520040700c040c40100482001c03c1440c444282d04442a85800f15a400c41a21850100200d82c0c41d40c0980342c0000804024a10700390304022140401a160192020700302e440240811030485c07008403c1c08000c018080c40c81ea200e904c400054a58600180381250524000b5241003085402d07002d001021171841040c07460040c06081c50844c02500310340e01c0d281da2503841 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 479566402 1250 479565152 479565161
    0x270402090609011805180307110f040204030f0609080d090b0a0c1103040324060b0301140a050d06180212010e06180303070f030f020a08070e0a0503120708041e050a0f120303 76
    0x2081c80b105110031b29441142401e00042004e01d004001c4c005d5036000540420900c40c00801c2c11f6407183c5d03c104401c02c00140d006404030b1039241c00c0100010482c400307050a042e01d1050460703204446140c003030842c040003010084107000c2e40d0451400c0201e407a02c2981503500e0182000040c40c25882880304000041201d041c0040204c2203410740014100c00c1b03091101a2807013034001b0081d690002c0018443c41008503104e0000007000c80750a503265280001044440d94010b6000d0007040d116a140680721a10300c20401c115503000c1c100c0d042c80c0d8100c000700c900900d40740711300c0c0050740501808140c8003107580031403200c1c0340c00700406140746884084044d0744003800c48006806168984c0030099903074600f88081d203240b08640d101c560b01468000704c020080c500c0350040d50b1041c82c8050040c0700701d840020720820340f40e240c042c02507070300d443c0b81c14070b8000c1780034641c041b45880c00458419041c00303128034140f00807181c0c01e071004205c49031144101102c90120b40030f086042500447c012012900c280c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 479567652 1250 479566402 479566411
    0x102100f060819050d050a050a0c0f1a060406170c0904050a0c030c0e1e0103030806040b0913030e030d0c080a140a080402030c03071211270402090609011805 69
    0x80008015a84403442800c3c185041006400ca40c60ba01140c818010284a40c0b0418a1185020ba103420030701e034405417903801040c221004125400210000708041018a40d20482d085000200040340c80411003800380e2046980c03500542c1044000104098158a452401031084c4041c000c0c900c9100f041c48500c541c010416100d44c890042d0f00b402207651704a94034051802041068920f03030800036081e0381d100340981200740303040142464181c3c40b103c10585506695051510980d2030310785400150282682e10b6015920031305100603c689000200e0341544040d1083c1c45d1126500010010140c580203443c8081010803858221900010b648e00d0090084103181d0800c3d500c50540c42800300e40310380060800030089081c0505000541c64200410751107081c0890050200b01d0400301400c180780d00e50f074802001c081c039020600166980d800c00304040342d4055410b402070400c1e0b00c000d01c040183c4c15203090f4050803030403010030329500f080605681a21040703012000500c803e04d9484004000051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 479568902 1250 479567652 479567681
    0xb030a0b0d020d0c03020906101d0a080106080f010c08090303072d080601020609030a0e15040504020f0d18081c0912020a0c0902091c0c0504050f040b0601090302010210 74
    0x24807110069a984034a100030700e010300303144205a07040d4810b000c0d4081000d040325200b4002c0358020924190f10000001201c00c0b200344030060080d140000c241440d019402ca0301c455402d2407408521044000388100304458010000d10158800702801c2d03415101c161051401e81c0c000f040001c1c0c3c0c4c0e601481e0b40a80c1001c01910841308402208800a02c22101c1400d0800103003810302032003e10342e410000300350031050f2400074615001e4180406000c1d2034401202c64003940c4250032000030300c101c0005480041c4400381c425075643c071880c0f036601c0c40c99011962015a01c0d240201c0304103d220402018014503501403201d42c5440071100200302090724581d00c2000b03082d00c512103000040c400c06039041c000000780d0024128020686080410f10106da044103c019105005042241c3d9452006d013034111b8440c4c1306058242e019003003040000c8016002140c120b8100820302c8a200014280d6510582c054032081e4403d807182801190262054403010740103a024060983c61000240e12804906007500e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 479570152 1250 479568902 479568919
    0x7030f150207082736090c190f05090411100207080d0809060705071a0903031602030a0207050402030a0207060905010f0501050a06120f2a0e04060b030a0b 68
    0xc4408505903802140b088511000200c0c410040300405810350080c144034600007880d01102d400844e00300380e258010810140f4134045445440901130644828401080c00310540600d041000156603182c00b480e003034050141407a400000c030f90b409680b2405c3d140751604240a50740fa041c200304c240040034109803035401c15091780c0a40e6903900240c00c104900f41d5005048001c0c83c050f05241005407005946050000d800d0400c428048081541c41d4000b0160034004d440d94507078104000480c005148404805041c0030503c45c1d03082001018522800f0800302c5c500c59070a0741c40040341c81e40204814180507030312800b410f100343c0c03805801079688420561070060404540d62110010380340301d10030540301c59549014080e201e04c0319019150240c1001d5a20340703c2075250a1005015501000328030b01204d6071006013145065072034100c0d5080070607000c4103031503c2e0070402ca00b001c0b5170f017180c6175003001c102c00035a1200c86007450b025600845a03d500b40e20b0550740c805159002404034829240c0d4840c5a1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 479571402 1250 479570152 479570183
    0xc1c1b0b0601200106090f060b070818060309060f060114093a0614010e0a0c02031303030216060816120b061201033003021605030a1101110c07030f 65
    0xa81001d0754400c60300c1c3c0000310b03000d80b0b4404100b04545865680c3d54552381001001c0c072440740034400b1101a42d070722085103a6200000090a5032404603150307060740c33128000040c882c0d01e0304000b03620744c007a0b0f6540c000000c0c2c80c0c4401c0700548600608981c016450641440045002c1c6480c040c41c40305000800c400356016400882018204581c0094503583e20600c0d10000e4103000c0c02e84940603882050704c42c17007030040d4100045203180d1840105220341854580824002c40351083c02a21464002001c1500348c10780c59241c044d407141901800140192446d06001901c0c61081245034010111403900800a000140301200c49203055585405036035240d40800d03c0d9030b00c40400402d0340d089800d80d40b07001941549003440c8400351010020036010204600001d0b403a000480d00b040d8104103040060395036858401003031380464036010180241c00f0108080210b1500b00d1540032803812058004c019415914454050b01e0242400c00c1959070f12000302407001030541d52542003082c0c055110010300c04c05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 479572652 1250 479571402 479571437
    0x20316020f19240c110c100c02090a020403020307121e0c050d0501090c17100e0303060105070213050103051608070e010905100b0703091503050415200c1c1b0b0601 72
    0x3040f0001000070b01112100e0032005006d0015005594044505c40d0007061440390003044205003c901030f2145940c4030209000c001c0c10380c1101c2c0210341c05410b5452050b80c5c1c0000480704014000141d0711a02242000750030b5019884006806503403002d84d40344407a00741010700c9005003134440c04561547da0761910b20040780101542030000c045074480482e45503e0040c0d20750401002202202c5084d0500036135400700140442a20f03404002803804075261491400041d58a00d0010305041c0700d03032301e03080010090240c0071944d401d203901000d401c00082c5903103a121a549210611805607549800790042c800720301e03160050f54002404202e80080241c072101030825540c0309032021030110700201810000f0056254442d9580780b51800c0800952829072141c200d520306416001d40e80c00d0350780f400640200143c00c0116000f9000e898006e4907940e03081f9030703185d540d2184e41409032856111b080d00314000d40f08040e13040c0ca08282250040d5104003594483c1201d50f40640858148080680890308004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 479573902 1250 479572652 479572661
    0x9030c0316080706050c07120201090b0c010605011d0913030201150b09031b011b0302010f020a05131719020102070e240102030306010c11030c04020316020f1924 71
    0x3406003244031032645082c0119140c00c140e54824028004d003403107800030703001d00413a05400f00e40300c00324640045016880100d0754035076290400721801001061035074013a44154890800c4c3c450a80b030780d24540a080c007603003020300300c55400031364440c80d00d03000a541900011a4280341611900001c10811012103044812a04a0b003211a80d150041107042441c13800304a042c950200100d44002e040404000003007501a049604180051420182a040503c01d44c4140c854030348041c011034441c1c1c0d1121004140e90b001403840c0e08020504500886c002500350440444211104000d00f002035090071f1111010301d1411060b410b5005440c0c001170428044400c1c82e12030504060715800640e0400e00043c11007152020721811984203004120150341c00c12180c644031500b000222514401d01000240380c2501a0f4206801c24000b10500c103003402e40754000b8400701c1243e02641d40300c0c144524450f82d15841c003840542c0600306080c10901040c030040d1142811840300785080c608111181c45c100584 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 479575152 1250 479573902 479573923
    0x204030b0c070302010b0103180308040312050a0911151c09060212070201140106022104050607031106090a021509060904150501030b121203060307080a0516050f0d0809030c03 77
    0x4600006020b02059820300c11030003620130034203080080c010701c0d0b41c00b0540c60800510040c2440b110b400440c00745802007281039203011a1100a01c5a8501501500f02400f80c1c1481110030000c0d49005004034a07121a81c103041242203000d80c0d042840600304c0301c0481103105c100082445e030383d030302000c0481e4060005110100d41c6d2040c28070a41400c070700090843e0849200d14503495402401440840c1d400708076201b00e003040000d004181820128010240e103c0c0d640410b90000c00010301c10f08168000d00d4441e08010601c09991441d61240025503c0d09501507000390302065494180c3c80b208000400b405421720050b044a05181e86200450120380c096078014004a410f240100007a69040c050440e811006484541000d000e42da4180d956449150350380d4080c04000c17000510b80d4a081103a400106201000c075042031005081c203075154035000d001d540c0107040e101004940d0b4100008038031029440038194001007400340c0c48a083c0d9800c1402655414010038101e084546d0b4100911050b4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 479576402 1250 479575152 479575171
    0xc10051b04030c0e01080f0c13230103140d0206010506071406070c02090106091a0a031104060f02070e0c0a0809070f0b0c0601080109021c080f0324010504270204030b 73
    0x140c4c28841d9a60b28404168080d03c0d455101c6442c0c4000d6500200e421101050242d4030340c49141c0c0d034056100090080d40c0b80856489108450041c210400c140000d41224000c040f0103180c0b0071110115911080007658040c0541e02c10801040f40d81043c1c0c0050600f140600c0401480d1103512854600707180d0162544000108403030011019840e019290364010040b80c10000d06d49403906401c03052a54441c03180784107041001c111200910f0094020260304000c07204200d0340c0e10348411001d80a170862601c440f005100b150400b19545a11101c580c1c02104c1180d0020b0800303000030811204020018031031005c6000d01c150020342400b0702201c079030240c04440b00c1d081c1c4961102400d2450818142d10440c2180e0400c90309002585501e0110161150003a902d03540d410b03018180000c1c0e40c403e148052641c1e17039000041101c1c16421946942c003404460080b403035a0f030580c0b001194107004900480321180c140c051000c00ca4884d42800303415a6181d14400350500ea6240c0724044a6102100d28684 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 479577652 1250 479576402 479576423
    0x31e1e010c020705100e090a0e030a050c16120615080706030b040b06041a0d0b0d0c0305210d240303260f010302061c0507020c030f01020c10051b0403 66
    0x1a035030140000c3e8040d110a803040441030842010041c64414200d50041c01130481e800403428003000c507001100030440b12401c69548270505540105141d201d0002003500b03010b030038920f010f510700e0941124119083d061103484049019200c903c018044c510b01000580d90700c110000d01090180000c0c00101640d44001544590080a22007512103032000300340b01b444108002d02c20016860407104441301409011030301c43d00940d00410092111221084d80004415010010403100c4494601130364440e80c192903a908441d11841a195605212040c411506000207120001c503503210007a0700c1c40401c1803101040034079140d000e0150054000303900041030010140c4110070680b484100c3e01c1841c010000203403074102d01c07110340c0b02c40600000384102c030009100003814070f05081121101441560070069030800301400303075548441d0b28080e80207020306003500744040010f10030f4a6902050b9009031001580c0a6402c000600c0c000380007150019000007070822180108003e00301462140b4003114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 479578902 1250 479577652 479577671
    0x31d0601050111061b0a05160807060f05040b240901080106030b0108070b1905070605090a150207080d050402060c0a050f0606120d080709150302040302040b060405031e1e01 76
    0x10f161140001c2c441443c0e60101090285140d6404580011030707440580c5982c84080d04a070403555031069402c20100702c21515180d00600039210003e19035103205480070401c0c200c40c980c0c200306403502102c000d807070f260304000080ca40c040c12640340c642e018181d9407a000111110800110400e034280c20080301d903956580144200700c09030f042903002d0070f0000c00410000d841c042d14059240704514014940d00c100b5080d03d8150340c091025115240d40c4200180401e1502c900420b964031002d0f102550f42510911394031404034654801c079100581c0061a0300d240c02e15000100015000c0a0310407a008001005030303041c3c0150510070301c841c0500c41d01c050202e03140c00f02c260625103500500030501c151907540c0b041f41d088000042c503111144407814422051b40d10380340107a0f81015668007408004a082c51290100ca515500610999200b140c0811070a00002d0911041d4050b6000b1540c02d6803201001d0107148a83c000540440c0e03c102003298005441e04d41580744103c1b48624603001691a003065a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 479580152 1250 479578902 479578907
    0xc030a0f1104110301180f0608010b24040b210405030403140d0507060b030f1609050c03040209060904080d15061b0506130c0e0705070b0f09120a031d06010501 70
    0x1001101c808842c28403103140f042c2000240c9101c10312480c3c1c00c1c9010303005940c9104140c0d40250116070000c1c0d00c1000195076407411140a01040203580d8801c0155581240d1681c40c815108000203400c115201d00b41800e00c002c039410350303214104100086034240c0324000c0302c003000f85110b40f0440c1311300040c6494524500d0b20304120303081501c1c02052a009250001c41c196445016115440c1e0400d1010031003928a00c00f083c1041d00e120380d5001c042c01030f03030058004c03c07800144210440d02d400000f0045a90348045500c0540002d4600079802600d07803010424510b490b83c0010f81241c0101c074250300d0942074610b41022203029039a901c03401c031900701c020000d0540282240714202c207030401d513014185895455544403c0000c140c035003100c01180701c000c103011403144618058404c0321482a00c50800100c040c00c039030030001044400300a04000100d90310310081c5c6107400b422045005060b98500c44c0d40a80e000e411400240f400c040e03507085108048001410300d02240c030b0070007014200650420000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 479581402 1250 479580152 479580173
    0x2a02030d02210a0b010206040b0a091208090f03030613020304020307090911010e0306040f2d060b09061c11130507030902010210020717090d080a03020c1006060503070309050c030a0f 80
    0x35803c1e0901c1c140360b0200320398000c41c0555205910000030015696a898150000c0c070b800c0c034019048a2041c00501541030700b0111140c0500d100400302d449803102104102d5a81c0310465040782c011040085400e0741c40a00d80203150814402400e80c1d901c00c3e03d0706000804c8801841068464000c0000382c040b16503007080c032002d07480b50f0680240815103480c0c0ca800401c1c8550500c014050010f246403d203189003000c0000300400101d41d02004181807904002005d8280e01c100e0074820500c80002c1882841c000308222040158524617119145e51a00e610031507419400c1d43c1038001050b280d02d0302501c0e000344a520b100311a0ba4800281803d807034000289099020142c13002500d1040080901082c0940300312828608030103040c0340e8810340b220102d560320441b40d5000348000d00c00304a41c0040e64150b0083d28152100340211198440c81d80f443d0350030f944041c812080403403020800b144840748240c10490109000300c0031200220340c56404646020440c0c0c50a64850038040c001504024043c540b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 479582652 1250 479581402 479581411
    0x405011e09030c150b06120a0606090f1e090c120c08091504060e06040b01140d11060705011b05071a0f070c0302010e150103020907032a02030d0221 65
    0x2080074007196a8007070710715103590310003a00400700040021600c10a98102002110303014007441d0719080754401c0c5600c00711080c1c0703c207940a82000c0002c10f071b843c407558400e000c85117850078075443d80b4a00301c0340241a180702c08650707050064030b54001c0303610740c1c0c0341c002c0c1d8810340070030f544e0341c01d5182c070300c0304550704a6030610300e06004c0049a105020241c81d000032101d0004254081c800f410307880310f1411030001c2883d8642082071340900800c10040c041d01d00c484034129001c41c0032182c41d8071400d00c104000e09400b4803006051103c0341d40c06841600300000540219449080005100e5021905c400045036020ba1030b0000214001000020040c3c80101d202e01071418400d081d0041c01c0215400740f82e030344000c1c002c0c42040416852103043c14404d403c05854503030b1400580340340d10505a0846a410303000d020903800b5008140108504910a108010340070304d05d9500028041945202094101c2e2f0328620001184001d0203a040c003500da070b10044c03071905c031026050318402030311700c1d020100074034000d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 479583902 1250 479582652 479582711
    0x8070605070c200102070f08010204030b09161a070b040c18151401051c02090f01020a0c15020a05060108100b01050412020105070804090e0609011802280e040501 71
    0x103911800282603600584840c0c03103c84056031100c0791500100e00e040308552048111140d09100041d040c0740660013481528000c20510440c1d5071003181c1e05650300d058a012441701c0c004a00204440001228994640700ea10309000e4039005041c1c5030090980c0d000d69050b01d2450b40244100014104a911040554802d103811b02c800036180358040c0105840b0b01c181000301505528028440e07208008803000544403070703400030000c0760500c00c0d00c2c000d41014961600840d02c0c030890103101d60002078890786541e03000c1e140103105410301c00008003c83c0026001015172140840ca40002001070114034003034083d81009002ca000d14242409c20f90300900c0f030403414400f04100600c00071000000906903190282410fa90f15055460050355030710899109000080c601505000000008503580380625840c85c000d00c220441c0700c40910b600340e0301032002035105a4001d1146460301c5c0001d50003142e200f0045445281940d20070b0610b400c194100c4044946954035581c1c13240341160302c4500c0040c2d00714803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 479585152 1250 479583902 479583917
    0x91e060219051f06050607030509010201060e1927030809100e0303010911120c0901080105060306010504030b0411090408070303050c180103020714010f06080f0a1119050d0807060507 80
    0x2e440d41600c0b80c441d40c1c03c9219520183c6202c0c110101c00d50440700041c20040c00303aa81d40d01840c20010960f4104045160040d405d0410000c1c0c0e180c00f43d1025402110080400740c40c0040c0302100c10001d0811003003120413503000ca280000b408003000c008e00000c5000340c6030405246003142c165414041d406914000d2149424514041200000141e9040d00c24890f030008450300210700660f9180504a070369070361040301c01d0802c03400c041010007410b40c0c48001e8170ba0000d1642ca034001c1000b5404101c40c03541c00101d003444204041a1724a03000740d0000d0242c00b1a800301c042290104110600c110745c155140d0000040c802c0c101641031141030380c00300c5c0b801c4450741080840e41900c044a07044000840c105a00481c03440c0c10b000040303541e4801075081d00020800c030001d03144004060006445002c405018201720314510510114406082a0780000c05549126410003004604100231502402519582d00c1c041641e0b290103030410002801041e07201c5c0c03500c419203003050903a40024903240810004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 479586402 1250 479585152 479585203
    0x1081e0a0515090f100b010e030a0321020702030102070609030f020703030e012607020f010e01020c0303070318050102120f0a14012606010f0602010b0a0b1801091e0602 74
    0x12030b008070b403502c66142490b419219030141c00d141c0010412104d100307014001180595410f00ea00c40081081c084e00c94900d20083d500405403503414103d00035012800ca461003640c441c00c030b02d50511081d42104c2005040c540d094021a0032600001802c450444e07584841030300f0b0541000000540c4041c5d0f10003443c4043c01c0d81e41c0240064001c0e01400c0c1030201c00c47c0f1044446464420700440c0f05040e4190080300d00d00550002d55070258550712070700c04d510780203c81d100301c0c2c8107008541080c035441005620710b4451440031001400a41080103116200210380d0780050b200b230000700400c0282c103d030a104c9041c81c280a8442c15000350500411500d81640d03a10020041c0d403407241142d52004034004400035034021219801040081200c9600901001042102101410307209555452740204040d820300d6042c4031824500780111018004148114003034001501c040004204045c034150070055901d41340d0b05240603c5911210542359211010711407503038100040c081c0161014400e680101e42e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 479587652 1250 479586402 479586413
    0x606090c040603200a0c03080601090e16021e011a040902030d18210c140303030a0c0212030703020306030f07061b0c05060a08090c0409080423060301081e0a 69
    0x7984141c02c141030300c1c0c1d0101ca140c1900425044250080d01840c143c0d551a4040010702d91200480e0440104801d8800700d0b403154403034803030706080e10484904010182c5503221a1202e0070510740c00b550440c401e044004000207103503004a201e04505100116040b4050103a60a240b0039041c0d04a00613490801c031403025070341c002044040c040c4641841c8040f400c0b0201007281a0074950020701c4d11003103202203198440c8a196500902600455014414540715035640c3d04001c80003880c568143d00038404a151106554050720705410140100c4026030180180c000968100311007000100f6404010400242000c0c40611083c1c00040043c14400b414800003611440c001c101408412a2010072582005020b62081018020042459132124101c4a00800000088070303084003500520300219668109401484a0158403950180c202400d00c038518180e500000b10222240034035040c50515074698200070344c0a0310680c005807010120700100d020201c2c1981001c84415030107a000741d000b152 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 479588902 1250 479587652 479587657
    0x1309020a08070f0e09070509120304030203210d0609020406020d030b090123300f0309090405031303060e0f0c0a12053301081906110d0e07080606090c 66
    0x106075040c48410f061a480c3e0071035403135030709840442c4c02006450a02c05455003110191a809008941d050907900700140556201c0c0a540700c001c0d0190f1208144540032580043d545161144c1d51401500b800910509001550440e034008604658006000e001c9a94144002c015a03903040c1820f008002c8000081104004144500040b503608000070b28001c82c11000b00460941008000e000c207010100354181c0514100c030039450844003098002ca00c0d09a0101c1d00c851030002c641d001e542050803c000380907003000018030450f6640420840041211002842000a0360144000081c4140c030740400c41d18003144804d003a91182c1c00082c540b07203a942c90150280c1038440c600c016000448007071400307a1500500d1403040840c40b9460000d2148004107018140182c1050700d501c01c030341c0c0da0340d610b11a200c00740d190400400001c0c4d03601c20404241240c1042096503031002d5440e15045c0703004402006c80d401c10080204c01e0700469010480c043d010070040d90004002c070b50030300050030032002004051 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 479590152 1250 479588902 479588911
    0x20c0705040f06120507090e070f060f03061d0603120906041e080604060b130207050c1002070816090b01021906200705011e0e0a020d05030d0c051309020a08 69
    0x898507080b141d2000d5039190000b60007005008400195001c3e00e20344a62501501c4c00340e1000781d031600301d0a050503100014014200c2d0980c00400d00f0306401c2050803283c60320b00c211080140f6480321000100800003581e001c002c1d440c005c08010b11400c10300300f010700700988a00ca002c118002842711031259980c101c101da0845410410b9400c104000c0103c2d0501d181c040c0e4003104550150008200034001a50404d888668086a0881480c0400d640000c102d005140d009801035010016250841c100440490241041030044520b070980c1e800309280b401c01d0103210356a038129012000c00c40104140a6480c040c982400034140d44104201d03d4080030384140009060f1946840300b0040e4042c212481120748003000080a0f6101c0301820440d0280c404400600e84980c0b80b1101c4e0410100c80c0d00c580000b502000000e050f03118500c0d005c011215905c03a40c1501c0a010802c040800015184169203035400030351501915940d18000c45a84540181d212009107401001921080c660058107161302 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 479591402 1250 479590152 479590159
    0x60306030d21060b0d1b0c02010318080f0a03050603012f0903010f0e1009110f03100504030e0102070b040e010e09100e0c0a09090807020f220b13020c0705 68
    0x2030200d45140e03420b01c5054021440c03801440e0480208402643c48000e10440c40010340c20320030600700318441030760b80d20311004403000600c02c064001c0043d032194105102c58405104d025000d8071550703d4606040e8040c08600c4241400010f000180c2038242c000c0c20b43c0400d04400070411f420021190404a0f290714111165020300050b513001c425000c441907031403401c0302030300070049100950a600d00405980041483c14401c0f182c0006010b0014003841c5422503200780042c0503110a07000340005510b5104005038035002d0031000f081c101c4411711a09108901a0351425200e041c010000780c1041d5550b0081400340b6800c02060100200468002d811600da4904500b02581d508001e80d0400364000f40e1200e4150911011009841002420002c08070040700c008000d90b94500404003201e04840d001841a08140600c901501e41814801c1c0d4010000c0c04505060034455540e0a07100d849001e642c4079a0ba854482ea009401c0060a902103400c1500341186003180c180c200c42d0341d820381481420310 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 479592652 1250 479591402 479591417
    0x160303030b13110304230a020f0604081b0a0605160305030a060302030f0109050c01030b18150918010612030804170f040609140d0c03060f0b060324060306030d 70
    0x12520b031441c1a150031400c0000422412103032000403201a4419507055444400d40800c00304401280a11901d0b02c3d1351640c007c207a900155402e00c9070031002c0303140c4503a0040c002d1000091100c024000f080344001c000060781e0480340c0340006c0211a40b03040d002082040f0301407110450149240c81440e220316014284262240e44e059240000780a09410094150003100333405d441400b81500a18110742c401c1095450440e9188011400c4546040006620084203045400e496402d01002608400320303e88060161111002180441c8002d17103c10410004007042c45e0a450028440c0341e01404850322a01445d0203a511b00801c25000544040d0540c40c1080000003001c800400303ca4040c0c0e48111001d440341e507202c001404061481c440d40d20112618030340c891851400348280d1050b40c1d8009071010103d030858607610010300c01d00c44502c0e481130395009000e00a603200000780d881a2a118120350300c0d10f40c0c8a070741d02c1e01c21000c0b000c07080c0101010b000780b00c2c45035000b1030300405c083c40c41e261000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 479593902 1250 479592652 479592671
    0x2030115021f1107020a06020c03011b050405010c0c050d03020d021209091609091a01080117030717040503120901021501140607080f1306090b0c030d020307182616030303 75
    0x82c1da0b446861300081d400140c038900010a0340c0c01095101d04550124000c00c151850361842c452b140010011420000368100810b05c41580213814240300117000b11303246002d541c0c44801040c60400248420340140c1d005030071492805904000080740c4880d000046401e044040006c241c281038003900c1170841100c080c40c41d80d00b191041400100070019030b5020311007002c6c0c20603c091668044002c00d070000e520000003250803400842c0541044134580f000b0752500480d62289407140784041000c12203690204030010f2507aa08204403101040c1107a0306540e9a41d03440c001901c1c10303202c3d40e1080003034414000100040300c16a00c100440d035205441d0300d07548441d14503104900344504092172042d1b00d804100c91036004a41d840309800d50742d0320703107034516070644588802203d4062820000480d500800064408621580223190031022a040468062161040c0103030510b0311a001003d2125000d059440310b009035a14202c4280c00c480b02030111050b10700354034403104090b0300015052603182c00015 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 479595152 1250 479593902 479593931
    0x309060d0b0307180b0102030301050310561f12060305070e0c0708031b04030506040b06030d09061d060421020f040c08040b101802030115021f 63
    0x2a04203a002819034420584036030020710030380c803034400e410740c81880c1017902081135000104584c140c600080c001c02085084030043d00282c0100d0701040000c9545100c5c040c422000c00490304a000452241382814081c1c107215001501d218017000400c1035001c880c203000684401d42040e019161140c0e908070081c00500c2e082e0f42d03040c800c8205c060400c4c5401800420322201254401c140c42090100845c0c6031105001a94140a420000380a12070200007003a4184030400204590402d141000c03814180d40340c0b1460b083c0801120252407022050041240f20b207001d00c0500c43e0000304d410002941401c100004088684001c0910140001191241c3c95036403079030241c0d030080100d0803050040b009110b1003d0642c15101100320b010b090448250704e145c2c50640a813400e110700300e50310201248e0b616202d940403094082c100948900b104407001c11810301c043ea100e041c252030100c0150b5070f075140c4660b0b41c2244040390740d9042107402c820420b0514158070034400765150f00d0000003041040310807001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 479596402 1250 479595152 479595161
    0x80607030c0e010c0f170d0915060f1202041d0616020304060207091d1207110603061e010e06031302030601080708060c220906032102060a110706062607080309060d 72
    0x1c0400c04100407641f030410100d550010f800040c802c00303400c0c4103400c0145003501035a110740912049051031075010720607005569803901f02a400104082940290000c1e00c20119801d00c88404164000e0341c00c000f00c5010305007140712a04100e200035460580f1f4003c000f900c03800c0d14000d010507652582c814007a20b0345401c803194140d81182c1d003030351500c0041c03001454a590012400719050301c048101a212440d011054900c81d0718040c0c005627010044004c45c406100036008214180300c0c3c0e600e003400c0291980c4028608c5120345900002c1e0821160041600c0c03d40160f20001460f0700010090010034804580142c10410680100e44c46400310760400740141c0c08200d08030218076024100040180c1260413000c1100d004d0101d000003090b10035507244000111000c9180560b0088010480e040425440034551044551296090562030b41e00c4201344e410691161400703640041000000790808a501e0144c07042a00091540034a4480c446d17850303001e0b1a41c010712507040440d0b84c0c40e0804c440d800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 479597652 1250 479596402 479596433
    0xc1b010f0513080607050a170402010504050d021908061e040804050909030708120a0c0c030c02060d06030501050f0a0c050a091a0f160c0b04050a09020d06050a080607030c0e010c0f 79
    0x1039900e0f0f171505600040c41a04011100c0000480b00c00b440e203415001e8050080c010b540694507136152505100c20321170803241c602d00c101e8103c5c038412060213007004031580b280e001e404083e024003454201811040c00441e48203500903200e101c107600303000000d107002040302c1c100c4006550194150743d443c0c00ca60304501a860018000000015500b502ca201d802da085106401c0b07100d08001c0200499403c6820103240100100401c242d860745d4005443d0490280240075844407002c200c03583c49645e400d003036a4003665180704400a11007800b02401c200c0c00f030100f403d45240f41a50a100701e2800080c0004407511481001410590011100340d00d03110440e000652408151541e86410041c0c04820448120341560903212030000424048a0b080864080300e80081c0144005814102044000c2d4071072000d41c0c2406a03954400520368885c4580000144400c001030007551800340005021b46600681020410540c803031000700c0e682e000154890411f400c0900d0314803456161606600c4c0c508140d0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 479598902 1250 479597652 479597669
    0xb01050408030d020306090f2e05060a02100c170c07051e060618010b0409020318070602150a020f04061808060c040314030a050301120501020f0307050c1b010f0513 72
    0xc20b4001010f0315001540540800da407803256640e500541d012840d0001d84103040d81c9941d00a0f680c4c40a11941c0c0c8584410841190010a0b507980300c0c001411a44a9440302c0056042260410100303c4244101034100d0120b0804001c0e203003261203240d181010040019010880c0132580701d0601c401001045845a4000d00d024a21080181030715554001103404504c101d05000d05840000440350312141240c41607d040c50410b800d00c5c484c0c034085d4100401d410900300c0c6e004140d52041100304009001866160003a0004060642481d0201e140090100b43d2060040082c4074601c185001150121107891502035204441041c0060700b000300c0c0d610a100510070078043c001034400880040c0226032150340c10b610304010183da0140c80340110cc205401107101480104070740e4500c1c00310f40c00424440e80c00180b80c00750600c580fa0071600152070030b40006001090300e007100d201c1009403503510000031743c101c2c080b6620080000c00e0501200e0304c40d002c20001240346070036082484500c001814029 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 479600152 1250 479598902 479598907
    0x40c0308070b0109180506160c0203060a052e0b071a09010507020c0a030c06180b03070c020109080307120e0315010321080f0c280207031103011109040b0105040803 72
    0x505107040c0302c1100380901e15225161814400540c1c4280d803035680100e0380200500003507a00d010b40b4185503004046c006080c1700664000c140140c0e4184802482183e99160000d51805c04007012500780c1401b0004500d000d0720400180d5024201526900c101d41d42c400b9015178550582c50328080348952001c0506504000000740820001706411042c4102d8040d402c840344a00c000b0200105c16403c0d100281c018610748100703000c0c45128448001000020b03041c0301040ca0f80e01c034142ca21a0340110340281c002106031084900b15070380104260002d019650065080044640320056621642403d40081c403d0307000000b4420780301804100c2c415200c00285003003a680d20300381034881041208428801c600344d9080c25444502812100d400703107180d1101d110907682e52501c2055942e0042420340529002d07000723441b101d12440071a516051546902805806103103140092402c980703096003500c242d04021105808080d0340b800c0c0c6480e13500c1244d02045090365000181c0c2c191250340c01c06002030000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 479601402 1250 479600152 479600167
    0x1e1c0b0d0f030f02010c0905132a0206150103060e060d0314040605090f1801030303050705070b09030a02010e030309031611031e1203061f21091a160503040c0308 71
    0x4103000c4490a221500241b00081640008407549080d5002c0d55521208950490903051110307440083c1e0804904454050f0080d40c4022928181c000c950b4000142d20174000c201403901d41e102020320180080c00c00780082800c00e20030300f0740100010040740c09800070f5902c4405040c0328806141282d45d09021040d0360f03945400000b0010ba2140c200b080c010000d4512202442c1080d2030194850044541000840d07400d40e0740c1200900306c05001d11080200502100c804200c100b00e050b8082da000000855803680c0340d201c048d0035103240e01c004281c1c5400034010407038400360102c21030b00c003030351101101241c1c555246021130510b6039030f0102d40d4051107000500f5150900c0c0704207940004468504480841d00b0040c5403002c2c1c0c2c401110b0307442d0400710042d640c5481d20b000c1c011001801e10f442c103013940002c004180d0525040340d000305440202342c888002a00f44041c980184810b03084010b129041da00d410f8840340c006420101c0740004000c0000300140500582e402d120740550741c886202d590700c220 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 479602652 1250 479601402 479601407
    0x8150307051e04061208040e0a0608060c03090105090c031f11040f0303180501020c06030612010c050a1b0b0f09030409290103021c2f1e1c0b0d0f03 65
    0x40c0c1da5164001e1313283c003802003518034115110141c036551181c0228501030401100c842c0711000908820f40c16501ca040c0400c0d0640c09101c2c0074407804206200781d0700c0703252159030b450945601416000498000c4c0310004181d860104131015038a1070500c00000c8102d101c00c01c04014007801c0005444103002260100301c04028a02d030a04490081c0c0d103030640180344160103554034802c2e10940e0b02503071005401068a04141001c1d5502001c010501c1201211889100f825100d1034642d4800040c400111080c4860300007660541c24000011080b4090710540e54034a07040c00007a020001260f50f1a00044410608004842c0905401c03281030118448007030019822126000c410801200400d2509510394841d20958040d040590541078012440030040c4008214040b0040c40390300c0603800c0c40c043d503171844e819214100741d117001060f6540641800c4100301d82c542041d00e001ea91081202841e0000113000520300301e450140002994902030001400c1107154900c020045906a480f6106054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 479603902 1250 479602652 479602699
    0x2109180411010816030504061b0207030b0114030604060209030a0f0c18020306060315040f020a12060e0c0307121e0509010509070b0d18060e070314010c0815030705 72
    0x1d00c1650041428204800151070700c00c01200c0002c0c514642e4406281458469000b081e0440d0144000040c1781c005a00e1400180780300d00300c540090313401504200204114480300c0d90041003406981c1c0b150481c90800244c84034006000a07104a40100c1c188030543c0d004e000100e403503076002403100d20021551410380e41609103071040b01801e00c805c00b10314010315120700071030b03124a500909891a40d503404e0b0a50388240880d190140c0c1142c0d82d41d00200c070345407040c801031240c41c4445c0c40d601c00268266480c58140c0c3c1594010201100c84081400903030080704d0250381c1c00ca400350500e802200b040c0410074005211a0072040038840852203001842c050542c001c6005999040080c0700310703079070102103640c0c070b00741c920070405000c20401800c1c1c8180402e0340310201500c60350414074114181a103c060a81d01c3da5070811400740c108aa00704200948016800ca15958810090060900800024012035001400c03214142e04c504003d04403560f00b0f10041c806040f00514130300344207800c50b00c85080c0d403 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 479605152 1250 479603902 479603911
    0x9090813150206150108040b09072106110702061b0a0b15010206130830040302010b18070e0f0d050a05010b03010606020a0c21060e0d080612210918 65
    0x500401000c1103e41c0404094181c1004c01a11080d60a8889980310444410000c10006241c028034038045402c070007420740311000c4c0001d02024000b2050b40c0c2003c0040b45d250210544480c80c08004500058540c8429260502118111641c0269450219038241411440005d00680c50340b030421610b840103500b84039402c0401c0e4210340c03555888003070701001c00d0031481e0041c00d0b06400348003030040402410842c04c0100f280c00210961120041006e440720481030b60300710301503511994689801d0070042c040c0c0e174010401c0d00e0203a9580c01c0143c0050540034140c498a4000d03002840c041d60191150b61890700e203590301104a070311020160a003076008200c01c0e131219100e5401e0120006840384009030b6040c070b89400440000403145428101842486043c104070031000d241d440344c0d03001c20603034851030b084d040060002c0c0011481d841d00040030040020072180c402e000328140b0640446001400360002440c542c002c403420000740c01c1e000002c4c020ba200d04c541c0101000300a0008044403144503028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 479606402 1250 479605152 479605157
    0x22030212040906090605030606011d010201090b18060f10030f030e09130b010503070305120706060503030406030e0715020c0d061e090512090d030e0604090c05090a080f03040909081315 81
    0x2176a00c0f441096260401030381e80c00c0c0010841c1c0d680b242c010000d031241d010f242038140000103d44550ba0f5413490b61400480315240803d460940d640d5400d0f406024007540400c48850441541c9031a0100142960040c00064050f1400b495007001b0503025100d542200f5000900304406071074501c0c412065000da1134800c594508000d4000121410002100803d49500c100a041d121010f500e0200260704220401d0310320300e490708400119510288020009051540c3d800f01d122206100ea0615054090303001d40c4041da01215240e882c00e9010610351071040c0300f01c1d070300b0700030a2482c148040a003925041c061044004920401d82c080080d41c042c02001d44144240d81c10810b07000c250030458010a22610b41103024144a4000a48103902c02c0c201a81c008010300d00302034031594100212820804032300041000003070780e09102c3c60b001040e00d00400d00b24000f050100d04c800300e282d031280500d11600200c40e841e52007006c10001c00b142070359501407000d200804520350764110b280b02d118500700018003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 479607652 1250 479606402 479606411
    0x150f0207030905010e01122a020307060b09040c05010305041109100302090a0b01140d06230f0a1a0c0a142508060f07031b03050115082203021204090609 67
    0x3e4a501440b01c00048078416110708180702441c102620180426003804030b0842c100440d80d031507070060081c0f5404044501c1d801180c4405003450301c5000c50300d04070600c500c02d40500301008002100c44c40d401050395820f10b070100b41a00c40745040c1c030020340b8558a1981c000c02c4070080008580c0300e10020000c0300c1c001c03581c1d00c041c0d4030f801eaa9407007180e1805800c0b50014500c00307500c10451a0703207402026003000701880000e2840e6208000d003c2c0050343c06a404803003440340201022464100078107951300104441d8260050300d0075500c001c0342c45000046801c10030000c11180035084041c031640420b15000440c0407205040382140f140c41e032108142e0008102802514840e401c0301c51400202502d83c90802442c42c2e446005a05006140003841c2d601019102c81d584101c80d9032181644182c82000d84020445504202641646401003401c502c02c10056000700b212440200c000300360601c0e15015809100761290900301e08082a100c0400c0c2d00000006001403188015449079048840c1880b0420 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 479608902 1250 479607652 479607659
    0x3051608130b0f0301120f0b0a05040b0a0509061515041205010c0f020a030302030c0f070f1e050304050d030e09011805010b1c0b01050c070308120f040b0112150f02070309 75
    0xb5490050f2a07480c01d91003014001844400017140040202e41c2c09012640c2ea81c00d015910558189012140c442340c0540f180280000c201120a01540000d0341d0002440140b0780419000e0b82d03404003c00305170646003484451213198035800c080d0144665862010f07583e450301c2c0e06401030030010110040711550700c0c003002601018841c030000c0d09400580c2e0301401901c20642c6040740650000f8090310300701001003000c0598001c24100805165101c1ca800382c283d402d007410b0060000d6441e148140070400f2400d52940042c20100c211000d03100f0442e81203c4000c0c2c14102142ca00e50703141462a04069030900106000500422044103100b0000341403001d0780e03c44180400b6806414207482c0d01c0d510303500e100444c110720b54101906001041c902903051421803010b10789001c0041d40290303a900c0d000100f051018001e04011988001036164003107031401c0558032507040c88814070a80c2c100f40031b00850841000701c200e0000321000311010061207590301000c02d60002398041d20084000c9024442d000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 479610152 1250 479608902 479608919
    0xa030b030d021c050a051204030c14061b0f0702030a0c090b150d0c140d060e01050621071107030c060f0206090c0402091c1109010b071e0305160813 65
    0x154400d5500f05500072064040311090701c968012034199018408207001c3d0210f15000a68150f00c281c0c00790341c41c0400d900040c01c000000e4640158040800c0d0418010003d42c8071404800c0240c84820101481d034443c110b64000c0b41d540901c48000391701d07020780303140401404042d18401e029030b080904208110300b050401c100390110061a034001800041c000f2100e0551076a22104107202141400301002c05032019900e0250b00c0403c40f4104030f9a52242403217400300c540002d50240405651702803a2050781c050381c00c90f040c0e10340b690442d00c2d81c5c4080001d650368030500c410044a000c0308110b030307605c980741e14203041c24500500074000040c0300d940c128000c0da8400620f6500800110014000814451007400003039882100142d80224603104103840e14510111408601c9008032404a004d0301c92104004c1e0a150607400302d40302000a01010000c40c00c0303542409034110b0202040303144c844440c038007070b24140500e0041c0c0e8420390103240c58005104551004141d00d1080142e4110107c0d2603e601 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 479611402 1250 479610152 479610163
    0x3110909070324090c06021c08060a051005070c0305010615031b0f020f120909010501020706020c0d030c020607050c13020406020c0d02030f1207050d0309020f04050a0b03030a030b030d02 82
    0x251543c0303594400c0c0c0c200c015541c1030160000100c61404282c0c01c240343c483c0003000d00c0b40c2d80710b000180d0201030100c00c0c91400700c0c2062520400d501d404141170401600080811038180605441045207c20442e0710700e0196044805d40c55015070303002c0c11280c2d6030401600a0110707208960180c04640f054030389061081c8a0000010307802c01508004940601c4c08488a06584040c00d00f07520a048010141c4141000949410105a20030a64400e908401d224608106038000d40c15035010300004c2c04026000300d256074107400c05403104400340141e801c003100c21550181d8040e41201c4d0015040081c42400b042680004206a50041b90300130700501d2203040b48164403074000160410511403042d03103080310852000301e0004007111800c0f00303605441c5092132803825410000440000e2144200901445002503114050404006400454020030042a11001c449100380e54030f00008004080c0750b40400d41d112005011a502c1d440b040303101900401080c40d00038480d02c43c0f911b81c280e0103880000c4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 479612652 1250 479611402 479611409
    0x20901051e090d0f0203070803030403050a08070c0c060f03140115032309060711030715020a1e03021201091503143d050c04050f0d0204060311090907 66
    0x12500c1c50409100c074281d40d840710721900c030300d0340a104100c800b01c2550344121403040507005059448a40356a4810140f8040c2030785d00044580c0c20900030040801d401005684004205041c0800b1594a510b01250064180ca00082035290900710215a460b41b0140d842101c142a881c10041c0207464124000c1c41c403001d03c00c0340e01c00c50762a01c0400c00644260400c041548100340102c03410910207500c0b80c003c45040315640a0f030b40c40310302005280daa214241c1c1421071041c0010314505555910760300182c644e8064484042500010340d00b040c9403040c0c9103080128448447d641440c0402e105c000c2c040e5101c0192039459034013000c000301d0b145100d4860b1941c0900040b41e02e121003441c0d0790720a2b0122603400b1380c07503440303004141880511003a05148202100d180d2104c440114040041d4000c0000c80c5d84d20305180f0314030740010800008400c00c212000e69004403520a1005540c10000b045d03400f4400b0b0081d0082c2c103001c000001c202c0c55558131040324030201c1d50000540e0f560524695201074a21 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 479613902 1250 479612652 479612657
    0xa0e10030e0d1119030309060e0c03120c0d0c0f0b040309050102010606050f071e0b10030b0a0b01170a060f0e0a0608030703020a03051305030307210e0d060c02031e090a09020901 78
    0x401040b02c0c0c1d456a11310000c2a10a080c00304001c111038940b07504884c3c960440400030380017542c00c00e0191406111521260000703c445504020340c1038049940c44d090a480c4000380004e43e50030b1018001107105140c03103590301080546091400341b6005000e4165880745070301541c241a00407038401e0140042d100c1210464a04d203003004426100d0bd00c3c80c0080d20001190005401e0184010030f26040c0b032a8403136610300c2c1d00324000394913601d80524084001400403444a181c0001150030b680c1c0580703040400705440da80310056465070904103005102613407100c18030050011000a04240d4100c0040c072584a00a080141d20307940c4507402d40b42d22416000030010b03040321041c000064000d8005e0300c0c141a041448040050321a008071b03217158050202558005c04455031005913800160303885101c06814940f080082e264240840c480701291300703006200d02c3e151010101c60a101b0001d03100c82c2469099401c07500084400380000d2680801980c034003d804030500450700c404c183c000c9801d4900180e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 479615152 1250 479613902 479613913
    0x4030e12100606260723030603071406090121021b0609061909080d050406090c050312040b071b0b03010e241c06062c01030b0601050a0e10030e0d11 65
    0x580aa02c1c03540041c036480501241c00c1d95022046e492889600c000c0110b400503594a0604000701840d1040035400006014040c071032030402c6840350029a034001c00d0a00345800640443c001002044011041030b90404d4404190b002584d0610803600c90004010000c0d2551764842807140c50300d84000301d80d11000042d4030b00012181440036400910310f107001e840342604284912a1610582e942070310247c800766102c3c070013403043c040b0900c202001040200c00030403500003441155a170303a0055201d440b0884501080303204c1403040501d98080c0091102d900c0c04201034644500443d2034000f8010103d0f01301c448800141c1ca90451594a003140100f9064001c2c43d0615201300b02a07102c00303603004c1c0030608850f14040c000076264010580030304015080000311480f84108001c3d004090001c1400d860004801000400c410030f003419000103003840e1003542e45800620130350b256041450380d15008000007030700c50581d42d8564882035a41c604181650b030f144070511401c44400c001c0c072140d201b9a8201 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 479616402 1250 479615152 479615207
    0x105131a041a090903070b0123060301030b010e13020f04020a030204030c0e1807140f030307170d0b0d020612040804030c0b0a09152f1009210503040b04030e12100606 73
    0xf803450094a82020306009c840c2c0351030000480d0007a0402c2e4401c41c0e0440f481001403103890940341c0c2040c2d02c10300f040042d07407900c4250b0b0001800384065061050003181c0c0003d01050161207501280c0c06990441d442000f81e0350390b8008044202c6040703076030b2080207030280402c145843c80032034140300b210b00903400e01c03039500ca050301000a03031041640c0003685032104120040000361540d120b02c04c030541c0c0941141e220300340c0003080b0064502e1800424030444000484a005a888034180d41c240a106419501950348074038100c0428442d84e00054025604200c001900d21803100c0205034000c0c0503900c00b29940d541c1d1240031424041c00c0f180001240d8444810381540d80e0440600c0b9040c2c841600e00c0035004e034800e26942c2001c800512003502e031038403210581e00340548104021103400100f1003c008004c00d4000c024041d000180c0000c00503480000401d0074140701d608840c3d01030760002d02001031480554480d66544c48030013403680c00d0f9410030b1800101d09005107183d01340407546c00c1d21812103460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 479617652 1250 479616402 479616419
    0x3122615010c0203060f0720100c0c0b0c091302092409040617060709080d0c030201020f03070305060a051c030c02030f03040303050307080105090105131a041a090903070b01 76
    0x2960310946040246250754080540d60420031240244409801221103017404280101040011081c03240b07803000c0b00c4131030701074480005084241c8011247d00003c0d00a4551011142d000e107101c805002e9000083c240709040440d2402000f46080403214140003009210665059010301003100368008640092041c04104c8000c0e000d40d600d444614091070b2040d8140010100c402c80e81100c0e88002c2182c4000507a4842002143c0d001901400c0c440c41440c50b0001c04c43c1c2d16041948a40100b0a00880c0101098001d4040e94010000500c2e059180e18240c40d000700105800c40340c00b48144400745000405007408500c180c80c01030400d1782408580c1c40350724162540c081e100400c0340c140c0b040031390049818200f800070b000554400e03551965030707042c40340700180b84940c10b812070ba202c2c4d00304e1401049955241c11030341c881d0f1440c100c0e0200d08201a4000d800891855103002034115007012003c21841c3d00390814250451012511180c19441707480544c0da81e40140c840c0104025480c0006000440 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 479618902 1250 479617652 479617681
    0x2090103081b0607090503100b030a0816080a26010e0c1c09061407020708151807030c05011202031005120304080a1505090c1509040213031226 63
    0x2811000d0310030442d0b0188410a2a000c01101d40c040001e00848050041e8a4241301d020310116619806129408000e000a511a005440c004110000008038440c8001010b52404000d54110b6203064903407a0f500c0002c1c007402407050f6250002c800c2240b005c0b4112124080507410b03500c0d5409045695075840803610016800064400421042031455648880c1540681a16a446080e0220b4903a400d00c549491741d2201400e004195001201c013800b11010010304d0300b00c1c0000b0792209580030b4031506c803491070800c4d01154408240c003900c10084180304000c450130088030000ea90340c0c0090815103a100341240429681c000142c10034030010001841c21040c0454140d8000d0306603450141c0c0c0f00c0c3c05910b08440c200d0122107901070f8403103600c01984284241c07540418840041d08050f2040350019007003907500c442c1d4650210003c501e13402180c449074140c403a1028804805004070b038a038240140c1c00b403000d5640c040064030002c1c1540c0712640000c000751202d28006504005515074807015080c28 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 479620152 1250 479618902 479618917
    0xc141f0f050c101505040e070e070305040f1a0702061605030105040228180b07030806040905070f0603140603070b1e090604030609061d1e03130b0c0610030209010308 73
    0x24803d5661950303016650f4820400c0410000c502d941c4014a80310a100c00d03501e02100e02c82e001d801801041240440c002e0202d5070020040c500002d0507655440e085811108100000d02200b078541068400c0001e02d40307c8134056405a02221180d5403141c0d0351000c4200840c40c0100000c8040c4010403039802c00d030300940302060300e8456a004900c1e00c00703010301c000d000035015000064110b42006044641040000d800390059203002450810305480142100c1c0018040e18000d9548803504c90901a0620403903000e011390200e25400c80d80d0b540402800f0f0108407050488040101c0c02107a098500001c4440480e4480351040b82403405285020084801592140d01816000c00a00c0740b241d075804002c102552050f00d0020710141c0c1d500300302c1c088500320b100c041d4400c20b016107040410303400080c0d51048038480c948000e500c21401144103003036001b00d52514082400b804004541c8014404c0a0404040e5040458030556104c0c140c00b036400c4018403020790000144401400031441035802080d06 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 479621402 1250 479620152 479620177
    0xb100e090a02041703190201020301031e02030106090f150801050112170906070804030b090c060f0703170a02040515040605031b0c0a0318050d02090a0c0c0c141f0f05 73
    0x1400e5844c183c4004d0020041071640f5030303030000900441c0d039142c80045e1500100442c4001c50456055985001c01680740b01000212a00740b06400000c5541c00d410000242c0020882848250785844000018094004142d403422010010125480ca07051158904880070350218415013205600d403501002072034015440516000c00101c402e030385440d03000f8005a4440c10300c141e640e52841c0ae146035103060181292043e030304664a03480050340c5a0080e501c11002880d03403540e8903685c9140507910103262445c0b804120080c0810001001c4a40d405001100d5080d1000c001e003e03102070f0781b426544114051013001c240309001207907580070001d80b810020806a08070034582602101e00c140f410b178014804800046251004203181c0d0503611b4400014502614101b0a8042d1b95000540c1c00e00000c20034000305980e00ca0750203506100b048012002500a084000c1c0706480d010b05e51000c52a40c005036000c1c009621141d0b12040b0f800400110511244c3e8070048000710f41d00085505510441d0324101 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 479622652 1250 479621402 479621407
    0x9080702012f0c0a062d030e0109060e0606011e05130308030412030e010614090a2309060112051902010e03070605030a1109010206010b160b0405030307030b100e090a02 74
    0x101801102001e4840e849200020143c260703101d0204807108030726400a400308014003900c02e0a1050701c50018202001600005118651401c012002050800210710480d0f00748601e0209002d2658080d8403041110401c3e121282c6e1844010f5510b0010b8501d01c84400340d4403280c203000701d0320440240c1b011069108107041201d0b60303515003030200e0b0015a016500c0c08143d4602580258061048101426211001b440035030f10700031070040710201070903036903000304001d03070000c1c808501030b9120107000300c1620300038101c00810181e1035521007002c6800c00010b200744d10000c074601c16905280802c6c640d002c070080070890b2425614142492070400100d05001c1d1070500d40100341d80903c0400b01030031040c1d492540300d180c2600d0070020f40b4429040b9810125080003414440d03640800c1c02c505640c41600c4103070361035448510280c4e6880c480d40700500120265024001000310200c01180102e150ba81c0511004101c07100f0807040e500803400301d13400300c0d40004c0c9140d464200003001c1d95102c225141d0060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 479623902 1250 479622652 479622707
    0x307060311040923060102010b060a08040c090203010b190203180d060f18060b09010f0e18070902040905181c02030c0d0804050f07080304050d0602070c180b03010908070201 76
    0x4040c1c135403403102296154101030700d10740b454845120b12a8088001d1001b03002e1740b245040070075184d2054540d0300040000b10320003d01404015050f8030028201503104554a45c4c0d54120315003e504201c90080c4050300e412510101180b0001c00c2d5070241c0c2160b04d140045030820703820054001c00b00724040721140d4480c03154185000c4e140c03240050310100740669222002e003e240030011a844005190f22413848540140000c039410600030f0191003030304004dd250f5484101d0401c01e600c51540c5418550710400b40c0c00f0031280724503009801203a036420000c2c00300d034541a6451701d21903500c3c00b034501c5c2a44000c8010708a051541880c170b05422481c01524500404080c400c1d003032180554000000c81c21950501041010420003c0124185d003005004220304008550b43c980c0300f58421140314078040102a4248110f944c100d8180c954030001d400300d43c1e41d98030701204901003100b07000040ca914140101041d0308040c060240700c29404511145448410750065840c0500c0b880580c1e15074240800a1b07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 479625152 1250 479623902 479623919
    0x4050604170f0d09080705040614010f110a081801050304030212130902191704120c0317100806090f03040e040602040f091e2702121902041109030706031104 69
    0x82000381216603400c007413541001001860441c46a100c2d60040703180c804100b00050380c241190f0400d072801d280051750703040318a81c00c444e2103118480c8042140215031383c91042000030402000c0000944210801d00c642507070054603a40030444000e4050f03001100640c03181c580301c41c000c07c02c545c40c41e03e21503000d80d02c0e40951002c0342c11141205204465002e00350740466001240c60800c481040c005e141503241c03d039030f04030a03480e95030141414000120060340803d0301803812030781c880800300b88580e1b4500d42588418841960780c41000e0480c0030303040210381024000b0032005480110f0600440c609450034050701c3c00c01d140180180c604603400d110206900c448844010000e007001d480200b022161903080510800c20041d00d00d10440c9000e548061341c102c40c21214805004514039094154801e00100d2040b04000c10b60794000c2c0111000e8080540c403280c1c034811894025241000180c0c2c100c18040164440e5802c1c465255100c1c1c0002c2100c1c901c40d800c0030302900c0074810010304150380d40042 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 479626402 1250 479625152 479625163
    0xd3509070f0b040806060d03120506030a124a040209180108161a0c0c040c111c170703060302100305071d06030a0b0409140a0201020f010204050604170f 67
    0x10070000e80b00041d041040c1c2c00c040048a400410031907400e400041603036000f410343c20005218488003511100000c00a81d0144280601180c01080301d030179460310f6140007480b00040903190141d01c100300080d8019140c05951240e01000c2c07405801c0041c042c50944d103032444901517601c2d58070503001c106012103034646404607070f02003207440c0b41c1e0b4074554105582e2504058148480704007820601d01c00b0010f003960745560284102185500301d5940040c40025814940080605600103090180c50b100e481e034800c0d0996450040382007581c81020111001c222558002e0316100c00140c0458100044041040f50745030f00260075003000181e0f19500ea001c00c41408078429808003080c0c0d108104455160030040180c030f188241080d00c0c0c1088458400112140400761141031030a0343e40036409080d807241e6100850542d0040c2050301c0d0032601d0200795644050940f0128014051518102d000e10414008d43d0250344008004a0402c0d0501240f2805020454103100540c85004204018040c09001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 479627652 1250 479626402 479626409
    0x1c0603080c0601080d050c0c0405060301201902030315010e01021e0606011d0109091109030307080a170114090415020d0b040615020a1704050a080d3509070f 69
    0xb07000658541282c550030400c504e9441070038040c081044584800d0041003259102e01b080340d00141d2030720343c080400e0040c6400340407490101c66440d400039804110328080c21641505101c1780c1450240102c0c100d849000a80c0c901104144030003041030158022060681d1590040c4111f808054801c031600e00b100141540d030103110303040310302444500d59001e40c4591100211a0907801b01e4000700000902e1002070b4030035186040d42d1154200d803240e408508903854440c0007422287ca4140e18100607090f03502c48070120380820140041496800c5540e0a231138120b60b1842c8032011003205070360034000298030081044454680340c190008003032003544090514003d80343c4d400111030a00b50144412259280c01a21210500d03003214801c00d82d0010346d00424a50002080c100c43d8541c00048880303000b19007020b60b0091a095020600ca00c0c0080c0ca401008080d50780ca20400c0c104048003040b4000458440c010036882c50b0308140301c0031200030038a801c00010f03000c540c2020303607441d210311003502a5007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 479628902 1250 479627652 479627677
    0x606090e0a240321080703050c0c0f0f06010e16110111030a090b060303130501030b0402040e09060f0109090c060e010c17040f090e060610020f070306021b010b01051c060308 76
    0x201c0510134814903018013100c0708140c14060401201c410710160041100400c03000405440b42c0000d040c031a100029907401c00b10000c00c49501124400c02c80343c03140341c080a1810284100f0000080c1d0401e25002c45015206034500429146100c20040303590362150301180640f0342d2510041d030250700c5110300a51094100c0710f80001c9020261929102e00c42d00540700901ca580188002080e4100d100c3c0c94030101e40d0309080000302c204442c400b0a0107030159274440c4884010580c10000c0d204000300f0303054801c1540c0c03503500207185c0e01d900043c0708503100742d00f002d04041440d840501001c0c0c0244440320705840141441181055199500d80d0265008204900010b0001c1810002c04940c14140c1c40034165000c803d0088107000382d4050f036a124000d002510490814010218440c02442181d801220190503145078507140e09041c0080c1d880382c5e0306444096907100b0420015641031048050440059584503d0282c3d22040e94901915444010008070340c0d46c2c00000c00103e10300001d00840800c1c9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 479630152 1250 479628902 479628971
    0xf0c0a12080a2d120b010203030a09020d0602030103030801081e030f2214011d030606100903080c03070c15080c030901020423010315030c0e2203210606090e0a 70
    0x80343c0101000c1514400642250410441d040c082c0e030003000b640e0303001850100004401030f0500004480c0301420134050003140c1f0000c00132081c507038844072a40c1640c6681c012a8900540b00e9819251502020700c3c0400f241c0007400020091b9111000820b048218180c94800104c49000c01120811f460760107040c250490455000a40d42c000c00d084010000350141000320b124005c0201e61540c1d4001d16051164206000c4882c0305030141c002070019603044555180c407500000c0c0b120740d69a02014041d87c4007070180350000340112801140d00d0003400c481d51100159225805101aa0341000d030004445e5502480080f072800c10941c02d0125081c282c0910011003030000c1d0000d4202c0364030943c0306c04400240072080c0045442e07059440f00300d8003030311180081e03541c40e40c0351146058098603400345803500940f810310600d03510149090055200440054442c40021500401c40314284650030114024080822190001641640c0e1006018070302180c00004a880b8400340d41c0d00202c07601407480803 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 479631402 1250 479630152 479630237
    0xb0402091207050405180a060902040e06040615050d03050a0c06060810020403060b0a0506070b091e0a0201030c02210d14010f14040216080310170f0c0a12080a 70
    0x780517298204180042808002140b00240c5480e444c48142c041d185507119a085011519103600c0082044001025194a800e091034150082c0902c1c001e07450720b06406030b001244a103000d40c100d85000354103840b00ba1030400f00500541e500e038030400302034400540e03800001440341d000f4040e040c0c05507040600161386906610b0081c0494402d2111b4901600c01c0100c1031106445040840b01065002013040380140d0341c8843e4a45420100c0111002d000a44a8101c6480e2000030301514440e200744c03018492009010f10403a902c1c030a245d12007801034816105166801c420b02e0050100d16180355012402e1404003252404a61003a4068a64655109410042c950f050402594010400c6605610303140004051aa80d07002e021000340403e900003002c10000380c0160704920080190441e04503142a904003103d48800142e046180306000c0d10006600c0e621b0140200c00640740c070307117071903030000724003512000502d42194001d58244000341700252401e410709000f54070300c45149491021000301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 479632652 1250 479631402 479631409
    0x62a0f0f010e01021e1b0717010b0f09160909060b0418060e0f13170a0f03111b100608160501020102031003021e040e0a020109080f0307060b040209120705 68
    0x8200d804442d40d1041c008415080c00e0882000c503c1040f0804550326080420744400f90b0a030406045480340c400c600000034170125000c1e0070701d45012244004c00c0700d0082d41c0b0500116500c9003104950048920000070004400124055801e020f24600000403607110041e020441d03100341c200c804085000701d42013080594138501c04075000700511341402120b00c0c000308071500301d5025102c03221400c10940007801426101355500c0300950072210500941c81c3c0038809810680c404080100003615041d08541040d001c3c1c0100401020700785907061030306070542400451218040c135140f2941c0605003240f000d03800503010384000f9103171600261095510038042071041c3e84040d80a24156401407080142e0f1005140100048a8041d181c0c2c000032100158090090201c011600d64480e1815403240740079500011481555803003a01c84c00c1c2501d8031032800c1e994079910301a80c07041903031040191000068a54000c02d84441000e000075042c20090307000240300c001c5000d80e062141e8030070b0318200403928 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 479633902 1250 479632652 479632661
    0xb04060326040e240306070309140c010e0607050a0b0c09040516020d0e0301020c030a051801090513021812010f15050a030609110901150809010b062a0f0f01 69
    0x2520303510451034a443d00b205502031850080032142100415028059100c1c41c0f0842556124401419100b403441c080101500400000006807215403022141410702240018800704260050312080c004001d00d0b0200242548106021185406201c011000044065090900440116040548561a003018401240d2005059014921800301c0003604140c0206603006026042d1030890500d103141d0010070701902c14032001007038a00c00000c1300b4a001e588000900008059841540b50079040c4000441c0c55924900801d64001544225103242c5801c032790040203003030880e601d000c00308020301c00060311410703500d129454143d44502d5020a181000d2003030000b1814200d0000d000c407030030031010898210780707800300511442da614002e50030b0150502813808885070060900b4442e40c1c444000301c001d6441601c07014081590803010540251060042d043c0194025050f20309086070078102440d50791014601c08401c0a030024178000d00b250a0200307040c07000b0309100400448140c00401400c48 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 479635152 1250 479633902 479633963
    0xe06070f0e1c0f0515010b09040b060f040b0304050c060406030504030201050f0405120a05040909210f0c150e01051f0f050a0b1b010615030b0609090105040f0b040603 73
    0x11441000c0c0c1014a160030102000000d030018120360f403511052074528a0445001e00180d011960040001014060b000c01003104040940f020300544011109021160090459110344144140400e00260726000c01955000e8054002c0b078206020344400700310182c1c0990081c0002070780711801c2009241c0c090140315041140ea407441d0846107000e45803152170b5180040110204140000c03010003191040007614043d01c500c40c0200036111142c40c0c156211020500140125001c810000b044103014100d00c582d03100c0c3d01d0b00c40c0601c123046a035a401007225424082c40020360b60711945c0451035800d01c2007c0c0b107541c1031342880740802c034442011015014141d2000c0000f60184005101c2510b03600111030072140d000c1c16607905c584200c120601d40c0341d00c0701502680e541c68040001041e105a2201104010107524100003100090b82800814480d480c20a0f808c84c0216004100704c3c00d040c1e021034a900461900066040416030000f01a075026510030394034041d01e080c60350201d147e80d40880d03060 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 479636402 1250 479635152 479635159
    0x30a140402010905060d0e120304140706090b090d1506030204150305100e0a170703080601050a050702103b010810090e0703060c03020d0506040623040e06070f0e 71
    0x100c0c90281c1c0020080a400c0c0100c2d0700a0310086115084119507801c10056080d5080c203454080b0854100300c0c1850b00308640030384444100010154207603c01107007010649646944105c1d955051862414460744500201d0f40c000c0705003007498000c21042c0340f803254600e0002c080402c1031072031801004281c0c1c7c900e41d0401c3c200c44014104100080300020065020280c844000c1038210ad081c5046041c0f40300201301411101310904105440c10030280244452446510b4155058903903e00460700c500070a04490086502009000d001d45010300d1400480081072402031075104c543c4a64031034600d00c80080101d6045001040e074466a8841c102250011084c40c044285240c03030417946084040c10b200341500300366a0400c500e2440c5007800071a001c0c41d004030081c0008110410700400a5000c402441d40b120300e4a4003103449498580180c5d0115000b031030f032000281000f41c1d840b40e031f02221004100ea2060340c40d11880043c94003801903c2c03003131950f40c1781c01c0000c00300c01c00e000c2c00308180310220510 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 479637652 1250 479636402 479636441
    0xd0216060504050904060905010908070c091503240e100b04021806162001020c03070806011406041203030504020a060804080a0503070c0609050c0a05040603050d0f140a0302030a 78
    0x240c95000c4161000c4480c01c40d00c00e000c903161814950014601e03100090059420948003c0c10f01c500030004040d2148039040000c10140d4506140048031100f1000e00342c1d40610000400100b0290750780d00524000807c0f0200300444d5031100501142d202c041381100c9c075040004400401c96052140085a00301a54217520344048201521460414844524414240450f9114180c044040f42000807a400305803264400a02ca4088150452070120140107124019442800d030030b0215041080f1000000103140b540d08281c04450765589850425410013024440095000440054140c0582c080c1e1000982414a4018010001f056030414000d001c000014400020050b5048604a500b145440740d00c9495144c8104c07605400f2060150216003400300e0a070a1141c0071401d1284520f0440e50200c0496840301400b058807030354400548103030040340712961002d000d5495100149668540001c0c1d44c0c9154400c3c3e01c0c0c42d0002d00040340041c0c2d001c820844810f005118590f00c440c50441143e0707 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 479638902 1250 479637652 479637659
    0xe0102040509040210052104020a14031507020a020a090615020613030c030c02130e1c1d01111b01020115120f0201120c02010e1203070206040b06030319020d0216 71
    0x303064202c050303c000e00030b19810102400a911a00550781c43c03122202c0c004130a1250b40c07411403011f90050f501603100e500700d10400280021034a041d0603140c90050041d090b00401d14100c0104200003c00311015405201d00420041c3d43d1640c03550054400d05038000b41d0241000e5000c1158003c1d07107805000d641c000001d20002c041001d5604200a5042c902000d2045161804403401488007400035003199440508000b0702155401c071802041d20241280c6404800c3e03001c84204410426041000c1040c01d86114044030369084248220241810582520074184a05510785007105250315110451a0b54039103642d17034207010751120305840096000d25607040c0030b4200301c0d18035103400003414419002c0b0035104690007084501c001d100001010003111008100190103004050900651402540c0d2100b031513012030800c1d2405030720503500a01e040c1da216940d1004948000d8030703d0368948000e0040100c0112000041828404aa03000d4020300c000b541e0064506000c0000044030054144c0060 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 479640152 1250 479638902 479638909
    0xf0803032205030d0c200f1b06041403010605120d020d0c02151309022d040e0708150915030c0409080d1d01020301331b03031410090e01020405 63
    0x4440f10442c1d854005012209150207036a10601c040025034240340042d031071402000e000c251400c404401c202544e564580300102382d203040a40f000610340c07000040c40706000324101103002280485018000080302a02c442c00030310304a2041c00d02c2c40c0294094480941469818041030040700014140048910025400103400c5005007503000c40c00d11010810001000002035400000d201d007040466075100c1c80f40c100c07425041d44c0c0c503140301d0745102104040c1c100700035841240d0881d004940a01083d4550210880f0000d40140915640764210701240c000c0e03545003a9114010140070080300b10643c030754001d00d810030840b84540d80c8258a0005102c000c1903a1004860400c003010f1070018000030300c5882d0f103442c0050388150f425151700c0400049034a1074164046400c81c441c101010452a900d441c003081c3c000c5440000500145d51070548a4451b6004a40120518464180030403000840c4107602c00305070003140c407100044101e03c070810807003449104002c09811003070000d41c5881d0404011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 479641402 1250 479640152 479640157
    0x8120304031409030a170a03061e050409020d1704050f030a0b0708060d0f060501052110021804051009050a0216080a1403010b04260a17040f080303220503 68
    0x845945000c001100410f0781d40c00d10904900c9980041c10b141c010158011000050308031241441c0480d07d001008244080c45116100510600c4964004074038201014000504410034040384c0120341740d040303a400110750300c40c031081e01e69003222500d81744c46ca030004001c00d18000d180064029004003c12002003000300154580c0280b075810041925280c050114000340420b11000d011400c080042d08204991604403604985003200c2088103014840c0e00101143d507155148840c3c0d9229203c0744c042403196402910030030041c4002c2c44120340c0c0807800304040d11004c45600d1010032002c1740a01c1081c00328814680c00209a40c8114285940c030b44402c890903100c4e0001a01c103c801080308442c640c41041809140040000c07031540741e50b5941d001c0c140c03540140c001c0c108100d082c41c204080561840f04407880c0000390100405400300c441d101c901a041002210740c02c2e2810801010031301d212520a07080042080300f0080d5030b01d19180c8055400700a45420310145803403e0a0b800003c9a4004103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 479642652 1250 479641402 479641427
    0xc0d05070905090a0e07170a06060812040311030a080706050a0f0209060a12020d090c06020c061306030b0d021c1e0b0f0907030506040309150905030d0c030e06070803010812030403 79
    0x10004070122596170652030400c00364410703051180e41d054041981000420000e17141d901c124420b0050940740d040d21921100d11680700f855000040c4800c00114600808420340d040c13016054500058260300d40d00700a40c8081c41c00d64403a6207500612000903101d00c20420f07203c2d80014110b081c07c0140c0c0001d0b109200d100c28034001c1000080c0340c144841c1c01e540c1140c80b81c245802c400c015888480c0741c070200c0c4000c0c5100d0310000d4007454450700c02509012045908004242c21041c150b642000815802020500101c64206c0c0c070035000003005843c1d4004803c10003002c0c03071226100e886123190041e24503c903245c070705911044514503d00001c2c6600601e5801415813050140c8660394001403034900b44207175102805501c24003017804141a0132000031000e031501240c09402c4800c01200c1640c0c00c03061413003107d8041d80321400301c20549100d04c13800c0c007401d40300746880d50303c2412160019034a50061002a1081c8100000410a500e0200a100d41c01008100d00b2411850291009032020403c0da0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 479643902 1250 479642652 479642671
    0xc0303080a06082104090924050c0d110c01111c090b040807142b050304030905090601030906021206010f080702073b04031805151806030c0d0507090509 67
    0x50f1070380c4c1d4110b2480c1c20303140504101c4c4010002038002c2d0078090034414044001541c1e074500d1000f19650a86140103c0d441140e1007a00c2c140340401c090020b80082564a070011400c020034000040016028011480707000c403400c418549504510f2901131101c03100c0c081462800d840e0010a03030014190805803503000341c00100181d16a44182402c13182600b407155800114007500c0c10040e40c080710b00281c0741d002031942010200c42900c05200340d515110545001c0c4c0452005101041a45821000b155110740c043c03401141c1c1520503034668042c0d81040307441120191041080101c03959008000024000f15803500945909084601a495000034011988484000349184032201e0403c203215110100b2410000310800c414100307200c41d010282d80440008280807012440191003030f1200f001c3d80d1004000d081141d2903152085119442074031050b01d4110202c550b080c2c903580307803000703144240060700300140d071341625000703500449000510881c241700c140030701400951100004581c0c85900310 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 479645152 1250 479643902 479643943
    0x40b102702040b0406090819111201110403030c050f011407180314060601030501080f0c060702121501081c080a0b130f0b150c0c0108070c0f0c0303080a0608 69
    0x18880806840b4980000c40181800100041c215511085840441d43c550059601010401000744640000c840e000352403603100001d030041a180420341100f00c1d0032070f0340c00001c1450640d0446d81e01e68120354403d90104020305064018000c003444003001e1003103410000c005144610310402c00311000a0024802c00a1002649102800e20703030001001d103800ca41e1002c140e014001900e40d6860007191a640041d0800000191160001500f0411003030302c60050244510b011060200070f42051000381d80c08000118420980003003880382c841041c081d030380000b41d0340d070525283c2e500e0700a6200400402201440300c1001c03082d4403443c1c170354101c0e88521010071041c01c04030010b91264848440700961610700b1a9407040e1610980c400c0908034000c0c1c0d100880ba95440514a50b00d01451118891603080302c82003140740d40c41018001d42c842c28500344400c600c8100c2d183d2054140e5000e80840e032072540d06000388149a0042d004541c00540008240305060920050545130038880c210000750307182c207 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 479646402 1250 479645152 479645219
    0x5090f04030f050903120405100c0201020d031a0630040b010302120a050d050406111f090c03080408102d05151c12080c180423040b10 59
    0xc208440e03036030500601b200c001c60914291030300d181c0c2c443c2c414a44154a021000b150203400b8100300802560140c01410203240e140700190060048580c0b50206030b0403100b01c244c5640c1e1503002078101c4001100640c4101c451420406803c07030001942da20000031260f04004c0001c1400031075605481c0c1c10380b85d0440d41e40125400c24a03002c92840c4c01000307030040c64803131400158002c01410440d003481da625a00710a0078018291a1640d4928415007005803040c2c0f1503800385942c01c082030042c800e40c0ca00300c07115030300d80341d0301d10b160007540220b050b0340c1014071401103052450144182c04040c80d03c00f101107803d110a1070800c0d1040361070078201c9540f50000030308a1101d1202103c80c480015007031014008860700301000d0480d441c0b0049410b10030030b80c1040309940c85440d181d441891061980703854546058000c01074100d20105443e80700e502c804c01c0f42c1030b0f20f1071f1400303482105903800c0d10307400d10303041510302400d03020307001000010a1040341000300302c4010190320b558981c400b172881545d0380000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 479647652 1250 479646402 479646407
    0xe0304030c090906061d150402190806131e09110a120b01050a0509070804031e0513060801080a14070513020d0c05030606090409060e120406120516120906060b070b0105090f04030f 79
    0x32b03c480e201500c24014900194250044501e51282c2e408480c0840703a9500854154100d48481d070156460f10210101c208102540e980940e00550190003810210500040080c0e40d2007510740100c520105c10048203410484041c8840d405000c0440d80540762a0608011a5030303008001c0600e8208102d82c800b050905001314501503a156140003440d494002d50180548554003e11211b080b415140d440003808034860303030030603050395500d00207028128055118550032080e4030010100c04d02511400041a941301007401d01010807001c40541c85880c0309891000722003040c40c2d18400d1040800400505503148001c5481c61201210006241c078400e092210040405200c00c407514810001c2c0d0b07020720022840980110b90441d940c05c0020900302050b241980d10940e08038902e04c443d0f042d00400103000d92980b01010b180c0700345c0011140b0050319044255111640051a0070341e0000d8290300380100c498a2502404040c1d44810a0b810212000c0c0110140200080d08200c2c030001003524492 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 479648902 1250 479647652 479647657
    0x1050a1811011205070c02010e191502030c010507080105040b0904110d080f07030c021c0b010306020724020c070902030103170c032701032301090e0304030c090906061d150402 77
    0x2603c1ca1003081140780541000c0d044110751803082e808600020540300f15460668400018000c0d101d158000142c9484082401031011400c2b40043d4082130102d804404001d12070355120b90010340d1014240d51400050004949801030300c5401401b080040001003141860201cad18004280c0e0410200456810000541d00911550f6041e44a00044003020316600182d4509100c1c021108418a003941c0b10107010300808620000344605002801040440e0303a984c06040b07054010b00c1004104160540c284914015030031148001799400b19080200c2c040800c11000541400c0c1e400b1840d550554442c00f084082500c0b004c0c4129400280407940e86605000755910070280706401a00d842d100420924040c00c1c4001d0741d4006840e184044641c2890356091a080c090100d0003808640d00740b0440354081d100104850106210400c00000003442288000700208611800000c50219502d07006040d60320543c01440e4484828150140903200c40000541144070221071280340341c89040810060b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 479650152 1250 479648902 479648927
    0x10e1c020307080c070617090d0804060617060f0115020703020d02010908070b030103062a0305061c060203010e06090103170d11070f020103060830090d050f01050a181101 75
    0x900c00480d0749220000300041c45d009441480e16008010782580e142140300883c1100e01c0041c03940100e0a03008078602842c03440d500035000e0640803909580f118615030050b1a0b044030300ca0a544404100048404070080c0107000d00741e00c1d00c88003800c42d1013520080d6640000d00000e4810645404548111380c000d02050000742092016944510341c0d0b480510340942007403009458040c10031a190f02c89071003101d02002030035080e1f03001240d5000d00c00c2e000c600500d001490550171004a0fa50b009800d0a5106558105889450003503035035070501c00c003250740403000b03400c0700d0042101100510000d40300403c1250051140c810054883c004514008050420030854a0703d00030009031280c02d11150490420303505000307232418021150f803199481c1d65405a02201e640b468040d204504c1d03098201800070800251000c40e0a08144120700000c8560171b42100850707856001183c2020342c1c00003801ba1b0341c0c0c84591110100308000001620072007a4507085001440d58501788203c110b00da006e0740203450b05 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 479651402 1250 479650152 479650163
    0x120f0609080a02390a090e100f0944071115270a0b0d050f010e01180608010e15070c030203070b070210060b1812070521032703010e1c020307 62
    0x79481c60a00894a41903103d0210780034500b810040c0811427024010103250300d521200c01116840c03040c29074402e41a0842c02000100c8410044035110301c0301d034888540f415a166103c640d84d1406140a44081440e155030741d02644a000c501e0380760f00340c0391069801040c0c2c034400710030150007513a0a0b0361001410001460344400c510501245020b00720018146448902000b00103a84524240c3d188a0009204500b107400c0e100d80184070402011114000740a140200454001c4e111100c0909450107075243d800b940e80f00250380e01007038101c402504e4010f01035013005103004040e510001c3d224411803001811081b40000410111403080040040c2855103000420025446d071104200c0f82e801201e0070f6203100d00c020b01070300413840c140301e20120310b000e032100400000b0300e000244a9920b100a06045504d2041110000c0c004002e000510455420a00640b460201300100b03403d04014070f02428040ea2410710000b0f050180040d2801c401d41700107503004c01d0001c02c01d808903d50710a407a0020031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 479652652 1250 479651402 479651411
    0x14060c0a05070611191b0e01140307060f0c020405061507141606120506010e09011502010f11120603070807031a16050301120f0609080a02390a09 64
    0x9201c00402c104098030650760760f004980200d0008565103001c5000c80e101903c5040600100061b602d5508442c100c100c0c166410706190384805110707010750240d0050b80400600c00c590203003823400b070100301c0c050501428400e081c403540d420014000000c1080c0240a42e560b1000700d0300c2d0340e443c201c00384003202e00460003640c2c0300d446242c401d02c1c8400b0041c8400c0d04e4806d9042c0c0c6a40940741800601c1582d21980d03860fa00b040c42a900321001d018007400190511480b10240402d0f500d9007180180078081301e080491001ca40403000900b16070383c0d01c5404004928042c0035081d1001c01c40100c82d08040031244801550f2140000030741002403a90003d1074611489a00008100705000428503410012480800545da0024115075001c6000d0a070000504104014409510074081d04506140244001c0000c100140d82e0700d0f00300d4954010031b42d1800e4011405c141103c0d410402010000411001c03603c403101c95201c82c100e107800c142e60320316103060703410281540c586030204404001d21741d2000c24003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 479653902 1250 479652652 479652673
    0x3060902150f070c0e060303090103050a1107080a0e01051602090a0e011e150f03080a020102071b18060b04180207081207091d010611010e06010b09210714060c 70
    0x200c16910004013210301c0c45409800003400303030004850704d12a000c083d010b94a0310962200443c01440c00402d5000103a40d500d9190045c1c41c1c030040030301412840341c0840c0e540c4100e44e8501801d10f0400b0100181085820040d070810307110000c99521050740d065420380829100c00e079000004e40020303032022125628040c0c05114400000740300c5804070400040801604804201d400128035641c0505c0c040b082d600c82e410400501e041c001000030394107a100050908110342e440c80c0e0508070040500c4500c90700ca000c1030040c087c03070410754041c54200380c50800c110b40c9007003158020b501452282010707010b52000030f04411702150301140c1c42c81d0f40c48032081d0b9482d03010707a01c00c0b007505a00341c440c1800a040346101054222a400d11002614000c15601000d0382c6045021162a56031501081172952601c544401205042000501a0031014011600c03440c0f40c1c428802c00c8404100c00303020b4900d04840c11145043c002c5603104c1910480e0741994610204207010810701c2c851403801001030700c107015515 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 479655152 1250 479653902 479653927
    0x2517040614040b09151207081503010204030b0606031f030302150702010905070e0901061a04080606030a260f07051b010302070308061309020a0315050c03010501320a0c02150a02070306090215 84
    0x12403086403012500c1100b007803801d06040c05c038066800003c4c682e00fe640701054803807500d80059640000144070f0404288460a07141810504607407041b005030340f04000341c404c2264841209580242d042c4000c101c440d00d980c40d003d40d18001c1d8410700d000c80c006000411445003080d0888009000440d105141c1180100c407036654960007403190760300601800740803910030b18001c10402900c0390030a10141009003680c0d014400000e1000d108000c81408020708a40305c40798501401b603080c040c8015010f2034001e1400c1036420f0003881446410944100448400203030421100c41e0419030543d48018513100b1032600c034004020142c0c0181d4011010903001003048160400205600c0503013805211940b1002d02000c12800280641401f02e02500c4804840400540b1749410307051888030005100081c25a0815440e40904182000500200f0649055061420820342041803100d002c6180a5408100031344450450100806540d16002c111003907543e203d2003a041070700d25035005591a2005604e0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 479656402 1250 479655152 479655167
    0x240f0908070f0e011401050711011e020a1202061e150a0b031b0405100c1a012c01060807230301090606080f0c2517040614040b09151207 60
    0x120464041040c00202d55488114880350702210706071150707424290740740d2750306c10341c440214840f60402403042c45408244844001002c0300300300036006456095000d0a21821007030111844034155800390f400d0220100001148000803040440e0303a40070ba4031410420003c1203000c00307410b980442c1c0e121020503007503c80c07801103020310041091000800d00f003c2440c180c03401a44940e6500107040410201100d00800c1001d4040b0b205040031518011800281d5507921404e81020391014480e446a844003480781c1220f4070510950070003001d1542c98000000c00d80b410003008141081090070304a0705c00f4249643c03e0a00000303940303190b5100d6848291420003060980f00703038400546074402040d031052224100d41d010700492250315281c0b0503101c8800240c00d0130091103440c4222405c2c080000b0070001d0044400502e080e400700e0740d0340c074649840104041005c00828005a404000402400c01d201044440c500700030b44200410101c0d4a1000d81c507405100d921560390021041000380c4254042807 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 479657652 1250 479656402 479656409
    0x180d0f05010c020d03060506161a150a0b0711010c14010507050310050f0108060f010909020c01020301090b010206071e170a0c09080a0b130f17030a06240f0908070f 72
    0x4c681c060f2603400e50490139925035100e065044801017180c01c1003030004102d070003100c42c06001c1d035044101080d40d07807180d182402c9955422070703d404040c1420380d26003880308034008c10f45040c2060030008184c0321600680d1454500c1414007100144983c100058400c1d400210100000200510724041c4030250403548102c030078020908044601088528006043d005c3e41141a520030000c1d90f2018103100744500b0065400381031000c06500042c000a140c001002500807540026841c0d525107040001582d440560250641d04030000700302502e640240c001c03502c0d03442d040c4e015102080180e02900c078070000741c103c1c05a40c1018010407050301150741001052941c10303903c911842d9030307440d580c1c0c0d190141d03180006c2113280c122000c280010100002100258010340d0f1501c800000c643d66400c0e0341d41a0390031081910808020405000001d109007030003405404140074210b00d07141149030001d5066849642800f08a1103d038244500c80d84d01c000190010704111a000368444141106200d544e22 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 479658902 1250 479657652 479657657
    0xd1e0308010503010518061f09060f08330a0f14060108010b04060e12011104081f09020f010503131e0b150102060705070302010b0405041406090a0206180d0f05010c 72
    0x1030200782c03086d00360680325030001d0034203003d40142c1c0c0b651004841b20824140c01b2039003100340920f0200c3d017024144503000080106039442a101e9140c01d803001d08245c012040380760481a51040350700c66050100c0d100751312018510f1000b07040e030340d02095200182144660b6019081c0b600703042540043d03c0301c00b81405040240ca40690aa0340c400c01a00350b44030764028000094944846141c903400c1c481450341c0d210030700c031001040120002411703104d00d810a82c0441c00961100c00076a080840d0201c040c02003102001040c0b001034040d40208400701801c1c01c29504102000001890011071100703496040b03680402441400009240e002100003058103003551508540c0300412010304098100304400c41d41a00980565602c40c082680d503600500005c0d8259501c0e0041d02c42c86560300e00c140d9100e280301d100c990721a85d03624070000d441c0c14801041c96031140d1100d0065409a6540001d984610014040030100481c80700081a000c08249000030f011600740540300081120641003400300401e981d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 479660152 1250 479658902 479658911
    0x304050105092b0903060504081b03040e0106050f090a08010f0c0302070c0b03041703010e0420030a080f0f2a0a2418050a1b050f0d1e030801050301 65
    0x1c00e80d60f4560b0400d0044a0350340f01c0c0d03140f07642011040480401e981203158100b0381d4445a890b05c1c2c480a44404440c00c552103040000c600803500380c01e08504500041000c000c50406092801149a55506014140c00e1000201d85803a41c44115402c0343c4d89104064201900555a0110340f4041c0c06141c0c0c18690881c140b01c080190380e13210b032003901c01c1d954000003c0949070385441d1241d1350726800680180d500300800e00314004242c4001c4003c5000380f0000046115034541030400341010b407e001028407007494030f03040d4070040b0790f8000740250690340c02c1001c0a0741c2d10388546100882e0702c196800c005410901103034a4508402d0341044c804c1e554000b241e06145500640000d644803d45c00744000e11680074060141e901e4040c03280291105078809c040002c00c0f034901c02200d090300030441412140b40e8001d200c50b00402c40003982603c2e0300c802d00102658aa0304004c002140c003082d10700150301074681d8003d01000e00030300100f800c3c82840010280e8881100504008000329424000c0ba030180d800c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 479661402 1250 479660152 479660161
    0x1201020c07080d1107180e060106020d0f030c2c0406030c0f0807030203070905090102130e040c08030a0c0807020d0209041a01120206090d0c1505122d1306050c0304050105 75
    0x4c0103800c2514021074098407002c0e09005c05082241c820301a5003101030b50354907000503440020421640a0074070740e0010007400ca4461001003480b1000b40e203100402d801c1605004d0002c2c0c002c01e408020b122207955a9044c006c02d15400402e044056094943c02030603c10008203110780320401c0c07010342d620300d07074100c5025840780c4a02d642c40034248002901035105a0041000d2000d0381c1c0304d0781e0890f9401c4005894640d01d400c1e0900c03041420b40120303200402450502c020030034078422900041001c0c0b8043d50a0601da840064880c102c000d5025007008400079540d021942c512002129403940203000181d04d00340342c00c0600d14520b2079031084060042c03800c00410010800450401d1b07465000300b03c1450101ca4101f03025140005013012a02000214804901130a03501d4202c2150b00461b5180f80e111483c142d0200511500a041b15520f41d243c01c40b083c500101d40e030743e035003001c00f0341c4003e480b5142c807a40f60418a140c05000c001e41002c0c508810312490524500041d80190b000f44000d02c0325869 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 479662652 1250 479661402 479661407
    0x414030f090f100804030c06060315050f0f1501050702010c14010603050d180b0904020d050f061011030f21010b070326010e0702120d0609240905061201020c07080d 72
    0x65103c650109409000160000303201e04444080c2e01c2c0302c0d0301c0c04148980c1c0c90b51000c00788000c2100c04041c580d03e40080014840840445035404082c540c51403100c1d041414030034209042050010b41000000250103055901510a509109130302c0240e04a01800e82c1101038000d01d09800102c500d07004900c007142c20140f162010b002048640d044d40009589440007081469000007640f540080c2c003070281815800051040c42e00c540f9180b0f418060500e019410007113850072241c072003424082c0c10810014800c0c0008140c615404ca001d040964854004207054000303e032008194402c0071850002156801070741000e480114800d880f070400c460002646031108415011040746801c80280042000401119010b0782200c440c0c015100c2c0c060554241072126802810000d017000e880fa603007000071840c5032081780094450082080b111501440c900c0300742c1c2070070744205003d80391500c0100e5260b85c1c0302d4400c2818101c08100031550395030710307001554039203009100c1e882441c05480103100d43c0a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 479663902 1250 479662652 479662669
    0x3100504050613031b140a2a14060f040302190305060a02030705031506040803280206060102100c0e0a1d0108010c02030904230c0309010c02031606050414030f090f 72
    0x5138551540c405602c540000008200380c15078065803002d00300e402a006004003484400440c0b4007500840100b00b01040c5250504042c1c00359440e4010000d0a0401201a041c40d0b81c00350f04c907084592a07902d07400240280b010340695003000c1c2d80600b0761807001d1309140b16144003c0417248030780e05603a950303951000224101d0000703d0b010380c003160f130030400940b01040340103803a07582410082c81d45007095183ea40162454102043d40d100411440b0850110000030321049150142548010002460300c2c40000391100c50228148142c40c0d1a054803c43c0746024039501ea00e0301d02c0103402d198800d070382d4424068550a05004e69040c2a141c40000308400d9018040d20f50390800c503070000e52800301d943c4107020080426400107640340f151242c503a580d0f00e108011441c05060404021626410a880e60b54210b9484d8041c41f4255481004401c0c40ca24000080d03800c1c40c3c1c0c01200024084d500c0d8108601c03108007181c0030031100d000c0000ca400c41140c400028000c2100151100300754450b00109020010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 479665152 1250 479663902 479663941
    0x2203050c06030f0c0d24091103061012060e16030b101407081608071b050a050607030219030f26041112030c0105010302040c0804210509031005040506 66
    0x41503c0000340c401907280c006210b102c040134030001341109045c0341d0b035008070b255042ca02c90b41b1812039000c03c00001a0f00500c801030380120a200d04d1810300f00001200300070412200c03806c1c05002d41803a00125034541c040402014071000c0d81c05a4501008141201c07540359102c4008280b5000c1c61780c2c1c1c94108402c500c221002540c9440001480b2039424800740e8010101c11914a5410441c0c0d0903c41c0d110120105054440c0c0e9403a61640b12902d040181030043d600c1401c000490400e00700020303a07075040325408682d402d4500c29640c0da83d604049082c02c6150901001c50380020b4070401c10142d0000c0a5800381229940340c00c0d040300b40390400b1001034044900c08608120758404180490201030021742001801070201c542494002d01c224119007101030703168580c0c0d43da900100190f0400e4096071030301c51041d181000700f600d0580d07911480d644240080114130011101810f0b80c060141040b1018800c0050464520340c14445080c0050841214121a503000c3d00300424541c0e020510004c07103a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 479666402 1250 479665152 479665171
    0x1213030c030e0303130308040f08030a0509060d0f0212150103021e090316060305010305013b120d1a0114031f0b270a050a1202062203050c0603 63
    0x92030000d44040711070408900c040d540c5030104225a0180740040080c1d01d00540c41410f115449503d4100340d201c802205620508a5070000c020340542a80d0000482d44103070011140d6a031a40d41401c84040145001030000b115584002003501520450240562003545800c0c0908030801000c0011002d0780520f96043c00040c11102011071004150000341050480140c2200c001103000040c40c508660310381c0c000d0300402ea40360014005d01c04c0c28058060300f030114031a101003184026560301b490f0080e0003a81c10b14099915803060200506010b201a050b58082d01140c0b1080220804401003d808108100204403030300e42086c40d5000f141c14500c0404000400c07401d42c0e6031040d502054020034201785800e40c5400f1030200c0c2000889016000500400680381e00c0304202900e040402c01c00000b01c540f05200c0a0300800c000c4d074403460450300350b50004500a80c045e42600c0465214080e114018084292404070000756190900942007100d000d201110a21002d0b0410300004c0c1c4010b54184070b9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 479667652 1250 479666402 479666417
    0x8010b01120f02092e0201060303050d1505060d06050108010807031a1506030408120907050901061206030c08060403080c0f09090c07060507081503010e0d11070902030c121303 77
    0xc0040640d44192411070184501500d03084c1500c0020340b54143d95800f410741082c1c01c0d80d802c010358400c0a060400461140000c000482c01c50700d002d0043d0240d02c03954418103440b8402d00e0800100401c000c0000e00e00648241d07120300403896120050805809414002156480000360000b000203003c000c90781c11204015944220f4080b040c0d04500c01801d000d1441c10046001200b6101c8900641c0301341e015000c400d0300c07044901e03480d4a00b000d020f448072031aa480031000340b01d140c0c0c50800300c5044a0140c06c003a664010b80441070400f1700000c3e4406029103405000014081c90049545072065120341c0d208000c1d582d510200d04200d015825030b840c0045030600100ea543e05195568070b8008a41c61616410039005035141801d07102e00b112a0f2001810740414008415910040d004501d2000c800900170314044101c103580c0c42e010030305144100304071307848030341c4124a08ac4079650113003150280c01d5549242103001c0c41c0e050741c0a02031202070070487ca000109400f030181100c01017150f00d03580b980c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 479668902 1250 479667652 479667677
    0x16050a060f020a0b150a050402070302060a150513020a11070303020304152c01030501050d08160f231006060f120204080703230a17070521090a08010b01 67
    0x90341820794001d10415480f40440e504082040e00841c1845071204490703095036070b00c5000501c40010600c0d809a0301031801880583e0002c0c0d0080755603680203c6840c0001000725000030903282d42591640800c0d000340c00c20314140e0340d02159030014007e040703581e10b4852030a60810700d8941d031244c043c400500140c0003804103101d00340c2c95051040303505070340d860221142890f09100200f9006002601c2041440d0303111502960b58050158600500301140c4980749c0c40c01544500300c4c2403051081c1401c2d15000084040c041099201e0710003541604007200d0089100c41a0140500000e0008188030034802e01b40356144072191402108241c4500d651011051208843c0503140200b1060003040c0c2d1940900010445000400000c0001c0d4003a044084261482d070103591291420f10750000070603008130410b0030100d459120904c01c007074116110903030344104905000c2c3c00d10700c03c4440d403952548130320b540345003d1413424043c0c0620201141e8584105035552101400c90b900700307440340e0100380c0110811 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 479670152 1250 479668902 479668907
    0x50106091214010204150c1b230d060e030406080606031605090409080f0a032f03041401091121060105040207020a031209030b100308041401020a0606030c0816050a06 73
    0x1071070603420b00300026017829124415400640c414030070640000380380c24000010f101c29200e45c80f00c4c8000e18001c5100490810804c66500e24980680701c2c088804a0403910003919414000003030941c024a00f00b065504130510030b0f840e43e10a1044100003580500401c041d844c0a800f12401703094165450f5a440100180c144d0b480e80106c1246907009a59089180120302200c0c01000d010700c0b01148a9528490610013504072022a421715585054100a440c034120307041c0300003048140c030140d02c0d80c2ca035603a0b41380040d03081118040410701d6500f04603040003001103c41d440f11000c10210340c907a070019040c0c19984240c90362110b44d900719038041d0004100030305190b0b0007030540780d0001d00b0403003109480303031201549421036465050006400307a1003001806455010560031103130300c0302c60170051455502c8883c041d003d28000d6180c803880b03001c1c120019a0013008111900c030740c04282480056900d040140c03034a10680324465060041341c000d02807001c3c03001e1515003514402000d101c2c6c05070501504 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 479671402 1250 479670152 479670173
    0x8190b01020307020103180c08070f091e0b03100e07150302030601020d230f03070801080a05121602030d09031b05090c0a18080604030906030509150c090d150501060912 74
    0x30780700711f0106139065000c5140143e010029106000042020300d240210008900095a000e001c811b0300d40105c08909407089044c44d2015803054101007820040e10002030700304104d10400d540900d00d01080314081d40c4d404500030f421a0b0780c90002ca454444c080d41d0990a81c4000c58181c1e0058004000780b4020302d00804115800300008140302d035130381c400c540103c0c40c1ba40c841804107600d140003000700f00003960301c40e000707501403d4614094100b00d00e0315515a590b6008494120164038000b142500c2c104107001d929492060300141110303800c25042c80041d00740c80850206680e41c50340d04600500004d1242d42480c12200050140481c80d5281c140b134822350307002100c40e54100301c001071950184080d000d40c1040a4902c080c007800c0f00f410b02c0c0c030303024004001d5a880b10040c10b04000c100602d100021800c0501c0343d20400d030101e001c1e5079108007003150340b06d00c00d501a44040d08456420610040d00f0b03803104660310002040020342d807141410390b01900d4034031601e5401006018418001a084101c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 479672652 1250 479671402 479671421
    0x7030f150315150801020c16050f010206370203190b15091816020607090b030114120304140405060f06190516030c050d080106080a0e030c030a08190b01020307020103 73
    0x400140d101d4a0ba00d115003a40d00c42c000700ba4988d44043c01d40341c001c1000c408648001c00044540d91a030b840202d00117501c0d241e005110076003403031031940d5040030305580705111102a080a401d100d00603141c1010040250020340f810200342450407000c010b4041d0f0740c820000c5410005103400320210341207071440722a80c0004000e54200030a07040010075507117520091b9000c4c3c00420000303e201020404000d1500030300a121104129400c0400c00204000001326030650b00c540034120416890800840d410484da0f500b128640e1000107000a0030051010b508280c1d080700b1601401541c40d240104402550300420b142e07407155007082400c0c0442401080e003c24090b2505100c0d042042550003507010304041d001c01c0d400300d40143c1e00c0008101050044091948541c203202b005541030000c020005403004250400e40e560f1400e0881507d2030030400d981400d1503079811240c0d90181c0d000000c010310825100c0d05000704a14075103c08001081c003030140381c0181a4000d50800c90240c0045016180060 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 479673902 1250 479672652 479672681
    0x150606040b0d020405060d0204080613020a050904020f030d03050603010b0609091614072006071106090102030d15060207051e090c04030203100b09060a120b0405010b0907030f150315 80
    0x580ca81b101c10140054902490700161030754a03102c000c6007072201c02082c0800c902000798440d001642c408902c3c005403007040d603900030300c1d17651072000c540b68241140025030300d84208080c40b040240c2c141c01c594880d01c0142c0003445508010010710038140505070300e01d80d01846100c0081d840b84801501f1800c07092a5103071600c07c51020802110542d40711007002d40341c241e0820a0917101c0c05103001c0020000409688440c40c0014688401800070840f0003014802c840001d8280c1c126803003002a2083c0c61181c0d00100060807814a64041c402807a105000150090a100148501d0440204000c00c2031041514204049101c01c1013a0204010050400360b0805d201c0800561810040b085010109100c0000c1c8032805504102c84004020804c41c800c101141c2c3c1031010401c031281403031070258030008484450301c540c0741080c0504540340c10f10390009200030400602d01d03456004449482070b01d4904005048448440164501304c50101920b050100880282c0319451940403522062160 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 479675152 1250 479673902 479673907
    0x3070320011104060504030201030c050301050f094204020408120703023c120901210903090306051b0f071b180506060307170a0b06031602150606040b0d02 68
    0x244200d1480f5005900b10303000280300480c0038011960035101d0b03002102c0207420070b80d09562514001848030400c249615009070303203000100303045602103c9208042c6484c00700410001c40004a607480806034610007084040108504101d02d081074400c030303002e6a42040141649071214020442d25a2042d58114114424190100100f8624000030352501c03658103000e0303800071041800241110034440e5003902581040881184004110045403e011428246501580390391803c52001c4001c00c200d03800301d581403d902c1c070b04140e13204000c0010340e8483c9008010a896070590384040ca0042005d03d09818020481c0b40e600a00c5030b03003e041d1041c81400166510103645a40c0c80c1c9a00c159400403e010006525a86905d9128041e156100c90290740c075506600e807825004142c070002501c5455034003500c1000c5101400c0750703040364030064005861640d40c0d08080f250000030b8880d58105600500405400014901c40c02a0144c000d000081c559030805003402c0310a441a4007160300161029803c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 479676258 1106 479675152 479675171
    0x5121203010609060f110309011803080c03030103020910030c0302120109050f060108070b0f09010503040f0f0803101d01170c131401050108070c0602030a11070c03140307032001 78
    0x901e40b00d01212b84111401d541c000355a040509034120016201111035070000066049a2096420b409a59120003042d10022514000100040d131030b8441000075240c40d07500c07200a68101000051003d005039609032a101c09000c11701d8543d0070500c01004100b50a01460340104111954540b07070a101d007026101e0f27403041420340c5040c000044080f8040c841140c64480c81359501c40904048180a424804980e41084a1484074814805030201e0082c100c103d0401c1c00361402807042c0038903400c0100100c0c2440d43d03840f00c034500380325681d107940b401d81c1c910350014140a220100001c1c10121403030044040c4030142c1041e0306000010f001d02c00c1150b80050368450b0700b81c100c0700041c1c584d102d549503180a82001c4c4129034001d0310128025092001481c2400300300d83c0f00b02030f181070105200c0d480c90b4490240740009070118245a4844c800d01800c1150f03001ca044c1c0003000050300004 = true := by decide +kernel

theorem cover : BRFrame.Cov 479496402 479676258 := by
  have h0 := BRFrame.cov_init 479496402
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 479496402 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 479496402 ≤ n) (h2 : n < 479676258) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
