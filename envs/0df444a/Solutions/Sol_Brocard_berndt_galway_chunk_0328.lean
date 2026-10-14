-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0328
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:14:34.167679+00:00
-- url     : https://prove2.me/submissions/5a89eda2-3b65-45a8-8874-9248f7a5f8d6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 58812952 ≤ n < 58992809 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 58814202 1250 58812952 58812959
    0x40507080319080606041205250503100b120f0c0405061804142406040608160311030c0a080a0204060f060c06021c060305030d1b05090d020f060a0903060b03070f 71
    0xb40d50480e400c654045d0201c0e00d4161107110588a94590010550f420ba01c0101c0b82144040c03094170301c2034041c003500042500641048006911000e00c0c5260300c055540340c4000d81c5440e951340490b01048008001200c01c4c4041d50308a00c2c0d2500c034940f400c035106d02d02d080f000035814200142100c030030b070b00461007042455550b603844002c80816000a048248615224a4844540e00700e000361241d04203021428031345032072010081550384030782040c20142c212a41c0201401c0c41c4121a0040d079a014105100c900780420109140c01c120101480c0c1c0300c503210000003603140300880c0c940ca20500a840074802592a081c4080310070417144100800502c1841c241d0f000f1034429400b40c03a8080d40d071041a0213012152400105817841d9030000c2d80c2030341000450700315988551045000b40020034001e01081440440040c10500440c82918001d03092214090119550181c2c7c400d6801d400502198540304003074801440f209050000302c0d02c0c3c03443d01ca00905140340001d038880071541100f04249245d4107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 58815452 1250 58814202 58814207
    0x501060309021f020f0f010e06090304140607030e04050c04051c0803060d0305040e0117060702060903030703020901020a060501090f0614060f07020117010e04030305010501050712080726040507080319 88
    0xc003c00100114020b81ca42490040f50070f201815046131071100108548112050090170a400500305804561040004201e400c480d07801c0c442d100001103408540300c61070f60500b5140c0a40301401264000c0c9403c0070000b0307148100700035209403182681d00c1680e071010340d4412520090b80100241a00405100040ca103150211240b608544030b4030305603081603070300e00d940034071303101d0a0b04000080145c1c030124900c039000821140d60700c500148024000c9061400902d5101d00c8041c0031242015000543c0c002a64000c0001244140d44600100700e190f82d650302c2d136401804290f060740d8400b81032a0000400402c40c140e100801b8800038240b40c41c1c07052180c09194541e11011003207041c050001201d01c000c0c0c08424115008200e0100517202500e0300340350003022110b050304070605000c014088a40410210300c4035417240c043c01d080001040d100d8040940d008060000b503401a480002050070808680b141014011440f94044070f01d400d4076501c03115264041c82d03100c492030400c449581d040051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 58816702 1250 58815452 58815499
    0x6180906040608010204080706020111040609030b06011119151a06131706060307060c030c060e070807030305041e0b030408032206141006020d050c0709090b0109050106030902 77
    0x4030028400200281c1e41c01e40c2c1402d90f00030358006605608040704c104001e68085c090100b0a00c0707401101440c1c00c0c18040040c00034401c80c000607100d29411000600241d024281c4000690300b003500321900000d0303407100c82100c820380d000c0840b40540846404690714460b4003038100c11190030302d200058110003006010b20341e04441a05481c0085075400050f00e6a1000c00501e404e4201c80c020f81040d00d080c50605180040d507034072031400c20410364100b1001c41c2c2d10224080805520605c0401d0b0820000116403800101e5003080c503080c060800000308050700240140103d40540702c031199480c0c5020122500e40c2c0d0b483c41202c0440c201000082c0010315803100640c0d12180b00fa190b02140795028495140c1d00c7c1c1c024200302c810950740c90b646041c0c0c4840101035540580140d1504020900b0500700940390344055070002d060000100e080707040a44144483c101030030b1184410802c4206905011040c08428403a010a5038982000801d0181c824001e0782c00850b00a00700056280c4044500840b49 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 58817952 1250 58816702 58816711
    0x506030109081303111507080d0603021c0c08060f0408070302030f0d0504050c030607050f0a03110304030c0c0603020a050702010c0303021b0c030705060304020307090507110303160806061809 84
    0x40d581c41100c0720018401c000900265140c010205014504500d0009908482100d0003407140c0001040307541c0d591007030300c00c44218641c040304043c0c80780d40c102444009000941c01c000d50114005101140302e0302e80804c5509018060604140000d681e4440562505c2d030030b07145000c840d600304000a005c84c0f0110010440301d442441100d00e803210805220314507811007040e10600d5520380041c0402d02608205290030743c10101c01600307540c2800f000182c428440c20803080213070b20010603d0840503009502c90a100703103810f15483e1b0350b45000d01c0c0c018000c100d0200102c1e0141900e100110341c030352082c801c0c1c565183d1b1035203409117420050340054a03502e00d07a503011002c154082040901f145160820080d8030807605004020a0103603004141c2440704a411007801100c06204200141c0d400044440880e203040314001b0f00780d2181c0408450b420141142c2c82032a11000040c0f100803c2c5450001c2e02c0c007102959000050b856800402c000c5105080d5070310035825400c8440340c0d0500d4080400c3e80c02 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 58819202 1250 58817952 58817959
    0x140d0305041a0901090611070e060d050102030103060c0201050115020304090f020405130614010215060d140a030203180a0b07060509010b040f0b0a09020301030203060c070215031f09020408100506 86
    0x401c1e6441c248140b201032907200e8480399600228500500d960458030301c8010b010309003003459259259018150341e810f003621070b807080407603400c0101d40d0315100c0f11081015560004029503580da180d080c14005030441000c2800158a0540005480343e614040c41c084032503550302440c075191400750004003800c0200c0340c911803240d00300320014a2355100d60140070380046001c6d0109425203030a94031034200c88429446e81c195048a04001c0c0c1b032004903840d031a8000707003c4500100b80012401c2ca1144003215040c2d904180c030a0103a00d205154002028001c0000c04a140350000000d00e424080c8245044c8142d4083c50b0b4103000e418001603403500000d50142d0340b00000100c04502e0000542981c140e030b01c00d44803a580d40d840180550400070b800f031018103034110007580340d945180d0120755541d40040504000240102c2da5404543ea011800b05110400608640d183c0c2881540300d0103c05000c0022026503146206c00a9881c039903000362022074040401a0094549041000300686001800543d2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 58820452 1250 58819202 58819207
    0xa050d0c051608060405070e01050a030303090f050111070c09020403150506011112040905060a03020114030405010b0607060b0f01020c01120e0703080a050a18120809010c060e0303060f0406140d0305 87
    0x1c560848102c00010540c81000301418105810618204030180e009031909080ca14010b04c9251541c2e14240c1c212a89442c0c001620025410072a1411602c990010810f508040d60204038100394800b401031207005000c07045605a80e0f0040c00200e10603448001c061640e00c08042079007941c3c0341d01281d403140060401000310f5440d40781450414034a04003010142a0101d41801000c186210340c0b64440f40c01c3d903882c4406411a000a0038588043c01c3d0074001603000030008040000030340080c003503050090003960f111051840c19002900a203041c5038002e10644855900a600c00680c0749511001a1140f0031048194143d03100a41022100710040c3e2050200000c0040d0700c0e0002052215081d668080e2070b079240c01d0b0b0040003001c4412000b000da1003800004c1c0302da502d400805402050703001e440640c1d0f0300311802c0180c8406074982000b03058145402e4110180800120045109500850b43c81d1001000c0c20100422101507018103079007080c181c0d505600c0c5052011414030310500a041c000d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 58821702 1250 58820452 58820473
    0x21e010b0312031515070609081e09011101051504020d09080c0304030c0e091203100b0d06030c05010507050c0906040e160e0a050411011409060d0515030a050d0c05 72
    0xe02c1c1801d600c0040d01141d070004200141d14600e40c0e0100d2034610200d0716080c0760050813861100302c2c001c01401400032503076030140204101280c030440d1107420b20301c1c00500090011143e02041c7d82c01c1550b11501141407564071280101040c03003284d10608813114070b0242c41003200144402500503c40300842c4c25a1000c15501064035007016045031181c01000755503030740c04d6140005204200e50b0000e070743c030040c1009020712854003048540507100d000c0011622540e07240e0006a41c22107030b6100d0034031880c00003405a2604240d4100c801070f01d005030218a06195900d004407018807134040c014216402c4103424a03140d20301003032140e4001c50014808a400ca0402c44907a081c460340070b0080404c440301440402014603000085680041c1480080010349410f0306c0c2c0550399440120703000d0410140c111000f6001d13440130309803020300d240a0b040300e8441e01032912810007000140d50a80c00c040f0f0b85c0350172850a1600042e86400954044040c180710340500d103041e60700d18034a0504642038000d140541 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 58822952 1250 58821702 58821709
    0x9050303040e0402100320070f080c010f0e030405060a080a0603140312091f1808190210090804050904141b0f04050708070e0301110f1903060303021e010b 68
    0x3407001d40700301101c01c04a41403920420240341c99001c0e4041c2410705105610000700d209512880514901100b6203580390f1003407a10120405100e400108154400b0075003d0031018154007410109911400420501c0d2210200995900039403141c0c40c0c2c4042d04214080314031303201c0c0c1d030400d80042003d480032692031348075520460a9460b16041c00d0315070344041131001800c42c200c40001d401115640291000448900b44100780c0b840310f11940154a85a00c40821031040e02c627190402c01d03400c40001034481d0000d801010854441e8600c2d1401441340c1d40c103a0042c50704030302c00d10700c4055026400c83e15142c40c09007031022510000f001990100f641c1810025110014402ba050ba10080d070429078004d6078240c100041c110302140a5400f85150800300311846410030b4505410804600300310054400500009014001022507480200004900000503840780d101a00b4000000007045c828598400340480c212980307440007a0043e40000d04404c407052120030305881c80341d0171000100e1003503000e00c0030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 58824202 1250 58822952 58822957
    0x627010b040c0519050a0801030206090105070f15150e0f22030207090606080f040201030519090b0601020d02030307140f0904090b0402121204051306080a03050309061b1909050303 79
    0x15807000c00c1001070b6080340400101c0346050802e0050400351b06009400d54014951303281400000d004d83e600148120041c4c1c055000d49003050303404040c100c20f80ca4645405442131046115002046040c009841881181e8009030000e903849004034a000c2d9640d4080c441c2e8801000d441665520000c42143c5010708101e2a00758105019400812000d40f03800311034402c03161190300c500100f000140500001c804001522600207409180c041401d031105c0442400306002d41418011030307880c0c03096150802842d200d500c0e1017414240c0958a035000c2007801661648400c6860740300155010568940c049001009041c211200504450802501d880850100c4135444c1050f6007180740c8008000c1107103880004180d05490b204081c11044a00d03410b5548680030f10f0023014400c1c0c00880c800c0c03480900a0784868014420042280d07a20310060402070075030350080c1d40b45c0c40180618000a82c1c045241c51780c45400352184070405180140000b0030246041c00d500c144010003c4980f00000d60380e808202 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 58825452 1250 58824202 58824221
    0x1b0a030503040806040c0906060c06090510020d09050d0c08030f07021009050309040e070b041406070501050709030b0703020307141303050303011e1202060301031b030c060e01110627010b04 83
    0x10502170400b4102801e004010f60b010035107650800100f844035a510407c841c015541c08103000c620700c1d241e868441d081240f00c81c0410661480405d0009212100740c2112800c01d000b14181c2d022206104012140c054080102810440082022a0b586908202c045a01291a10640341883d116460030015240018001d94041c0d00101d651581031601303214044101d0f2a200c028090385291010091041c081c0344100c541140561041400715115502190003607036010008004900e0541d0001d400104940401e46007041400005440309010b4800c40340a0740d0340362030358002c14000020710b4102d50307c034103046912400440000400039004102650282c590a4042900c440c640e03003003050310341c19a6002c06010300c03020100001680b03640d0300700ea0540e600800c2544840240382d07884900c01106610090584c0d034035010020394103900101c000f5604100f41d844002c002d51800309559120402d4950400c00494000701d00140c002801951000141000022944c3e865940004048991224 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 58826702 1250 58825452 58825469
    0x4120210140601021c09090b0a03060f020c0607140f09010302120103061e110a0c021212090109050603070e09070c060e0303070311120703270309030506010501020f1b0a03050304 78
    0x1d09014542d0780602c803c1402c40c14524030384694503243c8034010110b541c00d11443c4603040d620394100d1241d40700e10301c0c00300244d9085001800808014030201e0020745c06900445090f00684010582180c440d161060b124441740700342ca8200603070320801060950020003842e060560805c040c8070101050201c00d8025801000001410716205040c04102943d50080624240ca0710081070600b81c521015512003201d90714040c030101da02032000c01d98103007502007004018450358880314603280c0014010480200c2c280c2e40c42c03c0d4660359405101841c0419a000e40200b00d42c4085440107041540400ea403040a9107402c10600002e6111b150484401840c502c20780d40002080058154041c00b41d04295135000c41c0040c54490206812910108060f01200802d074543c603500d000007513072481e02003588103c002c04132522034040c94050280d42540c48112624021680001100d44c0003240845042102201404401c0b203044e03000c1050800390340442d41c2c4030080e0200800403481c00c20282c4098429070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 58827952 1250 58826702 58826741
    0x251a01030b010501030c020712050f030d02180f0d02040c0e1905090f010501080708040f060c02030304020310110403021203040f080f0c030606010504030206030a060504050c040504180b04120210 85
    0x41c00c0c08002084140c0010341414101075120500a6000603400101e504801080e41d01c0e01e0703e031902a09244030351035043e00900c00030a110000c40c540d036000b444069030340b10002c8001100a001d04c0b40200300c400e001b0f644140d41151607005800d1581042e401c000321450f00c014949209000a64a811036000300c1004071088681405103040148055411110031500c1c0e10540d890320b00024001003004000100700074121000c40c041041900e228200c0b16403040080c44096540c1c80d00075a00d070001c480a038801e118146861044510a1088040c82200c01340620310713144c1036400344a44003031080000c02480c84200300c001903511078640c544020344441c00107410304071240003c0d2407421108981a034480c2d00070409020b60f5070b8105080380c0489a064405684941e070307104150340140065441a0f410a05000400c25143c510200a201340d0384202d81c100250310721030b102c0071b4143c00c4606006045400060108010421680c02c45240002520403200307042c0000c2e2044064580c444040307030744529403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 58829202 1250 58827952 58827959
    0x606080a0201030b0901080622020402160b1602070b0901020f03040906061101060e010303030507030905120a0f080603030912030c0a060204090f0506010212090a08030310090b1005251a01 82
    0x540113501a045003141c800c10f5550510b0304050b2280c01c0503104224504100d20b0051091400e50340883c60250000c2c002c644809542d40c1040c2d40c00700d80c0f9411210180303100006180380c00f1621140b04d900125074001e10300c0a0404c0d410807601e40c082c650140c10341c0b0504c0790916607071300300b0401000540f000140200d030036072600b40050012040544000d12590601d04248103401524250302e04480c0c0514003c200340d103c25030300754000c0c6903460001e4024042c056000750038030103a0f07000782409141c5640d0b00c00440a104001c82c3c1d10782050b60400d6140c0c0081000000030f02e0201d038040181d00c2c180058074540040700c400c01e8503040100008890740307074021070b0401241100b44a070304082400584144245c0c5004d000003500c48684264121007a200841d1903c2ca903110300e500b0348090104841160380d20304282503030f001c1c24500362042c400c180307040491108660401207a803c50420058071264181440100c4044c0015031700c10580c5001d9a010000c000452041c0d00007101200003071840c820103504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 58830452 1250 58829202 58829207
    0x60409090602090306060117150111010903020604051e1921020106050a050103020a020c12031b0303240603070503070216241409040902060f0a02100b150319090606080a0201 76
    0x1700420a6041c0b20f40210149403501500d1185139000c0c030401c01c2002841200b400603115003080b400819100c1d071030045514100342d000200503000b03d001c3d1040f0b81e425000020518140049451028241d07004103114202c0380e808a036041c8507061241c048501c0314000341d59201c00b08039007941c401005079140e000400c008d040c81854440505030a19041d13284c0469074001960721485811001d001d0206079460f4440c00030700723206840000d06a41c4400500300404d144496032a0026950354061030501d9250000c2c0d0803010704601c0f0380703040181185007540d4070a0381c1a43c09401c010034950075405400c0d04421106040b903140f0b8040d000c03074040060309203101c0303070000c407450500d245190902405100c22032000308414159034802000b21408205502d07684045109405030103a5440203140c0441c2ca50811034021691854080c0010703020054401c50f0010400749451902c0c911540349410800718a4448101c841c0d40c00c4000220808a82581c0c10b5a8510031505168042c5500740c02101c8c24500315079 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 58831702 1250 58830452 58830463
    0x10080f0108060708130507182007260d110a030518070b09130504060204030506130206120601031d010f0c02060405030a08070909060b071416060e0604090906020903 72
    0x3116002031405250085000d4501d51020300803142403451880c6200803c80c01f0841e01c005060a03040c1030340316400703e10600c0050003000c40110030003060109a07055015000302914242c1c0e17007202d0f00c04848001811000d18000400104007002c1400704421069410b02e4090501c059001141142d40d8441c00d0800800300c030006002070015250a020344000500000740c0501030b104030220441c2d80f0b005034400944150103117510700d42d843e401e000401082c8200369001c0c4c8200c0c3d000d20165961a61890180c40030580c0940e002507002c90144165034506030200a2140d1010060400050080480300e0100064480002d10a8103079100c1c28a001540e2040c05110311011f0180010586070a241e034410391240100090302d8200510500001c90b4a407103330700d0880041c030140304208803940e190b044414045c5e01c00241030b01e104111642c1c540e002800040c0005042e40c0804070141000e081510480740027218401e0183c0c0920244000b0580c0b1a5034821526014811080140e44480110a150800 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 58832952 1250 58831702 58831709
    0x4030212010506010f0813050114011502030c03070314040e0405010c110c0a0312020111030c070501110f03040209060a090c090311010503010b030411030a0c0b09031002030903040b07020f10080f01 86
    0x141d06102c20b021680c0d800244000180403607003004240e6580b1105440c03181490008041d120b5800e100600c5808500c03424400d044e01d00200a551021141c440300380d03503d1081ca5110b240a6208004540209100d014100382e00d14003459954580b075928415921030303c2040d903003907403607035521201402c1c059003005203540c0c8904031030064003240082c14006201c100341403001800460350a05564403541c0300394042e680c044000701d0800d469003442a90481c05420542080310650320f400d0140030040b11140595642c0c001c40002e00303207503640b5942800032021010b40321540142d8034842c086800203441c068017409040c04d58480c1c0380b0604e17500700104031080da40c4215041c4001007005024103c0403030200e0b907100350041501c6071251400780103e0f140c10394032480a8105980060301141300c060a800400952000704e080b40d03036401102003040101d10083d1507011056100308400c0040c80c08440142c000c50b80005c1444481c402000040380ca00c401340c00c0041c0015281e10100440944004500b03400b5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 58834202 1250 58832952 58832989
    0x4020f121e010605030703020f03070302100c290a0c030f050a1a04090305030606130305060a05040b0a0e1e01060317040e01090902100e0d0c17010e15040b06060403050303010308040302 81
    0x2444c83c140100e1340710b50280c000039006003024401465507403000c0280c0001907074040c20b42c500801c90082c0c01801030014003c1226061801c41a400c0f00c1180558940900010114507903456152540d01900030580c0100100903d6112000b003500303013400d03100740c80c444c45800f032011588100384450741e4800d100d20400f051090f0301d4100380d900401d6022060b264401c005881240e502c009a0103030303c2d01c409103680000d14501c11340d801c1040c180c215070842c17130090344a0307030a040b641c0c2c40300c11290054079003083c030094080e4401410b503640450603644584034100b400000180441e101c0d00d511504111480c1c0642d000040000c040142d03400100c001401010410402c2100f9100b0b60300150007402c6044401c41049500454250075030f8514060340207541c1e002c0c0348140c031070340d9568000402107164029a09154a0310300986036844020541d06400c00003100c040c11603903500d69901c40c1e030b0400680095002141804044000390081005501031741c01060b20a464500e103204001340410410f442042d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 58835452 1250 58834202 58834211
    0x2090f030f03180607120327050c060a090f09020a11030703050904020306040e0d0201240501021c030216060905010b0607020f100203090d03030e0607030c0f0804020f121e01 76
    0xc48000110a5410414503005202020f2907003d001410354028103c003c1e00007440d400c601c1034a079030107611240f100503103000441d1205c22020f64240c00c103401500080e000b50000e2803c0e0b8900e1822030b006015032412420400e2280b5101c00e0082c900850a4120130350250340050810030f41504440c001541c0f452000003185000030959004140e0300403004098003458000c0003040041d681d90b00607031076820708001190003510700000c00074040c2000488420000c01d011096200d00340045050800b5101c041e001091804180c0a444d046610030110348400c26500780f1041d8009145940246045c500822000c500000203060980c2101d000307003000e9101e440104040700051310f804000d041202c030216101391310510016800d9040d1700c40c910809500903d1071890703d04160300340d8858516000078004032901e564070000140c08840300306605d0700c0421800802c10303441c40d02c5164080e52042c0301800e480d480044c5d0b1404941021070302d026003034603078200c220408401034441080d001102c504000920 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 58836702 1250 58835452 58835473
    0x6010503072306030f0a0e07140618060703050301080c030c010c020f010c0204021903050a05091903050f0325090e06101103070308060108131a060d1502090f03 70
    0x350360302040d01c5074540000400002c0c141c0700100c040082000c94000d0046a40d0703181ca01c1449040c448100d4100c2c0340c4078900a00c48002c21000243c0c1c034265030700c0d80c3d01d18a044043d6010015203421181d08000e1460b00849200312513200c0c00c01420705944641ca41c41e44039410b01d90014140151400e51600981c00201c580c03a0307036a44145411b0120b03070180ca041c69440004401242c820b0300442e40690414000200028856a05140d0060b0f400481e502000b85440d001d00140581c0c905403004050b0b644031802c045036580f011001d151416200e402d00c20b28100528501c1034007600704a83c90345e0120300b011201e40c070303c1010203546100b54006160408800342030054000881d10003421042c0a440146500146140134040c40441390600c1001c49444000600c0c0040c8107500441d199400100c060700407810000c0700c2081d0b408165408152181c0411400a00c0301910b98000c0255030300090508190b80400c000e4600058160050240940c2d200f01e81810f00a40305e486028450080d801f120307819 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 58837952 1250 58836702 58836709
    0x6020703120c020703020909390609180907120807061d0703080c0703060e0109030e090c030402131404061a06070b010b0c0a0c0e1f03030e010806040e0d0e040e060105 73
    0x501c180c9a0488403520ba44e11810300940c9090940e05d50b42031604101108a000c4128100c08485007024270049101d13902200c00c1417110a0240c100201e42105010500c030340b00c8054651256888100c880031034108503551031400c0c2005a41e0482903613542c4000a440c000e006050060b0b071049500d0717401039a429608003030038954403401440302034100d04000c1002d100301481400740c0f10080d070300241d0a004c0280300b581e443c0c0c020641b00b017040340410a554141401820408102032282c60316189907811a5515002d0190041651090800700c594400c4400b07510409086140d000d640520000202c0c1510b01c518911446030307010325548030380828000c480029903a941014156214160056121200a09418a010100c1c4401410b5402842d070114180300c5070807000d03110785486804107980e01c05148039422110124000503000410044030643d240d4000d101082d000300000d0030000b15030005960407030904c0c0e4001c00b8500041c5206507642c40c04d1074680180c401194405028100552500000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 58839202 1250 58837952 58837963
    0x315060906031621020c1e0a150207020a030b0601111605010315030611182407032102070201021b010903020d05030f0a0903140106030c0b0d0b040906020703120c02 72
    0x5803620201c1d050f991285851280b4043c1c018031280d2030740b10380500301c15034008001c0e4001c03562450103072003000001c6034080072814501410142c1400501443d07909034075140070f00015071803c5040d2503000c000f00401a16074940810056001d4200142141003841c0010810f02c0725201901ea20350003003d003101c1012101114000b100e1003400d000902074034403c0b045002e004035030302c0601a9407402c840c81000c8002c4c5d00081825021170b90340700b22100c0c0b1400c10031500314114440c040c280c050b00e2681e042c28096480040030003900904180c0903c034000071894011581ca001c5880d0000c1d0045900421541c040150600a24880c00ea24261050782d43c0020401c0c038043c80040d1062492a064406002060044840030440c0d80071282d43d481800c41d014100c6030b8688021100303c2640a4940b540d00d030184035150640303034810500c0d81d0342c0d8174090362804540c01428000125580d601702204503944d441c4103401c0458420000940c9070405800c2c082c0c000d61041601c40d2000382048591960948d01103071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 58840452 1250 58839202 58839211
    0x40e09071a090102010e0a0302030a090617010e0612010e01021e0f0a0c0305070507080a0c05010f021b060d0207050c090c1602060a09050907080405070f0e01090903020a020d0602031506090603 84
    0x20000d803a10000b400403800341441c2031011055005011455050690100c010030501d21561103d51110350350b020100c445814442da203e0b0880c600c1c40c0180406040c2c01400d640106008180040300d4004c141c45a08446000711898000c0c1c0d070010b065400c080e00d1a440c100c600750401d81d028240410f00301c1403e65440340c2e44018080101281c80c0600301400792095807030058109086407500c2d510342212035a174620700c3c84155078450222400142e60345c4074003d071000413100e59018002d0350882d07208240044020340180c650041044c03183c013030180358500c0a080c141d4051001403003043c1e07440041c000d201c90b01030500b8068072420827221510000c410420f02c0060303410740d0455940c066640e001c0381c0880950300690fa1120741360f014000200d51041915016038021000d03103900f00d45d40d0700d950300011400d218074405509044010002e41005911400348a406070054075000c101580c0005c180d003181d41c500b1100140d0100500070040b00d164074000e034865081c1c5900e03241402d0400040c515020082 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 58841702 1250 58840452 58840499
    0x30510091a270a1502030c16060b030c0d0816020a33020f0615180c190306060c140f070e041122020309070906061713080901080702010e03030a02040e0907 68
    0x10205818585200032140081d07823030b08400601c0ca456180120141018505851191183d0700440d5014a040d0b58190007040d88000f2507450b00b520b100144c00380082008042e640202981030000c1c001c00b42452980741c400c00501012140304400914840b0b10000e1506034085510003088060a020000307100c03904a2005508107448800d800d000407a400b1294a4218584280e20244541709032448064100d944102052920201c5070705d0084080384e205219000002e80502d580d40c02048410440707103000100c000030384082002d00720000b4501507890744000740780319a400401047c449140404061107804540c10450345035000900c10641620342020044a540040403480d41e03c41045000024010480140030081d690400501803403020315500b0348682240000880300104046c00c82c41c9541d02801d1203082030f5a075801154502d400400c07000941d0350310010f0304004107040000e948110001327000581e40b1410700d0072103502c20402400000e016407100d2418040c040714007081044000555 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 58842952 1250 58841702 58841707
    0x60907030b0a02070f0c09050a050603060a021b03040f051f0203040b0307020f060a0c1713030c0c0e160f030b030a0213020405040f06030b060109030510091a270a1502 73
    0x1e82c220001e20030000c1c002c0041426940352400c00040d9200c0c5400c0718114034007009107542d1091014156141143e0695040c0c1000c800569205495406448a0410449808174013010f42c241c03146154455044031001000418040100389007a050302031412000a00074000c100704070b03102954031700440c010300c03864900200010f507010f4800c0021003d0b85402904441d1203050188903031300101f08098060f0300007808061800ca1100550140380d0040c501d0707249031959a045910101c0745c5500c13520b0304490300b0f80c00c501c0c00140d260241d44507a004491940701103403046200f102c040c200c0741c5021804c41c14142412030381c00c5950b8020a8060100d5019144003546c001c0c2c401021000b44902c2c1c2025900c0b03450544620340d0701c0201d50005040da48a07800031600354840800542c2c854400e4480140564130138001d0600c1da00c0581c020a80c40e601c102a00380d1042d4203000080410f440441d4081d0490a411055003501c1c502d0101c0d802e004500b00000d44603242098650840100706c1c1d44080810301c0c3c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 58844202 1250 58842952 58842961
    0xe04030e0d0308010503071e03080d200c0c0f010813030908030d020903010b01020304081908040b04121a0601050703080414060103080406080906100302040c110d02030a020609060907030b 82
    0x40e22240c1994200401c00300c0820841d182c042d0000c0020f0107014068070450303401080100038260561110144070b8200c2510910b1661045aa6800b4562a203c0542c4460150740100000170707040c02c140305071840c2c2503181e003280144580b1303080d44115001d108060700e5a80314030a9800c11500c40e08900c0c4459415600c6409090941d03100b0758961001d441032000007504410310090f80e001d0300c125403080b002400201c040100490b500c0c01680106070715900000c0d1103070400307078080000e803252600c10502d840c00c10366580701a0005400641c048015a01d05613000800c1202182c1284400f0015001800e401e042c0500004c0190041c0b0b10014103002038074020500703001d004420304640c03244004c11200c044da140c0c0b600b02400c1d01b20b40304600200f40d4000100341448000300d00b5500c600d01c903c4000004d40d142d9000c0001402c208a50b100c103120031070400c810400c10910640c3d080b4001e42c0c006641e10010500000c0c0f40c008008c004c900d26412010901c00d0094000c14580216078000c08404401d80f41d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 58845452 1250 58844202 58844207
    0x140603061206090109030908240a110706050103150c02030a180306050c0405100905060a12091a0612010216030e0102240f13030c0314130b03090d17010e0403 69
    0x850401c190760511a900401946020540080c1212442079171401c04039039866403115550a043d00c610515010310407036104c0a0b00100341c00a0384203000100110b202004034030701c00110381c01040140c9145440302c00600502807402000006001e40c90400c00a0a5400c0c800135202d02030350700604200700082c0c8000041025a440b100e010707542148080009041100b07a44815600c05d200b4540110f400d42400f50529029004541c02c44801814952034800300b0007040310352101c01c02c103020307100399100385010100302080000b581035920000103440c0c2d420720341e003007005c042522a11091140e0041064041d052082070907459040c0d4141020810b0304c4455005034242a00c5441d0450364200580803501c0d0146400c032082d015074000c0c0d1841009844404002c4001c0314140e1024000c90b070507070328030030010f4840c1c0c4001d1841e44483c107a613030a0905502c10031030b07504403941c00780740b12200110520032051000c0c01080654851810a042c0fa1041003d210b0483c40c1c0520034509080f0034000000c05260 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 58846702 1250 58845452 58845469
    0x30e01030e011404060c0f08010e041a09010507030605030a021c020a0308030c0a08010911030711070b04060306030209010501030506360c0703090e09210405150a08060a14060306 78
    0x185158000c2c440103d20380490520088201c4041d03c0107400c0c0302d05544010301030407160078518815564400d0a0303003041e61902d01600054011100b104065000310a10803440310258042c42c4a440045900e061418008041d45c003541c2081e4881d0308595440310040e507d6560306000107018415002c503200381d500005e40c644c0310341d51000e404191b00004000c8544140e400801130442d0369140c13585247d032107204c0c1d50200c80501603140d659000800c0880c03851401a581c080c6221020f10480710500d03200d030341c40704854100e03a004c1004a621200107000b14905051580c0c0500400c0c0f900300a940303890000964141c4104080040e415000c42d004400102d401ca0504600d0b05280510445800c3c043e0900702e42d40d020200960001d0014000030403d400c80c400214021201000103058025409010002d07610064a5a104a4004000025940d00c84030320041500310202e41c6240ca07a00d84080103003404c000100118803035100c0b0b00c42070003502031030f500c0c1c400305840c142c41c04c0d0b840e903907890041190301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 58847952 1250 58846702 58846721
    0x5031e1501171009110f070302061b040e04020909010e010618050a02090906130e19150605031b010908191401020705070902070303150b0301080d0206090604030e01170f0f090a050a030e0103 83
    0x2d820002e000000d01d900010520b00a07072007001101c07001c041c05038bc28106401a07005058103040414045001362500707002c0306402035440c50001440b00b9201c5515402c46403140c0c8450300c0b543c103000a0074080d101510403698040003000d01545803440d5007000615442006010303502c2440c00d884288820b00c1c01d6030003142420500c20072146049524050051220560786045132030000c60b0600d007200c04020302a250480d40c018006144104c0b01c0460804844e6605c0402c074100080712074001040d040400c81c2600b511021009d041f50704d41642400100c408000900b00426801080404000b810002e4480c2c00c039a4200c40068071101240750890141c4415184007885884415021036540c04401c0118102d503509022105805100c10061307854410850b450200e40d0400c41c0000c0c0400e025001c1d52100310740c145025503042c0d0300c400d10607610075800d4440e00c20401c0030038100500c002980c04010707040007090000342440481a1356095803408040401030402c02c08802d031065a90003078104460b0b9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 58849202 1250 58847952 58847977
    0x110a0210021011090411120c031503030f030a0605030d090303030c090503010c111903050301090207020609100f170408031503031b06060f0f0604030305031e150117100911 75
    0xfa01428084600c0e83d40000e11254801c0d0300e032a500348040c070f060400703c8403494815006130201c1d54500412181c4c0c1d41008011485000454940e260316035020f000900c418080c81c3e800701e4480c20f00b60264005c0710003d800c0580690b115000728010315420460000c1101d51514000c600b81a2820048401d86616804580c0641c00c0c260b810b24256000f81c03408080c030415008440c0d0701880b42046403a007c0c65024060045001000107010314081c40c1c0080c007185001a0000e80b40543c4280031480300302d00100f0103000a080d035038003c0041030340114450b4001c074003000300d0111800d09844220306440068000e01110403060b48044040c0ca040c011396201c55014030000800144c0120b1903a00d03207008480c0320344100349000500000b4a4829a58600450054696410039003590380070b941d603500152166078010310300c0d10302c00348084910800d40e04c40c2d62024050005640c1d1400090211030501182c0c5912207185c1c2e04000d4041002c91f0b2641c202e0308401000f00f078026110420280911030462000403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 58850452 1250 58849202 58849211
    0x106050a03050307140d0c150b060f0c070506030411012607030e01060b0316120207020901230916031104030503030907060809010e0307020906010509030610090b01110a02100210 78
    0x144207002c409844c4d941d014601000c4c2c458540018680c0b01c1d140b080949001c64000c40079900805c285586a5000d841e50410000d000880d800000f122500429800c3c0c18000780029010884c000c10700080300140310948031182141007603500e099002801e43e03c42810040010148182c0400740900d1940021031481c0034110717400d00f400002e0151144c1148809150308081000801c0130145084901c20079005012204000541d07030304881c1410100070320f03092142c003800b80c000940e82c2d00d11454001c1001007848941000c1c929103403201034140c4403100e44921a08020821403081660306080b50038143e16000410691440032608103000b241c0024100d844044100600980002003030000c1d210366450b03411060b80c1c0c110a95007030321040311000245810501814005080c08100c83e600007005041a500b480d14079400309180180071a00d6040c5060a0142045261424822186034003801e10702078112030b5082c030400d56140b028050090051300e0641007001b0091003841000c03c4561314000900 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 58851702 1250 58850452 58850459
    0x307050a2d050c190e0a020c1609060f05040207020123040b0c070905010806010303051801030e0d08160c0c05090606070503130501090b030f07080901020d06030b010e0c0a050f0c0106050a 82
    0x1562a00001c02071401040c0740d440c904407214409804d907080300e09101754000e06640d800b44404c007940005c1c2c070b100c0c1030340303e1111030700b00c50a400c2d01c040016003018040004c1080c038107000080c1d581841d038401d03800f6910410810f030140c3d07030000600a0520540720442c84409008040c0a05441150b000f624014804107641c1c15002000c142141150710108003402a07907202c251090301c0d88802c0c80014040f480030010355a00000181455240b08014140081c0702c8600c41445402e100018a80b440020b8000c0b04200d0700c400608100040c4200603c0c09142008090f51448041d203254003555104009560019407e69507060884000390ba01600b41ca85840300c2421a04040f0103134000e85021500c6043d0100d42c43c0c59410a51348981c04003900f0700e142351140e905c180c0f88000c014244c603045540030061004480d03010f01664004602c1044e00d5034103589002c049847d00d60010b0030b01542c0c19000c2200800082d0301100b40c3c0e00c03034101c1200285d6500d200c1c140b150300500c03584d40300f140c22004c4407a000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 58852952 1250 58851702 58851713
    0x21b0a090606050c1002030720011506030f05101d042901030b01080d0504030303090c05030f03090406050402040e07080712050a02030103050124170312100303110307050a2d 76
    0x200000034039a82140d1907140741c405c004099000899844001850001c1403608070ba4080083d0034904c030603940001070007100c04088107600d089580200c0013007900c803101c9024045e45841140d40c07050a40c140e19843c9810415030201c03a40145912858401c244070100303080c4403182a9240d50194105030418201d595031420740007030002448140d40603000d800c0002241709000c1182d2a0421960382c5081c1f6060035580c041c0d00422080d08159013480d06804041003a490410243d640903025000440d01c0e0454001080180c4003981c001030b02590040c04104100d105081e02d0036009a03a03414509000d6aa411040311710700b07244281080141c0c141024000c4020040d8000c60681e806507000303100c080418410044100810141d00614444d010410407101c010320465221036280a01940e260880f11011031001141c20707208507404c1103c11208004060700500c99507041c0103040080d50901c9034540300c66880769048240900140c440c2055030020390201c1c7d14050031803001020050041c221030800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 58854202 1250 58852952 58852957
    0xd0309060801080318091317270a1401020a080d091101030b0a0504180506040c0806060d080a05030606040806070c0309080c060d090f14100501060f021b0a09060605 72
    0x1100081041c0a001080700303a00031040f1507801025a00029406039a40e00740710b43d5900091a03015002c41c1d1488a2002038210241a0301c41108808182d48403e0f00140c03502181c14540e820030041070204000810548406411008031246203450f840502041c10060b03081c030b001c20720000d10450000542c0030b20f40c0c2c0290b1101074001d00500c0b5002c22243d11000650845440c3d00341c0c0d80d440000408200403500d081e800020341081d001c1e1480104011565419140070f01c19102281d40026140c42172110060800805502000450b585003503519141c543c1549807180700000c1c070030000004005001901c80e00c00311002480c100d02107641900c3d01260040c6800a50b0808400081005500140010000039080da181000801c05c03442d100c14624880010a54110102c0c1d10321800c0f6841c00c0800c4001000140c00b0b20f14501800c091103c9a02502c01c890050b040710040c040004155051a680002c1c5c03084a2002c022914000305601030001d403038913400b6885000303082c0c1407050208100e42d0203000f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 58855452 1250 58854202 58854209
    0x10906031707050a06051023090a05040201050706091707030e040f020c07060309060b0405010e0115030507090501050a02010e010e030705010b030a02090609180a110f0103060302010e011103090d0309 87
    0x20034806900e206000d030840e910910b40c000e0a542d00000e40000440d03005d074010f07a00407a14228682620b80c1d61003000c0d541800b150b070b04030914914a80b280c40c1070f08100894a0380500b503400100a43c1c5807a41c0003074090301a800014180540e9661110b0411040b84000184904030800340b640300c10035482c00401d15221406114041c0d0f0030419800a104040c0c005d5078800d070a11030244c109681400e2044000b066214030a40344251144155186511940309890213403d00441c0204650304060078082005201410081014640000c00c0355091340940f5000c1030f1442480c01d142c0d40c0c1c0d15548102c2c0501030751404c0503025440d05525214040000000b0b12009100790000d002c05465401090f80b140c0703980300c0c081d4204c0100c0000a446140c804d000591050b20002040800340398402c0d01880c0450f001d0040320442c0a03200205003030300d440e250344d42540200b464113100150541d80001c00e0003d580d486503040c0700d040f49014810f02414015075140c5503000d048042040018100240042c0d040e11 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 58856702 1250 58855452 58855463
    0x207081206010f0c0b0c09040204121b0b03060a030201083312070f05040504140109030201020703030501140f12011805030d05010b04080601150c02100e040c02070303020a02091e01090603 82
    0x202d240003450700807640c0304000e45d08211071600343d55441819280b554070102c603036503010742e0070440031910450b502d61030b2004500450364100b420b0b6140c5415100d25409070800d903403c100602c100580c1c0c1d561100054140c95081c600100245c981d88000c680e986a9a80c0e51080b541030410044240849a03048410f09881110b8800c4800800b40f405034541505005a100071000c1e00e1090210741000e4010350f400a200d9807a07912640d0005800508440741aa01100180d4000a40e00207060303160003031501601140c070541c1e800c4800d00c0300098102e486500903d000d60700400400b407242c6029845001040703c4112800d18524907807a0a0345c6981c4100c42042046140c80000f0032000369140664060342c4a07070008020590900c82c0030004600030241e4142003100e84600345006880c1c45080340101070041d11501c2950080c001084103442100304000b0856008120820104e035001400a80060701940d8043c40382d00d501c280750040b005d9042207030310344072001400007400c40e0040c2c0c07103001203d0150 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 58857952 1250 58856702 58856717
    0xf0f120d09020a0b0c210c0c040c0e031501060909021c1512240203040c0611070f06020105070e010f02031c090f03020303070f02010515090a060513060e1515030901020708120601 78
    0x82c1e1b10341c5040c050a03602c604030340c0c014000c01090b42407951041d41ca03104a800c0030300020310100b00182c9048900030010b40c0e1038501400410030f0030381280003800901058002941002e000c0c15111542e01500003018408944400241e4107a4103480415000303841e0052041410318902e00f00001c05460700311800c140000a500d040584901e50304c2602d0180f40c1c0b04844140007880d2142c11100704859405e002c04c40d0044e8080054040d4a14076400002d125a030008261840c2c00000584010303401329a080c1070142418482c2c08a55000c81141d9a15000d413000391180030390034070510000d0002c081d004140c0c100c01206602450b8000025500c0703200c4035907808103007032280c070400ca0a81e5019601040f8001482000d002d040c40e2851029500c02401e40700010603594a40c0024007400c94844801002607030f81e1028400652100e281550110900310010301c0180c00c900403034501c10942144801404001c80071481c07140c03082d0101e980d11908424056102c01d4582401c02c0401c0c2d06503041404140ca2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 58859202 1250 58857952 58858003
    0x703080411130e150c03060a06110c131406010c030504060f09031709120d0206041101030b031203010f090b0f01030b0604090603150513030f0e030703140f0f120d09020a0b0c 76
    0x174403c07a4421400501704c52030540c83d0200580701a414502d0080c114041c10709024204d8070b800754070072542c42e20780c04041540302400000018403180603020b54104800d030045034001c2a0480e0460b401c0320064a441410111020400c807084080e581000b45203141d01040044c00d0801840500082c11301203500225010500c08981d96070300c0c00454040140c0c22900005000c40d86003400540d40d160306041c04504190400d002a0600402540500d40140080010b00115108001d40c81c090160000200012103050002807500311b940f540c03c904154444110b040ca46c9c488106031002010003540a00001d0b49900d061143c0c2e000011041c0324052410000907040e0580e01505c100070b503019103801030390520400c000c683e050010094075400d031041040000002d4100e100b01d04001c0b107001c000e4802d184841d5801030178402414480c411382d43c88250140c1044140c0c104480c001d03c1d111500040d9042c40c0d10200e007220602e42d01441c2040c0020641202d00751001c00c10304588201c1000c4032440050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 58860452 1250 58859202 58859221
    0x6031407060915050f0403080307080702120c0c06070303060312090510050a0f03051f080c090115080c072102030a02150709120c030615080606060703080411130e15 72
    0x89920032000b031070f21106120500c1030b010344001c050414508900901d85170f141d03100e14460740d00607900782001550742c008000489506014960b0180300c032007000d51a00a90b499003030b5a40e4004c400d110310450b000144030040600070b502c10402940c0c800e4902000c0c0d00b00c268058045400341c46040d0240107400308482050748203404440c20311801d82c8175181e605410450850040c5001440c0021520041101e01e4184062020b503000500e24400240b106100010a1018a10041c0d00052070900701d2000d04c0c03480c42d04040540d03400f80030788820f2504d0b082d2908000c1a008941c507950b1418100482406074050341c08401000b800703100d6000c46040d002d0310b5403100301c01481261900e0000320600c1042c4280e4000394480d100503401103102d50101610703500c950081340c0855001010300e1260710020000c0010502100d980110101e07109401c001198a001d40b08d1800280003d1407086441c03071102c403d50714148452183e4110f520208a582c2620200d01d9840c0710f0300200380c8103444060005203d803d07 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 58861702 1250 58860452 58860467
    0x703020703050301090207140304120201140903030901050c010f060f0611070605030c0708090402030a06031a2401020a05060108060a0b0a080c1005120405010b10030b03060601080c0c010603140706 86
    0x207600d9507480d0724580ca010003940081d00131001c1250354154000f41440032500c2007002d00702410300a4410003241e2030743d1001416104a058900018940038090004541c2c0c0c00700c1951b19440b003e08003941d80e007042d50051801072107465807030f03040d4900d4820003040a05041c4155420748203c0e8039404201c02220b114141e84410324890880041d00410000c1c00c3e4000e440041c12041e4440c148050801b0b402000080c1640c00440382c1c03242c559078928041040c4042d412844508802007078440041c0d04101140f402222509003002c140e0760012060800103034820001040728942010599840b0750f101c440c1c00e5190036040c0c0d10306414500f8420340041c24940103d01c003007240c130402d004010031070b8000f040c8001c400510104038140101801b035100d41004440c2c1c4144150310840000034820701032020080903030820401c580170141b03044c0c0c0700d0985480c006400344d000034007420100c440750f03108410584a841840c01d18a429400d1240000401482d6140701d4503104154040d1541c181c1c88480c211810f0703 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 58862952 1250 58861702 58861717
    0x3070b0117010213060e0a0801050c09180c0412171606051b0d2f120a0b060702040e070503010e010e0706141c15061205010e0108030909090c040606080708070302 71
    0x4d00b90804000160164055080340c0d17101410b9492165074a840702421a902180e03031103400080003070100801e28200004840e1410360740d20310411820014a805168000c80c02244801c490036032401060110360f00002510094881050360f03030301900c0356001c5000955001c01c0b1000c86c240400701d01c41500054040104c80d80c07910300d072810a240c510800c0080d00900715a04440d074000d41450b07904005401c0100c0481800500b0385a4841840d4001c0c3c0e4203500c003c1c08801044e00e0070074030b805165915011a000941c046030302050580342e0034221070502181c0e60090360b0541ca010f10120024406400c00c109000002c03080c1c1d43c406a9030311043d2070010924071070b0b9071124010445070b181c15942007002a8103903003825000030100303080c10458203456001e80043c40405e104409020300f8600d54001d05d40075084079094003030345515001541f0b03945e00601450324400d00c9071071700080306004100b10811003040024418401079640311030113000324030f00f5201000000d80c40c40010310781341d00034001c44072413 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 58864202 1250 58862952 58862977
    0x2090a0b090f19050d05030a0f0305010608040f060e06131104022107020f030f0309010c0c0507090b03010b04020d02040e0c030708070c0f020901080303010501030b0312041203090803070b01170102 86
    0x40314591010892444103d021140507481c20007004a0300361101050080403510620056640f2000841d026190700d00b1801c2200805041c0700060005551101909030010303801075110507141b215103071000250904901e81c00c21445041e00b003056800c168100010007a019103142c070f503039980000c103101c00d82c401c81008500b0034010322001a0006010902c0d150702c20918415900349d00380c0d002030030b402c56001e2500d0b000d0001d0003006014048100384500c442000a9040042c4201599900c0c80e03141d0540b8800ca18805995842200c99614203401544032600010300865491031175400b0700c00250414001c00f41503807a1200002d868090a00c2124050340240d00d49048070360311002e048682c000c141c0011204481d0450282c00180c4900031103034080e2210402070768503903041000041c100c4040c445120710a600c45800c0110940740c1004450a8034200703150319201c1d4456080030b83d0a01541d5000981a01c00000c0e401c00384411106114182c5041c5c0842200a501d640ca4440c20703401038508072942c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 58865452 1250 58864202 58864219
    0x3060801050c0708160503040b0703030614092802030a0f0b0a06140703050906070c0503011503030507120302040b040e04021503010e07030f0e01060e0405060603060403081801020702040903020102090a0b09 90
    0x215030710742c010b410301c2e00d10044041180045d680d03d0600b10303000b503440992541c1011940d001019090301801010b480098150700d854016200055441040502501031040002450b0310400f440780c4090380c0300050511066640e4140302d800304004081c030001c1c1300d003030380d1820105183e1860204100821261180c6e941b40394a00348c040e1120303090748400c40031814401e00b00720405981d01c41401801410380500c4450320703254a00b5027803501791140510783e0519104440422710000b50484140d5100982190100d50b80d529503101c164000d03c0303603030080c100c0c0e010701150004a00440c0b4141a200340d1007a19a511403041c0d00c1c0c004e661901081c01200c0140e43c0c460005041d5601c01e5000764030340d035a00c0b030012a140f0301e241d085c03500b115a1038010420200d440c500b00400c3c404104030a0750824019001001d81e4980303a1001018000081c280c22154004001a994080002d4050303d4056400500800850b0f0407484e010b8000c0d8001030503140160b500c404001000c000304010368481030300c058400e10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 58866702 1250 58865452 58865467
    0x8010f060b1b0a0606140406062f0c0d12020f01090c0509040f02040203011712090a050918120a0206060307050a1203030f020403060621030e090c2803060801050c 71
    0x580300722052404001622030007007510041144c40c00b0b6500100200b58400c04446890320a010541d041c0390050420f10007202054407c44000030782c0034002240c02c0300401c1d0441d000c00b19143c10815001103c0ba48000c8030303a0b11109201341d018507402000d07401d17000c440910101c440e00d5400e035101004050000c076846c000c1006581881900554414032481020924002d1980003a080307030002c1e080001000040764507282c00e0541003003c00d103075541303100541e400c1400410004581c0d03410340c041c09008500c40404544c51008050750818228001000e443e801e41d15020148115000000004014840d5402003151410082000d005441703020b040811300c6400c0440802034594281021001c066650900d040f00100da4130180015610800f404121507250600242c0c10f0807840000e025158095405070000131340203240009016019a14100990303540c0014809601812400301103803a08010303080c1c401c410740c212206540840380c03000c00c900c07500c41c0c00c0c441c220b500403180b00515060400199 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 58867952 1250 58866702 58866727
    0x2030703030e0102121005011103040e010b0a050f0706020a090506090315100f0f0509010611060708040f0209040308040215070c0b0c010618060504050105060703081311030109080408010f060b 84
    0x1160340b2480b400025207403a0304001060800c00c2c0403030707400e070403112086020f00407503070b22004000610f02101c000354185428840060050312040c03150143c00280000c43e44c078018065401d0701c04105009858549481e020300b440000303544001c42c0c2030000f0380000004901c42c40e0403c2070b1181c0e20310150040040b40c0c4000b2401804d00c4d8082c101c3c80c0c001c6602c440c00104165803d428401a140c6402e581000310310340028000860010382101d02440b5074031040204604002600c6903001c0d00c145003d0002d500c2e6418409144401e0b448069000401e800402040c150407a03111805140300760740700700f01800203262404080c01521002001981c02020400440c1d48a01c0030740020b030340c0d4000026080e5901c800f01071600308a201c00c1c8542680f603882c200000d14007413003201c0c01440c090391202c1c60301407203660042c036144008214202d001d41d00f4503c5402e012414400d6003080101500802c81c2c00d02a051440d042d401611400c5680d608000400c1d5910b00103003d0741046814101d14030341031a2804460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 58869202 1250 58867952 58867961
    0x60807060e130908030402011d0a0305150106051603050304030309060e0a050607030c020c0906130203090717030405011b0303090210121506022d010f061e0b030601051b100e060a0c0203070303 84
    0x209e00240e00104101c0c1481da034411045c0c0081d80b00380700030241000310141201c8103c005078401343c06e02c030043c00f210680729290380c0c10f1058903038103190443d075035501c80c5000e0300149200c040141203e0b10300108180f003110001580310881c0e0143c000c482da2695209400c8042d2100100c0300c000603000b22007402018100a020550090070050118412800307a0009c401240c1049401c0f08195000c410301308049000109294100e81c0004065858a0308100028206414244403075210500c2d01200c1801e051082d0300286030781e6030061040000c510054002031541d9504090f2125107468810507903c0c1d00890044601102c40c03039005005206580100d10300344201141442d281541c4592082c8402507081c4503214150100f1440018118142480343e83c020036040c00c1d0b40c9110020b10001d20000c1c4041090b02e501c00000d10b0a59580d454460b0064600410741024207200e00c0703914501e015031401604000e0350500c2c60021074080f80e0b1414400015100300015000268000308401000300707120340c04c0f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 58870452 1250 58869202 58869227
    0x30d0909090501090b0a090c0b070206181216050f062106031603030f12090b010e0903090a090204031407060c0201081003050d09080601090b1f03060807060e13090803040201 76
    0x11989040d484803d1210b05c00c60b44414a5655803044408020007408150040c00b15028841c2c140315059001ca40e072403040a2031220903642112100c13030103035a06801002036000910a0320540c101e18405210610f83c1401202c0c41060070300b1040901e0b05011080e20f40b003201c0c414120341802035010040c2030543c00030b0119900341c042c880900440c985c080c003e41d801184641ea50003c07000c0d2040c0700505455240d59a080828100744289000c9000b4650407410740b04401c403045080c0c1c03101d04d200c901e0361148448082d0000c21410000030741000c40c0c1d0191045a000e40d08401c03003003550907a03194a07440d0034055030012400c02e0408a0155102d03207c4c0e00e40c0312000c520700d103081c41c3c0c481d1102480e0503000a41400083c104040912106c54140402c500400c1ea030003040c4443c03c0c12100190301c0016011500c0c01a100503c01c030903440380300780c0004c8010490745080d1080a5100c0e00000c200300c0244a01c2409503544000012860130b15124408080b034003c055103055466a9004442810b0320342d4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 58871702 1250 58870452 58870463
    0x204020901020a02150d060608061e060c010f0b030708120406050304020a030b01290a0c030c0614090604050114060108060402071a0c0a0305090705060702011202120a0902040b030d090909 82
    0x7a80f1070045c0c0322404101c4440c4103c804050b240d14560100400380e03402ea0700440100142c036014454562203461100e01d03815402171100c65080381200204a4030f00802d62203000642c2400c0001c04520b8880d400240c1c10300d410740640b041603031034209603035a030019290f201414003401c00003001498031913405540c0240c401020481450796030b03140e41e800700c0000e0300b2910241518000340c480381c44603100c640780c6013140008401c0c1899101c6401800c007000c55507002d401d0082d005c03410810414103512650641c03d007142e644d260740c240041060b54818040304d0460301580380c001c58046481018450030701c9048140c0d0350603d550b0b114001e100c0030f5045400b084411800c0503000c084144000b50b5118802e0f407120b14070a0b194030700450300405540010b003550321640c11469042c00a510b90b80100c071051902820410345142c0610b41c018000e109214240580ba540d071010f120f1007010540004454070700855050003000d0800c010103441d801261013050110341420801c0001005c1900048401c50150707 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 58872952 1250 58871702 58871713
    0x10031e02040c0302030109200a0f020a0203030304030818010e03190215090102210603060109090c0807030b040303060603050f062101020f0304050120070201030207021c0c031401020f07020402090102 87
    0x40c0e020400740c90700b426500011a40103c01403001704003620034640c0d01d8080e600c12005403004040211030a2042c518080d041100c40303136041086500800c0030080c81d680c0501102d982e4605030030001c0404806032220300000d2044c043c4000ca500050080060340c1103102c0c0518940001c000000040d811368829803c01d5002d25107401e0301d0f078070780300120074420780d140400560750b403066205c05064a19040701d500b05111540c0c0501110340c4000031071906440480800050082c001c1c00c100c854000742e540301c0025440350207004410021440780950159203c0d440c280400780c3ca8120550a9079030486032000c039110340f54009800e5240294400810884900c603c28140e0001c0300660300b645d00075031035502402d000000380802c0100903c581a00f0100701e1324181d010b4008680c030b040c541c0c03081031006030400d074002ca070030300039907030740c072494021080c510091212230314000d260420050b41c00d4170080c0c035414499a84c0301c40d0b0704418005c990b6142c802c03900036460400140d0810000303402c6540c07428110b103d01c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 58874202 1250 58872952 58873013
    0x11d040518100e07050a03030c02061608040b040305010513021c021201020c03070215210405031b1005061509010c0602040905010609030b1e0a0f09060f020a08010e1003 74
    0x41c03007628150310703801c0400f0800702c8a445103245000c0341c96100c2c134000d510781d1a0400109070b2090b0240400380d4122141da40c1c178900a0042021441c9400002d40341c00d500085c00070342303c400a0000c10850b4401c00c0240940c1c0e440d0b191011100382c2010010790084981040200d10701c21100a0a02080c4010301e05180c03440100101400c9800c9814a5051307075100007010300541c82c2150344d02c4440c4501000c4680707402103001c3c00d12041c40d488403c40d000c0d20500c3c40810100641401540c00c2038400b0758040355114803545650360340b101c0805080c40040d140c600481c000e4182854000b800207110140c40303203803180306030044404000128003a81c0c0c0d95800c0c0404a645000742c0506402030000d9a9000c0c181819410205184100a4034410b0301c00c1200c0c9900408000c4880b5055109004101c00a00b40034801d041802404080030000c1c82e031468500f014042018503800f42102540c50b5548035520382c0c0b2008008100c441c1980c540e421001c4405c020000949801029134046181c291030072240da05 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 58875452 1250 58874202 58874251
    0x506041a060d0e250902030907060f050403080a080414070e1302030c1507021216060c2a080709021e0c0f0a050601060806010302090a0e101206050a0506011d0405 71
    0x112a15288801304860068110207640c3c00648080d040d911710451960814644a0f950341c8482c0c8078080500203002c40e500c2800340244148ca00a5400130003040e5980301c81c081c0245108411501100c6c581404042c0d02040c1c0000030b259019100c0028001003a6142c3c040324002d00e043e070b078404991512950a44240603191544510017038072114070856145c032122310401001c00c8503002500466031103450134011044512000300708850703690504140916041c1007681c401c8035241c18606066603481210716061413450f840e40200c5008005880804d501c030300c0004260302c0390000d009541154400c07490108a8a10010010f500c5140201d581d110070401c03d407414030070842d50036031791a080709004000113900101100c0d03206400346821031a2510400004540300d006009251007420380c10002081c02c0d68151042014103a282d0000760541120319003c0040c2c1401c170f4000000a088c0004603180d54090b41600709186070803090a0440c034290000d110050800800c0c1200c07540300c110400031580c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 58876702 1250 58875452 58875463
    0x4030609060b01020c0904030206070c0f2319030917030403050a05010e0d08010509070f03060b180a0b0909190204090905030705010608070b041a04081204090506041a060d0e 76
    0x901c1441d022444041e8540060f003003880003125280210489404c01c400030f40d000c10256803051107410000e255812605011a8003031403100000d0901e000400c011965400024120b01048580021034840400600301c80030102c42014004000c20700405080c4146802e201e405401d0028490031030b400e03e56a07031121031406a00c00402d40d91a50351f2804503840d40020b00c16a50001c00d1030401688075490300c0e01244411500400038800c01c1040c0e0444021a0700c40d410480050110554298807919800b900b13174405450381c036041d441001e0312400040c160002106070b035460500104220441c1d0369120100085100c202400c01c03443d47d00b044003180c0d0214030712079142c009020303c006580300c2c0c405242071821514160041c440991001c07200300102d0050b182154165440300300c1055014010b8113a140c4107004039046803082d409081480480c00c80d484001e0301c111188100c05000940320002444221207012003d40b140c5180f02c0d07510281414440014082d071900004000b400c0d4141e00c5480e400c3c403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 58877952 1250 58876702 58876721
    0x1a090618041a010801050c070201081e0c0a26130302010e0a080304060b03070b091009051807080f070c02010507030516060605030d1d01080c0f0403030504180c0f1202040306 76
    0x101440d0364074109520b1036480f8090301c0900000c101a0410440c00c00140c041e0400090400c080040025400c022400e210003118800030804d555074140110584980d801c07103034000d40016051116040d101078500100305021510f0001030005440c0c032085580040e000f00e03c20f80656407a20300ca20007003a410440040003d005010640c0c40f070a06252138030560b030340b2030240ca200380d000c00d00a201e00b910260480e450400200c4840e0804030120303500340d400c1021070703003e9076104203406000c1c00d407003110303c1c1010310559055075031881564840c0d0340041c004105890080c0000c117034443c0c032030040d40a41c0c0102840b600030306100d4102244000e078451089910001180d026882d110104460306003001445034a01c0a42810100003162034a03501005040251080c100211400070070800040e03401282d400c0320062000369669922410050138550003407084008c2c98030b4816150b0400341c0c0d00e1003007540410650351010801840d401080b00c030044003d200c01030b801e5003008000700140c0a4030400300c45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 58879202 1250 58877952 58877963
    0x3050415050a030e0307030206150312180a0501020a0c06031d0d020115060912021e060f030402010206010512031c0209031b041112070324080105040203070602011a09061804 76
    0x8414220100500742c40070003880c1211340d80240071140c0061b030041950360f07110b0110750504030405030f0100002d20700690b2902440441d0390020b1582d40300d10030b61021a00300f00307040c0c1c0c85174078640d030b11001280c2e140311580000d40840005001400384030721079009151002e00d004035021902218807281c6041044541034031000d03030342d00d000f58405400d41c10b8500c4002c0c05681000458140f40c4101c00d26543d001d42c0c2c00910a03a04d20804a03c0009420014107000202400c90303034550b08600d651880992003540c0581c00751088200008040c94100c11108600e06a90080c6042c407405030364455081d2002d901c00c021040d001d00c0100c14544040000110350032483c120301d224000c49c8404c1c0001c944885601c09907013001048940a00c0d550140d0042d000001441c0c0010f801c00f81004010b0000e5081e00880b13806624084009400c00d8150001c40c050b0380214280d61005d5135906069080b1240d41e04080103004d1001c03400c9149190008203142c0c41500504620841884a10841e22540003102c04542 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 58880452 1250 58879202 58879207
    0x203030702070609050a03060209040608011104030c1a090d050c10170a050411060a1206180c02010902030613030e0d03080907060906080f06060915041716120305041505 74
    0x31441d410000d2200509040c03c0c04030342c860600e800305003a00c203540400350030a500000d0640d0380d915190f02030001088100000c004501c160070100c030460348140310544a03001c0c8440d02040f02c4c0d140341d0581900311108613680b4601f0408005101460701e00c914140c40c1070040d10700d00503458498040d44d480821580d925802079254120903403056110140031511114500b0003004005800c068a0500000c0c08480080e2a01d91242003102d000300c100244000d00e5042110001d80c1c1a00100c10401000c0340c68000d0003807030703004203040342201c1e00c101001c1d505900403400324510322403101032802646c5c040d1078196080548003011450520820004900003010441000124941805144c1c041c0885d40382c8030030001c2c90300c8002482c0e00b1015010401081c81c02020448558a0504403542480040c0840d02c5410f003545a00d801600103115074040d03071710101103850071b5080100c0c000f40c00d04410f00e00d01f00803e051010030204910394070421800d004e41008041303000180003641e014100000d81d03a07182d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 58881702 1250 58880452 58880461
    0x12060e03090d051e0f151f0909020112020313060b010e03010509061e070c06050a0b040e0c0310060e010e06010201110c0105060f10201006080106050909030c03030a020c1507020303 79
    0x10001c0c0d181200341c0010b508150000c40a0a030b000c913030f030345650341400b0070400b154807a451a1410f80030501c0da0b00c07c0c0b00d070030701c0070004810140ba04281c846a0003601c1c1c0300e05100b039940c400d406920044a46040d001003010040b000900684d01ca41018001031401d60210520300300800d0841d41d00741d07621040369101900304a9003280c5030350a4114140100701c030b90901e0034128400b070303d000489500201084d846800052420302d0070f50010007425002081800005e101c6024240c689500046960082c02074030031042c5940054022641164042e203107001c5140e01c1c040190041d0780c4043d248504554036801074441030740d00100070f80040140f1000000741400c00c4005c00c525000c00803d00780c000c000860640c4c03a110340000400101406040001c0402004600542e08100c1c005580495962400724081003140f01544501c059031070a8a101d0701c281c6410199540d24090501c100d00302d40e0080000942d2242c154010700306003824001200c07081c0c2240c04014601c244c0460b6010010382c008000c11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 58882952 1250 58881702 58881733
    0x120e0c15090a3008030f041a0403110f060c180303070803090303010f06020d050301091503050607050a02060903040e041b120326040507050d02030f030313030210020412060e03090d05 80
    0x4080d4030104054008403c1c1256651083c034000286456a0680c0d540300040c2070012108040040c45034801c288030a61505140140107c11580c030300c242c0070320503900f0780c01e11007000040683c028803659244500381581c0300d84814808c004481c4180c6c00d40010b1104100041c0e4500266015040311400355407039604028035813941e00070300c0c1d109404540c00104030850081c0c0100c02c03603054903c000800326202d070f290700070810750402c1c03a0300051403446800708011710250703c02c029020200c0580d0030380b4410b03217900209656a0140f0300500d50500c0040d00801c0000d10412903000b48030b038841c0d1030f11800b10341d100070107103640401603416804503003558072404103034102c1190345521542098030b000150a01d920740a65482490141074000d2080030a400b0079540c04100300440d100791301044965034586041c00c40360400b803000c01140903110341d0b2580441c1d01194000e880603030b0504850f04810903030603150000686600d2000404500007080b017907030592a80845e4030800b9001d80c004201c50803008429 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 58884202 1250 58882952 58883009
    0x210c0f020106050a030b060f090a060602070b040503071707090908131707030212120408160608091011070b070305190b03070b030405190b0403120e0c15090a 69
    0xa10031a450400c0c14020f0f90703038044d044011740e038104030118100d5480d003011134106407140860300c0d84080c000e0700b08440ca004981082003a24910303400d0f100c1340c0e41d46480c0000315001e54080c440c1c0c15000044148501c40b42d00d8900c0c0c0d410481c4000701e800c113540d500e60800894a4991098514900005504800c01c20410248000381601500801807140c1020801d84450150000a100d4090b0320000742800800300080c010440b116001c142d41c80d681c41c4400c6940b0380c107080040c0c90403072119a001440c4d41c09054864072a104060141003904101c1c401c4800510890010600d2a80c05100110100d0468404244503c205450004041c2425040f0520300001d0b8114007960b6030a00c0040721103038602040f00c01c1205c51002c1e01c55181e80322440c105091107c0035546440800c0350140283c14096460f2810780106c0c0651100355000d004051043d0586401c409044856846142402c40700d007018082a44a60180f0080c4e60400c1c19040c002401c507401a07110b103047ca0071a041b000000c00d2940d00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 58885452 1250 58884202 58884227
    0x905090108030a09050a290912060a0501050d080a080c071703090705100f260907140603060f06090103090b13060e06060904020105030405010204050a090504110a0e01090c210c 77
    0x514861103490a90001d400e440385034100156280e10246618880b440c0c7d03070568a03c41001851594191001d24020755108000c0f41c412941504010001519090550b03090100700e4221400030300d00a0140410f554480c4040d0042104905c2000308801160302c518a00903003022081c140c55403410801e40c0d4601e4108242c0100d8811444422401403458000c0c030803461042240c109010030203d98211250104040f0b842500500d00d11020003411071400b0490360151030345a4888031080d003c50003845100e0008491294020782d0b070310006101481d00c0c4003c1d05e0795000500d0049030032070482e603400d000311206407003086441c0d02061150082040720f00683c901548040d0050615103000b90018086401c09400681880400070108080c0203081d011540036240c007601707012609640d890070a0040c4821034040d51481174141c0840300b00c0c0342800607841102c0d4040b5410311a40d00308640700004103000e100c1c010500000c0031090340e000031009692a245158035400140001c44400c0c0038010032203814 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 58886702 1250 58885452 58885459
    0x7050105070e0303030115090b0c03040f0b070c0b0f091206100b030c09100c050105150108090a050703110303070c0f081c050403030e0402070506040b1602010603050a0b04030905090108030a0905 85
    0x24401c02c0962000419281100e0640b41002d00d9183c800b02d082d24100c29507004844814000111406003500000041003111802008640302c10317941d07070000c2803600035500010118072150600300f101c0349408019141e03050070324041d14a040e17a07100c0045d0500315160400c00c01a00414201701a80d00030f04810720041c00140301280c503529250302c1c810386511070b041c400741c841c8000707110000085101c1c06131400c040b41d11500800c000e040c04c1940f11040120520441d001800c048000307040da40000c5504030503c0c0d40003000b000b503607055940703035010040d24181003901448180001d0010401803a0204002c0881c9401d03080e01900b404170003802d1550841c0401c0c000d0404601940c0c00c56801000c540c2241e4041c90b013540e9a004010000b030186c403880310007a003180308540520003031040d44101e40f40a00c4000500801e4002c41c0d07503042c0d099420901c0060020703000520242c003c1100500c00c51743c094400e242008813280ca940025640c01e40a0f0031441090b480403402c008180e80105004011b01800c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 58887952 1250 58886702 58886717
    0xe1005070309030c06110c070e061309050c130f0606050306030606040903020a0b090a0602040b0306010e040507170c09031f050114100c1a0106030209010225030f1401020d020705010507 81
    0x243c40281090880282c010030003503458400002681c400d500307441101d0ba80318140c0b0b410079503a06c440030024000780c444c20701c2401110343c0c00c000b80300540b0031595100d9010002e0102241100c00b0024650080303060a40041e4a0b603440c1e42c07810101e445030b40086d104d0350316650b44070f0611031300b0b0600d402c50080c403403030003549080901c0001c0303600028a803005680c011001c240039541c5041c03090800e403128a0042c0000e0004c10003054008480700034602c503a038280d882503401013640b01004250380701a00c03039001045000680440346101d80c2d0318541e004211460b41840d003007001020900e00f81007240e0801203a41182138000500b00d01d0f0092500402a0440d0031703a500d40903038005443c040d895905482440301c0380820904009090700441010034035807000309515a0b444802a000e94032458206006015041d5a40c2c101043e200401c50b500425501240c5110700f1035031440700742d0354950026070702400465108a401203090008050480f11443e02684500c080c0c9001400e48002400001c1401404d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 58889202 1250 58887952 58887971
    0x6060207050901140d03030908040609030b1b03070509060405100c0c080102130e070c020414010521121b06010906091107030c030e0103091e0515220201030605040e10050703 76
    0x346810a040304c0d008880301484150140340a400400702000000c0ca0000f0100700080c0c11742c0c102410ba4100d0740654030750200e070f550f0381482d100e101e500c09044c0d040380340c81030005c91240ca1060300900101d000140c022850072f0384480010740c020b1081c080940006048150310717010000b0209415008000c008003e500305012504242905241400307250141002c4100280f4520320518061001540207401004484018a4400300c019001d02800b03000b16500b00410700c0030301035603e10b81c102c038544c840a400d000114600c0e1100941c0100002c0003401100b4252400c564800d1083e54020804601c0010f500b52030400c031403058071a0b10760b10300c2038201d00303216400c0400e802003903040c500ea50601d04041700306022070060f801000c0420005d03000003200250707104112621242400918007810449507856100c50324480007e00c122032202c041c40c9800d41c0000b03685070481e00e080020340705050203d40c060f21100441d0803100ca1901180c3d00b58032813103080084990502c212a00809503142c00c0c00b0b48550b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 58890452 1250 58889202 58889219
    0x105030d02070e0c2109060f0c1204150e100203040507050d03020c01210c050c07210b0406110712080105090105010c021203120702030d0c022406030c100306060207050901 75
    0x34004c05500c00602c0c005080301030780c802c119060050240c01c40c0049032a0600254442d6074100403544e0f200c18000701c3e00420301851605c42961140f070030b4074501284940d40d60342d800445044a032000440c2c1501c4960545076040188109112000d43c80070040e1a8070f02401c00a00d084807642c00b00740108090506400031a5000c81c030b80c608808213003850040004110146661407a00c030b90704040061401c003403000300c60752100080088401e000d0842e4902601d0f121100c01e41e82201020039034107908180024002076801c2c1c455a80580106c0001030fa03543d0400300c90400d0703408220700300c0d1045081a441400c1d03e07004604e240c00f400050360032000540c103200000e07081000e80034000c2e110342005480c05424110420444806461940c0d600c02c80d810140d8000c2c2d81c076005015540c00d4031713003800382c00400ba601c0015a49500d01825001003c09401c141100c1d82009010340480d0b0076004024200c001a11148404007210000307680009010b441e25000900306101030304514400d484074001005200c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 58891702 1250 58890452 58890479
    0x2160509010b040b1c020406030b090604061203081302040c09090c020f0d0c0809100e0307090c020606040b1f09060207080109081801091706010e0a0506090106030c0210050406050105030d0207 84
    0x10302104446685d14000d07040c1c04050308202c0c2460300342900005000c105603605400c0802485403c1d900401e1a131035120401c42600d5a500440340041401044580828403a802141d00011801201c0421000c25000300d0f046e54001c504402c04030b02c25550400c96101144107841d4800c00c0303440600300a40591310f015440351b000510000070007000f804480140280001125900140180176070201c05260001500070407000380310910900031500e00060000040c003c0c0c400f8410158040e181503604e60781008010109425940d400080400c00031410280e4600d0191800441c0d0301e900d07e030f0343e26203c0001d240c0701c042c4d00300b8611641030000c10310003d2443d50655442c42d0b400d5900d042d20403c010f0040340e9030f800560014800c4c4000b400c0407000d160007c11040d06803010103081e424540d4900b50010309843c0140c6074079811031781c507200400505100b54803032400840d003481913490340800025a00182d40080e0b8099400940e204010040b52804000d900004910360016041751860800c2c0106240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 58892952 1250 58891702 58891709
    0x607030806120102041806090e060c04061d0409060e01150b0708030901020c07030c0911030705031603020f0d0203090106050102060702030f0a02120d09050105010e06102001060602160509010b04 85
    0x10482d10011000c0100203405941c090b008591811402d011507100c140045d20f0381d8401c0c035441c00c1c50140d20a0941201103001846070782c20f103405030b140c51310380f85044505400c040c1c000056220005144003007a5030340d006418504d401070703c3c00708818100600321030031500c0c208030314010b81114202c1004451120019580195001102942c60781d440c8292180139128591038050607000c1c801e000300c2080410300d1008255580040d0400c40c420400d813a250b09440240d030342102140060001802d8140024100ca40e0076009107805030030300d0314001504205d43c0006080f00c03034140d0048200120001c0900c10580108000d01c0200558182040003070740f20321a10050101d09100020700c0c102c000c7c020001400503444514800e9591080081248028603009030103c0e1075500b031200000c0da0841c654003071b602450008080c2e10400311151010749414840303412151a2941101d07007030201176000c2c480d890080c10070350003078403510740b511502c0c001800c0540c000c18443d05d924030051110076012010355041c2e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 58894202 1250 58892952 58892959
    0xa06120b040212010c110d05030105010503150f0303030c1e090105030402090a09020603040b01170f0331030506011802030411091306050115030e010902030a0f0c0e01060306060e0607030806 83
    0x2681c9403400860316800008002181c20760034440d002c444540d1104204450800e0035058030152401800210780d40c0c8000c0c413031540018414804928088000d184011080700d00500952421a001d03001c281075401c00c41e000c030000b54000c07a1070f03c01c0300c00c0c0c00c0043c160350800301c8902d4500800f41e0700181150101400190181c0c202d0340004d40d04800c145c0c0410300711134009080c0b50b268905498aa07120420134001d0f0000d000000241c0041d05000080700b90604544a000e1030618481e441184c481c6181102c90510304000c00c81b103500308000090b68880070f1401a80501460b40c1040007040403074003a2070702d0044180c030410030000860b0b40002e002240040440d285016501c40c100113104031a4040800b8004928050000600d25003905480101c000181c80910190f9240000a03080f038410380c10194241d00825413020003c0c01488030307a10035620548002d10762544030300f0b04500c0307000c00f6007240010070343c2c5520a008090300020b4148140d0b4080315014501306156070000d000039400f4002138003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 58895452 1250 58894202 58894223
    0xc01230306060f03011202040b0409020a17030906040801020702040b0901030c030f020609040e0f01111309150f03030207050a0b070807060b0301021b1b03010e061302010c02120a06050a0612 83
    0x201c0e5580000300d038042c02d0b40841c1c0d580c495840d007541d111148a080c1c0704074811071600d501001103003094012a5440c2c0c0d0000c2c1929a82c5251001d0302502d03004424000440b03001c1007100e064203980d858054400303460b9031303000141c854000d4030500040b5036900c0f40300303441054120300410000d1444402c00702130700ea00110600c02c003a075510100b8958019040c1040d0301c141050480e03040d081000500d01c031003a51003802070100c0416005040e00394070903860140c502c000120828840f130740281c1c11038243c1c0100c9100b25110744d0340c0e1712990b581e151305c00e030021801600182c2041141e881d1026650025040540456280c02442d40d200290303031003041001411540c4940030078400756429416202802e440b100d80c800050b0b0b11a040302d8450b0140a5140d0010301c0e403c040d0342d101c3c181449800700e44c0d03424500401e12601e4080c900003070b40403901805c0b41040322035801c1e6001610b5480410340b074410004002c040030310701803a000041d01c8000b819141600e16007001000588001c01d000145583c10095056 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 58896702 1250 58895452 58895461
    0x70f06030e032a06061210051506070f0606050604121b030615030c090513231f0b040b03060604111306080106120204060c0b0601030e010e0c030c012303 67
    0x1411802001c0401d00f042014140380c2407010800021503640c034240c00c0540701155078441c1002522401c403802c098251740718880880f111401c81c0c0c02143c10424140028000114400000f002c80c0e2203c107080fa19000d03a144400c0420200340180800382408a0300d0b42d04003800c0c00c0401d107454206040c080c1414819844c404001c0103d0121640603680140b410700c80f0100041c0d01d45050350302803000300c0e68404c44850000b02180184210380c0034207105404004090500d440f1000401c2c83d502e0218900070042c000074404a80401c441c0c41c010910500520021410211200844621035170f81d900035801c02140c2c003069035010442590100d400c80f40000d00c400c7c1c1c3c01040342503010789250083c034020000707004100541c00c1005541220010344e40d1012502e03070303110b6000980c0210720804010886c684e0026002039222803910364080810b240001d1b41401a400c8079003580d07882c580c820019040800c0701c0e4183d0a0603c50004440c1c4282009142e4481c1c3c0c0004440c0c524459107040303150640440442c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 58897952 1250 58896702 58896731
    0x302010f03020d02120127140621030c0c01030e0f06041b050a08010203150604030c150507080a030b0111011116050a02100807120c0519020c04090503040504050702070f0603 76
    0x5170540280100604669a110158030480310860110040107089401d00d6a60b511320a008058440c01c614400b120640c803203605100e50207000c000d0440d200148c803140d07441d4401e030030000380650000200080c0405800c0744009801c88600c46c00080064001021010f90f400e0001421908142d0000440344800a1800d909441c1c50300d45e0003040d4048060080082d4202e4150043c5004424000c0c50b20b81080e06007040000500c81d0340700003443c40e06002c002304180c0c2030701040c1c1d5030b81403111b041031450034100e07588421480e8000240000406d80d508440c55a550b0310418403c81d5045c920020007152640d42c065003604d000d40c02420000c00700e5100c010040000a014428071185d010f051030304150724040000e4a005400c071a40d0700040e50403045154414024060502000c07030940355540f8140510350100d065209080c1c90780705510454011a046440c0d80c4210b110f40c601031000755455508000402042d2640944400d00315070100e0000e001c40e190a24201003240c149043c002084101985603 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 58899202 1250 58897952 58897957
    0xa14070803040b03040c0f061b0201020309040609140a05070c0b1801060303080a05100b0d0b01110609030705160614030a090b15041b05040603020f0c030d0c0206010603060302010f03020d02 83
    0xc080c540000324000401c3d540c0710700a5800b480c8188034030211603450308100c1d0b40d2a8024400d204c0010409200d1031040d010040c80c00031250700610560707240440500216040d210941d00c10082c00d0b45c4d41c54030520302a540170303c66030000c0364920140302c02d00f803401004000e02490040540008c012802244601b9080741c0100110030103503009010f92540c1c0c1c00d014041001c102d8805030040d040c1400905500510b030444800d46000c001c595082c00d2941c0340a00044c040303500e08506010306010000240c15007040200c1c4a0740d458001190740f02158a80142800c4101c402003c414651643c01d1008a0300302c0f8012650030b445c142000e46036a40e02d0702400c080d040d00c81001e41102e11250511521404800c2c00d20700c8818169020b1100b40b00c1c003d06170803051103041040c0b00040060006103d01c41c801e40081c9404106504014104401a031880c0e0840c2c0c4540c1c0e80342d540ca80c0c1c07001030440c0c080d01401800d0041c0b0090408010591071030300041c100e01c05441074501050350004a0f0903a441d4036505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 58900452 1250 58899202 58899209
    0xb06040b040e010905070f06050c0d0516150501090c080112030305090a150501030b0105090405100b0103020c060c04030c080708030415110a0c050102100c0905061308190b15030a1407 80
    0x280b210485508105440c0c1046007e02104100d4864000c00c040313006404031045001144010325800071003040071034260704482d1002248115501c10000441d1582600c0c0240c030070452400290b84d450302010200701d0700208580c2c800c4c4410080100444074034500c51004442e010304021900fa41d500301c0360383c10701c2041440104038100c0000c081d036204507694881c034180ca220301d40c801c04c1e03640c07504d040140d880c00881d00246a58444030b1045007080d541e42142c1031010301810094101010303401414244034003100d514001a4022404006020100308503100030910360000d403a000c2d01782407610362284618010b002c50410860781a03020344e807190300443c8440031440c0035620341c1030240ca0f228069071443d20815005118030007692448041030304c18012000302580314111365514040c14402030790019640404d5058400c0c0000540c0c840074401c010418654100e0a12a001640341400444030b01400e9940c01110046ca420200e807000a114212541c012030050400c0030940d030124a4402a0382 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 58901702 1250 58900452 58900481
    0x501120506041808070308060f0609010f200c0901050d080f091f02010f0c1d090915090d0906020303010b1204060603021216050d02060406050a0203190906020d020a0b06040b04 77
    0xf01a01c080c4031100c005800c0392803181e0380e440500d444040400089000e00306c03501c0d5020408004180103580100b0002540c289942050141c6008220002c085402c4849142c1d0541d00002014240361a250520382d014050450319410302580d02d442c0c2808a0180280c071241c40300002401072541e50790f0755103803203400744045000a510a4625002400703813517100c1c040301d40c10341007103074480380c240c094180000048c211000e20207064000c0d4040003041c01014061901381c0c02545234040e031400304086c03620b110748800c100405084003806001400301140d90f00c03507000c5420510041c000c45d110f4001303c6d8030036003112021901c552910304100004005503400298403d070b1107641301410240102d41101c1014020081043c581d85d68000c2c0308052110200007035010364100028000c9500440140c00345c5805e0b80304903410132003d1002410705001c070b00320440210760142c42c01c20500f41d04001c81003e0803600d00c05044500740e9503503461010354016002c40d106a03100c404002c5580c036554403190720110b251 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 58902952 1250 58901702 58901741
    0x11407090b130b0d0c080601140f0d0e030712090b07050d030b181501030b030c0a06140409060b19020d080714211503030c0307060213120c06030501050109050112050604 74
    0x388480303c0201792582c2000081003810f070000b101036000c1c6c010f201000780b500d0112481d152071200328044a07801204500519642c1d1024034130814000c2018052044c800c91501e16501d100150103460403800f039222500103c2c0800c20400003d40202d4031024946942c1804603400744580001050203101940480f0259405020040035240030700094030002000e032410026000020103040d2101309228030580c0020021404000551183c100074141840f460000d030f0801d6100ea03101d03415220142d10400301d030342c000f04e1400706080c03500e410304004504074001440e103281040340c003a10340c48004002005001b040807210101d90600c0d012034a0164012a543d568502041da00c405000801d40d444044968002e04024460030004125840792034148000e5040a08964402000c4e500001c52031000982d611000146480e1444a4004540c41040900c0c90607041c21030050859205900c42410070070111010003c5917000301e6800c03000d041079940803440b0350f64100820060003108030703152000c0d9141c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 58904202 1250 58902952 58902967
    0xd030509030105041209050604050612070905090901020304030305060d020d03140f1303050c060906030a05060a090c02030c060907120206180603070c0507050307050a090239011407090b130b 83
    0x400c8080580c13811900c6d103600c80b41d01c4106110315401280601c42e0429400c1012004d0b8101ea00001a40300000d0704c1d00e6144c1903140d002150845509680006981c0e401205110806805010340c81c1c0c0704105465140452000e034000a4013007000d0a000f03001d00002451095603804141c0c21100d07034880850046594440b800d0b07041000047c0740c4400d8400307008500100d5024903010341101e07108036004002d2803c0d9241c0390071603030082c24041c20561b4002c002c840001580002c0b40602d81d079181d40d50300919103608034285260305204000b00b070a5903a401c00d1005110541ca0307107080300900740c3c05031035183d1036000700c014281140380c902c1980f0740e103d20048104010181e01002d580d1290b8402d505413421255500245a40c0d5202c0340a010713405034000b407040c0130651440d8060205a8116222051010a07181340c0f40200301d41150400c44c82c491810710743d04170745c109000d5030300115141483c00c8107601d401500108115902e020b102c0c400b0100180f02c00508000100c10350103040501c1340c180d038a140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 58905452 1250 58904202 58904213
    0x7111f030231050108090106030803010e0a0e06010b090909010902030d0309020a0f0b03040213020a0507030c03020a0609030908011103060d030e0d0c121406070e04050a140f01032f0d03050903010504 87
    0x1214403d560004100d1000500001ca06004000480b90300880d11415642000140110404001d001c602040d42e251100203001c41c003040b50034001c0007071002560b80e074401642403100d10030006082440580c104201030005071070000709121541c1c814070f000a20b41c400b030300c00070b200321999901c0b0742c00449000001144040e0050000c501592003100c2d00740740e00d40b001c2039007004da008041159010400a001000101e4000d40341c1004240c420f10541d92114595a681c104413420704500b5030018900160900018100740b00c8e0300068020701440303d045180c0b00c80011180d00c06e8400003400c004003510301460742d485801d0b00030080b9500c990301c445504d490350b980e60502c1d41080c03410340384071180c020342d440d5182c07001c07490f140505e0361035541c011030448040900c40a08006045100355a40d50000900101c0004110501031007145032017902c15403440c00d0002d614841c0b40000c00c3d0718884000b40c40d181000c3e0640200e01810180c0b07000c003403158207003416a06d60040a50b9141c00d9400c00d001c0008211 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 58906702 1250 58905452 58905547
    0x2070206120f070c0302060408030703020421061503050705040218090103121d0904170c0102070317010509010605031b09040908070b0f09030406110313030807111f0302 74
    0x384003442c0312000e55200c2c2001c40d052650a0070240c0540c006502203000714841d1801940e1003172250501524081c0c1e501100c500c07500700c01d0300d10801c8601c1121082c0030010f0b0b50140e9000c0300030710340b83c078140d080c19502d51715154107480c4075030b41c400d40d40050f01010040030540d409047c510000c000d4130040d0794030f003007403011120129030f0040000e800c40d1441c03d0086100f8410b1800040240c14602c00c0d0340c59650303031200c0540d121820601080c05200c400d01000090004244030751103aa83c4030031040d22024511658007044e00424820b60310078005000c07550b4094107813640b00d10101c040ea1501c5a421350303014407911604582035001030600300d0305000c2c46a281c00415103e8407912854200b5a140024901c81040546450159800420081100d548182c2482480340181820f41e443c0c070140c0555041d02d1040350380211000103010800006000301d181d255406100281e581541c3ca03901d1100c8030715041500500082803503804204081d440741c0300032100c2486c810b0950741d10031000c1e01445102e041c8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 58907952 1250 58906702 58906711
    0x7210f140303250915091703091206010803190309020312031504050103051b0406211208011203110a02040e010617011e111611090105011803080d0207020612 69
    0x9026403801054103a4580140b1203c8080503a1484136a60805000782c1d00170441c280107508000b42100c0c08100301044130b85e40c91090045800071641c5810740b90601659a22000e03400350706421a01c010011501e0210489042e00952040c408860100310f2080e402001580001b80d0148203800800140c0000315005500541c0c3d03800c0c000501d442500300304400d45000b400010090380007002e0310407090820180d00c13004050010804589252100c2410f0050368800c001e01a03103a550811900500810320f9612145044900e03001c51198180198810740c0000c000d070080400c41c644140c0c020010003803001d00c01c1c20354014002e1102205d4203040324080c1509004040000c0c100f100071841c2c0740d105100e8003501c80007481c0e003a018604003440b60030060100311070006d008030081000c1103440a49400c1e540383c1c41e1085074030400030140a41030041500058000c141071010292030f91075400c14524810003220746c002c0a00743d0310160707034003a00046c0c080c404000303400c84d00201d0300c5200701e203142002a00ca07 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 58909202 1250 58907952 58907971
    0x3040905070801030213090f031209080706021207110304051011010c09230f0402130e040506090d050703020615040b0a0303052d030411010e1309110307210f140303 72
    0x101b1040030800b01110340c18003004000400510007800000e0081030403224442002c0000182c401003902c0e0b0600aa01016040302c50719800102074201c1a00b40300d0064103c0da1034509454a92401c0c1070f00c035a0323031049000c0c0c00d22480d0746800d105489440b131529180c031511010000d1106500c45040500040d80c0d80c0610310000f40da25140380d00008060040c8803070510f0040290304000b40d500c05200080d403000c01c241500070b100d160042202c00035854207500a0b4880c1004008614104203501d04082d5440c4020381005400c010003c042a4002016500407864200315042c002c110030003d001442d01c0800f4680091008070000141a04540901103180303098800c0031095480200e80748900903c2402c151603100280b0100c5c003c9140c1e1001800c0902c410b0400001030600440020315100d00c0b4000307002c10702d84942901003080100d0602400b607100c1076005181041c140100071507010a26403003d4080d4040c101c01006109151015014042d00400c56005021101c800942c4a600c11640444e5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 58910452 1250 58909202 58909219
    0x40e0a06050a0c02030d0207210c110103021c0203060409020a0603020408060c040524040519090b0910151b05070f080d0503070804080c0d020c0f0901080601030311030409050708010302 81
    0x20340d0500303005100003d001c0e98051481d065805840e00006c0d04100c1b0241c45410080285040030210408a040b070080142c59100400c2450300c0d00444410140c9003403410503005200b2481c004046408808454190800240e100c1d5030b0b00010900409981001030f40c4419807100001e4114fc160f4020400d035030605085c5c51507603035012068103141c4070714844d1a401c000505690707a00034940351031b090380e40101c400609103800da507240000d00a010744c50102e0719000000c0c1003004803d401e8481d542124138203a68000451403d0146a08140c400307104400f55403200c086030024192007400500c0034480345d0014140c6550140c100030f41c0c0c1c1c041c00c0c00b81803040c01002e00049580100001d011042618130f071303900d906e107540e80320048421141c00b91040f41d01c180240800d443c82d10f010701c8000840071196006015042085042184035080c2d0840a4003604450300188520140401c801e030569405050110302c200014041600d544126442105030728601001c0c0007040d6400111981242d0007101d00c01d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 58911702 1250 58910452 58910461
    0x810050d02060904051b04080d0906020a170a020106050303030f0106021203040b0c0901051c0f050109060311061e0310060207060f080a0b0609030f0102041703120106031a040e0a0605 80
    0x21494048240c003a6202e101402407901c10b19164000302c2d40107600c0310f029114140e04410032012500aa0043c0980d034002020280c1015802412440182154401400ea184807922500e88107201000f5810f004103001620302a924000d40003000282409400c881d500d25110b2056030704e404081c09404014001c0c030b094045074075224820b8a0041da000003c00320075407180008101140e100251148c1400304c140100492080c4400c0b0380c9010003c614008107a403034074440041c4c121b9074141c01c8108050724241003480800e8069000c1d940303040b019220569076900420004180400b029010384011f240081000051080c01110400b03d0b00140c00329082c40780c803101c0590340d6896420702d42002030b145400040d1903207145e400403016084040d20542ca003428000c0480d00300f82550b15400d00036900010104000032402014131401040d1401450401409504102090740103114840400d0744854004c84e0001c41d50801c40403142009008200c1c2c81c0607030000a07190303041d150b0305854103032910001a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 58912952 1250 58911702 58911709
    0x50a060306030b010b0c1e0c09010303020109060b030d020d0509040902190608061503060405071205011d100b121803030a09110901050306060616140115120309060e130903081005 78
    0x159840038001010344601340d24051f001004140443d000380f403170b1140c20041c032040e81304d219100f8065070103980003064101d00f608210003a6540c1c030348114003d81c015a40304800a80c00303d1042e00300e5001e03103445552140c0510020b40600110207010354031490800003500b5400c0d8121010040b6140d9441d007440c56540c1104214102c00107a58044020908000140c803914199012035848407460816455226240b0345410031900241c0110b02001d990040c106800f41c60306609950010481401c2c1c100b050502c40014124040d82e000d102080c0041000702d100344000b00002c0049c50740d0b0b03074100d0380c485c54848040d002810003290b0548001c9028254144142800c500c4141030b070b00d0150060840c2d446080c240820365209241c500c580310981352010000610100800c50390302c0c900d03c0040f074140c1002000181c541507aa2001042c0c0559070701d01d40020b60408441e074101d45d214100888569110000708840c2c2481c0013043c0b01407031410400c0001c16400101490003014004840c0300c02075111801d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 58914202 1250 58912952 58912957
    0x705070b091b040f09050a05070f0e060607060209120a050c040b120c13270308130512181906030b0d0c09090609140c040f0501050f0f010504050a060306030b010b 71
    0x2c0c44a000c0440e6500006820300d03822900380b01c100c030740e0009070011680d01e455040c41c00c4064121a2030300042803c0041e0b0455800f03940180840a01c1c0700080e042020002e00d1600c10414024109038000c03442045543d620b00c0300001403030000d07081d50320a03403403031410f01c0c0c6984001e1103a9100e01e21303104a01186003085032041142c0880304004001c00119102001403d281c12203c000d0f03050348680400000c1525998204800e841d43c03035142049104514002c0c14011008250a441182484541c40401c1c000190a2000c414040705503a94282481041ca034006590440541000c411903018100003102d2907004201d07856580c0c00c0008ea004042040780074015444050240407168070188458003040c4c0c41200d64a2243d0303400103130755200d40d41c1c800048a080d9004e10b182c0d04031904000c40360a05001e51b8800c0c00300420100542d40c1071900003403030400c04481c010b00a80e88a480303680940d014804840241c40700a021440081d614100240604034074001150480c08d0396000150b000c491009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 58915452 1250 58914202 58914223
    0xc01060e24040605060d090b0a02030405190201090b040303021f06080d03021b060702060708070302071208060d0804080c04060f060e13091e030216050f01260705070b09 74
    0x240c00c03445469211201640c800400c6682c0c03003903881400103000e0f6108002801d00080154002c940300070103082403405890001d092650590040003040000b40000c140d0500c0c610038841004d041e601103000403101d84400360800e4404d02c0000070f02006040d00084c0d400d0158810100002910328591002415203400707110319500d99100003100d1003c00c0c00b9802408040c040907a0040c440743c0010881c41c58180243c2d10000982c10600501090961140b00c0c2c035440302c05d0b810b09618001d240c0c3da4009420742d1601214082010103008605c0c91b42c0c80302a0a58140e8010f02e80540391601c85481c1919552081e9034903100d0b07441d040c400140c3d8004196000304070b07481900d46544c003008500c14442800c2c0700b442d0342d51526903540c0181d000100c0002400041c40710000c503c0082d20351928001e0b00d003103001c401d85040004107890420003540c40880f0026403203420320708115010080c9013000304c3c48440d0078000a090a9503410425442d50000192580c103000e1000000a5183c000200391203114152 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 58916702 1250 58915452 58915471
    0x40b181f0b01020c0a091418060103170c0109030f0f0809061b19090306110c070506092b0201180b070f020d0503031f060906051204020a1701020c01060e 67
    0x854030359240d030305940000426001030042d64240ca03803100000e03110010035082115900d80d100e0010001d6241e0a500e2580104418040128288034024041d91807074140300c01407406000c000709040b001505c806542c040d610f010700a0080d5126458080c1054140d0380700300c000100240000914240b203191914000ca600b0005030038240c079441c106440f04a114604150748c082d08101c060050801c0079005070900c030841d961400c84070b046140c654184d4494140c0d910b545001801450a2044045130040480e10b04851b0340d40c2e6844150040f0740008900020390708810f01401d83c16101002c503082014025100340d030386c5101010348004810515100d409100c1814200340b040100089801c5014030741c0c1800100f401c28030341e0103135440707514544c03044904c20080400c049404603000941003096001d40b8190130906450b41c00c0100007001402004400b1030070000b5a00454250f46403070ac02c42c0080d0a07036040080b0030009580c1018040e600c040b007440d41641c60588009089120281c580d4040c0e24004d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 58917952 1250 58916702 58916743
    0x9010903060b03030903060a020901020d0507020f09070e03030409021207030501060206010627120302010605040e030a03020702040e031204050d020c0607020108070e1210050f010f0302060c011103040b18 89
    0x16100c0000810200282e0343e0148010010071740207075010070041f4802c0408000140c0d644500d08002030a001510002c02d0a0050900403000140e0700c1c180c01a80c03494081d2460741003a61084d1081705c44151030035145805020028002c01c3c003100c590001c01345401d9800f084100381e1100c0404400b120000d1040c030005811180050010b207206500c0d0b04840340e5100300c150400340240f003140c401c401c0d41c0c0d4403a00aa42d42030781d42c0000c1540a000c0d10000389000c031420005002d81d80e0b40d00303861b4030801984400b0158005090070031940c465015412640c0c9020881b43c483d2021240480c2d614415a02961548030301111144103500c00124a2002d407c05025a810046244d00542d080e00d0050034280c1800a41c0e000c040540e03d50254001c0082d401c503009207141840020b82d030040705d00140112286e49050700041c03100c00c418200d1807003120f6045d0744a81d80c0304000100c290040036030701c407031901e10302c000424001401a140802800741c1e28030349080b03444941c40f5803145d50b00c250069081d00901e164 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 58919202 1250 58917952 58917959
    0x20411070218191b02060f0405031603020708010c05070b01080a050703020f1c03180b0c030306060705100501031a01090c0f030c020c0a03050d0e010503010612021602120109030f05090109 82
    0x2c0c502041d8201c200c41c0311030612500c00d041003109961012105a901540d0520b030203103402d07410084030750460b50b020070014041c10b0988800d6200d104101c13070380418103455000da504051080007034400410f0840020443d4080c0c55a005107145c2c494071060b0f64a410b81e0002161010002c06c60000c030310b500400030b01c44185940d007441009030340064915841141c882c600307040c169104441c5418a4407a90f144141b150982401007081035254005818074034050105200e010750002c200d030b4100104450243c2c80d2a034524046182407241e10030181460308082c0004108580e0800c00605614501d4165000b60780741c844a44c110b42e9646414000a080711059040c03043c080c0d44203d10740307a8144140da025550a0022404411480c0d0003203480394410321030b02008550040314884500c100f403030000c3c6194035141c801030600710300d0003079014107036400682403555030016036102010540c082c0950f4581050115100d0092520748001e0300494140089030403424814011103100c6e0394161100300501d821b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 58920452 1250 58919202 58919239
    0x8010603050403050706090303063b0402040204030507080105011503180609050f0a11030c0103050903040306020d02040f03050a1103010b0d080c01020417030301141c0809030a021003090204110702 86
    0x10701070025000d20108024940100303182e03000382035446019440115809251030040115000104040030681900d1400381c00d24542c084512010184140c29400090f00d681c0005002481150300003800e80c0b080300c000103103255040d00494104d0781e10381c00310b0801c44002c82c0164199018110584500c9003407415140004960307910004d401409a4101c03002c0000b400c5065140c544104e50a54100711038101d6a209880d0811060f401c9400a180600c018206803482582d28040d40c00300802258000c0b03142c40e0381001541c1960010001c0c182c821911958a080c456122941d85400355000c1c40c41c982881002e0605000d004140c00000d844014054041e89074a8403a800201070307001c055408210000741e000700c03151001c080c0310103400556600e5150000f91401010640340042c010025010b10398081b0400302c0900102541000c10242d44900441c0028113120606d41c00a50000040346240c2c0c40d2903060344000c03580d51084d2010003085004401c0c00d2014002c0380c030001d6014040c881300070394092 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 58921702 1250 58920452 58920461
    0x10801030305190c060f0207060f090507061b0f0b07170603030a18050402041d1005150a0201090b0108060a0e0f07150203040306020403061b110715050d02030103050705040b0a0608010603 82
    0x100f00d1030007507050f115650350341003600c0d101e602c1c0108042e001720308481031000718881e0080b1218005810010b40585070346464032004948148004d000c803200032030b1000e8025050260350180d0001e003203107000402d80b910204185094801c0c1001a440394142d40070003840c86c07450342c01810000c00860421040031400c8800400919421a050030480030001e141d4a072400a000507280e403e00701500110381c0000b040c4940d000601003000003020340320411171a20f584000c4860982c041e070f2800e5407600700140581c09011244802001c008010000250800011070094001c006845d8181311024102481c9956103c905203034000c2508020710030840448030001d018030300c2da011700603207040076501d440e010b00b280c00c1540283d07100794075600302612440744160003c03180d11130f60800700f41c1940c0400c0503940d500d41c14014044600051b50a900c100b90180040d2500e0701c0c1011415035482d0703160714080762220104d200c1c441c0102d090240e454050300e0074890900c223031122580c603c1c0b0661300c2c004084002c0c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 58922952 1250 58921702 58921747
    0x6060f010203040e0a050610050a05040e0c270a060c08040b0304110d110907090b160201050405040c020f010b0a060f050a03020405040603050a03090b0306031203061203040f060905010801030305 85
    0x10b1104000000c0d414a95414942c4503075001403000500303283c42c205120b81c81102001d06402c100041180400b02c9400400f501d0640d0110b00f0303e124030b0b9444406107107281c864144038018001c0c0c01c03601c640080350b04000341040708005840444146681e0329040d41d020f0380001000304500401d0005010740e0701604003865000d401070105240404421020400008050340147e5200c0792640c040d80603400c00425058205010785002e86055190152030001c2d03014003080340e441c04a0030307000342080d68803920a960181c007001700100080c009a11000e075881c0d1030003101c00b14130350070030307001084502d001b0824804071095900c0d29905170510030401c031030690000f800b040501d40d080c000410070392960321591000e1445100200303d00040c5003009401002c984d07220070380ba2402001040003544001c02d459003100315019840780c030703a2541d10010b10b0018421b22000307118407010600250401c210194201241c2a507110714000c980c03150700448030124240005408684104519804d0311002000001d00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 58924202 1250 58922952 58922957
    0x130303150f0303020a0303140f0a09050114150310050708040209070201090c0b3a09050712081c020309060103021e0d08190504030b010b03100906080601060806030a0506060f01 77
    0x100303459120310071098a00b6081640107a1028201c182055014071504c040743c44d1400c00104986002c0c0c80752140038030000d120040c00c035125211202000000d40000c02c1403490b0b206003410f185881340d0304501401041c03030341e180b02e8031560800d83c0031000d080c401c290294aa0365903030403da035120340070b02800b1500034086c0400c540d40c2da00d203880850b1000550300c0160111254041e44c560350329a20308682e40480356a07032941c1c1c00f0010714200c50703114440050440320f900c0f08085818905810003604015456205185503480c240100741009806030003041103079540c080ca40c80040300d2005060490104586400d0198043c0f4018000361030324150f006400da80c000440300e599240440461130307aa405040480d4243d10204125030006044034400410042518125040601d07607200c0740e00521040c030039665000e100101103420103011801d24005010001814098650b8400d80f45035a050300348076101c0058964004281d0f245030204c0c440312126002001003049842d06000c019054503101410f606 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 58925452 1250 58924202 58924241
    0x9010f0309150e07080601120b1f051009240201050f0c0d0908070f03020c01090b0c060114010e0a081006050429060c150f0601080903030106030b0a030b010329130303 73
    0x41d17540c0100306080c0078205480341603850024900e031040d40c40d50003900c14118010703000e0b5012132020340308001078100c1b50200c84080540141c03e400b515114102d41290130701d524240d50794403509403541c00701c4924400c0e030b0340200820360721003200300c440c0c060544c3c40e54800340081224036039620542d041100014094044a440e00c08141d4030400c218100c0070088016803c0000100001d68000030300f08003c00c00110503d141c0041c50302c0c4142c030398105000b001d0410b001c014221245921403940800c0720030010381004496512405031310750ba00c02c22241c0d03440c1c190a001003c40c240c181030107007401940b00b40c8101c1000320800c2e081d5250803a100d1a5503078004c10180b2603141070031001c00540d007010340f203240d2803111410b10398a101d500000082403541404182814401c0e640340000441381120210f18000422619900002d11001c8103940040c5c52204450000310130f01003601e011900c80c41d03040e0358002c0b0303085441481802c0000c04440a8001d001c8258500021034041c0e004038081810540301c200 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 58926702 1250 58925452 58925459
    0xd0915031503030806090702010b030c061b06010b1309020a0909091506090b01031a060a0c0f0c06030c020c0d02010e0607020a03020d06090210020a02100f02010207140309010f0309150e07 82
    0x40407403440750b20680010b440300d000d00801e801c004880383d03003050a41c8000d01c2000303402d50119540300110711040c2d000700c2d00007a601c412024071142c4024180c6943c0709036078282d40c0d510842c0d007658002c07542c90172043c120300380c0014401c480c078800c550a00d0b10948a044080385440107180c01450201020742d0310601d0b0b02c6003894130303890310f1080c10050300d480180092900c4042000401301d428080c0465140c006440802441d070380c0303500035144180c8007464010703034540d61884c100050a0f0401d100401aa540340b001280c80c5405401481400c04d240e400c03500d40801850801088018114000c0d0205241c07041000e07050410310014260719001910404042e6a29400700d0068828100151040c9588000c0402140340508454044000901c010a10403245400280d00c00306081a20002c0c0051501c128030070318002e4064680560304a204c402d0300c42c45020718552030b640b0603840389001809250200641a00034411151510f420800d10500418140c800c94010052600d950105101302c11001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 58927952 1250 58926702 58926731
    0x303050a0e0d091e050a0909080c0a030206010501030b032b0507050708100b180705032203030615030608060c0304051e0705010e0d02010507060f1811030706020d091503 74
    0x1d06181001d551030f10302c0d0a1801400c0c0001e89072841c52807584e03402c000c2c4208859511140b8000c150303944600c0c00100c070301484c42c1c007407503900c500711111300140503a0441000307040d00450325a04841003038a00740300b008443c00803d40c42c1ea0b00304225007803005030080404030107162854102c00d22041d9013460b074a804842e4503000c0c40c00320380d603019100c107510107060295205064001d0442036013080e900ca850a0801003058070390598014a800100715010001904da21a442104501108845811001d010b072a040c0240909200c2c05100e81c5c031800300a24560440c400e00c129400c0710a801c014209a80f40c981d15007801e9880580700381d60f00e10038524205109905c81e0395236841c52450400400c0f80c645400c0014142e2404000c290f0f1043c45410b04400160f600320b022100f85d9a4040780026070011100c2072078000749a20303c100c20400f025074201d0410006006405243d81004904813194165a0751003242e40301c248180c1800020302407a4100000300c00a081e4400b14011030801090040321110300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 58929202 1250 58927952 58927963
    0xd1e050105040c080f270f030415020601080a0602030a0609090503030609070f020703020f030c03030a1106060a0302010c020f041d1e0606030c060a090e10090b010207060f050d0e0f06060a140a030303050a0e 90
    0x1588119000042c00304048214003103158010662b1307001514803589403428080d12190420030141c035464002001410310750b41688401c010300034a1604001011003810640d50301e81003205c0d642d024241840218070818058940a0800d80040d801024142d0550307092100d000b00d0a034525415204004003034801d59401e0010f80205005039031007005850480d80303158544800900028083c04865906102607684010b603d6011034041c2c0d40c0010140e590301c0031600500c0b84071640e9000c61f042203003c0c0f180b11400700d130a4041400b040720b950000700b124100035403240802e640c0258503034403181f03220a160400310043d000d41d1304c0c17600f8018949550f031003204840328002c9075441081e0100749020f01c07420383c01d1b10685010000a01c0100310141c14214098074038864a00c0b850240000801d0307541c414005a0004802584103009568480310700074006070342c64070180d49203441002100c80128040845107907100103150010441081280340da2819401004d014001944164442d4000f07020120704006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 58930452 1250 58929202 58929223
    0x15240319060506030d050a080c09031006090203070e04050f0a09050a05010e060105180f06040509030d0f020426030a0807110d0c02041d0606060d1e050105040c080f27 73
    0x100458039140c074008050a05d4075450034403041c0710302440b00185441e400b11019a00580025900c0d94404010740043d1800c94084080d0b041da0b0304029000c1808116a000b55019643c6a2a40c8074014005810003060b07420461f80742d681007020070300207052003090b5045010100d0240b8196101da051a86a85080d2855134803020750f10390001c80100000e082c0a40101968210026082001c2c140144114000c00300607220500c1380e901d0b040800c181c07038802d104071440501841f42c204017240e4402d040c10044e40251040a0707114400100403422001301400090101804402951800b514100240c640d0350380a0002c00401500300c002d00f080d80c0f42041700c0315000715a52123280d024000352040009032a040841c1c4d1001c18205c00b0030750f0303140000150064102d0b108841e000d4031409000444c20041030701c008001d00d05016107245410b020503903408541643c10030750f8103224442d50f802096070720040a44500745070010340c0e0006441914505110511a4503101407004140764103c9841d150450820 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 58931702 1250 58930452 58930463
    0x20106381303110109170a0204090203030409060618080109020a0603020d0b060304080714160b0702030319090602010f0501030c0b09040f06080c0307090c0e010c0c08061815240319 79
    0xc194502c9607040114617008105540c100050b2944ca0b030405501e4a0702a200280613a450713407440030843d5000d10945014042c1c081d130401c8160307034592000300000d00a0396001e107005800480400c0f03412040c000c2c01d5031a40c000d0b04810327066142000480095110680020301990384a01ea855240d640c4001980224040e5501c0ca0301d480d0203082c80c1d0103490001081162a138081c154011005c1d044c2d41d142003c442c50b00310916113450886c00803e05600c9003000c00034190010b030003080d0700300f0340103480c80e010340d43d5580c020040842d1005014045981c2070201902c00880718900b040071401d003000400044802410200b01c000c450803006d0300b074414075007010728180c0200000001c142010000d82d0f001340505d41051042c00d2030500d014183c02d6a5000c940e0411440e4140d020903c80e000c01a407005044480c100c5a0a1910a1080245006c11900011980905a0032090181d170800c2c0503800789100314009141c2c84000302c84941a4039503030510030b4050048100d80345040c504108141e0f440d038081e1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 58932952 1250 58931702 58931723
    0x3020d030f02011d071a0d0905060f0f04080f0a020c220f050609040206090607050607050d0614130c09120804030203010b01050c0309010309020d080304060c020106381303 75
    0xc000c3c0c291108010309640d070425906505820f04d00001d408011124460150b20b050a400c59030302d0b503c2d1140c422a2808541000491800c1103400105180710b90002d0008030000e4075402d850315400702d802c0d0390140c03101209001481d40000303041e0040140c2c0c03001c0d004503041c4000882c08a00b80c018207404440d0ba0800c01510340240240c94041c01b40641240841004903241407030004031a840d0140c00a40220404508a4941e85604048a10341c030b070090200c450380c0c0f9184400404541c81000205041410050002440003031401c007048841030041c4040d09800040b464000240b804041030010003140602c0020303c01102c600c06a0203030301400c003140da10ba045006060945083d10081410800308001e2000b82c100c005c820b440d03566209107000300d100d01c1c1500000c1c0c008101c2c0707100a4607005000040c0001c104c000e80c001404150b0359002480066030300d0042c0d00c0e0203108064000c00020b2503d695440300b9412002c03d100c440c905000303e9050050900100d28007590607042280c02c1140c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 58934202 1250 58932952 58932977
    0x190803060f01260a05090102040303050d0504020612040507060219022101020d0f02190804020604090e0a140a02040f050105010c0305070516080d0305090604020d0b091e010c11070302010203070b1003020d03 90
    0x4c03030043c0ca034003c092800a5141c2032840c0d50007021481141c01c400345483d0f541e070115046640e940100d641c01005880002100c0c02c150914580b1010240302d190302501c9407442d01c540380c0208428002d5100e800620f8901c44010300300501a03400e804155146039558200545101540107100f038008008081a0058a5050b0000c10000c191101d220200500004070304110040c0e80e214202c4050b03807032040307020803c0180810011b1401201240081071600d854002030400b100014048108034002c0328113100c50a24043c6000880300c003801401d001501d49440c101c08a0301030801003030001c2c0b06004413150744080380300313444403a501c0390040c1e505500000084240180c0c140582d07604910204090801414154002414410303450002841d40100800044108100f03000c01d6030440e075401d6440601c0d0b580710409034000c004400e80304000c501528848011a0340001c0d41c2001e070f13603040e00190315040c0703941ca58001068004003c000c00960002000c40180c68665075040120b100e62a0b50500104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 58935452 1250 58934202 58934221
    0x14070f023c06190c031b03080703180803010603020a05190528050702040c1112090315040215160c0605070c080307030c0303051f030b0603190803060f0126 68
    0x246121610701c107260a00c0002c0c3e1004210031078800800560505104003002032030140c61003600c602c2c03003840311640c07044601c09154102c2405441800d05940c1000075581849000f030500803e030070082c1c100340f0144010301145010b03600505000c119410070505220402c005030030000d07640c0202c0c1c40040d80104d4641040d0310707121100340d82007581d0811440f00960b10341c1c0040150140c110040d108a0312009024001c80c000e003001802d04c40302c4e0068070003c11001c01c07800c0c807540c488001c0b103000380705008010609220074031141c1d0003030394000c1a0404542302040f030344100b6000fa104000c03500c8800c200050004003041c10802c02061076445581d10303001213081000411440c3c0d80b0a01254008021031400241c0c030401d050a5964541400501500c1d40c10080c80300780d0303040e80d2045540d00407000200a001d080b206491180b18118121001d155141d00c80c2c08100d000e880000b48025001d10204609241c9134514100200040c5009540c03000724007000d0700071102203110701660300c03c8803003400103110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 58936702 1250 58935452 58935559
    0x506130b070807020a0b060a0801020a030e0c04060305100504110d03020d0207050a050306060d150e0309150406050403080a030b060d0e0105010b130e060319050d0e0114070f02 77
    0x1400d418440303000c1c90605006511541040b030000c101a501c0320000d580c2d230f510210340d4005044910000c64075106800005401854050742100092007801c1a8044603e80fa004010a6070360242c06485c4480c001c244040181601403c11149000a0154024291160700801c04002d009600801141d040c00102070b05040050700f16074003800c00f10005002d41d03200000c141c0c0c0c0104095880700d10030b000c542042100005918114140c140c1801000351009900201030000a2011a400e031000305013031480405911441c1b203500c0c04150203000410108406002900481129042c0800c028040c2c2000609070ba000c41481e2540c19a1400700202e044801d109040c05044045ca0881c9015005441c038400b4021a04c500104d0782c017000005907094034248009602072080d003408580c0c02d4843e14185444480500f0480b0006408450300d01c559841600601544120028140e00d00030090b1511500500d010a060f6000a590041d00f00e041d0040707045201950711040381c02c07011020144030b018000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 58937952 1250 58936702 58936711
    0x10e0d0915050901180f180f021201120809090f0103110301090201020319030e070806040b0708100501030218120708010605040506100f021203090601091805060408030709030506130b 80
    0x11010710301d280340001d410400311040c0820908003034055400600400f003882c06942c100e40e03001d13a262030002400380001c0044a0310000b144205010b00c0018401c89812802414001d004101500c40100f00107203070901d03480c80f444d02882c0b40d80d140c03540e40d0700447d4039200e080e40c100f071401044100401c1881491800910641e2088000340141c2c485030700005d60340e00403c2d035112090f000300c1c03803a0304245010341e000250038613100c0103a9512030341d10364aa07915a00200c0707013503030050b40079800074921501c110034040c4203800003c8803038103907070030200110b000b07400040b91034011130f90907152140c0f25903a004920b0032011440d40101443e504004000e801d49405502a5000c4c904000500840d44e8031141e40380311103da24a002c1310351960640089241508174a007151503c0c0300001405030040340428071034142c41440070240416070b0140e00d6095407101d210005861900174002087c0040c19960083d600900d42d860700c8681e05490707448003401c19400399540c0304079140301c4468208110f08211800d502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 58939202 1250 58937952 58937969
    0x100303030b0d0203070b030c1b0f010e0f0a0f110619030c031413020607021009030203060f0123010917010504060506010509031005040204140a050603061018020d0e010e0d09 76
    0x607403043d40404d640d12024021032061000100c000b40001d4400700c00d0703602a03400311504c0800f500c0c8488030030f0b40305d60440d60405120750030a20190500c0c00f002601a5200840d04000d00082c115a1154108591408003c41e0001c00741c42150344541d69503405082401910460703040342800e5101c01608a400d0a08520141400c0c10580003011080d02081d0703900c26001c40c4070012156503440080c16a1140941c0207520a0038042c2084050354401403481c240c1c2e100750111400c689507050b0100b0442c409200304628040144000c03d105ca1070560500b041030418184074071840d032076034000026000740070024003490395074101f00802e11546000b04c0d50450001c0c2030803440e0234042c60101e40c44003010250004040e48035401324003103484661002d44040003418003038a040c240254800040c20b070a0312607510a104840c0800e1180900e21310800840d20469080b4145078642040c082c003035084080c461000c40c2e0303110241e001b00322081c000c0d958446c0040e4040c000d0f500007040040c00404594012802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 58940452 1250 58939202 58939219
    0x7050102070b090f03030f0d05010b0306090c0d1104150e10051b0709050f0405010b090903030622020c0c1002070303050708070206070c0e090f0102030402030a0f08070b100303030b 79
    0x1140d80114a4a040e2082c1c042055542c3c4021400b180380340c5072040c541a01803100041d0f45508801004c0a810200440709041c88203076030703514a001941c0000d03201680d0003102080452002e024140040c070202000c250086003086540d000d8603031640160b40b00003102c061074502014802c2d8032901c0403000c0340c4120f807842c10100072100018464051400301c0310310141c50740d48800880e44100080e83c01400c940d10140141e14001c85109110f140607142150658201099031210740344c00c8441501c108c4900c0300860950b6201c908000e5102c1c0d03030405002d40c86070f1101c0248800d07222800100038007003a0100524044030340f98148284071b801c2d4181e200c00c5420a010610010b41d01400701c1d0360b210381100009458000302c3c00061654440e2000090161140b102c0c0041d003070008120840c8a00c0200c0c041c0c80c00d044910318000d080c3d00c0211002541a00038240c43c800280b90442030500301c5019085650a1000c0c6a84070640303028240e44600204216000c00c008065040c02048000744040d5003598 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 58941702 1250 58940452 58940459
    0x30b0a09150302210304090c08010501020a030c06051e0f0609181f020f0a031a04090b06040c0507080301080a0506060109150e0102010b06070804180204030c23120606040e07 76
    0x3104044030b400300901c211200341c641006004030415600e0196501800d89035920750341c492110082c40000040d0340490464000041c00f980045011301100e90581c5030880c541001d035851034010000103000e8504400580e2214043c0c10b040d6003414032800c5c018a0b102210b09101003007119401d001009900240941010006018404101c07070055003648241c1200c520528031a40019004045914480400202e042840c06a0540102d561050384040d94040d0782506004d010544915075405400008540c0125246080c41d44c0019040c1c0c10601d081410312604e913490201c964800c0c5d00c42186a40001218414002c0502419401001c2424544802480c02d4011181e00010300c60201c04d0104a40c040308090f4003c0d0014a69030030000c250300e0343c44906103042c151b580c22130700584800c1c10701c1d65248e50340e0031507038030840741502d402003074030030a41c1c1c80e10004035040f6849074003002524040c104800d6840d100c18004d01d0449240348040d1580745801d4081c44112900340e814120b850340220401c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 58942952 1250 58941702 58941731
    0x305011b02190203190f0b0903090d0305130306060f090c02010506010c0609031709150a0902010806190e04110112150506090303040e0a05100b070201090e15030607030b0a09 76
    0x41c8035501154005060280301d400040e0600c0198011007284107030307085d125410400c00d00c40440c41988241e81060198440120f9a540c81c00780c000c405401500c2d0040541c046801038021701001310501031075200b040c1d16681c4140c2901c480f0f5002400c030880c5d80006002c00b913a40c0c000c1400d46400c51000300458648040000c0440100d100003420440c6c4c0d034144082414480d0340c0c0381a590014000480700b900307105a190303a80d40240780c001400320b404000418803003541401080f40050b0141c0d00d0b00c81503120442005602e0407000b6040c0c65921221100103490b880b41c420082c81070f40180c62280214240800262829507606505003400d440c6c4041c5001000840c2c1d5080160783c400d03560141c03650192000f00f8694442e98201200021308a4200701c03105000d500054403404e00580c8041c1d505a031031152802c00e002d0b0107002400b0900403082440100c54081d03685031b200c03100001c19028200780b000803074281038042e116040002d03180c1c40e1504850130014254001001c020030104a1000d202050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 58944202 1250 58942952 58942963
    0x703050702060306040b040e0c121203040809012309100507020d0602030612011d070806072a120e0406080a05060c070201022401060909050601083c010305011b02 71
    0xb8031444011000c50410303152648500762071280a44100b000b8200416180c0d500c40b0700908143c0b1030046400110103450700400d800b1001d1002041041c11600c5aa46403035203500702c081054100f100401e4085500500010780080190350b0418040c1e031125114140318400c0c26401a06060007010082d902c0180c68403c0106084c6810500052716500c4450004000c40c0c05840e00c00b00c25820948a0b004003010b5580c180710818282040751030f001c3d986d00c01c160301d400c02207900c240070440006110202c941e44003d030840d1100b201c06580740100d91a40e0342c402e0600d152942d8000218945000070321401d2034455400904580d000410040c12596586a56418000c0c010f038400c01c008104071013164020030541400c010300d4180d810740e206078503075003410090f000d11900000130092240007601500503c951401410103a580c80c569a69564252160888074451100002d60070404142c40e105164072810070b01e003000084c0e00d0746500d9810f04a003943c100205040b15045010b080480380e5400151 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 58945452 1250 58944202 58944217
    0x305220b0703110d0204080c0409020d060b031c080708013002060405100c030e0414070c0f06050a09050c06040501020a0b0a0207050714030f0601181d030c010e12070305 74
    0x120030116515440c1c21005844104016100c0100106002e02c0303034820754026001341c80c1d03080d0440e41180300d81800c020594004030310181d0400d240340406004203602e070304455000313400070741201c180f01d82c004011010003501c105e280c800604a40103100c01d16501030000ca004000081018481007089112442490500b41403200e2030f02090000b4003c644400007550000c0c0030081850740f00c41c660310300240203040c140030200c00090f922848100c151405100b124001c82c100c034080700d500da0b16103a0075951560713000c5c4242c0d005801350b0b903000b00007005406901d00c180c50b44800400c2c140780c6c0b890a186401c400109051103100280018002070742e000a640e1111600860114081d44403650907034028403510340060b209004841d40402c60f0304108920501000c400d8049270080e00e90049204e4503901c01f03005081c0f84528001039003030a418903801c03800d1502101108001040da698081c1480d651040070f101403181d450b40342c00716410714180030201081201a4030107260a40d81e44c0c00800d5840b0f90f81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 58946702 1250 58945452 58945463
    0x40902090f040c0512100f05040903030e0a140c0a03120c030519051e1c05070509090411030d020f06010302040f020d0f0b12030a0c020d03020c0d060c030522 69
    0x1654500e2991007481d01d45922102800402480d506004000c00c00c2c1e001040405030740840c180821682c400c42d5107400112138041180003506400d10b03041001031b02c0c1c0c0ca43d00740c00b0140c5914581b95209414884440140d214034a00400207180749945410640640c0c9402d2103090140303410000b1a4440c60500d04402e1986080c403000380f02c5140641d0140210104240815282c070b0b40740140c42d17000300c010149079869241d50420380400766005400c600c104050241c110021256070903000fa1250000360300440541010360511080002244001d00c040301c050f40c00c541a00002080b81c1030620000d054025030b0b1001c0c0103890200c3c0600d5594642c103220090196580d40d003100c8a41031250706490803040c10f41401c1c03259450152030781001d40319241025115001103100c100044c0800000c61702400c4da29141c1440d584031a408028505031034010680c20342c06403e010b25460f60b1909121b00d1514441c42002512408040005048070001003101000c41e00f0100041440d1100c05000581c0030b5124 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 58947952 1250 58946702 58946707
    0x1005040309150305010504060b0c100c03020d0905060a050709050306010b1c02040b03090705030f1f090506013c0909110909030901032003180309032d0f03040902 71
    0xd1608980d001035550160300c1e4845110481042c20303500d41c11850480724116800e01c00207440700c8144034184070f00c0d00c110302c8a40c00004641c103405d03050741001d1040c2c041410018207043e244c0b2070b4403013503841c6013100f00e07600e0304003804000329045030380700381ea030081d01c6458442645800c0001196480106020701c2c0041030000c6003a03086043d4880b840b000d000292242036440b580c0e81c141000441e001514440d9685c003175480046094100000d86488040540380182400c4649030381c4403030001c1802c1c0407074038070fa03849442c0da001060040024a0081c0a8140300341c03824000c40c00c40046e2043e00485500302d0100780d0101c1c15049a1000004065403000000083e42c095280340500c007025841c007605030046aa5420810032500105c0030305014602030300c0600030124a039280318065021040000e261280a1004c1400341d800a2008010340c40240d0440785804140130020f407520740c0c3c00050b80ea00304c60000411101c190b00314016850301c58400000c107851840c5210b450340300d00890007041c0c20107901 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 58949202 1250 58947952 58947961
    0x2403050a030809100c170f070f050d02210103030801080109081804021902070512120703110a06140118090201080403081e16020c060a21020708030a09020a171005 71
    0x500a000d04c4074840d50342006615010b100107040884503c0c00c5620007803102c00041c01071070800541d0307481458980e1b51461004e468000581c2c06402540b02d1617481c40d401e116801d50038140e1841e200303110444104082080d031542c82c000b01540c0058212001c603905100071100000c0c0c5000540e1110380112800e20240d6048a000c200280200040007400c4004840c1d0130142a4000c0b035000305540301652485c822028070b2910035660303084107903139180b00c190801140002c13a201e19104000300032000705907295003031962940004d4075400c40c03c50828078804001001901c0e0111002c90b8101c4030000103002e46002c680010b003241800070f0000d01442001700000c0c1c011011512030b0389090b00c0042403004681005040b81c501408141d08000c0544181c60450743c5038607150080e07502424041d0b4621140441464002246900141300740d42c10507020b022070000a50b50707001841c424114224000740c113000d40d00410078045803a5000c05c2451400e02c034010f80314100070030080c0d800c6850b0800030445881c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 58950452 1250 58949202 58949221
    0x14030c0702060d050612030403020f060f0403050706020102192a0c080a051b0108040f1b18020a030506040c090e220b04061a090106030f09020604092403050a0308 71
    0xa0311002507028030005100c0701502d036030780d02c900d0050710107441d15128600c145103800d0ba030740314070f000182d441412600c0c19195460804003c00000e1040c8010609007945c03640e80c2480c0540301e03040300c0e0142c2d4001c0b804258042d40d61903804020081ca25044102031b8024811490512a5042c0490f0140a0704078200501070362382c45480081812070300319810001182406034860700101081a03448940f43e058200c03c1d03104e04c4545016a8203c2084040c50000c5e40cbc81a00d500d02c447c00c0d80c0035601c00319900040307481340d0105513079007021a07a40c0980d031446a0b907070081c02c8490090110388503502c0c0039811021260f11590410030740f2070b01d0303120070200d8445000300d55884940c00c4243c00008209100f441c10444c3c581c1095010301d02c2142e0600c039038140c440524003001e4580c800c0c1038010140e04010041c4a202c1d03000090b21600c080d400065102950b000300f1066402500510010364a41c44403c4507440e1034140440c0031464803400c46a40c80c1035a490945440d40a4405410070001001045040c807 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 58951702 1250 58950452 58950457
    0x1031517250302090604050108030f0a1803150f05010807120c0503071e080705090408071b0303020d0212040803070204150906141203031e100914010504050c040614030c 74
    0xc03044071500c03624401c140d80c4a401140c0c04100d0141c032007a00804d8446c10300b40a07580c140d0705204040d500700541d08015070b02e19000349584400700314045c0510270707841c40806126005140a240d52004050355128010251251072010303e2032189000c0c010030402c0c3c004210041074800c0742080340500044d40c280400b4620040d0011585030140709000942e0380461458880c61400d0343c1c4004209030303a195141380d140c144910074141c10040140016000856103001496550301c900e140311045c001d100002e0054012680003200964460184104507680400607600650039607a64149050b04011f0142e0301c901620100a001da07072500705644540c4103200c00300b4068030203014104002c650701c8116081aa069400c800d004a08201c90b080f000140031040700c1c440c0480c4181d00001c54a444140440464004c03c148012200d0ad58045011085401039202d54000300e011044154107103400c00c011a44090043c0304070781c1040204011603030700811940241da08002c0708680700d5940c818802030b1031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 58952952 1250 58951702 58951723
    0x507080402100503060136050102030c0c0607141525090302061b0a121b0201170c040504020f030a050717010b090d171c0614040203040f060903020601080c01031517 72
    0x700c07191544c109100030b410241c7d5100781201c1c1241020130b5442005907101d10410001c1c0e40b154000c446082010300b401401001c4640c45a64103012001180d01050f04007000f01d0f04000f0f64084020512540c0c1d402c501e21105280906940d411010507807000180c452000c0b07110090007800049050a1030003880002500020080010340c0c248821038644481400b0618010b40080b4040e01582c1500101d06075180301ea01c1d03410784603108011004084c200345602c00600e400c0005004000c08122a242c078001761084485000c403064a90070401410000ea031760041503c800c00008412400718840a80103240c1100c100961240e41c42e10000040f644003081150040c00480301118095403c40707400f8010080c0b080b260800b40e0650f030701c840d00082030b01c0540c40707801826904607850141d42d10301980115000703171040d0f0301d4241c0608117a8a0700c0654200c4041035015801c01401040608818040844008000d10b020852420b40c04640540740303200303026044090000180c090b0042d0010040e00041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 58954202 1250 58952952 58952987
    0x904150e01030f060e0c150d0b1c110414070c050f0d0f0807030b030304061d04090b0105101b0b070e03120c0706050c06010911120106030c0305070804021005030601 72
    0x10340d81c40c0c0c10003038003010000710100c60f00f901d0481c0c0f8443d100400f203074100d126034004000802480800d45809982e8100300310740903c840c0e9442c0c05c1242a0fa845000c1102441c0a2001b243c500426050205040001024203405507040031044489404c2a0080690102d4141415141c4841e03504010b498143d1381e880004640c0300340900e2842c45500f00b6040700e02d004042c0d0307a01000fa0f40e010701c11800d0394038281b806505507109201c1807280c14000c903015000308407a0b034001a07510400034000303000e88041000c10f80e880d80e1f80b6001482281404013944c03954444505004030707045a1200403107811001d4010140082c0e0021022401c3c00303105066162050000408449803901083d8141205900400044010b44a004000214540a04151081004014003602060b0302c1c1c40e200402814076408e030052024003c015495015601c43d03101030281c2801e0740d0020f0446040c5401504459018180b1405d1003242010000107075106528644080382e145081d030b440e41c8603200141c1c1d40c0070349400d42282 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 58955452 1250 58954202 58954229
    0x906060708160302010f060501030c0e060a021218010f0c03091e0509040b01140d0c1406040b04150201050a0e0a030c03030b040c031401090203040308010e04020f09010b030415020a05090415 83
    0x203142c0c2c150800b01d46c48014a0b030410015641c0d030f00543c11074041034404004505244400f100740d20b05203003d400398480c0d50040d14800c007070070072a4140a074401442091190320a40440e4030301d5901c0a51180c20408506000c403201c5500d403005003d04200e0700c0380c0c51110041c1d82d01a80040300c00d0703129000038680503010303d06908191a0140482d00709024031040e69041165209051030000402c800158010500002c05810004210000c1e174030850100c1d042101000300044220303555000b040105184002c1180c602c2c20800020300791400500000b1a035418901c1580410a02041880c002c941c98149040000c11919054001c0e0012000b91036000303140840c51600590150840752803101a80741914050ba25184120224041500c01600040b030500061041501507160641c101d80010018244147c11900141d40c000b42608484400310000c0240410801b076446008a481c82c415030660805503078290042041c0600c2c1c035600c1c0701e2a11200c1c0b100200c3e02e07016503500640301142c0b20b000e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 58956702 1250 58955452 58955497
    0xb01030b0f06040b0d020f040e1c020d0309030e0409031710030308010e070f0f0c02090411130605090705090f060f0c0d03060303080c03040311010c020c010f0e0906060708 75
    0x21042030441d119541191a6400107040307181c82c0c818040510801400088030404907020301c82d4101d403204982e0b412581e244c92082400b5420014071140c141940000042d004500d00000e00340f035103600464040c581040300c44c00010790008086440da000a54002a40c0780c01414110741403900c1500d01c24000050ac3d090081c081000d00c13407842601d010b510358610700c2e66548a50b040d000000c6440800003022822078404842c0b255080c04805005441c0141107148207400040700e001098604507505802c01c4144411030900800c0c100c5022040d8408000e1a03140001040d121003004241004114002410400c0c0395220300d00360808030b501400060b1202503400700012140d0250101458a110386024045910f100307004590a49030306548a8070542c917010701402e0346400240c811000c0c80071654001d041d8010034410300c0380c000306541c02010034444810014010600310140e030310402003132141d85a074503112000c0b010380001c0161102d0ba641c83c03446c10000385d18024880d06001519255185c0e0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 58957952 1250 58956702 58956713
    0x60216030915050304080f1e03070527031c0203070c030c031a10030609030c080309011401060201060e18010207050f0304090b0d020d1106130b040f06090b070f020d0b0103 75
    0x81c0503503044515100150103096000d480902084030000c003950000c11850b148440301d000503228000607040e50041085046071865000d0b00212a82c50018030041103034841c1044150f01c0c00f640049100b007450150f00d0010100342c03603098021741d11582401215410107014820002c40d0304c0396410179007910007103450307103492900800e8922003550b0100d150450040030b0883c03c41c80c04c0c042c1f8958401000414035603a9101302034152024140e0600070300403182400711300c901c001507200b0b100700f80c0002501800d42c00038600c2004d041c0c00c840110b80c90300c0003d000307100a4540b055042914004020382142e82108020301911860310020028041c02c28454410100080904260b0700481030600080ba4520244021181d401c48040e5200a40e4603180b000b003402c503e01d1508521016101e01e1614034481c124015000095201c52501000002d0030450302c045500c00e400034110b40d03d00007032064600070a03001c45015407500644140e910029a404558070550941211544200e0303422807580d690800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 58959202 1250 58957952 58957967
    0x50a0603060306200d050603030f07060b03070b0c0a021516050f06060301110a050706110a21020306031f14010e06190501020d0c050a060e0303040c12080f0706021603 73
    0x40740c02604040c000f14001c1d945803d190040e40000c0c09641c1000020f64a11006e400e000c0c041a405000810a0340c1000d02c2c11401400c0941c02140003103108113841041c507240500356403080c034044005020b4900c95590204a140410740c040703c010100c4401001800154840c40c4602c0e0703400c101c60040c0c101041030115000b206180248141c4440b50b54103018035080c0c51203d202481e01100400450524600440240c80c07a50300a840008107904002c50300030203580100c0300080482da54003609a02485095100880d10701c65007001d5045081c800c0200796114408851200804140255028085a140c2c8105007034243e50a05244a5030b58a8400b1003015065581901840c05580c4510a551f00c01c00a002160010707801002284550602110801600007045555025a42c100d1021841c076004100c0c024085002569903800c00d441c0c140f10214056001c2002c0364107070952400400e24410070b5800000203018001e0f41c840c858a40031000788600304c075210000d04030903014010b00da1f100c1c40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 58960452 1250 58959202 58959209
    0x7030f0815060403060e010b0a0e09010c14070210050c060a1d010e07060f030e0a0503031f031a0402010c050a110909030f030402150702100e040b090906060d02010207050a060306 78
    0x84080032600c5030012540d0103031607107859503002001004100001502c95000c8000401c03070324000106001c0304c5000645500d12a4000c41a40b1240414400880340c02c0c481c04200010a04000505a4814007005914000c261010703100f150260940c1611500402c100e81c102552002035500707516010000100401d04240001110014440c0650804105200315107039191008010258907280107001c0700d00001d8402c0000c105601c4421110a9840800040011902c00c5d005140c885ca401415080844442e21702d100c010b0f40c44840030408903442060789051802d03400031200141d551400142c03580361001e1001403072131194444103020310a0580720320903405c2c002c450504140e03e5500c291503036401b80180d10300c00204100046001850b00c102800411490110f145080c501d07590006030303800e01e0011610b000300d5015039005034245003900c12030349407010072a12103109060500c040e96640c03000a11a50041e44980061021341e030007000540002c0400424071050580c071054020081c0a0313030711 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 58961702 1250 58960452 58960457
    0x50a030e040908070624082109010801060c060207121e0503090c1c0b1003030e0102011803230c0d0816020309010f111002040305190809040b1507030f 66
    0x4000c041030314150040a85280d0080e5225091000d180c9651340180310000c0c40121302e0210000c819260498166030700001d015440c0584841e00b5848c81380e840c0030401000b900d4002d501009851b910f6a00203018505403085440c2020709001c0518010009208601010b000389000c3e4400308103042d13100e200c01e440c280600007030510006060506a0f00780c04244c910007856045226005120305001c01c1c90400d40203441002c484070240c0f6101c10f99451400c0e40c040101c02e03061078040c414150400d1640e40015000c0c4000c001102c041c03124030310b80880d44140201000407440e110758074005030346000100803150707807482a07841c12009085d0b56a0301c690403074003001c00c10100c00210f002d0010381c034080da5181035130040c0d45801c003481e0045800120741d03801c130014000030204c1030b803034a00200b0221031760394040c0a0040c3d80343d0441c18401e00d440d032440d0084c184409203c0c07002d40017641400c1680d02c9880c0685000c40d03808500d6001480300301c410714130310318881804a0200f007810f9001c442c104152180c1d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 58962952 1250 58961702 58961717
    0x302040b09010305030315031006030605180f0309330919081005060d0b09030403200a05010e040b1e0f0105040b030601050d0b030a0b01060813030e120c060403050a03 73
    0x18801c0c080c40c0007003440090b000350030500002c0c0340c0c101c1c516102e401183d402801d50305d4012599003c82c04036000381d0000c0e81d159581d4410002c003209602a01800320303042e41d0061501c421a1401c4640c0d92148006c503a014040c8102c041e40c1c1c07000c070340042110240d81842070001400c15400c0035851900078004940c82044103c0e803410343d149189032000c00342d03074110b40036014000341140104094440a00150b4001195000c03480c003152a40074182e0203104d00700d001c1c580c2c1700d185080280003209241c01001e08040d8103820380c811075803118103c80440740282001e100506011001a004003111004d03260001ca4000b903e5000d0303d101501408041800c07640306501003840d400464044c0500d0003423101e40c4030108003003441580504007034030182e481c4000100f42041c0c100d02003800c00e0301e1030340d080b1049410400144121034224203016844007403141c034103580b100e054074002c10944414100600070018100c03032018205040c031400035021405445e00350b0b203590707030f01d401541e03294460070039400107004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 58964202 1250 58962952 58962971
    0x1305070e120a0f020d1b08011103010501020a030f0915080405070b0f0a0503041b14030105010503010510031b0b190e06040f0b03090c10030603030e0306010e010b0307050d0f0501030204 81
    0x32846100741d1440c0304028210601070356180040a620020240da002c03014110f4000003581080d016013000340390390b41c007003032542c0b5160b48582510303d0040916050b46d0180014005070368000b41540001d40c00d071422681c403400325031080d98400541d410144129160a02c88100c0c07a8012511a020718420400c8595681c1d80e8800001580140d010a800b025005c005907200144100090754000d802031480300400309078040c000e17841a41c2ca80c0903804000d840410003a135480d02307106581c01000c041e0024403492400c4c0c001d50814414a000c010720300102d00d10400091031010050b80c2c040c1003050985035880810341130f02d001c1da05c882d41c540e000048400c0e075100724600f071107005e480c100c034015a000d80750b0506000306040caa0704028100300c2c0d0f5106100b5071900d981e80d100a0459401314649001070010300311304004001860300707010580268001401040707800e018200300c0d03044680181800341c90740c5801f501103c462050410110005007845924182043d065002c01d0483c0d01c2180d04110f144036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 58965452 1250 58964202 58964209
    0x50a0b100905121c30050f090115090218030d0905120c010e010c0510060b040f0801060b070f0c0e0103081309090203100b0312130623030601030b0105091305070e 71
    0x42c101084c0361094041255a40c141d0190020802e8403851200c40c000b112012041056010130001d500d40400f40c0716800d120034100050001e42e0016202c0c0000d010132010810302c401781507264130511002d243c0c00110304c003a02648101d405809038004061f00e0f501910010001c1480043c1e002d024803078020100300292410340025820508407068460780d0130540b07008010f4811044c001401d44460007901d500d244140c110744612400741010402c400e454a00f400c0081650400c160444031450385041c005000e000c0c04541074614007640f001c46d031410881c4a1904032050040365000900c0003035103500103c10000441b000d00510248107440b800c80315512007030030055403200301002c1d406030011114428489415080403005000143c11120856020010459160301400283c1d0000a88a4040c4040781c1d00545031034190980000002c1c41e5080204007440c0d61001610070b5060541e581c0782e411032070340150306849000c40001c10950046031804007610103000c0031111100060480c0811845929 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 58966702 1250 58965452 58965463
    0x40506130f02010c240518011103041b0503060108030702031009031b08131202090a0204050114030702120a08040c0609081209040b0d080d180209060103050a0b10090512 74
    0xd41011003440301904030340056502c50928403081c1e0b1740c10860707082040c1c1e24909403010008901c0d14440024540360111940400601c8100c44880d0782c1d042c56040400740c44050242c5c3e40150b0441307090081a04141e2109004039440c3d448141c05004200c0006010394011014065081c020342c1075071a81032040b0b80240864200c40d60007404a07020b42c0c1a4208504043e10240c52503204889003803a243c141e20301c9844940d1a684000500e01d0203034128000c504065400c076070800c3ca13000c81541010f080ca4000382141101581440030301d40044000780c03075a8402c008105203000c180b1016680d428a451008040080c00c9400380e404c2064080009611446010300b00102c840001c058110303001c0c0303001d050134142d011461456005440d04480303a070310358903c0003503410f05106084907942c030409040e0310003d854501e001d0848014100c40c41c503000d070300c80b551a264001000d207000506a5034000c3c0100c02895090707500354100120b900304800682c0c0013000da10688a0840340f01d2030740428860825130f601c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 58967952 1250 58966702 58966741
    0x30f1006050a06170403110f0708070902030c090607051908190806130b010c0515010602060a050411040b0301020d09151d030a0806060d0207050313050609010c021302090a090203040506 81
    0x201111007545081e05184c0e41c013500f10b071091624001e89014420002d140104082c21501507800451040008c0c007400c01041c4010030500c0c00560a600d05201000c0ca1070080381c201d00d004500000c1c5040030441c0c03c0c403c07004000714040814030300b035031182419142c0c0e4009400c01100c12245100f05d0b521680100e12062107040d00070620800c465036000000c02401c0d81c4616203042c00030f5071140c04000786040c0315809102844118418140d1301d04040207283c19806000c0b1444503141000b400045104010921031040c3d0a607004a074940c0b119010900a118101700410341501d4104183d0030044e00032022070079818292020700001807108842e10102c0c6404021840541c070401401140ca4020925a50700000040c885420609080c0343d0700181d82c0a114119025080011840400c0d46401902c1000e8581030711400c1c1010702040000c2d002c2406d4203400f074840e242c040580c0c490210941c040310610040906520b0005a40d061824065001907400703d4a500409001900445000d9802c8091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 58969202 1250 58967952 58967957
    0xa05161a0909011a04031712130b0408130e040f05060c040f0e060111030a0503010312090503031c0e0307031106070806060304060905010b09130b070809030a110a02030f1006050a06 79
    0x3503481d0011416000300b04c1c20460351142e400707100000104540118058042403c1c0d03406540c0d6801964404044140040c2080f60520401c80703944080381c01c0340c4030f69501550265071142d54a054030100c0301c0c140d1244d4400600d00340c0030710403c020010b180e400902200c0c440d90407aa81601da07407203041410300560190b01034204990408108408200008a1300940706060800c6280b8002e0012425580070342010f030040340c40000100b08009074403e60a12016240c0344c80d528042c01d00c00000d0b160b00c0391321a92160559900b4034560281c5241d80700e16007070040c00003100c0e0340b9642840d000c0c1c0b860004000f002010300607440010072590003900035600c01d080081c5102d20311f44c0d5a681d6803008060030b6205941c15980c80c070310080f042e212900c04a000d00116070800c110761015181845440b00000c091004200100060000117540001521620841390600c0030540c1e100b460601d15010300420003940c180304400034880e031894003141d00c0051585090040c00500d40321420321000c2203c0f840303240700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 58970452 1250 58969202 58969219
    0x150f050c0a150908034201030902010e2101061208040605070302070e010e090d023d050109020c07140904020f041803030b010e1e010807020a05161a09 66
    0x241c100480b01404111458001910b107825850b00f50050b00f00300c540c509603c1078150865440080000c07112000b40c1080742c58880c40004690340d02440400030031b11414140c03150151021a030082450001464002e00114242440003121040200018041c1400d0b5460700c0390120700702a09081007440250011045440d082c5006811100f41e4401d600c2541180100007000c5010f050701c81c40c0c903000700390011094006080031b00c94582040f25001840c03041d540b00c0b6500d0201090300c60304801490200014442c2008085c0c01e00300358081001ca14600c42c81d103410004504459958007a044681e050804c45280548410100c002c0303048196403c1c1c0d0000c1406c00241c01031504d83c030214400701c005040440d100401e1a2000e082000da9041200403c1d110f1101005659200c0445200d80d60100da00303598101d84520b0441c8038013070000055042022070303400514007034020405d038166542c0c0700b000c4403400e0307040d0101120741c104a40030354007032440c0801c0340b001000c248906483c48008020030604 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 58971702 1250 58970452 58970473
    0x1080903070323030106021b0103020a120509070305010e010e16081203061201090606050907090b1206010203070b010801060807051e01030b0a09020706020909010b031b07081201150f050c 82
    0x12400034100b0904041070022803e0088503903000780c0a940200816001806118000b002e9a446c201000729114100b604c14841d080c01d0662000005450800c40100000e45031102e0302c4050618045070800351903582002201d14040c0d0056011620034000308003903880c9240010313844410b10005105a01c2c0642c1b00c0c40c00d00211706440c07801540c100c20000c108001c00c5013009292800e5803c042d5096422960b200002c100c1c60514141d9103500040758030709000305074108040e5000c0307401410383d104203203041800010804e900030011603a1282c3c01c54410981982c0d40c4030308901a1066002d42081c41c0a100000a05030401c030623003000340920715400100c07110709a00110000c1000000055221b4070ba11400100b8280520003403003402d001d0200035a4822000f070900c0242e1006a100c0c020101042040140d105038500108454913540880c0a580b00c1281c1071540c4140a1600d41e000a03405100002070704402c0c0b045032030703811030f0a51521404540058015180f900800d400515103030051403511 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 58972952 1250 58971702 58971707
    0x20a0c02091308030f1e01080604060606050f041802090603010b040f060804110f0f120c0102190201020604170408030f0c0c09040b160c080a02030405030f010605010e060304050a0f11010e010809030703 88
    0x707962001503841001d80701d58640002c11b040000030380c05070071942c202c9010310003400003901410014010390b04029140c1940300034038a040380300b107114543d604480d0948019400381c068040b42c01c240c200074502912561914250449070740144101c6008024a20380041c816018a10f09032040750404500714215010009102d5030142403c442988140c03642c0c0c400e08183d0f1200d04c0203aa65120000600005c0d003c2400039103001100c003000842d141c03981d83c5050060307030700103841903200c2e9000d411400110079034807000840b4041c603000043c1c1800701051075444521600080c015009808045801000080e800e000158a0603a40a0a21580c0c00005415525248000c52288009103890b422041581d102c0d17941039080019000c00607000068108504e00c1d0070000b902505803000c1c000c00202e4078200000e0200034503180c0d8280a10404000602030140c184541c02161f50004105110082645482d15600c045e4040b641c6c089000c006100c0255482082954170458006000714034054064409 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 58974202 1250 58972952 58972981
    0x71a0a060501120e0102120c09030c01081006030e030d0903050702090f060d060e0f0f0a120203040e01050904080d180b0a020a020a2a03080a031a0f01030e010f020a0c0209130803 78
    0x1104c0c1542d002c0001010030501d10381407030310421100041e00c2d00d03a02c121040608010b850381145040100040500c6201c44081c002e2a0480d2642d06001503446655450b5900f1400350010b07654440d483d00354680103140d000317001814014400c440a0400740c0d51000e10356600c2800359030003038000340881c801c00e001822640c8030000321009041191035006018010504e010840e028512031504503000c4c0384204842008031066910304c5001440c14141090071500f20f0386014410703240704007104404034091100300d504580c0141d41c2c01c1018046288544541c0303841d21007000d02281e030100410b0000e0303e180468401d441d49004190702a09a5010740d84032440b1807410111012100c0310100c80f40080f0102500d1903078020b510946407ea22110256030150465001070084181004100c0b411642542c44140c40c4c000f04e00300b401c00042404a9003e400d00501c50340024401e03103807001138285e240640014038080e200e4801c9680326810340d10417074400d1101c0d101c000001c052000500104036940c240d02003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 58975452 1250 58974202 58974221
    0x609030909020409021804020a0f0c0f0b07080f18031e120f0403080606090f0d1403040603020c010e01111204060b0607030309021305040309050d030212071a0a06050112 74
    0x28030030903007900c03050601c00326485075020003c1141c1c0016107409410b0410305013040d0520440703045040080100e0050000c401c4110742c001000400c9681e54100306500741550611500b02c0d6007880c4500e40b1441c041d2030f10074107881c22101c410f41c0f1000502007882c001c1c03841d95400c42d06c2c0d010707608003160034511103072414402022010619041c0300d40b04008401040851082041c1050401581010b00700504121006800a4000e407401c03c0103460b1a112a423031220000001c0d0344c0407681c61402c2c01c00c0101c52151440d062941e000016000a00ca030f41038010b49928540500204024245540f5460803140b00c0000c0204155091001a15182c03002984e15403044c0180008203030406000005506a405220101d0100b96210301940c00d604100042d805e030b20429560802080c2010b89024044085500c41d05100c1d0795141b0960041600c01e1003102c0070b0130010400c20392900428504518000c20a03d03500340900304150005041003d03d004150460b041a15868240c000e483c2c0782c4005401400e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 58976702 1250 58975452 58975457
    0x7021c0504170102040b0a0207052b030e01020c1207080c04021305060a090b030103050d031d0601170c04050c0703020d02030f03041506030f0b060301060501090501080c0304300305010b07030c060903 87
    0x4400200d00103481c008207c610841d901801c0b0081c1007408021000280b40080550081c021031012002c44070b40d0340e81a401901801c01000140380000100d14140c4400c110319001140641080010310307001642c402541d64a00c1030380c15202818050000328007464201e042000f034212010011741c00c2c03100c0142111019854205101a00d8032414985644203070f1040704c596100341800c00c0c800c0da162207005007503c0c05d00b1039405619142ca407003035545c00041c0241e4519000303208111418134010409507161000140003440245007104051142d83c004c09410340c058020382d1010303280c080c400300481c4d040003030100302281181c40f541c68864240d040d00081c0c102c038566410001c40460b0651211461040c8500d81c186940d1401c0b40c28142551295030051303060162914040c4406e0fa00007004542c01840100115200e9455080c0f15401c9544d44005100e003104690410f01d510242d08061380555129071011b0000e40d81e40c0c0701c440f0b030501c160740c03018000400812620740042c46c40c1d048081540e0091 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 58977952 1250 58976702 58976707
    0x1091a090a0506010608010f06050a0f081510020a02030115030302070608041b0806040c05150a050d020702150706050121020d0c050406060f02010b03010605060306060706090602030a020307021c0504170102 90
    0x541e00c2c40d141020a8009202044d510401000f40e00f00d4016080040c010610b0400d0514131200405019692100c2c120001d008042000a80300300408120140500001f01420800344c04840e011791503d50914050307019500345014480c0003001ca075a8030b011a82d15600402e0034903c1c10a08981070b0801a1085808102002e41c240103800c0d03400c5140003a11200e07011302454205480c01e0024900168403581c0203884100c0340d814009040d2040d80c0119005040c0542d50703d5080141000920039050700950083d0f8107079100c0705008040002d0044284100c4003040981d881da00102c10301c0030901d183c0d24826a040a0050060030100070400d0194400c000d502d400365140d00014041d2000d07900914000340384180b4101405a09006450101905800800102d800c000224116200080040c0d026250001c2d0303c5041240d2544240400c90304018219102d0508107802d002039402580d0010040c495040051409200907024000110454850300d01d050f241810349482d19581442d01d26055609 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 58979202 1250 58977952 58977973
    0xb060603070314071d030109030206220b101d0402060307030f0b03010e1c080c090409030909110d05071b0605071803060e070b0f0f03040c030f060902030f01091a09 72
    0x40f4898a001d0180d507111446039580d210398444010048400081c407030ba04050712600400e070003140494100d8480d82c0c00281c124940c010440040d421518002c01508081041140003144000c11000390740d501c03041c4140c003e0100d282c9001043c1d0507240a940600200301140c2c0641c0280c0c060b0f61002c1e0036400114025041800003030844840b00e5101c0101d410151000034520600e0100502100240c20501c0f41400d040080c451b10380100382016000320b80c0c442106050500401100700142010b190900c0032081d20403082402d50000c01c00c041c645410807002c1005507000314a040f002c0c0801a07120f89800040751034a00141c000074002c2024403001200c14101080c11001050107940070f0480440c2040790850640d1800b1203560082c000e140c1c051215034590010f003070440380303815020312940d510780e115410007072103184955200500b0042031440d9981008855084450001c6c02201075540341c101c0b00c3d00c42400e91b5000340c2d0050908651b00010070441115120081d000b40b09007080311404d520 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 58980452 1250 58979202 58979231
    0xe040b04110a030603060b120c2701080f070e061305060402041d0907050108090303041203060b0a020c0102060135010e0a0b0a06051804080307030b030706050d060e01030b0606030703 80
    0x9109a500003903c4d240c1c1401405258040e64883c4201500d214801d07142e8550031a03290040589800d10032540d20200ba680034982c440e044140b0f0018004104155035540111079554200942484082c09070403000180c03499204425481032802038001251421903488040051800030400c0d58426428040424080282103c50401d00c00c050460813241c1002100d2615100640c1e016030b0410186c5000c000c4110004004d03aa0480d40c03090040305d0b0016090025009040140c1000c40c4144000c50010144c69000462040c405400e03000d40781c4690722480c18813608980852050480da1002161202c0410860000321200490a0000401e02c401126035400c10341413640079180a4000e005002c2101074034410f000040000b00d64440d903a14444003114516480204090214103002c00044e010901a810034180606c0c002d060f2804141c1f00e078005000380d00140c0c950900c40d4a086800305209a90300c0b88241038981118181890795117070002c00c0000e40c0020107500130503407076070090074041c3d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 58981702 1250 58980452 58980457
    0x1207030203250c0201030605060702010e10050903010c0806040c0e15070c0e040602030f0705120a0905010e0d080907050f0d0b10170d08070f0906080c07150e010c020d0e040b0411 78
    0x2982d5600f81e4103100e10300004003a50f503a50015803050070200458030050b80c01826803001c3c070100b981c4464914190030002d8900380200b884850b09542460003640380a81d0041115110300320444040003100410b0808840845642d11001d0b00811000d485034503010425026004036441000c40300c20f03480d129074088035020710a071001c4409580203c10311011012210340d044e441112443c00030b0410300702015441e550103020b001c0e03c000c3e5598480d4807080c00403e402c0030502440b02e07011034140c25070344000280414403c41d140c2c50a80148400407030a4580350081c500040300c0240105031404450311036041480e8050400707640700f807155000007200c0c0c00901860341425403e0f000743c00c41c0340e0b200c03c018290340d2004081380c0c10807030682160205180c010540c2c0040d05e10514002c1410381e54020000d406114100e000740200e400f202005841e190281c0020401012500003403000241c0f00a0503a035a030200d101035404034031651140d4070181490b40c484c0009403002080850300301510902024244d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 58982952 1250 58981702 58981771
    0x1170c0c030f0304020109050d03050412110402030f0609130312020a030b0d0501020703030609090209041104020c0f0f01110c1b03010204090e0c010824090405150711060105010201021207030203 85
    0x18040f08000966800c904d254008000680b001e0071702c640070340d8000b00706108501500c0202020800b00d241400802c031400c8007400d4000c0c2003150380c0d0a00c071542a091490031a8014400e41000c40014031214040c0a0302d501c155158440501c0130040c640900042e41081d401d1a040507905e060401d00f0744e485014090700e40f40100c00040c1c0d41ca01310300707005003912450b0700030748200c0d410101c100340140ca0794080300d54819003105921500b0480f420000e0081d10801c1d4011502c0e210700c881050304050f02180801104030301000802c40c4a0307048103600340b24080c1050064043e00003040e40d1060700f0310000c0400301d110f00100014074107602c5210100c22101105650003840d4030101e4135000a58200685582000d8602c0c140744070500c3c03040e4440c00741007501d10000c1c0907841010204003040741c1084160101c841070101c188552402580003403000380c9019282102d807281200003d1b9650042c03085038407a016408020086550780f440c160f000c0e500140c00820784216642c140040c851500042c075180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 58984202 1250 58982952 58982977
    0xa03030b030c041119021501090209030a020a0902040f171f060b03040303090b10080c0f040603060608030304021809071703070c06030c0f02011401061808060a0c0f0c0201170c0c03 79
    0xa070481207400c41c10b540d4141c1d42c03220a5610030001f50304030820078000541196101c3d04090f0382d940364030012a0400180e580025000009000b020440e01c5107038000e0000d82d52225029804581c0c2c130340b0507401d04002003920644980200d0b00c0c0c00c45a100c1903070400c8440d490305001007001c65569034501c10903030003124183c002a80d41d90f450380408c41c0b1130550503002152071983c0c5d2015401c100703035240c852080e6000c1520800c280c1007403040d1074a594000b40000e54010b401048482c3d5146003d0b80caa50003101c080b4840c0c055120000c00c001e44514000340901c19101c024001d540c2464089c01e0450300000000303046100c2400000700040080d41f95001a00d0f041d98041040058100d0191031914042c401e5015079060441d00341c0f0409100015a0450708a8a40f60f440700c0d003509005d00410025400030310340da0086000304015074225401041c3d16800039940c008403585071a8003120f01e0014100000e0000352000118030a940c43c000e00e43d03402803070401445150036040c3d00c0051850740120f0034800d9 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 58985452 1250 58984202 58984207
    0x2604060f05090f100f110c1509031204080f04030501050a060f1a120c09060c16061b0201080903090d06060e090a0c0e07050415020606090c0c0a03030b030c0411 70
    0x21095414011640c2000c1004000c00c0c4040c0c9044440e0345510400e040b0000c0346980300740b50004c004254000e40d0400420554075961800100e00c207030340b01c0c1e210310311846072301030b0850215000400000c119400050800b000c10110703144c40da5148007645c8050090600c1500520020000c100c4c28810140110b91452000400d40e16200c1d15120032403007940f200c202c1087c000341c501d40c05c000103011280015203503e8003c0c80f039500c1101e440310301d0042840c003542050700420703140c44240b8000b81d101c3c229420a0560039030f042ea204000c441e01c1615410a00500f803020301c4400055024480b002c3d000b50a403c192418011290007080d4810071200e025903001c0d440b8041000a1000d00d2401c40c0c11051000280c0341140f89520384404070300b03451003500318602003140050442442901503074003500d6001140e08203055a003e00a64030740c400c1c2c0e412403050040f10302003032030009414102c0b2222004040a8450b22030107807419001022081c0066815008058031140350f0b40d158411781c0c1120804280b0f498 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 58986702 1250 58985452 58985471
    0x101a1c1a131109070203250506040f06060909081b07091505150a020c090903090a14040e15060f0a0810060e0a0501140f13050709090c030204050d03260406 68
    0x28841d412080b454050303520a001c3c030920584c040101ca526058480440030300b82c01d2004482c0e0004040200a80b0600412051100304090079516900042c000d0302c00340001500c0e011100115104840010002c160802101504071040c0044503040c011150907180466659440311303065511249824001d803403105070500c0280342c0180907070742114111100c0b41c107010035544080e40d1351194100c00343c4034206c542d0000c2e5034400108111843c40b6005000d030b00600783e031407100c130409012028000c2e00c03460808060001264002640c0c3c1081c5544c0d9441040300d0b100c4009019610325900106600000c40750b03000308500b0010061100c18020350240050020300c0d10304208240d10707018210f07085207801d060041140b140d00300c404440348441120f4508140000100254019405c04484140c10b41050100304d501034000070068122039400606200c42c190b040d204500724400c074000d10794081ca40000700404a849442d062440e030065040d03000750b2490a480c2045960400c440844070030792185182c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 58987952 1250 58986702 58986713
    0xd11040503071d0a0506130e060a05060607051e03071704030303050705040308092209031707030905060f0601140313020406170d030c02030d090302101a1c1a13 70
    0x5900401da012490461882c85045050558001410920316580c0b110080b454680e9440c40b0f0076a0b50b16418020081048e004040a40302c10045a044580c076161100007006818007030103c1e400e8940c40406000380700c80c49590501c01ca00414242d0320644401d100c0e803c0090504102c4464000d880036210382c40b00d00d14900201542c80041030801049010b100400009090000356840b561046825080582c0740c00341d204e50300c0f40640d25400382c0c07a0030014040141070b0040140700710b9083d2005072030381990381c0800942c00d0341d00741240100a948000c001441d5102a03004898102c2070500d00322a40409501004110b41c10545403000040c5003030b9801000c5140511494004007000780c03071001e13450840341c1d03120303104e902c81000070f0b050545a170000d100c070903c2881252940e403110541006800010b003070080d5525080d400b80c104551400424000d506041c1c440c08598a00003414200f0f6440550b5010345900700308a03044800480e10144514042c0c81001c8051103158a500d5000b600c14141c20007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 58989202 1250 58987952 58987963
    0x807021e030c07090908041401030209041a1206071d03031207120606021207020906010e04111803030403020f060c070f090504030e0118140f0a030b091b060702010c06020d11040503 79
    0xb001360614149481c00002c991006440860f14080d01d01e91003031001c40c006030040d2064464807903006251000038039160402c07054900100a0580d4581d050401c80c41840355141c0003602d13110041100e503018a10b4081042d00c407408041c0002c0d056a041000c200a25a15a034040e109a0003260f2000d0220440031a28402d18000709201e100615002c210340703500d000c480c451494068000c400b1180010329036406a801c901d640800a003040004540e80d000f1114580c1008007280044038500c1118a20780c9000010395060340d0b0000e142820f07001840041081991080c280c00400b805a4840010401c0c040c41c055001050781d41030106d05450300b0b02d0000d00b614125080181840005010114060403503668502603881d842100340b5145401400241c40550380082d0a61103000303101c020040194201b070300f074040e1140c0c00450b1644103d160340401c0c04526415043d4002d4410b000300d801642c8158004611140240c00062800d1480e52942e81901e180d0110800e000380001410006d50a08104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 58990452 1250 58989202 58989209
    0x3030c02060c040b03010b0313050703060e0c060403080f070f1202011d0a1208070306050a03050c0a1a03040605060a050415050907090e040f03020f100603110406060f0807021e030c07 80
    0x20b03a49041c3c10118035800070b000601609a42c0000840054140595180e583c110030340c001e81201c641c0c60707980c680030010706072031600c4281c07038002c0b202000c4003030900382c00382c0e41600c2e8483c04060400807114002020380e00004015102d52140741c1d403400100d10160000c4454898650010071404d01c280700c41e540400c1c0190701c48205a01001c1c50f807010070b03081d44241600c07201601d07040c0c0707003500d811000314080d00180e00b000e0f501281c0040000200000001c440507945420fa0b032855085a0300e081c140030700064401002c1c140801040007800043c0c8035440641c1c801c7e001002c8801064840020804984603101c001640410301303c01840546421005c03e980304031076240212020f030500b0b07030010400341c1c00703400142003414980940c001c00d4000d000030042c900c11402114800425040c108010300414030050361686c500b25070122441c1004d016140070366842d501c0d6086031201e10b030000c44000d50020b08202c01c502441d01c08182c1c80c844041010715059810000310340710ba02c0e1050840c10600185d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 58991702 1250 58990452 58990471
    0x303041e0b04020f150a170604060303020709020f0d0608010e0c040209030d080901061a0403060b030313030308061f0f1101140402010c030207121a070305060f06070c0e0403030c0206 80
    0xd08040003403884012a6403060381a2080e0080c43c06980110350414541960003111050100311043d10b194040f5482d0b501d00071808045030142ca644042c0b004075080c03404040c005030440d0f4000d1210041c10f400801c0303d03d1078100d803186450160041202100c1071500b0010090f51152000800e10401704010385500d07104483c00c502e010905400031781c3da900100a0401400322060000d46900800c0d400306c002000c3d07010152407041d01000c0440c1540d0700900089840611f040d09582d0359041c0042a1140d4883c0d003000550b19038190744003a0f80d5904001c0c00154823104242c20140e2540001d074607a0080e00711504c0e0030850181d50344000d000c800024281800036071500c0100c0f113203a1500c128141c1c1280e020300b840200315409050032814401c254010340090304841d08614100804404503c0340e03812000c0e4101007a89031030100320b050b180e09440d81da622425044080f00949048002029418410010012090356410b01103801c54011075056002c00e03030b201c194804803901071180541c00443c40 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 58992809 1107 58991702 58991753
    0x7140a02130510050d020f0d030e040b030f0a03030e0304080607020d03240504020d02130f090605030a0f0312060506070f05010b030f07050603040302011d030304 71
    0x801080340614444046031031806101d201d0301c0d0103003400c03030303044800c1038a44000c00006070316012090368002240018441c0c07603682c40e03d685d180c280c840d4442e18000802801004211410490700d0390194210f00380352111040003050305846940c1c1820700203400090034220520310f0080e9001420b15205090900044540015000650f100d079980c0c10f014100c5001c000303180140f5002100b0b451034144060034040c920f4a40c0203000d08003c06800107091209a00f817400900990390310460400d05101d4052142084c0e074000c1001030402940140403060155407801c42945041801a0410207000100c1c022214103800c40c200500004140c0d540365160383c00c25440510090104481c01d40c68921000460b0402103001448045102c0242561526200c2400200c0d40003c00850465594002e007100307543c40c5030810400445040015900c91405207030904072070445010508181550 = true := by decide +kernel

theorem cover : BRFrame.Cov 58812952 58992809 := by
  have h0 := BRFrame.cov_init 58812952
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 58812952 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 58812952 ≤ n) (h2 : n < 58992809) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
