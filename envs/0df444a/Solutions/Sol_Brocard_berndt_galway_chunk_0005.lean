-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0005
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:18:50.717313+00:00
-- url     : https://prove2.me/submissions/fb95277c-ef87-4930-ac6a-29c30efc1da0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 719432 ≤ n < 899288 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 720682 1250 719432 719441
    0x1060303020a1403070308041101030212010b0a0f0305150d0302030c030301140405010503010c0206060405070207030b09030d05010f030f020609040b0402030f04051b030604060506030a02090403020705030105060a0311010c0201050c0f0a1203 105
    0x3e1b01140c4d0041c00140050800c0407502460141414010701344a05d04443c030440e08000d802030f110020000507000c4150750065042d005620132450140b000d49010146022020300346004503005072031440740441054000d005840300b5404d40000c5a80ba0341e9104607112420b01c6024889006910300310010486040601640f28206840d4005100d59103401c41404000c240003400502180031382c0c18007100043c2d41d00b02460080d00d14100a584030986645c0303990443c0d4060b4070101c0d1624000070104001a11000403601c3c040c0c04480c1030785ca404500001c9009000301d2001d003a4014030000400c0030001c1d4185649000314024801c403107034100150300c20180c07001400345d003a5040e40320000050010707030180c020981c00b41c0d01030240c4514003803503800f1480e10b641c152021400b40e0031401051009040911446900c00d20480e50320a03034501d5621814024006500a02d0410031101c0c1c5003400d590141c0100d03092000154220f0b001c500c0c6c000003103911005451801c4070741504a45c0c0140030f4500ca03014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 721932 1250 720682 720697
    0x7030609050f0609040c0503190516030c0303050c010f050103080a030507090f090f061505030108060702060106080408030907030203030409020403020901050603010b040b0304030c0503030406050702060906010605040605091201060303020a1403 106
    0x11038070b071152900001c0101140004004952030310709180d0104846d2000d10901e090040035400c0080060404e191280c10540031a1240780e4801c0711110400c082204e8103099000c498150400716600c41c00820043d0250410044540015041c040000b00f04124030000b445c00d0580d507a0100302c681c031000070032580c2c9056480b605544050640d802c1c498800c02d544641515004681c0c00104980d550603200c02d100301a56004010030001300040082000c18400603900c07007840d101a02040d81041400341c0030880141c4098151000400094954802000320502a640003001c4a0310345986881820207035000d404120b006020040001843d4209581541c1c142c500b2048140d081a0901c40e44001a8100070001d40c1041401c845140103c0d10600c02580a18010320f0045032900d00014081d10b08000a4200580e0f035100000400945a00109035004d4402902c0d100341e4800740c0c0320000d2640104500b070240e45500e40300340081099000036009207586d226068100b20000e10206090301c9004008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 723182 1250 721932 721951
    0x3060806060103020c0304030203010609020702030601170303040f06090209100807060503041106070516030c030b0609090c0108060a0506040e07030b060403050604060203060402070807030c1403040302010c020d080403080a02060703060905 104
    0x3012582540c0243c004d050f41140394402c81c0d080a03643d40010782513505650240480d83d50000d6071000350700b400d10100c0e0250041054050420200302c980c1c0d03589200003031024014800e031502042c200041a00b24811090b0018030700c008600f04000c0624510006105000080c440d1810000300f2034001d8007a68821900081e503200050360380c070b0070700102e5840b02000310380300c0c02208005030000000c1044400a0350051545144050542c58211350030036014000d240304003071000030040b400300f00055881d0208001c0c039201d40280c803414040740c101c1f44180c11035948403402040c0400c030303000103d00c2144100581d5400380584140356090060714800e03800040c2581d08080c00280109166400443e00001e0203800140b82c0310450312107012a801c0800b049000075048402c01d420f1041c2640110b05080c454400b0790b00e002e2440c0d0020b0820b00585d40f0090042500c02801c3c4240008032060b03500468111403115605c1d9030700c02000303443d03000840354800800d182c8400400c0c184207501c20503109a5404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724432 1250 723182 723193
    0x605030303040f051f0902030607050414040c110f0102030603071d0703020a020304050d03020303041101030605030a0201030f0b06031e1303050306010c0203010b12010603030806090402010806090408090d0308010302010f030608 99
    0x1501c8508081c1540f200c03c1e40c90303105901c3c0c507400c425010740c2600003060382c41c40d0000700310040344101414980c010b03048608000051005020310381c0b402400f6042c149007114005840c50007100c09071800403052100e01501d0003122100d9003e850190001c61084100314291021207440d40002200e400c030f600e0403414020108400101c80c580240c9c014495010140110b9050a0355080025081000340342c5c100d0060700b0100610081000707055450003052001d0030188501c2d800c18000c65074801071308030040e0400d41c944550003245485a4032500d600c040107400d0b150341c0e181030510140300360110449051101420300000300c46105440068800c20381c555130780741c50364441c0c1d001107a1101000505070380c103540e41d20209a1075603d00d05c0110213800088008282136241d0700740a010444001c10290042d5007010400c8010703079115510b0b0754032403822101c079046070301c0781c1c10100810b0154842c034a8004690009143c103141d0002c0165048903c03d03611400502106002201900c00c244211006c642c800e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 725682 1250 724432 724441
    0x14060304120804050712030504150306060e0f0105070c0306050601080702010207050a2004060e0105010e0301060b0307081008010c03060512010b0d03050c030c0102040902070203012304020402030604020705030703080601020706030605030303 105
    0xd10b02054006025004403446a038417108505842201004120042a03001a0400009500054440c5502e0007824100401450408042c2ca05011480002d00c141603001c5005002d0307008400751080c45030007404815410f030300ea25010001b02401e1355034502040a0b103000424080c4140201c4070900d6000028243c0c04080d50340f1840c0c10805c5c2007840c0e0130340700000038680151310307548104402800c1c0c0088100c17403945400000740548942801c0e080c006c3c0d05240c0d0a01c142d403400c40c1125080aa1840c080d038441d82e4100c2166022070083e0840e07200340d428101001e00f0a90b06420601c01c1d194112a403018441304207480f2403c03542400d0405401c0645004c545003c64001c0c40503000c10003040003528030700800820981e00720781c05a0008000380e0b038042441c0055080c00d10401d818000082c8200c201000096160401441c0c0104028031954000001900075151078055910899000044944130301c020300d005171510070211040c50052048560019140384a80640700c1202c0003e4051441c540301d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726932 1250 725682 725687
    0x30601030f0609030306031406010e010605040e16030204050a0603060302040501050f0d03030c050903030d06030b060103020f030c030601210f050603030405010e010302030a0e0a0503040305010e07050a06030c0201110a03061406030412 102
    0x3d50841c240c0c181035441c40c00101180000c900d82003040210f201074062076052402c3c5102c10801a0050720411000b800248000c00b001840190040c680017000f030228002204214064401c50308200d40015040600148843e09a08564244ca04c201da06211507a03e9205004c0c5026480f8155070740300190841500209000364440341c03500320980382c401c0c90005064040780ca0355102100c48010980d448004100380b02c186080300f07800c5442443c055284c0314142620141600015096801d40a40080072a0340740e80103030000040080b216a01c3da6180f074141c1d0f1040000c1c0340d522180d03c3c5490804000404030703d004001c840c03d0f80c1c0141c49030f1001c0c0b481480110000e420041101a059a4822031000301d510200062150244101c2c0255510780c25031805500791029244190f03680d90014030b06012a50300e903031819040d14007c1c0741c00204104041c1049000d03001d0549030309085000010408425545500400d05403000045081402c00900b4207000d0700d8172080303e019041d600d6040c82c8501003032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728182 1250 726932 726941
    0x31a0108091501080d090b0a050703081005031506010f020a030504090207020607020603040609031106040c06080a140106020606040c09050f090408070804080102030601030f0506030705011101150801060e0105030601030f06 97
    0x5405070202d61100c101c5028149a041d400e8102945961041c80c501329141d80c0a00d10601502100f00704504149441a024115000b052001418800b9001c001111441700695213002031800404071050404480e0700c42c401e500c01a00c0f41030000342d0200f28030212600000752180c0007589641c40310b14062600072460300035000780d03808a038403203003c000e01c502580d201006907005034082d05d40000c02c1c1d480307450003034510603016200b0101500104c0030000440e03d240051421180310b803c01001c9541d03802e880000803d16258260600040d41002099666000900380d20456040d6010031894080400c155501d0145120382507000d0f41110b40c0e0310351420202d840c140c10074031501d6902d0030f00c105542d4552098101d40c00011543e0350100400590f50703450f01860150720040c400802003401c101000c0385e01d45140d40921070501113590690103c0704002d6002d40184211299251810790301d55041d54040c00d031703c0c46030109258400002141030310380410224100d9500c00048502c040059070340d0070162 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 729432 1250 728182 728191
    0x3020a0803130507080102040e010e040b01061407020402070f022107090207020d0b010803030601030506040504020108040201030902130c0206010305060106030b060406180306020307050310060311070311010612080705060601031a0108 102
    0x8107922180b10005142000450064480000007503200c5040540c0f030060b04105a1110300c4071110b00050002017503102c0a1b82c0d0640d410b9241005446140145003500c900c111040207410910000c3d100c400d0242070200a06610310850765580541902c04428107901c400d5084201c10750018032041001d100190f00a00d0024401340081c002d000740d0f43c4404905800992094901e5080041000069070745441102e82c822402ca40403c0541000d8000900000340104028103041e03480700c540080d9501d550809221009940c410310200c14030440007034841b042844111500c0c41080d002160041c000d000d00d20b0300f20b40180410b400d00f8607103c011689850f104030001015068810080041003460004511030855525010b41e0303820f1048403405e028106500510405140001c03504101030b42c242210301e03480e01803401d58181c0c5010840140102150307800070071081044800201086a400042d00340c0502440607502075039a2040150195030200b041d00c00301750351001051f24290700a50500303820 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 730682 1250 729432 729451
    0xa02030a1805030d020708060108010204030819090504020d0b01110c090c07030c080a09060f090e0a0b0a0806090606010f0201050603030f030a0f0f020409060609030c0504050603030c0303070503010501030c080403020a0803 97
    0x201d80c0e4a8020a0030016007100340c400617013090303a062080c604200110b5004081c9140210b04d0315103903440300d81c0180a110040c40400300006582c2031014490f65210020b0000148215070340c840b540c4508004144030200d040c0895082e006070110380e44080303000b43c41d2a00180002e070b5599109034000000b40d001103000c03828401c0d00902c3d100411840c2018058083e02d58031403000850034070401411a041c02011041000007100060000c1400303d0304441e00002c032650003280b03c10600000542c003070002d402000440c410f110400c1542c0c2c40001380180100350a0721420010340314080e01300e003607a004644254150740100302c3c202d04907080c080103551100744860006648042c42c407000c41613885240b1030184045e00850140b103c007030140304000c0109032034180300e020785107107a80e11000b03001eaa1003024401c40d6117000045090f01d0500c116561225014180c90341e07440c0c40800646560070a00034140000c0c83e0280711207909000d8000a40030319055001010400596592520141d00044c8060b10 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 731932 1250 730682 730727
    0x30c090c0c05010501080606090604020307020c06030a02040503010e010f060806040302030a0e040b03010912110c0a03020d030e060a03020301030507050405010305100c021c0203030411030a020d0f020406050607050307020406050301020a02030a 106
    0x894003e04c20640070f4040100648980c0c1004002c2102c50301d0b016100c0d9102d81d1041040c007089640000e414500c9100540c0d10588964403144008028010b5a11040d015402c0500074aa005410350000c940d10300d40c028100080fa888003109542d60108507002009640104504511076000340c0b081e05071b0f218024804a2441d1850002c00d007914504d0508a503100749850440254541000740410760703186400003031043c0c03690800094910146840040e0150905c641113006141c07240319040749210001e448180c1d070340c2d1014401002540300b44400c2d54a4001c9103404589450980540380c101d0390040011304229018200200050246000c160b0030352003000c00e0021030340c45007400b8060998aa40146807a450030717040804480250b040018841d4011030308171401a40d5504941c600c083d0080000f100499417440803800600040d00840c1e070100012907807504100c0004000c1a883e80309440174448199144281400e038018030f80c001000d40c005105508545105500c201110904800c0c40324 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 733182 1250 731932 731957
    0x603030210021806040605030403020606010f1d03030d0204080a060b06070b04020105090f04060909020307080a0b07081e0406060602010c030605211504060603030206070903020603010603020306060c10020901021006030c090c 98
    0x501c194170030341c011804100044104014140c060241030341c00502800d100415600c400300090a502044020020074483d01403450703d50b8604005441c00c0c40c4d100f035001c540d219104d404880d616408100f0844000d0308040c841c00c0130742002e80980380304c26400402d00b6102d0300d440c0e0040d0365135001188401d030440404094188260b58602400c8000c28131010001450000c3c1d00500d0f09021036504001456070014a01c0070015039510002940b01c091440c04e8492901c8009031446140710f00090b003003030103004105000034070600e40d0000e000c503001d40e0000c006403902d0201c10783c261a898403075203a04c460024109100d01c0071040e0104402c4034441c1c155010f818440c2c1c9104a03291040e102a24920340d40c0c0c1051080540401505420102c1d504200c00036031710b0765000074040c0c4414012001055004404207240d03072034240c166800459a20191004080d12000e940300940103034051600511800d00b050051501c1d5104003825030b5081501c8140f100d05141c0800301500b654100e51080000d44d6100340c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734432 1250 733182 733189
    0x102010e0601030605060411090d060903020f06070203040603060806090d0f050d020706050405070501080112020402090103060305030712020105160512060a0e0f011401030b06090d030905030102070b06030105070306030302100218 100
    0x30b070185114002c0000c06080c40018441210064035054460b080b0030880b0810f55601c201c0100703982c940c008404140b1510030302c5c04a0405812000c900e0991258106100da81c40e0017202030003e40d0000c2e60100069543c0340f040036500c503800d4031003c1140d00281ca01001061051250820f03881031414100d1801c6080341d81401240e000c41002c5d1044c0d9552420f010421205200c11b134001c04c800d20f03006403554149000181c4c061540c000091065600003058201a4003e4114000840c0c2100503240c58030f4150801c00b080d0340610039024015460701c400a804400f04603200c40b0701100ca682c41d02c3c206a09001c1d0345444903c0644000e0307001c404117400107070214001c20101d10500041d41d64600341d502d480703c8090743c214550a0070b8181400c1c8600d81a06445244c01d90b041c1c098100c0e04003d4104c00b078103058400580d5a040280c1550001550070148003208100c28090f4400790020480d5130780320384040b822520140001030041e0448d60b142288800c45801070005400000322030400b07051010b000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 735682 1250 734432 734443
    0x301060b04080703021017070c0213060303030504020405010e010803040902030a020c060408040e0108030304020607020d02010c05010203090c090f06010206040b070504050a06090303021006080304060507030c0203030a1e0504030314090102010e 106
    0x950302e0742d10030801070045042c0421900d10480321410003a28482c9160320f0f00011081c004d07c180708000c52a6900c40c150b6440400c1440e500e94902d0040140e2520307400c0c000c000e8071003120103a0280303080000024624000045103412240f80c00080c40c1420300700340b003010295102510300428141c0a202d43c1c0c4032003000b072002d540141d10404145944500c0d000841b040644140c1c4107a02c90b8009008100142e03e51508480e4540e50484902c00e80650610050340d5214100c14043c000c1c2d0320102c10807100301400a0508001303081159000456903880381042a040030032a400360041e001000820300180e80d620303125400900c1030038010304140c4c850000c00c030b6a40e22507210500281400c03400f00189a0180100901000701c0c640a00000e814020142da8078855845440100140003c0d02414948601c22258010340e00030180c0380e940303070b03455402020306a10341c5240c2118107401140040d2140568100c2e01140d925031900c00741c00d41c070161502d844d500300f101000d0655413218249010035400b0f014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 736932 1250 735682 735689
    0x70605070503090709020a020a030c03170a020904060b09100f2114010b0304020a030206030601020102270102070501021c030b060d050702010e010506010507030507020d02060909090303090c04060e0f060301060b04 93
    0x480c10b803245001ca07400351400ca1994800d0481c82c1c41000840f04095011400201d8160581001c0e1341d54203003454104d61420010b03011070004401e40c0180040900141c008140c0080700300c40c00e00040d038541c03a540c0c0c020703c11041b40e0740e8824250b40401d401103002d405400f0640c03256040900001f2010b084904110369502509541c2d203550300c0d0b18484143c1d04140c01ca02411500807017034194649540400d00500040c00080e01c40c0c0342c04000901d25a00c03d404036030949011721100310507042070500c0c5c00102201205490b004d4050b81401062651000039203000544400c07c0c42c000b0a031741400240d00818820007000c0d0001810440208442c070680101806422a5400000c4000b1035580c998212a005043d81e4100602080b01e1b002185d401b40503030300342603011900c80340c54004910002e90b15100740c4002c0c0f5000300ea00010458a054040040e610911000041e030300e072402440100070441b8040d00a07513110800b00004a0824500c60800700e07030066000e0f000285003501c400cd00072841d0050350 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 738182 1250 736932 736937
    0x303070c05060f06010c06090507090609061401030c05070602070c0504020c0307030905010f020a030806060c010903020d02010b0103020702180405011d010606090801020301080616020a020a06080105040b030c030303010b0c0307060507 102
    0x340c042089010000642d00105015824203103081c0340300002d22008007034038084d017103640b1040e0001c140302045c00404002c004001c1c003000b00d65610455900070304481e1040b800e01e81401d0a54072000e500070f024044540040c1d584071031400140740e42d150001e40081c2020b54455003c200e000c12031351200c1c4010801c041a003001540c40752001c0c0b40007002480560400c0b410031404085c46e291a031f030005050320740c0c5a418280790300e0780d070343e020301096850080880c505800e600b86640c01080c0754012810380a45a09a4024403008078000015016071048100003500912000005129000907500584d0458442c0c8000b00c0e00584094080100c0380d01b500d101881655500e50400201d9002100c0c02c0041c08400000c0d03065615110300151a080300034440001d0118104045109034420700054858980c000e19201d84691603550007000d0a50074000c07940107525009001c0807a2800240c00722101d0b41c010011480d41e82040404281c0d500450020f0781c69100900c83c5000180c61030003214442d400c00d6 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739432 1250 738182 738197
    0x70c030c031101020106030203060703020a020109050a060c080106020604051002030402060904050a02030907060804080702010e060706020406080703050c070b04030f110a1103011104080705060906070b0901050402030c040b01020613080c030307 106
    0x40c20b01d22240741c0400806030640e07142020410058801003005135100109090068a0b072007850b0090313015248a610061090140741c0300136040086c654000001c43c5c1107696025416a00c1c1d030340903603441800b0b8401134031903404000d0361410362401d60001d592280c030180a103801c0101c00d0001c141541c0c015034004841a17008010008030303020821a10006000d103142c00e040300d0a040e12280a0f030312409001904001c1400c01ea42d600b134403000122200107500c00c02c01c40d6982d41d0703500001c0803060140d5403400000e0030100424003944014096820311a00040044210740f1039035025070b040f4011007140300c14899003402081d810801800b4024115026071a801040d15000c0201802c603418491050007842d42800103001d10b000004089041d91740a40e01641d5a594840024180d030160440c000e1014150b18204820310006401180c002c81c429000c070303600010b42000300000d441441206a006a2041000400d481c40c0e11a000e6049070080c0a25803800262000302410b551080701c0d1940494080c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 740682 1250 739432 739439
    0x109030305060301180204050a06080303040f0302061003120806040b0301090804150512010905040501090c060e03060901051501050304060b1801030309080706050306040e0c03160602010509010b0d020d050102070c030c 95
    0x35001d050742c441c2c0124000c001d010030b9506a0003c00300700c03000c003900580e9140002040c202c40c940c01200500301c400100c0c1d0720b0b4030301460820103c0203810803c8006000b07103404998401a410620740990703034014a600d50f2045111002c892400c001081349034810784840751800700b510281304262265010302121a81c80d81007a07420405a0a0100c20b4410484200000356150f420045d006040d601d1030100402c50b034507281049030150a0313820001d00b040c0200c110000b40d554221145409030309064041e500e680c0d440c1c001040c00c8402c12201285018140c00380c428680d8886c000a42e40944110030009100348610003180380e95010140482615180c50018014182c021521100900d00f04008207002414640010007a0101070b00281c001c5450fa8100da035144410f00407050350b040090200c40181100c480b81c0780c03289130b00344a503130050b5181030701180328085c040c01006003501c0c01411060080d60540e0074000a00e5940c042960f40b55801d110020006031090016802140500b2040c4060b506 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 741932 1250 740682 740687
    0x909030d06080f03040501050703090308031e060904020105030a15030c03080310080106030201050d0902040e0d0201021b0f0a020111030c0d03020301090b0103050405060a0203060a0906080a03020115181a060a02010903 95
    0x80355045440c4903406620f518a105500000301c40a41c0e41c00c0c81c0c0360b62903200600c0d0079201804680c10081c8481e10210800a220403044502c1c540d001441d00c000c070845d00d03007500f48809202c0565010f400a00108005280c02d000c1e5001081120b04d0240c018101507504d494072803646601e40c01c01c0307814030300000a02c019056501c00e020044c0244500800c19145503900203081442218000d1207a0307a241c050302000d5680d194411010441e1070020740384841c5100b04001e00072f600800010780d5065001c4c03942c000300e69000800030562140c0500504603030070f141c1c005450940084000c5c951a1108100f030b61000d4a060081d00714042154401580702c0d410902c1c00800d0313070a41800c10741010314100410011560028207650014081d000050381c3e6100c200204400c02d03110380090141d607052080026141600054500344a4040c0d802002100e450b00c80c6024128414840c1020643d0040303051070070304071950b01902c084034581004030444151100420704a800045500300540d6654403020145074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 743182 1250 741932 741941
    0x6030c01020303010803030103060b0a05060a0e0301050709030f020603250806030c01110303060108040503130608060a050402030603030415090f0806060909030a0903030c05010605030105010314010c05031302060a030b0909030d 99
    0x5007400954115030401180945e030303003c1480041c0403c1c4d2208840a0706031600c0c00c2140240001810181d079483d075400c3d000c1d21140c0719824076400380d0b20344800103070306e980300d00c070701c2c100b41d0743c0c84000c0c42d0040b0001d400304481ca410160241c038507032410000200c0011521070400910500315111002d440c41d100741050b0622081e802c01905008012141c00302031070002c01142d0741b11409080c6030072140c5680c14200d01e14007514907012101c410801d4040780c1c03641c020300c9041c410300046840c000e5154030703003051200382d000a43e4126050b0f881840240a0b01400c940b4030300028101d440e1008400e035607612009101a01603114013220741041082c070407a0f052601c002c40d400811074004501e0070000707520040041e0194803002c0c003040b120360180300402400790000d00082078020002c0c0241e58481c1040704041b04050803d112139842e05d1180c800d01c80c020015a8420710444504040d094699000e2010b668085410703c0c040543c3e9118040e02580d0308581c840c0114200340080d47c5424440000760200d6 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744432 1250 743182 743203
    0x40e0405150a0b010503010603091406090f010609090206041505070f03030e0c0f0114070501020d050f01060207080606010f080a0902090106180906030b01151e0c0b0c070c03060c09030203060f0603 86
    0x5402c3c8001440340b640c00c403048a045904c0c82c0740c0004c071085142071107461012401d07118411401400e09010302003c001440c5a038540c40c1c0c0000700b081698420101080381c4613207e009403c03c00034002000f044503a04e02d43c81761190717a41440703454218039598410b441e10f20351100b20701003907407452204840170007001038150108003a03c450a407611000000b9041040d600c0107500a2400044d04100f00b001c29010796140241110041c46941402801080070b00b000b4007980c801403245c2d920000342d012000852602a18040c1c4070900921410b03101201c03800d20090041101c0c0e074645085c080103850741c04109000700b02c6607481100c1e00d640d5030344400003911503030b00c14000d2904198061012401801038036046610b216000b03911260030a0095800f5190b460782d040004110034103440d611034200074071107d030301c1c8a1603040074140e48191014000d03000f02007000e00988681ca90520016840d64081c800181160602049040da40d5000920b0800102d4400400020b50000d00109050030050301035407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 745682 1250 744432 744451
    0x3080105010c0c090506040e030c0601061403250306050607030f030e0c0102060f06010314040807120807020307060c0905040c0309110d020303030a0c030b060307030c08010504020f041406040e040515 87
    0x600c2c80988a620307400d1094020218100d035140040b50160b0359507406509908980000e5030340f2200340c02020780d200c0c103017403050001041044030409010b10741d003c1180e105400b482040c80310008469190040c1d29088256501455a10702000c07886035214009014164829503e882c40c024886800405071818060846c005a0111492620680e004110315902c4154450028240e55a110040700a006c0200f0408101001d400038802400315030001800302d2801903002004492210008a40d006400c0703c0280041c0c006000c0356001034220b4101510461051820b030143c01d072204009012121040f80740c0d40403951b00d01e40351040000c0c44c0c076400e840350011548c03402400360f0303500031070703120320008040d58811a5a003000e10380d03140c02980f22480b400b201038206a1030386014036020b0010004440000041000d5500018503840e05000311039a0500c0307608140d080038502628680200c00e070fa10402d03403000051102050f80910b480059100d103024100500304c162a00d90038a0b14405c0180c2038206 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 746932 1250 745682 745697
    0x60501030612020409020d020d03050307020c01020307170306031c11010e010b0102030702011808011404050c0a03080a0c0501020903030304030302070c060503010f0b03040503090306040b0603010e0f070b0a1e02010203040308010501 101
    0x1100030002e066840180d01520080780034011840040c010042040c0d0080d030201048c070310b40c42419400030180d440751f00310380c0803241580108001079907240203d010040c00c140f4941c07440e011b90a1420f01550b003003200a821282e007403240c41800c0c900d03840c050900703c0000d110520240b81c00c8400b401032500f0000030310001c000803942200000e40768030800c0c90190602006c1e010368100058920b8a81d13006181c680001c104404030300d040d000740d080c402d45054401c1c1c400c2d180c4808180c40c2c58411901100c1d440464246080340b051070954008402100c155029542480307051001d44041c80103510413403282c3d600603500d2240e45861011003256030850303010010140b0041c010703140b07140c800c40d064070418124151a69100e15020f8550711465000700e4150045000f88020052528440b5000780c001310000e100c45844652003555440101c40c01c00c45a07400503104001070031a040007000030401ca4074108064041002c0b403029102035141c0f0300300041c0c0d400801c01003415846032800d40504801d117400b40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 748182 1250 746932 746939
    0x1030204080712140111090901080606010c060b010e090103050601030201080f090a03030911030d0e040606020a030509040b01020f0303010b030703050708090a02100203090a080a021302090d03110a020618040605010306 95
    0x1652100caa004000000800d98a80e80c280807884d469643c8080080009001d02040c0406135a0305801c0a9091170080c423240e030020522440100e20140315910682d03c9000f14446070715900042e14500243c2d0341071040340c07a656205902c41b0301a00380614080c0c1c0c000c045c1940365100042460400600c05d14403200603006100c2007400124181040700e41510700458450a00d041038003c1140d0551a25458450070111a034440c1d0000c0d05120400c0703044508101c51513072060300742e031101441100140090300800c0080d240d4039203613100707001418046c070403100d0304c0b008002028075503030003a000006032541c080200506d440d40340c003610340c0c014603518140205007452541666904030030300c0300912401c44601402c603524805c1068500c42c040090076424015987d0802640340e0300134600c141e0180380352148500f500716075402114410f02d400b401c2400140170584088500c0f0700c080082c0c092600408500c02c0259646a015042c2c100b80c1d40c0020707244400c1c081c200800c803115980076505142c1450341c01c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 749432 1250 748182 748199
    0x30402030601030b0405100204080c010906050406090506070602070203030412050106090c080c0304050f061003030305060901030201050306060711030303040602090f01020a020303040b0d0905070603050405061b0409090201030f0905010b0f01030204 108
    0x2681101d03440301084e001901da500d08142408030400c512400584085000071b148540003644103007066080c0c03504441651100d60440303043c81075000303200100341040b104000300d080820080c181c16005180c0103040050380e031700090656100b03501c40f000a42040380240d06104080c07042100500c64214104a800c004a2020745a42c100600ca0880284c003c00001c051008c00d11802e80f00c41c1103401611814034045150112803d80c1d40002c0d00040e181170006070450505c1d62415060b030760141c44441c2184d0300c980820146600512007201c507101d502803030000342e0714100b001d58002c1340b240b003016864902036014090b400c106004c1c62411944100140740242c3c90101c00c840580b1000250582e840305201d48110150600c1c5400400c90b00c5406000200d06500d688600d014620507003c2d0b0b0000d80341d03000c5000c1e038001c1c1050000040c01003003000f044041d1890340280300551041c10085071445164406004070360100609403011307515001c841440386030036618903240380401d007002c50605080c503407007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 750682 1250 749432 749443
    0x90a0e0103030806060304060e070e091002040b07080a090306090f14010c1d0307030c030501020307020105010b0703090b090d0b0f010602070503010e06041101020c030607030609050c0903061b0f07240203040203 92
    0x118013645d0004045001c4c8401a00725806286010003100d514030382d0350707110342110401140c031990a4003502038040805601802220b049544040429003007841701d0300c2d140360303642c02401041b060101c1510004002010350203140d90184c0100092550300940303051854034001b1020244107664076000e0084142c40c1c11200d209100ca00d00103d900e0342072602c1c000710f4904041900007070044440b1050010070042e05400451065013154001d0001da641e1b2a440030382c82c01200c0d0700078003040c9524400c2c401540c803a4040c10480b440240b0340c1c13000a890b40c40e101c0d03914000f92800108040c1c20001840050380410814000b09000d6000b04000800420002d84030031010b0001060031110200c1344205078402c1083c0021072100030141c1d0007c2c20254001780c020700c0607118800805041c03000040210044500390766041c000600500802d076950400c004810840050400c1001000d200e07804201e0080c2001d40600340c0f0814040c3c04400c142503104404204100481c044503004004100c01038030040381 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751932 1250 750682 750691
    0x50706050906070b0402040b04020706090507060c020303040605030a0b04090302010207020f06090a03150905030c06100602030304080301060302030702070b0a0504030203010f02030103050a080d020f0307030903080907061b03020c060403030302090a0e01030308 113
    0xa00316135450303e01c0003401510258481561060000c60f045041c01410b521401501d440350742180c0d09550b48001c19900c0b04440031307000e549604184002c025050240000316840254134900007043c8400d000010308894100500340d0040c0c1d03010a9000843c20413620701144110304848040c01c1000240c0021014045400700515120340c001851414a1a541101c0d25060380310301a21b0700c0740b4030740c01e00c6992400d0440b049076100381c2c581d000052060012003120301450300000c40d07914580c00e20700c040d006548003525400c118130940d40000382d03c50003040940212507856490036078a40c40d60040600303442804001c0110306d0f204000401c006100015594040b6900041454540c2000320300758009000e5100b1042c11040300208008416506034003440c207040c425140c9060340c0e180c3c600140ea851070300d070192902080a03c2114403849141089085019200e80304840c401c507080c0000c11480d40041d0b00840c04650040745800c15441c02810700c20151400f1021041e01d9851034600400c80306c030150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 753182 1250 751932 751943
    0xe1003020d0902030312061804020603040816020904060507030e01050105030304090c14030108010f06060c0506061504030507030c050108090f0c04180203010203040506160201020403030e060a030207050f0a05070605090607 97
    0x101d58141c44416005242c0e001e4005050303170b4540383d840311907803403070310040301c004c1e101e502c40c10002207000482881e0305002c2ca03009040f00b0300356075480c0d8486185603c031400e0400b134200500554001640c811600c0c0b84140e200b00b10200f014204181d000d070940300018400205039041c00d0040c08280c0f4004151021150400d0700030800d845c860b0400d40c2c84001d00c014211071580e0020000c1004541500000c2240102281c00c00103d540c034142120800640c120040c115080240403500918125a10304c000c1c103112035800785402c0d603955036149008103540c4111030f4a26081c100b0407003582c1001c5403d520144080c081c007055164160701c540c0354000c44500c0c52280341d4812507991040744042c0400350083d400b8000715628100750900d103a030398404072507540240304010640f260051060003a9000c41398140c468041400d4070f030081050781d40201c9417140403d035090114102160041200250601c074403000350202c0d07407103402c0081c24980b142c1c020380b003030000030000c094403900c4240c200e40c2c440c0d405c0b9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 754432 1250 753182 753187
    0x90c030a060c030209090103030c03021002040302060904090303020c010c020a050105010503060403050703050c0a020a0603020324060409050402030a0b0403080106080105010906080601030b0102070b0a0e0111010b010503060d05030706060b190e100302 109
    0x80340b05500034000c204907550094a01400802095009a40e44014a001e50225920b003040c0d403d41506070301c940d0200a4000c00d00b1300c0302004500f4a904100d00261090502604114001d2000c0342120440820040180d20220408040c03010a11910303000d0582034028048500e05600c0160152280140c000e040180c0050421a00d0758107110760002c0c96402491044603694a1600901941003aa01022241007810315148603601c0e43d05010701031540681281d040520380880d0350010300c4002e00c103982500440007a13038001910798450034440d610a880f606075550510200038030031601604007030b0510403c864140401a01b00f07002c0c50b4813040918011602000b58030040381040c04560002000500202d000722006810000c3c01c40042c0d030a0b030303a070205910311005c520b00740d03554158958040f0307004101007800b5007000c400d0480190b000d90700722031420743c041c0d440d0421a10903034081e140514012881e24036002001c0b940007444070b214034044503500710020004502e0104880e1200c18560300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 755682 1250 754432 754451
    0x10902040b0901050d0912050a020c010305060f0d050c04020c06010303080703090206030112030509030a050f010c02030f0a030203070c0c080105010302010e010305070206070810090f050a0608030301031a06060f0703020c09090c030a06 102
    0x11070301b00c0e0721000d6011880990f01c01d03165201403d01d420441c03082c0098001c030020648154441e01c1000d122700e20041c2080c85d030f0316100040c00aa40e240c100d003910603000d280075104c05a181c80c0000d24042c8007883c0280700a42c1755040050001101078001d008160818082001696035041500d05403031000d00303490008521441c0a94541c0b24140c4800d405000305000601800170100d40082046d01d603030003e00c0300268814040341c80303204294036a14200003d000c048481403181d8040d65000310303a42001e00100c802900c41109122302a407000076503139141d40043c001c650b400045118070140c00c0c01c0c2800282002000603407914001840e54080100302c0c400a0b54490400014100420743e00c44200441c201c1c1d0318610000d0103044500000c503504299001038006000021241200d800c4621265a1a000031100040002c00380520703038030103000c1c000c07900c0d1059100c1c000c00480703100350010b1030004060002d003c07a0a500814440c040c0d04000040b208030344002c0b81d0521403507484000080c05400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 756932 1250 755682 755707
    0x18020313021003060807050f0d1106040503070305030904060b03040b040b04031e020a050601080f1504020d0204050901020a0e040606090504020d0216050a061104051c020a050301180209010902040b090105 89
    0x4030030401070b50080d002540c02e145260560300010566040c903043e284c50503200c00034400c1c3d44203402856a000700e44040f05402103904102409030700c4c0d80c0202460700e07003035443c0006480c0c01c807560029610b9410010b0110340740e1605124010051402d5000d060842c6025150500c4007030000300090303d007500c09800202018824041061a07454110720302010546940009580e00f0711088212018030138800041401100065420413142d072404c014000000001c040001d04040a00100d8000c0c8001600c400143d070355000b03140c4034840f00d800060300c1d0b44104c00000d03d03101c1c407100c0d5a80070340d02d0100144200ea500c428424296002541c000d03a40300c00079042800203209840e14440c00781c194480d10000c012011503040c81ca00d0150200707100d83d204000030b00d4a40c0c80344c0d01c500d640c0040c0f29814030703807640c0c481c7d12004e4100f40001d2481c11403e0ba200e021900359203219a01d00440503194040c02d0071481d100000c140585050a4110309180c108480390703605100c0c0404c224140074000c110896a4107 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 758182 1250 756932 756961
    0x20c0106050a09020d050108060906060d03021504030509030c19050402070f05010c080105031005090d0c02010c050d02030a030c0c020604030803090a0602040605030a06060201140a050703140115020c0a180203 91
    0x800b6000003911691500b000c002034028030740003181c2ca4140300000445601c000359041c0200080400740015032152410405809031440045040d802043d140d0001c0d540d090035a01e2045010b5120240d480308030310105400c0245210801d803240441041c05c0c0101c0c0140e09140040c2e500c15580107039a90128200b0207120440c3c600c00420301e41c2803c04109410741e100b4403d5040301e20035000c0707e51088400b9000801d43d40d0440c0c40781a594081d40644c00c000e0f00c03485c1c0b00c942d03150040c149800c403400c09490341c0741044c1c01600d0350360140c1e00003d404000d40c1e905120b2147c0c50203051401c1c0d12440a02e500080c05403082c0d11001d0304604011001c508105c00520050034450b03031020f41150349540c0d808015086030070413510f0b04800d51500f10b0000c1c4c0140180104e44c3e1070070b003800c102946540c030807212030018040034008104041d607802195680f1850001014040c1caa901d000c0740c0e042d41d4550b0001d140c0600100c0090050400031030030080c1d6094805c5c207402c03c104045c00540c4980e540c00781c26460390b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759432 1250 758182 758189
    0x2030c010f020a03060f080604030c11030f060103030909090507120305040509070801030308060f03030a080705040f03080705010501080102040608130206090a0306050f01080105130204050a09050a030801080c0a0302010c0303020c0106 102
    0x551070002032400c0000070340e000785210f00250f20140041d6965421320842e4420b14807032814681c000c0000030380003e10408950001910905502c1c070001c0108010900c0d16010050380002903005000500901d500300140c54001d0503222014004541c0c141d40e002c8e194070076481510300e0440c5904041e01094010002ea5001c0c1c0005800c0001c00d00c0c0282c4c00804104081c030066020a1258010566a003030450500d4241000034004518110f940041112000380c0142944104203084c00003082c0e0400b8124003800550080c0342d10350b00d5000c14200356085840c183d00005250784104001c102054000402540c000e0300529003c07100308c028000301d601881440e03682c81e4042030b6440044100410799210030700a031800f90851940e40c0e2035210b51422550150f581132580341c50380040000520f010b03000103074040c903a08030200388449070740d80b000d10701000c0e1142100030428180042c4a510000c000b540440b8404480301d001c0249140c0000c2c0c44100d503240007404060b000a40d5a0081c0e00c2504004002d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 760682 1250 759432 759457
    0x7050f030f1204060801060e06030402060306040605060a020307050613030c0b0a02040803030a020301090c0207030503030606070507080a121106010303090306090618060b0111030906040504020309070306020304030905040501050102030c0a060c0203 108
    0x44410b6070404429403260151201140d825400446c1c020311943c101d04203084003801092850720b60b41c0820801c3e4000403e00b030b034810385600c0701103443d0b10b5401c05403914244070340055443d0046803411a0030414001c10441070710404240a001003039101c2e200c1d441c0150446034191054541000a0b4040d102c0c68001401a02c000028000161607131760056040702e5440400b0030001c02580b008076113420306444042d00503441800426441d00d0a00300902190344524100e0300d205584188007802d00101c3d240a07030f215401441c3c072821640d080061581c40c68401c201511141d815642d01402d007118500018144a41e075090704810415268400203843c0c4600721070030304200240c03501c2e40c0a00320418403140040d10076039902004030320010036900d2242000307003a14205820034040c04000e40004002400b030748908075001020038203902c000c43c0201d000307640d146c8405e81403800b4442640c1c1c041c2e00c6907045600801c228509080e001c40c0c88c00c3c0155000e540812080072408003203145000d2038103880380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 761932 1250 760682 760693
    0x503040503070c060f090503010e0c010e01021509010b0405011205060403030c0309050105100303030608010204060504030204020703030219030e0105010b0703020a020108040c05030d09090e070303021005060303070602030a0c02010e030c07050f030f 108
    0x1c041d600300100303246407125503586c500d4458039001072600741c600740d2001000550000040d01c0d40d545c01001740840030007062045a00d4842c0c3c000a203030403040c0a80305104103964508010f01d490070180601d0f805490342c00040030408450780ea84a5031803070018409030816568142c40c0000d20b200b41c1100c0d9070103810900034800c5003488100304a244600e0301c02140800d01e0035000280009043c0292421941c0d103072910350401c3d18580034000658041a0101c0815608014001c0007108105180700001d0a0b0380d800030740c0014806040e03003100e6060304100402c0000384660707800a0780c000342c0b49a4060b821f280c1a245c9440314900070607150455040143d140c001d00e4003e218180d07000e98144201d03141c0820038802450031805040e1a040389000180058110f051001c03884112504200d0b00041c0c00360480c0c0c64081c090303c803e0126001901d1003c8a6074031035034198079540d0b09008020341c00e5031200c042c500e401451903089542c0c558078070845000c0c1a1180c501611603a0030b00c1208ac203135001d0400e603070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 763182 1250 761932 761939
    0x30c070b090c01080906090a030c02040207060608030414010206010308030c0c01060906090903081b0403031808030304030504050f04062301030204050301021305150a0206010303080c210a1404020603070503040503070c 95
    0x5468003a0200b03254001a20b01d80000c2c444a000240180125041c1000d08860142d45d20125010004100c003039030010303001c00c400e00c0003401c0fa01c154002800030030040e540341d80c10860302ea000c01c500020014115070040006001149250f001c498011115001d01a501c110000c0d4150140c111540000031051030031000281e50140760700102e17034240c4203036500c1c1219650303212140c141c1c65140041040005d030500062001070301a19004034192402e215129019540d9400c0c9842e543c001c5a04030001707540030408200c41d060010311030f04560070498040c00201d0810588404000082030700d211108503818050b0705507402981100d02601c1e000e8000c1d0760f624a8560401045500c5200d81400303200f4146024000400c500309441187c29540e01410042c1d1039030b20206d8503810094180982c1480030007961681004c0d001001811005039407400626140c0851550304440a842032201c0c540c1800081000607510078046950000c8642007241d2030f81c41e1401e00c1c46c9940034030301d001000c0c00755807140070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764432 1250 763182 763201
    0x606090a0f0606081009060e010603020c0a060501080c0a090b03060a0b040b0301050a020304021005070305030403030207020a080a0605070807020106140d05070b030103060207020307050d050a0605070509030304030605060a0510021002030c070b 106
    0x2540b24030848950b103200c1c140c3e0391350800c0c101d80d85440307210b200d92301134401408a10301c80c0c1c0017040200c040c002250395180f81e42d15620300f100e01c280d00030f214035441404200041d0070300e081940000c1011140411440912401003a151030005241100e820703a0344070310b45129a2036074003c42c4210000703002000b15113081e9200000030b40c07081c1c4090b4452104d03d03060103031480c40b40044601040d81035550f1411900d41d1303135040e00a034121000480c0d03c040000804224000100103440c041805040046003508294102030702d82e410203450b480440e4180b03c0240711518003240103070840d010136158292003106505000381000000c3e004641584000800003040c0410354020b4943c0714021001d54031380ca40d48104000142c0c0807007000620307030f4209821500c0411601d604c0713194030440030b0074180d15000e4030b100000e04550068004031251079580d0305201079400c0003041d20002d40000c2e10032004071089444081e590b002800790070f90740309400000060700c00e55404241c4040701d601c810314004508111780340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765682 1250 764432 764447
    0x302070b0a1107050d02030d03021303060903050a030b010e0a03020d0c0503030703020d0305060108010302090609040201030b03030310060201050c0403020603010b16020301020f0405010e0a031e02010e030d0e0102060901020c0606090a0f0606 105
    0x14985034452030002040034076000280c5517500d0340c004c3c014240300d40307400c6060300070f0b4015014107108800c54a000101088442c0100054030344255100c581c0c030b24102a001d400c89046140c40c1d410441c0e40d4003141842c2e05c40c0c50340300080e070b82c04440b51403240c3c44a16040c2c85046243c6c00240d050702020601c0001c0580004a80e090504140c4092206964a100441c0d80c17107001d100280d03000c00418081125410040760507500580189008a07007c03640b5004a40355a0054070a50071407041d400c02003008550a2103599005004003110b03514003072440e0002903081c041070190900c5058005820400d0601c00c80c400241994058000d41d01d5400d00c840e88851600980f08041c00b00700114001c00240ca4078240c400c09890f4401350181f24020456946007140e049808101d05004012101340320030380c5c0c100451440d001c015516005402c2d00e400009050213409443c6107400c2e0300500c2001030200e400f09108e94440020b480e011800c2d40e030300c080c0a000d0074400c148055424074121000c2000c542c89001c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 766932 1250 765682 765707
    0x402090a0b060910050702010f03050702030316020102070c0303090911040e06010e0d0c030501050a05070503070207090b0303070204020c0604060c02060705030103060c050403120801060306060905090f04060902090903040302040b0103020a0215040302070b0a 112
    0xea0031802e021202c4190f0654800f0cc80000c01a041003000070002803940c0b886085403840e038800181008410b81e2002c8150045420617030100e254080c0800c0188003130300401c3d00d403516030001c190400c1d180980500c444000503203881c0c140a400100d03040d003600d820344604011a00544000318041e500c2c24080c1c024802907580a1445041c42d00040c1001e0080080fa030188410760300500ea142c0c43e18610000a2041815890b418081040b400340581e0341c9002419500c0c1d0303090003902160070301d49016011601050001030540d0459800c1104081c1c1000a40c3e0449030441c0011621551585003140c0c2c0c2e110396040103180203883e01050518642c411105030603600b0320b480820030f003502c2d1007065502d0f42041c0b042070b034445100380005540241c100502600144920342c0400c2000c0c2540c0081c1c0307000001c89140e60b03294030106081040d0b18145c0100320300c1c400203017001c500e440b00c4030b10025203c0030049031b01d0202c075142c4804182054801c10110b4001d00c5c07806a00c035210440c0000040511442a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768182 1250 766932 766937
    0xa09020102010b01030b03030a030e07050406081c03150e06010203070602070f0506010501090b0d020f07050307030512010501050304020a090e0a0c090b010908010204080304121412030403080a050402090a0b06091005070201 97
    0x491010f01d500a100782808090000e00031802c126104038110080c4c1200c50101e0414003c02d000014a5101e0707000e108050300c194405001c2461b589032451182000551003402010b00700f0440c030794010494500034054500c545a070412075aa1100181d20310b124924004104601c001210814080e44904410895124005171956a41e03104011151142c045c001c6960400e020000858407242e107600402d01480000e0216041500341e483e103034103507002440b0640101d10300007200c205041c6140c4c12107014001c2400c0840c150b0a080c0c02245111415000301c12045588a1003069461010442042c0043e13111010021283d1140c4011000d41100c0c10044e011801d0b80f21302007a044018003c0e1016155003900231410541f91948811031340200300c1d4103680343c441421464005000510501c5080d061b5240c030581d40741007915008041c5440248802909483d00d42400010f07603d200b001d940166230071001203040c05264000401c0ea11516000b030340d11000800c2e5040c40240c00001034400c483c000d8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 769432 1250 768182 768191
    0x2030c0301050c0f090a0506040806010602060c130504020c030d05040809030706020a020d0605041506060201050f0603030703080c1c090501050103050c09040b13060609020a030605040606020106030302070302091302090a0902010201 101
    0x2802030600703940302914803d816940a0000c502d00040540140014107030040189814a81e2040810416405900b20905680240b00103018035601001026000700488003c2450302480448041209c0d40740e003e900d100310b40000782211101d40c1042038548181d0b1540d820000e608141c40e00041d56484180402d0003030040c804000385281c0040345852000d90080d250196243c0b56a40e03000c006c14008000316202d48603506510060600d070b00c03a0b000500056000001c41c0d0400c83d41c4d80f902c00da0020070312031107580200102c0e400240d00c040515001010400c56546600001e0905e9904400704081e82401500c2c104408050240541049041f40e0283c41a01c2c0040812404c0c484085800c1f5805042c0c0d51059010134913404c0c0424100310540d000b40c1e0000f94098031004801c00745d9000004400010313403504414440d80c541442004010071081c0000c220103490360350042e40303640081c072020b48285000c1000800000000d594030584580c010120911031411445082c02040041c0081e80158a403 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 770682 1250 769432 769453
    0x60902030a2403030503010e070302040308030702030408160501050a08070e03150109050a0b03030a0804020105130305010510050102030301060e01050705010908040810110f0405040f060302031207050111040b030105010c0302011b09030203 104
    0x3280302c80d030903650103030f83d0340386141c0c00c0100d0700824681c00382000003019402c010020101e108900030358041d4030720754042c541c0c03070345031441481c640004d0442d02a440910003000b04116070300042164030000346400e041c0c0c000c0d070700c0403410780e0150542c01107160140507141c41d404070800c03d0380400d4180c0d03804030301c00c0006496520740002120a201309a58241c0c3c404c02510404e1801692101c0c1d1040c0305140840c07074603c1c7c84100c0340c0d100071281d100701d0344c81c1c3d1200280310180910740c880002a00080c40110f01310f6161000007884111416111418032100069503810300200390854007800c0e8101c07400701d9403070380e03640142030340d40d5440e0b03480c4131000d880c00035240c12006059040b18218242840401e0401d8144010000182003005042007400d6545400100503102801810708410b1a03048d140d0b1104842d080142c203588580100b40100e41c81004180814000b100999055803428642512608450701d41a03006240c014118408506d504003415803e517405041c16058910940c19a43c10a11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 771932 1250 770682 770741
    0x50a020a090501050705160e06030c120303060d0503040302060a0207080d050403020904060b0103020c01060f05180103020307120305040e01080a110906030c0105030603010906050a0b010906080403020a02010c06060902030a 97
    0x84080e0320001580401c000c01556100d100a001e910b401641070b209640e110b0000b0107004031a660050610300c1d601f0041100c903207004e000e402c1c080c0c5410745a040296414086050700d9100044c811031041902401b0007090010801c1074502841d4050725007580d603089080c01239075520545c420080706114000c0103a812601c50400d840489a01419021705502c8543c3d07001c01400c2d464015a0400d031f824044200346030003d010742002041111244502c0905010500c2121100c80d4407401e03000e40c045004000503180040c82e00215540d590801d8141104d905d01102d16100e070303520081d0124281000818100c00c003090041c0e145124400b00c0c1400207010040c01070301d0340121280c2ea4140c000071500200c0303501400095602041c010300004103241c1c80c0d5105811200c0a440d18003040c1d40e02c0e844d044d150f507000400b0402801d514241440549030540c0c000355110b0485000a0420120340140010000c00d900100e0143c10000001d540b00e01c0c0008031280101401e005c0c1c540c00822220241041c1039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773182 1250 771932 771937
    0x105040b011803030f0c0501090309050102010f020c070e0402010212040303021b0907120903030b0301020409060e0901020f0a0c08090405011205010501060905030a08090315010b0d06050604060f03050406150801020c01050a02 98
    0xc005142c0440b540b45103480c19070b04011003481c80c6060100d0740110b03c00040342031140402d484c1c802d4958483c4623003440c00090841e00000c000c821a24810844602000780004056040b80c0800d018145540d49a1004034180318407038040402038440401c0200426030045145070034540301c40c0c1d044009202c1c070410440c103001c00703851a502140d51000a00310031071130340c1c105020280c000d040115809028502003030032a03026522402206641d204280900000d0014454120790168008d60a26841f02d00181c860704c01c104000c0140090710038400d04211a441c1a070703880000041040001e036941c0da411004200c540607080701c80c0d51800c40085000c03030091204001742c41d00036000f4903958400d5528141594060703e66980d2521680c00304104202e8404c420078042c18a01c0e29168541551103003100540303046802103881000c080c0070034002c8540c40308417440c8120283ca00400d01c0e0701c030f03810035030020408240c02d840074480c0304e00c0c08500180150018022580740200030055540c41715465412070 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 774432 1250 773182 773207
    0x60a0c020c061911030a020c03160302030309090406060305010204060c05010c0c0308010501110106030c060905010207060305090c01051602030a05010b01170103020a0501030c02100203090a030f05070308040b0c0906070b0105040b01 101
    0xe00500c10301140140811884900f10107508249508164840c88207246401c02254031005074401810368441303007012300200c0302e00c1800172805a0b41505640c0040d44034002e80341c2c420300618441000405010a42c0c201100031a041002199140e4580d10000c1440c145083d0540b19582046c0d410940e0a00c42d1241109490700740d80c03840c045909240045401b0b11882c504282d19640360600800404c4058444100804240d02c0b0b030001646800300290405039583d0000c0d06161070802040341d05100801e0303c01c010103091034610754500804c0c104081c440166a0085d4051142031142d500b0000150311a1343c0d442c4098880e410f0010350110f5140c00c0e003900b400020741240304a10b0810171540685c000422450603401541c0c41c20303a0b001e6a80d012a041100d1090340e65000341c07450001e01d44c201c3c5e80c54104500c1d0345412894042941c80241032240051301c0101940c2401c0006541c0c0c04030720f410b0310358800e07000b081c29654803c01d08059450036001e0281c80d00c0b441c507265030551651300605061101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775682 1250 774432 774439
    0x105090f06040b03030705010e0a0b0702030f0d050c0c0d0201060311120304090216020d0302030d0c030204080307030f05130e0105091303020a0605040201030603080c0f060604020309070e040203030d0509060a0c020c 94
    0x681d0344034010b210281180a68040e003600c0f090003c100000e200b030003001d4001090f0f0004144284050608160940002c1d01b01c0080d50420048411906103030130458546401c2440d000c0703915215030301018038034883c10094606900640c80300840e0198190441c4003200d000d040d015902a031220304208c00d4024000190a5650007040200001a02c64001c0c0640205c10b002e040c0c24001c1d030341c0104d502c035487d814049005070400a502ca10100c2c00d8881c80914400700c0c5011401d05060010349075580c4918240a000e2140002c415004203200301d0848a64800c102004140980d0320154140024028058640300e541000002000260904000001c55030950b004104e5401c007515100700807c1e001c2c0003641016100c03000030022401800050201031058001000d00d02c0c80c0c0380d0800d04000d4058000c2c2e201e18010018071202d01c2002540e6801e451589007175403520340300c500c0007a28600c16101d08628460610080020240c00890024812101d019090001040c010030480e15130f840ea08910b9032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 776932 1250 775682 775711
    0x70203040b0d0b0604050405070903061503020a050d05100c0e0f030102030f04030507060207020a0e06100f050f0a050408060109090201020708030901090b090105090d080c07050102070f09051306020a050a08010509 93
    0x64600d90f030304100042c0402401a501c4c0c151600c010800f522421241200402c2d1400d0082080110911030740400815003c81c8107081c1e42542e00092030303041035102e01c41c49146600489170600c88284008003d6141c0020104a2034082d81c0d8068000090511914403038020f001e441c01103401e060084034803c1c01030529085884d50703036075030a85190b0013103041030300e030a03600b03105110050b180c05072103c0c060803042d12040190311340320003003041041c2c08080e820100b290002d94501c2d401d4101090390200081058101e842e031540307800445450145920a0a640c0b0a0340000240181107034400c1300294000e07404c4e2107260f0f858141050752441002c0e0910700142450a0400004c12440050710051030f052401c00d00d000800c1c030004100e040040c00c15240c2480014104103003e508108e03071402408280058003c0c1403801c140d028440c40188125404280c403800060491b0100c51107566074558089002c5440c0d4000c0741008100d1781220620f07101080000c000440c0c1490000f4866101d0540c2811080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 778182 1250 776932 776947
    0x2070506070c050f010501060305010905010b070c05011d04050c03040201090b0f0306040903031803030509010b010e03060a051f03050607020105010e0103050a02100212040902030a06050402030402010804030e03030d0f05090105070203040b 104
    0x807482c00c1d5014068a9038001c007203039800070380e8013030217414000d25240e40d012807554100105003040361410391081d4000281000300c030001555200702501150002d0903c581070390709000341c101081401c41c0b182a4031510704000c21101400319400356015034001e0740c8881220342c484100d005d6910030240729905905042c40020140d18054110910081c464600841d44065181c0950b040c0c070131450045011035120410440581800d105992078080240b810074172030010700000c42d0321100c001e01105e07d45078441f400900800348500e6070403a1065408011340c4400d507282001c0e51600c01c00d540400040d42044000210306252442844c180d80d0800d000d480440c64541c05c010710070030f00d1803010342540194002611082000c00107440180070314400175990703184c52000c0000301c640580002d40300c0c51050090001503640010300d030f0f50003a0f0508100024010074000203140d4011400d0404c842c1713061401c0c1e603410a90a03046036018480020081c0082e803500c56099803280110700504100790400e20211 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 779432 1250 778182 778187
    0x109060507090620120a0201020306011e090504051008070b030a050a06030c0905040507080609030703020c03010c08060d080403020d0305040501020607020a05120906040306020403050102130f0b040303030e01020c070303031b030207050607 104
    0x2165600c03503008941c011401701d10020402e400001368000982d50100030400d940d40c104103020300c02c40b1313100d5000c1d900b01ca04d00006881c03d14a030023802e00650751000000c4840d40754a4500c400b9018080031110126030701c0c001f10400b9442100d48094441c10074000c2030b540c0ca101d004080541c1c2c0e01180200c001e60030114220000c140040060b035040c450b086000405400c00d000c8203008000c00c80185035901b06908003c0d26052040d008903010342c0c54104000c0c141c1d980500c019810080c22503001c45111120708010295000b1a00041d5208801900c000b040581140c020400c544013038090302d103075960b0580c1c281d0301c4964045d40540305030051504040304c3c001c518010b01840340001d01d02401c1c079441c1c7c1c0341c85040f070304140c00858040c0e50006c0c54038285140d80f180d840040010380c180c1b50301d42d410a00c80c0503241c00740c7c0c817008040c0340c0c0315201c3c6114964203405070b135146201402210820750303490074020003600401c100020080c1040715816080c0c4c0c481d000b2180401d40110040c046a243d40030704 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 780682 1250 779432 779477
    0x10605070204020909090607020f0f0c0f060c060a02040302040c020a120f020a0506090106030512041d06010302041205010510060e0604030210050f030a02030601080c04030f020112020405030106030501090605070906 94
    0x80342d110341d00b00414151551403003802c90103400c1c11b00003041146840030004c0e2900c5070142010403d94413095202e80d100703500080e00d0600910035146001c0090b1a00040f074503038083e9001c5411140500b500f00010300c11550701500c21a07000700c0d814062117525100981e08c424001c0b10242c031107640c0c5c130480042140100388070b0305544114811560807059035210682440d00170345035000265181c40d01001030101c1044494240a0040c1c5801d190074a0005c00d40040001b108111100d80d01c00400100540e004c0d81c10f82c1c1c01423200d10340c1d542c642c1a01c2e1074102e0003031400b198076010700111118041031441c40380382e105550001c040d084e5854503003580c007040720403d07607144000c1c2004001c005d410100000380b0082c5001d4101c8010150304c0f0704154001509074a4014600c641a20303080c4000c10200e2002e407118200e054080c2011b0b024030201840440c068880c0380c010940540c00c080f400010000158000240107001e42d004001c284c42e02403045801080d0b512852000547c01100b03070081c040030140 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 781932 1250 780682 780697
    0x201050702010305100b0403080304110108010e0f04061404060e01060603060b040e040203010905010e0a030207050105090105030c0306010309060c02070603060e040c050105030c090306040b070206090105040b070e0105040801050405030403022106010605 110
    0x45e2000380e55134640403640c1c01d621a070030031240302a020003808100518101404000602401e2002d400e606040014070762203001807060038109400340204003070203a2544028840700c00044040703414a86400c209010f030001040508242d843c110001401d14440d110707800039902d01241c0c80746400c3c6040c1030035680460140007a6819503a540580001a001344103003a480c0c20b28071301a060024140c03d0290030902c09600850501c401000002e03400da0703000c011641d028a0204036243c4036200c03000101e000b004c000c100204400d24214000d0740e003d800003480c6048825036039040c000e0a40f03403c000b0f000500c0580e070041061400060a0200d580503601841d4045e24000c2c0381400c1c80b9440c40002d2030028141c0b019a1007008040a11a415505103c125880000c0324001c1c0218205555200310604000380140c0070050080400c2d403e1341e10540440e0018040100284840c2c103040c24025241e60040c8000c07446075070103608a140314150302140e66203810381d40b4080c0410760710300181681c00d58400f20 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 783182 1250 781932 781951
    0x50a0f0201140103030305010f06110a020402070501090b0a050a0f06051804031b06020901080105090f0f150a090204080609071202010305100509070f02060a060509010311010302040305030a020607021501030201050702010305 98
    0xb07071491801c101c4030390300c1c5000710300030750b80402c1c1540b42010f81c141100e2981c120030204001454051010140043d011042e9030b41503e005a03900e0690409500401c0881c0000300400208028080b4051f00e03500010702808030070341d04201f0544002520f00c1111140d119040e000aa040e50f10103880c12007528140d4072a009084ca0341e80ad102c0c109c2000300030714150714100e8442d039011a1a00580d41d02c482d00178090b22003583c0e041c1d05401c1811040009440041110041104000005d5190141e4540f000c484880242c04204400e4594111002075001409411018441d1100140b051000011094111086000c61404001442e0011005000e0007840e54058403000d100c0050b1a4403100d94041c410b13880c80da10028200026000242000406072034940183c1c1004404e000d5551200c81150449501c20240c220f00b40c56000181c0284c084c541c0702801c01d00001c642c1100258001c1401d900c182c0555090b1400e090150b100326869100131700001c2c1c00180c0512039000154001c0c2c1c081d42d0407000d40c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 784432 1250 783182 783191
    0x303020c06010b04030308010b030402010c1103070503010e0105090c0604030305030a0b0f1c0b1b04140d02030102030106020703030206010602010501060807030b03070e0106020a020114071a04030e0306010b04030311070501050a0f0201 102
    0x44900e5841c01200380c3c000d0002107000203003082456400b01e07105024014140c8031525504040d000204084200712016000a90f610f10980d05a5010080e2100070100503000780000a40b5550640c002c0904840600365030092501030100b40c50500c0843e4142c940c142c40e041d040da200e980204000340300c43c0080a400c840c446001c00722568500c101c02c10b00100a90400616082e18a008040f4080180c05a000300d412405c000030410b220409440680b0b41e24519900812034640c00241c0e012640c60001c1e426510000012a60690109010702568001d0f001c07030304542d98030f86049088800c03d1080f030000440c2c210209841e0b910035082001083c0c40203048889868a4240d112803000c030a921000150340090108401c650700038484800f20801100081e05122542d22003e608183d0710f24002181503038400000d0070103010b884401d0180e10050308880321580c5440700345009034840e02090740810010b0700451001000001c040050311410380d0b9840c10b10038140d2095031300004c44000a070a55484 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785682 1250 784432 784447
    0x20a0803070c0b0a0507020d030603020a06050c01090b010e04051207030203030402040504020303090a0b0301060212040305070302060304140a08070b0a02090a03080f040902031005120d02030a050d060b0c0a0302060702010e0606040504030302 105
    0x3d800d2550240d40c148000140d14105000c02928000103112a181031508000081004d170383c60105840854189040003a50b409210b000c040c0100795024000300019001000400c1e04203034109100c0c0708034070810440c0e002d0307249880100c0160280b2400200141d1003000001c005090507005190010b1000d0112400c08060000280b51402540c020696101e004001080482c0d4100102c034014089626074924050940d110f01b600c8100502000e4096080040483c0c00c0141c0045d03089a201d00701c0064407650f5400d0b18002900e45e00030b40050303c441410b4004140020614030842e908a10028501c482540c615620040ea41c0c01401300c1142c482c3c0c042c040007482001900040d8407444185131200100c80c00c001c00c110a0082801c0000c0d0503030302141ea2203000300d400104407040003078982805a1140219101d480140c200b6400a0702000340100300071500d05000614264914801d8080d240c80c0e5840c070308101e080380c0c0d59882c8456541d0003030300881c0071418203a100d02e030094000d1401600d031044 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 786932 1250 785682 785693
    0x20406050402030f0601030b0d02030a140c0a06020102030906010f080c011101021c0b0a08010606120b0604050402120a05090607090303080c091008010303080702061306020c01090c0902090f03010b01020a0803070c 93
    0x865101c4562071305541044019a414840c50094050071110626544029000b20b6a103d901c060000d200d1030a4200b4440030312002c120b4081390010090903a0b14407600d98a000b03000c0d4000380c555034000d105840003c82c0c3e520403035154406840c2c00100811001c003610740115504c011020000030f89550030001e5050695910740c40f82c901507161034008c20300c40702c1c800034007158940300c3d130210480382d140c8001885826441030031510b5405001c00302041c045990700024600340b103264080b55005100064000c0b04080c0001c40602c42c80480004014555a44441c280c841004a07030708000590840000c4c000030b40608201c0b174120b000c04000b00e080c0070082011482c004e020256031408240c15400400405503c45e0103994400c030a0303c0644494100311381ca9090807803a10500900f03da8011914a40c00e0800358454400c858201c04610031a07503484003108000d509c203400c1d1034090205c182c2402e0883c10140039078001c4000690007016410099100c0312030035003024008000304013000010b0404642d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 788182 1250 786932 786937
    0x9020a080304030c0b07020105030f04030207050306041110020a021507030302070503030106030212070f09050906040e0d0302040501020c0303040b0403020121020a02010b0a0608090d050a030e07080c040605010503040b13020406050402 102
    0x140340c100450b5280e04509040341c0d41e40096200103280c0310104600c10060340e21405036608000e503214420040c3d00c6514041c0c2c10001581c000b02c0d0940700d003400b04004c3c0800b42040410b4104145c603001c00703210300c00303808907202c3c050080080e400c4600441d940c2c80c0c1002610062076000d000e442c00508140c0c8035600c0b6421940281e01c001c000035004180b078400342e81c000003050340100c201d04000e100c03c00000c80241c650610761098510650240d0001500d644854101c7c1c500b000c101d400340d410211500c40058001c1d0003c0c09440c0c010320424040c1a6541000001ca0f81507c1c060b240d524109441d5600460f507100c04608110071342d1807441c2140300c0684190001c1c0600304401e8001045203420042840004903083d4007210411400b801032024162000c120300004120a1400b203030385038016101038001d002c40b00002c0310b135407007040c2c400a40c5000105500b581450f04507030620500b0b6941d07004582d20301054501074110b181450100d03614400c0420030400091001e400441c500d9900c6001078100d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 789432 1250 788182 788189
    0x70c03080901090f0c06080106050c0604061e0c0314060a0602060604020307051201060801030b06060304030c030309020102070f030c05091509070509040f0911030106060302030c0906090a0503070303020304030302010f02040b0a030f09020a 104
    0x42c03485001c00d02140c1c0c2c1100c5801e0140c81c00b40b40080c10b0400c08030410340e3351400500b020340315075035078840000446002c200004007482e26a000384010145004028010035440e25000700c88007801e40030030414034041070103000301ea02d03a40c000c05603500d910081200944c006001541401030410420310303100d05a6100070700070105a21200d01661450400c180c4915000b40190f1080104000b000300103900040000300d040e41615000031180c1c001e10040c0c0ca420480c2d000090b0007041200008100901c070f0700751070161042078030104d140d41c0340d032038014a50010741d284076588007400e0030004010600c200e020300403c4a0040c00401c0d10006264804c0840700400420b8440210000d4110014102401600c0041c00d01d0300e03003149107117058549406a8014404507a01c10703c000920800c2c2551600180710260000500f070301c000319500e00d400784d600d5201c1d1000314055400c0c80261307024154070f44241c07000c49410a41c43c80ca1b141040130304a008140c0107034020314150f41e8549a90150b01d5895503031028 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 790682 1250 789432 789443
    0xc030302150106020a030903080a09030203060a0b040b0402070309050909010212010603050a0b0901050901180b03030c0303040506090c01050301091d0d030209030f1605040504020a030501090b04060b010503070c03080901090f 98
    0x101e54400582500321081604500150360140f103480000075030050700641202d40050440d40c071541104011a40060141d102940c1442140c0602c004626641d00c039002030f00c0c0071a4100640d42c651001e01c000c2c0c0c003e040016020031400d0740100f015080840c0038552004500000514000c1c502c5018040e490081e0842d6000035a00d00402c075450f0013034403581c0d813803640c1198480103540c90000064503140b014014003810440440d5070840070380036900072240720b810040540340c5407155240155520f82003190150380c640314010104800403804a000d50100c00107035242443c40e030a26000740040c040b0034454030441c0b11400141002d482e82800000800001d9a6015030341f03104640415291003080911030038207800101055191152004e10001100c2040d200443c0c5a075036400000c40042596101800b554200003110040060241040d44124401c4604008003141007004590038081140c404001c03510000c4d44c0000310f07001c1e43c80b00343c0c056054000410440031599402c130720b00e581c88808664 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 791932 1250 790682 790693
    0xb0109090201090501030212010b0c0102040305250b07030e010e0d020301090c0f080d020606040c0507080d020301090f02030903090405100b0a030603060e030906040303030b0103020f0f07020405090606010c060e0304030c030302 99
    0x110b6a010449000900007440e0940c1000100d11540d0a904418403c0703030881480040e40c0002ca035801e40556000310340140c241c0d4154400501102c5160014000411640c80c030341801080d200074540c1a1500190146c0e903003504042421b006564032a040b5400c113a00c07214031100c8030300581c0c0900800a00611414000c5201458591501ca1010355034001042c0794000f800c90443d11540040d002d580000d04a030701251000e8542400c0d00c0c14862600c020b04400e0002440990300700311030300103504840709a0410010003a04500040807030205480944a540007005041c1d07003403600390000350708200646101030003940d8424452003130313a11a1a40402098031540c0070420b10282d4491075940ca01c000d40954581410000012414421400000e0031b00d60344426862580e4401e5040e0780b0246a03407040c09aa41411080c450066040301500700c0c441e500b403d00090300c2c100c000c0b941070700600040c2c40d4440e80b600740782d6a0300082c1c00d0090f03402c441d03444288800008512203159a60045010b5000b414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 793182 1250 791932 791951
    0xb0901030b0a05030a020f0d1a0103050709060506070605190c020c090a09020303030105060a0201020408060406090203010b0411030109090f080703030615050301030503070305030601021608060a060501030e030306040203040f0b0109 101
    0x14103907040c0e008442e00c81c0074401030401ca582c9020424060182e41100c001441d0740d415000031311039411190003c3c2010030384005030220007a801d2043d170305a900400441e021749503520650000e446a500549da0001e4050204800043c6190881a0840381d40540040001d05030007210307048502c140d116600603030140141000381d08101011640001c52090300b0f01c511046500401d44d2884180301d0707280550710004040f00d4031031023981650080c02d01c81e02955030a00303090900d0b0001c0c0c602107100b0ba1281d483c2c02e03a4041180b506201d4070b144100c102e0225810340c0e190882001c010211041d0a652030f540010a01d80018001d200414081d0706c6a00c0000e0b00500b04041104070300402050360b400d2080030001403011610001c1a40c503140d9041ca4802c0e925554680101d041c4040c1ca10400ca4030801c1d0040410030f403c000c100036210340000c1c0000c01040e6134800045040d40e0034601c82854680042010074a0303800c081e00110ba00600a0502803d02601a903c02e0741c8c448090780f021402c1e568804c48403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 794432 1250 793182 793187
    0x2010b12030405030a0b072705040507020105060306040204020903010b0603040b010305060105090106050904020d060b0705010e0c010504060903060203060409021203030703050f040305090103090201110304140a120302030d02090d0c0b0901 104
    0x2010640c050011800d05003404007103a501c101c1200301034038100b0f0050000d101c0300c1c802d040340e20b103032940d1103188603c290340d000080d507140201d0301500e4032860429000079070b82441407054500c221030040003045542c45a4007840700950141b80b00b980c06540f5069a20000e40700d0000643c0186c2c81200c0ca0803081d85141001820500d06070010b030704c5800d07504010044698810152584081c0031100140c0e0384030000a590014401a8810b26042c030002c503c1009121065204010a91440302034802104100d03004407060304c158001c01020403801e40040c408100103a01655101d01c0140000410500540000f40ea5003007240f0a40f845900000801904c42d81c1030041682080c03143d00c4800060501c1c1d41c0144c854015003604504260741c035515a41503a200315025000340101c10300b940e5a65403100400c8a41042d25484640507d45071403001600c420303551844402c0580541c044c0d806d11038070504000203913000d80103250b8020b003000780071000b084041c510b40c40100700b40c0d10000c4d40e414103023001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 795682 1250 794432 794449
    0x30c060301030201021506040f060303050705070603060b2703030403080417010603080304080d0605060309010207020103180803010312020f01110301181a0f03010f090c050102061803040506030403030b09040302010b 94
    0x10580144000d200402c01030760002a01415411400b5004c01d543c0d46100110340180f400d0103224410394140040001031540140040c40034501480980352015180e410507400d4031a00d100300302d8410000c001c09000c1c001c4954800c1a800054100d080c1070408200c0080d01d107400c01c1d0010b8660f81d8002908100d419411781541e840486810300901046245031a240e0700e6000040c0094a01c1e43c00090783c9001d0500c81d841140500390092290340c8074201901803d00075041150200c0c013203440c00b03958465010070007007101c540c140c1c009e1f0120715507800c6a80741d92038107501043c0401588582414410404028021444507100450885072a50714003e51700303031801d801c240b024207824078000c0c41448940e600d14201c285601c080c2d8406858042000100740105030154001c2041490141550204141c21484c0300465600740e0840e0280d44038007000ca00c86401c070103c803001d140e0040008002500b481e502440d401406401c0000324030040102140c82503c00300d6003200180d56884a04090b450b29000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796932 1250 795682 795703
    0x807020105100603020702010e0306010902040504140105030307080c070e04060203040605070c030e0402130902040305010b010f02060c04060f0c020402030a0501090f0c021b0402070210020102030702120315010c020102010e010c05070203 103
    0x24025420200307400e00c246a010f006060405400040e40390569000e01c4140d0b0701c45502800b191103e41c0e40f404000025002805480d00c214145091700c0710002c1c3c441081e074140c40c1c00a000d07500c3e01c48940e0702e40da0f299010002d4906980100c0f0800101101403c264500c0f80b4064000503a50b031825140080440f44002d2059003440305074107000000c00da20031111541040c00f5100142e903240383c8294803246140c5680004d111500000d008410464103402c1201006020380355114284007484d0141c1c0c0303a42003152180348a0000b0b1004004941c070a0446400040e60341c240300c0c02030341d0280c01140c281c0e4000c5603c81011502e48004000c4040184200c0300c00181e1544104100041580025241c200c8815084142c0c0d13420f5158680e25070329a07040319052a4000d11003901402081000b13800307074008907101e43c090702809d01d03100c5042000b00200d078882c0910082c9810807081c01c00056915014208069045640c0c641100c14408000d03c5101c099400130b80303405413119413610406152440d07a25 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 798182 1250 796932 796937
    0x2010b010306030b040204050a020405040204080a12050a0507080307050909090a14030a0207090506041107030809010501050103020301050f01050c16060905030c030a0b010b030421030f0509060615070302010603020406030b06010807 101
    0x403810808291329809864002d03504880220321034940c00055000303401a60003940d4058800030b000990010006070102d5103512503045816040352091081e10280690304424010030800c10a80c0300003900c2500450303000308242015030400b1243c1d0045103003054100c4007001603a200861a00c00d03c46501801c00980034139000651800c00380d0794009444d404c00784200c20809490300c0204400d56200d0700700340d0303041101c0c0307a0076501c964040c24014130701c40742a100d010240d4640030001c24254442c0c0222416204003420208042c070702c5500448843e804001018014013400804808810103208020000e201d01da51700120f070f508107c100350601207003401242c4a40d01c403160303401c0001e0700c07804920304450511844680320b80d110305018110f0700b141814010b1501e00e08008413801905070f03100844080781c0d03d02c00c1000e6512041e5807a40c0e48400d940300c44d8800b1034a8070b1506080085d60040c14640c0c1710b48004544203035a03a003c9026201181c00880d0100c00c1a0b08000c2c1c1968806800f0390b1111161 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799432 1250 798182 798191
    0x50906070518030109050a0302010510120201170a021605010e010f05091509030403060c08180c090408030705070602030c0901030e070f120303020708030a0504110303070515060d0b0403030c02010b0103 88
    0x3405803140c450300c414100c82030388401d10005140e03421740c0000c01898000c0c096600c0000345180080c001c100848101a041d40041404181d07011500880942c40d68107131034908890b400090050300101e0010812004140c08110107100703083d802803400c201611030000894941c0e007000c0e01c00c1c25a400140710090081c508000c0042010000031040c0c4c0d4070f900030084100341d8031a540000d045105641010301402d0610582c669400c2e4030001041c0b060581c103071090160200891030076150194094425440008040170502148608000703541000003400c1c02441e01070255a00c0c0c09981003140c0084200c000494052103958050060310018409000907001560074803410401e080514028815a8212403101c542014065130484804941040b0220345030300d44040301d80d003d045c084034101c5041901000707001d41c40c01c00006a401d440d52001c0a0a03910507440d11100c160708001f01441e600c4051611510041030f01201c00c54020307802550045894070213070f00041c0c03d44890702c00030b80c10180750 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 800682 1250 799432 799441
    0x1090207030504030204020c010b0303070804050102060105060703020d030b01050415030902090a02031303030504021305010806040201020c03030a020c090603010609060e0f090703080a0503060f030601060216090203070206010302120a05070308090301050906 112
    0x2c085600760380d0704480040e00e03000c44e00070700c60040c503d0703c100301c0d003500c8001004030a01480c2c0e00074000f01c2c0c40c243c0c201d07062681c130781050080a0091003401170142c0d00150341a41414003070f4000c030584150601d440c500345036540c014540b141c205a00a1000f107651400d0520a6007090781c9250341c0012421425032039400c01c0303a20488004d040304009010580c0e0f85d000700342150b9600d06030302c2201c6800c050900142d6121204a030f110001658224090320451461800c2030030302109403501225590041c107150144d035410b1001180005040507459540da0501080b100103070b00c40c3d440038020780d0300d40d58100d213010200e10034802c5014000d009a80e11100c02000014440710072101102024502a5280c0c1c650102180f000c0f0710300354003079615004500010803050fa00103129407161401d20f840040c5a9900c41540f0107d120650f60039006030000c3c1c0044c0050b05042101e4185a9210002c440c81800c96446042c01d24103250030884060000080003545841c09018407600181100054412800c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 801932 1250 800682 800687
    0x204060908070501200c0904080301090f0e0c01030903120507030212010603060b07080904140106020c040b0402030f0402060f0f0a050415050a020c01080c090402030103080306030f0703030903061e0905070801050109020703 97
    0x1101920035070716480325517500080c0205004180c1008005041d00c07206086c1850240d00742c1c0c1090244000d011702c2e0175140c031100402c5001310504948060040c0003140781140044015021142c0c080e0184060070340c1c0185031224503c500c5201d03070307900d0750011f03201d041c81507510388810b1041c0d0014003054109501401139840c54421901500d07801560580c8e5104a0f20105014001c4070b00359805000140307000044850f00450405d0214600311020000d03000d6081c200401c03800f0a47d0035101700328082c7c0c002401030605030001c00f22039031506101824a10b15213010800307544020700b40d10001e5804102003141700380c80c480c0c4042024081c180682002c1c003c400007540d0f200300841003410010001c0104125905050450744002c00185c8155900d40e107074200071409520548a41c0c1c041e00c525201c040c0c0d11440880c4280030750f6030503130705e1440080c44d546400703022b040c260481c180d03102c58018990030074a081e0b03c82e21034610301c2540038016951410b401036084450591101c04114010042840080e6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803182 1250 801932 801947
    0x7050a09090f0b0d030e0102060714040509090a021215010906030302030904090204061503050103110303040305150406060e0405060a110f09041107020d0b150301020702060304020103090f12030204060908070501 92
    0xc5481c1000105609007002c0180603003802d50b2981d8200d07244500c103c05240d030001d514a0701901c00c2c1c00702c0d04640c96910f42102c0f20900a051b8a071215000e02c000d2095182c03039800c140d00840c5440440f41c07c00c80313603000210004541042441c3c0780d0301c018501e14a80349030610843c0104592481080100d1654802035103a204a1175071a210700c4e6640c0c14a401c65030785a00c503101078100220080e09520740600007038000d00082c08241c8071100105584403062030000110b4065070b6000c0050128402200a0700c1009a00640103c502a40b21074001c9040000c410364a84a00c2c05040101a0740c180208403204845805c1c501c1015640d0401c0a44d0740484a0700c2210880300003551300052040301501c0c01441030180101c003d511000d900c051505100101c080c150007455040c2c4582c07900c454020030035080307110380500250401010700005000d5030096004040242c0074240010102d07405980c1d241400c2810510a40480c1e40400d082c0a810f50040212001c0c20b4240700400c0c001e810100041c0055 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804432 1250 803182 803189
    0x20a0c03110d06020d020406020f010b0a0e0403030609020f0403030807020708060705090105070c06030507020d05040f0320040501060f0905040b0306010902130f030602070209060102010c0903020f060705060c07020907050a09 98
    0x20846540c0c8001d641c07a185000100c1e03d4214104540342d01d410070a610207035203d0f104140040c85020701e0190741c1d00b4103200f0500301000092518950514200614010070380052065003859590782002682c001907000804240c40c0100e1855626411481c1c060001c07a405000002194800e807000c0c000c41d2400140f8907000299130810544500100c00100d94510410b0001131030301d620006c0c0040d130720350160046030242d042502541c040c0791032000f04076442d00481c03252a1100700162820000f01c2d000200d0010b10115008080c0074496440c0c002c282991400c2c2e00410000d2951010411210346c052042405410110ba003440040c402a002995500d8103010701c41109a00242c8a50104030150f0404005c084100c00054040c4e0f42c1e04002000390041e24044e8051013441001408030f600c10301c1944034040082d220685864107580a01032907941400255800030020072101000c10030400c825072140c0041c80205588960b203105000764000c01030240300500c07100748117180702c49402c014040240c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 805682 1250 804432 804443
    0x806030604081803160305070b030403050301060804060f090308060f0301020702060405040209040902030d0509031005010501080403030c020102040b04031401060503060402060a050702030a120302030411030304121103010209040203090609010507020a0c03 111
    0x110030414039a070b00150b48082d0940d81c5440751140c0c04170005000e2505008903030003003080d00c04496445007860094170003150002e001610404c0140708260044031100c2d00180500780011301e074400c8d845d110088404400040e001b0440c11410001189040d0814007800b2406400a41c05c01ca85903001c074000303000d01e0184922070340d0042521480c0780c80740d40c0018800b540040c201c50f20074450300405000340e803001110074085d00908080004404d11809124103e4006030759540031981d454800714000c2c1400901041103540070000080c51015030745c064006135020386038103c445124000070a00311120ba5009a001c2e4100030100409603840a0958880b10b46d64200190b480c031943c40002d040840e201c2005244a400c82d0b00001c203a9072540c041c5115030b2103544480d43c2c022601003090f5890203240301e505402210340c140e80f00003808100182d0b070303401c0002d0005400c00c1e0320800090103a030012100039885901c44400c0080c001000d00607641c10003060b0010b04105482c580301c030035010800d400007414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 806932 1250 805682 805687
    0x60b0d020306060705121207030501030b0c091807090f0e010f030b04050a0807031d030105010311060a030b0301020c0a050d0903080409020a0e0405040302030301090c110a06050702030403051002040510080603060408 94
    0x30303e403504000c50711030707591140a80380d05881d02211703091030390880703407800748206070b850f00184000d4020b11601d41a00e400c49840742960703446079521152544030b8009140c0100c1d5041032400c0c1c0260034201d840c01028035440c0d100601d8105081040201d095a20060b40e15072142c004004c890b800404420980342c004214a00d90b90395410454a40301800c0e82c000d01c40507001a55a040c190711402011540f070f003511a80c8840d02411081600b80d800a010240c001500c10403114280c5c9001c82c0207000a8500e401c0200e105044100007a089822640310950142c01144210040240900000700f400c04541440b001d402e0458a0b2503505018034050424030ba42e0003c2d9074100507000f5060710704030410040041c040e910385807a000303460350000e11a0000e120305040d00411854020950550802180401003001c4500c1d81c0f10700e0003801026040c8030541c0410400031010079014049040b252444401c0540d485151005000d210040548090304201000d000e20115940210b21260803540041c3c05a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 808182 1250 806932 806941
    0x30c0406030c050408031207081509010b0c0c0301050408030f011a0406050f0408010c09150504080312060a08060108010204030512040501020a02041113090b04050a0207030203030f0c040308040303031b03060b0d0203 94
    0x360f0300d105542007050320344408180c01840d02400420181f01d144c0c3d560740c5040a48039148541c01ca443d02600745944076411f500140b01044d041300c0501800e0030b010341290b000902e58170210b406c43c0d406540aa5040354000108402489606840c9006007804c01e900403001000d8241050b25019034040d0b9810064006500036a2001c4a002e4078050b14083d0000c0000c0d0ba050b0300c000d4084005889820b0010a03110903d800b464040c0080d1000c40c2c182d08040d51400b1008421440824801486150b00a520000126502a080210301e010307040890005907a20304600b06030b40b6210070745ca203002c140c1500300030511a50342d012901c0b000c001e5040d81e01088181c02d0382503000c4a4090810f007800398107100c1c90001a041c41580021484400c00d45041145441b941484d0003139108201001d005130380b040000c1000100e5210029031b000c079819040904083d00c0369540310703413580240d0044d0000782d00c0c0c0c000d1600d5900368900e000095001c50038100510ba00c0c10902d2034290082500184c44e04d640400000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 809432 1250 808182 808187
    0x302030708030108030901090807060c02040902040905010606020d02011404030c0605090f01050a020a091a0708160206030a020403060b0306010e07050c010204050a030f03120b09010902090409020301050103110114030c0406030c 99
    0x403100c455100204944968540405a03502d4208040c040e0009080f0103000500401c0480c4a2007036404a5450f001d42040e82d40900014155001080741c005541e6108000130520a11550028250660140484a401d01c5009003514100380341455005d0307403441031000190f00810341c01c130100e90010011074140d036001c0156060040c441201003203942000200070068400d94018502d5039032540b01c610f01261641022019085058414001c0e80b808024081c042074200c8043c01130025102d50055101940d0740c0071a049801c03c0e620101c9050300403c4c14020011240640d00c039585042d0001d11503903250002500c000d040251954060040004005000320029011200688070150100c0d40950340ca24113154548880f10040c0d00040e92085012500c09950181c4400810020720f50816a4206040840254004102580d00650351101040143c400380107241c000c501401341c48880d050300000150030b056140b259103000440810030407000340d10702c074151019101c95203000030740030000280a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810682 1250 809432 809437
    0xb03030a140d0603051c02010509030301030807050307080703050405040501050105030402030c060d06050307080708011401060e0906040603020d050a05011a060403060b0d020303030901020904060501030204050603240d0803010503120307080f04030203 109
    0x1407480b070f41480c501106101c40018800280c450070700c80701e60309020b01c850881c2225416603614400c0d03001040100046007981001d400c04500483c241c81c81d224455403100300179400780c9002c502084020030104001d151620a8034010282820241d156180c164000394950207201107440c416000810b00300381c090504e030701110103410054200c1d4021a194005107545050510071466950300341102c58142882804000d8101d40407601c4804200c006075041010400c0010701d81600300f503540c4000000342e9501c40d85803020900441c0513298500e501d00b4050700b034074888061080c3c5c0c010f128803440e04035125141220b0499400c410b0000d4426441c01c0001c096040005010b0f6040c48003000b4402c0c500010340c002c0512a000712030401000da80d03080190240e001d203216149c0e0054003480080c07052000b001041d0030340000400340701521200c00002409c0865030f0702040c5e8107c4000f000511803401c0400001581f4940403039030a055181c406001022030000501114003480d00d0303004a030406008005 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811932 1250 810682 810697
    0xa020c01060b090405150a0b0304030203090a0303030c0801060504060c0b040f020405040c060806090c040e0714040602070306050c040305060403050a020c09070e0118080303060409050307060509070f090b03030a14 93
    0x240002503031502c101030250401d40109205620701000700310004400f805d40c240d002c001508800c4114a05031422080b07400003002a81940020014140f0690750078038010082c6100782c40c005031590300d2020080881005811030000e001c000c000031702501c0c3e009603501c6180c0d58040440d0460f0350343c40c43c0510101d5500c203402074100c0d09110501080003406410803060b42d4060750b03240103a40d149020880c9160f01a00c0040301258200410301c00000d003000f28640c80719107410891100100e050703110340183d10541c40140144c010351001c0c0100308080c065550405d40c181145401d00f400c5841c1c01d034a6400150008040c001c00062504c1307291700034070640f0a0141c0061812078180307032424001d44505082e90429000900140b0111008000382046500380c0d07000e00001c0d41180d5030501400002c01c0c48100540d424401030125000007031207401124422450784001d00300c2c5524044124514010a421440c0440d05158425859840020a0b183c2000d00b40c80d200c0e0310320080c1e400d03042c81c5104120 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 813182 1250 811932 811957
    0x90c030204030210050c0607050301030b060409030216030c091a06041517010e070305010504050f0103030e01051e040801050702030c060f040303090203010203100501080705040806040b040203030f040e0a0c0302070b0703050a02 99
    0x9003844e2040e00310025207110001501a9074240c0d580341c01c125034900c02400014901e20a107400b00b2060308007540025a214070078012141c9198005282c2c50580070140e204460185034014144a0b40b0a00d001e20219002d040d000985108074800000b80d050146d8003401e4054400d4040c0c00008520990020400b040415919205941c403080300800d00941110310902203400c010001643d800c0a1190310b1250b200300f400851a6421503804840e1002213417180e13810480c06106405a03e44200018100d5101d00b580d440e030386520b00340031103095810040a07401950000c0c003e5007104040401e42030b51103040f031a01c2e04001e17984c41c501074005102c008006505988080f04100b218980c2004003015920241c88002aa9803a80400c4079148280d000c0c0422a401080108001400c107140f980e4119100030192403d00400c0440190160455803090030081d00d030f1414840d110034680b0600781d444120740303815441e1140c1c40e1928000c1160140800302003540d24400101c400c51290b043c0c03880c141582 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 814432 1250 813182 813199
    0x8040b0c0a02030601060f05090f1201020c01060305061005010f08060102010603060603030203030a050f0c070b040807020603070f090e07050a0f0c050609030909060904020319080409090305030910050106020304090c0302040302 99
    0x3406590301d81d126412402885841c0000c91228004d18198400004a90760075180400140a00c02000c040c089456040b01101f107902907209020f00151042404407400040c025117982882031401c84040c2408118280c0d01700c082c4001c0c3d0340409046402e160b507042030003954441c200101d00403c05036001a000d240707030a401008065000c001940107100351101401152181c41e08400058420b42c3c0380407403910200030180c0007441c400e818940c814020325840f42040ca558021400715407044418000140340c0281c0581d010790401c0380300026042c9940880d0061401c144081e015128410120702070010842441404903c104070070760343d196200c01036404c0760502c4212640c1e01d0300700e6101c5034424401d280004035142003a54455216036001002844d00d8008100c04291800600f14151442c1c0010000403903842518000d40301003a100713036680c0341e403441c11404250070003007451190b101e45810a4010411117034000103607800d944035503d0000309401030703000540081c4100e5100a4000000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815682 1250 814432 814447
    0x80a0303050103050d02010b06090d0203030409050a06030b0702010506130504080d06030602030a0b060c070504091e050307021315030201050c01060305070906030c0503060408030c09061605010b03010b01090803030f0408040b 98
    0x68000c0c5040f40d202e0f00c2150350f150013000c0d00360f0a8502c090b50494004e64184080034642c5002e076184400280040e05891070f281c0c5130070700c0344251390301225160340c290b44540c81002000701c0510300399440034007840200281d0410000080701e00449104800070652204041802d01c505075003160f02c400c1c0c15140030040c3d29900d1400c107000e900121402003106d45044c4800a140c10428115030410b00000c1c090410f0a042c02c0c00c120041c000f403402a585020f80051301180c1840c402102c0f900c0c0f80c010001551550154410080d401c11000300c0c000b60241003e9009001c02c217043c0301d2800b9240c2c242080f80c1c59078500d40b440e42c01819140e0000e88688584400010303200340d141d00c580c041c2c80c051040e030041d0546031030516a17580000c0c2c4008180c1e480401c0001c14108108014000c03940000304854540025205200402d03c0b141c0001c0e90280d5440d17400d14002d140034411001a044203082c2611118905071403180c4030302006262414400b0004002000c0107801e4046901a104000301ca0307848400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 816932 1250 815682 815687
    0x60715050703060501030606020705010503010902031005030a110306010b07021c0201030b0604090b0f0904080d0c0507060606170a060602030403060b0301020c0105040506070f0203090f0607050703050d030b090a05010528080a03 99
    0x60b4403030f49011900d41f0030089426840815a03005840042e15658550303446d24074128020b40c1300404552001c04486004501a6001e0001c4020940508095a0041e4001040508001c0f040c6e1100e8207051040202100580b2090340040c06d0b074028484820701c4640900050780a049140f000903480480081c01207500d400d140d0090000450035140780180c8019141409408032041c1d40192010100303206a110045094102c203810f40414900181481207950319003040c1c441507006600410350146c40d00d03030f4034651669895404005c0030818000b191030403001039101e02c6203000c080c0a403621a080010992401d404907900580300900802c41480d0608000b521042c00741c6110b00002c00e40c0004500551001081c0d800c82c801c000c02d4481e07681148000c116995014180456950144403000400f00303000748281210809151400301e03400c3c0d92030b41000003a00d0001d00c903c001c0f40c03510005003c0c40d100c04038500304009207640100800d0f1300200c40000c4569559000e10300d1881420341c035500300356 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 818182 1250 816932 816941
    0x3100504060f08010e0a050601032402030c040e090703030503010603020d02070f03020304060f020105010609050907111203060a05120a030c0c030c0b0a0305010806060102120d0e07030501020a0206090303040b0105060715050703 99
    0x3c0009000b00003a440c2c0280d125292010804054040c0e80a140140041407030340405500041815054a10305913288042c6070a07a0000c80d10703c4030040c00460108086c64104203c568014802d0010f03045050440d94081c155000c18011281010703400b10f045451000942d048500309a007055101009444a00d0000d60345d034054014900017079400000480c016005006050596200e919030201d03150624040c800ea83d20000c102d90104140b544103011072070000d1007444d503d00d02044800b0f41da0b1910030180000c1d800302d40e114600410904040c81c0302d01a010801400440d414a043c00091003207007464141e20403940c10141842060203000500245d084c0001c00e0032140e192801d000e182c0c2d1700c00c2d085840720800c840750303800f42e0001c903203641982e40448000c0049040c104030005410400c0340000b450101c1ca03030011a9241c0d1300180c843c0342d2903010405617a00c504103030000c43c6140340550715090090030602c21329001e41c00126103402007080c958110b000c902159241004245440c610050180 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 819432 1250 818182 818189
    0x50304030303060501080108031801030209090405010501051507030504090f0905060c03010608010b04030206190519050301032d03050901020c13090b0105041a120a0c08070305060603030301060903060203100504060f 94
    0x2031808034000f130194001c0c03c0140c100da10800c051410100a120a002c151314542d180728105036007003010b40015540d004030075010758010000010a03604200c20310603520584502a02d1500043c020301000079844000c881c1075030151314002c81c103c3c10003801d220207860082002085e5002d01420810420744007800785040300c4103541d45407003d0341e842e081003d4604c101d020194000c10104a96115081c100200851048591400c80c0c0380406100f107140c488804a40700c1d00020700000b00400c10b128a041c03400705590704000c10300d9880034a804a010241400400083c140b00d00030680e01034aa0003407240d92000c000282a5581007515011001c00801c41a682100ca03603074203800103e031038100303445400400006401079002d040c62000801520724125010647c00d8450401982c0002e80c110901c8801094040002c00405085250043c100b042c000c0051317000b03a2080c401001600d500c0400b0f0005c41e0f070403400040c1c1d41d40f40c0f802c5038445451160072443d041800c185001481c2d242501c0030104a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 820682 1250 819432 819437
    0x5060a05010b040303050405060a09090218040b09060108010510030603050105011403010c0201050405060705070f020604080a03080717010611030c0106170c0102060606030402040b01090905090703030905010507050a14070302030102070503040303 107
    0x1503030300c8082d86800c030302544c0030140002d041031000303004500b02900140b101100c2418002d01881e614001c12050703921044040b2400c026803180102681000e0041190304801101c0480d03403031a184000a011503c144a468414141c201c07407e8000741c021780c0014040c540200c0240302541c6c55411200c003007165800000e02940c640319291151720310621500380541e50140180c0015207650b501100c0940040c2c0c02070f1002d00c200710401d40140d031440d0003000200501c4007c4c1400d0f01c03183c1005040121700410550034000c900700725005401000a0060540390281040a1b10401c02a941c51960084800300c0c00c140d0710313000c2c011451400132030740e201d41c00107520110713000358002400482c2c0303882050700d1007500320105001160052800741c00440d180310044c9800084240e0b110b2607401502c1d4103440362031150b00103410910034940d00039541405000c0a003002031610140b0358038141ea40e8803010029080d0300c8a0382d00d20032004006d0103802c00840d0000c0080d03440d4422828025166841803004401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821932 1250 820682 820691
    0x60c010204030b0f010e0709050402030903040503010f060303032007060203130f0b10060504050105030105040f0e03160209070305091b0111030703020609060105040603030207060c03030b060f0306010305091216020d0203030705060a 101
    0x2c41c941900800b1f803140450f9a01c800c40c0c140381030144000b94001030b2004106000a2001040c903440134426107014074100360340400c2c01482c4d405d000e012600c030360b58588200c0283c05400e00c80320300c0b886e040360b0003036a11601c010307036030756850440c48540303403884100400d802410101c2c0701c18486040e44950050100b40426581c940d55402c0544440c4034030311903540801e0050004000034549076100d0745031a01c20443c00b2940320382a41c2c100d802c660000c104ca00207400c1c1c2d84864010340c1002d0038030b07907031103c1d05003030406c018144640b12a1743c45440514080501d0b101c100080110b0740f05103400443c480c50b0804032603c0301e45034030f4040e4659000f1554000903106082c000220391030a405001c04481e016000b51402ca070515004030b1b010785c107210055060503103801d400f00c0a03864070401054011110b040c015181d08100c00010182e543c00b0b0440844c55200781c10100203220640115604007042c41036025840c5c0c12480402e400c510401c1e4080c0d4540004250700050000204120744141c035074050400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823182 1250 821932 821939
    0x9090304080c010521090a05010608010b1503040203010e0708010905010509010902060304080304050102120a02040501030507020105010b2a010c080103020907020703030207030809030a0203010c030b0102010b0409110609060c010204030b0f01 105
    0x554034059845400e45a6000204680c1554000c40003001c10103102c0070510140450407051000c3c106090302c140615520003600c9005103c0203102d000081e004010090284241842c00031b00b44071601042140c001030000081001c42d80c09500660700c9912060503140665944c0000354004c0000d19000d8607607509180015011142c18840d545200c0e80c010a03080c00c2d80c030341342c07114140c0d604010812982e540d400c002c001134003100151024072901c45030700056511810000010256040074022105580c1010010b0003185200000c0d204007040701e004420810307240c0e808445c00ea02c4c130400300840552a003020403ca0a51221825041e01d00a803032121090f220024100d80e40d944901c4047e0058001410134000940300000504035240c0c000c1c216081c160242d0000f9007100e80d03503070540c4046943c50401110a580a0069140a550803682040246290744a000c40d00e00280715540c0300d40d0001400604542c0d5080035034800300d134580b000319219600ca01d490308030b024040e5070b01803e4444000000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 824432 1250 823182 823201
    0x2040609080309030601031b1a0306120102120103021005070c090204030c05060a020606010318050d11010501050a050105090603060102010204030c0806040308010905090a03030b0a0503010c03020d0b0d080301060e0d0605090102030609 102
    0x141d50f280d001034002e00d0340780e2030f43d16400700c0031009000c2118501c480c0d820000d61400743c10304003030314440ca05080b6035803030400b10304201c0c01003001e5000780d800340d00602c4400c001c480d40640c103070b0440750180d90718190183e840404031424802c2603c014410205203401084503010350340030b0410b807403042d80307040c0c010740e00c600800644e0302400d00814010313842100060600d5100b900000901c46008020136020590342d59140d040c400d805d680803000580201382c5910140c000d028841c010002962102125818040000c10500c200c0e40720a004070000004030f50760340d100358101e40056800c1100907015070f031582003003522080c0540e02a00000d15040000c00c07603004a2080705e0003800120018103007541103580a801400c13070000802c0e8422107078a80020151401c1c05002c1004002e65801650740344e411360034a00f05c0d00c1d039060a07402203a44000ba0400160944200d9054880c1410708550310390b208030010700400750b61170009200c43d0420741444100703d015000b5602a600413034016485a4a45881 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 825682 1250 824432 824437
    0x40204050907050c0109080c01020703090906060c0209040503040e04030203040e07020102090603060d0203010f0f0b01030e03040501090605030901020d02040306050603100905060a0b01020a0204090b0108060109020310090e0c040906020406090803 107
    0x30240d01c9900ca201140c020750040008010000035200080341621064862a4a42d00304460404d0580d40025080d000c05034000c00ca00d014000c00502007080b5414000010840d031403d48000b0b00450001d004a411700004000b5900242080301c059125031038a0300e0f0007500e17600b06106078a01040d0020100702c0c5c02d4018004c0ea030706003034003030401400d680e68041008090003010b64266015541c4400086180ca480e02448100d40108800850403400000004048411203140c9155a401c188824042c5a9100d0f07807101c00c0b40d003140f130030984030b44910104a0081c0303c2c8101a402503480002d00108020070b0390007880c441c030011000e40f13120090505a80c02541c01c0003c0040c0603400500016040c0304003580b14011f940411704c1210040c9074164003160880d5080751080c2e42b505a5a001000001e00c00c010050140800362415030541c102000c07544090b060900400320a0ba840b810100341c81c150400503240c0e4000b00406c02e01c032228450503c0c4000b58400d010f8440060603aa50110b0b000c0000002c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 826932 1250 825682 825689
    0x9060203090603070c020609090a0204080c030c03030306010804020102150403020a06050105041503080c15040501050108060105030a050703061e05040b0108010b1002030904050601090b0304060501060e0f030d0e01030f06080705030c040204 104
    0xc2c55203140e8402e43c04842c488025402240c1c003660a01101180740c071559600c5100b15074a4000683e90350404c0300562a105007902c010748a5409000c008525407004070a498021100382009200f64882c0d10050741040c002e00d000d160507101b07480410081c1a80080c14144c1d1a018410070800350362140144025116030301460004032840010800c0000c110700000d08081c586d09040c4c2c1d0320400f800542c01d20201d01910182c40c40d030344400060000c0740742403081a00401e8110018904d009040c0c2d180b544400e650310000d000c550384c54491070320340daa10340d0f103186010303d4400040215291a14045401003000e0041000c550701c0c004405c1384504090324207408074010f81d0000c60900700e002c1c007000040c100062180e4100200c2c4c14002030b0341c54101010b10301640c030890012499604000000b4603881d0034400c00340c800c505210300c210a035100070a080c9040ca11620f400c07082c400c4120016800b0b01444403100452910b0101300003002e180218800054500172030540b0340c040b46450030001a80910301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828182 1250 826932 826939
    0x130906050f1201020405040f020408070801020901090e0601020a020d0305030403020606030606060d02090a0306021303110405100501080a0e0607020703030e0a0b0a0804050c090a02071a07020601150c0b010807060906020309 97
    0x10007a5814649104149103801c1d821002500d4140c0b40c1c0c0118003919440f5081d0340c02542c0124050002030001e000c00405020404021030801c21124002400400503101d2518000c007100003140107030f482440fa0908580d00948000c04030220b62074028500c1e40100c1e01640103000c0d407030110f0000c1c603000c5032660042800401443c106030b000d41e540ba000358000c05505d90b0242d096140000014041c1c00500540c111810111460309e1440c01c0078000a40c0c00101d59108030300c0c1c40204040e440510194409894080c80d200c030155440c0d1080c04002d01ea04504941c0c1ca22942040020f0940d0005031202a02e120342d440501501c2e41d4000e008003e0075600541c480d600040c009520003030f00c1118040c4d80a40503408803200d0340c00b1800419034503074054030700360940c64001800c002401070000c40d000b4403519101d88402c9034544098001d4940c00c0601442400d5900d0700307114281c180c8100b0030001180d40040d144019540e44201d80c0703640b400544281f2000c10b0062000160351400072090f142510b0016 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 829432 1250 828182 828199
    0x90405100303021b190f0f0803090604030609030509040e010507020c030316060c05070609030801050405060d0203060106050f0706050901020307020c03031207050a050c0322090b010507020405062413090605 90
    0x1154000304c00c2d01e8a401c58000710100e40c040a80c1030000750642c01040f080d262541034508100340d01502c10881d80180c070607075108100380d10283d158941160203d9400c8a00058400050300c0c00715001d1161581d4030358420b00704420840446410b41c007040c0140c038141c007250400c4c5428024941c40c0e0082c800c5e81040c0c020b048000b0404140c554002d103c8880c11843d2540c03411000b40d80d14030443d0b10041054001409980040c40300c0d042601c103c680003841140e820350059801d82c0080c0d952030050140b0030030031a02207200e501300c00c0381205580c0850351010040c000f03443c4c50040e05001b0f403c11254880140724003c4040a24113010040341c2d285240c0302c0c18803016589261013500c540c0d010b26242130803c1420807419804503000e0021346280354001107070350404c113003224518030403e01c50740211a8071440c0c22000141a03070024125100c10740d040c2c070041260f40d1500005402d0104198220750040d9101e11b100400342000001000f00701000b2070466001900c2d128800304540842c050150009200f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 830682 1250 829432 829453
    0x606110106050d080a090b0a0302040603050112050307030e01030b03010c020a0203060105010801080706050a021507020a050607030618050c070503040609210305090103050603010b100c020102010608030f07020105070614070509040510030302 105
    0x1c14000c0036a00d00a06258036007c0d41e4003e01c0302c0da0303488060004000790380401c061280c2a80760143e070f0b0040c007040c1e81010302c20039203858964591041c00740c02000c0c0501103a030310340242d021740c000b0182600c0c018000c00410001c1040a511610840c8040b0310900581c00041555802002150305903410700d0000c0841700c1c249507041c1e83c1540050b20305400e41c402c03005488180e0b201000102c0c400e0046034003400e041c607210700e00b040c90810050400741c14142401070500032a03813131740600306008a1003100820319441c1c040003031405219080c00a842404000b0f00800c1840e0800c0903601102e8180d01221060081d042070b04420404580c00100001c200300464407941d07129401007900800300400024130007030504005025000820400c80100303c800242405542c3c0a109000080c442140a10303e0510190218036240c815100024180040880c0c40c0040c80855030200d41c3c001c114020000a030b0500d108050310342e4100076005407040c0e0420b000105600b8145a80070100ca81c15001441c04011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 831932 1250 830682 830693
    0x1e0a08190201060302040906020904050609060603060409020105070209010303020606010906020c03030301050d15090302010b011101020310030b07110709020d0c02010b0f090901020c03030411040c0908060604020706060503030d0606110106050d 106
    0x10440e00e0840d0748444002c00960303614802e60803940c0c811980180d0f2503114806000a45a00500842c480c003840c104100c0c07c0c0d2652022139500480407600020382da00a072005959902a0250107500002c00200100c2010b40004603240551406d80700d00d505143e84080c101d90f02c000b00200c00c1e0b050b800600040101c0d04100695034121840780225000031050b4a0004040715031545090380140e4690402c0d804550308804003000d01d100a400962561804244592012100f8400101b0304d182190020b50150b2048258841891820381940c05461707440c04100041d421480c03180702c82c3c5181101d26800c050051007001110030015200007104a030b40020031110102c01005000d41c7d5400300b01e030500e21101800110f1003240315440382031940c0d8408080c041220059240780c0306000c48503200f48004500014800d81c480b1080303c0141c4d40b1001c51429501901c03d69014541500c070103c4c1e40b903000e2110b48c00032001e0725410b5442c080f014204004950a0354032510490707402094203240e0502058 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 833182 1250 831932 831967
    0x3130503060609100902030601031b080115050705070b0702030307050304030c0302090a021207080403050904020403050303010311030102030403050304200a030302030a030c0305060a030201030b04020906031312030b0f01030506030106030b01081e0a08 109
    0x1230305040c005524402c5120000000c00d004a9403000102440010320040460a0210700046001e00d081410903107159a05c0340e441000d030003251407080c1c000c01d0110842d5402c20458034450b0b400700940b40c0b91a0f481c070b01442c0c4040103000480c81000300d0380000d410b0003080e1007564061000b407440f40c0710a840b40c2000f0303612404050416003c000042004880d242c849000030f00045d44200e000319a01d40c55400d05012215170004800d01c01d0f4010414000440c1d40f0000f980d40240e00f00502c0c09102100c2c25103c03451901144109800c440d8608001007819008400b90401600c44d440c10b100d0304840040403000c40301c01710b0740b65a00c050015010700155220364000501c034140a80014a440314002c0010025041240d501e04284aa018000200003a1000d800f011541904040c40440d4051340001c0080a41c034000340e04050355080000c0c100e40e02500100003d41e00110007450b103503100c103035054540c141e85250340c4105035500340b00c1800c00e03400610501c00c10307042301c0b02509101c44c0725500728441 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 834432 1250 833182 833191
    0x40305090f03210d0f06060203040501120b090f01030302010c18120503040b0f0703020d020307080702090a090c0605090102010b0a050d080a020f030a0e090601050304020a140607050313050306060910090203 90
    0x500c510386052503114003e150300e0750104541e000458458246002d5034068440a1348110281400d000040000307a40020a035020344009080040c0c0010000045500502c0814100e41d84004c100040c0070028210441a6050f00c0c041c0e4003d0007501d100170420386400c0c1c001d045094201034101c00c10450614000c0c1c400314114071131800d40e40b6090b030301c81480b10707942c100e803490502000d00014107130105034040180046800c6180003940c03d0240c2602e40c0f190501a02e80c01a001322641000901d1880240d484007101d10b6000560128068540c44c0080154000003130103030240d03180900f41c120520b001c012880450700000c0414031040d10680e1072045035000240060258032a0010454504100344090055178080755110b1322a0100b00003000804003002d881241030107000c00070321000d80c95609400081c0c1e03080c410b00341c4511441c1d0340070401510480c000a840c81c0000f1640c60340807a041e40550080315030480864041d51210717030030049940010f5415403c41450741d00c08000d208240d80265520 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 835682 1250 834432 834439
    0x306020f07050109050c01020610030b0a0b0a0503010507030b040605150301031509021002032101080309011d0307030605040b010501030e0a11010e09010605030406140603100905010603060204030b01150206040305090f 95
    0x1884102d80e00d440c299101c64070102c9054021000705034103564108000f070f50220b142280e02c1407407840c40d1100020183c02074040406c040c0c40e018038691342e484000c80c607001094060000c1000c0c0c0307000d0324020700900d44240c65520a41c1480b00000b02c07444c1c17000703051a420000700c4200b89143d00c0c5644620f00c4148002d4054a42911035030280050303540c0f0003440d400b81e0358a80145594100003030001c1d4480700012518242021300742c0043c49000400410343e01201e10a007041c90b4001c9400c1140f0455900006103280d05104104010082021a8100038016445501580c041d070762141d005409540000c4064107160b807001880030301103059190090074171001810a074101000c041c0100c1e1041d8001d0304404082f400002c2030204001b41440361340014000071407003000f242401d00c002900c40c00c840e18240601a120594041400300c203501050086138412021980d8607035a282c04c080d240024440c84020000c081c800c040c000c0d0010541500c5180c1c15520b85190000702e8007005005403007001050782 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 836932 1250 835682 835687
    0x20d170a06090212010305010b030607090e0402010908030301080307031106011202011d04020307030b120d050409020a0509040c0c020307080601030b0103020603070512040819020304030803070302090613060305040201030b0f0a0306020f 103
    0xb490180c62004040c80c180070360000c2c009606504010b403e513460003032501e000760f01c50010410001c0d8480700c0e45040d46c074500d010348543d445034001200d5640c3c454002a2180c040000005201c1d1000802011480c2c801d403a15030341c01d000a05000d0700c881d0300f48a0245105840310701e2100640c890740000d0041c0032124101d511a801c41e002140c2260011246480401c1e40c030041020580361804282d0640c0785c0c40e0b8003c1404807030041703004209004620031804219000b01e152001c0c14007440903141c41c3c0202500401c00341551440007424200e8007841a402070058000120f07400c03c001c5182e42c103898000e00c4c0c201c42a442c55082c00007962000300030a003041000e000720002e01c1c0405542a01440c040c2d01d1003a12081085013000d00469081c00c02400d40d40200070400001e002c0e071056950245440c180161201c801002060306445504060041039a10240100e401501544201e000e28001e80e020058810b1040520076184508000c0c1030780801021802c00000d00c803600246244403031a00e8460 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 838182 1250 836932 836939
    0x90203010606020601320114070b0106020601031103010b030a020108090c120303010312110307080a090312030515010203040e0604050919060603030f0305060d020f010203041703070506071b061104050d030e0102010606020d170a06 100
    0x20b612b500a80282c40160042d5004005010130145d510600070750031002041100c0c180d000180d56805541e2000b4103210107000000c42c9108140001200ba04000d405600051140312950b5100c2d8001d000c120b820540c2101d00b5007000e8440e19002c103400744410002c0d890400c031515500b40c2a00020030103010000384940100025048412690601e28203840c0421142040c8440d00481c8540c8407105045500c2031004000c10505544a5a0404002e5800289079251320b8903242c01c20034041819040d61012100745010000c29500c9481120b003e6074a81e0360b1003502a0b412020b0f203005880a692082c03881c0b010402603c0c2400a002c80c14005004403480d0039034031902014204418002c080d110380001c0b8020701402802e11065510400c10b01d801102c042e940701c000c440c40312030f041003d00f80740d41c0d4642690f8100440012100501b00051081c034400b07403103180c001d04c0244c0e00301c3d8483c019400c2400000e04580001503a0001030616103a01090b0208a030010070038600050007444069101c0301e001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 839432 1250 838182 838193
    0x501060306020408100608010c020a110411030702150f070f080a0b0a08010b030601050402040302060412080c030d02030106031409030a050c01090204020403060504030f110604020603060409020301060602060132011407 95
    0x200000c01c0000c000d03041c3e04088038298411145203500c6680c0c40d9050401440a030317940803828862f0f4603030005414011044090220b030040100042c09941344c2400002d11980540010340c4494540c660766582450755101d07140c100145006071409004940220628a201d40c05006032951000c01503030001001440140055031820480c0e0081800741d64550644405007010720030309024100a1320154942407071640880c850340305611500040c1081c40115004010030070003261850003c41c422aa01e40718010701c910300a610a00ca0a00824074101182d0f8803030148104036031140031610041c60030720062230f13825102c0e42e1140050003915540c07030461800503034039031000d00701841c001c0e00001404d280030301e4040c202505038011042400300c821480d1501200c00158654041d50540782c281d160b072a003402240141450100c02913040d400c210020521a40c00078100c2c6c1200c45112041c10046100b2034407010000101100d50991032019201031410f5000f070022180b08910000c80c145054680d40300d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840682 1250 839432 839437
    0x30702030a0b091005060907050c100603030503062b030305060a050604080601080d050301080705010e0d0803040f0c09090201120504020105040312030b04050a0212040f0c0801090602030103021206060a0b0304050106030602 97
    0x4403007000050080c80034004080000d2200c080841e0020005c500740396002442425000300380c1c01c10860009841c0e0b011010511054244040da03030b00911003107499103009402c581089681ca400b0790000d002c011075402d8280c20028996201c0c000382c429008a544041340a882e006060a0b0860b409110008440d03c03050010710007060548090881941018143e504200c0304500c0c403400c0210900062002e05404141882220000d013424100c1c901048045608403111040240000740003008000c2804900c6104080151003149074032003142e25644031800315036140710080d0018416100020001c0c105500558200e030050400f07030704041d601c0d518404600740c070f1049840000e4407015001c0c442d04190203a02d4101c04400c80560801c030a29420645d61000140042d0a50381d9040611050100b00c012b000c0191a40c1c00090090243c1400c01901030361080c030040340291081e1008071602140442d019004d500b009140b04a1581342c859801910341014105450555036403500100280b210b200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 841932 1250 840682 840703
    0x80417010203040c0503070518041505070f030e01050712020c0705042901050a0807030b0a08030a05040303020709020304020303070210051603030501050315010305060105060c010603060216020901080102190302070503070203 98
    0x90b03070383d140074a42150049016400036010307134040b0b44144456034480705881500c0c9003048c0ea030041c07591603040c90400d50403541c28001c401c030b01d007500b402007445d80039499280c41503803134605010307c0300b0503050b079401c8070005c42d526000a20100c002405940c1142c008041c3ca448600c21154804c0e15400010202d50240241070b034000c03101440b0000111801008030000403090801038140b65112501800c0f8801c01003c0c001011b80d0f668400c911551444003c001420450040b04d0300c84007060400b03003155225002c21380140c0301c0c0550005185526008480c0300304e501801440c02d1640310390230302c0703e10610005c402c000d000050090807081c94885590060700b074082c0d81c0204055140c2014981060000c0c501c104e4521090030051001c6031000864604441c001d07101140d403440c9012130b43d8010012504010711190000400c0c10021003940310080f5214000c84002070703d6666400c48a00300e11916003d00d070310241d15454011620301a5000d890400d010f0003c1d03d1900c240707540000c0c144284d401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 843182 1250 841932 841979
    0x9010e010312030207050606060c19030302040603060812040506130306050a020406090e160f02030906030f0a05010605040303020c010c0201050403050609010501080105090106060914030a0503030106030e010b010302030408030a090804 102
    0x401c01e1000003080340b448014281411850178003d40c582603291070009007198018200000c050b21000c50030811241d040c1841054031500818501c2c000f0041d60062042d0000241003000124031000c010074000c10540221440d10724247c03811b028010180c00088103900d5804030301c0800000305203940150743c4030b60402100140d4442c10440c002c1c11015213600700948613032940e0100560792407005d02000d2400c01178104070100c0300307405204a2452003843c1c1002c1e00000080240101c1010400016000e6000010184441da132596812586c0d402240710240044e848051a10860750180340240b2403c0c2c0180340013450141c0f2911a503160000984545c64580e41d40c40040007500020f01c5101d40001002000703100151605000030507141c698051081e202c0c0880d15a082e0a50b030801445200c0d961100030740340c0320f69455001070010710140940c0801542042c0507000349603c288200ca1007107a0080c2c070385003541c48104001006180001c42180c070311100b0040424040b5003080030b0f0704201c6450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 844432 1250 843182 843209
    0x304030201031a090f060604050d0302150106020a030206010603020309030904090f062d0203060301140405060702060108030a120b010e0307080309010e0307060c0305070602040317070201030507080c03010510020c0901 95
    0x14400141241c0070f060309024012142c44030011140c4e0b5061205030000020310303010f46241c442000150741842203a210551025112480c1c20030190045a551001e002540f62100f05070b07602d40080c0e032100418274000f001a007081c401884014047d6000c1c1d900100c0c40012641420301160100781229100c003020346403800504480c40800c603c9005060714105840112002d08850030784842c0c200d040348900a000b550040300203840d6840035030085005014007409010300b414581031035522a00300307640341c0c40103004030000404c008030000100c400780495551100020007042400e03400800e654201181000840003944800307640030420940603241c850091503032810031900140c0700c13040c0042407d0182c0c000180800c07a8581004429031069050309003240d035040e241c5440d200070303c01d9410050110754031002014409180c4e80c060201d452003a01c2c104200e41310700b8400e8070801c07021a00004814010001800a0708142c00155065140d60044a0b031034028a40050080e0b00f0036003007408001c01a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 845682 1250 844432 844439
    0xa0303110c01020f0c101214010f060305160305040305070c030804090c03060503030702060f04090608070e0703020702150f070503030c03070320030103030c08041d040204050105030118020d03020102040503070303020304 96
    0x500001c540000c09000a02000039004035a0352210b111420185c444c0013000d00d0101c1c0d51303000356421030021b0850b080401c5095089030307600844440030b000d00340070301100c0800070034454007030300c103480c080d110180e071360143d204020360214040c02004004070108102440b4040000c2c02d0400d07080003940c420484144c44504001135101100d000001c203104040c1000000c1104e900c3c0441226003007901501d9440e518100b002141000344140c0d405541071919110000070074a501046143c26511100351484e560b0300c0e80c0300200c0a81c01203080c06540400211110100041194000c0c541c0c5d010100d2814101400c940b40c1d1410b680040380c101080500c000300700300140c1d82c14880c24400715403500d001c44c0c01c02c3d51170450071a20b0105000080034002981c010009000d005000d07500108111750b10041c80000a64486440305001e0782c00b00d014904181c0013140c0da02e018000d215000c0c0e20b07010150302e65103554003007084400f0f818109400b5550700708000315a0791000d11414001d58000d030015a80c8614 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 846932 1250 845682 845717
    0x4020306060102120301090509160b030105030610080303071d0607110f03030f0a05030702010204030b01030501091a06060702060f040906060c1703010b180102010609050703060806010807080c100309020a0303 91
    0x4001c040a0440d006412114111403035001940d0646412500c00201e9656111049150035410703107079003a100d00c02030700000d4041d1003100290305a0300301b40e05079815503c403041c4c1101d540c001d0340111041a007080c00001ca201e4441c0240c01d1b03903500400c2002940519240c0440c0090344010302c16030751250503100648150401000c0010b4040301900158940703070101d030401c0070b04d01031881d40100f00500000802c4142e4400d4050b0780141d0b82006c42129256900d2030038500038020b410049810000704510461110180300e16a441148003500300c5240161700c1e070801c000d507404041603403440c1c03c0234803000c40c1c0020513120341e0700549003e445c0c80d002800c1c00d09280d4130f00405150480800c580400044c00349826980070f9840810401039008802009000141c1c054035964024155191504042004860703058100d482215054010381c1d901d6602e40d41031035200d007481d01a41e00d2640c00b40321300036104c0c208441d800301d01926625000848031036039400100480b486074800d80000d40403a4003900c8040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 848182 1250 846932 846943
    0x705010e0c03060402090712110a02010b01090602070909060912020c011706010c03050304050312070306060e03030306060403080c0f0f0a03030b09060d0201030c05090306040c03030306050a0303090302090403030b0607030206040203 101
    0x603040c0c0010203108199800296807001d006000030300854004000c5042c45001f074035010392240603008140054482540088030780c2d04101d400800560820b4010003103540204801e03000d0384c030940e0240125505041c6c00b14054520808116030703581c2e90300c1203200840c04500c1c54000c0c040203503010b01076100d41c00e800109221340c1407103484080499003091140c40d03a04910506121075140c1401500c9a4660600900790300a442e4980f14031013003082008882035160780640c050710855142e0118120604043c5590790004840349074100d01304200500226154038068401c6011140440d4545c4200362a4075040c0300c49070080c402194043c4203d802019014052125100808c0da80c00c402490306c40300080d920107103804080d060682d10442141224030034412070350301e0600581252000e0800780380482c003a441d144402d6000900d0440045014a41503c01104807509a550404e4003070030b5400304500c20102034812070a265881c041341c905130300d807100a0041c0e50301035006800b10f85094010300d070802 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 849432 1250 848182 848201
    0x10030515070311040e040f020112050f090609010207030909090602040803070b06010e0d050c09040302010608070b030103021002030301050907050c030409050a020702090603010606050a0315080303090703030906020a02130c0c02090c070501 104
    0x1203d061000b409107002c030801c8984e00682100c422112403400d4001a074502c04201158410203083c481042280079540341900d000e551340000b264440c1c0d48158009081b4000d0080050000300220020007010f9666000114800d010741d03401031810ba560400d561442c3d200603011120034042500b000440e41e04030030311aa20381c200350383c03401e4202080e0b03031120b03210407400084600c91000070000c50140740c401d52209001c0c2c942030088800c907a4652005801d0b41d0001d200403403180e8130b00043c2c0406c10748040152070488074040d03c0c0790302d580c8170018145c5580d001039000301f41c0e510081c0000203002c1814040c0502070f400b080b0340187d036084180188404580b004001d603010307038142402080015072040440f0000e1006140009038a0848200b00f0102c0000c0d900200d20741c440401401105840030840d0011070744a070320313880c7c0800d559000980e1102810040690b00c151076460101c15160030350403844140d042c514113a140130943d580001c000017815695020081800328001c420000c09115882c100d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 850682 1250 849432 849461
    0xd0e0d080a060312030915020f04180c020703030507030203070b0106030e010e01050403020709020904020f0403060e060901060305030306060309030c0604031107060903021c03020a0501020309010515180103030305100305150703 99
    0x200c0c3c15511244005480790142d08201551440740f00c05011035084d402d180020810020740d41c42c0b0b1280741e02246a01303d40141011400840e0f03080380850810302c20f0500d0080d0740d40181c41242d18645042e201a04803a6054081d17000070403e602c0010040b2441c68080d1520b514001403c442e942c4115003194403540c50300f47d00e41c2c5000107100c00f103500000c2d034408031408400b0140c4c3d104082c9021a02a000c0e06404454640c00450040104195500f2081c6884c04000881d5140c1d921020001d003642c20621001d8055001040460080d040c07240040d42d00c0f04900d03017242d20b005a0820340614011080b5402d5000920300c02e0188a400c0043c8840c900801c502e2904d6241030342103800040000e400d00680f5040c000c000c01e8080101402442450605504180215280e00e0002d900740e0103403e00300d90b41c60a040701c001202c0c14614105040d0f9803140800d11120201c0d138250740e019030042801800e00007040c4540100000040c404100c034030b000300c203496004230680c201a100501520b40f2003801020 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 851932 1250 850682 850691
    0xb150309011407021b0405090a020405040501021206090411060306060403050a030c020a060906080a0b0d0203060403030902040c030903020a03030506040b03030a0306030b07020a030f03050408040f030b04051203060d020d080d0e0d080a 102
    0x71000300005850710902c5c400c980015140c2c90740c070241458180502c0c8001c3d0090b00f0242003105006040d8040c000d0020190410981a40c0c5c6a0400c901c82c001120001d0010f125004404000c0c101071000c0c0d0b50080b0007814407840c0c113840b502d4681c07802e91312070b8040300055403094007203045007810310700080144071a041004215085c44805420003000030200381c5440d5071a803411856944070b9429445c1a82c0140c140c40207402d140c14001d02421415000364000d0303003840341420380c1c01c0c8684603140e021609070380503040045495404801400d4081d05803940a034541a440349155014001010620010f440010312607103035240440b12440000c02071006c0d508084855004613402440c80c460407140391800184560b95480d0a8405001d07641200d0f105684101c00441041445180d181c004d41c0a01e04a4500c0825040b501d401c3d840200d0b180354020601c0f290304030040c05c03c0e2924841d050710528690b0704000342100c464048510556160a0baa40700400000c08907070495241504404010001d10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853182 1250 851932 851953
    0x103150c030b010e0d050a06060b0408010c05040f03080c0a0204050703020702010905030c030303011e0801050a0903020c030106030201121d030a0509090c0a0c0b06010c020307030b060103060608010302090a0b15030901140702 98
    0xd2200e131120382168041c2000044541c01c200062111003061035000008120b003503150b22505030950058062110203600c0d258409815501403c252021280d808941d080c00364110381e5030a0b482d03000100000b83c82c2c441c0845180045e659030149501c200e10075540140c0b981e02038000107080781200e0f44814020307005400c040a45071030110490341951612071000244002444d419100b904440d80011300c0f5501c1d000911a42003000d8000c01d24890017682103800051048003011300702c0c0e04a1100a001c83c414a661006101e1560400a100c10080400721410401c2c845400c1c01d41c6e2001d01048001000058800744618007401d01030b030496003a99a4500308120032102510b49142e012014169803410800203485030f00c2007810406455003d02540c0e9802d40d01d2501c04085c0d002904d01e0307408242070900220711540300b0390400e030480f90001c24a413a00d07124502007000402d0f1001c0120f0300110320084140144411074015401881518000500c41503200d410242d41d600180400046400c1800000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854432 1250 853182 853187
    0x3010806040201050a020a05010903020a0212031615060504060306060302030f03030103080909060a080a050106080f030702030304030f020a03080705030901020d140a030c02071206021305010c080f090a0e0103150c030b01 96
    0x465000341d084c00c206544409426059241c000d013500028003960a05170076408240d400b14070000b01c02c3c801d5031004072844150700d10f03940342d01800f6048c070301800040d045e40d404030f440401c148001400001d0005200d50310b030700c01300d07040d1001508140c513100e071034040400850030104905021840d030a80514219411035803181c0d113522580214602c00c0300c0034004101c56644004002005101d58012103103006214940b481c003a0109200f42c0f02680202046440d60080110486a9265000b000b1314549410349d82d46103c00341c0352100c140c0e0400141800840000d100c1030052184a02803802191660170740000280781c03484485585003080b410703242c0c0c2010141c41c0070a0715010401d038100400d550411200c100d1030304850f58042d80d402584074a058080c0852680200036450b80c43d0f03003100640b038640005440c03200342a42d004040f901d0802c000c00f01c4142c810094401700360000c1640140c50b0b62500750307040c0340f80c00381c10507641220513014040c0e088440c0d12038200307058508d040c20b200e00540040007 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 855682 1250 854432 854443
    0x302060706020d0b06030a1b03050610030f02040902030702070e070302070803010e0604090204021606060f050603010e10030f03030b0102010b0108060a15030f0c09080f120904020903030912031806030108 89
    0x81500d90003003035070f89100d2030681201d02c444101810242c0c49280922024002d01410911030449038002c0d0807031203c0718800d000c0d00c0d200306009403030001d4603400d82e4000c40c0100012140128100da082c00049290009030000314020304030b50340204405420035039040c00c141005400c0e8802d2620402c4558009035810302a03a0441d608490420b4446c4d40c0c180c085005040c419000079031080c80050b0300408a00307990042041c06000c1c44040000303549403012004001114020998071410a00040018600c00d40328954001c0000c1c01d500c041a82e00e80c1e81c41104c07415218111b000c41d0f11181504070550342403160106049091800341c0c00c504200003c40d0300d0600074000c007080010481a01600b0a009401541148506150410039000c0c40d40004140359014000c00c42c150064043c150402030700003c0d80302000d04030b0381046107000c1c040c00411009600c43c508403030301800b092240707400c1d90399044003409010b003521018564404403d86010210101524854807851080c4011b20214600095 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856932 1250 855682 855697
    0x1080c0a030206090301021603030509010605010e0d060203040201021606051c020702010905060a020705090a0203090105060904050c040b010e04020c0d03060803040308030609040602070b0c0403120507020906010c03030f110315010201020301030206 108
    0x15580d689184031400705c0d0191240b90500140061510100d00c03c01d44e250348070501c51170a200003000059107480044489224190020782d2010b4411014400714025600a5030050f105004498240b00781000c4103100208135440781d000720390085108488200c020800d02186204003004500c0c001c02c1c1c0e400600110854052603014440c0419441e10241c0200600005450300400c91005403074508036030b0010750300c1140d0382d880310350810021a840d820700c01c004a018a500c840a054408030402c00e007c0100703041c1e03120504200d218841003500303444a10040a10fa503032a4003a14074050b0501c005801d0712601d070300000182d40200030400225100000340c03a00120700711400318103512281032402c040e005041d40a81030810504c04e2043e0550403100a004070307485959020301d0007075491420740f0f40340030b40d00019401001da1400103107651702c64885a004140310341800103481c12031190400403503d2841c0c03040417111001040c0000a41c2c25050000c012400b480294a95815503010440e10b006492 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 858182 1250 856932 856939
    0x305031903060b07050109050f070e0a0207020102010b0d030c0308060603061e030102070501020a080103050c180103020108060d1506030b060402130605030406060b030403090e090111030c0f0408010608030405010801080c0a0302 99
    0x6000000040c440e03000b540081c038a0a1056440c1c80c203a0911500a22000e20201c950384a410b00a910306003002c01c17200111043c40c0d90030200380d40e40d004000003030360118000701e0465503a012803201d06c2d5629a50301c56082e00030b64946a0500c0985409032145c880604030360b20070f083c01c2c41040840d5030340404203a07010401c1580d0714a01c4400c5000709019002d0050000c1c00e07075001064452140381e000c00d1a504890080d01105c03c008000018400d0210030700020000d04e55403600140055401408a02e41140740509980d004000d1500c03208000f26810700c0e4001141e4507440c040050003c41d19070180c109104a600b145014105103803448040c41170301c81c03103040c042c0c0400040c2c00c0c0b1040b075106800600e040d1039011b81d2441c00740340081040c5403074018412072103448408240c4000052080100301d003541c4000e10b186865000046d038060300f0040d020800c1420070440440c003140e0070300a100013860a9130046444505040c0007428071401600071111550147e108a0b04c141d98406c444021643c064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 859432 1250 858182 858217
    0xa08090607050f06040501140c0901020304050d050c041e060801050c030106030e03040e040506060406080309090406020f090303041202010305091504110607120c03090602030c030f0c1c03020304060605040501030503 94
    0x5180c50b600300b450300b07540c94020b4061402000b0038080c041d00701c0207004000d0b00192805540e140c41040c1203014050985005910030b2106004074102480107101071400350044458240200d000101030310070300c4804400d1454000d40307084400c0003030700420b40034001c80002801140b411a5030001e450205100360340800d0b854840d024441c1d081031007103401810048650f10464070b01424200c0e950041a5030702c0d4015403900c1400203e500022003074401d03801008101c0040340d101e0f07842d80c2000c2d4020080c20101c441040003910070581e400c1000384000c2c403911132a58525940741c0005011120014400075560f0060101d01074078100665640e0b60083e0300c40c864144249011000c61001d00034542c1c020000d035107050031003150170b0700800f001b41614401c0e596034036155140c08040381c0340c1c080c40c41000d956a0090025000e1507203440701400408240800b1130710103890480504c45134071011007500d00866800410702090002501402001e0242668203009551441d55895a2481040d44000115565 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860682 1250 859432 859447
    0xa030317060d0803090705030601050d050a03030b130903020703050106060305040503030106030c0509300d0203090105030402040b09010b030411030304030b0f040204090b01060210150608010501050c070503010c05030103140a080906 101
    0x107400c800005950030036100f94680c03404078040390340c070900e60207614400c1c450b95000103100c2c03410740507a644c0303140c1c0a4060545055566401c3d8040e00340c0c05405a404000152231110407201c03881388a0040d0301076401080541d03d94103100d07086612a40109040504010030040451000000c80e8112202460002024071006804549034002c3d119250380c01b9110b0340484026040005503500b101c035480c0c41440001210900207a0340f4082c4c11140009a00248004a1958040c90241d42e0045c0080c00c080784003241c0d00c0015680103400d80185840e00c101100b40418004c1058004241c120180c00071072600c0c3c1540c40f00c4a9903c03004151a0340c0c688004001021500c80d50002071019610030034150741961a0700c4041d40703800301041082074480c41c040e8603911a191940c11602181e02d1a190b209244c0d0a10300111019030140c4041c0d0628410024000f40c251000d100322400c1e00e80c26901c480e10780d4114504a4600c66078209200d0581e4465403500e0081840601240c40e0014125143d42e0390310352 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 861932 1250 860682 860689
    0x10f0302040b030109020307020c030a0201120902030708010510060f0207050904020402031503011a0102150f04030f09031b090b040c020c0405060a03020a030503030603060f0106080105010302030a020d090c03020901050a03031706 100
    0x980e411926442d24040000178404c0140d401031409001a6000d8508100c90b401c14140d5030000400040c0c002070841e0180c0c94000c4003a40685841c030b00203004d5070619074540a2642c02d550007560250b5284200c07100806c10702c3c0d400b01602c0756840151000e401018640070003e84080000b030806449180c1c0040410000d80c2901d081c40c081c0c110180007072040ca41c034103507000398403030b51901c0840c0940558485030315296183c0c0c5883d40b09070144020305040b621161400c4603600403070300622080c1714031050040701042d001903681d040d0400201040909908004040c000d9820f05140030b4051800c05840000071900450351100039641500d000480b0360f1540001144c2001e141d00103504504070020100501c00d011005501c569001d034111507140c3c4640000c024400300900c612030014441c1001800998400e0700116040623681c94003500b0b01800400000c100c4020980803544900d6624013041181030940c1d0b410b0040908940039507203945151800380c0130202003071441074149010382c0091500e41c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 863182 1250 861932 861937
    0x40e0a11090d050604021003110f070303020708070b010302010e0915040b0303040f060c11090108030a0c0501020403061404030201050c03090304050105090d0606060504030506010504050105060a0302030601090503030a0f030e0109020609010f0302 107
    0x8010800c2c40260001e007449629098240c800b03a000d482c2030640c0414550082c06007100342500e40092030f00e01400049102500d40240404030f08240d020445d9202140c809006424058000c501201c07155240d40700150a032402c2c4041280135006100411240500000c0e001006100c1a42d01281c40205d0300c00203030640c800e94000e4501d40c2c042d9040850075a0744941d080b50f0203440307144c00c01005401c070000c1200d000307000d204007492039204211400e00c183c4a1100c030b05101d0b00c00d00c000750505481c0d07034a90090f100e1481101118007404002c11041c19824080c45d5009282d0283d201c1c070f036091104072181c4038404c070b00415041c41000100e1410135151404021900c80d0020010000540c581c200144a40c1c01403100b500e4038800c841c000325151074544581c234101d80005010b90300e0f004a00c2f0094000e034000410301d030f052291050000590342ca042c40100742034940b0f562901c109000814000e000c84a0030384600c400341e89400c141d003005031100821030380b88000909040700080c060010860191 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864432 1250 863182 863197
    0x615050604060e090109090206030105060d0e010504060b01080703050106020606010c020105040801020c0c1302040501050405010804050f01090602090307090902090f040c08100b0108060603062b080714070506040e0a11 95
    0x80081d0005805a00c03a00044500608652003080b80e6625500d41065607100400654021000c0004025070f01c0c28100401c50301c1070310000424100d10182d0300c5803c50740d00315805c2c0c801c603440329502c40c82b540e0b01c4480294408800d0070100300c90b50400000070340e10300c801031500b814007480345040ca00750f80c022000c3d20700804010713000799542d0707504480c0a81c40d541d96510300b501800a0300c00d10b00d0009090f000340c3c0c0a5030b806a488504051030500116868680a0010390380c5010300e1200f0a00b0750028010b014840c2e00910307025903030f8580c10040c1840d200103540300041c0c951400100b02e0050b40c40320300654114094284180f099140c07070600102402c0140e100e800780c2d10030303003110403070340c0c03803c1d81110104c103009880b07242c6503584d09001e01442d4402143c1c1994805200507100e1301c1f00c02c011600303044817104c440040003000b01c2680e4401d141c3d40068001d4490940301e00d200d0780050420013444014100a88446041510380034980004140140107164401d440d04d5043c00c1041400080d101c48 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865682 1250 864432 864439
    0x60302030604020f030a0902010905060307140d06030501020a180f080304030206030403031401030308070201050c090310090602090402040314010605060403030f0305070221030405060c0a020d08060310050103050d02010f05040b0103061505 104
    0x41b41807224805004040d8050203e001c5003800d40c00007054030741082521f01c207001c02d4803050b801e9140d8031506201503000305031081506544180100c0171500c02d202400e81c10703c6688451440d40c0403800311442134070303180d4440c5484103502082404840c20201c141c500b140e034161080c9460380c036145030580c081c040035507000d002c81401000000a041e44541150f0044400d50020031a64a80400c0c1c21074500c0348512183d05680441745494507002c4d60342c000090760713000358001800c0c8010080090180c0c1e000d81c0c000d84110502c0320315207070303502020310482c030084c58116000b51903c1c1c81c655021b010000d2400031807041c9541c40b400117805130300a000ea4490425101090310702d00440307a84c1000caa410545051383c45109040000c0c1d1044188000c80c0c070600c0181e0000d01030400c00c9a0300b1100000c0c0108a01c0c0c050080c030b80b20300501c1d8810702545029602c20009006c100d45880340003400c59002c0304107100001e042c036081c007010804c0d0b5021141526000349003c1100810701c491018211b01f1a44003913003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 866932 1250 865682 865687
    0x5060403050414060301030c12030908030a02030702030f0601050315041b031203050906070905120c0901080718050408070b130209040302010c02010b09010305070b0a021606030204060905010503090601060302030604020f 96
    0x10550700400030000d6801040b26105030b000c8001c1804028042404010708581c4000c809124030704144011a020520918007204925120125641981c00c407001d10710260303201280380011480d0510118003d21100c2c00107240942c50100003035901c1c822080c0340b50f030400420021905105110f040085a2404c0b00082d441140d600e00c2c0508240310301b50381c40000645480041144080d012820320700444440d1f55003003c003800c02040005034514420040b21038451130180c0303541d603140c0c0c03180b550003070003000043c2516900c4c1c24441094902030200340c2060178500003c020010310b4903003d0318507054104142651550306e0301244400188210400ba50107482c120800041640c150030503804642298024082c0c0442c0301e0900044240a01000300280c01640d014401c4580500c06006054018812110354200c0c0f861010f01d078820b25006072001070b400103401d00906c0c1e000103513075000300400c0c0b84c01c0d491454540c28890b16170340180a5801015000008a00656120b80564040c1c0f180544944e5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 868182 1250 866932 866941
    0x2090a09060b0307030e0105040b0402090603070e1006020f0d08070e0105070506040f0507090605010c06050402010e0603040503030f010b0a020307060902040204090e0309090a05040201020a0308040f06050406050f0606040b0706020310030506 105
    0x400e030340c10480f509130000b03041c00e118403121841800755a01581e071102410b001500d49a0810240c100d00134070075030701482410f000048861000c02198066004044039019247c1000802400c00e4070005400441d540940c80c030b158006d920001190f07111249207082a039141803400100c51700c1c85400c0004c0c009126020a020038842009038500b00c1520907400c40d0030180d62848100d0641e0810700c00e140c0441c006a00030702c0851003540016a00903c14941241c090384a00001009070f0030541301500c60303500c00b10420082c2200c0641560140005601d154144114144000d549104030440100b05644801c80903086466a0b0117031030241010040900940803030080d40c6a49804c0f080c1e1941c4580313102c201240e6402054490345001d550185d011345031841003602e0580e102d40c00540221400880324a102020601c50b2003454000e82c0324038808501803e080d88501005400030309160311801081100700440075a0380e00703c58000794003120240c0c803030392004459003420003141d00240541c0180350420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 869432 1250 868182 868199
    0x9020309030903070905010f09020702030109080301080f0c030a0803061306050307090209010212030402010e090403020309040c0801030302060f01060f030b030c0d050a0308010b03011202010e03010e07060801050a060302070b070302090a0906 105
    0x2c040c1d16000360120340089644498110503201c084c480c0c51201341e4507820600c11250300d5001032401600140020440310896a1041046da00c268451078980e00200100e20b5404801d104800310b4403021001480c1c1e041e02c5880c0d00d00a440003604030b520800080050058401030754110500078075000b01078031000756942407c0c0020358080041a40103005040c2c0202d54024081c003524085c6d901a036440ca9903d5482c418010260340c003400c15810b51006102050300c0e980c55020b030b00c25030021580c0e0048103501d50310f0040d240071310251001241c00901070040c080254442c080518045181c13030089905003155011070b06040f54000a9600441842491414042d000500d8002503102e0754600100c0c0c0c1c1c2e281c1c8a180c1c1c9001c2130141200001c100102140590f10a2059081c0315500900008078004c0c1552840e160000c2c0382d01c00408a42004010007080c40c018001800821280c00c0551401015a4494405090080c032150505601240c00d26080c1c9413031858002801801100b000a261200c400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870682 1250 869432 869437
    0x2040e060612010608060402060f07080a0306090c0201090302060c0d06030b0906090601050306070c0204050703020906070c050108090309030c040c090503030408070f05010e01020a030f0509030a031d0105040806040b0a060902030903 101
    0x660240a00c0c15100403184414132403101200e600c4c00140c4056200d0b642001070700d9005501c03022031000d007070000c030b0007007a00d400050400700321584000034a5450900524103440307401c4074032001c1d64504002000460b80100e403403035011004c02d16503940d82c501d421400c0001d0074950409806082e030784041000040001031081d0050050104440d0f0507a41c400405070b890388100d440000292111009600504007900441c0c2c02c82041c1c2001341c04d081108000c100c1d00d400444080d96480a40c51041005503000f03281d8076049030350700b0041c0d031420b900e40000c240e031a01d8401c0214007840d99802c0300c82d0f40c68030504101c000b8041c014282c0351749566806030180c0d030340e805002d0381040d00514900010700b0b42c02009044164001030f009440c10300c1d92520140c501a80c40503050080c4081000000c07410781d801e2202e40c207424132907181d040d00d0610304c00c0ca000c82204442403003818068100010306c2455000141680c0c003e50221008503190399640700720003e001143d024108150000c414000d0102c0040007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871932 1250 870682 870691
    0x705030d060909080f07030e0904121403010b0403020904080409090b07021207020a17160611070906050901180207020616150c05030a02070305070b010603020306090903070506010b070f02040e06 85
    0x1880442d40315180c0070215200d0240003481e151003008803030b0360310700110042d001d06402070801985880c40c0401180d07101c0c40444088816000c5400990700141c0c0282c040b44c494411064241d0641d03040c4400c0341001d1140f8000640308060b46400141008220002c4501130641c283c07042c0320300b25091400201443e4191680409030248221031900e6800c19019100840c2c3c00400000046107401d400000c80b5803502ca0f076a40c54051a07a00c2010f100344600c440c401070445030342e0100d0301d8420070f40e9942080003642040c0307035250400004100e541d540c146198159010a109c01000035400000e01c0d0080c8184000290001e42c0410140074046504041707072450340c01403100342c0c8894811103100c4111003800d0b16040c04a01d0500110300440002e40c050003031603201e400d0040c03411404da218100015000d9000070300081d000020401e03103007842074100c1c1e0000c100b00001c50829115a4889845003014041d20803076410102d4840c090002140c41c00e041c2580240003042409030703814009480b01411039 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873182 1250 871932 871957
    0x30606010c0f0602131a0903060402090402030c030d09140301020c1e0a1a010e0601050316080601050c0105010b0a020106081b0103090602040504090302010608010e0312060603040303020c0706020601050301060b0405060307080405030c03070503 106
    0xc01d0f9480b21101d03001160b1f808a00100030340702950300c80e4200b20b10034030003400583e058882c100c074100540e1800c1012241d0303040c01e51208100303d403501e00858010580c0200450085e401488100d0703d00d40c000544507035070b124464034080302c00f4120040030b10f0004040f001a119454002e480381c040c0c00030b0050a41070340d40000202c0c015a03101001503440ccd05c000d40d404845041c49941c40388000c0c1c4900031007504110145401c0c0e00e4214034034180742c251202070b00041c14a80d000200b92904940901c15400100507550150910b000401d224540701102528043c0c145900c030b25612082000f1135044402410000780308110104150900a000388247d010303101e599864000882c50000300001070780c40170b00c000034208007990b4500062059030781024000310b0606400b8441414541e13003d01c6a0000b03414280e004016039890002003509445550b40040030840d02004184030584454085940c01115403e0162982d141c92411301d00d144a24900400180004200d0800b080008402013010b0180113 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 874432 1250 873182 873209
    0x3190509010f09030305070b0403030e010c0302090a06020a150c030204030204020c0d0e040501050a171207260304030e060306010909020408010b01170108060105010f0e03010c05030106021605030606010c0f060213 93
    0x180c03810780303c4094034003000d00415800d200300000941600741c81b0340d01c6440382c48d01048080403080d01c2403d40307588443e40004607802050001c0301c0d052041d8660006c0410f48000d0000c0340c61525a0540c0710900700c501e00505031101c07842d62140d8000d40494004550103081150b86102248081d030300c94014a2122000864804080c51145014040d150585000a0010a0305c603d05442100c44907007000c40800c25000e42c80ba654000610341002d8070389180150468152600c0c843c1951300130550704811a144a0b500380180300210360b2200000d08142e45c142d030710035602c0e02c80400603580e00041c1c0d03210031500c90000401090164042d080491040c4080c0c8642000301d40101d521802c818090040410703c0c5e100b20010000d641c4202e00813940c41030035003000b41034540c5800200b17003510581000b04001ca200080100300c1580c0c1004600e80000410b18821721490a040001b0344030a40a00041c0c1000482c00b81c200501060344801c4001d030390721903401c668550301045401c5100b9000c1c8a2280c050300030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 875682 1250 874432 874457
    0x5070305060301090206090103020c0106120b0103020306070f020705010c0206070b010303020309010e0102010902030a0204091506060203091c03080c0a05130e010503070608040503040b03040c050301050702060406050601090b07080a020319050901 107
    0x1402410103042c5d0050a2905040030900114002d41010350420030303942d281c0100141c82508040748840e20fa01400000342d040d811801031615041014085108019400c0404c0303211a0307001c074090069907802d20740307100c60002c3d900010b0031500807550302810088100000108040c0c0020003014008800e0b214080d40c002c40200580c2200e6141c00c001c5d4050700403844c0d040042c58540c0c020401c00303200c2d400295088580403c07040481e20540c0000c0b016900000d02c00055140081e17544d000440c030014400c00201150390014800c036005440d07041070b104041904d090716030065003500d184602c4211460462640e031641c0c8041e00b01f007845102d0203070140c4803002c10114441d40400748030703540190080d803800b031030710202a00c0380c0e000034000c3e15180d8a80d2000305080c1c4c4c0a000700760190525a00828050a04c1e00b8580211140644a01c0c18000c0c8090304011100c50942030301c0d01c1c16085101c0c0354503003102c1041a07045100e800310324094000d01100c0c10007540e42240140c403c001c002c2c0d03644800c4002 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876932 1250 875682 875689
    0x807080c100c09080a0b09010905030a03020904050109050115080403020c040207060614030d08011205011d010b040501090203070c030c020d02030105100603050702030901050d09020102010e01060b0702030f150708090a02030601090507030506 105
    0x943d80074054194002c8454103000c1409025001c0c5c101d000b24000003494045034449a05507040f03001402c00080d0006007079441813401e0301a541c0507181840c0200043d525080c10810f40840b5441c004040c01403c03030000d014107009100f59284d801d80580195a04c210a12b40000140000c1c0a0041a0900e01182c007030a4100080c1080b030400a94880d10440e90030054001d512084013503080310559254207a04482880404400104615090011400c0f00701401000240c0310140c1040040600c1803080241c150f60000e100d0340280d402d41020000340c901e80c00820108004a14040e40560902e800e0001392114544002d040b201c2542c0d04010589a00000701d80340d03c0b034201c0060010f0710a20480a000200348d004d14205841400006840440d0724038440c20340304030313a202a0115401048150035400d080c40344540c0c81c4000c0e0003404050901c0c000c4003c0c4403002a041404200ca00800108440c41c02c2007030b00007442d0000c0403100903695407070f0b165000e02807c8034200300103801d00002c80e18905 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878182 1250 876932 876947
    0x203040503040303080903040503031201080105071805010e010c0203010207050307031106101413050f0105040c02030c061f03140604020109060305040506040602030c0f0705070603061208030109090807080c100c 92
    0x80d8000d001d1032409285131411a020240600300a03064001003000040c0c17582c080005182c8941400d11260542d85001ca0b21400c5600003000401809604503c02294003007640302c100954509091801c108064000101d0b1403a51500009415602c0014404140a070000280c550640b00e035441503420700e6206030035a11044143d9990b05424000c04061007a4a0341c00d41c440c2d04050f010340322050b510002d65952041c0c0e4030039521168490303080001881682003034000c012110070640000d514000c01500b815175a50700080000000380da1035034074846070b466502c01034001550441c0040504078101030034140c0b50442030703034200d003c103c022200292041c0a4013030507110703d030828054116a0340300e45401c0301a5000400866400c00108250204505103601a03c4064018002131040e00e050102c00f504548040e0450b00b001040c082004e00000d1241c07007182d05540c142c8c200401c141c1e8081c94912120300428200800301ca40110343d107010000001406110700d4403001081c4401d0741081d80c2680e800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879432 1250 878182 878191
    0x3050f12041206050a090501051006020601050604060e0906010c0507030503040e0f04080306010f020705120a020306070201050c0403030e0303090a09020702040506040606020a0308060d0c0b07050c03010c0509190504020414090a0203 101
    0x40c0c44802e10800456800d52000e94002203041002c075000c06159100c0382181c1e0204d80d14218451989800c0c04415410003030320340541800c1c0e4400d07140609240002c0d010b40e0940e10168802d030343d80800102541d12a4076115104c0e85e2010423203050030388a26115440b074201c0e00611891214403000524200760215049004035003184005155484810044a0301e0800c0c424000c00d5202d0081c00081c10b454540d40c1d40c9040700440b0141c41c203000c05e8410142440070191400046a0618040c411036841c801c00725000c49070b041c00d110700120688004241503001d1581d0442d032001401030002a40e4250360001c00c0300510890702003103a903848000700800c50f100380c005c000040c1d00ca6603481c0000b07409801040d0b0000c00041418201c58540e9075042a5074849401c80790328840701040010400030100a14116035a0440090141c0f281c1c2c4d010040c01d034050340d0f0f00d0071702c80c80901003801e54420000890300046c00f07000c0c0065544603242e415204200c3d1151404901840301d03940002c0400c10a4802e49014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 880682 1250 879432 879449
    0x10207030206030403031d070801060305010506030d021c0201061503060303030e01090c05010c020406170109030906030b01050706020307030b030604060b011209020a090209011b0b0402010305010503030304020a0303050c010e0703050f1204 104
    0xf99192520101c00500b003004060002414042c812141c0034070420403040101204000400c0d458190f290107400d490019003490f010307070700a440761103c0075008502c00145044840e12506aa03070a034108902409059016811104007848861a060340c9600300c1402d07a030007a10144840c0e40303010600c0d402c99400100160101100000c1070242f503110b0410145040e0004001003001500d8118820500c550400c2c202c13506e030b6581070500105074025204030010100c50504000b015000400a000e62064000003001701d6030000005020074000d610482d21030801070125091843d00c0d242c072100904504106c6400f0503038003161514403401e41d004503c03c19034080c228000c10780c580b00600010390003c203a00d40c1031103004c00410b9050780c0b032041819810342c00f50300c102c0140d0034240000b500310340041c0c0080c0c3c0680c004008120141e10341c040c000080b2541840c00655590400300c0c03c078014140f00c100c4003054001d040c030000c00e0000004c0d03032521814000c001d8a14100c140409a000c5106612403a0b54 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 881932 1250 880682 880687
    0xa05070b03060118080a11120709020d06030b0f07031a010203090f0102010b060a0302070c06030903050313020a08070605030901060602010b0a0b03070e06040305060a0501050f01020a0605040f0203060103150b010207030206 97
    0xc0010500080d6402c240c06042401c40800311104c500d2021800b174010380000e50203075200d6000e100c90b003090400d80000a03985454101c181500480d19132403940210024950001090b40c003002c10391348104015908070709900a141400d4136011a29001916080300080c2808844c070070f4540140d8503035880c03a41c140c004520700f0003a00b0600c440e240c10201058195503840c401d609454481000401d4498034503a0010303501c6030075207044510800c40350001c0c03041600d00a80e1400003a0003104aa412140030751a0302c010071070a1000642e0b400e8240c0104000c2d01a400c000190960802d01441c015a0042c00a10556448500481c00ca5550700c8611350300c2480d8000070029424001c0045402811500d805141c0007000310104204e075029500c22281a4480c4041094001c1c0d14859140075000450b20702995404050000b5a60540c2040290409648030081002c028100038a0b2200c9540941551000d41e900d04003114400b41080a100c50035081c1008081558804202a230603607600400c441e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883182 1250 881932 881939
    0x106020a030c1502030108030706061211060304050a05030c010207060e16030b09030408010213030b0709030305030a0b060d050a050105031501060504170c0d050102030114060403020609120a06020307080105010f020a0507 96
    0x450406103100700f61107025649149406900c624001107020340f20840042d5940c201c5450301c1402c40f41e241d403142070055440b50304240025844202d29840060854034180c90351a1410041d082003200740000300a4400020428030540040d0050110a03010340d40401c8464526902544c507003d0790a10710030009000001400010b24442d4202c1d089100e9070122420f094441d8805422a40094100111000402420410401c2c0550310a901a0041c41d00941d07051555070302510340d00015010000d91521010400f019031100d01c16920f425a004100344010b04101c40364900620007805071078000d0240c8102504c0c898410160141224025552145098a4194810300d20a00905a08500d004141a5852907510a410361403814094000103980b540342444084017403515040c800e014110601080000d0782ea205e09030351090a0075940401028000300c0b03818146504098002c283e1440072003440341c6e0076400800903040e40d2086c6c07601c1d60840491501640c2d54000c0c45001061030344441c0d42803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 884432 1250 883182 883187
    0x301030f0602070317010305060a050108030901080406020d090602040e01090c0504060e090406060302030f06100603200c0102070c0306090201030c030b06030411010e060a0e03060a0902030601060311070204020a0e030c010302030106020a03 104
    0x20304101e1300070300d0f28040e0f14544207118a41d01000b81d0013034900d503000000f80030343c4140c02d01c140c83c01000702c1d400841c50003a230b034000a000100d0080020b41b030f00e039001ca0034400c0e940903034015400340b580c002e01c115511600d0303d60001c0c100d0003c0c010b8050b03031032606200c00c09480c0242c08139029038095480708100c2a030398200704433030044002c0084400f9034940c0300001c01a1001c2065107420043d11016100c5854440f440303082035100c80c1c0c000010181460006a50002a4440c1e40802048240565a92556003a03014068400c04100a0541101c55000800c3c814a0b42c40b10320924070076682400074081e07a0200b1419902c1030300c031181d880001000424001500804440404c2506050183ca0103a0754000907480350040e0000e440820704800768030072075280a01083da449107060702d0402ca02442600400e40d07506050060364141a959218084070a480d001a580160383c001c2c0250340d00c150628009010445040c40729020344a500c4440d03030a5800382c025281070300c0c031581c000c00c1e2000e2aa2005c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885682 1250 884432 884437
    0x30304111c06020912010b0604030305070c0b030903040306060e0c03060d0303060305030f0903010e030a020303040b0a090c06030209040f0b090c0d0207050601170d09030c09110c0106031212020301030f0602 90
    0x800358000c030314900c1c0401d041c030541a6911002d008620058a070329210061022180c07840d0269095a45840d00e008200ea450a06440079660140b500c0780e100c185528041c542c8000d15044151040008400c2040703064000006105903845000c1c28812696140c809480700c0c44181c815050070182400020440d0611311401c4070741038064500400c95517601d44a003400c40d030000c4103040f4201d800180703e05640c00d0034040c0040d5a511080150320300000014000e45038000034100410503615000400d00f41c002c0c80d0040d0b08403d400c529011030081d0764200140c001d510640040d070140d4100551141d40c1400762043c80c07088a0003800c03d0b21030795103815019030294400c202054200c1d034207200c050042070b42045031318081c0022131680500d0144004600c0e25110307800006c03208109003c0014400101c603d0007035000c403401c030107000c10800c40204140320035024140c610401980f074940c0000a0203490440302c50350f5040c580700d65041e00c03072094000060f44401d00000c0c0c420700d00d02901c0700008000303500 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 886932 1250 885682 885713
    0x302011b02090c04140604030809040203250206040c0501080411010302090103090b0103050a0201031103070905010c030c060c020115050301020711060a0e0d060501030308070302030106020604020d020301060f0801050405010b1002030304 103
    0x4220382000e5940e03001864200301525802d40f400c0001c141030041a6a400e407407144000e00315800b03400c0c10f103035542d00c0c1240c0c810261883e0041e0b8000c004613440c61181080d400710150180180044100040750080d514041201c065031803001c00a000507207940510240d81c01150800012400607070050015400b079070048a800b8105903940c12102c0206500b0f17007280340a10b01c01d002905145a8138000102541c03200e400d03204115030100140320003941c001e5046000c50300b0a08201e84040300c04e050a0f91600601034014152070b00b8170040c80089581980703d81c0001c042ca6428510507511042410300701e003c0c44200405407803480b46082010b15010018007014420344c82c00498540940c00032843c503003180380b81115000d40f540014001c15070004002c590184480c40c04504640c5003280095942e400580040d0080d58800c225005646081d0003030f80150003c0850103030801d03a201d10321402031000311402d4172154038205e848512442c1400340c005c01010305d5401541182c8464888022540c144407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 888182 1250 886932 886967
    0x4030512040c08010207050c030607080106120506011403090105041209050105041e05030d0503040605010501030504020609090402010c050f0a020a0504090b0106051605060a0b01030e0f0607030905010e06040c0501140903030301030201 102
    0x1000090f1940240000c000c4d151040010b000550205400d162030028080c0080040c000400018407045601110402610301001004505da40360900180c9400801d09048080002c0000400a80001c15007081d40540c2c8103140c1c0b42400d030655030048546031480e0003818005442023104001038032000f03402070400e1502800c101100d40d581c1000030710f04910704402101140c800303c2003005000c49803280c0c03801020207003000d0080b0f240950005038a0301c5410b0340107210f40420030105003903900c6850310214441e404021580301e00c231041c2d84141d5480040c6801c03445111620340110341c3c0d040c607000d50303c40a60302c030030640300b03e9080c00300640b0f0582110b0603551140c0030110b00c000108504001c4103004a002000c001000c5218400060503910660750700c8a29920041c02078140c040c00140c0643e002c2460300e00052605101d25005014107091041404d5070302c220000d000070301464010784802c440c0d09032070b2400108600f4680706614001c1040046c0d040c1c20900040000d94000c40c0755030120112030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 889432 1250 888182 888203
    0x906040e0705090a0903020601060507020a05040507050d1103100812030609040201050d0204030803010e06010f0801060f090503060103060507080f01030b0103080304210804110307050603040602070206040806011202030d080403051204 102
    0x510200c2c041d00070448080790b2061716001060245a01170000c1400b422041c601503142c04080e80100e0001e0400d44030702c1d40520b42d12800542210710490594414400e402d00030322008030700c100003000d41d401c03c0d604500403100503800000e0000e00000d15101c00a201c4011a0541c0c1d542820090180310040099062010420010061024034030060010398414072007a84c030380d41481003c001c060304c0146024184072508015009580c3c02c803071814110791075842c0c1500540701c40081114004141e5101e1905803103803000120070800391380c010714880d081076680c031507007540e9401100b402008284800340541c0b20b00401031011038141c40c000c5502500030f036400050304a19100c4541c0765040d41050000040d101ca043c4000c202d141030f00281551801c5000f824451b04210000c1e00b14032014000070465580005c000c811500c0d440c06807401000c2040981c0e2843d07135039075020001306182510492080c014072000e440001d008041c402d0186425554031810031030712561070103452502510a4500036607a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 890682 1250 889432 889439
    0x3020c0607021606110604060f110409020405150313080706021903051608010609050103020c0a050d080403110303070806010305060102011517070b0a0c020105070809041104051e0906040e07 83
    0x30400303140141910740c01029003003011101a5003021183c0c0181c1c1c2041108040c18495480018855410070b4010ba40080d68207002c0d5050301c014031038002209110180030030000307105c4000fa800340044800c2a5021864103a09602240d040d00c070449075940140300d521410004100c46402402c00503120b000014900a09200740c9181c019908040b07100294a580c20064695000c0b1200389074240e290910303144950400001510500d61406803d04140d80030921541441c0f04005684020b6000301c2610000c00c40c0c05402400300d00c0840e810790103c0c1c108000c3e5844454001f0440317204245903944c0406a80b58140114041d2801401c5181107640f124106c07031020641203002c00c002c0000f599104100c8950809440c20030b405644074a5001405014840c00c094100c9903500e241a82441c10b41d0342c0f0390591070695054003412066036002807074003903a11008640c0700000d10aa600480e40c161a91050450420503640d100000ea07400100c2c507004902581082e0304403111a0512406448000d0388 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 891932 1250 890682 890707
    0x408130308040302010e040b0102030405010f020703120e010801060207060804030503040201030e01060801020315060306090105010e0a03060c050d060816030605090f01050c0306010f0801030c0303080403110303070201090506060303040e0c0a0302 107
    0x40380c00607611180c000030704004568000c07851170215201035809100705959500045d460340124440e19042c0b000d0844074001145c4244820009503600ca801400200c1405a0007800c59075078038462400f046850001155403400003a26104032450f82c0d5902646a85541d822a1503420180c0228185500c1d0bd00300808500c6c2030041801918081c0c0c0016180e01d07061121080140012400501032182007080c030410b91101c081480c19a1300a00380034182c00c03031510200344e45095651000d4025071034085244001ca501400500540f4001c4505105080d103803800182c0b501d0400e080741c0210301280c2e00400004809403c400d070f004c40e40b00b0030758990410f130155050958504440f603901e8002c00204000d104d6800c10766104510a440c40d15281a40c1503590f05105000b15010140c140058170700054109032054010360000700258080e2a128141100081e01a0001c040d0803038550142500040040c1000410b0f14102c84108000e00307410340b1070164054441d072040e5644c008154007040901e140b141c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893182 1250 891932 891967
    0x4030f0b0601080601030204031104050402030a0206070b0907090c0806040c110102070305070c1502030708090303090a03030804051005070903060f020f030f0f0a0203040206090f0a050306090a030201060b040b040b030408 96
    0x28054100c089091920301c00060048000910060500d0f10600041c80482c516100c0760280c13030300c01c4d140007903151220300001c0d140c5107007180029800f4400107008000c1025201300540104040d104903160542c4805000c0e00359800400c03000b0001d80714200007001c91400d030b00f0402415040741440da0324074440414482c2a40c0c0030381000c0d8040303400003445034200043c2089401c01004260f045038081c010303da400945a1003000800350440b48080303911102c40d9020310071a881503000414440580b5500e140141141d0b0044405680c0b90043c80121010a8903500036280f0956055903540e20392800c640d5410010107101d031200c00d181d98203200200e80c000d11180214020048017158441919081280001022000b0802611503006005000040e1203000a0f41c480110840c0d0311081041d141001c00c0c006205030780b00e2a454071070031061002c2c3e944081481c2101b64040d0380280992510303090140c90350712442c4608a00c07180200420400d0140400c051504940306618a900d01704800a0a5000d403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 894432 1250 893182 893213
    0x1a01090204050102060a0e070e07030209060403030305010305010507030506010905060c03040b0d06051903020607030804050309090c0a110a02090a0507021603060c090e060a050f04060503030c0109020405010b120a020a050403 98
    0x1540010180429130301040a1035111600d16024031525401e01846922220301e44102c0540441181c081006540260103803007060381c0250106d5103d035520b09004029100a200a590552030304021403c4584a030203040e1084a041e12940216850700c000e100c0e203075100c0c0c0b01c0c4c6e4100b800300b440040381e84400200201103091010f03002003a814103041c10040c1c005412102051000e00030303041000140c48031b4013a200740541500308585203640b0750170943d08620510642e1a804901c40082203480d04c58503000d041c0352040e41d40c03032194403803010340c415641c0d440d655000380d030004964000903035141c2d154020383d602440c144195043c06500101c450074190658004036910790f150030813500101c0c0c0c0010b00c113000b01040d84c510945130030214081018001c2d9030103614000d14071075800c5a1161583c2e040f14004040250440344c3d21204c3e00300c0e45000306246e80d001c9204605250001600c850400c090b40e89000c45080d507499141c42d0381c1e40e000000e5024540b00418400306020010110723038000603000f0704 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 895682 1250 894432 894449
    0x40603060504020108010803070b0604090c0b1201030311010e030d020304050703020904030c030201050a0b09060103090314040e01050f0102030c0d0c030c0b011d0901060807090504020a0b0c030c010b040b0603070305041a01 97
    0x75061903c009811450140c02000007680b0510080b008130748041c0b03060b504020706680004026446082c044004446904820441d020004008400101038900c81c0c0c101c1b40280d842e40040010b00007118240c0781d801044a0480c0e02c103101d0003040c8d205c00d42c0190740041c0300701e00716212213640e81c0c007003110360344115820340c04281224400003d0540a000b0658801070240b0200242c00304400012290303540078203601e0406036916114010180100205108903010310741140d290317035850084030038000090240f01c2c0501c207004950115540004151000e081500300984021800d4910888820132205001c2c0c04001c0d681c040b410200710440302c45406072501540402905505e4160030048843c05080a1400ea240c4907007001840c4000c2a4501a210f111002080359215400040c04454140c1c00c4000b811000044061068030000014445a00a00c0003404a05800c00130003040341e184000d40c0d5041402040081e0200d0321990141d540a03100306075141350045591440001010241c118404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896932 1250 895682 895691
    0xc0a05030a030c09060f110a061802011202040b07080f07060204030303050609060d0201020d120608030307020c010206091f050c0c0a05010203100b1303080f0c030705010605090a0905060105010503070e04060306 92
    0x71502e6140c010070b01580d9090600b480141d150030401410075058181a00401000d081580c900030002c1c070041000c0c80d00240c0511459801d51194682c00c2d40419040380410090701508107910094000d480c1120394402c01c1c681400119100d07484e1340d0340940300c1c4034540356080200000150325803000c0e10155000b0365002800b460018180000080c01404981c4200383d4641c1410048c0c3c0d0008016160380450700d08121045800703112000031703203e15000b60015000c003104000030280d0008030a07000c143c09a08550b1140c07100c00d09251900745852414011000d04541c4020f11600e07600020b0700182c913010818030744850002d2813410941d280d801254565000014412003013a21426400a4020400c10707901d051880b503815000320555100c020101040441c001060200d07200a8a0030100c2000c10341f036442000c1c1c50624000d140318040d2034412815840030840c00c5030940b240194070395203c0000d040990910006444d541c00050002081140503503c2c20865201c501411001b90311071035000c80c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 898182 1250 896932 896947
    0x504050106050405090307020a06030b01020f07030f060c080c040603020f090612010e0c090102060a0b01090b03040602030403020d0509010c0201030905100e07050a050105030f010306050603100e030a020708010c050403020f04020c0a0503 103
    0x2c142e44000d01780400b5540180700600c0580d941a4642c000c9036900e050008901800d400141e01b40310b4243e0300204140140f990000c1031110642c0c100310b9040c803c0c50104140404003e00380c602c80d1041da062080c0000c10700050001c24000c0c0d00405815075070480043c14510110005800d5038441090291803040d075100401c0340b11208642c1030f42007580038500909000150000035940d0b00c0080131300c250240c0782e1010310102d90013404143c02500b040481140d076480c0c2030030110702952040d2012001442900c25031411980300754155600140142d40b40c0c00001800d400450103840a0740707060300c542c01190358420030041a48141e103c10110b2002030801d1900d80b20400c9aa00556170066050240c10000c1012a4604580290550f940006c00183e40d071030b0200401d1034010450030f11454541b90040320b2402d04000005442e114402d0307400c4400e02500c07550414262401105810042142400700b8070062800001d105480a005440142001c0103500c40615101140405036464b800018000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899288 1106 898182 898189
    0x21060909050d0206060a030201080103020d1b0603150b030f0c030c040803070f02030d0903050d050d09020301140403170402030a020d050102090a0602010614041104060804020a030501050405010605 86
    0x2004610301600d40307a562410010868405032149400003003807442c100000c201601d84c1a03485c1700091b40395500340041145950f0b1300300e404040319017040c20041c8580e03112000801c282c3c1d174040f4212030034a07000302c4803c0094208200d401c1080080003441d070740d09107403aa040003a829109032f50b962080080c82da94011078000402c14080050300c00f06010107800c0007034106008a09484481448400541e00d04030300340b00042c01c540002d07440306000e42c0030344d01819448082c400301151030411540024210345285009024841d0050b06101c01c0c985d1140c2a9102c5607024454040035041030380010344e903204201c0009104039000459101080401e40507524103140c00f4081e035400c1910389a020f40a44443d000d2051445c281002c0016145828000c0c1e801d56051041c1440c40d02e402c03c01c0440b10000000c00580c1c02445000c40003000034801d1203894421405800002183d07801c00080 = true := by decide +kernel

theorem cover : BRFrame.Cov 719432 899288 := by
  have h0 := BRFrame.cov_init 719432
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 719432 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 719432 ≤ n) (h2 : n < 899288) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
