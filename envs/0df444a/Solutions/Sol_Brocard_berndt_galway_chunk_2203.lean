-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2203
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:58:37.567233+00:00
-- url     : https://prove2.me/submissions/4da8638a-6cf1-4a4e-94f2-79dbb21b534f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 396043165 ≤ n < 396223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 396044415 1250 396043165 396043181
    0x901090203042a150804051011041a0304060b01110c040b0f04050f070f11120c0c06030903031009050702030910030b12060f07020c092d0a09060c2118080a0f030609 72
    0x20026010081248a0341c40041010f030301c500c0c203274a6041c07101107050100b03803007040307400c1248030100c80c0c8038130f024504001595000d400172410003508541200301071000240f0548890011500802e07810600c00109038014038441400d5405810401402400c52000c541c5d58010034090752042b0308000407a4058450040e4611b10052540c800380c01540e02c0140000074005031211507003501e0024038443e001419640060b90200c20315040001444601c0c1c28001c03041c0010503d4000900c02172070800d40c007075128094010700f140036a022490321074410748264070012085100510030b00f4010040182c0c980d541200319080c1610804041c0400d003414000a032410b0301c0360009042010a03a20800722400300d5005124a500c90180200c1422640c20381d42c0001c1e00c140c206800000c5c22100c0e9081c80e9040d01d828004500a00007507841010398440700d0452007015120804e000304200000700000720120307800b080054180c044c042074103c6100c4d1b01c229107410507840307a60180066921a070480f07086503178071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 396045665 1250 396044415 396044423
    0x30c02030f0901140403020402030f15010216050f180c0919050a03171908090c09061003110706060b0901020d020111042601050702010b040c0503060901090203042a150804 75
    0x5000402d40e962190f01d00c07100701e105400c0e00900701030b545e902103026a00283d44018140080c0c900704504001e1301c503a40e0003414401d10090201c03402419403030101c01060b02401d801000e260660703000130b40b2824901c84411042e000c2020f01031522407844152030f00807180e62440381c40c02c17005c80e110034030162902505890008004c4980035155944070708100c1540c3c80440b5180c40d080c005520707408889110040d442c06241c039141e07158a041000340c0e040c9128450b1103446890181d05105071500c442f039001c504e00f01039050014109088444503030450007521801882d16042000204800e000d800103440070b611300ba001c840403c64070b050b099080c0c1c0e0441c00c010100400034070080200020340d10452101220003924140f00020291030b29003035600c11280c1c040542c0d1101010440c5081510400c200310006180c8a400c60500b580054840034042c03007407201031900070002c141803104c031800181502c101a440325403a13038280444464100e035030340706031130341c60140000e00e07001e140c002e40b0072511550344 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 396046915 1250 396045665 396045667
    0x1a0405090d030914032a012f160606060e0306040f0b041a0f04050f070503071406130306090b010b040308030a1d150906070c03020304061d04110307030c02030f 70
    0x10865046000301096001a5500418211002c06030a404d000500042c2e04690500c1c6e891701043c0c9aa500414184001c20350760381c50412900c000355030408a600c0d590300d400300841181d04011603075400d58080c81d5503840c1e00c02151243c9c07004001056020314102c58440c0c0300c42a40c804c01108160300c60008480c050304030122250500700181d074425810b030780030b449040070221400c1554880051440112608410400c11130240020321100708281c1c1c400b040400002d111190911010039141c0440344245a09500c8050101d02e85a4841c0103842c005480c000192500554074180100580950101580c05020180000c035015440301c01b282c0560790071401d500d1960f280d005551000340800601140c0c143c1515070340c81d41422050103120341400c04421120300306c0c104109050708140c4094485c4003404000281000001d0300802560f08440c0e09081520000e24504040200b140d00c4a94143c0c1c840d25200c000d1100c02c0000300694050902660108090303030400f00f007072703076248500c1d4156803407090 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 396048165 1250 396046915 396046933
    0x6090d0309051908040b0a0f110303010f0b0309030d02030f040614130b060a0b0d2702010903120e030706171023030a02030d0207060f02191103010e101a040509 70
    0x83c5808407140700708042c9103001e03910f035210321203a041001c441c00000c8040140a840d1603100c81d416a031103118001540c0f81d541342c681c400245e0741c1d280c17149040d2650040000b54440c030f02441914202055008192741c0ca16250704440c0c2c82d64002c88003169008d00e400b030b545107000d12000326244108010103006001c01060b40340c480300c030f0a00405e103d9103c0c511110105003880d5400180c0410074890710041409841401c0e20b00800c0c010b1143e0740040b00003c290b10015030f85c0303c2041c01c11030790400c50100c221030044900b2078400200102a9400d4440c8000000d000381d8004250b0f00314505141e4070821a8540002c11440c40f121341c810250744040b081d0ac030544e040c0c400242c807a00903000400701e44445041e5404a42000000317110140581c1088104208107a0030054030a244011071010300481c07088190000442041c40700060100e0f00800750300c691688003548000b85917040075048424400c0800b86e00000b400361141092014900e82c107410306030341000c0c0a0f031030080c20301d100501800c60b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 396049415 1250 396048165 396048193
    0x160503130213092015090f0a120c0302090a020c0a03140d11190c03051204033606030e101113090e070e04050c0d03090b040806090d030905 61
    0x3008444266400242000c0028101e1500d100e040c22036889110031004860070000c1111044080c8000380703029140c14100d152444182c00c0440341c6a4000f16080960341c014903000c2002d828080e003042d09404c5100d1048414015443c0184080741cac42241c83c060b00d40e8030301200d00144d004078001c1c0141e81c0c1c400001080083d0144000c02c02210100c00500d0078854003075440e600340d680343c0491084c2c1001c0000c4508200421069280c83e80e11182030500da2280b0a0b6002062032085d40c0948405917040c00100c0d040610031210b080756001d00c00c0444035402d0600c043c65551384000c90b8800f05d4000754881c0001e02500074040d4458141c030f80c6000d00412908000c211005c0c0c03101601e4842c0c2c01c1d1013045240c0700702e4881c8100001405030f003200020201401112076141404503081048140301400400001400000e08404c50f150b040c0c0e000d044080161400740c88094540e08045644100410003080340072002480074400d408040480f180c00b50882d00076000c1740d184240c05000e6800c05a4021102 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 396050665 1250 396049415 396049441
    0xc050c12030f0d0e010f0c090e0a060b0304060b0f03060705160c1e0e0f0408040b0702010207090507020a0308130f12050c240a15141504031a160503 65
    0x10000141c924000c00c40d5800d4601d07a000c4071800b0001c41c1d882e01d02c100994400d100d0b4010300801e801080080d00c0351480d018205a15911600390b20300d0040d000a050489150040300c001d001a121094aa040c903203000b8019050000b011405840c0da460303034080a20700009c0c03850280d8800d4031154034100900f4401644031061100c15240ca5088150004010717180c141d45031000602c0c0e0b41400486802c1c6410241d11035006446601501d00100c1403001050b6540704a50485804151480c8d5030031003440141d06003041070340700c442143d19181c00c0112294022410500281c400c0d0f5441e02070760317100e10000070f5100d295003001c0c21080344000c0c9d000018451070f030340e44820561414103d041441d4490b400c1d00d8221000c0250202d441050300c00e07842344814a1000e42c01002c00b000901808540300440c00100e001d9110f102c00c5000c004c1d001d41c078561109500d03401d8040c1e41c01140ba5941341c0ba800e000b005501400c51402c1c01803040340c001509022054500304c44600942d40e0b49140d0b454010b600041d07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 396051915 1250 396050665 396050689
    0xd0509010f0905030a031115090309040c1707080a1112060613030b0c070c171203130f0b04032c190924060c020a0e07110a080d0c0c050c 60
    0x30302c0160500414280e07000c10040001e2840f0b45d40301141c0101c4100550300349502820101004140c0200b44140304030040184c0f07840e0b04c03003658000340f08420144221401143d204100c54140030070406c2c03024265000000742d1003040041e109100302d190602d0982c00c1403141000035910f48207881d01181c51803420100401246850f603e10b00c2c80503403a921003d0741c0c0d085c01e4070704088481c0c00248900411041001c040020b0901200c00e0100c0e0090690540d00c0d540c5a00079680f60410000020700614140d1895034182d40d0000f000b110841d07a01e01d00300365640340981c1c098000c00c00c040503581140c0300c0c00303840e402c0c003040d10300452954232010310a1005800103902e032030203040c0c5200d40120750a03025115084030800c002400c2400c0c0c0f0b8120203000008410342d0030403c2000103148000b400368403030032051021281d490209810390354034009c0480b107100070784000007228010600d1003414008100c01816060313a00d40310402902e40c8244050f65940364804c00109035400402081c0424a440c03400000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 396053165 1250 396051915 396051917
    0x60403170c0123041203060608041b08100207060b040203040c030f061425020c01020a03050d020c07030f200901050f01030e010507020a05240f0903040306060b0306120d0509010f 78
    0x58040d141ca443c0030000c181c80d03000c40102d03c2010303040200b48149103000d100f5445041c02c0030042d5a0400c034004080200081015104140d80c400c550110169400208014041c450548080c81d01c65030082010b9030280034140e40e00713414101c200a40d403415108481c011580a1210202c0038034540c0e0358100b050400781c096404540c1d4007500100355660000051044505040c0c440d2046000b40455082400c1c540c9110219400741c070f04010684d03000655110107942609126407590b803c41c03d41000b034821902101560302410304000208000c8040d44000c0c540b0606840d4000e030320490714041030031070210440394001c6445004002c0c60501e0030281035050018980490944174a203070387c0d030a40e0816200b010040e8480e440305010701409005c0fa850392800c44000e080301e401d072a042c010300180050b02402a04e401040442c07440041082294011a4804400e000d841d03603a12896001e50800c032045401011000d0032213480000100d00d002c501001501c41c142000b8481c0c00460b4050100d0901c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 396054415 1250 396053165 396053171
    0x601020c10140d0e060702070b0a110a1203060e091603060b010e0a0e100b03040209071412040b100605091003020901090911090415030c060e130c08060a05060403170c01 74
    0x55110590040100f52802803d00041000b107403580c921450408001d25003c2107420000b400c2c0070340100542220100703100752604501c0410404001d50034400303c480018004c211346d2074003640054040c0c01850441c3e45000e000d00c03040e518a5001c0d44c481100d44040c002c4040c01c03000510000301c0c158030a520503001854094610708d207480200e00c640d5180d17041014240e131104200b03c03000c03804e100d0b0000a4010b0100283c2036050035408188005006002c403070602030031052003041c40010074140d07480540c00d00882d4016090038101410086000d0700c0c1040001072150011a0540c02181152402440600f425200303c003c0e41040f002508041002030411101040c00181480e0501a00102c8680318030040d80c2c03440c02d00100002c9070302030041600561805c071000c1002c070750700390310780002c031415414945c00c00340c4483e00150210b00b0002c1f82000700c600d4442150406540098002d2003075000791454049035807a0340400c01c9500071440f0013807044000c015200c8251425001415500d65404004 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 396055665 1250 396054415 396054437
    0x60b030a0b2412180d110f03070201090b16020303070303140f06011e110d0201050603160503070b250308060a05040501180f110415090902090a03060b12010c020304060809060601020c10 81
    0x900b002a245480b400241b84d600303040c6e000b01c4050015102c03650740000214644070840e030003c0e0800082c0d10440340d41c0c8e0004100d0a9000c003c145813000c3c0d00d90b0003010f590b9540b0051801a00401d02c116046a00c6008080081c10b403070300d1030a0542c010b0405856085440c4d190100121070200502d003800d0130403031449164401c0600c10000c5809815083c0c0022460349485018149440241451590160800c003420800c1e82c80c04542d076001e85001c202c500c0e40d250082421415a1841602200c070b00c0d01c4aa000d0905060340418402e00a110448100c001541d8440400c0141c41c030a010740d8044130f1010a1000b241440c0750300805402440440c0465010f5000e40005010b403c00e6100c003c4141212150b40140c69000c058040a0720481c90114207048146002c17400da00c2c03050100034809590342106481c3c5a441107484c403841c003000e5000b40081c054480f4001c0d2250094480d001c0031071b003120089000c5c1e04e40030410512884040e80144090400d44040000312483d40c4150800c3c84450882 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 396056915 1250 396055665 396055711
    0xa09020a06050d0e010501060f0c030203090607060605091f050409030216060305010602120c0601210b0a020a1805030a020906060d020a02010504030905190315060b030a0b2412 77
    0x200c030000c250310380b14a511105507540b640240e451401480c10641d00d0301005010641c0c002000011203191844d0411076818507160907071840c4295840242d101d0000700e824410090725801110a171001983c6200c000d849441048600c2407450009503000031808030b0610282c24250320142400f80284111032402c50000c40f921420626604207400094480e001440100d40400c01980401b06030a010340c549801c0b404103a8032140d06014901964034001008400082460807402e0100e4122681b0202c2d4100421254001c1d03014444040c0400c041041100c5a075050041f240100e84018000d0441070329030703900701701e081440100401d600000500664095120030310150650f41c0158000003407505060138082c203011401d9003e0b40c440c40d10004032240c504914950001100d030b0000900000c120407440b00f00c040c0103940c00c201d800580100400040c1505038104100a50060381c1501c0c031080399041072410340d00400980c4100c6441000900140c80403020243e40c402101d230680c403030110880007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 396058165 1250 396056915 396056929
    0x6040b150d060e010c0917030703030c1e03060602071a0301030f020d080c0c01080f01150804030e0d0b150f030601061805090106051309060501120902060f0301030f0506150906090a0902 81
    0x45050f40c180e40d00e071131140d24075400040c4107015010700d220103880c40d41d00341c980d242c0d28072500748001e04040c0c5902031104041d0203038041d10000703a04a002e00000a81190700140208880d124800051140060018090b8250540e440010f200083c40354516030940d1a80864407089000480e0040c2411035a200131a11071030151240d60202c1c0050700b8204501c00004100385409072410340c2107100c040c0100040100442500000c00450400c0d04036540c07241800e540c2c0071f180301c0800750003801a0a03150300f0081c02e103103500c0c8140420071034080380c846ca0500384103180070100200f40c0c01d43d10000040c00001e00801d860801c281c4d144908440c802d4580d400300383d07014800e0f801180400c44c0030400b14844040d00000d400540002ea030308000f400d10b00800282442e0300c201c9840f480035690548102903451742004c4486400324034000d07540d00c0d6500c0c504000a81c0140005841030b010b406c011a104c0c1d2025024480f1000c0000c02880f150740b1403c2c1000b070240c4014205007903d42e40d814110b001030700c0e111 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 396059415 1250 396058165 396058181
    0x80f0a0c0c123302034b06100305071404080106090e01060e01030b100503192108012105030f070302070905060f090a0e0a0809011706150307090819021206040b150d06 73
    0x18450881030940d001607403a41159141946c00e5429020070030241d07481d0ba5600004a0000d841e002c121520b45290a6441d12140390f02e206606000281c042428001504072034101d402e0000100b003040080e00b0400d080b640180200040c24501d0750041000c00c03e101c2c411a00250100303503c80d1400c0c0d583c00060701d820405540c500d80c4614a06080341481a003180c003003040303010401d41186110113124018001041401103d0004002000c2600068000724071100f41503413010441c1d64031282e5001c40281c582120004500611407071001003680030b91750140c21300488010381034041d4440200d04000100f40300422105e04666a0060030b003070340a0400040c41a280a250101c0e580d40300c5030001071103050003a00280040b5440814806284c460700160b00b1142640c030300306500c0b500e0b4080c08403080807690344210340740d01c5a07890319510541445801c900c80b5108450040364008c12100c2943c030f0740b03000c40c1c01905015140000540074041510368020040c1c004000780c0c407900b0140e80d40c90440300340e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 396060665 1250 396059415 396059491
    0x70e0406060e06030a151d07030c0b1809040201030e010c08010f05180a0b0316240f020303040f08130311040e010603080f0a0c0c12330203 61
    0x10005010900005100c0d0001030040740000a65034600301000c2592240b18200007004a820281342c00b025030340e01d40c4040000e01c6000729903503008044d0852103503540410301003a40c0c2d610b03030700200240038052a800c845651402d031640403e0308001c8420844881802401039040c1078580c1d0529036081000e1080c8601c6a009442c0d0a8403075052019800c07400b000f6402882c0034141ca07804504980c80008480c0d54454660354004c0ba00a00c07003c04070741458100e03d0701c00e100a402c00004904181050b03140131405200c00700c81d03880b00c448500111407020901c603030100540c004001041c040780c5110200c001003070288100c1c80c0350a50005040c22020a158400d44003601c00300c186070030f58502401541034503141c000c02405001d0968581c00c00501c1101030b245d410003000200c0c0d40e9490700481140020540240303a44142540c2c8001c0c0c0c200800c0c10300301c202c1e0b240350711912109030100015980181c1d4280d000c01514500201c2c05582d00075030004d007151180c1461a99410544410802d2040c04000d00b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 396061915 1250 396060665 396060689
    0x20306071d0d050d030b031906090c0803032503051006120e03030a15050411040501050d0e01111b1f090503091905011202030402150706020d090305180f030307121107 73
    0x1079440040480c2d0040c050709109030011044d844841d148c1480c144e001c8d5130130400002c2c4a020b5803801468100380355000007881d0102008003c1d212030030b00000906100e044060101102840404078100c0700102c9a05170302d0b4a46174000d00c921071180d006145401c242c101c00243d0201d01c401801e14541003159488001601c8508882c841d2210501200080000f914140b0103441002003e40103030149001d0f07241003010205043e0054a4507400c8a01070010203070007000981c924144220595000044e4078043c0d5049460041880c480081c9110002e44401c0c203000716042e000103240040d007400c0c0400c0c0c1d160f10050102d03078069a12242c0708a040061002c58100451826001400f1041014100d4110b18410b00c1040090b860b2102e90140d60020030074425504c45c4a4074100c0024010b1882c00181d11f4504400c050801d03402800910080f910400b065010456140802160b400a115941d03050340080c0141c00001d000074080d24204090350a054550001540c1014a0000e01e81e01081403007071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 396063165 1250 396061915 396061933
    0x212070c030803090a0f112e03181202101113030305130e0c03090d0906080606251115040602151005030d050304110108071b080412050c04050112020306071d0d05 71
    0x40d028419500b010002c3d031143e5141508c1a00038182c00e92003460b10802e0580740c860454500c0515041c01030215440744640303000d144032810095491004190150040d45003010020b8455000e42c25501c1034680d081c0440780060940c0d40c1203400d81c00c030094480200c2003040300481e84064a4214600c10b804d64410340c0d4403031030240691450b00c220040b814041c4221414180852070340083c40c41e80c050025540c06030390710101c50050600728075101341c0d8900b8200843c080c0c0200b2001c1c0380d6010020004540002007145889080c9140388641d03c912409031b80001a803064511014107010390041441e001041400d41c2d48012a00340028111750400080000003080100442c10200f003420b0700081c83c06002502e0700e500050001c40304003010070700d0801501c80d09000c103e0800103d8020380108411680d400c0b4081c90311030381da10f90207074400d4412030401c40081b0b10000039600e0a90307155001801840b23142c4070200c0645500d5488610a83c51149103c24407000d61949074212104074450310003007903010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 396064415 1250 396063165 396063169
    0x9111003020d05150a03030804020315010905070e030d0c02041107020d030f0207120b040201051b07060c06141e090712150b03070803030a0f09170a0212070c030803090a0f11 76
    0x3e10040c51a035141115411070580350f140d860420069075894101032609895030300003e80b5010705040560101d28110300040382c40390309038003d40e0183c0f48030b4890b461041c04900c200754491115070001000546000e22030b0001d4a80350f00101c0c400e5014888a52920110381c020402e16052080306070003141a1817240c01c080d9904200c0840200440300d842c14081c2da0701d50f01c820103580b0280000c1d04022001c0b500c1d4080e03035200030500c4001d404c040212100d484e80e9510290042c0c04001c070950316246005030035561031241242807441200e0102450301200d00104030f4416081c006081440c451007928070202d450080d985040c0c0b40030340110704030070304082c600809406507540088100c0c025041000100003807240041a01d4200035200c5000c54000c800000384002024200c0700501403080701d074040604100007000404044603164280c0d20f40001c5c410345c40304c061040c1351000f84449000c100410111b903190340950f41080100003640d6400c0801c0d2680c6100c00e0200109860296411008501da4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 396065665 1250 396064415 396064421
    0x16020901090e0c0603090c0a0f1707050306012105010606030504060b0402190e0f13090c050111030f0f070605040c0602210403060b010c0b010e0709050607050c010309111003020d 78
    0x10590755606015540350b111910f511810080102c0d8019a004000f18803014401e0002c03c1030880003800207000207070340e402e035407520116034072800703d140c1c0c450720042590705004190b0405496001e4010611a46031250f586015180c01110341c070b00c030001c3c1042c140020350a000d60002000f5603a8081070714101070925000300c460b035155040c4980d10402c8003820303180040d18011040b088504040c1035458126010800d5140b41102071030b07000900c224400842080c0303501c510842401581d80380940f68880005481d0f440c5120500b000310f900034404921350144c944010b10341c40e030304002c100341030210303076a01c2c4419508166000c46640b00b42c1c4406100d080d904100c4203c5180c0b00000d1008450440c58080c0107510940c0030144c0b86907110015610664001d0506100c82c0783c3c0150440965a501c80055406400a4401f88009045020000b07098503002c42903400180e0054060003025102400550081c041c840040b2904880d68003038cc1d05039030b241c000140c0e012003a030720b0140e03484450943c2c040407 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 396066915 1250 396065665 396065669
    0xa110309030a0f0e10140c0f0a050c040e030f031909140114070905040f0902060307050c0708060705121306060b0c06010e01030804030f1e060614040e10150b16020901 73
    0xc0005009890404c0c0e81c4540200b6182a05030500440668041c000380900c0d1007081040708091007400d0a2040c0c250303001404a59180c0680280d4011504141c200710035600a2a03240300d590380207120f000b114421460045400544c01d02c0c40c081807200200c01402a10720701c01c8140c6144684010300001480203000e41c200ba03100b81c1100182e02e244c54034010301390313104500803180107a035154040103001149a0010b420b95400412031070b101c0c5012100104140d01c103428016140c01400e00c001280c0030000766550242d0700c10384490b810308052000d01156500000c02108001030307119011340210341c0300c1c440d01d0302500305000500e03521202195003901c0c240040e4400a21885140010404588135000361019a03500100c24410240030707080408440342d84080c080540c48480c96981c01304030740e50b84220122070038000f2440503019088204800c50703070310101109079070308406190002e1403010f60018a235400305810790780e004c90721246500c55980244440d804050382c1ca460901c01d600e072000700140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 396068165 1250 396066915 396066917
    0x6070903031707120902030111041410080912091f051806091305090307060e0105060f1c061805030409060801060f0609031704080a050606100e09010b030a110309030a0f 74
    0x9250038030f403400a00110b0032101a1040326038500040085641c2900002410741da20f141003511662101001941c0304603040a81d03104800d0005545203141c02402c1c86846005050080c11005400300c1c50483c260703101c220410b511450f880d030403107100c0c03405400c480e14400c21a91206d4590100c940c0b21b0441004601c00948520010310200e4029a61152000389035000c0042c0401d4a450f8290303510300d50300030400c00810b158208445029403c1c01540000d115603021640b0f00b06400402050045200d500b40d005042c0380c42c1d0350503c0012400d603402052848070300c03400030404100c082e200c1c1400c1d030300645c100742d02450711450b041250881c24001d800140c4401800b1660b01ca01c2c0c100b0161080c00c01c4d200003015500518001c000031200501941c6c0201aa03006403070030810f26140c05a1070315801ca0b892803050314140d5003101c1041c883d590460802d0000b504040240e42001c0c000c01164000030482c00381507440e541070990440c1c0749000355001d01c2c2003900a40e164079402901038404014256000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 396069415 1250 396068165 396068207
    0x618050d020d0e03030f0a0e1018090903050d0c090902070813060f051806040504060b19090f050f061605060114041b08040c080f1f02030c0403150204080607090303 72
    0x400c0c1681e0200444815009070306c00b080e030f1002002c600fa40e42202c00b811807680010756080150f1101d80104500035680400d00c010310340b840e220501002103400f40c100160014405100913030b624003c03030307011980d20002c80c100304030aa035132603250b5010f07a4030010301240d4490300442c0c2d43d00600c560842182c0038081d24207000d00c445076519030081007801070a0f1910800c445d02040c1010302d440702c1e17044030701406016000b0b00c060313a1544007540c10783d0300818214411100400320102807034419000c000c1500d90420b0059042464002000300c403000c160001a0f000c4410030003040001c00740b0440381403151141d40540034940c503007565403040c0c0c4e0200c015039000f94107024a109844140d404418406c1e285814000c0d2584c070742d410f04c45200b480a400c1512903225908103011450390001d40e881000c114960f0040a103003507800c0560a900060f265100740450600c01031001540b01e18004021038a4070000605055940c01c0c401e137400300c2901c01c0740103e0041c4805200381680302078003408911804243d5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 396070665 1250 396069415 396069437
    0x3022d06090703080f070f020d2307081b04020d0501090605011b02030604060e030909150307090b0604090c1b2306240d060212090d0c08030103020d0618050d020d 71
    0x3c01451044400754582100001b410004002d10008120b6503a60080c2c804a003001c01407030036039030a520b11400b1504513011041e603800041c0700000c2c81000d07204500040c154030461408802061202000e41a0748150240309084d18000c0c14460b50380202055000841c20030b1405002621044603415641800302e0b460f9031240140e10000703809500141c0c0140001001a60b0315125410741c00b4805655074416500401d2055009803091100c0311590101c040d01e15581d070340c0708103c0441d407a545032141c002178280710070024804140e004890401d414146002150120342c80b2007071124041808503995140004841440f400c40079100c039603030ba004d400070039007400d04920b000309803420a1080c4102c1e0704801c00c000080d48603203c0c0d40030310b81d034007401c00d545070384084a80524041007140c010003644035001010b80c64600c510421741055401603c400c1ca56401c5800340090201e41c0c1209943e41c90f00e0f50321404030041506429003070a070240c00500806034003c80c0003401c0401c0c05080d00100041c100d04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 396071915 1250 396070665 396070673
    0x6010f05030f060d0f0f1707051506030a15060608070507020f0904080c10060317031b0702031507050d0b0307060906110c1005120a060b030106030903022d06090703 72
    0x100d0b40c2001d0044800b509075030310038001072032003162140000e0261038010348590070404001e40c10803800c3d100d90380c2c00b40200100d0040e99124000c4440103070081c3c8c80030124480c0701507045100ba8000d0805001c1c0c4150205503142c401025004102d6003240c1030361080b04010903076101d10b115420181e2442c04501e40f0420360005900804880022031041060f03101113020400c1010403034030154441000c0e5032100c4940c0362440c000300300d144020f5414006588980b407021110b441240c3c45048688454054801c800d03400255641000c0030481e0507100c1c2c80e801404070707000514507030721607400d99550582c0c4000344039500003500e45a482c0a4000d500ca5003042c8200b60300300038040700351000c2e8500480450700741c0300b49038a844240850316410040d1481c1e17072010503038004000e0016000501c03103c0d40310307100c0324005421166544550282005c01744018041c0038803907006946154040d104030780c0d00b1621002c0b045024070306141e000c0511501c20040c040c45140520140394000d4880000c5c042061031034035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 396073165 1250 396071915 396071917
    0x100b0f150a0c061b020c040c171302040218040e01060522090c032a0e010302100201200c0f0106030209040b130519020109141012020f07080901030506010f05 69
    0x422000300300401c206406511800140705402c1e00098240843c51a000c01c1d411250701d4090420010300840c1d400034850708050003015400d61255450415405440fa01d181807541c005d0121a21121240790308005039440b0700290000007228040b4110410142c01007208a510329070786d4010702e90421030100410303502c2c000444071140801680c100011600d5488400403c16200c00521a1400400100920a4020108403045800012081103034440d011020b05400c1502c40e004442d04070303000500046c100644c0c03611034103402e4000440c401c0f403000022214003100340c00000c00880702043cbd04008031820480340d9883e41c031082c020401a4290340204220401c01403004e040003403d14040707500707518140402c2801b141c010056444412082d040581c1172030b40b41406900280e1241d001045a2000b0590b81849030f40c000d1007002d1401e00e5130f030305803482503020b0319440c207159090080301c002d07aa10b00014524903100341e01c4250350354080c13030000d8111070018003000d041000d40001841200e40100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 396074415 1250 396073165 396073189
    0x70515070f020d030c0903170918010e072d0c030801050a030804090e030c060f0723030f150301060305030c0d030b0303160609062c0f0c06030603010608070305100b0f 73
    0x4c60046603c2c2040401941c0000460384000c02c2200c1c0c0c1c6048004200159000d00014201141d0b80c90508000c0300840e40106028000c1d0a041c20301e12001c2845240111000541c1806160300b41c0c4a0410846108824032001001d11020403014003041c41010b500402c400c0c007506080f180103205c030b81140c40e024176030b0103503006801c84560340301d541c0207186108200b9500e8500d0080e08407500e07483c0c0740e4000fa0b0240010b071078080c04100e40261031400804491111811000240510b9066503030303500350045c0700e40010344640c400b03c2c1c0040f0310648948007070256002941c0180021581c8000c00103550b882d00300038070f44440030503180c90702d40000d036035002c0112011a820242500c60301040760800e58003c0c4080c1c80014112854880e84c0c07180a0802c1004060300102929054040c000640905071900d100c0f985c000d000350050000795201d490001d0180d500400e0103000042c1c41600d0f100164a09281c9030000c2d14076500c03107610f42d4021040340c0500c800d4440241c50b62038082003160046414541d0038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 396075665 1250 396074415 396074417
    0x3030f0901080903040503010501080d110d0f392108040206070606180c031b141e0307032a0c080708120103150f0b0a0504020a090902070515070f020d 66
    0x11000300f400b1180400c1520081c100080c000c016035650707405041d989151404408000c1000e81c80c1040316414041200c22070304481e921002c03206c4112310320032104600c07058108294185e81a240c030000403500400d9041c030405030491058030300850709006058080c6c1c40820000c0c1e01c584503152080310360155a40f600b142d4151440354440030145025405084d241c0c000004075000c4003440819010941c2005407050100d480400020751000c54081060070307160002c9004c6480160301c041c41d056141c008209641070400101c8502056070500c0e06284d0041d2100c100180d22a04041291000070790020380c01d40100356a00700c0702800540c094100f4408034000b520f400b40c04680d01090040c0b44c4100e5450541200403d601503850703140c2031a25041040d03911003058644002807d0305881b038410003080900007080071003450718040c1000013a60040b1144010400505000510907029002030101540714001400c441500c005200c0151f4030000d0070780042014034a140019a40c0101d089040a041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 396076915 1250 396075665 396075677
    0xf010c090503070e100b280f17041a060d0f080301061707020607052a070828110409380408090d0201180e04060f09200109052d03030f0901 61
    0x2d17100d401d4201f40d11842e01740d61400490107002446030301030700c2d283d19030080c0d89513010a00108078401d00c2d0039008407402400d895020030750143c2c7c0c020340b90100c2c2d84448003c0811350261015070350784044150300102110202004070040c04074540003030304416000b17120b0008008600e4a100c00a50380c007000ba0280341803290004614810100144d6024107001110505030495003900403504d560f0b00041c8034040481c02688030030800340900d52403403081110b800b030b0b101e4628103a58440030780e45240a21903d03409070b82d8020080005400c0308901c168003a0049012035444d02501003d4070710002c0302e0052403803070b13890400c0100160000003610701010082c0c3e998030445035180300586070001c000c55001070403c1c01c400001a01086012064807c034481c9074180921a000e000740001d80d080780d40010588101c0307200080a208800c2c900e00703901c0348149407803ca40d503500e41c04210ba228003612140714183c0c24900c9401c40010800f0aa42c100d14250011403810300381c681101c50301c0c014100c200341000b403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 396078165 1250 396076915 396076927
    0xe010e1f150504181b121103030c0d0f110c010c061a0909030d15050d02060a03020f0f12060d0305032d15031207080a0f020f010c090503070e100b 64
    0x4590907610081c25010b0010012180d46252101c03002c04004c1d130880301d03415140d1000c1d602184016500080303d005489071640c2c2009a59a4007516038002d0625402d0f11003807140103002003082203006403041894403812006020b8402c002c0c03100c940300490801d254400c5844041c0c44e42c0c820300c4030750141d030802d40000b8140d81d071a8030040c0301103000000c154000b21410911041040200090080c001d20b40d10412002045848280c500c1245205840d0300400c40404100541000002840700700c0ea1803500614001103d01c030245982c009101e80e42d8070080205d00c00d0840310070050100d0304200b0880b01801c6801c0c840d0340c000c121b440700400e40a4608243c01c881140600c103540000b41c0c96481c01c04241980c600348501c00307410f170700b10540103100c0d21520740f00200700041c510440d1282500100c4591821410300e9081d00c06081c0110039100714400e46089008034803080c40f403000c11803003560713964880a00d070204152400c44a07801029155020b403040c402c40d03880b2080711508585d181c0ca0601e4540c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 396079415 1250 396078165 396078191
    0x12050301081915050403180e0603062e030c1d1603020a0201180b04051903080c1b0303160905010908030d0b041806020c06010b0a120b060903010207060e010e1f 70
    0x180b1445110f00454107102c00d200805401c841940800052082034046203035030760b285007160f0101601c451360540c001c100801c0210941010300340082502c14007442e00003801c4940e51902a6a40d80248c8482c1000e19003404800c00056032a141d80245000f003021609080004400d0041701c55401004d0550004040304114000e400820206c0d16485100500c00c8250820f0262a101224101d41038029194103040315519000d60b402116099030310303091183e64212940b0380d507500002d42c7c850049516242c00481c00020001140315500324924950b20000120010300b000030b0750b801c460305110701700c00c0901001e0800009d5411703401c113005021070041040d00c0840c005159103074a601c0c0a035864225a0180708054004109485d6080c007125040d80e0303584a800341c1e030b0143c81a00b10009103100781d903815990759500095103c41c4000e0003949041140400a8226400301d481200c0303a03a1124004d0074028020304c110f030503010840c00500800040900d504940c0859103103459504c84e40c45840c01a19 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 396080665 1250 396079415 396079433
    0x9030c010e01030e01020d1b0309050d050d1104140a0608010803220509251713060f2c032802070f090623060f0c01020c01020d09120503010819 63
    0x195413039008660340c0650311140c04c054100705403440e8040b00043e90400746503200e4030440410540000140c4440100c500088400c0e070300001c056074a0a484480f9030f0303840080c0100500050000031200d01d040e400b40824001c100400d03500c50800d20440400412644a002c01110105081020500c4400799000407a5400240700e4200c0c0790869260020400361034030b503100740c801a909588400782100c10b00c613012114038030034040c04400c1c41a68404038800c042c107800382c00d6807548100408540c41000e07922110440c0c24001a18055151014004a1580110002c000700c03040f40f8000c0e5190411085e100e29502c0f2540c85440302e0400c01582d15021240700f40450000b0305001402680c41503507501c4040060600c2e401021864050403c680f0b250105400c4078400d6880007900745414850071000d07100c0950800c55441c1100e5408000c1280c08980070310080000d90201c0300300203000406410584003e060481354003041c0030081005020b059400101403604100c18501444110f200345802d000c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 396081915 1250 396080665 396080681
    0x150e06180601270b0304022d010c11030d030506190b030c0901090305060c19020a020a060e03010207060e0a050606150403060b0a0306020a17070e0901120804030b0903090301050a0209030c010e0103 86
    0x100a0009404110f001404e0000d41c0524002c840d500f0702c0b2204042081000d603010f05445c001c01240309a02c00c21540101d0060261901a0b100304000d00c00d1540481d0402c2e4403648040b0010343e0705c0381088aa0700c6d0a045c000b250000040380c81d2402410140008000c1c400030b02100d030f40c017001040702003003a031190070040041d42c0c1c00002cbd12840e007020006c103001034011004001940c8141490103c0c0c5903c0040c0c0030385016002410313041e00c20b240c034a0594021004100d07040c0c041d5007c04c441000320700765006032200d203038030240249842446ca050042c10940c024103c1c1c0d110b110443c4807036072109199020355003566003003500043e5200601c0300103842010345520080c0090700201e08954555041611508a48031f0054144da0654901508403000400c0c54035151744003884400600c00f0000d0402030300250f0303100708081468161603840f14244100d0444900c61580e00008003001c45040a006240e0443c0d4508001c3d41060708002c00640c58024414034a0304105084036034642d50b03803194102d040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 396083165 1250 396081915 396081977
    0x40f0902060c1b09060108281109030c18390c06010e13060b0301060545070f0c080313020f090417031801150e06180601 53
    0x203542c0b050814000c2c0c071500c805104008850207800000070394101304424602c14075050359a069140d0b5415005e203c01e18007450000108000402c48a041509a21a07030642c2460340341e14548070b001c048109494050340ea5840b034041e001e1a03400f00450048400d0712900005050ba01240188140e218006035040e0340301c103070360810036200f0445200150400141110308801d0150b42c8181e1301c40d000001254410b4a0b4494400e241e11207003000700c0c507241d2046151840080000c643c0540d01e60001d43c2d404019001c0b940580c881d0b19600041c1c4004c0342d658611f012403500b800c0300056402840401441005082c442440185c189031a4003c0c4616a0092950b0b03003d40343c55180d05009520000014000100324080c19000d988884507103404203c0c10b00c900e610510050b440c9030050700350406504098281c0f0445d111010300f503103e2210a01404038020f030303040e00c1409400e241500c80e400c0910040c040d64003448803945d81e00003692107003000c036520480a0a06028801005917610036640303003400340720 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 396084415 1250 396083165 396083167
    0x501050d1e02031f0b03060d030e1002151005030a0f05100f022d03130309030b070305060a060c15021b010e070302040b0109240507080c01050406110a020606040f090206 74
    0x20081c0106074003640c0038605620381000201e0750070103605807611030341c0200020362905100003112442c005194107001880791601001c84a0100c0100b0300125031010503d0150300100441220080050010b0707070b02c001c2507802c00d200c440c54080429245c1420080141110404501580074447e0802ca02c40c070091100c1030403c0200b6034512164001d41280c00e41042d155207010b03c0c5103200c2144140d4010440505084516603110351084521031000c0306000c03010f100c50350704008082006428401d102e030233952004201482c00600700b02c400016a08500d0510054a0034500403990b0440f042d10b850144500c01a170344c03061401000700e581c4109051148d5036090500078080c910b4086007500c01c80388241c50910601c9188001901d119056004c1c80217503038141c1041c800e2080c0c00792236194800f080c0c9d042072403404240341c032043d9241e44900c0c2071075401ea44601c01c1c00100034aa1081105510f11064064140504180001c1d00d500000e0540c034861038544600903200c0c01968460381485900501b0343d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 396085665 1250 396084415 396084461
    0x11060414010606050a0905040506180c0403021c150e07121505061816180e061207150c0c12030c06110f040e1e010617100b03010501050d 60
    0x40216510440c5409550800100245090040d4242c40141c44540c4500880c2d5060105210050000501c0683d02001040310000100c4d40d84036114003807415051a56900c1d805c41c014001d5041c1c4000801d001203500501d41c00c04100110441d102c111074040d070104103032118400f00340c90880160030590a080f0341000003020030090710440702000a004000b80480da9072002044a140000301400030f0000c80c0100084a0902d107003490031424040d0300341080761018692501402442d0741c1c011142180e941c9040c1b007002d20f005907a40c2c40c6039a45000030040181880746130003680350048200d805001c668000141001890345031040600039001200c1d0010b09030b400c008280c0c0d07a401d04262503481c5000c92071201c01c0080320071036180120382c248007440c03e0714201d020841780d44000c2c19041e21808100d10580708124200d403440c020a2260380d0700c2103e40041b002e0001d041c0000d0903010200340b0b1890b041046c50000700959045400134201940c4425100d5200c0003d090b84600005450001f1620 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 396086915 1250 396085665 396085673
    0x80c010204091103090d050d02130e01030302010e010e1902030f0d0512071e051605060103060b01030b04061520070801060314060708061302040e15012a060903110604 73
    0x5070040b10308450060000710300900034200a84410382d400a915004120340c850201e00520082038404140040103140c00700301e030f00c0450a048650000015024228010028142c2c2405240080203141e40200840f80b0040c0342555240b000c45000104115000030000c1995028800b4442c2c00c2020019602c25401d084801411507020034a010791020210000c00c20052040558000702d0f455124092500c4615410995007034010384440000c50810106880c0011010320070750b40210b109510119001d2486000901900c0350ba905031401146171500400c5070100030740a652410045041199494140f10003c80581c44a1507801e0030902c20070100240c2401d0550020040b0b90040b00ca8101904030300010300d4a8800036110480000c100b400414003a1904410118014031305000041c58640d48020307001e8200c030111950b18140001850882c609c0d60001c0300070b2281e9017800b201c1c0e9002c4908040034011002400b2000c1e01c030039500c44024040500810540444400000c1140c0300340ca01480c5c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 396088165 1250 396086915 396086917
    0xe0a03171b16080a03050711040605040c03060f0506070803040213090c0611060c0301030503120901230a0b10020709050c040f032906030721020604060810060f0c080702030109080c0102 81
    0x440c112002c0359150700007603910004640d0b20071060340b41e5685840c0c000c003a110450503502041c079960344203940c2c200014465a540c462001b0222194801144491404404552801c2d0703650045000f01e00400503c00000d135407000b00c0303a000d98100c0d862560303a0000d070060300c000c15000700f000f03001884110020469035041078141080014800032a100b554a502c81101d05020030700c00100340380c2c030903c610b00c040e01500b014250b200c007164000080440686e06c40140802d69103851103071007a0704209100090b540e900400d811500c0035203c41301501c0d11400d00030b649414901ca0300c446031f552500816100404881110010030344002000307010398032070903c041c900000450f0380101e010407025034a01448545403003031140d54010050b207400e40c5408001304107080341070001c0c030754100c1d1010000c0060340c3e110082c0c130140455645040322071a06981e28105c840481c7c0154041c400012032003a402035116002c000c002ea440901c280e112069440801d025140040d00140261408200400d071200154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 396089415 1250 396088165 396088183
    0xc10022205100909091110050a0e0a0303080609040f060c1d04050103020a050609130c0e21060106031a0301090501050618090304060c080417030702040c0e0a03171b 72
    0x356580c80308a640380100604103242036100004207200710002c0042c1100c0350720280d21a03015825020107132580500103a5010703120342030390b4080355021480440e00b80d88502403a0342c02005036071252009055480140c200c60780144050b200e0042c0074002410441500504107841d80c0c0490107112003008440007504140750613a544443e07071241c3c2c40442052410b805070034122a00a403002c5c0c110703810801446165880403000c1a080154030202948005581c401c483c5811010b5a504594900300c0381044400111014135a940f00c1d0702e6507040d0000f00c0c0c081031190440b0180d040014100010407a00141c8990024225030305500e40140340c024444190006446110704462402d443e24078081ea0080080d01620150550f80c8184014000700f40a0340b1055a11801440f1640c10165201100c14804180d110700d0711150700040740690450801d4001c0594440003400d001711228800750105000c40c2e80d0f440080c20380118a600401414280402c8030300c840c0416803201d1a80b01856015a6148184 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 396090665 1250 396089415 396089467
    0x30803180a0c300b0a0b0f0a080d1e020607030b040b0303030a060e010807030b0103140c120304061205160c03090909030e240f0a0e2106010b1303080c1002 68
    0x48110703080760f00003600c1501841c2e54001003c2c807081e03c41c5002c03a00208a031004003504290008036401c420768550032003000400290b001002298270b0440b000b00030818403030054900074922170003070b9031050700812215409007851a000904c41000ca0004001d00b001480a5826000010520684829036000f840544440880d000d0180e603907105100d90700e850b18400a810031011900500c00116900c482d03034041c24000d0100e80094603014001400007001d40003072030031a400010100110b40c1c00c844038540c0d030720501000b042030340b9160740206140600f440c082020445454401000c240c01001540050644c42404002c0390350306140c082d048601c44403207503100f9030701070740c0101150307001500e0000701e403081c800101c0c20700f20320040094240e000084003109001c030f024208a16600d4480a501c00341810b0b00002c00c54880140340301d400d040c07040e0072010740500704020040c0035402102e000c20480740d01032003003642d81444114a9003451294404004132600000b00c150104400c01040c100c0c11200d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 396091915 1250 396090665 396090719
    0x5120307110c0105190e040e191e1a0a0f0614040b060a090605031302091603140c04180b0303040306150b04140d030c050d09091104030803180a0c 64
    0x1ca0010340b50b500480225081c4d00d030b4a010380c1c5c0d41a81c4607002d042c0c462a40a480032909440c00e440e220b091402d207505c81e000040329a1716070014444000c488006003c0004000031868080b40c46410070360700ca07045203e520050100c04030b10309a030f0641c401540a40c2c400c0e070810007541c848102c80c10058502c003004d4440c0f810060041c03594038200086540c41b0320755840d41c034a4180f030028140c503140c00c001c000c4116107100c84001c4000d40c40e42c034000d0b442110040f072087c190910044000c2c1c21559102184880c001d004010020301501c040d046900740d50065003c8000c02c40c0000d01c080203080c90115007030b05030201140000c10010746400190103400c800544c030481c503444803001101c0d40242d110b4256140c14100341902d050030106c2d100d28169000c0d00e042045100c4603100c9030f18000d868403c4400089170300208000c446811322070f500c61803075016030040c902491038550407410b0101400d03549409140f04614084a80100100c20f01241c0c040c24110801c0c0e5140740140b00c1c400340038040350301841 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 396093165 1250 396091915 396091933
    0x102070b030c030f0907030b0406020417011b03020d02130314061609060c030c020301180605060f150a030e2a01110a0b100504060b0913051905040512030711 69
    0xd494400c1da4403a52040c101141140c0d100d4a03410903464002c0c0440d00d040c0500ba8010000c0745800980350300c118000c05000d41d86604d071106c0c1403c004600d8030002c24503458140c460301c0060750014013011008880c50096214140700244078001e00c514040c0c0310314210001030020401415405401c8c4c13190021080d0792499882082108640c1c8520503154001002d0640520215000d00309259140f40039107049122440d00340c0c0882d003107510081c42002c42040c0445584100074050081a60083c015220030000b05041000b00301510b40d5112049401000491146607003842544480e04001d400b01c125020180284981900055510900d9000c07040d1400110040d5015034410000a140c00c401002e401c1e44a40f109414040081d082c00103c840001c4006025600c0d0300904d0040d043c0891200d03560401e6004009400141494013003049080c5401c010b440c130310764141400402d488810228440e070b200c1c27410350f0903d1f44030064203802580100620400543c019000000c0e050091704840c8162 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 396094415 1250 396093165 396093179
    0xc0207090b1f050f04030816020f0111120705030d020403080d0b030c0a1e2d0503012d0e0102070303020d0c0e031b030f01061203080a020f030c03061f0e010207 70
    0x4014209101d048201414020001d10443c002d001c4000090200e50616813641d9170500b0300c0e803080c16102808019803070228154645001c0d0720340028402d081c00d250881c1082c00d59074942d0100c01c510b0410090100d4600144030f424421521109400201155144d40341e00d403600d065003028200c68090303071410700301101d982400980c48044600c0141100d44503460211880320703c010340e03000c00c2e91001c00a0b40000d41100c0034855860002d1450b111002c1d0300da150083c90609400a0b809548240c1c186802c1d500340321b4081301003810030889111a0313201100c00c9224000a40780c021301c1d080c0307190710000c3c500c01816415400740c200f1100c07034507081c8564060036004869401c010540c00c1c2e81030300407960507083c0d003c8403064504400c40140c142c0d0347c40d100c0001d266086903296170040ba0b0703030740343c9076040c004056021724960f40c0a043d5075011414481c04440d001183e0100503c0c0740d104036030001c040341d031568403c40701380c0f11311503500c1c5c0f19032440001080c028051030505843d2805403141020100c3c10f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 396095665 1250 396094415 396094429
    0x110a061b03020c091e0901060305030f03060f0907020706020d0e0d060209060c0a0303091101020a02090a1a091801060b0f0406080a061212140906070b071e020606010e04060513050711010c0207090b 86
    0x14ad403c42e005608020340103180000580c4050840399205400030b010a9294899404003446041d4980280554914201010342404000500b5104202240d40007000070f130f90700c4d003c4002c099041440140ca0fa045907010801620a805010346a84580da8502c820103501d608201231040c0315940014034501841c00682c0c2c0d03200c8098000790302040c0500015160341d075507070180448108041c02d44050424400c04550628819034079034041030040c0340d804412010900921009280034a20b03e49070007500c81c0c55010324010b500607a0100044040400c50640b0103400c104040e052448885a9452440c0b5101075450112610304020030041000d0b400911801026180c826030064804d0f860315086a0740c00d0003200f40101b44405110130222001e4144940110280240166030000e05050610400151a4010305000e8601c201e003804030501c61a02c5241410101d0b2050010200d581e40714003600b6030700611291402070381986030203070000905500242c2003045440d020000c000d1607400b00140011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 396096915 1250 396095665 396095669
    0x506100f0609052103040b04081509061e040510050c1209061302090a1107030c031b0213020a02010b03030f1c1a131e0504110a061b03020c091e090106 66
    0x701c6081201e070310b9040809501c0c01050084644d041d00d2400741c543d01d0341629904190070001c07840e409008800d50143c43c00c0074036900802e180006041d00d20f050b9092004a100289480303131401040c1001c501007090030000e000411030000000c0c44545060460030707115402000c000f0310140001404500341e8040400c159005080300101e0320111001d40e002c0c000890006001044130542e28000c0a400c001818040c2500901ca550b400f0001506828014a0243d0b4866440580440305140500580d40c802c0b00c0400450240e90145e10354900207020307130040048640b80e0b90540000950341c0c101c80350000003451071030300d001800421560081140c40886506000d2100e02c4010b1030500c030f1141c50515642c140e01c002d00344011840c0d100030481d070803008410001040040b900c0720184001c00c103000c0b80c9045034200996061418914160004044010040802c0311107221031505109040c030030700440000400140007840c1d98200303d07034505242c1d888078920410f15042d140210304405010f00940341 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 396098165 1250 396096915 396096919
    0x21c050118030206160915270807080607020303063d0f020307050a060902190308090405151f050c061006030e030c0d03180609051c090e0c0c0304030506100f060905 72
    0xc240c82c24070187c0030f6041c40480d011810b0120710041e00e030310f081d00804036042d09020100146c0d000b500c1e114520307142810580048280c0c0c2c0100b400c101a16600100350781e032010044a0081001403010001034001e11500c2e2903040324019100d40303400c04042c004542c0c0070650310750355080103601c030b80d07070b003245c40f4043c0d40d000030030700e400034115034000c1038440e0000c000440c0001d114580725a4035a4a0306100b00c120b038402c0355840c002040c070a0440c600340c403405a000982c0540c4044917a005400101c0d503209810040c10036800c0406e0103000c1d0f920032400d45024021309000c0b500c80c0d0802841a0842c1c04032885004006800d00c0d643d10542007022098445035a00c8400034a401c120b03402040c1c014114418481685480100140f808501d1034019034000900650140581440c807508824480c4107186e1b046c000e04c1010007040081c0b0078030001d03260744110340126250300c9858503a0201d085104551000d030080c401c172405d200c03c42c042044400111030215410540c413030741c0c600c0255000c1e9214440c0d16 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 396099415 1250 396098165 396098177
    0x120e1212030c0708120709080111070b130501061d010302040b030c060d020307031112060306100b090603040f050a2d0819030902060a020718020304020d021c05011803020616 76
    0x1680b9921050103011110312405845007003510f0445c0c900f684800440792030000036840642000401801e00c5124500c039054a00c0d14038188a6498808009102402c0c40107060210140842480301c00e41c0220302400c0c80c501c52502d01010808142060030003800182d03c01ca01c3d0070000c014510700002d03580b9803540003410050401f0316400083c1d000703410040590051548403c40e0156014404004112414200c9050076007800e0500503d450b0070700050240501003103003d001d0215080c40020f1320f0340158100c49841e074968403442d00800c0030282045c01807a510403c1d040740100100749244409640c00d55003840c2c51b005c000030348010301ca00c18500203030501001704003041c1c24052443c10054180c400e400c1c0407510f20403660100340303503500600300a0f006800c443c1c814015082034001c0030500c040c0b405404d5080d070800740c000450340d00154800074800e1410603246200352001e01c1d40c0da5040750308000200808005104c0e400c41c00184118120014003400000401e20032580c41054001c2c03129030703909 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 396100665 1250 396099415 396099421
    0x9030c0406140d170310140307050310091703090a0308070302070209040209090c0a06080a0c020109051005071b0602030411091006051606020c0c120304030809041107120e121203 78
    0x20088100c0200020b450944c0324402820000c030b2054001c1d4017680d9610800e601e03803450090307081203070f5207094540f501c2034100705420407240d03030000f5800c581c0b12040038001902a909180859070051658a01d040182c000b204122000710041404800240682c84421459440800442c100e10031862f0003580700201002080c09418041106548242420101d0300d500003080c000481c12820b681c00240021040400c0150580c91800f5200500e10140024401445650faa035a00d03040c60004c00d001c0300d40e0350400a41c280f4031443c45c910380d030500803c0d46e15035a0301c141040001303588210350966100300402d000800c0d604005141d00e116054503202c03905c00500303041c2d04459a6003e0802c0c0f511004010b0343c0400483d20610041295481031320051503107165260034410440040500c82545400074001003000c0340c00c22042340c040711401c880006402da10a81c1c10440f03170060241c00b130503661000383c2424101d50840a1004004812288480c0f07444000c0462582d41010302c0c0182c0c005d5000b4008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 396101915 1250 396100665 396100669
    0x1317030c120406140a091206050a0c0c151109100201050a060f03080d050a0b0604121707051e070f030f0201121a060d0b09100e010b0906071b08010f0209030c040614 72
    0x150008045c98503003010115501c00c81e42a01b0362440d1400e4404590364020700031108014424200e80554a04051b05170b0303551a01c52a4540038020900007400b40c560182040115120040f20302c8520010004401c05140d8a0000d00800c1d0498200c2e03c61803402d50f0101e1015100080002103980c009880d510340410041e02802038039026208810700e81e213910007100d05594035405880546907080700392021091900b413071084000c01820b546450842080300340045180824400344244009100301500c10840c41800e20700340071607104050301003005501204001022102d00c1c0c0c0c1d18000d07610160b010755480c8140c011146c825000011102d80d5080040301820040c020b0001400300d484000b4161a2540200d60147c0041790458910360250a041c84425140f180b15405044900c00c0d2501f80766458003c0342c1244a40c2c0c00107044201e0710b5298100940d0444036401c0500007502c000d0011580010090f8003075048401d4042c4240100c019140d4641014440c031b00c1155010b0342c0041855400c00d00b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 396103165 1250 396101915 396101917
    0x60d09020a090204180b1008070818061006021014070c0c0f030803010303081f0512100c031505120c09130606030b1e07090b1317030c12040614 63
    0x10080380c201c2040e4000240502282c400341c4020f0188045075009080d207981284100d480f00c10425100302c070f10a00e51071340c0e0b070751081710150300c590302d410640103e446500c4c5900e900d03200010a0081d5106020402c03005190345a5940301312001c03602120501c0b1a129401d40c00e48038804c62045021075480300107401c03180326200301850076000d0940c0e518a00c2d2101c19401445946030002c1d105108000010010150f100ca945c59009001c100501c2d4000d102c002d0228980c0464401e17180315131a801c1021001100500c80785885110502042148082060029028060103040c00240300030382880050a17007095031900880c6c1d442c12000e08800309540302080310000001e0300110050302d032003c0c5040010b82c60f03c0760318051806103c01e1252450b190350071f5020500c3c6078049924585107807041c8602c1640002501040d54541e4610988480000d60101c5c0f60440a910071040d00c8000e0b06401040c02e8040018030841040c4004d6941c03844804007070314103a02c55449960300040e40c0c1007580b580803100700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 396104415 1250 396103165 396103181
    0x160e060d0203100f111306020c06031902030402010509060315120d081f050d06060f05040c0c1101050c1905070b03010f030303020f04050423090d141605030301080d110309060d 77
    0x84c5000a140b90b140c40032440c2d80c0c003c00440c0080105003081400036a4040040c1081b040c2c048500500c1c614102d0070b403e004122205010280b550080045411680244250344541c08041e200c140c80e40703801d0049045205029a4440c01110072100c160345041002c50310480715a003640718026a6110386074030322a2505a00411141c080704803802280d039584040c5896a01d5024100209549080032038100d050101640541c5c843d5180100c03003140d080e00105038082481c1c205c00110825411783e0016913151003a040e00b24541e0040c3e403c0d40465042c01011204418001c008490b036542d1203d00018541c0310a02643c60740110003041000003d110790010403000c003409545130704141e9644040f9064400c0d1100542240d01901d5604100c465048100c0f584620301c1d0000b400290140100500084c0e10703485d00c2c00c0d07104800030700f40c8032607000440000d101c5684101101e64030742c2d6400c515603d807030121101d00005512528a90201d250010580d04102c8004080614020103582c203003004003801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 396105665 1250 396104415 396104441
    0x61505071112070b040602010c0207120206070309080319030e03070317070302130e06041b0f030906020705061509070e101d030604050c01030c02070b0327160e060d020310 75
    0x184442d8402072052100e280140940002c06440f90b0810754080c5c00d4401894042c0115840304008210032002504213950440c2c050725410b54038003050408464054164021450a12001803210f0703d02e0360500c0e25a42c0540540d80c100001810007175010b4503032107801009000a00800c011b480e46131140300005410842e94100145009070315405d001d0002c800380d214080800303003030302000443d00b814001d540b00d48400d809100c902d00b41216000c3e111000c9a11240c00700765441c9555000c00c00280d04407604160070408481551404250006904204802150242c000000440c4005d40034162882190b04010a01b41014500303120842d02c00381464030400d0a94200301c1b5550b00d50701c0500000c3d00490003400076244411400b40050f0903175840084102c115849400701f0401460f050041d603400c10008100460380014815400030601400c40a188180c05004081c61001e201c4140c08012a1500215458142c1d18103040007007404205801940540114401c2500e06800c0c0d17200900c0f200a03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 396106915 1250 396105665 396105679
    0x301053001050f0709050415090b03011d0d031d0c09190c0806010f020c090411030307080d060f0942060512100302101d09090c040615050711 62
    0x80000c0386425580207031044201000307907100313020714190f00ca05981d02604054406001800003980c40120400c60781c410886895540c404290007a0f4080d0805041c1c9a901c6403ca4030144a03071034495240c4188008510101e07180c5006404006c440103000089460864007419000c0e0a00003401013402004000400c1c2600c28011480364036254428000d030b4030100d68a051003850030702c00140a04000c0701c1c1181c01d65120292410050303841c4d50840b944141d000241109603000000840e146001c1d0740001801000c4c081011803d1190a6000c10101d590014000c84440c3c0d96940d0081103540c000880501e4014000c0240700d020081c0d0040b028403c98401744461111683c0812034450b42c6079088100010800203811101f0240e02010700c0d00085000c005002652540d80014000c0c140f25003620240418100100001058078003041400c0c0300c094008008c901d03150f201c60383c0b2400d031601d815101d141307040c5021500300040d01c240c0c020000d5540f15a460032859031a00c840d8100641c0175281d10000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 396108165 1250 396106915 396106999
    0xd24080d1815050705010b120a0f170a02030d062103050304050a02040203010b1308060106090e07031103041101031808030a020f0c150106020601080c01050a031e0c0e040b06030105 79
    0x2049100070008810780c2d116030700e80350245405c42c00d40d4003445410b032103003404201d18413248001040c094021603010400c210301090624020303c0311000c9010000503044086646500b80d45c000c002000c800310a564100412034642440b4003040b0251240190741010500000c0c001074001c000840e0082c1c05030046881e001c043c0d5001034107981c400d801038001100d0100d100d01d04100e4100802c8040c2501d20058849903040140050040420b4840c0c59807680d01c503808a42c0003800b0b03502050070240c2e03400203907541e03180034180756192501108101d030000303203080c441ca00344007504084a40c0f65075201041c0c030311f9500c40c00303290006500880d00010b00881f0803c940b40490104000060b81c54440c1081e05000307614000029080034016886034607143c02c48554415940c0e400343c200c0341c0001e518240010140301844250007181701c0545200c140030b14000e50115450b42060114444170011030b014080b0b056142c007130000c0340c003080c0301d05604042800c2c2030300c080d80604440004005208009104c1d171403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 396109415 1250 396108165 396108179
    0x1d0109020c011404051f02070b0a020a0504090c080f22020f010201060f231014030a1d0a0c0609030201090e0702010b180103020a06051603030903050c030d24080d18 72
    0x24299805c07034940d8003003031011108600c0900010f9000101c03031400c505058881e240c0032803035200181100031441d4002484a1083e01400030303140944108d510411007020302040c094402142929012000c01c003910008002860980c81c1c00ea03110a01d1f40c11a00044542d42440125010030070f040d03055548810002c208102030390b500e40d00404640340741e9007101011b803010450444282070703124004c10040b1710901e00d2035007100900d10100701c0c034228179070f603940c40c0490306009102441c0c1d6040003140074110000d01c1780380012440e501070b0003107041c0c00b4001c0d41d03450300b99440d9410380300003404500909001c01c800c41d1210022940190a8000420041c8200c00021a4540070000d5442c440219100510a504001048601501903030078090f03e060000e40780410700c030300080e10007420551100c61403030401d0302c03070026141a025000f0480340c643c812107442e0b00241102c8070260042c01f049281c0b91880e003410140550031501e900026021181c811201200d50307010b50444910f9000b01480d0000707c1c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 396110665 1250 396109415 396109451
    0x9090c01082a0d180b040b1f081501080105060f01050d0b04020a05190f20070305010f09021c02210705100c02010e04110a1b0812040c1d0109020c01 65
    0x10b034242103440d075a05102805441210403211202aa03041d041181c50001081c0c15445604150800b40c1300500340c0e02c0080d07e88400d84030180501d0803151020001800349400030b1240c0c0c00f8041180d404600381c0c0c070754485a080703940c100d1b40c0f96400f481e0080414181d500640c01880d00941812004c20218a41d40219060740e21005001c400100001740c0880d00c13035400045068201d0861810805029000074000d11103082c1c4058072002c0d1084c0218242c15a00c200000700065a1003c000e0040c1d04000d10080d000b0649242c003a4003c0e107100c0c1c2c40d04a4070120010328010560b00034044018020708040c14092102c440440084502ca104004900da90394402c00076001440c030355610168050354400107001c03981001c6070364052030070101da1403441e0050390143c4c0c0032080e040c906141c0f140700014a00644030f0000c0c40203071003d680003d0884240288030307072152256000e0521141341a58860802900d810040144844240860700521408100d42c005068000c0c80c400042440042c61b5590711003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 396111915 1250 396110665 396110731
    0x6010f1b0803060108010801022a010b030105190606030207122003070b04030e030f0c040203190501080a1103120403030e010c05101a030f120901090b0a030e0c09090c0108 75
    0x8100307400310800541e50307408102c060140c902031009600b4101744041c2c8400d010304c0d045c0d90040c800400700032070a010200350701c00000034400400900c150b051211018559a05000c4030f03070302d003a007000004a403180c0a4001c95042e42d03030103d00805040b4076840100c0c0d1a4005801040341c801090080b80d0306400200040c104841c000d500f84403045c242490b001e0001c000c03914006000ba00500d482c041c062802140b0084035050545015076240e60307035000008000da2800d840940203141c0000890303181c0c000a408580d1134400d0701030f2910302e50540200b580c0c035104803812101220040000340002031158030f082c400c251041c14011044046541e0312800c2003510202d11141c03d07624030440358215001d11084031141d0040d4041c014601c10a014552603040100e0050340580c5c0001e42c0c404180d02c42d5071000010700100207441e03140d1501000040207401408844c800510a03401e05003064030342110708a0040c46060000c00f03504c001c850054134079480041c005030b0b2505526140501700b085030008002 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 396113165 1250 396111915 396111923
    0x42a021b0f272e03150c03290901050103021e0f07060f020903070e07300e0a120306051f0c1b0f08060c0a080c040801060b0711040b060306010f1b 64
    0x1150002c1900b070f091840040c5034480401c038007111003000425480300301141e8000ca5030320003241c0c455041c2d900350090700180c4154040c0c0d80020440031441030410040c0c00340c5110480345035045917078803001182070380038aaa107461822070f00d0160b00c0b01058100002c2c03e070301100801e001d040212940b56003048500c1900240d0080703400182e104c505d4502400000050400c9500001981c14080c1005060310f55444818081c0c041d41c2c1c00401105421140c146c5d15101100c00500001d5121401c8540300d02842104503070140e159650006918007038002c041c00e81e003000d01041c980122000800250f02d01d00074902d414822000c81c45008280c0b180900c140f080021002c04040500d003076003544142480e43e201c3d11168005605200190803400300b1919620300310700c0c18592985410004480314070583d4041e00b055840c1c403400103400e40c0484060480341e40101403070031070701030254140801d540b1040080369100c0e034204000348584d030080c1e03c0f0240740b8606107030106c1d10480c0c850485000502130f0000795 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 396114415 1250 396113165 396113191
    0x1b1b0a060207200a080d0e040e03070303020a11030405130923011505090c03160210020c0d0311070b01030204050c0c010e010b04150305060114042a021b0f27 69
    0x6880d035003036203816040c1e20b000d98104284c0f52070841c50584601440c10b82004100c1101c00404040c1ea841c2c000c82c0c00c80620800340c1c1c2d580c401503d0040e000f5400141c09401080f070445618203001004030940701103401c042c0c0180700c000220144d410017400e840e0b0040300e0480c4440b0230a01300c0409400000b090910650000446450f04204003054800c9944214072030364100d01006198181981a250002d0380b495469558480c042e40030b906144600a8a0704103520100368000c0e01e810020b0b0780740b0252544e4804108225001c8601c01d02481aa24080c01700c0000e40010001410f203a0300590f0310291000065051566807060039007510300d03c07100c00c2c40380da44640202d94186401d1240000202180c280340e0304461541c0e0341c05480c1c1e2014424000550300e11110740480c0d031610340202c840034aa90980b0000502607104140c05911280b1155006200b4800d0582c030307030825080c5940401d00003c1c90141c07030100100403c4a4001c5481100e82c074400d841c3d8001100848540c2603500840c0200c081d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 396115665 1250 396114415 396114443
    0xb0f1c0903090810020406050d0203060301020702031603020f090112030e0102030f04230105070c12030309021c0302070803030114040e0c064e0a06080706171b1b0a060207 75
    0x1152900c1400130008007042d104020030851207070041c04483d007200c1b00c210056220b5581000090090240840182d0140503540a0100c0c1080d00010340050700d1080b12054444501c0c01e0034400d07104000d001d54200e010711951400d010034000c0340c1901b04130340e052046034503000038145002d489400070791046020303413031602c0300e60659403040c0000003151074286400d6003010344544910704a00032031f208040000317511020303640a0502c40d4008c2c2401c40c0c0c0240040800b00380c54801d8640d008803054003170300140504100460503090100441e4103e414078170703189a100d03000404000c0240151040203c1a128190101074140c031240b0107040704104125041208021052000010115898001c0390400c0c114000c40c035112071040343c0c0e10101580c0c404c124026601c0d03104541c001c0601da0443c0c000c40c0b054060016642b40c0c091800104162071011403403641d00c0d072900308070840e0550400700d40c80355800e1152914031900b685441d2040041d08007128641d14964484004a070f00c03860040e41c2040f0021a1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 396116915 1250 396115665 396115679
    0x90301150801060e060409020d1b0b1602130524031501080105100609030503030c07080705060c03072c012609011505011d061804022709010b0f1c090309 67
    0x1310780c80042540d050003020382543c0010700075100303100000c2428010080c0c1c28242c52004208001400c0110f0f066640c4428500b904102605060380480c800d041d003150800700032519001c0c4c2c5010b00b0030b000f5a9450401c4218800c0c0b0303c96045405290984220054907001c103041048440c028201c00c0000100b60609003030b040d4020100d41c02070342c24811079a00c00c00c0068000001c03294054145c0c40f10130b40307031095480d08000c00d104005020f00648503580c1481844503000b070041d8002c02c42c2e5240e030403118005450034040030690315003000002d80450740200080d409201c4500d1a02e04004018160804901c029001803e0541e1220001ea6444542080c801044132469001d0072090804011840340e0b5210b0754800c2619072241805800003090505d0740c441c1b14a150480200001c2044d500ca20003446c00c40f4449980841c3c890040c42420320050950400c0b0914a0594152036400303490304410b030300310040c00e90040a400c400c0340e080640709003c610403032182d41182d910940d24106001e240041c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 396118165 1250 396116915 396116939
    0xc02010522060b0a050d030e0102010b0d0c0510021204030b04231915060b130b0405180c210a06091b1103160b040b070507030e0609030115080106 64
    0x1240c003203031458481180c0510080d9501014106a0010020401c80e10318404610300751344640c8000e4201104e00080310405420a43c6042d48a50a1b402002a038400c4c07410000e40504110000c1c00700c80b5102d90070310950400104c2d164070710741d590049606241c01034000719860350150380700f600c0c17004c0001c0910040000395282e40000c48a02c8001900f900c910310216500c500c0c07008006840700d02c04800c41c000700b1440300403500681055200401445a03143c000d121a81d00c5845005c2c3d82410300400841c1d650178070000c0c0d40c19500e0142c0251483c04c4001284062058042d101c3c80300380c0d800744103401840502901c070104c4107100864500580c1056411030040d210103400800030716050800054138004c90440180c4550401d1810003c0e03089a0b02e07816085220700b0b0681450400c49000a000303100c840c48045000d10f101d45921031160380c481c0c504460130302602100800180c040b041740c1c01140780090142c144032600800000f10008461580c222422250f07005c00d4103a51626410885545604 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 396119415 1250 396118165 396118171
    0x613080f0c01020604030504052e020f0609150f04030903050a241a011b1202010e07060503010501080406050408160b0702101406090702190305040e0606120c0a0c05100c020105 77
    0x3c00209010309003550081c0081c05580101d80c041d01101c0642c1e40f0385080950000d081c811101c082c80910443d24600035201c411240c90022280310b44404160780410008804801d280030007000801900d609101004549000e00243e00700044002c001c404900b0a100718220a4415090804844600078039214040210710046007580c5c41c15030030a91a0a404080d800100c030700f40707031603466006a0f01c02c00c89100310014010301807110b04011a40e0007a01540a13082c843c071184d0465140b207030b03603000891f41c48c4002d0003240d0000380e000d4041000103003240c00007a00315104207051401c0044a15000518202094050300c00ba40074000b070110042e010710281000340d181140600107000e0b21822020110030140182d070103850240002003203503100340007070454038003900b20b0110206038500b00200f268100d401a40000107040020a40b540350290440310052072414180e40305a41c0c0345000001364100d161400b050280d40f4000d200010014040c020a03007540c480002000d50324800020308403070b001 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 396120665 1250 396119415 396119417
    0x6050c090307030201030e010908070606050a150f1b0b0f101d060d0206040e070507020406150804020d0c0510080a0e06040b0f0402010c0807141002040518060613080f0c01 75
    0x4014000340340e24089150070903a40c0a0038080350340601d4801d200e0042c0205440507020010104001c001c1001e01e4100780c0031664200c1354034100c240c540b4175a0341220308007454103001c96054108180c101e0700440e03140507190444001d0f40c0d0072019984900050110032508070030544094410040c2101d0100c10001c050181d125100c2c0d003c085540300610207000140141303100300d01c80030801045582c0e03c0300b200c01070690405082201c0c14100c20180043e0044c4200b2440346090400100e000404024004c02c44a02035960f0066a1100d4003440040c85070480252800c1c1f0300c80202103680d40341c1c203000e2803c01409075682280d07841c118036260708984101010400c2ca4001d1002d110210f105401080d412141c0c1c0050340c7e01945403440103071550540b140d00248400c102040d03100600c15900f0070285034000413400da51002c00d4509020040307100d00c1c006c01d039009110080301304070800040010359005c90090952450140403506072883d400c81c0c1c0d40701301e102d030b4080c4034514807598081c03002d02c40034042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 396121915 1250 396120665 396120667
    0xa050904080d060b04080a0f17190e01020c0a15090801052a092d0301050a050a0507020d0206011a1204080a090b030103031407020d021201060617040c030b270a06050c 73
    0x4050b10640c0300c1e0440100600f03014141c611002c01c1c40f02701c5906400c0040024421540d45c101d0740e0b00c5c51860880800c0d01d0010428001600301e003035002243e1210000c01c0144102d0b0350034148000c4026a14400c03c2503020042908070101d1185000d10489000b01d0504035030384013016255545960042100c01007019480b8107002070f403140d4698010844c080e1019001d51a610703a80c00101e007064120200e401c647c55824032092116840b010f50050740a5240c0305010700141c0d440d40e40c180c1c2e4032000510003c0050b03104000402507442c44039015120b040d807030f013502c0d0b142010980c0340b400852016a82647c000c1b6002910311010ba8112031144010492064503d05640c5161030261054190502401000c040080e00904550b500003001091a500520344c582d000700c403009842c000c00581c001c1b0004107024003032184a2001600400d4482d50b403162f084003086003140e890140c02039010f8120180d50200400c101030080703860712506d003100f03c000700405400c40d42e410500c0c08d482002d0041425404 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 396123165 1250 396121915 396121919
    0x20708030d0203071e050d0e06071413080a1a010e130321050f0402040c0c11042408010c120e1c0203160b0901050a05060d0605060a050904080d060b04 66
    0x6008029600c001c86418401622503980190917154180000099030307035000c400b2403014140d0b400c00c000d404e0303065032541c0801000b5610703825141e49840c2942c0e5000407510b2000000ca01c1c0810300d0013080301c2220503894a4040e6036421500749000c0003840100ea40c1c03840500400c00e00c46e00907144600402042c4110307442802d040c2c0020000c00380d4a0006010081c20321043e10100f00c056000220070300106008115518200040b101d00c90342c10766013288118101140c0381102c6101c5c92011003416008030a40d030401d21002c003080020300003002039008a000c000810319800c10f03040300c9000206041800403038908400c0e60010b11000c003e88200410310700c0d007004000b4441d8009007013503002c0e00c921144030a120101c501a8034601600c101403281e101080000d070108005444030034040c00900000340135036100c6048900075194112101600080c4a40c0030201040c10754116070340140c4068074160f0791f00c0c2ca80e40412050310080f14190707620040003619240c090024890030009100f0361010340d013064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 396124415 1250 396123165 396123179
    0x11b0503041703090a0b1627090905070b160b060d08030601180b0d090b0609040f0f0f02100e1807120209040f0c030c170907120303090606080f0d0207 66
    0xb07001c168288901c000200000c0d030b0100c1c080140000e4242c10050f0303003000303150180c001c0841a15400c0b001c00083d0200c04145000f101411a2043d004060245000c240781010110070003007a107403000743c4481c82055070000d88220f40c98007e10380c1c0c40b212040401658403a007080360100c00c01400b07440c010b4403d09061030200761054184c9070003220928080f84000503107100e803500310b1510341003040c00541c002109800300e000d9500101e0301ea840f50400007107a580b003074108040240b003110090f008103d244051000240303e20010b140d041c0c03240b24800101c45042c6c012131481083c60244030040b50070340c01c5c542e20301d24003880015005009501010701c076184c1b489000700381003c0c2400ca01d802c1500400d0440c580d5442d90000c81c0c0040303a90201b0042c0030305104004006d0a607403820180829054514440380d240340040d031074481d800120041980074500800200c11a0b10038030240d0806640d400c0d801d00081e04c500642004280810003890325501c42c2c401c0f00d08050681c0002020b641c0211400c014074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 396125665 1250 396124415 396124433
    0x120604020f0f040f05100f090501080703080f070f150b0f10050901020c0d350f130902070b16020f1509122209061202090402061605011b050304 63
    0x41c5050310103000d02c0714541c0125000d48124003c41e01594100820040b100501c10281c90440308800b05081c00540e03181d0b074441c104c0d4028050402d0580002c0414400305040200400c50496204a401c2c600b2100b902c5410b0010703205202250042c04501542190807103a001d00e030813041049843c0d000a0040b4400a006142c10a5800e0103026003c204030905a00130b201680f0900005401103151141e64a013081c10305041c0000c908034411004290040c2c00d01d42c0f801404178014140c0b0145c90715410041e502e006810004000030210078455000c030b50392106001812100d4842d03150308500b41800702c1c40c01f000540e07150719502158001564807141a1000840c041e200347c150540c3d0600e42c0764400d00e607007804411102504541000501c1c5c16890231400c141e0300309203240b80060020b450b2203161b82019103445200e6000032600588445015151902e00c03a90024801410240b50a03950751001e0580300703540c0025109070b5581c00e400103410000c0184142e20010500d0130519614050b941c0c101c0c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 396126915 1250 396125665 396125689
    0x3030609040203010f09080702040f09020112050a020d020703050705010e0615040911100f1b0201080f060a0324060e0903040326040e04030e030609060a0b1309030c0212060402 77
    0x880c00361a808101903440c29485204034140039542885640d00d5414800625480004202c3c0541d29158003405030015a00c0740c82c030380540c16540c03840b16808196525001c4d0401400401c0002c1c0d08000d00130b50021203200804034140b09480c1d0b141c030788070181092800c40d12101c41c900d14a41004081080e10700391105801401c0c00c0480c2d00051103061401c044e070404041103c0150440c00f008120180f03650401084125500c040d601d421103800059415400c1d620b450360002d02080401c000701c1e188240540460764000c101508075204130340e407512581000c2d5441c801c2140e0321f82004d04c0b00c051280c614000c4001600c0080690140d506020318916070340c2c0300d01e100203007030103031000c20401243d640c28100710090035407000f84a441d9038a42c402007401c2c44054800b24080307900e11515121364200440c6207072251880c84060f003440d6075041c200501910000074216071020360016008079410491042c400c1041c065035a41c0c458458601c1404228003201c17107040300e1135200004100060b5a1010200c2e4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 396128165 1250 396126915 396126919
    0x3021e1309060902060f04030210110606012d030203070e04020c070302060919080705040c030c020a030318050a050606010e0a03120c03050f1b06060109050d0209060d0c0b19050309030306 82
    0xa032401080c10b10800511000c0c1009511100028942c0081420318003c1c0059a008444203181141e00c03032820750b0b6100308400444419082900014141d40c000c0ca49841011407084000072503500100c4502d0315280780d141e0150202c0c0c4c2c04018007201d1907101a800340241401d4030210b2070441503203042a501c05051000a2044038001495000da07110309001d00b41d032800d5000c801803015298000203448494074050320740524a0481d140354111312034020703040008a00e0b0064965107543da24124080e0001c400e00d100c204800e0b8642c200002c00821200c51090700450107060303141001c5000410300c1c00080700c0c440c0300ea028240140082094422014401c0340c16040140c0c0c029030318074044d94207001d0f2142400a100c0c010a00c6143c0307241f040140f204007200c00c420785000341c0c0e6440064590100c50f002c4d0700e800040301c51018005007084003c054100e00000c0454a0200c040c4d581c1d504021000c1d000100e0f1404045203488109010b1418030b000c10315036007445030071442d06108103590383c04000d007524 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 396129415 1250 396128165 396128171
    0x1b0306050d060c0201060e09070810110909180a033507120912020606010e0405130f141c02070902040b0a0804140d0302130b1e0c0c0907080103021e13 66
    0x3c3c0d0014001d5011030700510b11546a40118941004d480d40c407004940b0441c5800d005200702c07004158000d205603003070300f4072070f0040764204084071060105104005022035400d120310200c245e03c0d400c0c00c124441401c3d20941e1a0400c4840e01c4450403140580512440c890510307000030400c441800e0f00240e07a003c0030514246030b08800110a01001c0d00c180c0e50040d054210714038103068a81e90101d0b8030b034400d02c400c1e241c2d010401040401c1c00226041190f07490900455401c2000010b032000e00c000d2040350060301804a510311580103075090080740f9404c800d03011a64612040840e030140301980082c8203450003141854600070500c0118818000f0410070004041c00040421441002d030341890840d4208552050f0400800035000b0740c0031005446144020340c03000501c0036070101c00c451820810043d210700018047c040d60f00c0c20b0300420340c00791990040403400c41c11501d442c64018400d241560b1400f03080d5142d0b00500c003140003a41012842030f6402c1e001d80000761503801301e50845480c560400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 396130665 1250 396129415 396129431
    0x20070b0718030308010825050d03031509050f011202030a23010c0e030c06131a04090c0203090906042a0504080312040201141813090b07031b0306050d06 67
    0x8403040c1ea0740030a0749420309444070000c03052581c89249207040e954400f040b600e4600406180c907400c1148601c902c0c05440009000b400b2506004002d81290f40c4a03080105645855202c501d00301607040d00091003a9548904018800742810411801440f08041c2003107c0c006030b4011035101d83d883d500140094103054138401901034005440d0440480e000000c00010b10781d0100181004080c8008034860f1184581406041c07810000312840580321101000107140b8003100b174000c000201176280394550080c040098400c029002d001215103d42e030123150741c1d01c055020000b0f8410080e203468002c03403500c11102c810f035030303104c003881014000c031207040c01041175503201240d8070f01c140c1c1c104994500000c9084088000c9103a1030764000c1d80b01f40c07900e400c0d001c1c0c2c001d00c03000d15004071110158042c1c03c41c1805400c030b003024012032092020642c0007041c0c0c2d01041d140c48038070440948501002991314200211808040d42a18190480c14501404210b02d000006201900708040181190f0b0356203540c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 396131915 1250 396130665 396130667
    0xb0c0a0c21090503072304020c0a080405191206050c090d0302060105091305060106080a1503050618030a050702060903031b071d22060603080d0f20070b07 68
    0x10a0314a560300910601c0c0400300c55641e010961010003050020881021003c03485180119921080d500c0b80d0030f22024214021880c90000c9030180941500950f0800150390410b101f07016019009000b41c0c201e41ea81c0c0c0c41c00090102002c092030321042d840d80420170a0101c15041c03100c05040a41004021a80751200002e4201c54401c407800240d00040c01540c0c1002c05401083c01e60480300c0484011041ea80c50044100d200e03240818000c00725085180180f0403039002d806503e40021603080300150840b880c6a0b11038003802d0030307001075416910030310800032640c00035100c00c001e000000024605002c19903002400340e000790103009108801c00700d004c0c0c0940d142001a61b202c2c40442c501654040c505041041d1600340c1c501400c0700201c0c0c040640480400e80c50507450050301003141e401d00a400c15044110f1300e4014050031100a61112400004607100174058030ac91112843c0c0000c0b4400004190300c12202c1240250102c2200c0a051018034403000703094941d01c0781c02c609074004070342d5031480c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 396133165 1250 396131915 396131927
    0x80702010c053a2003040f0f030e06030f06091003080307030911030111071b06020703030c05011e05150904020a06270b030402040c0c11040e031e07020f09040b0c0a 72
    0x401030b00c1408050b402e140e0110640c011a54899590182070369010300d03644244581d2000703c4014240702607e07860324001400e5000380b03051041c0a45080a440c40c14000080d1703860b80b0545031500080d4008081c09110310b0304640e015000340390704a2641c402880c1d80c1d910406400020549001c0c5640c0e40400c00034030445103550006120000d008020310b0725812610f06007900540341c1520b10f02984020a0b1144040b00340d0041680d85540040c42c24a1940d0303422640c100c2c08850842e203d5480d919038060810100c1321307000740c070180410701007001c0c5031414001040d6202e960101d8401c00b0050140b0001d078594404410554409180c21002c8448602c002d0b0805658500582036502560704000303000c9415001541c09107208680901c1100748281044881d1688a000030f0088000740300e4002082c9055444211144604c6094071709052400c1d110504000100c24002400c1200240810451600144241002c01d08075801c0d17045050685840d04e181c1002802038001e42d1000a41601d00f9010380 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 396134415 1250 396133165 396133237
    0x203060c0c010b210c0108010f0b09060f0a0f0f05120f04020f10020307030e040203060603270d050c0f0d140706090c18060602031809040609080309030a080702010c05 73
    0x14114560340c0505030070700651400b0340050f07441d075401791810700306081d0300c070342039440c104e0b0181d0585000c01401d000c220501380c2d0040242c20351100e41005615040004803001c0c0107615400e1b1517074000c18149a0010b844004510540c4040040401c0100d82818002e0b100b95004500c08280000341d0b81c2718400f2607040c1139805500c80e1301c0300c1101800c0d100305a0000061080780c0c8a0340d142c640600f165418071080e400240c4447e0740c4090107100080c00600001175403a502c0310009500110000300c140b080d42402902d4ad0380d10300283c4c0002e1341031000c01e03081200c028101d0500e0010200d458031800004d09008200424007031a0f600060318900b840400e40280124540001071012800d17a5103110201c0c180030380d641d00c84000d007007000001e1424000f01c03d1b20420315442c1880e00c1d0900c100c80c02c214441800400448409540d5100400403c080401135031184201c10f0003156606510b40f805418004c004240c0000c582c1401c0916a0315070b07001003503c0c1c0e07082d0f5240b030034010040180c0d0130081c00d510382 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 396135665 1250 396134415 396134419
    0x42702030f010518010e1c030f0f02031006030e0705010c1211120d0c09080c01030207050304080a081c0e0c13140907051512160c0b040515070c0203060c0c010b 70
    0xc0e052108413404825051060b6080c031000b0444032507100a00398858202000400801c7c405001800039140070341c01403038895911010004d8610704803203001d4203d070001d40b106510200f0180082c40782e280c1510a4511040c030403402081102e00d4503000900306624200000c1c210402006000001405130030745008251501065901850187d9410710715500020829400303141401c0c08150200c0c010b04d62542904c52041c0a845000101d81c0150081c0d0300001d01202c5c3c510003008000361400080c84840c03c0785229a0f00181d45540762030100903d544420747c40071183d071503c4504000d80030b0020317102c2140d20080c0c903a40f00030090b091800b0001d128104000421120f074408111041801183c0c01c0280c0713508a80030074810821030404a030078019901400d914801020200300b40c0e800342e0b80c81c3d29100d80c0ca480c0009100e0f2459880c00304040701540c048071503034000c1641e04040084070b40c0e401c0d4045610314014030b080d07030035400203035588401801090b00d9100c0020300c1e04c2401700c2904800c80c00c10700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 396136915 1250 396135665 396135671
    0x1104060e06300106300b18070f09020a1713021e0d0f06050a060e040807050309062214030d0f090f0609090c02010504030f0503091504080307030506042702030f01 71
    0x1442014030440a02d201c102105904802d004404031000070300402c2c17200e600005685250741e524540b050948414a080c52050f2080c45800540c140045c580300c000703440307a01d01c05a1600403881d006021050342c008402580d003501e404000030301010700918000ca5030100c60684403600804072907403480e00400d120f5600f04d50340e8402e900c20301140e148000c2d2080d104070000c00032503a60003c3c00080f00da80d8000c3c0e01d02c4891a00102e00030480b2400540313915030055003503034a030515140005245a00c0240c070524203400780000350401c0d15545a00c9002000355a201c3c51072280342d00006510303254080f90200c288002c50f240046c0080c418040e460160810315540c442c44c07515030b04050822a56441040030903420900e90314040740c03060156600456042d190b6200503003419100380e40e150401008541b041c851205400540c000c4451911b000b60b004410465903401d1081c8001d0640704020402802281480c40300100f03c455a90111319094011901c000415480d20009090071010079600c0c00c1503003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 396138165 1250 396136915 396136919
    0x31212200306030c0103050105100809030d0518012301050d23031312030212030403031515171b07060608100c02160b12221104060e06300106 62
    0xa08030085000d001e04408882c00a10200011801d54100b40581600f06a2440c564441c49004180b41e581144c02c440943c0c0c24800801160000c03a941150100209900c0c5102c2003403000f0203100b0342042c400031140c40840c02c0c0300c5045000c002c0806205803400f840d40c24041d60140300c800110760200359076020718012140e550704405556900003415240c100e0701125000500c50120000c1981d00e40c0d0b054000c0c145c2c0e81c0040e80b5003411500018019010315440350030140c255040790507510040e19691131035903610b02c12810020502441c9903000c00c1d41e4041c000501061050b1010300c58136846c5184038190391106a4600b403c081c20040d0300c20a941d01c150300c11404d401c07003c1d811084803441551300322504138407a43c02e00001007805101d02d0021100c20003138200c07040707a42a61154003c01e61262040f1800301d80780740e4060b4900050051b102cbc40c000e02d81038000d92900d03000340c400400701c03003640f055141020800681c6d00310b0120b08040d9001100e5080201ca007803e4040140d60175181e00082044079 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 396139415 1250 396138165 396138221
    0x230f0112060f061b0f060e0f0f06040c151e12050a0f15060f05030604110c010608060c04031e1a0405030301060305160203030a0504152c0304031212 65
    0x340d01e0380107140119130005003008008015554400340c8a41280580988140301d4503450014480d0700005171490281103106070348240108111400c0321040001000b992070503042a04c56610b558124160010712002109071180d48844807610312003000b07010a00340302041e0003d0b202074102c40b840c144864188020080080000d5005204056210106000744018160000017200c40b40c000c00e0046200104017107072040c1f080000c2c581c40340c00540002100b64204c50701601a03006542d01d150301740e448150a00101d14180131a94001e518a13201900301340c1982e451540344450303030705013846440004080f402888480c107006e51071459900040c05081c2481c1c01d040d070300c1c2e910034082c16002c80d0804010600d402011100c0c007000c101c42e40e01a41c00c548030940c81d10081e110240c8107580b0600001c3c4038489401c02e9100741300c3d50b9080c0b01c5c40c00e101c246540d000544001807501c5101015003091008001049105d0141000140a0300c0c140101400c090028401007441c0d5015920000340340891020503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 396140665 1250 396139415 396139439
    0x9191104031103281104140601030f0c020d111e030d0524041e02161a040233040605070201031401150c0201051207030501050a230f011206 61
    0x624016550b0a400716021420f16503204c600f02d80e84500396150920600001c1e000c003c0103603543d407003403100000e02402000004d050350340c1c40a1040c0b003803291406000362580c040c4200c44180300780101c1484500303050b506c00707034481094102400070b004140e5000c0c80000d0051180030800c010814001d41078849007110941d807138129031000c00401d8a030001280c1c0c1c0c9142141d1004400600c2000038101d040741c03406000143c00ca1520062441c0070b800480c685940941c0094241e104211001d007024404a04007a00078621312841c00000c0c2c201340c01408056181d091000c205420113501d10750b50840b4400174014401d409540b1070341c1c0501d02090205071203900c040145217980c001d90301400b90609500041d0450f1000b0f102d0850071011442940c2d1000e406809944d40c882d005042c0315042c407429400228008500303c0755000000d80c2d841c0180107914140000e00003400c4e20b0200e00e4541d001d803481110400d55001049440390302890844444c907845032408007441c45440000384010307036403001801c400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 396141915 1250 396140665 396140669
    0xb0d1a0907090e030d021c05010611210a03020714030304030210050a020c0d0e0105040306050103060c1115010509250806011101020f07150b0d0b190606020c09191104 73
    0x1aa014107003001034100000c0c0912400b1928501c003461502540c0e050100c005d507c02810948943e070700c0c0040c444074802c10302c13940d4000c1000380c851080084052403081e0900d80d4a003011001a65007a000c01d404001c0031060700d400f5400340c01e0050359001d20381040350000144810290080c440081000209540800d03a03500f40b4120f0345080c0300f03e445d00c010342d00a034024a5245100b80e031010824191003440340042003da0201030401c10724042e00ca481d03920542d4400d803c03d41c1e04540b562640c6103240e50010150304031204100c05000c0000c0d40d02022044584103100d1248104045000f203400d03a0b0f03500c0322203007000301c503807490700e2401120080c058500303881140c0e002e01050407c50f58400015060084405200500744514075000c0c01e0303550f811400e075074400000e152650b909945912521900034034006240215202910b03407804002e0051919a210911041e96050080c20030a60b50002807a48031030f0f000301d07810429a9603940c88c81e000d0072404000802402d0904072200e00d0510480c0c02001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 396143165 1250 396141915 396141931
    0x25030e1009080c032205120d0804030905030109060b1009050a14031c0c0204050c03011505161e0c05150708070302010b03100b0306011e0e071b11040e06040201050307030b0d1a 77
    0x4000340d69901005103102141820380032a400c40000348ca162032041c02426881480f07800c0c0b100029444202090841d4046441210341135980d0104c21070031702d00100303007140d00101460601100e904000200c1c5180c100d520800100c0c6031a03d00c22075660b0303424010401146004890a580102025402481c080a01034141e000324609408103015200c07080c11207040c1e601034051100b4000039013030225081da0202640c1884250f4900d80140000c0da60a080910650b00490702d080c0212103041161421516030301261007454500702d1010204954010b466a60350007500107901d038812401c050703000d4412000c080c0d03418082e8102c3d200c0548016400701802d0b070720950458580d170b1789517050203070203256000000c0803250913410200008040d50607426440f41e01c9103030032101000303101c3e451030140060031030448400e41e4000d4013100c40c7c141480b0300160785109100400700c1d0b003441e4002038400d01c0090500e804154903018440026243c0700e1b000c00403154402044040c0f08241c40c408140c10324140c540d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 396144415 1250 396143165 396143227
    0x20f131d0106020303131b240201062301051209071809020f040e070e090d030e0d09030b10030f05060f130c180e030325030e1009080c03 60
    0x1401102010300101d06a031020f400a5145880d14140440390700e00a42d030842c0c449180380c00c21070200611143c9503000f804c80008041013440707503a000840c0b50002035880c504581c0344c64030812400c1720340c0c0c001e080b901854001c2e001903401c90400489191107038003079807203400003c241440344841001405134122804400c8018102420b440d200c81138511045000c2e40c01200c245203d05039280640c0401040510f000844903841d540d2001c03031803c1d400448014403e60880c400b6900e40c140c041c00b0b01e00e00c2ea00d5600c0a03000702c1c90040409458210140030180010308003030000350700c80801f00140c801441d040152200c0044440c60256036921045a401103500310000206d0514681500111807940d031100c0190005400c156012042c070540e10000c02101d915854422404801400114000d003080380c0b1101822090111100101c0c0d014150340b410103250003001070740c41502050544c200ca050300400300f00d510150a20080f0707805201143c541130300001420b10080304100340c1c034500e6070b4440e03910300d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 396145665 1250 396144415 396144449
    0xd020c03061f090f0902090702010204050312040302010f140c0f010506130608060a050a02190305100f18151e0e010b040b070209041b080f0f06070c15020f13 69
    0x400d07500b4400c1c1c0040020310b40c0200140700a40403900400110404800e0008481005d900010121241030f079414000d42d5002070140003505081c8074020b0944103003120b04c0d260501c3c540c0000c008406e440c0c3c1c0c4004000403135206e42a00d480200448151642020841742c000e80c4d0b0b014843d009004c15100e0364410302000b4540055003030540203813030464983d10003a007240e41e1100b00103400380c60020140852030f81c1c2004070300d440c01264540702006204079500041c0a14100220341e02d030510382d4001c0b128100001404009080c0030322003080c240b40100e1000720f188011001ea04c0864100d5400c40c48149440740c280d4400c00081010300402c40c0e207030710145211a640c3d50100040da00c00c5009404ca0360030100010b0026003040300090383c1051192007118a61241c490802c0d004101e142c1003500345420030107886002901c20004803031100c940e98003401c003e080400c805000c548e0b100000911202d484001e070148503025605551200c61000c803161340d40c412403603c500346100702c0d00a10600a680c0508 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 396146915 1250 396145665 396145681
    0x5042a06090e06032a090f0f070c05030301141f1701090209010c060207020f22140105090105150705011517010207120e061608071109090a0609080c0d020c0306 70
    0x45401400c0c00703405000181c001600c0c0c1c200403080d51264010020001c005d07040c250302e0304400705104a080c49038610311401d1010340c01794401d402401407010007140f000c0c004085900030040320304441134070000141005011021a81000d080300951001a12041940c0003007900400036000302d140a03400250300d0382e2a140c1c080100d001d01104140061802c003500c80004a043d40184081800201103503440071010700007400d4808442168014400700b610784051042d060b0040302c055090380101c010856044c04046007401c40c0511031f140c80754113070000c00c0c03200302080c0040740c12040e0424000d00c1140c40c048003a0340341400d54441c0016041480395001e00c00c010601c01e942d92250701040d9101c94407040c8070103da007041010100c5a020f54200000400d150720034004803009442551119200d5507036081039541c0549100c500f03070180500400300311070740b6004103514084680c001c600249100c0281000b0780180207108608900c0e2081640f850000c54001445542c080c10841c00c40b40e00c0c0c0d4813190 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 396148165 1250 396146915 396146939
    0xb070503010b0f030c0f2b090b0f22050d26070e01020705030a050109020f040905030f0a120c0804200319080f0304080711010207030b070305042a0609 66
    0x2150080d000340070700814401a58603c01036800401c4054091b08200581d00f0303058085d40042ea40e031903c1f00c0141c800300103219001d040c851201d00c498108014544054070f41c4009500010070f10020000c0c41d40c002045c1400010080b82000c04400a0340d15041213481c246984009520441c030105882550744030a0040d14490a01104000d10486201e900c440c5019a81d18215502503415030065000200d1140c4003008003d450740e00032400401e28410600501040e800d09603007441c0a1410900d903500415800412280100040c0d280e2954134150343c0d1003103030a000d1200e02c7d419100d00704200440740a6101584038044d501403c03442d60701196044840710401c06244019030503806c860080ba2504003100340b101c0b4140c0c01400b21914003825415074078200c0e40100c4048032200c01c0400d1440901c604032030102000f0100780000c01210317095441e100b1a6900040c02c2e20201500c400003d420424419109161480c403100c1490030388200e0546091102513900400c03001454800b800908409404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 396149415 1250 396148165 396148169
    0x6030c03140f1f0903020a171b010c0e01120204050a0905060f0a03200105040e0c040f08060132090408090301180804090e0f0708010b100f17090c09130b07050301 71
    0xf0120901c200300408071024000c4480b0503000c4d40900308912001c20b0303140e0814003140310340080881d41c40180c9a10010300044c031240c0d0403071982c034120351040d138903420075113406040700d0901b00f500c0c25072048486c0c00040e115507003019401c004c01c084000384010240c2c00540c02031004071944600a01000c0a01a00390490300c009481110302c804520b01c448450501030350f250006242c540e00d455283d50090300301407001e41d000c103c1402d00080400c088070707051400c00007410000010705106c0d40740544489481000c5040a280c1801c1c3c40b4008401030820084040d07a094081c0c100103252404e41444c003000d81000029030b0003542040c00c03d11510782c89c5040103110a07441031074241032074107018810005003444c1e8000710b1584200100b06034010410400c0200503c450400810a8803c6505100700408844038141c1400306070152100d0350358000800603406d84030080029115510b40d407200c3d02d014002d50550760061146c0c403e116034410524a07848045002d2402d01015441d004411104d0784024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 396150665 1250 396149415 396149443
    0x4030311091008090312042102070617180d02150105120a080f070b1602120a1d0a0504110c0606060301211b06080a051b071506030c03140f 61
    0x20402c1c14480da4000c10001c1e400059203001c91b4101900c030201c0c952070f0b04041d40d066490669515240c0794400e030121501201e80208c1c80502145803074804090400208512180000c000c400e00080b480c00f21401042c216000800499065100f51a0065143ca0340d6412407464955224004900743c04c0c0200e501c44070000180c000c2002c84032584030030003e0303000098070807001c602c00c01c50b85010a044d442303414060f0340101d0b9181c0d0300c032954080107031070120341520424100c40d0612031810321079000001d0038220300440c034051013140d0f6554001508031500c2c0d040554000d140902d040c801e0f040280203410000c00c4031045507400e1315260704001d6a40000d200b10001400000b1b52600d0b100c00508840c0d5103144035030b0b40c00c1903013507054111209550740e90300444001000c400070001e1000080c002c0700e40100c0e1030030881155201c031140303c07215481802c5d4003070301c40c03440081d8000400360503a00010055420002c02d03513540f6100c0c613201e1103000b210503103034000d8030070042284421640400c0d04180e040706 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 396151915 1250 396150665 396150679
    0x60901060e01050a21060312030e070f1806030506010920090a1e030b130303050a0603110111030c0f0703031403060604050f030f010c120606020c0303071b090905060403031109 77
    0x40013400b140c40d800c129200708540c40c0038112a01d0161141d00990000d1441045400120a610710300101280d00b5400302124540c006601040714421070380e9104240c0704003e01a507401c0490030803190203040e15903c024110311908000180d0b0b0314590784002c40c620075034420034003050069560003500780198044680e00c00644a82044200e11005c00c00619201307d21100c44466542d444d50f01c0c0c1c04400b11b5007840c2c09059086280101541485400d40c001c60031501045642e01310744038041103040112106041c00315502c01840e04202c1002540c40c02d075581d41c00c5481540c6001c0c00c08d500c17540716110840124400866000d03c88200c1341c10b80c1e100d142c0107060303182410703d007070200642c0400241840d83c041c004d1440c1940344040070300626046140caa103034049501e2400000358102c5116a000350210341100c2190b20352540e0110440da0203030b07000200d01110950050340303d281c01c010f0340d00040040c1d15002d0030100b040390225006110318040d841c208030315109001444280e03c00c8481031980401 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 396153165 1250 396151915 396151927
    0x110115060c020a090e03072f0f01110609030903120309030f07020a030b041103100605030c0f120304060810051c060c02030913060306050105010c210c02090f060901060e0105 76
    0x3100718080007050b4001016540c00c240c0d6103941e8421129000381d490680d07000081c150090001c01c110000d0b0f290200c2c08484a41d00040181c04840360600040500c11200403040010980c481c0910122500402095580724145a50b4050740e0b5032001c0c4126000e4011480522520404042038030302c65190940518a0040060000949680402400c030780c081d121103408000320b03550051180c802c40c40740400300c05a4101030105441d11492000c19031155003003400501480d200459030700050141503640c40910515240007e200e00da0602d080621b91001183c00550142d0100c0407602a0410044944034a62940240100340324007482075071040940b080301900140740f42c0e200003000005407058a0071f1810050001c1c550800b07201c03945003019180da02c14810b2050301c0c40741c02d00400382400c14490032070283d59940c1c94140a020005441c1e000300c1400511107028a13804407186500401e00085403800d112001d20907507066030514003541c1e012001240c01c900540c0f0800c102c0105865050500c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 396154415 1250 396153165 396153167
    0x90703030206040b04050109060f0203090c0319030503040c03020607030f1101051012230d090506120c0c030412030305010303110d05040b220303020c0306100509040b04050c0a1511011506 82
    0x2c090705c00c4415640e200815804251580700720414520070300f00169803070034480c9140b0f1400f08081c2c41d2500c01c1d0007a485403490f044d500205014442c3d81070526a80325903850500c1e400716035070b690000c0d411205c0011014101684580340c415071201641310b208a140c2d071080706e00c1c207e4100300c400d01000e0058200074003c905480d0100020b8510890201005200c42828401040c480c4010012903901004190007103030380050788030340500310a0340c5003800c2054442e107000d0745d0385010b404000e80704000500302902c000248200d230054015094141810045450002e004020901c415400941c080001100c5000003148121040d200c80e52080d04007818440b20039202d502c81e248e072400380e183d80c4c5800d0301403e150503d200b0003140a90041c00410100b94141400d1103c002d24506595034415002e01c07642e59802e0130a41c0180d005809864166200e19207580341444100000707900001d0a800000c4090300580300c181c0c249080d64500b0504070384014154240c3c2d0000403410040050f03400244911 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 396155665 1250 396154415 396154433
    0x303020a0b150a080304090c03050903180117070806100302030402011713050604062c071802041d060f01020c0906090405071208040f06110c010c0311030a1709070303020604 76
    0x2112100041500c045540003c1c41140d4154440b5880da00f0201c0c003001582c07070f14403900900e00d0441c2800d01551609400c1c4540328440c000084850022194071092241d12414500710480041c0840d241581400100542400030844000d407081d043d036080c6200c9580b082c0240c030301565045e180c01c0420130220031201902070000b0489055a6031006600d004500c041020038040c0b8000d41002520030110b2540c1303045100c64900d000c00124034900c0d410805440014072008407581d0300d1810001002e401006006841240d210b51990152546e000d0450f5503514a0b03140149012a42c000c0006443c0300103985880c1c1e00296a540984200c0010786103080a158031a0300074803031001d0391714031615095110010080c0800580701e140c8042000d11003042d2940b544030140006003415049100c3c054503195441451540d454104071016041f034081500a03204201d00121a005403a1641811032009112940081d9144d00400c0b030701011850b030321008218041074a4165001c2e00c0b176584d550300d07142c00c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 396156915 1250 396155665 396155671
    0x2104290a0b0310020d020903070503070302090a090c0906171c050915120f07030b0901031212271709030606060f190c0209060102010e03030a1a040c0c02190303020a0b 73
    0xb41c081c0b5400111104860320041001e40741d03d1a0050300d03285400d0034580b811160b508024040d5000761002d001603624152a43c4d803152103500d010488410720701d0702030410500340e4031100d61103040020100d104414485403601101503002100c3c60f0f910314100d400715440c0d4052030311010510401c403600590030040c10328002d800411240d03614280b00940ca003003e029040750303c1c2e80b88a1050041c480724540c1400760f0b16031a04101c50442495055488040d41080742c050352005010381c0c22070303011100321036070040080c910000f0184140c42400d04100a09020300a10455078002c00130b0000c0002c0c2d1011055444101004e001081d26503510414041070340d002203031900c8215810311181306c15445420115808003901e45d100421000f2a205121003040040e02160559051114400e803d10303000003901d40c800b0500c41c01241810b4002004102d407031041003243d4000e410721061380390140e0442c202c026203510968901501c1004001f83c0402e515050100500580011030907001040e01d00c642e00350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 396158165 1250 396156915 396156919
    0x10e0f240312040905011805010303023a0809070503030c070504150911041703120a110705030d270803010302040903110102031003170c1c052104290a0b 67
    0xc45046403500c42c900740e042a032144903021789800042c4180300c1820840b00f50703115034103014040755045a80c0a912280e1a095280201104500c000840c040f440500401c0305065000c1e00215455110000c3c08850100e519080d0b9209032200014207040000840d07441c075504802810404e0b091508110103008101800f007164042d82e0301c04100803080c0d11803c90072040511406503660f14000900741040b1000028800035002800043c0083da4074411311940301d031082038001010412001c40000c03d01803c0b1016080b07100c081486c0c40d042c82c031540400400c900070040e040c1d4012000300a00401456031000403c485824801040141070039004241814440d08001d04554803a150441c00c90700201ca91350304041105408009200c404801c083c11072600c0300d840f07450903441420050340d410088a19981d602000c0c20a2107525218200b543e0b8010400030b5001c101442c1c1400b5004050001e03102078804040001c21a107000740c1c03188081d8550b04034170102c01d02079918008200002c14081104035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 396159415 1250 396158165 396158173
    0x90509070f060306030b060406210519051005010f0501090e070306050618040b060f1c09050a0524190903030e030408280302030304080c010e01090b010e0f2403 70
    0x124001c109864a040941456600003c07200c0c03a5090080c03205d400900141c0c003580c500079003444484a01c41800080070300c0140000c2e10702c60a80b5005181c08080d10b802008000101030410810101091980074540c040318140301c02d98841d800700c0414030942c0f161501140c16400100a807540c0503c80640c428130a04001030032a54600100f58135601c000030608515010510028580ca000d20403841914025600c0c1400c1c42d26101401006101b8020000115030744031040b1f1100c1119908071203131559000041d11550522413500e584c1c2c03905030b2603c54040f00110640c00007041084441079120b529008482c8035101001c107595001030071005401d408068aa107071210b03c0400805c01800246001002030a88604140072000d00064074418544452480c000c0040407940c00016290040e0704071078406c0d65005005a030a00501c0c51400046e515403d210f064030901126801c2c05040300e810454a58a0b81d40351408400750b600202c4034000e0206a0440e5050310001c100c0c0b02261012000d030441d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 396160665 1250 396159415 396159419
    0xb0f130311070e010909031b03020705120307020d0614090d0c0210051303080301050102240109020f1902150a1404030503090a15020301030201030b060a05090906060d021605061302060409050907 85
    0x4001c81035801d810105800d511091506c007010740c0080c40c460403000040c60940000c0d400d6030003e44a1440e0310541d441041101d541642c446c10510403150310030b90003000c111002840d440c0000c0035141c4012071011840f60600059250300b40410503445012845e41d519000032000c0c0e00b00504d481291089004004060000d00042d2940c07009403001365005101c00e903141d40c900703000246000441e1981c0008481c1981400d0062082002c029064405c00000582c5490070601c1007149406281411898401c2c51602c0e0030746c20f030b000f00d18010448042a42080d072603485103072040a917160f9894001420f42c00d00d00180c0400d22940146400c101c007081926042030443c0c4890701081194142003110030b42c000010011580c05210f1404200c17800c3d44c0c02410f22402e20720151990103640480b60080d4414400130f0300c10741c0c81004941800300491011901c2d42c056041c0070040090790002100c0030f02c0b80c00081940c0381c00c2032184000c484e074010601c074500740c00e0840c41d00140038041c0000005100340c0c600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 396161915 1250 396160665 396160679
    0x705030c07031709010f11040501050f0c0c19060e0d050c090a1b1107080708031c090209150a0b1e070501060321082202190b0d06030b0f13031107 64
    0x3c2e020318407080010940701001e00c00d5504445070810703a03070041c1c68100010051350f60002c0a5070340f00115107001c5510740c0700f210810707810f110072102090f51002030181c20381e0001640c82030b600140d440c6a901d0f440646d01007000d005070b244400c0b00140c016031000d900d440b00752400303210140d4810b0000c5230115604140410121400724001100d502140540c440c0304040081000060000d01c502d4006040d100e00e800070700f03601c07840f038050031400540051414018070092900090704d40e5038050210159032401c40d00100c10100c407054054800c0002e00c00009050840200307681c8180750b48d0400080c90801240308031010381c44400100d0b0503540324100000400c151304000181048001102c813446c03240c011000304400002810700e068400714034901f004001310007003003104180e8103444150042c000c07590b80f01100442580b00119075000012000c01d040041d07008a030460b1300c510b60308100e40d100d50b88001c00c2c4180c2140da00004114820105c0c002c00e2090708408201201502504c07011925100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 396163165 1250 396161915 396161957
    0x150f15020a1b0303020f15010e040507031209290d09060609150e0c040e06060309011d0c0102070605031509040212010603110111010911012007120b010e0705030c0703 73
    0x4100001d080034803020001e050f0140030603460006101b01500c00c0c61401500c41c031001006015064007429041c000504006040000030b01454202042d80c01030080864004e0211000d40515410910318130080202612090b6201060031400c0712441d04100c548120040200000ca00c181e8405494900000b80040944640c1480c0c003401d00e00030350030b58141507218200720b02c0600800315201003008100a1b90302840092904010300711175407a0f59440e50f142c0079025204015034104070070401844c80301c41000c0001d030311010000030713001c3d5110503032b940e08181c5542c082141d59241a111042102d403162805c02c0c086540107200502c1d01d50030710030004606007150043e40084810850305140101151303004160700401440340720090160000c1540d0f402c000b0041441c0b400d0501c054120f10042c0d1154103c0a10100d0b04210b0880380c2c010360302c10301c4030300307a0003452015503400801d00c0010561100030f01a0070321403000c0761aa640b46490f680580c40c0c1320760020b0b2094040207040d080800d0304038500301c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 396164415 1250 396163165 396163193
    0xc0e1003032d0e0102030904020403200a080c060a031e06060e0105041d0a0e0607030501090b1f030509190c1701060f1203020a150203040b0c030613150f03030210150f15020a 76
    0x7515080c2d0324000100d102c0d4100461248140414dc03410042d0450004403603150389010740b081515188900015070240c03c5541c220000c03541140c807510008011544808110b42c2c4541c0c84ea9501502a401075605d403255000e8000d5440642e82d25180d1040c1d02000385401502d032110008134540c00c1100c1905003001a5005c600094491004001d107140d20300400c030304040200d8804003405400c8520700741806c0c0c1120404107164940340060100041800801030740101c59411031114811840d24618030541409020740480c40d00c05143c10700501445804240e5078181d00000141d403c0c8038030b00a12001010f4120214842c8400610016105400350b102402e000b04001d602c03410245003800d40070340010200200300400748201f118580c0c0e03071042e865400c004030f10001a1100c0c45181d9200d034000a8004c180c091a003a2030000c10181c0c00100c1c8084100d15100c20040b5414206418840301d01a2090001005807000244040c90352040c2c01c48900b02180125610000540d071000360170b516034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 396165665 1250 396164415 396164423
    0xc08040806090f0706140904050601090519170a051905071d01092016140105090a2d20041b021b18040c0e1003032d0e0102030904020403 60
    0x1010800d0f00a501000381310050710b1a0300340701d100c0d40d00355041c1212034060041c0c00c0e8407564907840810302030790107012000042c0c04068451060309080c641d500d4a0045140304170481c00041c401c00104000010540c00f00107a4400058524803003801d0312425840c40c040c4060361140140000020860300080081202c2540034401d09461762524143d042103031100c074214a800562030040340403140e40702c000c90b8200c2c0b501c400700360600c40003410132892007904031175418a19807a110500c411070000040140c8564800c008040000c01038a041d14183c005000c142842030256029140c006494482c11008804c0e441c10300400c290710b05000070301035801028203103000924a07200d842006a0500c03555010300c0070340d2003111240f80b010012425804168504103001d02220313012a04004104038980000c1c0380440040c8541d04140120004003180d9210840105540e905010811b14001001500103803464901c643d802000103804d03a02c450303854010a0440c0003c101a1355036654502c0640051402 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 396166915 1250 396165665 396165673
    0x1e051203071e050a08010632030f1003050316140d0c0b15010c020d170d0e07090b010e090a1b0315050102030c0307060902220b03010b09060604060c0804080609 70
    0x1910a10b220240300824690411008128042c0c845800c440c9485c1100c1c241c0c035160041070303010300801e18003681803503c0d5042030258414201d820b6983c503000e9070064000c030000390010707115124128440740c540e110007013440e0824004c1c51208690100391410380341c021b2a01d031000d02d909c03c403481d04204251820b00089660443c1300b00c2488444200164400040384407202d581100f0310000c0c01e409030802000b84602004104102000048900e004d2135010703046010340c0341e1410070110000f82c11054104032041c810b181c40003e10807181d0154200c507200603115090200c1400c0148080c0f844000c0c075008042d51200c20103030001040b10b4110408c00c0c040e503800103100c0611011140030a010741c1c004c9046601c14860071400a80100440b07113240d0307100d40c000402046e2440412035262181046c40c1000740100280444e041701e45d0001000c800d07044000f044110184000c01400b45010b807005a0130200a11050081c40d028440b00c0f6221030296605504095582180310700d820f504660706401c5400c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 396168165 1250 396166915 396166937
    0x120f07030c0206101404090614041b261c12050609100509070e09040311010b0301110d0c020309060a110f03030103170a120f0e0d05071e05120307 64
    0x80d140c400c48684500718400f0f400d0604114409040300c541c103005007140e0a4a9840d0800c441d038071031380072141d00e40d4404002e20206a900540845510781140c06540c80011016007003c3d0201484000d8181c5a00c00c0740840041c0138001c0343c1c80c400c401c150940c2214452000d0400c880c844c240000e454500703060350344042e0319010b00e4000d01602c801810147c051000103050082d040c1f1664081d00c02d54401781ea0040c1240d0b00d0200841d940742e0607000f10382d008043d103001e0005141d413105468400c01ba15400a10140c040301c000d1500300c0f030a024800600c070805101081264140c0d4000072000c8481d44102d03820103142c48005035043e8410035810010640100102c82249418031001040d07200843c09107041d5859a01d60b080b00c000c2c01080035490b640006100b286090144540a801d410010001c01c000c040c0c0c21000001441c210540348141d10540091500c002e1140c01100d4030150301040c80511910901c000e01100e043c008411641c1c1c3c0242c06429115101c04000340d8420358495643d80c1c0c03550 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 396169415 1250 396168165 396168167
    0x21020a110a08030c0a0909110301050114091011011e09020a080706080c0a1e03090c0506040f170106030209190b010507021c11030703061e0c080c0a05120f07 69
    0x140048404414942000e0440e9002c2602c01c0d00383c3c0e034007401020031030740c4e10b4195800807100c81d80d407900300740d007101d2500502030713041400c2d0300195040c0c4100b0b80700e12001e80302c800012071050080452050f4032601c2040304800c00c8d071051070b000300018040c20010640001440355078500c101411951401190380303a01315400d51500d507811030005e001c590050314071103080807170040c8001401016140b084100090f549109441031031031000448501d2040b40f0001d11892000707002e4210304505075039040c101d036004180c1d89072541c00c0340c01310b924a12070f2812051601c416008104521049c00100395620300000015840380b500d158814000042d03800210403521a501e000c560303151001d80d04201d010300008005803642e05071504404141c00c0e16a203a0181707403400288038108500c202d40c03d400f03105c00020403c1102d81110004064444881c500c1140860f0706c0d000715a51017101e50300090301e07003000c55090f0510800500403000c00e031a0040c41e000200c00109880c3c1c5084d45c04000403044d48040051032 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 396170665 1250 396169415 396169427
    0x20a02040c050703050a0c050724030b0316090e01020c01091a070e0d02040e011b0302120606090117070c050318090a291801080c01020d020a030516020121020a 70
    0x80704050902c24188401c50310000c0c624040d440c10201031003c12410f44050010070030580707005010032803070a290b044407050301c00e04154400c841500828180f892104d014a00071580f480c45403450b442900d141072601c1c0502000d485090f00012495500b0080044e03072820031300841844600078030f003075888003011916000f541c01006184a040280d01c00307a0300540d40e6034149018010b03404a80104500390701201c841d00600c11403061035642c85010f40e58401d56a01a0045c3c690421090840140b45c2d841c80d0522840d881001200750000d10301240c0c4901c980208807040f90000001d02e400d240301242550780e1841c50344a6101c020703001060712001c0d001c91a15104156000c4500344042c4102802400410003040f92091120316900da50710b420101034580d801c0010691445003246a01e07960f5443ca4192180c80c440b078420b0050081070020b039803880c0001019007250b07500d50344040ca4075000c4031400021841f118022410001c0444504d40595480c2e108481c40c105110401640d4680000009d411 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 396171915 1250 396170665 396170681
    0x120c120703060b1603030212040b0a0606020a0807031b08072303070f030305090114010f0305010c17011413090c2102010e0d060603020a0f0305010f0e0d2d020a0204 72
    0x815080001c10f00c030400250068606092000b246120107a02d503140a80181c0175910031070000007102e00401c02845150403940d405049540c8082080a840b4801261550764212000e0f04015040080800081c0301e10902c002e002001403103141910740e581c2c0d548081d070340802d070150f4065418580443c8404a0b4443c10400405010000c500d0841e00740e44c0c500b00049850341c00b03014156143c1c00240c070800207410030000300300300300d92903801984c5503010298460018002070f0342d00d42c6400300198149000e0031000714800d54494565a20307a00c4d200e0190600c1c2506a055600092a02d08030400a6028060300c0b458a01c2500c1407a55a810046404100351203207417078149500c0c0c15406000036076040040132000d0b68050700e07048401c0000f41007440141c260355100a40000c02c2440004500d001079000c041034a11401c0240808062114064203440c40b0403105601c40c2c1100d00300300c10740e5006442c000280c1200d002c294441d8800100102c0909601d028000056040355203900700b1842c041c031036462 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 396173165 1250 396171915 396171917
    0x40f0e0312040c0b0403060e0c2b060e0138010503010b0a0504050405090a02191206051302120d0f080f010501110f0105011d060603040308010512071503020405040f1103060d0305120c1207 82
    0xb01c2c0d0403560301504591b03062b44071020007100742c45041900b4040d0503044681844500340087c801c0141e0b00c580640d2403402000c81e039010300c07072010142c0d030001d4070229150201d4005070750319800e607420103010f000160b001c400080c4c01e210040100281d00e884600596100b5002e023005400341d142c035401801011866440a00ca030405210b000303000f420041c040010b5065088100021560b84240e1090411807010300c0181d444089412207441c1070300005040200a8520f5903001108050540e0688040c1c10a944840518811000600c12940f003102c101a4005440b0111114000049405402c444081c1c00008145650340071400d102090a031415402c080d080c1c0da02c529514087d00c00411945044c00b1302c1c1d03c24005802c4454110408102410181400341e0f141041040c442801900a52041c1310b40c034007c5040c4840c103030180c26248600701406811281c0c4034550394403c806c00110224010003203091210501c1030081d80e021044c000b62207501c0c040d00f0560340d5292000c0c02c01e1210341c010b20000c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 396174415 1250 396173165 396173179
    0x136170a05030f070309050a0b1902010507020a06050408070204060e101409040b060303070c060e1e0306041b08030c01060518131106071a0105040f0e0312040c0b0403060e0c 76
    0xc8005440041229100301440d0b581c140c6401e80d511301111030590691006074406003c80c0c0201d40255030030002c02c180c0728103d1051480d010341d0300303050b403d03200115050303009a00900390040c0401c9554112a034010300c01c0007094600074607940020222105500310072040d001c00c04c104040364101e06c0ea0705001e045148400440081d45800150980310028402020008882e011905a44003041540d422503808822318406070340714000104007031011012284204580440c55000ad001540e41aa5030030340900585020303581c0780c40c4c58507a01040042c1281100001c0000550f04c0400c0c0060822031848000114440e40382008100f0b480030703a02c44481c0000c80c0a414012030036680103c404140e07a00148074200c48034014005000d6000381c100141c545001d2620f007400d8920710742060b6050300d074200c8081180c0b010212000c0c2c11200f0030050b0b41c0850f8010029512904103404c80c25500c00d00c40c0364844d100300c2d2540b074034000c903400a50080b50780075103580c2d580038108020700400a128106136114 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 396175665 1250 396174415 396174433
    0x60905060907420e041b0f0305070519030e0606090c03011404090b010914070809030a0e120106080303150616140a0210180e0601090302013617 63
    0x220100d4100f504100e00f0055101c2000d1404030380540441042c150741503404854102005051341280700501d0341700301c0c41c103504110b40605038105000601e0484d0303514408200d40c1c0605600400780540318a080c03103401e018a4020100280e80075030040e01942e008034000c01710214440c601a8054a2148511140420046102c2415007985d0440b09180c110110501e19000407034020a00c800029140081010000c07030f1300c1089070009c1c8112400b014003e810b503618003108540b01c007070070781d1078904940080211ba41014401c1d8019244034500801861890040c481c40c4c6007140e103140e101050a410110030400d546071351483c500310340201901d00d01d01d000c1c0d00074a84981010002401088003e20720711741d4844440802910403440d901a001b03c40084c0702c050060201d50300054004161050000040b48a6108086142c054801a16034220322400c40e401550800c6110304868040d04115140314100781105461500c0ca10a0410740c041107801d00105401000d403c080c000f40a034010001c1d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 396176915 1250 396175665 396175679
    0xa09080d0c020d0c05090f06180f012c04032309090601030c030f09081b01090b060105031b180112020304050721080408033013080f0304060905060907 66
    0x18a4901660450f01d501400d0340516009a030034860303400250304031440c202003050081500aa01c0c0c041e4404035040d902069190445040c0c401c0c00b100c0e2a0142480c0340010420998a83d440c6c003400701401c5000110352a800000040604c4100c0e42030303001448980c10250f40340030089144214100c0c050f803543c80c2a0702d0b40b0108441250151180b41003507a104145111107100c1c0d0b0004010b0403141c40107109950b080e0404103c00e40102c64840b595005840307482051030014403d01a109612443c1c12a899556600544054100404075100c180f01c0900032208004454001c10300005040d800d0804c0741040000148070040291041c00d03c1e920400a20010900000b5140c0444600b45084d88074007640950010b10510381080c01056850082004034203060b0100207080a24510880464020441020a00e44608500c170703841100340c0380342c085409400c603043c01410050040722141d00c1e00001042c2c2d41d599074070444007620b070a82d4440c0b07801c0400c00c0a00c02c06070040c1c03000f8010981c460420714 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 396178165 1250 396176915 396176927
    0x70c150c0830070c0b190906091e0c0b090f0d06060602191e020604050a09050415150605030c21091b010e010c02040608070b0d1119120e060c0a09080d 66
    0x7030310503141d40000403280b10382981010686c148201c000e00c0050100d01d03200c0007a00c58414101d034ac2c5040d202d4100c00f402c120201d0444030705c1d00038070303c07108172443c0000048080d4007420741950410000480d140c05501e6009400080500c00d6070005009482c0444c001d09140ca000341c00042441c0c040d0b40800415441041d000f03500e03014243c0345446091610020f41580301d40c2c1e10281c0c104101300400141080b241c4c1c80b962080303001707021862904041101060458002c009035200f2780c15640b0050054074403401c05542c0c414449445145460500c55058100c04c10520390b00880c1d40005003084064401400f079100c1c01380c403001e0040c1c40c0488040018080c00f850303400c002e04106e80794000005554841e0400802403502c641994a42d03a2a4020750300c6940c800000c0c03400950900324140d0b62032207504121550441280190601081600021100324420710010100e0a4449803243c0103046d0502496000303201c01f1405981c0d034a079550002d030080107984e12003102508214812180240c1000e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 396179415 1250 396178165 396178187
    0x729010902090a170705130f050c0f0304030507150504060603050d1701151404080d110f030301050909011407030b0a0e01080a080a050c0105071d06070c150c083007 72
    0x748045650101c6184c0072031514200340d010329400280d440c950750000c0000e5020058400035150240407968400700500f040784214500d101c2c900c102000040e000c02c0c07040d8068612680310300250414204800445000d644003610b081d250181d480c1c00c03c100b004010000c40c240840b4505018185c01e030aa06803118480c014480d9050241c6841c00007602288074050380002491503420b41d90725a601c2e8905070303607128000fa00143c0450050060030200c414000340018185003410025440c5a00b0034003400b814180c058611900e075900d42c8007001101c83d0303101c40c0b1441410a80d400144c10041d0104002102c07000790b20001170010789000600c986180442e045201036007120510fa6150b1840400b280c2c148540310207039446510745014041034682c403c841c40c26407a0340008840300b10080c01c040060314400c03980024540f1900000400005c0340d50300402d409010035041c80f03403000070300e6107c40d10207600c02900440c218401024907005a4084c014544a8a040400301c0c40185031050000c3c010121003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 396180665 1250 396179415 396179429
    0x5130201050913020315090c0408030a0e040b100f09050f030c100c1e030201060b0903102a09150806030d052a1f020f04030201140729010902090a 64
    0x1516074210789030b0b8844007140360241a021541d03850002040b805807621783d2403030b501c40c140d47c2002c52420b007000415141950340d06c03406146415900f40c0145c07010445100c541343c1240c0c460203050481e540d490f041011004c02600c880901c0440c04000038560081600254881d6564298007060b80e03c1c00a058241c014043d98413041c1166582800d48411041410052590002c407011900d840292099418824800c1d00240300c225120500d584090080c00d0031207030107501085454034620000e130810100981d810744003c0d400440000e05981c08c210061480c2d001c030324a40810800c5011540d51000c0b0071540b0b10b082c8810b4186900044d0301e0301d00c511504004c010021590940b40b6950300f040da1820241152a501c20600000724951101d0380904031b861202e85d043c1c480d0440c560140229085094401c2c0614549800c650055400c04290507025240c40d20034843c0702e0000304a100004185c024640070f0b929400300c2405c0744044510140c0002c401c860041c030600100340c407000d003010140d0700c2c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 396181915 1250 396180665 396180667
    0xa180902060f0318060c03060108130318140a0503010507020703082b1b030903080a1e0e0a0c1508010504050702011b1805180408030601090906060e0a05040513020105 73
    0x1030300001c0c00c0d0340035140c0c2c00b280402e80001400380401001c2c442e104100800030544546030703942d0315010198002120040d000c9501e620010b03131b4101d591140d83c6000c44c440d00f13060100141111080c02c2c40075080d004400808100d000d114030302c0c9004030b0f84d9002804101d0090081e854032060003034070707141e16100080c9440d50100b0000d1070f2589a40c0383d486140aa420704139414030010841d00b000e010440410781000c14400030340c03003101d88a4011246842d42507140d04000352600c11803d0010b1a1100344000f4090184901008000550180780c0d9088e55110060400e0b03040380c14400ca8980300e0354000c0b1980f001e00c107003001c0000d03001929941184c408035000141e40d07641c030b03805901414004400d000655040c04e0040c00841c1c01103001c2e5101d00f01c50a40b08002c5440b801400002040030580c2c50006484800113800100c01e00b00450380078070180b6000e0012959107440f003007a5412900300101044071001c8103681ca08051402038020300040707906001c5420f154082412000d4030080290400c44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 396183165 1250 396181915 396181931
    0x51617061515041503020307030b09060a1a0c010e03040f0b1e0d0627060906060212090406120c0320060702040504020103060b04140a0b07150504030909050411010801050a18 76
    0xc016042c1c0f4014030200724042c541203001440100250310458021020915003865a4020304100748a00d1017100040d0100c42250b0810364240305e015a6004c07071500014040141c2042041c00b8040d40b412900368030021074030b440c14188941d0740380f003003500a038250381d41c240710b016101d07500d03c06000361024000032401d40d101481200b0b90054960364000da010300e0031240341010b201e459281c807103000101c2440200b280a4071100008181c4031944281001a404a13800000e000c10002c0103002143c1c00510024080d551035584012110300b026050303440103a1802c0400a1240d2241440320389189481462030355000040064454010440081d000c0e50f640c40004045900a0348408080d1801030a1a0340701d550340c4214207645071600d00c0880c040c24074848001081a0402c007039803202e41e40711540410ba44001030250004020080056003000b10f4910000303501462442458060b601030142260b4090149002428650040e13011070f000c0d0312191000c0000038101079034051148d11000010600700c1c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 396184415 1250 396183165 396183199
    0x130b09220804060203091005090f130e120d0e120a050c0c061602010306080109020f1507021003061d0c0307050c0102040302120f101a1c0516170615 65
    0x1055034000800920001502040c1d40f500000580a1020100c8413140752a0510000b1686d9000d007004d60354021032009140341051501c0c8103465401d5a81600000f0f441c09212103182c607004100401884a080014a0900c44121801401c0401d0b5a850041c100c00e1040c808a821038441c0034040c504114010466001d91001400103082c1c001000788919190248120030320007000300c50030100e0200c4c3c40c00d400059404c4044c0a00f5100301d030014104080742030700c3c00501400b4101070740a4000d42d0380800606006a5170071841c82210021940c3c0000e242d41046103280c841c400a0590002e8141000100b080b044080d0048030391091780c1e45499030300d52500c000da9a006e4051500300a41c0700c1c24581d00d524a4083c0019000c810019035002c8a01c0c51403540d907000c0c1180c2c3d62500412140210403101c070800e003883c02e040713440320342c3c454440b80307507082192035680c10402b0b0b051120760058140c04c02007000c2006100c01902d182c0544024002c00c0c14400b8024412412892901e40a148803500403c3d5203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 396185665 1250 396184415 396184471
    0x80726040b0a0e0d1112160b160b01090b12010203060f1014070510150b0a0c0804031406060f100c020d020a0e0106030509070b0f07060b120a030c02130b09 68
    0xa240050440f40d9440005c2c600181e035a10340340f500354000c2c42d402e216001441000503450f11040b03000440001ca00e800e24513402030035403046803020022054403180c2c0c4000fa101e60b003224000c101ea000005400152101001110114120400142c1c1c0c014810301034903a450111540c0d40d0101110034010103d83c2d1003094489000079101c00080030400304401040c0b00001c201c0c1c0c9070b52109450104030140362008018001c4100d0301172181121030610031241003e00450342c40d950b080c046c8210608040d03581c3c1d4be0700340204045070401419000f071400e110003414091114500e80ca01214203e4540140e8080105940b2002802a20507400c00d05100c055441d40303000ca05c00742441258001d107642e110072000d00900003e0b00e504080348903880300000c014509000b038982c8441106141441c0c10048d45420016089042c1a96800700c00540074200c00402084569511f5100c2d840c1c880d541c03029401080ba01040300d2084a4041d401c0020000302a961821642d5002c221402d210744a200450303510110 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 396186915 1250 396185665 396185687
    0x303060d06150806100806102327010f050f0f1f050309070b070b040605190e010b0118080607050f09030304091e112a01020304080726040b0a 62
    0x4540c0b40010816a4012610a00c9100d004800071116503440941c60341d60030044841c1091602415014448030000350003100c0390b03202500083c941e001c1801c00241c250803507030740314400c460054921240380241d408901401410005101481a450000490f111701ca4082506100e01801341030700c507140da0f482e200d042000b424240c54002c43d0310409000b50181d482620340510038800d050000849110240455841c50b1b400401034180761501e5540f00c01400e00604400d41c1e12001d01c00303404480c0c1c018450954410b03100000803599001801c005081e000003100000c0c07540065480034080314900007031440e08850039140455580601181580c03081c0140f0701200d61501000400003030035000383e0441450300c203040150301707100b000d0001c80c04216503034070710380001e104018000b80a1580301d03107484103280025580421054082503a015003281d0049a003203c640b880131402400781f09800070054859150088088040810bd031090f000900071407182442c4403000041d584a450711506503541 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 396188165 1250 396186915 396186941
    0x15190e100318150204031406010302060d05040302011d0105010906141e03032b060806040b0f060a172503030e100c062901050a0e0d060608030a0210060b04080303060d06 74
    0x400e043d40d544500d400f030b5000c0e11013910b185007408410310030301030085031180c101e0768014180d0b031802150540b15406010010000c1d42507560307841201c0030900e56203100810007501e00c000040c840d8104640101210f155400c808500266559160059240d551940d43c480d40c030810100081d206500c0000d28502c200c000000250b14507998420307140240c48400b0a40112998007840503030f80790040940e4540c004c03240642203d4640011918440201030700340d4205002030101132900c2d440e40e0294011381c40140c111043c0394400118020503054201c0108010301c42040741d00c40440c5103841c002d0049140540007841380f21203140054025010318030f040030310b41e0700010174845617100b0300b01c1140c001803128030b60384440c503119030241b070a40c030801c22582060f4040e201c04c0c558054034002d10081041e040d004803185540c0e4500441d01c064200b0203421810240d900414a010f00006050252650355202c01c50f03034402071006112400d07000c8242c3c1c2d8029000d40300c016201840e41004c90240ca0f440303943c04 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 396189415 1250 396188165 396188183
    0x10909111009050a060e0f040e030c0316060b010215010e0a15030302030a17100e0a0f1506090b03040305221505070201140702011b06090215190e100318 67
    0x7454014140c1011a50120b07000e01e040c5a0315403098400810311401180d000000e071154a2051070194070491801030070808481c00c08616146540c03655102c074211480c1c542100f4000000c108080c09441c010200038406060840d0b01c56039585000300040c00380200180421001590081a950021a441c00c4011400421960700e040294880c0d20402c0d400001521700f0003540008910403801c5801000900d50b4109010310340184040194000740c044101130f0313119413910610903c0c9000f000d1a000089541e46051880d107030029245a0075a030148507071040501c200700c0400e42100540c0e80032000b903411074852030885440054424255041807401031000540c504440da0700901401c0d081e40700b038841c20106000c540c05240c00f0300a81d00000e0009000040d0b498500d8403880000218611401001c540b1808982c0010342c1440d200c8940001e5103408034112038590040181c400f0b400d1900d007031090b0480c040d14003050b0b00e00c195003112800c0c1516a00503c030615201c1d80d074401e440350445244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 396190665 1250 396189415 396189439
    0x141e030408030421020c040e010f0203094602060702032a030304050a050d030c150203071b052d06010b09040b03030c0a03121107231501090911 63
    0x3003071142c0054500b40c4500f0031510301c110f6240c050500905140907643c004010702940003003000050212590810280d5403540d20010b001f2440d800a940151034000241c1903040c2c5107402a0020000c2680044c240e81045004c0c29000c1e4070300313801c400d41c0714000450f400300590300c1c00030918038461504020f405100f8020780c00400340c1c400c400704003c41c504092600601c0e40c441308240c1d03a4011030080ca54800000b040c200a076240075065040500d203e4180881d002c451504c80e94204403540f00c0d40c1c0700b0ba5400004000b030099100340151042191103a00401d83ca6031500d5207680c401022a54402041c090b0100042a071000020b800141d94820b044032082d68541030220707100e4000000c131038051170508403140c41502d40071041d1910070003c4001030250a460f070301c044462081c111960703640c40380d540e01c061a1010351040240f1141d40611844440d10f0382151039502201c06000d512603582c0c11040c8000c8801144110150440c0c50740100455007001e5401d2000c040c800c108095a0701c00039010030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 396191915 1250 396190665 396190673
    0xb18060a02010f0e070308180a03140601031a01030803040b07120204080c031e030d0513020604031218050a27060303120c0e010804060c120c0504050307090606141e0304 74
    0xa002c04500341400b07101c944011341d081541c40300300d4003000340003650900286003a060300009503150800000c200c001c03416a40d40b10032030344a440c80c42c4041d550b08104018814400c4600c202c110503825249401099851516045541d01001d44020001c000f040c01058a4601c20b10011240040c12581150341f1782e540c0030b40c0742d81d03030f94101c038100e01074051050744510720012940e41c40c0c02c03030303008002441c607200000d1102c00c000c000080c014030005502105003000368941402400c0903600c031f19112005202824009402c034441ca1181d0803030040140010721050712049841c404450340c42d046402940581c09001490340d0302071b0707100e520551400380c0000901da0300c080c0c81001c1c11020701040140401c0ca03402181c2c180c500b500d850b0302042400d404600010030130b81c8130302d81d03904841c50000c0c10440c1d0500002c06640304000982c0010b50301007001d0000349421710100005160080040001510b030800242c5101e55002030411040c40116000120707a96600c0a000b0800504d10304c2596840c1c9450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 396193165 1250 396191915 396191921
    0x1b12130509010801020705030405010f050d0507110c030a02060414060c010905010204050909030301030c030b0606070b0703060f0906030f020f13090f0b0105090f0412021609020a020606190b18060a0201 88
    0xc1064420803000000003088801842200c0c0c4407900040514a494207003001510100711640d4000e0030000100b1084840141d0391258034003800d19661214100f5075150f030a136182c290702e820703400d1080c3c000c9071202d40140d540f80122011100c042203549442e040c4040011741341c2c020b0900148240d420840d005041206c1980100252001101e01c0040c035110803428507907d001c00d010003400f000022400303001280c07030455980d40c4a1001801c8510300b900c81d60300d000c0c00d6003081d0b501001003a120b03607040c0411201c0c400d0038000780c5066107082254910b50388070588038101441001c1e000e00d000381c0204905480c0c8601e802c44c5122015414003060b1030f035141c10031891002001c01d0703659002c400e0002c941450300e64a0140104081b120384035243d1200d489041d8841684203541c0d0a520a03e0807054460b000c084000000708004d5a0042c0c440c8061034020f4100784004200e10700c82c0e50000d03000e2003505100c4048400ba44d9210b40c445480350211a00c8003e80c80c1d00540c2194894800b042c1220822340c150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 396194415 1250 396193165 396193169
    0x1502130b070611040b0d051b0a0207050f0103230702010204050d0b010906090b100f090f0f0306050c0a320d09051005061804020a1214070605030c1b1213 67
    0x105003085900d030b1090215072540138038020458521020854601280301941045802c44445050310580c80507841e518006a4407608486000d60440c801c10001840c04510301c4424000030300302030107001200800510003d120786104c0d101c03600314202041c802c2e0b200350b040e10b01030400078140d4030407c0d405003000701d040402441000602402c0c0307540031584e503400c0d014240700306002a00c83c445200c03840006907a04400b142d41802003000c44000010402201920440200f0340d00005c420760b1801e6050071b0b82900c0008055203c032880c00c02000d59101d91054204801e070002c00300c48400c21402240c4071030801200032000580304000324100e00c89101c9079100c2007141e445202141c0045500d500e801b4240c50046945030ba02c054104950341c0d1469114030540d9025200800350056379403508045084640301d22000e0f0741c250a070704a07801e003241080102002074462810603500b949000103c16216201d00006800d1200c50001602d00001c130030041c41c102c44034010803064a440955104c450351107118 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 396195665 1250 396194415 396194423
    0xc0714070e07051312170a0512061e01200d0f0e01090e070309020303070212032505030d02180904261305060c07030b13020f0603060d1502130b07 64
    0x49011880c00b034015800c030388911105980c082489031030310b852640c81c060f0194041c0c0307403109003260388050b60302080f000301041540d0b0b889190b02c03140c040090104103c40204018000e501c141022111008240640703000c698003481d200c94109051450340b540c2e518dd095100259126000c451101607800ca400d5071800c0c0031030740c0c8000b655000c0340011a1555004e100e045514007000006c02c00d01886034102211030350020341202e10b441800d03408038544641c650b032011300c20b80002c500401d146100552444031181c8020038920080e0b515281d840d124400e032504088000d6001a031490004800c002c00c402c100c900400b10350207840c180c01c040d24107490005501c200c114150400c03425000000d01aa01c0d070001070021282c05038145030034000c483d8480044101c09108450002001400c0070000714802c1084010a010094252040c4240700c0b81c0c043c1ea06100b11000e20400c10540c4810081c0c1036900e0300b08680c5a00b0007020b8a0368402072088605443c0d0030700c1c5804020071128070543c010b000f02841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 396196915 1250 396195665 396195689
    0x1009030e0102010c140306060418230405031c0612031823130b030a08071a060d020405070318060e0613150b0f13050a06051e04050c071407 61
    0x40400120b08803030364004d0aa02040d08040b4040e8128458409103030320110292403030349004d440d0412580c0d80d02d1a100100c182c0c54581c0d8083d001c600d04e6140360a200e0159242c3c541650800d0b40c0c5003912800b68070303a2403072100c0c6008005140d50b006034100e9401040840515010160345050003801c9002600b00c0e00b5104545400004285040d00740096a0002d000842c60800312500100700050015030310107040c50361a4502e00d180c030340c0c0a01200d041c0d90b110710f0401765908240d10744688424403091180781043c02d40d00800003180c9070442ca41d01d1003541250005820340c0c540d4800e40040c0003120341b16030351241c501c2000003080b840e07510030001d40300904c0031116030f0750720b4005201c041e440742030008158a1400b00da0280e03912003900070b0f100640c0014805a013140e80300e13000c215190001c1d07546110b89600c1e40d0078403020042901c2400f0203001c0c2610f00c95052644031020100c1110541d80d510300490f507503400260148820b038160f4040980c030040b058401c00100100751783d80c480030300a0b5402000c5e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 396198165 1250 396196915 396196937
    0x130f1406030607170a020f1603090902030f0f040c080d0f0314010303050726031e06030a0209190207050d020102070c060c02090114120a0501150b070b010b0702010c05100903 76
    0x1400285240c41103e065450030301d0f54051a01c251551107020700300840050702030160200e5a08100d024110b080c1100b84031080f283c04a040c0145105c0f0140d01c007215030703841007040c440c0c400d050002c201e0b4000c030302c141d24280b10785843c80c03c4c3d440202030390700090050148a007080b80f0380e03a01402c0344020010079642071005100c000708819041d43c017880000c000c11000c10030780000032542944000078190405000007900b04500d20514a41d00407540703004008005554082e2602c100d142d1241c211314150014080141d20b5804074202c0400500521a80b07001c2c51814000905160101c0d401c9a91000503158550118440030b4041d4022038011140d400c020000411401d00c1804c01c820039030740080c0a400c02340d01c8d00002d480742e120720800e46504000f010722000840c6108110ba02c08482c815400014110010201c650209240d038025200310311040020b80d001c1420504003505540040090b669588207502c01602e003042c80c80c00041c80f50190150707503c458841030740600000d42c029240e070401c82c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 396199415 1250 396198165 396198169
    0xc0a05030f0705090603070807030c17061003020f03010207171222080d0905030307020703110f0f0621150f01080c0a0e120a08281d130f1406 62
    0x9250985540e80d030301501040040e45050100c140d04000c025050310f01f803680302d82c00b035400e20741c8581003500c0f2614a21020010034040891402c1c0261141e80a0481410300f48542484100c0c18400a4882c14551070312070721300c1c2d81c29411070300356a46c45914010f1500b5000d25240c129001040300394074000300c240c0019044503506c95944c408501c0c14047c03444100311030707075000d80e1a0454030f180b017540caa0310040c04d000034101700000c1d8020040c980003095640d28610300420502260503803540100c862101e10000c43d10b07640c00000f51361108442c0980c60780f112031084908800c03c0ac84400c20b241c18182444600495580b81281c1903c2c251481000c20702070400558540c0c1080c1d401c0764454004010410380d152203040590022000100290380c000b1101c1c80d03883c82c1846045003501c01480004164144800c040c4200ba040f035800c0407035800c080c3c040c0328083d2220013a850069401e2008180317611040d03a0b504420200c180701140e00300030400c801d00f0440c0050001c62102c407035080042020441c1c80c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 396200665 1250 396199415 396199423
    0x17190914030703170705120408011508010b06120a0b0604061e050909040609050106180c030e06010f06121b08040506070801031104020a0e120a1b0e06061c0e0c0a0503 73
    0x500c3c1c20420143d004c648601e41c5081d2507010300020394280c0100700310034000002c3c81c001040205505000885c40500c000d00c00d100102481c1d01a1085a240651820268440c1401c0d207080250340c00e5040311541c1e491200d00080e00e0014503140e07202d100001c01056058000952400706841d00e58600030801004c07a0642d41c606c50810502e0384a83d00500003000150540c0027001c9032031054001165250b84c600c1c4583c0c1d4020f0003041c0942c1e9036154001042451ba0600c203040c40504604000e08403540b400c0d00b81903410725280180c90070000d031020342407445105900480c0441c40d060900c2c032902c411030800105801d40940d400c550700d006030408286800d104511a82c1641e4214004000150b1070004000081d844a140b0005100850f6043c210550ba0101a00c1c040500a0098201500700c2d02c2d00555419541c4910300c0481071100007403024070b000780c02103684840282c1d920356841c00d046c0c0c074401290080180ea440000d0038940000c01e403400c00304103110062402e84910710210344410805840d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 396201915 1250 396200665 396200669
    0x50a0b031f050a1202032d15061c1b08010203100803070c05011218081e03070e040c0909290f0321070b01060503090606061204171909140307 62
    0x203c8444a0320920a00b0b510105282c000d40c0b00404451404104003c00080a200405c40195800c0406000b00c8010001c0c0400f80582c844280703441d406141c91030001d18407070600c81c0248510204402382d1000c0080000002104000c43c5d46900591561105014041c0d070084800b002428896900003580f0000007054903a61130b80700c000352003942c0c105801180c0d18922041803505882c2c940701043c1039a4400144140c14234080c08000d50341d21410079284a080e04a0f10702401c4c9840200100074105910150280d040302045402140303100c0c040100b04c030100c503d5003085030224600f200d1380c90b0141c0c03905084510700781000204444c030158141080003102440e0003007901a004041842c88140c5510344000c0a04006002142012010386900e80541001d07085100400d0002041c41200001006841d511910031200286003803a180c0203081a02c0d40030380010645071075900d0460742403100009541d400b840110341c44940c1544030340028209040c0d0b2242e158284000300d035000e47c0313003004100c4c801 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 396203165 1250 396201915 396201919
    0x110d030f0c03050405060c0f1203010f031b05041814030a0c14190c0603050109021305010807030e0102270307030309050607031413092412030207050a0b031f05 70
    0x4580c50a000309640071211014201c040140400003c82c2c60382c1e410300a481e080034003c0c0201050003001400c0740c0381018055082522a10500040003c1c1403420382000551b98400d21107081424918a000728101c8160842d40c3e20a04090b0780440c2c40d8405000c140c0c541303019180d01316850000041e0f00d40c4904c51078528030000390b50740c0b5160f004030302d10112520380c5114000441c3c1c1e240e840380d241003017100603510f012114146503405c00c2098503030500842d805481841c5046241500005001101c524603215184c18003480800140f0110f010398040c1d81c039648840025542c0e400c0c2ca54910080360145400c0800719040703c0c08800846c280090702e14107072581500c44841881c1001d08000f95908280760442c00c014480c40040168042580908600d074607001903000c82e10b04040e100300554140c40b01c10000c03605044400400381c0804259401251105680c2c0003460401c0e090490529845070010340c2c200103070800000307059440b4401144030300c5044c80803800e255172440f0031703c8543c0010f106050b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 396204415 1250 396203165 396203177
    0x1801050a0c08371407090b0d092f10020c03060a0e0a0c0807090c031812030605040207120810030c03080d020c1e1603051b120307050109110d03 63
    0xf54090200846403035000311020340440031515a1402d038060040a03812010030b180c03106000410700e81d00d4104107030000740c60f00702a000c0b9410000d5104c0039002d42c1001d03032143e64555403650188070401e4a8042c91403403800d25030f100040e1050030003401a400382c21441c0255114070318151640e00c04580c2d04010003004002e0041c0da2070320215030000d0200d43d15010201c0c0104000344002401038032064000f07004840107441c10030300e040340c0a0105c41d003010200c4d00341401d2003641c61180c85901403e01c450350380100407003605880c840c0200c0003010365421403608244000350040074007013440c0100100e0b40706592003510f47c0e52076541c1952071240510000f48440f0b441d00e02440001e205401400700d00e00e0314400107050402c0d1307025041c5081403000318103050440c4a034025003034403003c3c4840e90041c2c2e265140208040d15664070a5a078600380d1424420482c0c0c0c18420f4281d0391345004440c0640600c9204482c0c0312021801c11034000d00f940041140d2400081d070403200c50b030034200112011281c15440745 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 396205665 1250 396204415 396204421
    0xf0c0304210924080112050c10030f231f0503030703020f0d0309260913150602031e07050309030619050f010e0705210c07140c0306220b1801050a0c08 66
    0x300c61b080c03040ca0401c440d01e025201d80041c0e25200c1740e0701c200c860750b8151b802190900303030415030000b125a8420301007070b50035040400005000c1c480c4142600000019242c141000c0c4650f22a90308210315001194035000000e8210309242d80050003070340b00d05560003580da50140c4041d05400b10752024000a0800c08a4814a034421301510121013002c400c400055240c6005000000c0fa0200f0f186034507840103a5034000c01e001c3e00039401408024010600042d4903245899241c450300108141404a400a000602d08100202801507440081001c4c085907101d00300503400c0c80059119403214100c9620340b40004400030040e21000c4d048801c85002010561a01002240d15500500c1c0900100b08028031003000610702d101c55910440c0411b01ca2900c0d4059803130410b01903846808600e9407a445110905416940450450340113080805010384807105040341d079001003d41400644420341c03050821816090400d01c5003280f019510007000b05550f0001d201d401c40b0303042c811a00006100c5400 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 396206915 1250 396205665 396205679
    0x7020a0210021f0207060b090c031819030201050f0c16060b01171006020c0103290d150c0906020a120509030708060406140f0f0c03042109240801 64
    0xc9070320710486205a032490001500c24540600900140e6440c4903800285881032001c42c0c4503140340c030101220039148ca07080c99050528907000c081c080000007405003010380711b6524200b042800c0542c031007410410f41180c40c20064005c003811640003401000300d60000b45180300100c1118040c4120403c4110221210384510001380741202c2c0c40b80c1440401c5c40707209000001c0403a00c901c44d40a09080c1d100c45402c0c00350090030003114451050616081c0350f0310600f1108213259020b65840c29140301c3c0c01040380240082d004c131600e004048c02a07400081c00b02c407104d00c1600203400c5000e00c2d03152014010364801080341d464a10000142c0060004100441005d11880051502d49001001c46515030703100c100c102c1c181142503904030fa00310b40e9450a420b034412030603030301544000303003c200b1b450902d0711803540c0ba459900100f007400c15510000024082009000702c00026043c2d01a5075004d4a02d50324000d41001c176140525106503886210840b103140d082400510400030903030319500d060b4a0000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 396208165 1250 396206915 396206929
    0x6060306150305060a020d1d07090605010e060d050406110c0109021914090606090a0618090c0219020402160b040213020a0e060f04081f14281401060c1a07020a02 71
    0x307603140582d9202c2c034003160a0915231028052400c038807009411458508042d04084540903401507043c00100740c01540d4541d44c40f811f560704032002c0345000c1001d580d01d20f032a100806a10495880c10100451144492001540002c140c64400d40d0103c4a2100303190348503441070814450200f00c21010304410845052030000203400c00d0000d8005424501c1120000340402714580112002802c0c150b0340100408650300d4102c001c3ca8050010001031034a40d0b070086d100e4050505545800785421112004c64945a04a441c21507603000b00600700c00541c5042004175101f594160300c10304800f0840384203400725108840b03404600340c0310742c0c0746c2d81021000e22003560813600c8a10301c001400e2000003541c507024050602460100050300e01740514044104003110490016425011480c0041115044009400d11190201c141d58102c2980880080c080900803d070181d052a0754043c0001910396000585030358041e1089004034214442c240721000c07400e0f0211245130040c1c1c0004c41034009818402 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 396209415 1250 396208165 396208177
    0xc04030f031103180405010f08060402060f0418020903060702010b030607180e010b031602150408070609050a030f09140303040605031b030103050d0e0919050a0209030a06060306150305060a02 84
    0x41030100700c5000c4074602d03e04540081820030003070b040d040115200c0785814801d0602600565a201c5206410a46100e6803903400500090281c0c3c40015002603410402054400401c101000311010803111404000690020400540a44550f8000c2004075006008a0340180406001070408d0b940d505000c542c0c032052034804040c81c45011202082546901d01c609010b0220a61104c0d036900300f500e96098120300b464144000c54108841107500000d81541c9150841d400406d21074880d205030402c00020300c0750b007100820f10301c01c0710006410503411508441601615072504082c0b165565103800c0b06021520395140d25401c100024045c0702d000d08040c50700304100c1513218000404031941d1703e0641e4400c1e001903a140d4032407074000c13644a601004840c820135098075250143e04040c0441001684207460004100d5204c600190003034800b43d040e202d0040009040324915070701400e010b0000c00d0540029601c040c10b040501040c04035070060801146e07840401441503555040c58000250064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 396210665 1250 396209415 396209417
    0x30f03050915151e010206010f0614031b030907050909030f03040b04080702190527040201030b061306030605090604090f03050705070315020a08100f06110111030c040810050c04030f03 81
    0x1404110506407544c130307800c2c0418020524060710801040700060304d8110140d01c840b1104503501e8040c421141d005440007075034444010010341b030b610785420701030603a280707076104244405000c0b003000300003800051018215030003681c09003640d4030394403049516441a1240580715a5042000c10f0009003440746590f8098040c149041c105000d40d030004011421809084031500707180354040c0214a480d1210661401c581185015052290118502c0014000b00040e0502d43c5d651064403654232500f08449204411110030b0a03003503110840540209043e008160182203040c0005000f0f04052054240e9290000000c81c01c4900303e1f0f400b01c42d00d6101350400c888a01510b0000000154007007a0525490079528015031141600c2500420500000b40380c41c01280008008005254040100d03406540207441d18009182c8041000760140224886c240500c503000030401c030a06035201d0180050701c0c4008161f40514100000760000e8031010303281d0003c0c50701c081004000040d07240700780c04010707403007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 396211915 1250 396210665 396210691
    0x70606030501060e010e070c0b04020607060603080c070911070503070f0503210412030510062f0c13020a1202030a0b030f240c071205190c030f03050915 67
    0x89a03030300740c2951450b500c01c0c00d0340305680005110174081c0c1d000007a881029031909042d00c0c14981c40740344001e200504064010540042c5200a011540d04441c007d540c0150903160346200039505540e9590715481004031181c5000007000d620600f0300e0403035500d150800c0040d41014216160741012002c500e004484911003002081c080355441515160b010100d003520540350301e0f15081000005c9000303580c6004240c540340c1000146840460382c41d090300d110746404064021200845800390210f992440460003126547d1501c9040019003240a00015105800360440c8034040109901440c840540805c54560590a4161880c0c0c040c41c0e00c540002d41c0401c1e00304e1a000842d00341600403402a0103a008172051001c00c0390840c4480c0d10014110800804515000000010038040c00d50020542e8130220b042240382071203030f01074039040c44454144610700c2600c3c44001e4038445d5038002c120080382d10518100c0702140603218451054110350302420744191b1031410301c07e1070b0a00814001c40d02403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 396213165 1250 396211915 396211919
    0x221090405070507060e1e010c090605090a0306092a0b071b0b07031806021203180a05121e0403080d11130806010306060e070f03050915041a061c0206070606 69
    0xe1716001d40f080b1110420003400400210b421413141c600f0510701a00c2d410380c1032410700100994041c2308501211403d280c0142c90352482c10002d000c1d010268006840e10782071040c000c00b4000c4100010502d00d041007840507044242e60412141020544120702a1000600180010601030304e040890481d40c05c5100c911a610f408641000e80c00c91702c1c05900040498011000065890380301030068160350006042940e5580351921092100518425400c40403c01e451400f44080242c500002e80c0300050f038607105025407801d4143d030440040c1695440311035298111641c103100894096941044041d8a08441c4500740c00152244d1004201e000100300084e181608628516002900805000e40025459428000c003131b9000350b0091000e0380000418402d00c10f8004c3d1841650803502d08002c191569000450340c14103190040000308007802108000030040301c07842c999111919401031000c1c0762960018010348a205c641c41000c01c0c040040c12070058a40f030742c080d01e0700b50b1160788045020741e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 396214415 1250 396213165 396213173
    0x5030d0c03170714190e0a18150b120f06010f17090f06010b0403050c03070b190c0f080301060305090a0b011707050a09020a1412040308060402070c060207060221090405070507 77
    0x760041c00320071800044002000c08042e8032406d01e015a080444a215000d1300340181c01d5152108070102c0d080d215944c1500e5404c600509002e4401801c41641d42038460710032880a070700910040b03942080c81c0c106035000507103560150105e241d5400d450b0355108122514410406003560000e001c00050703200360b030040c3d05802000c000d0306010345940744410391503920707600e00b9601e0040300084041c03198215034828010390700e4150903600c02841c4480c495000984160702968840c0464801030302d107019117031100d028040e1040056040710100d9038100320950f203040390281ca586d41143e0040c51208400010080d181004512010032044101620310050f610700c0020981c44040d8000340c4000c2e00410481d003055080340126501d50380f40c82601c1d02e028450789001020a400420003010700144030045172490312564140d800d0384d07600000c501d28042c0c40f01d83c0603642d5055807050000600c100d2180001a04980a80c100f007155034052141c1012414003c02c0301030b1074014594010004240100780208e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 396215665 1250 396214415 396214417
    0xf0e19090b100810021206060a050d050c07020907020a021e030c19061808030a0c0807020405040c0807060216141206010f090c11032a0f010605030d0c03170714 70
    0x3807224400442842464281007130b0030070380d144502c1d82c2c12a00c103008003503443d490002001d5011000710b03911750b51894403040603500c074000c550850503e00e207013804000c070040213440182001802118001030b5592440c004981c0d9030031009000b50000c40c103401411075126002090900003c00409480351004e201001c51f5031030070b0052541708243d019507800c0016907007000ca51080000c0264041d198035061221950707032841035800d40c1c3c0820150344903000511003000c040d00d0040da4014014040c50516003031000b034100c00b500a01c080c90042d400c001800e01e0002502c1c45854210b000700d030642c0d0380380440e10510540f1110016420004a1003100e84010051050758081c241c070070009000c082c2805604401c990705030103480d06108421032103074070301078000003601d101207103002d9100140984503040000784606211440e0300b6104240160050240640003402034030340580c21603407070592203c000c0390b58105960000d404991050031480361003031566011a801b01c41410a00701e401440d504003841 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 396216915 1250 396215665 396215671
    0x7081b0c040e0a060507180e071b060c170618040611031f0605090603010e190e0c01180f030f03020c031e150405030f0d0906051003020a0f0e19090b 65
    0x11030300f0103144042040564451141c00c42c5107442c002c0c6c0c0c1103a0410705c0420320702d46801030183c18400c05000480b410301c101c0e5204114240c100d02030340d4944892410380c0140510310300c810f0200d9240c00c8921480030184c0302c168411400240849913072540000c0c488400070014005807415610b07809140e4000090100440c0034081201c1c1e004d00590201c01081600100707600824200a81000342c0821580c405013500c3c19180068844122501c507610350482c0354154080d800861410010f0b090414000032610f0541090281c80384081422110b240c02c58150940c021006654440402400841e40403941020800c1c82801294510144200007902c0c103001a048486200840c9243d414040c0c020300038604c0403282403652105500f05555044e032a030040c0000c050290780007051181c0e000c41141c102480083e0030181c20085410141200000e903041400260300030303a400c6400080035000c043c640c0e4100d55616040442503103a0b41c0d43c8142c11086411000e03041074541c03d011012a00a03151240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 396218165 1250 396216915 396216941
    0x9050c0303070c150203070506060913150509010606020a02031c0207121506140901050114090d08090a05030d17190c020604150612120513080109060f0207081b0c04 72
    0x1007518036100803144c00e0b48214800f03404541040c090300001840001e00b494120354201c076409002c0e503400c42140840581031201600e41d034604008160158410340c0801e004010303401c0280440c94840340309071b0b0b441c002864000d4240c3d0140041c08080c89010b00d1700300c8118061710548030700c0c0d079a42c8460780819141583c207940b400e010b43d080051581c2c280c403440300100f41030890000520f5060380080d055130014820581800111200041c5c1e030f82000046800b43c150007001040708000c1818070003003580081216a01a00080201084910b00003601e9140c91829070358206041c1a454035400c801e5201501022414250106c4510240228020403241141a50081540f407a0500b0000110540302003070003060f42c5040e00a00c49000481d54003801d468120f9000d402c81d441c4ac181c01ca0740c07403041a1040740c1074504514041034002041d00221600c900441090260b14020241c4404911520327000820102082000403a002109224049060260020b13a208085c500e40810103807400e601c0c0c20300c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 396219415 1250 396218165 396218183
    0xb0703031d030c0c0f130509011d1b0d0203030f0f0403140312010e0108030f0702061201120c06050a050a0804141002131409010308030a1811130e070909050c030307 72
    0x1500d40401300403050f142d03a4201c4400c16200c0c03044000c101c44550002884500313944a000044030394100750011203107c5443c4038040160700210070402c0d21011183c40150f2384190240058000d0b242c10f8200021003034005014600c0c00c40050b03407940c0185d01003050b54a00030001d000c00008640c041862020824811010790f5413612192412070640340d050700681c00c03c104c04401403002110001c00e99038029003944902e0382c1c40f8201e00004100c3c5c06a00b800c0d08980402a0002c1010503081c044071115500c14a248009682c40365001d03240382c020034040c000094024030003009030a01c100c0d24190001c0c0a41200c80c81c2504c030703440e61410300780006045001660001103042c3d400798500300050003010442c6c400c02c100d11030302001540100040c0f001030140040800070941a0803650b02c40600362040358500381c2d46019924040c030852228400280c441d41003084a040c1c07100c0b0600502c91066146000741000302d060050000c001c006801c410f44c1c1e544914292101240c030304200419065008100075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 396220665 1250 396219415 396219427
    0x5030f1305060a1b03050702071403030d020c0708060106021c1413090c0e030118020d1a0403080a0b011e050c07090509030d1b0c020d15051501030b040903090b0703031d03 75
    0x2200c3d04010004d100d004051500003000b034803d5000c0786e090306540f040c04880e801c05402c1030019185004050560403044e200041100440c040040d583c01190100344c00e03900300daa07880304181e031604030740b030640031603075001c420051007184c41545151045400400c159081100700c0406500440c444c0d0408999180c4e20b01e003840d180d80d000078000d02c4d011002c07030007804111080c0e043c12010070600d41c03009000c0d0705840002010010003050b45181629403e14080b442e181c02e0800034144041602e001c81035515007030792400154403d62814015105c0c0b001ca90015410101d02264254031041c11185240205000031585281070300900b80200081d00040d0307217565072051400300300c0c2c040c424200001516600c10a07080b0b50412010301c4d1150b0100d030407401d561005e050008a441c00000380181e0540303804204844011514482c2c00744000a90b800c000c0320f04424244000c0b1844c0c010040c0200351624000c0086080403c01040841e10910300403407140c0f5060410880201c0d0a0002d40f0650008200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 396221915 1250 396220665 396220691
    0xf0d060602060606040506191e03090b0105090603030a0e1210090b0703020717090109050405010e04170a0905040b03281b0b03060409060e0717060f0705030f1305060a 73
    0x202d641121044499a1505203014000f814a10070301c011140714000020102c800c0300c0c003840d442841072505101040842144071801070003003001c200101d803034001100003c40c85082181d5410300c652005401140b03400d4205105640c09001824102e42c01a00809011b03241d0505000740d0580d072100d0b500201e400b4205140080022000810405c1054030601a05010070780c103209001000090300d020968402801c00108c0b141005a000030307400c58100000051000028440140300324040c00c200c82110011b44000505481800700c0000050341d10901070060b894554802c1c20800802002c459a00170321690340c80003d80c1e030041c1603001020481203182406807080c1c100c0440301080c1351500b04c06090452040003400044c040c680070782d558400600410410b940500e481625170021940410340d1168581010302051409203118014507000c9201c034100400d040d40202c00310307101c00c0c2c02e40d51650105414201b00403e001d0784408801040070214030300703000c290b005440c1c55002041442403045 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 396223021 1106 396221915 396221923
    0x12010207030e09220c14010e0f10050702040e060106110c01021207020d1709040606050403020303040b070807300e030606040507140d0f06061b0b0601050f0d060602 72
    0x6550300380f00c00c01c50703890700b15041b103400310407100201e00c01111180c0040801d00d811413070040180c2c41c42c0c40c107160030350200c01e03403807801a0400c026900001c0c291180c410444079140c010034014000e0b41c0d88070400001034007440c1c005051094840f00000e644140340f02c0109610340340807501200b1503940d0407001543c0d0b41c0044024028002001949465601c000240b0780310b54540400010300501500540341202e40040296040ca440c021110034a9880f910341100ca9a50800000b8005a50300c100c007125090013030383c01c0d28420807200c602c03102e103940c41c10208140911040000e01e01d43d03000801660000c010b64001c249a1951711084d030320b140050801c660b42c1d92003c6400014001e0302d138000c00c88403860020500c00c050f9540c0082e0782c0302d03280b800400c10021030600020042104615002c0c1c100342e0604d4aa80762089035844150a50003000e2000d00742d988640d0200880780d4100 = true := by decide +kernel

theorem cover : BRFrame.Cov 396043165 396223021 := by
  have h0 := BRFrame.cov_init 396043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 396043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 396043165 ≤ n) (h2 : n < 396223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
