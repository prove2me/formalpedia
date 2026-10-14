-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0088
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:46:00.431985+00:00
-- url     : https://prove2.me/submissions/cf9942d3-1832-4f26-a295-a1e148be1be0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 15647488 ≤ n < 15827344 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 15648738 1250 15647488 15647503
    0xf020d0e0d02040b0303090405040308011703030115030c02010e0607090e0a020f0702010c05160f090f0507020c120f0d090e070e010206040201111f06060f0c020a09050615040e100503 80
    0x207440000e1a25041e424000104149440c1c9a410300c800c0c844448140c0c0e41c3d01a20344200e10aa940c071941d54500000300c41c030480307004072480d42e5410030300061003441c0e0848580c1030444611703d00401c141e13124007820780c01455000c0d01998103004100801c011190408940c501703c5691418128141d95071040410807030003549616050054200035030f001561041008801e618090000ea4145c0c04142848243c882030750b0780034410004c60b44074100707c410150320a9025400d03001d00c7c10710080c42c00d814005d40340d0034546051031040d140c108018000032002c01065945902002c12140f882100e51400f0b821901da51180c0140000004001401644124032070780000c2c0060300102082d07119640155200a5800d034240190310500785415160f510f80841542035880d41800010041c0c10800e009180c400080d10b00018052046460801600c4281090080b0f48030000c0004064440a0020744030f41e0703603161100203050f000b003008176007004e011800364001c4c09141d10700b81c415980c1c0c074103140e10b5051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 15649988 1250 15648738 15648767
    0x3091c120e1201020705151b04080d030b040b030705060c0f070b04080c0d0b040609021518040b03070e16020c06040315050114010507060509030c0307210203070203060109020a0203040302100f020d 86
    0x2108040e007c428148441c02c079040800441c6006000986041c0a0302e25041584044016481311309440d03090758162207420030701d110a490a2040018210219035a103145100d0540140c06c0014100c1d010f0800303000e4103d00d91500d1045d500700c40c0d5581c50180d4507800134003e41056000e000d03801001882c081e200900d00c5684034181041c140e50f1501c6280c001c0c8905103003682c004842c0ca0f41241700c0020035009000d030922210311001c030043c1d030b43d00f4001210301da015203900981c8a40014401280111190303a80300002d5000102500f0300c6450407410000390601864001c1004580401044026050340c0c804600307a540420190b0783c0d4100400e2900301004040d804280200f0040020071003540240398812144401c8a00c1d0000d62100c2a240d80c0c0324a5041d0783d03036684902c80401e90303034540074141400b450501c025828000b80b0340010340c5079035042c0328102220742e00041000c2854000d109480085800410303100c0ca0000c12003001e000d42801c2d5980c4001400b0740700503041541e001d008480104031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 15651238 1250 15649988 15649993
    0x2030a0207090b04060902040914010918020607080904050f0a050a060f0b091f11010f0204062f100c080601080106051804020d050103060902012003091c120e1201020705 74
    0x92500d0ba2020052100c40e02a42d006500e0303040c049542500b900051009140b07040d00054800404021350242600c1a000302c5c51443c14080c2841c080f0100c11105580180c04848603551801c0c185090003161080c148002d4020303040c00300300b007c00560b88031581d01c90f922000d4180000d940300c0200c1811204140260350700c510404501344020503403c1d02402d207003074000e0b001020104d002c500d071400702040081010001060010a13400e1041c2c20302034002ca881c0181c00660038181020005003207800c43d42d004010104c02c4d00119095280000c5401d00b540c1c80003016201c0d003070601030400c00603000560f04000401d10981c0424280e5104005050403a051036640c0c9041c680c009000320740440d082108075502503003e000b1040700130103501c80c25000b5445441d0000e084480c5100240134902c142c480900c03542d0045071b043c01d00034408001c4406210049801981034540104a19480400c50b000038040f1042c4d07070600390805800c5841025140c000312500c40c1c1040c520284a401d0340300340350009101e40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 15652488 1250 15651238 15651253
    0x81f0e06010608040203010905060f070318150203040206041508060103060608040507051e04060801060503010e0601060e0d0314070b060301060f080709051315020304060506040603020d030e030c040204090e0c0102030a02 96
    0x1944941d000f281c000b40300400204120040341c4130280b510200b070701e43d0110360303040341d0901045540500ca045c10401200c40c280e044805142c6807000d10440c5454000304141d0000000360865030380e0801c03200900529005541403806280008009008c22107901e8046890000d011500038003540a01c1e1045503c040100000e07410281030250080c002d640c202d42d54643c0c040300c00010b1303550307024140140c4000d030000141d4a140408060a42e110300c1d5800000b9002070005100782a80400c403002c898800343c0d88010f00309428981224841445158000510710205443d401c000708542c090b406004120001d00c020750701e03400c2e100b40501092042015590040030100b16880094004c03591045d50031780b49205054440e05c800403030244800034043c0302640001000b00300b140c18414150400f00603a001c20013103040d0340c08a004078017001d80240070301039085400c1031070382d908110040e42d414001d04250340f9941c1d1100f0303550240c5041e0540c051180205200c454865100100b0b6600000e255401003181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 15653738 1250 15652488 15652499
    0x30703090c05030708030702100816050901120504081201050105040b1b01060302030601060809070b04030c05010809101806180b0402010804140616081503030d24081f0e0601 76
    0x1401900000c5039480700100000920f0b03a014449030005150b0040a0341d50303014248100b01e06070911402e07000a0007003d0091007441440342c100e4980d100da071400e203565240c40c18801a113480d41d000214582050810003040200030706031000d810500165103061540b640c80304019140340c000c601400229040c140050845c0c180c00040064800b50081c3c00040d6060301e80e00400e040c00c50903004000840d200c0d4081c000c038200700304680802050000c1c1e460f403c06085660340d01944155100d07040c108561000402d4507010244962401406150b0042241804040129090321074115044d60003520300301c040505803c4821160511980c060341041c405d40d03e40c0d0040d540d456001e0025640f030b80f00110514180c00d010001d40380540206144000481c269182c01000080c0051480d4000944c4000808180c2c40010640315180944038020461203415540304000c2c44070700c051141859404000001c10803000304114500d1203042c488546a1190750f1041c80654666500300d050691000004002d0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 15654988 1250 15653738 15653741
    0xb0307050d09020604090b011d06090907052701020c03070f260303150a05060a08010306050901091704060810030804031101030b0607030206100602160504090c03020d0f020f0402040b030703 83
    0x49011403600150102c0250045001600540c00000d04d460f0344500340d00c1950381187c40e050600c0c200e4103581ca5600b20040100d038140c028100c3c0c19008401d90381c04203840500400940d40c0750380b224070108020003100e150030000c40203400940c030302500078841882014240402e551041c0e500c000d6401c400700d0f2030103d4401c4d4000154282124014a030a20107036680d506200950040500241210220380054208941000326074081c2d032180f0402c0042c0d40000ea0404921411a0b410481c0040c030340d9981210140540790541004180705664903c00100590400241090314400e6803104440c2da00d200582d5500c0c0510b000150141009001c1000011011049000f04401c189400306000c14000c004c212582c01403602103001d42c02640800901c2a01000b01e08010045440208004c440c10940c41c41e5600c10b1b80031f5140205d03141d038000018802400903141c019075000c0c2c2a0f01040810b810311001180d66080224401c64400105034003520b024002d45042c5c80c04519041c0c03135615284070540 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 15656238 1250 15654988 15654997
    0x6080115091703070c0609030b010509060f0d14070e09011508071401020309040501090b040e0613030c02031903110601050a030309061805060a020709050a0203040302060105060307090918060c0305010b030705 91
    0x110341c1e100404c030020002e01002040e8008018a45403c0c03002403c41c541142c82440580241d4000e84006080150076031340c42c00c031040035803c00d40e1500200805400d241210192980000120717110340755000800f41c58075400302d44913040b200c008100310380c100300a62005c00142d106414860380404800d11000108003240c0035813250500441e450018614045000d450090f80308c600e41c40c3d030f00d03504807404d420140182d014203080540609850b103888d002c908020304d50341c00f0142c10803403040301403021514100a2031b02d03090a008860184810940760007002c0c183c560f4006a0a030080e4000062142840751580c07041c3c0707602da1500345100c3c0c100141180e081100c2c1804402c0103049202c0012542c0b24503009010812882c5d02030582079050482e51816548042c287c402003078130400c20000481da0108001c2d05450b011180655079445481c0100d41089071504401d04492800d01e40040c84569420006050f40c421101840b0030404664160708907a401d2041c3c1001c11010400035840b148248001c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 15657488 1250 15656238 15656279
    0x106140a030216080a0e030106030305032d040503041d040314180d06061e030503030103080705030d02040602010606090503060f010e06060f0304060c140309100c0e030a03090608011509 81
    0x1403c0c14803071002c4803030300815070740180e803401c000050b030021869020030412041c000c1a002800094510740e0700504a120050410480f00000390303010703501080c455600010301180300c020400c43e0401d410110b4607a4014400c041c2c601c3c1040014280c6003000b0014a4440c9030103482e00000f40c0b40540802c5410f621607281c0310e40303404059102180a03640d8451602805000b401c002444a0619000113607a4078450601035010740200d0b010400217000004680c1501c4e0701c005090f8a501040c9000b031320b1409907840d9650081e00108011400540c150310502c00c4a0890366070028403a542e071b09040e1500003c3c0c54604021100000520403809140c0740c481d08a040070301100e00c2d009081d9414031480c6c0043d0b4003141c07015100c804002a096000d005c01004078107051030b80e4a58140310b50291f03901c2001c60720304132916894115500d0b035035001d1030700d80b03040140287c199940c1301d601d840c00501000c024050a4003140c0f8000000c90203506110074200b0f10b100030340b03c02e04800d080403c00e022000c890102d5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 15658738 1250 15657488 15657491
    0x6090608130c05030a12020f07050a170c09090d0915050315060408010f060503071d1b0706060306050613020c0a0305070c0308040608010807090203060d0219050301050106051803060106140a03 84
    0x9480e4800300081c05c42e56018030324103040c40350007a800074207012618107118110781c48088248160b0b03a03041c5c9a40700712000315400380024008100f03908e08007003038120455401000d4408001841c4804140301c03100b0b00311030b5205c0282e01c0c1c5800844014410641000c3c0005809100007003c0c0300c04142c0c20100007000421303460034a40e9401c1500d085d1560030f880c2072506625280100464241080480081e0903403207404003030505000004d00740e58000610340c104110f0202040c004a884603022112082d400000c04e00807a6220b080c048041c002c01d69201d0b003e98101d030419042032150744207888440c40e171342000d007040e105c00e503c08461305c0d00501d80680e10702c011800d0000010702980d0081005043d1a10351040e19031601c1da00c6810300304254008940c10340104104181030351450055855141d0403a66001c14200c1a40c50055920140c0c10803a0190718260012500c1e03900407015006100c3c0740d800380604001110207041e11a0300a11500020810500b11108015074000107050030005d1443d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 15659988 1250 15658738 15658763
    0x71a040c080f010e0f06091507030b06070b0402180c0a140c0109030305040b010911040b070305090a09051506070c03020105032a0706050a020a0c060c0302130e010806010609060813 79
    0x503024103041c2c4010103880c0c0303a0365031103c1d0350303500c4000e12601283c0c021000184c0b2261504407407154032001203400840000e1894000504158020f038801c1030300c824042c01c0c0720385a68880c80c00c904c3e00441901c080e88140d213040d86d500346270018074078054803800303202402d030341802c0158400b0390f0018a80c0241c00b4440304240300c840c003801024421641103500944c4d0200c1c2c40e05046c200a0079184060700aa0301d101d080900080e942c0f180320f07003102d0484070407100003070781c41210381030884103409445012503208070300301e82c00500007034541c004900840990b4200100700202d0310402c8603030701c1030050081401c1e625103401c001540c01200a1603002e0600c9107075561032542201c20142028003903075048c02c2c1e007a002c0b51300801c1c40302c0341c81070719440b00490408601c3c011003001c001c1c0a0b0042c402d4010510307138480c520060554441d8051342c0000b148822480c80c1c10b9150540b101d41640240514a072030b01c10700c4d00001c0c903944904041006c5889a8440c200703903844048141d600b99084403c03d0301c14035031480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 15661238 1250 15659988 15659999
    0x806010219050a1406040503090f120109030905010e0109031a04030309020d080d0c080f0f04061e0203040210051903090501061a0d0c0e030709050a1103070c060605010302071a040c 79
    0x40d01d0407550302c200d010b0301e0341d03a40c3c0b46071034004e80d80c1c03490110311aa440141004005500001200c484880440b10481c0d002020000240d9144085416003050350a00316032030100358103d201c0c20141c0c1d400341ca030070300500c2e40003004454103800751101a140c082c18549401d0701016564440d500180640ba02080c10b800d00d402207000780100c0001210248000510710304030780801e11419940c0d0b481803500c2e0322207080c0100c4540c000c0c0d0001d130800c03138580302c0030000c43c04120256002c01495101c0500551f68071032600980700081d081100c0981c002c5440d07545010000b8400c404841042c221001e420400341003000040b0000c002400c001c403107641d40d030fa4003c6102c0300c070406010a4201c0300450706032f40e8003220004a003a5049440c001007849001c0500700b000360340100b81e003016188069000581e558a13007006034054102c120405c26481c10010038454601c2e400030741ca0b4a000c0c09200103000e5217035504c004408038400d01001034071070401100040032002180e1f02c241d4003e4082e00391024a41c0d15013 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15662488 1250 15661238 15661273
    0xa0209030102071208060109030b070e030f1006030201080a020f041a091903020f04090804060f090e010e0405070602150103060f0905010507120b01030e1203060109030b010810050c030403020c0108060102 89
    0x1c010644e00c545030400b244004d1139001001e00c1d8000800e04e482217480746140c2d141001100d019100d202441044050780b0301d01e80f008c0081078225890082254041d0170a4100e074001080075000590000300640c0011350f000c00a80200c0e582c642c4401c0d803884c6018600300303500a4031403d14050030440c2c081048229259540e00440e83d41c07941512038a411920310b184100700d0b045400001c000d0182c0e003000300d089c0110300083c1c1682c2c211861428041550b5600000445646c520303504121b041c000e090700045940f001907002a441140300e14100c03600551181403c0e81e542544812059040d40024014000950b040c0c024801103003452001007141701d502c1d85c6240c2035410071030300c0d8000123217036011803440f080081c060f9428600c000e00342040407000304074015032214100800c0e510701c140c0001c0440d0b01c5910640803c00250380100c4240b4072035031200c142d24fc4507111040303008030b62400e00010410390100c40c021a8001d03507054004000071000740b001580c81505c020302080c1580100c12240b104120308 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 15663738 1250 15662488 15662497
    0x2030f070c17030a020a03060915090b06040305030313021908060417040e0703090203010b01140301031709030601030f0b070e0609100504080a08130f05210307060e03070b090607090603050a0209030102 88
    0x410700141e1618106c6000404403425640f119103041e0800705101550b101d9100554140d540c0c0b00d00c0410960070100200c0c400b8415640014154480001048206515121a034584030b1007202c5040c010f8200c0140b843c0740110b607001308543c90b00000c003c80d0019441d40707269400070aa008919042542d640807040140c0c03822a1240040303a00e070400c410440c03400b88940041001c007400c000104c10506408007505000500006011482c2450a25502030f407040540342401802011140c0940e142d2618003205c900c140000c8a50a110034007099000b0f0140010700300d0248045c00c00e0741406200c0c0b00304a05a00303000344107403c3c00740030000130510003000e03c9403108242c020240c040ea030352140039020a14180c1503000c0700c0c030031059110a00c915940e8000b400c0420018208044001e0505200641103100d480e02c018940e518140d803000104d00c1c04005040307003038080c843d95011695003002e010740b03039401203c03020700082a4480911a46001e40d000541103641e001005007020b40100c0401c0c01c9031701 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 15664988 1250 15663738 15663751
    0x3070e0613050115020d02030408030901050d0e01020a020a0605060f0105030c03070e0909030a09150503071101060902030f061908060606070302010905030304050604140c010c020607050c040f06060e0402030f070c1703 95
    0x50350184c011a01001a449802207138402140303410b2601e24426140d0282d240c001c0e0401000140000d18030250390000317210b0f0341a80000319030fa18901d41c4040e44d11440360004844c5141080300013a098a08048460607409042c0c6409246540d00300c2c22203003c2d84020903d005220480c0740c400c035640c44040320305204440c844015650307441d1100000c3d00030030300369001100140755222002c10070782d4000103490300f01d50b160400c40001c000c1c0c0485140234000c1500581c07501e0344003100b00200540c0c51030466000b500f00340d404110981c0511145124100c50f03001d0300146900c4600811624208117000302002402440009080d00710ba0391410b09552040e00c0c00e0b84d803035100800348414480fa04141036940301f40200101380c200c84000c0060720348015048003034810100805c1407401d2000520580b600140010703c100700606210000d80000d0055010b00c0c000581100c004040d5401c05100b180d000d80d001c0c0c050a6619034070280102d841204505c000c4800b4402e03004130001d20850f8202a6000380b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 15666238 1250 15664988 15665009
    0x40533010e0607020a0302010c0201050c0f0106030c0501020d0206010302060c07080a05060a0c02060108070506030a0209040509070311040c080f090a080a080601020c01090303050307140c0703110307090501030203070e06130501 99
    0x81584001015468031490a502c10300080040e00700607520700c0c02103c1140c5d8282015541990035000581d2680100d640e201400e0048a201100015040d4080020b60b072240044019403512880120ba680411004680c00341e0b00c01c0300140007501d060303006030521915030300c01c85091985540c0c00500300f40154004071180c1d4020002d104029039a80200310340d00380c55100070b007065803400548564a40d420700c141d80c000c840000c081850301900350122500301703030040c1081c80b050400e0381c00030b50b03128518841a40c0003040d100c0984024034240c080c003d000c040075552110141c0b500941200c202c000940040301910a24080200095001e0040c2c503c03220b03592500011460301c0000642045075121a81e8100040309406000098010b425240c00c15003d180010079213801903444240c2e0300c48c1004040b001d03c03944100008000c404106841c008405070162220184e43d00c500b01c059607020b00000790315400a42051140d4040502d000381e01c1040100346081904030b0000c00c50444e6000e030031030080c09 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 15667488 1250 15666238 15666331
    0x903121806030705030117010605090c03041505060d060b0402040510050d060918080903070305030309010c030f090804050909010f140f090d1b0203070b030f1b090a03020405 76
    0x22200c00e000103030040c01554040d2540c6041d96000b0020b1205000ba101e5144510034400c080304000d511034405401c015010031420f0030f00684007050750f04204c03012900c0b0a480c420700449060307503001f100e002c2d0001804810621344603603281e8004d007000181094006a0030f00c00051a540c9000b1029011620360700c0321541c070b4040c824558143c62594201001c8070b401c0006040322508000010600035030060102071310b0710281b1000a007402515400501f96100100a200c040a01907102548034009600c04000a6480c1ca11500c01c0c0c4000b080b001e414484244020051420190407640e07100b814080005034040d11042501b0489440300e030158404040704003088070340341d0002415900f051841c0c0c000d044184048100074100140f001159560310000d81000d011500c003042007502800a5020030380d280d00e04424605000d0310100c4103080640d507803072140394808076610100c1d007038400041d00c412401800c0d0b40901c000703804060400f01421030303980302d51032000700b400001c0140f00c507a000c2d001c0100d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 15668738 1250 15667488 15667507
    0x100f020c12040b09040902040207020306010303030e0f07050306060108091207081201090203060d170d0504080d0b01050f030a0c0c0204021306080601030e0604020d0f0c0e040b130302100b0303090312 87
    0x18042100c07200300e072003a402c00c4240300704692a400e030381c0501c00445001c1000c050501c00f1901034002c50100a4042c03040000120405805401c401c400c16024001c94206203810400a5518810392040d0b030b406070007400100d400f03940b0402e61a580105050102e40ba100008501214203038040315003913036161404620140c900c16080c032064014488042d003035040d41040d40016041d54082113005140182170a1580c2d804400a4203440800c007012408108030301d803c4c24144000c1d071100341503181c603a1400d402d040a660052060321214141c0101c0c160441e95480e082c07100400c3d1050207001444200c42400740140d550b400123007035900c094044641e80c6441d06001422050000c1c141c641414284840b001c0e42c440c000402075889a01212229182c04a074104a00e02c2c041020018080303400070600030405030281001c0700d02480c4100c80c3e100d0140d4600c829104c00f940d5078040140140c102440c5036a260f01c680c0c00151900000506503403400c0c1814000a1800c00320142d66103400c480414500d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 15669988 1250 15668738 15668743
    0x23010906061d01120b03160801050105030102070803070f1e18050301111e09040617120f030103020d0c09020a03060f05100221070503130302090702010606080612100f020c 75
    0x740314600305040080600d40c0200101203081d404a41000043c811186048400b034000d100c0b0440041d040d141003009500c4904811142805004503542c201400040c00f820140b0032102c0e4540c200c000b560a649840d02d0481e441c0349a0860a0300704055007402d01c04100300300c000780c02c0c2c40c0403e4072801c60043c0c1c1028200d61100165010f0340c170030b0b4900b8903211499a00801100c054440c805000e4400c540074100b42c0c0c55500070b11a200d50032a03c2d00308081403441000118054070540d003c202c41c0107591074007510301c2d41c5c842ca540414200c6030900c0104014203001c0e10340305c41c079885190009103160f224800350080783c008e680c1610009032101c4003000524400e001e0300707014150590701c060303840c00d00801c00703591442800551091070303501c0940b5003500619041036802c540c0d40141603d540754481480a40300711300601050384604899408151124014440c0008540d001e483d030403003641c0e442c0c0c10040e10103540058141e03180620b041307030400d0155a104100080040c014016202c840f0070340c0651 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 15671238 1250 15669988 15670001
    0x30a02120a110a031e050703020703020610060c0b06010509040e010c0e0f090117190302010b01030b010503060907050a0302070213051b0307020712020a0504020a0f030e030a0c110301230109 83
    0x507041454032a0302c009a9034084100c81220040d403c0c04114480c04080c8441580c0368041c965260924010920280030341c0741e0020199640240c1c211040f548440b41032502040d16481802c0104000e078030440c0012b08660f0005034030980504195007000194004102903507580384039004c40f651760305100c0c07820b103400c6400c401d0b0117803080d112081058201c4000c1a94180180101000e0541da03200b00c00c0c048008200984a141c444900341503201c210746800782c00392042400e8a03001c00c0c00c116140d4090b501c504183c0e40310fa480142030500341d8a54060917121540404561010143c08010160241e1100280c04006011103280011a403500720804030b00d00307a459003c2c0c0c40010f800c00c03d001c0b12550004034441030702c01500211703808416a00c0022003449460344102e030070500204040385030942011103e42040c400d920103009905481880301c3d02c070311417041581c003c6844100b40703901180058030b18000119000d40000f80700c90040f13140c00c005541400c81503002c08440e40061020109030b00600 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 15672488 1250 15671238 15671251
    0xf0605010302030f010c02060c07020f0d0f0605012103030902060d02130e010603020313241a0301060503160902030c0702091015080717090703080c07030302070b0304051e1002030a0212 81
    0x801900c81b03031903402525a41c011380787d0300034006c01181020555a81000401603017000802501000009140246111001c2102656081d01d400000241c001d011086044405945603400d50301c0c04095600b034004040104041ea00032906200f00040d110443c070003401d006000034102c108483c0740c1452903c2c402d00c160042410940144144600c40c1d28901d405450b483d80890443c0454841106034085c0c0061040c60098050400700c10415403000c000d404503003030710154002e00104e500c51081c16500e81d011a10a0800b1b0034902c002c22850080d50702840d0800c18040e5040d10b844074640000714a10310640d0305250303501c5500c200b000b03500b4800c1c404023072040c1c540c1048031080c41c0c01000a010307010000540740d40e1141d00340001e01802c0c01030220f403001d55400045c40740c5404c0c0c3c1071b1131150340b00b4550004402601c124403020a01c2030008040d03d1050743e018000381440d942d5008178011007110a0b0f0b44841d41c1c41902c0c90f40c054280d0f14000355120b41444840140c44070800c000c40d000449014002c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 15673738 1250 15672488 15672491
    0x2040509010819120203121006030510051516060207030302130909120503061f02060114010c110118080a0b0f06060304050607140403020a030c0602120a0801051504030f0605010302030f01 82
    0x7402c090b015012415540942c1245134000c0d10924130206030705601c03030100000c482107407540400c4047c0015881c041d0582d00c090f03804000c4c66903030414452000e134813400303450b602c0305c0f548012f215046c00350b01c0245401420003503212850b10050743d880042c1d0b01b01050880100c0d401203a022807010b10f0340c010000528081800f072042e24016140e604041246180040801000000158150f22002a1480e4000c201d614084000c203070198025118902030080c064104203209174000258030850400c2041e0750000380d0706030f0380c0036808015608201b200d2100f9503010403024000895441c18807e042080f07004a01c074902510f0003441643c001d440040419118070014418080440d5001a82d95441421414080b10580003400381d0301070b40c040c0da40003d6002030001008420810007000c44012140c26408a4001110604407074841380524610701c030000b0105001040b0b1890549070a28907120300128841ca00b5480e62906100e0b029590416524076850364010011414204403440108800100 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 15674988 1250 15673738 15673753
    0x317010b090103050703090807050c01030c0c03020304050f0d050d0215070c03080604090201030209030f01140603011817040b0c03090f09070504090905010e0601080d08010602010903090504020703170a020405090108 94
    0x103951500991440c181055900c07000220b03154080e40c41103e0320354000c0071781c0b83c803480c0510300207640700c1d00710009900003410001040d01040c01000c0300316a143c0c0c50340245007400d00303040510003580713109996142d00c070901c29451800300d0030901060014140e1079000c0c04c10f0038504900c9085024014152004001003802403c020a03444010b01c2d070003500445002c01c00d4000790004070040d020341460030303605004007601a01d039114150f12440b10300c208860350211a035100702c2050708942c80340001c40502007061140c0030003c1c405040003101304c020030020600303107600d6440030102500302c00a940015880007580079001c0c5804080c44540a0040740c0c0d410740d602d000301000380180610700c54244004d407245881002c100003904aa818850322108940c1e007983c0d01c1840d00e50f118030103443c841c04504c106002041b66807060148001858041d01d80c40c2c0c2a034941401d200c003e500158064041001a40040081c0c1702040b4400740101c8620802685490a000c01c0210361001a48a07401c1584803c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 15676238 1250 15674988 15674999
    0x90311010f0c030f02070f0b070308010515030402060705011506030b09060d1101050a031404061409010b091302120607021608010506130c1101020a120e06070212031b04030c03031701 80
    0x240c2c6080c00ca915151140c60381c4902a03090386020919044104440c0302840081101142c071006030003411b0290381d030541c050b40e80b01e050110707001460b001d55803c0c0004100080150030000020300c0068424000003c00d82003e0000340070b4a0016004000025101c80c40f140c85407800820003074105c0801c41d09130f400078025648071003000c0b0641c003599040c40000314150344241e000740c0c001c0045c20340700c2c41d001c03010b032a041c0b40010003403407010610101082e20748081803c11a0504c0382000000001e00080b0150700c42501c402d816180c42c1004903800094000d000030000d00510416000741180d8005090740c03502e008100141c2d49680c2c0050700d46a140004008081d40c0d031380b4041d505c2c04200c0c0c00c00140f60708a800103d0354403c0070b00c52680c80b50b000082c0c440140d540607005010a4104100802071491500240d644070380099400c0d00040e404074003151000142030005640240c00b03a4080c441e440107140040500d41c00c1940251a9685281e104005142e0800c26160121a000040350120341c1041c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 15677488 1250 15676238 15676247
    0x71401090614060904020f0303070b0c1b03040f050108040212010e06060907050711100c050303090a061505060d0b0a090c031b0207080601030602030c1c0c030f180f020d06050403090311010f 83
    0x2000031f442000581e90403119501e040c8111129286c000014071403c3ca0300720054125a442918540101c80d00c050040c5240403009c01603c094071854890054854a0003004548805014005032782c01403643d00342000c0c410b02449041c0040e81c0a4020380030301d14005c01000f10340d080051440c0107100d801c200c0034001030900c65000100170002c40b041900f00d1011a07080300d0031036030700200600c14480041440450b1100080c00900580300e8078092202c05881e01070000310701e41610503a46c00007014007400224400c50381100313407a0f00c0c0240c808941c060780e5180180588151a10100109030b0b40d002140d60b0040c151180758001941d4001050030510f030a0070951f46040c144006015103a0100c0400c040c1c03007000c011246100500140001e01c88400f40400008186420074079010030300c0d04403501e01309456400361f04900c0180c0055200a683c40741c603600d490342180360080341d000003104440340004109210300bd020707a00a5542c5400b080c00c500e000090030643e4000d6506101c200702c4a4001190311 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 15678738 1250 15677488 15677491
    0x1090f0b0405041a0307120c1a0307050912190209060301020306010c020d0f05070b0c010c0e030c0f0103090210090510080f0c18280b030c160203030714010906140609 73
    0x2070f2400103c2840c1564240032003007503294410341c0343c0a040c0b800120008401c080d0408a402280d40740402e80c2c0d90850213801c031607950701c240119241400056081d5019030081c003022440903040b1800c00c40d03035140705414041d03212242c16030071207078404420650400c0800c00340c3c080025402140b4600740440081c00f0102541402445002e408015208006209074882680d580c031504544a4a0700c521400b252a0001208012a980307071104000c18944030b50036103251010064050800240380d00240454041c9203001607040c903482d0702d508401038031041d52006a1000954841c50594140303c100010801009840c00c100100d10060040c00b20303141c803032580c02505140e00907588017034000089619107102c05542d5480541e405444182d204107041d00660602c1c40210300643c5034a94498000070301069952010341001440000224a01c0410a2500c40d000400300c80c1001c03404d03540c255032042000d8800c01e00740d4441541038104506401050015000b0f15900000d130300d0604040b0750b861700c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 15679988 1250 15678738 15678749
    0x1020702090103080906041205010b010809031e0a0903051506010e0a060807050304150905060f0105120a02100201060e04030e030111070308280c05120907050604090b01030b0a120201090f0b04 84
    0x199481d855910041114010240c0d21494102c8c8940303401d211b4001d09003905030a0119945c3c400050181c2c5022044803603d0301568280a20101c40ba14420740c6a044801c0c0b00052009004010000c11000c101441c100e060110348030b00d251521100040c03034680c1206000d40100050b110500c00c9641003415070303a04c088180350081e2070340d440d4100f043c200f140c0c0301c0c2d01c040d02601e400e200c4818080040f41441c0318080310b01d501c00701a40e03180c0502c0080c0c000d10092301aa90042a080c400524024946d40f41401682c030010a42d03945403140070545000644080f4085181c186046c07006040c00e02403046502d0314407a605081654546010344244e1b00240710300303011401119540300f4138004001d184601c404a1000b004040d03540c401c0604940e00401d0001d07107401310180096038640c1d0004e408400d072800032f00f081e030625140c840328a015115107a40f030b030b050507200d005911341c2d61038002c0c1c0c40c802045865290002c0462600024200051a401c6058805028207062086050b0282210200c60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 15681238 1250 15679988 15680003
    0x1206030606030515012402031201030308040c0b03130305030603010921030f06060f050a030e010f0e06090f0c010f14070b07030f05071407050106030206070605071407120e010507050d0f0e010201020702090103 91
    0x2000c006e800c0741140704074460115600440c5001105140d440301101d0300c250b00c0784545012143e201d034003c0100340401c032182d8036a034241d4406a80024070801c0910740105000e00003160146d82039903068404000c0c006950303070043e8001c000c00c1030550b15002c0c40100c54401c1d0410444c031030425200030f207085e07000303182c840a0000019484d0a040d00c01d612000d00b40741d0f244020000109a24610006810044a0b2280380e100b510301280c0101008078005070700d00d030064020312000721041700554034101d407010035605201c000c90b5002e40396000701d0001c004d200e104510305500351030100e5020f4200d4817140c02c8040c0851900040011141c0c00512203e1858401c3c00c0641d00e810040c5003690141aa13600000c5d080302f0041603040421203181c0005015a00300e407035400000001041606a5000320358000c0c050a01d0b40c40742304041070064480c556078441c103141452410180b903ea0317510341240b02038400c00142030340c044801c0c00c591080707400b000e16509100a40c900006c070340005a015506000141051 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 15682488 1250 15681238 15681299
    0x207110607080c0114160302030f0f1b030c0904050a09020f040f15080304150c0c090c050c0303090a05010506030f0703060506030a150204050f01030506030a12120603060603051501 79
    0x86200c040d600d803488500000e12643c51090002ca080d00d50580300000d200350009040540e01f8024002d0728400c1c095907198550b20350724030384035042c141006040e4100035451138001c00d50346808800110f2040711a1000c1c20ba503400c10205200482d1030007050380fa81c0c0c1c0d18051892005075a41481c0d541100022580480c4400c2c00b101400010001509030700b41d1414503400024a41c000440607104440542015500c180d44500d800d40300300d0f514810040151681807028409a1030f90751110032050f40d5031070b103e41070a40902c2d116143d54000c0c1c0c0c1c506041e41c04050340104108007402920ba02441c1540505000307442440081d03038400d02400000d2100307403103100050b070340d8030300308150502e00303801403900c8010120f1482d10800a501030b0007814020f40c00c1c10001e403c17550180c0100750041d81d000c4d0003021041403e4880691034684c02c242103017040010b081c14860f030b01c401d005100185005000c002401881d61030300da80303401307071502c50000041a418010801c0000070b04c100d8a01d031002c2403c42105 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 15683738 1250 15682488 15682493
    0xa050603091b030c0a1701050a1107030c05120715110a1d180408040303090501080408090108040f0602040810060e100314030408010f0606230301050d0c090507050910030207110607 79
    0x2d04028804054100c80754100000c0c8440c0302006c10b28400c3c0c03d4100030001030300c03101c1901007641d00e01e9940e220115010032039500001c1c444c514074820a4000c6041e620301c107000300185065584021816103002203185002d0100b1500b0f489034811004a50700340d40d20708503021f140038040c5c0d400048d51050008540c0328004007926900c1c0b00d4594801300520441c01c074070f45494000c40390341050000b0b80c0040c11001c00400c3d84d5029010302401540c00501880c140b6101400440f60464024070841c0c82038140b45801380003514600113000542070355005011000c2d46d000c1500101c400d507a121014042d0100c06001290b010215100c040d0382d00103c0c00e001d1641ca80d8522031170740c132940d480b0082c0b541c6442c82d50080800d03e540b115003030390030740e81d00c4e1100403002035030b00c204071030448600c2d5003421000c0004015902c1c1c441040d040031882107a40701c43e16690782000c007080b28800ca45400110300006550241e034980740c1c2050070100310310704007103042243c1d40c0c071552030b2140400c140c107000c1c24000038200203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 15684988 1250 15683738 15683743
    0x1050705071b300b0103030c050f060705040308030705090a08010e01180209040605061203030403120c02060702101e0f0506041401080c010309020411190e1e0f04090f06020301050a050603091b03 85
    0x403025001136407165a942d580c640240700c03903400300040d1154090003407401064800450038500503841540d07554103250440d01c03100346035840070f401f68003800003c00c05c10b4242d07121311b0140302c01040c07440000183c2c0c1c1000015242950704a2940d2440701040300c0040340183d440003a0300340c1268000a001072141d48034808540c160b00d11041072000c911001c410042059480a10000300d840c0d08041401035a00e030a01c03c0e40c0d00c0c44240c44c4000582c01104401560b00025407154029032601c0303401c0b1a041081c0c001c1d10049810380b41e0102d444d181c46508114160030a4061200c0d2442ca00c050780032590f1520a08585900490315410304054640051100b5036a80360000031601c0720003881542da07116240484581341145c0351000011a441c0d00505d1920701d09070100d060a200303001ea0784000d861000040200900c610416181d0196541c640c8401240d581c844229009209540041e500d50410040000c40718040d4440c900c5840104104086d00f40040745030104101c110502d0700003401600e00090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 15686238 1250 15684988 15685079
    0x1140a0e01090e0106060806011d0415060203031501090f0603050702030405061209060c0306030d03050907031415060f0d02010e04060b0a020a0b060a030308040b040303090501050705071b 82
    0x102030541400000c2007080540c1d0085003c42000380c005c21003542d0f01d600030340d62882c04440607030104030802c007000403004080649040e001002400069500c201240b244c100c1c80054100d400140e0001c4108075000407800c91032000d8030b609003403031400580390190b4000030003400d014400030962100041400f00e4020019600a400024100e54030f4071600f00d5615503009003203552024600c248000716040c05540000c80303004001c0a800f410000391000c0007500517107000f428a0711030784251080000450340d14000304184e4480040608080c0d4800c002c96250300001400340d9125900014407801280d94034502c2125060342070070501e5600a1000025004000e5540204200500000e0b6210300c6030380450201691031082241600d19250300c002c3c403411070040c0c000140491700e000302042c0458410006560310610902c0c0200707070f50345160b482609590381915898007152002c0303140410065444200c0300c4281c189c00131448002e10307180d50004000e10003410950b1410b1403500c41c0120800841001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 15687488 1250 15686238 15686249
    0x5030102070f03020c090c030105061309090302010c0f080610120f0603030503011802070804090e16080a0201260703020901020307050f03030402090f04030c060f09061506020f010b01020601140a 85
    0x86403120228104050b50748a0454210014013030000045118a0100002401416551035840c1560700b004240131440d80095000000c1c900349000008e0015202d00880321224440d5001281d40068001c001c2c0050441c40814403d21200200700300081d1070701080c05210750110300c1c0c4000d0001e8455031040040c655910040e5440c1d04064002c8181038115000750b048950641e81007950040003840c242c100c0c0100b003402445050100030400c104e1617917401c100c111007410f0b41685c4c3e00c05500c807218084204c45a0200515412641040d0295038201e111741d010540c081e0007005d030304800c20600d41d83c5031100074500024140c1c0800c0400321a4420810369007455440800ca030703c1c0890f84c22160b1f9a9230801c42d400c0b8807481180000941446144101c140101c1d40740d141c14941c0d010355914440540b10300980212420307078a1002601007400c0e03000d41e0300885017840c441c03011300d030501c40c000342000c1746144907540b107a0624110040c503907800101c9504640c44100540300007403910002442e20081c84d03000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 15688738 1250 15687488 15687491
    0x204090f0501050114010c020a030b0a0204120f030f0305070507030f0e0607060605130b06070303180c0b090f040506031509031e0a0201061202090a1a030615090f0105060307050a0504050301 83
    0x140e02040030550056042e1136a00030749404120814004541c1a10780b010003c1d0003803012031040001400405506d504941c144001608003030f20307020710344102c0140c800256800c2a100b01c6000a154010520801714a03d17482c05010501c0d008102600c240320b0010001c042042c500340a450152140c5250001c0c004010700c100d9403a8070b50704000c405007500780070782ca1081d0040300c1e2a20340303d540b5108003240d410000d4050f90821040d03807000c0e8028042c259240303038035500d490001400038031440c5449016252414541ea280c00385081480304540250103414081c615040910201790341c00201900c840c80c0c0050392941550b6030b00510b40c1140039200d08000200403d0489178150203a00300034022406550b8020402c06035140510708104040400294200317170400082050161241c00000b0f00001860010700364407220745c00319151440480385558000352842c988e0b0003d252110324a5000104030000070b00075410440007441520016052106000001a41c2007010b0300401c1074800a0500600 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 15689988 1250 15688738 15688763
    0x4020c01020d050f010f03140106150302030403030c080108030f090409020a06110d090b0901050c010b0904030e130905061512070308070204110a09060f02030403050303100e0609090307020409020409 87
    0x11014042d4024070300b941c50407030428001a078644114907496040b682d9068003074420a145841d00c80020012100701e010a5498220105200740d40003020f0501e281c5940e4016035038902404c000b8101c8280b16941e0080110310f42c0100021800003090f1841d00e11014800c070740d60480c40c000140100350311000250000e081c3c0d0800241d06401500c0710f06411036040640b0384100c40d800301156486901c0c01060301ea04003e100741452540300e04081c1c00c1e8190000d0000440420500020380c131240304032000c500007190044900031078140402e146080080d455420700c492a00c6641c0d860701c139103005040c0c001d11403c54509008039a01d0029021100041a00f550503ca03140d0401c10705991045c40281e01440c1049207840201141d8811614440c0c0e20b555038109140c01c0c000c4c203d4a141c00c07134201000b103200902002c070210740240005c5000d1444a031442000342c2c41c0074440310b016074008041d10300c5807415804201541002208486425034100d4001403449000e10000c0c00800d88068098240000040c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 15691238 1250 15689988 15690007
    0x50405030d0b0d080301030605060d06090507050a08011e0207110d06050402030111040509130203030d0e060910090b0c0f040929040b0f0402030901060e100f06090308040311030a020402 81
    0x200400042404000c140b0064078400e051102c50006030303d008010400800041021540d594031030364000200800303065151150f03484003826a420400c0070303100b82d006184101b00518000c0201001412940b00900681c2461303410310106203030315121301d05940d070001a66420021080300c000c112003001001881740ca40f690400c000181402c0300c0c00c134020761030500200c10701407c0100740c83c11514020120001a501d24100d1800f07043d10341c004913094441070122406014160003100301e40e4900c1030060000c0d240c45c1a64900c1d128414091141c0c087ca40f9450501040c1610451503108500d81c01c0940e8071b0740419400e421350f00c0b40d80c1c00700e4501442c1012003040c02c5207006003c8030201034054030401d0000c00404100441d10b0441000340c0c8840d840303840c1d41490406801850b40100050700000d09150760380702c0956504000c540302c00c090903100105101c03020340488880090480c13864880c40490541e5a440075511950002600c0c03070300340c2001881c8543d0b04202c06600643d028005646175903181 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 15692488 1250 15691238 15691243
    0x30406140c0d02030c0c010302030609070c032a03020c0603090607050a09030c030c0501080a05071b060e0d170f0f06010c020d05101a01080c070303020c0708030c070608010803031303050c030d050405 87
    0x34030354803c1740c1c000e030060301c45617600c24001d0364001d405c0208900c0541d01e54071401d89062540400840a001d00d92011501500c40b1039500014000e10031156069170400345002410610600c07043d07441000c080c406d00410100000d035040d80505181012035854030364a80a841c00c0d11180e100800410300d00c803010040210500305082255130a0b00d03522982d860f10301c00e48040d5142201c1110000703110026980580c54095040c0c0071007401080000341c1080d038161a1814000006000c001107a40390440e4581c60558800c0154050b00c000c1e056000380c100800b12202802000d00403604108103808500295076490740300180c11031b0f00a003141c03103841503521010041c000f001c00e00580081001400c5200754045d00c1c0710b900c03c0070000c40c0b10303242c07030b04695040d40250040c41881c10b29210701000441d100d0000c03c0104130340c00b45c0000a0980500d05030004280343c074143c00c0008207410520a019141030b20b080c04103180399044c10415250400340a403a0b01e0360080d82c003442e107428140010f010038403102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 15693738 1250 15692488 15692497
    0x20405071b08120601050c10051308030f0106020607091d0a140f060102010605060a170c0702030d0305250f030c030b030d0905040b03010603030c1209030b040503030a051503030406140c0d0203 84
    0x2c03039009613074480c01901c0e0b0b4022071a4404e41c0390002041c20035640c045611803a40143d408546922200c19170b00e440f85d290300b049901d0b5410701807082c0140b1084c0d40401155a02038154603042c807483c0c1c00c110110824a502c0260390318080f1602d00800c1d03c00c81a42c115254542d040751400000703141041c1502580c52051311020b0242d4030340b100100382410008101d505100d115214080a07011038901c254060f20700801e80800c00409105400050b82c00740042d01900165076004580c07030602540a40d08082842003803900c2501e900091803581c0c1d006444104c055501d801c1c001001d10702000700b9806800f48000c0c42c0e50600500030b48826041e000713080b24081e510141c43c20450301c01c19000341070232074240b400003074003040b20440d1040c0050444500c280030303101c0c18940000c10903035941e125862044242e0382159a03030400b00800c80140c0d618842d05a02910003284440b050350210003190700d901c6035001c0c45c0c04004201140410b50407641080721503842c000d41c225040501c0031100203480760403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 15694988 1250 15693738 15693757
    0x70609020f120c1906022a0d0c1703130e0601110d0f020105010b12010b0f07061503050f0604080318160f0f06030204080705010e0102150405010506010f0c0b04020405071b08 76
    0x31222240d4013910348020000c00d55199800500c248442a4441c1d088440900a070308000d0b0b85440068815841d4502e245800e079100d40600d840301c90070f0003001c01020041c1d0500721500d91061004080b045050414902141e0b0305210503803182d00c80100403105000b4148a0442a110340c00d16a800d02e41e001a041a940700e00d40d000700724603600c0301032a0300144030703a80350a07520740340300001806420081801086040080c3c18880d2401c0f40c1d559401058800d2540520b00280800c20200b06208043c881c840c1c400c03c1d00e40c09050586400c1e5150000703404050030b05010101c1c1000000d030029010800000c0d60071075a01030100c0e19a440030101c02002150003050518515800c00040e03242c00b81c02031b141940e50180142140b40d00340401103aa80603070000c15411881803411105080895006a50040c0d0103640045560b1500740000b41ca1b444815040c1820400600c0c038407004110070790a2241c00c05d60407030300462107813102c0404030307503d200c46440bd00c000da218a5140c0e04004004c0010a0f9140 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 15696238 1250 15694988 15694999
    0x105010e09010e0117070306141b03040309031104020c030f0a032a050f160c05010206061c060504111201090501060509060603071215090f050604090503070609020f120c 74
    0x10212001e01141c0711081c4200c203030000c14076006100807060200940320242c0c2e082c084034141640e0b034071900e0981d00310b00d500304a00f80191060040080c1070640513840591000030f45451410660381c02030a6040601c0050450b040110300d02c880d998881c0c040720451080d460469855118142d603042607070b40074180003004030f032402d030550102046180d002007540840141125100941c02410b13600d40c0c1c0000346000402804008040403290006180040d0900904101105608040000e1700e09840902010f10a5031404155244410303d105aa159a0b40c005004246601c031803034111041223002d501c6903800142e903514002032100541c4003559144c064402400420b40d1501031051480d400d03140303070303412020401c0052140390040070040c135944100030000034902005038401a01001940200381665224041da400c0350120740a281c0e000b602c111020029078915070b5455030307284075100b4024403464442c1c2000341550344610102401110142031816003180400089484085d4010f403984900d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 15697488 1250 15696238 15696257
    0x608030c061f0303020d0305040201020109020a08150c0c03071103010b0301050f090615011d0f060301090c080c0918150a090203090d020604030207061119050c10020c010203030408030402040b120303010501 90
    0x4000440e14811030b80c0517006003103a40300604003200602001001a81550348521400006844031800d00f001085840041c104910000240c0806400050034185600c6c60601c40310304017180101c211048076a1252008032507d403200017180c05003080c22409585946007800304a11602d02887d03540c400d0441b0002d0b12040d030340c0d2031404140c2c0a0b142c11440c0c0014904030320b950034201200a038000c0b49900806040d2007c0c17501d000100154000d80100020035102c24051980d01d4001401031307008142006924101203050380800c1c0405640c66405c11400b0920300420040c03203c040c90108180b4000e003d84403140c0d15400014040d5005542d182e10b284a1590340c544058404140701d40510760503400f130900103251000032608155800300c220114000c2042190941a00101e80507149100d407024213048103d180c02c001d48041103818036811f6402c40340b8200200d0381d0201c2100d500c581d2240c40d440e00c9444074004100200b0b88039080c4d6401952980d980203a00400001440c107d84007641e0f00d0094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 15698738 1250 15697488 15697531
    0x150a090e0c1e0406050405090402040b0a080d0201060f150507030512040f020112090308010506090604051207050306070203070f031b02040e0604120302071104020c030909010603050103120c0506070e040608030c06 93
    0xc83c03007144a03800000c0e038248002d10503850801102500075000070008101d0b11300c244000340700b00c00191b0014a10303500480042c2c1d00540c0a0103100018004040304084035072400031407007641c80140c2003070030422000184c41004c050107101a5030348450400c1c4400071a00d00b40c0744c16208018000d2003640461828803008016804600660b0082681640c88400c80e92901060142c2c0740c1205031503580c022001c0c800840c5503210031000d00b02c00048200180b46580c034080900d410300d14058440000c40d002040404041003403080209440e960614119404454107003403007603040340c0100c0007540641008030440d008040040e080d40143c1c05800c0348410400b900505030200d03c58401c0041c880305a900c00078200b490994090315090b4601c8007524601a5446d001a11800d003d810001c04256240014028055a61900818003101d810102034190150301c8643e6a900010104020420940d0a0a60303070b4543c1d40054004210320021682c4906004050b030351100d5040700d4101d009004c0c03070040c11f00c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 15699988 1250 15698738 15698797
    0x60a0f05060912070503160509010603020301050312090312040b071101020d1d0d06050c03090601090b0904060e0f0f0102040e0916060503130203070e04050d0e150a090e0c 75
    0x4560005218502d050160014010761403160f2003016801d0080c00d10000e070b0740d01c040c8180c40c00c2d03110544498014500740b0041001881043e0072007800c0520620040c07203c1c0e2000207904240c411065022a10765520304002454040d002e042c800b03422101281c00100086104c000c2c3c82018420200c05444844005c01207030346180c401c2c07444000403a640b41d10705255645c2c8040c040e0059000d8407000f120707132041d114001a40c3c0280d6084281300340c008204610b52074140a000d015003260310042c06004180c0000440d001c1c0040c1014102565501c100e0001d45000c1098003003d10310743c4c2c1592490400030340010700035080761040d1030107680700702c001514200d004546801c00b1040050524000c0d407c010003280d07260002400340801103080141c81d409a6410401003004001034a000f45252409142c618201492551100140180c0940700203c82d6030304044400710988152150381c503500000c0040701c04502a0b4410101002c40c002031103c4d04450a004044034810b4111002c00c0e0000001444c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 15701238 1250 15699988 15700019
    0xe0d0c12080307111204151e050903070602010501030804050f01020307020306071101140402030312060a0b120a180203062206021b070e010f050904230105011e030c09090c080d08060a 80
    0xb1750820f0b0401050210100300d10340b00c400c00c0c84070303d0140710900d1002c8503100006130080311280841c0d00820101144c0c42c04120702c07005000148024003565146a81d180140e000f41e0250f036109030660801004c49034820403d80c1d07501d540003411158142070200c07000c2d00d21042d0128407032095090031180301021020460107401541e002c2c000b10b2134040e5a0088840200000d440d155001d80d40b00c1e00040c90354070b04009083d091000045188603802c00000302c000f15040c03603001000c0400314660120150b035000c142c881e40100c10030b0707045811405114134101e102c2c40d5a50020812072010418101080c24420b403803040010034000c0342c90694540d1304000400da0b09214415103000030f0b00090200342000010150414455a415903052805204401301207250311040207060b95158010003d40740746121842000912004101101d415515022100101402400e90f030b0b0740c0f5580e8040801080306208070052144400f41c03624201d441c007000749142c5058070050300c83c411441c0046214040612580d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 15702488 1250 15701238 15701263
    0x19060c050703052a030a0807020d1d040b060405040609020408010b09091b03030906030109020a030501090209010905040504080705030c0307060e030310030f02011106010b0403021c02010e0d0c1208030711 89
    0x450400c40c600d284201e1440814a40c41641d4080703101a640101c01040074240c020b1b41c5868500c40c1380f034041002490928034a220b4810400d000c246c404138a04105c560104001c419100424800051070100340c4a12035680842d23041458604000360710807040e4054800c0d904103c0080c041041001c2c100318042c1000c0d43c0c01e1010b60404c2d005a0b1101c4c0f1003404200300000301074140c80c1010a050001030740b580003603110182c00ca40004603201d081d0707031500c1000d01400c2c445000b10704106008000030441405401074600a0380e803400401c4c10301c441d034002c0d550529803000459a40c2c083d0041d01d151280c202c10300c00c40300d190400044950380038010058906c100111003c00d442180745032203143c1c05907400b000680c10702586100c10f003030304c09090241501901e00290a1941d40340b44d441070251002082c0786105010303101d84180700050382c1c000000103031440220380c0700340c00c1d220794100018014907a42c400c20b13032000f5401c240402c1040001c091403280345680c030b5400007580c02509483c0c45450401d0322 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 15703738 1250 15702488 15702497
    0x20c010b091b0c010b1504030203010506030a05031806130902040302130e031813050f01061101020f09010309020a080f0705150705060105090a1d0c040e0715051b19060c050703 77
    0x2c0141c1194802d01a00e41040d4000010640e090340b007001c00d4100300811818050260001004d209504090040640000e0280e001b084203040580b5600d4036801803592401c1d80480480a4180035681c1c3c0081e14260307581d070b40705420042d80d07134079243c0007c0d40581b00480c003500703aa45004000114a115420986414002031458440c1c21401d80f034070101c00715801588003002010b0310754080c109120b924842d40c02400c100c411075044c100c0160410f40d4503840d4001031b80c01007103400346001c0005c06583c035240081c01c02240765a001d10005000c14000d4014283c94481c090081011120004031013086540a079021105441001c00042542c070484001802550002004121506125010f5540034219060009030703110510fa540290410546005019900c50403040b4003d1415201d80040c038074040b00180099443d064144800b4071080400b01c084c4800828144003040d10400320403902c80240094880905444c1072441030030b10f4803071064070124500009048280d000340103d501d1550180c89 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 15704988 1250 15703738 15703771
    0x90d05070602030a061205010b040e010e070302041107050303090303010608010f0b030f0a0209120105010504110a1b050a080c01020a030f051b0304020301060305030a050304030e0405150d111201020c010b09 90
    0x607100081c3d032018081c0105182d42c2c2d5400100c0b082401c26074500903104200201d1030641c3c2c5010002038a071201c000c0e0280d645040420801d030000040c2c01c104683c0d040c1c0d000704403102308041c0f4011034000c405001c0d006000000c20081400c038040000c6050702d629848000c00c690303c0725410903144500d4056402000810400300d03045403d0009503070f62103862441d0143c034200200012540484541d074800074282c0d15000180500d141600030610f440080c0e8003120300780307103028100034030049904000388840800c40e03c880c0c06104040c000700342000e0b084480c0a903100040c401c0c2d18001d60145252000003854030054002032580380c06503500490404402d0515443c0b002811f4000e984090030480e89517507100000000a071080c0043c0c41340e0004d0351201902c0746441e04000d030103428180c01c0b1603c11450001044020346805040c00e031010416115070384124a1850031006c0308450b264510b50040c0240c02600980e40150000d1804a03e1040280310314600c110601000c0c0c00c0550342e210f840308003000e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 15706238 1250 15704988 15704993
    0x50d02060c041e170a02010e0613050d05010e0118030806030109030f031112040f0c0f030c09020702060c060c030702010f050f06060715060e010510020a230703050f010603050105090d0507 82
    0x14180d0300f050250f601034180080e41c46000101090642c0c030f409409030040716043c3d0541d030b00020703114510202510400c1c0703000070154025101c2c081a0090303520401410105909011003580090104580340c0020040c56a108111664041e100c10045000911050015502d810180034200c51554903848489100364211002c0d006010048500b42441ca410b005002038501c054890b80d000f1070003951020034403401420072036041405070700811042c22000700100700185100d07011004030703022030744010303203455861001078004c1c8581c1c0d41b605e12034465a4280031120840d14011070260340c1640080200d01c07040c40510b4151036080724480c2c1640603480004035107082120040614a00c10340300d00e90b401200c50b120400b02e0b40c15400404400c0510001408103042016039000e00f800140003d000d030903e640e8442084802e410b40304840f101d0f02060980001400300180b030090360f403001c182c500489035810f00c0c038020440b510080e5865820000810b540b100c02054000051095036a410f25001040c3c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 15707488 1250 15706238 15706259
    0x151e0c030a0b030d1d010507020d080c01060b12010902070602040e070f08090a0209041728030606050909060f0f060409050f0601030c05030106080408040e07030c030e061504050a1103040f050d02060c04 88
    0xc100040c18080100044401aa03880214ac00c101b0312400d503a6031105039680c032450842e1610b8000c0008200c0400400c200300700c520300110b046441c6000b0140c0e59801c145400400b90007603501644e804021030007440354040d04132510041d4035000d80d031124800d41d1051040c0b40c0d541c00520010350800c4401d4040340103d10700b003604001031500d4043c418500030848081701320142c20713260059540c0a2206508103015854054800105500d00d040703801e004000c40040c0b80701c48040c2080303104544015845001d629950f011440701200241910349980d6240c4480010303160486002e1100c032507140001c3d06940c02440341021541d4959034950851b820140250707a5404060025101c01d01c0a200000710103220b0320310039208101995010a0007608514043c094607000300850b11550800801c00080301c0e1a007140e02e9242c0303000c50300452203494020582d001801c00c0d007644525141d000080100703124840040000481c454001c554441c2d4035000d040341c45880945481a03e004100820401c01244 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 15708738 1250 15707488 15707537
    0x9050f0f0c04050405250c03021207030503010504020309070504020f040303090803040b0307121407050c060a0608030a0f12060605090306071b020906030f0a03110708030301030203151e0c030a0b030d 87
    0x20005011b0715074161083c05201e02d0300c020100e070300240c106010181050740c10301c285403c3d405051100d9003007a002d40d80103061070105003d130600172a400300c00940c082c3c0040140000418014000b1503881815004000140c0c0c006d000641c0030807040a8005086140001180d0440744010201c90964407000400c0b54000302c48104050b440740c03070714044a0340c5024402241c0c05006141c0764240d840354809441c5003040310042c08400c5035071503c6003c0042d40f0020049903809841e5180582c68205403490607220800c6e24140782c1d19880ca003090100d2205e41003401840ca03010b0807021111180da80960881710030031005c480f0104139861280200042c204000f880f50020300040595413143c5000308183e02d0440c28820940000d410803006007454041417041c1e1015210b200091443c560554010943d1002d402c3e141c0c400403100d07040007607440e0b50003891041d0f0380c2c800c94017494245d040c013178000c0b042c6d5002564407202c210b01d0417600a419140c000341011032065141c450841d61880c90340d200020030074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 15709988 1250 15708738 15708751
    0x118030209040f031205010602010c0f020c0904030807090b030108010506030c0d080a05090d0204360201051903020909150108162001110d060305060112020a0e0c0d020409050f0f0c04050405 83
    0x14159050305d60304d003550068501078115607000042c404501c0400401400000c4441c00941d00f28401080e0716460b2030b01c03850750242d0503080c4240c00c0e0315103100c221204000c5511034040c05c600400086800001074200390b0003404118201e81d012040c04080102d10858000010050782c42088641e4002d40202d0203041c04010007013186514007841e03000318040e14441c529203800001510700e006113500c0c641400700000d00200b0580b0142000c5540041c1080c860300c9000a4003a01c0c1950120245100b5011031f032860002809812150600302006c030074144150b251180410603c0b8000740d0340724241041c040c1490060751342c43d41c0007880c4442c13840380051505141d68155490310382105030341c4001d0300204084002d01000056151840c10030798107084041e008202980c044003840c01c0503a85580d60101035940318404400103445d000b10f401c85610904244005650011400040c1c0100e0f0b507204502c9071120b403c8802d005d90311000004074200f822a100284c5031020303c024401c508141e48407a90086 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 15711238 1250 15709988 15709997
    0x60910061b11060d0903090e0603070306020706020408190c060201050c0d021b0102030c04080f010b060a050307020c03060c0a0e0103090201050a0c0314031609090e070302040504020d06050907050118030209040f03 93
    0x44008503ca50b40200c81206540c0d0310790564108259204803a03000501c80f0701e000711810b00b406030000c0e465400078800035081d00c3d0003050b0b50003072000070790440b00180140d400312103002251099602d218203503a007090301d1618040d000002c1507401805000d1050210b2041185070198200c0800c009400c1406000c52503030001090840b040b40c24801903014130702048400b51610328006100d49002005440110750340d04041190380d060b1100002e541b8415060300300340307480390350b0004100d02d4088842e01c91585817048000f800240440c150092240802603a80d215412101100540503500100390007070001c1da0402c040440c0610640b2062690b0744a4940901c402440507044440c80d001568188880002100d40d288800e4200841c1001040c0c800018407843c2005800c8507160b454510000e03001d542c031040014115540c140074044180d84c044420003660410b41c0c1e4032940c4450500680d808149018034a014450740f461240003100c2e4000e00103807059a941c2c0e0360380940000f40c28101c0500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 15712488 1250 15711238 15711263
    0x90610030e1006140103020c0a0201110a050604030c03120902030d030e01060b0301030804060305070219080a09081b090108070302090103080c0304030c0303050304170306091305030f04030605060910061b 89
    0x40303409001814040ca040b90000c1061420701d0a0340f0075803180c148406042c1481080b000085076400302d40c084c04180c09007025032108104407500c500f000340c1110020443d00a0800b0841095004211070544500a90359003881201e03031f80c6080d084404640c00131354940c0c05402d542005e548203400051074041444000319801d07030f44030700c40c0407240c200380c10850b01450003060034407000f9814482d999005416100070310070001c850780c031a00a040c2600000d0044007000501200f81170003400400f00a10002c070441d40121035512021219811000c20030f071054200c4400000d6000e0000394031015244c0007001c0380d0385646546d44640180e8403482d01469280414000080820031601d1103800445c086c0d1180703039481c9803078a04042001c501c80420b00800c1d0b014407d02c002921404007050b4003d0300c07202404103044942c10803502c3c40c0161305440c66112400038000c8104201c6070001c034004d250a0754588a55210f000c000c0518916074010000000d0000c401015104c1b80d0074420a10140101b4080121 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 15713738 1250 15712488 15712511
    0x30108060414010b0d051510050604030303020904090b01120c05090108030f09040908070c0602060c03040f1401110f09031b0609150c03030a06050f010c120509011709010e06090601030209061003 85
    0x164904401035a59400c541f4060609500440b0b0b01c6178402c1c030300300680e02a5410000014002c0c052404040e00305513001c0340d101501d407070302c1d440004040d41004040e9260369603440e4a80c3e214182080c1160704441c1341c2d40000b0710381041c10866050307844800240d81000304000f6445078036000100210360041d101c010031404528900d00034205203015a0109805c1810018040c0c500140074000c00305415040081102040400354041c4a26030700030034100c05410b0004460307003d0090f50a8500c102000043d0f15003030501040014454800c0039420741340c0841070009040b51040040c0080c1c0d801c04000c00000803140b9141c0109000b01c010101d0850620001c00c0800f49590000c036464802c8940c1d03500d0503c0f592806d0300411681070400d10f4069000c600c25600c1061340c4140c14000c0007409004104852560f001d1079950f280143c9074000c820b140e16110001c4d0b4068aa1445003111500580020401880d00440c40c181a00d401902159064440001b880b10741c02200c04c01c0010103503500c00031642d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 15714988 1250 15713738 15713749
    0x2090405010e06030f060c0f030a2009030106080102040e0f070c1205030709050916030c0903020409050307020901050a03110112020c01020309011a040204080c120c100306090f02030108060414010b 86
    0x203852041c030200b80324500039080c1450007032207003242c0207a07500c21020410407021110880f040d804180c44080d449413560360213a0041c10240c0d200c0c00684e00d694440d0b011504000340500f2044001314004e1042075a645203c9080344528040d07060070000c1100020403a070706010304c00d6001107041c03511010f451029140c2014401041203081c2c00140f0020601094981c03021b103280c0a8402216003126608003401508210103080c1009018540c0302c50366544031034081d1111100843d0090414490810b0610b131940e00c07a800144201e1107801d01c0c40010440d41001da081001b5207500c44a801d00600364800107560000a03154140d0481e90200006007030400e00780061802030034404000f107a032010a2903081ca81d0410002c00078001d0f03105000810046900203024408130740243c641c0f41d403400e51704c3c80c42404c00720020700c0c0035001348074501c030200465855408441201e60462041143c510f42c03c0c02207080e88001c0c86441c00c00d52100b030200b4040b503101c415402504030080000110080070f90007280 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 15716238 1250 15714988 15714991
    0xd050a1a010e0610050307030b01032003040b0a020408070902090307090603060b0f03030a020a030309080706051602011104030201080f0709090608030403050f0a0b07050d02130f030210080606040b0d02090405 91
    0x428129000c0040000c08060380007541c0020b800c4849200100e002c000040c054003005020004161f201d218404141e4003039809440380300c8000003060180800740303440d440755501c1541c0880b110410b640c00194851240c3c030a54050300c0201010b000605c4c40c2c21f48040103500b0114181758140030b00c00300012440f5052049000940c03107048085501d104080401405001c01041c081c0203810400450f91481e60100d0700010b181c2e40b50400190703480c214100f02d4200c1c0909203004101c58034100600605c0c91a030013040d086052658024464541860701001c0140114400240411000ca010038148010a0030444d400341d001d01d0034000050341c0b500b0f0724058502c140e1041066800000b01402484400d00c4690001450b40c002026144034039511485e074400d00400c914104030303021a00f034800d00d4460701100c440c4680c42403601a01a21403141d141450064030040b48620114030b82001064012030b0300d41d2168000604150419140c03031916001ea0784055407c0720456420002085555258801ca5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 15717488 1250 15716238 15716273
    0xa0311030927070201060303050d09030c0209040606050a0f0e0c030a0e0703060b040b090603031803030c060f0610020616030e0a020303070f03090b030405030910031b0807021b09060d050a 82
    0x4502d5001141000b03002001c050511011a41040b5051012030380110450302101004403000401888508045843c6104054000e61041c00c1d030090105012584d0083e905030f580c11034030303800701540c0c039000042040841e210342d01d84c404640700040c4190081c0409076610201e00f000100e00e202c45541124142421504103c440b150785029140c9103050a204d4050800070980d951100c904000c800281e90303000d903d800074504c041a54080042c1e440a105072170b40c1d004041c4c01c80e80741d41403480001d00b4001c000c0362250702500c06020b00282040c400980180995030781a00c003400c4200020080303000d0300d074959034190b41c1d02c0744203a43d1005072000c1000b00162806506204081034207460024074241a0f6400516080780074800e02000c0b40340030045031030310202114030640c0c140780c0f020150b010b0549504003981d8200840c4048020710f8010400f030f482955207034250740e05402004c150102081e4683c040640246400000403036a09184e0804000079020f402210503061a99035841e01c014bc030b002c2c10 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 15718738 1250 15717488 15717529
    0x40317040b0108060601090b040b0708040e04050607020105070c020907080402150a1806300f0e01021b160512030c01110a0909050705070b10031509030e03010b030a03110309 76
    0x4111003e0140b2010b6004942440d00321295460494001d915026501449200030f800080b44410003034490301f00d400421103500b44086520701402d04507250380f0121075800141d420140016050b511507443c04803c142d00030224081625881c3c0112600342c0000d00490300304100d51500d420841c000c40141030120019554507030300860b00e00c68840440b04030b43c00f003800c5c400052040602c100700b01c2c00100300c0f9a80200071041d02c2c90b203844000c001c4d02c1050303041400c041c94650b18891011040d00100303841c00103c00e1004240303400446081d03903002040c00c204d509401402044c071079403030507003000015100072100300c07824461885041801c4480000c6c454a0741f900c0090000185504001c80b880144200541042030707150001014200b403140b000020011154100040e40c00440515184003458203c045035511442d00c0084070000d08070f103641503011540c10701c40f18045242c14001c1c86003185024000c2c0501c0d10307580d601911800c80350b8603c0300c1e450209000c014002d0310b6450030018101d510500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15719988 1250 15718738 15718741
    0x903020111130314060f0103080d090606030c0501030b090f0a0209060702040f05010501021002070521070f050d1b05070b0c03190509011d010c030f0309050102030a091b0e0708040317040b 82
    0x400304c03603540d41040001402e8200c14100311024442010f07060459800c0701042d540d03884091011f400502c40048001c20f928a040e501201784144040301c034042d03c0003031303c0030054080900104070403072348200c410444400100000811a13022a00a050141009000c50b41441550350000701030b0703501e000c1e02c400d20130741da140108031a40e810000111040d041e00011860710710f0760b0b103c203501d034030383c0c0800300d60011030700503030001aa54407408a522054002c80100301f46290362601d11f07103909881c002800080d5600402c2c002e01e0f041c00c3e13041c8000551020003048854502a4022125044170035122a00c0c0010b010196800c2802c02004043c140c456640ca0303036400702c160014010503400c1651140150504030000d4141c1d03088000c1403503440d018200008480d035002e10450140c03141c01c0000303095500100c203100e400d1005400c0f84842e54422080d80c4035000101e001000462158480e1540500030078012414484c0225001608136003e49000d00d00094103501c00c505481e010fa80c104c940b04000c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15721238 1250 15719988 15719993
    0x60b0306040c0c05030405010e0f030d17060307050307300501060302010201050a061d061908011b0206070207060302030c04030206030708060a0608280621060c2109030201111303 78
    0x2042c400c0c900c0090078800908203440d25415968002c5000d02814010b02c2c1c10f4100255443d600d00c81c41c802002802c55298510700b61004018039104100c0d40d40000d030030004101c051601088240a90340c0c0940280485450a44401d0203004051490304085d80b110302450620810f0242000d1800d004000101d541c9183d40700090840d44018998000c051611109111900c020944502c0070064822000c1d0191120400100700742c8800311540106555075900007802c0c101900508a00c000544213007010302003059040c0d0b15807404a48a0340103810902d401e028180c0030798055900030302c12686150420391241d0120700298002c1ea4800d0104d0010303010007400d131415007400c50140a8501d422406810f0940410704000003074030148142071741c502000404042641e120100408a000181480c40c035190320b560340c0f0303400841060b01c883e81031085140b0068024145108082800b0307451880100303013800c18031300a02002c0d10032402c5540343c080c107600c1d44403850082c00885050ba600c8155082c95403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15722488 1250 15721238 15721241
    0x3050a0e04050f0703020a11030406090f0e0702060705070503040519092306010f17010b030402090106020312160509100306090605040902030c121c0c0c0501020118020112060306060b030604 83
    0x590016120780d040204000c4100c038521034054003c555414003680310500a0b90940d0031403a40c8002a41f103100c0400c000800642c8403490404452000138001803007922030400d070480340d20458084000d41d01c00004070b401d16105a00402c0c0c20341c09038059a04140d1504002611343c3c201c1003411000c0200c811051261200d01d12440032008403040d00d0712081a100358024040c804003d005506008080c82d00300d54240c010044150070070000c601e070380c0d80e540e1a00e180313a07042d40003aa401d9000b03c0d100c40011402e10300003c2100e40c615002c3d03413403940c00c0e544d540300390032419030b0b034008441000403d10104a240c5c0742c0065852011000c2d40f40800c1e503508040c1084100e07416540010711540c2081c0600d40135031008544802d003200c0580d12404e00b200c54448292414002c0045041c1080d51001004030103540020603404181c425003048281540e1000124281d4054140303520903c071762215400019070103001c0c1002521850040403443d560b0300d88801c811508240d215400c1180000704100351490103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15723738 1250 15722488 15722507
    0x5030409150501230d020c06010f211e0f060509010c111612020301060503070303050a0915050a0c0c050d05011b0503040c1806050d060b0102010608031c020d0204090903050a 76
    0x70720b403c00500b960804d9402c0c01d03207001c4000c90b5844400042030a101e0f1001e404991800600c43c00b11050355948070603c81c14540c01d03200b00c88240c2c1c0310342d0042c611500d201030b10450032504900c440314281c0510301c00314054228103404a0781c0c90180d40d20140022103902442d4850701e10400002509140300301d001c0c042e041a030003045c0840d089420710039203c2100c0d00100041c2e4211242c1c02c80065160303c08640101100c0c0c1100d40d051185400000406901c40c0080450341d0003a524440f25564070404251842c2c000460070011410038010030945034820318036849417034003891041400c16656004140841711040041d961a5110003052011891250000304183c44520f401c501c0c1d031415807158016064180142e0341c0710030610b04a41d1500106410000c05071500030000b1460343c0091502e100100b43e00143c140c0036500300344000500210220954140b41142d81b5681c01950115044200070f50204030303c0141c05a00384400b0030410307050300c1103100e010300c00e45807665116a0364a014040184 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15724988 1250 15723738 15723749
    0x141201080f160b0f0306030307020a0f1403190303020703030b040c090806220f0501020403061d010e0c03030307120608030a0302070302070b03060303070602070206072a0603020906070b060604030503040915 90
    0x4040410400c000c3c0d0081100e0840080d10052a1070f9180da034006415442400d002941c8880e0018011031110b00d00c1e2120703c11106402c4410340300f09a44424981c80e40003194400600c4010406410b0200b40250020103880d40f00b40740001d0b5042c551000101106c4280c2941c81c0000c82c101c40900c040c3e00100081900400743c00c054400b100201c1400848682032800010101000d426000e8200f0400750140c8022b1507101406001039420f0020b82c2c40041e1003e250091150700304004000d0010700412082f0000c000076001d117107103948850060342c0c03a60641040c10102030760f03000f0000b0380c0768040c03019065a4290b40d030056a25005030400074542540364021401101d0100b0901605640020483d4492a80500c015031243d91038000180640580040940341031509561541c0d41640008060040311990201c12003003522128101c04078020300c420503030001800c1003144089042100c41d194080720003003c091500e6102e50761541550000e60202101a07158401d00074004d40c841c06480181a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15726238 1250 15724988 15725023
    0x115020109020a03083610080402030a020111030702030106090203270604020d03090b0310060909150b0d060312020309031902010c0b100506070f02030106060809030406141201080f 79
    0x107015070009141d440c00c2e0f00c80200100b000003441480584051103031081908070454901c0c0707036002034403003180110a2403469071055802100c9191032070f0040352000e0040e50080d0082801c02800e81c010f45411545070307041083da120a011000041e9024094003018014005c4056104d08101100c200848408040782c42c80f02440801d046101303c002420951060f0125940040c03407009080968200c07020303030403c0629210000801c00d0090307100d40c0580442c0c4090b84d07520583e80d44c45800700f00b1900c00081d229031144034082c0412220b51010003504204001c1c0c0c030f0000d88651b803a9542c84044c04030034982c0000d0b070008102c00c00345281c140001400544605403001d10180345500003012005c210780c0c01040b5620180c003041c01070551b011408094040a06180e40d00c002c90300302800358450340307542244a98207021021032001c0c428140b141c080e0008000450034281400d030b0980c1c4004008001c100000c4042c8071006500f40c1d4a1507880c000c01d03644000c7e0001c0c400c0e2910060420b04680d02c484501e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15727488 1250 15726238 15726251
    0xa0504020901080a0b0d0609080c2503080705011803081605090d020103021813060807080c010903083a0b01020a0302060601110304050301050702011b14030606090409150501150201 79
    0x50b6080003115a02a802032800205d050355000010082ca115080140003140351010400c20040e20030010326032040c1ca001111840080a400110007017090303151004503407190001040004c240d40040d00711280300b003001103140310359099840c4407c4000082a000034101c2800e100d0030141455850031804002d26201e03160040401c0072810003c4400c100904041c4c2c0024410383c00202150300c00c5004c4401401059005d034961041e401030041c03400740b60040d006445001540902c0042c01280200701a19141c6102d455620750070199005035041c004130401904e20b0070200d43d400141d0032003602000d01800142220300300c0503c1282c003003602640c199880b003031200010039000502168030510074607010005c0201524543c2c21401681c4c0119003540c2001c0500ca031958040d00100c40c0d451005907505208103503104200d4500c0108030440303004520400101c0c44505104006040c8000d000d080030800d00c00c81d03581c0c5601d84201e00040700c0312541d03c00060002d91b07040c4e03170201c040301c240b40700a0000c03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15728738 1250 15727488 15727507
    0x120c090314030a09060c062309070f050f0909160f030303060e060109031103070305100c020d0c0308070e06040b160b180c0603040303181b0603021207030b150403030e0a050402 77
    0x132a190140200b80003886c04000208242c5e0b4001c03000c26800302d0320084032005100c0e688011154152208055401400002300311440700d0310804040302c0d4024101400c4040640901c448030b540501001510300800349940a4010540a09070040442600c007500c0c0301e01c2c509004040340e0094200d0215554410700f071090580e40090080152034001071200c0508c240000040e14010181c4e200518038002c030140d2640c85503460b80001d1280901d9001e8a44509401d001120f403000c0c03424000700850306d44004180c801c0c0c4580b00291200c10050104d51400340c0711403c40e01c554101e101700d10004d8074003694103820000200d042c00d030030100c82c020440031801d12101c0e00361110700a0014500800e00403002030b0a05100e40c10164000d40c124644024211081c00e015000100e8030182c4080011910000107006100e442100c620b00c0b18200c3d0410300391149603089000e0000c400c2915448200c0e2010b20156021200081000354840d85800034a603182800b4044039002941c003da03c01c0c0d01c1030000940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15729988 1250 15728738 15728747
    0xc0305090303180118080304120e010210020a02120403120e0f03070b03040804030b0c04080d08070503041101090312030606030608030703050304020d0c03050a03080402091f05060a120c090314030a 86
    0x40028000d60b141c1602c000660f0b0050040c11420340724440991454485400e10941e400154040e0380640045204003202d04800e4400c6918607903a80d005a05c50032040c0180d80c199170150200342c8851040e03601403403810709844607541080d00b060f52024141c400c10a2944d4224001106418007034403100204066503002a494030110300c50450031100000000c2c082006840c21200915400181401c0d2400d100d441408690098082c0031880d100e05002d00c00354600a4040510686d0183c1d84c07203285583e141d6501401c1d90700c150110381804a034000200010754062200d040c07291541c1e400240f25464100000c050784d040394003a002c0c2c1c0d08204501c00100c0e91100c1165440398054900c0040c0c01c3e95840d0908100d10a648043c141c0d000e1500d02d44e04043c1d00c074803014002c2d4003c807001e1001d41c495443c40c42d1149451043e83d08400540c00c020801030800d4005801400c6050500810030000400c00303406031050b0f4100350001400c104030500c10030845401004490130148000c50601010190150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15731238 1250 15729988 15729991
    0x41a090a090501060e01060c03080108010b0a140f0d0303020903011401150302030c0f0c070e010512060f0601020f060f040b13030509060313120c030e27040503040302090103030c03030c0305090303 86
    0x1000303589403100d45040c4603094110f280108481e00c4401e00c2580c1d40c010041a1166020080340000c160f1000011182da0501440424500c01001c850200e0b181c45840440c424109059607007040c00010845115603c4442701c00d4240c0c0207443c050307038a61001041608440700192400c07210594800140001070700a00302240c51445420016a40e48950f00404000e000c0c02e40710300302003440042d4000642101194150441c0d1200b0402c05a690700c42c01001020032540d12241c0047d4080000a42400c000000981d001901030040c3e460103140c840e0754074140f08044904140d450260010b02080051494105502500c1e01c56220340c0314802d640c00604a2055410041c41400040b000c00c0348107580a00320003541358840d0800c1e00780c0e02000405400b0580105d8140c2c00314400580208031410b024080703d101644610500745059214040703680350200250003991244001c1c00b0200068a441d0149806540a5290721007484460300d40141035841d00d1704a801058201020300001000000680303 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15732488 1250 15731238 15731251
    0x30a05030f031e0907030516150f0e19080d05071a0c131401030b03030a0219080702030d0503091002090901060806130203190605030105010308070b1305030315041a09 73
    0x1d030742e926860400c480070b030b142110007020400c103d001d028281c000000e00d00101c900c2402501d00c1d021a06e10388061503100b42c80381262042c01082000ea10728880c90b06248a1646810b041d0785800005000c101c01883c640d07241130708c80c403122000340700100041100e020070a24502d44036280080e85e0703a0780c030f500c0303482092101c190f100d181c00418180d41c0c510081c0c40386910a43c90889036199180c00070408590072985030340c080b038503000c044d022600f800f2007140e850860030b80007804500302040c401000300c1c0c05040c6c00d448042081c4103010050340c080c810021207041981c0c0d403a8407801c0040e9218101070110103440b00c1d40384100510442c940700d84541c0e80c11034250342031468160381e603180401c011a044052907013030284000704100d2203154003145205541c6036200b042112580315000e05089803000c0c080580070310400c0c0188400205008415a4862507030025140780c43c00300d944003459500300b500c40469010720544650401e040501ca003001600c2070340ca130b00641c8465000030582e83c90018102 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15733738 1250 15732488 15732517
    0x201030b0d0809090c0c06070806120a241e270209041101031401030303060f050102060411090702070902070308040204050c09010e0405130515010515030705090607060b041409010b030a0503 83
    0x15800e051704205030344181c8000c50070346200d880c10b094010a110170407a0010700c2210b01000f40001e00382c0000b40000110b42c000c5122000b13051840701c41c42078070030507001d0a00f0191541e030700340c0380284011880c034409642d00300c020440300c1042d0740884104510306c00d080ea08103007440704a00907913500320100d90419040170b100480c400c29140103d0240401813202003030155064000801c16034168840021180480b840e000d9180d1500012a1640c0f010348029000080d201924106490402c18440d00164a401251041c03036451070440181e8006042c168040b0340080100002d6003040c1c0980d0b5840484001480d240007070040c006012141c008194034016075440d800101c05140760750440c11080d400501303d07111804041e03860619007809001c0e550041c058201c40006210b000d40950380251401e440b90f80c1455840810701c940c1e60460401642e4483d00c0f685941c800380c682e4400e444a41b11076991940c89c500e445101c0b142920400c2c44664001d0f80321030780b030340049040441900c8084503620750 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15734988 1250 15733738 15733741
    0xf0906070c090509070501020f0f031801020a050708070602010b060702030d030506040b0d080d0b0a05010f0503060112020408010510150207090f090b010b071a010303050304060f11040b04030201030b0d080909 91
    0x30202040222a00b0030481185032109000c1d0182e400108441114401d81c01c03500c41410700e11130141c4594105140c401c49501c1030140210040c9019841c2981c803070184101c07041a04a41c98040c0b070b10b28140e020907490b401888040c0980f90742030081480404094a41c0c501d000c400c0ea01080d543c0e04040c03281010195910041015562640c01928100030010444e01c3c20343e0145c107112407150300030180480018541070b205440d03030070000112800c0310310584401940f111041801e4501c0c0d0b000030b0809040106042c0a26481801c078405840a4010040000750f64601000d4084455001c0e420104c0e400030312000c034801c010f90002e900021b9400d5001d02042c5410159840b401415001030000c080303110450000c1000200340000d0103240b07000d070700103030b204d4651186011540c1400303000217070000303408000180100b0b800f078100c000140d21850f0002420703064842c030102d007600a6085028442c03400141007040d0b69041c0110543d02c0c80884d40c00361540c50655803074483c1e01c68540c126025201280 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15736238 1250 15734988 15734993
    0x8070f0501052d0a031406091308070807120f0e03010e060c0a0905060f0901140903190305070501050c13090501050916020f060f0f09010905100e010b03150403140f090607 75
    0x74562114124095411380c07111910880074010740000b042405114007032000280d81480c1000c480350240404844100c900189500c641d800c5030701c810010f0b643c1070b1080050800107100c4251000344108165225200240318513401001d0003c03000ca2203100b0380c105604400d031b215020a5113501720744d05030310403940c90100180554610b01c0540c040e83c1c1c00703003003c504c421070f80c9031071001408240002d0fa1522050000b40382d45100306d0003103010f4507406078856100d080c00140240701040c0300c20b000741081c508041c0b0700d40d505402d446040f1480340c40641c01250003e160300104085c003000e0040d0075070a1005605102c00700381d02007402441c0540140c40c111002901c0346c0280078140001c1900001d41384289090101c040132140251040ca030600540c1b4002207883c001840751140e100e50010242c44544004000c41c40603003480600c400e00c556039003207246540e0340d00300720119000c0d80d1481c0b403440341c1c5070504004d003d207294010041c0c0c500c4000c010112824100c04200c4802c0001181ea0580b41c03081030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15737488 1250 15736238 15736297
    0x3070504020f0306010e03340905090703050c010f14030a020f0408010204050a06030605060702040e031908040203060703060602060a020c0c0402030414011b0e0d05010209030604030908070f050105 86
    0x65014540240c40011000310081e505001948213a80a0701c4810500e200d00060641d40e103102d42801e01488070905001710200d0621503c8401c0b266441e5108610a84400c41e00302211005e890503229640861002c104120b028403500f00c2d61202421b00d00e03111070010f00060540c01880070004071865002001030002285541a20300000800c1001c070740b0f42c1e403504402c42c001d6203d030140c3c41c403814001d080000c0013131190180e00141d50001c4c000d1810f0003920360902c005800500c00004141c0024000c0300d000f0401001c20b01d1040b40c441d92000c00c603041c14010b00d4140680038016004050624000f480104d030001000b41c3c1181820a0042e036800b148204542000741c1c08080e541c0c01400002880300b8848030950004c000200d41000f007000b00c9034020011a150164001900890489040c13442c0510740041c04c003c4050003040090701e41111540000e040c0308088408801081003003000f0f11030410100044400ba200e400c00076021182800006800c90003210404000b2541039a00e5111a4403003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15738738 1250 15737488 15737503
    0xf03020d0503070f0b01030b09160b0a090306050c090f0a0501050313060207020d0c030201020d020c0a0501030213080106120b01060302040308070b06011e031d0303130b040305070b040501050f0105040506090703050603 95
    0x4034988411600170328001c0c0340c1c01821311090320f404400c903010406000000c42c5074184018918001c941030f52602c01c25658941003400c003032081c0607003001d0000224443c1c1c01450702c15203070204010b664004041c100030f121255a00454001c040d040340600c400e0341c120080700e8010000c4c520481011078180b401d41302a120300380c4001d40040386186410104211510840103982c800d8003510284840389008a039600c0c2500e211503400a10442c0401c0554000c1d4001c1000e11014400074140c11345402c0054203440c05a44031500440e2421040f409002000c58040c0c0900000d01d030035841c0c1483d644a4a41d1400345810191035050583d001c2070351680500003102c84c49500300b1014031001035280018000742014541a10004414020011548030103c2128440c10385a00e54030a89001a1112409000002c10440a000d0200250004903212110013031156110394004030f8246443c615140d114041a0b21090103a070604040c00440e0780c0b10300d900ba42c4001c8500d000205565607100283c0341c84003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15739988 1250 15738738 15738743
    0x30b06070609050706080702010209030604110109170303070e03030301030f06050604020d1803020d020f03030a0c0e03071401020c0402160f02040204090212060f030303040f030f200a0b01060503010f03020d050307 93
    0x703000a2201007000c04584003041761542d40742c81d240ca90320144140d01703034841c2010341903054000364000760008000c0302100c41201c406251401203103456805000103c2d00b101c0c0b0341c0700c5950001c1308200307250303078400040ea14082c0300341c01131030540d49190717610031031001c52050061003181c0319400149252226030555403007440d004000e2195400c40781d2a00c0131401c805805a006000d480d80768840070f800007a490b4004500c3c20000c51442d65507102210003041070100e00d200304000b420003605c0700e0340c0410001c2c0c003400410361040038400702c0b040060321300030450000c0380c0624014040301d691640c07020807110550b6002012601e1a666a00c0041c00074440c80e0841c0d204184041112008110500c060030b1144c00c0644160704800e4141040603601c0c0000c560007005140d0300415640000e1051541100b03080321418a10002103003628070986c00581d0581120b410790100c800c0c4018003003082c004078018030150030003510719410202d26520144203404040d01800300e01d40d0800400c801001200c80d09034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15741238 1250 15739988 15739991
    0x8120702040906110d060b1813060503010617010507021603020120010501090603150204050f0118030c0308181906030e030d0626010b01120b010c0b04050102030a0617030307030b060706 81
    0x3013031100c0c11455001121440704141c070300300740800c031a07080104032040e1100d40b0720740c00c40344040c090401c400076002c0c1c25805042500c9a50014561b1024000c001c0641610160601000f0382c1017006801c680006040c2011540030581c914050080540c0e444180d0340c080c03808840580a0100c01800c0300d026200c400107a600e800000945440503600c2102a40d11075044061040002c6844400b039004a0048030342c828008054180b0359030259501e00310350201c41038880c4803607503030340ca808080e0701c0300d64030988011100050b10300c1000c0980e14100399101084604c500102d24640080104404500483e410715942c4d0103a00c11034401002542c02c1e0b001c10315010b01040f6280c4032120040100c4018100740c580000f54405800032040c01188c2c400030044e0b4a084c1c1288152100c28040c0000f0b49100d030501c4640450500460b0289003103a00c110702800000d82c0d00e0804891080c01c80d040d583c48250300789102d00a02d0000c0e01d01108480e040030712484c002c10300c0074910001500d507201d008170060206 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15742488 1250 15741238 15741251
    0x20906010c022403072601061b0501090303020a0912050705040e0102040905090d11030a1704060e0d020a02090c07050703140f0307060507080f06030c01080405030912011a030708120702040906 84
    0xf414030034021340c82601c0c50340da181c8091107074030301c0004207490101090454107501e400510070071788074401b10600d909a01001000708a600d440d560b085a10388041500000d800107855001580c02c09001d10040c140e44001154114140d140c071b0b500d544403030088034405c5031914803624001400350103440240c0300c41282001681880e40b00b40340e41c0c150310596107005c0b500c20708055960500100c00c0e00e6100d113190f111203d100406511941c8035540040040750041e40d141d080c900c40d60000c0029041e00300443c1c0091554009a00400640c070304000c150b41d00c0310404108100003e1400f141d8182108e5210104564103801c85480f9400c265222103840c01e035210118020050003d03580049010f55002d8175508010340700c1c004a0400c8070412246290903501035941a40b00c1d5106070b094550050040c03045c2da0034540c48400065080c0b04007070484805a445212420b508000c42c2c106003940e5000320000e0941503d071031607941cac80b410b01c00281400c4441c0890084195103440c0c2180c0d415907031208041000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15743738 1250 15742488 15742549
    0x20408010e070e010608010609120c2313180305070c050603040b07030b030a02010e0f0a050a0f080c1f0c0305040504060303050406020d170a0906020403060203010e0403080a0207020906010c02 84
    0x880042d0310400314049414000090240e0040711554162003042d9104082d2a0030495000003a400303004046940412004001441484001c9600c4125840841010148040104000f90802d083c07140030061403500d04038801510072186421015941820f1954a490050404550702d02c04c5512480d0040d0b800020841080302e640f002c544200c1c00d0380c600700302600c43d40d002e250f81e0300c0060800901084038007012240e6441c040c82e20b00c05008006007007600407600c0d5404240e09003000c3d4490701b4002520b280070300c00c0c0d10061061503e08502503c0080701000c06101c040281c4401503c03881c00c1c0300c0300901c0c0100741442402200e016010180092148030703640d1500804a50007440398800502074200d80c50700c1d03903105071890070400502880c08901ea455400c054001000f0014040b2107a580c00c00c030000000c4ca050026500800100790000791920306410060b006680007031100003028410449640146d58001009402c00d00c2031800710b08400c040e20108081f48580030701c010080c2c100306ca01041 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15744988 1250 15743738 15743743
    0x30201090b011e06050309030d09060f0b0301021201050d053309030712030e03091e030c06040f0605031509040506041104020c030301050f0d1a060f100c0f06020408010e 74
    0x6001d2190910301c11a03a40e0381000c1ca2005044455841c030450310110401c065449034000e5a000703180801030b245446028a900300440380303202c0007122142d468651a0000d00e03400e00c1654000c01040d03000303611303118480d10390300b11900b414054284034007001c5180b0400d00c10204046920310304040660661441a006010b13142411144140c400792588800108861404402d0b6512194403180300c20680381000340640162401d0768000020b0701c001d1002c05c4042d614200400d40c0610440540b041c0400b24005250a00c0c204054150280781c04200c10403041403490380181c01c9516603c0e2007522920384980c80c0c00804989209198010f00318403c0c0000e10002003840c9008600c036242099000002c44144401c0c0d01402c5151070380e640084c801000300303040040880001c404020b00c450507482250ba00c10320891004801107002c60b88034010001c507401c003900f0810009108881c00400c2180907200184013440b94100105070007900c1c3d40c40030030858190141c801510008000b40178440786100b2455 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15746238 1250 15744988 15745001
    0x60c03060906010504060e0f040b03030a03090605090a030507060b0402161a07181205070503070305030a0f031103011211061605010b100806091f09022206020c010e03010605030307030201 82
    0x501c0790880d403001c070b0001d40c0030b40115411101a900e442c07901c03100361030404c064510b40c0140141c00c5500d404d924942e0396802e00c01007403080141e40300041e01e110795040000071500c008000d030401d0b511603041100801c0e04001034031600b80c0d00c980c0c0850f0801103040070034040c0c06002c01a45000e920100d24008016001d40041c0f14070503089286034142d46e4051045079a051030100352a00710602c024184600d010300305400740e101c5d00410489203040da444012918201ca60f5000751084e40001c2402c4c030307020b64401104005014686002e00c4001441d8604250510043c4500d101110050752107004000b0b682c002460860401003107a501c0343c180102d01d001d138800a01048945510b05959030046182246442d21f00c0c44441d5100300d2540d0b01c00c000d00403981c4016218900c6c1c2c0c1c481e03034440b02401c52800c0000029110202000d41c40781c0c5600c4610f1880c002441c49e540000c2482d540501c9003903400580d6041070300003440c04640e901c0103080400d00400181c2c01154040c04001040014140c0542020703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15747488 1250 15746238 15746251
    0x18061a0901080a0504030504120c03120206040c0b0307021b0f04060303020303060a06080405061303120c0c1208090c040b060c010509070501090b040b040618050d030807020708010b01080a020c01020c060c03 90
    0x456a070340d50310080840d00f0480d0010f000c01d0b0305002c28092700d0301c034848202d503042c4128100383d406170b101e4648004000c0346182080059100740c08102c10400c103806080c00a005400d8000d055041c0174902135114520560b06e03050310b06000c01060070030b582e00303050156810360280007006480c0c2c8a0400039101e91040703900c14022024007034001103e43c070590b1024841c1e90080054441d80d01c1d058040110501d19520035030400c22640e81c2d006140e005072060010078400b9844280d4410940c0c6002500380549000d01d0050004403810800c01c0d10001c01c002002d02c004650000d00d01010350002000b60042d01100b080035840c0c141000329051001820005450090307d800c059540d550302e01000c1c07032080307001f0b0000d03051060104114060080c0d9882ea58081040b003804205070319074020a851405007101900001d0100c003d1013415a01840110b0203080a04028081d0800540c000b0b0810707078002e81402241540018101b003e02408e5041d01e54051a0100f903810506190508011903007042e2a103 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15748738 1250 15747488 15747497
    0x17030a1b0309030206070e0a03150b120d030501050108060d0204052206020d0608160e060d0609030507020405060402040812090604090c050a02010b06040302011407060b060a18120c18061a0901 84
    0x2c0750702140200a00c100c4044000c0c601b403401400c40cad0728500084088a200050070744c0b01c021802c015038880c0685404203000c0c4000341040c41c82c4500082c241c88041e400305043c014400184280c9490b0448408241c035015034011070152290071454461903e174118405e120510300c0c440000f00002034000306040c074440d000c10702800362114102a101c084013111444018200b40b000c0001d0300d100200300360b200070300400c51484000c25454440941c0ca40c100202e001840014650086140512880c0d4009070103031000c41c1444e040041180c2ea8045840c4810f041030401315455950350788010407a40503160000050040d51003c50000d025904078000e010055420000d22101606261007030710100d81d0140d6078081c3c1d0380300c1020b8101d40c0303030f000040c140c4859481344030a0400742c4aa40050150007801d940d500711070011002018251003d58124140090000d5212170116008240344804da80b01021910304007803582a1200040100da4440e586221084080d1181c03881508042d0505900030388070b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15749988 1250 15748738 15748741
    0x9030c060906190513030c15080105030c04090f021305090709140a0b0105120907090b09060607020909070906150917060c0a020705090f010807060203030417030a1b0309030206 77
    0xc00c030003405040502a0808814418031024880001004041c0b6215050580c6401c0340e0390060301d1101001d0300203941d0b02840f5081008000b41d0079400c2c42e1170b0071035031600c0c60b280c0d410040040d460740010302c0014822070311912a0014400c882048107406903000b0320400942d2814017220004e0003080340c2104860082e92000901c400040c0501d1035500c4840144d842075070384040d030305c000504181507031504003c010310103050440f140e450128003c10300c3d80000c1003102e180c21a50310a940c64090918041c0f140c01040c083c603a00c9240c15601e00c940c1c112180441c6554914040e46000b41c580d125120684c06d001e00000c1c04191940320003003031002c40e40c1e000c591a8841c01001c0c8e0f01d910100340310310b0711350000c40040c0104d440b00c0054600c004072441035a07103096460340014030704030381505d41c21258600c1e00300401111348100022130040a050024504515103602d44070303080e0b90f0000b21004401000400501510707800d500190981c4d120940d00ca411060036030000700101880c3c041207000d4400d110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15751238 1250 15749988 15750013
    0x30b070305011e05042007060501141c02100e0303031005040510080a0b04020102030c011a03100e0607120906050c071103010b06040506070c0f120507051005040902070c0e07050903 79
    0x2c07400c000c11540f800500200f186490b0a100080c40100b01c1c11207550340c0c48a0960610031260014404580114030215a95041c40340c0c0b030448010400c11144140498060203550260502c09110920f030112521411510250b5054680c3c0b401103080343ea140c0000001c002c80b9400440d80c01c030594200b554200403940d903409da0b840b610740182c02042060703800401c2a00c00a50301594040c2e1061044c410b41c0d00301101841d440382900c90101d502000307003010b018a40183c0c01c0401141c6000310140500340b001c8401c4460054941e5000341c00e42082110440c06000302d81349907045442c0007070740198104418a007000c8407401542002408075907031381c90b84082d0703a803a10701401501e950304401843e0603e40f501d010300f001240ea020160844030803103c0c1c0400280001d1400c132620080124868181d40901507290803800c02c1c04541100f03100780148806590030b075902c602981c0c2a54002000181c0d034021904204c543c8010340d40c00144600001c104110200394050301900e200001070702151920080750 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15752488 1250 15751238 15751259
    0x10f060e0f040b04090501061511032107020106080303040606050103140105010807110f060f0f09011a040207020d05070f0906080105010e040602031008060a0203040b07020a052e0204030b07030501 86
    0x3019a00079120844034440746020b501490640900800c000b405072403a0362000d00796860b44e03106640140c160450040015000401410020300e044040c40c41d211948044030040014044480320403c65140010700c154000d601580207003d18100701ca860346410320340480a440305020b001e0010341018006090192030030801410b9940c16181d401060f691030340d0480e140d810407068000d0611619030300030b211200900c00c7c24054a00030404504524098003204944100900034032001c2e0b150011466400601d2048118504411180961b8490f40c0307000081c01050600c001134001d000b482130000c0c06a0207420500111f0f02d810a0600545640b401018203c9800344240c500701004c0030300190004206074000c55100c0c10361142c1c251500d481e500c42c5450100b08680e8904440e82c008240024003d8400201b0f5004081d48004c2110900c140c1d1015158001c124222400c0c100d4010120240c500d00b0760108034200803000b00310348460f500d040000d0340c000103a500a01003032a2070008185040314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15753738 1250 15752488 15752507
    0x30a0605030a05060601030f060f0b0702040506010504032a09020c01050a0e0f1b0d0b0106030c17090309010f0905030a030c060c0e0a1a0d020304030f0e0609010f11030702030a0b010f06 81
    0x20901400441e0f441170015000ba0540c802a507030140d640c0c030310103d02c04048034403620180c00004480350b25106203104dc0401c40750090002418840123110800004100d907410340b0300c0882d9451250800c0d400c1c3c00070282d481c50550080c010550000ca103003c1c415030158801885884a00700900107419520650740e110f041c022010651034100360005070f200c107401c852a4a03003010103405803a07074007580c1d01c41603090b20b02a004100041e40b02d201c100d20060b841030b00b41d150004841400c49480c100102c0301e55403482030308204ca0600031160b000c4411a0b00600d01c000003040c01805035404802d003840c00510700076020704226a420b103415642c5403d584150b5481200c128040c0c916101e590500508a4070300030500881c18441d0010410000040000e00146004e140300b511400042030724038101800313131010b1414050095009019454050780c1c4484440c081280c1420f060178001c15442209066126040011303405114584140307080004001c0181e0407a546024000581d54503200121110f505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15754988 1250 15753738 15753743
    0x30c0203040b03190c0206040314120106120608070803040503100b010801050114190c051507080a0f06080d02030c060106030e0a0206090316090f0e060c1207050708030408030a0605030a 81
    0x820301c0184112000180290341051100b2102514003014020309800d4441640079400140c00590501080540111100d242c0c0b0008600d010308041e4284400421580c05205140c20000518240038000c41260700120251450106940009840e802d02d07683d203501511070103000313105038441e0080c0400f01e40310b10001071105a41d10b00459180c02c0044a07910b04403518a440d0078810840a01a40304110a010b05682c41c0d840f4004811007a0601c81d0404800e0240c55604a2860003003008250380131080b030394072100703502e40013030b000001c2080b00700208901d402c688501c0c841c02010a10054002019103045000c01e02141c20aa80f52941201034602202030482c1c1d60b801800c0c603d005190640140851820180485242c5031541c0d50b2441c1110729913210002c03440d961810700000056030700a24410030812001801e0305d0400300420141031290320300802c699881000401e10f00c40c414802c895140e80c110705400c0d100e04103800c2000c0998030648461034541c0c60103100086500b0041303415000c80d43c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15756238 1250 15754988 15754993
    0x90f040608060705070221010501050a0e040312020c0102070503070813060f0203040306020703030b060a030b01020c060403030930110315040f110a09020d02040306060905011802071a040f0201020d030c02 89
    0x202d403143c0030798054206803012a4400340406410b100444240c04803442c40030950004a050351401040c0701c01c00c2440e400c85032220301140708000100c0c0d04941e0b0f07510b42008070900107940d8012405028024090340724020902d00001507602c00b40111840a4150700d4880408041d1007a901c920968103039011950074400b582003070108001041d000e42c042c120840c01b0f8240401d80d281614000340650740501c0019010a5584040d1045540c5c10440c00d0104041581d07103a1a00e8115100a8840c250390b21a1700003c1b524034620030040d01440a2103180300e85140c1100d8904070b17903844d20080d1220095642c2c0d00a10601c00d0403070307003041c0c2c2c00704040c040c135000b100c0401400020b4544051160304c4401540c0c018101c00c40001e1440014030092202a040000040c0c88606501c2d0282c1a198540c1c807201a6600b8000140622984030a5404100d690312000587d20003039494002ca0241c0d01e240091102d41000c0708100c2448880010b400e49240300342d0035100710248070307030060701244c082c0c40c5c1100069 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15757488 1250 15756238 15756241
    0x180b030906010e0a0906110c15010b1c06050405010608010311060a080c03060102210d0e030a021e07050a0906061704050d110c04020307030219090302090402041a030d0203090f04060806 81
    0x507400f55006500090554404124070381140c480d2003c0c0c03507403034400346000720000030000005074040c000d000c61900b6440e40c80089514007100c2102d41d0003010340301e06074500c8100e03e01c0201802580024001c00b8040c105015035030351b0380d41c040d156802c00d200a841c442c11401003103e90340340c00c1d400c0700c80c02e4899807660380031034039100007401e07880d0801040d00307044d031040c804010140c08a10450310440c0858004d4142d490b007103410b1f00c40996880f100f6440d080d600038010402401c3d00414410301c40ca000300c620700ca0701c060f18035a5614201003944201d030006920280825000520b0b00144240e46280d2620f07509000412017804039008221800341c2207401066400f449144904082e111400303e02048650f800c01c80d800040881c2c7c025210800803c0d80001d421003484000400082407045030b00b007000035989580c010030215040180020b10440c5c2e40c0e20700701c0d180e560402407030f00c003818003504980c9c0005001c103010b0b603681e201070003891103a48402124103162030980140005d035941c600140019 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15758738 1250 15757488 15757499
    0x3042a06050c0a0b010b18030a050601050103020c030d0603050a0308010b0a140c1f05090c030601030f060b060f1b070504020403020607060e1e0d08070c0b0f04030905060703180b03090601 82
    0x1a00300b24a2900140100c1c2c0449010850710700c0914041c007180c101c41d596030102e0400c4100500e84000c40b1a01a80200000501042001c034400b03045440a00300541d0f281ca03503c9000d030a42c4249200c10841c580b0f0504048140100040e5560b541840b035181c00141d41d032507405140b00c500070b03646100000f80305401c00c0a107544102c07001d414031185400440d108840407401d07243d5943c01c1450038281c100c1c1d441c0204201400200203000366070300f0a40c05408154115200d5a0f40301440f501d01400c11601c03407420102503124101115468801401c41035240c034101c024947c0c0c503840c000711604d4107104000303020031585041d1003180d00700ca030f00920342494416282d0f1124040c05115804504a01502e0b58060f2040d07044034881d00c03a07510b408081c04503100c90031000390000c1e201130803420400c50310040d030740300150b00c00040c076030001501100702103a9615458115168401c0e5017095030041c0c80414030360101a0419290808041d1500241c40041c0d241c0c040303160103000842300e0900940c40007004210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15759988 1250 15758738 15758747
    0x1080a03030c030e12090a05010e0102120901020c10080a060501020c030705011d0603010b03010f0b0f16020312180a0506070519110402070b0a0f05060a1a040f080303042a06 76
    0x120082d400c000c00c08031445107000742031000d00c40600a07001d40c00120300750f1600d440607a00e8007a0609003045020303031196000003560764a1340c0e96a2201c540d000948103031103a00800c40e503805400010070705001c403038007240020140c901c282e900c1c0d1a1075003412400b040f03541c000b08103c0280e420240060481c5858400112644680c03100c4000c03070040c81b48140242921030200070340c0038001c044e4015a4951400580622010055008050103007050010200c2600c600040342c01818100b401010107004c43d00009003080c00b01020f0a082c0310000400f400800c05401071101070190845034000802d42e81c0052107000c3c400c80000400307075000341d503503440c44800f540400310032540114401b0032440741c0880414102e03841034909441440c0300e40c08000000181c5d0041050400c40703040c0c01e204a051080100d40039420b64042c0341201c1a241c130342002418030300e80503030340241040c60b59903441d41c1d81e802d40281c03681e20669041d507980c058804014031801c03026142d8032040080c200b0f405c01062a10b1001c0305e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15761238 1250 15759988 15760001
    0x901050c16060b06070501020c1002070c0302060304060216030201050a0b0109030c090507020304150903060b0d021f050d050f0106080f070212090109031202011a04060501020c04090c050312030103020102010f0501080a0303 97
    0x2250155180008906910b42c0c9005e031005c0c43c82240010303914000070080901d0141c109210514050041040400003940a8030000440341c0c1a80c10320b407030f91914980007001c0c1c040c02244000141d0802803440915a0542102c0c0c0554103903101000b040000380d00465011282d80000fa2000103603079001c0100c0c00b0309509c6113a019440f03105490400d0380b504050400045088000f03000100625018000d000407441b0390036030084125008078903840260301190104402e2803610102d4980462010010f900620846990a00c801000c0000389845c00d4814102e680a0186030001202d0000203003102c00c02e104010f000e804d07640c005240510300102200110380c82460310310304108150130000000350301030181c00050801600085140303644241c0415080003c010090705c15418014200001d980225a0300500030742654041045021030401e40b80d0303640d032540100c0e0503208021030504290345c108041e50592f4400d034024072490100030b000400390780c1e0a001c0c0c500e2a0304070b0054200000d00036807012 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15762488 1250 15761238 15761243
    0x1503030806060c070302030703061506030c0c02102001050f060603070503011202030703021002030c0d0504060c02010825051b0c0f100207230f0d0b0601050705010b04020409020904050901050c16 85
    0x940f013031612940400c0c2014201e51007195400d4031340d101c42c610b8403030002c1000060501450b04004000b441c0e84001c005014107540603000740c403100c04504003613208814034074064401d14045d115003480280c2c0e079070003000d0072204108420780c0c1d01d0114620b071426004590141e0143e59400d410b44c0d081c0240e01941c076852400490340742c41900c00010058031011256400804584c01654031a0b807803213011424a00009140b01c02c0100c2003100f4010590440c00d01c0e00100c2c2c0a103400d0b01580d032001000d00114000184011003008000310b501c0c65194018000d0451b420b211054030305090700200d0855481800c0c080007680207400c8100c0c40c4103802d05605007441182e140c812100c13a40c5d9030300107464002650076400782d021407502810200c1818031310610f8054480130755045109407020340b80c400c0c03c888094012130411070002400c0062260075007004029450081c021036a0356030f03e494600c000e42c40b00d03081d20b00503402d200000303441c07000603c500740c0b08121180101d803414946042114410240c000b04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15763738 1250 15762488 15762493
    0x2060f0403052710030c0206071107090b060c01020f0703020706050405090f0601020c0a0807050339030f100f050105030303070c0303020a1101060e010302041d07090207030e060d0b041503030806060c 87
    0x7000860360b80c0300852882d104c0315450018001c105110000c1c104400100a601805000d02d0103c070b5203100001c1e0701c01110120100003400e50060740008115106400005003250700100d83c00b10400051402011000c1c40382c1c003160012a6103881c00d40f481d00452051551200c490340001c6d0290b490006070075840041441034801e042080c0340098110901904585000c0d44041030038065800c040114804000341d60329001403004d01e030358185104601c820702030003030095007000d403003c0f40d00c041001214800b0b9141c19515410840250b4200401e0710a00d08417503079050100006980c240841200c0c010417a507035880720b03003280e140c80c242c1c00b0b503011164107020003000c1c1301441ca04070020311a20780544100e29a0034400d515500411064440030680083c00d402c0e503c1941c1d616203400a44502150012040982c55803000c0c01c1c180c0c2c0341c10002c0141d6800184c009850080068154440000c0300c108030380400c20744240f180c03842c42c03045031404000c012514100204006140400c003a04002a00c1c108 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15764988 1250 15763738 15763807
    0x50c0603070909140a060605070503071101020a050a1202010b040608060a0507090f180c050a1b210f1707020c091009230f0606030105010c051002040f0602060f040305 73
    0x403290451301540507003038004e2818030500c0980010390051500030070080c901181403503a282c640c1900c07403040d000000d11950000d01c076103010341d0080c404821460b03044001d66464100c5070401080788207800c030700b44005502e4060112064600781c400c82003a1a1010010401969844104001828043c0c1268140a149000002c0041003110920b02400468102c159070382c10141c7d071501600c04041441c41840014402d10310351030b5105625107014001c030103c1404090050034901d10051002c031507544502040c8415021b2503030801400040d40c1d03425910a510341c40000e0007208800070664604005030401e444801c20742c9001d681941d00a42034003010003144e55200380000445020004401c410029200c2000078811801c207807030381c412190700704641036240c65000594188414040c00d0f05203c107200b40d8405000040110060040f000d400440d43c407034035a80d410200f0101c901c212401403050070001103600d40d800fa90240520340c1034890900340200000d40030a400d480c120398102c0d0180c6100c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15766238 1250 15764988 15764999
    0x90204020f0408060a0603260f04030606030b09010501030507050d02061309060512010507050306010302030a0b0d05060603010f0204050306070e010c05010213051e09060f030a0b1009050601080103050c06030709 92
    0x20007010444a01079040b036803203241100365400c00a001380702c01000703894070004101041c01c030080601c80c40401ca10000d02c0114845e07003813009010304000405817481c013260100800850ba4460003d0f24001c8400004581d9000c0700076090350403d02004156800080c010450b60030203c0c0d10a209510050419060441484d020f0a181240754403c1c0e42068581c10104040d06204c0d500c1941a0201c10080c844e9240c500d0010300b080c0700c040e250904265000001916500c0c09070711100840100505001990000341001a07039400e09840c900e1180d448d01040e1000002c03144221400c440d0054003a01081c0d0b181d01040d41d9942d030700030f03010381070040c2c5060b1800069020320040c2009080c080b0070105490416082c82112400060314112601c0a0712100c0c18035034910803465480001102c101409146000100e410441d03d884002c001c20000414040b548001c034080c0e03c142c801e10b1104104640e00d9500441f4806804c0c8800341c4a600000309002280c1019401140d10070b21505082c0007003503540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15767488 1250 15766238 15766241
    0x203070f0e060f030f010f060908060714040b0a09050102060a0b090615040e090a030f030e1f0e030c06040b09011b03020703140403080a0905011814030106080604080d0b0603010f0603020c01090204 86
    0x48443c6110f004445c001448100b1025140d000900386900e4012840d508103052160750f00d001030541414068451103046460650b107003220060401c0c2a191900e400202c0d034050000720340c601581c1d016010b5800046c80c441154441c1360f601342001800c100c0191900e0003809000034940492201c034010410000c2441d051062580e4002c0911800030b0110005a050003000c83c1c11480101c010582000c00743d0302043c900141d00c00c0b0000c02e00e0491600307040342e200e01000030505007449203000d01000c10000515600070810310b11681c004c1c0003103d219626010803508a50b0000c150019003c004181801c80d14800d07800362040c544241001c20103060074141c00c0009400c146c3c0100c1d000074000821403161680320800c8001000300303084c5504000c1c5810a90400c10425000f8000452441d921072407250341e09410200041001d902658181c0c01e180c18003242e01d5000340c904e0305800d400e1075248100b50a0481c00c8030f0407a140c8801e8528090704000c1c1c11030117540215444082e5648800c8001c000d40e486 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15768738 1250 15767488 15767491
    0xb030f01020307020a150203040b0105010f0210051e0f01080a031b0203010501030b07180e010902071a0c0405100c050c010c14120a030c020a080d0203100306090c090f0203070f0e060f03 81
    0x3140c0092102d40642d1802d95102e1b1044900e220b00c141c01801800005035400700c2c501c3c155903003403e00448004c03c02c43c0807460500040c481d07560650801003402201020700714a07040140384401686640e64607107150102c200c100b8450100e15038030603000400070a03c900710100f00c042c1c0e450080b2203181e40c00d400090030744000303800583e41c20001c0818402e140b504244028040d000c0c54440100c0d4078940920304100c0f45051090743c2e4100d800290500400c43c8460209052201c5203070b4690031810700c3c200701400b540060007554062800c6081509180b03000c1c00c0c806075841d42c000e004040300c0030031200455400d002010106d48240d04040c2c1c8485a071000c2c0300705024035244e03084107a1a40382c4102d004003561a080c0919040d5002180080046000c071000c40e1100844514007603a292641420300086d07240c151f10117002e03180780c41c43c0401040300e02c161880840f2280d07007040c0004100940c0200c01c9100955180d808110408982043c083c0154840308120b90003c00030350503c00648044030301c9900 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15769988 1250 15768738 15768751
    0x402031b210f04020a14010201140f0402180103080a1209050a0501050a050106091d15090709231c050709020703020309100903080f030a0f1d25090b030f010203 70
    0x81e107010410110442200d58000c100d008000300342c0c00c041d000f040780c4404a001d0b034101540c2c0901c1484184c0d000b500f091b102101192280c01c02850010301c8042700b00002c3d9012441503a03440e0310640003681ca00c6455060300c1c0c0000c543c0e460542d02110030380f605401c2c20503000380c554035403407a40080750043c0401d038070050041d0300100e11352071710561010071964160000424808880c4050101c3c608044a036120654542a09016610390074460fa04034400d140d1541d83c0f010808041206166224190000b00d6241c40c000a20340e9038800c004c007526840c100381040c1c2050a1409100802c1908805214030342d0092040d124510b03210f20038130090b40e100c040c040d000350b400090f41c1c035400d01b807811400071000c2c09807811615050542c0d50f800c80d00c2c420307564014810000400420901c3d50958008243c82482c0c8900300301030200040c400c10720022810081510340a540310319812070300800303541c2040001c02c54560660908000b4021f0082c840000d03002c0c0c152146045040c408a0b00348000d600801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15771238 1250 15769988 15770017
    0x210021303021203070b0108030307020a080f1902030706110f03040609020d020303030c1309020304020303030601050d1812020d030b1302070606030b04060506030f0d0e0d14010f05100801020405060403020402031b 93
    0x1c09051406d5060410b81c00100e003680708004015407942d000c40c082a11503400540c0c140d03603420b4075084060602860451031045a41c010900b071145800000410b44944284814088011501c101110b103020f1100018031015042000030006a441c1e841081103070720041c441700700041e00b074001c42c4c80c0d0f800880340171b10510b000203401b4500700031034a501c400604c0c10035000d51440c0341660200c0d4483c0006024a07061241c0420102041d00181e0481c280301381c45d54070702d01d110604c20b0805054080b145240c141c050702580b40c485180701c1c8a805801d0031b070500581315409001c20251071340c1c000d5210b4070094419941d5400088000740e15452514000e82c0a070001190301c0c1081c03403c01d8102104078840f00f1856000e08007502005420001404004404807100c042c0ba450700c1c10700c10b400801c0710121600355440e042820346120381c141e201e2801001f4044451201d140c440214030700300d200b0b5000da40d501c0407042c0300400c018901074004540c0950960320081100b40010707042015a00321852503900034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15772488 1250 15771238 15771247
    0x1202030301062010020309070806090105161d060307030608030c010606030c090f030206092106041101090308030a1802060403030201020d1109090a1a1e030c01030c0210021303021203 80
    0x1a50300030f400c101400300c40030800710403d0440444942c0c03911460140c4984d19008070000c6d8595005108000c002c0480c5e0040d620980741010300f5174024042180d910400420000510101ca4803403c43c1324811518002d40720441c0f2070070003c00007903820080110003050340700d00c1d01051100080c0054020329034844c0000c11000e0510710044c2c1038a0443c07020304204a02040200111081c6000401c1281d406680c4c150390340c1455400704445c8030030b1031000300e514580e16464104591001508034491801113094144c28100500110707402c44841c8005054450103101017001501640c0c030a410300310846450010b196038a6006c07504580250380140d0150350302060b4030700280390038000d40855000c00c0d0300c1c00d0b14021020001440003680030b030a01060355550a0a0300305101c24044207a030541000b011500003540d0700b01ca000c503d140b541031032402401581c560701c0c0d49500038011502d03081c0031600a0921180e600403000000d4010030320000d02502104000805600c3d80c4111480e031000c070303001550b920b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15773738 1250 15772488 15772499
    0x606120509030a050a0f0509100806040608190305160c0f090b0a1206021305060415120c020303040b0403020703060c03022706040506090f0414070807020109030206040b131202030301 80
    0x844900801c4503866420070004a8109940001181c00c10001c038240f10b40d07103160f0000100ca1074000c04030301c10f800100004160f401d0702d42101302948a058102c03000d01c840c40c1c940003066261740d5041c00361240307502660f004000080c080c60207000d503041c2d00041c1b001c0c42c0b00540c80c0d4814101e11980b00140d114410305040c40043c0c2140a41c2c1c54120041d116507180c01d24011100c28145035810000d880d8a44c0400d00840022040f428200103120050000d6103076619041d490b0401281d1b070a10002280c0003001c540c18412140c0680c1c40205240d40185085994a441d030b039171542001401282140203141c00440010001c4c0706240f00e0b115142c4c0c0043e10b070110a800109010800d005001d41410300d1008101181e0300d020850b000c0d5003050f10025251031071140400c070400340034050a9070040c101544080c1d4481c00c02d22440c4200080c0c6e07a101403945038030906901300ca44450024005800c0903001a001c84c008416407908080c1d03400c0000200e0344c4613207424503d00000c0795400010b0b00000010000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15774988 1250 15773738 15773741
    0x180c06041d0f04030e09150d050304150207030206070f03021509030310060c0507091a0315060306060d080304080912010507031406060406081f03050307060903090e060f0409060b04060612 82
    0x74031180500091940f802c05413005410001c1c0000d00910403103546000441250308140c0703400c603220001e410f0a640031010b01e070250700ca070081e025480010003696402c0c01441e100254500840fa00540000d16109268641000f02d1060100a4096110f26402c1c00440c03029a0f658510600c22040a15224204110300d000b030000c040e4828410010703c40308030408241c011580c1801c482e08440001640700c440350909814404c4404160343c18080d03a00c1d68207001800401a6208003800c0b800d8880a030340340003c10180c034a1a400180c9081c4052002500181e031800041c558140700815913200b40404000150945d2800c03103010300000d844020020402c890000140c1c0c000008a590604003810a13100038041300f07006003032102c400319803100440592103510116002d142c01105680d40d40503142030580141040c0001107000510398a400100820f042203034600440d0011301e45140c0901c070100308005020907034010344403566900c0c041d9940d680c0b41c0c454480142204c1d10b401c8251a15802e4400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15776238 1250 15774988 15774991
    0x11040b030c0c0c010306060816020f03070602120f070906111005010b070203011d030d090c0510020319020d0c0201120e0106060e0f090105030a0f0812010b030402040b10020303180c06041d 82
    0x6045c5403c215087c025140c0001c0595803080d8500c0051009602949080b4501001e440910304076010009400f0140072040c0c00804103012100c00023400d6485030410110314090840741e10000800300a410300030903208500340d021100d040c1d821103050324050f54561088030f42c2a448085452000039011045003400c0c0182c0d04452a01001d072040410310750440c50301c921400c4501410555505030072010408030902c010094103018010420440030950082d50740c1c1d001e11404107e454500c59901000c134800030f08050040c040c1ea990300d02c969081da005441c07000c9041d150400c52a00c401c03460464000910508009107642c0c3e507007003008008070060080d00f01c02c08500d0b03400b502248006100ba9100000d140040d01c1e0700001110202106040024140c01013000c00c240380c1c804000009052452140a103015074001c5804001d041c2051040200c2844450354490240e0000c0c000500e8105800b034420b5146110b08044c4e0b001d44580c0000030f030969100d6042041480c1d400e60b4a4440100b11b1410075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15777488 1250 15776238 15776263
    0x70906050f030c0604051207150c02030708070317030c0d0c0518010c0b040f051609090c050d110f0402090406080105040b0903160602090a05030d0c120504051311040b030c0c 76
    0x142030303e014180225003640f20754041c150042c2403607600b409840b1000c0010300028400c005c2402190f0b01d00c0b2100030146020301000307901c00d1041140110340300c0340105001003140d502402c1c544404080203151211600001e0544840e10030901001f034080c9414094003044207030315500c00e6915200035610069411180d4003413810045200386401c0001e15554440d50041c4d0400861800c404091038000c1c23030f00d0401c507211105041011000900780c0c1a51300489260f0744a20301400c400340d2200240600b000305d01c480070305880300c500700d000b2160428082186540303c000d000945000c460300080b4081c3d40300380d03009401581d5280e08110520500340f000d1900880400060340c0340552440f10449880c40c8454064030303056002a881c2d00c02c1d03460000400c02008003406964805500003c064113180951000b541d003000b0006c40201400d125608035004c3c0c51004210300d0324511051680c00042c51003511401118600704000b103902d00321038001d07600c1030001d40d00c1035684d1403000710910304100300f00000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15778738 1250 15777488 15777493
    0x9040b0a06060e060409051b04080703020301060b0901050306010e0102030c0a05060a0507180603020901030b040f0203070e040c0f0c1703130c0806060d0308090109081c1a101101020408070906050f03 87
    0x22128507a84d440c200c3d011181110000f0801d13854010840e03240b212030648584a600700020005071010f40450544122802100200030095480503540c5043c840e0400c03840c002041040010340d190b0141c40c038030011201c10710490741000203020364185001c41c100820b840580c8540e00f000001682d83c003170305038400c07080e150122550640e641c207480004214010b08003170580220b0102202d034400d43c090f00d940300780184244a29900c115041000358000d850080015040a000e17003c1410140110005081d1582e01c00300d42c2405240215441c0c04a0303602200d40b0481c8803002084a6080c40103180034032000f465182c0018002c0c0307080c051541e11607014220701c0c0c003c1000c01040e941c6001d040404130740c042c108001d4566035801c960f40109003e84004206d100301044004040b0807080bd081c5c030703440c101203042000c448030840710500c5005151186a0146840c6000019140b2600b040d10300e96000000140c1070a4540002c07500703042c465000b404030699a6501005140350048881d100000f09401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15779988 1250 15778738 15778757
    0xb0903091504030803010b1606060e0405100902060414060d020a021c0207030506010e04030c0203010c030204140607020a0303050702180c03060901090b030a020f0a09050103080304021002030a0c0f0c030209040b0a0606 95
    0x100c4031800c0c0014421031007c0d503000700e00780410420682d81c180c001940707c40d0030425a45c903010aa414440203603020780b214440c0036000590034800e13101ea0301d07056030010011801c0510700090341c0101049113048136040601405040c070401d81a0003e0300d0050381d960040d01110001040159138940010800b2003103510032007040000c5a00407641c18150741081c01144425902d40c00c017507401414081d0000c0d015803034150121410b941c90f0b0301030000c0d200040c0700d05203034070051010085c460050030400b81d8048112881040040d0040e00244451880038201c030514071540c0c400c0700ca80b2202260b035130900900000030010213250845070f19004d8854231601b00311070000c0d800400c1d42c8181e246c000a00034242d003404803201350394610002c0010a440740003800107685038070300704900e0b4000b40d41c1207001da106103030b921103400c2c0040290f5121004903918050120b86075103405201a440040076070b415051150f0100c09a101c00050600c40e9004600e00b400c981085c2c441ea1003103801d2a404031003001000070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15781238 1250 15779988 15779993
    0x3020306061c030e0f1f02010506030114010e0411060a0e040f0507020c091f09091205030420040207020a0303021e0601060c030305150402040303021609020a05030402060c0a0b090309150403 83
    0x440078442d15010300d001105245558003146219007600502c5078081807114014510a401d1260700d44c101103580e0092029849010915081e00c03d05c07000010b000c248480140b000112442082d613015000b25000c201010028000c180c6581c004000c29000508014044a1f5802d0900442e01401c40b5024100300c203240840000b5254244001c0040c0309540103000301e811001c0080b40c51030070740800c030605c0ca8030320780d1601c0c0d03103004007035000084500b8034454102d104281e004c0c1090324456070b0001c03a032140c154140401c1400c400400d044d800e50140c3d00740a0b507005602c5031039502005d1846078008094011018440e031060b15580c0038103400c10ba00030001400196440003100e00010391508005c506c0c1d8550348020b2541c0680100070581051010030000181130f800900b40003a80d5900c03904c4513900d03880c0d8501809901c103020261022400800c04600142000c400601901f0003290589441d81da907275543c5554031a040ea0b07a42d45580c00461030707103c1ea103803e9400b944440c0ba1103c0c0107203041e00e0b55 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15782488 1250 15781238 15781279
    0x91505011202130c0c0506130c05040501060905120f1c180b09010c0203010f091214040509060112091b0f0506091807020a0b090106031703060f041a06040b040302030606 74
    0x40ca40c82d0f000540fa10001c0307030802e01491a00508940c0300040e12290310b40508189171860f58001c0a40710100b00e8880000c0d5802d1900c1030a0503504180e42d014109070504081c08001c5004850018040c400c42807ca81600824015648520f0a40c0070300c5c41c005110100c01009602602c8642c0d01070388211000300000c04c29607044413400082030030103462248103400001d00410030400c00300e141c103060581c000304011080014108010325a15030b1000300012020315416801a4040e5540100104000c00d0700c541c011201d40401204416001c101c44c40030395a03003001c8651800100850a80002062043c1c2c0590302d90000549020f54010b4105010440080c884484078422080a020400080f0380720520901500c1c100780d8200c90a6645810014a0103009000c40c0c4000d54817208030703240c409218020401207a000700f034020003006003030000c4170810005143c1c189200c0c241600200e085c10380f5480319005000248000c0001503201c51560040c0750400324000d001ca4458400d01c80121030200c0035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15783738 1250 15782488 15782509
    0x19080a09170601090c0e1306170a0b1506040306020a03090c0501020a0c0b030c0403050a030203121303020606040c03020c010e030d060b0304080f181503060103060602030301230a09091505011202 85
    0x13a0344081040d40303c1940030f803201d01500343c0507500811540071801d034122007070f005030707040b00c203101c141c0501c11096448158440b08084002030284c42104042004101035907900741580f46c1c01801285020b680e5507410f001c076032000c3d02d04404284c40380e50800a122040d20404002d05003030018059111490b0344e03800c040c580502030085a10004000304200031145810f0b42c001e540d000d400c460b02c0d216030b420082d582e900003807001400315010000180929030300c0b07035040b00003e41c580c004016640720101004007505041c2c500c8810907a00344904000b0010034001c88402c0074500c800346644001e080306003401e8070142d802c035055016040083c080061080d004461082c00300402040e15040d4040c01c29800060030000545c2c000700c0100d440780500e0342030307008502810007600c00f0049035a03500800c3c0e8407808244244204141e4011001e03c0310303140050407081c0860010181c5044a86034921201200c00000d030a840624400004040112092003501e015011031042850a421250300041c0702414 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15784988 1250 15783738 15783749
    0x20d09021521040f020402210603010209060403060506040e0706090501030e030c060106050a0306030605010b04090b0108010b0901050703020111040801020304030207060801050f060a0c020d11010e06090901050904020319080a09170601 102
    0x1400b00080038880c030082e5036030300c850b40100155903921a101c078480c042030340d1342c0800100c4456540412400d240c1442110007109002e804170b800d19103151240c1c070003000001d1426410913250072110b204810305001040141209444502c3d0090804000404507000004081c4a5610030072565418410004940341103a0b000d1030030955030091480210058a40703640020007050600c000891324031075501c00b400036101080d00402015902c4001110703065401c1c8140d2001c64000c04c40070400754851030081850034001c1c000403d01e05480034454205502030b9025100a0350b021092004141e4103200b0400200403514001d281d550521000a121416842046124a1000440100043c0105c98001c4502d80040c203411a00396682015102100c00c04101d50006048a212803100e10340101960441d00b0082c00e11206a070a103000d00c0700c4a240500b081c1e074544542030000d0329680e0400328003c42e5500c60f0511644490305d403134015003410302035003101420581683c0a1101120002889070440e10b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15786238 1250 15784988 15785047
    0xc0603021c051509040215030c09010e040207020d06150506030a09020a15050a080a1b0216051e090c0c10090b0708010302030303161e0302070b1302090403030902010210020d090215 79
    0xc41c0c5d440021101b201c00000c0e20311124010040084059500014081082003a01d40f940c0c00e600b00030400c0202d1050342d40096005030380c00001c2c804501c8541c0044058903000030900c1c52640c8510005400c0d130002c407980744085841d4001c440c00c504112080400400180f900500d140c02100c5001c0d02901500760281c0400110600050400030250400b052106904400321012a00e06200940b0307030b40c00610b6110a110964800109802c00c41b0008501c550102d843d1411007a449003008520107010b00601c0e02030001740058000c1d28400c0c4030303078000802402000255102280b401031b07050341d0010261014071426000403c0580c8011085903440803407881600c0541d122900150380403d10301c48000810191082c8807040341d505940101122030183d1031082440d40c5400b0394008100041600a400c032502e8000b290001c0d0280e00060300140c4140165001440e0001021049800210840e0005521100040c095081c4100c1c41c151168403d441c0615203510703c80305081c4800c403c5850146003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15787488 1250 15786238 15786241
    0x9060f0302010c0611160305070203070b03090307030309050c0406060c05060a050105010c030c02150301080f0601050303070f02090a091509030807080603061f030609050304050901120203190f0c0603021c051509 92
    0x1742c01c02c2c08503240d03140c80003803250100e492401c0081007600641c100303e002e482140300c007044005011060f00e1240c01070340011071034030203107590480c0500b1040c038045034544601046441c040e540c5000f4800500307059940c40c0c10a04140c1441c078949075003d40105902894400180038590b406882240703015054105225405492320200b1030b1000039041d5000c243d0302c040004a9009004103000b003584a01508803541c03642c0747c0082507101d100328600108612500e290140050500840d2560b0194031501c0010741c100d8282c81d002c48004007074000030803482d5180d181504260f0170441d800e810400602e04411540380080209640e140080d1091949032410b41c031040c10403400060007070246a22040504c0901028a4115074030782081c01014410b0142000204400e1107071038620081c1c50b002002031140301c14084a4902c044449002510012030740200c00c000300f01803400207030040c882542c005960b013158069400b0441c10b05c0c900c6103034480c00c181c01c4c00311a1241e1907440c0c400b508100d4806026 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15788738 1250 15787488 15787511
    0x30506060d0e03090904121211030f04050304080105130b010b090904201207060311030903030705030a230106020c01030b0f04020903010e07032109080615151309060f0302010c06 78
    0x1d60080d0807130750b0340c801180c00400c010800d1074049901d1040a030340303450583c00380103a194007da95401110840307511007400017451980300101810380250003041628903003500e451203142500c908507640010300a02060050801116114041c01031010337000c0c540c2420150b200103200540042d00c05803203c03107030185521030408800321880c1840d000901208036004800e41d0252070710744900c03a000c0403d00d0301103414114a02c041c1207034815001140075524580d02d140b01600c03580c2000d0301580100d80e8440c2d4000c440c0408805100301750413402441052507162030760083c40c0221051041c1e040604048130449562514a170b60458440c04840160720f4031445c0700464010031b91608081601c0c4500300001013031281c3c00804010064103143c01a40ca075400c0582030b10401c0b52485505900d0380f1a6000038606025180000d42118000f45210601501000030003841c0d04102d808085044440310308204c00c0c2401e01c504001801080f02e82e1100301e165400182c1403118007140070b00f0881c0c40b40d608858 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15789988 1250 15788738 15788743
    0xf0306131a0c09151629010803160f0f05030d0c140409020708090d08030403090605180108040516080c040b04110307050d0207060f05070809070e01061103040306020a080412030506060d0e 82
    0x1700801281959018948581481d05612905d644500a000030400c0119048090411403c4c140c03013201c80114a066001d461000c012452010251120300320a00c860b0700140f40040040320071070091006544609888592038100e50b900786040d41801140408503660715880fa087d1401c40e91400c800617160541c0d4140100d5511960146d103038407144180c10030040160200285000d02c3c082d80c0c6055049440e500181c0c0e00b4410036103000d0051031030306004038080d8881c1c0c991070fa0042c411800c0d540c200030300801d01c00d400c0349141c00840d9207420107441c400c900c0c02d2510542107501422541484a0b20f03410400c1c00261002902075401c0120000c0c65035140703151501151003071944044200580c0c2405107071840148402d590f007070000b400a40c08540c1d0307070704009828803c0d2010820109040d900e07040381a14085c0c4081d020030700c039000501000010851510291240c1c04c02900d50000d14070b41460312142c00300d003a00c4010245850031007072024645601f02982c81004407040001441c1e00c07615000751 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15791238 1250 15789988 15789997
    0x6081b0f030705040e090304030b010521100c0212070b010308030c0c0d09030b0c03090c060d141003020f0109060509010e0414040303140603011e09020f0306131a0c0915 74
    0x250030080000c24403204552010092003201c030810404103098884010300c41d181d100e24031000d0100702e0b02d41d0051000d460f01143c1c4005540740620f60703410707110300c4280540c1001e103041d2218110603a5404030050094041c0400e9648503030304503070706103030030308542c0e0b0351204540c18040500160070103c0098a0000181f04540004070728004440754152441c0c00101546400d004c11100000e5102c00710720b40d84085d000740c901403050b5001828410101400340409504044c80241240c1d072240d440c00701c03a4580c40300c40c5024503258501d040100b411070061040020844030150b040010300181000611760080a0711140074007442c000510005420004000d0101c18903452881454482440101b54060303001f030b9152440350030720640c0d640d502c1c01050700701c4107a01b45841c1c5484440d1124a1051001d03800368030101d02c0108546801a01c001c04207281c40c004a46e1313400c052680e00052414003154046900061924155450301841e24002c090054010340c0c00c014000e1004042d150b44000c0110140c0e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15792488 1250 15791238 15791257
    0x501060b040f080705060f090112020904140a060605090a030b06030a02061803060a020406171e0403090e0a090c12060615090501030b090103050a1b1508040302061006081b 75
    0x1191110b4484000c00c9107582c4034450000944110707440041c440c28007030b00b5120102d600c6292a03042404080054903542040410860075660800c074011480d40c681c801d0041c911480d0300604400c2c40c0c5500c42030100e800d2500701509000090100316180d03a04d552011094aa106000d0314094035042c0100745010060741000b035201070f020a0360481d4403880740b80748800c908110115262900d40d070950b40200d20a90041c4000109644e61942c5000da070841c040b500a01c42c1417204070b40031100c600c11007946d01e0030348007100040c10950080060103036000a042d08007400e0402008075000d143d50305034224100d4031503002c02104900000d01070084030750280d0001c01400611841071038880b94020005105402036a0209140c908048250704004c080141038a500000a04602c4141e0b12001501c9490004100b024103c2040c08202c00340740107038003841c0300600d4840035000d05003468041d040103002440180d00040314201044401d078004a500e4012100007014158619881452192449001c0c40c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15793738 1250 15792488 15792509
    0x11010911130f05070302070209060d02030303071d1503010807090e060106120e0609011b020f03030604020f0d0903030204050a0e04030905010f0302041a07050d02030a0c060c03020c01140f06030307030813050106 92
    0xc00c00419019001000390510272188032050369101f030100140b01e02d0001000e50540d2050000844c900e0040d4042d82400e1444070144641c252a50002115226407695080070741c0300100c01004105c00401c4688040d01c200001840b582c6802c0480a55403001441a0401c0000325440103803034070081e42c4445060381d4842c2c04c0c0c814034507082c036510380a004c00540380650068001c0080a5580c03010500c5008450544051441d60316020704200c0650440c1e503420003042402c10000f0760714006072042c215001e20036140962654604000c129241000d0742c4940300e8003016030208070010354004500e1007034030400d0a007400b0030107840404a009015640011a00c243d0010640c031505554030041c040c054803460403102c102c00308010407600c9012350880c0d5404203403c4480c00c8000b0740b0b150000051140d00b80381c018100500d0298090030754402403004400504260180114908190788103035003c81c082d070013580780c00e100d0380e8020220403004040f102e00105040c001020800700b034101000803c01c0011307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15794988 1250 15793738 15793741
    0x4090906050105010206010b0a12051b0403060501180606170406020906120f070201061a09190b030412030c090302010c0510050c03090c01020a08030106051e0c0703020111010911130f05 81
    0x41400007801c081c040e060143c890341c000000d691154404641c4807900507a261070460021034071213000390501402d102d00303001d01505000c034944100c030040d100850084d20042001c1d403425803a00c0d90030b801c0350b6010200d030341800014030040e60010015100000704564811a6548504003e80207020300c0c841c03070368021000240f1031242600d0498840c01780703012214140d1070792506031b01603088540d14032400200ca404030b0004280c1000c1440507218441015084039841640140000000002c0b038100040e4940048203010a0002c103070781084150705141010003641d1100e10b005055030784a403000904228000702042d00304001030100395500d40c0045070a0002d0300305011031402c0358000701c4880301184529440240d056200140d82c406a03600408200d1460b42858411903d41d4810005492002200e01d1081001091003000709503001c141006000302d242544001055428500310030500d0741e040096030f40c0481c2d071f0030360b40d0f5540c1c039000ca4802c8010007001103254068100041c004020324903000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15796238 1250 15794988 15794993
    0x3060f080a02010e180106051606020d0504230c040c02101802120102030606030c070201020a020a0303050405100302030f13020114270108040b0705090a0b0d020a02010e0f100c05040909 81
    0x8501c0016403003602c40c0035248280d2030900114034005114820071140e1400100a154007500082010540d01201e04042d80c07555201e0000360b0703110259100d80c030340d0b03100e003003005000074241c13140129903030f0074042c1004500722030b607295540c280001c00600c129900c0301d1850426008004119503218443d5060085c414001401c6c804052100d000340d002e030b0408060460810300620883e071003580c00400240c15910354901d01e103840d410a4000700d0652080201c00000341e42c41c04075640c01035100c1d82d1034076034031414401800340416075542d0780000e060041c4140702c01d035402c9200c420345c48006880b100c0381c2440e607400101c0314049409040445000009484049110240091800000b80303110f120b02002400004442c80c80007100c0103071401d11103c0204c0d0042d03101e039000b8032200d1030050584002e01c1e00c0d0421100b083e03014811550b01c0543c005580c9480c150280a45100448000094541000d400e00003d8039070b02070b15041d074452581d511220001e14000c005841c003510700800d041210181c1c51 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15797488 1250 15796238 15796243
    0x230108010c091703040603090303110c010605030d0f020c090405150f07021204080a020f122e06050307090c0302040e010602010e15060f04050c090d1b050306010614030703060f08 78
    0x1903415400603148000100f50000f14000703070030100b0b4121000750f10302403400d8000c130002d040c0039000700d04050b19400c8a5022104a8014001c100f4810700000782d4035140070209803401040924600600c690103280c060380940101d00511000f000392601c00c5555694500241000c000c90504401c0e100c80d801400711651000c2581445401c0c241c08544010302452201c0740c00b0b00552081809580c45003c0120050400340383c54004040058503a00b108803030203d41e6410304081c0002d443c8641d0760001034000c68201208005642d0f0b0f95030108220307072400e010200342c807100f45000c1d40e41c0c0030361145000d08946200340e040750014120b02e9000eaa0950b11020000d0180440070004041032042980b05140610301094040c06041c000305031007192407613103080c0030140c0801850aa2030030014000301c1c00c1d0740ca40381c1000e00007610891242c911810151102482081960080c501a5101c5401400801d4004401d041d070006071920b41505ca41d54550300310302903c0107410408100000000000700400300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15798738 1250 15797488 15797501
    0x1090c031703042307050301020c0328021e0307020312030a140705030106030b0307030203160503060106050301030b060607051608030c0114040c061112070b0f060303130923010801 79
    0x1496030420500c420400e010384501054030040d042141320346000140c401010a4180c1c070080d0398040e18041552a000079089801c0b0200c80d00c160f4000048040211829034540303d0003c11030380783c410052154100c025900d91041c0345050202481903c8042038505c00c1023915100c0c0c1c1d0080c100c1e840ba0f003800b00c145400707810035a00b2038401360428003e8544900441811031050b4510b036103450a580c039200702100504040b50340d00d80c040c01600c8010025803018410700c030220149210000500b840e0030145440c0440581c08481000410300050000030b28080b003694010b0001c03290f00f5214540c85c104241001c0c0c841150003200040750600207402c0380040050560f104006c0d00810560030b01c02921106c40604850007003400c0c1c0a08000d2044600651620580340c41003022180308050421410919070b008190540b0046000c3e0304020b170345485500f50560080c1c3c15405181469041502010346403140e00481c0317180364586090110a510302000c1d1429000000c8541c9100c0d42e461310f080e4000c114 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15799988 1250 15798738 15798743
    0x70c0512120601050c0c060904060f0b19050c120708090303120f090106030b0103021201140c0c070504060308030a1a030a030905040605030705060711060405210c1203070206070609020301090c03 85
    0x11040062843d40c015015100b2206201d4050020074400f6420000280d01c1082101e50059803800c001c9555080c140c02000901201c1c8141980d40314904207240c4070724071080c800c40400004110183c140000801c1005851200803405512491075182102c5c50b4002c59103a190140701c04a000e00c4406011390a00d406904221246081e980300c8142d024240c6445000141c03601c170309070004200506101103601901c0040c03500004a006208001c0001000d054607078868562000c5a8000300e04002d012050007040225410012180386580b4004903010007401d1060003a550782440c140101003a40142e0140340040c182d50b9003900d14640035041580d03600916000c1d5181c182c000c83c403410002001d109580c0004c02003030920b001c5540f0408640001070710540c0101040c0000200340c2c40d00e20740144110381078400d40000e5807100348110b1070802c4484142e481444c41c8211110041804030480b05042c1d01903070896654030321400e08001030319041d070000f0741640c68280c00c4030500a0700042101641d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15801238 1250 15799988 15800017
    0x4020a08180705031506031005070203030106020d080112030c020f09011701050105370302090403091508040201050a0c1712071b0b060f13060308090109050103020c0d0503070c0512 79
    0x1015001c110340d031210301d800b8140d0194851003154000095109906520010003421140b21140316180f41e01600c0302943c0100250344048010b0000c00c1d0140866131800c4050702d004000e562515405403c20b4019000c080c01f80b1075911103070801e540b907001017204460409091603416580d11501c0039004904200c561100e5480c24001041500d4407040959260100c0c440c1405400c1c1e441078410064080d05a070040350300480940040145c90b10480355200b14001c0e01c4c0d054519283c060706811075110902c0c00c1003081071001c10040141c0c3c0000030f5a810b0000783c0b82007064802940340000d00c091807581400003903000428003004054082e00800e204900e190340368440e000449070300421485041e000142400900c0f00019440e04081c9c10624804c20000c00e20104d107910070781ca240c210344450b0802c0e01c01000005415060b560842c840000400081c81d0840c90010000d45058980011003071003001c04c2400000f040025110795000304080d07801805440e00d2030441040025194070030006800380c034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15802488 1250 15801238 15801271
    0x90c140102010605010e060d0203100317070201090501020c210304080708031b0601030b1308070b0907050a0518010312020109140d0e0402040e060108041b0623030115030f02070204020a08 82
    0x754483c6c1c45800c84020045c04d41420003000030300e02c0019410003403803e052040c41020001c0401c90b405005600d524091131615582c41e0107000050140000b03410050665018401ca21119220b403034085a08102c0200030300c40ca85c280d0106607040d0311a0b80d012060911800c4030106007c1e0b0040014082e40d40120b0034800500d00c200120303501c0d000f003444060710000b4a00b0010341b40942030100102c8040c40b0340030b064545161a40c0304a5080400c0c1c0786007045030f020700401d22a500f01514460003500c003c956801c03a106809043c44603425050000030074015444861200c903a000b501302401c2581d00c4480c1608146500da11a030766012441d03403000004481c4801d12030706003454821141562840d044041c401c0e602c040041d501000c000c1c204aa60b0701c000304040101c20800042200a0807039a036624201e1a03000c102001d480461402524012a04000402241c0c003440760010700e0010174200030a01c2e419095095000b4007078620065045400000c680321034a0f488003200348950158411607045 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15803738 1250 15802488 15802499
    0x819080105040e010c1b0303090206070b1b0c120c010e0712150902010504090c0c0803010909060b0909061b0c031c05090c0a050f060706060f0314010c0906080604090c1401020106 78
    0x240e52a640b402d0021481401e090704003001c0d140c03004030100d8000c8c200803ca5500ca540490081e030720a65007540c21495117000c0c050712040b801590000f90320300d04542c5007000f40c600340c121740b114140c9010803900c420020314480c2002083d042075410b41450415101c1642d91005022070b68048101c0441300b405440480c54600354061260401c4540c040c1c1da100d04041c00c01c15404000d08041d401441405020895503000039034880c0110701a00c04001c0c041140885807410000350b031b0396a4283c600c50200c06041001d05280060b034207510250301d078031032201c02d021352824106030700c2182c52440c0e42d804001120440300b581d19245580b07a46201c0c100300583c2e540e07441c82a460303000d00f482c0f0301e6000401c294100320300d28141c140e076401503c004250a140c1b10740303959918211600dd920005100c410000c0410074810740086a2068401c0c0c04000e110400e10000010101e554070700660007030006c01004100640c0342d69002000707a40e407124103000050744034100301c800d8003e020348890042d82459808140c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15804988 1250 15803738 15803741
    0x9120201060e040803040819020304090e010207170a090312030506010806030609060705030603010b04090c030501110c07030b0c0f0309070807060f020c060705011103041506090605030c0d0819080105040e01 90
    0x850311090b40d20040c42d142c40da81d41c40164400780040c4c480d05001d000c0040b440c4141401c0008200040d00210b40d29490000c6000580c0e580b401d80599a0744140301c42d00c0420113540c0800c003591083d406950341c494840d141a100c22140340c1000e0481c8607404103030f040c400d8042c0d20860117044c0c00d803503042003642c070301c8205955110221800c0440ea000000801d45150051001d590400310040022581506840126007180d072142015510040701000400601000703224481070b010490307405030700d808441a52143c0e5070800344002050a0a5440091002c940701e40940e0b00700000c00c900c0c15540e040010074550b485805005002c154004d40d1800550640601e10003143c0302d86640183c4a900b040204101107904990800d4071155214200c8206030143c00c0002d500c2540300da2041d181d611489002ca2045030416005280360500d0044244100da80c0010820034480040311803004824851400c00d030356000c1d4040850f101800782c5103541c00142c00ca480c26040e80e00654040041e40900341d803e50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15806238 1250 15804988 15805001
    0x20702040b06090d06050403110f010614040b03070303050c01090602070f060e030a0e0f0f03060f1f03320706020102041a0301050a0302060a0c080d06090f0603110402160b07020109120201 82
    0x5504c1004540040009a0240c0046510034040d082088030005128409404d00c00300c54800c5550380d5460a043c03144000c91a02045802d03c142e40c100105c0c001800841c0d502d15a601002d41031000103c0d0307000c0100b41c00d400000f001e944c0b100d4150b460300d100c4e25000e91028810f200c22101c0074107200242032000740000a40f00c114481d03a8032145081c00f007805100c62004400c1603a03800c5280c05100d020036840030003e0744d0003205040c903030070728914001c4640c0c0d0311510011512803641404010400201f0010307507154040502207120f152007100c8040000c120060111282d82060003100c000041481e0107501a1085402700000382c000348034802c550310300500c401d029540e8405540d68050025040c8007000d828802c656080504403a4015140c4900701d41166190707a100350b442e544140b009501c0e50160300212501c0c940280301c070303505542d242555001c000f10700078042c40c2d0204054440000ca0a84030134415080102c500b641d0801d800000e000e4014003100362144009068584480d0b8414031400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15807488 1250 15806238 15806257
    0x60703110d03090b060409030c06020304210c0804210203010e030306010311090603040303020c0f010f0603030f1106060f0613090204030c0b0a0503010303080709051207090e0c090c070c08060109020702040b06 91
    0x3c070190384102c01c000003050b02c0701c408c0e000c00288003074080029020344001c41c05640a039413a0b900b6a10300321108040c015241c0c1e000700c01c1142c944030036000113030f090b0300f80c03000c2d44d0f112020510f65076000003c1103950460020042d61642c207200c0c4180b110380000c002075024007821390b4284588080780742c0b602280e01c501d44100307802900800000e00403030b1003a405080c1100307500d0142c43c0000344d805000303425190b0400411140558641040040540011050082e01410704007604d41c0b55040301c201e901d452000740840c0c021305050001c840150385900880e02c02c158424203400030365840b544000020340290000700e5907040207610105001d08000e0a80f16400015690185560b0940c1d40488074683c1c05030890301480340c0641d010400e03589103914010114800da0040114a16000c1000c0964080e00020341d1340360080310240030756491324100e00340e00c40306c26401141e40d50701510b4603000709081ca900c600000d0081c0c500104106500750010442a03008440501071003014004000092080c0b243c42e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15808738 1250 15807488 15807503
    0xd1a19020a0512070903140706031a06030403030e0c0a0303020106210b010306110f0f0702030c2709070801051008010606031104030f05010e07060f0201050109050402010905061305060703110d0309 86
    0x300c6018405800f102d60043c4986411030341980c0d02d64980d64240d0030100c100e5001d0b04001014002a40d252080401c000042c0c036841c1840c504400104483d48409400a0201900c5070010445100f08100740c0b00b103510041c0100788011b6a03802c009000b0540e600403d429101845869016240360152902840740c0180d250344080e440c0d070f500e400003072200300701e07464119201748000e001c0e902d41c0c0005170010403900c410107903650950b441014207140600f00b4461080b08044d8505e07401c0d800d400081254003000c1c8012101d651035001000385083e9550b8000d030740b01e40c00d001c10070050000091145c000c40b07201d10024000c094480304141e0982c0e4100031600c070510070a000c10408115030194143c2518055230001901d11608203100b81041803940224021440282ca003444050b42403150600410200b181080306007440c5e0300080921250344217041c8201008903070740c4501c070204003c200003054000c0c8030702e60f07030003561801a00c10300c420408540280105405402041c1c064002c16031102e03803250381c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15809988 1250 15808738 15808747
    0x31204030512180406060c03020c010809060703090311061609060201020f09010309080705070b090f030f07030f02120105070e0109080c01020a060c02010f06090e0105010b0f030609060d1a19020a05 86
    0x102d0b210b900002d000d400e400070000030006031612a8417448018107001c0e078900c10406410700f0041d00d42401208458100031a81040208201c070100340c0c80e400c528103140200c1c030507810703050441d020f044c1d424604449010706814011401c4502c519454488107a0303d440248641c2c0c6c6200741d00301c0c021803404802d0440200a0010760358440c1c1d1140c6012441450000c4c00c0c08801d4641601d001140e411008a0784400140b000252401c864241103a0508170300070711859620810040c0c4072000d51000400141e0310031460011943d070611150109801540204101e01c0c000b80700421005014561501140e80b114000c25622004241d452145906030020001810240c3d200402404103100b09400c5540e50300d50200401c01c58091030f4002c0c0300c0e070040442c1811008140a00311401030b0b000034441e540811944000446000170f582c1c1c002c1e81180c0e554260743d110008a00c0b4200b114000030102e01c90140d20215807000381800d603015581c0c0204140c0808507243c0701d101207104007240000414030074003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15811238 1250 15809988 15810013
    0x1110d0507120c060e01050702120c0a02040c031b02100b040b011707110f0609010606020102030601080c0f07080c0d030c09181d060702100c020307020d0209040303060302100309020312040305 84
    0x1401142040e88503e41000351046a855043c00c80b017940d007019885946803070606c031251b5410024009030b207104041851501c48110348c61780c0d691084400090143c0e4a901c00140107600a40c42803130454003446c0c00715052510244002c0d00c99030560030044c102d40c9880034084640c1014818102c102c0345c1030715400c02e5540b805115145800b801040c0c4420442ca15424084000062140154071000310008207010b0a001003083d003540e290380c0040045a205204005440ea0b012003415000554642080d9441000503a544100d1040039070280c100c440004421401d40000580300320200c050b41d408000f0500030510485400880d0302c03c00c1e0f4920284050465a00b4980e84946545121080303244800001c000c0c0399402c6c06022140b080158002d01c10001d2160381c18010803074540c00d6440070314a4000c165000030301c2e4060b00700010380203210000010b401c1600035032200300556001080c0c007605d0030950000901910142d10b00700d01a000d0701040c00c02801221080d0303000d0b2948100540404851030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15812488 1250 15811238 15811253
    0x708070b0405010f020a0306030b01120c0b03040c030c03030801090b0f01210f0513020306010b040501020a030f17040809030c04110904020a090b0d021e0c28020405010b040501110d0507 81
    0x90419255035590342c00a98131643c440c1300401503c40c56440200318145181003418001c81e050f0700c9456020076414801c0009a08580c400095810103215251a600c680c1001d6140d0750a0740c2000701700141181002c8140341e003244446040300c411000034080c888051007031180075100a916140402c44040c04d009411416a2402540d1501c0c5440000c480c00d4901d42030082d24020b1301c8180d004204c6041e036000b03500b000c0c803d40340580805d250381d5203001e2401000079a036085810000d802c00000d003282a81c1c00b4030a207803c01c055480030203480300741e0819041c683d074150302074103409110b44120035407010107007400e01809850031080700d00343d0304000c801c3c0d0030b00c4081d50001240100300107000b10081030162201004c0e041c40d02d402480140c49021646030030000c184038041c5d0034141e001c24031482c00d01400000d4812031265110091009202d08080d40000520510078000d601c5810000049249010f110141007205c1099940d1503228402e41403594850b10b1104041002030300422698002c01e811 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15813738 1250 15812488 15812491
    0x30207150c0222050c03090703080703050c100c02070f08070b0f0903060708240607150609060311030c19030f0203030d0203070e030721030305150402040e010e0c0708070b 75
    0x118142104400c48940c001901e0f0942500d09040b1a1100002402c54025900c1035503070203c90100d0b101d16605140c00e00035070301c03219072000a000010024002e000c05220300281d400701500359040300c1c048a0401840c0010f05a02c01da03510040c031400c01c0000750302290a80010443d48190090810b440c00c0106030351180d408140d0f01220b411003000b4400e9a9101004114860b503038540e160501410b00b02145e9000b0300e42c85609540c810401502c0d00413980d01c0d40c0441d0020f584c010307280012a0b49208100020300120307442070483c1442c2080001c24800d0181c3c01040c507460032001d1b80e03054401072080110440b12110152900c40007000c003480010241c5c1100801c3d90b000800320f0341001c000703c460006030380c003c6a001001907516400714541f170a0401c0301c3d802a2002883c20300020544c003403801c01441e1401d001408258580300441c641c2202161020744a2102030070070f5688a0b200c5002d01c211032428450000e8161880001924010048c02510050b561000e540c2e4230317203000c0c0d80351039447d410b0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15814988 1250 15813738 15813779
    0x30f05061b09240403050d1b03050901080604060f060c030207080706050f0f0403020307030809041506050f0d06050307060203030906130215070206090a08011b0201020705030301061803120207150c030207 89
    0x608005500203e04804040c0c4000c502c00d000901d981500030340c00400f0007808801a8285401c0000d04000003900401a260080340078a0118191b0b51104009006007403030780e01c64040100182e001042c9181d000819841040c043d4084071700301740d611803200d81d44102e00c1c492600000d4051021459146000e8010a01c1c4120040c6003428a40c0341d0300081e08161150784100c2d8030000c00120f40096091034002c4400c80e0b50f100d071005c6071040c03610002400c03d1040843c0490f5200c40020200007a40700d90f403201014000207001c540040381c8034140a5030340c1c4d00c151107010051084c04002650310300b60300c0c10b56032700b07542c0903058484119490084048030380114408907800b180903c015099a203503c0f9580000708020400810194460002800980300d800482421640100051000b00e240042203e044038110302e48102c0101d6140b141d518500082d4100400740030a10666501180e4001410b00039130b5085181080300058404064440781d40e0320000902503000110100a0f054600d000c2041c03104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15816238 1250 15814988 15815029
    0xe06010509061201060f090503030306090106081018020703030605090c0a05030c0c011a1201060302090606370207050105090108152209051603020306010b070302030f0301030f05061b09 81
    0x5038140f0074482c4182098208030001500c01c0700c0390f0070596206107458000c00003600911f2442c1046004126204030500480c000d00880c2e2000c12250700b500a1950000d0484078a035143c4400090038501c0030754800303c2c09a00103402c02d00d01050604d01911010302901c8042c9a051820341402d00540e80c6400081200c050b140040c00303180c40c0c01e41c0c203008170b10341c007600300d400c0040c2ca030ba580b8104407008044880444082e0b02d0951305100603182c8940c1c0940040e42100c80544a11225140071440d2802c684d9604910001181c002c9040301054070803050a89190203559000b5162001100c0c58010300408034009210407001c14401c85201c2034054640700050808100340003004000743c80101c58800d0710840365a10350264040c004107021800d50058151400032a80d40b868001982c1c802042c0135040c95101c0c0080c0b440b0426008000719280200e14061080d01c941e92420065000300362080e05480d54010b410002d1964003a1511230b4071100640360101e81800071202c00e10014501820034805002d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15817488 1250 15816238 15816247
    0x609090601080d0c060917070506070504080a03030e03041d01080105060102060c0a0f09030c080307050c03010204081c090e0411040e0a23030d0212180a0c030b0402010318060516090e0601050906 85
    0x1e010a511420b401f60400340c403e41d030700d2580c0761491800900410141c01c002d01800305020940b40400c000c00600e400d0314000c2822140401c9443c00c51003564418401020100464500207690351001812100c000740200b02d41d984020043e80c8a02b03040303c101400d43c40c10032500c10810f0117000305000c070344600d14060011a8480c0d6405500f601d003074020900303607480441c07040e0800808100c40d000d412401e0740258103040c41c1205440d5110b03c0e0300c0d0540c00368589002d54440b16445842a18020029501c1c0e08409041c40e081c00136044038184007450181c0d0910030104044000002c211415a0b403040c4809122070080f40c0071aa200f031848220540c0780020890300c0d115440c0c81c0060580b00c0d85071241c451090034034034070854020540c0410072101d504000d400c4000310782260300d22400c5075005400d0204a42e21440124014400742c2544404682d01c9100d600620219900c4188120500c0610250700302c1c2d0030703205590310701091151410040141000078440c2d44611301401c840c480140502d03041 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15818738 1250 15817488 15817493
    0xc0f0209090f0106090b0f040e0f03030406060501031107031d01120f0b0102010b0a03080f1b011401030507060c1104090632060109180902150d050609090601080d0c0609 74
    0x80000a0301d140036160710000501c0c16040082c442e9400402419408000600c041800300f44440307102d03ea001e115a41d42c0d10445520b00c400e0010701e0b10041e941c01580e68a203404e151100052425001d8540046e1070b0411344801190508201c800e2aa01600c2d85080542140c0840b1801044c0519603810404100c0e00f21000c1e5945000d03c0001c003500383e002103624501d100009085440f808030305807141010200400c0803480c03c00c11030300c1d6448140502070b82e03120565800c0d486820240b003035440c0c541c6014400713400b00020a4046040c1c80c85201641c411640e100000c9075210404040580120707604060b00e0554038256003c880305a03c03404010501a002031400101407280c4c124a04112002004004514200d883c0700e69100d002401d000d580d89040400240c19082c10b100c014070442d599550fa1029550780036103464903603042540da10383d54244404410060542a00c034030b4081c000d41c01c007040703ca02d00410001e050b144000000d049420280d507088426500e0490155031665552000501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15819988 1250 15818738 15818749
    0x902011e0302030f060901120f0f0c08060f010b0406091202030a080408030301080105060d0c0905180607030204090b030312040807170703030b030c03070602060613020c0610050a060311040302010c0f02 88
    0x81503640e00d0040e03d900d00060034012000c0018200351041c0310000050006511004071440010b4010058654400c0980350102541e01c4c4414050a12403282d240042c0e00d010003c0c0362031113100524140c40450741c0c0c50400840600490003030001203070000c035091085c007044401e81072043d400102211803100b180e071121b1010342d101c0e401403c1150030000062002c10000d0107090342041082d103501c0c8000c5401c2d00c0f0b01480d4911402140900c0e62600d0102e02c98010891004400703204103015036010f401c0c500c40c060000c2d8050301c0b4480d240741c10507145418528001c020348545005001122131a503540c1e42e00c041c0c0f0b680c080706003180d0b02c0a40c40d80c01700c0d9005016000d40b160910a80300018443c2c860070415160001f030042051081c0d002100602c400d960114036035800010070303104c1092a034070006245000c0d01500504980c244114410800401e650981d441d00712002903c60f03c1e0841e8440360210305071081503120b424407200821003000107520404501070658051149030355200e405600188 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 15821238 1250 15819988 15820037
    0xc0d05030f040b0702180c07060f0f050f0106020d0206010f1511030703090f091e0209040209060310030201170906011e0b0a02010c080c09011d0d1208010f1401020c04090201 76
    0x500c0320300c002c580c502c1107042c4180c4100190f0303220342c1d10460500d0401c4e030240040c410414010842c6032a5140b102010405030000102e1000c030700d0bc20301041c6010030710000c00039024400d2000510440c070701340010f1800482d00a05031496000e002c2c46076418039411090b10401e80c0402802c010035081604140d007010b1025003170035032280d030782c40212034609806032413009a40e4010005003450301c0f00200c10b5030806441c8401d4090320107400341e02c070110030002a00a0007482ca11070f401110000030441e150101c0c8050b1010b03a8401d8841034860f90390007042c58500d402c102c56050701039125100521611590800e08036192036145110582d583d1900f44000550700401c0360040540e444080f00800d01d0f820000950b031065a400c407090030003a65000084c0700b130f00c48104010f50300c10030030148682d0383c44590076414a10740210304860000000c02c0d00510300ca0013440742500c40444050b0102d01c07400c01c1718450301d44400580c014607201048100300700040520440803810b1051118030103000e0b4240e80c81c480d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 15822488 1250 15821238 15821249
    0xa05060a060e06120d080a15080102071208040b041410020a03150603020a09050f0a050603190b0a030209012d08030403060605030102120c070f050307080304030e030606030c0d05030f04 81
    0x10a04915003440c902e002480a00028829002a150300c68400000110120015018901089262200c8002100034038444039240c8010b1a10030011403000c1d0150001c0c54094031902580c918190200c00803259424203603030040140700181d011401080e942d5100c6500c01242c00c041c1d41c90108021500012a8400501400420b480e0a40c0c034280f4002044000002c0c09a4101540303401d281e010001d0421500d4091075200b070000440022a985980b03180d05c0c007402016140654030308110307960351090300741c9081290000d42050038203c0b503814942e11010440b54003502c0002d031a4289a012b040c81c540b18080c10141d6080c0311f560300c00051503214440c0c02410310201840d41c0d141541404804d90b2101d401c0103000342c2c010058407058919400c1000c0e4041e1210080b15150441441c0241c4884c40710b01c4050036500c0f010441c1c40c140002d0782d00441c0240d110791120698881400c060586480c0b04603552585500b22007000e010350f003400c04c5907140b40ca103e901540d26002100000100a0704540c20a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 15823738 1250 15822488 15822491
    0xc0906030c02060601091503020c030c0106050907050408070302010c0f15150522020a0507050d030501090501270209060405030106030506060102010c1701050f0f04020304150c0302070b0402060307020a05060a 91
    0x82000640500c154202200e541c80035086a01d0724500190191900d4400d104088a0b1707091650410b40c400d5056881900d01386098958840801204e107010305014066a8400d000f817174045120140a0030449040300e0001000e000c40340c2c40c40d001500c15001c0440180da11420354013441d000614045204408a42d580600050007400814525000391141e0403040c051014400c100e60f0041305504510600b42c6124009a17550305800011280360080000041c91031040034000310703080e601900818142c0b414203000300520703aa07031001e01d10351060040590689140e011170460f06800590000e041000d4041e24641c5426981c0300400d003166580d0307005607800c1d08600c0503c2101d40e42806a002c04500321714006c484d01840300d4032120418018030134248031f6030305201c5205c031640740c9007408a5660001402191030b07107058280300054092094203203000c03034030344252081c00501a00c2074070039564208090031010382e1207074280003103940003030100419440390440c20710028404200c0640301e03540d00d290 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 15824988 1250 15823738 15823757
    0x6031e060312180f0303030a0f0515010e0f010905060a020a050d0206010303080f0405011e0c03060509010f05090603010f0603050f010b030d0f050307030b060a02241b030403030204090c 81
    0x28002600010300103034801e03000101000c11480c0c0c0582580c4078500148400c2d45140f2030000002d00e9a19501c00458242c00003008104081609a0040c06403014036032040c0441c1e5644540c80609907078102d181804512a441e4415a90803e142c0718000a00c040c10603040305900c940008800b40c00c299003803001640031588020801c01d0a021505021384140000c00e019411942c0203800b103003000308800c002100c0c180000301844401d4010b0001550589901c03034001c4032040c00030f005058000c5002c3c010a06000d03000400c1c1c14610081c034100c580e600801500a03090101304000420040c008651540d00c0d000d07450300c81402c070302c00c60009510800060800e045462020703403c1d641d00d01d600902c00d070040e0004481558002e0410901e212603850401e0350303543d810100390000c041d81110540c10810100f50b12910580000e008250034200811000e22480614141d030407001d170854101c10305e1142c200c496150424030b040550b422510900f009420a520b90415100310307030b008020300c40003c40070038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 15826238 1250 15824988 15825031
    0x4060302040e0a150209060f0a050d0c030504052a04020702030102070501052a09010905040c0302070501050103080a090806060d12090315020d0606030902090f10030b010f0303031401060e010305040606050603 91
    0x724110001131075065041c0000e400024078035010340071020345d201c07500081030313900b140c81141202c0405500c0c1d081000011242c050040041808980c101c860348141c540440c0f070301580c000303d52480e0010b000250741d080c20310028880690040c032812078040d03400740082000a4020300446208840c50008900410703103030140e59860750100c03400c4080c060410002000b059034400d10400030f031282900c020800000d80743d01107000340304070703071002d0280d501c0c02001100308103c0343d00414031840c1650b11a480b440e185c002140d12090165103017544000e907905260002803016001414000e00d900740507100c60760301d84451407100c01c6000380d075000741da0000f0388000e155034611904018290924080181e581d4680c0810030030000a8241007517102c407900052100700c4244001e034040c6a0142c044142565200124040d9000c03900045010078105554003000d80d0100420300d0480d017943d0f8410a1140e003003001500140001780003510307001c0c1c4400000c05d407500d4010007140101c0150340f9100c004c01d0800e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 15827344 1106 15826238 15826253
    0xe061303060b0109031b0311030c011706030312070306030218010302031902040e07060203030402040b041503080f040b0c03130605030705040b03060307050306090f0c01090b0301090b04060302040e0a 87
    0x2a00c1200c10103403182c80a40850384904008c0f2086800003040688031420751591500040c1d9421490860301c21501d0213642003140503007035a10b0591401c0c403014802204a0f10480401c0c0c50b058104114184610202c0f842c24074101410070b5541142e001035203c0011904060b00150103072918000d642e01e6030311991084614004031a2a01e59640c8081c0d229041100c090f4896450000c40c40340c941014003e11072503c040c8807455840b42d0640c0d03500600c5030000c3ca1200703d51081800003003030b8524850000d150100d042d500458540702c20f00001c1c558400c0b03942000040000c06c0c000c1c0000c5507000400c2d13074280c540100c1001d40b00c1e80e510340807a161243c0e6611044d070520404003840704a8401050100c4054010b100707a900c0c2c00c10510065801d030b101c521501d00c80740300c00c000412460341254403050300d100c4000e2020402c00d070369800140683d01e411143c218540c00038080c407010410712 = true := by decide +kernel

theorem cover : BRFrame.Cov 15647488 15827344 := by
  have h0 := BRFrame.cov_init 15647488
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15647488 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 15647488 ≤ n) (h2 : n < 15827344) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
