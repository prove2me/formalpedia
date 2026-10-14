-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:53:29.7113+00:00
-- url     : https://prove2.me/submissions/ab98003e-2ef9-4c99-a44c-4bc45355399d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 571402877 ≤ n < 571582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 571404127 1250 571402877 571402879
    0x9040513050c03010b150c03040b0432010c0605063c030114010501081b2101060c02010c021020030a02070e01120818060a020c010e01090e040215190c02 67
    0x2002d040c0b02409040c241c032640d10003581c1010a034603404210019030700060007841c1f0b503007046d2810aa21b030f42d12440f00e54403680c030030f9940d850302804804000c002031100700301c0040240c6189180140d900000b9015242c41c03440688910341c8c4800040030b90312110a8140c40c8015a05008080c05103408606131041c040e10f012084040c2490b420b07405400c3c1403181d81000c03c6c01001c0300c09240e10700740045417003d000070507090050602b9000380c912580c1c0d17100600b141027010549010100c42e100360b000b800c454144c0c046010030009095560160342c05c8156509805d406690700c1200f1800e1401c144c4106607401480020100d041c80c00c1000300001102508074182c1d1030f0309445040d5a170b00300e000c08854081c050120303150003e4896100003280000108206400d489150f010601c1140004149410084000002d42c00c400307440c0c030403076070721000030400c810090800103960750410319002021003004000078060200e81e40c000e26007200e041c041e610b01b42c400394251060030740f105000801440c5041003c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 571405377 1250 571404127 571404133
    0x30709030605150108160c0c08060402041a010e0d0804050d03050903010515060a030b0312040e0709060809120903030d05010f030b0903190c0c05030708251401140904051305 76
    0x2241c1d10940c84048607844110580d90041740e41c03a042d5000e03407840c034003c100310248030450310b01d14001190746101c0b00080c030281e8042c3c05149400d00500080d07070316244040305a150f148210101d184e804c000b401c0c448404c15210707403490001601e4203855034880c44c0c105560111035240c10408155000303005203c4428181c0080c8100d031520b492001000003403800303aa40c00242400001c800314469440b01585000c01411156101c1041d0b100142d5980140c01240a03108100204001c564001040c40004d1070b05141181061030880d040c02d07200c1000c1080103481c40d500007100140e59904200360340078281c240c2030400c29540d490740c00c03880c02840380c401102ea01c0c52b0103000a06003030002c07064402e800c0c8442c81c0c04042868000c4101c0350945241300489004210780c82c04101d685017081500c0103006014000d120051b44103503049081100319801150b071102086c410b2001900f406007a81c0d8403042800c00e2500b1042c0100d00b01c00b07502a9000700c5408c5031901042184499102d010145003078020310503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 571406627 1250 571405377 571405381
    0xc0901090b0703090317040909060f0b010c030203092e0c0302061018020f0d05041b0b0405150a021c0206071403240303120f15061c09020406080102030709030605 71
    0x1640d07101e8020380c04060040341c0004010400300d41d248410200d00742680003801e1801c4e40303880a070f0003142e11707251056884558815414200305281e1255941501090800c02801005541e000b580e074030420703031140d0082c4407401c00d00460614001c20000c03142070a100c40409800c1d0394000401c0780c03004200c15401445543c0101d50a40c1d0f8104020054a0b2038522440c1c20304184e00c00c00c40a54040a0001c030400d40c00c100c290f2048110b44603050040384903626840c3c1c882c6c1c844d040160004001d4000d0020b0300e50402c020403c580d00c280402001504408c41c50b80c0340d036003e90050782080d4546021100d90481c0707005101d820381c1c1c0440c1091160025443d9100c00c007140900000752404121100b01841c0196055407400e5041812080c601d40030003002c591408407118502c1e8241c1c0b805072b5620300c0c1c5a10071000c0c0801202400500b100e50081603c40134100031444c8888440204030201d66001203954404040a5444030703080031019012101c002e55072030034100d20040c000b000f544000e41300281b410b40 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 571407877 1250 571406627 571406639
    0x60f070503090a02062115030f0d051b011107080408060703020703020a14010621110904030801030b04030903060903170a06050a0308090d1b060f08011a130803030c090109 75
    0x81a40c0c0140c24140c010aa910840d500b4428254440c0c0c0b00414030300b44681c0c01031b440c8000e1640d4144a80e4294071003082210488043c9460300300c0060390701c10150030441000656592203415140390190411102d0070b80304554405900401803180030804c01e010000311041803015280042003203406040c1140d0580d542c52a080341280109940140140c00ca00145004a24200702c011850540340c030000504550f202c02c0d80203880070011943e122030075028000740c2408203440c44000f0302e800584c1e1244a0785070943d070081666030b05000c02000b4404100101e024148180b43e04030145500c80c204200940403401d01402c16850305e01e1403000c452a01d4001160718845000f4141160f00190103641d4180c11a030b1510380581100d12142e8010407112040400300702021004000f440501e201142c2079402c11000a1620030a1500c410500000c0c2c001000305a068265000c942407600c20344a4075021144050040807049602000c1c40e44808818441081c405000070505900240c03600201260703250 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 571409127 1250 571407877 571407887
    0x305010506090904030e06160506010801050615071a07111b1320040e0610030e0c010e040219020c0a0e090c2106010f05040506040b090105040f0e010905060f07 70
    0x40509500241c0c280000801d5003003100301150860b110342821207030a2000804105a6040100e1549142d156140200180142448500d001d0305c0054020704c52890301d90049104901d08054581040c4400100103050144102803076a8558446411120504021a005141c1c05540740a40c3c041c0c01408042d21103450f03a24905c110348136005d0700c0c2c602e0301070450400c90010180b4042c40d4071000881c00c2c0d006400780000c3e000f44007401c1d0f623442c20581801d000341440b1120180f031000000303152400000c07401d103510028000f0700c00c4009183c412203051620011a02030b005c1c00b4521041d036610341c40d0000110740c001c1015294141c003aa2985a140e03520319129480400c01c0d078512403190028000481d00d42042d0100283c849407102c4168030383c06410000381e1900c03409911215682d070a601d0140041e160500401e500850704071030900c003590203200083d90001d01881003a1089544a02c405601059074101030051044c05000f005103041a04082c1d4a44004540d0004001a0782c00014100c03401a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 571410377 1250 571409127 571409129
    0xa060914041b0503061f080a030c02040203071b11100c1505070e0901060509010806010f050d0902010306050301020c15060301050136061206060819030e040e0102070f030f030501 78
    0x2981030081207460316251074405070035000746180c50b100d0020000c01c4607102000341a009078002c211540c8100da9484070503518004941011803aa0051001e0f0804030b948078901c00406070301141c0060f40ca440701802561500e0980301c002c500484046a180d082c4030101402ea07001c040c0544500007486031000007254180f9890000500b4038688111803052507615512280d1710200307504019021450450010740c043e5026030200300001c1c40000c5814195a00c20307031803500f00e4401e090403001e44440d240068200d006121001040035501c14400c01568030a41040d0020000600219928a480001da40d1528400340000031100e00110210f102c80c01c2c144101c030b040b40c04414403541d0102c9260f148541204612a00740100700f03e08854030030903039092180400030040e0340c0804c0c50020484c0703812410790340c0e5a40614440d0700503440a03400060000012002103038585030087c0400030540008009224400c0310300d25940c4003264020130000b050417003452080c001d031154080780001400c1181541c02c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 571411627 1250 571410377 571410401
    0x2121320060f090a0305030c0f070e070f08090a1202250b040b070503090a0f080606030114011401170703020702010908010905070605070203150903220503060c131203080a0609 77
    0x1c100030540d210700303080c400707000c8690000b8109030f5403507039a4075058503541000d9035070ba80d5500082d221940c40c000c01c2101070010003146026032418038100c40060040013600035414140300c110300000340000014001456103651256441000c44030a03200296501c045000120041041c0a00c02d8401c1c181801980100c0b280d92149a1030903041c84c00000c1c094111140c1240d03184018460b0b140127656100000c0003400c001c40022080901d096103040ca0500040c2034030b8002d91501c100c01c001c8e8100c00c005181502e1400b0001a8040200c0b0012101c041c403c0c0c603002207800d040301c144100681e05070002c000d224001d0765003061f46510b9680c0c0e5802c80340a810024525406284e08111450080e805031154074001010f642c40c0410301207081910410032148401503070000280340504180203c11007000d80f0300c4000441c0c0850802d4042039a4890242074580100741c0420005074480021398064080c118183c2e8810140c00d051078003401c035000135140c800e00d490030140c0110308040c0e988916403686403 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 571412877 1250 571411627 571411639
    0xf0d0201090c09090830070806090f060102031b010e06090d170606071b1a0a021b1f121a180402060c1213060e0a0e0a02121320 56
    0x403504403003100400c0010012a0f582005005402d0030080c03018070f491b8101915405903040034801080344804000c024014403d210480c000c1c0086501c40303003440e642c0104d015258031046c1d1038550041c0d2650088030340b5904049220395528500b0807040d040803281015200884005484104030f85490703805281a46000400f6007500040300702023054215040740014098901c0c16040303407544541041010080801d0526041d42004070702d4a2581e0000b00c41c404490175400c015445400039200d0317500111881e45608800b890301807660355070310390350010100000d40300842988418082e1a005040d0000e0640b1880c0010290388842c50004c1000c4003039000384070380070000c82c5900006884c0000342050340c11000a02005282000400c00d40c0d001e805490400340d19070305d80c1c07101014400d03580c1d003052080005840e000040e40d00d854500304103640b6400702202c000ea0706c80b001074000707021307500d00410750740c211105010a0913651000c007010180100d82480451183c1150b82d00c0659004030001c0d0051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 571414127 1250 571412877 571412879
    0x513051507120e150c040803040b2a0a1103030a0504090203040303090606270204140603040501020702041b0f0201050108102003010e01170106080606011115090f0d0201090c 76
    0x14441814a5500c0345042c00c00d00024184600d40d40129a62000b21004551080c511404002d0184540e070780d02800e00042c007072400303040c022402d449005601c80c00084a0000c101c1366205030002041158034015494080340c00310344d19506580d2103c02000549500000f12501100c5003004021074001c010741c0c0d103a0915203440d210f413441c002d6100410507010180e41d10001c0c000076010340121001050041200071542211206110f03143c0441c10006102034030410080140400200581d208004103c03221074803a681e40c14800c0c068881d8880081d8064640ac45042140c0a680c060003281c00180d500d1440c0400c035980143c1c00c8600070f0145505951044401c4800007066400003415101e03403d0607014541c01c22148900d20790400e0704100c2480d4401d40c0144032128400c008141a10b64420003802558a0301d00710329100e40000d0400c504000c2c005003040341e01d030010403d2660320410f894944102d45007040e0340d1a1034500c0800000d442e0b010f5440c2c1a0016441400741e40a40e5800010001c003031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 571415377 1250 571414127 571414153
    0x50102120f220312090309231f1206030b1605120402120a1e050c0306070f03200a12150311040e1203090102070b010522091112010e01051305 62
    0xb01030100c01201003004681200c8140d14030340c043c10400500c05c0d100c101c0c000d4140126100748024940028200895100c0046c0c06687d41c0c8001003034400180514150040410100312902c5145031003c403c0a0304141c000020469128842403140600d03003000c0000000c158000c5945124030200000100c107004007007005850714201c2d580046000e201101c90b8054a50346046900681a10345035507080601001d03020701c041440354441480048003d0521850b001c030014041240510b03800d010907035541f00424883c620510b078440d1001c03254685a40303030607040c00d00400c43c0e00c003030400c2071506041500c0040c0803200c018110095035071094201c0d4500488805101c01054000d100c1d00785441200f034510740c0a44c03048000c5000b00500d80002da9106910700f410100d804060b80854020305002c401c840950711402c02d84001e90079600d001050f200f5140c2019649000040c0c2805d03803060310520b45120094055000c0150714541c00c000f8003180d55000e4002100a1422001404941201c401c0c5006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 571416627 1250 571415377 571415431
    0x30615032103020d060f03051912080907270608070b090105090a03121e050a080a020d060803040f0f0b03130b0405071e030302300a02120304050102120f 67
    0xa940e107545801401c0039400c2c50200700351746003544428a20510f44005106004051108800d60909170050007131080269030790703041c01c0c25614403d5081280403008500c0c021310900c541d40042c05d04a4840300b84061004684002440301d445a414091500d03d001072203034404103186003180c5d40b24a103d41010850302c0199899441040344550014141c840403000801040010022141c50380d24a020031581c0308418060707000203550502400700501100c8101070344020300c01d9004203609000b58950710b040b00b00b0009440c0740e4000320598000401d010130181d03c60b0b10550102e802c07400348010141d41e03030210301200c0c0c801540d071304007001028001c0501159207100000d4220384244105d4a5803590b512103d68031000003034042c021000c08010800070b1550400c00c0f11003030010003a1410000355030005948040d1811664401c0c003140118030807029034024446403c92100811481c0ea6918180c40d04034000e61112100402000040f0b0207d001400400c8010780b149041410700e5140800251440345 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 571417877 1250 571416627 571416683
    0x605070204060f060206240d080a03020706060b0903070e15060306150c01090320070e150d080415090b030a020f04120b0402040b5503061503 62
    0x41c10640364840010030740701400c1240028401907004d0000c500304101502081415803424044100e403c9a00308001d40d01c015910204a0344110410f030f0310701e1121819406805401c50250426140200001d1041581707002019451822800c0d164900e840c1c0541d10100701c016618440380d14559200340f90141803510081d40c00400041240b42499081804081180d108201420311a511200c001003016041328203011005882e000703100c0500305014615581d44902c0c0304030f407186820f03000421541c2c1c0c1c42a54503400000b015010004031780913400d051926501a12501a03040750048c810540c0502c2180c040064840c00c1a0451654840122400194014040031402c0700010400021002144014501464481e0398400c90b41c0c0361030b004000c22104560000c41c0580c0c018000a0808114001120200684c81c2e00980512074000000f840706108140e02004d102d0105200340c03204d03001d290006048900c544002d100c0060100c808406480203840014a9401c2026000c1110860450188 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 571419127 1250 571417877 571417879
    0xc090e0c090601090b040b0a030b0a05030a03080a0b0a060503010e09010204061202090a050d0b100b1c1a0901030308010e2203031806060f060212091f0c06060306020a0e040606020706050702 83
    0x82c40c10764954840b200c1591185c2c7c401d41c01d20781c001804184c0f840c0c05000b0b1044070070040b00c52422072880d00000c039446401840000b0100304540c3d001a01801403603000580700c0b50050104203840d511140050290317802809590000c014100000e14500414000c032801c0d541c195580c90108000d01c0c00d90400783d08107950385680300d8210f400115994031903014604440e030050640c00d010f81480c07011300c00c4840181c2c101640c0850100802144558018009030310340a08200010f6400041e01e40f6802c15000d08004551140e562800081855030000c0386d18103840c200c02600c0550303120900c1101c1e4078079000700c01c0482064145507100100f4025441850300380005020941c1405013907a5580407261503810100e0405058072051050035810000c0c14940032800903440e11380595100000c48088a164150b90010400410002154440c01a000005038030003401e00c030480d20f0b403138080041d4000340741060001d5170782c3c440543d091429014100c1200c1141d00900a00b904010080b40c880c0c1c407800b420b03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 571420377 1250 571419127 571419137
    0x4060212030705070615051002012d02041503050717090c3d0e03070b03040b06030a080703020d030b091306020307110a05010e15042d0506070c0c090e0c090601 70
    0x1082c003081d0b05010341141e206e442c001d40c0c4010b9040c082000800172313008860100b160314111070040064040b01a00c19030900030904c02405078113400000e0b000e44500d80095071145404442c2105442e0181c0145008070159159595141e40c01c249900e2201e0080b56000304650241c00c4600389410411503070070710412641300d13210350581c2505042d4019981007202d0002c0d01455a880c400f4a5481502c0c00a100c0c0f084000c0e091651510407181d8075801f0290020b4107003166000894100d6030100400754038642d00c0910315445140ba424060344131101d0403111400f05e1306001c6660180e2610300d0150f4031440e08402c1c40c0300c0c01151602c0d04c03c0207400c002d104005001c0c1c3c002d091980c040e010031010b0103042c85500086203030f040c480394440c10815001c0e44810409640024440020b50400c0d100c2d01e41c006050040302c00c41002c0e040780180504d4500080c01d03d001d07548c01d1005117a80000003800701e5001c1d04507400c0241d03a941110003100c0c41c00d600d00300c1941005000561601d41800c4003a0052014584 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 571421627 1250 571420377 571420387
    0x201030f0f090c15020d140f040807030c08010c081909062019030209100f180905100b0c1b0d020402030732030c0d29040f0204060212030705 62
    0x440464040182c241c0b0b003200040010000104d0449820400c0d043c00e101503c060000000007810038081c01604480001001c9400728800b20f041c8103490040070620200c2c0c16803a03a0342044800303650300d40038a8180d542052107410940d406112114000c00d41c0c03030450301055089403040380042c1600c510884a00e5228404941c00851000040c000701c80e4041806940307062410030240490408130b85130307007410700502107003000756280f403055104112941082800c140803600203e0b05203071454140100708102e00808501960a90300c203e2041440c2052060b41355100c82c020b1810303000d2041704201903403000d0003405190b40c000480c0000d07030030003600002090034141d0004080c1d0300121880e4000505440c6284620324a5034040714909001c1003c11440021045035182d05120042180d90b00040008099403040c030140d110304c00100c54406000348848441a085c0d24821040311441c2c426420103510740c0003c0c07564803c072130403a030300c0e90020003001c0454090fa9945400042c1080240541400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 571422877 1250 571421627 571421651
    0x20a0902031801050a06050a060f0207080105040804030525050f0112020f0307090b03040c030611071403040f061409010c021c05010516031b030f090c03060903141201030201030f 78
    0x141d40030b154007010350072207409800c004900b141c0c40100485561800d00004000c4c2d03480340d40c0c5d40c1007554000e24200003452510b800681c0b4150342603114241c250700e81000c01050001081c0130b081500d1103030040c3d91143e011a03800c00e580c800d04084a01101c1c1c941001080703c0e20340540e40e25070301e41c4181890701d0610051800c0200300c2c0c0204100d9501c18000008000c901d590011200e03001d84180c081c0c980c11401c240e150402c0784842400001d042c80e80d90001409002d500005450301641d0001d50540640c1c485100c181d100c1d00144540e10100300366440101d41c4602600b225a02d04003d41e01403400e10403240c00456407416800c0080c0e812004a10a0f046c5020030040c82c11031190040e0000306d410b080002e0b44a0f4401c80f40c81c411420149001e1803100088844040148158038518001c110743d40110500310040c03007203400041100260040010070408030350001025103010340c1320031220b0710903450104014841c900d80300c007551015000520040d03010741d10060100305802c0b40054410300402d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 571424127 1250 571422877 571422881
    0x70909021303060213300602090a05030f1e070605090402090105040b120702100b09040b04170d2f03040b0a020717070506090304063c2303040b0a0207020a09 69
    0x10780511a0401000e0302403280f007015802020194102090306c1c2c00075000007005508648000d00024692500040c1b0408995101139140003d4540242a21803014406903c0d580d07070603683c1d0307204030800420a034102c01c0304008075580e011116540c840900c0c244190b402c11000750b05c0786a015050150a00000c25026440720142440070b08d803184840013414427940203490500450282d03814107042c200001d001780c4440d04040d8005504c8661441d0780d840c1c42c0b038044000c003034080b13028180705000f027045003607980c05400018080f0a90b440092640b0010060000b900d20024502d443d00001040841c000035102c0b0302e156407240e00c019006061400760369034411007048010f590300700c041011412100303001d01403041581050f202d02c000c518243c84d01c03001800c1005a49042d5000c45c0328034245015107407c200f01c0000c041c2c024040102c1c40c030745007403002d00036032200081d0340c0c4091140c8032051400d1403030008680c0215007090341124140e40e0b65030803001030b61203040120307040a4002d4000038004458 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 571425377 1250 571424127 571424137
    0x5010f12022b05060303090a05101e030614030a0b041209051008010e0601110712050f101b020a03051219110a1103070f1b081b10080709090213030602 66
    0x44411582c0034241140640e030024000511075001001296403555512410104442c5d064544119122440c402a41d2030100f00b504861191b410340e00e9003420b0355055100d5000e6400750002103400040c1031007403581c0c5074440c50008110952040200300807e008090b503682d240028078042e4501c0792102c0104501250807080e02012074295070051108040c1c8001e990382c490780030701c7c00c0b0398181c0207440703105d03540e140f00d03c110084c170144102654107100c8180030728010707041750f101114000e84010700c0c800001c1c5282c103004911031490301e101c441860b2010411400403601a45c82c1030920062042424100e1400382503c007070b400c4000e40a8a903014540034811900000c80c2e40c094441010110107004d408510500702e031075803c00c0102c100080d48840300d00c1181a00020480801e410701c040d501424849600884004d1040c00640001000c030940c8144c407a00c003d9410154008110b20141d070000710079500140880c3c0018018450b50010350b000d8903503400101040300c0d4845d665140c2804983c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 571426627 1250 571425377 571425427
    0x926070b1201090f181104110f0a030e0a112e0e100512010902070f0b0a0c0e0402070209131b17070e070804170d050f070e0a05010f1202 60
    0x1c1903004000c1c0c51001e00c01d80100855940f024031001208121402d0b402c513000300000d0983c00403071185c90054a613540b0808140c1d44007083d03075540b286465862009500610340c24000241007000d800d0b0408004116803010b039500c40741350340c00009042e0400290411a00e110480c0100f4054444188020b9090f001d01e580400c0d11200001c0b504c41e010300112151000d1400e0501c48200802d4004042510711036045800c0b020005032901c5d1507180590b403000300041c000d030440d41c256042c44031444131a4030a488c070980c0d58480300c10b640195000d0009902074804041e500c0201000081c00800c0b10029841955110701900701c1c100d4440d0200b0a14542c103500075030040e01501d2030300a041d00c000c02a240103425400101d00b5589060701c001131001000410051480c130800c1c40c0700d0943c0b61124180d4a070a440301405024511341810a0092000100c0340d560029805540566203424154100720aa80040c1d54004544250270001e0754420840603148813480e60800c200360040092103840003020348 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 571427877 1250 571426627 571426657
    0x121080d05090d05040f09051f0b03090d080c07020409020f09240a0f05062218051501051801020a050a03050c0d1b020f0607021e040c0926070b 63
    0x802d10701051400200096580604c0000c00c0180181c202440d00701c8200c1d020f01c000400d80760346d80070b8440284c0c0c12a10044440c0141d6000c0442c6080e0038201851255a00408580d0f452410500488849509a80e600e90321501003010402506043c1c0001c43c4450000c3e00c5011034040303000c0801c0c0c681c201220710718070500070804a4480c00300c803200154003044c0203c60340016142810b080d0301e46210b5030701c5000d00c034040c00104401520300036501c004180030340c030b41503a0390035039a13110b80c10840782480e0a4000003071030040003c5824204103d8400c030000181d4a60b4101485000e01012140d1690755850640c45401301000006608014504d003440c460343d41c0340e84a620115001d0300e080700290044082c065030781c0000c0c07202c03400d503010703100034a4045800302c400481c0d40020410910030000043e40003030301d1030041d0320a920118000d141c41d80080e0341c100707c21001900c08440307070340550203120005100016950549100341c001851380c49000000e445146640d403a02862a503c45000c0c602d0703062b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 571429127 1250 571427877 571427881
    0x50f011e232422150f030309050907050c06010315020d02040b220e0606090604150c2303030f0604020405060406030e061501050703200304060c02040c0e0105030121080d05 75
    0x80345510b02480940d0540c0c01c2510110349805100c008040c00300351600076035803600308004a81e415440c500085c001d0110300c03e503090b241c0c100201a03600714084c6500544129004c91001480340c0c04894141036414040c1035981d00356079402c0140c0440d5030901c4c03550b640038011010412068070042000704000820180c0e02d03900000d0f80302007012500902a1900096442089070014400c00305c0d6200034200d515560742c2075407000045281c010b94100c2000d000036440001c501d036800c210013403403ca0107040c52150240e070851104924014803100303460745410a0003c5001100640b2020760803400c002c00150a007501c0d0808104d06030090b500c4080000e88034044080d03100000c1c049942c000014460003900605a000003800d035104040b002001c2004600071950782103034000700c0d050100c031141c5c25203655a0351fa1000500400009500f40e2082c0e2070600c1c00c3c1d13a800e015031855450200180c4400b03041d607107001401142c001d401c60850181101c010700746000103007084001d003404c0d01502c50001303c81c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 571430377 1250 571429127 571429171
    0x1b01060504180f03140a0806031203070f0503040f020405040c0e09010b01140702010923090f0601090b0a030b100306180501060e0607140304060c050f011e23 69
    0x2585260340494040d51500040d20402c8020b14510440c983d00300c0404045001c1a10341215008011046082803d802040c80d400c0698850911801410110b044901902d40310040205500c001d4a850000c94803801c09100038a005602030369019014a14003182d01c0c2c0240c0201d0240d800840b000c840e454500942401480c01c0b20503d603420000c0070008000e418800c000192510b142c0000c0b54038160307404200e20045a1154200c240605054411552004084000c5022003500e600003203109151060000c0c16058180f04180d04c1034405950304007800d4607107581c1d1205a405907002071f041680303405002003141c5655420420220780d5540008525260031303110380c480c0e4801c050782003a130707803c248c0104400307503100c0400401c0700b004030b4880b07546010a1400d034980c0d040c41101a8950700010500140042e0071a44206404d400380c02034400525100c4045422184404044d410700368070075842c120010180d600250003007031b0b00c01d50140040ea0047d80690100400c4480e44001e2000c83c201c4006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 571431627 1250 571430377 571430381
    0x10e220e0d0f02030c060a050612370b1b0d051302040b01030e0c15130b031608010e010603020d022a0f0102090901030f080714030408060112080d0c0210021b01 70
    0x204030610196090074001703583c0d591130f8030026180280440d11040402c0e0541d807403080d40030080302c0000844004030b00304040c002081c003103c00500261002c003044003d042c8071140c2c60303083d050b0f4044400e400d0ba44c3c5110404d6401d800541c20115030020030721141a1100c82485011301035104691805d0504e80c03288100710a854a01c8210b038101400c15074501404400010071905000b0200c810001003400030324000001d0184803941010140100c2c40082c150540c6001140100202c2113115406180c0840945850b03501b0701c03460f04142d000000410049200f5406046005021a005842c0c440540c100c09038200b601c03a1040d44890025a180f51401420440100c0c0114544001d5007411200d80005550100510010b004002480300c000208100101250480399004009100614522285035a01c1c4c0080c003800307009106070707000812180c4d0f022800d4a01d5a6105e5226850b1002c0d90014401401551500038150700c0b50070000700450002d030025003050940440510346282c0000030082c2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 571432877 1250 571431627 571431647
    0x9011a0d0c0c05030a0c05191109040201230331030c051005091608011505060906190507150501050d0206090a1502210403030903030809030403060203010b04090c020c010e220e0d 78
    0x1400c004251031800000e0000d602c60003401c4088442982507035071800161140c800c0e2141c214140e407280c4ec80d5103040c00505c00614007510301584ca903083d81781da62600c2a4203043c956000c84402404074040e0001a1150100219151050003a5102c03e450b4a00001c1520b106403100750080e040b503e03010803007403011100300000b400700b80c0091002000c0c080c3c9190a1001a000312401000d00107401c1e24161502000c0782c0ba441c1c00340144921200c002c603c014503e80000c8411503405480980d040c4107041680911410b03101c00401c0110080d43c994200f00300c0b0b41c44861303c3c3d6007200c640b6000050b0400318084691300264583c01070945000ea4150003071045032001c3e440759500c44140418004694003580c10300030740380c0c1401c0003012600d410207080c1c039500450b88000c104e68000400861800d142101801c1160f0440c2c0e800c0c023605201480598440c0d0321501d00031300160302ea07030742c20400d40746c101c8280b07007000c50000f40088811100348681c025140600b1002035960302c0301541c0b03190241c2c04001e000c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 571434127 1250 571432877 571432903
    0x807140703020f010c0606170307212a0b0f070f03180308072c0109060e0d151e0b15070309030b0601110a03030b09011a0d0c0c05030a0c05 61
    0x49000c90031640001c103012036100c0d045042001248441c0200002c580c401400f0348007090400e50000d00364140a540d0750710081303003200c800141007502c0c82c45038a0052200400d2395075850f00c0d102d107040e400c0441000d159040c1c08401711203a058440e4040f40c5c5a903809809500011031403002450440ba000c0c0c1a44070065801e82010701d80440c40301e000d64146150400d183d89481c1080e1151603110085070240003110240002c1c00c060391841c101c050071383c0c0d98644100c1081c0c0301e60300742560715503090343c102140502c5550004854141100014050004209043c0090100003240c030066202810741219159a02d0401c0c0c0c0d0703d01d0814690301e000e50f02038280c910a01c84092a01041e9076000b42000c0b480e100c0240114000c0e0040b918503030207010038a284007103c0c02102c1c41d00d00340c8e0600070040c214050540b07000d80a03c4c4004a1000301c100300d07a0b200949103105030791425111311229801400780c401550304110050490500241d01400200020095580e69a08800444c1020390800300c00104003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 571435377 1250 571434127 571434133
    0x3041104230c120f06030f06070c0308070806031b06040f031112030306010210051b0313030306090b0315040f080f1308031327230c0a051c02090904080714 68
    0x400c00220400030100c4c1d01601c000d110407003640340c8030042443c00c3c42d4840c107180d49004580420a640350311504841e01c2c0c1d80295207002c0702da141c40324255100e81c8150f450940582040c59030404042d0314030700e802d00c2400e015000313030300d895034492407a1182d841031341080312410102c04c01c01c101454800f0400c1d05080803540a507103981400c1001070b503206510038101ca650341c1c9076400100404000c6410040c2e0b500d1000410740d581c54039010403203c00c1c810f1102280428545400401c8a507020302c00c0d9040c452019000b0705030844086040d2681a0b001481114288900031040b00029041d101800d1841016020640ca51080c0021803085a060360094619a4014016007680d01038002c03460f411500360000c400c40c1098405a42c00700407040703080c26601242807108420094824122251880c2241480c00c069511a6000119544036907080d0740c0c0099418080320358100d50300c490582c8131004d0244014508500c5002281c5003070000c8038242e0b180c00b8046015400d0240c00c17800c590810040e2806 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 571436627 1250 571435377 571435387
    0x111030a050c150c160c03020a060509191a0705030d0c05091305070c06050618040308090f0a0c0e1018060f21120311030f1506040b03070503041104230c 67
    0x1c1c8001800b0344d440c0d135a50070100710114001e1142507441b40f000303550050184a0215120301e0042d0407984030031010b41c0144c409a680400411200c0d14030025280b0351102141410904c4041d40b4460b00b05074000e44060104125410301001c492040d5401e488130b5071a526280d408800401c0a0b00b0f19403114044464100ba0820500a40c01b000703030683c10754407600000d05919800042000c1507078a1014080004170001400141500301d182c80b0b1040c00130008450001c0109035206484960300304004103098080c050510201102d445e0640c0c0c40a807040c01845c001c0d50780e54844001e55083c5900503582e42c0d880c00280406c5183c2414033014140c42406100103223111010300d524400d0f8032a000d441200c80d0aa0a103100d031198101d0fa1406044070a01da44900300411944000c45042d41c8001c2104000741003440ca034144a420782702282c01e01c144050850745e4407401911076600c000e108491580f40f11145241641e154402c10381980500c0790b849540500c41c2030241180d59029214080326082404 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 571437877 1250 571436627 571436641
    0xf100c0e041d2419020409091407050d170a031103040f0539040213080c030708010b0603012309070807030605010203190c080f31050d0308060111030a050c15 69
    0x3c20030303007250813595405074807081200c0e1070000303028603080181d019084c08034280c14004040e509101d00c074032100c01d0310501d0340e9960803c020520800c50007480f202034100c6038003c40500d88080c1c11120b04604001c03a0078081048529240d5004480456207140c0c0170801409000007044681e1148071000f60300074101d40c550321b0100d402510307000f200401a0400411260f651100e4058a400c90711050300d84007025122038003103845004036056280248500c0c42c0000d01d8141c1402900c20f40c0501901c803624603401e041e0560031464404035104460700d511800c401d640cad1034400509100761441c0c1e9441d0524248010300405803840e61780058115803003400495184010080d11f5204003400e401c05810b140440d20b1300240502821074560100c841c042030000b1580340b4048501c00e400c47e00b0400309420740b868400c0d078201c80d005004903600b10320301108040000b0b009200d40c64008074141481074140103544a040d180d0b034007210400c400501c002c41c6203a200f01c1d041040849a20ba0625a41100d180401c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 571439127 1250 571437877 571437943
    0x60f07180e070905030106140301180308060603101d0403030b032109131104050102120c06010b07081303111809150408120108060f01080f100c0e041d 66
    0x30003050780281c01c4501007118030303009000600007080043c0080c08103030340d1442081c41c0481d2480800380071b54200328080070400c40300150705601c2689602c400079141c684509021711030700b0042c500c041c1560440303070102e01003400d000800b02c80703c0b414a81e00180d00d411310f801003d484060040e14000c2d404520389299100300023103922582108012483d40724a050700c001a0718403410a620040d43d0316015072520710300b0003540100141d075420303005c59074500c0300400340d1a42d40c481c3d034905c1c1c1c003e50000b0006101e0a800940184107a41c0280c811508104c03400107100c40c0744240364800c503110b2191803820b02d9070742404002111481d12004100399585080503a1341d40b5009000391015849401c00d000500b0007a0006c03d44a0f540345050346c040c0d2039a100c11615507203520907030781d445103018040300000b80d500c0f00185200245e40d110300078003403040c10b04032904080c0c19070900000174418034480729842504c403842480143d9040b0400e08a112440061540c20071180040508241c2c10000503d04519148 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 571440377 1250 571439127 571439129
    0x60203270c09220609060b060f0405010e0d080d0506030f031216020708060405071e08030702091009090302060105100e01020601062111190305090a080c100e060f0718 73
    0x5071102101070742e074007200044240000d010540c01c010040c0d41c031000d21015a10610549214401c10400d07c0702450800126008483c01881d800808010601249d44214190403c3c2e19000d424524802c00a80e524a559040000c040031303e40da03100c0801020b0b00c0c0030440c1d0405c0d08041740c0503502e0302c20442404111100c0080c200d40d0401d0203110034040b480e200304603c800500703403030098509908240c501706803101000d10590071500c0c4071422401c0c4900c642151102100c1582000754076040e603079400d0001c040300060584000070601c00c0c00280c2c650481c004c0307040051090380907040030340c1010100a6048000d0745103104000e00441c07003600998002807418152050303400d003040c3c4104d44490031644d40009810800c0c0a900f010303240285100b462014016142c1800d2034004071641140080b02219421501c40000c3d5202445850100710700400030009140340344103071038008004042020580c0c00422941c03c00d54403000c204810289011005e07500100c00c0d00e844c03500e201c0c084401100311541 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 571441627 1250 571440377 571440379
    0x2040b0103021e0715020c0f06060a060906030e0f010f0c090b03040503070f050a020418020906121c09082e1103060108130b0c0d15080318150304060203270c 69
    0x40001c030401484005e0840006140c0c075100e0540d5551504030300a5112049003413a00d42500c91500480c125181003100c0c07000f960600e58a444170945441d20480180040010000880c000c941a044141100703002d800102180d000c4041541003e54500804204d482c0c3e001c0c04c2001c4007402408001640441100c2809401c1301c0904048030142c00c0007400c064505100947c0249000200506003401d540c150ba40240201c44c184020fa0f80c0c1d200b03210601c401100c42c2c0b445038108860080384403a949202801d44150351611425207078841141c68900f05550725482443e03402074461015803407112070410040300050100f40302c41010141074060038000030746140e05020300c41c40041d40d05480b64011307042080d00210344085605004405030708aa000d841c0b040d000c80e0501401800401c04800034408a0301d606d401540b03002007100e04817040b005000041e65006182c860390114262126000e14010381c0210b10043c0d803801c00b0003074504030400b281101e2030b10444441d0b50340c540301e001203005580b00750 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 571442877 1250 571441627 571441687
    0x191d010e060d02030112150203190e030409091406010803070b1612021206011d0a0308160b09060a140106051c0b0301020f030402040c1e2a0f02040b010302 68
    0x403803140040c6590040400b0440054030110001071581403400040c60254003a03034007004c24050141f0860240d11040b142c1210648000001406110071548402c0ba0500810281c13410603403074026500544034090415108503400301106401c40c1401d0081d54010500c2d42d0085140c8021541c039200440b90003440700c010301d0389800c20702c880c43e4010121a111001c140d641159682941c08a20703101e4401660b11500145c000c4961100f0740305c0c020320829100384010404c04001d85540d441c4a10b90b8440d590b00b84c0160401240781e00080d10300c04429001e2403c1c1303c0680490726001c031090040741c0c49500b20540502c0e80400401445801c803013100c8200465028180180c1c6440c0f190ba400345c021070382829050740c40090b12201021040003e540607602c220b500b40070040c1aa042250300b99400f51312011106128401c0206c1540903401a05010b18100b8491039080711284000c0480c03c440042510761180c014459411850680300e03568203a2000d007030442c20404bd00d1500050303801501b443d0b1450075 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 571444127 1250 571442877 571442897
    0x3040c08061b031005040608010c030b0a0f05040518161e06120b040e07080d1101061a1303061107020103050a1a0d1502031003051c0804020609011e0302191d01 70
    0x41468030804d8040c11020b081400000c2d41c0b00300d90360092121030200e81c0001c0c50038442c1041c40c41c2c161445002c42e915240680300450400707003007000400002d40203e6141403152040b000d440700500003070320b00150107003000740280e188c40e07510841d20304800b40c400141000c0c1d810500502e5005100407001505040d00020401c0741e950100d0300030600c0c00c8000c4002c3c402c0b03400008100000140008905465a840c0e4168420f46d0885d6401d03184240104079400c0c0b4881b400b080c0851014002c1d010648294024222696682c0c403180c1c100d86003452482c0d03528100080c008150358241c01501d80020301c0750070400c0f200b0b0881d0040031442c070040001740c0c40f54403200d0030403040c4100001075080b444403000c000c5580b800d2980d146640201e007480200d0b8140541401e884091003c14a8014104803071344440e07100f81d4441c1e0801503a41d00c488030780d505100c03d0a0602500710f01511003078424402d2031b2801a5a40b01954a00a003114101d8502c810004024030b50305081d64400c00d02032140c0c0c000e0030031070701007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 571445377 1250 571444127 571444141
    0x304080315031e01060501030b0607020a06031e020f0304060e030c1f0e0f0607020f06010305060105010c0f050303070f030e0c0303160302071206060f060507030c23010f0203040c08061b03 82
    0x1014505090f0049940008144201c103a03042d4000300403901c09880411500c007010003400420b0244071401780d4040602c00f401c1001c94000d0300864aa681803051485042c0a82218803049070421944000c0034540403003000304200341489030403001c0e40c00d103000b142460000e03000d07039550740c82080c260948045c0d8604a12000d01054100c0d1140203104030a44075282a5020516a505030403035604005100300004a07000c0c403001702c0c8440c1640d81110142602d41e007807100655000305200b40880e00d910002149130081681072005e140150340342e0790b4aa00355040d0110013800d0303c01c01c1d0315a1825400c0045504030994000040303c50803050400500c1c40d164907402c040e42020140d0b444100d0b030310121003071941000210750101d011742d50b510020b07000e1a034607400d04494600907040000c0100b9174010401011503444a404014280ba09412200000421203641d0948420308a58041351790044244020091303002c1d1481c000d0480c90009000a19010490030680141e100346242c5840e000030104141e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 571446627 1250 571445377 571445383
    0xf050117030a2003070b1f082512050309090f060609150904050124020c280302031b031c02060f0a0e060412270618030204090b010509010605030408031503 68
    0x54083d82d1010740f516030001d8103003400210400c40c0c40d606c1511100d24101d8103042403000500545202e007004260f4150322850748095084188091511303002820400514180000203074102284108041c0d512000c80b4070611641c0ea0015140c1513098280c0010401c0c06c1e103d00f4113980d500f030340450342c42440d00000d0100d4007403413084904080e0080e04080002c1060f00c0b41c0302039880105c030840c46503000074031031440480e1901010011b041d4000404002c0d03048203800c0341e440312040510903c2400c212580ca9000903e04881a103480003580c103d241d00c4083c40c54144004e050b4028080c00d0410445243d54000352a880c0003400907890190a03004240681c940c1d82c00342100321000c1084a11509050a141e982d0040b50041e14001650030b800c2811040e02900701d10004c10020711400f0329950800500751b0b0b0b1a0740e40d8101001c6072401000c0040560f5950003407010b0b0034010050262594100700c140043c94005820480602c8000c005000000d103620049031342c00b1201c40882c048182003180080d003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 571447877 1250 571446627 571446677
    0x30207060b090a0603171303030806031606020606010311030121140f0303101d0106030f15031406070c0308060409020109030203010e1c091208031f03060f050117030a 73
    0x90031524800801100d08410f80c84041640d008031482e06c0a26440c03c15200c007032103403030600c80d4010100700007000081d0040d500c01c1d0308004020143d410404030785001d080740c0003803603000d44016448001800543d50301486100c584940072200207140d581000070958840191450520321160043d5102040c01294101180d600801805481c03103011182403a5640b03410503640c200100b110814005231900211781140c0005014107075070110b50703281440a800502e440040c00c0b44403911040c1c0d11001507609a981000307188a402c1407031052506a040350301c0c0c150700800b40001d2000c807101d03020100e90002241a84844103c82c00300d40440d183c40100c41d01d075090360000f500743d800c15844009605000c03400702e141140000460b00700010f21001124001c14610424440300d1750701070040003242000c4015036110600001000c40034481301d20354102042d20780d02c280d440d580da42c0c0f44c1d9805c54030b0318000c0d00d00600450b01300d04503502c0d0940440391203101300384000d01070005801c00a81000c04003800c0031 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 571449127 1250 571447877 571447879
    0x160b0f03060904030c020d0b060f040c0c0b071107031505010b0c101107060c030f0e190b0a1808040e07020105150607050a02090a06081c0c120c0503030a140a0b01020d030207060b 78
    0x40300c0b1f04070526200081100c269035151150076618070010040c1450b00ca881414592551900d00424042c0c0300c801004034058030100030803240700d40f074808031001004104020340c8180c1c4041801040c805d500011108103801002c1e07144810084200710703d5000420740c030410307a55000042d007000c1c44054441c0611800b08000e0100341082c01403089250181d000001850224000344035516488403190f0322425402544d550340c0d20703800c0206000c1100060328950102030003100089101c00d00080c9002d500003103400f00e4003154000b8052060000b180d07800b03900b01001d80024809403c2002102d07500700b800b602506c0c09160007042c1d940500034104036081c0c243d500685200214100700c0c010001a08050060050034443c0c0d40031018400701c0350000c9904e82d00e06540d04c0c8810b82d00303036641c801c2d814102071074001000502c403204001300300240015030280e00132520000340c110000e41c5240c0e081030010002d004d62844c10b4081e403034030391700814014140022850300580d00c40c8185020401800384130071702 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 571450377 1250 571449127 571449139
    0x10518070b1315030f1d061b04090f02090a0f030803180c04091b120c0902090a032109080c28030f0602130b18090c0d020c160b0f03060904030c02 64
    0x400d4070b65015801003c1e03104022105111115686003002c419801d50351b0312161641c01400007420020072803070020440e000802c250b40c0340603561100c0d402514441809640595030016580c02c080c913181c1c0181009100f003811442c1034915684618104e40001411019400ba24100d0000d100100b4042060740c9907008000704400c1400303040104401c00400c201c4001f1000503d0082034200c1102c01d0b0b807081ca503100c00100c00750350074148010041c2d0000310b101d42c4c00280010010001540382004080d52450070746000d18110001d80e03008008207180e80c001030b03060b0016103410505032900e4113034000c038001c7ca800c4c0030040b06908801411004003a403015203034407159428041044840d40007000d04103208900c101c0301c65159011400140b080070803800208440031100e03101c0d82811001d281c0c3c03241b91404910b0038003602012642c00c1c0c1e03011000304241c0f50040111100c0c070024a03402000a0088030309520f041c4054080e072080d4a01c00601018802c6c00417200040405100b462122882c40d400303020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 571451627 1250 571450377 571450409
    0xa05030a0302060103150209060d0f09050307060207051516081f0803070614090a0f0206070204060e0601021216020904080904110a02010516091e03050f030705010518070b13 76
    0xf510b5000031300044811501c48241d000325007810307000390740019200402451030002c004000303c009014030030b00c18011989640c0c480c404980c041c805850038902030440035a5484c4603180141c01c1c140c1843c4e0401c3c07112810350900140e1a04805038204030801c0341000d180c1e9071078110180098010100c90120030340307965080803541c00d0002c005090303043e11940d010f0100d11051442e9040c0b43e20300301d42110807944a030320140e001c21a00140500501e0010b44494500402500410700340c401d1a0005001d40c030016003440350070b581c10407540c901b005d603170402c1a003071040d001c1040030043c040300030180c41011403101040c18440c0e6901200c1400c0c170000e000704506115000142c8007074010420007405035103007d001a0080500071f603681040e075525641d20411074240707600000c0001e0303c0003c000050410900c0880041c3c010028101d24030306950007941c440150313151507400c0d582c0c01019035200e0042c010b00740c550004001040340a0760406c7c10b215442e000c0141e842910807a0a5011000ca0b80310411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 571452877 1250 571451627 571451633
    0x2070f02130207060b0f06031617010611060a0606051602011b051c0f08191d0304080c1504261606120e060a1a0303030c04090e07060c110a05030a 64
    0x40201074081c8180130038000c40384001c0410510b41011001207401080070000542c0c025503144a9041e0340019041c03a005080128001c1046030009800c0100410034803182a103000008004107079025100e400c1c140585402c2210092882c010003911920f18400401680c1c210b80c01007100c3c0c40803910303050000c00310400b1810016554020303020b25040110749000c41c06d861a00c510105481c0700c10b1510b420100752201003000e003205000c1e141c800900c40d665580f085010342904103201000501c18000c603201c50501010303034240003650709180d100c0c1c00c07010240b01a1410800941d0210748005030444903000b4240b94555840020b151100f0182c05a800713040d503100903000e50541610810b40d5640e8840784220146002c0b6040031003080c00c40c0c0e000c10001405503410ba0000c0e00c07140b16559120122007000c2e0301103072558000b992484550b100108003400010020702c108440c8402035001448460700d0250060701c02d650140000d000d40c6020041c0d02000e4030b850f00f8440c024200034089a4604049003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 571454127 1250 571452877 571452881
    0x21305010306050f0106020606061312150c1809240b13090506061909150e0310092d02060d1d060105010e090604200a1202030408040902070f0213 64
    0x1000454280d0f20380404940100204030041c1c2c140e988540043c90302c4e45801e01001101c1e0040c929400010000c40001b1408403440441d030b02c80c031480b904403291001071403002402543c076031b003011404000c2c00900207408101904100000c44504410009050308040c4a004408203e1a202e28031002ca0f80c01c00244018128010300c45503d5051130031400c9034076810100e0990344261040c80d4000c2003403104505030840c0c0c10307071004881c010741840c0b40019680d450725a988040400e4820105990480340e150508052104d00c11074030310051304004841080d9074a60f0040608400c000703601059118108402e42c001c3e90142046c0d400411403925186801c00d007502030304484506144076800d8003541902e0080c0002e60303506840e0140c58040ea81000c24080c8550b000c00140b00c80d9029842c1d02c1425444420400100c11181c9200311281d41d46c0340210014180040a40008007040e204104000200b00e000b403d03035003600c040090242e0344000c5800c2c90200c0d03c04c3c0707183c06903120101e0300058251132059 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 571455377 1250 571454127 571454129
    0x50d08040602100c0804080a110d0f0207080a08030c0d0e150105040b04150603110d020307090303021504050714121b120105190e07080712020112050709030809010c02130501 76
    0xc0c0c2d08a483c0104070030251410344035584101d030003080800001c2000940050050103280031181b500300b070041d896001c841e00c0c01e446a0211004160129982c003500340d814458403002c1c0c02d0403001410008059500c440c1d4911004208404405000c50414000b1074070350882100c8110f401c2c115000441d8148164074240303028407840380f26518000400c403d42c12301d406010100c07652441e4a0019901e028002d8014000302c0d8030341d003d019010030005070804000c5c4080d60050308285e0710604885d04500d0043c0c5420b0311418a400c07005010010000060310001d80d80054520316220710344a88406800300f1500096100c823041d0a004012409000400d100f8071ba005510044803125010100010fa841c01c9130000e440e85c0301030161000344403203d0320b400d400101d0180492401c8904480c0d80f100b00300d00b803403590b0700030841500001010070155079110040480c50200d28004001c20b00705090702900e0060076100082030034101107281300e07440e8018045003203541e8021b0000b80801101d122031400418003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 571456627 1250 571455377 571455389
    0x310030b09060f01052707051213020102010e0f2505120f010b010c020d12051606050403030c0e010c0222021b070f0b03070e03070b070506100501080c12040c050d0804 73
    0x40f1000000300f40c6040140b800041000c0c54000b010b0541c131201c40c906c0c1000c01041c2c4018040100081c10f01c40f8540c0e01c1e0039110300a5100d50800c0091640b000a0a4074102000c4518a0b40a25410a15100e011402005148500b542d00c10007566011f07180903858210303031106074024020580c0002c401000b0030300840c58441140204080541000156a1080745c00740c06504642102c2c0d98400050f000c1c0307440055a03000d03080c0203003000300b100400340308410040400c454503501c03401844101501070080c0b0b491442181045284071500c100000c5c03c10300802c1d0040d00c685007100c02ea860f51442a01c00c040c12408540007550717212041c1c0c24012500320321956044242c13181100008007510411090300581303640f40340e600d103941c0380e030a011a49460034020069150090301c0000074140c8018004143c0c103486030b00984a0303840c00510501c2c498003941e104c5814803115100304204503103520700310380300c241c07805404586a44070750403c281c0000441c2c00c62600f0001404e840b00601c500c4001810403108 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 571457877 1250 571456627 571456651
    0x301060b12150604082d0109030507053003060414070c0201090b0717130e100e0a0c050d0f0905060906040b1503030412031707030204080106080a0203120310030b0906 73
    0x8010050041520130f501c07407010b55810540c40c0203101460104428420b40f14602c0e20305420900a00113401c441c10700c042103002c164002007042c2080014485000000b006c80c004151004500182600d13461240d0380d0400d02c0e400c00000112580d4841c0c0c8950a0058503620b040c2c0703145010040074100101c02c3c04241d0202c6c407a030500007902200101159105940000d2114081514860184007034000c1210070640c004000d01c0420800d00b50500b440c4580440103c41c003c0701d150a11004030003101070708540c4544d040c01d40520038540c11104403984602c108078005403a0301c02c0300500b40202381c01e4000418900403c000c0c00440b02c40002c82500660141080440c151a41050140071100d01c801c2960150014002001109005e021059001c0e00a09002c0f2a0301e1150700c19070001038040f1803c3d808650701150510807180e0074811800542030050003020000703046d0300060f540703001c41c4a1203921040004001824164079100700d80c0110780c022140c0c080c0f8107045400980368501120103003080c0c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 571459127 1250 571457877 571457911
    0xf050f07030b1512060114070302011b0e0102120f0c16090513031403180312100506070519060209130207051b0904032304030501140907230301060b12 66
    0x1140402c034074014843c5800c02c5918107101ca904d0807810000c0200312070f040c07008408070300481c1c1e54001c00401c1c90900c00d030700015900c42200c20080100a44940303400402c02c43c80e0591042c1c0e600010380d40041c0441d804c0b404c0c2c4540304c2d000b80319601d100d03502103010710340030300d044c81903c1e6425000824245c81b4000024803269a0b4800030701030a00c0ca07904090005043d06411484150340c0380c00554120052030780302c0356404d030699582480d50b40140b262111030200712041189440400820304043d0038101ca0240c82d250007a01c03036076030f10f0318030980074507414544c0200031041001d85c1e4101c3d9030484001d40742d40c140f10b103040d9002c0001d4000748001e449500031045030100c8501701d084094100c4000a00d140c226407241d850440e03120400008100c0005401004581d00c02e0701d040c05400114070840000c1206040c040c020a91314402404203402c40e80007100902074164541070403041c1c1c07a40344040b4003681e03a5800001e4090092035100c5180c0020006888018000ca1b0412921800035944c81e54040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 571460377 1250 571459127 571459129
    0x203070e091b1c030305010e220f030e09040b040b100b0909060f03070303120e030403230a0b0c04171507050f040302040603060504021e1f020c0907020d14041410030f050f07030b 78
    0x101c0260b441400c0d227404240c81800035060301c01500707105020386041c0340d00080c44000b00d2401c203c251000c0e034640d0300c0c2004010030025110a1aa44004060b10700c3c10207a00d0851624018001e14455621030340e50140050a03503201d808580d61002402030803940d0840d1b880c14060085a4400f100402c80ba09001c132145d007800000088404a991103a18844840092000150081882140420707103000704c0f040480810009072255000e0311102d50041d55903803400440d0341a05441400e8402c1e17030b4220100468240b090008460b034000355505109030744011155100c0c80b644629000203601a1070000302006200480d03100038030a44c82641c10703596662644c408010700740b2100350700651150b01500c1d50806801c1e00b80844201c501d40c0d0040395103040880000a140c000102d4112005034014010040322a42c440d40d05594078214040d00c5140074140302c0180e01042000030001d004005440d00054803034425402004520441242000941050103449c04036001c2601d9800c0064100341d003140403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 571461627 1250 571460377 571460401
    0x70f080322170f0d0911010e010c0c030807140708030d0b0f0306181002030103050102030f010618090203101212020609010b0a090e1e03070203070e091b1c030305010e 73
    0x14864000c00a82c8810045407032010441d4000110000000300030f010740e80c5062410702810039541d02c102c1200414100540004004042c0d00880504100c02c03000358002240c00c20f036000c0c040da908555035540d60070040c185010008101c1401d024607201f107040000e4003e40110203440320410a20092042c5024036042050440d443c41100c1c0e451b41040380451460b40c1d088001e401000c80850070b440841c5450b2030301030100e0b0401d90094808d65000820800326041c43c030506409846035003440c7c08a1401030b28000ca1035003c0d030242d0640d480d80000402c1b1000d42d401d0003000241041881e1110303c640b18900314800c404072060590162140d80b02080b4a40c1041c089c100340c1c441c0107091020f0b02031900620001500b0505003c640074001c00408085000c1075507950005040389400942e43d07414944140f502d0610598400c1e00d850707100c4010701c406040e01050101c4040010081d42c948519103900181d1398200d240d0a002c81d005484100b50b0400d41c154000f54121422081151038540c1c402220440b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 571462877 1250 571461627 571461691
    0x2060f090a233708010f0b0a170d0503060105131203020615130902181f0b03061503072d0212030709030201050c12031305010c020a0b1b070f0803 64
    0x900720100b040700d26900c50f4681090003081d4461008a0120b0f99a8010f050071100c20b081001c1c1504d484155080c214140924504010158042251a06155410000d49402d510303200d01042101c00408076070160f109105443c0072061804900d600380b5074800000149403440071040340503002d403000007407924805070410300140102400036099840c03100203000040444001c1280e01031884201200100809800b203842182c0c0701800e680c02c0c043c4074001418041d03c0d80c0c40300e402d80c0c2c0b0802c10041d06886689c000540325510074a010b807a078489032410b0b2403180c02204151034641592a4020440100b4503201850030307010303003d8a080d407252151a03006440300b1034120020034950b0801300019481980101901c00e1003005071010f6007000896114542e005071090403c41e1805081c02e011701c0020711459858005a0004292400c0280d44007006035000a08600b00c5408581c548a0300380c610a089680c540e902c0300e03140d922181c1600d400340b440d8106031808000c100844410060300e81d100c0100700 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 571464127 1250 571462877 571462909
    0x80f072003120f190f1103030c07020d111203030703060e01120b07110a03120c0e131d011107060501050d0f0b2d01030204050703020909010302060f090a23 68
    0x44205500040102d005070b0010a41403401041001440c110134001240128110107a0741d44040c00380200900900e5400d600e410001682c000304103009504086100f1190641c1e41581d510350900c105041c081f032404524038140e900025004410103000d480400150f1085410382c40400c010340e00c0d00c0007015001005d01803100ea80300104603000106002e1217816610010f44d281000000058078501401c141d8102e1003100418003410f4041e6401405008040c18038200f4a050340c40c51842100080189440407085074503282d9465100d1503007061003034180001c07481e070f600900655a2858106109900001080d5061403504001240383e02d0210360244980e600102904015032540d150046540d901821110310054421020010b04500350b45500940340040c0e80300c000c42d851030050000351140180345904151040280303810035030352003200f41e0549806545407500c40e02c00701a00c070b6542c07080096250340003182e0000003a40341d400c0184038034003a07100000c03d440c4420000c24051500000340c449 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 571465377 1250 571464127 571464133
    0x6020712060e070602031315360e01090c050f0706022503020a0302120903100207080405120f011a01080f100e01090e071e061b080f072003 61
    0x10400c0003040c18400540d24040c41e40007410100ba010854070308070041c0e00050250300301281d101440d0f41c070071908200034809081115440d407000000242034020003d000601511810f60001005a80b03214100301c005949455060458a515031812002c90034418200c1c62410288401030080c030a4069070b00503007150890908101c85a550301019400c59015055541c2e0490f0108103400260300c58198a10700a80203020b0700c10030307403d0007070514040070409d010704035003004400203944000900d04001151103800603240c0a981c40c0004042c89107500c500e61003d00c61701c605a00c1e41001c641b1132580b0903000c1c001c001c039403242c24007800308000203102c1c41d004c181001d0018150b0121901c0709030707008003000d40f1011003d803100d00759040c41c0020381140c0501e40d07680711003c001440402444000c1c01d1510305100719400d0000c0813011403ea9800344404015500c02c21340349200740342c00b005501561188285488550300048940b464105042c151103803580e40300c030b48002c414040c03c0f80741d404a001e006 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 571466627 1250 571465377 571465379
    0x303040314070b0c03040501050901060302060412060219050406021005150609060c06040c151803061503080409050f06040e06070f1206120b010803190f0e10081807060207 75
    0x5440401c1c19000100340c002082161000195880e01c24900c03455503040c885032a414a42001c9013125001468411703180e162010038005a9520403d540494059902e0505484080d01c2c2580c00b07801000903080c400c0c8030301c0c0c9841c40201d0300900500151400c5e64200c48041c40c410a19009a990503114600d12001d80c0c0803c2406040041c01800c0410019104038640f165105840c0d10f0114212025611003000f100d041c01406683c1f800e00d08001c101c0d141160f0f64903d0714510429142c440e01c00249a150303524070524250200002c604002d68015092a856070f40d12050a0b001e0041100c2d600d81016902000400307500d00342c0b080d943e000902c200141425500e0b074200b65409592010340b00c017030080360017200640dc1490300a0301c0141c2405144c403806008a461300400c6802c068100c8151a0401e12069203000750700010a0202d48a514141180c0c20030107100307450004030510000c3d000400002c10140030364001c51310302c0c001c00150000c00d00610f0460941521440e00340100001a007002c00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 571467877 1250 571466627 571466633
    0x91035280609020d060603052103060904110a180c050424030b04020c0a021e0d0b0402010c0c0b030603101109061b15010815010332010203280e030304 66
    0x10251091500c074103030000b00c10806400042d0241154002202c403a0b0f00c8440c28020484140020014a0403045460364a003408244181003800003c0101d17004102c902e0008051149588500c40c5000c1e001d8814103246880c0d40c09004d951001c103590000c540e040c0055000c546108108440440380c3c0403852410704070588880b16134450208414004142e151445050581d540d0301c024000c00c25008014840f0a400c0d20521007410f0440801c3c0051900420304c0c081182c072100c2c49000d2090303200409103441d035600c1c030060b00c284000b20009082100070102c04280580f0940c015400745100f01c04480c5414890b8040f4004d0f035001050a00c000d03102800101214100500980115240c1040a510841d41e030352065151884089045010440010041020034020b01009400c8068525a8645581140c0301c01c14030140000d0f4102d00c0c400c0f40e2114844840404001e05961250240250368908000100c048504040684503403c04441c50744000700b0300d400e200d03080183c03500034061821591507803 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 571469127 1250 571467877 571467943
    0x8060d030c050f0607021011031b0307030e100b3d03090212030a0810081203071b2603040b131a070210111602091035 52
    0x21000c90303683c415500300308200c080c00e019180c8100010f90061900207600450b0105503009010000b1004000f0014080c4031040840d001c81c0e244051500a40c4c1c0b034a91300000c0340100358941c2ca40b503e50150100d403544075190342d040381c0a000d40c00c50f200d6048100c51205a14000000000d1480e815049a54100304488000b01511030150740d040c00034070351002d500442c188501c012044c4026400005604042c0c40d08220160b0b041140303500009901810508a2035840002e2140c6060468011002621852055081d01030700d000c003001c0c1010301d10217807528012640203904540381074440c2200034024088400240ca100d650400400b40240d01d406004034540d01daa40c4098440c25000b02c071048841d0080c403c1c00d030003020320b54000d004200c10a00c030034040311803548150398084005c000184164441940c0350b09960f8044034042219220041c0342103100d0030350381c400382c0890761581a841c0114150702c3ca0190001404070255603400b40da505484d22503000c4031007205580018803900c40841401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 571470377 1250 571469127 571469147
    0x411010201140a0603030f0203070f020103090606380a05070212030c2a0607021807111002090907090e011401140d0e070e0903040e090a02150706060608060d03 70
    0x60000049949400414a02104080b0f41c91001c59455400c1042016400351040c0410101032010358104070307d0303030b031000b60384031202d00c02a0400d605c4400303100c10f201c460342c4484002c0c18075004080005400d007414999000c02d0000c00341c2c40700c1c8601c07404500c804540c0100c480c01103a6a407510300c3c166055080060410480c86520b006100030b0000280c010341c1004003c0c1d8030000314042c581c40b104060003100c02096a809201e0144005000080068031313900e4100801303010514109146580d10401102c000d080d00400565510980d2445030207102030354001d041c1d00806581080740b0740e03104103050307541d14034600c52809403240602c0104040f400c0c0c501400c0a844c814034005902c1c07407038101400515040108144481030f91024295000c80d002c11051000784068007001c0114500812450380740d0203144a998803205061002400c2c00d8402d110310401203500038010800180620744184168021400c12101c7c140780103404550f00303001d601d90703500c41c8100400d04900c0031480d59044410a940d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 571471627 1250 571470377 571470379
    0x1724040e0307050f0304031b0f0b03090124030b0604050105030c121009032001150512010e030406080f0f19090f2118080d030905071a0318060f0411 65
    0x103102c524000783d4140000801c00c0360801c001d64440d82141030941c041c1010071040f001568525404200082d4202c545600329902842081e4683e42d8010109016044a00c0c4202c1210009202600075a140051120559006904130700c0c050345c4007001d00003150001e009850b415400300b008115076150040c0310024004800050715181d1040d240c0090560702c40300c0e801c4010803c0c2140e0000c1c031250040a080319a4448002482501c401114540d190411401036030701031780d80d01e03131100f20002e001d400c0b070141c13958a0800c982c0d943c0c0d900c0c0320041c405441a2010310065020310045504888100c120034001c180001c40030801d031540c80c1c0ca8000a00d06981d040741c4580910701410f020402024041c19107040814400041204000c401406054401c01c00b4458070b081200c1800b01200020340d0010382d80c403904000940c281c0d181400703843d0928a600044c400c0c40c0000166440b042201d01540c0950543da074201c0d241155441d501d511000d040b541042c440704041d000034081460701e0308015108034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 571472877 1250 571471627 571471633
    0x1a011530051e010e1503011814070b03010b09030f07181a0904030309060b10080c0a030204030c140a051c03080606090a03060e1b090c03041707031724040e 68
    0x541c0c40400070602c102644074208810f0a401041403a012008102e45681c1c0110002c10412409402040b255107100c40c024042e040007801e0044a02c60400450380506104003807683c5a695610300c2d0851584175070200d40c041c0c05490f54032080d5803000516403041e2205080f502a0340c0340c01d6034440004202403c0544000b010300c080c9a0305603251407401c0340c00b91b4000d0360086100b030181d05040d819103100123001401450417840158240f03601140498008581c21310450390f80c0a1710204030041d0203250009001c002003400c0004a05800c1585c0e95500242540d440c00d49594030410010031514240c094026201134103503540000f071054049940c07200000b0a400e00b07200f600c07808118050701030742003150080d50311544000445010843c50201c2c07070344c482500c400c241154011810301040a08101c1500c0408000701302009515449407115136003502400e5103030790907414018900703c0030404007480000300d0b02c082141281600c4d504105e240d10480305140d000c8079807061200819000c004805140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 571474127 1250 571472877 571472911
    0x309150c060903020d030501140607030503130204060f14041103161205160305010b0306061b0f0105072c03031e09100e03120418091a01153005 63
    0x548544200c0e40d030342d4029070061503a0b800e046405000c80b0011f800003050840c0c201e0710105281d980c0c8046910041c0d16103003190f125110300e1401445c042150034000c2d40141080c40200e5500c4083c0403e100b21504c40040da03550404041c28401102c82c02c0713a103102d0b04041040020040343c0800b03995042511140341c51140daa03a61a03042007101ca00742d0300c0403080c0903181e04540f0400d5140c0246405401d00107400340c5141043c00024840f4407981440704007500c408278110301803a1082c4006a5040210310003488540b502100c0204824120000c100e900300b003145564014200000010300400c001030019450107040c144180c0031880e080b696110071401c10044d2800c552604003034610050f030f280d2030302a0201480c1c4200740c20884903002d18000750388103000800c45507051101c000c124100741080000c404480c0c0c203180d00114121500182e00d041c6c081c0c000a010388080c8180c00c681007155a80c0d1241c0852946135090100c1c081e025401411032200044c00307559681c0e44000d402c0b80614061440303075 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 571475377 1250 571474127 571474133
    0x30b060d0b09100b12030706180c030c2c040209090a060609060f120b010605090607081908130201090308130f06020309150a080a1e0207060b04060b070309150c 70
    0x14004aa0201443c1c1100c18403401c540818010b1104800049170001e160180101071a5500d01036034101510058803916528813415410303005c0060550014241c0062035103d0615688040305882080c11880030180241105000c051194050114013040c10000341c5a94003040641200a05418a68050080c000c40000c00501c91400104440200400c096280140718800718034260b120000307840a07061014000b54880c03041c4c906484950405a48800d070043c08191706000c2d50b08000c025020024502040084106902c020900c01d80e45100c11903072400100044114040d000a000c90310080c2c0602c00034040001408050030b611350b0a525a0340e130780d80707440c0d100e915640c00340c0056007000840039403d04088030308010300026a5051450720b50500c4004088a0005000910160b515482510380129000054404a100090075500d4010900f488401010b02034980c0b80700f1441d1480000f940b00118060ba9030140d056210388401c1441c1c0480c0004e42c2d04142c0c200010081021a08800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 571476627 1250 571475377 571475393
    0x509070818030c010b090108060c031801060513050f0a0e15090f0d0c06050c091005090d02031006090b0d02181f030326011a0f090409060207022404030b060d 69
    0x80701c3d582c00081844000322091014055068204a9158100c007041100c807074030b8203046a810050021800030b01c10341082a140c01400690426540503100c0d089034105407515801103406440f00f18800c2030241c07a0201108100d0346e0702c5000036520340200700c0c0c03514050001880d40c0c2d0300c42d0ba0380b01070320b44070709405000310b0500018001d0817000c110300044071402d01c01588a519844200044614139080111002502004518407084c0400c800011980b000392100006010907135030290886080c01c01c030440100140c103d601808c50340500e481c08081c06031030101c40006503a900540341c1c20b41812046850b0f0f031020001420348000c8a4004100c0503c0d030b14070b854a90042d806580d41c59941c0482d213481448100d01380704425034030075104c0b0040c400c1d105041005000740c22000d241a80d00ca860404d41a414020440900c1c0e100e4a8201001c09100285d002051003e20031100c00824000b080c00e0011601c154260208800900340400d05c00101740d4240d072a00704000814010491500d5a5030803d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 571477877 1250 571476627 571476637
    0x2040b03070305071502030a1b140706021c02010207020906042309030a080a090b07111f0f0605010c0b0a111c0c030507020708370503040f0f050907081803 68
    0x2d0f1076202c1c001c03c0191106282465250700541d1029502d440203c030030040c81003007080c03484142440c107851100700300700c000f100e00461906008107480700c2d15030b0394001944441c80c240f20f00512041511200520074418030858807840d030300030820802601d0322030a1000030140c4c4941d0307150603900708a82402d038080221486204400780e1004503500c0100e4500100704d040003900860109040040d6840058002482706500121034980002c040d004036050174908078103e0095969000c030f10509040c902e21a80164442490014042c49519a110011940c5003012000545104002000b05903806650b8110b03580e9040030181c030508044c000034070200c20100081002c2070107540c51864103481505405166441807850020b410300600d0700c40200e4450005001c80362a68400c42403550030191000c841414820300781404400122241c80c0c00c917070302d0b8098006c0303103608030481d03500003811040b4980610640c2e5000d0b2049099855400c0d02351840348024040e1803800c88075075403480b121002000501 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 571479127 1250 571477877 571477883
    0x6021b06160b0703140403170402041514040509030408070314010603060203070e090601031107060914030f0319150303030905210d060801020a020a0b102312070302090a0902040b030703 81
    0x104143c02c02007030207400c44160f1414081500c20410801c808603800041d81814854a00c00900d1655203a100040080c050110000c40c11410301078040b030010224141e0001c80321080d24100500e440302965643c1d01d009a2003642120f600818050001460030822552100c1d0b032500041802c40d2a070f45c3e840280d800031501e0703c0005002c4003000d00c2e9442c00c8000035420480c05c0c01e00700800c411486006803940315000707001c0d1510b034442c6803c0080020065007112001ca02006990301c0b0225003a4400c2d01d40c3c400d484100c0c080044e041c00e034032048058421981145140cac00ba07581d8442c51903500358090041200240c0350f81c041d691110720640e00d1103900700440e200501d105c0d551034031024a550201c90650304100341c40da1043c400d00c42034030f07000214031080c03a4000c00c94050b5681c40c0b801d07803400900389400c4407000c000c46041d080340031029880c0417112880219164070040340000c00c1c06d07940707a00510020754858030b4580031a040142c1644241c041c18005480807070040c850202080c035000c0654012 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 571480377 1250 571479127 571479143
    0x906021603030f110f130e090a02121903210f0f0e03030402060409091509030507060606020604030804111302040312032f030601030905010f090b07050406021b0616 72
    0x106042541c58400c80f46814014042005a000743d42c3e450401030040800740c119821001551076030448011410000030a0304000500b0546040943d10352a900003100c124061901d001140c082800b0204503010f0f05442182c240100340c0710354508403411007030f880003418086482c03113081d803500c00341d13018054491080386000b03d4440300c054407000440384003001c4542c05800c1031091100682e16201224112030207400042408905802d101c1944000c1c0403019200e50710382a010010507402c2000380c0146402650704100c04d69036400c2c16611840d003150020000382c041400540041d42c1d402d040404080d001e02166158240b24101501b282d1003078000f9101403d10312005407580d5818000e0f44241000748901c00000c108204a02e5155a00d601102c2a106030200c00100030340d01ca0ba00c608421504800280007540548041c0401030140400039a40250b0400020748154054803c50303040f01e90b554000c009682840e60000c120154510f40300c2e82c0a00f08218400440040444201d02c10f4025084 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 571481627 1250 571480377 571480417
    0x240403170f1009060e0a02180a0609050a060504060f11010b120a15020702010f030b01170c07020f01050307020c0120060711010605040902100e0d080c030405130605100c0303090602 79
    0x450301c2c6800c5035440301140c50b040140a1000c07440d2a2a9140c100c0416030016072510700700c1d40c801000c44150104160015203400c00091100e50150b03c01c02120020744170314a869464101c12140c62046000c4e090104070f030145d9000a0034815840d070a052102007000040074511000000d880d80700e803540c007007003660041541009000140001c2d1155820b9048214139003e0b484e400601000040703002c000c24141e46030140701c030b103034001c2c12014560ad040410344612864052051105904200001d0780903420780802d21000d540a001180d000345940e80082400302c5140004640200c0240e8030740800149e43d012041644000300840c0780981c9081d19121050984c08241c182156900c0d481280300d00d042c51701840c0943c03504003c07101e0348801c0d4501403a40080d04808505030800c034440061903d40c00140075aa03288010010740161003003120300004400d03040c000b140689055000309640040c100c210040058002d4403081140383c400d040c04911901c1036107422040340c200d188000c0001d190010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 571482877 1250 571481627 571481641
    0x618130b0316030b01030b040813060f0f08012138150604090209190305030307020705011707050313060606210510090e010e010e01020a11240403170f 66
    0x200c0031007202d407030080d8a5400c900d07544650122400621010300440400300105007809560021603132003160103c3c698030440d6071100001c010f50018401800041c484d48005070420b48035188180c103d6904401e00b241c0b200840f03c0001106403031a104175050f00701c0c207007a2560102105144035a0311030303d4000715141e41c0d081ca200b1620480080110707000040c1c0401808141c1e4600003944c0c10340da051034005032101131800201e02500c02d01c0c0404640440241000010007c00200441c8035019070307420b80d072005a43c0c00054071160010703101c5444da5612080061816449030000d950301000031842c2c0080c11b040b0781c807610b0481e034071900008002021244681c15882e510003055151804150b13007041185054441454420041d01901207803585481415080200940144d40242044802044103a000b80c44d5a4000c1d0b001c08a00400710b442c1c0b550079021500f010405014070351200025a0411400c80501c0c0f84d84400240101e09100c0d401c03c00805401e22150100c0c4148000d001581c01800d05403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 571484127 1250 571482877 571482883
    0x1e041a0910081216020d140f0c130b01090b0c010509060c07050a0f0201050c01020406080a111606050601120908030a141302131407020604060612020f0618130b03 71
    0x80140101c0848400c08028807400000e851600203e00301c409a01d4904107002d4012248040034080c1d031120684100d5800d0001344940340690f00c0d0804100c03901071155654403038403a0410001e090740412030b101d11203004881c5401a140f12071052501056190f01c544050020741c0105940b03440c942e640d50104154407000300700a580101000f00c1c0541001556942d142d5a282d03140d800800ea03000319504401164081c07002e440c130386050440259180c5172110f40003841001d041b01d000000509040481442c600c00310219081d10b080500b1400401e01c40b915620007030318000d0f1000341008115008000139040d540708401c00144078921241e500d08019001034103555885041505514070b00301841604a1000e00c2d0300c0016605075032034a80c00000041d0300d00240741c84030348007510410940800202c00e60108040e031260341724030010000641c031525001c07441140444001e402ca030750b0442d084c0c510b14222000d05802c40c0901d00e0307000078a410401040e0301c0c000d2665811401074513003840c00c2c6245018 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 571485377 1250 571484127 571484131
    0x6130b0301030c17070b0403080c0f010507030c02120903030301150c0507030f06150806060d060209030303010e0714040803090918010f0204170f0316030c0b01080303190c020c1e041a09 81
    0x84c0009201903810101031005921840c40010140400024412a601000e00009030380b0200100200440d1410200290181c840b0711504001409a01000d070f131204075000c29504404800b5004600356820030031003c0b1503084541c80309090140c41c88202d070000340c0c10868800510700c41c3d050020516003600c1e00c0d109980c141d413103a5040036619101400401300000b01c0c0c0d81d02c40c100302d813912690075140c00e1010081c8907094605405000000000c0740c0504074904841c000c21140e0f5a201301a591001e58a08074011400b4a022642041149844516000407196046502d41c0230320304e4000403840d00c003801c58080701c00c410a840c0d000b10f01040001d43d90a01d109034000c846002d04411078841c0100303600d0b48120a503074401c1c03d1000b4001e200b03041c818041d03c2c5000c0c0c1d011802c10300300d58490a000b5584e400444120700b5041b0b0401091880c1c1030240900079106a01c2c0e002460404040010130059488000d40c804100010b4524090a07680c2d81c000c01004043d1403194079150070f11041400012940 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 571486627 1250 571485377 571485419
    0x120d0c1403061e011b0602031b07030903060b06090d0b090105061009031b03120804051006031112010e03040e0415060501090905061c030e090a06120206130b0301030c 73
    0x14000c11102e626540910440c607025002c28030565240c200050754a101c001c503281e03a1075450004803200f0004994021030283e80240d60743c80c2c09220f8964407a05510075100000c00045007032008000082d07880e000083ca0020003808503040c014007001060300c49030020800e82d000c24015050252407202842841c1d0045401d40b0845041e803282030b8042e00344006880000c0c0b0802294a0044005000580c198080c40e4860b03041040302030702c1076004020400c1500c1c150f650f80602407801c4200c86041c4100011030b580a1280c40441144a0401904402d0802070f1403c9540340d84900b041e0741c10a00040c00034003017112041314a03040c1820a1000c80309103880c001d6081e45000741c14801a0b0708840740780c0494800c1d0b00007150070780d9603038086515015520b60020b80d08034403581110806812200202a4003c160b484224030341d101c0d0f80c900300343c9400307100d1903040c00c9040284c00e026003050b5004000308030b1446155000d482e0390303414050b0640d200341c3c03080d2540d04005174103100c4060030110303143c0c40e510 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 571487877 1250 571486627 571486667
    0x2192d051c060c110a15090503070524040b1614030711150714031e24090c0901050a0302040e01060c150b0a30080c0f031c0905120d0c 59
    0x1300304146954201c107540243c001640a003410311801819001400358960140a50751102e1032458110746e20f442025034803c240810f801c02200c20b40300c1e900c2e1030f4415900205c141c15161110045080002c0c018081c1408110307011040098104011004601401d4071750b4480040c02c1c80480b18a080618511800d0103200c85c034024400303500d03446105412001c18060300ca6aa9460303c0916143c00303c030312800083c550a1034010841484a10f900180c40110000c01d00c40d01c104d43c5104205603054100c0740640b801c0d4060045441e035501c01c102800300090320703040052500fa1140780d180c403036203400d038840380c0094008103c100400850001c01080200100002d019018840b0005004031505005001039035020078016071000807580407a41c90070040300c1c604103000c042400c160046910140c0000f003e8450f4045100d1032140c000100c4040030f406501c2451000c07030140307442c0017a182d003490545051151944102c3c09c019544000e1003002d81009000513400758800019040015800f05061404 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 571489127 1250 571487877 571487897
    0x5060304080304060c1205090d0323071b0206070f0201020d0206040f08030604140f0907080c060d050a0204050a06050c210306010f02011e0902192d051c060c 69
    0x41c40c0301d01660f801c507602c142c0200d4000170f500012220100d191000202040c20700d018420150b41c086105250022030f69010711071049650390040c40d8400e618600c0401d01402d0001985231403081d000801044d4884100c3c4042c010b403500001d04c0c0d6008541c0c1a0340303449071040c0020442d07070104510680e010f000c0c0050052840c207034490b180c000e0700041703000e08800800400140565202c0d130200c003100c3d90425103803006042418042c1820030081b20b829410344282100407848090024070803030407401c000c022034501511034000001410024001ea103041e0340034480880c1c00e5484d0b0000d14058002a69180c1d203c209401d507440c070f0f003800e074031042090b4511140340c0031101c42c20300100d0b9400203080c01c051040c034a0b00702080b401030425403c0010488622900a8400034894000e203c91500840300c0c494140c85410780e1824112561062100300e8624038840d0208100b040c0c94008401a8400404212a600d5000c6aa00e91851140c0050104100d00500400205200c0c0501600761031500b03071041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 571490377 1250 571489127 571489133
    0xa180e160c051e010903020f010519150807120308010e04080f0c16180f060e0615070f030822030509040b03010608070605190c0305070b0916030507050a05060304 71
    0xa062400c11180070081107950400a0041c00c1100a0004080d0104205074900443e207140c000c10040ca404c030300500800500940d458014003a20f400f80a041088140350442001c1800050504868803604102a5640054054024050280101900380071b0a45110661900410040b0140c11072a9446055010700c4082041c4c070ac169050003583c43d0100b555030580c0401c0a00e0f0091400d940d52505043d4a00403c2c1850344141c44500020351050510010f001080b0b20001e581c1180200010440d0400020b82a8940350200381041e81162100c1860030100f503ca001804c185554280c0124654905003c0200e9085111350b54807182c1602116000700da5a130010110b10840b86218442c64803990348005541d800c1d0312103402006070404507964195038a002074141d0308000c02c8900061066941c180703503280544404c0303820071b80c1591110702c1c080346503071855400040a000c031001441407a5040c02d5003ea40407151000c1c50080c0014441d40d0302e40b0f0704015070341c0e84a4002071b0040500344140000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 571491627 1250 571490377 571490401
    0x302030703030902010c02030106090615021b0d140d1d01113313050d0f0203070605070509060715052a070302010e0604030305090c0f030327060a180e 66
    0x40d95515203404944041036000481d480441618003035499440c3c40400605043c0c3c17039018904544119000301750a07078551078180d03161310042e50002418404451f1443c018900300446011091003000c242030028401341c049481d04400c90004000319200100000206044070685401c009003440c10f01c214000307500010362128011101010807400c8503172190316940414190f40001300c980c9462080b68074000c107041e00c035003160400c184c4850280310210070480703204102d5500302c2c60160f00214501401c2d40d503041c000b481c1c0180b140d401c110080c08291000d594800091903503601582002080c10940101401250700c05401d544a2113190089444d03540f00141c0728400c40e0352000c0060740c072000642001c1e400b60a1002d148420760160104020405030540e00c1035000e4080141141c055540b4132003400400144405110f500d0707070051044d000c8407500d1075204000403d0164601170f10501c3c40011403490741000300c1c0707040410907800c025117200d82c034030b9410002084500e01d85201800e1122040c24 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 571492877 1250 571491627 571491637
    0x302010b1c03210612051005010518011707090c020c010210200c01110714070803040e0c0d06030c060c1401060311060c0a0f0c0501080a0507020c0d0201020703080d27030203 76
    0x50225580c0025034900c203ca0348200e000705201c800f0510012150310b003807515000c404000a070810328020000c14181003c0501c4000e80844c0d41210701c25900308140b00c00701c1c22a00c556480b8030312440c003011035000c01034003911701000c41c01d800078505038001c0d00029040003488144025400d1038003941040e0707180518036140d5043c00d021070b100e0352090140c030094050101520220a0440006030880801440e400303507860307200080050300c0c4502e443d00c40a07502d074801e80c4140c41c988551240407400941200c0c1c0200f00b02c100c0e4040000c1ca25a03641c1d601d4090035603680c4200c001c261001010014050358450207440d01c1e0300c034002080001d04503500c10424a84c400c94a601848010800311040720302080300c1030506800c4403801c4c1c6904500e03d040000102e01d40a0030340080e50402c08190740544500842c1c3c000e401d150042c0022542000c02c0c01150000c2c41400da0440c23248640c008041074506005089120340000c01003103c403086507511142da02c0045804c0c5988641210240c08a03030f0200c20350b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 571494127 1250 571492877 571492907
    0x906120c0609010306080d020a03260604020c0102130308090301150b0406052b0c0e04021809150409080403030e030d1202033309060103090503120615070302010b1c03 73
    0x5844000c2c850048005002580100040c0e00c1005940080190006007964155201c0e560b550500b2008280c004280003001c01d096000140c104041a51803600b60040c009142403500014103100c018554440c0620091784203682c10300707000955129904080c0207584500004204468880d441d0007405141381c42144a140c0401101007110143c86482c50281080030600d03201400784041c4681058000308984076200700425240041e800b0503050600039100d031440000c2d090040003003040248134424900a05c4094102400d001081003a41c0e9132150450040c003070340712240c480d0305515014000f000c0711070440388a58020902c1c402111740c800c00c3d601748803040d070b0800358a984540580c0c1d4034503001203c0358907454258500b81c4d01c0201c2078130040019400c1c00c0701d001015855610056085502201014040b171b00100001181e10744006030b0b40381c1118010b07190003541c0129071002ca98540010b2411401030b5104d89031561180b40040c2c0f00010349004000c400360052a6941c040c203c40c000d44d080c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 571495377 1250 571494127 571494139
    0x5090c0307030e0a0804240815061917010503150a270b07080a0221090a0c0f0303230301060f090b031602100209090103080d021e07020906120c 63
    0xc001d039119400007411000400c04642d4000724928200c0629041070180050f02c5008040030728200e00c0e039074482d0701c40c400141c8414440e602e0f1714902c2143c00030644501c580200c000c01840810702040d1441846001d00c96881c0720001000400841100d58180d11591107640483d0800c1008034034800701c1504002d002d070700000c92382d8000d00700280d01210314100524450901a81d001441130400d8107030311921003a07031880e94965407100c0304001c03802040e40900340c1c84007a5041740f1043d107000c0441900300b00c0039411900d5004081e954030b03185040d207410500500c542040308100f0142c100030100080104150b10f40810102030001c2021808140320301000c0010380f51001e803400780030b81b02c40c41c0500b801c0d1651907502e18003c1c081243e442c01442200f001445a6130100c03c00702e029100790350362454000c050000d26407943e295801181c011f540c154881c0343c0e00300940780c01c41e0204403040200d0341d070300c50100e502c441c00d82c010021100c0c001801d41f800754451a03160300418a01007100e2030568070454003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 571496627 1250 571495377 571495381
    0x901050111010905030a0503040b10061b08090d08070b24060d0216060e070e060a0b09150a02010506040f020304170307030f05180c06040f091a0603161805090c03 71
    0x442c09000c08600241260000164400075107034010011031046000c2c201c40304464542c1001800800e1030362181e040095200903995143c00c0b414034010011034000c90340709040103400c000040038689111b10440d0a10000102c000410021920702e6511a140400080340350109040b41111012502034a0303101d108000791300d940d09410340d4181c1d100c454010b102a1281e00552400c1c000401c03100540c00400e106020300081d0100454151503c9007102501c3e4500051a1100d1200c0315004a18201e40c454200300400350003c138190050034146000b940080756500740142130108507140c040581c07014900400c2080046290503032541600ca4450b0f1002e41c0d00d0b6100e00c02240209024400c0f4400141000c0c10720401416580054290341c5414054410300c0c0003007820803c0902c1240b0a0404145000d442042980b401d0303400385090100084400300c8a00050700001c550350310455014020341801c507000b5036280d40c0564130840690400d030710760901d1418840020145180108180d00344000000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 571497877 1250 571496627 571496657
    0x29180c150c0307110a15020c04050403170c030f1003020d02010c32060924191b02071e0e041103070f0e0606032206060e07020d030e070509010501 64
    0x41100c035201c00c4042981d07142d8080d4540311000c4090044454031680d05036001149000124803003100e8101c1c2a0010a0845030f01c03000d0001820001f0001c1e028402e0346146211501910034656100322600c12003d40c3d0303440e040c1200009203038058580c8140360f0311080c0134001070b141c48e01080c2010ba02405e01041250319885c081c226160400c0000c40d00d44118201d400c01e15001d252400050180d42040d034000e13681c0c640410b42d0701c0c109555048518030b00074580075a40404102d950390004485c4000d0502204400742c0030042d1640b1150300056103201a60324210300d90f0501c114006018040702c09007000114600c00901c02c9803e0049a03086040c080114040060003090b0707801c0c800b405002e90720f04039542d02030740e500030300244241c080c0c2124010008409181c8070007101d10529810311100c0140074509c1e1000000e8100310400ca9060b90b4072540841d5840b682d08103148101c1d69a8006d010708041c17140c000b015035513035250f000c840c0e900c801c0051041703545415865054500a00c0c00f40b50307145c41d0780 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 571499127 1250 571497877 571497919
    0x80105090f0a1b02070306060801052a0702041401060e0108090706032d0213090203060d2409200603090309060906040902040f03020a0b0910030f0929180c 68
    0x3c051100081d0701c40041c000c290003042030070444c3e0041500708007090751801c20b1420790b54110752074400c6401c800340003203007080780940285400850280c0c1c2c500380030031035012030111024840d00851808120004100f41a0302c805d9000404000b0b2922402c6410140002d940d0b0741c042d40505012b0584500401c801c5083c00b42c006246050040c03078010118000202d050b00940c4840d0400018500008001c1043c1c0e016008890040c0809442d08120035415240d5115410f640c0d0000060b00c426408401008069402809405030042110065468001d01a4043d6030060304085002c1c8409104116144002000ba03e0180c4002c2d034170382e50788021601c0004c02d5441aa08100035443c0f0204020a0424030102c0300d030183d038400d40f071050460307442d0b050300301c07107809080450b583c0440d0051040c2103a80c4207402ca0103021058200200b030250081d1382d040c01c0306080c0b104081d4a46540d40410000c500d10032841600802d002800390640c01e480c1100940703070082000854004d5500600d5400c84000076 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 571500377 1250 571499127 571499141
    0x20f0d051e160822020a0b0c010507091203080a0603080c0c030601170a0605060604120303060503190b0601030c2102030f0718030b04210203090414090703021c0f050616080105090f0a 80
    0x1d11901c541601c0b01c0d030b9100c080c4c00001c0c41210300e4ac0703400002004540590509016500480c1003401509610756044544d114000c09250000d6182c1800200041064020b80700552074103004c0c007d851020410f262806505901c144e9030718510041300003500c00007007046a90075400040120f00f61392000b01080d5180324540c0b05008150248ca0340000340340e856400b03039007901d804805881003900411003681c01803c105001416210109000c984558081d50005000e5121401c0c519000b080342070301c40800c40240000401c0c8103400104000c9280c0044241542c041018200344c0b038030100c00c0380c07092000030b440d01000740101200004a014403a0b030b4464603a5a610941740142c4016a40100a45a4102c940060b002d0b600b42150181034440d00b0180c14800c102c001d00a05881c0e00d541c02b000203010403010038036045081141e81401007001244441007060091000788103504001c02e44002c85003101d507104041202d40c40041c01140c1c0c03925180342d0400429150590700f600e83c8000b4400070254 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 571501627 1250 571500377 571500379
    0xc1b06020c1e0105010602031e0a0e0301060b070203070509011203051c05040c170a03021c032009011103030c0d091415060a090204080a0303020f0d051e16082202 71
    0xd074050958082c00011507186030780800da00a011990341d03030340107170303528003030501d0a414140d01d800340c00c0d20510030800034194003606850300505003205007020900b1607c1a13040051a04800075a0f0000d40c28104544001030005980001d1258076106c0b042d005148502401000c101001901c0e040310f032485e80780002d400380282406c00c540d04291400c80d200303c40074804c1d02c0da1503250000c0503520440115110000a4050f0060000c0d103008590400a050441e0041c02c14541c1c0d80c0f40d0029034440d4065010742d07450002c2c0d2060b0740c1d820104005040e862200b00b4203000b0740e0081081008502d40f6205a40c60074030140000301e0140c40300c0c5490001103206d501c0070744007031042c0519440000c401d0b5030454002d010a540001c0344d01e440c0c2503201c0c245c0c403450040c00700d564414107903900000e10a41c024610090001c203140d0a00710031030682c0041d950180d883c800c008880c901300d03600f1400103c0185030892550103040008881d00100035000045c018100d60300e000154050784000492192103d084542c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 571502877 1250 571501627 571501633
    0x1b06070206070c0b1306020105042a030506160315150503060a0306021204030e04021e0d0608070e0108010b01030903080402010e0a0b1204290103120e0603190f0c1b06020c 75
    0x240300c0c0340214085d04030102c55003072407208035000501140103210f098007540d007028180c0c500d400103005160b2151803056003482800c585080c000b0102c2d0051152a00860740e84030908500c43c0f0140005054a20115160090000d40c0408200046a50a98001400917400c10319125075881001840782201680091306d55400024403414440700b000600f4820342c0b10f40c03211170300c0c860400240f00490198040540074840007021081e04440c801e0040d00203003071003e0010440984a041050600d110350340252240c1c582d0400500100d02c00f8042c07040c0d4039400780390820511940c0d403030017040d00c1405440a41804040c00b0144615107541c1402c0c4c025054480280360f80e403907010041501801c048409443c0314015024450320110f080c1c4c8040f40c00b620542d1141d07101c1e42191504140b90312003460030700501040023503401403922807601461082d010303000320b0aa0340c101e05020340143e80c0c06102218005180c0900c6400194101c001e6541400710641d9640c486803448c6001e000034464010005800d00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 571504127 1250 571502877 571502879
    0x7021204061b141515030309090604023013030818010608070b040e01050d0b06060a05130f0801150602031b010e15011a04080a02090a140f07030e1b06070206070c 71
    0x41000100320b031041c61001c040c46542e90301c0c41110b00c9400021701280754103400801c64000d080c50804020b82d000500144014506103c0ca14810000b0b6a0b04107044590303040c00e0f030880c01c0300340d031041000d84c00701c0b01c003e155008140030780d4002c1c20148001d080b018424100900700c2c1c8060b5003540b0880141c44000f040302d254503111000340e42150440e10800c40c803c1c1400002164a06100c9002182d19522111810345a21450100040c0360080c420f04001c2003018041c00100800d0204010300400c800c610301228941051001403e450f82861008104c0031403000402649900204071b42c0c0b12000b90f41006115100c04001c980905407021642280f84296440180044941180c56041383d41c1c92600f039096081d000c00041c12030089109000003608070714032640143c20440082030b0300003440140080d980b00303641c0c011074081c4401d44403410482c408804000e020f80e05482101c0100c0c40c00001020b102d244130241036002d42c0d010056901480d000701d070260031502d0f03040a84414070ba2080c01c0c49030203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 571505377 1250 571504127 571504163
    0x5043e22061e091407050919060e040e0c010c0b060301090501020f04050a0609060c0b150306150406122303090604090b090f070c020d030e040c1707021204061b 70
    0x41d00e1800d64003030382c1120320100003c0307141207441024030700020000d42c4022035a61680655040d0448203044d500139140e29582d83c82449082000805454503480b0760b408000140e0070f01c401c45007034024010040d4003075080e4410980e0490520403119910240c141d80da6500e01020901520704007100400799800800ca4881c1004500050415504256010700384580e40d000304a270812114032460001c664070f410000040781d0b03c5050507a0010901541070b003400c4000c3d0100340f80c440119141c5a0ba500c0c0009401418035090003610010074504072034104030b0320f0503100c000401007210b5484110300030300b00da40811082d09106845801c1002400700391546c2d80c0e90054805040107a0402d80720340090000204460381e1034902601514503a07403002c41045641d428003a640c0881c80b010303420311034050621021581c1d1400761808040030395540c1c18004001c807494803502c02000c1c0c400c0c001d42d005031064507101180311041e681124058034041da5610000b40000b2a4017020b4100502400804c15181e1072f1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 571506627 1250 571505377 571505399
    0x1d090f01180506070f090b0f0f0a0c21020c060c1005070c170307050f0702040905060c07140f12160206030c0403030f0c020f01110c0405043e2206 64
    0x4403901a4003a181c3c640c0d40d060303089450900e03001402010a5078904280080d005840140140e18002c0442501c0c1200381c1d04000e500d6040203120b04009008a1940c008200c0c400b04c400c1c0c4a11442c010003840d1412644029440c0d0140e441418012000031400452400c000c01140320b580f01911030030000d5041907800100748400d40c02094955041072191303024001c0542d011240308029507507620382080b200c1ca10192840d4802d81c001e83e8425100e00d045008550180049801400300c00c161541d110307041d240c1140d00340c1c0000d1165035141c00082e0300302c90070400455100da8803081d458206548a014180007040414100300103034004001104005510682e1002402500d0280e01d400d15502c0042ea8121041110004029048650324007401240c0d40202100f24621441400395070380c900c0124042022600d04039005d40361100155004c8101d0141011103808100d007140202403000f9010504c0c0c80241301c2c00c06c2c12801081c50809450034162184500394589111540c140f10103541e80b100050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 571507877 1250 571506627 571506671
    0x30302060106080c0a0f052215021e07060e0d08040801020a11010c121e020712090f031e0204020f0a0c0b1f0e06040207050321010b041d090f01 63
    0x803882c0400402c0b052481c440540d517030801e072a9602050919101c508441c1c54003c070140c068101c03a0300f09110020516100f00fa00502900300303c8006c001e86001c402840e0610100c076010703140c2560075081a240802007107240650b04142091700e201c1d5a0f000100c0ca44541c901800381402c03001080204508030107400803d00d90745039a8500e41e4029441280740e0132120103e8141001c00c032071061030786c10f80c446608401d6440c0080728040c01d01c00328505580040e680818011111401c00081094105400c4024031016001c030829a080c214210360303c40491802e00407012005082100f0194210340e2160100c17280c100e030224210380c82d121401c0000d080d160120400705d60030b845020004041c00c1c1102080c40315138460901c44000c16161a22410745000083c000b01c2c8c0050b02000804003141c41000240200c0240e80c10320008440e10000c0c515000c0c00c1078120f000b000104200800c02d0100c801c10440719080c42c001840881c2d00d41e580b429213841c00608400740c0f50350810100e81040c101c00c0302200 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 571509127 1250 571507877 571507889
    0x712080f0c0d03050606040503100504051606020309190b070f0602162405150105030402120607110606010c020f06210a0204090b060a0206220206040b0903010e010c27030204060303020601 82
    0x81300903201d107020883c242c005c501600380c2540c800e0000062000c1c141d0001600580141b0560f80c2c203140030180380201d90b030107820220140c0d20001c1c0c140781c1030400d404859202ca92034091800110b0410088030002d10905c10040d251100002113001071003050f03412038010700d624071448080f0f03070002d00d802c10300b0b083d94005c1c8103860802464204861402c2e4003800340300c0c1c8a88100502440045801510702d9040a001070f13802400ea903080400194040201c42d01840c00d94a8014500c02c80120080c078000000b07007554104101400101c0058a8a110340035402d881116561f45544c0e80204802d400f2041c40001c3e2004078525017440f4148040d98000c00560352100f02c18840c0a020178203101e038030711540c00c00c1d00050b07000000044860015100000b8070102c00c030505100c120a640004e00c5642003600051400390000901002a00e02481201031a00000b4000d0218600b0018040c107a403003a0058440786030140344480c070009046148075030280d60f00810803c41c480c2c981c1002513480009010348 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 571510377 1250 571509127 571509131
    0xb0a1e1115041205070c0803280201110d020706020d05040305091c0c0e0c0705010908190c02030d050c0316150510031707020d0501050a0e100c020712080f0c0d03 71
    0x1c19032195040c400103204580000224034140d00e0224112a10b07032107510140d5448800f5074001c102e000051004042c1e4070750020100e101d860003000c8410141100e100100156850041d2201c0084610400c2d00e010301f5071110010303201c2800d1b0802601900c580300050307403c1c500c2d0404210405410002800104006030f4001030450b9442500215030b88019202400108071110200901d0a0720031149501030b101e61540c50800c1540e41d9494207540d205901100c11000100780e070b000c60400d12480911500103850074590f07000c0590080f0303807241c4404e45d40c441080000a00c441030b009041045402429801030500b40000c1d00741441e080c0345012109910300c260601c0f011800484a800d0454142c0381c103c0f420803043c0e503222102184990101c1c2c0d040f13070810000a0071202040081c860a4418030540c4004a8094421a612400c0007070300c00034005001e00d4184d03001e0f0f44c0c5a0004a950507240c118649542910349824004400d000d80c07811003801c41800208608002800300b50345e09038000359242 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 571511627 1250 571510377 571510393
    0xc050f0f0610050a120602040f23040c0c060b0a0510020709150302060a08130c030803070816051206121c0e1e0d0309050402031003021503010f0b0a1e11 67
    0xd0040e409100b9a44d00c8001160300780140c001c80001a4003180c4074400052805a4a00c881d126051480d4481040d120160b02c80000c426200d0809060f0b4000c101e800300005c10203040080d1103000c840340c0142203590340b500c491090b0380b5116a4400549001001e0200d02e01512900075540c0b10140240390070941041380050301d04050010301401c2ea87d00902203401c0082d085011652888001c040c2040c1c1440190100045002c4103d030300e0245001e01d030b1565591030810320203401c824001d0000001f52451001100403694850159180c03440c5450701caa98684407040040c1003180300750190040d0740200920a89034021400e40600d030381c03041c1e0701c8285d007200c84802040b900d450281c07a041410060a9040c8020345800e40d50420414424204107007819100e0780490b049800482d07001c4050801d100040c0b095151002070503400c40104901e00e403440d81450140e1a0164007840f55030340020740403807000e80d2580107001c0312407825034840e4141100b000940f00100003c1e08400c10052034050070300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 571512877 1250 571511627 571511641
    0xa0b0d0905282001021c03061203030e060f06150a11010e0307120206010605031501032a031409070312020f03071b0504050405120a050c0f21030708010302010e010c050f0f06 76
    0xf541106110f0503005040194020701d0111584036a0750540e204041c1d50300303408a08440c440c106413a0340d5009980005a003022001c4052034000007920341d600c10490082041019558104503071001d00c3c0145140351103c03a2190b050b0380303d40c040c01040c0129401c0402c90050540000701510400c7d0080700900015034500d1b60903600d03554280074100000c0d200300001200400348500001400c403061400040d2103000069024005001012951503800d005003581c4110b07606019118000031211088a00c2d810a00ca1040c2d894a5510005006681d09140c0c0310502e0300903c03060415142c42c1099a0b0380740007610708041480c0007401e0640795002000000706142c2028402d8a205a90020080c02046a00c00189146030040600142000700c10046558000002d0090100302d0b19a070300102040142c5940c01307002045840d0300504010428010003105aa11500e524116502801c3c0f04481c00354039001250380c071440300000b42461080050011080d0000181120051200c00503684692542d075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 571514127 1250 571512877 571512923
    0x201110d05040c050909061501090b0a121109061c091e030201050106050c10110903010905031305013b100c020312041409062116050a0b0d090528 64
    0x501e40700c0b0f1b1603100e1800281203001548944090210504200041715503446c00c0700751617442582007000043c003c0c0300003490040c0d50b016000607100344030101801d0a6016012462600a04098040f50300b004c071144942032000754041d03034009800400780c01d4410480d0059948000c3d03a031b42c08400547c81c140000402c144070703c5c144ca0000d40b0010280007010165051400070305500b080115050700b00b00440c2c00a95024481c00701e030144110051600c5078000802c00a40c90702d1640312138180540c01046520b9513619801385503581440681e4085079480498007803840940340d40341d840d045000e0019200000344c005465640f61842242143c18481c030420800c0c615015500c03600c116006032040c40e882c40c0c80d01c5045c25a001c18054401000c42d81d002c1014800c5ca1004440211507800400d1820020120f9022600141078195415080130349000e03102201849400c1041c551182e403400d01d40c040002c04e1180c4901c1c0c88074151460411f404040701c00c0c950f40c0195104440001c6d070145c0d0710766859060 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 571515377 1250 571514127 571514131
    0x90415080712031826010b27060906180c0403120507150908090d050a0210030605010f0201060e0a09050c0a030b01330503090a050607081e1003060c0201110d05040c0509 74
    0xb580d4640d40c4910307444185c030190480c42901280380d501c82400212030303102c0d10704407940504031200521342e03800500b0715007841e9000984510f0042e9810310801c0500d84a2514030705c41024080c42d0204a03a031082b040c464140078540004001714106641c1913207607030b07014028100d507134090000e11040164032541c1c030f0112002e9000c010540181803041010602d004103201020728016410303600e1020481e40000d40c01508034054501103655500240110f5a201030758a0001d4a280000c10100e800d10108a800e08401001000740c1d5032100c244400b0803205204c03c544140b00030300500708040c0c591070141420312090241c400400300c0c5000b2800e41128200c600d4a8846440c401c101c9050700070b25048803a94001410b050040c0300d011424400034504200851042003960b82d02d280c64106804105180c560b4082e00d240982c2d09902400b0003e440340600c1400c90350b015000017107610000405a000d0000da018a010080011600c001c0790011608120310507071140d010b580700c0940b10820007074000c5003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 571516627 1250 571515377 571515389
    0x60a02160e071215051003020f04090f0506030f190c12030809010c020304030b190e03030a0207020316052116080a02130c08010b03040c09020a0f02010506010f050904150807120318 79
    0x613000b01004117040034060000d40d4603582c50094549204008801c009920940c4210b40c05070340e45420a030356403a544662500071fa07085011f00715518490301d00369614072000305004800d010064501c41000400d914000080904628141c18a869418080c003000f4088074035900707035400c110300720f03201e548003000b00d50070340f03502c82d894454070744644000e1680e444e070304000041c82640c3d4044000c01b821003040034601c41c0c5c00c0c001d000340c0e40d404a403042c036040010040c1014100f81040106012681d10f4445d6000750390500031081c8081d1240006062420004000500d200e200307a040c00b140880c00466510301c024020703148840007000b03d11403881251032030b154038800290020014030002d401d81c0c0085d40c105000c2c01002c59016207500c8900120b03444851f0020209d008a070241340015028001c0270b50000c0242840ca540205801d005091031040c80500740c030890369913070480d000d00300011002026150603401c0b43d2519845016492006c1c070034041c10740105604503500e840201980c480e13617098480c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 571517877 1250 571516627 571516661
    0x504180c0f08060a1a131701060603060509060909010b1002010c2d0804030c050714090603071809060e06011e0806091903020a020904110f010914060a02160e0712 71
    0x200c1d100c031503105d054404c43d20030f884901c10000807402d283d03400e407031901905010420441c0d18200c2d503c150b0840f40c0c02d41c485020306051100412456490202c0182d0180c0251038900155417110f8001c5d0052001040d0304c2c1d0300162642d03902040540c158400b141c09011601e07141c0c43c0364949510951f02e00510301603a58001032500d2124804c910500206030007520034102019104170603a100783c1062141d0704004410580e148120130f81d45007000c2801d8000d1015030290451505182c4500520046002c03005480c54403000c00c40200019503019134000c40b1510180c41c0107503101c3c90a06c00d490001035007080307900465840440c9040703004c9126405049207400401c0341c03014030000085055000c680c03d400303502500e0100300c0907880d1081d540d40b1841c420030180360100540001c0018008440000700e041101140040c05171440c9240c0640d42c9500c00c44a890315210b0511040f8a003104802d1001c1c00804030080014889040402081c021885501c0e001e420010700e4004608a0b0042c903526100c1c03030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 571519127 1250 571517877 571517879
    0x1d0c0609040e1014010f32011704050c04063201050d020f0307020f0d0c1203021918090c020312090a020a0611060f2701021b16120803160504180c0f08060a 68
    0x9400a0440c0078a1f000c107042021921140300780300c0c000d000080318180d40725040850703c0e01551506102d5203014205084841d540382081e5005850818180089686601c0e209811310304a680500c055402200280358150340c0c41004c00305001d00c2d0b82050300c203100503100c0c03400b03071900c2d25002013510240084151785d100c40158442e02c4d0681308400074002c040a06a08100300c4100b100c001d24000da044c10070340c035902c250500c00c0404030030494079680004416071034040102c06180d13000c421a001300c0501144814903464452115040900d0540000d520031509540010283c1e080700a010036104564191501ea5641840205501504030345d0080759014140c8003030144d010100484642050f14030005040820100c258070402802e40d5804055901001c036401c03076004200100409804006000f80c2c00c01110740c1c40125a00010b04040100c8252038003c05041c3e2041d0141c40c0240703c20321004030310403840014100100403519001c0b000881c170401c29a0128000c51b600ea0140c500038200311902 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 571520377 1250 571519127 571519199
    0x106090b030d0f051b06040c0605180d1403040806010f09020310180b03010e2505030a17070203030304060f05060a08060c0901211d0c0609040e1014010f 67
    0x50900e0507210310902c00184070082608810520180390f40141780300800b46400c00e07061290755130120342c3c801e03400c2200c10000f1001c002080e40084d160035a003510485d07942d40b0305161090050301c14103080b42c41c0f4403001ca0009251031000590074107c0d4528046c00003280e031120710315802d0f4402207540d482d0351032a030f46e4100050120071030b40500c00c0401050000d08a54a03100003802e4440c1c1140d180758a0b8001040d840c107850030482d0b20214206402d1000a0203841c000201e502c90300c1707503540035010030054951500310b041d0060480d54a03d500400703503682c0c2d1602d450014000e00f412010180c04074500000601c05003041042907080e034041d040140700c83d654400380e14990b03038051941d041c100100008001c42010320345400820881090f000412100000c58102c4069642c800304e5041544c00030f200d1495584900e0211004500700355804900150352520403846d144400c5032010106151800c460603a90058900744d043c0c5500311180508070341da4090769405151140002c0b1029a4050303030074008 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 571521627 1250 571520377 571520387
    0x2070308010b0a050705151801060e130c0b030a0204140405090a0602030a090c03111206010e061e03190b09030f03060603130206030a0204031b030510051008120702030106090b030d 79
    0x100c08004d10700280f81a485940c2c080c20020071034100020151680b092003a0f2142c0001c5151080c402000200701040c0b5040d07507000500e00180c55030041c8181c1107480c60522881c20f8110003d8954100c02c199681440342d110300081d48103100e07000b421055815000401d10b45070007030901030301c07111000307004407109620b404009603c05000304031170544e036038281303800100d20104c00c4008500078411240d02401c0a0181700fa054503035510082250003400050141326000840d0541100c81590800340203210320644501d07009042c886164544540c16035444c3c6494540ca03001031691180d6240c008940790308040075500d0280720049580340c00240001078007414000041d540c00720042118280d0900c031900421031030743c81514040c8800750000b90070f005000b111100046070074004004466140c1c61034035035a481c3d9007081c10b007500e00c6071200c0c0412004c1d1010f5421001a2102909491524807156010180c90340002000c070b00950904100181c800064485c101c9480c00140152050381942c01007210 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 571522877 1250 571521627 571521637
    0x120319050601030e010c090e0c160807110a0e091b101413030c09060506090609040902040b0a06180503010e0705060708071a01170c01050a1107031a16020102070308010b 74
    0x304069507140d0020106009000c0c46101106c1c9484d12000c0600704010660301c568014400c0c0305846081082010016161052050341074015040c6601ea480c1840d1040320b1007900c4140a07030044001a0100d00c04000e140528041c02c4000300303e4a2403c070301b4258506001821820981c0300061000c0da6140900a02c14140d0305440d103e81d0514000c154860700203a098150003d440ca071440120600940242c1d10524014000c1204d409052115610004100e0700ca10940b4602843d201d510080443d107440d009244044d0f0000c4c540c60b00251500c000400014000d481c0400c04440240001901d040611500d4582c06642c006880c41d41d050505104040d4010013080740c1212003000000c1c045008a5140c1000a05079a002103441d4500f40300808090701202042400341c0129030200f04507a0010212030307a00030f40d410280c10010040e84000e09040ca6a4006004030305a00a5181405044055035200b4051103664401841c0440300407808c0380900c4000602090b05140180010f15410300940 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 571524127 1250 571522877 571522879
    0x6120905010e0f0d2c03030903060a0c170402130c091a07030f08130605070c0f06020409061707140a05100908070504021c0b010c080a111203190506 65
    0x105050455a4035503007150142c4024600d95001440307041c0851005101e107504103001480c0c0300490200b0100d41d0620f010120140060b8603e000d104d81c172a5480500690b01c006030000c0c2502d4030351a021311050054140e245035072000500521814070b20b42503014109010740d401401480307109204403150720081010b40082402e104170140006003c04690242504140d000e07a40d454542910346805004c200f41d9620180511086030108911403104440081072190041d401140d2a1201c460079a907603800f00f80090440400c145042041c030002d0b030003c00c12194212000c000007a90740c0c0395030220201c8181d06a6031038100d600e0402a82c210490391050515000f442040c01c40c1c0d40341c00081581d02616140008148039840c20041450140301000c001d200a8a05500d0506d014802000199411210b65030365596400101c0444c1d1081c441c1307551030350740302c560349a55190040c03010b000c2004001404080c0d20640e08420380845580d41600d01500014007004008a503e403442800340c28020481 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 571525377 1250 571524127 571524131
    0x801050d0206040509010f151b2d0606081b0d0b06041d1c030606050a050f0f0403080316030b0d0b090c040606051201050d05060c070f020603010303120b0907090612 72
    0x4a070603618941154020018480d403041075070714007038080c0b20003a56000f011003482700d00000369542040048102c2217130342e4400e180007103007854450015101511070740082c450340030710a10b072401c1084550210701683d049004940c0403091011412800522081c4030b00c2c0c000154a900e07a000503c0c0f0310005402c4a00100042250952030549036a141078a414880103940005800c403820500308400002c4249245401d0104c0d50403c080605140700e03440314441008000070b5102c10007000c9a0075074014a041911996407503a40e800c05032200e4009030faa00c551001003040741c5038424064480c40e244800050007240b440746407601c80d18003207400203213a1009802400e0405021340d4542c07143c58058862621025265405141c41c8580ba0b00c050700300f41e00441900390441c021401c009801d541c410500e09085585440c03a18000c1c891040701070b002500824044008020150040307800602846141004c00049690310100414240b007541c50b80c010601c00c003c00d2042d03d04c11112090300403c00140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 571526627 1250 571525377 571525379
    0x7050102120403120c170c1b0d03090b010e1003300203130501230f301f0b0a20010c0834090806070e1309030801050d020604 55
    0x72414951001c039000c80002c0c0c1100003600301c1014601c03581d5a03507042460040040c152046084464082c090142d0100700b8010403413111040c0c9910801280d86200c80030303640b082d015503c002d000b4014110045992641501c0040740114403210030501c28820202c003c1d070443e2560701c070104500c030f41009808000b250074514a100d0b4000c0c5501000642040d030003150798410700f03507040341c1820554000c0c0703042200f039041002c2c8800d0010401852a9412001c080e070350030304500010420310401d10956104010707003003801c41070082c0e0211402c840700c020400015654a445042d030003080d002d110005c3d80f175582d0a040c00040580340282042c11560b083c010345008a040d002c0b1018207240f640c180300d80c1e4440010020141c2c1c00180942c0185288200d01c4071074071000101d482800d0007401084405d00000b0950309018490610800109048415165107081c03820004100c05812000107010380281641c08504104a1203085181e0f40c040d81e610140d80d0030901000344441d112007059a02100c00c2c40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 571527877 1250 571526627 571526647
    0x40b181c1218060b0d0803160c0f050a1b06120903090b0f09040e010b0a0311030703080a0512060f030a0f0609050d090e0c161b090c1809050108070b07050102 69
    0x8101078450500c82c001000c1d5484a01e0300380240e40c9405402e90052000114440c0007400320707800e40c0d4000c4030030300041d4102405201300300c811980500307001d0100303c902d0343c0c0c0800703008000c0741000e03080b401010000703180c88030300c100da000d0803456208410004032001040000710505500010445110b440c12840350307595410301d140b0726044403401400c040000201d0720300c0c0e031500c1d04c100c0c107402d42c4040c024440e400c41c0341c001900760056484041c001140b116850f180b65601405018046d6074422100303a162a0351540040070341e00054440c000170000c1c08003080b29498400f40c80c40510300010300426140e8081d60b1103400c5074088090440c2c9543e258074010001407000d01400300440103a6661401d55071800e640d95034890f8003d03094583c1001c017000030702c8140341245002202e4581003035448c01070000c66080800e510345030341d00408003186072400179402030794001c4402510b9a40c0c2c0d0912040f4548070380b80082180c00c28032500e1010350145000b004140140c1020b007000e80e0050300010b0514075020 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 571529127 1250 571527877 571527881
    0x601110c030607050a03140c0301170c040f050a0c0e3d0c02010f0306031101030903020312010807082e09080d1b11031e031f0e040b181c12 61
    0x66041c2d00070490200d480d01a03140c0c18841c04c050031580a5601f030040c01c152002800b10311040c001c9803407200041c1d011a40500d000c00c85080c1009000c1d10401408001000c144007c000503108110103c0c20300c4412400280b18010607909020014042e852903003c900f5940c002c1080c0710102d0450f4440c2c0c840b1003404100c4101d501c100000e00e034450305160b030464400142a4030490741440103162a000003840403c0c03130425000c10000f02802e00050541e814202603146014001411400300d01d4000081404e0001198882c00c8032545012504801c500b600e901001844001e8004010b1206e20440307298500705400c5414124010302c4902c2c03901440070000c6d07041d5900d204201183c0050910b5200c0c11a034800d49a11070307010020065801e042d903116a192082c1006400010400400320119070008000541e941c503400d5001d6a085006644a16005040c401180c0903100d40030f804002880d81ca040300c1d440c0700c070184d00a0140500500c03910320301003100030b29815602040505001220324100d18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 571530377 1250 571529127 571529131
    0xf120903070e0c28050409090c0b03090d020111091804020f03070303030b131802040b0604050a0305010506040b060702031915110c010f06050a140f04090311060708040b0601110c0306 80
    0x100c0f0055407941d01c00894504a0302c1801c3c182c1d507000b00403d104103a9544201560280e451854000c2160302c11801c107a4a025900e8000c82461507000062200e07181000402e00008501500207200303c094520441040340100712003140c200c549004040b49255003c00c04550103840104800d6481070103002103850410542c100720042665694102624500200e00f2041100100d0051110348640c1103c102d006440313501c028003c030340710344542a5960f160702c03d50b006000003400701c244099503070030034a01030302080d1201402580f814180d95400c0c206141103030411074000e03004103200c000d4020240d0340d2131a081d4080d41c841c0001004500001a80d0140740041d108800740c858851000042d014212030000c0f900c40c0c403c0c1d00d0140304000648030580c0f26402c40d101103503080241900600402c107820380b001d4005034040d14049003181010b41019030008081060307001c80701c1c5e543d1040310560707450350706882c051f2501e03100030b00180740c544c4140054640c590700d480640d10030204540120b4030309002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 571531627 1250 571530377 571530391
    0x1d12100e15060d02060403060515040e070501090e0f010605030901180b01083007050304090e060f1005010509040222150f0216030f0c1d0a0e0f120903070e 68
    0x82a00d072500304071200440e81e600104103d03400c07019501c2681c002905403182d4480240502d8588d00082d0328101c043e03400100301e042c06070041c0302c4600d5100c1c0f52a29481c0c64000d01c0d0206401c83c0b004601c640324801c0752486401d004a1f045456402c1c03800903503242c0c0000f00320045a6496070380b06c100080500c1c0c01901c146225501602d880d5040007445810b103950500f0810a0901c542d00108007100900d010034000c0056544c01c56541c0380608000d82507120760340081090b2402e00c444009400400a641d5204160510582c4015107510310300b0504000f0910601c0d0016005010703d00062400f54001c0410702d0040c48072200500d0f4980412260b08020f5201c0100d0b4002101c04150041c0c10000c0c50071000c0d42c80c409494000c000903548440c0d00810f01010706508a21503c0c0000c1242030306280003d4155402c5440c2e035002c13a1203500110340422903030b0308562404c2c0407008407400e0b000108803207041c18101c00b522180309a1a640c0f0324a41004040701d0380b5200b05840011071030178809601d070043d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 571532877 1250 571531627 571531633
    0x30d020d050103061d0d1b0209041a06030a0b041b03020909010605040b030d1d0114180a050a03080901180b120919080703030c03020409020a020d020d1d12100e 70
    0xc0346042c510200d81e0001c500745a2210425a044d89174000803480c4014500182800406441810402c04000d840e110009400a44100c00c5c4001e005404070015050360010340080441c1e0380d6a018507840c0d2406000c0180f541030054040340000380c100b00e010801c070f4441c89910710780c240e81c2e40000d160040c2c280e550a42d141d6451806000314100b80c080e02c95411000d500800c00245400c200502c880000b0480001604400c04000350036841540c080a41d80300c070400c044e8580015101324920403100384030092040c03650300700000d641d0902160800449810070049801c0011031001518426000d1070102c121108901010500d40b001d5401b8200c04801c07161114400c5c03515541080c50305408140f16183e1341941010365000078052803c0b00c041d1645407074040f80d901007140059002c4d001d030f6084110b09900109403002810350007e00e0b0144003040c1d03401c8038500803071940700b5500600500d20114180348003141190341c1d420029048032802182d4812180a414498011422110071001028440d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 571534127 1250 571532877 571532879
    0x3030f0f0311180112020906070201030513081b06010f0b03150315090d090815010b070606050306041401200a0f09090207080903160e06130b0a090c12061d0603030d020d0501 76
    0x4d40c0c0800d60050700c41c6200001c610704014100051540c1c059900c00a0416482d10002008031b0038101d11508101e6001c180192a06a00b010021150000c004039499a01c40d103c0002807500141d141601103400840d81c643c40e40d01c0740b0040384500d20080000581500c179440d45045411252030b01140304141d5403000d004603644d00c880003002c1406903400524550700502d5239002c0d0b401d50340139960456154040700d6903907041911388040541503a500442d450300a4600304803e01181d04244040d01030036200030000000300c01111403001c8483c40341041d5000c42030000d000704078010303040141400810704020f00c4584d902c001520036a4841841101c0c0aa0003083d03a403014107041100782420100082d00c0c070441c1d03090a0700404400304c000c011a1103048070f46400030389107519034410040f985010b082c6164140d150712006016045030710b02d00e400102100c4010343c803541d00b40706200542da17400c6504c40c0c00c0d075620380b008043c0c414050009941404100302c940c820f440c00344000d062003610000d0203d83d075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 571535377 1250 571534127 571534129
    0xc030106030c03021305010810181b050304050c061605030414150708031b2701020606010903020d0605040c051c02040506040902011b0c18091b03030f0f031118 70
    0x242e50154040d00a042c010710010086140c00ca0a00c5e05990080c600402c407650b40d411841ea28001e07179400b0084940781d0040c800c8030300342c25400025803820074a46411942c0014401141e803880304503800390003a00b0000e1000c0c40b07807030407100603e0200c42442d42c0701d50060881e240e150459126a02403851070206a404080500f010328a41e81d4885110142c1d50a004494071006a5448010300e50421a0b80d4030702004518840c140c10341d00521503840100c44a04851310035507481004400c1010b001d03102d44030018266602c545040c4040c0c0b0381c043d00104500c4466a02c0b607018140141040342e2108075400c0c0800c40c0d444041494220f0f28000c400c0d02405034040c01404110b503170150035580281c2c02d091602d000742c1d0308280030303081230101c00c032458021075aa0b051454403190720707400c422462220b4003502e4100300c0c0d654000d0109940184086104c1007103040c8a00101841c901c001804540034910307181c80a80903403003a0345209040e090105203503000401d09580ca6100748401131903509022400700403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 571536627 1250 571535377 571535381
    0x1b0c0a05071e0b07020102120d050a0b1f11031e040303081006050724050a14010503010e1e0708060708010e0a0b1e06090a090203011d0f010303080612060c03010603 72
    0xa01031240700120a01044810101c554014000c243c1550000114034086910801c907003480c0648100100761103540c50001c010103040140e80700740c800ca00301866842c0c54a070030304074416440f581000e540045070200d0010749240d0401c8803c0c4805005c14030000c14501494540307510b40362040080c0719034850440c070b000f41101c00701a04000c0c6008149005000c09504034044034a443e8110899036184464400e02c24402d03101c0752242000386050074280104811a13820496954644000781c0d580340e80c80d282494200c0c0e001c190941c0c0e055002d202d00f540140500c45880e504000060b003a40d00ba161155106490003500355021400241458010000c04440c07420440c0c00c0004c600050200110500000f0818607142020780c04074294649500055680c0004480c00303628040d040e50905a51640c1d0b1200a40091003440c1a030444520155400060803925074030171507a0000f83c16269095840841c0c00001c000c0606400003107445410081c180c0400ca034510490b0009601a07582d07062000041c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 571537877 1250 571536627 571536629
    0x3040e16052a0a050f0706090b0c34060c02090105012f010209030a050109020102070605030f370603021203040b0d0c0e180a0606090503060403081b0c0a0507 69
    0x1041000c2441465140041020480c50b0b229108a0840c5040c0c00407880c00c1c10030200030740041103841081e8400c201480080f44007803c0b03a0040d220548155643c85c0c2e411042d10442034100d159400c000031424113810070740c0c4078901402c41034441d9000b01d0102d000c0714050400e140c00642c041401040d81104610b4844100d038090282840e0035940030400d101c9542e104100201d4444c94401c0d4038010705008d00096054070000032009045518001d09410051300030188000182e0040c000d061011440600507821a03001c1c840b0756040b030032907540e40301e0144460880b01811003a0b200c012880c0c90301a41d1542d80040802d142403200140c41c1d482c42c1704100700210074421601d03054000388010080c440d500810780300b90094001d000315441034903100c1203442c40841020150f000144c44000c20070b003124001034600c40d0030303a150b00f0004192203000c10740310032038244145513040d070140c000180024460310005030000c1305072000e040220803072100f040898011207005100c650091030341005100b0304014681c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 571539127 1250 571537877 571537921
    0x130915061a07080304060b1207170d03020306090117100606030506090f060d15090f0b0108010c0e152a030705060a050702190516090204060807030b010e0f1203040e 72
    0x41d2411915648000050000031700117000d0940e41e0a66480d561201a10520300c030170108150350380151181041c000c000f10309820030009210300c405a1001c2c901034402c49004410050070054503030320304501107004c019070600200c014010405e819403500303110f001d0300c0c0140125403404035070383c50000240120740c1c0d0b00034501c0e02d4030340c110414001d003070302c0303020b459942140c010030240ac40c11008501d01011740010900104040b6401d00c0d00c10501c08404080750503500100001d00c045809000d08075043c0031080c144540c40740e0311450001c01c42c40344c03100900e012400608003044660703800d20564260340c01d01d13400740000d0f0800500c0b44200981800402d030301c43e00c0e034042003049040c6200001d40e51900c0ea07201007243c1202207844420300004100100d0007166a42d9007490550b1100e5240f0701030b4000348146000720395402c004c2802140070340200c03201c40c04c040e0340342070903001c003441000104c11142152a40100c00c41c40c140407010010301c010000382c082c8044144450510100720300d880810301d0b80003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 571540377 1250 571539127 571539179
    0x1401060608070e3c060a05070506360f0d050903010b010c08040b09011106040302010c111507050904060b070501020304030219050304050f04020f0d0504030f14030613091506 76
    0x1899443e0300c414440c20b4004c06100040e440c84a0645036524100a41006590000f40403840000035684400108245840741c2e06031101c5494145000503207841091115642284000020302c40600460520f05445003043c1201c01c02c2000b4114981043d04800e2000009000000c8400440c2000d00600c46010400e03c3c00b0000c181540c0c45401050080d40106091b4900002d02c0c552280c2c411031410803620701e884150f601906262502030b000303101c40e80401020502201000ca090301021072400c0400c01d45030140e41003682d81c4003044800e940002620384e1f0140e40c40f100407a118030b504000d070841d54803450005960b070920f814040e151a05800c0842400002070400a00081001c0140d5044400c241c2c0c40d0010880e1700c40c006000ba0044800a00c0d020034081100b107512074094100c130703000e03601070748a80c0300d070340c11184040710041d03980040d40f08081d2041020500f81c2c00e102e84c1380720584040b1040051318801503036860007541c040c019071070000c0d6110501403000890480654008800070280 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 571541627 1250 571540377 571540399
    0x423090309090a020a09050306010b0c01060906050108040b0a110703020304080c03030702130203150915010f0206071d030a0b0403021b0402090d0303091406070302070b09010221041401060608070e 86
    0x15110002c01400800c0300c9801150300c1c0d40c00c0d4081c2484a0152030018140d62081d03854038040c800c550001d50381040c081d13003485400250761401c0e00c513410503504c0682d6012220750362a121043c6501c000303000c2034209680d0b4090f100c0280035850280c02001d11a9001e55900c902d0200d41e079103045803402125110f900100078040041c0e650b4001405030000010015880340d032406640c5820040c0040c0e130b07582000415040003042403141c0022a1030003070980314580800351500c0220395986003111203401290340c000c040314440c05200c120400c0654000e08440d00000d445d070b92410b44903001d07134084025038003100d44200038590040000040c0c41e01600c0031424107080c0c000148030808160000790900d5902c031041414008220820b407000e00b00c61044a40074140140c2c024002d50041c002074950f0102100458500031042c021560200544c5004030054507200001140b0000090400c48507031343e80c03041d000052107081c0075520040500380c451411600e450640607240e00301d43ca02c1c443c450040703c94 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 571542877 1250 571541627 571541629
    0x801050a0f03020d0c080106030c150c11190306020f19050708120612010606021b0405060a050f1201050411010f0206040308070f170f040218040b0a0b0a03020423090309 74
    0x7085a40403190b60314444039a00f8400015000342d00301c16219401d00c6804000c0c0501000000200d030034042c40c045e40d034103007481c0450f0b0346c01d0080b80042c180e5288a004c1c1d03440e4074080c41d40410341185035a620007641c0c2d80c2d5591a04983c001c00c460352604401244c034400c00c414074410990020118202540380c81a43d5407031b200313284240c2c9410380c0304c240654042080e980b80d4094200c68480480e000f00051b6803103040103551041c01441c00b03d0001182c0030342406500b800d004140c0241c2e000781203100362074142420820a050300c1050309030885000340d21221040c1090280501441c09080b04c6008540c1a10005040c203402a000c0400d643c032007004d20000a5020404552081c420318241e07080564040003140c0d050398602c901c00500c0d24040900a41c0c100e5a40031600551080340d11176118a10b0b14825201c443e23040307401410516411300003030803100b0541c001d07810740d9138000d0810794055105d500290403680240081e444510742d4204010040e141401c450390000360308801941000b6a0368 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 571544127 1250 571542877 571542899
    0x3180105070503130b0a14190c11100e03210108011103160e0102030f043b1f05131b02011b2f030c0106120b041b03080f0702010801050a 60
    0x1d0001040b0002c85e0001440d516136586c0700a20348101c48990b15998145003800c07c1d65103070740124840b840d616080e11250824020041a45041c4402010704031000158181c038005001e806419405400304000303802189005180c5030103242801c429a00583d41003401650845000103001c50b80440100b0a012808521301c01a03034000c3d981d880c00c81d04030405200100c0c1140103d50203461002c40125010031581d1010300d40105030613558030b0902251540680b6000a0610b00002c180b05507040400f080441c101d200b10ba02c485a407500540d81c296503160045514003281d900c0250701141d40b024102044038426115a091881c6031009100e0f80c0c090084240c11071610040034401d00a2840c5c0205907040203407003003461000400540f48000d07809580c925100e0f8840a05202d0381c1d481d100d00443c001c3c100814000c072070380c0c010502d150316950720755410480c00511400d00310160a050b00000c00151040010315948000c050307040e4941c01c061001511400060300300501c216044034050018601c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 571545377 1250 571544127 571544161
    0x601060c1a0402010813020103110c0109020906030d050a120e070b0711010801080616030e15010315050c030612010b09010816080106152d0801030308160c02040c05040b03180105070503 81
    0x41b54450303405c09503510061780141112100c0c03d007080c2c00401d229802c0712041d40151841030082e900d41010740e5980041540300c2001107462001b01c1c106110050f070180c800d5040c8042c00c0b1090348000f807240c041c004805e25020199000c0035803407100080782001c00c080110300c0c410401d400c3c00c000381070b0350500c807000b034580c4001003542c25811204040300207418845d801c5011b1070000001500c610294000c49900081424042510a1558400c1c2c485d603141651040620a054407150705007541c440070104204a03061032010300f060b41d21540400b85030f98503809114020b2124a0080102c54040e180d070b004200c100303a10841007a4540b45081102d5411a0651110f0700c0c42850040e4950303249a1004007508804190b95241b044c0000c0049400381c0c206034118141c0740240c5890049a440c2034a4500724083d500c080c50006079105007400c01420f09402082c20010305007001420103454a407803081075002218030100c0300201300004409a02c4c01e108941d080085032502038610314120704e83d05c4408001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 571546627 1250 571545377 571545391
    0xb1005100c0b0712060e10061119080904020c010e061005030601050d1e06050a0513031b14010f02030a1401050102030f18040905100b0118050904080c0601060c1a04020108 75
    0x2400d8002510300b4031400003040208190013080151a448002c8109542d008032440c100303550a0000105550340280300c40386000840e6402020031940f01e540e14549016605000c5483c07a0050001038100c0e500d030b0000d00720359910f03040001203040141c4070003854a50050600e6040d6400303402c2c103000315100401d855056510030303188200e120101e85060894501c0896038100500c1d504500c510801540c0e400050140c442a001800725450340e41c41008003844020001f40458a210036140368036000c01c07501c010313250040740814098000b0701c007510b0a580062407902507065000041007004074440c4600840ca000040e0403207461741c103260020b90381e4458400d00031988003002c84d601c0c8a2500780405584100c0000e0000c0c4140c003101d181090752100700200c0c0c0804a82046405080c0e940300d007400c2c6102d030b0031414808802d00c0c81c0c2414013035030390800b070800d80c0c20b10f008112810800ca0208100381c000e01c01070351602e460341d1580c10000f1000082c484196899078900c4140b2001d40e911000550f003040c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 571547877 1250 571546627 571546643
    0x906040c170d08150a1217030115030504050f030301060201060e103204021c0b0301050c0307030e0c1f3e0316030e0310050c03041b120b1005100c 64
    0x25150040c4120229002d511640704001040c0403e05034004c2001d402035034804c0107c0c0c01c418000f20b00c021030500090189001145205d652854420700c25001650080d000e01d0650342a01c801031425811070740243c000c800941c0d1211402c02c8080c0401d027081c6d0340b014105e0b202c240d4003400c2007032544440111100e0381c012140404c40c48000c01400690f24892004004d104540d50001440e4019000814602d03100641d884c04510741e08c1c1d400c06010781880f0349544612a4135603a40c0c00304c10360040c1241680e000d942d104180a2800685038620380080001070354050170302c481041c10700205140745c0303071403a021401180d4148071401d88111401d10150002c1c141120f040d4540c05075080c0c91170040c0999070401e49000c10500c0189034100c6003c840c80d0b0030a90035070325418400006401075034420b840c4039902c1e01c4100005408038a100344980382c01b4070010040161036940d130000c0500340000311000da0b5584515400d00920f45411109003004000c1036807180f240380080140540034005a21000d04045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 571549127 1250 571547877 571547881
    0xc0f051201120c090227220507030906060e011a04030528051e2104030b0604060320011209261303061e02031018020702090906040c170d08 61
    0x7003c0c50200e0005480211421034035144a00401d060325907400b810080700380e401200020076070624426034611001d150341d40120184004c9407440082000420301c8041583d59003440001441500481c0000c10112901c1400740d4105a00c8041940382c0d40000e0000407010481000003aa0204002e6080b01d0100d1503400c510000011003e508005120001d100303002e0150310b003101700404440720545111403000c0b40c00d860390850396143c40c41ca01c240e201e01e0030320b428801040000e0075041c030702d5800400074001188040d0340f0354a00d085021350f66005100c1e01581d6000e00c4035940e21107942c012442030004184038084140c2c581120118000305000003003007403600d1150382c4804580131243c0d590303002c9200c0248141e403403d100d030017000e20100d13034041010940c0d1286151040c0b402035034050440b020000c610365107801c28152200c0a1740d00c4044a594092200c00702503a1400743d401c1c450302c04d00015084600d460f241c1415500181d4125486003544140c000341e60810000c0c0216044000c0d080c401829 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 571550377 1250 571549127 571549133
    0x60901061103070c030f142d07090903050301140f010507030c0f0b0c12011d1303090f1724070e0307030b01030602120106020304051f030b0d060c0f05120112 69
    0x98410044054032428104c070000040007040c11071180254007822101c14421101aa00b070344a000440601005d506146117068038000001c0100412405050498894a83d02c4070707090709590000001b903002c1100400100701350b4500c0b840c0440c29140844000c05103e40090005c0c2c680d0145043c0541004210b5480104004403a490350408940200e4018a646000d505040f490350000350000d50980d006d60000500c0b818000302e49429207240011800307180c0d180b00007000e4900030240c003681000250382c0c2c0040d010701001d1501c0041c4c80c00c10740c90b00070100340d61041494600342440d80c3c1e0340301c0c0d50340e0106001150038070b10854000031a80350440d80f00035000c0000e4541001034002504c9002103d000004200e002d0303000303101c540700c14a03a001d140c3e0790f140f009903128000c5100e05900544410303c111000c401c01906100303950130609000920003040e0f000b207518000142400c8858955981420310b0a5800031400c44000c82d083c0b078901c0c03604010b49212903031450107108a08115801000302820 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 571551627 1250 571550377 571550383
    0x12040b0703031d0f01292407080a0c060b0f1305152d0a03050c01030f0f02030403020705040506030a030509240c010203071403130b06060c070b040e0f0609010611 71
    0x460700381c00210344c000c00f40e000445000745040c1d5001d80c100340f4841c0d4001820a50900da0035071301c103801071a00900850410301074440f55224998100d00450030000000001c0c0746e01e0151855a207142e07205281980135151040844101203003103032042c9040c03c82c08480c0d80c2c3c0c83c2c84c80c03519108544800318040d19001301c4071001c02409082241c1c000b68494035140003000440b98807920a881222180054a800e0103002002c2c00602000e0300c01d4102c001c5c480c0d00303940260400804644006000640078081c101e4000481c0c00c290b4044006801c00340e4100003e107418003415030001001c8003c0c1c40900d407240d8021708030703200303029505001d59042154a40074482c141d40440e040a141c201d03040d5620380303408001e03000f5407044811703002048404a8544002070240241c910600820303860202803c1d41c2c0c0c848a0bd0440024255940840100a6425803500c14098807000300409a0100d41301d80c204856000300c000d004040c0810161414104506560b42c625001c1c11200d00382020300c818011a004070341 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 571552877 1250 571551627 571551671
    0xf1e09060a08100504200f1b0a060e031602120111031306200307230a090602060906312009150f01031116060e12040b070303 55
    0x5400035011030150710035034102116501c82c000703041c5800c81c20740c0c5a004001c101c41c04030300048448034a086040500030035000060200512008106007801c02031010510100f000c0c211080b01c60f0080c00891040215500807001d44103d404051414404107e2060340e42c030090944c060710466401400e106009001e500500d250310718904511390b81c1c80c011201548400c584002250001d1601e100d0178808422108518081012250803518548415200b11801d101045c0c0c1842c641e10800081c441c0165240d004002e48030b500c2c0c40d190b04580ca002c502905000d0300401c0300301950824010005440c40c1218401c4e042c45400c8010189050080c40c402240021200c0083c01695028811000c040c10840221041002221010101c0e541d01032030204541083c030302e09030040c558211000042d80a5040b101c0c2d001d814643c0c07603041010003a90803291078025041507803e80d0380e0b02e4000400b0f010a010203150b25464175903035441e10f07203446140c281500c180300c4040c0400d40d0b20100140c4003d90740b04210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 571554127 1250 571552877 571552879
    0x140604090b0718090e06040302150408090108060f0a06030e0f010608030304062003040c150f2102070213090218010e22080a02010501051c020f060d2a0e060f1e09 71
    0x54110441c0c0c4043d030300d1000b1f8034160003520030010090006145c00700103600c02c0c0d510402090510b0705910056642c0030307024007041d90010000c210f07000c0d00c0e10b4040b05440105040d80c1c0c0455100440d07640300c1d044c021404139001c0303180d05010050200f0340000048076041540184000f403001070080d80c95403900b4140620000c101c034000240003e00002500c07900c1581e50703c6200c10b07260034040b039043c0c44201200c00c03088045284085e8030608000b0041001a03ca00780c60b001600c1e000c0d41c1c0d130010300b0140002450204503683d0b150001c007903003131000d07040392040c1c5500c403140b40340c0d410100c1003054010024104a0075030b107801d00650310080f90214240440340e00070385a80e1104403488000e07000e07001c240180d50082d4480e01654020000c103000c02451076402130501703034400203080c0c140201c070360002401c00c11164960032000b039564a40103501f03003110303510801c01c100d095841c1c000500d0460300a04103481460705001c044003101b42e0804480300650449035517a0540d041905095503401800700c62 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 571555377 1250 571554127 571554131
    0x220903091a0912210a02070609050904030c05071d0405060f0705032d01032a0b07080c03090d2001020d0e01080403020a0b07030614030d050703051803070603140604090b071809 77
    0x41381e100001e02c00a03001e1070f0380c00d409580340d07241c545000715480d640b41e2040e41c4d80802d201000c00c0200340034605c035100c07550080060300d403000c1e100e0103000c440c1d03141d08c1000c0016444480402003840b806100e0300b500800e08041c0002d01e4144120005e1181c080a444202413101e8580105400c1044581d11442400c00b40c80389a280e41c0d4038100050300840f80c2c0d0482c003603151302610040507164080c82c0340d000d443c3c65911032030600c14075071107207401500076500c2c07400c9a120420810200e6915130001d851010700c102004500c0400070584038104440d251242815540040e26981340160442c02000c8810785c03c0c60000b0180d551410100d03d0840402c0018200400001c1444201e942c9900860140d13008100c8501112580c0020316a60f9944101e850000600a000305c50006c0e2060300180505c1002203115403004103258002418499a0b41c40b948c08240c0d1025801e06141d80c200e82d055004000f2a020080000b25071522074920b00010540c0c01046444040001e0002c07040314403d01801da40582 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 571556627 1250 571555377 571555423
    0x10311090a0e0a1a130b13030e060c010e0d080103030509060a0c170d06051c031404080f0109020f06130312050d0608070e06030304060e0906220903091a0912 69
    0x8800b800701354441d00058003030041c0002e0800541d101201c12080c1d407081516120342e075a0361010fa60f80c211004124104003e07034a082350345030b8600020f4802241d000000295040040825918040e0107801d40f6050250500042020a4008041c0c5075122001d4a003142c0d2001002d004403151030f101c15005100405040c24120180840409840088080001000025251000c00548501c01001024600d92511401001a00c10904440e801c03004604040c101b60311001c403541410001e9044091030382d503500c03d1b0030640c0741c03001040c1c000c807805076580d1385000103a0700b502e08000c900d4040504140f60311100c5a60107403050003203e0368804100c5080201e640c913a0041034807a8601c0c402d10840e0384031076000c00c11601c3c0120032501107904a4950310310a00550003032000524009004690103255001109650b150001458201e510002000100c110051070701070903e9003540c12510103020f007003001049c0200004115000d4072412244035240c40d40301001c0e189019940c680a404100700740807 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 571557877 1250 571556627 571556633
    0x160509060a0507051f1104030503070f14071706160e09041e060b040c0534060c1701090e0c0607140d1707030207020915030109080a09051503010311090a0e0a 69
    0x2105903c140005d010b0001c450b00d4035518001e07002d94040070340550420800301d800100c43e8101d208955108000e101c7c018259090384604141c01c1d94004240114140d4440024080a000700e551246059140b003407500c0d500d1a00406203441010300c607000303c0c1410007040c240b140d81202403100a1090007207001d054658500303100030b4403e03503103100c1c080d074200304488400f00c3c040c00a40c7c1c0d5100c10b0842611030454011006610080c00301c4015007034010315400c0350003280050180c0300c0031107c0368944240c8180c10a0740d903401168140d200d41061850219044054038000c03614885159003200c10a4541c4180d003410860038203004c030340b0080d504c9030315031010300700c0d4000e102907600071a000e50001840e5985442642a441000742c025403000c3c480c000141d41891020702d41d560318178060000100e000e541e0742c1e049202da02024030f92003c00c40c0085e04112901d01054015459032800040310300b113503d10382c0d0f20013280c070803000c2d40f911407018600001d1451301160321055652600341c0c00c544a8500c182 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 571559127 1250 571557877 571557913
    0xf12020c010b0a05090112021c06050c0406023009010315062a0c05060d0e010c030b030c01020f120307050d0f0603140606032112180105160509060a050705 68
    0x700b00300c1e00500200100244500e40100710a040701e15040d500e003a0f000304c0c1d6003080084040d00340903840c5003d05048110204885203d0a4400c0d039080d01556961818100c1c0a89010480d4070f801a0380210f01000d4041c19880112210742c60508600c2e160300c502c080b20050303018020b01c4651148440810340f001414540c040d00c80241c243c0c000c41034412881e24080c0020450380240f00241c40c0b1050003100b00403900f0841e00800c0c0e500440b840001c1e94510000789607003520303035050f000c2000a4564159511302d2605020000110509000503c0045030800701c0507202d2480c1d000c030800b0148040300203007c0900550032980356185401042000003d0905c003a0b000380b009000c15502c0300701d0352042c10300b400400a8182d004a0000b0014846501041a0b00c0c034000fa000384540c0c0311200502084403c1c0740c8492820740104000b90041400e07643d456005421550003d0041e0603a18801c09510344aa82201c1203da141001392a0352b035440341e40d540103540510418900518601c250f2031200b110784105 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 571560377 1250 571559127 571559141
    0xf0910090606090308180a0302040f09020307080d0e09100b070b100b0c03220b0a0207050907030501051e032e0c0f09181103090a03030b0102070e070f12020c01 70
    0x1000100140c03600c1d010b04440000007800001d100311001c111020030045003200c0e08008010040c10076100d6502d95001c5419603081c000b43c2032007107440311549000c41c501404010b014200250082c0480c2c0041c00c00200b03290200800c003405296140c0104030a03882c005c20b60009030100510b95235848030b00f882c1200d64514101d03036a5205811815004c00c4241c44801201d8500c0e0b441001581081c0700032403420182548a030340e107100d249040d0300006540c0c1c100009800a8034564014055240c0b401c0700f03000b21001c004140c00704043c81c1074014800341d034801201e004000c03240d0b680d201c0c05c41203503404246044825110b0030341d4818003000c0501c0e030f000d4640c81540b01c04500d81040c001c50954240c1501c04030607100c4501c022072101d010921a100c1551081824070615080100b2803050003000c006655105a03508103131354100d801c0e217405160300b500415861020030f100030916903142510354805500082d0480c410014803032400100741e8408c907029803030110401011540d4640301d10443c1d000b000c1c0c2e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 571561627 1250 571560377 571560389
    0x9060219080c1e03072109020301050109090803040308090a0507170d030e1905070b0f0714070302010f08070302130806102907031103040b0403200f0402090f0910 71
    0x50400080e014210400580d01460300342c50360700815112500103000550030041000c000c2008000e0ba86c014464048458844854010300005078078a80b0700602d4250761058001c048080e040034800000203000d0340840340e0041d01450003400301c0d1915036209090079002ca13400f4146100e03400740416030101700790811220884c00c000300c414440b41141c05030182d40002085984c3c5800020f500d04c04400701c05622080740303100c0c80a942a10b40c65045058290300309021494030884049280c00400c401070b902d51080ca00800c0080c082c0d549550b0000380000956000c3ca41044034003004201303d2030181c2c068503400400c2846022400e80c40e48040b41e80d031081201d091080125007040080c3c800380c080d9207064400c1d0f11644d081c1404010b0205813060307610940d811410440301480480c4901002d001078006028a1010a039580b45103040c0040d00700d0002c84070703e4101000c08201c80459540b00b42080c55031100741d40268a030380c0c1d450002400414a20b01d07543d0401040e4040000007030f5041130401c00d0b908 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 571562877 1250 571561627 571561637
    0x40905190501050d0f021c02031e070605041413060b030403030e010b271b0c010c031a030309040e0712140d0305090d0c060f020c0d02061f090e0109060219 68
    0x80c1e2002040304801c26040c014281700090410a005410616a1100e2032518010b100710303120b420f03502003443c1008003518000302c10203451000851460901c8840010700c40b504e050f07410141000d6500411400d069002e0384181000801100b6101c036640102c80105a8407009039100d04d09410040c010700a1003c01420302d510303080703010040e0300d0a41ca2402165110341c1c9640ca00d28400035144004170303009070a4044404a401008070b04207009002081038098110011550444044006e0103a0b480c0d49869000d004001d802c140142d04c0001c207035500c0c94070465005c103500640c500040e050042540200c103142807511094410300c800c0100342d818883c0b0380002c58164401d80001203003119000c2d280c19405801c00145080280d114a02a03050540990000500d00000e21a000e00b02d03808848030307800c540c00502041d0b40e40c1c5e03010f01c0b43c01ea1000655107400756400301207280c40256820790080340741540d510003030080418400d5210050141d48080110350b1742003100c0306003207101344560f81d10000135 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 571564127 1250 571562877 571562879
    0x305060a090203010f030f080d050103140d02030406050906130308030a0c080a0c0e0d21121b02060106031e05010e09100605030d050306010c24140c090105090105040905190501 77
    0x80e10b882100c0c1214044e03203045c6602c90440d030b07c1a10014600c8070683e8214800c0c844441950340a10a140c000c40c0702d15400300700d4000b07035840c0b0707070420f422023841d9025034100b8070042154940000c1140d070303049800c842c0c09658645225010124180980014041000c044200034640c0348950110302c02c0c0410340c5030840c03a652814140c4055030000d0150340001200050300718918140a0000b8041034456020241449544108040c0381a8030324011000100304080c4203402c403036613201320300010310145035958800540138406942c0310010321940c42007540e5040012200003614501c03400e10741c1c05010912286d69111118500b5807001e40d034030865030084028602c0c00c40d449100c0c6c0000c840002d8042d0070300701c00c0210103981ca03420080ca5281401030541402c00003818600c143c07541812a81c405248458075040703100c4c2290383c1c6c115400e00043c918018402d1440d40701d0300b59440da10742481c2c00c070380c4c4c1c02650340101c40c0c0c1c3c040c55126040362400c080510403803545584082e00105d1034000304000c16 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 571565377 1250 571564127 571564139
    0x6030521040f0b03061c08030f0618010501081807090c0f08130308041410090303050604090b1902040b031003050c0103060506030a0c1115040b0615030f060406030807030305060a 78
    0x3622680c0310340341d00101c2d40ca8041043c529490302441d8418001441000c00e034100001e481000d0042032030031035401d2400400c0080c0640410b076017940014051701d800c8411508045d22010014040c020103040c801d0b4034000420406401c2c101c2311808040300c0540358090744d0b824584003d01540300a07180406c01c0c244803489254800c80c141480350840b80803c61120102e51020348400c400500155813281c40c0d80c548820b449020840250144001c00c800100a1000c0c04e0040864030040c000030300c910708042c040c20224102900d0390b034100c0511780520844c0c2010740b903194001d1085030f000c0d40078607030084204144410420f940c541101c1c060750a82c2e02580c44600110100c500c507018085e480803080c8080b403820912640b1041050754581400640408800740c05840d00040c0d03441e41603c201410208402c1100c071030002c54020702d080e6070045640c0704602c1c41d0021400010601065051100300103049503990ba0440030085130410120755444a841c180200500300441e034190140503682400114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 571566627 1250 571565377 571565443
    0x9030f1e010e0d030903050904020f1803030405030a0314070605040524010e04060b0a0801020d020403020307090b0105190c08030712180330050a05040c0602010c02030a140d060305 79
    0x1030144014064050001c10f41001d43c0101041c52065081000900c903260031511540700410001081a402a8031203605524810818000203050342c003940091104012644000408045169260030041280c0c0501c0c1c515031910b009a08026100c54104414001072100108100e40b100146004180c582081c601908003695828440c24540a5003100003034080350aa60080b040700e1001491404180c1d9240c80399803c2ea00620920710711a030b0700040400842c50108a0301e4000c10038003d091011040c0310001801c240104840442d000350071103840c155441c03203511189651540700d8070b155203908003910000e00c024010805180d85d54a403011001c00c1420200d40410603690650f40d54102d9220411051802046d003204e603400740011001c2601c1c41402c0e0b001c1c8510584405000041626090504a10510242e4042819a4986903c52031007503404070481d5003c0c40b207410700c80f20305030030f00b80b0042543c42a48001c03a50319103008000700821802040c4504480c1031040c103540000c101802c0114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 571567877 1250 571566627 571566641
    0xf050319030903080306010c061a100809030a111c081816181e02070507060504210309080f010b01020d0f081807081219030204080a020909010209030f1e01 68
    0x22a00b186010800180f48000071a888041894125040701c0160b48400031340d1f044801002400c6191417500d40c2c02c0c107042c500400d200c0664a0720140c0c03401c01031085d58480c41024004810007442c1e8030340c034481243c00c00030017050410001800000c20040d00008101c41e405940004c060000c491801e503580c000050500508006040d690729014070700509104032030001d83d40f06403580d440b04442030740d0350f040107a40280d000f44070102680d0f81a03a40f40443c201a82500210103000081c031060000003501d030b900b0305402040410b0703420059100e00301580e02004031f500140e03683c810440f80101d42c140640000c5400e503c2a000c8400b103040d000700c01d6451080c0f140c0d040000656101c00600321104070001e6102200104081d1912580c5034800b4600781119040b51015001c0d002444482c2d00110500f480c001100c00d00d0304600b403909200d04141c40301508940030b44248846c40200302c00b070001394111115204010200d410741102d48003a507481e08040248010b048180b500141c6100c201070040203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 571569127 1250 571567877 571567883
    0x10801140105090103090c081b0901080f0706030b010e0405011d060616030503040c03050a08030103141f0209010e0a0923090303130510060303080f09070e270105010f050319 76
    0x80c2008000c03c01100200366100e03080e01e2441940b600001d81e820140140f5268034440810110301500306000e0101c41001a400300c1c580e540031580600b005000403038810b0650b030710340c9000700310b01c204100100c85100450807000d42c8a403401c0300001b8181402044050903908101202e4000c2d0b40340c1c4d0801c0614000d4405040b1024205080280020b00c28001540d210784562000310403643c6984406103020b07280d107000c4030002000801802406400340c6007000c0210942c0c010f25805903c14802982040003020030b0f80b00c1078020549080c640c1c050681c1601d6600d025000e4074206a9609101001c1e0800302c0c1c4000c4810142666107043c0192034080905c40d01481000318030395200c100c00cae1800d5001b005420b90340e43c06410044202c502ca203004000003580266181a1242400140f803190284d001e031900e20a940581c2c810481c026286004551001c2c200880f4014040041c213042c640c600e01d03114200d11940780000109900d4603003a0f100090705c40540c201c503070882040594501002b2500030103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 571570377 1250 571569127 571569137
    0xa0501061419063203040803041a060a151e02030415030209330304060b010f180b030604061206060911040b120621011a040911040510081b0108011401 66
    0x10515090540380714094281c07031210705010f04600c5441c074130040d07082500c0031542d83c403001003400180494420540c00101a25aaa840a050090000c0d031688170600c511040100403404030380b02c40e070084e00302030511142e0342074102401b07900e08002910380d40207015800d4403406140c03025075414400e1084c0d41c2442000382948411a099000c2038514170044014000300c0b030200c2d1000f41504000802442c09a8801c00001c50b2003c20803002502080200803820100441d04032000301e424000a403403011201003071001a500c0d00c41801050250190781c01420120202140c072f03c2c10840c00350f018500311120351008000040040704800c40e0792203180308903500287c003030014040c0403134283c0350280c018600901d05d00213004110411041680390540302d4015940d90784180c2001d607031070780250481000c01c5404000c98510b80e550356118201c001580c9001e141c0d1840010342507205140b01101070010300f012244154840200301079a046400b10b07080c0014816170002a1540110304041c049680503114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 571571627 1250 571570377 571570397
    0x2010e0c010801030213060f0f0f050108040506060907020115080304030515090a121b0605100603050c040608040f0f080307030605041a0907030902060a03020a170403200a050106141906 81
    0x2080038200c0c0f18810841b415070748400000301c2000750503400008225400b402e9040928210081021001c2640001e0601800341c040000140d40441c1c00381e800f1008a0300c002c403540320174a0481c014442d040c44170800d1100c0a07070101d80745200201038002c8a202c1c0085403800f03c89990302c0801100300740e0300759000b0b9004210b980c00050503061684110700452505280001100c01c1c040c80c02d004204050318000e0799070b000d200300f804da055400c0700580141d00f8248010300b041d507403440452007039101d08010800a00081401c2000c0d02ca00b2080c0580c1110005903041040c0c1800c2007507502c19100303603010900c0d00f100007071241418010301000d0007060010f52003241c2c0c03110501010b460010842e030b04150b920104200143e44e103078080d0003422802d41d00140c4480c04a50082c02052520030341507144002c0710100030009074041801c0000c020b403840503d810802c0650801d1810351520f50042c559400d1070340100c0c10080c882c194104400e02294210000c00400340444842c0b200303800b400780041d044c004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 571572877 1250 571571627 571571629
    0xf0c0c030f0315150e030c0a050d050f060a0213060207031205090105091503010801140f280603050c09010902030907210209040b0a1118011d040e0a0302010e0c0108010302 75
    0x107246110409681404214a43e01d01c1400d00c40d1110360300151880100320b4000d07076080e40d105909400d00d10b4194018501241c0e554000344031909140b0409114245021142c0200081404070000d141ca15108036245c0c0d081c540c0542029400040310700c80300750340c0d0030400100a07200048290071680c04c0b0a640080034460b0400325010b03408070000d941813203c1044114800c1e120308120310418000b003181541c40e941081c103802c3c25500300000b29200d0030084400c0c1b040c46080c031500b554114009206068841e507241003403c0070b003070f10051401521032912600006204003c2140658608120b426400d1603880d40e01100c01ca01013a60795440300e40c007046089c0f2108480c0818618080660b045455500c40309074000342d2040300c1110100d908074030910034486140d12900400030381103402280c150410581d10309142c03108980d1421507040068842195181a130810102c000c40764001d4003d07c00e0490f2010816500e205c0e540c0704800643c40c003020b40f0741805010a00742034150050352012a07992841e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 571574127 1250 571572877 571572887
    0xb0c010e0a240615020f0606030a030516110a09090606120305030412020f031308010e0d020d0309060f09030e1002010506180a15080d020c0307051305040c08030301060c060f0c0c03 79
    0x704820120380e4510004c100d42c207200e100050001a03a80c014149007142c8000c031410004042e1420707010b54400010040004d8008065812400500c1c0c01000c82064a08203030541c83c10480240b0f80108400e41d0101e0014103980120400b14020310f401d0148a07510280c003509103400e02e2018001420074000300c0c00240700711616504202e07281c81160000c110003098030f411680030342d003142148050001c00304502c05081c0200301c0000900005040c61861b1080060341f2800514142c00c1007694400b484000c10080398480d1040341c070640410000b9555610f405484000c100c55a83e1051300189214940301d8414011144941e1015024013aa10154800302c0304040303000e00503d03640c60301c0d45091000032001d24641e0000b0a180c030014402aa1585801f9017040c01100c881d0340240c22140082c800b54507000c0c5401e544500341e01c0009501d075201c0c00c0245152009401080d40b5010000c000142940d10903c00c5250302e0245000300901d03102004480f0894105929000119040c0b0040c070300400c0c090 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 571575377 1250 571574127 571574183
    0x50109140d08221d0c1b030714100911040c031404030801150c080f0304060b0a03080a140c061512070e0f0106051606020a0c0501060b0c010e0a 63
    0x20300442214000307940d07106460f401001c00104411821030420840d048000d021100418990789000b04a100380c031400c0d64418001401c0803c0d00100003414954002ea59019444241c40b002c144c0783c0f902e500d4074028282030440e134030180700d5100d0452072155603007c510500c02503e50000804640e0702e040424403008c0c0520406c032a041c1662194642c11010310020814417a41c403e503075482e019810300c1042c0075003c49142c1d942080081c000b00f00300000c0e20110072500902e21000c1000c0c1c807990750345890406020124a180e410640c18603001040101e440094070140803d510303581510984500c0c22203003800781110058030760303220380c02152611400008150b41a007000d8142c5c1c4074030311442d010030b1920701a584141c554099610801c00100e10040c0c1c0a03014001914101d80380c40c419040340410b00d6035908000d0314070b030b90005462200e140501103a40781180d010740240690380c0c1c0c940310140c072a0000c1e8001e03403580d420224442e04429001c80c010108a52003505072543e0551200c0000020903e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 571576627 1250 571575377 571575379
    0x21c05090304050d1112061302040510031a0f0106020c0609090705090a06081f4502041d0705040303030f020f070605190507021218090c0a02010b01080105010914 71
    0x410000400d0f9900c80071110b004c558040e00c4181c280e0400002849642c118a244502098000c00141310034040e44013059612590110b07004101c07a01c4024035183d20000da07501c0140203c280768090300d908a4005101481000d203c400844142c0c3e07030712400d076291003940303484c41d44c0100d0030410201e00e0f2501070310036034124030a8a0440d041c5154000460601c011681041001c921160108940003003400248054248070b108000f005510b040f0244d11807a410040c0c1c05074414050a110400d281100d05901544100c0c000c01c0b201108019400402980a401850245583c0d01684082441c440d41d51500908483c1d451603e032920b5030f2011002032984044104c0560340070041e80308484800e00c00b8008581c0500f0300016182071503c40200c404404505010049040400704901aa00441d03182030410400144980c1c8440c0c0a410494101070030300d80d15807020385001440000f800c031101a04107150f0305c0d002041004681e600544000030300740708003400a03c0300e000074041e44845604103c2e00e620 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 571577877 1250 571576627 571576633
    0x1080c0c1c0e0a080c012a2307091407030903020f01062312030a14041d1e01050f04090f0203070b0c070e101205030904090321060305030d0c110307051609021c0509 72
    0x95503c4039040400004234011500003000c403221580303014800c40c0005d0444003010051038500301d2007242d20a4000740350701f0a041d07035650107500b410700a10401591a201c00020400c068545204006810a000c540c0d403c0d0181d0b0500e0684500f80718151071803582c0d10b0001035042042500040750748001c0418440c2d440003041c00001134046510310b400d10060086007500d100d51400001100029640c4004014505482c000403c01915820101d840ca40c1d02a030f030206100d001c0e030a040f07001045070070000b50188100d01c1d000507401c2c604409031a14160010a8a00c42603480b49030000c1200282d0b00807060040c8507c003004200c622469044440e803284040e0ba0400c801c090026003242d00800301078003c540c6480c060700d21900008418945240354201c108209425611060390703e01440700e9207590150348514420900d8002c41200d5031034034100701100d55824032441d2040d20b8407082000702c0ca02020100d408101c83d2070600039941d0100c403954840085021444d01800508009080a69180 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 571579127 1250 571577877 571577957
    0xc270603070e07050319020a090504110f0c070305010506030f060c0d1b02010e070f23181f090504050a0f080d020403061e0b01080c0c1c0e0a080c01 65
    0x80c0b034440c6454451803064450f50740300c3c500b026008091444072107180c44150300c10804001040e42000800c416a901a90000355403000d02151003128401c040700381070908004200c3c112103400010b034403015a84200d000b8005902e400040c9130b43c4002014a140098100c8070014004070303458000740580586400010405072000c600030003070028440f1014005035100d100316154660100142c400a10a805000304510b1a190410019040413070300c03e081101d800426007507981d00c0e144c09400902c87c0580c2c00e602428400001c005803044800c0783d51020b0401040040c40c0d0805200c1d040c4940d80007400751a1209440d070f101080c0d44580e240840354480700b070246480c4051544081d01c081c622914000500085030042000f5482c1203440c101e140509008400c01d10b80da2041000350000c4810350a15100d0071b40c01e01a41c10188200704c50303103669140d10442ca9030b01c0e90104015810354415900746641e030f81c03140001ca49403c00c00700014042140c041c090840c24142d1907109101c4031a1b0315900c01c00c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 571580377 1250 571579127 571579139
    0x13060b0d0230060c0a1805060a08010f08120f07050a0c0b04030203070e060609060d020d0f090605070e09150d15050708010807060c060b210601080c27060307 69
    0x1a0509404250380005442d0008840c10310350031889040c07a960b0000307001c2890020b0003150b079441541403201c02c1040c19001d440780c0c0165144c4010250600501c940d480d4102c020340203000340f00912901c1040c07141c460b0000388010002c54046020703011506c0840c030300707240c200b00c51405502034003085502e84960303000c3c8004a05003480203409044000c140d2a0b03264510300401d460004560810003000c0703e00030030302c051aa504011103005000a55030313903440b084d40c40040f030024041c24148a00c07031400e00f02c091040c0c04a9034072080c8510322640e0704200c0e41c3c035848002c4075411140351f0350f1b503080032540d0042503550340104e000c5081204028940c0340c5046548e034400001004401510380c909481d0300c1400800303500a84042c4c0900000c1c40180165807030404014001d0a0940002d0076540d550840a400ca469480c0c22602030340d0341480c0840020340c40d00100d50303598005d1081182501070103042000900c2c040d14030341010314804d410500100040181e0740010000548540e92510442e60000781c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 571581627 1250 571580377 571580389
    0xa0209012d0c020d060501090203060f0a0f14060d050108010203040c080102030411060d020421110111060420040504120e0a1412030c060c0a0e100804030f03020405060d0207050c0913060b0d02 84
    0x20702340d12080541c80c4d0410000340000034100c0da0f030540c0700d0041180103119041c40a0134000881e51594800b110514201012412030311400090780000b500b0700c0700220b035000341500214000da1040d494011382c156603078140e5080340020f0703c009000c10008a120011882d00d540034041d03101c40c4a400510302a078a08028141c07281250303e800100f0840c8590b0b1043c8040351055191150081c20444085900c00101070b0f155000180300a000900c08200d1407084c619102d03210581102c05041002582490b050003210039400d0302e600300004095001035042414880c152000700c03601201817002e8854040c0c00c102007241070140c00d009034801840b4103408404200310090140c001c02c1101a503d0382131080c001c0111803e0325200d40a003110b100c041c50030b5540161402c1e4000d03010310304814411118001100640700316402141d0001010809102e011825401003c5461145080307401642144013402401c80003190a22180d4016542c5c401c04218103800601d1210307001031486000220729800501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 571582733 1106 571581627 571581629
    0x106021002070507050a240509031906020708040e0f06040c052203140123091c0e19080606040b09061c02090a0209012d0c020d060501 59
    0x144071081c48084050100140000310707103642d4203d4003003010209060850f5111600400781f000301c0c0110106c4000800c0030b009000d0b20b0a6a02818814401069055a07050f408101c0d42d00000c04034801030010702881070130403800d410a02c069865441009080c41e010764903111030f8030700042c1c00c181907591420503094000039072111080500a005410340c00200b86805040e880d400d42c0c41c0641100030401d0038000400c1904c0121010302e54516410741e92503000d50407005698044490b60750300380e015064503003002d61200340032001082c04c4d621180010b5281071566603080c0400701c03050104641048049400f8401c0410000020f01c07090790103030042c1d201312484a48001c18004200e21016074503001000707030000b40341000c0050003a51050420f98000380d46d0500f45c49003800b07150b8a95141c2da1000320032006d11010a0307800d641c450250401640e001092403a241c002405500540b8 = true := by decide +kernel

theorem cover : BRFrame.Cov 571402877 571582733 := by
  have h0 := BRFrame.cov_init 571402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 571402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 571402877 ≤ n) (h2 : n < 571582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
