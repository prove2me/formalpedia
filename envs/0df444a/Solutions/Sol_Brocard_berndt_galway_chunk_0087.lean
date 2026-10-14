-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:45:40.344709+00:00
-- url     : https://prove2.me/submissions/fbb03844-dd54-4a40-8b92-6bf87a2f00fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 15467632 ≤ n < 15647488 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 15468882 1250 15467632 15467651
    0x10e0109380c0a060b180106030e030409020703080609010605040f05211c021501030c1e0b040618050603010503070b03040317040309090f050105030c0d060e030d061703070213090303 80
    0x1c95002e0501c0d09000e41c043d2400d03100c140380c03071402c8880120791300c0e01510342c019415080c50161804141140da007410f0101d420781000f00401d0a43c40350390000d1005500c04204103050507845030fa41407040754144e40318034490342c079500107a6481c06107101d4a210919042c005103d1070800e41c20508000b81010780131142c170f912080c090303420024080109880c807030f00c040d00502041e604010050758003698003500c0d001c07941142c4824125400901881c058403001c2c0c10085038904141607450001d103103080340305032a59100e00004040450165414151507980180410540340070302c1102d0480d4801401800810720740311000700543c000810035818480d11600301851030782c1c1c00c540f043c8901e02c241d903603189041c00e00302d100044903003031061030420600d00b000511158400052003a58034504440c0d00180860500c0c00c400a07050008880c0c40300d002c042002c3c501c51f0019003001d01520710120040c0c0700c3c411110501d59890082d600080d61002200000f03841c50101a030100d81124060314001c6103086d44d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 15470132 1250 15468882 15468989
    0x2130e01080109020306070e0f040c0c0213020c0115120308040206130308041706040f0201140c01150503280b04020607020402190206100303020c060a09120c05010e0109 74
    0x241c0c88031a1594440403102d00710b14050141507403040c40c0e400d00c0c0c801c8041c02000301c1d0405210350500c0b40510f55800d100d052140c0144103443c28940c0c010726040000319070780c1400000c5d42120b06202015030030050130341074601c403026808064070070000d584a4448a1524221020000500242d81101d020000300394010048100c40e0003071406164095030720b80c135016081902000ba107a00260b581c00190900c800a6204a5821400b6409180c40303421000918900c80c040d2003040c0240c08503601e080c4000d000d17080806140030444404400351030030701381d12418140b105028041203005100140c2000c10016034102c00543c1c22500127003013142451504d50128040307900002c0c0110050551005080110342d04001056205041a04500d0700503c0c5a030040d59030342c010340f500c5100d0f001c0841c5100390284592010001490722448800046e0481d0805a43c000114000d05001503540b5450103441d502034814042118031903290100c098541c0d200c000d40d0b4000c001c08000c0421030000e0704482100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 15471382 1250 15470132 15470159
    0x2131206020301030201080a0207020f010c11100201140702030f0301090513021005030402090907050d030302070f021009090f1401090c020a02030706030b130507020c1c0203030a0c110109180213 85
    0x14819400140d0b03c0d410f5000150554900030305081c6c1c02030040003d0001030301c0c1e040303490b02480350a091070490607116240c08640c400352002020b401c10405a018044642d05402444459002c0c5108800c603071143d800c120303200c0c801d002d080c034201c1804000400003007000f54099648a0841c7c810110401119400211203080104020000035000710500003546800310085412203020401030910703510301004203078185030400019040c9036002c1303104814052a048040c011f903900805038080341c040c900f4041c0c006000c6000e00707c900c0d850300000d40850701e0310b8400c0008240710303081030084a03803910441c1d201038030802e0610030440c041ea4450384010b0724100180005080c0d280c9021507513040880c1402085074007140701d10880f90074881071260035500400c200c4c0e6046803e032544003c0108c9050b031412482a0800025058840064244005644100c2d030241c2d41d803084510302c0720000840b004640d6500180940b6010081c2c42c8602d21031400e01341d0040c142e161108101c024025601d203040d08411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 15472632 1250 15471382 15471419
    0x40305030307090806060406140f0103090f0303020316030204080604080c010f110306011101020708070305031305060109050a0506030a112709070302010e01052b090f050d02011a01120213 82
    0xd0701e030030030521003a602030100c1070781701101f5101080000d141c607483d50035242030440c100d8003518150449200c6079120760400401c0d03035046030a2104568040c60300400a5000711004209480710301c5000d1001c4c0d02c079008403400c840a183c028002510f0b5902e83c02003d5200380c00303400da41c4d0350f03880e05002000321038051440e00303994080030103489203403000025045c1c0e480b40403082070b964070400540d400540c0c1d5005848000780c0502e4142d440f9a01d1044108842e0f01054001e0094441c0000004481013550040c920590000c40140400e4880005155030780b150801c006020244001f145403803414181c00030403a031440790b48082c4540e541c000300350481c2c8005036801c20064002e400c2c10b105550300b2030601030f8441d03001e00e005450101488001c003441d00e1201c80680b000c5000d61080810301c055500483c0b0040e8200359486030b0300a4038504981d813245441c1c4054050750908162070f20b48548080000c0e0b4040d01a140e41c0c0d0440c5801c1003180003540440039a030700d1480501408280b5041c49000341c1c010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 15473882 1250 15472632 15472637
    0x11b2d0606080c0409080f030a14010806041b03030e090603160602070e0c03100603020c0307060606030e01060b21060d05060702060106020111030c0d0b0406091104090b040b01021e03040305030307 86
    0x1030304042040342002c1040602034004c0d410544034500045c054021a15180c804800140e00da455904220018000f400c1003a014007840000100f5001000714505001314841d15441030000501c18001199580622015001c40d2092028207075508190000700d03842000141034911181081304440d8401406030402c0006074440c0c0c40c00d20034041d007801c007950800200804603045180c03100c1c01c0890b40459002d0282056008201c1c2440c900c020170948003c40c0c0d0004040c0805615580001c00400e065444007903550308000000412088020840384640c819102d052a41c00080b2840d040c1070701d02601c101d81054541e0341c0031012442c03d210301070040b1180d038003600ca65450308030020300b501e03042407540c890100c00b08140440d51001030120394007000c40400120755140a20700180040c0301c00d906c06260300b4140781d51500f513410003200030400c4d40c0361100c04026000313100041c0401c40e9451000d86001d6400700320200c4c03041d02e60048542c070540d0004200c2c0d20b85501c0780e481904640054a040c0003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 15475132 1250 15473882 15473891
    0xb0903090301050a0b0d020607030201020c0105010b03190504030206060d02030304030b0108030703090f05010c0b0405030c010c0203040501031404110d05070b070305070c1d0408030601090305031b010605011b2d06 93
    0x240e0340340a000d9140c00210600050200259450000d03421018a1100a204002c00180c0804140c000e4055500720210f0030001c01196039a0080740210381d104440c103000c2003100784640a1402554030601c0c0c0504c0d01580100b0b032568580082c0012142c0c110b00590341444240400000110443c482030f0103020000080c60b119840ea2078042c0c014642c940224100c854903c0d0305101070b9a019840701a031a0b0400b0b00640c541e03d0340c0c1409411407081c00d510304299424003072000e00143c2c00000a004940082c0d0f400c00c00c103c0a061640e901c100d02740d80c01811003001d1b61100081e49480c2900b1074040e0302a1099504c0140e60300b40003051544044021400716070049055414401c2002d0503100400d0450400c2941e0702c2c10014000342100028801800d014011020900a0344103603806e034040c645c01402c503961100d80c2e000002101041c3e4904402039800c0040200c0e141d40700c1c11464148800f4aa00010855983e030740d42104c42144256a95070380038400c0145c01007401156070035510b24002d800025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 15476382 1250 15475132 15475147
    0xa02060c0c1207030f060203060d0f0c2301121505060403060504020915090a0c200303090106120201020703030f03110f130902030907090b0d08190f0e01080105010c0c030b0903 77
    0x40c00344840d140d0b0700280c1000104001080c00b25141c81210383c1d1000700141e0740d5942e800010244006000060039106041e90030700c003001041030b441e209955088000c0040c4c805c5904464046c1c82340501083d00040d85416480a0450340d9040020450040320920302e05035120004910359030000d61041c1c5034543c0340c07424407007035041407040b0303640010120360700124009012001c24403968010700005000c541c0c1d10000c130242c511030300e0061100c82d4409e40e4061440c403070601042d5a500184ca034010f15501e0312400003031740960200141e603080da0680207401d50700c0c91614140d41e011154004035041c103440d20149401001d043c0002c000725229590810344600034021080d98101c89074010000e210302c10000d00c001c0c0000004d00d901151440540840c0c10042c810200d007407176184040080c400f05e804039118408c180c1e0346042050000071a9100e102198400c1000c642c6020012241070100741d44400600a41d4440c200d40f6155501440303030307580d841da5250b46031000c001c001c81c0c8003880c503000815280c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 15477632 1250 15476382 15476389
    0x312010f08030906040501051308030307170603060103050a0803070203040906090204090c020d0801210203010e01020318030a0815030a12031b090e0106030e0a140601140405041505090a02060c0c 85
    0x51029200d00030007581410743c40804103075036100d140940da0600201084a82455201114420143c8092803daa4a07420134041c0582010100500203040ca180d00340064190704001035028101c0e904400103180c80c00d49929640f40301d40c406042d400c21800304100108a08900d805610004c0c11240801a13840d45002c03130f15003c9034802d00401045401c9143d8040040d580000ca0070b0540301080024810304102810101c94800110750094044d420590481d140e0340703040d40074500c0341042040c04500b074490001e2071603c911a481c011008115004041140382c0c80180f00301c1e4a800d009400c440d07410708103407a485109400c03800326400003a1aa105855024284500411424540e0030100c3c0300c2d42c1071072413003180003505000300030805903100072a10940c402042400101d036001003160b640200362000c9203480c0c10090040b404e01d900c1d00e11a0301140d040900c01c80b07115030b8000314440350f030f1000381e58024060301010300715000900c6450f401501594828004180003a0f458006102440c43d00061 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 15478882 1250 15477632 15477659
    0xb03061002030903120f120414060c040e0a090618060504120203040323070f0902070605151008090309041409100902031f0f020a0c0201080a0501060f080603010608031201 75
    0xd03402150001c0c0031074406924009400008003061200341925403801e5280704105008006642200e02d104c442400148a030928459100003140340945140d6035903950341c01e21038030407031091440d083d848000140316400b05a0000d0b1110b4070440c2e0210305000c178100d0813030070442208003d5503d25645c6091100300036500c05440000e44e05070000e1404c203491604c902e00c95548c0c6580069840108501c0c0c0c1c2980442444400c0140900c403109102190b11242402c0c000d400411003180d40503d80404603040c0341c0000380003202910014020112410814000c5840c4240a454007081d0300c0140b010b8441580c3d28003889500d0703640101401840d250600c141d9180c0b0070240c08070050945046441e802503103003c43d101200c1041420030000b511000c101800040c054040c9a0161a2020032000c29441c0d0100040383e06500036039407204030b900c54a00b52021a0f00a10907240480c0b0388480030340c42540940382c511b03071101005000154a540d100c3c6038500310340c4010000381003007154100500140100040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 15480132 1250 15478882 15478909
    0x308090607080702190c120309080c040b06040b0904271a0702030f0307050403020d030905100908030414030109020603040b0612010207080a0503090f0a05060a0b030105060a03020f0d0501060b0306 86
    0x28a542c00d400c020502a4032190803451144aa50f0086204401d01000300d0100e00180f420010800e005031641c00c0007005034000d4091100300780a00d00302010726248c80d0051101700040101424600703841e040828080c2e60000b8203030390300640c44032041f0456400ca284140301800b240e1a4101c5d03038000c28a40611a00003410341040b07944001414807806503400800d0320444041c0c2d0a075641d507615051020b8801d4013443c2d000a5000b4034502911040507440004c810407150140d0b0880c05071000c00b0700a5941d030010b4000e12647da4020703c0304000e030346041d002007185281e002d0700005107a0000c1c3c000c114698001c44080d0307800c080c41801d010b81400d00b070a04c03100010700e03e40218200182540d9800040c4201180b1804001c004004110045000d02001503050304083c12100c0f8071980e40307001911444101c90102099103412201281403c0c107006903403203002d00400d06501242503900708122140143c42d86a000001203d61000251007481100040d10701c890301c50f502c1e40351100c20482c416183d00d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 15481382 1250 15480132 15480137
    0x106030c090b040e120309070e01120303060b030405280602070b060f06030705070b10082506050a08040206030711030307080a1802010806120f010c0e030c01030509070905040c030b040308090607 85
    0x400c0f822466010454000010041e140742c6e980b5200c0303003d038902e4909541c201a112800c40800041d20720103c03403140300c0c0075119440034048140d0340c0c00126491701040318050300640054030401500294000384ca001d12004104500b600390326519040103d0b042214102c4000c10010700388550b900e0840702c1030030300000486e0981e14501e002e84000300750340203580004080c2c00fa054003103124044c600c040038003e4100c00003100d0051b1014030008090f00c1100c92203a0b40c80c43c20020100d0791501c940c3c22550714680c0c0f138640ea079654546a01303000145e400140302400300304010180b8900c07440188011801059181e45150042c24412810004c403030302c070543c0e03600c1d1f40c040744403820060b604030300c1069010008030f5111800c40d0303405041908000f40c03c606d144180d46007070407004006800003121440783c80b00360110384150703450800640c21228251100c9034198004c1c0b070104002034207a0403036a0f10a00c211451842c150703403561609c00c1070800f6a421002310314214204002040c2c00c12500d40d0044492 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15482632 1250 15481382 15481391
    0xe01060f030317040201121a010905010503061005030c0702030717100615050304020d022d03060702061810020d061409040309120320030c07060306080309060c0f0106030c090b04 78
    0x42d900980303079034400200d4440c0446410005415a802002c0b904000d114007a024400590305031340c201030101441660501040030301c200030030035500c1441500d11410009e000110f0340101c20340c069940da00010078003030124804100f1480183c0302407111034010200406448000c4440205850034820718144400c400c51401d1000c100d50f000480784940c40c1140750501580c0c0b0745850001c102c460b9020309029422000000e05110304510110212060f09464008984d10880504c20991510010398504005a20480110b2003c05165600300f502080d040e0441d2085a490104c2c142a60040c081c900c00ca030f80c1d00c0c0004c006031817801d41c520004c2da2044449900515003980d001d030607403140340503034400004000302c00010180120035055502804101300d45086080d0080c25a1341d030300003c4001c42c90b0084040c00200e09009001d00380503074050701c000c3c40c182460300050000640041d08800358900c00c1c51907a001011082c402c95010710b009002d2082481d0400d640d03c401d85111400c01401949030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 15483882 1250 15482632 15482639
    0x303032013060c0206091906030c020102070c03060506130507021005090115140d0c08030307201519050f09010605010513030f080f030903030910050c09010c05010e07090e01060f 78
    0x100189005891803410141c0010f2500d0000c15068040c42828581000c48000152a54504070307410300c04a40791070340c051080e40b0401e00220f00740c1c01035083c0180040c883c82c1c414070001c4d101e82c0002c5c1d4040005050350b80081c2d1251110f8068035019269100076800c0305042420701384190060680c064528002449002c01007842100c01341c807a841044620b08030400c1c422000d54501201d5000160415421802c59848018080c0c0741d90061fa081c04c089818403060b56008403c0500e81060008540081d00180206040e504103074140181045c403c04000440783c2114201807003042d0140e9241851a4141c2c540901c0c02801c40d011a0080c40c18400103106035420240c40d03e905200307503a804040310604c52075501e4061001d0080b8442e84214100101c10080b41000002c042d40c41798002d48101c980d40c40c20b500c8480115182910b040c01203d60822502070380794050700130380c02c030248202c0001400c01c044052103030414010780c01a01295448a88401c40a80f090154601400d0030210915100b80b8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 15485132 1250 15483882 15483907
    0x609091e03090307141305060a090b01021903110601170706120906021210050f010e09060102100608030c0f1b10020a02040501061106090c060d0b03120403030320 71
    0x3290058a4032a24226095046001050055030401407020302150320641c2c81d2032144e018030041d03802640c0922038030700502d103907040c00f409001e004100141020f81c0f1681041e09600c00ba062124815040d8400c203104103180b80c0e82d400c00b01c42c5d04d034029910003500c290602c80903410440c040c0e001c4090900c2c4113081548517500460b0040841d50341c1c0c18800318141300d15907a10013601c2107550103440c26201144c0001c400c0061070406200c2c00c0030b214003540154445003000740030003948a03c140003440b110000195810300303041154010300140100d480044d6160400816603510780c00c03180c501c5c0c00100e40c030204184d040004510020f898000303081d94104481c0e00840798240d09030035a06c03503000070400440c420f000748690001c1d143c014006006940c0c5030040646070300d03501c100004a601c1500001003d800c004203401305290300c020101468aa1060302141c06044100800769040c090207003641d0500b0310303400040009510944011440d28000000101049408a540103540c0003c105034807c564 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 15486382 1250 15485132 15485143
    0x609070206251e0201020901080703060806040809130f0606030e0a020f090403051902030403030f0309050607050d0b060408010f05010e070504030201140c010c0306090506030a030801090506030102070803040b0f060909 95
    0xd5030301d00b10301e5480da0a0380003180c070400449840c600342107010702c2d100381803075040d0001c1107210742c00e807115119511144401c1b42200c3c0988207666040c0c21802c00f082c0001d081070001d02c64009c1c0100010002294041d03201d0403a94009801001c42c1e076100400c04c94583c1500400100100c1c4102804441007079402207100311407003010840c410f03400c00c03000800f01805001a60140c5002c07078902d02038081c101c440a907880d400b40c082513000c01d00610038030b401a442801107100d4580d004015101c01e4446d0b4500707440540000c040043c8050700d03428802030a4a910000d40b006100150000c2240c0901803c0074080b42c00c180c120b4a981000300c41000040d50300304007100c04403542807814400885420140034403a02a002c2407100ca5405d0590800c0e000b58160801d0040d5203500004100315240c1008055603440d060030001e0111701650010020180a940080e9000b03030060000340c50031001e6075884080b54070480b0205d50701030600c0188140246140c0c003107984100c0c155080d0006043c580b6501e603944 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 15487632 1250 15486382 15486421
    0x60306240509060d12020105071701060e0d02130f060302090a090203031e0d0612030f0306050a0603020f070b01060507050601060c030c060504020a05060406020f010b1e09070c08030a02030609070206 87
    0xb56002404602c0c503440b203d02d8000c00036080101061055170740c0304001d000c1e01d000e0b503890300012403254040540e071866444040c120344803600d0f800f40540b540310502c5591104018107981c818041103400482c120140120a001c43c00000009001c50444c81040030740710014110182d12464259684e00686002048800c034424120720000b0020040d500300c00c0b00e11a0590100e1028201a00050311102c48000207000c0c034880d4503000c21f600d030501c2d411030071030301030b4400e2540c0855420340402c15503000350300a00a103100000700070f2801000703886108800c0340030b034090000514000baa5a003844010301802e030241040d13140c007900d850103e0314020a800c8945c07170050400d40d41c81011034115500c0c03154241c0107007006800c403501c0da666940301a468002c020401c80d1070b0350170000510300e47c0c6808450b4500865002d400040840f6100003403000d0320100030401c3d014013a420a0b12408030317040002640c498031040b440907949142500600012041c0542a403040d94401003d01801210b040c0010820 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 15488882 1250 15487632 15487639
    0x10e010e03090918030a030603030318110105090103020f1803070603020906030c0d0e0a03021f0e070b0f0408030f0a03060803070f120203040905040b060102010b0303040e01090f0b130603062405 85
    0x9607242c004201e01c4003402118a13445920000441800c200d405400c66403c40e8000d450400c2240c01390a0b04ca091410b80070307001031a280391284400c2c04c039070150307010b428607440601d00142840c4481ba040d1040758800e03c07a00c54558802c10801310310f0b146c01c00916000e028240f8096050480b100e01040080c00090000c4905041c08581e0405000840d4004c2000807501c00c04c031641e0f6017560502940300c1900042c0000020783c540c1403002c2e1206140100740400004200074001d0a11f0a60b4004180e08003254212103140104800101828208054480943c120a01030758414103880041c5c01c50745079074442411a00309224000124001514812509401c101030003030f80101e00d50100c2c210311858100c0c0300d44a24110070b100c14803401e100d0702d9124030000c0c3c000300b1060505404050303a81c000c510942079a21b942c4001440341841a030460081da034040480031410540e0000003449551408403481000d554581042050103054003503440060f5102034155101900340c2203c00c03600c196406500d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 15490132 1250 15488882 15488899
    0xb060d02010c05061512010b0d02060a09030b011701050f091903050405040908040306060602010b130c02070302060705240903070201050c07030807050a06140f04030e010c050601080f010e010e0309 86
    0x9690042c9481c0034040c2e4400151886440d0400703298a180c2c400c1a2054000c5602d43d844c903280d044140b04001035648020030000d9000703829820041e041c2d0117010001c04000d003621000001507100e81009010303101080e1a0300e0380c2000e0041c2603084410040c180204000c0000c1403000740040401d45142c1c801d05410724004044542c201a54144101d5009941007840c0c0350900e03040c0082e150203407080e244642c8091005554504040b401c0e22419003500354482d0b00101c0501000c000b0b94801c00643e410342c01541c6403e41e481d00007908a40114205652540203c0d20b600d81d07440f11442c410f16000c00c0408443d0307850802c03d100036903e014201c0000e061190000d024085100c0410400008580c482c00866075140740313203003860700d45081d404200c500718103205081401240d810800362054001801034400c55403107440031104800514607507418054a001c850012903020b010040c040d040b0b800040251000124400303085841500002c2c3c3c82e649004c0d04014944000b1040380d80c90101250640e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 15491382 1250 15490132 15490159
    0x503010617040201020a14010b01030b0d0309060c060b0a06050714070612090812010b070b070306030b0a050406021902010e0c0d08180114180f120d080703020705070e090606010c0b06 80
    0x3d14114807100c001e01487d0510503218081d0314150084900b80f0003e90b41031151100c40c00900803d140e2041000f008115911428040780d88207440003070a02b8000c0c1300c00314078021010089001a010b641082002500000c1c07400148040700046180c103000480050554506d4520b00404030500c144c040e402541d20350f41007500303021a140c140d0789442152010300115594940c00601160700902c011556035107400b00107140940288110b0301120340101030315403280c4d1640d01141c010400244219103140e402d0101c0304d6481c1d0041610a407040258000050505003014013070300d042c4d010140107201c0e1010700c003a40b0000d464032040e00e00c5040c54510725203080f0074400041e074059841140b10207411502090351481840706d200c521051107026104000031104002c1403200201440114a0f010780c000b406450310144103030001e83e0b1020061030300505084d102d545040c1458100e030302400b40700c000102488540f500c241301007508503009007002a80014a42e551840c818070007003456101d12030f0380c140d05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 15492632 1250 15491382 15491387
    0x402010c020609010c051606020138010935010614060306040e0a0309030b0a0c0512040201022503050f060f01060c05030f04030b0a1a06040b070611030906010905070503010617040201 80
    0xb10b1521b03601100740ca03001e0313109000c0d0381a0b404003031013000c0c0190300303200e80c00d00454120030110000030604418800e80110703848995104030120a8001e040000c90040002c880c014401ca15030300c07842d0300c2c2c08400381c0c440d43c2c07003042c01044101c5800040d603450840c1c02c019000c00510710340b007002c0b02500c03045c0d01d0780c1d1014001001007804690b1403080c0d001d544007040425601001d44c5041d284141e0300214a80c0b07840b00c1c102c0c203c43c48501004040384080007560660640d007262241e01903c14030468101d044604030300c030845010b0700c201b04500c1c0240d0100344200b01c0c007400089106040d140040c00d1918001581840d880010710411050106102d842801e1000c14000c945c8059404039030660b4540c3e407032500d148002c0d8202d842e460f406107000b0300203407004544481401842c100a040d030b810241026110716072648580c5003152401d6030b4504c515243e101c1c2d40051842031200e14050109589041d115138140d5400070b0501c010014100014010990400e002c4c401c0300c500581e030b10081e0b40d9a031005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 15493882 1250 15492632 15492647
    0xe0111030a11010f0e030706060e0705070308190c1101060902030408040b0c07030f030804020301050f010806010b0a030603021011250e041a010806060a0501031a040b0d0b040803010303030b06030402010c02060901 93
    0x40c51307146400c0142842032410004014031095208030303401c001c4036036691610602c0c0c2c201902c03c040000c604201c10f501092062034110b0300b0010300d491a50000c60703d00300b0042100e00c0da10007140800c45044003103003030000070b1003000001c1c68400e4007903140d883c1c0790345c44002903c2103000e001d11200010400c0c02a0600030000340c4041d5500c96040717207144009003805400114110b404a00c41d60070000002d03082c0c8418415141200e180800422282e401c0c08260400c1d80c202602c41d40c20903549440c004007503501c01509011101045c3c40d01c00d034440b8031000e45402c00551100500300c1d02103802c282100510020b11080031100c00c8044408152154600450001046484070740000300744400030403c00030100301e140c05144102ca509403003a503100c0054080d501c10410440c244a805188003d00d03017415045046a94002000034804006d156280340e290f002c261425181c894010006004040d0140315804415008637942d900358a490340c002000400f07801d800030b001c3c1c100480c0c40c01c0241d000c0e441d07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 15495132 1250 15493882 15493901
    0x6030915050c070c05030d140d0902060301090e070e0403050403061e0207060e0d02120403060b0f030f03030f0a020c1f02090a0b03150616081e0307030506010e0111030a1101 76
    0x205000504000140b000780d070704007400a5406068543d0002114900000c0003c81c2c9000c0e6212048a004d202540c41d8241d0031081c5602901522944410010703910302000390701130800c84d40300040c00a40040c2c0d15151054603001829002905001d00020a4002050350200e80c2d2084010070307800052400c040350780541101d0150284e00100e954810081304c0d4004e00394a00c081c0c402c444031007081c82801c0f81d07208010441c8a5420307c00708824404549a03030030a0148044c003a203019100e00c1480c7c003191400c603600184800f150400300034000300c107c629400f944c000d20100010360a00c900081f5140d160f9594108500383c0d0001c1c420030310700040c07543d01a1a00040000d1801195075510b40c3c1e03c01c0b40703900031120820b0031881c51219003071038038104c0143d4080b00451440c040c450103550f900c0da40150300189403440244000747c10704c0c070343c4540d510040d0321451069402003454203100c00094041c1b8100c3c54001c2c107110800c05444e180480003c25100d0340751103071400405443c80080e199004184040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 15496382 1250 15495132 15495173
    0x17040b04050c040f0b09061903060b0a0b03100305060105030c010906030b030703050f010b13050114060d020f030106030605010f02010509060703020901090b120f0108030c06040201030c020c030a0c06021e07060309 93
    0xa407102135941d54403038170f50545c09452484007075039610701b0050100324860091000301c00b036101c14808a45594010501001c01030500041d4940304c454a00340360300212101001c80001c600d0500c100034042c0210741c0101400e4000b0b012401c5000f0001e0409030721030084000f0140d0341c5000c91460b55003000a0380c000c41d0090140c0c0c480f0308058107168040c1130014159402030380001c02d4810586044c0c400c160403035800c400c820109640003c2000459030208003486904c2e90248142442400200300031402819162400140b152034840090540800d0001500540e45482c080199103000412081d07845409403030010303610030055006944503140b603080400d0f145000714041c881920361003c440d0240144219212960307030b84240c020381c1c3e4400e0f034411251542041c404540154003e03040006090302c2c80c0103550720b42c81c6036800719103880302e00c0000f91003029681800b000987d4040c000b1000e03000c1010304003d40c0c864041019a550099031184c9010140c1d503407404010b00440f500040c41111503607 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 15497632 1250 15496382 15496391
    0x11b0f0501060f06020a020a0608131e06180b0601030b01140c01020a0206090703050a081e07030c030f09050307050d0204090b0702010c020709020301060e041104080d0c0507050117040b04050c04 85
    0x1814480d00a20441c06843c402c1c0000390004100103000080400c078059006250710036080c14040e04503900b00015094040d00c1c0d0002e4041000910022105d80c8582c00c80303030520700340301071380d040c03010903294141031418500d401d85c0d180c0d0f004140c00c4031044d43e21a800382408544d5204081c01220012090382000b40c0c0341c480031a0451801030103400808481c0c5451303084400c1074542e074240c01c0e00c070b42c01031100030050b41c040582d06000a10140c05800940541240110782004281190840c2c1e448288100c00003540f51400408040d00f01d140074031b000c100d44c03074084011401c0201290b941d51841c02560321449440b00c01604640d910382041c0407543d8410f01001c41400c007100d002e0701070b114918184d405409480300c0454246014800e9074107c444960310b0310070440d030060a10000b4001d1a030a00b00c0d1120801c00824152030400015015a92582e0380410040c02c0b401e060b410642140c00050410906c402428038481d1a03001031a00142c000c009482c0d0342d00c43d8644036250010140c0d100d0303003041c1030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 15498882 1250 15497632 15497663
    0x4150b0d050103020f030601050315090c0a03030e031204141309050f150901020f0a0507031107061205060904050a02010503100801150306051006140904060518100909030c02011b 78
    0xd5041941282e01c02c0e503469000b00341600415441d840c09018160b010b500220342170084500401d840e5401c2000c140656010791040408940c603100d0940040d000b03e1000d154000d500e05080006c2000c1107605040c05081c0f60400710100300700d5100000e01d03071040c3c1d043c1c440c0c21640c0380550700000040e42e0007402c807070b051400d49032050789800b00ca20313855030450080c000003a00104103000720360342d50310240c00c1646082c842c14010340d016045040c0613010402448905284650f04001c41400380c03100f900d5244001c84056054015180010451405050202c1c10301000039000a19403041c5642400d0841c4c0304ea89100e001203050245a0000ea640e6003013011340d02d294403100e191802524040d000a0180f90303030740121003110072514450803000801103160101d00d1862000a45148100100041070325035603100040c8889000c4860070315111503032410701500b03080442d44074008001d049018441c41060f610040c1442e281084c02a040c0199100f0408410900411503c1c0315070303001c01440000e106 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 15500132 1250 15498882 15498907
    0x30909090b06010207060e01050703080705160c091d0705010507080c0303010e010312020a0b0601080705070602130501030c080c0403020402030a020f03040f051b0306011a040e0a0c1407020105070204150b 89
    0x60b100d035800f50003000c102160191164142c45500601a1034903481c00039603942c11108890010f140c4000c000382840003000c00c00d00c2c4500000d01d18010031b54640c0107828451000d0460729140100300c2140102214010b0400740403400c0000c07100242000341c3c0740d20213420130342c20703601c10b10420384124000000041000303081e07812a01c3c10b07030f401040d204811182652043c1d0b0342d02004040540300b4105280010700b1036202e00d8556074000303414a07001d03087c00c000c0d41d16035042e070b0008a0b2207001c5a010704c4082c091540e00d4820790090074500c1c64001da181c2050700400c1d03214070031400040d0269800000144614400d0703012035032410440b4880d65034070f01d094100001c501c0350203d41200e0742d0165030080b141d540c3c01d4001462010f440100a894141d2800b400f4481041c65502241c07200c400900000074520f00240740c46100d0300b010000482c030300701c0000b0010242c007020700c50481c13440360510112000d42d0380300e0165005c056066a0000c0d102c2d482d000c0e04414070390307d6404071801540005010240d40c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 15501382 1250 15500132 15500153
    0x5060a030615051614010e0f070e0906010b03070302090a18020310150e040506030a0f1b0603050c03040f0203011407050c0106050604050303090d060b060d021b010903020d050703090909 81
    0x748040394942c0c00c800007540440f283e00c100c03103c25100345401e0340c400b400b08005010081807000010300000d144150102c075142850b585011141da81c2d08001d80412035050701c40c98203039200f8145400b0b400c0b1076040c1a4202c070700d8007003d401c041c101070340410700608a86544c0d03000c1d8094000d07086400132015603805198040e5001300c030302c1c0314180c1c2410780000b12040c41020860b2080c1081c0c99541300c61041006020080400034100c590510410040001240300c10444006150140f004006044600921013079484c00f07550014003010f16100412913031321801001e81c0e810591202d41560608a1400068050030512030700c4500c1c4a00402881013858010006001c0c0101c1ca000904c821790303480c0c4c10064039000358030407550190803c000001c035902d00800d2030880c861080000040040e01d080125040383c001344c001e1030225034001340c1c160300d080c42c07e0041c1c4044200c440c0244403c0c0d01940d0700079281c40e02108800c2c140a4003152401c10940942d8003c0043c0a0601c410400046141481103414 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 15502632 1250 15501382 15501389
    0x8030310090b011403060103090f0803040c0e07090602070e040501140703060f080303010315020304050f0708010203190b010c0204020c010b040e03070b09070605030f04032f060603030c12030a0605060a0306 90
    0xd442d0030300005665015200300c400c0b80c54100102c03070565407114015000f40c00d0001044590100641e0303139500103050000618020307409007104d4890a0b08040181c04411000740041c0c0c00c0c495080010041240e00240d0300040d203060030600f65580d166481c005014103a18801d007490300a415040009150381075000a0449105452080103d69590901500d84c4400c1c040900400801001e010301c002e800e0b0010368105209208803491001c00c41803050405582c1d4000d100540d4000060009011803070350380c00701110f0b903502d00b000f91514100c000b800d801ca1402c00203005503004219011031180a6100c01e003001c001600500101c1e0210b00c10a46a80c0107220845d00d10907042c02054008900080c00000d482c0d07107454542c5541c98280000305a03250040c0210100103c92400044c00e83c0d60400f001070a045217115403040d812044940e5040c008000c103000c3c0643d105000c1d0090144000035070f004200ea10701c000e141d594540301444400791140d60090b079000f040001d480300c0c000740c2c50380c4001c086 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 15503882 1250 15502632 15502649
    0xa020a021302040b16080c0303010303080703060504140703050601050405180406050106021f021305130203040c0503010b1809010b09180c0103060f0e0604090605130309080c010801061808030310 85
    0x625206074044220b00507400340c0e400d012070921052880a0451030700c80d100d10300030300c60241042c203280001442c641c8240c03c1100054000c4050042071500f41c014030340900b1048400307002c02080501c0d0a00381c41001072406042540340c4c40415500d034080c1046401070400a0150000c000044500703000d0040151011903d00f498100005012880425440d0740149181082c8001c0c060a07034070700019411080c00301000d80080c240004503075481b00c3c5042c4014100f14005038a07441c2c681001071000010b03070b0005010740d0610700d001010b95142148000386010300700032580540c84c1d084c0100c1c014510359260642044c01403060020181500d840390780d100108030103d6010200c4d83d170045090b5420b601c64000801c00c80b620a000181100283c540c0c010300c00b4000141011450f01c4210584070103950603801704c0c00c1c0b280c1240516912042c0d10003d00450002044520000e80001f4185401442801c08100c050072440244a1171005407034018201401101d4407410945503820301303c402445450381 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 15505132 1250 15503882 15503899
    0x30c020c030a020a120602042103020d030b0307170a0f06020c0d0f05030408030405030d05010308130f0509130c0b0c030301091404020a03080313060f0203070201060f0f0306020702150a020a02 84
    0x181d00e400140c42000ca5406000c09800320f180c0601900c1c40e50141e101111043d8081c0000b14a40d610682003404402444110418803c040d040203400c0c024582848010103080c03502510090300d0010320032044880440541032126844540c3ca42007000602d80100011021010201404a10340240800070b01ca01c00f0744402d42220320301036604801000440c0c0100d04248005800700b0300c80b10145a2242c050350940c0d15003540075402608560091300221007036400031801590060015050700041c02610002c10403440c280760024020000003840403207005040020101041181c00e00c4100600e0030411b0b13952203103032170014103890350024020b104000d8500010144a50070303c0c0d00c0240595006862083d400341561a05140d42d40000d010042e10409000d4075000501c944c40b07130380501548c2610058480c18000c20080c2500c1c0f00358044d51040d142180280302c1881007a04407030031640c0c8044016903450452001c540b0035010036920544000c004070303a0000701034021a040c05618400c9401d0603 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 15506382 1250 15505132 15505153
    0x30207050708101103160503040303140f07090801111605070305030d0605030c040501060f030b0415120b06030715050d090215030603060901021614030403080a020d08070207060c061505030607030c02 87
    0x158503010031034034001580c0c00041b040d40c415020b6001141c200b8001e140201d5011341e1400a5810201d00f0340d2034118910a50040044e016840082d40c00601840300c000c3c000105042452031203801014036031a8040103a491120810108014002c011503020090740c1c0c40d04000c1d04c5481c02003145205180c001d00600c1d0b50b05840b468280320b01c03030607101180c0b1141140703542207004a000f4071450039455041569003500d0040b4080200400001f000104108041070056140400c0050301c090b1034507019601561090100720101c1002180c40d042c0b80c5032071303601d4407200c0c1807540181560741806504a05600c1c82c0e030300c40051031402144600e409504440f06501c1d40b00c0c505080f40700709400781e00311841441c0c00030300140201503589802000141141c0c20262691034117109640000000c07805680b0044c1006003c940107072529601442c14009010700074034050001e82861064280203162641d1100e10048040b0600c0d60361010b01030145c1220403911384500b02030000c1643c10b890f14007610600742c400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 15507632 1250 15506382 15506411
    0x303060e040b012601020c0c01031503030509010c0503130b0d05130809060a050d0509030702100203030c040306020a02011b0513050d080406030902031e0a111801060f03020705070810 80
    0x11400380381e0010b04000300e40e01c2c0c100d9241403c007070289070007141c07151407045072030000c42400a040d19911207400740c07a8800c0303c00005811107180441d100c003504007041c401c0001c01e4200c015113088400c00e003032580f06482d95140c824110310680d10340e070340c10510b034510129000740d100d80a0054240d020740b04005c2d0f0388a01040c07105050b08290002c081200070809002d49040c0080604071080b000d0030001d0038691602c10001c1580e4040325910020750002c20264158500880d43c0b000262240c00903502c1d5007010107083c3d00710300c81d42c040542403d40000e075500029100750310144256084080861240c0c1d10420001c10a40c881241041c186800d007401180c5844c1911346006196806001d83c1d10301031500c1d00030f0307000c1c208484c03060b0380c5070080c110f8003a9840d010f54201108402c0364000380c014030780c29282c00ca04424101d02c44502a44100804240754154031401c0c5041d24050308103107aa074603c0240440183c81810340c014514041c640740082c03500b0700050f1802171440070610034010121940e100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 15508882 1250 15507632 15507659
    0xc030c01060e0414150610120504082a0a0f02180f0103060c02010204080a120302040b0c010c12231f0311030d03020708040320040606020c031606020714040e0d0804030306 75
    0x454003001170702c4040358240c600010710342c40d520300711700380f0080014000203800c0c111002142c0940e00010001a00e161010004100b9070284540c1c2041c60100c0c0c41241100303540300c55182c0001c02200306001c081d015955800d0300480404405429030050f841c2c2802850080c0000784421640c0718200b9401421050060080d20281c8240400903c0200300c2925034082154070004503500f455401c000101c5e8004040d00284640c200120011070300c1070300048000d247c503c66000c01d4903103600d01842454003480b1403906000d11041c03680c2c1280380d610f400c0d000c000040c050045421000e03e05101c000204420040c3d00d610b0208124103075000c040040e6803e6081e486017010062400d0420001400050000814041c24041e00301d480300c00803003c0c4000c2002c581c070540040000d607004280c16070316883c007045011423070b4407810200d002c50351800c400603680308035600a80e902100c000c1034200290300d5a50040c0556281001161203040ba95500a44807d00c15a025000603041510100e00d1000058a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 15510132 1250 15508882 15508903
    0x60806030a020103092a060f0f0507060218090a0605010e0904030503011505040b0a030b03010506040b030c0402090103020c01060603050906090304030506010608060d0b07050307030b090105090403050c030c01060e0414 95
    0x103411070070315550045008004069048030603400b4450440c504034162142d000003003480c503801d4148981002005001d400795440c00004104943c4208852310b82e1000079503208980c8540c002d0b8903502c0c1e0380040c2d5180040300800c0e980212901040091805403030f08501c04950007a2a50354a50400c1b200b0312506130b1088070081e02084007000100140c00107089440d4400c2182e113000c900741500c406c040a8603910859070b07400002e48416000402e0300d0300b88038041d0052400c0ba03082151507010400b080d145ca81e101d00a521a0b980441c91002c5640039404a48200305034500030081140c58a001400804003510f030340c1c01502c600800101644c800004035402e40342c01c94010305072680390a40407680c030800140a00d412001d0f00c00e50341c00143c0604601e60007840c0daa10b42c10344a25000c44003d045400c1c07000d40900c200b29140c0104140e03181c0f101da1680040e010710302240d94000514003a4038620441d00d4241d0300d9868010001191070fa50b060050086102d510b0309400f644001c0700c45030f40c0b61050381 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 15511382 1250 15510132 15510139
    0x1050103050303060d0314030405010f060506070510020d061205010203250e041104050d0b010509070c0201141317010b01080a0b010f230409020301031101050301030302100f1b02030a09060806 84
    0x40070486501e80410302c3c503c211720038a0081c038444c9002d591f0f02040d4005580403502c40e03454030340644002c6450f00134503020b0305094842c603041442a844890340c1d00f09800040381080d60000e01c1d591154140c0e000200684140f400e050f4128030946840380c001e500486040040c1803005002e007050584c42d03180c1035000e01c5296030740c070488050300c001c10009150303a43c07552100f14810000000da5488524000300c000340101804860f44d0700d41024880240c8004200300f0801201414080060f80c20124200c403481064094544030b81f03451420205460064000c03864100c815403205400010542140494400a0741d4400254540400b148241c40d4a50f50a5000c15101c0503054407031845807111744800c1888450001724001500d1004400c0d500a0700300c401074030780000050007800582908240300c02000e181c01031856245450013526003d0f0103644030042c42e190f038203d0418014542101c070700390142040c0340d44010011070000e95245c0c0010b4032180815503910000a00c1c5010f410441d102d40c8018 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 15512632 1250 15511382 15511387
    0x904112119020a031101031803020a03181a0903030705010920010503100b030603010b06032a07051e030c01050109050f15030316020315040507030506010b090a060507060207060903080612010501030503 88
    0x45d80c5a1420000c0c4045842c1095902e1031051040500a0b0203940200c3c0a5006040d00b80d641d414000c201904001c451100702c1100401049030000c031001d00b00b1501d000c10352080d2100c2c900b0b00000e00318032031000050000c1d82440404014040081114850901c091600e5051340c1c41782001590107010413a019640158040790410141d0342e01402182d00c0b034001000000d5004444c40042c1d5581c100741d0300118540210090000b05181c151a01c506010a0300c81080c10806155600381d40d41851517408030802d07981000b4908110030401c1030341c1080b42110024000d40d0b85554400c4014082110095151015240031601d202812200f41081c20006005145001d002081c003544204400b02c0807600f61159900003070540f6120f10110707000714424005072075074074a0b5041042c030748101070b0800b5002c400c0c03c10034035009561300d0341a10100c0b0054106940c94010a0400e0002030182c60005003805040c10008000c06900c030014910428040301c03170304443e00700506090f0884d40300340030007403869008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 15513882 1250 15512632 15512639
    0x20d02060108060405030d0e03070f0501020306041410060c03120501060e090c0c07090b0f0901030c050301050f0f010e040201090305030d09050d020705030703020405061903061505010e030604020904112119020a 92
    0x180e403c00230044442c0811030307280481d142d54107403044140c00400d8400d658084144070380391901d80650b000c1030000e4803810405050500c62100c0304a0a84200c0003407107607023444071301050b00804403462a00855001040300350303900e14002d170000852a440a00c00c040b00c20000c1d603021900701c16205458111001480750505008040d0f0083c800741d6021075000030000001501170343c403040b5482c003a40c410400381e00494070385024113007501c0018104040c2c0308864010000751035281106a4119813290001d20b5542d21070b800140d64023851501301900c540000103004440e00c40380d030004416a0b209000b2100004907008049841c0e090034043d01d94550000c080800141c98181c010a400c980c0080c0204a40e0707550b0101280e4031031841e8003c8560a1300c89454841040400807d40300504081c03c0010340c80d25420000381c0c84190050000b80704c0c2c810040420184006004405490742c2c1c05003d551070f2000502004007805106281441603104120301060040304c0c041c4460702c00b40d405005202810308 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 15515132 1250 15513882 15513907
    0x6061508070e010e0307060314011a0708030a0b09070e0a0503010c022e050112030909020702010509040509010b0406060c0b010906050108060d0f0503030f16020606060d02070c0b030106020d0206010806040503 91
    0x107400c80c00701d04004e000a044526030385d0500c041340c002c12003924005260300102e0440018607030b0503071000c001c031750307044650403090b60030b03682100c119035807000c01283d0b00d656840c820001010304d00c000541240b119420802e0094012100901e100c00495201400075510001c040c01d8610070084540160802d0706a01c0c1400d410420750000c2d4a0140d4000d0618225856044103c40090380800030701c1c80c0b8140c10f08181030b0440048005468400e400f9481c1121940028100303100c3d442580d4040e45e920300000310742010070f6122211074200100b090068960310000200468038200040e5009030100000184c413030840c1c442d6008982c8180c40e05d000b19901c19080140020450300107030b40000c908a13107540001c40c213000443c07265154031701c1d44405050548a51101c1c040030b00038003040d580000b084c01043d41d100d0041da09203603850107003d0ba42c0c0c582880c046405412a5120000d20705000c00041011a00442c017403440d50300f02e500b1980d00ea030380c03909099541c58090707a001c1d281c0d40040102d04400710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 15516382 1250 15515132 15515147
    0xf04050712030219030801050909071a0703032d110c061506040e0a020703110a02090c0c0138030a0b01030323030a0902030708070e01050405060102070503031201030606150807 77
    0x5000e801a030300743c0750400004030504c030724000084001a07036580c0107012500d01202c01e1508508460000c0c07150b9414a51041134001c90400a90008c10000c0f8204e401c00d48a90008120542e028144200740c03200c0c4600c1601554842c2e41da0302d40700b800e016212034040110400d82c0c204405050044c030040e190003840808070030080d4503060b08407108100103d60401d507203401e1070007030060840050343d030b2440d8140103283c1d5846121400305130700b00100100150381c03034080468001352402e0401344d489a03140d4185004107103c5881070a50500000030300065040039402c1c03905841c0300c5840764008600c2c04201a00c4442e443c1c4020f100941240041c40807034800c02c0444100c6481134001b1400342c0035081c001c0e0250700201c0c0c202c2c80386a11b0708624000c40c241400904024007203000104142400c02d000030a250303005009180c01150b441700080d416138801c015002c0107202c00341c2907075602d02801e0480080d010302400281ca4081c241600021860824108804200082d40d6800b40c5621003140840d040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 15517632 1250 15516382 15516419
    0x115020102070209010f0f0b0307020309010305150d230304030f0807030302070c081e070501090303181508010f0e060108060d060603050610060206010b0c0a02011101020f030c0304020102060f040507 87
    0x103650a1140d034005803a103004290281000b00c0a00c2080e41c07038100340380c2d991b143c250010f0708940c0d030600c203010403281c0002c1550801d0320242404039590360340c1801c2c00b44640402800c00d503c052420300030303024042c5c6400000a44044800443c5002c200803144658030b08c26807000800e000c07049100040401c4040e0060200303140301e4a405490f041407130704c501132845010b80184245401c0380150780d0501003d00c41e0340d4240f14244001d00205454100060822903051101809001c01092001850340b00100c4070300182c1a6a4903210481036240b40080c16070400b402401e46c41d05a8090105544858108440c45588142d469400d00e41c3c0344420320400d0048a1001c030b41d841c2e215400400040d00070b2041c544151070410000341150b04d4440024504038041c3e0183c1103e00c1c0070011514404408111a42c06940a0928119505204031114020301c074143c9900b03e0003402000344241145100020350003203000760301f01c0302c1546a240600c030800d00e0541d002001580191403c101300b0242c40702220a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 15518882 1250 15517632 15517637
    0x50703030e01060303030501080c090403080105010e06040e010f050109080102090303031302040b04090602090406050f030601030615170717032809080114011d0c1c09060905010b0103110c03030115 86
    0xd09524050769800e46050b50402c81c0840c0c2c54000501140e001005030141d54001107400d19514100794401800d00a03040c002c160401403080c00e000310301d80781c00048500802c42144180c4d41503a684c10681ca1007c400d000c1c040c00202ea0000001d80e04405000382e03030700d0400c001c02a40c5540c45048412103000c03c003c03400c0341c02580b01d58079030b02980e4a520403d02c07400c1c01258056511900401000b00f00c1344640c03c498800c100b50012840140c07000280ba03819280e00c0200056100e80c444910008016907030303c00321001003983c035030209040c4080f81080803a51f414000300d000240450515407603000d03100e05010440b1081c6101404011451405204843c3c80c6c1031021040e51210820781c01c0d110111000103036014540c00401081da5050380d4400c40603a401c450030014101010f03416600d124110303030031401c00c400790140080d941d1203500208807158003120802c102c000e51315003103000c0d140740300c042070220b890050801c0d609901030301100c418400720809949160b0924030041b00f0300c01800914003c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 15520132 1250 15518882 15518891
    0x9040606050301051603060b0703121814030403020915011b140312010302100c03020303040813120303050f0c040602070605130905090604061b08010501110a2307050406060e0105070303 81
    0x9260b10300f845a02d000758507490840094480e0488041d041d111030b68460b0020100c1003001c0c40129502c503804400d0400600404038084940000280301510781300f001802e0b044207101050b002c3d0704000000d1044a100303484040d401e81d07070a00c034038060704214050280030030401040010100c2072104083c2136030788a40100302e0a285655000c078034542040c42182c1640400703400510540c60507007192040c080503031800309a030b030b842650001d44a000140008000b1400480c1d5003030101030841c5103501520f041102410003201a0400802514054802c3c4680c608400040741034642c02c00111015245c0d10380003850410301e4024200d869602040c4580d104456246020070000864021a4000e030007500090101d070803d41030903002c44e4144107800306a2245542c18207a007035005010203045800900304070212405603a240d03405c0480b40d08005040110014100c02c602c40c066096000715a440d404454086440f00188412240b05004200208826140120007503120740020689607203c0d01d00032030b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 15521382 1250 15520132 15520139
    0x601020a051614040501080316050102070204050c0307081003080901110c040908091017060d020102010b031608010c0809031806040b0a0207050906061201030204050c070203030d0c0f050301080c09040606 89
    0x103080850070b1803450b5103005000300812001c070071080610512039003150208003e51404002695a202c2d5565004640d501c8842d15010f0000c2981601c540715000f40040c016440d0601135500e56a004440030b901050340c11011825171075004020005980d4401d0000b4601010600151502c0025460b221860722448440341555101e9000d441003641c0b1803c0003030307100c0588404024162406040c1c2000f0020740c101c0d090038454404400c0b503080340050760004017517019800101c8c050300340c2421054151141c0d0400703005043c03c41c4160812510300384000c00c0818560700c412601400181c8100d842c2d54828400d600039000789070600001c2a0008011501e010b0f5203040c071104d9500041c404001582100c0c0c010407007418a01203040e800041101c10074540198001e04501481c4103000c0a4002c0340d5540009409000c0c07402150751080c1c0007001c6036100c00440c0c1000c2c000c3d0003100c0f044d00c00180c01c4920b01d00494010402d0301e06840044d0b0151100098010a0225070356004dc003d03902d00d91030b41c0002 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 15522632 1250 15521382 15521393
    0x302010e06131d1f060f030207020405070801090b0a0315050907150201020307031107021806032103090c0301050910050709050a03081801050a0509150c030c030c060901020a170601020a 81
    0xe00400c400e0034601510501d1084120100400806160554504d401118405405000d0340810794015040041465400301c404170001d004170074009400c01d1074101800b51403078000c04654101d90304084207207c003111082c2403282040700703840000c242d0180510074040640458000c03d0f409450102110701c100e5a951030020000b04544407140580d60010500000642c14050702840c0c040e040c650920b0000103602042903550b21007036809070004500c1c0403800030340d41409000111800c540345044041d0082e42c40246a038401e90b00c600061040c3c4d140e9441d1410103000e4580725400000c080c020b02c48541c010318003e090700038516420081701c0d0501240da5558480391001860040e40c141d41c03101040d911401040c0c2402c00001d050210030301401c040203900c10100c0307400c14004c1d512240d401300002802e840300d01443c40b2171202c5000100345810101000005080d00640c02e80880b40c1c540c035003900711400c070303c1009140f0380040c00000802113507607045400e0a8004034184101c60700c03c502c0383c640 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 15523882 1250 15522632 15522667
    0x20307140c060708070302010e011a040c0207090608010204060206011508160c1203050603061f090c020f0106080d02070603020f04090b03030702030d110d051201090504050307060c18080c0a0302010e06 88
    0xc0b0750144002c01c0c80c201303042d4240f14100440c00e510000308610bc039241806101078610164a0f44160744512070110100c0c428010100103050f4a1400d0080b136491b02540b0307002c0c1d0018001c023001486140c0c000517540143c4000c01c1240519500c400b0038540b80c0340800e68182d960603605a0500c10100c00c400002005220b00301d420f924540d900040908001080504048000d46124007910700c3d00c592101c402e500002580444800d5100028814a820001e9040c100034001740d01042d440c0100c0024140e6000c00c0008600d0500c1c0e01303850584c0e480720307010b0f801c03401402e1410304d0312681400f00340208201d1354440746907804d0060403070781405450750000c1c1c03400450024440000320f2108285105840400c08440d00c524582015400c0200c0c28000c58840c0005208250270750752210042001d02c00b042c401c6503070864201c0010b00500481c0ca0000e808a0091a0a105828803501000440000109100805660003000840a203103540c00443d040500e240c11141d12410070040545805c500c1804e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 15525132 1250 15523882 15523897
    0x50f090420031e18060a020901030902030703050102030103170f04060309020a090e0703030306090e25080a11030c01170406050c0405030d02100b060c1e0304180b0406050f01020307140c06 82
    0x1481d20b903ca146420500603102c1c05011100b0000b4100d00e640c03c2d941010030810340c403411420005031161182401280613104282000c0c0d01801068408414404107400950580c0c0c0118034120700d43d15000200b0105100380580f540d420300007400300784602ca01c20f07001394100500050049170195100c020401c2141d10082036081c1c0350f40810300410406402d40100e50017401d200d8020007001c1410341c0362a0700c4005803918020205220790109803590109c42114010303248a1088820741c0700035281c0008103120340a290340c842c0c8038520b034003004ca601c075801c1d0448040c0c030788902c0d0f07640307031595924071015250250510700c40407001d02c00480c4a807410081c0489210725a4000c14050103600591011a04c2c580e50250046508103c4828504000038070004490868422800341e103162009403420350044ad007014031624072311182c0020503004d030340003050100c1044408014965954082114501d521394002c1d0143c0c0040c070a880202d1011000d030080c8201a0302034508070101100010b003154030811 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 15526382 1250 15525132 15525151
    0x1104080a02010f05160206030901020c0d02060103050c030a0215090102010f0e1015030210050717070b0108061003030f0f03060902040801051008010207080702100314010e0115050f09042003 83
    0x31506010366078442100d40c0f0325070305404d00901e44800043e0b00091251400c0b0043d024440c00808504860f409504491003208140255481d45c8001c1d84000d4441400f0300c4191068460180e004410380703008a00300c09011782c02040b101105070a42c2c0d003c0200c0e040700c600e280c150355807064900e04d4417550f4061400410201c3d800350a030f0008680014048802c07040c6175401d100151a01880140c9419040d0203010754282005a250411864484800c1031040d4021010b20004a44081001130300700c4c0e01816507008105892041c0d5036020170b030720010668030000d00014141543c2044c0140030340d42d1580c10840524000c100d09880305844c50688c0d0180e070124840303079554000c01c806480030189240140003108001d501d801c1403901d900c0400c2c010103070064400c40703000c442001d00e140a640580c01900a40e00414055a5a490000c20b50341c424843c1d81c0ca42c001c5041089482482441180c41401500100354101841c400c1480024019801d0a0303040b0500c0c440b68801007000c1102035845120340e107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 15527632 1250 15526382 15526393
    0x70819140702010507020d05031005060304021302070f020a060315030201030e030c15010f060c0b07080c0c01051305060604020a081f0b0c010204030201090504021204031809060308090f01020607050a030906110408 93
    0x2080203241582648510b82080024414006000d10102b825000c54008446603030300e9403200c1c0001000350729081208000c80b0310002d4444c080245402100760018000c81e40e49500d56641e4500307809030341e130440d044a4240c041003024030066000e540004510110903003200d080c14500301d03030700e4a004036105144106484c4c1d07100400c14025a1b000c00c02c0a440140b4110866003071903034619905040240450041c04951000500070581003020f68842907009002445a410300000310009139580c402d042e00c26002d8000021390324100740c0201c0d02d03280d0b40e5035a4400d503a540e00c88801518224441d4a03e01e402410500060b40701100014180034182032000584c1c0c0c0b840e52001400c10b01955004a0043d030040c04000d03004d141701008184d002e030309030a0120244407290b410082c14240c540001d02e03002e00d809008400e203c01c00c130227860010010f5a489155001045c016030744da0804550405c006481000302443c070b80d1103074021346000d5115000102e44200d4a4a10b244640c01a0b0804903055101 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 15528882 1250 15527632 15527641
    0x6150201060302190e18010902041103040314090d06021e03011e080a0305030a1515030c0905030c030d110304090504030f030f0b1c020f03070303090305150708191407020105 76
    0x140521460072891310503840c403581341035120b4080c907000502c21000c0740740e11425000d41890a4120038003490b03004004000e14000e001041d523a80d0001d44080c1c000401803007902440268090440e1502d40005203080d007413406a580f00340c0a903000316502c090000040c12420f00030314020000e14080c0640b505a1000c0ea500d400803050300c1d40035035100301c81c00d078030440000d808a900001213940000742e0000c081450f608107848a41c01440e581d00042c42031007a000c60a12142c1e050b800101300f544c980e9104140c15035500e0030181c1d00c900745415258150804800c000069000ea01284031000c0301a00740c1b401c09550b2051402203a10403142a00461800c1c3d0340440c80590501c0f4440c03503980c00484c10400001e414011030208010500c04e800c07003a02d078000440940d1350b083c1d100c0031050402001c40d500142c5910340242800c500c0d2104407854804c4540700100151118074440c49618290348201050b520480c03080c2410041e204003262056403a041c1540d65140207030214811003040c0c0021030329090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 15530132 1250 15528882 15528889
    0x1c0504050d0302091c020f0a08030307030c020a08090103180602030103050312180a080901110105010b07060b0d1113090209070e03100b03031b120301060c03030605010516020d0606150201060302 85
    0x40c4500500402d8410000d20380d0503a1000c2c3d0049103034002003d05090b2001038408503490007908115958400c0b00001c0000305150000000c2d88240c5040d0f40901205891010a80e41e840040d64020000321047c0b0003601c03103500c0f0354400c034402e41c109c001794046150715403182c0d82203900070703002501c0c560000100e00c0010700002450039000502c4d0348907100100341e036030409922a2500f440003800c800d40000d141c2842c3e84109a49070f486022480200460b595400c6a900d15a00c8100f080f51101d0400030035a00914000700b41041d019080b00f501c0019408034020007144c0780100c0c00b034204e1255075400346400350f103d0f60511842441951212005026440c08040c900202c54120351178250030020a0385241e1004800d5551718458200da41c1c5851082d5680c803400c0a00030801c101c9203034804070000a900f0b9010011700b803032500a440070803c09440702d0046910307104d4100220889400c00c4c0e003030401030404400119450340503c000080b0261074415040c0d000c01d0390105240180e4450005206525 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 15531382 1250 15530132 15530143
    0xf04030605010b0316031a0a08010b031905060f0604090f06020702040b04020a0905040525080708090c0904030c14010f020903070b0301050f0d030c1b03031106070210111c050405 78
    0x141074001c0c982135140c10ba81d006100312140010404168403504000d50040010820b442c5c0a080100145031131512800c0d4180200485101c0510a108030844204241c2c900e01c21060307032035040800340075103607980180c02182400190180307400c0f644d600c172078401040c1c1c1c003034941e107e0b40d105100140c1d44550130700400080e03882c91034407a48680c1c41040040310454012441004031882a01c1c04126a0764002000f0042c0103007003400404500d1402c008418030f64041505481030035079403281c0d0500e40360031015942d075102c010803851700702c00b4a50100700800c0c000c0200042803889031201030200c5204035802803d440c26074125001060300458410b200c0d26091004801515003202544d046626003000140c03198881d24110b8092000d1503c41010700d4410700c1c0c5601050b40141800e14a8000d1030b0b0080c20080c0c0c2d0344000d4000170030392442e020409801150701c6005000c5640103021420001340481e000380952546209442400c03c2400e525444000150611305100d010009030b41c0351a042560424 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 15532632 1250 15531382 15531389
    0x30a0503191103060d0213020304050601031e03021203181b030106050103050906070c020303040b04151e090b0a020f0601090204030b090703080d0f020408010f0504020307060219061109060f0403060501 88
    0x85040855800342c0e000304030262548244201e03140d4501141c00d001042c0c0b0b10801501d0880214000001c00040c0310000904038101ea01c13802c2011008500c40c0318488a09106040080c01078000f0050410044071803005540c00c0011003004086040010701000d16042118110501980000000e03d0461a01b0701c6281d00604d001e08003800240740c0304030400e40b100001048031040c49141c00c07003181552010010b8902428011800701c0da520f8441404c241058035881d4584006900905000d010704000c0c40c51101e4202c0b40d45803001041d080030709190307a68109420500c2188115010708592140400c10307507000342114000140c3d07a6007181480c10003048000e00c10000b66204040403c00698403408036441100801000070f40c2e400c03020a044064030455003c54060360074aa041030f01070308030758499802688210101d0b1100d942c0c541d030907a10741c140491f40e501800024491400071410b5a00440c42d9030403000c1e074071850001c1020006e41c0d0364000c10300716a490322003c101801004400d104141c090f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 15533882 1250 15532632 15532681
    0x1207090501030915020a0203040509040b0402090604060303020a0f060f090c0906060f021213090f0515040606020309010e0f0a08070f120206090103020a03060506040b0c150601020703031808030a0503 87
    0x894100c0e15000003040d620707602481308950008100a19510074025240900f90003888011141068241098074000039101a8130440c0b40c103001c206c491510384a00720440342d068001d00701810290315410052a07046809840b92611400e0441041e1002c1c811004000d01c1402514031003800c08218804030f4520382c01000c140310031030110034905900007801c00072000012085540d01e858006c01144140312503840b5408590410290f0f40745030840d45c100a200b110b400e0240c07000f8550303220401060321642d109180140e002000600c0c03840d486000f060101075805002034620904c503030049010002282e01035021504207050501c42103d40e0214030000342244519021199013540018825103c0c101c07a950602d6400107007080101d0094000c60010702004201d540c0303496031242c080c07443c1d070300c1509156081d01031000c9001019250113600c50003090103a000b05041811550140c60050b08005441c003100340340c4c200020034400810040131150700540c3c480d5207a040c101001c8040040181c4040032 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 15535132 1250 15533882 15533891
    0x60a090b010b0307020f1009020102010b0a0501050a12020708030a05180105040302030a080921090103060603050118050603190c060306050303120a051b04080a050c150306060d11120709050103 84
    0xc5220509014152610590303580d50344d80ba4000c06034034000010700003030414091490035041d001440c0e0b000385d6003603000b80c00074004607146030100442d291460003014003040044c050009450310a50301c08a0f110703c900001407802c0865284c09800e5001154000740c95501c0d00f04005521424640b45142200b01c00028482c030b090640d4065141d00586198138101b107210b000140301800104040e2080c028041e00e074500010318460281c1180d40b207503c01502003400c1c010b00140c0c4c035200380b00e0203041398520290740c0b56070311540302804090134000e03100550611611143c0000c2c0400d0940e491010740c030850380d000c0250714020000d001e8030b59070f40c8981d02c241c20501c980c00003210403110850740321060000004150b6224030303c401540150712415405013902180c0866003030000514500c0260184e822901c0b142d45071000c0000c15403840400c00540b03101480030500c00d044c44000340004e42080000070484941c3c4150034015908500c1400d01702d41c2036842400102600f24000d01c010344400e00c3e0522 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 15536382 1250 15535132 15535151
    0x6040e1b120304060207050904060902100f0206090f0a08090103090804090603060605060403020303030a090c08070e0124050a030c051b010b040c030b01021b0d020301050c040603050109090201090e1315020c060a 92
    0x2521946c8501c9a5406100a4000601000301c0c40c2c3c86030041c29802044912099100c140080242100800510140c41440081407207001e0000750300b402d0385008001022003400c1951559115042280c01c64149030f120030001d40085d1110001e807020306191803000555a1035410041d060341e14a0b4030140c0180c10401c018000758401000f20f035030088200002040310000e074500341400540990244116018000021485106416440c1d040303c02a00300d8424108000c2c0380d00343c21013645040742000c2102001070000a0f07001c0c0c0c1010070001003a040c584e017001c8210f20805803280b40c2d05d180e0400c1765551000744000340703054480d45e2985030507490104901e071744000c0080d540b2900d4410611601681c2c2e046540c1c0350303940c102042002540074000340070900340034002140d02d42050055001181c00d010011443c1402ca1040b406141d4059694159591801c002c2c000e40e032602404460500003910403c0004c03640070800d44201c0003902c0310042c2c0e03c009451945007080c1c07014082c5101c4504160509 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 15537632 1250 15536382 15536387
    0xa05010f02030c0a08040f050f0a02120d0207031211010501090b01020d0905090112081b06010f0605070302070603020906160503030601021513110d150618020703020d0806040e1b12030406 82
    0xa40000c0d44a0800c1103c0f03480354106a1447c210b03c0b031008040b4450280642c940c05000b249803445948295400e01342040c00c0044ea58940381140c82c030000582c001042000469070307032406030700b03200c00d02c1c00c1400480d00e10620f501c1c00c2d180241c0140700704685544c3d0100565a0402c030600d10040103241c503041d42800d100004100c0003042c031418000c402c0d105004014000c40c0f10854003210745246600d011111690111a1a9482482130811045071800e001500c00d0042d41202c01d001e0741a4007504101d81000400e5009410485400da04504c050200c1c404001c6082c0aa0301d82902440084d920ba16103130000914200e119540c20003880120401c0c011000d542030310000740316511003001c0500409034408104440b00240c0080c00520346003000c0d00559961703610100c165460005030310104600403144034103910850400500607800103184442c21885030110642020000b400400c00141290507a03150030004200101080894004a1128601420034019040259002c0c504003071070715101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 15538882 1250 15537632 15537637
    0x21080402041a03061806070804120305040c030f0c09050a0204051e0f06070f0204050c070f0b07020309060703050d050106090f0306020304020a05060c030306010809190f050307080c0a05010f02030c 86
    0x2400340751207215082c6046950140302e0300e0030b90080e08440d107518003040001c40c078204509110040b80100d0b0040740c6401d114804a511035500010b5040c802482808103c008220061095030b01600e20500030001491900d40002894040c044244420b4209040d01c400c0b0b59020b040324000d103204000c208055140c4160340c042a80308904000151004800850a4040c121646e01d9010500203202810002e0815140083c103000351400c1102e0355840388032500c0b500c075401c0e0140520303403004450342c00620306020341c503444130b036034415a400d008102c404141590001c00003140401d0010400845407000c07440380c9401010185004c41001d8a000e035081c2d144081c1d800040d010b55000070005080d0340710034038400020800a0080c940e9009004042a00c9409c140e4030701e40003030350240210311a0311002035000c510300d8000500180002555460a81a442c1c6050485541c00140141c1c00410980310207004109010805420740449501d4023300b145d88011204000310b106009001104000105 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15540132 1250 15538882 15538891
    0xf05040e07080313080601060f050313050c13020d0513170a0302130605030402041406090a091a07091a030c180102030c0109050304090f060b0a03020a120e03072108 72
    0x100000ca1410091816080044a40015845100000d0a52040650901940102c81440c0d05595050340c0720441241c0000b400480740e0001081407010903003140110140c9030009218000702e944007005100440c0401c0d001c110481d400365800b1461680800b040d01940da0f02c40840408032400c05141e903241c0c1c4010f040601c401600381d2020800805107030003a0b0440e40b50751607007070301c10001e25070b0f444004100d5441200c00701d01035814203454640c4208990411405280c00038040c600e03503924840d9100c0240040136090380d5000a100442040d80301582025005840c00d45d1003002c2103080c02c1428401034403000c0807400c11034040080041c22074002c13003900e1141030756480c03d40d54400f503400106d1460140368041104c9500c0c0040d02c0b01000390020040003210355051052022044050741c0d1411503a840c404c0b40740c4000c08000c0c0100e1580301c1d13801040d0344010350400f00b00d05000780c0301d83c01c121192080e810311a41c2c4000780c504280110203007010669075031040b0860308000c3c004030007081b2860252 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15541382 1250 15540132 15540139
    0x40503161d090a0f0b010914041a0601032309010509030a0504030b070905041a12070513020d0612030c0209060409020d020f0307080312100e0103030518060f0d0506030601050a0f05 79
    0x4012a10b182c2060040d003940b140c0181125840084030f0400881051080c80342e151868517085012001503000c01180f03101e250090170158034000a441d06d02c21590005040604140d03846d4013810281c04c25241c0102050308a075605605490401d6481d403c4900c0034014030351386e5006105800280d03030301c40c08032400d0300d0344152280c0c0d02c2e845108065600340b103a5001a44e000782400328080c80e11034602500d64107040e0490f9a4001c05000e0504151282c00700d010b030a40204140c0780244d02546250010702e14919001400900d03640d45295501e85c1e0141c81c1411400192380440b0541545824640c1c0c60f0452001c41d070800910070f165000454601c48400000d0041d651003c0a4005940c140045001020f00380141c0740c0d510f1700d40d001c0e03007030407102156100d0240804400204851605003511810381c2d605440703032703842d2441c4c25284640c0041c65a003150351000c000c03c1500440c001c190301a00401040e0000814241000b804160030020140c000070b0042c0300980c0c0c200801c0703e80c4081d0404403542074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15542632 1250 15541382 15541439
    0x10b07020a03170706060509090307060e24040c050603061f02120c0c0112060b040608040807020a260f030307050703030b040504030c0309080304060e060c0c0406030804050316 77
    0x500c0480c803440080d034005003020030003480d040c0300715101d10000c180b080e100f0705080091a496400308845c03004144c603d44001d80c03042c08203100040081d40007480ca007104404a8501036810b09071580702001c466500100e806203281807008215155605a000d4402191114218039004010600303116000355186d0a92126010b101d03801030003404104907180c125034159517179210b1050507641d1a81c3d24013485001500302f0306261001a49803240300181c45035030304500c1c5003518201044400d030101170802d031040f4004100c04001030340d0f002c0c421401800c142440c0b84011107480d00c01c1c2d1100004182d100e540346c1210001d004164004012242c3c020031605145460f001103050480050000500040c0c2103440c240902003416000189400f41700e22a980700c008031a10343e2500c0d5200d00491140c003010030140c1014082d2450450060810201f101003240c4c0d0a0302a00000f4054880e00d40c000c0d40c4001c070008007407001c0d003002c0c400c801100c50b0441a01141c0b43c58856410360345c41042d06500d1103a10785 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15543882 1250 15542632 15542647
    0x110c01050a05090d0c09060f0b070c030303110f03010807090c050901020a02100e06161202030c070e0a020d050f1503030702090c070c0e07080601031404030f0807030605121605010504050603010b 85
    0x940d110b041c021030300300c001030351001c6d02c0e2540200104090300404044480303d50000810305c079528111002950301c01c1841d05110301c0c5035400d402800c007494501c04a060240b001058400218010314000c1403290024108203241031034280884a00c000c188013040020010110141d80025540003400e60503600c50007a86240c04045440460440c050340c0e102e41c0000380810300139050343e0440c0f000b6005424407003040d080b4036416030350f0384070342180c002c0d0a4200700000c0010b180e102c00200d41c01403804a01629040b51014510112901111030a4141000b58148001440741003001507902c03809038010f616000c025000580b001c4002041810500340001d600c00401c610000c40d880241080d440c544668184240080d000200440310a40000c0c98009442a40903e20303070130358011905511850b41160007042d04580080380148a1424103845181c0024962568200c00802183c2c1c00082c06200100350f103044001441980910f0402c0300501c010710040e40c45100b200d044880c150b102c250764a01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15545132 1250 15543882 15543889
    0xa0806060d06030302010e01060b04051305040213060314120f040506130b19030f0c080c03070207080610030204050a0b01020c060715090606140102150a0c02070807090903110c01050a0509 82
    0x152044104075542003000010802d030b01500400b4a082c1c02070000d00c00c007621003880b039942e40030714810290b01c019000700b4014120380641c440703a082030010740380e458800200c1d4505004c0e54141d60040f90760b101548549000000c052003001c44054506641da45441c50105031503001d070140b400b60612541d00040c541c25412150403220001745840350f8980e48502c40700a9482c005040003c48501081c00d04c884046c7d201c0d024841c0c0721840d81c4d152a400c009441e40c40c440031a681000b4036040940c412901c0c040b1f0b80300820445144603e0a41004000ca1400c6205000642d5400741050326800d01f4080c1d4a04079a80106d20040200c50543d002d580721861401c12030082c00007400070490543c9002c00c41001e0000381e41040c42694054041c107807100601c80012a992807945014010000c98040072448250154118800c81c030810700c112181507031110f80c1c480c2402410360103081401c0c1e035011400c081540020501e46240b9100014003055115400044c0c02840b030a0020380820030300140610031a039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15546382 1250 15545132 15545137
    0x10e0c1c02040501090209130b060301060c1113020309010e060405070302010e011707030f0605010c020d03050c07090203010803070b07180303080406020c101401050f0109030b0703090b040c050906060306060a080606 94
    0x2a0000d20603c09565943d5006000b58855280d45006c0c0e15400000c2e20080c2c6036010321702004201901d011b00d581e180074011034000e0b4101c072044840c0321035210f00ba001a0f1300d04001e0b845c51488540010303078a0512040307113801c44240303a03561a000e03003240d010840070a07070104131682220340a0170100140e44c801001242d1807a948080c00300c003400b0802c2400308031940b543c0f100803000070791501001502d440e040103484000007000000d40c40404500101d001a2041001e003d0440241044817943c0782c84903a40300980e04260042074440e030002c038400c0f0030320184440c51604580c40c1d050020201c0d06201041504105900000e401c0c010642d0200701009210b904031082a5a0030003943d600d000425014400b61004c0c803520407890000c40d0000c50641b0b008071840c440c544050f100c1c1c04009296944000c05890300510041c24141d5800c03822011070340c10701056106074030509160707144d1820101048203030325002d402140a080c0601c1082801e8881400b10b0398000b5940c1042c40c425501d01c0001501c92 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15547632 1250 15546382 15546439
    0xc0a170c040209150a0905010206010608150411040f060c0b0c0405010203030f0705070f050d020d0509030c12071203080405060c030402060702061b100218191e0b04030804050111010e0c 81
    0x13007000110700c0d480381d03409808641940c40076400e503805d036607843c0c1c030499a00d0019600702d418441c9110301144240f07003d038020003900c4a0040c0c407070304107a0343d4020230b185045180d2000c0f001c80e0000480d40204090002c801e0b070700ca4001c1910b00c0c2483d0070900000c1d81c0c3d000040035074280f045840b000c0f0b03403002c2c0907000751040c4a50244120380c00c49a45d1411540b00d0f1000003041c03016100351b2400d0444c1070700480a4804204000e0020850300b181d0b0302c10040010007850003600b65000f11280840e0072980407800482282c000d8440707200d0307824546042498010f0050004119035414028000169110740403662550b80441d91a07844401c022006280102a01103030040b51250202003404016140c0150040c0000c803c54504541ca1070410b104503890a00013491040c1e01c448000c0c0075004042c103d000e0503005034a6180c031402e459014646169200b5003003074450402c0410300300107640e0300ca40ca0140c0030700c485000303014028030388070416540c10b0b034004424841c1512049240c0140c00050088101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15548882 1250 15547632 15547669
    0xc030203070303030c0f0e030c132307090e01050a0b092707120908040e190606030b0a050303070b0f150310140601020703030507110a0b0a020c0a170c040209 69
    0xa041d074903c1c0140041c1036a0300c00301e000c6040301e00100401030141141c01c210640145c080c0c4000c40070841040310704100350002a8407155120709501010180d2110382712241c0e031610045403582045840039016618562000640c038010350010b21250300c80301000011030f842c0040442d11031444070001100e044401c42e80c15640ca298940c51601400c0c8030058030700a0a003a1102c1c2030b550101807612050f5209100080c0001000b00400c110700750344e0b00c1c5120351245030009074814601241e0001ea050341d080741d001000094646d100200e540c9000124000105401c42c0210300c1c081c1d030f555880303600b0280289051601d500e000002990707816500c081c0704034102c0c0102610308902008001c9401002862950b62540c4080c0001130342550000501d602a80e805484441c10032400b6518064014400c0c90441c0e0800c00000000500a454001030a003100c22500070f801429641d20900480028940c03150b91080894800300e803111001041014801c1e00581c2c01596540b0387c0404602c14000c2e42034040403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15550132 1250 15548882 15548893
    0x501091e09180209130c080c09060d02010908060108061009050106020606010c0302010b0a060c060606020106030816031b050307060506090105060406030e0a0b09070e0601080f0109090f02030303070f030501120305040b070c030203 100
    0x1c0c03607411880e01c0d00e165841b45004401d400d498040040e560415032000d140c000304070f1404620246482441e401c03506105140c03070802140c42d400943d06084003a403104020358002c4042c02882c6070003e45d4100541110301042005600d0010020743ea20006030400d8117100034264240f080c540300b034004050440b40580401646d0303984210081c403440c0800d000b51030700c2d880c042d80030a0240c8103000c2c00c0e080340e402c50066401c01c0c0e89001754218904610408806124030080c0e0b1148090744849a418414024409503484040d9810000d0a90b480185040d21a188010050090b5035a00080e90140e034007a2030001049161258007034503068043c40041c00b00a040420080090800031f17290007a5003561119200c0f68a80c2001922aa02e042d1001e01400c5408001849054801e074003110b5070342e01400e81240854510b8021030b0a640c001d540140c00184509010424680c15005e028010107100c3e2001c0144e400548004115000e41d0051000641c0c000800310180000083c100c406150000d058a5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15551382 1250 15550132 15550141
    0x20a0f0206310314030406020309011101090506010306090201080a06060219030302040504060306150b0a0503010e040201030b0904050601050315040807030e19090902011b11042d05010501091e09180209 88
    0x58502e605102c1181d4569041a48801c01100481940c0440d1501d0b0021030a0000000065940c0001c403c24044190741c3e8045400209100700a000c0c02180130703000001c0d8814050000420a55005100008a905051080004541c00200d02c0150740035066125442c4200d0324088002c5e1180b94045640f00e070600e540030090003013a601607481c0c1e020045000c489255a1040407849001e10034a55000c0760301400104540408802a40e500c82c0c030500d400261207144900103801c210341a90b042c1c035164032050041c8580d00301041900c48544401c00705003114642035641e03400610600e03000504000e45400c3c04001c0d0784901c0711441d0364800c40419082282e84402c4650001d004a400590001c0c0c02c1b8040740340c00c03050301040d41c4442034210800c1a14000541c0500014001d00c034000c40380340181034041450415640381c45001c0008041001c2240d514010004080728036039004003141c00d003407100c20740403c0c240200c50002c95414040100d0003468465540807c0f01c1c60700f002a420035003020401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15552632 1250 15551382 15551467
    0x2010b18060907110709090f050109030c02030606061c020901030b0d03050d060b03040f020409080d021201051206060d0611040b04030b060901170d0c020a05030106030309080607020a0f0206 83
    0x940301d84826902d1801540ea01c00342192440440c0c160b0030b040d070700250400c0c442c50740c080d0040c14905006040086044041b03075a51421035272104000e03400a4580c12203002140740038889a0341017201107440c0341c05d0020107070541920100350348090fa0030b59070005100580340d012781c1002200344802041280c3ca20024100a0701c154855000015414035040000c10a1040301007507e000740e4000211401c00e4102e035090000030507420400355204503042c0038604207042d40e40000e2585d1440e840f42014554900400d00a020680c10b49010a0740c0041c410080d843d15903003106080700340c00c8840428004444482c100003885182c0001c03480401c0080c021040c06000504107005800a9a04e010280e0740d03250301e070001c00c811241d0a40c040c0c110145101105105008115000b40000e0611703c1403590303100040c0c00c5403d6079000f1004903202d860100715460080c401e0a40c000d00c2e50002e401030341c100b44d0781d0000ca0307401e00e00c00a2203400301141c11000000d402041c003243c1c10480d0038902c3c4081030004030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15553882 1250 15552632 15552679
    0x6090603060f0301050910060f03120503040515010b070201080906070c080703090b0304080306100207050307140111010c090312080c0403030c0503160b09160807060507020612070507021807080705090102010b 91
    0x1800c7c1c0382032250000380c2e03c001d00084421250840584858868000d504079423607807000d041a1800c0c4500002c0980c0b440415404034000c1401c0c48a0b550f507601144009844030300d0040082c491600000c080101803900002c440c0101503129101550700c502030301c1c003a2403500068200000d00c00c400f00403c4100308400000354002c140454408418556954089a558110b80601c03905600700e0349042000003a407412a26140005042240c5143da02d10641c5007101c40b480c1c50b0b070340010301d142020030610403100390350300e185100351074840e100d491702946043c0035100340e101c0101000074494840c400d000e003c0c81a21869000c0303010803a4940f102d402c084181800a4503202d500c0c0c05401d540380e801e11071503440f07801203903107003000b602c179540c90481c040d01c568020741e205070381050007004110f04c2404420849031098410740c03100c3d522201c1030f00501c1041300b0f9281c910340a210f560b17001e029800f9003041e81c00780e0000c51460519a00d41400d00100e025004011341d0b150469001000b1980c034840c1c080e613 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15555132 1250 15553882 15553903
    0x40305060c0304020f0303071203020c0106050909061501051e03070309060e0105040203100c0801171501080f010b0a0602060609190e0303011e24140309030a0e040b06090603060f03010509 82
    0xd050030345c007414100f09070700d03449421001000901e040c0b042c00c0746940203070003810b0380c501c40380000a29144e03513101056864804451340c171444d0700810200011241e5000218840c00400e01c3c0c07140c1002c900c8000703403000c507400744940e8880b00070120000307031780e18401e40000c40c010740e010f10144403c4059641940c0601400d880c103c6c0b0a00a9132640c0c24044420b103d0300b207628960f640d400407140d20300741c2140c000c4000d0001403c002d002c1d011300c026407138070080c803420f0003072507644000c00c541d41015815a003182da807003001502c9400146c000b00021a030008515403c56401c640e0091240c0390528900c00520b60040d0308150142082c82040420030003101640c1241c0f040e8000490350855501851400b0943e40a21030800c91a10031842a0045074081945403000d54200001682d0b40d5403440081e580044404900d00d13807000880e06441e81d13004031034140f0788200340c406000361840c60300000d0080c0100c0070cc0c54082d1901000140c840d5560b404580408400900200301e01d04060300c4003611100e1032039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15556382 1250 15555132 15555139
    0x60b0403050f0d0206060a0b0304020307260d170a0b0301060503070f03020301050604020301031707050325110a03050c010509011e0903020108010b031003020d030c06060605030709090203010f030602090105040305060c030402 98
    0x49140f50350fa0000c26101e04c540e000a0059030418201804201d1940014200303076050b20841d4004580d00300e045d004103030388a03280c2c0742c44600090522401841d05c01000c00c0c0c50704006001002e104664031f038219a58000742c5955010407103600c40e001181c014001c90b4445a858820a00001040f07103100502c2d5040d20300a9000f8017241d40c540061000341d00c020b1100801c050b800c5020325201242103409041c1c00b0303120354180c910f0810040c0010b0144154000310f80d43c540000402c8208012562000016680064607041c3c021403654482a40b1007952a600714107001d00020030050f00e0381b003070f840d92540c3c100b81241d0809090054130020000b05403408200d022404260011900090450943e446601011440d0079854210303800e0007680f503500c8e0011010320450b0301042c00019500c0c0a00360141c0025900c0c80d442c1c0c50304c04001400c8042907400030803654810801070040c140d6424402d02603d40280001d6a50060100101c600d0b21a60f44050070a018503014003000c0d0013081c004500450084 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15557632 1250 15556382 15556393
    0x9050607050307180e07021204080c06030c04030c030501061404090203100513020414070f0504030506160e1206041205040509011205030408030310060906030c0507060e1e01020913050105030a06050a060b0403050f 93
    0x8d40d40195489140100000c5034000300d58100140344c0500210340c040d88101304541015966542e060041c40c0d550411501130351100410321a541c819600c101c4004000c07242403081400c41c0c2c01082d200d10122690720440c0303440b0303000544100c584d20140102c007640074108014141c84001c801c0f03d46503064604000050070992051440380c070446c1584c056a4100c0040e1940d03480b5014032a25140800c0d84c00010310000b14000c201e83c3c0e442103404003d181c1d0400140405103003034a00261440d00c00d641920611800340001c1c845900d07503034100b5042d00c840305046031009005080c05880c40c02030f41d11800c103a210000c20854042c050300c401804480003a164107c4240e1142e2080d01500d819204560000381c0501000c00455480e81010b410f85001c0000e45d0000c3c0399010b50000d40b0500101010420ba4002841d048541840220249140f0148804101950604000030780743c601503840074000c03d0711030001c071303d8100403540444018a1030303e403440c0d6035568030700d0010b0312400d2419950701d0a0156 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15558882 1250 15557632 15557653
    0x3010507022a0a03150c230406080603030f1605070f06050a080601030f020c031c0c02060105010c050304050a03030801052809020f07020402041706010909050607050307180e0702 78
    0x1040e1040c0d002c268400a2012040091484201c0c6400c108541c8003000881c0000419202c881d10742c0e541081c0d00c4d000c280d040301d01d0b01c050810505107201d1454081c4807041c600c000b000c0350050302c0070f13141e00d4581940300e5140c41c0000381c614090344902c00404640004c40c031003080d4010350745039950741c8914151619165610103c510072141c0d80700d54801702d5010040211240d21419100d544080141800607004602650040498109002000b42c5920001c0d00f01c0755800300c9121000c0154a9010500503030000c460025203035101031040c6411300ca0000c3c844002c001081c825240545400b92031540401d07620b00300200740a2082c850503000d03828000583c01e0700c1d070074414130046c1a408a809440913070324103004100294401d2020071600c01c400d1100a005a480c3d0008000074040e040c00c110b0603041000d05941000c0c0c060f8001281540f07070224280c00110049021030b8410042d043c0075450790342d4001c0075541e0040d02c0007082105940040b010505038040240d0500611069007215202d000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15560132 1250 15558882 15558887
    0x9070e0f0105040507210c0905040e0307060b010507080309060402040b031b010e0310020f0405010906020d02070306050c0c0a050d020618120f0903071815210201020309030f030903010507 82
    0x544100340341800090041c890707818a80c002d240c0084043c503007412101c5040180b490302d00300d2483d448010139221580d00400036030140c82c5030301901c81104c080140502d000b10080c1c0d644102180180815190584400980e008105541e04650080d01031941c0345000600e180d1151000c036001c900c80e91902402e02000c1c200022007581d0740415040646e5038030010001581c506c4403a0021551610030003140302008040e030b0000d0418000d03400140ca4880c2d042c000090180c5c00241c000070110361000000d80241540007403102e00320380d00200d0015894541030340542461043c0c0f0700704a424460191924201712001410322502901c65080e5a140c2e1141c0380110030000c101b07840c2188543c050404901c4041418006055000203610490700d0009818046030800b1b1142e03102c81e401d001203030240712005200e0b0041c6098802c05105200500c0e0030303e04034407800183d1f030790080324140c400002d000171a40204101d03040d2520041c102c1d2000900384d56801d42d01e901220115010f9424607000c14103071070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15561382 1250 15560132 15560159
    0xc080105100e0f040e010b0906030a080d1802060406020318090702071e05090c030405010c0206060607120306030203100b0f060a02030a050a03060b210603060103020a1203050409020d050907 83
    0x10401000c144008403651002c81d00000700d0000c2e01da000342d10400c60202c5070b403244100d0004010200000c00c3c17041ca05400c00c405440c004142d980685c11000e0444000384440080b9801e41c442140700140c0b40301078803001c03030000004040094011400003004168903800001900d10030303056a0210a00a02e98014804401d00c2a240c03440980d00c01103061140501e41500c5151035621500c14440041d03445000030a8080140c82c0d2000b0040e0000034002440310a02490507030f88014002041e403401c0c03a80218810f8498030314042e00c512102c100c0c2ca25402d01c26049800111340040440c0c070844041803650004168030150181309012021415966003000d0054561002c070680295042ca1034160003510203a0188074807204145d9206070106140302e06501402c0a000340641d4494040c00040000c0c81158010340118400e602c0200108016590050000161510f81e00c1403201d1500c2850b0a80b9580207070b4200d20481800413400924820b1250301003441009204100ca2a5035074466001c2080c1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15562632 1250 15561382 15561389
    0x1d01060302010e1302070f1202061303020c0f01020a0501050106050d0b030a0f02060310180902120a0b0103060c02030d0f090201020706090303050904020307140a030f05060109120b0a020705070b030105040c0801 92
    0xc0d842030303e2055903281c682e101054400501d600949401d4496480e80044a062041118500607141c41c0358180d9504200545d8000740a01000301480d001d502c0107036458521800701403040d20b8060000074185d200b802740d00c6030039070300900a00495844540c083c01640041055800780c41c903000c001c0c070b11490001901001d40c1d810000c240f130030035103c0e001d004150b40700404000d420b8604a200099800c29440c03011541c034428003002030394825510400414001c404400c03042540310f55101c4020503640c80c2c6050441c0e03840000003455000e4a003040e8210b00900054040040c54030002c29402c0c6001c1c0c022810180c400da0170768012548540007610500c54500019000403001d0025020038141980159001622030402c0080a0f2442c0040c4501d5448800c81100007612800c050300086401d000e8140c00c80c01c2404c00d9400141490004c1511041c10700c07000c0c040d00345060218410214550440b20001d411006580f03c20b922044059501ea00030302c111801a4503000b81d480f00c0c18031800d8418142d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15563882 1250 15562632 15562637
    0xb04020a0c1104150909080c0d021005060609030c0f030f0a05030d140903030408070602040509150a080309010c150902030304120b0106140405060903280209130209040b0405150a1d0106030201 84
    0xb07407170070000500e0040800007412101c0d040e04000c3c1386a000010007440910749041e07070040c502c5115585060080d2203010f0480350040c0401c0c08148859900403030810f4240d5403e4505183e40c0d81544006071901035005030741061405091800000e21a01000415000c1c00f4031105202d80c3c1006003102104500071900c40701c081d041400402d0029a44800030301e510383c003840000d8141919400003500c07a42c0f040d070348070500b211a86148003d0f0b04200d00c0c018001c2c4518000355003001590300000e454900001d00052034010066808c91410303d1584c016a2859000743c212910b603502c0c1c22580c94102d0a0880a85446043c0380001030528031503203d600c108003002c2c0090b130800386441d041c81007582000c0031b45941405000800e5010440901c41030001d43c5004503ca8507105950041c0040048098271000801000c82c61400250701c90070b45403600b0680c090368404007a922810301c00e05104400084807020303201c1d601809201d5126810080c0b002e6425000c840501110075001c81c00c81d02c0a1100902 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15565132 1250 15563882 15563921
    0xf1e0c01060503061005030d18090f050a0c08060603060d0c03050318011106010b0403061a0904060204050f01050702150a021005040c0e010506030601020a080c0708030f03010f0b120c0a030b04020a0c1104 89
    0x40e05881227020300c203004203058400c0d0300140c4415010040e41c01032484050304517603074000c00880b40c0d401d0060b400d00c230708641046401401e0400101d00d140c80000d084074029a110b030440c4080001150280c1c00554020342a81e8449640641c038411160b042e1820340d000480800c0da269440d031020078138a048442c288a06450249181d8825010f0042e0400080c3c181005584001e10307070300c6103203c542c0300c5c510600c1d00581d00c500b003004014441607010b02c0d40d41009418410f080042c1ca40b0242403881440c2150002d8603520141000c07858171403d180710021450518003404204407125030b5040564801b0382d0710061300d83e03c800c207121183c00200d841e240140d01070f104c0100402c50810040281074042001d4549154903003845034650380c001410190300810000041040c000500006400741c0b5181c0101441e011421030036580c40c003800781413503a82100000b2201c414a0295100c280030340400751082d9110444108040c0420481007402d80d00c102e440b801d00da030145440c0c443c546040b41c0d810700c0700c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15566382 1250 15565132 15565153
    0xc0e0108030c19030c020301090309030b010902040513020c010e0304030311010c050708120405210403060f050702030f0309191a01080f070e0907090608030c0f0c060f1e0c0106050306100503 83
    0x8040c015107030004d40c10300003100780c081c0250710207001f90a0303994041c0d2100308070f10380b85240183c00e008050b4801070141303206110a0120f035a500c02da014010240703860253b05c0320320011549004010203640c11900d440002000010581c020000c1030b16248250001c0000321820141500c10348a420401802880100040c82d01049414030f03507500940034100b2103110b000b1506040f05c204c040e20100304101d4201103410802c0000d42c1c00390030340440c7c03042402e000c1070804c01e070007a5407030145950a40758240084001418804100181a00d03003000040c50f070404034250801e65986083e09820b030007400410030012a904600040d010f82e6007900300014262a4507152003079107810360140c400303c2070740592107000030240982d0042d8006000a84003443d683c4910021700c3e403400f00c209460102d59001034101074040c3c0e135100142d0720b0380d8000c3c5480961355680c520b20030305d4184c132000c1c00b40301081000c10700100031141580084103a030010b60443d03885072a40d50b420040c1c015075103e001d500d03501083c80d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15567632 1250 15566382 15566413
    0x4020301031e110406090f0b030a0f0201081b07060608011a090c0703020705060c01020c07062d02030c0f0609010b06130302010f1e030c080105090403021e0709020301030c0e0108030c 80
    0x10711903070f01402000d6010304142001a09a07800d551141803c0703034864100312841e0516100d0600409001c90052000e41c20356640c1105140250201a05110468000808982d002c28055601c4001c0c0a4215a6142e403864540300410213070240380b50661030008000341003440c0101103244004001e103480c0040e0f4500c0303001c0346c03030758000802101140109400084c00b502d450b009805074810744400541c99045040d640d524194076070b440401006041c0c003c01c0c800800c1c8820301314440302100f555002c1c00346201c200340e1952003020b1111071703144910b4122078603602e00455914001c101c0c41d0000d02030180c2c0d00c01000440c0c01200c0c2180e002110241d010401903019071098400f641c00382c1000114800d80c02410b4008410700d00c02000820340b10544a1075030b5038002c20b0580504000c403031010700c6c1e04190300c00030350740c260a9080c1d41e82d40404500c440c5005500700480310040642450655580d80c4900d00000b03c0e942038802e074400b450420340080f0300c00c100441503c02c00d810714801010401c0510640 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15568882 1250 15567632 15567683
    0x110c0a090b010201020c0303010f090c05030c0f070204060803071202010c0903020a050603060a0e0c0304020f010c05060f040201090902270103020c12030c040b041203020609010b0d0b06062b06050402030103 90
    0x1842c0c155075082102c06500101413000d5802010380b454881c02c40c0c2d241c49095803c0d41c0c0402e41080c1000010810840a480c0c0041074507244032100d00100d0b15505144085001042e07283c0081905100101e03902003040b100c07160300da10a014aa00030b01241031203407401d913210034540c00001c0d80011201d50600c00c42c04c145000e503500c107200605510b0441d03034880152030110000d40e2080c800840000402065003442444162020400c0ca01130200494a0711190380340c440152015584011000101c0c3c1560b01c1920040e0144c68201c000310360300e10007170a071000829809106075424200c019004d040c07640c060f10950b050444030801400840342e160144211942c4010124101030809010119151035220050005003441c00c0807401c02c81010309010349446070052544e01d090303043c002c1c51801d644680e6444020035a00c510042d8403601c81c400011544d00402d0f141d45025005803420307400e01c0404034403040c03020888880c100012030f101e4040c40103034442404043c1104c824080b920503c032203010710 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15570132 1250 15568882 15568901
    0x60f050a0509040809100f02150f0408030a090210030606021b061207020a060908030405060f15010e060c0d02010b090f0103030e01120209130b2814010909050408040303110c0a09 78
    0x4046103481003103000107005801089100001407047c040c008039040d0100302207007808115460700d607500d2514283d02429a00000c10041c070322400403002c02c0a99402e40c009103030007036008211800000051100800820051080000600c0f070a0310320301001c111844100420f202c0607040f50b282c003604034640040780c1c5020f400d0908500c610451107001c641248a0a14002d02c60b16a07940c5d241814240589401c0000c0c2c1402c2200d803000007800040000640690408242802c1407009a000300c0d00283c0c50340540126641c0c14042d680e01a6040369040d802500f555108655044d01030300e0f40c0c400c034151400240001404980107807041002907004a1030200040c4140c0c0015151060700700c0400c1c1c50501c40b00c40304030701a4480c03010600320720741140921040030b0b07034031140100ca000307607a041c0d0b0402203184543d841c5010407900360801a4445c024003006480006000c0c1b1090401c0e1400403c44d600c40e05c016400220300540c4441c60010200344010303913001c02028401e0707603401c011014004203108507 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15571382 1250 15570132 15570143
    0x122906190e01091a030109050708150f130509010c110d02070e0408070210030b04061e030b0a02070209010303020705100504051e03030c070807140103020309061306150905040204060f050a050904 85
    0x20b001031808240c4000c141c4424040c4c85080e2254588220101591805007511040c022840100035030403c1da0b82c06510f007141c044803050f400403002c00120300c50490722045c01c024503040c402002010340054116900c46615551107507000b1450805d050b88510040c111400160402001080062414008650454000d2402910700601903000804614a280140300800d890381005520ba01e440d22544008200449145840031004d098415420106020041074249400b000c0b82d00803000d0340c140c4070080d6014010242a50f140d00300079554054a200d8a403083c03080703c00d60030240d440b071010350381218405408039100365549980343d10380107004007160f80c25220a0110030f2119400704a600000c04040014168081c00e04071b01801c03051070185164185401003003400110107000590907071000b1810004d00c1c200d081440e0220241000c4400601c10304070b800703008149206640c2c821303801284202d404224140e0348003480300b09401244152541f217015820200a141400d030140c0b0340c014405d1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15572632 1250 15571382 15571397
    0x90603041b0b03040b040201020601050910090e070807030506090106060507020a0308090103090204020d14010803040305070e0703060b030c0a080a090506011a0403061a130501080606060a122906190e01 88
    0x407450b500765a0000c540560380c420800341808150750301407140902601041e03d419010b4038162402510090641c402c4a0030585e545800403e00c0e4024080c142c05000703124252400a0380d81d0074507980c0d4403000c0ea61400705501e00f800c00903640b4050070032901d07440d9019201e6030392145107403550030882c0c003c1c000d4207050640350403e600050360b5500c01844000c07500000052032811101c1c1035940080305810016560f842040309201103580050180104e0300140081c2c0441c0c0c1d20b00c2e504402801c000da0000009082c044140103031813011030007909205c0055910810341d9a10783d445103040d40c0300b02c280a820f40e001500140310b11101c050184810100301c03092580340070f039281d80d144112208940d00f1740381203a9114400c0858a050030301d50b841c485141c0410300c803950404030855182c46000d408280304880c0064034015440c0601c0b003e20b0382862007074041100300441c1c0c22103004000060f804603460820621400980d1411000350360901d00350201111030800201800d44000b103040072184e0500001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15573882 1250 15572632 15572639
    0xc0507090525031e060611011109040b0a09060303020d0e061603050d0908070606050906101409041d070501020c100203070803090a0f0f11010e0d03030f1803030911010302090603041b 80
    0x44c807507141c82c2440e44a20000b011840e090000301008a044803006141c0d040c08403118900c1c40032800d403489500200e0740000c1c0c4100340310014a02a019a205203211821b02e4000800e040e004034203100000047e8540c0b894500c0810102701140c4140054122040c81fa140c0220101e8811405040b03d00103c25001401004584a4042c1078116000403504141c46000034459418500c940e0364200900307844080303400400c45030161506022400c01500c00f140403403c0c1c080c40c0e9a60300600c0011201d030304c083e50000c3c2046c2d88151114020b0054a01620640e01426501d00703107050300e0000031405078081c5003052166a5001519407010b04880000d00c18607030b503900030403149031318118001c0c81110081f0305c06865103403e005003414403810a06200c0c0c505a88000358550609070003c65506250009865903540c100500605652040c1409592001e42e03500c00c15405038080101c0e43e0107401c0c0000d42d501c124004405900c82c6240941d00448184007060005e01c075401ca0b02c0c910003800d0b281003000d03078030b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15575132 1250 15573882 15573911
    0x308030a0e0c04140405011a031005070216120b01060203040b09010507060e030c0607080609060109030f0212010e150f0105060a110a02030a080d0f05071b05120301060c050709052503 80
    0x3d13003210b107440e807200c0300050000f0440c003403184074200711000d4441e01721902c0003000241c40d45550072114025503120700c0007403400d074403e00180300b5a09424103903044283c0c580140541c1a681c00300c0440d080700b0361400105046000005841c11103080441042c544000000112029002031200b10f40842d150452000c04101c184003138a00520100c004040034548110010a690006001c1501070401e0311300b4400ca81c0d078407103c22003c0c6c13608901510003d803071500c00302d0340c001038100c0710043c3c0794030300000441c041d00b0224003644840d1062a00c108075840d1b0350f006450006003881b400350301003420881084000e001c0c4102184e140700d900c054030070b00d003400e402180c10083c035100d04030f031102c0c1d00103007440b001202842036440d031aa92003410481f601d00414042c2070388150701c42c01c0c52030401400190041040c03c03c4125140d00314042c04a0320b0756951000a045881c40c0366084078640581c41000c40c103c4442e11070b9900c00c1c44441e1440844080e0340315000860101100d290003010f0302d40040151049 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15576382 1250 15575132 15575141
    0x60a030b190605340611070c1512050105030606010f050c03030a0618150605031f080105090105011203020303040201050703030608060403021501080307030801180b12010c090b03010308030a0e0c04 86
    0x79a881c1d913552061554004002080030082c0c0c400c0c420a186001038002da208803c500103154441c40004101e241030700c10304103c0c0240c03036006042201184020803901e20841c40d0400da071a0a850350301c0f00c00510818601500c009019141c0c0641c483c4001844540c440e0000005100c07013820203603d0310108030303801da0450b80221080164140c58100c100080b04016001301e85040b0b00e4174082140340b501c00c0800c01032210f0342c030030740040003c0480440c8043c00c104140c1c1500c101c8055448160f40d41d04c40e00710380601011619050554600000011003038400b028290905916902031861070391154010344140c4c12601c0140d00300350341c801021039594400c122207402503001c0c3e0000c24031382600d04d04590900750140c01040564200740300400c0040c0d001066141584ca1a02e22402d040c4072880142c0c1c0140424502d40d5840040228440e070030f103c0c1944100c0340d041c1c8a40e0b8002c0d0301e549944402c04135200a100017040c1e89230410015411880c1c1364007100030309480c03070f01b80c03604001c05900040558 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15577632 1250 15576382 15576389
    0x20f0a0810050103052202030309061317010603020112020c0c04060608090f070609050607060905070e010915030f031206051306170105010803041710110403021806060a030b19 77
    0x10384010184020014580801c10080c002464240f050380380201c902034800c4d441e49200d100c0f140d00c3d86580c00443d603040c41564001c0307c0c06003150f900d80c28400c8400841100601c96140c2307640c00d210301c0040c160018003481040c0c0c0d4040c1c561201c2c80c2e81103c0305100039030112084290303d0184070300c850010354a81c000d01c0000c0400b80d0b40c1d012142000070b90a8181500084080340340e1b400390320200400781e00084c690b812140110f8480b5218000e0341483c03005010030250082c500d0007650707004526a0550760300d09060b52440780080286040c83c0300e200920340380d54000a444150200c682c6c0002910464942202c4e2003a22008128250b40e0b8000c60407480020f00410360103511a4070502a540884070b4811440c15000d000740465494000c1040e201d00c20360240e1180c0101d1805402c5042c00308100c4803540140600c0200200401200c081449401c2400101c0c45199a0503026030441281d03c499070240c07000030640313450820507078001d400a05400804c290030810008140c0010021246098000c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15578882 1250 15577632 15577637
    0x90c0303080603010c03060608060d0302011103070206070f0206010308030f0a02090301111903110d0903140f13050f01080105040c020a08070501091704030507030b07090503030a0f0306051c060b04020f0a 89
    0x450030200200350031754910030110401c2601d4400301704011030b4840c05803078200c41c007500c510200b800d00341004ca016048006031461055800010f1000c640c1d800107103140b0031318455451100c9201c04020480c0ca0358000c1c84003a11003502480490607000b1120401c540221041100625288108000c03d007500c0c1e02e1908054442c01c00301e515444824908403403035103042c0c245410419803082020f080e80034040c0d83c6608401c0d0395546400010540a00b09000503116401c008580f901107103628054940e008403c420700e80032107143d0001d11800c00071030340d407941001612007100a03800c1805100c0100010700f014821481018030718004540e00800505100b40514000b2a0039007150a00a84034540707501814601c8070100810004a10042403a4003a00d43c0241541055101d48608031031224098200e00e0b414040040c0e01540e041e00008000300c2081940c9040c021142d40320b04000d003a16640c0320904ea100c480503044000515250321900c10594000d00060801140f018810a2074011010f504007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15580132 1250 15578882 15578897
    0x910080f010506010e04020903100b0301240501030f0b0d1103030409060603061d010305190c050603071112030c070609060609090b090601080610030b070210050a0c0e0d0503040513090c0303 83
    0x12540c2c42107044031303c1312007550154509048e078000720396511504001200007554602500466680a401a8500424446240e030b5403000d0101062021071240c45400e010034680702c5280503a800314003e4203900e40000300304001d80e080e582c440c40d11201e204640389a050004000200e900d030312503c00c400c00340c1415940080d03401c1c00c102022140440f841a0007c0148090004000082002960000000410140d09584100c0380340c01c0d00a505030390841030f40f200001c010440c541d903014400305a004c4000c81142e80ca681854100401403200b42d6000310814802c1100303030702040c0d213600800d0340395100e01d4001803170907590803401046540d1502d0032504004188248040d80204000d80ea000d0b1156601a0445042c06000004102d105d031000606c1e00b1904400240c059009102119100342a03010a000d586800b24085c801040d00c0301210004c1000d01440702c806040101d250010715503c0320003903280c5828482081150301e03c42d00ca07807501584507601e52000a85006015000394800e0301c4803003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15581382 1250 15580132 15580141
    0x8070f082104030311030f03010e04050613051207030e09100e010609060903060c030e0a080406030c02031608031911030a06120b0106110a0507030507031103030301030803060910080f0105 82
    0x2400e02040c4200c488029480d1040d9410420780141110100c03030f45410056500c0c0c150305d00711411405a403607000040700c004000021020480d4042c0c0c1c0c0f05a01c40d001b62056a512407500300d09803448450050100c3d444080500622004a030091107454040c0c1840800c134002d42c4001500d0309400c440a506503000c0c031804028489584807480d02400450a006426508015005100d01120310024004585640d08104ca59000c1da00c101c1d0710002c000c05442d1010094200300302c295210b0711452000902d001d980101c0c0500c04025691100140007200b48060095100e110076600040c0540c1101c2c1c00452038181c09c0c10040c0300e1300a091088030f48054072441c080e0300c15004c868843c0e1022113034032006803050000a078184d8100341901c075a8144000d10a03202e0000304d20b400c8403c60011f00da442109404800d000000519408580c40382c4041c25401d80b0501c00d00d0b0302c80c0403c1c40001c0101d10144003195071440c20710051a0b20014000c0410b8050365688682ea21705542e0620b0202c0d681d64900502c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15582632 1250 15581382 15581399
    0x10515090702030313061d060a060311030309011b170c0a03030b0609030d110111040914010914011502030d020406030507032d0b0a09050403050307020c01020a0b01030b09010608070f 80
    0x2030354407110034006075003185071400300f075a5441a07042004140720355400c43d11002c458854108141014808100c8089280145802000342547d01054805140101c100c480c00e2a00004590b840300341a52503d00e05803000308107107119800c0800480c1c500035a066000703117002c400c00140c000c00071107800902c200701584c100507048a00030140c26000764810004120a9140011500c0248610340342c40d441804c0001191801840700c1000303c030001600280004062110340c101181c080705019882080d66680e0751043c0449400d2030051141c04146d82c010050110018104440c1300e1982c01600d2070200540129403c07070f482604203001180c0d889051084c41641072040e42c64890542004a550310100d1110403511024406500d20403034036134200c0c0085468409020004000103102071245d07080c103150180850300100c910f800144143d0b0403003211503200040741d116403034002450403da070342161128007800000030001c406641d00d6800005610504001000003040200d1101e070000341402d02d03c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15583882 1250 15582632 15582649
    0x1509030d0507030e0102070f03120908010c02010b03120306011b05010f050c0d05060d0c14061312021311030a05040f020307030b06190807060e0a080a06050601030608060708010e07020708010515 85
    0xc2504640c8181c0088c040c1044200c0c500054a4200701c81c1c4015444891085540f50f031144c1000d2155400c040c0c0e2480040c0e015000718031800001c03010b80303504445041c0101c1c1507010841b501d50008010700c00e9070b00840068030202d4003190103140040358503040030100320180ca0007503801e022100f20018984410040c64402e4a0b040b000c22600481400c44c10340f01c513050385982d40502a000c1c00903501080460f0394410440d4404000b01d240426269070726004140c0324a10998181d0040c9a02c00308620303400c000b0f210304650050000005810f54071043c48100040c0002803048899500c030516102c00360b41d041103894020b500c5000c80d002d16240480901c42c1c100148181c00c2509520550184200745000c5440d20580f031071490504122034648002500c14005903115003414005d0b81801000d0040c0d0360001031150900b80c80c1442919030307511900d9038035101102c1141c00501d01c180188443c95104031b4070750700811a841100c2c4c585481d690401d00b120340503a01225480f04a003c9014941440c140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15585132 1250 15583882 15583907
    0x4021201090209070503070e0306390708161406010305010605011b060507021504061a060702060d0504020103020c010608030d0e190b07021c02060a0605090112021509030d050703 78
    0x7800100d000354003103102180d01130304600902c50040001115184584848000010300500f2540d0501340300c055010b062054201848165100c1407694007540b0200d0040c01000300ba0500f1103180c41402d44071154a40c109445400041d07080101410108403d00c420030075030b5404502810303080d451889c105007107030465401305044c01111001e65080c0600060a030344900c3e044072000c15141c1e1010004ca00344010401c07451401c4da0181c091000703011866200040740f00d091841600c0e2111040100200c0b80902803000f54440c0c0c1c01c008240d40314a00782c11042d08140306060140c00c101c01c4144090a54295400400c0705a00100b480c01521682e80101400f240c0c085020b4080e01d4006461078007409000b42d809130002d0084008164164420010320158000080900c400c4e403102050083d22801c0076142d0144041c02e0640101d8686010440c00f41202d00d0a000c4078a16202c690900090340070040e08140300728014080c98826407030500014085540303ea40341a680c00c10381c036001e05100c18401 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15586382 1250 15585132 15585169
    0xc0f0106060504120609080307080f060303070b0a0c200a05010b06070c050d0302100c0e03240a1a04050109050105010908060403020706051605010c020f1203160e031c080402 76
    0x1042044002e41040440e010741d200d84001000700c0c03819060981c0a011035210090000b0000401c120388160302c10286401283c07169480c1981752192010150359000c4c1c01070141c40c2c45d0807035000c9640c1c03d031701768042d14510f4540c0c100003c128102048540c501c040c804c8038440203800110340601000303400e01c10b04e000c6c440101c802c1c604001d01754a8012609186020345402424425031f071a040c14003c11600004000702c07102840818500c0d0002451003c000c02c1c5640244103400c5107501c4101c0c2d00f448070401e01d800b00a00801130351801190b1003d025213202820580c481017503600000e80741c50041c43d019140440001c100c83d450100018020541c0b540b02a505400c520300b4000000c1e0b01041503c00c640540c81c24546070390158074168040a42c0100040442d840d060306102020780100302c4240e4411290183c1e40b00e81202d04141000f88003c0742c0a00211302c030040d403035030300a014002c040c00c040c0c0701900700c8582c05e05c10006039045070740d00181000803071100010401181b510305000d01c15883c1e02e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15587632 1250 15586382 15586391
    0xc0c0402031324060902040510020109030804110f0a090c0f05070b01030b06060405120601030302010b03010b0102060c0c0102040f0b070c06030606050304020d02030c0301020d05100e010605070303110f030a020c0f01 94
    0x80c007050b503035210728180c010900784019412120580d030f0b418000115500740340c0104151541d8001900003076005114080c051407003940303495002c80c0103202d0380040d560542c0b1910001c6c0c0ea69600e070080d88211020b00ea912040c0915403a01c0c030f49640032103402600f1945030000300c1007003450024101480c0d503071009080080c200b115900013810a07080e2411280d0011102ca0035417180380005640c0d014a070061900281d075401e041c0303000c841c0010081d0490780681c0082180d40010780130315080c1c400310a140360159108c100450310f0b003524800244181c403140340006041a88031802c410b035201c80f90f4040c880b01800030600c103007071280d01018a00106510305003040190724062007c1e003207000080000c3c1c410100050010b05648003488030405086000b0001c541e10002000500010001521a40707502c007001c5001082d0090003034a280e040e5680354070350385d08044865a003207015204441c4000071016051100300707581607014010b94025000d0300d1002d0384403007203140d1141c40c004400300140400d030b060 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15588882 1250 15587632 15587641
    0x204180f1505130b04020d0c0201050402010e010302090a03030507050a080304030c030e040c0f030f062c01051507020d030c0507030c0e0f060a06050a020705030601060305040218010302100809150c0c0c040203 91
    0x2100000041840e10000101d038071306000300010000e024100c0e680228506240304200000d9040d0302c26481079100342c8a05005c40c002d83c004400300c0c01190340f05034020320341c103000340042800342c409418080d04c154102e800c810507594425000b40c1068034114003048030178801c5c504060300800301c400e500ca02139030104804180d0903401441031802803601024155591550050350780b2581000014201c413014114241c402200b203041c0110344440d41000c0541c8140c0041410f11708040e540700c2c40c080000003242003031929001c110021540080850500204510304000101c0a2107000c0c0118010081125444c0c5400410350b541c0c0f0780284852030b22564082008115034a802d00d42e802d071510351500740d032a01c288510070703454004582c110a60511a14000140c3c10b035141e00b2084c8503510950b50030700748181e404140481402d00b80030081d440060320046000d014401c00425501034802000ca81c07240d070420541100d011801e039544181e0041c00a210f40016004102d800351200d8181c0d01140b440c80c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15590132 1250 15588882 15588889
    0xa02090102030d090311070e100f0803030105090612010608010506010f020d020a120c0c080a03021501060207060c0804030b040b0a0c020708030d0e010b060c010603020f01050304030503040f060204180f1505 90
    0x101000405810340d60044c580c181845050311104025054080b41d04081d1240c4005410041c00c803000b680c1110000000b1615030b1740080c200341100d0002005504590808040040a6400074030a070f8000710340c1c80a454402009000303048c000c0405030700008003414060001040380180d10a10b80541d0b00c18076040c40015030000350001d110780c000c0002100c02c8481101203914106504c0c0c0500248020030340030801ba43c0214101d9460b074803035000ca07048079900d2296181d001c2024030850700580c0009104112890040f956046e0551161007101d20b080e4403030340c89040c3c1b140d00395002d5441c0e00b0708208001e01c0075450321480d140b103181400203190301482c3c138840c40da40c0c0c13207410b000030041500e0340404c0c40f026500350000001080300400241e110881108428004c121600c002c0e4410b9080c0c48201e117035035020f1300482c0c0c0141d070541e903164a03650316070701c444030350700705400301110095801c004c0003030b0324040c0c0d400d4580f204580d6040800c22113a840e500030255041545110340704806100c4c00c0000d9503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15591382 1250 15590132 15590137
    0x60e13030c0204020c01090b090f0106060807030203040813080105060f150915040905010303050d14010b0306011b0606090b0909010b06070b09010905070303051207110c011407020409050102070b0a0209010203 91
    0x95162814501c2503000d440800c01900455408081c19820001107000f08074507c9111449a040c40c07044420801c0600042c500b030328480d00c41c12010640da140800c1c40c1c40e100350005c640c414006c4d140b052078015030803041000000d441d8819078183c0d540c0c50900401d031510080001c500c207000c81d000094880a40240ca0182c4204070341c0c14824201508405405141042610014003c0440410a81d07940b82030280465002c04800000140b41807080300e1058a0b00380090b0603155649a1681180c0c1c07140c3c019108200c013a0800845030443e480c0d40070014686002d0140a48184440840c1003c204411300681407006404107c0d40d904050102d022921440c003a150340540145508820381c58518140b4010036a94401900e0b602030240b010051641010040003101c0c034100d03a50300c0b42d076550300046544003078468400d05035070030549110803250300c41c50700c4101c03005030b40010304d01c4d00846900240848001036030480d40740c0d401107405000d120b54960b01d16480155010250700c3c1c8011400001c4d100d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15592632 1250 15591382 15591421
    0x40504020702040f0203090708060705030106020a030f050712050408011a090604050402240909060301050f07030e28030e090c040308031504020304030315050d03050409020a02010e0d090801060e 85
    0x803540070600c0d4095650b182c110320780340030f202101190342c2e04103015400d0f1941daaa01800e85c4030302c1a40f02042c2d000f80314604480c100c40042d4040e2411007184c1c2c1c0c1c100c034a425807000f103200300601800f42001180d0299100642610725403241da903500d181c90802400d480713010354940c0664103c101c6031015034580c0700b0f1440e8441e9040740c0c001615540ca2000800b1060b00c43c5c0080c040e100800900c282d140070348001070085801c1260782d00c0f8280c0d42c0000b0942a640115014040f4003180e1012a07080c078000d4106108040c10b40060b40d040c1510071040340c0340c1ca0b20f8011b01b20940a0340b030b0783d10300c1415003003c1540401c2d4015a8880340c0c0d0f141c850045081481644070040c00b020380000010103024241100d00c000c2c501c0100203554a051509006019212800090a000b0988100001c0905e0000e40045540754941c540038101417030880f40e5002500a800d5400c01c0d5500c0700507440424105100020000045031a07101c0c1007402c0c0710007d0308488040d0480307480700301082d040c4040c201c403141500707044 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15593882 1250 15592632 15592639
    0x60809150f04020301060b0a0207091803120507120e060105090703050705070f1b0e04020301060f14040b04140106020a1101020303251206080a03030506090402010c020d03020a0b1017120405 83
    0x55150b0744082030060603d40d12026140340e0126200d80c100f64042090350454403024400d00c022608040030111074a032040004000c02d5039500c01042680030340d0400c40c1c0c40205418010a0b0040408440d01654402e0310b018509400100052000345001160240c00c8a030700e1a080225107040000070b03119100c0c005024041030782e8902004100050100881c901c15078018111a070284d0340d08120040706e4094404074400d5003408000f04c0d800320030380701da081100da070000030310300600349402804000c14640d04819007043d199800c2c03408844403540311500a104a500500740034039241010780c81221010304550440d0000c0007441040320100000320300700d1085108000c8603800d4400e0580d0104030f005810342d00c41d4241000000c580030003151500e01107000b510300b401150740b02c41c01c104401d0012a030007400304240144a1300982000c0c134181d01032601c2401140c0410007503850f80c0803000030482c0d1b10100460b9003e401d00c20740344036515240c1c2e56001d03c030061401e180c840c016180c0754041c1d400f03211300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15595132 1250 15593882 15593911
    0x6030902150c0c0d0c180b0f01020a030e01030b030102070f03080f15090103080a03022205010f0801030b01030809060c010e0703020103140f0a0e010b0a300c0e1b0c0706080915 77
    0x1485503100e0b0301e400806da020005401c1c5540401d1800282980c80642c0d40b052045092018980d4004100d04c100d06034540d032000e80c212402c50042d00200752243d1007035091341d4240486800515007401d900701141c082e40366a03806240c212011207055100404002101000360b0340304030140ca401c070702d003415268003541c419192200032000310000e0141074940b4542c2c0c50301c0294203413030205603000201603d0302a070320802d440c145943c055991880030710000b0240920140100080b0300c1f030001400f101103004102e640350044500d0300343d0a41e6203101a10f41140c0000d0010000c40da0035100e45500480171080212040c07400021880c1e03941340091500c00750a4a54840e080250400e51014100e0070000704a600b0103601c42d4061301d41c03454010201014104040030381c0d5510501001d11140b89a804680f840c01e07107040040e4080000c40103840d4080394001c100c8580b500e20395640180c060707400c80f00e00522043c0d161131401401c400c4007510150054000030100600509503540e026072140100641c0031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15596382 1250 15595132 15595159
    0xa03170d180c0302040c030b030c04090203030702130204090f090201080a09030311070803010905010503010506060a110304050901080a03120b03030403030c110303040611060106020d09030f0609080406030902150c0c 94
    0x40500070301241c4054040980081c6410001012000e5059900a070303000c110303c80e04040e0a130100e03042c140c952a49035100c0900c421703d500e01a01301c0d8a496101400380e9007800a15070110351142a4220012101038000c00d003402010030742c0c8964502c1c0440f080d014000c80c1429000a042450041c295a44490b04c45044000781402a004134000800c0c412466a0351051400c0103201c0b50401c1c060180700a080500005962505001d0700340100c0000b40340030700c0d00d4036085050b181b091109002b00307a01d00041c400080d0a544003d00e50703000300a5034000c0c0500070740a29008000c200c5002d4607001c903614101408610707450000030790f41626890301b4111401c0310340e1b0403c041210705400d0304a42c98400040c0c0400c04591001503150040040001c403501a62039503003ea0f202c20000340c0c041c0c00584091001c2003c01e00c1d1005102c5918000c1a0020310520710b901c0745c81840d400b40d00000d010a4035040640110308200d80195840e0031000600ba003005c502541d0191100c80c1c0e40415441820240002c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15597632 1250 15596382 15596407
    0xc100b01170604090b0c0909010e010b030c180409080414040504111002010207050d020c0913021806040b0a0303050a0e0a0b04052202030708100b0a020c060c07081902040b0a0317 78
    0x1004e82030700040c581070145032540c140c04450380004102800340c0840800080c41e0386000c04698165402d80d5403480c110360364001610b0503a080105906182d0404080010340d80d121442441c6655000d99911680d8500740720213000b2606900030210300962600c0c08001c08210041d06100b42c1d08422500d4150509081c0001c9002e800fa8002c05040e5003c2c80602001c0c4680006050415043c242c0c0c1d40001580d4100c24915040101e220180d000110801b0550140b0030356001c030342e40710380010700002d911030051022a8211245070011404981d000030203a1000740c11142911254608803065207502d030820301042c0260042d4810940640c48000c0c0600210740154890500c150f0384650440d00c92800c68002007a046040e1615284007440d46808100412520300f195a4440c2c0c036001041080d1044c03051001b161f1000c0842102e5008a00d00410401e405111040300c035451001340704c5246807540100030032a041040f559104640e010000c00009002c5515100c0030300700744240340d40380d180d1000780 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15598882 1250 15597632 15597641
    0x220f0c080d121e140411060f0904050402010912060504051c09180207080f070605060618010c0314071a06010201090f0303111201080d020105181b1906050c100b01170604 74
    0x40f1100f1410042544145248000031910681c0551440c0c1d0803501258288020391080d40c00140c880d00e01007060907e039050a4101d00d40041c41894805a165960321500130001d200b8142200c1c202e840c3c0c002c0c0400d0010411160b54004014442c0c0100311011281c00703440600300d80324461a88040085200c0740810350350580b0503190700201700b6655440440e400c404075521070141200c103549040c0100323146003000410342e0001e400c40300c01e031b01020b0303071020066400550b050302c00c40420010303a00404402d900030b80a031500d244248050103115451030186417101e030004141c0c90440e0b1514041c800400c03170084070a2092500740c00c0004494507603040919152140c22030304081c0c5603940000141c55400000c0c541846c0099a000304002e403103008082e4a5864045848941507000c80c1c0e13204000c00d04c080700f503107000034010048940321000f038002c00c4580825a000c0d03008540089460445d40906115403d1840032046040100342055030018016881315a104400140c2c41c000056058995a21 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15600132 1250 15598882 15598931
    0x50117090c03070b0a0f020105040b0a0b03070816050a08120714030904020a0c0b0a060e06130b04050405010c08010803030903030109050618041b080606060f03220f0c080d12 76
    0x243c0e000e4980f60f841e40301444c0d0045902c0000190601d8404900500c103114040c0600c1c3e0007011071200e91604040d480142100c6003026a06000b102000200b0345420400032610306115038106516a00d01010019400702503408031141380c00c0b000010344000091808c4460965000200e10308aa058504183c5180030324803100da002032001408109603a088070510041601c15104001c0a41d0391459000a0b10740c5449110314900c440f60109429152484104207401200b081c0000d06d10016070008084e1030042d60180c0c0d9a9554064494031903a003c40341d41e01501d2840011460350518a00c0e84c0d660b480144529002156103070301090440c0d540d0010908400e91118070011203003800e05204464135242210b0b89159840c8080000b220080864090b1040c00018140e40c00c022182c000b42c0020fa000500200b4105800b9000da0119803001070b222400e05d000b800c1c10700003441e1900d8419020f900c903400400d596400001081d96555010b10349000c200307184140400c81c4402c00802c1aa001340d40754 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15601382 1250 15600132 15600139
    0xb030103050303100b160204050a0f05040b07020c010804030f030b01090e07080a0b010c05030904150e0702010219080f1302010201110a0c0204060501030e03041415030106020a0615050117090c 84
    0x1000006201c4004042c0d80114000c4040c2882e1554810351022188103400460710003400769054070000d45016440b03554403010102005c906200404610021260b04450171102035030381c2d400b4405410360420110980600070300740300041b03040548001d0000d00c03181e5103207000c040e1181c040d11801c0c0d00c0b0304070041c0106815401070740c50b81044100508030020032a403402c1218a04055400303550301c81c82525861036007080180d850030078400c0c2440041c0c068118440c01070b40300c012001a0a141a0004074859850b590005031140c44020344840da40e0002112281044000011722580802010074a60001c00c0d116000055001c0c1d4030050717014141407040c0b056160004100001070a42004242c1000340c400c0341c08010303d54803500103608840c0d4444001e0394590082c001481b80d0350b442c030120200e00500808101c1d0b01540424003a4041d84241c201000581201900108001084c001c14444189480512180380e0414000a00c1511001c4100c0c0e00703080300d00d001c2004100240b110f06010140903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15602632 1250 15601382 15601387
    0x3040b0a031a100c11040603051608060609010b0d09030e060301090911030d02061603090b0106120f05010e070e010302250311190201030902010512010f14010c08220b 73
    0x10041c0040c0706049105448086000718036040703103046210382d04400201d45400c5800d44841c0c80c2c45039200c0c61521080d42040e95820003101240c1d0802440d0070040121542c021901d00303018010b824420050301e024011511000140010444001136034182c0785842c400207807444940c1800c640c0c5071400c0200c9600f0100c004000300d40340e007064110803a00350086465a5004501c10f0a069944900e80342c0d000040c0c11580102c0d81c3e050941b041c0180d4403405150128600d005070311003503650304003a8072200208138420412041740340507000761b03541c038a140f0f482000a585028601e840c032000080049003004116003101c00203a0090b4107852201e04400c2c4540c0000c0c44034080e4101602c7d011000b41e01240a1100c0103c52a100080034060b4144000c003840f50803210342c0c0150041d05108c20200e05001050100c940466030040c200350003455014866145949015108044d035088550440c0c10400c00600c0c0c84003050720401140c1c2c00c00c00544c0d410600c40b0145409013000c46290700700c4074070700c0c600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15603882 1250 15602632 15602647
    0x90b0408040801060b09060316020a0c080d03060503010209030d051e070501060302040e03070f08090d080316030608010b0307051201020432010e0f090a02040909060e0c010201020310090c0203040b 86
    0x11030041e0050301e0510303000b005800d80707410030340042e400317010314843d80848100b000803c064007000d24403440784a2801142c1148880da80d44907030300d01c400e4000c021075512184005403c1503040c050b40005081c180c000b146802d083d540420344944000d1807200c10300c00c0009103001c588150708980280454206425a02c5d0b2009180082c003814007480142d100354200740c081c443e44c220103c104c610040c7d102801d0322507403880e0b90b12010b1a4200c0640075500a40d9001c021000c19071600040d8411009005480c0c00540803c0d4041c0c00c85005070000c3d034440e85440480ea01c2d035140080c0140a544044407004108031301c84451902901c229040103111000b1151001e0340b503d943c0e0320f0011405030080804112941d090011145181c2490055520620b81c100408190030007050598200c100c400000d1710b8261981a40020342d03041d82400c0f640703240d80700d800e1642c1c02014000c40081c58000d00c001d41c81c500349550b06403000e1030213000b04074072141d4401425808038020001c89000f00082c1580380d80b107003039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15605132 1250 15603882 15603893
    0x30112030e06040f060210050c0c0a0605040215030405010c090b0a0e06090402071205070c05090c04050105031801050c0705070b03100315150b0d0c0c020102120a0309050f01021306020703020102150604090b04 91
    0x840740b41079845408d00007c2800f609040081d00c29451a20004248104c7c3e192148405060302410503a00f2500044410b07000e043c40e00c000718403070741c042d500202e40241c10b44001480c071826544583c203041c07018000d442c42036a00c04c00d40000c00e08121042900d80403c0000680284200900108890f80d882a040c21030394100000d05245401111101ca60aa4480c20b0066603242141c1c40341030010100010b000543c0508003440e00f14044007480c813090a10680660308503942610618581c2a0215080f02000010880e01e4094024090741504604080349481100c400328000105024041c06603c0d030034035500d40c02180101c600d6005001119230b00c821200340da91084440d458103c4c00e01070604016802690950082a41a4000d0002d1079032400300c0f45041d08001c1c5081e04158455680001151040003183c480c01ca040b80010b03511150102806111703505a48960151340000c0e20800140c0e80204044021401c1411030ba0a5a6110f900160007425250300050a6808a80500c418004e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15606382 1250 15605132 15605143
    0x10e13050a0e07080f03190e03060a0b1003020c1207051204060504050a0504051005090a0605040e030315030604030e060a0e120d0908120910050903030a02010207060b06030112030e06040f0602 84
    0xb02c1607800e0381c03440c0340c841543d907450b00c8158214180960042111b4154140d60713407100c5407055000d14008400f518486c0002c0c2c00c100e408d076005442140c8400c24840741d454040421303802d948050408516003101c50212640781d283c0341e120181e40f440b010524400f480001e1040703950300c013000c140e145c1e0b036507071141d10280694100e8007400d4011600300d24007103281e0405200d024003c82c28641c07a0000c0c50f16140070001c0c5050020151034032140c41e1800010f15803942e004c0e0391101000c26000e5a00ca1070701a858100b145281040d19209a10030400d100c04260080c800032034445060f41c0e07039945c84603a4282079808405002c0036542162504803078041c02c20700410720703030030100c026600e44080350394440c096a0344500c0101c40400050701000607e1013441c0c000702100303104480d800c017142081f0401c00000d0443d0450482140543d400007903440c00c22419110b081410f0104644207419541083d010801c40d0403040401000d00074451010052952548280c0340280070580071405400c0d00c8000003510384 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15607632 1250 15606382 15606401
    0x31203010914100b0313020109080a0302060a0e060403051606020412030e090106090503030d1503050303010b07060501060309121b0510020c0f0d0c02100909050c0702090a05040809010e13050a 84
    0x40c40030100e20703510f880c4000042164800881c0a00303540300c0081d03500000340c0c40c0800700d0500c01c403030600064584080c4100d003400da000c0c0e0082c203020300d0310000032070607140c182e2500700d5980c02000400c0b00003600441501c2c0c07180900100070185507070b50325020009129035088107217940111080b50081542c800300e000b4182c50152058031490340e031150142e0340e48145015066140d08103003e99103c50f14681c0c8890510a01c4024501049a8035240d2138210750080e08031400003a40054100107202d42f0307004181c01445c2924042100d800541c80355041900d01c802000c0411004110108018581700d101d0a2841d4116040d542d5101c0d5101640d4001d600044011640d40030b100120a202c2c807000c41c15626600580c2c640040d03002c01a8200000981e036204e0725018045580c00c0800d0b04a00e42c40b44030b00c0340a101c0419a6104502d0040120390000100303101c8440341890f0804c4000f521a400b6105400d02c20700f45411030b50030300f030002440c0c4030170340103401c821615010810241c90081d8102c0440b1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15608882 1250 15607632 15607661
    0x2040905090129060a090f0e040201021b060304030305040f1a060103060f0311061b12040e0a09020a0513020d020705010b090c0a08070509010302070203030a03051f05030a110312030109 81
    0x54400c0c980d8a1441c0324001003d519100101c80005541c42c10080020141000545007480030f0a07150402c581c2c50320010f800041442c00c0d00d0003004119601041800300c0220640b54540c4031582d45c0c2d0024500c1c0c80000d00040400d529040440c040240300c6088418041d440090041ca02c00f07604804940782e401180c0180c00a4140a400a034810b5024402d1040d0380e005070606480340c0e804c2060013416400104100513484000c8000c440c008001d00095607441414201e075551107213042e580700c003501400751402480a01d4203c102e0010380d180024003045850556200208185000004000b40650109841e06500000300c2c40100714040d0700c443e1400004841c01b586940b90080307580c0b61809244000030204120ba000320b100103010b840074085010701490058905103043d4040780c00c641104a00c8804651500c05004041c41404610000003a803203440400c450310b40000280d540f40c0c4114080c1440c60a1000b00c4203e807010b1182c03101003402403100340e0740d03542c0d134542400003007140c565007080 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15610132 1250 15608882 15608891
    0x60a06090b030304030b0c270102070905010803071202010e030a03050f0a09080304060506150a03090606060201020c030a230705160501260601020c041a030f010204050904030c0c0801020409050901 86
    0x11000ca8034840d2641519001e002541094151b07500c010388002c014000f034244000a01518010081c0107d80b010200100b8030782c000c281c0c0411780060710380b58198011010450510b00180312148000040d81ea801d0f4102d6021440b510313900a09900502008070900300ca40400200800741c1505500068011000750200c02819911810800c04a07592960000c00380b200403c00308000c01d4103500300a8100c10028002c20541080c1c1060640c0703070303012034007210205c4c1d08c03200c081041c40520312034a001003c07940002d518001107005015104d2080903406014003001b8210801c1d1005990080c85089245816141d0340d0003003400e00d103036101c6040503400800803940001261952040504480c0780703070b5a50039541840c541c1c0d0240541c0c400000d002c581184181004100144c3e19400b80b4006c1d660207800f61086004510145800c0c40110358091001e40e004110400041e00c0f600c0003070b40d01a400d49800e89515034245000610b400940d80900c1c210340c0082030104480c0790310b901c07107801614808000c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15611382 1250 15610132 15610139
    0x310050307090203040203070506030a0e010c0c0201120509031903110327030f03010902070f120e1008040b0a050c040f08070510030902030706030f02070813030308100b0a0309060e0105040302060a06 87
    0x7a1300c401c0b100290560800c1d20f08000760b040c03007030103150810500940410ba400c0d038800320908540d583c80049000510024452080d075070403c85a01c2c0030358a400703003404a0324041000503074a1007020207140d200e840e081c0711480024802d500206140003500c84c0c0b50740e01c1c280380d00c070017800954802031031962015040004020040000c00c840000310103104403400c40e071a201220009400c0700205440c00301000e40075900140a0485001c010301c0139495098000c02c01c01c007407001040080c0b00e11814081000309020119141c00c240d10351108000401082982c5e603000c403442c580c001c40c1d00205015104840200d0030701404207025040d240103480f04408900389207800c60554011580194058202c0213050017014400c1c1c0080c00018561500945003030341c5642c4600780c3c0d0b800000c22400c030001d818014030800d85d00020190308140000c0d100fa084905220600b41c0c903100d000c0180007890750308c03a0700341c04104003908a031000d508800002c00080c50103050280d00c1b0346084038020011403503c440071 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15612632 1250 15611382 15611399
    0x604090209040c0801240302010c110d0b04050111120c031f0303020609060f01030f02040504170403080309073c03080a030c0801080106060c0308150402161502160807020a0b0310050307 81
    0x36400e00f00c0040c1e070a96500d1f41d001500d0441c0386038815244d088a0400b06603003910ba100c010382c041c9114864591176840c280c10540d003100e1800409418010003080425048070386801c02c81e0700040000c6c903443e0740e52140b103100b100a04000f000d02c01115001c05000040c180c0104085100300e0440303060341e4250341c84500d1701032101d4003404003c0400d5071a1032440007505103980301c550f0051107800e03945500303080e8600c0ca40d1180c0140e402103e03e0302001040020300300e428000c0c2c10003071119013141040188001100c07981d500110810108044901d42c61410704107610a018004542190000f942e030300713060360f00401a000b400035950219091718000555580d0520034142201c956607104640550356542c11540c0708405041c0c409000c2d00c64100396031960f40c1d440106141c0d074595420a80d0217840d45440c2440024250007000b0b81441400380c0ca00b4481042c0380079030801e0780190919610b0340248005210b0040d20782003403410b030401008000c4d5000c602c40303111050741d40480031030b80c0b030b82d5542c0050b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15613882 1250 15612632 15612671
    0x60301050c0a03050702010e01020313030905030a02281e0603050906010608070e04020c030a080108060106030515060a02030d05010f080f010e03090d020604180203072604020105030604090209040c0801 88
    0x1c280904114080301903100358407442d00002d26100104000380030070659400d80c4c1058445000b03003801c1142c42020180c2240c05000245426400b0749031526135a00005e0024908189000b01503414034440c402d01d0080c0c1301c500c030241c4141c3c1c880c41c0d10b1480700080004070010070b01490740030a281c140440c40b842400148181203401503510580965105002200c446c00c400c03581a0b0841d800313201c0b021103988203001910100b42c07141c2d12150190703d082c0d40d2a00c1c042069009505051400c403d000c1c0d604504640200415026500c1541d60040280e080b45035100c1c002c001c009681c031f80300c0082201710792050781c60100d5071140101c421140c00c3d81c0005007200c42c900080310301c0381c1c0308025454050620008185075140001c00d52030402d80d40e150f04959500d0a103d4070b1508503030010130400d80c20381008078858500340c099203910035415882d81480b01d52001031300281c140701e0003000103206940da03600464101c0307602400311682ca04107454001c802020601414215508000c0766500c01c80070740c9070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15615132 1250 15613882 15613891
    0x60c03051605160203030d020c01050106050408070605090f0904060f0507030c0c0f0201050c060411010f1103090103110d1509050603010504021804051516090e0106020304061b0c060804060506030105 87
    0x242280c2400007120a840c07541c07003820440008601c80e0396550140e5030034409040300d03c44a54025030754101b041d00c4c140c2102c40580000041c0881404240204a000505c0500341c420300c0c100241d03071381d40c00400240c0e00401e070040180d11140c140100b1040201340e030040d03480d01d030380d0b5582400a0b444140065054425040e80c030000a803c4002d22800301e04843d40900c121030060501d1454580b64114890510100320380075074040045403402d2001307503400055002c034081e0500d00600780140480c010382e12480307041c189504040e2560344841000c09550222032816903802c40c03c2012081c04001d40320b950136540b18641c4041e01d0440001c40605040c0500c500c10b950050052402007403440110045204c0030304113890b0b5200e015030141000030450501c60240405c00245010300d80c03a54070051084d003581c2c115401c03500c1c8100040240701c1e000070685041d1007180c10481500c0b40781050b0f00c111a0010f2501405207619058002101134214110360f0080713000b48000d101c1039035032009242c00d8807419103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15616382 1250 15615132 15615151
    0x110301050d080f070f0302070e01080705010804110f030d09090609060f1a0d09030801180603050712080702151c0b030a1203020d0e070503070e13170706020412060c0305 74
    0x200d900000b0540d10041c030200c8198045207003481d9050b01d484e061141c490710201c01690040d40140520080311132014010400708004064090521300003e01c40b5501410041440000c400a80e1440d43e400e820401c01c40030190840c0c01111240c1e100805418152094050765031400d080400c0d80061800b520701903680a51186110038586288030101d4400079036840c40c0c50310203002e494115882401100d40300703402a603910703036594149211f40e0381001046079518143e601c0c180f01040020310129071102180d40d4550381c001d500351503040c01000b130b00c280070b0020360043c0034138124802c04003020041c0c000c1190f0034406010600c3c400c180e40e401c41e107120101c2c9074154000c8c1c60b00e60025141610000d0300480d036250150500c0ba40c0701c00882600d09624070788000b6001144140454242001600e00030301301522080d2290805c24402e020000301160060f0104e04c3c04520346191200200c1100c0006600c00f030b08550b91a80d40e0100c0d40c0000201d40211500b50800081040a61007030090300d002d9005176 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15617632 1250 15616382 15616399
    0xf02010524031501080a030314090a03110708030c070f06020304031505060d0b100305010b030705010903080703030603050d0801091805030307080402030c031005040606060311040303261501020111030105 89
    0xa1680e00032070340d00300c0a59035042c4a45045000480500d46003103009000c074170000c0c1940d0702e140c41c0c00341c281c81101e0048440307014070b601003100341100029415411a05070410f01603400c40b8001103420021303d90002040e0b480001a03084c1240400500002120030302da00d0410300e69192036080383caa10032840003810303054001b104826480002d1b4410382d04440010000d01029205544012a900044980750303038004000f0400c105001c0300f80503003644010202c0107002e40a0612001801040311800050719074000424038804040c02035100304041c43d0418100c800884481c240141221824040d00000a0801c000000c41c44600c8003116420356004000d5400c5a542c000c00b2a2a000020410303a403601c5040100c07181d503182402013103a101001c4002144600e42030034408180d4410354000d20405150140c0c40040403098029601520382c9441d2042074082240c1c0300a2a95010309425428017020009100712880041300000b4001c1c800c0c2c00a002108111584002e50301003445500e41007100d1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15618882 1250 15617632 15617671
    0xf0a03020108150d02040914070b030610050d1404050d020d18060e0d060203090109030e03030301030b04020d03050d0c0503010314010c0801050d0c0803030106090e010b0f12040311100c0f020105 85
    0x20f01e207660f4240342e025003000200b404540000b0192580c1c1e406c1981c2461036075540c034001e07602c00d0101201600d001c29685141d03080101c08200d01041040007075081060101d1000c070b01d0400354011032190a0310f10705802e402d040a041c465103903800070500a0140c802c0f6000725140c98024518a8403040040c4400b018452402d08140c81082c0400310b1541d01860740200c1c0c800081451000d1402880d651b4000110350150b45809040650000c007040d100c1e500034801000019810451b01d50310a0341070b54000e40104040c40d064840b8090a940713a5062414005590080c6078802c0c0518100e0b4050341a000f01c031944030f51b00b1800c035200100401e0000340508018482d5050032104911041e00c54250568203940d00d90002d42181c00a8001500040210004000020301d00003490f014200206100d40380c00d2081a42c000c15100c0c0388218a1040010400075043c94003e58203200010206010f071154586884040d200070106e00070558089030b801c2a0060301039205100725803141c00325440c0d803c1c41144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15620132 1250 15618882 15618901
    0x60f020c0909101401091107050a030c0311031204031b0b01140307030c08010c0e030607020c0f0a0e0702010b01031a0108191d0a030f050a050904110d18020f0a03020108 74
    0x6000341103001c540f1403000c801c08025200d110301002c07070508494400385941420381000594200e1460044d01c05001c0c0500d002260000c24900740203581411701c8040188113107825070f288000c0011080301800080b98504880e11500e50881c440c9100366122408194040c00e5aa040c40035036001418081e1080018045014298540101514000c0c11103c405659035101050121141c12039100e44e5110015030321841d07000614400b625000b00e0242c816498030000c000d680b50101e80c0424460913103c10008a203031500c100c014007401e0707034100d03000e0320349030180010303020704a09031103a40000d1030204084101d05899181004c058030584d10421241c6440000d031034012a5118a0040d0507618a910448400420420148840c9803c0507042c0c2107004d05015251041c0c146e03030340003800b20030410b4229940d8800100c507000d0501300d030005418088007207510351714043c10721410b401e94a800607407804c4901601d2815102c600c00c41d1042c0465081e6024881044d81c40e1000902040d90403003c6000180c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15621382 1250 15620132 15620149
    0x50103060819031404030507031205040b0f0d060914072706110102040504140f071403010b070303060302060406050d110903030f0703020a15050108060604090206040b07080d0504110307060f020c 85
    0xd020346130004020482c6074140480b0f034040e6004440c5036210385410010400102100389811101c0d0070050300381032030108d904465101d2034101c11066080001c1d80910281264404809071110002c1000003410301980715202c01e00c20758420010406407090a0342d598a00c0312510200914030f1150b131282450041d081d00e44005050040705155000d1201050944461281ca64225080c5450700c005042900040010780340213040803040058141038803400381c4003d42200c3c11601c4008039a0307611911418210300400140d040290701100002c0c0018280e81c0c0310303020307010034410307150300308500d00080040407900c1c864070b916581c05400c00d1140b031620a403140301a050550003070041c2c0c0ea1807031481d81d03415a064034150707528003207503500d01c018449018104400c9030300104c1910208081115034000408034003440c824808507410025001c020040800141c400b101c4501c0000d00003400d0074540010314007240c210380c0d4040d118a210010300d1070b00c5081c05025495003034024201b510054000d005d11f00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15622632 1250 15621382 15621433
    0x5130201120b0d080a0c02120703020a0b0c010905060114040c030b03060a05041b0303020d080a0b030601030b090c06040311090705030408070204020a0e03061501090611100507030912020d08010501030608 89
    0x1c1507520a001c229003000601a50806940f007420b1031071540304200c01030700260b088c0b01c40340d4041d0348144016125240242e081d0740e142e4500c030f0b480c1d42e82400b01da40546410580100140a6400001440f0340b01d05c1e181002c1103030403a002c1c08904803607002102160286814650b0650082e4045601100c180c4d000a80207801103c02420ac40ca031030146400410503a40114016807000c5007190031554003107200c41e0030030602c06050050300121800299079041c1130101401c00300183c13010a006d1002044040303842c1c40085d00d4182c4540d9a03080002c03410030708000c0709004400d040c000841c400c0c80303101140d00c5079521401e01c0f400c05810350280300080d00103601000500030084007035001c2d80c0e82040081d01c900803602202894244d80000100102c00582c005000c0c4090180070107803206010541c41896640c0d0301c0001640c0e51594000c4020745080c01024240e000301010207501c007903011502c949100c106071544600c50340d0760801142114018490b2007880d41110b039000511441524416501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15623882 1250 15622632 15622639
    0x60414181207080a14040305031207050c010c0206180601120f031202120603070b03060d0f020a03020a0803040905130809010309020f04050c04030b06030d0203031b120c0d05130201120b 81
    0x61a200c2020001d07540c1c844001a15a0071003ca50203400540c00748620301030891107107510b810145590356403960b9008040f400041c11030f84034002905075105400391100410104000c0c040154100c4001c3d490f040140d810381481d07490050050401c450000d40541203c103c0f07940a0140c401c00e40b2030400c01140c20104504000c0740305c03000101400540058a407050400300d140d03c1c0c500b0f1080030180351000e90b80c04214200802e10400550b07541301130002c0c000300d40003038180203581030f41d00c00641d032214683c200941c403a80501001c54200d000102a0098601c0040c0c100240e403074628003059810301a4030010003036a001c02c4070100d254402d0700010001440031f040061301503103050005098503c11503001c00f82d440045800c000303000b5505110b64208405401400c3e1423401c95900948900c00180108215900c040c0c6011400480b98100c4004160081d00c150807810440b90014180d44248203000505060a012401c0e07110750f601100d081c240c2c16180c207031440e030304204440060412001c010f0352 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15625132 1250 15623882 15623893
    0x2010e0102040e0601030f0603030e040b030c0603040b041b03020a050d030e031e01060603020f0403060b0a030501023025020307050f0c010327061107050a050f0606041418 75
    0x24180824005403001d40b0301a5419201850994001002c41c0c40280c131004000d4141603003040441e030464084031401c001610301044840004c0302183c5401401998540c00c10030000400c418032240c2c2109901a40c865100491111490861840a8042400081e40c0502c41724400c1000b8580107c03240452032090420002010b002d000103030409229402001803141044003d0842c00d50070300c41c0790098991400c0440c1440200381c4085648c0c0034600004041d40c0e074403942c82d00c15a8031142048011030388400299550280c04515072100d001000d90f084900400c150044144000c5c2d880280c1f04507002e00d900301c2c0f81984681441c03c0b040d10052440c2c10350004104180c0841c800707203e841034210f508002410140c9080380010115084d030000d01c00050400200c002540002c4030440402c203821400c0818000c20000c4444178502c10f1a000401501c1022289800c00074082031182811304c55600703940043d41c9038400cbc081551b0107882c0b000e06410701a000115000d642c040c080300d9408070710003146c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15626382 1250 15625132 15625151
    0x60705190c09090f050f010c0917030f0406030902100309080909041113050108070909020d0b0603011112190b060a0813060617060a0c1704030e0901060c1406060a05060a0201 76
    0x4007291810103007969500e444110903024498100300991507101b203203000308624100300030011304c110401c0c05245210644a43c070141c120200700103a4489032005000240d82c1c5907a03441c0540201090b0703004038007035005002c40c036045902074403482c241c0c150881225854403408100f046280c4078020300c111100c1100902c10045922100b0001c05454082c90780040c1c654181380701d251804400364800c024044c1809103540042c0c42d4030307005031512544a034071200f46484100c00a8054500b03108200028040400e03400d00707110400d484a40204e001203c0050003c0003035180c44152078030390010a80140c810045900d0961050a05540c0070151071010191900c9680e140010740f0702c41d9000c0c0440e0100c084c0484000c0c50144192600244d240008110070706a080300074000c8020840101c18850310100020300f8140901c0903281b5040d0010080c3e9495030310341c00082c00c5600440300540b06041c80a00b00c2e049202c0004a480c01110000c1400c241e03103242204104103907012145140440d500c03940e008 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15627632 1250 15626382 15626399
    0x5040c09031b0b0c010903080f090309060705071206020a0f031a1005040506070b06100215010b09030c040603150b04060302090604020703020a0501060602010506010e0402070309090506011106010905060f060705190c 94
    0x44c048101c046001158204241c00c00619040001e131259425600800601140c0100041102c038603a03000d5601e40e488044604084d4208502603000c94042601c10f0100c40411105600401d004041ca8454404d1510541002c40403240309612003440e0803603025211139249840141541c8810030340ca4600c0ca49501c2c0d001041b4030f60400c0300c0458401000f64107114241c5011050208240804e1005200040c0405c0504242c1101803191114071131002a55103040e88040c000200c000748080c10520061b43e80b8941903000380305006080c5099031070300310381ca495454a4090388003165002410040c061b01c1d102c003000300035800381030110154812200140b00240342030080c10010450764000080a1900b200007514480a011400c2c0c07245104000060000b82c015000100f60354209100040c59501c9000596026881c0704418000d40300315000040d0090103070b00221f103d004162180c079150300009041c03150b00e002c1e042c8020083d4109001c0d00b040c50070b550342c1914410b80148420ba106560b102c00b80b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15628882 1250 15627632 15627637
    0x4150902120907050306040b070f0c140d020d0906020a080309011409060f0105010305071211040902040803030901060803090105031306090f03030c02060907080d080603070305010516020705040c09031b0b 89
    0x12440380d005035a04000b0040d03018040c4400419003136015100d50319081d51460f815400041010040c0050340c400348000d240b2900b01c07261a2640400c42201d80c02e241c041c290b42e14195003a85000521601220b80003580c8240c4008040ba403090700108808095030360b0b6501a0b820042c48980c0643d0380e00a0f840e80c080c40074030800e0182003200c001d86071905018540c1200c03908160866411700d414481800407641e8456044c078031036500b0140c00103081303410130200c0c02e180c4101d41c803081d00107001140100b4034440100c0158080c02411008001d80340c0c0e1030100648071701420100c03e000c0740302800003484d096a0002c01000341807003030340005154070352a07651070194500b1080c00d5001076910321032541d402c0d40400030580c000880400600c0100d1a041031a41e803401c10002c0c5500300400b0002051490700c0811501002c6c590040003032040f8900388500074807800c04041180014880d480300041c942c1000e01c0b0382440c40a40ea40d924038010706540300d040024503040410300100d08d0980d00040e03d500050007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15630132 1250 15628882 15628897
    0x20d08041b0b04140105040f050d0609021203121305150a020f0d060501080708010302030309060a02010b0622090207030207151205040309050a0806010506040e1008070303022b0e04150902 82
    0x1c1d01d4880b424007106034030341d44041483c0c0317050020070002400755024160b50f500444600b220411035507080343c0b9000001c0c011a80000750400803880c1101400b60002c0050040c0c110402c1c9006001c0e50b400c0882c003402c45a11a0141540c0c002040708020014010035560340000c1000d40945454180f0040b0042d035481515050200c5daa40c103400d104541e48041740c56004122890800040e5041d0703000603031a4440c88540c18412080000c0c80e98289000b0340000244400c02401982c03a2041001445144040e1402e50020360045840c089035450302c0b40300b95050190554020f00e51f4a040004080181c030744c8034941010700070000514800c00e0000e01451b885a0300c69545c60b40c40510303000512602080c0e540008405030800303c014406902c8500c203880c00c4078080c40210710a034448100081e145d046903003103120360780210032010042c507400142c00da6100041d031900c0d0f80300204070129603461180f240c0600c0c0001d025220b43c944140740507080040c00801c00700c052102079039201490401c9910176036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15631382 1250 15630132 15630149
    0x3071503020a110607180503011b050d060e0108010609060b070507030618061a01020d0309050c060306011106070807140306090411040e01020a0309020a1202090408030a09020a06050c060115020d08041b 88
    0x11707101b54800300c007101900050200350001d100c5601c2e0006400c08024981e2090010040e0105083c05881903941080c0e0090000401c00030480d40c40e0720031140680424002c0e903ca26003000d01c00940440044103d0b14031a1f005006810400d0a6a031003d01502341d1808021841c0d40c045010008220a88142481841c0401040c51040c0d0a00006400c16039160124010b0601e4091217502186000c00c00d8030844004407038040c1d07669511801a0381440c04a60308c0100c0d8410502001040d5400000b1f09000d261161942044810410040181072200302c404540041c020404a80020700c51620098200300090001c02d80c5282e6450039030032030300141c050300002500c40301d40030194200307904444043e00b4031404061350340045402240180c0d41c054002040b00a0000004e07191000942c0329041c10781e40180514606551000028a0340d04212000c0d15035014001c00007070014801900f111141d003203074014103d22100b1080694021a00600554a00e0304a609034200c450320000818007418240c07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15632632 1250 15631382 15631397
    0xf0f1110030c03060f0503070315060305030a02060703060b03060f01030f110307091409090c09070903050106090606080a060311060a05070c06050a120507050d09050a0f0803060f03071503020a110607 87
    0x100402010784a151703120b0000d6084001c0180150b840200e52002502c3d04213070b40c0c0355141e08040429009100e16400a0081d0101040038500140e0200c0e05900a08141d81d003449200c3d103e181c0440766201c280c42c41540140c0386011219194040d4004c8441001000f500041881600e411002154804c4820380000f845014003441405070810401d0b20302e0748152444c120302d01d407490601c1c2d40d40560400c6035118181d10400114114800c414080c0a5a03001c0c000f440041c0d601c41d14000544414000c83c40444d000b607000034465002c621400302100d80000c40c0a0103030200c0c400740306040d801600c0320001c000040000c0070204100c41020350050a0039030b641d41e90388900c24001401c8840400040e00544d044c0001d2100c240c1d070180a550701c080d000300c400103080c049841c001d07141408510009110007841c2030b05406104942019502c10ba030165640c00429546200305030b1100d900d80200c81c003058680ca140e203140c074440d50141c2014150b500702241800f0b4446c110b03d10b802402c0710900005003c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15633882 1250 15632632 15632651
    0x70215030a0c02010e03040302040905030418050f16020a080904060e040c140607050a03200d080907060318060209040204030503030f24010c030f02010b060a0201021e03040f0f111003 80
    0x118881c00d00c0d070b03420b02c0c402000700c1d560070b0120940b00d2065110203071265460316000024441700b8411200105400c00704031008200e0032141e1405840220f480e010300041c41000a402d615120003941e604402c0e0340d0190051001c2d40c1daa00c0d0300d580107080110b4215945050214181c0845400f0038021b5008074078441d00c1a15040303084042c1c00c0c2019642d80150014490100010720000c0d1281040c0c0d4503040180c41d00d4070b40c034444580040020107603c4103100b2560115000c54110340341d940103603604001d403800745455030700070b070706540506c25581055000c10746100082181c41d4054503007442c0050015280a030760b5103a441c40c4d5081640d82c400c0140d50303c000d00400d1010103100701e58942010000f4002c0010031000a0316030b444081016061258500c80e041480d4030030f50081050386002041951601c1403104024000c6d08100340e508641c4580303840031460007090f074055a00c03c5a02101c03000926115031750740341c600d00d07a080b400c9a45441d80407292101e40c2c0d560b2141160020301c2c0e5400940c8084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15635132 1250 15633882 15633901
    0x905060703060806070c02010309061a031c02030a050c1501031514040201050702090702010902100527030705130b0a031109100303080a0902191511070b0405040509010207021503 78
    0x800340c08001494689042000036150114256074003040d10305045013200c00c6170006030f029042d0007100500c8145005242c0454030160201000e520005a0880d6102203c50402c08480550049d02c2d00c00b59100b4041c900155220b20000c0280049480507034002031100385803d500f005082e00101d4070480003030411403514a651041d641c1c100c00516880d002414240c002030300c244104200030f40900003100014400500035000f2420b0958050a41c841c5881003070802051a08003025045111030001130041c8042104040302402d5007006020300111860702040114010b14040403406980e101da1510b549507070b074020001d00035802202c05164072043c0200304008440028041e03c9002007054050010aa1140b00144d008600b1000050002100d000159521000e580d00d101030003205031f8003050920808581000c0844a80c03919a0864a070300c20b42034403050300380a01d09003208144010019840c044e0411358100d50441c00051510b2029004603000d202c2007a44901900d0000060003400e40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15636382 1250 15635132 15635143
    0x405070206010612060303050301030209180f0d0e04020310120f1a0a061203090e0a1103040f020103050702070605030a02030403050d09050106051c0b01030f111201060305070b07050d0305071b05010905 88
    0x401d041000c11b05641e0003400600060101074001c0d1a0744001441c94161410420f0044a082c0c0171128006544400e15540e0040401c444000a9840c0010809800c0a00a803401220101e0405203a182000c0000c0d000345d40f4010151101c0360007056800100c1d45a030443e0043d400d00c5a01611145032509042094806a82c09080d034101c507102c00f44040307640110301070b09544a0700e6055031680c075071070201d402800701c81d10303280890712002080c4410801c2481500242c24401e8030140010740c0c0f00c0a05a84800c004e2045001040d000c00c001071034841a83d0085d070744544a0700306a8144100c42c2600d004403148504100c4691790740b80014440352070724800d50303404100c2c1c00d20b01210180040d80d504c0840001840020010400402c00324204402105072200c0f1710300141a040c03846a001c00e03018082d118601c000d40d241c0c040c512000c40d40f0703038810382121059a007080040c0403401e06104210000c00e0000c0100041046400c00c0016542003440b070b05800e18000c60012542d0749203410140d0a01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15637632 1250 15636382 15636407
    0x1090308160f0305040501060510020304030204230403110304030b0c0c010e06070e060d0b0d1a06010302160803060301090b0a0204030c05030d020a030503130609080408010b013b04050702060106 85
    0x10350031410030861050340402da44800300403529000c101a20344d0301d030507030245c4203d800071640300b1740b90303855144880d90000207402200e000715000c0c0304c0c4100c0708060780c0b440c09e00d5541550040d10716000080c0800e003d0603040081c1c1c5124400c8034039080e600e840f8050448010342e8100c00307100d400a41000002002d00a01038495540d101070034a905201101603d0036042d0003c003405100042951702c850b4206d64485480c4003805414040381700210300d01507072541c1c2c40841d414844003940d07001c613200e03512134400c5d100110501c0310180d40c100110b0f10717410486e4000504095041d0b403076508104c00104103200039030041103a10000758a5070f0031441c00d00c9402d00d0540050b40640c0c0142d80001081d60f0000f40090030070b8140c144141c1c0c0c1d40703d59a02086000303184201600e805d04089071202000000001442121101c0008020880e144001100c040407503025040368030001c0d00d0720000801040d200d02500040700202c1e40980e1a888003c2010744100315030581c05a00b144004000254009841002e413 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15638882 1250 15637632 15637651
    0x20c0c010215070e01050403120302090a1406030613090f050313090b030d030207080f0a020a200d020909010902090408090405060904150c03061806060e010e0a0e06030102130801090308 81
    0xa0000e5140c035100c18020040c2483c040043e941e101c0f020a900400c22200515001402c00b02c0006032541e02030003a42c0310901d00783c09900041c0c400981400c200c1a0b00209400c0140840c1c55510b821003048004d440200f01544000d56441c00070300020800c07400f00094034071481c06103464043d00c022012205030780e03a014007455428181c06950a035004104007002403058100181c8603034503418070000c203001e04a400c0031000b0000590008864000424028051082e800c902610842200d801850340000382c00075000510610300d04c4c01813a0680502d07512080403000010852200d40024512a0041d10180c1c5d00c0c2c0c200181940103070500c0c0c0162a40004169034125803810140e5514903174448001c20301000a540c0d40072a40240d1081e0003120050240401c6039110390603002c0c0c060020b082603c01d090114040c0c580001295001b8104203c00c06002080380301d44601e2710300895001d5500800c6103031715550811004041c030101e40c1034040a0000078000040302103451034090004d40c005041c5010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15640132 1250 15638882 15638893
    0xc061509100803030a020c0c150910110c010f02120703030509010e0102070b2e0602010c020c0405060a170102130b040f060e0d020d1104050118050a0603020d030c03050904020d020c0c0102 82
    0xb5001002003103035007042001c400141e0312000c10300b00b81d040c4545a01010740c01050030090f405081184c2c0c000e0803030307140c3c01c0352801404030b4132a00960307602510307040b9141541c001718980380184d07000f8408401c10481d0b50040e0741ea010482d1811440707681c45008201c0200e582ca2003072040d18074092058005c50341900000b1840d00d007680d02c640850300001003828030707602d40800c444555010000307031500d036840b080501c0c24241502c030320001c0e010700801852200148550415103034249403030700401e405800702a00c0e260031141840e5481a4110341702c0e40c04c80507503408005040c0c00c2a02c980e08040241011811581c40b1420039050165640559110343c08014000ca00c00b51140c2c1c0e003600340902e0640c100ca55043d80f80203440c1c19106120b40e0f07116207501c1803411000040d500281e001c0e00340d0814000c1c030200071076902e0b5624403003101c0c01800b0294120403202c1c1e14800003400740d0301c13544641c0d01a0400d079081401038030001c2e0517a8010008904641c3c0c01181206680304204900141010240060070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 15641382 1250 15640132 15640139
    0x603040c030f05010f060308030603060f01031101050c01150f08060c1e030618070504082107030503090313030305040609060509030d120e010510030c0f0b03010e0403050c06150910 79
    0x44020355a02018003403420651450003085000d51000a5400b6007074400d20a507a030b0b0b0304060443d40c04c11240030b0b00a00078800014682400f20012074140c0c2c0d0300010741d001c01140c1500441d055084241228055076076004054031113444010a10001e0910704100d40403581802e04582c1020fa000e02607400b030100501c222200c84125500d15900048041401e50300d0b03955000004040c03030506260020800042000d20500c1c07a4080001e0050b42c007450121441c07511245d99a031280071a1400400903203805015440c0000e200d60001c64101103035500320381c10301e0121440c0b800300000b140d108030301280c0001820030a2541001c1c0e000000c2c200c0e400d280c1d05044030a000709440382040e03004042084404030407130000c2c0500e03134450440380c0e55440081200303281003440e082c026031450105480c607a042c050000743e4064540e0020003601c000c402c6003402c50b40b80100585214030007620880601c070043c0030319400100101b10061085040101c04102040010244500ee80e0040c0c01d02807695000102070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 15642632 1250 15641382 15641393
    0xe06070507030c17030a06140a050306061c0206030903070308010b0f070b091204030c0e01080303090d0c080f034305030606040b1201030302010b040c0e0f031002040801020d0605060304 81
    0x1e5400355094103080b06031011904d01882c3d01a5000500b15641c0008414030844291651000301030358003408010f01080201405c2118800c83c0307210310b55147d8050000a403960801d032980010820480111aa2484650740007500541044448407d6503002049140906601400541c010071801061034905620100c40720701c20310916801820b06400c01c404a43d0001e802c0011110300031590300210b803143d07200d2920128001040c403801c410603e480c4000b080b00c800200480b4000e200c010010806848003100c00d440d15031443e54140d400b0711080c00304098460b801c000441c881c40d140542d100c1d452916500d0341074003503000d000c459920700403c60600f15940c1222203120000030b1500301180c8942e100320000750030384542e030003a40c48000d0204d403483c5401e450180c0941030b0382c403d400038080301e810b6006000445100e10602c400140c0741d201038850a040c807a0900965141c060166540b03920714131414000da9209505c15129a9070008055200c0e0700c0d244a048050a4101c07955855810a038580 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 15643882 1250 15642632 15642637
    0x309030c080309070504020f12010b090a2105030703120516080106050c010b0d030f12020306090408070602130e01050312030f160c0506090307060b03011b0806120a08030a0e060705 79
    0x41c21684000040f40b0441c0b0208000d00007404001d0041d0340c0c48201c951001d000785c1040303080300c01d02ca8240001141e05203a83d42a2020b48601403c001c080e03520b40350042e0114580300300190451000c548031900443c00503c0103000740e50280c2c85050050b41c52000340700c01c48100401c02c2540041a04081034016030180050b41142e0702441c01c0c1e502c4020304410305004142100c0e2041d8040141d280e0700c010180c20003660074418405844081c48040c800e40520f09a00c000c403491988480c20400150015440c1009040d585008000060a0490f24810180240f0040d04908075001d04000100314615003000341d02c00c202000d41800c1c1c00c60904408800c0c0100010307003009500300541041c0041d00340300e010000e0300113070010215156410700a68003030700d0354000103041c1c13101401d0889510482c14140035601c003e1005940b01142203038030000864804c08094802e9a210104460140c8260b100f0064a807489005488150381da08000044c5011501200c0001d1010f0304820200902c0541000a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 15645132 1250 15643882 15643907
    0x31e070516060218030a0f23070302010f21092a05040902190303080a0b0a06021009021c03170708040302070e040204060902030705030402010f03110403150608070e16030903 76
    0x80c00360b01e5000541c180100920b5244180e5050b124000c00c54050011f0381c0c00406403a4066907030612540d0003003400c00480381a018031f400c42580882750810065220f44640550010303a0f00d40192801c55406241030082400d855800e55241c039131a82c042803084c9042c0b50a449026216540b625544c0d8030310840310105188a010301c5141d503084031800b503440301240c0b0301c021100e105030303007126239100d14000c0c0c035611080d1140c407000c40c9070507910381e258140300e2a200241e1b00306400402010409139030355405445164412a0071007404030061001c0c40c05114150246442a00c80c1490150520251407074040024090401c102000702403101094003c034454040e1040b82c00851220355480c0082000b500b210783c050b40f4110b00c00410000116804400345000700d02c02d98a00c10f800e08645030480c00d0701c0100840009002c02003004100040c2d10148560b01c440000e0800b0030080d079210030b51410b200740c80e40b04448803200c0204010f2003065000d030544200e0454141005924056100141040c440c0350707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 15646382 1250 15645132 15645143
    0x2160b0402030307020603160306080c010804060c0e03030f0a03110f0301030f0501090f0f0210021203060607020102070b03070201020405121c080702031909060908150c0703050708031e070516 84
    0x3190554600340100d6a010343c01401031546c1c0d05148001c8840c400c0040301800000385000000f003050303c030114070502d0104050b500c50210b91a151600c2c030080020b42454020710103c0203010000f61000c0c009443d582441401d21034403048644d1000e803d442c990309145030940e50421482524425030401c1c1d9045d079800c00480341c2000740505c0d1460043c07403140c0011f0280050b410010003008000d03d500e07103819100b80c2d64072118892080c1c0507651241416501041c2c500280001150350811001030149180148112a805a911000700900358010394000c00182d40002d81032182e420b003112405559a00000103240012602041c1458203088501140c10000480302041c001482041a564800014900c04407243c01d03c55000d41502c11905c40c06d80484c5103a540085c200c40017080280580e21044441515955403000789052a4814001102400418440c4402186a40019600c944006a244000c02501045038228040010950170070400200109480781c00304004034070140c2d83c0302 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 15647488 1106 15646382 15646403
    0x40e1005030c030d0e030c060315030601120308010501030c051210090507020d0e060304020301110301080a0501060506070228080109150605010206040b130c05040c020309090a0216 79
    0x180c0b9280d8550480a9541c004a004103040348403c48001c090310940401c100c0010308940055558000d400c41c44025801a807d08001c954050100d4040d0940200980c1ea401445074105001340c0341056140c00004440c18002c0301640c1c1d00c0c0700140d03c3c0c0441490302d50007003603180409108201e443e41c02c1c200030402050010800201038070190317517032440a9a5520500c04240d1000d801284c0643d030300c5503590320841c10b00d801b55000c1c0403684058240701003a810404d00f9254603401503403080d1400c109140040e0748850b00c41c003010480c0c6070340407240d40d00320340d007010034140d41d41c400c10a950808041c0420444c0400786800c1000c04a40208465031f220401240e5076517049174000e03c4100300c1e50106000c0c160031074140030000d1003401400b007207648450103d8145e40c685921100981c0c0085150a90741c0b8202ca01c403a80001b66450840c2800c04100107d44421227200015007005001e = true := by decide +kernel

theorem cover : BRFrame.Cov 15467632 15647488 := by
  have h0 := BRFrame.cov_init 15467632
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15467632 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 15467632 ≤ n) (h2 : n < 15647488) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
