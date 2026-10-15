-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:47:39.352816+00:00
-- url     : https://prove2.me/submissions/cb3e87e1-8b6a-4163-a03a-b2b702d759d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751079136 ≤ n < 751258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751080386 1250 751079136 751079171
    0x3050315180f180105010308070f02040b091518060303070303021c02071505090d0206070806010c05100c030524010804030c020915010e040b0604170f07030b07080117061306 76
    0x2c020310810301c8a28108500c8440e00b26106200c05841c9030705040041c0000382c2c45030290344403913500c01002e01e1912600d01c0000c0c040c102c1848180d170050100d0041220052140d41c20400805041e034014078104c14000c2417400c3c01d641110013941545c01084041c001078820750060108884468050b0044103201480c0c000384d80c014202602d405a440b00000808003c500c5030640000d00d800c000c000d04001200c020b92940c3c0d000340400b00b40641178000400c164016103800c10900d0380714048e1154440e65158540081c002c2c8804900007914ac9000604481000d080340081c4145850700340c03240c1500040115030100000344100c08110500d42a80c0040e1140d40c0244e020300010561042c601c0e001400040500d2001e0741e645115904000c030740c0f0050f884003012038095900c00d0401e05203081d00807030300700d1401015440d40d891a22402d0070000a1103040014240607050701e0355025003591780c64000c0402d50f1760000d1145659007080300441c100e40322401107001050f01c940c034080b45050840280c2e01e0f2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751081636 1250 751080386 751080391
    0x90b0309060115051903090215043b1306060e0405010c0215010605180a15230301050105040902220f0501030609091a0c0f07060b011205040305031518 66
    0x185503101074018009104000c0b082881d000703080c0791460a010603458501070b44544c0050701d10a00d03648851500075500d514598035036002c02c04405947d16a030304c0c50a1082c1003141564190391501608030041000488984403481885401c1078111a4980b440744080d000c0703103401d040307484c0d40da00c04c000a422989540c0e0f2a218a014034000121440e00940180c140824811820240c42040c0010701000d0380100540350501d0100c0d01d5100d01c0104031011666100d43c0d13802107a01c1224a06026071001d900403200030b800341600021400120b6425540d400720f000c00c1c05080c1c0403039010710051000126990180254000c1c0043c401c00c854130648807001e4030f25441e00219044641c10708180015601030003100c00422860b0005c00202c0401d40354440d8030082038058480002040c408194182050016100d80c0c49001c4045681c50240d440d040004080c52505140403031090244c800309010b440c81454400e5405449045c0b0b9030b620002c03848440c202c0790708256445021402d840e10600d18102e181407 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751082886 1250 751081636 751081651
    0xc10050c120403142e0e0a060501080708070b1921051e0103050a0b1f080616030c0c03081003140303100f06020307020411070827031615090b03 63
    0x20703500c6042d400c1802030070180e44000303003041e40070603d03c03030203900001ca0040300182c017009488603100d280801c0700301038035081c10076440a10591004205200e6140c1c80141200c00c00422600ca0654600381c098982000b4400d03440a13a1050107400c0d5000b8200424140d141990b02e0f1005910440304410803200300451840b506650350f0348104032075036100b03d41184082c0070f002041c0c0070a61650761419910402104000c1c0308419440100d03003001d0200480741c00d21104400fa15640302d80311440140d4804049504d040b08941c00500040410702a01c20303840c08d07285550700c1d50030a11144e2010f6886840203005500900070f00320700040450501e400710700340d023416034014503a01d003031400343c1c4820548960048480c0d140c0b200c40c10480141c001003200c402c664140c1e00420400e10101101e4158012108054803440e00003407000ea1010300b28007140511296038004405d00d40301c000a00d5550f154038409010341c850000d000b03011024041841c140a01c00b1440d00c050b4290301c80300d08040e25002a00c80d003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751084136 1250 751082886 751082923
    0xd05060402120109051011040f080d0f08071b140a0f0501060501090e16020313030f03020610050a17120a0c0c0503030304080a0806030106031e0b060301020301080c10050c 75
    0x108502c0d12030b100e2000a0108002480300103000e498251b00e90521101d0340c0000782d5500e00ba8000e007000d4500b610000d11000c01541821643d4400c40c58507122b100b4900c4002901031500b02c4209c2d40100c1001e801400a40d6504180d1010b00c10b03042d60400d017004090f030315a42086016062140100001c0c0d442034852861801c1c604410310340340b400d4a040d034000302d0500c9001e880c00d0142c05e105009842d40000502c4803100d01c003044da1001d07402c52281d41400b8000222010f40801800035189800b00b5062090b800ca94182d0b40e003a056101c0d600441c000e1a0744403003441c2e001c11400309104481d141001c400c0094031070003103103091002d1441c4e101c0d41c1a0408070301048141c00a0140f444482c0b80200410303400303145985099916044240303e00060001071140300c0c0041941d9071000d620440296500413104082100e1080340801d0703801e0070640031189800040d002076a0342c02c040c02903074102c400c0000100060000c0c1e0b4104010b090f08840745104104061004041d201c40030004c4021951142612 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751085386 1250 751084136 751084141
    0x3050d0269370503030408040305060a0c090b0901050423011706031c0e041a040c230306010c080307081504090b07211e0b0904050c040213050d0506 65
    0x36110700424050040704a0703006048074418040c4254000b561035124000340842422150214480c00b6010315000350091002008110801c45480b00400c00d41740181c044038059a20100306005450110480d103000038004041000b5a401d044068000003105040444c03e150b240c40c01c0301c0e10240c3d9280a103009011181c0c00c3c082a5820004100c4001003660300a809490000003203aa05c01e4002da00d0b65160000703515030708030107100c8e01c1040d810040081042c0080001c9002c3c403016100c0310f6a110b81705500d8000d555038010700074070011071118400116a0710b60343c0003494041044c0c00081c4882d05000c01d482c20200020400c5005521980c89a11400c0c0345040c81c1d25104a1100380407022406a86441c1e000d00100c1e4410414607407000c19442c00c2c50040a9101510404056420700d01d42020300f01400342404c40c00b1035440d42030b500b11100c000c11102c00c4500401c02e010900f914042c120342c0100c021f503002c50078590010149091582c6a4180c0a9030380d0021030000941a8410340c0c140d0050001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751086636 1250 751085386 751085563
    0x30303020a27140312120604140907091512110607080712080c0f07171b0c10140d0e0a1e02011206140409020a03021903050d02 56
    0x280c00902038150014131017013650b1a0052094807a856180161200c1e80d4000380d11696940c2110310729900118007000306040110b070a55442065000703980c6010700349685941d6005400c9182000c50307208070024106040c40751103c3c00e00050012489030001d1381004808080f541d204020030b5900c3c40781000e5440f001c8a4030000b04a5a800340810310b006c1c20403c8042c1e829000c034400e4070b142c141c1040d032481c140740001c036543c19a03206000d082c1800d40c00110088206080114007440840420340e40c00452205460048a00c450f00d4280120b8400041c0030740440ca40d42da034441c4202440b848111201c01e031250301c502901000030940b51003140b054006410865a11004a04400c01882070a21925041141c2880b03200c0344803140303a0140c0d80e2400e10f1400c1d95154501d2000550700507008403200050002c003000484c109020a44a40c891609103c41c8180300045464100c050b5007121b1031851565038581d240000340c0043c121a0201e4412280940c14031010f0700c8620303640104c452010301c803100f031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751087886 1250 751086636 751086659
    0x3010b03092b030b010c21110115170c130e0c1815010509040e0304170304030b07081305010f2f030406180c06030c2007030303020a27 59
    0x10400159810103940106000c2a80c4480c4a500c0c180b6081c0425404403080040711441d00500c009000440c44d00c1c075001981c01050103d40d510051640d4a115100381440041d0980b00e4060a00c00c144400300401c0040103001d0700440d190034411002d503052840032a000415000d410741155945a50361806544141c000f00400c0070300c9401510814072540c40803480b100c03200801404c004940700003015121450b8441e000701d4040308002002008401c1000d8959a56078019004030300d4050036842c540100c600d4000161340c01c0343d5020455402540e03c1c440c0450307440e40003620b15070f2144240114007000a000b801100e541c21705003200050100d00314441000041e205a98159180d0156181c00510a40b0076003243d502c180c0140011881d811004003004042c403c1030b101408201c1104400715400d40d00d900031550080c03656603101c8180342407581074824a0a0021225002e40c40603c0400010f8066000362408081e14102000000b0f000705403280800b02c00e1403c0ca48800c0800424000c038805407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751089136 1250 751087886 751087903
    0x41e030206010f1401080a0507050f070803010e0601090f0306022b2a020c040914070e01050103061401020a0b071101180209150a0b18040606030218060c030a05180603010b0309 77
    0x105040303144074031300c0c1c80043d24503200070f007559540703e456000142803136008900b15400c10180a124a0341d5401c0f80c01d0400c1e4507002802440300c00c0d40000007045203907220380c0444054400a038004c030000340c903680d1004029032002a69003115504c40101600210825200c00c0c000e0441e190f010590380a90210203006400031640d0700c2904102600c08056582d0010300301448c0c1d5010358000440780c0b200d04054901c80c0074245140030511070303080045031300008054000e040380c5013a2410300000342c5030100e12150743c0021400d035005a0100c0c03030903004034080540e487c3d0000c0140c1002d505c5d00a40300c4000707095072040c1d02c550b004507080780d040e03400b1800e10190f20b03540000309245843c2d4440100f000506c20304200c1c8103820307103820041140c900401e69491418600c0c04001d10800c8007d035110b5024010b03400816510507028440124003600d030030005c089400002070704024620b070440c0b0364001e482d940c200b400c40c102d110072040e08640e05a00e502d0b00640c080c048142e191b43d100d00c1d144a0340c51030040ca2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751090386 1250 751089136 751089149
    0x506070206090d1b02090117070801021e090a0504020412021504080a1203021201120204180c180207080408010e160b0702040c02100c0f1103031b03041e030206010f 72
    0x86410045081c2c0081000700c1c1c004810310b01000729103001c0880d10f03642c203600c1d14041d6012100200001d240c040707803c416000307400c000f000e03500c0040c2d580700550b00300d00540100d186100141c40c1d200d03440e416100e004040005001b403541000c1a06c0b007001c20201e8225400c038520344800040750f1800d51501d001e50446079441902c505141500300440d194880b404880300a103c100400030342e03500326000340c056914010103000085915a51480d070300c908880244401d034040c620345100b0858440e40682100308490304101c00900c0a4070b01600c01e00140e130040d002da004640e003072150380000742c0c510700107000821401c4004a41807501100c900d0034015262403101c414510401c04100c039100303900030745040301c0d01121b00042080c2428026400c08417035160701c140240c900758461f264150445039102c0e0f1020300b035581c41e81c4075056601d090741d03910050321015892102890013400121500c00156407103840340c209412280110740380c070085003441401c2100940c10400040c00f0079a8154500b1004010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751091636 1250 751090386 751090393
    0x50c070f05010f24050d140118030f03140c031305060405010c14130308090609031e01050702010c0207050d030c080310030b06010e060a031a03030406021b19090f09080c060405060702 80
    0x981303e00d5900c04194880d1034000c0340c24035101d80500c50f8071a1600700e810000c0c8003d20107898001c2c2d21500328090f42c80104c02007004806070346442440307441019070f05801c3d07000c16009030700e48151110464000402c0301801140d06035806000903000e00c00c0e0f9002d54810070012410404000000d4034010b840001d1440101c4140b000d00c403d0502c80c01c07000100d07500302c1406540d0300301c0c0340c010075010300c03c2d040c5a50b054880c4260140071000f0a03002403c08201d048001c007d42c0c2c6810108909a40c217148010f401030380071900510441c0762048484400074881e0030041002100c07a6545441c0740c0040380c02c40c1100c00307248410000c1c800c14403c1f1305d038441401d180c0120b01c5007041000a045002d40b1103140109a504c0b00d07945030120600814031800d041c014116903d07141d075031800039500d00c1980441e900e240104d40e02101641011418950384032180d11031011000d00704081d80004080780a248040e0075200d031040400300e420040107029010100000c0c010500c3c06080881c580000602403000b1540b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751092886 1250 751091636 751091681
    0x60605120c0a08010e1003061118030f0714030307120903031d0d110a09020c0f1b030d050a05090d062a1d01200f210d050c070f05010f 59
    0xe40c04500f481c1074580116039540d154441d000720600101c0c1c40d8200425075850480220501c41108000d0491400c0080300d161155028400345500c40410305d12074020b5078041c540c248580d4131a400000210480501120b06100e0b15880383d04640368420540401301c0c00689042c41403651110295a0185c07803620703000881280c010108040d41603008000e0140390414145120030b9132100c44100040c200c5880c10b540703031556543d40c1ca071184140707000325641e80314425065000f0b034105404203042001c005c010b03114845c0c40c000140c65682c84020441c0030020308000815855541d0081070020714007c0c500043c010041c11499041c2031030000080c141070940352900b4800d0703680034030f02441000d00e110410300c61002040050b10340703109a120250035582400e40036580c803036000030b207030100c25141307001c03950408410741c40d04201c500e0303c1e50030328900d02c020800002000541d4002035002440000007034a455595280c08140c9480079400f1680703a519243c94403c841b03143d0141081d024582c00c0d0154906 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751094136 1250 751092886 751092907
    0xb0904111023030a1407030510080f1023010609170c0d140f0102041e120b040209071713050708010c0903060504030e0d0b06040f020703020a0f021201060605120c 71
    0x1004540d2010754a040b00100103048141190800d41c0480740d10226803001e410800400b9003e800b013222620150424060b001640746000100010311240000103801c0c0c45010b0b11501c0043c0c202c8000420320b80011050a40c0c05400701c03d00d541c001c0910303540e0390501c20708250405000301d00c3e011184031a80c1c0710b003040c81400d0b5200b040300315001ba070040c50110b503004121109802d2140d00c80e58143d0652000c5000943c6d140c03080c00380d00a4904041010402503103407210102c0140113110041c050488000001c0c0050400724410b94010f0113506100b00d400c41500d1140040140c02c039030714000003070681054020030400f006141c2c003a00c072603030091020840c10301004140481c240b1014103055140d030085400e141c000c024070300d010361015049500320103060034410516070b800d503242405a442c03c0c6c01c0080019507072003980ea002e075055000c0e00d11110329494400c42c14441c1c81d4280d034809404562154045c409104000040841f511415200c8104448401c583d007001089811034030020048422070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751095386 1250 751094136 751094177
    0x30c010f0203071b0204110c010e0c190e0a020d02030103030e030d03180609080f030112031409010806120111190912050312070201020d020d05060913050c010f030b09041110 76
    0x4c41c5501001c000d030842c5800003034043c108440102102600025410200020640000c55111440340440702041c1d4424140b02c0c80c2d500d21080718001c114080c0d01400074120200c5215003059072408090306000321030382140202c0e402a071045003c07685140c0d080041d81024449046002d001d42001c000400490600c1c0518062040d40207142c00e680d0440142004008410b0700c1d030320803818230ba0350307229030710340c080005207100c400000c1d1b0218841074260b6054612400840388608410380d03801d0381d00d8648405100320400c010340e8101055480714001c0c8543e10b0308a0190844641035007810f076500b5040c240140c9001801e40200e0242c48a00e6001c001103407002003211071408240621010655964000f20700a0185c1c0138070302050b43c0009000c42d6200e516800032802040112002009038440c0c0701d00e403000e40709031031006100d500403001c4a20290301030070984052081074100400c500c5104400280380c4003003105c04941c4540d901001d0411070070710001c002e28a0b00302c1d0810325004000329410f000d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751096636 1250 751095386 751095407
    0x3060103050d110a060c080718050a122a090f090f0813080303010f0e0112021503100302211203040f0605040f050f071502030a0921020d05030c010f020307 68
    0xd100d02e00075078030760403e4104840c201c016000007040001c210070302c6000f018844107a0745c80b00081e0202d030390034102800d244001804c80e180189038410b998a002454180780c10100c0065983c0c10600c0046100101c4642018040042400c40d191802c0d00b80008441204c20160311030500d28908094800000c450311004991284c201c0f0100b03480351041c5400160075490368100c0c40190101000003e41e400c6000344000c19a03828a1907404281c0e25842c461100d00c50b8144080d5115000411034106000000c1c000d6410031005100c500807207403280c01090a12500a0a800c1a1107000420f40c401040c18040d0840b8582c0b0444401d213541480d8071211b183d8840a0409400c5650b00d00c0418100807100c0704089540f580f107000d6503c10307140d2094042d118031440c4901030744c090400009001c01e0344080100c440c40c1c0d01545a680610b820300640c4ea02c0403812a10403142c0081074107065026907109501812890b1260008641d20040d05120380d09580d550908007200d40d005009001800c0c0c1c01c80680351 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751097886 1250 751096636 751096663
    0xd020604060e1207080c0a050d1106070e01080403112d010e0a080403060b06071505060301140907090b130e0307030e0118030209070311041715070e060a03090206040914060306010305 80
    0x1615011600034841c1041e07c5080c1c007d25622941d0240307a000381c0c1010780d500200d080c542c103484807603a42c12401d0b034032203074003104850000e000c010000d00081e00800c603600002007d442141c600f484010004c040314001d500c0040c005091007102e05484038000d0003407092990749400a0300364801c0a64800c1d12034011400300901c20b50301c90961a81540301c030000d448985400450103a15030840c13000305401004199440ca00a500b01743c0d50390815085070300d100f40103030301c82c0c401403802500d0400d0110003446c001103900d40c003160240103004c04181d03070f0040ea0b80310742030200074550350030701440c01400c0001511103450522241f89100300c0d282c0407050b01201201e0301618120516542c240085000b0a8080440d400140e404a404242c4496600b07043c000316501d042112007145180d43da6950780401120950000f07058891064001d04040c0054160340701c80381804200c00304690300042e0290001e400c1500c001d90703a100c610303c014001c1da8405400c400198090700c0154150b0300d54a0302c9a21120824 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751099136 1250 751097886 751097903
    0x7150801032901230108070e040b0d02032b0305040c05040207031724040209030c150d1112011d061909060f03060c0809061b04080d020604060e1207 65
    0x1808081900b01c0700240e1040949240c26030368540540d1000c054490107849014150414030400c02d500500046001e100203450b20b100600544040201620860320040d411007030014030300d401610204070b40070301f80040000d0042c0102450805a080c50041e40071103040500b07003414400440d0188058000345d800030345000da43c800c3c15007400d60390301c01c00f611601394000840c0d0801031041819407003144a10f800c400f0150450040381d040005034010401d01c3e9038150001c0b851038441340382458220300024a403000241c00c01c40401403100869090300c4140102e010002414860300c0407e4510343d0150001710f000840c002d0b41140d9001084000820480c001d03038042440752420107442041e07000030000c1d882c0600402d900e41c10f050701c2d4100d4610003150b03030909100d905000321340282c2d0141e1140d402c0300001c04891741c6040000030104441440410f141c0b2080001088080080c080310005611580003010682410b182c138070122201010001950781100071110300c07040ca800200c1d800c051b00700005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751100386 1250 751099136 751099163
    0x30b07140a09080118030914012003040e0633130603270b0a020a031805011a10020c010503220b1005060906090603040312110405030715080103 63
    0x548400488181000c58510003180700800168081189015942541d00a104a036849002800b64101d5000e006000c01c00ca00018000c251103100050502341e81403404204e101c0102c1252080182c219645c40d0300c641000078140300481c50948010341024065403d443d0301c00c000400e01404030706401c1c001340d9502c01900d9011207260100c0035a00400c6840b803c1c141c607142d507000c0c050010800c10a0408508010080ea085944007041c3c2c0200826001241080c90740c2e15000150000e500c0301210009040c1c0c0d0b0300800c414020305c000102d03031041c8114000a06001c030120f210200d95035026005101d540700000a130b0146070b0220703407665843d0f400c1c00c000e5141e407070f42c03c01d01268100c8011100100d0104105a500740540128442c0c01100000341010f5459122018018284943c8007a01c2e00920108180c3e80b0b0b0b0305000008642c0a8024030f450207001201440c07640985003e0b04000c41104801304003480245001e0240000400d141c1707005000c218600034015100090510000d01070403e180300 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 751101636 1250 751100386 751100401
    0x405010e04050a0603050f0102040f05030f030a110106030b01030c03061409030d0c09030206070506012102060a0e060c06040b010602010e0703050705061b16090c0503040203070e060d08040b0702040e0604030504030b 94
    0x104c0d4000e1540202502d000d00042250107000750091b10411103000c0c024900045e681c01d010421300407050031400614a800c4c240001641c800ba48020180c2c850740d65084000085400080e0040c0a0340c070940300450761a1450070a44c050307448800503003180c0043c0d00184144034000208442ca80340d0004e1010030445101070040d100301c1030b20352000c0e4008400043d03020402c000170030701506030381c815400010013421030800c14919a41400e0005e4010303e0030016075034854050950880c04403c014140740c5051968140241044020341e000c03a01c440759070300140051074080c080c65031011880da0003800101c0c2f8549590760b82d12980c0c0303c0c560182100043c0d1b03c2c00b92140d400c1510903101c01d40100c2d500c2007481c811303e070981c0d2900d1080340c42191038040050203051085e41101c0c041c82d002001801c00c1403c0c805090720103a806001c0030381c081644204200081c1411014100038540c00d540d0f56110030840c014407007940c1c01c4402c540883c1d045442000000383c0c014090f642900d4100c022200d05958018 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 751102886 1250 751101636 751101641
    0xa2a0e03060903040f080303160813020d110a0914010b030703020702030712050c1509040f230a050c030106020604080a0c0f0b061807051804060f17010e030405010e04050a 75
    0x96014025041009900080000200222000c101c0005030003a52140656200e001c10740307500805880070007180302000e201d8844540c0200c002c0c1500e01c0401003c0e40002c05443d0585c4007161010b03050f114400c500c0c0392109510307008100d000414440d80003d01c801946c0c44105000d444403030304000c00401e02e060303c02e034151644282d018044441281c1c640313041c000f08044003041155280301700095540d090620200110120f000450b519090801000400c4040d001c0e0348141c0d82c405c4d65480648406518031540e981c80130700559544540e50a103050098140c541c000c2003062160010001005101e500182c1c03c2d5206811100c1d150310794016060498000002c13100140000441c940d6200a1100422034603010300310440d0809140c020104101a07448411604c05000c15402c1c024401504100e400150f46400d0003000080c420742c441c0c90048540340150084010000b1800d8a500095070910403140c90070700d03403402117041600d0680028008000104040e0041d81c60ba030201d00d5040b0b083c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 751104136 1250 751102886 751102907
    0x20031002070809060319110a0801030b181006091d0d05031503010614010e0a0503071806170303070f05090d03120f050a0209030c010804050706030e1204060201020409050a2a 76
    0x820302656414007601d800402c40800b40c400c500c071840c281044500c070704860120723a41234101b41c9442c44940c3ca0344e00ca0f0070300e40c0c078000e03d00032504aa161354034254550521000a06d40b0003800001280d1307003000b00b0079003103c54074201e05080c2c01000c882c8002e00b100015420581000034a0620364070340d540c01d40c2051340340301c3c041083e82660800b400843c8000b01d1110401c00460281d0b034101480b03c9a00410141c01c001d446400c1d01a0004c400910070407101c100c00c030020b030241c1c0070082080761782c0380030078020004c2040303a080580d04048240b26606500200c2c40b1210440c0d85411400c151452001844c81100418028140064400b10540072030f0983c0040301080354601c0c3c104000c2c40c2c20701d80440603510451465201c0d000d40384505481d98013903d50140201d800200920413103050a40a8000300709100042c140e07032084180034001c10314070714001d1020305000d80c00540c540e454660048160384025021080584c04c041081c00c0492454881d01100080741041582c50a18444183c9800401 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 751105386 1250 751104136 751104139
    0x51203040902161203020a033b0a1415010509010803040e0403031103190b190306090503161406010b030601020c1302130e0f1513150e070c20031002070809 68
    0x1360414802aa010350240c04900e1280d20103000b411000d5441640d4860000015454a105e8a10f92a1000090040352480203a4201103a078014056202c100c20041820100b203410b0344541c4010303504e9292816000e0043c0300a44552540c1d50500d41401d0701c9001d107025050301c0155040004050510036000000031b212100c00ca80d54900308440c40da201e109241a0841c2c025041c543c900e0307602c0c108400003510a2600c0b001c0b40301c84070305558603600600030802e0181e4140c030041c014036048112440411001c0340c41288131031031204044101d45c2c06e040c0144d03c01c050320142401085800d903000304850fa078880c4100d0b4450343c4102d0101c4420028042c414400d242e02107449000b00d046500820042e002e40040a0b5460050744d8014402c501c0d407072002c8400382c000050903050304400400340c00c0506050415223a605142c2e48135104075500344011940000010707980190703d41400401c0c140740c10040301d510021880c0140c0400071968503407292060f01c007031950002d800c900b40000b51059030501c0a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 751106636 1250 751105386 751105403
    0x30115090506070318050105091503100801022107020601051507030201090b010816050a0303140d09060f050a1406010e130b12070303020f0705010804021201090609061505120304090216 81
    0x290900a0065076440d07480a005c40c80301402180e29130095090f2030a12600601481c205070306500b4020702604003501030102c0c0b0010200201c1ca031071003030002d000450042c00418000c1082410700000d032440103081e81056412400050060781c0307a4448142c1912030004030503558800c40d01d4100d0041c4100340d005040c40e50302e0b8001149600c2c0210742e000e1684d0503510740c1010f8940322400c1140c60340a500c030040201b0b41c881203010124112002078801c00051550000d0003c0c0140c4402c42661020401000940e030340b9010085a62201e00c81c40e04401c001c02040d07070140c60901c0011f49410081001c8510941404504000140c03194220124112018100c0079500c4500b08030a40d031100c0500045015000d180f02c2e9016402d0005801821208143d41e2450141c40e584c080c0b007801100c001d090751055480340030bd040031440e103000302e66515104010009826001c9503001c40004829005544200c03400c111000300c040000003903800744c0d03954140040e034030f0300c0700b5580303032946002d42500030000344 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 751107886 1250 751106636 751106647
    0x1602010c1406011712040e011a13090207032606090a09060617070b1804110c010c091502070b07110f0a090e070b0723160b03060a0608040206030115090506 68
    0x70b00650184c00306243c0b18080b128100341e0300303400c84d00902690268140c00a03c07540108110450000c42c1c20280005c1036880345803401c01c1102c04807072030084d0440400310f030300040d240e0201544a48003c03400110303820008580340c0c00804140f1035036005400b0038460340114021601110060384003100a03544039800300100c40c0e071f500d0f000100702c4040c0b032005543d0044010024183d02d8420488120804c24082400d40c0641d190402008100c1c0f0318042290980c10300c20303184402024071902104000702e4482c8005030f840c0541c9a041c84550b501844115008014200041c402d25005c1d901c25580c00010958000c6010000c201c040040c4149258469001c000c00502d1070220f030300c02245619040141d95403d43c4a0070b03120124801c00d40c0045c82c070200514a4003440300e951004240c1022000c060342c5011110503800440c02c10309400440c10a60b00000b07000680c0b0b42384403402d004141da800c0c06807240c685600010740c10302052081c002c124440040f01e00c0b4a0b403103140c1c0c54000c0c0c17400828030b6440302d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 751109136 1250 751107886 751107899
    0x40e01060306150e04030522081e0106050a140303090619020c0102011a0603090c040501090605030f21180607030e0909060f1503030405280603021602010c140601 71
    0x34800d40c0701c1940c60924191601004002001c5802c05a80302c1c0007000143d03445658044410b507006442002416442c480d8440c0c2e240d22a1b46e1000081ca403940060a1b28040341150314001e0707403802c0c4292a168500541041161140c0e82c018084455440c10101c1c08000b03200440d0661240d400c00c1c2d03030b2000d00040c9030028400c6c218008a25010300ba422110809003001c01642201c0740d40040070080001c5440076442803a1840045500101700c07015070f00c105100e5004a400d0710420303000745038443e03101c80c0e050160341001c03c001491100c1d20350040440e0303260710080b4035171100220300d00550303640c0c0040d030980e11154140f0070103078813940500a596180054180103080289500d0024440c0580b0b40108014520004900b8018030300d182c080c200030388600c1c010f541365140e0300c000d03150940000d0000180c0c540eaa8103070150700032032000c00c0590302c42c3d04000b1081048550b4000c00706052051000e00c0c0b025000961518a881c1d0a003880d43c5060381e01d0420b0340400c00400152a03a9100382e000104c0c1e03c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 751110386 1250 751109136 751109141
    0x1b011107031e14060705090402030c091503092a0f01090305060f010905070c020f060306120304090c020d0f0203040e0c1b2b05091e030d081609060c120e040e01 70
    0xe80e40a981c5600070030350b103d41c1554680809564034000140e00340324420840c98681d005540022800c1202883c10341000081001450042a21300d00b101000c42040b50500d000d005041c0030f1403410f002c400070380c500d0480302c1e50f211801c02c84c002d002d01440101e0703003400e134040c60440001d50f40090031140c140c0350035400d042c0b2541090156000b400e0030070001c500018010203903600040c1c0d00800c0a4104c200407020704c046500003c0000d0b41c0400c1c200003d07014110240010b00103000015004595007406140c06480c010071f0014980420804007022a60a640441542c0070760b1a0811302c06c0082c1c440120206450040c100317601010b0304108078080d05d0000020307440307500b420b0f440c0c541315581040c008041140c4442020150105408004144080c50100d403200310034505855094a010700d40b0020a142c0306441100300040f84103441402041e21543c18030403204012841c1018100f030418034001c1007841440c030010481d000e2a041e03400110b014908110382c108011340b042181c4100c201c1480d01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751111636 1250 751110386 751110443
    0x3020a0f390b040303050a081f0303020114060a0e0c0315040c020f070905130b060301021909061b0f11030a06360803010e0c1909050906031b01110703 66
    0x1030000015100082c0981c2000035201100e825465003070400d00004400c0c0c1d20440000d004030516468540903003020040c0640c040c02a43c000d0303000040400c3c010240c1190014040d0038244126103048080003500c1d417a1a070b641d0b00c0712001184d40c1e00c9480d40c07040801e40e0207001600d107030b01a00700112150015400260700b01880c021000f103d104946e40e01e03076030007102c1040e2900210415085510004540c0040040f904900c0c0036000603d40000a2816513007070143c8a0144005200600d04100042c0d021401d59410440070a414040540d41c0d0f489101050343c94600415100e041c484040143e9001d100b4218000e42240c42800a6405044c5100189401031520343c20803000f0010040751040034100c0c24241c0c2d901c41d40d424070b940d0910142d032000b00d00040158494a804001e111804040148040c59140890300e90200a0742020300704444084d00822440c0640e000042c10340469000780036035001804282041d40340320604145542c141401d0ba00007600342c2030742d455003201c1c00c558400f00c03c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 751112886 1250 751111636 751111733
    0x50c0f01050c03071701080303150d02060403080324031009290714032205071e03020a2324030c0a0f020f07140d0b0405010903020d030903020a0f 64
    0x10810201c071058170760000c100380120001588240300180a45103500f061240412005068180148071035002807101e1303005420440d8486004810b00c43c01c454100005c0071208050003090034100e00420100c0d584024403000c14083c40d448003030702800d12802c02c0300740b0907281da007000843c601d5626070281c0e00a03007400e642d0300000580c3c1c06a40c408044040059a00903003a20901181d0031403000e00e404801c1004103400d4941d8010004002030311000340d0310f14140d886d030030407410405130b00c0d5004014401040e60b000c9400481e0200c000c20320310000b0030381403102140071918410110000315030343c0c3d130f555206c14440741d500400005000e0040f0301d000103824100138659943c0320300d001c90f07074041b81c030f54204040c2c000d0280d000307040c140244800003d000e05415070140c100345880781c040d02c4c0c40c60800c2d07007907400703030b6842e50740e03c24030402d15905000560101400342014408210305a81c02540c0381e4106070040e1481c1c50042440041001d00026000d000c1d0b1300d100c910612070503140451900401a84a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 751114136 1250 751112886 751112897
    0xc0b010501090308030105060a020313030c0e010509070e041d1603060c050403121202090a0b0a200703031b141c08011a070213050c0703090f030803010501050c0f01050c0307 76
    0xc00d0341c42206000c040d2903000040504503442d101c01d00c01c5641045003000b0543c00140080070320002e110b42c1120080d03000d882d00115462409903070428100046e000709003e041240b08024a0580114154085000070f8070001030001c440041c140c114460007840168900610140941d101d501c9041d810980c0e0041c0000c00410603400c005441500c2540b2004140d0188664260b40c000d0045411001a680c03401c070151034034203000300045407210b1503001201003420105071400d031144c0c4201040000881d0a1041d0716940c0c84040e0965110400c1c030000b400c001e0142114102c49480345042c3c0c1205034411012a003803210030400a880d609003e140c4ca20760450f844140701c1c0d07144500d149504807980004000054136480d600f440c250b034002c080503a044044181e041d01c0e00082407145a05c00c55141c0d40c15a110201c0749002000940d00d0b0b8030400002c0950181800403452001c100d0341195401d00b0200e6035049048003103030401d0b21076042c1030307010b5103404108401064400000d5100b4011603440 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 751115386 1250 751114136 751114139
    0x1c0905070603090b0901091e030908030301090218100e060f0f03090c1806010c060902030a1403132c07090810020306040b06070b070f020a0c090c0e030619020d0609020304030c0b01 79
    0x5d00303003202c0d40c60001400001010800c0c0c000700c0340441008494500038500091010303180d00d0040e02d15402a4050344000d0b40c006098060415092000342c42c9d2582115140e5611010070002072030f842030003901c0c0d80300d40c00c00548201d20404000445d1030030100000110307203d161480d211501c2e071044965450088021211084c0d40740c20034005c161103210b050312255100066511440010500781c1c05c100e80611605000102164807240759509403c031440046a94070039a9851107625003c1d039220400e01502030ba1116150301c01607400c0310f1038090941107040c030341d5601c40084929554907440303e030480c01010b225078400c02c0e00340c000f0b521509080d00c0c28071400d0040e8003800100e00c80c1e044007411220088001c505010b1080180788c03030710b641d41c0c07040b17030142d80c0143c1b200030364071010781e00c60364841e0b80c5c82840916840d0440d507161050071040303025112503c4d081008600d01510715114950311540001d914608a0300ca42c000406004082000c6441c0c0c90030380f40240c4203280e502019034582c600c0701c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 751116636 1250 751115386 751115401
    0x120306080718091406040f02030106050d0305070b0714070803040c051816120c0809060f09060a0908070b16030617070b3f0a111c0905070603090b 64
    0x60580448541110006800707a502c001c1c0b40040c21030100032207001003500d1482004040800510b4043d80c06400340c1900b031600f40c4100743c00c642d40c0b40e00580c020a500a02c00c00401e0700141030304c807006c2d01b00d0360a0301144c0c0c07004402c4407980741d04c082a00c56008045886401d0240f010f0155101e02d10542c2c40102898445003000480c400c5809600f0614583c0400252100c00303034000c0108001442c107105034141d40b503280010540f40102010800141c9150130803c0c0c1240c1004102c3d04001c204404141c542402c41031940c440d03400601889106807140ba0840801003940100d0f8809030f0007030125489400c018880f00c400002c00c3c41c41c04006424650003107860f24041740a03104400c2c4120041248038504020154030341c00c909a4401c8007028a0030034003c842002c0071403000256040c000041e40e0140070702000300080c02904080d070240c50580029913540c1e07600116201041105034000f040d18401803ca4050914994010494041c000380010010b0b015040143d40d030f0300c100d0104d58a96600c02 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 751117886 1250 751116636 751116643
    0x6110319020c010b1221121b0c030706051807050307140109030602030c1c05360d030203010801180206091c0f1110020c0d2a0312030608 60
    0x980042903010001400140094a40e008040d0b061482c80041800781d0048009204206140c403907030495086482c83c141403800d101148101c0454141d007050078030000e8408400d0b8100010040201040340c2d14026031003010301000e480c01125800304481d5182854a0300c85c020300415119949200b0320302510700e200b10340200c1c1840c1503e001030000d01480d440c0040d0716031100e13001c0080e5418032031802c40c0440030904d60b0005511842810b440c0030b680b4034014988016408100000e00c290a2030002417282e041c0c5a80d522035402000c1d0803c48081003000420304040e010f0038202c140700c07445922404101c0d05d425802035812503400030020014200d9485000800100ca164001c0d4041b03010400d4104901e00300f1039040401c0101e6520052050300d41ea60340764248092501581ca00002c142105c6440ca00880741c2400201c1d02e02c0a088510416004206501071070301c0001c00d00c0100c01142c018404c0c00904801c100c5c032200188401b141e5480c00c0c051001c1d41c8035000f0400181c100703940410b1540001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 751119136 1250 751117886 751117891
    0x17090d09240503181603030f05190c08160b01031e05071502011808040f14131a030115030204050f16031806020a031401170a0308042607061103 63
    0x820203010410700078601200c89500007050a0a800280c45220403410800c01290104440000c2c141c2c40d035a095017809010341d1001d800c00f00400c0000c1008000c049114842d0f03103150b544500f00000c062103146886070841c00781c8607861600100780401e080038040880200c034103c80c0a50035505000e14040d6040c1617800c1d00d8100036005a100c00d008004400013951650160542480001703506442103030b4010440010200079100580041020701280d0000d40c13844000f4100929802404545103001c503400040d00201d202290b544e80054525030000b662001c4480c5c00003e008000c0d0f054806070a254071121400103a01032840c0c80c0c0021130911403240c1c005d004840381a1622611654240f044019000289031000d03140c031400c0300500056031038006880d042c01c541d10007051150f00c00c40201242d04050340481041108002003040684005c10210750a68151900152a954509001840c075280b00e05040e810090b1070740c2c280b0070002c400c1c003418406100b45c4052240445140345c541850006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 751120386 1250 751119136 751119179
    0x306010806030d17150d20040911011805030f03070b0c07111c060f0516020d081f0e010b070302060a140a0507020c040f02190c0c05040c17090d09 64
    0x106262840d1180f94002581e0780085c1544911000840d5400403528500ca240400c03110902c114070700403022012050100e64011080c2c03001c0005614a89a140101841103ca1810b003e8500c042403c2d055480e034120f0040e150190403100c1003240d00c031400ea42c82d4427220081c0e400e91012404108002c040e24219644103822051903003080031103904220b00601c0404c4807019006181c05e134000003e41d140140c1c140911446000555464a0417061205029204808046400545e0050146900103e101d50000d00301101c03051200c0910020b640c0413181500302601c15040c090000448042080040c4401071195003654415143d0800746e4080da007078900d214500b0320101c0000350200386030b580015408491403040b10b40302c1c92407001080441d01f942c8441d070021600090004095001c0030140700f00102070345004007000c404e540711022668031a00038140704546034141c0a06261091310f1004900f56030000c1c01040c2d01b00110b49554562022803400c000c2040e1000001e405070342d00045003502c004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 751121636 1250 751120386 751120397
    0x1009120f1b0b0c0c060921191b020603010308090a0f12020105090a12030801051f02190503040803040605030103020f040b0105030a0e0f071d010905161b0213020306010806030d 77
    0x51607580b000c0303000d002802c03045124014000807040d1841004054012803000020f001c00300c1e04032a240c144401d490700041d0300d04400300207060100c1c110707401400c50301d0242d1500c04481002110180342104c041d4002940c4140040008010f01842030020312584004542d8000c0c070550b00d442140d03d402c0641f160301c3d8441348042030750016500030802130032500c0c4c0c004c000425947d00d90342c240e9481344901c001a0f0000d11450700501c281e04000c4101c1184803466040300000f0000140025900c1e1620303081e11144c0c00100316100c080003000c00544010303100171010390380c03660f1f1a100002c00c10f820904c41030384144800c030303401c14040c2410b105001c002d81d0181c0d02c03a49143c5d540e4509001a2444200005c0d0318420580ed00002010500c007540c09481b05002c8207280b44110841481980c0041c1c001c400124a000d0034840d01c2420201089448807180c241101d03c3e9004840d000b0740360184c40000703504003404940d54420211540e0045106e0300e0300340c985800c27549803c03090654070035241030600e01241 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 751122886 1250 751121636 751121687
    0x31c1107050f0a0317070803190507020601120311010e061305070b0702060403080702030f03031609051c0201082e0608090d140705030c010c0504030215030402150c1009120f 76
    0x5442d040310242d0105617800c17052a180c2c499880e203100380d008403403200807034914142e01c603000d464a006440c0c224101d48010300c2a541007240600c50520140002000d0040e012505054000c0c00e401034014010300200307507402442c282c4004000040018001c0b01d03075029101c00841c415001310152840c082d0050802414181150740c0c403180d07607022103000c6e64940305405c000750800d0001c000640c403480e0b0880c0d0840e06181c4840c806010702d58160001c600c50461040071a0342141c001d2543c440c080c0c0c0920345020785840b4208101e08000c00c0c8050130002045410880c1c201c0820450200100d03a4290346085c175654502ca0314580b65032000f101100040c18100700201a600400050305405000f403084c0c1c0d10b0802e040d812103013100e8005266001107480864104250b291828040c19046000c0000b149589005e600003000c00140790362001940402081220b40710008002c450070030341c003a0a082094582a0070507542c401e0782082164002500c1ca504018203511030803001c5054104041141d1a04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 751124136 1250 751122886 751122893
    0x3030e01120b040504120e030a0b040609020109211202010c080a0f0b180105121c052505060f010f06090902180634050615031c1107050f0a03 62
    0x620303a00c0c401030180c82e292181181c50342d4451040c28040d900c980c2d07101090950304940506911401411136200307411280c8114081401d000459074456441280080c944610f88010b88800b5040e800602c030008100c0341c1e000d020019091040121801080c48030700b50107145c2d50403800d0f00c0070000060005903041d800701e40c100301283c00000c5150960321000c1840354180c0c011541c5d46008008204070310000c04010041e60808540c160400c1640c0d00107001141c200d00300c001074190035402c1c2101004400500e0758240c4001034030b0564880d003503130000288140340c1c0c28902d9880405442d030034074600203000000740c113500000d0300b40700703d030f01e55180c4224a41c648071044c002504030002017420030707280d418217920982da4000141b5a00d484020754004942500800800c1001440181c1035051205000701c00070850001d07869502000030b035680da40a60801020070b092203601003481c03d041000f501d02140c0607410080300d0043c080c040302110318856072070701040b1551800451840c1c00030f01044061010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 751125386 1250 751124136 751124147
    0x403031404060c0f26072105030c030405070512010203060915030d05030405070b04061206060f090306020a03112a0a02010903200d0308150a030b011205100203010e0601170103030e01 80
    0x1021700030180c0d40701458403449001482e01c030554900070403402c0021000100002e4a03858101041d03008600c002140c88000c000d0101c0c840079040030341000010002400700441042020007400740648240c6141003540354040c084c1d00150781c09845207008000040e806007080c0301652800400034003c0241c800b0413523003074070503604c00791041d00e842c080c2500100d0007804030f10050000f1310465441c0c070f000e10b100ba240c0d6002c86107180c202c20204402e1900384040b150303000a00781d0980e500900010b81da40281c04059001780f0b11084482540d2501159554000c00704108400b409a500381d804d44601400080864540440c0e010090200e07088405c10300100b0510192050030056040318081080b8601c4001001034040d988101c00203900700041040d01c0214041103001100103a4801c10001c1c1075940381c00030f041050181503d0381c418101084144070003080603254500d09001d08550300d5031103a0604079491021260300c0d000c21400300744040324605290821341200d805030b591b29003110801004440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 751126636 1250 751125386 751125413
    0x3080a0e0304030209070c0b070203030114102c0f04051608100b0304150b09040309030212070504021215030607020c040b0a090509010501080f030a021b040e120403031404060c 77
    0xe00384400e00000c00181c84200c0a64040d40240e1910300c020240c0d80780120340b1032030046c5600219001440104128612405020300c80c02d0100e4603240b4a000303403181200e00144c0b01d1200107400300b0104400951942620510b2100030040d03d038a03d41c0c44030790342404103540e4140c41a84000303440c207441c0d0402c184118042600003682440c000441591003503c101150401d6600f40c852a101612082d1031a07a00d120317a512044091b6a908041e282a84021713040580500c0041d00610000d1441c21509106200c010040d00c0f0041c01151200c0d60103808103940300c01150f03d6051101050380c09503081c81c1c0080c0d8103104503001d600410800d98500b06000c06400e006440710b400500d0301c040402c001c1214080c0c0307441a8080d2000140c15850403640c075150a20b00c681c0c044154100708a42e14115034007103078801701f040800024041090100000c107000700030b540c10007000c034000c3e0300d15202c44844510041c011240a80d80f20700030754401c0440c07024075103d94131480000c10a403070800c5001030303010700703d010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 751127886 1250 751126636 751126661
    0x150b06032e15020106060f0c0b1503030c03090405102405070264050a0303051e0306090a1815140f07020c0d06020d1112090a03080a 58
    0x144071124155080c850403456400005450050b08400c80985609228180080803070345080310b40d07802403a1014001642402016143c2902c0344005841070111808040c0070750400340c212561627001104c450f840c0c0e000f03182900e10580c104004a000c100c82e20790301c0e4099503441c1d00c220081d01104400b81c448007100c0e1407604140401440741c8405070341d64094880103076140300032800c2c6000c1030409042100450bc5e0007012910882e0246001100c0d020040c825601c40c140d00b0b070020300c60b0f9201d005145001c240d0000c0d40c000007084003c0300305a4071401400320383c00c10718a08200d441d00004640b80c1400200c0314603070045007480000c0e00c000c5068205c0d1200341e49290b40440180116211440441031020b01054602d484040c2851550100d01d1241d5120300b030481c4d05e103c035041a01c4c00a40302c0b8181c80c0580d205042d035420349020706c255a412643d0b01c21003040100413600d01e8100d04082a041030f0b2850301c501481100040c45034102040d903211540d4107079140c0308907135945e041c4040100301c03003c40d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 751129136 1250 751127886 751127941
    0x405030c010f0c1a01030516061b0f1205070b0a050919110a090605031207020f0d050304150e011412041b08030c010b092a0f0c030d0603150b0603 64
    0x810403a00c440301480341c80221604c11036065042031441e000e4104e69400401401e03030b004000c1e6590001124032a52128103152810314101e00b46402d0b035040410000c0c12088401d4034501010303820000408409111307180340501a5503052045080310021211501c032501315000111b040114062014241481000b44442c9000c01e000800c00394a10754200304903459032580c06010601e01080143c41180c1e945141c1c503d0100c15502140801c1410055075018401558022040003028400c1c1c401800703a05807030080041d40c1c7d0342c008006104c103042150101d0340c4807100410310300d04075003281c0203a042565410255181c656508a1140c4c9450f01e061085200d10740110340d5000600040510508030380010034190a00300402c50340100c05010444403c0f0a52051010b241c0a6440c800c0310b881c0e00600ca030f8940d002c040141d1010301c80c03080c141d540d40c0000111110407850940c80b000640b40660310b09404040d03148020001c9801c143c003016400001840040c4007040b56000580b03c050008184 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 751130386 1250 751129136 751129157
    0x90f0c0d0c1e030c05030a1a0403020c060f0901031d0a0b1906060c060c08060d15110318060622090809060403030807031118060d14160201110405030c010f 68
    0x401c030400e601e0804002c0040c0c2038810420034480720360340800107040200d0252481103101d980b001d4281000380000020102d4640008090600901c0103c0d0840c3d405040c0a035682d9014180011583c4034051250120703183c1051801c1c0760001c03850102c3e042d5082c800401d0040410788425020640c010130070001000000f2110440c50b02c0d80c040c2d40000c1415407030302c0e000424075213805025203445034011400c004601041005e41d68035140d03030a01c0c07a9001310010301201c0c400400000a8a00708402c45100d5400001f0721201126095025000c0c1111000b990301c1900e41d40d0410081075201022007028a03400110708403560280c0e484822100e104664441c64001c0c0000031030841c1e007007070788160b01040c8035904000e843d54160085851110750640c0c0326180609489406000382807600110b400786002003214080031001c2c3d8008040d402d410b031850349803031603c28500a410305c54481000019400c0041c2c0c1800d04d01a082610140c0fa4000d01900d6002805001140d00f10b51412405003000003c0c5030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 751131636 1250 751130386 751130399
    0x20105070f061104270c1b0501092001020d030504020622150f02060106050a09030609230f010f1a0d15060602062403120c03040b0d0207020405090f0c0d0c 68
    0x2407008086001031001105d41c8600030702400000d881c618103140b8200380f005401d4941c06080c907d145138075100c4014461040307040c441d00620300640010700080080300e9405a86207190320081400708240e003298088010f07660200d05880b816580203420030024040303c081115902c0e40345440c0c980c0012141e01d41907072001c21034504946001c6590204a07000c142030031095041c03102e03a02425090800a00e803504000000f80364152510015040030b80c0d031510282040701128446103910f40c483c0d4414040d100c500c94942e1507407240502c0d94007661030940651000741642c09280750040690200c90561803880c010701546405c1244101c403904550403c0da080c03010544100c1c80a800b05a0060005242070180c212540200080003250088400c61403c11542c00003070389411000f204041d96212a6140010f83ca10300854021208610011503108070150059014042c118002c403010f02460311a280344039124520341c1440c0003503800514140826050a900402a80d8070800c0805141540c7c0ea1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 751132886 1250 751131636 751131671
    0x1104152c0f06041d0703080d0b030312010503100b090109020901050f1201150305040b180705030d2706050d1a0409030203030702062211040f060e1f03020105070f06 72
    0x8900900d9218000280702e5141804d00c903020203c18040c416158a400c000340c0f030765a0350401d20000380000c500280c00380c2c0c4485284c0100e018008050300700c0392520400070004c402c009090003003a00a00c512075140d07103904400c2c00740d0001c6070b401a001100da42d0900c01c081c0041d50102d4038860602c07a0421a1344406c40c4084020400e104e00c0600034000755040c1242000703644e071000b5219082601300b00c24000800d1611009a400060103150403480d0354055074503030304010180d80002d5040c0200034074200040d0704045051613050591a100105001e20071a04800001d503018035000507a041c404411034544640c0100e00403040301840494006d10304001a0039280000402c0340142c0020003131000780303601000740c0b58000012181c0080030351035810050300c4485007101d028040260b42440c3e020142c5031580b0002a15121550074801240c4501c21240300860580307204000c255865120542c0c04204030f04502078a60595420b854a40715031a5021540c611540585841d40e4aa414030070f101c4000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 751134136 1250 751132886 751132891
    0x7050f0f0d0f080307090b1312030c060c050c06100f06140906071406181b0a08072d0f060507061407030b121203040f140d0c1104152c 59
    0x11240d4660328a4503e1780205140d0745684400091942400030020501c0c100661000390748940a40190311800b9050403100030324079100c042d0181c0d14280e21030400c168454010714401c52028100c0d4020b840c1c07000c55844035031140c030500010441e1001d00344041403160030198031401032031840504019010000486640c05601e0895a455280c0702e8581280c00500c40103034802d00ba41d5644039038003001e10034151511110b445402c8030294034229800c60769968005280545500742c129403415407a40402007051282003440c3d00c41700c121a221018120b026000761042c3c1d9032007108600d1442c82c0c008143e86640005500300c590544500c031410f6104940d8030458802c04441e90045810380b0b180c410301000850740a10500c1c0ca412103d01525804c0501c4220b0f0f4005a01c031400003140e200504207041036550b01c900c011461f0142a20f200c1c502d0307a0041305c0040c9a030240c0841c000e0f403024142048100d0f060a0002602600d200508000348202e00d132072540c1d2004c0051100180c170310601c09502540808 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 751135386 1250 751134136 751134143
    0x7080d02300c100c0f0314151206150a150f0c060b120c0415030206090d0303090b0106020d030f06080604021315031407093305060301080303160207050f0f0d0f 70
    0x8411138054065400b0f02d02e43d01004031400c0800c45c010140c000014070b0034004281b15420001c2500d03426450f1500643c90198a50901c180c03102803c245003124080404050814841c080c4104080380c900140034541d49400b5184e2210310102500301001c1d603021074410010744980f070351480c00000a40700d200205058204140147c104084404100000c4420f00c65800c4040ca040800510068075004100c524075082118105d903010340c9490114058040c204000701300703580b01400000c0c0745400142100030051241c6044c00300500142d03482d0102e803c24451500d80c0c0d8041d2000c18050300b801c60b0891845040501c000c0382241482c402607080d00b02540c8110303044545030007080c04460341440310001502c0710782d80c180602480c400d080e54450789940204011034a003407850718892002008000e00a1a014140039140c0da5a082c1c9a51250001c40f003580744a0664180e0941c80351000c550501980c01c0280600090040f1600b4801c0346422000c00580080380000d156000c03c0542c0d18140d0120310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 751136636 1250 751135386 751135391
    0x7080708092d15130e090c0324132a0503030316182105100c02070603020a1814120105040c1404091407080d02300c10 52
    0x140041070061a0401181c1658078000c0000341a14505500391071400103070045454030800340706010403c80c07070702c9902902c0101072003100000070710001a150380e0344260108420303211034203151070905850382c20412101d603d108900000c280c026101c0d0316150323085900d0b400c0d4511100c00540e41c500703c2050300c03001419810340c01a440c4880c1c0c0d0350240b482000e4242071340914114101440c5a907114425a480c0905011060407071400000111804100612420301400d43d0100f0403010a0712080c50300c0300c15906401007840000c10503013503004d4034445010710740c000d1010510b040c40440080d009001780c00d08108000f0680181c500090b0802009802901d80700c11a0401e44010440c070090041000d07022f50741411304100c0030801054840080343d00100c1c816030800c0e050b0b0300040060200c1d0394020990b40a440418200c8080050000140c884100032200140d15a020036a0386100c106150f03240c10241c1201c610f02c1c00c0108840c1c1c2181c0c10301400c005c0c144800d0700c00d4182032002d17010300d03203071081e9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 751137886 1250 751136636 751136647
    0x301050103050615060c2d03030a20091e04022b060f0e010303030b2205040c0b120c0901031e0903140901021b0102070f0f1a21060607080708 62
    0x105040042c10709a6046820034500346e401c89520b9101c61800d00c4000000304000030040107180300311112042c00c18424140c80c0e032460303c025818001c0c60000003a84071080005041c12520400b541195460b1000034070180c1e0701642981c1c4424007039040c1488540003078082c081030368004200403000100300c1e1200003c49401009e44c82c1c00d41120199400444c20340c1d140710041101da5809003940341526007602e000b1070200191000720f204155120317044011a041c00b110080e102d045070340030750b00440c450001920302a903111200b030f10500a41c40d0500e40202d41002044954500400400c03410006050128041e10a40080940c41c082d060110070503607190b031f034030104240d4000041c05194069400b00c074181140d00380000d588001154480200200c1000003040382c2e8001c2121100404480c40c51a800a48503c640c1c0000c600e0303481000c0482c426500200c2c851503864094a1030316204204030303400442d81c001c824103402000390019402550811074000031600400003040c910340280c02413a41c60 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 751139136 1250 751137886 751137901
    0x31506042102030d180b0c07030803010605090f0f0604051c0c030305030a0c0306060e13060e07090503061b070f0c090212091504031d0a051f02120408060f070e03010501030506 77
    0x241311042e14020440260217100840e000e14009005030b03101c01c1129521041c414121b54a0614260409402c080300880000745081d80400203103040038040d564040456080b50a0012a03030032905419030140040c04180301c1400c00f4100e001c40d0b410031642c0140c2c284c416840e41b41c81110160010750000e00001f0410000340180d000e0400041c003179240810085180000081884102d402914030465540310401300d00701c120781041d8040d02d0600c50481d014100320002074055420b03442940c2c0680201d00c0020150082c0d81c44c0d05804403100c09803030386400241d5648810102d0562003c0350100b241e0003020407000d002d440035004495100d0301000580c00c01240d003906c2e04010700018081c4000307000401000035406600c80000f5a035070940203281c00d2005000442d180e2581d0007403500320100f0700c401c0c115000c0c070042e003158440302da4082d41d0304a070200307041484a2040d4054008a54070900209041c10104441d095100c07140c3e160960141d008100080c0c01c2d10401ea00941d80340c0c0c40072042c1f2188 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 751140386 1250 751139136 751139143
    0x60603020901080d02030406050a0c061d01110c0c040c2304050f0907120f0e0a0c0306050f0709030308060607060207050604050d0f020709090c03021005190c0803150604210203 77
    0x540083c0004250660b01508025640c0c8a20301810f000c0001c0441d04148080c01041c4426a40364424000d0083c0b45950a03200e1408100c6915030709035600b840019011000340780102d0341100ca0729000b80c503060039030b0010310000c0c000d6103c07908100a050001c3c031b90414100e840704130f482643c00004035910761a203010000d4664004000d180703d841014180221541c200c800c510789078401110202d182482c1c02d44604c0103103060a00c401d03c0c1d0144801003020484080f07654410380e0720a00302040035840e201580c4020302000c640884c040703a030920007840445c1c0141c0c80150b10401c020304051401d1015a00c60007680c000d1b0604450039030100b03051108000307003444400070b100501e1502c181c5038101c030781d0004d5035494280b2809601541c4d84114100b44030107041e4081c05190081d0074980c0090500c2002415a440081303402c14816081020303040300b61180c120449156007100c041e50440d280c403040022600040c04401c0e81c881000c110001e5040844402d01da00580c0d000b00703c0112400d40d0043c1400e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 751141636 1250 751140386 751140389
    0x30501090c0e061b01110c06090f07080d0810121101090905220c0509160e15030a05092a040f0624020109050109140d020d021b04021204060603020901 66
    0x82c0a00168016010b0300c8001c00e44030ba03c0040348260703034240000030700a40182026124100c0b1184000344502030510006242c0c1e004800420496003090303403801029480c0d070034500918015802c03450701051581c1c416404030f5004600c2c0c100f40210180d46614045079010360103070444180150460440013503070000c06000c0203050311107040c0264501510400740d042c1c6000301e66549040060a40d0052080b00c100c131030301418014000b5052030030702c01d03016a45c4104580c0e1803400501d80070b40040c0c040c2000c0703200c4c4682c0c0d5907000b0242c2c1107071101807151002e0b06000344220b5852060b07038003c80c0f240100403100202041c4164031540c00e00079600a110a80d00008040c1007100e0500c2010451500d2580f17948043c5605101c04805103110341501b01d0140000c184013522660812600105000d45034281c000711110800443c1e072003606446060340c407803103515001e1016800c0303642c170640380c6070340c907800004081c600070001450708540e0000031000d1001030b141038414544d211402d00071070600e009401e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 751142886 1250 751141636 751141661
    0x51917070f12020316050a092412150204030305070605070c05070f1509051305070c080c010204140409050c01030b06070b090c0102010e0312040f0221010923121b06010603050109 78
    0x1c102c03a052401003038404015110306411030380d0b45c18589c0400220740074443e500705d04030059800380c3d0f55240030020303002c034122038140d4442d13058120f082a541c4c417030f1084600301c039419120241000c00c10307203c1400410004003d0418441e80008440c0020030500a02c0f0142c004602005203441c01c1015400d6071440c200049414440d4a441c2405103640c0c10ac07016180b52441040444d655a80f03940464184402000040c030b080344c08104050008019009801601c04a0000c45842c806030410401500c080b14805010b0341c00c000440381c1d807544640c204101c0d10202414443ca00395241d41c500c0e845c030340300300e9840f5100d41060350f9101c000d617420b0140c40384004040000310f0514420061854040c00040c000a000000c2800303100c0841d250080d00320307460203c00b10241802c0e60300c1b51001d4040d2200030000c807620f85d1180005c0620f41c50500350303045c0300c0320349600a11150000c5900e0302c101d036009039070a51240310048100348026204029041c003030700c100e42c0c010445500d0400c03d001601d5426600c032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 751144136 1250 751142886 751142923
    0x19030e070501211503062a0c06050a060b07030309200a0b181305040201020601061d04020903031207020f0c03010c2c060a090609051917070f120203 65
    0x10081c5aa000b00c2000d0340069103d80640e00722a02c240703a1009103064800c4808080c403c441c00000d1000300d6010325281c82c91010403031000c0e040c00d1550285800d0760810880450024502800414619400244d010412060001c4c40d5500c5007200320250300152012800291260481010402402c820324410860042811102196800002c00003904d6001c1d40820000104000424140e902402204904090004910100c007120100054241104d00360b01511600000140e258415413505a0410f9a40e01815104000d0300801000e0340c0080599a03140c4814080c110000e100305032440d008074143c1d0000e152400d0400c113160b080c240c200b01a01d00c03a914142d525000c50340c224031504c11500c41c1c41d01c1c0c844805040200400c4d03180d600700c0241e41180020800c00081d0383c0061011098462503111160040e6454007007003a000c000782d04000c007010303424500b0800540749000f09864540c0031801e849080303480b144084d00c50015984461012203000b05140290f040621216807089181040c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 751145386 1250 751144136 751144139
    0x2150a02072114070f020a030303020a031a030c01030f090204020c1615020c0423090303010906080a11060f040b0f04150f0806131410080d093819030e07 67
    0x1400384015003c0e69600303c03d0001d00e42c0100800c8a288002941e40140003188858480c00c0c0100213410841c2c41c840824030780345040f0f0740341e40c900d10b0082c0f18500080c0204802c0320000f0044001d080c10720991041c041e102d00306980180c0d654009060881007000040400c07a01c1d8884501c0180390303e52012110640240c0c41d1500c0583c04a40421031542c195004a0544000401c00245080024010310021015800e02a44900c080011030486d03185000504c101e5450301200d17034548103050301c01004524010f82003020390410102070060741c4800112141402d955142c4003009900034500d5040c0410006414840018a101e0302070100c4114074162082c0c0515100c007034204500035100c6d40c4101c0680303c205001e8602da030800035000308541d0503401117040c032000b03408181c21540102c224900500e80d440248610807009041103138040c410f05101c80450311407011030011101d05140081e1410079114102d030301080d00520103140c185c0840300545d40c05d000300504a4010b24911071468104a00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 751146636 1250 751145386 751145453
    0x90d2105072a1805150a0b0403061107150219030e06191b020a02030c09090601060e060d0c080a150605120604060305010504140f1c050a02150a0207 65
    0x104420b1100344044600c6010380e040c401d41507000f40219620701104101d42109a04414014041c84000502c00c07040b113020000b02140d60b000d84489030600f0301080010500a0308010400350024203582c0c80e00d003994540c0c0d500c8984155060800c180c0006040c1044c00f00c2c00300d02195a05545020040840203400b030603150140540240c07203904903c003044080d06550741c0f180c103800005600c504103003082200301a46900f10000c01381e11038000c03821600380c0e9007000000c0c14030410021014080c80d81c00e106055414010702d08009410610902062299011070701c921a00e9510544509400c2d01d00225003c00350f598074000c40709a00511401008000e400c142514040100701910f6100780e078580e070200e402040c441d40050aa9030074101400f052100711041c5494171582d000550b421131001ca541c072940c8000d070f00ca40c3e42980949800c0c9645d40b070b11540252085010302e10548030700140d4551281103103030f020340e0070360b00441e4005044402c002c02000ca40120f0741c01c9242180e041c028040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 751147886 1250 751146636 751146653
    0x32a010908070803270724050301030b0721060503010e0a030509010521070c0b0708010f030f020301020d050702030c0c0d020a0302120f0706120506090f01061202090d210507 76
    0x110003042c514000c00841c480142074207240504c0311051745450200148558005e90300e2a85100d0002100000341c000014025001c0920002403400d8440601d140d00e540d4594262040003401c8500b004013941000c490035540c2e0408188c00d000c004030208a03d42003904050868101d00380828050340304031110400a41c000082d81e02490702420003035111030a80d4002842164000284402081c82c0c01c10083c2641d000310f4151f0503240110502c00040d95000b02c19a801c01e000e01401e2489107a0303607002c00000d50f00550f90b0700e10b01c0c0302030005403c1402e4650785000380c550644585000d038101045162180b1410402d2000c0044200c947c1ca280840940204103104014000640140601c110300034902104003c11003041141800b282e1030265940b6000f070114039480025282070f81030001180c502d14000403200d019215a000c0e03184140d03e801c40940700c0341c56800c50094116001d00100103155611a4000c107a00e002e130300d1000715401e6030204000c604002c0199501030001c00d100c060b010585a1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 751149136 1250 751147886 751147897
    0xa0b180a06052107030b061b070f0f05062505071404020a050904020f0c0d09050114030708400227040303090201360f0501270503032a010908 62
    0x148452609922500400c40152032400c40c011f400a00014031207141401111071000c4120170201a280070645440e551814002ca6204508492880a0080c44645061401000d2406100e81070a00c1c40c00c078190b40300c000008400781940c240c1c0002108200c84030b441c071304104005c00204e504511781800102c000e23000340103940861740100d5011803814115100c1100b100e00f041071038800c840440445c0480100b82400d24042c0328000346580880b0010700e050b4130160380c048c0e1301b2911001c5040d52035181410328008a841d4607220030000424000b05c0355502d08401d03507650704000015a5507840c5005203c0d040512096031465500d0316031070818403c541015981c0c10552619020030401e256000480d0592050000c4403505031600c059031055443c810718064104114501441029a40d6281d6100050345441258041400e141980c04002d024404612880350001d103841a00303511130000c01c0c511307049400d031031a580c6442007180c600d22203054800d1900c080c20030024000341c00342c1d50b6904a9030280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 751150386 1250 751149136 751149187
    0xa0b0d0b2d0a03060608030409060f210218070c02011103030106090e130b07050403050f010b210102040305030414120a021f0314190c08041a04020a0b180a0605 70
    0xd0780c0c9040102e42d200c0000000464000c001803181c43c3c2c07148992a100e80c403c1c4261000fa070f00d0108002046c3c2e000800040403078054031148004030317100c0e407200c02e01501c850710100c1c0e000400e01206013002031101c010134000c01d015502c01e29050f40e644005003000140c00720f0f0301142c2d8410700040000b1fa50000003c0240c5113860f403036002c50744940c0c010070907500c075114004003c2d0500713104100c40c80d0348c03140c00382c01100d00a10480da84940218410b6003203a95412510f50002c0514240407c103070300000c144211904c0c08800180340c199030352900c034119001608400c811403194030810308035183c0780810600400107540a030035070340403990000b8032071602ca0541e4801344841903034201d0124002c1e031100700d2440c0e400e0540c60580c50410310240d600004104010915450180f000000758400c40d800e500c242c0d802404000070b04034007001c0352420540140100c4c2e0080e8203101c04214000000013414404a46010003190385038130b101001a15a020703080f44007003000a20000840c502001041c2c5001c444 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 751151636 1250 751150386 751150459
    0x7090608011412030c03070b0403081f0b09120105090a0309051503070305130f0b0103050709020a020606060c0a05100f0513050a030f020f1f0c09050a060503070203090a0b0d0b 77
    0x4040f4020303070540c041d440e102c084500001c540c0d10203001d020403003039105900c0380d601c84a060ba14070907004011922031350a0010511010018484000303808010990618020710000c02d880307100c1211402d40e8000c07283c0c28120f401903910107040603000705215014205c110b07031358202c1040144540c0f00c00d00004040c1000c054441d4003085d80340300459050030409070804202540054141880070301c4d0842880f0444880c1308454000820602038401d44503900c40e2035024110382d84581041001581106485c04100d0080c0510400011010002d00c164440610000300c1c20b44140400c03035040701c20007009041c04e840c7c1c0500300d100042d0045541100b550f41410125681b190a4408a05c1c002441036000218418513881c5851200920a0b40b442d4074030124040c80180c64824007101e50240920645d078000035906130a2200c2c074043c078003842d4002d91510440703003400080070016482080c540c0c030042c112040061031408400160050300140d40c0e081d20a405c40180250710f090010040035183d018161 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 751152886 1250 751151636 751151659
    0xb0f0402010909060605120c2104140d0f030f0204180515060d020c160501090b2104030c060f0507120c02070801020309011b0c0c090b2403070906080114 67
    0xa0049218802a0610f180700b0010303581c030342c1c40c080d000d03900c1001039000c1a03006000055103100b880040300d5441e550b00080401c8034217244000d407c00840a8821689680302502e40c00030203100b013117541c42c00d080a6881007900c0ca80305601404a80e4800480c01e40300d40104402c0c0729030342800c1c44600c415001d0502c0001d056481d501250f000700b50681d86544c2c880790025492050845a0f0007800c4485040810b95250002c000d40d20524000c0b41d00c41c29004c158015410449202080c002d0440b1040d94841210031500503081030f01a80c07000c60302100440d101c84484000c0c05194822040d5020000c101088181040480604103840b40b00384402c0050f04c0358140041c0510034401c410060100d840255140e04001f400d031406041407240c41c01e41c000c0c04040602d4100d1050034050802c030740011003000c86606204c0340c031001d40180300d182c0e60491000c00240c1380d0f00c1011134200c0c503540040c803610340c3c980c10040001440d100300c0350b00c60401c00c00450014401510441600441c0000c2140d04060b410b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 751154136 1250 751152886 751152889
    0x1050f07450306020d06050d0b0103030f02330c1303020f030709180203390d120206041721060114130303093003090504090602090f0d0b0f0402 63
    0x481c0000ca800e048046210320000c100503454001d08140fa00c501410301c082074a41080c0151107486850240c0b0a02d150303c0100701090061586252621a51054500b81da510320110045003942140f801581c40c103600182039000e130944101a008000401c100e0314184624102c0c021ba0005800040c0c407034040e241c030b80c0b403c42c1d40c1005030900500c1d0400c0c0511070080302c1207400a0100c0c0144041e40240113003042c1035800d8444001102004040082c0450500720f181080c0720f405500300030103900480c00140c0c03500480e401c86904043c205403540140f005141c00d24044003801082c01125021850902010340740064044140304490200700001c00d42e0ba94040040315401445203198110890000300701e40d01641d40103180781a01d000f83c440100c80d5941da05103451103851001100185100d0041081d000b000c001c03603401e0054001d260140c055038403480054103d070481d000c101c4100f580000c1d003a0244c1030010010b02c0050742211440600031054039011a032040081c1001c864400740340004085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 751155386 1250 751154136 751154237
    0xd0b010608150f28090905150610110a1a04050d0e031207050114010f03170307080a050604110c071a09030307080d0207050307030e0915060a0507060f0e01050f07 71
    0x8146007251413008a558031900c0e08020242010180c94500815001d541540b5600c81c1e218044c40300940302c0c00100c42054401c0b24902012001c5007064003c0b042140c2c0891500407030807a044014942e04141405c0c10b1030710610f000c81c1c5403d0902804140b51b81a041d9544c04100c8525100c801d0183d2640c900e59840d009004080003084c0f2500181d0a50010031178811081c05034042d00d1140c0580341056520300d0110340f490108460381d43c0090700350000602201590340145d0b80007070000c1e00108130200c0300303101003d5a400541d03000c3e03210b034800b4200b00214071103450b20743c2440743d6540c685898921240c02083d20781c452030001400704840003d240501c400c0c240e04517090700d40c00c0001d6075261030503440c1c014007031110f0146245c42030015034080ba1401800401c4000c050b0401008140b501094a000fa1043e8004d0102038a03500d50355420327505240c03000d000f90b10001c20900000901481c20f52501805058058110300411078003290380030405c4448502001655012120080820180780b6680308 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 751156636 1250 751155386 751155439
    0x9060607020d050706021f0b0312090301020705010603210302270d050d030f110c071e0f0b2d0a18050402120703060603090b060904030504050d0b010608150f 69
    0x80c4d00c030342d0000082c501d80c0801d030a072a2041c40301f261007810102000c6501074540607840d82d40d241d00440034440400102c50b00070405640082c0001d070031b26070075480b52801c403489980180e030081480d51012100c0740300c442410860b0340035030408600340300d034800d9a201d045c8207000350710007500e01d01109140c035569000b800c6510f81c0d600030200d4484d01d00406000b405000c0011266404a042c103048501c202c941d20280c03660420344000804d0346900d0a807031286951040080003190b480100c50100301e000300317400c1c0c010107080802d270700942c4e03020010b890b428031450003c00780e4044183d01d03100018031194001100c12602079407400700f907084a2217164070f0030802c455024641c0284002a4210440c4018504c81c0c070910840c8ca0400406d030341e904040e002e5842c0e01d60300074121034240c00042c1707031841e0000605810500918145007402d48400205040a08410013514042e00c4400100312a6501050141e4400812100245503048440200e50454113854405200f03c1c0498a54400020007180120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 751157886 1250 751156636 751156643
    0x606050603010305150114180c0931050403050d020304060b06071211070b0d0e072610140103080c010f020a09050102070b0406091823150f09060607020d 67
    0x2541c03540d4a1502940d0381c001c080007035040d05c2c500400041c841c49048807040440340d01400c0c000c074206009814090450000344645244801448001f00b1a100c103401c0000c031141e02070301440c408420520f8400030105850445131401d092404010000307600900341d540490b4072800c0540c0f03903101d5162030703006842128451070308101d012641000344074030140b442a11103ca42c650002d03840790310300c2e40ca8603060f0b10300030100304410811103501d91072101c0e404402200d0b101d506868161b82c890760000b00780036134006024050b856906081e00b211005020705216103c0401e0f0801c10034244e54403146c29010148405403000c0f4001c15216000e14080d0403c0942c49030b4550110740d50080300303001400f8401607014960052064075808034183c88014102c50a0b284152a03881c80146010302c01e2107a5040f0948500c141c903110a10132101c0c1e00305652081080f280201c01103584e2a001290344009810200564030a8105403041c0300a0b4498040e0301d5000b40065441590702d1a040c0040345194901c040b009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 751159136 1250 751157886 751157899
    0x80406090605011e2310091d060f0a05030d11010902030712030809010608191a093301031739160e0a020c06010909030e030d020d0507020d080a1d04060803090904060605 74
    0x8d881511004c5240340b00d020708655500040000718140250314110f40a0250143d025507551603100780030b121003003452409800049103400140c2c1c046801c0209644c80303111084590550003040542141e1100d81c400c004000802c200c42c03130412040d5441100c8514050003840e420035803014000c0c2103003000b00b00460f040130109503040c20160760740d488282d030480e040e6002440604400b0341ca1442501144007601807001c40480e402c58a03290960a200c407100c07103150350100000080420483e00422507618074590807941e00501142006019641e0890310720250816104240703807070031200d483c0341611281006880b4956a08100c0d03c000d200305810300020741302e070000005000003d600034951292013a0f4a03400150702203c00d05079191180c5040d400035801c030108460b80a4822005024014001000f401c007042483c0c540c1c5040d030b40400c18100006030402815604030085010f81907600301c054404200440c90044010345a0048050062162503040040b42c244121500304102500004080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 751160386 1250 751159136 751159169
    0x2c0a0b0a0608061e010602010b0a15050412060f05060a0806160201110d050603011406030304150c0f0303050702160807091104081507180303050307080406090605011e231009 76
    0x11a142d48807107802010411044c140045511071043c02911b0394490003406084606040a00307020840721400c210720308120060100150594803005c0d4840898051200014224074940c0c204003078400c000c4c0041c0c0510048681003104410001c1c225a200030030f04000c080c0d000c0e03045012405004a801540400040445c01d00d003a002c07035907c9a405842d04400800004201102c0005109000c503085941500140320400030400303440182c5440094526007064042d2041e501d10b0001c18500703100780d000959417020421416010000560302c45a40380318010140e1510031026070315001070140c0015640c9500c0084c2103802a031081e40d024003d2401030b0303502c48001c10345e10b04542ca411a4035000240d40104240403142d540c5c000941582d0709030751560f02e940d0f0b0b040c1c5c058800f00d0002d4821110940c1d1a80e6807c0407620a00c50b05000e00b010140700120003d10f00902d146001041d08642d1608041c00c00c0343c00285011903900700c6810050310b4410302c401541c2810f40709504681c0c0411100b58603000c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 751161636 1250 751160386 751160401
    0x181101031506031d0703111002030d090807030f0c12030b030f07080f073021260f0402010806010504091a0111010b0904021e0d062c0a0b0a060806 64
    0x1060b907039071081d8a0b91300c1aa140786080155108814400502105100049460b06007000050040c644002d030045030710780000c0d55030a5044a152030410344d0400c201082000405a004420b10078240d800c0c60901580802900d503800080e039039490a000741542c40040c60300279201032141140008100007a60841c603503505069481b029807805d805150b00901c02e01064040c0090607030881604041401c2c4545100c450340414203182240d03060720b120315441e1000c54049000c421600030294a603840b4540d5240a071111124401225040c00302c402860f02001310500004084036071140e024600809152203020050311144601e8000c1d0401c00c1c1400074540941504442c4164186001c3e81e80021002210401c5800c07034915159603030344a40004081005071030406c0c400b00c845034250b00040a244210000140441a40d5100f00e441c0341c0ca0701041180d0640b840200c0007403900211803d80d44000800003140c031410f41450007891140b40c440440c114074590340c800b00107040030b0701c03c98925091080 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 751162886 1250 751161636 751161641
    0x609030901030506010f020607030c030b0415030b01090605030303061c0c380d0c050c1f150e07030f02041203021e070b040308071a10030b090118110103150603 70
    0x2403128003181c2483c0105080d9403041c940001c001c0000d9015003040d8484890480151411000c0b001c10981c480350b100a00d9a100d12903485141300ca0001b17043d42525502e072111034048164040c40442e490038000700500d0301c000c401c0700c0c0d014804079200300080f581d140100409640d8108090030b00c00b0800408207076a0000c061007104c49402070100c0f00c529a212200c038002d042081501c02440030706001458000b03042d034000b0480c1c0c58103801c203142090309040c0c0d854a080b440d40c08003402d41c0304a00a466584146100d2200030900703884130300241a08103d0302e030b1468003000d480c070300400d591800c6030100c0b140554180c0d40546004429044c0f42c80c107608009545201017100d600c1010140303a400d030010140020150120f519000640c0c1c285807450f2240611500068020f0341c030900407030455030703c91326010095886088201140c00d1b50508500b000c18861400410081042c0c0c9490b031042c400794a43c0703e107070001c3c0d0b5000e01003242d100942c3c4c00480c00390142403440004901405d401060064164 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 751164136 1250 751162886 751162897
    0x6030c06120b01050403060b1809010b1c08071502040e0c030402041a090106051e0336031602031c0302030a0b010305041121070305070f091e02031305060903 69
    0x1d40d140c00100380d4a0808000701c0b0628207001d80410000c2000b0400a40c45410104049000410400341651019413421829000b01c0f81081c0346d9640e01480702d000e00c1e2802201c01c0001d82c602e40c01c0c003000780c02c0d03541d4801881881c001400c0c00c4080c40c24800f5100c40d40d0115006043d00005008a9041c0680a403102d1342041e50100c1c03181c1c0c140305100b115141d1215540c070800c107000b44040030301e91170301d00d040d5000d031b002c101c055482c04504180303c41c51452071002940901e059410100c1c400c0d0b440b06428800c1c00c80e14084070000c0c402454860043c07040042640c140b058480d240c5800e450301c52002924101050680e0340031041c007c03e16001881d05075010318850601e686080c8180070441004508940040314024051a4980350700f0901d8144020f25100c2c0c5104440140010f400c01e221180c6032443c40d84c012681daa20515060000381c111140f03040c0180134038581070106a0b504414460300010780e05501c0265940800040c1402c41802c00c402070b804e8001d42521494103004a041e9202d5101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 751165386 1250 751164136 751164149
    0x21180d08040612140609070f0201090501150f23010305070e030a030c06051303020712020607050715182105031306030518030c1002090d2909060c0a05160606030c 71
    0x14030903200145025031300d88a2003200d000b0240b10042d6070340c1c54103846060000720b003501150340e10716410001801c00d20800c040807165040d0920014a021440b00d000780e5141c001000981003060203030401c011084c06800c803140d090034045016502c1100031116660410070b000d52511a10300b00c182410b4010002005103030241c04240419640c170810490090300a040080050340010820041101c41c01032510344c00b40b0040c1003034a440e00540342d072440c0821503000580883c02d80c0e002001d0072030b0424141e01050140e8050101007034580a40c82984030116512115a0107109450800b0030005001702c1d08a555040c020341820350702c2c2d03c1c0003402030bc011a41405000c6403100d00c4001c8440010984080c0b903492070042080d00c41110410001c3d4115030441d982144503000301200141040711984030040c0504c443d5143e41441030700303070f00c00d042c0040c00035500da400000a100001c0f0b03611080700d8106640d410703c50341d58407864480000c0091005005031805240c084040100030102005400301e415 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 751166636 1250 751165386 751165391
    0x10e330a0801060506040b0d090b0c0c100501050f0d020a0b031003030e030c1c050a020405010b03091c05220e0a020405030f01051e13121121180d08040612 68
    0x480c0d1450310700f2240c0a00a45501810600080000581110060008890500f4045494032065482d00700d0010b081d201c3c08102100401d00100200781003086030303c2900c02c0034052265500d007502254404d08c0d040d8800e80075585c4000e01d0070940d01c90f03c0609006007240c99201e03036a4075000c44a03409940031400101c000941240e88003882c0d2400180340440070400901001071001d40d010280192648143c0c1200c450061203024001361395148200d0f802030902e540c20560780d1408207000d40c1400d13021303842c50207496074240500366916486003d442d03080c03013414081200000c0307502c1c07600303044651503014601001800040150000c02a00500f040300c1c002e50440d043c2914030f00c2414240c41048940c0d142d4011841e902d18200071241e01078582050781480e1590050481d82c403082c0100b0206c00d600000308a1544c0541641c0c3c40401610800b00481c08080165000e02006030019103e00341400503600b202c1d80300d08510b541e03155410750351658480c9442e541c0c0d0360345d0140540002c1103a12245295031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 751167886 1250 751166636 751166639
    0x902060c06040b1b031509040c0b030f012112030c0c0f080a260c09040912180b0a2f06100806073006050a0801022808010e330a 56
    0x50f4007029a40a806e6820401c0c08110340034091050821009005441401400d4400a842c00f01d50008502500d051120903c503581001c6d140903107803801d8401d90305259020032500000c00c00e24014294110050b1501045c002d07072499040321188403440000e400307402c12000100402501c00c0060111001e2500c400046d034521009070745c403c1440c148285017100c90310340080c9840403450000c1001e1740d401840001c600000b5202e40b0024040f03144800003240005e4101c55800d400c6222080040a841c0b100d140380c0400c20300c0090511101400c102e00f404507a40c0080c0b0b80030000500c0d4480303404914201d96052520100900016416104540300c0e4010840800e404520628200307001002c290203400a90050422410719684140b6a1040183e03550502007443d9882d03248140041040400260321400d104005142803d11111103130a401e105642c0c201010750030496490454400c52307441790407a0740320701e6840c0e41107480c40050b802144003249070540190501a480240c928280c07141240d89 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 751169136 1250 751167886 751167931
    0x10f0b0102060105281d1515040302060f1207080a05010501020109030c2003010e030405090c07020d081605060403080109180804140109031506030209100f05040902060c06040b 77
    0xb60028094542c10036003264140c04071543e180e0120081d5005101c0c002081c0e030352001c0c4c3d051a82e107100c100d002036a103040c003801041030041c00086034601041300c030382540c00c50600d00c01d8103074402c51000078000c1c04003003101c00015000d0000d071400c034280b040f00c1c03400f185000720f402883d4070000c64600c00c0c218503040021842d54414401c00020f1503140e111b07500b111a00d40c4850040d98181c2500708107660402c022407220f0f0b207080c05400380282e104070042da1500d040030200b00e40c031344000740f61444801051085002507522444c0021000ba00710851564904c100181840740c21003021019000e441078800388410994040b01c058101d0b1240c5004200d4004041e0803408561401c0b40060001d40c0d05020520001020401e15207440c041410b148004507640d40ea030803118102207556551603a40c40d4400c2003503003040704002d507100d440c0b035603056091818122559242c2c0d140380079041c05142d540c828001151603080441d04000e1040c4120380041c41d10303103442401c1c40021105203803480b1040031b00300b208 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 751170386 1250 751169136 751169143
    0x90c0901170307020f1f050c010c0825021006060918051509061210140106090303211e060315140105040e120a02011b05090f0d080912010f0b0102 64
    0x10359496001451070f00c2000e80800541440d05426217900c1014000d40b2a502d5810481141c01403005484503501c0d805042c4040d404c44c0d01d10f818150a00c042001000541c00741d1812a04a80d0001034070945484890a4120329015880212100d8a03240441c08110340d5042a1404202d690420454002c152840c92050a0302c80c140c40e000034a0f4020b8a00452601c0c089501540c041405013404040802000f0701a14280b4070000d0b245a0b144d8881e022155140752141e050b01404207810102c00c5980b840e94010304040d10f01c40141038980c00c0f0010251003113502d0f0407583c10a030201004492143d000c030048802003040340310454404900705a04c050f941ca60317014642058042241f24485a031030a010b000150910b2075a8120b0341c0540c65030703008001c0313004000d481907002da03a00018203840009203046810300e076085a00309000050200038202e5490100110301e101d02500c01d04064111131a00c401140500c03c603e580c0301030700d100104082c1d50154481d0548802000e41402204200c6006913103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 751171636 1250 751170386 751170419
    0x10b040c031817210411030715030f2c1c050702040b0a0905070518150301090e010b060a050d0f0e03070b040503120103030e1009060503130f0b090c0901 67
    0xc00402680c000800f103241c40c00c2414145400914581c640b80da00080600322007800c400910740c181050003071009102c4030711850050a08194010062907050800c500c02c05907002d10a6002c064407002e00d60b40300340c5260081c031b800071180342038800d040150b070356a0f280c3c441d105075030785065118039501c602c5894081003511001d20780584540789000741035001d10000c0c0c0041042c0681001403900c1c001108442449181c3c400d4446550303840d2600309086a00d0305101a0640d0b031442919104c01c5100f41d00c10703010880b030446040c841d00089801700c0105a902508011900b80c1c0c0c003120205041150340d40000040c64168066002002040c00c156070201c00c640000f51400f060b0b90040c021140040c440d4010b5982160203002180e0800d019040d210fa60300c5800d03081200080c807840040d103c01e00b48030650440540c035a040843c840b42c10000028454000200281102a4914819810300c407040190381c4203140c00811408061401601a40d6101c007880a07850042e2070708800060415048041e115 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 751172886 1250 751171636 751171661
    0x1e060215011a09031c090e010f0503061918031d03240403050d1a090609070c030818030d0203222105120702010603110f150703030204030503040602010b040c03 70
    0x10b0a103000c0550015254200000c4680c0502c078000b04d1101c3c0504200c030b008441c9840741d8404c88080e041c0308900445c100c0c1a8000320945103903910034001e030355002c0780325644541c00740209480a144d540394031020b0907034150191340b1481c2000c00201890390080b40c0d046425515903a0043c800300c0701040c036503150103d12842c1c04240c14900c4000c200020b128801340c129002e4580541015822589001107602207500c45411061b80164051607040103c81550700c4042161039114034906030901400d0104414001400c111200c1c0024698481030114210300c00740080441343c82c3c0045281b80c40085d401595083c812200c1c280304142030078cc0034007260030580c0d03001d10071f84682007040414184440c0c03070038201014130105100c1c0c0244070542010300f03441949180c2c0003159091a50501d0300d01026480845801244064040c1c465900c4071031410002c540a0003513a9070304d45031803d0031002070060350002820f40c0000140001d03c10f9054000c0d030f010401c03c60701002565602c0e1820740c1142d0b221481d03017 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 751174136 1250 751172886 751172909
    0xb0a0b03060709141002011e090614010b120711030f04051e0102030d0213091a101e05090316030f0b010e0f07030e0717100e01060f0512071e06021501 66
    0x10349410320800d081d14054946c000404c078941c2a040642d2207442c21400103007a40e6985c0c3c5000117209060146008459130a1465040c1d941041100079203881600601012580458041548503120701100049944200c0c00c0c1d80d2a00000115a001c65015104031445145000050b5800e900e0464003c03280340e005800861a1020300d8001ea40650041501d0340c007209500800005e400e4082c0c0500380c0040c01603201c2168a44c0c0d1100cc104550172400743c00c0b410040d0410212520050bd50108441c1d1061801c0c095114414100000e1a02d41080000c001c4020111000010005d4060411150034864104200180e8030384413480504002158103400240c3d14801107140c1c1402035001351500040d1600b910045500d60380e8800020508501642280d8000ca10300601282144210144a1022002486403628000341d186501046005551268042c80c0b0100750324078080002c0d00c020904680c400010321540002c58104618510418025006c3c4040c0030310320300c2c0e507004a6410b0764804c4004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 751175386 1250 751174136 751174169
    0x30c14060306010c030903050a080a030524011103090d11011e020c15070c0609060e0406050a0501082a0403020909010509120c0f1f06050118030318030b0a0b03060709 73
    0x454598001079021750034003000740408400f040c4140425402c840c0118040c0d035039410345070001000c03200010004848031107000201203540301da1040781c2003880400d10b0860303010a00303076100904600c5010041540417490058000070081407500711105a40240c07101d4095182aa40c12a01001030400900041e04071541313020301803400756148625541020007842c1000c20b80c2c0e80303015010b0203c1d00480d01183d02c45108210309a40010364203c1c540d020380b002d020306442d02000c03c5030001180211418018844000348400c000c117040d05082d01542e1b840c1115040180062810507405400b040c0e0090b400c030340002d0b444100501480740101c288100800c1c00c1b25a62200c900c040c3c00205160b2010301401d124080c0741c100400a409003114907a2401642d0040c01d81c14108035405580841c0c14000b001040703611112402981d401125007504000101e17258801c000b00c5214001c0d0002004c01802005012020390150f008440b640741c00d03801c40303425880c0c65400b0b68045a452040d4030408190080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 751176636 1250 751175386 751175389
    0xc0506030403050d0f0f02120f1f09050c0705070b070b0f1314120c070f12120c080f030a1a03060907050d0204060911070615050a06050a0c060f06030c14060306 70
    0xb1081030300a03d8440006e10b030107600301c60f6080e40d00c242e460001c01c0100c0030a00008c2d07090341c181143c100c0820032150054010b000300d002600f00151241c131099070342d600c0c0081c030110700b030030101c40c9500e5004066a100d40d0b100c84d40c0041079041010141d81102c401c000103040c906d0b20301c0c44c0724015050320b061003100000c0c59035040e8103001e0220289480b03005141d80380d850505a00094a13000d98824054001c5504081800020050342d9110a5405030481481c0700400e5030703007403017108040c0c00b0724240c0c1344500541001000761003407444200302e10703e002040000549407079008401030300219040e4610030160004041d91341c072040d0340481c07960700048800c102034038142c020451040e201801c04200c540e0b60f90388107030842d0080e0f002d000340d40f48006022801c0017031900c01c40c42120348852100711501d0410022075100340031f41c0106418800001404c4200341d0207424100d803026844001401081819494000a0002c0344001c0f269a4002500810410703400d12058030341c110090085801c40d680e100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 751177886 1250 751176636 751176641
    0x40c0509070c241b1713080d0c02010b0a0f0b0a12052e03051504030507060516110111070201080613050f040b06191a250c0506030403050d 61
    0x20000c0c4244812100781c2000503c00707a164200001040401190403045405403500781e4400c203100c00c01d08440050485180b9421050f02c100340c8190740c0714002c0550360969070b0341c01e91081801c01752510001007005020b41d98590040101c18130164000d00c06d44041d0014010544030b01d000d054140031400c04207100c0c04508901801103007490f4505010198060050007003140c10649821144040d00b4041e240115030405c9034260812001941c0c8240d940746846031612518004201a80c01000301c0100d030a0600c164251052160415000c00c454100448600200c1007079444020210350540c4a01208000621401ca038049201e0155440c06116900440d1070034801092980c0c005888a06880d100d030141c814680701d40545d8000003914146824000380d1444006c050500c078202c1250b011102082c40703400c41045806e0a0741d00f048800b80c030f03140040a4064855480c500c074001c2d14a900c032846601005c0300349240145488000e158803030041c4041c1d88021100900402c108001805541c0800d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 751179136 1250 751177886 751177891
    0x150e13060e061306020f0706060e04031b08030a020318010c0c0b010b04141005070f080d050c040503030a0810150e04050c04080d0f05070b07030203060a081b0d110612041208040c0509 80
    0x46d039000303241101d19503860040f501603400c8440800c94100400c41019001109071000364080002800d0084003a42c400d0058880108180c1c0025008004034500c108120303c0d04542d0390501000348580f605001001b0141d51a803507040d02c82000c8040009480d42c1101c0494054900140007100103500140c18001d9031180240d80a04102c81044050702040c15890118449403040d020155909508116041614801350034078549070010030003004103560001c01c030f40e42200142008603696491000b007280340805d90b48440070b0011092415180260300c888405c0144600301c0301080030740c803804200341040c00395014040b0340d82c0c0000d4100d51414000c400300c00c030441b054981949040400d03510840c0907101501d00c003001c20380200500080380b40c1420410094840500141640649041020981c0170604003030b0340170b00402d0350650309000982070b0b883c101c048007410701c6940e155001d600248000042720b0a80c0e107559540010034560b80304d00d885502840e0040704100c20385040208000c03078050301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751180386 1250 751179136 751179157
    0x204090809040212070e01090608041e06051512070e010611030f0f0a0e032808070c060206100602010b03060f0702010e06010b0c0106081f150e13060e06130602 70
    0x5101840c11030761103000030114408400ba040c4d1103801c08120103842d21103401e1803070741072000c000c0b01803140170750000c20036610039000040c0743e03462240c510740e01000240040c0c01400c158100410440204035140640718403040075141a401203010882e040e46070343c13940c0101e401880001c8010000244501c01d8201420301e82410341e441e000002130340851039070180281d040b8000000c68910001c90300f0001c0c4c00c00c2e07000c09801809070f169515400c049448600390704e0402c0080c4000c106014000300c8010b0b07030010323580a44145c81141c6c4480c07019540b030604a881d8440d0101110002c83c04c1481030090914981015008000e03e03250140400604000200048110743d6079010107810a2403c01c0460300070304541d99403c1e50ba100000091303080d00c406401c030f10800d07030118800121982c5004600c01c181261000002004c9400780c0c18586110b44507440540e07040c03040c109011850840c681c282181c10301c592804c00400b00b6030520a903e98000711020199021055490004a0340640040200d60384 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751181636 1250 751180386 751180403
    0x90304090c02030d0603030201090b0606070507061b050307061d0712080d0b0d0308060a09020a0203030c0901090b0d0623030d080a1d06010806010503030301081f0b040e01200313020409 81
    0x3004851802205c83c0d9030300580060313450380408810320101200301c58001c0d00554100780391102c00d858481d90341b04188105810890000e5100d01c0b00390207007095891440c2c1c0401900e541c1d8415081034405807010600c0c0d8440d08004080301401454009840d2003101c4000d0025070b0480444d4981a181d0f81001062410050315841c003800c0c3c941e10320150001e803e202e501c40c0401c508000080c40b4400400fa009060880c3c41007205480203a0000b003603e03803106040c20b4550b56515520300403960700480340d20540942c2808100040c3e00c04d000d8200d1001d586000300c0321650403031017903141c00f0b90007010890250150000060ac0042da44101c0e9880d42c004155000890f2864482c1102c03010003d100c0340344641604a600148029a1f00f8000a0300400f0110015411941400f40d00c0b6210203401c4403840382c66401c40c02101c188146900410035031900100100105150b21000d140a002600070158000d444640940403a403584070a5901402d00408003a00400184d428000101881c420035669a403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751182886 1250 751181636 751181647
    0x60f020d050319020d020c0c0604080c0d050a050616030b0301050f070804060b0a08010f05061e010c05070e01060504031a01030312090614041109011203082205010e031908090304090c0203 82
    0x30f2081c00100b00c65403d5190059880c82191101401c20500d680d903a40b00d4101004100120240051200700e50801180d010100c89213a18102d89400c402180003803050254600b000049800000248079080b210340301440b5852004003054201c0300120f900b03102d801d1401020aa050384611081d0307a205128120015010144000183c2c2101c05c1d90301c030300d8144c0c0d140c0c05c9411101e26a07000301c6070407031000c0ea42c0840b0100c0035641c0c0428400340340f00c0103040040c62a031910030f12400300304030f00c0144107070040074020b96110b00c00141551b01901003990140c0003110520b09401d00c0c076185030304a0b42c00d0354810003021080c007402c03000f414482c4415502e003502c0f44550034042d01450303031407030003140325664050100d6201001d010b014101648102140c608441c42000440c0c2c1003801c0552007800c4404a1070094910078950f10740c1d0300000e00c090f02c52b40c40e0800e0305d144080e00000614070740c4009158400440d0610000b10784003c0300301c900001d550800e001c100016141130700804001c4426005813420038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751184136 1250 751182886 751182931
    0xd030e0c04090c090605030705060406180e070f270302150405060f09031e12070c17010f05010b09150c1e0a0605070e0612060a090f020c07060f020d0503 67
    0x1500e07038500903034280340384160401c2040154485c40780281016005000428588400520103014510034070f000d10203500020b102c905503002c504409010844410b0342c09080a80000707100300b044113415008a00403510520b08800e00381a0014503862a5981d050300078115400c0c48405403c903840809000c06c1803002082ca84c0d11003010f0245c0f001c07020306203612070600604051034640c0c0c1900c094039814000c104e80602031340200e5514200c000665600380e4500240c0b074800c4102e0100e504c061b03000c0d000d06540d00390204040d000141072251384402440140d80301c8031311070014864000540e074015229032a4031a01403600010f826400b04441c20745000807900d02c60252035405900c50b0540a030840142072041002d030744201500000c00349041c0c24881490070115409104215103c244911034100080c0b00f0768071800c0780c00140105000500000c20ba4548184c00f0350080c0d20300b4040c0c0d018880c804600d080c0725425000e2810900e60003801c01c1100448103030340e40e03031001d090344644812111207172180 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751185386 1250 751184136 751184141
    0x1512050730063b0c0403080702030c090f0a14060d0b0415020a05190807090311030109140309010305010e101e050a30023601170d0206090d030e0c04 65
    0x1851402920448118a542d03c3d160f00390302c068204104611141080c000d452400c50150340980e070b0f00c815859698a00e0f400000d1406102001e01684118510200203040740016110f6001380e404031424450b00150044404c00468100c2e98990040801d00c1c215022404224840e50018011002381080c1700a881e207800503a48004907002c04284000303140d036003603000340305442c611344864902240c4500b0441401418540c0c1c0c1d2201400703c0010201d4050250303002e600150005d07030701c20514100c442d0011800754480c0c00581c2e00601082c5031000001d400304030204100e10940141d049000f505041409042c1e000020725405e0f4035181281070080341c1c0f40c80b0380358898040c00e5501c241404071107400c07000b2003100d40c600d14640c03850011080c41e0401a00c540e0514480c48000c44400d08039500750300c00b0200c0c13007041032240c2d074002c0c0c1e40100002441e020700784180d46090960410f03120340c08601501a03075120700a4402802d0b5501c50401c100c2e07001e10a81c444907100380c03100203444064180c50002002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751186636 1250 751185386 751185419
    0x6010f0c021e0111060106050403030c11181602073c090501181b0302090102010b040216050c06030403171005041e0c03060b0d0213151205073006 64
    0x403003440c403001c22182503801030071349039010b6607140017400c042d818160000d000780030344e10005042c01a40101c410411051a4600e15603000190000810300c3e44c0c200920300c540400e07500b0585182c40c2061101d001e40c03000c102c42d400e0302c0c180000e213410812030307a46548500342404004401080d0b01e1070445a80000355418200801c02c05201103a1541880240a4001801c46400b903020b49009501020a403020908000b0038400e8200141c5840100340140c2c094000c80d1071903540244001850150100441c007002030203401a4102e40030321089005104042c48140e4001e0045001a16100608031040000a90025203015141246950380c03000c00c0c1911020000a01402884103802c44210940d108407440f400341c511382804481d2818200e25840d119038996004d141b600003542e220014407111030f001c010054000464500060704d039004044040190b070500619090001141c0003034898000c4156809c000050740100c014825601c0c8910260200e44c0805d05803035802c001139005c43d0042e9882d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751187886 1250 751186636 751186669
    0x71406070e151c02190e0109060c03080f0a11070c030606080102120c0c01090213050a0b062110051210140114040e1609091b0806010e0c040b04060905090f040b06010f0c02 75
    0x346e262200c0e100141001503140c0122003000301032403522012070b900c071320000d410145002c200c8220f6151a54400f0240001080c404100720300041c4c0380c1c0811190f22651011640114801c1240c6911044454280e106a0041d0390000f2209800b144040c000b0300c0080200c10f54a0000060001143e4045050850310042c030a001c1643d81d0100012020f250061002160b8100c4d1600e1514204140c42c6210706002801a00c1510018001403140002d0300400c10152000034402030b002e15a4581c00d035600d8a8044121000c80d081c503080644590201814505a5400401e03143c01a51004140401020710401c410740d144590482c951010032404103600c003900c615030300480c3c20000c034104901c60700d4950010040c0060f0040003000070714030201d401d9042d070b400301c0326910003503d03940100c0445001d25041084950302c00940000c12581045200702155400c2e05c400200703546240300e2070f448000c219409070100680c407000401070742c400d109485080035035040602e5440c2158001c07070022501030000c413 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751189136 1250 751187886 751187897
    0x160e042414061003060503121e030a020a1b020f090903070f080408010c053a11120a09030f21021206012a0b0c071406070e151c0219 58
    0x102e1401c025030304080c401000d040034050745141101003603031a03e00d83c4a056a1500110343e0309924803511440c1000d4240c0c1d021010b499081c50000a0001c1d0b011401e200c01040b1001c107503080b0031505a1549400c2a0018581d2001e40c0c03244091201030f1800074612019400f0400040d00000c1c0c243c00c210240074000c0003c148c680d418507106e1400c440c060f401080500c101800015118034074034410182c5510840f03150b00c2c0641d81500d802c02c4600388800784800050921401c17a000c40301c05000b07051620107900c00301d8003540340e0840b490b0032141d4021000d0001104030b0b0340902524001c01e00e00101c5e61a80c0c240081c408260341d134010882c1c0100b1040190345140308103000c003039079000040343c0e41d401c5564142c1801140f007081e800c3c02030181507002040c180d04000082d44140c041815910400d40001c507035044034103c080003d441c5e400486890002c141c0303220109490342031004075060241c2c1c80c0c600c0f031450074000941142071842001d0749500d8880c2c0800412001d2440d00ba0300101e04030313654540c1c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751190386 1250 751189136 751189141
    0x24070302090909010c02100213090f0209130203100f08030703030c02160906080c0105030f040f0201021005070e031002041a0f04080304030c030b130f060221070c0302160e042414 78
    0xb41007c070a604d05880180c018001c01340c102c56120380b035104403852040009901c0d0313400c0808801038000c004035a03600280d040406030116005800452003814440305414420780c481050403034000b450b020700165a0300c140202000a4085da01c02c20400440d401160f62058158180321100b03469500305514042c3c0700c03e020840e145041080756101802424028114906503070290901d0704010030290403480f03070380508400c0da4001c0c00030710030b1540515004d000c0c91400c50409001d000003d42458064481d2001c0c00d03d039540e1520a49040d2950304e55403500140b81c0c40b103818003a4000c04040e805601c000c000c001030180c000c0004200035803185c9440c110703030362442c03c000301c038440c0040802c0180c08802d180c0c20005610000901030031680403400507100c202c883d42100b58000e1000c1a1044200500280000103801600c19140e5901ca5421200314070301008240c0c11301d100b148136000090700e13010003140c0050012a8003540041d0f20300800c1c0a009100e01250f000d82c0c040041d8035806600107000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751191636 1250 751190386 751190411
    0x207050f0309010f080403050409060e0405060601030e030a030c05130e160504122406062106030218130b2505120601080a090b04060c112407030209090901 68
    0x40c04840002550295080000c100e00280801c1c00b8421404200902040040c04060051060741d004c0d00755514204481512901041199901030380d0958580c4500c6000403210340c4680a60200058000c1c00303181052402070040d4080e1084003090303000d0000502941c801585200300c0c000040030003002824aa04009100e00b0b00300c0d1949035480304100c4100018000200c0808000c10300e030380c0c440c846642d1107a00c00d6a5010360100b4140076a80c942c100320300055150b81c000d20100004010403401400099841010400c0b10070300e11009401201d5200c86182d5040b10310000d0b40d000110086c406844080b81c0d961422000741240c0c0507004101c0180c2c1c054501c41c03003080c603200b08546410420b02d8180b14083d8907500e0080100014104428207000820102c2d860b00310780c0e40241d0215494074181005d1a2200140000200e0000000c41110f00940561000500c8190300c0c402c0410801e091381600003079500c0560000e01c00300c01d040e000c03c08d603c110b481d40303290b042c0314481c89800018560703c802c5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751192886 1250 751191636 751191643
    0xe0d0605040605160c1e080c06070f0504030203060604050901230702060601031e05070207050301112d0d05040305121e0c09060f1b01110d0f140a02070f0b0a020705 72
    0x107000390701c841c211320741d058586500092459410b070303040b034000b4100c0200d0b41c40380d41d03c0c000c030003a00510b00540407a2401c40500d0014200e8059404d40e12030740120040c0000440341e90066100280d03140d0f106030003041540c01d01c0d40c00203410030000e60020569400c1080303400740e03000d8050030045031350000004004d4403903410710441c0d030407000919003404111503c9803545024402140350901840d40c82000c280814001c2050f0401808064000d10000d140c805803260160417550020b0004101403a20305005125082c00011030080c0307000f0103050000c0d140f60800208001042101804010845014108072040c0c3c03141c420030f00003600401c2142480b501480054010f8605500d1039000c2c8940601e96946006441c041d6440f003801075181e01c0d001030784041101c1c55091205107946041a03850100400000409074007040c0e03101408103c040080c3c0d00304484000403c030210f1080034001c1a03910311079400916880d4050343d80c4504016032520744041c03d12050381c00391502640001c00e9010000d050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751194136 1250 751192886 751192891
    0x3070b090d1205060d060b031f0c0e1819060801021611010e01020c1002120a08040311070501210209040e06100e06151b0703051b031605100e0d0605040605 68
    0x2c0c0002d0095040c003c2c0410140200040020051504d40011000e40d4500b0040039000384800045c2c000e10702a1508242d000f428090203000c001403480300d0003006030400e20f0a203501190000b000e880e4a54818820710300a0f014000c00c0704075140c07610b03400030f200c08090000d450245d0540d800c101600c0d0540c0352002d600002494880e040c8144010780701d030720b07a0700403d02c101c0800041d1a081503000900004901b08441c0030102117441c080031a910075107950140480c0d00c00c40c800c0d120652043d40200c02242c1c8c4101e50b00c01c0a000880404c1011201a041d100c03001508521a4000d42411040c800003000da80031400c0005441e801701d4204040e040135828054000d0101c02a00582402d0050204601140050b03042000003000a1021115458000340000100d5500c042d95040b17502c034540715881c0d62408100e80240c103040c04040f9068540440d03c40e050400720490000d40ba0302c0c0c1028007130180c140345490302c103000501105034242e4440d034649102d150b00c649000910f6150503d0b1100480b1000b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751195386 1250 751194136 751194167
    0x6081c0e0a170c102303070309050609010e0705010215160c0602160209150f040b120a050307031205060f21070603020715050c0d09111201150812041703070b090d 71
    0x20ba041c2030b40c04014020f007121700110035160541d0341e41c2ca404041d000381440c480d000303101c2d108060401034000c4040d03100d101c0c031101a5050383c4425035903200490b603038084160790094015914010417140c0302c0780c1d05151583d0b02c035804c0410b1244000d8541c8d6003240c122000401d819502035507000c0852130207542190b4800102d141e40c0790f01582840204101340c242c1d40015000319a220410345166596200e00c100d18080d0a08940d070207101c0f450b1082c5c60341c00c0440101c1c0896090704c8100744400c280c4c042d040c40b602005d0305440011410000300038160210f40443c01c041c0c2e001003840d00c001d02c0b0a000c0c40c4064403460303c0160b6121510300e800310001038000c0800b205146071405000c1a9580c1504442e1410aa2080415925030074109181e1004040d078000c2c0d480010301e4204144000c040d04004401c0c40f1209000c15560342e01c14140b51100101d000d48600070f0420481403020400c0815100761514400044030304207603a960710909100c106942005507640020310250940703a0144164466111 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751196636 1250 751195386 751195397
    0x90503030f0f03040c0504110a021504020d081303080d0b1c02030607110712030e0102060a060305030901140405120c03060703020f03040b0a09050a030305060406081c0e0a170c10 78
    0x581070011158090038007110103049001001c903040c065100e9000d000b40c507006100304281c840d0250b421941e03070b20a003411070160040000390500c2250719440a0b1140383c008e17144410042c425580c030051070b0722521100c03840300201440440418101c1003d00010041c0c60380026919088004201e0460045010302d10740407011540c4100580b80804c20031b4000486040c01c8034280141505036082c280282c120701110600f288802c400d1540c00750004c45442e4080c0c00b41e607665110a0240402d8899034007010301990b104114441d0a5403103220807000082d01c8455090400d500c0d0400243d40400c10410b480345a80540123044052030148001e03500710559040440c6000c1440d4607030702e040d010040002e081c442c0300c000000e03c0f400d85904150300c1e03035038444141c0300005401d140c00340081c00c06a8400e402103180030000301d000c4600044000f0041e0088014400c40f00c08080200c65208801208603000007189400048003000000d00244440c0c1c000050305082010105001c00d11030a185040c04000c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751197886 1250 751196636 751196647
    0x102030108070e09150907090b030303070c1106040806182a0d08070510051b040612020d11030115031a18150d05031c0203040209070f0c170a09050303 66
    0x24002208000c03120f1400c4507807102c2c0e07948545203041001c0f15418241d200c000c078081000000c4080b86040c242e40840d00b00300422910707c018142d40340400c40d0110b0101c1c03c082d1401c008030b0315a03101b03034514801c010102d40c50543c4519015041141c06c1e1803000381000000c000560308a014040b088003000703071403da40c001d40340401c03d441000746007950b068060000d1401d00418444410f0032240025000300482d441c40c03054484c21001484104c1d0b29120502d00400e107041030000c00c3e400c032001c447e255518000500303140c031701c0e1400a6000488060300ca56661104c100188030650140d030080005520134403c0481c060b0010b01661228500284000c0030206043d90303558030300030a10f8061121011143c03240e5a1044c0081c0410700740e03141c0caa031007000c04110700100070b4000300a20018640054a07040802010600416400180c0340254801482000a00113a01c101c3e41400c3d001041d1408a800c1059911461001e0640149080900c0c1c000141c491040f608111080c008002c11340041d441d05 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751199136 1250 751197886 751197899
    0xd020a020120120c030c0f0c06121302090108030a0215062d04060f05012a080d02120a06030210141806042103020709050105090402040e030d140907050301020301 71
    0x42015000200d01265045885050603100700100750f48032850500b0b00f580c0c0c262000030a5500c1d00940c2030381d4054424000341c00d0382a100811000010400900001c0c2080c000e50000962403100400c1c00700e02182070004a000360761807000c41402080032002440c2d685600c072100030b0616252240c80c02e032414461050240540300e1050b100031000d01c950601518002080b540609080c0a26855500c18100040414901c00140c0010b00f1070340241ca44488000c0418121641d03008061007002e07aa08100c1c0c503c00101e1995030042c001100c12201c010300c3d0501c0705020103c889000e58100b43d8643d550300041c011070030b101e2840030750000f00f0306001418131415a000600307441855009601002d85011f00c54454442da41660040c00201681c0492680b6030801d07102038002407101580140701d601000100100c043c070401d41a1100902201d070140d441e602404040c1c038000c100c0407000c1c4420840751244054520510b9058407001c2d140d0b81c3c582c1481c1800d01d1802c10250440d501c40d910400040050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751200386 1250 751199136 751199147
    0x803010608090705130e190b01090c03050108030a03090f0f0b1e060906271602071a0a05130b130e090f10090f08030f0a1b0206130c180e0d020a0201 65
    0x141003001101081020410039054100b50410f80d4004d007c101c0c14000d50208508105c1d1079040e50a0315004001c0781019500840c1690001e10a00c07455400c104540c0100d82c0c426049440040d0140300340c03180020b12035507400d04040e04160251081c07140da0041c003500c4070341000d69142c020040703040034000381030400010303503200c5c005481c05200b104412409c400d20b5000421040180d0104172007408a40350410031300010f105102d213200010b004420000c50055003400080d82c907201d80648a030304200c0c00800540301944145a2150011124400011500c007070000801b5292203000284540a240280c0c903070050721702400600c1c01d0b4100340c040c0d00b250b980010300600c3c0b01e00846400b0076421000c0c01d0603843d0300480000a85402000400c125100e850303080801d00401031403000b00560740ca80c814042c11645240c00341030040e0400340c04075004c0c412019003040f0301c50140e0120791b8015500e81c007480c0309a280d070b100c0202d10381e142d51044800c00410702c5045101070340d60000d01020900e65000821 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751201636 1250 751200386 751200409
    0xf1009110d021810080d03050f0702011503030309062a090b0a1d0f100801140907050f0912100f0515180901020f120414070807140301090f0803010608090705 69
    0x742203d14000100380d5201c05894000508400041d038591010310200140904000c40f0504810a9032030040f0303c0350380c414401d02c02c1e1032800c005080300c0e490440d0b500300c1c05049113200540340c00743c4984002c152283c0e005501102a16003034018a074031202004040c0290f4160341c8101c40c580300500500c091603800c441504114488414200103000d6420300044554011080b1182c0210010a0f4880f80fa5002100d5905860041d4800b000c2c5210901c10000d001100b150340f00001030050081202c071a0110005c0d1041d05d01c01440084205012a05d05180009404441701d245446030510b030284c0800d0720505821101e1900f0700300d02c8921100c0420039261074100c03503c02c01c041c000005000780b002036040d074080d07141c90003506030f60f4410700440c0b01c41040250b4040c0c45c1010131030b103180c1402000061400494102d080a8182036291024815565000a441c980c0554070742ea899400211510a0881150301c2040d00c1c5480c0c2d410201d00600c1140001c00c614060340c0002c0060000d0380d200e00040c0d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751202886 1250 751201636 751201669
    0x5090f0624040b1c020a031d0102030603030a0c02030f0d081911040b0f160b06010e01030209030618030d1407020c0d0b04021005121627050607050f1009110d02 70
    0x240c2d500c14070285441c0c0e0b410182e1361a80303210304c0420b11100c1c07146e06070045c81d07544036000d09100b18243c00c8a10f81d401c0703200c2582c4081c3e060b441003101c403c0300340c0100c6440210f0f500003000d0301d0a1804003188541018040c03101880000e0302c4504200d540c007544a840104c4800c104000c019100800401051034417660041c07880f05400130408504440c030b000c04941e1910441d4130b0f0307210007260fa80f818840f10101502c0d03a6010405d10448248554400d2080d1101070f28010300074009510b5100300407002c41450944030101d03010400c0050104940b502401960f203c500c054501149004000281494255100d440c03142d2003111300000070a0188091070f41250301220b11003108180391400341e445116100840c24100c11400c00c100b00d91130b11280c100ca0b003003441e8440d2203404041410041112100044540f491200070341e0500807420100003030714815104004580c1c80305a039070740c610314009041d172030325140321344a41c0f10700200306451984501204058a00030242c41c042d40c009003c03003c41c0c28894 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751204136 1250 751202886 751202909
    0x50d030e1002154303060909020d060c0e0409080915030714160c170105070503100e0c0d02040807080709021c02090102100608010b01081003020d1b05090f062404 71
    0x241e0200f00340398120a4030324902440078904031804d44142a011307038000142c0424902800010889018002c0c0c8144030360060072042c1c0821541c0d00d407001420b010a007441040441d90028402e82c80b01e116101015005141082c7c4520f0b0010030002c020720407161184400380706205100320b95170007c1c40741a24011169031240c0f1404840a5007462640a034400b5081d41d030401c0001640c8040e039070b02c075a42d02051074020301050343c1d080d009035070a103c140c9401124514840b402c004440001000542281c80e8241142c54280c0320361480080c2d801640000380141c100f00c8040018200400c0048002e1900307031000c0d420850450081c000001d440650005099000500204503038420300040740c01291103101040312b241c42d544c0c114020920b401072980412103060100c2c640e1180311201d50b00700d070350041004c1c9040016a480030500040c0903000040000b554802280ca42c2d02e415046100d000306411102d500c2c90aa0100180700000e0507010412210020b0034403041402c240807074040d189001c605 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751205386 1250 751204136 751204171
    0x306050c0c06061c05161509180f020708030a020a090e0f3409060e06130303031d03070b1905041a06010212041410050406120f06050d030e100215 64
    0x50340c021113000782c005201d4010140200a624190309015040d07400340302510050381d004e0031080c0c40114650144011480c00c1401030b0300740300c0c6641c01c2011449440c1c10098208000c44e680e130703602604160b40340360b02e00d0303008540c00440a9001c10107000802c0300103203025050514005000301c039800980114158403046c0c02280c009500d142c07082201c80c1c41c0303003880d0039203038810305004044580741e001e658002042c0007640300252134803505850400b550030711031840c454a1941c040e8014208403034000c105035441039040b40c02100600207800014018a0000d10920308030840858814900420590b841c0c03904080c0804070301c08000340d1b0b91842c030042c22040b081d114080140d14140003240c1d9a8003520340000d010690318030702e06501c4810f1030300f80d9148030b500603080025143d501543c0100d5001a48031803c0c800a0b01c856003004030280c10003030b000100d441c0c4400105044c3c02d8824020342c0032404804000b1900e04100282d42548403552003c2c21408407043c2c5101e16150000d030880c00701c018031244 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751206636 1250 751205386 751205419
    0x3060708240d080c06060f0d08030f1302030703060501060f05160b18030d0e10092d140115080105090c121914010f06050f1c020303130306050c0c0606 66
    0x1110240b29000041c031500c614038071030919035507281280d4142c001e840e0400b01d4006802d24001404c2840c1d840644e05066540b0744c225924006401400728029403201041403026031414402c000141d4040d10001c91551b04001c0080e01c0c018608400108000b0104030108400d01c0d8892011030003139100000c1d0f110754607601c0c2e2840c01e00942c5038a04402d0700002603075040c0c601d12580a14012242c41d0300707440b42c4040c8034070303100c040783c0003600d018100d8408908120b0305043d907101503043c0c41314018000d0883d1703203058a410748680e400001ca0b510036999000d002402403c1c150000d4000d04500000b80010720380f00182d640c40e900030801c03050060311007204800032800f0501000702c04603442814401800c00b13a0410300010525000b088040354070f08058201407a41900800d825154040c04840c01c140501c0284416060052440f500700d14417a9803030b200595080c0000d0031184002000200c1041c150704000b81100d50107440701290a40070041625007034400b0400c2c2e03501003004c6030112038510f040c50 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751207886 1250 751206636 751206649
    0xf0703120510080c030a020f0d14010f050703180312020a030b0402131a070b07050c0f0706031e02070b010b090a0f0b18191e080712020306070824 64
    0x4100304840e4180000c01c000382c20342a44003412941018100c80070064031006060701c524107002e000c0d4202200300058040c03410324101801103d4840d101c01c4071741840840d409130868500041105d440d584450a20101071b516005500e200c400c401480c28212000d40c4c2d01030009840b03260204221038020440c400218001c0d0b00090030f00d28050000c0d50b80d002c850040328480502801800f44a0703903a9500d040007005001c055030041e42d441002203038103859041c0b09413010b4000807000c8a4600c40c84804111448060140c3d200a020a403004150220080099420201d00a41600b0801c1c030601c86030300850b003110b0110b41100e40e2981e200e81e4070f40c00000444c10500701508410810031085a0001d9200140c400804110280c200c1c0c1404c81100e1004225068a444080d4450500848014045003000c09150040c00031040c0e000034040f6074400101c6e081003010f0348180c0c1c800f00907102550540c1000e2002680c404050300c8d0441241c5800409c0f0f500300300c9400c11000b1144240b4003502d81e1902da9a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751209136 1250 751207886 751207907
    0x111611010917250b0301060516140f061308030f0c0403170306040501050405060f1002030c120c010f0b010c080d020f0412140118030c05070f03030809010501080c060f0703 75
    0x101140d0929072440c5105543d040c0942d2282c221041240c1d01802c0b000d00c800100e001e440500c041189183d10b015011200e503004413448000b010300401121000035a174400c600b46014060002d448034505c88480720f81041401072122040341d41c0c1c8040b4000082e1100d044135840510341071030709400c0c3c0360042101464005e0382c10040401c80c0c0385081c1e0503070102140240d4440c41c01150117103c542c0e200c02c01d110944406503001500b0030003030000203c0f00c2c507088410f19160307451407044a081c00d0f00f50f25400d180111801083c2981100001d0110303141c0001e001c0c0108080c2c0c100340c14007070760080d840003d0429100b0580540b0300130001c03d885010761503030340441c9c11150303074120150744507500d070b00b80140c2900b5054400c8808440843d100d04010300103000d0f00070f07048940840003482650644040e216070082071412038660207185c8006c50131080000520000e54002d6440d20301c0c40c03404800d81d6013182c9041e006544164812841c0030603580c0d03081d0495410380185104151107107a5454141e41c680c151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751210386 1250 751209136 751209149
    0x1b031201030803090c01140306010e0d0510020403110405011a160b3d0b07060f0c0507021201050c07061a03060a0f0c08190c020307050607050a031116110109 69
    0x1040000002d01c08600301941c0a4804141651140054540103440310541d10348242d0a440080c000030f603071507006030382d000f45604001d00b003040d604101c0c0d982d540c00c000d000c144980c0b001e5404102401446100074960342e40400580d401c110950400080c881040030000c0d0995680200058594868a0807001d00034410340c00b0904000c2e80c1002c20f2020141c441c00c000110441e0901810240100c0c1c9500d881a608800d441030186a9414188202442c2e840f11501303459603612440040c50385580380c4150f03030040f030703240d55115111810781c410408091308445d407d40c4940c0c184001c1c8803009000c1800c0740c410580c441c10020319413000c820b0700384403007041e1094542d141c00342d10204041d41002d034018041c1e40707980000070000700b0811074042e10140420b0765148108000c4804070101e42489038080c44541c40540102d9081c01c203166140d41c0303408002c840785800200041090b90384103402d030090740b06002d040d044040c01c10303d101e80c0280588c1c03d21400580340f076084000c24001039003ea0381940c0a0042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751211636 1250 751210386 751210417
    0x1b050904110d030c050610150c1211030408060a0609240b0d1b02161505030c1308030f180105040e070e1207030348020f120105061011031b03 62
    0x60004080c20950b03008d104943c00c03001c48020b18a00e651140c5441a50168400d0110b88610f01d558000c40b500788841c59161480e00c010000030078211401c10440340324000859010400b030f41070003444010340d1062650003218140344070501070381c41c082801c1c5a01b40c030b01c54411152682c4404e10301b50054804040321000d0034130042d44200d00c040c0c0c04940760384001c042e8000e002e14959100f441c132040c030030302d004800c001070028008609148140300c020a4102002c03c40c1006d51503c8201081c110ba02c074002400c5000d0b000a0050740a8449007841e1040540c01d081c11070403e1703d810141110048028030040401c1000403a600d0382c2c5c0e450460100c50740f940c3d0000c0b1030000341c607840c014044080d150341000c072410b0100c903a03070a80c1203030030100035007003400500c0041000e0040021403000003072090201c0e881101e17142d5100c1c040c0c50f1043e100082003500c10003c2054113041c82800392410500e0b611100f0041030380060380c0401000421500d13540c5180c00740c1008100704135101411409000c120030030b00380 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751212886 1250 751211636 751211641
    0x106030f0b090c0306101112030c040b030f0a0c08100b0d15090c03060905150d05030c0307061406010c0803012304050a06051f090605251b050904110d030c0506 70
    0x1905100507500c600000d83c0d044804c240c807481b09a800c4049454550005d900410120314981d40440207590062a4a080d02e410140c40748a510046d400842e00b61510740714002c100040c2c4210f5000d1082d01d00010300380302a42d400c0a682401d508000350103002116000000c107111001c142d50300281514040020b8101c04a4855031008060000c01072138400080c200000400c0c40c2900d4031a960040032031070011508600500140603c8030f0040000b0780340d034003090280f0844e03401c080c070080c00010300c181400100b0355904a0340750b0410701c016010138108140e4201100020b8595001c070713070546100c05085000e0002084131140f030400e540302001c0d00541400140402d86006820010540b00f00700c481c8609100d903541c038041e408040901d10000035242e08420094a40504000d04295006100c1c1c80c40341c80d56a9445a02001c00c1281156075191041d403036103042c401a800c10f00038080440e01052141490740f500c0c1140b140c601c140070f21450051400c201058002c0c0c404028503a4098152007061 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751214136 1250 751212886 751212901
    0x20a031b261902010515030c0d02041e050c040f060f0903030e040605030703151b0c0605060111030a0207090f090c05060a02070f1203020111070305030a200d020d15050102060106030f0b09 82
    0x2d05041d6403003540011a198001b1442c07601141d29850104042c01c406041e030000d408100280c81842105a00d00c5540400358610b130046029a9100e40c02032130f29035549038034101d91296113070000d40c0807004004404400c0c81c4c20300c0c0c0c421100b0046a40526210a4015402e8005030007044a0340c4407039454403894400004200518408404240038500b04001c8030442c01070041c40d01491809000008190780703009400120346510460b000311043c5441500c0581a601d401c2c50755000390b0041c5c02580c0005401c209001140c085c034a00e480300c280c014400c9052959502500a10b00e026030fa204480128569030000d100308103e000801b2041a00350810b961145003107003901d508482a0019400c01514109002c103890854014075850307564140b4554850504500074083d6a800800c001840e2802c0e400b505923980190003580748403035005075204e82000c0034600f101c0c1120b0711281c031020000b4007044544c0c0c001c202181103550500700070802629880d025002000a15601a40420f1460611414 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751215386 1250 751214136 751214141
    0x91b060f0c02220e011a06030c0c0a0b01090902090709050604062a030f020606090403080103110f04110408071409181f0f0f141b0c070303020a031b26190201 69
    0x5484c032440200502041124003905403070807010481d4120004101244803552414001c02e11b000d40300c02603404207a031950391403c4a0f002a40078880641d1524a0b80d810351510000c040d402c40107500341841d450b480c10010400600540c4a0501441460b05903007004120814074420aa84001c1a2900740c0642d8a40980810328020940005210b10310004401d41000d085040c010781e05500d5142c500da18554580804d42140b0042d2508015140c01805403502c1e24051040d009481d00c0c1c0b0103031140d0038080700600e0800141d222134207101c04405c0806903519038070b001301e400c80304900310382201d5944003010500e42140400b1030f600e080041d000408202d14594040074044840050501642c2c040c42c1000e02510440c440010380c420181c40824007a4440d11804000c0300303c8031441d607003030a0b11000400d0401081d42c0c41900541c0004507903408040d03014840605041448000001e20f001940340c840c0c0905075a045d284010203030040011280c02810181c94174551428250301100420201c000d01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751216636 1250 751215386 751215401
    0x1902070606031b15020c060a0536091506070c030c0306050114060324010210050906010602010b030d02030d0902010519090e010501170606030c1b01091b060f0c0222 72
    0x54843c200e8401203129100302003200c4042415a00600451998038100403550744030880100520004118860f0410540c0041807190049192254660440b102411010220000200f441481041c1c20807400150340080b00b007084800399041602c4928514090000350050341000d8a03195900c0d400000300a070981105068035000c0300100b103451417040a02c410b0380810384d1140110100c6102912501c400e07045150040c000510498143c50301d400e02000860301c007a0381c1d501668100d84010710a41e90240140001c01105400034610355444242c000e440307019190311040741e16200c0e100c640a5a00c42c1c02518210b8400318000a50300102104c041c0402c4098072410202900a83c00044c0c40c0d8064002c0d0817074103600c4d40340c0b04030036610b820410409a000400745240500140440344203441171a01c5000c20b291007030300020b03c00304203080c4030300c0c0080d00209001d0759050240c4140001c40c0c1c400d0032060f190020b4201000d608401d0310005001d10f4956810850707265411914049989164020a8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751217886 1250 751216636 751216673
    0x90c030114070e0909070f03110f0123090301140726090a0308100b0a121512060203090c04050a0605120f2a030d080403180e190207060603 61
    0x4029441c05030100165441124400c2c0030030500c01d4540c0560400703039005a80002d80310155610759850705103400704065190816910600c84446404503400d040c090a0b00304402400e0000208261088036400c020000210552066010a00880c1031314250854104008041003d46643c80c1032000180245012003c65000c0c3c00c40f014007100919900d0911406410510040c100c40d8110f52015945810081d05441c0b6044061030009508440346000c0e105039082a80c0c1e0608004140c19000e041c0d45101407a60310400182c1c900b00b221400340c0100f190341030381c000c00242e100d07540c0d4540c150a22030801c90140c2c015040c001042aa4402d03540900c040e5031088610160600542c4004c543c0c500c01c10000000b90b6103c0a9410040d410076201c0030208204a49400e13070594228001ca400c108045c6444404941c0d82d10602080540091201e8080c42c0f0424204801e5490511041c0c42d24901a0800b04100c00701d542c0f151840c401c0c0d0301105c89442d000320341440396070b0381c0c0c1c58041d201240702070194 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751219136 1250 751217886 751217891
    0x703020a0b0a09121713020102120d1b020d0c0b0c1326010908090d0827010e0303090f150f030c0307111605150d1401090c1112130e090c0301 62
    0x90300668081d100d05e1040e2210040317031824640c3c607210020303141c030001d500603819031003920706188850a219009204004020b00d002c1000700345030102808815103410801c0540d0403040b40040706c158003091b42041d00c3d41103d17400f190790300d07121004c2d8118800c801e0b0350b8500040d100c1c40420f5032000e6103441101340e1380d01104d803007456100d80020350032503a1001c0024040c08041048040b189400e202005000d801140014581100321071241200350303d40c412006210072a4411111668204000a0300003405030b018514009289c40002d00c918204424903105425401814009149482c1520f107100b066911840c0d99082420000c1e8068004907500c1d0300042c0b013041110f840d96804102c1e002050788003550346071040d040c141040401064600e0108800300e0501001e20714034814041d281c91802c070b0091090041d41042c80341c9040d26840c50b00403003404001881900b1007040064018407401100e070744203440d410080c20840030ac4d11250b101500280d1141c0610561100200d0030000141c4114004c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751220386 1250 751219136 751219163
    0x10815181b19120b0604061503050601021504150507020f0f070e22060f0209040204090b090601030213050607060914101a0f010c021827031305060703020a0b0a09 71
    0x2078031040b0410340034094410206080140c0041c01c0b141445410801c020310100d20261241c0040d81c2103e401c0348407200294441c402d002c80c95070184980190b0384050a83d074051407a20f0344503807601088614481c10410354510014520078070901000001700d20700415148040e0070b000c0740941e80d4646000e140d0203c1114404140b50540140c40c1c4c0780ca0040400030941e20310419103400c0010484001421a92502048000c140303a0740ca10040002e46000b0000050009110381030185007440206851705042c070401210b049842c00701c00341411602d04440d05a0b541c540303031500801030071103800000c201d07440e0b0768961036400c08081045829015112000c10200032803030303114094116584840b6410588825440301a54441c101c24035106001420103048030300c0d1000720006420040700c03803051100c1c200070400c1143e0100784000c0c2055a446008600700303488603040c55508c150a00c58544920000140003013010b000b03003d5032245980002ca40070b198038081d0703901006402910300459001105000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751221636 1250 751220386 751220419
    0x1020c0114040f2405011203030b0d020306010923071e090509060603061903030201020306130522020a03240c0f02060402190b071118010815181b 64
    0x75002d201ea070300400f00145074200340e160000c81c180c006a144004400b5207001019210761802002d0090024500f40030048995080c000c04980042d218144940540b04403c00542e07000034505054a0041a000031251121100e0700344942030021039441c0c04071028100300d0070603040700080d5410030740784503a1003c11305100c034102c540190a0242c01c2d40071403a000881c02c0f50a010b400f842d404140600324120003030a11504042038005940101c00607900081041058100b50400184504454600340154140100b2050854051200329048008031905002c1590b0b1340d075030050010364009140807d152a81c03625800c1040341c005860090744d00348442400c0031840b4070b0301c80958001980c041c0500703440e0b590801030121241ca4505c0840c0d140f5940100c1e404026a00402601e07219200c031080c43c282403014082c0310584400104845105100100550480460030300031100c44240d24030700c180c0d2221840d0040b03020460a00c140361181032048406521481584020504100d41c1044007804290 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751222886 1250 751221636 751221671
    0x306010506030c030703020f0403080c0d090603060b0d0506040b0924090702031b1f0213080c03030a050a032306010206160c0f05011407090e0109090b060108040501060807060201020c01 81
    0x111620000310081000820b079920990207408e003590800b10030b80c030b0b0907582d8642d103013a501719904502103500099145e0b8459500404454000d1145e402e0a1010710319005081c944c500410789a5140f483c1c440e000107801e03079610380c0600c198003401031002d0501d050400c0305035007075015080080700410300c0380030203805443d018070740030f20a2030258008c6140041c40d034103052000640d203180d404144a08501d844501040b81c0482d900c81d680314800684032041d4200080c044c5400d0f90103420a0340200c800b4642c141c4010003110014031b80b50407ca0765030000b0900440040c60418224440002e00c0741641480c6489a150940285002d030f007218125141d800d001038641c01d00e40c0804000c00c400301005d1000400c084944107425008000014911103800807021407020b045600344002141240e06000105510601c0c42c0501002501000b4204441d40c481544041c0903101c0c6040c0650100058100102500051b010f00300d0b9909540c00142e450030080c0c082e401c00d14a0700d44550800801d01030800310341 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751224136 1250 751222886 751222891
    0x4021903060e0c0315030703050f032205010816050c01021206131b180e070c05071502121b011a040b010c0510020703110718270209130f050c030601050603 68
    0xc003c0c1034510344480ca01038020341c412044158141c01003c1c00080811014410605402c0c12080619528410000420041440c1c118202040c2c89905c2c822711150340c1c401c0c200f0b680403e850401c1a1708da25420b10a43d994001c920760444030358000140d000d80300d04001d110901940c402d41e001141c5403200b0103804151542c0035045180c103041990040c82141c0300715075501464503070769030980c1030301d8403401e403803800141c200e60f07a101084040c01c080040010411218005100c0010400301d01040d46000a4590349166106d1003045808208104030022603012121402480b800030410070384581c0c3d06001c040784049a06220300d103404a4210694018035002c00c03841d0f800740281c00510040e5003418001d420610702501007150a03940440002c02c1044018050020ba02550300071481094040c0c041e600041e0380c101c441c0e603a1400e0011001015652003019550490b134403082981c8100c80c1d031054960300d19000d05885109100c0304103120011801501115080d819541030ba83c954040c08036030b1105 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751225386 1250 751224136 751224151
    0xc071404050a02072d080c0a1101050c030405010509060910080a11040612020d18211d0f040225020f090405280c1e17070605090a0504021903060e 64
    0x600801040c82d440241102d0361901d00d00d803150500081d95100d0046ea504a43c95070b0400e5170000c009030041c00781a440501845a092030728038a00186001d15036101d025034402c1038140a80070440000310750300d40c029141600340190801e41b909004540041c50340000b41d1305400f80c2031900c2c3c1c400044180c503108039015036030140c441d0040850304403a040c2c0294401c0d01d400c40d155645841180c502ea134040901c0e44040d01400a1800101d400500c1c030500400c0c032a2440c0903c41440a803d002d821801c40120315458129141c0200301440801b14002e4402d000300d403480100600780150901f140e402e400e01d2400c0c0240d610569032404001881189a0140c3c6c002d041a80049506551550900084809103000000c1c1031000741107580c42c180c03840130b0b40e0001c998002419040040103607001e4070784001004804115044000302005464880000b8048c201c100000002c2001054950f11451030040401820440d1b9030082c00440d0300c0c0d07035920810b01c1c000190421400042c40720402d0900381c002c13250b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751226636 1250 751225386 751225403
    0xb030703020d0f02060703020709180209061003060e2802040b070b0a0204030507170f0a080a1101111b060106020109030519230d111c0e030c071404050a0207 69
    0x199002c001d094554280d00301ca100100081140c016141d4030080c0c1101803194004044442c18982c01c00c0a442e15074034500560065114081d000d030360b507261181e0308540301340c42800c19100c01c000c00f01c000c0c04060304130101d045100800d02c91080700c4100ba080c40d0929440c070280300e10401c0d0302d6110aa110318414409054401e0007141c000c11500f1100b16048603510700010725299699840504220107030344401400d22824105035a101d40c1405000700704032a41c3c0140070300400d1750f500d40900d0300800f00e190317082017482d4002c0360501d0400d50100c0c690458202c40c641d111a00c0035120841d1120342210441c9a008080000070003c1c0140500203040e070f0303d80c039940d00b49074071802c01c03101d8000d40c00d01720010014074640c188815070b5240380e80383c02041009030080e41d9074410b08400c0203175160817031b5150341240d00b0083e1040521506201545004080742d0119213034411a03080352440c0205504c5021900811070000740c0314030840300d1039903c04c0e01135406010b2a60f805400c03000703e02600307802030031086 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751227886 1250 751226636 751226639
    0x9090b0a0213080609010c082a0a1206030503071419080a0302071a0105040b030a0b0a0504060b0907020a0b010509010506070f06020f0c070e251b12120c02010b0307 72
    0x31140e0040c102000c0b54a20380200559560356052800c201070b01c801c802a5501c18441c114a45d10030781c080d80c02040850b1040c1c4207001111030b40005642103418039056000070031801031841c405c07000f4003a40f07002c0c10010f221460312414500d8580e0310003a400c403420305000c80d01044461020036010241d002500424001074100e44509d011584405140010558200910320000d44507002c4520000362005000d0215810700003444100e0b1091440303a4841e6002041d8400087d2000d480030ba40000ba0b848046850344035880d040c0040e2040a01c00c80c0e00055050410503072650010356240e41c240a00d24501c2d43c1e903a071300103120751000e0038010707150020810801c10340401c403001082e2401c140b29000c010b10344110030340c0c004102d401000c440c0c84c464200c0c200400012006070101508401040c1e41c40c1c54a044445160203004034004c440d030b05121000d14009841c42808020b2001c1641080c11640007015248000b400c0d104803001c0140102c2c5000201900180f052240c0032011101400416119 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751229136 1250 751227886 751227901
    0x2040504020a082530050109050612070f120203010605030f1c0f0503010b1309230906010b04031704180c03050718170f070b0c0d1e0302090f0a06020c0a09090b 70
    0x46117864a86400001004180350f41d4002c42e01c6020300900090380c001a090a00e4400c01c80300502c06011030034664403148003886042042c1202004450441c1144803104d49144046409042283c2c45594580071b084441349078241c010171141d400c0c0305036541c80c240300c00f51100300303507140b4180e400c03154000b4100f0b0005001030545003000700703203205000070441da00e195a40c903007809440001d80604201c600c1c2200543c00d984142800a80100d4200041c059541c1008189000d81c01584006081c0c4a10b4104500e030b001ea83c40f048401510a03526000205010301070108060281c005820380081d1a25000800c01445100002201e2807540d21b80804039142c00c0d0b9949140d2151b02e175482d00c40c007810019404070340042100350000c0800c0c80c440341d202c4070224102420102d4002400041c000c0b40c2c405015a0100045040e040511900300144c0340e8241c9400b01e00f0607100d001c5040c1c0c02005030b07800454501d400094070395654038100c0f000510b564892645d04240c44656a009080409450105040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751230386 1250 751229136 751229177
    0x40f150c020a151403061e0d05030d05010e01090504050a0803060103060e040507030302120a020307260c0610140f0906120318041b0507060902010302040504020a0825 73
    0x10240203251200000e005500040e0000105910039448030f911402c94019440e0004450628401e0031242c4c14114500340780420100100300c09081d50b80c541c101d15204a55031072a800087c401d800c681140d0b00c070b040d81c0e48030b4070007001c2c03c1c041c9041015201000140303c2d40d49025092003598000003500444203242d54003070054001034040ca050546034980810481e4440060602c61405080189080703031a605019080020800d220581d01e2410031190304007a070000200c0f1034241e07019108240213840c2140800c4124140f0070300a20300c10340010343d0710720311b900019154002c400d01d600c401e940035034030703803090404013941c8a201d50405001340c0905d1440c606003520681c46100a020701c00c2c3d42292680280c1160f00c0800b11181c1e0010b0380e055960706050074800e84210443e00481d1111644400c117014003140a0f0a000400483e2511251021a4400c0c1c065034010800a08107546a001054024005400c21640c1403482d002070310002d5098000340e0702840080d92a42c4941404604034441d81031b4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751231636 1250 751230386 751230419
    0xe0a02040b122e060509010e0415090501020d05150a050904050a0618060c020601031a070905030115051c020a0605030a0207120f111203070e1210060303090803040f 72
    0xc2c80400c0700c0121a11040078083d282c2d42c0011960b80000c0d042d410144011000d1843c00340b50016403030b02205012684605e406281941d807a0103102c8120740d1145130184012074141010f440450411810908112054003d0070111503030340801d2150b6603451a200b0034042001040c5507000800d10800c000c10b0400a00d41074019002c1d10075202c0d203500c03a40725441510404070203011000500300071030060140b44d200b403130301c07440252001c0c03c01949943c0743c0391020341e038283d0404040780806001c14952070065036000003c000c050000d12040d480c00c00e180708a4800c500c11580035043d80c200007011320144404030381c0d03501c1c0d0041c0002205401c110085a85402c01404000304030750800c4520701007001000b001c0859200c940e00d12050f0344403508001c10103c586403c011303050b4003c40381401c06034101401d0b2a40842c8501c0c1202c2034120400005000c1030600c10404001c1c080e079540c01c529504e540c0c1059080c0c81c0030b030320350303242d000d985080e45603072803146228803042455246401e010030070000107500c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751232886 1250 751231636 751231639
    0x20304120c090c0e2b410f0307020a120201020304030c0b0a110109120311120115030b0102030f03011a040510111c081f08070611100e0a02040b 63
    0x70206030325600b1039412030350040101e0011480315400580c25250551111103500581d50440000304524010100b1034250404014000d00319481c08201035501a1b80c000c0951010300454110002075801040c0c48801102e403002c140e0250074030304021010000300300c0340200d60241460761050303d002900400364140a074228110300007080008045490441000040c1c0490300303c0315501c15501d00080e15002d030701d03060301d440741c1d04201c0f040303004c80e40c07041400d80c2d150b1082c1808253312500c1c4a038285035106040761680180004c0c1e00104201c440000204002403940c0c4040101c0034180300103a98901038298030401c12001040180180080c065200d02590b010f11b2403142060740340d00010741e2020341d1000c4800003035000c0e0412240417000308660881301904000d14444c040e41e1480040121500520440d0b0307035043c3c0134804007040e220242c1c00004042c41c8080d241c52640342d50000b030100b05400f56407045845925030b6072007a41350921a03108030300c1c0c80c0c50007000080300540c20700014015200295 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751234136 1250 751232886 751232903
    0x614070807051f150f030b1f0515030f071e0e01140a0e0906010905131a030d090305060703020406050a0807140313030306080607080c030405030d090b01051f02030412 73
    0x250b84140d0ba1400003500241501000b00c0e0000384d010700d080041107154400e22100440132000c1002c94104850300d50032480d00fa011811032088000845800502070f4021034102d044150b011040200010165004007012030300d510041c0c45104c8101e03010347d034a22001c2d2206444102d408402801009450b041078818104210b00c10700d40a03240b2070070f03000042060046841c06519000e103150038194980c0c80542420895070541c1070402150a1850210380d00402c181c0d10030b0000d203190140d003080d00007c44010111000403c00c810000e000c034141c3d01c01168540314032404601d0290290080d03d050301e5031070742ea071800c1002d007940c00ca4581e0000b8010005004020300d00495081402004510903c040180c20106202d5480c0c01412541d460740801b0960b0030000900c000c480c0d120304071982124014041315101d40341c42c10041d05600c5104d255102062a100c400c2007000307101d00c001412960101c41c400000e000300c0c0c648079094100c900c5034000580041100340035070b07014500e64084403401505507 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751235386 1250 751234136 751234153
    0xd0816090e0423010c0509040b01030b04231b0702090c120103050d020d03060f0605091915030f0203090a0233040f150e0103091118060a061407080705 66
    0x300c0c450703088140ca0548660192a019040340c0c1c04100b038841030280c450008018040121100814038007640b0719a80c0f043c0e40750600c2c0c00e541d0303120340c21182c004a8003c104001340f41c0e040e11544400102e4109510700c3d400d55000143c20f4401d000842011070210350a6989408034039030801414034802002124294000d00c001d141807149507182c075010718403800040540b51414440645080d2601c0003210426050181c00e000d019a0000c27200200c40b5541003041d120400c560000d510040014007103408041c003407200044d503108603209804140c1a0792000c01c520302120080c001a807100311080d960943c81040d04a00500707100141c490900030400c0c0d00c1f13072001e080802503410300e43c0c610301c11112200007080c18030890012024000c000e25400c1005506002c21110140900a075903103140d050560b212079210a20800300c44103060001c009000e1a64a400b1000d102040001515628043d2240850110f2500c0c00744603404151501c0da00e8850401840796a841401d13031088004495900480d0344 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751236636 1250 751235386 751235399
    0xc0308030f060405090c03100f0e100204060f0804020306131b0f050a05060310060c1707050322080c2b030503011502010203070e041a0622080d081609 66
    0x80e40c080e00710300e8481c04850030b1200070070059940103054060660800c210b207880c181c0c2c0000b41048507240c1c040c404148040c12802d0703440103244220300c020950280b11458201e80a590b80104203a84c010703226514101d0342120201c6004408480094040d0720180100b27011020b48000d81003041d00c41d911400f540d40385940c81811800c1654000d5594100200c42403040c0e14140070201d000e0101030340c0007810340c5001030000200794100d1103144203200c00da03c52541480b040324204002081c40045003540d0301900d02c3e20039900c1d4002e1030015a200c1c10301020b4043d1400f215510700803616010014181070916400300007129001c102c8100d08840d03a030b400e1f8180c0c601203042031034030b042c06525030640b40d40c50480c00e00b280d052102100b5046900c108100008507401050324094884282c500080b615840400c1944c0780c080024490307404a03010072904004152030b003030300301040f60004c81a4081507032011100d40c0c2d004080050b001240d8260001189034039603403102c040510340c6140000c0300694070007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751237886 1250 751236636 751236653
    0xa02060d05041b120501050612030a0f0e0604230d020109092a08070807020c030a0308280c11030c0d030213031403180111120a030b03031602041b09050405040c03 71
    0x20b001c100c50070704043d400000d00200781f0446502802c00e449412510140e040c0b00780e02c03486000800001d00454483c840d40e42840749407072055450004e03002030350b295103441e4007201d8185c040700c00c510106c049001c28800350a021000000c1c855060f181c501c4a6424960481c020b4803800c80b50414180d103140b8410b100c0c00d1700001c20b80402041c0e40304c211450410f940700600741d600051030f40056500115000c84691000614081c009400d89081c8078251160b10780320b00680c402c0340403a0704507a0000306103030100392258001241008551034800e100c0d2041c0103031588074001c0d032107240c000d60800e24600002500170f40050040036000d922150000d626582c450810f0480801641c0c820790022030740403600e00e03000d9034441e1424000d0a00001c9556508030142d60340e40c00c420301d00d450000104900c602c2030302a40110041c448024103480e01d07512180380d1924841544541644100e0601c0d80e1505002506d0700001107049403641c603a4a414100700501005c0e140140003228200c0b410b803130000105400c0f1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751239136 1250 751237886 751237889
    0x513051b0d0c2306070b16050c0a050c010905030d0912061121060904050303060f061905190504050a0611070b0412050c0a21170406050a110a02060d05041b 68
    0x8503c0f1041a89207203101c00790004244016010744020001c500c00300f1403c10201c0e0303100a10310f036050400304540d44206c0d2180220280c40a040c454a00036208020380442c0d0455032403000c0e6110510155034108051303880500007803050104080360014071a6031401040245003c0c003400001c02c0020485c01418100da00c041042c2c3c2042c54803040107081c10300f5880382c031500440c00f102d108886040a480303403030b102d110160205219032000b0403540040c0d22000c0a03101110401c1c09180812008850060040c2d844500c40d440c03002c2821141020b65401101038405440002d45010f007207a0400d40c060300d045400b20b2030054184510200050308404100c01000941807000c0d004021030814a03016141500c085411445090600414002d031042c89041c013180d5140c0e803507c3e120810890416890014030303522454200c1d18001800b05403250018020481250b803959001203030410699820f80310644c0a9001b075000008014101c44070f0429008150020f0152075032041c8000643c4079a115050359 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751240386 1250 751239136 751239149
    0x60914070609080601060f080f060409080f070b090a1a0702030c01051008011d120912060c0903060906190f1d0c0a0605040b04050411070f05010902040513051b0d0c 72
    0x142c0d882845004000e2040c140145010308201d10116034071400038000400003044200c022221500045880e41e9079080403101c9030300b008035039075121119608100140d000010580d0224940804600303900c1c03001501c1d00c03a254010b4000f0305903200080c0503485984014080740c0840c842406001402d820a10a160066004074513010005152186a60a60751080e254101481e0f0440049080da140891000c110181c80c0e06040c0d6145d0001b000689603c030b89074001d50251203030034208480d20b68040d0090841c00c4d01101151003d658500041d96202012103840030000b02d0076041c494861745c030b50421244103541e0100810108860001c250003514103602203421580078444455542c01d2680404010700150301d0010300c1c140c18844101090b20503171103000c0c0940e5640131003d000c4551042500d0400ea4000c50a50100045003002806880302a0059100b1850800891200400300081410f401c1e8000080c005060b1022044a003815001c6005a003200d01500d00c7c0c0d0005030f80c42c904402070700a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751241636 1250 751240386 751240397
    0x10b0d21050c0f0610060807020d030e030d18021903030f08060105120f0103120e01090b0f090310020c07150c030e2809050c0f160204020706060b07110102010203130609140706 77
    0x21705508005200c1c440c0d03071012003403141c0d02c0c1c01d00c1050341d40030485100d046a07a00b40403031542e0907414207034607502c540302412000d1407620b0b1213110451045040e007000c13103000b1215200b48615040a40201c40210b03c0000c000c205200c1120406501651405901c814141002400c040940310103d441c030808a4409045800d100c005004204480c01e4000a250340c2c2d240002c0c000c07161000181c080c7d01c0b00d0164586031000446d400300707142044011610581000703415110710401d082c0d2544065000b0321410080c501904401081c03e034084662446000000d50f5800b8280c180f03130700c064465182000301c180c1c0042c0764003500c926034408a880c03101425808032071011703c580b401d8402c2d8111000640803410581c8100a100d081c402414160707024442036030207030b50821489100040003441518401001039042c070000103207010f0090080c00450b4011401c10040f9014800128201c0c80102e680c190308019241c190380c0032071100d911240c2e1340c40c428000c5142c2c1d0f003a51050580741124581c0400001107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751242886 1250 751241636 751241641
    0xb240901140414010e03210a02010f0b0a05091305030c15010806090307120302040e0a02040509060d17070309030204051f0f12111c1202010b0d21050c0f06 68
    0x141d0040112100030003940d82141020708012180e18424200001d440c108000041501c000359070500c4803113141c050300207004074866240380d4089440d40085040c600554030304407030083d050850b030088400c2980c0084c00c02c0503090402c01042072642c0003800a0081e441e05585a800040e420401042d910079148018800300400788d20802d241a0160031094031604103805000c04110000240c85145070301200d82c07014140301502c110001e002e1031340249040d141d10400c1c01041600d5500030000d843c6c05664016150341d842d4188035001c820000000c0811065004c00c5007400c58442c0609a96480782c9000781c0200d9480d000107042d1001aa01d100c001103410002d0724125410044200007030a09214800890b40b038a081c1150108004901905551180e02e6001c541d030f0754002c86c0d031820801451541c0501c00c803400d120100c59a900381c24070140d07182207100481440e01503a480c1c240b0f54010404800d0072440072039090186c405441e04d006200c02803000050240e401d0000b00075840c1010020302207403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751244136 1250 751242886 751242889
    0x50a060209040b12030301030602090d0f1506080c24040902030109050a0b030f10050403091e0f081f0c14070503070b06100f0e031c112e0b2409 63
    0xa911819003d40b00ea100b00000042d520b6000c01500d0441c1d40044c00162140d50940204010021030000140541011400081000020016000c0e450841d460401c805511003022560b9503400c112101d90081e0301c419410b0580c44010300030443c40c03560b9401c050a01c0c5e0344a1115050f80c000b178200740040ca40720002c21000c403400d440341d0380200d0b4080300180b601180b900005519500c40b140002c40041e1a00b000a05060241400c13a000b0960429500403502420080010044060041d00d10320000e81c900040c07040400210042080703114511010303801c150392581d10083c07250401020034000c02c2d2000040200c1240e0241003000d0103400650b17552115803030325030700303800008000034810784070b00c20780d00c1c103491380311107600450030f4035040c8000980320040000b4a058060b05022460550240f03035000c865901100c03881c02040c05a04880078906481c0c20000452040301201c02481e41840240440701c0c62500828600e003009468040601c261000c2030540b548044543c5140b1880014a031229 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751245386 1250 751244136 751244141
    0x6091005040213050c040b0316020106050307060509271812040e06060d0b03011a09061c260a09031509322b0302040f05040216050a06020904 62
    0x1940084a010092440c080c0d0005240c50b1824140c0505540e64500040103c0c40350000c5802421036020429102d103414002900d04c448007078403520040d401d05070001401e08000a05009982c20b58451307604090b40038040c4002e501910552002069030007405400c0840d07100364840c040c0254070755101100c0c0800840f030f0314000d043d0b085100042410401040302c00c0c01480d289801100484040387c0c0e850003a09900044c0c907450b0700240d419427a02000040f110204401203400507020350f41c0c099190388407410043c000030002c1243c001c00704481800c0001602503015400340e610803000c0c00f001c0b5242d08400781c0c06a004507908030007085a180e0207005100c40c0c1d090340c020107640200c0501858132507983d580720200080c260b034004200000c1d03012445804c0085040030442c00c0104540c0c0448002038000164000d040e0b80e03290051403a48003203c150710038022070f0140d071101e4250301c1100e0320300740602000358003003507d030100307400d01c00c00220010344280302c0072580030700030040503845041c4c0d90b040008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751246636 1250 751245386 751245403
    0xd050f06180703021c02041109040b010e060714071205012c120a02010204030b0c13081203070e0f04050405010f0b0d050c0f1c0c0801050f040201021518030a020609 72
    0x580350341d44030403034210070400180003041e03d5040c1c4189001d40e03028100300c201003c204100135445420900b40c14030030000c80c0054411580c040b1006d00078405040b00548940e500c03100c083e9081003007046004045001030140041141c6400101e8030040d60360041c40703000384409070044070181d450740380d942081c1c03041190b84814034401a141b00d001a1852110329512031103800d002d46c0032400450f140a20500030f6054070700558110070207524900c0c1240c1002c60b140e00c50280c0010700503007050089041c100004080350312814086c105442c6440d018015199080130541d401d921880c10300c0c90303a801c0e46540c0a118041c5120300e0022503420850040b100c1070310111030001e0300034400c0c020910b020601c0015010340c510f40903155032002505107400700700c01064284150b5a00e4641030f480108124103046080121840400200090348804901e00e10100c1c040d100030340182c0c00481c0100480702c804141a400480b4240490f0041c05154400b50858009009400258104908110050700207001010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751247886 1250 751246636 751246651
    0x90510090e0c12131a090d11070503010903020a0c080309090a0f06050d031715100809011503081e180f3610030c0e07031808040315050105060301050d02030a020d050f06 74
    0x5e08600e85512680e41e10b50b0024030b50410840d5281e44c5036031038a01840030350b014100241c000c0c413420820b810b0295850000274800c1b503048001000008586c070300401a90400c207030080c05892345895149540c006080d1400c400e141169071603400191301e03501c80c060b140c88144292170702c0c803042070314060350080600300070700c04140100b0b180d83c004a0fa9807106034610000f045410322890315229848000d0040607200b03841c0980c0b600c107810100034001c0d00f10180280c40c1d01c1402406403520b61080313105aa004010300001030440f102c00340c10442c40e203040c410b1030000000d00280c9608003022065804180c1e03c500d000c00801110175082c86518103005050b034000300040c1c0c284030051a542c1d403091044a14403420303040c035001d04041408984250000c007650340802e8560100040c42d0304100f0101d9100c0d100407510b40040007102d449440050044504841d00240641e046a20788001c0c02a88031510500b20b92502944a2600050b60351810110803c3e00400081c11000000d00c509858040d02a0086 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751249136 1250 751247886 751247933
    0xf1e0e0c03030a11071208131512021c0504080c1506130c020a1202030a091403120913021305011701030f0f02120319090510090e0c1213 60
    0x14140d03034a00108031070100d2618548844000ca4a4950a04080c11a04810b03079282290003420107200c03060307015128100044030017241d000d07991000316000c02d01c01002c10000c920075a905000c03a0340e456014000046140c1c10441d14030a49240040480740c089078112003072080420300e9410071a081103d000c2e000c40d070540c9040141008000518040c1c2034001041b8060f4851000910081c0300b400302c482060b42c4031803090624070200310080d4032500011103040024118481c00a44804008408208040090080c00c009803051981c002c181d4068095aa0404141d2088000d11259403000380040081640141c4000b410a40010000c888500102c210000c0e0b01c001032000c030740a220403003440303680031040c0950300e60544007281340442031200388000b42c0000b003400c011224100080d00000800790780d41c11580c91b200c1d41003180c54443d143c00d0030001404941b0a100990071703950221b401503200d20009042008401e1500c05200b812542d16450848241380802002200d241e0813580c0d0040c400c01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751250386 1250 751249136 751249153
    0x5040213050409030905100c120912140c12010203012c070813020406031b0603230c0403050723040b130b133801210f1e0e 54
    0xc000c000355240c0034281c4225500c04024082500800a0a0080c400a00700d5140800284400340c088210254107541802d501c10b901a0b074940300d400720304280c1c0d02003074410b21044005d80703807003420491044060419205604004e0704695481405810780004e050015980c1d40c100300940c030100c4d5465009610a03182144141c0c600d4001120f01d5a1100c01480c00d0502c1d07a443d00c4c0001c542ca8462080a03400c00d00d810f5012040c0030840803000c101312400c200310145c0d41d0340d40a0480c21191030005000c83c03014800c00c00c1d11100324009100b41c00c2021880c400b41000d8032911a1420904154000001409003802c5070006c09146806070036096030072942040302000d4000850118042d12960113249640e915031a1402da50704025203003c101004000c005000f40c0500d01a04c503050544d01c148009140d644041000310300c0d28007546100410f03500d076088009001000e00c0006a044060000252683c50b00412030b89548541c0c105c0c141c5c0414002050181e4500b00c0c8101c5800301d112030b0964005014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751251636 1250 751250386 751250407
    0x106050f0a03030f050918061206040b07030903021005090d0807020102090102070b03060402071208061203180d0f080310151e05031005060706020703020601081506040504080d0c0315050402 83
    0x702801101e4040c2440e12400d01c15a204403500c2c810401c00d00d40c030a01e000060f842d011103082007180b00e031b4000c1e07d41c401d0781d41002d540e81c0c1e0f4400080343c000305080c5e40350b40080c0d001e901c030ba00801e1032644203004564181101d041c518003540c1080300c4031a0280d1103508241c07126540014035a80000c10f0303000851070108003400003922000308c0d01540e10b07002c500001050454485504840403150040e1111a01c40d01500e030040c03622800350384203031040b5040040d5606095000c41103a109000040c1440100050401840382c2505100c400351018910207a00001107807190000358414440d50001d1078000d07051004020441548190704010801050300041c0703c1a0b489180c441c554100e41080c548070b9a810628110900940d00203913080031f404580c6030304101990f001741480d14465000d88105a88030f90f00317940e80360410340003c401c4002484c08520b040c1800e503c042e40090182d2411882d080340021903c0544404103462000241d07590420f84140c09840b0196015041c11502036240002c3ea04 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751252886 1250 751251636 751251649
    0x1906020d051c1b0206011e0521030a02060601090b0c0c0f13020d150902070506220c0b030702060a0e030703031122140a05061902010b0316080106050f 66
    0x8003203a003440800200348036803044400344282850000b4600348200310071031410a03428054440c1c0355001d0300c55400003143e14840038400d8a06c00042031024070720949044104034240c1c2c44048942001900303482907080c410300034402816040d103a500105124113140000510030b00c1240d0044000380b0042c0b01c99a00030401144118242071b003180d90b00130356528540000c3d01c2c0c010380307500c03075880610004000303104000c81d4004c0e560765100d03404046103241e0307070301c0c60302050f03100d00d8400612a030007010004d070210000b00800d0140001c1e41064248400c2c080d602c4040610498000040c0100c01004000d0300c02da040003456842510302c0c2d070074090101115116503880c050042c00806054880c805580c21034100802d0342c242003082c52102100d00c481980e04002d480c000d0103802044005d01a071003006080400c6004102d62020317094030702d0501c00c0040c9040d4000c1c101403020855495030100f10407503608005807060090702c000d035000c455151002103404c4401c0d640c4840d02030858807640c084156a2074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751254136 1250 751252886 751252903
    0x151413480b1207080601020c09090d0206090a0b040201050d0209040609020304061508121605161502032d2106030d0207030f021909090503040f0e060f04110c010f0209190602 76
    0x241410b13602500d5140060b070502d41030707600d07290b041502c55040080c40c203400968101d08080301d8007a11016125507001c00d440c0c10481e00050200c03480d001c0840c0055105a00030003800c5c102c208014100400c550000d000d42e403540c1d0003c0059178012051000f4040c0c01c1c8a005805120982c4800003e49441c07002038a440e0203d10108410a020841e2418103000b8581020340540c8602030700d41c60079842d0340d8080790910700e00541156004a100c00741c201c50000089a0000c3d1482002c1c0c0e00400348805102901046440a074180c071400b071151a6003a86464a103c000300c64101000d13403039240c01c200341898149109191411580481c5003000451071520740f030104d440c0c040d240481680c50140c0300302c02400b02a4004041149482c80850030701202002400589242c030b10442c140c555110500c00c040c2500307540c6c065004a401459032420304d481d40c0640901b41e031003c84581481120140d1500311000b007400364940c2c9400040c0e00d00c4614120b4401c800c0d00080e1241c84c403076182810b80c000e5541c00035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751255386 1250 751254136 751254151
    0x1b050111090103380103091a04050c10050d05070309050a0609060b04021606151208040f060302040803161113060503010501050904050a032a151413480b12 68
    0x140b50550081e901c01d810020006400204864a0b464a23040300e08400c2c808131003d680c0d0303009100140710280b8003408491500019955071074144400c0c2c01e90a0014040a0407040c2815550340c0802c000075001d101011984d40160b0000849001d20f081000c181e802c000c0e4054483c0381704000c41c0b41041c4506001001c1203400c0b80303000400103030300c5002320302e15840c80c2c01008101c02044001010882c01c10010700030f40d600c0045409a0b15a02c0c103040c0c090380a01d00071018190014400c0100000c0c100496143c001d0140c45403c000000300c1c40400c128203409492200016220142482142400d004050040c80d042c1c50303c0c0368515007a12060b40b0b520415000070200842c000c00300d8160381e141c00b0f241c48800000c03010f4050b4a0312610780106030307802000800c06d0190070003240b4a042400e100c0454032441034642c4404007152542d450505a01c40ca482c901001c14094081803a08441c19000401252401c0140109121382c1e45c0150318a5140ba444130b60f120104203c0382001840301008160850300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751256636 1250 751255386 751255481
    0x405010c12061a1b070803071a100b070318180e160605131a090f090106090b1c02160c082d03120702030307200d1b050111090103 57
    0x40004d0381d6201210000d0003030035481618030200d04c10201000418003280304000070440e030064000c0c40070042108681c038194400c00c1e0441000351b480440020311000b4800c2c64031800c180d2120001e040b00c0c040c91b40000d07610410b104000798070361007284902101302d149540200402510300f4100c94084559000b081d00f0440c000c2440b0040504460010000d80707101c680d881320990304840802950f410007001c091145221400741d024034186001201c1c161212603883e000a00d041031980020307548558200c0c1c241411603910117008010520191510080013840503200c4441ca081416400c062a00b043c81281c10410744030001c45960ba11741414a0402e50110b0302c4102d40342172a60541c05070b02503088241200400300850640d0120003980b00b01c0454982060802500d2884100001c014012400f15031100800510713980c061000700308602032804200441c0840d982d0384c1429035440b42007200302c008004c1f031494004e40c2c15000d81c000d0b0034140c4005080c080c410030600328a0040c400c105409021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751257886 1250 751256636 751256647
    0x4051b07020a0f0303032c0d0503070c05010e0709050c19180503030a091e030b06041a0d06020a030c050316120b040e07081c08010303080702070e0405010c12061a 71
    0x454220702d450050005241c10f018195603410007030058150b1080b02d0600a00324055041c811010301d0600312a0b00500000b018020b01288069a0641c00a41854240001c8014501c00150240180046140780801401c1e2551608a00c68191500507182c000304920910892030044802d041402c91508246000400800c01c11004042e15595401454141c0000585c248a0b642c00c414000111000c003650b4010003000c20b0200408088903010040c8402592008142c061406030800d0b040e2201a2000e561010700c000c0010b403031042d04001c2101c04d2600800c0007600907805110b000101c0c60f2030700b00b007880d629044004101c811644003401c024003810f44080515000c11354002d00300350030050000c01090050140171a40d440852240301d800348942d4400d144104441d0083c403440e0740d059101e410403a4219a0705591054004020704210301c140100040c0011003000706a00440c01100001248918114000c0c08080c518907415082e40c100310007003281d240036146048544060341399168540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751258992 1106 751257886 751257889
    0x170721021905042607260c04090308070315150504050f0307050603190209131a100504170a020a0834120f05070f05010e04051b0702 58
    0x20180350302032406960030452008200c503060040e100c6081d10360440c02c0c46da107030342a0380349030184c14803040c1c0c200300c8010b1092516414080d0f13424803540d1030580b400703042c10328003030039031020196035081d000212448450b000e4060614410b00006c0480101c0c001032480e0094003d89221b208200111140ca28001900100f200c001505050456403803980c03240f106841ea40d41c5030040d58080042e40b04555514005000619601d4000621000407102c1e680c2d08000c69900b06000300707280c0e103c0c06103594101c02078030221902c1c2880b000d4400c6180455504102c0091402034100d407001d4804100c0100201710180242d00d128038201d1b500c0b05a249001c400d404c054483c01b0070f8401d0300c0c018422107041005100026011301b11014145042d9540c007403034003503142d0046900fa8000f0034240a07960b0720045594014000700c1d000c0c0000e01340200c840310700741c030060380c044e003111000101042103 = true := by decide +kernel

theorem cover : BRFrame.Cov 751079136 751258992 := by
  have h0 := BRFrame.cov_init 751079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751079136 ≤ n) (h2 : n < 751258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
