-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3735
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:31:47.932697+00:00
-- url     : https://prove2.me/submissions/8dbbd9c7-28c3-41c1-a9f9-0736d3f4da60

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 671582733 ≤ n < 671762589 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 671583983 1250 671582733 671582749
    0x4091e0602130623120a0f0906061806170703060e2e1406010e0f060913020403030f1418040b060a0e010320070b1302030304140a050d1208061306090b 66
    0xa0f040c04055003000c0717400b021255092401058017403001d5507a1800c0420041c150001c0303d00b80e80042041002c15101d1015100709414407540c00c04d02030070403100095a42c140040d6603402038a18019107034a50465440b000a0690410051654468080121010900c145451603a200300d81c3d16000013035501d4411006031070020a401e10155800010004a03980084620341010021103011804a0300100050041c1c090980740c0c1340c105960401c00e06107020f05900400c00c0e40d000b6122240e841003c16011a00d0400002e007000440c0c0c4140071840c002c500d403c04204007810002c00c0172071000c3d000808590385030007441c1080700251a114240070036503051300c10410441c0005007403000700058803501031440e20079180700420b001080c00002d1021540011514012640102541d550700d41d039459405000700006141e41c800c0b24801000291441d040801a0f4032552003400345000c0d10703410000b42c9800000400381504600060894100f61095108020103804c01a82c00901c0144400c00d12403a0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 671585233 1250 671583983 671584037
    0x290603060a1803031e02070303090203160302100804050106032a0e0c04050105070804030206040807060909050709060f090302041d1c0c0f030306030b070809010b04091e06021306 78
    0x18914019a030320a42d030b03200703540302e03115501410040b41030310404004a64001c4040300c080c81403407001c6064420950b140d0055022039000f28101c540c954403200c0d501580115600c4021342c030118224003030300120b00405030168020f02031341c0002911942ca4032050521501950312840d1016420083e129441a4880d10805481d00a8010840345000c4d032054400b440b03540585414081c021401d2010440751a0844010710f9014003000e464682c3d81001a5817084a402844046034074080041488020348c400c4910503411965840400d0780340070f0064408004107400e0100b00700040c000400583c6582c0070320300740038103541d03080c141003c2e165241904021604111215a03d180491101754651005e610f916142e08030340c50041b0103042e49010350007008a40d00c01020341c0c0c001420045002d0b04200e2051042440e01c00030300124602008000464000b80c10042c0b9000e00304615036060000910311510b064070540e0010b14045405075407480c0030705a5804180042d1000313800380100e2031940c40300010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 671586483 1250 671585233 671585251
    0xf2f0102150622060b0714060a020f120c190207061116210f0501060303080a150905071107080109110901140105090d06090302010f0e0a0b1329060306 66
    0x1590900100048a40482c007440c54000d8440c01d140c0e000302003c0d68070030700042c20b02400007542e8076414549450b82e00f0f080802c101e4540113402c000340d40e001541c0212002e203049510340c01d10340782c1010517004c0b1460b006010034001d04400d12203104074104080c4038401e111801e40042942510745600145041200b40242c0307917a802c98030355200b010360242851019a07a0042d042c00501010180c001c40010fa01000a400101080d540340300b4440d0641c0081c1c140e0703002b9955010f19603507805541c0203803881d910390681200241c00c003c02003040039500ca140c20800c0c603d0240031000086032038524003200780d00481041d95440c4801c0c001c001101810300c0c1401419914000290700d45200c101d82e80746154030030740c1400301c006071004266980342c00c0422850350001c0208981c0a107818000c2c0207291009083c0c85151500700a441090400036050754095400b600c07150a95480c03890b031821b01200424202c40d07072580010344042d54028000c114402c00d04140f1100e0140c83d01004241c5452006410814 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 671587733 1250 671586483 671586523
    0xb01140d0302100207210f080a0204030807030f05090a0801020d061d0a2a0503070305010605040b070f0c03060e0303041205041d040c17100608070509040f2f0102 71
    0x740c000c61900c0e107016183c48016220403981c140080e8a10156045180400d407407410611550b4104c0c108994402007540d425072940d98525800007288240d004c0603100200c140000340010388501c001c02d450b4040d62a203035040c01c4200740801c6200580f0380111340c0603500821410442e03c05489007800610903082800964031807105121401750026004400441d1250354041040c9000500400030720310f0614840da401e16440d1008005800c01c0c0d80240009040a0000801d64443c8043d54266501485403d241c21550f80e1500000b60070a042158023145007240000400c2c07182c803032524a0b0f208400559902d10342494500300340c00e140e80c0180709020041c0300038401c01c5222003400c1e01818244405202d15140d40c145201e402c0042ea000740b500b0145008402500340b4045210b0034201d04408041c4070f401e07102d00707110303171260314500031290000c503214000360104110740c1401340c2090003400306000c3c18520000c144440f090703007400040d05010032040305c40e0302d507410408403800d2034001031404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 671588983 1250 671587733 671587759
    0x2121b150123031504290a0603030806030703020105030106030e16080a2d030f0c020301090c081207170702060c010516090905040c140415080d0324150302070f0b0114 73
    0x130280200252000e0149468030325000801c0340d000d0b080c6400500d03140e1a00010b031070140b0312807002d0802404120700054078031001c604541000900314007501d905840d207a04581c2002c1c0b0450003880080c2d5040e5452207201900358401505004c46000341c80d9a001400e1103003c1418046550700000151070040240c1110107500d4201c414442c499980d4540741a030b0304440903034012125130002007006035065103002c04100402041005000c1198482c10680c2c521900d061403c00c1d09004a590142202d5544c000c07250f404c4d800c540060031801d01c002e00241c24540d00141aa0844000311584840400448070982c3c1c010340001808000300b4046030180300628260b601c041c2c491a4030301c07030011018001608043c1507900c60f0401c081c1032400034280540a1b66070401142c1c0e400c01c0520600c042450950203441d915820400c0d14606005020b40113402c0f85040094480c5503a0034084c40e00301582408140001008880c0d40c44805020303802d08a40c03541400c0340e410f040c00414241501c504100c040503 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 671590233 1250 671588983 671589013
    0x7140601080304030f060902060310050a0504090803010521070e010f0906031e08040503031206040b0906010215060415080d090b0301060c0807140a08180102121b15012303 75
    0x442c142d0354400c400c1181c911646c90420f0140021040007540844084100940301c0000e525940885d6400c85a501e14180d650f402c4c40101c40c107080c03001d012100e0410043c000e030b0510150b001d0300c0a000030040c00403034405100c024140744040d00303c1001001e031000100024481e81107500e001d415610400c20038a0b01c0c1d981c0e00c0b100681c1554034203e80a00c0b20101c2024048928151001408058180d9680d680c2d0f0029081c0c40400890356188624908010b0f2070b868105440c655205400603001051040701d13003821443e08000c018811580f150f2140030040001421441100040004000500d0b480c100514060585040c68222040004c0d080c0010002a1350008000304001d41010046643e600c0c00d040c485a50540c6c42810b40c414495140100c081041e8600108018006040d426442050400c012130f10344180407100c00c1c40e003c081c05241d25241c9803401008020003a402241e06448184201c000e114070309070b01c0030558540891000c4410300b20758214280042d8204d0103089a14500014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 671591483 1250 671590233 671590237
    0x41d041a090a2936010b04061205030429043012110709050405061f05030d030c2609010f110304060b01051213110303030402030c0123070602071406010803 68
    0xa100b440d03040303084d00078080861070140110910700c40c440c107803aa491146034050107400d000180e980114509000021603003880000d002c090703540314025500c0c0138079080346110340103032007180c5403400c0e60781012401d0741520f800300601c02045540100b0003040103581c00c0e0110409030409290f01e0800302c01d001d80c0010401030142196a0b41c60030300d000500c03058040d440c07030101c1c81d401060100e4a0041803100744100026a9841444000d0103c03c20b00c000f4150b410404030329115258159001808842c41c06000f5007084103110110b2030300c10101800e480b440440403403000c0da81c02414000c4800c1c410521808c1c0140c801040d00c2c418180031318100d54004ca00d9911009201600d0350b5598040c1400d268852022502c03c803685041040240c1480d14080841d002400f10481d404481ca02440c0002e050102c280c03840741c1d8000300a401d044061800540301d18030180b60410003800240340744a2803504440103000d00c2405031400503107800079840c0180000303a0f9941d035501d880d40b000b001000f001c900041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 671592733 1250 671591483 671591491
    0x30d0e0907050702030a0b0a0b12120319150302030607050a020a0b0601090305030c0730060905071206020306040f050907090f0209090a0c0f0302041d041a090a29 71
    0x1010061907880e04030844250040308802585405440224018040d682c10b1a1780a0400304a0800c0303188070002c20801c0401600840d001c90307820503000c1070818100d0001441d81700100c2040c070a62402c10030f1203042210f091038603003000c1c2005c0600034000e50070200009036000c5400e041451510081080180d520904d01100812640c0d4480000342c1507481a4040310095501404903501c8411085910303484142d18020000744160741e4a248401c0030610915030410100711034810f2600840343c5410014004080043d10544030307400b4000740c51100e00d0340640301240511801a104d007080020082500d540303902c0c20749541d0034441404040e02010502d0701c111100402c0000c8c07001c7e030102901c0080d00800c0c02c1d40350701c03001304020003000024070341000e00503507a10360300c041031aa100d9a05900f01c0c0940d001c0d600b4080e401000b90b211485c5801011034009020344d01007140020345401d0a070310740c901141c1d6049203400540c2030340204011502c404a03080a035110034105000d006040c5c0541d040018 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 671593983 1250 671592733 671592739
    0xa02060c010b0306090a14030316031d030c0d030e010c020d0807020a0c0e06031510060f020c04060f0509012102041a30010b0d06111c0c0e030d0e 64
    0x5060854400c02d52085000140107401d5803010300d0190a4a621020f04803c00e40750503001c0314407850344034000320031a8402d00c0908400040d04003202403c5008060f82442d02c02141d64840c00c0700e0514500300090441c20010000134150040d0320000201030300d001c001c840c40168109182d1001d0b95802160140444180d40343c488415075a04004a14040796090040c00c03034410030300702003040280300481e144a924281c00300d410300b40c0340c80455206a02e044400c41c3c108400d0b02c00c244192031083e58400350150700c9104980c41e0124a43c0020120380d01c40d03114a5511038110810440c5083c02071560740108a0072050458446c040d141031280207641410082c0301d240d45061011145c1d80e00401640030300406095800748003502600c4034003401d840c800e40340e00c01c584080040e54012050042040e081c03409000c004142003142e903007002a19a603044005c480600340800003e1960052001001d0f00340340001090a1400b43c001030036408100000c54029000301075034044540d00f20418100d82c40b829 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 671595233 1250 671593983 671593987
    0x13060c02150a0e04050c0a02071512050c090a05010c0804060c1a090a032c1201020412061a0405151e0301110c010605030c0d0b060103092a0603020405030a0206 70
    0x184001040610740c40520090108080340700c00c8940e41c000900081034074250b90803c0580c0320101e9481450181104e1400141c4c089c071014003c42d0484c98455000c0c1049080120408100145c2d42c0d06450f07086450541c03510000c10750004502d40f000b21800204030a0804411850458032401124442c50282e0000c2c0600c200c0124200413640040040451b000d550030201414187c49131a110407480ba010340024442d55610281038154144c1e00c0b81381d012414001150707c540c0d005020b0342c80d400c10f85642707140d54240000200c400e49450040c5805118180000c0da0500070300d00a0041111020842c0c0520b10704020807444048514140385d41e08002c80e40f4030203480d02040c0c1004042c001070745594042d400d1a081280140604001d0501070000b000240401c07900d8006160b0390740da44240d802e0744688003c4441020401c200d000c0f03600000c041c50045034440300d030707290060302590743c01c0b0540140b1042e4804d8000c0e08050640c40c0e020f0803044c5829883c02d890100000e40d103826a00c40a8459800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 671596483 1250 671595233 671595257
    0x6030106080f190c080a05011a0405120a0609120f0509060d0e2e1107170d0e0d080103140a020a091113030501060503100207051911090c19051306 64
    0xc01000c2c3c003002c100140050005450410000700000f109845c8041300030304007000400c0162084e142129079042c40d840880c206890001009003041d0079480c0202c1074000ca0583c14041220303400790030015401450001c601d04a203a50040c5007038424400ca03004c000d8140203000480c0d603280200c456400d41c200020540f40c0414070100c3c1402e020202e00041c0c1910f041a0758109a4228850f881943c0c02420402007402d0515005000303105224005102c1c1000320340b0b03a01200c41803000b600f2501ca00e6100001d0425900041f0303850232003034404c43c0020400c40d0004008000c3d0740c106044c28466101c003e0584000d4943c00302c0d418502601808041684401041203510b5080301501c1d103e0103e41289030300ca960364107025000b041c0318022103010b40514801c0c1c07019291b45000300c0740c0f8680e01100500135624550b0060f941d0850881048401c501c2588944804c2e555021050b0b000311004811141d8980d801c84054104240c00d522032010f124040c8401002111080701507411900315013440c00110351 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 671597733 1250 671596483 671596501
    0x18070e0925051002010506030d08100306020301030503070605160801032a030f0512130506030606040308181e030a110604080f06011a16021018090e070506030106080f 73
    0x4070803500340100c1110318281c07805407410a841c040450300180c90308490b144058008030709880c1c00b02c900a030036903c400300400c0c50074480e107202c55104070181d000c00c24007510307540c464050780d0080c2e00680e11584003180e0407040c45072511407284c001011140c0d80080420060015050410521001e0201050601da00c4800c0799404aa80c000c0030007118668559500da14001c5079a40720010b0a0700c03c2c0c441d0030708000c0d920500c10112285034a070030102d001040d10380001c01c0010b510043c801500134100307120000000d0b0604014001003c40c51071124503030700040c1b042c098090403196010640420701d0402c03d00a440100d40c0ba031503075400c8182c007200340500c8004100741d8419540561014426529003444518020400b18166190901c4031901501481e841ea0898028624400c49100340e15080b07034014500720103c40705815003402c006000d0300c030f41504414843d203154000c842c0f483c1c6682c814a50900180f00d41e802a0a04807100b03130455041c04401411020000d00c1f000f001400c440100385207030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 671598983 1250 671597733 671597743
    0x1030609110c0f0d02030f090f090a0f05060303090618150a0804031d0616050114010b1c0203090a2d060b100c0b0c0f070b090a030818070e09 62
    0x200059040c0818038004286030841d5001e802d800115003c0ca01095a141c800400c580440b80b100e0ba000310b0a104860040c454550710107160a90b00103030201c0032800f6a01c45240c1c0c2445009181400250505030481000540c0c000612503403007a002086440c80c10360340c1c4819106190450b80c8414001c01c4051702041038100e08440c41c5502c040049010001c040e84120598400e5110b50344810382d205841000c6414482d0041071164032174800c5c025400c51003254110701e0b52650040303001103217500224602c958840c4003a080503040040000700180b0004441c1003201a19000305011851881c0c0004100d031074a0004000a244060102104204207a1840b0910034036105120080885035103261410091245545a0780204903100c2c200c1e02c0700303002d80320342e8285a4001c001d145403176440c2c2c0d040050301c2c2e0205902d8000c035a01030082d5400718002d04c610922410031180200540d25060802415171040200f4006900001c070320314a40c40350001c0b6401d402ca800d84000d00c40301d0344034860414100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 671600233 1250 671598983 671598989
    0x20a090209131407110a02060f0c1024050306010f0308090d0b070c0b0f060a0e090a0f0506011a0712030c14030403020d09061404150c0c030614010b04060e0f010306 72
    0x1107800c0c943d02c81018915944103d002d400030340c803600c00225414480d10744803540c00b07078080d62001c0103120303039814040403c00500e20300d141402520050034070200403800315004040d056241403800107030044107180503021100a0700c012001000c2d00c0d8503060800b00c0f4144a40002000c0c098003041451081d1900308100d081c0b42c1d03200a24807240c0c501740500504d0050023880035220410310300d021496403510036082034060480907000c0c003503841c01c0003d0010b50039009070500c125881070101540100e00c0d03403008908101d102d00082c140d99450b0203403580c201c5118600e5078a80010030001440080e12003185040709180c103050104480789411025185030800440000500d00c0020412007010350200368096003007d940c035202c1140d070321010f007222202c0400c10700c40c1007100208014032007104414158680551780c5e140c1004200714543e65804032a41550046404544800c140031a074810b0700c20329405402c01001c458140b07407419000034458510503820b039000e061010281d000d035900c81d403c00c1c030103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 671601483 1250 671600233 671600269
    0x120c12030c0c010c0c120c0c15051c0e1f09080301240302030c04030f02030a050a230c0108010b030415051338071e030209010318020a090209 62
    0x141d25014821110700d40c80a06002c00651078011400502d43c0140081e070001a00b0801d01240b4040700031060f1550700703e40e84180c40ca000c08850024100d2680c09030500d0786441035071607030740310240b0903000d200030b215045404c0c200c1820034000070700740d0000055400b0400071891503e030301e43d030748088507a006110184000e010303a0000000400c0d43c5c030030b1440c03000b000e05003404d40044c48549040101d0490000386d030843e103a8030f0100001c0010404149450303d500340001d00780c1380410b10580d0b502e031408407045403c071480d00c0010101e03403c00c00c0592041284006c600d01070b240b24803202000030301c00e51050049020001e000720205081c042030700b1050301c0c8420401d070700f00040e040105961629101c0b0103012600720100c4c1065030310094081c03000f0140303450f11004180c0641c0d500191600401c0008100d04100311f000740821501052103032000113100c06507140140e03070704407410004080d2094240059405419100c1c1c0c54010303120f6140b088110781480c40d0051700d4402c450001030000440c0c0c154141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 671602733 1250 671601483 671601487
    0x50709380a090b1c021309020402040e0403110f0604080a08090a02040903021b0612011401110709050601110a03021203100806010308090f0d240204210b0108010608120c12 75
    0x180b8800d0356405200030042c21100f00b180c080e10b10700850204460715030000e4118007494a40f80013691345030040c40e1071030b10003407015003000c0d1518203407440c00718126401c0d4001801a80e0400c0c0c1c480b0b0601c040020400304101900080c50035032100c2c0d203648500c4138400c00300060080020a2500188000000d5a90040041c0040700c29030900030341d03d4544bc1a1400c243c00110410b5410346400320845413000110301064240b686000c44403c0306100107480c05c0c2c18068205902004410300b4041c001c05443c0e0031b000000c2a04040e000102400705141280266074400e440e00c80100b5000a82e048205034100d040c20350703a039102e0880341d07211034190344003019a104c0c14001100304071500d8050510a2001c0c2c68000d054500c920802018425007040900701074113801003100072050201144c805000c00000140c0340c25035811325103a0150702c104a01c1d49011030258101c4c200101148050300400300f03100240902410244150b03100c03d9421404000300310001002d03900c80c1020701c8110b4220b02200c11483e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 671603983 1250 671602733 671602739
    0xc0909040c0b19110c1809190f112d130e0303090f0102190f0917030d0b030d0914041506081009140c031305010e010207050709380a 58
    0xc00c03815122980c1c80030810300944c40d6011400044c40c0d10071544001c01650422004d40c06210f1100c001404110703a81c042e105441c0d4140f0320010005030201d00c5501d28901080050500038035842140e03501911800f803d80c0700400360866004000103903046040c2042180c40c88000003401071203191108400c40d81070103507940c2c4d580070100185104070341c010309468000840030400343c200c0c800c0f840035031890a61082e19600580c864102d12410100b98217000007956159078204035180bc655040b000141e20020324090021500d002d84044d0b99000e030028400c200049030050525203450241c0c1081051108100040c0d0381c490b08012511f0313605190700660580c0b68540100b2140d400c070380c20441000ba0540000340007059101d4050a61584030b0100c907030340ca234415001443c1e800030701119066406260608003148084c071501107940103080005950b00c10b03614185040032042c3e4060840395182055240321405400504000103080c000448444150481c58082d003014030300301d0300c1e0408903d005c08 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 671605233 1250 671603983 671604007
    0x130203010e0c0f06090a21022d01081005040b030309090a060f060801030b01090902031e2103160c0201200a02130213050f0409050a11090702060c0909040c0b 69
    0x40c2c0c41d4400b61000310425200701e0500104e0311420075a690030450828040203015031f4030300e038412051861980d6842444a94001414000003c2d21031084820301048102e8556001c2410025042007800d0403115498001807030854041c20b403050502481c0c46100c1044140d03424011907842d100700820503903c5081041c1160000c02d0140200c4040da00301c11004202a40242d1105040f280e1094034040503a003003154070703c050a200682281c252084000100201100d8030043c06042d00d04001003280c0c500000501c410f880d8401c100800210040040c0f101411a000c3ca02201e2895810b01142c1c80361301d071004131014849410720381030000c980c0d080200c507010082070060f000343c02102c0049603111540801c0d0b04910071001344d95543c1c0504070b410042420302c542108100c1d040108001204202501d640d81000103044044400304d0304c0c1c52881e1494501221400c3d00180c840c40104460301e088a0340610301e1080c0c4007064441c0a0110000c0c1c02c10020b0305100b8050483c9441c61901c9440400c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 671606483 1250 671605233 671605243
    0x5130b01090605091f031b03020907171005060403020d02060f03040302101a030a1506080312040203010c030509070b0f040b0a020307020301060503010b2805090705040e070f08040b130203010e 84
    0xd030600c04c800090119400c20360300c034081d034688074030700c4030a40340302e480c681e5040582501a80324106580341c0742000009a079034090801e2003000342d40c03147d000c8804500001a49014014540d40484010038014407a9845600035102940d0341135a00c0361190f212400060030a0154803541044401c000080008050b4080f6100b207400655a401380420318242d02c0d03c542c4100540105a013640c031012541000c1455400f1440740001f44100003c0e8450301c03000c550342550711200d03405408541e00d506010441c1000d00c103409101c0410300c0c0401c1903052400c2825100c0c410340c402d903050450049109034440039080c088400522040001559a49540c1000f940700c0d04041e205078800d5103007000001e5039060602030101070340c0c401030442601406252110450003001c000404061080101c0411107413552484140a200c0a44445841e145040c0c006007204100400307260810072180d4a0400c103030340202c0070b503820903070100421360035650310089186160303001e14001c1e60541c01d28990280658000c02c2c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 671607733 1250 671606483 671606489
    0x140c030c010603140706080c0d051e010611070e0f070507060f09060906140f0c0d060306110c1606050301030f020102030909180f0f0d030203040c1a13060c02011205130b010906 77
    0x941710107a64801042d46c0e480400c440540162004000c880401c656582c84980d22040d100b011180d01d4a03120140740c01301e00c0c03d802c040040703000807070a892011820040b507001000b6020a0980502d488000240c400c10050202028820f000c65030504000c0d013034000306504565228200088496414458054103440006aa4151824401504500c9503982582c419140c0828040305920f841c840740440c0e920040d001081e903903a800000c00001c1c0640101c030340345810500042d4644440d81d04075410803c940d41e8181808a00c1c40b010842c20342c21034240d9046a41214003000c0e0400e05000503400d42c401d64480c641d02c07564400800090300644480c0940c0e60a01c04110341e0025881e41b4220760f00d80c0102d01184496020034500c4541c144070380c0085500c503105001510b5001d5440e102e81c0e07442008a0001042048040f400040345480400c1c19001400745141a0752500c900e600041c14020204c40c10580c4141c8520001d013070800c210034020416076210031b140301290383da488180b00502041c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 671608983 1250 671607733 671607773
    0x40905091e1c0302090904110f0a080105010905060105070308060f15030a1a0f0109030b0406060302060c150f01031101080709120516080d080109020d0b0d0b0a05060102030a140c030c010603 83
    0x245249442c0c520902c00e540c0700e504040d0000005440300d44519001d015090381c480d0b07000d040510038112a443d80c0405d10020aa4000045480d506125403034081e21002440c150400c40f0500002c80030907880580c00e45c101d2025912585801c880c6030118084c000d0782000d0a003800070010900040f45a0395105041c80c20340c0c0c2d013061035552043c50400049040c3c04030320a0000c1c801381c4051001c80c0501a9094005105050008266a403640420b9040d0002846131041341c1002018240c0c402150702e10703039801403030107034614442c0d81940da590b20290714244080b4100000e00c070001c6c06043c058840180602640d03040d07882500f88515080daa105028101c800720100c2502000540a50024410700342500640b21203509a0800300008000e400c4003c0341148161a1100d120490726600011a000350107000040d11710720300324858206a503070241c549070455100f000221840c5500104001812031101001c43c1e6072b085041c581880d60082940907a00303035107007a0000082041940b42c00000040b99 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 671610233 1250 671608983 671609023
    0x62803110d1e02100906020705010e040e070308040f080c181e090f100b060a0c0326011d06091503011d010203100909050a080906120103240908040905091e 68
    0x200348200e800c80006d10036600560f200b0b020138401580196410802140003400c0011140c520b10400391500744140d2060301c00c100002018031480500d2004403018000c080c0c001c1c86404401004124103c004507600c1464075450b00204156401c055500c01c1c1d020000352629545050100316180c03140000403441441d8800c034806d249000c812030150450006004250781c1c01c210b10101c042c4c030045400e8200b00c1c20490341d411031161040c012408400d88078514545940a0342c10000310842c0b03070748401080150901c1d90030030405242d4a5101c1682d020400581074892055488c000c02e0142940200054009103541d07034900d016030307055000d90300c51031802d420100481d40d0f4a480360202c4011276030150142c0c0050b0a48800301f04610700400f401e4102401c0180f900d40e00c07034141e100244080c1c108840e5034441034800c4030345003800484807101d0320958008004854041d52442c0580c0300d1840756a08164403140007030540f10040c081308c52008201015002c40d5803c1169054445980840101c404491 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 671611483 1250 671610233 671610259
    0x70210020d02010b030c100e03030c010203190b010c0c06030221010803070606060924050c010f09051605011709070317210f0a0e030c0a050303062803110d1e02 70
    0x170000d6201c60040d4080c280d003140002c00c2808450b40e18810b107a1b6505031104001161140d0400d00c001c5d80320381d4029421440c00e046040005090f10a105840350400200450050100309035034800e00c111941801c0050340c4070040b0440c5030855010700459071045401400010340104084002d24140784120020440117403a01026100d0a00a016003034042042c0d428080040c48480100c1007045080d060040c01d0440c8062028252880d21a90307140c1651030300541e070100402000034801404a00c484040078a080c0710000b80440b004002c0c01c003000b500200428030008082c004640a5900584070000d030090b20821540d05a100c081a40c1070540c40d90003d4985d088010580350040301168003a902c2915100701c404058089040c4200710340c0001c0209403036940d001c001010001e840f40b4041c1d5181d02d4a401004800c4041413481c01003c01c9813030b4008000e01c43c030100303038060301c0c1d00c4580e120781e03610307444007051948201c0300005122080507031710300c0c030358403000c5000324106071085880c2c6001e048 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 671612733 1250 671611483 671611489
    0x62b060207111207090906020d05010308071b05010f050d060b070b100905010605181f0207030c080c03030405090903162f0307120f020d06022709040611070210020d02010b 75
    0x1803040f1007403000e5008510248801051600105090b0b800380c1009801d000b01c04903581c0480d00c0030381c03003103a00c954001101c0d000c100c901040000711500c541170305030860b07242c13a00280041c1182034030700f41045000110004039945a500c0720020b403c0d890505520341c0c0e00340c40c00504400781070b5408420860615000140100030340200b5058485035510b071410040500da0f00155402c080500a42c080c1201c01e40741a8001d00300d071441404103040d4000c00201e895810040d0151034541c22141003504040307107894458070000111070403640b054907801000c3d81c5440f09a030460051541454100001050241c03c0c4a1070004101c5210941412071400340c0d151451030301d000d03642da0001501900000010440f00006d43c0303284070010300604045c0030104080e0300203001c4c0c641c8104203e5403036502007040440d14520803494002c03000c0d44001d4901e914541d10001c0c0c14090b00400c000e0003203481c4c02008070050b083c00c05440c205680078011150000d5440030281d11600d245100c00010340c603017070030900185 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 671613983 1250 671612733 671612749
    0xf1d0402060d020c0109021305150d0804270e0703030806010c0b040b0903040314100c05030f16030914070519050d11031504030c0b0604050c03062b06020711 69
    0x1903005101c02d00c1c010b200d41d00d4001035001000301c01c001c0c0d5a203c1da50b90160b00c550306240c03890324004000103001c4c81c03e00706507d40e19038117042c164040c143c10000c0800007844041203405941c41800c200c1e0f103c101c0514800c40710340b070350071107004101d09081400000c0400015448180c83c4aa100c00c102e65a40400469244000c070002600342c4040360042404203240c05c1415400c003c030380095a00e419203a455008030b40d1031005030310105074081d2180d20f502400c10710508030100018503010303180d400c0041e8406d0741e90b01302410711322011442100d0100ca80d8041c3d0700a4070000d50108a02015081c20b505064840546206060045064008840300041c0f0381c003841e0b0a494000f80001c640c541ca603143c08665968404076107402d48200d03c0c0d009524940304034018841d9110740e032a002180500e203000f800080d4003815890149080a0a02c00c2c001c1c248000d032a0310040a8401b2038094401817192050070b00103c0d2081d02e86044400d08509118403a002401064001c2400750040c0e84203105001d00c070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 671615233 1250 671613983 671613991
    0x408091f122a03091103071e0b07030804060213030c0b07060b0109290424170708040605070e06180108011a0405010810080111040302030d0f0e010c080d05010f1d 71
    0x10100b5407602e1200c0c24080d5100410701da00800c4400c249405010129140001c103411200f02c5268810160491054480310000a03120010302c0d541016071554001d40415000382c0300802c070360303008290920740e41d00c1c07a00d00a00464010740881e040f280d90351314041c1c050780070340c100b07640c4c0508050091005500491b4000b0845000e24007001d1403601c805100480d000c220503039181c08400c20000014980190211503141440c0181030035610910100064101c42c940388130020300d198041c08000d072468200c4140c552054010401141c4e0751b640e564101d4688481d80c8050341c0c0130030081502d5103409030002c0010285442030320f904820781d032945031440354002da1000820504200300014043d81d403182000c1030708421010b00350451240c88034400c07401d4403140c12100b00850380c08902001903207000c000180d2804034a081030860141040d400416408600d130810341403004c1c0f8030401c3d0400884070102c43e02e0050038903042105585648110403504540e1090010001c0b0314030300403008070140e48000e402 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 671616483 1250 671615233 671615291
    0x40e0c03071e080303090c01120b011209061808030717060603150d0c0810180c1403100f05011403060712200c0a06050a060e0408091f12 60
    0x1080c9030802c980d40038007941d85032040d215002c0c48001201c01e400c001550041d40317880090001c0707020007400103141004900c0c1d9695103600746a42c42e05245d0700200d4815910140000101c0c0c0c0c0112810480090000741c42500009030300114110103200c030040140d4042c10302076960b01e030b03880c0c3d075007048107181030040d1855035000404101040781016203c0045e060110094200c1941144075122801035000a0f440700c0e000f41c00110f4207003c800b505108142400000381035924015a0544a69000b013105000b040640050301d90360000550302003100d054030100c140d400340080c10805c00c113507010700350a01c201e001981901d0240c81c0d55203004141e06102d8030441e51000740c00e480c00880b00021300a10a20810103800d01c08808a040d50410014452211907070014070240076070380b400d40b084a40043c044000645001028001c422030700c100c050300715400004160701c804055000803480901c05038008400c01d14300140011064001044001040700f842c03041044800740074460004108929400034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 671617733 1250 671616483 671616493
    0x613030c0309051809070f0812180931050a020f06042d0602011b080c07120e1f0e01031104090204030b010e070c02150c0f01020301090204080708030901020309010c151109040e0c03 79
    0x11000500005402450b4900c4803d00c26040b000c0049580100c007a03a00c81c10082002c3301050080d07800700d000d03903074a014880c036900c003550341911020745480d2001d800902c10010450301303407540d0f9180c0d42501e000d88540c09a80000d1181e900024040f03c0105442e42041c801006001030018010f2244291302c6540d0402c20f01c201c842000e04170b0f07410200610058022078140101004100749000e0a40002c5541c2c4401a500002900304007189207140f140d080c2020011004510f040d50001d80c84410003002e00b40468440718458010030b03180540e4110b0000188007140000c18800c0000c0d015048940045c0564001d840d41c05084910f8440c0b0b01c0060740290700c01c0c40404150ba000340c0200040005102500e10030f040010119080e6131080c0c0c011082d517500071606014013030007802150b004200d503030700561400003101c00103902e0340a480030440c140700000310701106000000340381901400800c0740401103c814501d00d940603410607004e05015038541401d410000d04e0024a125200c0e000400800c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 671618983 1250 671617733 671617753
    0x121e020706060b210702030c120703020616020304151e02150c0304080f0a021006030303050601090902041a0306150304060c0306050d1113022107110613030c0309051809070f08 77
    0x901519405440e90717003140300400501440017024000643c500355480d444941c0c61950f818000c0c58070310017070500030b0f01120030b44110040540000450381120b410090195100e2224a4155001e0900306410042483c4050603200c0175517000c650100c040548841400703181e119402e85181070b0104550041007403004019080d00d0311920740150500390640d2040310080c1b9001c1c2d8000d41030303c80c903a0049002c02d8075103040c86039561304407400038090320641380c0c118182413170000f1205820f00e122030700b0701c1402e000101281ca1500c440304520843c0f600d0305181d6580b41000d2170018002c0c080c101c004000640303003c001182c6032501c0808101c4581d08070807a10042c003040300c10403060340317150480e100170741e0717420000316100441c900001034524094034202ca12602d050030000c0c01044611f20500b42c241c0280c02007210307017801507008114564042c6003800741b0441514050365051107607045698480300350980030410442c22400356104a2401d030650301c40540c1c409120484510328040c82002e508011409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 671620233 1250 671618983 671619037
    0x1081603050a201317030f0702131a09010603091109071b0b06040b0105120601210606051e07051924020304020f1c02010c0203072607050306100303121e020706060b 72
    0x41c060b401c2c002094a000c1c2b00007411000210313403880a0f500342c0c801c0712108220443c5031201040e40140305034201403000b0f0000b507071203070f8291242c2003031039128002c0d05010400b0740d80300304460344040d442c031800303906803440783e05044121002c1290300c6d9204a082841d010481d5102d442940e5018402100f0301d07040d900c904006641c12200310400d0200b80d04240100199104e541c01001300500c082d865882e1366403020020b010031140001915280b405040008000054002490708454060b103210010400e16900c0d000202d4054907140000500c002035904040400d81d500540c041c61007203441c010781750b9030202806401030512002c048040c8041c2d44031350155005000705000c40c0e01c01402d80320a50380b2055040504034003007580c3c0500e580300384d844c40c01d001c00400c20f036005800300720010909c1749880a842418820346003c020100914034624184150641d0000100100344040c00c020440a00069070000e412000d4180c0c0c42034200200007030007025030b40884680d4182d00b070821204100342819 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 671621483 1250 671620233 671620237
    0xa0e1c0f0c020616030e15070b15103b01030b0301110307082406030c0901030e0d0206100e0903030109110c03070b1501081603050a201317030f 63
    0x450414816010001001a50b6043c001e04221400d030441200c5000035040007042c1501d004103080c010364040c09040b004284a100340c40705031317a0010071901c042d81c443c010300d00001c000c072280c1034100101c1001840d015030042c0710070700e0904000c0385440e207041c1c851381c20b260451031881384940f40a044000e510a01d51180c3c104118400780a00046003c07004070101d0119640100d40c1c1c80c001174265014040d5480501201e2444d0744d981c0c42d0503d640c0610200010940d2002030301e001c047e020005412030445e40240c10442005018506446102101c0c03031029499100443e90704681141c6014046104103100318028090b000240007581503a080998070780042c01d1aa100094080090000d000006010801044024461080c80c40542030200c01c1d2044161010740301c906210403041003200085a405858ac400e003c0303032030007150035107031031100e440103111445000307200600030358109120140e480020010801010302c0304034001d9035034043e400031162003e1100303200c0c1c004111034a50300b402140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 671622733 1250 671621483 671621507
    0xe011d150903010c020a080d05250c1211071412070f09140402032109060406181703040b030919032303060d06090f08120a0e1c 56
    0x2a00405114480000032640d19001151080c000000503500304a82803c3c0528415024140020301c065000c9548400080c01503034080c0e0b004a40d0358000038460b9410f1b01c8944880000110160740c0c241c642c001c000d1040c10009016100c040e001c0b1409102c1602c10000030b51001c413a50042e1108500306030400c2804030304000d171203a0081605804001a440038000207000300010000b0181c45441c04906c0c40039904010f00021030a07902e00e041202580300441d40301c8400b103040c10611804241d0a906e007035540070382200e0503003140001c100881e6594000003d8107011103541d5140074101e07502c4089200c041c02d4540500c2d05504284001c0082950f903002468005003140140d8016500915007007502000c0b442e4154000703035419081a000240b5805400301504083e1041803031860081c01044101d20500c00040200b2741d110078900520015070102000035500c000c009580702d0b00702d01500907421081d28072920880c900300178407d400c680014040300e5a00d810903d00103140888400b9501002652 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 671623983 1250 671622733 671622767
    0x5011103040302151308061617070f03090c091d03070c030b0c07051b1212031b04090903080405070e07020c09070e1504060f21090201050d1e0b040c0e01 67
    0x4005170705000c0303040461501800c0c140c802003413540b4041c404180da03101a00e6800d8140511460711103001002d4614460b0721107014140b20f584801413600c1140106000c40007e4071444550381c0108840d8181e4000e0004031344484150900c1410300e100c42c82e105d1041e000010503001001408000144407000b0260f840849120081d0a0602079120700381814283c400d03018a407808040d41c103582d4900030a041250038034180080174465921241b0b04820300c00030345a128a005417403c5a13121022090440d00640b06460091026050034a030151080c40c01f40d80c100d0300307405402408108012100c134520f10840007a4001c01c201c080c800b0074400758200252030300040241700c0380060607a85582c0d648111032003070801c055075214603142e40104100300e044003103410040383c160381d00503046403401740380c1c081582400005026402d52006039060303c24505103400322800c0a1a00510700855518a46144032802d01808941e0200d4100402c8070340c01064000800c00284200c1401c0d4801d4026051f421520 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 671625233 1250 671623983 671623987
    0xf06070b01030c030b0f04030c03181809050c0105030c07030507020a050306091b0d03051b010b1e041b050304060b1c060204050f15030403050306030304170f070501110304030215 78
    0x1038a90102220090700150303820b400f007241c10401c000380c000e40c0d917a00403802c03594842e1a0915039070040201303082c100c010b01048101403242c5081c19140f482d010007010045501d075544089608450058003900707400b41c1e401c1c040c1d06004411540110f0880b0310500001700083e240020595065132950041002a82c000b00da000010079291001c2110342e0050441c00010b2809140c00040000700c41710351603809001703140380080c1d5000650041c06952900340701c00c142d403e050500e42c8416006107003254009901c20058000c1100c860030119007058000001d84041c0184400c062580300c070001c080305114000b07081080090049040c3d91300c54500f0702002000c3c1a0751450804520030382012740341040d204180c0c0000c2c1081503240040312040c1140040c0c0d960615400d1900c001900d5000050002d0180500000001d8059809000710b03406007d02031021008103440c04100e65950812100c9022180700390040810303158099956290813603250001145000d0661707080c40000900d101c01e0796846001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 671626483 1250 671625233 671625247
    0x21e070501020f0409240503031b150c0a0206070305010b030123131505030d0f05070c0302090403110f06040809040902060706020f03060a0e070e040905150106030f061d060f06 77
    0x7070f00e004100800c4520000305110185038403803001e0011032010107a020f0395a1400f04060789011098469030700390031291400d55079464200c0781c102003c082146880741a0442080403448a85010b0000038900768202c4c1e0707540c3e640b00c4041d8102c0d5000c2c050090000ca007880100300a8032400b201e42d0310030f1117407901114486801004030708850b1034303002201406a11010010078502d40c1c8440715005010490051240da03640c0b60014102c203500072000402c001300007510005000200354031800656010309164458075060030010720303810005280641501070006c6088403d0780010300c0901494120303c84078513124810040000400300301c182240c100c03409205000c0465042e1001e0650400551035a0307680c0c1c50064104004d5030007030b80012071000c15030401d00c010107074400e120301400641a640001d1a04160610900c1d04540540d0213180c18440030001c179a0a500d0313080000e82510f54035050158646920422280c030300500305644525040ba40040c0052402104008503050050038141c50105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 671627733 1250 671626483 671626507
    0x615010315180b01091508040c080a0b06041a030606100306080a06020d0b030a030e061b060406200405061c060f0b04031115120601120f1a010201021e07050102 70
    0x180302da101c0d50440b007201900414451403805840101c407400d1a10b155640d080500824a014140300c071724040200c1e00001900300030700b004c036060250100d0403c80d081c002c09445d145120b110200c525500881c00c0500120324030300d00170140300403580001d01402e4541e8410041c000303405c00c09040f00d01007507111040041d88100500501130f10901881c005a0750703042d0f200100d819030303414441c0f00c0d020758032000044002c00d82c0118445800b2000701c030750b1a602c00d0300e80d0899462400380c44240b03c40740260000d200802013142d001d0b0900300c1e9029404030b0f0011449601e03807001d00581c455250800380c1001b40061400000070faa21008090341c0000841795111104042582039a400c2500c10700d200203010300500400c2c00c02070025080841da0946400c1040d02050450700520f1710b406000e000c1100400d8890b030050748491180d90702070f001005083d1034441408003400440403c145600e26041c040c2c2da07170754818021541d03100d20210312604802c44140e42d50695601488007600c8556003401445400c2c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 671628983 1250 671627733 671627771
    0xd050603070f030b040b1005090118021c02282715080106020f011a010302181e0114030c07020d1b031401050a151505040b0c0105090f010b0306150103 66
    0x103002e910301c01a1445c0038680340b0b200b041d01910071090480c4283c01005544d032600c081505441d049134545d0781254072580d050019014aa102c0440c0c0320180c40c1e1180540307210b40c041c0048075081c203126440c038a030040503e807014184280000015030348281c0180c9d20345891040c01461140d101c402094030b941c5190128803690004400e5001882c241c00400000f5410040303802c8003250540200800c10956400c11840c941d03802080b414036070046103850340f241000d804080e51850182030301040090407a070601c05070b401d40c450b40f07003c103103032039202e03103070b13001940709072881a0102c0c422146440c4007034003003000c00c00420034202c03641048940340c407600c410f6401ca104010f40c4500000486941c10070315440c04c0d039000805c2140c0b198905034184201c00304081c101811074070304500c1104040324094085405224a411a4589440000d9030b449081d20541c01b1310300c00c00c90382c0c0076102c03000c0c442c01c440ea00762a005503201d64154042030200b0f00c0104114001d00352007a05050020304500d4460b0780010780 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 671630233 1250 671628983 671628989
    0x80a1a030703111f0503070c03020c09012615310302010207170310061407060e151e1b071a01060206130305040b16021302031012080d050603070f 64
    0x511040014545800c1854004404c681c03e0141d1089400a010380140309000041501d0208520072a02d4030a00d0300900804028680c0640500020341e181e80d648101403900c44400280243c1c42c83c012000341e440400e0310b41c04080f4405101038581c0341c45604039542c0000300d486120844030400743c10907800c490060441c070f0310b1081d00003686491203410031000a526402c0d1402848104108012005111034100d401742d505904155005901703400c05840ca40c01001402004a0300c0c20300304c11400c0b6000118400300c240b10002054080c0e45a0a1202c400035a12000908548103403000c201c01c5411801c0244000345402540c6082030510b40314a00e0661003a0010014211700c5401071100c5035041c8291075000140b56403400301e0004980e40144542f01e940302c0c9141e1900c020650a1b403031415404908a5103800500f0388100d02d000c0d146c048001e62007912811165100281c0000750040c92002e1500d405812008942c00c1503400d203011409040020110303035060040b60b0380824980108400e05000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 671631483 1250 671630233 671630243
    0x711031c0903150c20010e07080a17070201021b01121a010f020105060a05010c110409080309010b0a03080409090204060f080c041811130e0d050306011d01080a1a030703 74
    0x7949145040034207041c010160325100041c1481d80e41031580390800443c22002c140d80d00c00302c1c0c56084103a24280140107188a0fa07049000c1c6076000100d440f80041c8011006000310301144001c000f0300d010140e00e204041d0001c0c0982c0100062000036401e030201c1e480c0090060400c540440d0400c002c003812501581d00b801d8110f007121041c035403a941d00850815140d02140020001c0e4101a0000ba900007a181f04150410031328091110030000032600c400d0301d005001c0d08c2806144060b2801d1500c0744c0040b00c1107601c0d0b603c1c00d0900c42d120704d40400c0080890750002e12880ca010b0074032840b0405442c204100380e070000c0d12158001240d0f09801007180040c250080503003558104102040141d4904121a03001c0c8241c10b13081c0b0300400d082c03403207142d6115411100e000340f04040d05800d001500e90555103030000c3c0144c0e9501c0e040103406c50b00540c031400d000d9031444d40020a0018180742460001102800102004001954020a90702048891181c1009182900e400400080c80c0c2003980c0c00c1160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 671632733 1250 671631483 671631497
    0xe0607050403110306061f031404060501080d05030f0403032c0106061b0231090c170307150b0307090e01021b07080d050d1b0905030609030c030711031c 67
    0x414084149008104103d04a0103021142800c41c006107254901d03145140405500a220311111402a4401c1200e249091740003140e615041c20103000074002480b50321018003441d00b048410b1403042e0216481080354051100380c2d521244c50403030040142d55400d034264410403020743c013416101c0340c6002c2c4d01c0080c50000b1a460b400c0001c001e01100d0300f203c42d1000292101c0d9404010323500d000c0c00c41d03c0501a00f000401c400b005450416034104022007841c041450012020b0611040f100c840b41130350300c072041b1401000396000715070740e4a10442034080d0540704100714080c0010601c0d00070aa480d800202100c24040e00d82c01804112110300400c01c0380307690b00003803201170340440c9078490300c8404c1c0300d001038640300340383c20841e688401c01c0d0340d6544100040003403000340ba0901d961002e6800a20601040c049040c42100504809428082d5a100b0310418001880512000046821011550300a18204001c0c0d41c0c501c41006003212a030351345809000003d5208113600010403450150f0350340e03401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 671633983 1250 671632733 671632739
    0x7050601090605040915020c0321150f131e02390604030c02040f05070302030a0e03030108070e100e1314030405060a0806040615110c0906030a12030e06070504 70
    0x1241c0b2a6401107005a05100c1600e000c42c0c0450804440c00c00c4000002d80c0d41c0c240300310241e056110f002407000c180d02a110313100da0003000324200b0a2194a1a400394071680d50040104901c0385158a080799010455655240303569415401995500010092101443e200e42d00250140e0300109003690121000e1031459511800942ea019441e104000446803c0b0303614010568507203500900103400d00c503c0d468020215107541c0d000c18410381c00130008001c9410151030040280d40141c920b034225070b003807030789903903d82c0c0c0301104a034101d40040d4000c015042c80c0071602c0381e00003030007000015481a003030400507000c00740040107403017491343c810354450b400700702e15009140a0400c022162594802d100600082c1c076800c007100c066081d02e0410441e542d54100c0042d000d04000d0f00f00384060051010483c2c42150000100080c00c002c03003094501c03c0c0782804c24090b160a040b81c40ca0b42c03507488007400c280402c422800042100d00785150100b01001c0105a044c43c01c10192400e000241c0c00050130 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 671635233 1250 671633983 671633999
    0xe21090d02060705490c170c0d030506011d090a0902010201090206040f030b071e050c030712080a0f14040f05070806010305031902030c12090a0806040c14010906021c1407050601 78
    0x4a80001041a1905a102a02d40700280003486c4054010300c0176032201d2549000034120400c1d500b80503500740440d504000c0c4464014098403007542c0d10381c0070403003034980d204a80605c500503200b00c18019101d04490b43d1118145030183c00410020781c15550f079041d004001d070f26400c0050001e810003610f601410f40ca54a0311400540c4010083e0040142c05c40c001c894103280c1401699001201d842c00d00e4139809489221030440c070801c80003c00e040c2c0c03034014100c01541c20148540c45001c81e08820054642c0e80084841a9000801e000b00c0390045080042c000a40a900c001040d81c022000c032071001b52210300346031500c0d41c20707041590340340c0c400300340c0065110107580d0001c03581941d8400343d0300701280d030b408683c3e9032040300400340400603010609042c0c07600c0380140e00c0000c00c03240c02110b405040904250000700c90602411040e90a201020322032540140c0d540300c1110510342c01010311280d100301d06d1091810300c5040d4400c05c4814000c207245011050013501c4001c1c0600040c1643c1d501d0402c01c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 671636483 1250 671635233 671635333
    0xf03180f030f090f0a1d1504090c031203020f07050a02040b0d0f171c05060a051903081c06150e030f030f0c0c040e21090d02060705 58
    0x484480303900c1007149202c01940c5400f621850344003030741c0071a140d00c2040006680d0390141d4026001c0c150318400d5403210151841e41490160001c6803014890154080501090301c8010102400030422654108001051030681a29641c41840c005023000c002607802103584e4031612003a030f200e601c401c894609600e814451294186012a400228134500c1d0b035500b400039010040203400450301d00070545045580ca01107901c140540301699480da071a0404060050006483c4980104009040491b890400700b42180803640b2100b03501071071900d15900d15415520541f4503166404401c0d401045100c8903001e413a01420242800060605802c040100710600403481140300e60f2000a2180d0b0301400881101c070700703100c0e10000599409810024034900074400c00d01d40d400500e8041c04c40b021280100769680303041c110342a83c07400101c910700e0000b218000d244815078045004610400140303043c1c00145141445201038514108041c2141c2c40b194402246901102c203140210141c201d5125803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 671637733 1250 671636483 671636503
    0x2508070b09070501081009021803010213030506060a0b030609190207060b09060910050f0409051e0618070510111608160806070305040314130e090c03150c0f0318 71
    0xa810354503490406441d42c540615441516450ba42c000b03800d035049607a49c2c1c111610100058025581e418691100f2110b94183c1c0c0f01c03c0c2c0d41ba0081c00007003062494200300d02d404aa9012004a0030364580300204400520068225a0300442818035400c90b01594006010000c0c0900341c0014040e030442e0521210901c01044244103410400130084d0841c1c4605030329050b50b2043e52101c1041c14020003050003405060401b525921500c16140405680741c2100032209112100395030740c41c0c46080c0038920f020b10b89000d01e4256003203a001030115080c030340c1d598108603c01e03141c280030813041100c459041c0002e45400b04ca0641198609200311501001154007154582e038904d50414941116581c40b2038000d04144101a103883c0441d0626100751445481c1e61b8402000c0d13a524003045012080c00c6000e840380096502e0050005480c094020800c0d01407450050050040031a2914034041003070001400d5082010041c0112155042c01001070b51040c5c20304003403407040c0300e0001681850803080c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 671638983 1250 671637733 671637737
    0x601080c09180c04050a1412070e0c03060d061b1e051606061a1801090501230f04141207030206120601020a0b0702010c08070503010b2508070b09070501 67
    0x10450401e5100c0b04a07045021400c2c4020701c595480b400e8494509215035800b0030b40c0555840c0010445800c5a820001101c40c00c0f540460031203c00640c59454080314841c4068040d400e000082400380094002c581c480d00c001d114002c280d07403e44d074200c100c4003004518240b070507064170102c5210340c020102011054490100d0030344402d42c800020701b41c0c8074050760707800780f003495040e80c004014841c1c010b01d02622802d51000a0a182e4100e64150b40d040241010302140610324490059401030801d24103036038040e0344600d40c108103030600419074030840856641c840810018090a822504090300c040c0000381d070b940503a0280341c003c0151079054030b240b01029400080b41000180e03101030454128000c40c1c500404c0f540c0d60080180e00382000c0c0304028054410000c2003054844e419400210445160303110103480744c90310b0070102c0e0580001d00403205001001c0091724500c04031040019040d405d40080300144694580d1007640d0741d001040201c1e140d5048006200a0020610211340900800c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 671640233 1250 671638983 671638987
    0x21080601090b0f070503070803091005130213020a020c041509241205011b0c050610050907030e0a080d09260a030b0310060e090c09040503070327030b0601080c 70
    0x4880b02600703205103070b0041e00c0e0400005041081150500650740c00f1a00318152540301e141c5080c216854099100060329402e06d840001001c0c9181d11500480907071f00900400c070f06030007801d244802580241111004d41c0700d40b448408079640c581c040c0041e031507030782200f020040780307810101825554101c00e81508004005a002c0c000c200517101030301100c02c1c00c09080c6027000e0500b00b81e80109401152911034050300b205401280d90401120000d2610407000c4400641e20450201c10118031801256440b24135803000c507107924400d4101002600c0c485042c0c4045011030360b071b01c54560b80078043d6250055101c0b20b420f81405500342c10100e0344d45441c2d81c42241079480e04066005072241c0c40b00300c0c0a140d510074000c800703520700f0002c41e900c40c00c00074020050943c039614140da0901c011101494a0b01c203056540d4550f0400c20810b40c0500e92000046003802855607050300c00d4a0b01514401c06030710030314047c20300007040c40c6030f0304c00840c003415445182d802d0484c001002c484000300a04110041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 671641483 1250 671640233 671640239
    0x5070e030f071d130c09060302150703020c06030a020d0911040615170a0b1903151104090c0201090210110106050d030804060e0705030a05030415091206182108060109 73
    0x107000000401d0a06860754900d40c0d20501130000010a00034080c2000c1402a004a4904125885001542c0c000c030b980d0180e1165803121001d0920864500500603084104e8410140c01c1481c00b950700207150f01409800c100655484000300d40004806442c200d11880283c645400c241c41610043c141e0920140003804104030701400315448280d05182d0032009000148040703006911403440801c0080c14040c07074100c1da0700b4081c45101180030566002da01107400d10340b60581c2d072040280c4083e100014070b04140c40c0000d200020640c03191290159500d8034990b800680e600310007245920101c0e02c0f08075401454005041c2190b03c10b070803c038000c024103034080001c00d800141172544181e1200c00415079801c1c1c84412420030440e03501054040c070a1058200c1049070102c054419a0ba801410b01c650b072100c00c104840b18a00c40c0714554003544401d070344002040c00e40d00066002030b140c0401c044030541950346c00c1e04442d041c02d25030241801f240d1030610302552003404160030450910f8860410f82c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 671642733 1250 671641483 671641499
    0x50a0309030302310527070525030201361104050708010f0501051e0c0a0803070201090b090c060406080702010b0a0306020d0c033b06010e190e06040b04031205070e030f07 75
    0x740c0546ca0842c81c4640000201464405c1040301e00ca4a950b0749041d03610b00300000d25008500040c0d204a002d03508280c401250301c0c60426000c806002150342e442d10352290307841e440448418001c2e0503604108051070102a9454900801d40a0a0241c1e641d2883e507141c503d0400003203201d500268100f05041100c2c4128441003201c0840c14450001e02d50b94514181145c1441c01d00301ca80c004110b1a008401c00020b15010340c01203440714002c80e024801641c401840e542c4408000c3c0038950b204c01d0921090001c0d901c00c4a00c02d50280042c00009590702620b400101010103da02c03c44081c1d800203280c0502e007803180521a4941030a0070184035151030400340e10403606880e20f440100000fa9001049803824101007075103c1000365094401c4c81d61522091086003a084400038120340c10401302203c8500c66200388030103e0500006030046441d1507580e03420545000c0c0041d8100030100103017034a5040390b44241c6018840d0307603e40a0300d00d00d007030303060500304080200c0740880c58011140411044c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 671643983 1250 671642733 671642779
    0x40b010306020d0216060e0c040608060109020717040f030606120209040b0702120319182109080f0714120705060a050c0706020f1903050a03090303023105 68
    0x35030140015803600c044403600c3c4000d01450035200c084c940001a803505200780c0e640038942c0e107200b06041d031f202032007584288400c1d038009220350241640140010400d000d03c0b9405032003094440c1810748040d1400c0025030420303810a400c40115584600002c01c100000c40c40346100030009841d907624582c0d010f40004261440082020303107100460b000040d0003e02c00c0c04480013410051a8203500e905000030021001001ea144c01c3c8076480c034010b10101c0b005401d4080e0303001c25500180350303d412420400100c81400d6403040c1c00050004520010803240c106004107442a5691401070000c50302d08960781d0401119044558081c14483d010701501c0d1402143d88815035400b501d00380c3d6501002c501c102c0d9288290b41c1807221500a100021918076800700d00c01d14922010300448d00c00c2645018989288264104024040b583c100140b0002e98023907009461020f00a060040c00d100c01010b10240c244609901c82441a540e00744980c58412284841130161006807800341010030600c00300c600f01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 671645233 1250 671643983 671643989
    0x9030215030f100803070219090204170c060304150b0d020603010303020604110a0b0a08130602030910140601050a08060102070f08071a0a051c0605060a0f17090606010c0203071a030108070e040b01 86
    0x83da1000c023645001c103034034030103c00042c0601d140455030345580d49000304014420701403c9040f40103980c440030350b500e8580c0c00d036030266400c032200c4c81609560f1001d90005000a40360030307800000380e003204d0340580d450001450085000781c02074042480e1900c1d20406023405690b10394483c070312a11081c03003c0350b10141504c0900800341840940c580780d803110302c1b40740b1402150050489000104001c01110041201c2c9400007070703060148420415080c03030381d02818048842c140058014404555580d102d0310016810a00600640b80390039101d101454100401c0e410030161355014610030420040c40040141092852048031410010103010041c0188140d03076070155080407099040c814820660703c04001070400030041c903230703503e543d8101420060040b800d90000c82e081441d12105104642d20051054400e200903120b583e0700d00740195112080d610003683c052181140100c2c81c1100c081211001003612046640c4940c5080126480e05006402015000340704405001c006043d8410442c19 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 671646483 1250 671645233 671645239
    0x19122103050f0a1104270609060806010e0106050f0318100204150e030307030e1c120f0c020a051507050312040b07090f0b0d0f3608030f060109030215030f1008030702 73
    0x284924400c0310940c1d0802c07000075041e006c3d103017490010b00304401c1d9024000326900e603c1a242a60303038462400076500d41c04d1040c0c2c40850001c128200500799144000c507444104850134042c280401d42038540b406c03808800e424025540002c00b803000c070081e1a0380210381c0e116460800955801c06000c03a071a8001c10788020203200c4444d8122240c0d0b80d4000309181503484043da0750080c007d880c20941c1c8108030392492800412001000c49216130300c10b04140c008140c0103481092464980018008011880c40100202b101d0501c8500000b44041c03009119200e210b5080081c1740c100f50401942c1c00c0b40183c003103420300c81008020401c04044a90210803034600c07251460303c445041c203420b800b4000c2800321405151510329802c64400703030040d5030b06510070011942c204510314581c9030f95880180c2030b03000d81040002e10009141005442e151980110f062408a45040d0b495011588007500c558031902048400f10030014042c0d405100d46502c620003a6000003041d01d0706003070030344910030504040c0c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 671647733 1250 671646483 671646509
    0x10c2a051009050c030a060f050a05011217040b0417060105040b09130836040b0a050d140d3603030c02031e030406030b19122103050f0a1104 62
    0x1805014020751305071440280075a10036400c0340ca00500200710580c0c462031b840d4034040c040b0b10054035912540341030b40e41e40a03034040b09400b01d8880d18151400704081002d801d40c100f20104007940c291011304024081079420680b50b905400d0746908002c8160030841c0100e18241d10486166103074004d0b0341d04881800380c5041c0c02d500d1410991540d00c00c03990314410303c0200104220408030054011800741001141c02d8159240440410083c1c0d5020450f4590250304080c1c00d10851400652a0042511551070b0303502110100d884c42c0d06012811800314042012112402886001c1c00c07070f500c258400d0a000354400c5000003825812441450001608001d00000d0380030031900c0401080d103065500d00ca176280c0300c002c4007007100d507030780c0c410b000d0b12000900b8950410050b00b00b05200e8543e040250400120940c100b400e440c2c12440011025100130101d01451510b1042206080030182480d80d00495289020106800c0500e0301401c03010100389046288000d000c8403400b0f4400b82c03403484080d68 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 671648983 1250 671647733 671647751
    0xa0c0b07051908010503010c0c05070b1c09350706020313020d1b0e1e190221010b0702090613020409060e0a061a040323010c2a0510 58
    0x210103006502d00c1100000704000d00c0c0e03a190783c000d050381d412280d0450013806280b141403c1258440e4418100502d181e0007000c0a0003444507a030080c0c0282d9030440c080c0c27250003c101441c102039407a03411055a041e05020340742c142a9070801c030781088c0c032003540410207484d20607440e50312003c0c441c109010709060b0303003c4041440220ba80700140c400d42c0e0020840c0d044158941000901d012903c8010a124030350860b000550ba10010041c0340700341ca607800c0e003241c40c44180004000144004080f0b00ca1b0300001d0001c49a90701039032015268680d082c80c0c550319040ea4507072100040c0b20043c1c10610707209905019040060355080c8840380d002200b80c0707000300000101001440a4000c5411442085041071400b05050312121003070345c0b151000301000c3c06103035640c00e6281ba03010b135850540c860401040000340080307200b010710000101c40420b01040201d03035400c0002c5c01c40e0301e2060914001969592000d590f404e5182c0001c1d0406000d0f50310603218420307039070b5083d07441c1640700f90212120340300e440d26 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 671650233 1250 671648983 671648987
    0x110604031707020f04050a06141503040b060d1502030604060603020712030c110712060518330702100b0109051e03011b020a050f0a03050702010c1103030c030408070b0a0c0b07 77
    0xd11a080f07800342c002d014504100f042c500180425000c2c2140304860605d5a181514008403d03108020320b01c0c1c0c020f46190cc0b582c507201001d11004101541200455482c00d00280340c12040100c0c0d02030050005880b8209102080250b40c481c5d4002402c01d801808410046180c81c01140400091401c0000341041095420b480b0070010102400c0140204000021001d007101c000c0c03600c56200341c5080003680d54552103004c803041c0400900400da4001c043c95072824140c84800500e50741c00e010b411540d4440a1043c480100c1c0441740d00e0016082003d02030300901d040d004082c001002400d0000c003060801c0040303482d240d00c001c640c02c04005954008041c949083d80181001030112040d80f0076180c00b5074019550740f011340003ca50328070a4500d0f005444002013107500341c407a410350b50149049099001115100c1c0c0c800303402d8070205203000f80b211099030200000e11480202c503016549032882c015040f800c024040e4095401c000302040041081c0364049948510386510142d00c1e12a921031402c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 671651483 1250 671650233 671650249
    0x1090b0a050a211a09130f080c03030403090305190503090d020607150c090902090114070203160f1502030906160317070503060406090902011d01031e020711060403170702 75
    0x82c01a1005006419190b110301d25000004413107105400089615003010a1281071a030440f4030307018028801c001745c000a50703501103801c13285009000c114108244428500e06540c02502d007100401c950050400401c007050050441081c0c0d0800c8401091388c2c1516119240c4c41407a4000d0301c10b82c03003148500c046688140c1500c00d4103801080030f410305100481000020103940303440f6404942150400184900107000311050007906a6581e8849030007900c403000e07640c0024200f26418021040d808088480082e040f200402d22034845040843c9400d8049020300e155030302080440d0000c0280c40d01c151250720498000458018118100c0952810107c1e0302c0142c0302c034001c0f05071091405118803140c0c004003550040d0800c03107042000541e9011410111902038130001d02180c030030b1803c000f501c011210040e045620606002c180e489050303408405460070030103201d2625601055103018002030446284c91040281c034450b240c85d08588a13440b0b01041198001e801034000a6103030b0440d110707252 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 671652733 1250 671651483 671651507
    0x904030f0f2322060207031e050d02010b130b0117040203070b0f0c0705120a170c03040b0712020a0b0f040302100e0f0105161d040b090c130501090b0a050a 68
    0x780086a00180300c2450010392048200b0b100304804200080f00440031079068000f10344180d0000d062032803031a45c55500c450108000c4204800c80500d50f60b001c240d052004903542500341e800056030a032550f040212a12021001e0200c0c03d203455940800c5076000080721280000c0c142c03001585582c0d03440003d103410040d4001b18101140811807144600ca40c0c4064800303444118240c8040341e4890342400000781e0b02c0780c54507403964082c41d01a030106020340401d091002c0301d15070051a1000d0b03110b020340f442d40f09602016030018000707a0031003030002e12144507808241a1000d040242c2d429102c0d46506d4a010380700c034840c2034140c400f00d01010b0080001000c44080c43d001440841c8007140e07a26210b10b0401c91100e05c41d424000040c0d50200ba00079688a03503441c5449940c0e000c213001380202100000c1d10300f0070f40c01507501c0000807569618030030068030400e100000103558002c0c44011400604850b03000a0510004200c140140d000c180f00740c03060603e182c40d100c1e84402c107411084402d010030394 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 671653983 1250 671652733 671652767
    0x3010204030b040b01080a0b060105032707030606090218100207030c0b04030312140c07050a1506080d030c050f0309150c0c0c0d0203030403060b01051c05040308060904030f0f 77
    0x390010421a100004030b2240d030241c0012071441c2c0e40d4010b11511451060002001a49060b000441540c01907000d903400510200a00841d00701c180140c50101d8590760300d254259001a508204104490203200003a05509106504181180210140f1452820b029501c40e1601d8044030040d68400c2003041c1c000c54100e2500071801c2c0d928203107400035a00600040d80040d2114007003459003680e03406041c948001001000c0c2e0660341d92282c10b24541c101c4c500813121800740c140c00030042000000301d00011800752100007012031a140b1110314020411458030700f07150030040d80b00c1e5841d400c00199124240c16050300e036a251740c3d103c0c80d40d05000c0b04c407000c0e00e040042130007440507a61504e00980100180d035800c442d8540f0b85102000700b144480000290306500c00c010610014000d174022242c0508107041030b605040e10b010003d41010082810b070300c205640c550802c810f041d8000341caaa0442c40546800c0300c1410240c030300078900d0500c259a041071090f040c2e030703036080c0a00c14251609240000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 671655233 1250 671653983 671653987
    0x1e060f09060c1002070b151014070b0f0121080403060504081b0a02040b0d0803130503040e090a12171503031c0912021903030e01060504022107080907051e030102 71
    0x402890f0003e400951050350503d80c540c0004086aa034490300000103000244106072a280554044441c0703032000c18540c1d04071a0910000c0c000540406034a8061540d6a0550180b903040c0300c410750030308800c0c88201c0c0804903000d1110020569140c100c60a0b250468800302d926035503414001010b10503c408404504180494a51149404661800c000d0700c200c900307114803010f07001080011410104041c08064040001c200e161400007040b000880c82030080d00d0500e40d45143c24007000e20100c51070b122540105408008024000c45080c00c01c0c0084e0508004100b882149506040c5000780007484101c4c0b801d002c4c004039901002034401d4074403048601202d590b4032510040c040c0c4019001100c2c2d485038a566100c0150000c54030380b80400c180c40c0c085000c000c01d9242100540803012940e0520756a401012581e91228001400c03600da0080040c4140065881d481c000701800410140400c1781000a0146a400c0801c1c090101c40341120400303003403c10010140304100300401c86039415880 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 671656483 1250 671655233 671655253
    0x41d0c1b03030403110705060d02070c0819060501060516030f11060c1210030321110f1c05060109050d110a030f020a080c060328090507051e060f09060c 67
    0x100000640c803d51003a510300c01490010285c90383d90791160300074a40e0218060260703941c031110507805040b400d4050954588400d50710040c09040c92250450f010706000000361140038899140585401460246011403a282c0d54015809180028002c0141005400350050098602c51f0f103200c0d4034200b165065500500340030010401c0ea90084085040e0883d0700000600d480441540ca001100d805450320003440d082180b2140c61040c0e98140105200d036035500300c4a00c6d20ed2900640700c0003140c020204c2c6d8880c004c01b045d00d20000424200c042d0142880200046668003000440807900c09403403480c0711417000c1c0742c01d1704c840d4880d04415402020658002041c482d90312a8101c50600a441d00040240c07202c010b2510750344207141d1181c103c0c60070400300e1035020b0221030f0068602c1c0241c0316140070300e0401008000b03465012400b81d4041d4040c5605200610307101440c4000d07030703450380201d1081488400101d0b000e070098000c2c3ca2403092010450341c0481d26803000301c9480700c40c1e0b8004c1e6448012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 671657733 1250 671656483 671656537
    0xc071502030709170c06090a09020a02030a09080f0d0f021005040501140c0f030114060c01020a0c0b07020313090203100503071203030c080114121903021b06041d0c 72
    0x81164110b002580704107002680007615480d914440c0d441c42c018000c09040c00d0240100c07540b081090030f030440c0e89101d001911481c688007410b01c20385613601a41c1e071144040700052041d5000d0b004a07450360001c40d401300154200090501946185007804402a000c01c00181d0405681c466070300c01ea035003001d04000410006502854031041034100c001c2d0300ba1924612008540240c0f400602c14980420051081d05600744141c0000302c401000c551604049840c01826030b0008100c00020400040ea42d004000c01095070a40c4091503100650070310074101020b12070400903114040103142d0001c0402c503606a00008003010f0040503086400c21640d5401d0140400030052084d000245080c424001c2984624600750480d10302489902d0104002000c2180740680d056200e95244100d10b00e01d0380b6a4881295240c525010740c020f001082800190006001203112929100e46001c20040c42996210303130010300d01c00304a2181c000282e0f0345c01980c00803440f0303d9038005c10700c415881d560001c0301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 671658983 1250 671657733 671657737
    0xd09032003090307060905010203070f0206130e16050a051614071d0112020a061b0b0a0b0a0801090803041b030501090809040c020f06070f18060c0b0c03090601030305030c071502 78
    0x40050f000c840036656038030300850312075805009960040c4c00402c02030010601c0d01c0c1d160181180024551460402040120300044905070700007140c2c0c0240004104000b108400e044111880d5070806c289002c001e18802404c51140036804040b0403070461442040c0070f98420540f02d0b400104086803152500c800701240c507914858210300303501d0b0480c17002040400ba03611407034441940c09030a540301c103070400d003050702c090500c444c4d001800914580120042030b0010350fa50300070300480900149a5090000f44442c6030032540060307046c0c1c1e040007424000a100f00d41202e902640010030900305500d4841c06a42c26429a44050301c258200066041400600401816103544c110307005c008401002205a848907500341c42d0f0311007504200300050303c0600910503960090301d04e150604030780e5a11140043c01071419000000004c2d80c1c0d420702c004000d02c080115412032000c0a820741140307000440700e503640c88140001010000048003054901200304240d58409a100744020004c20b11091140c00039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 671660233 1250 671658983 671658997
    0x602030402031b090703020a0315030809030f15160504150909061202010f0819091208010605040305060c0a110a0b060a150206012d080a1104050603030d09032003 71
    0xb8021114665506190705401035003a4001402c1c044c41c90792840c03070940094001218081c103054681c1c18500e00300811100140286100d2081143c46101d42414589007a0340c02100d00c0442d03009441000c1c040e41300804017176101c080001f45060705074003220100da40e8011540284c4000107d04084050150401060410b030381c1c440108012a507036a80c0540c45e42400000041d000c203540a003c010b20511400c542c5034403103030710841204080180608442252032440c815141006400b4032900740c2648003401e540100080e203807042c101411a1030365a1245000340141498810000ea4011260b02a44041165108280c241d4000000900340240402c40803900281f103403402d0200412004400a00c0110750b050582c0200314681c207200030007401c0f40c00403212640c2c0c108142e00082c85c0c0030040100e40040c103000005810708050701c2c0740151560154460f2184a141401c0c10042c4a407000400e0b10411152400007090001c5141421381344000140c1c0341520b104c50700f203840b0701d01800010051280e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 671661483 1250 671660233 671660239
    0x15090a0305060f0132040903090b0a031d0a031b03141c2a0305060607021f030e010219050a0c0203100c020c0303040f060522091a190611070e040602030402 68
    0x4244d15602c03040c0304681095486004171101d00008183d00b0554442d1255a219042c02079129883c4d14481069800c0030808400007a10780004d00413114505440c0d144031400c1000a00c1080910b235400b52014950a908201c40070505601d1001e140c428410200b000c140054055503032200c0d40504e81c0115142c18180300080d04000300700301650100590030106000041c08088209282541103005e0038007d02400d510030703030500a05016a8504990102142c450b18009801480c00b00700982a0303011400c2c142201d034414860342c0850300b4040d88100d0381e2041e500d41541d8506000c48181c0b403052401d440030b500351040412000a030001135200da001c2040d1b540844102d0038403c01010b550340700b1350203901804156000300b0440180104080c2921b040708240038095038403800f20241c0c40f015142c1c4134030035050b100c0110b1301e1243c0d113408a500b07010a054582c80d524000c0c041104840c03442911074030040160207166110317101c90910a04001d001d131200d28480504050a001b00a508190f0302a44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 671662733 1250 671661483 671661509
    0xa02010b030a020901051c060c050c0f0604020d030e13060305010203100509090a020d15020a090e060108070f0e030307050102030a0501171603020405150910060305090c15090a0305060f01 82
    0xe207140001d214541c2c0e50340180b568032180e09210500c1020718015400314402060030f032500f00012030900604200c01400d9941a0b2141c01011345945800100300205115070085800e0002503110031039880e5041d5010f041c010100d09142002c1061009141c0442400038682003000c02040010b4000394000d21080387c40100441d100c80c00c0250712201940d01c100c40b80d0050500d08011b00388201c840b914107014492100d946800c0041c0c107002c1e07a0100000c14000341000b082484004c82c241d11890b081107023172801c448070f41742640020700341007031003c03156061203101c21020006640c1041250081a0310400964580c01c1880804d4007600c021f0086010b00c40c104049800078480c000b441c3d546219001e0300c0c0c103002500e107800340300051402404400009559503150882510340c104481d01510301021491011440d03c00d0003011144050070300940c640158520a0130340d59511000343d1802c2d01070f200503541e40c00070700014a400b9003075440101a030103920101301070b0101c43d000d41d6040b00d0008094003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 671663983 1250 671662733 671662751
    0x181806060a050303040302090a090f050d0305180604020f0310111b0c0105030403030c2c03010b1f2007060f090b13030b0a0e120702180106080615040e0a020a0201 71
    0xd071800038011190541c0c0140320410141c540700e4801500318503886000519200f0300d8480200034400314201303541c80e41c810803030f1101d0254584074084d4032111040c02c41210241085100fa260880680040c0c810129400e0107076040d50240308000c0d4145075850100000e0011a104401c01c0d00002880403184800680744581d20501180000756104142c0d5201e10f1a83c0d0340d035055004003010140d0744200411404400c070000c40507600815080c034040c0b0015218803c00302003500707440147c002240200e007104191030790315001e0082110594010b04102c02101490b0690108015410104005901c110703180003032259041400038451244942c0c1d0b41840d48c6d112260180507110320811040304147c2c02d5010804548116200e40e0899401c00380401c0070742c1e4514080e0710b0018121030203104500c00040c1d0b04210702d840328031202c1e10400d812840040c0e40c90214042c06004008142900a80b8200c20288151240b03000704c1d130141c00c9103042c40305036080c803444450003504900300d200007540ca040105 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 671665233 1250 671663983 671663989
    0x41a0405060307060917031c050609060d0210030b030f0307030f080a0905070614120f0709050d0b0a0207031e09051201021204061a04020d0207050c060c0a020d0218180606 75
    0x9805442c03050301c0d5454000d2074002c046c0c00380c401c05241c2045500061148130342c0c082e1404001c0440c504414070114107405c059082061600028041c2489071a492411b0401600c0d010383d5403c40050398240002c9900780400800e003020300ca0f00b003206680c080003e101c0c0030550420031241c000b22566844459039650112201d00f02c2d825004007078000d030321100c0c0030008188104a400c4024450200300b070308051408250f204514001c6e00c0c800188842507042000701c9074813540285c010241161031900003841c68681c20150000984000a031031717000941c26042c140111001100d0900b601c80881454200d944003c10591140c003d0511900900043c128409014001d40702069a0810701c000c01e9116507883d0402018031088000072658000720f1031750a40c2e03452010304240800100090ba076210a031170048c0c1012400c4072400c0c802d00c0240070783c07581c1c0354000036005031160341a500012004034a0000518a002e20311407140362142c0e800812401c248060511000002c034801151004d444600c10 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 671666483 1250 671665233 671665243
    0x306420708040e1e04060c020c0a0501080109050c0408190b1e0712290a06050c10020705070e0a0c090e1e1b0a020a0c0f0e0c0a0905041a04050603 64
    0x14010740030600040c4540280700c0e81c000d81202e000075007403036500308108080b109440222005d41d6001d40e502000c1c0c0d11107070180f00d0960b01c80130440700d0001180c2082e0001c0c1070300e01d040c003c443c012681d80b00064050b0302e20700e088a01600b0300c4001c80318601513460a04000c80c20a440c1156805c0c0f06001241c070301c0386810091441e140e81005419800d5490034411980200180c40e607000458454406528001c0d16507216000c90241c65901640001850240728036010700e54401c4d81044400c00080050240126294640d04041c00700546d03030b030382141842c500d0846581c203d080050340c030b402030140b0b401c2aa8800d40d800443d0746c44090085684041260404c102180c0c4200002030351402802d140c03080f6503002d58400522188100301c02540c802c2803001d03030040039901c001b5920514019080c800888454002040022518103c0506189440c01802405805580701d1040810b00c0c82c0100c2c054008003020706000350040003030b0b00326100060000b11041c02868041c5180c100424203e04010071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 671667733 1250 671666483 671666497
    0x41503230105010c030c060614182e0306060b0307080a060b03010603020a1209050c01090e0907050d08120c0d38030a05070e0f0a0e12030642 62
    0x460310320380da2800d40159a20312464800b1010003940d804a100042c10301d21405010748a0100c0840001003410248607980004a050f940e00112030030401c900161100c40400700c0c070801003130081c000b0701c4540f06010310044680000303040700c0c20b001d0007003616900d00000d14850206079840c2282501c0708811039045039101e0042030103110081005001c198020340040c0b904a14030301c0c02c8201241003a002104840c2800001c503000e0300851854403540da0700c841c044028000700303107040e2000d0130890081d599030013091080c14041d5040301100b005000340d8000b0740f00011005900c5e802c89151200030602594000c03c2c0c1040100d207492404400c408400d00001180d0030250b071072090700d000c1d02c03242d500d81401003002c259140c8a407802250005000340017a20040411800c1d2911508001001c0b900c20302005060111103880e060b0101481040080c01c000c0908501e02c420b9902c1e1104800b04458102c40c554030440752132001c1d010028100300c0c2d481c0c0c01c080d445100c041890103041ea424203480e80300e001 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 671668983 1250 671667733 671667791
    0xa09050a080f040f2c010e040b0c071a090f0d080f0916030809010f08060d0201081b0a05070c050603281b0e010206010e06010507141002041503 63
    0x5945240000c0c0c1d03040c000c002c900d146041160500340c2e600542601101e043d0004022091038003500904403c1c1c654141454600c44111282c1c60341c14042c0030b400424004001400b50350030400070418441a0104550159412500600c100d48002c051010f00d5282503901e89090320404019190224000c5003c0e040601940d50b0070407151a10801810f00010243c6002880e00074612176400c800b589102c0c0ca0002c52007076104070f45880d08400050407250783d1001c0c05046c00310321410810940e40711200107941a5090801281d140c0390f85d0350050a26000c8100660920000036800d4400c80e00136020300407862065004605694552040c0721240c0020b90305072150344c00a9040c9001c1d181003880804103464600f4000441ca03805080d882c544015004119000c10381620f2480440d507810700600c0c1c050400900301d150f05061a4000801c9803258004c00392620b145120303c8500b0301000d1090503299014200c0035910380e6183c130b00c200e07019145003641c10046444c200d04c07083c1c1310f90860300c0d8110801440c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 671670233 1250 671668983 671668993
    0xc0603052707050609030c0622090b010816030b0301060f090608030f040b0f070b01030311060601080124020a020a2c0c0a0309150e03041401170103020d020d060509010f050a0905 78
    0xb19044c410316030040d48074580d0500030400c3c180440d0f19001c002c0c00ca00c1031035100ca2070716002075803d01485850160040b07600d503810801c0d02140703a6003002005400441c846210b01d910310840004400414000700d085525500f007120001e0700103580c2d460710f07040c2e400385d000c10488160b890b10b180b03650748114045042444028002001040c010001501070743c03d42076000e07450000035a41d01944074100341c2003100030800044102c0d400d800304125095000e1828202040c40354107020781500b00107501c1445296200301c00c05500b00700391003404801d80701e59004d0590030201d51a1000d04203940981441d51186951000d030f003644032542c86148a005500c141420341c904440c0100c110081c0c00e0500702515052101460110703170701c0302d034481c00300103500c00d102641d20b8605103074884c00480d919604817410000c403408142e400380d10790450181180d41c11a0307002c900d1441880840d1003044020300240c00746280030100145028190064240d205c19000104020354484003030000325100c1101c013902075848 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 671671483 1250 671670233 671670239
    0xc0f12270715050a090314030301032d1403270102010c08150d0c05060a0207150e150d090b151c0b0f060102100e011b08040807080a0c0c0603052707 65
    0x101c0c01814807286518080781030988a0f290b0300c00481f131403c0c24108680c400070040061080941802142c3c840c411a8054003006484548101510130b00c4058010150041140ca0b243c2081045070040c900d04101c608040302d00c1800307080454510004280076500309407481e080700344596142031048070760705506c90344082c4500c18003400c0005450100c4044040302c80125040c0d5520000e01425a05a401011168244062a80c03000c08414000040c885d00510f001d000e41c0e1038120000174004030303100c000c0e100d582440c0d00c00301071303e5180405070650764a581030041510ba80740c40107688500668400c2c2c00c480c0644150f0400c98400c04019040c0c00501011680596207500c03425000301c0144100c03014201d050042c5402c4400580702000c11b0b80d542d507829035041e640e40440b00f051009030709050005213080e403aa110148101040240761500029000d6100c40c05a083c680042d0703000300e142c0f001c0c651680f2024000741401d5410400c136034040751405800e00c0c00ca00c600c403081c10011010301b0903039203 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 671672733 1250 671671483 671671487
    0x423041b092c071404030b16020f16091e0204060c0507050303031b0a020a1e030207050f030d0f17190b09040c090902031f022a060c0f12270715 63
    0xc9420301c0c0700141072081000001081401a000d40030f00b240028010016001030300c081c0c5080306500d51070384160001018445907181c0c0c0046a070480c6d070cd8520118690b0754421266100100f031500d510390f03003440460041030f4241d114940c030180c248110b08131032405440d4810143e581c003044170080203041c0c07a182411110a400c502a102003400360048500f040120f680b0190342040307400400c9140b40c0e84112010915904200c038100510003611980400381d25100840c4e21041d605026030144006070000c042c1e482e01c2142d00c1218000134601019803070500f4450b10b0f905004010a070003029041800800b00c61609280b414000e561140f00c0500d071274980400240034050404081ea8140104041c16108001c1881e0712543e080381c001d030060740c4680ca01a50229844a4034840104100550031078a0350300b40003032481c0d00056103a20103615480c2c1481d8514985c45001e100d44510781c8240240324114208180304032002000035010711072408040c0c110b50f43d0360b54034800c4c99925880c000729007030713014 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 671673983 1250 671672733 671672747
    0xd0c11010c05030c1002190e060909100f0303050a03050105031b1e19031e1a0c090612010e33040902062d0423041b092c07 54
    0x18491800ea90810079812501400c1280e944c03042c10329150001108012045011401d40040400e0f00b42808c04803050000b01d51035004010a41e400ba01d51440447c26400d00e544c60040240f0b1240c1902d0030503500c3e0320300246941c0040c201d0902203424030001284500c1c010454503201c0b520300a6841c419039910042044858102d24035849141d81c40082c10039070388401040424400301502e6980c251441c41c500f080f0203145001c505100181814002800148012024030300f12555001140d091385400101150500c2000c050a41c0503400050b0318400c0598440d00b541243c171030200b141c0c016a510701492079078590010400d80c442408000f1044801188000c4255101001d0f2000500229690100c2c8056115040705841d0110882c560403226101140c110f2042c40030951703483c102840c256903281140d80d4880c40d100c03c11444040c942840d01c071588220300c0a00c603800980c12490043d00c015240c1d02c2180a00100c0344200c10045c1900d002d060b0310151581110302d450503c80d41d86000c219401c0c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 671675233 1250 671673983 671674007
    0x1061e050c0304120b0a050c070b0403091203020607030c091d091608060103110429191403160605121e270616051c1d0d0c1101 56
    0x110034207100c0103045080400103000075140011865505282904100700808801071186100d40d00741303010030419203107030801c0c1c0e8070442e445030103c00c140e102d600d01564619659000b240e04c08121041c043d0500d94002103080c02200a80c804100104424508554014035070007200c0c051034000042481c205166220107500110309002e031203884d60042c1085403003c8081c0c0c050000b51380443d0061080c0480c02c1d01241b06040d04540c100f00008900c02c0c42182c2006c01c140801e1040c1569038a11f41549a440d013401d070503460315200300300c1a512150b502d030740c000c2c290800074080e10540c8601c2c4d045000304e108074020f4035225103440381883c00c04400001594030061001103044000c2c80600d05202000c014240950204440b91104840c503d00da410798050344804040396506c50828840c0504a500144004681d10302c0e26030b031303544024508260322140461481c002c0d0b40c50113119401719140e4020003043c074420300064034052914045c00702c03540c00c00e885000d4a0010021084e01840d0b018030490188 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 671676483 1250 671675233 671675237
    0xc06090105280207170d0905041d2506080c0f09030f010603242c010908130806090a1703040201030b0301050708010302040b030d050d0c02070f062601061e 68
    0xb61841c14111041e1580740c854041d001d640290030034000c98903049503260101c0d90003c02010200b101620052178003010b8070070f080c000e56684050b1150522068180d813542c400030f00031540c042642202e0071410a100c8504d891040200352408200c0301d1290440600481004100700c0c200202d040003403119a10002ca0340b580742c07041d091640c005100a0044074010740c010455a0f0365024031a06000300c3c90f42c100e41d281c500620704110282d5240310400d420302e00030503000300d00c071081d004080918014400b16101400e200000304821607101d1043c0680c1e001d88090f0826a1450b40b20544020317554801d640b0001c084400da1400c10304031110780700145070311a00501d4040307618107415000c40e00b12141510900c0008030560014401e605007401843c1503004154000c1406601400c0300034031a0107100000240306450315042268135100300548005400c0590551b00226503810002c0d00002e806248040c01d5554070300f4030600705240040d4181200e005844050034100f54100c001522084031000c00c00b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 671677733 1250 671676483 671676517
    0x15020a0212011b080a1d1902031e06011805061c0507050402030705030a050115050f0f0708030c1e03010501090509090a081c0e0304050f010c080708120708090c06090105 74
    0x561010300f2190340b85006815200c141c003c3c240001034605584415104007803241c0500c0a000a4150001d003017079090f205108a200c040e49103100085c00c1c411005190141480c031502c0d00e400604012401504803000a0101507421941e2a400025124116196a40441810144461000b61803800c80c01e29109005030340820b512000041c0407078200340c4414002a4020041041840d04e07031003000d0141403a02c4011001d1115600000c0680c032580c030041c10110000b00d403220500c241c0c0700079200c04552101480340c49140015054034180c00c4002c480701010702182500407808c981c0c80450303041c0c4506944da180b04a0604e000d100c0540e10251003649188619190580410344d02d00150003006400140c18a0040c0c1c1d004074081625822043d21016030820881001a5541c404101c804841c0a00f07100c04028418241021a0f000b502c2028000180c0000c5505610491501c40ea2140a09480d0300c0a10f48400011984d55510314000c1e980041040003210125030048001c0c250703003144c42e0202d40c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 671678983 1250 671677733 671677751
    0x370602010e12070b2e09150807060f030b2110140705030c070501061511120d0c05130801020306120d021f0204031e0c08030a0e040b0117070c0b0115020a021201 70
    0x1e0303484c2d054a089178050b071030442040c0102c10700313400703440455400040c0d00c21200e42043c41064030360080344200d000b0b000c02509620780c032500070307000011a403900034a50000c80582004003022811800b82d0207115020b201c0c103002c849140ca2081030b000003210802c4590940e242002070f030342030b40040c001c1c21804a080c0580c10000350240210350151182e03844801d44d41100110185c00e03e10201000011074010341c0104144c000781e00181d803601e05011002160003009807400b07544501c1161000f12515a0107200842c0d0580150021801800180c580c1410b02201c2c040c91a15080400303884030041c0c10021a002a402c645c011f0a1000b4200c1d2900626082d980c0d52005450510112801c0c0140300c107134a281c0a101d40407083c0c50003000a44080d61408000c0c400040c500159a540603100f03d17a0380c8540c3c040790340314898080d4846011000020a401c000c100900f035044a5207040b1490400d2400120f076448030003126a10b107102030740040441400b10f90800590724151307851400c86643e00d80c0a9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 671680233 1250 671678983 671679031
    0x220b04060e160906030908031605070c0807060e04091104050703180b0a050f040203070303080a1509090c09020903100b0d1a0a060509040b06370602010e12070b 70
    0x70350107150052200303090000600300191407118607510203010b15140c1041840440c03100030461394042c02c09007840d06402240d0005941c240200b03240030780109080303e000b140d060030004405090310f00540310540ca808610040100391003400d840107200c070003204a5503265007401d402c10741d000b0030f8506000c21080c90352030b000f07190584141c0041e19064103c82c14001070610134442d01da08401241c207101d8661800e038010903524102c41c400242004400800a91003825a034041c031f0510100880c8901c0c516540c980c84800740c070710f01c0e0042d80d42001d40d001c00a4031790218421075400030005000340c84a4465003050030000c0208031044c58208500000d10000900c243c07400c4820b5a65905502c1d06908008884104503100c54015502130707103407003050001140b070f0210b00d190f0146044410300c900b240c40d02002c4903910b803402c1808500c1c2d0102c060351946440d40c0c040f0502500d2090380200155240c0c1c2d0560796480c5c144a228040040b02003000d8400300d588a50070340e034000b04824524079104041154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 671681483 1250 671680233 671680259
    0x1209100f0204031b0b0a050703180306051e010608161103070503040f0807061e0e0307083403020d1403041806050d020916020106030212030c0c220b0406 67
    0x9200025540050148100134080c510001141e03044c884101099041980104081c89446444000d00001240440400d40301d9040803240841452510403095500d1600744050102580c0800c5240d0b2508002c50501d440341254034101c41c11583c82d85e6403a1600340042e08502003488030a010002100110401814104001c08055110b18021540c962400c04405072165154010700c2c42c0380c00400e070800055a01c85041d0601241c411214001c8491640c415600c3c00c0f04200720700e402d80180c0d1000104240701180003904c418003806d4402c0540401040f61032682112039132034007003003040401440541020480d0400c094890203045508100c908076541c55504641d106c18100c0c440e10108031040c48540c00340600400b0103448030b080b00c2d0b02c80d41c00500c0005000f040280e84011052003549405d02c04d420050055402801035401c40c100140c201345c495100340b402d40c510f403160111604032400c1010ba09030b40040708085082081c0440c0b01c034072000d418041950341d485500d4001c00300382c0040e45c40c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 671682733 1250 671681483 671681501
    0x50603010e090105060105190e01202a1e2b03090e040308040b04060b0a080f0d1b0303111209101419090602040b160303180206120910 59
    0x3510262890302d10505401e50341e00402141c104101808040013600600c101c2c0355000f040e504046503403400180041f680c4001410801400309800c20035600d40480c08114242d0181c501c8802c0d0002d000710408031980310741014150b076000310034648151510540814441000030b03000b00270f04d880c09032100c00b9042c4085020580c240352000701118004140e000a4034100a080380c241e0150303d4a8561405484070b10000c1025001000c4200003600708031166114844044004107041807854a48070074507510705800e8100d0b03803148268400c1c1ca64090265598040d4002c0c003840c00041002d895030b046000d841c1070000400300400c244005803052000c50300301e5109450110040032540e003290350a0050b02e0321130021141500c0900306000481101406102002203611800314000800c0c0c074110000740708030380c00815011404503044620304034119000d900240655814400000074210301c1503840c4190038002d601820400c945a550301020300c0d403d601103c0b5a0a0316203e003604030b42003090319580c078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 671683983 1250 671682733 671682749
    0xb1c180614070e01090b18031e070501090509060d0227010b030906150102100b01090e0705030402030609010e0a02010c050114091e0309061e130f15020a030e0103051005060301 77
    0x41d041003480c0781d000072880000030003440c0c07024480c1e14154400042d84508034030740c80350800000f101036031500d04114900c1070360080d00c0c8810708201036180c01e039282d40c3c0d42d00690b40002e40552001a4034039200c40300600500c0c00401850b0743c00044c0c0d003000810901503140600f40441d40d110242178080c1c99135100c0c005c5c40104003860b034a15126107034506080c0010b200c50704006a10500c4001640c1c00200308240320403440d800100a409680181d900ba034465110405560034502084800c65000e8081c41c0601d209030101c650f640c8407000b1380303802d0b110351620780c0c40d241c0d00c0b80510001540c4a4101499214099400040c0243c5121080e5031115401c813561056a808158010f42c404100c3c8162001c40da150405941009090b0000414500c180e4130345142c4590110010b9851250000c110381807030045480481c3c00b6980e600441400a04c2482214407081c0c480540d40105800440c140116543c550ba03806c400c040c078800154014480603003c00050850b010700812992200310045020302080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 671685233 1250 671683983 671684021
    0x1c060c020a031407110105031009050a090c0e070c0803100b2b06080303040803070201060506070c0f0f210c1505071b08120a1202190201060b1c1806 65
    0x81d003809000c4aa800d103110030048420841300c00401c11a120425100790300b442c202d80c1c0e07030325101d10a06220000382c0140825501e410140b001c8081181c1c4201c4c003a0707101d80080c5100c25921348006462000455182c80403840034a54240003c4005004503402800c440e917406400d9110101003000e034004205900b841840d02c24080c07050039170300580740c103032030780c451801c1c0101400d0030b001c5922800f01901c02803103842c0c08008a51000e00030f41081d40070b040c0240c019074031011142003c0d03003045a203124003803643c86c0031000030842010182410007035130b543d40200d1031180e100c0c040000214140000c1558000000a00418288200e010340c0380c802006036074041c1c441c4854141182554030014440f1103450b078110042103141c81c0424040f40e2100c5003803800b5211800c4030029201158017035464250288002456080448070b120484075809041d0300800c60316449500341c6000b4869003071124a40e05421001403030080b00e0760045404604044e4005a95910b180e07503400c00d4408050445070301c03a0702 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 671686483 1250 671685233 671685253
    0xf0406050d15230913060b0d0506072c0d0807050c04110903010522021309170d0506090103030909110405060f042d0e0403051201320f1c060c02 63
    0x880c80c000064980d0441d4404d104c1c2c00e14035040d11080e0b8400e10b00402198403058020241d94610b0b400215003034000c001c2d2501813604600007040310385000003400100c100c180011000c91038130010081d00719800b401e4403920100360b4a5901c0c01d500701c0c200072103243c40346980d2840740c0e071520700070031511705003c8221030b40311480c10041600791200101548060142c0c5400e00e555040d07440400030009030140d42414200c4566049803010346080d510151803003141d200b00e81011000880101100340ca0f0b040104100e840310420421049030a120150000340e00c070905008a008950000428040700c0080a1070b007603070f40001c140c0d0b41e0000c240a40581c1c0c00850100700c0c2289004100d4680740d0b1103c0011040b581c11b070b120205000e207070701800c110207041200040416005004455425205a03540401d80d17942d441140a0503150007203c03207401c02c020b03000b00e103100303c010345524105000a1402500e14404e83c240070300a9036120194403942e003a6500c0d00c0104883d840380c0449105190f0180040c00c078 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 671687733 1250 671686483 671686529
    0xd09050301060504050402101815180806131709090c040303080f010f1a04090e01050405010c11071a04170109030807051207030507020c03100b03070b0f0406050d15 72
    0x1243d900441c00703282030508110050351080c000071700840c001d04082e0724504240d84c1c0c0303501d00242608040700030490700040400041c5c1005441c245044a0b880e2003091036140c110f126110542a01d1402c01c640703901c407098000501d003c5c1c1c1c525042000059841c00c141d03080c000030300558400d8900300320b07039800000c0900500da8400c0309242c1c4a00840480a040d5150458034030f8811005e01c5150038030001911204200701c80303c01214020103456109100f5241d070105614020b00e402e03034040b03c00e50b103090803607040d0502810000442002810260076440d1511001c1c40ca9030b00c24103441d407042c2008120120f80d50f240080741c103066010140000070540810314003c2c0c075824000d000d20090100910a806066401d2001254800c21030715001c55151501c0d02e09902d42466001c40680c14010090340c2e28036800326a008840f000000c42c12190415503034807081041d0f1082008512031004100b10074460030340108010421088031035400181d1642c4000003000b0594030b600b110021483c8500d04a00e518 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 671688983 1250 671687733 671687741
    0x8030f07030204180e0c0d060b030f010b0f060d0603230601080a12110127020f041803260f070815310507020a0314180f120d09050301 59
    0x191840c10304503d80360504aa02403a200d034a8070480e510340d11580c42405801c0140301c1010901009800c90303d140b0703010720b448400f41100c04040b074000c0c49480001d031b20400c014000c903218080060004035403003000c9002e004007644071101691026448900010025000c451001d0103844540613409903150000c249030308040c0103901074280c90b808142044040b8008201d610235550b030038204289100c1751241211701400c08070002d10558216400038045454448413030308e90b16482107410380d00c0c1c107108008000440703108605401814210300c2c0542c00082c015199295510100c08203030007107103185c8503401080c0c04100d541c10740f10103429050042c1c490300003071144c0d041000f001c05240c03d84054800305600c04040c03410100d80c0b105150143c1c07540c000d0300190b811101103088041c44245001c800c040d6894682140c2240090f1078003460a990f07070403540540794480c1007080c011300860f030180204440e0304803d000056000350390110350512103200301b1040002800307980741c10041e40d140104050840d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 671690233 1250 671688983 671688991
    0xf0b0909090111042d060e1008150d02030a120306090e0f100f0605060d05010e06060301080703080a12020a03090c090903050d022802070509060d1e051908030f 70
    0x568103008040c45000e0100003a21309a45540300060102c070002512601036200c80c1c074071039486002556001c5515980500f5a10030000c086d03c22510f045410380f01240c014200b100c082580d2400b2150040807460700302030381c601f00c5000a046071080714a588401140080d583c1052000c41d954141c2000030360070b00d0044103c4c14407098050050383c01c02894564030360022248100e11035540d04030880c00203403542e102c18003421014158903102c850700311041000b0b1800b80200301ca500364940006d9003528218080f40d060f190500c015001c113034030703580c0c810149811003148842444041c09150460750820b00c060f248180c10369902042012072802d00488640994011110090410000300701198012045035180c10301c2a000507911155121410000307070305048401920358116194100d8650b00150170f00035070f00c0403941820152030b000c041044110041900824901540703030100001c160f40076213621960300aa05841c102d282c4c8042c0000c2040034007000b1980148c010090195041030004100c1d84 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 671691483 1250 671690233 671690251
    0x120c190e13020f150915030415150b0c07140d05030a0309030203040b070f110603070f0e0a031a011e030b070f0e0603010f17010e1f02070b0c03060f0312041802040f0b0909 75
    0x550b0606032a0240903001c80c0c49c090710040c2e141c1d44c508a045d601d405048000303150404d0f003652103500d080026074a50496101d100a4488801854240340c60a60469055268130600441c9030011005003a4042d0165950680650105100c0040e010700c00d0402844024803607109020b07580c0c0545440484101c03c070040b2401080280300b000b5059401040e801d00d840424100303da000c04912000034601815130f08014120744000c5804845049510142c1e4145e950054506915004055440515090310710000c4d1040c0f014001252a450250002d182e45440398540703140b0800010001c00c506610aa05c00c041c6180c1400c400c008107109143c2e00c3c80003035040002841442d102051555941200400d244540e40000c41c140310717001200d6049452059118180390380b6403610403111104c50b0011076100d4050f80d50b40101144918000c51052004451040b580d81040c1c14641c044405094a400301040e5541c00c00c070200c0c07090401025100200303500302c00b05a80301407010501803260009008112 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 671692733 1250 671691483 671691487
    0x6051903030815030a14010921080109050a0f060611070603110a08070c0605071806110607050906071a01030c0e0405120901090302120c190e13020f150915 68
    0x1c2e6001007542e4000c54401050303400318010100003420080345050040c015410840c0c2c203d4000300c10f40012000a0051884044a94040540312041d110898003100003c1031400140304688036940016004603071400001f43c01d16502401508a075400d4100e070000c600410f088010400d01040a64094681450305000c0ea1134804110b1909018060201c0140000180000e603101e1180f1030740421941c00010500c180c0c07c0c851005000c00e0801718560f138140300a4100401c80600400e80708102c001c151005102981d03442108440e250060380c1001e5211804111110101361484140d20705280603103500d0320154918685000c501e410355000307095210500c01000302203000410031180f5082400840b50f60b031083c810040b2160b94258000a5000c10318940f01d85070a0710000d07001d82079100c20703114030880005004142c0307410360062250303c80d0742c90f1240005082140400c2402169403000d803503541700b56070110014625504014450078a1540452024407503c2c1035015060600105640c140c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 671693983 1250 671692733 671692739
    0x902040506090f040207020603010f030201030f050702031b1903020105090705030c0a0e0a0603080414130501051513090e160b04061403042613080610060f1809060519 73
    0x5400d4040d04105500c0f0742c14941000480d41c4482e01110501079008092940e20740c0c4075102400b1f402114082a800139207400d040c00640c21083c4070700c41c0034a00a80045051855184d040c040d0b07110410074a61003809041e0000b06449000c1400c0c0c107800348203800200381d61402000b801c0c600012644030074840e600c0b0200304c2801e5161a1080008d45080958400996541c180420050449540002c02080d0000b800007401c10100a20034a941c0c02101c01e5491011a5100300742910001e00400341d01c280020351081c1c9401e1040010f2050705041320304203060660380d55602046500c0b00405181541040c1c8000c0e000000c40600b41c2c0182040e69a854145414824004c041c0c41c58050800512038000003c1410311000e85000000752005810304c124001e2030b02408005a08030312000610303000798410104d02c40202041440c490540943c000e41000c0ca01074044450f2101c410542080c8500001c480d07440800044c1c51001810300c901c400b04001d490f01c014400d400840c1000020034402d07030203040c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 671695233 1250 671693983 671693989
    0x60e090316150e0a11040b0f090c070f14010510081b040903030209220f06030b0703150905041b150f030c030e030424020318010318020d05011509020405 67
    0x40081950442c2a40c0c40d00c1c100c640103800203003141c1520307076072510841d90700108010200407070481c4c070320042d0390a100500301d020500c20b0700043d520300c165000c0c680c000003c1d01400c8034800f078120a0b000e0ac0e080c4100c01000e48036140d80c0d5000c0056102142d44032000c0020102142004200a1025400800d03250209212803a0b04150304145188140e0701ea200c03040900d8440d03019210b00600080058203079205641440d0f14920030700004551050034054030000c01d007554802d070740480c2d402075940519030346c80c40ca0482c000c0110010140701c03441840c80100d607001a82c8150351045224403020dc480e00e01c0c40310303020364a0301c1c80c5d0b0290a00010903032031081d806910000d40c0d001c18060781004103080004c10780940250019040f242ca040c803010800050100d4071464440890307041702e00c103500301460500202e0f03c80c8240c10781004c12401403160300390694400d40c0034024034044018284a820300c184c0c0018969034000c0c00545150b911038005080c100011110000189081c1d18110b02e041e2400c6c000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 671696483 1250 671695233 671695267
    0x7080c12010e04020a1508070207050a0f0b16050d0302120604050103030e0d06021e090a08030c070315020d0903030209030d1b080706020c070f080c040b0901031b18060e0903 76
    0x400d161500d03104082421502c4010582c0d001d02031b6410400b10203048208000c0c88080c00711030550042c03181c00320014071824250105c2080e203034031075a02ca4980d802c019806030386038480907003019980f40c000000300100e2014401004504015900583c0d14911602d0a900c00500a42498402c0b4944001000004e42000c02c00012490a44000002d141c45041040090041c200b942543c5400c1d0302140c1942040c100080000003005ca8805271502e440b0781e54551346c1d003d0384404040d030b9409550284003141420070303400b06091401201503e0034090781103410545991440c01c901187e00840e05105500d818004400121410f1806882240d01c2c08907009550320418030141c00c032040040c0c0c0c0420300009404454813030015004880c0415a1001d080602985030301ca002450b002d128940003007880c0602030490803010042c214400b6900399110b01c2900550382c180c400c1416076003440010170000b070b000800102c0041d841d000600e41d10309021409805c0c00103043c268650070802c4a0640e03800c40590f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 671697733 1250 671696483 671696489
    0x30606030a05090a150c020f071d150303191115071d0d03090303091d04030509030c041109030106050f030d11190609060b0d03020706050f090a0b0307080c1201 70
    0x41e0214050b180d01c540c40e4100b014400024100b801e49400c245488841d541042808060990851340042d00400f2410780b00e114a000b80014800c81c0c0f80c1c0914414000038100740c001c0d0341c408500304290086c0e40000d01c0e544c030042e08055041d151002c4840c03801e400005070f440c804801c2016001490f00403002c2640f03000002d0004044c40072840221034a5002003148001e103581c00f901c102551402c034100034000c06c00c03e1008400243d080039010919040203410413602802019440c90303661140d139820360301e40e00030152840d0588200c907800c582d140d540b401100c1f640802c41450b00e0391011024107043c02d44080790001805415612881d560644001905040001a91600150902c140020603080c241509011030000b51013415120610005901101519214250401001030840140103041d103002c2000790140e0442103040004038003070401024105080c5201d02c0c908060700c00010320b01c020541040c000c140c4080208003034280c110000c01e0700003c0c11901e042c18099680c01c0c58030301901c140 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 671698983 1250 671697733 671697751
    0xe13020a0b03070c08030c090405130c060e12010203131b1d0c041d06030d17361c02030306130209130905030706051501020706141308070303090b03060603 68
    0xf0003c0c3d1050080b403051603440704599540e410110160691508101e0042e48101d20b0040860390b00e141001c441d4036155404104030030014641a000d0328081c585030750b056002899810300742c9100d03e00303200852040c40c0c890710038498488141050041d01d0940f40760311b034132178614038030500002c1d01c0842d0482100c4140344400c0701315600c0c40c260002074040ea600000c3e0308110a001903a031180c6500440344622000d804440030b01c4440c0800321680710b40d80800d00080b01001c400700d0b9400c11040c2e400b01c141c0702e60b4882c0b110b000b40d8100c0e0306c0318045040030700c0003855080600e132034a004d00403884803a154045440110305600b0103d001561742c0c1040c405050500c4d030b0000700301d0520f85407521544404101107100300101200b03401c0080c0c6940c0032803000c5a4451500002070302612008110903141c41c4103134014071405080580c15140007030303202d0341c040d03031710005008c01c6003845401c8001c00c02601c43d80000d09041483c40c42c001c0d1480d80c20b80c2041d0680e41003441040b205440d9401a02e83c010408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 671700233 1250 671698983 671698987
    0x210020d0e030703020718050f1503250303030e010501061e090f03060e191203021312080c10020906070b07170103120909150302040903050d0c02070e13020a0b 70
    0x2146840008048151190040b804046414000d15030041074001c1140c81003c030114120008590300d2003100c0301100e44014000450011400d076100011980340051b40250440b2500f8107404500e05c42000603800014203450480001c1c801c1540c50b0041c81c81c2d62110000900955040180c081c0c90085206100214001401c1030540054424501503000341510940b0250050301d9082c030320013404006425640600c14002021811007100c2c032201d00c0ce07900803600681c1e40c42d8081049029505c6244034502041015901051400039255608c80c15881070300e401d680c070030034640c050781000c81c0300c0100500c461040c4904900c9403075039000c4500740355024004182d00c0e03891540942d0406498100e515501c0201c0001008000d006183c0311500c0810b922102060740d5600107140984442c2506481010514401000182805c1d0800c4a080d403103820410b00b0301018080410840300c0c0c4034004801070f4041242003040f40c0d040c00c03a09030050880b0304501d05a250301d4010488084261145110400300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 671701483 1250 671700233 671700247
    0x10207030f02060f2521020a0b0a0b1c0515010305210d02071401050603010209150904091e020103051302100f0203040816091512060207061e1a030607021002 69
    0x20540454809050845403182c440e00c0b80c82d050f070072148040380111030b1b031b010f06280176806a0703a0019202c0b00141d660b00808201c1c0c440d0b070310046a110080d040d4201c0c01c0d102c01054040b5603403003003c01c0415500864110042d109401d1085c030302518551a41034600b100c0d80140082207001c20210701c0360341d20b04d09501303401c0c008122504e01f502c10380c0040100e85102003a4081004101070a1070340200b03000000b84032035101c00c1c041508034031400e44007541c08180b4040400341440792002900540303c0041001801c070075661140c103015040010448190740500b60010300b19a09441440e40145010202d0843c90b1000d5000c81e80c4140d111000d0410300c5911041d242c84588204101c802400f500c034151050356900d040308591200941c026018007a0800c0c00c0d4118900740c172540801240c0b140c0310002003000c0140c6411009600c8003000f1f5640303548610715003120b030084400d03000b5880440040041e00807010000c00760201d81c2e80c90b00d6032083d0008802d01c2101030340000c400b07030341c810202d80041c0c0c0c43c01e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 671702733 1250 671701483 671701507
    0x70507020109030b04050a06150501200106050a240507080a081b0d0e15070c1b0b1305040b03010c090512030d05071707050f0a030c0e090103080414010207030f0206 72
    0x701c2ca50000342900c003110100301c108000401d440305107a210b01c4051000070b054100240a8800d00c0c007404c2d002544007100c0c4129140c040e00022940603a07080000350681d11440452030f094034540209406c2042905002034490011040b0a01c01030a0b142c01703801c3c038021740d49841107882500710b08000c00819001041ca044c1c0503503013011645104040055440070300412400c007030981c0203486032160040340b2a0688001114405910a144035a60b91843d0b600d190740b0650400518004405080030392400840c80e969000700800c500544080d01380708a5240004200607141d014415a020741d050907880b82c041e0383c0001141d01a01d404a40b0384419000d55892a0300d1070107034042990006041800b0b00403056044000340000101030000401c0c00d94403014152184e206105a1144400082001c2040f25200340d01400c202c00c01c40c5170004446144000003010380c0000c4e001a52001c01c0003a080041980700d582c0c03440281d800b80054041e240c036603101d89070100c00428020340501c6002403000784a030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 671703983 1250 671702733 671702747
    0x30c0311060c0105010315140105031c02030c120d0608032106151b0c10020624030a060b0301050a0b031207020303090d0605040320032a12030613060605030705070201 73
    0x2ca40031008120940e900d0a101400a8400082091113403810035071031001600c0e000218180c4002a004210340b5800e1a614401c1038540d001101c01c5000610503c90b2024092180031f8050b11481c00458892140044d514102c0d90310b83d002428030361042259103042404051031741e808039000000e00e1040da0f60200450151000d0003140b07010601c000600524411420b81206510540391040b01c61103031200061018080d6640b400101692107100000c0b096041500884509030107120340c041c0340c49981010902c0c102e42184201d0f0f1840d140d03004035600341400d02c103454cc0103480c110f09200b90310000300030980703510110394005030358400000d0750415920708000700c940c0c0c40c1000e00442003039280c6003400b1000f0403080c4e408800203919041c1c500765150200341000400056a405503141a02140707101022800000e5422074041c0341d07181844003900184643c0300240e10720405a503992400000f008068221201d82c2404545490010f01c20103500c8001d5070381c05085410441c0d6034100c18001a0703490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 671705233 1250 671703983 671703997
    0x2030409060905180a0b130309270506031b01181707080c03031306030902010c15150518010b07060e030d06030317071d0103091502030601140301030c031106 69
    0x3260400c00d000518018540c07001c0d02c505054900401c42e082e40d054426191101640064442c1c1c0c030100208020003c03451b01c424205209090011801359100501ca02d1411030700c03101011301280b14480602d0203054040c00341d000e103040b0098850351324162503024500b1b1051450b241005040500d180c502c2640002c0400900004a01034840e456506203644c1c2d00c2c1102d000b4803466006144100200b4203002042d9407100ba440c1300086441070820b80704070024040914180d0401203a1814140800e403091207007000d440d1510000300390581640708142482103d0390249004170109140010010f110701c07525030644d15110101960cc1440e42024005400d0119441005010008100100403031a9100031308682c4682c42d41d44810181d01407005517084111015404649824094000c0b0310000d80e06014552050400080c2661142c4a000001604085040041360f00200303000d155038103c0b000100030254424400e103190304660f81c60500c102c00e40b100400010303034407400041f680c1c1e480050f80d010b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 671706483 1250 671705233 671705249
    0x70c030206162f100605010c14031e27102106141005090f0f121b120615040c0c1e060617060606070503190806010f1e0c03020304 57
    0x422600d8056100742903c1000e103184a2040648207002080c0a02840c411510305071145510352080340c0f10b40c0030500c01000e00c030519020801040009040308503c02c90a20000100c060f01c0300121503c032020311616100f4000383e240e00c41d0a91915540300900005500454907002c82092030080c0320f1149102c15040c8800e00301c3c00c0502c0030901481e00c1c0d800b0311118404880c5814000800002a00e0a101d400d0100350031400d54588010755090070054855400303000780140d1030038003400d06210b00b03015401d4600c01008000e00d86d08882803500350003e41c000c462410180506040454206040c1c0e1444241680070b261125155103640f401000041c5540e50801e60300741d02000700404500c10000501d4003200e001d4944100495920110740b107441640d00090000c20490316a541080100c4d0400e541c01c031010321080280c03c5816120300c1003001d03856640c2e00c6042c0281080d000241c4405c0b860007007442040000080c25025a0054243c0400c40354242401404e440b0300d800c00b00d0652141c0e030482c1070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 671707733 1250 671706483 671706527
    0xf0a0503030703050a02060601090518062205060f01111e0c040507020d11121e0903031b0114040f0f021f05040603110403050604080c030702210105070c03020616 71
    0xc3c95000740042c0141001a070944019956040064440c4011030003910b80180c03200600d0520a100f20074203e0700440003e052a400941121254a080002510181c5660384030418011182409000d403242d00d042400c050701242c090740d08055941008000c0c0300c0101e44034207039003440c1c00e809004804004402400901c07484c0b81a10010359201107003484e00380003440ca030030803181d0180089410310100c10048074252502c40c03001c802042c01c282d1807006181701d0710100714900c400da030100001c115003040840e01944200700f40c00c6a908560341a00f1480c03143d80401c040100040a8030503110429912150f00003110300e1f0350003c1900071701d401c40c1030200d840c8090400a501c0350014003400448030079540502041405c400d540d903107030040e88802080d81c0c0c44071001c540050fa0000280054401450440e030500c01560000707142c1c40022008043c02005050884261070028001c503035000c40503041082039007a89903002940c4050040802c00510214444041040e1090400e1502c020807601c882c5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 671708983 1250 671707733 671707747
    0x614150405040903080603060601080714090303130905060915030309270108070807050303390307080d0609050910050a0603061a04060608010609030f020103020f030711120f090f0a050303 82
    0x50105c2c0d00039074209109110f1b250000c0d11544c0b182208074883c43c0c0507a1004207210030401c6450544d005200042d515000520100030f91048000d60000141010100030460b41041d07414042002406440e650098a6070132251089481c000704490001a0075940700f0508100c4262070010880d451003006800942039000241c0c03000c0006000c4180c814040c2910b0580380d8030170816550303105015100c8401380300c400e4084101c6a103051a40c43c11600f01140080441c04105004e0440d4894031045846441c042118074522032688a03003800381070740745010070103428201c5000707a5a86d54280e11a410989901c00141c41481036004a03004542c0014284050090401c0717048011883c0741896000d18601240002d4041c1702d910024101d601e180c95006055007541c0f900911001061800e905042e02000208130450b51100214031451041d42c5036800c1c0c440044145092104c0d505002c030140c50180014214003050100321200d042049441d101c0e10b400c010045035a80c00264000c0b949400003042071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 671710233 1250 671708983 671708987
    0xc060b0904060515011d15070f0302010212010f08030d050a1e020d05061c080d110a05130b0301080705010c0606090501150807030513120e040c020304030201030b03010614150405040903 81
    0x1690244c1c94103000c8110070040070b401100d64644440102002913030085a5100a0804e1400301c803140c0315030703541e0601d0b00d5a10f0702d601c0c60b0881450800c0b40142e42c0028201c068072540b110050140040f051480340c0145083c203101c0e0f881c01001407030604036a070780c03010560028113580b2060400459410b071100d8034517003500ca0350094000a260031400303810100010b03d00d00d003c12032140601c6400207005500d52090b214407440c0c1d0002c01004207210343d03507190750743d106402c10054030503884142e45e595a20f140d200400342c45001c039540854040c09080c4014003000341c0124185043d51001c1ca4070140351405420102c01034005030f880001c402d0325000000c21083b00e5035001d480315260f140c55440b0580c030383c0755084003150411203440100c40d40e00d0036011b00040c9210b031021841da040c0c0c0307172460f20500c030b503000503040342c206c2d001c0711001da81b00017801c0046507058000c00d032190000314020091546002e00c02400f5001c8a42214401c0601c50b00200c41040084140c502502003e00200242030b41c40c600 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 671711483 1250 671710233 671710241
    0x13150e01020606150714190606140a080d0f02010b06040e0402150702031002070602120c0903160b030a0e031e04030c05061c020c1e030711010810060c060b090406 71
    0x4000e005004100c009641810069481d121946141031480d15141e5262a4804003c140204044442c0200110180c402032a0b808510200b409410001052480d10341c0f44c58a12002040103401002c080700204400782000c01c0644002c039840c200300700c007100401c0c0100c4c0141408036030264001004200402e000d142c5501c02c0d403003a4030a030f480700a000204a03800300345004488000754180e10079455a10300202d0780c0c0141c034000b40f0516015040501040c82c0b81c0c0040011116811000404654205546010405802813027003002d007550480d42000900c0000344001041200441d071160300b00b220f05c8104100b26000080c1c025032010718032103014600301d9140e0292006440180c01004040741614000085a40740c00340d5118000002c605071400c1c03000b83d00064603241460040c990440300b0b060502c003400c1a20183c1201440c0d07a01102e01d042103002013102c06050401903500100400d8084000c6860140c5203581004030a031358075442c4c01009000020200344c3c101119006020800266402c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 671712733 1250 671711483 671711507
    0x2707050405061c140c060f041e030b042d0b060603090f031303060b0a050906040b040608030a08040b070e091b0d0e0c0906030c0a0b03091908130b09090109021315 71
    0x10030b55004217040410800303107020b03001d81c0a40b14001044100300c0200502c200001e480c91420f00798502035a40c0e04c41885503502101d080c1c807a407a07000000f080400142c1195510800311242001204120380c4440032001e40041449005940000c040303640c0355800c0000d00d104241d840103da544940070218100013800c640b02c104c0d061802c00030002e03907504d4188880000c0c0e840c05442c07002c0c65514a0104006000d5a03950a6041a655100401c0d4050f041c4014802e0b09125120800c09050914020b00d00710720080440c0c0c00c01c80c5000751400ca940d1900d080b10f8200e5000142c000f11181d0440c05c038501d9100d181c5c01d55214034074006426400400c04200b4914110341102c00302c0e03a40e0303100014542c0301c208107454240d00c103804c11010b100001d86e05c0302440d0806a03d1044866000c1c4803d02c401e20710391504020b840010010602d8081450103128001c003820803048118149100764011070701c680c2c0180100d0b020103801180b03006109450741c041c80c0c0209140310407204803103c500710103490380020719 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 671713983 1250 671712733 671712773
    0x10c0206090d0c03050d08011512110408011a04060303050714071509030b0f0c1c0e061e1008030d02030402030c09010f080712050304290c062707050405061c 69
    0x590385006d2540205440350480c2c103615071420441c6503030082210214203941d81d805102d5a500713410040f0104402c050809404030000024a803100c1d0955260b414524072000d0b44220308020703040c40003d600ca400d42d805140c1c0800c44d032400381e0070079016608001e800e81000040d841203000401102360321001e0b10080317a000e000c09003013540b00e840b140e01c1c0c520000c80b004214040c2c2000744844049491035001500440b25400041711003103030310000d040031001d0754580f03d10f851100601c0c051006100c1c08a800041752400d12540d11f2900e400c807a200d00a103507000da01d00d6408000642591800e201c000c41d1040001c0031103c103503031101e150000c49006405a007002d48035145000c241402c0141028802c150400019030030309103030180c42c84180100c2105000f00b04007035039030360b480445400c0c040c001c1c2441c1080075120030314025520384404006040075051202c200320f840e446c802804900501642c10641c0c012607141e442e03201241840b440c01c01c040300030001001482c8140304500030302115001000f = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 671715233 1250 671713983 671713993
    0x30201020a0e190b130b030f0601020d0c03230d0912020105011203200c09040606050915131d0a03050702041503150b01030615110c0603090c010c0206090d0c0305 71
    0x44024007001049007641ca207a803e0142d18180240345030107001d004844114141442481c0d180c050030107082c1c1040d10040300b60396803101844010741c1c042c88440d081c103200d031410006a40c07090b10003c180000903080c904940c9130040c004460100c0000c110342c1d50070000c00c020721080c0f40901c0c0601c4203c11040c40c0c2e8006510308030010419941c520b0b0300d5403500e40c041d5240001940300c9248584c0c4440c90350035004d60303445a5011500076494200c107083c4076500031000014018540014060f000d40d00078040744c510980d0110100e0940c1d6801d5911081c0481c4032000600480307010301480c02c40310014009503040c030482440c20304256012004100c2c482c425034091120322440449111025402c2c0001801c46011508441c550000c6901c800011001498041505a9646076020300e4213280b103032240000c3e0641c2000000b2800401c51541305841c141c4805183d032611111180d1106513964000d4100080d0008210a56a0b40d8080c0d41c0004001400400c51030702a14194001c074900c0d21041f2098041c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 671716483 1250 671715233 671715257
    0x1c06050c0301080c04020d0204050901080604142107030c0b10030213050105034c1d120706110c0106150302180d05030c100609060f0f030b060d0f030201020a 69
    0x8040540b4103c90202d8000c044012495041102a40007007110203040d540c20301002941c4d80c0c4d0340306018020420840a480c890900703007031040180103022081741807030348030010a00903001d560000d4a02d04995804641e03c8082d6854200c805008507040900150003410030300c0100405801c00c041124402c403207e000006a02c0030050a80d1400d1080541c95045800c503c404401080304003541c0c0741102e5002e55002d10381d100800c003c04841c2c40b078984480a14120012002c1052007098a01024000c01c80c9181002c500c100e0754607921504084030404001c9961030401c0910b8001c3d4400760f500d03004840d00c40240d00301450003003000340300e0761400506210f03410401600920031111604410a182c504116100302481a00f01c62034804498503c000c0089040a44051144242400c0300c0c0201040c0303585080e01090584d51950030076110300f0066142002032404c03402820048036480b05000441380d0310080080d00d442040c00014004822560342c4004165065008001e84515900d5403610011 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 671717733 1250 671716483 671716501
    0xf01061e0603051506031f15081503070603110f0c010207050706141909030605090a0212070f150e060f0304060f1a040b030f032a060c18030a021c0605 66
    0x10342034412404180c0000995101307424213100031a030020390090b4140c07002405d08600d22090b84c0e90350000b13844003445c111044186601120503030304400500c4a811244030f0030400252109914850042803503503456004081500000c141c40500c42c20002d56500c034101d101009005c1e601c8038138100c2c0d842c0075040d808110300d4003c203101c04103a250310590701d0070941c800000300303001d01c5a100140c041c800140c3c0e00100060030703030080512900a0034040d21120010f0b2062040d403001e11980c115941d00701a03424000d0000c25406001217446440c0f100c061011141c1d82941c6480c1a24091500420300040000022000704011030040344506400c102d03884182ca800001c80c2d0412211840c11004503882480741d203055000020200c10003001c1d90f0181e400200001d28580c00031609201195400b000d081d000d100404000d500c00d00c1c6240501603c0c0b411502c00811480f60340b5044030f1070002800c880c881a14100f040800031a40130b0704160603144150104580025840e804903141410400003506d1a2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 671718983 1250 671717733 671717741
    0x110304050f0610091104030f030c1704050d030305180312042001050d0c020c090a09060b0d08090108090c0d0303060e15030c0411070f06090203060915040f050f01061e0603 75
    0xc0101c0c0000411414403021001030006100900c00105d400d00003c0041500003100e503460328425140c03414159a40d207080c4000c00007444440010724011301c000c100f0f81c3ca41d880030301c10480e4540303000507107a51648114102a03d0542c4100c48910000c94003140d10200c60301c0c094040e40c040c8506000000ca09009070003007080035220b850018100340102e181d610020b4004040b5880c0d0350058a000c0c0c0070342c101050114808481022945032100060802e01c20188645220120199940549540c02d503c80300c24610495000c64100300c8401e0006042050a005025020070010288508103103a420010040c091500440320f01c03020f0f0501081120700e00c44a003110070a005005802800d483e076080000504c80d00d03119a440e02d04c2048140c00140400c500552101d00ca0040041c0b5480a4014546001c81c010000502d03607001c0d24800d5081020784010341d6006512a0040030510078a00d0454200074003905061059802e150010400b00c11500b011514000600036a09000d41c4e01c4400310700b40c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 671720233 1250 671718983 671718991
    0x303050a181a0a0e090403050d2004030f02010c081306030b01080f0f0a11070c060806121207020f1c0201180608010909020d020306090d140a0f030e0709110304050f06 73
    0x1125081c1580040782000401501a0f0750060910142c010030901c0850061300d011076007240003640c00115406c900101e807107040c01072003196120711100e81c0e140c0c001001d00c2c46031f40005030510f0305203e030900840e841103010b280c001c0d901c000041e0725800340030521540c40400d4080c4201283c10401da9841c0b41d4420343e01148601400c0e21880c480e1345400910008200c0054122102a5110000041c40f0245d100003480803500c107613801d8010900d0400300800c0f054010300258030540c1414401c0b0402040098488203a440100e00c0070380e520744030b2002a20486414488580001e0740502c040c41300103800c1c8407034901074000c0c0c81c3c0d11a00d41c080034010800b05040d0140e103020904000050000f00c0c0d550740030510300b600c003170171179503803101c441e00041e107400000c448040065203c035000071142580a40d0100003c40c1840300182090f00004000d4015002c40302c400041560303600b060820440100001001410003001c01c000690346101c4481161f8422241901c041c410005000e102140015290344a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 671721483 1250 671720233 671720249
    0x5060d020f09040c0b04061707080c0d0213120b0403170c1209030d060e2211040b1f2c010c0f0c0b03010603020304200a14120102040303050a18 63
    0x510703985001008101c0601800c240c4c0e07840964040412503000c084000e201a044585410020055464a2001e43c040080c440d804010480c018003410640c04e00076203010520040026848041c3d10b510110b041442c0e500a025a00c82d2060300011300c000d5009190041c1d0007952803440c0900c2184089007500015204283c1d200f0041082002021391186403a8102e4a130006407884d0404090381d41042d1501c681001014034044403e00c8809802c210140482d00181d001c0c50702d10200c40d80300e40310400060000c107801a525451042c015984000310b07048040446141c50740050464075009018011140444250f00740826942404a03d811002901c07401c0c16951300f4070304803840c0d0790300d24940c02030301046510248420001c2881081000590702805050341d0040e168601400c100c9c4504c12140070822403034214491907482ca031035000208054840640d80c50340c4100200c0003140c0300b40010140c0c0640783d480810003104142d4000004c0c56040f201b5a0303001009c240303074058030191903224410094 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 671722733 1250 671721483 671721499
    0x6020615011b061e0b030607020a081c0f1b140405061911060406141303200c03030d0213080616030f180c0303031104050d15020705190605060d02 64
    0x180d2000018400a0080e129007800324003020300b48803404051058502904c5482d46078466056981410031106500c00075902c000c11108460b900c0e41c061500c10700754a8041d00b10301807a060003403d110382003c104007401d030500b0014502d190009090000109030382d00001003440300c030804a1048081603030103480009004901e02150103030b84181007403040c070380c020030302812440031001070b007040c0003151146000700f00100b1590030002c1c50405030314008110034402180c4521550100313501000c00d500803040b6040d60b5001c0704002a026160070741d180b40140e40343c8400281c10b2034400d090b8005e004030402010a0b120010340b41d04102d80c0340c036011074100d000d4840001a17481c03030921a401a5403400c0ac07010000401080707000c44021081c00c0e15005030340003c18078200b0001c141e40752245002c1003020b03103011800c150400b80090300c000341c0c03040044c00c0c0c84812001d00c6016445a4105da81090b0300c04c0480b0004903c0000003130360309501e10000d440c294541000074005040c0040c5860b505540200400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 671723983 1250 671722733 671722757
    0x40b01050d0b0a1e09060605031314070f0306020903121e07020d08280f02070e09070b0301080706110c010e190e0a0b04051b07170c01020d060602061501 67
    0x5402024000c4120350f01402c14040060408013040c40005814121941e001c5640c0c14044c8441c01d490607a44441c04014081040003030602c1e016505010701540021092001c01c110401d103480d200c101e80000b11005882c100002c01c0110a900800b690030091b41a01d2001159000c00c501c1401a104a031404062641520324001100c600a0845d02c0c40184000901c1e103050315000690781180c40d54400e5a5404910b02820b010303403880441c0c8000306450102021040400c000b522000180b0451400280890105001d06002d01240c0003504c1000c88031030701c0e0341e502c00c00b050b5954484c0c89400c000c100700000d0809a440c004c10ec501d0199810785509410300300003070030302242a80f01199031482c80f40710400405d08610201600e805000d6106010401028070001c20003103600242454180d251201440d040200c418025180256002140c5d0007501296008800323081c49551012884c6500c00140305040d419103901c40800d480c62903089448503a60242d1000e20440b0307100c1303144d0124036449001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 671725233 1250 671723983 671724007
    0x5060f030d050a02011509050402031009120e030a1a041713060f0c020409150b0406080a14030d09030801030c170a020436050c01170a050a0603140f0c040b0105 70
    0x3040f14400f14400002c241484000d6040340b01c0f141d4010003001502ca40c00d0000391b2904000188003103030701d01402c02452480d40d031511807403030400d86010b05000241c0000e00b80d030313a800d0080402281e0099003840034141c400740000620704085400701c40d00c10018181d4134440c06002c0584801e104040d036001002800d2140598440745080c0114041004100300040140c80c0c9000782c08a00e8818080c01d801007007100c4800e410b50350a00241030089151010400c24000b001480d01c4145d504008040d007090910300c0ca2a08512644c6900c190755424030342400c0c01c165020340c4c014100c80c00341140c05409900c4074400c5a1902e51601c0d000c40d50340c0003000c40005031800d0f6010f8100d007c000030403010691030f81c09d440100c40112204920541d085092074100b80001401070300d040c5002440c0007040050001070301d12180300f000c1c0095007003e41d96000902c5072030056010601842cac000260340a240c84400801d44d031495601d0041606000b00035541c142c030304050103242d1641c04143c40d01030401c034111000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 671726483 1250 671725233 671725237
    0x2105090a08031501031b120b12010e10050604020f031303091d0103050c01030207020d1506080f0a0510050f07030b0301182405090c0108041106130e010506130509060406180c020105060f030d05 84
    0x15490b800700c0408407441e1886024403c03807610030381c03030700290840e840103301c15001c0b82e90052520b4000c50040000280d24810407007201c0d03000f1307075080c03101043c11101c0c1030854121150350840080144040d00b210005624550380394100c905ca1402c680080c0d1090004600380c2c00b920030020741007485103400c0000143d5101d10359101e0120700c2c000150107903803400218a4040712b01da40515507001400040c0920505011078222000740c1074043c013142c20074241c0000850001814002056a204c3c80100079079029007041841c40011498040d03940042c1c24031a403402411011305080f06480584070710411158000c06120300c1c08a00a01414003080c80151120034000300b080300c0007a030502c3d12801c142d0303036100a0141d44191049040c0881e0600344504074100040e040740384104000c0c0056010315622444010544400b0f03200c050040d11840c01003000792400307811131805241c03618100200f2551550241846081e60381c000d00407500d40c0c9050195214554030225019000300408105450242e00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 671727733 1250 671726483 671726501
    0x304260d18031412040f0509131a040f0b010e0f090708030a0f090302040504050d02100216020d150c030e010605040b102601060f0f2105090a08031501031b12 69
    0x10baa24070b4a114466201030352003504095001c46c0841018811814114002c0b54012548509400e800180c0e8071004203565640160f141a0811280002d042064031f03d82001c0090f44246458401e503103540e943c802003041101c0b0104202c40c580e0005000200008481c0c00b01c580380e0002c2c42c5000701c211800c482c071010b89846a4148104103100000503101c611645208a001d4405090f004185420081c182480c04844044040c0140408448100900602c040c5654125468800c00d46146820000071b003a07801301c020014a4100c035224480d030542c00034891300c89120020840c81d0707150010030040b030b001c0000c03a5030003154151042c10070301e0048a10340c0300c2c4c3c0c034003d0240c1140288500c005008800980040002882c0c000310900401c2d086101d55990400b207041c010940d20003192012800744c0b074070039001c1c00301c3e407100007145080c0828407a03076034000d400504d0f440d9245099a8120705081c40704080340c0c0004c1c034198a6462181c0d101c1c482c10702d9100c1d20313a9010000120010907101610aa00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 671728983 1250 671727733 671727773
    0x309052e0f090806130203010506030604030e060a272c010e0a02091c0b010f0602061f050406033c08070203010b10020f1b210304260d1803 61
    0x58011840d440100441442805c16048260342c1c1c8566105150a45401034822802a4401024000001c0d0005125086c400f029550f00c1c0e01e61110050845030030301c0ca8160b118100c04034806140c1450302605003403085c5d030b14400c0d5000d041d072421404010901c49204140e550f40041f03000500c41c1500c2d1001c0a03404c00d040d51400350408042000180c04e00e81c0054280003102000c0c01c40004001540d044e1354014a0300003507840000d4940300f0060b4490ba0000c0404401c0c4090303282c101141d80c0c400b00c158018100241007040110f031280740603407580348240081c104410701c1d001c01c84ca01c80c141070361410000929003046e0000f503d4a0f943d010968000b9502285d05540f126400c1c812510780c504e145601f0070b0598020291200310700078860034401c8081404001142392183c00902e911000c1c0342e1101a000400021085980745880340d05600850300000303e401e240b41c4000c102c00ca603182c18a0300c07c0f060b9400759141050421011303206207562a111101181c0040720410108044044000c41d04d01c141c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 671730233 1250 671728983 671728997
    0x501022a15010b25020405010803040303080f04030921060e0a0501050109061410050c0d030218010201090b06120a1b080708061009020d090b0a0e0f12090409031404030309052e0f 78
    0x161700003001d4446c240c2000b001c940c4042010400d1640c0b001d45103800440507480d12980b82043d88008103a00c00a002c1c0c604a13106d10034081009411290004007a03076040b050030046c8450340405d85448400c40c9406980540c280300003c903c0f8002c0b84a05012160b010b00c6c0700c0640e47c400c1d030501002080d0300c0031081c1442014408170034031242c14051122110500d41d00180d9410a40004e0150301c0c40803642c06045a2401025000080100803e250000400c1352481c1d15400d050f14407914010a40100401620f0f000048540304c840001c0307010280c40800e820380e620f840d100c3d61341c999244070031548021044c81e2014200702810300e5078020b0800d030104a00c085012202a106c0002003401600c0d000420b680d1030507001d05400b0107201020082d84280e0240c200300496540d4800e1600500007014804c9079118007203c101800341035140c03e92815035080d1510b403585d0303003400f07030480d01544102805400c2c42519044e5403440016000b9841c440e2101260b00050b0480f001c540385038071a101d070b0081c8102 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 671731483 1250 671730233 671730307
    0x70807110706050301030201260117030d0603080327060402060d1b0e09071724030a0302100c082e090f020903070902041a070501022a15010b 62
    0xc0c80703510080c0c0325035251284c0e80d51551000411340b1800441281c03107a0130303030840e140002c9004514141140c140c031002c3c0da42a80f05c0d0302d4503402c1d40300b01d40050549514060001041103694400745104107420009410344002080c4180c00c1844030389419481500900001001490408050040300020380d00000e45500b0f1143d900640f00704040140001c0782c0811500d0354646030800c1500d83c0022146802543c56181800d0511121005020342904c90030b030113412244500c0d801441075030003030300904854a4801d5410003075107070942d122010304da0307a040490064030036008a1040d0f001d90700400d5000507503407040e0b0861038014100c41010b200c15400120014490001740658100380300140300059a500c402400c00d0324054080d07001001301401404108125009000d05c07980300d140301001e00d991650107150440c028442d411410f900d03010b15900c0d444040103400c0308804502040411107001e00c21000600010040900c02c14070b81103020840c81010044a04004e0b40b0052401d03080c44200751 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 671732733 1250 671731483 671731517
    0x10e0712020c16060c021914060c1603140114010e06010806120319120b0a0506030a06210209071106070f05040f08030a080a0606120207080706090302060106030c020114070807 77
    0xf0b01d40d40020b0000b9070440c6420107501c0d2010355000c0c20700c6800c507140751007450035800c111103128034204030744100c1d00403490794003c0405004c1a03d20402080034080f5481d100c2c0b61141d51106140d280ca1a607610b00182c0301040c45950b43c599050313032aa01d000d440107643e00f000444e00303098000c0207290804130303000540001d1207040014202442006c41c89200200d0300d8000100a000b10709210030034a420520302080544503c0d1685c0e0540b501a610241c0c0ca0f518031014001800d80c81d03105020201101001b00f002600b07008a445409200301d90b140d5180c1c407140d0f001c075030140180f450700445070010404100c0356406041050303907a50850810500300780d035828003180c003101280e0000003281c20008a00000c241d01404080d40718402c010100070141c02d0401c000c042c040d4000e114061035500240c58024804a001a41c1031a0790101e030a0259881c40d2034025200c43c1c081c4036680c0420b0514840c201080c1c018001d08000115190803180c2541d52030310f0841d509200500381c2c009002c144404000242 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 671733983 1250 671732733 671732773
    0xc01060f0603060501020c042a110f0601050603040f08160c0306060b0723070519090507140a03051305030a0c03021e03451f021905010608030a0801030b010e0712020c 73
    0x1a80c4c0b0b2b040301c00c0c080b0003400e03410443c0c005c0301a1442e8100a0040c0119500d440503030f0341068000300004800701c001c2c50005990322a0b20881c00c40d6546105040b410030007a12145c0050b40c1c0b18070411302550360344100e2984503015a0100921584400c0441c1c01030340307000b600e2182d20040d0841111030280d0f44c5c00200700158114180003100c0400c0c0c10003031008044501800390480b045c3e250800e205d04020941d0007031401000c0c3c02c0800c150b02c41307001c40c100b044541d1050861a402c2030680f903030b0b01c5030351401801e0001800c4080f00940103004003030792640d440c002501da1002d00c0101541c5017003d401220740002c00c402c20300c6070490f010780404101080c00c8640d5440c0e40700648055082225400301082805034020b01429030b904000c0221028044c0e0200d0402c81e15201680120f444a200d483c1c112701401940d080340d85948000314110400c00e40c0841401c4c100c0703004100042c0e181c1d803903004484240d10212070f1000071031402d10f10131070b5a0308140c2c010800c200d01c5400b40d8203050a5081d8010030b40c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 671735233 1250 671733983 671734061
    0x23040b0f07020909070b1b2404150c090501210e070306051311120c19050109150504060c03030e0109030c0303050a0507140d020c01020c01060f0603060501020c04 71
    0x40c5002240e2038085080c200b02d00741e040145400140314480c41c11048040038070a8501844140c810800c1c14681000100180150002502200e00b546480c01c0009140d07610700312415643c01c288a907514500c10402d100d84885000c02c0d994001c05281040019030b11140e0a003a020f007095241004a0844030440c4243c0c400c2c800d100e4090034147d855401c001041c3d500c050b091001064038052540c0024040b40b240d4583c0440a03203c06200c8180a221103080854112885800401001c02c521176003480c480103500386c1c3e000340c0f5011780b4240c0f1a071166a004500c8a00c410115a0400041c018117000b0410300500c6442468003180301c98034201c0700d40c20340f144100d04902152190307847d032081541601403960300c950200c000300194503021900a204000107010240070041c0020030350f4080c011501124403d0070300c40002d641d91601010030354004c1c00c8500c218420800c0020001c00c40921a005890843c0c40c16030040080e10411701c2004001c1622985090508495454084148280d12042610 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 671736483 1250 671735233 671735257
    0x30e031201030f20010903021e090403030203010515091e120a0b070807180302060306060f0c2401030b0a020d0f09051e0d020a140703020d080a14040623040b 69
    0x1114900d485a40e161200c95144d6100a1183c0d10b0007040c0d9008004800301d0340c049609425841e81c0144c040c00125150b446103030480e40d81000c0205142c2c058004504a4609031440368440303480340c50550716030090b0019103078482021594002819000044a02240002001001503400561450340f0301402020308031006d40d40c03e001c22204940001d46603a1010081c11309400c2d9088090040041d40b44d40d0000130711901303010004c503c035615444203030f4100ca9800c0c03058030741e2079058611842c0c0c1c984030841c0c00d0260185541c4a074440c04041005c0b2030403281c1c807000b5146281c5880080101035005141d640300c0c5103658840b2000701c02c5060003401041400741000d80784203484103131405000b1010284d402031030f074010901703030b2200c80e80000c1119051390051992500c03011158107940c1810500d51010358004550300684c0103118201c4020308940590784c8030342c850b0100d8803910300c1c114001c07071040c6400b04090120402c03150003900d40c1c0f00c200189058800385041c0d202c01d0700c5401c940244c4400c40c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 671737733 1250 671736483 671736503
    0xe120d1d0f0607030216050103020306030309010807092d170a0611071a060a151b11120d020606010c11092e0f080a050706140c0304031203150b0a030e03120103 70
    0x250b9003104031a01b41c0a40800e2806525615050002c41d81e01c1c800d4501c03041c10881e400c000a002148121003600c05048882040514002c2c20f01c1051000741d0062401c60803c0790a003000103a5075a0400e00410b00c100003c0907100c4040c0300d8035110003d195580281000310b10400400001036500c140992124800038010045400c106060164801030743d00301c00110090f10701202c0040d90003207100b241090064182070b2141d1402e00d03101c118881c01904140d0007a029804504038818080b40703416149010380d088500c555600c9004452640001501070503103c648403000d100d078100000015032101002c5c2d08030843d04443e15031001c0d102c15210f1184200794401c10140008a8808501001402d120005000420304c0d03484454030b0b000c013403140f0000c0c030a840c0e00607000d0b070000c0d07002e4402401d0141c1c10750b902c0d07613580d051040c03840409040e1000040d1502c0704585001c1c640d040e204054941d032072580d5040c0480c508080d4000c000d161079001d8244014030600f00c80650720803586000c1c502c182c03220a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 671738983 1250 671737733 671737753
    0xf080c0f010f270314180d0308010e07030605060403060e1e0106180e0c040207051c030911040c09060509030307020301110c0706021c0c06090203030a0e120d1d0f06070302 75
    0x7a0b0b4a20200c0c042c40d29408200c0c2c03d58000c25030008001d1940000f04035541d69801e151802c0100750690900c0e8581c000444030584000d054010075044d040b10001c260010300350340c50190031001c54001740501c503400300c0b0510081c000301f41940e100c02c0201c0603200403581d00d0030b980d0686851401c042d040c0390025a440301001d20005c1100b02c000c541400005d4014000518010f08150b103e00b05052014012540415a10203000080040320b41088040c50300c40c41c02c111407407008003d01003100007998180060360348102641024890720785001c0c0c8560f10800b0490512900b141c280d1320034602c03103078544014002000569828400c008200c455207281664603c0c08045150403e041070384903005540220091500070100e502c1b40504c81e191601d089102070b82e0624141c03005000488000c0e40510001c64010b00c429000316008212000403101e80c2241c1040c0c0191603500e506003084000041d40b590151589031050000400055000030800074141aa00b808613000e504151415001a80042582 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 671740233 1250 671738983 671739011
    0x1b0d0f11010201110903070909240b01030b0d030c030f1101020a12110405010c0809010302130b0a090b040f180b0d0f03031a1008070210020417010f0204030f080c0f010f 74
    0x210280d501340c81c5101d0804c40700e000040d440f005184a82c4a00b5a1100400d038200980c2d15094031883c1d0641c4985600214070021080c0144204410103022a00c0c140b9240802c1c60240e900c101040c0e4143d89102c01000540e500b11541c4058083d40028081c81d01c1d04894045421b002600c141e0186580d4007500404088084d81921118000458602402c010910899034080166a94a9049491a5610810f090040780288500e015034112504007510100f42801c3c500010559420280c0d01d41d0381c81501e806855800b0310452003200000301c509001000700c01121038402c0c8104481144c0018181d8110002c52400010100304a85200c4140c641d50101901482001032404501c2c3c0c9107a100c043d10b4010807030b100c5019045109004030342c400904200d108003c0001007400c086019900e440e41c440c00c44202401c059442c640355400c00c103400f03520345a64800e46080b40d1300b10700e01c0c5402c800203880c1c42000e81e01500341e0000311b018100d480e0411003424000d02c20003160105001032154802400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 671741483 1250 671740233 671740241
    0xe10020c1512011a07020319150507020613050717030a11010204031a19060311100503060303071103030706181709130f06030b0408031b03091b0d0f11010201 69
    0x581d2024040c81245a1035003200d62260640d11000d00d4000c1031140703000040c03050301618600079032501c290700054400500134861807986911401c4214010b243c0c500e880d00642c0c130216188401070b4004000074008042c01c00d100c56516000c2c0302a00d03401604c8202c402c004405444074a44981d200043c0d00342a182e0205141241a5803d0001c60405082da0707a0644801d800e01031044100074002e010a600415030b4001c40008820000c08110169032490000301c1410741c0c4100070710441100300c003421500c2c0100d00b281d21411006000d1751806030141e07035080941c1d900c82e00f03e507003503c4288503079400660750344201442182e00098050801d4240e2801c02c00a008942455841c1002400410381d25102e40305170300700c4003160b010b000c241d0100c49041007005020650014101205a10501003400702d524010341c080d410240d20500742c82c0d07074040c201c402c0380b2043d124185d05501000e070018010f144c0045000e10818020411080441e5176101d201000214040a4800e8441e0960500c941c2d070b02489 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 671742733 1250 671741483 671741509
    0xb0c01150b0a02030909061305040b04020f0102151b041d06151c0f270b07090302010903080310230f0405060604090e01020f0a05040e0702030f0304120e10020c 70
    0x7003000d1400026001c029180e001c1c2600640c0150185408a84240d42d40b80c22640001c4000c1001c00032071416041c46000183c0a58050b405640012100050382d4800310306e0360501e140b10400480039407114800e080341c1041010f05031003a00404e2201155006014800954018801c048060b4034207000d002c00c80405821170241c07441000c1040380020f07080544a00384590010720000281e600303a15000403001c3d000044410900703030311072804120161200f6018088540c001c40300c945040d0380382a410340380340b6600d0201a02164900c0420000030710000025a840301c00c501c0700404207507a405113903503043c0f40080d464030b6a0b4072002902d85103040c094a400741a9908440a0000d8101140424094422809544000b03a12010034028000c025011030700758101400f0003554909030a5002050b03a000390003800d0300e031000b5034003003000d0a2000056401c001400c1418500e16102c039524221803034491400c090600414400c45c002540e628402c10118038919005841c03500300c85420001e00401c1c500c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 671743983 1250 671742733 671742749
    0x120a0b0d0c0f27050613060605071712010b130302100f170f0a0b040b0603010f0806070201020304030f030c17010602102a0f2003070309050315060f0a0b0c0115 70
    0x51441c00c1c0c02441d82040f04805240d1500000e003030303d820000c00d814020b40e8900103059030a0000003c0e0003a0302c50004c01817503028084030749454a6440b40c42609205501070800b0a0391541300600032000070300d0081c041c1c0c4000488004203180d40741c0c0800c0402e0300101032280821110303449840400e400020180941020391040c031524641181d401086001c003809000005c2d940d00100b4043d505c45034080305070042e000302140d07203030740e03490090740130710f200328003860030b007070291001140f0154014001d880c0a05d6054448000c440c20341b140880080c04420308500405c07995003040917a0b801910401d50103006681e000c0d0940c41c1f40c1040a1050b40ea21400e0194100d05150a42c038000302c0110600189450902d0203122060360144104d900070640c1c202c00342c4407108031504140109000000340043c034441c0d2038000180390340310100340c0c03215403083c09903022a014900041c6180b80481c0d0411102d6401840808a2a203030307045464a50405500030000d030307544820380381041c406100300038000c041c00c4c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 671745233 1250 671743983 671744009
    0xe070f0e010230031602010b010207030804051c020d03030e0d210f060e0907140402160f0303061206140c27061b0a2006120a0b0d0c0f 59
    0x103080002e65441014110400006103511640c0d042000442090320300c101d640c402a07103d00f0a4201001c000800c101244007541c03800c5520016540003082d1101283d80044195003003034600b005000300c00000006011001722001600d4005907150366240702c0c802e000703a400007020100c0420061401d8101f030180c000340308051071101003c0a5081012000d8252000d000ca40d42c88203144a0b0050076268011400103071807501040481d840009080d0203c1d0301d140c01c03818030001e003d4144000c80c0300d152810020000100b600c0f0002c90007561144504d60704c05c0c600000d400c1c0c0c1e00c80141005d00500e90045800e262114000102c000310030360055081310075921414900b54002400c0c0981090b4103c600c041c240d210b250121380c559a0501352400300400d038012400c40001c1a1000d0344030014280c0498404015191500e000c0c1c2d12007002d503031842c01c0500b0007031820303074001441e400114008000c003445076281c12043c801920350f210700c000c40c035100d201c00c107550a080c00e0301d88007208000e400440c511040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 671746483 1250 671745233 671745257
    0x30306050a0b041a160503030901060b0a0504150c1704230f090901140a06060f030b2202212a03180f07031103120705030307080601050d060e070f 64
    0xb1140859080b900d2038400c00400181c00300401942d40200343d00e0b2a03000104c0140174050000110055120301840c000030800c0c0350b01c4159a03c4140107040191001507001e000c1030140580780c5a0307028203c2405c2c01d094188005e1a6100039210480c503200705c461700d0340410100104040e401d804800850004483e4100b8550308002c0b03400c80c0b010001041c49a6004404144a1a420741c00405407415200c440b480c1c6141180304500907260a109070710004041e07008801510344a48100c0800f03810007080420a00a4032a00d003003500c42c040a52080c59500708900440701c0041c41d0343c0c43d001c03c00040100020300e8003000031000711040c80004210b1061070030300e60303070403080c40030491b5408005140e5501112030b940031040c0c542280b111380107190b40f0900788007100340a04484400306006048045031502c0314019411145030042d1440188540c1c0140082141c01e409404080c0d480003061400d1030030124a1201001070f20383c5a48090904404d0006024400d940f100d80c3c90380d07880e0142440a0752010b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 671747733 1250 671746483 671746499
    0xf040912111b030a3206150f0a030b0702030c16030203070806250c05100911030a0506041511072103050c180609040e070e0f040308010e040f02120109030306050a 71
    0x142200014000e2249808070990048402c1d24078017041000703c1044481a41424415034030703401a5805c09040100c681c1100443c0740c40c0c403c514903818080c0c02403c0051555a60f00104003000d4240c1d420f6020034400c20170509000c000150488051440d0300105034698010306090060b10342080c96141c20110410440e82c0080303d130042e584080c07400c000e07041307140400110b6540164404c018158050700300303058030440c055040684103d008402134460500c06d6403c2550f2000c000d10020300580080001401103402d0085d880d00950076440042403a815985409200794003045084030510507402d158146a01c0311040d1107010002c40c2001c00c024184204a4a894002c5410007d00c0446044075250f0545481c0161140c0715000b61060043c4801c141d022510b1b00c0b4107002e41038402c41c3c2c10f000a004101c80352039050140c2d8050f100c8241e16420604207280c00d80008000740c4c0d15070070780301c81000141c80c0e1000c00884100480000a11a42149070040a03202c06500041c8100700d09501406104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 671748983 1250 671747733 671747743
    0x50307020303160e04060611010e03031e090a08030f1603050705070209190608240610140906031005040c0306062705030a06050f22020f040912111b03 66
    0x112007400701582e00003c0803000c44c1c04104083c0e1654102c1d081c09400581c054015070306240700f8040c00d00a016000080f2900303030f6070740002c503000d0000103042481d45c0c104001e5001c2c1190032100801c284d40e40c05134940c40e180c145510503110b0b100c000280760f0410102d15018181c0c01c03488620f41ca0180b0003414024802849405810006441548510041000f00c1980b104a62403210030440500503603a685030526120894203617120760781015100d4250f42400c1200e00d41e0712400005180d450502e6245904841c50ba800404074005624100085016030340d401b00654400c00c42c200d0450002801c00d000c0c00160346120321407100f49420b0000500249820960030060400c4803105001459480d20000c07100c01070740d52205405000c0e24603042c0a01070b207904030302c0c0307e400f00d00b0300103425480d031901400044111240426003800d02900e14001443e00003249645071200520100d4054080d0310b40703050200d4000c240401090700d00c1710000c41200b042c0502d18901040110980051098002080e111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 671750233 1250 671748983 671748991
    0x910050907030f18200a030b010332030d110a120b03210304030f05120a090809060c0a02190305070509090147010c0f082512050307020303 61
    0x71540f100395000740d5074020303031200341c03061000e4141988000e4581000044046145442e01c00d8284000740ba980c07a04042c1c00300002c5039840900740c00f0b9030303107141c81d16640c050218610341759a0500f1000b850070240d00d500014019030028015640d901c080301264002c450303404c2c48040d500102817001c00310700ca8100039004000c0e00c0104000c140e4011800002e0704000d01102085003d56180c000c0d00c1e85401254080c40c400c2c0e12a484d20f0102a00200083d2002d0040044203811481800000751202805420442e8150300c1464150b040c1034001c0d0028101b138000341501440c0e90300044040701940f900c0813003034508900c443c4403010014210380320161100c030540540c5003c0c81c000c00c0800e25041c003d40c045160001e200030300c05100001d500c40074000e40103081040300403005202d0038803400040d0020003460360205071901c09011503903546112641008110903901d0701b00c18070840500d059100310340200e0030341d83c0300e01c01d42500031840c00361030075004001c805040001c203000b0071503201e80000c01c0342c4e08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 671751483 1250 671750233 671750237
    0x10804030806190b0406050d06081f0b060f1c0609020c0a0201111518060c0f12040c0b030a0c03050906060a1208040b1602042009040e0304090e0a020910050907 70
    0x10161a001e603010000f2869030100e0041035001400080099001001c0c0100c071140c12410310505030f403903010755507a0b541c10507840a50000010000e802c1d250581c03141185650191900341810340f0402c00241c2600031004211a8144018a14080034030714410100540b0300d0003421400c00e854024032560316000312200a060080402240c60b90395410070100014007201d600380b20311407401103c0c403012481180020286445504040360741059410f00351400144072403032441c109070800944405605000d802901c58184480000c50958181c4000354450b40c081840482c107a42c240400804452000700b032074a441c2c00850a020745540c41c0074031182164038a00d0460400c042da800c21811a200d2644100391001300003880322105910031103a6001a4003c4404101d03030248038203000b45103828219030000c00207080007002e52510385a44031605002260341100e040c030352210300d00021950042581480c07039102c0701d02ca10452801210050348001c000c9401e041103480c040104002000141c4202c007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 671752733 1250 671751483 671751499
    0xe0702070f14010909050a0e060f01060519110a03090f0b03090c01050a11010203090a0309050915040c031e05060f0d0816060212070909051e0a020a0903020a0308031005010804030806 80
    0x2e60380c0e114013600c0300a0042000100140e041071b00006000302074020300b855241c010742000485003206942c01c14100c1e421034866a15100c90000065903c585100401c6d040c130800c0d0001c0044c02c00c00b0400001598800c0c0c4822880509081c0d10014000081c2d2100300b03414030030010880b0b68400441d44030f1200c40c0a00740143c443c0c110301016070343c14144030b101036140d620100c104004800c00150180e44240282c842c4408070361228248007442c0800c541074140e0824001e62005241029806142d91105a190004281da80d00725010f041121200c1c0d104d095a88650901900e403034100c1841400707040881d0404410341c007179a520109805007010305040c0340a400343c07846c00d00400b130301101da220520a0381b0111501d001880509a4800c41c090b1006282c0303400300144248081114044008000d00d410280e5030741d414003454043d602110400f410400e10000c000010703141c0c4899039003e148510540c584906d403150801c0204106640074070304005256081c000030070f4014030825008407042d92081 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 671753983 1250 671752733 671752769
    0xb0d0204150b0c010609061203081810090501050604050c0412080d02071a1501020102160f08040905010605220608040201030504020411040b070506090a23160308040e0702070f 77
    0xc020700110354082d514003580058a90320741c4030107500c42420341d229841c003008101e8a0f070f596030700b25110103c0300a000c54101c4000c07681c030022081e40300044220900860388502aa4019403060302c0701418101e803c2e84d159428012289410701420740d2104a054070181003e00d05401009050f200c0800a48031400000d607c0701d03500003035011502c40580000030210110094084c0669000080b542c620303800c5002c03404107a81d588180200e0b076510000300c00ca0001c10f0015210040102080c460884400c8000c0100190740b40190150900804ea07a03100e00c0e84844084100c4400580d14070341c850030355a04d164040c04460381210405811540a10300091156101d10204000301550b0307001c80780c2c061000c42c00040d07034407042c402003005520807030940f8a00d03100c0000e07603a07842080328401456001010341700d40170010054901e0382450703031001c102c80110201000d00e00881c1d80580040d01c54050000e81804a240810502c0750410308520003802960310f84000c0704d110140902131404401a828180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 671755233 1250 671753983 671754011
    0x90c0c060f0c09060f030403120603020303041401260412050c1c050d050f0a1a03070504092d0308072f010618050603010c08070827031201060e03010b0d0204 69
    0x5103c034403034040c1c00c183e45e84515400c8610503402c03c640441c006810b44115803203050013401014112503015000314181820b04900a417441100d0556504210b401e41c1e84500b404501090844d4400c10034090410509150400111400b00c4002c3c0c602889410411104e102c000007581c1c0380248030b480380c040c824044206045482e0711410307880e4038440d4200300031b024101d54116005c034025000d8010030403110000c230024603141c880844000c2d03416000914200034608198008405291203100c1504000c0c2d0445056464140301ca40c5001e85145181038440c00c268003c0c1e03040f83c000f0188c1c18410004444401170044200100c000c0c204040c0d42c035801b80382004425040350700038008034841310b040b10f0742c41c41245c001010102c0b5014460360819051903000349c05610018018461507907066910b0b5a421070400e114115400b080b01d020944515030132400d4001d202420002c0841c0c168041c0d0344d45800001050b180c0300c0016148240d00d00707841840e043c1d440700810304502d68169004641c0c2500d002103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 671756483 1250 671755233 671755237
    0xc050706080612010c0908061006120203220302030315040b0907111c0201050610030b0105160c0306060b0304020315070c0f1128060305010e010504020c0a061802090c0c060f0c 77
    0x3c2051541c24442c200c180d4030741000f610005c0c1d8101404072200c1d0359600d0b00030000307009a1710410011039001c1010070180d80607038000350f60245801f03910b5900c1030898494442d1007040d605059005801c00b1051181890301e854000002c940e08503004d10200c407218000480e81e12000d0455800c0c010200c01c0000520000e21152441402c1d1019110001e001e200019028000449410380302c0d02c81114a000503900921421007214410303034805d030801c650b40680d4000c2082200007500d03080ba5860300000001c00900500000d0711030640c186459003010720615241c00b00922204018210180822002580c8224010f848a401240220014110f410134a122103420301c00c0390341060711101c3c400c80240c00010107502c035448003002c03242c805039a00011000c0b501b0a029502050a17428010001407909030003070040c02e40504262038404495035039007811074440199080e240d03528400b00100b94a4410142c075808590034031064a820210340c1d04503182c25000f0040e41e00d40e0316100c00b02e1160803c000c2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 671757733 1250 671756483 671756509
    0x9090b070c170d0b01140403050706050f0903070303030b0f120606060703050910090602101116111009080c010503040f2d0804034b0204020d0b100c0507060806 70
    0x10b050703583c031002d601d074540140c416040c003d40442c0d100b110f24909654000c007184c0032a500080600113603414050104c9241d40605122a000c0700c060084030510b9405102540c000c500c681c400092001511080c40311070a81c40320340c10700c508108260f0230381d007420108920358080c0b0700300d900301e903520b010303140988260180b01c0c0c026401480c1d1a80504130290840a880305884041e02128402e110031701d4850180d60b81002c40480100301840000d00c000c0b05011003000b800d1080600740350101e2800081164030080d0071402c00003541c040410044200c042c056a0b21040003881c045103185487c0e11110240080b0040090604e89200d0804800d50744d00044080e009102208402c0307101458100601244c106010523106000c03448100c2c3e40da812506031a0f000c0301c111205005628120100c10340001d0b2a4802c204110091002c2d100c00507038480c8000c107030314444d2410003d0742c9440c10061080f02c5044001807000d01c0031a1094101050000502008440042c0b5210f0f90030f60380d460100c3e031000e642e06 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 671758983 1250 671757733 671757773
    0x152d0c06090304140907170c0403060f05070306080d091e17030d0b01090608061002190501020c0d0804020603010e1302090a0903080705040501200102040b04061809090b070c 76
    0x103000d141040800180110ba01e42100380b81303d0030341c1c0740030003514030300550380303080492801241401c0f100024030035141c0c020074840c8110b05196580d241e98060b44d0f50301404022040e9240c0070080340d150035206000290080c0c0000f00310141d4484000340c4031501c1402501040420789505c3c14014032454000e034058080c0010380f01500440d501c90a64030303000040c103c80100e082080070540380d485a181001180c24a650f07032101921b8040038411145900c40d526402c40c0149111980742c03280d1603410040e454030580c00140d54080c0c00c0380d12420801c10200800403c051101484056076a00042d68159011400326203015150003c60003400c200d00d0a0007900004c4d500104002c4002651113900e04c24000c0c0c507080320781c0d03441c03e80441e000e00ca02e0045a01049120140040c0101c0318140942da28201400052601d521400e4010319600b150b448000011142429000d08400740c000000041542c10f1041c0202c58084da01d6a02e040d800500303e108000ba504110028402c1c0300c111040a45c50314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 671760233 1250 671758983 671758993
    0xf370203010605310c0e0f03100e0a0c090c080c13030c0e040203010b090f18070807030506090f0a050a0f1a0f180303060a142409152d0c 60
    0x10310b802001e60b4403044a080300c100c0e021138002d060100306010b02c00b16080c01e559142055044001080707044485240000d404d8403030031a440052030314503c50b4500c0001e214005141899052400280c07918071500203004c0f02d824010840212508554101c6c0c212002400c0c040d11050740c201848541c50042d030000d40505000c00300040c05551290066000780d000b40c000b88070380301110041c4000380c04140d80c0481a000c5240c0020300020300049040319000000b800e659078035a84100c41450701303200b0f40081c0d4042c1c004405004103280200b0042c400052082c01506012a0ba80c503056210140302070082c00401c0d80218140420054401010070804c400501201034207200d0840365251008032490005044803004504481a001003a41d12682d1b0050003030301d6260811000f2400c064070700c582580c000c1425100484141110280520200a5505056107506c00c000801c900e102c289080701c42e03032000c1088000e201403035507500311058050303451002d82d801603a00c0218050303114410942001d0f00034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 671761483 1250 671760233 671760259
    0x51908090f06160e0105090d02041d120c0d0906020a06020a090909050706030b2b08090306070804060501050904081b100c0801030213050c1602011209050f370203010605 74
    0x860784034030f80d2078041e503561031011002e00040d02c01d0312070809045d50010880c0212030052401d50051403811150348016000d100071030461910708007004164440c0c440003c2600300600908024603600b00c05249082c0300c8007894802d01039210a00c4441c041e00c05038002480108150065801400528407082d0400c13402000b800e02c0d5403203007400c3c0140d00000b4105030282d625403034001c0284181c05104840100107007160ba02c0144001083d42c001c0710303051410300407201c09541c2400118401d03134041c1c85c0d18000b03203090300e441e904413041608410b01c40d140000c1800b01282a200541d03501d00600f0007040c06400004c041149468180c1003030b42103681c145210100e80d41e500140060481c0d200355840c410324002c0d81440d00039100300f110014101001401403c00e21054882040115401814030141c656046100c2c10151030081c0b500f650940c0c800202c2d03601c40b40040146041c0802218010100c0084007900d512524070950f40040e0000310511104080d55400e40c0110000e210050030540c41c0342c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 671762589 1106 671761483 671761501
    0x30a1401121b0b0f0c16030804090615080c0304030315080a1401050114060d060302060415020c01021c110705100908071e03170d05101401051908090f06 67
    0x106641c401070300c4901011b408030255026005050341c1d2400c20352148123484aa82c417009007c040c008107001013940c0b00340b005400000d004041b42d13880d100e9007411009819003800341c05c85190b0404001500c0600000c51054142c07064400f541800c0400d0360590032a8001d02c50301024442c02d003000c082030710b001001401c200213110800520542c594020841c1da0b0010b4012114107550503088170240c940400081d122040d00f403005207280103950200060500b0021141000e00c000e88804810408043c82804060701015151894001e01d840700104619010f124948140c05000f030040f41c0300a0402c80075003d0f40030b1020000e4150729554504415100f81502035100040a0026140750659401303a540602070914180b4030b10727814a0150030384681c00503521810710400304040f480314005407208000031140d504016241e555940d11007814050a48840d01c6240600c00412540c21 = true := by decide +kernel

theorem cover : BRFrame.Cov 671582733 671762589 := by
  have h0 := BRFrame.cov_init 671582733
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 671582733 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 671582733 ≤ n) (h2 : n < 671762589) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
