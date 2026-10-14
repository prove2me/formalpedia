-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1666
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:08:03.799738+00:00
-- url     : https://prove2.me/submissions/a466903b-1cb1-49d3-ad50-8a1783815af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 299460431 ≤ n < 299640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 299461681 1250 299460431 299460451
    0x207060c080103051c080c130b0a050c12030115110c0a080d0e04050c071e06111207050304020d0201140f0c0312010605040f150302040519051005040f030f0501020c15 73
    0x4241180015400106100d0041d00420141c002081c403440703032840586220880c1c142842c8008d51200c840307411a07085803408031300043c80021900c0b18402c0074448210b1039005900d01c0350640d4101402c2111070003c010072101000002810102006c0c410400300c4100352002d8101c1060b00e0326030400a4445050070040d6020541d10000b9103c142801d102c0c0a01c075131210344902d42406059955100c00c4a0310301c6100448500144218000c41e1aa00c104840507940580b0686d441c00c6101e0545013070480109542c040c00b10a10800c07015031102000b240c0c151ba424a4920f60800c1c01c010545100d010741d10071500384481c080340444418070001300400c1201c46e0102c007108640c1cce80e4034007103030a0701c40c90140c48101000c40c04100140484000c0e00401b074039184c10094281616a004209110a48926210b1084d0145801c0201d07003031801c20f400c0a8441494606d240ca400d1100c02c8030070754443d2100400b0710003205903000500c40d081d03040d40c5500c0c51000035204a2301e40081c41c80f101d001c0c1a140f40b00d40c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 299462931 1250 299461681 299461693
    0x20a0f0c17010911011407060f0b060406030209040f06140909030f1818060d03030b0103021902060a0b012c030c040912080916153b0f030a12030207060c08010305 71
    0x142e0746c0101e21072680440c64103586c034034040c1b80e9507480340948007082882c08401d8440d9561440d540d50b4001410107070801d954010707211040ea5040100b52421000841621307881d2160038044800c072444011200c000564440480c1e484007072860f4554030528412001c0c030381012070314001c4910842d44040281c3c0c411500d0349510481d00c08070310010603041d03408942c822060810f440c0000c0c0260820100460305060060424213101d403500d002520b22440b850050b04103d003040804150707486a100800420720f4022465940400c01000d082c0c0c500000100006500b02d90001c203a13400c00071300c8501d4901800c18458985546004d081600070000b0400c0490003103800911034140000d40d41c850321004000c00704600e450110280700003c802ca001030704200b542c1c004071440e8202e5401036049809048021594101e50550f84e0f0008580d00e5029481b4080030516034441b40d85c005407010240350814950042c03800080000e50013441044401401c2d036003400c00e21509503811060700c0341282c2c050025281 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 299464181 1250 299462931 299462963
    0x70f0f020402210a05060913031e080703050a09111e04020409020a021c020c090601110f10060803130501030b12060f0403030f0207020a0b0901050f040b090a0e0403020a0f0c170109 79
    0x80e45e070100e0340d541d00b0107000300c0000da0362150304043c5801070b0300a003030000c003e0880c015540d0041403104a079134045105401440500c0723525104e042c0d80081c0407401003064610581c0c802d2415051115514032603034062500c0c07580320f15421051001d00b100181f0031540c03596240c4000c3c2c043e400240b031400c0580252941445481da4210005441c164580d002e031000c02410010410b078103102400050401412a215402c840400c01604080b509400000c00c2e10304894071008065508507001030085d50418048d52247c902d140707450405a401c2401d0200d00f104802010540042034142e000360203100780c1080c0700caa901d962500d030307004900990302400b07000700c1d202c201c00aa201d5098001d42083d14113400b00000a081c0c4082c11000b01d0500d4190701e010b2503034050741140d4105800c80030300054000754215442c5020103400b03004001e0398800020500d001c0c1c4000c1c2d200c2103006070140c40001401c0c00c0d14100300c1600103120160001200c102d0980c0003189201d030003800b403810219001004514015 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 299465431 1250 299464181 299464201
    0x90108150708010f09020a030902030618010c02030a02031c090215030a050109020f092b1b08061909020409060e010f05241e0d1b1a070f0f02040221 65
    0x1506135203d018600d10f5851410351804003e40c0301c0c400b9482090303515442c950042c3d5080c025240182d11000e0000841c11504480900715040d0404042c1594000c00c5030070030103038000c029100001c4c3d403100032240700700003189402c0241c029410020f5000359890171055007058030f1000f0313501a020001c0b003008542c0c0c0f030300a0401203100e40c00c072040c1e5441080c4640a030510f4662405a50603041c40c0c8004510100b40300d02100c0300d4000e4004a80501c108400c5010035000c04100304024103003040140500e04081179401d0849450750903002055854800600c255104c036004250360a46c459401c000e0180205c2c1024003c100a104442c003c504140c0400d41c0032201e030081c141180341c0c580c0c800c005002202c040100450308070b1030b030361450001a40302c0301441e039442c10f110085501a001040003410381c0d0710101030440407500550490540f451147d081010500240d43c0103e500c20208a00003040e424440b90200710810000c1d4018000034105000341c040d64004221404d604890300c9881e01c65001c10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 299466681 1250 299465431 299465447
    0x30519020106060e1207170307020301050c030408040302091510030501060e0a080309010e0a09020414030f01090f030c020d14160608010315051b03010e0618040c0b0d0b0901081507 79
    0x100000391040c0310900482c60304170717014194032044404580001d695030394440d00c201a4000070049513000030840d441503040178050643e012002c889a5850762a00e0399956405006900020b4000e081c10340010b01002c0c03620003600301560b030003006180103008002008014000034091100064421a44c81a103402c00101d1710094a8004000d1818504843d004480c0410302480140c1e11420b1120700003201401480100050607401640341b5005007a941854034080c0001e400c0040c582c54882810045143c100110f01c0f5550316107080e0400045a0002644040c2e0203000600524a5403419104408000850fa0241c4424100c0e00a806e6603d02e41960300e11024840507041c008031104142501010340d20442c0d10480702012444400b4521184004640090304000c2592030020240840c6113859078040013a503550007280e5400d441c007559011410b684a1080c0008035501040006820400d0340102c8003600010f491021590380d19071410f80e0350082045400104004107002c03c24040c404d20007 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 299467931 1250 299466681 299466689
    0xc0a05090f01031212020d02090108010f08060106050703030e190b010501030c02030904090201111009031409130b0f15040314210d020906030705120f070f0c1e030519020106 76
    0x201d100581ca142c96800d8000e8040b00043c08020044404030303010034041c4064440303101071880040c0c40304040710014044001c180c001000c1000c4201d41084100e90000b11203064402901e171807500d86486140603000742c8811080c40005018620f500441c2c041c0c2010381c0c142d640d02424905085907600e00065044811401140e40160010400d03c490340c100f41d0010307400a41306140440c6880302100c012410031940c000c2a500703072500c44800c036040c5a40404180c1034071443d00407036450303c000c0b900054040d0801101004040341c036000c4040701c4d55106201b68071079132406019143c0f0820710500d03110241d1305c24007003103c078980001c810143d8104005040c64075013900f00389498002c4091190240341d40c00454620141da5004c10030548685c42c0d1001641c050601626000d80301c240207041804e08038401000c14031140060402c10022a070700256440b00190b02e0304000500c6e8070203017084001a900710b049402c40e481101c280104042d0b1010082c2902c0b201c2e54901d2a0f06411305078100e090355810b02c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 299469181 1250 299467931 299467951
    0x1d10020901020a0f0f050d080f070906050d05061206070c05010e01090309121b060e0f01020f100902030111161a0c0327070f080106272c0c0a0509 64
    0x10450000484c03124809144501880071030132440040c0d070300c051400c1c1100701c96500242040c07060008002d5010303100f503000354403420030150302810b218005106008507030b007944580740c1302e001040c86078403550507004803000300d5000e0301c10915000740d001d07101c00c03200031085038036618081c0c00703201544042c815107d6403a85075841d080f030146040c446006281503450151117646807407948045091007580344100070010b640300e90000e14140d90401c00c04c42c8032000907138107540003068001d0201c100840d240d0303061075110400248070005400400d00414400100d4100031000103603038102064102c030300310f060511615148483d0541d00502d0503003c071099540565400060010034000741003c1c040310316071964030b014040c1c4124070009940c9021491342c03010382c01c041c1106044c0044402070060401500102c803928055000007111820301c203030341e50f1507040d6040e0340c0d00b0007001e00d03d10001103d00d00748816504503902d508440c41c261301c0e264070711034641c8164031194002481c0d0504204051040e81030b50 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 299470431 1250 299469181 299469193
    0xb03040b06041d071203080a0c02060c130f03050309040e0708122808090111040506040902160b0a14070e030c0409051c0306080d090f06050f09041d1002090102 70
    0x80c14040a07004903e0700440d02d005004691907001c40410841c4014205000c1c01c00400c0107a0501500031744028000150b01c07400c00c210401642d070001a02070b0014104010380756955405c03c5040c00c8200c460700461b50001881000009012000004d82484107003101c0c10024013000d407a010317641342c42903c80c050080d0041c050001d0629406000f82481d0343d07241000c040e200c0c44001e500c403040520450300038045004101030020300c5200740b0510000c113208006407442c041c10200060450b004070710501d8800d680018030380440b15904051001c0741944070000d1315050400c0403800713014104007140301c4503580d641d400046441d442840000d501c000081c0180a0a044144c03c0c040902100301080d5102d200e50721010500c1100101c11408404065400180d1142042030403814407200586800c2006803d0704180a8418401821400c507540c03030030041c0d0340b0401119800d10501401c4a0301c2e5200c0d2400b044001c1c88010011014400c801020945040540114008080b4050f55103028016440a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 299471681 1250 299470431 299470441
    0xd0e010e06040b0417190f0921050307060501170c010503070c0b060a03020a090b0f0f01020c011808010213420201020c0109050717060405060406050c070f0c08070b03040b 75
    0x900000b80c2250092a0b0014044c06410a034046075001005c0305412001b41c1400c110015408050000a0142840c00c2c0d6405407904084000c19401d00710014811604c151700e080810004004807204d135540f01400b40a00c0d03075501505901203904a22102880c0583c0c0381a00d4a9031294003201c0c882e40c0c45845e002d03003c00254440d54500800104015004100c0c0c41d0080050781d1003c14400040c070a04401003407407074910050085602c40b01c074031316000e01c010361008400c583c2c0100ba601c4c480705003881c140070713000ca1995400c450280241c3c0001c189520006404546440181e001e0003036562007a41114080e541818481106400301040303000700d04000c40010b002d41c00e550408800708500d10025041c843c22700600d50031900000300403201c5a001e800100104034182030001c048071680e00141000346010780b185902c4010051000b402c0c5903076540054000c0140d101a90b208540005079145c1d00520392500d08801007072030103940c00e54860b29000140c100c03040d000300c910907a030040420940d5210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 299472931 1250 299471681 299471693
    0x601092702030a0506040b0714040e0402060a120905030d0501060e030709020d0b030102040b03061906020d08220308070818030711040b06030a020306040b060a020d0e010e0a0801020d0e010e0604 85
    0x51000101d0b8103020750041d00011440c1081100d008070b001c0d403000102400c00d0034000c2c0800309141000c1d84100c4040c082000320000c540c5d0026807068050341c3d06980c800c07618404407580307e90302030519603d91400c0c80c05024040c001000c0c2c080e0300c0c26007808200b00e980740c1030305072030440074004010f9240d840a00306000041c3e154018103c41d407400c030307000704030404441c00003426a041608146440e920200402c0a2403a203140c40c04d965400d5004119030160a00f14000d4440081c104c00200380a05140410701d00400d1620707a51030140054070f0440810300910b00108a000f0a88160b000555240c01041c460b180100c540781d5920101d00017145000c4840c1c0c0c0c2c1c4070341c6981b0140c14547c402d544030011030a85c1c6405006601c10140725000698030f190600810044408045559000e08000c1c00a0280b0980010300782d80313007000394101079102c0070a40d401224101e207220200b50704500103090014000b441500946111a0300000c180800d5051411480c02c0754000f14014546600c0032000c11f0120300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 299474181 1250 299472931 299473001
    0x60f100e0316080102091c030c03140906070f02090105091915080106030f0b070302030f0c03061f050403110d0203060708070203040803130303120b060306040b180403020a0203060109 80
    0x6000380666502c544518200c40c0001c896501000007030b500095525402d00e00f4002000c94100e01a9004503440d1980d113009244032610354009081c40303240c50302460312940f0641511b103180002003510b5507039011303454116590807103410120b003e00c41c108008210351500219184c072451044a601c0c0c41047c0230b03220180a000b488000f0042100c020700c0200d59140c081c0030707420145000d13051006101400d460500f8849500624280401d8418424040c0080390005603940022510960640382e0b12641d0014808210110106000d001e4851456081e640c1000c080c00c210390003041c0c041c1543c0c00d8842404040b401310700c0000d61540014000410241c094040c0340d40010003441100d081c1500c840c1110b00e164080f20503520900741e5001c08004044d840720554a04400e40b80c030500031503500d040420124040900b040344115185e0075010501d07118019001d0080780d02d5507800b400c0b82030a0801035195040420241c1c028005c141c000300c0c491115000700106203451300f412101500411502c006541 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 299475431 1250 299474181 299474207
    0x70608070c080909070c050d0201020f0405042a180501030b060d240807140102010c0c030f030b06040f090608061608040309030b101403010b03070e0a02040e0f01030506060f10 77
    0x2c1d406014029290b00e8444103644641d02c41e0302c842141401c1414120b04d0301003100c2c040404c6a00401016400040305015101200d5040c0c0e004a0b41480140d6012203008030300340c1046d00c1e04a801c8440d9512944440d02c000c8036613280e00b1716112141c541c4011800d45280005141d0080f0042000d41c081441580c888108400f8011480302c1145441c5a01d113a141c3c1c10307902400c007943c0100d10a11985032003c01d00083c40901740001c11406081f101c0103080d0005001025040c0300c02e400d08481b030b00303000e0740207009044002401d00d65945c0c0c0303651480010301007501654200515004021448101c002074003400380014000c0036000d42182001100c00f8400100103c0170058164000000200c6d90400c640c00303992a103884211103400c10281800c1c144c2c14905e964880c0c3e0401d904c0c1603003510042842c81c00c4c2c1e40a1107115909543e5400c00201070f118951044040394211002c00c281c4040d1710000c0760599210350180c814a031103020402002c58040311005501021144003003803030a00030310110000e0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 299476681 1250 299475431 299475443
    0x30c03090109051b0301060509012d15031e09080f0306010212030705070501050f0c220f060c0501060501050906120a0f0c020c13060303080601080414010f020d0b03070608070c 77
    0x140b0055540c83d810044030607000408418018144107031483d081c01041c000d801c003500d030001d135585050710001d0508020000d82d100081101c43c00584503083c181094064800300100000030400c04000030003c0903910350b40c5028807240f2041c24048441801070f062404c1d003280c03040703081c24500a90345569034405880181075218595889440c00c1200303001d144030303040586a0b182c5407042c90910500b51540108160070b9500380c44108070102a08006139099420002816002c6801c0c03c0b95411300080a9040a00b200710800e030001810359001104031041c0744940024000c882c2e0316401035509000342c0549a901030002e000056002080151075680641d8030040801c03038607042010350045840b20586100141c0048000f201c9504200b0511124440070032000c000191650314000c205c414080e11150400071104041428030050051745081c41d0315101c000c02c1b18920b01c1220320029408038103244d007164100125083e20f85400309441044502d0b17500c1e858001da860a8048421040b440e01c11200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 299477931 1250 299476681 299476691
    0x30201050d180605010509060a0303021c020a1401061a092b0f050d02070614040611101406040b01030b22061a03040b0c070c03030e0a1509050f0307030206030c030901 73
    0x401400c42050704816000700c10021301c079418607041c0304481d80c005001c603009015000d03003040000d03400916050402508405500c00d100108012030404c035001e24094665460111030101405044d840f03913040315a0810003150240041c510305c9004c2c0a8103c400707503c41c03441041034022076500c0c4410524102c1d54050b04e40c1100043d43c0c0d00f00c60040361107040e1010350005a25100480d01000001d010b0011030070600000900408200000c0c4168003a140800150080c1c00c1c800d1002045100600c904000c414060052061400c001d00101210440e1049080000182880d4000d200d0f200383e812014110803c07260750b042c49020b112100415102c04240d40e480000b400c83c441a105000181c031220801c1d0f981d00301801c0c001400c21019002840c441e9080000100040d94a28407804995150030700003d54a03058000400d00c0c2030940c03090f2011040404035544013a445001c1c5016104111004540409083d05040c0d48085a0000a4001c042003000c20350101c0e42034003a552141c0c1000000c11 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 299479181 1250 299477931 299477951
    0x1051c02030907180216061109101806080c19050d0f0221130605040302010b061810140d0b060702190603060918060b040b0a0f0609150207030201050d 66
    0x400c036402240c12155a400500d814041c11008410203403803030401d18419814000c4c981010340404400c1703040140302c2951980000401403a100556850050082c140f45404800740b201034030040724400041031004441c0408203200340030303204883c05010070020709070034440f000843c134029074031500d42e08041c44002d00104600030844d024904040130310b8280980c0f13412480c0c560344512942e0380d80020460300c0c0d881c200706441042c1901c031310302c0c660801c002051075146c5003030903401080d20400150f003229000502d44000b08410102c40400107007542d4000708940d040c881180d21190144450070000002c1007141c1c0130035801d81207012800c500400b45c92820b03001e54001080c0c0b40d1a25801207070103500d40e10401c031094062142e0001880a40c4080c481d4000b14108030f100010241030007400b9554981c10208940c41d0341d4498542c45c40c01070450404652a50b00038418500300b440b60000203030f140789002c40c4282c2ca480e981c105201054000345402403d40d0700542d030b56007121059940c42d40d0741d0700c100a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 299480431 1250 299479181 299479237
    0x40e04030302130b0a030903080f040201050a0c110d080c0c100e041a030a030e010206070e0f1c1403090312091819180c170705060c07050a080d0305010608070e0105 72
    0x91145c4540740003c0d61242441e0207407081a0003000480c0880d4503104001c0541d8100040721070051440c90080c03602c0540d880c003a0340c458002c0c100b4503040080203440d041081200001004092144000c40d0417609a1204100d03a410030800100d00040b0b44c5192031000d0b0a054001d909518a80801e0403400c40c0c1d4080030030314000d42a80300354005458651600403a5806009194000038a03140c008041d0252501084400b20f0000810b4022036070043d04a810090144400c1000e0b503011a43c50750840c2104041e644d40d420240d40584203000311000e0903c0c5240d8042154107c200c080d014004905900004101058004100b503802c0700c490b200403031145006100d11840303080101040202d84c016410301106814143d084451011188074820022020006910040751000ca54041e42c5240d5520044d091400d0b6500c89a00000d02c0b480c0800c101c6c01c04503000d003480089540c1009030781ea172114115403081095405002042e4403182d00765240d485000141803008841d0113030304c42161030020745 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 299481681 1250 299480431 299480437
    0x110c01050411010e0307030305040b1e0a080103050c010c0209040b06060f030703050103210e120c030316170f0a050c1c020309090702010507020304121e210302040e04030302130b 78
    0xb02e69144049825800c150f800a0001d44019010b070000c0c4070960851341c029211b4403450040d03c44605001c50800000c800198441c1745401e152070380349454040f9071202401c20682800111214080c1e1501407500e03500c80c500f910b050382d400500046494580351030700490310b040a45540e4101e90100a050480c404140c01140101d81e2542c0002d095859818610f41414085601e07542403c8035007820020640d204815586010741190110a50101e0895181c5010214880e83c2c3c0c042c000480ca20380030140c5001030361112401050190a00524032915000701d01c03030f80300c140f0030b8032406109074140c043c400c80260014080307182c2100d144c012000180c400e010340b40d107243d20050303200081000c07007410058411900001140002e0001c1d052000000c1d440313000f035005031504000110061014402c545201210320044508c209441c0c043c41d0400d01048450750514502ca880f6407511110154801c2c070880701154500081c1d0f552645855600301c010b940300c4a07406c0724850403510041007400c010401 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 299482931 1250 299481681 299481683
    0x1b080304051612080a0e01210204090b030f0a030c0305040f0f03050d030504050d0c0c0e09010203040c06020a0206031b1b010c030606080f07140408030301060201140108011a04110c010504 82
    0x30860300309041001039001c2e440303400880c030f400700407000032001810b804152a0800c000e07041c00c0b1744040d07041c0d0040300d5880703001070070822003c89600c400c1d19010b400d07070050042d540900024401e00791000c06055440c04030b040070910547c49030013840c2c0844e00c13500340e801443d4803074507101c4e01d881d6940380b800742003840503002055400310b509020002c101b02080b27074000030165820140481e10b06a01d41d551202d9840c15000280407841c084402041514074469000c2d100162090fa1b82d41080c000c918002e4008039021140c445580902041c4140000380c4004081d40c0101000c1c903590356001d9004000c40c056181c207130840300502c503041207644280c60509040c0058400040d0ba0000780310b005041e03401640c02131082c0500c00051080c0b6034288159a948843c0f903061450403480381c6090b1454912a0390320113480307030101200124900e42d064200000c3d010480c0801500750342c0b18580c11f42210904210707030f80e1700c1009074880c441c1d605040d005044c10f04800c850160a01e042000420f00350340302210 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 299484181 1250 299482931 299482933
    0x503130f080a081510030f14150f0102151f1701090b150105070204050402010e0904050c15040509070e01180e0a0e0a02010c0807170403080714060709061b08030405 72
    0xd40384421541c0304440035449211102c90071280f0034401c0200ba0310000d001d41c804d0815461f11074810ba82d0071250001c0c01c1e0260744070070b0035505280509090400d0100c0403a042d11514004011401561000031404640f500355004001a61510102d000240d541d0450308044c2d080e00b02d000007445a1814a0b00b40c3c0036480b00000302c1c2810b81031400c402e080c44014400000c60844c0301c00380255990200c146c0b50300e9039042d240003980c0d80307070381c00161940c003c030003200b59008cd4442c00f044104400880d505c00256025a80d44003240682d43c1400b071280035038060356130082c51110010f603809105005022007000181002c040c0344a0302502d10782e034040543c0280214030600c105110f03250903544180d0070149000d0b4040d200c04185a80000e03d40c8040c43c0c000f0b003480c40007041d01c20a004014800501406220901c19a00ca0782d81c5007410058010200c1036800030903004104004ca00c0100b14144521841d584000c421400c140050f18000300010341a54803018500044000410007002075020f680604 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 299485431 1250 299484181 299484187
    0x6032003090d09080316030e0d050106030c0602010f3b010f0204060e090f0c0318071d0f0606090d030306080115150c0b060904140115081e0d0503130f08 67
    0x3842c00b40112003a80d101d480c09500410490300c050300c1c00d030405080c60b54585800c0503944c0b241c4000860103801154050415446c0c003a00004010b8446040022240c1c07a80003840520584c0c4180070441d124140d41000e5480c8249001e80c1056051a50b40364512540329110644100285039500b110800c811003030a107540090180140c5d60000c0d03c80c3c800d6101161088441d152480300807160210140004214107004004203d10003003403040317800d103401c080040390b0840f0341e2008680003040344100b038a0003001c0920003080500000c0c40c8175910843c00541028a00440403041c0048803540507015404c05940303450110303224800b80908034081040c04840c041503400c00048401c2c040c4400405001d0162034041900010758503a0b40c01d40c0094101c4a11031903941e103080014000000714103138480782d481c1840a0300d190010150f94400c3c4c40b01c1100320345180ba005008002d8001911094182d81d502118606541ca0b00c200700940c0d11a900d0300100481c0b2940d6aaa030480142561080b2100f80002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 299486681 1250 299485431 299485453
    0x510050c0f011d0102030c040e18030c0c0a090e0d05030a091403040f06020607080c1303080a090905160e0907020f030307020601080d03061202010e03030f1c050a0e03040603200309 79
    0x1071180341c000300f02500001c600d1410290f80943d0725100d10f204800400800a0008021000d03c99071040307510000341c141ca40e18030b07081c0903498817540c2540d0354621030324050001241401c40c0e4464880d1130709010004098200c80804c0a480e42d40009011480b00c0340c480d10f0110010302e4800740117079000007140045450340d04002c0602c00c0000c241d0040c000715400706041162240c4e01c40c0500d604801c1a01e0a1076540151503a43c180419554002900c11000016001d406c00d81c40244a0201c2d08060404c21268542c03240859900c0200290f1000094500264110620380181c9058001038180102c0b40c101490b40e8106007150000c80d040c00142e005100100041c1505114041c4164128501040319900b014140490b16000003800390411820360191041500c08104a0316180c017119070140e260140f80d07e00c5085080d0800018000d1802c142c003088114005000e82c07203003400420007540c2001c0c00c10b80c04800401222240641c1c800b407074402000a0a0020001d600661001005c3d0580c0410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 299487931 1250 299486681 299486711
    0x6080a0b0301022125020604030f09050303040e1e010b03071b02060313031206141504060816090306050f07020f06240d120c020102160503070510050c0f01 68
    0x140e03403111406a4010001c20702c841c07851070681400f641c0085150341884c5c0b117142c503c010f0301c42e000a2551001c11100c000d09001500016003511030342c8203039954030303895603c800304684029061042e91740591060000b805448191444d8507071011180a002440903e0564031101d0483e01b0380c00310780603100010601503c107502c07000b66980c440c0f0259501a204150340e012a000d44402000344280b503c481c25004101440703200c00400c00054030000b800904c2c0c07a2540c5028800b90740025031702c82c900c003031265001c0701ca144081d20200d48158444d081d455981009000c0c0c445680c804030b00411001610120010f889071145a0044900300b5a9501c2e929203074001174034229207004080410350140382004205c00c030310912500c0c0b0362000c1c4c0d8460325000c402c60120f982800b03d0b28005140b400300e81d192440b802c1d0b0044807021a54000d9086030000003642c02d482249454a0060b140c044d00041024042c0f0708242480b11a000c8261a089150103e480d00c01404c06031600700c41c02c15030751242042440303010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 299489181 1250 299487931 299487941
    0x913060501111c0c020f10080603011a0604090b0d0519060f05151e220b06040f0329150102060606160f0503040f060503010501081006050904091b06080a 67
    0x40c030b10000e1802e0800414810350145600c807107401009402e01c001011500c41062200c581c0101604580403440f2842016182210440c0c800e0b000f5803804035800501c54a001401c0031201c00502101d00c0c043c20301500c0d00c00b612401c140c05800003410344c0a00000f9004010800c0c0e83c00d1400d50b2800d12044601c1c00c00140c1d0340c0f0071100c10103181031409002042e802c006d64082c1040089a441c502066102d00b40317034600e400c1c1c1c2050380e44410701c91042c04810154001900451502c031800300502039641003000704a000e54041c06605805416007840001c108149480c4076540d83e2580c034505810240c65200b0000702200c40035441c000f0030b5a0048030356010014107801039001c5906904040c04007070480c14082d40c44401401c1120241810380610009004550280c1752200e086034096440309005402d941c0f00b0710419000800000016030a4210000b202c3c0039654903a440740d10302a000001c00014203151641078501c03802558406c81d900c03034454641740040241d40c45010382468042c0807103003116 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 299490431 1250 299489181 299489207
    0x7020d0503040203060609040c0f1e08070305030307111204140307060318110402090909070e15010f050c0c21011a030316080c0115080c010c08040501050904020913060501 75
    0x8014801d0000507031300171800c2603000c1010b65407506180e4407410544501101c685c8900300c00640001c000c00d0200400061002503000d060000441d550750710f603034607542d16651002905540052001c070304481e11604c851030b5180b40e110200c1b002c003050010344c071803658829800344845121040c0000d815040900501c5e00402c01030404005501604c041d010007044c810100030450300640702130140340d6031160b056a0311014041c00300c11032131418080003551921070f80070381e090005008001030031082d031041006d00d0010042e941d88010140030704007540d2079041500c03602080e01510310b0000c0d543d00c1c2e00d01c5c1f81007400325000080c96103001d07250902d03084030114482ea50404060988203d01038500004549210420301c100f420750b82040d0901004500409480d540c0070350801d460fa040580071040d609081c2d85420013903c4440c034900c801940c12448001004142c16001c1c041007250b9800b41d0007030028202c0107000903143c114108000b5590741c1c035200c0c20f0041169181c600b4003181d41d016282c64111 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 299491681 1250 299490431 299490437
    0x4902031509100c0f14070c0b0405120109031205060d0210180911041e031505160806010c200904060e070617040b0601200d030c1805062b020307020d 65
    0x48032010b40051060244440c5001400311079450000183d518008860040380c2290b00c1d040512388822030705c1c4080d480385c41103910a0070300c011181c942803018421480c80da64180c6441c0090ba075070320344440c00b8120040c903681d03001c2c1c00000007202680b644050b046040040d503480c2c1d01d11548500358414018415000120b4480c0717417510000202c110b01080301c0580351025540944080d00c070042000ba01c2403074000803d04044420703544034682003900101e0081d095517074000d08200300c1800071500107804607080b42c00911442103480104034000441ca480c01c2d0520040e100302090032000c1029201c0c240d0741114102c0d85d500c0410240e050620060f00500954600354440900e44c4031041170015007c1c0000e0f11248010000c03446603805192060780040403040510b102104216105441e140480030b58004039003400850b0b030400c0d1003650340e810036070080309015410364201018070051ba0800304101c80c02d0429132010702d060201c0350f400822040c80c40384016950703241c9010004c0c1812100c40342130040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 299492931 1250 299491681 299491691
    0x20c09010909050c0d05030c07140a14010507060504050c0d0c050301050601080603060708060d02040609090201020106090216080c030c0a0c080f07030b0a020a0e09090c490203150910 80
    0x14004110025002d000729000e02502c006400c10303031f003180700d028401880b40c0700f011000502629039004c1c5050401c4216850003607248e171104108480007150481d140014001c1144400050950b402070b40c0281c082c1e0103c0d1407034100a400304100c10303101c04082d529440c5a46c020492485d0074015079900c41e0342842c04482e035003403560110381d0f0303840081d0509042c00703407601c0005c13056142c2c8003e2501c4150014414000903035959051001801c4440b81680107508009011840201c5402240c0d0f602c10b51400001582d1103c0d2100c1903d81c202c2d01002849010404c4124850107082010a640306d020303906c2c5481c241c1c0703003144403860040c1440d404502a042094200040380800c01503903807001d00303854050b956181c0288111380c22120f45003000c3d0300c003a920041c00401f480000d216641998180e8030800304010414410344070b20201203031400c01078411020311014442480900303800c3c07034681c8185030800503d0ba0001e03050200468160001001240070440c4c841400c101500c440443c280342001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 299494181 1250 299492931 299492933
    0x70e04050108010c0813111807200c0d080708030a0203180c01021c020c030d1e0908030d021c0207050a17090901060e0109080616030b010212090420030403020c09010909 74
    0x4905d020040001a011603d102c1c800c060000c030303d0403019005401001c0103052038820515549040055813200001000c0d03800d05520f14030007810602030f505c030300c6000341610f211392410000c0e94580f1501c1180c40090a10403080020400d201030350150045d031320f0241e180d24040e03006100404089040224580c030170101001c1c00d98000c500300512031080d08841104200e50b150581c64070344912885c640600ca42c0500c000c3c001c1d48440c40111108660302c48000910051400711044803183c05204042c0d0400c010071004440c40fa8002d0402071040645040d0284c428110201207170070124050760950080c3c0c01150070003200b00f420310b00e0603a40d801c0301400c00c10000046114900e05000c0c507024000301403011000c0303a0045140000603d81402107c00c14a0801c0d0880c041402c40e000c1500440d00346004041e0030347c00800d903039143e6a9100d1160f800c0c401d0810030403000e400c424031308441000f54452a60300c0c09d05018011881030f8003c1d002840014666070070301c01c040105a004411091501880b40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 299495431 1250 299494181 299494187
    0x11716080d020c0d11040902040b130c080c0a051b0a02030f03031902030c03040609110d03020106030c0501020109080a0320030f07090905070c020d0804050a0e0910051605070507090203070e04050108010c 89
    0x17800110050f00d0000e0120783d648089401030009180550b4881e0f080b2040306021b4155812000c0070145039981c1d01c1c0310383c0783d0781c1b100b4005009015001001c958103203c0c10410740703101041c82c03407048128401c807000c0703000c1e503004681814003d044803083c540000080100c40074a24400c04e814203aa0700c411407640c9442032049240c0c0c00098001444280c170340310590188904c001003811610001081c8800d0000203240180c001e1030720b84400c440c544608100050698010b10440c0398480d04840e01a00e44610340008130300910094603484440c0450204444514161031b028610540d03040810a03002c0c1002000a4803101c041c0d484001c020b0f003000c04000001d80d004e1034100300d4a074182c8030303000400701c03a240c104100d00517908965003050708080000f03003903032103100c0140c0200f03032006c00c3e2900070010120000070f68000301c1e020014400c1041e41e50406510910044c03a0950003881a51400c075140c0c103c0342d059a109690318800a411a000030b082850544a02401460004000c02c15410280400307 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 299496681 1250 299495431 299495453
    0x7060504023006060d051e1f020c0c0f03030d0902010c050631030816120c0f0e0303130b1c02041e06020d08011716080d020c0d 56
    0x40045856002140031915228803802061a0140400c40d010034030b07250032a42c0160307040b44940d0b288907040215006003022008445910741250140c018107450918017104101c0082d070840682c4212441102e04000301c518120000690740809a90f54441d4a9030a1900503035a50051040081e440044050b0364000300b21a10139450800110316507400340010b9903848801c40c40540785000740810490702110710019070102c0b00b1038500e0a050401300c20302c002503108034408000c0102708800045034900400c9600200c1d0340d4800e2401145110440c1d101c07405507014a4450008a00e80880304110705800c4202c402d003040f0141c0c029814082c0c02104003440b55810f2084185d062000192203400010706400218103548108066603629958030f00d01800c2c0507a03030041c485007070008801145103840440d10144014040e925071410f6424908502407000401a071400f480c818202c1103080e002e05940200014a00c1c000030306010242114080d0a00c4003402059105410b04003800b03000801c010a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 299497931 1250 299496681 299496683
    0x2a0b070503090d180b07080c011811060306040902060a080f0c07170a0e09040f061a180a0204170601180219030b010210111c0606020c010c0501060b0f030a050903070807 74
    0x8080c00001c403000c1800400003045c0c109131701c0c3e68400249101030042ca807009100c1e02d03a10000070080889508051600c200d4015030007020042d0842180080c0e10b0004050341e00030500030000921403400b41c5c002a240c2d130207881c2c3c4001142c0e00e0ba0801605144140140358000d0f00c800d615454084640e4940142804203503141b201c800011030054040d500c224480e08401c1c03030280400340603040c1b03401c0440f20208030b01d80c100c41403400c0080c0210309448000910000c1280a80130760b04419041c8802026400300600211034241d0a0000040f00310084100801140b040b8021388182d5042100107030000c000d40f1000c0c0340c000e004212440c1401c08200090b5141900391600091412101004034142190380d0700b03083c4442e00b00381c00c1002030800d440c01400b000306090300c110fa2030303106111810700b90b41d07081c4101801350b00440c0480115500500c803190200384070388000154161501e50941c03082d0066011900b00b090b010040000d1003002d44a21a00419080010b500b00455555040b02601c50301e40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 299499181 1250 299497931 299497937
    0xa0e0c0910051e0d0318140f0d14160302011707170c130603020d0b0102010b01080a021e1612170115030e0624010309212a0b070503090d 60
    0x1407500b51902e094005440f40c102c0040c4010403801183c1002008841d4040c100e91041c3c6c400b040c0081e0b122181e1180c044c4ea003070b0241058121922000802504141c21f24069482074035900303001c15141800d1004d203a00908000c02a0051421400010251910840d1102001c1d80003000c0c817001d20340003050a10340705000991b005071650307803065840007130040c058810640302c0c00c200d0220702250590054980c070168080c003041030301480ea004900740e481d01d0b07a12a01040000300030604a2016030018841400c100801814074075240801140640c8101c08030314156610450315000c000c500b003e80340410029240000001068503410038101006204001c1458405074554030028081e0300304a03060010701d01a24514030301207800030080340000c200045402e504802c0c210711503010388600c02600b070b0098070f102c0e114510b6581241c018580089802d05000f841e00441c180c0359600010403545000005203904443c001e8500f0075a100e4000d800d08003485028000c00070105d000003003403503560b00e42d4a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 299500431 1250 299499181 299499199
    0x1b0e04020d080a12020d050708070f080708090a0203031602090c071220190302060702030a080c0711030d120c0f0827070306051501031b050a02030409050a0e0c091005 73
    0x41134452009a00020a01500105044c0c0341c50b4103d0340309500c01c1b0800d4480107070540e2080002c0311414002c05185000c1a45c04000c00e1140d845101d106a00000d6a07080395242c007155000030380342d6000143c80f0030391100b40426800c21800c001c00a81e0f08110a05241c07401c0c070300340d5983e00703021a40d2010484200810a0010f9070700303800c1d54000d501318070006420b0b034414500940111003208801e0000b40d0140c89440e001c580704510010880321000c03d165605c20b41a182c241c00410316a01410b4103403114900305088100aa405001800301c01601ea1a0561081c0c1070f41400303000d403800e1103070301c0f028085880403461007103801041c00c80c2e0080100c0c0c0724240901d201c02c5407900204040c18840040d10031030402108004039540820b000303008103240b0040e07464800004409403440485e00e414644042d411080c14180924060201c0b081c0d180103407410940c03544581c50880c2d0b021240d42050076120030300c01005420030b001c0c0d50060310065480140c81d18140310403400020300b034820540150985 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 299501681 1250 299500431 299500447
    0xf030a0201090b090406090c170c030907030809060d0c02101a01090e0915010b0d15080304050618060a0306091802010e060d020f220608131218031b0e04020d08 70
    0x5070b8031030b6001e400070701f0b003c201e409035400005203408100380240c1c0f000e00095000c200b100302c070441544e2213a01d04800a005841c02c40e902d402c4d094010103281500301034140100c0c000d038015401000c00004056000700352007443c03e4a080709440b0f00f003040010020303003040640e0203668040101e00540790102103110141e103c000310030780ba01683d014516181118140081550413200d001003410010480081c050700014058000121385135110f41506903000300001c001c1410240c024010310f5107043c121242400e002070104505911441038000040e80e1040280000ca8251050400035480410014441d05403a4001317003241403080410b511507800410b207045561016011101c1002e0440c401940710300701101408581c43c0460701a40d000001c2400101c5c006d440b07001c1c142d03c80c802c11040540d011400d0b4460401703041a148404c000c00021012043c581d880d80b140c0381e0025403003020b0b9840d1101c03400d099200c00d8000d82d04880003079100c20080c400966a0b0002030308101d0382140700165180ca134 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 299502931 1250 299501681 299501689
    0x26250503090406060509040b0604080a0b0408130e0708090607140d091a0405010b090912131d09011820030a150603060b0103020a051207120f02090f030a0201090b09 72
    0x40ea90301e480d071050401e6800300b03007070764844040e0107a80c0060340c0034054074003e042000b032140118010f0031510b61200b0380300004200d00720402900310f4001e43c0131078035004120141040018007504160440a22002408886544040100d50001802c0301500c46030400740401403566a504980c8070240b40042800c1c41d000c0c035194440c45400350b03c41c4100318564240c011003c1c2c00e40702120b0540d02035113003024044640c1841c0c881644100703080006464044d40888241e07440d03030030002070000d03c140c078183d02288030694401c0e03040300013001c540421110703d80404001c1c01d4400409160102c100104a2030380000d826440409090703102c181043c43c09035141020070301d840104134004d01041c070541c60340c0325800341c107604c008141d0303000d40b00511019101c0c05c019002d0303205103060350340000c108006240c004090381c41ca103900304115141212040301c0d02202e040644000642d004200d90740010300307a01c40d20300002d041010b5541640905034501c3c6580010346062220711a0a07a244000990b81210381c0c0c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 299504181 1250 299502931 299502937
    0x8040f020a09150f09020702152125030b01050406080a0b040912110304050603160c050f0106140f010906080a0921021b09070c06150326250503 63
    0x4031490b002c108484200b00212600307809071080300d414204100000c82c001025000704c0c1c0e2004d4000e0501c141a14004125580b55402000544490030201006c90b1028901618140c02440da02304016450b548034800003842e1401501040700b0b06140810355003860f41c201044d901154101c1c18041c03240e07603400301888042c104134a01c195200303107410b04000821500f2646108004015600c1000d0000c0020030182d83c2d2241d806010740c031450a00014032205a039a1076900c0341405442e003d00b200780315a82d01498104020035618032039450703840500410700d5082810320400021070b0440c00d00300c4004000391601d181c1c1c0c086d0000308092a0000780d140c1c80c480d0010280c180c0e1015180142038002c180051800c49202c0d9403c005010748804a10100c0c902c0b10444200b420003040928140c90b400303001d80f550742d0880c00880c0d0468552006041400c00107010320020f5002d5460b16282038191400711400d0084a1030141c09100103010043c030344004101140d810420240266007600c2c41400c140745540 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 299505431 1250 299504181 299504189
    0x130e0715020312160815011d03030d05101806050d0204090f0f0302070f1203211103010314010b01050307020c0427031206050f01080a1503021903020312090108040f020a 74
    0x16030143c00d0140c000d00080f44855003220640e10401291240c02103001204c04810500e40055000c0070f40c403105840c0e908a80e04448401400c903898107179001014815112300700c40c0c558002c440203608000c1d003090340010701203440d403447c000c00a40f0b05020004180590b103d07406801640d0f01c05100e403c1000038240b100350036401c08040b503125499894029036503041805003401d03100340c0c000300240851041030760040785030340345d01d61500c010514040251266070030003c810050b9210440e0400f0544840700641c0070310701984140406c0030f541c010803429101018600c0c0c0c10050100304001c4229400f103608101160207c0d00410064640c022000d113680500d4255015145037000c0c0d001010741002d030700310080300800001d01040b6506e104115010740a1030016002c95000030020302110850707070106e54200da680108a440075103130307004941800d10600c80d01c03044036070040c028402d40c90308000441030342c00e5a038203041c0340040f04030008000e0540035100805914405030480c00b10350310b034400c0502070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 299506681 1250 299505431 299505457
    0x21e03010b060d09020117042f1302040e060919020a171f08071206020d09060204060207080c060301030804030209041103011a090c0f12090111070f02130e07150203 72
    0x1c0f003500c0d10720300050003240022808600003044000403103100d079240c94456a0814038402569900d02c6095031050700c22801003040920840d9000241d603140852081910a071000c0107880c3c6081050840090202415007071165149400300008040c01100f0646101c103403040168941350f50040c01d80348044039400c900001c016010400000e08600d080205400d83e85004210000741e80c0d40e003480e2102d581e40070b4000400700001d40c0a01240181d0010640094001c40003c0e2010080d10b504c012a003164200b900142c000f0070307040003030707907810060480e2003030048600342e145500d5940c809665200300d100c000e024032501c01c001400d100c08120b030080c1e0403001034000d220020f4058020040440703040c610b03030300c0b541035100070842c203043ca9000e880300d0702d6034001880d16104d44215001d0020f400201880c580c2c3d034a42c4840c4c69034a00031405008600c2c1b089144107511600d03481004100b030342030707000d1652243c0303130010003089031000107400000c07140d80750482c000301d0308024002c03400d6102c1c0906031551 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 299507931 1250 299506681 299506687
    0x18010f020301060507120305040b2e0b030709150c060b010323070207090e0d08042108060405060303130506480f0601031b17010e1207021e03010b06 65
    0xf64000340100541031003840410081000f03004140c0840380d055070301900181405000500180c5100e45c801c1240d400c055000039032400c0410b2080340d54115030032080000101100f8006081e030042c03203e0003c1c0c40b21442d521900020704c08000c111410508002c2d01160321002c0707994259010390f019075a40349010541007108036481d0540101100107035500300c0144275254000503024014402d5111141c80d24014120245440f0021039440340050419940c0c40a05007090440202203620144440140c3e191401c80b442c040e81000200c540040c88213010341c108101d820142d21040700d2010590742c0c11a01c094880d400709174094400d4480f84500c0586608003403401410140b400311907402040820002c100e60041201a40c3d00c030014104288610b511113001400000c4445004142444030110304104a40d42c4400c81b228101d0500c410954030f940d50300100074000010b201d180c2d94100d441108a00d401801ea02143c1e402d01507400032043c0020000d041c81ca2683c003904498090580201481e032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 299509181 1250 299507931 299507939
    0x109121b0b191a0a080d091412030d0c0f080c1b1603031d0604030206031302010e1008100618051c02090c030a0f09150203100e01080706090906050918010f020301 71
    0x8204945415548160035804c00091281800a2801041183d5684120011345428602040351603d410240e03400045800c500210400810203020b290f40360880c041015080e0000150030095901811020001c5110070401aa03104c0400c80303032011110210b0707294620344501e016050101400704004000f28a00b0000709155005107040500c25501c0000a10f1a1581041201c00d02c61840020341008045c0005442205003909101043e0700606003c0c1040c96500c0c0019081c100144160012038440c2c802d0009a0004425007405080b050909500324640340400900400140c8202c91040844082815400c2400301061424650181c1f041c3d00900340400800c0142d001118101c41591510b05000150303415405094501508007841c02d03011000c142508000e50f06c000d110f54a441c0c2032520000d200c0c14102c001c503000304440ca000d8403005042c610001e00007410799028200c214107011050101707940b00c081e01600110000c582414071010008a580981107001c09000c00500c0480001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 299510431 1250 299509181 299509211
    0xb0f1005182b06240e010b070f0308040822080d031a1509090108060f0702031602090a090f051e0318010503060a0b0c01050a0e060405060103020f0a03060e0109121b0b19 74
    0x200c00d8078175038001202c160f81c98100f18129030140601c0030740300303012440d20500428000d40c109074106005440740c0d8a03042e4ad0701c2c034540005405121070a00e0b69100c2c0340408c10504c00b400443c00800c55440c1c00d00c030b061150000c003183c10003000c1805110f484451240c01616008030100c0f1000c400140a503522513a651102c0c9898220490380c443c00c005c046400a207010344080f0485041c00d1007101902208140754080c007848003001050410182c2e9075042d43c00c04a02a0b800f84880d4510820092200354409101885118070072075510320117510074003c01c1703845000009400c201143c2031030a5a2207940b0040003c2c401d80450b0b000f5140c0c41c0c000a05040c800b6410340295205400c6100240b1150a00404085d41d80304100c6010f03181c0e8109400500051030070139401305090400405904d085038481c0c0b036003412680110140703100790b0b55914404040140804002003010b1031400c0854004075114010b0000108800c001400000c42c0380c00035001c00841c034072100541d600d113a810495032158580708 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 299511681 1250 299510431 299510501
    0x905040b011703040b0a030213090914010b0a0308160501090b04050607081311103506040605031b0307030b13020306090102090307090b0f1005182b06 66
    0x10107040b0311036404824054000086070210350b140e04540d031909855040c201d0081d00302211544c848101c2d2280010b04d52058083c0d8801c45020791000c00c04503030150649402c59031814000c0b4094008014100080364028041c1c41524022400c10000050507207407103401040c0b0120003c10040082050106011f40001c3c0c030f62040c800c5807070f0003405449480d942505041c00307a400910041a92003480707054108132040002c42c2c042c60400d81d8110b80500307180050410180060101028141d4000b02c0b081c5d030031280301e508008192000c114140c00c2002213501e8881036400c90424500480f455046901c0801009000310341102c00c030740706c505080c5030407900b403460f1003001d074800c1c883c400c0480c41150040c42100c0d4140e40050050181d103103822440c1c400751083c408001d41c0080c16800309030190b15000d9403900c2240807561440e036640101401c0175a0306d110b04a40c10300400001100081180b09a86521050082d00340c4085000d080d501d8104050010102e4a08c4180c1180a248000702006800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 299512931 1250 299511681 299511689
    0x103050c0105070f020d0213050106020c011416080f040312050306180105031b03011e0b03070b04030803070c1e030203090406140307060c1502071101091e0504020a090905040b01 78
    0xa80385110035440c0110380c14061a03001074600031460302003000516086500c1e011151014141c000e22401004100c411503000f64828030140e00602c03a903030358075030740a42c802c40c2c1d800c4010103183c14280f800c1541c1c80c000e10481d10007007491100080c444e901c0907513074082d41c000310780c4a0a83d82c3c0c2003140c80c0d030060440d00141d0f0000d019407059a00802c01d51040300c11a41030703d0303001d0700828802c0d42501d07000c0d80c00b9001a140c1c94048d5664049800c070140014014a007100781400040740400f0b5110a05140c84426400340324011428041400002c2c40c59085a80180c0c80f460f0201c146010b40c01c001101c0340d030910380d1000d4038401d5502c213010550048084c094021080b030f01008000e0f0380f54441c41000c610103a0090f0706801000040c8441d5025204d0034951502807410f1400c0940c949046070200d0f403041005540d03030602a0403155103503a1050f40840a4202280140140d84000c150398600b6817682c01035610498003c01d0152000d4400d02901c402003010140c00c0c0018207142c20100348400007805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 299514181 1250 299512931 299512933
    0x3031b0c0605130504140a020f0f0403060c02190b0c0304020402040806040c1712042606042a0521120f040f0b0901140702011b05010515091302010302250b010305 71
    0xf200184500e4a80310700c40a001600250100b15a00d0690304402540b162a150030500d800b4008520303251401d1010f407020314400e042c00158604c07410806440c1485c000072507109507a000c08200001401c88450b182c002c156126060348a0302c0b2440054040e0045400000503803007007200700014092000818400c5440c5c8040200d11030803900c103015220100300d00c800385c46500c1044100103282c4444880c90010001940700d44000d414140f17903600780072082d10103407022001e46042102280c0121554000d1a207207081442a003494040420394442e20094205c001e42e003003400942c1086400d200e48040f03502e80300ca070350350350f4440d401100700550031a0041042c0200381c10b1000c40c24002542c1210248401611403401444070065005072a51100c07030224100550403011003c42540c000300300c40b01611070b100100341464012941c1c448800c07801c114510a8403d0401d008050480c103000004542d028030340036035200d41078041802165003800160082d2680c9400103814000d03680001c3e41030302c1c4220 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 299515431 1250 299514181 299514217
    0xd0803070909150e0406060503070b19051305011101060f120c05030309060f0f130b0d050a0b090a1d06011511070e010e0702011803031a03060c0403031b0c0605 70
    0x11050070212110144500380f400c5000c00140580f0311508102a401849400701045171529500400e003490510b91000c2907151000c1050203400a000310580d000f10310600e001802c04801c0701101c94240b18034866141448456001d20400d00800e401143c0544040c6a4a070805070342d034078140b07240a007040c906865605480001143c20310300441125660f05006080500b8104148071020269105100c48030304201d040001030704e00000b40e404100241380002110351030b000b09040510035210024030300c0010300c0ca00403d1f0200e0f5501d1420320341d0440380321100012001700044040341c40030030340080e401c168030500c400081c03020b03030084900070941503d90364010b60b075404904c41a40c50085014180e108000c407001440109140d21201e0380c010550310005c82c61000103010300414000922042d800a038907503090a5981d4803146c03119081c56400d400400c440d1074400c1c405000e0340158040101081884210304403c1c0100d5040c096060ba041040d84140b95170351030015045601c0f0441c1d4070003080c0d8107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 299516681 1250 299515431 299515439
    0x3080601020f151b0403060606170a05130b0c0d061503110a021c1403070903050f1515150d02030a11070503070308040303020409020f0c150402030712020109050d08030709 75
    0x3140302120030b62200440c03200c41c1c458a0320744c282c0d04141e41440907036800501c00000420988d0040000500701782e140c80003038040d02c4110f0001d00c003001701180522404c10060040c0d40e14072003e1100c010b80c001c84542070b10388a00321083c0282c8185814001442e040000100d500110141c800049130b142391010480e501d803200300b051050080400b01009608180d1480444225184a07181440d02c5480d04030318140502c11061040e07001502c0207070004070060410300421004205854a03502c1c003800034050926840e140300350443c00206410106490340744195140d48840c0d04400344210044c2625032140b07440130f4620000e401c120b580300e140d10705100c8044540c1d001c0744e00b2031b404d0603040f078040e41c500841510240c0300b801c80a0300440130160308010014803120365201a00d0005010f04003da07441000c13800c600c0c60030390001c40307940c07002e0821028000107a130001200002c0ba109001c00010b90090f0f4001a0303600100c50340714541141841000c2e404000d54a13004501c140c00c16110301e002e66031a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 299517931 1250 299516681 299516683
    0x90616020303070807050f13050f0a0e0f0a060905130203010b04111c02160f3f0215070507030908060c1204170a050702041424040902100c0506010e060906101b03080601020f 76
    0x3043c40350034003233801000410344000141103a164400c1c45450049150b40e641d100e800200c0704100d031240c0031060080152000c518081c080c01030703980030490781071111109502240c02a03100c1c40010b034500885203480682040307102c0c3c0556440720344e103081c00c401210480c1060445560085402c0710544601c146044400e0110000c00401301c1c80781032480495060342040650300b41150111809510580010510a10102c10468410b80e05941c1d407517200c0c0355915001e040c0c90362603006924547c104904000f0004004025541d82110b0888900c41d40d4981d41440aa0304501d130815005203800040c44100305ca03007107401003110a100341c1b0104103203035058003226100c0341d00b80d074034264548100300c2c46807400c801c100707450454400044c00014881d0450f40090b500d54107221510012443c0f065030306050200c103120300c03401414007001b1080c05240c520009a4001c1000300a00d11a50000041c1d00000e442182c2d0a5411003012300c44000182140c180502442c03022200c0038010301c16082d0081c2c81c180 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 299519181 1250 299517931 299517949
    0xe04092a0b030403050306040e0105181006140d0f0c0906050a050904050d03050a0b0901030f3503040303060b12040b1b07060c0c0b0f090616020303070807050f13050f 73
    0x920703400a242141c80e80c3ea0100c03929800580b03016805038440d640046100c00071710915000321100701d1040888485141c190382400b1a140c4203101e654a000301c10008c00142c0080c0765580c0604540140700d00380d451400c0c04152031142030142c00c01401c81c5000c50160840e034450402d954048540c255202e581e10100801d81c0c808031001001c0703800251007102c109029400c01900070700c4000001c144c0b460030070007144c003528090740283c2e44a0b41042d102c0d4184044840034050141c509000502c060001c103103110b407820450508800414400800141858403a07408400503168400c011952203080252a20064005940582c0d00841080c04102c42c40050f038004606198001c10075404d0200036200c801c01007090b2051039003444480c030f2211001481000e8190f1044644483d400305504004000520f030500c0104040011a0361000b0380c520142c000090342e82c00495807400d1646952120001c40d240c1c00b45081c03c0764140808201c007000c9012010700c0c003040c0c075415181708078040b040408001d5241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 299520431 1250 299519181 299519189
    0x6050405270c10050d2403170d1a090901020313020d060b090f04200a1e08011805150606030705161a0f07030606120c0e04092a 56
    0x100c484040d9085054034074021070101445005032440222001d0101e0204052029020001400054030348641c1c64188103602c82d0a60b52500c103c402c121079180ca0028090078040500307411400d1241c41c01010545040ba10407440800d420b0104641c1c1c6440d0b80c003440010001305100c0c06c142c20000300281014030070380f0301c03178010510700304450b6586809000344400d2000b0140c86c1261a004103603c261102d00f070313280c05550720398011200b40c5001d040c5010501648202040207084a031820001c40d03039100740020544000010b1010b40180f400f051401d05600f0f58841c40c2d5650030300b20301070900b0031a82c040c400854054400e54441e44040c2c010111501000c840444d072007a01807000c03c000324402c0000e842d6418a09441030110503ca407101d4541184400807041004041803c003e0550000c4610030f800c0040b6003000d000c144c2c1840340107010b42c00d080b8050300c1002d5465810311031540c45980040c46614000d481000803c0c070b5801d03c80c00901d441102142e0f803404000b444007072550f910405008507 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 299521681 1250 299520431 299520451
    0xc1805010e03070306050f090d02010506090a021b0703080c120310060f020304210201030b03010212160c29010b040b04030807140609060604180b0112020321040906050405 75
    0x60500005440100c0d0840c6215007520448101100103211445500d018062076400750081e4541a81c1c0c01d0b10b0a031a0030040030869041034107205e4107803110010680c000285501c09a241d0304107000c18800d0710746022561031340e482180b42c000b080c07008070001810380c0303111402581c05c101c49540c80070f00148001d940d1a0103010400800304a101c0c495150002c80c03220b9441507034a03142c6da4071030100c040e4861003400d414200c0c000c13054a0456030036200324008031a055001b907040014000601c401120010020707001c40c1c000486034040103208000244200b50f00282e4805050107134019441682903c922007200e10000f10000302e0703659420010b4604443c19000d03c0d619103803c0d5070380d03036480750405802120b406108140c18440101c0a0145510441c01a001000300746440c03401c000a80e000408100b140c43d070381005400203d030b106034045040d2024140c241440c41c0310ba1021901c0c02c0d00c907a0340200181c8500096125080d070030001001182d0716000c0034404240c54200f04030032079105880803841 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 299522931 1250 299521681 299521727
    0xd060504061a0a0e010911040803040305070e010e0f270a080904050f010f09020d0204030c0305030a0306050411040b030c07141608120a0e01030b150a080c0c0309120115180c 76
    0x41001947c0045040103146043c2038101556042010b00e507411581040b1040d4000c8081409800c414505807030041c0040c4030303001c0840c102040c0c81043d4100c0908020030907400d092046040700b29815040c0700f003401910440788440c00728100010315400c004001d81c071541c14103000c00ca8490209211505a40c10785040303850341d0b031800c1003450003540045c0d10807010940070300c0000040741144080c3c1c8000c60091001d942e6032142800f0040c215244e64120900c16454010600511400325082d1401c0d00c1c2000d20f207555a07120790012075158016100000d20081e40600c071400d85000100e15500a01e00c0c01c09600e410030b446017942600c07407480c0318281030b40c0c03034045c06680d00e101c3c490b500070800130806043c0020303501c1040c0d0100d007c0d000242561955000e00107401c501c2c450740044001d504c11141e0f1022400c0010380c804180d00c0340700d289041c038800e4000c803c18074543d020070f42c00300a40c510401241510703541c5e190f440300101010b044400e44160701e0101d01c02038190054200141321503000c8401c0303130 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 299524181 1250 299522931 299522939
    0x1812120503070c12170a05070e04020a03060902040b0403030f11030304111207030501020301051201150509341b12122702101803020603060d060504061a0a0e01 70
    0x36907400041c03001040118050801c0080f40302d6544080c3c8450065994070014100c101109000d1a40605100140340c6002d041003042540304010368902c050840b00542d0b1204e07039542c102c01601c1d03e0303000701002c42d00c00100001d03060400c0300100700b124481e49800004500142d000d5030000340a00f1036100f550420070003d40014845840804003840040002d04609000c459240c540380d01508120341582d40003006000d00c3ca44100f820300c11404460003800031072440359030a03145880302e200e454000c19014004c45c9110440e1858030f10740c680801814504010a240d80c6030484400f1070724000811541d80790b034080482c44052144400f40c1284044031400c1c04690211800e10000301a4048142c1e61040049401ca10341140100c031901000088001c040c140100712401400c20031800c14045c804001c0e146803501e04c004402202e804450080c0c480e902d9038085152511003000c01450103140004000801c2842d038071061000d0740da1030407407503600d00305014400b40c0800c9000f40a152441580100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 299525431 1250 299524181 299524187
    0x10305100b22090e0a060b03030a0507061109130b04060611150403031d21040e0a020706020f0c0a0c05030d021018050a030f021002090a0303030c0905060406181212 72
    0x40301c00d2040324140e0b0540c0d80e10446001110842c50901d91281c00c00300316041440164015052691801c501840c64400100c0c3c010f400380c4140280104072907250090851041c01840581d0490f480c00f0748003a40f0010840e80e224024210314265a1003580340030740100b580c5101d09403060f6152400b200501c001c804240041d201d050005108804040e1607812a104c003101d10401036085025100c006d08885840350407482c8502100c580c004900041440704002840045507501d4001120b074a00503503462003410310202a10905125461940700015400c003c07020024130350400764015188140125120010543c580d035035143c0100060340000d04031941c05c17816902004400c6002a14828524003690307a060030106009000ea000c500301483c5080040d40601c83d40260140441c800c5203000660000260f00405c140006820150380c1c8034805003039030042002c0409450010a981e40f03ca6546c08001c6c1402d03007501611041003a40c41c0001402c10b52101203c440581c021164903014102c41400c07 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 299526681 1250 299525431 299525467
    0xd0e0109031104111303020901050d2604050618120703021e010c1502070b0a050112240e011505091b0f0d05340f03021305060d0605010305100b 63
    0x20f980300707a0300c2601c1903101e84100002e103a82500d40c034040c0d0f282c51440c010003215a8050340094010f80a00d0b4042000a140d8180340d00d158850903218110060b0380f4001c880103020307075000301b074100b1000075030351402c3c69000380303c04055942114155660300d80051a1910f5507a00d1000a4111481700c0b03c0f8078a050406018400c2c240c4185488c08400d0000c4d2100f10119620701da0000c00154001100c0082c01100d800b10b545c0014240030034001c951500d1400300503c07008a00151000e11040600c951402480041c11004c404000091104400044005000b0201e8840c00c4a15488083d4001620b08000d82024411441d08007040c201403c44440c100c0c6d680c0c82003410800d03411080000c2d01e00c4101c1403003054010300c20030b41500e5082c20644400307010f01d00c03610070f600f0a000b844070b07002090304c0e40038130300807456150385c07801503103c088035441805003c1181e009164450380c04a81c4803a00141a4454001c4940981c1c062100c1d8a40300804d00c40c4000314041e802420764100000d495102c8a0049 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 299527931 1250 299526681 299526713
    0x50411100c060209041e020c01060611150408091809070812041514071a01091e11040503070e040203010c0905060406051e070303020c0d0201060b1b07260d0e010903 72
    0x80460040048600b5040342041b15241c0c0c0c504a80c0403d0810240c46c09100d100c0190006003050080400c0d08011070703075100b0b800044500000c00850000e410042d262068480031003002c1c000501040c195035501d500700c0c0d400c171440141840341c0680024a080000745034480500011070701d511301414035071821011035228140000b4000072a203a8450300c4144002800d0742d500882000034089203000b4506032000043e8400118542410803080035201402404400381e031542000145158486e21380e0595070041e42c0c412030303043c0203c0d1000074205841f00d2200b846148201c00801c0200c0c40b1100507501807400d0301070300d41c1104061205000c0140180010b181d46130303058003503410700005521151074039889084110000780d008280070029080402000154003000c0c0028881c3c40d04000c02c2e042280039a5200d00044141307200c1014401209104480c050003000180c3e039045141c1380340804555855030030344080d504c10618811000c510034511207084c2d11050350b4a002240c51520380000740c102c1100 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 299529181 1250 299527931 299527939
    0x30902030c03030705030d230c070c080609010c0206060402130302010f02010905121c05061c020a0b040303021c170c03040503160c060306063608010906050411100c060209 75
    0x110720041d40d8208050328003607200c1c83c0159520f8495942c5501500c0c2c0007000e00009800b942ca50074480c003100e444199202901c600c0287d258281400c294074098480e91100c00c03640280c00501ca460541034000005280a0f5000c030384c2d03207403220014002207110f10650f4125507207444c5818001913105404a0b00002e81d07520001c10090070395218a03080500c1c82c00c10b0185400c00080000504041c0043ca002c1d00d000110b0030040c514211000c2024401c5030011800c013030a8601c2ca41085544045081003d4614003090344c0e25181c0f01e00d07029655000c103011340007103500002c4640158610403035450f601c40d035005604690703585800307185417420b8001910031141030109211484152010b0040100c40e036000c1d00d1072003c0c003441d2080280844049400c4401008985406400445108640d481c2e03010038249a0509601050300f0102400a0540118a40c0d5080406100a1000a41013580103500800404500003a40420010200400c94004020400d40d04818010a40710307400341c01c500d0340c060 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 299530431 1250 299529181 299529193
    0x2030703030f140c060402131406040b010504081002070b10030f060c090e091509030c070302060a03090c0306090203060f04032f070303030e0c04090213090302010204030b040b0403080903180103090203 88
    0x400784850760300013226440b40b50703004d00300f08001e52504410044441c14405820400c9006902ea5003070b4a4100415a600543e2070703c81002859100380300b1a0024070745401034403881c09154420720044d5025071000d0760056840c0c0c02041013038284e01ca588013140d501c41540352034903180d45d554902901c40c184006041c011203038000503402000300282441101c1e171401400155046030b202c201800c10240076980ca40d131080c40621a030300c500090380400e491301111710644070306d0703000411009000c41c007034014686807518100100b0040c00d40c21003500240b003102640c0490b81c80c1a29140e82480440e00035000079640441c0058550503c1c090010080d0383e03041030300607040d0254000f071401009600c01c50020b80d40350045d0003038070424050b2130b02d0b82c1c004960034007424080350000385240c1d400805030f404881d594008001014000d5040718001c60344626079951a16107402e0030010701604540c00d070045441000052014075008c8100c034001588141908154400c1c580118002c0608803030481c0c044c4501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 299531681 1250 299530431 299530457
    0x1a2d01030b06030711010c0e0a030b040501020d2405010e18060315090a020a0801060506041e050a0609143a02030105180d0e010507060509011d030910090302030703030f 74
    0x1642c020f61003441360f615620816000d03181060300b180d1350150350008110004642c203426586040000b0112504800c02410540780c131708002e8028414418105109850f00d0801e203600d54000503c49220345009044015103a0754400545042c009240c000d94020076902c0c4c0016100a007085003030300524094102d50450300038808038850700c801941d6803541e41d404071403541c0444c90111400000f5081b0b040091280701c0c036000114025004d213001390078529800c0940b815140b50b64078001c400030b19006220300385243d901d8030301400060103030140c4181c2d52583c3c0100007403030410300e08140c2c00078405005d00748c107042103c02440862443c500c2481160110a5101001d40e5003402210300400c4040201604511658010391500301a41c0c200c034203000408a205040740e03003160644a0161700300c40e000c203807540c4000780c0038010700c0c00e0030040068003103604564081c003c00101078110301c4010b41c2c160502d1040ea5005960b0f0400307a05c4002e52541c80f4140c2440000c0c0b02c2d0018075401402410046145211 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 299532931 1250 299531681 299531689
    0x14040c0b19031a0d0507050f220506010c0b1009050702030a080604110c031c060807030f0b1e13050105010603060f0b090a030b1812091c0201140406031a2d01030b 71
    0x3c00c52045d140d42d800f003081400302e441c02c151a013a10080466a00da54003603903144c40103014485c0003c04120f40d03944c10020b083c9074041c00c1c980d01416405203810405103004040d8003159082ca004020300b013483c01c000901002c0c00001116079101c195100d03246c19030340305010032014003420780440017000403d0001d0314034103904001500610041a11805001900c81c02c50b40848085500040e11035214000420120383c5003482d04d100a0b4101c0542c098554540c42c2c0c00e0350004d903080c180e0078506511410480b0108201000e845142e1042000744000c0e641c0341800c42c1903414a000310740312203410b050304000b52001400103102410024041074116a580d40380c5080d646c038210f9200340064240c1a200c000024103000d10007030a4804041c450802604070b010982c11044c1c100c1a1041c240641040000c7d68050170100d80510f441d5420941c0d181c0d1204801409031080c0c4069101d01e01e500780300d80146182c030441500c166401246140d1000c1940315020030b064011605542c1415920b090503000d0342c803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 299534181 1250 299532931 299532949
    0x1b09060902190e1003020d02041a13080105011d090f030309030c06061e040203060a08030c0106050103150501080712180b07170c031b0c0114040c0b19031a 68
    0x10050300c00580710440b0301104400415075441000c01c010408003101c142e95240c5036070740000000d85c9401a21400c401003020028451a0086244801c121680005202008000f07115920402d41040101c1c1c0d87c414801d8242c86080c0912400c0300b9915880d80c41d0246085292a40181070104545480d90403594403030959105030340c0503183c0c0d0400952802d02070380400c081c3e6005401a80c1004402180e0300306d11415860240e0414451038002011070362540e505032039032014108038402da80c1e54024004680d8020300c018401d8030702081c1400b04071b00c0580c22640341541245c00684580c03405944403d41202c03008200e001e01480141d896196103022232604140c020414490205049a410700d8100a070400c6280381440500a07111410031038140010800c1d44d402c445103015400941910400750241801032820a1111350702c0c010620a05200058025006600580d175800e446521031440e148140700c1e208002400f4080b0910034210f0354230941c01440000c00d0072401c0b8ac000c0d2074040004007200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 299535431 1250 299534181 299534189
    0xd03180b1003170903060a0b040b03060a0f060501020703170a020f0a0615170a0303180b0a090605060306130b07201b060c071a09090108030c060606040509041b0906 72
    0x91800414803c00425910741c03900610490007240c2404600d80c0080d65a590042940c188161189281c07100c5440310b4104054404008059426a00e45025120700030b24110748900c0c48542443c1d4002035075400403400405680c1c01503038002444141c520094829408259003500718402c104600c0400c038400d20204102c244180b0000c030f0b84070480c42a66080d086990420541c4031004031460104550001c1c5e2164020b0f0301d03007000306a07085040c50122600c1c800e1980070f4030603c0d009041216100b815803240740520300c1a5000c0065465900038150707a82d4003200c44107508806086250003003407494200503072201103490b00344140501400e1800184400d5040481241d00444814001107541d14902588201c20f032855400c1c2500e03e0301940d5610041d20030341000201c07085a90001442020031036203040e40107012101039594400c5126600da01641d4a103440e0b0040341c002c903056240c10404c41d401c0721001403001515803180d07200c04040030038548801440b0440d0050001700d018450062100034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 299536681 1250 299535431 299535451
    0x60f0607120c0606151704030210020a11060a020306010804061503021309140f12090a0801020406050d0f05010b0403030f201b03030310060521161107080d03180b 71
    0x4441e614006007502c12680080a03900170704c80d9142c20a541c802050707410310110901c8109552241c0c02c0903820405c03842c8054142500000314069465000b510b584522101c9008031034550341c035500001c00320b0000b69a00ca0002c0c2600002c00c01240c5150440c1202001198021034090341c0c030380c0000c031003e83c0350b40c14044140c0c954442c41c003803045559009a83d074130003d0140c4917500d2040402a2070300d858140348448010f000c0341441858941d414001d018000d003400866450740c941801030000d070491140202881c1c10180c3d01105103c0700d00500e4100c4416102050901d4155642603481c0c2d003c0312100020050341902c1d402100083c81d400c600501c0501c00500724000070451a80c00c0c05800c0d50030700f40664410001c0c001400000da05a40c100c0f402c900d4880c0c2c0b00e019414014281c0c554000c1c680c0e01c652104010b1000c012090b100184402646440b0724944048280d499925100076101d220302030b070440200611500c1c0203400c00054500d08541403107100c04140d41c0c090802e8402c2d950b003a12 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 299537931 1250 299536681 299536697
    0x29061005091309020f030a05120c120d050f100506040b0f160b070f030b0604030209040f0507060314011e0501050d090606170d021b061e1207140a08060f060712 70
    0x10b60174001484c041c07403801540078101c02c000603144c0035900e21003500c096040f004006090078180c00c0500162007004031018840b6030355150800803030050503007901ca2a4015000b0808034000d20721481080d400c81d50081d01e020f00741403070320106a242da00103600d4886045820880071130003401521001c0369003841115151307054200048010071640e908047d0b0300a151400b4070603400c0741e8840c4159022250304440321170003680c4501c0c003000345150b60741c0300600520070041c02080302c0b50590003400665034141d050811680c0c2c2c0700f55210480102000354001003406200600c8254410801400d02c8400400c020070600703c5a034903082211001d82c00114009409040b001c841c820510507281c0204440c0f0082c0189100b402e00c407540800b0a94446200d094000740b0485040e01c50240c21009140051807544c4562030003024429011003103487c00e00003004000b00f0001078041c4e0f426500d02a080f80d980e0180c503078440050203881c80800303420550013141408605e0019400740000302124945079100e0380 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 299539181 1250 299537931 299537933
    0x30d031505040204060c0f05010b120a05190317101a0d05010e011503200408060f0f33030303090304091503020612180f070329061005091309 62
    0x640c912690704028881d500401080004c907070702041114101da04880400012403c0307281407801001d90160442d0410841000f80b8000b0714085a042d07240c80c000d8003034881d81103000c243c21000d444c00010040100e011009900c0b46525043d1810798800340042c1c0c4035523280c0e02ea50500f035400d0038038050154401000103408688091074000c040c0107200c003074080003165041001c0c0c5002002640c220004050356121165010030255111181c071002d0162041d650300d8031040b080c1d489078400c1f1000c00c07008241c0c101083c00381c40c81c004050f22441e034203890104a42c40068100f8014207001680203c100300940f000351082c0d8040c00110301034582e0f10019a070380c624016108003907410204100455844c030020030405070710340404442d060407111840403e581d40b000500070301c4460024165807513101c4d4080c13070350b4140800214403043e0703400798904a0701012480152080c16a01d00c00e00752810301d00d90302107400c82c10041c6098101d100c540c01d01905202d0040c000c40d08900400c014001d186458901030741c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 299540431 1250 299539181 299539211
    0xe0120011104180f020a0c021c02041a041406090a1e1505120c01020a0201030b1908031e03130f08070602030a0204180c02070e090304051225150807030605030d03 71
    0x40c808800302c113003541025694000542410b09007800071f401345001c04c041c8840e14076103204803141d95a00400800068000320401c11720306100d40c0c1c803d8000e51420015600301b00a0b4681d8911a41c1d00421a0352165a01440e000c0607200448009100c4c2e6a4022400b10401660280d2003036120400420410a40f0704020800c10960403003001481340c011b00030307120090741d0203e41446029020b090100ba0403110740d000c0b66032189075210313600304544010004126000e0100007401d01803048001102d14281d00d003070f008110b1000390f410403c2c0c0e140c50618040040d44c0c600010031401e0240c048203003046603540b1807405070781c003c69003003a80550000b000c0c0a20302c040718441c0784601910b203040000c00117141e00a550f4580f82d0081c0c80701400c0302000510b0146c000c10849001e0400500620050403204108990343d0b060402e0729215004440600d80340404142041c2046031032002e42000c0c02c5103030403000d41d00801301400c00410552a210003140c551020400400c005110340e4000812000b04003003e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 299541681 1250 299540431 299540441
    0xc010213050d0c09050c1903050103061d0703020904060912080106082d0a0f090c03150b0102190614090a120306060c02011202071a01080d0e012001110418 68
    0x1d60302c51485003007480c000c1024050181d00b501c4240000199540b190402c040176800340c4d288054500030140503403a140c0d0303456000a4101c911414090041414401c3c41101c003500400e5510737216030201400704054503000071210342103130044900180c400e2923030711b0742000002c0c0d20380d010003c0303508140100030a55105028a5120501c902d5254a41d022000741c3c1c2055859100210045c024803004901030141e1a446a401d0340c0000108100503840b9240c1504046064030083e0748510249074a0b0102400d40e000f000100c007016406000341c01c0c414031404400762005a0107850b41541c481c5c08105180c80c007190703240074145900c000e040ea00342915002c401208841d901c6002c02d03060840422200d034100c0b04140c0040d034242424164220039010000c024064510080c1c405818450042c004040034072540b8182d886100982e5860001050252040c1e00b00000f101c0c0041d030b15624408410000c1000b010041001034004141102c1400d000031311a0003a411805c0c40b0100d50812907180c1c1480e110b1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 299542931 1250 299541681 299541689
    0x507090510060c170c010f2a080a091203060e070f0e010f140310060906080103020a0302120115060e010e0307050d0326010303090306050c1303080903070b0c010213 72
    0x6212a15099900354152000c0c2c1c8210018441d030070740c026080180c14a240081e01104c0c0f07402d10380b50420b40034050b01904505106c18001031034400e0400090250882402552000040001018114013411150408020048031440740d9800e0a0000561212554414042560740c0401c40c5420f0000e908a40d410290a12041c050515120701307070160024000d04100d5424201030301c0c6da440064068882000c0c0d041d440c03280c44030000401201c04128007010301a1842a650801e11548034034040c3c1790164280406944002d110400704014644601d61a103040841c03400132071000c0d0305800b00a000c0002d03400c01400b1414984034030081d540d1112002c004140d0450041824070b18150106220b0126441c2c05010041c3c02e1030380400341031884009400200e1050031101c170035a03507402e008040515078041160158208404611035100550035100208285201656031900e50f948903816a48074801850f054050f100c0002861581c0038042c00c2481e419400140e6112800c0041054050403500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 299544181 1250 299542931 299542949
    0x106030b060a0909051b010e06070f050601080f030301090b06160b1816090507030b09070e03010c030209090a1505040204030b040b010801060602030f09030a12051207052d0d090507030507 82
    0x2c2031010031400031761101b910140c0b403001c1e00400c40c00300041f02c00442505180341c2000c2d0000d035007410003a10240c1440007500a0781030b9101a45c0ba848020348a42d01c0c0400d60075181d10038001400100d1850740010000035004004520f03110003909103561103003c42c002a01c0d400d04d230000304030322420541c20a0f849040084081c0804600c54055084003804a000d54264181c2d60300c0050015030203540b0039000003e0013000c0103910b10340b9003001010050b2541009000f542440d118035113450003030094555403100284100d00681d1021305032801400440e0b03c2c0c907002c02e1980c0c030005068039248020409940190480c031414506410500302c0c070041a4400d82c4540e01d0034104000940d4040b0648407202585140740c2d40c0e400800000919203110711a01900c902000d002c2c000445400c003006040111040540310140e071348880c001e07141c0b4000c0b04074038061301d806031988900b6843c40405001784030709204103080c00d21480841e10002c44072609012500795008180034011301c50104000001000024 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 299545431 1250 299544181 299544191
    0x31410051e06061908040602040914150907090b09180c07050c1203030105010503090c04020d09060f0903050406050c12031509010e0c090609030307060906060f0509040f031407050106030b060a09 85
    0x2c4c0010480340110329441040100b002d0100d003c202d503d404883c0104090442440080300c8450110782400040d41d209412980d54017a10484e4101084250310580039515816082490495020f0150b40304401c00303940408998217000204c0307403c1c070b602c2d0b000341e0170342d400c40e500c544040c508a4605a19030095a02c81c0d1140e110f1103c0c1c03c440041101d055400078603100f0340302e89039207144078035000400f0000b561190001c59010600c0b5030f69404060f015000e030302c013070040340d501c4102501140c40018010740000d100308000d0102501074401041008980e9003160310714504606c00880c0e42c1c100b9508051250705100e8000c4080c40c00c20821809021100c482042c6428030444180d054400c01c4255070094601060320741c1942e50500a8940c1290010b10501c03403000b030382c5481c4006103c140100c2d50148240e08000c140d46c01c00b081524816035010490070040c0c041602c082c0c0304403c0e02e08616101c244104110f10005c0d9081c09240f0080d88101401c00f050300300304c41001006440e41d003103040b10394a04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 299546681 1250 299545431 299545447
    0x207061b05190201050705060f040606050d0b0403033803211c020415030609050a0e10200d0204081903050a120b0a120b01060e0307031410051e0606 65
    0x115500020203404402690b40602a20040e12280115000540b090190100b00803084da0031540180c800e5204038000c12045848034208070300c1c601d4840015203c2c0b902c00c000100082e0090388280d070112070440c0343d244481c4a001d030501c224130104510124402e20b40c0c402c4140d42c00e0400015040720703041da032803811700068240800018001d2454408070448010316038502c440f50395048601521408031001560348448001030b01070311440c130074250b10301c0ca81000264103140c28428031a29008a801800205d01081070040107030480b0441c0034480300c8820644080040e000d8010110300ca00752402585603807030030272141d040c1441013403419805105120142c0010707500204039001f00b540f5041072004460b058a03000024240402003c0c0c000e859804003046000f40350311046649031064007026410f80e2030f20b208841c600e500b900c0c0103405d50302958042c40021503180241c03400d8040403048a102c2c0b403407601c1030010b44e1000d0f03c1c04030901410b08145419892180d11751391f40200300356196458203543c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 299547931 1250 299546681 299546683
    0x120307061a0a051e01090e070e010f0e0d0326010608160305040201080a020304060b030105150316050f060a0203070204110304140c06031f0306090819170103200a060207061b05 77
    0x94106018401d0010b078401800c10380c001e8507a64047c20440210240c0e80c42c0448014201044038000d041c003003480c2600c03008141d40b00d031061003220768014105000a0b0310340d035002e58145900001d003440141c0044565a151440d8902260080c895a503603280c06080c094a10f2034480c05485001080500382410400580d8010707032803035081100c3c0d9500507035135540e6040c400020034603842d00c2c640c1075080c82d0503ca03e10030361201c0f248201000718180d9075200d01c1c002810203076059501c10751b600034190107582421803401c200170b04030b01c005c00d0066a1074041190b00240407510760021101c1a0207002c030910051050300c09500c68202020002401404280340000301540801050700301c04d01244e81c011010720216003150001541e0001040c0040100c03880c0c0103c2c942c22001c403442804c4500c40d00314039075a10442c040c0d070030003030300e011001556401c0d43c9412a613400c1150544601020400e0144180e450b03103000140248401e41c0a0280360b41404402444200d42c1ca00701c03801000c1c215807040110380 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 299549181 1250 299547931 299547949
    0xd03080f09060105030a02060d09060c0e03070801051b0703020a0503070602030f0604181b08071511061515090d0b01060f03140105040b150304080a0f140315120307061a0a05 76
    0x2804484a944070321449e001d4030050704035494010b100d130381010011b00000b40c1116004010741012420390396090384602030075080310412603550340200bc00c0407100d809421101c1c01410300e6802441590610002038a4403803655000d24800c0364050341c000b040180c05651070850350b4000408603418401004110740c040220303c2403004c050030810345048a84111151a58800d000741107503030940341da036a43c1d10b2040c030b8202c40f8040190041030030010b0510b410580072912074400c1ca910a1108541501c60040c005849909130000d0412001000206040c1e946c1d103c128088034454110005250f0600c0030080a95001c240c500f403d2500302031040c000440e103160340c241507400c181e0340000c0700c41812001030548801c1d260074030903260000040c081030114a1009152400064960140031028900222101480218405898882400842c039000d00900d1000000c42000341400c01d80c5030300c0c0b000c00781181c2c02001c0403541c2c55a504903c005107104460002c80d41803040b6418a403081c502808a98840 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 299550431 1250 299549181 299549183
    0x90608041101120213060503090106060903350d0c020f0c1e130c1e050a080f07022505040f051005091801090b060108130507060c03020c0d03080f09060105030a 70
    0x7281e0f0350b48241c50114142d041d100719000900c1e000980079540d1030041d2190b44140c0d95100c26508100b40458624045c4007044100d80d13011701d07200e4140340310085216241c1e030b03161407000903d002514120103440c0d50310003414008101460000781c003000008040d16255607440010b080350000c0c060728000395110800030118484420b610340c0f07060003180010740035524004201d040b8030315200c074008489034448006250030800260703404440291070026900c6015000c5d84070006200400029a1001d04821445d080406c80c0125105600c01502480050091510000b840c0c1c14248041100340b03001c1c040c24803450740c1c0d0881000356041c80b00311200e0a8820340640d601035040e02012030300c20308901007004070305041140204080c00503890114101d40c0c2c00c2e80d81a0004036502c022510340c10342c038030166034071a0340b001c0140070351031404c00d0980d002100390703000358194051100300c00170a844941e825001c062283d628803c0c0c0d4501851807010b031080107409891180e00c240010704c42600e000801011035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 299551681 1250 299550431 299550437
    0xf060109020f1905030402100c0807030c110a08030309070b0c15043305090309011d06090604030602040f0803070b0a1e1d010c1d0d080c03031303090608041101 70
    0x40440c5040001684643c80403e1007541411580d070107025440b10146005620031254204071880c80c50007118110503c890103408218200f010340b001078020655913203020322580c090002d400ca581c0025031030040c5540f103007801d0303000041007008207042403048002070210f40c200c2c81c0c03c103082503560030b989195503943c01040030040b901060501054141030a1100d00d104503504010310f2221340480c420362140000005581090080b801c0a400441034900c041c0047e5a0014100498100c95101203a0450031940041d401c000961907501c850b0020005903018110150351741c0d140c12020307951f0f0f800d07a5000171019041402007400150b40324020a80051062001158888810b002c0380104001d10441d0548a4640008032200c421800e00305041413041400030010042600c41c1590980c0d0b21144c00c51141c4a114429440303032920170380c05101d99001d005018240030301c010346030f403542d402902e0140e584a2282c181c0f50800d03034842c10360030190000d450300c01a1800c040e40c0c0d18810008401116041c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 299552931 1250 299551681 299551687
    0xd020c100e12030705060601091d040204020d020a201617030f040303020c0102070e01180203091501230a0f0623031e1302091605040f0e0105120f06010902 68
    0xc0034400c0300429104070004010a2a0300410a2030301c3d5280d1000b402255103008601c0020788032341c040d0038044c0031240d801c240c001c507500a5141d81d4051341402001244d000b0313420300122446500074406003038840c1c403a48503c0001c010484c24045000c101e44c3d90f00d4010b0b032010442099001d05602c101c811280141c1c20f010304003210900312403d50003400c0700b04100000104000003031650014103054520000e07001d6803007141e258100024491024051032580c26802221040100555402036600045100c299252064507003078041e1460b01c01ea2001d09000c1c0b122641c0581040174500404013004112809032403070349000190500f0f03904a21600c000d0007884600580801c1e0502c2e002007019820128681c2c1d00e240c14440c80300d100108074000e4440d072034020001031245d04500d1076124440d400800d0440261303241d04180400c5070304041c000082181c00c0c0000a10200c4840041003e00241d0b01c1da000ba56042205004103d0b85403100d07402c41d540800501d000f405800300309141950000c1d040965 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 299554181 1250 299552931 299552959
    0xa0305030a140a1a040614060901030f02030a0212091501050d02030a1416080304082503061a0f06091809150117010605030604030f030b15070f060605030d020c 70
    0x100a00800550310448a0300508001003c92541d11180960f0701913200c0880f0501d482c8140012a0b425008821003001d90504013843d62a04074040c05103510145070109205000c84070030001e0780c0042c0d540004094000c2185101600c6400c00c2e56404400301d0010b020b01180c0103481030131f0181c10f02c606800350055802200c02d648007404401056074000248001011194040c1607407202c1c071000003d240d21034014046000040401140c1c21103280302c005240d0035002c2c4080344a182600201c050324030041080000c0042d030240140180e01c2d000c01c2ea90300c1c007100c005047c0410b0050f0442c0007841102c0c10400d0301850341e20700c441510903481d011030b0034003181c2d00c1100241c60103904440012601d450700c07000007a0440c0340307400b1004134541c01d0000c0c44050750301c1c0e0900d80e80d11801c0c0c5000740811509199426000d1090340250f50004006040008120204000307100341e600a50055a00e1910801000140601030054100503c4140c0080c806a80000402034407040e281c00410311803a002e8109035 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 299555431 1250 299554181 299554201
    0xc0302060f12130506071445040513020d330506030d0f1b0c0f080c0a05030706050904090f06050112171305060714060705090306010509090a030503 65
    0x30712071120040e60010314142041c040f50700020f41c10003200c00f0f1089000041e03035507101c2c0c145050b0f441c0c05030b01c9183c00c000202045200c2e8006c001d66030701c412121418407d00c3e80030020382e02c803048480881490328150703e510038031094410050001c4545034000c4400300050f21008180081c0c10303086144001c01a0001c425101d9048000300080f40418100503550103001c040c0d8481d60107000308030111031b16965444400d840c03010041d140b9a000c12005a011004105040314080303202e403154840741502616030291a07082960b903003040c0c8203544035444120a90070150f070403a01070003084000b0726a49142080c024038600c5036004e520f015603241c1d11000300300314200780c09503501a8803034000d220b0743d0f844000c07005001c1d14443c81500c0d20500020401100e00c0a08101c1d410312900040034a19035090109002440c3d0010720110ba96400e0701c50008041c160034000e807401024181d0300d075941c803140d440405180c02d6060700b02c01d01c00c503002802d2000c07422001a107101c010b513060074000e440c0d6903503800c0c103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 299556681 1250 299555431 299555437
    0x8060604090903141c050109090302071505090d03030c030c09030b06040f0e060412120504020901030b07022505030709060b040504090804090f0b01030c02010e060406050a020f040906090e0a0c0302060f 88
    0x1014072400f0105e5420b1000031480034074041c402020700d007004641ea80f1094101500d0385024080c2c00743c0c00104e0140409008014281d05414013414882d1600420f51f0105035030f40b0528034141e00090782c420301c1c1c041c0c2d540d15010310030340602e403440c0014000d0b0443e20780707002c41c0d0401b03090f681c46195204480000c0b49040d0304410000c1040e081138541034606410301380040a540d6a0350000a0b0051504885020041c0306a602840d00a418211140c1c210741d1195480d001c080d0440741584103003103241c070307614030700c1800d80c050349454032040c81416141c1002d2600c1e0000e81e030890003d071070520a0511036019280b09540071901c2c2210003141201140c141514148256080084540e042c030040c128040d4a64004906048080c1c3c1c0400c08001055800c901300c0d24080310420045d0020004640454010b810080c0c03c208103000040c0781500b415580c1195610640c044440c0d142c8440c8208268100c41c4500607107130100740d01421280b45150f8418801c070101e0701000344284c001044445180c2d55540c15 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 299557931 1250 299556681 299556707
    0x100f0f0516200901060912080d02090301020304050a020f100e04150b3001030807020405040c15090f1e03080706020f03150f0604080a0f02030f06100e0708060604090903 74
    0x60501940d559000d00c09140a4600000c1c080c41c02500000b543c148205078050482e1f0240b000d50b082c15003a9900c034501075104404841d0344135001e00c4509201c1c0d038203100841c00340c1e110354020401071445105002058030b41c000c9041c0309e21500520070410035080b1488419009007120005140301105c10014404601034000340c10591000c01c0700c148a10740319401210030701c500360b070700b10201342c0c080100c401c500000d00000b800170300e0601000005040070b801c8076400c1485104981e103440d456049141100c100f01d0490070000c1c0300b1040400515506403012406441c501018a030703c01591080341e0900351092000070203e541c00a84038007800004d40c15110021b420206071990303801c2c0090b0360040c01a00010040c45050001682450fa181c282c0c22202103c01607005010440d02e9921243c0e14001d059200703a8044c0102c00040c0d40e108014004140304180445010403104d080900030030140c10020010002d000c1d40310b00740001aaa51815101292111000403e0001080c43d00311140844040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 299559181 1250 299557931 299557943
    0x60e0d12080906010503011a04020a1e020a02010e04090308040b04051204090204150c0201022a040f051e0103020108060d051912030c0203120f1305030c030405100f0f0516 75
    0x1040e40400d0781d2080c0e000380200c011104444499880d039003014201c0ba08048041c3c82608640ca40c82502c1c10141c02524082e0040c2c2005030b00d00410745621380203100841112030058104800b82e104568010054181e440400d40342082006040d81d000b40001c032000d000644613198500c0050200241006600100400482c1140d200c1d941c40c54240040e420a001d0140404d1031800d03100307202d0f4031410b0706171051601603000f0040b002d20603241100ca0b016040800c0c1c040e003008648605075484500441031007040c2e400e00080d440c0340c400f00540c130f10501c0c0e07030741d92044c04d81c2e4100400c0540e902c0030390141c12040403686502e07070100070301d030003817426000744000515a012049400180701c2d124000a84050031a01c0c248101000f0200807130b120b1286e5070408010007026008199404500b00c0b00c40e501c96280c2e10380280b00e00d00b64480320300d9034000349200141ca134400030f0244003d00341002d406a61104500b84819041c0f1040c40240c1210501041c4104100f800710b2600318106038010154150b54002c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 299560431 1250 299559181 299559203
    0x1207051606021b060309070612020708040b0301090b0d030203040b090105040503160e330111070306090c091b0e0f1306080706021212060307171b19060e0d 68
    0x1c040691030b510480c1120342c8803400080b80520720b082a00071a803181d5030200103407030030f141002000d40c1d5040702d80c50720104140e800d0041ea4000f520941c0104080c05c828100140c680d171501c1c0050701600c10002c801806a160805414000b07a000410b580c1944c4480c5041ca468100000048a4500a0341d01c080d07854410031000606940742d00401c4016143c68000c0740b000380da24550440682505804d403900200311a003000000b00d03c4014a403200e900051601030188a07050130605d207371841c0b80d001607400c43e603100700080400410381c0007030b001840413607000d003c818155907040c12031031080340e1660244030380c2680036440750341d1740500004904030041c00910030300c61044c02d2000034005030040e140c00d0b01c54400041101400005c40301540003405110301d150a00c80e09840c00740b61006001150148554030380440c4600001c081440030070014070040c10b42c400700c2541007125a11580c03030140111103484a6070a510420038000f0151400c038101034481c02031500205912144280c40505000356003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 299561681 1250 299560431 299560439
    0x2041401060309060c05040f05060c03040e0f0a0b0109150305100306050c070c0503060108060c0d060e01180c090e0a0b030708010c050a0906170f0601020a0c030c0501020d05040812070516 82
    0xd030f0710001081d800741c04d040180c0ba0204009a0300ca100b03902a44030080c20341d01c0308020b903140483c0100f1443d403040042d01c0c00c2c00c3c1e40e800c8803403104c00191f41c00074072a0890f10400c121081d90340f0450308016400d1034a500c0c050300e07021004070500c13020012102055142c60008031403444481004006550001c8100580d14284004600e01e81011008079001c000503900042e440c80c0000303960341070390056406416a0386401c0f45c0728465500c4100010b01e41500c408001403484045002c060003032102140048849404ea100780b0f084a94119001c4140444610b041c42295920500d890b880400c18200050040b210400285070006030741c4286601d600b42030b400700c86554040058000c04405813107984a030b6031200d40943c2e19445003407145000903070100004000e0340d2104609900700c003040c01902c503038070446c0d2155010800039401c2980ca042104c84100060359040028060030390f00307490214240707814030315896294404520407148041c4003051003010703c441445014460610180e50303a66032965 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 299562931 1250 299561681 299561687
    0x90309090c1c020717160c030c09050106021903030b13090c14033c0d020f0606040e0a060207020105040b040e0108011a032a0d050309030f0a080f070204140106 70
    0x2240c24103200c842d0203900480e0a101c03070390007900c00450b402408500c0c80002c0043d540d05941043d0100d40203044c06c42e0616022803501c0780d451020794041d80d280f002a80c03e2a00c0441900c0301a8031810841d4400f0710485001091100d1396801142d00d07250210309055101c002a89030000341e41c00021652400440c0010411400e5402040751001c0000b00e40c280c601c9000c054482c240140407200c00e2136807003259240980407c0402c00030040c0d00307014249452500c41028500300c407400c0701001690115404280c500d40c108020b0f944200c0844060000d800180c40c450340f02c0700003040041c1240d802040d60b01c11a80140c00f0b6030b000e01421300e9001d07160f55403000d5905c4610070a00c00c411195103860004200b0700100070b4000041100900105a264102c04181c4030191501416503a901c4c4002251481941c441000711500ca008078011038485101408240c1040307084500c000555004040d00740000b07803541309a031740c9007d0742c81c0742c141c03218040d00120300a8100c10300090008420b10b000410300e250 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 299564181 1250 299562931 299562937
    0x2150609190219030902100320030c1201090b030106080606031f020409020f0409140c040e250509090114091603090203011104061d06270307030303090b0f04080306040203090309090c 80
    0x1c02242d84000c98541300c1d40a40869448018050000b86002c0c200d4a03455127200044d50001d5100500038900340d520a40400340100a03001400d44a07242c90800c03002c0e24090281d03402801e500005480300f4241180003030b0361442030b80008000e50007116078030407030410309605039030040105202c20355543c5010180c5c0d04056000e4000c10440320b24141000c0c030242507000c2c00758403c0001011a42c9040d0501312049501c2030010218956030074180400f031920752584080341030326142c86e20380a4a4201c040208002e848058000c081400c1d00303094890f0b06956141105900641441680b49203580789080031006004101d00c00ba416600340011109054540c07030040c07003160304580d0b8000d45111004921090320641c1400e495110009025800340d00020000f44207684405080f0807280680e82804241030403483c1d40b0590109a030340a002c7d086c09034020004c1da000c6241015410507182070380d10300b4528003005d07244034005ca5011000441c4c3d04000c20032a10070450040041c101403030450b41c0c15510703034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 299565431 1250 299564181 299564183
    0x902040c0f0f020c0109030f15060f090b0306040b180f15041709100e030c0409060504030806011106010317070605091609020a0e1309020d0b07021506091902190309 72
    0x12080076400b1592440411811824a8165141000350303286840d140089442020b003503502e84200c60500b00d04452034400c0900034005c42504072000d0789002c003400d0031103a0f00c0c0f0741d240c002e400c4030f02080001009074040e02d910000710030600148104c1884142e1a2406c036081040c007a201c2d141c00c80c40b01148102c5003502c17503407180b5005203000c021680141d1746401042d44050300000d0f8030214850003805015001d201510203007c8030000380f55480024152016881d0a442e1030756a0001d001c00d06a002c0d1031240e00901c207082000c559100742080d10756505052001400f501280c1c141d2042e46940c810071103040e940c0060060005050a4031300980300d000400301007642c2e000c0300c94005040d003024001d4803247c1400381c490b40d501d00d549209001d40840300503034250305540e07200e08810050b40d8a00d280483c041c06150100c0f003920f441c55000e89042c0351554038140c4504007100700b0990750f640500e038641c00380201c6c20485510f00c0c540007041c06409000042d840b80c0c5140d41e200d030a07160f4154026603440b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 299566681 1250 299565431 299565437
    0x60806061b100219030e060f0403050c0d0302071506051c050a0b1503010c0e420703020c0901030206030402010f02010b10030902180106052203060f02030a05090105090c12010902040c0f 81
    0x744414000603402c0315111003080000350030400c00248c4044515043c141d0290013410000c0c9410010b444007401c0c16466481d0320042507000c240c4805102c5403407003e4009200c030040400c40d440c10500088d010003a2038000c400c076054003602d82c1040144c01d0114042440d88281c10a1250600b411003400f4103a450000500030340c604107150310003920480c042400e000e4040e290005964603035109500c440102d1014120100c0c003200350780b5540407000c10a4a40d0145000103d0700e521003454000d00f4214001c2c1164810032010f0014409641e5240850b074210f54242041030214400c04400c1e40513050500741e46900900e903044643c41130b505a040401118400c448101012010034200c1c44018420301400c00040e0082c4502c3da02d010240241444c0d521054444045550b034a81d92a01903820043c0c8172818144c000c002e21088070707003034000c5030b411496a200074040c40c94094801a0f8a1140b0070400b803103020001410341e001c442c00e520000310b26070060424840b2a10002015240d502402802000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 299567931 1250 299566681 299566717
    0x3191416051c0809061803030310030c0e0c120a180507060f05031306090f0501020310090615140904060819020f030a030e0105030601200f16060806061b1002 69
    0x1000305284210a000b6a1040c50241007507840814000f098120102a02d81d0790f1903040c64018aa03801c101452060159001040c2c0890451512510803507050707001054005140050010703000350304003030358072607000e2a01200c3c0c0740d81d4120241026205a480c4680c0d50b8016000c0b85041c46004181d181c280c4106880303c8100c00c0076400200c905100032150303c6d640b0141c80b0b0b100340000d045138100021a50007503007010000c0e0400d859107400c9a02c02c0d80e440e030366240300450070446504980280401801c440e050303c10940c0c56804040c1110b06052a0041d038400300103900c89a81c1c2d00c980c0400050014401100e02c0429000615415600c044509a2003030700002d90344401c5207000101e5041880d851703030700d056844840000540340b540003d0300380f40c180300441d4040780fa50750080c0720400c0394149500040c01182ca03415040b9041c040600c0281429182c171000520005401816040c0c000c10240c0d082e45e540c0c10010340f882400c0d900d00b4014800e5002d6842e98a08a0101e1780180042030411400140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 299569181 1250 299567931 299567959
    0xc01141303050301030b0414150402010f0807120b01110a08070611130902030a090b040b060a050103050c160c0f030c091505100302090103060f06090905010f050319141605 75
    0x3036098000c40c000700041e004200500c0080d403048009030b0050310885640b210740e440000380b0f6040020900d00031400b91103204c104000d40d03a00100e060148642402d0002d55401c141ca0020705490380d80007250b84580c0c40340c0308070889902c0380716100b0701ca07425103041c1c0303024207410b160500265004100549400e4109100807401c1d08110b02224500c1c60100307100c08209242202a9020790401000510100d95410b403020104c0d41045c0c082d48614454140b10002e8070304041000a035080b182c00090405151100f0022600511030894416202e6600d01200240b01442c0c108a88803442d0001c0030300c4100c024000041000d00c903040c01c20b540c201c0b6401d00c900d5180d48580c0724a4900ac0c403c0b10b92219000541c0315296009034010a14207078185404252180c0714910f200580c90254800c00010b102c00f441040905000e102d1a03024000b015006503000c0d14001c00a03650380521310000c000504480d0040b0100140000d03903401a100d11003c0c0d54081102469003407505a051158502414001003500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 299570431 1250 299569181 299569201
    0x1209010506010917190b061c110411040305070e01051309030509090411040501080303010501020c0301020c0703030e0d1a04120c020112020c070902030103051c080c030613110c0114 79
    0x41d11446041c3d60b903a84103864501c4c00c405098a00c0c010940038004c50905c000c54001940e254407510780907680a42650070101c09002107424000c01d810541c0208a21a03000510b10300709070800c5000032940030611402c40e40703002c0e00d0380c0305a0340300520a100c0d82d040012051014408141200c0d011101202c00c5404881010203441014000a0000d4410803d03d0281c1c9042d000c0c0c180c0080c0654000000b510221010604642003030700710051643c8040010000341da4104040480c14805900950030020420340301f03669415580801024440056140c40030740c0c44801028500e2500030f102254840311820380b29541490070340d01070383ca64000600d003058281c000c01e1001501c0f42c0c180c0d1603c94298210b802e0500a404c41590b5090500412a00240445003400690f000e140a6009001c00405528040f441030007075619031400c0c4040c40007002032564a59003503952140059800801c00b100c1d0300c090070003d14540f0b07130443c9942030100e0503000d1030381c0542c899a03c07000d80e5172841040c2c0d20388100c0c1c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 299571681 1250 299570431 299570441
    0x504060b030d2c10020105090601140f0d020102160f030b0105120d03150825120b0c0309030904051e010e0c0703030e01020903010203310f0201030506030a0c0902120901 74
    0x510045124140c542550382456030f0022070011904120070350061500c0b0009941104800b02c032401030303455a062060625050140500420300d094012a081c81c16002044118510701006845200d060400f102564028050382d540081055007100c6215112480150a0348681c00241c690140c3d0000108241c2040b000c851071546c0102c00070070038441e492400f2400f80c110541c040303401c08a11407000542c10010045490140902120301c4081542c2e0760300044040c85503030001c20101d0a020b40403010034a0440450707000300510154581d280da52805451851180010340c2c0d07049440c007410480d10303140396030083ca16030400706100d403440c1c1d0781ca00c044480040c0c107642c0e9881420302007001200003802035001d05240021300c400035040180b03030400a422604211030002c10003a00c0fa452103d500784070480b03460501d070000b40e44030042c541a2140d2000b001c0c444402410705994601007a0207030740401c4408052944240c0b88003041d9194902c09000e5000301011404a8507502d0218110100601030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 299572931 1250 299571681 299571703
    0x803010803030412031e090c03121215030314070c0e070c05010b010305060f1011010e060601120e0d05030405150412030f1413170408010c080a050402010c110406180504060b03 77
    0x50180704005d100b600d5130061051f608200c80c07074000d107040080002d90412807100050219200c1c4200f20320b101e001e8005461486040e5400300840300341c1031000940000f440500103640e06415910766140e8a021071903090207400c041c507469101010010700035030000803210701c140324400074405195008010b40950302e0994066902880c8221940c00c01c0c01d082d10315955161041c64003a80c804484c0708460301b1158482c0c0c2544c05c0d0340042c01040046d581042041c40d0000e00d001c02003100e0200848016160032403144403070200900000460b00b88102041301c0d0910790b981d24241142800c0924095101540c120081c0000c80c0c02c0c503c0310590344c940e40c440c01040ba1903003600091070b943c0d0107040121000850200b01c0341d40b0502d00700650a21701460151018100d484000a014988000003030002c0400404a85d4142d0400d010040141d90062850402d194007550302c444032440d100000f0040c203000d030000f00c40c0301c5d54114008882d407003c0d003000d0f00840c000c0d002084540500800e054880340c4000c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 299574181 1250 299572931 299572961
    0x10b040c05090f10050702040510080c18060f0a031a0417040e0f0c070b0403170a02040b0a210207030806040515090403260702010203040c0819060b030307080301080303041203 77
    0x10740e0f08031418510700042e1600c0c0d903171402d6480c0c80701c2a80000d088550075940034010402d40b40c003d2240c80010003102c4007400c82210003424105c1c84804000c00c1503401000c540c011100101e002400e43c0790344007118041c541c04020716600b0b0050f0311901441c0c0d04e085406980f6160700a1064021000c0101100c05841d0501c2d41414582d813102c51002d40142d000d0150610031750704103e10f40c04104030060b2540518442d54030072254040400c0c07440d11130358003d090390205510402c81000500c00d0401200d585010301c0c20540e1290030460704184111424100c050405800025070a04240e40514503d10030300d8101c5042025460f101c00003601d03c400001d0141e0400030071004280440c1c024011256030b0b00c1113081071241c1c080c080304012409801540c00b000980e4010040c4402c03c089444c410002d0320141c00244150402c0805000201c1c01f05103024020a5440c6051140ca44084c821202441c0d0001585541e07035030340c2c9040039900d030310845e425109007203c0b01407040350314800e0040c01101400c034a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 299575431 1250 299574181 299574199
    0x5090607080906040302041104181505010c0507081b120a0b040f0503070611120615030720071508090d0e090613090b1005030f0706270305010b040c0509 67
    0x981c4900465001200060b4009810f000000050b40c4502903121300d009921026030310f030707403400d41e4070100c00140708404440d060401448001c203200f85030940e41100d0091078401240075103070411908044039038100361810b0042c4000f000c1d8500001e1416003040d0700990b550805c10242d91022a20f134220284000c1ca0a468000824045a80b10110078192030055068030b103000e005c5d42c1c45c43c04494101d241c500c909279002c41c04403004440c90601d560302c0034058a40e080c0c1e640078a5028401444010004000d10250008010050410500007d44002c44504442580e84c42d030321110f1444260302c448800040c0a0f000240328142d020a01d09540b22698840f81c2640750800104444000010310142c1c0210703030148414526400d03800307002c02c0756014403680600e0341001c040641781c652a030b030045030103584000182460004009450320880c0d040f803130203000c48905407080300400ca03a440701c00741c211070344a000071040c1300c1c06500202d14448210740c10006848203d6044d66a80502c2130b44991040c945 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 299576681 1250 299575431 299575433
    0x3100e0d050304080c010603050703170702010801030204050a230633180d110a09020705061501090b0c030408011a010e3006060f150307030902010c0213050601090605090607 76
    0x20710146030068407030b10b4032500b0031551010707517421191554070985051780070341c20800a104004030300c500c1c00010b80088034907104540d00003900703c400610000303000b1030f59000050315141065100340784480012100c50500f910501c0c459140380301c155910b9114200040d42803000c411100c41c48030000e01010052581c600c20900e40300742542066058400c0001301c0d61600c01290345410400704441e02c10008510b94050440901046501039044920002c1c410450a40450070000b0fa00303622003c4815403145d4004028012030711030300700340d004400584021070300f8110f03050003001400a480410f8000c01c28041c50001404510101e007039414003140c2e82c4141083c250503c1700c004e01c418018070703501541248040400c01d0803500e1103900c4ca009500318900340520751500b81003a600c42801100c03000b2420081e84104051844064054030a1551720f05500d000c59001c2d092003000c458004011074040c2c8180c440b800c0203810112503860020398444000300b40c050041040d80e25407100500800c0c00c00400e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 299577931 1250 299576681 299576687
    0xa0b012a0203070e091c0807140912070602062e031506050a14011205070e101b030507051e10020c0a0c0906030309090219030209040e100b03100e0d 65
    0x308166018040c2c0840414000e0104000303034011606000100b8007829900d000b5101c52524001001c1045010028001c01a0b80003540d040d00a040c60f06103555415108002541c0344200340d04e000ac0c602072200c00241158021811601c158100d41e10301c00c01c05c40c07150501800480001040041808000d818004070f03800d80003500e41341e070700440001107158481001a82005280c3c2c000485c600e1480c840c07000959100025000c40c24011105103d98246000d01030301c50000800c0e401d002f17202d21810410910311a20303015650201c00010306001c1003280c1070040c01584100d00607200c900c14080d015042c40c205009600ca4198058003808800c1504ac0c2400d010350b100c424404224442c1c0d12803000403900009480005007a112000602035265140290610456074131051149106000311104c51480452010318442c140c500103071742d26688000503000f003c41c450800124411103000a810011591081d506100f0485c1100d12111038040e2a81c281c0f204022503c906400c8012403c0754640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 299579181 1250 299577931 299578007
    0x3080a030506030114153d050715140f130b09071a07060b0a0b040909060933020a1e090b0a080a050105151611180a0b01 53
    0x140140041061000301c0c0c030091083c001070360084000a03004030100814036140d101440081001281c5001590000c4a15200ca4a241d603260010719200c100c500c442c7c511600481c0c4407590700c0580c2001104440030000d0003415014208001c0c0d512482c0860480303003041c0480e900c5484140344a44d060708103542c42030395881e0058640c01c2c407403260b0700d0b0202c0e540080c0c94207400030000c05500307507454080f0b60600c102030790100c11003103000c3c040400c01071104001c95412038050741c1100e280400d1703190039490030400600c0440c42c0540204624000b4280301c0c044050801040384000b030038448450000e0304007a007280305201808006c1900d4036020074071540102c0f6a10140741c0c50b030601040083d81c45505410540c81914600300140444e010003c0d4204c0c0b40c4560343c0900001c1da2002e440a0305501821000d22483c20340c1090500036102210400440b0051014a9400075140303845500000349c2d100492403003542d040529500700103800c031695100c1c0d003454480c020046040115848040700400c002c0c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 299580431 1250 299579181 299579191
    0x2070804181a2220031e0f0403031109040f150509071b0203031207180b040303090b0c070f0b0904050c030f16050d09030f0f0201050f0612030408011814010603080a0305 74
    0x140c0f02c40f020500b40f9001004a80e001e0108103075070b9a170b4501041c41c113178040341002d602c40a24182d02c0c180301d04020907400c0103500030360508000a0110813400d00e09458080e0a01c4594800d00f8000c03201c0083c1844d800c400010311001c1100c10842e034079a0100600c0c2c00040720740400244035560842110f40711131180c00d0000e8006802c1d20700c0c0c04803002c45c200103040c0442e8644089507410581c440c1000c17900f007100b0000d0200304001c82c01c02e41160350040500c0414442c4450f503d030b010540b086c61202c180030705c80c000c208800c0b04c4c0c1205540c83c1c12800c80c1e40c1200350341038451860400014a1b50810b101120f100f80d0381804045855591060800350b0f0b40a02c4150b8030802206001039410b8083c51b120341d0084a000361030390b60817104200d40040c01c6070300174240c00e411a414002800b40207100b2000407a00720108840c1c8100003000422003038076500941e030183ca0a503081c0030b2904000f4110799260b00c907040c014181d09100c100c2141405007070742e0b410720000b0144202000207041d0580300b0380c0015000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 299581681 1250 299580431 299580499
    0x2030906090a08060c09032107030305091e1c0912080705120309150108030a0909050711030f04050f120307020f0a0e04060c030b0d0201080f0a02070804181a 69
    0x8607220b0f40168074000080750381e11a01600090030852514042100003610390120410319901c6422443c9640b06000341903005013496143c1000c100310f20002e0040502007070103d0040890302c0480c18074555650080070019020741d90018061440c9481540b1800a9400e401c003020340740d0729643ea03282d4540d4046c5005075414010040c64035500044a0001c6001d0001c0500a0070710009596211550180c180c1c89048103610810441400c103030041880401c0b6160440b002815a6400f01c0c2550950698001c0103400c0c000003c60b1104800302d04050015104196801503000a80300c007131001c900551440c0c0e805030b50040c07144500516207841c040c124440050866108596510031034004000296000c8407451780352154500d2190b8076101d214001d1400b1180c180322107003660000b27401c40c4006442012a65103507c0000c0300c11242d40c04a07140554000b844a42c0c40307554407060141c0720080f031600c8895504181c002028100605c004101c80351000b0070b002411440c3c00d0807115480100c240c41842 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 299582931 1250 299581681 299581699
    0xe1314061504410112020f0f131a040f09120203030709091a040c080412090f03170f030f041203060b040b09040e0303010603090303060f150c0804031b03210203090609 73
    0x1282e0fa41402041c002c01d880c00703c03240e4844091041240312154580c0b89806868080300c40003469413003d03c0a0b145d14a40c0c00c0029050130283c07840301905100880081c0c02c41c3c1001030081c0c41926561011000d280150320300c0b00c02c40840f0008980307030320050313581c3c1d800074003002c40c00d002c1100541e0021002007021025614680e08a00104c0d081c1c1e601415488040385401081000f48030b80948030044000032072034541c0141c0c5c1410003090b00d0314100e02014188a0020100c102c5100581003210700c451624418161240381201e1006130900d400c840442d202005021305603000e0303005e802100c003a96804140c01e41420300f08082c00c1010340140c0360780d0790f1243c1c0740d07848030b1803490307060000750b020b03010a5a0200d82a002c60030080c0598580d907004d08a01c03000340c202080021511044620040194a002c501c418590300f40a0700c10300440c4c00c060841081081000c40c030004e00320503402240e2040c08007071481180680c0c1490003032201d40b068800b41c0c20130440c4014510b003880090031050b0b0001c2407044 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 299584181 1250 299582931 299583041
    0x61205060a0303171f0b1206040b0123040f09020406020f0a0206030105010c0203031905190c2a08060106090e09010902090105060d0e0114091905070e1314061504 71
    0x100c1028035074032210959200044c074030b403500f411600941c0c2c4828145c030309004ad0103240300001c0085172111141c02c060490399101e80c140d041c4820407a4000d240c100305400b82c0607241d288805c0258018820351016110714602044c4040d4003194000e06140c00034100741c1982e10349401921141c3c41c546c01268103000c10403089151001144c00ca1454060690b9000c1c0c880d890f41c4203151800540310b042c241400300c0904540300050140340c1e42e1454880c0541a0b680c042e2452100c907401d00c0300c81d00140d420707020f50380010580c680e2100008088403403800015000b80c6440405c035088440d81c0d040a50005035040042c0a241807480003041050400c000c0010041001019682100c2c0d08840c0486210b184d803083c03040d000d608000e40c4103510719280001c9040c1c0303107a5440b156180741c0c602c12000b00c01c03203100c002215070525100d54080f081d0400d5007034004040031860951612001c81d040b01442078210014691420315218200d84110000700003000481c00d50f80c240c0c600c200c400d0440e540440c5c1401c0d5a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 299585431 1250 299584181 299584231
    0x4141b09041103070c03030e0309150a111009030e0906060a0c05032a0d0203030702060a0e0109120201050a060b030c04090209031c080103030201050702060709030602180a061205060a030317 83
    0xd4804d904550304c0d000c00ba80146001029030f50300400201a5501c01d02c4214403541d1410402d0410802d81d00c100c540d14162904261340a04a408032a0083e00074840b10f5490300c400d9800065034148290b03104030343d0500200030001010b2041e2100c2d900481c080c80380c4040d06000700300d0303c640c42e8084c0d004c80341400ba40240307070070007071404051440541020403142001d0b14401c00554441c1d44c040c0c0090b501318038045900035034420000b400b9160894940d000211040420351105507101d410031900c541c08052504041d000c0c0c40c060351103140d901c1c40d00100040c0c20480405603400b85c0701111095141500e40a290406500324860302c580c907028850f03841000b94011440c000d40d4640341e440e00e011a45c5036040107400c64070010301c58019504824200701040b548486a1780540e40e01801c0180c0390132030001c4c00004c280c0384502240e00540003910205040313421103c06c40354030084a2080c011641d400e0140101396000e840000c0124001c8641407104446003c0b0a682c400b03200580c0001b20b0400380450707 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 299586681 1250 299585431 299585437
    0x1a09010807030302010e0a03021504031209081206040908030c07170c0c01120204081905010207060501081f0605180c070f0807110103090b040311010e0106080c04141b090411 76
    0x80c092507002035030400801d0b0302800788260600810b00a4481d503481610040d407140c101d0780d40d1850b080303404000101018059a40f0044500c0c4440b02001390542c00e24022000342c1c0803501d00203140c1c403001d00050079460030b8001c12007500c2d03105284509546504001070340e0754124000c200c4181c0032007a10503003c000124040c102101800000345000e80c0745e04009010301210345000d0404034010481440101000541c3d507600c016040c2003050703100319900b406402401100c800411950500b000058140400145d0741c140402c0030503d080f52916007044a0704441d40d510032241c10642c5c80e0080500f1340712142e40c0380d5010440400f4180f4010b0290740c0c1d00c51400350a00c080360f049502082d460f00740011008520315618003800c1c208410341c1c450f00c0d2015004d20040000701042075030550310103404801e40101c00715a1400009005c041d496804240d210340c0e414070098010381c03030038542035003210303041d801c4070300034401025000600300e100c0414103501d9001549c082e0b0082e8660151524080e602001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 299587931 1250 299586681 299586689
    0x80d0e0a030c030f021f0507080c040806061e1207030b0c0c0c04020d060b0a17130515090102040503070f0312140d020a0201090f060f050108060606090d061803171f0302041a0901 78
    0xc0080c7c18900b20f0fa000d4a00c0002030444141044180001d101180c4005240c42c1c00c07100c12101c0c200f07440800000b1491400703003007040303d4100d4040d030050421078000141407400e0764464500c10701c080d0f480e1504038081f40191144114a58040000c408540c02d240d8010301e60300124010108000f511001c480304c055115011800019943e09a1402098140c821494100c0f5000c0200044500c8503241c2079502c800b00110140020600d10105109010960446000b1700e00903040c0d400744da0342c805014800035298031054070045e03040180c1144a41c4215200d100c07020b00d011100d400d04081c1d807101c2e0000c0d0026480501959a15901c03200480d5448035003c540c01c2c030520300410060707030140007001074450680c48280c0d9a80700c032082c002d41d40e60f003105440803044142c0e84018030500f1400c011020b01206c804201002d61000f409801741640490f02030b00f00ea084400b114180d4035004002031041018004400a40801210502c0140307401d401c9030740e0f0980415403440d04603c800c0009a4109030a901c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 299589181 1250 299587931 299587993
    0xc010c11091006020607020705010504030b06010c050601090606020f030307080f19050f0114040e03160503040f060c02030f060415020c010b040f2301120803070219080d0e0a030c030f02 81
    0xd0030043c042d4100465680300341ea41c80588045071034400064200e00503400020070300c05e0f1440014846034031805c0b1aa4526802004a503981e50355080404001d01d018040d10005010f441080041c2e002c00100b02c0380203d20300c3d0395608407540c40f50510801000040c20747c6000c807215040001a00b07440340a1103000320404051280d055240c4516005034200f02044240100d0400002e88203006020082c0e41600c20382a1284504908900c1c00380c2c2180300d0307034201407140f0640c6000840c0f0030307900034090380045100341c003111590140c4488a41d030310803040318014070000018808010b100900c1d00a0b01c01403198600114841500d940010f040c4ca4407440000005aa15020342c100d401c0c1d1003038801a4071061004004595041920040044e40c0382ca10142042d18000003148100340700700100300c1a402c000f05da001c03909055160111b060381c0824002c8501070700b0a034855184445c00311b81d5610321b070750545805080c42032641d826503100c03104a00c66415806850f250361408518540c541c0c0c464030303030f00c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 299590431 1250 299589181 299589211
    0x10501090c0e040e0705130905100209120303090c010c08210a06150e10090e1927020f01090510120e03090a090b0f041b030c0e030c010c1109 62
    0x2203002040b0514aa2010b485079080c584019030040d40030038584161b9401707880900d201c0012410140240c481e14030010140d2140b43c042c413444110550142c00b1011003100c000351011043d01c852580c0f0b0100342d403a564140c2004000702001c2d8042c0c1d403100d0b10310b0b201c2c050315400c00615a4404851659248039620300d00c1e0000d04120b06403040d445000d01a012400e40c008003a107800b07800600007803240700a00d000c1c445444903045400d0180700894010404408003c0c824505560102d00202500000420250a01c818504054408a04150203060b4114020101041d076020440c0e4042c00402d0a0305201700c80402040c16240c40034044000069610741e0314800c41d01c0c099075822a960004100482e81042c0701d2503941b83d843c0741d00d144c00c4404910010a814100000184201c14400003040c0d109141c164400c030b0348450462075505a126584003007202001c58034081d10703014031200416604d60403200d0303031144541c06000300407140e50060b0074101c400032941001c10940341c000c0e114080024a14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 299591681 1250 299590431 299590451
    0xf03011122050a031113151413110a1407020f0f0f060c011409010603111207090f09031e05030c070606090f02030115050406051803030c0d120c0c02030706110f01050109 74
    0x2da824944012000c0030200a50b040b0690400c0c0c181895009a003440340700d02503131804c541d1750b05541800d540103003000ac0007150600c0303110030120ba0280301940049608100031240d2840d507c000e0740c800359000391440003480b00880402141c40501921590302494a200001d45501c2e04000f4103003a01000e4000a82600d1101034201c02c1200100f00c0b5040c3c2c0e0414000340b0000312128102001c2080c05e880041034225040452420503c036038100c0b40c00d003450900c024040f07511540115903894003a403180650300e40d200504c030f803003280702903035010200b2400c10100391110103200c02032050501130711000413010340f03d121ba031050f06e072101002c0440c10340110040c06140039204e40441035459504240746003d2070801c0182c482d005001d040a4902003050500300700d51401d0080700d0240c0400d90595098013501c503005004450390102c01c070215490a139a1140050080400082954008008221503440c00b10304407a2107142e65400d0100d8040e40702c2090010754240070f0305018000b003803008a034030100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 299592931 1250 299591681 299591689
    0x504031d090c040621150e0c0309071701091b09060b120c03040309051306060f0207030201140a030b06030103060603110f09040b04051f0b0f03011122050a0311 70
    0x440d59200c0c46480054240700816200c03408803000c40d080d60604690aa110510101c02803481e641255502c134100100f1048419060304401c0c182d483e441b144441d65141d051008009000884150300c141c0e000c91014800e146031245594440302d180c07000441c2e00700241d40c41106411440301c0000680c0003034075082c0142501406070034027405c0000070007410680d42d017200d26620a80030300101003200c0008013040601d880707040381d031028001c06800001214000d05118006052621801c4001461304689a1680b8804218142103e8050752411810b2403511010b4203d640420000e405150f9684407023020b03611108041c50003107008600002e421448c50800414540417080741c00d200e078040411401550307a801500d550000d81001c0051035541d21440e10926181c5581e80ea86081d80385c00450300d420000503002507614000030756500490032030440506003661036071400c00c25424418015009415041c0b800c42e0103921b25070b440840c1c01951a4081100c1001a030019503820071001700f170024600b0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 299594181 1250 299592931 299592977
    0x80f101815080123130c0b07120e06071b0f03030f090b070804120302120f040311060f0712030204050406090f290d02030a0c06021e06040c061b0501050403 68
    0x66900020b106034111408000084c0700c1420200b031508007000007080310707810b4024070203201da503020766020010340d00ca921505403500441000c80c3c14425004486180e18811400d054180c0d8010b001c00781411402e944038404c2e604507040510101da122040090004e02d0004420011802500d0700c042074510808000e061040c0c1e1741140c40588010840314001490620407103040b81c6406c440d0b510b203490385190880c1415001d20707002c056400c0c081503d80000250030b0051084a10402c1d000b44c000e919881030042c05d004140b000c000c090350030711130040418064035421013102041d02e8014505626600024119060b5401c00c00419070381d0784510b0078201e1580701d03003041d217980080310340e030081c9004106002d81c01d44000114080c0b44085a040115101003000c140c01030342c000510100161152002507560308030700c9071000c00300c454941d00d111080005c50500d0007540c114071519005802e040003550700d800f501c2c440d40d03000e560036103010010450a00ca9180591b110ba940c1810030781f511000382502032 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 299595431 1250 299594181 299594189
    0x10030b09070c0219210312110414010c08030c160b01090f0b0102031c0b04020403230d1809051801020304030e0f01020c01170a1d03071a07080f101815 66
    0x11103001e8188516540307a09a19502598a407225600d82c505185c207c2e22001d519000f00c14650070484011541a26580900155002e03014211052110840119070f0807480000c05410703140300f0000315079210740e06c0f8010036481d007180c2992071784c50940d5601c803940c0a000364401140340d9036642001031101018020448002c10901c019810202e817205403800c44001020500410343e5987c2d11036402e40c4803501617400840c0c0140d0301c00f40840e0904038504141d0f0032012804041c0c007802d014075803220300500d03081100c2c1480034040c241103030401d98848001c01b006042c0c2038105503141000700210310709000a4ac032403407280d0340c0e542d000b0312940180254421540038036030540d04042050072250b6807100180c090a6402c50144006868600d890801014000c030300c02e0f4101d66822050301d8001c0000014469544035280e1641d01000300f2120300080c1c031090724000000b4402c0710224101c4240c001490750011580800c9160075551040071b11086941e1b0f80300c00c04003a4440100d03022106020701410700230 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 299596681 1250 299595431 299595469
    0x120a150f0b100e0904060e010e1b01020114040f0203010618020d0e060105030d1404080a0f03142118160e0a09050c060a0e0616061b08010510030b09070c02 68
    0x300c2c500d040240094a000e032010b40107034030580005041c000c80d50014403000d07000100030045503126420b8140c6407140303889050f040f500e0485041d079142d44144034156258014015a41198407103a4400350208842d800c01e0f6450340d2a500081043c101150400052624441c0016950b048910b00c540c20740b21240000704151f0840001089140c90101e4400c020301d007a4603000404817450604808540031f1900300c00d140348600d12485082005590740070901c0c50083d26002103180100f20368100744d20904000d0340d8058a8419140011000503840e190041c003103150340001003101c02c0c0344915180620052451071103040c0c00c01c000313581050000940000000e541844110641d84415079601c175115090750044400003121146144111001c460203034000701015690488401070741002c100002041e11030700d280c411104c41206032607614902401594894001607841c1400708410fa244400b130141c181619210805059907851868510400f4243c460141d564014010b20103541c0d150103542c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 299597931 1250 299596681 299596699
    0x10050a06030b0a090b0c0c01110d0518030301061b020d02090901051801020f07020906011e0905010f0c0b061504090212011401050c060402240d0501090b03010b010905120a150f0b 78
    0xf1031704840380198410348030a103055642c4103040300903005180c010b1130800c55100200741312410303440e5608400c4c0a1001c1005143d046100c011700d6035120f120a20079540031603080342000402c0c0300106a00e40c626030005000e81d1404865070003048454204407480d1107182d642d4000c0050000d140b50004080140c0c1c20021811301c1b80604441401e8422101c0280c030404054002410503841070798954200c031000c06840001c451140005015003000d8092a40454082d90300500514441c0c0560750f84190004d030041210344840d400c2c49005410511040f000d54410080031401c0a4a80000e140c071038034410700c000d51903251040c0d094006800c620350034104403013003081007200800026081c3d0810f8040390714840f050902c510240940000c1000020009004900c107210300c0d0b0554001812503403c608180403e03032011003014204c038a01801c1a0104819400c1880f650038401c0c0c1820a00b4a5202120181d0b182a190310028180a002d50070340c241c1c450740240c800710014044e01106000540c1e410103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 299599181 1250 299597931 299597933
    0x2b0509070e0f04050309030a080705011b050a030c11070303210e030301270501090b01021002030106020d230304050a140c0f01180f0807061808060c0c10050a06030b0a09 74
    0x22181d0009040248048616000304050010a1080350b002110040854a1041c890328000300c01d46c12034841030b24554644a0310041d03800303001d860500d8403031440d502d0520781910108107400400c603400141c81000316405e40c8a203d114204040800746010b42c072480f100c2000e142c600d0181c00400d001c580729403401d284d000e4042c408004160b038103403400034500c4503003072401c1c0d04c8800c500c4c03001000500045003800300010f190740b0b0560210b0b00044080c2d003941c0c810079409640c81e05074402071041c4001640042c2c04043c41c144183c1007094000c40d215000c61503600080c0340000b1640003074030300782e0b900e4000c00c8030318081003c003000c04540c1d05000c0000c2c01000500400082c04c0300c01c0c11181605028443e050081104045070b0800b01815007807090480060b00ea20704039079a4841d901590004c03d4503804031066451a8001c2d9008640702c010080200b0399403460b460046402240100d00f6510031900c00e02402d1425004041c410442200e000920516508000d042c0c04400303015502d00d2131501e00e03e94 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 299600431 1250 299599181 299599199
    0x40815090d051902161502010c020105070e1504081c08070306051e010e0d06290904030507020105040f06180e04030801030305030c040b1c0501061103120a022b050907 73
    0x3d103c443c561450b0400d0842030140c141e083c21100f024101c040c201c404d5000c50145010f0300049030040c0643d00030005d403007903040142d00302d405c04d90301c103001b1a0030f10344004903c0c030309115800d03405510610202c2c101070380c0b625201e24001158100d03c048030111506820781c130740c2c8003105952106080c41c041c4400c0c0e01d00000f054400c045003440e40c6501e5046c80c011400b99018144501186901030032041c0c040b203d40c00c021000302000c011209808103060081003044520740c044407400c120007014484a80c8030303135038152060341c8408400c07818043d090000081042e08500c402c002041603403070781d044000030700040d543c0300d03012900114500303c02c0400380800300354400303030041c152580342c20500e5807500c61842010140c0500c3d4000c0c4007800002590528840c1c038002000035075928028280016602c505091340e080000f8001c940045d4000d021800c9984c480d82c0c0c0258105044050062801d075094142107501021490301d114044008030103440301071101d2003626446010040505142c60612183c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 299601681 1250 299600431 299600437
    0x5070813200111160806060d02151b030409140a05040503120603100e1501121e0602041a0c0d050903191403072402030601080a090c0803040815090d05 66
    0x4207841814071202107105074010301d44102c01485800c1200d403485100102d800040795140590030700342c010007000c28601c0c103203180c0301030341158028250b800200c038428071025250810508250380c0101c24590400e4001c0500040c4083c0c5140e6002140502424104601407075000d41100d19a84c0b4010412002c104048261480c0c15228030719032500d03032030b080d001a18091403095110101450661004080d14002680d0745144000d1014555503a0342c030600003c008080903805080741e4680d0381070b03110007408400c0000c02c20340308142c0141001e4a40800c0d9900d0105136210300c0041d0800076a003d26940e04000d4005814854030385035140c00070640c08a62120344400c07400003001148140202040b071500c4189010200380021a61142c40c14104107808032458129142d035006141204d900840d0280212841568103844103036898603181c5103000100f641035000d4840143da00e0b4007190588080c402000200003880007804590424030300905020800340ca0064150301649991140035001826 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 299602931 1250 299601681 299601713
    0x2040212040b100b0306310f0209031207030c021507080310050415050109050f03030f0d0207020a0812040501050c0a020d030e010201141621050106020d0801060f0e04021c0f05070813 80
    0x441f109040d040741c4a4404040e9441010906401c14207030110320380c041da000c0e2510b031004600304c840850024220401d0ba1140007130142c0010400d2100b240503042244805085841071454103292000f141c8400300d280e001510101e02885007264104000e03c1c041c0581444100601c10064400d803900f0006400340003140305440c0109080e8007204601c3e6803d00c00d40f11110300d24888a540d5510180030040254040398089128105000c0007050781c0e003002640028120b4030400051900b41040c0040d035aa40140800c4641407040ca100c403030040e200d005082041d0f611a450340b007403080c0014006400d50b0198840d0080091110040000031003101c0404d0300e03002c4690400b071468800142c94200c00c0c1c201503040c1c061050501000107245c550014110b4003039a02503a961405da62207800485a200f80c0904540000d403d0b9000d035940b520301383e8018920030f480407031040c07441400d020703a0505982c064031241c401c150781c80003004081c0d50001c0d59280d02090440034990b003040c1c0f86da0703040c1841c1c1d20780070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 299604181 1250 299602931 299602969
    0x16091211210a241a0909030c030d15050612101d0103061a0306130b010914150609031e1002030c220f03140c060f0405040902040212040b100b0306 64
    0x740c1d4424400502c0006080030a0100910000a8104581e91307400c07020201c2034028a04000002c02034800803050302d44415101d0f002d586402d015100701006000c0150340758100c0b03100d00500040c1d5958980040c001e40003102090324a500d01510340b000320740c0d00d6510106041c0343c9a51000104201c035100d0f141035a07032000c4000340164070800003074282c031041128146c0503c115000d003e4041c0e0b82c4580c000405d0300c1098551802ea807200c14040a8403942407480d40702250b207401041540510b00100c1c100090302a010900380501d9100007494010b410b4101a070112800100c42c050031014480d2101c2080d003010158510f082c404004803c620a80c8182c0d46c034000c00040d500c03c0f03a241140f10400a20081010a10003522414102c8080c80c41c0030010304184545a12080304d1b00b0080143c500350399080800e90f081c28540804d10015002d0f44008a0b03210b503007041007a0f500c0102c0c45503140600d000762071a200501e000c2007144503003a02600038550403034052003002880d6982003810480091101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 299605431 1250 299604181 299604203
    0x909050d031b110309060d0e07081f180f1a06040b09060d02010314070c0c0f0b0708070809040603140114010503070b0703030f020d02091801142704050606031209030616091211210a 79
    0x103031818030810cc00c0c0d200510305140d8101d181c00b4420703c2400e4485692015803441a55120001007008031131440003240c0c2c01c02c005000140d041e18054441484150040c100807070300d5000c083d04000c1402c0103c407007001080340310b0030080900c1448206a8050320429100703149942c21f001c40103407117000f100f000800c50348000402501b0400d10405444803420050000d00038161285041c10030345103c400c01d81c0d05907103801c00e0180044684111181202c2c8050040d01c8040c1c1000d40e051701d19403040c04180d06054844545402c910359601c000c0070311071011074006840b03480410800a140d010718800d10010450702c001488480007020300e060402000b01c4049450090f00b0000d89070044003c02c1010405101070100300501c8008103082d80304100031019514294200603190906015150800d50140d00030400140c01c03031a0728032030140d000c0356420140b2015950307010f9014102a0b9000480d0000f04c40c41c031882040c101903482c81003100320000416001990700c00d07282d079070702482d0502500b60242c1d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 299606681 1250 299605431 299605451
    0x20105041e14011107061a1e0103020c060114090c04080709020a0318031106011a030408070609080409020d060e0106020a020114040f0909050d031b110309060d0e07081f 74
    0x41e000900036124040c0c0240206a034580d01301007142c0122900b41c4401d0f041066910092032400d16030305561000030311501003004030000301c40008400c048510b0525038208500c012068081203464000c2c000c4102003683c400d006003d00038000406494000a0041408248140c95012a81000342c0c2d2007010010384a4402103000c6014120390b83c601e6074080d030300864442c24198054409070184805900301c074003a0342d9910001680d01e204d043c02c43c1e980300702803000c10700240e01c1c4801415128003c40300800c5551941e00d682c18558000d6201d808100d40c005800103130305400f8001c000c02411003900003055507240c0b41c0043e48841d0f86100082c10001c0c10341c828207408060b0000c3c1d5003e480b40346214440e0302c0d144d0400100400118100f56054400c404229800c00c3c070902130b0314401002c80040b07050940c54140151200007030070100c64194001407082408035116040909140d02ea01840411005d074a800403a052000a0300241ca40d84c00841e503920045a42c6a002121070b90001b10000e608000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 299607931 1250 299606681 299606693
    0xc03150e0d0c030504030c0e040303110c1e031e0d140402060910030e06010b0406090e0606120901061a0405010806031527100c020607090f06030b0409021816020105041e 74
    0x50340c000030016481d5800210302236194110701b91140e40b094600300302c030b00c18242e0001018004c0c0c030804921503100c03001c2540812405044600c01c2050101220709181d0020104441c03201e0a14100c000c81e40e0101c0c05000b25425070040003500000140141050f00306900443d8040c828001490f0080e00c1c10100ba421861207076000200e4041490103603052075841d60700502066200c0d115600c00200100d00115a404030f10f4076050051100a00307042c0342808451034104030240040001160795613070b910000e40c0505040c009503103039070844005503070745003440b0005d07060110281404c2d00a9104180103240b018281d05111b8101c0c41c5220700d642028a103c206600700303407140f100240e82d03020b810148071491005400034558280103400f074030070340d69501d04201e407184070b54802d05030701d48031213441080380074001c3d0300111100c00b015002080b90b1815801141c04140c0e00c802907d05201c5000030441c44820503803481d4a9421980f000b4402424203850b41c5000b2004020741c4000c2003c014003035820049 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 299609181 1250 299607931 299607937
    0x1e021303080304021c050f010c02070b070210110105010b04151d0f030109081308071215110403140606010306060c050c1903050f011b05040305191407030c03150e0d0c0305 75
    0x2580d1700400c1e94104852170015141c00261541d01280e40c00c0a150464643c00810b0701e501359844107510383d00344441e6400b00041ca108844e0f00505004d80340380158503501080c02070038080d01c1c902000e01d075500e1405240c1c859012115465904200030000c51406404400c2d583d00301d8030204803a1805400e0a1100090041020110051039075400181d6010071622140c0800b048500941c16a02900e595001c00204501d0412000b41815041c41c44000303010801c0d40001200002d540c103003424140c482c0e0341c0180ca101031280707101080d485042017084d06e60f49401040d010340454903052541109543e034603a902e11a61003114407a40508501c040300b421020410401107420000f107400171300500d00d000d07000300b10140425010300030780c14070802001e00900454089a90000003410b0103816a420b0f091003140e0030300c2c1141c121401c00000b05491000b0494a03001d076001d210701c2c04240c0e145280810080904121450089040000450440d98041a01c0303000c00e4450030316000d0b564403850121540d00c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 299610431 1250 299609181 299609209
    0x40f060b06040806270303041401060f1409060f0612090c032b020705130e120406020d080a0908091c1a0f070306290d09061e02130308030402 62
    0x410200b4001005400040c040b405851906402c40c03080c80e01011071001d061401107071000315801000840e00007505403019241c88080b03031000052980d224030414046034096408054540001401d030042c500d044a007a941015085429520840251000c030310580200e41c2d1064140d00300b00700103000c1e103005100030a821074004041d40c4200c03001d144510a400408902e1104188140594840031400010400e06650005014150301c040042c0b00c41e014061486801020340902d81c3c910140c0560100940003900705a0042c0c1100d85100304000e050309002041c200d0154280910310020401c5241140c0e1a54000d95400000094203012140f4100b10014020070b10010158095000c1d2946a0201d02551840e1035040303c40e2900700c01103054603128044c1400244104200c1000c034400319840c8038440d42011606410100e8040e800c0d000c56075403000a942c956100c0c5129040c0062752803a0f100320101e2031908606003100d0b060741050f500c1150000407c2401c002003c14150340e120b840e220414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 299611681 1250 299610431 299610439
    0x302041503150e040206090607030e030d0918060b09100513030f0303050603030a020606010f090314010c020f030f030f070c080c0d11151f1502030a02100b0108040f060b 74
    0x1188140400070000c20750700203196602c00280d6804103980d040010303d280141d40080c07070030f4103003007209007002072036400700800b201400300440e070801c0c4644052083c910400d0468403540c902520b0300059040c094040e601807500989000f4040c000c00c8003950943d6507040080e00c01e401c0c4010851421341d024480d04000c044600b0042c04000200b0102080e0720301c1c214401d540c01d02c09621850240340d540e0182c00d41d40000360b044240024455403181e54050b90300e00b01071610a6005a03a074940e5900001380540c06e031440d946501c01441c400741c0402c082c045c0e200c40381c0000c44c031340f141e8184151054000500880a603182e208085413100348107901c01e090a64001e03958594440c1c0d0310076096618000900d40c0e501143c003a10409480700d101188010442200c94000c48040e030f1540e501908020b006248002c48522020011440400800700c07064100300301d0300115500d586d2258041e1810104a0300078003050308000b050015a64801c103c1c5810984c0071007050342e94680707480d00e803020b01003590b207090300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 299612931 1250 299611681 299611709
    0x50903040e1003021905090402040902040b130b04060b0906030a110d0c050705071a09131112010e010504060f09020702030a0b0a020901090e060105040b0c150103151410050f01030204 80
    0xc4000c1c8905240d00f103134401c86800103a00e90b00c1a0020ba10b100c0c51040980c04464900040c000d405c0541001c500a48000e0001812244013000518098506100700580c1951400c41030028200b5218000280c10000e04041c1007529000c009603140c40300506041d110740c0c81e0b2900ca00f0303034051002914483d0b40f65400038411004030000041c0203420910f0265081d108605000440c880305000d512450040140290f2a02000105201080f29201d43d6002d50f00d58a00000f01c0044100d006030000c4034a80302d0114041d454428140307014801038011520440c03808804000300c5210b104082c00f1180d411a0140c3c80342d415000203800d090300040050a192080c40c1001388155065000381032254090300c80c00005a2036040b20441944211211400b142c41040306214004841c0c01810740308402c00b0440c1c002d41040300380f1084050f02a4012102c1d0101501d504080704194054203403054005031540120386400350803820200064494a8001c3d0641004014940d110b5012103018095450742800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 299614181 1250 299612931 299612941
    0x510110106240e040b030304170a232803080606091e040c091203080c0f0708030412021c0e03010e0303090a11030604030503060103020d0902130c0801120f06050903040e 74
    0x7000a0507121002e00280c040d90f04001c02d46003a12074955040c5000d401507041034140400200c40d809440e0000c461403140c03c4015000a01d801c11202198142007840c0140b28609111f503413405810741c20b0f0320250210801c0030f912983c51041143c1751141c040c5402d0001d900c0ea900440d0706031144a501e41d80001014607090003e40c4025003c5800500590701040fa21001e80c60448181c00705026200c4480c04040d22000840d1082c500e0b10b8101000036102480c0c1121046a400660f00004044850300004002c100500400c005040d0000245001415141030042c0d04a091004641c0144051000060b806d0007140c40941c0410101c03a103a104480c0d6a052004c84150f40303000507001115038070b00d6002111110300300400d985d8061945610340d5425500d69070010350180d0070030008440b545035601c0c03040000d65070f030408007800405210710010b00081d00002c000c00800050301310315059940b036034018000400c0b0100100209401620004041d1a80c0022905600c40c80c0d0102000c0541d00007409 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 299615431 1250 299614181 299614229
    0xb07090e0708040b0702030403020a030809041e06141806130b030f1c03091502030601031103010320120c011815020709060602010606050405040e120f09190510110106 73
    0x900a03030150202131280d035529403003265030b031046000c025000b0901010400008480300007030020f5000003040442e80f00d8003c40780c00c5116002002c040740c902c0d00e8000070040d500d088800c1802012042d9441d00d410a03d0b401ca04003241d101603c0c850107200350250711080107486074004070b444d810060566056001c50656181d48100c460400d41058507030009c0904198000d10414510743e902c402c5d801e02205a4962081c000c0d007004100905268039281d44464680341e4000035400f0b544a10101d0240c0090040c8407c5420b0803020902c2c0940481c80306480b02810009000b4041e43c824607000c0c44085a0200d5440140780e19409101c0c4d0700507a2030035010064003c40ca9070151090043d0030007405ea658a4201d00341c070258031603034010440c00c000602a0313003010340041400d559003070116179581614038203000140e8001c032040b40d00c00f400810051800d00d0240c198030a0071140c0b051402c0c0641c100380000361080c465030741c58014099407052145041200f9000400104100700d00e902c08400e05080c90 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 299616681 1250 299615431 299615447
    0x20c0a020a1502071502070f0303110115320d060219031406120f06010603050114030601051503040507031208100504090b0408180306090729070b07090e07 68
    0x4a2081595240c0801c2900c1400103503002880b4030b500030094203190401e034a05024101d491070f000c600a80d80d003c41d0540300d141007907005620a9540c1c40540001006030b50845041a051b01504515245c040222408400c1200b841c1c6c59044114408412110200000300901400d910b401002032013601e4144001c07540641600c18600301450300100c60300004400325040710400f098104010400714806e0300b0300507162500c03009841c0440e04050b02c6000d00a10f030034001d9000000003504c3c6c1005101c01502c000501c207107400143c0007402d25505080029090011041a1140300e11001c00041c081c04001c001e140000e580210800002c49686400101040411103001e40b81070f0b40a800020641032900c90002c14030b402100268068442d40c1e9071f00c8042e840801041d03003503e000400c0d105070341d6003030100c0f50141100c032004000d12031a0002008100c0d005118100d000031144004203006040b00d0206c03200b607a48500c6100d126681c4183c15234444c10b42d0f4200f03580c0301b4030180810906940116074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 299617931 1250 299616681 299616683
    0xa1511091809060106090b030703050a0b13060303021c0206011502031204110a2309150301060609080d090602031603090b0d05180d022a060703020706140307051c0b04020c0a 76
    0x351030b444c1c1e0301e801303060740c40c1d01061083c104103a6013040004da84034480c2d40080e0700032010020211344401c50b100020040e103511070007000b801c1c0d6511030070010150100404103ea00c0401640c41d90b516200c031001e52158414841d08043c00b0046450050181c03082c0200c1e042c2c500e000312590311301e0905041a9501d04c05030394020340031b0b1900c0c260101d51403041544040340d481d09807503050019400b5205200102c8070103000150441185007101910782c2c0e080c01400c0141c07800d1340d030700b0740341500e000344c0e02c0d1401c08000ba10005000442c070301403080c168084200c482001a03081440c0c0900d0640c41c0403680880f0340d5100c0d00305840007260f842c00380c031884c0d0083d034000d20701c5041e0740b000091007041c0e060325454014150000350344500a4000300c2c40a00030605141001c070746248464114410218032668001c04003100142c214030020f002481c1c2021500701c400128040031815403403c241f000d4a644542484584442c910742e00711407414034660020b03681100040e0041d51601d6088280b1039a40c000d03540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 299619181 1250 299617931 299617933
    0xe0f0601080d020106120c06120608010f1a06131509080102030109060303020d02060106020d030905030c0307033234080405010306090b130c200607030e0a1511091809 73
    0x3001d9000c101b003d5003068108800341c041500d04402502d40c0c101850791a141c2c079858100000e00d42600307108a4401d1009000040713030190b50000d0803031401070031030701c0b851080f001400600060703141943c0d0a01a0741501d03014441031100b048080d50070000c0d036803007000075600000010469038603640280084038803d07000c43d0803121018100b45c3e103c602c00d00803100107a101000e0001814401d41000e0f43c028040d0055030700d031034884000c4d075007142e00c9820b00303a010400f8060840c008401002c4c20315040492440320480c0c00d0f40b1040040c82c18401c0d4000c0c00552040081640351041034940341c40c03e10003207054882940901442d000c1c0c1260840d10030140481d107820310010b80c6010386c0c0606c0340f1020f8010618421034a10700b06140082000054400401c9119106a041c0b0407501c0e03a080440703c641c8005001a242905009096500d000c41c95021600412007100004081c4800004c0d054504e0a002c141280b101079860300c40e009201002c0d41c081b4411180221001a10170694014101d00c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 299620431 1250 299619181 299619191
    0xf020f0303030f0a020a030b031005060109120f030c021c0c0905070203040e04080f090a0b0c06011a0a030b1906170916140609060f0c0601270e0f0601080d0201 70
    0x4205074aa000407289520304401d45400180d400105038014200c4107010701f4000b800700044c202003454880040e01c1000c000d90b48100303000466070800307001002082560014207500000350342d0741c0390304009124010f0a01491078000804c540d1420764100c102c0000c4150f4540505180c207000d0701e800381030701c542085645400c011500301e0b8404421035050318904010380003103485a40c1e0340800f580c40724100000484041c460580307240d80c0d80f42d1020042100200207510380042c02034440c2071038410f901030b1440030000006040c0032095081034940300700850800044012003d00440c1103040380a400154004076a00080f81041d00b00860070000038040c1d01208080d90340401081d55400241080b50f001711410404004a40c42d218030340d01c41a030058085810400d50b0301c041540c0750010110b0421800000c20240c514800c1001030350300621010040002d144251030303a00300c2813986022180c0f211601c485100b440722104000507507640c2e0444c2d0854140d0760307440030090380f111546500c900042d4240 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 299621681 1250 299620431 299620459
    0xd211103040b060109141507080307090305121e0c0a06020301060c1a07090b0307020c03100c0e0f061b0f120415081e06041b091a04030b0112080c0a0f02 67
    0x1404101c0d051b81c5e000701880c4001d2a040301041009050341c520303241098010084480090044000b03140240c0c200e4842924036030841ca0b00504101c1c0580030041c0d80d0b14107110034503d203441d0803000307401424420344940e910006400c86509003465410702402c02c41c000000011000d906c8040025040c1c000c0d0a0f0748038035450703070100e90420007068031008009460408144262040f0300000c507048812401191400024080030030709080b03038044100003403651191580401508000070f6140d907101111029030310010880001c00500a9805c01e04d003055840c1c0300807010311020400f0700614214001241c0c0c4008456141480b0395215004a1b01801d041005108049000d945041d0244c01c0b800408400d514850f800013401c0c40000304803590003615000c00c14041d402c2d025929089040035510601824104a452422000c1c4007010206103441000b00b000881e0484440c139040d11901c0c441414013511a0801c10f50038000e600401c101e90140e144400208000070404148003842911044012051 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 299622931 1250 299621681 299621687
    0x150402030609010902090102030c2b030e0721230705030a03020606090423011b050403020a090551030a0308060105040902040b13170d211103040b0601 66
    0x4160741a80c0c00291007001408241002c2c2c0182c174081a040c81200c0c2828203110700b0314078007600c0c0c00e00d003584210703640409c04088043c800b407490315150904007030000c01c0112a20940d124007074031850744c5940e4200042281c10190906607a0500d4118402403c240003542c81040c00548904102e41035218089000509050202e0f41a02d8590980c01074491951100c061183c6840b00070012204160701c101000510b440a5245413101c1043ca07000181d50416008030091110740280c4880502000380f0007080142e41d03c181000640720103010124003500c1d10640640c1d0105015078002284101c2101c070110842803010404492a0543c501c0075800146c1e0a0400c0004ca100095609904000e00842c0403e01400800e50020340615010f031409a41d00f00400c1243c2203a08010119040010184500d8038440151000b0300b99000800e400485000c560a903604c2d105103000040c0b0041040d0090003200b46540d4403d10600a141070081c905c144401107440e40c030272901104c821410601207015548 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 299624181 1250 299622931 299622937
    0x3010b0907080a0906091208191506110c10020a110a06080105041d01050a0204080c06090a0e0a020922200a030230010609120335010608150402 63
    0x107040d07241c00d2100d8940031214006015485801d482c0c0e45e4850003210001814019907601c0d0844a43d510741c1c81f42020f20700d85e0180484003000034445814500b00340d0818885035421011903100e41001036001040c443c185082028294080350f0103105507800b103003100d80114000d6042d0344203496800340230b13513403104000104015018200010300e1307602c014480d42c00c02e9800311414000c510780b028440c440e0300d103204e800d42d1821980e0309003494010804000d054800c01000844100440780036003003030f5001d4041206183c042c4510400001d140001c111410306640c101d411101c00035000c33101c0c2c100441e041e0110305001540040101d45008014080c4c036140c08000d40025803003140d51894100007400803806900710441490f0400b00306e9a180c044010100081c1c00303181004896891550b24010020704a26069070040e580d040c0c565003a80c0c002980319402d4640e0000020240d10614000038800100d03000030b200c001c041c0b0310701070001700b50181c0042440303105440064000c80c4d1002d032a000d004c1030740 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 299625431 1250 299624181 299624191
    0xa031b080105010614090303120a061d010b030f040215030f2410030c0e09132a030f03110a03090f140d020d02190605090102010c030513230d05030603010b09 69
    0x8848a082413180d40c0360f02c1c010016486c0c001c08803400c110030003c0c2040030380401d440c0c01250300d036201c0c0c040010884a01101c0180f04c1240c958034105c2d0703d4000030300268803000340340205800070880041c0c00c5680e81001e900d9008400f4071040d48915022840050b074050075100d1341c4a071624040341c1165201040c0002c0c2c41004050306540d07807200c0f04803080d0003400070b00044071b0030300199400c40c0c07205031079403401030307110310f0760101881c94120781401c103840803154048150a0000b10790b40003c25800c550390404048903032150481032800918181107516a030540b01d00d50290244a50960074140e0054581d01541d000d11503054030ba03540c0b00e1201c2c0c890242d0101071908820580780410262500d0301c003000b0040c1c00074080c0440c3d0242141d80c0c00050040e6003000001c20000b15981031196424441c44624501a040421013820100d0511114042c540001850146e00c0348100302c00001003606101c0a4140745c00720b64050b4005a00a0010b030000c9400768082e62a015403030000f4640107640034024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 299626681 1250 299625431 299625437
    0xc0915131a040e150a0c08010e07020307020414060108182505030a140d05090a0308090111010c09081903051204060615080a0b030d0e060a0903020a031b0801050106 72
    0x40301030311562028144011511024507100780040707141c1c1d115801589192414a0098450301000907940c80c041c038406400004181d00d003007841c1e14500d400004103819140700f00b03200040da03039455400b01e10714807840c200250090300b00118407542d0080403e0081c0914400d032162411951169000c1e00d0700000103000c2011031340640742800800c184840030300400b80d07102c20750b03090440d207035004a494602c1491040381c11440e0550704890702c103c2401003180d52981480c01c0b5161000c04070029001d82e109000140c940840028a203005a000c0c18500301118070150080c002d8104070365000d81070482510603050300e4055039000642840c0c15503090044107525854981c1044002030a00008400007841201c810b41d41d85000305003e00e011381e11000078800d541d80c080702490940080380c00c0e00c2046500c0d50183c3c0c4814074642003a6041000841d05807000e54103140c0740c415041c002c503001c07030455102a41100300000c02100384040751a10410403620008450f1509a940c25818200d810901ca65400 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 299627931 1250 299626681 299626699
    0x3070e09011817130b040602160b03090a020f01020c041401050a0915140d06020708040512010c0210020a050403150501080609031e0f040e0901051021020609040603050a050c0915 78
    0x40d032403d420203410702c0c00508604000e00d41d00c8804101440d80700381c001c1409640940701100400410000010241206035040c90460030020412030303950604281c02440b03010003000d200c045034800c0284506403d00100b040c8030b60004c400f15404803503c00e010702c0380180300041c40400c10b24118000c20402c240500c44008100d403406e0488030900900101440c0c0c80449001c81e8800f06181d4000303040c45500031140599100e2070001080751124055520400d240d050258801030300ea0089040920000d84100250f9102c0c185401203809114940004049511090107895a07400d82d6102a06854412049483c1501d501c3c28660b901d0103103060b0b215541c00840f000c1d050300104440a0070301c500c41c0311040340c02c0c10340701e02189881d82c0c412104030905a550703a00f0054a08900a00c810007813010707901c034449184c5041c202a05680740768001900404000a03842e12507100c69101702c006507004800e840301007926280054641c290118854031070012640460305e49070b41c243c90b107007443c0703801444008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 299629181 1250 299627931 299627963
    0x109080d020310050d0c15080105030d0e0105220305240a0b01032309060c0c0309190b030403020d091a070609050a3201020a0c08130503070e090118 65
    0xc0030b9440107082e0056146281c20028694607000101e60185100b000c0d1006080d040846030b2401d5240c05214030100032801004000684002c00c41c040c60f52214500203c1c080c40e9800141c54900c075840301e00c0320040340b08420103800c050400c002400c0d01d2090041d214070b0111812606203201240b054008a691080046005500a6840482d4280781810041080c00d01040418019903501c40c218000080004c00c001d0401c100b0700180e61301000c3c0742e800d00c0c2004203516400b0750364056201c10901404003410788501a00326804080c00402c841c1048581d071f85080d07c2e0003501c0d0060017507000c02140242c080440c1c807040c00700451380c079214440440e40c03e00f0140d0729010043c03e241c0e103064030b2500800000d50007144040c481c010700c80509403100e00300c020b507000016660002c103110076915644184194640c2d00d500c0382c03801349402c2c0c004040c6134841e0010540000c01e22125030146038541702e84800015242c024032407040c4278001c050700070840c0c0394200340c0d20240801c00070070090150701e0402002d9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 299630431 1250 299629181 299629207
    0x141203040509070201090c09020315030a0302190c030b0a0b030d03020c030a030207020112050a05011502060915043306060f0e090a021b0f0c0307030503040501081806070c020f03010908 81
    0x15503c00550b1001055896540c2c681050980345030304000c00aa40010400400e83c00d1440b00c600003d070164000e08802d00c0580b8003c1d201d50580c4003150101c100b192400082c0480340c40208082e540110b080f00e4035080000086c802002002c041c00d0203405810842191240644251000c4028175000b4601c2c1003c01003044000f94082d1300200d06119030b18811100c1509075200d845d1042101140014680d4103100400a07900101c00b544000c55200400300280ae0002041040403010665600300c0382c3d03112880e04690080c500b51383c1035440c003014840b90000c04004003110010032081441045050744564045814a80c481003030300c082444540285103e043c04029a0b9000701319038001814505178400340204ca03118013100d0001903004682800c45c0c88402d201c0088401c00450082480301d00d581c1d0350641702d00aa1082a051021510000381500170701c101045140c01c2403000d80d640742c80d0952000d03040c000c2884090b8068000d060107041e00e400d0501c1a442019008a81c00382000c9606880c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 299631681 1250 299630431 299630449
    0x105181011040902070309181a0607140a0b0f011d2404060b1c02040303080703020c0a02180901062106090503040905130b09010203060d03030b040b060a05041412030405 74
    0x90695040e082000190750f1000348050a0814860f5880d4000f40d0700d0302d0000701c00311f01c80c80008100d140c903100d041a0f0705400840d2100102a00f82c81c03054407815282440e45110040b000203c0304ca00941c2400020407400700f8006101b8014200601e07620303603c400701c40300e804810f00085c40d61680d003000841c85440fa043d04801c510104840112170903807881e0b000c1015100f01c2d41c412200c1410120712580180702ca000414582840900c08505003842c0d0f4900034510742014100e28181580050404103c4105100313049406801038100e5280c0780004e500d00c047d114086528020b0b9501e00b400204219481c0450500c000c6103d81800c03500d203c4070b488420040003800000c603442d01c020040042d0754801401211702c0364001a05c0c0c80c6501c042400d0041c244000103203110004d91040080140036900d4000d00207071035406180c0010b400c0104408900104000400241c1c48140441c0386413003280c0c403000403c10341d20285044010086403005016043d00a500c8085140d0402d02040c04181002c0c0300b1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 299632931 1250 299631681 299631701
    0x32a060c020a35030d0e0d1403041a0c1c06032004060812030103050f06090604060e030c01110d0605010309020a05040e030f04060c060516090308090d05100e01051810 73
    0x103240f403400c4040300c40e1409065195008070454101086665494280384142881308441501030010143c000760300404c1c046480d12900b88514002c000705061043d00410042952000c1100305214140380c2800b50352900081000d5002c85166503209103082414000c20303040380d0344103011440405840200d41c0c40c1036145040c50f60003940c0d0b4040060081d10811a0300c1d4011003a2401c2350b600d50560a20a08288540c180250700303a1084040c000d06034000922180d000d07400070307000200d6150070140142184980842414190700309082d030250258444010021003007460401c000442c1e0301c00c019410340e00044000307540914504d0b010070460809410500a000c1d8cc3e000743c0e8600101d0b484004025001500450000b03a880f0744040f042007014030990380c01040c818490a060b006240d0010407654607404000c0c501d4002081501094481181c4030f0242a4030800b600d00380140705010000038440400b140303542d0b608040125080010200542080d10b160b04040d00c07151100c100ea260141200903c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 299634181 1250 299632931 299632979
    0x507170703050915040f0c050d0515190e06060f040b0102120304050a0c060509040c1b2406090f0f050c180102070b0301150216051309020a032a060c020a 67
    0x106004c0602841c99040d441603218100d40c8185440604000d010b240c22600720314080c081a40a90b4041a80090148071607685803649983c079550714211500300000d02481040c0460402034188a03215000c51240c0c8101b909954441845060100701b00680310807503410b902507080346e91942c180700303420001181d110380250201c0d59034400c550391716801780e42603074042c6c4000380d4082601703201450140107a09a1070040d03c1c084484000741c2d5222070441c03100078001000e4140d08000c94108810a40885846a02d2144104001590303001d04601505501616101c09071500035400000b00681c858030380650a81881c290070506640d05039203081c85007000850540c420303d10f000460114034401540030b4080503001d111415451240030707140032440ca40c00205000c020905018540703900410a0202c03500401c0450320314135a0002c00c802d500ca641000e01980c040501c000a105002016a00c0e07003007075540000074030359070368800b164000000d01000758410720001007000701c80d11030703080101818488a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 299635431 1250 299634181 299634193
    0x607030c0212060f040506090102071205072604050103200a0c08040911070201030b090103021f120906090b01080601060503011a1b010e01110424020f01060b03040605071707030509 79
    0xc00618150088800e541c0135001d800420040080034007000742c01140c403e0080d800c1108582d0b40002c072000c041a508104000814140d050029080c0d60748451000014141198040c448c0d0a5200307600901031580070070700301520018524416540240c4010700044402d0500e0949882201c020b8243e04058603561014840801d129103c0e11903800c1056001340000e94882d2039100150a481c5080e811900c0380c0102c20040016032100c400c03090424401c403035604075814240e0703800d40f40309100c08544800f0500e040070b401c0402410303a00a00119001e10f140e800e41c0da07691a9078660f42c050034002e20f400a00148010014014140b40d090040c0d02e01105075420280ca1903040d245890a009403030203169120b504c00c4240c1e41d401c5c85485848801c04545030710709400c0504406401d59070f4103d94000a088002c3c0e60a564404d10000c1c0b8a030017600001e01100707541e000002c0142e0001d440c20b40d000740c03502c40820103c60168850495007554260b809005640d507070016801050000d103024400d00500b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 299636681 1250 299635431 299635459
    0xe0d0809060a1d01110306130203040b062808070503010e0d0e04020d021c0501140d0b041506030803010b0301150c0213110904230603010504050303340320090607030c02 74
    0x28000c5c1907101030303807420a6450b0701d0304c0c0c02008004092074503000c2c00c00d40304000740720200c0c01c80f0785640d500083c01e650300980701d1240801c024044489080034a105003150300302149112004c140d000c1100c06c01c500030300000d403000b1031583d1603041c1001c1c80000f19200c11450107580c10141c0140540d00d4109400600744400517092098420b0390030810750505955800502c00300000724181c0c0042e050079603400507510215900c0100310100644041d001012070790a031501010507400c03100266600c0300586440f5603540140c079a068000303020301c1e07508041c0072035508030152044689180c0c458001307200340e80d07055400c2414001842c45030950701a00030104100401911a4062903030081c0c00e040020701500450b6041c0f0010b16805482c591003641070500f480301050f00041a85d401815102180400032004101d5184201000380326120801c00503890079821a0182d1082003c001c00000c00307055007a907001983c4061045422007903105e1002c0c400c003004a031040d0a04624580302412002c0d91580d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 299637931 1250 299636681 299636683
    0x20303070c0e04050d030c050f0c01090204020a020303190c05121e0c0c10050c09100e030a0c0519030b0a0e071e06021e06070f0e1002010e0d0809060a1d 67
    0x116400902e481020801440204041001940740c03401c02c42c0360410545448942c010281d1180744080090180c0115030710070940820351044070f80c41e034010411076455020100c0030391250401c903034089040c4a111814442141c0320b00030120b03205401c0d40e4541c5064141e15049090b00e0f00586041d000001c03d0310502620011200d1060050750310390041510340503100f00c060714200084100070802410a800d100c00302c8180d509440411404840c102041c40c07c00d0801c44541140c807107502d03414032648600c94140020302c1414004d82d0004e4880562100c07482e00314102d4005503200003003c00082c032000170f060140300d910050b0a50345a40c151005955540d1069540c0700d404804650f04051442003005240c1d01002190007883c6d070340d040c2030070784c011440d6003648038600101402c003480b03600c400380c0d090584030b203142d12494807004000c0c10054003031001c024020034003250404c80360b1051051403021035015401b018418289500145a180d44103404100a0b04030002d4405d81780840300110380c62444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 299639181 1250 299637931 299637953
    0x60809030c0f100614060406260403030f0606020a11060904200a0908060c0d150b0313020114090307050f010203120106020102180d1a04080919080d1e0c02030307 71
    0x2030ba03100910030315003100c2c88402100c01030b5000341ea007070300180000d6141340c45007401d607001c440083c00c045401040c0002c00c0880000507401008541d17401100308006c050300342c1d2110f20101650501081640e48401c4181d0b1303510800c010150556440320800005807810790b0041441042c051f00c08540070a036030300c402d2881d04112100c80303248400400c1020764154052010030007042580d0090281e4144082d101c0c3d15407240000b20030815450301a880c41034152051500018410406070307a039a031401600f0280394181e058022400102991064241291440142c0310380e050010090881c55140104000ca505150480241540414048010b0300c40003c0412402002d294001681c0c031030440c201c2c4090034450881e058414054003100c06d0201f1400c03808514812580c6041d442170341c0315400e01d2081c0c0d01900d00400c1d480201064100c40340008003189000301c034000c608035610075600385015111210146c04500d181c0880e0390881c8100d620401c44540314600140590b0714020040c1c4070b40b04440 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 299640287 1106 299639181 299639203
    0x109050408040b0403050d030b04020406090e1b030f01150c030c0b15061303020901050402030411101e1d18150f060a0c1505060a060809030c 62
    0x200103141202d000d00844008140c503103940c1c1c0b4140f961414501e0480c0700103400d10b4081c02042c107107070003584c0613114580c40307200e81181081c04d007c1908200a022038522003101c03080c03070650500b00c0d0045011b80e5049000200c03540c14000c03010844e08042d01004100806401d074540031a900803034610401d0b40c840c01d404000d0b19424140ca40724071a12501d03991164000501c840c440c020824251700312482926814030741d82e6100c04000c105d01040f07038003811a4642c50440c00c100d2400203501300c1003440c0c81c200041d42c01d418510329103950303025484040c049034108850328a00c11040441400d408001c87d01c1558440340c040c0381300b0024001400d100b40d52640e40b00c040c480380d918046a00e80c2d900010b80340da80c0301c0008200003444884007210a07035190040507003200560f040c40c0189032040c08040c0041d0000b5142403070483ea035141c02041e81e04680070901280c9489181030021100c54 = true := by decide +kernel

theorem cover : BRFrame.Cov 299460431 299640287 := by
  have h0 := BRFrame.cov_init 299460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 299460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 299460431 ≤ n) (h2 : n < 299640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
