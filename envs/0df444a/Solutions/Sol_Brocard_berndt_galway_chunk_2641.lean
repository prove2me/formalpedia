-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2641
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:18:48.807248+00:00
-- url     : https://prove2.me/submissions/6ee19694-fb8f-4393-a7e6-70c85b9d3ff8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 474820143 ≤ n < 475000000 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 474821393 1250 474820143 474820243
    0x20307120903110f0601050a0b091c3807030b0d060609090c08060919050c04051302040f0614010e0604090507050a0908030a050f0904140406020306150903 68
    0x90309014018004041c120036040c0244400d120740070304d000424604a40010b480d200742d036031030040c03111810303008540f865911054144070014440041c0c82c0115410340035400d8003014684030511004c0c0800ea032103507148070003031100c8041d901003603031406950701c00328505003c0303488035403c0002103078600f041c04000c120794a0071700f000c640078005900411354244107c40002d801910313540510341e100c008891900f040e41c81918105914507290089130fa035a0712482c101c85203484a00005010b4690413242c0880b040038006040741545003501418a41c800300090402106080c000900cc034482c1c01407181d41800500788006c6c08030f84402c4112402088011020405030502800c018a00d5101140003c0020011310004c550650040100d0340680c8080d192145460000440701c0a0790f001440c44560095031522001604010f00b1281480f03035228840059480c5840001c1202a107080b01c9140d000c88820b225041c5552400119071081c28100c4071079868400200c010796440c0461002c031012a450a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 474822643 1250 474821393 474821411
    0x8121509240402160f050f0706031a0f031b0105091f0e060307170403140d090606060f020c0f120a03021b09060907080a061e031502040e040602030712 66
    0x51145000482000e0704601c4071120a08410002a8014901401c0f800900c0c5000d0800050007511440c41d003910460550741c0c0f860001461508040155001c040860748880f0000328689858140703014a071030440f130070030740e500c07448000c660707203420490301070000072502c00d6140e41580c0160113540038200002c200c003007082c998040340707800c1d54050b244030404914004010310544c6411419248989507d513123000e50410100c1c180d12803101e0141080d0240f0424444080f900d484c441c000b0401d0b0000c1500104400398035182840403104d869208008100f2002d03200151203031301103860120303407504036140d0746c00402d0071002400000c00110858594451304468030105600400c03008100c2c00b015840d810303032244c001d0501c031440b1400c50742180d000c841c542c0000d9000707002e00c0a69801c022208000100c00c1c1c0c51304110308030450303448080d0243d602c4040d8200200100155420f20b408601401507040a141040300c40400101800050210b40c011001903403140c41441a40c43d04c00513480c080c441d03949 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 474823893 1250 474822643 474822661
    0x10602011b02060f070201390503040b040803041509051c0f02030409020c0c060a021506030606010807030e10060b07060608010b0a1502150709030b070819091103060a020a02150408121509 82
    0x8e41401c080d4500988280c0020542d80a035080c1e0703100e9a00808030041d2030703580c1e544101242c0d00062041300d440309002c80c1100c0d165094071840240320305c01d0700103081c400114100185440c9080c0d07848400c024040810100c1243d0100c2074804480030f00d0710242c1c641c00e1104080342408150f221003a088400030545c2103195600050301c121401144c503030304005031030b05014140c41c0c1e60f007100c14601082c401c00100318603038480c0d03200c000c441d0951400e40d1140c006280110b01a81c0c0036074071840328281d02180142c140003261054000a01000c1e00801c00034426101182201c0381602c00e844454620342c2c00b0141180c02400710a07070103114280580d4051501020150841455001c02e803461028070b40040c03500c07802030960034054402c203412311003a0744540c401c20b805454000c200b02c50f40406104240c080341c80030001c00d40075250440c000b60302c0c2d0034a410b00a01c2d03c040c041950503200300440a200200306d5000840e04550020903045446584a0320035003002c92481071400c0c0c0112180c001c00940c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 474825143 1250 474823893 474823961
    0x9020f10120c0f08090d08040f1a071d030a050601140a0f090606270b090a3218040204090303060803033405091011030304050303010602011b02060f070201 68
    0x45a40e1102d0009440d05121140d80c6d009003400c850100c0c0b00c25010034003203140e902d9040d403060710602040c613150003082c00d100310000c816951440456071201074076500540c1610400d10012082d001080070407032070740301c15036190790601c901c0e280e445841c85251820380f04c04440c1c1000d801d202e0b845082540e41c4400581c02001948500e5001031008078015005e20108007822100d1220880707c445100d0826404032070075407000c20701c03540c80071041a0001c0e00784d0700c0e0382d5503250951126001841c200304015140d60407001c00c4c2600340c49460606008614100d0313042003260419010b5400059440441c5030990040102c1c1d0807800c0c0707510002c010401da414030700c91110f4a154000c0d44903c928011181c004a80b004c14000c200b01068007480085014101400a034002e5015494004660b10300c840085007180e100303031010b65144d00000018800d140d02402145078bd48140c00a00f100f00003d140c0c02510703141c018000740130203040301c0302041910f4401d401c11400c1484604031400c0780a6070610600b499 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 474826393 1250 474825143 474825167
    0x1060207052b0f020d141e030a0e0a080a062903070b0a05040e0f09070806070c020418020402070c080c030705010e012d0302130b03061011190c03031209020f10120c 72
    0x1845a4554034000e007e4128503140c22011034001076040a010810a0741d4030104203031199000040c0d180006a510010400128034602440c400140000110340e015441c1086620f24404001012041c2c815900e000441e40c0491b117800c003005448076902c1808550911903a0300820040000100744002c0080400289004004200c11940b40e1030381d41e00070580b42c082c1110840c1c00714818012100250401c0c4d0000819003c0d901d0418010000741d5000504a0700948003e0351406034928043c08030b0803007084200100d980c220000c209140c94500000c260906817000a030401502480340c144507041028800b06080740d54004052100c1c090000900035084003100141d0b440300c41c42d0004640301090200ca001e024090070107040202c0c80c40781503609049188000c40c0a00c42d42c2000048400105200d07072000b4411b4050321422450f50600402c401110140a80c00c035140100d4240183d0358081421003120068602d130300080441c140c10b4a0101e22894682d0b240b50500d00c462205903845450710801c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 474827643 1250 474826393 474826433
    0x313170a0f0306030b01140414010b09032107240e0606100c0812100803030c04030b071d0906030c09090d0323040314070210020601060207052b0f020d 66
    0xc1c03206044021800d0350a280300c085d02e48040c505c01880026040101461a00405880030804005515170145040d070b0990020401c6000462a920946020f1181d080c0303030031040b50030000220105403003032279a00c11160000e00071181c44001880c1d8081c411030aa0304511607910810000305008843c603194041200c003240718150710740b010a0014003440c4104111504240c161b420090210689032076200c0103020040700c0c43e141000041c0c0c1410030002184502049801580c6032450340c64240c61241024040005004000c6482c109040a50b022214041c400301c601003e9078945501182c06c01c1080c161080c3c04c60911030800001c0c010003d401030744c0060035a8100b0480359641d4244a0f648c0e510340070050f01a900d0f5001c280440c0c4603001c0803114103494054180f0740340080d400500d00800c2c0d0214000580c00c5600100484e9805206042c0140000d07a42a4018074190130b681d41d03000207001c1c91040390300078007501e00c0034010301c045500c0a195002e0702c0100c1d01c400d10b0030f0000c0500400c100041c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 474828893 1250 474827643 474827657
    0x8190e0303040303080f0c0405030d0c061b0c0f02060408010603060209030606120a0318050a0305010507110706053009031215010f0c0318060e190608010b0313170a 72
    0x24050400000302c80840b84c0542d5410660346030f90501e030180440140c41010b070902c045c400882c40f0383c0c0c28485032120f980c403503c6408109040345424401e9070f011142030340103000b214012030502c580108c107280d0b846502030100c03290042c1350310000c1c106010781e4125055542c41c02d80d0100c1008507d500500000800301c0844985035a050104200b0801d02c1c01c0040c52a088010315800280c011040b94611080c64204581800d403100c000c9000a901d9034410703030f9641c3d140c9050142803600200c0e40010b4140380d5001c0c041280c20f02d50054800d104a01c07400e200301c8008110400c0b150301d1401411510507a15940002d2410b00703024540d03403a08070206254001c0b40d12030100d002c0c550082410000014180c55200c00720400c039806444046040343c081d82071145000102082c4006111014064110f640ba1042074516030414041e4030710300020707803031010800580188410341e001600c00b411650350260f1140ea80d40c800c2c9141c1c110300c01d410b070020129480c90300a80120050500503102d4a03d903a503440e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 474830143 1250 474828893 474828917
    0xd1206060504030221030a0804140a0519080405090406200310090207060b090703060f0501140f0c0304030c12021309110603060402090d050c03060f100905130819 71
    0x404644052240c040801e00420081005042c10076003107490354130210000183c18148102c8070b0440d0700074030280d00003d00300720801c800c0054018070060032000840051806410b40c0d5141551070003a40c2446100264030f2078010200112042214041e10b4080c2240c0c029007007624101c00030340b4014010320b0016141c8010054001008410f41c1d10402203100410300852a100980000750b2125006031f800b0f54913500344242c1511000741d92070252140c1d540c0040c10303510300603402000e240b9603080141044541c08080741400700780e03c10b640c0d0149038424140e03520100c21a00c01d01d103100365400200110010140050704003002600440b00600079521103c1446428a18404550844000520604091030070440c80d051841c05590304c170901400040c0385c42490380019070001c461813021a401d0f84a2074013040319080c2030121641003010307400016054105441c072050720030414000d0f44c01ca0750f80e4000107840151548612a10140c1110845076580300034a4a48001d084000003000451110701c0030b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 474831393 1250 474830143 474830177
    0x5060105130f150e22020f130c0e040e010c020a120e0307060201021e0306060d1e060b0310050f03030d0e030403140d090506190c0c05030303010e010e060402030412110709020c0d 78
    0xd0349856500d9445c5d090001a0303401c00400c8a590804103030003100010740001d480396223100315120021a0b44841c10740d90541d00400003a0b40c5172205d000301d140d06103480840380c5500001e0302231080d0b0b800140aa01042e45031703000c80d50003514034a055494450200300090558040d0300404076032079040c181003c1c8201c0800070341849e200aa8071f407a0810010000d1280c2000642c0c002d00220a180519941c100050354500058507415041080c44120020a00201c10b144040380c078001c00050341c4a48855015800280c2c4034000c100980c9203a40d284c170b07511040c04005004035009141e21a0103c2908004201404e503914004810b0384082101f01501043e54a4088107440003881828040e41e6201d5205401b10b80203034801030200c0d0f55104c0940013081e142e406202075800b0784001c500d9030030f00d58500000101100b5010b4175043c0528410400e000c081400b042d101003034440a401c15032101d0051030083e500c1c0c440a680031541c0140b0204a094807441c0104100303c52525640e1458034403040d0347d10b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 474832643 1250 474831393 474831421
    0x3050a09050d020a05130e0102130807210803220b060103051f091e0f020702010f031a0103020c101409070605040b041505070b09151305060105130f150e 67
    0x1c007130341c0a01040c0c0b0421181c50103000c43d4a01060f81c0340045020710418401509a0b080211240a60545070700240680b0104000c84801440d02c180300301d134840f100d000d1004d020001c044d009030152000100048200030b2050f888100005080100340710f000c661300742214104400e8503001e0009040c0004150301030070501081203501321640030904070a00d4141c000c0c00800100140c101c2c4c2d030b1007200103825070710143c0c0304007244800f43c150056900c8505200041041007003100d0700081c545050b107000070407800c000c00410b00e18002e08006a44240c00484c580c50304801c51300c8021124103003030500c01e010408100d89401200008216080300f030303c1c1d07507043d210340c022030003103d200000030f120401c042c000d150800c1c00380e9400713814031600d00f902d41d445000e80359008841c00c10495104c0c40c400c44c00b0003040030101c4e81c403502c1807640c6110543c2035550140c813000188030319072042c0408560030700d40d1841e9074455500c3c0c42030604200007420807044181e0510140e4400c03810000c0400c400504c0340c220741c0c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 474833893 1250 474832643 474832669
    0x30605070f080c161a0403030c020316020d0201090e04260f250822050103020f0717040b0a02010e060a0207050a140a230c031606111903050a0905 64
    0x1030700e030300ca50b40c3c1102c1100541c1000000300360443c510411074003c1003845220390b4076425007442c003079510314080c10060255201135490100f10340c001c010340040200351001d8505c06940c11900041001030324001200e400205401c0745504d000319109010410480301c85a2418001011803071405020100d1807002d0340c001c00c0c85281810707204001e409100360700c00743c0050140460701604031000c0525290f103449600000d0742080d0700b0031250200181503505407403c500900b42440c0a41c45c201c09200848140c0c020171750000d10107100c102c5c04980d0000c00ca400d60300500111404291101c0c0d1f80720b0700a010b042904401e4419000300400303c2e2000403240201c480c016004030003052020380c0f0350f481480021000043c0c3c1158002c81d00c04200180c4042d4000c0312016800f01c21000611116050034203224000072035511036070045401e1229808030403680f42c110351140c1807a5500000c0c0410346428906240543d040e04005400190201034024001d084242013650b00c1c281c080741c50f0f10912116187d100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 474835143 1250 474833893 474833897
    0xc030e0406060c06090f0b040803010e060a030c06050306010201061e050a091a01051c05040f02010f030c08060f061b0106030c0801060b09060a05160b0105010210181202070e010906030605070f 84
    0x10101c1d02003801a041040ca05d881040110014822622040c40300b0105440c06c07540500000010840c1a00f21221a40c12600840b15209680c0c0b840e600d10f01c2ca01c807648140d005124000c40041c04513070027036101600400c0042c0c11136508101d481c09450b1290035500a10780b05422aa0313020400c59011b00c2580e000d000d2130307006900707044900001529150403030a40e003e41402103182d0489050007a0007401c0c005c40c07050320b00b810050311520001d0440f02d042900c0b00c00701481c0040c0c00c0011640002610382040040c0c074501150b00d80840802c0f840c2c40380c64240449001c0100d00416403041c1507012204803405040c00001c030580b15101a426a00c80384200360400710107114880d51031411b0001042000c0d25800c000d4a04010400031b0510b402c0e000006850042040e40100440d5805000c1201c50040f141010001a2400d00d64160720840c010400303070030610703250001c001c50b90080141d0405010500031080380c40d070b5680701d114040c04081c003044450790f05243c0414034440c011303a030b500c1c40e1070859 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 474836393 1250 474835143 474835157
    0x309011404020a1e211a04020904110609030303420405060a031a04030e0117010b1308060124050a0c02011d0a060e04180f061e05070c030e040606 64
    0xc00d004070394501d080071203000713441ca140c5000240c914120b40034100401606225200c03042d521b080888100a400445a6100801c1c104001c01a50b40d080300a500c1a0302080081a03801c00c100451154082c1241403038040c0300000501c414050000c2c0484d10241254503454103c0d420340390b03104080603418403d2a401540f10505948a1400350401c59200c03030060b01000c981a980d440d03001105081000003d202804081400f0515500c50b8550b1a01442030902d8a0b4113414000103240c0c00105210ba01054a408103002d114001c25411036401405107104075122542c5a1003035100c400054071181c10304030b03149102c1e0000e05000d9410741d0740542c46030710390000309202a0010344104444c6c8000700080ca255a40340f00340e903610001c803103001d080c0650340d41d03405120714410300003250881c155803200311200c4590500010011820000d00503408034010803145548444021621107070843e0000140c20403040020382c030fa20824581c1aa40070795121004070400109000c101c4c0e0f0180521400180c00d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 474837643 1250 474836393 474836399
    0xa06050604180c0c06140f061c030509040207050102120f010504110d1503170405040e030702151b1b090a050f2205071205060124120e060406020309011404020a 70
    0x242c2d40c000c1c0d41181d66801c0c0f21109203019501d9030100e984e02401803150005041c10b0107071138091683c000303034450b505a072495021107000040c2d0340e4000428070300600b00800054500a1a101c90f01910980c560000083d03458400100755a1054807044130500e01c200301080001070985014064030f11007003500e4158625250411100705c025100300d03c084e00c6902d0612070300000054007e2091044080b40142d40b545a600389800c03c420b4030314114103840c0743c1d0f00521800d4007681d114804e0f581191000841c5595882001044000728a851240718006000780d0025a0703148481c4080b00c50385490499800c841982c0e5560342004661b410f45d110106107103400002030003c0f01f0511644015902d414810480711407a07034a15140c040981c00ca00d107411100c4141d5002c02004220030f901501a44010780c4a420301c0b10301400050110020003000c12000004c45143c00019900c08481c00d004001a00c880b89804d06112003e07510a4517000c07010741c41c007021090306c1103030703084001d00559004149916480ca = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 474838893 1250 474837643 474837689
    0x11010807180e01050310060b032802070b0f0a0c021e0a0b090309030d020304060507031209060903030903021b0f040903030b060a02280206161e03080a06050604 70
    0x110040100051210001094140c10707510105180141000260034a0560514081c1420445908100304085040480c1801030b000d207201600e600032076220740c030401d5011140100381d400c00d00e4025031403038901c0094000c0030305c070045056920030000c0701615500d58850f18204000c81d680c4141d40401a008004440c55040041d1b801801c010040c1c011a6110346103901c5250703104c3d0f829140c80d20300b036000142002e8281010f1003031080d0407840d40007560406140400c050002d00c24041c0080c00c111200f144a00c85c4241503000700c7c901d80e00181c0410200743c0907d40070f170051030092000e0b0054454100140c000100810603000310980c09080c4105001000e814803014200140d4114103264035040600410345400002d0440c24145034010301c2808100f43e5214031f805d542172522258588a0a440400750302c4400484503c030101d1612013111840d00c5c101511081e030500103022a403002040d904080c140c1c040031182c05100c51900c2004040e942e03008010280c805c5204034204001d5800400329054 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 474840143 1250 474838893 474838907
    0x50910030c020c03070906030209070c0309060503041e0b040201080606190c0203250303140901050906071401110702090901090506040f112e0206010515160807140d0c1101 75
    0x500302d004460b41c2c00040740000f401d211103030b0002030304241d032400d04009616207000c856400034010b0505200c4e82100d518010030602e00c0380240002d2140000c0450304202500002d00c1ba561000351801e194400c403071800399858801078405031b00084020000c1a020b1400000303e41c0d82491411900386031ba4152101690654071480c0203903894000c207d040d6002005000402000c00003a11021202604501c2c0241500c41088000360104405009000362a600481200d1005100302c403401c1c1c840400740b5100703030700035040711745601c0303a500300286801042c40080242007040d1080702e02041c244d1701d104a0314226049000094000c0e400f98000c1404602e1908115000900611502d4003031601440400d88514003490500e44400030080081c10a0b04074140c64140100319202908241d4549400640c0c55203105102c072134941c070006401801d4280e20850f02050f41d84c4200415140d640b2410030408100207c10250742c0d5029541c1ca060550b84120000050703188c0c420500f040c0a030036800119640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 474841393 1250 474840143 474840161
    0x1209080315010f020d120f142203020c0d08070c080105100602010209030a020f180106050307030509012c0c041b180b030a0b1302131418150103022205010f05091003 72
    0x210366107c6880310010603501460540001000d14181d5505080d03821401104010f60b02c400d100403940000c000195010030310700c000000071961248070312141c0c10012818840c1d204010001c60086400240040c01034008503c0362902f00007140e00d56542e041c0030b80c00c0c2d100b1814080d42c507401404500300180381010350016050405000740101501c900840d1036421400e0300002c01080000c010001c4859050269130f41c405521002400700000358440c07079078400c4038040d0a50207024401e0a8051424040200094a0800030700501280c0d646160564142540390842070004800899000c006429000014121740c0c0400d0043d10355980c4d55000c00050981900c9a5031000c07100c0d549014410441c0003031f12405240b111068484e45c540384120345203080f5001d01d14003950600d50110010640307140c40b11b5203c00f40c201c14140d91510303200100c000f0b20a90340c1102075054091061a201c1688002000544200303072100c50210101e504107031a180a040c859a500c00d1032039503d078951510071307040b042039 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 474842643 1250 474841393 474841427
    0x70e060102151f1d1f08150a021303030806090a05161b0c0603140f090d1808060c0a090605040302060a0f020109060501080c03010b0f0109030f031209080315010f020d 73
    0x502030f2138041001c01038041c1c040000648202009000740f40001c0c1ca5500200031003404000045464a00403d0311041d10303040400a02c0c5a000c00591231400300d404032081c4036090204140481d4036450090034031740081c3c4446004a51203000904000510304c01c0070300400c1710700800c44980810308000c80340051544c0291580c240000002130000d4803122050307001e80101d45010605409404441400e408010000d045480f00c450070321980d00400715859a16078490300c0d1094120020000d913281c05c84540c0d109a03001d01c00c4408103d13503010300c5800b421420806c0e5440407042c0d56514000c40e110301450001039400f800c20090880000e01403090703110004241e00000c07072460119184c2a0498109030300090180d0403141d010004d51500f8400c0940d0034a0407560b400c41141c40900090000416000040c00448070790036420600d40242c0880c0ca0084d8400c9040c000043d83d40b0303080d07555030801c4c6c40c00c0c44503502c110720440042d8043c007040c80000c2119030080601c600440c130115103911384000ca0001d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 474843893 1250 474842643 474842701
    0x5060f0319031815120b090a090602040f0e0f1311210a0302010b01020705180f1b03150418020904031407080f090102070f0f0902072102070e06010215 66
    0x440301d0a89240040140590010300b03013608880c0802030244100460844030851406d03100002c19a95131540c1c91f000300b5004400034480e811480c100c00203108907000392800102d15800000c810300c0c0130b0b500c1440303000f145010580c551515000070403039541c003401c0281415100082460207042c40900600082c40f5803107002c650400c00c07003c903030600050000c1903006035115289008a541c0401500e4000c040580d8028021210075540d1a9600009403501d8055808100400c01c80c150201d00385000c1d100b80c01d81c02da03a07810030301c454250001807044550700560501c564042034900d05504150703415009420044d140c0e50b1540e04403120084081005007440701805080003042149000d040e1407440d0029459844144c00d0000e0700c0c0911603841001c5100426001b408403000c40842a41194803d000c0540c840240d0f10b00042c0045090000c45070018100c0d0910146641c0040c0310021038141d20b142c480c1c15190038004a07100c00820745c00c1d1011400810120b540b81b03503446045078046101d01c071101 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 474845143 1250 474843893 474843917
    0x60203040509070c12020f0106080309010207090e0a05071e060507050a030305180a1a0f070c12031119030b060a050901080c04090c08100605090f0415050301020c0d0305060f031903 79
    0xd242c80c0c1700070380c0d280140d003c01410308055109202d501c01401c4000015400c0c1b40f08800003d40c0e41e81345004460740c0f0358840c2c2510403611810400511455840300070390b451180c481610300c500385100c4003645048850070740b0000301203008604403110150402e024004a0545440c2a0f02808005e000c1040c00010161380c8010b010092100c03224241c450400c110342c0030349030b19007410b84501c090204a00744d01c1401c00c0c030000940100b00704001e50360181c060204030507030141c00d030020852944101e4030640c0010319440216004c400260309281d15880404c40524124140240b80c01944c0c15800420810402c51400398000c0801c250b0024150020320324064803a02900c080d10405403046020620810030300c01c40d51741a100b4080a02180d1070901c1c18000650000340c03003000e0f03614100340541e540704001103610510540307a202804028009554401c582074443d070707448042904a1001a28103c0401d1241c03410b1041680c00b2840200100f540f010202001e4031070341c081c1c1c2011024011080960 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 474846393 1250 474845143 474845153
    0x2010e0d02132405010203071b0902030a0605040507090f0b0c03040306020a090e01060804030c030e010c0204110309121903020918041a01090203040302071e0e0c091504060203040509070c 82
    0x10601c4000e154002c528030070030f0040f461152255014507000030030805004c0c00146d900200707481301e031900a0422960b0712800c0202d2400c001280e0440c0301c13218000010081c0051054210004031001640c0c108030341ea80d400d02c112488840e80c080c1e5a41c40034110400c010003421031001d8070b14900050b05581c9810f55960f1402c0880c1d2202e0f09082c0030554a0100b0002604c00d00d01d400e00521700d03800d1020003460680e40041404007100300003014403124800c4101c040e40320380c5071864803540c0640100008a200d4010740c03c942c004071a283c41d14071407a40ca43c4115007148069030344250500100700024609000160b003c0d40103507a001d50010408983c0b02c40e0100000c0c0004c2c01340f8000d02014101650240d4001440745050704030519190040007440f002960025512089608034205281d85081410b0503e154140a03400b0350b214211900c24051030ba14210000c01010703034101c4440d85a401508800005070069100344000342c0c006000c200114201212529403005252030802c00b181d5641d590 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 474847643 1250 474846393 474846409
    0x40203010f0f29070f081605070510090302151309021e1602091005030f060f06010e13020a170a290d1106040b040b07050d0503040b0402010e0d02 64
    0x891a0707414a036081010328142c650b80400b0340510300d0414042c20080c800c0c41c60000c0203046510891000040420a0040485540600540c40444103640e00112002d05204c6080c0190960307883c0600320700000c80340b801262807941410152141380c486465a002c1200100b40181d607280100c0c030030014a000c01a0101d011006840c03000070043c6c4a890001070a68130f08150103195507019410040840b91901d007100d886540c51f4110381c1010181e460680141a03580320742d00c0f040d01441030b003c0011080b440800d04600c1000b0315041c1c10071560316080110384001c4000d03074060300071410b00f48410441c5140d07001000c8101c0c075400c0c48821a150303903040d800200d1044800071015580c0d8118a2040d001585002c06441a982601284003040000150340c00004001c018180b80c81e6060916a076122913050310010041c03404156121592060045c0440d400300000711460b000b030780800e61216005105581c012508880008940d96599006440d100e074800e4640342c0c02a1115540d000603a00d03182 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 474848893 1250 474847643 474847649
    0x100f03020909011b1707020111030c0306010e04020c010905010b0a1a0c012004030201020c0409080a030b010e090103110907090e0a0902030a020a08010c0905030c061218060705030414060f0c0a090504020301 90
    0x2651703207031603e000c24045852a0010300480c01310390600d0100100e0303038800380c256600320780c1c1c440051340c1e20b8903241e006035010303501411141d801c540086410400440c066002204090050000380040701d91042000143c56040c01000128107251110881c41c004400150540400d03200000501894607000c042028100c0154803107030120010b01030085590600007010b08100170340e014403641003207590381c05103400f88081000405641c0c1c12080c446030710406c0005c101c100041c204c4851942c480c01c10011450b45008018000c0004801254019109620240032603901c0103100d80c442e12180301c400040c000fa4002a84d1600ca4400034070056910a4041c500420040c0000502042502f4010380035011507032043e07110f60017400461300d5984440701120800301ea010000503031503581540040288440d0340713804401e0301c6078004008146800400840c0541c1c007075000e00b1700c2c5a08076942c40da0b490b0821160400203400000200d06416032603030151855000368203143c0e00c000d0302c40020508a802c02d82c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 474850143 1250 474848893 474848897
    0x3010624020f150106030b01020604030c0b062101020301080607080405070618030204020310060f0509131805030d020304150b030d0c0302010225060c031103011707051f0206100f03020909011b 84
    0x360040180d19014031a0f47c0d01103100b03001502d00c03440c0c00d4a007d041e05060b41c8010701400d00b0000024401c0d5a60715114004546413240790080c0b008441d0258000c0d002400380140c0c0b44140c0c40440e1115000344016886554018000d241c00e500b07000044903108603004400341100f034000004001a81c950000e14400c1340000e40072841c00307240600003084040701500c602e041c00020044601952180810f003d12000c0c9058081501207400d46401004e80f410300001d0407134040403410208a02490b002540914050000009072445c01c05406084540c00da100f035625034000a501c0203054020258000d002e0b009000040c10480200f60320b410914840d8641050026855043c13401c1000324461081c180c0c800f4030f020012403030104e130820401c0c44180541d81c280c1c071004171005612901000071001070000903000c1c40340d070b031481a0001c401e55040d400703507005801104005001805003a00c00c104641c0c500d140b01042c1d614640a01490903405000140e186d502c0314140032000340d03400740c024818612a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 474851393 1250 474850143 474850183
    0x31401020d05070215061f08090c06040f0306060b0301050a033002160e0f060d0804050a1409090f030a210606090611150103030f0c020301050a050604060503010624020f 74
    0x11703250440340d042005000a10903260040d00d070385003481094040c80d00c8000ca051074503207034550700c0f2000d02c1c200740403c03202c2c0c3c055000200440c0d051a081c0440c070445c5d00c110000d2003125180c0b884416140000d000d404d0b04061049400c001184080301c61f001005210169008085803000601c1c0b0361450204404015a20610b1b4010300b60340d1074182180105091000c07030a2500700303401901d01c0c1c2c21000d040c0300e00c07405814840000f0b02a49204035002000000c000e030640e10b68078801e80849184c40040240308075400400202a000c4c00700b0503031408613102000d0742c600f030440c8106548035000d080c5e80130400c00c48180c231810802450301c01d00300584601e850b441410341c680040200141191003881d181c640100b270a079681c200000100c1e6040d80d0f8141410440c162980c50101c4401c01e06000203075240d0700b400207001d80030140c0e0380301502801301620103111304c9450300d051500340d5840303114010000d0f05200185540641d021896031f0f100b8040d1060302c0150282c000101c5c50300c910300307182038210050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 474852643 1250 474851393 474851413
    0xa08040807060f061a03130f0c090e010b01030f141605040512010608010e0715050a03090818041112150f150a0306051804060e25080d05070c031401020d050702 70
    0x48606604403410a24174400e166140c40546c0040b140c0920030001e02402d001c420160820075109500000b80180f000704120814151059501a148603052180030a00c7d08290b0f011000e518000e441111600c804003100c25150b50354508211581e030608002081028400804c40713075030700c2c0003000040500d003002140080c240342080c0c3c02c642407210645050307802420104806074025602d5810741903241001900d501e0661016405050004001131000c03200195004400310420445241d9078015503041040c1201c0446501c0c0a1044100725400494203900007811a00100d02c003034807803c0003034100c035840200040070650001c410009910f61040c0071a55054446e0302d4800c0b040100822101041c0003030b0418043e150b12600584040c088030340300c5a940b4640356040040040240149908141c0c080c0c5e90800b21280c0d130710f90700640b16280640001400c446124005503880d076a00310203051001717440c6a8601423060440751500407195002d00c040c4404c00c0203442002c1c401c03a1190054422121 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 474853893 1250 474852643 474852659
    0x20304061404021e01020a15051602071d0414060c070308130c03060e2803090801060b030c0d060b040e06100201060e0606090a030f0606030b0a020f0a08040807060f06 73
    0x640c1c06088040c4420010800503030380f801d41c035040900381000400c800d101080d00403401c1003d0000054001324240054000144e100d5001a1003585070b1269002034108804040b0b884028030b01c1a04204245c00c91841c00307019401c18000d40091080404211092481040d2800d0880c102d5030000703d0800030403084141034100034000d900c07040101c40b0030301d00b1041c2d540b0740d000c030301d814000a003501e0740c0c1d1580307003801180c200a100220440e440d4003041e00d002069801101c0042020124002010082c3c00036440e0014010310040c1d40d078213052642107685150381c0d41c0762900501d90050340151076280c00101c1c000d002c402840030b044080741a0180c0c2c5000e6003804000c0f50000c0c022400c683c9031640410202c00f606040c00c1e000311003110403607920415100000c0300c0c5641034002400c1c28400030710034020040c003030f0310038070840c2d11810840005984030040d03030781280280c854114400301c0c20006110607503c074a000e0345d4424454443e00b801e01403603842d071008031a0b50b071180c0c250040d5100428010740ba = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 474855143 1250 474853893 474853901
    0x204050f070f0201020405060301032910081501050901030b04020105040b0307020705120c0d03080907050603150a080a0f0f080c030d0f0b031209090a0b0d03090905420406080102030406 81
    0x880b043c0025450145404046a01e901c0144030203000710f0004100511142c000102d0386048407055482d443c014104020240343d8a44184100a09803050700035040e44101c3c41d07090181202c900800c242c0c056803858640941c50240101f0880c1004010070005c42c0c48405107019500641d41e950003801d255041c54244919184012150320850780711900d00f007490355410005c40c0c000d5a061822100d1034880c05401c61a10300143c01c000d611000c08030403c810310407800b003d1407a8410031180c2c00301055907000c025483e1005001c0161020702013400030000f00303008280190001d442001940d1406109403e040c3c103640180103020085511a00d4070f20410701507010344a0088011000340015542d4032076030750107510a11400394012011b580019510500d0f56010f2102035001620048000141e0300c4c1c000c1075014a07000782080b03e4038001c003258407080e111402c102c1e01030005d1800d0318107074800c2001c16040003010384818081d0506481600d03242e211802541d00904c070020001d62a401c1c14903025042e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 474856393 1250 474855143 474855167
    0x30b101d0d0b1b09030f210c060106050702030c0d081c060b041a16030c05010c03020414330703090b09010e0105070807170403060c0c080d0b0d0204050f07 68
    0x80d100d066004002c169404691034200c620394500d10b03803800c0c040307200c50840d01500d1082030b454095045440000000801d11405401c1c0a0007003090030109400ca250650140c6030070080983d000d08018007003140070b04014030305e00c0c2c0001e04480f01802c0710000039100540b017a40032215803001007805591502ca01000301540003140e41d052108601f0715480c81d1840c01280300d20103e40b10214140c0d009480c004084a0510340c401010444009040c1006810000104400c5580c1d600c1c180700d80800038840d1094405654425000d045040c003208200105218944183c400354040281076050400d000903079000b01c0c1280310300e055254070b01d50501030290340c01035001d070300000c0f010420f10549030b07403140d1440800002420b126803900d62905101c109401034404c010b01803000361061140440880020303104482c40340b03200b07215002070070608032040303200403200514540c414003821880181a80202c81912006800c0b8269031074581c0004064960a40f400001041d1701028482e010390722121604007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 474857643 1250 474856393 474856399
    0x1e030d0801080c060a030905060708071706011209062d060621020c0f0d0917010b01080a050a0f0f020d0b100522080307050c0319080403060c030b101d 66
    0x2640d0700d001a0700743c4400003d12103510071640000c201e00c00340e01940c482580140c10004484403031425040c040d004400688101c400301d104d801281e8044622180b05900c43c0c40181c0d02c2c80e58195083c481c003c0a07105201041b1501519204031190170103845181a2103804100b0b8400c41840750348291408640c060f8000c4002c11060403944030b5510b0218104814491031400b00698400386981380c5030030714800c0380600704c1d83e025100d4040e1a07141e02ca2030344c0c000e445c0c80800c0c4000d01b114000034076003210b2132220b01c58081101100002c1303100d500c90340502d03440000101c0215003081100c800c40215035100d25802c400355030216114011460f03600c50548094002d903954460382150140151884c060840186142030075000103d2108108245404c000c0989808132038850780c01d482c0c241c3e11900180c82150007031007810500e205a5400d1b102a5030225001074141e45000c0c20341e251080540341c0400311a061544503050100d050321804803004200015565000e00003d00d1031035410082008022684 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 474858893 1250 474857643 474857657
    0x20607050114062b02040212010602030c0d0306150e0a121a1803032a070311010507030203071d040b0d050a0506060105190c0213020a0504091b09030b0c091e030d 71
    0x10700300d098400e0351072a60140000480c9944c0c5440040c000c0d20a00b40c0c01c2100c108030000019140360000013800c001541340040d2203515075004000c400b2158103108400d10400e288001c0d10f401405182280d41203180a4108605140c56010308100c83c00041c03000c03200107a9075141f800000c2140100a81c100f21070600303400340e0303502c081113103584c901003c0c001c058901c0c1c0610400080c00807200092050000f2416580d48411007400c001d8540049030810311010350030324000039100d62192081380e01c140300d6904d5000c54a444916001c1d4043d9040c2003141d002940e59400c140540c0e2121507051300b80e4428001401c421000c2d05e00385040c041302410705030500500380200f1601103e481281501d400381840e010340c0c06840e40c00082c2c0240920030810f220b403072001a40c001a180e01038010310a0703611a0100f8000c541f10210350482811000c001c5030001007881e9400e0000841c0d41b01c8094108038009000383c1001e8403040002c00d00750495200c0f0110341d142c42203520042c1420b22203c00e0b860045e0800302 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 474860143 1250 474858893 474858919
    0xc0b210403200a020307030b0906070c02240d050a1509020702010c110f100203090a0b04230604080d0f09050402030405061b0f03040507170d020c0103020307030902060705011406 78
    0x6441c820040c44500030ba090710416040a040c01007000c1c0026540003000c44814a1340c0342040b0300c1c850b0054400d00da040c0a880005030364940901074000c221680a170640840315110030302c1084214242c01001c154130801c10000c502c00d00940500d90246c201920005068000100041d4900d0250ba000b00b1442c0c0c010700084c1c0140c0e03044001d25001c0341d00816400d450415400001d024900c070442842d600030b05601c80203094030360000c05081c400c9410740700c07020500d44501070b00c900ca000c0c602c03401d019005802c0910320321400580014000c801d001d45100e0500d6210240981440140c2e0840b10014071860f16404c8880e074041415070040c00d06440c110f03d5400c00781c540700c1e2100d000904171240d4600704000d0880054201c1c040300c3c0402503100c030480e00ca0400c0e282007601d9400794441c4070340c03406004107103400c604d5020810f50210000ca40003003080e031003030307100540194000a0000040c1680c411070741c000358840500800c50f9910400c000150f03181c541e904074500040150105000d200840f00b00c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 474861393 1250 474860143 474860147
    0xc0605070c0501150f0e130f021203160b01050d02090a1d070b030709050a120615050a12050c090702030d050601020309040609051f052223180102070218130c0b210403 73
    0xc80b011030b0040d032000a54060349c00841c060240d4480101c089103c005032030741038401703c2084980c1540c0309030603902d48e60343e0301d00411900640303540e40031394040b90003008504511000d41c04409490400741d00b40d081251032411090170842641d1021001180c00010000d4055100715800d0181908075450510f1508001303800c074083e60000300041c003066840a01c07880a0328481c5e1800c0041000410342110141c6a08020100d4010903100b00c2e070b40d1185110900c0c003840d080780000c0c070a140700d600550a00004028440c05050094082e50540c0020045c03850340b52518042c24000d014075103c0400c84e81071091044844071003c5114940001c0e006409000a607144940004190312690042e00c10320300c00244000145100014a02107544a004c0104142d00d508051449024006006c0204071129010142130f4400c0e040000d51080994005220300210800d0064200c00c20380ba078015000d425650307500000301d80d50401a0064004103070a6400b81d0b140030110120100340c060020203080c00d540c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 474862643 1250 474861393 474861421
    0x8010614010f020c15040501030b03060f06151c1b0809031b03090d060e0d0905090a0e0109060603030306080c0a0b0a03050c07050d1d100c0605070c0501150f0e 70
    0x1141d04015418403144a8184208100101200300074000b003c0040003150855450348944185800f0030f00f40324004d022483d000c11810721500301c20201c5005540c0b500704110202c1031840c0380f1802c4030800d0104080c82030580034100c4600c400c40a0000d01d40c651120340340346900108060034100304201f0208400d003400070042d01c00c10095009d40d1500c000e61000c0c0d4504600484040f1904030080c2c101b40307000c0c082c60ba08050f0940740c400c820b840310240190800c46100b515801695001140705020821140d1a17034044d60105c01ca080000580c81801e41d204000d0b030382207038019000680c407a074050240b19818441a8000d000880d15001041d1074010001da050289000354000e01d035960000404241b400e500721045207500c00180d61003510040c50241901341120301c4902e4810f5881d060907242c0c00e1802080404045a44038104410703081e64840c2c3c05080001d00000c204041c1d40040c0000550902039a6502c42c590b64007400e00600740080c0039075181041d0700c8080140d0041081c41030400340981 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 474863893 1250 474862643 474862679
    0x4050c07020f190e1e160c08030604020708161211070509040f050601030501020a090f03030215191e05060a052202041505090109050405190e01060503070602030a09080106 75
    0x9940e801084801c03c000c0c1901c40d0a44c000400d9039085400c0054035101444250701200c42240e0219050716622111790b0351000e4105002d000c115030403e207001107404800656400340000384050700d001c51941c0c4004058100d241012180c105581e4210b0030031210110b64840241e06160180c40c030964841243d56418062050718025032811000c07a09001c0d2986050f40b00710742003401c81d0b0720303540d40e442c019000350f0000f10301c42d000a036440d0300461041071190350f480c102c94150f030080c001c0404c00001d0b0548500b0240601d61020810042c1641e9442a400740140e000c100074140d004d50700345051694240c0d0001010244182031444041c442c90361000984103074040510080c1c24800640c0c04818003d1003550005200c5501001d1504001075004008001520342a6689210740c0e580e80700b0302c015504191400cbc004420440c2c0000000504c5611998200e00007400214034150b40d031006c2800c00d001078000d8030041e080002e54104081e005004c05008190f580d00070881c0d84d20b0544020b8003d84000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 474865143 1250 474863893 474863899
    0x7050f0d020c030f0c010c050a0906033303110a120b090f011a03100501030c0b0705030d0e2413030806010c1b08010c0302040f030f02032a04050c07020f 67
    0x10640203400c60403075040c0e42c6078842d0103040301d0783c0304d2001c0340540712a04401c0c0c0200b40c0e5820b080700188290703c180e050b01c003506c400b07880f800c2140381454000d034098216405000d8001d4a000b0030704420079140040c0341003203915160103100050542c24440058228070710054061280300e042007101403c117405a070101a00003048000356250380700c15030301b899a440321011203903090402141c85003942035040032451004808a40f0070f041c1c4405c101c030650343d00344405404840034800c10000c1c00620001004084c0c80760003601e02e04080300071300000301d0303a07041286e09540d840444900014009800081c20702e65091405841c286004400c0c401c00000b5200003c0c01c00000001180103640a40c000a040c990f0080c24410b05841041050502511520501d0074640c01e08610b40002400784c42241e00b44c41c0400d51001040c0e096843c4c5221902d9009002c90b010f12400006c00f008840e6820300c0c29400240300d00c1100040801020041501c03000390280108050412000c070040c0d079402000700e1413280076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 474866393 1250 474865143 474865147
    0x2e0908030406050c3307020f0d0305220501051b070804053105160f1b0812070c1b05090403180503030c031321080309011b180e07050f 59
    0x1301c9101030500e07114884906001c90b40d161242007602e5019034001c62004041244001179444000882c0c3d203d00c0d61140c80e009401580d10042e1051180e00150380c0200704401c0d11016a400349007481a40000c00425075040c4d5665090005038482d91069407502d4007400340c0f00c4e0405403076032265001c3d8410740c8525440788584400c80c1e108071150010100d94203030b401040146140365600002d014040031908514031007000304a040c0058083e40d0440940c42c09951394000100c8046072a500c445d5400c00c09540c004010300c4a00d80390030f45101c0711807040450784d90390403e481c07851030110990a022000c250740c00c2009241808603071142d500c815482601443e020812b489079070040202c00360150406038050000040c1c0c0380c41400c000008061160030300c1c16011183da916404ca1260005a07242030341911521700003000031500c040083d41d0040b0b802c60000030044c0d1000140d4507240c00341c43c28100800c041800f0000b1007078500c07161600504008046410900e094a1700070101d10031200c07aa0903030000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 474867643 1250 474866393 474866407
    0x7150e090c0918090a080d05040302060a110403020105031801180311010537020a020102040f09050601020601062015010603051f0506070303090215250809060304030c022e090803040605 81
    0x20485d060603660008080d90f51911091392100c007802e4125825400b5115902c00b0070f82e10142c520564000380c15441c061760805003180d004403000d81c00503110b442034525041124140f05002c1c480d100882c0c16540c00e0344a4003c0500d0080c155280c2c1315010085070f4500001c108a4161811392802ea40181d0f1300b002a050850701000c24104500c02c1c908107580b407022035000d511139015801003090341c505001038403156568000c00c8003580e00454603a4016081200100501d6009240d211542c8882e01c01c840c5091901c1c4a00600c0c210000200c02a1002180c004110181c0c1500c11603402c6a08500e040e00d521501030502607811700103208140c0200c81c006000410300d803007640302c0c4113290f47c011f04000b41400400340c03485c1150007001c184140c840001d40c080101501020080d01c00f031350b00180460800111070204810707a00004c000340d00348060303c0d5010300160344607005031070556208121080c000100c581210b294070400c01e03600081c440070000a00c4958800021768040703031190702d406590342003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 474868893 1250 474867643 474867661
    0x60309030c05160f090e0a0611070f12140702010906050a11010608010f14090c060306040f1803020615060306090424020909070512160207150e090c0918 67
    0x500c1e0718050300c2802080308a07140032003a4504001219098241c0ca040540c07200700ca8021241010190812603201c10102ca000840396000080d00c50025080103017850000e48aa00d00b440100100326511062217481c00d581d1504100e0107140c0c00111490a4100441d07540082c0000d101ca008040c00c0c0800480d80200725403091603580c5c2d205150070000c0c004d01e90365542040c0600b04000001c145603040c00d008185803d0040060b0744500c00c44401030101007020700c14010180d0018050a8015032070700e041d80f88105141c00755416022124a00c1602d440b80390900038100710016110041c0c0700c003000a10301c1165242c0c0152070308181d080360f400c501d98540e881c0244201000e41c0f1030301400f60b00380518500f92180ca0b4041d041101041e03400484960714550103d505202d0112140d183c0820390000c034014041464254800c65081d00403100c2c00398503011264903403400076030184001421032582e0744540c181300200e0b58100d0071100200741000098400107840e1031842c90601030754030032140001d01c042 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 474870143 1250 474868893 474868907
    0x7060b04150909021008090d03090510020304080310051e060f0724060603020f070f17030c0c01060504090327030f0c08010b01020a051011040515041802030601020706030903 76
    0x4500038111405a070390b10301e1014007a0400000980c8120b1520911190341805214000d100b40800c1000d0301d4040d048240c01e0b40104600070f4203440758030690207104907050180c401940242c1c020b282e6151641740500210b2607042a1f60403d40c042c1a40114401d100c20100010507c0504120b0703c441d1a403140d441d2101c4180150140a01203005803807500c0c40031400d60f80403e0031240c001d0010320801e034075410194240d1041e0f04210b0240c1004000100102c3c01c0c42190202c181d100c2d280c0c8960b07020751669451282d400030703100c201c103407100000c0000c207040e000d1003008000c280076203051103030142d0b54402400203094450100000e103e035072140c00361484202d0601015591042810403a6070003824100b0081c50540922a5150318290807103110307600005d08c142034a540710004059071031400c001c3e1030150010980b4406084400d01001c40c07555074503200d90b20400a64940780752075a01c2d1003603c80210003c820030850b002e104000307000315a41d010031280240e5241c2c2c02c001c00e15145500e821580c01d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 474871393 1250 474870143 474870161
    0x50d0b060d050103030c02130209030613060912090f050a080d1b0807030c0308060f090403030e2e1b05190509040e0606040c090f150e120f061b07060b04 67
    0x190320b0400044101604140d2200285000b0341e0401c0602009112079000ca11400a00c158503a120400180c90440e09107032003c0d01d24401c40000c40c1a940a0b81c0b401c20300c16008a1260116400c40b03000c0c8000311000c242079004190071981002c0c0c07186010201515612076001880401c00103500e04000070700c041c8038088000d517229290715642c00c4207080c010508082207104a00054403034003c02c099103030035094004014001446030800f40c44544c2c0541c002d00f0030800c0c485030f9001c2c90100c030070600c0c1c40d090b40c440f1260318a503805561010042d00a030480721542c0406042c0e50350384d8289010f0320760000540da0072901c0760090100322103403114280d40714040e6101c3d1035441420309803074503010b40380130034828004c81041e40d007032044842118041c3c60000081c007441c00c18501c140c40411502d03016140d02281a0320f2402c0c070401c0c8410070b001051980740004950030581d48901400f2600c2d140802856501100c0400c84401411280350203038024400d00401038000c540f5841c2c880025607559101d9102 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 474872643 1250 474871393 474871417
    0x90c11030414090606041511010b181902030906010b070201030216080c10110a0c060b0a300c06050c010f230a0b0d030807050403060906020c0607020d050d0b06 70
    0x21241c0c0c030b001001030401a01c007a280684031100c00301c0c080f800d1410540342519400d004280302c4010300c000c100c44400c002c11000c0801d42d210401981c0039114203025034802c91446910000c06d00e00400250741041c8039000c4c00b406584108200310b080ba0000c5140e5040d1090031070b88507500c41c0c040c00100c010380689004000300000f00c604800c10064214000d1101c04200420b50300340444260406003102d688603803450404800b00311000078940306038030403d10144a400001140013001000c2400451190068100005042000c080440d40d46540c0d4002c25580c411a0022040c95074504804140b079204038018000081800a1030070320a4100b07440544c03035040100300700c00c0160b200e01814540c50328202d8101100f1001300f1704515440c01407020364000600014211002c03650100c1d14150020101c1007045801d1001000242c04c40c020f40344181d0140d0f0005d41c940005d80c03101818640003400c1c0c2015540544402030b2850382182c00e0702c0740e41c41041c00010f803022200c00800c005210304007070121 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 474873893 1250 474872643 474872647
    0x1503070e100305031c0c0f0e0409020a0b0304050102070c080105160f0e031f0f0506060f090303040b07050a1a13110d02121b2d0f06121906030804090c1103 68
    0x286894034001105c403021155200380306c4152003103003d54001003450034410000b40031070440c0616080030f41203000d21a10183c11a40903580c0c1300c20340781444d00252421203240e50002401340070700440c800c00f030003d880c0b150004c00c8a4200f103400c0b402802c00720103c1c54103105031441c4035000749000c1c805140701d13190f0160646042c1001d588695201e000e90700e10f0492014549811030031100c19034031465120394400341500c0c0c074110640301c02c08060742000e4802681403008000200d084040b81019180b060b1107680148000740c07140ca042d401d000b50005040020b8885041000480d804802013202103540002e039102040384a000801c0312239169950107900001c0450803600070000000b50300c1c2400212481800e034585195040090362100d15000042d005588502680040410360010000c3c02004041e9601100c804001c100c80740c220441d000b1b881c0e800402080194000c191030411400d40c0f026003084487e04651740da204901950041c0030303869680d010a0360200340104000341008480d00201d030303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 474875143 1250 474873893 474873907
    0x614100e0403121a04060b12130c080a060519020333121612030210050606070b01080c01081f1e050405013807062c070e1503070e10030503 61
    0x80a0704105161360f009620340103000030f08005000c00da522040034031412301d030355031141c1582d048030380807031003065901c100344d454005055203040200e088114400d0030041607e2920f0116010b1502000c0c03004110720b07004000b084003a10555950312050501c18011032840b1081e0a650000c540400c81415003045650072040c040036800120100340c0960900700290442d2031382c9526500c02551003008003d44d000711000b00712050b054000d158000c0d03000c1c00c0706060041540b50307485e020384c00f1323400700341190400e40701000305590241c800c5510050205415145c4010744410000750301c01d9200e803602c0c01e400560041c590300900322844000341310007042803001c0d5842e101c40418811600302d0300c1d030311000310302a1610f0490310a424541081d00c105092810518242c8a110160808020074a4200b003a10290301707100c1d000c4514520194040001410340701d0903c4602c80300e001c0e0240102c0614004e04024649a0342c00055900c16940c403844030710041d8071401b0460810f021203400040040c040415a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 474876393 1250 474875143 474875171
    0x50610031d010c170105040905150414010501180c0807050d02071e0516060f02060a1a040f020a021018020103020a02100c0e01140c060a0e0f060c070614100e040312 72
    0x138480d980c2011003038007600d903a1401084200c944040c0010070540049401100e040c010844055005000c1d580c401020300d510440f0500f1981c090f0001c581c05500710851915815040c4104040001d150428a07058248404058845c0c01410300f4040d260350006880b0040103103010302c010340b2038001c2900310032402840c40d2507500d6208010602e0302e42c526074200019668419082e0f0b01101401d5005010603031a880c0c00e88001d0034070103004510b40c07800303804d642400791540d200e94101640003880040e200d60045034000d04190801c0c50002d10103013458964051200290007000340603909003070040e030b118140380c400d070300300b00e0621661018185822440a410b54004540c0d00c4119070036030340c04080d2850031751034a10a008041169906502c00400201080b00e00d50140c842d6200d079000315200400c548c075249180107404c460004143e0408502071040000c18000d0f54042d41c0140c50314151490b180714107107000310507403240c404c030a500c1001103010301d030040c1c10750701d49014250b4050152078110182 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 474877643 1250 474876393 474876407
    0x9010804241401092703051e030a0c08010501030207020117060d0c08060402030d0809060a0507050c012406020309100c060207020915150306030d0507080d15090e01050610031d010c 79
    0x3200d40f4142002120741880d03240345c02d2001c24241c0c40d1501001382486850482d801d400040340190b02c07c0e4904410b1011034049409540700700498800400c5070340310300000501881040e40018103040c010700210005030b822109081515086034286d84007540c40000140e080560b111010780010803440000c110b1020105e040e610480c001d400b11a1000d4103c40c080301d880000b190b41d103c03030703401c500b0109180200940040c0d4100150b031804a04110b0700b906441c1c04c4030381c45a4080c210301800e004541c0860407000f1184000c09840c0003850402074200c01180410410300ca03098108801494510200103c65041e0340340203802400d40034407450031000e201c0c00081954050740c80b94850b441d840c00401c00303050469108a03009400b4140c0400c200b00181c500341c1100d042181c85540a100500aa21030b0380318000c40900409001801d551406000300121a8034085080c0070341d0400c01003091980340c42c5924000941246000a407001c020014031014604c00d150380813080d401c2c0002c4911095101c41 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 474878893 1250 474877643 474877649
    0x906020d080a02220f1a25080d02070b2214100c090918050705060c0a0204052716050f04091506051201060806010519030501061e060509010804241401 66
    0x41c4140e40a074981e1180c051508901c40f1314002920100042108620b410305502031210500401f404807140e2640c400566811100c02030f141e4a501280b4142440351f000403003030b040100458812a080c508482000018a9001000d0700a4a4400310300004281c00c02c0300c01d41c1c22088082c1045120b0000c0303001403262205205901c07000b0b04211580640d00c0c681c0d61204d848907401001485000d20740b0043c003e980e0000e81b207410190156140344405601c0700d02819102d90a405001c489003101000a9510305c0310702c00300c040c3c1c01c1d4803070f140900341e50445120f41d405688040320111481c5e00902d0006015048202008001c016506800c6100c1c80c01340c2c120384291401190300801420004500d43d003243e560388201c0071183d0240004000d030341443ca00c1c0c908104135904101045540b02e44465094841c80d900c0501d20001d602290350f22603c4107403445000c2e20207031034490302d4400c4100c0001d0a910001d000a0034101c0c2c4d01c00603040d143c041d9103030000f00c4003c5902c240410b6803030144100c0c03005400d03c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 474880143 1250 474878893 474878909
    0xb030903030123010905010e150d090c080f0303070309020a26061b16030c05030a1d0906010e1918060f06030606050a030e030f040806070f0906020d080a0222 69
    0x4551945400c03d50038080031010b041c2d4034581003030300d498011142e24880364042508a60b2250b1000c2009904030000e096040c40c00001183c252290300c0c0400a40c1740a81c8103c05541000b900c0040109000c03017103a402c501940740100e01c1103924000174000d03d1407944203810801c014031101018a0702e0141110245165501380d030801e60b00c145002800341c1c11000480d8a41d4010008102c08290014600031814000c2c9004050400c55580b0300c0d1031079000300381d2203020540c4281031358900c070030201c0c2004171040d0a5890001509184001801c029007810865216202c0d000390310010450700c0c0301e00001441600310800a900141a809008201c0c50080a8a0210b007040200f549802401400200c3e10180da03002e240400402e0308031300400c4c1111468029010402107603c071580d10034080d2000e441c544004c2c0809082c06d180c040c14444000c4448401c0c040b0840041041d1a00402c510106503100e09081125545083c0f9000086c850103c2e00e5124a080c00c3c00d1031021079481c0c10a4007950f200d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 474881393 1250 474880143 474880169
    0x18060b010e01020a2d050f011a0d14120a170105030a03080c0a05090d200306010302060412031223100e0612210d0f090b0604090c0b0309030301 63
    0x50001107a2803a0301103481c0340981c1c0103e10f644005400e1009000707000314031051840d5904c000c0d035262603184045c11006e9a06501020103c403c1000a00c2014000041c50f807103112104000008a85c059120880151220040e0300c1c8200705c0340818440e965075424401285980d07261940e1000e0540d900a1181003828003944002241a0500060801c0e0b080d82540b646000c41e51103d02c0a038942e80141c1c00103003048428840040c4603103c40c0c0d96010b20728820000802c084c0184068180755160030400144268011401000940c50b101c3c1200c003030340d80e51000b01e11459120b04083d61000701c5d4580c040d081504d4022910310890200d0084144ad1724881c03070407031031500c40c59201f940262103402410115094640428820324000042c0245103004000b522000b000c1c0040c61007002440e21800380d4490b80000c4d00100c02c8000348038901810003000010012440503841f054854003000344003030300480e552490003060040d1a41088000c0400e2a601580e9240444106490740c0080c41006941001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 474882643 1250 474881393 474881411
    0x723011e02210f0a05060102190b0109050603150105060901030b0a180c1d220c0c1707050312060406051f0f0c0f0605180d0c0c050a060c060203191806 66
    0x32920706000d001c1920107400e03a521582c1100b4005c0134044d00c41c0d07056204589140c481020300e80780340701900d0302642d1a5900766160480b0312050342d0703005185a2098000d0b800c50f41100c061200054155a0203441d80360b21004c084006900030004941c9080c0d002c4031910700040c003001c4c217504581c2440c0034038600303010200702000181d5445030583d02d81c2038105400214080341e400c20752a034440d4001e030640350303861201c030700d241490454824401d01c0c00003a403090301c06c4041c8000f000d0b440041d800e00351562403600c4010b07210192240120340200041d00088004502c0640d16030300040b0190000403c2e125092041b400504070008814440d030010510030094080303103a0044010a00451f000000c1c40c00565955641c2030003860020408041c04483c01206169880308000d15400c1548949507810707200f80300d0400310194641c0f584220301c144030040003070040355403201000d014141d00c50b601507160f848218582011504292040030303194581021035100c102c642d422001d003280550381c1001000d075 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 474883893 1250 474882643 474882697
    0x90c031509080a0e0415090912020d09050f030114090a0b01050d081602030114130212030301120f030c0f06091203090206220e010f1503020723011e02 66
    0x6030340d80018240300003d01c400c2e03201600034008041c04580c001c00c0040e2a114034042c20360401030301d402c0540c80c503a07075511400030429090045d40007003082d80020300101b003001500170211740042c05210300a58501d00360750380f140c6003500884030b419640b003e2031081b807409120550703940009420940e68960124000525418201100088107420899107480d2040719106444402140c58080740c00d03643c2c9000000159409194450144404408405180750980100948408000c040030b5142d002000100103080e5041c03803040e03c01c3e80c0701d101100136203100e05081c0e5950590544c00b074142a6101c04ca0810800d80e58016444144611112000c04180350f02c21402c40d503550720300a4100104120300640690b032810a40c0c18012004c2c1c03660b81c000e03150428100101001e030304c030300c005111300b1009210b0060030f01c041203110a030a1804604144ea503031075022145041c2040b42c95650103182209102000a4200d00c0c41c2c002502e800c1e00c2e00700c2c0004940b80081d40004520110941003d2000364003003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 474885143 1250 474883893 474883901
    0x31406100311040203150a0b0d0b040516110a05060c03010f0b120f06133603020705060d020405121c031a101b080901020d0507031d0f04090c0315 64
    0x10390010742c0301091110355010700c4020350010348411400340d5450b800c0c9046644d00c24950300904404030401e070302c0700480e850309001e5460508095105078144802c100c04040d007100e42c040006514500410004840c100d02800c1100313600c3d018249004003001c07c520308004a0042d412203120380d030042001c44d5039040216a0340248000d00060748000004039039643c440c904815000403001340607459070712400049004031101000300c00c0d910300e200d4007c2d24003910580c4104207654a0850a003d120980c2d030380094861842c0c0c02464030685010410030710b406050f605850160001411401600802c580c4141d616110441e00754500103548801011091007401101784070700143c290100540d52303004c04c225008103a04804810040c8948001d00c0005194000e10302103409007a2040e0f440202100083c1030000b036034000e5090003010000900000c5d441050050406030807250209042010b000003800c4081c10340c101d42c1d000d81024849024820580003440449211701c07106411a1641c0d45080251 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 474886393 1250 474885143 474885149
    0x16030305010e061e130b0607060605150405010c150b090108060f1b04050f130c05032505030703150e0c040602251e030b15010e01170610110703140610 66
    0x1c2030341e40ca018421420656417222803000070910110342c461030303100400c900e908200000d0b500039444401c20001c604010803022800c2c454280340034500390400002a00d03002c00050002c2c44001d6038456070316140425406200743c0c4100405440465030b407511029690041568640f943c01901c1001c0780081c1036007504440b50307280305420942441c0c031300420044e00c0070060942d15005101050202c111490701d103d0200c59a40ca92120760310380c2841101000324070440307921401d11401440d100c0704203503001415243c4c00303419441c01141c00300340b030154080703070650690040006100c203000744503450040c2d030090000c0e03c42641c00c941c0f202c10300c1461400c6520502420200710041c2d1002841401481c03032544c1030308134242e4040902e1580c2e035540d10b205d66400322180040d1902c031418203400c940e800301c07101d084981e0910300481c003c42c0198443c072115401400b842e21a180290b680f2082c01c1c0079004414a00c0d058609070f40740c3c556a4204111401d003081d01421003805072400260307484110f002e500040d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 474887643 1250 474886393 474886429
    0x10030b09061215010e041e0309031509050106090218180115020f0303041203060503060609010b0c01110d0605031e03030f0705071e0204061406030f0a0216030305010e06 74
    0x58581c18107001501842904590042c0611402a080d070307600d820703100d8000c25203140340d07000c203240c241014290000c06451400d944030866903032001183d030250111060300c0c3c001c888030780342520b0800315000601400c20b004015500300034000400032810740c050a80c51800c040348030070386030040e0708010001c48681200c0300700c000c1d484014400b80030480800031040707500b4011503142c200c00c03101461540e0404c840850f01c201600d2006100217600d0300884008080c00e4005180c11f0800381d0000b150110140034050300c410b00421803058200003508000c0c040180e5111481e40c50024206000c09441c003800b8603030091092000d007413411502046407404032450203000d581942c998042148100e80c01914150400c42e00340710420206040400e000c4440c0800c5a20010940b4140b040c4015561a54409040480c003862001803940300e00e07084a030700c4a007850210106990b0000b0f904001c4c0074072200c003014452195100030400d6055440141a51244416820241e0f20581042502500c0d0300300710003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 474888893 1250 474887643 474887659
    0xd0606170a03081b0c160816081902010203091008010504060f05010807030b0f0a17011a061c0603080f03090f0a08040e060a0e0c040620030a0c03120c0e10030b 70
    0x44c24100c02480203000184001440e807802d0012651246468400460107010002036103040040000402c10441104101280907155524146c40c03d922141c031004903d0000544004d41e8046a2080c001c50305803140051080300c400c42c00a8004014902c02d02405015620700040410b62040480b2020105c0300c050703444504994602d0400c8000d4041082820780010030141c010106559030f0f100000a000c030301c20f0403200d00004481c81401d45908400005e060100c0103400c0703039183c69100c100c84002200b02050940414050f002400504d050b50001d02080000718040e004030000324001d41c01800088111640d450911003525154840e8590040c01e400040100300030074441591840d90001000b400c4c05040780c1e46803440c2003188422501886c0d003503c0020240041d030781003800c01c0210a0506150000c4020152005130360b8070481c0201418044481980b204240c400e031054601c0308001c0348148045c03d1881e801400464445120912425400c3c0c203280401d8401d104505822000400400c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 474890143 1250 474888893 474888901
    0x2031005060c0309030106060e0f12071203180f030b150d0b09010207021503061219081e1222050604030f020f01060806071803150f02090d0606170a0308 67
    0xc426441a2810400ba010900c95071440342c1c0c0a10540d0000c241d2519111400c1c0b0305402004240c4201a50b8603108403401c0071180b046503000502035040c0e500401c64800e00381d1050a080c3d0b140d030141c8003540350109000070301103100007010250108880c445d55018600b5192040004001c00a52400b9500102210800c0011071043c603001500034150f500014941400360700403c0e1090b03040140107290050000900c520b909000001c04031a038142d4002c0d1208000740250010388a6105001030108031000c100d0508400c0f113640f00304280100911101d03a034414211549200c1740044800d03030f10300d0000c071103403886000c85403a40c0e010722a400fa000d0803442d0b4a9a80c01d60764203100d0420300085104244880340040e500344500006030140754010041860f1000f001801c082c3c610101852900c003103101003000810341800300300e4804a040300461240c00310040398000340030701076049500400c0803105209005a80d402003080d40c040650503110050064511070391034401000050000d19004005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 474891393 1250 474890143 474890149
    0x50d020d0e01120b0907090e060103110d090302150108070311090114100e15030a0c02010b060304060e0a150c030b0a05030c0f040f0207050304151e12110408011e02031005 75
    0x2d0f1410895811000960010507800f0840900040b5001000715070540d8090142c044510f1504c3d0b80700d4000d280c10701840e2200f000100c0345014a050301c41031940c6500c0c014007007500a00a12000e0151082c10503055a0b41d44ca0b11079031112030388415070b580140034400b12002d050448819040e190202ca0080c2c0c9150795409104003603500e05050405c2021384480100c087c0c1e14040048420715502d406207446c2c0c00c2c00d07400c840840e40f44609100646e0724203040c40e940d45c0c80b40c0050766841508420b000607045032080b501030902042c044020031101000740d400543d00310316030009031405e14607078003001b801003044207000b101840c0e070083c950b241c2e00c03040b0000100e25101a03075100340c3d00081e0010641030b064450340816a084180708480c00d400104041c809188107050500d0380d1185880d00b01c1c08000300c01101c03c1d00420740c1008804110700c5181404032000160800d90201040d500c010390b4030769803810071900900950700c2c5031070b28070042e81c0d006200004500030790b4055603a0b0030005039524509420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 474892643 1250 474891393 474891407
    0x30103080c070f08010c120b090105130204180504050d020f030f0d060f0e16050f09060906070b0f060112091208040f0f150605090f040b0c07061107050d020d0e01 71
    0xc0d40c01d0034412102c1c081040881140342e500140545400412007040e180740140400541d02400d242023464481e5060403a511200c02904403202900d0f4807050b00d2020301030402030310440e00100200b00b21640400d1080740c044e40a240f145000390280d4416100030740c401c9032149201343c10651168424440711400c0d084a9004126550b501440004c10030303550820000307801c0303240c1e03ca912010303110f00070003c46008103030f8004201c2d040c1e172401c0c6184c6041464901c0030707805020720f16401039a01051601c45502e46400300c441043c0c2103619500c59260007590031032911002c590850000311080c80c145615552400343e11281c541c0100100000c036455070b030031640d44000500c2034644401040151001c1410f2001c03442070540101c000a00c55100c80c500e440507189154031150144a4035010070042c000800e4403da0001d5118820501a46408600401c0c5025010000d0502454119054840c080360001400c215201e034082e071b1511200242c0076600c9514124110001c04e00303801c03216141d503100d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 474893893 1250 474892643 474892657
    0x90a0b06030a0b0a0c08070f05251b0302100e3607022109011707051306020609010b0301021303170d0e03090102102003060616031d0409020603010308 66
    0x440b10000d0141e110390b440b200d01600d000b40080e5455141e41102a07100099681c4110079042200032246020b20080061007050b00212100c01c20303d0601c006000020450221140c120512104040c1c1099035455840d09034403003244503106a40a110101d8000c0f0580b110348000107100c040c01c8042003030046440501d94010502c822041c814000b4150342590342c841c0a00e50584c01029207085200300c00710003850741e145815840da803d00400009070380c8952a4581c81200d8031520032603450700c10042d1100d0180690070806001d0021011038011703400075207a882040204002d100321048001458200e204855040c81400180801400410305415040040d60f528405451a10110500305800c40300540c002c01280d4100080102296904201400d0306042240b0304100302039040d07203034010041080000107140b0074040002000380d91107005541d07668907500c220022420740351a004001d41002902002100c1c0d80f00e1a003285410a40326503203100f0340c0505003610390b900303603101c00301d8030b0304180 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 474895143 1250 474893893 474893899
    0x306020a020d022a151207090b090a090f06050604060c0501060e0402030a020d050a1a040b180607031821140304050307140c03010e03031017101107050d090302040c0503090a0b06 78
    0x30a0320920b414030304004000e00740c080021b007003260420000003030480c940d90b800140c05040c00c0c44024420b580f031406000071646444800100180300e079841002404503540440d42c0140e020400041264101440d108541e1003000200085612964039104118041d81c010707405030f0040031440018180340000c1950f942c0240115403c180302c5030b40c3c0319142d459501c1920300d07a4180e8002d00080100300d0103010381080c00e00c44449406000841d900b40c0d1380d04001c000344101600c441403074058542d0006003074102504032007c1212295514400703080041040d00d031600156254005940ca0750810090b680103940c040b01031840c20300642c480c030702c010020001101d420b000340c01503198070f550300348111400902e001c00595140e14100c10030000d40882503125155602c1c1d0140001d107480004174115200b180c0000e4005035480714a18510070134003030310300b000300035105a507050031035181c000d620082264400c0750140484101c6101c105c440d400f055a0740f00241e849000541d00081e10b42e1203285e0300080203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 474896393 1250 474895143 474895159
    0xc0105070312091a06030109110103110f040821040f060302030703020c03031806090f061f03300504030803130618030302130609060c0b0a0f05010306020a020d022a 72
    0x2490b460011200c44a00448296100528842009500604035603001108900800c4608100d0710b502c0725000a014840b03040541e1240400c00306a0000155015030403a8940d00b6115503d40311119620205120704007504c288408041c0c4803021001e0413a416104180e4505445501d8010190b01030b400203030081c01855000c1c00701800b81c20742040a18440c0140c41499001091803680d000e04140e00607028801c00d070410310000003a004001143d541000b1004d40c0c0740750200d038444041100c50341d039810090010034940c001e51109841d42140340c41d402c802025200180e040a4001c0c0e840b8403551000501c000d0041c030028a00c1032103809960b5480d0301800000ca0322100700d00c1c0d106003041c2216400c4000c01c1e408039068021510f90f14058011380340c3d60911100690403c0800340c007042032041e00038114041100050304054168200c803e201a40400a022a585900d03140700a5008403030140014801c1c5241045c8a510004501c04a001c0c102c0c1e0580031034100c10300319088002130070141e527040820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 474897643 1250 474896393 474896417
    0x603070b0a02010f0606090b0a0c1703160e060a0906030906060b040b040906080a0f14010b0a06080703050708010e0c09041107080c0f070b1602120a03050d0b060c0c01050703 76
    0x5080c00802410400d54000078100726008880800c8803940d401c40c0302000146081800032448203c1101c0c240403250920b403000c5a02440c0071180c0c601003840050682c00e002c801c1c8011900e120916064010795a01e501010440030405e00ca024080c03000700c400059003010b010005203000b42c5c05250070500a50000c04c603a5298008040f05610076482892030382000241000440340305e200f20006851004064a41c2440c142c45900351840208809000c04a2540904901200075400b070180070902500c03424210b59100380140c16000c04503042c002003420301c00080d03042441000c80e070307060301c0c8000a60642ca80f594498101e950b00328071305064100b55503800381c0c1c51030724031031020707010191082c40501c0d914034030711040c5802c01c407841d203148030340ea0b00c0381e001030101552440035550868840340043e841b00c140d070700000d040580742240c0c02c0c505000c0c58100750181079100008000d108904402880a0300745407040c40014415250105966084000c000c1c10641c4181e0044c000b0501a28281401d440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 474898893 1250 474897643 474897659
    0x7020927060403080a06050102030918190f0605041805060711070e010b0a020c0d05030a05180405040501050f090a030507120201060f1205190206180102190b0a0e06130b060307 77
    0x10741a03600b80c001c1075000007044102d05050160350080d0000703202850507d0021804501549110030b030051524078110002402d091311007425240601da812000d2241483d2210500e00070201c40c06603a00437401e104149500c03407102c00407401d203580e12400508071a5074210044904060084900c0420f00072124001075a0014081450203008030a030300c0c40c1d4540142402910b4004580122800340703c24201d000041000401500c55851a42c1480340d500c8140c0308c100002d200b040c0101c03a9020785014140402c1c0401580001d100307202014040400e0b0700c0314010255518913680c00100059070800519001402c14a480304c1000c0c207500010840b00d8903489a80c1100b520741d001141c0396040e48a030b9505100080020b071242c5000585500c0c12045981c0104800e4842c8504220041c0b21443c11244030382d208100380400003120212001c4101801d01e0901d07403101064551208150400540c041c10702801302d07142c3d003da40500e000108100d42c0b03a450341c58060000b0405641030103031110002e1000c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474900143 1250 474898893 474898903
    0x4051509151008010527130807140d18182c0a0b010b0901120b01090305010204090b030705030c0d03180b040303030e060a0e0c040e012a090b07020927 66
    0x82498803410f82560509040c840600034040c2c0c400f1108803540100c001d16a0b4403030704580c0120600d6000d4032004040d01b401246807103581d60042002d4280014035040c03203004100c0b03035034091195440d98490f83e00c030701c02c100c0f11b0a241d0054050780480c4810001403001254022004207000000084a000085054141c8600c41540c09121a04102c2e40c06003007110140c8518090300810303404605001c0400c00003004420300c9074250f5201503071041c400109a0080380c0540003558000001c1d507540e9144d00a01303021307022300c0c100e150180c450350744042842e190224040181040117402440700000507141210801c03043e2003009107180700c1d40c10100300011034100910245001e904e011450a10000009181c003170003d240c102c2c1c081c502001d84885403800310700c0c0a401482258041500350f5101001c07070041c0711150303500e510640b00e000c11940c0300000041440c10920640c682d1303a161030b81d07110044098414a0b400039884521140050f4510105182041c40d2210030301214415406286965181c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474901393 1250 474900143 474900169
    0x3030a1a0d0506070206130b06011b0605100611060108210c0a05060609010816050111030f1b0c0a0b0409151e08070807030506271501030506060405150915 68
    0x2d0f0011001c2000044d01002282e07001070b03501c0654801d003100354458203c080760190006040002820101d400c0c800c4800706034101a0b00007074100840c3c18001d4802d08994518411480032940b0614019504000407405604881014018000d2200c2c0d0703c1c60220780220f40c00c142c0d03c42600902401c0702c0c000081100b100c00900c07170402000f06040030710400400c0300c0c050f1300404055110300640c0e080c21390348603101001c0340c1082c20305880c9211401281415406005402e07030b41c001c40811010740d1b444c951128503004460010580300c0e404001010b1062005c43d50040c40c105130000c10007040000c1c0580c2c807521651901d0701d915a2207985540651155401c44d014041e64100ec0020030300041c6000d0000000034500c0500410a00b4034641d135458a5041c0205005c480040003402e108400884800303d10103150844103a4103d4080000680310403c1c00307000a540c0c0703200d400001902e500f890300c5054010341400518100700040c40041005040009207900f001c031a00e0017403218903444418241c0d042d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474902643 1250 474901393 474901403
    0x80708010204061d06070f051e150901060602070b21010b07060f0203190f1b020a0b06040506010c02040506010309020402030c0a110a081603020733020705010203030a1a0d 75
    0x910780c904680104030401400c1ca40165413a40001c0e001e655032001d0403112000e503c0011400404103900b0a2400c011b49481080c6415500810b40341c4000340c00b0400c1d402c1130b00100d04540c884d4a0b981101801c83d8424003d40b40541d02241c010300c0300301e200c10b0140c07171000b0003c41c05c4020380c07041c405004070317614080e80f04520500c000f00f0540100712440c0103229440303601100450451a100d031810f1001d929240790004840c0d600c10003600504200d4020500b02404203243c0120342d00c281c0c070029951000d904080e215000c640c00071920034a840d0049a004640580d102503004031aa000c210040c400070300840c0c14980d8500940300140c56a00146104942e90710300151507107545880645000050120f00c001a004040e0701e5001500d001c00f500c1044078810150140c11351305280230383c0b1340b17003441d0000004044041c4040310341c00b441161402060180e1284964a000007210503030f6581c4190050501607041400000d1280843d6803240038096035803d8032301c14060014011642d1612030103419a0703 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474903893 1250 474902643 474902647
    0x10e1b0d021603020c1005030a0906020d0e0c0a1e06110c120c01170402280b070627031d0303160b01030b060108010807030303110c0d091404060e0f0403090807080102 73
    0x100345501400064170100c4186c49820b01050782d200018150300c001403203072002d19902c6001c8006e001071541038030b2410740601c00030810641a00c0c0c2d0540e0710304004106503c0707001e0f400c00c040350141c40350310b00c90201d982c00514101040c0c108542511081101c83d040815889a51340036059650b811b507030240c04401c040051b0480f0042c060005000307945695802c2040302d6600140310041e01c80314a03865400404050809200d40300801916070114542d1051180b0017020588005100b071a91140f5901c09108880c141c240d6502080801c01001200303001d40490072107c0081450020f882d8004890f040c014188d91500100b4a040d003000350004d041030710072128460041c400c100381a048180c1244090900302d055602d030501082d0740b41018000182015203528032403e95558070401c2e14000315451054905131103440e0002030803000e862140d924007402c0d184850b0032074281482264256400c141c2000c40300c0d500e01c40707102140c4001a208804111094000013908407003802003002616148001603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474905143 1250 474903893 474903937
    0x1612110d080a060f080c040e030c10050105030d090e0609040606051c110301060f061103090a08010902150a020304140a050d0b07030b010f090302012d02030409050906010e1b0d02 78
    0x42110a00d130404004110030308024060b08200090400f8810000c4078042805010320080c0ca05600480c1d00c5221184070301b03071031401c82c585a034200c6c1d4140e40d0280c08403101150700700821901c0840030f05c15410b4104119010036002e08011810a90040c0a910003107040d076541d00115200c01c40d100d03040b03e40110000812010091541304002c2038500c120001d00c1480d0500e0318034a03110145100d03550134004404d080902041c3c091080d00e0600d28018068070885607264000b0340a4142c420b8201d2140d0b05401c15894613600203415070b0611086603005609040c2088803c4107010009c0320840d40c0800c2c21100010a559281d10025410b403140011205a0901c9031024090f2000c10030b00b1b5051144903454010201e41c4021f014041342e40910700781505c4140c3d040d5802e4500c1c02105210f10200d41c04807a40c0c682d9400100500458a880e40100100d40e1041c0b00746481c0c000c2802004851605100800d428a5040542e035443e4000c050306149000a09030480e4102d80c400c10740070054083c0f06134a6 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474906393 1250 474905143 474905161
    0x5130b0f1005030f0417030c09131a060a030e0303090136080a180b0309071e09020307110303040c1703120718090905010b151612110d08 60
    0x9016144180c1e80000898591000901540002088019840141c0c0001401e02c0700d0f034907030911500d80c0015183d07620305080300d80380c00c1c6500c0700d40c0c464058441c800087d000d107101441103154558030060712001c0684003904006481d4020160102050744071a10281100c40500c01540101800c0c0300000b14091001e45e07094403080da01004c540761581e02d075a180160340d0000c5001c3c40c00c0d58403180059403001d4600054070401b00110620720301c0710a404020455010140007540a864880212403005545803280a404c03540048a4801d040020100700401d990035005541c10403401d08289850b1240c2d1361070a2301d16081190150b5a00841400800c000446204003611210194000d14070300b600d95440040021806881801006100c80f070b4044000c0400c45010040d1074a01c030144560300490070f02d607010b0003a604800d44140e40d420780300001400e00e4422100841c0010200070b170b596025844100e0031243c51200c1c0b000f44004079451107801c400a010ba81e400d4131607034540c210641012206 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474907643 1250 474906393 474906409
    0x130911071a070f0c0201030e0a060905070503010207030c020f0d080c0c0411030c073201050109110c06040b0a021614103308030c0f1903050313020a05130b 68
    0x41c1080c481000c0050040181d070202c00200511041e0404000f46912880100c004140801c0c3e03803d214000c0e610544200501508245036840c040c1d000c40d030000c0d844500309400c038800d41034004c0102c1e4985180d6001810621140c602c440170041c8140c00101540e01e03020a0381e4485c02040d0f00e180c0040912540c07034078140c070524180d0001d0b21034980c151b1808075450031742c500c80c04070054500125030154281d03100400e1035903144400802c1140080403010406180038040c20300510b5482410b150b0321019034182d0406507124000d50400030040d07611240c0b200c8071080805021044020340800c05481c011010244141c401c40c82201030b140c000140c03140440c1045041700300440c89905110070841803642102e94912131038149a00444403103443c900060305042254003954150001290106140c02c000c0f5918101e81000419280084042c0c841103001444240d40207010840c18030100710b44108a000c118101317440588807200b519190f50010f00b183d0810b404120b241c68030ba80e1000b01d07900701294 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474908893 1250 474907643 474907673
    0xa0305070302040609172d0c09070f0f140a08040525051e030a0507081e03120c070c08010501091107020f0f0105040f1d070e1513091107 60
    0x34046081c0313420004000e00411003445400c12000c00d8880312441c0707580910034003120600c81304213036449500100b002001c520940840c01598029032405d034495003480701c5014820000380d07460b0545214040e200f995462061005541040704815106850800c0c1324011b1561b801a0386074109245000e150240c54050000300c00188842c6d9882030010b0760070480340100c15141d045600f2858404080362240b1034131030901d4110351500c200d110324014880045221000d5920400070766011704168200000b01080010151500d58010054049100c0d10b031441d560b00605825249464040c03692288004508950030001d402d96403580104240c07466846040240c07071028442078104030103600080d01070301040b03405a00450006074404142d80c880d0048801030305d050085800e100e929502c0c0005100004114010029406c0e4089991203004071040ca4041ca002802a8080b61010303251001e507030070804202c4c0c0303071801c0d4010224900071a409500b58103419650451388135156404e000c1c000081c40c007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474910143 1250 474908893 474908897
    0x305010f150f0503150a030c080607051201030b061f021c0e090f040c0305150406110c0a0213110d0f140105010203120907151e0815090a0f020f0a030507 67
    0x205107034001d60400c82046074070340e1504003640c83e5543e195a4203043c004070350400380e002c0b50140b408000c000c049502c40064a000100301d944650729008152200d02c43c400c00d00c00e0039080b050040001541d84840a0350129000c0c100481c1800039000c14000003d080d030100c40507030040c050000e00312540020440c00c0e103c403454803400d1034060f40003003502e03080060010116000d00000003810b01150207110300095a000c01260007140703001c0116000040151021110707035007413129000481c2520401d035840e82a101c4081c00000402c1c0d030800c109a4556035103400d40c16250042d40801841700e50150500c0300360204046802c0f204203c000044800e02002c04a51032220740040c0002d903400000d07640c0030080404810303100d1b100d10400d28606030b0a58030904001c00c2c03039511500c18a9108000669220b03911898502d9404814030698489100f22008030b2480141040b00300a480c20104403900304201000000c0c6446c0008402c0090345c0c0828030320340c4c4044c40040d610a00f140c2c075210b01640146a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474911393 1250 474910143 474910169
    0x60302060315030c090112030518120f16181d0f0a0c050405040305030601050c01020f04090902120f0d0302070c23030615060702040f14042105071a10080a030305010f 73
    0x41203d0a0030300907c100f0240410901146c1d04031251000e400244010300c0003040340c2d40c0c142c0103819250b5a0b444440c00e251090103800c5240b10182e540b44c1400081e5075a01484018911840d2007c80007482008884840b5100b0b280c86000071385001c0c0611601c6050f45401740000c100c0b241021700e006101d41d4031090145251504110210740d0001c292500a0024030b0126550400b000322217000e40900364055030070400004001450f10b0066010b0161a0f00c00d135505120b4103021542c180d25810000e600c0c1005070044900c02c41c14910950007084417611604d0108482510780d507e240000e0151424041c1403141218011920301d41000819440303103100950181c4030740e424005c20014000c5000090081b911100303081c503007014030782010458241140e900b0b40140b50604180b00004050141c01031b05c20f1491001e0690944190211042e40c2c1e01310034002407903a196906c0b818454001000845d01d2036400c000451342203005d0120341c1003a4000e03500450a9410090802400741003540100c1d00c010035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474912643 1250 474911393 474911399
    0x2d0a0c0f080727050603150c0d0e01090b01060e060d0615080c030403020703030e120609010c0f0201060e18030912030702030606040b030d0c1419050c030a15020c01060302060315030c0901 82
    0x124540d0030704201000c400100b4130391111004a490211140603503181c0741e20301420040b003060601701802401c00c1d222001e0041c41c100c11000380c2200c2d41c8100180c40178a82c040140800350084e03c50005580002d0321007480c007402910740b14215a540c2d0011200d8800c400f4031140b003180d02000464000b912107515902d1400e180e40d01030340d81c0302140300c01030510044d0000c410300c1c1d949030044054241414000e5501d28500860401e000741816003100b004148015101220300c2c0c41481841d00b03440f00d0a054044503202e001d842081118004407150442c81304100700c90842d195205502c030080801d40095071120307868410181482c200402c42ca00a078500040303000c05580020b40c3c507080140c0d50404024802c11420415281c2180301200e440c0342c4544004d011160300308080e001d42050040341503030004452401055112070094101802000741c0180b00c40f1011400e5005004005045c0c00010388290b4035404203e4642040303070041c0d0f25199000a000260409011008040c402100d0400755581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474913893 1250 474912643 474912689
    0x10090c1404020442110607020d050a0e04020d06060c1106031b09030a390f060f1101060608041a0105061c0b060c07060f022d0a0c0f0807 60
    0x3111510031541c86488203c1300701001c492200c40c28038410440c010f5400c540e00800781140140c000c50348490710a200010382542d101107000750703c2148c0c0d590f849150102074201151070b46510403000794410781c01c01040384640004c0c414240245500d0b00c42d514040c0c0282003001c818070400e803846024000800070028148502441c80300030710580d40e440d40c0c8a58505c070109180484804005000c00b0002069101360080c5040e007035456260325903108007080004028022444591242e0341808168907001c4c04030314020615650a80110300c1c05030a821a0b54480350309540e050361121011030340c02014041840b020904481c002610403000002c0d0354500b03070210340039210f40b008c06041c0507000980324440c4a07a40c1c001d0800d143c0e00602c0e0a480d0301414907080e886d007542c1c2c0700782404130b01101c00780b4001500100e81d950103805001c10940011355124024130422000c03801131340340c50007048500000100c0c3d09002c0b01c0605840d44019140c141088507052514940d03400010842c4851200310003144 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474915143 1250 474913893 474913919
    0x30d0f200f1f090210080c090a09020d0b190b0a11060a0b010306120c030201110f010608060f010f03030e010f05040519080123060f120a1a06010c030c06050910090c14040204 76
    0x5564503084070647e95014000801e8002c001e11540c1c01107058200181d61f106c02d0b0090b01e02d48056030020000d00380240f0400c00300005124240d44250304000e01041842c0110026010749809410001e8652080303248a90800a040f26074807a0207585080c0350059507850300c10400074080b5100d40c0346107114a602d45007141032043c80b00038100150807200345402e1130f0610400e10f903803c2c050000d0022980300c4014945401c3d0884a841103100c03100700028122031310200c9801120740645400400c049204011514a040081ca040c06d01c0010403001800d070f1181b950414650080f060a0070740c041c1440c61050942e2801540b014805207401c1f0890044924841526045031049650140c540007410100da1000b880308100034160182c42e480c1018080440c441c0b010b140b041c10941c0c072450b44e500c8015265016070010160025484007840c40c009883d66009030780020b000c4040392103c5440b011220300b038078420324084071038a0391018104070070740e558031200109040c121001d41c00c0504142e05100c2c41 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474916393 1250 474915143 474915169
    0x6090c0b28020102090301020c0a0204050c09011215050a12031206051c141603050c01050406082202030d0c03111b0105070305040302040213060806030d0f200f1f0902 73
    0x2101030000c1c6000258001d6044a50325080034009545605d640c880c95611440030b103a043c2d0040f410040081c0300001e481c0c04071446d4400c141c4581c04c502d0402d090640007071a40c00c0c007a05a4408a0f500480c00740d4030504800000d040c85540d01a6411b42c03840c009284400e21500e0807015400d01909101c80e83d16410060900f00b6503103011401c12030389091820820425a041450601604010031100c100c000ca604058074021412100100700220044030b8910441c440c150015041d031010a01d4500030000740f0f62280040120098204144c1d000a130428203181a000c0200c0c0819900c0002c141c3c002c1c2c0c0c180a1203004001070401a4100c48151407801e00c043c0e40c0f141080400100c440425010390f065402560700500b0440d10358647c606003900502c82401034a011a07402c500240b03da103400183c4030340145051307881c0300f903c098181c4140e0f9840c03200d580f03000316040720391580050400100000002041c1d040f00034018125000130312600307198203002016040d803c03c4002c20160312050280028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474917643 1250 474916393 474916447
    0x1106040c170a060507030b1509010e04021c0509031c090f060507090902160b0109020915030c040302060705060609010e01030f0b15212503060506011b06090c0b 70
    0x204880721003000e410702500c844014426407416013404440750b13055001081c207050a4460416402510550031024040ca481e603900040d410740c6008120704040d000f07001540c2c40302c280f0710440100c20b102c00055540440d80d1034010792010035030810001807111044054103040c042004031100c030ba11034142c0c114004c140a00f43c40d0719480803948052141d46803034010303c52107104545031403c0f50300f9031901030940d42c410364128031381d49c00108820040e8801c8851100300107154040840030b400140290b40c000070f101c08070248003804004017503100d103402031001c3d62144014040c9450a6020010644d00607001903500c85480e80060001a00900e151901960000000001c540d5000c1c2407800901d09942102c0c3c01032a500681d10302c2806090030500c54090f100184e5500100381750324121006601442e4401100e030891081020070307090b1b4043c4d50050010301d01031950b04605658240701040210085540030340c0d8100480c184010142d844005e4208142c10924081005044507603010034400941c00f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474918893 1250 474917643 474917669
    0xc17070302160504021204061a0d03080403140f09040b030c15030a1b050d020d061505030a14090c0d0206090a030c090b0d1a060a03021207062003070b0c0702031006061106040c 77
    0x2060010350030880e4102000b4020100c1104605d030033403c018041d01c04a01281525184014082c141c1c4160344155014644e800e081070f0400b000c10001d4401d504026416003d98092565951550241d03008441101a8180e599042040c640c20071212050118030100c0d103d010700140181e8420200c40c03948003884c0d005030700d81d00f1560f1144010a2942c0c0100e5171106c15a14117031600e030700200a10312071100c4070002c00100c20300004140b5102021200031034070f50410610141e491416030f00c007941050000c1c014604003410302c40440c4c2c030030000380c1003135425048050081003000c92a014803444143c00792025600c0c0c041d550f0380c8100c010000d00c3d464101080140010711184c44030b42c1d1804c02542c00034045003c0358922803da54884145004950000756458150250100721300d030030f1a003007108040118545111a260050380040c00340c0231203540c200030007011001d41c0d03003004840d150303126903500002c0e00e51525202802601c07103c6d07101e0708150403202c204404a080084bc402c121103030380c2100c0c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474920143 1250 474918893 474918911
    0x9020a18230402010f03050105060a0302071b03050705030706091409071101050c0a1b0803150307172404021011030906070c030b01080313060c1707030216050402120406 74
    0x25000d01120310000003604840c0a85018803002001d205020718000c1c0c0b0799424a18600404800307031b0f1000d001d51500031100300403072590b5620070f500402072140603045000b212404005c00c900b19000c1070340300382c402d035014003002e000c0c515062007044d0041246007000c0c40340030f14110101c0b4201100c9260f06110348d103a440001c01c82801070a5885202802038000c0001e407601e071240d07000c02d03000b214841c00010210b400714940342e488006440c41c040e80000441c0e00310b40d07403080c049409894889004d030b050f0085903000203806021505c040000d007108030140081003600c803ca461b048170202180c00c2d54409802c03c1c4805a11001c0d02409003071458a031240d41e0100380c0d00c0b51840c2d882065012600118006002d1041c03241200e03500058134072030201c2c1c542c036983e40c1030303510360b0b0b4017503007400c1840712201c4001001313041e02500004a04910410401d148104400d008080c603030015281980075130000400001d800c17040e074101c030018001c2140c0c01c505241c280f0070b4112a902c4000c000178000d907540c401d00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474921393 1250 474920143 474920189
    0x4080a0510060f0e01060507140a0303060e16120213121a06060a0e0f01210501080607080405070909030e061206030d0906020703030c0206070203010e030d051e0606091908010c020f0109020a 83
    0x89c2d50a001d00301c00f250071004203481c00600814403489042031003000da00c007052541d10315880c5101941c0c2969240c600c1c2115442c0301d94000e5004100d9000c95021110001035683d40320200f52100600403c62400d03260300d20290285034003401003a00e88200303810080310100541090302800100815100c3c0f5003104c111a005072010720f101c200a040e8031410b042c03a00880280f0b134001c581640c540c90140c0c1d040351145901511b4450b0300b524010580e4000e0441801511559407222851034003a1516000889800001c00c0070743d4072010080142a50b48010448282400c100f40005091103290060040e03142110094481c410740c00001e0821003042d050381d05540d00c4c2003d40b90740301c1d0014002c0001d0b40844825994a41c45580c1e09130384c41c0c2c1001c00040080d5021000681010881c104004080c0ea6503020090f0701d900a256143e800311400122080c03002d811082c00d0090082c0700e000180080707200c00080d190448009400d02d07203a0600a0b9030300140c42e865510021100403c203e81d0b60020110f1003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474922643 1250 474921393 474921413
    0x50603041202070f12030e0a05011403040c050d0b07031404030504060e0303130603050f0708040804090506120d0e3a2a091116031404080a0510060f0e01060507 70
    0x32000c501801c540801d2040e207400f4805c00e110704c6510752022030448401800120319161156038003088410101200d034908030303001564444d2083e00d03074820a540300c00000e81c2040440c402520450f08620401c2801509441504640c0d04c0c024100340c680d2030155401030191160f80924803c00042c140304008070344041064451840540c0301d00070b02ca9440e1a4001c00606040704c03034001030100d4001042505014440c4d05000c2c03a006405140350a00b009100e06c0501000740c8519006402d1a0010740008024031401c40a03800d90703075480310001110002c100408001e0401401d159228010300c00d45032400f12016151000b40503005d21090f0201d00f40405801021030800194980721003201c4101090184010b080d00d204910420003580c0201208903180116243d58111032400526240030034040d0921560b1030b04265403861810f62241402c03407c000651000321070541c8100c0500800d60079601a01d8090103081c046050700d20329280f01480c020a0600c564010301170001600c00500040c180 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474923893 1250 474922643 474922649
    0x90f06090d0c1e17100b0d060f0b0f010e01080109050c040509090f0d030b01120908040f141002010b03070315090b0f0a2702040510082d060105060304120207 69
    0x1001260255072485411015032503103200c070955032000342c0c0104249000c3d0481c90404031380f44d8020031106201030307600002400d144d1a003d600c00001c280c144006015070249003690392080c20b001c80d10803600c2090149118014954905009018170450200d036404041d81d411204080ea0100e0701d9254181c0d00903582c41103070002500090400c0801c00405800900310205140010448031840142e0104034121145000c42900003502408500450341382c58009101035030040d030030b031440d040d5141d200100000310390b4010a02814829049001860822285c1c03150044c1d40c0020b1041051130b1000a803200600e00008240c0c01d84004086150001a484400030702d5100b0b141828a04001860400200d070454190510506004103a810b030030b050b42a104035080c00c140f07150204580380d8204406060014950080800c0c650800100c0a2040005061456500d01030320b1490342036020101c0c41d0381900441403441c0c0d0280c00104210b40314503048a41c05500b10408081c1e030305000b00200d0903c08194 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474925143 1250 474923893 474923903
    0x40207022103030711030a050301031b1502070501080f090c010809010209040203010306091202070312050c1501090204030c1202010507030c0311070602032d0a03020f07050706090e0705090f06090d 86
    0x111200c0886070000000314056941d54031505003040b1440241607491050704843c10004030288010000108540c410b21010110200c0703000d00300f503c5110311b00c00880380c00c905000503070054204000c6035800c5a02182c00001c04907643e41940740840056a0311098500341c541040103400000c1d5034031a00390305591383c1c1c00d0020401d41d503950303403070400b40d015182c421001d80e0490080c040c06504203000103070000c00c403903024500710f0006441c52815202900074400884050141c48040d8080d03031444239a25018200c10b210040c0c5803425818800302841d482c1c2c0003009840380d0039100d0310141c2e030444241c5040d0b5900d45445204a201e0340750032904e4100c0203440c040d031032080d6140441d0b0b40c0c1e004009042040418038a41000108580100b4210083c40d2030440f1203403c1041701186041c0700390000c0940801e0354511310f15245003035032120714001036540500d00140c0900001d01020702808007240d00f145031480d003a82440210380005510140100d442e87c4100000500001282c0340c5003040320095400c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474926393 1250 474925143 474925189
    0xb12160906082104170601180212040b10080a1a01150c060f02040312020a050c0103090f0f020103020403050706320d09060e01020c0f0717060c0705010b0409030c170a0e04020702 78
    0x3da01744039a80e004c00e0044c0c0c03982d030380011031070540d1a2162080d00e07001000c03011000c40c1a2290b85030603070101400b8028000c02c81e00d140380800e82101c00c1281e480480d125100c1850000c1c80030312000307409041a04007002441ca01405030900303a81c00008002e00940005001071111101c6044000030b01c203a600c0100224956001c41114607000f0444c419824001c0040d00c00309925100110115180090001d091030050794281c0d000c0b407601201c8107007080c41030400500d0503489803038040c60400c03035a0001000410a400070110b801da44501c40c11012480100c0e0f00010350a8443c440480c010b5000c5113001e255549480018031200f0b402c00581044117030000c540d80c1c0180f594040d12014400d9a04049100d00b071070028043d84a012480d142102040244c5460748410034034090582c1302c00802d032480d64803006209140c0c2d8a038891012464440d84940c21110200d1030441c82c03103080746400c08404882800800c035402e030000d0310450580c4d01110016918000c5100003280f40519005803400c42e480 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474927643 1250 474926393 474926429
    0x70b24280512030d0501090501210203010902030a0f11060403110d0f080d0b010e1203030609090109120806011e0e100918021201090203040221010b12160906082104 72
    0x100041444c100084410b00490b13880314100c0c41903031000e12460440c1084514010b035105820515a40803520090000c5440981600000d280101101041c0c58602240f00c3c21403c10000f02c550702c050350801d9504d03078105859034440010407421030607450f001e01e290308040f108101114800d80b0301d40350f110300c13656228a4104000030082582640b4540400c1b010b5007449031520700000c061123180d4a481c0210702c0e5503228800c3c042c40c0e01019200620303941d2103402580010343c910621030b19510041d51401000d1400c800010000510030f04e60805440e4084402400780e54420114600b07004180c2c8c040d6120709011104680390f1722107600c43e03405030b004803400540040550b001030440c5030b0310503407411203643c0380c4101008034030007660020740c030120f00c0180701c101c64840c046100d001c00c04d41000082240b0f03494040f507034130084441501100d8014030380e896400d02c44420b1003c050203c000b000c004440c20040c1150b47d902d2418600b0300d219112040c0c4120042c210411100035060b1a1851200c481c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474928893 1250 474927643 474927679
    0x80910030501050f1f0e061606140a020c0726060108010b011e1b240c0206071818060b0a02011b030b011704020103020d02070b242805 59
    0x20a00400384900203c1c603581c0d0540ca0903003507609024000c01da40da160701721101000e440c503400c0c03214015001103081c0401c0f480c00305171803000700341c050245a000c503c2c2e01015089810f1403100820714440310b8414407012010000025141e0143c5480c5180130b4481034503091030300c44c1d0b480340d41c001c5000342c030494002148000040d00035210080c030a8179481c1f81144101d90002070310310801d5005000880c40d9501084103084114603011080c050291038400111032096004000c20401802142c5034035856100202d6604215155100c0701c90700d080585500f50500001c055201442000904c0b45c807042c5c401e0440c49590300c90030082220f20030f00d0303507500c0d5a0380000c1e003e03080a16054807405440b403040003001b4001d00903010350f10030507076600c45210440d401c0044000740241040e81056070078410045180f10314401041c0403402070040203090f10344501c0f00040d410045400c00c05001e00981001c2d080d0f225007005a10741e080c1c2c950b4251a85259000607000d080140d032045501c2215103c02c540d0307040d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474930143 1250 474928893 474928901
    0xe03030c0f0a0c241202091206180309060403060b040609050103031e02060606071217070c0c0b191d030a121209080f0703030f090b01060f0806130908091003 69
    0x24030801420001a554144034682030204c506500c90440001c0082d000c001e105007040042c031440210700605140186005c14404615070301d04007510383c80300061001c4409002c80e040030b256001d100441c5880c0c3d0100100300e00d40541e2200614554680d6400490b42d40d4a0f08020090310380318500f04419a0b40341802445000350403100c50b4800bca441d550f450203440410380611401010780064980490340d40c0d0b54a0340c49001c3c42003020003030401b65944c0c49003945c007402805241c056071411101906410300030380b00c4003203078010000c85c4000c2101c03250901701141203403078158a80c1442403414000202e1405c0303c1c1210941c0c9580360061a040208000005000c490705400c140d98880c658000c105c01102100c0b02d555010b01980000d10296080da001c000050903541d10903c1e02040d400100a04c0c0400d41e104a0421982040e80380e006001d82544500e0480d40d0302c0c4289080900c505005001c90404001590040c00d41c5440301155428440d0450444001030409442c1400b80005030500400030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474931393 1250 474930143 474930163
    0x903050301180605010207030b0603010e0d110d020102120f06130501120605071704081b0a11030c01050708030a18080310030203010612080d020307180803090f090405060402010e03030c0f 82
    0x303042144020b0454080c51145070103803001a00180384450031a115a03220f1240100320039450342d00c5414600c043d010512011484202548032490b06d011814489410000390014a204580c81400000f43c0c044034202034981141004c2c00040491729a040854007a091004140d80b0a81c03c2c0000007500f07101e80c00034480c030070340607a1080146d41c44500c41100c540e09141d10407c010407030390000c038001c64041d100910500070040340100c0c0c0d044a03100c03841d0920b00901c2050701e42e03503c0c203484001e0710f080038010005420024078081d40350802c00d42c0c544445000140044042030b50b9003580c00c489207104003111425030b42203983c898880c60910500300500100e400124040c2d400d10400040100a80c007074490a07550142049050481c205029030094000500a03400c00200251180800d1440c01c4164042c10111000c0c5540b000d8070030500c00050442c00384180a0a041010040413981c0854030719002907091a10140031240100040d1641c05001c1c040e484a02689400b0a048240003421501c0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474932643 1250 474931393 474931409
    0x3010609060315080a03080c0c0f0703050f071203050a2303060a0509090c010302181002030c01050f100303030905100f06050a080328261f030201090b0703050405040903050301 77
    0x1e40d1007490781c00340201c10303904c07a401d002c2c1d00c039600b8800081d0003446680d0380420924511401e02d00c2031350308075250030950303600d01c0100e80003400300b030007488400d00c41005000001c0c4002c0503064603180c2541481c0c5442d000c003404110b000308440007003d01c640002c0348400e0f820800d40036404c60006440d1032561040c0c1d00d1510070b5000c01c000007440e09110f8082d42c414550318015000002c076400040d0065440044030015811000c1030002c2527a40e0301d0000001a0b8807940150b442e0700d40032070b18a08640b000b8191020803038000302040303510000e8034a90800e89038140303801300c1c80391020310b00180f078210556001d040c810301f0528034020000266005204807441203030721280303440d564502143c40f4071400c4007030140460906170001980903103808100e41c900e03052030050509800b28048200281200100c200180041010f0000c201c00c503032100013084605181c0c0b04d00f054603540c0081d000440e80e01c00c40c5403401001c00c9100601d0701802c180c3e4004d18010704240500800b91600800c0395001340a5500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474933893 1250 474932643 474932651
    0xa0e010f05340509130c1709060907030204091109070210060902030633030a02130608160e0a08070e040c0b07051018050a0c05030705030a0c050f060f030106090603 72
    0x1494158070140c2d8090b150700318854810341c0c0600707500f1100c0341d10103140c85401031075980c08620411068440c201e94039040360380b1502e8034000d0250144e400003019214034200d62002c014080302c880b01180c0c0c0011a5411100050300036458604202100d000f960040d520200c03a0041002050700814025041a02458204842074891403408120f010582d00c254200546a6226610380650041d12450705890421a5215041c120480a25910495040d0401600461a294641006591000505000e0600c0310380303031411060300c040250342c0f00c43e00360420801c085210215220042a00080c0000c0303800d5800c0d00e074917100d5020764801e09072001c40700241081d0001404100000990b00c4042d4048080e00c1d01c20030f01d0380030002800c504154031707025505c03601c15200041d808005c0409078038402c401c5611020305d04801c1500388521170340002e0183e0080c012100010740b120913828241c5030100e55103580320252001186c811b00070247c04458581d00000042070460f04240c0c00011100c6d2550184 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474935143 1250 474933893 474933931
    0x90c17091204031e0c03060b0a1205030a0c1b09020c06010803040b0a050a14030a05070816121a1815010201060e010e04060f02040b1804020a0e090a0e010f05 69
    0x1030396034500141c80040404041c041440011080343c1e10040d8080101c440d00d00103219621a0901280c0660044138101e50710000c038011410164520001001184900c4d009414151102ea84038030410310b0748020480b0649042040242c0b9184404200400446231130300c10351a144410000e61104098402d50706c510130000452040c0002180d043e508415040ca05100d0444015246504403c0d882401e00045240420707801c0109009144a481c5811002c64182425030001c2e00081000d8142e000140d0364001020031640c0204481070a42d6580200280c032860341c00c4a40c6084607200038156100154045420303c050402c10b019004043c6601c442c1a40b0300c01c90016030803501c007441741c04d1002d1860b5004118541d40445000e80c4503001e044045040b800400d80481285c0c07298000791190324000c5072005060f001005141011441a1411840d0400c0000d01800c0d0071581548075106544500000e943da40031a0407101c107101c86000203000c0c00c000f50542c400503060895912a418a87c0103030f02c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474936393 1250 474935143 474935161
    0x17010513020319060e0604150b1e0f0f030a060905060f04030801150c0203100507090b071e05100509011e0c21090813170a051f06090c17 60
    0x9103419950040003840701d1040340e0300206014460590a07248250b54010364520020b0600403684902d1084600380144543c01e80e4460032903810580050060008a900340e024607040c101016094004990103460781000b40001060b00c03414500c82030f00f40c00b66001c0b01081101603004550654883c0b42640d00d0b96071401c0441099641c111000340000f070008d001000400b01200707030614803841030302e000c0c2d00c005003a80100340f03400d042c00f208205085d540d1013004521340d80501c8200107404140392403464100141c540e14200e0b50b046209240328210f594500e02004410040800720f8202100b0500c00c0f45031400c40706008001000d0302021107a02d4182c0e00e80348001c0b51140d544c806080f0784400100102031030280c088103030000c10b02088180d0722a010804128094050700c0f40c2500d80440301a4181020202007010f0109074148100d64020b8001000280011414402c07524503151400b003072041c8041a040a050541d120580051400640d2407030303e580095941d06104601d4290240c81d1205060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474937643 1250 474936393 474936421
    0x15090a1820030402133801230c011e0e06010b09030312060a0b0715200304110d0c030302030d0b06040f0608090111040f090b0d0807030507021207170105 67
    0x85041d40380d608100103401454003019030218200014000600d40507001134000c0718203035100301041c0f402107000301034034521201c040d150b05101080ca4100030404450000e907541d84000142c15208180c04640e486100c1825449503c0c242150002e5840d50803404002d14014180314a07145464081d0710b0000c6030040c4400110394a160024004518210401803001140d80c0c000e0283c580c81004500c00103803404080019100365401110401720013412621710204441c5000d82e801c0641c0e41908034215000030300020303690300603000750b180c010f000c40d1040007980020700204014100c1d1020140841410303400000b820032004410020400707030a00ca010004070b40124480c0700b03605000c100c07041c00701c80d1040d420070350400405800030500441142c000d0880e50460341140d0310000240100300010304172406100070a44041e14030354049540c6403a840788504c0744013009001d2020000e001c0045450740303103c0602c98404c84090300c03c0d00303846052200d40700850b040c07603454030340c24080466407071194010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474938893 1250 474937643 474937691
    0x10504030f080d060e150102071403120a09090c03050a14010b090f01021005070305090d030606050a080711072702090a05040b0105040e04030804120305070e15090a18 73
    0x200c0c6030846540d500c0c205035901a80400c105184c90305800a11810a2100b40d40120f001c218101928640d41c400240341400360b91111006107200030794076001d514041210405c84004503050350350b9401040701610000c002d80d1105412a2604810b2040ba55140c0e000c140100c264413130500c100b100000402403105401e0240d0003c14400f00020343c8035140611044c000740d003040c010744580799001c200101c21100c00b00ca402010079114010880109024096a12203a50350306041240e9404c085c0002c0642c02111144401c1c0452800400c0055001d9500d24202044420484242940b6400c69440040c8010074800d0b01464452180e100302c045130003a980b034000023400c2150564600010800134080c60002981400000c00010071140b0202440906c0b03a4066103a194440c20245800007445d10508040c000301880d00d014000b80742d500c20420701c03042e001160340c07500105c44400460051311420580342da100901001c006440b030b100c240c11007280d50342150100410f40e01d5031645284151110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474940143 1250 474938893 474938903
    0x4063605040c03140411032505010f050c0a05010c0e01020703110402071406011401080a0513141e010504120503010609090509070e01090b030618030714010b04020a09030c0501050403 80
    0x105000c1401c01e0b41c040c030030b101010700d004592000035a070040380111040d43c06682a0018454140007400c1c1000301400c1c000307240841c01d41c11400d112000b1050701c2540255230420a02c403080c41c1d1410f00c290700361a0364509000c240d4416070030900d441c5008040d070b4092038000c5100d02100064a60000c150442100c0d000407a805411412800300f0009601240b000c44030003c0e10803860061110400485010700741003982d511010018000141a66200400010344c043c10541080110149504086496a80040c40c000e4041b01c8848150034041001104041400790700b07060600044150005400740f40a080c1440b4003625002c8200c2c0c0c0e6220074024000481c010480800c02001507a00c115400005035090b203092503181d0586140d145820b0340147c1070ba50701c0c3c00e060120381c03a0030710910790891007424401015944aa200680764000c22102401200303180ca10380120314800c6d0003a0191080081c81156940d0b8000409006242203020690b406610b848010400b0f5008004541c190303a044 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474941393 1250 474940143 474940247
    0xc010b01032a11070308120108120412021212190e0415120c030c0603290102061807030b07091805010f09020a1707050c0f06012303120406 61
    0x50903003030b50f501409088030706040c414400c00002103684c180160002c0c4c0e0003205120038551505510074540741307003622007910711601080101310015604400b148510350540f000c6421000c02c100f45030401200fa1601c29980c03030300284521514a90324149036010041d5169a544c144503d0244011203c0d03091007007140780509282404100072140030703054800e20a410003518503440c5e075610070024000703501c51400b19481d800300c1e0128494a400c1941a50b8141c01003c0c00440500d00003565050080c1121031003280d00c1c041316040c450184010b5010f9600131861440500b00010001c0508100d03101c1c0700003c10545040407143c0e405405200e0489207041460100d41d828140d5510080d80480303042c10510200040b0034854030103400585104c0c2e11944c83c0c00d80c803110343c00d40c0103082290981121040ba00300c00010f21038802d11142d824516001c8203295254018070401003840c0405061100d401090041400540b01d070f4091078113401c000d402ca44ca5032140e080642400d04004141100c125040d02d9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474942643 1250 474941393 474941471
    0x506041406060d0527010c03050106020f0d2f030301170d0801140604030b0906060a090204061403130c1502010c0914010c06110a112103150105070204020c010b0103 72
    0x755030422504003981140840e6805c1e144040020000c000007400c1101d80d4481c08083d200c5501849101d0051203240081d00740e101e8012001c0d6201d0040310b05000c00d100751103410310320401c80210001890902201100540e0300301300d0361181d50f500240709032000c07044942400080944080f40c038003a080d11a03200e0601507424070036039101c5145e03001c094a4210b001804004041202078500d01e02907902c4101a10711814042c090040f82c52003a0407000290b40100010403066520000041181d40d42014071612915400d5100000413540c0304050708c0068488808200a48210f03040341550075290000c100c0b40420700c400b070325113941728410355968201450108403a54065403030f08402074890f070700014914002d0901046150040d0079130400040aa43d8140d000ca00100700e02060101501d06032490760074030041e81012403000900401d0503034813100110b00035900913420740e454168001d1040d0349030100781c00c43c40d008150040c10311303001905004011100703441411100c4010400d00e0150000382032 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474943893 1250 474942643 474942667
    0x30203310b03060f06030109090c06020d020c0405040602090d150e06130807020a0801150303080f10030f17030705090f090c0307030b120a0c0e090d020a061109090109050604140606 79
    0xb0062605800040d440c0d1004215583c1c040198040c03c0b041e40d0009160803a0300701440b20100540010f02594484c001389039545130005800300381000115000705480ea26032070324001a0042e06941d94010021004d52005c10181042d1110740303280104082220040d9003811030340c0ca00c0c0555101c075941d4200803c0d000441c0110000305106800038005e100503a548448080c04c64000035610ba41d8054010414000c05034403148094201008902012050034030715890070b50b920584c0700082c0b02081b0040800c0c200820100c0e20040348521440c2c6940745d1038020005859903110070f50403480f0307400b40c16540c51145440d4800340d0180041c0ca4615065a550641c00d0740100307910f001d4158451580690100100f00c1044403c03840c51148000030582880e04c1a41d816581019020058903000646102c141590010f8000c080540050300404c0c1080715083d2000f051003003211058120301610300101e0071801e1604094000c650903601000103800c603171081c100d040003d580f17090b0f0144082200011080c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474945143 1250 474943893 474943897
    0x20d140c2b090f0c06020f060f061002160b0a0e0d170d0e06010306020714060c030c0a11010e0a0506010504090320150f010515030405100f06080109030203310b 70
    0x100701088002003407203140d194407603d03007041502210380750030011040c46001d6060060a8006010400170121810480c07101303516040d00404041c000d0721050000c0b80040d208201c4018400070401002e130790103881d003800c040c46500840300c4001003910307801c030700590381403000c4404642900103000d072203007100d03600c11b00d6480d034403000d0800001511130003d03a0b600f42051004138003c611954005071313216802c0c50000c8815001c288803410f6500848100400d981452045a9020100c80c48090361070110000603101c3ca00001c180d0080c035882d0034400390700d01500040c1000d000380100225040e683e0303200d042000f520402c0b4002000241000e803d001c00c010721001d00b5040041d05800d42d208000e0700202c070810043c08030303040c0c41c01c80c00d0600104400d0811881c138015840003841da243c81c52a10351120b596908440e5030580c00d190780d80c0700c0760840101d80c0c1e00c00e002411080000b0700c6180f12078103001303590303410070101043c012580c08407018602c8403016003918000c2548440807031841ca0009401900d17 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474946393 1250 474945143 474945217
    0x15080c090907050d06092c121c0507020c031e0a110303040801050708150a030f030e0f0a0b07110907020c060c0c041b030c080601022a04020d140c 64
    0x1011003400100c1300c1110714043c0704007411034914002450700c50140d442c9a071112500b1000c1002c6a0721256403040311001c6441503074460700c113100303c0d41c5140511303498480742c03a0a08c0000c070031860b02061100c4103501090303800c4d24035000c4044414010442d0f507110f080102c281d02e481800c0e40240c800d440081e61100d0540300c1c5200c000d01f038a05085c0d80301409802e4860846022000840600801042034003e44080071010000d44003040d50604590301c107900410782040140078004e40e000c3c03070303441a030360a40c80318003c880290521030f646548030781c480740c90740010104a40c1c0e0100c3d03410403111801c144801d00d1280358264000c0c42ca05041c00b00340070040e404006617003468011000f451807103071940d000e1006034540410800b100303513000c083c3c010102d1303041c1003003801004803040c2880840d03a40001c0d0000c0d000300784045007114600c820740c0c202d040307c0303000c4005400500108111990041d079901c11640c0c8150140792844680d07410351b403079160703106981c112008a500c8020742842c171140741e150f004035 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474947643 1250 474946393 474946397
    0x22a0307030507080a15020901080c030c090d05010506100c0206070209090f0307080702040b101d240a030b0109180c111e24040807050c100915080c090907 68
    0x3000341c880d1070b002d0800303e094001d4041603203c42141404c21030a034045800988400c2021402e040e40103000802645c805400480f0000000c0086508518207808030350409000400d0607001084070b16181c2d010782021504c46108192500c0c3c41d081d210701403111801459801405a45802c50f182e0811401c440054825002441052188550480200700401c422402a64803d0302c8035070510411059480400e45e02d0f01070b84948004803611500441000180c0b544400600d103102000c0003c030346943d4040b81d814113001200c001c107000181c03111004200f88082d664050103008004401503038001c403607108025400300e11036009100129a64051081c0c0c4010f481d18255410100002c1444d02c3d0464203052064034030212140c04c5054208180d000303800120b00e003207a010000d15030380300c6420710040003e05920000a41d040070040d00340154044000014a0303841440c0384d4080051040000d8003030140400801c01c4071610300b6000e0000c0304d2007001b51040c154a0003200d003060249000b070207803080c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474948893 1250 474947643 474947653
    0x11090907020a050f0606130204140f04020f0708040504060e07050f131205060a060e06060904020f0d02040b0a03230115110607030e060117060f070c020613031101022a03 74
    0x10000f4014400c160424a00c14010a000e08100c0100f05410100700c0c10150040c0c0704001c20414504181c4554049800c201e810243c0d948002021034080c2c420b2442491542ca8001040c01c1004540006002601c0003a20108025034548000038100003040d03402c078011440510441142c8074591004042c000d13500c80315200c00c0f5039240064a800e40307180104440384c1e080102045071104a51140100803c6442d00c07010140c1029808a00710b42700b42003805004903000a0f0f0300b001d5106402c100c50301502d82000031541c40707a8904451900d078200110440003c0d041101c0328a44864905154400c100040903481082e481d00e0540c0b42c40c0c3c00810841d0041c8003010072180f50254043c81400e100c0c010507180824281c10307009000d0f003880c0b0140c00c551030f40c00040c020038181510014401d41d204040c0307400d52845843d001c800351a003845100000750301403000112811266a00200d1508582c400e810b1110360f0642040160b03103511400c00b083e01d0400d0004c0880303c2003000b80c4503c4001040190070b0360 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474950143 1250 474948893 474948913
    0x403140f010204090b13051005010f090807080c01020d032d180501020409153507060f090e13060b0d05190515071b0201051207080612011109090702 65
    0x41d00b680c00c40ea0192204a60300e210300b00c56405c1c81d000c480300030140314104222615040302064540c003001e0083d641000700919507421200d000d15803c4d07020700700c160221000c180d03a914000d6500c41c4203144590041c050384d9540c8012600900032003555405981e2044c500c0360300300c144c02ca2041c150134010400799071201035480c221a10449a0b29049002d040003580d541c0c107020700481034450708400503101d4204440b04219190301413242800800ca408041814090000a2414415a96609841a40076100c000981e03144c018044000c0406030b600d0300c1c40c01c20b0360ba00580344251070844207404810f003442880c1c0c00180c1980d2250b048480018160f05074054261a00c0d4541000c0c815a10802c891030f40b90403040c84000c0040b000744082c1a1102c0c0070398031b401000104811000c1000b007200c0d8460050150442e0f0142007a1110000101c60307910300c40c504880028400304040e070b00c0c1d03405a00c524200c15500001800f41c8420b500d00d1312400c1e07207091000c1c01401030401c2c00520340780450080030200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474951393 1250 474950143 474950173
    0x5061303020f032b021908090601050f03120c010b102106120336181107030804290a05010b0415051305030f03030403030506090106080f1b0f0a090806010308040314 72
    0xc004061030950307031f05c403403850300368022480c0c00b42c180c101c94480c0d03403402000d46184d03a002654a40c0940780c44201921803200c41100381c0544145100264029030072905c11280c01d6106200703000c114001000c03130f00616034070604202200c4581c003070411a5018442c060020a014004c00e680072140f80c081c0d6046919184442d08103042c046009952102c2c2c0440200240f401800c984600306045000c03c00c400e100c3d4000e50106440741e41c0d4014140a1f03010001824404205200ca1491409241c040007402400b45021251a070484081c0011340c60038001061741076090003a00c080d9481080000e48201c850001540c01c3d411900e840003008803420000300310758034144210720519540c04010742d1a42014030340a000d440d4003c2c201400345015800410070241c1c411190380d00314045000c50901c5480349030180344498071490044803503c4002070b00d49030024000d0003c1c80303980090366943c5e4a06842c0c12503507468040a20016008200c00c0c402070001c80c150002011510000c40c044400102a401d58 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474952643 1250 474951393 474951427
    0x105040507140a050a110d1b0507080d050304031106060a1e0b0d020405130e0d08040f0b040b09070e040b0a0b030718050403030e0f1011040305061303020f032b02 71
    0xf001d40026004501c1055030758100300142100100880500601151048024255045090a0300a40103002d803644e040c04400e01c051b8010f8000a41a03507c2c5240c0001d000d082e982c07041d5000c60015101d904c9000380030b80d02046160091071f0080c46010060324000117400e40805500703501451800a03100042c0c481854801003018034500314001d43c4861900c01001244010000312140881c24107007195610000810907522442d01c506007195641c40b0344c14200341501d90402d00618081d40d42d07060106001c0b0325003000e441400000b003240c81c8581c0713481c10811408410358004120441c564086180ea28594100c4800c101000e800c8501b03007a554a10350441e02d00703000710401d400e030fa6403080c001495890300942c5149690100200108001101d030700381e543c00c0000d5805030141d52641c18011034812402250300644d0003004a580c1c9041c0182240b21080841c0c000302c0c0540301d040b080381e040355004001d459002224007915100003008002c56000203c900008120695003006003c0c00381e00e680caa = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474953893 1250 474952643 474952657
    0x14090411070f1412070303110f070507150c0804140d02180a0f1407300501081902030a12020a0b0f0601021b0f06090406270501120b010504050714 64
    0x82401e4180c040d400c040c0b068081d070310f00314031080d0460500410385a8280c0100c4000740d5040c54000303820f0485009240b03280c001c62007070711200a8001841c00078800001640001c1e5003100548082140f003102d800d4400189950000701046010b110800c0603502c4020704016191010380003410101c00b0341c3c0095000ea0203401800941c050301824404190350505c5440c040c1c8103501c108201c000740d08140b003000c0c0799005120408000a682c03680c1c0c2044100ea007506c008034030128485507450303801c541400250109000e19001072144034080214810960140d000e0107801030058081e58510b5110030102210301d03092141544501c001e1280060a002c0000d4858949810f40305042d0402074002824a10040250040741e1741443d902c02d6a5503074284440b90141c000ca400c160384190341c0001c0341c06412140d1121040c03203190380080c03114804140c070030f1555400c1e0b450100166030300c0388514024036150160140903110100010701c818101a0310441d000600c60905003892120b410703e00c12554806a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474955143 1250 474953893 474953903
    0xa0902071a09100b01050f040312110f01091b1203050307030e07032a080d0f0c1a0106120c080c07150914010f290a18051006020a02011409041107 64
    0x40400501d60150b4810f0504400d02443c02e50326041c001c2e860704500740980d009c054105a41d50400e441490301901240e42802c050303000b0fa84601a440e001140241490b1800b41d403905c0120881c24842c7c0000781ca40c0703060f03407003a0b00c54900504481d2402c0300c0310740009142c5800c0c19542d00c10010080c2040101000541c821500c445808816030400e401c84001091240c2d2078818440c0305005042011961065400c0301b49080d4004c0f64101004070b8142003401009000300d24411004046510303107003105816100f05807503000c003005803030000c5030442c3d0600311003400084c0791070b0110389002c03008401040300c02d00924011042d06003c0c52184100c5031a410112017030000d94840d40d0720304100380607541e0141071a040800100d01414518161f51a1680310002c009059801e10080c075a90543c02e200030303001c1c2c00801600c5220a426010090038280c030b419900d01c000c2600003d8140c40041c81076400d680c10b81d101c0d50788078050a034000c1789810800d6482d0f407040d11000d00c480b403c40707080d0251480341c4c021 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474956393 1250 474955143 474955153
    0x20d09020a12110f03030d05040b0907080a0b0411040906180b0907050906091e09030903100e03091e150315010c080712090b0c010c090b04050a0902071a09 68
    0x103204011021920703500144022004905110100791252100040240c065880c12040418140024154402c070382520701d1440ca07060601040c0610a001e542c42403400b5411a00115105e40c5426503442000000a001500d030000040014180e5203071080344480240c404036400703896644036001d80340e00038580c0f01101103810792402408850140d081d04051031001403d00da90a080c0820610040201501c0c056400700021642d40c1d0129000380c07101c042c0c00c00c0d0340c00d907500700041074a4480e07029040052080c1300e04140e03111020054810541d000d0b00403c0210f280c2000082480190b0b86600089540458001030030510b58075456103440b020303051481e0b2550b481c50941c1d08c0e80c128030240c800a40c100300001c040d40340010150412a00b06c903810184280c10804500710885002a254204c8030200402090700b1181c40015017200c661070415071505c1c418036440d007140d400d040c0124416a5800041401c0804c400700c00ea43c002c020441c0038041c440b4008540c10b003044103440041c0d913041141c8e070003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474957643 1250 474956393 474956411
    0xa06030c08010e0907121a070f1e080a0e0c060c01060303080f011d090a06150623091c0206040f08070b0a08040204020901030e1002040f08010506060724020d 69
    0x2100790802d025160b83e451072280790502c00d284076a04c3c2141d014030440441000940c9003131045900c0030300c480000741c222000b118680b1250040c10030050b00d0b1400c01140c00804d078002c41d524905100c250420b11075942414a646074100000581107114451090380215903045c0241e4460400402807500300c10000f103065483c0d0b1600400402004281c2d0107030412038801440f0b5840e04442001d103001700b0170003071030454841d41c032170710709041031042c0c02030046242c420b03000641c0380611507000480d590381e00e81c481c0000c218406000040310004c10650000c0e003c222400032413800300c20908620041c8100c0c0107a64040d81d0105a00382d10a03040395801d00305c540002c028490080189801038421045010304201c405000a05003803c0588028070907500407511004591081e40000707424808502194100301414804c080294802c0c02142d0340da90b1942d201281c0c69005010301030090710064141494600152078014811026100001c06003082c000e100c000d8600e40d0020b0305056200700400507420030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474958893 1250 474957643 474957647
    0xd09050d0e06090f010c03050c150f06010206040b0402100909141006090806040f020402070b150102010b040e03070f05190c2301120b010219110f0111030d020c0c0a06030c 75
    0x101c011018441e1200700441c038880e032a07440b41804807003802e017071140c0e080700c4925068415004c2c900412441d4401c0003901c1d007920044400090058031402060715098841c0b0740120303220141198050b01300381c803600102d001402c0c240103030303c6140600c0c5443c060603520f407103040040c1d40c00507a4001012081400340500c3c0035000e84070714000c100c3c9040c915101d92418640e1500c40304001c20282c00018107059070703010354546030111110035500c031005880a00d040e4600c10030f0340030300001850044d0700c0d0065160442c101031003481a40c030b0f100d030003d500345603ca0392010f040e40c010000885a0340991700c400400128101c1c05415034521802e00c228925062100d400101401c0c030085100a6040700840d44142e6004001d905510036418004100440c481c00180e14182080701501c0c035403103004c3c04c0c0c08248a158581000442d20444180c145000d1180044510031000321f04e490b0f242e0020402070071100d0f1140c5c0100125a0030f070341503600c0f11002900091029186900003000300e0384070010242c000d9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474960143 1250 474958893 474958907
    0x112140603060708070f030f02120403120609020f1c060e010f091505010f0c02030718020c0f07030b0c071b06050715060f090f0b04020301170d050703230d09050d 71
    0xf030b0003840c1542c60303454044070080c1050000309850742415610341141c0504041038045803030fa504594641b11550a15140c010300184245410a40961514030049503c00f810300031103502e40030300d0140c83c1c00c102081107012000803450381d401c0100c940c0d42a00040140c0000480c030300804501d18107200071440c0c03072094010303107002032810191011100b02c1409540e801500303590f1b01d401d00d440c0055000c0310520100e450400681c00c100110080302aa9951902c0a50001c0c80440400419501c200d401000e2407a45d408035808001c00100c2d005000948038030140c400340002ca07004115140f0078031280351142040400350b07003018000030b20000304c00003170018880b000041209020f02c104507180c076080c44200002402d0280e600c113983c4840240303a261040e03811002c40003c00800c02c40d52940d6840d0f881428541035007504415024015000354010b00400136502500d0b0961a2004220200e03504ca004002507030490b030300b1428003441002c0107441d00748100c2400510640060956a44a0301c018103a8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474961393 1250 474960143 474960151
    0x90501090c080f070f171e010203011d0103050706051617030709051e061b030d14090a03080408031003050d0e01110703152a0503070305060d0203030a0e011214060306 73
    0x507a001d0ba00402070820045114422908075101c001b610380f1403200d5190030503c0070700b481401c50f2a07200742c0f88103951065004504031014000901f21000c034680f44201160000d220182c507941110030200301c800c4c0034000a1541da42c0031140008034002c540d55903400b081e0604940e03030b0b520350040300301702905130880110b2019000484210b9010040440301b02000704402b0b40c6039000d11008140103804031b0314031041c0990f82c1003403001c0e43d464080903410309000b8440ea00e9a246034040e0800490800710300891541d080c55099614610300783d4482e112041254800361440f400b90050190002c0441d00074810300b2000903456848651300f9500c1c034001091040c0921200f00355810500003000000c0704c04000d04030403004842c0119000500100850403c50ba01c203a00200380c102e20220f03a8144d40c05001180729501c0303500c0410064a40c030381889070b220071903a070082d0540d10411184030402e0191011009019051410030000420460524141d8000c0480e651755600c009040c02103a180c1401b605503c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474962643 1250 474961393 474961423
    0x30218040203060a0b0609030f0c09070e01020a1b03020402030a1409030a0e010c050a0813030b09060408070222020417060a020c0723301501090b0103090501090c08 72
    0x20a040c0307900040d403150b10180100142da60b03943d02c1075134103031244800c0d24400300e002001e45410402e000403481d1641080920184900d10300400101242c6c029101480342d41d00690080003080642d035559078094003100d44042c0007045882002005a4884c0020b5110b044d48103c04510110000008440c5d1100070b03040584a070028480e00c1c0d89070340c0c000c1c1200d600b04000d10305603101903503504065091881400300940120400aa090703844843c505100080b40d210f21000c00040e41c5800e0300c1501ca14056a0040091408100642c0036107000780c030240281d00340034000480f140d4550820030881e4071a0b8488050740c1555490055044024050b0360362000c6880810b40c58854000700c100d80700c0c0d030b090240e6a544460700f42c410070384501e00c500d003130407070080a0700d040c1103d0b0951500a0441e2014a040d0204a00c4172881526034100810041150078401001d10550390800644c2c402030458581690304056850413007038003180c0300740a8619043e004240b121542d60408811030b042914450030601c2c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474963893 1250 474962643 474962689
    0xf03191a010e0f06040e09010e0d020a08090103020c03132c0f0402100504080109051c0e09010b0306131b1704150b01050c010509060114010908030d02160f08040302 72
    0x140603600038039150305901003190f03806044121040007030340328012034024281013a4140c4c1080a04801540f0482c00a078140c000c403000045000702c22030380c682030128000d08622060104520550107500030b449407120f480207407401e0000c2c05198000c40c600b01c0e8403c1c02e182040e0840100d010134480c800c143d0328186c01010000c180782986800014a401500013400340250b10800030040e40b090040c1c82c05803220a00178800c11449003001039484040d03c42c0c80085d01014020340c040a8042d651501e04072002a00781d0100d07a10b8900411100e0300b00500098010b030501451031030f030403207900c5001c8014450201e5641c1c2d145140310010041c0c401607801c80c40f000b440782d0503c00400c0c042c0100340c2945540e400701158080141004841c54090410303c0b684643c07d1106112007031901190b00d6060399480705d01e440b001d1080b1401111880c02d144100320440c2c008001d40d07500480a81c00801c0840038a00f05404250341950316110ba00d20304101c2a210494007050500451030013202481c003014140403440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474965143 1250 474963893 474963941
    0x1208150603060f040908120a15080c0f031204032009010812070510060e06010305091f09080f0403030203030f0a0207030e0609012106050906031b060706020f0319 71
    0x50080c070025140303921a41d4001c003003585a0381d540d001180069401305001d900d644c0c2954480034400d000f99140c2c41c0003820640401d140c0d6406003441c508a88081004255035080314043c00b000303040328200c03103815000d02c409940c0030380c2418008000451243c240c1a0031201402e801c0c1000e00405484c503481041c6030001000010f80000b444000c0c0200440410354641076450b12516201c04100c0400701c2c607050160000c1c011804400c094480d10302a02c0a00640e9900315100d034644c1e10116101c6d2010625014a130401509503004402c040e111780341c0d0500d0841c805a10340300c5908154001c8005034000800c000c00303251400421500f0552103601035083c80415a00034160f2107400c01c41a011790804101c00c0e500381e00c039032070507010b103d012041400c441d00d248811101801d802d020f01802003a00901282560400040c13007034680c0715080e510784090280c00c3c10400c0c00da010000944241c2c0d000c0c019094070f52401c1000310300940035031410a852130311071507224082e030b0995000303541c0400c4840d02e40f03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474966393 1250 474965143 474965149
    0xf09051f081504090348080706140103021207030f03031a1003290306060d0201120516090b0c0709020a03020708031302150301060c0b06011704120815 66
    0x40003500900e070429045680c0c4050480c0704400c10215a95442410320020318245a0007212400301000340103c030780b00c2c034135980020a1040c2c0032102078081c0e6a01e1010704581c50700c00301e1100c04450740304070f0489140a1054031040d00791b84900c0c064000200005004008500d490055204407008410262004c0d43c6181ca8900095800802c058141502e4622900320000110802900c03c00010302c43c2c0b1440440603002001090f002440d2002d4070b0442d80104d04026000e1302e420501000180100080c3c2c2d0b580003802421810040102e06214100450403000310060045601c0348410000e292402250000000c0540720720b940a1045131f01c04000541192502155190560310a40000343c2d48041c00d02e0101d00905c580c141c00b900702d041c040140455039a0390740902d40e90382e0088510209146505040c0d03100307480280b0408020500e20b071542000a02032001c1c0c41e80c001814142a00e0f128942c0144080301d16080390211041e02c5005440c03031142c0c1e00140301c10303003040b164941442291450004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474967643 1250 474966393 474966439
    0xf090f23030d020c06071a1920251e051009050a020f03030f0f09040f020a02070e040602130b09101107060507051606020d091e05061b06070f0905 64
    0x4454091007001810405100c18400040756100011100c0c0303045280410722070f02c11415600302c0710303002410b10f00000d83d040311041400c0324804001c48000c1c585240b2150134540269075041607a82c40d0078012b0400b0100c2d0050b4200031641c0794401031080d0361502440c149003800032404800b20100d00c2c2507a250301003400021100c101e254155010443c0102140004e0f2441c0141680e00c1d00c1701c180003808268031100c50010b0a0300b50800c1c1c03014007902407040d105000386d010742d800010040e4080002004a044000c1505402074010203005141c601e8200e24540ca0849542210381e89080003d4030000d43d0918085003081c0003180d18240b595882e08050350740d00c4030180e00c02c2c0401c2000210300d90f4240a818004e05401c2000031030100800c56a400d0702035184c00e06a042200418003100c0002350560f04280b076001144806c1c220381e0040c42c00c0200304480b90f00841c0c444c1c001c0031001a20b030720945c0310800c0761b10700415164850700205c07101d000c8000e000c0c14a40e00024010340c0c454030b885071000c8407240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474968893 1250 474967643 474967663
    0x921050711010819151e050a050306280207060204090902011205091b0f090901090c0e010e01171905031e0f030403030b01181d071e0f090f23030d02 65
    0x901041d0f48040c4480081c1d15038140d08132003840b0750b02030a091510103811240c041101e10030741c8c40c41c0e1502e6070740003099103c0364100e40380307600c01c3e1003c0b0442c0100001141e0080c0c640011020042c100102505e80e8000c03600160050b1a04aaa800380134081d5a000408101149010401802103140001c5001d4803152aa403c800d02e01001e43c21007910b5a03211102c108007441c020380b1103074180ca0300e5580a80030313015049041c4d0740d6900380840441c0c4480d10b0040181640c0b40d201c0c049006919251103d8612160300001c041507004030f0030701400315001d8148002046000d11700554a65520141d50440001584040c0401400c02c200c0358043c00341c10b100b9aa403094042c10000b6505484800613914142c000c0c0c0742a8944849240c04140301c0310351042d96101c2542444d01c18001d40e5000300c06c1e1903014481d5a21010402a01c1c0003000c901d2140d14101c0d82500c0b145002c138245a03a41c501003011600342c3d008201048100e1030010304054543d03603039581200d0100c00601e4058003440001c2c0d00d58a60304 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474970143 1250 474968893 474968941
    0x90a060605101706040b06030c0702040b0d1218030609050615030a02090f060a050909210a02061603020426010c0206060a030b0a1107030c0b010e010b090409210507110108 75
    0x83c000404c03903582d170b80c010f042c0000003400c0301d0741d070349085503076998154400c4400700c3c4958035207c02820740e810601c0c10500180d61007805414454105032091300e040c1d42c4220b03807120401c0740980c01b100041c150b0040c40141440360000f0295070808000c1e0b048000880c020302400381d4802c4d4600005a6994000340d5045005074080c42c2c0d40792100000f040ca0b848154014941044041c2d0910035007440c0091003200c00d640340400c1c002801501d91058020780306003400f410040c0d020801150303844002e84141010014a400d00515055881d1520500e012000300d0b052b10090040740003540d01c403000c0c019806d4094103071010b000c0a00e072050000380c81d2002800041c1c2500725400003d110550700e6801005101c5030700e01d01c15160b039190301e4001c00c1c0d41c2694008840d0518004000501400c0512007203050b5402d8403025130401e0484400c1c0b0006152214091f20401003001808840c0c034120701c903440b10307141e081c0c2c1e81503920b4005e414204110b400742c09055040204210400000c800d91001c2e070510180c10b0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474971393 1250 474970143 474970187
    0xc061b08090303040515030403080a1104060e0f0406060e030f032d07060504080315030106061e031404050c030d0504230103020706150503011a0612100e090a06060510 73
    0x1001c00b10749580101d0700180c1d00007121008181407062400003540c8140e110703517540313641caa6681003558150b400302050304491840070300c414030031240695a1101c503058050400300003407031144000f806884c901d81c440c901285a02c0c6840e40d4030b0805004091412018000461500c100010f822071681507800c0490071028900040c40c0700c140c01d01c4201d40c00540c000c003003401a4141030405480741c0e401609c800466031003601c40901c0c2411306014001c11a60300d6150f6042c0820702e40c8905c1c0050401e0f41940e410503a44550840800514100c402d009a0089008148011980e0181490002c40103400340a02200b07000400c40300e6900c41020040352a0a84c000c0c404c05960380041c0d000e4007074004000d01e200d003040e01c00c2c1c0e48076945043ca0412618120700902144580c2e600716070959007003801e5030360061000c01587c036100701c288000320b40000c40351a208540316a68030341c61040d03400c1a51203002a4019800b4075081c45840d01600002d000d040701e000c106025043c8010340161400b818500c204564 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474972643 1250 474971393 474971407
    0x512060a09080d1e0509010b0904030302030c0408060108010c02120c071203091d040210030c020307061d06040b0402010f09051008041b180e07211e0b040c061b08 71
    0x2a180584040c2c100d211000d00c01d501c4d004040d900003c03d1658082c012a14140c0046c0303150205004604002c0c00251035518a51079035102140650b0000701011440c000c10000010341c8001000114020320644000090b10700260900909050850381035455000c0113002c400103600f0003081032421540804090329540d2400c1c5410398400032143e10500000e440300d4003903801d070307101c5544603441a4821190401c000343c3c42401601100d040880603401a4003c0c001640002e02550041e50705142c0310301c1c00e00413020008050781c40e040089400b110b110014100340710440d42c02414880b0701c00a40e040c0504902d051030081441c80008007000b00c10003454a0104050040111000c00402a002c114044194a030300b0300e00000e44102003000d64480c034103080d60610f854080342140075240e49202238040c80022401008940110352420340c0c840c0c417066080e400052a1045600380944117030401007241c0344c00d0410601d072310301c03a074004001d1040400844840300b420b20468116245d0280106480d10740c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474973893 1250 474972643 474972653
    0x30a060509060106140a050c010b1804021311090910081903031109010816030b040c180b040b0a12141510090303350106050417010902061605011e0b03070512060a09 72
    0x10ad0054030681003030318603090112007604110094400d900070307a80605041070701150702040341c01c80220340a060805001c0b0301e030a40340007068140c00c24401000e480590791212407450030111610a401905091044039804054150080c07081505040c0a96070500d1072907c006001d0040040c11500c00c0d503d55200e5111050003035124079038040c0058010040c500d2200009051454158400d038600c02c0301e40390000304003030b00300c04076410b45800c0000e080c01c1c4182404140c40b504240b140340000e898442c4560360302204070b0482248914803600c0c103c0485c195480030310000001c0450048200b110f0f41c6000c0c40800d8100b203158041001440d000d00d644044140368100700c0741c81c183e030f6450040c20074000085075a8802c01500540e1455080300540c4003503081c080e1308036402e0920094010105000c40030032549a803005022aa0180c0c00105041c403049080680054030211038644903980c030300c29000282400c001d0000544420746611120003d4401515074070800145003440203034540900303900b089 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474975143 1250 474973893 474973901
    0x41e090c0e0f21010f0b030f0c09340f02011a061e040b030601034d0307020a050f12070b0601030216060b040c0503040b040311010b030a060509060106140a050c01 71
    0x2002540c10000400c0c0f02d0190341d40038101801e9085401401d0034030440742440e000c50303140281003c400040014003140d00c00c0c004140e0307000707107a2410703588044440540003400d0903050507440303900300c01c0d9591800b401d00042c00107205010f50a0031689002c0380c0079100c0d01f6421610040020854201e81c6546a002c40401800281c000180700c0384400b040000d20394580502440c040da41c2602d0031b010f1904440c04006904c007083d800076286810030465480043c450354000c2c03a02d0703c5015002146c200c8204002c4400e41d20540d10b40c001a44200d154505000d024840404142000d0000e008521084030451005014900b0060320040004c000314046030700079411079414007003040395070303903c2d1000e828060002c0149844050259051109884845100d01e044910459001e85040c80940f5152001c80d09255508030840c2c0b259038038400d1494940e0100700000000b440340300f0110726443d1a030780450070040117074403010a1241001040148010380400c0c0c03040d0341100d103401510f0300e94600e0301034050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474976393 1250 474975143 474975169
    0x317070812060625060b0d0506041502091f030606020c370611070909080d02090406030503030c04030c090c050901141e030405010b0904020901050d080906041e090c0e0f 74
    0xd01a2080070702c0c1820741d48001304011070007813a0401480d039040003405103850021500070029081940042c0c005600b200c5e80781c3d02440000401820803031030030003042c031b15481030203103000b804100101c1e0f904080c0d15000b50406001c10f803003e0410312920348003080d1058201c1042001d00300f100124200080a410040700118a600b1024180307280e4070800034090140300c40700105603001c3c4075408298800f0314080c01c4801a07100680618000c0032040300402900600343e4a03a20070386405c5d00002084081001d0742c02510303c801029a42c0d0320f140362410b401ea4103580042641400c19500e500c00c3e982103000d403150a4000e00700b000c2d080380030441c2d141d03e138131401d80310030b440c1c00c006403100b00d60185243c0518440c6109100801036408440100000040d08650081d40100e40c280144400e080201d09c009006109100eaa0700740600500042c985800c180c200c1d003d9940600c0b2600210005043c0d01401404410b100f00924070000030000d1800813456002405000c90707000e12030180c0c90b48401d00c1c01c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474977643 1250 474976393 474976417
    0x3140f040f09051e13080f0a08010812030f040209150a0806090d0207050d081b010207051f0b0a2612070b060a06020307060506060c01090605011802120406110c070f03170708120606 79
    0x107100107c7d23801405c00c200c00c1c00740705e20074400c003602d0401c41c425500c02c480c0a007044c18208100399440c2c0e0308000000f40b000304140540550000c180359652202c881003c01b0f070a00301d0140069107802c9000703c0c50500d0ba0344240b811980300c04010004d94075070143f00700c0304942104590b030b0345e40d195001d0390490050860b14240d2540c4000b4401e0180200070800305030040c8207503030030100c00b046448107106503000720710100d80c080282c00e4200415801ca07910042011183c401c480d40350360602c0706403400e24106804000000c28000360180c02c005031390300c1c1d0b50b034080022182800308030b08052b40251b89004031b200080c001a13958001c903145607500d10a5450b180c440d04028000d414407440c184016110070b1158841c11000d051039100456038600070340e900f4000d405841c01e00d036a80e0f41c40b0745003d00190702c4005140c0340c0401020140c801e09000b00c9025241c04800e44c4020352071482c28088400c7c012200c030040580c1403203588001019082260f072000811000b41540752683d10009103240320702d100c5800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474978893 1250 474977643 474977647
    0xe0714090901020c0d0e0a1a09010f181404050609190b031c1e140f030c0403060e060114012c0a0b0318070f1203140f040f09051e13080f 60
    0x224451380402e0b0f40003001d005607140c070983c1d0780c2c03402180e234443d21420b0b06001241050007a45240d5124140607aa140800d00d0207510448444000c91610003040c0c010034002401c190203000a41424001d184c0c1040d01034980c10214606501005010841d41c20100d200f2500c1d4404400155001c11420410320000c6958801d01c1e48001c030040d01c000c40411138103200c0c0d0506640400003500950480d045030140905940c580540c894420b8141d40c401072407054588010f01000c00400c440b481544880c50307210000300800d50519992503580280d0000382810061401080c200b40500c0805a090350207004454031205280c0c400011420000380d000420200004820000c0c280700c82c2c1551000084858103a070511512030202c018018014080c01801881c02c802c800002440382c9203449403901000d203c14240014852081c0e09503100e50302c400c518240c0c0e042c0034400384070244103290b0444919516080d504120714100940c5000042c07900034542a03001d000c10601030041c00f101d1203149070140080d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474980143 1250 474978893 474978913
    0x606081203040201050f1324020d08060d06020c12090108101d07031d0c190b030705090d1202010504110616081602041401170609030906030a0b12010b040e0714090901020c 75
    0xc600d51400c04400d180b07100540407603012082c00424104030340c842560701e603001542c0c1e560600c41c5110f5410001c44580341c1c208942a000c0742d0030301108000751d421440042e80e0798140c5e40010200e91000d441300c40030510800302040882414000001080f154540c1652a41d4a0305402e130020701e102d2520b060004120561840300c10008201000d000404031040d038945034001140646034140e0f030017000000c100400100d080603000d50050030850b00010625200c0000b650f0b104045a602d031003104015079160824402084071681081694a405442d01d508101480c21032249144000801415100d40003444141c000d480006004500341c001e04148042c0c0c000740c868182c000804d205540d130810344040100a0303c54080f514a0280660500550912503a00c003000459400605054840e690f06e4a8215207a1118601410a04071a80c00010360240a0044c0010345a0b41c5206003820740010341c0c1444080e540d008803141880081e01c04141d140d40b44c215071070080c841c1c40000c46552003804010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474981393 1250 474980143 474980159
    0x20403020409030e101b080304050f15070f050304080a0809120414100305040f060c0903020409060b042a0305220c1d0105100c17040b070606081203040201050f13 71
    0x4403100c007a0340805c8101441d000441c0c06820740380404082070344080019010450010166800c54012400d440c8120408861070303140260405c400d810300c03000300081050443d003000e06050070380f155013005480c41c6425500d00030b0920500900c4002c1c0b0120720041003101c03c04109400d01a528414040d5646840302d43c1502c1012801162608c98a070704000350008038032138080c49018692002036907914003240d0743c0b1900a010031b6100d000400170030318000009a59640507050000b406003100045030f09000d0144002e8401e140540420030b90518940c2c08414a40710880398002d1141c903001030349031600c140549120418680000351882d40042d10014442e00100e064102e448440d00c114050541d6000c1015842007407103902c0d400715004070884401401003014040a0384101d020320740c607400750703540c2407555040b54012081d032034408140c100030040305128100103850b15000500503025400c80d424a14440180006d04002c0f010810404461098054504030466809000340f402d07107400b08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474982643 1250 474981393 474981407
    0x5040f151706061e21011104063011130602150106110a0f020609031b0f031f1e0203040b040201031a010e121501030507030b09070f090f02040302040903 67
    0x29074001802410003041e03a602c1c1000e4004000342038032480d0001594624104480c103c00303882122443d203a681180b4901d50b4080c803a01c6004544694801d441f00e0078044014503404008416140c000c2d0211854000d910003400d2241c1030001621001c070720512034504400c520300881a84800c0b6221715a4041880340d00032511001c141c484510000f100d070b84e110000c030b0703048000e40410f102a400c8203503120045450301e080d614205001030080b602d04500c007400309241201e2600c485445d0342408100d00784c0362502c8004561040030441c010000080350b26528800ba5860b440d55143c50f55950f800110356030040d2006007840400034200719101d00d07143c100040d400d00120f0303007240000c1ca0603a198500300341c91038610f051500184d6400d001c600d003000600c01d4814a40d800da24080c4501d440c6821050481c0c0380700c6003e94424030113082e410745503203482800400d010b00300c0d188070b070001441071006550b400495000c491072031602054201e284403401009100e46e801c060b401c0750600c410320080c1500001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474983893 1250 474982643 474982679
    0x9030b0a0c0f020304030c03021c020603160801050103111b07180522110103050606090402070503070b060402041514270307050609031b060f040e0f061905040f15 71
    0x4604003200c0b82240b04a842e4411070100811200c4014000c1c009818071302c2803500c450400b000400b054182a40020328541c20840340b039a2401091445601d0407648081c00c14010502824140044280900049000d000e02503080741c0b9241a800000030040341000b41d00c008103401c0c040e90829901c000d1300074014040c201c0f1540d0001d066401045c0c500000f203003003a0101500405100d001c142090011005010060700042d03008800b0b01c444616540c0314801018a94802c02c000c41e6294407915060030803402c0141024451481880100144411041c12803054111441c19100c0c0c0345c2550303800811406460220110821507001d02c1c4d03054410800a142201d0044048500b400d03078070005c201591003403007802a00341d04500810f1494007001583c40d90044002000282000c6001c042c00e005a007003a400107019915a0052007400300d14640004e03002041900c6140c4c0040c0c085180c07c40c0c44d8400d209030740c0500da03108114403140240b036000c1d96070038820020b1081d0003079907402007804404c0c0c0c0d60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474985143 1250 474983893 474983897
    0x60e0f130c020a0b010608010e04030e01020708010608160918020904030c06020a0905120d0207180b0301050412140405060708072105030703140105030d050f0c060415050c030f061009030b0a0c 84
    0xf4002003030b803c7c000e28480c0e040762106082d0303001540d5a47e40441d5401c0f44025014150f220303562001c40c40490038000e40c4045c04030840100600100d0301980401041541d201a001c10b00e414101003400140c5190700a086806890390325081e00c1c3c0b40f40840f880d4418103c064401c920105a144045074003030280c0003100e0048400948405032490000d03154803000781150050b0b03002c0301c0d01300803041c4800301401c2c1850021400181d02e030b4003100800d088d240c0031941100c0c17802c0c03074a46407010b0079049204a40e25600f0804050f0502d410031004c10014498000013800b82c1402054140c1042200f902203114401d504880c0c910500d00540c000e401c9810944041c0e0100c0d00f072100a4442c100201c4507a4100c0e01c00a004000003c2c00d140155103e520200546040d11001c0004081d650701c10401203002d03034491505062040840400c120844802811800c441d11013003050004411210b06426007290003140e0088400401406c01d507500740ea00d40c0010600d0410008014030f4045944c80007040e06482c1d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474986393 1250 474985143 474985163
    0x203010513180209090c12010507032a0819020c0a2d08090301090c1202040c0908100e100c02030304050105060102060106050d020304080d0e030c070f060e0f130c020a 73
    0x800d00c0400382c800d169004420070114100180261034201c0e6003540081c091025958601c0c410302c0454080180210700305144d0f074449040c4030310550302d841650010b10f00c40078407207410761000e4814106515140d5040d810800c000011072100d0b505940c6095034104503107001c664400302c0c9442d690b2682010354041e201c00640c02081109402219000d0205034012a07164070000401e0399881e01d150080140310382c15658603c105030000c1ca0b005d0000000d410308440c032001540c1030388104000c0d6107883c10070700f04026540101b001003da0018110800b1a41c145010800f0215821b01620700083c4601d14818242804500d030100368002c0003d50103a400f58009201a66440006a030369282c288035040c00078904000701003600030315501841d040340c81064914070300901000c0e0740055803607214003c48240c00010790424401070411600005009840004e1082e6150a1014080803407072124580910b0081110b0316407a03844032420b017803113250300740708012904520744000e59507503d80d0f008803a00e01d08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474987643 1250 474986393 474986419
    0x10b0a023a0e130e010f051e070c03050a0509030a02150a1205010602070e0a020903120405180105100309050f0303040602120f0f0406180506010e10060e0a03020d020a0308030a02030105 81
    0x108906020301082c01400c841c540d40010810000280700c1d92510401556880c146c040b0714040034000e69004112003680440c00c02500c900c40041c003200640264180700030718992800090300f20302603425154144c282a910f4030902c0d030200f0f00b40782007020000e6101800c000190b8507070408a028100310083c40c0c0d121291585102c0102007168000e0060001603403003070343c007040841d507884040781e402901c40c107016003099409030102c0e161840380d88102c04010f5001c1020701646c101580703c065110f545000b00c1c2d81e5545080040740741c54201c03210803820075444200c0d210900000300034a1003a050851f049075a00c1ca0709040540080d088080a600c0040c80300c1b010a5047c8285200c85010300a4a0010071035622241d03038460003440ca40710340320b8518032043d0200d0049201800b00328000c140882410006103080d02c003880c00701030650040010b0119000405407291680c0100c141580e5054413a161031076490f000181c2d0a00b060750004080400000403c00d4582480c0c0141d030407241d040da0a20501e83c0c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474988893 1250 474987643 474987647
    0x172505040f080f060c090a150203040e0a09020d2a1403010b0904030f030b0a031203270804181b030b01032915160b040c0e0f010b0a023a 60
    0x80704840300300f41c641c041e0000c00c0c51414010001c1000100080100908541c1e4848090042c49000b18100240e040403400300a92100d0440341648069446800c00141d0042c0d0700194040300311070405080d82c810240500c07007002e00001007001c40708003052085c3c050307607032800042c0034190400300c010b010354280303504114682042507803240a60342c5a01c555030301421229003140142269200580d200008000000c04600b50000803805542a96000b280044a01c0f2104420700040003040004c81e09180d003c0b8003280c1c840b000e44054403040d166000034000d140f0000303006172030705802d11020511648201480250141d00103004405d003a2014490312001401c85100444212403c8204825441240e107080c03030300c10540302803142d90f980c5640c2401c100e104200b0003012203120403203401c50401c06000901032200c2d409001847c4c80c008604040c6040010142c0841040c81011101074000c00c0542100f0300901284620103080030750680101083c007241460074083c4c0e0301340e2100558100c2ea10760303018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474990143 1250 474988893 474988903
    0x130902030d02010c09140102031603200601270e060108070306140f0103020d14010f09061505060a0f030e1204180c1e121109010210020703172505040f08 67
    0x10b09510384440c15490401b20150340b07050b01180c1c504502007004029035280c4001d4034620451b02a548a40f42c0c83c0c26a5041460311a4030b4008440c1e0741d000900411181480e0380c040e54092004102c407942d56500302d00248090314007401343c13907641d000c1c41c070010919080028030201102d006480074462884485c3c401821260203170303071245003150000010700140c00c240a0141c075845c8a80d035007840800c1081d80303240c2101c0b1082c6400c47e00d03c0d11145a03009110107030240d08100d201885010020358070304000180e0f14405d00303481c28140b01c0103000000c07101d4041d41c00907403c40c10410030b90b191002c2e070440349941580240200945924907800c4109609080c4c400c420750090315490302c0c00c12401407810701403c1c44140c040794040000507151040c0380c0703401d0b00940103500004240d09440f00c8000c40060300b00702c0d0040d00c291903071b40b040c0f003c1d101007a4050500c0c030700e54103040d502c0000360311580c5c080b02c080d10000301c102107600030814180310055448001401140c1d8a02011300c0031030340b00d110403a222 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474991393 1250 474990143 474990161
    0x20d030204030209060907020a2310060506030601031107060509010207020111010e210d0e03040e010b0a05040315020403022d0a0518101502010b010f112a130902030d0201 75
    0x78411000103005c6d08112406542106160048411421040e914100d0a14001c411019413810b5840744154049080010f0401080700c2c0340c0a1260310b042c82e010814034000140000d04140d1101e107200002c5c4000e00c100c0c0d2165411030014426850030341041400b0b980011001c03400114030610b0101640010b105051008171400301400c0e8201201c40c41548100c10b003a0b0302c0080400801048009071024030403090074141c9540515100e41c500a40103020010580c060740c041c0508028815919512502726001d03207500901c3c0048a5400d44240c000034061030300025004910319900400c1c02d00c1c42484001b210159180040000a5040501a4604143c82496000003800603038400c4c05840e240382546c030943c0019017030151b40e41c0c0d088054581000f01401d0313000d40d5560020b200d80d135a01990041c4211796a0418803c2c030f56075681503c0d592038160b010b0030b100880350203150b2540b050b2418940344024000b8215003003d2203c0e10b810b0002c01c101c2070100d02c0ad01c9406c001070301c080d0044c0294645 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474992643 1250 474991393 474991399
    0x130c03082115040902042706111911100f050f101211031903080109050115090510210b03011b0c03111f0b0405060a0e150d050f010c020d0302040302 65
    0x190100c2c150501c4007a2500705022640207460300c54004000c00258030b40c00d0044c000b101d00c0329816840d410301c2c0080352458080c225100c501040030b180c079803d0718a20090600c3d00340c5040c01c1d844000c50000c07400c15000e5210596594100328404041c107445810090044003081c410a5080e25003030050310030147c0c0340c812941160300ca001f180010900c030000c0c08000c1003010b82550402081007441030155010b01004401058400c00140200c880612406024080380c20000107000c20391007018006211501c00c40384505071070040200785a1240c4004a04404204050294124284820f4028010315a2501d005e90328100e103c49200701030490425080c0142d4540c1a050001d40d00c0489040c0609810000c0a101d1031008401c10264251444c081c0c0b45031101c0043ca203500c18007040203403500580040d1017090030f074105000089644c06004d8006510b140c501d8492580440030a0040618400240090003000c10740d1b60b48031410b4200c0e2520300c1c0c40b81c1c20348401d5140c040d0203800b01d00a0f8040690 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474993893 1250 474992643 474992671
    0x40c02100f060503420f071206061e09031e0515090106090c0e010801090c030e1203010602070b03160509150703020d120c02060f130c030821 62
    0xc1140c03588a1000140d0005020420ba600c0703901103443c0048a6070f190b003542264004081016a409280d840000044480002e038190380c244980f41505000d000c042d0804e6110001c1612030b401180300200c0318010741b4003889040d943e501d019104191400d2406042c21802c000c3c801c070340d07106411420580398005e40c0e40e03448142c883c540300c61040b04104201e40512034042c0303c4034080011f00c0418490308195001041e014200244c4005803003c5c03840303038401d00c1100884814aaa040007085042d18103450000038004030608085014050b0703652500c0441c09a40c1e6200400b031101001181615107a13000c45000e02d40c0ca01c803011360340c032040300e100703c05081070303841d03440103510440003401c1248004108400d40c000b24412a01c007640452011000343e070000307d5000d021908410141c0d4000d140080c200912004000080d40f146d2008000201c1003042d0b2000540074490441840c0c1c0d415000460001416240d00d4020030720382c051000e6980c50a409428801400780c02e0304c05c0352007210a445840c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474995143 1250 474993893 474993913
    0xd0e1f020307060b04060f0f080d030c08160e12070e0702061e0916120b010911040614070b0c0307090807180513020405130b0901020301030b060603091204091a040c02 73
    0x1100a00e8421991a840351b290800084c0d40307842048840b018200840421170014a0420311034600380b28842c4000500d070070880c1981c0c19603001908240e010344880d80191b0503505046049031031040503a1640c3d4846052881e2046034440007a10100307403050784011a0294880d07110903a561603041b00c106c1c40d05103200340c0d8803298000d420760564110408500710383c002001070039245141078640d0800122009020341c00000c3c0700017000c20174018110103104006425a000d1900d8540c40707039014172000e22403034402000000c641c0e5821654156000260a50a81090500b03160141c1c0117840c0c41d1300040282e40c0114410303c020500b6406c8600d4450800c034200d00b5144000702401d00241240c4450054481090140c0c6460003458442c1c801d02807824402d02d03062070000d0003054084c046800c01d03031043c0018000105401001a0010000c40e1820748a82d6150046403900440d5190031000c038002140016203401d95400c07815001c4c140d0155000900c140d0b00074030040380d00c001078850041c1c1c09400310b1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474996393 1250 474995143 474995153
    0x50d12050c0309041a030606040c140906040b0d020403290f07031e060807120206040b030c07050f01150b18040203060604050d15061a04060513080d0e1f020307 70
    0x5124000c0c01d1016a42420700f0701e4001400c80b08105254041d24604000e081010301e42407201551180e0212000c0046d0701000340700420a8203401844101401d00082d05070b6155a8542500c00401c3d48002e001e0359180405501400b035007151200b21103000b901840e20b452104900800240502204444440c0c0d0382e50981d44803010700c018000c1018141d8441c1030002e402240c1100b00880042c101000c04c10520f0701418502d0000a544940a42100f95000313100580c0c074202154211303685654566165107030010350030250320403846d0007030852080700380240c66040c2c107403c9000b40308101e00880400326914003240345148281004540d9200d00515107031811314150303003e5904000c024001c02d0a0544810101e03104500d20103064610380e43d240d00880e110700c0c09009004c0648242e01d0050030700c43c207c001d14800350040d400f812042c8000810308226010202c2124001400c560041b1038403091145d8003e826240c0d002000c90054a4003021300d500c941e203103d105145940c6940c01540340c05496124 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474997643 1250 474996393 474996397
    0x30408070303060510030603170906120403140304110103140c0304140c0d0c080105060406030f03030c03110403080a18210f050d0801062709020d0b1c030207050d1205 73
    0x411014550f03601004680c50f10b904801c2401103032185c40014130141075051003161000c1c0f070301c0036602d003c3e403c0205030415100d14081c1c0d0040c00c12084402e101c1e445600e02521803007207840c080000004041f0800052080c01403145030542400c2c0c908200c0e0a20200941d080400b08442c00c10f0392a00400c045800643c420590741d034181e482605403880c542c5c0010001c0c007540360860040c2c60096940c4001d210101c030a20501e41c000300d0441c0c1c20000185103a0b41c3c141b80002644000c0c00b81070b9507a8030154803500a40109440710907440702240c1d140c0e240d01d820312854005c50303c110000b440e188202e03200380e800502d851703081e200c2e86524244454404d1900e040c916a01c05421151034290741c0321000010400c014100c0d08142680b0307040e200c8d605004c0010940c0841204d034042c2c410030880c0c000d0000080d1100c01c42517429031075016a170341c4120400310002d81304281d030342a0800441c4a1242c20076410703048001030503200f54281d82ca100d588108014030403070700311b1024040103450030840000301c0c09031700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474998893 1250 474997643 474997657
    0x50a050d0302010b03010f02070314030f010b030c1e0403050d0903020a050d031403070c02030d020123060429010e0904050613030210050c0301030c2102040c050c030d0b030c03060c030408 82
    0x400800e641302507501290035200384a00003003000703030049030038420180c00894a16003060590220790942c5490001c84107108018440c03074001d40f9000002c20446c004140442d6261042d00c281075071014811a0340c08100d078030510060b90780c0c0c02070b000c0c801496403040c0c480d0070032030347c0080c0044031803810300b410458a008004d004a062284881c0e0011240511101852003060b050701d44202c1c0d90080c0c01810304004961150b48116450107400a4160079011f45500e4082a030b001c1040741503440c90007003402000c0d07100006090861000f801c89000304c41900d6a03801c00c0342a030710940001500d406000e418001501c0041c8030f030704144005104203942c0200c403250301e40a44112a460300c0143d00d01c1c8101d030015202d520100400000610038460a91b550070300420018410381d1022640c0700c107030240c5041c00840240b145807191010b04c4074078401d50550310221442c80035256202c0c00c80210800409010a1150290103045c4140c151071401090682c411009558101d155542c0c541c0c0340d140c2540807103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475000000 1107 474998893 474998897
    0x20303040302060a0c0e03060406200403030c06020306150301030b040308070c1a07120c1e02010b06030f0901020403081209060f0601020d051b01020a18080304050a050d03 75
    0x10f00c3c15403284003c01c0029115000000482da11844051510382c07600c1000103000a016041e404030140b045060007444800c015040c03070400030b01840c400680407a00219038100410b1058005550101c00100050401ca002561450b503540081e003003030760f0a0010604000030560801c030016080140c50074008543c000d00d5503008855104e50841011111404011400240c001e0000ba41e84075604d030710038004014481001458800d03640009100340032403040043c03501e40180b040294110015205a185070348100c82010050805045102d07299809c00c00000450181c4000e04070044c0303950601141d03030801d8201149400c001800201e043d0300d140040c0884d43c0e070000350450040d206400c0042c2c0f601c40c03411701c0c00d2003a4494005104e5075400014407880213075216450a000c2d40315209044c24058403066103580da409035008203608030980755001c6c00103280100903001014440c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 474820143 475000000 := by
  have h0 := BRFrame.cov_init 474820143
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474820143 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 474820143 ≤ n) (h2 : n < 475000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
