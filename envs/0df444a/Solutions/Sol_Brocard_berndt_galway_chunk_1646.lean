-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1646
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:02:08.95785+00:00
-- url     : https://prove2.me/submissions/bb175d44-61e8-4f4a-a369-bc61127f14d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 295863309 ≤ n < 296043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 295864559 1250 295863309 295863313
    0x91b08010b0111030f0906160b250e01320d06030302070b07080711180703090c05031b1c0b0109050a05220b1008070b0408060714040b07020d17071202 66
    0xb4075580301c041d0a100743c0d4a5503005070401300d10746503405d86021031004000d278480d522403107614184c8080340d00b164030074850303408a00301900d1241c0ac041c054031105502680c1070b920219403100d01158030b20030211a40103081e0150412a0080304005840043c0c20785204200707020407050303c0c41c10020301c0c00155070030508510704100556400103018070211100d0300e60000d00f400d010036500c0001100404c0b1194001c0101181504200105525502448400d8070034140344191907180c0342890703a2001890302460300c0c541003440c1322000740741c200503004a00d1a40741041c0210303010341e9182d41003c0800ea020941c040e84882c00d022004901c0d010f0150b00c4a45903509004607010075003500903e42e4450009402c04032000003044045403d0815600541514412030f080a80d65072112407440c2d100e4400e0300c0c1a4051b080101c1e148512440d06d40490250700b09a0034141810149001e05a520800040343d12401d0f042007140060944d00403865945040035034180c890506082580003c001400e0160840d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 295865809 1250 295864559 295864567
    0x105040203190c05070609050d08090c130b0316151b0305030a021c0c090303120b010903140102122d0403020706050d110304140708060f0703091b08010b011103 70
    0x15120b01030031503201c6100c00e01e002c154803580710750580700e034812448045c0005041550034814804005a841003000071641d03160666611003202079205c600000032560310000c10340701c1d9100300c44150024482c80c500101940c1c0c0359045021408007038016640056114902c03604507401301c60b0044040c0e00f2862035200201240c2c01d10341c0d0002d02504c002444d030211640e0109410b07021116903035000003c20001c42d4104032082003c10041e12280aa00c02280000c3c18681030380841000b03400703154110f04060710b84a030a1419940c8000d0300c880e03034000d0807800d994203002c05032000c545204014002c90300c4060340c00c03178200310b00110444034000c8411084902d0a000a000020398005840c600302c4041e403400503218081c0d1110310000d085401c1341c08910010120501c424829014004c00c00d13840040c084030800c07a40c401c0c0094403004221510500d801191001405050103a040341d000a44501a6040700d99444111300c3d40034010f580017403c00e41e540d071030070000c0c55800542a1100c036038824025410 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 295867059 1250 295865809 295865821
    0x60b1c030203040b1b0a061505190b0a120603060902100807090b030c04030503040b040e1e0403080402040f05131202030f070f02010c050d1805040b031c2f060105040203 74
    0x150344594030802e003401c200003c043c803003d44405c0f41d440c1820354142c03d80b1070f10341c00c84c00c000c0090400c2e400606144211240005814503040c15480c8090307000d03444040c0c40901d003014030423681d0411100c0005000c0030030320a8061000901c552000f079445240c001600c0110350041c84104110f0452400901895400340666240c00a0601044904e0054241d40e207a40350350740040240180d82c0300404030310010601088586800001d00269150005070020590b1800d4410403814844001d4030440b92464002c500801d100e01034060380540080c00c0812089650740450044075011078521454000e050811010401030700f4444104d10124030042d400c0540c4038081c800b03144a03640008140045550003030003164040d091400e80f03160003c1c10740d0030303900b003988014180413003880c01c040520320f07011804240d40c41c0500c10b815440101074010500d46030151520516121400c0d100410300081071040e91030001c18140743e0055201c1d540c0c852086006010304581741402c10782010703128034014410080 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 295868309 1250 295867059 295867063
    0x11a010e040504020109351204091a090c07030e0306091509120f04061112030711010621140601030b060105130e10030210140313030e04020304060b1c0302 68
    0x21481001c450000e1261902d20041e07420701c00f80d40c800003d160400c0607403511006242e0300c04140d9018480f0803043c4000d0314180710b841c0da00c601c01c2803011650a03c400e118111560341700800280c004201c44000740c0d0002c0018111740c800316105510b81c1d10000d030080806500c0b0000c012171820950042c40755061440400c0d803a004001580b00c020340740000080ca0cd1b0101304040e04800112400d1540d903103d030104125060792090041e040498500c1c95400781e54100001c1101300c04902158041c00c3d5111414100c1d5032000007001c442030303507403517190115107003005c501d038082c1e5100d08190b005550b01140c60204103a15810205200c25001702c1e004001103412411020b034032040c2464129520b0340c440324003410005c01600114040101f080c00c00151540714510602624007c0300c0811494107072080441c0e0744100100b07100d40d020814008290400510602c3c00b134018400d0800242210030a0081812600b00b00d4094a10980ba41c01000c16400c020b0708400310050807280350551084c1c541c90181d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 295869559 1250 295868309 295868327
    0x290409020307023703020a02100e01022104060809161401030f05010f1716060903170c1f020903010f02030105040513111e061603020105070f0909020a0c14030a02011a01 74
    0x8280c0c2640c001d0000402d41b090204103a0b8540c0100613480c40403112800a0261004000d41703409841060f0452400e0551030008030402c80524213910310f0f0038100340c421680100050803540e8144540010040a031200011000251205030040540c0380c525100060594075903e100c006a58503003801803000b08546401101034410210383c8241c6070981c49002c40c03401d0400300080081a0011401158841e80f1000760000c5034010021103000c1c1d103070303141d0740c00840c8912009510b031540024030b0701041e11298941a40e030f80d52131000050400c006c04001c00e0039070f044520440c0c1040d0380000184150b1601c1d10620ba0400c01160401c10100100e545101d414910413000a128040c0c0c50381d0408846210f0100c000701540291070305403910742610040710a12240c00c01103026500306030020305400d204401306108071010b0742d140c401c0540f034410450029071101120f84100000c0c92404004103000c4d20341900b030540360000640d03488204078802421505680c003c84c0081c1a04500c07203500ba80e1083c140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 295870809 1250 295869559 295869643
    0x5070203030d0c09080307050705010f110d0f20060406060803040e19020d0e031b0f0322090207031701050105070305120915090d0e0a08060129040902030702 69
    0x7410b100d0340e402c02d0342d130f6040a500c1401c95100028000041003000b04040c01294400e80303c0c4080030048a1065070011507410b044100766116000700703150b040c4121030f510340150403810311811081d0915568400c48040e08030141803588103a050004020941c4038036401402c0c404061803c050415034860426640504507030101c03585518030540140320b6074101c1d08010f40c54181007010490700081d054482e0402c448402d60102c80030140412800045121400110340720701641c84c180c005108200e20640000101205121040000c900d6170814030050920300c0c001c1e02c0e0031a51914041c448249144160407480c10404c0a000910000390050142c48030703c81080100e00683c1d0b14441c52038503004940d0f64030b0420407100030a0201d006008a5400d90540e00c03031341c3d50326401f21001c061080340200e5209d030211652017600100a41d056920421440580c2040035640c0030341240c41082c04c0383c105400129001d5800402d024446030100407200101e90503599114008002d5440c0290050f8032600e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 295872059 1250 295870809 295870811
    0x70e0a020d05011511010c082217031b1c1d070e0118020f09010804020d080a09060905010309020117060103060909060e0d02060f01060f090306020a0201050604060605070203030d 78
    0x11485641090301941d03400c00d03109070200b20030f41c2c0d5203000e0510310000d82c1404001c01c80254000e054050103004192200c81d45480780503041e12001a40300c88071500c1c0080d800011000d411010004400d030100e110703c1203810201d04d890f4102003c0b110806244072140b20030101d4204a9030149403200940381d1035905000c1e10000d40a80e140340e50441c0e02d5000031030080c0354001d40c40c020500f031020850072030584800500da1020101005005d01c100c9c0304040d44441000414070080c2c6c1607610034414168494400780c0900340032500f5681d02030300d58000b0b8030080d001c00c1070208184041039010b005080284003d10301400a0500760700040c0c0041001400001364410044c00186164020740100d0010819940c1c00c020748182400c0840c000d0105143c040c015019076240080001e1000590301c1c080c10040752200d409034078040e001c0e5004001e18402c0030910140420000c086030051000c1c11301c82010b030b000800c8600e0404102720855001d0b0b04007800f880b07406e1000401585002041e142010302c0c0041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 295873309 1250 295872059 295872061
    0x20126130c1706010305121611061b0a030215060d02040f0e1b040608060105090c0a21090203010b01140a03181e0302010507052107141920070e 63
    0x10910400701075a000106489110848068036800000b07025040f82c0c0102d0903624407141a5103580d4292042030b0300c061122503240c101c0c0021074801d151000c2c2c0c09074002d002d64940700c40802400e40b440e10749a800d40103504080c09000a15070144000c1c0480c00c00114008407900c5d002001811065680c040640156a50301172000c2e510800e0f03018440d008040301c21144588501000080c8000801c02da05015508002c00050300c1000090001d040e240001d12000391507842011440380b03504900800d10421003042d84403c12079103000000d010303d180014001c40c14180d903006043c02c1d44c1810000604104c5d01c8690102c440420105862444205207400b150400a007203140002c1128100c1c09480c56000d045011030081c4c1100610b00000e220350020b101a6071a807a0560740741c002d41488822924055030440018406d0043c03090340306c002800c00304c25141000340b01c0c8407550007072040b44007802c0140488040003604a103820b440b00d1480c03450b110000e81c0c000107003a140c840d5442030380b0181100340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 295874559 1250 295873309 295873313
    0xa03080d06091508120306030c06250c17060105090613110a020d080703060602030d0c2006010f05040203190c050c16061115040201051606050c0702012613 68
    0x9040740d4020200c0a0050000d110742202e514103500040c8240d100b00d201d840d05000900a4040c2601d201e9a030007005417a501e06c0107400e04c05240c0c014552515007100146509003018500410390454900500c4400f00c060f003002d205a00010300c2c0340801900394084c0d401005141d50b1032104961184060f14514003400c0300101c25000f8004181c040d581d04803020460700001d5030f000803242c002540d5942d680c0b0058459800940440e4800d00420005810410196070814407a42010030203800ea0f1030b290030740d46c035035640d4080301300145c403801c040c550031180c010004240801c101c0009800300300d60840c95400c007084100345031180c040e00c598040e52075140d80d0807442e00450580c0c041c6260101529000303c0300000002107400d03140900408102400e520101c550300000d154141128a16564592034540e50019a000d03001280d0310340040c91008150300025408d030040601420244003459191000e07440054076074154441280c0d010300c140009034420421440f213564102c0c171660307a0080300c08864 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 295875809 1250 295874559 295874561
    0x270f010615110f070306240306020304020f0901060c0b310201020f072103050f0c0a020901060813200d050a05010c080c0307080402040f092003031e0c010e010509070618050a03080d 79
    0x1840012441f4400d2907000414041e0a0300103510440c422107541c094000100c1c2004550f140030b0089000194000042c00300149600001542000d414509002c1801c0032200b01041c3c03a4105001c0541e5002c590541d100315601004240080046940070b01581814444585009401c211041c940001c08510300401d1500802c100d48089007442481a520300c001c2052995510303510321300324000c44c1c41400000d40360b4400c0d2100c0780160800750002e011420030f51903c81400a200a01c5c02443d800700f445140d466461a44980391144141c001d06216001c0b0705280303007140c1150483e42c4c10300c010701082110b0035401d80103c2e5130102c024180817000d41c54500118005282914842c8074507480d000c156028081e0300450b04140d451202c0d41801d903140c0ca00245a03c82c001c400c075420b800f1000d500e50889009203c0080d0080902020001440000800310070b829a14282d4142145d40c004440074000542c2c80081c000c1c0030802006407900152900d13011521002da00d200242c051030020031804150012 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 295877059 1250 295875809 295875851
    0x20c031806130b040f080a020916030b03070602160b3606070b06030c01020f1e0a0b0403050a09060216060c030c022e08270f010615110f070306 63
    0x202e01c1000c1d00d0b15200c2e40e1060507544240a0010f050304013120000e415240041c1d41c01da42540a03000f0b42403a06d4541c480681072207500c1422043c15140c14007040540c408206000007406154001c0c45c0c0034614900003440c000c0380d5007105031404c40411031403402d00e801460701d0300c20340700400c040e8240c1d4100c401510101284615144d610000c00103d03a001d2019803002d16005940440c103a410105c504030040e41d450609840302603c540080301c1c0012504255541c42e92a1106c401c2035640040065446644511040300c1c00c4002c0b0324049010041c0d01c2e400980e28014001d5400200482c102450041d18000014820081000208640ca10800d4429104030000035405000300e007212070202c0c044141c131540080b420101d85032004d018084140b01d090880d010703a02415892144c1d02c0214100c01020044030506030280c4212003180007096000d1144000402d0b8065554141210380d5a0040c1604940340801540e64031504504c0be81c03503400b0440800722680880000f8001c480007030000203d40c2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 295878309 1250 295877059 295877077
    0x30f0c1608010b0a08010b010c0204020d0608010908130e090319120c09181103011202031204150e0402071a06040b0301020a0315080715080403200a06050109020c031806 74
    0x25a21000080000381504003c480e15001c803000700441ea02ca040060803a10f4400419000a14aa1100c0094200347e801044070301420032012850300c4e1982c03041401e4681640d4101d640340400104e00340d620317400d62003901c00b52200b541d00700e07040d04010b040d04c0e580f402940f140d90a9074806001c02d04449024903d42002e01a0a5000748082625a100540000280c1c840c20a01c00036407006501a004144900c02c1d8121400e9040b40c116400c00070090b900e015a4070049801d44152180b0a0b24004003c2c0500014911a809413401c580200380082c40c4600b84003042d409103005004220001e4003004446d1407042040c810009607035140030005025100103908140c06502c005a410140383d416004801800c0c00c51214a101c2542d40e454148c1d1110399124110030403004403031100409105820864000d0701924010145007000bd808a01d1b6400040d4442d241e07a00640c00034041186600a9070f0050160b42011800e04040c0300640e81c90380308581c007a9580c02c90207070103015140e40301d10503242014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 295879559 1250 295878309 295878343
    0x506010c03050a090f0b0d05151c08040906080304060e03061909051c0203090a080703080a0507030c05010c050d1409210c06010e010512010606140d021b010c0e0d05030f0c 75
    0x1561b1a5000c2000350700031888011418104000035900c2c1511511700b29030b80d1000b07060340c0744451461800c1124202c0450041707034080c20030000061140e4807801010090700010010b140c2d075520384200038140d03a1030458801d002e034200a0402070080d420220700e0303142c41098140440e00311883e00d0682d050250301010619440500a000d800c020760000280c40010170968030103c44036180c940c607a50324405480020049042040401314261150010f03011042c42030408203058400c650f40c150039136805c082900001500030400000c440b040b0b0180c80c01e2000f86000c114540c1c20120b07080d03919001080d40c1c03203a0504240c200205032641c1c0c0022152400200c8081d12241c1d40c42d4644910384c40300030f10035a07104a141c904003a036103060612808040b647c007502e8001f81e02c0a094840c0455070454100285055428840c40058404041c01640e0858288000140d41602400043c0c201d100c2c003e03141e802075030140f481100098000049501b40d80b484103102d038a4140881c4224030380341e0384032681c1444d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 295880809 1250 295879559 295879589
    0x1b010219020f0619090f14071a030108060c090a0b07080a0e0d0b01050402090f09090d020f0607050316050c1507080109110f0306040207020a14010921030c030513030b190506010c03050a09 82
    0x203500840e586060700c08280080300f00665801009d5070500083c080c01605421000100e5a9040c01c040200100b46c4054070a04c2019075844c900320954014210545041400140000455030301140886241100311604100e560041c0c6a9441517a41401401c0c0580d0b80000c000310580e4420b500580e2615004102891758584004855180c0507c4116180580b18012502c5804140400c1181c8a00d06a98403141541d03540290950b03c2c90b0b40e18445005e210342000610300440301408001950042540e0000b50f41c200070300c0c01014020140e2141c019207280010011309018200119031240c607070b94440940b21703180c08002030000d2080e40c0c40250f200c0c203a0100050b4400100f15800f9144a090b201c0400280e500c01030b04003c42258500304101c0e00080e1850000039026140703100825009140c66414003224101c0032050340261b4100f51591503a800401500300382030800188103140c0250207019034100f070400030380036481e0040000c003480008200390f100184190865030041000707048040325 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 295882059 1250 295880809 295880843
    0x6050910020f120105060c060a0b06040f03050d11010b0f0405102c070f0c03051b0d03021308010e0d1d090106030c081b09061b010219020f0619090f 65
    0xca600c143c0740c1e060110303051800002c1350f2a1002c00d445900c01000040c040030707030318064a94024028445080e51240c07080c440415441f00202c048000356100b00f00404881c0c4540b203001e00300c0d1600681109041c0e0508103890010703110b03166031a919080542c0d02080940f602d001007110b0707d0700e60b00000881c00b0320b400c140d244441c6d034a40903008111510380801d510703100c400041340e10445020100012810307103a810000244210300805001174050b00090313010350b5600d007050504102c030350014000394002c100903000401c004211402030405170020041e030781e0860403503600d07000c080000c41c0501c035615400c02c1c1480c0480d0000100c0150050903810550303141d150150092030001261400503500d03000040c80801c003c10f0440c1385003103500c0c05a0400c8002c8080000c1540607034004210b100c4441201090010240050701d0035000051001e02c282d8038103140240703481030b1040b081c039103944083d050020b05030f40c2035200d800072a0800800300301280780f030030210b44c03819458000a201c107040d9000040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 295883309 1250 295882059 295882087
    0x30c030d033603050c2506090e0103050d080910060b0301140306190b030a050733050a050d0915050916030302060a0c0c0b070302340605091002 63
    0x1503021022803144a4038051001d03104256511415801000b840100a0001090080b40508420103500e0200c03003c1074291141c078008242d403599265201404110700384080d03900040f030600907000c400d450940d2036140d900d034a60b440034621911018006040701060210300284034109030355020180c144031055403030410094035482403182007069150f28005081c10314001c01c03c1307400355503850542030004c4201840000107159691360207601d07200300c14101002138402c0c40804c000f4042d11707d5031168900d000489802041002c031005441c18414003501403016000400d664900c1c44601d056070300c0c0e501c0c1b00c1c581002085d014601038280021900c14801884048e0805441540d884040e40c1c10b13245d10000101c0000b01c2800300a0158004400003402c075420380d03115070388010b0f491900030307550280f545842e00c00c100d003902c4e10340009400044404151000e00010354410702e6520a1400c900d640020070041e1010034080241016250f00108645c4042044150004601c0c5441103540b6180301c12441c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 295884559 1250 295883309 295883321
    0x3160f081206010306090603050303190b04090302101b0815191211040c0e0402070213111b0d17041103010e0d0801090603080708070c03050615010e0f100e030c030d03 73
    0x30f4000b90078042c000c90300300d07a64043c04c0101d036403140003181540c507a0300b9004041c411049625140c29130300c581c40002559140550803c8a010350060b01c00301401c21603000c1038510580e42c0680310509001c038001055030001446900a03561040620504280350000e10001b000f60181e48241c02c17031400106291214001e4040914401c50300f60700030001400c2400140c0b030403120904046882c01980c10510f080c5600140742a510040242282d508007420031000c80d0f8018223001c2425501190410850000644545000818000401d204d240c070340e03002080d14000385070b50b580591028000c6820004410a02010464020001d2244007480701d1840e81e034189101c41e07030780016075031400001c518a040c4120340c250307500700769081e00d44030494594403070030380c0104c008a072401000c039800400318009001d03070b0717000d14a44104100140c1d0741c070000601001c441131080788a083c03903165900c000d070b40b400d03100d05000314079040c440c072421043d00000782005240001c80d509030081ca0407044074568944e10032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 295885809 1250 295884559 295884571
    0xa0f03080f0609010311040b03010207080d2016030f0516081c060e040303090305040902040b030a06050603190e0f030c01020d05090d02071e0302040e06040c1703160f0812 75
    0x4540303070340c0c1d8000c2005410301c001c0c403000d480ca24520365803403841c2c00c0035000f010143c40090000341c036110360341c0da410282e940404902c0c1c0b042ea82d618280c00c141e54105080c402c80b5980c2000a82c10401c0300c1c1c1401c003008d810f4650041c14081d099660503000ca0180381903840c039805c0e162507808110041e0511103060391000c501840f0f80c850281c1d500812080314032480c8180e580b5664241d0b8280e0300c5a500303500400e000c01c01a003d000c014000010000d00d00c1c00100040e04900900d19200d040884041081e500d507900041d10507481801040100d1681a0440440c40c0e80c0640200744c5420f000009414001a0340f180c40f100c0c0400100c9008411054009004e0610000010015030b41c0d802d00c0ca5031074900b20b0358200010f0b04600d4080246000c1c5260b6204030106020010f05070030303600d600003404c03206154800c0b000d84c5c100030100418001c03001801e00003044864040c4040e40c176512440c603106e2040340f038000c03c0c0001b601c00d580d0a00c0861004200700603448560142c0d038411810402200240c00c40308 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 295887059 1250 295885809 295885831
    0x2103110310141008191b0e040b0409020325050a2c010605040b0d06050a06031401140a0513110f0409060503070b0a0f1e0f020c0405090a0209090a0f0308 67
    0x1003006642042c0e50b00c00750228084e5618015500e0b011030100c038503000040303680003c1c0c0d00d4800341c00c00e031a0103504a03401d500158440304402101e101c180425101c038013061910542c46d1420500250f280402d4038034600c0814a15044901d1070860000c08005094010f5500200b140b00301091074030300403145a00c1e0b407108455000300003c40d01c1070b510450000b4021900014414030007000410940700140c00610911540030410b5915100410f01d420740703a601c1900025160030a4214440c60608061f01609a84038200984a101c0c4045824500503121f001c1c0600c074030a02c808070080c2c241d8032000d1540340807104d05036a40721420400f03103540c025000f40c1e03011915000d80007a00703190000c0d620b000c541c440d10b042401c0c0141000b055070318210078640e54083c000da042490300714030041821802024900d4275112414069039200034501070b1110249802945800c042c4100e0303410000346000392580c111003881d03a50b80c42c01412814100c5006004100c0d400e110680307420581c02c03004580c420956559 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 295888309 1250 295887059 295887089
    0xf0902010e090615030c07060c0806100806101d0402030705041d0411040507180f06090609050a0302120a08030c1c05060d031d060f180307032103110310 67
    0x4100942c000b400d032099640210740c0082c403030324a442c210245900c8402d514241e0b040c512540c0322102a10b2403400c2000005154504020b640c2ca80340301072064611040c40d0100542c6803840124000c6842c0015103418040ea1f10000b044186507040e1041010070064815502d81c240711002030401c0c0c00501401481608800c00e00041c0d40c0c907265800e02c682d8003c402c00c1c191003046000c3c04010700b009001c0908100d40388800032140ca40100d5040000c0c0345030840940c1841c40c041c00200704e24215004002003001c404800c0065039908002d02c425640c04944a40c40314004141051502144000040010b2000700401030400e0b260780140004042400005280d00e2031440740b00f0440b14101c0321716038040e200000400110303101b2400d40d1802094016241054820000042c405400c24000540c14400001c0c03603004028000b840b80c1100c0c2d1094000b042c2203402c40d901c0541a05000701c2c803440240d010200d03907405a1082e0400b007950301c0f03c12042030317581c14400d840e1340e240b1100340200d40f500d40e0790003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 295889559 1250 295888309 295888337
    0x80f09040c020609061f090c11010c261012060207020a0f03020d15021c1d0c03100203060d06020a03150f050312030402040f020c060906010902040b030c0309100f090201 74
    0x100740319109491400203099180c1d107074460006e003038800d604181c2d48445000804100215580301c0c1d0480b00e140390300d0b0021165006000d1500703658180440c9002c00011407402c02c6c40f00c1e0801040e008920304035103071450b140c0d00d0040106502115a200207607100302c6030481c0050020940c0200f0f215402070301c6007081c4c180c0380c4415840410b0f030341c0300080d04101d8800401010500640b051485849004005031900700e24185203120700030b0241c0d244c18001d03a66102c891014518805a6400403001c1015102a104030341c0080e449546d83c0b038141d0122a000000100c05a60702e440103110203900c100f086460300c110102c0103000b481c4080100c83e04000e0700f030001c121480060004012240014010050420303464030003403060b0000b03031080b6005501d4000c040038030781c0b1a00150a8403410740000340740c80e15000040c03070b00d4980f040c3d0005500f68810001404581c1000046030f82c0105107400c0c06603241c4a508816103003181e02c41501003018039180c4c010641754425048444130134002d03a50710351000301e00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 295890809 1250 295889559 295889563
    0x70b0f091002130306020d0603051b190605030c0307020a0f06141311010c060b1c02030d030e0a0b04030e0d0c230901060305220b012301200703080f09040c02 69
    0x30070010f50300003441c1c410800a4030a800071701415805c59400325505a036907450526002507038074520f4003a000c3d01c140040c24202202c44620b41c03101c1c6030494004500d001d00180c00d034030001e0280c10000d9400000206683c1c020070802c52a661301c03221400d828092030802200509181c610751488690b00404036a042c148001003a0109400400e00c0608042c15001990040c0c450403086440da612134002da040307952041c541440b00720340d5580c0d01d220b44040344101403c001842580c00d0902d03107000032401300350b9000981c1429040d03014104200c15200c0e428140c1e1000304820046502880c0d481c01542004031550340c0d24100d90341c10701a402c01e506518040b264000b0030400841d08010b142c4010003095220f038000e150048840b6044280401c0007036503080d05801c3c003540a880c02c4450230300400048000480200529415249003d1100040c43c0005c12803021055121682d4440a95000141d0000c1c030401c03000f15032180c29030b55a10031b4046554195080380c10514400c0745040c0c8e840f0511400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 295892059 1250 295890809 295890817
    0x1060201090b190608012307170a051503010e0706031109300a050a02030d080402060d050a02090a260109080f0705240a05010b0406020d0c020303070b0f091002 70
    0x4440301c030b80740c2c69851040c00050110360954001001c0e840d14400583d82c1420301c81d07600300019600382089110703648844c030b100021000e4510000c100601800414010201c004240c001d0f103580c070089503907268a600f00f5003007641a16215459440c040d5148041100003d104044402c0c9031002d018030000f412403848180100309226411500301d251080b0502400c00b0040b001c1c0807009241081060724100c5d8a01c2e10302e00100403034455002142d0481503140c100108891603015140401551030702e640842e01a0160000e8005420345030004611401800d4059455100000d880084400e0707036416081c1c2c902e1900c03000307401c55141446c18000500380601a81407100c4c0c00c403081510740701225280903071aa20911082d41c003030040d01200e0451040c0401c0e1001d8408007100440c03014100200301404032070040c1e21000e02100100000c1140311f402190450b441e03050f0342489082d810060000c030342103200f101002043c4400c003c042004212044202e14080c0b5030403c111101c10010f48041800c0f882 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 295893309 1250 295892059 295892063
    0x203060f031216170c0a03080a1109190e0901060303030b0d0201080105091005060f0a0f031406010e0105070f050a051e071701020c101b0801120201140c06040503030f0106020109 78
    0x240401c0481d05456141d61041d08030f9114110360301d030440441104140340d030850351806003150804440c96090690000e54541c00c4107042c8010040d100c1002c064036403d100300280a8040c40c184113442c85101340201d800d200a09070714008001078030300001c00c0c90003032940e030004802180ca08016008581481d10601540a5043c2c50301c400036400c207030402c500c500004000c2c107000b00040d00c01003031984582002d480211402c91b192525000b01100c058a1a090301c281401010720300101103401000c0340f01210740000c02801c0c030380c1d40d4102d0800100d0741e510460401412182c084861101040b50001d41c000a01c5e0043d416070300c22010901920f09001d040480e0032801e6880b961043c000c841d01c400700041c0d20326032940010f150110034400c003414a83c0900121080c0740c3c1e00c1c88020040740a100ca21152545a843c001c0407660408a04124038000c480011707040107039108854010600f03080840c0c441d00c24650443e4502d25007890300301c0d84ca0f8821512140042d11203000080c0150050160343d04042d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 295894559 1250 295893309 295893343
    0x120c04361a06062503090501020c0312030a0f0204080c03160f06030b1f03050105151c0f090c140a0f03020d02040c091e0f24050913020d0203060f03 65
    0x111072451a004210006020158055030070040c4542000120310b50501032045442e014020444c0c07810090040a159848181550050300a040305a90042034110a000d040c0700710507160788810b00340000821b0b1f1851140340e0544001000b20755920005803c50307a80300c0480440b03546103a144900919041c1d18803580551100c841c0040c44410b000360010b42d00000050220f0810384858440d0012401844c2c00e5600800ea40b13500501143c01c000c00b00701e141070303203030b14045142c030244010403664400c3c801c02c503490066950a50b51054615030704445c09880d00081d002e11001d03124209210210b002040c00e91145c110014000355800756082d0942c11641c00406545004509409000207031240c202401c040245035800484c50004981000d1010300641c07440e1141203040801000e25110580c00030000b0340c80150484480c140034800c1e00f51003541920382a03885e410144041050000403c1616030154004a400d2500075001e502452180380111001c4c000181c0010a154a8455103030807607540e1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 295895809 1250 295894559 295894583
    0xe0f0f011e0b0d0330050a06080c210c0907080a0c0e0a03150b060a0302070302190b0c0703020703060203070c030f0305040503160503070623070905060702120c0436 72
    0xc6802000c1041251000c41121180400000620342ca041c016400300d00000c3e55a001f40031050405100d0b020140c46081c0040c000c24003680c0c00980c07807182c994000b5400c4809907100141c0b50303005001c403449010001e0308454182c1486038000c0c211240440d05000271500d804076000f1500c0c41107800e0f03514554094aa061045d00719200c03550b40099680c3c88441d50354460075400000e0b15010020a020001980d0060321a03400345802410b2814541408103110500107450000ca8451000f494100c00c003c0340443e942c030420b2406909080c540e40c030140c801c601c04410040c61a07001521010610f1081c2e4030000701d200c840505038215082030b10007802c1907006000065143c00d9000803413000c0c50080d01200c0c24584144e403080705540320308002c0e0f1480001a0300000b1402c08007491a600410309041003440c490426000c50902e018124000e0b1080001310031390301c2c58100901c82400328210180003444040c00f004046800030b401c4180e50380030a11001040109809190300f40c0c078485901501101003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 295897059 1250 295895809 295895813
    0x150f0609010312050c100519090c1214150105180906070509031f061e0e06060d0b090f040b0a0212010308091903030309051006050102100e0f0f011e0b0d 67
    0x181c2c0c50b40303c5908240a020030164049540801580890841072000031502e803610f030a008904035900840c0c50714960400004400280400c980c80c3c064a506003581e4283c00381d01d003812026210700c0403204d0681c1c0150b072805100c44410841c03ca05a407802d1b82d0700400340d600e030b6200e00300c010f0b000c0302c001d603e6800c03000116178298410802048100300040440b034800c003840e96001155138030303021203401031561100d08200c00140701e00e143d4040c10014044d0712031ba07071600000145004001740380c10710440780062001c4210743c03690b01940342d644000e814400d6514107075900750585c5105640c150760300f00b04040001e42c490214022101d85a1309003070406100d91940e034940d08980c2202103201d501454804e8030050006030b02500d07900440c041d0350042400b020606105040c4a03150354140141070408505118591700019546601200c4080009034106003003192410010071000c02c0045014201038030150400540101402002c0e8104d028500c0703080d504d840c000c40d241140c821f83c111a400001c800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 295898309 1250 295897059 295897073
    0xc0703050306041a031002030916050d060b01030f020a08071202041409090102040b0c0a1a103302012304051510090204030c080105070c0201300e150f06090103 70
    0xc081e031580c1401d490b204115600290420240c6600004100d41c08070420500c0542040040f00c0411304207032b95220203007000c0106040c264405030203414617440e03096244060b4417960014184040c1035404540324507410030300030303c0341106031244400200c404c4004403144e02140308840840b040031341c0f02d0110041c00030600404250040044195550074040041d00d0084a4003c01d482c1c00081c2c0a44600e00041c03600305556089507806810000c40441048940c0d991220701e94203441c0d10b0442d09290004402a03050301124a0250010700c000302c07441d95180b160150001802c00760101125002c403000b5041041c1459000c50b0094030903400a12507800c516101c009298002145007030a41d40e00b6141c82400c1c080c4d0f4403e40c4100c403040600e000404c5040300a00c20950000200e151031f5010010980000300720441e408ca40031b200d5040c1b00142c41008109400301031142ea0088820701c0005505000303141c03074520784140038220304e68840001d41030000644035984951401041e14050b642540c030740350 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 295899559 1250 295898309 295898321
    0x80309040905120304030309151a060304150f0209040e0a020907050a090f15030c020d2304030b040c0503210d180506040c180608030f0a090302060418050c070305030604 74
    0x140b014041c1d20703803041500f0300d1640114844c50098401050303048507450004580000001d6240105141000e101914a03400e107506a07020022169242c80b6111400d0002c04014a41e008a00c002d04e04014100e404020b60040c0c130150b082100c04200c0040c80c9005607031600e800c40e0000350700000100000b5150381c01880039162649462074004443c40c0c0f84d06581d508110690800c0944450641081c980c003603042c041c00072108a144040c00c0b400b4007012010741aa2910651032004c1a0000521111014400c066800139030300500000c025061070304111201c000d440c050349002c0e0080038001108201d0100e0084414a800d40400c1d14040c5402030610040a040300503d550120400c41c0d070002c41c408010881c041d60040180d41441d903d40f90001d03508960300245070341c10500b07250040000200100a491804800301d070050780e50700d4854030032100e001003030300001e42c094404640410f203640703a20300580d14114840c07810001c0e80c6515046148031b0154040003030000f1350400000d40705060a03006a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 295900809 1250 295899559 295899563
    0x70204051b07062405011707022401050f03013c0e030a020c150703080405150705071505060604090209040902060a020a02030115080d110319030209090f010803090409 73
    0x1410041c4801003568519520010055401e030381c40e00044c1d6a80603000c0c0701c94055502000384082071614107000640b242c0c04040d25181038903240c20004640038000e00040d21a914162000c4105503954074060300051403c0c0140c07400b402d0121500704003406c051060000401341d00f041d00701181c0441c1d00322201d000c001d074202e000d0700e41c0c3c04608072000d50f014083d160030180f0400165890b00c02215000345410420003103e84600903619103400541c0c031003412542c07081e800d0304d025001556181440d03450108047c0c05506007084010801c00300369400000740844a01c680315080d1104e540345264015148261819a40860300b040100b124001960080400510240000c1408d50080d0002041a0044401d030342c0540c0040d500a42189801e11450f800a00b0601603a03040a00b043c480340c2d41da618145a51003482241102c240c0d040e00100141d500c2000c90340001c7e4040e4141c0500140a500034403486409203200401203500000c04002040c140c07441d0000441c2004c14610070000509451401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 295902059 1250 295900809 295900831
    0xa0b0657010f050a02030a05060a05010504050409030207170a14030a021e011e05100e040f08070515011d0603031905030c04050d0c06081b04091e02071103120c0307020405 75
    0x1058202c0502070081d54821020304030016143d1034100560700c26120001c2020384503180400302484980e0b0000f0640b019208281c0340010700055030320b030581ca46030f150303009140f01d045059100c0e020a6000103c40c01810b100d4594040704480500c9466a030340109443d400168200036910505c00c48072200007104010740700c0021400410080e007105481401d0704042e00f02a850700104102d540125140c400100101ea02c0b11303000d8036151315240481301140b64010500d480004980080c8003041220460710601003982d2112942c0d914159482c84c1e8100020200b1050250005221460044255500b100036007802410314a5100400c075916403005104c408804014400410039481d00681720a400f44100c1d8003404503820f200028080b1400144030f400100f039008140e10042270160b0580b400c40e0b42810000c20012b2541040465050540c00c1d20b0300141c1c40420340e5018001400300c50301d00300301d05809437140000211072001740bc0c41900030301c0b810750f070042001c403006003056405a075110310700d441 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 295903309 1250 295902059 295902071
    0xa0e0a0e0127050f150307050303070609020d0210050904060e01032111010e0322031a060103111c0b01020d050f1b0706020708161d0a0b065701 63
    0x22030404039242a154458910080410400a4443c00700850f50010041b8000c1c58084e2070070f00042d41e24032410394010b081f2030701d030001c032021503c0d6910891007042d030081100c0880c2ea0346400041264000a01107441031b4203141c00003d41c40040303c20503060342e4008120f090940c0d21a01c03420b03210010440103a04021a40c440c0120f200d02c280b250703c03000409680030b15941c4050307056071a500403403d4081280c0f214115000c000051500c0101c244080d520035180c005550b1307080040e0001c041c249009141c81c1c0c0d0010700c444582115500d0718100c6d6083e070600f040120301d540300482c0c2d503486034160032011038000c01a112000d02160003401c8003000b840c10400307030fa8070a21005410080507500c03050150b402000306000320b660a010405a00e103d003515040014545000c42c410881d90252103c0103410300b501141207101260040d10800d000601780c21783e40c15020740c10702440400c00180206542040140f405480c0c0252400d51440c145501040803150405d403100d41140e420302d2200c8010340d6560 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 295904559 1250 295903309 295903379
    0x7020d03050919120b0a111c02040e040602070218010608060f0f030a0605100801051003060203130c14031509060f0603031b15070c02090a020327030a0e0a0e01 70
    0xc0c29607001e04001110018150070520b0217107201e800207402c5c104402e0410041e035010b404400b0551307030103980114480034226440505940281300301d4014010b000c40d02c400304801c1c42220307002011024400d0391105068041100302c5160283c00703019040004540c200807544074901100701403c0400001c25404121651a0010b490301420410465a07607883d84104072404007084500d80c004c0c0503400003030001e0325080e00038207078288550000421041e400720203c0c070b09906403c0c4e1001280e0303009903451081620746128403400c0d010868800c1c400d200d21390300c0c14604401c0c8c14806005003512802406c0da0340f9041712034503841a0040031560184400d01c92114500104602c0c0050076500b030001d00150301c0300232004040c950000b8105028002020040401070f200c214156a11524040006072a6107039156202e030300750350400010904040b04502e0b4800340c44040010621a50940c0354440700c40013890901146503510321a03d00c4031130026004015840302e0640401000809040c4800319600d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 295905809 1250 295904559 295904599
    0x90304170a020907170406090c050618151312021f0302030103030905180403030e1f0203060306100810020702040f05040f030e0405090d0c0c151701090207020d030509 73
    0x1140e041622540200000801d50030703d2205190440d0007464120501030100c00d0616001401410051a142d0307036070f148070140420300103000c02802c40101525a1450040b030b1455203400543d003c9403080019200e181c0418030304100b215140d4031321400e0108a40d1410160150b00405075901b070303800005034000000c81c0720f41d81c0150000e41020b81c400684950550600800107405904654002c0b11440c207092200c4900881c4150b2003a810b00d13011401c0341f40400e900b405d0812851900d1b0000301036a4032000302c41c4054015611070b6800b941103404a98455a0400303030712416205a01c00c2c0c0e08030034549041440a50000c19072580058000306501d010041144201d8000b21401d8403035240d0703c00913204141d800600c1030701d4a24200e0301400181001101540c50f4411902d528051000b409001c0b020011041d188500506829440611b8006010405000c1748a02c41d545204510544004111303054940f094032001500038203060000c0b00c4a50b000c0e82c483d8091507441380c3c09150b00800c03041c003500c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 295907059 1250 295905809 295905839
    0x50402040303050c060108010c050708090409080a020102040806130f031b0803040605010305061807050f030708030309070e011e050d031205010303021f02180609120d020303071707090e090304 84
    0x10036503c80303a0700c41c440c0200314180501a00803821690408a1504034140c0c4a8151035110390400c3d48195958040c100140c024504420010a160004525007451503011340c00361045402c084207443c0c09580781c074501d08a20005050080c91034104420a4010078071502d00d4400c0011203c0c00403c0448540d20b649800c1c1d001141c040307820030784520042c0200142401456003085080164420124185000307540301c101d0390080600408010f01c11444654003000000c00a284203002d0b2a9242050980306403500c03410f0243c0351070781e00080e0000a030300c0c03500003240c1440c3c90700e400f05903881410305c0304000d0448042c0e081601000098104e0109400da00e02c1018000c52094000b041085110f10700c440800c05000580e0000620500c22601d0040042c1c400d41d00700f11044582591314070994001948110b03036844000090702c200145401815000002903004007016159080140744072200c0713140c4107408541c0040001d01700c610400c0410154000c2e0390b00200200c0550341800d841d144c01ca446011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 295908309 1250 295907059 295907063
    0xb160804120f06180308010e0c0409110301080706050c030708031506130302030c010c110907050c0d0206072c150f0c0c0f1c0308130b0705030601020d0206070c02010e0303040504020403 81
    0x2d015a0400000d8031840c40c07804d400d00000300f0a00401e89019120140510610b0100d03146080000d508000600484000e031210b50000c100d841f080c1024010303513030000d000b40e800f10720482c80c01040c03540c051400e50b800b03000c01d10000e40c5031000582c0d91001c43c0d0006803000315800c0c0c0380795003040566102400b42c0301148220030198000c6265004240c5000510b80c47c03141071024805242c408a44501d4811114800903114000b590701c4d0441c0440b4240700700400c01c0068041d0720981c024003a40814540e011320761540d14008207000c2c81511458984143c19442d540481c240005641070030300c1c1501c4240102d030845424209036000f102c031903683e403000d02c454109400076500c000c0d15140141402c03400250a450800707450961440c9160f078240103c0303000e41405105800648402c80d40c880b03c0350142d5100003007084504141c3e01c00780440d00259107140c0035018980d0b22410b0980700150b0f00c1c2c0702d0141595094104401c640056a10303020110366550140020480072031291039900060000b18 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 295909559 1250 295908309 295908323
    0xc0f050303150109051c0f0f2001020d120c020c030f070504110427020405030102040605250b19020c0d0905030f03030906040b060303070204330b16080412 68
    0x3250420102e0350040d000d003202414030a1294090106459604900d03c8007444c41d100400b0920f028285510382a452950042540d158582072030704010445941c0014090000300d5203410900b078900583e101c900d11340c201c3e0300284000301d202d02d80d0b654640000c000c00565006075002908080042070030402c0326990000b9541c098402000b140c2090b100b0030400d004038441c0e450505003003040071302461029420342190170080700c40c81c851099450f4119001800c2c010300841d40c0c0e550315080940b407a0403a405580a030096400c0b11882d00c40000821007a4550100003424156114450541d80700b800542d484a001c0e03082c0405e25036620100610343e20884240c542c8840c90b49840c041503d0903082e4243e0741d00e113420500c1401f011410008545d0380081d4480c0c101600c1d43d40300c0010070710310301828034081c1d070042c10480d248600100f08000c5e880c10540b048c920740301c2c00c480720348110024003441c42800070ba41c0f4100301041b800842c1c0811114520b01c81d003001c0d46099aa51010740308030086030004c0d1145 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 295910809 1250 295909559 295909561
    0x2060f070209181213090203100b040303030501030b2413240806101401080615070b2a07020906040902120d090f050d02010c050f0703082a0316030c0f050303 69
    0x90200300280100400b00124041c03174101d000a00c00c0d4030f51594811150180d40200100d01203038407a0f4402005024042c0344151220f80e00d0030b00030080c00c401e200903540584600003103076040c029015480316031098013101c044000050000c0c0a85103440b6044035030990fa980e203d203419181c895480410000382584c10400203800e00c4601414100c001d040c0c4d1007586800c1c101001207400641c024064080c0900740354280c6e0340c8880100381c103011806a001001000042e1010401c40d000701101d00401030018508940d842d0307441c050240b00201e44d40b40600c1c802c20f2050320014038080c4c0800360300460282000ca00840741c0e6022a20b03010319030442e1240350b04851890281958410001c000418411580a0000b032510002c1410b41d4030380c000107070420660440340420f0110421202461040240841c1d00c2c8550780e003003002d09078000720400c0316440c004500362400080520100074440307510601451419401001705040d120a801c412401d100f04a074006d0081450061105c3c0e0362070180000d1130b66 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 295912059 1250 295910809 295910851
    0x6080307020a08060601230702101709011104050d14010501060815040b01090b0a2703020103060816170f030406050304050c03011e0e011506050a08070903080702060f070209 76
    0x1036084150000350580e403001e02000803587e44182d0b031880f20940014506442410b0200084c0e05c0d1141400107074001680d042c035211500d40c008040c066510091100c852340340c4400f07800c11300b80c1d01c012102c101844020700c0b091102d4034101c450140c40f18417842d0850f4504501566103403c4d54400d0380b000005c200c80b9410440304030751900e24090400700407a0104034040c0e5080002e404807000d8007400b02d6482e00400d840031454000c8000d011202590769851580420030341145a1784660350008a0010341440300c0001e030301c1e800141e50003a1550225460480ba802d1a030b880301b074204076006080b000c0c418946000c0808900f48000e101910180d42c54955074a800d00f02980351034003d01c5900d02a030b01d09180c030808110f03010b0003111521030b02107020650010001c1280d0250900c040343c060104c023403200000d110358210008050b14640c1c0d8483c100389590b140c0b41074441030120311001d401c01c0b1003040b00f980140b514200501119402480c202d00b82603071900410310b0980c04030b50290707010300624180c01e6 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 295913309 1250 295912059 295912069
    0x70f09090213050415021803070320031203070c05070911090a05090402010c03140c01050f0601030e03030112060b0a0803130305070b0f160c050d03050307030b010318020d03020106090608030702 85
    0x101032424034083c03006050650300d900310003190080201c0e45540c046083c07401a01038910052207420300a0464026984a04010070714100252140d01b420b0101c1e0b00109190402240c81d0700400c15280c100d504641d102c802c140e6188034681401c40707040c000d40602040b00e403220b104064102001084c070390b07120300f880740138000c2c0760106402291092844100b008010703070388140b880d64459498585010000c8800c1e900004074010482c0d60300c869400c00d002c103d0304118030490782e8880e031000d0703805015002d550f880300d60f100d03c000e02884c5034205004500c0c0c8045005608420202100a45040e049668544078070b030031a0403030101c060720500c9100c0d04009205081020390060000d400c880c3c1d24090406035811202e10401c1d88400020021804400034002502004001004094100ca150b280c41d880c00401e41e074400c40311100400d24085412455520030320a43e040c1d200b1003104044034070303eaa001c1091140207020b0440856494100104446580f800740000808000b0000c43d1540c0203441002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 295914559 1250 295913309 295913329
    0x3803101e060e0412051605010e0111090d0f02130e0f010c0306060e012105042405011a1b010608070e0a020f1608091005040816032102070f090902 64
    0x80d0080e0704088040c44a02d44881a89410603409105014040341d03a05094172103001d030b0002e50103010328802c3c200c420300c5019080848410b884400820021214880440c114000d14046a400907006c60755079000580324030001c200036000034490041141180b1812040c1c40c08000c41c0205500701c0720781140d038441c2c01d0203000d04609050900380226818210018075504010315500d040000808143c000d002204003020444440c0190a0040d85050b08102c20181518100030300390901600c9008aa07403114440d80c0e06a510800702c05444008415090815070041d2006c488101010710390302c0c1050000b40303d0301004101c10390190455034505000111090001009240c000d0700400070440322940301c1e011a900280900100e030302c05d402c0f600300388500c1d000d03054903503800032140400c0105040d0860040e1040301d40080c111050b032503a1200c2c000d81203c00c0d1100034419030700410460800102d1189503002c0132107030b10403500603580c0c400360901c030b000055000f40616640c80d480317801503041003040c00f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 295915809 1250 295914559 295914611
    0x5060a06080316020d05010204080328090605070303140f09010c02120304020d050a05060c040509071b0206030a0b1909050903040f0311040b0904060b03060901380310 73
    0x300600c40c6030500a6407030b8441e20440f210190107503c8010115600d401a007214190030000864a50b80c0f00c104603980e95000701c5403545400c1038501642e400300d040d0000740e04108415a0f440303d00030724104c03060f60309030000401141450303144c498413881d0f00c003001e075164422915018454014242450b40701c1c03c40e409144440215040710700781e404000180d40840b6009641070300c0312102c400b030504120782040e5442d8001812405107105101240c0d10fa0740140041d00c004039800c0702c0545407001d00744c84c410701018004c1c590380b60454030007000d46411000ba55210010440101d003410700880001c4518100030b0742c0002090300b401c001d1010000074410991b11070a210001c610703150030800c0706440c07034169101c02052172000e01e00f09a180c1e16950001003030030102811105050901d4a0540c0203802900f101c240280f0801000840c1c1e00414040d01c0130f2807520f04007425059030060882d0142e4a000984442660b1220b1080c103120b0700c08000080c0382501c0c0b000000741309040d10403142d501e0301c6860a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 295917059 1250 295915809 295915811
    0xf0604110a1d1809010f0c0815090612030406120f050403120207060b04091a090c0f1306030f0b07090602030304020105030a02130305120421120c080c1905060a 70
    0x610388119402c0042640c24049403079610207400302100004221190030300c2e162202e8108101400b00c000015041000340000c01d00051040e4001c90104480880d02190141d1105e0444c51240c403450800c40342e100e401003c0542018030000d61090030500d568040c1e40700750b0014900c2041840c0341452403242c4280202c248006010324100b5890040c24a10b1040c110b600c07480c0e002442c0e200300305040d8002d13076003900e000d0010b0292085600f0314070f1b64200c1c1203000110021805d400500c902c0310118403002d5000000301000035400c4048144100c0a236141d562103641030f42c880002c40811100c0f611044894420009a1507a2401d07002c0104542202e902c01d8003554010b00c1030000503a003010940f40d01c030a1401005071214001d164070301060007207910261141c0590a1000c0c142d090210007442901d55141d950410040100c1d41d01e025004100800707880941c0244007021010305c56050101181c1c090350190b420607684240d91400c1c01410300b00c40c0c01401907145860b040140c1401500e90000e40040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 295918309 1250 295917059 295917067
    0x140403020109030b07020703050114010519060207120f052b0509030d032c03030a0606050708120601120e0102040e0f06010e01030b010c060515090c042301050c060f060411 75
    0x1001034000c0b2490300008080c41040c900140c030a83c030800190000350382010080c00065801c0d201c600045400703000d042e0041c3c110500d0020940340507121902221480d40c000c3c2b1605251403a050941120072500304d900039070740010a4041358080146203080c034061007140000c1d515490b004440f13a41100000414000c040c03160003103554002c54425540312540c1004920039107010881d000d2000c07c150300225500c640010307074060543c00009544034800441c400c000300d41d203078081035885004a502c010041d402c1004400c4141c100c004503076410850604201000f100d04940c44410ba039820a078041060b9800700c1c0c1000800c01c146041600701e540443c07160f0030b50400c040000e1245800f40c507e41d06060321000e8a14003a44610564090503402480820460410b02c04000d080da01c90306c0841d00c10000c600204800d00885002c4404130303080614a050b0024541450f610401c0b42840e80b5414400144180f6210034001e00c242c1e03110b401f4503502c0182d940307842010041140d9041311100c0700c0101c00c0c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 295919559 1250 295918309 295918313
    0x30c04260309150f031e0601020c030304030212010b091609051c062c07050a0e071e05190c150501050303180402160c03170a0801060815030706050406140403 69
    0x1200702c440c02c00c400e54101c0a40c040314244a40c0e144650b441400b00c0310300000c00c222884002c144410714070140e141421600d600c5034001240d85100311500c4503415041040100b00610b40f4401504506000e070740007090000b403110004110b25400c94003c08500307484900040050b0780300c4c02c00d40103080c0450314446d0545110300c945400c0285801d001781083e5882040304c40c00165141c10b03203160201a0000c10802c662062000d1f03c0360241c0c42064001d000444010402e00010740c1158800c614640e2800c64054100c00c003090340d02c0315a282e220030302c482080035002e505030043e40c5504203086510b40c81070b81502c61524204c41040c06400402185c904001840642e07800b0045036a820415114000c07410015000500240304020715804411030982101c0d041000281415007120b000d05d03a84a030000741c80041c61024450000035000003010b050042c84914001e10140e5000075039a2104802602040082880d01402d5084000491804102049a02c5d4408040d50184000c1120f0030b0501d4515 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 295920809 1250 295919559 295919563
    0x1e0608211204110d0501060b040f080105040201020a030f030905030316020c0f06161a0f060a09020f0d110c0d0810091802040203041506030f11060309061501030f02030c0426 76
    0x1e000182803c4002042c08260341e5440003480030316030048000c20a1070354603c0441a641c1c801e1091081f41040444002540c0d0703410700c6090720558042c1c02914003045c0030758003224451085440402416501c11701040480c07001c0024600c200b007401401303251004aa10041d25048051000c1880303411412401a10364850034140d6000c1c160144070404c5101452515000d048903054140701040b403240704010488003c1f42c4010300600c0c040e0ba420f0314594903020380c03a00344e01c10000800381c2c00c0f074200400d100d00e00255004103400e50102c9541418000d03900c0030141405585207810001807069000d2054288080300c1000042c190b110081260740c040c00c5026245048210000c2d120b01d60100010701404140300e50f511102150700d074100301903070302c0e89081001f40007130b4101a500c007942a0131000b41814100100c900588014008190980c1c40350702c0c0f95007810781103141504040d1111450701c243d1000380051402005a0b080242c0c81e0740c1046515200040b0480c40c5505140f1040f02c80704941d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 295922059 1250 295920809 295920811
    0xd050c1e130e1b0c0c150d0b090c0415110a0b07090609030b0c090a05030f06270a060509010236011404090509030f04060509010e0909030a031e06082112 67
    0x50b000b802504c60403488044d6061031501c5090319000b00d200c190340f20281c003a00c001812a500750f940200074907410740701440342000c0b003103c220446c3d2038100000d200002e0140b6000d440310a113490000d15224900c0ca1080c02c01c074010108803074000008083c400390030703088415400030f810149030428080380755444803810700c6405000e901e0a1400082e0030481500d403020100d0142001808850000c84415001c030b075100c0040f54100019103c12000c5008114428440d14030801210003d0101c03611070385403180144405400801d456500f00700030905601c0382114009070b440400d011130710300070505540242c501075286130365040080b10b403042400c10550000380c0f001c0d03034058040001c450780ea50f44214030f544606c1c8140e02d4468004540051620340c843d0040900000030f990f0700d14030f0502070050019064003510001d1594100b8030000e842c2c3c07840baa01c0b01000280c00c204000c04922015145003c503580b80d0003600880d0800f040c647c1c0780c48000514500000c200408107460850150446814808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 295923309 1250 295922059 295922101
    0x170403060f0b121e0705031203070305070c080a080604060512070f0e0f070f1b110f010306060f0e150310060206070c030804140109051c110705060d050c1e130e 70
    0x29132804d1442420001400540b42c094220343c0b203c01d080760b0792080350708115408000030b401d280026046a101302074128245030300400080c1130800e40041600d07403080003001d144d003056841d000000c1b0341c0e0b03900405480381001d810140090a091080428154080341c0011261451007801d000101c0e00c500740256000031107140600c1c8800905004440071851020800b0380740304100e0b030f000c1c207102c9281c8101a80b40001c0300d4040c8442001c9c4019001e40b1098420703000456015003501440300d0040c4550314103150300811200211036070b01000261a0000d8030034041c0340d8400c00042c86901c0d010010203400035001d00706041d40e80705541e8020050840184024803c00410800d5200c10000b50800c01d082580001a6011528070720400c00040042c0554800001c000c001e00f040d100002103124016201e026201d1450b04130000281c0010341400f50203204a448200700b1940e04401aa500c40442d542e08010143c1d5030651540d210205103e54001009120003c824001e01c0702c07071240c03a0b504500d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 295924559 1250 295923309 295923343
    0xa06080c1e1e042103020d0e03010605040614180c07121407030c1104020406081b090604080d031401051c1103010e0618060609040f170403060f0b12 65
    0x84007035000030056020b0000350248840780312a802c601e00056001030310644981c50002a44459903c9255540340e119500250160b08071911000656110b02803c07240b288005d800801d005035904042022121a540a20a8160b4010640d031141c0340640c500d81c40f02d0441c02c410b1070103080c0404107100c14890420002e0600c040840c2c80b80b0640c0c024500c100b003000b0500003880c1c03600b1441c00c0103002c03c3e01d400b404036403407a481096404c02d4a054800d98055502650703812540d80d50f1010402004001030714038030041c3d00107008050b00e65039600d008101030301c01c1401900c1450b51110b00501501c896140500700b204280c4010700c0320791a1008650004601040551240034460600324103450703501500c00c0d010f50134030200f01d00d00d140c0061000c1c041d0381010303080040451014034090700c840303007a21140e0340080c42201180205143c5d555024000f130042c02c4261184e540b07915200d01592180e4401c44803581c640a10101c010710030b21420102c50410f60700801044810154642c8a841206804000e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 295925809 1250 295924559 295924597
    0xf0b03041a04050f010c181217071a0c07020d020d030c06060b120a090b010b0a0207091b020c191a040909030c150b030601030b0a150605090a06080c 65
    0x406145066408000c07001c0c4620070480c02c05007000707912005000d02490705036003400064088244144d00d001d0543c008401c88030300084c2040007190451140d05c13816034601c0f1040030014038003070308907000b014124403070f5149800c018410903c0e01c034a10002030146805a10a00c54040980c0380c4d0310180e469180e0485070301000032114607040d00c0004020002a00ca24074000c404500302d0400d400410303401811644111844d03440003664004e4407646500200404440350040154204210242c20401070768019910302c50f480b8254a011100c1e40407c01823004a0b940301c0e049617513018446442013200076a43d160440c9214401540d81d03240078480e4154862a00354960081845841510b0160210100900c01c002c140e00300107001596040d001d46010810700741c40750500f0003512510080c42c00150240c4400da10719215125840c03801001801c45a0701c40d020f500840e0b00c0814420090030480e00e034207032688842014810290300317940041701803000810900c81c60440642c19212207113510b060010070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 295927059 1250 295925809 295925813
    0x5270a05060301021608130f0b0f0a05070501150e0708100e06010318060504030806062b0204051f090b090102030d0b010207050904030c0203101a10091e030506010f0f0b0304 76
    0x922445e60030b2071021100d015032100300000240240b841407003480881040d40c0e1600e044c22106170041c4100318101d01c04101081080e040e00000d4204140c460030103d041c8910364035100d0030746801a00704610306481d104140010480f00e14040c0e0040c4803441d00211514001c4403078105114180291642506101c0006415a12980218400b20ba80d44810100d00c800c901d0104050700055900314045070071500007500c0c504284050340c4014064075107549800d1090310381c045003482d410807007291560b000c001c08038282d01d4411306000002d0102c4003540b4180354030b40004140e045039030810082c00204010f007855a0ba400801d0703c0c04494000c00000e000c090703020041c1d00e0301645a1060750440105020007003031542240308007982900990a8902d4030301c04402c1e400031175007100c1c004681131446031910b20b428188081c1140500083c0d0030322183c0c490329070044042d42040c0b4003229141107000b010520030403006101041c010a042142044014204100426040c0c5c45010384180a1070110010341 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 295928309 1250 295927059 295927061
    0x6031a01150311121924060e0a0303050304230c030c0901080c0f0a090606022103070503040311010e1c23040e07031404031e080f011203050708030c0405270a05060301 73
    0x100b0840b0039a0800c103940e079210740c032000309001d0303040d02c6d144484007080020418080c485203510b4020081941144505540d0f0940b01608090402c1c1c401c003180420f0300c1d036031300240024425980c4c84a0000e11006000000301482d200601c440b1500900a0000400404000007080307501e00008031a10b83d640c0450340086005225203034011040682000800108a40c02060900001074480d40310b042d011213440b50042948070984e20980041d604100181c08640308944101d90203d9000c00881c008041c800e88071b1404003070030b00d1001d800241c10402a001500300e00c4c00c0f501d2070081e0301e140120100c1c820820b0143e01482c401d0241a000040004404607c6940000c03400c0c40c46141a920500782800d00410780c2e07024040740102080741030803540006000b401d9180c80ba5070a4906441d107a8200101901c2081d0f50f00000c4051220901001d0001a89180914490301640303000030b032920f00d40f104102003170144000c05a0388040103001441c0046802125690005958801140d00d03115440070034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 295929559 1250 295928309 295928341
    0x60a050d090c050306090601080d080403021501030803010626040f020111160f0801050f0a0c030b0406031421030c03040c080f0f010f0605010203180406031a0115031112 74
    0x15180901d44000e2404000c0030a04440555005504030381250741d903035459540c3d031642801a51201e40c400040103000500c2a076506900c0751003441070352902c12050b61049070220080c0c1045906010100c018043e4961044040010510310012800402c1540c2c42c10207036150050030142003411703500712560559000b0141206440a140119404009005840c8880c00000d00544103269082200011801d605000c0c40340104113400310820300c5d4a405d0350340c0c00106528034401c4141070715841c10700425910703489480b0040d40580c4004960b26100300b00581440c000b800b4030b00c0807920300c0d02c101084e038030b2290503294803200b5000707091b640c0d07202c50070140c2110810758003080c0a03101c0c1151030151003101160701d5120032003490080c85262640c1c0c0049041c0e40a5024040c0140d000380403481c82d800341d40c0c4800e000702c0f1014000040c1262030351150354901c40c00c00d845511044c41c003801040482d403518919440c007034241c6000c00404543d02440c10861041400c00c0e0800004d03400400d21034102e0407084 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 295930809 1250 295929559 295929577
    0xb01170a082a0a0807060f0204080c090a2d0b06040609031403040902040810060e060102031e04082e060b2208100f05060a0602030f0a0306080a0f060b041505060a05 72
    0xc0c3e55850103072074400400d0b0702580d4111101e5003031582c80c000d40440c0d8000d1f036055075000809400a644c1d950709005010758020641c84100d87c0f90b00280000b01d0b6010000d20301c040000074419120300d4089440f6098412507001240107030000c020802c403841d40450b511060b03a41c0540210382d202c4416503140c0c078600940e0854400c031880010300040092001a105191008091043c4410356a682d008004010100c0340e0780d0150704100705018041e0304143c00c4c80368003d01015610f051649038140d0514000080340b90541400006520a2403524a518038410034640200141302075403c20925003640c2c09040303908281d010310640c000310600814542440279210000031a01e080d24100200809442401c0a00d90042d02e002c000c201c00e400d01985840a440c1103400540c6030001c400000003e9503c80e800e03900405540c0d40d00403590400510038004d515018003600c0d00b464005041030b9044684a01c0282e00c01e6142004200040010060100c1151800c441c17040e21810038241c103440c68800c0f982c6e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 295932059 1250 295930809 295930813
    0x3040b1b0906030a0c3b1c0503070b15030a1203020903010510150e031c090e091c030207020307030201050c0106030606230114090d0c03020402070b01170a082a 70
    0x1c1201c40e90083c1d0103030702c442c030342e80d03890070b0401d6080c0041526401600400c500b00c1191a00510302e1b00c001840010700b01000584003100b02c0f24148100320200341c25482c1101c042d000020b0300400d11200308943c03030304400314030010f460b01442c0400184ea103140400e80209a41c003110205106180603a0607200b14180281c0244050b142c8180c0d011441407240c000c10120301c000c03c03070440c29180b141c08440340c555009002000110a20144151041140350364041040f0107034001003481e004102d18035004880a030010150000c1c0700c0f400748006803009100c001050701c18412070015070340003c0c5190850350207007080b0799605c1d11820303611b02500e550381014006a041c1710000807a1140c02440d900f2880c4021050b80b0b07407000d00b07801114266100702c10340440e070300305100003545480d0002d18400e009200d43c08060040b9035960105059030450300041d00e561008000410681e6104105141e4a00003200075041d64109566003115a004d900e403000040c84110025860b180c2d030700044a0001003040b0b00f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 295933309 1250 295932059 295932061
    0x1510031509020a060203090303030112020312160521160602160804050f01020607080103290705030906221407031403030a06320310290603040b1b090603 67
    0x5114080d00c980c00040f40655000d607000124030b4404002d8403031060000300514610303442c00c0041000300344e80040c10381e418029400c42c12035465450f0014074500b0b1610382540c541400781e0038072a00b05080103071444500400c10301241c0641d20b04804894000c000030900382058096070600d600213001c0c0043c002964840c1c0c0082c00c06100c004c00290045030f004039485100d18800c400120b03181c1d402910460046001640180000786400e2003101c03050f05000761080c858400d0518261701d0100644456001c02c000005000720300d0382c01c0c000d0382d0f8041001c0c0079040c8181401940300c1c801200d03503080582141c0104040758602c5800340309510096421900040c0200c00b00b480c0e5a8403903009941261055250a00025211442d060074540b4440e2400004200c142414003680c441034400704495418001c4001c01001c5601030701c140025007500381040a01d00111080000400b85080c041da842a0000c0c8100400160940c44a560100240d40911503440801004032114000c80480c20b510034800b00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 295934559 1250 295933309 295933343
    0x501121a03070f031412040501050a030207020418051504031e110708060106120501050a091a040f0c0201060b27150a120b0f090a050709091505040c02060702151003 72
    0x40520613a40241c2041c0e02492180901d80d42d00c1c68500000030054009010800c0303103601402c058101700c1c0f4541005440c2107030300c0e40028100c4d058071080e0340d01c0c200d911100c0c4051100401828042c0c05034030074507000f40e00302074901601d10700b5030f02c0c1810004016611011507151040700700d0741c00a0071903401c84039182d481d0074030542ca4a00034081d2000180030b2407c6071050421500805049402c0a0100c05102c0e007400300000c0500503402c0d1010354005081101c07581500d940c8511203e045031444001042104d0700002802d454203a80a481d21000c1030050603151051030103196809040400e105c940d00c0c03181800b0405170900d14180c0040680042400c68099820158a60340000f480c1da04002d004030070801c019501000242040d0403401540010301d030385005500c0240c100c90303941020600f07036a641c220442680c4801500442c1510001c10030000c50034140200b0300e21a0040c000b0301b0b1075107012500207644521282210304c0098071040420007407003000312140003031a0082d40d0000f5899140e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 295935809 1250 295934559 295934579
    0x3100e0405010c020d08040b0103060906110c011a01170a1d0d0207030203190f062d0204150903051002030a02070b01030b0f01090e1209030c09071709070501121a0307 73
    0x400148801340c0030f00e2094860041c440c0c10040e20440e809aa2510300d130742951503074401880c100b030080b12101c3d5621001c155061250b0003030080101600008261100380b4604090382d8403111080c60305210311500340307000c6034150241c5540d011000540009103010b4840405032002c20300c800d10582c9000e03c0c4e0401444c00c0e4085039102c2030b280290100c80c8192607800a0585100312688007034181c0c500700811100141450b003040484002c2d01c1490000701d40d5004a03904d468102c1d9408011584e8001810014403110241c01c66004885003085039119203552241500d9180345030381c00400c9680000054013a4080d036058800a13600702140c1c6469607100d01e4010300e2030308140c41c0141078036010800040c80c001e45001d24071070742030060080c0500502070f48100c042c580052210540c14020041780d42d0090712007118051103540301c4e5650820000e0b0344548845030380405000204a900001c1d400e00c402d90308a41408480c101c0c40c0b000091409401d201101842144c0c43e205500d4001d54a00081e07400318 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 295937059 1250 295935809 295935821
    0x3061a030412021c051606290f0105030412020f0601061106010806070509060d0906020d0617011b0309051e0106051e010e010507081b010b01030f0b0a051908010c0f090501051e03100e040501 83
    0x1107900d110100c0d07d0b000800c000b02c8500310271540000e104200040000381c0b80c000300c10a09092703004032000021043c003c1c5040c440241c210600058803400210480342e020001c15005141e1000130b01594204504010194440d941b20140210000140384140c10741390340c00b044d02c2c2500702000f15101c1c6028002440601302c9442802a02d01c090040850b1401040c0324241109031400052281d4080e21802640503003424102990720b03000b03a240103100601901c46900d4840a10000096118140020407142c952100c038440d0350804011500c0000b039070031008441c00c128090034082d486c4c030070710f1401488500c107991072141e44600000c1c3d102203180054101c5901c0d0a001d8030309002e401d01c030ba0700f580c0840303d490745550362004000f00e0410580c2003483c1e0444007680038503140300f0100d450b06101401c0d200700307140b1540050b81146a0900d100d07444141003000c0c0c0350034a00240f90010401c0d46c90016001e0032808201e600001000c10301d041c1008040e10020016196001d50301c0c40c103030078454002d02d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 295938309 1250 295937059 295937111
    0x100c02030a0e030c0f27191b02060718030f1506060c05060f040501020f0315130e061b090a08100506041e0c03061a030412021c051606 59
    0x1002920010b40385004503500c44501006000400d01c031408504000c03290310102c1100300c20101034a4514a00c1c0019040f0b60301c103501e641c103e01c2450701ca420b6140308558416411300300314100d00040ca901c56038003098080d0003032001e15001201c941c040c02d8802c07141c159030b03000810440300303443d024081206012804844080c0160100007007603179440c0c281d1b42d000b42e1680040898020800041d0742200e900d60050308940908001030070300000101c03e124551091341e540d406c18504a0010105181003c0318210f00c0c007408100b4800314042c841c2c0140d41f0340c805001d090b01c1d801954101400e074415481a40c2040700020840e0000716590020325031207065521015840b07904140c001081c9080500614241c5034215100800108a440b2007a0050a0a1610304105501c5000020f40c50701d000d00906060080084d229990b0b04041c90250400704001c050300c0b081d500204c580b00081016281c0042503039445080055075140fa540f2044004105a40020400d51034070000c281c0209500c030000202d04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 295939559 1250 295938309 295938317
    0x140105040213030206070f170301081002190c0f08130609080708060c13030b04060519060303090b1308010e250b0706020d0914010c120e071205100c02030a 68
    0x198994051200364461120b1501c2c004071000b90820050030440020034106d400f0300d100318aa48440d945d2860a0f40c0000e0310b03180000004001407014082c10303c099900c03501e54000462400440901000e0415443c00020080c04805014202481421a069982954401031550341d41c006a440d444401d080c3c0c2c001c0700c4c00107468100209030140c0000b03624081e07030001d070002e01283e80c4131840c0003003a52250781401490305008100100140251640c2401648030310000304040c274084402401c42a141d100c1c0c64441410880e042010a80001d0b50005441d0781d107100540c2d401d05940c584109020356840208298a00346492540715008982074001001941420000c8001c00942b03100211950080107a8840b0800810001850540c001d02105036408408070348202107071203904003100c4820300c0036142c0c0d468801d50207407103a0000d00b4882c0e401c01c011003001b60018090030035580b0b00090142035621018901030b2820b2160821250321600843c03203043c046500c0001000b91a50820507062001c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 295940809 1250 295939559 295939561
    0x1709030c07140303180d0c060309030f05090904060b0303090306010305280305040e04030e04050403030b01080615161b060507050706050324120102040b0405030c030304180e010b0607030314 83
    0x691401d4400d40b5030854010001c509118440c2e1000c440e00a07121800c5038402181c0d00620001070307200c910540200101c1e1000642c100316418007502843e007480103801080420032020040340c0d50703031003803940060300444009145646180420f1640c480d0f000400d51600c41c110000003040000110141d8095108800c03130b03e01c0d00713154002410700e20500f5008010660602c028440046000c0c0000d500601929100400120710004a000c5903c180d4041e8006502d80c212200d45581040c0034507003009080c2c503000302d02c221022070200180510b0a80381d8601d1800d1800d20240546d00100c2c0410101000e95201010340d59071020b0440e0f400140111a01c0c000c1ca280000c06600400950348100c2d05a20f55244115020000c8a01508401c400640c4004401030281c041c2030b00740f024001034895100300c540d6440c05c040400d86040320030070003039100fa4001c003c00e0024894962800e18103049116000c140c01103451a01805000c2d102032864100300d000c01d001e000d0650540040340071010416444a80d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 295942059 1250 295940809 295940819
    0xb1206060a080607201009060506031e070b1b0618010f0b010806090a0f020a0f032a1803021807030b030a050d0f05130b0705150f040f02011709030c07 66
    0x1511804c60300c0c82c0200d20000805401c120028044850301009042034a01c1b10305d03000042c20071130398400801d80f0315903030b5441040300300d04041040d25110010040d00c10907010b00744028a0b0307102d1050040003401e43c401714010420070090b0116200c4e114424065544074030b000c5000104103001e401c5805180e6080c405950450b805030b200d82c2e405048103035289512540d40e0350901200c4100034050781c24013036840e4406910140c1c030344050300101206540f0340e6440c4c0c100c51343c002e0603105000700003004658600f441050244061000c10340d1040642412001ea010b003075070404210741282d10294002498901c24841a14581c40d440d210340c40a490821000380c1c64410b041d80d070300c694440140b040d404001d400d10900d0203440300d1521250f10b440c100345400701c91032190031801d03080d90015601040c04280501004024801110309a110303d1004040d0324001c46040c10524029001412102c65014120190b900c10400f581c000900a030200e0818180343e5843c0d980c90b400b5a00b00450341c000c003040460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 295943309 1250 295942059 295942063
    0x90312130e0415020a050c0706031d06090c04090c03060c12050a020c071802091203030a1b021b01090801020a08060f01020a0807200a0e010e0c0910080603010b1206060a08 75
    0x2c020741c0c10000d08081a04015804002540155080e4044c0720060045511480c8100711002c06040982d8011400e24003148034030800341c1c0e0080846055800c51004c00111030000980317003c0c16a0101e4000c0742c0d0b8507003810b04d9201c0750f8951f0030103000c1c9410010490314142d005184002c2549202c4010003150b0f541c401d0440c1240a41a10f254142e08186810000c0d810140c04051490180e0040103242c140f0020024000080c0c0c02c07000410744e0000700400075420072520407080c0c50048044a03840c0b0040b660402521079045043c000000c29081030b0640080e4880d61000015060301e00c002c540e501c0700014040c103120422a151441a10a0005c3c01c01d59480800d5114010f548031000790f040c0760321aaa105203907405102030006c40c546404950712a81d507070001d20300c0200150454411103504110922076401001000c0441c4440100904000d07626960304aa803402942d1803c560107440e45000a4050300004910a0340040c0d1007600c08050480401d280d03000750003c40760200c01c1c9a0b2005220307 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 295944559 1250 295943309 295943311
    0xb0a0207090903051204020105090415080f010e0616090f08010b0316050a0605030402040b0d12021009020f01180e0709060206060405060d0209070e041e150806071202090312130e 78
    0x3c0004409000303185486406a00c0c494202c0d00c141401410407000c400410101c443e03050001e0113441d41c02c0d4041040c80005d000c0240340a500300f000b481481700d8100740d039903a01c1001e0070050002d2403002c00071031071034414080c040c058a42503810301d58555490317000714041c0c10701d503401511902071b40710288009159411008111100504a80a5645064404e5609420040044e42c0158591400e07000c2a42c1d600480600c5509c1f03146074046508200c0c00091403d40c0d02d042022506140030020809a83d03410140c80074804241b07403402d46107114101001c2d0f1441c1a41c40380306050000e10500840300e4210b80c41005441540d402c80d046503460200700300a0f500d0035102d042d00411080c06c0180981401c10b41140d102129041c9000c1c52103200300400c0440740b074464050318019504c0030610500300c0900074500014040a0b03801099030402d00c4413500d429000d4000c40a210304600381c0e020015654055440c907200003400c3d02c1c44500c1c0040d410901d41c0c0301140112080c10312074008100224070148407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 295945809 1250 295944559 295944563
    0x9101517070302090d0f3002060c18030d02100c090f030627061a0103022a07030b1303021203040f08130e040c0e010b0f0304170408070b0a02070909 65
    0x100301901c03040c03401d500a512a505142d0051001e550140104910301c070000c00d01c512846000d001501120b110001c540c2c007106406180030000780301c03103d2113580011056040004620f601d42e841092100100141449891198150058210300542c00f500450040c8070401e1200301402242c90350982200c5203040390007075140082c1000b109101140d155030240d030307040d0605480c3d110011200081803d01d400340000c111003c2da20b44d0406000661a4400202500002e007800c0d0f0030810781d040100a0700406400180c03800c9050310a141410008002d101700440c5c04c47c10702c15603414440b0b00b00300c4004290406070094450800c16901c0b441c28481120f2013140c000d01100540002556900c00d00e40c03044007a00140319a044001c10040c2c03007012030901440c4542d00720044a4034188a640200c3c005a000080c0790106001c2c101040300040e08503580903600c9140f0410301c0c0055100c3c20303014010360300200c6241c4200100400c0ba03a0a90b8002c020061003a02201d803103179611510390060790210240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 295947059 1250 295945809 295945847
    0x5030115081b03010212160207051807210608010911011b1b170a0201020d051c0f060902030f071413060305090a06020c0115210f03030b091015 63
    0x1402c0d0380740b0b40314024a0808030001c0000d413400e171030b81850b6020004140c0341100c049559400c282099501041414001c02d02030310b864021150800b0310b0361510300d0050441341401200201d40f0209042c0c1070b048120b800c9908020030059455070340c0c4ca8000c000301c003002c445031105510104034940c080c45ea2960400f889c00c840825402490343c030302d5084122040308844d0103102d1980401c2c500b010340544d01888604500500745c6001c20b0000900c1d103843c2c184650180601048035802030000040c03074a44010300f080004c100e0141c2d041a500040070541e1007000c0e0300d8030210922080d49007c50f5002e010348140d81c0c03049400d8054610110143c170419142c920014000101007001034026080564041c0030502500e10b0740d0681c0d211202030b0f174848034044080d23942d20303030702010100a0000702c04060000750300d0586105c44402c0d6281842e03080c014000e00150f88050400007014800c0e00500120007014103812094103064100101c541168010044264080c6050208071403090098034104039421721 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 295948309 1250 295947059 295947073
    0x10605040509010605240415050304051b0a171908030f01061b020d020d020d031107170d0c08071407060e0f031005070c020627031c120f0c090503011508 67
    0x2510320009240c40b0020030300302c00a00001404160000e12382403000e019884480c1c0d0b80c0303090701c1d02030b080244107850307241c104581e00303002c1c00d668462545a5041d00c4007000c49500c200325110a185c6404101c05c0e940c1d07410704070b900c6548200b010070406540103000300301e00814513980f078000548008410203003800011740348203101405860040018403201380003502080b12130101e5000700360860350200060f00443c040702c1b411801c07818100241c0004200b01100c0c0006100199409610341c250b030001c0c40308002c03004141100740803495085070203940e400301c1190b80c44501882c034151194818810100400e00a003022500d03403c0031780c82031100c0300c00103000d086581d2548502600500e0003820200400031402c0040d030060311184010203803000814070f0459072403403103c1e2021944035014035080c0281c11400070300e01070740c4214242d42010211400d2a00c8460320f14582d0000520041d01c20000041c00c08441e01007a9070406101c030103403001a4000c0c0040e80240b0302c050042401d0f4401c240c45648805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 295949559 1250 295948309 295948339
    0x20307060b120d0206060f0406050d0f03140d060e0a14040b040c0b070803090c060901050301180f09061b0816080a0e1e060106030603120f0c050f010605040509010605 73
    0x58058810310200a00e10b55004848804451401d010071001a0140e40700300c06108162820884404400c030040300d0611035030703040c4404a42200408a002049510700100c0da01c10103000ba541400c807540d600503925107511503c1001e0028017030074810894440c6030340010400d00f01281c020341c2d04183c0b2026001d07034a6100c1d50740750180a031000708140c134940c54480d00442d640515a0040100c6030107404096201d00713003962004c3c101500045158840c1c01e08100d00070440c0d80001c1a01e04592120302503c0c0342108041506000c0d0017605180e195607450a030716001048a00c0d40030f452107441700c02e02c203007111031004807d0700d80803c181d450011041e840034805c0000e5118800300c942c4800c060f00e01050310175080b44110304e445111000000c50203004030900d40503400401c6100d00514040c80e003440080e145445030036108185883d0f00c001c0250b4090350400150003640081289a8000304484015030115811802800e440c080c07540700700e00746408542c00e00700502800c001e0340c0f0010030070407c2d000c800c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 295950809 1250 295949559 295949561
    0xf11040b0c07090609020c0708060403020a081e19030b0901050105090f010306050a0f03030807050304030e10020a02090c0c10150504051e04050102090405070f0c0b06030f06130c060f02030706 84
    0x81940d80d14456070001143c488818003409000b440c03600005a19240041051801c04120390006034855106d00304101c0400da0016443c001c050b0040381d0140d44412825038410ba001c10007094846031240058818408001d002d56915408038a9404004400700402003201c060000c5c8a860b002501c240580702d8180703031007003001c261074070305040004030580e9480c0421104280d650003003443d0805801e0400c14103802c0806560b105519143c402d1541c034050b90050304a01d03082503101d00440030050071180705c500030450000e0003031300104008031910f459464840d4a60040c1d8006081d801000e1020304000180c0c085c0042e070441030b42258112608010504c0b000782130042040500c0350200482c45006601c41c0c0009000c2c074061000942d81d08034450512040c1c4001411b030800f00414841c00d4400361b5807010025003100d43c490488481515040006840c00204032040300711401040c0a22040c2142d80d0711400d10240f0400107024400e503034030070946692031900203a10240c5c0040000f10700149403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 295952059 1250 295950809 295950817
    0x503072a0204020a0917070f150c08090609030610030c060c0c0311040902060a020d03050c28021e070f0501021c05030603010213081e0f0a03050d0f0c0507060f11040b 73
    0xc01e16001680554510512103c003261400300750450f04140d4082c021385894062080241c03270f40750b0521011150b2124010f00c442d5101d9809047c4100105000704550383d1401100c50920000301150701d20300301082003141174501032004a8100c0c1420710f00040b058000d8801d01c403020b82183d1a0501640380d5101c40240604946000d80d000381e0750000d10300141d8514003d05802c1d00c07154020f000340161002c01a00b1114060314021456006004110f18010814034040f52022403241007400019111001c0e0b24182c5408010540034003a81c0c40011842d01c002107a40c11100362200b00c91465554400680c0c0f0340c81c5411a5880d6040400015008075003d54021608224007a000510306182e8070154036148100340c01004041e080760004061200c0c0c0d520003c1809020340b8050001a02200c200c00d503140d040041c02400e10001240414214031030f0780c400303448440300d00401e20221b1401c1d2002031181d4882c0d0012a4140c0c03600c5e002c050a101c56104e02d1000507446e00303106103000d003001459112900 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 295953309 1250 295952059 295952077
    0xe091c0c0809120d0513050901030f060e0705150d110304030206061002070906090204060f140a0f090503010203040b0601021e121c06080115060302090612190603030503072a020402 79
    0x416228140300c040320401224a40710f24650300d0039140e00c9030050481d507801442d1f12403482424407030018408a444008100d46407544084000b480d103038502000f03030074400d5030342c09203500c10810391400c90380401500041c000089030850030400880b10b42c0020138a070005845c09001648540f000800904123500c1d1491451010300480307001580d14100242618446d03003000007495004141009010740007100b031180c0007020b00340542e02e01140803021a590140d0000390042080d40100c040d0858040c0305260301404010700255035070b261608008502d00d0056803440d0061240341d12400d030b080b09600d0005001001100a030041407003031105506250491410400c6600b0075042c081d028965502c2090024201c400000c00c41c00301500c000c101020644c1d00c10801e0500400c10800140e440204450612001c44000030030340d1900e40c40c0d4401d20700c10300a501c040625208000c024150004051407288403503170780b1400d2170b910703910444000c0e8030b6007008041c2240d01d10740070100520b8130380c0150801c81e03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 295954559 1250 295953309 295953319
    0x230420030703080a120c0c1203270c0f0b1c020f0d0f0905070503030a0e0607030e1c061b17040228091a0102340e091c0c0809 55
    0x260b00ca8543c0c510a5100020610216030454031070003514000b0f02480c004040e42c0d06005e69400d0440d1100280780c0c1d859010f030b004040e82e841705000448000a402010041c2c035209003a004c02c1c80e4034007004d919055004045070801e28800001e1a004003004941c64000c02c03404052a041c008602c00c070183d0000007103074040043c103008601c544907003885007944500c611000400c0381151030404600b41078646e00214001d410800c41002010380004003a241000e040c0c80c0d940e6a0340003410f003141c2140500360340680c04500a021101802c803580501c8080c0c074061101040170081400701000745024021090010411020001c0b100000245c0010761041c0042c14000200410f03040c501c01000131220042c1410074080400d0042d08107a1040d40700540c1c006001900e5001440c00103942d80c0740030514107661925140581c449410580c80a042e4032803151004004d41e40c8a050001e40090119840e205a20505d0103500b401c00a81d10480440040740d1205040304116445e02a078a9101e040e240d6000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 295955809 1250 295954559 295954573
    0x503030421021e0f2d06130312080a1406010302070c030206190206060301061d1008060c0304030e030105150f0402040b040303050a0f0311041203031e23042003 70
    0x168075843c0c0c185086031405020041506110001c01c000020f500007030341d01800541c0d8015008074010045400c1050034829281d208150100c00503140348103c803040700c980d10b0b40040000801806001d024215112034a80c00c03096611000b4100407580b6034112072142c5100748000c070b1a030394000c0c2c1c000e2500340c0c060601226401d03207171307000300d142c41d48040b101d00840700c900d0b070790304015a506220103074000b08214000e1001c02c0c0f0b0402d801d101215882003e581e124562404031b02010fa08110260040101c3c00c2503821501d0000c881022a41040f01c0950201d502500711080c0c501d41071040b240700e148007212403018040050180b00c40782c2c80d881d060035007081e07003004085284115000504001d43c8a07079596981d421184100801d1480821454014582000b007031180c580031210503903069810b80a5000c01c81078403420124080d00540f0884403050700c98000c5204401c9003500034242044140c0041084488183d82d2260841c60849024014a880c440c1c0c140d900c1d000c2e0354005502d040010222412 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 295957059 1250 295955809 295955813
    0xc080a020c07080a1118092a18011e0302031c170106170106031e0c03020708160c12080306010806010e090414010c020c0306130501090c060e040b010302090904062c01060f050405010503030421 84
    0x1c142c1003d100c0741f09c0b4412000042104080322810000f2441903051120103540c80d41d03012a5a4030b140040c0b036000c29103c0c411440505100310101c4081c1d0038011040342180d41d41e40c50149c40c4900c40c2c064000d5014600001081850280c003444428043c00c4903601d041c200b24040e440004c100044000c810550200842c40c082081b0728040d0541d000c8114689044108614200381c0042c071552040a40052178403019002c100b840d42070f66408003003800c06031060b59851004036004003c170745c2200c0e8400f05600910090181040640d079044114400810030480a8a000c1e6941c158542c585940b40d40700d900060364118243d0005800c0d14803650011594400d1a41c035261030346c03003e400001c00959400c8c0402c3c8039123040d014014548000307090440c9040124400316905550040024019545401d0050301c0301a1003018140080030305131140c0100105041c1407400780c100f510070443c056140ca180481c10b440c0030b1240d07034122540100254900341c5410318100c2901d40c0301d1010b1440240c00109600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 295958309 1250 295957059 295957069
    0x70503042a060809010606020f06040305180d060203150909071214030c0f0c010801030b0f130803130c050405070c0b0c091005120a0c080a020c07080a1118092a 70
    0x10160030b180e16196254a4002c20702070840e5080d500101c21580000704448070702c1c3c0d001ca0003540043c0c0500d01a562000510302100290010300c15003a04040e0040c4444140801d0340c5c0a54004c00041502c140044c807203404120708000c0c1603951800642001c00200260450440900c021a10450b081d1002c101d100001c181107400480001156401000241020003130511900f840400d007400d200c149035040d500c4040e4501002441c2c0b4011142c0707134000c00c115445c0c5015150101c2d502800e41030ba80d1521a80380b0402c2da0800c40111640344c1240c0000c9074078903150207928850315155440c1840d01310f1a403a0a40ca1120103440152070070804c0103003030b01d603440350900609008403a0b11100e075100d0f0500c00f07040300e204e002801d00399464070b0a6074006419900115458100203010000340e02c0c0c1010424860a020042c0d000203840d10510640708104000b01400050520b0129a071001403840038141c004003c3c012140c0c003c00f500008008601c03012426440700003440040d0209100c0c140d1032001c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 295959559 1250 295958309 295958393
    0x21309050a0c0e0702060f271b0a150311070611070213140a0b030c06030a141e0718031e0606090b0607080a02030f030a0605090a0507050304 62
    0x40c40d00d411440d1100284015010100002c1c00c444099000e030346000c0c64020b48842c8042d141c1840b80c4c114001050f000c2c906c0c401007840d503103403200c441c00301002036400c001c1d5641e00850141c0000c02821020483c0340c81d004032400100d481d0469804006003d040084004281811012440300000c6c400b060201d10184100300f110b08010404641d100000d00420a401300e090400304906410420450301000020b003003250030071300380000403071542415000241080c4102c0c21868124002004200c01061581c1181e25044044450090592a0050381428801501c80c0c0d50304142030305800300344150712614190b0300d104110001c8805150b100c0d0340781805200c0390404090842043e14600091101c40e1080b82c1c01429083c000300b005080c0d074800705105004030384014120700c101046211503180240100ca2041c5400d8036041d54900c0c043c8030400c01850b4500030140201042000100882c413136104990090501e600c0f414295039440e074422026074001450078031040c456a0042003410610301c080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 295960809 1250 295959559 295959563
    0x5220602090a0812070209060904053d09120302070302061906030b01090b13061d04080c0d180504110409020a092c0c04060c03051b03040b0d050604150909021309 71
    0x20b80e548617100d0041000c0c5040260105208441050074800091000621100b1655107114040c8900d1030824003001139405405180350060005000c00d048000c5640c0070501c001c0c4200c44e034000030100c8040403422801040e80c02005030f8000c20105120b101c501c0c0caa00030001c140c910100e41c550320790f84c032030892072030aa10a0340101d88803800302c2c0143c80c01480703082031001d8019080102520300601440c502c03404200e00009055a000031806204220040340c0d8210300315811144010107002c0020b0407a2041e407200c0700d404400e200042000c0c60540101224588040034280c00e06082c40303004402980901d58800c00d00181500c0005d826038200003000c540c100f2410f00c800c8044510144142c4040c00802c99006180200010b10542d80c116181c040c0507509403074541d8846603111600001c120202d4440303009031102040000381d0404a400a2000000304002805940c5a0006000070349003002c0101c259036035082c8080c0034807002c50f484250510300081402824000301c0c030004080700c80360002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 295962059 1250 295960809 295960843
    0xf010b0a120b0d11040e010b01020316110d050a0201120c0503041e0b150307050d1a0603070b040e1602030c280c0306090c08060c0d09080f0c1005220602090a08 70
    0x1415441d05c2c051044e5001101d40170002e1042920030b1000075107a105042640380f01d00142d02507031091217010915040300c6135014202e600ca0440358100295100402c0f20200c1c00100c1c083c0300000154507600920355180c455840751401c54444c3c2d41c2e0b0400c407201d905d0003d19400c8801c201d50340451082d18215005080a2160303034000c030b00c450300345402e02c11140c018500070701c402d1444100180110b41d582665880c418403000d8240c0b40c2c5000281481700690140503240030115000c1072486072141100d000703c0624518034450031402c01b043e6102d0041103081e150f983c00c02402c0174100f414000c102110202c1460600004180c1c039541d80348901070716001070b200c0c140c1c0d07801c1c0724007005401c100c0d01000c2c000c404001c0c411480c080c400000e9030300c1003200855005031030342104010051500c1c240c0d0001d282000e00d03076865803002c01803a940d80b0080d03601a9880d03400c0c00041040342003a0b5107000320102090501449103102030316000045d511060304c15800c1400c80d43c0001e04035105110100c0200d602100b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 295963309 1250 295962059 295962083
    0x81314100903020f0309060d05040f0c06030209030106090b1011030d090507080607050313080904090204110d0b06130618050a171b06250204020c010608060f010b0a120b0d 75
    0x2c00a14000400f085050710754410400515240d03501e805481510300d6041000c14103558500d0403052140310280e00400728042c1400205113035806801400d0030a01c19030003044016602e01c25441960694100e40350040310b04c0a0601c4440d100321040e110900d80c01c1e049900d0102c0312030368101180d01e0ba91040e50560020300c81800070000078014550050800e00e0a94118100700c50100381a4401040040440c5000031719034100d62a04d4111035007040d0010000c001300781c055a04030000e50f000c9054060301c00d244c4a40f51026140140c141d0707030000d03400200f00da00c00d414948180e0750103500c6070200d6180c61101d2800039150b514a406000030302800c21822800c51100b0031070614114619601a0f818007180c038180d00c0c117403110300a1b00c0e43c0c01000952180042e1103800b646241e440c4558000c3d4115000044480100c10150800030031200c40500b00c80703895482100300c112030b0000b80200e002525041000241061003220a8481401103001c0083c1c0310702040f00003508660030100890721106800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 295964559 1250 295963309 295963313
    0xa1505040806011d0c070309051503090609072601060509040302010213080309010f03020f13090b030705030105090303040b09070e010618050d02030d20030711040c0903030813141009 80
    0xc0100c900600f0058107070002c0d85800700f82c1c4c40301c4000003001c5041d0514007089030030a040c466901d8034014640540181800800709031f0100b6240c2c02100d9a441c0340c400c410124590800018845c4100e4003101002803600f08010b01c0d0f11024032003001c01441541d00c404c1c021070541c2d00c000042d4000e0740301e130300010303030b07804540c0d089160400c2254030031040d40d04240582805a600405081002c02041c540140d882801409045031802003001015016121450100d00b28015a000d011044021000c8a0006503500d003054244c400031076120381107400900200d000941d22000d0141c00c021410306490141e5110904845c0d102426481400065658404640780d0280054082c0280105903160540341d469034021075503d540f1100c030807081000d010a0946014642e80306000b00102c144141e80c0e4542207802c0400b022045e031420b0038415460090021001401906000c04503941a103e0b1b00b13030b543d2030356950000ca498524080d1030508480454030019442804406003640c9001000100c1488034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 295965809 1250 295964559 295964563
    0x70c1e14101409060402010309080d020a0f023d0209181e0402031b04180f0c0609030c12030e060307020114060303030709050409060209090118230112020a15050408 72
    0x1800030b29001c20110512058440104186600a4082c00c0c0801c00c00300610708035071544034542040007601c0c40802c8881a141e4065800400d0010540c200c5400850101706040e8106500155410365000604039802a5514058030480005420350060403e08200041140010042030010000c06500304000684d620400c11030302692080054400e5464941d000c00c1d40ca02c403491065450302d06c0903014603d907a0751340d00300c0e0f40102030303140c2003421100880c0b9204522880c03840040720244240b10780810300612030340c41001220b8000d024a1282071401d03151405020f18584107400304940d9409807219920307218021402103245030300002d820500c030910000c20500182680d40300390020000e00098641c80b030b070320006552049400041000051801400a101d9440c08030381041d4500c7c00055a024050220301030300710300f08001d1092044d0368886a003407000b4418180082d60942005101003241c42c1740032101c8a00c05800a0003098884440076003580c881d503d11070000c1d2000509000c64801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 295967059 1250 295965809 295965821
    0x3060c090810110a0c0c1505070302010516021903030605090c04030210020a020102250503010c0f181d2701020a110a0506060609031f0507090509070c1e1410 69
    0x364101c00c025500001044150303074414068007208110384007020501b032000c8003a21500070190002a40d1900840c3e80300a005030700150341c16000342d40303050000342801000075025200f03c8c082da0b01410030b12035181c1c1c03407024801e64604142c0030140d50b000c02080b82d880314002c0780d0098849043c490789861940c41000010a91b1106150464100c500906c0060b40c00050100c107c0110400752448a440001360b5050705075203900c00c9500d0740c01c002d404d01880d904548080743c00d03840341d070344d900ca0740004400c0200c44c4a03192260315030101050051211280c00102c0d91a0450210b212402c12000d40c1640d094800384000c8002c0024cd50000d007803200540c000064403482818200601404242c50b25500d803500c2c40207007050301821703000811704050741e0148404000c4101c003c99035000000f941f000d40c00140b80803284040400c101d8180414640b624228951140b4010303920a45070000c40ea0303410810200d0901e491050321045d6045000141d2100d00036a40070404100402c003004d0480c01c4441507a103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 295968309 1250 295967059 295967083
    0x3130801061424030a09020d0b07020606010836011d06060a05030a1e1e03020d03020c030a030e0f0d05130e0603030f070309120b1609050f04090203010603060c0908 72
    0x42c003581c4102d00d46000c40903a0f6001200421890300c0e81d4941080c078001c0d0030740c0c0100a500c043c54003809020004510499400780d0040c0d03003114055902c0c44015141d0501c1964a082905400900c525916402003140e00a8103640c036110701102c1c2e0f003043d255080d81d0100c01d8180d100b4540074990500010200400380d401035044602c4a030052034400441e44036400800054103d0390011090780201d500da008401c0003552209407a540101c154440d516001401c6c40c0880c012f01500222800440c400e000f603803000407083c0051440c140c1010310a90080c0b1105140468500406003070289062051110007a0441c064952503a101c024201000b051101c2d608941080314900d414022503031000000c1c1c9105440c4110656502c42e081d04083c1c0e00b0f200540d00c4014200d640003080c50030400c40000e2540515a0a05007100030701d55580e080d1604c455038010990084004504055103150680042c86aa030000e400001c03000d0712501c5036801d81780300c0c406050110b0815041000b0a8a0422406007451 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 295969559 1250 295968309 295968319
    0x9031806031e0c04030f0c060809151f05030627030c060708040c0503030a030c020f06090d0c020103110a0e030d020f030d0b04021201030605070201140411010809031308010614 77
    0x12078089500000d081c400322001c01080e81041c00143e425292a044602650300001c415030140041d01d05680318640e5809804000745078600400c5140e0400500408403c0030343d41d00c100c0c1c0303585541072140002100300b4050b2260134180800a260313202441614040e181c55100e402c00e04028003140c01210041e91000c541e03661080011400091001c10030581100f032602d450b4a450326030b81450940101c17903030015680360000190314804075415070b00c8003a03590056000d50302c40b6654550603548550040700d04040580181e103011613004d10403d050344080d8414100040c1020514030190b1081d00f000b2500d4012950a007141e030494501004860a0396a091009000c400c01c0304c50882c0d200d009441002140c584c90752012813030796540e5016149401d03c00e208502c240c2da940e05108000c0d02c01510408055440c0c00c6c00741f070050300a040428819a044032100101c82e0f641d0340119502c0b900100030005901044c00090b0a402081180b10020002c20001248503800c0120a024030000710125501c60 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 295970809 1250 295969559 295969561
    0xc030909040c0527040308091f14010905060d0201080603010e07030b061c0c0509060a120f0c0803040b040e1503070303080103021003050135100501030b10050d06090611030903180603 80
    0x545180611654815032516251f149625a000c02902c0e10395940d030382c0c84001945e90050b80b0400d03090b52010b076500c14501c0710b00f02144d90352103801017200c10946070746401048190724100907500903848180c02020203230000500c04c0c04041d2050510a881d08126885110a0706005041c6040903207028408686900d031000c980750780e074451b40074444512681d0300a540180000300c0796075480c0c10300801013003102d091072109200c6160101904111690895030381c0c24200b00032070464000801e507029584203d110310301d800d007058801d07651000004c0028034014103108030400c16490600542000714400c1d00e90207400c5d41144100b0400d000c1c140c0d07815080614040040001c1851000e06810854007615404001d04080800d205840031f0340c000c007003180c441c290305080800c0099204038100c0f8010281a903180e11801d06c02284207445201e201e510483d8003801c203010450503031185881c1407141c0310004003000005000002a0421101341c2050f800109000305800d0000200d41a030310012568a891 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 295972059 1250 295970809 295970869
    0x30e040f0207020a080c0901030f0807060608060603060c180904020a030813090506030a0308071b120507060e010b01020a02120c09040b0601080601020a0b071101060905010f06020d080c0306060c030909040c05 91
    0x540c8105110180c681c8031900c03910b406010b4034030200d61a140d084dc1c13041c0b26403a00c50032810b985810a94100b40640b0800d40026101340180098403000d41c0b0024141e0740400c2035504118001138094800d030f0340010000000070000d40582c0003400f070480c1683c1e5400f507407498544004100d80008001030f0080e044641c100f40001e41c0000a594131840ba410a00d103410038030f24801480800b6068020000c86542c00c8640241c0d81005c0600445480382d2801c0c0140020a40d48600340c1d00082136182c0540d0155091400524100420680608036101120717162114440050112082610151f807448015424003005507408161540c1c000420b000034561318800c0d959250201000404040401c280c1800c501d130420f00a4000600800c103500061085d56100c02c00e14503e114640715520240c85070a54a000c1e150040101324411034698004d44c0c119981d000070b00c00c6540c0000c100c5801f03804200500341d299580e441d501c80c003880c041c501b110091420641800011100b19450707941d40c460b01001000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 295973309 1250 295972059 295972069
    0x60c10050717010f0513090b0a06181e0c170a0203010609080c130c02210d1b020703060b060418061a07200a030b040b0403030c0e0f010c030e040f0207020a080c 70
    0x2003254001d541c500321903a030402c1080010b214151f4004d00320a00c00c410302840000c59001001980c1c0c09099584401c19164518011100c01c501c411032960711071107601c2001c44403948110702c00c2c1000c3c200781c002104805640c020f00c8408407880101154040b006002709503005159001815000000b407030112900e00008000740f00e85900000c0c0c80b0740300c1c882c0040c100d02c01d01151a94401041400d4282d12040d852012541c1001001072034291070700d0482c059231a540c010800340c1d4a0140c0290002c9030442c0c803214080c0c02460203581d085032040200040340496034154110000202e10002022428140401030700c10f00c2d03132841d49128605015a0740404e440384c1d10210140c091482448800101c5d0b00800e80b209084e40c8054503402105007000300744102d000c41c0b07510961083d40c0c20000103180780c4080d100b404079401c840b42c0110740c070f60b054691540500b5041c10a41e020b4100a551994090001016509a149a441c20b00d801103081011800d1200142e005081e000e005440e201424102043c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 295974559 1250 295973309 295973339
    0xb010f0510020c0f0406050607030e09070302160b0709030b3306160c0305120703111f020a11030d02040816031127040f0b0f010503060c09060c1005071701 68
    0x9482405240128144c41d96190701550041202502450b2680c3c000d04015001d500603800c2c641c0507052020004031020311902c2150041d55100303003a0388050103281c8411540c1d1900a00407030038040b18080c00710105240d10b0380300307100307020400008800400314034071590b00c56500e5180c2500c0380c0109652591a9482c042903458025002c11400f203e113910341400c000480081d8000390140c054001ca21300b03880d4041e030003420745a002e030302c400418191864840d582c4505104150300c56101c0b0309801203140c40c180d0010801c04000303142c006440071103000c8690660b8841800f04036115400101081414001e00580c0c3c444206543e04c2c1002c2460343c0c4500c1d1007c903c600f0094800c1e800c41c1d101c0301450080029004c0906040e54102d9054942447c0c06014000101800d448080260001680d21070321810040c0c107959014010300000d884003610502c894114921041e40035000703000380b050480040205100804600102145a080c21070000e024560105180c0415448200c010701c441c800c40b02a407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 295975809 1250 295974559 295974583
    0x20d0c0f0c0309090b0402120103050a0b09060f040303090501020909011401030f050c0409021e0f07060f0509120c0a02130203010915120f110904050109050d051201031e0507030b010f051002 83
    0x5c19a00500000180284904500103a503980d8240010052280005480d10340522881c48001140c50300055260b542d4822200901e280028900003030010303100b81c01091200f841880098101080d02d4009039042c10309803c460300120b0800c0201c00c6a6a040c000c401c03420303a40b980200700c24180910400c00b1485180140e0040300e8000035854440061480301c40201d104501c4002c0d103500a04120f01d4040c0c1c842c00c416101c070b501b1f09000d100f8081440c030915010713049000050080e410b004803070b1640764104000680f03884c0210922030000d030301e03420f0300208407a0715442e0041e660b604022a0400b241e40c000e03643d004e100e81c60b90042c0501b01c1c1d41c184019196401036000d000c5030000d1715066030601040303440c00f60005403600c244410003005400a40d02240b045e0306036280a03400e840b00715424002c0103054458126440c1c01000810143c045205462100c840c076140d501742280c03141c41c034220f4030364421680204014010031070560f40b400f045000d02012506600002c0004100950340d450020321 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 295977059 1250 295975809 295975811
    0xc080408070c0f0e06041a091302030f03040b0705010e01050402010503130804090c020d020601080309130f09021507140c150c0a0212010906050c0304080427020d0c0f0c030909 77
    0x901e00b80b05403030035400010502c41400448054541c20b2646940d101962240c1c01036040c50042c0100014080e603924562501400500b195542e10b2100240c041040710140d8050241d4105003080341c10500c010805010504141c55485d0311030301c1c001c2d017150030384c000c0484c15034500018480143c1e804000c0ba900600c4400149040b0510750405d250b2611440c0e02c049461450148003407480c0d0b07000300b40996500000c0c0c0030f03220030f40e0762880003544a208014420fa40702c44528008141025070ba44104411264010001104a0180d000c0707015030003011603000c02e0100200f02d9900300001c0603195072902608002815010600714041040540714540b41c1703d16140c08560358071780080030020f0308881c1e90010a003411700642c10404d98000c11450038240c8141d410100025040f040311403c40e40a1688040c0c014503061500703501c0e0854650007024034007071144080f1020000d00c1c06002400844198110000785044000c0c00904400404030181e403d00c411582c41c1404203810400020448043c464 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 295978309 1250 295977059 295977067
    0x150902010207030825030906110f1e010605030d0503061017191407030c030f0207050703030e0d0b151c1a06060c010911030d0c111314071d01030c080408 67
    0x541117000384d00c0003c880640b43c61842800d0141540034800c0c4045034290b442c1c82003503203540702c0900d8881548803800201c4d5031240042244440e030300d070112000507100c4c0000107001ca89960020741011002d030b041e44002107010090158500d02a50203184040083c100f980084161000844e1580c000030700709185c03109815440700056555800c00310f007140d000b08200344980b80080d8080d0082a945200000007450500502041c24136403003155a11500007004002c8070349155401c495065849511580000140c2011000507401e0710031240141680075180c000d0115860038030102507840c00c152940c40384004502c00c0400c69614a4032540708851603904c00581e0b9039004511544582d83c01000d103036103040c1082c0d041c403600d5160460320400071010395401d10842c0300100c448024420001d002c0c4003404600c0512444c08449540c40744443d003402007242c080114122545010490b04240401d40301c0d42c1541003c40160b01c54007030080300b400d0400000c1c0d54001d004200750b500910007440440002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 295979559 1250 295978309 295978327
    0x30501111318110706050a151208030c040806090705030d1d090901270203070f0e15010e0a120213020f0909060d06061214010504080a030b0409120c1509020102070308 73
    0x43c001508a810750640c0c55500c0101d0300e0b10900820f021030702c211aa92800101c4855078602014600c12a03080783c003102c08004990711401c071304e5030018221004154082000007900ca80500260740b2441d003000142c98600d16050505041c5003007250401c0800c07202c4140341031842c43d503442c444c407100d1064034056001c0c1d4032000c510b030050400007001e0030166203a401c60f51014803495454055244281c0c00c1d02d41c80761b65102607021881c154000c809042c2c1c0c01c1800140c0400441d24400b8070358805161500400103c2004144140c1181e00711000c46080040700c8010f6041420440c0010030a0743e10440c6810702c0350200400c01d0081c10b0f002e601c11200c400100c0c04c1c540d076480035041c109404c58400c00c03200c1e6a405541d80714000d4480112100401d6900e1205094011b2082910840d00034040300d20b481c600110071030042542c0c80790141d0240d6100d05410100c0e41982150030b008003191034040800806007465806136003070380250030701306040c0906640141d0380420b0100c01c60790703c2000140c8610140c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 295980809 1250 295979559 295979561
    0x6091205010605041503050f0c100516080706020406111612060603020616050708030a09060809151924050d031205070221030603070e090a0813030501111318 69
    0x2da210076401400c0c181740810f10345160821404891081c000c030f5280720501c1c103203580c9815000000e50360158079406003404040c054801400e80d480724514001e0a041c1c0b41c2d0303d003915904415070030359100317601060920240d60000903103555066074600070400d9007401d0002001c3d82ca010f0140da051011359002500c10040340303402180181d0313801017a29890310303031180080880e041020310596903803103204400202c04801200300c54200c0303143d03500c1c01402800c2900036101000041c0c80004d1034420091070001148003280141d00401001040c4039010b4800d00c801401e07501580072201c1c2400307500c0521007118503d40128421984162460002104c0b1030400b552182c0031603500c20030240c00c2400b001402369011030a414a1f030b00c4404400131100c411039080704180004c4428507015440084240310249400e00a80c1d400407229048a24046d416680c00f94150031503100a0955101c5135000d0081210a010b072240008104103a2810907a448074010344800c494418400068541d003107d010800032 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 295982059 1250 295980809 295980821
    0x314060108040b041b1809020f150322122f0a1b03050703080306030106091a04050a110c010b03070b070507170a170a030501050303090a03170c010c0207090608070609120501 76
    0xb01d2100c10940400c6c1007198090a100c031022072140c240c2451540881c07916140f050080c08001e4801e9086030346140f1a41441f4038501450b1b900c0c054aa20984006004080703046030058030383e43c800705014100b0410403841300500003000e400030203c0c4148070403d000010030010342600312501c0318403441e4850205d1541c10881d000641240225032000c002e12441000440c010b960540003040401d40d90030408080b200ca04044695103842c400316500ca071b1810780c00c05504900c0e92600042c0242c205080810142d11600b941091a5100c1c0707010401450240000c00087c004c62092a14010791665a59202c080902070000c90b895040a1000220381c00c000c00060580c3c06414030b00580500c500ca4400c1c1c0d00312102240c0041d06000011400c0d050200540704c2c0d00c480502035945541c1141e5901c030320320508a02400f1390180038456547c19000034010204c0100150b0090100c540c2002d54280690340690014100365020720000c10440341d000c0e0484080710901c111310f14800340039180090140030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 295983309 1250 295982059 295982069
    0x120a081e090a1505130609020a09061d0108011b080709090603030e0f0a06020d140c0703030e030609011803080a0f2a020f03030103110d0b070314060108040b041b 71
    0x480304108000104002400c400060040d00c4440104000403501e805650003100d418200ea103218440600159647d0056000c1510061500500c2c1c1c0d2110124400c6075000d5000d011b900701c45010540d85074240400e1140503100b444024444150621444a41500030406c2401045803280019450b140704200c0711000e082903401c01d000c09552070400070232040e0b032040d4251080c071040f0740a019514150b07140310100c800c1c035000351202c20484c40c02600d10350015842c00c11200030400c068298031205109440241d8032036124403442031440e0050519112000f80b1760302d0340d83c1c5080d04218491409000381c250031685482c0921941da01c211040b4050034024541c0000d050500d800d100355000028082801001c1d03201d40d480d021140500100d96038000e00c818510903810810051021030507501103400c0310a0003900c118044030711a550340540000480304880002da42c0c40b504028003400c411000e07041042403815001a00389a184d03180700d00c5010304000d0025202c4403601084540302c110140c0184 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 295984559 1250 295983309 295983361
    0x2240c0a030e011b02150a020304050402070c060e2d0d05150601180b0316030b0604090212061012051503010e0c09090f06070f050f042303120a08 64
    0x1540c41c03801501212056040320701203009112503000340700f12840f050b8402ca400400540348140d070f2460700d22141e0f202804480840c04108400b01b0261141c0c002080301c981310300080340e030551130218002c0c12405c100422a200701078010040f103240c40118060145204079020240c03110340c410300001c00086007210010505d00908442c400c3d1900d9558074281304d05402e0320790149900000c034000701c016190f8001c0d01c0c034404c1305002141501036010106445200b581c00c0028101d011031000034580c2d0029031000800790f0300040c0020101003103042440e009101035411500c00703010102c2c040c0001020800342440c0710340d0758001403000070580c0c0074104271200207802004580034102000d40c59900710f20265025400a50114907003020028250450001b03610150015803982c1c030b030403180c1c0c600850713080702003000520640ca000b1080500400081061a200141d10011110602030b000e441000c09442a003112802404030201e101c2210303090f1100d490b151182c3e9503031015070080c01280180383e000d05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 295985809 1250 295984559 295984573
    0x3100302130903030c080c0711130e0706030b0103140402130f02040906060806030705030705010c05030c01060b0301091d12071704060302120919030c140f010219020a02240c 76
    0x90035099100070340a030f00980e018005410340540c1960010001d030350001c58400c00704001c00118900c4140300e144080c00400105091450b9501081564071b00820401710f40c1090708108030240d010300c50320f01c00a1081c03e0034030000707402602c160315035900240044d00480802c488200111386a90000c0100001300d40c00715100d82d02c0e0405240140403a000e190003081711000032404525000620300c0490364003c004110003400d1400458000615080032242448103112807480c2d500c0078000c980151000c1420113460358905143c241c1a40c03070079484541038001183c290401e20b100481c400d40d10396040528560745100d5841d010410120040e10031000360004500403d4490b0715800612810913500c0600750300780c6442400b41d84644d0034000b40e1004141401c2d8010020707024568070f190090003508114100a80c000415041454411202603140d40c005140b888008841c46d205205030842d01c0100001c2c0603560104812012505100389056041002c1c140d1210541c022140c1e80501c1e0000d503010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 295987059 1250 295985809 295985839
    0x80316030b03121306080c0304080a051306170105010c03080f0709050a0306050612030f070201080a02250b0c04080a0f050a0c060c0b060f100c03090503030a020a050c0a0605040b03100302 82
    0x403a08802d01d51003800104d404005040c1d441000e0250141c070503100c0c414a180c031907941e070310001e60000c60039000740070040c4111142840b0440c9840005d0080303440f1145d01c1c040500d5005014a0b058011070306100401c142d081c0460751104440d54030444d614a4486652a1107209031010800c9610040c0d0244010030080200b04164210b140a100c007501d000300c5102540c4083c1e5140d024503401150140414007201c0c2c055032245188542180603014014900f031640b40c030080d082112a0030b000201d440c4012a1000c1004040340c079a484a402c0c82840e00702801c20304d1040c0c80d070140240c049c0076142002c0d44041030020501c501141c0b154803445411b182c9070f940c0d20107040c0c1d1408500987e6541c0f0488005070342424240369070812400000c1c50300821150780c00068602c03090380203003602003081c051350108194804000510b6542c030143c0081c60048954a02240780124a001c5507010b010604010044250054140d80a03190240002d075101c0c0e840d80e00740142105254006588610606d5541326 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 295988309 1250 295987059 295987093
    0x30a0f02070b0c0c040e03040305100906060302040507050a2d0c140106081c080f1906170313050409021c080c0303010b07061821050705030a020105100e04080316030b03 74
    0x2c10013015901805000080740c6001c0c0c881c0140c1c4005801a00002040c1c2c5607800507034041e1000c58410360000800644a070080750440300e040300c0321404213100260030400d81d500800540394000c101507452448220350207005580c68041d0780800144000d40020f802044418090840c01c45e07101802084420394581c0344c0d56650b00d21011030a02d640600358038101c0e140c81010103910902e41d00f52625103580742d1001901c90380c40b200c60040340c840d070f03540000f0860b1402080c00035260700183e002181c44411003001d007a0501e005a00c0503104038608114000103846041c80343c10f0310510031f01001c070407a03914200710119101d401514061400004000b080c01c0f002440a03040140c01010100710460b1041450514141e003182c01424144d905490030044140394550900034164915105043c04041d5a030245035401150271080580d4560041008074040011a4802003c0c400d00a642c2c908094031551020304c00600544d0300c0722001a04006100d00a0700050707500760b005400c0ba4048240101103071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 295989559 1250 295988309 295988323
    0xc05070609030801030b0703060605090d03022401170a0210050c160b1b010b01020a0813090203400206090f0d1505070e1503221202150702030a0f02070b0c 68
    0xc40058404000c40c1f080b40c424400d21060360040d4603080c0c41c1c0b410b0324082050101d52110100d003144030b80c80c0c8207051540400c0300d0072400043c00e0b0101c14a54144918070741b4400c03000003000e00c1c80c0c0c0000030180150703032a012080c10300340c000e06100755104144c0c82d4450138200d002258000840d80e20300d0000d40e000c05440186619405450304c610b5035241c40400500362040c240460380143d008400e43c002003030549008200782d0700590b40c00072016981d0038008041e60401c40d0508842c011800308901c00c0742c161164268817450a048004604448a0b0060740e421142807010f0f01601c0301045000050f2910013036564103110040000061010524211814071180c980440ca04e0741401c0c0071491850040c0042c1c0350490b0014020126030307800c420720031055007006250b10320240301c0c80011510b0035039803111101450300903070340d10b840345c042c1d2a0042e11708001016208525250501000801a030200540718841c40901e0300c00d5422542c8081245848800c0e0410900385000040762800e400c0c00007101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 295990809 1250 295989559 295989563
    0x2412040302010b04060305060f1008011514010305070906180b0309010911030d0e04050907050d1406060f0109030602030901241703120705160501140103050c0906060d0c0507060903080103 82
    0x9003c003555100070311054a88521000f0613552080020855204040c21a04ea0000134440380c181d045644a41c00380c02c1d64080917070070645a00040381481400d60800c680c0510540c20708080c0118104480d00400d54412803190004004880140aa01d400703041100401000c040310420380324200700b40d8450007002c481380215000030411880c0007180c2000b00740c0155402709a111006c201c0d01038003c1c07101501c0d00030640d040d14080c0c3d00020400b9a14640b0300700082d4000c40400e045841182c89180c9040300c0038100d5441108030600803155aa84030055400740d80d40108056129207480c0222400b600c04030401c10410300f5454400300b1100302c80d41045045901070507102c0410031307505804a4582c40382c1c54090800001035000038002e1801140200015803050b40c0d0300b000b51100c0e4803014210340001090817040c89640740108140403080001c2484c650f41202c884040382040c01c001040e91044a101150450302c80d10b517200c00600444c195070226410000030300c9091080e180c010b04c100000d001c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 295992059 1250 295990809 295990811
    0x111c030e0a110609030a0204110306011d13091b03081e0301050f0409050a080c030a0e03011e0e0109020909060f1e06011805060c0106090e0c0906241204030201 70
    0x108501024000420815540d00070900c950100c40e10b00c10712215a200d004860342500c00c202401005841c0d51241032184950500080d03202d09040300010720359010080004040040d24540780f9856030340c560b0101c810162150000b070320b49050319248805c103042c2c0034640e01c1e80100c1900001800503040080c40004c6012440d000800031501101c20540002c0c083c054018138403c03000b0280e414581d02c15034645006400311001c6a03802c0d6110300d40380c0d00451403200c0f1500040b68241c80190065018003482c6c030121700030300030312660010051800b0050622010441c0d190782150a910070203501032494550041c6c6100d84600e0a15044d81d52282d060b246040380d0343c02500080d4441c0d10352940e40c0c0d4030407111403028200351111030044a02e080181180102c024a000c800511552140000e0482c1120303400042581c034034100764803040718160100e440c4590001e0701204450b6441c00d405551010048034528001103030f500c0ca150500418442e0740b80c0481002030348612144d90388200c0b6110390b02c6580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 295993309 1250 295992059 295992071
    0x9050301110703080a02160f0303270f230d02012f27040c030c0306140a0e0a0608030a0519090b0301030b130b13050c0a0f0b0703111c03 60
    0x1451a81d44038094014000400d14004502201c60035002001298190204222800c5840d107805500c0400c0f1541200400d994602034202d0030303000740544405c4001c864100d0340310032403611092414008884018a405278414824074072110f01c50958146c119800125080c41140d07060187c004d01401c00d043c4046011503a1014a07401c03829408450440340703050030f6040444003447c0a60072066152801c1c070202c2012418402921039108400d5500404d50340890b04c00815034024044903210303041003a04c1d03040c0004403500d5450710b4145070b040b0750740c1500d062079555076200c00c40c000340410f4109684902001403514500760340100649070402c03201d00c0a4000000d6424181c8068045100c0c0f021040300a100400c00704403111803030f81c0d01c460b041801e410ba4600c80da03203013501e085c01215951890800804030360700f80541004048420324003a1091a122070920850301e1608280f0301c11040851800201c0004042c0309129030500d425001c0129111140c92801c0080c214030107590b000e00103403400c8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 295994559 1250 295993309 295993331
    0xb0d050c0307020d1103040503060a050103021c170a09080712050601060513030807030c0b04140d0302090a0e060d121e0c030f030f020f0309030a0e240a0309080a09050301 75
    0xc04890003000309030001c10305560800d409907400c942821075004c180c00140000a0300f45c038240b00b05132107a0210303c4000f80540c114810410b160071800701146040c801d0240b03000004203109600a400108100c40e55203070108442d007100c03990b0154200700e94038000c03007000080f41d003240d103151004140b20300c086c1c40d2945c0e26004c3c119071030b00030088980d8480780b4500c0c003003001c60b41c8240146204c50180c90004a495a55210f40c00006002d0700e04079207076810040c0c040700c0e10000340500700c6134080c01c2c0340652a1801e030714001150505503015544d8440100d60108489030f40c0c50502120150f0b2101200500c0310f014500581795140120019114034401704039a02c64500c90b2001d2048070368180c44003221511040800c0b801080b04540303030303414076608201103c02c100d00c400c0a503100d105a20002c41c0d072180420002044d404503240000d010310001c2a84140c0301d840300c0c2400580a150103141c17600d807406c4d5081103018011044001d02101000510409000d500c641c0080940740b05070000e0042039401 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 295995809 1250 295994559 295994581
    0x100f020310060f020a260304030f090906030b0103021e030a0308040b1605030412050405030f0304210209070807052808010609180b0a0317040e090607050f070213060b0d05 75
    0xa001c400010b8005040507070000f20103480b060b595421040703500310035404181b0750910a42c0255800c7e00802d401e05004440268040e440d80c0162141000600045145a8803042c5100c01808000d1003000024040103602e1828001400c60035001000c40d04290310600307001c3c20085041d0340a40b03c8040282c00034011044078840e104144d6455920103141d81c0e5203407280315040d07014581c41e800b000810480050300ba581001100500807005014581c0d07607140444080000509490025108900540302c10142c0d03940b03250719071300550301d0420250903510044120380521401c00380e083c950412442503107000206414110b03841c901a141c40c44641d0302d038502680e04040500c03d0003242a10b40d40c43d9504a02e1541041180c0c3c4030150241d24142c2d229500c4017808040d4005e014049000410100f11009400c00302a421800c114050540344c00c0110000346030b842055401048014006414411901d4800310807122805850040121946074008600654845c0c20344011082c20b14002c40c251480b0307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 295997059 1250 295995809 295995827
    0x1a1f0f051e07080d1503030f050313080309010e100605010905010c0302030904060b040501080901050408030a1e09030215070507020d2d080306030c0105040e0f060a09060b070309060305040201120e100f02031006 92
    0x340c2c680d032948c0c10152408031219030000706060010189280d8010000303002c00c1c09540900030034400440e210921455580c5003200080c00241c1c0c1d5801c0081c1000b2990300418142c1c01d0300c0007803a100d0814503403800c0907880c510a640e466074005181c82c000054952440010340165403013644d0b0103000751200c90b0114281c500588014052000c1080402c91140c00c640c0041031102c1110801c60038039181d0ba5610080355004082900540c0040e0444075081180c0e040e0140d00945900740113003016a0b0b42c02240055144420061001e80ea284008a1000c020a08052074205180b00c00d500183c0c2440e00301c003560030130b64519019214450610106c0e42c00b980690b41a2107001c20568815500c0c035400c0662030b2030203808990443c2c07240b10046007020140c000d1001410449211a6a1b01d05501d002061210a9808882010305e070006000050303902c101c545480c04051800810505100c1c58103a050204019030403071031500c0c0400310401c10700140c000d0361084001980c01440c00c0d41c1d50310182d41d00c140e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 295998309 1250 295997059 295997063
    0x170c0f03031804020a03090803090105010f05060310090b0a030f11010e0402122a191e050a140415121a01050403061a041a1f0f051e07080d1503 63
    0x203200c02240b0007810182d02078404500d8038030340814005900d0b1070303c540f01d41c825500520f20365160001070003034918205401004104c01d588035403451170201c500d0340146045000d028101900c076aa2000345980382032801c0c01454112081784d008400902c3e0210b196195a40f40d0ba010443c05c68003051546800e1082d03500041c0744401e0302d4035a46c1c807007999218403099040031640c15050000c540304900b4090010b04204100d024601140b00302c40341001d07018007100300410040310f0b0007007013000e4143d6110056030b120f0307451414200098000c111241c0b0360340c02190012807a2001b03041c2c8001d150b50303102261803400d41e803a82041100180400d40b407031b150b03d828000c517800700c1e40c00c0104200040c0c40740c1c07103d07038209420b403070004c60302604100050580c0d8089908070b4103450708030903c01c030510b4811a4114840070300c1c9100041210b034500007400034801d0310ba410040c081c01241d407908039110790040b02c03020001c42d0300041e598501c5281c0301c0401d8100110404a0b18640060032032900b44044800c0c080e0f135 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 295999559 1250 295998309 295998337
    0xb280c030c0515090313090506100f0915030b04060803040f03030c031101050720060f0c16150c02150405070e0405010e0f1b03070311100207170c0f0303 67
    0x6840d1010350708404440c004841070b1059104101220440704000d81c016005040a556261001c80b400b0b4030304151030300080919460300b42030003010754801180b5054000181440103100920301c0d02551311040c42d5201440e60421101c0d00300345940c4c194040045a24111001c2107003d8231682426038038051070081c80b014803c20f81d03044c00880d0140907025100c0e446803510341c9039030492542160035564281c940c20085211050b90003c00c0380300d0500074160008600c000c003403e1400080c113060101010340105400c210000721600d03501c1c000d03556210081e81004140100c0c4040c080d020000341542200da10060160344580c018644804144034000c50308007000b0322400c1c0c00c15451210356840a041129650743c1c503961f0000a807418801c04811190410190415000e4610100c0f41c1843d8254001c0c03180c0c001140500c0012110540c10030032020907a91240c40640030302e400c6c0e140ca40319420110a8007075070a000b09601200007203105040390223540f01d284543ea80004c0c19900d014100d81c0c04205 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 296000809 1250 295999559 295999577
    0x11040503030a050c1609050a060b28050702030a0507050a0b0a0f0302030612010e0c09060d050613140a0f030201200307030902030102040918110114070318030c0b28 72
    0x18800c0018128a0f00900151070400c0820156150364220076031012021b55116420851085054480e040043c0300110040d0703e000707461000c00c2e2010010301020150080d03410010306186102d001602c08441e8040d04079040740215007400c5540b1515845182d11805082030701007241d0320580d054503801d04490315460300d8004807400c03e074045d40004200642154020140c02d04000c801d0188241003003022018000868080b028880000c0c0300800d0b0345e0050720301230350800000e10005425584510401013081f1208036501d454030b0120390510002980780300320f9890b0746c140400c103c000b81082d48260020070003001d00c03141001c08a6414100070241c1705080c00014410390181d00a0088180f0013000141341540b113426501c221b4000320b401075014802c4030324035420400100c17483c407034040302401d20403582d0a51740aa18a503100c2c0102c014108908503070039803003c05584c00800042e40e8065a2110803d844451988581d048001d01306440340501d600d41442003882c1001d8201c62000b503581c0006 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 296002059 1250 296000809 296000827
    0x60c080d0506061c24080a0204021602030105091014040c12030215070e010e04020315150408010204141e10050f090904030f090e0708180c030a0c0602011104050303 72
    0x7403000a009603044001040301e10f4075000d0b803503402c2484800724040003072800c00280810844403540d0303421041c08440b00505020502000482580456040f0760150b552075421044100d440d8254500039059800d1506001604d240480e040d03500c0e00c507180080014120485008101000c16907000d49603030841402070000d01848018541c03014081d0040311400801ea2945441c040411111800000c000b500e01c5080c1d50b07841000303d06030710002c640560850500035000d545501d4903004041c4150ba052218026030032400040e64010006030008644031950b60311581c20650310180301e54480c21070000681250200c180d90320094880c0a4090003050040000c103446030b501c2107504140d111420b108005680c0d035401d00091182d442031703a459600940c240c0c00a40310711420b410074401484010700b004003469002c1c0306d080e031000c4040021079071049110f105905282c0300c04201c6030140030300800c1c42d0500a99042903000c41d0b5090303000304503080340d4004013407450050f8014035525030020841d88003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 296003309 1250 296002059 296002061
    0xb06090105030a0e2a0d050607030905070e0c03010315050f06040c020304030c1d010b1608070f0f0b061309200f10020d1b051005091002130e01060c080d 67
    0x90300c103110003c0019660307900c0c3c1c030803458003001e0b009524001c0b00d43da44014691003003000c44038694800b40c40403003060116548040d00c1781c030003d1040f010595600842e00034020104480c00051400711460b4480d41006010741c92260b0003408140d0b62180c031146110031141e405c0c8038040c0700d010034100d0005d0a440b24000c1101030010804035030f00f14841880040080b40101041b00c0c02042c101c00840268840b800c08441c03000c2c8168421625910107020f4200034171144283c2c403209641c0400703070310340e40c001c14907100d89a038141d0070014100c039000700300040800441088403401380008a80082d060700446040d18243c42070514018a0200e03007510821206404000783c184c4034100403c0d000310000784102262545800304104c1005a100300c45400d4031680020302c3d00c4520000c08080c0c98150315545171641d80300000800d0b030010650f2500062243d44041c400a1082c02295800b95901c00c0c0c80201d440c4240054004d001e4820504030000817018015401c454850b81d03c80741c3c03182000c1c00b4100d054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 296004559 1250 296003309 296003311
    0xc0409020a0f060503040203060a02041203050901140c060402120d020c0d0f020409080304030809010605010c080721020304080705030d0e091305010c0c1b03081b010209040606050703120b0609010503 87
    0x26000a1004004180c0c0000103101c80060f0280e40d5843d520fa190500400d868890060102400c440c41003005000b40440c21b43c0d030000c440c3d010300340940c0c1ca02040c40100e60806034006000d811000204910075200004150140a540202c42c110a0240c07450f0109440340380c0440218096806012280d05900f0243e0b50001854000c08002c95101c1c041e40115003922902c401c01c41d207040000041108160f040011103410034100c0c80200403281c14100007038a41c0c0407000001c6c14490000c2402010000900b2480004008400c402c10040d0307416071004e0b40c1e039001400360002d14058402c0200300360030300044018005e40c4d613988100303840d845842400135082c0050000181403803200e8a001c0411030901401030340080036075070b250524006062442c01d070801000c2e1030ba5034640310841040414000e0060b10a1200c07800002c082452010182034028803403054000d800030304100000404540003400f42030054001d031283e504005400005400b291000030980340d029405000032601035100d03038091 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 296005809 1250 296004559 296004563
    0x1090e06041a030313061b0201050307050304060e0106080c041a1c0c0b121006111c091e060207060203030c1602010912050c0301230a0c1709010c0e0d02030c0409 71
    0xb9450056001d0003007415a4402202950310003621042003000340d920035000e2900608000700890320040c2580001c10790f00c0050881c40c1040404804201031040a81c420010120040c0080041b5aa40c80003a61a0071120307d03810700c910b1400c0591200540c1e004031908501500504250003014141080d220002c04400140d90500710220040f480450106c01030141e89841014400a450714000d0b072094a40030790064000c000700055610400c140009421448850b001da03640e43d0389090880486502640354131a40d80110007180c9000500c1032050140192001a825105070303503281d4030f0581e0b80c1c0c801903403042200c030000c006844400521600024404e88145001d42100303980e089640055111450305440580200400c101603190911aa00003540c01c43d041c00500084860703510355200004085124080c5c03240105140c0502c2920310043c20340d80e040c549440760070905076a82c0284295841c04000c5040642040c03c00d01c0c0a00041d06040d500030300408070b0721004000d01001d00149841 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 296007059 1250 296005809 296005841
    0xf0312040807050a140309040f0c0804020f031603031707021c050d0609320c07060b040e150108011413140c1c0302060105060c060417070b0a05060f01090e0604 70
    0x4500001e4120a82c5e41550811180110741300c031403900810045444090701c59a41a10300101d9040c92508035000c6680039804841d05041880810f022a0510311801c090742410400c00c2c0d004400c1541100244202c90300d030305241051a600c41d00143d0381e0300003160304510500b5041d11195419403082c030090442c0c0c1c0b0302103070100b00d0a13500d9910f00282c07048402007950803880075140b440000040d41401141c100604c650520034108610801c005d8800d48801030019912001c551110780c40e1034007c0c030348015190085650012416a018000700310a0150720714035402c058100d074402c1a0705094071300407008400048903480055423000e0710300349100d6114949011f0106c03101a19034840b840a604c1c0703c0d091000b40e999070711a18000b400c125050308120300c1010b0070302441401c0e20740001c4241d2f006921140c1050000140180a071450144500051101402008000304115241c010314010f100654100d407071062844019038000f07030680555120000c103035002804510385a04402c0c1070001c82d0130307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 296008309 1250 296007059 296007073
    0x100609111605070f0e0403031b140d1407260106050f0309011806020406170907062a0602091e010c120507140610060908031603110609010506030f031204080705 70
    0x800380180304405e40c00308076840282c404000c107260305030044005403071240f500c0049240001c41c02410592101e41503600092010810181241c05a4483c0d140e00c0303904401ca03013032483c2540c001410607a20134034110020702c0800d00c00c21f203418401142c40c16a0701545032281070803003000f440d48241d04005c140c854250340f07980040c903203503901409800c1414041c01016950394280600a86500c003581400c840005407401013002c2604040390a4059034100d1a0841c15540c91400d02400303030040090801c06400f40c195810200b2583d50300801050209580c4520510310f65449148458409150b00c0d000c02c85007000d0100242d030703000d402c03a00e485031400e0450402013240c40380361083d0444103240029902210034010040251030040c0c1c024413240c5441c001c45070519100301d440b4010311682c03481040f000707516241014080c1035180c99038a480703c126400d9140858845002e448140c0c5c445000703001e2902ea1340c00d18a8040112050000c1c0c00411280301d03241c80d0303100601c1e94080c0e1001e50700ca004141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 296009559 1250 296008309 296008319
    0x20d0207050f0c030a112103130f06030b01080a05060406081204050906060c03041401020304051c030306050603161d040203040f050d0201290d0203070810060911160507 74
    0x210240c420180100014540030845001003403802c803808614512960100008100052603808401091441681c003c0c007094040761800031024140300c101541800086900400d40c28000105400c5030b012444a00141d07680c2c0d5420b500f22201c5000f5240040e0260f40011080003158119a030022005440050403aa44001e800c0c1005000030348400d0b800e0f40000c007044107290040f2400d4000d80c048501c0e51420948a540598a00c128426001c01280c3c0f641741d00004d80c0240180c400604018000071002599400c043c01c080c08101c0c1c0440100c0d180400211365410b000c4181d0b4820440d0b813120b641c04000400094560840518006010700d80c01e04002c40d41e502d850003d14001c03403041403203d09000e1146803090802d1444c5040300d085a00d40200219282c0b4041016140360101810f0320b40080707000710100f503408560f102c02941500c6800c400282025000403076461100c070352031003000883d446061080541d4890894800380b040f040c40000141c1c143c40e019404414410000c98110a94030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 296010809 1250 296009559 296009561
    0x603060b0f070f150b04050a060803070201180b03040308090f010603080d0e19051e150105040506060c0105010b041a090604030b060105040e0c0a0f0509010801030308060310020d020702041d030702040b04020d 91
    0x445101c4c1e0320b612510009410700f0140030740d9800c0785d40d04070240880d6040015040d40d900038584045e0410100161f145490881d03800c1c0c610142c0741c8240e0440d80e91030542000313482c0103402c0c2c581040300e115803403c1340c06020040c440d040950790300c01c07a02850011110003020103041c4550325080d140c002c9064007180c5803055004109a03038442c10140c1107082542448541d030f8551210603941903045040d009100c950540031090559a08840c00202502d031701d004104140125180c1012561800001081c1040c440002d0801c50b4180040c108846494103102000350050100c041e4110001340700034030001d246918000c1d4441410f08d8040d0a00da590111880301e0300041d200900c0250340001c00d80703070b0240d000391a80407449103400c00514002c10702c00001d0000304144009010081c102c0e000c5680d82d0380a110501041c072401c80e0640d250104034250400a41c0313341c1e01248120715094040c082070b40d50074032203c1800b0341c0401039410445d8940900024181105100394040d608100c1c01c032140e025 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 296012059 1250 296010809 296010833
    0xc0a06050f09091e0622050c04030f0b060901080d02060103060e16030311010c0306030510050402031227010f021e120c0a030306090204050a0506090402040306140708010603060b0f070f 81
    0x36080c0e5004e14943c808840100c0350b0241c40d2600400d06c0740096410340300300c60703030400344d408a18000003541c1e0f8800c40710b80c50380d0145400051005244803801403c3c8030350310465900401c0101d94010050342da682d121581c503c0102c0d10321000d82c12001c01040481c459600c645402205002a01c2100d0500d00f014400d5081039002140400c100303400c1154981d009125078480c41016007030070072940742140c41c0e580e41d511103881840461615400000d08545050001c0040e900342241115143c003900d0040d032410301758429024650224181004ca025881500f80102c0741540d81c002d0b01c41d65010301084111194480043c890701e10440e400c0f00c8a00c0d04aa0040502804240113094a0a10b51800034107032072142e80403182d0140140002e000640c0c17440c04d00700c01c03108102c1c0d0499640316072801080190003540d01c0035005600e0265041234808400902c507225400d207581d03101d210780e02d5031419000c0b2030803401031040e4008148001780c0d042e207406004082c1e5030301071407500761030a5490b40d480c1d8010507 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 296013309 1250 296012059 296012071
    0x2a0303070b10060e0117130204021603021011041205070506030f06091303020309190806090a0b130f02130e060a020d06090b030d08060625020a05030c0a06050f0909 72
    0x15a9a00b00881103180c1d01140340640360740e281c80b168418460380000e2406003400300184800d00070f14086900700080c4141d01251560280065403940c101e800c102240680c2d525043d409401001d414086034080ca20400e1440c40ca1110701034205424011180c003c0910481e08403140d00c11558040744540d2800c01861140b03000380b54182003071500c80280212240081c0c20000407000d1400b240300041e0300401660402d030403d9400090150090f5210720304111a40e0015644d40104001e200d130301c40000c00c1c070b00e400601482c078800c01902c4081c20304044488600d4050440640c5003000070051800030390080f5902c140032400b155130320714505038074144142502d900a0301d0b9400600c1c000d003001d680c0120701c0100b20040080181e0f02c210404252035181daa0010030400c00e030040002c0c0c00e0380d80c4800f540c508221803000041c0c0102003003001810604a0001a840740d60304510000d003e18002902c0c0b040024054480400c9928021095400e0341203030a0003c0b6411041c421000182c480c10600b40c8108 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 296014559 1250 296013309 296013323
    0x200307020a08160c05120703080a020304030c090501060e0a0f030b0a110c060114060406051b0102040b030420090603150a060510170a0216030c06060f17070b09032a030307 75
    0x3501138a000764030034550398807550080900d403100c40c007010804a0701c070040340e800c903a416540300c00070365040b4150b11031500010240844960b0202d110941503000c141600d580d51038070340c0c850a03503000b0081b901d10148100a0703e00c0c103214040c00025140c14106421800c4140003003403000403143c1d070890a4201e01e401a20a50100e40100510420240001c0d1456415240b01d4502410302c40010001c2c0318410300c619800c503081c504091840025411100100180c1080b1622030070207113441e030100d4048103805c0c2a201c51403130009600e0315159a00c4ac0c00b4000c000c0041c03000d80450300da0641034a070010304001c1440d07540c0800141c1500d0700350781048603001c544d036000c0070441d424281d03040d031103805044c0d220800e105204080c40300d00e108440010198150609280040d4a458800064006070f00070002c007200010000411405c5000100702c0059140203a481c1c2da5150201594a405a01340c100c1e81075105180301c544401840c034051345608080700000f0030003002000420701c1c0d5440948212489 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 296015809 1250 296014559 296014597
    0x1104110d1a04050919080906030405070810140a0b041103090d031407020703080706091b060e01080910021b010e0303040506010e090606040c02010b1e0f0301200307020a08 75
    0x14980e5851103000380c0c4100d80401c10b5092800311140d9421408160581c4081724004281c240560354064030040c120042c0941c1c2d80b4076080c40c055071640f2551160680903c0350200a10011000340103001010000284072183c0e5911030100b1030190451006007038120741d031a1000700030554080c004511820f01c1b40700611907062041c00007400c45801021078140700211005000c0496800701d8880201c907009203c594540145090200042002e460b000b000310b2030540050100240d4850090215680e0340c843c1074020000d0001500d91b02000c58015816411807168111142000d03170140102d05c8040002040070144510034608494031300145800d04d51020040204103c0208001c030302420307030132420384120b060210a03c1c1d5104006003407103106541f40c0041c0e05040c1e01c00d510403040141c0041805458486081c0300045079020200881c0c010300903c1d407a03040380d0405000f007903c0304c0c00e80340e04500f82c070030030b1fa1214100b0b40000d400701003140980f14280b0003041d141d2000c0c244a039900312561000d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 296017059 1250 296015809 296015831
    0xd090b060a1706010b0c0f0304032006030403020705150409020c0c1c05030306060a030207020d0b01060f0905030303060f12030f09090106030c08130c081005090c0f0d1104110d 77
    0x1190801e0303120b10003814000d00b01c5580340801144582c1150b540c840c810b0340724440701030403d00b0a1844114091284400b1800200b80400d81c646440414001d581100041410030240601440203c0d0041d0150707210980410144c1461244105030201c9802502d0500d500c9103102c0701aa802401065500c0d401546c2c40006032500c90501058031200d060480071400d2a070b40c7e0039480380801041140f0441022811041e502d0080c0c04032182e40382c1c0108103070b003464103e01c1c00d854003005c28007655001030030070011014140d018694441c20707110000c0065066549000410003c1030000c8101d0f60400760705411148892010005048000c14021005484409039001e1150300c60341603001c00101410803461651f41a001041581c016207407003100044483d45050040c91510150700810f10761148003003480070390360340b035000601950004003601d03821882d040c100480c418034128400d6000b10415240c100141120400c10f1240c80701400218122f00c0d450074840e10364000c105000d6150f6161710103020303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 296018309 1250 296017059 296017069
    0x31314010f0e011206030501141018020304110a0603020c011401120209100305060708090111130e06030c100e0f1927090807110919090201020a060f0e1203040f080a050d090b06 77
    0x580001c400c0312b9124228500b4000d5a000c4800c4000130171500d034008045020301c280f20394071742c0014401602c0c19460070f5031104000c0007544070155680a5510f0000c0404200364041d420504032002801e07030803200d81c4650200701d082c0401030107000c48026074107000000100140b05903071052103e51290116450b08020381800d45030701d6a0041c050680c1002100007000f81403480005980c1c44004401032a0760f41d01c0801c0c03501070170303d6a0551140120207071034000d603405590000c1c1c501040e100780001d038039a0401e21074003002c00c565071001001610018428400803607100303135801d0b1650b0242c0390b080b0a03c1042c541291a01c07001170714820000610202030181a81e22403030171480648140c400b40c6401210310003a42100c8110350091500c030351050055a20800c40e62118030303007002c0b007040b41c00b0b50302c010303d401007500c2d000302da031f050181120f008602003490050382e10851308070b582e8858160683e6540e4070782b54801482281408400d000f0030f400c0301b84d248604001d5512030f040c0c1804608140c4200b00d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 296019559 1250 296018309 296018311
    0x130209120a170f04171906050105040612020a0302010c050a0c0803040317030906150102070e0f041e0b0c070f240b040603030519020c0909031314010f0e01120603050114 74
    0x2c81c840c142004914494441d15007202e084505003e1207030700c52540850700904000d240321040040710440c007540010300003254800d504070380c0111781c10084070f5501d03881000b00f8200500c01940c089050789041000d54001c00e8403550051040c425280340640ca13507991207289103590020304055001140900c00c2152a08950a1100550310028218607003403008503545d020040040c4034910100030035030a071b80d008000100140203000b0030f11041c0d1414101d640e100400488003503440d84a030f0075800e101440399160015001d0b0b0001c03203007103840d620ba0125a40543c8800402c941c03c080d1403101c400424000d0129100c00f98900108080304031840290005882803407041c3e80c4540d152035003c10000c1e03000021140c46460280e00b401102071044400c7c0d0030a076810381c0b03054000c06c54008203c5c1011020009100c40320041501144550311b8902c4602e46900010700e560103c0c6101244485a500540c0306034101d007014540514040c62019001c0191091980308076416915460814000c203014101c40d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 296020809 1250 296019559 296019593
    0x1109030304080f1005040b041403210610030903081f0306020c03030711010c050405040f02040f12120c020112021303141023040b0a0b0312030115030506060405130209120a 75
    0xe12950900c7d458041561001420061501c0241191030803050000e00c1a40c014540d803080c48010f40080103400c90117030304101d0b4540d2148401b0301d50741804900078440c03890f0b030a425039514642030340c50031007a08411b001112800d900b603070b042d08000005203035070009202c40031051014580300e003840304010f002c4081400b912031003a4100145c142c1d516a0020640707085550445001c200e4500440e101002440b0b030b50850310801d112900d001c203d03014060100540c0034850341c0c90b011000144030040360304213020302c802030015007500c41250300c0703551700c2d0007400ac0400129a06413100da641d81e102d072481d001030740170405d064006030750b030003000d103100d105494076a03805030200c0b02441c0c200310006e0748120300200300038403069038030f00444c40b0545136a1202d001040007504031003841019500101c0c03280c00c2442522400210901030050860ac40e0080c1802801d0203003110742001e06001c100442c3c1e601118150600d0b5030700748207404403540c0352011902c0c001801302c003038107001055080600f0240b45041c0c40c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 296022059 1250 296020809 296020811
    0x921041a0a18061b0807051e101134060e0d0915030203090f2407110c0f0609040603080901090501021b010f0909051f14090a1109030304080f10 63
    0x400107a9003165081c1c03005818500101880d444600c0e00c917026000d0880c01070418850005450f9100380c0000d140c86841007481c0455200c000c00c1e040342d105aa1100100c400019001e1000e4200380100c9507603400400f81064200303007980042c5502c14242c5002030340c103841840d21902000001c00081c4202c402e1081e00346003614001e41485c40b255000022a5640410907034000000b480054007800802e1841c3d69010030349200c0400c01800c00c080c01d0b1201c0b1200e200311140c4004c102450b00402c082e12202145102502c20840194200b2155501c00341510703030428030801842501e43e03954412540038502c40c58515844808203000103140340070383d801c07103415540034180c024115520858170000140c0240b80440d0120440340048443e030040c0e60203020440d0030082408012038143d0090000e100f400d80c0a801107a41e1021005500021540e200ba04000c0c010041a404540c07500a0140d810703140c18098030b000c4450021a245034841d90148036150041c07c3d1603030102005121000d8002c00c0b44030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 296023309 1250 296022059 296022107
    0x606020601121a0f0405060105010801080d0c030905060c0109060501060c1505071403040302010b030c15040b03060f210106050904110418120914090921041a0a 70
    0x140a96100c8040c02140d03840c02655841200f0000b65401203c041440714804a400f41070501e1548050001170341c1c100e903d8003a840001c1000c2d440f0709800e50407518404002c0501510300b00317041c0c82d010780c07114080d010072603000c4d4082000c3d01d40d10004c04103034494a000080c1c5400c1c2c1d00b04a0100c841c1030b0014010401c080c9291781c08942d010103002c180c021110f10002d800e0701c5840003581e410106148100500b08080100300030b140d0198014800f010041e010f032130b0585414000c20008083e001007000c0185400c0c0001c2c002011030314040c0d50710260180103c0e62030030005c030008007500d204144034900c46400c0c100c184142c540c28003600d401004241d44084481c20103503140b40e113a01e04040d08501403a91000303480c100c4421000112049034000921106d02400140010f103c14100c0c010400e45a5102602d20701c90300340755040b1841100b00700050f06110020404980c01156010301d8813034062400e00c00481c0c80c1d95147c0322102c0301d628100b6001d6a840140f00b000e000003100c1031f107054007507203800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 296024559 1250 296023309 296023319
    0xa080c01140d020705070b0702090f06010f03021b0610061209110f04150b0306030c1c06090c030614010f0501051c0f0e0109080403020f030d0e240c0c010f0306 70
    0x142405076071507001c08420b5103540b10200200d000303000d10000509184a00f1000280781107031800102a094001c0c0d440050035526000d4100d2a0ba10544003940081c15200e00780401e50f100764041c0c0b80c440042c03120b44c1c54965054a02620306a015121141d0a5013a85401c0051a0308000180091491900705014064898a0b11240044060820350080809420356559a900c50380301c134000c04000c0401210103501c1e00259070301c5400c100d170814024814400144521703d090304644002100d1154424103215051b903551014103407004044880c0442c1004c084002800e1380074042a5142c103440080341d661500c04001185005135010a041c058200302c0d80c2040c01c1d4080d03110403800315421002c034001c0c4a6208060091140c91a9075480e546060704000c2085002d40040085074000c0f50300c24125103100f01055110050841e840d000305465503488284c13400c04200c42c400a010034201c00c04001030407000901c076940003402c6031403a5040407038150310668001c46100c03407003203091400308400c0d4101 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 296025809 1250 296024559 296024567
    0x20c09010b0904091406040606030516140409062009010201060e040201081501210213091b1b0c060c0308100b0412050304120b040b0a09080f0a02070e150a080c01 71
    0x182c00510702a903102c43d111000c3c00f45032658400d8000c07180d01100d041d0320305400d0882c0100350701c0c00f045501e4041d005030880c0c00d88400018200780c0305411620141c0070b04100070000140354110046809a41300c01c2111801710705005400402c041d580806a69402e941c03000a084030441d800007006008804240000342c0d0303019480d25030150765074105240c003800900040c0e030b050b40d440b03800c2c103861200e081c10094801029005000310b00a60828190641e40b0392107080c054901003a19030032284000b43d801482180b0404502d46101002030b4500041d01080d114022604800d03084103001c15210004001055400007501c0e070300c62204516440c0e45820705140a61510962044604840040c00c10400b03200c810300c04c66008028443d92491010b01d14900000806000c580a07504140c0400c0052028240c50080c5920160b11040040c41e0030004031540505402542d41d180441c8540341c0702250b401c9501040500400c6500c4844413800450020000740e0511500170910a030002c40e41d0490990300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 296027059 1250 296025809 296025817
    0x3111216020111010b06040b0a031802011b03030b0a1d0a1512080c030304140706210f0b040603060b031006080d08060613090903030c0e0901030611040302150a020c09010b 75
    0x82441c1a150140080c5046809000d03100d0305c595114500060001d813122a0000030031240c106620144110b03002c0d45801030700c40c0e12a100c083c1c007190024043ca1140b82c001d52984409910034200007441c901d0803800b00744030108a400040307801000381c00038003410282d203603142e9001c850500c0034840e010f00710080800309025032050b060a03030b120300c1207201009042416034a09650110480c1d03120b1909042858101e0b03841200001940918031b004600a445020020360980390301d1302c2c0c205600c2100c0c104000810582c100c036034003213075950422003a65031140682002180030300d03070200380c965010042504200901100c400b0040c80c200d02008540404100d0f804095801e0070401803559512006c10f40c18400e034512107031540703c440400310300c2e22040e44c0302e0b03c00309009507410007034110740e01ca003030715031b00008603429600019100040000450302d400c802501c04040c000281070a0390395000c242d9011400030300480880300401c118083c1641004071401c05038003102c004969515226081c8030500c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 296028309 1250 296027059 296027063
    0x90902011707030f0e03090109080f1203061c050109020415030f02061e030709060f03050f0f06120f1b0a0518270c13020301060203041205011803111216 67
    0x740500164419010f50300c12010790b1030410307007480000da00d4400141c0365407009003c980482c041c1200401d0010700098500c51413890b00c1d00130080503101c040f0a04031504000c1c44150302c500803c3e42031901c900604d09032200140320b003002282c40319540c0304100645241c1d180031034101d8914642000440c0001091000071501900e05e030780d6915000802800d050300591340c005031001c00100784040643c0c00120712003240c4c041c1c0c0d100d480c5249422822402c2d100c0c03d8403914030010085000c900a460703807191080c0c11160042002d04603c5501c80f0845c184100c9407001c43d078681000e0300c2d0180040241c15001002141104e460020908150004451100132050030740b503601c1100000d820815584403114109101e41e0b001c241103034968101503601d016805070540039200c202d811303507940d006034020349050311055006141018241914220b40d104c10307203000d89481d034980c001c0c44181c80d4080c0e42c5000031402540d41c81d41c041ca40c0b10030b6614110900d443e210002004115405001c04031a200c1e440d225 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 296029559 1250 296028309 296028347
    0x51003030806040216150b010302030c1207091806060305010b1303080304080702030102040b04090e01060e010b07020d06020412020a080706050306011d0307080d020d02060f040605190504080a03050109090201 91
    0x70700c0c0c06002c00c3c02401648402e04081c205000301200348000d9144960307400d12070f100e051140314a41001141640020754000b4203a460501821102d60540448180c0c000384030303e018440703990b4a90702d410304142000c4100d05105d54505d400c0c000c0c943d0500405000d81082d80459140c080c840c0004001c42c0c0007444054010310011000c00c040101140c11142110b8009000359141c6071113000200803a4030502c1021410b81c50301d212014100b41c1030080d00112941c0340744040f0b05a04e054494041c1e50700165049900c5090741e02e80c000000c1e05880a040a420704040003a842c805902c1809104c0c80b0680014102e903002080820140da40641281ea0114003803a1211210700030508140c0703005d1581424a078180240e060100761000d001034000701446c0300d80c2c05c90742c107880c9108059031501c00c1501c00c0c40b040310201000134003040464115a030400e0194042501685040a554049480980b400c645d04000042c542c0c1c94154907001c0d003405001000d60030045d6070800e9001030a034900d052801c0c5009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 296030809 1250 296029559 296029561
    0x141b0a0210060f0f090e0d0f030b0405040f020a050114040603020d0b09161206050604030609021c0c3303090303020418020904110a05030403030207111008070e040510030308 76
    0xa80c03003402030300a40007900505002c01a01c034480c00120501e039000d101078203d45403030300148420309405031890640c44240a005072034030342c09003215250024400242496203031000c52071603840c0c51080d248598020b039a0014920501d00c100b05000707a040c1d11103410400c40754100e8030f4001700507040700c007210b41d02e0500617a2011000c2005000e0003801065950090411003000f0528411601c2d0261090042c1d996542c11100c074010710003119414020242c00c51020301080c40091450350020a289000908580811002c80c03460400803580c00e504540f0b0500d92081004070b480d1401072013000240681010150001c070715041d4000076480c5030300008060f200c01e896400c0c076002c0e034112405003801e1100000d8050b20850740d0b4010350310004007d4003c2d4a00b9115040c04c01c024001d80390790090035501d607883c60300c1d039440c21000380d00f00316010b407801081048150745607501c02a100d9a07038030460310f41c4109480d2412000c2c0c1000c2c41d80b101c1c14003d504090410602c02254540c160603207a2604081e407036 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 296032059 1250 296030809 296030827
    0x91a150d090f0b0903090a05010201020a0507170717070506250507060608030a0518060301030b06011d03030703030b1009050109060c03140304060b150405090411010c02040f0b04141b 80
    0x4034042c500005002584014240002c281e000b10040c00408010340c1d030100c14965601c01203080b4800d036041d003400604203000c1c0d100010400403a8600048410b20810708054458403a080781001810b05d02c240d0020001c0c40904000d01444015407041da1107503505c01c24608203440c4a10704d1607401c6040b081120002c0c840041000380e500202c0034011b441e0440c0e131a2a4a980050543e6024540d101c6107900300042c3c440c0c4030300e85241281d050340d80c00301d8400010b80f02c403401550180302d02c1c40c0f01c80228446622880b880c2e28200003400c1114003035036005c02c4130540b250030300507100c1841c00c44408012180f0420b00290b6040301110003212454500048010854281120980526201c525140e032000040c030061113081e41050407107800444414b41158107005580015208502c18513410204030750008010503d4501c0c1c101b407440040c14035826006680e40010700311201042c00031356191b034503422030301141042c0c860005070068a82000c500b5042002d000c00c4200150035110404560000745802 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 296033309 1250 296032059 296032073
    0xd020306013e01150911040306050705070b18070b0f04050405040b040501050c03070806150d1d07050607021e0406030203160603050c030c0a0804020613091a150d09 72
    0x1907003007180c1c0075409280071442051400001c1e0001c4940703841180481c2d0350780c00810700c501c1a412800004c20040180341100c5003010302138543c0305c04e60560f0b041c40b0010100c0c0240c000c1c18859031803940c401e170751110580b50040d0308034005884079521840400380141094030010b158015a90488000c40d102c820084041d2039620071508010340203401d02080c0030400c48a4120321303000e5032182000380000d5864a081040e42c3c01308480c10000245030a012460508001680c181e0307003504000075a01e0031403407a64010580784c4c12038030034101c0c40560340c500008010038020745c0007402c011100d00f4a40744981d00090755a9807900c86410175819440700c021201e030f80b16440240195070140940b111488031602d0a0080c00840c484d4501290422002540480d280c60460348603540040715136040100000c4200c40340340c001003040f40c000c1820841e072494000e18030100350041100c444003007041c03050340c0041c0314201704480c00b040c00382c83c0c41400c000400910a080d94500c1e02c0320032000aa18003e410514 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 296034559 1250 296033309 296033327
    0xc110c150c0304030c0510050c071806031a15030f030f0309030702030a230604031407060f0e0d1206050a030f05010615050a0f0809060a0216080c0a020915060d02030601 74
    0x205120008001042017496503002040321342c210f614034404228200c0c00d403400d00c03d10314820040d801c614800d0000d40c0151000d00c01d016120403000406a44aa5818503100010b80c0c039128031036481010007580325811004400070603c19006402c0e0070600064490741c03400784202c4013204110110001d1941c940802c250b030f150540040c2200c1c00030186080205100d41d9004401001800c1c8031813450041301c1c0003c50502a0760b0560302c8103000b079400300126007150044641195a55111014507001036414010401a000c07141d0203031025078030510002e049141a26218540f05040c01410040c0c2c5e80c42e1401442100d40000b4030075a090018940030340103140310f0300300c240c6000d0311400741d0721a541c0c05400303002d410300c007500c400690b00a80310064400320411500340d41c450f0321905c00280f0404c1180c01820321500150b070400b000642c2d5680705840c0f40c11501ca00c0c903140d880750084e4410b5140c1082060b4001002c080b08110141d40e44020402074410020001580c40d0000301003800d81c0d100b2100e003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 296035809 1250 296034559 296034577
    0x501110c0405070e0127090b031009030e0406090605092a0304110a050d1718030712110a0b0415090308120906070e0f1c08030c0a02010c110c15 63
    0x304100d140143c4090114000c0740c9102c0e0001d2186c4642c1c0a5425001040c52081c00d04504c60b001d605290004a5010300302092000e80c050064080a082c05007181c040c1140c1c0504c2a16203840e040c10110610084031215401a0825402c0410030040c90701e802821580029030701021181034040d60b1321880a0172070740c001c81c9007a6240002000240100741d00501910a000c45071080e07295581d000308045c2c80c0400344082c042c0b40c10f40a1400300200c0080c000c2000042000c005840e03a220600060708164080e448400c01b01d54001040c030801c14084504035405408a03081060345040118140d200e0055008001e942029a0388108649000c0c19418009550101074280c1c3e4045140d010307021860240d03510103079441694045000b55014002030300e01c000001d0000c013440b0710078104100c042403103271070980e1805161400007000f14a500004510401c0035501880d40c401c40014000c1c2140d4804031a0740412003441c0c8040300000b004038580b50001403c4850116150504d80c900c18103102d00580 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 296037059 1250 296035809 296035811
    0x806030a110f0a031b03020f0a060f0e030f0d020c0310200705120f07120e060909040c0812030103030f050307090e060f04020d060f0b041a030406021303032d090501110c04 75
    0x2c030001d42c45e4104035400e5901c2a1195144501c0c113200f84241c546c80d82c01000c002c04c2408038648440c0d44a007144100441000b4111010024500d01b51410f1440c11410240140c0080414407160f00341008410b2205c0c2a924040080c0c40304400084200100c01000c100000c000003411410b0020800440c42c6818608610039a5641440300110a9a002c3c0500300d44683e280382e120f04401d40516194002c06c0740c050107142c0360904800c01c2004a91008000300c030291542c3e5408204a00300f003003e010b201460795085a07482d4110f0401a201401751910101041380030420054480c1c1d02c640c0c8401224107500144020781c4800c03002801c2100d15011a43e0403510114018803040c400c3d8101c01d085030045000e40b1840e0b42c030f07405441114452801240d10144480086c411111000e100455201d405070000505043c050509000c000f452030b8010340018034880105c5103003400f43c42050714207000c8c9080c80c2a942040a50140807000140703d52810b102080c03040c146480310a2040e00707881c544c0140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 296038309 1250 296037059 296037083
    0x1c020405011202040e010b0604090b04090b01030305041d3c0c03070f030501050f0d051e0604060b040905060402211c021c050301030f030c0f03030c0806030a110f0a03 73
    0x76800140b035060001640701c0c034205905001d00e0141803044685400c400b406246c80c180c00c190440e40a003000300d40b46904150348807410b10105102c1e84406018501c01e6650955480c0f9000032048245410110110700c0b00e001d03411300084955444041d41000101c0084401120002102c003200340b881c044c00c00c01c50000d450800140140c403400441c03003081180c403820030380201400c0840c00c49201340140d580045014034145103918000851811242c0306104a8100321580d154000862040202e1216190b0040052000b0482c081c010551041e00c165010443c40151751281c0d03540d14000340c0301030301401c00808003910a481c041c280252000c0d40b90304880410880700500442c0c101c11516240040c0503042034560710f82c004044074503402881d47e0300c041c110390850b169001020421071086003440a031506401c00120000c031250cc140e4040d440c009844481200d01600440008000e0f9109800000301a00000c280d402101d2180b0381c1a0387c00d81c0207807192004501c0d05070441d0809001c0c0c81d601d030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 296039559 1250 296038309 296038319
    0x52704020d2003070611060f0411130225020918031b030304060506010e100f022404030e1f110114041407060f05031f03151d0f0a021c02040501 63
    0x824002d128202641100d038403da6a58045810b0070600080c4880398101c0b40100e24400e404c1006150482e000d0f42400000c4a20707100092000d012170548240c0f80340d00468800049414501c898042e8004080e0083e8481d20300d600103203161078001c181c402c0e5201d003228012580101003050310300d14590030720030f140c3d01510700b00e403550350343c0003190122902d5082a00056883d403082d41101c03000c85014000034580e40354950140c0d820043c104035042107109042540342c0c0024074202b26815540c03081c1c4460210f0a050800a0041452942e81405180210044018003415080801c010081c9240010210389080c10450140260440d01100300340804180403e0000b00300b03890860020b604115030b80300f96500c2c410346800c0090b180d40c50100b9410f20001d1003442c0380000e59803c288030b1400380b5041c6ca84966500090302a91107003180b07036507030354682c03074500b050051200106c1030075820052140c5220f040007184d88a40c0d8141c0240501803800b180000004081c115440b000e600400500a42d0b07119 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 296040809 1250 296039559 296039603
    0x1215050c0d1104050609011d090106120c020c1c02010c0c090501050306090c0306061017010b041e031e03050c0f0c09060904030c020108060303071b030c052704020d 72
    0x26002012220b4502500c5464100d2180101c6044400c060701d040c0c01c0031071745401542c00714a4466420501002c00700c2e13111050f518035a2007406858107440c1c1d003030054072000c03c010859040001500075584030144d250103030354645000280407119041b00c60400c40580c40120342a42a640f0000c03c410580b00c00824010810b4110505a035016401c4644943c1d458095030b0f69040c1c881d01164040d04000c01040090815210484102956040c44000528042290800c0b00d00903032015000b18808901407025003101c14404071400d00714250340c3d11031340c00c6d911039000407001d46a00002c0107881244600c100b50098040e01c198400000945a5003c000094107440d002071140086c882d15055000990518090351114001ca4266550000640c00f640c0150380c0740c1400b5000030b82c188028040701000625503107281c0d1000140100a1010074510710340120200d07160b4208038445c0550824014000c2d03500180c0301c106800c000c4842da10b6032150b002195060b080c100005d8040021810100d44440c0c1c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 296042059 1250 296040809 296040817
    0x60304150c0c030806091008030703030b03070501140d0f111c11040b030f0a02160c051c150c031d0c011701060c0602090a080601060c0302010606020d091215050c 71
    0x11800c010301c00554004070440d02801160b800601103030340500420f0301801c102c4c20003544185404420b0900640310301045196400224041380000d450b50072400300e505062000c0310091a080c240a00013540f0840d9400d41401707240da110034940e542d5010310b040031090350069030b2180d0001c0c40440d9615441c2200c2146c0024013000400c1c12400d020071145660a064101c3d003c9803000d0042e142580c035425501145038002500d1541076980900c050b4600e024072800005030f26110703407181507500703240030180011841120b81c0d040c06a10158107aa011822221b100c80300c540302007800181400207220103400510042e41001551420300d005100e18980c0081c10491104003600ea03102642d540d01280c5169001c24000d03940040c01100107040050030750740140c04046401000902600d407941441d43c84d01c603090707119800007040802c00206058081c0b0035074003c0d01c19403001d4040c1083d030300000303021403500d48503182d020403402c040c201c141b20b5000c5020a4070f2044890a110500b811030306501075400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 296043165 1106 296042059 296042093
    0x1612030e0618120319111c03050f0a06030825061802150a02060103120309150b0f03060103020a05012a050a0b0f1009020f0405060304 59
    0x91039001030300d03a0015141e0107940c085000c03010043c0c0c88103003104000c1c0c1904100451607001e40c0130f90300e0780383d000c400f801d01e000080802c280b6245006003048841004524520049248950640007640112585855945251140b6580c0f80403541e1512001301640820007a1108613070f00c401c03e0440040344215060410080342e26003005603500c0c804541080160000c69004510b8100d81d21100102d078102c142d03003030584c2000302955500c0c0601000c1c1c5965041c02c00549082c1c07094200390243c0b98890340e00c2d58280314480f04180030b84642d40000340704405600c0c4603840f50800189450480e42c000f0006c055407407800e0019194948041f043e80f080203014010038900407550070b00c424401348144010171610515040c80242c942c00134040b118984200350900811025040b007800540305200401640c0340f40c03980040c103044c451030748607070b070070050200400080c03046010040103021 = true := by decide +kernel

theorem cover : BRFrame.Cov 295863309 296043165 := by
  have h0 := BRFrame.cov_init 295863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 295863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 295863309 ≤ n) (h2 : n < 296043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
