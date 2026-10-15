-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4580
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:04:34.090351+00:00
-- url     : https://prove2.me/submissions/a7f2d855-2660-4a36-823a-9da616471ec3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 823561151 ≤ n < 823741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 823562401 1250 823561151 823561181
    0x10909052812170a15080f03090406290903010f18050c0a1d09010612030807080f190207020d0b0c0714010e1e010207021306091d060601110f070f060f03 67
    0x203a220704c141440500914044015071510741c0707400080c80402081200c10003416030028640f51003050042008503074455103c5016502c48102d9000c918290007607289510800380b00280c1c40b4101003001c280140b10000108007441e01d0624503a02c01d448241030080000c2c403441c121220400b82c4d00510085144910401030140007a50380100c040d45c4180d00140d10054241c0002891682c80b00c841c448080383d51000d401041c0144184400c2c0307940820110340c401044890419603042c8981010480c1c03025083e11803901d607002c9180d40c110366034a6881e20700c4507005081c1d0411401c280c8146865a804500e088a65089407a403490f0141d1040c01020014504c56000c1c0000310046a039031448071004641c10407845d58200039410041e5610f105500d040050a240040c006040848100888020410703008048414240c18036050303400040d03140e4450b0007231a010516804901d40d00c0d00c5e100c4240c1810056002c0c0c000f0100d95102d03000e11010845415944840c0305403035204040d021102624840c08132 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 823563651 1250 823562401 823562447
    0x302040b011418180a0e0706090b0a08040614070509030c0f03120c07080102040e01050114031006120f060b07031806080c031803070c030606051008010909052812 71
    0x3000440000b690090f24020300b03114109607501841c0303442c00a088a400a1496072840c221140007001c10050010f820a800d11000d040c4c2081c07904020343c0102d030381d94810440759000040c02c0052075006409825060780007421541003c21014010b5005491034600a108210322007170949060005120082c0000d4080c18100c10180400c04141d4441c682040140c400c0140008001c03034244014001010050f8180c0419410300c40014010320008480941c00901402070090f40180b002d1460212500c03400d240c92908100034019019226103001c1405043c0792040010300e60560b20020440c0d94400c3c0d58420542146150b0f505c419170803800b500000070900e600003503684982400071900000c1c1c40c1086201c54040c5140c60345140c0c000f010403102903000130000c0007003040c240640703070140004842025009007102c0b002000408140b185451071030712183c5176010f008003400080e60141c02841c6040da018800300881c401c0d40c6030700c002120500140701c40c8042a40c4036240d694003a085800401075 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 823564901 1250 823563651 823563667
    0x21201030b0c09130506010219050309010e0114070f0209090703051b011e0c020909031603031e151806031a070e120d02010b0a03050304030209040804030602130302040b0114 76
    0x40810002c0005500e01010844a40f050742c0301c2403034209039580e03654046910302d07004000a05103c10f2260700d605800c1031480110003d10040103454100000f840e10b104070341046001200c41c10220341c4c03403907544a0005516400d000340c00421612144c02542d8a03407080e10341580103603a07102c59100240080c2c005d00104448410031551080c07038078405151244002c0c000345001d507941138004001a0100780a0050401141015105c6c0e95004001201860408280c0603140310b11000118001303040541d0344075521600400000c1140d801d10042004100480034039480308601c2c640e9008a0030464248810319400e81010f00030401900da22064240c03420340905c188110410f4060410001c6c0100c0004041c40b580b903000414109030300c40002001c90300102000682155422540345000340003c803020700103d40004102d5045030f5055802103c1ca668604060079140242d0700010541400007070b00301d550b541c0c8519507400f503031300803182000310312a8030703005641070000c000c5040302d484030500c2500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 823566151 1250 823564901 823564913
    0x917070302010e24130e101a0d06030605280c05091e04050a151a0301030b04080c0d18090218120c0607050102040611070614030c07050307060b1302120103 68
    0x1c50340c1c03950006481300e4030700c180c00d5400c2c0c014070081080c0c080c04800c1000920400d201e159040301d1032555200c01c880c10401509804030520b41440a001400942c0c1242d031b520590118000f140c200700b04000500741160a400b03d14607400050a070810042c90700306640e0f5062055440310446907c0f6103141103100400d02401c0070400c030683c58042c50a003076142046d1030b076000f16807081c2444d0100150482d0405900000070b110b641059800100d10304d10402030000107011281500d8004501c03012590301d500e005440f41c8074030350b43d03091103000d4070b403070b0030710045d04151640c000d40c1009906252040e148c4441e501240102e0f1540740c0b07031543e1078000f0031450030030444030640b08601e00d06942d09002d001001c11610b920040089031180e40c0040c3c10440d042d40040300002081000300603000d110314101000b056401c21181d44001008000041000a5400380445d00700e164030109a0342c48810a08000c4020448000268040c0f45285240c0c03115a0041c4203d40079001d85040803d010307421030300c8034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 823567401 1250 823566151 823566169
    0x52b0c020d0b04050709051501050706150320090106030e210915090906010302040503030a0f09030c0b1c0b0d2603040516050409020105090f1801060917070302010e 72
    0x9907088800c1c00710903008900700408041c8103900440090600524003440c84040701e000401c0324681e050500d41020050303078010111201260402000320703402c126000c0480301880640e000a01111840c2d40c010480d0380290030030028034070100c0e05c0b2100b51384e0b51501941a42d02003c0401c44541040c0a05000858a0702e0450006181d0b07602da00d05096405011038003940b050311050618040101e98140a131500452081e0321450078a410360510b40b400c004240e9134000e50a8080a22100081d09030315603204000f0f040080da0401031500c041540c480550207241c0c0035450b030704030400401d80c1e10207480500380201407640320042d041819148440e01c4e00c1e9a02e1140c1000e240c0040f90040030155031041140c05940640c1c0200060010038070242010011898076520050080e400c1160310000760381c2000c2910482d4000391126011080c98034002805074603003001d0406244101800407840301e82c0401c0392019182480d02c0d40e0680700d00c02000c07a68510349840000d00250300c41c2e5038040181803007100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 823568651 1250 823567401 823567403
    0x61e070f020a0c090e120f09090a02070f03050304150c0509060d0f0507020708060f01031e020102010207050a080a0219020a061404080f33040303020309150a09052b0c 73
    0x1070315108281903443d020303012a41e920510640c3c0c1c40328a075000242050200390321032207001b050302d46020030f01c04911146008140429100d80f80c2d0800182e009680740c1c0440308116809050807800b00140e01c0d02900c0c54200340c0e01500e08a10010921016845074070619210802c02c3d15842e042c00c02c000f0410805621204102d55020b458548030000a400d5006241c0600f00f15009410202c0c10301c0026440d101c070040180c20080401c2c401000841c1070b404015035000c03441c601000c4680715600050f4060320811000800c0e6100c3c100b0744005001e000c8000d00351410550b403d442c4556180c6c9007229040710004030280d441070510104220b07290044000c0d40b4400610420785007825640d400319414054069244101d5411086029603600c0740c5442c2074030060314112840d04e001d450031104940c20380d00200020107160780040815840034003008002c0f104401540c00c03800d00d00d03180503864050061ba0104849512455552189074000070f408500c0d181c01d0100c2c06135014041c0c1204481015107414 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 823569901 1250 823568651 823568653
    0x60a0c0c021c06140114010c111008011503020a050f03090c0909010f0b0405130204111b070905090a050d032c060709080102090f09040602130f0305061e070f02 70
    0xc006840c0c42d0082181d0818145102e880d20a50b410840181e03940391801c0c5902c12494001800300c0642070098084604c0203290901925170305140c010080458508243e0340703c039032095000341c40d561103003007181601c02c034012108526030022425130503801030354801c0c004100c0038011581210720300406541c0c030034204811104005c66807400b04804d42c00603100d034801a51070301c403c4803150303045000381c180640d0159002c006624060310043c4201106880081c1300300c2c1c4841004007007018080503116040d00e401400c2140702c0411750300541e600740074807070010302a080c84000b560720130010408020190f00000030303081c4186511070803001855a6508802caa06410f500c0c20402403031118031fa404205950000c03d0700e170034658030140011b003441d030000d001d030fa0040100701216100c04400406d0b05009403a424403586861401001a0049520074040c00c088610b001802c90101d51041080341d0081081c0c9a040c0c64030301d10041000d0403034049a2000458001141209116004690441d90f03184 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 823571151 1250 823569901 823569917
    0x5041403071a03180a030c020915060a0f030b240a0c05010203130506060901082d0a030203030f070e090f0c070507030c05010212070c1418091f09020102060a0c 70
    0xd02101c14001030b00c030442c0b1105004020000131900090121080d00d5659000708034010180d60001c140c0380034074030005c3c062030f4001c010581c2c00291a19100e000000101090384440711010b0041901c0c4c0b140303810800090601d40c580449080c03682d51200400b100c8004c0410f245041800c0301030350340c8140c801d441000481040c06011440a1010b9401203000440031100d00b04d90341002e600c2c001c0050240361150300100c0c01001500030010302c10003500700346c85404101d1a01c843c03106903002c00b22002048140a049488030403d94080300462080301d01c000060125100e201c1c04440c0e0032884603c1031b4102031001e020552011805910030303881101c40d411103190800e00e0f0740b103c3c00c000d025032046906018800082c403407503030148100790000d1400311005040030704945988019401d18030560000b0020341c2c4030503041c1d84410f140b5440300744110b010184a810040d60181d91680940c010031482c2c9100300284040c0c1190340103000c4403a40580c005c3c08541c50740ca01c0c00b0300416640c0b0280003846602 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 823572401 1250 823571151 823571159
    0xa0224060f0a121a01060807200c06030f010e09160308130506130305010606020d0903260c0f0d301b02060105090606090121090611090a05060a0504140307 68
    0x149003c0c3d00303480d100710701c1d46101810504141010f400c0c103070498800c0c45005810486c0e190341c440242c49198040020503042071038546c0e046410710400c002819001180041001078181c0c5e0204203904991014030074092079660341000a495141560741c294150080100810100d00b001d805422071020000115840c40d99900c001040c550001e000d10780640515181041401420b11545005200c2c0b07002030f100950b0040c600500e1000d40d0301008000e4900c01d0344065000242851200040c44a1034070070341d0300c04009a00c16a02c051902c841c9109102d0072001c014818800d81007070350303c280c018810f042da42071080380e4039103041140500800a42d6a800c00280c0d000d81060303000b5101030058010b4030a55043c8420710584c0d03400144002d0148d81c0420100c000d59900c40142c0c0560709a010340d4104440d4548190400740c01880c601518041c2414000e01d1041550300c020204202e0880c0c110a0b41d0b40c0d41d20034007400340a03901516000c02ca042c8010000e1510b001143c0111400044c250340c0ca550300c07 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 823573651 1250 823572401 823572419
    0x70c150501080a050c03030a090e0a0b12070306061d161404140a0e0f0402100e030601030b06010f110c1207030203030409150e010803072004110a0224060f0a 69
    0x260301001842d8001d030f0401080c000c09010078145050190040c52038002408006801030358140b103241740b01d0181000051a92203190b005e450540c80040c00d000b03031000e002c2c100c00d076138000c2400290348036031a00000042c229600541190841c5180c0306050055462600184201c0d01d118812409c1c0b1000140c4041c1c0441e91400520241140c00101c03000003070403030103203c1e02651940240c080822280305110480700e885ca813255105604981020703209401b89400c0329440303112840e2a805114030000441080a141e2030b65110742001c0c0d980044034200100100d40f0b28031011001c1020350400350181d9075500381140e041e00030a03180c80451307901590360343c0840e1560b0310903401206050307540d1020031407030b1241c2000c0c2c00040000051240a070350400b613505442e4030a41c0801804808260002204802039412019150400030801c00c01c01900c0c080d0443c507907010320883d1006020b00c41003650019400706800703024912102440940c1d5440409201c80b18240414480d0301941c28400040c408603 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 823574901 1250 823573651 823573661
    0x3091309060b1807020d0903050a08071e0606050f04021629040c05030c031c03050703060b0304051507020d02070b1e0315131103070c02040e07080105060a120209070c15 74
    0x2058064a406141208000b8203140d1001346c503504200c6040c20400104200280c00380700507820a0365282d80d443c40c0c2c80c140600b0000203540741c00003180e00390b068040c040c2690003a41203440544d19107507a1400c100402040f449440400301e82400605813040200d4940b8000007507000318401c3c1d101d01402c10b0b82828403c0d002c115000c4030301c09075201007403000c2c2c102030008030b0351200281c00801c800584022018082900c803c403000030107960340300141559106c1c1d00080000c006032034040341e0301d003424108952691000301c0224007090341c0700041481d007880042d10401410066000d03204407403c084c00f6041640c0000e04003208540703014038009c20f840c90000111300580c5c0508200030080c4004003807140003408807c110304020b103440740b1032809620b424201d80c5c1c0101a0718140f2100100c41c40050018090b40c401400c061286203400f00e00310205610660240104440c81030711590381c0c00d541000800b08002c025000203000001c94a0741d800384004500644c40740308040040c07007601c505071040760 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 823576151 1250 823574901 823574929
    0x5060702061c0204081615020c0603150301021c02070c06080c040b030402060c06073c080604240302040f1a210d0c0b070f08180307080f0c070803091309060b 69
    0x2540c01d1b508014590181c51030160301442800680302000109000586038003008169030004004520b01021641e02941102c0c5811100340d04c1da400751250004034802500080c6003291014490000414528002d142d014456102c002d01d080c41c16040c045084a16040504100d07001301c03040c4140e40c0f41e48011b004140c89413815a4400310503207110039121030100e00d2549000c048041020300795001c9002c2c8404503207040709908281c1d00700d490b00004680202008040010382140c200300c0907201d0384401d908902140e0086a05102e0001110002406c81d0f401441d19100d00c0d00b030048850761401e2076440311a0403264400d000e0740722070805070703c1800c04000f0003000000907503410200013001119500f05402c220b50741340281c5041c0c44210040c00220014106001c50811054092003580081046500c1c140d4010441c41d101d4401c2681e800b9550800351389242c1e24000d1240108544000000780c2c0e01d040c0c402040030071445504200013000380081641555190b0b15a90a0f150644600c41855655 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 823577401 1250 823576151 823576183
    0x1b07020d08040308131508151f0302130503030f030604050403090806070804120e090106050f1e0406030c0c1a060409060509060f06010201090c0b0d15061805060702061c020408 77
    0x18002129030000721000380d0308002c06e84105480b42c40b0105030702218041c0c0c40881e4404e0800c03032500da40c00040c0402000c0300b00b08450002a941c103103c0d0341d416000b51600d45041d03901d15441e903407680205a1a801800031804402c4814000514145402d40109400074000c0c01c20038011501c441e051030a20004460340404180b100051008001c2d030b031006204180000d1600a5000702c481c03000a00c82c1006118440c100107010541640c1d1280c0541216001d0400003000d042240404400d00e039541c015104120100f4680809050f0080c040d4250f95141c3d41d202ca04400d0541c0414100c3d1101b5201a000c207822035584d00b5410700140c460300c94980501605002000103140c00c06c080d1214810082c074490459040159440008011850040940300303124801c0c0e031a5080690032800910500c5644032006504060000e04e060300400d0349051a40c0724003406000c9a19401805001c0c49031a100a400060402054103060b2000b00c40e13000d040c042280142c074003580c44480a00c1c1101c5581c08a80c9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 823578651 1250 823577401 823577407
    0x5130b04051305010509062206061e0305040b0708040f060c020303040215040506040b030a090f26090906040e010e0106140a08011107030f03060f030602030412081b07020d08040308 79
    0x207a14004006001c5000c08250a00040d0304000c0440d10001024080301e0042120031076001c3c0b0104621205c030b04c6010009030821070541e071924010411013902554001d07074107a07588520492403290082c01c0c4102d4002c2c815648544448404441c80e150007001900c102c0802c0c116100084c2d4103014007101d22403180d00841c3c03a81020b00400804c20a0901c801e940d00000700410000b40d152401a2022107e40e000c1d025241d90b512118032010f400c80c10700051000c0400e100a40030004051030318206074403413000d82922244c024043e0302c180d11881c1601c80c0d0040074480000d0080c030b890741200450000c41d0001090b00b020501c112800e5808a8102e5018a046040045642d046c1108204010050000284114584190003043c1442066009010018035101d11281c81c0c4c000d40141d4010140340c404451102d941c0c0c1060b00007504181c604996800d40034021000540c4030b00f140c54090101000301c20780305204904868400d6102c240126000200c42c0c681402107031302003001e00001e5010721200d0350303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 823579901 1250 823578651 823578659
    0xa0902030a1503031b0f050f01091a100e041a070207150e0a06031d030c0604060f09051c12060b090405010f060c060b0604090507090e01060c02031c05130b04 69
    0x20586204442042c54000303507420400101e64840d200c003151a4000001c07681603096418010384240d0b40c080c001d00700f48125810400b10b138605601c071908050140d0407410302000000c400d2040c0708000e88000302d104003003003001e01903410001c9420360440c2c4148800c071541601c0380c005004a90b001c5510b400540c000040c101b209055209801c8661130651a0a000b011480380014902007c10301038001010398070401c05210003c00500034502a850804032074030368904011159813080120307800c5402c1030400d0440340e4005c1c3c003402040740365544a8064079043d04000c0626040c0360102c800c610412414030741d5042c11200c00e108080c05013080d40000383d92008032000340000e880c010f91100000e24602c10081054603071000840001a500c00c0300450b0b03445946c40001c1d035501a541080000c113280800f440401500807001c0350448a45084c41c040b0760ba6114000e6a01c03515844e4042c0d01500211450045610440c169140300700c01c900b0200d080c040c00281100000e041600041035241c7e002500388 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 823581151 1250 823579901 823579921
    0x10318020405043203390c13051509071206120c2702072f0307060302030c1204050106030c06091a0a050901110a2f0306040209240a090203 61
    0x2000f0001e0440c802010139000f03e0110b5803841590b441c408024802c843c0d8804104910300c00f00b00d080c00342c0e003250302058021741d0700030741f200c0b000c40c2034a01c10b002e4001c0901103580580a070714440c110700158041000b0f07600080c407204c960020030308400c0000c1110f072440080b400d4410301d0003400561201c0561030815140c0301c50f030440070350082c442501c1c510907407006104456405401141503a1400b40e106d43c000c1c581110851458400c01d200d400d02c0001205004d1100c0e00c2c1401100e800310b040347d041540d04e5509804900c403d40d03901711007000401607420342c0790302032108a8025114030b00000d04956251100400000d603500401c2c00030b050420b040000e5a01140d0000b0300c0a141c3d07070b4a51412050b02ca0160003071251007146818090f02c6004041c8202d070500440da156a0800b02141e40d081080500c01001c000d0861000801c86140c210a401c0e4100020400d205a50150900e45a9112003010103900c0c074201c0840c240102c0740030f003620f442c2d031915094103008000041000d40c49090418140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 823582401 1250 823581151 823581203
    0x30f030b0a0b091c0c0b1e0a08061e09070509060c0f0d09080d05030a050717040302010c020f010203010e130c090e0d09080c0a030303150308180a050d0c0501031802040504 75
    0x20362840d150003041d200c0440d0305011744404444621920070741c0c1e071004d0406441c40111805500d4845c400110f83d0800498002e80c805200d850212110000300c0b50b001c8a0a0b041140b0030791315900904c001000410941c003d40040c90038242c000c10340303401c059200c00e078145401c3c1c001d0600c7c2e4007608002c0c23005900c1508034035140c02030039246000d014007660b0301c4c1005206000c010f20030b048160303c0e940800d0100303000e03801d001030054008401140314607040c240a8081c00a8140c460018030031748540042005041c42501c0c160703a084040b18400791903000c6c1e0640d828100c241e095454014a60340041d107045076204051400b628034010b000c0a1040e0000a01501c8259016800355045841c000c1200c0e030341c070800c86007039030b42c10b003400141c400d000145034030203a950741c000820050002843e0340401c040760203c0180f02000301c030032040490711a000c0c411160084a40200540d4090308103004641c041d8000c01a000304403604030600520355000070b810b641050301d040e90354601016505503030321010408 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 823583651 1250 823582401 823582429
    0x1211030304080d05070303141806180604021314240604080312070e0a0f0801050105011e0c02010212030a0902030606030d020706030e030d110301061d0d030f030b0a0b09 74
    0x80c509092800196035140d00d800c9000e042001000910b600425000380c0c82001c130280c451004042c5440c10580e0308103c1071494608803404d101386000128103000c24558482d003e0000c00240960f03071210b60034800c40c6540540401c444903240e960b9807000f0110300d29810b00c01c01d21845010700000c940b03d40f41010284540c036003030040000308000d04c8441d100200311407640400b803032010801e6440c1c0c0c0085030b0125034884916031190300d0501c0066100b103034190700d0b030a443e14080200826686c607c01590009418440c00f85000340c0b10b1490051140a40f501082c40c0b801030050b51842142c0f40f1004e059030703200b2201e4940042c0e4030001101035003005c005842d23001c94142d0040400c0d1003000310180d41c03180300f0f101d60020951941c3e91240c64203810b200784d0b84555110181809005543c00b41411250024058140040c41e040300d02807a603101e1790b0303412082000141506078007581c151070840b0140b0043c03440720306040d200c1103160300729101c502c00c2100601487c648a80c83d0480340d01001954040691 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 823584901 1250 823583651 823583653
    0x6090906050f01120603020a090207050c09010303020613151d01050a0624020c0603040f140c01050708032d07020115140402071415010e06030d0807120204050a121103 73
    0x100c01d10198940004080c400c1009007003404d0420034810003d00500155007000b900b111904a001504050700d801404030700d0300c0b80f0305aa0100b841070050000302c81c1b0910004d00143d101c2c0020609903d6543c85501565016103000d103031440000c0440d1045c1e81904d0508420f1440424120501250030b1045039009051400280003c7c0c0ca021709942e07030004280d82c04540c4038000410400e01a000f000541c0004030b011f8010b90b1603151500740143c2e010b2060b401503403910001d00480326580c00120b4010801d0300161595800c0c83c2e5281c840f41156000245083c2d071004450f00002c1c88003614005c900000b044031080e8003294500100d00034295001c00340c5006406200c94414884034004110918207000103650050301c518240c180040241e80c81c0e2880b0701d85000302051584d510840011260603a00c0c280072001e01901d84006050381c0d03800c100f401000142d2030501082d2280c0c8920880034407114070788800b46c1007586842c005003509079541d014102400c40046544100f00000301da000103200218 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 823586151 1250 823584901 823584911
    0x1e07020406091505010e01090f140a060507030215060d0b09010c1e1202300f06010f020d18090c020c03240a0504020607120503060f100e060d0e030310060909 69
    0x3c10035400850640580e505000d00005105800d03442507504100400522029030310032a6611040c016007040c00c240140254070414000c42d1081c083c0048a061903490f83c014100c607640005000016000504190741c81071074649440c000c2a4100042401400100000070300b0306002ca00181035455001d511800c2c0d190900b5156a0840d000740c45070a107840c1c2c0305805170390303210380058842e06180141012494032891182003c95201c080464511a50400c1c11500c032507142d0b0790056845445142510005900c000101640726104140d0354a0450112440b0304400d42c441482c481960409440000103a000c00004607480c603040020011a40c05a09192500317540302c440000b0f5050000c02654030a501c0f100480d08544912003114a02d940050b449291480c081500034050740c001d0705c1e07207407103400200108000c40c984008600e00b01003254070380d80101a5503400b1300c501d80c0c024840441c100c590302d8100602c148028001035210b00c144168000c038045c1400c1010301510f019400c4686464500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 823587401 1250 823586151 823586171
    0x1406010e060309010f020f0a27030609020a0302060d021201050904030f140403020d0602030106020d03050f160507050f0a030917120c010209030f061b091c081e0702040609 75
    0x86900d4203800001e41d51550780e590b920502c18050b100d402c3c00c44000a100081d040340040541c800b90000e01801e5580309920054a1141c0245a008981d100d502500401f41000096900c2e440a40c4440c8041d00c0d1030801030750303500042d0b0260825440748030303969000200c44014500c02c5459a0240508407101c903500d041680f402040100801c80e1403060181d09515071600d80a504259001942e006007002c0c0d507001c0510f4120082d410030f110301c601501c1280420310940e400f07030003230a10854003014440c1040d0354403440070701325a040c540c0b60803d1000070881080030800501c200a40d840c207120003411605024600107000a010750b118400c5420388403404601d00c0c40200d140f00061000101c450707102c042003c1090700a1281c00b8000d0350610828407211072010001c10850701c07548508034030482003c89500410b6841c4100d0202c207521042c100d41e0800304051101009031818000c800860511960440044507a0a06030141d240b92801041e010114501405184080c00075920148610780ca6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 823588651 1250 823587401 823587407
    0x130c0305011701060b030f13170a0e040c21020702060417150c120c0d0c0e030f01020405060f18060406020f19030804122304030c0b030f0106031a1206060301140601 72
    0x4c09007030ba407c00700401d00031071143c5c0b03842e0004540e9590855219402418102c00c407040343e5005840180104490701454552445d20b071052100161207902c44331840c0c10a030007249044480c044030900300703e43c02d10001c00980c45d818060300103440b20a1350203000c20071005029260821955201120070707030780c90400c00c0c070b1407004040d80c210b100c0c031900300c102d561140070318000c1ca0b004903001c1c480258030384a800d801c2e039135000320f20745032018050341610f00c02807110710540d080c2d00c11030007801d81101003040243d1a0741407a5004202c13410f50480618040038000001950b181d01580c44032005a005180b48000f9280a00540c10644509440a000c1808940d0f01400d0b480c4002c002a20400c10180c0201d5140c0c000c952003c0030204894039107107000920b42002202e0341190000ba11689101c83d80802d03101160421680107000300002c10b00c8981c60302c50b044001c1d0544070503803d0598807201d10140b00340c945628005103c04604042c02c0c2c1480c000041c107085804103180c0e1204207504405105299030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 823589901 1250 823588651 823588657
    0x100e010917030a02160f0209060a0f0303080a0b15030718030c0b070609060606020114090607080f0903091003020414180130050c0108070201020f04090209130c0305011701060b 77
    0xc450700d00d0320384942d52451400001c0c000c6003801e0803105013009904041040ea21084440c9520849206842d6201c080a000360f52850b4000d04881140c00582400442d0040315415401400710300003143c005142e102117801c1492419070090300309004401c3c080142e0700b1981e805540c0560603105407409155864044400c1d40a05c100d2150440004202080c0000e68020300480d540000052000036130b281c00083c002c01e4002007005825204c0700101d50380f500301044a9002d2181e40d0b4400e941ca803141e00200e80d0915020307205052a100030017880b046502c45403800c049292807034800584951403c80c540031045030000070344d486001d50824046403842c50b8988941543c0031000d13130004007080c48101413898602c2c900029208000c046412003003000c001103501c0c020380c0a98840c00c054070b0301c0c0c030264240d0003042c2e03500e41182801d00081c0040b07030f0305501600f014000200541d041503550b40c1d1850803180000007890003e5220801803103100070340618040c000c0201c900070000285020f03000d9071140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 823591151 1250 823589901 823589933
    0x2040f140c070c1e181a060c0c0a0b0c150609060405100806010306020a0e060a08150a08030c01050103051e0a0f170316020c0114070f0c08100f150e0a0e1608100e0109 73
    0xb010100d18062380d04000c01c21000d078038170b010700146811910f5070802019604079030300101c104d104034034961740c400070110b03076140c0504000342001e000c90f12030900b000040d001c0148000c840b07054030b03e00000d9075001002158000e45c0a0800140d985025410003414288203c803406e001340340400c50082d01d240e00200b20741d400890301b0a5280204800c0000610b4400181d0001c0300912012a84250103007040d48124100c034812400c50b80d1051388019100403009995150403000d4010048001c085604030f00c081c24054403c1ea6a0041e000000b501c0e0341003600161100200b5600701c00c1a03040d05030b0100004100760100342001c11201ca1101020801351003405001007030f6008000801082000320b60800c4050000c00d0f05a03002c412210408200a00e0f40c8000b68cd121802c04110101e0b030500401c1c503074191400e6031440c00f116a14401e00344082c140d00d004202c554455508041c42071115041481c01400751003001c3c01c02c11188041188c01c0d50000016942240d140ca04d01d000080d4400d0342c40c0e5060 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 823592401 1250 823591151 823591159
    0x60d050a0312241e0302060f09060f0301030302060708090601080c01141308101103010614090109090c051b0309030a0f050a08031302040f140c070c1e181a 68
    0x84801402c0c000240600490144003481c40c100641c000409400c9684182e80b0514501c403800410180604c107800300700d10011790007000801ca00e01c0941003850040c004100040e25a5190081000c0d5507013003644260302c11750050308400144048aa4011019034101440030001c1005504000100d41c40e4150028a90305200101d1400b00d4030f902400c007070310011002c407540c050f04140d440b840c2a441d101c001c3c11000011b8a00864000700314501816131341610180d03030b202c1d0070740c2d0740891400480b9131002800f00d06100c0800700014440205005a40062007030359a615150178014440444480e000d101c09415a00f0510103151a501e001400700002504041c207084a01241d007002c604108184401a01c080400030070810303030321790040c0d40c81d102c180f09440c20000c2c0304100722036a00710783c0c2c06403115000d405c0500101b201180d420780540049070041e010580a169200215050035601c2103040d440c09604910070001e0b400c2d2085181070041d00078405202621100014030741a0395268030103445 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 823593651 1250 823592401 823592417
    0x3111040603091b142b03120b03010c0302190302073305070201020403030f020d02120f090d0614010812030103020d060f0c09031b1202040911090c04080105060d050a03 73
    0x140207070540014401e503001204121855240d001c2a04505030000003617016000000e1801072010241418401c1034140303803c0744421904940d0200c0b5003440f00040070394255100d40807404555020300c00c1c04002841070320016542d8a0f5040041140440945400245441844100081462700d17203403c802072000000c01410202e400300c121071a02e50051100d0300c0612300410024825015402041902e00980b645000f145081100300c1c0d88101c4803000800581100070b030034801c850340e000a0a050f00c443c07050f0720304020041c004a81412680c2c60709444c02900c841811001c1041c481689014140d444040c1ca28803501c401d2041c810300c010b1000901645090780c10400744400799210114504200b802401440418030008018141c10301043d0741da411111444a051101c10b1444802c4a802c0111035502001310303005c00c0010881900141e0300084102c0340491b40d83e4810402511941c1000300780c80d101c50610b0611030866500405a5001e680c0c4101c1c1e642c0030500029003071254990502e01105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 823594901 1250 823593651 823593653
    0x1e0c020c1e06071a04060b0a0f1503150803070b0a060902030402011e03060e0108030909160906050d1116060f05010302010e1306081e01050a110a050c0c311104060309 73
    0x6032144d004070701800d418440005000400c911500b01c682103203011103201a4894035501140e4044c9490712400a456a8440280162a0082d00017a1405150324800b400e400c1d0b072442640d0965029150444042c4a40702c2007106c2480e0501c20000501000c640c11401c5240590001c1c0080d20f00c0442d1100e02d01c06444141003040c801e41101d8003800e40740c943ca8100e96592582141d482d0004000284200708010020790f0400344100c6403000c0d0030481d6038006100e45801e9054036680d0224180e0b440064071414030100042c522001000b03004541c01c4a200d0158550a188044424086c65840f81c141440c004001503a804041c103100c4010845000c0c81c08480003a10b900146115845080d07030f03009441520075515280d06480c406650100000d2140780d5603a00d20700c00721840700120740b2483c4414040740390110301c24000b6007040d4042c40216100700c40c40d000013030903880c44400347d0440c10804549180700300c2c0303e212800d1301000b0b240d0428404020500c600342c030380e4001c3c0d02034003080580e1340710b04d00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 823596151 1250 823594901 823594913
    0xf082505031005090c090402150706090c06020303040c150503040602210106020105090d0806210f0115030618030c02040e10110c1c08191e0c020c1e0607 67
    0x250040c1001021540d5510001c0700480180c0821039061166002d068811403490030316050380c62003198000c3c03180c0010a0782c828464402d0708001410340305203a44112400c006400c800080c2c025241980085403a4607082c40d000212222940010f100049844000e0390f1142e0404190798209030b10100160b102c003002c01c0c0584180300a00038400d0140380803c000608141c0640c01203000d0002042500d41f0109060410f681785041030b9241074002c0c546a031500322804449031040c42c0207000e0000d9441e540403091409080d00d40c0d54841054403e1045410001c001c1c15110300200f003c90381c4a10243c01b1b5840e240a07004040080010f400745840e084111a140310500c403a020020404c002003280e0609402d40d000540c00c03600c401c0256101d00b414040480c00d244080820039129981c4003141aa40c100c03499064001052652110300c0c0c48260f03509180c035800c002000004031031500003502c120508802440c2210017180b0b54010755440b200c02c05451894104988d41050981d440c0b640c0f080036150074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 823597401 1250 823596151 823596223
    0x5010506030d0c050d120b1e1906020604110402070f0b010e2412010b0604031110032007050705091303020105060108072010060807060e18010303080403090504110909010f08 76
    0x540c0028481e806414010f0408c842d010400d1041e0f03100c4072548400d001086007211640038140161b070110300001c0c00180c011280c1450b01c072016102504210540c1e0310300b038801c0d0301040d048804400c10801407000a01c000c200c558001c051250550030701d0352030000c000801d000b43c803180c0d0094000c0040c00d95415803d40220942203c09004280e8565480c100440340803000c880d06072103072a1100300d030344a09101e40200c2061407604002480382e80100003020180b0b9100c25801c4409020f85880007a441d540c80308041e00c29074801142c0802000c96280c005e0031250000c0074181807101c3c480c140400c0c140d1001c2000b000d0448010360704403c5ca0400c90141c0b40c421082e0030401d420341040808122540f0100300c2e00100c80007500d130300030394008103000c029074848085142c586046602c3d0040000c07901c101d20340b03600640a0f090a99080d03458202143c140e8548503025542c0881c0090304100504118140600400d04403103040050340c101000d868480903080c030004000100090381c441c0108062000c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 823598651 1250 823597401 823597421
    0xd1b0b13080a02030913020a140d1404080307171015180f030311010603030e04021803012406050906030109020c07090f0f0c03050f18100905010506030d0c050d12 71
    0x1a20380b2240c4141c00299240e200256040c040c0c2c0076100703003408001075030007a5220084143c0f07400c1c52402c414254005642c208400c90000f281d02e03820540c0400e1980d182540c001c1c0d000300c150980d0707407801e81e0021b040303003159505d000c0e545040182007041c0c0c105030004403000d0314004111281119001101220000f09a40544903842105100000e038812506041c0003281d100fa1103100708101400e003d203080b104544070150125204401c1502d00f0303c1d00394001c0c002c4101050328040680071a001090031a02d0401800300c0d80d044000d42c02d05000c4041500f000100101d1500c2d0b0310300004040401c4c8580018807c1c3c0c003816402080303c070a9240c00380032001c05840040410045030302c605030701a020305008031090700c0c00c600d003d007101c8901e0f100780101c600c5814104010f107641d40b0f60100034904400140079464a90060031a0748419003154003c520400707001c1c0c000858107040c000209410103142018032000d000507003620780c000032008210040c3c039400906100381030201c80c1c88540054041e10b04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 823599901 1250 823598651 823598663
    0xf080601121509061d220b1306110a0212031e04061406010509030d080a060906030b01030b06091e070c0c03080d1d1b0613030b01080d1b0b13 62
    0x1a220600c0004035441c0b1080354110b03282030014503070761209640710039010b00101c690100340c41c00041c9044400148102050030400303015850107003e880345da101c010191800d1800c02c3c102d40c00d80084c050113001e2002d0040e0640202844d0030f40c240c3c00a07558819032051801d500e10003000260896209500da44544a00740c14241c401d4645803820000500d28941c030029170400d480c0c049806540701d0016903907901d00103002407001c0e280a060984094030010b00c01c0c2103803038681801082c4650140103078001944587c0000186506502c0e10159088004103814003d00d4031004205240c110342c06070381c030312045103c03c0f12010f0b04c89030300032205625403180103405030700c501c5000010890304070300600a142d03969400700b04000c40318a680701000300380f140b081d4143d81720358450b0080000307407032103010400002040c02e40340088600c1c08800f00c50065200340c900000d03000040180d02d00910413100403501030b01d40041c0c014078502004086014001000c0c04803410100020b12140b40241504001c5030451 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 823601151 1250 823599901 823599911
    0xc020d0609140d110a0b010e101e030507140d08071a10060305090a080a0f050d09060c02071205030a0f0318051b030319030e0a0602030106020606041a010f08060112 72
    0x3800c02e56441e6808800c80d00080ca861981c001031810215010401e1548855054090b918100c28841c00b4000a80340100304284a1000106040903100c8020400c41c7e030340760000110702d1400c01900345011940710403546042c0c0d108501c1295070b914001417840350b0140205407107031007a04060403800741c00242103810b0080c10703003401740000d07481c8103003c121112650103101580c0e98199841c0c541985520080500c001817041d50348003401416911070301c1d126441c00342d00b03010002d24420103880307a0700d00507a020380d6190130b860b800c554144586805010b0060700040c940c149540e569540348a141c0b85c440c200405004108043d603c203030030107915014070160300c12401240342405504d0f55124140c0020001c201c5420058504010050725595541041c00d0304441200501c10380107420035041d0242503014540350040003c00601c00365004e84107a500520462810105120480b50364a580e100d501038041c800701800ea034000c0a00c8580c065610300809140c68140040e0b03078818001c0700d0026564184 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 823602401 1250 823601151 823601183
    0x190f0603090321021903020c0a231c0816090b090f060c0d03391107030305031515030a0f0e0a06020316030207170f0d0516090609060c020d0609 63
    0x180d005007911042882048a010141403003e070300300e1040180054240d000f40815201007030142080e0b12034010300c03688a034402c207030701c1660074104000c2c3d902192f880420741312044010f42d4404003072035102c505174030003101041007583e02500041482c440c8894a02e80001d904055840e001d051810252000e0010360f11040c041340502c0d00c8101d18404132002038036100d880c901441d04401c0302d60280703030f0044520425000c2c81c0c000c20750410a900d182d800340100f13a080d501d801082088160b000314040e650f80b903181e05101070300d209001c044014691195000e8540141c0c0c00114504583d000584e403a80020041408000076020388800702c0503844030b000f060000300038069150002d52141d40070319501201441c105005908a0141100240010740d04600c2000459003002c010325003004244901800c00f0205101d040684004580e40104140c1c4d05a01b0040c0541080390354000d0100f42c1840c0c10064107140c4024104100220040d00c280340c0d010020b030602199520480c8681d401002e110640400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 823603651 1250 823602401 823602467
    0x30f1f1116051c0909150305030a0f02160b030a020a0c06180611040308041a090604091410030b06012015041b03050307060b030c0d030905190f06030903 67
    0x41c409454a004440078100c10440701d9800150301c54490b126506000c1c207000501c001003640c0084001c240c2810900480440c0e400c001410003040c40365103d40071140801402401d001c85600742c14000d8000900912030511050107803035100a03052001038962914841c200e03114548110082c005c140362020b402c032011030030b4000301c0c2104d006d04004e114401c56401c1043c407030710503032001502c682c5042c03006110060b031801c10135170170a80080c000c1c1c3c00c0c03030500e40c00184c1540c00b0358007070290243d4441c0101118a0440781540e40708012150240d112840d6440744000d0040c000e08840c10080c60396003040b000303011b40b034405a1800303405040b2a01d000c000c034141d0040c1d07082543d080d81c0c0c034980c29869800151400c0141d2081e86c0c0d002c03001e035050900e151346c1c010240408400e0158513010b8007000c500183c940310301110200d8025036810f600e0350f00c2d00c002e1000014030200007030365408000c10140300c0348280035201d1003103075074900e4001a007001d503003002c0301e8a42405c00340e0125940a2180c030203101e04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 823604901 1250 823603651 823603687
    0x6091816090203010602010e0303130209131401020301051c02031005060a09090c050109210f0816030215070203070201020a150603050615010f09060e011409030f03030a0b030f1f11 79
    0xc5a1b8000700075000c005161160780740400c0351038064203c9103900070401428400403d1790030a00e0741c41061174100d00760790f4001c00e1072050036064126070f501100400c01c0e49001002c40d00c400c8401c02c81500064215008a40c40c4c030301d0f5403540c04000c1d807139038045082070720740c2e00c0454010504c8810802c403035803445c0b0f48004030701e55510549001407031a0001050090500060b0b4002e440300109a10b00d40b0758a40e00c811120544110564804100f8060005240210144240c4040c803a9001d0403003684240340014510710090300e884c0456000340309040050340c00103240d03243c0c0d40e04000c98862100340b55801e02d024003401c2d00010282c5c0a0740c414000030035220421910480801d89440ea42d01d51822030071038150416214800000d42c5625040c80c03d5405800f80c0a4445920700b50b081c80c00340c40502003850003500102036144c1d580300008021140303103d44a0ba0b1003501084014010002d09440a140e86800c220508951800d0b02000b0b02807804103a4422200c840e0b04e8043c40f905c8680008050004103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 823606151 1250 823604901 823604909
    0x2101060801050f060603180102070609050d0f0504080705060c010f09200118090515060a181703270d080403031731020402040e010510080609181609020301 68
    0x50700b00400b0501c04901e11101034480c0350007800241c00c50b95003600700720106d401548200c900d9503003081080080780841c000c514203203010b00010301003190421001440c8070b1508c0d485408014051206001d0f0700800b0890100b21402140c0e40b03512005141440c41c018a4002d0800318a1441e1010b600200511001032045503140300b50b00c042c001c9044d0f0015a800001e00c0e02601907480c0b540d205024130310284c2d00c04c64105880600000100329111f0208019601c050200c80101e1440411b00100841940010b40501042000404034144801446540e40a40c003e2003100c41c811800f01d04203401e080d400450700c1c040c005c0008040285604190135654424002030f0000f0f241c503c5003040d18003410104600070080e0b91004820081d60580e580306010b01c0c6c140b040042107007004031201503683c0d400900007403d81c00c030712401c03d545004208144c400b2002100340074003103084108600ca60324000c0b800d03132141c0750114005035100f001e5013040c1803046091581c0a01d001d40307600491440800e0313025506032 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 823607401 1250 823606151 823606153
    0x70602032713141509010512160f050406081504020402160f03030501050f0105130e0711070b091801030512030c0d0c030b0306010504060509180106081b18040201050d090221010608 79
    0x585850413442c08040c10f41c0a11600a00e58000401141c00c12070300c41a0070801150544100310702d10041c1e0306030042c13a60301090000c004058144200d00d418031504004100b2400107000d80c0c50260041c1745024001000644581c3e030100301081b100d418082d51003000e40d8809040f9841110030710380500105020b011f0540a00705038411901954019001c4900c040c0c00c0710700d10190180781c05040380648800810080810401d090f0f2039108a50801c400c1c1c2c050506101000d865944200900143c485d80d415081035107000000100085100403c50b9039a0011014009550b42d55104404207a8441c02c0b0040188034500035510f480e0680c5984480ea030340d10300f141175881c2039903900c0802007038900900035140e21a18075404248403c2c084408041401c0c0500004544940d440c0704060411b0020318030079103520041e005054840c900300c140602070300c8034141d80032038604007500002e1407400780380b000a6156039554904030070342d1707900b240340004441103041c0d801c54600300c401503034080c3c4210b100380416 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 823608651 1250 823607401 823607441
    0x20d0b06060715230103021c110415181517031c02071115120603010b030703050a12030621020d020316170c010e09070c0203070605031503070602032713 67
    0x1c8070031030b00d0302c84c0d040780d800420240c1900b100740c8001044401c0c65030304131410704000a03560080d80707950003001c42c44002200440110751403d51000b03242141c1c611313007400c010703d070501d00710214040e0300c413200541c4d6110b450200c1500004440c1841c611502c544890750080700c0583e286094041c0e0001c00061740328a4518a100d0750306000c0c440024160103101c40d500c40d05000c003012003290440110307800203000b800480c802020b4808039003845038170782095909811005008040c0070a40c40c40410043e018603007013010390700d0f002524140702e28021840811008150b002000c3d90786054607400c00907001400e07100c00084000103c449003401c0d1044280d400a0802d04c1542c030300c1c002c1031040d034510045c0c5400d414001400200004424024921000d01c0301c25000c02c0050b880c10851746005c1c100c46e459039584c0313050030200081d901079901c00c26842580014400c0c4080c590100c1aa139000ca0075035500c02c0c0903080c0d40313483c480164865590540001c0d51900100d4120996001b1501c071404921030441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 823609901 1250 823608651 823608701
    0xf140d050114031c03020913060e06100507110907261911030f0615070609110d1115160606030c080d0e0d0305070209090f010b01050403020d0b06060715 67
    0x521020304d0000e1a800800c1d00301c0c1070b605240250000c1140c200000d042070400c13042d600310310b070071243c003608400072403007401013042014100010700702d15010f42800d115080600c256102d0307184014030110640a9403845010444083c050040014500042d00411a01c4055213384000220040b00c0b40d9454200d011410401001c2c1880369080c1c00241c03441e414a19a103204519a102602a01c1c050b00500e00c0200785070042c09082c040c2030554819200400c000b01c49041221391000c5001001c0d04c14107100850200141c01b0701c0444049080a5038080c0904410f220711032160b02600700b640100b070340b10019031000c11a0a510141c19a40304803041c0e4031603500c030814540d549902611140104140445074030b100d1502d030a640e00410701c28a0b02c40d14160442e4042030040300d0a40f119031047c0d110807206640c00e8000e0041f034140140c2842e20a04051460f00007807802e0448241c003800b101c54070700c00b0030b405407950000c44030507540103038203541c001038001021001404544803100c6804416481a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 823611151 1250 823609901 823609903
    0x8070e0d050705060901202d0a060504020f102613030e061306030b09010905450a1713061d090a0609050a14070f140d05011403 56
    0x508094000000380100b50400d030600050390f00030703500340381444039001c0b0816501841ca184c00b1b0310041d048000d00350b98803076240c20080c00f0f001200a050001003103031510100c040c00140450340241c0040001c03640c1e48450010400c504a5009081c0d0021400d51a00140c603800016a070100d00c60280c40c000c0b1250224500400c980c1c050351340604032040040114082403140c00110f5030207400400300c3e854081d014404014000c010341c00203001c20344514121080c0c1c5001c49500b8014480101c0903c003500d000c40c00350b062001d40c841985626141102c0f800640461503580d80da41102012903086500380c00388030942d4882429a0442d50030024400c2c20f8500c6038a40166054210042c858401440c01c000003030741c4a10160b644415a0405280001c071036a840406290081505540003c4c030f507810309160700305449004001e18800c905080000341e9a92461a00c1a40503959140683c2c101d03583c010110348643c0d0109590480e040003213903144001502c4d030700482c100d42c4403d02c2c091400c0e1508040c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 823612401 1250 823611151 823611169
    0x203090102161202210304090515030606101202090603131b051804060f05042d1e020d0803070e0a0816030b060d050307050a0b011e03021005070f0308070e 68
    0x10f82001e51242161401402e04403a0844038150000305104400184049149140c0060f8050350039992a4014403100540d505540880c00c00d003036015140901d41140494907180d01c04c005207041140e221110100c04c00c0c10b03415a00c1d0403100074141c50f0740381440c030208107202d0a01501070b02d617040041034041564234401c0200c0200c95000d440c00030340c0c0c040000440c0407080001e1003910010746a009083c139400780e40c850184039600c20084003000d405d0400614050900100c90031703a0303403a54054014003007040c440c4410018000c540011255040c280b003c10030300004800014007540c0040140b1000980000d040180000b0035588000c0300c83c3c0d61480c9030b65034901d800f41d06000c40503a03041400440c00100040b81e2003480079182c401084000d641c1c0501c2d5612002007501c203070704401035404c20400c0448000340140000040000f0560080151944191b554070000703100d00e03074500610085a015105851100c1d0700031a0402d1002d550b0305000e043e01408940d01c40014203000f005620300d182507100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 823613651 1250 823612401 823612409
    0x180303070b0a0f0e0d021f0c0504030809120a060209090a0203010b1204020f03122814131d091216060902060705031b0106120201050a03091104020a020309010216 71
    0x81146a0b407100042140200102c883c00b003506900c8240b41455500104400140d00890342c0c0144002c2115201010070076a44074040202c803428503064500c0c496025081d00c0c20340e90400c1456a49030400d400040c41c400d01e4081007032080c0500d001940a201455025000003035003507034000c0c100d075201c20780c1c84203d100902403c108502c0c2800400540c0310040341e0248c0c030500c0074282031142400d200000c1d1038420344280071010f5120001e4443c1c402c00f04100c80b088404c49c0c5550303a150300d50060001801550020511390003032407020a98001d080c506049040041040b09030641004007015403040d01c0032003c4600084074071420000c1a0182c421100f00d500345504000b103450010429a00c00c030142100c1481a030f4091024084100402e005000811034050035a0304c2d80c0041540401050130b44910350300040d200c1c50042c9402e030150b43c003c82203407181c0025140020707006401b89081c600850030090700701d800c1440801c00d03800c00c0d40c0020044c070001b1b0090b001c030f440d00c91800841c0c080080781402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 823614901 1250 823613651 823613663
    0x7170c06090901210606120c1514030c04090614270606090f040e0604140c01090e1f060203040503070902041208070201210504023f01090204050c18030307 68
    0x2c010444000d2103600242c110b4503412080c00b0b1050162104015616141c100c2d00c03044d001c1c100b0502c10090f90489010007030a0091032104404601c01c0080c103910100d944031030700024001300003016800c400c402c440241020301e00401100d030f19048506c034040c0140160f01e0050854409851041c2c2c0b10302c4468401030a92100c0c10166560740c02401019000103480941010121015401558442c0501455040244002c02c403619003030600c201da210000503050402c0d080000030700c1c803a03644280e000b000d50b9032400748050952111414209445480742d248000d00301c0c0d010011034125404070060040300c008600315280b464803061030900700c0c0300e14802c14a850390302000b28400a400312010300071150050401003100c4085061030006c07c44240d982c0e04003956600100310442c0703803128919540c40703a418070094103400941c00f4a25032000c0c080644881e044890b8181400140175081840481d5020781305220500b0642c10310701654024030a29081c0d0421007881100609000040e6aa4150011 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 823616151 1250 823614901 823614919
    0x303081902092b0c030f11010c080702040c110a0c03060c0f02071406070c0e0412050f2a0d050c070909050703080a091a09040b04050615030901060807170c0609 70
    0x41c00541e9503a011050244940084034070000c01c00c128011350045015201808041c0000e01c1d1120300c007000740404a050000c1d5421400208519409a9412a40c140c0b0000f50115a040081c2c40c0503401d0841e40115200c0c201c1800200a65400c4140880c0d101d410180000780d0344950944038030b114040c8200043e0b1060908024002c403101103110202401b805181c607110003a1100324031412603400010b080707a980070a02041108442e0006070040b10b80c64880d00f41684881c01d004503115410101c41c5040d040e2100f9600764407007008002404c0340c00710480313600000951010b44950801e0010070042c0c000c410000500700c0d22030007200a401d503c0030180c030100381140d80e0141c0c1c94010913090020000143c0020404881d1450b2610704042d0aa10458480c068401000180c2e00d0649040c0c0c00b4a08150902a554407034003407001c21004410f1955869039034542d01d442c01465a03511070901807150341400614900213090444000c0e650a054840c4c1f401c81d4002d010840c0b00366000181c1003e0700e4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 823617401 1250 823616151 823616179
    0x30c010f050d1505041b02100204030b1503011e061d07050403080a090b04030602091e032d070e22050d0807020a02090108010c0912050601050d020d050106030308190209 74
    0x81e0748a158210f00b58401000001d4481c0d002c24103c49090303a41601c105100d203100da25140d010000041050f044c10700661602d4107542d200805480050902401c61813100c066200035a802c5d0410f010300d200603078640304400d01240480c00075002a12070b8142024100305803d500b0302050040754410007054803640d180ca40342d031751091216070010752004100018200046681c07480c0d41d004100960044802584410f080300400466031806090700c14080c892281e48801520042901003042082d004000c82d030b418007501225a41600a0030b90416006001000c14811142d400190041c0781d018401c1c455072072056285e0070740183c9120041c003154401000c94880503c2000c0265000f17980c1e205503400c107480703a80811752980d402e80114107540d45580c0c12a804680c000036400040ca09030030f0000409009445280e121441802111301039404030082c1b0b415925008034a8140d682e014008102050f0b582c00e008100c90419500408070040c5a03414001d015000d00944000540003080ea50340c0c2220 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 823618651 1250 823617401 823617427
    0xb0303090907051e0a1d03010b0109061d060d05090105060607081207050909090c0301150f0b031308030a02030718030317040c0f1202100c0807080304020303040906080c030c010f05 79
    0x2107401d1410613984081c5038071001d448800580b07102419a118480000601102c4901c50000f400c1c0d094042c3e031404a00340707070703a0781d01c0340d4904200d4906081011170039140c10881040c4036000428680c1144000406400001d103070b9008078401c401d0100200410b850380d07401c01c100f0307218a5901400880c4140009284001d01d10300c42904000741c1d0070214542240d8201041080b00100d560390300507001022410440d003001e01513903d544101c8601400c90609042c0d0440c42003580c0d015030422440c0201c0000c4603900c5640c02c10450540000140d5128984171b02203401a6000b111118002200c1072407042842c85083c090006032541038860102480c03641da00c3c03440c5800c00400c15542c0080c590f0000a098881d60340d83c40141c006d86c8001c0051600a00510081c03c5842c901002042030312a00034020400c1402070310034191713005852554035291800020301e14041c85e004100018900b43d000280c00000150204001c2010740c1510308445600300103507401160030102202040080148030f200d400c0d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 823619901 1250 823618651 823618657
    0xe0313030b0a020d050403020f0c0a360204180b09060f06030a0906050a0b24041502070305010501060c0614280204090c0807021b0d060c020327040b030309090705 71
    0x85402c0041c2405901002d07a420788a003942d0540c09030300038942d0700c0503205003403061000d1480e050b42c00b170859a14001e66850402800c0742c4c94510082c845103004494090001d08200710010103505540702d64135460201d4002d00014a00c1e1011440c1015280c8982401c1c01d02e107104080c02004052140c10f01003d000103544001d1410141300d50760303002c8c000082d0103403107240e00805d0010ba00141e0501ca800c280841d02c00d64902c1e91030300c0e0b4102c5034a5a0000150703001c03a0103481c118942040500d40341c10041e03141000035003004080f54282000402d116902000845840b03000707450910031a014100e43e900e8650098584416802c0c5803d15804000d807120641c03031244100d8180107140034ad840303e0300303001c4500700d010201c002007840c014450001e5042241d216410300301962141003820f00e500040c8903015211000701080d131175820300030300319009109907058182d91980d1140c1e00d8482200004807412030714200351003186440071004c020306000058030882070700030304002c429854400082d14250 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 823621151 1250 823619901 823619911
    0x90a030309050c0d051b010c0f0219180203150105090d02010509013e190308040804090c030519140c0306041503080903061b0913060801020c100e0313030b 68
    0x4070038110b004580751104c031004034000d40100040c0400c2e2881c01c4a00c083c0b0b65280c03006504105880800382d010950422060340c07040d40c1201c02c5000500100c9480c1c00d042c01690100c1e45130014400026510000f036002181b144021280c200e10202031203006403951f0058144054000075804c01034030055010710011b1414803414140150707400c449040800c40310f0703090342804e0b409800d010390441124003203a4581a40e5800100502030b40303103c00a50020045000901604000030b66021a0a00800c101168042d240710b0700f0510030f0000715140030300a4a0f00755000c100d50085461450b8118846210390070044940c00740ea85a0340e03c504440c03006c3c0ba0030144c03030302d540f2076600c549003032024015500d06401144103924140e100c05c1004105403c03c1b0000700140000c0d409948441d01c11003180040300c82c010b104a4200b01a00c88071035816004064680291010b0b40c400210241c0d008000101845003401e5010180300c150103e035400c0e61a80140050031060315003042c1c4c28000103060703004042d404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 823622401 1250 823621151 823621153
    0x6041b260c0411040806070e130b01170103060b012304050d0515010e0a050c07020a0902030405100c121505010936050405160b030a0e160611060f090a03030905 70
    0xc0d0500070005040b00c14203003441c0d115800c001070412840d081446519440030b80c0781800d440110b070010100303198075000540c040e038007651840e0101140c1e02440818020707101c1041102c09540e10782c603000340203110300241d09000c166108000c0010700940c400004400d4075602070b4604003031600081c40702e403080c0c2c4503003114a4080d02c8440c5040c102c002001e5802401580c07524038150801c2215001169000b074510184908104500c101503128075140d1000c807502c901005950fa9a1803c01071f040c041911f130601c002da410500380c3c41e4203a520500500355004200400c0000005031110010141080d21480f404110105000c01545120307981d80018680d207240348a410000d0443c64140065245295141080d5108140001e000c4100b001d46140c9150b0f2140001311030414890080300d010003811107240c02e1322182141c0a440080c4440742aa0b07151011103e295511107030040d110303c000e1030030003a084c4282e20002d0781403206820164010074510b00a051140403544089001c0d1a0700c28084e070741 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 823623651 1250 823622401 823622413
    0x1415030712021c081e0a0903080304030c2f0607020a0509100f0f14090603061f051e010305070912020d08040810090309060c03120911060a0206041b26 66
    0x491440300c1e400e00c01181c401c0c403444d50344004402502e180701c000700620851050050040103800d6400034140d0054942011740c603512591030f40b074105d5251007090360090440c00210705145891400401c00b4100c01d440ca414040400b540349e041c0000d0380141000a940100031050412090402c890860b401c034030400d910308580ca44aa40d91103c0c000c8030752080b240462001e0302048005090061448090011641e48009080040019903106000380c0344c5084841c14108214500c1408200c200091101800182d41d8800b04059480000c03199210039005c28280b00000751032921818040c0280e81280c00100711419841e001d00129482101c1c1c11510358000300b0011801c4482001910142281c0f0b00b000300701c0c0d107913620f801460100160310a0303082c84800f00e03900d4006a00038110009407000b06d40d000038214a00d0400c04a07440c6010001c1d50030440004003150a0b0b54003043c1281700e170380220482d1041c40250000c107400300f44036202c0c00a5511611401001c06064490b16060360100d10003101e01c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 823624901 1250 823623651 823623679
    0xe0f180705070f0c15031109040506031c0e0f030706050a0e060412050a02040e031317070308071a10032a0803040609080606091b0d0f0609141503071202 67
    0x107071159182c00741d130035821001d000c0101c07034000417100030300060b0361034140103e04038252000c6c02c600903031104611480c1c4a20000d46240c03820042c1c81081480c03103906800c05440307418060915054484080e014500981d01882036040000c0d40710f04896644c1e642c00c0c40c0c40f4030804126903d40d4500c50895008400300000144a401e880380e414505004030003078010502d10b07204000440b01c031007801454580007403000c0250701510390000030449068a45540d0922244d02141d800c03c0380c982c0000704a917102180070340502000c480c070701c0202e45507010740c03120300c4d1960348450500150b1480020584154100c840c02c0c0d143c03288605030103403c54001d03441c40468840800b9406c0d500a81c00041c00510034050411440c030082143e581c000c40169004034503070401c1110b020740d1200740041000d6500340007401180c80d2a03c1c0d4010024260480400c0049a40380c02c4100f01070203c48061311074145404c80440c07104d046011900f40b03504c40003802061040d161440c02c241004404c80140c0e0b10064021982c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 823626151 1250 823624901 823624913
    0xb0402090a0f1d0114060a050d0c030b01080a0c170619020c06010602010c0e1f080c0c010204090b09090105070903062708070209131a0c07050a03020606010e0f18070507 74
    0x5180e6070300c3c0d1116080d42e900c10303a0039003100d0b110385500011000303030783c03d0000a854401c43d1405507441030b11f417101c40300f4450801c10001e43d901d0b80024900352072500000f84030748000c05c110001c140f246038510707001544d414146400210600c40108150000d8000c20300030410141450340d0080207403005410300d00451070b1a0308200c1d00b68400c10250351a00124048943e008503400f070031043c112000f940003584800000e09181031034801c1402d0005410124201078145016079032041c040100075965291242c00c0704010707140d5180b03881d01452001010501056041c0075003807280340140d5402c40792504e9034403010080d11002012030401403100e035006c00c000300713521500e11001d40640c52040d40d8207020307c1408481e140c0100b4070000715556240160000d00111505161132144400b02d140640f10402d842c0081e02c660301008245200380c0307040e402050f07000300c1c403e889810240c89500000e030491090058070b25482e01e1040d40070f682e03900350750b40044c48540e00c250824401e2a1141c244100c6903a40 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 823627401 1250 823626151 823626161
    0x71706161205100f0b04080a02060901110f0d0210060e041106090411190c1208040302330106020706020a03031a180a0605030d080402010f020f120c01050105030102070b0402090a0f 79
    0xb0070b080f0300072000d2280030402d00303003c4010002860203915007490485200d8035500c1c007040c028807409000808100c4c030b0703200740969103054080d081600d911110840440360b44948d03003180b102c054040c1d03003c0c41a0300e90951003020102c8030300583d0001141c3e11079494010a0710b200e00c14039031100381800742404548075441802d8544182c0b00103195074640c02410502d06103082041c0c801041006d40d1814000340906081c1070140c201414420840d482c0c51505070300b40300140304044170722104406030a0b0481c500340c004000b003514046a4070402c0e41c81d440f080340c40f150b0a01a59002d6840701c01200000382c0300c1e922006812149501001000c0d0030303140003034145034900d1142880603a005060103040c0043d849210000c05c000c07402000d014140005c003801e80c8000800c0641408062201e1030301081c000c0c0000030f5141c1c181015942480303600751034a0074540202c00804120740c40e082c004106420140f003100e403a690483c404100741e944544c200301c50520020300e0303c080251140d0312031026050038024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 823628651 1250 823627401 823627411
    0xa0507080307150b0d17271f1b030504180b130915020c030d1d010b0f0904120c050a1a150a152708071706161205 50
    0x2550ba81e48640c104002e0b10784403218000300c0381c1d140c00101c0400d41d841d0040b80d19516448904203a0f901c001000030032a90040e01412154280d0802004e26401d5083c841c4c0b00d22150308642803a500c0541c0d005800c1d45c030106526980c04100b0208025001ca2000074181c07a44901c00d26005180c903480300c11002040d14025850b019090312003880380064645441100324802d19010100a1180282c40d81d070040494015021045a800114505001424022600a052200424001e201c000100c0f24000c02c220031000456520304401880d061801003400350718440d00070f1002d400c944541c0c551101da011000600c0c0c0500040041c000e00082040c072940d11080c0c0143c0e004059860b10000c0615946001800980c000d40c0b0725101101076a01c0d400030000b9101100c482070740c202107402e03041d64841e01032500400000319a0b00010f00c8103071880c4800050394020b10603a01040c7e0b4800d440308510040b0b1207a500146c200f0300c0003501480140071a0741d0010007514149174003030001c070b020104450050354 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 823629901 1250 823628651 823628653
    0x40503070b030702240105010e120d080906010902120f1503100e06072127060e070603020306060a0815090f1f05030a020d1b0b12060904230a050708 65
    0x4100401d03130140400e14081c0e44a4001c450300074110380407291103031014081e140c14031004045a2069440b160408401401c0b55400c64040d15000000a40441c800703d5a201c0b0a10030344002003011446402990402642080011902e45400d180880074800050a009100304800c3d06504690b40804c2206071811101600280b1440303514101e41c14000014031040500c0310502c02080b9a802c4080800d042c0c2ca03032000002146c0c1c8401002d09490405c040000440c59a85400d0710140003460b40700e0310311103e540003120b040543c0d0701402e80507400708462040e84600d00307001000910b4014020913501c035070103501d180140d40d001c0700000c541da14151400410201c0f840200301c00c03144441d19000860a86204081a40b45403000080d030380c00d4544d0f40280540c0c8110400c1c0100300171502c5040d444014580e442c480c1ca62a81c0d50103500f40c00915280e4220f2044d0700c041029414241603c40c000d94101404202d21501d5400c0803c40b40e51003042a6664403484002c200403400c00c0c0308030700141800e58 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 823631151 1250 823629901 823629907
    0xc0f04120c0509040c17010b0a0803091e0f1212030a020304120e0603010b09010c020a0909051603080412110a031110050309060703230a02030106080a090f06020c0102040503070b 78
    0x1c00c1450341c40c0120740000c0e0103241d000041c84041403c0540701c00c220340c1980c1c0d002526103a076140c03c0740501070008110f80c0012803450085078048000c00a442d16000590344c45030740a440740c4070629400c2c1c0c81030603242c0194851005407842e091010140b40c2000c000c008584000f00707829035461081d40300f210203076400d83d0702005010402103100c40241032440301c0d01c0c220340365540100010b6910320041c4542c0500610000e400c000380c0c5d015800300a14103400030407222038a81d44011100181003014800c440c68011707544000c010055404484d0b05a03a0070101ca60b08042c10203041480e119803180d01920040110341c61410940e071001c0190001c0c0d449904000e0071040c564040c040d44900440c600004d01100b84200b00081c0c0f40001c000386c1c42000ca14011800381c0d0f0301038505140300110807660114441c10810000080441d400071170407201d95980701c8006503607082205080715109107006064403100301d1b0800c0403032232580141c040341081368001440c203661900060704d0400d595004840031780b004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 823632401 1250 823631151 823631153
    0x503160b0f0601020604110609030a0f05010e0c09150402090d02040f0e060915130201093f030c0b1f08100b180106080901140c0c1b030d0302030c0f0412 67
    0x49908203402c0802800200b040381482da82d409501134240c00900e014940c00b088128455408001c2418040c0d00f041c1840d05d03540013401d2441c040c1c107844100050b50310030344030301c051300d8107008446500c40c280303040b074130b003a021380980401000c3d51082c01e0040d4090117180161b40980d94030300c200c4075041a90702e00060000402050141031800c000d00c4d60310140c1022210300c1440b0360b110400c3c0d60106c1402500c0321000041d10040c1d9806200350170200c03844540128000044400034185003098803003000e0050f541c0e000d42c10003d202c0e030b000d0038014005148800c16000141d410511260001210a407480140040e040300e82d21440c1541c2c000380843d4031285144201080710b108441d03074220260b959519141415a010300c40700d10612442c0d0820040c140000c03030001c001e40c00031700c0b0844406100182c1d8146a04002d006410102c60307040e140c041e801c91282c0945010703000c207882590240c09054262001d04081d0000e410040180064202c1000388c1c2a0120300c14004201400004803024422051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 823633651 1250 823632401 823632421
    0x12091006090c0e220f24210206070618141b0d02030715030209090411010e0301050708011806050901090c12110f090439080c070f0503160b 61
    0x1005050b014140301a500d8828072401084c20705100c044841c08201c050303040503103000814844805245003042080000d03100005400024202c0f62a001080920b83c02c86102d00003d0350030050080d44070404004607000510507403c0401c0100d04a00ca055465803641c503017010161221510f501107400c02c5042146482c42815883e11006064400c00c103010801d6000c2640e40c0d00500801d0343c010303641d50301e800c0024071031340440325146000307051100c039400c0500e0b2450760114048020b5002c03c24030000a400380c20144605407103041c075a541c1114592820b400820a82440041221082d490b18804900c4d5103c01c08054000c01c200f242c000b643e00401da500030508000e02140c41c142d2820708051009034000704003039413071449400860702d598005010014009120f03515a00d54549403140c40c2031f200305800045550b0781e01024030b2a006041423600226184a41121400d620344010b100b114081110751a1034106244910112890300c12108020382e91083c0e40c02040710101d0600b4100043c4090b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 823634901 1250 823633651 823633667
    0x702310e1005090705040209060708040902030a0c0809070306110403050106030c0501030e0d0503011401090510031a0f01020714060f120106140403030813050313172112091006090c 79
    0xc0070384020011410311064140c4c03202c0840c40340740c0c8039940210300e100d1070343c0e62081250081a4420b43c2140da1b183e40d010b026010350012641c1e91240c0e072034100840017190040c00c01c0d42c41008104090036a403421991080e0040c07100b241e211720900b80c18003001c000590240f1801b00618090b61801c81001d29040004040d6511840e0035840c940245000f03041080c5c01805681c1501d2221949000c014224801200c0030700e659800141d00c03424026602c002e040c1c05074001c40007143d15041c00c107041e101d03010602509601c10000c00b0b00590000b0410442c1e580714842400d110744009090500e090074400401000303030040c40d41c50000c0b07940040100000754103ea401e10400048001e028202851500c0140400c08020260503c0f080520b588500300042441140c520110b44000b091006403200107070700d400d10009494244511480c5140704c3c5002503600c585066910b40ba07022807038940848200c4c20000c001404855152250852684a00110303005070409801d0951002400200c51358000340446 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 823636151 1250 823634901 823634923
    0x302030a0c1b08030912070308070305061c030c0501091a09070e0705181f030603060609110412141506091005150f04030c061e0e03030702310e 63
    0x1100c40035202d008020640702d50000d210f19200e640b64400d06080014801811420140020b000000c05800114031401070b6111b503410042030395058280041c03c4440210401194400c1c0b00500c0068403c2c1c602e400c1c468480c10000c21403200942d2a400800361411441054035440010001d00200c1040060300404007040140500d0509120103001031241c624200c0030400072520360b40790307910b68540301c0c01420265086a200f000000c0780060003010540000c840803410031000141c0c1516a000710360300840004503980c502490407800956603a03041c4401c48401000c800d0400304640180f0456803a000030100c81181890f200301000008000144107291a0304194410320840d00ca07023140980501a4800d00381d13890054130b0240c03809004a500c020881c440d01040070650742d5100d4007146600002c0d020220011551050945400c00030010325501680140f10071405850811190720100300c40d5980c50340d104081001c02c4100700c42116040403c1515404800740c0c034401000505120 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 823637401 1250 823636151 823636157
    0x50609060c030f060f090405070f080307150c1101020d050f0702060403090315060b0d270f020603040c09020d240503060f04030504180b0f010c080909091c0302030a0c 73
    0x140703041c1d41c1c1c1540a000152040140f0b59510000903690749800040c0414600010b04803841c07450545012030b070710f944034020b003000c0e115060800a50071a000040c1d0f80f00d40d50005480401d81c110301c0111004100101660b0f0410440003010219603500b0f20040020240b9500003140c28a0b220002c081542d40140101d42154420780c20800465400f00703014059030b600120280c1050862485800075102d1504440c040d0000061380181621f0503034407070b6000c0c01d501b50a01611108181100810a644800c0504501e40c2c0d0001d110061825200a6a11921a10b14000185d84442010080341c0041c5080c03905103645029458200e29a101200780203d41c003482001000c0c01c01c00803c1e15904050401d03071540b40084041010980107105540103001551007245103055503007074010140c1400740c04580909515518041d00f54400c6884000c49a04250f00520f030000b00020b016070341e90020701c0e9080f03038001c02440e0401303101070780b0002a554605980140e01c2e41001c0412204035200341c4609024 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 823638651 1250 823637401 823637413
    0x607050f07030819020414130504050303191401030312050c16030503040c031403030a05010605040b040302280b0c07050f0f0904210c060b01030c1e0306030209040f050609 75
    0x10446240302140c12603941450600c1c01501e907000e605403651421380416205130b00101e40810041a0360003018007445c812a40c0503904a141841601159170584025205030000c00c00104590030942d9541c81070600d2080000390421494442048510283c0040b40010311140328240f6020030f501070360f074101c02243c0086240c0304008640d030b0400d41031844c00800348035000c0005400c0c8088040040001c580242e1f0000041c3e15541c00581c803a882121580c030442c0c541400460a01e20440070703102651106c1c000c0620f804d003140c0030400c0384550444440080c242850340b0a00c0c00000380100c138010302401c2c04458a07034419600c3d083c01c0103200d400040c000c914621100005603100300ca1021030040030380c2c1d0500035869600700300480a0b008420f4400f040303230504951854586c000d011300d2800b030295504102c170301410300044042d50101e904007070001d05039203005201b880c0702201c824071051031400c00180d495030f40d070301107045600200c40a482c000300c4140c070107041c014240100386c3e002a00704044c0003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 823639901 1250 823638651 823638667
    0x1207111c02030409090606080312160504270f0f020d0c110c010806030f0307030e090a050f0f09010e0708030c060105190311010c140d02191511160f0302060705 70
    0x254a000704d101d2800481d84910300c034014880e00390b005501400c04c2d803050b280e03160400180b50714082c406954620b5006070f040c3d6001d10491103041074500ba24002c10a1199100e030340c1143e1703030080b414103c18008007070780c0302e9510205030700030300c00c0c2e004219030050096200c484410007001200c400c0682803041c401032440b806902c00c408100180e015a00742854561a212900400d103000e98030b40001d00c0c1480009601018190081d51249940c80105d0b08c0c000f40f9640d00110f42c1c1a20b000380e8040554581c41c2c03001c039600324094103200d80d1010219000107162010008010700c1c000081c0c1c000341450f040000d14074424402403080030b001d0320059079411840701402e48405000380543c44081c1020b00705445042c3c15a2141c103055000b07070782008900d000160080f140315210901c0d0a0440c000d881003c000016540b44010300e15401034000c280c2c810821704140c0c0c1c841c0038004003500403c004404211034074610032030281c218030180c02910005034150300d034a00a0310b081e901401880c14080f0a000c2c102d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 823641151 1250 823639901 823639903
    0x201060f1a090312030406050114010509040903050c0a0c1d0f0a02130509190e0d0e0f040b1804050f0313140d080f12060603091c02031207111c02 64
    0x10301101e001d40032940e500c0207007003200c1866029012100c0d900d4050000c20641880404020710f000e00e008280801050b44e03650488040c5500448006002c190140072200840ca02940103131001c60003030604a01d0100584e00701410001000c00803103800042c10014000041050780c680458601c002065443c1c2c1401408190301a400905d041300907038001444400700c10300c8001180040102904a801605011040d141c0001c100c4103402070b00d0785400442c4043c041e0004041c0382641d0036413946030751412004140311280b00c0c030b00140c0e03420a44507098003425450306410b43d00c400c5c0e10003205104030700f041e2808508095060360490700c0da80c810301980c2e0355070322a90b801c03a0403200c001c040002c4210303019000c078405256920015107001d00210380e1946804e40b1000921210620071100d4a1036941d210410450f1300069a40090b141d00071904800342030501711204070b003550b240c011603060a0007410798010460341196481c0005183c298184000c0c2c0f42040801c16000c89180000101712112b13a0007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 823642401 1250 823641151 823641179
    0x2a03170c06100f03141203070504090c020d080c0d0603140a03120b1507050c0d06330b0309030720041103070c08030601030608010e01051e0108030d051e1302010e01020106 75
    0x340c0008852807100a218904102d44444541b0010001ba12468a071001070a5908180300300d264503810701600c01505480801c0c424030000c400d841e50803281d299074280750410307045a080340c004148cae908000b0001c2060070f100c21058424640060403244907a20317000b82400d40e19981d603c0341d1030400200d401255503010360194a00d510641240d150343c89420304515101051241681000480c108a0f0511880d0303084207002641c4c40e1240c039048101918034210011444070420302001c8090307418001d01c0076600c000e40c2c001c241e000440b402c0c15201c0c0c482440160040302d20300c01e030751650141d848013070500d4002d2149600101c1c44050541c5071140c00941a080e400d02c0041110100100041e034681c02640b00f50064404500204a0300900e8204540200f10a46640c043c01da24524651600200c1d06503450503191900007071400c00f65040e010b400034204c0a80340b052035017500000001d9500070300c0800c510070542c4003c00da0360341c0c01900000d8000c3c0161401c40c0e04690600e0020310000d030a400344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 823643651 1250 823642401 823642403
    0x3030309061605070b0405060117030a050304020609150a0e03011a130902031903020709060f050d0609170705030901030f0b100e0325140105072a03170c06100f03 71
    0x540b00010400e503900700e4007449410f6000b804401c4030418842407100006026040e81c0c801000b03030428a10918080355030340503e8000da00000c0007000020010b003400d40140003440c0d00a8043d801da0300c2d0300c813191442074002000c00d000141c0c002c5660101860240034802451a40280e001d00c140c0c0d594000c41d921112083d440c4c0041519443c00303404549003003101032031143d941500c0e00380240d132501c0d0003522440c16102cac1d10b0b0064107010002c2070801131442100211a8010010100c0603102e550b0345002d0301340a00251403c0e4a200311000700c250b001c000403d000307031092020b1a03440100b500050f045500d42151000072a1a114030102d00c0d48440c0f0202480041d07a00341503046014000000e45800c05500405202c41c1c425062410242c02480d04c031800c0e07405118007400f102c4040801140c050059001c0038002150010781420665105c0380d041c040300240d41040220742d43c4903200c84075620303034149242d070410200140c110745c0b008080c054950417000081c0010255840c064444840d03282d41c2c08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 823644901 1250 823643651 823643671
    0x3170402060403260c1b0301140105150f04120501050f2701090602070605160206091b0613230409050c011407060c030501030209090f060a051314010903030b0303030906 74
    0x14003a030700302400c29580d044c000b142d0085107658500d1010078940341c20500c1424290143c00703045401d01841c0602815151640000b5086402c0e03180804012460980b10b2010311428400c0083d20b0210034041c0040c0058203000540c00c020104c6480d249003100e00040662072000340d03805c20f2120504404608005600d44500301424004090280d24018003881000601442c0300107019410080103821007441894010408040c0481e102001e90725640e00302d035a201590050b00b17070809940c0c0c00c940c42c0d141002c0c01800e518108100d80d02c044c44c07115003a4000b5220045002220801d080300b482c0c52219512044d201880500b49941c1da142e80d480100740420b05000040c0c0c9401401d4070034009031a0181d800120900050030040005401443e007070005901400030701001584c0804001010a000c000a900405003a601c01e5030140080070f019004816010040c82100e0216114a004100100d65240000781c603519604d4060215094605514080d4006204109101d000070545a074000380ca24 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 823646151 1250 823644901 823644923
    0x40510031b3504021c030203090105070c120501090c05150915070b13030206061c021002070f0e01050f010306060f08061503091e0615010c260703170402060403 70
    0x1128040182c03041600110440400101070b9030440c4074890301c140500d00a440c1e5822882d003000f01c0f540b8031500c444004c4e015a00400600f4015441500100541c6014042003015a80c42c0d010180d00e0400d42801500c190303440f0312056040c402002c80b59401803408503514070322100d0507000102140250800241b03d4101d46c3d43c0c1c1144440b0500488a0b1158042d500d05170f10b103002d246408401c8811038061f4018421a1300040040c1400c6003407074554440880260341d00303691542001501410801d124085004138040040c4660b0100d01c181e01900300d2a554400a60515062091884003116258105401d180040107100d80200756081c40615603e4005015900d01c004144160b00303080240c00c040c000002000320400700070840d00291502c0c030142c800c800860000c030036a00c90041e18440c02f02c00c0a882d40200a44c0160403864030180728498209401444280c810800b00d030441403110300c203100040403410168841c10800350114146240d20890505401040d281d02690000a01c8401c6103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 823647401 1250 823646151 823646177
    0x30d1d12100203041a071b08030406060b0a09050102240c221d070306180209040b04140108060f0405070603111918090b060702101e0203040510031b 65
    0x20301c2000768a200010056580e410b05117003481e05000c02550089544a071070010410080c40b0703e4410030444401140d041c50309485803103008482c1d0002d80308503040e42e0340352070005800b00c0d4040900040203407a1a0302c2051032a10380061b0504200b0842803083e18641035404a4080d18203d099800c107000454180c0c84520401e0355020509aa0390801d510300b0900c10002030400040300c808421070044034203144c60343c41e1400300307900396912030080411014a0403840b80020110b0b07400f07403100040c0104040380390180308000c50b04580e4500d289000c5104a01c00611040b10b00304a9550050004c0010b102c05103090707103071507403100041e0161108041d1100c030311083c50a1a201030313908806c9446425103a030070000d0405088851522039030070940c810300c0f0000070305035620321170301010703140c0a0403d51415110703500b0441c860400ba0031400030b100059410040c1c03030482400070841c20300d03542c00a641c1d40c4d042c0f07000c012070900d0035884c020400d800d11000b024030140904804d00c400c49142458201e800c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 823648651 1250 823647401 823647403
    0x6080609120309120f25020310020a05070204050c090a05030604030e01080c0720130209060d0b0a03080301090504061104150c03020f0d0801031407050a12020d14010b030d1d12 77
    0x60341d40c1c4484d01103000444281110300038807144079030072520a444211440104070401c66100041d5040d04210006848100203400601103034200d0301c0e1040c5000720950008040b550280c4040d8000d100c041954141c0c0e041850250000d8203085008042e80e191554000f82400c0c8070742c0c0081d04112141001c1240c5055040907a02c64035404154803c82503d800511004c4800002d03541e80304103010107902c20751030a0703442100d0003032001030600c07031411070380e150003c003d014903410039600065200800404a101c413009540070f40218280030460341002e00b000c905a0700802c4006003d4181040b00b0019030707400081c189400b14143c00c144c410030301c4034101a810320752989403c3c141030151340300c80d2540300d0307004051710305a0380302c0c86001d0074224182a5265880707425005254000d001e408051110780700b80c0c40d14210f0b180c8010440914028655903030b40000c420b000c446400342c0c0d100d076020b001a14041c80040c489540d40c0c90402c0c40d90000c1c15101c910540a4140a400303040000625096090 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 823649901 1250 823648651 823648663
    0x90a110f0a02030f0c0307110111100b060921010c1404270e010b010206130302151317180f100309060b031504170a02030717090a0905090106080609120309 68
    0x10494030071515003440001c5641c4947c003030501103803c00c0c040340000ca440e41c02501a4602502010001c21583d8404201c900007400b04140c00b0f0b5200005000310000c80d1749004030800300910b800850300310f04203004400c0c1e0959091380711980900081c0080c13001c2e05181c4106603000c40341707000701290010b10b85660b40ca12001d07190507403006282c103052001c14117201c1500000d15801d03007a801c4074155070f5583c04011100d0700d806401030040c0c1144c0ca020055000f200c1c220703a04400e07014000720704041d080e03403582d09a40400b2410f10b01c0d40000b04605080300c600d0100d0320302001e400e880900010603400d0000d002c50307014003c00401c4c141d6400e5500c050008a50043e4011f20020703003182e145811111140400700001c58040310040e0001c0d4411484401c4803054031a00207040c0c00841c2440c0303450b506c1c11102c1c0d02d6080084160507090281444030b44d02c00685000401c0800000202e50418001241c2036407041e400042103039201503348600310500040100441c401600c1d1241c403a201c514090303040c08 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 823651151 1250 823649901 823649917
    0x6120b0c12100f060813060c050c0703120f0f0207030b18150103210804080a0c0b100911070302030702040b150301090b0a2304050406021902010b090a110f0a0203 71
    0xc441030200802d030030a01d0b107100c0c1502c280d0801c40b418540d5411040768403100440e08500401002c154120000e552500020418a2107051803400c0c01003510b00715140101540c010381e090850304d039103023740c01d82001046c80314042c0c502e40340120a0303020102a6a506180c400100480c82d554006001c040914680111041d40075090304c12003c03d003c0d503010202d40a000588400b10164041004800150024040000c1944900300280d81e251511403150b0821020074080c05050920900002c02c0d000116105034203100d104403415040150319411204001113061030342c8000c11480012a8002098a0310755074100c40105543c5100c030f000c600b070403880b5100c8c5181e44802100102e41041c050b0020b45201c0030a5805c4c070300090b0740e82440409048002c5941004190014554500d0308007a000207a000303001e203802500e003d180d101224075a41d2941248030040c4d41d907021380c2c8443c0c901520030a07006160504140510340b18241e000400344941b908403e90003c0c005003e060190007842034903c0307a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 823652401 1250 823651151 823651177
    0x190e011221030b1003020927010b032d0f01050901140f1305010f0311060918091e0a170c1905011808040302040b0306010b03070f09081002190306120b0c 67
    0x4184c81007019019401101e00e041c0314400d500b00e0312031423002003000c03c90914000c00342d8541a0b440c1098082040e1710203013500c2040801d0200d4a1080010213010b03211040b00858080c2c03451902e8460589290310603040b00744581040401005050140b0703c4150205004541103101c980b110070008000c0d103400804460b0107420607000042d190103030702c900303411039008260301201000c0050811042d403082c2c40905512075480312081c030320703140c0c01c001d0180d0141c460800c56006520304850004542d0314a1700310b00c00d940c4515140d0f0104004010300c54103021011a40314288049404140c1d200e41f40b620a009a00f0786403246a0305020007501301c0d503480c0c03040041d0390000f948a4106608264814041070b030090b814101c10100905000507424101e5410004841c21611001000c440a40c0b14082800c20030401c040081440c002c01c0c0000e40100940348001682c440f01e00020017150300c110b0a140050501d070900400458141e00c1e2604181c0b6885a1020000e03503078030460103034500a82211403c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 823653651 1250 823652401 823652419
    0x1031803091719060506031002120408300106021203011401051c0f06170d0906081f0b130f0e0703050a0e060a0c090503120412050c190e011221030b 65
    0x40c404594411790081c10107030169105111800750003016445580d452601e60f0742d601d0300003808134445802410050710b61440300d601c0402200140301352900c021181030520403185004004e80ea030100a170340071001e003035401a0304541c903101400400e1002d40e08902c2c1840400a0f00c0040c842d210040c0380885041984104003000c81c089090008000c03d0090b03414040485042001032040001c035002c003801c41d030356482e1510741000f07412940c4400140560802c1d085aa000940d074501008144019026211449480d000d60b580429117131815a40301107000050900b06004440d003003001207034440c1c1e2a0401140a07148d944522004100202c030741801402850184205d03045103400920315200c0c1d03542e0307500000d40c540b030405445885040300c0440300340041000308514030807018210400f50150702a6080102d0072004200c43c90a60303a004030700112900b105100c5282c0b44031601c2d001d02454420031244108030b43d12440344001940d00d0644e441044d4809100e11b51090700020800e010180030002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 823654901 1250 823653651 823653653
    0x30e06060409020301020c101523010c05010b0d08030a1401030506010306050903040302040507020a02130e0316020411280c02060703080414030a03140c090a03080309121801031803091719 82
    0xb0050032040c0c8110720780a408280040c40c043c40c85418240c1d906404414841c82b09110019180001b2039002224030b55285c2d608a2001e9444481003c0c01c01d005100c130f20350341d241072081581200d66414901404490610061021401c0064800c1c152070f0b000d0000142d03502c0b0005254035601480c4d10007503210303003800704010110b0740c041600c54401d07100395070b03003041000d500780c1c7d240944100101c665840d5009001811a008002050203c02800a00700261030071559003081c0c01c1c6e50149850001098040040c81710040c020800750001420030b15250800307804660002d030b0b10384990000641004440c40c00314083c40700c80b03102c01401307400f6107003202e40d03400000b080500641380f809185881d02625100041034240c3d98001c07a0004040100801c10550440c3e4808495800c0031301449004c1c41a456210035001d003010084c440240d0300c0350403600c9031121030001419107241402c540c107011107540c2c01c040020341122103201914031041d044c14090142c2d5140703c0ca07111840000d02060003941c40b01c64 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 823656151 1250 823654901 823654933
    0x5032d03010b1c0c0e300106080d0309020904030c05011d010c020d0c0b01151b0302031b01020a140a1b11030c01081603020d0e1c030606030e06060409020301020c 71
    0x3100b0094988070403c40362035030710041c0701181c41c2c9000040101d541000482507a203031440300c4110001100c3d01d103030b043d03a1401d0240d0405000c2d1000d4250a603646410a00c60000200095040601382d8681480807121300c0c0c0c042620807402910050501105030030031030805c00290007000081100c801039040d030358400064940038040c000e403e41c001d40500c10049804502c02d003100c5801d9500703c900c0c02c1180c2d10300071611050070028103080042009101e01c0380740f2421400050780103180a5801180c031407a040003a04451203030449039690b02e0703204006074508241c001608243d0020708100c015150b2900090649804072083c20740426550312865820402c50040c84001d0001016001c84164820007001500d440d4400d98140780707c04013412814482c0d80c03103900100311071000100e01240e01d8242e400b8042c6070400300300150f0318011a0022440c12194035215800080c18540f809201400d96200f44a03199400541020302968407000e110040d501c09404982e03485040d48100c48214119100700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 823657401 1250 823656151 823656157
    0x9080f0705060402091003030c0b0405030c06100504050a020333130501030b0915040602070c0314011a040614042c070602010608150f100308041d0a0905032d03010b 72
    0x4a202c1c12000000c10706e9401503003801015a585622240d81c15211921000d000181c01002141c0c14882000041001d41081c00020b00448005940418660a00c0200004d40d0380041402c0b03005441172040001010701c4403111b8000401d001c12184000f220640c00d5005410070443e0190001c0c0c07001d0446c079140045510060480b0f0240403203403140d45440d0f0260703440340c00c003004003800203100746d020402141030356004043d400d10031504403080355529a00d480000008030405d010340d035940e003001e100c0c1e01c1c0c50500c15901000c04940400189040040c003e51074007501007040c0c0541c0c0c0d81d40c019403083c403214010484010000e00b80512206480401030340d01c028502842e0300650074103000194805001451040c41390f20580088040d598101c030303003941518004c0502801700548180000820210001000580200c00844c102116010400c01039070748054000c120b440d04c0e148840c00801c0011007030310202c0c611320050500748181c0c001502244071001250300d1003007a00000000710741c0148001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 823658651 1250 823657401 823657403
    0x806060d060812070c050904080a050c0c10170f07020607030e0c2e08040206071212110a020d0809030301091d0f071503140c031801090b0702070807150309080f07050604 74
    0x45045c4458894040c802c80090545000b4130944090011001d002c0c0a4000340c01c0c44051402100c1d02e00030000005500c00b0140c0405102048801d00081c2800510410b4a940900409841c035800d0510130305c020b40d40c01e4001c01800800d966581c42401c800000e010208101c44028410304281d41d00700c04083c0c2d800101e1114081c04c02410003c50f070102c0c0a11215031289800600c164100405e9896815204207585200720030404806000c2805c146144904c20b0441e00045050342c4411040c1e4020346002c1c641700320b00c014800704d2000c01080150000c01c4030305551100700c3c0031544030001108140080d10300c4156900704e016001c011598a10300240c202c00702d40c3c00305580c001d0000020415030445594100c4a0b544a156400040740ca05680c00203641100f09080004da00b220b4a601d403a007190620503040791191886400d2010481d8100114005821410003030130b0103600d13062004141510804c10401410344841c110750511050405503034500c0e14401c005a86d40b422460040d4440b203080710 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 823659901 1250 823658651 823658663
    0x5061201062408070903021903231621030309021003020a02100204140904031b14071d0a0b18041101031b0905040f11040303020d030b01020d0806060d06081207 70
    0x10810500b038491403103a80207840f561100514a030441d000e00c13015104e4240285d4969240290001c00602c100c0200c6080c0b40c000065008065100703181c4505000d00404079030030307800348a8418010070010307a003800900080310310002144581c918040c2c0181513080b00c040d50000440c050140d9440d010340003032034110015400d4420402c2a9000707801240101d00076100400c07030200d00d0700740301d043c03400f616601f040c0a07040c4200c07940c80540d00c0c80340c0480520349c00c03505144131004402d0b9410080044501900160100040340200f800e207400b50844010b06e0003d0448d110140c1c00c80e6925001103411510200c0b50700380e1b0040c078041c00c1182c21105000600750002c1c0c544140041c071501c0d201d9071003e40366510707550030f100540380404200c041d05000c40d00081c1c00d90f451505015550341030300104021442a0082d003001f41980708003804841d9402000750564101e548200310380e952011480d9400541100c1907912950b031448200010312564100e14868070074800800100e000c4000a8104180300b04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 823661151 1250 823659901 823659959
    0x10090504200301061410030f0608100e030306090613110d0509150610030e010204090e06040b070801031203091e05010b0f0103140609190203010b07150903020d030506120106 76
    0xd402c1c54200c1d02c0611030f1a0200c42148400c4039140b40c035061503c01e004481ca00411980140e0041c542102d0f140d42c060000d692081100600421041c000c07401200120782c0070354103521b40040820908200101003920800c05507249602885d941d0b8400c410005512040c2d070b4880388c410030f010000305070950b2401c009101e46c3c58000640d0241e10700c1e0364420280078003ca080883d071a0b40c140c1c05490214105025035401b4403010030048600d10940d06002d00e05070090481c1d0902d420861030441020300610100210a401400402c3e44032804c2c8071150701c645070014000d01035007448100034008014109801240540c0d44060050540040407500300c1103403100150501480107400b103804540042424451910000d4021b140c1420140c0d8004180c1700b200100c400c0b05c1403c0c2c000c0703070f109800c01d02c1401e00214040041c01241c1030b420704405504142000f85402a442c060f545001e801c0820040580300d0001900c1511804200b00311444141e0003800b600d6100c216a56150a04000d600403000505c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 823662401 1250 823661151 823661213
    0x303041b08030715230c072a120609140a0507140a0e04051f0c0906090509161e030e0c0301060e0f060415140a0816060810090504 57
    0x40121141c1580c0030085038040c0102c240301d1000f411482c203c5003100303140188003150011602e1102c500c141d41011982e1f03940c4c0f84514160421a2080c1540d2403145200c0c0000882d60345000b009100303542d00c40c2c01c48041e460741d82c03074010060701d95280020200702412040851135000015452200781c803c80a0711480707a1183c9591489003060410a41d01054034602003098408564503950040d0290083d0390f0060b1400038200744074601012030501041d600d00303801170f10a50182d5a000a0310035440e011000619203030014528600241400010801100210030400c2c0030f56003a1460683c0d841010b032034203e000b84040e00401c0000b11201c024080c8548100480c0b40c107102e144187c80016050290940720100b64540c409002049203401540e101d600000c040c4a5900381c02c01007001c8910300c601048180c0c20b000a002c216070110030142d010072010071010800400710b50982c1d1051800000f540d0b1092180300350038000d42d20404025241c4001d00041c0000707507035224803c4289580220001c261 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 823663651 1250 823662401 823662403
    0x3060905062820070f050d0e01080f07020c03160504060e0105150304050316290c16030309020619081302010c0807211107060509031c09080303041b08 66
    0x11000034000b030705208950b0100c441d581d9481282508000900e50480d050b1018001c4010f0740420f50603141e0034042c2462a0401c9000c100040d22194149084d4422442c800000b0303001010261241c0044107140001414076482005600e40c3d0794001000c903801c03800b040081306842440d034000c070b82c080c6082c0031000c2a44860300e07101c103040301c40c080c2040c1c05101c1610f00c5400c2d15000900116654001005010343c200d216102550704240248800e003000303064002d0340600c048131055450b06e200411404c200380c881e0840152082d14100c540c0d103410a80c000d00d000c500404400d90000e6100f0404940c2001b141410f00c4103208512041c0c9480c196903e900444081542c2d10110003800200d9500b10480001c0c0c160014080301880740b90209203c1c1203500c1c1060301307640b0781e8070383c10001850b105e0641505003003000b8407801810035090007880e0070124004252140e01d140213808003092042112940030340319800303000050201c81c00b543d07101d041038541a100030050603031800b007480c82d0003004291020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 823664901 1250 823663651 823663681
    0x1323041e030810080a08040e070c0b010f0608150a1a0408060108030a1b0b060d02010512072d1407080c0304121109071d0a0807030b09012a030e0c04060306090506 71
    0x140220103107041512301003070b010600900822244c100100080d507280000c05600240e40a0320710542c120110f54200781004002d018010403500c7c100c94461440d8105882c0c91102d1425560380d00308040e40301e00701c54506e07081481180d00c4040c07030348100d5000049000021002e480c01d0401565990079840b216120341c00050f00603c8007528260300040881c5491a00c20305c18154541b06040c924107010403100043c0482404490b40d102140e03c01001d985001c210f80d08591840002000514400002c500c005044030707896034019000140c00903c0030113100402003942c030380380200e2084a50ba01d8842d221404400030150045881016081140c01c1034581001c0c1d1078454401c0b9603584a000e00e903004081d940807407043c00c450b08070100950100f4030000602141001e18020300d49109581400c07150182110321546409407860142c071040c11403810030018095054105150100c5e1040209500c5828059102180b950007071921400204102c10b907001036a10381c1c09001035411950350003041a90544c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 823666151 1250 823664901 823664903
    0xf0d150e06060a0810050406170d050c03070f0204090803010305070f09060b09010c0303140a0c080a0b06090910120c03020102060708101205070b070f021323041e030810080a 76
    0x2081c2070050043d0180301c0c0c3c400310740c010402c00c0b540e002c072176a40011504555141d041103101042c886400400200c0411a00c0900882850203920341f40740c0580f03da80328051220300504214001600d007066548a41204207041d0300002041d45d0b959403403030f020390355a04034450350600b10185800082c2510781803040e0300840d41c580f0306162070600900c004442c1d001c4800d004400b07040d901c403061a00300036554016880340c60103481c0000c0b003010749070f405000504001e1101e04200d04090441d40c031900c40c40c065540d500f00941c7d0301c0c0c01c07503244c418810f5404221a005180c031070040c95801c0c002d001c031040000080f24000e8003a20510b468001e01160030700022109600c80103500702b01080f42d19003a2400c1000280681d09a03007005403030b0300b01d030f0300c07103038403015060340c3d11103c2c060f101c070551901e403034203290710030b003202042143c0d103003162030000e0a5015045040102020000040a2084000b20044039000d015007507100340c3c84c00d18024201c81c0080ea03031900007068405d4049800c0100180241c012 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 823667401 1250 823666151 823666159
    0x17010c0f020313171c2102040f06030209010504120b0f1608040b06060d021c1404050c0603040606091407030e0c0303070807170309030a030f022506020f0d150e06 71
    0x1810059590342c1c844084401070050b1040803010500c0081c042c00c5e0030900c04859894802200c0d4030306080c2d6aa00d400d0600c04599441040200070414070029100c044500e142805a1506042c0c401a61680140e0f0b0150b00703401c5810100300300b080710301c3e45c86902c00c2a207900c1001c00354541c10801003840c60000f2901020070144008140842d82208550f51f00c0701c4010709a03890070620544050030380c3c11444000c5110031541c2810714284031207001c1c09040c1c80b0701c41c1000780b80341f41944039030381e545400358a00c50003640300002140c24052103412040140c91400d00078401070740c240e5284d03130036034804954560020380740000c0c0e00b20b4030402003840400720754000c00450401c011516001500d6200b164100c0b984018440d0f01050700c0005000385205400c000051078465043c0c00000d0103071200c0d03521a410040c410000102c2a1101c1d0704a00803000e942c41d001c1c4800c503014902580244140030061b50642c030041240310800d181a00920303220303180e000700000078070780d10230f40440644405e417191640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 823668651 1250 823667401 823667437
    0x4050a03140f0d181d071d12010b13140a020a0201090b07051216050a050d0b040510090e03030112060218030610080118020d080a0e0a03030306140904150b060417010c0f0203 76
    0x15103446550035140c180071805144100b50040c3c0c000230811202c1200356040c0fa5101c400044003071505110b003a0800305110014451068501c0c5104100c0900800c40711041c0e9022648042c240c0c0b003503000c1945035034001d12480481c1040c020280883c1c000403043c3c55000034050000700f441c02c1d4580360540e05603d589a40d4141000e100b810b075034a8104003082460256556109040703a03480d40030f414080d44001211a071950b082013003880c141c9071038000c051042d90042004101d0007814890380ea1340150070000050701c0f124001c1d5055000322521100c0c540c1445018140074582ca100c10001040303840540c020043e0010340c00d001481e41e80340d4940030394402c031031a05210204003030900070800b250039454a40c00b109240300005002c03203002d800580000e0354030501848036100140d16140044000c44001c0700e5480c090340c0b0f4111120749044616001074844d0310f6082c182d00c8600503980a441030b241e103401d0841c81c001d4058024001c07464850001110482070041544c0040100c501200c010355000c49 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 823669901 1250 823668651 823668661
    0x20c0f0f0606061c09060b1c050c090c0d0c020c01020d1b020d0f060603080909090f1e0709020c03130b040e01261501061404050a03140f0d181d 63
    0x1405400c89102c4019440c0c12407200c1000c81400e1249101c60382c410720001964500e4002400008202d1140840404408c022443d0214100003800518580111580c078265134071044124035502440703c800384102e041c12440076840b60003040c031384c140704404c0e421644681c2864004a40500210380d03a5400060000000d20240c200603003c0704400b8020950080c9400d101c0c0d442d202203600325402980e04844c0071514200710304d490440b032a00300b0170000080030120101980107440b100001c0c40b000001d40380c088403683c00700d01404000000c00c0242d60440d00d400b04154102c3d2aa40325030001e880c5680410b10114803503082d1400e0354181c500e00354003055141e0034002e4a46042c42070380f000d034582403007409840182080400c11a0000050903107821400d5140c401c000c0c0c42c2c80f141b102c600c442e20600f8402444503440c0c41a000c400c0760b0300950701d072707000d4000075607810304210b100c1c0801d0246003d5401030184054001503416503031019200800715031039440e00c02c0030000b800002c0c02804201d0314004a0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 823671151 1250 823669901 823669909
    0x1b0809061303050a080703030b040915240305060603010e0f100f021204080c070e13030315031b030b0609010f0311192c070215070908060a020c0f0f0606 67
    0x40700c8505080a03190209440c0c1c2c403164581800c10008507070600c0001050001c156260060405801c1c040d03c0074441a4070702d513100c5800c2c0840350380980d4915541c42e6071500004000c6000b05003599590002c607462601d905000341c0b669001c64042d802507007004422009440c00040201c1c0304840c8801400f5090403021111b806080b0381c000841505400344401030001c100c0748040c0d0302480c441e030600c0c2d6548001040c4c160801005601c910260585a4100154007500da0003400c211941490f000402c5400303a0700084240c01c5940002c0d0840c1c014990b05412a05074101c0074056074050445815160f4805081280e0100c0034061119401c40440c001c2001400b155a19001003030001e040b2803c8280c014010040e0603880d6000103007a80c0700341300d000c90303d100702e03002803122034000581d00040e840d003c94040d40da101c101b03200c040f13030208241c002803000d8480c040e500301600e4544242d9805082404801c030207504080003a0b480d03802030000242180e407001450a8141240101400803030703658500f00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 823672401 1250 823671151 823671157
    0x40606090e010e1b091f0306110406031d0303181513150504081e0d0c0914090c04050d0c0b030405060a050c0705070e06010e0402120a060e010b03010e071b0c061b080906 74
    0x1040c46c040c01c4580100c000340c20b40c010f14000f00c644404030307512185400d00c000c0964460100052030900c113266200c0200340040112640403020040f240e151220142c10036280c10b40c1001440043d01440080c03004a540010b0401c8141d070140d0155011010f103283c0da101101c1c03094400810f1400b007044107540c41e031080c2c003851400b46a401134850074840c0d4203a07100180d0388244d8051001480c444c0c400d12424299401d54a0342c1c8030162400f6540d8a0f002e1144280d0344a60b009043c400c1e41290b0271784003008074400e5800b02a007008219a6102d007400e182456451905480301900d260070080007030b0311155040103840096400500809000d4508005005e00302c1000e0005410010b1031050f040c0d9548607400100301442041074541540d15100c0074241c11510250407000c0008000c0e80100503040312503064030305407500900c00240c1920740c900c064862242600031400a40c1170b07001e03500700b44139281c2c0312101124015110704041d20740940940480c7c0850500003000501c080c030606581c0c1c240b000c06 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 823673651 1250 823672401 823672441
    0x512010506011e0503150f040903080603010614010905060f0915040305100905033103030216080a031e0e0d060c03061a27150d180218040606090e010e1b09 68
    0x20100d0304200803010902765030542200364040b034400c205020613810300740710300380060030400010044d00110720b0000344518064482c80d403054102180b106000340c5100100d50704650010702c9201189444c0c03c082d0803542252109035a40d000d2410201040707086030040d9000c5940c007201440c40d00c00c1c15440150034101040c00a410140216030440402e00d082070590043d502903002001d0501d455290b143e5011503903007001e5025004187c0b94000250800d80401003515a40c81c090800c80b119070049800701248200c0303d60101d0695940c405008481c0d11241c44004960303410f0107030743d42b114015003035145180c58520350ba6038104040d500c080c8140d41c00d0f0752500d6501c00e403060713400c5804002504d2845100c081400060300041d001500c00000e105035446140d440380b07540070001007500001c5551080c10f4190f0007a1091200042c01c100950344200c01070010168108001c2c1c00c0200c0050003442d03080c403c0e40a078840c580e0140b01035460240c950440e400d00500311003550b038030624030316910a20461 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 823674901 1250 823673651 823673659
    0x302161406160210020114063c03060106051b07030804140d320708070323010f0e07060804150c1206030609150c270512010506011e050315 61
    0x2000b401030352a541c0307080c003180e0baa83c00441c1003229051401113018024006034070400425100c048400710385810f039100307024107200c11544001ca1a0358481041500085164540200030000c00d5203500900517041d0484004050b40550f01a22107481c0d6500e00e501001d08550300c00d120401010340e02d101488141e640203880031042700f2440e510180d000c407494201180000c002166850340710b42d4150034442c480401801061550b1404240030f403641780500024128001c440c40d440d049462058011007052a00070080041500c40b550030002014244030540a50040190005903588140b01207400f582d080280900d0080f8503104440041c95079141c400706200c01d240e01400c964940d445120021406410003181564141c5007070030344503004052411216141c04407002c0713010382c080035940482d0f50611455050500d0b00040703400d042a82c0d48144e0344005d10fa01d000d0759260044d003059008100a0706d5040b803803501505440c0201c1c1e0380e8000c080000f002440007544100614140d502d421501034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 823676151 1250 823674901 823674937
    0xc0e10020c030a0f0b0c040b071b050316180b01051b070509010e0f070512040f0c0503010908270102030d0203060a0506030408030906180c060d1104080a0302161406 72
    0x803010074100b400c07510040e252a03210481500031703c01010366065110aa2443c030900d410b09040820801e4040c1c840044c040c1022480d111882681404010015190040482c0c180c0840054801d140c0409400b610b2610307040c00c194107580c18064081c501103218144c60b5181030100d44900c144450307409041860b0bc1c0d02c45d11500040e80d48400603400d0180080e0741d0224028134052012954509028100204102082040d40c0341b141c0c61011490304180c0c02500c03a90741c04da2500345070f99004030b150030940d495442c1c0840e9004209181d401000031039446001c05c1c441200c98080500321410f000081c41c09604108000074080c056a4021940000d004160300040c070b495001141c0190007c56048440f4800002070115140040203600c0d0b01c0182e9100641d03894110400441d211190071000b5170007038901003003241c40c0c540a90485c45410b0720b183311581d2655500d00e086d0b42d0f1b440c000c0c1c0c0164058000c03202d600e84030b420200d51513025a04d40384e03c2d191401a520080c014580d100f0450740c50788410b00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 823677401 1250 823676151 823676173
    0x40b1503090717251202130b04110a0201050c0901020718020d0c0905130905071a0708120103020a060c0b0c0901200c0109090b03060406090203031213030306090c0e1002 74
    0x310203101803c884480081010051401610b54400b0840854601140040e0410804074000310f461440056054030144000c15240030850090700c12070800943c07140c11f0130f101c0e0084100000203000412040e500900040d02c40d400000b0051154012042c0160001081806007242c0460204400d0312036880040c94007211740c03101c201f11078400c20464005810b030790040186203040030f62a0b1851400f00c00801c111440c0c0c1c1c2e0f0b007907540c0040c5d01c91583c0040400710100e510000799002d82c0e0340c1c0740d008180540e0359284c0d0410580300c09807d00080303110b004151804644203100b40c4580f40c4c203e038019501d07030403034482007410b00c0305800144800d41004210013094250030102e241a00c0d0310482c1d09c0c0240389101114002400c11411074105c06400c40c5064410515a50001401038205401460000d80b0510600209041d8460195a000d01281c20414450001035003001c2d060003500941d800c0207883c0c0c450b014101a41c05274a01c0400040000c58088280e140010038079aa000d80303801224900500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 823678651 1250 823677401 823677419
    0x14030604020f0d0512030f010803091e010207120809031905070614090d03030e0d0c0503030c0708070b010803040303201b030129030f0c06040b03040503091e0f040b15030907 76
    0x601c9045160050100034808800c0711201f007103016045c0c12016604140c5218040b48030606914240d1003000d903028027104269000707001d0b04025040150f80149060003034140518154402107046009201e4648810044450200c04170071081d8000301030540700346041d50854a40002c0481c920040c02c04002d00c08050351107444a515840c813940f07022803420384480a441c10715448032200c0007840b4a051103480001c202208a981c043c904080064a94146003807080090240e00d400828075405e0034000f181c1c160000011300110b0f4480d0355105190700c0c1c03802600d0052003404041003240c0c0e00c88030503520008100c0e240710080760030140002580a01da5080c45e04201f0341c00e00150098190f41213100140c0c00c09000c89900e10307802c44c2c0280300c045440f1020070510701ca0380c418028060000700108040000504c12980440310040641c000c0c0c0b044402c032000c421a41c051154030a13a95542d0460041c00c003809420100380c0b000b820301c40c00f2403404444d9104da600c000e00340b1501d4054160003042e0090 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 823679901 1250 823678651 823678663
    0xa1514031602060f01050a0e09010204050d05030d0b0a0e040b062b26160303060806040b1e0f060f0303070605070f080106080c0d020a11011d010614030604020f0d05 72
    0x6521420380401078440a01900b842000703809000c240d505040140400d0300c03000b240c03500311404480704510039910b074240580207002e2034020644c49a000b6180c103041c49000805840c2003403204a0800600d0220300801403850b403107108810024800400042c0411801c41c11315900c03100190030030410702507103400c90f5822107400b21101543d0b0725881012041c01181007040c180100301e40200c2c0c0c0c006106007940703c02030040c565600700e100c82a400340c500309446604143c2c0106a00380031180d042c202860000c2101390700716403440040d068804003003124501030f0b0102c0d0040c030380342d0000c08080c3c4400c0240a507622150f2011609132008000490014065110f01c520232541d5a495030500184040010450441079109804000c885003e1100080141c41181c0ca0340b210400c006948049404082e41c2c0400782221120341546031001070020180410114165504010f0007002181c2e00e031040685210040c4403501d425510990028005040a150b45105110003c06e0360242841580e16207140607 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 823681151 1250 823679901 823679911
    0x51c090c09180f12140a030204061d090c0a1701090e0c01020a110f15030a0504121416050a02060307020a03090914040308071b050a120e0a151403 64
    0xd03403844810010a001840b07050661405030594403420007054551003401001d500d40505012165101d04403882d0040ca07500c0d220322016200c207500c0700b0030a10040c000b0f4005103c4d030340103e01c1101c0301800c2c6590b00202e80c0c80c1c140004140501c1c0d611241c056400c0c5401401c1801e040c000d060448140e8102d603040610700801f2203070300205480d4400000c0030b08005111410b54155404002c1075000220a400c00c0054810260307a0080b001300808001000819906050050b04100105010500026410aa206d64000c880701c4070500d500c0c030341c12180000180072003042c1c210244070b03610114200580311a00c0d980641c0484034152003540010b2841e0380b00707a66040161b800050100101600030700010000c041c030b031008210300741038450661500c22005000038208524440007030401d40c000d4058020310084e280b0503681301c1f0003902d81b40e43d968017510f0050720310144004052031103501c81e01c60800302e444c014102d12549850000810740d6640301e41c1c1c044040c04401c0c4814007084800c000650b1140c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 823682401 1250 823681151 823681163
    0x2040b030405120310060e03120d1505060f1e090303041d090307030e01180e01080a20150c07270c030b150c070e01081f050601020d051c09 61
    0x10741801c0c0341c1245040c01030220203900aa0510800460100c0520340340304481c0a03040030810182031000103424040001c00449104601051504940c20954041e0f0403848121041d00c40c0e40d07498100308080c9000d0141d89402c0d0203c208181500d2420840943c0c0400110141e01c038100307a0200000b908540040d04004e0202c22226400e206a16820000581015284000e1882e140c4a034400034141e00d1541c4085051001c16050004100b00d01c01000c0010444c202d010300e00795031181107160f254006454280c840300e61800398055100329509680260380001020540c1102100480c40c0a07030b00140349401450207141e60000b00040117036102103090341e1040300415201001340c9a20110703240103c00004062030002491110381740e440741e2100030031450001549845003e80c03e45c0c0390808942201e0135207030324440002881c4100081e214480d501400c2d42c104000954a099401c03614221840790040c3c0c09030070f404c0041ea0040303000340000401442012001c911001d074030700a48206c07007412521 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 823683651 1250 823682401 823682407
    0x212060c03070914010503072f07060e030601140909150a050a060605090f010e0616050a050d08070831030909180b0103020915030d090303030b060f0a14040902040b 72
    0x4055000301d60b2000781c1498446042c1000d01da1313000038001e01000b800d54040c8504080c59038840600054041410b0105135885c3c10001c1e1720040175602c0b03119507c180000328240c0101d401031480e020400ea0f0585070f1030f05990045021343d030100a41c000c0e000d018408140500c0681c11501e12080540a100d0302070202e004c03506040000005003150f072203502140802074244484c07442556181c060701000902440c1100728008031000050141c03141814102507610301342414000c0100c0808d61404a03801081901e810007a03030300301584d520104489880001d081440000c01030b09000e85070700e54070303155880c070300756143c402c240e204e07800b411225016008100c00d0507003004941c50078012a800060b900040000b1b002031035603114000501804020310600741e0800003400001c10804400100d00c00404031031030000040c0001c0d04544880c00240e001070300345031106015042003800ca4009050104400d4a4003010340f0f4221800d603065000c0c1d4020640401000506c0c111500180000d456003c8a55613 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 823684901 1250 823683651 823683661
    0x10512062707030501141008270d02011517030f130f0602030904060f05100507110a0b0c06060d030c0b040c080d02010608010f06081c020304030602130e06030109021003090212060c03 80
    0x4a080e4804550318855480040240b03000703540705080640003400c152842d462340b050000c9d0000f0b05005c5099500e01d41c032582c40c104003c5503054001d4901034041700700c0c0d50f102075161004880c6441d0604c5402c01a0b41c02082000840050803008019000102c868416031383e85400ca9000071420550007140161300100b04401c661415204900c0140100f864003441c0614080200c2c50b060030790071310001840408a4108140103003031131520100740d130042100c03110b16161140b248036500840700074845c0340304800c000340850034410a40241e0940580b509880300d503803035680c04a00700d40188100c440c1507c41c80c001030b00800030003c0305c0486801c2d400206159042006207821207000b81000c4001c503080000401c1420804101074141000034000c0300200585d120f801d07451403080394401000a4400260848400c032418100c03015200340e000201102e4a4000c01c242c00d8941908003c0e600c85071740715184088501036804000468805130070160385a10130345144e8100785040310010084500001044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 823686151 1250 823684901 823684919
    0x9080a0c05040f05091b01051207200718051f0b0309160302100507210e1005070c090203150301140405060c072006070f06140105010512062707030501 66
    0x210f2403070082c0d5080000d8074200f035005541d00140c11042d202c1c251480c44640c0316074403600c2256140900308041c40720a00348854020000680380c091040790400e030904407a4840c6002c984c07181202c03000407403910032050f180b201c81e0040c80003a0016207007030100c050b040e17409a04c0c0309a4070014003a54191540701d00c1d10050040c1854445444100b18080c0002d0500050b5907800c0700c1a03503681e8038544145c03910403d01d8541800d09001c0c0c0d40301c0780001c4800b0a80c21032944012071950792901610300c800420780d070b013000391400c0c010b03484010f04011103548241f100d00103d034050b5900c40031015a0811414482002c80d00312080c400000304885031031402c101c1841000c100c036a4111b4002c072000c605c0d0191a48408402d490400411100da030951844002141d03101016a20807036002070400442149a02d0894010180b01c1c4030700502c18806000012558080c0056514050988981ca01150384400c10003140b1407103e5590302c51070400c80b00500802e4002d0b5503243c030403025034500190700d50414401c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 823687401 1250 823686151 823686161
    0x307050c0a0b010f150c080a031d0a200f040c030f0212090106060804031b020a0b1b0105010501050c0a2405131403090607120c2913081909080a0c0504 66
    0x104680d01d09585e0b00030340095200511042d4150410841c50701d490590300201c0140c94080508124245801e80b850742c0e101011510602152103443da018030f54203104801521004000c049540c04810840d10861506042e0480c60001243c1d04e000070350303107405144034002c036003054511000c0c42c0800c40401005800074424174000e004079040800c048e250680d8000d10307180c0d542c41454080001ca014480464541c00d0066014002c584505a04da01c8000c4080402a091a070481d90960801d400012035502440407600c90f010018082c000c611f41c103855100e1015010400c0c01d1903e01c0660b5010a40e28551140300e019034299800040710071000d007854a00e420802000c190281c2041080c5900d81d40c52600b111400340e80301c0810034942c4450741d400c0d1651900c90a018000c041d0440704240200d41648003007103d03240380c0f503042c051b68859015804000e00c40c01d82c0280601c44c01c020f00c0050000c0103020030030355251071801101c0c40b900c8407801c41c102584640100c3c0c88590b1080c0600086c5414060 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 823688651 1250 823687401 823687409
    0xb012609070b130810112a01061502100c050a0f051201030303020405130203150f0402120a020306040e0a0503072a060305070f0c0c0513020f040e100608090303010b0307050c0a0b010f 80
    0x10622241b41602c0c241c005038400c8466060200060200350600b031a1000039a500e840c0405000704007240c0c0d00c618030f100c0088412035402c018080d4101100e89a0414401da94406140b60b80d0301c0c2c00c080549205507014541f06004009200050000d0429819244c1a0320f018521a6030701588513440c1105001903800040901200d89006104000d5202c40f070f0081a5010542144c141580ca1101c0f030101d13009126540356504031039034400c2040302044d1a6001540911000e5030104050001d0740d401c00d8a94803540c070f00401c9a0010818480401d0035400021844129182501d0741c4080419440d18114150742c04000400e4550b810056050b8102c1000c0c49100c0c11404c2c039065408039a6910007024201d80075551080010404809040e007481d4195440c41001d0008240d44035111800003183c101e040317a103244c03c038144d41404110507110309481ea001300c00c224021030659090a0040089070001001c9404101c403c7c0000074558100700701045405000b0030320204954104170f0308503104045504 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 823689901 1250 823688651 823688683
    0x7093b0105071b030e040902090a05060a05010e01120222030f0c0f03021809010b0a0b070c090b18040203191a0a18060b0613030309090b012609070b1308 67
    0x4401403e00c0f00c107221140f44241d241c500502c02c010b80c80300040c0100f00000f030294101c0a81e804001003080d80ea405140034140442e8000e15242c0c1d14401110046514071415000949900103410040003036005096154a81c088451031221900683e0440c616913503c08d403030004c0e5181c1c0203030034080ba0b14401400b4002c0c2c41d280000d00c50450700421201c5403003250080d214030602001030071803070084d4401c1c1c48140008001d060310355611100103e03030b074010303120507102c26203071040019442d41c0320b00c90a142d908004d00320484800300c114450300b101400034030680c1c040c0a1500048008200c59902c190f16905c52003500031480c454040b414050f40c1e0091082c8c40c0646001c6d400f05a1408005000005a6001502007281070184011030014000e0300c00143d294a520702c004000c140c0c12a02000948421610400142c1a130200450380c0c1001030030f62042c80d011f15115488802901c100b81076004a00e0350445100b1590b0f41041c05aa50054140143c0c0b0000c09005102641d070a05c1366106883c5914 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 823691151 1250 823689901 823689917
    0x60b0316030c09050f190e0903040f05040c0e0d15020f18030f06011403120f030405150105090a0506010c1515050d05121e0403080706110c07093b010507 67
    0x310100d81c1c800440056244111119140c41c1000d040008403003011f004060744011950030030303051140e40c5ea00315018800304c9000343d460114060800d07106078001e200aa541e6080990051004e00c140d980340800d069604116035010040100183d0000f4992040080c262070f5a4902c1d0b42c004542e8114440d003114826006504032043d141400a40c240c103480304c243d29882006c0c0d0b8a40000d02d0321040320100811500b02065a41d412908032002d50300c00c44c0601c0548822130f0b25050010f40c2d1801c24002ea50b4800f603140e0104d840c440d060ba01c21a4480c40605050045000603140c00030f103480301c0c10866110a49070008503a0250740c0554190051109580c01800d003e8155130b400d444510850780303a80c240c18081090040e00254100c020002820b843ca0159241e45034145844143d01058003907800368100075441100340010402c850080c05468060070400382060820000f4005d403d810a04c01d03071064040e01d030100d0300c1c040b1b080028031a0282003985169a03803145030948000a05e540144014a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 823692401 1250 823691151 823691159
    0x9120307060606120f0e0c0f0f0a081e030703020d0806040f290f0144060906010c0803070f0e060c0105011a131403100f050403120614060d060b0316030c09 68
    0x41c1200120801c0319042c010120410204061582040500d81c3c041902b000c001400c1074007041603502c02c0500d81c0301c00105804130760115928402d00d0401001603122103c100402c43c0703d40000380e0402e0b0014404030b020001510b03080159403040e030010344240c0c500050301d100395840d5501448403004c05d45061481060320701c0064401c0c103000b4410304a8030182e5022520a5500e54024190010105124062a890090719504602084514a004488902c081010340d8040c1ca00040442e40c40701802c4d02e03554a8180c11101c001601d00b5000c244025800e107a041a0703a10406000c10803031a4000159640c174003840300c1c43c0c0101c0c1a40410840c1c0f4100848180344075010107042c15a230710080050010103034a40030a01e802c0c154a404000c0b03c0c5400081203030340e032043e01720790b01460007540c0d03014600d1500140b0508071020741c414015680d01d001e1410145080a10292000b842403545c0020f119076142d4014610303a0080b81d4041d80000b540b1354001c04142c06105502019620340f40c151841428 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 823693651 1250 823692401 823692403
    0x3090e15040c022109030f0f060711030909010b0903100f23061027060c11011701060c171204021311031b070212030307090b0f09120307060606120f0e 66
    0x85807120402442c00248000b02030310200f01d90740720f1f0703421642200c0074910b0b80c1548546440d02540c103580019000300e40c490703013500c00000707940b0b08000c000c01180459103880d62409556010440c0345404d4015040304000d00800303880ba000c07440d00b032000d011448a0f45070661089007081035403c003030710302803410a20180d80c80e070054000c01500d250038401400303804480d008425000140b004002009210004a207056200140112141c0702e581a000410030090056a000c481004403041010300e231030040002c3e91003111400c00d094054031455043d061503201340507041d44201c12601502c2c0d1043c040c0300841c00e0bc585942400706038584208220703001040c04200d0307844040d00c505107034142011200341480c540c6084903082c40d4010508511000032101007034072904100e4801020400e4a480003c0c045056011078001c45009035266280c100c20904100b404009040088020720080c00700d00c0000e201d5104100240401d52901046d094441403a03c1c1584c5d403021a45c546142028076003603039402c4c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 823694901 1250 823693651 823693693
    0x307030510020a1824030b09070f090803071b06020703050a0308070504080a1203050603010b0f10110f030403110d080d09021c0825020a1203090e15040c02 68
    0x28901e00c05a5680c090040c100e4003071a0351495103a1020404000140141014801c4500400200b45901e03040f4880102502103030000d4000e903030401c0b012000503030031a00c40d8201c4112054a030801c1d011003520352007141c0c81c40e0402217046075a03401001981426a040b481b10000600d00ca10081004604543d40c69845104405000703007806204000708400c90300800640700a4480101100c600e507810381001c07610303082002c2428010900e0030703000c130f1000d007418040c2029223003003e0700c0000c540c000d0505010017101a14900400c1090009031380d0710747d0348184000109100718000854660b401d5003801c900003c2c4400f1800d20034030f0364890311000554880c05584d65080074600006681030b0350b00109808054004141e40c0809000704204200301404000e003c42c1c0c0d030a080d003a0020100b002d00184102c54824020b03500803403007042085041c9540c2101c412030752003480c200d00d050b551094411080301042d18900a03031034801c003900a050400b032003400c2c0d9540c81480200078100003114402c003580 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 823696151 1250 823694901 823694923
    0x20a09050a0b0a050403080a210b041d15060d140a03081e0f060103090503030703140105090402061213050d0c021008071b030c0803070e0a15050306010f200f0c03070305 74
    0x8000440c4d044148c50082e411800b5004030f01c817164860109015400e030040056080c0e5621036840e060500002c003c450f45d00081207481c18001b04064441c82c0510b4200c60743c001c0c40030360301c07420f00719041001030202200300b910440707000001d007044402e070720303000c0d21a504c01004000302520080e004035181e501605000e801210581021410380c8440c00103c001d424807400180440c1310000a1140c40c6905a112007003504070031002160590300c2c0d001704000b114050302c0282d0f0080050203c0c58154a020080c540c106204010050206040b42c0d41c05043c200703016011400f00d10155000c41c04d60810b120140e0b07200034180341c550b00620703200b000501801003a8544058501750f00c0f401c20100350256500b00c0c01590058002c944901d0100802041c135100510860301841c049500016004c502800c2d021280006454850859642c0001102c0b82045003280b002000225280c00101c010602502c246502032a405480425002c0ea00f030781c42c219005a41354020351109904002043c004280c0542780 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 823697401 1250 823696151 823696163
    0xa080313020102030d1b0e040b060d110c1c0e040506010c170c010f2c0a060504111e0a0f0e04061113150207150e0919020a09050a0b0a050403 62
    0x410308900040349140103005a508080d450420701040340b41040440005440d0b850352001d0003808900c0520064503100514a50024020302c0070040140b00f58210303143c090b0000b10501d00308001409554500400000d84034120780f1140b1040002543c02041c1042030340d401e503418000c90401d500000d1104071082800f81145d0041c59484603495265000c84001d01303e54002030000704851a210320003801800c3c0c400c094142074003204004510b00301c810b11003004ca400042c0c000007119440e000050f1000410032282c04d1308a030580d041c2d40da6584c154252549050103210340d103102c01c800344806041da07074119011103881c1e01d5003046004400d1080c90b9025511503400700715201e80d0f2560b450036028803140d051071803082c85000724000c4440c512113030b40d055003135003180c1505690b00f035540406400300d401000011203100f001421424003034481c82e00041505202a0244400e501328400c0781c20180c2c50340d00103003003c0420021840c004e58140e020b4103580501034078110804801400600c52448000d03e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 823698651 1250 823697401 823697431
    0x60e06090403022a0a050102070f0e06010903060c050306041505060405011404050411030406050114090406020703140d020d14220f0510051906080c0f040209120c0108090a0803 77
    0x8040c4244005111a900c05283c81c042c8003250740740c0d130980b000112805010f02c0c0c2c2079900254a601c001a46da080740c4508002501e130034180200c0440c66207004000c68140715040e0300c0000041c01901c03c90304002660b070b842e581c807403d01000b00015a88040c0d180400600513180600c2117540314011102119403d003401c2e40e146a0400c0400300324040c0e83d1101d64000d02e824202d4040a51050045100c0ca1054800f000741da81c0341c00d401e4440f200d03403002c4580c0080000700001c0000307286a00502e078203070090406510741c540f10700e0045407592186505800850300403d401d03440040034015006203e28220695480b494040228503034080d007030106c3c80407007540209541c188005600e140f26281d40003419240021804000c00e009054103460b00c1c5205002e003400d880300e42503144911803d5070400e5014202c000302030301c10424040100b01000b80c0c456400c004119055a40e00f282c642e1844540c805050010900c100242003800c0040c20004e590b00102203a40000c0c0c0d4010440754803405182d10640 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 823699901 1250 823698651 823698653
    0x21005090a4205090a05060417061815091c02010204080c011b020405040804150206100602150604021c0e0a02180c0d0c11030309070305070f0803030114031c0f020709060e060904 78
    0x103030651191b40f03c0f80e0404000034002c18042c0d203861031841d034140720780e080b500c050f00c418a10801580310030354016450b130010301048081024411500d9080000e071001c8417980100f40c0c82e82070020224429080c0540e6000408002690003840085448203003401c1c5a41050050142d40ea03681012500c000e1007256110001420010540300340c0b000b0709503005610044085c03202d0041d542e05403d83e0302102c42d070148a0001146480042e0003411001900309078011621042c0030312020b904088416410301203c8038504036440c0c4184940d0005805a80c01002d00810703030300510450301040700500c03542c14010303000c210150711b21404551001801031000110780007010700c102d4100d124090025030a000c00000c0c041e03541d0000031040309070707400f44090300c100e65a00c859501c0d25070300900c10b00200c0c0d0000d000410108aa15084401d0400c02400703075802a0f402030f900c0491041d52a1040000c1803001001c080442d40c10400b0001502d1144d80c1000306604048440010301d5006103000c0c811046100014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 823701151 1250 823699901 823699909
    0xb19030b0306160806060c06370b0a23040b040b0d0c05040501090b01140f070f060e0d05031302010509030a0b070804060507020706120f0605090c0703080f13021005090a420509 77
    0x40c00c0d804000003230074031074050b50440401620100c0ac00314441d2441c5200400c201d60039640350745c42000a000c0351607180600c0c2081c8000781090503042135100d6a600c22030131442e20b03102441b1112510424511500500785000c0008549041c0c0016101e6803500ea00701015981000104025082c1e20b00f0080e12110f07200400c48080c402e07100005e10103203680035402c2c108540c64102c55100d850a4064601c0c51141040450b5103020840d0400c0c0c2020011180b0030155020300002c2800b0580541500e90702c54113500c804407240002d58158000403240340420040c01102d1080c1a0001d4245c800303840300d14900781c0c0081c5070041c0c0c694400c03040b940d01c000300f505001d03443d4411030081c8000340c110005842c00d0000071400350081c41c07003940031030550303000a900011000c4003148105801c0031440d0700b10007150207010029101c0060700c17003404000c0016020a55800203458000c0c0f611040c45100503e15980c01c9085034241d0341100b0705030311050340800e2030a110b0703041d03446a4061071601c123454080f080005 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 823702401 1250 823701151 823701211
    0x1b060f040302120f0d060b2709060d1a0f04020319030207181b20060c040e09120319110c10020d02160f0b07090b19030b0306160806060c06 61
    0x5c072403c43e10740607001030149501c00207840003400241c000d44c2e015030a50030034412150145400341d80511000d000031814a8006800c14081e0b0181d800300090100425003200f0703a070300c180c0f500219504110108070851904100d5010404081010655500403a03075020f580c444880c014069080200c03402e0520400d00c0f5400b54103c1c1c0781c0c104000e1003110504d03c0160024491003018559607505d0b400000c0d841c0400030f0128020f80d00c0c1c1803094a42440d1a00c01181c00030041c1410419004104e6811603003181c000243d401451080111140d0038000c060001c100c0305007000d07081c0c01070400d00c4201c441da8800316000c0c8003513801c800096941c0198240c000001d1086162440744a044a2902c030103120581a90100940c4616003010164440303007000c0d11051070a1040d420046000c0040c2c4042004080707000349000310500703012a140c10070500090802008640b000c10700c0c0d02d51024843c0440e4400305041e00202d0640c1d0340c0786003031102c490742529007100a01000954181c4140308035410084856 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 823703651 1250 823702401 823702417
    0x902150a0e0d06020d1d011a0d1704030c03420903110d020307050c060405061b0a0b01030f170901090e061201020a020609100b100f0c0204021b060f040302120f 70
    0x5c100b00b41d4000406c01c0851782210f60b40100303030b5880e00402c06c410304c0c400300e21034010100081c800d40802c1d03000c0d500e4004848880c040b51610745d10a0200000181b09000043c0145202e8481d03100004101030b44007019030b81900d05e40c4201e444011480c40000f030301010b140c0041182000104a034800d908013501e491480c4500b60f080c620540f0840340003288d010018000081c4200300361030381007082c881008040d000310701a056002c60100036440107801c00000402c0406140400c0d1007403082581c440740401c110903442604c0500c0d24811840c01c000410741c0c0d606080da145a01c060400406e480001c00c1c0364031078000e1f11a400d8544000c6252583e03071041250a82205000a41d41c0340c000d0300e0000d4582c1e5003075500c00202d00c04c80c801c4c2c030480c202900a211001c1c001400d60582c2d944a504212a078240060380f1702c051040800c0868003686403800100f4000c1c60182074200b0452505030b90301d08c2e0900c0181344803410040e000034800086e0303001c20310098402040b50212f40301c40f160780c40c0610b40e200d0340c41 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 823704901 1250 823703651 823703677
    0x312090f050d180f0b0405120f0a03030603050d020a1119150c020108090f10050c070c030b101e120201120624020d0f0809030c010207060902150a0e0d0602 68
    0x9405080c40b42c0c42070030080c8032030b141c200c3d1440b0b03142e40302c42c4440391800038003810944070000e200a00c42403c255075440304020200b001c82c2c1807500d00b03004ca1420080082829000262205010b2081c4981001051360341c000c180b00034080e04605883d50007500d824406d015120b41030071540b0080d2080f20902e080050503454850b0664400004000380070740701640b0049010175a48000202059000700c2d4200c403008044000d0f02c4112010b1030f011005200080500700707541010310504010444800c00320001c2c0d813065a0b810340a00703000e41f00303e0030383c060f40d80070341c031050070151440541426145e0200111001001c2d401004141131006983c2420400c83d905100c0d841c01c68001202030410f82104050b544501c480001c003640084100c1c0c40310324246104022643d0350b814242c90030f106a400f142c0c030030300a00550f820075010901c0c0c00e00766448024240c0d41151240403150540c50070500c070041e0907070840c0b1040d182c00741c4000e000d030594100810f114820031a60101c2c001b40103160b0122614502002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 823706151 1250 823704901 823704913
    0x80f0f041b0b1201140904170306120a060c09120203030405091e0f10050409051914010c1d060a17040c0504051816080c2233030312090f05 61
    0x101c452a043c1500340700340841540650103420300c504213400c00307a01451304209580790034402020828543d52001c2e0030301c1e80040b800982d211071105e00b0710494201902c03a81c0041012a0918001010354050790003002100518207d01c3d00140c0e8001304031001c42d402901c8882856440e048810307050410031803400600f484100800803180b83c0a5001c51065a079440e443c1d0065403109c2c20f000450700e0401000340103074031050f0352181c1c2c000800c148110450aca42d0075210007100c1c4a1540c0d00b5500c40095000118000003400e004402d0b512a40150f0354200b5504241002000d0b080144418800100035480c2c001c1c4802040500449040002c0900303006002071045042c802e46003140d802d01c01803400030a014080e1501d50003201201d45204603260f0a000781002081442000501c15100c030148861040d545035074881082c040c040c0501c0107180c4000c0661101056242c1e407054240c4990000762003541e07650510000c0c0d00500701c0d801c00f120750000000c10801c0f52030402c1c0061480703030f800741c1544929 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 823707401 1250 823706151 823706167
    0x8310f140d11210d0f080112021f052710050d020c071d060d0b0604111308011e020c0d0e0409020a030602090a0f030b041202150108070501080f0f041b0b 67
    0xf058604114104000c840c03200829110854003002a01c0440300040d400714010052561040b0f843e5000500040299900c05111004160b400a1808054002c65004207a1642d00320003500c1090000310803403021046a011200050203a03044094640c0c10b124003c580c4a036504025415641000c0101c01100c082d01d403540403041c810490101c4610300c0d01a14000100c49041c516000f102807540444800165100c2c141008043c100d0244900c81c03031102407003100c00340315001c0b41910040c00c0d16400054000074080d8a00c950a1049000d08616401080384d0a02080000b44054416280303180420010480d400001d001d00810b59001c6d500c4404001d021040c0705641e030007000fa000048804600d40c640d40c1882c040711034024840a010500404d0018010400245015240325500d1058583c81410700305480162103080c0c010b00f48a5009031414007503940c2080c06150051030410401c0b03080e1034810300c42e4140400c000c0c0010200721060707081001c46060024144050410f5183c1ea907259800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 823708651 1250 823707401 823707439
    0x509070f030605040c05010518062215023a0507021305190608150a060b04180c09080a1202281509020a1208310f140d11 53
    0x4140c800365103d085e109000034180d806042100c405c0c102400224500070200020095290040c860100b8006022022a0001c00d9036441c001c000d440c108003402e8481c9025140207252800040200031443d56541c0b18038248501e204002e5248200d102c17603514090040300c01200c16020b000f6000350042103811850018015a8000746e2007050403d803007682c515010441042955440e1023400c01d6900244c607841c90402c20103810b0340d0b200e10500c40208a650346c3e01e0704500075a00070b0b400000c010fa100840c4103805082ca01500d04201078a1820324100d5003020b91250700c0310201e0b40d00500703e400c43c044480d281c5009001c4407407403d00880718820060750320600510036009440003210058440050942d900e0018810002c2042e005012500b0690030250203903100310515800303940c1524280300ca9422103c80340032100020404c102f1840c07262045c030031445002200ba80064170340c221504010301811448800707100054401322203e15a0304524104420f4150303d24140d02d41080000103141a4803803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 823709901 1250 823708651 823708661
    0x5060301022122051c390f0f051b06040608060d02090a0b2e05030a11160b060d0203030d0f02040510110d030605030c0409061803080a060f05030c040509070f0306 71
    0x404210014985040c1282c200c0b4800050000740c210311041640304d00400108901b44000d543c0104008405901c40341c60b1007240c0c500c9280304551000088080e007081080501503620615811050a13601c0d011150008800380114018070b810000319030001040390740c840d62000c0391315401a000b10803d05050b8910700c064a00140c0c40c0d4041d01c500820703600e9203158207400441d00b5101d200e4a10101d08640c6003102c0b50351015104505864842c220400c00c014840000d01d40d03501e680070140516042c92902c008020700040040344950004601100580c50220850712440303651038000610400540c900c070300a0040b600030b03982240c1c2e90362042c943e19800643c022000000c51f03040300c44030035004104030b05682c0d042c0a201c1d0140c1100c0351408150526030046520141b0410f008109407090010310750040418810540001d08248240220105944200c4002d417085c844000c2c14181030a0120f80d032403d541150500890341c40e0005800c408050150700098404520030300302c0710b40d43c1c2c1841c1c0301800d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 823711151 1250 823709901 823709923
    0x7060f0e15040918050709230133120f0e0a0c050103051f060503070903051f0b0a080316020f03060c0d05180d231b010506030102212205 60
    0x51130801001009420391244040041c0c1c404000d000c50380c103080c9880040c100d00408105440040804503149014181405018180030b000300c211a580740b8807014041110800074a04080303824402c0760703800740d000642c10840c40c0c2c040d00100300b25622248000007040504800042c600844409a0401014190301000c5440c02d0381c042c0040d8884030302c400b0744565842c020145c1c203e140d4030b00f007081d0b03406900550b0b0700560b07078100810704950302c1d10348a040111606c85140c40d00d200112400c130f014003500c00c01c0c103050000e40356400764500385190a0340d41c0c1301d0b404040c00c100749004081c20840d074441c1c00140d1560030213026540b00342404901c000d140e401809601001c00c0c1850005a0004400c08036000507480d140c0040810443c0b402d029926400140100810a514030240b5801c0111541c01060000322818a159240609180705404c407840603003a603110ba401001503051700b4202104070400c400442c40d089042d0744510800d444001542e904090a010f18a881e400c00d001d00840c1c0da00201c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 823712401 1250 823711151 823711169
    0x510020c1908030a0e0f040e011d0601060e060f0714070905010b0310090e2503060f060e010501050f370f050f07060b060301090504030f050306010207060f0e1504 71
    0x180c4600003441c0e840030760754011082c1582c4180328283d08284115480040c020018040180c800b0312000400d0565500c24641003c80e034464a0040084140a5503202800c04101c054401541410001000c610300320503002c1c03041c200402c044803414081e4044400700369101a0b0003540340140b049040d1201c85500c610f207280ca151a000140300700e40502200e00ca41140030a4a80307140c205050b850051500303680003001885550b0290502034141c2d90079103612074113003200d83d040c0d905d10b250010a41c1c0451440590341c40c1000c1c0200090300b0900e101d030f03065807401d0a003c0c0e2074000d24072b4811124080e50b000381291020105204842c104210b00d1110145241c4404c12405141300009403070040003c0300c06000503d080041d0315001d803060014050041c89040b0100b8401d8200c000a511030b082a00404e10309507a5209110130036811500200c640381450410700d0a5217000310010791940100d100c0e0000b8440700703010b9012103a11910300460074210040800d0f0020040c000c101070150014051040f81e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 823713651 1250 823712401 823712419
    0x40b130213020d140a020403020a0522060311030f1911180106030501051e0307170102040b04150318030c02010c1a090109060b060f220302030a050a03020c0a032105040510020c 77
    0x2204c000d60081f1000d89402a0001c00c08030718000500c0002c04070311810b0200c03503109902c2c80c480c19030349000d014002d5000d00c05459818082808040c200740d20749802d001c055110502c6002220b0004005801c19038000582c1409400482c0200740c407030408019004d07182d0442000820000c0d01580103506032141500d11030200740324210311008480d01c1c078282d070f070741a03202c207204200c0601d00030459400042c40b0000542400d075120f0111000d40c10940122200d00b10305039044500c0c1d64144221042d370000e84607008070328091a18040c00c000c1030060302904000c0c0324082c2034240300343c0564100282182031403541139407400003c0140242819841102c0d1142041d12408040c54a03409660386840f000c50b4640c506001d403210300700140d06029095240f09040c1d100000580e500740581607019000c2c401a00c0581681d00d0300a040c419501d03a15032040c3c0500400780007064405072102c4c400c2c82d603040c03c0d00c42c101d208401a141c901a60b404a94040584e0040030701150b03020178031084601c0140c681d428 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 823714901 1250 823713651 823713661
    0x20d0206070507030203161118010515040609090207030302122508072c0306042004270309081006030c1502030f0f130b030f070206040b130213020d14 66
    0x1070b075225100000e00181d000340a045d40c01da00c01c8550351400c80c80341c040507802e03d4050012030000390000c00f080d48005941c80040005d420f0000030042c0701200041c103545001e0618201920704011400381c60503403540460a4001c26000e941114910507241403200b08034607083e02103030024281c0b13030312141d2141082e28010024900400d007460080075103480321002d44645d44036400110800d000307200c1c078050484000b41120344041c00690301440c02200c6c2c001d401d11000071070002084a03a91801d02452405608902017000844035017503884245620300c070040b1850908940d14a25601310301d076980039a030500102c2c02950f80c08941202c1c41a0762010096968851440d4805140580640560010405102c0119040c0c00501884040d003282c00e09052000b4480b000e4502c6a0300641d107801800400d010f02d40302194040c80d8002031314802030030540b400c2c0c1d441401c0300c08080d101e4020615a11402021951810b26203116945c0030712085442d200d4101ca0500601121100b807075403c24003c2c00f042c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 823716151 1250 823714901 823714907
    0x3020a17130b0301060314010609060f0309172206020d030f0e010e0606210a141606020a1a270102120f0103030905090f0415110d090203010609061d07030905030a020d020607 76
    0x181c101c0c2d4440d160000c04a10704002521310a000200c21010503a4900c40d0200050fd2102074045a170b0074070607032a455a4849100400514000c64102c5580080034810060107600007000d0b6280e8050b46004220260070f040e501010700040c1d64a03402550a001002400040001c3e00e01d10807041160811006001400c40684a6446141d690321035040060f0400110790361113021207510214404541c0e842442210160039107805800281c0141c0204946800b400200c4100e13000c1e4540240c1409614181440540880384150454400d40b00c0114807a1201c540d0a40c107403060b546074607032140e03003030f107400c0800e0703824503c1c00d0100300d0101d90342000118903824454119881260861007010494685485065030302800c840b107080f8885e20f40d410704c841d80b0500c04c0904607040c130079003012616501c14410035007941d413140c000340e01e010301e030103410480e52040c08842d01c14811510440d50080c1c60f0010124081c0c03400e08000fa01d207100c001b64007c0c0d01c6034005220005c0302225030aa5000d61980b020807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 823717401 1250 823716151 823716191
    0x5072f01270302120705100519051614120d0605101b03032403030315060f020d08042a0806010605030408030621010c02100e010903020a17130b03010603 67
    0x10701440000600d040c001400c0c8018001c10851401040f10b040c2d0780e8a000052001c48170b12841c2001a1003c01e1401d00c0b1241001d01c240901101c0c10700609110001e40011403001c2c02c000b020345034110b0541c0c4030000c094144613200d001503200d003030aa5038080d50b0107080080c2031180710702030080040e400100350043c410070072550031000c021085650030302d90340c0b4200c0140c14003014480d0b510490074292144100503002c004011482601c0109a00740d070b6241c04800420b09030711620911099004030300c107003980414070811b0525103051038041d035110b50a0004102d0322200c04484c10b03c207901400c420b40b039034454203901140c0c2c1c2c1c042102c40c2a0380b142c90454290100740d4008100140070b01c046095454603c8108107001182058004442c0f4598140c07401d4030800303460b10015070004103854614204030301038616608012002881611342c50b43e8001e40d81c5668070000f03840a45009101c150242c448411600303450160006c1e8041580c440b03c1e1182250300031b104a0b004a403424070b03c1c1d502d0032071805003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 823718651 1250 823717401 823717457
    0xa0203180a15050304170307080403021507020712030921170a09030f020102011e02032d0a0222080102090103051302090103080f07140a02120f03090105072f01 70
    0xe818424402e040c003902c142d00081c0c01203504051907269030f54400c2003071020314400e1001c0d50701c0018900b018203001c1d08000100712030b8a01c0700800343c1001895070300020040c04071145c00380c40c2684181581421540f040942c0c01c1054455484130280c883c028294298810b9a4010188600242101840d84043c2d01c134000d03a001c0031035081d000c2000825502d6a901456074018000410b100c41c0407010741d02a8469107540b180b4140e8040144080b0341a204041454045514500345452884a0655210250050024144070b0700010409400140c0d01584012903103196035840300d080c0c651003854080d402003240c0700d0000b4504ac0000750107903110030041c0d0390b0b240c02602301c44050b400c5455014103a0300c0540d0700c0790506001c0014800051a01a8140720610a076000d469000c805204028180e01300d40d0b8281c91551000703e0803801540e020003210321440c0242040c50340e83d500c030301c0c01050014400d106483c0c045d00141c5c00002c1a01c0e41d490b0b007002c0410903a15010416941c0848400280204034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 823719901 1250 823718651 823718669
    0xf0702120d0204030609030c170403030210150803030103050303040302010c1d010e061e0306040b040516031a040c12050a020406230d020a020d030506011b020919020a0203180a 77
    0x10341081010140801080801ca20010152070b0640741c0c0c680740107440c00c154003200000c0030041c0c85024849030700c01030740a0181c14002a0310f030611315140250b88503e000f0160300810b50769a6401c80c2a59441030b83c500078038101040da80c80b9a500c2c04d0058494004640c281c015500340210360b42620701c22541c000f1042d80c940c07038445c1c1910304070300111200401c00d5661741c0c01c4801040b88604000ca190140d16031004000000d660300c0c50000103000940d01c0080d031550140c1d06000503c81c4501450090106100180c0b50000b00e0b5448509038503140203c000400da0003515200d00c18100300d074810040d0101d43d6040d01c041c40300d501e400071210100d100c3d91144600103140f0590505801501040e0b20b8030041c07200000c90b080c0f080c180412400c03a03009041100140e44070407501400150180a803607408002401e1500541040000c8039802e06501003000b44243c03010000200d90340600d410496408917050310454075056425006540ca034894071210481160b082d180d0507035072511907071040036555460 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 823721151 1250 823719901 823719913
    0x30c030303020c07091b0e0f0a0e0c0708030a0b10090e180102041d06090a060e0403030f020c101e111b0703140102030f0a050f01060e01090e0f0f0f0702 67
    0x10310100c00075005010400c40340d01520300001021951400303214030381c203091000343e12242e000d1007001d042d84c0c603d489105d005060800101c2d41990300c80d010380c800c503441c0100b801d00e65070f60015004500c0c4620303000100040004010f105400155610954041d03109607070702505400508c1c1c0540302d04107503215043c00381e801400052130810034120582c266102c242d0015080644812002c1d072203945259018000303000420400c0003034a031000a8641168522a08000c3d043c2000c8405402c0d420081000d01410303164114488145410340c1140c85020001080e105140a05416a009000e02010303101c4008401d11941c0d103480e0791032282810904011642500c4c080d031800e4480001468400042c1581c0118030001000c02c4a081a05600441c14800166646800c802d041c06804c00038015a650038a80310400060803440c5050905480c0300c0d0a011880d180030f040102c545210700c0d0002c4e00051030007030a10050400340308905004402c075204030700d00b40e5140001103028000488035000164448 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 823722401 1250 823721151 823721153
    0x1181406090d03230a0c02060f011211010e090f06011101020c0a11010513030b06090c04060c031d041d0c010c020307170a120e040e01060b070803061201060b0c0c0a030c03 75
    0x1350b0040c001e02c01000c050408403001c484210302040412168203400c6034035405403164183d0705201c0e442c1d000100e041e5000c070b6035044c1007a80c0d1044161400003004503001e543da0407003580c000d0001c10600440244866900e140c0b220403140e0101d01a920795011407003030355119808a0045c0251400c01c1e030314200404a080190301c507100d00c2c985606c0100d060000c1008590850805002100c01460092900080d10b051040500581c1d050050114180e072205101c14407550798003124405a02da0103250591072402461106000019120310480e481407070188008600e80d543c403d40000c2c040b0050640d04c4140c0b0342c0b80151401c2c03805040c002d600d600414400e01c03d0140724501d01c2c4140982404030354400700346603640c0c0000709000b45194007096420700320511900d003601803030310740060410003404040e10380f40c1610058000c3e108018040c580110000304951120504c16000c0d110060007808070f1036031244501e01940c0321110105181c000c611090000381000429070b012a03500203600c02c0e2003459 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 823723651 1250 823722401 823722407
    0x304231f0e060715090305070b0606070f060c09180b0a090e06070503150301020310080c0d05060703020c151f08010b0a051011010e0303091e062701181406090d 70
    0x4100d040301c89130707000d8a00141000d020300c00c1c0040244680c40d000d586d90001e041403208507500034040c9106083c100201d030000749841c031340d0400c100e50000c00410801030446098a108950340c0200012800c2881c882c0646130840c1c02091150100792890514a0344418640d8141d80040e00520a5944100c0100e10140d104400440d804940700320444410041140060b00360390099691075602603100320240448841403004c07203025001100c4d0700c1050249940c03042c2e1140c0d0300511300f4041c907902084034188030b68107101010b66180c403240501d40234504407031208600c0c02c04058050103803100e50000b041524051195101c038240041c02803034054a013404001c03104c940001c1741c1e000c000c0025034114030210240a54049881040b006c0d58682c600607105a1810500c044050a40300012070091802d55002c074845070008810400903000c40486a0040b04110001c1c0d0b1a0403e5840d0103484241c5100c170001400599104424140d01d40c21451441943d03050240d84501b102d402030091042c003980 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 823724901 1250 823723651 823723657
    0x403020111100204080102041d0405060403080907050d080c0d0903050c04092103051503010603023f06091005010305030a120e1002070c06080115110304231f0e06 71
    0x101c1000315912807a00d00e141c1c00580c0c010b41e0004105a4001c9028051403080c2c0c0e0203c0858a49440e1083c1d42d850141c603280c1d0b03a1580500b0207414000111b020a074080d00900200c0d0161074040e18180b0518841c1c900b40c0401d511107603000381580078862000c40454490302e1003404503504400101a20030380ca8003040300400000804844022043c02c048550a0708165010003007005600d002a0910303012025142d1a02001241c0d4881e0345801c038148010b95580c102044110700d0b01206802607044e1000082040c1d0302c200b0000002038040341224800c0c0000502e291048000c001076034107100625104c2c0381510130a000040060700107010300700c1094800c006014809140b950302080125080b40e00c40d08051140c055940701d25000107102d005e0244440b09803000300707c10b1800204a41c5441540c1c0c00c0d03e000100e0304010803901c143c180c1c03a01c12080040e02e01400035200180d440b051441407217564410b08090050262810103440310000c20300800c0e00440c00040c0d15512a05800b0b84200b2400754 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 823726151 1250 823724901 823724927
    0xa03030c092c0a1b0c110a0f0f0602071505130e1608131227060e01080708061003090503310b0c0a141903050a030605090c04030201 58
    0x480394100018070308006200b500428400240284124800c601100031036500040c1890342c00c2e07051400f07100760a043c4500104201919180414401c0c1e2989055904003020b81a6190700c50003420020a2400082003100d0895607055030148080b5618074069840304100e101c0e0b40d0102001d00d8000c42802e000d54010103c8007104072001600c1a140c0082d800c05040a0301c240341050300704e0040802d0950003424054008122110700112003d441e40c40110010a0040581c2004885a00c01419050078003940c406a041140c1c000c440e203448840050030040c80d203102030b0000b504900072a0f102030140040b01d01910010740440000c2926078015406003525690488142c030082107200310000000c10040824601400d081d820501d25000850700c03a640750704160501c44040080d00684200003e44440055001504410b660590420242031007010440281c0c2a49010422010150f110340182070000f5035403030800030240c035070341072142c4000300301c070030607101d910030082030002d92301501040da020 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 823727401 1250 823726151 823726157
    0x70c17091807030c020313050d02150a0e010f050703090b130308040e010305070503030a08010e0a0906090b07020706030e1f0b060f090f1c0f02030304150c0b010f06020a03030c 77
    0xc268003001161004414104150180c0c8820007404000307581401280d40d0050544000d604003030035004032070007070420b83c40380500c59480c4858030720071511900f601e0081c0c0c0d009035841640311100c120010f015001c000f03d007103000420a120118603140203c003512a4541c0640c0c1c3c142025040500384034031039200302c005852415561000000007910320b4004c0002c0c100800260015500d075240140c60030030107030401486a0002d00c0502d0180c1e40c4012132504483d4105d04d002e11540b58203005100038205144090801c90030030310000c080c0300030703810780781c1c05003241c2d0b07013100c0c441640c4500c1141200d5080250310000d410092040000303042150b180101980c26035800501145281d00290705940000e0240480402c04544901549000107002410040c25180050080c0540e09440c03160040840e004007038180a14801055440401c1614040c000e0300402e4501100201805841040b08602c103d86505190300040780c1d60031961044012103490340c0043c0846050340d80c0550180c0380e80301d020410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 823728651 1250 823727401 823727407
    0x14040f0209030a030e032119050d0606020318040615030902060909091c02030f1b070f120204050a0903050a050c01090804061d0406050a0501050a05121e010608070c17 73
    0x7607658144010080c0d01d100c1d440780a000a805030505041c54552400740348007901088031100340e03543c50000c40340c44080004411101c001d581c44280c54502486010b8842179140ca04d02080440c1c00000402d44154404403040c900d031544020081500c90ba8003408055130301c8891050030305800794005c40703681032009100d0707410b041c0200003042d00480102e031130740c01c01ea01007007030410b02e04c01003242c030b8014003407920103149495140500040107124032071140140e5542070380c060500110500140c8054002550965045641d4200001444803403001c168801e515110118250f00c0d00b51082d5501c60354561103a1781030444126060f035150304520407240d4155201d103500000034403142c0045c07015200a49840f5036101a0340642140e400300401c145000b2481d14105204a075140c800b084121502480c0040c1d8401821034210780714020401004d6031940c0394414019920000d80d5010300400070150410202d0383d03603080455a98000b074a40001141610481101083c02c4580f21224080301d0702149103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 823729901 1250 823728651 823728667
    0x60f0c05010e0319180e070323010807051206011202060d0509031908070c12112d0a08070b04020f060703200304030507090b030f071d07080114040f02 66
    0x400e64542c02c0031440d003600002131404c001001d00b58103110f41001490492407641c0c89a0360003820040500a000d4001c0440b0f0004151500c6500701421a80e243c84a03640c0c1b005001da04040803402c01e004400701130081010202d0941010303a85043c060b40030000610b810b0b40307803440036a025101007400741c0c3c11603010401703a42e1058035801014003c044001c020742c1c0d00c05011040d0904002c1039141c640c20005100d051140895214070115603c6812141c100000e40140806a49403015a40c01980500650895a100f1206002c07500c07201e004149450416400b0f05100e141c80d2070b54080020010002440352201090303500c50324a41c0144098a020020a0001d0001d80160080f40d8114001405035400102c2c40850744044030105079203100031b50800d4155650103807543c40d0750294010f140d60301c21111050b541c0412920101088a50075141c20310348440318060310241100d041d48000070f1038004201c416204042d054100c62820309910b00c0c80918000300405003600c04241c25400d0340910100d1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 823731151 1250 823729901 823729903
    0xc17090c18010320180a06090608030d06080d0c0807030201180b0a060609060e0d06110318120304080f070515130204051302030a021026010905090f0304060f0c05 71
    0x510200410070540c0070390315510304907415140d038000e040000c540300152804c69803280b6490000500c44546040000d680344a036160050075190301501d195414501d001940483c08070052448803002d00c0184240ea480b0071140366580d0910081c40c00082003505010302050300540680b039518030a20010948000006000d240c2545044040d9024152481401007c5043d44900b00c0104003a007400780e21710740ba080010b04105c000c0c0031158055001c00710030000b044116131101e100c0d19540d00c884c80d100d080000b6040d020500ca24103440e003501c109400088040c0c61041660b22903580210f040740392910304040c000343c07a001040d080f03401c0c2c4580180003813030000751000144149004049000911514010802540d0029010b0f6403050301540f008005620041640610319070156018560000c20307060845519000d003940e0031001424411b000062151025458101c0d04a0301061200d40c81d01c0c2c080c03030b4840004039040c01042d40208020805980542c03030080100e6242c0c2084d14100384203484007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 823732401 1250 823731151 823731169
    0x1305061807121406190b01020a02100c021c0302060402190f06210f02090a0e0103080405191d0a0b0909060a0b0301060b210c18010516080a0c11040c17090c 68
    0x22a0403c3c1703030245903000380d1281e0943c1d04400d100a088080312a008203643c481250203030020020b903e01e07041d0964480c0303078140c4000d40101c0301c0e880000c091b0f41002925400f007598104d120740300c011a02c110701c0701d81c00c2942d819035040c0391100e00d010340f030004140e4061041100d503600c8410301e040c40d6940042e5600c02d1941c074050b02c1002581d0b5102000822a8040043c0c02c806205140d2000500c0402d00302801d84003510001d48940001260004141c114511a40d10141000805403110b214180242c0e00280c016008003500b0310048601d00d003040050241244c18000a51107000010012402d0390000500e0100150000600c43c3d242d4040c4047d55228a018008240c04030fa084d580c91880031016652121480c0c102c0d40c20481c1c0141c0341c0120003c92189035042050105101500390a8540460740c120343c80341100307950b0200120041c0010440302415100048a50100003042c01c4c20b00075807000d5a4140e4034500c5407504010300385070544019203200e031280310f0380d06407204d01d454503460 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 823733651 1250 823732401 823732411
    0x624120c1002030a090b090321131a030610110a0b040c0609080a030302030402032d060c0a1718060f010e07180303051e031305061807121406 62
    0x28169500c4200240900c000d0754022150840d8820454a8080703644104100c098400c00180c40d03540e070501c1c00001e8501a0300b207da05030214400a0441a001c103001d004007804a10000d0f0b601c1e14540d600b40c071074841b0317403100160303924107100f0000a410b51400310110620420700d4100b04154102141a051038210300780b00423030740315503098180001c0c006643c892000030f04442c9080e0b503116041001064030742c2ca000c03c0c01000e258010001c601195800d01152407402c4950f014429888008144c420700391f02000c09286140c02508080361130b00042404440d8044501e4440014010001080340c4050400502d180440f000b07130700b051803c141c010302c102130082d03c3c410480962941812040c280c040c001614600500c000c240300a0700043c40c258007001140d40608100d0b440307405582d4540681c00c8910389038001a50300104004501201400035030207240a0000c030b4540381d40c2e14a4a80840141d071004e60b146500c010307030400a503450403042045c482d2007410745908080b911800507281c11419a4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 823734901 1250 823733651 823733653
    0x30910060b09011b05070b0d0204080307032c2808030d0509061f27140901110301030b2a0301141003020310061202040b0408030307081305062412 64
    0x14102e0815039000922080700c1d01c00e040300d980c0c0c030052603403441d9a40071075101e0040b9a220218030901c0c100807550669004003102019281d840400b407030010202c1030840c900da00c03c0155078566059102d902c2110145041c805032070044105001c040d56058030700040c402580c01c17034841c1da010a00840a0001d03006540c841103010039a410b01e00011070900c1001802e00c407030816211800d410082d81138000307108941032240c54400c61a401080710580503001e401110005040041e0b81400c048645581446424084002c0012280307182c1140180d04c000c3c80050855002500401d000c00c100030806030590b44a1855024000d909100302c05454009a0041001c00da04190a52060618038150701a0807800c0c0f40861451030700da00300001081582c010541005464a850385402c0d503182d048801030504a20b42603200c0f640c0714103030b030390344c2d07000f00d440f03000041c0820f011440c510198498042c115034410054202c03562000705d55480c044894805242100f46130500044640380e4510014004000720 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 823736151 1250 823734901 823734907
    0xb01120e120f07060b0d1a2203020604051603051c0c020d2f060a030504020f0303070c08210a0516060c030c0e030601060f0806032119030902010c08030910060b 70
    0x2090078011500714680d118010103008106030000781001c4912480c0c4851002d4561803600c0c0c12100c403042c4c00c080d21128111810f08c070340440c00e058000800300d1241e40300c1c00440d20340b44901140c070200000c45100080996018072840200030440c100070212407101361400c1d0105100540008038441d00d40c58050700e058003071038000305654103154030002501c07104c0300c4001d20391420400890707038921590b2840c400b09585c07400030400715580d42540c0101c3c5400241129125085070401910020f805d2003500d0b103a00c60100d400700000703d03035500d94444024448409040c005580003c0da450b0380140c0d14000310402c40341400000070681e108404110398580e400089a0802d540c000d070920030f03511941c900c65400000100540ca9018425003a41e001a151180140d00c500001c2480d100300800e03d100ca01c9210203051003800c007030300054030f051843e810050f1004000004240c0882e60440406400101820480d402240c207000056402017881b9044030807120b203144080c1c0480322140c0140300115400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 823737401 1250 823736151 823736153
    0x50c0712090e06040906091b210201021e0304150306081504050d0e060c01020a023a0804080c0d0216090612110117011511010b01120e120f07 62
    0x1460203001800e242403540e4060b0504542400b420300050040c2c0c4940c1d01c0742140c208100a5801100040740d01003d039018800d1a603c51007210071860003140704145900d0080700301c2c0001986205031341901070b00134102041585090300100740c9815a200301c1032000b004006080280401c56000200c0550b1340000c0c418203141c80e284c20310b05a0b030600c0003000c1209062001090020905100f07006480c200303100d002c8a100d010408a01030406d00c61010351003c204031740c1a60300400c0c2c4290703035850314120b01d0680d0000610040c00c4a102d846140e095a0454000c840032405608070941088c060a0b48504100c1d100b0501c62030081c106281c1030050b04507000c1380800010b04040c0f00090580044180641424441c0d4000400850342015110428000903c0359a034001c03450034100d40a05429041c141da10b401498910303580d40b09662002655079a860b807090f850600c40c448133600142d40d680884030800c098040070740b000d400b45d00b00d01e0041c0d1003440a20b8045034010804a5092440603881d1080303 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 823738651 1250 823737401 823737413
    0x509071203030f0b0301020a1d15040b0703090518071b2f061806180904060c021002090f10031508010509010f110f0d0f0218030705011d1210050c07 65
    0x40603110078046d03070041c0140e2519640220004141c44145403030000102000070000381d03013180c0e101110b010403c4c00035000c1103d03025040102400781c00790b1100a5503036035403000e01c8802140b1068280340d0700c04101c0401ca6071841a003508003400c4040e08401c0c0401000c1c0c4a4500c0086108020b42080c21041400780b1180c41800030303c0000f102c225000d5050038200d0f003001c0c0414003020082c80c490480002c2103511101041040211500050654145850686004002052030080000151180c070b1030618928280c0c0c004c4031070545002c0d050321081c0b45c5013410f10050364080c0e03003041d060645400096003520001c0800b807005201e0078002185a09064001e1421942d10f02480d9042a003400c500342884c00490085a0300c680d0808500303962504c020240c0001488401c40340c81c203143c00001d40d06400d507078082125140e0b03641141036030260340c0d854006440800e249251a200502460b034600c1c2540752940703107500780404d108141d900404080751a84110348084558003030075440441c6403801d00c14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 823739901 1250 823738651 823738661
    0x11060d0b0909120d020d0204030f0b01030b06090c04143606060703080f0901090501050f01051e0109170a061b09060503010b03180f0d09090b0f0904060509071203030f 73
    0x320342000703070182d02210f02499050744075851031211180d8000502140c9031700c003641220010740e08441c061608004da0310704420845428401540c141541902040103032030302e031600c90700640010201c103240529182010085d040b030007032075a910440c02c403171403002c500c000304040c441126174100c40304035101d1020040c459840003405060003082c0507c48040000d41103400180c00c080c1144140f645596258501400f41920640c0200780303508210034406d42c81c413480501d60680e642122414035405804440588040c1d5800340140001e214103010080b0f50b1072041003041445a1030300750313005030307030252035001c1078900340d200300d0f1401788014404843e0f07076510000da10050b101c0c501d032403031540d450700340b001c0c49900000e002003551010140c040c00c0d00040c00c005003011898454240d0f442d19000b00c1c0003601e0081544598440c1a0074500c1002e020303c4e007603048401e1070900424524071602e0f107440340310003458018000308851044000100e00284d00104c2c41000c1d0b48030b590080f918008180000c001d0719 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 823741007 1106 823739901 823739911
    0x60d05101104091a0306161106041a0606120412030603051005010f0603020f070f0c0b1804060501090528091508070f061b11060d0b09 59
    0x98580040c000300d8142690030002141c0c602100a14140c000f51110f03803540181b0000b5262851000e039031b80c001080c3d45421070089803d84003891910a00f03840075290b1091440405441f00c604100ea2940302d602075825900b0041e1180105c4161800508000c000c040c403c1d07410100e40d4406d50040004582150884004006030b03851a00180304c03c0c0510380701c0624000e40070420074024001c45030712400020010346440201d44517803d4414004000f00d0308807121800018681e044400a0051009403207501101c0da4801000c1104039078070360b031125041c4464504200300964407403504c00c40d1a0384410200d51b0140f800260104044100c4e0042c5c0f002d0b5140141c158a41d2594445103010b1382d0303214040b5001280c41d806090108031072131040301d002440140d0542c00d41118899aa130032075205406051201412500042c51908402c4d2a481e05565945100d8244d180c5801421717000 = true := by decide +kernel

theorem cover : BRFrame.Cov 823561151 823741007 := by
  have h0 := BRFrame.cov_init 823561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 823561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 823561151 ≤ n) (h2 : n < 823741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
