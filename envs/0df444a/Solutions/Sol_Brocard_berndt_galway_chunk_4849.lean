-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4849
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:54.963544+00:00
-- url     : https://prove2.me/submissions/d4be3d66-b007-4fc1-bea5-aa10c5ab259e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 871942446 ≤ n < 872122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 871943696 1250 871942446 871942453
    0x4172b0f0f090c030b0714031501021612150615110d030204030506013c08160315150801021c1103040206070807060b09071e0519180b0a08100503 64
    0x440201c3c140800c41e80c100c81d00b041502c8040da68800f422030342035105120080c05100003101b0701c448030b05a0b00e00410080002e03000c807111111003c0d100c11906289210b02c1201200106c11240007800300c580c482e000f0300480340c000c9103080c1c41e2910038800c107520385901c0e00003500310446032150040800984003402c00303d041c00c614050030354617126103c0c0014000e045021000100000002d032860704605540e003100c01c400220105002184412000c0d9440340a40342e105031500b01100d42045065841100d80c4041c0f01001e210014192902a008070590466100100d52000401101c280014071140700201625812103000c060a0411110f5010038815610740a108000c0140c03075020490344c4039a0048610780d00d82c03c092404602502010729040d4100300c2c440180065190400416620100082c00042c590400030b10304403001d000c0c2007409452248001c0c00e249030303240660003100080240d1601201038545070001c03d0110b41c00307813403130704001601c440411031004000d8000001504044026 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 871944946 1250 871943696 871943711
    0x314120910150605090a03020a030b01080709020f12061201110a12020a090b0706060b04060903050609010b010e0f130c09030c0621050a0b03010606120b01030504172b0f0f 75
    0x85030110641d50083c2c0d4140000001d00284c10b607100d030304440040d94000c210802243d107034a03040408080a202e044050711641030007168900c03203070083c0c40928880303440203030410100300440c81c000700c3c3c00f5282c660010781854a03141310810a00032030040781c0e8001d05c5a591041e061a00800c407080030780808012520500c8031036040c55000c2c40902c100c4001601c03060701d840d05814120010506a030040691031000500020741c20380003d804000c03a80220199541a5240e0610600342c81c16401c0c43d50002740b449100e00c0e91403416400c010202d4a019100c00e2070f03140113001d28400c40b203901c45c808001c501c0b00e41c42041005000e1401ea000381025150580440020184411000d41203803001c0070010b40310740008000c141144d11880c1c41e140e00400074022280c0d500d20207400e1915404c0303070341d0b0582c1c00c20085901a50007030040c02c0c09194000c00300c0b007010f100c0801804840d0086441c51500c00301c0342141d6409202c80940d020100c03a0211320000b0441a0080c1140817150060819908107091125 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 871946196 1250 871944946 871944971
    0x5150703030b03190c091406030705060d09020325051207060c060b03060a0f0509030906070b1321080f01120f0c120c0905060319030c0314120910 64
    0x25250400d605007404180e00c0b09040000b4100710311200b140c40c408501106034414000c4041c40030085a500010400ca020079039906a8180f0300d084489a070036a100c580d003044035080c04001000040c090010000e20145a640001c2c1044003940c43c41500030314182104501c9109180048010305049400c19a41410407881503180c40b030301c3c803e0034140b01c0d081627041c00348032840d0090500c01e00b0050948004e86030801001e070007485042824460107140c08001400d4440c008203e1f241d4540c000c10302805c15429a40300858810300178403040a0303c1c00c0020080000c1c0d07881000008504011441041c140c00c0b00f04020050000200140c5000603400010041c4099090030501a15040303080c2c3e4400c0c0c0c20b1824800c0015001d5400003c0f03445003030701e0890034404111078440c00c0c0c0301034580c01d01030364a80c10201a55030000c9030a20724180d003042102070020703001d01146000240700f4107110100000d454040c4456400010442c4c240d11004001c200b04100d003441100c0da0405d41d158100000c18003400f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 871947446 1250 871946196 871946239
    0x5060f040806070e1f0903080a080a061e18110c100e030301030f120c08030106020f010e281412030703052811130b210118020a030f050c0a0905 63
    0x21001303006101c0a11698900c2449220346c9405190092022665070041c0100201140c0041341c3c3c41e5441407a140010070504e140010300c01e1056021584a1406410210300c44a4180e01292014525a80d0450740749000318800141984420b0103014110081c001d002803015502980b07107080c00c0c0d0304208010301c000f0b11840d0f41c002071303207400c400d42040e4a400c20b00f0980d10034200481c007400d0401d003c80001281640004c001601c2030115001b1710442c04810b6100799511101c26a110b03003c2510b040d14412246191540d084845c040c81441200704e120019542c200802e41100800815000082002683e058000c0517044400300050034028080c4c541c1d2a00c0032801420300500990321204222050307980346090b40d1070040400c100ea060aa40c810f01c581e1664011902c1d140702d0b403152030b100d6401a00c400c01060494024448107898045180c14810003540105015010302d076980d0701407a0542c5291042e60310611150381b981750f0300d0704852805070030540030303600036071161000c200c176050b0055000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 871948696 1250 871947446 871947469
    0x100e031009031205010e071103031e06150f030f01081621170405011e0815062709060a03030509120114040303060e010905040812090705060f040806070e 67
    0xe0001609561440c0495590b8500002c00441e18102400802c041d94000f0303003180116425100c1e1a2400c400f240002c5c0c89000881d00319941e0060700500c4140440600a11980018010400d4075080312040406030143c0050ba515034004402000300600100300000c40d50141c0b01000040440d0b000c00c0a6580b0490003038040c004001045114914404d082c1c0340740300c40c00c2c9a00009074010440c07800c50740c10f03c0341c11503c40d01d40000c181d03418900074041245240c1ca203103022a0303108102a503403600b582440c01008031900303812020400030501102450702c450140c0c00003080041442003021001c1080c2820042d01361845001201c80400000381c00c078048441140b01a908d0346160400d19074030500401c980000c1c2c01080c5e001d2810003041642c19407001003555002c0c075002c240c60f601c0e1030100c0119074084900a0a80c3c10802c41c00204800340c81895910191020032130b0b2803a0344803c0400c1c071681001c0e480c012940f03000708040c45071300b4046c4440340c1d20452030301e0514136441004002235108a0740 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 871949946 1250 871948696 871948723
    0xe01081b060f0d1104080f010519020702030a0f080d0515040b0a0503070314031201060f021b060403060f110c0a0303050c071e0606090903050909130201140d29100e03 73
    0x100d148070003080303c184d0280c80003408070b40291051130b45080021400380c14121030b4000d100d04220301c000c801029900c20b4502d00740d005002098016540d668980c00d1a440803800e54a0503018800c4031314020031400358503c9140600c84a03030031892200b00303201c251480e145a551080c810030005100c5da4a0024108040341d030000041d500ba18200d090803401c61040031101c0c003c0b1803154002242580e00210301e10f00320340c019400c50750360741a150794007844030101300a0f0350b902840401c41000400c110360011403110201d0840015400400b654407140c1e68441c0386104090303041422100181740d05441255841643c03503020514040c0181e40d8000760006c014660603142d44400328090510010758404401f401494408203c1d07c5540c0c1409012900941c032414030490050340002d1520800c1602c4040740340d03043e107511403c10382c04070403041c01d42c11414451110a07900c490580c1c0c0f0708100b5820701804520864140406c150000c24028001500200e51062046015803402207440000e08444400c40 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 871951196 1250 871949946 871949951
    0x4050c0d020a12061e0204060e040b1309240e03041e0b160c2115200301060306080303010b1c14160e01170f0603070e01081b060f0d 58
    0x119100003414419541c00030740d041c20f183c1ca096020090141e00103140500b81c203012810b4a00001170329816031286014040006120700102410fa0602d500309100c1464020300c0c0600c481407040d0305804441c0d94041c16511b1001d014508400410284c01051103024015800c0c800c01109251041c0d4920840c4a0f0b60054003903205000c88560803c0300407805848280302c2c1c20380e03030b1181555035101942d02501c02e841c0c1340f2135002d0024403d4864003009121602400c0b4a40c038810164645249201075200305104880d01c1e80d25440201b039100c1c420104400c0190b04098803075061240050444074540c21040c8503910800c01031080103112415190300840740302d0080d100c9900184180e000d010070f03042e0400301e800380c1d030700340007800020070114412030350980d890a5210060900444114058100c40b1030150200c03400315149001032000d866200314003030100e0784a2540c40c04001130900d001d0b8042281038201061004101603105130900072454212001c1d0300345458010580150f02c04c19940760035241d0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 871952446 1250 871951196 871951219
    0x50d06081b09130c18020418151d0621100213050a06090320040c020d0806090c070813050d030f020c0105030f0705090f040e07030c1a121f032904050c 66
    0xe407603011680074207140190f40014074030323010311080900868030103080c102d148410301141881c00206060548082000525455181d030750500c031b1140e0150106402c44c03001c00701c2080310b0b00300801c4035800441c200000142c0e510545c2c49a149148055040b007071244044000400c1141d60000c4100f00756a04442d4069141100030007006500600320030280c3c0050618140402441d0040342000c5c15443c0c9407035001075940d40e81e080015082040703560903204141840300c0c2001c95401c1380a0108684c0104042c1d03d80c903201d9000866104031401c04078001072041c40c59030b600540c10b0001e0b0403103042c2030a045045062407049108110b100911010400c400459250302c01d0703640d00301580ad144d001070020440080701c248510740b6032009000a5440340b519080004d82a10038110051038407003401c141a0610054007840d10700451301a080c0113540070300f03a07045000582d8201c20382008511840950703405003244800508003d20401030188009002010800820400709034100e035420304480345503c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 871953696 1250 871952446 871952489
    0xb030108121b12190f140a0207030b010902030415020315040902031507030218030313030314070605090a1211060a0506010c0b04120809120a050d06081b09130c 70
    0x2440d8084454072140704007900c00c9800030b152001020300c0e6410720131070311240c1440d41c0141c40568500100400203600c4900c4c3c5504440c007a40039054001407881a500c08179500d1f207584020340401c0e0041c4010543c0001804200112103d42c48181c0c45003e8055003180360121101c020030320071924060291f51140040c50444da0188850b00c0e4410904044500c06d0400040040082d003114010041d42185c002c41d884039860000305540d05494070f0b0f4421b621042c11035808480c1385904c6402800342c80401d0000710700060940c02910b1180c0c4030a4024034001c0014141000140e80042806e4180a0021002556a040030600c2d0381c0c0304c04451408117442e00c41e900102c41044c2c941d24050030078140301050004010741d042411080d00c40c0341c0e030742c0001c0e902d640c1c00310358a034881d0030020314401e41e00300200c5040744d00600140146a04560000607015611000207091425403e0030340d0102103000111380752454048191070300500c5075001c039940303c01d1654500f03440c0000360107102d031601c44060450800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 871954946 1250 871953696 871953727
    0x90f0e0a0f020a0305090c040603020a05060f090603091018020d2409030e15030108070e0a110a0c060f02030c040302041808070308090d050715050414070602160b03010812 75
    0x2074060100210740d21800f0b4000100200010303221007040e402410440c900b1071516000f0f01e8256600140811030b00d07890041044190b0380f0003c0700c043c00b04c03401d0020b0055a51140c02075441404030b80302600e000d101024000003110284907a912800356105130007030258403403481503a0090750210104030340440c040c3c0d800304540000e110010440b81004840c80405500982080d40e020f0251000104503190104406c00c0340030034003c500140d844620108201e4500311407107508844180400912003000302401026070b4000481880480d010f84600010010b0501c52510520a4180c04500f5403c00301810b0550b441a0b200c040d202d90344624446840106038010b40d800e55511805041e5074400700d14000d0294141180c0d40d01c0c1500458588503c010f028008640c48140d00420f00d1003510918088078004120250045d540316880302c0301c04816180410080c0044e00ea01d80061209144d820480304010a4540104034900340500041101c0c1c0700020720851031403542c500c21603c419601045000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 871956196 1250 871954946 871954961
    0x70614070305070f0b100906050a14090a0e06010609030b0f060f01030c14211302062a010f0b0406060c051908071e02181611010f02030906100501090f0e0a 68
    0x40f003400442444a621b049505c10412940d262070103214290740c91041100e52035291161800380f040003000c03801185040d040c1d4030f500c0b850201c1d00103010072412542d5860150260003000c0402d03041c00051050002060011b40d02c007615210214803803a10001081904080008250505031a03411b000c8246000e403001d00702501c0051591a250f40f118000c1c100041d0f606102c48501d000800d0100320351b0f4100d0800c000806402611251504c800c4120020003040014290b0719131030340340c000c00c00718902d0a000301c01244600c2c04001c21428488810881100c0369a8000070a000c4482c03410780010380c0c0450400c80906200141d02030704d04884c10003180740e20400c0710060001c40c4111001d05a0103140780d01c100078074000c0e649000c00050f02d80c01d800c50b07001d090300c500c80003035208504140500d104d047da00c100390005c44000300714840030303090580a9800c04c0c8c03a245c0594100c041089410300c011601c0300700900003442c016076118600001c003440c10300b590003050703080b91012001a0b00c1400c19084844d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 871957446 1250 871956196 871956203
    0x714060601170c09030102031009060e0705220506130e0717150d1a1e04110f010522360209011e0309060b060a050414040905190302070614070305070f 66
    0x642c8d038644418010704142560154185091601c200070680e0300800200c1d03882803070141c90f002d03e0000108004487e0301c03a480b69402031a40d40340030105880e01d030140503081d001c8604801e000d07881d04050301c01c0d065000081c22103007088000c40000c3d020041640c1c40a401481248002c83c0b242d52220201d200c0300910f4502501000304841001909488150514821082c3c403c5002c9115410520951001c0050340e001d0450f080640340c1d42e01a00d000001c0b0040090141029454465a203d060303060b450070501014000c02e00103c101b07c008100280030384031490450030081187e054501e4540f560054070104c2d0109540030400c40103a074042c401640c4000391a4980f0908203900c000000d0140c16943c008641e11818078403011020705064094409000359500c41c3d03801c150408032041c003150321070f2821907072203900c50030040003150050207da040c40328058144448103e25060103440c000300ca612101c108502c0394000c1c090364070680705440c0c4466241c584a940c2d4642d506020340032620502d4040d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 871958696 1250 871957446 871957451
    0x2040b0d080f0a02010c0207151101061e080c030d0206040f0309030206070c150e0901090209010c0b07050c06100602070308031314012403170f04030501110714060601170c090301 78
    0x1046100c02440240ca00a803ca034000d02151500c05030032a2540b1440c4183c0702c00d4040c1030042580307503000c1c05506083c000d02c08000038015903915400c164071020042c507104800788541041c840d4030320174802d01100000542c004d1800c080040802941e5010041010f020184102500d00400d0b10488a88006540040c00706465480500f0a41c030882c0c03c52042001d000c604440d60b05d0840d004980c0040d6069009080c3c26480e860200854013075030206400320704004980402030000390f400580c05009044a80c2d40d140ca40c480d44100500c0c0c0900506020b080c100c04520422403943d00280300020b40782c0c07081c031041e26916910f80f04010021020340c010402425644e80400f0010154003005a085240b800403510f00302c0d140c1c80400300d0b110ba01001d0000303248182035810b0f0454810003455481c01e1414090328003540c1e0b440707003401c440109007029221000080c4036000c1c450f40c602c0301070200315000e010700521300740a0006401411a0190009551600310000d4884c03407440d0251101e03008080d00a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 871959946 1250 871958696 871958707
    0x90b010c0f03020d0801080c030607050c0c130c030501050114040506071a0f07260f040816060f140c0a0c05010608070311090108070b0406030b030a150902090f1302040b0d08 76
    0xf035101d40d8103418030000140210000100c2250000740c2280700c200180240916840d81581184d665100f83c06050051049240c55074058031b561003012142c004140000451a02d10b40c8000e0964106911080c10001c040003001c0c2c0042d00402128103e80c4100d81241c0c0d200e074103141103a1840c450410442208440500700b000384407400c901d4500c44c9510f503807130b4600d02c503103e9201d0343c808580031b071031850040d44000040c4206c0700b003100303080d00070780591422802e0070070703200d02d03543c1440f000c41003203e03090340f0790ba26074182d84042d0086a602c010001070501d1a480c10301c1e100e000038090180394904102c0d085a0840921800798003c60140411100b9a90b041d0b45038102441442864440710303000750b081d58000100c1c0400816481c00351078902960614003842c00c84100c0180210804c0c0366450700404024038001848a1900c0b55803403d00700d404684043e40c0d00400080950051003618160004820042240f010b9041015443d904560005842d0345e00c01c0070501d05c030042d0300020405400000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 871961196 1250 871959946 871959953
    0x333010b0c1c05120c090613090c0302160803060f03010513030e030f0616090f060804030e0a0b1c02040801020c1c090510050309010b03010908090a0b13090b010c0f 72
    0x2004003410711002c5484001c1e407400003860689218610b200000d0f424044503401424016295410003000080517080028070303000541598858a6000c18041051404001f06011805030f5040901241400c40c1444601d00b428010707800f407074600500c034040000005400303a580e4640d20050140140003000141341503400410f1450554000317801044400c07014444500e0001040030040700100b014065a0f00c8414551000c240300990120501540b41d42c04a840c0351441c803998018003040e0389038415420316080c0508103618400071240a006100700070300c20076101e80d0841c1c001e25416402c3c4001c0258104c080c0c0020301a80d00000b03219400003d8160050f0b0000960904804052400710f14400300d40f00240c9050146104003a081080c9d410400703040c40c040c01c09164410003a0300007062042039503000900310358000e40100d60814011a40040a00f0141010030160a4441045181c042d95240000f101c2c40c062184494954039110030340c61503480740d41342161050f845441307810006414075 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 871962446 1250 871961196 871961219
    0x10b1204060c0225050f19062d020c0a050d120f03020403080f071a04031202030403120905070816121101030b0a061101051003030c030f1e0804110f033301 68
    0x1240310b200b10005504042d1903d41108144600b000c00f011b401c5000349400800d41c4d020220540c07447c007800303031271414019070800000304181c084055400f0b0000c10360240c00700714500200360015405401070f0a20000020f8405403c081e41c40c1460a0104c0410310384c1d00110b01902c92500014580c040104000c00d466a1020260002c41d124240b4804171301007203009031000d0328040b14068005000001d0900c00924181d0047d034000303001e40f500080458070020510140e0f4402c88041301e455200d03180400410b8014810240c030803a410300c41c2c110f07903450a1107160119898a1000d4850704020b802405e5a81c080d91240200180c054400c250890b41d40001800a4aa100240009500700f030005141040e01103661029260700d0703100d0300c00740c1070103407012500708100030000000e101c0028410a6000003d041d07a8040200ea5507805649180c07d00d800540342d1240c410450017040024107074410355801041c1c4490003c4041c0708081b000d094021903040d00742076040007060f03c1030080d00100d966100b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 871963696 1250 871962446 871962449
    0x9040b150604081c0e03030307030c0c02090708041103191403120c0316020d0c080d1401090e010e0a050a08030c090409030903061401030201051605070314060f010b1204060c0225 78
    0x1440418404000c03065940300c0103120015459001000049c135990b0081c1d00a41816245141c100a8400f0039404030b2480c0c0010b5880d980410380ca1030400c0104090310011350600d885c184e000e000f619a01400f11151130092030703001001484505210701020504105541c100700207018500400e017001c0040f0052940190b500d090351300c4141c81184034084c0001003206440d00580e44440110040b501c4604260300180070a202560726440085034015520301101d01030104204d000902d110200400c600f1905245012500e60b00701801a401185c0b01040e540c014a40003040c040e03aa0b80d5840342000c2a20602c0d201c0ca40c0a4907146000040c15804034185041e41e100d40e070308000c01601d441ca1905840d40900c0700031b000550401103400700c55480000200824403500c115000326490b43d0b01d01d10b5041d000042403220381c2c03000007080604070300411103e006099100410f031500305040717600d40e0b01d50b10040001d0541d0340c840d4030031880d85100300001e04506580c420b40310100a1048104118034015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 871964946 1250 871963696 871963723
    0x190b03030d0b1206010e0a09060b03010615091a0d0c0507050105040302030a090801180303020f09030304140f06040305060406090f050313030605160e0f01030902190306060905040209040b15060408 86
    0x1448240d40c5a03c001a240741030f50780980000406a45c0e030b0781130f10003030420208211040351312a202007815880c02d000d620701510413000445e1310310080c0c5400a210030300c00d6020200030601d861152400032508000c80c0e004068242001c00e0300242e03000c065404d4030409200424541c0b80600300814554040302402140c02d032a0b4a4183d80d0365108842400d0310410a40c440781d821141802c000003900a50040a0160103840d240c1e08101c00000041d095401a6011110031054020b59019070321300b17145c8000d15a2002c951a504150854440c01c1d501c00c00100010328071551010503400780185103004d070010550020480f6603070090820003410b00940383c40200d03820303400e22003c00c000c9003408070015415101c075541d0366a024075400802c04402c014070041818035545554400c09a1140d80d4142611600212425102c61a40c54040100c50307207a8031101c0040d240500f4800182e44510341a48c00c00e821444071180c40d220006420b1b050b0600504041d03000800040008182c00d001c1288085802d6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 871966196 1250 871964946 871964959
    0x28150b1c03120c020c0d140d0206090f0105220c09020a0302180102241e10060806010207050108041103101523100f05160b0a180803190b03030d0b 64
    0x80355081d080c3c4020a20900140c0c00c2a00e0883c1d0710b0030700304201c640540c0101d0301061a00000410710742000101002000141c00c61010030450b400104040c0000b800c551000300702d80e240c00f1041caa5020701c0c0101c010480381400300d411050088044501d006020244d004544d0b030701d0a038102900a41c0440a0304032200d0009091000e55800818058076407015400b4a4101d4080860b8919090740010301c160901c10317002880744485003036140c0003449042c201980518007030406401030024400148050304551040ca400d1000740d9200c0807039600194001904402402080b0000381407598102c1d980e540140342098404004800309500412541d180000070140c414840352102c0f090025444941c002d40c4403447d42498500c00d507130000e2a03030064580a820031400350481019000303601d00c00e440e07681c8510b050008031903583c41a0380ca03070104043c0c421845009a5103a0b40709000003410350800002d4440a55440009500071946080006003030b0303070b40d0311250040540101800d9403c10700406 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 871967446 1250 871966196 871966217
    0xf030f04020f1f11070e04140601080115060e0105091e10030b031b0102070305061611010209010c08030c160602030106030e0a0c15050906071428150b1c03 68
    0x1c0141603110306861030075a41140049a03c42030754200f900301002d210a00c01c0010014140d01d0305000207008510075807041607260044c0c0300442c80d084042e00241b00700c0e45007042200c1804103d03407800041b181541040310306807a030000180c40340c0c050000341607006104400c80741c1152515003a41c40136503d0480c3d00d99820540c2040441c11905582d4070640c0540c407800d511807414180c0b0502c03003002c009c148101e0300b80686079501c050074040281c490240030509490055080f5401000c2140c000844600031410041487c000900751181d842d0042c0c0740c03000010215003c042c02c00121040800e035816551002c5643d840e0000081d4024481c2c0b00000e86050748060141e4004503a1400c001e13044036400c42c0c07060424140650303009032443e2070000d02c40304003c8152240c49650152403820b016603a030f801051200d11025040440404541080b0047e010400048480720312980043c5a0400e0091491140420040000307024196070144c0c4a082002c000520700c54460010052521aa85090458 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 871968696 1250 871967446 871967449
    0xb03010c021501053a0c06080601050d0c05040b070c150810180b1507030201051005210111040308130e01031101110a0209011d010b04031e080f030f04020f 68
    0x405120001c0000b01042100400c554504004c080b038041c801000c0c0510b0510301c00510582c100b20020112940015225062080c40740b40c500b500c0041c509400e040415140c4000000e08520581c004040921342c0d50b585014458429001d03240036255002a00da61001b981c00c001a10702282d00c6008108140c21407014540ca2013220414010500040210301c40c40c10031004034442c0030712507078240e142c0d562402c0078802c0d42d42c2c0042d180c078a440315460195850380c05080003425240d000300410117841044108001c107443d42c8120030030f05100a03094840d008600c0014602511066500000b2120089004420320213180c0c01489030150f40705102c1001c1c0e964039007002ca980c00900c0060480d121005d02940c06500a440c42102c00942d1001d84d5060300c40d50340007481c0120281c02142c05841c1120503c007525202d000440d002d050302c036030a1070071306145540d0003231400c015481e40d07112a40d00b840680c00700000d1900b968215000d205110b034607032030190a00340d6000b10448003644541100300032800359 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 871969946 1250 871968696 871968703
    0x17070b0109140412020c030a0b06030f0601082d1c020f0129030307060e0c0f0607080a0e060d020f0a1b03080a0c05040806041401050708091504020d060e010b03010c02 73
    0x401d078000303903502e032990b5960b200d0b05940140c100b00c40f001d6000c0d20180d50031135901130008440d035030b03c580c60400d10742c20440e0500d49060460606844268072040060203a410b000801d600b49601000c2d000d100101500b0000303195a41d2904040c00c2031040100018440025000802900a160742101c491204102c0034900762803160f4100d09070750040d8099961030701b18100c00c541c981200502140c2c6070021990700c030b100f11343c9644440c1c9003e410503060b2f642c1c607107840700b88104491412141982040c00c1d50b206c8804c4c2d0700c05e410110041c03000c1d001d130701d010075207554054440c03400d002c0b0021034444003405607070411a8040d030300d44000a20384107002d82b111801c1c17011404601c0d030507994040186c0e403011224030051081e002642c3c1840010320000901d0101089020702c590301c6540030b80c0b03080f08400281400d541e00506880144600001002800c072400078400c419000d1880b1400e06540b00c50010170109160510b01400d6a81018210000c45005401041c01c27901c040d8000c20448005480c02c90320b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 871971196 1250 871969946 871969961
    0x20a03150b072306091605030109020f060c01060e0405010b03010c090602100c0311070501060e0106050c030304030c02060f0d09020f1212090a15091d010302010801180917070b0109 79
    0x5149414010341d00440e040c80510b106024016103c040b440400c0c01c8454500003085818a202d548240d0b5004010210a4008002000c080d0024044071020b5400560500300f071105860241b8408146c0e4031081f03000b5000311005054610201d02141454201203001c0d05006500c18083d40c00e160200740100c0c8648544001c49419601a2641c0181264400017170400700c003a69041584410702450f25903000300060405910803000012058a031000c040c20117a0141c6c0460f003481424401c502c440380c1c2c040b0444c1d911940c1403801c1c42c48002e552000840c00e000e002200c4e40840030108000d0f0ae41d1495600c5202014004c0b02e00442d000810030401c0b41039400501c00400c207801107030300d8501429280014280150000b8200ca000b5a2598000880d02803844011030000349031031810080007034104500400e845032180c5241c220341c15500046c1c00042c06110340300c62003006031108d040081883d80012202ca600250307801200b12104040e4000390014103040d52841c014400015010005200c0e0f0f41 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 871972446 1250 871971196 871971209
    0x50306011706010c0506010602030a14160213150b09011e09050f1f05041502010e0319030e0601060f030b01020f060c1303081303060b09040203102c01020a0315 70
    0x280852125070040c03011640240000d8144850001a032000032420310129020300f509a004688030030054100a1080c000300c5400c1520030010040001d030800b0301c0e0140030055405a031034078480e402038084400140780410010401c04070743c10000c0b42201c0c0380d40080c50400c000340d039181c400120b42852a81422039004590003c100c0c855001c02082c10640d4812042c48002018000c40c20a0000c142c03481d01c07180901d020010302c2c0040d062000368400e00c80405e1520070b03480204800105400090303036038410480c5e088619044088070b40c1030103100e40c02010200170000c2c1910207559460720050040441c1c0e120a002090400f07140c4030955100007540b8200c41510002024a92900b4200c411107034021801c6e000010600b075404800720303078181c0042403407145140801b54902d145050400c00c44507509443e501c0b0781e40100521001d0f0340c0001c1d40080c898041400003c030000c0f818003c50010000041c00e45a0342001c4040703003034000041d4040c2441945a4806014800018801c00d4803d400f42c085e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 871973696 1250 871972446 871972457
    0x90723120c010e0f060d020f070b0907121e080a030c0e04090807080c0f0f070302150c370308010f0b040515030c070c030f03020d090510140904110d06050105030601 72
    0x43e803500c0c00352103d49904d90007074086032410103180e9000060744e200304c4030100090000a005800c00c5460b522403907008441c83e010700300e01d03403c088071350550566078240a0312624010300301d10360005c209213400000e00c0e4040560303607683d40b020401030041e00c00c030285a8003240c0c840816480d81e081900803203c0c11503008410714504121a5a085202d070411025145d842c491041d14103120242002542481180c01c001030026929510400c0090211780c0c14081700d030b8005220180002c1c60016095079201c244480300c0301442110b809240048404486070082c0d07104c1d112030501450f40247c0d072141683c0e140b00303d4111017903c1d1044c410a5128500c1400e400241d10041c0580444000d0043c580150301c0015503803410041d174075604190304654105641030a040714210301016010011442d4141090900b4120589032070001a03035401c00300c640005020308000d9800d40c0c00300000454a1041e00100200040c0b9013071800c14049402c0a07403011822031501c000401d0a40c0100d00f0740e44507440c140c0d200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 871974946 1250 871973696 871973717
    0x1060905011d1c110102030a0c061a060d020a0e0604121707080f0c0c121b0301091a0103150504110d080d110d0b010305060d02040203090723120c01 65
    0x119004074003030781490004042d0010600c019926400b04420002807900350400d209103600340f40401131240e5080c1ca0641d4400c01928640c25000760a04088030b8000d00000f962051013402c4106502411543d981d1048002a031070000d50b1456010344010320f983c0c0c0d00c00903004002000d1015500c1070b401904e00009100500200051070f4081c1e101031040e5800c07032142042c2455648090300d41040c6d8910500440c0820700a815442c200a40250100d04590030300c61881ca000c0700e80e0300d481c1c0310815030b60010300c0e46d00850b6040d2000d412040c0070550201e0301c0314000c4a03040c0010031894082c0400c40d07402c5103071103040b240049e08c2d0040b10301440d00300850395080910502001034075522038004a5031000c0c20b0010403894050340c0311b84a0221801131800781c1d18480d02c12003004a4081240f0b00d41814645000c0c005184c903070300681c010f02541540c0c01a40d0b91940c4911a141500350b51001824040b40441004d230070810502081010030103440000b2114a01588030f5100d02c0e480360b541c0d00180000e5603 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 871976196 1250 871974946 871974949
    0x2190921020d0b0613020a020304090c05030420030a02121606080c09130920040b06040b040e04020f0306090703120e0f0409111c050708120304110312071a0f01060905 73
    0x84140c04c000014841103102e0340000511041e070700401000c90260f040400c081040e5400b502420100840519289280d45441d036140b1048206480f180341d4800b81c9900380c0d0740c6030b0b04d04004011580782c00030200e4012000020700259500c808a401c0d4081980c607040000f107007802801141c1c0155210301003035090104180510018014100b00f1480c0c050b201c141c400003103403134465442c400c900d01c4106403441034050030500064a044a103482d000346020841007086e02101f000f80c2d0241c8801c1c0c80e466615071110b0002542c4800074400040e410b000315018020400e45c0081c0c10403c41c0e10a81c003004ea143c8200e001501c2140250301810740002000000401e1880d04c2d83c00300c0002441400c030040a0b11112011030780b0f02c011a044011020f91031182c100510408100b040c000b455a040104426a500c151f88070180c00082c00041c01e6009014803000c4594082c0800141c020750400119114561820000744500c4d904c180e15016140d00c101207903000c850002c00384e041c1e482985400149900c0d050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 871977446 1250 871976196 871976213
    0xa093e0703080603030d020a0503250f03021b060c031b090a0b0913020d06081903020c0603090304050411091c050c0d051507051c02070b04060b0402190921020d 70
    0x3c002980c513000805c41070101d00401d101400311000c40d681c1351500c81c03602060100d40b04070b88942e22000150061450307407a159000351407013414259880c0c09a2a004e202c411401343c070080300b8000f8840d005900800004c120b005004c0c52003102c0030340d00c0c090128600d43d0515101c1c42190304164001ca0303081010b11441c50720340d0003400080b4001d000c40c0ca8a100e40c098080403a04140c0c13403d04078548801781003225031410403244000040c0b008000541180641d4003a689080c0c0d0758419001716408000a18442c8080c42a10700610014105000e4050070484040050303000d414201d02c220342401c0c1340c00701070054000c0c1c100050303802001059000c0080382049050000b1120480e00d6101d149a0518103480700040c46000f070019032902511010301203141080b011544440191035441801001c001c9403114903426045070300180009030200e400808103020b441180399a03640b01704600700030804d45a0206c1501d0071285040044204040000200e1108002c52480658080c482d11680c90201d0b0805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 871978696 1250 871977446 871977451
    0x4080a0305041406240108161b050d08042a21060e0c010201051e060d0206190c0b0c0a020303040605070318140c10120b0a093e070308 59
    0x3080003022480980440610301602160003210f40305485c83c0140d24200010036600c10788400f4207003c4a41d180c0716150703040c0059024001000c000c000250101c00c0341d0224803808400c0d0b0441c0640760403001d880340c040d106490507901201d170017801c00d5032300703030110944408071003407030000201d0bc40fa070b0345407080c40081c40704001300c461187e4001e107400800240361885009640310004000c2c2c12850007040019084400040c030304016180840c41000d444040e4038444c0b5488202101d8207030100107640081051b03405151500c1b5070300c18494100a0136580c0140c0c4120819108400603000c031b98800300610010f0240d040514050792090012400043d4242c00c0700d54000d40c14a000190110050011071a01007a48002d8464004030070a503a0f21a5042c8132805000c0c0e410750b50408860b2004400a01c08170507100f01c0d00a0a6a0f450485d0007565040c010500406800c0070034040303d810231060160140d407886100305034144c100501d60901c1c40680c0100c0300203280f0b14500b4205078240d14290340b0180c00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 871979946 1250 871978696 871978703
    0x405060a080a0f0f050115020703020315131e0203010609061208070206090a1509140d1b090e0d090f060e101209030801031a041716021f02120304080a030504 69
    0x162110b030045a40580716044100700c0d110300106003545081c6551f000202e41410090454004141c188090b841c0000c1e5520f08001001544100361b40c3c0c45800510300800c118001c0c003100054000d0900e00040040380082580220002c1140d50350700c10464080396150710400a000c1c84264048c80130070890b1014001141c0094041d83ca40f100f20000035100035190381116001d0000304a99101041d401658074010b80521500e01200020040c0001c0744182c100300d0080c08151502c0325400c10b20181d810101c014491a1414407100840e1072881d511180160303210000912101c40000f02c0c01a41c41c080c00465520351940c2d40840e00c40424020f400102c40034410078024860b4204080ca82207204030440785019543d11a069415440c001c241d12090000701c2d400d1418200510001c542c00105544000b50f40c912166525411404420603c54a0820195001121502c03c4400584110100620005640c2614600001d0081442640c0400d58000d40305c00d006000112420b030080d0300c4103401601 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 871981196 1250 871979946 871979951
    0x50111030909012709050712110312030615120c2b060e01140f040507020a050f060406060b0f040308070807060f0b030d0f0203092b0804050907050405060a080a 70
    0x300010614100b0b0a9019420152019091066511012500f11501c03a0301040030701034450186c4032165106101d0003051052103017601013004101c84808050018540070f0700b92180c03503280c02c01d03082c101c2e0000c44200b8010301507a1403000d41e41514804442c3c540c9071101ca00d0a0310303110035008107501c0c0c0220b4a8100f121030b28000c11954801503038140f015420000c0c2011030760f14180300601c040c004041e400440329000400b800c80c184c1daa00000d40078a0002030710005043d82d05c10000b00d11b0300d6400302c0090803500451410300d0100b140032030080c1c4031340c0c0941418400302d039942031060010303c44e482d80340030690428001400007480000c0240f854501556441341841410b440e42e200f29421020f40008107550f8001030004c41c1010b2142205902d281d0414602c07040103440081c1d00e0344181c410b074038800c0c8100241040c0701c4410010840d4809080454032421708080e141601255015004491180d0703080030010b45098070910458040d1403024140c00e0412035000419954084041c00501c610358 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 871982446 1250 871981196 871981207
    0x12020f0d022508030301080a03090504060825120602070c0e040b0703020d1119020c06090609040e0f030a0906020f0610030b09011e02043f1e0b06090a051005011103 72
    0x80013000594080c1c00500d001e0256030360980341c00303010742e140d5600c40c1e4000c608041e0204002d0750041221040044450451070b1100d054400980080c82c140d008070760707030720010300d400d00131301460f40c1c080c004c50703481000210815500c90b13003c200c0e2084d08440003048803180344001007115102c0c0d006003044140e852400718000107000c03210111904165030f40c45010300c42ca0000c80003203504222600f03908006494240c40c04042101180322071180b0085103008944814401c0504c1c51308004002403002042d042d00d49070014550700400c01c0c2950320600c0300612400b41d400c1042100807402a0050000000400c1b800f861548d440e4001840201001c145558801648540c4200229140a0b400602c0710060f919410080d00204002ca007041030103e0000001040c1148004a6968520f102482400a600555a2800251130711540700c903008000b844000200420203c883c05a0261108803038060b0b55940b449402c0301190804c6851144c04840c07803c08002c41d50203040d503510300c062014240c0380781c40d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 871983696 1250 871982446 871982459
    0x30f0709090611032715150108102603040b030a0b0a0e0610030f09020a0e010f2306090a12050c10111b1507051005061008010515120412020f0d0225 65
    0xb000200e490340d41c03001c0300340501f0510f907030b0000d0000e0b1710900707114034102d150b0b007000411240d0310641c51400b1440750110303007081f81409003017060703034010301ca000d040954926003003035108040c028072015140039525600e40800c2c0d190108103198400c0750080c100a0345034a441c0710031400f41c94281c00704071041c0d41d140141400b50b21010031041c090108001510101e5141c40b1041c030700b030155a80a0101c00202d41d1460f0220303022002c8620740340720115600b94540c035580b0002010822658824001043c1c0304280804110b00400d1150b400c00085400c450100c01a41c030070f889400302060400c005401242d2594280007965400400255025090070a07c000b00c13100c02103640d100481c20385696014841c201415440382c058103074888401c2c8c0c0c8680ca08000510080c00640c810b006852003000d074100c00f018031110038801e907040080c002818040c03e0415007400c0ba1074450003010540140294007401180c50000940649448401c0c0c0c0240410310b410408464000308000d001282d4205260707001902 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 871984946 1250 871983696 871983733
    0xb031317040e04060c080106021609020a0905030303040f170405060909283e0a02030d02160302060a05100306020c0a06021b1501060815030f07090906110327 69
    0x910f102e49400603400170b10380300c040c0c00208140e01000c210740c0040942e441081d10f124841c41156084840541c4410190030265003640c256003115805220100c200400e01100301e26021016008554122034884100450685442580110341d0444402c06c40704010b402d0107018142e1207169035052641c003074000c1e0300710401015010207015206844040420f6140405c4124400c1e0b21041039004645007400411250103240c0305809040d94900462500c03c094028801c0341e80c0e0200d0034400710356904000072240b10720042c00800394014419000000c0580c3c0c2c0c00d200d03003402070001084c6505c0007445c59441e400a580481144142030003446031140014010b07001a00543c0507005802e4805081c0b542d0380d5107007084101510a02c1c0030b5810040064076002050325030071034000c1d44800983c9002c0d1012a113070000b030385d925180354030640c10f000409519640c0160822031040b0000d02404400c80c8510f07089000507201c0c0c030000c44810307402c2c460a1504948075600c14032000c007030360740519401c00f0580c0b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 871986196 1250 871984946 871984951
    0x31b0822061521050d0c03020a0506070908010b010309050c13060504150501080901020a3609020309190b070318050a03020604151a061e03010f0504060b031317040e 72
    0x44098099051115003c40310505050743c40400360407412040b540c0f24640d85803400e068240034800859001c5080c54801c0c0a0300f901d0607008002c80e000e034104400c0c003c2900c0390601c55070405510f0420040015846805000011b6400c8001092044580303410010b003000c1c0d800501544580e07480340081c980d2200c0c050040040c0300c0740390304850345203840c001600d0b00c24020100d245a910410200d000150090140d60540582c1c8002c0c42c0310f5101e05811007003441e01001041a01e480d0b001000501d540701d0740045200340440320941d603250351644040c0001c46134170740e00201403244060000c2c04a07480380d403121011801002550041c80f00c5038403081c0c00c021030828140c0041c2c004800304030a019510100a10100c0700c03500802c0907000240d00a8900c0078a80d05140c800d11001800441009003881c2d0800741c03a10500040c2d50301e50752201905000442441558000c0741080400900800020705903442101411784500701031700c1c9a03561141c5002c6000007103043c060144808202c0701c0303141c0c440740d1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 871987446 1250 871986196 871986221
    0x16090c0509040509100c14180f0909061f0b0316020a0c060203030f011a2d0d090b060108040305030712180302031b06010f0302010e04090203011407031b082206 70
    0x2004050004080081d030340401030f14007d000268400996002d00d980031039420070308048140c1005080c0d140003030140500386841e10703484072401050010112011a4842c041c000c854004c001866844580c00b021001521a5100e03a071000c2c40010b07006065200000000651807056840f10740350b035603a481c501c00791034000100507400031080100c07021075003141a001d42044000f642c0d0004000407040821b105080e003002010450885024030b000e000c001c840166038040500f10740700d050241c0b19138010001850305603001c1c103030140880c98650168118501664265862600e0359035401015120b5001102e040240c0554550242c00044d031085800045144207070b029558030fa08441012030802ca0f00c04980e00750f50042001080b540301900d000a08983c3d0a0130725540780e01028002600070f003400301c8040e400d9424144104034035003d04101600c1100f10351010083c1c1d180d103800c0740702a8041c1c1000007001c2020500411054800040190003101614804003c10480381c1d440d1002e9032481a20749 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 871988696 1250 871987446 871987453
    0x604080304030311030405152a0a0b0a0212011a04080610140301060f2709080403021017131407080303100504090f02122103070f0216090c0509040509 66
    0x40c410107901c04d01c0320410700d000c54003c2d810700d0305090008180d00c1420041c4640d0100000d0600705605191500410000c5001e09016200907021185a12440d0f0514103d500c100c1c0c400c00503222031003500c2074811080b05400c0c00c1002e42c0c05c040312409510304500043c64454000c0c00006006d400800c80380d84213500140c0107231540c40c548a59003000840e101c455501c664100034050056628007030180084a100d13109141100c201143c85d202200d81002401c000542001285002d01c4500e000600c2104d10036a87d600026401035802c4400e411084810800780052a020800581c14110220850341c06400c0e0039003281c04507518540b500000ba840000c40d5000402004504260007004000900098809200b040d0290b0303240b00102c4955031009104101001c050350280c481000f001e1280261190050b4100f000c44440c142c0c41e400c2251030b00005034074188004030162000c00c0d10132040328100c001c500f19504203030815001d000d448121804000b401e10003c051f80da9a4000c1d94013405003000035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 871989946 1250 871988696 871988699
    0x2210a0f0504120b2a120c27040902150405010e0603040c05040504060b030a030c02090105040608031b120d1415030606040b03010209100c05060a020a02030d0908070b251b1506050604080304 83
    0xf01b43c07143d001000c6070003504050140b50130040401001c1c01c1e41d0400030700c507070b52055104000038004280110020350090070001804c951a40108014016614240c981d10b462800a804000340d512046400600e90400704030304010a08054001d83c2e003040c481c8001040b51840d1001280c030301100f075041503000800382c50a070070075030400c03460080c09040709507014440c02e801d00700c91640ea4030440250044500c0c021100d080041c1e0144500c4009884480c10340340e0b9241e2302e112002c003038004511107a81c2c41c2c0f103c4012a5068045490005502502034090615942c400040000070f00f194882c0c56015502045500c01c551741f04004415000310644482d20540c04500300545888402450b42e0b50302d61040001c102c1941e00001038400d048804036020681003040e05d800e17a4030740901c142c001c102c1c0e11480d0074800c0d0145920140304004080c0d00f0088249100c4030403c8406404440038491a001c40980380c1c0c012800141084400d040010000b14081e955070000c0744182c2d1241e40445240d8101080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 871991196 1250 871989946 871989967
    0x303091c061d03090d0804151205060102030403120813060f0c03051e1807030606060518030c1509040b03030d0509070905070e1002210a0f0504120b2a 66
    0x18104103400c0310b00c000d1211542d41541c950fa0b0348107120f200341c407981d0501c0c0e014013000500412140038100c1c00b02c42816401200d8806400c00d00d00b04020b0041d1407c00300007880c0e65100000f50303400c80303800c0140c888600410302c40581f20345802402090703c14000c54845808030b240c5000c2d10030515401d400015454100c803400904031030b0082d215100e0f40e0800080108000b4031030360000c1c0c0041c1c0c4003d0b010940c049d81115145820b0003075100070041d0f420131100003005900000a0500c41e000103180e01a580c241000b0151202e180742050359001000c03a030110604410314010b86141e000181c400601d160800d4002803858102d48006007250343c0b0b400401074240c8040c0300010003846e102c00d00740b01900f450380000e8039060101008500644103411580100c620030054101201c6410948681c00032103440551005c0d48048049004180603119031035040e8491780c01c40342124103420500d19000003603a9030400403e80a081c150700c920021070340905429007501e10181c540100085556a100c5080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 871992446 1250 871991196 871991201
    0x203190e031c02150103020a0e071b060915140a0f060e0112060b120d0c020402071a07091e0902070c05060f0315060301180525080117010522020303091c06 68
    0x2d845110b10b00c4c8100400041e12504011010f8030488280032190f5a1a003504681081103c5000040c10404103000e40510400340d00c24104140a84084030000a5650000d015901001c650100003a0000e000458106141e44400090140402e000c100329559034011a0800c4082e0003220040d20f04103802c80400c02148110300f91100140c0303040c0f12030552401075a848000244040d0240200044500c0840d0b0702d82e4100d8151a60241e54071000d1060052a43c0f20f02d0001c44400000c504038000c089005500d1400c81404e074107002d13518807442f0f0700700b40c90907020f03420000c01251460403000020400d130362010041c226151a06d244183c4a152071485d100b00c209080112600650042006100002c4000340c80e070342d000c054030808101a103c1c14880300c000e00500410403030b107035440c1e0b224090040c0d011940d40e040b81c0303d5031001e00307800c0040344403c0c0c01c03104181d46030001941e0100d5458031100100202c590754500003415a03090100301404100030411785520060450a02c10b40d8100700100361 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 871993696 1250 871992446 871992463
    0xf08030405030601210b10050a29090d08090a090606021b04021c1515020c03010e0c0612040614010906050108071404090905010608100e06160203190e031c02 69
    0x2029403104101310301c0b03890290681160f170060041050350000441c031071180312002000f0300d400307070940c2001940e5283c1c294071401d19916844c541842001c007858071081a0302a02c580240c01020b200c1d00c1e06441d075440c10640d000c03402e8517401c4190f00c0c00c002211921791140b030000704841d4000d40300c02440900c030b00300120384441841d40704a1060100b003c00246103100c046150485807400920a100500000ea000354070303611401003508400700c1c01c02d96a602294000c00d0400960007400071140e02240b00d6243c15510180c0c580060302401a0411451403180440c1c010303004140014000001084580034031000340c00c01c050781a00c80c1810001541d100344880e5200c0c0c0203140c003040b28203121100d802248070300e1040380282501d403c15141884000e40c001402400034008540030308940c0401040500040748090300640900000200554130300340030503d140306258059482d10700301171403005c03082c04005018000c11892071940d44050f2000c20610098000041c0764544940c6001d800a1500011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 871994946 1250 871993696 871993709
    0xc0b042904030509040e0a020d060b010311280908060c03011505120604270b040611040602030a0807110312010e07031e0b03210304020a0501030c020c1005040f08030405030601 77
    0x1110400001c01c0e4003c0940d280c01c0022a400710303400d0711740220145045800d80b0083d52140400c044082000300b00e50140f003a01d0710a80b400d1080c0304010340c0d54000c1c0d018014200c000c0600c68a0007442c082024041464084818248102c0fa43d407075001082c0340010880392016015030010041c01a0955107514807000b51891501502e01103910040b54080c0f00041e01c4113010700d0b101c403442d91204013403003210881c400101042e111030004e541003184805100743c40c240c851600d00400b0405003ca1a030885050301c90316001945448c217100400c0b2514400280158100024088003c49020080c0700a040c0f0152881020310300d9414540307107405d00035000d4042c00500d45030840e001c4107044400794460328102180740000c3c030383c00c0c03c1010034101040c100c0c0c0481d0121000e6418040b40e4456805140194003c4c1d41151601b41c9800065003156411019540544d000000351501d6281004000d001c0c100d46191403400c0c1a95002000203510b0f05400555503504049801c0c0030300d0804000d0140100f14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 871996196 1250 871994946 871995023
    0x17010302010c0b042f0a0b0c062404050901022106010f050d0b100c141f0b0307030b07030903180614180a090609051e0c09010c0b04 58
    0x2440c0d001a28806044000070108410702000605100b50540103501030303802041280e006220b51040703068050300e420030705803051040c0400400c281c1444000e507074031850828000d00590f00c0348410700c0e02082c0c1e50342041c0d10810141c01300c81c805480301e000d001c1c02002450005600c512200c2d0200310b201d01c45d0081103004821410810910740e0b4044800c5150142900703055584840481441010700900602c260304007100c01c1a035000342d580410350802c1c0a0140310b014074450000d5000b181c4131151a041c0060105060b1400c200e2440a03a00120204900030100d9404a40c0c1c1d94540151880440344080840da48180150074180c1118480c0500800c01c0030060505090450150150b040410180308601011805e52085440305a1018010300018241e80c6810340d83c00403031000d04928060042901e05260124006407629000c1c090400d5801e80c0d03045444e41c0d1035402595533000a03100754100b00e681c8a000300820340b1080c90314003171400781c103070b055180480e000440d101d58008011505002c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 871997446 1250 871996196 871996199
    0x20d1a09040201020d1d0907090501080a11040527180f241b042405070201140f0d0203040b06010f020f03090904030507051f200301090903090f090501061701 69
    0x13a03001c02c001d03598211130700b0b2081d511003030f10302d02c44c2e41551010351240d00003906400340035501e6000704105046400980e44c0d00360540d1902035400c1501c816070300c5000c0044003484140150725121804001da194042800d481000c200307605040315250581d1450016681c1c0d54901d20b81d40707801e2002e0445403081d130004040100b0a40034050f4580300c509400450544070b94045413030081304c40c0d039000480b400c1d00c90f819100d40e290401c038010f03090840e110609400d064424010846c3c007030400c0d00e01c0d0b40c1d0141c40d5820041480303124850b42d50302844200103448000c101403290491a8400795001d2170050120402c245058400505403400310100740341558441d0155480d61300000003120a540000c0c2c0e1001e99075211860140c9190207100e500408a001d802c1c590210703031414131151190507034800800c1c0405204080b0030001000700d0400d02c03241040802c014401d100d8250400c1c00514843e01d40300c0c8402d03503102c1e1841c440e000b0541143c02542d84410040103102c0c0e0282001d030000030704411800aa5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 871998696 1250 871997446 871997449
    0x2030f1803040e010b09031c0503090105060a24020f010204060309050f0613060c0e090c0703020105062d060421031d06070b071101021b0f06070813060f020d1a090402 73
    0x2035052103411090500043c6a80301b68609000030300c2e030280100250740400c80b0400780584941c2003242d10540c076628240c0068424503202c08103600711030b1600b052141d98074201c0d54610b070543c14080c51905501c503960414a416009200500c02407039207940001c0c103100d040c5041030070102402c2200c0c40c6a4803d00a01065003000c80b09101c0066106000050074610344000717507040f60052049941c00200c580400c4041000c40e0004d00203035100382e00810656540104001e01d060082440501108115029003195282009082d1096400a0005007010b50780c0c0c020841c0b403c1c4081d202100e440c00c1d4000d84042507004540482d04140c1c0703440043c441a03800f000304109018a0401410304405070012905590080c003e10011240c7c0344025503481001c000d402c0301611150024000301d101c0d840c0313546007030140424024040d014130390710100152101103595442d0740081100342e0309940c0ea080c8211140702030b44000d1071807903408600401c1000140745014003c03c007400015008401450411005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 871999946 1250 871998696 871998719
    0x108010203150d06150f0e070801153c12050411040507171609050102013312050106090606031a0922080904150f0303081902030f180304 60
    0x85031000d0320701c0c05181d072180c240a4003078040911030b124074000c005e00c04506080c440b0040b0003030740d4042e0440e403820349641c0c0301254245024410801100f065038021a107085c0315030810709031911042104003608510500440003081848c0f60300090114000f410792480b0f42041c602041032200b99010003051601f900e80642c00000080142d00c1955201d000400d610b00030740c10110090280114104245400c14000380500c2c5070204040219000c21030014403907105008502c0c1c000084160074001d82d000d18480c1512426121004100703007400040400d5881c0b818100301020ba004400204203180340c001c59204990396908030701c0c1090300b405020115500d07030042c403170b502c448182d41040e003503541d01d001e443c4805034003094100910002688002807205040141840031001c407010403503042c2284428902d16001c0c811030851989020040001c240a4022140d01c00c0758110f0b010f0f0b0302d00314200c50705d080342d00840d045510b0700310581c1400003013031040b03101e4074901071414005c5140c40d0601c00784220 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 872001196 1250 871999946 871999981
    0xc15160809061b071703040f15180807060605270112020d24060e06031002090a09090201030207020406060206041202011a0402130902030106022401120f11030718050108010203 77
    0x11107200141400c200803180110210040d017445034580c50307081c14034082e08044010402941d02c103041c494040180703c0c06106003071105840280c1108000344aa51b07580d243d80148070705481c126928a00040c02e81c40d42514450344134a42600d1011003903140c46003071444041a00304503940402c00a800c00161181d42c0c200d200650000c5804c55072081c44d100022500b4802d0040c0303042c907070504200040d0201d0030b41400d80510001c50079910101c0c481c1c41007904900400a10541c4a0b2800c00204041012030b0b0105030020f0040c94091f180c07424503000b2500343c1e58580d000038010b03801282003100307111038071040f28458a85031000307000c1301c0c400100c0581c00c8200300d070701c0a20072a070005516030590184d808540023000c00359070954807581e590b00040c0d11689208203400c2184442c220400b441002d003804c9a0588441a102c00e1000899444520030743d40200c00850b03200214003001c1ca00c0342c0c0e0030008a00180b04009a0062068030140c3c0c0c0010f40c1d4040e401440a41e00606c00d0002c40300707210300c0480 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 872002446 1250 872001196 872001241
    0x10801050907052107080d0f11030a170a0f11030f0f2a0d0c08010821070f08130801020301140306161b0b01090207020f060901020a080c1516080906 65
    0x20304c40983c4000720341060720560268445100700d55994000079040f040040d01a202510740148040ba81c0300700700e45902c02c4001e4138000a90580c84811100b2150715841c1c0c1200c040600058684002c002000c1110961001c1c40115140801040224004a00150f5111140e000c0240300c0b0300b010003400322000b4252012020880c0c001030344071503a14607141035a071065603a02090040400b0a10050b154a60a000d09202802400c9070307c00c4d80b551aa00c4403010b00c80a4034610701d024140d8030b489800440d01e070703001c807100c0100300300c8001740800c00b19508024110040c0010307503d524020080b1081d41c0c51502182c0680c00010412540741d4071405004480921400d00910880e54038140304034034500360710b0080c4050040000801c90710010380c0586000e510a603240500680c0100400145000c0c1101c42030040c2d0007860403c0004041c840500301648904045911030031501e40340010490044425504101c61450052403c907071100c1c445030841817101c06000c0500704040341c11030504842c2c6825 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 872003696 1250 872002446 872002489
    0xf010e0603070203160819020a05030703050f0c010c02010507121116060902060d06030c062f0c030d05090411040503070603050705090d050a05060a1803120e01020304030801080105090705 82
    0x180b040380c024021600e404107422600c240100e003c0c501004142c2000c99080441c0005406e0095000d0001600b44040c2e40c12000443c2003011555040310140d1080341c0c0380ca02c0380402e003d0a89002000d000c2c0d01c0e1a804940c0000c190b518100d40000e0802c030403980c24101c142d04254980c6042d00d9420102c9000810014960781c40120078103041c00035151a210003500030030005070741d12014203564400d030140c0c1d220721070390f0340d540d075807510102e401241d00e035411502e42d43c0940710700549081c00064001e40380c640d00c1c00c0d0340442070040300113030420001d03484440110345e0005e40a5000c0c9880e11445500203da0b48080f41094180307804a96a40d10034000c010903d562680030825040c0503400340e541c0b07540000c1070802c07410218600240c0f5a80003000c100c402d445981e0200d100b0b0f940501810314104a050190081e803042e07600c0403541d01120403864890035075200004035000d1000e0000714407550094444564070f524000120382156401021030701c203a00001c80a000310365421030769a05020050050 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 872004946 1250 872003696 872003701
    0x90309010e042705062d010909030c020901140307050a030b010b0a0509150a0305090c010f0c02010c060c021e010209060306061b061f080705060a0f050c070f050a050f010e0603 77
    0x4083c4030b0410003140c0b6490f500c9610400204400083e580d0300c94026072840c5030032a00780b02d60070b00328214010691901015031800520241265070700499419019160003080d111098000c248001c41c00e80141c0c0c0a8142010181d01a003020415500200400e8500e546042e00d5601d50040d444410b0190f000c06060008071a441c00c0c1c41a0260750f5140030041901c2403460820740590701c154810000c1e10b003c241081d000502503070700460480c405140603107070b08401c2108a10b00f00c1c1c102d07107203400890500c180f0380e0070400820018483c1002ca03090a400405800c04012804800d0350803594160320160300401240c20b09403030360300c01daa0f0010803d6030001d45411043c41240d0f01d40e00403d0312104144544020001d40702c0c000200585a603050081c00c0ea00581c8500855403540950301402d41c00030410402036442031721031a11410a01c0440c9050b6080200041e2464104061030340541d2070000c80c08414800e603c9d2601011008140880e19081c400c01d2180001e40130804480701c1d1480344401200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 872006196 1250 872004946 872004971
    0xc03060111011e140412031d0304030b06030c0604180203070c0212070509010f05011b031e0f140c101d1002280c0602070c0506071505090309010e04 65
    0x16000758a403854000c1c40603c072260003807041d10360511812aa458105048a00284400460540034940107000e0040101d848030003074000c1e200f040040301008072110355015400d602070001d08040e500c954640c00e09420000201843d203003811005230704c10382c0c00f0002088800c2c0a000c0600500075803010150b1070b81e0340d42c00142c8240a08c0d0f003001c3c1d0804514042600e640310085815819110300701c3e1100c1c25a41c075440c0c00c03010707000a4010240815099000002c2d402c0c0c0392100080964468a4107078440b04900c400c1d010314a03412224030001c01c010f81000c0360595049500c03d070221500c08012414510210965030b912481c4420310360301241d5584880d80409002d06000b0340101030341c0b0490310888148050030000350b1040c2120486000d0b0914204011113141c03091400303003c616035420030076100c1512500000c3d84901b004603444040b00f94002041d40703421004c0d000c107e0152880004403440c4446240a0310750040205d8541e810402c03040a5580c1c01078100311340b89906583c0002e41d65581e80 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 872007446 1250 872006196 872006207
    0x10e130206030115080a0c020c01030b060f070c03350702030109050601060c05010e0d0c0b220f0203011a031903140c011527020c0109150608010b060309060c030601 72
    0x2000a90451030000010540c05404507040400b00c50550750f00120b995900c03000d200302d511020646005030001c020402c0558426044130010440040110f0319003d103411a100703a55018505c00c88141c41c1c48041002400110488c0d150078803040b1a0004510820943c0341e50102d00748640d5103544440030031200f082d07440960025243c15400012a0134950b1580b03006403034008002e070100d030650f0805180c06160240450b14900f000d080d40ca508103840c4036a91005c0d001c4400404841d14004002030761134000005603442540140148040ca50700800c0d4018903003503d20004404055882d61a04040e0589000801710616114202640140c609502c0d0031108600d0300f244440000384042401841c061041d40082c96030660003540c4d11080e50b88500400000011000c2d2080400a248141e400d5058039002000305114031070002a0000c007961b20782017004c905145610386982d50325402e0029810911890003443c40468019040d89000b00d1030941e6410001c10401c84c401c0e0220110b85ea60f4001d1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 872008696 1250 872007446 872007481
    0x607060f050405010519020403050c1203070b0f0601080a050709171005040c05100807020703020607060603050d0e03280f050f030f28020a17041a09040b060f03010e 72
    0x4441840242401d043c05030181c5019107150a01d00100c829481c8040c0c0300e4130880301102c1d4840c0242c4015074850b420000d4601e1034075041c001c10700042110750300080c14000110300c030780c0304500e111942d801d00c20001000040300908141c081d61038003003803105458000e48020100d600d110101000a4007803c0414140b041c0102e40345a2175050800388020020605030600540300155117221321159509811030700844180e454402503040302c0800d0000d030405400621545005410100b204d680d01d039640791500f43c0c01440c0c9400980314400c102c07074503d0144000c03400e48005120036454800075080c0c24060300d00810004105029206080c003c010341800f400610034210f0041d20707181c00302c0c0c03100c0b0390f46503202c21603400d00342c00ba02030032010340703082170220441c61a03140e8028100056540e0b9665408541d46151050403401404001142c1000a00d140c01310100501d5880d02d42e040c800030301c010348258103451b42c0304100a001c0c0700744400c01da0017900e0444852001407462a00d410744001001c05d501c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 872009946 1250 872008696 872008721
    0xb011404030c150c031b02060f19030c020607120b0f0a1706060a0e040f03140c0d121404080703030b04090c0302010806030a0b0115050c190b0a06030b06060706 70
    0x1040020511071440c0c1c1032022100d5543c0800d2048980f0314049a510091001c020081a49850400111500d40503504001031024003003526228400d911041c4642080070040141d05900c4861001e40380c0c5800303490a482c1c0a40000d100604141c11301500c00b02040c0e40140c050b560342c2c40350045507503504e92039442701000500351925854440e9401e40c41c03903c54030710364000e510881d000b0074041d0801c41003c05c12100702844039081e648442c0d88520005084010541c2004008540540300320040401413289003034003001402c042031030040242c4203080a03590520070034504020900400c6030555100e03807066000900c1552404280703030a0740207088100150381c02900d42501d40d4100300e440b40c500310580e03000741c032400219a110010107a0310111540001c0080031403074010010b94501a401d040c4010b61803d00a0800c00d00f039074910310701559111620b80050101c541a401d0000d40c0604039003000c1461420b0000a04544409521907400342c14940114400074020703042c062280e00c0250802c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 872011196 1250 872009946 872009987
    0x13142e330306060b130803030405031b0f0706050d060603062603040e01090519410a33060815040510050a1d06040b0a03081306120c120b01 61
    0xc407900301c004c00303410035004200b022060103c042000328001094070310423a070140080d481d02c03046108440d4003003502580001e05208001303803050001d00038460000a00740503a2400e403940b845c10151000d480090f801801494500391083c4000c443e1020f0741582d180324142d02d201c62840140d250f9181d8421940070003401a140030000c2030145294016500805000083d9650011110200780407520810090340d4051071030745110070f01016800c00b01790325444880c0c500c10010010310180100140846184094a540d0b030f400c42100012600c110f1030408281c0c020702c050050490035403458071107a000d01d4084c03219400028612000040003564940001f4100740007604145620424010a60081038400d804511005c40c18018030500e904c030301003991420320359a44544040c4002000303800c0c03c2c540c00c541000408404a41128003c04149440c02107a888580c5085c100815032a0001680a943d0b42024507448080398010001101c0c1c9118900c0064540b01c40001611681981900300c105080e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 872012446 1250 872011196 872011199
    0x626150a050702101803081005061216030e033112020a0503011a090402030f120d1107020907120605100207081b030613142e33030606 59
    0x240e407904102c0c09111290201c40c400109120510241c85044410b103a000c0340c10040341c00803130702c40c0800c5908003142045004403243c8031070119400c0c0d440b55040c0c0c0311900c0100c040c0000d855548804921034801850700300500f40d4984109902d074414400d4440e40d80303020043d1103584c4030b40c2071f0040d440b02041c00481d00c5010f40e212a51100d60b03503c010143e00c42c0340760f440002401d08040c0180c100f040156010a903420b0f60880811600040240003640c25101303400b1484428a4104080c020f4000e10003007141e11588040d0f002c20950702d45840f608000307070303050181c00700517190b02d0b45c2250498840e040041f011010a03111400030400c90b44443e61024034a2004101180c0204110701a07a003048281c83c0c0c00d141240540304141b100b0814250036602c0700002441c40c450369004401240d1148007072803004042c044000c0e1800c0f001c031181800c0088010380f06000c268040502c01c100c042c60903424004040c0c410030070b5a01802d13429000a10038207a02c0100b6031114420480350155a00040400c400ea = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 872013696 1250 872012446 872012461
    0x2090307150f09061b0f051603121e110f0607090602120903120708040e0906010603050f06180705120108070e100b0405040b0d050a060e060703062615 66
    0x111540000c034042088030b0789442e0303100e1080d002c22003a0b07074407612801c502108100b030201c03107a182c5a806071000e03004c4140e00e40028009124014541e205041c826000d1407e41c2825842c1c000901110380030301c071906820401020340111070303041c552107508014004c0802401c0c06401c2855902900240c0d0240c01c08200c0313101c0c0c2000000061754816800c0755180c0d0031040c86251280301c0c0d4010580d059010524488250183c503004004151140c440c2c2c0313091a680d0360741050b50800179034500300150010401802a503500d40f0903290300042000000d512401e04101007121802800188001820b00340001903082d40208121214511020000c81c401d40e03483c18003c0d00c40500d805079090440411004c9145440328002440540d240845140d02d0a8a07042c00c000081031144d0b516600f10b040d140c80c400c0032840034003011800b68080d010204416401400e039604010300108502c05044c940b00007400107001c40004560141c03000340c00c02c40350b200046509803910742da41d103410411040180411101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 872014946 1250 872013696 872013719
    0x40609090303090b1008071a0417010902100e013908070c05180a020913020d020306131104060c0f0602210c030103030e191703070c0e01050a0e090102090307 69
    0x854004d070419007203602d400c109070010094070711400d00e0325070000300d080c05078045005c5140301b403c802443c800d140c15690341d000003100d01e0301060440c01d82d5580078a2025401c1c0343d0303006071007964585400460345480c4c030006003d42507081c1000f080d1030001c81c0b10340c480c000e040c11452801c851030500002c05004a150030000d81e07101801c00c4801c1400e507080010541401c5420160110106681d140559120710800300250000e1260540c40a210b080c4596840118401082c5c3c1d044d10300005039880c60b01c042880780c518202c481101700300b03140c01e140e050a4001c207400d072030071b5a50924102e1361348815810810b030012101d220142a280c4000b440300c03182c0024001c0300103d04d0b01a07031102e100c0c0e640e0b0b1602600c640000d200c01b074041021030480401c3d6142c0010303a450041d036105800b00e809501e4100c03001e40c190383d070402440075902c001880700030b0006038109d9178020100506170354450341c1000081070700e00080f403141044034219071022503200e01080d01070302c03900d11004d0200d503075081e03071014110380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 872016196 1250 872014946 872014961
    0x91805070504020a0203071b031205040608060307060e150d05160f020f060f18060403030e280206072609090a0515060c01061820070f0b0402040609090303 68
    0x96500c915840014541424001c1e00c0004845801641c101600c585404045040c00d15188481403a2000003100040b4611145404201c460b130b41c10f900c8600301b030400380071f144010700420701c40e03448000700300700180d44201400c45108007980c81d2800180c1084807401076000b0b0840503040c15040c00c0400081200e640c100030800c0c01d5658070213180c4ac2040105a85542c0d124044a082350010000140d0400b02100481e800a500e00da0050b0750000c0c0114050030f2403410703034085000076118001c41c2e90780c202c200700c5d456483d070000c0da4503003245034014000780c540790321401c00038022280070800c0b03010302841a52015403490300500e0b001603c299200210410f81c00303031510070712405c01d150102c0e400f94070500c41d2522602c0d20313001a10707669543c00c00304440741d041240c8902d0070f592501c2c170209020910007070500300f90340d203144007282c0130f81ca0a0413160940c405580315601180c0611564000c281d4850007841c03c15001048004176448070b0003c58081d001f19044030000c0d07402c1c0f80703c00007055855403000301d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 872017446 1250 872016196 872016203
    0xc031c02070506040e0c07030c02030d2c0105041403011104060206040519050a030c08090301020a0e09010b1e03151c020108011401020c1e0405011e0f05060d090303060918 75
    0x114042d4032141000306134003445c05210f6814080c40009089294094002c0074928080e05080aa0b9182580081e180150f0711036850001018042c0c01c424106060a681c3d0340134a001b1f0141a56101c807100003072803400b80d4801e104030f50302000b40c00000b0b0b440039480182c5e54480d115096a6864130ba41c4040e5403580156000c90b400d100c1c1c91110000088860003c0c0c1b01954400b000d001c0c007410a86017210702015050003030ba54184100600203d5550910003000007a002c0d8a6100d0302c501c07107204004010005a001c00350040c3c040000c14250801508801540347c00108003585a80f1801d102c2c00c0080c041c800402c2e040450001c00003556406043c0207482540300340c1e42c00c001e81c0c3e22502960210803e4104c0180940e0092072140014a045006500105440001d00c07440004000004080d1003003a404002d8000000104852810840d1309200c040c22017000303080d0b025480c20000c01c00600c200f040c0c4045165440c0720b54004c0511a402507070013000344000601c10b10f100a070315400c1d4090380c440120b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 872018696 1250 872017446 872017453
    0x6070b160302030618100e01080f060f040b2a0307030e1605031c0c06050403090302130501031707030c050619140114040b192c060a06030e0c031c02 65
    0x180000c0340300380200c9100303d80180040340c101c800c0b0b00352003a6042000e001d070002c48006003030100f102c4d2117501d035044c0241807101c010131044404848143c02c228002d0441c561b0000c05000304030104c1d943d0381c061500b0501c131001641a4445446c0c0168103042d210702c40029488002040c40b00c1640c1c541c021a0301d5081c8002940c8458841e400049800c00291040b0f90b050340190a01300409180c1182102d100b00d42c5060052200c1004e0303460508070340046404a0115080c1c00c414400d608003d82d4030910700d801101304100742d50542e01c0b00c00080108030444100004001480e208140c42120b400034859407040131680c0e5420800c0d038498200541035444c05006250003c070150710401d81011354101d415600d201919000000c00744005050704907801c6030441e002100182e002422000701c003000300008082581c4c00640f600c1750b18070000700c095030b80302c070049004103012083c1d0b900600c0070200e841c141030028900c5a0001002d04000c20780104546c9401103914444100c049a45e005c580d903c941d42c243c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 872019946 1250 872018696 872018731
    0x2040611060709061101021608030f18060615090306040b01051311031812040f03020a090c05191e020304051002190f050a0b190c0305150405100506070b 67
    0x5a0741e41085924500041c0200820010350340a113a20289050401001620702200080104181e1070903d204451418001080000001c2c4410f842600900040c03900507881c40e18414040c1e035518044c01c0144540c100d554048082c40910003207030b40b072001c0a8142d81840c0703403505000d0880c3c0c40c00d20034240119941c905401d40741d541c0c2d20038059542d000426450850301c4603210642d2440c1112004043c0d031040c0c2c01c3d40742c4e0b1000d400e40500002c004004040b1441030540c0f0500c0030202907944412000b5080030858000b0540003010340301d24020f004102007003001760310000c0350804007500307140c80b0119146480060b2a903000c4024025101c0544940481523402002240d031070003c5084c400040e02000140400100e070b0140d03181c06a8050400c5418403038080c1c5800b41190001d880075104124182003c160010060203034080300d0003103090801207460228a48030103581192510b52089540d00005500c83d218400c6400140c103024110342e072661002e1030501c0800c1009d4890a0303402201085 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 872021196 1250 872019946 872019977
    0x20a031205090a082406060706150806160e01050f040308161b0905090f0a0b0c25050d02010902030309062503200c131d0604050106170c0a0e0c0d020706020406 70
    0x214900a0001807c10307072410f0026203d00e00103140c01400c911155214000005220000300700103406028a14000f04400210319405004403801420042c140401171143c000004480d03829181200e4020026039500c1d01b260b0941c4105c00c200c40e00c01071070020000c0b24000c100c158018801c05640030043c041200d42c840a2806503194000c2d1150b02e001c2d403000700c4101c001603441c0c1c0501e401c00e5803501071034200007605000c681c171550181c84006542c98100b0b0707040140f010030031801200d03c0c5240001c100e521010340110f500d034420368200c1c83c02090700060003c2c6c1069081400008040100321180c1c884410f80340003010b405c070720b47d079030000840070484036101c440c404200502400c10082c1040f81c6000c0c1d01841c0e101401c103140240b080420907460030181080244110380c80b5a219100016416080c440100c511400210b03201c41076038003403203c008003915203420b03032026520051640300c00f03561080402440c1e482901c045510190011820204112454000c0c0095402d01e440b9000e58240455 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 872022446 1250 872021196 872021263
    0xd03020c2415060d09111521070207080604050102180a0b070f0c080f0d0f0f1b0819120506040218011d0d0b01030c050d020a031205090a08 61
    0x520701c20203803000404105400c0003501c2840080c07802074a468188242d524031a0202d07161008140c4a50300381c82c03200307503061800222a1a12000a040307460400c481c025602001040004016400d5100c4d03401081c001c40c02000510700415104d8110f520318503003894594083d40049421800c2400139101d0807020340f5100381d011080c0c0d40c11010b42030078128079403038801c61050204402d072036050030664041112441131015804c821a01d00081c81d000094040080000604500081c00c00024146000041d5400200e03d105030b403c064580b006c600890419280c0d030320400d002e40b41040da0030240070503401e4100c0441c07076a5980c5c44008104075030b00c04c0e0a02c000e074840c907012a03449540c0c43e82f204d6410760150641d21002c0c0180c0380150780d8200e602022a44140b0f00c45010346003489400010070421540745400402380006458040028006502194a091081c00020080f40025020020305403003481035503c0604002c00354006907948213841501c030003034508800303079082111050000044c2c0c0359 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 872023696 1250 872022446 872022493
    0x21528141012030503070c140604020f0609100c060f020a0807020106050d080a0309051005090f0c0415030206070501140a1e0b1e0303121509070801060207180e0d03020c 74
    0x10348000c0c0300c00e12141e6003100c4d1030780002e218109007c0c5029080c40800d011410b02841d441c101c4004014a04040c010420046c0f0184003031841401d0400c5840b810341c0320009582d000344041e00b00f4400d07080d040c0c9849400f4101c4001651080c501c042141d00c5815803041c4024050769140c0c000304130140d140c005220800d06500c0380501259000c0202d00d41d024840d50241800c640604280c03000c429906500b00c041d03d1082e1030300c1d5420390004044d0414000d043c0042c000400c0704450070400d00740300c0120269290803910020340301d560003040ca0810300400b9004816680c010440340300c2a8039042c1d9207076004024881d500c141140c0154100c00c0c911b4814030a400c91600000e01c08502c400f14a5401d800041d04007200d140c041c0010300c0344c90710841ea03000c2c62501a0304000d501380030b160610018031a24480c001c00301d0302000100c4004211864022414900b9510f0040940c6d141d0b19801014602404c00c00401681c6d9114180307600380565450783c094104810200269980c00c05010000c0e10b0911a1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 872024946 1250 872023696 872023709
    0x131e0902210c100f0e0112090b0702030a09080c090406270803040c090b0906040b0612010909060510210201030605060a0c050c010c03120e150a0b01080a0504030215281410 75
    0x4805d0031582580151060003c1ea500e0442c08141391900c1c3d904c07201c012009444140141e400801d40180064110418202803c4084020a07802c11380f6000180d407524040d03c0a400b542c3d03a00d200702c10f103d605850a0766201e968030700c071062a036118680645150700884094540218405000c95402c800e130046114081d00200f030b40e03020352200c1080100070715a042056a000310f08120405059910458550081c0130089000500da044c0d42800c8003900c100402c04c10580b2401e250501045289008050000c40c00d001a00020100d03031005a0052407150001c42d4485404105080450341c03000d50381d240d1610600907160804034040042d900c1e94200c035002804a500100f040d500d02e02254800d4a403100ba42d0104c58220f800311140a02e584001d42c0d809003520307150284080b0030f5070000b40603600315182c200308100f546002d4400948400444490014003032044022440230400544950b5080751000b00601262030070059010041036101c10201051a11f000022400107000d11000101e0341c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 872026196 1250 872024946 872024957
    0x9030b0f0610030b1f030e0d0206041506081e011401150306080706020a080304150e0f0613030e04020a0e030d0f090e0c0a23120402131e0902210c100f 66
    0xd0755501c940110745c01c09a00b8040581e01c0c2c000402e0f880d001c11019802030407940181925003814180748031030a022100c1c10740c80506020007080807040011f000c480c513100c214140d104454030000342d01d025140110072004821000000840e04070b0000380362803550031840e01d08019080d80c03100095261005445404090703044a0050000700d92180010341d172091060914480c040070001c0c020f000c850b48988450302e00c1d441290000460f010070049103400c103d242201c0100068103a4009200e0b54401000a006a070089014140d0305c0c02840740480c0340e040201511700858214a0003440910520700800c00075a51000015100083c542981c0c0981c00405c0480d24010300400207507054280c490f11185c80340741c0400340d03a42d00e05800d0b002d044032800a0700e0501540c20180100031420250109400c1c18030702d4240983d280086216002803419140705020400d102940009050300d0500c07000c40c0c03041005a240c8003248400450344e00b040040445090240d625005011a003034030300c400e1010003084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 872027446 1250 872026196 872026219
    0x5060405090c01201209012a060207080d1415040612020f010c0c06080f09010c0c020f2206032f0405250305091c020c090709030b0f0610030b 62
    0x14890070034054011041d0410340e041500d445481807800700001d45016501c1c05c04651400e9540e4400482001424190580c9072260320220001800c440b80c81001020540d001402c002086020340c1501c0d0700c007403580c404001d5102000082001800100d030314042500302d42000c02d1240c91f161061105844820300c180050b0b411741d500303018804116074503250501005034a0032002410301145c000c040c011039034507000c1034100755145422548001d800d0344081c1e4180420800740a60003015200d880b0380440e808040e40c611700000c0b40ca9215030b0015502c014110410f00d480d9006a90050000c80c0d1003a086403035602011160710184000001102140c10401110b0b070300d580c42e240e0001d903088400700c5142400c81034103500b240318410946d030074103010940381e004100740c0103414000000c00020842c807041243c01d005c80002d40b200c0001c81c0c5984140003000108101d40d1080300102c003c2c5500c004021480e060114225115620813203050340b00d1040c14617001e0115119000f0b4915420380a424400c544 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 872028696 1250 872027446 872027449
    0xc060f08060d1b080c010909090201022e0e010e060604090309170c06030702010c0807050c2a10110706093002100c0b130302060708092a0405060405090c 67
    0x811040809403100e00d99007030b0041c2000f0550701e084000308002c400405440c40e4007000945100700580c000c02c04645090041e401507600801c1072100f13059450454240c3e014140c3c10340d4060502106250b00d0749191003424030f0400015489403580074a03002c100c90700c568510040000b510000305004001424089080200c0c0c0c2c01000414001380008055490088015011959603041114a040181c0d16007202900c0a41c120080c00c2c0c20503000d1030154a400d10700d50301c19039500c1c5205445100c6c00d4184c800c0c680114080c190000401500401c3c802d840f40400400800142a1300c80c0c50005014080380002d44034017035176020341217503022a110519441850301803040742c0c00100b40009034207104003402c00141c0c0e0741075880c62122010340752460030403260b0425402c600750050540c03900720791040380003000c0b940010f200307540a20513141c2203441d9618160602e0a28562101000440c0d618241c070202950b002c000b51420203030245e41c10000d0740d443e40b040205440b415600310039260021000301419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 872029946 1250 872028696 872028709
    0xf020406051b10050408190c03080c16020307030501061818030302030603240a0c022b0909050915060301020a2c0303040e070311120f0a110c07030c060f0806 69
    0x14904100f514a0a03808607030040681c0c5040f6400c9811130400036008003031050201ca40501b4080a141184001805550107086194094010f002009002c1000c0d40c603404520114100c50342d0103420384002e25035a25001d4040d000c035014080c100f4030642400b0781c6900951140000500e25001c000c0d0591110f614290021350000d00f000c1e17010702a401c400700c89445609500341c40d0419100c032420140c5081500d1004440100b0301c42030442d0040d002000e01c0d032600a940307440003e4010f000d8400c00c001d01c541510404025400b00e02c10b0b03070820082095081002c2000d0625142c9454080e44580d60038041600301d108407040d000200e541c1d0505c07043c4100f19a82c01ca202642142c0c5c00c0c03041078060500092841e04154015103005245c0b4080010041c0d160081204402c40d00000a0414000760094504030500415a242114888000510320030094000341c0088a0411303001e5903941c1c2e4007140b15110724a03408151114552107200241e424400c0c410f000e060601c5a40790086030302c55404010b031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 872031196 1250 872029946 872029987
    0x903030624050304170a0e01020d1817010605132319050705090a090501140a0b34140601060f050405040504080904050720071a0d06090e03040302040f02040605 70
    0x40e81c803d0207454061043e084c4006040e92141501d411f0058851140028580282c040b0703407204014070b0106a0340c01035400800403081c0d0781400c003500c0444031003031a49401094543d207e2035001c1080807200d4540d045070741c0010680b02c05107480140342030711105a48a030721010b80d0100e1401102c1c0701c41c12103200c440d512050b04680f00b072034568070f85030341d8038005030100e0030b80c0d0003042103190b131000100103d02d07440a00d1590342000351840c002c450f02d0410075410f5409001d0400218004000e11081c5c0140c568020203500181521042c61074441e074107200b138600700c0980e0300501d548640c0001141442c010208a036040d80f15940e51894a41094144005800c02500441d2804018000f400c2e080da41c0340038042c85001d140d40d410300c5111f078001056848110381c4406150719082542d050000d81600c080c0003a510440d0304900341d54450303180c0c4a00040c6515480410303c0d510341651040c50890100c0100100c81c000c4600740a0703806203401c40b1089200f10b02c078450102c0c508004500c0d141602074400c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 872032446 1250 872031196 872031203
    0x304030201060e070f020606030c0117040303020d091113091101030902030705060f22080a03080c160b1e0105032112090109120305190209040b0a090903030624050304 73
    0x1401030342d0761075000c1d0300348082d01c03200017041d20f480b038180d03044e82d04101e159404001100200490f450900010301080011030000520410fa1070005041c14001d40484143c0c600703d00c800c11628030320b03060603109410a21000f0b40320307201380e8010024000290080c4141c0d20740000015080d4045a00154010a014001203030940038800b00025955a00000b422020380d02e500440d55428a0020f040300d9404e2500c10080090070000051124007400583c1240c41545404c0c5581140c5984142c2d80d018000c0100511041181040c20333001c11071501255400b8401580207a12030164180da00031064509000c2c107605640041c2d804243e211000c1022006c01303a07460580742c03078800c00364034030f44000b08102c2d404501030303446142000070400c40103005400464149003c0040b403e102148846c005001c0285d600c0054000c60102c0541d03070746922001c0003020051a42030b8050380c500b500c0c000790601040c1600460b14080000802c00342c07110340c00c42c108400044003c0300c0c01500f134098549810140c03007617 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 872033696 1250 872032446 872032451
    0x1805070801050909190602030912040828050a202d010509060703031a0d0809010e120a0b060916090b13050a0303050306090c040f1a0f27150f0304030201 67
    0x64265910040017400b07018000d10015a5a15103620810319081c100c03c8030b441c40310010481002160804280001c025030000d001e055511601e0307180102004088a000c1c00c2c50003600c240d10100701d0950140d2120415511583c0b9050980c02d003000b14010114922410f84964a8900101c407070303040d848400c14900504201d410a206000403500390780201b0303821004203944e00e01c21442440c8243c40460390940c201c40071514503e10782e40d900883d014060106040c4418549901450364031040c1c1a01c2c007038403e000300c0302502c5140c100541340d00d4081c0c441c0b40c01100c0c080f0100e0640007121196102707040594542041441c6081e90070310b0645c2c8150740c220429082c40c6000f048641c2c6140e1580000d6010395500f0703490381842e40400840c000c001c0e1080030a00d104020802590f84511807031811070703202583d000b81000d8400d918120601c11400034007589800001d00e0781c030842c01e0684018102540004920131842141d090181e4003e40107a8888818801c0c4200c9440c1c0c0c4030400216845031003803002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 872034946 1250 872033696 872033713
    0x906050730141e010b09010c0210021f0605150c03120a0b03010c1d0a06081911030c040807140a03020402030402031f0c170f0703050c19091805070801050909 69
    0x90795204403d50351408010b8518a840c210034a05180a501408031113078440e280a41d43d1001130202e0b00138050081c0607580c0a050b6100440c000d100c04000b4410440c0420441058400394030000c000e00e00900707200301c040d03c4d401992503001c0b2041d12400c0d600d004c021491700b00250710a1001c5800100f4405009072160a4100716403403c1c014851400760301c1c0c03641000ea942d64201d80d941007015503082130203801e0045040110236449030003a5000120700c003181d00348051390b25012000d4490400c1d820f0f0403000c00001c0c0001041d040000b0000c4540d00801e9501030381e01c0340740080c04c40314484180c2d5403001c1d02c0e41d001d0015252170790045401c90301c0103048400d0a81088480d4482c4200c0f8001c030395000d9510382c00c05015603000084550001c002040c41d003a40d10f00254440d44d010400780405081580d07030300c0061110307035140b0f046480c1c044840c241100c0189550500030013208490140d000e0000c46010151207000c541d000d0b0350301410701500c4690160b801c2805100c01c025004144001d01e1040010303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 872036196 1250 872034946 872034971
    0x105060301031704180902010f0806131a2e050c0c13090f060c0e100219030e0a171209090a150504020d0b0a050d05060f040201140d0906050730 63
    0xa6a4520154031501240b01b00c0c65000160204031011000d2050040c10b0041012941d10400e240c452010b00c9440002d000800c442002e40b001c0e0500c0c0110b4000b15848903503c01c0000340071040c0c4880140451400f0030745034100c41100d650142c0e140039100c6901c01300340500700c1d2501000c0f1200e1642001c4000500c0d404c10340b5511412800000c0956100e940c80c108100b8050703000b0042d00031844152100711041003070110080d40d0f180300b820b04003252440141ea1500b01807240d00d0160b51080000c110409042d1101c010101c5585003041c540554499078112248060860090b07800d034200003442030f4982d076903400c034500c0941519203070448103456001010441e41d40380d1000c0c1064080014001a038100c01c0030034804c0b1140715030440c41c0700f03091011350303440007540c0011a95885107120106c2003154440d480140d03040349070805481300c0c003000403440e030001611544c04000a68000c20f010320043d01e0b075a100392000b628070360000c000700c42030f09944810114a2008a0741c0c0f41403220000900200802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 872037446 1250 872036196 872036219
    0xf06040c120e1c120e0115090b0613030c080105150114210a0608070e0903030105011b080301030b04050d110d0f09050301110a08090102090603161b050f150105060301031704 76
    0xa80418080242113000c19103510840b00c051001000030000a8245501040c40e42e03000e01c44c402e0b1541c4c591101010716140d40c2c09641460040e151002c0031103460385000001001c9501801045610b480700040b40d0400e642900381c083c1e041a11800154520f130700c1d1400c046d5018080090745180d1010700c0f0000c0d03032203202c0c1c000d03c50441e280d030008000d400c180040b401c0440f00d501040451599030207000c1d8441000c01121704442c1d090900614055a090011521a072412409002c803440800008148444400d04071310807031042054800c9407122441c241e43c02e81110100341c141d540b040c8541c01c0f05a001e8024806042d00c6428801c501c0c0d507649000038252940450200ca410b080410603c0150f40c01c8070300543c01030b0f824002541801c140102048141c0401040d14003584c0c000c000000741d03240240b4800b444840803907514a00d000007814159500c1d44c041501c507255202d01404030845a1003440d40138146e89004014903d075928540740c00c0642c500349840901c412904200000310ba5501c403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 872038696 1250 872037446 872037493
    0x204022809080d03060b0d0507110f0d031407020a0206030c041208070302070e0c0a0e040e0303040f0b0c041a250c0e06040911100e06040b030f06040c120e 68
    0x1603549015841c00c10a0b154140521614140141800c2410078418446488181c07522102c4d02140001c42d82c0e64660102e0300c42d011844460740301c1c0500784000900e88008501031030040300a4809009954000003180b1819104030340d003a005030010700c5014010302e02603000356040038095603003c0c102508c1d8a820b411740070303440c041101c4a62001071754004040d014804400140130404140444d454071445802c0240f003404112410484080170a048a41d01e0703074002c050036250324040780d443c3e28280c40c0242028181d0801580c00041e80c500186046041404030340a6a600c2d80e581c480d04000c0300203010468009420990b950a10f02e2400300c188040c02c0010011513010b090803001080c6407801c10011100084d00f02401a41403143e100c0200340580b41105c3c1c1c00740b042e2128401c4070074501c03044555001001d900b0707034004800200020540c112401075030261440001007103c0e41c0700c01003081f00300d030700803030a413804900007215068094509074000000d002d26103081c0c5000e038004055010490040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 872039946 1250 872038696 872038777
    0xf1103031809090102030f0411150301081f0b0f09092e0c0201060506070b0a150b090108130b041403042c060d2d060f0603120302070f020402 62
    0x9081140880e494215201d9800000003c000c603d9030038554511030081000900203003014500421240031621050001d61203150355000842d1696101c1e03e04036100c1c51110304010204140203443c8604003401c0c460f640a8400c000d00558800c0d00600074000e01c0c200040054409000364072154800114030130f4a0f1091203000c45021601c0d030104000c0008680d200010380086a140410a00443d210f44c0200d0b246641c22001c2c0000980d100c010400c06001507840206003283d050340300040e50012600608558207003600c48400560311140d85807900100d5860240c4101270002c0403c0c00f0441582c9807400c148031135000e0b64074094481726105000c0c0401031201d8100340d2003204601c08802c0101c0c07495000401250001d90039051606e80d40740d0f0301c90190b40110184003613409140322090795401981001e41c424000d000e00301a51f030720703180205039034401590007d00820b84106824403a1007215041c1e5485015002d072100a602400002c4d088003000d1a58041c501c0244c08001d1100d5600c041d00702071 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 872041196 1250 872039946 872039977
    0xf0f0524150f060a0224160309080c07082109030705060f07061119050703170601090305070f170f0d0305070329030c01030c05091c0b04050601300f110303 68
    0x40b448080c1c0e10090f8043d84a0900030040411f01908082140101e69640349626021400b0b03d40c45c103244105114072101c540b000c0c895648000b0b04076202242810b248801580c4840d00c035040074004545522410350200d038180c0020900b0b020b035282034409003616101d1401100d05180c003543d121803c4070081d10310000b00d4500410341c90188006040d41003482211450800d00300002a07402410802a40007060100c89039580000c2c40d0f80d01c0b400410000715007040403103004981d601071418905940380074240081c11080c061142c040e0780010b09410415056004041300043d1800407001844054a490109070b00c621600030841c68245200040340c03152a240f040c9420f6020416141080d0503c40c2814103007442c2c1e0011405070450142d600e19030f81a200107081048800c07800c08105984103005010b0380c1a41c080c03009210f000500141070750081c10400030b283c0144041409650000307441125240d01c00d07404800041c0d40030340302e00b042c248240d000040217003000c3c0c006030031500101a004140d80 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 872042446 1250 872041196 872041213
    0x140a0204150e0d06090203010b030307061509051603150b0a0f09050f01090302060c2401080601140d150e01020a0e01020114040f08160f0f0524150f060a02 68
    0x28500240410103100c038108810352910000c0440c0385842aa58080c01560780c540105c015901c081d003006014031070003000c0d6681d4101c5031030724070020102c91581200c6882c88041c040792401d000e2150b107016100c3d0005140d440c11000f10304030701801040105c0c400d41c0929500000d007400e000ca01501115030152203094201484c0380d4028800106944101c0c461101c80c00e8542031640c00039200303000c0d82e405039151590b540a4003043d500c6c1c0b1044081c0300500e02c1d00100c80e80360b20742070303186440c2c10794596100f511520b0b40d130398122542000c610150290b0005c0704034003000018101004001c4c141540c1940803d244540400007070881c0c003c240100049110351006030700329a030a22428204050142070311144d8100342d00d50078042810350300c1c001d1000030005111802070750b107410075403881580310305a203ca41d0200d140011030740454200454007803140c1520401c209005042039a0791070556000141b4541d94561446044101d000b41e207908903400682c60981d548402c0d0080c02601c5440d0000c00f24071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 872043696 1250 872042446 872042459
    0xb0a080f07140a0309020a03080310080109050c0d260d1503120c030504030813030c2111010507080c03040509061507030e0a09050f15010306080606090406140a0204 72
    0x45100030000c04900d8540e50401204a420200031000754405020140d111000500103800502c00142c001c0d40c4858034000000421050b0002540300d0074882004102c02551840d801d4246c44988000410507040345840d0b40381030a1a070f0459684500880000742480d2800e21000c0f035000110312940809400061003c1d4203084d00d00409400a020407070022100d0b00e035444040ea01c144000c440c1e0100800c501049090506c03400c10389000e1034004200f40c0d030340c6550000070f010b050814402181c0302030a82e01c0001d10801c06581d0140400f94010b907441c006513a5540b04401d5080380074040341440ba05004e4080480d0380d04019008000c0040b004698aa013070404200e010032000b1700c01d0b44500304035038680450300041010703150102c4d07060400070200500d10001540311040750f0009000c90b45001d041081032199614034034060b500041c40400040c004c0304c0110103851160180c02400d03070150b004581a42400d040f1154040d018140001c3c0c81416440c0100a00f20252201c0503407a4000c501030048 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 872044946 1250 872043696 872043707
    0x106050715050a0e01180b01030f0c080f07080d080106080f061c050703021905031f06180f05060a1208090d0f12081006090506030a0e010f2403082b05010b0a 69
    0x741500c01b400084801b095654144001c10500000b80415040e00f441410466403601440281c01035000707403110005000c1940ba80e0700060722030b604003449140c4004e0081402081d015040e40c01c0b07913446035030595481210901e070390307006007078150494601191042012200c02c1300307010b81c40c45800a04040b034550300400c550700e42015a545002c50390141d00304400c0e5000900c840352503000302c0b0882c00d08204003c03070500400c807d40c824509072043d09460034a2843c560302850810700e680404000d151100814440341d0300d014000c0000700c0d04601084404251100c02030102e492004002e1800c040003503403004a2000b4045080f11000c8840d0102040942c0085102c3e0707101803124030111005103845030041244038a40326017805158000041070f584266500481014200f0b9002800745148001902d0300030603581404400d4280c650000c00d4181103641800000c03660040d10580c00c000c460324041d11540301000c00001070b00190490300441074614020107000300303204c0341c00c00e455070780050b4081e10 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 872046196 1250 872044946 872044961
    0x7090c200309010203070b15030613120e030c06130924140315090c03070f061b0f08030c28030c0302070f171c0207290106050715050a0e01 61
    0x1501e820511146100d039a000007561042d5400c001692481d0301d40c1141c5009031945a80e0180d01342c000c2d5010044007241d44c14003992003610030748030141003503042c1e5011a864540b8600260b03042d0019034400000c2e01c1c1070009041d618400580310b21005641e00c12120490305514800d01d450114a41c5120b00005099030090090001903091400c0c0841980081d40354001e0082281902004801107040c5070303003c120b0202c0001000d400c031421980c80300c0c40c0f80c503030381a00e1084000144103075805c804100d07507100c01c1700c0e402d9901007a192040180c5580d00395103134100a043e0760707401c0070034410041090503e40c083c09064444031036080d8480e1b070a00300101038807650a4960241401000540c0016491801c00e403a950b41141c01030b0b00c0c150010305004a144a5039181e110381009440c0b42e0010b5402650041403601c3c46225030409450014030500e82c02035200585807507080082c00108941400b5500424071386200340b05071440b0710443c0c4008011203070183d5400ca1030030b0b546c2c01d204107102c00921a0350b8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 872047446 1250 872046196 872046257
    0x4050607061a012303040c1706010503010509190b131709010305010e0408071205090d0b010503070806160f0c1a151c03051809160305010e1006030e07090c 68
    0x21502d00d080c0350251309400159025202c0c00c0c00000008041c8280d2505107006400d0458501540d02c2075520150303940c2d4800c1c02450300c65440d0034042007940400040c500400c1d02c8090000e030a5160715250b981c4022801020f14588001e190000707000101c3d507540c154842c0c00040c0c161900e4649260006085a405030084420304120800b8800401d0006040da10540d52121804481c441040400c131490301841e81d4054100845180600800c00b80f50a982e0503950141e040f40d802547e280c40c50f694410f019503090b0304805c440a210b8005a1188003c3e0082d80c04c50700f00800d5144095860800c114001452240349081031000d2055080002400c1003d5070b0003101c041022303514222909601960513036004090200005450111a0311040070829030381005082d80000d01c0c19082d05286c407000b558900c80040d10b0030300080742c00280041001d0250071072450040307865061042c15801880402d0031440d892146400005051005009082015401d5541c00e8907010481083c40c90000c4d40c1c05410 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 872048696 1250 872047446 872047457
    0x120f10060c020d020312040f0e090c0612100521160b0d1508011a0108070816050708190513060201061824080c1017011a04050607061a01 60
    0x800c0398540c04040080280d4040b10120100c8016200003842c1c000ba401c45d41c07240850224001070200c400103a104101d5130307800d0020101c4c2e40c1d0700703002c143c43c1d12a030201154850000d00031004501d1005181702d60000146444001460301d03480002d4800c1448041e0010001c0380d00342d8444200717014005412004050540c1907841c070304004000781e5038013407030781e41d004078950703d035224107150040101120043c0324407402044000e01c0025a00c404000061485000c1460100443c02081c85041c80d82c0c800d15106072240c0e00c07540c110074201e40f01e0744540400c1e0b41e0004184962100d080803603285254038801c80d265079581d072400502d40c50490106901c24425a49025010001d845910101e007840107c003550024401c605050400e04900624035480d6200368425030115215400280405908030100c80c843d03005034403020111540c0b0703c0c0301548010210800b0040194603040c0050b4039130f011042d10b47c3e40c10151101c01150705504006016a04240c40703104080c01045850050b03440d180003840e00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 872049946 1250 872048696 872048699
    0x80c150c03040c0b0c100e240a0605151c020702131401060207030510110408030a090513111206010504080a0c0e18070b0a090b0301030b040c081b0d1106120f10 70
    0x5c20340c50301c00100403003000c241c0b54400c16441007424008040d002200030705400b011148400000303840d0200700c0e00044081d1034900e002c075440c600030b8800c0c50a84103071592035241400c0340402d40704841c0c54035040c02072550207200b0180141e503220000c0401035a03c000000d150040c00d100d0b200304c0e280c1a03011500f5074100e0031050000c210041151201003190041c080b9001d0340c0042020050b200340e42c01a0000e00021400d10804d6600c091002d0440b441115070b2040000f002407010119217540e805a84001e0081000d00070088001c0001d03544024141803203800d080d941e4115505111140c2d200b202c51904446044c4807088049102a42000f0403d0801025440d4030030215500e0400340580d01000078081045801e0b00d01c00c2002402170105656001e481356980d142001c011902070760111800100418086009403000504031b13983d828071030315410040340c01018030013040e18030402130f214184200040441c54985070001c020851440000780e03030b50301d0400300d841070300c1d00044c028041c180d025420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 872051196 1250 872049946 872049967
    0x20703090e1e100515031603060e010509060d0c0f08010e010e0703021c0c0e07030b03061b0706110a0c0c0608010506030601030c05160c05120601050607080c150c03040c0b 75
    0xc40c00005228002a408a83ca030a80412004000d03039002c650b0050a03c450442e5400300c00015502590074505040401003400c0020341c1964040e0040d00d444100380401002180360852050381c01c01c0015100c06c00c194030640700d001c0a00c8407130b001400081094a4200b00e4500248076162240080e080204031914807900316544640c0144000b0344256191040601240428040403803131642c411301c0a040786580310401c590f1755100310303101c402007450070700c4110b0b590401181c103e201c2c28491445201e4091400c00c1c401040d007000e40195885651040d50340c07100c000000c001c2c100c5900548440004004c503140111002101d03800050422644400401003034907020f083e01c2e0050030900740840d2240741e01380c003190075005980f841c0b00a002106020814407020f0034800c4181c0c5c206980c150000a107480c1c083d90303a40020311425030001e504001a4011641080c060100d45041c42c0c2a0380005040300038442000e50180c482c00c02e0401d0000501003005107500f00f800c02400300c0142641454500c1c02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 872052446 1250 872051196 872051221
    0x90411090f120c040506031e0c12030711040f091e0219121e061503020909010216020d0f050714040f0501060807110705060a03020d0f0b0303040603020c150a020703090e 74
    0x7882c0740c00b0341d80703e00c0801e072075903030920502090884488241208c0c500c00d8100654035a101034901d0300842480b09030116944001c81110301440d00910034140403491802444010007050034800713050340d9600010f0b40020100b54100511116289025003503103503500400690702d1110001115000c0c7d00302040080d8111007480c030409542004903080391054094400044c9034189800a11035403821400315250168400366000340c030b00070348881040d90340310440c042c201c1c41020281d190380d04002140d6001803410505002049105103540700e0790500507039400340b80c06290f401811040004004402d21401c02c0d10a44000d0051a0020b00c4154589440034180a5010780380c14200554441c4d211200c2900300824402080003801c1c00d5926003100c20010021340010604034007040c105881302c405c0700c4241c0140e52400c078009001d103280030301d008020350080d03000300c030142c4090248103200c03031132205100442c500c900c80d8001c001d40d0b41c500519005005014079000000340e4030300d51051003420001c05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 872053696 1250 872052446 872052463
    0x60519111608060115090e0c0706060b0c150603010e330106080106021002090d030c17210a1401051e040c050405040b0312041202180405010e0f0c0d17090411090f12 72
    0x161050340c3c94502b42800b0002d000a81c010441030080021103240710000022488008403204540d0422625150700301400c1c1c45070b64421081c1d0303a001d03443c4050061040c00c190200740200b0f0401c544140104550280200026405500414100c0004116454040c00041080c0804110031481c001c0003000140380c1c440b01500160410220380100310400c1386000c13080680a005d48091900c07480420100311859101c02000e00842901c4008100c158805000d15035410400110607100ea0707090109000103d103016244070100070342002c07540c019032118030511070440c042d0350f115070f03980b4101001d0005030365540e01400e0003a84080c4003440710002103030640d01035800341d80300c007002c0b02110b0001a0841280a422001d0b032030002007030004020055018800011204c02554070907400740030000d0712625440d403080d8010741180e4960000030156404000d6421004461a040c06260700106080b45e020741155403001200180900c080e00e40361004902d4444103d600400410401e40745540f281030f02c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 872054946 1250 872053696 872053711
    0xe100608060705160b10050a05040510090c09090e3414040902031203011706040f02090a181b0b16020906150708030a06060519111608060115090e 64
    0x4102c3c0f0015070f0b012030605044c2038000411013000d0400075010307900d4a860b031280510400d5203d400240c11300313040c01001d200d40c0703600c01074141b404d1500c8001f034041c007080403501c1c02300076442c6004110108c4c640f00d050b0045100074028550351a003035100f01c4240940000550604120100c440fa0301c41441081c88180c0d43c41004000742568400b0120b000b6160000000303616008014081d590010301c0f00142d81280c804140c0200000d1135840f50980310700c001d0324090060440707101ca001c00b500b40002080d03001030b4446c1c3d00040119210880e6008802d42010171108244002d40c01d075500e1408645140107006207110383d070b02d403074020044100e00300000070001f4099040c94000600590729075424401e01c0c1010455075030fa40810b407078501a158401c4814404281c500175022a4280c0315030706440401840001c111140421100180da640403484c0500e540b40c4107044a0752200c11082c081b00d0003c0074114020a200d50501205406944904066100b00003403808100440d40001043c250003401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 872056196 1250 872054946 872054957
    0xd0e0108060d02090712061d040c06080c0a0804020303090a0816140a1a0c0a030203070311060106170406060515070201090b070f170915120a052716090e1006080607 72
    0x2501c01b020f1000d040d840e403182d240c0b131007060039503043c0b0054031a03492311491207100311400071600c030841600c01c100180c800384110f80c02800000d1000d4041e450544c2c1140c0024200c1c3c0c186481c0a0004214450039040580d1076006002c1c080036482c003081000d0f01078042c210b80c0040c150340942c08100c016a02e8490b014192007003009400c1c2590404013218498282c18080e0307034101d1610f04000e95603a000c0031040b0000f40a0542480c912040071a00368107850880d507824504440c0f02003400002c160240c01038407210780d02c1c00005156079812211003d4803140070300d480d0321005076000261000103941c0c481038840c40c00700000070019981c0340c40102c50581c441510000c6200704034180c5050f001d0501c49030b03002101e0240b409a0008001c01404000402c1182108a42d07a2582c40d00f00b80d96058400311010b501a0513040c6541c02849400f00242101000725038084184c000e420080b821990700c90f076406691507616079a120010f11681c1030203058900207115091405100c290340d540020221000c004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 872057446 1250 872056196 872056217
    0x1a0406050f0d030c0b010308030105030f2a030c0915120a02062d120a0f021602041e050411040e0319030b1c050c010e010212040b09120d0e0108060d020907 68
    0x140201c0d2909004c94101d441c01c102c943e102d25044911f83d00038090f4500c24450074910910510380000c203c0c418500c9030f00390003884c01000d11038002d414507000609034940120580001940c42e81d06c4c0c068440d00c0e0107d404180c43d0128024480fa070115440d00d050140c103c03419250141e120314040380e4a02640c59110b0080c3c0f40483c0d804510744145000d585003040d000901555100070307803007003c3d000c2d110703910040040240c1340f1107040413442480046a80541d40b485048003500c0e0a9200ca00c041000c5a2034000d400f40e031040b0b2208699085400311199014010711402c0f90a2922482520040c0c15000790325001c000221484460590103c0da07042584802120800d0780b40c2001c4c1c107071f002e040440c681c00b000240c2d1810350f890768401c1c49000c0c00200040e4042c2c09641c800280404100341c41130806180074185815000d490703200b800b039550445084001900e01140c01c2020942810455440640482c0c1a50006107100c4e00905114401d05071100300001595450303981c00d1300724403141411101c1c00b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 872058696 1250 872057446 872057453
    0x3020d1103030715050f060f033a02011d15010b030603030418090203010c090f1404090f08030a06061805010507150e1531030e0a091a0406050f0d 64
    0x5119001006148040b500300111040072203170452409041c103107810203840c1e5108428032003609480c1e0034035135140d8400c401c079405005d20112011518816807545100e5070080300351400280c6015007049006030342d103c0042c88980b00c803401f00303083d5040d08006001d07101940c480344284004180281c040c0e260000002caa0669002c0040b18000c2901400030401c404081d50b2070700043c0000c0000340d01a509042440344d045100d050701700d05513030340541081626400d04012a512403a6825246e412a0b07807582d00e20041010391090010310b0303104080c4a941c0e480c0181d0340f0400ea4985500c03030001c1c0042c011842d50306010303032044201660803c1c07900c2512038006003009848161240c1c0907051142c0b82c42035000c9071002c0032512050440703c60400030305944818400052400d5441c0c4101400d0110441c3c0c40400d0002c0e0b070f943c403652070082c94005280d150075000075500075426488411056541c070002caa00860081c003010794481d08035800c000703451074a4040303001d40c0360103103000d40b0510316218028200b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 872059946 1250 872058696 872058703
    0x3030711010b090a1b0e0108130303090b0a02031006030501030312020315091501090503061303030e1e0d08012304020306041d010209090c070f080a09031e02150403020d1103 76
    0x140005082003124101001d82c1001003210345e114110b4040a5a18120118081c00e84041011410f0b900c610b0750343d441e00351100b01c0d207000f410114105601d070001e14002c10140c01c5421f0144054a40040c2e6900b0084914104406180e10ac1c0051509080041020035007107445820121034020002d40d813907079100c500341182ea00c0c41c684280e11101c804280100100040c0640b0504142030b00c44a22042d2910b04150351001c04030740b8004040303400728003040001d2017070300580700e11402d0038115002c03040c00c80700d81e00160159051908441d0301c9a20302d515895030011865005003174041e110318425401c0e018450130307410300317a01281c020b40c0c0000118009454a40c4140c0030007409052507400f084d20300e01c106000c1c2d8800001780340710304101404241c99180306412100300592210b03904104040650b1885030079000030725020240140c0744d0b00000454007118203580c1e50782c80c0b503040540f840034900c10040c018031a2140c001c9c81010521045c0016140c0780701081c01d003034104010104040d0300c40f00080c503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 872061196 1250 872059946 872059961
    0x3050304260624180c0f0415020313171b060405030111090a06080c0301060c06020d050a0c0f0504080d080907150203030f0a09080406080901150b04080708030a020303071101 76
    0x1d144280d50410800900400882503000c20240c42800031800c642d0801c40c65040c0004882090213040020400340d0302180020051050220303100b500b0031b5500c170403440034a4203020303d820142e0400540700522540f030398484405800814411082070fa14044101d54030010454042808166214160301698034402594001c201c01002840010a10214443c01e130700f08078503450280041c41c03008901140500801c070304c54002455428113581ca44081220060782100f4151080c036800c1121206225580c0501f521840742c1c1980841c0310302110740001e1030117440b0f0003e807081042c180070034030500001080180690209140203515520b074154558140086503011a20040d034184d02c3c1041c464020019610509400250303218076a540c1100005640d014440280009020401803000c01d0150440700d422403034200c00050148001c850b16051144583c20687c0d1080c0041010020700000300210005054903001460408865400280d40c0b0300001c1c00f8041440b00319140b01400c00001d40c041c64 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 872062446 1250 872061196 872061269
    0xc0c0615030c06091406030606070b0c070206190f14090f0307090207030207230d1203020705060c030a0b010e030a02060708071a07090915171009140c01020703050304 73
    0x814640c0c0d1888041c10030702d04d40c402c40e4280c0f41046008038451900e01c0170b5a210703d4010f028585030000030341e110035007240c1c01440d00d04216818042c890141c2c90303007001b90200031074405040701c03013394030a805800c08030180300340300421080160481c840c5250b07605440c4503c50998005a0400000002906140c0030390802d0008600c04625501407503800207070700007101d00400c00c00820a51100c1c50070f100c6a0203102c1c2940240b51142030000040700040c903421000c0c81b5140050030001559561818444180c54460b4400310110501104e4051481a003a81c48002d08180c0003000a15002c6600c039241840061700c01c500100741d40003808544000ca5070004d50003400380b61503120940382200c0e410016580741d00000e0210300701003154956481030222503030b03445408401b0540b40590000c640703030001400d0400b6001d0034101e1644d51031107002c1d4402007481100500441c0c003080d581c41d460030707070540c100c06c1c110351024008101090020040780c0c00e039802d54000e290002c034141110070000f120b0310b0b901e031b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 872063696 1250 872062446 872062463
    0x90a06020d0c0e03070608010605030a0209060c07060909180b1b19020606150d0c05130f030614011d0405160b1c1a012d0909050702010c0c061503 64
    0x20035000880c2e070040b26610050344400c54030b80d080300700381a555420b601414010510181c01401014001e0b0b003c3c2d6440403607580050b02c1c0c5a40303a00814220f40041d0302e51510303940402030501c072058004001801420800b40c0410150b007200680b140c50341c10007480541250070070350218070009000445400c0160810080f41d075100e0b110321006c08510181414100140506404141c9a02c0d12250021004a009007583c1c14401c0700d90501c401000864000018000100100d1825180c0207110300020b054a1042d5140c841c0b841c104113041c0e031043d4201050455941006200c0404041c00d00b17503000503840c08070351407503445203040d6150110030882d41c040500002000606152214002d006c1c145403500500b110000c50300fa04401d071280c8a042000b50034050070100059441401404000304407484075440440c0170001103180054603149140015001c01818017050255010704c64001d11188000c0080e80d05125006010038154100100b01c6a151070011000d502c0d0600e4420240d6041048c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 872064946 1250 872063696 872063707
    0x10e070b0d0b04090f03080901050f150a090c050421120507032705030f0c010818100e0a0c060507230a021f180e0a110d05040807062d05090a0602 64
    0xd858040c4d001d41741200007405032000500e00301018050309024070305c80d550140c1c1e50b40342d1000100c030250384a0140c94001e1070b0700600040c1c81c01240254241c41c3c4141e22405da81d14240704414520040403690000e4042c003050594000908502c0910b91250261405035114201c0b40790444418252806005080f20800106440e140880090b901228002c50071a6054844d100c0b4040c0c9940202c0c00b00303404248510001a12990302510000d0107081010640740c200c4d4441d0420380494010794103100c400d91000607030300c0c2001a6882c03d5405400ca40c241241840d40590b254a03502d000c000c0b620000f484900d8083d007000c14100304105801c1d900070000c1142401c1c280504140752140e5020400081d80d00c20b01c3e01e4489010f017020f40994a800f11015426030b075600452000c1c240c1c80c0b09180d0034007003c2010b100147c050b4403407140200c1c81560115516401e50070000b080c1c07002c0724910344114040000100501c111a500860541c08242010407650740300f40c04a411b05c0c00381007014100b24000a139 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 872066196 1250 872064946 872064953
    0x307060c020c0a0e091c0e0d0c0302010e0117060d020402070b0f060901120c17030c1b130c0f110c0301021c06120b240a0602060f0108010e070b0d0b0409 67
    0x210201c1e5200165000d4800e07039510a0b100e4503080098035441020f4000c10950061294002c0100c051103e0a050002d6001f0303000300403e41e09000d128041e903c0e42c900b03410034003c40da032021784c41803140002d1916600a204480c1380200440c0041e00c000d20440d0610000b00c06c540341e0344c05440e003040c0c11041d009498a400d040e0395030780c0e01d02100c0303461055018200114126082080e441e0f00c19400804518403141031011021055040301e10b403035954481408121201c2504020900054110400000c7c10300075800510240443c8002c58600c6c1038249410314420aa202401d02100800d40ca410300e80301c104403004c0c4d07083c100c80c019015090350000034855040c0c207481d0340c690791520030307444200700156680350300403245540700740002c1c030161900000c03410400420029a07094880c0d40c3c1070405c06101400080c1c41d100b00c5038813410141c4c11680420201c1e001d900c0400c0c1c014010903009102c61600b00551640b980c1c0203000c1c001018101040e03058452a40381c0c07156205400107001007203034600509 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 872067446 1250 872066196 872066203
    0x30f0501020a02060901060b0a050d020408030a0c0b060307060c080d15080718020c06040b040503040e1e070306050f13020d06030f1202150606030604020903011b090807030b0403030203090307060c02 87
    0x40c42d58058818440401c07002130301449200308072510403440d541001424032041303840340d100c140540c00c419004d11001c01c2c0c80c2010700050050040f541c9642c9102000c62800104c80c5800409842c420380003410200304041c1c00998403942c07242d028490940d1065074845042c01006d0b56610b02145a890726030100b40143d000800000792101c0140e4129400174041842069101c2c160200c0c500d500050041000110995074554203c1e20417015a814039854165003200414200c502c40c0d003c040310f1200240001503811700c10b801c0625403070207100b141c0c14132011850b03403003501c804107000c1c01b1144002030380300780b43d0741c1030b5100481d50500920016980f81403503040c0c001c50146c15125980781240f031400207400084c2c000401540c0003a15602696070000304190750700010f140c44e030080d07003c0000e41c49581c2c1c203105245810300318540c90b96250080440c02800302c021074006003000d500020042c00800d4500040075800b0764180760242e601d907107984d4507900f14000e81c1d200510203030500c0c01d080003058021 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 872068696 1250 872067446 872067457
    0xc0106060e0325140d1403030a0f09030e13020904090f0203011401060e0112110a110c060c1f0603020904060c1d1e24030a0506041413030207030f050102 67
    0x803000c0311002d9400002075206841d54036643d14103411940c00401c015555050f10700c0e00f40c0b40041c03603c0422070643e12642001a0030040300003050300f0000400151b440c81e84101400021010010040c601035554041d0051541d0301e00144105001740c1190348100c01501100d405540240c0144130407005da1800c0e80003480d13202401c030301c654201a03614041d0080045000d040303d03040d81d512002846040010b45d080c0b0104c007900040b5580b181d11a00c26400f40d1002031040006698840c6218080e5140d881d041068200c8007a01c03036402003220010b5032000150041d0030b44480f200c248540d82c00000c00e80c0050032180c2c0001e401108010800050010650050540d0142d0f40c032680c4201e00668a2034040d280000046980f108c01c400c80722981016000055401d04809010b00a944c0406c00c00c00120030305800001c10345140c000200805880c19014143d003041094800b808a201159103030019036100030710250034401a992043c3c103151003040481c00454200ca14000d4038134107418414040c1d40311 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 872069946 1250 872068696 872068699
    0x1030926120c03040b01030b0a110a120b06040b0702060c03040909140d0c12030e07090f0207020312040302062209020d0e061005220b0301020a17150a06080c0c0106060e 74
    0xd1070001064040100100d070302c950351280340d8100903800c5540360011518007900c030608040d60744c0c8941d031b2411803000c000d044500045d256060b415140d2144081621001a8043d007e44001d00080041946003000d139800541c0c101c8440d521400c220703400070700d1070166500c860b40e60f50800c4400028007840061500f08903102c3c0082c2c40e41c181920005880b40b19841c54001d00b000f422200c020b0001d4801c5c0c0c803003c0140b10761002c0c1c400081d036949800040e281941010340d1160342c0029030908615040003044003400c031703001c01c80381000e00d160006041400703001800400e01803440780120407c4100c00160000d802242401c40d01c40f280c0c00b84802c0141404100714840f0310500c00461902e900842800b41200d80050581c0e99102a40140c080c03205d900c40e199500d0640c490481c3e115a03038081c0040e00300c903400742d554645200300d6a0a504600c01d4080c1c0703001c0900c1c50217044c01e1020b440b030386800d0003079850909006c00180c0300c41c10200c0e0710380300342082481c0b154600807000c41d4060744902d0a03128002c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 872071196 1250 872069946 872069977
    0x2090619050322081204030e1002160914010b0c333403140f090d18090b010e0415090501062a08040b03070206070f1d01030926 56
    0x2c1600d5003203c10301e200300261810405101850341c1c503562a01440d0b00a00c40e281141600d03140714003158404102a4019003d07811441d50a4140d141d8940000001d00c05404140001e80821601902120040c02100307160900081d5819041c0b40c01c01900e000d180c01c014910281042c49130344030300c8401c3c1160134031801d203102001092103070420151841591684000e080c0c10302c02f40e000003804008403060440141600c916120002e0180c0021051156585030305400183c43c01020031810640d5403400b03d81801000d0124119401c0300c01d504100391440c1500020300707001402c00507540080b040d10444d6009040a4408100e440e00d01548421103c00140510403640c1754402982c0b01e100c0f520602c101080e1003a140120b440c034100407504440d0180f411145070035150029419181d0088812201580c010000e0005071030340700a0081004a40f450400180000d200701c80090404a0b01c0080c10191200b00040c1844151800c3c02d1814250610041484c3c3d9400101550703a04981c2041e000c605 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 872072446 1250 872071196 872071231
    0xa060f14041104060824040f050a05010f150f0216031a090607050708030612010228023f0c070f0f05060702011b08041d18070603020906190503 63
    0x81042c0554068820300c1e04e8a8800741c0ea141684000b045100c040f000039568941c4514486032036500c02c2c0c02000b01d03403a00200d0305180080701c00c0140e40d810f034440160320418110411090411840741e4041094500d0000540b24194000300c0c5000a405040030350501d8000b030020800204035404000b8600e40c025011144d82c400c5801d036141d00c0100c2314003000c620100b000c500002d040314021a80f00c1c6004001030011000c02004c030303003243c020002844001c9402ca840001030700c402220740d05100141e01c0203203207554896400b052203501c91401c1485001081c80e074041c013239500415000c0610000800c1c03a494420182b0716076030300c0040b440303201a040e159040c08a816000b50040e141a50300180050703142c001681e004542e640c0800d2482c11a1000c0080c4103000500400020702c01041800483e140a01030302600e00c030001c00107010404580700c15090010280800b2890308222412402d006890b0f0306c02c4004100c00f84542c5c0501c0c424030031002c5641c0307040e80d0803402843c0038050a00b82c6a4104 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 872073696 1250 872072446 872072471
    0x210180302160f090f1b03061e03030c080313050d03050106030c0801080a0308061305010f14040e06011406090604031b0b0a080c0d0207150603200a05090a060f1404 72
    0x2c0b819405001c0c1001e1a000e030520a852013900116a10b00c2400000202c020014003a0810400340201440020361984000c000c03070340c80c42120300700f18100c2800c4424840d29540c0c0c05055103a5000e0001c0c07181c0300220005140305030285040740819005420380d041c0c80080c4400400800c0c1c240240c60100349414401c2d8032480c420031402d8182d40c1d540c001080910315644007510041002426294029450f0411007410140c60090600034807102440c55032503400d04081c024804213000c4040e02562824001008861001401074111030410315006c00400a4901088440c4514101e0780d80000d800580042044055452504041c0001401004c8941c80c0c105444540c402c42c04040b0008031010041100d10328181d0081100c40031440740140760461a544200d140206081004041035580000b017081c0b140c07203080720b58800c1c61181020b81e800b4007038002138803003082c50088500408520340014140740c9a80e000d90068540c0702c0000c2941541c541050310110100001c59003d0b82c140307a4107103003c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 872074946 1250 872073696 872073733
    0x405010902010f0903170d0e070803120109230a020f12151203040303032403050d18080316140a0b01030309091401050103020901020709050a06030209010f05030a120210180302 77
    0x6032980300b041810703002c40540c3c076825185c1020704604805548c50306801c5884a0800111000342103800103182c0310003642d140b0000200c016400204000e0070001c401911600b20000c000d0030201040030b815098075195402402805055241c1805680004140c01070081c415030161090b0440c4c010601c2d107591600511001c11803800709a0800d5109100a0000034000e4208510107508030b2440210850f90110800420300203a02c19180b0f5006100003802c1187e0040c0507030222a104907000141c5868240742e240d80b0302c510b050070341c41c10200260b0081003042d401c142940b100c601c02d04650000e5528200040041002c1c80300b280456a821400509281c682c012a1100480700c0f042d485d2580c64240150301961000310041d045001c4c9200105d0404031600c44c3c54041c03440004001031840c203610500021082c1a0040100843d000000b0800c55a00041000c001c45e8005c07010103541c42d108005902c0c0441c4520051143c9061002c5012421025101804400d01035401c5451b00e48226580611 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 872076196 1250 872074946 872074949
    0x5090306060a0311011115010f14010e010e010309050c2e020a0c03120e030f16062a0311030d021e070b01170f060c030402190b0d0f02070204050405010902010f09 71
    0x1300c652000300131445602841d2080420f41005040c1d445042d804040001a00741c241c1000020060142c401d00400000302001c00100d40d003801c1c031124001500d00043d015a2912000d20b04250b16818020100710091002c08030450f00600000c000c03800860010304981c1010100c40920a009501d0005440c40001c24104d0641c00110580100d8103544480d0054441042c221040c0503e10050140c192010840f048a9005010207401c001e05c2000c0f0384620f0f003805500002c10400070401a03007030713401c401800400601c003c090307140c011b070b402d441c0070b84807079908011200d05400086802200101250000d102200f00354041c2e80402204080c511402e004444000c2e011a5400c3c1c0103128000c51850a0354088080b40e040394829002000d480e0b00c0e0203030844003580350410100a00c030031401c250324034010403114108507105c2c3c10304094520340c0c14010b94800a802c5a240c441003e01344e01d8a0f8121800b40350060402d11281c90a400c050f4080c0c00c803400300301e0010394032001d40342c1500d102d400f0150 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 872077446 1250 872076196 872076203
    0xb030a0809010f02071a0d060e0a140c09011d0d0804090203100e01030b130201050903010c09050f0d0b070804020d0204050a05071205010503150a0b0a1508010911041e1505090306060a03 81
    0x103909103040c5c03503d0f9900f1f4000410b00003507155a81c0e0041850300c50740d18040e11a030510310700415501c15150f01c41c0c10900001d410410292000d03c00708016a80192002c00c00880384500d03d80e0407452031001803807800c15480040e0035004000fa0100e11000c250300151b108a0b8800c0c0b03082045a6280440700e0740783c400b403002810003a09540800c11071032903000c0e0840041e00515155080288460000e400c6803445000c030750100721064000c010078203100704e41402d45007017118104103d1242d0f849038920190300404030f004000403240090119514422182540c5070080e0081240c2e250500d4518028403051b5540400f140c603100d074142004456000e01e6050340c0d00070b00a001c8015090180c041e10030000f80c00100c5181c1c4803014a40c0344d8841c8505400104104406c081203a0000c26003e44201c1e41a0400b500080c142841a0031140d482000c4070200ca0342c6d80c120b44174400078903401c0328110301d094000082c8003503080c5100c648250f101000c2e02d01407000701d0a072481601d42d1010024014850321005 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 872078696 1250 872077446 872077469
    0x1a0108030c12030606090603281d0d0e010f0903060221100506160c0305010c0509010f0905030706081801290a0e0414030712120e060f06130b030a0809010f0207 70
    0x2101c1601f0201c010b075402c50142d111500485194188801c40c40780d840304240500d9039610700002c0c00315003590806d001d142c141da0181c105100da05100506203050780e06010b041c0450242c2621506106014001c01980c1040c41152101c13030400d0085007890300494032004020303c1e98041150390203c4000301e0101c2d400100813501c1c0c882c80d2030600c415003105006c01d44542c80d02c82400004560280510241940319a40d06e640d40c4800e05e00140480801d044500c00b080361003001881030761030010340901a43d5442c1012022075641c01d03030860b6001880c070800590341d4202420020441038041503c0045c0040295032100e400c042d00034410800300b50302c03d42c00c9600c501c4002c600404c4c80409004546401c1d1811350b45000500d840d821840ba01c0710201000040c460603907000c90303c10a03c50f62041c5901080942402d040400044a1090000d800e06100303120301c2803031841c080100d81c0030714880030740541603070780340030190820012075000400c03400d000c02e603c8a22008010b20225015081e12401020b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 872079946 1250 872078696 872078707
    0x1051903150e0703141501080304030303050c070503070501060f0b0f1b0304080a05071a0304050307020f01031d0a0203010e0601050102060a1e0603200102070b12041a0108030c12030606 81
    0x10401c1405504850701c401640e41c9041e40d80403201800400065401009841c9140c0d01c00241d0900d040240c88901007011005001072120040200488080b2901450041450348440718400c00300e2040100c020214800060004200300064110800701c504050358495016603e00c29908030b4400e40000003102c0400b00a049001c1d1780c49038a0101000e1440304a9003020780f1900342a141c0303500603400356010345c40030600b00a01044a06480e03400381032400401e0942c2420b580d5076903603004094000344111544d03c031071042c59120f58414080001241c10b8400c00c0b14441546036118030400b00241d009508156501c0080600003031100d040b0760301a401481199141003040780185941850444070121690246402035014015000030794009e42121800010251203020000445403540c1c0c1903401ca560200221020002501e504001c540101500c81e9584d02d442e46280d098100a09104c0c1066800815420800805410303046820400c845110039181c0c81d2580c030340001c440a96000c80704201c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 872081196 1250 872079946 872079953
    0x307060509070e010303120b0402071e020f0a090204031a06030703020925030b011b0c0b07050106030204020f0c0f010e060105010f1b05010e19080f09030a14010207030801051903 78
    0x1056000010340d041c2c50b80103480d0304501c1035032602030740705070000faa40480041503800c11b841030401e10b42086400b180b82c15100d0f52050880e040d04030100200150070382444095494180051207120700003003414408546441c0b83c400203401074041941c3c02501c281c2d49541070644480e0a5019000040003411207900c3c60b420042c118400510040501001c50035281041c1d40100441c4056070b6141c42c08255860f0300000100964425050341030f081c0e0303240d00c206003c1032041c8224801c2d10100c413031b510b5961405041160142000f680000e408c40d1002440e80452400e10000c1d02030303400a07505481105001ea14041d003a40c1d01800940042c0d00418010801980603107030b03c41e03400c81603040c41c41024248a801d41c1803101816001d5681e40d459070f08c0300350503c40900103500a42e190054125100c19a5201c0700141c1c094840314180039200080c101905680070001119007642c01920520032078400d00300d43d4041d40201c10308402281d061800401c440c5091005412039400c548a0148502e140d510f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 872082446 1250 872081196 872081201
    0x902061605160e07080606121b0942031311101101270f02061e041508011409280e0708030903191a0a0507020d03020c030706 55
    0x410448151185445602c103240b00408207000406082c29824024500301c40060450080280620310400040105060946032080c1c0c80b5002920141000c2c0f00d01941c0241e0981c61040800050344080b02d04c1072901c2d00d024000c40b102141001000e200c0d0755441d8418540442900c510400031040303401c0c8000b61a078003a03c2030344480c00b80990b0044201c040a0170201d815a01e1404c6150005607002c051300320140000d0103400340b0045a054198451941006400c0092103102170082aa8400c4c03948072082d5078030385040e180614401e0703000c503680d030500013a141100c0d0301900c20b50b107442900c01d039051003050241e500b84d07040750304804c44242c0d00030001e0700700b000e201c4004240c604144a10365440d4030201c400d801aa41c0c5e1070302484000744040c40300a1062a01e5201d0348980c1c000c0c1d2003000500e4a43d10042070505100b5900d1600641102480c174000c05c80100501080c14104000c10401c420b050300381d000030380038001319000d40f40301c02d41c660001c034242d20400122500030b0384100b04c4a000105242d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 872083696 1250 872082446 872082487
    0x30f0f010b0f0315150603192a110106030c06020a11010207050604050d170d2309030a050d0624080901051015110114041202030703022a1f02010f090206 67
    0x101700d840d451a804400040c4981c0007500d01c1c0f2440e820600084201c0c2c0494442d00201c1c281c904501d0051844c1000c034000000e242c10091001c20107250200680b52400350842400345522038482164281ca6040082d501c2002000c103841c00d161003018400f02d54004517441007a00c40c0039000d03034034080c100014031039190030011003240d80f5010b041c0d881c0b5000e0112030240c09611a100d101240c011010041c80c1208a0302550384c40404444c441404040e14000084503c10300e600d007401d989942c400d502c6507000789219031082d0802594400c4106c03115541c1c84140e279684086845d40b0300d030b50321039103101400c94004561402c0c070450b0804003401400381659025603084464038040800b005c0b000780c5682507a00d90300c0031140c1203000c6024031017003144035800f00035204842d200850074400303a9180255541c02c100641400c600e004208550ba4070300001558507040b00261400007120924925410b00072030309490040107518240302c06600c068540103051030150010625402c088000c1c68015680505 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 872084946 1250 872083696 872083711
    0x20a0503240a030606090e010b0a050415090c0f0305010603021e0c010209031e06010b0a02060601030b010e121005060f0a05041505121615022a030f0f010b0f0315 71
    0x1003403004910796540800320000b441c411000400c48510b041c003040141c508550b220100c5074105481c10360143c030b5240c00c040c1116002c80b004144404001e9041c3c120100c070350003401942c1c1c18030f1808000660804141f8109503070ba03540802c01c90780d0300c9a040b402c070b000d0511381061112613404d5034202890b240c0003500000b284000014580104c0e078002030b1500e140040503800454940c2000c0740a04130900880340100360300341c00e0b0740c60900142e400035120500100701030705160b60780034214070340d9100714074500c1000005441c0901000c2c01c40400c40d540c061980b5072041c00e500b0320000a1003424400c3c3c0e00c0420303000240011040d5818401004064000c00f0b5180c102e01640560020b201e40e5210b00c0740800411002c0502000c0e2100d252444048019800c4007107a820135170b80c030000659000034948040c403c088c064058894000e4510754007030103141603141d41407040040486001c140403e815107a10401c00003004000c68500c1403045d80d0340a16040c81c1d06400855a4411036000212282d900004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 872086196 1250 872084946 872085001
    0x60c120615040801020c1b031c05130e090303060a061e03020309030f07080414010f0504291306030506120a03080c0903031306030506150d0903020307050109050f10020a0503 76
    0x300d030f502c0642281c2000313111040303951101414803c102c0e200a00000a01e00c190060125858160300012100e007c03c2802d40c108240002c2c0361251414400b03084010740220030100e1941d040000445030360b60000c2d940035210711900c6070002103160140c414400d1036200703464000b5011000175411380094000603c0b070f2410f40020000c2001d07804011006002c0e8900c910321840d1036038140098079500c40140c0303d266040c42080c1461440c1c80c1d81140c2603034100c907441142d0700301c1c10043c001c603110881c901e00401e40100e0070106050000340881022101503a44560b0100101d130350754400c02030241058074046030305821400400d00441e120750100707540030491501091801c02464046032030750f84402003900391044084818400d89516005054000604171102007000e402c9081540c1680326801022a145a498036450304040c024010fa03010b442d048802040f007004541011a21040c41e8140481e00380640040b6400112103407003510f105410585d511415035598512481e0300c00880400043d4640c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 872087446 1250 872086196 872086199
    0x90c09180b0702060906090309060f0c0c150333011b122105090d1d0a0305210310050405061f02010b1302041a090a0302030d11060c12061504 62
    0xc01045080b03004840741d80c001c084902c1d0502c0450300b8440080c00c410a260010800703003080d0382d6402d043d503044500150360b9640e1215002200c0b031411030460150394208450b1184040b0450070341000d50300c1030030003403e4028070041e446c0410843e210210241c41c09000e0694039003446510a414031104054140850340400310030b42c030785400549800c0c910310006094407481c803203030145039007103604e41e02d40c0740740300344224140140c5894031510f04e001c40f40100080ca80c00441030341d41d01000d541c000031001d800036030b0351038490411940310041141c448180581000300070b4104445402200d01c143d01581d1176000f0b080c202010400a06000390569500201c050004500d01c0e41c5040e0082040b01b0607000020061000c0c020f200c41402c01c0c00b05d1001c0c0620500c0700b0813801c1808005008800081440c4039030b5031200790001104c6c541241c0020703406100e50a0340343c1802c0d420440014983c0b00d00c5c02110700d9503448098a100d075104070005040d4481910300800d129042c844054000c00032143c40c9641001d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 872088696 1250 872087446 872087453
    0x71806091e0b030a0818150d09020a09051e0903040b0c15090a0c15020312070e0306090d050a03050c0f0c031e041401030b032a0f0a0b030609130606060c060b04090c0918 74
    0x79041f407450a00410343e65035000c01185014010b2f40014149158144100d240095404041c0003880442d490601500400690b658034103100301e41c040c040460b041a2210072202e411683c07011051100089401d41401240c8074520011f43c02400d56802182c0c607080f942008007481400c0103d43d401410740c8402d01441c1c010740c140c004014031035240307950f0340000c40b0751203000c15140c001d0182903200035030002010309005a6102d0202d5500c07050070300740480c0c42d80311284c0c00300b600d200d40000181910001300d0780c24680c841c044024500380742c502d0003803506120345043d200d00c00d00c070300d125250a103030400c144026a035000e50090304100c0c45c02000c0ea221090140d42c1e28468100d0140b00c1109030f030300421b05c070340a4984020500e100d01015a805648036007801c0c40010075100c09440700d0311600d1000000340b4600c01c83d2482404072030b4000018809903a0b0307040003400303440010340304544081c14540c0310b5400f0f04151040c01e9010344c000020942c13452400c003061008009814050003400d0400701d048020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 872089946 1250 872088696 872088739
    0x602030f060f0103060602120702010c120903170a02100905101401150507050c04051f1d0105030f06040602180a0b0301140a030302071806091e0b030a0818 68
    0x9004010980c221916007201004403103100740201e0ba06040c5041024084140d00203102c40c10f08400e6001103a440d5000c6c001a1036040301703c0d000500411035000d0107060198008880400c480c410600c4565003d8400400c4010380161906034006070721140004581d00c0094102203103031401755003928a4001c4262068044c1e81e0901544440a00c400004110604d1150001c030030060980c50000d051a14560701c8907250b03090041f14621450712000403949842e413030007000100c0b0742515000d40a4668402c1a0601900f41083c402c0030300c002c46000003040c0c24045080d001e45206900601000e80d00c1b592100000e40181445041a9580a160707040d1a100c1042c00030150502041c0700d03899626044030032140840031200c0314050301483d402040029000030b00312041d102c0c50742421928000c4500408003c0c5101c0c0d01c04030600b410802002402d00e0890140314a4004a990070300000300000c0a05a584c1c12641c4000d080701d40420120031403405c201c03480d03611114000c011f40603000c03460000c0c085 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 872091196 1250 872089946 872089951
    0xa050c01020708070308031303271403010614060f04052e050a021e0c040e1b060c030d020a0c41190609060504150b090411060c0f070f0512071a16060203 67
    0x401598ae943c00c0c0881c69105210790000b0b00304500030722466090414180e100b00711103020501400012540300d4219003408190380151202902280c902d401441c6042ccd801c221800000240a0008401e035907460311450468200d4202a001802803c06404103001c0e66102c0d0755000149009440111a0540d554001e07003012008400080c901406a441c00380886091040e51a1042104006110350060044150355445540082c0141c9400740300c581559420311020000700b202c54079602a0707400d0b034941d000300b90303c0d40c0d1104c26100c14208190101c0f03080c0ba041c2c841c00710f1251300124548080d1000491508510f5118003404500001c1c2680c1d88002d60b2015907048034500c000d0341e02151700351101c2c45071080528040f205a400c1742001d48854440d08604599140240710001d1401c648000411034840d607150380104543d825590b49021085440311030081381e11624101e04003000c0048001400300944100300c845944042d40501c0c4811240d10803113110202481d108014000300c1e40d144095031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 872092446 1250 872091196 872091257
    0x8060f09130501052406131206090b060108220c05030706230708180f1f030e0102030439080a020a05060a0c060509010e0a050c01020708070308031303 66
    0x1c1c18040d00b0301d409030941d10000c1c072024502c070007007a4040d441c622030810f0480c8507900b500e00e40c3e502c184c451528004204140c1100400800d10380d00c400c2046202d601c909519405070705e0ba03440644442d0b0044800100c02d581220b5100600c4031441c20756045240000e00031841080d0b03050342240d0303440100e8206240b40c1d2100010503964910030030801100c3c0c0c880001409018031081c42c00019958141090044024580601007848041403072070715102c1c5405000c5d00010050f10003a0b0088490483c003181c18090308000034207040a07582c0a041c1402501d000d84ea0102c04110340010300a65034420030141c044a5a01c01e600e00c4009031880701492101d030142507418040c0c140c006060040c014012003c0c1d1205002e14010000d40d07046503481072038070b80d5065100001040070744603040503901518482510f00340078010a11000104440000e102d586904203800340c4002954402146844131010b200c0944110810400101111115660607025520a0820300d02d20302c510707a030407140d88841b00e541a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 872093696 1250 872092446 872092471
    0x160b040b06030708030a1d0d06091511090901050402030601031104060305010302010f08160c0c05060f0d0b0405090a120302120c030a05011a0412020a15090f060c02090708060f09 78
    0x70440c2000d015400140962000440ca02140c80d0381c01002d00000346c0c02484404010b00d001001c0d40e840510210000b80c12480a1010004034142028612014a841d6201038a0300414185c024856010b44010744e0b00141a2211a032801050001960004005034100f6a545150244c040302c21070140001e03054654000503158150b00c0050304052000c03005c0d106008081040020504400700c59608000182c030384146010298904190f01c0083c6410843d84554045044462000e00d0000342040c6405100309224600070401131004484041c2c1d00c405440d00070707028a4001c1031034101c41c0196020b451400614002c0300101034400c0c54001d890624410f50000203002c0341020354020a030240c00c600174602c41d055422102c221080c0314a11503111039000411014040d5075440820000400300200c034040485c05509000703003c000305020740e10185aa2010208030b1910410310801850340c0a4002c2c02c407511400710550740184000c01c599030240c0d901505030055101c0071461405526081c020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 872094946 1250 872093696 872093701
    0x1d030c070e150f0109050301020d0e19030915050426011a100c0c0b04060c030f09060206070e2205090f0c0604150210052805060114160b040b 62
    0x1400c0c2004181d6112264698041c0309000c20001c080d800c900c4a10030454000044009503001610b2400041c0c0c4425490351000c600b45156800ca9040111030003521070039540b240c101c0890080005001030b03006000540209410b01c5641d480c002e019221058070308055003003540c2d0701181100074900e501c02c45581c00745910b43c09030016003405143c03102c000c5000c03070845860411000c5802017070415411810000050b11800511031810040c00142980c2480180c0d0741d501c800300501040f00f6400700300d002402001c51a00e02034800d4070040241c0f4400d5000d484251503545049800b64000f04c0b0003903000d45001811015504403151408010b021504045081d240200c207407402c0c14001c1c83d44080c070350062403046081d6a03c510449003038500301c0241000c00f03005207104901d450b0422641404003442d01c014030107540d0810480e9413410701c001c100b04018203200035404c8180c80302990000d0119502200720041c082c0c1c5c0c14040c08205e0303182c4840c0a0009440d07212025094802c1c0d9040d600c0403508001d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 872096196 1250 872094946 872094967
    0xc06060b190309111e060d0501141e0402090f04020a0914030c01090e0702030705060106121109100c0809030304030b090708010209100c111003020310080d020d0c0203011d03 76
    0x40d407604044050400b040011666107424a05a5a850001e4410101d4a00c0c0022040700084600c2001101030103e43d10348110140c100001c0c00203002c0c81112948140b880582880c0c0302c5900d1030902000c461600c1200c07168003d00019420040605a1103440380d07044e000651550b101030010032042c0e40d100300f022841c020100c1100011440003034043d8001203602d14046e6001111142215a5450f40b43d105641381d241c128118058404014014010540000740d81070b449003100c0c0d03c141c0c030310300100400e0503144001d084520504092035081a0414400350b4414029104c103003155008002052070003d4043c002400e40d80581c2007201c000d01a00140b01940e00300f008440003a11418008600d001612000111403000c03c07000d8804020700f0a80b00e40c100036000d204a8040807019000007056503000d40080c0107900120740c400401c5500710780028100c84000b542c401e400000e034000d0201003600c141e08503616116290180d070150340b1800c0030080f0a040039228080506140003a640390b6120a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 872097446 1250 872096196 872096227
    0xf0b0604050a0c0e130e0304060807021b010f0c14030318010e0607050405060d14130614042f0a0303051215010e040b010309050604060506010e01022b0c06060b 70
    0x8003000a854908503048402507003040c4140e00010080b51172943c2d04844904030702c0500341060248005000110740090030b150072034990780c007800d04e41d000d80305900c1032100d83c08a0203000321a524005085000e0214005000380880450140502c4491a85409080c0080c0c13640e03005503050046030300403c1224640850a20402000740d800c03101801460620081c018018052030007107910540001039040d0344141244c1c040205460300c40d0074100c161900d45404400c0f178040800607106030782410380402c2d500c20100b203202d100725480198218245440070303c3d00e144d03400c1010607540c00e030099070090303402d0350f00d40b510b240c0110301c02e9940995400442000b04044c01016150040b996800e00100741c0b981c0c0c0110707154400d084180c800050321012440101c0140106002c007404900405003400144030f0300d078203c9441141e0a0b01e03503062590441004980d6083c43c9503541c0d41c1c6e00e06000101510400351403156a00d160180b6002c001a90103071613a078101d861652184219241c00100178110100c42c5 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 872098696 1250 872097446 872097451
    0xf0f0f0c060304050d2007080c09090d1e05130f0305070b0a0207092325090501051803070b0d0504030207060c1a0703150e1504090201120b0109030f0b060405 69
    0x5076401811030500d035484983c1e0380081180d074001e000c4444114a18641c0407a00d44102120301c07801c4624a643e00e941407a00c2c1c80440c0f0780140119140700004040b0100041c80300c00680302c59070707502d402076002c81c200d580c072400316920070f41005805c124084c030034090340103504054441403681d4581c0500d149072503403034218240d201c035007502014007002901d42d13004988001203540c12000400e61800c02c0c0801070488040f901c01c0d00700d50400c1d03401d004440740d5061039a020340b60760807484154200043c2050b44c0d0711010b8030680f80002c108010341005080c64080d501c0806201070100c0e14401d49a4003c1005070b00484149107420f43c1d00d904100904ad8100071000c0207002c5d50812500f0003000d51150301115513500034009120101f50045901d0521030303445900c2c504240c0383c04c2140340c1c0d15000e84980040c0d0035140d04044038885043c007003d5260511031000599030503142c0c0190006944c4079100035102e5603400070b060000c0340780d000001c10144084080218070840d4200101d05d0814104421034901 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 872099946 1250 872098696 872098699
    0x100e0f10090506370804030c020613090c030f0e030405121507020d0e091b070311070609030624030b040602040e0a06150c0b0a0b030106030f0602040e0a021306110f0f0f0c 75
    0x80303030042e0344d50001c114170f4220340c05141040c0d480e0309038000b241c0984111a6031b400b4821f0303051800188a5030b1075014555110741c90303505000544c0081e0b88003041c0e54508104400d141c008020400c2185041184280d4410244058900e44068400f0304240e40c1c10440f0302c400503810456001e03401a920a2080d0091417007207a400489003019030320035044142190200c020b4500c006400c10a05d8040e02e0f5910300042d412044840d116250344000f88003070345620041b1005030501038403444011800320301c0350100300c1d11525007041520b180c40e5410352100191096640681c00c210100718100f080680910403000d000c40417a005e860624000c2210880c82c02c11010015604005400075130220f405640240055070041003200003000020700410f001d5100030140d82d001c044182c00c200ca1600038000300c1e40f41218400c00c60b82c03510358880c2684202c05040c041c0362601c041c00d000050280034103040810888040703419100780300c0100b03460700341614162449507110156820505204020001c2c001c00c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 872101196 1250 872099946 872100037
    0x20a110a0b040b04051011040801200306010c1e1b1d0c03070314090a0506090613060207030903080705010e0c121005150a060806100e0f10090506 64
    0x1003600c410341e01403005000204210080310204040c0401000a09075500080008001141071605408400e504c07921688480b9401d2031407c0d02600a08907004d814150642c19151550303a410004460000c0035a400703c0303c141e084d20415000105103002885114800e84100d440c9164083d44c800032004d1660148000c19488044601403070b0b80bc041141c0c005030000030560f100c0d114508141c018001440c0307801c9001c1440700030000e03899000a11700c0748160044098a48549800e4405e5484407012a450a407401d582091400043e1040d801008030500a1400f400303c580c403a42c40381c02030343c000502034419a444010150712103005000101c3e100804079100210032020390f0f41651a905c000d1090b0242a654400156916001a0103042030800090210814980340d19015001100a5600341e0042001c02c0307041a20a00a0450501418009001032401d500410400142d0150031000d80100004064005515100d070b001800c40108a1245060040c0003040159040c40ea1046405189175 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 872102446 1250 872101196 872101213
    0x60f011d04021305100803340309031712240303030106090b0913110d0b0105030106050417070f12020301050a0213030b0a0b0a0f170d140901020709050703020a11 71
    0x1d90f0f0060000c100b0303141610104180e0b4171040c050404e542d107644809220700000400c241180103443e080e0a0001c8007005080d1844611107090350011031802009021401200c01440450341031a400c088807129401103a25080c000701c885000000e00751107084980c4421100c0205100400b10504500201a40114115890580014030f01c007000c1c4113090400c540024082034503101c560000b032a0200c564000d11041c5060100c03541f039070b4808e128072071200d85040c0384000705612803000c81c1d04070381e4940da40f181460304250104421302560f030580c2e800742c41180e800041400b11007070742d4801803034895803a20a145041c0149400d40780000e081e01e496910410404401040514604040c0d0703402007030a102d2030f0350f6546070000400703400e411207070b000d8192040001e40441120b0100b040c1c0398a03144541c10889090b5003030b69104030080d207580100341e941d00d884d0005c0c1c07045000707002d12030300520482d041640e66480328400c0b84e9080e038800000076000a80d800c51130b60030455010109001c0c100500045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 872103696 1250 872102446 872102449
    0x30605090d1e020309090f1603140420031c14130e07051e040501090603090f0314090d0501020a0e100f120e0d030e010c02160521060f011d0402 63
    0x4240c00c0101c2c0140d018007807940d50500c0c4200140c40c130718600982881068102040e504540f030701c045404c03868407200103070482d101c14402c3c011500604205900b414942c0c441e641c0301000c840304144210341c12508150700401039a020000140d8286815182c1c41c1014000840103001d2901c00e400215411002c1054060a65200c0c40c944100d803580c1800381403139103590b00111150711501042d50720784145080c035480240e403440020030407548240c90f00203a01d951100203038240c64000344090804002505102e010034050f0340010201e00a0030340c000c0c6440318803000034801124418042d94030b0b030350128020481c5a0041c1d000c141510041340d000c840c3e070f010014000c0215542c50b5030442000902c5e81d41600c0e080b02508140d00340c2c0780000580f11204101c0500a00424180403090015030800825110160021940c2a01801380f190603500c00d074100418040110800a001030743c0e65402d42003d005c00b0f809000c03040c05003000c0036140c1565454046440000c451550300d242c1c603000500c0610005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 872104946 1250 872103696 872103707
    0x1217090111033402010b010e040c0e040507140c0102071e08041a0904091b06110c0603090a0c0e15091005090a0e01050115110304080d080a090516030605090d 69
    0x300c0504082c4044828610701103d0060240100d11500340c259280701071582c1c040d009003c42079001c0c0da80b8411000ca52082009491400030303c0c1012506100707100106040c00e4012030352112071800c2240c1d041917050300b00c0c601036011300c60120741c03071754086005010480c401c1c14901503050354408407540f000e400d4580d0f00203449a4400e41c0341c4140e03c1e00700c085401e00040f0985192600c010b0041003410458100031901149a03451020072210101011070345a001d0000040508e0561000b011178504540030700809500180c40052280305a0a5040002d6200145c03074010301030041003040c50742043c5481d100c1681c001000d0a101d44004c0c0100b00c6a500d59a014200316a012640c5074102d4403a040143c00030102c9900c001019400d01d00045241c0f14283c03002d52118030142c3e140030300740052004490310b0780a14012400d45810078000108068440e01e5600c3d042140610005031400699035860314001040110358502c180340d00041040c40782a00c907459000c0050741c05011000f0303000500602 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 872106196 1250 872104946 872104951
    0xc07030203250203070b070312050c090118090203100609121104050408070f0302031308120313170c0601050906240310030c0e0103050f07030503030121121709011103 73
    0x14001d0540342c080b00010340c14070700510040c0c3c024081d202c00341d45410001c406a40091400d0300410a0042c009169540e544641c0c0e104981d040111802c1504500c01119030140e9944080c1002007000c1c0040b07280d010502c001d50003281001404151240781102c050004409580890404c060742080d84010492010410303072400c8084500050941d01c81c41c0404240c0035541010700b2403079602c00c40c181007540000003000304c000c40c0709000710380b240d6840c00300350f079800214102d0382c41080502c08540012142000002c0ea584038426501d0090340d2900701e0060f41d007041c42014038560040d00104494280600e801e90400d80a0b00d00d50814403646036003440e411160307802a105080001b00042c0c0d417511250808018542c44035005c52904c1d520300d40d04120755000e00096406010302c2d02d111440e01400901082265480b0010792b00390ba10700140c0e010803c203884110301e00510308150680005030440d8a0f5034403076641c1c1e1610300b00d43c3d5a4586000501d2801001d00c00c0982c90682c0000c102401e00c0305803076 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 872107446 1250 872106196 872106217
    0x604030b0a022503180f081015051906090e0103051c18062123061f0201090615050a180209040c0c031d06030c090315011206050c07030203 61
    0x41c2e0b2040340704000f004208450040c0c020000942c62004101a0b2001c201d45020301c40b051400d03400781d210340e403c090110b8030780700f4905a0b0748078240f80c0701108000d400602d290500c410211141d00e80c0d900110b080c0c002030402c01140f0380c241c03a0041c066107410440070f03009400c2074240071690b5811603a8031782e902c84580344c4182e088401c040d40444c04a10682c0c0020b081c08103802d61500c900d03a90a405420a400e410307a41421148a1825190849403440340010104030401d4070003101d410700011905400c00078251980001008074038000c442d2007110b4800c480c82e9264000070344140ca50808c8011105804254140a070100d2410095917403210345601c00e4550f0103401084103520301f24010024400c0711003603500709051004108200380c0084060165a01030348a0021100303140d03c80011804062501642c004401c0c0041810201048003134040d0f840f0140490755603503520420750b00e004901b44e00c6100340c406c480000718104800c2c0d00446411051030303039125003081003a80d0007a469000782d0001070b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 872108696 1250 872107446 872107451
    0x1050702010810180902120328180e19110301180608010c111605310501090213080106030f0206090a1203050901030b1206160509040e0d030b0604030b0a 67
    0x6010441614141c0c0c0100040420f504401311107a28040c003a15041c40c043c0d01c508051a015020004084200d500b461300050140c40b25046101d1a4030045a10303034060010861030050380d00d004140c40312494050590f03c01d441c5000d01e440e4510f01d203004242940b9001e240d042041c404142c944643c2641e05540702d044c3c1f5224025020030411006202d194803480c4150300740603e8a0a10340c01518110601041e101035031480c05c804130040408503a103100300c640240c0040d10180d9403209a40c0c01c600c0544a100d600c1e001d05a040c503580c010b42d8000c0e080044041c1d40020b007400007000004815000b00304240081c4885031458580c032032000c00303041021380580d0001902101540d15241140040d003011140c0d080d0135507c80c10000d050b0341000700800e0200307103024068900c038075044d00d00b400880f2103507005010311341c3d0710186031022400e8008200c0a010307040c0450340d031542d01e40c0220408540c80c0001008840d4000030001c094404c540309150041c20208400d1011900403440c1d10b40c00074800101 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 872109946 1250 872108696 872108701
    0x1d031507030f09022817030d050406111b0f0a150b010306080f0601050118210303020c0a0b0604050f0f13080f0703030911150a18150c03080702030306010507020108 72
    0x1003400f806042e84000c0d0b1000402000e1075081803048081d84078a196800742c1007a55480b07000e0031800c98004451909964000d20999443c1080d84e04041c0d0302c14810a000700c3e010040f8135015140d90407841a4243e850200c0f110020701007401c1241041910012004102407261521003401d88810740c940c00740d501d6250000101e9a0340a500410300410300c5504499102d2a002c3c00180c03151000c0c012540041c200d02c1d440c40c1040c3c180380d0108160703200340d40300710b400b0010940188510300b0a41c80031024035409000b85050000140b2000c06018080c804800c0c1625203042040100c80c0f0007454851841e09050a11449400054140354400c0080d0488440706043d03040c030a1107809440c26581c64418006500b108055041d080107900700d1140d1002d99104074900b007080a824199140d01162100500c4040800ca200391402d43c1d8030309500c0c503a8564a510f030401e01030105e625940c0c1402140000850104240d4400c51080e4001703040d00c0554214140080000c0c814450711501070b0400501102 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 872111196 1250 872109946 872109971
    0x10203091b0a0332031909050f0103180c060c14010606021f060801180210020c011421090604050f1504022e0908010c0503040b06090405100207031d03150703 69
    0x80c6260005585140c00700c090130903001242d99a0240303031001120200c018262601038040c1006c3e00c2900d000810070003114120300d0045000304924003017189010040c5580102048030180c24001514565079851001b0030340e8282204105444c61000c080c03a0300d09102080035a901103034944980d816685010700301c4c070403108801c002e801c094016003079551816013200d0b80340403030f0b07154400058400e40c0c402420000e4840c003607031a0030910f039003240890402d207103008862482c5002880c910070700c081801018003214408840001c021200f41045a00250901060080c100480010359800500402c942c95084480000046000d00001e028560703c400a078122511214101c0c030105400c524000010b602d005c0080406031284122501c0f94a400582c00900784100212031241750010f095250300e840750700c01d1001e0018010300903201c500440e00031590340180c03070006011032406503540c0c1d0348a03901102c014102b04125080144294071601141141c806000c04541c0e0008040c140050450619038 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 872112446 1250 872111196 872111243
    0x105090106240509131b08060301020703090501050d020d181e080904021308010c08240105090f06040803071119060c0b0402040e0d051209060105011713080309010203091b0a03 77
    0x4100e446450b003021b840540c3e90781024046c0e402c18070b5540e514095610341c14145400c03486030f42406400140da0480a1011354095002840111240c1c50f00500c1c20320000c401c101203844820302054903680011104040c0700c0101c0e152201d1064000c250701d02001142ea48010500c90708640a0040d44c001c034185c400346404002c3d400060250384001d001518406078020110002141c10b0850003051150240d09020407000d200c0b000041a11024580100c80e0104000745008040c0c082d80250700300320105002d0003d001402c16a44a11020340d41140e04000b0052030712003c8490708168104a0802c2043c20b40c41203644642541241c09000551202c0c004107000d0a0100d41c284400d1041e40e9403842c056a200c2c000b003800c20781a00c104529621038200040d20381c00300384112800145900340d20120407620f00c4940b42c01c64110070b0684004440703a5102441a0070484400146944c007004028142e08141301c6500030304406200c6d02c140381c1600000494041c0d0a00001c5c054000a00711100d00f5030885 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 872113696 1250 872112446 872112469
    0xf030f060303021e0105010f0b131e0f09050613020d0603060216030e040615180503010c030e0c09040b0c0a050d02070b0912190318060e0105090106240509 68
    0x2060054070388906000e540c9196210011910340000d00203010f0481040c4103183c140c1e03a00742218440d00e858950358181541210100c810000e1aaa00002e56025458604604240070450191020f85001102c8000c60fa40c0c1d400311010906000410000d81e5581d480001d03149441d44005840d21881e0003140010603903a000102000e1001911130381e201c504031b40d150a43c2e48a0b548080c207540042007408280c510f20f00c50103901d000c10100c8198024022154000c039003007520740c4e81a515981d080060b0942d50781518120109645040501c1000301c00e20142c010180c1c01d8440b503586040c26500e9100002d80100000714605006c162000070034070520440720402e03000481035446068034207140700342c040181c034014214411090a612995904400c0d034540403d05806180441000581500a080c0c640801d00b80c01032410903480000e680c070710441c08401020b1340005002d142c074141203421034025402c061a07281d01e158038004207000f091403201c01c0e1212443c10544540b00100403a2074007024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 872114946 1250 872113696 872113721
    0x70609350c04090302010b0a05040204030c0e0613111e0a022a1905180c18010c0203031918080a122307030201060603021204020415051002030306030c0117070f03 71
    0x280f0080b98241607054001244c0700c01d046a80302e14072641c90082100b2032203a0710004091188a1204011400443e00c4144e848140946444880d20b0b0b8409100100e41c0d0002d0069105800817801e400804141c106e44126100c1d2541e0f030629100225030083d50b80c0d00c041c0b9031600e0000d8101400703100d02203070450f00092500f0140072010306003646940100c92062500030640036a1180703036002c42c10341242c035009005d114100ca1482c90314400c40075848040061041d02d40c141300c0303110400801070714104010983c50540a8600c0000c00048074010a00d40c0c41103081c005811703146105002000c4086000030409621081240d480001060151078540d01e0384207080c0480361400d822000e02c8124002068164031940c000c010f03c2e91140d0017501240243c00140c038000300e00d800014010b0820340d200c1003003042100c60b201c08480e40d600001e43c1c11481d0040c19801a00007006014460a04011089000e2001d00f0500c01080300500c460019500083c50441003111900420241902070f502c40c1018480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 872116196 1250 872114946 872114951
    0x6051e0111070e0a0c030213210c030f020f0a08030d0e150709080609010c0801141f020d08101203050a050705031612090b031305010b04050108070609350c04 69
    0x60301c2a00c0228030034204ea0380c01c1e0960910382d01481c5144248200c0d003a1300100140c0201c038500740b01101d013888101911020a2003511403861001c90700050240c0300035442010701b070030740b01054410300c205800ca501e110346c000c004910b0107000f03650740402568003c041000d00044e1800310703100c18928119075412031450141c0881d060007001c41c0d00c50317815415200841704a03515500c81d0300c032007800c80310780004203000560f004005004403050241110b120b60700040c2404c148400200e019010803454550001c05a030110b40500c00943d041407040f98003d2602703002405c040c1c42c0c9654046800009003004041000014090704c44a00510590310029008402c0300d4540030007940c056420358040c0c0f07040d03a5400c00c0308904404c0c148507220740815a080c41c1740d59801c41e01da01c8191905845108800c070740a540326007400d40306880310f105040c02400424020245c01c0e203032820142240780710b50495420701c001e40000394245015181c000c0401b0441500e00c0c00c0c00541100028107040c9803400c40c070ba1090 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 872117446 1250 872116196 872116199
    0x9041503021008161803020f01050c060106030b0f09090607050705160801090b01050d05100b061c02030103021008040305070f110d0b0106200c060a1404120605060406051e011107 78
    0x41d80240a18898016011302c03a003c40381025040d91a10a29100a410043c03171180c01e2005041140ca2504a0752060510303d0400100c2140503003483d0098200c0000242d54041140d054505100111980b56060310031100c2410140e641c01e44480c0f0040c040c4081c0040052000104801049009401e03045001a0b140f200d03180c00901e4040c0050040988214255400108161a1460120044030b6000006042109440b050a00905003080015a01c11014442d500000384006c85500240003010303001681d82d0306510400221051031800d200400c8114820000001c2e001012200c107540c11880c1440e6001e010700d00b11040040511216412020000000041100100724241aa03076251034480c4941801010805510700c40111b01419612000780c802890034010004d011080c030b6460000c40b4107401c450400a568016841140e0070b0454180b10814018140300341d51f044032080f1014000c01d4504000175003182002079a45910030304091100515070b0090482c1c2e034050b18004151201306 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 872118696 1250 872117446 872117479
    0x230d140306091b0f090a152c031e060705040b030f19110705071406040e101508011406030c07120c06240e0c2506020412110306010b0904150302 63
    0x54000b244e415001d0031b9240000b182d2005143c0c2c0c6029400380c25522030180c8040d07411005084404605035803400700c42c00880300001e490510081f50300d0600750840404180260140510708800200034904101040c44144411486030701141d40000500320115101d80340d0307400384600029011802030f0003910b40f0200300c240f10103c9018044050080c0291200c0c43d99551140b000c0d07081078660300754003c0c400c100c20b100080300c41c0e05213034004481c2885628001c1d20340d204d054000008280f448041b0b102a0010892012481701158a143e411744551b800c1d4180424200018060064010550070191043c01e09143c031400b803c0003e5a04420f05002c09410048000125107940c0745450180301c01c01b0340401c0c8032a1001d401e500031007000104600d0140d0751036449501c03840f4100c00210300f104041c0c2030400f244803800508003070700e9840382c10043d400147c50140c02980b01036810038003e400400c0100020507440342a00d8100c5800e49010410108039847c13402251042d4000a610800e41c0284035540d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 872119946 1250 872118696 872118727
    0xe3a081c06210308070315080d02030418020a1d0d0204110a031a0604063614120a0303020904020d181e0b060f010c230d140306091b 58
    0x211400a8242e10001c031002c03203000905100020003801203a01c4034080780c0841e01c83c0c0d11120000e0000101c41340c603a911041c440d418401d0004040006900201341400018000c0450004140034048114030340b600341c1c1030161015403000103c5050282160780d164090302c0d860b00c0070040e2a801082041f2030301a032210121290064440da500086c0b034a49615080b188500c41d0b00404c1c2d50080500d810315181480c01c68024000480355188a00c0d40108002c10040c0ba01e0210318a0082040700c840d69420031400c055910500c400243c030a0713840c441c0c1d00840c4d0307101040d01002e041d01494003595540b800b40106002e0b00c81e002c90b01b07010914000a03442450343e000300e40c604452164549000c0305401d0842c0d17800c84081034101074105501313100840d82078540028114910001030411100b01121030300c1c0d528942d40d000d5042000c0740c7c03021680d10042c0c0d60601c4200c8600041d42000c034411000d1f410851558000203100702d002e000c244001ca10500840c00c441255941e015407603035034900080150004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 872121196 1250 872119946 872119949
    0x1e020d0e0709060e0a0e070b0c01050405010b06070803160e0604090f14101401180608090d0503090c0906030703061503030e0a0b0a050702040b09070e3a081c06 70
    0x2030307014950000c184110507000d0340341222460528814030307880e0213841d64000c203003a1200480d50f204a09000800c01d039480060410500d00e08000070380c619140c1040d40c20344180d03101e220301c2040c04018106c009848001600d07006502d007058006601d84450043d1007541e64815941d40c4100041000101041e564020308280020304100340803e070114240280200c130103444040701440008802d0100c40c100003641c8140500524002e43c2156821a02c0c4d5510310460f00448002061001005007504042004507454001850564a54640111801d44070f514104005120740e094101141259904000304d601a42c0c11603070030069180700d1041c00e2a5580188021400301d0310080c0722201a140c82c107040030072a5141d40c0020303d85000c0e14030840300f070b40c4907000072a03015964040d00501510307000d01c087c0c1f00d00c18580f118101000d114040011445503444d00300001c0148002e41d145500c00b28020642104116a22420803120351514035000c1c0100018606024680300220126a504d03411420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 872122302 1106 872121196 872121221
    0x20405060f0c010509151f2d061103030c0703121d12071101180e0c130b120c0315030715090e0403121e020d 48
    0x128607030812865420031820118440311401e509124241d04000680000c2614018100000900c00700c010147c5040540c1c0745409910011310031400d10181c020190b11190b01e9200b000d181910300f2883c010740c030380501d00f400e0000e2100d00811a140c210103440c0c000d58a1030340c0d2505102e41d250b100250807010031081001424141c06107104140e20b41c3c040d81051a403605c1d1040c9107a00d014080c0f424000441420000000041d00d1162a450000d10a00389a0b800d10712004002c00b04202591000c1c0d0b840c2001c130200030308280304600400c0c14204a020724400c103525859500120300901c408148085050030204201c02d906c900a1079201044241c1001108103200c042030400b440c59100d02d214601814020004e990013140d024041e000c5491526514a46628004c003e415110002001c45584400c1110000707140c8110f4a0136050010f400e541e02c1c080203095a00078000c400d00c02c0c = true := by decide +kernel

theorem cover : BRFrame.Cov 871942446 872122302 := by
  have h0 := BRFrame.cov_init 871942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 871942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 871942446 ≤ n) (h2 : n < 872122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
