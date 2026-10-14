-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0605
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:41:49.752365+00:00
-- url     : https://prove2.me/submissions/a78d65f3-2dfc-4912-a878-3f7e035013e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 108633093 ≤ n < 108812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 108634343 1250 108633093 108633097
    0x207030908030307020616050a0c03030f1e0603170c07050f0109031a070809030906120a02070f03020c010f080609070c0311030d0218060c0601030f020a0302131d121b03 74
    0x4050050b030b40c680c43c2509000b59104421240c0140c4c00c2c201c190f1099159000340100e4004e4060f030707500d4030200102603c0c203801801d4200c1c1c0480445544062580c44031400803040040391304c4420b0086040ca140d0300308041542005050003824050403c0044000240050098225030342654455840081540140c900345226030004d0080000f040c4421941c60042e10901c0c440c6100f0b1321401003e84440d07860039a0390040c825444d8110f5010044403480f04440c50080d5441801e524000d403400c111543c80800040301d540080300540e1155140600315a0002c0031441610141d16001c5020300c0e0141c0002c14008000c0c108070240400d5502c8001498802c04100364940000001c9036958810658000c000f5480520700c650072401c40300c55075203145404002c40b43c441c01010010040c590940d01c5048244070b0100c401c03a413207002c4c2c0d400040140c903004c8012241940300c140c0001c800a41d401c56a12040404400954541254060b40003045d0443d00780c4044400e5030030501402e1512000c1103140d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 108635593 1250 108634343 108634349
    0x30f1606090221070b0c120c0703170408101b030203090f010e0a051603030e060d0603021e0405250c0606050406030b0414010501060804060902060d060906090b030a120302070309 78
    0x10f68001900d030a00300030122800e50711184115010190703609003098040c09900a04d904e550042400038592a15580c040c000000004003681c10310f80d941d580300d0085000885001c0f03901c0c04003060401005038288026a00380304504018130064044442c007900ca06031400c84201896408000305500003c10080074003010318041c000c201e0301c1c0c201c0182c0d41d500d01d0000811140c40c45400c07055942d032200020300d20700701c0c0e034561503070781a501c2607000f08041600400009031a0640e1201c00101603940c034000c40e52110071460101c800d0422000c148800d9070f0005007003440f0800c071500f619840301100540d07000c4845041c42e104c518409603141041c090581980056849401e1400100611003d01e060358051485410342d4004040141481030a987c000d10804000c140401c0015012400d550081c0c0851072000701094900b1310200e0600003140c07116040601102d035500350500070405540301d43c180e5180101c0007001da8550a42d140308615150749240c208140d00401d04a00700350088002c00d020f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 108636843 1250 108635593 108635599
    0x11203030504050a0b0a0e0c0102010b0a0501080c0705030f130501020c0d02040c0e060d020301061b0b010b0d14070908070906050609060c0715080403020c040c0516030207050a03150b03030f16060902 87
    0x40c108014104c6c05010940c1046016000d01107010506600500c0341046043d405400c420a080c80e02e001550b440c00020281c00c034050042000000140060000303040c5859124030f03640c3c950800c102c10305181d8510f904454199030041f00c2101081d9500d0148035801c50b412a00400d1443c40020100d915600d41704507103420620219400d0010180c540203541a03580c186c1e0b80b0300c1c0040d100050168548903900014101c803e0f04001030010100d2100144200203440c1d1020510048031101c0d0700d5043d01c119113010010b80520340138003040c4818400306004000c8164248002400c00c07001940e03a01c65503504612940307001884051243c03050014034028446030419000f910282607004e0301004084604600501800716002c1e00c0f45441c4c86681601445aa145d0b402d05c042100c50808505c8144401d4081d0310601000281a40c1c503880d120010714420300401d0b44803640030310880191000208002e110390000c0c08401d008007082c805031800c4801c07540c3d03811191041c6091130320091080d03c5010390 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 108638093 1250 108636843 108636863
    0x60902040311030d0e0a06030e01021b0a03020c04020f09040e0f06090307061415040c0e040606170a020406020a031b050102031014040e06070f02120c010603120503011203030504050a 80
    0x18466040e10507282c0000c10303001e0722a4901e480754116001083d0303405131079203e07441d00f07410300c03e141c8079034000420200070f01e00040c6170020758010303000740e4401a1128906580b088602c002015414040040290010348042d41000c0c00d20f2984205401403040c401c0c02180c3d554107038008444204400c180340307410075003551749908004a80a840b98403060082c0c2ea503604200502d1034007055170300e640e07110320f60b08262620f014400c207041102034481001d010082000c600865400b0b03a4540c400c50b0000c045580b503088001031283c5014107050b50046c800d03480c003441400100500da4000c030f24001655410f05d00000701143c4405c042841ca8a000700240c81580b001c03081102d070400804860b02a50b0702c0402d42d001e004114010003041e00c1d40303004a07121903000039003c68070300b038042c41040c041c100040c010380b01000b21401d5885801d82203066440002da441d1901001400402c0e14002c6080522f86045851903040a0340110b80b01d441200003001c05a44000150500c04240440c00d02c0c00c0d4401c1c0184 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 108639343 1250 108638093 108638099
    0x8060409020d14061611031e0d2901020106050f15070503040b0a17150906060409020f03060f0108041a1801050415050a06050f0d031707080a05070f17060406090204 72
    0x2e40e980c4c0c000c84041001d11000701814441c03070b0082043c0c0d41c41c44135800c001c2d0329100102c5080d0b04024403982c0f110041c58024441b06c0099003850168203648980750300c03840712483c040c0808000c20400480118156407603d03000744125100d44500400900040d0750065001c2c64000381c00c07500c0d2042410140050001040c00304024110030300800060000380c2d500303c24171840c50107a58810b8400c3d1000804040d012000940c54105152855806000100b00301e00b41903840342404180d910515640c00f02140000401181745043d200c8007540500a00e042500307454a0760300c40204554029115500c42c10300c0000400c0c08145640398000b09490740001e028500302480c000840a54455919603c2070401e070029a00084502c01c03d01180c8000b480c4140c0340c5048014010300444100c01a401c0102e4021100008008003a07028064007a55844d249140707460b144150071240050030a6003007018844001d01c009500c82c0480d0b403480b41c0da8001b111151a40000500140000c1d403040c1c0490f400480c3c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 108640593 1250 108639343 108639383
    0xc0702060c0d031e0c0f0c020109170105010f08060c120c04050d031806050c03070201110c06120a110412020103020c0a02091003061103010312050304031206090209030c01030c08060409020d 83
    0x1091344a800c031a01c0c140404000d00520555a4501102000890340302400e8200c80c030503054600d406006050080c0f58649440c00c0c3e847d400e1808409039503ea44070700041001ca0001c00c111001070002030041d204900b89101240c403940b080010000c1100700d028045480090844100c4006000043c4074601d03d80417440c020380700003481500c154003a45030300b00015203070340104104e52101a0300b001842c5889401e03401542c1841402a03081190b11812040c0304090315050000c18003102c044180200d00d103411062001074481815080c034188034180000c002481002d2111500b040e8242030250300c803185040c0c60762502c4c080d40c0c0e0207503201c4100b60901903419850400001900c0c080c07001131206100c00d00e8400b0750703448203202c001c00c803400d0b84044008030340c4a2009150001c6c402e06d000e40803040491008400e0f01c410350404140b150b800150940a440c0421032024180000e080500441c014000050b1182900410460080d900c0c2d020f10002c6681ea0092902e88603071202074121504014400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 108641843 1250 108640593 108640601
    0xa0e0d0b06040507020d141317010207052a0103020d0e1c0905030c0603040305071b080102040e0a051311061b06070801080601030503070314040506070506040615030b0c0702060c0d03 80
    0x103a4051454603000c1100304c0c2c0301050004201c81d007616a01c907003110305000c0707101c158000340c1410443c40d481c000104140700400d4000300380c1e4600d8000941c9601d1039081a80c02d160581c4802c5a04103200c080150b803000d20780c120030590700001d00300140c562051110940140442e1005d42035a401608141e03c1d01800524000418a00302d0340c540103403d88070b1051641d12444840c1003580b00c0014030001c1d0000b446071000741500c0d0301c6030920420342200442c40120018050b00001301994001c14103100322040c041640c0d0344540b009600344440c0c1807030794a0b981c0300300800d000900b1140c1d18400310b520700e455030403c4403100d05400c0002c9240c00040c100c21a00c60800761490000600710000020301590000f66007410ba03030700007029615081550f5015544101440c1010800e180305110005460756208040e260103400b0300b01916040c940f80c541401107601004003116041c81c0f207581400881ea52007070582d0300c074241d06081b66a5000500001e0384a0194000203249481414010f15689905404c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 108643093 1250 108641843 108641851
    0x601030b100b03061005190e030d0e0f0d05120708030105133e070609050609011a010c080405041d06060103020910030b0a030c0b0405010207120b010b0a0e0d0b 70
    0x503415040d141e550044103507503140d00c103051a280e01800415484d18107611051410740190030700628120540d0f2102561512103034900700807541e04c50040e001c1782028002d012003048285411420071449800144940d032100c0030003401080c0859400c0c2c20000c0800001e0202640c0302d00454907010b0134a00148280c1c42406400c1c050000351103030340f401038070600441d80c585010440f0040d03a03604070071a201c65002c1e44240f4504208075006103240703442211717000344060341c006c4201140908550804910345030020b00243e080e0b0b0300d02510300e2101d009000940c2c241031802d00e0410840f841500b0030401501031500484e0b40603150407610034000c25503007044154007100e5800c3d1006a5542e00064080740603900305c03d50000708000c408226940f07c0c0e070012404a03030040803020156104e8a8421400e6010380108101a03400682480650707010000e900040484c0740040b0761004056880108599040c80340303100140002c120703042d44030b0060180f0700c050007024081e94600701040c10b100c3c065000c191 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 108644343 1250 108643093 108643103
    0x21010908130603110705030406050d0f0c050903011a0a150203090a06030c08150901210b0f270a061d010207050309010e0117010510020f01090b07020601120b0c0f1605060103 76
    0xc032080340c0e00c04c108064883c69500040030b181001e06d850800d6840d940031b07014408546686111b8080440300920880000300100c0c0d80315515403a01030107141c01c4541c0c08003820b003000b0f860b040340310300e998079031101b0801d03511010707485003001104941c00d900e14000c3d42ca0384e40d8445d99030400800d81c16171691140a01d40c241d039945000c1d0ba00d40c0d2030109544410482c3c03158001140c0001400364904200401c400c0440c44200c42404822541b41c5100e000c00680d0340c0b0988080200600100481111108201c1108210050000d4207844c01d07050b51501c0b020401403c9a0303d41411008254010b4900640c1c941e042c0029591003c1c2031400b20b45a45c042961308e40883c15040c0382940552007400c85401d040c40001300c042d1240d003000b0821146c000c0194034201188110480e00c00e03410300070f0003008521031084c02981118106140081e04054058208158400c000341076500421070320b43c0700c660010b0325604c02c290340c0e00c54a5460031080c4102c5c4841c002c400303540c0e5480002c1250004810341280c1c010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 108645593 1250 108644343 108644351
    0x615030106090e0d0f090b0a050702010e060a0e130b010c0b060a2403060f0506160503130e151c060908040b0301030503090f03033108011401061d21010908130603 71
    0x5e00700f5585c51442d801183d43d500c10a2090b420441c1c0103800511400f0700504150820220000c002005036001c07040800019256541c01e0031a41881200459440031402051040035814000201030611508000c1c065078020030100e01070351500456403000d00b681c1c403500c0000c3c50404041d20584003102001e400000c3c50842c0000d80a8441908a000e80703000030702c054904110001210f407627481070003095038640010054050941c0303428401300004c1204e41116002c6240c07580d01000b15049406415000303900c2901d51a51001c0700f154918550b0f90301200c0051516090b040140c0c0c80c0c0201c0d0450000f6000002c000b0081c44000005082c0b1800c040380c2c13080e00e20a015081c180c40c1c2c001c2c410800d0f13401100700840c070256a0070006d0031600200602d6441d440c0d1381c0d00c4104a00703603a002030071011000d0b65440140043ca9100000c042c0c0311901228a500358400103011071045000100c410960308508414407003030700020340000480e560008119030b00e480a10302d101c81c006080744100d00100707140c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 108646843 1250 108645593 108645617
    0x5010e0d170402100f020705060a030c020c04060608040b07090504050a020903190201050a2a03031401060e0604050105091f110d030501030b0106050310030605010305010204180209030615030106090e0d 88
    0x2503141140c1c0b140c0c0d0b000e0001a1825082c1c08103580e01c0c1400848481035000c3c3c21008281500c0354000f80406040c6550041150404814068101410308080c1405282072a0b4203004458000d101c41c0d800c0342d48000050302a0346c84803c00c480d402e00d10b810040d801410241030101e8021550060f0104810840946035600f2480030098ec1403905018000d02041052044240103805904101c020f0ba95045c4402810b41124000350888000050103e0219986458481d590b500c1c44454501621751400e1050100c101c0a0015030140103912426040200c00505903c103526410000702c40d8414050800030300d4141504040c084142c1281d555419105020808514512074000c60f4101c1c1d4100089100d6a420294110f074150700085c4691815404884000005030252040b02c2c000c500407800141c0340e500702050030b80b0300c1804114104d0307060300500c858ad1a60b179000ca21250802d0400129020714066030340424090186a80580c44440c600700b08604440c8003c100c0176240781c1c80d5503c140d06a08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 108648093 1250 108646843 108646877
    0x10022805030412110a1406011401051615020906032401020d05041a07020a0801060f06110303060f040b0607030302070204110309190c0f1509080c0d0b0c0705010e0d 72
    0x40b00c0c080c00d4525640e031645507850291064041c00c28229054501d0300420b500c40d03100e510b980014030005644043c0042040f0b401d20718030b001c000038092800c180b80000014000301c9815114501a1110b2880500070542034144d60464400000c00351210352240790600410000d01c0030704018107205410402c1c690843d40c404038021603a007103291a118201400d0800030094000050504000c1007410409900580c1d21040d201c80200102d90010424500300048291403030f089520007024802180d40c1075502c104d0101c1a47e5020070140c03413a1044048420000c4d015107444080c46401c00c600003510018181d250b001410752a0007030b6801e00c8651361009001c800d0b44000c590b105242c1d0005040c44040c0381c255007141c5401f90240c0300d0704484a8440180c42418071240e07001425982c00003009107240d68100302070000401c4004041c02d40c1044001c0032131400c0681420062082a28400044c00c0c2030041040d00c1c0c1e51034000d00200030034218180c401c0c0c0d0311b6200072503074808200a500c0c0e60882007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 108649343 1250 108648093 108648097
    0x12050d0306050a03060e010612080408190f031209080d02090901050a030206030f0705071e1a0411060705010f1803200c01030f200301091103090613030210022805 71
    0x2580c003078640f8854034655221000100070404024070300b5529610001151018842c001000d54001c00c407207680c640c0740108051910041c22880300743d204800000d0000300300d008013041003054150403d00f240300b05098200d0f006101402c030081c0b00100c081610881003207143d01130300c1c1208c010b940da00d00d640d884004205082c2030300c0c407000750301c1107041000508420759449040d8024406007081400c02c1516500d40e1541c41e2134a88410b42104480c07503032002d00c1255404010760080d40c1c034480b202030034141ca894110780e1488000b10f001c1c24001039007108112095020080c4c08150503030401280c500a07824603a0014010410350015165640d0303403240c014203a50039100c1400340b02c01008a0081800107501030404000400115556010201501c400c20340100c401e102003d03028940ea036050004440c11107403074011a000c016802d20422640000008000b0380241e1410340d246010707040791908a01d0000464080030096002040e05004650fc1d001403040d141c005c400f220011100b000400c442c24 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 108650593 1250 108649343 108649349
    0xd03090f060908070b070f08030108030306090109020a0c0318050a1403120a020606090c04080d09080105090a05120702040603080c070501120e1005090f1218090103080409020d140112050d0306 84
    0x3d504001810040c3c41d00c40d60040040303a2213213400b101110f20304d450310201c980090b440f01c0c2c10b0f500000104026403406400be140941000f10b011820310513014401071060f81d4501c0001d00303101e0040c2000808003240c40340500142401040c101d2450b44842c1c0003040c002c2d500524501034460004141d40c9115114165000078034294018905e50303030703400704028100c5c001900540078100308000101d5008014410030201000300d884100f80e4619080c0400e003100c6005055044640188601e43c1c005000450796105e40b0a00507030041d224401400020018429580300803d03079000080c88094507103011400c1c5080318005d88503445605010341e20302059440007216035425070000144031541059031750040760003401072350865544000070701403686414a4030031441d00c2c2d007002080c4041c0462500321072405600056841d9030a40d451a9104031041c01a030141c1000103401081c048814511548801c1410080d101d071039156594407011080c640f01d81d50415140c0703001c0c1200000003580030703006403411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 108651843 1250 108650593 108650609
    0x2030c030d0b0402072906011805040b15030906040c050301061505070c3614010e090a1b06082a07020411040905062e0806040b0d03090f0609 62
    0x152240c44078080c001000030440443c2d01c680c4c203000000c0071408540720f1810460004980300400d00000740c074002c2010000300303428104038442e10101d0790084038114040c212081a10040b40d40c1c90010001444118840f559900c06031011040182c0302c80c00040e401d014034020810302e01c1061b20b4005050903140103000711520150880d0b4003086080c4030b80e00502d1030900803154884119140e4a1526045400d0995441c580c07580e80340e501c0480101140c801004a1141d10800c000940507148040c580c005101c1c0e202e10340400000240009401d00500300c9299110031840580013240c2c04801c02c104ac18010f00f40010364560008100740c0c1c2500107100c806420f03045a001300902a480f80c00581d2201c0c6049801c151501c2005001d0b01580e00640b0181c1000b00011a0900d0b19000f840140c42d07480d9030001014510b035428005a10340f20280e50b21040541c41d000080d6543d160100340900724483d00160044860280003080c07560101403070003a40c0c94a01406442503440d1812241441c0c40d000d0007803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 108653093 1250 108651843 108651847
    0x12091401090e07110706030b040f0b030a080703050c060901060e09010b0a0b09180c0d15140f0402070f03020c100c0308010e150603010609030b131515090f0f050702030c03 75
    0x4806102c18071441d520040c0c0703141203040b841c29100c0c000e00308581a031051001c40d03101c80d18500355151500440b0b4500b200c00f1030810200c10244002540c4d0200348802401c04480006d509d0245413103102101c040d1b502c010200d902c00d051090a1038000e0201d40300b0281005d44c0880400c1d0040d40c180908035000324010280711465081c2103c103001a80107000413a40314503104040c4400c07090303440c9082d200301e07400d80900341c0390010410a6801d07030b0200c414140c82d460311310b14288901074115255040424056075101c0b101082c4c000458002d10800700003800e10316406200c1d104140d40051028114241680e0b1101c144146e82003d96400c10400d0008000c184000018401c4032001c4c283e540d070000c4041c0541c00603040200220310141d01c01c0c0c110074001201420f042c014050f80c0d030100c941199400c1441403071400c20343c5a5086c1514814200040240c95268180922550703410607400381007525400c1140a444040700030040c1810010021043d04080c0041c81440c004000c4c3c038170850802010714 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 108654343 1250 108653093 108653099
    0x60702060a0e060c01060905040c0608041505070e06030405060402040e0d050d02030907030c0314120f0a0c0302070905010b0c0f070e060909120d02040611010b06040902160f1209140109 81
    0x5207a030441c890b0030b107800c40c1061000d155045424010140184040b42001030281014100210141c0407a04410181322441091100080c004055029500b00200c80012207466042040b15400280d549840c2d02c01300110500060040204401d0b000b1031084030200000c0208941070f43e00c58100602c410007240d424440200c452030345400440d0b201444406035604a40c403070740c0b05c4507401119082035030040261130340001c00c4c000400085000000c01508141000f0340c07c80480302e140300c0c0d10001400c01c001552003004141c000c01c4510080d00d40c0e108240f200f03603180d01d00030040b0b401c20b24250203030f4481c1d41c07100b003e0507038041881c0c01502c88080e00d040c120383c0c4601c140014801c0241c116100e034401e2401c80c2c01c80803000406072041c41e14121001d41c0d02c3d440d00d030000301541e002c85994400e0b07901d4031604120b655a51002c56085810180000d6221b08400000000ca80d0080304041c0c00902c004519030200145000c1c1c0069031115500c665514075200c0c4071030b4044410100c44140861805a800c1c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 108655593 1250 108654343 108654347
    0x60705070c090f0507270b0c150f070306050f0904030309021c0305030a0e19060e1905030405030d170c03060409081b01051e0117210304030e060702060a 67
    0x800c0158000d9003951016aa1051820110b4804603041c1032016942c50a0203861603000c4002c94014032001656004043c1c0405040c1d8500114404c181c1c0ca0440090051510501403200806802c1c544a03414940d02d0100640c03800c00c9821a100310006c0e150600100d15880c0400c100309030300700094082d03c060342d80d5039401d400521400c84280d80c4030342e440c89101c4218003221207081c07810707100382ea405459042c0ba03801031042c1d900c0e24401c45226009002c0c03102e010030128507403104581e0841000700d1030038100d080d000e040c032281250013180c0251080c089002e018000005108450040d01143ea8012120004842d030307020582d81c040a0741d071000082800a80b90101440c0c101c900244000b0b0300e40240e541d424810340c0310041d4445480a032503a298805007080c442c09a01204540e0381c00d140b0300030300c1c19a03000f82e201400303071081e0000000d4521041890400c6100c50341c3c0c035075a0403c80d0f03451850002034120b401c102c8080f00081d4003400100c58506040341070300c0c05a07502901050505c240c05c030007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 108656843 1250 108655593 108655597
    0x50a020709020c01090b010311010e0a050d02090421020304032001020a030e040209040f0f0e06010602030909150d08070b0c16120309230f06070801050904030210020304140d0908060705 81
    0x3d0a4020364071608042d000c075031444201741c001c5100ea41c2c4051060103a0300094200313961020540d100700c05401c410001902c5180304240310b994115039800c6a955286080d2501403801d188124580303d41519a0040c1600000104180c0b8000d2465180740560030104280e50000404030a0068202e1905000024042c0c003908080c603600402c05410540000c0c049000c80da031614802c40307010707241c100711111101d5900c100304032071005c400038016560400f44007035502d02c40c0c4448980100d00c00360018841c8074420138919541d40000306980040011030500e0441500f01110580c2c0c0081402c000c103030003092007421226400013180001140104545074100ca60880d816108185a103036800e0f4000034a0786207140240e481070a44c080e480a101c1805689001078000d00d94220768803010510a0a0350848011811694115200409541e40d440e0403030400c41c040c038146c49003138004001e21040144058076040300c110500300300c84c0c9400c1200c0c422260010b152040b0309290304001d010588035071003100 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 108658093 1250 108656843 108656857
    0xb0a0f020f030c0c010f05040932040224130b03091903210e0708010e0f03041412030c030a08180312010306020c0a0510020a030c05030c040e040611070501050610050a02070902 77
    0xd141c1e00386507807210400c00340e030000e04000d104e250000340500e010403e40c404600c41c40c00030b10b41c000ac26240640c04942c5a01e81c00034040854140091080f4420502e1401c64038041e1300d030142c10f83c181d80d6841034040c0e69081602c40c800c103405014160380031210048402c08e00a9019604c550319817140004001494803600f034030b9205207880791101c40504208109030f9005040309070000502d2001038900074100104200a560190001c010401c07091040c80c13418480c00343d04445441001d2100480c041c42d51080141d17408040c040410b41d140d1f11900218042d104480780501d0844110317054002a0716480340520060040402c0001030002c503a07180e001d4240d29900f80c00322441c002c0715403203952822407400c0a0200c20742e00000c005010796414040d40c0200105400e0003811418500d1241d20507000b503009000c040a0840006020b1041d141c2103000d0b0981c800c044581c1e500b000b81071007130180c00c0886000c0c1c02164640c881c03455040c0700e60200e032070b440c060358090500c1c40d0500b0f200030083d5225007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 108659343 1250 108658093 108658097
    0x30406050706090204050f010603050c0f0d0f02120c03011d0910150810050108010b040603020d14070e130302071428050301020406171501080705090a0b0a0f020f030c0c010f 76
    0x14543d030010317141c510032140034903002c0040810662505400a044e01d000134070229092000780494850b003550101a078504001d5070307401042000d00140390100034041c15208a242d40c24000611460081320b20055058400c050498142611006070501c2a6001540d4001e040d9000c5c42c0c0c0b40d00d101c60103134001c14841d44052100c490156a03180e02030f15140307800c0040300c2100e9035003004100e0071000b44600d1f0050031007a0f03020700c001451030700080d1061107551806007030b00c490103024021582d0203225100182500c10442082d50501c812420840070002504402501c42c02101140041502381d00b00c20403100107007852060000d02074078541210071214005110f44001d8030104a980d4203002420182015655001c030b500340382030150f0000c140c0584071140c3d8682810018130282d900c40c0074035500440c0340c20115610708103040801c058140a900070200841c02213110034503280d1042c4030701d480541d10b500302e800200c0d0401034140c07648103090540c0406d81c440d1410010950081d0b010708480c81c014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 108660593 1250 108659343 108659351
    0x121e0507180c180501030228020f06010504060806040b0702010615030911030a170706060e07230a0507080a02030d09050c03150c04050907120f05040b010b030f061e0607110a08030309030406050706 86
    0x80c2006030145000002d23003002580100d0f440e03c10290b030403c580c9006107422101485040d1810601546402c4080c0c405420190b08400180029000b50004402003c0380400e9012038518800002c00a0503e001c003180c8104a07010341c12003614000504c0c21000b600001440e665109900500b4100d40c0300b41c02c220f4281d038940400042c40140307100701900c6a255074490b0343e07241d0704041107182e9802011a2102d256a0188042d08100354400b0685040541c000303641c9665840005080c4d02c2c1d4081c1410a913541418480d20004002020441c0480c101090702250040584080740c0d040718023048a00c0c0650581c140820007107031800c02101038111446040408420b094844000180c0e042c4021041c0e0f000e03212014130003040481c0d01710074010308220304414214108407031006914840a85018404c41c400480888140000300c4c81043c0180c0040006640e0b0900b49850190300075002045407052021040021f021400401100c0c4603c0e01c10015500e041c3c20b12900381d40c0c135040f0800c1030703074102d0f65 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 108661843 1250 108660593 108660637
    0x5070b120c03070909021605160317071a0601030603051e01050601020307030c110402090a03060504030806100806040b0f0406181505060d0f0b040c0512060406121e0507180c1805010302 81
    0x3400300142414900c109c406540c0c0c1141014000c10350414112004030b84c040040f2030114082001600b140113264900100d15100e03034004030040c01260b08060110702600990808900d118a4580e407400c98601c001d00c1301d6541d1900680e1240651140075000c58160940d90000504200188030bc0c841e0040006040c00d04040c08a03800ca41c45800c2102d00665420501051540202c0d1090384603074115003d201101240d54001c0248402400f01400781d500c2e00444ca003d0380c3c1d85001001b154078050802c204950b44c5404000d05002100c014807941407074810400440300c044000c6409450010b8410340c80c002010b0f1090f0010301c10881e1404165958880552040c1d5460054420b0b840c0c5030382e00c494460f2082111b5018485010300440c1c85180f07407801c100a0650f000e012980100c0e009030010712405100b0802e00f9070030748150b900501c01d00818001182d56120320b10340b0555091000b00401103045002c03405d8400e085070795406607121a40140c10442580702e6001015580d00c1090b18400c0c52007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 108663093 1250 108661843 108661853
    0xb0f040b180c0f07240504030e040903121a041505150c07031502070303050f0603060a020f1c0e06010909030207050f0102031b03030a0f0902090403030c050705070b120c030709090216 80
    0x1d190202d4110105c50008440b04841300d8014801a28036a410080c500f0725a0303020384010300d030114050049803100200800d25010700c1800700f0210b08050103101d41c94113065000e07614107014076140d02c95842c18040030003041a442e404c9003a200c001d0610b080014040e01c000000381c101881082d520301c2452000720000d0709918001181442c0020056150b04041c034000d020303610014201001d001d1903c0411410ba6000542550082824a40142c1d1250f615508680030f1040544154028101440d00f00001280780d02008003c0c54001c151142642c85603024030607981e42c0a0043c00603486108180060f20b8019920844203505004907450024081406602e43c1c0f0500741083e01034001004000100285014881c0c8592000100700580003039640025100b40700035001504040d602d41c01c2c01c003031501680803240031f01d800c00300305c860569848a41104c01e901c00003090801049402c04101c2404082064a0040e075803912040519410402024000cbd084080e802001d00c9101c404440071031 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 108664343 1250 108663093 108663097
    0x6041404050c060325051b01020310061803020607110306060607030c03200a03171006080103061a0901030503030123010e0f030304090f1d07080604080306040908030702010b0f040b180c0f 82
    0x5e4051b240d0710f880b045102900c8407450325114034006039900400400a03652505070750841540e000381001c929444044110b00d4440b1600d410003504408002105024050400d018601845c0b00300c080701c502d40d480702d0074059140100900140072480a01001000a0080b08003244e14540105e031a050440021845854070b1362540c410303408242141146440e004500300903d42c4160030084444c8800e1400e84001c0110b0300511020306101e43c2e40b01840e0003c2014816040005001030040e10035503160701f8401e86130352080c1701c0c041d40d1852071100b06003200340c200c2c00c4017118001611201451600c00301449801e00d011210389906000402000c00e81c04a98031030485c2040c0c140100003040c008503001d2203041d0300c00340104a03166010030410800c2c90030002d45036900c20303409800d281e1240c840202203005042803d0b0000c003180d10110400c044542e05501084031880d0446000380240c1c4408148001c50300090340c41d540040c152900004080d10ba41c9017160040300741d4142c94a000c500c403507114626 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 108665593 1250 108664343 108664411
    0x509010b030405031e0901030e060106051804021303051f09020904030e0f0910030b0903070c1206200d140601020709090f1209030309080c0a1205010f1406041404050c0603 75
    0xb05d022451040c5540d0610802c5282c0d1461402009154107180014140b170040c0510f9400c2c10304017603801c0855442d2030301502c16101300030080e01c1090740c44c3e03c3d0040c4c6401464110b2400ea0aa094260400e14250b004881c070145c1c01800c699129211500c0403501510714141c06a04092a0014030b0f806486030b2403101d00c944031a00545108a0561800844015014007900c1d044e0b4002d10840f400301d42400e0050b412140d40d0100383c0804015483c011000e06142c108610b4580c0b070000d5881c10305050500142203000ca010000c11401041c08840d400d26241543c90300c0c0140c0c4102d40500008842d81e12aa20305400b03003d034044000d020b95200c0183c40340030280c00b0001140c00004004240c2c2064050b0060201c00c40070345005010440860b81402a510460003003803080220322092010030350201080c10440c000c00d102d000c10148900c41301240540e074090240c1d2524461002a442903400c003406907603c5030180c402003080c0010400b00341c00c00703880708800080004107140341c0d031030288903100c02c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 108666843 1250 108665593 108665647
    0x8131e060b120d0f2c0a080a0803010611030c060f070504050a080c180f1323061006020307080d0b0f0a060309060c0306030506130501021b0a020f06040509010b03040503 74
    0x6a07241c2d1603001001d04454400c803130140080f4100a000990145071103184598808a40c094007529085c001184d80020b84c0c4204002d01400741c11070140171139400194140c80086d198005001c0121820a5032fa1058100c1141d00b40c0120b40070518405005483e160400b0386440c050307081c141c03690b00050542c1507641c03005600d94070171801e4184030b0404a2003d40d4840b9140c250f0341140c90724000c0d071f11003408018081c0d4540080d011a00041080041c01680813a901d6461503841d0964050065910709043e80d1040008001d0340001691a20010407904240d9100c0c0b02c40707060460000419000c0c0c003034840161b03804690140c240e40d0780c4d01c6141c05c0303400824040c3d50121b091161400e2050031108407002d000d0816003004030a1020480000e00c25170001c1208411681059650034101d0080c0608401100c100102c1e140e440d505001c0081c0d141c036401d00803141000c140c800c0c0010460103100701c3c81600e070002ea134400100b003800121009150300038080d4003541d18001e076041c0140902030704c0e0949421 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 108668093 1250 108666843 108666853
    0x50c0d0305090c091905060303070b04030c020f0406060905060304020612040305071403070206031906091805100b151303080a03091203090b1609030503071208131e060b12 75
    0x55840c030308202d10002d0b0901990201400e00b0050480c1d440c05e0b080040c0320441944610108001c0c3c0c4040044803c035a070000c50100705424a4640108461314141050740b10380c8020089490300d1425100c0e2a0827900240c607910f000924001c00d02429400080c800e0303034008418030002502c02d00351080644254840c3c2e5a16a8442c0985441c485021981d5540c0d5502c1d4010705c18034006886803001c0ba9044001c1610381011900f0600380e91024120a4110f154140d08000300300410880084001469a10510903610402081412801103902d082c180c6907108002820480c0100f0707142d0b000301400410381a1041d0400d0300c9449078005a849102020000380d0755120307030414801c00b990510320060741840c05000e40081c07503c2e06035030000003a040c01d0f9400c100034401c04102c0d0140c1007010007940e008064039119080f0742040e000c80d6103124034180200f42e5200008540e98890010300381240d030702000c8552154040601b50801c54000801102c01a039505d42a01071503548648600f444142c01c0014a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 108669343 1250 108668093 108668101
    0x30602120610110709021602030106030c060f18030f0203030f0c0703140109030206060603091516090f0b0d1d030c0a03090f0518070c0803101a030421050c0d0305 71
    0x545103035014460b8041140c10260f44100420109001088030310b144000350300c0790003444021240c0e000c2e80b80000d500d9840c10000104021410110004035a6a900c85100d03840c007120090303400701c002c841721070042c42400340203000061580700300040543c0041c003120308000c5180c4480015500014500002c1e41c0010303010030400c0140318141c0301c051350740c000a100d04c22481d41c020359141000b50415100300008030000340702640400c03010300602c3e8a0340d0084070f5400c041078a0007185014010358000900450000f1030200790480c0e00208641c00341404628001ca00460741c1c0c01080307007003c08090200306000d803905d011b1040029000307102c80400a00b003001c07400d25024140503119804041d0f00648808104036075680c2503480030940418510704011360741c844000301c4114181d0f11004248800c08418040c07800603040f400402d50700442e042c0d01d00c11404268030840703030000302c60003422440002c10305480307401201101c40108810b07092040c28155456125402c0c12905090680080d580d90b00300 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 108670593 1250 108669343 108669349
    0x203070e061003060b1b120a0305040b10030f080a0e09011e090507122007031701090204050d030309020f06031303030510150c15060e0f0601021b0d0302070306021206 73
    0x4402c034100306040c10080103241600b502020f020303281d86440000300200750380f003035100144481e40c003c0040404031551650300d88009801800180c80507604a4403a000250940045110410940703400020010070802039a882e41c03103580c0402007000400014074440321030740d03c600791640d000e060400124150400880b081c1508841a80e010440a40c00c10003031000c41c54000c5658041070729000070119401a025103084c41c05c1c8444a008200300c0800070b90038040c594001821620040440c0310501d15913607903142501a8003c0e80103885e0301034062540c51001901a5020010481c405441c1c00e160240702000540141c204807a6004a00d601070101c0d02015854800e0903802505244007201707490408000f102c8100d54581584103202c4c1740404d94081c40a0305404407019404101d080c4200c1b51682511108450141c5291040c0c1c0c1404001c52030341d40c004180d241c000c7d40e002c5082103001c1c816808000b100d4149000c01e03004c0d406241000300c08240d06000034031412140c031409041500340b900034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 108671843 1250 108670593 108670609
    0x60d090605060915010c022b05070807060914031507030f0b010215070819020304030306050a091e050709030605091501050306040507090507050c0f0c130204030203190503070203070e06 81
    0x60365102d100d003c0b0402c840b01802054100c2c00c1942131a03c68548213180c8045150140020308005407664501d6030029130312030701051401601e1140054034202e50303480b01400d036540d00d03d00894010500e10340050181c0504a400c848411100030200c400c000000e60b0b050003040029a00c80c00002e840b90302c1905110b04078040c107060728000f03100825a1001e0160f90312420400074003420100035522000c42e44412802b1608040903004440c02c41d5a810325240107801400d8900c070301405003d401400045801c200d00c0ba0182080c0c100c540b00c02c2c2007520180300300040400030325020502c502038070b010002c40c0d41407150034850420316000780090103441d9452100d4800582c0302901c00c0d4810b104000000d003010404e002216400382001c0340b20b0712503a000392070790300906145200c0c0d0300c074010651440c01d00002e42c25800c010165013901d004c284020a0005900c642d000c00780d00365014400e1225000070b01003980c4140b80c007950591f420043c00e40e001070308203107041e4807844e000d0440c401842024500409 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 108673093 1250 108671843 108671851
    0x709060e0f0604030b040311060c04030b0c0309030910031820120a0303150b0c010c0f0305150105070f08030c04060906050304120c11090c1b0703050703020915060d090605 75
    0x30751403a0201940c0300042e424811400000e040004810104041500071168542011410f0080c5c400c20300c2c08440e840d94a03000b51005461035000e500104008078807075030032640504a100c001e145032503807480a01c1400103080311a00704065070780c1f192030310000d400c502c3c001840d4030500f081c3d0440c0c1ea0f10300c242d21000e01e851100714071502d01c02c002410445000505a5007159150030007041e00c20602e402d910b189045580045010103000444152408065002003c071940b6034648500840ca083c004508890781204c0e0000d02813051003802e03050b5800345001d04a081d210b1500c04030b04503440da5030308601342c005840c50b00e5a10404a410f00150707400581d101c000d8203081c9402030440c90a502c5010b110310018032000203100000c0b51000c248054090310200d101d82c041c0c029842420200545150769000600c041c2c0d81d10001300c50a603442d8004a51201204e030448010029a0304540800140d80c1c005804008410b2032007007600070f140c5800c0007401c940110800c00064a0205040100a84030700078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 108674343 1250 108673093 108673099
    0xa050402030606070f050c0d12020d0e0f010513081b03100b06030a0b040209030a0503041712030a0c09080d021606030b0d060b060f041518031e0206040e0709060e 71
    0x441040302c1911018280c034041c0740c00039800c841c42c0d159418240d043c40c990748090760f0444100f44800d000c1c8030f0007041d4440841019801ca07a55030000f10f00c2220002401ca010540c0403081555464680d840365010b000000d50094400d0003e540d00d51002d450b2240711000020307042e0a1500680343c618061012203400031003107506005400c240e8000521600c0001c0c05038030110759a0400769446d445560540e47c40c1400507080300e07541d056500b4090754980240c480d000402c42d50385940d12103502c004c5240e181c144222007040e401d40c0c03210540c603000b62403600784402c01c021030707c4070000703080500708640c811030761060300a4882490940d540c040b20b121141c101a0500d810490102e640e5158810500d4809400c10030000b031480643e00051014412110555414880820007089805000c2401140c1e4111078030b82c403003070075071015286c054000d11348009451068005c00712000001200040070308a03100601c00c5207080c2e141e4030381c0e021501d8150390300320000e2500c01080c0b043e107402440200c8805011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 108675593 1250 108674343 108674347
    0x21012061508090f0a020d030302160c030203160e04080d180303061404020a020307060c1803080408010e0f060a05040203190302030a0807030213090b0d05011b020607080f131a0a020403020a050402 86
    0x1803041a40d10020b517003000703004980c22540e090506101f45d058500c0003541400131206c0000604000740e07841c046000c20780c402e008640a020100030041040f008503054840102c0c0d4580c0d9a8603090025041800d01008030394442012106045181108887c8070b80700791400242281040140a100e451300820f46008901c10024084000d4000040d01c0b240c40d480780c0c1c049010011602e080301c4c0012081f88209081c41440e1002c0100820807010340183c0c0d003640001c108000c00a4421640d40b2007a03030308401a500594049070f1000c0c265000180e1050018048514070b40183c00e20550508450b081075005800100b0000b081c01e078026038a82d00524146002d5049c03c4090b2160041140c245c455600d410b41d440d1222440b41c0c0300d5600c0042c589030044020480910041c403080450700044041e10010301420000424aa0080c021030b801074030540041640c83c2d5662034907800d041414507003078890501252020000e0400365401600c2424003a80c0075840d1450b5106101c99201c4540103207201c0c41c01 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 108676843 1250 108675593 108675613
    0x6020601050105041e0e09010608060c1317012702100930210906080c1605030c07141507080901080601110604060605090a090c0302101206150809 64
    0x4007400b9503003910300c0c0000c240703410b2194021711002d0252039800058040781480801c019000306611110803034403a801a01c8441c0d0724001e40340294401d41840346a001020b0b402170141d100e800e4042e80071103006030000a00c100b65003900507040d0401a4480c080812604030314021404c1940b5964252189070400c0100c1c2e60511121101c0324100200b035810440305003440d04070030110700c80151401074000307590b07001c2a14000384000c544150703070b00e80c84013161146c54002000d03407180300140c0c070034a04001014100100c580c031354121040584030a07038003440f085c0319600d051a01400200000d0101c0c1441c80034055144040c00a400d03c0c100356a0381409050010f2004030b43c43c0c1007110341031102440c0004240d40c0d00c100590781c010f0440e4440e851441841c0c20801000002e43c008401d5a100f2200d4044035514170000106460499100600d4040c030042d08000504008000059100b82402c2220342254410580405c9a51542c40a1034000011400120003500144e00e203810048101c06840c202e00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 108678093 1250 108676843 108676847
    0x1401051c0621120e01030b06030901060306060e070e041a0603090705040f0209031b0307030f05160b0703050711060d1401140a031e060f020406020309010e060901022107020405090a0606060206010501 87
    0x8207120f82c081c4255a41100540d0388250b120303400200c0b0040030304e600c0707040c00c0003034600900103804100c440900d011008203052203080400c1c0d22400c0e242d95940c0ca003c0c107a000388005000520303c5025940701404540703080d0f40e40c11002c0d6200f030412a000703018039403511041100340c41e85404801c2d04284100410384031901c1c042405201aa58403002c401c0c0010007034040b07480e04030158400313042245c1140040c402c004010803468123980400f1101c0b40700c5906c0c0c89000b07506104d0a100140030071810800b00c0005406003100200b0104024410788c100b805040700c40040c1c0c2c503010360150981c0c0806006015600c03120011003040242903070861545801c0d83c0e03800c2c403c0d0190404148040000540b080100119608210803001a0190554a036a520310020755aa0882103c1c43d000c59000c0e40c28000b281042c0301901c030038000503401040320744032284800c1094100910b4a4072812000c100c1d100241e11035000c0e9501910015004081c51009410260103c81164105008542010004015076a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 108679343 1250 108678093 108678113
    0x50c04060f092c06011a0a0801060e031e07050a0b2a12120f09010932190212030403120302180a080303060103060b0c06011401051c0621 60
    0x310301d590002a840e0711048083c4004052580164001401500001003a8404a86030b4100c1d0161a11a915100c4185442c10a4064801007200080c90303803004104807440f0310300b44806403902a0540d41c03818075400d0000c0f69040c040a1040455004c402e0400003801c0c108902c400804407580d5a85c00c101c501d0801c02c81d080326201448845038241010429818030070b02504004c1c1d8100c60b80c9598841c18025040380840b0100d0305504404c51480005480310340c180509100c482d0300c440080d42e0f281c0301c0c01d503c00f00d02c1020400b4191030340c00d0022445400310100203410003c2c4000d81d9000d50091540704005090009010201d0a03170828441080020480304485048103241c0c00c02588030100c22403803500d20341c1c4681e10700340d01003040080082e499901000550050300d00b80d0703050011a40f0f42c4100c80782803040e0841803150381e001400401c0407800164660350003800503d402440d0040e55460409801034940fa030610f495518441000410941c1b0b064110f400c1c402e04030250440c4203034950000e03072 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 108680593 1250 108679343 108679349
    0x10080c060f0901090f09050106090801050f180a020402030901150b070c0e07110312061903051f021c0c020d09060203071401060f0810050601021f020a0306051c050c04060f 75
    0x940008140d0342c032203038042c5800b800648640e0030b20160007640c48000720040e00080c030914001c204141e4020600c000103005651180350040342d1510350303032070741c108121a1606c2004115001e000b410b07040d8006070707154002036000382860340010503848040c008035013620b0003c0e404441414000c10a680010380d00b0200754044400704008440c55a0b0b0b04002915280c0590090340080d0100041e05080b1400440388a400750506458621280081c00a40d103070340610f50201504035403028400e92502c1003525044100d84014032005030070a90761140c010900d180381d40e07440c109243c465840c554003980c104070700c45416515103020b56060346441c1001c0c0d12440340750400707072280800d0340d200250080250007400051050784401c500f001c2ea10100107031180300820044118a0421300400d240350b100280508011000000c2401d502c20001c170100000d51002c2c002e1000d141e1180c00015081e43d841480c00501c2c115510408419956468807900f4504018000d502c11440c00340d0901000100d0640e00381030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 108681843 1250 108680593 108680617
    0x10031506170c0c030f0403061406010e03031608070f03021b0103020a050d020307020f0304060504061413120c080a1109100f140105070b010306021309020304080f071a040b10080c06 79
    0x501c650300b4402c00c0c00c510840b00c40101740c0301d00003000410081c042e070002d0f080315141054401c0c00d03219100119015045084010740c180d1017030240d81c0502d1a09900150f80030b1041c0c10440c580221035940003d80d8414280503005a00006c42400c1e2510442188045010003480c0440c586004401d02030024001c08502000080c1d0220026120a000300030004c40c0548600807280c649549500c020701c0e40d403050054400240c09a020300a040c40d801c0151046550038845110886041511150100c2e82d07918003a6001030f084100001c091109000c1c003120b880c020305420694000d49000e00c4182180038060100c91004480b04121a418941d004400d07101e102440703980940d11600102c401b406801d0001e45481114400042000190340c0208161031070030b0718a480413961140f4020407800100c80140025004210000104c0f0303447e401802007901ca0512005c208149264807061100110303001c880583c1078405114022146a41da580207010200082580399001d5020441c180646101210 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 108683093 1250 108681843 108681847
    0x1a011512050c07050105040c0501030f020715050601051605010606080705030f07050306061c020406020c091306021b010f050f0901060305100e07080a111003142410031506170c 77
    0xd07075186030b00d00300d80002d40c1001c001d10090406040c10f1074202c84030301c1400e012904d04200d01c40840410f00030780e4020764000480d801e240d103001000c4000707000010501410031804004801003810340c070000c110154001d0300001011418040080e2030f0310b2000c0c2144060007400e04c20000b4840080c4600781d4803405903d40152213407100c0002c20603a000d07558501d2000701007005992011925a80903004840041d8210313030640070910240310101c4000e0b01c0c09405065000381140104026400602c1d40c0840b03042c06012400c0c50140d110300f1190044140907203184c98505210002080307484164015000d10000c000451070f44d40e0b4541d94503502e001618510b5140e00340351b110240f061040700d0007050030405035001a0040d141908032402070740c0d1800d220301c0140d4410f40c44244644102c511841c1030102902007902c494000d08901000721132181c42c0c03074503a41c010742d0894035241c04540385144a40c5004c41c15003840541000d00c006550000381c104140d07414010b031030082e00c90394a5041003500400603 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 108684343 1250 108683093 108683101
    0x80402100c051002120609060405041208060a0f0e040c0e07121107051f05070504140f0406090c0507051e03270a030f03020c0306250201181a01151205 66
    0x1402c054102d0014070001e440401d504170002810b031966071148074129611111907450f401044101d41f02035401070b0680b111a1000c00c0c44078000e18145400103c000d0021011580d540c410701c1c000c9815800c81e1801049541c180b03c100501804800060312605419803b030780340102c0014480c1031052403052015480b581401d814125050403241c810340c008059400f44c01c542c04290311462000d10000e00618035200000e10401c0c407031419030b41940d4181d034400101060b100204a00700d03030350b1040f80f03900c95521100003c40100074803a00d040a221500c1740364664100342040303400d1020300e47d002c41030f0074410b510070040e100000c41121148201c1032800504021f1044403801c1043c1200300703094108011800110a2050401c1c0c00e03104d130703403082d4201c0d41054002401d043d00d500040e106030489110640c00140e641412080c82805903140c1d00c0005000340f90381e07071508042d000c3d05030f040e201c03440248220181245410813090261044000131000c0600c40440200700a110756a0950855654804a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 108685593 1250 108684343 108684353
    0xd030b04060e010801020306120a020a060f0519030617010504020a03060203040510050415062c0a020c0307080a080c032203090302030a030e0405010609051324060903020301060501080402100c 84
    0x1070081d01c65800c00603060340c0c403103032042d00079401a07804900c610030200c40020b5025001640504845e40505000040303451f052080d03540721010301080040c800c050029140600802c101019030a600d9600451403500d01790312805d222030340300d181a0b40c50b4108070401000d83c0350b061000c8201c0b036100400503a07a1745c50b400c180d4106000040280c440302d040105100a0100411207850303403460040040180c983e403202c1d200da0410381040342c450041c14030021020b03850300c0c0c10b000c2079002150300005071a050000000342c0c116881040d0480300010301141c02e00c04641e1140e1541d5009926042c1c4520310700705034a01e002044240008030000b603901d5040ca03004c040c40348c0d404400441e070250890b080c1202500d0050001c00c14081c0d0180a03518060002808510500c005021280c000e4011000440f0341c03400c45d00079001098400c0c1c8210703401901e030703807860300e45002070b078020400c6035240d07202c080c00e600c101400d4808a034040ca0401103420180005642c5000c840e04951b5000e0a06071000f4a40e4946 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 108686843 1250 108685593 108685601
    0x2030705030a0501061a19030b06160308040b010e06010207030822030308040615060c030e280305011406010509040b0409060617010e0105270c0a03080a0e010309050d030b04 76
    0x4480d8050146034151420480f05400c41c070196508041e0780b1042900c0001070381c203140140c6070138421102e51003440c00110780c040e6100406028001c0d005501d890007401c0800d80014124800304c0c0000e4070201040284500001840e0142400800c4803405040c0080000c0d0344010600000d0040a40003981d400e00c03400c2a80114080648550103406160f5a4100500b041030101c030240c0e074850030300345241d00e8503440c20104400d07074203103449201069445440c220b41c2c601c500d1500c6a00064030407140d1102814280c407412104401901d01c03e545400c6181007400d480342c41c0c8030b242c0152594428010b503603070480203a40b01d031703041510300089051005000801070300000c0340140c04140790003404100c41600c0b160008190403ea00240540304442c001d40b402c8500031151075070201090381c00742c9901c0c04904551182004000304945181c0007000014900a8599000f1107805000003101800a6040701c00c0180402090a0806c0f030803030a600c949454000040c00781c010035999580803065a40c850340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 108688093 1250 108686843 108686849
    0x180c22060905060f0a0503120c0a020603040b1608041106030c120103083004020409050703150204060e0f0a031101030e03220e040f020f0409050303071706010201110f07020307 77
    0x10600c0140e030748040a0000305800e4405a02411504240c60118103243d04004102d400241c01015094040c00320401943c002440d81812800350031805000340c3d403a50040c6008500540300001e0354240301280403a10018228441d05001c01c0c00c08000126180b2100340800e503809031815a601e80e00c0c008100045d10803061848a81d00c130f07000c0003005014600024080740706481c0c04415600050701c006a6a0141c0380810b5a03c214001e4005001420b050b080440030034861011114219281da5807010b0443d0446070408200d940801e041003d26403010785901031101c01c0c0d48041c0801c600d480840d0924005003c00340496420b0400c00f003a1764800d900200300141080c085c1d981b40c8010921000c00c41e2110444550040810341d008100f241c80390b0111405030350701c91070107000382c03d80303a00f8000b06810703400070789030300590311520074020a005000440c880c103a01d59600c0c01a00401d8000205000041d00341811a8500a0f03030030200c201801c2100c002d03140080685488418910010b0f140c035a03d50 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 108689343 1250 108688093 108688159
    0x80409050f09101e020c01060b0a05091906200f030409140a060501090e0c04050a03150f0b03070603090503280327030c020f0a150305180c 61
    0x200005405400180c60190b15080c05660100389a1030070403054134507803060314880000000303582400382515401040c5941a120010541e265030300003564003038000d1010f0708080b40c00000c2542d1185442d0400c0760380c4130070403500700070b0250400d41d0041c21301c000484190800030414040b09410541045000c0f0051100000c0782d80c1d498840f4108000b50103105009080d124511022608185460003680252541030356400d14807454982844541d41001e403c03800d01a508010100d40b0742c50b2895020091802000504c10304c0f1490810395084460188890341d51518001c0c02107216500841c81c001100c1c2e4070315000c11220801d040c000c0c19481544180d481410f00303828104620b9040345101481c50106403000c10940411800c2210703051041c10304003120700498040440040c3c05441b0503400280058043c000b22400080400c041c4582600484004170600c00c80b4407030380b6810b000383c95010751020341080800200004440d0341d200c2d111405071240c20640c80344050000c01103020300701c0401030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 108690593 1250 108689343 108689351
    0x3020304050a0611180a0b07120504080303010f17010522020f060307080405190c2304060305030c01180203070b0901050d3908060f0d0c080312010519060507080409 72
    0x200c00e440d400c40d48817008a0241051901c0c079a100383c548259031034211203218840354600340c804e07502e0514582c3d8001582c0140318042c000400c0c070034000c00185002e00400401a40180e0401e052001303a0302c0b4504280c00103a040c1010020215030f52055100d00c401c508201141c0c2c101580300280c1098403032540150032103004000c200d0402d070b10010090141c1d010f48140e6003a103040c1c0c195032159154020700074000d1f2040d0f4a04101c2c8442401c00c140c03640c0c2c14406000350454100000400f07a40b529071041c0c5940d40302107001c4400c104c2c2071050f800034041d0069200003124141d408280c40700348500c182d00302108045281d0394aa40518203c540e0000540010800e8000039581d820003918000110160071603180e105113282041c00ca01004055669140c1140554406080207505504100c40300c2d0041010b4111350300089050000d00c02402502d809951502c020090054215105034032a80c4103c002030000c40b032690b030b601c03002e409444c114503040303940d1412400c01c006e00c1e11480d484070300c0c81454 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 108691843 1250 108690593 108690611
    0x307080111030a051522182001080f0c1b0d020106080c060a02071701061a0301150302120f0711121c0207020901061211030c0a0f050a0207050906040615090906060513050103020304050a06 82
    0x6000e5480a010b04503032300341c2c0a8203d4034004445201d01200c7e26441e401c10f10001c02c4184c0301c0c45015200c400a082d80407000c0c2d4810401040c107040b01c0750301590142c1c1d12524240400c032800e108079200000c0c1a98118100710000c0390083da100c14901c18a894003d014105207601902034014002811104110801450942d031401d907166009100b181c54400100380a10083c621038000c54004000b01c50744500c958951004240d00c4401c0608440244414040704800c44642480301400700429031844985442111100303101600c0b0610420310014410081d100c01655510061815100c541c03410311140171503506848020100084900d0a83d200801002251010303040100410f84140d40d4030111001d00d0b207800d0722980034145032100541c12801091100d428500045d9500000040000c6907040d0b40d44110483e00307030800410400500b07512014032550301c0034064040100724601e00383d0300d800800080391000015038000c4504041d000400f1a0600c4401c0100072002500718404001c0b441c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 108693093 1250 108691843 108691853
    0x509150c0d020307060f0c05030402120a120201061e060203120a090c15030b0111060c0a050f0d050108061003110f06090a0803041406031e060307080111030a05152218 73
    0x1001801319285e44c01c0510945441210b4007500140261070380713030182584c0381c960070402c0e002e680b4410046035114400c03540c404a9585512081c0c150039640002071020708000340d170501e1044c1d852400e01459640c03c8200440d0384d00100b180c010f003140146000320b58551981c82c101801028202030041040d074200400c00c1e500780100c000d040861501c00700855030070440150b0780648220b0a610607a00308000003100d241001c2d006040008003803410350b01d0f140395044001d58079001134115000e140ea46000600c18007104003c11500404140b604030440340c03840d910b040e1380c15500401c00b0301a403220880a00b00382c0301d01c0c0944d8041400100902c400c2615811100d40d00e4203d889820708a140c02041c588680c1440405c40b4000c41081407510440580081403240f01c501c0a0641505445042c20008071060300b8410071070030156204009940e8201080940d06075900504454548840718041060a41d900c1d20303c2650640154107621051490007051402011015068041c9144616048007080 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 108694343 1250 108693093 108693097
    0x306130b0102190b0a0b031f0b0613090204050f0603221109070e27040f020111030706020913020405010f0e010315060206041232090d0302010c02070905070509150c0d0203 75
    0x86005c1400300828402c1104140c1e480c00c5000080214518031603103c0002d0350150864003a80c2c0018120317a01c1c041400140c403080003c0303944aa04030550100b01480300c0e24001c90b54160080c0c080b81c80c01d05608114107490ba2104040003c0b0080182d103004680c20401024a0741c0d40b14031004104913014504104054901c000d4554214442c0102601c281c0203040c048410078401248031504032101d60b52070743d503174100c0c60700703514140c0c1480b940462001c0040d03070030002010020300c200400360311840c560013401a5600da005e804c9110300c0c01444140700030b903480103c04000101a16005030944e043da00140c1c0100300c00001440340a00c03600d804070302c171a000100d05005911a40d520003214007580c0c0300720361928483e44c5c0c4c004c03200104191140c1c95400d10700c909090b4901c68112524000f22035001680c400d03080e460440240c0d444058806400c0d8040c029417004040c0603005002925159130020440e10400b1070045c030491500c2003007900482d0700c0098803160a20b5004482485000c490065070b65 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 108695593 1250 108694343 108694351
    0x30b060a02010c02160f140d080a02210f070b040611030907140901060807080408130e0109050f010305120a0207050a0e06100905030a080c0c0a1806050103020306130b0102190b 77
    0x5817041800940c00310800422520031a1382c61011070030354506081c03400644800070b0540a61007205841440040b0307122500070b0800f450315400810819401c604042c0b1484424402c40b00012820701c01a8990b40740304003198030865000e48005060f43c0c492030113a00400c887c25a9024401c804010041c90140025002040d620781c83d4050003220348050400c54001d500b4002d00300054480d40204800c103004a034200d41040c42400c00a05001c0c090746140c040c0c041c0e070f5016a8805104c00e00411002ea528411282c000c69400c1040d0702c15810354680607560745d041c400000340382c400041d880300898400c1c0304200c05454000d0a0100c1d003a0741d40c1200d0702914050741c015108000700181d41d40050f00071601041220400390140115420726100c4415581100b0380b4841d0341c0c0600000b0129580d2140c0c042c8000d04610b083c801c01106d4448000f80481e0401d40207581414030400c2802041da84031202e0192440c020000461100d4001c0b004038240014044088500814492542d04101019480600c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 108696843 1250 108695593 108695597
    0x80405040b061603030917070510050108030c0705010806061308010203041406070804030e0a0b0d05010305120a0504031103120d02091305070e0111010b120f0d0302030708010b0a030b060a02010c 85
    0x207034003424000c00c00d162060f0a07800c02c3c010720074568900064040d8205940060185104401c11074071155118910b90014004a46c0e0303400c800c100c8034070030300144030302400360220600450030603108170403490744d806140c002e00d41402850740005913642d481d1001c80c2c417049503100a000d5a699200d40c03803070203508242d600f10b48800c006420b02c0385110700080c0c00b41c42480c05550701d403400d880c2d644055544841608646400059410780410300c0181c1e00020000d280d80d100001945601d5030614504002c0d4036410342c41004002c2103001d240d1a4048240c90503650020600540d449a1100207860000c810060000d04080810100c1140030107900ed4084800d041c0d80040348030034211032034030403030b50708480180204035040c40070744095108020310084194050000501d04440700d00181c4c0003903020442e42010760100c0d801c0c41c01c2c180144030900603540182030550460034440d4010707003203a00501480d20140804a9907501a62080e040310502004c0a441181e648403001d41c0203010b091441c0c1c4800c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 108698093 1250 108696843 108696851
    0x30405010c18060e040b0d051507110309011b0b01080a0b150603010e070c021e031005160507050307020a09020325050f09030f100204150c05100b1c08040504 69
    0x1040d402840c01502802d1515410607180b802c2550030342c1e0010300755014940041e81c0780b06080003a11580c407010a514050001003940d000014051694011300610301d02c10413110049160030207900001765845e14100b402c03c015440c6d44200448181449100043d2022642800000d442840805c035010308a001c0c0b00852016030300d100864040c02c42d00b81000350480c400300010000c14810003c0d043c0c01200b9440e02014480702e60300003884003000c000d04220078500f040b038071402032b240c1085211660f00b8803a0f0148807038608460310960015a00159000340140061042d0802a041c000c4070002540107295401c1141c55122100007500200c449030340b861170349088051401c60039044422981d0050341d69501d130040c90a14010303281c00141d003207a01840340d405000381a403002d00480c2d4404c10300c0e80c0c0c01030b02e8501c3e0036004081040f201c026002440b0340c50320b200001c02d002141020329601e40ca46c002c101600e039080071034002c1030040d803480460300a4042d07982c100a0b0150062080300c9040320240 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 108699343 1250 108698093 108698111
    0x10603111003060501050f03070c050607090518010e010b0903150c07110d050c041509090506070f111002070311030316090504021c0b030a050f0307020a120b1906080106090203040501 80
    0x2d401c44485005031307804558288075410300b520b04040250341c40102d928100307140200d660f03038851a00400307442c1100822001442400305e4207051011114600030000c01d00c4180d45800d40f540026001070042802440c00014080000d0710100140c00c002004110500c45500d0300c00031800d801c0c0c1004004030382501c103070041c40c00b4601d00751131000f0703040c0d800034045c10f100030035841004002d0440c1d8840d28019180c038900040c0700314040c03080c41032250148000d8030b040d10f081c40c0c000f00840e0710800b410091020020f2044410070002a4175031500702c0343d02c030041c1c2d51a07407400e041d01c01d0581989403206900c0f0000c100843c2414800c1c41e10001c8040d0740310100c4c816191740030002a030150b1a005d080710032024000301c02d401c6c100d0304443d80c42c803806400c0da44009034a844d030310700b003403242c9010113082d070f00015401d8210304203c0c021703e004022034200b000c10103185030341e203000c0346c2009408241a02403041d014103420f48280d102c41300905042008128503a5501003540107504115400e0303845510785401c0b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 108700593 1250 108699343 108699347
    0x4030b04020a05010914010305150406090b1201090f080c07030609030f0908030c030a0c0c0e0c040815040312020d15080a0b06030111070305030712020d020304050f2d030702030106031110 82
    0x81d1095400a100c46c25542c0c0c03c2c0c00044001300002000700c0304c21510764803880d4a646451007101d01810031600085151464107050142001032800300700110b038540358a01c070205411990300c0c1d04240c1d0005000381e80f00c0114220034601502034001802207450919001c0801d80c100660800d034400b20745583c9055680c0c0c521094aa018885404009800801c20324052038410300c490052a03118030807402c40240c80d8181004003050859581040010003d81445012001c114000b0b188008401049092601e0f40e40102450b0a1380b140b4070f00b964000c9540120381c9420307004842c00044000c00181c12a80d14084a941c40e42e260b0002c2d034103640042e001c543c41c2d0506018000310450140c068a2612041d9542210154001032040341049001a000d0600d8040d500040440728040304003d40c590821781012410304505580102305a4403208070640f03030000b18030319070004c807032061900001541ca0328201800d501c80c40318003d50651030b100010003000b060401e28015078205485203a0300401340002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 108701843 1250 108700593 108700607
    0x406080a05010503121b0303130c09090201052502090a0b01030e010b0a05011107150203071101180b1b06040f030806010804080315060f0a032f0415110304030b04020a0501 75
    0x6903138064100121041d070384000c0400801018000100e44105140c0c603981c51815600142c608214584482d501c2009002440e44020050702c02e005003040629440d0f4000380c114800c0400e83c02c1c829034050100050200b8400380f010b5055005010680035140c1031309034a0003040302110490100340b4000c819407800030148507140010001500d080001800c00006580c00030803515802c0e403a1107480e07004581240e18401d021032031056a00150303101c4405103015000c26482114131410440541c1c0c61480000700c0f034030114107c944504403030340d41e0b402c0d00070500b142a0054910200500c41d01c000d00041000700c515424805010b0784c0c0703140a0361960401183d002c01d0603180a003010806002042d140b01c0c3c0440241c0340d00400400d0b162510f13042840065180e002010424003003583c44007038500c100d00d801494210141008603c07140c0b45290030044c5914000d501071604240c81d48040f40054034094405e2a191141180072280c03104d9582c80c0214550008441c04c900403050781a0008565004c0c800e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 108703093 1250 108701843 108701849
    0x3081003050a020f1f0801081c2c04090b01050a0f030b0c09030106030c0b071a091911120d0905030c010806011d04021305090c0a020d050a0c05010f020406080a0501 72
    0x4090b00c80e40c0c1e1160200800040c2804800c1d5001c105841410f13203480c01d024007248004010303124244190324202450b414000100d0700581d029550620050142d0340c01000840d60444285103d28480501070119498840c40901d180e005494090190140801507400c42d04903441125035400f6a61503942c0a00400800c2c4001414440540c000c6003050304010040c004444018000091883ea6a01c0742c82d480070302607100e4040e851300000e140b4103001040b14008100ca10414a60301141082c10549961b070401c0e000c0c21a01840c01c021010800c00004902e00c0b01c0b240040004061030204c0c120113440705880484803010a80c44031002890341804103610003d40016120002d480d9549001925103094100407407501c40321aa104200c41d03034642c0b01500d002c01544210811582c208414000da0820250002c490560140b088040300b5500181403140800d1620f0201d40b25400440107441d256000b070f800400f40d5003403038844070070002039034003500440d4a10380c0e540c8029242d1201900c100d0304280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 108704343 1250 108703093 108703103
    0x12020a050a050f06070503091c030201051303020c060a0e0409052a0607080a1209050105150603010305070303030e1006060302030f06090f0403230c0f1c02100c121803081003 76
    0x100f044980380a8028080b402e00038000e40745003007450030008100b041070452060307113081200d81c1807044c55424803410ba40f282c0301d01120511103a482c1c401950702d50041c0780c1d982c4185d90005480755040d229200c03049143d000607209100c3c0c44510f14245440340310717040d008540021039400090882d00000c03800b84004038041c017901d103006074a46070002183d014002c0402840000030b200100c031a0180b00341c8030540d01600002903d400d0210000844d802d0014a003403141c4414801840416404500b52080fa94035007000600b44040c1144d035424510240301c4a1380300e9250180c001504c0342c050300114031800b107245041c0131a642d000208034404205486989803043c60701c0000e0002402403030300850f200300e10920010051048071060261740d2104060611a8101c20164030b4000c108015509010100302108103419441110003035031540f03004025400c9075103030100a802c6500903000445040507080040c414505100840c46008920880c11000640044001a1704240041c1084180d87c0d000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 108705593 1250 108704343 108704359
    0x1902030f1209060d23060a05030109080910141204030e06030405030909060a1e0906050411160218041a1b0a141908070e01020105040b011205100612020a050a05 70
    0x110307080c00200e0f00414401c0c120380c0e07680c01c1429200c00d41c00c0b86400c20321740d910620f44040c1c0703401001e120021809611581c0241e04080c00800014205003e071986401c040c0c442d03064050070301204440381a041e02044651010000c1c1c50101500300c20911071149000e0344030541c4d5204090240306041c802100d0161154005111040a5140006103d80c00050003018040e145458406c200d84c00700d006101c0400e031101116040000034101d02aa0b4001c100449040208070320100c405003ca1103408030031000d103440310300c0c05400c564030010141600300c2c84000340c05036460a8513040000c4980f07000d10000740100c1a0009104a00105d040100d40c100c02c0452401c26451b0441501c5402900d26007d0300e1403000c1c440500740c0c121281007241208882e0740e41c06090b04101c0307805821406c2d80802541107906100030000814089e40e07283d41141c011103c80004032a941c1401402c5c1100980252911400d0200020f150030014002c041c00d00d0003244d0240441c1e948500b045141030ba107104042d004210 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 108706843 1250 108705593 108705607
    0x5010c02070e0a0222080c010e0301090c1206020408010c030504020f0f061803030f0f040501140f0301050f011106250201051005090705070c08011514030c19081902030f12 75
    0x43c1c0d0054021140c0244810005225800302d00c0c90345000da8012034450b0b40f2100306007560350382c0000c0d01d0070a0314058008000d134a00c03a480c0e0034844a80f03409008030420700902c3c0013041001ea40e040780c005014000080242c00700f1520010040c00f0241c1d401d922400d0b007040d41d4491481e115200d00f041a0300200450300c1c0c02c0100c080315080100c0044401d60500003403001c041c0152094000b0401c03070f07404960050303031103040c5400582041d800200307801070303a0400d015014441405200300c90645108031014506050440c004a680f030842d04928543c0c1d0050000340304e96001c101c01c001816141003d9066040540c45000301e080743c0f030480341000d00100042e000c20075800c01d03900b0340360880c1d9585011441c00d1482c1c3c4075041c4080e40c0364080d0020780e6503094581401c3c400c1803040c202900603105010305520004000907500d607140a9510b20075040c10b13141c20b00b4503c004602070004c00d41d4905564194000c558a0744180c650030000b64068000c184400f107010701c0105140d010009407040460402341 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 108708093 1250 108706843 108706861
    0xf120a06050909060708070807022119050a02070e28090302060c070c031707080a02070f0f0308180609030a03020a15140106050c101e240e19061205010c02070e 70
    0x230140010040d400349000070070000c2d01e5107044002c0c01d41100c81082ea56074114000500b18255442c2c03010800c541803050f0900203601181c003c2c1100c01c004005100e0381c071031204030030303e40c840100da04009155800f0442008602500481000b074066026212240e46a030410041486090310044c2154190502070002030f640d000c66a0005106020150810303680790f40b00031980d444139401307c02503441041c0400000f0004052840648410109d400400389566122441c0740600da030f07802080c0210419541c40d98607140152a00088014119600385013281400303074440929100130340c2d0300b40d2042d071000300b0f0b00344c18003400140709640104d8040300d80c43d060080704e040d000044c141c038140c01070b801c0060990040b80104c0004000700340400e00e070f182258101004540c103000700521035981c50036414024a8940c0ca03400d080b542c1000d5003010701c1d520400c60501010304452514002c074904400400d07140c1905c00303100b0f00c2b00d2003000204800e85040800b682d0700e034444d110302c0c101c2c0a244400154480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 108709343 1250 108708093 108708107
    0x1050712050a0e010914060c0906180409060f0204050a050904050d230d1a100203030a0c090803070c051201090c031104090b07120c091a0f120a0605090906070807 71
    0x25078020b000903811007443c24907081d41c0901d402603840c0f40c070700041095000d00900207141c014582000c042d26141d480c00101750140651000b900551030010031070405900e654000380885c0350b2241c010000c051800b028680250400e0042c02c0c09010700f2200807610381010715495000c2e5400500508900f0f1000c4400c9075004032944085001040d088da503200c0e5074030b00c0e1000e011503070f0380c0010201d00740c80400100301410118a00c2c02c1c0c880c0c0c09107a45180d1958002c030443c3d07040409aa404107040c140c002c4140c81c00b0a16903ca070007207200001d070840c24050080300d02c2c1c2c1a240d0031900c0d0a2003414180c00c00d03003602d107045405042d801c0100804c100150450380e5030403403440050008254901151604020030608a640704086214146041d12800300740c441d5455a00c0c2c54102018100d041550103034030030590184050034020f0001e0a40310b62031074401940d010920110310340b802e918000d1b40001c05440584159401505201c020618031040425594410840e03543c85d40807030369841208407645 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 108710593 1250 108709343 108709351
    0x702031005061309120318020a0611030c030301030c14030a03050f0a120207031e0f02150406060b0a0f031503082a01020408010b0901090903051c180f030207080105071205 75
    0x101c41204060441e9015002c0e51078a1350003280d1036500c407011100c000c4d0960702d000d0460703004144101c20210059a4110b955001d4600034581000001040070300e2030700d184100401080c0d2480f02000000070421327803400c460141c0740e03100c6507180403402000c20b0569070380da001c10080120342c041c048580104900409010030401a05d005015106800c2d090b0080380c0c842001900054030500041304e03007240d2001110011007152900c09284c0d00030103030081d00c6424017841c041d03003042503101007030900120303401c4280a4180d121440c0e07075600300d400c00a070a40710307102028000300b410410940d4045a01100c130008513038110002a203020002c40d54262000400541d00c0044500102b900c5c048030024800340010b8036459000044480040c000c00c01e803a0816840700d40d6042c1400c45020000c1c0d4007034184c5040c5014803045003200c0880c20112000b41c560441070360488816944424140501110721a846a0080d002d480d0b0450302ca0507414242c2e031013101c2041c0410a0805c3c4205450320680c8090b41c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 108711843 1250 108710593 108710599
    0x901050a0e06010519020a020f064012140a0c050402130e0a0f15050a030b0a0e010c050301051f05041719030503060a090c0c0f020f0a03121202070203100506 69
    0x10300401d070826425006200c80b6200016031102c082d55045040a005809c261035088820f641001e008900a441400d0b0700d4040a204c030b4854141107044c1c19280c41c018407141420214a48074a45442c207200c4160b103c81c4003034642c01101030401a1481002c01c001420580103440c2e29241d6017040c0500c0080d5226031803d600d0344101074400608150700501032401000c106c030006c20407201c40c900e05d00544600e151464061019540304102c269035088008040300e0340b1003a01c00072540c88803035080084c150b1030561034641d4200602010100e0b80040114181c2d1002c450422224041c00c99031180508500355101c003003a0704000c10b00080b0100440415081c80d030204880c450181f001180460074540c0384118017103540801444614504840c0301c0f000f0700090722040010010344140203001d00001c49025040340f503965001425074035801d254202d10304000d8101c0c082e681c1d4070300d444c00c2c8036000000b00d080010440110400540091300031940d113150000c0040481507466002c810007071001600540c1c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 108713093 1250 108711843 108711847
    0x306040b1f0b090a0603060509010e040f08040b0301060f03021603050309070b0d020711150406120f021210170a1403160602040305010f05012403060b0d1a0901050a0e060105 76
    0x21110080703540006000708484042d1140b103400e09010380c0c40196007249040c5420940c003882280c40d81d044090441d0700c0c242680301e25413580d0070010303084415120058102ca00004010513861000170045040341c01c0ba6035001c00b66821800202c00b01c1c000e250312890400c0e08507000c00d000c00d210b500995000710b0080b040d0741c0340640e944800709081c0c0c080001c600c000ca40214120040c0f00c1444450605c10200781c444003078448024100845038880d602032034041c03000800480d98018a01c1e84215002d42100c0c100715545c550802c03030071007801c9080b59240c00009070b200010440c1c41d02c1e40700640c0000014402041304451542e2189030a80e8440c0070146203100278401603034000000c10185584074020040140e0340c90860030020f0940e1403d81f00d4251071030414004008a121a56440040350812220044004048181100900403950140140d5038010a0b41e20b00c41c030840c1d008e00104040d0898a0911642800c188003408009200e0140d11005d0454204481502101c106902c0310301494424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 108714343 1250 108713093 108713131
    0x90d110f0a0f0b1003030f050f120106030f0f0e03092101060303091701050f0a09020a030512040e01050f030c102d021b060a0f120203150a0902090306040b 68
    0x62500e07000c540e00352035081c8005182d60910028222450700b122020043d0121542180c40c05400311101c4500e0104000001488090005040d0180d81c90300c0204040115103513525070000f40600310100609075010700d0700c0c0281508220b244a83d00b41d2420368006542815603200400a21154148000c094107a5950850040040038410b6101079440390311185401c40c10a41850518004c44070b0800c0560301d000103205e00d85002260169202d902c1d4038004c01d5030001807002c1801441030791302c01001c0380316401da0802902098809441031b55030069420f14a60b82c3c4500b000647c0c0118810542c040d00100030300043d41c2801441c0e0b804600542c1003a042c510702c000b06c07880740719500044212504820305100040c0a030b05100101e020000510b403011410016000185603109500340807051000000c0380c00412801858441034800460004544034941049411805c0001c4501c039031290590750000300c1c802c071091080d28900c0320f028000304171556440c2d941ca804c0c110302410300c801e281e0011800d0707 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 108715593 1250 108714343 108714373
    0xd020103020f0d1b08011d0702010221090d080606030103060b0a1d040312090210050c010e010203010f051009030c180f091b0522050604020702030d050403031403090d11 74
    0x400c3c41081c072035400a0803034060144802040c0040031100d04009915004100382d084280c4402c0800c0c43d91806680c1c01d4a81c1d01040e4028880d8400344c80320300c46402c40c00030100c0c80090020388500340309410b13502d034480110b40480da0408100c400d184d12640510050010030101d6010b40c0070064064003140b07407161110b962407086d52540c0242c02c450484442000205a03002c0c22111f40c0300c004400503c83d400c02d6038006042000c94901d400100000481d056040000940000c524482075000855507961180e054041c0100d190050318018005041d00d4804580f0580e10390003140d400c440300054141c240300c039181c0a07610f85001500403c0d103598002030303491024420441e00c544241141030ae42820818140c0f441911a0300c21881017500076410354011825000c48000629501e1000407103569903000900280100170001e9018800ca001710691640c200f001082624001c1c2c0300c980504400b44030620f582c0c403085500403041d03006440c1e4649100d021322420b01040345e10806880000d001c130454 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 108716843 1250 108715593 108715597
    0xd02030a0b1f0303020619060f0305060a110909010b070807060c0c060605030d1d0409080309070603050c0a05090f0d140709110f0a0818010c110d090e01050d020103020f 74
    0x109a0300c0c0020201030146a80c010b507a001400759045280c0c44030a8a10713103029494400003000321114a286801c11441e14000e80e008030007901d101d400d5400e0317103900c0f070038074683e20007084810b910818a000502c2094074440e100f41c41101000400f46c1f0190707820584c0301d50780394100d041c084640c80c00520500c0b000840b54010244803425607030f603080c414001c9052130401d40b402c550185019820107040114440e600c411105681c01043c1509640c00d254000410000c0c00503032800341c64460040240002c410300414103004840f0540d03000d2040d40c840c0c5001d50034a2085401d080003090381001420964140300030608210000149148915011503d41d6449806060000780b4641c010341c80c01d11120916100b651003012003e0495400c00c3d4400d80e0110b035a119000c40e400030721564000142c00c02a41e1131003ea249090381000f40405a60000003601c000440003842d5403901030007440f5020b40f0701c105036400071122000b40401c8564a003d003401005d1440e4070060381055000c00089860004040c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 108718093 1250 108716843 108716863
    0x50c04050f1f26240a02070f120309051005010807050d06021b0c010210090c052b0f0309060c02010807110309030f0705031504110f06090409110108070507200d0203 72
    0xc40440032090681081c07007811034a0444410781e130384400500c0300160320783d0b4400c40c042d5006030784400b41c0c1040700b105402c40f10018400888280f182c04c400e07616030805942103200d501100c1146100029100076150240100b60041e07101400c00c00c824a0001c860784880fa00501005291540401c4820002103081d02c2084182e417181541c9001035030304125541d01c0b8040340300b00704a54011540c1d80418002c851180c503215010000302034540020388040303a9034103150f6007807400c140c450b5860300c1855040302e843c05801041c04040c0c0000d180340514110b0001c035605a49085040d500c1c08416104a490038080070007512041c0024001034604200d0380f500e00c00700360000e18029180804052801801d82d101c0c4028402d500140000200c440b840e250307041e0003c4490f40341840c0f051020941500403008100e03485070401c612003003032000c0703200e0040e80d00b0020b90303c507030003603490880136521440b906800801455645550240ca0185034648182c00040200410f03200302154000070b144c01d041e10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 108719343 1250 108718093 108718139
    0x20d0b040f0312180f0c0e070909050703050903030a0507031b02100b0301020715050403050f040306020a0e06090d02010309021c08030703360f060c030603050c04050f1f 74
    0xa81428181504241004808800360400740019000c000d01a4074204130020010514400006440108142c0b10040c0000c1e010011090f512460301000080600c5424403030716903400d20341000316012602c64040c191140c80418011451a25540341000041030f00070301c0b010415503920043c1c0031508858000d90030840c1c40d68005d100c1c3c030030589d00700400c80f000e40428130312036841045100d0024440014269000101604c00151555281010349541c412840f0307496140b24009804003c002c0d00b0360103800302024a80d25075148a0340c2a0503c1400d104211200e9401902c2d18080c100561003600701d484154406007462248007044100b18541012215003100c4524010042102c4960706210b1500004403010010701c002584600e401540b0841d40e6100c035031034242a008905001c1c4280b001c0c0307000366010384100801c21084400800a0143e0b0000300d0320750140001e0000245418000c09014a100c58001e114030348400304c1c414100300046030007803103c5161020014045040c0004000410111 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 108720593 1250 108719343 108719363
    0x8010e0601080a0203150405010b060d0f0b0301141303030b0d06060515190f18030c0515030405030d0203070c05101b03020a090605160203010203160908030309030d09020d0b04 77
    0x2408986003000016000020590303c003100102c00b583d00000d09132001018030304002090f403601d0a0103409041701d5800140c114500140d29441c22a8544c40030f1061034046400704120054072040509a80003450101d0401d0500000311719680103c6030668601c40c80380c2400254000c8080105040e20b10110064410f203940d1401000385082003504d052500d40080d840501c3e004410160750507001c80090b0b000100004285001503007401113010070409040f500402c280d09030340b07240403620b400309401280e01864000303003158048259101902d00882d8004080c608250b54456103030002e4000801200070040b240c0110300204c2e006000003c3c0c049401c240205030320b400a58100c4090008240e0801050320400549a20f03d511a90000030f803030581c0760030765403a1400a80103035800e01f01c0b20007030342c594030000600c00703885c03100c1980d40501d0350552681d114080d5281070807034a03800100e80b03000c0d007604100300d106001c1660398000840c05200810f1454a510a5103c0360ba00600c1101d04803959552 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 108721843 1250 108720593 108720611
    0x2040c0c1514010e04120309020103110c07080115030507090c091a03070806100503040b0405030906040b03060907050903070603020310150f0206090c01020c12030f0f030a0609060609030b040c0f0801 87
    0xd03200c6898050302c0c045185640318241a55401c0b14500c1406c03d0f081007503902c0940400f16071094100400b801041e04010791a420005041900c4100b580b0030b11159620300b08107031840018120b290000c0300c0d0814090004246414590707401347c40349602c17000420a5610011502025501041d40d07800b0f01a0080d6441f4a031400c40034142d03000c082c01092150101101128104d540402100d030300030f45c8503070400f4090b2200d04e016440c40c02070300031080e449403012901250300f0074954095803007103004590b051078070784031040c0c00e03105481111041c0340c0540003c5001d21080d406074005641007420304007104512039071410030b0181108843c58460000d1100515140e44650400c0980e41100c81d00000e81a41070100c5c0020b5a5402d075001080d005411080000c880b103001842034030340d80c00007040c1c400e54424052445003010307802240d09101d2a480c0c4440030880101c0b42c4a2113061360380d5a00c03624542c40c215102c00c54100e40040c01200c0d100c07460200031504000c6102c00f08010000f80e0000f00c2c600c00c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 108723093 1250 108721843 108721871
    0x30506011b060e0d05070b010603020f04050d031101110c070e010509011e03050d050405040b0405010510110a120c050601080604031211070f060605040f0504020303070807020307080703080703170702060402040c0c15 94
    0x81f06900080405005000310507801404800315070865208a568103420301c0c05181c19692964104070004d0294645282010700400410042c20402d080000b40c44882e41c848800003461442805481d401c40c04003001401141c14620f003000d010290105040310091750f0390703513103842d1131401c2291038009a00460104a603040500034051008400c0710240015818070f00462003044200311072504000500310040c40c050340901c1007540d40c6400074441c901101e2101c02c060700007100508203c0d4180700f01e00c00018108004912036000c4d5034140c0d10005040c1c00040d20202501c030380f070b180c0c1800403010071400f0300048208800c1e030a0300b449081c010075600d2501c8104400c032102040d0217640c15040804100041c0c0d404030446111540c07000300540ca0f41a2400803a242030b1075500062424411040301200f88114040a444143d20960b80c1e02041034080c4001c0c0c008001c252112805a409080070800603e0305030008090808145880d111040c0f0a0b154030b14451000301e001c0e0100c0382d4406008030480 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 108724343 1250 108723093 108723113
    0x1021c12050a09030e152802060106081302010804020f0402030405010b0306060609011e0e0303040602010615030902421e090618060417010f0c030506011b060e0d0507 73
    0x4040e00008000744101c03030301c0150803034031a0405241b00d07400400150307000030400402c4e00c507000d8901e40c51072801c100581c07055005441c8102010b001d0702c690000014110302c14541644140c94100c1da0300f10030354441e0f00640d40c010000d0b0040360b000185540310025074840780b0146100754000c00004c50300210050a2504081e4003924450003030400b0050f039801a41c200c100d11025048001455000070318200d01141c500404143c03983e4103000000380041c02990540240d0103851000c2d140014510842c0410b80c206d0304186030080d048aa0013032500d580d40c5a03201c0c40300e415400c18514207034519820620001d404a481d800c0c0240300000b29032442810010040700034201048035107a46000103500000300c1138003440904a420300c11a0a0220207a2134500039140200103088088542d10320780c4140300d01070410000203190241c603003080c0c8014a882400b40f940101010384031243c21000d000c00394064220310728000d452054840e4016840100100401c840760146555000d894204500d1314000300 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 108725593 1250 108724343 108724351
    0x32b0e0307051005030901020903070305060403031521030210020409060e06062d070605010306060302040b030604110d1e0807150e0607030e24010f08061306020901021c1205 76
    0x340e10404040c801c54a691440706805a03c1c2e08115882c0e9903040c0030079000e44980c1e401540c1500807200700200700b00d00003598901480c40f90314240304c050200c0b00d4505034041a807080380e5900500800e1540d038261b101050004e0720703021380305403500b041c5c040211030146d07405640300540d00381d40ca4008000d0220401c480d1500244100c40451515450340700003a518501c1c1440b6401a5400c40507801c6860700e00c0e812180019072110040c002c940c0c2d00d0400300002c00c803610040e40603d0078801600840c1c070700030a040e8403441e40410003001c1c860b41752052103007040c10040e0403211420410a640310000c40c000c8010b241d10320070fa41d00c55032448103140103101003181e5005407050358108205800e010402051080c1d10000519001a1525482d12900c1c50000151903808079540c0103480d28000000d0008001d060f1031086904c03001d020fa070341840c181d85a400300c9152040b03022103115100001d1107074005000100301441100c1d11403603141c0044500300900319070b00f000304a15401031000e444107800cc550344 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 108726843 1250 108725593 108725599
    0x40803101d01090b0118090f0b060c0703030305154c140403140a0303150b07150b130c0206150310050c040f1701060f0f03060902032b0e 60
    0x1c0701d0601428098492041c092891199107030b8000600f145d104291804030506006144400160f40d6058200240144005550744074104400c0d403110b17007014000c40e00081d040c3d90003031082c3e52035504d0480c000c1c0b0740903080411881c1010031444c0d6903500c2e603440307190441c0d0746001c0103058000402e0030b4001540d42218410004107050b01d109111007481c14034400c040a506043d104085000c0b91440284540d0b01b000b880186c0500c0740c00c40310140054546c040922948007080b203080415a8102040c140c3d04c144026400b0400880c0c0015801034201b07502600180b0380800d0441c00440061103c640891001e0217490b079400071250482d50401000303800807251000e8613a8109400c01090301d858007850110748090301c504c04101c95888110031203006100b00561556056115104880310200b03c2e082d1012660070b2240100e100d00c000e09a08044440d038080700111036107542c4d54100500790940b4140e80c117014003088102480305e640c0800440e10114040032001c0000028003602303443c00d190250340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 108728093 1250 108726843 108726869
    0x50103050307030c020103020d02030a14010b03160513050a08060f0a02070206220509090a03090b090a0515190309050f070e061903021c0b070c031b03020a0b04080310 73
    0x865004001c0342e100980625040304110132030b00060740070380304803a00328100ea031000040246828055100f0b80314080f03508860740003a40d071131040001501040d42d100c209120300d00450b03428240200c000f0300b243d000441d490603025640d4400640400786540c00380503160080000c1001020055940e0b03075001c28040011814050301d9004654180540d01c0312100b00c50800c24145003c8070142800700040000a040d40f84a2070030318203881c0c5581680c5002c90128031180030220390400700e502555031804014000c03003100c624020070480c24000032400581054010087e414041e5804400302c24030010070b45010840603050f10b4124030b09204116544103540180c4401d12990440302c0000380c1015080b1940c428000880f00024050349050344000c1d8486c882c810185200c0d1b4048107500003840c040c00c032641c516a600d070004d8514a04014004000038038031550320406060107507500b07035680c0c040d01c1200c40545160340d80103c030140550302038130100408010004210440b103135104c060610300c16440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 108729343 1250 108728093 108728099
    0x60c050c0f032104060213080715020c0f0105091302030a0b0f030303070e0f040b030f0a030906090e0408071109090715090b04030b06151b0714030d21020f1801030501 73
    0x115016035400b080003040d2003c1c0300402c0500501d601694458045840d80f079603910340d030b2000725a9880c5184240e08010408155030000361707002050004000d80050182500c6100d21001180c065101516071039018800d0303040350307020549034405580300f0307a80c01800140c900c038248100941041c10740d84851280e40300b00100f00f172840e4480c0c01d901c0001c40c1912031010030000300c5d0008002d401e8000c1d0f030981511845c0c410000e55400042c41104150007034176100c009a480d6042112070701041e0160b8808bc41c2138001180004051100800559000c2c0c10018900d001d0040002c00705482a0380118032a44519000d20102a2075400c1d030806032002d05042c20490718000d111000c50146100c0901001d945e40c00151325911070100100e00c290003800900ea4442c1d000c1d802101d02040d141c4054058401c11038040b03048040300e1200307185c42c2402001400c1507020803504442100b8203146d55481c0c80a01c0d80d210500340f0060014111042d4544035154480b102008040801840200390b54105030a003c010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 108730593 1250 108729343 108729367
    0x7080105041a0405090705030a0b0103110d0308041113110307030501090203090a03110c030d0c060b150702090a0902100908010e0c0109060804030302040e13060506010f0e041503060c050c0f03 84
    0x1050512042d0741c0801d05030788842451b401c00026078882e54140c0107010420040211079912141642d20a80c01408600b02100921048815001004000c6900d040101d00800c4812001401160004000c00c485d071a101e40500300ba07a07a2203c03050340501c400301c1030000060b00360180741e014140d00807045041d468003582c1c05540b004460005414480e0302003003c5042a81030201270400480541204e004800401004103c10014503050315174901e030900401c2245880f0040811211400c6221414040300b602000103103800545500a896551805034006844481d10400c1481c03c43d12843c810501d481d5101d800c0d608000d1544c107440d00f01c4104003a4980c0c01138440c000390b032080d1415041a954a1605a0003882030347c00480c1071041000030490420300300124280c10510500d0140101e41304c0c08010f60b0001c1c444034040d0049038022410443d2418140d0180196a048800080b86c4695a4640d0012640c200b000080020000a8003806929013001407080c080200d0004510340201c100007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 108731843 1250 108730593 108730631
    0x316030902100f03020712080712050108030d020903010b0d031812080406180b04030501060f06020606181504050906040b1006080a02090109081c0201150308121f06080708010504 78
    0x41c07209022a11940f10340052007641590305c442d91141d00002200307a80d10001d8000841180e4000000e14024090041811680503080c101d60440009600f05001c00003668041d400c103000040e010b6694144884c43c940d41e000c4808076040c040d480d038003500441e50204e448000c000e9000701c610052400704201c00200650100c070201c561324134210200c042c030b04210140c0d44106a01080c00c9110201b03004c81800419881749084071030a83c03480e07070180e50b02e070310503619440e0403039155500001c800403442c2c49050100707035a5401901c520001031420052070010341162803e9499801c1c40d80000d00300703c108008040255000a02e02c0012480c4c3c1340390550051600e0b0340100b9461b81542c0100307180f00076902510345036001c0d0140074103a80c100141c1d051980c007002c1d102500380c0d006608005e955010302e02c030340450200703a0303411081243c90718a4025040d4080140076060f4600c40e0380260301d038a01b00700c65400030340203801c070741d5500750b1b880c02d00c410000c08840040e002184158681410403001b2041500 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 108733093 1250 108731843 108731869
    0x403020f0301020c120d050a0509030a0e04020d060b091503060306190b060a0201020c070e1314100e030c0f15041b0509070201060602190b070503040c090207080316030902 75
    0x294001640303035410100e4064001c2850400080c03141c0e5031000b20480e0240c02030a24241c107400200215a03641041006907207040e500c81d8041d4008000000d645482200b0141184030090000341c68a000d04c04a84101c03181903203c00010343c80400c4a94452400c0d246034405800c3d40e010160542c100400085e4607241c0141c0440603507240400c00c0082c0303183c03a41092500020041445448061880b000b1f80070354083c03a00d100302405541c5e0081403e0303014280860080003611003040f80403686513107440c1d590204072071583d120f120300e80c0c0c40b5031a0b128034000e01003050003202c00746407100b41710700485190403a054181c5031540c00218200d0b01d2807605030a4298020381007503194120f03204102001489804540040b41c02c50660810000f182d0340540002d0100c4074140d0031a0161452100d5429003040300c140c00070003404225021074030040c800c0c0b02071604075001d2111800300f0b6075a00111000c9130b100c4003044850361401301c20071640c0481c1800a041d80b1446040034040002d0990015410002e03040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 108734343 1250 108733093 108733099
    0x906080f0f030a181211090615190e0904050a03140324130e01020408160b1b0f0a0506040b0a0b21031c14070203040e010e060d050a0f030e06090303040302 68
    0x84001d603072004090703140d60010030360174105d41c0f14071400b4104002e101c1e9041d030038140100302c92400300391503061001c186442c0308441c0405030f04047d030a0340c521200242d9684c0083c1040310f50a9503140c2c55807240e14030f90050388540002c4ca6419004d1401406520110380e161034020307003d00c10000e81c1c1c20403500c5418045400744003000041c5222000031040440e0030450f402103868a0000742c4076000560040081d101c024040300d02580c0303903800410700e82516016050002c001881107a0304c0c02070815242600880d40010b407028002c210380b8440c5884110340c0c003070b12036a101ca4240814017004140c01a04007420a4051141c6401e100c0441d004008040b0613111000c140710520207409014015036080c1507400c508030380010801c00ca40c0d0040d043d00c040003031105404001060b00540000126411143d41c1d804401c283c3e80707404031844500d103005100e581c101c888414000c000031400c0c45130207806071003440019010700761400c0082005621601c99030082000300813054241d9000803d440c01c40e6811 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 108735593 1250 108734343 108734357
    0x303070b13141908091813060e0a0305180a03050d03020316110c0f010207180506041d100e030706061706070504061710050303070b07030b0109030201091814010906080f0f030a 77
    0x2041c045040c101811b180303012403000002c1480024200f0781400c0c0700c041e005082c2489814501180c403920b4912a24009010a02c10441c05005800701242002085402000900116600e483e1141000502003c5c1e0001135400000c000d10b100c01d403440004180300c1c07442c20010245e8254041c5980345c05071101e040c46008000780305445030703208100c0040507103611501030050460711036a44001d48019148503110342e0074082854281c112812a12069a030500c004282e10040000580001c0007845129502400100f0121000c82e049008100041040c00b2903188088408a046402c01e80040c05003010803004100400c00150302c001140c820000e10708910f400390303d03019003095011010354001500343c00042901810b000008020324450005a14203000c820b1803100115222102d0b0700000340070805010b41030182584c0ba907100b602c1c03c52030140002e103001c0d940384000c40c640c5099000c1d0342c0840d02d5081c00d10000301d080c0001032191140c080148144004103244135240d000fa035003207008200340 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 108736843 1250 108735593 108735607
    0x609050918010b0307080705090112020612040c0302060a0507050c012f010204150e0a061106041101030f06031113060b0f090a030f050c0405090d020c010e0303070b13141908 76
    0x803e5000e0b42c9240c40c02811030300007541d98000c0581b031b801c280c4a00351050704400000600c3e50440e1881d030251075401031890b481d2010801002d00b58920203001aa00395031404800710060301c808004000c103600c152181503e07201c141c9042840d100320511010f0400c0707107000c0032180c0440c0c01030f650380513080d99611118100d007840400900a008030360204031080d40d1804070208090f0000210303c1690340c140c4000c0c030341d00d1710344038190f461008128400354581d0002c400500031820b624040c03608030205150100311080411120f205030f031400d42040c0c4800d202804035082c00c0c50303c4038841c421445061000e0008a00d4603e13100614001c40f81c008502640c0000c20180694422100001669225508010040560802e180c0d9096142d2545000703900d00400714142c4007001604001e01516a802080004402801101d455802d48103e5425120600001c8005110001441d2050411000300203940c0c056003041c01c01c0aaa0307481001c2c1c1c07604144900ca040358282c0185507a49500a00b10640c3c0da11 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 108738093 1250 108736843 108736891
    0x609031c031401030c1403030307050d02030c0409090c0510020d08040b0402010c02030703110a0501090302100e01230309120313030f09091805070e01180e01060302040905030a020706090509 83
    0x4050481c03101c0002d20310300220400c000219200241e420940001c00030844060030300d59648002c1d2a0760011030420f011095041c5c0c01900107562114400e210142050354446015054803c0090304407061083d060044c01141054924406600264030082c00e9040302910081d1003082c0140c400340000040e407002805590180444103801d950140031030300c03500d80e80c3c00d000c610042a041802c3c4540b4130100001031662144040d02c040d20703001042c0c0c541858188006030381d0900e400c0001410b10807003c0c0340b0031b4001511040a000b903000c2521032a520b2a003c4c1e107181c20301030281034079072140030b0600901001ca440f200c5c801d40c01c564181400710107000c02c0d03001a58000d2980c1d1140010f6424110400110b08618a144ac0414070583c2102e50254503100101e030704100c24010385000e0651007603c10000262900b021240d01d01d407100000c4c18580301d4002c03c0c140c908440c3d05480c00e030300c00141000750590401a040091520b464440b8450f42090700140040002400c0d1826410301c007840c008883c6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 108739343 1250 108738093 108738101
    0x140a05040b09030a0b16020f030906030f0a060b0a030204030213060e1801020c0105010609080f0601030b0c07030c05070f180e0709050403050d0c08180c0622090c05180609031c03 78
    0x6a00202d1010a84c03903c0c9851202d40c2d1210000c460040c068228008c02c011400002e0341c0d81840020912411550b491049914000b80240b00549058540710001120400c080040050300225500076955906500501031036100c0107175801c841500c0d0000410001010360b03411504100c20880c005409680340b40d4481c007a00a442840380786500c1c01000281650b0844884001c42d00311600341c44206440203410754481501340b1000e00044041c40004100d03410580c0180500c1d4881c1c05d001400090039124180340162603040030382417034621002484481546035100012031804041030252803000c94050703403500001c0c4030f80000340c2c2c1c494022a041502a0056a41020004804012003014040002c00c000e0081d00e5010401d504031161303007900680400c107074180c00405480e113480c01100629075450408014040b5064000e09100402c60b01c0890007410341080d00380d55034640321940802c4030024400491503851040c9001c10020300d290b200828220810180901003a04110107810103030050 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 108740593 1250 108739343 108739363
    0x1d070203040b040f03110301020c0a060e0304030506090105102408070c0204050f0402090604060303140c030f04090609060f03050a1410062606010b0d020309030d0905010903140a05040b0903 83
    0x2010003c9008101d44007071a60380021a8021030300c104803c207814040c14201e104646010000750088100c0e000418038680068428512a10071a485c03c1c4d602d0301c0d654244002910b8a00680c1d45460a0040c100306405400010348240250a00030072400c40400480c0584070441c1004d2155102c001122a8020a118911607401034410301492904454210442e039040301d00320300c41d030b8032100030039880e00b400e03c507160607640c0c162610190311a14011507a126081030380d0640042c401004552110b494400c040c0001344a209400310b8241e0034400c000040d0b0765503030442d440d4031035403200c104081907000130941c400582110340000724102c5120a641024211280c10000c1e43c10114001802d07001c594061034a0760111081001840900c03403026245c00084c415406c0e035107407e1107020311941296005642080c0b01d007046034a000c2420300c14000383c03045500b0070b0f5241e0b59100c00700d40a040d041b49800101a501d0050b003031805480c40c1000d4401d00407401390051559010400c00c0c200e4a040200902c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 108741843 1250 108740593 108740609
    0xa03110d080a020a0b0714040b0d0207020301060f1809030905040203040f0501061e090507080601050c190b0708090105090619020408010213150903021f020a02090901021803071d07020304 82
    0x5200c98061010350303500c2c4616401c9505ca0a0540001c00c082e100b0440b0350000e403030140703000c0d2170310b4540b030740c0c441c2036800464041e250144d0030441400141e4092207988002c004440303814105038a0844000701c120781402032a0381c06404c2c0441d14001a91140004050762011980141c590b1942d0500982c0c0c204400001081ca41c60080c007c00c01c01050101420324001082418110030388502e010b1080e9002a1a200c000c5204030001c100c0c21360090000e800d500e840d4000712804244003200004400354030550542d9855070100c01e002e11168070210499020000034001c3c041d074107003c02c07076139520b89004080b072200c4240e02000703080042e513075011180200f5040b002076450350225aa20500e0040310b102d5031030f01240b501d030210b0b0b09900488210341202d400421003401c0d024040c081082180c805410704046001d0305001c280180d48030307840c00f4081c50f61800011788501107096012204880103110a100c1d901c003400070014490105140841d08a50743e450f0b148544440c0c034264958003458000ca10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 108743093 1250 108741843 108741847
    0x908060f010e1305101e020705030a0e180c19030c0c020616060f0b030c0a0303230705010203070806030607030e1e070b04090b03010b040501140d05031603020105010509150a03110d08 80
    0x5002d032440d08000001d201b418072451002c82020001402c9101d15800144240c1044c03250415050003181c1c1d484da6024041c0c00000c4000c445008581d50000481d01e858020b040490564405074101c0c1c10f01c0081e1200e0f09042110504050010b0640500800028401c0e0400039140e040d10804568030902c02c1e42c0003001340101c0d26003020001c040c1c5001c000300c600910a072006050b0300c0c500000114101c0c2e4060b21803441448041400c440d40001d1940e15003a0850b08005410004100344019481441d16560b1034195003494070400d428210064540c004050810480301c80c854400b1683d40b6410740300050300d688601a55039182e052806507884440b2500e8081000076050b030090b0032841451030124020084684840100001c4410a0180c0c8006040382104a551410565080000b050150341241d0408030441e4294000304480c01003100181d45410041001d41045c001043d08003082106083d040030280c00459280d03150740c80094260100c3c003139014940d445400740b80004c03a80001b1520307 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 108744343 1250 108743093 108743113
    0x30209060c07050f04060e0c07020409020d0302030a03050c0309030f0d09050d020609010c050f0405041d1e0c0d080a050706110703110d0903050c061e03010305010603030908060f010e1305 82
    0xa80b1101d280c030545028020200d8210024a064401c00d4252001c050109079652101e01407903603541c005903012078000e90f03a42d49100140c0d58000190201d54820340c01107030b480c425150300038150b9801802c0f860580c0818418004c590501105417a6a40f95a4040c1900d402080141782d02420a1400c050054000c0c5002d01803c55030215180e803182d46410002c1c056510000002c0362244281c182c10f210313800b0280414032091030a90070010b4510300e54100003c0881c072440c1502e050040c0d110640e80a04880c0040c12040031003444100700c103040846d00950041d81d1902c0e8084248a034861940411000041043c100710b000c0d03025902c051182284646c030703810540340140025083c50503126140c07103034440d2031650320301c01c040910941750f00101400400384c001003480001d80000d501d40000300b103100d8507141381c1a0050055070007076000e0000420407501d10b0a028161903071640001c030154100000300000040300203041411034680d000e4260302541c1d10741e021500700c002c3c03130f8006103a8055911340d1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 108745593 1250 108744343 108744367
    0xb033d09060e0102030f0c070506070c0f050d020609070617042a0605031e0403020d05131703040603060b0f0304151805070f0602030a080109180507081609020f09040b0103020906 78
    0x951311801c0e81c07039012141510344514215103401082c9004080e62b00c03140004200c0c0b440b6112a05007107200300c190511b91030b00369a40a0070005030761801d8005920039020800066401c100040c010440b6082003103e0084621b00c000c02c840d0010f1016022604650030145141c250105510f0f4030307102d0261a800d030903140c10300203055074410748150502c040009403c0741010581030196000b550f0540041c1014503a1480598480d08100c1c02e401a0481c45100000c2142d002101307900700c542c04102940e5038070305140c070140845481e0b4014011b158014007180710b04690020071260080d400c13418514540641c054030030080c1a150880e4140c04507a03904440c00c1203000280e0105803110b01c44c0421859889240c205d03a02e00072250300200027103031080104210001c680c0903508041101000400380705058a80510b801003550000309254008144001c1402003d980d44d405002854020b61030032030300f00d807040d134140200c0d41031a108039680c10380380307a81d41c0c020750442d141c0701e50140010b5194040d580e44 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 108746843 1250 108745593 108745597
    0x9030703080114010c020907121103060301111207030b0f040c080f0601020303060d030c020d08040608041e02130e010f060f0513050705161a01090b033d09060e0102 72
    0x20450104812030004100a000c07846084007034041a590464144802e80803c9440d80e40503080707005001c807091042d08a03419500031a80001d00c408240c9aa0303040c110145400c640340f1810000c1802c8090125105182058582c140c218080c2e03c0c4c0132503a0303040040001c1521030340d829116406498130400c80721030703904021668441d01c42942c0c5a245a615140103988a2200f1507916501c564064400800a40502d04e54100c40d800030f032500c40640000d40d80c10400307a20a420600c0400c040c81c040004015000c1410780b0480d9862800060b042040e90104003a0680c0407160042c03551079200006140009600030006034400764404d01246a035008800c03001003041c003400c0c2c000c00d4103200420b0010390714054180600381c213548030303440c00300380041b10790a00202400440e4440719408000286a4010707131620301030080c0110004d040c41a060403d03140050b0010503021565440352120814052203070b2a0b0413102ea0304a07a40c5140080c40320000040c450101c00901d40344c642040802c0c01581580 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 108748093 1250 108746843 108746857
    0x1521190302160e0115020d0f1202190e0a1215020d02090a03060c0e03010209090a020307020a12030501090b010813080c030904020f030109060b0412150b33040602070e060102150903 79
    0x201c5a035885d42040ca00b00c1e00e403070002d500f181c0800d0384560006001c03841000c810850301300010700113080001383c24600e03104108406c0302c1d00000f21207030740074183c42c64070380075060040018100c514500d40d25540c400c406440d04126a0901c1c640c0820007e03142540307901182d03d070100040020300d0081d142d1421030024080041c281001502d001000400d5003014821105610310060503901c0300c0d80d904007001e000e544004c0800d411402040c0b55500081c50142c850071400035a502c01207415810040c0000c00c643c4902030403810010464140259a2000711000000e1a0000d9050b0741d00c44141c2e54507407546c401d0311010b6400a10000350341601180840c0a503050764400c4000780b103d5a601c1c80060158000d40c01a5440038691414000005a41c0e200c05041c51143c103c02140301c0c010200000c0240d0001105031441103158012010b10314221600c0044c002e4000050710704042c10044002d5940c07080e80103100c018030300c00c1e000c910242e0080042e42080c80040e441c44045240c84c401280c0c50b03411801c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 108749343 1250 108748093 108748109
    0xc0804200105031302060c030a0302030613060e060910050307120c06080c12072309040c03050c04090e030c160e0603010614090a0605091521190302160e01 68
    0x310300c04840314180d8490840d1500305949550454640480020b100b11030920100d0380050200500d05e44400c00380302820008005440041e102d2601400303000106802030040691140380140134810061036040c45500440c040d01c41b01050340c1c0709844400044000c2d007005074188280d0380c0c0054032400d41030403140c2030f92080b964007071090340c0c40109071107150301562285800c00c814419070180c5503d81989540c00706a602c0e041400025541c640d018000c021080d02c1c4248400050b0050303107003000d00410007503004a180420641c5480da1003031580d8040c80c0658410940c88602c0035112580030015100c1c0203407100b081d80c4015902c1130142083d8170080c480c40704a00340318000101c1c0c0d85018031404084a60b40140c10b030298200d1020054003441c0240050212a41c5820100341500c0d000320251007040b0303000c2903141e125850402c010040106064031038020764880920340442c80701062140d002540d00d082e441c00000d0318134040c0e042041c2c510111a9a801c24400001ca0481100899040b60084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 108750593 1250 108749343 108749363
    0x111091206060102070324050406020a1b0308160203221e030c03061e0e0c0102010b04051006050f0708030f18030a09150302040f03050106030b061212030a0e010c0804 73
    0x200d2581e480714400c580741809a04000350400224840602d1079a1003110158035040c404450204001244d1040c1c6040d1501030380802c0b000b120b141c00400481c03071020b030742141e0181c1e001c090b036004183d041d005100c8410403420307005811141d130080080d6445606428000c8205038000f140000081b5458031901090041c54000d0059205c4502c03921000d0700c5d00998500d0303806045442e078002400107a005641081d4101500c501010100e100b4640c0507141c0c4d0016025083c0d10000080c2036941d240d8800c0d2089141400f8821240042e007068011104103041461702d65a22801104040c0a840d9020388103400000030091a101c00b00c0e0300e98803692118004a410165162034195640903414600c8041500f81205121144407001c0d824090605071a000d4505030f19982e84c04000c1e0b220343c0c4200c6490391108401d1080015a18003264072402c01e0300c8000203019211440707a81c0b00c0d11300d541010003100000104951015980241d0022002c03c2c0c02032002e2031081d1001400c8e0301003190143e40240d1320b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 108751843 1250 108750593 108750619
    0x50d060b0f1e040c0903050f0d03051501020a02040e190f120c0b0604051005031f0c1107060e04060e07020c031c020a0b1f0609080d05030709090902030c03011109 71
    0x3202c40034001c4480c5000308640703480003100384002418400081000d10203941000000144100004001d02050602924030039801001c05000c1d83c1020f0036400c250010301d2034110099a00144119104d03030111800308500002642a0b800c152204608540b0040840e1122080c0000300301a01c030040d2040c0303110b00c0c424005050407545207142100040c000c0c00e020020a03600d207050b4100d5500510007038424510942d40301c0c0001e2408041d00e002a405641c050311809402149116800f96102076081240b2200d002000a1b0f8803403226008000c00d0001c0403051101985655102d1000b40400c0510a4a035085c00500603503a00c1c80780c51218031a20420740810300d000340c2e010a194901446030000d025142480da60300080500007010650703c04000550b2286003041c40d520007006002c581c65101c0068201b4080710704005032041b400050100c100140a000c5034000354000880d0a41c0c400000c0000301d51001034144442122466419801e00300800301615280c401402d500d4030880d52089640b807 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 108753093 1250 108751843 108751849
    0xc090103020105090d211205011a0301060807020309040f0f20091c0b040605070207120804090b0f0310020a090807140103020a0909060e010f0b0c060403120204050d060b0f 75
    0x40902009000030710502c0440e04ca03007015119546854803406440c0302c4050101119038000441020440000d01d160380b000759070130307102c4c03260601414400165081400207200680b40724030040c465841049421070005907058400c3c020307207104d00c1004100b80710901507280688003400f6617200c0b121766a40741108020303210200da0303103d1a02d0b980d000180307818095642d00f001010450841c610a00c1ca0907002903000103901d10200d14829441074800084904040c10000c2c81c007562504070b41030300c0b5030000d030700d001041004050781c04503562a031000c620b011144020540b8030f401c10f12442e4040c42520081000d906040c2c002d4200401c5940c0e0712292a0b949601c2150b40ea01c0510030b00440b48001005102c06500c40d8000342002181403d01c105035550351032400d4100d40301030707000d4000d040d054801400351b041d044814100078458807981e035041040c0328090350f0f1a200054002801d200c000b82481c500c003542e6070142c034000c0c04000e00341140c0511905104e80600301c0180c8507442030001c80c10208040c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 108754343 1250 108753093 108753109
    0x1501031518030513050607080a20100b150309010506010809030a09030f080408070305010603060c0903030f0e01020f07090207120302131403150103050307060c02010c0f03150e07110c 80
    0x214078440428040303030664078161281d900200c180300f001038500802103815101d1a00820403540305102487c0e4500c2c20040003000d000c034a0a4103400b51b898409881c028000005481000081c0140c00141e20590080001c825404405100440110101c01c01042c8034040d40818404c0600780c0b07914400d070351101c208645a119595200700071482c0c0000500101d0b203114043e0764a944a04407040c5865102c04d4910b180c034009905c200d415a4440320148200309007805030280440d102c0c10149034150540d83d0181c40d0084c1b200d146420010001ca100c40d02d03a200300600d4800c0d08803082a100d14030344407003943c4e020303520001c23055841e000440900c1c0c801d030b44280700722000080c1c0c1031501c11074182000c13001c18a691400b40c0c050360600c5134990789a01e1ba1484a1418021761051004583d103051524125060b501c55040c0f0806591501500d60890fa800034494104c4000d145400145580341c9004145406019007080480d901620100f01840b500301e49213400d00890203007152030105505042007548 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 108755593 1250 108754343 108754361
    0x512070c050618154b0606040302040e120a02010e0708030406050406121e0b090f060303040603020c03070501090c0302090c0408100b061908060a0e060306060111070815010315 77
    0x59404030000f6040c801030213403800c2e0865071340c509410b908444010760100e0560407209202075041249010104542c0400130a0403a81510150071068642440042e02034001da201c040d0203151102c041d4080106c05000c20b4140aa4810106071240001c4000034004e000341008421311f44100d150101da40b64000040d034007100d04a6072035524140c28500e003200c465094114040274541c40781c0c6240107440d01c003148102844005240000c035218080200020504080c0c40b801900000c071085c041941c80110444040d50324608001daa2182c43e5481c40346948038145010f0440d52a145580d010010280302e1801124022111082d040c1c4845640c03516612403403013500c4407944042d02d040e600ca50540c01988400f01c000b4101428802d200440e40e0480130000f8607140010020f008000007458145403140203410b500e01c9804203458401c010a9885030050030481c10301644104440d2822002c101a0000d0b1060f10143c0e0880d480010710307098940c01c02c1c0000c6492803505016826144008c1c480c03502030b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 108756843 1250 108755593 108755641
    0x60f06140d0209070e120601030506070e0414010b031305060103050c030c12060106231201060908070602060c0d180501020703030b120303060918030406090306060b0f12070512070c0506 81
    0xd13403540c080070703a05640c00b140141d030001403c8494000503002031208a00960280018103064981408002e10140c6e548411790300c11843c01259592209002034500e0640340240304c002d9890b100c0440b120122410700740000c01c40d01c204000441042004030710006144c805900300c2c0c1181000e001040072480c00541000000c0d80b180340104502881099032051000309803040024884000e45c4d1070380d05500541c6a1564031018000402c480ca078055a401c00800800000c0e10540f8242403009459032005440e0b241c620002089c515503001ca9940a039485410064021043c03041a142c018080d41040000390042813074155048101c1c10980200d08105034030780d001d0f514556880c010421040c0300034100008103d108940000901d000308000c00142010b81c480500441c03940c5000c42c1175400c260040602607105009003d50141d2034000c0e203503034031207480207040c1e1590307910310440c2c241c0a403800f4005404904024032031001c0d00211420400c900800c2518460b03590007041c2c0184020315040012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 108758093 1250 108756843 108756859
    0x50f0c0d0c0e04090b060a0503030a0f120e010e100509030a0c02060a0c0203070807030c0f0b0406050c03070f0f0b0a050411040905160609060809010504020112020f07060f06140d02 79
    0x20310419a90012081c520365040c420058241d000118046400d845001c50310b00d40500b050015a18011450100400044004515115244000518a10600b45400305010316111842201e51103900142280559240200190f4148044c01a0b0340e1220520001c03080b444c00012918202001c01102c0c986940d0b44c0b50300c00460260340c24011036500441c01320040289a5040c500103030f405104110040c01c64000800c10281141003050480307956501c00494900401c034100414490502503034120b238000c1c18810307215504000c44c82d082d4410310b8001401001003d01d00c01c00c100d031400c1040256402403000c001559034030754203601250015903000d420800040c1000100d4685500603030b60441c030441c1a02c494840c0350007604a901c01c0c503000100802c0311090700703000c081c0c0d20500442d40149110700902036800e26800103020340141200080115400090100c1151200c0c0b0440318025480401004065140914a4010981c0f4051209040000e0f20520350500c0c00750301104500b40c004080074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 108759343 1250 108758093 108758107
    0x305030703410304060902040c05041517040f05070e09030a0e1c020f040609050c03090c010822062c100204030c0909030905130b0f0a0b030a0b030316060f050f0c 71
    0x1180c0354000800483d001601d80b8541b00042c0c41e54040e0181707140315511401d40312400d0042100704008010101c5c400c100c20341c20304141c038110144080c0d400c10b4010740c14445151840c1070203410507515810008440d440c0e28144240040c0000c02400e06100c0382e91340d1a00c0354030319000c004040040340050000604000d180701e02503c0e0080001c10540001000000d4580d40c0744440c0040c1e503800c0703c006d21020408010800340070800d010042c80d580f0240703404040c520b450840d0104240007441001603003064030318000308012860380408504d108400078407107600907681c0f01c0c4081224101ca0751200703000780140700e000d50001d80256416a58000001400340d420031086000422890030140c0411000c16000242034403020394520100d40018030201d0144420303c2808581c0d020001014055041d1801c10025240854150303500100c40c503901140d03003030f1034000003459030040b519004406142c07140200d04008c0980c1c8842030785038844405000b150b9540200d4008068202e45262161000308448 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 108760593 1250 108759343 108759467
    0xc051c080a02191d0a08010b1302071a0c04030c0b0a0908010b0d06020706020f031003060501050105040608060607020a08070810050a0605061b010f0f0507021c1d0a0305030703 77
    0x1888130201180d4446140c0c004040000d83c500c6141d0340031025695481d00111041d081520507a0800010710b00b0a40c5014515030b580f4144100c3c1d88401d00c010a03101c40403c2e400d614203801c442c011a009005404010b44644008600f50320464900d000710b09249000120b001042c0210000a000244940c801002c075442d0800607600466048440d26401c012240600403560040c2d40203a51b411804010107055291550407504c0c180c01c03c034144031080c041001503d51101186910180940f9019107440081c0302040c900103654000450341d009401c6c0209440b140064855100e1b041d101c024400307a00c4a119141c08c40717440b07025194100b1f0041080f6052143c13000001a040c007100b500000b011010100c80300101e07600703946820340f070b0b640303510a2040c2140d041040c018100c1d12814468a5481807100240c0f810386290f0280003c80003200305011641d84400c2c12400864011080c1c0e55180b815190041c92074501201411001140d14885020740d6080e4028070283c01c2c3d030092505e1140c58100f0300c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 108761843 1250 108760593 108760607
    0x3801060c06060b0c060403140304050718140411040605040e0c060c031606090209070e010e100c0204230f0403270b07060f0c11100b010c051c080a0219 66
    0x106980e0301d40ca40c180090341d914003c00425506203d640908018105443c00070021810244c040203032120600c1032002040c0082001002c944085105a84120800040c41c02524a280c0b01c9000181d024040209000025101014403901120200036072611181004200c5071b594181d1041c03680001d403681411f041150041207451070031011641031581861305a10040e944c0c40781190a152240404400c508105c2a0f035a0000c110f420210502c2c041c1100090058404540c03140c4920703002109004403d0103403c1000c4696000f0300b00b0f02c800c03101f10301c204100b24960500740c0d190f110000005a501180d806103107000300e51664840c1c0c042c021506013001c001c20940302915010303c09240c0001c40301c072180e000341300c054800c0c00085050602c1c003041404454409604000703100010070400d5040a001c14800358810001c1d10000c4c85130031400040303c2c5d045096030020042d1041400d00b80c0c0c0d2641c0c9003590110042e980d5103914003a913408200320164002c42401d004240840d0300805107842c0100b00c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 108763093 1250 108761843 108761867
    0x3040509041406090d0201060b0a05161e030801030c0902071509020103061212030e0115090207060902090f100801020909040f0f17090307080a020603070f110a380106 73
    0x501c4030b010000300ea406080c41d00644114006078005030404520a07028050040148406ca035820708102c000d04014020b80b041d422a451020500b10003c0300b0014030072003080700e00f031103003002169104003860040c2c0b2294080c00113545540c100c1000143c0a0204d0003190700c01c55101c1c0115040d001040d820f54007600e0404400c906150321003c000c120281211302e40b4050f07074001d1410004151400c0e0028084620000808440ea410066400145240c00848500319800004016038030070450070480002d0500c510001e5006203080b06102d20001030040c1d8034081c03030180c1c095030000c5586e1044c841c201d210f02d440280c2c002e40d03008009008500802c100110850040c03a10005a40c0142e450341903010b00c0009011154201080b18460707802c0030000607003e8038200d0000c01140050342c000920900009101008110300c494000700c046200b0921613400090641c200c80010f40030b4641003840004120b5450013200004a050510007110b4078020300d000d050b6650549a41d00f004021a10400c0c6c081c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 108764343 1250 108763093 108763103
    0xb160503121315050105100c08040b0309030405150a0c0b09100c02031305010e030a0b10090f270b150409050f01230f0114010e040c0c0c0510020304050904 68
    0x110818408894401e05207202c0e001e9940e0541c4080440d15143e035000304070b08443e118091030140107010b542c68400c4841682105030901c40b201e11024030b8481064801c0d43c21120b0103c0010040c80240d1030004060b005032103041310b110f025060100346019850040000c5e10b0001040c0c40384130070104840b100099041144203080d1208640d01c0e642440c140d885000017140140d0002400c2e411b00c010621240d005040d0929058030400f1000000960b40c000a0402908007902e41001c21849045d030004000202502407050005241d00a1001d00074216110700018200702c14076016180381b15008220100c0d40d2001d5852000d4861900c1c0b802c5d110010000107070040d96031040300003c04c000300604c00f207050384140042910000d00d01d103014282c8580c0000b01141840009009480844c03517034040c19116034000741e0621090304401282d041440410981e0010300d841d5151503000d9200703410540640c05040b01d81541c0f540d8070140300500b0420b00d83c0c0c500582044c002808545001c41c500c58015000f1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 108765593 1250 108764343 108764347
    0x30c04031b091a09181e070f150e2e021011031801150306050603070902040915050303041805180102040605030103060b0306100302010c03020106030c0807050f03070b160503 76
    0x90401508682c0d01e8015000707808010541c00c881d40c5070844da41da0340080c1d51502c07117900d07103001558503540314100070205800411180280a08500800c0001c00800e41c03c0340705140580d44141079484c034690a140040020fa150014098500380301d5003007035240c2d031180301000b40c03000c0c8240c0c100c0c09001410072140460094644404004c0d4142c0110101111840c0d041546c03410194030482c00c507880e03440307195196418050302c8030200b0224017200e401c0b0784c2c01c101c01088503135030304000a0504045400c03900609201127030104e0703209980c1d03001c00c1071642e074044400d0b04241c4400c101980c0e40107038440c0280405644500401100a68000e01c0e0804903e80286001c1079420030305900ba40c0007a0044000210040010414050340e8081c2c00c1c1302c10340503000390282e800c01c10243c0084481d2400068140440e030300d85101018801d5001c0c800070368024400c2c80e2003d45030440369403140c0c4948500d62003031001a0320100303123140c04240700c41140d038510701061520382c005500e058403110f8401c040d039150001b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 108766843 1250 108765593 108765599
    0x150207090501080d0201050a1401050d170a270f1e0f03030503040b0114060304080a05070212010605010905061306030e071d01030c08060402030c092a030106030c05030c04031b 77
    0x29a0180307038080e2020307002511007901501c41c0203085450040c035008540b810200311b50414800c03010014103481056400307420807a9036003800041150040070154030902c00040c0b0004640e070207642c00d5086da284482401c03d4442030700700741d5005011f500038690001c2c5000c40410481c40308100030729980004220200801d60386140a2540c100d580e0300c1640428000001c100c200580c07411038502502d000440e00440f0111a004203e460100510013411800d0002e011221b180c003580c00da540c803a500130303e2100e08a24000409000c0d1a00748501401b00714074a03c0480d5514203d03013a21a50200d1000b1035048502d404412405007002038009011070081d4540410210001c00c5520000041d19003052850b514524001c0800421948454166007248040c04010f03500441c03504e40d144000c40d03080800c2c0e10f4210891a1060350701c80c05400c100b050342c100a140765000380103541228181c1c0c4080201c007102800a0b0741c144070880e58400085000c020600006820a400c501815982d80e102d12072a41c07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 108768093 1250 108766843 108766859
    0x503072f031c2a060c020c010f09050609010903020405090c03010f110d11040302060a0215100303050306090711011d0616080403050304030210020a0c060b0406060f030911030a0803070207060c080301150207 90
    0xb07104041c0c132840c1c0c1300e099452a45030100101034075a0070a20b0910340221141c54003d11441c50303030241d98400c810004044034940e10036503100303020b95001001000181800d25040c0d6071100c4404041d4040d500703211580d01c0303015403031040102107000046c80c1480d0000c2c1d490507034020a518803600f01c1c2c00d4001e1101201580b54030002e4948200a80c0041921030260b020014102c14010164026145881e00c00c1c00040da0000c15250002000d580801c026110302d4025a00410340f440032015540c60280d0485488290000c3c8510108410082c2c0d00340d43c81e8503d20454030204e440024001c6149c00000c200060f01c11001198020302900c143d540d0308104259000c00e0340d100d0652200010390f03030622207090010300e02c01c07070b16a2142100c0c03c1069a203091406840c03030314403034050804e059580428105208a000c861b458120004055030100a014075102c84190403d61b05000181714036440860202d000d5410300c440690001403841c11603291443e00032900222805040440c0240003001642003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 108769343 1250 108768093 108768167
    0x130b0106050f041a0d140f060603040c06030e010906020d02090112020f07030507110306010f03020306090610062102121e06060d0207030e03070b09030d0509100c0503072f031c 77
    0x4011b9801c0b0a10504104440b442c910201612591040e40d08005120001e40e900820030102c070868280443c08541401c40ba600400400e11b0150181b0f000040707001040d18a0350040c84030003c01d898071183d0f1a10705c40d00030100d0064405044400c1010030180c008a80650054007055204025074203248109070b01090520b40d0a9001580e0a5002c1c14103200310303c0d0a110080c1c0c0040c0c00e1006011520340044502103e002511800d004e00091450803454801c00c2040b898103121458001d40d81c5a05442002000e203a007103a43c1012445a010f03000c924005841095004020041c02d150038000740b031115030001c2d032101900714140310f8201c6e0102e0701c42c0c0382448038000420b62440642d45503a40e007010f042c10700140740041d60402070b00b0000021140d4070b0800c0c1840c105564031b0200c8180380340380341c82031a40c400d0f040d003c1e0034041200c502400c1103030300c8025428103c01c0c0400c1540c1c80d10380704042c144e40e54003a00609060304805424400030710b1248800281043c40c02202999011558810014be8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 108770593 1250 108769343 108769361
    0x23061b120c070e09030a170907030b04080a02061003080d0506011b0c06021009030917011d0d0f1106060d110a0e0a05071e032003130b0106050f041a0d 66
    0x1900090020000d81d21103e00280d88020207001561409144200c0184049a200d015100484001e0301007a150001000010b000d150322219501c0c403810302c2e0906840503080040740000503c5404005610420704c4440102280d0340b055405082c80c100700b010102400001f02001d0421400b07150391011155016410343c0103a00518501e0903d03070070050003e040880c11400b108505051407807082c006a0700c0402c0a04682c01081c0d0001d001780c825070b60502500c0c0c00e0042840024641e10881d03422200403a04090b012043c0e21124641e04024005882200402035030b2841c42c1c1020002a001e42494070041c1c147e24458600b0950340701c00b90000030301d10b806030f42181815550140422414000300e200d2141c2168080c01c00300c40044140d02803000516035000c200302016100c4801f01c1c86058940c240e105c4030002c06000949a14000280f2654044400b40580b02d00202e8000020018081c904580c0b071a40d04501762071926044c00d4081e400c7c160800740c400d0b81c0e10020000310600012500c104c0304030f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 108771843 1250 108770593 108770617
    0x10209060a030f2007030509040207050102040806090c040507090e0910060602070e10030206030c070f0c060c030f14030606090d0f0303020705160501080a09030c0506010b030123061b12 81
    0x44549043d40f1081281d08071070743d40344050700e00740b40e4030369002101c0c065900340c40e81072a02070b549440001c0414040e01864a000b0400d40c00410082001078011a900f44281003401c00c60304030607a03100400003030b18019030780d2034042504150140250500440442ea0100114044403000d2952510000403582c0341d07030042e0010b03044400c00b881003d820b5031101340c1180c00c03410001500c42c116000600300c1d10010f4041c1da41341e03000003810010490032030600101e442d0403820031188145c0c0c0b2034014008003404082100007485083c440683d55001d40390088d00c0d0001d81004504598805040c8070b8550300505070141e00007650238541c400161190a500b80941c8241d8000d80c45012070b00d007da1820f1240b1921000300d5600d006d040c480750740c0c00001c00d54403459406021949007420b0900f41e0301c141c0790100142060181c2e40000c1880c7d02d013807000b50f04844c600c2042e5000c00d8032120315401c60034924106968401d804006004001042031104846000c13144151141e085a804003a001d542c40303007640301c2e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 108773093 1250 108771843 108771851
    0x27060a0e07060905031005042f0f19050f030a06020408030703140c030f0706060815040c06030908030103020907090b130e06090105010e0d05010b040905010b040e0304230102010209060a03 82
    0x50440c060007100c0003840b8a0811004031800c040c0003e840d50101140411105d40c4c0300000f601380241d10f04d0211000700766412140c803048a50110203503007004002c0017806070000d940002542e042c00341031001c40c110b000300420169410300c3d0400c050400e080041c954588a40b07200d040c00304a19200400003443c1e00d000466641102c2d24024000b5890441c0100184106100b505040a408030485005001c80c0b400d031540c0d2160f034940b1400501207508400f01030701c201040c1d02c02c41135080380194081c90003840207050300c66449000310143c60b840310f40100444001e000420040c10007054290308950f01d806d100b2106922168040c0280d003204003034104040c0c0c0d01c0c00800900c1144d1a40130f4005d20240c0b0508019030400001030400e25252207054020410340c0040740070700a080d44151141100140140030340040c504009001c0c10310500344a01c12480c20b4821800090008115000c80310f011031042040e141c0d544034030502045580007141995002c06c0385c403289540740401030801d4000d5440c002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 108774343 1250 108773093 108773111
    0xc030501050a060c17070512030415060b09060702060903010605041e05010812031612021308010e010203010e130f05120a1101200a0c06090602120a0506010827060a 72
    0x10248603550f601510034030040750f9500000c00c818014501c64029104400da42d40c011901e8840e10b0820a80c4040400e20703004000d020811011190380c0055a210300824004c01d03881d000710100c1d034400d050340154030103010040c83d001820003401801e800c400003000011480e64031408901600e00e2038a0140041101c1c074000342d0031007203074407595024150301c000400d05c05021642e05c81d580e120142c011009405d03101403410465100706074404090704542002d40d21121400344040380c403151801160007550800c542c5580501d014403e07281280e00c210000701c0076440b1400202c0a40c985040141c075480d03c0600003101050042044500c0007000c030410f03d5603202e0f0a6801400c00b8040803660f40e469051060312450090385001e09072101c03450455103035a889100d075003581c9100c20480700070706503400c00da180810701003070350b0107055070741503842840010703030b4504400008540040746c145000c0380f0060085000241610200724501801c410b02080c41c99103004014a89a1b0496030300e00f07500c1c0c403164a5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 108775593 1250 108774343 108774349
    0x5060307020a140a030917030c0709050a0b03120f0f0d090302031305010305160f0e0415030201020d1b060f02070b04120306050a0602070e070302072003190203060406050a0f0c03050105 81
    0x40202c80038843c000d0f185119103540c000304413501d148258418038603a0a20030001460030f02c1218130058403102100c840c1170740e5019190141000712681e62026103424002c4840f410b0110f0380b910300b507074032545040c07070034000340301d6904907412090100c03603410f0042c071940021208610851855900a80081d529074103142884034419005811150404d401c0005100e20f801c00c03485055003500440c01d021010020032401155614a45d005480c0d001d82002142000300c00064124402e132030003a800d403402810300c0307001a14a5810651919641c50000480e200415420f501a502c00d40044002518060389500d4000303000c0b000340c03415680303001c60081d4441c400d60188101c03802000142c03160301a43d460b0079000f9407214a01c0c4140d0302940714042c00540f03058441d81c12192040c0d880603030303d034007a80c60740f407a540105024203519001c0e02c54000c074030f000b10300b01d02c01c542d80095005000300210365540e40c80313001030b000190805104c03036160040c0d01c0341d8054601898201a140d40e9002510398501010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 108776843 1250 108775593 108775613
    0x30b0a0603170408030d0c031b08040c3609021e09070813080717030106110f01050c07030c020f060c01090c090e07061b080a031d0c011d0a05060307020a 67
    0x2210b9208220400600707a012058501142440200241030410544154041c001e40c650341d40c2100751020002c009147c000e80100c0c060380c0208001c0168944400d40c035103070054820011003280c00c1c20313144410080003080740340c02019100c16000c030b43c00c1c01d15804517683c030b2800e619140040300001c5160040c0d080c02401a54861203c0c40d01c041305081020004d0442e0070640c2d0090078407000011500103011141c080940904254040c2964130741c2e56900061404544481902e0503026801d80346030801c505004881c0030325040c010303241c600b41207560140e401d6a400030742242c1000b172560051125039100b80142203c0c00c401400407a40c501079151610103060585c00401c06d0358680080098070307c00001d503c034241d8015044c0316015044216010030b000148000003011a41e0001d41d410240d941900300003072176000215010704e0400d210704019100c8452581141c00030f01010b100c00d2020b80720342a00b2082c150058201143d03d511800801c0f540d510448009016a001a82c41020020540c4d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 108778093 1250 108776843 108776873
    0xd0306031506031214090307060201050609015102010b12061509040309241b02150904090501060314070509010b031b090301020a09170a0312090c030b0a0603 69
    0x70080020605559072011541c80c1031060030f0410201c0d401d801c2c04141080d045460715a0000d003290b032442c0d40c0e400c00070702828085804901811542c0c00005004071040c5280d03080d01207045000800c40c2840340e0381005e101c0700c0d043e250540500540304641c8414100d0b85c5180c010003e9002140050000c801e000103e02403c41c030400641c0160108051040b521820f403400038811075844001d5181c6003022201007881c2d42005c56260b4090007104103100b004c2d070002c8031414240d20740400d812240030103c090b5401d0220080e401410032003a140070040d14100500104000420004821507243c48860031180c0c2a001200d00106103031000c2c00c0c3c80e8040103941d008101c1100d0a140a6042004545080c08050000162000c0303c09444000c4203107142a1620404060021034540d034560030008c110121621602041000041c2c1c80d0b0b400740008503150b040b0941580311144007804188800c002065955030903113401c1da64042c04000608941131080c022882c54001040160039824540000c51000e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 108779343 1250 108778093 108778133
    0x5040f060c090506300a0605100f08130204110a0203071511070303050a09240e0610032a0602030a020d02070e01060305060f150d0b060c07031b080d030603 68
    0x400b000725a443c441107410030b0080201d500c0b85c0c202d42c0000c2884080500300784420a264170700810448400385d078844011513908a4450020322003c075010340710f00c401342c2c0d0407900080308000011003035460492076681d42c42c40504002204101350040da035003500700e03c80220058000140f01030034040030103010112208800820040710004404a080c0b910503088020181911000000c006102640c044422039800940d1003540f00b00b03c940c9a5400b0a0407018415407528102e25040c11001c0010001e01c1194805c010000080c2181c8407103450f41301044144141604102c06145079040c0300380120020703c0d9640041d5241d400090000c7d0404284210440c11540305a004006004803200ca05045424a05000500c0d0302c50002103084400104505038102e00351718800400c4031071202c01000d0b1080f61840800c03051990708104078072031295580d040110380c030007079040c00412080a140e03d1541c001558400011350354000c0d190904101c8613038600803980e5041d08205208140c1500d0343c009a0039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 108780593 1250 108779343 108779357
    0xc0909070e04030c030e06190318020616020301111902060906280906090c06020d05040806011a0d0e0106030b090d17060103020f07060f11070b1603020d05040f060c 72
    0x4001c0000c0e240c94000c001a0420403844046414140145c24110350541302030000c55851007441d442202c840e055840000c0040c0c504402440a040722859130f4000e10381c014580c61600c41c949a41c1c6800b03203441c0e0700590b415540c1e080b07100070f482119002089003c852641c0022006842a80a810084000d00ba030a0341d070041000c01c4422194001240c1000d80101e41190401043d800c100d40103080d41940140700c1464600e0b000140b05044450104582c560b070b08903403080b003505e1070803501801541f05d8610ba0340e10403001840b00c1d2110705d00741d03400c2e482940c4025082040c80c0c0c2c60503042c6c60541c8100c0883d65540c1d5818401d02c03d144001d10303800303d1031500611545800f520014210108184030840c61400341c40030030316603840b980444040480a9148039218012410540f001745090305206680d41d10b00740100004005035070039184070540250310341c14166030703030b600300c80c031009000c000c01080540c01c010764a09650940b09031800317a4000c800400c0c2a1000e1303d880000c40c0c002103448410f10200d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 108781843 1250 108780593 108780599
    0xe01060501050a080c031e1305060a06080a020d0303090b0c09040f0207020f010305070e030f0f07080a030c080715060602011a040209030705060f0409020301080a170913091a0106020c090907 83
    0xc0c52003034005481c000002c0c0c0ea55034000100703042452800c886147c40301003400f40540b05081d5850f010040340150140c0740240c50b4000944111005031080e006030b07400c1802c40101615062088035030b841d001b030402252b603400035520800b20074800c98941d01d1104010603400003506161044440050b0301c02021071030402ca03900007403039218128641d18109900c1d100010410b1f8400c841d42d0601c124040c0803074041050410b80c0a440300d200d401003248a100720000042c07901d130001201d081d45905a02c503104076950a45403410700d0b502040b01a601100d417940b9440e50032142e449110700034106c80c0e0001a5141d0100d10300d850f002c10881b0745901c00c1c3e0040c001c00e06c407540c022640e481100e000304c0c4d0b850780c1e0b814100c0c1c1700303440e5012329441030110b030703101200000d071103200828203090040c410000342d01d00d41044042c0d0382c518052226000e07000584440d050369040c5a69100d400e0f00c0780105041108040b103288580c2560400742c0005006801c0b204d5807032160b0900300d1903070350041c03103108c050014941 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 108783093 1250 108781843 108781847
    0x11010b0306090a1101030b0618040b0303132301050a1413030b060108060d1e0f02040212091212061201020c070603020904060f0e04170c01060605070311010e0703020111010b0d060e01060501050a 85
    0x500159800190308449c0c4402c580c1e540c0c2d071004c6002c040140c141da03107400d8290142c118400b4a803007145190403801e08603040f0758440000b444c10305c1005848003810840000f13011686c400c83d031105240729103405c004865038501c085420400031445001c0c0c4c09031524040c1300041000e4000b42c1141d010350301d40708408000030070032014002c0348903405441d8107542146003000f040801101501039009840000c078a0090101c904141e0302c200c900380229408183c0c0c030001e5000a10a110581e100d0400b00380200d090b91900f03900d0074400e10000b6002500341502c5048550401100e40c5c01000440d500040c1100242001d000f4035000b029890030b050b42951130040289071050b4001c000030090030350b00c40140e035803c900780300b40c81c0010042c030002c1100030b480d0500503100c2e070b110420540104800603109035101c101400b070261461810700161040c01d141d6401550040205006c4032a5075403201d4003013079103480d40c858201200f801424042801030400040600711595a00311904100e010011102069 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 108784343 1250 108783093 108783097
    0x406023a0b040b10081e09030403020102010c020d050a030b010903020402030a050a0c020109170d0207080406091e0815180114011a04050d080f071202030a0e1f11010b0306090a1101030b06 82
    0x4544c80c1810358143c0e0710700c41e0384441065101d419050320824403040c86a1410000040c100303070392003a002007045c150490340981e900d0a007280e0b60f00001d4802c102c0381407007030710030382000d0324950060404421050b00c0303600080030303a0422120085042da0318002c22454400601403811541035500003041000d2840d25500300d00501c5014a1b0015403000a030003034000c503694110366200ea0000003640d269a124035006045c00c00c0303889003000c0b104068031942500c50b00d42004a080305c840070700034054401c2c041d030f850f0302040c002030146c030750381c03105181c0300703004107005e01440c034042c019402808119810b0500d803015980c1c0c5200e031041040070134001400319031202a01e0301e84941c0c00c50340c1c56854243c404130a0301c0c3c6100301c10b4001e10001407480620081b42c3c00001801014903607855600300a00c40c1424030039618040c000c440c0f200c010076040720b0300c0e05001e100070100300300c80306d800800d1344011701c2e01103460803000307032110401540940f800b2014000300000c10000e0750800d103414008890004000b508034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 108785593 1250 108784343 108784369
    0xa1109060d0e160f0602010c030618050601171501080906010e0105061303050d080f0f07080a0209060408010c20010e07060f020a0605010603051501080105090406023a0b040b 76
    0x50b691080c0807110002040001c3d030a9200e0307819150a1034490821500410b803d01c0b40101540c03c1610601d00c0301e010780100015a008541c040551004c220080c1029041c06460315040c0300c40625681783d503002103800b00788594040c1f00701c070203008400400103210800080c0030f00c280f13410681c0180b10012120b2401c0381180d1046868903101c1580c110140f18042d55036000800500c1414801c00c2030540044074a44a001c0320382d5806250b07622220a070013240402c4030100000b446c1e4800255400d000e5038041c20302d4103130192401d41460349580e003c900f111118280d80010401402d051244100c111602d4400c40440e18002d008400c101d0b91015540c0c030250040c10180301154a107a07074040e1080041c0d008043e0070910600c03955a603000301a0080805a4001e8124191807103129000e500403000a41220000703482146165078546540d0000c0d08500c03e440d40c0000811244610fa80400e805400501c45482d294400d424110006c8411203c19109c1c1c00d008900340060180e0707640e204401c06102c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 108786843 1250 108785593 108785617
    0xf2411041502070b12060f010309050705100905030307061a0a030302070b031e0f01030606060207060c080c160303080601020709090f06090503040803040609050306010801090803040f020a05090c030a110906 90
    0xe0075100ca001c0e420b00b0159000b94010180100380503500e40c442022150003010b00b680e9140c05008590011003c0e01c10489010704203a00210040180381069035501d05480018a0310039050f584541c00130381190f100501c02c0e107041d078480031081003180811962000000c0c0880343c02001e1481d40d40d000e51600d041713100d0080c03208004030001c0c1e44242038400c203d030380e00b481010140c5140b0b00f0241100d59101c0a02055071a6440d0020206d003c078000a00d0340306440443c2c40c0c0244016140c0d65150450b40714510110081c00b400007070b03441303100781d44c02550003841c441d0329513040a10f400c4d00024509250781e0700032145142080c843e200400c800f101c0c0b840781e042c0c120801080030445414102e2031441207a000d100c0d1403200080004500740c0c0203050100341c0c0c204405540302c3e42d982c2c140c0303282070b20b02403e0080c102140030004140064180c05200b00c12900c060466240c0682e91b40006030380c4038084800b299002e800208000018829101350a0580d81290905040065420201e41c03240031304501c0c410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 108788093 1250 108786843 108786869
    0x17060c070201030906140403110303070905090a060510020a1103120f09120601080d030509060c030115110d050403060c0801032003070305120a140f09090a090f241104 73
    0x2564402c0d00038484e4160011814446003200301020340c07003800300311020303800a0b0302807540201201020045078010381840d80c0b40c1c3c1d000c504001c100700140602401d00010030f85e88920004041e00d9401142c03417000110707005440e5855440c1085081c1c02014001c4070710a40040311284030740c6140074181c0c1c040c40d404000050b281c520000118070320b0b0514078603003507440c03141c0c100003c0d10b080000303507508040816540910440d00c6601c2646d981d9001075030b40d000d0312031051005001c025441c501e451080c141601e04a032490780c5a407006420f00c080800d02e0400288002000c1c01803114a010700c001c600c10780d00d000e520075072664982c0c00c0146c81003010a2051100350040c40215a82000000040e41d00301c8150385c40180070310a01486940031803c2400400c0424080c900701c3d038421010745021350f10140d034040ca0545200300b0001d01420060440c40103c2e600d481d0840401c003d80c0e80da26a65114905502103500d020503000c0441200c0083e141d47c1c5130800f001080b080801c0c2054601316101ea070700583c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 108789343 1250 108788093 108788107
    0x6020d02060c180a030b061503160503040507090c0207150c03020c01080a090b090f060609010f05010807140c011e09031b060b09040c05040c08060303180112020c010b090117060c 78
    0x101e59188a0514640d02244c0481c2c00f04c10b00607407180e0240210011100d80c1c00c0c2a1141014200c0c42c0002c0356200802c1c00c60201d00880240200b0055038018030034401c1c0d51800c0d031180c01030300c202d808814186005901082c414003285c445262003040320505401c181c032701180203903402541c030b00b8040030740c40c100407598000c03505400d40c64010f96925075010010410a2602901d2565105021014900c00e4840c0c00046501c90074660249030584100b0f00b10b40c003595040000641d001c030005462542004040c080342d021483c1c400380a08140c1ea4080c0000c903d40b140c034102070503820401142195160714000c007020010350003001540740b90b1034a00006524928606000c00213010706240d464201c0f07004400c200c10802130b0500442520800c40b010000303208540000c44041c0e01c1299100d4043d40108918104014103d6079242d11241c145082d5041100005003403051ba0044185001d031a07451300c4080b600d40c03902e400098090701840145541101403030030255035440300a0803184045100103204 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 108790593 1250 108789343 108789367
    0x3050c091509060703020102091f1b0f02100e120f0709150305060711010e0c0d0807170d0903020c09040c0524070b01030510110406030b0607020d08030106020706020d02060c 76
    0x746044a070010f080c02e484024a040c064082d600c01c0103901d2141618414030030380a04070300c0f417108030f980090351400e4180150741404400c196000d0815142030454040d801c00507600c2148120480c012580c80c41300d08075510083c8202c0562041003101150040d020013030807031100040c01c1c01150310705000841d1004034506110600000c940001c1c20500401040001164000380d8075039140d400074000701300c200c880031102611508281500d40e172110701388003c100401c0e0240050f144241c041e40c0b0307000500c4d6460b5034410341582715240e280540703a283c40c1d07400e0505406200c18401c81c0000d4445600d02c0c07519903250f003c01d080038010f041c89420824a460103400341e80311151003080401714880d41d101e02c0c600344602012400d2200312098460340c11003081040550140d407490740e40c410760860415040520550190200101d2940c108406000351070160355503400d00201a07010300700c500e5583d410044000c0c1010f030250402c0c015075200003146a201d0307500260041d4081141d40380b41e40c0b205401154 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 108791843 1250 108790593 108790597
    0x317090609060610030f050a0905190809090604180302100c09030c0504020a110102070305071e020d06020a02030705011104030201030605031204090c031d010c0f0306031109040f05030a0c050c0103050c0915 90
    0x280e00342d1f850302007007040e480340070307842042140d0040c82198000500e4102c0c0780c4c981e41e00000010207a9906004031240d9050001100f0b800540082010408070b50b862003541000040140036401130f40000c2074481007d180d446507a0840f2000d02d00007010900b15280c08140310047c0c0304882c0680d078009010200584100d4903c12150080c00095640c0d10b007500b00281150009001030740c0d40400354012499103802d042c092003000e80d014025009401480e141c01c0000c0d04124007120940c00204040c40c0014801c0c858401601c2d101c688803a1100d040d400010111080358000307074042e9111560f03884001d241e02040d03e046031003400003c5004903510604801410811800c055464000d0811000895040d0000d940001e05540d40080410303041d4403c5003a01e1540c440a0110200e46d2032100d000e00303004014070360007402035404500b40c483c16680d841c59503000602810005005c90a0b884c1000014041e450b5090003d2809224500b04500d0b840101c0c8a10308010703108000031203c1007502094841 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 108793093 1250 108791843 108791861
    0x2040b0307080303191407141303060f1a0102061321030f0c0203041412011d0d120902060306190f08030d0609061d0703110403031709060906061003 65
    0xe84094650340d44080e0703583d40040d45d8031000300c0c01150f0100d44541d4644600e91422042d445041e2054494a900381d031610302c94503054032900d4081181c88101d008490240005500c141400203c00842d080908201c803e1400c03100e0b200442000404401d0b0fa0004050b5040400541c801c00011040e01c1c00018000310214000f01c00c14400b00d081e50200e4059202c1c0800708549070086c0103100c003007a42280c0302d12031402424980b2481546044c22420070260b40725040c1140400080c0c070400d820010f80185c00ca51200c4d00540d400301c440d0030121070788a9124102140914428055800c0985c0010654000101414050a10203800c2105091880f5100c4000e010514000b4011515070500a4990344002d8025490f6418080e00090540341481040c00b183d1544209140c403049645201c1d0b81101c0282c00c400030140c442414041d0300e1717102d1000300001c6200352038074044e40180088072150f5000080080549400000800040308008180c1c0e0b9400181110702e4003050428850079402051200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 108794343 1250 108793093 108793099
    0xf1302090d0b06120c0307060c0314041401181214010221010f08030c030706020a050705030f1e0c070b0c2b110a0c0905040201030902031c030b10080105060702040b 72
    0x700d001800d1008001c041c502811083d1505038a100050b401103070380d2109440c0040d0154084030007048000d00c03032508460301600c28a0151600440d002070407217917401640003400d8089851301c1c00c091545e040700742117044482c000000942c0c245070050402040418400143c920744401d481032041c1c40c0c080d4100c2d00030b8101e9020510350700340c41d00c00300c0c003500500f40540c02e00e810380400042608d08002050b901809502001546003e20039900c000c0070703411a04801045c03100a0000a000a00900203020320600c3c5402c00c9403215507403940d0035044c0184541c0c0c0c011030942000f28105220010400900b13980074020600d90302c070780031406a890054404028101180582603020024000c4003040c28514200c0c1da502c400d088036000955100c1040d114018103402c7c2041d000c00c0a1005da80016511900504000070500c4558012038102040a264041c05120170406400c0b466014425840c4004041e1078052550340c0c01e602c054a811810b01801d403103824041013040842d555a081402c80c91b8001d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 108795593 1250 108794343 108794359
    0x6040509040c090c110616030603120201020c0d0503070e0415050a030507030c05040e1e0709021216050901120207020d0c0b120a05040b01031113023103020f130209 72
    0x107410010b01c461814040c041c03030a41410001c4103001d02c941c0c2d03e020404440805040940c8540700c83d1f1100c1c0d010021901c0c240350b2641c8000001c5060401000c108054a40000d42d807507140c190600c0c18040d4840e0408203101d170030301c2840740040e8400a10106114259000070b1555051240680901c840303070310465000e001030740040101b001c007145540c00c0700e119175140380000e600c0d5001c110545060300c11041c855803104040a405c020f83c0d80c0c903a03441c0300c810f1065504698607a40020242d034007242030054015002d0701484080d1107140c0783c8030b441c1e00241c40e01d03d0510b40b0b0140000c003400148000300200640224040c02595103410040790943d038007480482800307540d0300c2440301c070740c2140403204040300101e800140321145601440344245d6002e06803940580c00c41e034401c48001039000c2210341011244c20343c200c44840d107100174010380001024080440078a4420800583c440d044103c4055207031010400050b226581041080f481c111100700380c00a41110b45002800380140865001c2d40c8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 108796843 1250 108795593 108795601
    0x140102030901090308060915090703090515071b0c0603111603210204030206091c02040501060914031b04020f0717040e0105031605090601030209150408060718031106040509 76
    0x81540b00310403c510070f07200c50126684884c100306a1030411140b207501c2e074508030400d40e0340740b074030600d03940d4050210300740064010070940361140740010111103000600a82c400780094a604003c20f0315054011440e5500010382c1c60307a441480080d1403142c038040c0f54a400a010742e0500034003e45050720020b50188240000f1741c10f0041030310003031206010446119054598050703019008075001d6a030080c200614000d40442407000002c3d0561b50000481c24070086800165600c0c080d45009041d20f41c0c60322603080c00d001010f42d4541d6001c070181e21942c044003a205c81401402107100042030201e030010f0722862001d5003046076101e503480c014500071143c0c4810070900c099034043c20a545421380908034681c0c031755080c0341d40c0382021450010900c4e681507041080d49001c46229074445010314000d400c2c0783e40b00010428140000e05002d215070800716040c0400c61080004507480560307840c003020702d0341191104400b240ea11780000b400c9071040076802c0d50151105802c43d001071030082d046511b60b1078 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 108798093 1250 108796843 108796861
    0xb061c06022b0213080610060f030b06030a09030806120601051005040e07020319050a08040b04020a050607200301022a071a0304050706090501090b1806040b030403020c010c11060714010203 83
    0x10104d0703150418200034010100d261040044c0c000d2044035000d4058003002c0c18900f0944079082110150f404040d120b50410045071146000b6501130a18080f010034a01e1035480e002c1c0c88024010625805190733001c902203031a542c002141ca045030f105480501d034a9100b003000319110300ca01c0d0070800c10000420144084241d0000080600d070b0358100f03107120b92540d20f80301200c06101c0c0000c02000607110401080105002c000101d030447d20080c2681e032200d544002107141900300d5201a1b6070135400d844e034151201d080202020300d499048008501d03152031a01c640707101140c52030a10851102c0d402c400d646190b0108810320280090040f00300080d546d40c0c000341c2d01c5500480d021542801440c13000201240120f00c5441030314416150381031900d04098035405076400070702c4800e000c100360040344410780d1a640014409007800d82d5034995070f440c0c1414080c1c54a0380100010381004a988200404245040d003040c11000e41110071130b036508514244001601c0105c0e0100c0e101d54800018000904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 108799343 1250 108798093 108798097
    0x105040c0305070509010302090c2a030d06090203010f0312212a09120204020412050703021503040b06060706021b070801140f06010c0804030f0f0b061c06022b02 71
    0x380319204072064940c44e0307028000c40309800c1c44029080303004800482c1c8910941e0707000d84201140148c044540d02d00d8007002546a03c040b47e001075050b0400100940c2a44060040e40301500d8048002e40c030f075501d07110444906040510001c0c0108148002e402c012a1158048030340003129058010607104d40281c048000303201c0000c002c410b100d032038842d1400e0b030404030300c1200c880c506544584c0c1105190011040b060000300d8012684a9800c00010640000841218044034062401064154194030500c04404ca0040403201511002e004110001e9000c00070791754003200036640ba588802280ca0901d001e40208030704184d8400e420125070b00040c2c8000780b00740460b810500280111100c40c42514401401900c0718100c03511003000250965008112001d051403003881d9280c581a9a5182c0d0048410407080447c1e4183c69050080c050200c2207003070913080b200803118801102c1d0002c01068106041c408000c1c845500425031000c180b0070b001080030010089241400074988c2518201c00075 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 108800593 1250 108799343 108799349
    0x60f0315010306060f0c030807140c01150f12020402090a0305010f0c0318030c0f080418050108150c180301020d0c0305040516050a0303050f0f0d0e0c100c0b04140105040c 75
    0x20340f500000045007031241808203200300d6640c07034620140000340c6080b99100d6006000800340107261180702500841e2000620f284d1075104000036242c1c8501a01d141c00452540c0075940d140303007070b90081c080a11003a100c461080e40c1210010b0351b48629101051030240c0e5540b0180c100e510b04000c20ba0208130304d80000c5a12002e540e01000246004c039400308030a95900f102038005000b240d12a00011102d0302c00a035058000e1802e030703045c11780d1401e07600300744107541a041d003480e0313126401008950810000b40c2c0702c0803000388070404945806000c60740d05004075543c4403841021012a8641c1e07840c03e50441d0805421064140490745104102030060981660111080d02c1135821040c4440c0b0030004420685500074000e0210910750b440c200d80c0358001c45c070086601030042040d00c00d400703210380c01090b410b041c0181c08147c904020a41c0c600700f64501c400140540d0000400798400c560281806880c0c2da030200c5807503880d45560030304600030400050310003155032800060000b8010014518411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 108801843 1250 108800593 108800597
    0x5090c1e120411010302190c06090203030c0d080a09031205060f1504031103030c060c130806041a0a06050a1206020403050706090512030909071d03070b0c010606030516030506060f031501 82
    0x83c09009000460492040020b403416051031140e02500c11482040c1050003a0f01507a4007103400444c640001c1d0460b44000b401c03a103d607101142805c403094000c14815480034110000700407603015910f003d4131600f000c08400c80100d96550005606076140700050003d400c0c00f41c171040102154040d20703401a44039000950328040075151a15031442c0002c00c44120240100c054811038941c0e202692554020314158120021a15000b04240c14100612849a406941e034251000f900d8114074210f20000f0b44071811050400e4014030a5882d007041d01700855610320b400b601c2001550038160020701481c1c0000b07002c3d00481c0d0b070008100390710280c0041604d00c00c485c41000288500ca00ca17a5911420070310640050a01c80002c802d01d00400d002210320804103440c11070700707003503400180c00c00100343c100c044d0302c88002c50504400c82003440f0b0503003d040c81d41001c02480c1842119040400c8030609030204258541e00058140d07116041035a05640403100110b413241055900808649450210140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 108803093 1250 108801843 108801863
    0x13050a0809030c0301180f020112050703021c0b01080f1003050708032206020604020f040608030a030c020601060e0a090203040c1806030203010c032f0f0a0c0501050c030105090c1e1204 81
    0xf40c1c40c03070103100e102900d10120703542041070100c1c0c1e079412040c107901e42000e90510020308414800b8052500489100c0e1444d56030050f40c1d0308500b1a580340c00900c05100c1003080e450031004503a9641c000071890380043d4a008418001d540d0550346021190454000404500a10000003070300000007003d040d41c11084403403852091020841001e0800c0340384100801640712801080160034003010100700c0d11000352012450b26194200c4030f04d5680080c074590002983c0301c0780c0b448450307810f01a1314050590f80c41c0855030b090340b44001504081a41c00740800441c0e000000c03c0030400c1c130a05010007000162150080d00b1b0b050142a40205020312060f4025400c1640d609030203413081c804d4001003480c50364299940000031a1480a000180c4100c40d4040303010440501c101c1c80c04809842521034540d5030501d10001031408500b0b68402034140645004140010b000b6036440b07006242d80004011400d03601c4000d604450510802c41d503003252400b03080002c1c020ba400c1d6524030090700c00c50007072800c14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 108804343 1250 108803093 108803113
    0x306090616030c02030f03010803070b0105030c03120d090204050c0a030509011407051309020d0605030c03010504050a021207030b01030606090b0a0b0f0904090b0115021b010e040513050a080903 85
    0x19444450454861200708440303075407164440d020f503100b1a6036803207a10480741000c20383d5081851a60003a080302e6a150300100d0390008000303007880d005003d408107802801c150f038501c00100760f4603c4c0407181511400408650b84020380d68660103150a150020024000c90801d64180302190b8051a40840040d0504002643c40c2d1414002c080f05141220351440441d5207150307049542c0d81005040801d406d015460000d8000c0c0b030341c005000c6901c06404002030341460301c010180782018101700710303000744d0419003000045000490820000782c0c040d40c1e80002c520328001d1044c1041c0e10754000904c11004072002005214555101205903000303548100250000714003000b8080b0940e20859807000020011030b001c19022130301603c40d90002402c04510206d05a071740380c82e00d680036000404401903005100400c603030f0400c214002c000842c1004003504000303c1c0000c2c0900086c1ea051400703652a030011680c200d59201c01c0c0c005042c0c0043c152101007075185031064082e8440c04106200b480750701d15403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 108805593 1250 108804343 108804361
    0x20f03040b0f0705070b040e071d090a020c060a1a1e01030b06040e0702010f0b0916030c090b03091506180a0b060c0610060207060203120412180312230a080901180308060306 76
    0x1d003180c8070400100e800d62182000302f500c10060803a0800d580a00c0380d03624210081241070301450318500045140200c650300d40f00305041c0b20705064421400300403010011441d00a02030000c40003840e002c201501030001041c0240f04607071000c1800540c10007004070300383d810b40c001400440700c800d05010151301182000002e400c152024608468080203080000d4041e40c0300e0380c821141424240c01e0b103543c0c1c1580e86541d40080303a004030715421405a446058040e01300c11684490f04481c4005505d40140c0090401640107044007449503640800c206207075241740a4030744c40c1c1180f500300c5000c2c0c90701034444414182980f103200090321500d0350209502d070021080e40d0f402400c41132a441155140e03110311501640d001d01c1401440103011008000711175040c1c01c00c000c0c5005540942c11038410300320041003c1c0b040c5020381c140c0c000200010108a10000490f40315591624094001c0d03214420158010710240e44190784000e00105004201608541c42c42d100c0d42040307042c0c42e810f60b525244 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 108806843 1250 108805593 108805607
    0x7030215030a05011d18190b010302090106020f030d0b0102120703030e01110a02120d0b0303070c0816050607080711120c090604020a0e210102032401020f03040b0f0705070b040e07 79
    0x100755420106040006c2a11984412910901c0c030203070308a41e40701c1c4440741e000420a50316141503840c00d400600520940c03c003140e400e030040542d4030040c41100d4504401a44034040da200c14508240c84441c90407140c0e1081215482c0200e01c40303441540d415480c178001d0001c0440b181040559402d2080301640c44280d070064607030551498016050b0003000c1d00c0c3d003000c0c1c5d030302868140b01b006a4600040306545c0b400c0002d40b0b0314500c2a1402848035040943c55031402001405641e02c1e1108643c09005907101c07107054824950f800705000e07407140070701d250425600f09540e200a8111010620401c100800000c1040350f0740c43c19603048102e030301d590089c0000d0340720301260308000c54480b9408401c60306061058201a0440d8045c604690320380fa0750140c00d84e4402d65084400009800c45c3c40e00300c0c0d401e5000b0450b560800d00083c0495690001c1e200e0f2680214810000d030880049a21143c10882e4400c0b01c034201ea00030b0664500e1500c0300b1341210305400c2800f9038900601c10f0000a0f62142c06158 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 108808093 1250 108806843 108806879
    0xc090e01141504020f040306050103080a021005010305070e09011b021b01081003081605010218040506030a2001090807030b0f011e0306050c0702030a030c0210052a07030215030a0501 80
    0x1084101c44602c0d40c00380b00c0654405c500e1280740700e90030003000002c00c600388a00e5010794400d1610716070746d180141d802442c00d04240b4003000414078040c01000012000a49441102e984820741ea00c80d03503c1226090040c020b5031701407007c100340c1c810700b280707200d0713000c20562000c3c40407001d021b10042d100d0004450811048410ba11001d40c0d240003440400c203503070050504540804054011951240d40704c0c0c1c01d80c0c01210362071141905c81540d84030f042c6460b0040d01e6012009a0040840041c00d40320285e284000720305180840000301141c601c40e034899010b00380075150000407194995038914121030031400856840c00c4407680000003062050000550045e0004803000250713540f421a12203800a06024010041003a000c004003001a20b0511618030304074020b403101b003c402201d006100032a1a040344660412004101c803060940f40403a41d2250000c1411280d0181c4032488400c501d003c46680029511000f0140e40d015039000c0b8100a5216007281c4800b403000f640d03208a60030140c14692 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 108809343 1250 108808093 108808111
    0x7031202010218060c0705100507020f040903120906060b07051516050403031103132301020d020d0c02060d110a09050a0f1809020a09020909060906030a1704030c090e0114 75
    0x82629075460700c034021780101902141518961982d4400044800c00b024504c0c030041074001c40c501041d894003030704440340074000760380034001c41c0c0341c0e56001410900c1401e0171216055640c1d0110081c0043d5030300290180c860789001e2a603a02a03400d00a9965144071441041c0000c20300000d03242041d141d1015034413a003d51074503414141903503010fa40080d03052072402503030302c81400454140301c030720304106008111100100c00e40d40102c07a070007403c920303410304d600e030541d80907044001b5000e500240b510080401e030b00e0000c03141c00c11480051441d09c075003207880351070505040100200030b9500b002403c40340c01c3d43e200c04180966810603c00381c000c0030f1050401c08200603500300808060211107040d4048101400101c100c580d030700203580f04442e50000044181d003c00c269990382014840650001400c0321480100c1c40d21600090b6241d0345010000c000d0301030102402208007840302520043d41e40305070440c5840c3e4880d540403000303088a038011021582007054404018545440c0540251945 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 108810593 1250 108809343 108809377
    0x1030914010c021b0f060313171c0c09051516080703051201060903020102060f090c0a09021c09020603062101060303020105070906050c06010509060109080123010b03070e0d0305070b09070312020102 87
    0x102c48288c4040180705054034030b40d82002d03c1c4111443d03900b008244201482100548034141038440f6000c5607020f0300a88140b00244200340066500d003039500083d60740192942d981c0308022b0685c0300c0d104441d407100810118010658404064100c0301030505440c0b800021110750b0390300c210450f0700200310710000e80540c10940c0410f0204c440944883c0e03100404c00c0890b0b045104000c00b2030001100380e44440c250680c081080c0c10882d0801c819103114240800c030600c9444001d40000e4070714400030389200e21580c406085a00d410081001884041e2a400001c0001d0b66032800c003e80600740841d920790010308864408152a8000c01c2a00c0007041050003c1010b03070300706030a020300c00d0400313080541440743c10342d000500ca4400f405201101e000541c0400385406d290303030340c100d170219041e00603925542c0144204910780e64042160704094004603200d2080d0030705410195841d20078014041c1a0540200c10410350b9400012100102e80c0319249035401003030118000ca00300d003d89103d1400c0c034501 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 108811843 1250 108810593 108810601
    0x70b0a0f0309021c050607022a0f130501030b0a0e03190e0d060f110910030f0b040c0206070216050f130e031204050c0402071101030914010c021b0f0603 67
    0x30915202408108608001616100d02e800180c030700700d4208441e800300c0444419410401c201803100316045041c500080a000d4120603080041c581c80b448903460000401c002450b0036a2441000781c103445000d400b0440001035840100007400e8240415200c06445d42c1c007040c10b607119071040c801020f0140c03018609001c0d80c1003844071002000041c4000304081d000380c4010903070300c84400c200720030701c5040c000410711000e09094054501801c1c502040c03c6003801040c0d01500c5401c051800d400d483c2c60002001030358903030044010100c9090b0207810901d04214503010075000110103025041399000ca403070030104c164103d00f05004038040c103a00100d00b1031840703c007401c1900e01c5102e07081c90103401280b01d169125600e803450304025074000401e881c1c0310510041c040709000d03900d482001550103600c5e180043d00c0b0364a140e0709040c81181050782d560301c0c10044c0603103006855042d113000c00013406500700041c8025a28131500806400fa01c6182c003070642540360ec02d2074141075203c050151411651 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 108812949 1106 108811843 108811847
    0x2070b04050a0605030a020f0a09141203090d170d05060a0603050108030306100c1505180c030a110a15080a060e090604060b010504050a0b07021002070b0a 68
    0x10104400d01c81c0b51101e141c0c00080e641141041035403515060400402842103c402d071580c0c25001c2980c2400d1a8080f05070750469096102c0c403840007010b10b04200f14003003a1070344048594030400c1282c400d030405007105e01c0035600070035902e050003101c042800c141c2d500c200000b81c4501c2e41e440c01c00903140340c40a200c0c80901103034030301080301f0341c10b16012035682e200c09480c10f0b10540003c108546d02038821420300000681c8490000c0a044911201e0300107000181c0d190700c04590045411407480000060000c03220700008c00601f0012210303196412155000441c0b01d80100f4403010200e5103802664a07585002031942d00d003801d80c03406c3e58503403040301d403a508200203942e18041400072241c00040c4982e000b98016000043c010307100e200694641c0325603400640c00421034a000140c042100019005450099408500f407140480c012a180c41c02805840300c00305d000d0000c050418 = true := by decide +kernel

theorem cover : BRFrame.Cov 108633093 108812949 := by
  have h0 := BRFrame.cov_init 108633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 108633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 108633093 ≤ n) (h2 : n < 108812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
