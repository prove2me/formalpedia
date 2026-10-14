-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1869
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:58:10.420921+00:00
-- url     : https://prove2.me/submissions/19e38c23-ab28-4240-a36a-436f0b2c0918

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 335971223 ≤ n < 336151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 335972473 1250 335971223 335971241
    0x5071112060709180b01020a0f030c1707060c030605180a0b0a08010203040210020a12080403090f081005060301020f090f0d060509031c0603021e030a21110102030405060720030f070303 81
    0xe146417564240c0c16030b03000906104156032107219070441000c203040c00d64122401003005031800ca002690b511444090340000d00c60607100e823008000044100b001241250403e00525400c240c401001c9a0040e541a0440e60301a11424010a400804401054901400b40d102d680c107a074004c0180001c61803e440c080460420038401000c82802a898030907000103003181310300c20b1085040c00704003030510943e83d000140405110100e03001c0d583c2c0c4102030780c43c20706421043c6418074000100307280d454103000301c1e80c659000c4401c250918004400300000502448284e40d408117500700c05500013030080c0a0a40b107030b0002c3c006141c9440400c0c107401c0942c21400c43d4088071380d02d00b100500050303442902002c00040789405040640d000f10011903e0030108500107081941109100c0100c0800c0841c2e2135000e4007240d440000b00318501c10918241c1c041510001d00e140c0065000400d650f04c41d184451a5402c502c1103800941c01d410380c09403d546c8080760003e40b45200040038818507416004509407 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 335973723 1250 335972473 335972519
    0x10201200403121407031706010801032a0f060207062a0602160c03050616110d0806030a0602030f06120607020d0806010c1a0406110a05071112060709 66
    0x114444011040001d205a00000308140e5500c030a100c0101c0c4240480342c0720f8a03105183d603950303c94a05000e090b550109580d071002c40070443c001155544182000d42c1241e42c08401e640785003600210300c0c074801220145243c01009110400a0460803030140c1c0c40091005401801e00e05d81422001030a100e000c4176641403406400d251201764010b800180e203d4503030041c20043c2c40b006200c1520842d040c25030009451741d06261004414800080381060242c4d548000544002e0b00d060025a02240c040e20400140d03008030080e0007182c0d0041d412698005030040031740c6c05058a0707030b482200b02d0b041a51880c500300400d00c20850700b41025a048059034200c60000c0c0f28628000c03d00940d83c1902c02c1c400c00401c800038000c1501079000310021111540d1040070040311660b00a022400c0d907070101d030142d480900f041e070a8080d4011860407103004100581e5410f19106090703e03031138420300c45031309035031b81042480007140480801481070300d0207001180d4488110b01e1912101c541145851031074014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 335974973 1250 335973723 335973761
    0x1615020606011409012105100905011a03130507180c03050a2706110703030b041a030a0b1b1b010b04050105010909050612030721080415091b060e010201 67
    0x1c028010385040e00c0301310b0b80902c1c145110003a10b441e84400b1103c048001000c403801d01c814800303070005607808041500c400034010009030b070380d4004460144007201c6049104580800c0800c00074041c03507123281000d9000301c0486402c150350301e5800301d03585c1004000390340240d40c4812040030f00d0b505000c1c00307810031141201481900d16854500c1c800d100081400c00048100301484000c20807c1d03000341e01040d10550746c40351268010b04001d80038142451415103e10720f071055002407416401508103d0102c041e0040403944420342e40c00750040c0340a0311003a00c9076410101c29082641300001450010300c0d4480e03a184280c5103017507035403d5607103800d0703107510640c103010061200d0390b40b001005041300d06004d4003080d151a560040382402400b502032142500000070000240240c176076410940380c81c118242d88001c8102c207012103440030103680040014055400750915064190400c0a05900501031074152490314140c40000050075480300c1e020a606007a007540968081c0b1600d03900d420005070a40c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 335976223 1250 335974973 335974997
    0x10b090a0b0a030e030f130f08070e0405010b0405010303030c020c0901060503130c05100e19080d0507060f09052103130224160b01090c020a06020c161502060601 71
    0x145609400d01852405081c0030074019141c91094100c1c03141e501c0400e0589540f0300781010346224650201070464400b0081a10000d401c201c03881414040f01d14801c041c2c041c282c104001d100b407070302c8040d1054809649a03001a0f01e5951240700c0c0a00a5200e51400509900e0000f40070b424407040b46802e034410000700b00100403190704042129480012100e104a6a28903032504140030316554011a820100d50f0803680b1481750464883e8070781040c121801402c80e502106489902400340c012090590080b88408094038020806020624882d100110f002c0080d00c8943d4101ca000c0101030340c0a60052203c44000c4550000c2c03d400c4041c0000564a1407034541d402012449800740c0c020f0040c601242d40c00780f040d01d0b0180404040d40170040b9141c0c5d0b800c0c120060031806070001019185680c100d000012803d000744550b024101c03544c1c007e40700038280343d01e0341c00c02500040701003000d500840652110741e0001c07010300006407601040d194121300d10b4503402490250001e20450610001030481c0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 335977473 1250 335976223 335976229
    0x1f060905161d060d090b07092c04030c060227040e0601030803040305120c07120e090f25120b040902030604080c12030a1d01270204091403070506010b09 67
    0x2625442c401030800100340031501000c00c00d280304e084a480c03000743c07800040e81c0802034404022402030402c0e41d5003500b6140c40d4901c03400803400062456182d40100b1400c1c84420300355181c610750240c0a03042445030281035881c0d1000341d0b8096682c81c2c46a1911512555020602110850104000307840070844040352586159940d1010300011b07207898000b00006082503c00c001700c42e1f00806404080e143c0e414400c1c070701c03201d54102c100111810540e4012403699140306002070581400c00808066443d240e1200100544001800345050b1a00f05c0c40400000d1b0401c890a200d85001d980e20f490003200740c10040d408a41151030300d5803113030303050000c2000903903000555580c100d80c000d40322580d0352840c20380c1c03140307081507a2140c10300180002c4200308218820b5400301940d40a580001150311390040d90b41400c83f052414209070070750b150300804d2680f88115200001051002c6d0000810a800761641150040314070060082a80009024070030080240b01c074070300404c1c10440da68244160a400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 335978723 1250 335977473 335977487
    0x130504020103142a280f08100e10090c0921020303070201050d020c0a1a0702011407030902030708060a091a0c0f07111914010905030705121f06090516 66
    0x40c281c0303e2102c1901101c0104840c01117850a00094000043d00c9402501503240e802d01444440040340010701600c1c4081c1c041c1d01018031071007001650024841c10448015030b0004007420400805010000105d480126446007134500c401ca03842d0095024a0a40c214002140b0002655000301c2c8013511440140c4000003642c0074580c0c2420015162803108030310100034040c2c0300c4050264466010030300d0034003d83c0d1014450b14001c410309020b642c0c0d1a12000d07030981e5030001e029004004c19000150301c3c14820782c444080a0301c010281d50a407a03403a0159851b200040d110341e40d000b61354030680010040306102d99a455440c59421002503d0706060900d15409900400502148001003080c20400130014a841d004001804c070061918081e10104803841140501781d041500348540c4a43c40d80507040c0340040b154000e000b80401401d03c01072250400784400c02c03411034400d00241c2640c5880418009010104a00000400b14604595030702038520141c5040c00104032a40340840351503000b00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 335979973 1250 335978723 335978761
    0x3070501090e010e06060c071206110a091a070b090610081603031b050d020c010206010503010905030d0c110d052706030a05040804080f0c03010501060e280513050402010314 76
    0x8130120107607032903c000c0b89030f0344500501c142050003540e00205220705040c0900c80b1103801901c3c2000400d50780700d07100f12648120001300c0041040441d08100100d02040c090b101e00588010550501da020f6440c00e41c0c000d019209405550001403c01031140012018600208095401010b400c0c1120441405400441c0030150820070302c001440503004206c0905c5010070380c814100c89001e80340c0340d0002d41701d81d500b245060050003039100003d01803074140070f600400c4d908940a145402e0b1a20842030040004000340c00c1807007001d543e1060f03800d1081c09214102880c5860302e540d03501c00040003010072130305c01c80406620481864805030796250341d825a0760007084528000341c0b41e02c4a05081c0007a0280d40e00c40001031241e403403010701d080340104803c10b400798164002d0050b6621b401050700c40719051004d85800165866416800140c00e00c040c903468000151001100b1307440390041034034000c080f694682540e45a10510046582c1849030300b0515044030308400300380c03c090710b010110b05040c0c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 335981223 1250 335979973 335979989
    0x108071707022a15130512010f1d0609010203100303050903210405030609010c05160c1a04180e03160204060504060e010f06020c0102030909191a03070501090e01 71
    0x180000c980a0081224802e480c05118081d501103622400003825521141c500f02c0c040c50a0718041a40300c8504030541d60901c0340614118015420042400002400d02c182c4291541d2180e130303001900e510b644105020106e85541079030000001d00d007075920703020024048190366881002044005200d80c00500203407907142c500a40d941004000082c41c1400b40013360700d01c43d42c0d0b410858035001e1901d00038011503100750141c1d03955071b549a807a0360880b00a80d00b210003048041001c0d00300710101c4200c0c4a9151710800b5103064480d145c05803100720380031803040300d050b2000010f0140040109804a0855440c82050902162845020303030b43c1c1344c3c094800314940706048140c00c3c1d800c40d81c4542250002d4030b0080d20030011140c0e5080802c1c00c0d00b00070702c9142650081d402010030924804290101c41443c1a0019442e0200b10014802c4000d0300500801012040409000e03a03090305001e0300d5124200320034455610150001014202222a48218140302c1e40340803c0082c1c46003030054504441c091 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 335982473 1250 335981223 335981267
    0x1103030f04120c061104050a09020f0711031f090605090a030e011808030d0221041a070302090d050a0c0f0608010e0a0603021002010905210712030f020414030606010807 74
    0x1801c0a8030034003d604070040c080c505000c22000440389000c0600100d038000c450008070159100d4644041388122070f40415545000c21808010450405004842c040f014044070443c491425202040d07207801c6080f1301813035480f90148400e104890181e00c1e0811840406429036074000d540c042c045880d91100f45e03040c002421170354100c01c030705090b00d94010400351080d603a0f1010f80030700b0840250710550005590080ca90100c05900c000101624802d0b17a01807080310781201000406818418000c0c4800f082640800c143c0c0c455840309000800020700c56401009011070030720f0040384d4155181c0010b00c291a4441c010041164440100c50445250710354100258440c86c221001178011038002030342241e03444680b03280865055000b011b10b58001c1c81030340c2c00916616804082c401540300d81c8030f68540d0074411040070441500000103002d0309424002001d6411044d00e400340c1e0000e6100caa00207070f06845c0c4040c141010300816901600034a050002498171200182220b5080884801840c0c03074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 335983723 1250 335982473 335982503
    0x120f1014010f121d0303013f0804050607030314060402190c02190b0307180302152d18062811011103070e010e0f01140f0313031103030f04 61
    0x5039078400b40440c004c20b410584803a48400c10710b40c1d281c1c820720500754425101c6410410908041089414801861988254000312000700e0f07090407000e00f00c10b03101100200400607659079030380e0041009601c66103012036240c0362441000201540240158015401000501d29241086407100304894a0742001d40e41c180d80c6001140f00b6503e04182207400b802c40c0c00b000300702c00300840061482900340307581c0e08000180441201545111920009400081650101c4407580058000c0c01941e10f0f00c40c565003000800c1c0f40f400c861089020385244515034002a035240e550301403440340d540c0c1042900c6140c500f440c040342c14008000e051410545103024500300002c0c2c18401c0e0034282010300c0ba440240010b0701c0301c250821041e0b00a43c0c031030300480d2407141c5801c0c4079401003503140143d46009045a05941d10800103417407400048810140c038040800040d0040d544003409980a10740c0c1d500c00001450140c90040c01c07500e0070000d0040b1950040c000c2103410383c80c00c08419403040d8800c4d0001e141002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 335984973 1250 335983723 335983757
    0x6061602040203011214071a0703021006090e070803041a0702030f0609072d0b031005030a080306090f0103050703060c051c090312020403030203030c070503120f1014010f 75
    0x5490000e5000e0300000c00042c6400c40c0c4031606031024040e00411000300ea0003820b1594451a41c0300b0040541000b902c0c40c80c00d05016005045c406020b4010703a0110090f10b01400211906900b1030a0355650b00d0341d4502c0b0301c0008000c004054100c0f00000e500e4107042040c03284a4421001e03101080d040700007124000c5440c184030130f042030465107084070f00500340f0003551519001580030b00c040b600c600b0040082c091090522030404c0d00d0f000240481134900304403a1071240d40c030060034850804501d010004060700d0402035682045d00034680365841e41000d00c2005407a0201500300e044d0000b16000620108002040040450740c8c000e0000507402a5a5001d81d81c5020b0600280901c10360008183e00c0e2000d036030018108144280c0e250104e000100a1110403030040c0c0c000513006034020f100041e96551300c48000c0170390354001c000301e90070b0048022400400c0030044841700c0410804005014400c442c403020a001750620703a403030401e8040c00000082c40d8203902d5484908000e111809480314003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 335986223 1250 335984973 335985007
    0x110d051812031603080118110a0f110304090f110a1407030309060608031c1503020d14010c090602010f020712051606021801021c0c140f030d050910050405060606 71
    0x20002c000350354500300c3c41e080c06071500400748201ca41444040c0c51202e0280c0700d40c8214401c501a000b4403906001380c0c00001c5500c0c0d0360701001c0b101072041031001c00c40c5143c0100054402003665070303804183c188101e40100103551842809000d488028820380c540c658100c4405425001320300f40d40d9445101a040841c050003c0c0540a0021480c11401241f0741102000802c40d40300b041e400b00b0042c10008100c001151520941003c4c901e440d540d0a00051410410002e6910f024900c03240c07990001c0b003201402c40340151750102c04120040300030040280c081c00b030701071800d920b18011030501d07245443d003000e0743c03801c150920f0400800080c400c1d02100712100110400342c018000319128414982c05544012801140d240503200300444013903007441c4101c0b0300920070300da5541c14100207a00e0361001082203c0100e000300314003500002e207404100030405000c1d4041002c43c042403a00740541d44504001d80c0b031000403806410041080003161380015980e030451404d41b82d203640c41445281100c10f030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 335987473 1250 335986223 335986237
    0x209090712030914010c08030a0e01091406060a17070e13050714040b0a030c1a070b0702010b01082d1306050109090b0f131211010c110d05181203 64
    0x201418007041060661108920b4242c0d402425004a01c00c9524015603450544180040020b507040000910030015600b12400315400c07074001080c0c44105a582d00d11706401400c08440f0f90b488402040240c4c80d08602e00c0005180704003221082c2d491888640d5161009406807004070b48883d03005c50b044603808050640c0d0b207500305e41660701d42511100d641c03c10000c0507031101e100d603003040075521141c9080304a01d0220f903481103203020702626018501c1402030700b03a01c01c120007541c1440500041a1403000381c0d80300710800e078000644d45143c680054456032010b8050340c0041285130f0255150820061580380c01001000c1c00c85481e9200665000925540080103041c1400c0c500000782110301904480012445003184a0040d0755000604000b02c100f242e0146440c0c0300c1b0410100403408428010300031400500e02a540000300900c0d140c2524204004100010b00008515148040c00d0001c0311400c0400c4c98881d10b051010072400000d95024481148108003d00441e0001001001100c0300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 335988723 1250 335987473 335987489
    0xd020423010504180902010e100305010e0a0b0f12010209060d020403151112190207080415110607140909090a050c0a0f050f032b0e01020a030c0b1513230c0702090907 73
    0x6140f85160f4020700bd0b240078031a05000103400790208440d040c05008481d524400507000c218040c4900080003030003088407070550136a56007041800c0c91a140c0314014900300216040141c0d07943c2c510329140488c0203106c031842034120720704403600204130300c042c1c12101180c0e24200150896110000c0d000c61101c080e40f06010842d20000d80c0404010240340030b0422615444003040c1c82920303c1d035090310b40c80649840e0520941081c3e001448280c041c0400c500102441d81c0c4281c201510325021a01c81c02c802c0e0348540241e40f00d1800c1c401000002c00c4058212a403da400c0004a403400401e00d42c005168000c0600c02e210540042960b80c40030005002103d0102c3c3e50803031941184a42d401030b5100e10720107180003883c5401c0c80030155000245400603182d155403240e04684258482402010015202c0750821080c4103000c15195a45401c2407070300d1660200005246044c146040c4611440e06036080d455005001002443d0a24100740c9188a806864404103039130b50076401030920f03070240c02c4508 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 335989973 1250 335988723 335988739
    0x3050304060f06270608070302060a140405060708030603100b031b030a0609110a0b040602060612100e0723030307060c09080d020d0909050f1b0d020423010504180902010e 75
    0x10a4514008410480e420620080001705d4803101c095031075266030f0001a421403030800c14203210340d220340c07507007202074607ca10a5401c00d0b440c1e000140345235121040c1604c41d480040180003803890300303006890646416210804c11132080c0c0e400319469280240b07421080082c26840c0e8a05510140080304840d94040c00403c0703000b51501d0700e6180a004030302114000c01c60a00c01040400b45801100c003590b4154000341602d94a1000f0803148000446600b80c503805040c189100e51455401000f400038108405002120306003001c83d503a15185024030300b036904000034a204543c80c0407080b07811403a00490b0118246401110944940c8817640c080091071060001c3d03182d8582e4041400a8100055921000840d42c0c80321140c0641d407094401444003201840850021407001d41c0e040c645441844107c0d041407106000f8100302c0c6c202e607000030302d10b4003410001c110000300300c00d5000b40710009087c03003030505080c900f01350012444074201587d8280e81300c0b50382e02036a00404802d65403100040501c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 335991223 1250 335989973 335990009
    0x721020316060e160f0e0708071211070b100602010506040b0603010b03060a180e06250f030f0609020408010c0503070504060516060501060e03010f0b01020c2e0c0311010903050304060f06 82
    0x910385c40c44070710034140d000402c0004a10303040d00c0707100098010300081d5100511011082003800040c42094848a0542c104216032000150400340c402c0c0f0584401000c6e0301e50902c0d150300603082d524001c2c640da22842c50f210500f43c0541c2d9142c192415500d442904686983d40c0704080380b4854581d402001c0d405501d8503000b598030580740c0000c8070312084601598807640b190841703040c42e5103c5080c0803000707255500410040d1342c0301d1020a44ae08605181c00310342c00d00352403d01d908031609070300840d0b09150002014004036809000310803145440d1b01e401e900d0740ca0504001041b44c040c501a400401000081094829014441c5400080d40121b0b00700865603466602a14025425144070301950a00c4611401d4555511a0356103074a01a006040110303840f804000380d26a1095035254150200c400d802c00c000e6000c040100046603948990401087c0d03400c02902d980d032a0018441107a05042d28603001075481800e0780d80140e40860080b5100891032912806060641c1142014070004000e01c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 335992473 1250 335991223 335991239
    0x40f090b010b040f093909050f0904030e0d080a0906110604031403040809090a0c0e03070305030405060c0102041d0603151003020409030c1505060f0306011d0612030721020316060e16 80
    0x80500e0158032681c201c288d4603414080f21001140f00954001100000100800d0140801c0188004001c0c05584001105ea441c842250005410400082c603414004d01c142a00804009a0b051801d0000c20311491305a03001080e441c908030703021840d5a0301001280403c42500300742c8111000007030001500d07103007082625004101e19030180300020301c1401d004500e03082c046a8007040e0b80e0001c001d10700d841c3c00d203c1407142c40d9014500c12000d642d03003044001010356000c1d0303c4c1140001b50f20411561030404808142c074160245208017110b85003d0309005c41e518501c03080004490b41901c000c02d428000d0704090300d103c54461400750450b241c00c2c0652400307160951005d4461802181c07850200c200220038503607644400d0089074a01c41d042c170104210102c036144059846103004040607148a4058030050442c1c0002e0b01c219041003003482e820034281131446401182500794070081d81041c95102c0030701c100c42e83d10314000c2c052694805044010303110030b002e90042c1c0c1164a0f000488a9520600 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 335993723 1250 335992473 335992571
    0x10303052a060c0a09170c03010c050315010c0f120903020406060908120306040b1e0f040902010c1b0801111902030301060923040f090b010b040f09 65
    0x79484064120000350500414100d40c20040c02000c5070041c1010f0340d5054031200960312025881043c004003080c002150b800243c80b031407000c80d011007c0e15000b10342d0003d060031744075255810000e100040c4104144600c00312441e001c104801d18250100e200a4205039642001425002c1c00c4040004140d160164002415804a0303109642c07c000c102d6a54108503440000c500070758030640c2284e18032141c01200740d00a19005107000340005011a194800946150700506440001031a8581c0e13101c124a40303010142504102600c00b401a002a540001c1c106002150018440c1c1c7c62410302e24040c0c0d068200542c042c0035044000c02c045003110000b050103401c4031a8110a01802d000409165072001c07003039074101c54603a03c850045074108101403800481a0356124103007512402d5610155aaa0040000240200c100060361509508044050303200581044003080300802c0200103c0a035074807103508a50a0308400079001154034407603074403c078038201c495031a0070720302d00d031410310a00d4840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 335994973 1250 335993723 335993737
    0xb161b05010c020c011409010305090f0601060f082508150406080c400908070605010e0f0402130c110d111509070302010302220305030a030c0516031b05030301030305 73
    0xc84114100a5004491b580310780c00c003200080300c05100d00103565001c0c0e000950404040001e40315005e03006000d007440c1810980c0110000786600842003010340c0c108491541000400346804002c04405000e00004a0920f030b8030800c0154001c000b441e500700d03e042e46120004002c10520400d582c9042866441a0004502c0d05c10969032003c0e840c0c1489031040c280e2850b02600304109035a1040c04600842201540160107040c1c031b900d100070020b02154010090988900c80000d031a50500b018411070020090110b140c080340c40060001598400072690040804c00c000800c000200400c100c130f2501c03200c04016200e00c81c500f0000c441d650824800b40503181d2200486401d200c20f90f22483c0419070640d000c0230b464100a0307003030015510940040c48031100034001025404840d00d420145045140e01c08c1c1c07682d403c0807401900455041c000d04195070031621f49141095074400f520315000820140c01028000c2d0080460001421410441c03022500309080d02d0312503039242005409a4080a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 335996223 1250 335994973 335994977
    0x203060414040507060513080f0723180a0207051005090607080f0403050d2703020f011512111005090102070b040303020a11010324030614040b161b05010c 68
    0x31110321a507074403010611440e04a001004030750b2a2507025aa540d22a15510010044d15078020603000010003402a44191032402001e50901c0c041041501c99041012109910010552a41aa515048a1142001034040040140e00e0304402c41c002441903540040041c010400c070031050b03c1d100d500543c0b1070342c40b034415203c040e50340c0300702101d00590484070341030000c0c031502c0800d0200b4400c201070851045004000105062035401282c0000101d00c5202c00340300c070cd00c0d200c4081517414400b201010803110000c0c0540051800528441e030018010386e0402540704a0300c0d003e00c522420682265403000e04044080c000e0000028016403150140c036002d4070501d180000d40c02000002c840440b90140d014004001159540c0c84200700820074550401d034807058200c0c00950300c5100486807006410403500072900d10b1030701c4030a0b1740a003045c0726000110304040001007550780005540c0b2604c40c514001700d5001c0414140c580d560045418550040201c81c290100541544000c011100030f03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 335997473 1250 335996223 335996231
    0xf120f05100f031a0402030a0f0b040201020d0e06071b0f0b0c0706020703020127080d05070605090102030601021203040804230f0d03050a0c140312070f02010902061806091302030604 80
    0x51205602c1c0607440d03c402001400207085105680040c544610740252000b400e403944e101443c0c48402c8580352070802a1503552070141400111360701005000351052060403c1405e104046c030015503a07001e8030310044c140b54501c01180c0232002a120f040c0c0003602e03160700d86a83d2141c9500902d020b503008411718080610485401007851400042e0341c1c800c40c1e40c141c0d510007115180b00c40c5d031100c034607000040d507504d510103140128203100c06002d01038082c111580c135651141054103140007650f101401140859104005005e200c0e60b000c2518426000d000031307400c5c0e8070b817240d01d090031280c03089038850340005640c4044010380350000d0040d0b0300380c080d040318280001c5022008110400820450003004a04104580b400e80d83c014a040b00c02d09000e4010380c0720f00c00004024074155803080f000d010150300c8000401050980140c104490b40c0d000d88002c01000941f0360101d0010311552000e01d903030180501e2410580d6403050101c4101990103070030000c90007500b40c03041c00039400a454081c4680e0034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 335998723 1250 335997473 335997479
    0x20610060e01180605092b0602070206090a0603151d010605071412070204290f04020f0c060405011506171018091e1e031107060207050f060a02030a0f120f0510 70
    0x14078040b54030b02d282d0501d80e01861981d48e070b40e080025400044122b030003034021711501d01ca40c0c5e03a90b000d52000b09003549000c94020401800180b903000303d82c1200d0f22141404449113440d8105848590640c2d03110705040e42d903207203c0e051881141c200c98948201c90b11448440300c82845800000d084028400e950611035410b05401c880130250120320f001007013080e0303d01844c1c403520302000403004504000d03100601d450990b054500207503000d2407400603154400c0742400208007091207a4081c0400c0b030710749507610300c1c1000d0f40248507400b03c00e29015540c1954002c10461b81b5a00c410030003c190a5140121003000c01080901502d508101601e011203569021042d40040410751032643e035112040c55450b649100c003158400182c1282501080f9010900141c0d82008111200c0034240c170381c0040065030314042c01c01100e403000c0e2954600560782480845070064001080d210741c0c10752801c0070062000c0300f544c2182d10580c007184501030b0900b072146c44446503001d98092401880c4640c00c0c110702c152 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 335999973 1250 335998723 335998759
    0xb0d060b0405030606040c121103040c05011b0609060b120a0c150f03150509091e03091c0f0501020301060f1b0809060f0918070807020610060e0118060509 68
    0x203076101c2e5981540180000905a19155000340d01410f01420020340300c00031484032500b1142c401c01d100002c00400001d102c14880f80800c420010038003440d1032141d0b000e581d10b80c03104200c60407030000c100f90b4071880b050b0308002081d0030001d020725001d0400402400c11b1044c0a50700e00714030b00705540710280240040317025420310383c41121040e1962203280c401c40c4604c900320010320070401d00e149a500502c8000c6810380d122080709000d0074041c4002c0c0b400005210700078200c2c0c10303900440049a401040701103020348800c0031828241c0b01d1a0400b5003000464100307000b600328080c4008020354800400818041c2d0400c2e11001c044c2116034034085280c0091030f0b00159108060030140980d0f006005100192500070b0040580b18500360310603050550004c04502d01122441c02e000a00b01c02d0401c011a02c0e80c0500700c19400a40c51004022a040c4454180d9081c260b07030051388100014449220306607409600c01d0000c020106410b4240c2c1a6640e1000342030760031440b00b1501c50301d0166010601c4034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336001223 1250 335999973 335999977
    0x3240904050606060c070b07061401060306051e03010f0c050c0111070503120c04030507080106030215070c09020a0e0d0506060a061706010e15030f040b0109090c09020a050c070b0d060b 81
    0x307074484002c064544443e81000720541101003044445d01c5030140c0420301c1c0814501500070244507001c0401d2070601440b0822103100305170414410585041f00402003540c0b1030010148600c1e0030820143e40c80340d0750000c6409492455840b030041e50514020401e261750100040007460300240081003030440b00d0040b403281e0300c140c03400600203520030b00c0644110795004101035000b04400411030701e05a030720303541c2030700f441c01a40c059116a5942d840400a47c20011442c1c0100b40c055a005494164299200c4c80d090300240245102c035540803403070042142c050707803840b07442c10f900405002011001d40f86c2956619022a8001c3c0940456540003401030b01600340d1411454070401f5078050340e600c0c0d0300111075400444540d594071514071202081c240100000a6000e100c18010155591500d0704003256982c0041e4402c00201d482d000c0035001140c8448804015a0080907015a43e05e5091100b151030b405442c82100b21030064444c00602c03075484000501980407190310600801e80d84400c01c901c58 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336002473 1250 336001223 336001231
    0xd14011e06140c01090c06050d110301060c060b0303040b120a0f1e0e03070b04030f0e060906090105160c0e010602010b0102150c0c01142e080c06070606080102032409 73
    0x8205440851482500740c02d0290030142e0714800001124040750312503100b05112030b032140c400f20300c00050203d0340015030300810183d04111000c0038074551400c40c00501546494030043c15450740d0303c03001d00c20360703038180b080b2401403440d90500e03900e40c81010203807000641c1c251140c41d80701d890300d510200e00c2211402118160740701c06c00030006a034000513000001d0314142581605500007000b282000946050401c0e00841c025901d05100b90306a42018000c070030f071090b400703114034428456a0107668990088a140b42c070286015621680340580100c0803281588000340b40325003507c4080340540d480000c042c100c88150b0700038000180e070301b001aa01ea5400040d0804d1810b005400103600740074810090540442c1e000000132110402107402c200400250342c0800e40745110510b00c8202468002d008a10107800740714010198640400301c2c0c2d50780860f000c55800303004003141c1e1000f8028541d010174002c1045d58001e41d520303d040007200716862945569401e495010103240e15883c00d0007070006205d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336003723 1250 336002473 336002477
    0x10509010f0314030d050c1b2a0301020904091208010b0306090103030c020f1f090509010b03180a0c03060501093206031014010312021207060b0103020d14011e06 71
    0x207082d0540d2225005021079440e0821103102c204901850782082d8403803184a1445a91440e4845140080000c0310303083d01e8405d4401ca03030084400c140d018006580d41c0c0c140c000786040d030a8011034a40d000ca4064010b04801c0c2d40c8c490324201841c82404201440d0301031a03142595110faa5a0702c4100c180901d00055a0098104400e00014070029000300780c0713008070030b00061041411025210024a01800c404580c0d9035030360481c4404140c01d46c101c0220806000e04403402503096040000802003800f000b80092070034040c840e801e280c0324105006c0c0396070542c2c00c1500c90071510b40b0390a10038080c1c5404e10444241070b18000462581482e01c0d0003a80803100c520302c0040074282000b200c1c10034007130080c181c2d45d450300806030100c0303580302248203c698003003800d40503c41540c0b56080428034040c00c03d007413034159003001c0401c69030400a4003c6600f0582d102600040c03491300040120001c0c01104140700110303240c400d07951a0001841c640701e0484007408041c40c240140c007141c4040b030303c51501c51980 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336004973 1250 336003723 336003749
    0xb01170a170a0e041503061b021b010c08030408120c0c0d0f1b05100b04090f0b04080d020307030e0706020d090b0c0102090616060608010605060f0c0c030106090c0801050901 76
    0x201c0d1208100030308402d089031600501c944074000c00541100c05640d078440c007034081140b003041080b00d58054001402c07031400c3c0542420402c02c802035115101d181c1d400d207a5031582203400c0031603806810410364064200300501c0d20b91a003031408200a611490081c0034040540c400074a00c405a5811500d5290449015000e0308000403401e130342c10007020304203800788200320312840341c00484914088005c90240e00103000e4440312078003040032650240a030714000d40c100454100031800f00c9405440d21030f13001070a440e83d80d0f52420041e080b401081d64035408980004140004668950051501c80285505940c4415514039040e60341e860a40140720100d40c140f5020130080c01030001602ca000c200c2000580781c081070b440050b4443d071040b002c03a00501a000c81c3c0c407041c01031620507040502000c0008200c0350781054001f881a01031001184070589001071540c50416052101400b44d200240090050356102d03201040070b011084405000a90107400000d61413030405034050407100c071140402 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336006223 1250 336004973 336005003
    0xf0a080f01050604270e100b04110702030c10020c0907030e15150418120536120a051c0f080f18160f0314010c1e0c050a0b01170a 57
    0x74043c92040101d01440c5d5660060303598034940c2400000703c01c04151f44001046070403102008210350541d0050009038509102010043e18000351900401e80100c07035034040340c100740710101e180c0b400003188150081652000c0c048815010380286041040c034070284c0d075600c84101d20040058070100ea60400c43d0741461070880b441e0030207500202c910008504180d0b1081c40704c5d181e21001c02050074a1000040300000d07444494410803c0207265500c0c02910680e002405022a08183d900c40c1f03045842219141203840c07995408100c140c881a0b03000741501c088217840c0c4e40000407003000c6200f410205002d50310b401482440f42104e103114492400500c24180c8076000d00c55052900014418901c1c82603081c10b9a5626414580f4001400b0109204c1c403424110b1070141c4918100c1440210280c0c18803248240f4590005d400300070000c0c80314090b03140c981d90102e0403110304018200c00b50050151203902802d1000e13680b4210f049e15180c0300c4440103002c400300c0300d40c0e0700c0c810004080c0000280300888 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336007473 1250 336006223 336006269
    0x40e061b0f130905060d081e09030d030f051509130c1d06040606030204030203060a200d1b090e0406020a0e0901140112022b020f0a080f01050604 64
    0x6090926100c15010303003060111841d1603581c1d4840c0c40c60751000041401c081051900c2800b40079802039058601403800d11042e5602c6035035005911000700348444500100949080c00700c1524035100005013190403c26903203074040e00603c40110f00200c81400d2000050100450304a4286811000744c48400199941c02c0c0555005403a9502122805600b250000d420940071030000d44a41404160741c4950800708104002c441140c0e001d1818107006100400140c0d901146980d40500d05180c0495113001c50002002c0c0e50300a98000a5941e0b0041f40131843e5040c240e000c5550024049070004007c1c20038403050760310307041e248079401e002c91582000800080a0350040c01c114590750500700c1c950150240080d0107001c4c260414403100516400c05402907a010441d070704502c448a208500c3e10b880c549440c3e824000c280d444180c0300c56503424207256091954100c8080c007022111417070701d80200660003803900605880d4180240c021f080041407d280c5401120105c510030b00c24820050145254 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336008723 1250 336007473 336007501
    0x601091203110a05010903090602190c0909050114010b090a0b0c0304052107060809100e0c1e03010203040609020a0902180d030e0a0905100e2a04030813050906040e06 73
    0x30850300f4010301100c80001031090098205040c401c0e26006643ca0404030000e241200c0011080401a020304c40200403034100d080c0c0c00191400488041074000c02410140e02402041400d01481040301d000043c541c070450024100b1140d0032a20000c00c26503032903043c0c003207016045581d01760341c00400c010002442d04180480340e10b81088054000325162050312414600f60b039002402040380041044415601407054241d01600c040341000840c2d044980785560302d190800a50080d20403800c0d26940d000c45505011500f60014000e642e80d241a00e8000040e0092082c102e005181104000c160303004140260b03071381e4203442c5803100901400301003040417400038880f00380c0c28421a9025400360340c9842c1011400352000880c045075500f00035040c0d075114485075221484098a1038180400003c0d03008a03480e0041a00310201c05812000c6400346442c4100d0303000500c1d145000602c014040f041c0c903100d20840d4422114950150b5921040c4420b035145240e480750150800000982c0c0300a502d40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336009973 1250 336008723 336008747
    0x3030906090103021b0703030804030e01080403020703032f330a020304140a03020f07120c05040e030412121b03050d110c0a11030c060901230d020d050a050601091203 73
    0x104454040d00b036485d060900b521904140d0009031020b08100500d5007115241c01004428a0310040a1034030780c40c000d407200321034000203041000072184040c040c0e42c00810120400c40c2d0324a2800c402c021000c880f03985512038200291080c0d012520310414000141d000501503000003482c07061130b82e8090601c0001e50000700200c0d001c801074180004803000801540c01e032035200350018070103040003140040c98604c5651101c41160700c010f2040f000101c0c01c2c4d40001c21113030240c9012440544950503542140543d402443e80c4841a540400502411300c08855240515842d00740c1c2d5002001101c03a10060320b000007401148080051850841c40c1e640819010444030080c2030904044040312420402085000e0310902d03804000000319180c24840700b0007102081f203c8620f4180c1c00d100180c40c105801c2013124401145081034174010240004607010300e8141401150380304c8040c18508014242541c14014440c64040060301a5008820001c20f40d90382002491030010507a400310b4031240009 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336011223 1250 336009973 336009997
    0xc0402031009050705120412140301080c0103050c0903060c031f0e041e02300a030818010603120305071101060f0b07051005180f0d0f080c130e0105040b0303090609010302 75
    0x1b6107803c8140c903000041c091481140c40707484100702c4500c01001c088680710500e200b003808200420500800055407000e4000c28240401c0c0703540d07602001c89460041880305034060080030f007004100e00029000b503200b10001140c500c0110b401820110311102c290043c0d216621a40b000301b00415019241b41c0f4803802000107180e9411580d030302040b44100c024001d0002c41c0c40c1401001601119038070b10314690b0041c0b00051003c1003403a20024038201015001407014203003002041b0202000f07421003005180c020040900c0c030400b000c1d0003030041200302c800328005183c1c4218018404ca0602070881111480f003d040c0005040003a0250103900654084038580b03d4110320900d0b40031180901c600c1480411040c01d1002d4000205030b040404014403502603402400e4020090340c1c10915200240501345094481583d47c091502e40034854241441e40314100d0307240000f140c0100c1c0b600c43d030580d142520240003d105150a1580e0790007079401c42c550001d0180841d42241d4425030160010203005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336012473 1250 336011223 336011227
    0xc060108032208073c08010c0302091302090a030f051f090c05041a04050907050a0506041a0306060c0a060f0c05070b0c0a020c0a060305240d0f08091207080c0402031009050705 77
    0x2021001e0000040e0340d0003003c90500d0407504200c045070a10030520020403e041c20340c80c242f158000200864106601c1c0303900c20f54003041c03190850326011020005940e01c003405410660207403c02c10b0f03170350241404103100755010400c12203e112043c06441d03074481c2c2c4032100d41d040710700b05000c2002800003c00c42e506000f2071070480100680e22406075078010110701010300b00080c2803a040c44007001581c1c02c60350240c0345c1000204100c0001040032040001c0160042e9100d4454800013007083c4149040440e89100382520036090080b00d0788103d269904000c02000448018441039645006180b0b0103813030341040c840000c1ea8040d107980141801d442e02d2068880906003030002a40741c806a410110010769035500304a0141d400c5489503c881345098981e4096043c118005042c3c80c1e601c03007004261040e074030500001c0007a035000342c46038042c0050240020044409140f5518041071054a103103204424124410b41000e00c03c5901400f99081400d00d090704090030708014106c0540076408000b01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336013723 1250 336012473 336012539
    0x6030102090d03110d0809031603120207031206140d03081f030507380913061401020c0402070309031b0902210a11041a0c06010803220807 61
    0x30310411494070b2842600d40408031200140e00b6441d11560301d8180e004d00403a14140540000b0010a458049020381071805101e007403881c1c1180c02014038098a40f005d030011510800300354002d842e00b40d1100382e14004010080d520303840d4220f81d15011040b030f500580040c540d03c000c28403c41140ea4481e5212100e251414800210008914910b60003580e00390030842c020701802c22240690342c0418401c98891601004c000180e50070b91881100d0030043c8030001602c0005625030000d051f6459842030002c02605a4480c104000007a03186480341c014083d60807140303014a054800c3d034203403d0701a40e030251030303a0542e611f40000c0700d01600030900d5485030750070005184005000030100c0c01c09003282007841040d03000081d141d2440c080c064680709410201c900c941038880784190703001c84031440100c920311440c104040a441c0305640048002e8058100003003200701700040100900c4e4450314000030621915000c481a562160041ca0a00d80000c10100400001d107581c0c800110520a0003e0b94410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336014973 1250 336013723 336013729
    0x3011a07140102030402030d1e2d020c01121a0409050316050c01090503190305090a18020403050c1f140c162105120f1b0a0c050a08060403080603010209 67
    0x1001c1c0208003140c1d000420041181003d2021401880c4c0c2414440d010b01c030282c0c60003844113103001001080100b4100d80003c90f4800840e28004005451042c2141c1d03012aa0001e40f1031320b030710720054042340122500340c021f940c3c01e02c2108210342c8030b10b0710040200002d01c10480640500c480c10b4400d840103208400c04c007130008400d0000745210300000c1100c80300c8600050301c1c0072003a602c418882d803c0442407158400d8030329003211940d589450b00c240e840480900046070103816801c040020030b800c400203c90210503600800640e80154202c40480d02058100829107107801c1200b41d40c4040d4510070184035008003100400303c0c8000401d181803602401c4a680b8220650503101c0310000030f83c9007002401e000a00f001d085c85603c41201c15210016103d0036914903120380b1494070303507200140980070094404142c0c0d031041110140f901d0481030981940390b07142ca81c554250760641a81500141c2c0707107080064281100c00c40c00181c603241d6140c0d1400c0e100e00c803008000540654003002442c1040e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336016223 1250 336014973 336014993
    0x41b030210030f18050d11070b070c2112080606041d0f060f06180a08030c03031005010c0308040b06130518010e010501050901050d0302010e03030f15041103011a07 72
    0x1050b90380005202044001c014181c8441e0070804d80300c407a240890a001c25404100200300b0303005402c017100d000c02e01c103000d107180810075440a1142540407a90104104040c040c460803900c46824014501d0800d220007a0b840d10344e881c00034146000400c0c0344506900940c1c1440c3e210400a0800c0d0803c0c0c1d9a2518840c4040030000c20b0410003a00420001070340c90180c0b036240c02002c00d51b841c100d5240c0b00000302e00140301c1d214801203000700003014039455580325071400c2e01038004c40081c1ca807104201c40a559a0390000da5510001841450010030740f9407164080403d825050355801c12141c44a071034102d8a070300090801c4e0b802c48815840100b0007a4980035039030103110140c8139140c002803000071041c2102da6062021075a40d0401004120540d00d070a541d60640e4400c8a540c4803054092034241e0041c40c3c4108082c0302c81c000801008501c0020642d0103100307615499002c03407071881160400c002c562546062641c0b060040c0014400100c0d8804001c05403011908807900c1c2101549a2070310076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336017473 1250 336016223 336016249
    0xc09070311072a05090c13080a0b0106020d1403010902030a020c1203010609050607020a27050a0b1c031706011b080304060b060307140d0b041b0206010b0c06041b0302 73
    0x180e1440d211421030310300c100441c2998881440c2140c00f0a4180300002e0440745010f04469060b880c003003000004040c1458107c401080e61800300e580c580054075060910300c1c001d02c10440540940c0c6440202c00c0c0c000c0c400050b007007400c016560320310307802c12a00070000e410103080003000030740c20310000045a0080288081400054081940301d40c90280d008004508a4000602034407090003a01d005840302103a08055034104103451820550555001c80f0794001303104144011802c0209200208041c2d41c4441c51a42041e1403001103011300f01c0060480e0842c1900040005062103500300329002042005d5070402c01c140b41101e481e901c0c0000e20028402400d4088e1440c0b41d001040c00b00301303c1c4620420010480c11343e00c3c0c80c01c618021601508071211942c040e100b540d070004400440c40310582c000d8003c0c21004104100e908000c5040d200c281c0f40808000004d440341c2d000100e200d41d1b008055900c1c807d40d0f1802050141e48542d591301e00500c421804504013900940084010b0340c1d039011913180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336018723 1250 336017473 336017483
    0x309080d0f0c0c020d021314101a0705061b041205060105040b0102120d020a030605040e10050c0405150714060903070507050901030b060108040c0320040e0f0c0907031107 75
    0x7103508500803140c00c558102c51260700b4011880d0100006032101c810f5131040540440d840040d076854403a15102803d150f0f481c0c00c90310441d000400c150a60310602c4002038958480402e4400042a032810540380302e00c580240495101d0070001d40152084420154038820301c411070340c1010760701d0225003000140fa01c011607017a00b0480042c040e9003003902c15459480424401020000d1440840e41000c0c0b1803a0704a02d03403281c0010341c0c00340031030082e00000020400a0f008200704000041840c0d150f0601024468241303061101050490301003009480940b0001031040c040410b109052041e01e0740484000c4481510a0209001d801000e0251070720455241028550f90b501c140340a80c01e00d11281c104500c2a0103002c010710200d0b40c51607841d50301450030b00b024840b1b500c403820030070010340480d8001461080d2100042200d41000780f244000307040b00390341c14040c1411040340c4d141c58500e00c4840700042d601c2010303010285c0c600340062540207056800d0002c0c020071044951032079030780181c2c0c042d28 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336019973 1250 336018723 336018731
    0x622090e01020d240e131a09010513020604051309120f0f020307380103050c1207141c050111030610050306090412111b03060f13120309080d 62
    0x80280c0f001c0c010300c102c0c03925841d6007104041d10b005582c2250044c6000304c1011000c5040043c411062005404141c6904000c9405000c441d001d45c10101c040b00310394114440d402d120110b03d4080c40c0310581038019034001e082d00e0a042c00c00c000e02c2826102400780e580b005480b9040c2a012a040c41c80c640303400201682c4d240c541c2c21032000003404a000000c04d5034210341c800c00c010f1001c034000741c0f800350500048425020780300d841d0034030503200c0e030010002090301905884000010424000303001c00f181c40080d01c0ca11501c20074500e0441d2a49041c5c407565080350b038600812150b901d440506039000482d03c0d250790102daa140d8880c103003166500c604071081003500205200300d518020b608403058519501d4403d00d507140c070740041200141c000d8001030144101480c450718044c021103403103002e0201402114850201c4d040e003811403c025022041c02802500045004202c0000d01284a6008019100d1041c0000d41c1c0d687e0241260b140ba10381011360360001e9400140510008290319a40b8090100e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336021223 1250 336019973 336019987
    0x60c020a0b090a0507081605040b060903030a09050415060c06110f04031103010f180f080f0a0324051c0602091804020a080c0102070b180405010312080c03060622090e0102 75
    0xa04d4101e440e000700026520550801c0f8414107042c20420503108c0a0f03c01248007905c03031021130098019400101d0723040c00086000c9602c41e0b400458001121011a0103004c003841c080c6144040229601540d00003812403120303000482c4440e0440744902d160381d944c2c1443c1009401c1616255001500100e844030002c0c0d90300c80c81850709021320300c120099214200100d140800180d468285010402040340781842c030070310700b80b001c00700a90300e11f01e241100301956002ca00c04010010220740a071240c154050f23040000241094983c1a41601da0140505000f60b10703d5a190864000c4003000300e502d182c0802881c48203031615480a581c840030003101c0070079800d161040000824040d0004c104c654411840c6481903a400207a0078201c402c04080650b0b01c001d541d15008130b6001080c88180c026040c5000082009a0007403104510340362a51042c0300c03901c501005980070720090710f1803a4400c90a22501d0182c108141c40405000040e00302c80d12500e9441c0ca0b200151450003040843d541d60100e40301d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336022473 1250 336021223 336021233
    0x603160e0108070902130510170106020109050609060c1e0d020d091a06030c0613030f03050a081509060402090609031f270339171303060c020a0b090a 66
    0x21405024400819828104601e42003407900e06c07688141441903c6400f000e400041c0204446040200903019a01c2190b0310381c0d2001c1d020b00708440c02110b1601c00c400c00200b20f0b1001040050080e0b81d540389091074030f040600f1884c0d641030f00c0713017840c1d540d6401003101c1c128190841c8003c08e4000040b92020408488600388880350250290404030420321100c00c0001964000c2090b050f00001103910588401d4400b054080700e031042c3d080180aa18089010000d141c0c10101424822502d662080083d41e10319100003040700303407500c21540240050001c51010300d0640c02070051140007a04490078902c481000a150400f020785405800803066000c5420603445e002d0b400100d10a00550b0306001c0c81c4011040950400a0000e0104640707200c0c4030400c4891405401101c0945c0641c03600e0800c00140d841d0119400c1030001c8617038400740c03612480110003040c15541440f458020040490340366403200030107021131400b4081180034000400002416042d0681d0040c1640c034024854100c8903d84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336023723 1250 336022473 336022483
    0xb010e0405160e0f09030a080c0a030e0a060e0606061207080c0720040b0102030403020108060f040b10120506040b01200f0703060e0f0c0a210803070305100f060f03050603160e0108 79
    0x70002c464004004007c0d5698000724aa9040302e0170b6080660307583d400b0706003280108910743c0c0f00700982c09101c200c2004d011041d0003c545000b0801e081d1841926103404005040c40341018080720024440005440580111015a4488240c0700000d1a1403caa5110311928642c8890041040f40c9000c026046050a10414507100c00a0004625190558001030800c0d0001009a0710a00c00520076241c0d5823120741112100c03000280081c050301e403600744041c1642844181c000801444c100c001015031600b0f010b10310800308181c60b68071044642c040e40c441d041c0c2440c9100c03803940c4112200c0c000e52400c1000744c1802140501c078005400194050858100000383d40c256a2035840b9030650b104e00d03915031400e4022503405600800e032071000744443d400320902141c03000d0720b680004010030200a41680180748603011500302d07684442d488801807078030070000e0b011f0390000600c4000038849290090740f14680080d0010704032400c2555401c0e5403159000b00b508084003c0c0d0dc0000100800760040007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336024973 1250 336023723 336023731
    0x101b0806010203042d0306110a030e030702091f051005040f1703160c050310140a0e030901030902010306080a0c061409010c0b150a0906080d0c0b010e0405160e0f 71
    0x30185180c10718001982c80800700094852140c038041509110800840d006174900469001000744618201c0100d5242070707400918081c00420300b440314003040c103900841214420781e80203021071001c0c1c8070317a000d2503e0404002844480c1b164454008201542c901c1c0001a00c0e0300d90341e443c5e540d0346040031601c0d05c0c4000103501402a078140d00b005078214800110613201020352403100c0d2140441c4034248620805100c1d40b206d505406a801800c0380010a078000350b9142840036642c103003d846034481c01c800c072100886078802d90f80090043c41d04540c401d400ca501021300501d0041109a242c454803420002550b030202c031060042d4104001c11a0403c0c100303400083e07006103684c1800c0719030001030920074022000800754100000040c1407000714040c0030303880c654080e16412400d9298a0310b4001420305000356031043c0b240100e03d038640c901c01e0b034000300c2440d0700401e02c0ca8581d10345845034074072000c00741c0120f40394043c0d14000ba0312000600010030041c0021420182c0d1401e22140100304440040c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336026223 1250 336024973 336024977
    0x602030115030905120a050409060602070911030f0402190918030801060807170c0d05040309081b0a0504150302180105040615050714030f04031a010530101b080601 72
    0xa48801300300c01085401100d240c10781d61640e10755010751704a41d00e01c20382e000300c2d404500d400c0011510540c0001c1010995a15031010840c032801c11100e610b907400111144907581c035218000030014203280c1d00b618481401020720684071034941801d20144c03445034070189001484101000d081c10342c010b04150041043e0708001145013803030040240507542945440043d1031005021a444420140448010070a6408108094245842e006140c00309522800c0c03014032641d064281d00d000e1840700480b40d80002007540e00c40d14176001c14030000d0408106c3c0302d901e4004510000002d42c90340c00c1c2d441181d60346100365140b250304000420045074030f190400d61032200c01304055102c0f990050100d901c034540202c0e0303010b0900413124200d8a94840d2402081642c00003188c00020031611420781300240176441e0490810760b0700c031001d0041000901440c107901e520301c406100c1d05041108144200664184140c076542d800400d584402d943c1c3c512041000401d2010100c2c1c40c1540c0100217a421080034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336027473 1250 336026223 336026231
    0x3090b1503070b0c10060605090328030c0203011506170a0204210f02031207050f0c030a08072a0e160f0e0a242613060e010504060203011503 62
    0x40012076501ca400d405120700c0344400180c45070000408100c203044085c9000030070321036a40c981800a24541000329118020301c2507011038050315040140b0b805981c0640e58455002c84942d49003203a0740e100c0e40400340d806540c0c4440201d0030034505910f1a02030a01900c3e42c00c0c809400545128101c500148021503051040c44240400002ea103000d03001200c13104070f09178071020396040407080500d512030000c1d0b01d0321a040100c12484104000703494414062070a591048020b5851706881e04440945650b054011803030800009000300050301200340100c0d4800402682644422051031801400030328200014104115013161300c601250700611051480a44020a02000e010001042d1803181480001300e131083c0716842d0303031114400500e495552144000d41c0340d000381051454402d04640020008880101410300d841a49514040c0140c010040c42d61001d4400000d0010a001100c0c1d16449070080c2e54044000d0040501840c0140c4005a895141040001196521800b60380c103042c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336028723 1250 336027473 336027511
    0x19080412030e1501060206071805061e0d0c0c02100e0a03080d0207060f0207050105092a01140c060f06010c020f10020a050714031207080a0f02030c0d03090b 69
    0x1810440c5038490242000310340e100204085509001d820800400380f21143e50000840c81e900042c854042c00c80307030b110b105d030352038102c4580e8800c802c0c0c9008258011000b00159101401080305401800f541c1d520207038101182c0400a0003038800c10070a0000180140d110f840c15440d015503803005071140703403d00b1103415405402180e072540c0d42e40f00240500e840420208040460f5030110b42810394030000801400e0140072011009400051041d42e1075840c003000289801070000b11134030070540d40300c201d03240c46282d12000340c02c910050305040d04102040c1c4045400c20010307005032a4880c240d1002d05164270385401c2102c01154000c00350340c1000648001399001d41c542804840c0c5e6404151006081a1102c0d2010391400c1032414005240d8892400001450407504101e9200740c4022030596040c8a48188414201e01407060040c107a100c0402910320924060b07690303c452900f80e80152410310032103020031420055920105800700761141c040e5400c02800211081d44507001103a00301070929 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336029973 1250 336028723 336028733
    0x1005090a021302041805010305010c05040305030304060e1c050c121303110406032102010c050a0905221b02070f0807120809100906020d020c011d01170a02190804 71
    0x60000c0041e000c1c0007a038648000703510031501200c000c0c3c00c14068400074500b0306001c020040800b441b0660340b0b94600160008081d110f042140c0c100c80c1c21400442c150380b070315200c401c014074000b507644003148200b8018044612100026503024845520b85035100d0301c151411a00700071003a80110f03117242040244104200d0012031220039030340c0041888203a908683c01003401049941c102828074040717500002c840f41c1c201590200380a0555000f80a0000000c1040c3c6450007031155000101c0d00031403050083c0d00f0020040c000028a24410345400b01200c0170040444040c1c5860a4081c1641e80300340440580402084005161140e90044410f18150804d6201c50a0f8025041d4100d9010301540c148440c04041c0c49142c0401468030324070001c020405441c2e040702d0311502c8050700031218030401c02400800c40100780c0c0010b031620141c000228400080c84200540c40c24140302d0b03a2002131005054034060f491054000e82c0e00140c1d0f400700d601c5140390204440a0800801008a0404c80021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336031223 1250 336029973 336029983
    0x7080c04090c03020f0403050c0118030f0b130b090102090415050a090e0708030d0506040c0305040f060203131a01080c19050906040b0d030314010803130b0c240108100509 75
    0x7510305503000607010302102044000c4e2044424031a01d820380442d020060080100e2041100c80302600c1d0311420701c3c040c00260000341d17450310001e044064130fa00c0c0400491442c0010700e6102c00c528803900e0400361280d035140030f0038030f054401c00c50582d800b0a00550b03030300300b9108983c08103264111a540441c40c09002030101c2c40c541c01800801512030f03114075a0b003841007000f0005013034108162620781075032900180c020002103c0352403003079003071010a684183c0070f0300c21175000e10f400115400c0e0450b40b54442002950000c1c1005040606031031a80c1c011844084104901d0b4001100c515425454206c56529084000000d0781c030039012080b03500010410700640208442c0f080c2c8008040c4ea43d514009802040c0300d10760160401c1c4d0030315001013010b9140d4028000c3c000320510354102d59898026903642d901071032421610754100c0d0441030021070890b801510801441004031052061102c4a21520a104008403814500c072400180f1032170320706104a200c0d0310400c001c204a689006904e043d030754 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336032473 1250 336031223 336031229
    0x30209060f010e0607121d0d240f14071b060b01090306110c0d0e031207080903010903021b01050a08010e0a0e0d0c030909090b0c031008120901030507080c04 69
    0x2401c4000754508407640100e11450054034000e00c00c13501d4450f203007031174200d0340400c0d011640020345402c1e10b46d030008540d10400c402c048000e4282c059440e84d9036101280a003c00d004040125604104502e07190024058946100c00c0d84001082048200840b4a5500b81c081e1980082c021a640d910b0034800000d410304540d0358000c1c402007542d00c44000180e03040c0b003003030b08040e01c241d04180b01044003d0707100700101101c10441d41100e05480b5403001c211800d00b200d0158590507080342e079105034044940d10241c540e50380600021403500451100103400c44203152070032400b6030800d8038100284500e42d070300221a24070a0070544d25050380c0003002440040c2c1401000401c82c003110210300002490b42c40704040c107880000303c81c88426403181c040c242607c443e50031000170700303001d401080000c3c250158081c0c03240d000708030518a03280c1c0510740c080c82d00000c01282e081207a07450b0000d4820001c104011544005000456a9203d00c40005041c2d8100a10304c03000e010000041c0f2644508c800c003100c0032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336033723 1250 336032473 336032479
    0x803071a0c1603090302281719060501030507060809070504020d090b04030e120f0c06071401091505012c1e010e0a06060f0f1407020915090c0403020906 67
    0x901d03656002440280d010b0380404598160310000402c1c101600442d052060b42c2c001c541c900c0503401501200f0711076450080c03400741a04a016000c028100a682ca042148102d08082d0b454006003e80040c0c19880c481c1c030142c0310203803540d00410500005201c650054a1145800c021929001d12103c3c1c0d03070b180f0751056a0180307a00140000d8000400d510105d8039950100004680d0b0410b030500600d0500d0401e0003a1040c054215054070351980040c841d0303005c96418015003030705041002009441e03003010406450800002d50740702c031855806e07c54509241e00c500c0140c102d45600e010540200c2d90160040b400451141e5212840810504800c6040d04815200d00149580b214030302c0f060142d00d0710202044004000c004103840350f81400c0984155840c1c8000c204842d5129400c8030765a0305075402a012841242c2049010f48c032031609102c41c0258040c18a14024455000c40c1a442c01114451f80000324074074000c215241c201c2645410113010010b00d41081d040da00011500c000203012684 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336034973 1250 336033723 336033773
    0xe030604050a033606020d020f0c090601090e1801051003330903051e280c080c06090c03012c070302040509060f1b0301030605190e0f07080307 63
    0x1d144910b03003014907801403804c00a044144070303070951907804024020480503000c0c02c80391250b464030000b41554004141e02c001e0000d0040f46003404903000303015041c00c0c1042510b2a011480d142c0d81d0450501402204c0d000001d45646603402c00d00319134015142c21003440c0c03015001c001107864038241400000c0c0c1c042c004d4400e10f00e0f80740000d00c882e03030020007501628200b9006206050f003200181030342030f94078920031400c2d1500c0c0183d040c0d14420b070380c041d43c44074001250040c825a14010300d41c0c03111541d070915403078008641d15040c0b1150008425035200d81d200804004200341c0900044a1a41c0150000d0100b4200c2a8901d104402c407035503a0740c0712501c04441e40840b018200305100c000e54016004110f070b802d1440520b521540111428400311100c031001c500305807948140f0362040d01d01c2401407800c6900b181d0302c181c081c00c0c024144000102c9a100d907007001042610580300400102c0c002804644003038200c0e01c4c01c215550b03120b826103400900014011800520391001f0301168100510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336036223 1250 336034973 336034997
    0x1020a081c0e16090609020f0304030c0303090c091a0414010911070b131e20010203070204140613050105060f091801030c090e060717070318050d0e030604050a03 71
    0x100200718590002060303200310541c010100c2e02c10f074401e00a440311614180804d603281c1c0c64210a0b0310807110000c2c00b400d0200001800b007071041c1c00340c110040c8a07190109036540f8030703114404820b10b00e40004801d50390f0780100613001c0f4100b400c180030b0501e040e00d0500c0102603240e074250100f1014403d000f9816199128034400780c001d001101c0c0c8160f4803248160302c0781803501d2a43c03003001e00c0140c01c07070780007001058070710301100303e5414a0001c540c00144151050040c01c400541c1c00c00c0095038038103512003401218010f85d264040c40e440400302c440c050540b45000020400362400102104680070b24220040c0101c0d04d03204200c82119600740042540c90441c2c00200e240070840e80ca80048840c000030002c03080100c850105003c45810140a101200e4541d41c2c080c1c40c0c20058440a0200701c180b40031568446c40180010f602c0320450400080f040e200f00e00d18100290600b208480b40d070065022510619004a454a0910000d80050000c0d03c0d0507514141d4581c85030348040c090005801441e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336037473 1250 336036223 336036277
    0x40b010e1c140705030613050601140109080a0f05190b01050d020303041e090c050a020606041a04141009090201021207050c04020412060e19021e030114010602010b01020a08 76
    0x101c6600c0d40d200300c08104048440600c90f4441959006240c400d00032140030491680544d1490780542e50081c01a1080764a03181010352a001480e004505100100034000343c0d034501480820020307030180740d0b00190540c60746060b5082c1921381c20005041900d0505040c00f08000c18001d5040d07600c00d40707541c2030700304007400041c2c914080c550180000d02e45c514540c180140400c1e890200310b0b852010280841030b080d0005030f52500604c1d40420040c0c1c013403000a01381d03242c90b4202c800922105819000765000d00000301d0192980340903c2c91b41884181c06101c02608a51230f404000c04d501e41e010080e201c900e0340003d45602d041500700aa5405c081804401d010040c0300140007001c00410855a03a6550400803840750b03455039040d28001e2804212100c400000300710401c1d40f10b40b000401c400807482d5820801101150a049a4010240408017030651024800e4072001c0e07440351008080f030f6143c030400900307541c240c1145d07904541002d0b40c1480044d0340c0b441960680408209006411201191f40d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336038723 1250 336037473 336037519
    0xc0706121d0f0609010507080c0a0e150421170c07080a150c090f05010f030b0306071112090616020d05070e090f0303010803090103020903070e0f070e040b010e 70
    0x414401404510310809100e81c001461406001d540c005503910f82c0e481260641c2260350444011f070120302c1c0c1c6000900211194002460690305078108040d468240b0008101c4c50301917402c0225030f2900003c0d00f4000d50000e528441e10000c200d20308681803600035913491040c90903a00c098064a0800314036910b51300b50900c1007038090001401151040000350421201c4040d440b01409a02480d10240641c0b1078400c19018050701c0c0302501d81040103142100440e10020806140c104056503480e00c000955014800540075005076903c83c4034407102c0c1202d081c10602c0491140c14685001c0114007a252501800e0f07900c100880584544148006d0002c60018071039940010504d0040741c2c4080f07000f40702c050401f4090300030b2808039064464031766002503a0b0310080c0615a12940705102c4000c541d807180d0020008204060255441c0545c1c0303009400f15124191070341003034008400108006c10ba8484607103403001c40110f030184858186e8000213003e400d100d0034070600602c0d2400100c810000321841c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336039973 1250 336038723 336038741
    0x3010f0b0307031e05030f040302011b050717030d110d0615081914091506011704230706020304030506060906011e0e1008010312080906010608100b0a02030910050c070612 75
    0x1502da4403010001924519482340c00300b03c0c0130070000c0d10140d4402e4010701450500c81d60240003000c015042080f140040c0170809040d16841c84100500844840c02d406a007500c50010200580c85c0c0700e02400da00c06842d01900013617820b800c1c218a0949031079200382c100e80c100b411850800e220f044c0e8030034058044c03c40e20700d040405507820814000d14101c001140c05250f484401070a40c9526100011600c84610303080c2035940d804602c1c049030110b040310540300e0440480c0014645096000c040d203e0404119600840240c1c0021400b0824013000f4803a45a0040c402c580c0e040244c607258001800c88100342109034090910301001c291068055111084200801070070542c019411040c02040c01c0d209000c21100b1540c110404180d56009030320046c019002140030304a180e00b484012600c24000610504038181e94060002d0481c01c100000e110401c004c1e80950380e502c0c03202d0144100300c0b218103145010042c0800100d101c0c0c1c03101048101c01c1d241c1a250990300c8031441c2c400c44002e0034007a4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336041223 1250 336039973 336039983
    0x509010210091101030e030f0702040e01090f3909020901021015031e08071e0206210f040213020d060f08010b01020f060c041412010903020c03010f0b0307031e 70
    0x1c030700d103410f0142c00d0001c0c000b12a0309a9003840035603140084203031680501107840c41c51003802e001c2c4000528064119154894040c400000c101c62242c0710035041103001c2c0d4050341da42c3c1482c400700310216014500c0c0c0902c1e100101e07006401c4101c40c10103043c410b02074402e00401542c0800d2481c1342d80e100784a10440c040104000307001d6030140449140e1203202a100444d410000103034402c42880300c840400010340e40044d04a400c0002c00d4988485803900b58211040e44c0b4400141c0d800160340755005070002400c500c0341000c40403816490b00320408030103001c5400d40555041000016641e4001c2410003444865001d42c80b0500d0203144006895682c00441e824401c4000105400d0815405111102c000364215824030544004450701d842043e50a909605d504210512404031240d0b00700260131005030a0315951701402070145c1c00c5940341042200181c100385d034007442030301d0240550314118120441c200b069404c0d210010b41d40b042d45c1e200c010300c20440c0d140d4039014400710a03510100c3d01d404c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336042473 1250 336041223 336041231
    0xd051506100915260703020d0b09010b040e0408040b0301060216050102060412180506030117060c040f030b04021c0c0807060905030601091d0a030f090e13030806040b0d050610090213060509010210 86
    0x407403170107400785d045030394007500043c41c02041d6019485c00304802c90488190b282c4180c9030908259001e0682c21005006448040b404c01c000035104401d00d0042d4000c2c0010340c05808000e4400b6901c0c00c1000d00c0d580000d0465100d0824000840e01a0700c801c4841c82007400d044030305400d484081807411901c3c0d84010780c8000301000003e814401c03e400711000420b84010307100c15948500c0c40303000a011b02d001c0d2441c0f0003029002407000070746020b0f9254000f0300041c10166001c1c1210715440000c015100200c5589079044020803400f1000c000c440f01408490410121583c10310740840d540b2441403041d541c6290704d07010801841301c040c01d400417500040c541560701c00c001c20300b400f40000707070903502540000e04081000100e486044840c030303005203844104c485010178140c8080f0307641080a800554403a60394185800c0c4c5503280c0a070089100e01c5030000e0481446d04220b288100449076104d4141580104014155100c02003059020743d45039007401a1540301d01c0d03004070710f0615081c02c086011454 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336043723 1250 336042473 336042481
    0xa0f030b04020a08010612080f0708041205070609080c1912030c050c030105060f090601022509060e130f1a071205180d0e0d05150610091526 62
    0x20031a01a44114001c0e0b55000510350b5843d2a50b0032a40d8501c60a40003440c0c5804407000030b02c40e01c00801900c00c0c650300082c100f40898407441040d0348035600c640041a9a0000502004003d000e12001480c49080104510780f500d000c560301c605c0007054803807107a15400d101000da02a0704e46a00040c0c40d0700c1017040140e07405c2d1f1034050200c0b80402e0040e1560300c01d0050b44046031905001b91489500094200c0b00c0c40d00414081c0000928060a0b85041d0b02449480c02c03000c08003036502115440f032010a96080300d140804031021158142c0255800581b242c040040030b10350161f0b107280700c580c000598024601a1b05180201015444203803005000c40d5060010155004c20349040130042c2d18010005030301c0d4003072046581c1e005500e5400180c3c0200380c1c40100280110343c0c035603800a01a042401d00318550381e99600307088080002c10703412941202848400e00307160140d41d18102103418900201421f013250355078281c80c000b588200700502d5180164003034211a000d1841520360784041d1034a810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336044973 1250 336043723 336043733
    0xa140a0308070303150f080a020409050f0d0f03140c12060a0b0c0a03030e15160909090f0b061c02041e050907080d0311030612010902060408060109060909030e0f0a0f03 74
    0x490744649009440081c00c0116440036042032040c07c80740c0310001021551038550134417000d005c429005560340d020305104404000c8003807180024650060f0fa4030034140d0031040300501240d8804c0c0b102c509826010302008010120314040351001c1c802d203084001642c6d42c1c0360024415a5180e041480c210002052408038003d002807110102c604c81c1c1c906000300d00e00320460541d201c0710706024201404807400801c40c022450b0704d4520302441c852420340b60241e11401010142c4201590854101d100701d03264805000001d03024940100e82111018108141d4030105172581c0d0700500040e1240703903201c0001c4140c20000b0718502c0207c091103020300103850f02e0481c140c0c54403098802c0d40418010844080c088912900c58074025480303c9200c1e80c110b031901c0c414455800045140c13803503030399070303070f05400c00580d070f650020b080248032545c000c0c0810b42c14840d03002c087c0c682c568008007810b4140302100e0b002940048000018020980c1d48032112000580019203036a0660300001a10200b007001106001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336046223 1250 336044973 336044981
    0x71703040b043014060109020705031c0b032e020a09030b1f1e0b03070c0611040905040b1b28200c1903020a03030f050f31050a140a0308070303 63
    0x102080c0985d1400da0f170750304494003a4420040014901d400801c011540c64290b5440d0280b045603507200011074020703400c082441e0036044c0d04c201d031641e6100500d46a080391044020b4501c7c4140074410740c00c05581400c060020155804000c0c41c94000100140c100307484400d444940c00b2115401c0d503a46d6589060110f68003030311400e810480040e9081c00729102c1c2189080303e00800c01d560319680d064030319842d48030050126469140c0416403c1000140d80869406178900a03809403071a60dc0d58113003d140f0a03c902e61049009240d0401030080c0f118000101801c0450f410310303240c0e421b1543e15124803c43c4c0c0208107299481092001c2880321f000c1d1407000400d1701045105941e100502c414517240d090110106210081d44544482024000a481101c0c1d1030707284041d40c2483c034284482c46182016980150450300d0010718011500c03007036500c45034a640c2d40c6030726950345804542d00380004100c4014160040000300c40111105405039114000391800858211035103039198041c0b403800070060 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336047473 1250 336046223 336046253
    0x51e0d03051e0a12060b0f07061407020102091008010e04060b0103090510020409180b0105060a05160308071202031506130b040b0301030320031c0b040509071703040b0430 75
    0x44c1481c0c003003449400c910720a18041c0d8400000b11424642c21402034009584100b0003100c100752101440c1c850100c0d405143c5005034800e400140c1c40d094002d083c004a54020740e40c1e802001040d9004020040000441c603400030f801c214003060003048400107a001c2c01454400810034425000065002c018035800790040c1e49108906001030a030514010060300134006001d484010000010096468460300400e040101030915901300705154000b48060124400d0a4011500c000e040040c3d0070762101140b1498494440c1c11070550901031104400301883d000110701401c00018030b68001907514020000a004003000700b80d860391a603c01c00840d400178030088000c554481200782d0007860201e0000f0409501400179402c054642000e0b0b120144420015111385a940d2045462512140501840b8980711001850158039043d42d00510000390007103100582c06c14401480410302103000c80341201c00841135031418960310320a102c1003030440401840b58440c051010300401c40740401140c48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336048723 1250 336047473 336047477
    0x602030a140708060f040b13061a090a0e040203070b07080406020c060f0703030b01020c0a030819020109030206040303090602040306020406030504030f0905031506120105010816081507050d0e0106120606051e0d03051e0a 96
    0x203c44a0994012f4010b040800d540400308840a2140203556020300f90f11500040480740701668419200d00d60754028401581e040200050074000c041d010000704001413803e40305c1300d1420746000c02c01000741c01820340c010101a00c034440c42510380c0c803c210b88024a03c00406048041d0b507603143c8841c0a030b1210040b401e403d141c1d80c00c2050071f5070040c81100295078250300580080e5a81da54200c00410a2803400c4848039424400030020444602c0a0400791505407800215410281005041843c80403c50410450301042c18006510701044840044408040a5031503480c3c020000d20711444c0455036082075840c04000042000c000143c0d8081d002c0c40c170003980c1865440d40d4055440341e450484030b03801031144001140034284a10001d143d0050401000120007031001101030940c2c01035400350582182070f403403090034040188160743c000c20040b214607802c9020391a1003131951501c00b200c0c030b1141460118040078140228222140201d542400c2311601425041c3c10030b080c3c000c6480140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336049973 1250 336048723 336048749
    0x60e090a060b0f030a120c0830010b0d090218071e03050907120609050a0b060a05061206010c02010c1e12030209030c1012090602030a140708060f040b1306 68
    0x301504044443c00e4400310050040c15005003142c840d181d15003e00c140c41c41c100600c0d421214040340c8884050b01c0341307480311942c1c02c0c10000c00351108440c02105180e1117000205080040100000300411650828204000845c0300b960600024511040c03076842401009541000c205034507600000b080080300040c04011008a03040c50300704d0032241c0c12104410150b100030410b001400e0180c03800403440b445084c1c00310700c980c2c8030303941d241c104030a960741103c402503803d0600951f07140c0f05409402904080d281181060a48000300c1c0300c1c0c07074028050b14140600e08045006691160402c0d12002c0e170050300d401d1610ba0318608140810410400a480e00240741c90310340d4816200e80200c49a81400400600d4040d90103400c000c00030281d01012030a210090a82c0d50881c00c2c01d02902c09014010400107890785040709040054440c05100002c014100d10100030049400102180d0032250070380720a80c540d007a10b001300d0018502581c0d1103500010400601011381025086041590705c0202200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336051223 1250 336049973 336049991
    0x90e100f0207020913080406081308070308010e2a220b03060906060301081c0504080106080705040b120607030e0c041a030106060f1709120c07030c210602090103060e090a06 76
    0x40c88102c17000704010001c0100300310800c2110f03c504c078040e4015a440400004800183da03400c0450303803292508601003400e00004004103d01000e000b070340b240e000c1e40035144c14024010031404172170040b441c106998070701254405e41112280a9080c5055002c403500340f8a686400b840c10f10350700103c448510401d0f005000549074104801502c0c100c840d01401804031038100765600341004150510142000000d01002070000001d0141600034071101d0040e003007031030800e018002942e14141e40e6a0007500400840e0405c4c82e00064120340c451001d10700040c0387e0710b41003845402c0400e45003140e0b034024181520450102820910b100019404400800026540d42e4040d01c904019544032004900c8900310801030203c0030355200d5010000ca015a40e41d001f000040802d140c100440d821010b030b003e4001482084903030207819020341440b8000c60241c41041500103580200c5100007000e0719004190040341d80d00a0b0018005000710180c04a0350b46803000045940e50708940f41a100c5e41d05100c076003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336052473 1250 336051223 336051241
    0x20a02060a05010f12060209030f0304060c0b0610050f1b0304030c091407050a030b030a1703010515040f090e0102070f11040c1b06020306150703050a1d0a090e100f02070209 76
    0x30808072005010140c3d030170041350311100e0013504034410f0f041c3c05010352803880c441d1841c00d1005001500164039421a848cc00c0c0c18140000f41740242820b0103600000c2c11822000c0c0c00034295409240d100d128280e8940c12138990004a20410f2101c4c41e041c4000f28000c001c2051800d25102540c00d155020070401d610710b000c440070550b040d501200070600c10005841541e101c1d8210b5080c1c2d007001380440b41c0740e190303958071088900f2501038140c0d410303a004001806140f80102c00324101074898407000c1d040500302103902002d0886842141c0300d40b6035480003450118029010745800581000d0300d404001c840e0300742090070918500b0305034031881c5000d51050840780102e030501c185111001700428402240e5540000950000e461160b1200c64851100440300c8080009e01819101e41e89080e00e40e9111940030f030920b01102c0d0a102604ca8102d00702c1615180c1e40300340b40889031710042c0800c61240700c1d0b441505201c411034004841c18100200072440c0d0700b8035001041d545200fa204041d00303980761808 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336053723 1250 336052473 336052499
    0xc02030909061e060c012003010e28020a031b05040b07081e0a050c010b0109050319060b03070f0509010504020702010804110102010b130b03060114060f0c070801020a02060a0501 78
    0x442035004881d400800c100d810b1200300c1c6080301580040c0c00035060280340c0000d40642125000215583d104d84241d22031a844d903041c0000001c0c2550700300d09650522424540801c4001c0000c85440010903c000e50010181e000c1407441501d003808541c0c4120f5a40d009002e0039241200e0450380c5204000c01001502c1201103408580e0211101400d0030312903550f2078459405141949441d128613034801c1c41c080c1c2071100070010002d003521050f50303c007403181400f420754004103000e40c14416814410459a10049417041d860320110100d03043c5440a441e02d03a0007014004a015094400c030702010608001c41c10201050f10821120200c0f0390707076600308010581c800d50400030300003a032110200700022490321b0b01705c49040381400041001c3d040c64002c40c52000300500f0150025845006e410000e0405108242c0581b0211a5801c9000000700c0450b413140b04218041d0003100c00022051400903040c40460054001100203650f24514a000255100780907555208031601e403900000e000101000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336054973 1250 336053723 336053737
    0x10515150406050304050a0503130e010909020d080a120509030d1b05090613050d080d150602031c110307091802040302131802092502010e191e150c0203 67
    0x40401c0c40c107401c10034102c407582c1010304210f445104614410000030420302c090a10160309249800d0880e15000c0c4800e94540180e01800105203000d580078050b03181c400720a18040d800088a55031a0003000045a5140581d081d014403245803006010300d4001c007100510f038144c011501401029403100c41144448400c007807141c0400c02c02c22072481242030060281c500c0006680641e0b41c043e94401c0800d649031201042115a15000514200780701c15510a03107101c4003c041183e08621b042c00000b9660380300f00d0f034100900e1945107072442154680e0760016152130504462041e11303414900d001a10205080c052100021008621407001a001c0d00c00d4908a13600108210490010340802c007004206684200741c0140501210002507210040c01c40d02035800e0b0400107003540300c68417103000c0f580600b54000b030459041a180a46141000038004101d41105d0101c203400c91080c58002850300a805412415887e09c030807030000d0001c2110368810214a05409001c01011484101d0300c1e8480c0305 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336056223 1250 336054973 336055009
    0x30e130e0d08060604090606030501090e0a0203070501080912040e04050c0d11060d0216050a1e031d01050405090c09030c0603010b07061a040612021315090f110408010515 75
    0x305070411184650090703074002d8000360626142c503448044c100f064981d190801404aa240c000400c0b182c200341c40f886c020740710b440c805061429850303030001b5115800c0b40b0504e4100b000000104681c103a05001001d190003145250075561991b521181100c1c2c14121001e441501888041032514100110810304a80d48090000c0b40140204200700d600c2d000301144e611700c240e080c03000b4504003041084032600c083c024001010310301c0c002d15043c2060a41407842e1840100089018000079420407203152191082025148507122807000403100d50260380d1000d83d209005c0401d04c1981c03096400207000b42c04056041c0c0b5021a40d1005100317841c842803213042c2d201c004c01c02825000c20b9245e170251071607500110120502d05403560000d01940c41d142c01c0000900300d0180707074100714588902000011042030f2018062201d00b0038031131030500c4461181c401c6007510717030f5211031400e0540d610400000030400c0d02940c03240d442c0c03441d80e40202400c803240941010181881055482c107210904480d4007a5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336057473 1250 336056223 336056233
    0xb030601060203190e3d020d0c0503071a10050103050609040204050405070521010b03010504120f030209061b1b091f08060103110a0b0a020613030e0d030e130e 70
    0x16604c0c440d210b5100320544000c0100322118509156140040c03080010b84039854100e1846291210400754005403070f40200c0b81d00f01c415a1004943c0100304010701d501c0c0d9041900f041d52042c00c0c10740c218854164000c102c80740005400060205880f9046c0c0500070300041066201d803a0310040d02250b40036a030350f960180010002400514141d080641d01512407411b441c14180c0c0c0e08082600042c0b0056402404009015030300040382c4240304001511200300c00a000c04d08054403074a03245008000c1110800c100720b2208104a07006e901103864518000e0306a0f42e40e00f0314605084801111160402058000e40001031400740503104251021080200340203d00d8032880301050710802d42202504225444c7c104c0002d880000344606402540903036148a1a409030004000040415030070140c0d49000a11003103841030350000301c40340d0041c4a0483c044d854105802c058075020000c45000d58800d03000784000041580c000b541160382803003514990018010881c02400340c850100707040c0d543e81e000d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336058723 1250 336057473 336057487
    0x80712080409051e0108031b0601120201030507090b0304050a060501052d0d0203120405090c0f0403030e010c021e0102160503030702040f0207050303040308041205040e06010c080405030d0c02040b030601060203 92
    0x1660301030b039003200c204900582142c400c80e840d013550030401d92118510b80c101090b4514000c40c160418004140d808018001543c108600d40c003141c08141b40282c10150780d18005106540242c40307200107883d800c1c1a290700c4c1e24051901d0382d610f00350540c044518606000002849040602100c5400701d403d1041040e942e1a0000310a401c0a0b01d504841c0d0005001052030b001d618240100d42c10000c0190542c1c2d919410305003841058480a0160320014004009428404141c03d095505481e03242c41c10306100d000c8200100d83d117032146200079501289000c1000508590101c409a05a0003a001d17120b00c0742199508240b44800307441880c1d0182c0041240100528059015500482d5842c07001801c2809549840345150002c0f05c040300803030750304400d001c280070498101e00307400340310703880c18a15081c00c1c0340742c0800003075001d003415040c0232aa1909008001110099030040e1001034210f58195201001c010030400300d40c9000c5c1c2c002c1c0d01d0200d0816007400c0103d10141695650780045140c010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336059973 1250 336058723 336058739
    0x140319090204021c0b0a05010c152c100b10140309011107081b03070206070605040f02040e030901120905070302220f0605040b01090303020c011103120702070807120804 74
    0xc12089034029400c00441e089541c002d9401d441d03d1319669400100802c024090140300e03001500028107018401403604001021260540e001524203800421005507030315000c0c801c0031607100301c14001c8020040c5e030117221000148107001d1054010b4240900c2130380000f4010f09021020038240010310f03100c9080c82c4030502000541c1c0125208000251b0003600f40c0425941e60402c1d441113440220020b5101c4009640d0088100703482c4013000035500d0f0031081e900151191213410b100402c10b907100c070002414410700f403c4444507540c001d0401d208121960460035101e40c4001e8400d40030903040f0414064001d007901c5480c42c1c8991010082c200603003590200a003039440e90440801445210149484440841c01550788030f840408000c600b044c03c1070700f0032007039940174000c0c9070400891620400c00300e40e002070780854441080c01e0032244440c3c120b0003103045105200442185003441818800032a0380054090111900101a103d180d13480c1c41e81003014090340100a80075810900060200007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336061223 1250 336059973 336059981
    0x114060a050c0618100b010c0b0402040b0414010911040503060403051c060603020d110c0a17071b050307080f120a090503010c030606090915090b2b03140319 69
    0x4800c0382000c42c204088909868079110003103545444070f4880c464000920394080107410f401c50014041400300450700d4000030201800e081c809410006c604006c14195101c1d580300405881c80034206120084a080e03403000401020b10507581310701e1403e04801407070110b283c20740b800e0b154000c01820013503d0355241283c0315005007200807040d003101c0400c04880005442030700300901c01ca03100507071240403840d4044200c6008513503440ca2650100100b00c040c201c08200382407241d901040d140d16008843c04d00110a00410000402003032084030001100d4191800302e8088034004c40484d0310090f1a0301c920b98481c007083c041c4244591015180d018400703140c501504c0407043d030b0710300622490340c1e600011f802d4880381c07494000466a0f804041c002c480d84a0006000b8000035003007804030304442011034401407814800d4481170760340c49520040b00d5542803640200340c80c0d503265400c3c89500c1240030720200164a803044002c1000e030000c0e0300c002c0325a00107032403041010340751000e03001c0312030302810000d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336062473 1250 336061223 336061237
    0xa020306180114040b160c03050913151e050f0d030e0d0f060519020a0518041103011805161e02070315020702010909020906032406030406020c0d08011406 68
    0x41d5200c00441d4643d541c2000200d115600910303107190f15042c012800c40c601c040700000c0d1400c101e00801d00d200801d401c0b00403200500c80c1a200c18a811446a828900411840316010982940d002e00011489040400442c00d803980031707001810305035158100b000580e0340c0d040240d005444016840e0110b8060548103215100140080003490a207607502010400015411203a4641c4c840038414203140046601d991810b42000840c60012061009402c500a412030014482c0e0340e41e04494403a21203800c030032400030020310a1501c0c0e507103d8010211145075808211405490100040c07075001c4007000040c2c00c01c09542301c410085031942580f05080c02d41c00407040c190b1242c04400000210885c590a0356503000d03040058544102d071000400c00a1194030140d0b40a0040c042401f0725a1403804598100108620f106940d4140808151462081c14400d5a011b40040104000e018068006140c1c107008841601d6513281c14607400c4d220f0b00d90a005083c0c064100d48200555804c1410040080c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336063723 1250 336062473 336062521
    0x606090e0406020c061602061f0b0c030c0a0b01030302060a0b0a0e0402030c0306010602010b010f051306080615040803281715190303030c111902130c110c01020a020306 74
    0x140844e003201c4140b90840541d070050b19644040e90001e440c50341444120b4004440c42607540c0c82c10038015060007c2c420a002e500f10070791000614140b55442001180c04100010055990003412030070b09407440c2000348020703400b6009580000c0d008403402c1c400c0c0302c1480b800401d410000d44c1400e41c21103054000a00c01c0307030107102e1000032090558041010130f000340700603400490003603580d2000410440b00b040200c001d225050140c000986500040700040d9034983c46e0008031781e035401000420101481000050080d000a4041200640400200088035400500d0002c0c445500c5000c040d01801826984c00112040c5c241c84100c10404180340d0440c41e00000ca030800b01040001407021405160704042e49400382208004060b090b0003412200031a03800c19001e00544120b0940c0c44a074030061484013440e0620a60007195036400845854200f070510070065124201005021580440703401043c80c412260704001d81c1d072001600010456000d009805c09484030418088000070052480e01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336064973 1250 336063723 336063727
    0xe0613020c0106090c02010e10090819050c0606010e330d02070215040f031103070e010905042105040e060a080303041a090601030209040209090f030d06180606090e040602 75
    0x10108900160003002a140c000240c2d8514144111040702e04882c0760b070f000c2da410655a02440880450002c400a031010707800301c0c0030140f40c641007140b4854040001c031021701500313281f040240d001d000741480555100486a40386c40c0c00005548405480b04025801045140e50200c0140c008100404c8462024035849800d01500001e9085811450700c284a25501280c41c2c425403610541a08103032102c0b4404070329141c10a50202418110703400301511840c8903140792a26030b181042000010100019025200e5071100c1244018010945050b01d0700c01003103540c0c01c141c41c030010725000c00c07044545410b03251904e0000c504071406401805207a11140c00000041c1c007110600055110760300c0b4114040107000007090408a824010307103000030342d500c03c100500068884030401c81d0090340464a04400b9038402d0010b924040741506140400e0002085890748141c0c2d41e04180252400560b860b500840c660940404840c82e81c40340300c0000f5150721007003100c5604031500d1a007090081c4000341c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336066223 1250 336064973 336064999
    0x5120331020307090b0411040506040303050319050709080d021c03180615030b09060f0411040b040905071a030c0f0901110a11040c08040f1e0c03050a05010e06100e06 73
    0x107403c0c0055548550801600c50181c009a85001e104402d0500308030402e060401d803c140100b4428000e5000090a003e80040891440100078802840d00303e02c204c8140410300c1c2001000341910113038864617403a4800e15003c4800d15001141c1800c2c0441d0420015400034001c072412030142160b80c1645801c2c0604100e054081181c1e405800b1406e00c82c0b1200c620b0320f40c610720f0000384c600e4000f0080002500410280002c000c2c3e480c0c2d0711504250888010104030810b02c00040c01000300160b5143e0041c50f11074036004200010965400311803c0002c50b854004080b0381480741c51004071412340c84138004014034034010000c0c0d4040c0c03110440600d44008040708520354585002143d4400781c5001d401d03c20144a1403a040c000c1048600591031f0020403403d160b03a0b5103030600ca0308000104440900e5800f955120440000b40380e8607a00100101d1803140c4c0ca0500d6a100c40300d0340015501b0303509002e00100b4807000050018050700205007040b180914214600c4680030015003020781c4030111992203 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336067473 1250 336066223 336066229
    0x61f1407050d110304060516061b09081c090512010213121e11120f070b07230a060207030203120901020c0601050a0b07020f1513030512033102 63
    0x50045a03100d00c00800740c84042d0000505040000c01d80091a54403c00091240c0c43e0f201d001c2d5400c0d8007040780710810002c003500d080e1002e01035041400381500844500b00b148280d000d0f0f00441124100f000703980079162030000d0b0b9001c1c0d00c0032a181c48049070700300b07008120a003824410725242501441c00141403081ea211450002c241c1984104441402c094180d8240b1159161036036075441d401c60b11094040d43c640d680300ba5060903c0703c15206a0b030191406403401e00a110317001340380c80c51505454030f40381c03a05480c03400d540018006960301c0152942e5460100700924540900d101c20030018070030000700f40d0700c20019611885045045000500c5641d0886a040004600880e014800540c449130451281860280168131861241d104050704000154102046030790301501500e425240d0308414002c912064201c0a121aa4000c00542207100340c2002070580c003581d02c42c00944865030340050780840e807408107030f0b503e014120b00c0c01e5401603a111840050a200031000c564003000c510b0329000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336068723 1250 336067473 336067477
    0x70b0f1918141c300206070305040309090902150a050703140703091502070801110304150b010518010c0203100b09070801211112100f1e0504020a170307120503061f14 73
    0x203500381480025203a40135806104503035006a440c5000c00c45860943c4000340610081c1c03180d0400700c2d40d40c0c1030b80c8095403981003140d90419046040203a80e014403d071b0081440d44040e03400d07000902e807010300007420b441a0b800c03031b03503030a4155442800d100c0c05c104e46d449440401c03030101003d501c80c121000400b040c0a010b0040c0789404004100c0d00c83c5814203080d179003403002221304504d540c034045440c0c06581e0080f0a03612815900c001810b00000101c0050b00d0b03103004290040e51504c00e100e95117a0240380c4d0340024001c003405a503008840e0b210500b054410240a0007008020403c03050188415990101e0f00410240148984000b245941c40401c0b80c02ca009015002e003034000c14a0509041181c0c010300342d00175a098020000e0192445030034104136a440c0345504560b03143c501040a56454a0b51a4040c06606203466821001d91a440e03550760b0001100b1160901c0908003010064016401d4070720556000d440c550340a14615011030550140012103020720802665000a0300c400f980 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336069973 1250 336068723 336068783
    0xb0d0c11100b09090f1b03033702060420150d050601090503150a050907080d0c0b01050108060f09041e151508070b0f1918141c 56
    0x4030004100d0342c0e8105200c25004002d000302aa0f42c090120840415000201c00885005412194080f0540100020b0031031180c84094404d8421a0880310750b202c03041102c1c0751461021076210b488600790544183d8480754200d401a06850f45c4a00191022000c40143c031806c52000f090301002c0c0e403a00400000541001c01060b00884e03071041000202d580205421001c2c2c1411801404404c4d100030420120306002420181490f0f201c202051482c4420071400c40504541e1040d00c1076040034840c0100b48184000d0192180d2000310300029055024000d00d901400d070180444a03210b0a007000d2241000f8007400445142401c03054440f00403440d80c41840e101032142100c1c04010b800480c540d0b05940002c801c1c0314211009203002c00c0b6410000030440220b0f00c50000340307a1a07114124514800f03009214500f408a903000002a07039840e44021000f540d000b07041200f40c4102e84a40d01d0200c00040c4580180c0c00c2441e020015006844140902d041244070780b000303608141c0c224014440b081c1c0711030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336071223 1250 336069973 336070003
    0xd09030c0b09030306101d091603050a060e010b0a020c100903022b020118180509011d1f0b0a0906080f0d0c0308091014060f06040b0d0c11 61
    0x1400010801405030303501c640100e400e000450642c00c02d040000d0748000446c4102d414058101e1000703103062100c00f00c001d20090028840340d0a450f18001d030340c0098425441010000340307040006052281188513030400c0da041c0c6400d40d0916801c25002d000958401840307030055201c1c1114a035942e41d80c01d99012811074190751044001440d600c140811680e88507074120201d20a0604115030040180c01541c41756024a003259070281e0b20040c841804101c3d82003106030540c001b00540a0020603009140034540203c000c000e071303140181c450711008030600001c101e5500a40750840038134502500344014220040c00009201264a0004e03949852641c00788054a407155002c003c183e02c1480281c80d01c00d0f560340603002c4096140f200604808541d08010705114011000c01c0c2c41d035100b00b008034003940c0030b0f2030304108003203010321001c9010200300c412912911601010142d181864001d0303404a5100946841c14184441304102c0038040c0c41440e4030800500c0c0c180d061450504102050080d1101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336072473 1250 336071223 336071237
    0x60509060d050703020a02010f09050c21060a0903110d1202031503011e060b0a080609100305010e0a050613150209120a120e010503010b0306010c030201020c0f010501140405010305030a03050c0d0903 87
    0x246c1c40030382511928101c030b20201c0d00d0301c4041c102096001c02c103e415120b0450b020418202280326098031341c440303200d035101c0710320580d002c012854205500c8040d94500a843e00512030800440c440ea0b04e242ca1326503400000e041c00c508262560258010f55082491402046418200c22011a084405003441e13075100c0089240110311029044c410880508582c0e03d10501e4410414405011110041c140e80d0140c0a0040000d08040360600e805020316031041c000c0c01400a040001c6507110814002603c2034010040170800d0140140400c2d80c0d11640098100b004900b0940b9500094210585454008070b540d2506441000180b00aa258910800c0010482c0c1d54481c401495010346251480c1403180800041c405002e503c42541d0b40103400b40ba103600e03004400e03e0100e0283c01001c2c00c0d40317940d01c070300d4440c003074243d40642185043c2c64110045031151001d450420003510381c00c1c800588070350030420000c030f00c69100307400150b0f202240e43d400602e00218140200111010702034190700182e00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336073723 1250 336072473 336072487
    0x20102091009030c150813020a0504021803100c0e0609030f120406080f010302010903060f0603081908090102070209062103121609060f120e0607091d10060509060d05070302 76
    0x14504c1c10b4090b0041c100d0700b44804082c840058076940000c0c0c00d4020a030855202d0000319034410200c500a0100a00b041d5190650042841c41000712402e4440c424003038207110500c1880305205405461401e95102c0001c4812007042c0034a070fa1002d01e480c0e0301070141e84000000303054104910f034182c0384190305044c1d5442c60140024460340c0090003000182d040900108090303a4002c02e20420b0342e0304000000f8503c190802c582008003015400109010300115050f0340c6800c0c403c42058120100d03444109940c0d881c04503c500301d10031410000d5006e1140404240f840c1405124507132050841019452910018121140b564110700751221000302c0390400c02c800c0d440007101000d079107011814080802803c100700540306000d050902d4003086803445040c03400b005660010f107020603883d000c0d91090b00f0b02400041011109020382e4400c04114a8004c1d45070000f014418840e04048541d0942e0509090084503103501510400e58000014440d5101d6041c1500c01c0d1030240490381c50040c1d491034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336074973 1250 336073723 336073733
    0x10b03070909050606070201121b0905010908060417090102030d0e03130509070c0b06010c15050405010b010c0f1101030b030d090302030d0504080c0f0411030901050f0c0316080702010209100903 85
    0x8996081807080b00c0c00d1100b40003458503a5010381da074507039090071303c0051060020000c0b0014000100d108007401408070004103c1604115880180c81003039959584498032589066940c400c10b6600400c401444900c822021a40c20050003465005205882c9001080242801a03034210134500d01c850b000050210b000740d244051080040c54103948007540781c642041e01410000b000140030b4140f101c41800030340c081e07100e4900101d200c0c1d171000044100d200e890740000011300045404494a6281100038142580111040e41c1e1142d0322081311002c2c0011039844407014004500b540307051545030904042c031560117000c640442030007580e40707085140c61401018500321038203541c0070510104110078440d1403000720f080711102c1e1041d00c0300f1400541002c08200104103450000c6c000c102c0100a0040304841034020700c0c040c180c988440310032510b40d0103907240c05e884269031440191030342820b0101124040d41c090f07640041e0b1030000608010303146001c10b01d51245011244005440c01c0020301c01c0003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336076223 1250 336074973 336074987
    0x6120c0513091a0f0319620706110706091203020c07210b0c19090e13030e030d0f1103040503061b2502010f0e060409090f050303010b0307 61
    0x14044034007013008100440440c1d1561200a401c1c40c0102404000700b040c000d00080740300740080e00602510342c540c14020986200d000504514410321945510300039600104400080000345885007030f4000d901e007101c0001c0603480301100310b074140d45405100c0c80145200c000b074211507006640106d810800e91506020040e001d40c8501c06062041c007081802c0c103c000f03258001e540141e800548021054034603a03150080b0701d48000c0144048100b04140c1e19001c1c0c019100703181c034081c400003002049070815155038405009040182c00076000161400d5061039400ca403a038002c3c204020f2080813407000c40c1c00c2250884200740410300116041054961110102400c3c107501c1016604003410800001c0e203840d0b028081060044510483d04181001d0a08030707012818100104c0d40c580089484404024610720002d9000c00c840c0d207103584681d0b025804040d0070780c1c4c0c0280301340d02c0d00e410311000000600312680c040d69000b00325140400065010401580a4000e03015825283d00d40000014448 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336077473 1250 336076223 336076271
    0x10201140f15030a0b09012307081b13140a06050c0a08071b03030201140609070207050909030904060308120c040303020709051e040b010303021606120c051309 70
    0x1030a2040e081000842541480342d400010300000075400d8401c0d400060f1070041e000e940a07003e42842d2040c00b6490005601201c00300c03030b40d4401e84107138440c00c6501417014901107901e04007003030700c401c00500900c0c0c07612000300e104a00100c6a600340100460034001040a54000c0c0540c0951644402e00c94034100414000030312880c030742903240464503880c2c2500d8582c400e42c0248020b0000c03d520080006151900319210f00c9040078803045030b43c90500a0180140504c2e9070007521400001c034410703040215440c4d100f080190000d04c011464101805a484002400540c650209000d00c4000755610b00800b00218018845a40c440c0079980c0c030800803403030103031101312498002c1000300300003030300895007200b200c040010000c0c141d0307290340c1c401c2c01100c14a20050140740e00842040b040042e641e48407410b80b8082d901b02c4604c4100d041c030060b40c07001103008402c08500281400004110305402c10341c06c08019262035400c0400146008612010070381090001030385508030f6200003440350140080b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336078723 1250 336077473 336077501
    0x80a150905030d14011e03080f0f0d0204090507030905030304020909100905031206030106030f0f060209090408120907050117100e070f120209010c0b28140f060a061808030703030902010201 83
    0xc0e0b20250386c1c500c01d00c600648001800c0d40350104041c100e4a150034180c8145940085015070b5845186102000a41c040d00071414807903d0b000101d0191803007441052551980800218a5500e5a401b0403000b41c078000d007950410301c200c00580d101070b041c90088483c11441000119114074581a03c0507900b000180810b000c0c0e8506002000400e901c00007452070260003058407800c140950410802034800c041c0d80d103400032994400d100400200c80024444000311a49036025511009141070304c4070640e1056900185c0c1b4180c0c40c07041110080041500070010201040303906913984600700c0e440004a840002244484083c50080d5030000f07035a8100503180d160852924030b601c00080c10300030f41039101800c40868500020004203001032400d02c901c51460003010341900301440b150280c1140c1c91500c21500407480401d100d05c40741c03010076007c1e1100400d4001e01c581070510442e982d121141c118244119500f00c0003074801b009000030083c250203a038000c035101100b800003a00307617083d0b1015015 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336079973 1250 336078723 336078749
    0x20f0903060f06030303010e090c0604230f0a090c05071401200708161104110310050a12020411070c030510140709180e070e150a080a150905030d1401 66
    0x4e41d03010040307030706481100c241c000c0c9a480e4040000e1074a41005240340e00000006401f04455008002d1130760500d03c41304031200b603100078006010300e17180480e404580041003684284150050340d04440300b0042c2c6480c21340e04090300c90312810004080c140f0590550395503142001764041003410603024541c0030b0203210745421082c0d5202e84141c816200e04048404c009840d4004108601c0f061003414680180305200950208406541d50352083c2c80c2d8200c40b201d07100c40092642800041300c4c00b110109009092104055020711000d4824a14201c841480800162000500342e40098018502940060071b44050b4a06450100c03080100681410180c010403c1505540814440241c45109503010845d11114100b24040d1a80b030b41450000e010300305010510f0312500302954414072240892802d0700c1da00c1e106220440811b0702600c80c2c150014172264000c55051840f8030f0691341001000940c4000c90b880d100c1c295000082c0d031940300342e04c4615400e03071508541c4e0001c3c00762000c003401c1c1d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336081223 1250 336079973 336079981
    0x200c010b0907091509080d080a0b101e050903120a0e0f0d020f04020409020f030406060608010305030f0304051005070507060e010606020c042301060c0302070909020f060913020f0903060f 82
    0x5003a03c01c0c944106070340c684a48070160358451298052900428020048070360580000ca40645030000841e94600c00d185006140740071444e1032603500d03250138601d443c0c511020192101924815480d1450b400501908001c82c07401e9440070842e0640c00740e016038515841d03100300880203103104501c80340c1a10882c41400c0060140e600c03840844102c1e58120f50703c2c815504120042400381c022035000051007840030400005824200c40114813491146100304000d07500c0e1070013515891001e0202614950050048240700d0600d900150303080b07401107080b01c0c8000003584500095850403590040001d401160050400c44180900d07041c0c01170042c004d102c0e050078980d00a43e42c0c4000daa0b2580302d55201c0b405840f1507509a0442c8000c4030401010705100d41e103594000e02140c1d0000b4081b0014480e025000890103000e06c20143c1c55580201b07090700c00702103501000000c0c2c0090f410583e01c030507410003401c8600943d100810b03994482c2c50a564071601040e0405d1300b41100107281c0444004510200 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336082473 1250 336081223 336081227
    0x91203030109060f030b07031e02041d0105030109170a0908010f0204030b090105010b0d0b120a030801060f090506070212031303060f060602070b0a030507140406030906060b0a1d0301200c010b0907 86
    0x3075072000c3e123480c2c00100d80402c200b4000c420b11544040321102c5200240206040c819860900805c1c01e10a1681c01c3c0d0382d0780ca106050032141200005032100c0090010303c03414412410042c4600322240ca840d400f01074481e040c0c1d60840300056000c0014560000e402c01c10407503048101c039031190114000b001250705d0301400141501c1b6049008041568030280301701c49a07a1a42004041810307402120000790442c94040d100da0000c0c01404003150914a911764590700c01c141c1c21007581c60140c0810304048840d801d201e881e1403540c641c0202c5002c2403002e20b40100c17022510030020340c020b9102040f2200702280880481c0e460390011001c54000e40414080213003010101c4180d80030520700010b240c0d80d40c0204031030160281602c04220ba100246c0081c007145c0c180c1103540410701a40c41000825510446262284121200c120118000801000c8103a008021038202c0440250002c610b1800894004010a800d203c44106085010900c01101d01c3e09105d2019202c0c820340d1079002a0401c1640 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336083723 1250 336082473 336082493
    0x4021206090601030207060905010903021c0e060703030e19021507080301030209090a020a08010f0c0e21011503150c02010207081e120c0304052b1103091203030109060f03 75
    0x1410700480c02080842d1403a4030a034103d503800c0350040020490180f142c90210302a10b0b80e81d030150014450801c94026800c0b040146071040c86151311540c0d01051030000740b0559410100b800c0c4c081c1a695180304110031010311401000c03044d0918516402c2d000d070300c104581c411080c44034140032207090080100084046c1c0480381541d80459001080d907540100b4107161880c0204000c1d0040c810500000d100a0150030054050049100606c605072664904072224080e401da0740d0f91280400e40c1405000000700d6142c1507880840002040a0301003542d81c00ca103411507032013121111103c9101c000ea20105100d81c100e201038503c0203520b000c49039104c0030b03003134026040f809020941c1001d24900804281003240d542d05104100040b1520341881d00282607003045030300741c90600443e200f8581c0740004800f0003001407000c071400e140807181038004032009449c0c0c1101103610b110400c111892951002005090595070354000c503540d40c100729842c4251501070340960a4100095024070000b82c070b00c1c0d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336084973 1250 336083723 336083731
    0x60f02031b0a0c060503010f051905130e16050a140307170c0a0603020403021306030213020703031d030a0210020c0a021c020406030c06020f120409200f0301090605040212 75
    0x30000400c094041d040e04001d56020014151100e0400c00a001504900071350b040b02c0785404003450556403401406010414031240b2601804e03000340a02007840c25038040340324803455200000e821881004507502d081c1d84000c4503842000740c0181001607103040e10803000a4141d0042e00013241d0344000209541d002c03207001d2904d0408648000805c041c03070422141784c500800034002d5514695481000c2c0c02580903020903801115050b00b96980c0c4ca0ba1805040105c3c0e81c05080c0d10703045203008500b04004e4000c41d2048007050b4983c0c0c1c81d039040700324841c20000c0701c04e58a806542e4400007941e02900d080300e441c08030110035006000c041e03038201d400700d540c0410580580700c200101040c88010100c580912100961040c641500402840301c21208101030b142c0039002c44801c210042c044a65410319400700300107420f0100f10030b001c041a1600002040c40c42d521303201c6070503080d190100d4502c1d004013105680602c004001000300c0326050040340d00608050790f04528046100c405c503048880700038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336086223 1250 336084973 336084997
    0x8090f01230c101a0f04020c0a060506040b0406090c0f0f08070c0c091806111216020721020406060503010e04030f021002070507030b0705160f0f0b1609060f0203 71
    0x419811507055083c02030900c00c00c00c00004001560240000741d649280354140640104103928010304c80f41460310840f00700854400081007000003565a03030001d40001400544c00584440c0740c107a55803143d001d02405009084004203800d84880c2004101d11a550b44060400003404070960b881600280c9035604280e507403402c0310458081d4200144442c0f41c03548014241d5140c84042c201c0f094071400031280640c0304440500c0301901403664103485000d481c015102d03001070400400e1303055000c07500c00b40c00c4107064019070341042d9584101031031001c81080c5441c0002d604848410452034580702c1c00002e0071960070081d0a65050810b40040560000d10040900041440100c0c4080c02007229040180c555002507559520900e1700d940ca80303542c0d21040711144050004203202c5c43c001c03425122280d10912400181003803a84a240318402401410760f4030214074144180803c1058404a1003000710700020450010541d41c002c0c1450505e510000810041c00d91034a5503e6012007141c0d0220300718 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336087473 1250 336086223 336086227
    0x14040803040503120103050c2103040603020c12031003050706020109150b0f060c010623010e060304110607080c06150303160203071d072a02040203071b08090f0123 72
    0x20b403420501d503210303444c00400c03040030380e40c00001000f00001c0c020a5028081d40d225032181c0103102c144034a0f4034400991081c5030801e100078001381d40700e98041c098004030301e81114a102c817254280207042d402620032115a9005500507c02d100d420042d0038001c220610081103ca01f075520350305030b04905003c0111101e40c45951254075696030001c0c41c0302d084801021203035110540d0802a00800700c1d071042c91140d01e10510f0f503442550790a04004c00503901070312544008081c040801004e9400104101c800d841c0180400c0125254400a8150b40340306003541c0343e507200049551480d0440040c0010300840090042404c280c0f00402a40c80743c0280364442084140c06200203420444a034200b8004031680f060320a0480b1b02080407240034285a860f50850100c09059a03803040701e00b911100142c0d001004000c0040c2041d9008540c009224500800710f007501e0340c1138040c1421680300c240c540150105054202d0314080854627550a404d0920011800b1131602c0b0f106407891500300700101c00c0c80 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336088723 1250 336087473 336087481
    0x1d1204180b120d030507021b030303040b100902030106030f0513170912100c0806010807020a12030b030f010c0815130c1115040b0106111b010e030706050306090a14040803 75
    0x10714110007220100c000c10f841c80030044810090080ca4121107100040c803501c2d0041e1250791004000603503d0b04080d02171843c41e5160341b106048050090000c4182100e00d00000034030004901c0618042e0190759004282c2448401911040d80c0c40501030700c0381c08842004000004101c0240500400705004005d80c86d00c400000007401004641d90b84c1c003c50060010046030f0700d0310355015501c15040390f1105501c6460f1000111400f00c003c4070658050780c0b054000c800400d148c417025000140c814500801ca888000000c0386c20914101c007612680d0307458100445035a5000401c15070300c4101401c0840e118041c180011b01152420588681020764681e1036142d414419941403861a02c8181103e10314420000040700300302c0304940581d45607040300000f04005208040702512502c07650018016008905000e240c01e043d1004c0c440e06100c0c003204100201d8400b8005480100103079203600d0f889241a0041c0100c0210085c401e50515140202c1030600c283c41c4020345401c21341141d070303564032652 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336089973 1250 336088723 336088729
    0x206161a100e0c0d0c050f04030c08010c05030609070503220b0a0c021b010809010f09050706030b0405250e10050a090b070b190608010510031401140619091d1204180b 73
    0x807c2060302510000006000b2003404440c40400d002c07900558001c000d20b07426460101c0e541d010984030b06a1003142d0901292189210703402464101c40c40c1c01002c946090304401000001060076411500c0d40c2c0d21504012a44505114000d440181070020300b002d81d00c0c8000c002c030342010180e00036040c80b880c807002c214028002d40c020607580c40740000030404140c09061041d503d110a100314000241001c1d80d009003405c10f40a00c6010f1400040000078007000101107419518807140030340101320000818408582d2220041001d02d480383d180c0ca070740d40c035400d81c00400c062203a80020081a000f04014000620210380056201907030091203c0b000444940c132801500c0554454001d42d800e18081c00b1034200520055811a886280c4940a0840815016080e107581c1d0300240a46582d0304c1c001102800c2038410034040080845207250344580f41d607007410443c0c44004001500c1c04100d28500a200d41c03c000c0110303850b04a140b11785c1410300c0d15100c0710b0b6200609250341203090301d41ca200c00c0151 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336091223 1250 336089973 336089977
    0xc020705041e0c0e120703200f040504031806020f030a03020c0f030c010b010f030b240c0f0a0b0f0103080d020711090901140a06030309030206161a100e0c0d0c05 71
    0x410b000d40240000300c3c1400c0002c0c6404c081c1c901c07552013082c64050014407071800150080460785e101031010359001c645859000200780385044a50020a5500d894119696903c60365115a2103919188032031b03d60b5804007605c214441c3c0200040d076218401c00d24141c0340c0001540c1022905180140c2e5462a194180342401f81b11040103600f4840868100d02d110f40c10b40043c1c2c04800c0a80e9280e0300045030031022002da0301f5120541e070b0024009001340c0e8040f6403408800b46099000d05155181502c000d21142c940781c0281e070307011510381003c0d2648040000c15070b40715802a515141404103541140c96100344c51003a0100299915400039a0504005901c0c20071440003100400d54011450201082070180240c07a0002c20783c031501500140c05510700307100f40c8081d04d0301556010742d820b00316401e1100aa202400803204d2119008100340007a21014120140600e0720420601500749000e01c0700d070700c42c2c00e5003103ca110f041400802500800e0324040da80e403440c010b107001c00e0700b12441c00142d0b42e0b8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336092473 1250 336091223 336091271
    0xa09230c0306070f12020a120f02040518060a050d03051206010c02130e06092e02040803070f1403211807060507030216030206040b030903040b04270c02070504 70
    0x42c0500c81c2040b040c0754220201021480c100d44481495070001c080340d504a00c900d54440000c1156582e1901c0c1d0010390b50302002c002044001c006203055241c800007402014902a04181007036042c0c100845402c0006004005050075182100007006540d0301600600404408c3c1c0409140c103000201c05a1086814070032881c2c001c1d0450f00b0340e640c9103200e04081d001da04825502c0d03125040220740c0b0b0941c0000e4400185a080560100f0a407442005014001444448075186a001d200101e082d010520041036007a1040000644101c100d1078010503824900d8400e84e140c0d00207000c01c064000040b00e208038600d80130b174205842a40c07950860301002c0034404071085107206070540031511315041300c001c040ca039001390200c48103240b0750741c90341c03083e03101d00d000c029000123082c00b0400c0485180030265402044030801e5030308040d240d036400c0358160032543c000c0c28841c12840319084980d102c000c045403000d16404061042c0b85850001035a107900511980c0e00a0760746401000345603801c02401040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336093723 1250 336092473 336092479
    0x115030b181c030504120905090c0d0b1002030403050d030204050906010305041e050c011202030c090103020a170906010303090e07021b0a03020a080f070609183201030b0a09230c 78
    0x1c0c600c2c1c06004000f48021a01140c070100c003000c00e0a0498001d4022100722200100400c41c035655103421101c3c0c0750081515440400d444881101859461055420221035298015030312a4170358109a0f00d0090703481b0f0b0240c24103104100501554640c0081d1a92094083c2004141602d8602d81100c003900c3d15035a15601d0008250300c10200031020800050002c8240e842c00d43d01c510055141c0105d200c15141c00c070502c1070810980e04654000c1d0040c3c14214880d0400d01080d1140b554160340304502241c0711802c9130080d800500405402004040140c0060710840e0298a0590806950740c00900d03100003088800c451040c100341c1c0c900407158050b56002d440360840310794445545e541d52255661902d441d000d110700c04180346100740300c610b04803a0044545416100c5981c41000100701c0c41101e402c10340d0707540450346241c401c4034241031170300314041c181c140300d6624504014520302805091558074905000c1b2020210b04c42c0460007021520055841d410708440c8989940380003050040d85030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336094973 1250 336093723 336093763
    0x1140706020d05040b01150903020d0503130605030f0a02040806390309010522080904060e0705090307060906050403030e03100e060f07031b030203091005180115030b18 74
    0x2d5545054000320700a503c03c15854082d640c8504244060b00d488820240000700314000410142c50813201d80c003105802541500d2804c080700a83c600c1144003074005101041c000410703c281003905088095100004250450070320303013070902d425150710006c4e02c3e5a401c02c800101e045241c0c11804298a055901030361000d100c0c00440000920a030000c943d000625442c00c400500103002551409502005054280800040b196140c00d00358010494454020b40e030b0710404500003a0003070f03085020349441c0d2551a2626941020103240440e070fa00040100301403c80300300045a084420f5030240e90349401c000d40c072101c2c10340c040780c50002c0504100003001d080c0102e5180d183c401081030b60003104485850b2403982e40702d0301e054094844156000e007407290400c462032805807280d400745030001012000e89e400710b80305100d502e00b911400e8424030f410500d0030741e0030030b0345000074800c01d508645191a8800b11900e5134541a101440c01011154022199045c4c0030846409000d404880c0100140c622 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336096223 1250 336094973 336094987
    0x403120b040e010e010b0d0209040b041416051918020f12040b0105130b0102060708060303090a03030807021b0d021203040f0e010f083f0c0a0314180114070602 70
    0x38007078150715060329a5546002c07008015410301c7d010b146000c42d0094036120203910b8941c0e54003801d160040096410030f075405d814034810141800040d11114003448088401c0d4104402c00040755503000c0e1100803408403900401100388590a002c001309808100143ca03462107400d0726029101b54092020424500300400041110342d00c81141a26400d50300500400d00d80b414550407206c1001d1141e002d6841607000130303c403a10510142d54030500140a4038180304104c00850700380201030700101e0100e003482080080e51581040548000301c0998100031840612501164a101c402007010b4020704a440407004902001c1007124024008103005c0380166076500d4015041c0b138428003546441107002c442c002814000041c030045a6005681707503e900c0303074401480248510054409044030001c0c03d120304550703031040c8040c2c089079001002401d0280e00c1441e005081c1070a4551a600200050000101c100a8907502c102002c1080c2044441c050083c940f1040d40d00840400034501c40c00000c0313107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336097473 1250 336096223 336096251
    0x70507020301020705061006140f1b0f0f0105060d0b16090b03090303041502040305100f150b1206181801020f031509070819361a01030201080403120b04 67
    0x1a40707c0d203c00c0228844940e2606000c8802540200680c1108403041c40f414118002c02d00c01401480351400208a141c104045a64101220300a92181940040c546074034501001c4c001c45501031800c0f52741a001807126900c3d04184000540303802c80a007210580e03540a18003445541018154107001c040d22440e12190072070b03072a401100c01b120780b591050840605c280e4030b402903d003900c2e03202d0302034402d0a00154122001b4469401e000c40c500b42c0b1044990b0350080003002c82d030b0107009100095030786c4001070115002c00c04400b8101c1030080300a9007001c80c026000c0c00d030664119a01d0110b00200b0410b80640e24060700075040d00f103a00d42070000c14400c81ca845121400800d1005035440000e40d9108032003958043c0c2d04451011500341084000504200240e00003e000004520030360300350104030350300080c901a4244111010004400444148101c40d1480c0e02c1c000e9501d003150f0030960650b0f0008041103000b41004040c003040d11000151058203400c4142c010034080c00402908195001c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336098723 1250 336097473 336097483
    0x60408060106140f0f0a0c06060602010204050f0a1412030415110d020d0e12010f05040303020301050306090d050a08131b1701061a09010513031a060d0209040b070507020301020705 79
    0x50750003081501c50741c0400f6030000700c10b5508200624010500301888900010080d612140f83c180030010800ca482c00011001e214000c09481ca95000580304c1c1d0420041c82014010b4030b80300380c07051881403020132201c0c0010a00302c5907680240d83c028a6080380c0105a840c50040d6001101d01c1407005c00c1c0c12045036403203990300c0d12040d1900d0844a0940c00a00260b032120f0203000c00368002a15901c1a00350342c01c0401e00124001007240000400a402140c0c4404441007943d0450004c0d40000040000d0314040240395000b00b40100a04410031224402030700a01c11485801c0c00d0009850000f20f0752030824244034545a000305004030203c500440711008250f140c0515031200907042030000c0c2240051040c4001d0ba11068140c40700000100c501c50159084030180710f040120401003242820340200000c401184030760443c4440c0d00604010800c0c10000401d400c1c0100e25001c400009070340c07000495078100d500071501c8160b0b0727100c02004403040c4c86403c0b0081d405600005007082000720000d1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336099973 1250 336098723 336098729
    0x111011404150c081b071a07140408030a1b060e0109020108090115331107090209130f0f02070c090b0102030901020703060f0b0d0503030a050f2802090604080601 71
    0x610703070940d56850201c00201c0d6010300e203d8000800400004030721071380c1548038944212110b00100d00b00b0540d540d40c2104000c5d800c0003290440f81d07807014011699006080d102116142d0031b40c040c20541008280c40e50307400381026a40420815102d012242c000b0344064801168021905001c001202070005010f030090410483c00642124001410100c0c18410320014041106009800602c0d084038001455556201c0e05851404807244d89910422421125034040781515401804024003101504000c41075101800681c010070900c0c403540c0d01d200c1d8050b0080c4140b4000640d84502180540040c99044601100701d440040e44c40b05105c1e82030b4044040300e46860051000c82c0b0700f032004a03120f004404580f40540d014010070720002e01c00c4e802c4038140c180078400024104a08000007085103103414001c0c0d1b080d803c00070901c05480114040c143e440f0300440713081980b0b801d101e694102404c20385460380080c140803040417441c5040035012103503c007000400d41c40e1510f4440510765294007081c4 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 336101223 1250 336099973 336099983
    0x50a1409011a060406050a26010305100f2a0e040f0e1207052805060408190903021f020307062309010e0c1002100f06090c020102180402090111011404 66
    0x842928114600802201c0940c3d01d1681d646d0f0030005059400e0b961503c43d51804c880c1a41c0407404c030603028181d10341c8940214000d40041030b110810310340060813104201c070000d480310306100d2a04090000c1d1098518903030501031174140404e0407030608882c014150080030394040e0818050200c41001c942004e00e00d5007052080d221404c80c60000d25190344505040145603403c03c000365800301c404c07008814103901c605800c011407288155601400d011084800301c5e0541d80100e00507101403c50003402c80140b80608201c0b03401415500001c0c800381d04d80c818403400f1505215070684c050310a1083e15103180e40075405200348203056009030151312021306a024900b44c0300002030700e92441405915400741c904070140c41c071040c01000340440b408140d88940d0030b41c400e8400c0380441d0891446001c21100d4040c1002424034206013003034095503031444000045a005224000803400064a080a0351004413001a5201c0c5c5420042c4c4000c2e06080c005502d9502c3c102040c1d0342140c3c031035205841a4030178 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 336102473 1250 336101223 336101261
    0x12111218030609060723030910060518011502031303060b0f01050703091a040e0906010501020c10050f03060f06070506070f0507050a0212010f0207140c09090d03050a140901 76
    0x4030500d07940b40e42c22146201c4503440140404ca401e030150b005050f9840e0300c0840c4000c1c02005410481141d0300a803040710b090307803203d100c05040c00d440c2e1080da03020b40000c0b10b031000e524911003403a0a200d0300600070300051118415800c00e81a000301308551030040c41410140c05659070342400b4009140790840d0300d000f01403220503400c066120388101c402256042e01c8081d00346040a40c00d82c011108400c02e610300e110108404600404c00d031030024440c5044000424066040800090900dd2182d80090040c44401c1e00851510b81000c10f860903a400c00100c05d441750340b0f00340082d00200040c503440b85c202d80000383c1ca1051000102d01d140c0702c2e03802501c4410320b19691a104444512458071b002d4034940103603d64000601e003511205405e1540ca10001c594169988160b00c1203a00403041110010811220030720802c0c0140241c007101e0508482100c5145020352800351228004560340082550762400100c401c0c001c3c0d840b0031350f0070404000e0401d491400ca95028003e044423902418000c0b40 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 336103723 1250 336102473 336102517
    0x9040509070f140406031a180705010507020d0c05060f04030b01051504030303050a0906050a090203010b09070504030f1713050f0f060d020a05390613121112 69
    0x300140200440306106500c94034685070a9024002100400d0b000e40c0c0140c4512001002c24110516070710400c00c803103400b000a00340700f5019090340102d80e8140d486908034031020070441c1e801400703556160360140d0700c0214001d450314021a24241039000254007100101d040341c0741d02c88050141003502e1091031903107100d988900804c040000440a0106d40942c100001d00c00284690001d9800000000300441c00121a9546100b82e4000711036100605907290303807080035407030309000d6804542d9090304d41082d1401d000348000c0852040340400781000d00a00285c0302040040c071040145410580b115581b01d00d403281115100840c280f18107841403152114040052034007030a4000c80c0f1000600700c038601507a510341d076000307500242c442c4401d2200c00c0c02650074018a09443d0001c0ca00c00d5100b40d817500b10414080c010520407440710003d1903100034100030340655500d00d60301d5031542000c0c89a040c141e0f4018121004249502c19401c540901e81c044071002c03ca86016003041c5c000c528507058990701d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 336104973 1250 336103723 336103741
    0xa063b01080f09120d0e010c020f0c040207020906120f030f120f061008060114071109011e05150c1c02070b0a090504050a020f0c0601030b0f040807020111030d11090405 74
    0x12003a11180c00a13081400c204142c4803041c0001e040000c405000821180c039540007450840b6608480340005d60060b000c00383d901320081c0102000c4910440b000c508000141d0086a0307488002400380d80103c0a089441d030303691008120b08030818000b08110307561181045207801742c5803c44019201034a0640c2c0100e000034100c00191032180101814480700340131041800c0ba2111400f4144605010444480220b03e89024004100310380c014103c28036095041014000c440030140d000408103142c940c21000a407a00070680c0080702c4045030302c50040007149001111605c122001080a4440e52241c4507050f1002c150301c5040c68115000d84094551703a108000582c800d20716088001290504144601d01d0664004c2d41c02250105d401401c011118110304280c4d40011070081a40d40194010410441412078155001d10202e402c0034060619550b0b402c01c81c007400400034107001200d184202c02480c10419681103810410062142100040c0043c1c1d036a40500002400350782403100282d1030b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 336106223 1250 336104973 336105001
    0x60109053907081b010b040e0312060a052107080c01090b2104110f15041a0412080c0105010803070c05010f170106051c0203150d0f0b0c0a030f0b0a063b0108 69
    0x44070b50b8009e940b500c00c850510049580008089603842100d40301c1c00300355030304c3d5a0381640313403007010310301642e600703291030b600c462030b000e6154042003160780314401544403a40e021010404072010140801c5e280c80580c603840c5c0c0701d42e000c6a06d940d01c68031407034100f1081c40302c524042000d42e2000c0c1c0389540e90740b9405051120f510360404500080e00700802c0308205040c4003c10340c078003032441c880707507107080c1912146481400c41c203240b0f042e01c2c0b4540100d1842062042803003004c0c0140b194400840c901400340d900d40d901d10100340700c7c643c113010304c0c9408402403500508400c0c2c424205425030317504039a1615030140c0181c000d01c07250034852041c0c8070000000c50040c42103902400c8981400c44400c80b0400400410149000d402c956203524075130548005424051242d00440442c11040d488501101c0000d00721060b15802200450818030382d20321644400800f0b2041d00e081d03203000d906440c0704400700c0c032303060f08171062109003880200c920744401900c407500b010120009989041c202e48500740156400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 336107473 1250 336106223 336106241
    0x807060b04051510030b1201020405270c090d02030d051c180204091502030906010512011b030e03040b04030f030e030609030f0a1e02060109053907081b010b04 70
    0x80c3e01010003003600e501e0070f40d20210709001c580c0b6001c601c0700d070400080f691141c0503002090440c4e40100d010f01061400000071024804941011407060500d2141d0300c030a001c01504002c0c004800044c40c1c0100e132120314485400d160061304540e1880c9581030018400d80c048004d00200407003044150000303089502a00183c007580d0100b012101046400300720081c007000300122a01d20a881c540b000f8960b0600180d0701c40c104c070501400c00381d807500e401d1000300c00d45001c50442c503074541038007008090710040e40303210f0303521103480d0005202540742c041c286507124075001451b0aa02c00708001040050b102d240c4c2d1140c07403113070391030f01d0b02d50512a060641d202d00c00d0715040486d0f0402c0c0801da0004011602800314031032545030032142031898001200c5404822103c84005811201c0107109921040c022250410ba440c40b40c261403880c0030201d0980700c15408002e50001c0c110300c1e090f680c091080400e660303045402210840c0d032800000072000d1011204c6080781259400c1145030b0f002032409205003903034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 336108723 1250 336107473 336107491
    0xf080a0f0602030a02040e0408030411010f020a0609020f030111130506090303040603020711040c05030f0705160305130801050f090f03030606090415090608010b01200d1115040807060b0405 83
    0x440e4440d640c0704007075000104071403241c41d4284400203074055180c54a40c0210b0040c5a220350328241800d00314550000071220368107128841031f901420f1540010110400ca402200005a01c5218400905050204000e50f40d01d503080060180c03003030020300000c041104050294481c0281c1d00c20034400c1c41c1c024000c0855143c1c00030700c420012a8025002450218841c400c0b03400d01424010002e0108d6080300e16800002d0004002c0140034000700c5002c541003541420164200b000306455003c9949280d58001c2c01c10101203601c42c90415684550405018032400034089031078405030750840e05030101c1c1d80c1c01c080e10541c1a0310f80f0302d480200c21640103000140c52030b450100140c080c04082e180000b05001d0707445030300c640000c0301c4040d4424070016007030180001c50101c00e0040010b203c98840c03031113403001c4040c0c0c1014003140300380060000c083c0942800e082c510310410892803414072141c4520b11054000f080e04000400c041c0741d0003045520721440c402c0261804035410701c03040380c1041704c103218 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 336109973 1250 336108723 336108743
    0x90a0e0105011a0f0310090204090b010e0d020307091a0a0303080906010f030b070503060d06141503070b0304020108100914060907110606061b010612061103070e09150d05070f080a 79
    0x3120007881320007141d00c400300b0b490625946075140d40e85c1c01241e009511003a01c442c2c1c0c603140202c0035070b40079580d81c0210004648243d82032000390002500c80c00d141c450303c40d0591342c03410b22569160400007820b40d060001802a07a04903500d007005411040120f5424840d400b81c2d400115000364450b03039540c2901c0d041544a41a5514007030300383c5055002424840c1c0c01394804e00a030000a007c0e0144030840c0420f003c017041641031203501d109022001c8030b2041d101c0d8020a00a10007201c00e5000d0342e03801902444c4c000c64649545001081610a64005282c0c1604141240c198414040c464034040c1505035094001d507581c90200f12404d50110b100f070602c40c0c01c90404260340346001c0b03015004d00034410342c5803507241c0a00340029086030126405500201d90000d0400240081481580800384046072000d00d14131b081c400091040f0a1103c041d0322403420074022810302800c0c0b00d600d91446c0000381c1176240e154264100701303580d40280d111704400381c412000007040802c0d020a0400d001ea5010044003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 336111223 1250 336109973 336109987
    0x12020d020d0810050303030414011a030606040903050c06040606140d0209040201181e090e0705030a03030f0b100206040506090c03030a0c08120705130509270c090a0e0105011a 77
    0x84282c48050480d491943e4888004101c9030f40900046015610030a0740c01ea601c2288902c690949110285407030782a03080321701c4224a91008070316103501c8207049a0009103a01285000e441a0103200c103aa1180d221320310802003000080d60021094401d22804002c4201e4004100000102813490094200c0c29a002150041d409195400000324582c0b0305807002d42d07112445202c210040e000055124000c800e81000203034212f106903140b0103c208082d001329410980460340e5072001010050816580d6185c2040101c1194842c2091764401450510303071004505000395280c00c00d80f403d45540c0500b10124200070300018000107a0fa03000307009982455240301040d12407103007031101030315490f204004054a40300184c8106109a13905d8030f60944a84903800031940b03810042d00030500551041d02403010b4400c030146210b080c84442d00e81c0001004040d01c036942800e40c0b495005401000020511000350400d8000e45800380c44034000708120b82c3c1e00c82c1030014100e8940600301064400700401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 336112473 1250 336111223 336111227
    0x4031106160308090c0907031e0c301401140904020a1406132403020309030306040b030a1b080d0504030b150a03151401060c03090504020a030f050c0712020d020d 71
    0x40ca84c02803609041d503001315955804640f0048040340e0150009a517104c1505a0074181c514000b80b202c100d1204101c401040313540900404664a6608001030841c2030501d90311030308000d012564042102d0501403544880000c840c051801c1c05002c00070382c040101e50380c0c03e05042e06201d1207103400030101d1031282d180c584041c1a42c00d8150096400113001c102c900798a00c0c24503e9100204900030300d03620300781565503e410140110f000d91404142c010000d21904010000c1581e4001c0d000702c80c000340075802c03000081d240c20500500104042202c2400d00e1041864060100881d491a03054030012041c2d880219618030aa000c0100b149003004046516455480807500714058007a1191003403503140d407510444100c0c0c0610a07046240c030784811885a010184402e4010160343c01c14000c030040c1503070080c08002040c01a5806540d0205078903100601c20740000086003c00e0b002000181040e185101581e0301c450006e0314281116070301c0f100c040348001007659400380c040d4060207103001c82c4041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 336113723 1250 336112473 336112487
    0x10212071404030c03050d0305070215040803070903120c020a0609050114070c051c1217040b04170c0a1b0f0e04050a060c050306030f160902030c0717040311061603 72
    0x21407a501091101200103138040880602440c0075400410300070030000340c01401d484005080500719000f40303000030310000700c85500c6500580c2c0111419120f0ba46c03008101c0d03e000d0303207a0000d0103c0c0018144490741d16045500b01800c5402500c0400000e500c071001a98500028801c95000608443c0c0d5400c07a05401006406000d11404103508659503c0c80060000005400ba416441c0540c101d28801c01000c5034400008240c98200f0b10002201150580c0c41c1e03080007031003d0f1001e4185400501000080d075601d68014508110b40c0c1e446800d03c80e0203503a00c03a00060211822600390140890700315a4040c03900841d480743e00300c00070041c1862408444924013600c1142c0e0f502c45d03e405140061258042c421740c207082c540d9415100c0c0740c50000c0500c1c0c404150b80580b41078109006000c40e140f80ca440700302c02c0d100d588402503a2030322500c0341115148180340c009000300e0250750400702c00324020700003802100d0048030f1002004041e0010403e20348154040038607813481040c5000002802904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 336114973 1250 336113723 336113747
    0xc1505041211220b041401090903021c0c051501050904150902090109090b1605030c070c0e010e10080303090a02100302070f050309030d02061504390f0201021207 71
    0x1800710200ca150010541611414441003e1040800b080003030401d968400d8810f07078041224240583c5242c00c08004c0b0502c3c040c020321700d030300da02d130f40c0c401060600800402c00204452004969134882d4500c0090401210b560112072034002c40003150110215400c92506981005004c1f26517a1241d81c0e51010741f800c0d9500400c80c1580314990800566544c005d05402040701d0703940421400b006141c80442ca820061080c1c10301318103840c0000d84168003c4c20744e07900000c140f04041d81d0312050700b000c20681c1c1c0250b0060300d5107055500046044900340e1801c03401519040c101c11a042d03111980e5130707128001110040d102c1e80c4016030f000007501e03064031035148401540c1001481e0100940755004400e052f84070a42e610b610001d424103e07400e040040440707101c900c0c0301601c624140480b4200428240e0704040e4071603038131580c103042e0600501060001d044801d207140707000c203104a10701d14121046880380002069050383c0c8600d034640180200d504201b0085001304455491141c02d8074a84c00d000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 336116223 1250 336114973 336114983
    0x129120a03020d170f01170f160501030c020303040506010b13050d230f12030a110711011818020a0201061214061b030f0c09060a0206010510091d09010b06040603090c15050412 77
    0x11030700100e806010300c04210858103280c08440c9c0d041c100b80000d0192100903d00400f194010030030000414408516281510464142a83d6030716044421f4159100d07140c01050f4083e10300c111050401041010410064114407102c5452002ea49021911180e90320350002081d080b2040b81d001c030a4007240190b900403c4c240000403400d25819071000590480c502c1211200384c61081001c0079a002100042104000b4214180081c2040704561000560311840c08545801040c01c09800e4002e4000e080500550031481c0b8815000d810502c0c50500c403445904014003541e07021072607540f00c011145907400c813855001ca2a40e11076020340312091400400341c2e00120b00901600c1c0e15565500d004201000c142e6000b404070f54106020440c52a05205681c018400342007c100444816000d4100281444950b003141c5903035109101405000c03020200c2e903014a002401203085c1c2c0e0190301c101c8440b40606011808103845000c0a2403261110152502041041c007007040710641084580328140e1042d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 336117473 1250 336116223 336116233
    0xa080a030f050103110307090c0c111c0b160c080306010f021c0906020708010513021002240f06030c1e01021504030305090f0129120a03020d170f0117 66
    0x3607841074086510a13082140c0311401000020f01d01d1a041107088041c201c4002c00304807141007510050011013211100800b01004130000410980c3c808140080d10900c600c642c0c5461036003442c2c40d006c010821224003503485545201d0414451049a40c08200c41c0c0c840b40c8945123840307140040d02c5040600200108610a41424103000180d0300042c42214074203440d8650100d08041010f810903026401245c0745038946410426054581604068884d030162002f070780340100c1c800d08070305010009110000c00202d40b0444c0e4800088403036018840c1c1d29051040d0301d00d03104c1804041d1507021007480c155002031146c40000001d6005154840d40c190140119204d143c1e01c545503803c04003044505034042a07943d010030840c00c2c418805d810452541000070840c0f1654001a4011580040d101568080034180c40c00e50342d0715641d242e0034051624801f121a0041035150096030f40c0d5001030300c0400604130030030b81e521100311080a103000355644601c50801ea0300340070120a0041c98500c1042c22403080c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 336118723 1250 336117473 336117491
    0x7050109150203060a05010e06041e09020f071109190e0c120708061003050d080c0f0c0a0606060c08090411120a0e06071d1302360607050a080a03 64
    0x25032104aa03041e50600240c0ca0b40b03810030811094000640c4594107000314600d40c503a460340d5410494040d11030304070b2500c5486280d140c42c0b100300341154002d05805407000440500301d02d150340181c980c1e20f04c81c2c0d03281540e03c1d060a041c07000c4850299030010151142c0203002d08001c1c065007081c1014024201240e06400170b0fa800179081c0184405003074416007090a052100c21414010141c2c02011440800c600f1403641c2d81e0140d0b50583c030f2880600700180e403004500d081e01c0480450f030311441d00141039620740110700805500c1c3d60290300c0845c0c242d4901500001d459004041041d401c1ea008008a4140304400c0180700160000420103d95907004202010101c0c2402c003415015040d0303c200000c0d10f51818018034580b002c058940390505ca10f00ca110722080f19095001c5d0a0f03c501902c0b200031000d08408180081e004001e0020001c0c01c0c0c40d40c00c88201c81c1b6074200c00340c04100543e41105411044400e0008600c41e81c40090b01c00e411818030300b004600743c0f80081414601a207000121018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 336119973 1250 336118723 336118733
    0x910053a091106070b010503070f060507032709020a030b01020c1305091501080312010812030103030e0d0c090e1b150313020d0c030b0a0b01021e21032208030103020607050109 77
    0x12010404940145c621130052101d41010010741300035000282060444508020015219005d00d140c003c0030040c43c0229035511060b08620380c200014052030b5003102c00e403034101c0c020107074110080303090002e840d10048422a41c400540d540040c2da02070b00c40014150309074421406803100500c421090320074480034900020440040b00d0003000254003540d100c910703000e9941c40300304040e40b04800c1680000c0036041c116a601e400c03a411a941410005100a2880081403054010041c0904007200c028000100307208a40c01c80d0940c40710301400e4035102150701d01e1000e1500312420b0916000030019000540380d10551006581208081c40c400350942c807964000398195040c51000c17200002c0c040b004004102c081c0303490603000f04921906101340c01c10140000d64a403e400321185c16400e106070140502c49007807011a40c9031071043c0b480715003000300700c00442c0541e000b03131100c4c04445240d18845c03d1200031008800301b55940072404500d144d20f96000c01074640c120382801d940319542c074444280010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 336121223 1250 336119973 336119977
    0x30c1103030a0207150204050a121a1009060b032a27040606030207050a030318020913020a08060405070b03150405091005090f0601030f06020910053a091106 69
    0x2c0c480040160b5582c41c01d1a21415468116018003440750062205110b0381c1e451107010030650701180500701e03c540507824116500564904a11001500b20003449421800107500e84182c41007040213110442e80d41c10011120702c8110f0b100800100700801c041e01c21840b1000c0346042e00040c0900e2800c000341c4e22188000481c0b01980300b0040c2050038104134240c100b40c00390300000d00007400d04506020719074507960b44960b10340d5401410150741e44210f12000c0c0c03c09054100e00c54001d1300581c01441d1a40d1143c00340c1c0c0801401340d101d80304020700003442c2080028101e01c1a644900901030300b500d4059030403a243c0000d003d000000801c00e00d03d503400c2d01c607031181c18032441c000c01c010500100e8000c0544115070b005008020a40c0007414081c0b41c04100242842c1120381c00b41c0951480b040728208030009018007803070035510001d400c10f031890386507100b406445806070210b03902440c0310f0b4880c0030340e600014021188846e0074410280e6001707807226030701505419015125407a850302403100000d44903 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 336122473 1250 336121223 336121231
    0x10605030d03051905150f041808030a05160203041215020c03130b040602150a15060903120e0d02060705070306020c01060303090f03020f060d020903010f1d0d0f030c110303 76
    0x10f6501e00070071003211004071101c0180855100f04010301c0c180b0540030411000c0304104113003d50040700c2c00300c91035210380d07015030182c203503944c40010313a07580c1840c10203110740c400d5609507070f041d00f408046100c4082e60b82c0c220840705030707940041d0300d4149040011842801e503104140c5425074100910142a42c640c0001c000590125002c0c69661000c0703440711010000c00e81020b000030340207000900c15590005101c884000c07250300021020b130364030010000540351400c000781000500c4040000c030560000f883c46e080c0c0b40726003034802100704084c80c110381c00c1c03003014803c0f5449239011412902500f440b40042107034900076004e407546540c41e501d5035001e9a00c907c2110f050747c1e56548041050550000380900900310300c4111421541c03640d000100c0302c1c40e10800052150000003007007400d450480d411182141d40250003400040e0034154a5070081801240202c009080c0c1e04600100f80c80100d80000300707121586a01c54140c181c2c6004130f00510702c400c8660305011840074050049082000030310b1203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 336123723 1250 336122473 336122477
    0x2208090301051509090a0b011809020301110a0f05130b03090a02030a051f02041409090a15020403150207020307090c0201090507030b060111060f070c0c0b1206090c0909060d0203010605030d 83
    0x21000d0107804c1c0004a44014000d00d00b41d000700c02120300051490710385504441455801c00d4006040411a000514030394400950543c42e20f9990020749442c4005000303015803e454404450048240a483c1c502c0f4400310900e94112a0506100c909244409190400581022940c000d411075011900d0000c071010103840c694000b9441e41c284141018691039030864144055042915045001146aa42d400c07464465469007001504c4207000b0400007082c244c0140c001c0e440200340f06258402544940000e0b141d5400710500040001ea50340220b50f402a0b001e001850b0f95480c0a43e00c00003845509811030440d5203e202500c0401e40400c227040c00f450003010402401d082c201c0c000f5007006840d981000d071903040b0300304015100b840750803480d0384142c4901b003402a428541c503240b04243c42c01d8101c042103010200e1303034a00c2071142e0303144140300c0d5100751450141c644a0040d580c4c0c150080305000c40d44110f0020014001d8144000748000d81440600003180850325007001a0410100c0b03850600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 336124973 1250 336123723 336123751
    0x151d090105090a0305040e0603030f07110a170c0d0201110a0c05040e0105100e070c121d0f060d02130b28080601050d15080304090204081203220809030105 68
    0x90100038031840350010301e90801444140d501e0f90b03001e055806a84600f807035810400001404c41e840610031070b0210b400c0c5d4034225075541281d1905000200d8080103203070088071500c0f008181c1804036110441d0010310f240040c103003080d0103010410380a840c072504a0411511070b6445c01c10381c104100340c04529100b1400a000032381407900f8001102d0b00c1080009030f50381440140482c1d91500b5811100f17469100909030700c0b40d80c80d400c040d90032075211000140058032101c0c041b00d1319a804841501c0726011a060840460404c0c008c12150110401003540e11400800202e600d20041f235004ac106450020380342c0b41960780d40c40b50101c07180c002c804008100055200c1190100840714021030700041c141c1051400e500341080000d019000340b175204454135540d0461300f0790b1049422140c50007490160121380c5d8581d214403005001c2d4000c0d100303402980c40350300032402415480d0400e49110307192407038040c160800f400c00400c1480419590550301494200300040c41d984003801803078842c50b29080144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 336126223 1250 336124973 336124981
    0x506010c120c1505040f02010804030c0804090516031a06091f0e1504030b01050618090103231531110a06050a0e0f0406050303120708180c04151d 64
    0x800d284110701d0101c0443c52420040000042803121120412a020b20f0080d130b455440c0d240a540401c94141d01a11065010400081c3e00c840c607044a442542d54408070b8908540364901601500d03061564840c224640105014060412002a09699a00030305403107010440c041c448000b074065518604c005071a66915281c2d600f41030b9080400d08001142c56442d29182d51141c901c4880306004641c840d100000d41c1d10b401c10150350032034402010041c902d841c1960340c4d00c1c09000454640000c0015802450344a181849c80465900806200200601c05a69418241c0d074408124402c0c401e0740100c1a2001d0315140031030040102c1c1180c4074503100c82d000d200780c1c420000390000a520000810004100303e0f60300c1d070750003500250f41560030340340002480c204a0024010708542c1d0003d076018070010a4100700c91002c480614002c0c29942c880b5480340e00c441d03214190658141412101c107034005440c01000d803e1980c440c904901000882040f05034407400707850010581c001d0456030141d8164248 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336127473 1250 336126223 336126233
    0x60c070e2805090c0604030b06060306040f0e06011806121401020c0d210e030a0809031b06040b07020708060103030521040501020901020c03030913020f070614090601061b060506010c120c 82
    0x4135082260031034409013010320b1365440d141e01c504018216801042d0100200e815a11150070ac41c86400081000f4000b02c0784500070309039502424460804941c2e00300120300303480c03041481002c0580d02c102503040134a41141c0c0743c400c115808920b4000807507500b00940c00d41d801040c40f0a0702c00d0703091559819512040c10b00c02741c0c3c2e88856212100149882c1104402c403415000040f24030150b031070305281900d82e441184550a50080f0b0f52401203240ca145000c4003a5040440d81c140703c0c61042c090b4401c40e40741e11508036a039024a01a14800380d001360300500100f4003c001400000e441d01c0d040107060700d040c02e84c001c5655002e0b201210075a4010412080940e010f00415001c0314094000394180411000082c504a4100d4440b82c0c416500280004000d41081c00b00c401c202d4010500740b1810000c0e00c82140c1744503003110348071160f01450740003044442c4545858100f0800c00340c62958926603e40f111300040c1005042e560500410390001c100140150984c10f1000001d40c64a035407010540c10300c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 336128723 1250 336127473 336127483
    0x71e06061509080d0806040c0e03010f090c0b130e1302031905010515150c0705060403081b122712010534050304020102190b0114060c070e280509 64
    0x805650f03500720701808603039039a1001c003560b40700408840200324200000750035581340e42440d032296015420140354130f0205100390405501c40340b0884101c0b104e2503440602c1d60b030a0042081750000000d80c1442002011900c890700c0350012251224410440b11650019141600c11101d501c1e516138104c0c01c1506000080c85001c2d030002070810a4031503500321038009000c010502031032071608840410300d0090207204010400261101501c01680c1d9926410804901d0700f20400c1d681000c0c2151111440c02030010416050b07072101e01c44c026003400006001c0d00b03100e460710146001c405a00c1c0b03051205594408900f041010b03500400000d0f01d040c040003561000c0640620501c9002e583c03d1180f1104404540008008041b403401c0c6449455074130040f810021911114030b07000010300942401e2014945060307049a400380349061a80007504140030060245160707200458025810420807410681515540071064400c0c00c6040b03084c1c0307080c9401940031010f4109040342d981040021034401085 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 336129973 1250 336128723 336128729
    0x30605090603010e0d0813081204021c11011b02030109030f18030c0e07110609100609050105010804060b0109090216120c0b1602161502060601080606071e06061509 72
    0x80280304400b9555501c642e1440c0c560000b004000c6c04034005808500c15940400840394001000c03a9110143c40e5820051801500c0991040c5507807031071f000740020110003000388180e020101c5e40328105440015550010100354480044265a0b1882c005940c00c0c402c00d40f881d44280c60b11014407041000c0100740203040c1040c8441c0442d0100c0c14008034900c1c1094108a4010068500003603582810490740100e28400782d907464071407002030040400740490071601141543c0b00401c6255600d44007102514401e20a140c082184100400c000c581c10f90040c00c429a010706010380b025507201d020710101d9000710300000342c160061850000700304900303070b00b101e1600c19850480c64203d4541c8600003581009046140c5003028440c01a10303a41c001c0c04901c5600140c2d500c00320140303560305201034001c401080300c50f005008460010f1000c0d030045070080c0c01000d025001038201281e03940e0f500c1b40da480034400c01080c03100450599000030858000c4602410390306191a00b07044042e0390281c4422402e030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 336131223 1250 336129973 336129979
    0xf14010b0307020a11060c160303080f060a0306090516140f03010b01080705030907150801061803080415050d0609060302130e0607030513021021140f1b03070306050906 74
    0xb0700090550000340e070380906030032000701030354216170a00103102e5100710180d00b9000d029900400d00c0080d00d542c0f0400031039000c1c0e03d81c84801e0752400500c41c110482118081e034480031180040c0302040d029440100307600c0c45002110108005034024140d05001d56100800c104501204010760303060605c48000907200660081c010101480006410700c54010141c130104000400000c04840c401c010342002400c4654001560400300c4030001e26400302401041c000c03c0102c0714103842c1b0350002c000711003100e400c560001d05003804c1000e1750a05884898405d020050140003a04842280d403044100520301080d000943d20324500c140100c00c00a48003042c0c644c2d1030603003240095540483d515500007118580090300f5550009400324600c0c80c10301c0071350402800d80d406403480750060310142d18160100841440405450820003e440440b03600c0705407030b00c1050102e030000e413650b640c0c0354100500c040180d00300300003000040001d40080302c00e240000d031982010803017030418810741c5030001026 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 336132473 1250 336131223 336131227
    0x24090b0c0405191a090616080901030b0f090117030405131a09040b0105090403171905010803070f06020c030403050a060204060e060c060f0403051303030201090b06030114150a090f14010b 82
    0xc08600d400c4a10a104501131800001038203c981d5620301741144c140080c10261a01281c080341071114168100101203400b107407610041c890149024601110110320040c0055940d81c00d0680401012404c0c146a0081d40b009110220f060b5031404000a4460f40c60341000a1108891044582201e5503030800e40c001d498010030300c00461040300c00d060560744240c1d450b06143d229894200d070304a1820301c07020304600359003084c4242900f80e6500340e4000c44250b2401e2000342d8803012030307940700d129401c0020729646240e5201000210785070040c260940403001581e041641c2c0f80c6519003070268002c41220240e500080c1800050b81055803140710740005d41d541414025080038190340d4000140502a18075442d90006082520804c01c80d200c0c80c0c0003050b00680d1071303a28900a40038000105088a0b003000c003e00050301e030b0405110703007800c003d4240c241500c1d070740380c1e14207903451000040822038101d40c2141d000309010001d8041d0000800700c10400203003040c01000c1c1202c0900060f0840501c00000b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 336133723 1250 336132473 336132479
    0x15160203030a180602040b1308120d09020d02031504060c05030c0a0509032b0909092a080a030f03051506030606090a05030106030c05030f01020724090b0c040519 71
    0x40003054982c03010760400001100c032080310840c90042c1054500030401d0b800024041496040c850180034042c002941c000d01071920342ea841c0c0e8075002c1c4150041d480d40d80a101003074000c0c03039580140c0761235400504414407107005500442e04144050f0031908400380884107100400c20389105800845000d031403e40e0550404642e940d040c2d01c280c0d4102010080085900c1c83c0c59035052107012030403c020a03007540600c0740102c0000501400c44c09403000b2a40143c000600608980181005558000d1003201020051454070106c10b544210101c00c0307200c04080440d02840400094104030f00949a0090349003000740020700369040246044070005404154031941d403a010700303481d00300e08120b40083d111150000401e6074100c080d440740d0f61560900e5400014080c0114159042d544c041d8140e5910418038030100e403e134454020001d110080704100c0105100c0f980d540030414006000740402c046055485018a2010030b0b0b50444100200080401503071900303201004103400200ca1844480346 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 336134973 1250 336133723 336133727
    0x60102150c0c060103060b100302181009121a010815070807020102220617010b160303020f0d060806010816050603060604030c3f02010e0a12051516 65
    0x10355410416002542602060030704162500740c489030551407044980c10f603928104440038218a1070028000d2540e91910034034617100e80211100084e54049842c048000c0b80d06012540070a90001c2c01008161328000c100c09082e403102003659030164402074203165881c40d40300442c10040e40101030300d500c400440d500d0b043e0b020000c0c641c0007803142492030080d541e0740e0003640a40b20f002840c03940246421886000103440740362030810b60300155906001c20700441701c05040301ca800c0c0101c824000c414045541807034142c104105184d071003498050304184440600b030a00d83c100100c2c0c044c2d403c1d110301c000d00012004001807401055004024859421b505040d2004101c0902940780101c10010000c0e403d520303140c0c1150700442d484003508542642d602c01801d01c0400183c0c1e4480c90058100c481c200611012402d00382c50100407800b031490380300950054030003005a60b101038100c81b60a1000807421111591582840c0c0503901138150300c19074020400b0100c000600e10015002c0603481c8500e0300e6 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 336136223 1250 336134973 336134983
    0x3060b06030601020c211501080708010905031207030b091302010f080705092808060106020d0e1f0e030d12050c0403120f1101050106050c0d0f141303020307080a0209090105060102 79
    0x2000a40345188a500e06e501028003c00568541c5500c03841008440d44400c1a9024040c3c100d40307440c400c2e41d00c2507841e02d55a5090383c1401001801d16803051003840d240ba040500690b4101a6a0900207661001705012a800c2401102d003080840c03100a1407100f55600007035113000c2c202541c41c00c180a032501d02c0f8003618900a000d80380d8054542d48200000040e82e2034540311070406c2c0000f02c00400f0350340b088090f0380c4039000d0081500601408000080d4240103844112449100811900d00362a034a20103110f40d0304c030641071108020700054290029102403098000074100b50703460002141295103610192803020304001c40300c0c0b03410081003010441e0f08940550103103143c508417028009100048900405000107a800c03540b901d4000141e40d6007000080000400c00c0c0151080182c1002c019140c4808130806040802c400d5040c00000c11404001003203142a4601d5450b522516500446d10b00b2440d80c11400955019140140035864801600d5601265a400030f0005240030070000752a6 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 336137473 1250 336136223 336136243
    0x10e072102301909060e01060f060e01140c0a1208010f27090201050c03030106080114100801090c091d07140a020a0f030c0204090f031d2b0b0103030903060b0603060102 74
    0x400c401d01d2850300b43e81d01a0410101a50813500601c440404980164024192440baa0207052000c800c0001c00c14000c001140f4000e0050315101d0450082c03c5480074554010082c10003503000e1281d00d900054246070600b18000415500c5607404d41c10300f0091101c44269070459281c080c82500c00e1201d03442c035050311101c040c1030a82d0100e00c01c03400d440141c40900604070400d8503070202000200d071242c3d0061103a4100d44040346441e11103581ca80038000c5181741d2101d02c0000400140050000181e2904008506201c07890003180096aa00c01c806000040342c1d080c240503007550061221030307139006c450103107084540a081c40c40d220000c01d010755141d41000740145280300c110216414140a0340c0d060100d140c01400521940500389401ca60b01345a040085006c2008a451010700d01299841014480000b0f0044c0c081280c1080c208011780c1c092645845003140a40e071548000f581c92110540214072a444a0940c14118503010b015a0800007509000c1d610071700400ca9243e90019024a013 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 336138723 1250 336137473 336137491
    0x30b01211202190b060f06180d030e040f020315041806090201120c0e10080907140301021306110f1c0518100e0117010e010e07210230 59
    0x1c003600c424416070034122525a00a6003525a140050a0104001a071807080390111040c00d403021003072040240728000c090044c4841300d2a500103200030f061007100c6212310b90080c1011b10a000c00040060181d07910317aa80d41c418640c021003031000303150324091003032010f0748100c1d01846130711000c0da64015002021240600401d40702c440c0c010644e4040c1500d030100a040c84010f00c82003e4045014001c92104070940d8011951041c01c5174042d8881c000260044e545400504005850102c01900760740081400c1c0d5815542002483c0822048551280042c4040d4032140301d42e07010703050881c3c00d02c1c2003032441003c190001c100200c03001c4605450440d01240a080454036407501c00a003840503501620500d411400d0685901d02d001e803c44140940000b003680c410010101140f89052001000c1c8580c4120984980041c0180f10341c0c88200d5920000c2803401003040c80550f20780303951081c840c3c92581c00d451350024010060034404818140400720001c00e40040744100c40aa007044e28000780a034071 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 336139973 1250 336138723 336138743
    0x30303040f0b071806080105100e031e120705150108070308030a24091a0301110702060c0a0b0106090f06050a020607121806060521030a0804020d050a0c030b0121 71
    0xd126001d19114010200c02c00404d426507502d40c1d80183c120035081c0181d920070000d00e403030071640c207104011b844803040e40030b03000c0e008811403052181042c1e0102010304c8000e00940e1b150131203e6800300d000d0080140904010008169001c5590340c0c0c504040e040034145401090050010507449000c50750000a1881c000420381400751080c124041c04030401d94500b024924000f40003d125002000140511400c59428440e2801014202c2d810341c1080401c130380d02484140d0140c6042c4000e4004e2000c610b080d115840c5141d540e440c1c00c2e120980002001c40e1a042c414008019032032000320182455051035440e041c0e070307080082e40d2807600800306c0080040f01d460081c401e54094200754609051351010f460b2030302a905e03150015000b41e01410703001d485518040b41203c0b1215450000244003480030710b00c0c05048007000c892000000340309036041404c0c1041d000001c1c02c204200b4010600134034103041d070f5504628180030100010380c0101e05600207040310b101c0344014292010741950b44034031505 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 336141223 1250 336139973 336139981
    0x6070804061103133003080f06061204081608040308030a0b010f2007090f02041401181e1206050a060e010602030409050907091e1401060c02060703020c040c020c0a05030303040f0b 79
    0xc0c60817180d19504c1c1d101492410300b8404050304154180d002c0d005200384c020070740c3d44610500c1494081c010310348070401401008540496600130061401c40076848184603c10110b880e0004140e1281d44100e40d01c5a000040100c030000314451050011000d10f052804c04100c1c0307138010208801ca4000e080010810308180a15103010080400102140d220a000301030b61040110020b400c548548101003c825459402544c81103501020000d48818044070b03482c1031146402151010703001c40340300c0c26894000031866400c45003140d100a44180c501091515202c0390000a8030000e5100c01e509820010060003581e0b0040103450581c0c90b6400002420f40e06c04084602e001c1e220303401161442d15051000c02411040a140c15480100900500c8036013061100c1d008004000d1003150001104840032000618204c0e0040200d80c0c000e20480e1807040342040000c040f50709070b044203000350307100c144844118200050104010b11003180914214589600c8030030300c0020083d0000c040074500d00c002 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 336142473 1250 336141223 336141269
    0x4020a110f010b1807020303071b0c090b120a050c0105090d060606050c12030702070512010b030615100504050d02040207030c0b01080303041703070e100c020607080406110313 77
    0x34003002800808681d001070240034954001c000b0450601d001e000940f81404803541440c1c1007500032002daa0003103155580700c07035048a1503070350004000c00c0d803c100300d00000402d55103d06c2c0c2e00586000311000900c006c211080000f55034003d0035a03219508545d4690300880c1010440b560f05160a08040e07070368a60500010781141e20f81031005149600d44440407807440d80c444050580c402510048440c03040c0c04000008082c002103d01000580c0304407070600180c1131070750158000d1400440042032035481500000d0400c00210fa21801250205d002c100072803030054244030f5500f01038101246020f0a180c08520080c1014101038055900001e002c81018400c40e070034260070703400150307020982d61958125600c3c0c0e0705c02d4400fa601141103407015030b0214040811240a120580c80c0c11411907815403d00508080e0400b000c0306004140c030003140036803510030061140c188112600b03980c0b6400e240c0060141c1001d01c00d0000c0f168014058041c10741560002c0100b5181c5050070074060410401003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 336143723 1250 336142473 336142487
    0x20607081305190227060f121f0b0a03080405061b070b0c0c0f06030402240f1b010c090909051e061806091f0908190206130209040204020a 61
    0x30002e02c2541c101e0003220003010240180756108407262481700403504080c0408400c181c172142d0f811244a804a00e09180200c0d40d180242809800080308200191038141058070148121421140301c89015003c0c10140c45109242001190500c21481c19038445c2041070142d800341f103000f028006171035405002d480400081c44849403084170015520355270036601eaa00b05280310006449044148801b500c1e0080f4042c41c6d112001d01928119034690302045800e14041c4014114100a15011115000d920000b403004110300c03a445e503a0741a2305105035619505070100c0003243d0b458181c5814081d13522488c40d0080b10044400890140d0107802d015080007503915800750a00e11078403545115042c0450036a1142c0d04000e8521201032500360344d40e442c0c0804a41001c6503401500f12560120320910030001140300508000800070219601e102c000e40c0168031344003d90916030351080d4481c0e410454036034088211920002888200c1d0f0101d851542c01520080c03055401054074000c1600c6507403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 336144973 1250 336143723 336143761
    0xe010e10020f090d21020a03120501060519121518060602070303050c03040b07060f18030f0302301906050d120314100513020c190c08030301141309020102060708 71
    0x22401175810210f44042c0d520342e0030040803404034451043c0d040c0a8002e81c41070704e0403148107441c0c4500d03000149440c0e19a82943d00c00300818088031031141400f000640c4204e028880e036003407001d0030380c5007401204000b840c1c1c1820000c0c2c100d410311106200300c0d540410304a00706e03541810906d449280341d800807800c5000310b4104040c000400314500d014000c1c035400c81400800b4810301003081b288143d40e400c8051503041c9024005c14500003081200341e12940c028080d40e00305000240501c03101c281c11070b03080c00c8030000e00c409010780701d014001c018450b0400c1050300c0090301c00400c01c849c07500c0045114852080c001130100c007c5501400021400b90b00000c039288800c00c204145444d210314010a10f070790f903000701030044005038142e076a01000383c42251041c0b0090001024559403440e95000c4505500008580b074454042001403102000c00143d0702038450301180c1b01914098800703000a610304000000e070441d0410030081c0c0589d801255180d004010352030319180d55900d4a80c24210b00d52986 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 336146223 1250 336144973 336145013
    0x50d1b06021204030905031515030a0c080a21020703080a030b0d030c060b0103020f09060a05040810020301091a01210b030d090504140105030d0c0609060e010e10020f090d 75
    0x642c5400001d240b02ca5070f100701d10039201c0c11a01e5840d402415520301881c268803011040040200301520161005030104a100130125810b0410941c0d50359480f40c440d82c4003400f2940302141c401c04014541c40181c1d83c00b800954401180000c3c031800079030740c01d078030f1101500c0e008000030301448030380c4a50083c8002500142180c2001c0b503280c90009c14603a2224402c0e0352080c07405480300e035198424001c41d62040c00941100d414414188108a031540c0318951a00901a0402c800140d10805014801040e1244040103031650314040c001c0c1c00380c460010414001c21400f03001c180081c0e1308035214410550150711000c40c6003008410310310041200c00c8074564144640c110700e12072554091a06000e4880c140d03014868420400c403081d403201028040ca641c5904092a04505544280b080640d2180a1800811608440d8950300704071052500714000caa5124040940100020402084a80d001010861a00020b507007541c4041c001c950042c5d200e040c60600c25030034010080c8844030302410fa0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 336147473 1250 336146223 336146227
    0x30b01050909071106090c0f01110a06060b1b03031e0a090506011203030608031306081504150509060907050a031d0304290711060a1211030108010b0a03050d1b0602 72
    0x1e0300b0301520729088131a2220301445502c001507007400340810312010240c0c01030031248290f00420300541710b419400d140700c4454401c580304a0007041c0301b405000c00503c680d500c0c6030b075611548034600880720385000c44100254420000d0160b280c4454182d030000b80488040c42c0103903141c0b050580050194800054018407403000007103803003102e00d20440021071094070200b003059603555581d6241d002e40e05012072481c0c440d501c1005003d0040340000d6000c0c040708510400c10f07c600300041c0c126800449910541c99a00e001480507051a403d01070300458202c62414003450b04140c003d00e00c4c800c45685008150b150407400d90940040d800c100214684d14080d0b0340c5941d19560014460748882403514502c410300404c00c0d0907043e400d0b084be0312280d00b00350f40c12040840d040c1480100c2d80003564100410066660130550292076210b501e102680c07400b64507580354980080c01d420740355400159071103541180ea04100180c0000361000c0e000c400b50905003100d9481e451240f2612001500140a580c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 336148723 1250 336147473 336147481
    0x1206022109010f091203240303170a090b011a0c0f03090315040b0106051e07050a11061303020f0103020c0a0c0e0f01031104090c0b040803030103020901091506030b01050909 76
    0x10400c0c41901c909500e1008002c002d8400c00110260b03500c1c0200540b00082c0258104266071103500b2034000380031949650075021032450461005100305910a0300081d80d503007070f085404040c40c102540c01c803100300001d2000b91625142c0718244001846141c0b1072454901191402500400644105051100a840c10308004010080e00caa1080107103912901612070141c2604940101ca1400b03190070000d1101160300b0040e0a651960021100c51210403c54102a6800420b003000b01926407149003d0710401d910f42c03901c500031101039011184035040c03d1084480072200f00000001302c4c3d0f0102c2c0ea8900404680006178024420040100c081d405030343c40000c1401112500042281c401d1144d040ca15a50a0b03401880e40d903082c0402099242074100b28207140c5003d0b040a94841c1c0950345003c50640d4509a5105942c0654854803da0700003000400951034070040c1c590050020301424000c103c4484001902e40120340220024541d50307130400c000c180d100304162040f00d8005031804000e820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 336149973 1250 336148723 336148777
    0x2a120c03050a05060109060f0305060409120c030305150310090f0209010308071119030b0411030303010f060207050f0303040506032203030501090f06050102071401020102120705040510090609120602 87
    0x202d82c414240703400c120218420f03510604070b520484051350b96540c000e00e424142140642401360442c0c0d800b540703d450960210707070558003003202e2401c00c1d1152420091685405000d4400092032600b81c1001810752084640303000c0749001002c65141800500d0170f001d80340001e16582240d20281d00011041c001108201c1c0d5040105a241c3c09121000000728010082200c1140505801e000c2c0340342003c01000020b5003040203541051041e0701c40e01d41140c225000c04d1840e0400d0f4420b0114145c2c40e401000805d4050003040d01400302a600c3d51841005000440c2d60703807180d841080c0c00348100000040a00d207081f5100f5a818482c041e0000810029040080281c002802122117003490441c9000d03010003035105002c1252010f80107001d0803450011a62006400d8016203815035400700200e490349103104600714801c1c1040d842d02c4d40c0341c605140602590741c2700041c0880a1004000e0280540c5403c400c8003805c403a041075104106c180c0f1441d005001e40a95203042c80340361407804043c80540 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 336151079 1106 336149973 336149981
    0xa0909020a0905061c03091a0c28050d050a0806040207111509090a09050c09100e0714160b090c1503040c170d030507032a120c03 57
    0x160049128041205c1c0030b4044000411440c0140f0200702d0020700441c08490f6107440c20304103c98001480c0d682c048605103580c0388501221401410b01c41101083d141583c0502510210000d642c40078085070450b080c1600031070b00400009610707044c944255006182c021203141180c0076030400f489051015800003082c840c0c01082070b6886615440c020f40c1c0100c1c0c0c140000a1a5085410803a007444541c4c25031601c103520b11400d00014540c0402180c6c1a1285450200040c0e10b841030183c801c0036900044060845001c1551411111045281e4543d14081c2d407120400d0381d0703065081516401c20002c803a81c0322082440424183e0810302c05143d00501c90382c503036000503447e1030144d20503130740094180744142d02202001c12180da25025042c1c104400341424050398100c101040c1c0d1682e41c41c00740b05821151489814a11441040c0150b48800050002c1001c150060002000380c = true := by decide +kernel

theorem cover : BRFrame.Cov 335971223 336151079 := by
  have h0 := BRFrame.cov_init 335971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 335971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 335971223 ≤ n) (h2 : n < 336151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
