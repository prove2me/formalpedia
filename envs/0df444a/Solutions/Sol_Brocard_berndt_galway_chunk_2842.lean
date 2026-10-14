-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2842
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:53.641993+00:00
-- url     : https://prove2.me/submissions/004e185a-b7d7-4f86-b78b-fe2fd905a4a9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 510971223 ≤ n < 511151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 510972473 1250 510971223 510971231
    0xf13080a031d071a0703050f0415020105072102070524040302061303021b01030f06060207081e1b0d08070303201e03070c15090b06060f07020103050613 67
    0x3220050080c5851190316200ca01850950000388001207122030031294402140100440c01d422200e82030707403002c0021018000304120542d00c1d00041e602070001050b00d101c00c1900044003140290954800400c0e05082191560994801604403000155250286c4000585510081c5807451510030584135115960001c1810181c00b000000440d40c4030b240300c3d0b4251a8a61208400c120f182c20218400801581010181001c1007460141404210360145000701d03007015001c613420103c0b041c5402610058004070800c0c4400d0740700300407054280c1b4525144044085904007265180c048242c1c010060714a821800041c0f5641c44041000300d5822103c2c8698811003450060018001a06000000b4001440c2c5103e089400700503140b0418070b44002c0040d000e4190044039681c1d00041506007448115400c000102d00c220726561280c42240b00c000498284904161004041c002c02851058101f00308954440403004103607182190b0a090200741c070745410000420812407840c3c00b41400b807078 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 510973723 1250 510972473 510972487
    0x20628060b040e04122d0c08030a090309290705032110051c0204200409020318070f09111b010c030f0e0a0b040609080f0703110606090f1308 62
    0x118103c424000c0703120351062110389000241c140d41841890030012403081041840031440182d204a8810380100d80c40e0502c8000b0342603503001c1d0250420f0302e038030403299920703601c0c2d000701600032042401070444010080c0706040241101341c00350f01e03680c109513000b44020424404115041044e20f00c22060f5076840c4035029105044070080d21000c507100181d0306542c82c030000320750903d1804e0440d02c3c64282c00903140e1468640a100140c0f00120701440c0e032501c81480125086e0400b00900040c10300c0c8140940e4a0405400c2034510299a8901c2d42940d0801c503001c101010318000c034801140e0b84180c020400311600c14805845009a0100018240c004210200c400c1340661144802881035107042004114960400c41107651148261043d0b51008a803040410480c445c510703030007440707041c0214260990350313030b02417441d001408400d241d100301041c08010507400940032084403400340c0c000c0c20903107003400c00580b0403c0050607100041500102054400c080c00c03001d07141503508110010760303c2107 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 510974973 1250 510973723 510973739
    0x90409140a0f1208010e0103060903020f1c080f090a150204050a090f0507030e10020912011d070806040c2d03080d0605040207120525120f020628060b04 67
    0x1454002c200c40d00d201810007070310502d026038681416101a1701038000a603085960741c6000b040640c20036001c0d0302c1012030824081d9003c000740070240c0c0b010310030190591921b00c03000d004e2180107000c90300c1c0602c80d83c04000c00e00c0c2000615030f400c0c0c1d4001c18568a0402e60f100c034240203210b00e412032074204200100201d003080c6150003003107030008441d200b04100d03550020124101c40d240300700c103001900464004020147c8a0f0045d150309440180010b1410240560701c4c1d08407859030000050900b03d250030480c000350140807074002844c0d0300c0050200391801e943d80c404129403e010781c1c4c0d03c100c0c242034401c004c14030b803415645c0101a45010f02110b1900e909110350f103500146110b0050b5410041c0129007400c0034020703036003516400300b140150f12074032007410b039804d4000f01e04907040e22113150616006040303041403001205000c0c1209802c175400901c0c0060000346005000805c2d94031581c14004076102c072b00fa072542102c5494000541c0102c1d00e84050001d07240ba41d000c0e0031103420205021846035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 510976223 1250 510974973 510974993
    0x60901060617061323131103120a080c07020603071106010501020115051c0c060c05010b040c0c020f1306080105160905030a06020f0d0905010c02010e0105010b090409140a 75
    0x2950366140c001142c0d00d00c14a0500c4144202e030281d4200c040b00082001584258002400018071205030714484240c0030100b812059088030507980500c401d44800e411b04c00752295102c00c104040e805005980d0b50307403241003624481c00c000041004140c074000754400740c0b00419070f200c0a5009000d0780da83d0404240040a25145040100300c43c002c0800000340c0c1d40c014400c0b8250110607540c20304031140b40c68204007141d81c50083e01d5280c0342210007103500294000c211800a04843d4030f81200345019800c0c15821039202175034040c002e81c0303080828145030390000f4a400070f490303044660b06255900320002c5080d421360803d80548040c14050040303445241900150700c680c40c014070619804031100401c4a08010707a00c41c3e80c0d003541042e146180031480303540091591950340c400b801e14101001d101c0d00d044800070b04c01910581d544881845442da4280501490074455200a00882d414a07205140d14410460001c0c4115a05c002c00381c100460341e03c02c04500403002003603815110650034007007149 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 510977473 1250 510976223 510976229
    0xa120903030c0b1506030f1f060f05090a0306110a0206010501030b0f0d02010e03030a0903020f06030c040e04050a0c18051003081c0b040e160b0c0a080f070210030e07090b030a030c1406090106 84
    0x620623076030300c40340031500300c2c49480126600c503943e410200030780440c1955503611100040f50000120704001c008a95140a05a4281d1440da41c255849400c104001c0c28841c0c1030304418105800c1100a410903a00c0c03502802c1004412100309419610b588016545142c070f10209641500006c1205d0445a41109882044038025204e02c908080d120007006103174071080304d07800103000b800d10041c0030320020200da0b1917100340716000725881d006841e116042000200c0d0b04c00710340050048a14024101e46001e0740c0d803c5624200035058031800c40d504c91045000f20092441c8030500384000345515005600030200b1f40402600c03c10000e00b501780419110310b6140a50740f00d01001d602c1c0042d020302c10000729212078a890000d059010300569039990142c0c0b0124041c0b2480a00380440030240c3d03204691f11185150395100092000c2d108041282400121784c01400c4088c5451403039040c580340420a04007456061420900c1126586031200100024a145058512508082142d45c030f0b070550000040d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 510978723 1250 510977473 510977491
    0x603031215010e09040c030b04020a0902180f010f0e01080c0904052e06020d140d1509150b0f0904060b0703050703020705120a0b04060612050a120903030c0b1506030f 73
    0x1003d20031014003100075001c1d01d000385810081c54003080411310108055800c50301c010240b0081595400e11709090340c02c08540c00903010074a03400d240a0b0b140803d0f50502a00003801c08807000300100c1d402802000c07008a09906000d0280001030f83e28102d6021103040c1030340144104020f041c400102c075001c42c251406247c038400302c4012090840301d01c6080b60112690ba074001c210304102d0b20030840cbd480009951252144a0501445490f03528900a403010010044e40074440360b490111041c05841054100c4480c514141c1c5090242d401610b044603610300384080160b5544100101280c024007455001f10240b140c04a00381c001c043d4010000c0030258000d9080b113018903104c904011020000c134846d02016400030503420b000039160422140c0c001d0041c640000c2c00350703880301d000100b800205021035085d080008081c04000103001203218038a03591800841950940d82c02601d10309007000068600c4507210001822991205c4100e0700700080581196181c1c140114a080e51400c191002d0032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 510979973 1250 510978723 510978737
    0xb07060b0a080304150201021204061505090c250602040312030509031c0f1413032c120307060204030818040e030904020c0c031207051b0d0605060303121501 69
    0x5500d0034420101c00c0d03500c0500614581407802841c0517202d050309901030250b54090000342031142080c0fa10510443c014030000c40c800c240c40301d42400c1d0210942101d40305079440410301a20340001710a0f04c613261035160742c84165003481444655240d5440382e000313050500005001c42080712240918115081a8a040c0050748804500e55100d009040613810251002054403104402981110070720100750040010f0000400c00144090072048503444443c003c141029000c05600c10000440049094642800904420595001030310b0031315056100d014403080124100000b44101c615055020710110342d143d40e00d00d00b18401d40c0180c50345035230070361204424801e6802d08e40103624040500c40059031900c0ca495007040002d40054a401a2500c00c0b00042d5010b40c030108103040c81940c04607011a11036a2030710741180b0701500c07084142d03841442c11811600607102c1201c001105035100d140411155a0400400d20350301a0341031441903145424244040c150f84965a250481c1081ea43c40c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 510981223 1250 510979973 510979991
    0x11110061403210322201206040519051c020c040b03150109050a02120c09121c140909070c020306010f050906040e2a09100501020d14040506040b0706 66
    0xa141d03001a4000b43c3e07030240400019200c0140c1c03450f481d14003900d444440441031903644401e41201410081e0760b0011545044202591421460800f011800c0d0301c02846607280c00d5960385c3c1c83d06642510780c00440d91400c080d02c204003092081c280c032904003a2404100200d0086c009544080700d80e08107000305d01d00700701d41a01e403c0c081521301240b40c400b000c60f4040e920300340703240380200360040031f02010729800d0091804c0801580d208901400102503c00c0e241c0c00c410080240288060104c41169440070f1444465a11600c1c40c1509481007818480c0450074032401d00c042c517100d5200c1f85507005020740d041284558000d00304000d0705009030101d4a05030b1f25055040c030008202c0c01602e03408540d5600103030a40c5081c0d00034a4442043e034080d54001802540300d94421131200c210024a40d80c00b142c407191a00309544456407001d005040c2401040c41c06001075240c104100b1044100302409414904400030042180c00829018003410380c6c56944009100d074540210804a030400c1c2408128 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 510982473 1250 510981223 510981253
    0x41b081e0702060f04030e19030624030f030210180323092b03080901050606091018030b07030906110406051209071a0306010e120c011110061403 64
    0x4244107450070b4000f88001c0e21652a50202854010300407020880304520756022a180c0c8002c0440780c26020005002da60705500d026402c0c1c030380c50207031038644410780446810201d0760711082108a0703810980c40040185141000ca04020400c0000700c100b80c14040c941e141c00340c1c0740450034a1140296036200c034480c40368150025a041d003110004000c2c1c4240801c60b070518189624900800c03103503140200091440203908a0f5408003002900400c281c4020415002828000c10713502510403100503241030883c900003090144520140001c000500d03944040000e014203248003d0f5401c040c6952051070088402800350502031030845820781450340350344007002a9429102900c0c1c20352201070400000c1014000705d031320020b2203079215102d0580c00140320030303484000740c07403580450030329543c2c9181000026000d0010040c0c441d004a00698202c00360361800320760400b0032802440c041000700c0c91602c0485c500b241c2020303040501c9242120004a80d40b01d40e88103c07031600250250ba03510b071541148 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 510983723 1250 510982473 510982531
    0x301031208070e0f0103060807060206160309080a03180611031509040f03050304081215041a130c021f14070c0b0a020a09090c090603241202041b08 65
    0x24034002c0b442000c80300076286410f4134803444416041c980003070095503c12300c0300d1515960307500c0f42c80560882024001300301c2c181d001c4d0710384002ca107042c144017160495440078058411848010101559010140d4208842c2004030560340e422500c1406486691034050441e5072080e00c01c60315103944085040401d0804504981c80340342c0190400203c0701c101c1e1010b89485e0310043c803c6502503800c0103030f010106180030046004805d04201603401c00f0015081c441100c56007000b6800d90044461001c070759035207094185407410003c200201d00c01c0211074061780f4040869050f035521015010580d61f01450710360000d9071265916040070819107850708140d510104509024045003181c0c0c000400b510b0154000b0314407216203203010522180e642902c00c04407105901c24100080c2c107510200407066050203214040c00e081c16540144030095004e18503411941c0c41151043d00548150704195900d42e40070340b0581045041390f807882e005811009203481d0b03044503000603ca03407543d2008200c00e56040 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 510984973 1250 510983723 510983731
    0x50f1207110d0e06030402120610180227040e010c0302190516032a0b0420030a06050406060b030c030403020f010b01050d090c03021e0307120b06010c170f0301031208 73
    0xb01d03211000c8219091111344d500c01041640c00c1a0004a101a15941045024480c0c0448251102c006080a1810180b00c0c0340c540d4004ea524014000e604ca0303845040d18180c0310083c0420402c407400810300115005e80206103030701c100740d464841d007800f15917016001441000580b070140041001516000d542c58000d00b051420501e07111031040d00024000c0c883c503640c11442c48050b04003c03000d0009182101d50341c074012584055203009100c1080141000314110314520744002d000c10342c0c1600402d0b591640f40d8406030000703407034074046400d1041c50707401a40a05000100c2d45d550385403d02c0e40d10034507403060760124014411604042d80d0818188a205c13500c80050b50707030300e140c41c0003200640040e00407050260388025960384000300590f40c81d40242400080004030a000300342c0702e010541400703d1584820400f580342c41882002a0341c01007510b612a8090a0902229916050a0000902d03a181c4a03448000000701c56108a4851020307604036803180340f400100e50300000044801100682d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 510986223 1250 510984973 510984977
    0x50303100f0b0309030a08100b040303030e0c03070e072633090c090f030a03031b051201210501061202040f02070b010b0d09020406150f0f050301060f050f1207110d 72
    0x2200142c3c01b94030410103681c004a0701c41d221411162182200191036000ba80101e0100707a843c1c01c5508180c806000c64900d050782200500242d6203001068851107400801c2c40c0c0400c8090b6001481d6900405540e04440003034807000e6a50f0706d001070a4011542003000f51041c1508640c80040881c0402c42c00049074801c00780205a8035121700c02c4117501c5412004807141d1000b696002c0c015941c42c01c118030565540170381e5006c00e030103d84e4140c022100305100d01100030400c041190103010f0340c030300e1081c41c11200d502c0101c2c9020084501003900070014288020441e5081007800140070b180100c0159880c0c0c021a401c000d92407505c26180f0032031086080040c40044024010030100001d8400307041c0502c50700701e0100d140701640d4005402c0310602d030400030340040340d00ba40ea0f01e590350110f0300e03103008078090600406561880101a05078041441031a042000490440c00041c1c45141654210300c040324910340c6840c40c14049950407a006c8074848005800d403a0754514041001891038bc0721074160b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 510987473 1250 510986223 510986227
    0x30d14090f07240903020306041a0606070503031f0305030f130b16020427060e0d03020c060103060b010c0609030f020609190f0c0b0a0801150201050411090402030109050303100f0b030903 82
    0x3e00344010315a00c00c811040140b045400c2c0c00005a00e05020451045114110424002e80704040d0300c003c88402600d1240119401d00243c400248004112604a82140411415802005121546c0000c41c0e0001408c0d8000403c0e5203902c02005805809044081d841c2591619201e5500c00c03d5030140011080c1d20700d105d40855400750800b41d000c010150000300303c8844080050341d00700f1290500842c100c505a6413140d115144c50310038003060100380c00510b030551070303e4510069940d40300c0044c04060b005503516004e09001c0d070702403640d0815240d0301c8501840306031a50304020384410004030b032000260150705d00041541d28089000d00960203044400003000d406615805d04180340421704855060003280d011030014000c0014200c0300d0241d544080343c640c180400522208880309100c400e581c1000f0500c000101411548182c40303405031a8400c455486000107400b410483c400035101d0f000000a0204000602c00030b03c0075204908a41c1c600c8981d02d00d807090007480100d81402d42a042 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 510988723 1250 510987473 510987509
    0x21e12011203120c1e0f0905030a02010e06030702031204080414090907090e0f07081c0c0b0c07030e0d0506061008150d080d020c1b03030a120c02030d14090f07 70
    0x116501c40c0c254180d061a005d00d0b42e81c0b490080240070b9498042e4000030400340c81c090610f5980c041e00e43c1c00038013420f4019160a443d5580041d102c1304491035a64400c000120014500c04e1081003501c5401b80d41d6624a200380c180350030058a50b80c004c3c0145201c04030064030100303441c00c042c03548900505052006010701850815100c0041941c441040c0b5640205c1c0a00d480315202000800c010b40810b0700541001c0c0c10098070032503112580c4c01f10900740581c58034444081038480c4021503110b480081810b60301c3c102c920302114a0708a101045600008000140c0140600041c480e0302c2a082584e0a804d40402250705407480442103400030540c5409090500807410240803400d2a0f621a1284904003584031074840140c2c0c12140da015041e070700044c02020101c5803d030041c8800340701500618a00350350100020401c0c00c034444944c1013240c960f0300700401580300f00100e80030100540001c000c510380c0540350004804051351a409244141e00303604056140108424007102d4a41d00c01d40f403c144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 510989973 1250 510988723 510988757
    0x6050906031b040b12073012050304030e18010503010608280201020a020915030709020a0f0804030e0a0902120601050a0c1101180b1b010204050f0112021e12011203 72
    0x10080030b13517411010340650301030441e404025a0001d003841c5c031207600e044007060642d0203c001a5400000d840c4070117070007480c08101080d0100f0b00c5241c15240490340e07599603040503505003080d03010040c3c002c50682c600d03417950b10f8800b40740340c144c83c0101c0023803240c941c0c0c544c81c06030303543c01350f07514074a0002c216040340d9111902c41461742000b40c8107005466210400342c000038010a000c941040030f280390410f00038441d1800b0311000010f44020030b401c40c00c00040110041c01144521802d1091040d03040100307082c54010a0048a6124010301402199444440030b8001e5003180b0541040304621401090f003541c011804d480e118503481d91082e07a940c5003501c40c01c2d030303084080b200a07040c400d80c03482c850702d199800c0b841e13b405031000e10360490345d4080089402c1142c04440400c9005644144010310007982d4060100c0e00305442441d00102865041c5440802071080040540701180042401d00700040110003510000a001c2a052480d0381d0f540340c0c4042d000c0030030400030b000581e06440380803c11 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 510991223 1250 510989973 510989981
    0xc0708060105221808030405160608070e0a031502040f0509010e040f0609060c090303020c030a0819030f0213051207180e0309030d18441006050906031b04 68
    0x3e42885004a049192003040c00d6590b14090000e80e0702d07001c008100018807000300031b0040e00c1c5050f80144000c041c81e201005140c1070024041c8001c02044240601599907451290030180d500000725103080060502b41d00c2c0294410b1091180184800030005020311380707000806e04841090700d1800e0305a40743c0e0340d0004841d014490850f00070781d48800c450045003051040c800300c1c01582d25a42121402c40c00c0282c9403600031000e0030b21a602500400340050309040a0741c0c280440d41124080c45004000142d028082c0c0e0b88007520074a1002c101e11100c2c42204400e08206c40381501e00205030a401d44981b5141c4c41540500341200300e00b00a03035104136001d540b000f0480c0d000d00003501d041c800b80500090130290107a0030400094544284113000400404035000104105500c030310300042900765407041e8020b280c0d0344441c0c0401d1210700a00808902180d440c041285e00183c5459003070440300c01000300101d0103414016026880014650b04002a2800c040702248003240c04d210340401c1004060 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 510992473 1250 510991223 510991279
    0x8040c030b2a0307030b04020c0706080c0f180a0611060705070606030204140402090c130315110a0801150804021e0307050612040b22060c170406020c0708060105 71
    0x90102d8030446500c4504a4146581c000e44040564034208680b0050940304080e2810388942e104000291001c600052080119400360400b810345a846000f940840d019a1003100803483c0001468069600d060110904040302118071081d030f02c1d20ba24088070b04202c24080400300754480804200c0aa001d040035084062003480c02003052034480d40031600380c82907000c00400a1491405000452506030621544600b805960505001c0008528140080a40700c0903180d80740900b8141c000d034032079800241032405424010b40d50b030b00000c200100002000d200700440d10040c00110413105100f0030035280540d400921109404143c0240b0254048442c2d010b030754140304203030300050310352203010280241c03043e1004408101d19007820b207044e4084009001c109884100f075650251510340644940765180c02c41c0f00090881c00c3c4a01c20f45070101311064150014001d8001c010030818181c0003005401000ca0582d610f43da503030b0b070903a650303020280180b581c407250101c505410101c803e240b4130a9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 510993723 1250 510992473 510992491
    0x30f0d050714070602030a0213030605040309091a0607061103040c0305120a12021804050c0904231602190b06010215060603060f04271e150b18190c08040c030b 70
    0xd8030740f409c6482038020b0201c2e882102d0060325802040180f64011440c0f00040214803c14000700010b04850310078180410030851041c400405d88405100b21340d80020001501e0582540e5a03060900707050141054901c42110313140716596400500c11f04400c16960005007585555000d10311121a0300003940010148080100003608016007995071405140c1c09621420b01c1690b41d0700d00001440700795946810814616801c081440200c041e4584031070303610102002000f00580d14102d0201c0c1884091000e440b17413031001700d8659050140c03032000280105003d0302100e05000c0d0444855240003800c031405070740254184005a11424900c0610008c0140180001040200045807268189035883d01d154100211015601008200c40091015500b103810b092030300440380c0c0c0c2d17020720001c0784c0701a0001151241d440c55495195200301e40c01050409a0455041c41c1c0850072804c8805a20380400741c02e81040c044488060003500401d01032a04002c03140c9485080d51242101c08402500d14a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 510994973 1250 510993723 510993727
    0x91518040504210806150403082b020a050901110f0a02090601050403061406151201090902040f1407020106060e0102031b0c1c05010b063108030f0d050714070602030a02 74
    0x511601c0c00c0f151a1060101c6480d6007006080c294240611a8a580b002d0149007a00300401e0000ca0611010f5a429101421050015000c0c0c1d000081c014900c1c240c2e0002c25500101d5140341540d08030010303280880c4203a84400030307240c112103a00c1e178408040300c4281040e08400380c40000f6060408505620a8040c1041454141d4a07580e2004564400b910501500030030014401e440c80c1603d452400000300040460505585032003c40000004bc440e4110069490185c00304540752034020003488510b111080010014100681c02e06480459424006500e040c1c40818858022114580e0440381a401942002110465220351103d918451040781c45818482c00303080d522551980800074802511000c042030030b2402509580c00b908405104000a1100b40c2c1e844150b400444103024008600114044440e009092050b456402050690000040070b0301c905418400030500d07894411801c115030740e5032480885403600c0005e0303144807140c0c0c01c01550001c10340341c0d001b454028451300d20042c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 510996223 1250 510994973 510995003
    0x1030515090c09100801050906010807020d0e0a0b030103030f0908030c030909100312020304080601090515040209191211060301060f120b060310150206060102071701090204060902091518040504 85
    0x1850390250191303001c0001c04800041c002801c041c0811781d0403010078280b220460500082c00781d280d0300038050303100400500003030b0008541c1d1349824a00003000940306050752945c5a06008001d02d400c0d022810200f8103112000501200c0002140c1c900105180075500b000d55200803c003c6800140c12907004a42000010011a01c582c1e070345c189100c0d81d5001550340c0c2c0c0c80c1100c02030130034005900002405140c4001c1000b0044a00848407070400c08070ba0040c2e072400782a0000303508c0007105840c800c9a8a4203c00410101c0d420126804014011448804018100010450320784002d001e1400028100032a101c4101e0080d80246e0b07a210120b08082038806245021405582003101da9059010040c2c00401c400400c9580c00f505d00f0707910348081c104616000002030350358001072043c01c82c000c0d4170071200182140300b0360051481a500400a0011b0f6503a0303251100690408240644502c891300401e0086441c1c8404844058190f9001c11031801c0d020000c0000038000200252140d1055003400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 510997473 1250 510996223 510996229
    0x1052802090d14031209030a09211202060907090209060a050c24240a051509040e1501050303070c03060906020d02030405070611070e0f0c0408030d09060b01030515090c09 75
    0x782c0d0020104001c40d11a012000f9100443c0009070034944030790020096010f6440c4d11110709c0d0700755264510107102404900400c05c1450b03175846000b800411900111320ba1071540842e545008403240c2040764089503c3d24403100c224440c540010b90701c9181080446251409080601400e400803026680c9013484884000368008005048104401d0308604105c1102e00182c800b03042c50001e0310800400f05a140080f41440b1014021103106042c41d014020100c2c2d060003c940c0741140c040e00901120001840c03030769860080804201030340c010324002142c91708002083d100c1c11a0400743e00c04019107161607640041c40b0700c240603500903408101e48002414140001c42c0101d1280000b01001c1d8540f600042c10036414403120a8290007055040040c1082440c06541002c1ea420b8445126252503110070b8192082c0d40c41148980008240c241c1388070101d603c15030728180107103020b01042c0c5c245801101111030884122100071040410342805051508031207a00c548a04440c0707140510f50400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 510998723 1250 510997473 510997493
    0x7051c0b010b0a080a05040f15020c0706021608010c08010b13050a030f0501050601081605032208070303050a0b0a0306092316170d1b080a080901052802090d 69
    0x441c0d8200b0010b042400f0079031144aa9600040e12402080170381080e50700c18050440d003400240c05d01da004003022442c0300da01c3e030480f59004609800c41f419186c1d10b4002a4840ba829651110742c11441138000540740418051400d0741c0303686075201004c503828107200001b0b030341140d484132100b0a140071000c01c0301d886400410028500a248030310328036525150090035200020a128100719040c010f000d0300d28805605c04030716018a041c100d031281d0780c0b410040c0b26407103000405000e82e49505442c50a00c0b2401f07000742191070083c1d40a000740c0d6541c00160040d108800103035508075030303108800c2022580d05d42c04504030500c1800d40c0110005a100790450702c281000344001c0c02c0d000482e00b01482040544032000800320080d071012a1000c0d48449a00e900c0300c4101d003414402a002111b070785880e41d40241104590040209880304014100202941f804894004281d807a010224030b400b0200d888100303103150522109200b950f80b411594001e0340150207804d400020001c540c500142481ca4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 510999973 1250 510998723 510998729
    0x501061806080c030a0c0621060306020309060a060303050703140d15140301110405090603030c1501150c0209010b09120709020306150309030414011101230a0e07051c0b01 75
    0x8004100d41d03051111450400303102c11851403003980f00601c01c0000408210301041181d041e030510700b44001010700c90318034044101d0000c0310510b2410102004002159025501414020003116441e0740c0f0001903038201c030803501026000c2a42801041d0000e07109941d8800703402c0810b1501c03070a0601c03460114050fa201040c80b2120403640400074032082c41144214400160120024400a02409140720180c8110301039640642510000244681c804204070b07050603c056007214180c54800a02e10400c501c02c0c05540ca2134400c4219046174144180b4550944a40080c607004e0264038000995401760311078241a500007400001011780e9060901c00e050082600b088007682d40d10306041001095041101802c1e601d000c00e200784184a0800015941503070f0300b0200c0c1d0440c658400005843c050b14450680c00d056003042d46004103100310508060451032a03a202c885282c43e0f024a0364280c404460185c4c001e9408005e040041d860880c411410341c41c0c0a102c441c608042d252152605200260 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 511001223 1250 510999973 511000019
    0xb01090312021c02031213020a050a120c09020901020d0315051002100615200109060f0207060b0303211f0f06020d02071212120608071e1d04050106 65
    0x40c580b0000000311043d207603030080d040c1c80030f5071404944000c08107401901a2100d1060a482042c950441d200c510152000c2c0800a00c1d03030810781d503148a00070703100d84102422252141e41d0760000070219034a0080d5111081c05030050401104100801c400074124414046100040d1140002d40c03038484010f40d400003826a070182010050022441c402c0e02d4039035120704422054440c00002c05503003c40d1644d822024814150600303249004403501400004901810b041e1506c404240c800c0302d694010034509202d84030901080c03521004241e104d0103203140ac1c2c004442c480748400c0c808003110040343c0e400540c111310300500c002c81407110050105150000c283c0e01641d04001e00c030190301081a10180c442c580b004161450400c1201200300303000f0080146421800002131801a004850455905050071801c104030743da101001790341c2c1e100c2407042c28041c01040e451040329002c2d0f04640c0c0180d61200c0a042d00300c11907030640034048440100242c400307540e12140810340001500100094105503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 511002473 1250 511001223 511001233
    0x40b0f0a0927050601052806030f0510180207020a030f05061803040302060a200f24130210110f0703020907021605060a030b0429060a050d0b0109031202 67
    0xb220740150341181e00d0785030030307020950040c11001031000200316040d510142c4035024805824100e90302d01d0a21000000c0708100380c840046101ca905034040c4144003c500024001501c500801c2103000150b40580b0980c00140360440f44226450340081c02a030f0310203040700e0380c080c0d40c980304e0320f86d1074002c031108540d42d03000801030007003e503807500718110ba0210340f0019614041c503503170001c2d06610880d03400c03805020045d003603847d031090399011151030006c4250607900b40030354141009840700000e1803280d050066076a491300b844800c9842075440795811802c8c21001e2040e607001c00c088068112155400c1020142c10010189010f01446031304c81560001003101300d0a610400c40b8041c8001d00f10340c11907010b81221a001d98000000108480080c0d40c902e948001c4080b046020f0043c4c0080182c0160031324202d029034202d50000220740402c00e03c049180c0c080298104071440c0304055140c40020402c3c0030401201d580c55202c14040481410b0040d8182e40d242e13240d03da95110764042102507000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 511003723 1250 511002473 511002491
    0x4030804050f15180109030807151b020a11031905010204030501110901020606120c1008011401050c06010e0a060e0a020316030b010f050706091b031502030c030402040b0f0a09 77
    0x801c80255100b0102110010943c40d9800b00c0d00059001c0c4a4039640280710702c9122000c185d000e1206540510b4200d40e09594440c0c03642041d045880c2d03440c1607240780c14a09400300600c14000e4104000c218170b5903014014558403074540a44009541d01032503494004d8a4a00c40c010310038800d0220304c1d600c50400581c40303500e1070802d1401c4512003c40c102c40900c1c204203040944ea400f2a9183d8442c01c1164018005207001c1c03400e500d010704042c8613940004040480d400c949030803242c203c0c102c54440f1410709040742c2660046889014802007200140d2010b801808181c2d0714540d02d40c2d1011034203c000846c3ca50700c1c0d0201c42940001e64041020035400414002169072650500443d13020030304040c400440408002481d48042d031aa1008000b800703e080010007071a074000c0c80c40c00c0c6d0810706200300b502d481d2840d800e10300c00c6d41c44100d4402c000c20011169a1aa034002daa01c5403401e200300c0303030441e640c039020701010b0710150302c1d055030110130070011500b0740e521f81e1065000707070909034070003e40025 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 511004973 1250 511003723 511003729
    0xb22060905160f0810030b04050106030203010c0c052424060f04031b050901061b0c0608062e030e0a05010c090906210206090112050103050a02180f060f0102120403080405 75
    0x600f0700360500c00c10180008100c0b8000c00c080c804421a9800551001c6540d1030b820f040e801000a504001c0d415420542c00c100d641d40d10a4100b000c9a00070006d546a940069420208199000041c028003107513100000b01c1e5081074214207040e0003680888152620303e1940002c002d6842141805a00c0341d0109040c424001e02218080307030441ca84034080c803058100000265058014400e42c01001401c94500520003045001040d80344d82c4540c03030307a101603240d000280c0384120454001c0d0058900c000d806401c03000700c4480e02000075030804040d00441315500214050440d041400032544200125580000c0c0e00b48079810742041c1560703503d15240e082128207070a40d09203602141058010410440e02001c009480c003046590468140e07640d8038110300140c40c000d09107403001000614081c000000d20001003011401c0703a05c00c03102c10041400d5841d814100040030703200424410319550005101e030030098842c1d205a07405004413501024080a0100213a00641046451050100342000603007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 511006223 1250 511004973 511004987
    0xd0f1a01090510120f06020c0a06050f0603010e16120309050d1401060b070206030112030c0f030c050111070b06090405030c011e110913050a14010801020306130b2206090516 76
    0x3805000c50002d1145d103514420300e00581e40986580d900180f542941c402c00c1115000031644888107110501d800c0240c040c54032011689203019500385041c40c05d1000000c40e4042d42c09039042c001d4100da5040c82d0708010003a030302c1c5008034107203c00c0503000f00c4c80d40c0d51b0350b007541c40882c400c0a00c00758455030001c455081d81e4050307000300c64160050142d02e005a4841d02038070706540c054052480c2505550504442e010b0548a000d4903814040304c2d401c05041c3e102c50700d4a000c1d800b80000b48042c04400d101c0300118820080d02510b41808800071441500d410300c2015003080c015400c0340e003001843c0e1403603821100002c00c40d000074071120020341c0c00b1003d1130040c04a0320140e4950b541c1009020300200f5540c00340e90744000030f07059480340018841819507020f5088102140c1860180790303100e100c81e80c000d600a0b03030b5142c8a500c01b802d101034005814010421141c1d0098043c030100d003441160a0b20b40d0150445441d0542c0d165107001c540c8924a10410b40b007004411355182000804081c003500346 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 511007473 1250 511006223 511006229
    0xb064209010903030809010f06080a0b0f16271413060b190909050403030b01170702070918140322050f15190306050f0406050d0f1a01090510 62
    0x48024801951640c0e003040d00740741103a4050500507103540d20310b0b80340d07401481003004140f100380c50001d02051100700090811801403058079901e400341c41e10f51102e043c4100c1104c2c2012004098a540207113644241c032445600c01c0700b580c44a00e00001e440304c05804100d56007004d0101c6503007a09250452a040d00008074400580c18100892170401021072420710403d80d00304a600e41000c040e02015100d000c0010082022843c10400ca00301494000c01030080034001c01d00240100c090a101070540c02d144a000e603201c0d8000b032840d945440500c03009001c0d050401407015500c03402102c082840c8400c11800380d00200c002d1a5280001c0c412640840941d440389030141c9000078042c00240c5900140755200038040351041031081251075140c03070303510503500c51350a06515691010121600343e00a03906551080314a1103025074082d003480111802d611403950b1060030500c029021070300e02a01088441e008a00c2601600c12440458955840a03400207010f280e4840400500c00c2822a01d0406 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 511008723 1250 511007473 511007599
    0x21e0f040f2322020303120f010f090c08010510110a05030301050306070203030405070618080115090614060708090409020904110f04050421030605100e0306010614070b06 75
    0xd01d081000f42c0400b005501070859158054080b02c040565a08100340d4101620320400f036030703c0b4904011100b820003020300c1112140341c0c11007004103070008603003d444042d40659441004030381c41c080421000c6001d00b05164144043d0310500004c0d100c044c404c510000d4024002981d0301d500d8141810324001c0001c0031582150010f02c1800002100400c00500b1140d0910300701081451044024042504075842550150301e80710321440101e058131021411180d0444080000c0c0f80e40c3d01c80d500c86417114124065101400700240000242c0d22009401e4210300508001a000510390128448003019901a42c00004841e200b030590300e40712000d807080460a913002d00190800d40d944145c0070301e004820582891034800040c0041e44240c2c8a9801040004c1c244a0a01241c2d00080c09203c100000c0074020f0199500214103a03011708040709082810349112071034a40b80b5200c6079100700000e0806a840070050059110340c49800a90f8074504015203011610728480c1403a45810100d00441119 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 511009973 1250 511008723 511008791
    0x15130e150a0312021507080615030709121401090b010e0a060b070b0a141602100b06030c0a09090f0f0b03010902012a0c080a03140304021e0f040f 64
    0x40c01d44400e180c020440e503004205410854640c00e00341c0c20045c0a07454016155007280c2003000f007591000c101030207a07009680403101c034081c4207510302071480308807104004030301d000104105030403001c1d0070320000d24080c08503100e107528240c800500750742c203080d8260f800307440020050100066081c403440d00881d20460401489140000d46960350182900c01f0740784200038000101d1031003103504164800381405000004519018400140345045004140014480c0e44c0041010040c244034415040782e00038000c506640e5521202e40d001d92100488000308842d020002505051034002c0c080018110f80c00410030350400b80000c0708a810246d00700d0f00c40da041c03411400150360440d01c04070b40e01440c40c0e501043c04598014044401d04100b90003004140c0100c8001400100071419a030707800d10a68070706506026540c50551680800c2c1d90196000c064a060b22040500740300b101c1d000c0d040f02034400e484403009170f03000400300e802c00c281041100351280420841382400001490180458030a01d81c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 511011223 1250 511009973 511010011
    0x1080d051306050f0921010c0e030a0f05151306140708040602130305150a051006140310080a030f020f07230d021003020414060c061515130e 62
    0x6036104595202da00b0a00c2400a481d10301141100c0c03c6680104014000b40c4403442c0d0840070300601c1496040090300e9510f00314a295009105e02021a180a4002e004081d180c3e00c079201c1015000204030b08803118400c49041c40580441d0301d01c0d081c890060f036801049141c0041c00c1817025681114114028400d02c0410041130513000181507801c65080030006881e00300c03214040d04c20080b10b0700007503c2480790344813040d02003500e050000c0c450500108144000c1e110040030083c0d540d417900070000452034003a02215020400005160b2000c56207070841e0b01d441e0b80c0c6111a00b420b0400c0c0c002c2e0300055094900d039140d150100090500007407040300801c0000d01c0c164440d51840100210195149c20340304480180e6600c03200f015140f960024521088020407841c0074009500038485d0000804420000f40001d140c0002a1400001924083c000c269a103a51050001c0e910403030080d40701d441c650316000c0994501c3c014124811182913820103050505840d800c114400030503e04100000c15255 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 511012473 1250 511011223 511011247
    0x12080103080318011d06100b13030609080706060b0d050106080118090501020409050f1807030f121403130b06030c01020a0b07090b270907021c09080a0b01080d05 71
    0x160b91010301c00060030f41e03080641036024050708550080204101a4035207141c800200420392902450304092610040785d5140c0d0011000d020341200c44041c060700c1a0104041a180d0300a40e00187c4100d02061401c4080d80d501c000325096508000050781c008100c1300e0754030005205260141100c0d0801d0121589480c00c4103c050000c0100c1e405100d48400000d01003007000d4054070003401e003000090040f40351600c03001c0b0740744a0440c4c00000043e620000ca440c00240030590300300762504051381501038000c4d912045400e4100320b20f0a4100514810400705001d0004040c40c081c0603000c900c1e0358081e485003030081a004d805010a44682c1240708125a9030b80c000036004d0250f90b00c9032403440951307078050040e038070300c40d030b55110307003410200002c2691606c01c1c05241801003940c29055800102425000c0c080c10620491f04080075030720000582442d10301c0c4018250100245180c00f58070b013911100c2d654200001d140c8215810200c03000180440002031203e0b080065452500c541080901819 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 511013723 1250 511012473 511012477
    0x2105190b06010e0d150207120309020a0504020906070203010e010230070c0804172b090b031302030a050c030d050a1403060a1203090501020705040603020a0e150a03030c1208010308 79
    0x810b418481e11030504081c0740c95640020701416000040450003005140c11500a035000c01011144030409003004503000d4041e01c1a2201c46070003400542c84c803410101804001d40c002c3c401140c0c4141e0500c804c0c0016074090141c005040c1d0303850005030322000703800c080c500052070184d000410a9810700001135072041e80a81c890f40300e406032500203901d1001c0c0c01c2002e140c0c4626002a1f600038458100303c01d126000192600001c240d115000761080407002c038048c0c07403400807010304002806030341c070400c40100c0300c8001d15045140b001e8901030080040d030000380b82c1020074200315802d070000f000c0f42c64149400d101c002412602410000d1915030700b124010462222041c001d1540e010200102d1030640300c0070300c80409892040d0f00c40c5c203c2c10311420068800c0300d8a2107218010301c2900c10109050a0074058442100c0c0d0261070004a00d080090074006034078018a5a8401c5104520311030156803101c40c454002c600a4451a1007401141403102902a01103107807014441c1203001007000541000c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 511014973 1250 511013723 511013731
    0xf01050306190503240f06010203090127030311011b14031f06021501090204050d020103020d24060813030923040f06090b03010905030306192105190b 66
    0x194800c10414078070030300724040c110b03500309540503c40d80e04481554105510521030601c05658504059a1503c00c0d0880ca0070089410b05e0058000380040d0140303500610b100034a003108144104920306030312a0115040203558011b03000294500382c20003058200307100d00f800011103c2d031400c0a000546a0103000c81c80012042500d0b4140000084c0c60348100910340c140d1100114400441141c0e500d100075596850310080304400d40700003000240da60514030882e41101c2010b8100c101d00001d6400540c0250020b03a221200f407611240c1815041d05841c010b1034900012400b0b102c1450305101c001021820020074201301c0c412014001c04c0841c1d04a002c03076048600d000c070a140e0703089411001d602c8041c0d050800366003041c02e04600e6201c03003495070428000d468158504200c2c0030405d504043c00d988a554020740244c004101040060800301d0141890401070000100f1080d42c41402089040b5514003078607843c0020202d540400c242401041401d01490a070100d0590f4075444a4003802c030f01034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 511016223 1250 511014973 511014979
    0xb0a06090e0f0c011206050303120702010e0f2505090c0406090b0f0313020102010207050f010204081228050c100c0f03050405102310030b060105040f090902120f1b0f01050306 77
    0x5c026450034025004400549000340a594607a032032071054141000040d6468005035080119980b040c1500080d400810b030f00c00c1c03004002c0000d503009a013124802c4c0800c0d548500340c940c04081226112820214012481d6040707a0b0b5659140c00e900400c00703a101d410508080c90100100545000d88e801500e80080d07202c0e4002c00b01c04107620043c0d00a2184074401840b50190007240560b030381041d4040c20441c3e090b24152003080e2140e070315071400c51244040c8500380c030680c2100301c06203400d5108200034070700c03650500601c0d011041d45094940007609103001e19880d10380d41000700c0c0c198400c461003020035a80c1000d00550030507a0340d0503101c7c2c0c5944103c0b85815034078110211b2141141000b1401d1203a0b101001c0201c0c10302d05886145e1240c40e000035a52400e028004c039015500c500100c9040f180e5003221162502c8c24121a00084e2264100030381e80042100070400b403500d42803080d51003004070b0380d00608484051400d8031500c0d000000741e203072081c18005401d681c0c59070030004a0750300030811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 511017473 1250 511016223 511016237
    0x307170d050f01150e18072307050d0816081f09021312050607030e07050604090c1d0307050f120f0d031404021c0309030b0a06090e0f0c01 61
    0x49000959901910642640040c1031000303024428002d11486416a194100782d0f00b5220303424401076501c00328007100c2d02d41091040944070100c81142641c2070300900e0350b1034190184c5611112042d281e00301c48081c04442100041c00d28204541000700c180004042e09002e105482c00f01d04503031041805544040c2070208030230006001f800300a400e2036001ca0309141e84218142c540c903216001790481c2303000d01c614082d41040401d50020703118402429682c00700c0108041e55980c41c04030090520290f00400d030307100300680071629540d024090130113404506800600c1c4090070714000c05456201003500094520000c0d445216100440d00b4801e5441c15146001d02c9040031002c47c0c21031142404000b40c80c0607500343c2172020308000c109540c0c1f008003580d00b48090032901041c400307202d0702a01c00a5201c1410107140c4405505411080d00c2c41d8001d042c40139110340e1300c1d103842e9600725084400f0110300c1d60394401806454028890000c0340d0012600504912407440c000d41e9846481d501594140001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 511018723 1250 511017473 511017503
    0x6050a020708070f06080606070c030f0507091407020d0915050c0c03030f0703090e160e030a060c0f260112290a06080d0c0b0c0409150501030510080307 67
    0x30088480180b001d0700482d841e407070303813001600840c2c0c080c3e000f040d0000e42014080351181c0f502200751b0704941e4210000c2c3c04400c0c5076542e0080810019181180c00b802560400900c00c0000d202d40040950114203006040c82c02040084c100340700202c00c00107020940009000003401c0954103000380c036150a10755a034000d4110a545000004100c8030f40c5448005001520f4240c1540171701402403003900e80703602c0c0075100c040b20600283c0440e0300384040c400c00388000034101c0c8242e050020f025005410703603040309102d0f2902000e13515554070b60304c085040f9410203d0083d030b21810070700c1149140d070148000d050310748032448840c81c0107100da94049809420607a0a000d44070020259881d041c20b2001d119991070f0404030813007101202d50401851410000207030a00c004140101c90b400181e1b03521451701c80d40d6440c0070562001422529103904184008900d800140c42a1403036500d00c6d1610084045c544400182a80c00040c150281c407050140c04008000001050700e92455010030640d1060407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 511019973 1250 511018723 511018727
    0x60516080619030804080d02070e1608190221060103020c1507051204050d031a0f2412010911070c150c060507030219080c0a0c02030a0602030c0c010b040b0a06050a 72
    0x8542c0c0026000030704c00100000c100e18009002c40000c440d0b07400703590500d69030b0b21104043c950100d0310803075240e0014204160081c42807400b254401b0f0303040a00c0201d5161948403c080b6044201a00408074a40f010b200c19100703c1040268414402d07c0c0139071410054620007500c5584030103560313080328000004610054012020307100c90300c03203108402401d40b40a06195645048900012001c01e281c810103000014000508a5200802501d403001e180042c00500241c20144285640b035503d40d00d41c4a404100c1c84001402c0d050010be114110950600342c06400300c07580c1045202d10a841000f14000051100f032100c000c9480303412000e10b035040254401c0d24a5410101d0040205103000d00f008911034241d4090b0070008940002e465207890209070956008000340c0b0040b8141c8801d1100246403403044010f240f81c5407015041c1ca0310032600ba500c113400d0340c00540d084d82e0351400106808050f13075824030410241110445051149240b00b030003144c1c19003054000c89041140006018030094 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 511021223 1250 511019973 511020019
    0x180f06040509070c033506041119021e06010303051e07230109050c0d1b120b0a0212160e0a080c1008090c060a09030501060e040605160806 61
    0x8006400c614440c40c0185006111070301c5180101c0c08155411482035500707070044000c0c070341c60392411014020351b20341c41200311708904028070495210340c076176118601c95950103020300a01d988001c41ca40481100070801381c144590700041c10112280300c40c841d45801c0c000901203044941606045641d801050520440074900c9558554000780004403217007009186012080000000c1c14189001c107210011030f800c1e00d6003800080c0c05a0b20a5005c00c4952030721078100030880e8032902941e01c18680b4240d00d10b42182c0550300c44a00750a0705819801404040144d0035403200c4400811440c2540440c0110290000500031429014040407000c441601034880c89510351b000600c5c40e4141d680c1d80006944e10080d0786c1d040c50003654441251240e540c05016214003811740c80c2c010300344500e8004288a0142c210f52004402c0110700b0300c001010800030701c20301001d001e00d40c8503524285040c1c00c040703054a41c00344c42c00420700c500308520f1010581c48401c030368001c0801c89030311000400039200840c0342 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 511022473 1250 511021223 511021229
    0x6041e150603050d0f0e030601140102070e19061203020a060203060d05011a0312091c030519030608070b09030a030e060c070e0901060e0403080705030c0d0914060903180f0604 77
    0x42441c00401200f0302c48002001810552580d94207403000801c0d03901201c202929171032040d096030010300103001080d254403000003061410301c1180c5080d1b80d505c1550301002400d840b8003454500d09410205103108600510340909207000c04042103055a90b00299601c260900240c00c1a501001058069a41c615040710301504000288404034034100d4481c00074464142c118071030301c12603035420742e4441c2c00c406a035070122000b492481d031840c510740c0603a01b07569511401c404102041043c2802c001c0059403102c048440340c1d90001d20282400d8110345005174541003100c0c41c0d4400e101210b01640c00280a513507407036161030700b100f048580b000400c1e224050b1a401031214003405902190780e00350a10311510540050000b44282903a030105122002015640680003075141800035400500400095401403480ba40351480c040c61030131001c0465501c2d000c21500c5145102101c20420310400180742c005101c40c1c0954906000354402404001c0d40c00c02040c0601020028400a595600107640007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 511023723 1250 511022473 511022513
    0x6121205032a1305010e0d020402090411161106030c0a1b0c330f051b06010e010510030501050a140109030206030705130e01081b1c1b0806041e 63
    0x4203460415042c41c25040380d008024810b2641030b001035258032544504503900c0c409055002c03061019001d1102a610064165800603140c81c3c08400807201c0070000d000c00300700f5500c00841c0c20483e10b0701540d48411050b40d27922902c82442407100c051020700c02c88201c010b640c03c1c10707404445084900a04080c0242c4081c08000c103240000580d00e00152074064004032404207000c005090040703440400e01101c0d81c03940011200000741454500400c02003500c800354140c00109610b4022510707240c044d091300308512240251004001c0c90500340728111302c55070582418002c560601000c61507030341045c800d00230f024222000c415501d902860161021350340113000c45599141100001d0101d41c014660352842292040e400244a046040018140d503100c00c0235000000b4000f0000e0822084c104040d80c0c4440301050084040d42e000586170b4160b8424903036400c0d00c6000c0c0c03181c0098480198420110394121908100c0041d00105208070110b003541ca05407003134290380c20904004c0380e500900e480 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 511024973 1250 511023723 511023781
    0x5100c0509120a12050906041211011d010c1e060e01020301171204181407080f010f03020904060e0c0303030c070c12031e1e0905040612120503 63
    0x465031120080000403070070380b05400214048031001d81d683e410814050700f000c0c40200c0001d20f0922800040900540050000741880d80f83c90980c03c48540b4480300310707a138100c4008258a0303541c009000c62011048682c90003962a540c80000e8040e0f100250001c10041800f000350b604802e00c10405410305030071400c00c01104a60600741c5000703500a020b4211004c282240036100307000c00058010010400159040c1082d1401e803403140c810703a0a611140d0384a407142c02c110070554100c2d04a500c90112661040603c1c01d001d0807800c6401c0c81a00310104911008800b4000350703d981c03040c070750080c0d4071440018960451031259414202200781c1240e03d408000144000f503103050703000e810500d000c0c100d02e03043d071551010b2988806004940c000c000c83c0c00722001e50382d00d5820750210b000090250a0003040081c2d040005020510312401440119144220501560619104400c0508070080503540e01c0c00301521360310312410102d0b03a0282003100000c0082c25143e441c220821007610716940c416 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 511026223 1250 511024973 511024991
    0xc01170a0507121d100603150b0303040b030c0a1701050a0308090303090a03140f160b0d06090c0302040801050a020406050f0703030b190e090a0c0b0d02070b0f091c090603090510 78
    0x100015601484c416224466064a0400c0808074840c03e400c40b60301c02480d4190200c2122401c014103203c081465140c00144030010300464030000440c4503020b00a0030315510900108058190740340036807000180010400140b055031a5910500262604076117440d0f140c6900000107850b61203140101d9401c0103411000108204084034203201d6040c07284141c90408200c507100c659203000c00b8107074607814500d84402300b10100090000340210f44070050046810341e195045042960041032220002039030002e020040c2c80b00030322540d900f00024010641c41c0a00c0c10500030a60300850000c00001c4200155070801c05000743d004003c00c410281c5202d40502c00d001c45a0610009031140b0b00c5003110750b1001640d050008190001c00030740c400150031060f41008080f0700e00e900119265401d03250308000b5800814868000b2070312940f61620340450340c1c0342c0010a03e0800c101c8102500c0c00581e080024071081d504144400141c8400d450005450b800da418460300d80351145e0544010300b07103407280503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 511027473 1250 511026223 511026251
    0x30106061e030218121006081c020c060702040b0604030b0c0702040e010b0a061107080a050a0302010b0a03110402091c0b1617010b130302060a02030c0c01170a050712 73
    0xa101d20100011541d81d645807840040d402e92049110000100a040c0a040031034901603c050b81c00f400f100040b12a21240a9861000c030b4a031608245411f074000101c80d500c0c80c40003400b82d0300d5142e140c40501010580c41011541300e000f6264001e00c60344d21845022030700d807135007400c1d00d0040d504402c18a03041c0c20503049411060303101307083c01e034040c030f051910801d80700805018a201c460005020485001c1c40c2aa0454606d03028040350031080c0908040019105d40400410103aa03015401034103c1044515004e0f00b180e8800c0780480c0500e03c01da00c00c001107940c1c40e07602c50030f0840580c0c0c05079841c90311000044081e041220b48100141d012010501400408c0240510440034820003d00c102c100d0002078559080b100103c001c1e003040140184516100e03103016041035a0b21a001c580701c15100d0340014029000901072200513800410301c16030740344041048425801c0c0a0070813404098041e0710f00070000341c000f05070040b01903d81c1c000c500028400d04008402020140d41004070000d81c090b5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 511028723 1250 511027473 511027487
    0x12030408040e0f0c1206041d16150203030a020f04270506030309030a030e0d0c061101050a09020105090103240f06020f010c0905090c04050901030602040e181b0f03010606 75
    0x2000d0101c021140001c0f642000203c41c41d0060004118460500041c031a0000e61401d00404142c5c00c42c0d00c600303001180110341100c402e0300e2051000a00420040c00b02a00060403443c0c0c0080e4222503040c04544965401108494102c1c50680780580c3d20141041c0307207516441260b000f2000e08082c640003040c030580f69492001c5034200c2d403605110948500082550f039014500b07280390305410103100c1c1e400082c000e00c003490000c500508070300324211444d1600300c1c0b8000254422001305041400050400b41e00384107207a4004211401084009000e400080041c040c50b036826050595503c1100707144011160b2804459100c259034407012911455042c514482c107100340d0000d481040c04451202c0301c1805001c880d008650b807520081341c5071004100b05194040c045540c852820000420706440740c0c01c901e406180520700160751585062002081398600400030106d6280c1400304038051000414820650180e10800d04030100410000428101c118082281e03d036107080c100041881d00466 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 511029973 1250 511028723 511028729
    0x1e05070b07051803010911013207030f0206040f0803041509060c021005010506030c07290402120f1f02040503070e0a0506190515090d030c0c0b070c171203040804 71
    0x2143c2c840760b80f4201414240c075906d94009000481c5003203020300300e5124400040c581a01000202d0398040e022881e0096020704003502c030100300c2c1c002030402c00c0c5601f0681103040201c1520041c61507140a80350340398240608a0002d11750540000840c0a0150419600400304103400c400c01000c58980342581c01401081e00007005800341c0f100c041020106403040c94100d410142910b491561000801c40580d80703d00800c44a4018272030400341c0c02c00c9440355810780d035643c05055084505050040280d8003d0800c030201c2c03250b00400900c01c09a03401300b00412120fa1541850003642042001c0c0c4010340240e4201c160140b0500c800002c8400c0724000c1d8074015070710340004006079242c0d1001e10800703c3c001004040d850750000e01c01c00c41402d01607410480141401d01107810040600001560300340c1c0d85a05a0002c0c041d40241011310000d06200c20017030107950b14662030109a0381d905000002c8a200380b00c1000300160000c81282e805003c8000505040c010069581c03415281448158020340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 511031223 1250 511029973 511029997
    0x1501060804060902040507180b09030a12050f0d05010503010f05070507030f211b030501030206040e100902040b0309070806060a09090c0302040c021b0a03020d020409110303041220011e05070b0705 86
    0x408c001445480c40045030711212028001e0300e1066a130307403252441e0303030500351010041150800101c2c0010310a03801070480e85010700008107981d4504420103095440c50407103515140d15190910071003c0d04038040303a00407941070420401010300c000d0151840366007580006009003000c440309004060315030200d4141c518103001003e020000702012000c81c0d6090100a4100b0740422042c8280c000e00343c510390b8400a0364214500e1f82d80c076a5540010390708194004010b800010080c840c448105100c5840a0303e5000000c03c010310340003002500c00d130850b202c0d074180e00d59a00c0030002486491400385000d581c01030802d000c41029058025030781c510090611304c000c1c1d80e0500f298110726100c8070303a102705c0350001c0808000501c1502000024415941c04440b40c802c0880f883c4d690361400e1015100600503521500d60019490400d4040d664081401c040200c0840c00e0245403682c002c1814964030380540030704034903180100d0b030541d01449001c0020f46080b00d9070041064542d4040010030072000c0c0e00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 511032473 1250 511031223 511031267
    0xe0f071404060824090f160302040b04091e08040803120108070e09122812150b040e090a0c0f03140a150c181409091501060804060902040507 62
    0x9540c3c02504c4051407110241d1849010540030b84442400304640d8115404c4800e40c0c1c059080c0458071443e1401c1d4180003540e80703030116000c205500d8107110f8110310601c29a0240850b242558035044452094074400c0d080040d40811002031102a4050310050001c05048a6a41c000d000c55014102824070440e51503108842d00402d0030100d101c1b07002d00800c8884010f0681c0b0546139400402d5070400e0b100107500d00010440340e11003400d8642200050f07101e0b901c032030340d41c1c1c4001b004480c283d03030500c0403400300644c806c203080050120a50440b030072a0065181c81100d1f07141d0150990034078904020203044c10341c103e08046070200642503040100c1b445191900d8890344d42d019003075150000080003030300303405103507400040c81c1d01503400440c00442c0f20300d00b01c4106d480c0781700a0300c9000881e40183e004489882d00c00703617090030f01c10034007a0040d000030000c14050601000401c180d141c14041d084c100b0406030003280030880e15802c5118283d40c010b00c14480c6103043e0030020030907103400c0304002000c0d41c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 511033723 1250 511032473 511032479
    0xa0c120f092f060a030b090a0c0807140d05060f1806010207230108040510090809030d052b060e1608060603070f05030405030d1506030b040606050703030e0f07140406 73
    0x2c10070500c0790b0014040558140c01c89007004100d010b402241007070041c55252032054090340da0342d440030740c800c0030b0001000808501d004030062802c54010407110074000940d800341131501d44030007550341a00e0760340d101264690b903440104103452a40745000360003110241c15140070310f282c102103510815003a03084030b40b2107a9600030310581c0e41c01c0005002038541644440344003035108070302c05a44075000d80101d901010b2101084400c40d84000340507128038401140d1880309107000d00007503144481070b1030194141006400c0211442548440c80d0103002c403c1d451956045900b41c100c900141221030401e030031403078541c40c00c0c001c462740541c0301e10000b0150030010301c4514004094a0064441e541c4009103002c0041041d211030380f01030030985140c8800d00014001c1450383c01040c054a03000d54100b0001450b019000c1d007070b1100d04103401e100d1800e01c042440713100c0e03100c000d50b0589a0140b4021036040000c0c080c0b82e0605c0041010090180140180401c000240310607402e42520151070410419036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 511034973 1250 511033723 511033763
    0xc03110606130209370e04050303011e030611040e2a0711040905150c0c150a020c0604030e130203040203030f07031106070906080108150a0c120f09 65
    0x441241e03002c1d80000201c2800c11001010f90213040d80d00c03005411603903060301c0403159001c11014042d00d900301c0c030518404d207421441da07a0b40c403000902c444140c542c1a0b040035a40c50b500c81c0014000e4a90055840a591030130007401d9a51100458014804211841010300142180c0e4014058078010345041008074400042c5013020300c80707140050b18580041e40e24502c00d419694065041a80c00580303120650707190f41d946109000c82c02e44598005c1100548005680e0040240186842d00c251001c0c450b00d030000c500031a00c500d82100c040071010541d45c130089060020b0103120010415446500100020907030400900c42c4404d0702250159140043c01d2100e00980c0700032100250160001d101561280c80480b016021141c4a41070661103007181103256440c1030360445041c0c4c0003d42c00b60040014542041ea00f5001d018803101600340c02410712403a40d160782010740021110ba60740c07142c50842038861b030825094501c150f20240f249200e04e8003803c0217031440d034000b82c07502c500c0a81181c1e4800 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 511036223 1250 511034973 511034983
    0x1c0309030804060302120612100b01030618020301060801080607021c05070b070e03010b040204060c1b080a030e0907030c021b061b060103050c060a02070303050c070510030c2703060f0e0d0c0311 85
    0x4030340c440c0240b018a102c204452702070400590f0003410700d525020041402c03c3c400e100c2b5075040118400050700d9600d4030000412052042c1e0280015801010502c185140c1c0401c05040451896810110148241c2400c94a5209407240500440840402c3c810f4061344100c01c0c0540d208114000c1c0030541c0c2500c1044120320881c030030700e008994030200d1180020121008980754600e8a1203030f0b20402e9982c0156400c2041cae00078120b000502850010189140505141d40c2101e441c0c81d040018414900010396980301c00d20700c01c041c1c00c1c0500094149a6241012200700d520351403030028424507161040da0340c0e02070a01003143d080c003500d0f0341c90b5581d080a40a07500d5991180d03006000492554805894644c400d000a02407030003a084089031540b20000303106464092541c1c0002c0c010b080e0480103040700880700344401c0d40003c136100c0342c0500000b802e91000f6681c000e100055120380410ba524001c00050b02c40d06c1c894080c402410300c54603040782c081e80a075030194892424007680340803560303155 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 511037473 1250 511036223 511036249
    0x80a020a020a0b0c030a1b020325060c1101031a042415210603061401051215220c08150a02040b04061202090a270207021c03090308040603021206 64
    0xd0b441800706d5243c0c01e05c80c42c6000015a0030b11010030300da95070f0f90042400d200c00515400c03443c05050326983ca002174120b16020040c082483d1a00840c08250b0341d10200f2454000b41c80e04040e00c030088041c000e4100900361640c900001c2080040074101c14500070001d580a451031100c00080320005030021152004d1082c18880795281601ca46892098a48041102c8150340c00960780e08400310024506124008101d0845603101c074880d0700d40000c0100d41105062510000d4000d030a080c0740c211903092485030001e04480c4001a40102208081007800481c04058004000d58400241211012901154a00128508080c142d45e050003c0080c0d104511074030030f82100030841003203210b01c564010200d110020308050314054207a0300003401c2d9042070700007032500445121549034484000142d501a495042d400351306117045500040c00c1c0c08035980b10040c400007184004400c040c40303404840701841c1d00c4560140c032251034100041c02034021110941d04281c000000c90814501102103002c4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 511038723 1250 511037473 511037497
    0x50705030d0c0c0b010b031005010c05070e0c0d020d020d0c090e010302060d0608030a0f0914032805120a02014a01060803180103200f07080a020a020a0b 67
    0x50725524412072070090003908508001c014043c840c16000580b0b03590f000b0300078101c4401c1507481e801d00304592510f40c4003030360100d0b05101c886685c0e00000350380402c84900319a00e410191550341d44802d01c000c030511070160010300c0c0c14030002c1c0c031041c0d44d076159020b8900384002000403c00611620030548141655001d184040354181c40108014540b4a0040c1340303041a0100c08244207a0700d8281624540007110f413030000c58020088030740507507031000c0044000c080d015071141c280d603000f4020035141c108e10580e44030281c000080c40000340740f4500500510f181d00c0b404442407080c80c0d000348826504164005001075081c071090500c51900d1800c4030450400c40380c8241e02c0041c11412055040400d40e00061010588184c00c0c1120b60003031113801d006003080d0b8007075035480031001d404098020000004134141480d20181ca02c0080b0300001e0110540c030380f807d040344d980c0e40b4005407441d54095244014540c00c40003030904400c980c04204800d07500e100340d60012007182c071401500424001c0c0088188 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 511039973 1250 511038723 511038727
    0x40602011a090f16020a0803070c02100915080405010e030a02100b0a0303090e0612010e0705011806050405010c030903060f0e1908030c090f0a0e010611030412060902040f090c1505070503 82
    0xc607495403d07044603404e403080d004841580c021940d8082c050740040780d103e800b0414080e41c2000790f04050b40700d40b0000781c4034608140854140440c0603162450b014190040140b590001402c11200354484190082c101d02120340714501d20000039a1402c01a45031030155007007100e2078681d41856900b6005603607064403441c107450f042010351000840c005084175406262048020200b1400f80b0800a08181e60030280070f19a090900250860140a0803a840c083c0d1103401001925404030607034068540034a0002c41400450a044880d20010b4001510203854100052014021940500740c000040800d0b90f501c000e80300f005001e44188400003900f00c1100300001451a03800b41d00070021918001c0c031500100c84054086182d0140c04d0b081000354420312401401580e400440c0006e00098980041d032a1504166540000010324180181000c0e01d80c1c00500455403580c00690301005010381c01c2100800504014030480c00501c252609151f0507107180120038403ca00300c92481b071700240254 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 511041223 1250 511039973 511039981
    0x15030b0303161b03051b0904110105070f060e07030c05040b01021b040905190506010503060907062a05010b04050123060a1b1110050301050306150301020906040602011a090f 76
    0x8400329041001c01c4070680c6101804003030b901d01c043c0402c0d010f18040c0c0000c00e05001c003401421704809202c0d1440f881042c10600f0000068294009040310440070300e0800e880e8503070383c0742c95030701c0d0403104000074026402c5c084101400880003401b030742240d01034a00780524982d04c805010403515603c4641d40160440c4540f89103103035034841800c64120000d000056000e0080c0ca61906105000010280040c0492801c0081c408108165400b514048014105034100307521450f65a111034030811046c00a1402c03180b45455201380060b000b00c2c1d071901c1c1d80d03a07400410302d030a5008202d050745581c81546803000103d101d040c000213058101d04041400c515142ca0f4a0030803c0582080459202308414804c044100c446a0440382500d98428100e02070706000031010450740000c0e802c801c10800c00c040c40104902d560002d6400e40102400140052520041000c2400392140c10003032600050000b600081859056001141c941401c044080c00c100c0d5400c01c01138025030503a042600442418042 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 511042473 1250 511041223 511041247
    0x60303050306041a0607050c0a080d09172a01020618100905210301080606040b010c02190b0a091a03060a0e130b13030f030c091203090302040f0615030b0303 69
    0x1c1c0300c0c22492404501c0003444400e00042c0e65030701030031085030223401c180c0d01da911a082c40d031400800f4103005000b41c400c8070600310004054202d540704502c0188150840700c1690482404a03044c14100804803001014040c0081c01910702c941d81c000c1c1c010303c51000041d8031a02d00795101403020b00d00f031300600f405140c2c65807000007600450b0300a882a0040714604c0e0402c0081c181403803580c0c5180a20300703880b9803428000c80d0420500504040c05142400d81844c03a903a8010301500c40f07650304a4011180a5112400e0142002103811035446c0c04030005501c0107880d0850040402c41b01042c11020280d0a40072101040307000541d44181c0021341c010050092504080c440e9600c1042c0060b040e101842d29121450810000e0b2188510344103190054810305038458286030418074981024008818140c60003040401e252088000b0000f02840042c1007502c030324000001150002c0042c04482240e0381c048005200742e02c02c5007100f144110003a100035000b0300841c02020300044c003850410004001c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 511043723 1250 511042473 511042481
    0x50f011202011e2d02150903090a0e160c020d081b0a06060f0b12010e0702030d090b060315010609031506120c0503100e060105060c160608061306030305030604 70
    0x102e040c0514102510b512503210349a41000020b10f03511240b022208603092403020000381e00007183c01146003440c582c00d503000504000812500c0840155940c0d51042440c03d6009866105a2000680c080000e065103040103050050020030400342038000100d005840158100c08000e40041d0f0301e40e070400200b04c0c400d000d0001194003142051b50f807264028007608120031a14110b4130660b071400309100321080351003190042c103200800b0a140c002180c1100c091000140f00300546982e05000003802c461090054400c40314501500340020756030b51802c440030140c200c4210340a40700d0305207190081d02ea512100c5048609607211034540c03d0071501c94402155102010007901034a90341d0026010307007602c60020046015030703170004100b420704080500304080d00c10307844d6050382401c4464401d0b040100d001d070b0440e01c0840f0800d039100c40b109038050400c1021061102d04900040e00024500d4200c0c1007240f00e54011954852117411384401c0408441e118000540014014400034806041030781c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 511044973 1250 511043723 511043759
    0x203070302070218011a0405030303060d060b0409030e030f0c011e020a0f1505010801021317070f0b030708011a030a0c0e150429160303020d06060918050f01 69
    0x150152074242d8036004600511420780e0480b40c01c0d100c003801045010694034000c04107004140c0d200d854185001c0c000f941d00e00010740201e10030b09541c68803804100c404e80c403100d0040d101400078040d240250030003410100200301a24040d0043c034904c00702400001c0780d4100103100503150b56005065813181c0000688918510310f0035440348082c0600031500501012100702d00c2201e40300022403040c0c0c01042a900c0c10f038810a066030062200e403542e01610b1291f8002d030f907010320b4014100085030300320714034003100f550010f0a120b800c203202207038070b44041c030065115140903101c00020344d0f618041344601c10070450440708904014000309111180b250402034418926140448440740100002000c0039405180b800080400240806c28440c1650301c01c4101000170501904488800e0b055101c20f21402c0f54042c2e0001c0028840000c00d4026811b40d01d280340c0030702040003c1c603100c400c090480c80407030041001c8071011004006c2e0380d0031280100c0e84036060b24142d0307030f140381d107420b840a00c6260742d0743d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 511046223 1250 511044973 511044977
    0xc03110a0512071208040206032404020a091a0403020f132318060f070e1f02160e060a090209012d090f0f0b0904060e0f0f0a020913020307 61
    0x240d08200450020445007071054001d400443d40c481c0c181c9002d00401007803880040074400080100001340e640c502c2030b258400e200ba0004615001c04180b0070546204d82a140c0d44e105101180111030319500c03d01c00b4066440511040659021030034401d40035000d02c0c07000a5200b05407000c80c8170030303051410090001003125040410400041450b84403485521070300003180c041e400c01041845034a600070848010361413006084581401e03254101800c60080181e4144902d510011841e519800f01c0700120400080003006440041c4000948602251090324800c2049040102c1c82601d10401d440c0102d03001050303074210b07c4c98220401c002c1d410654a40303052181419511121100b40140c845203905000c51300c4150022141003e094002c140e0002405c0a481150502406900c940305c034080c6c41c006100e003500c071241d040001d40940300c99001085007120f00c6003404802c030f04211b01540982c2404107188030340c0c2c3d5410303214002c034015985e0360395109030000410480c408055004680006040c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 511047473 1250 511046223 511046233
    0x506073006030501051311042c0c0d030f08010b03150906060f130314030f0a08092a0301061401090b072904110406030f1211010c11010b0904030c0311 66
    0x183d120b1500310340c0d08407a50384c0c800812101311400c12a182c802c1a00c1c1d55000c5604205008403184c1c5c0c03c50b0001d0942c280c1d604a100c2985180c6400c400f040f818000b08002406031480000f1403800900d0007c6100d03800c40490501e074008107003842044241c912030300c4c00c0300e0401030020181c01000110900500f0f0b8580240d400c11110065101e0000104a001240c01140c0d42c05481d42c9480700050b850b00141d0349860f001880302e509850355410803182041c1c01c5203065009034981540c41c0d810040040403000e0390004250488503001d00701599880c241208130020030140d591036044c032003001c150801603400162800c0e002d01c0043c0c0d0110183c0f00b40350080c40343c2c03c04010030002100061a00000c0740301491410010402040720b00400d00c002c2600640e002c0c004185103540b100400070038803800070320040f111315151809510682004030201d291100070700483d04401005494503032040d08080c00c95003402c80c482d800d401c00515950183c0d6055541c18000304a980301190041e940040344816070140f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 511048723 1250 511047473 511047479
    0x60f04080f18042405030313030b0411040c030b041b050f0d11040b13060c02060d0b03030909150f03010915020c0a08130f090c08011e0909050a0506073006 68
    0x1688903c04d910300c031286007140c007950f902003000000e02c0c00340c0c0030511a5208015442403000c1e01c40301c0004417580241d4040198980e0f1400070526580400083d070410300c3c043e0800f440ba03174590004100808140c500700224009440e085030054a56205039010480411035102400f8846000b022a8031138010006410000e00244180d1644640d000c0c996040b03011406414014031944000010403050419000c100074175400300c1d1003400b0760022600d40a40c4d40300c10308242d490600444c0c00c020f00007000030805103800c0552480d00300c41c803040a0f01440c02e0014241c0c05060503c02c001000340c00c40d1484034002c504034150300103580700310790b08603240c060183c00d01d00040406024103007140b141d260b80a1081d00b0b0040b1505c502850740e0000e501d0a040400b1541416001622a415104030300d04111020007840001a020280c540c80403140724507001020003400701c00300e90b243c18544240d007550085d40302c000080364031215000c44403440c0c0509050880d801c0e6980381090040750144c0c4804918103039 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 511049973 1250 511048723 511048729
    0x11d0d02030a080409060e04050a021e04050a050f0912041221020d18050904110a120602041806030506010b1c0509010e120406090b0d020912030c060f04080f18 70
    0xd0600c81183c910901140620501c0d1043c000c0380080c20907076605c3d05541ca0f00351107043d580c2c040c640c006801800030b40c80360351680c0c902c0610070381c108030050000c0c00b460031300d102e5040080200310790030001000c030b0700081030f4810b90100b0100c04400c1401141e0307040070704009184a14075071150003115038900540d9000e82c000c040c1c07045041028147c2d00904800f200c881400780c0380724110340541c0001d8010f460144125520401415005a00a004400c031280190003182140c5840d80001c1403901e08001344100700303d12500140190b4818481c00f04107000721710049025103546020050203504124010300c11000a0782c0584451500081420811402003000404413607040d180303a407150f5101d0741c0010207120300f00b040849400042c16182d152a1a01c2d200901c1d010f46d074020311145610001d542030914a0507010b4580104c402491243c500a00010460f581da0204141c2d9135580214000118071010301d05103a0300c20b0313402c541d09030704e0300884056011b00c65102104d03104a1081c0240340c501c45803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 511051223 1250 511049973 511049983
    0xd06050c0d09151503080301030b2a04030309050406080622150b010f110c0d030201061a04030b0c0c0709020327070503070f0f09020708120c070b0f06011d0d0203 71
    0x70303003d00307004030102082000c4841990603040c811075600b0a0040c0402c00680c001046074116074208104486549541480a00e60a00e002ca005296403000c0409101c41c5400b80040007103900c80c0c0c9807507055030b03562010b00050b59841c0c82808030341c1d0080303000510103105c10100c001030b010305210a0302c0071045954a11003000003100b500040144d076285040c0465800c62003071324004c0c00a080c000914841260951b0391048060b078414001c1c003c0c1221001003600035040a0042c182c09200050702141440305c64001350402d00c805d4403510100741c0416054010681220703003600c0da40000d09040c03420a038a180c069413024100c49044041e071200d00c681c200004902c442c0c003020070805030000c580350608140c40d1021a40090f00109039402d02044031141d4030743c0580884e800c500002d6100c4410b402c0c0302940d4024410b0f80c0e040c0041007010420002e4aa10040006a200e0aa5804551a22404007400720003ca5009012451145801e40f4a401d45201c0003200d4030010240c003180341055000c20300b04 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 511052473 1250 511051223 511051241
    0xc1501080c040b310507030b09010302120a0b010b0a08011205060a052701061806060e0d06150e070f090b03130203010e01060914070201051b0a0201020909090f06150d06050c0d 77
    0x710782d5900700100da00780315010705c2d40c12012615040c8100c0c100c1c040011030114042c44020301c550303205900140c403540103100050703041e60440c02c1a192076940308440345040d44529100320000c3c0c2050004904100455001c0710161f40000041481d56a80a01c41c030040501800c1c000189107011410074148110354a081e201400c0c2c01c0010404d145002d401400e4202500e81d6241800d0425a00b8881d040e4800c2030f01c02c1008003100c41052000150402d0340c0248000a0b4040168000d82004115040d0b0307024500d010382c0c0f0b03544d81c46144c2c6d015600216141110f50003601710054003003000c103d84170b0001072000c0d0302074002000050310b24a80748c201d0b821611035a02042429441d0007880e040300c00898203940d4044468002030015180103c580c0300c0a82c031101c07030a10345140c04106816654401d505903140068040d1109000d0f003000f08420340d4903507040040030305501c203000024051440100351a2403040000d422084001e045a6442000d414000c0c09e0702c4030303060240311840c4070010030f008110074 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 511053723 1250 511052473 511052539
    0x150e010212040b09011205062b02031c080708240a0f080c040e010b090c2d1207171b07050601030c030b01060201090203120c0a021002030c1501080c040b 67
    0x140d10013030000900410361140ba1081050b15240030044070380c6a03168507400810308000e040720001c006c0c241aa0040d03804a00107905441020703040e0803040d020900c041c14618950300c500d04d9070b65481a080340c0b044801c0740c1c914282226481c80220020340140aa800c1d014028001d01001c2c0e1100b00200a5040c25800b18245901141c5505e109082ca4824944031900680c020301040303510101285100700050015a59280b0016108446804922502da4141620744850340d81d4080c0250111603a0003100306000000183e00200d04114050680c252a0030b023240c4100c84a80d40d103045841081480041241c3d1401c420003244d4001002406524060b40c0f041152450060550502201d0560140c0280e0300750780c9044d00c940c015a400050404880e00340424583d6160f0564900c54100101d20710003c0d0080c8400fa00035018903000b00250813102032410482d122000f40c01001240300c3e40a202c1c04007290842d11701d01c1d40380c0c03d0075004421400000307010400b01d4113141c1400803400351100300d4099 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 511054973 1250 511053723 511053727
    0x21b0d140709110f03042301050702030702010f05180906030f0106080a0c08030c07090902041b030b03010b18010314031c0f05060d021f2c04060b04150e010212040b 72
    0x40100b07501c1c8600041182a080304a0501c80d03882101800ca2001a001131b005100802002e00d000714842c60307001380e0140340030082c8158201100c1c040e41d2900550300807030200e0002454000d07603038840c0b82600c04141500c000c5a46200e440c00c24024281c0c0041c1480c0e4050140f00b0101020340d00c24003032000280991002428600303024184206018515008542160000c00030204074400004903d000e503075120b907000030003000602c0050300600740c00340011002c200d40b0060f85034068050707001c1d031074007030080d0002d10103c0d40d408104003030480039518050400080030018030100c4c1d2251030b0440a0950704d01101d00d0840004641c4480b07625943ca030405c4c15403140343c60701c10040c1e1801040c1d00407100f510048140036440e400071b540703107099036400780d000302c58180c401e06a81d2141c2c08445001c0c030451441a0fa050038004e05401c0682d850700143d001d030f0b062072000180c0039400022101202c94218403551811407001044480e80c110950150440c840c0c081c48200031030480000700001c0034488003842e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 511056223 1250 511054973 511054979
    0x6091618060216050105040e0a020f04270f050112080d0b0d08070314161209050910080714010e10032c010c23070503160b01030b090607021b0d1407 65
    0x143e035070340031034014504100301840100030f6910300204d5a60016031036a000f40e1900c0a51804002500555210078045643c0300321660364008042c83d4010603103003542081c0f1680c10a1403020080d50400e100c0c40340c0003e5207241030408140744102805101100210110b80080c0000007d000140000c3d000d132007030403000800c0c40401d601324820ba4003040b20b40d4a11070600098000d40560f59102d1840a04880900204035034401c1c4145c03d80d8001d880010034900360341c140204038019100260089007143e01c50310401180c50b149035450051903007416500d204400e210301040c81010303808010750b00c09050301d42e104014a03800405021010981c07940107451343c01c541003011400c0d20400d229000511240c00c900c0520981c840c1142807503c20340d040016620404c0c1c0c94401c0c40c511071028070040c100d03101804401080b40000da014100c9010b182c03404619103a030050030b9140c06055485002503881522110707070703000710290030844444006001d002c1c4a400b07921070b10b0004030b2081e6081603c0d00104ac040c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 511057473 1250 511056223 511056253
    0x1306050909070303080c09183c0601030e0a0c060305250c061512050307050d0f0c0b04080d0e0a210207030b0c0c03040602010204060e09060916180602 66
    0xc141c1c099400001014098910b8034003420b8101e0140030f0207101d01001a1071005d030b4030780c0750520102c4403240c00c41c00b12a1501c0003454062584e040095065245a411400b0f01d21419808805030041800003054194031401c006400031300d41c409110340c00d8001c11038507202040310304241500030a80390710003103054905400341d01d0703580d2242040203039480c075001245001c90350b02c0000707c481c3c658400c000180c0003c1c0c1e00f103d41c0100742154090351250507128071074410020044090a02e541c81642100d002e000060300c00d4918030600800f50300010504c0c1103104c0842c1091240130b81040c003c2001600d4044256882e105841010402650700c0d4811a1071000f0025001c9001000c2e150311603030104a120020b200030744401c4644005040306840102065580340d952044034188a4190102c0741c1e038983c4d0b20b5011740030750024880c441c0850420b02b03d01005003004235180d0703ca6040100001c501c1c0e501c1006c40d5203003850003214142004150b446205500d000e41050f180a4101da070020a0207480c06502 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 511058723 1250 511057473 511057489
    0x5030d0504151e0905010608071d0a05060d060902040209060a031b0e1003020d1104060903171903091109090a060f021312081303060b031b0a0510030b130605 69
    0xc0d00010070320b80340d01a82800d11003242c0041560390f005011034240301d1824201d000d056560002c0e013040c025640c00103841e555042c1001742c1120318044039180d590300c80807120100c0d03008071007154100348083c0541000402c0740e80600000c503c0240f00509000303081d00444d1254000c80342c100e000c6960780100314940102034400d00000b03016482d00311031094541c000302c0e240d568a01c10103000c0c142c0100e00103110b036140340c2005c0c811080d22410152126502c420080c0084080c1c40242d81100d21012010060300e400000c80d2203281c6080307404419a01c441000310010a2904400d0b14816041d20481c402035980d40141c50164181000412070000507080080490315540300700c004d060320401c218520204044508011115024100f070024031181c18a100b61307100b44216615201ca090901008209440d8000111050142e041750b030050502c850070040d1000b4228040c1e40004481420401480c0122321a121842c140c076005c100d41300c00c03e01040c0480d411495450390291074040c18000c034100b00c80303 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 511059973 1250 511058723 511058753
    0x803100602100e100b03030d090807120c081902010e0607020c1224071b030f030c0e03120d11120703151401080a090b10060e04022a01060305030d0504 66
    0xd0108104080301d03090715621540c040c0301511098a56443c4201c0d46c0d42842940c20002201c14280030100d5a4035004865030b1041030111417000f02340b40710488141c400c0c00f6113000580d2154041d854402059011070400060180540440d03496000601103050144552401602107030024010513030010100032044034880d04041c0207900a10300d04800441d000d05403121840d03190789095042e210f80d202115101d05040d3380b80c0300d0154420040c0c4c1090341c0320036907003103628035070382c0800089189000c202e98143c4403002403541a84000511030440ca4400010000d00c45407180000304560400c40ca4882c94024100c0300185d00e84240820a4258060107201d0080d50440d24411303245041078801691000041d4440e810010004000780304607100e944480d031201c1c0c10081c0224146000c00c4e1515249106014190024100b4040c005240c10f280c0246d50703103440064102d0510b6510440c0500c0008880c2c9443c0c0e03121b41d240e100000204200740700a00f010006214003042038039103802c1010f1034102c420 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 511061223 1250 511059973 511060003
    0x50a21050f09060703030213031a070c0b0a0c180603090c08070317070507030c0306090212030a05091516200609090708040f0b010b0405010e0f0a0e0705070803100602 73
    0x103640c0703019590a00b101c030120b904840d481d4a821550604a00074081c03c0088140c690b803591021040c4000300101400c0d03000350004d0300d0001d60750032800f114a0103031071b0f100a002c9039070000030031600c0c0c3c45031708006846111854911402400d1500c1503d0b03040032a4440004659603400c2c8506025200e0328038400b9064810040401c6450340c0c0e6035504c0c000002c81c80e0440441c01207044810000e0a0141c2401140c01030502080c080d12400c000b4000c160b03424080744110b80030140c80941c4000030050b038402540c1a00e40783d0900103400d0902c0111484100204101582000451074100403441c5022a080c0500b1401c040c43c403114603c41550014080c403140704450500480d007a9a4070711070070039481501d9103071808154841d881d080b0418140494001d0101010308004a030b100ba0440140040750000d988415059903040180076400c00f142c003500e600700401100030f108004d0010301103a080706551034180d1410a5a48070000c082c2c0060b940c2c0c0e00982224a010491240c0c10030411102c0d411007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 511062473 1250 511061223 511061227
    0x40501080705150c0c060f0901080916050402070f02100c030818030403241406010201150e070f1202030a0c11060f01090b06070f0c0f0b0a0806011803050a2105 70
    0x1400660300c035400e841c03150b082e403e0014000303e030001e0034000039a0035507000d0f0505480302103410380080030782c00003511140080c9a00b40003900c425000a04c44210415051000f02503500f082d0511000e540b14603410744400995410900c01030f2101c100e20031a103070b22982d55a07003a000e1483d00400059014144003404c8401c60b1400480328008011181100c0c0c0c03014400002100c0700b1003114400581e1074806107614640101c04c4a03012403166018440c0038264001c01ca0513a1640c1650180d200601403095051024400a11300c5401031000d62042c5040e8141980401c1d0b4020150081e640708480c4220007585481761010126000541031100c1c2003d07402811280c548201c0c0302c48041414407900641d240c0740d050b0301c1802c1c0c4552003103903d51074000604041c00c1c105410921400d103034500c00c102c038150010500041e04174011090360141109643c170302d0315646402d001150310004145486088000b009400000184204840100e03144200104c802810710608500002020215040e041c086c0c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 511063723 1250 511062473 511062479
    0xf0507080d05030610031d010510060c0f060b01090f090905011a060d0b01090513050f010f06080f06011209141507020a0b10090203090a051c090b1e0a0e0405010807 72
    0x1100f41d0703a0009003595500107035070380d580b000c901908101c501403020785901080548081d4041d0851481000400d00000b42c80d03955040803a40e1805100d400381c407546030b00c001240024a150041b5544d2801454040e03143d5403900302c1601080030585c030071420103a441c010300d002c101d828010036084030340242e20298803180c51000304100d40724400c00034135843c0d55206031840a80c0100710074406400040d045520f0400500014401000d060300c24403038480010000051846a041d0444d041d260b883c0c4e140b44d050b48540c20341503109000505094188121070440c1800c11030148244682c6c18025407014050500c038011090801242915401003000c8036010801029000140c000031254042d01020003641c0d007490102e400c001c942c003c0744110b070000051022244000175403441882c0180c080e9001119415070350320003c0306030306d1010f001c40c1d401780c01084440f10440c0680030341192100880341d00b0100344402c8600c5e44c0440c41c02c8009c0380b5000c010300406d040a00c100c501505c9031000421701d10741 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 511064973 1250 511063723 511063727
    0x20d08070305101e1511070b090114030a0f0c090302180f060d03031805070e010f0e06120307050a080d0e12090405071101140604050a1a130213030f0507080d 69
    0x30050280c46403d02401508131042d200c0c2e9a540700040c1000d881c540c182c1002d0b100f00800341074034070044030254407030144c0104204048100f1a1a5404140c480240f034050790181c036803c076000100416617071036030348044885844e001d0185034140f00e81a0781d4a0191401d52041051035080d40f0701d00942d540a01c8104100101e05078882a006502210408003081c00703427400b2800752124100c810080f00d0075080241c03c11000295203400c0d10501c4074180c846030b80321205040260394074030403501040a1003000c110b982c02e00c0c0d945c1c20070310f580d501e0640b8641003050320703503520b40b040c80340d021a41c1060001d00003070350150b94410b20780c10b244904040c0910ba4140c4000510fa030040d41c005512440d66140860b0040d40a0100c0c032030102c410400a000281c03c481c0901051134048407082c2c05103061400003412041c5910071410110a07800018540c0d441c92000d11508a0900412410855081246031900806080360500842c450408120b0405030342c60442c1c2815560fa00c00c02c0950310130807019581c16 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 511066223 1250 511064973 511065001
    0xc090518061506221202040c0f0c0611090d050618010b0303040b0d24060305070c02010804030f03020408030f0912010209060304060f0b040e1509070602071806080706020d08070305 79
    0x300c5603e901e8100d901c4001c0100c00075070b1039000031030025280c00522a90030052808001d4000c0f1010800c01803003520990f40403401009000c0010060342c82d140000d0303215400152808000403000f0700b4040444049005d41d05080400d0780d256110504029102c00304a001d84c14405000c00240600b80310640400d5481c02140030706e0203010381c0480c4004001001740d204000d18406814800b4030441c0207100c80800706a207019070400a414400081c3e2400d01401040d4a030b00d50681d507802080d90f03a0b442c00c481c1c00c2c003c00d40c0181095001c020006102c01c041014041c03800c0307403041c850b030f44080f29810017101c5110301c10550500e0b4014400500c003541d445090340e034000d403c01e00c0450a01c02e0320510320f00806c3d0304402c45510924015100f2000c80c17002500b001c2002880c02c0303008003601c6100e0403a0351096584509401a0700c0700605106d0740c60154080043c0e0000003502007900b0b5280d01825081c4400d980003000161f0120407500c29056101d0325464100b22207050420030350501080300900c078 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 511067473 1250 511066223 511066261
    0x2031b030913050613020a081603060320192d0e07051c02030c07151a010f0201090b150108070f020a0f020d06060b0c01060b0c0a1209030c09051806 65
    0x1039590740050b045031210545801c4600520038115950a07d65401a2050106461010b504020b42d5000f9100a0007031081000b500e0b0042c0700034842c500c1508081e40c3c81d00c406c0310050782281c1d11604504940480c054035002404104041190260180c0d4407030f410040d03d164842182c40020031f0801416100100c140d070003d180d07143c1650349810102144204201d6101c0da288220704c0001080300d280b90708806407010343e210310080c0c00e0702a61442800c041d03071210f20541c2d14480c20034540102c2907000d0311a00c883d145a42c000454242c0603903c5070411628210760710041e0070007030940c003401c0c0d603070240e8040d41c441c0c0720307003002e50f1004094a4020740da15454400248049040081c600542d074802504a4186602c10410300100d500c4060840540c0c02414212581e98200500030a084a081c829280c000a400000782000e500c1c03074462481181c81d0f40709001c14402c1d00c890210200b11003642c0f05014007429400170a0741d04001d804c5440400340a14001019000741c030a000015403250b0510010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 511068723 1250 511067473 511067509
    0x8070b0126060f040f02030a05061911181023120c070c0b07081902011506090e041112060f15150a08090106050a0621060e1303020703021002031b0309 66
    0x5c1c4010351006c0707480d204182501400904c0364104205900711308214a80016988010074080071f450500101517500608006003043c60070201c20443c94103007503003030401c002c981d49071610340c011003200620701d01d075035807000168901d100144e40e0b150b401e045c4403069000300b00b5008a5240000eaa200c0c881001c1c81c5018012055500080345030074050020107640008410794441a00c480c3d000d00042e00a150340039282c1c1014059050000b595030184100c1d40c22154107140808035560b456442404000418110070350144414060801003041041140e1280b00811810b200604002c2d08919100e0946010b0a21915003030203040001ca04d54030a89101014904150a00c2d031107616107a0302500c1c0341c1c1c00143c1c026201007000034999038440e00742d088011400c2c00e000401d810300100c0030190ba156014040d4085603441c0070a88200d4105a00c640940c001d1040d2807169440e50f00003403200c203200c031804005074004104070301c0401c1c0c2a911a45140f28290041d460010041c01040c04141c1c43e15520328 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 511069973 1250 511068723 511068743
    0x30603150411130c0e060f0a051317070f0e070e040c2c040f0513120509060f03010801051005010f18030b04030503040308010e0c070f08070b0126060f04 67
    0x1c10440c840741110701d1150018001c1490040c036210400c01060360350840f03c0028105400c5100d241001821200461240944146403503401581651207a020007030103402e44c0280b1100052804421f07610445070342015000c0d018061a01e40c5551a480b001c0e0420700100ca210000d10540c1d41d081054883c1035141500c022603d13204420f002e031443c8608500182407140c444020008554040c102e900b4080000c8504201c4940c071012004103ca070200e90405422a9450310742c0c001c00c0c00074141c200649100e26010b0714028180c801f1850681201c2e202180e4017402200500070407200307004450b0310940140721184014a4800000d022000d41c49000c406e0110801c0b030703841214000104800516000b2000c4461800c10740360041090340300311001e50000307449100200f07552400001c19070048000d51030840c1000c03030a4548201c00341d80703c1070403074103036008100000c0001d501c00c4540b4000c3c07010340380a0441c803e103003003408410042c0d50400042a040b0608002c1f1024214000c9038004d0f4000d05011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 511071223 1250 511069973 511069981
    0x4080c0d0201110d02010501060201110702030601050d0c1e03030f180303050d11071a1b070b1008010c0908060106180323030f0c0139021c0305090105060603060315 72
    0xe20f072076010300c15540b540c0c025010744c1d00845405400c000c0c102c40740f0b54001c03c0380244144e440291401a80350007545034001d00010000303840c0001455182e43d0090000700c1c1c8140d0359091004440b08000b43d03200308405c50b40010814150009a00320008403541054420068205507200441a41b80001428002d000c2103609000f15103a000194594017075800d10768848250404103001c00c0000980c007056035060740099420440c034410603d0316403001031618100440c40e41c0714031400d04001c00d000c0401124400c0060703840801d00402c09401680e441d46035829050280c214140318058114405004a01d0071034010600c90814039011650041c101c1d0440d070101d24000d098041080400c000140300108408100b00740040c010079241d11420700070090080c0711400000e02c1c0a14110124048240203004002d41a40503e521411140c900c10340e40700c00010460b01550050801c0304200291742c1d40104034142c1d20034440c540e08104126800340c02c40c50075100286e5110b44845424003801401d4000c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 511072473 1250 511071223 511071227
    0x3070f050d06061d030111030c07030203070c0e0402010206090303090c010c05070b0a11010b030607050a050309070f08010e16150c0302031608090438030321070f030204080c0d0201 79
    0x788110406946090000c1d42e52010014000d540140843c1c80c0158000b05034001440c0510501012410300012641159030300210948503820000c0f090702503010401c00c050002d1240440c0c48044e18010044000504050000919001e0001c244c0c100f1513008005000104074000740481012809180c04141c0701c4003032030f0490500a080e48602c00030b9101003008480560845001144110414002c01610061000b01940c560702a2039940c00f2800421a19a209103d6801158050304003c1101c1e83c4942d1010ba01102500540c060300c440d075505e00c00f81119543c10301140c209c200340d60004160887c100342d01c80038640c0c03040d81032806000e14a4492400c15000340180c9241000050000d5280c010740c0c14a581160700903c2598446d074a4401c00020381d03640200c44045c03d440d0b081c00d20a510038000200440c01c102001f80da0b03803603c014003405418910920307890300c51140154801c152401c11400181003560407040322024135005010511001c000085c004008150031036000300081c3d00d40c001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 511073723 1250 511072473 511072477
    0x140904060b0a02011b030c08040b06040902120f070603050c1912020c07030201080c0711150702030a051605011419030605030f010c141201050409080c06090706170c03070f05 76
    0x10940700e4107000b0a010303a2a54041d400b00791071500705070420003443c80d84c000c02c60450704039000d400081480032001c500804c400d585c0084d48a1400780c8002400c7d00b407600090784540c08043e807611658040303070b040760039002c00344802d00041c0510f041c00e020904204042e00403602610300e0814100c0031000c006180103108000c00c1d580d60b00203a80455480350380d09281070b00c44c070803808180d010a00c494041b4006558803801ca4001d10f412500c0c910910b42d0803020412074090103051256a080240a0a00907035018001e0001c401d214200a1050681d1072002c010250029030089052000610105a43c20b060030200c1f040690707540030f050b0907400a42819801000c0b5038116036010b1144004032514440158410f1109030540e445a01280303843d50b02c2503445e489140e2100944103800c0c4010030007401d05422075100588240003240c101102d001000d0702c0c0c0780e002c4508807000c0d40100402c200d0260481d9000a00f43d403100c1c011080fa01d00800c0c1d2409610026181c0c5c0b0800c6000301302c44800c00e2041d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 511074973 1250 511073723 511073729
    0x6040612020a091215060f0e04020d1401180203010f0507050f0918092d03040b090301020409090b0f0109090f110a09023603060c030718031415060114090406 69
    0x4102c250358151070030440780c0340d40c490300e05d003403000d2030180c002c0380400751081940100c401d0441050200c2c0d40d95421b000302107005600864032404030006d0b0110b11002030203090316001303146084108030a081d004150a4500c0352035500d0103146040140000254404202c440d03084481040c241d54451880214a002e0580c0c100c12018640c0b0405001000001041c212198448000d050a08088400b04441c0a9a6440240d101d6038002c020421030314141078058642c1000c001d00050805039103000d110107468500e8812280c0840c0e040801c0f584541c0d40720030034054002a001003000007090343c0c890354903121301200a4001a00f62200c4001580c498011b80d02a04009900303644a07010070100c0049110044112045201150440c01071015641e00040c500c15000700100410703110100c40741001da0003d4000310810601c400c0f007102004155100300015449802880e065441c0320602c0d1f400e206402180000fa0000300041c00402d80c2c1c007520088602c01450440360f82c51194800140042001d98 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 511076223 1250 511074973 511074989
    0x606120907080a030c120206010f060c061b050712170c0306030a150e0f060c0711061e07060b0f0d030503060102010b0a0806070e010203040305070909020f06071b0506040612020a09 79
    0x110f0380c0c00070981c3c801030039001c640c4121099000c040e0107007000d0380c40f14024041e04200d100c81c550204226841003001d1107000380540000031360414914680e0b11602502484400410000948842040745c9610030021420452520440100030000c180303489a1001d00840342242000c004103040d60703424400080040d5000c09180643c90201c407a040c007030310108619a00d54051703021402c060001c0840c0b954482c0c03659444403460440c07599642c00b40000c1e50141990043c00501c071480c2602e20311001d015001d02d0a00c0b901ba201c0107185410380c1030700d030643d44542c0104503247d04140c06441740400d042010364142012500c2e91380c0c920040f401841804912907100e4048180020b101c01e010401e5070241401e640e60010031103400f0016613591041d03200003080c030381c0844004c00c00391000794020440b2038401058913042c46407060024404d60040c64080d00d00b000004040c9810207908211a00142000c0d030f07680e82460f25007100a8089031180e800418210b80001d25485054415001000600166 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 511077473 1250 511076223 511076233
    0xc060b040c1101060911090d0501060b1b01110c1009110d0b0a06050f130c140714070501030e0d03050604060302040509032101230102101b1403060612090708 69
    0x901c0300400c0d006074050b111005518000300031a0412860162144c041c951000321482c0005500078012103084030780b01900c40c5d55a90078045020556100105002c84128040c1c00f807007240c10711282c1c00c41d1408548003060000800002d001c1200205403018002e50410000401c1c3c1d0840c141040301c005032580307203a8003045058005042216507070b19680512414131b01040000c0d01c036010f01003003c6c8039480c184e81c0b109a5000400450240340c00c20030105400f858081c6940c190340301c80741d8250b007101074221200582c07080c0030000c0c45010000f1100410007441e041c031a02c81d02e00f00441c0c94090002d1440201900c0f0710006602e0748440d003048008603809881004541307000c042254482d04004002656801001146d10320361141004050584010780541c0803c40300c1510b41088414000c1c080034198000c01c21600c491110600c214241245c10700c615034210392406d030b001000c10402001c3c005a440d0144240038132902c0310303030507181203502141d40d0b1413098542d103001c1403820b885507000b11124811 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 511078723 1250 511077473 511077491
    0x106030311070f18020c0f010f020a0311040302061e0c01140114030d12020f130801060503060a06080601050904050a230f031903020f070609121d0d020f01030605270708160c060b04 79
    0x41d940245081082039330100a40007001008500c03d10503448060b6101405020b400201c58940d010000c46040c402e070310501e061802041c0302c0c01e46a40e080000f4074485600010843c1020702c8843c40341654048028041020664002820320518211001e40c070b50b50220700300241c0c0001c042251304024070000c518020554540085010700540e020303079030007030282d84082088202c1c94000e110582d50f10354040d228580c240000d00041d84401001692903203d07203200440495042c0302d0b000710031540b8590f818020021240510701d48403c9108406483e4010810020010517448240056420314500543d844510750416002402031007000fa21403490980b50000b003010079600100005126210b040d0300c1d140391000d01440d4440d40803155040b0000b0044040149044100c2007450601414005109911072303005c140354014050302c03448019403c550140d008840c2c0c0c1c4840da40121140781c421000d2400441d64591300700d84400c07020600c1070380381882d800c1041a82054440007005403081140541d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 511079973 1250 511078723 511078751
    0x31503051203011e1401080402270405071707051c05030a090905070306051e1f02060406051821122706010b0a0c11030106030311070f18020c0f01 64
    0x4000e12070040c200d41d51480c40c0213410805040c0e082100c4140c05031091283d21000192044440244101e9015542120201481025900305021041440400e034118585840e28a02d8812240c1141009030040600e01103107510001e01107068480a43d58440c0b2092030342d01010000f60b031424010254000807070003240d00780d40486184112000c040c003c3c0f006031103c0b0070681c100e82182c01010f8000c0868051500d5140d0a00701c0c622099030702070642c60b0064000000032400e0820300c3d40200050b0440c00500c014011240215030b00040b190203a510b1400f810b08a19507208121500b807440380055a0b21120010784a1041c1c803050003510f820340d511460700c14220840542c4106400f020745500007000040190f00240013030503900c3d400502841d0001441b0243d40c0f500800c07604440b000150032500800da1820b002d400000c510941b51204c04e064113040d241e05003001c0d6003184100c00040070041040000b480c516011003c04882c0040e41c88180020850030147ca18080350519801c04c03520080c601 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 511081223 1250 511079973 511079977
    0x1104121a0f040501060f0608071809110c060a14161701060c050d03090528060204090606090b071a04050a05070602070f06050c1213380313030315030512 67
    0x40d100300000c1080e1612103440000d0440c0300d0103440c0024030000d0000b60200d00454962b42c003031804040042e05160388450b11801c1d25108865024000008501081d4400d010003046810000824050059006565400d011420f0080c070101c941d0316030036401c425060242e482c0d0f01d01e560030912054201d60311454007810090319502c00b140c052280c1d1500755125846441000700066100c006004a4000d42181c0e07172910004030806a60030300d0110482c400100c2910081004040f071100200b005850010094510103141c0c2c84035200b800708110b200002400784042d034125000c88842145a500d030340c1016407408542ca0002411407195030008200c031a00003071100100c0d1007500100c40c4241d1207040840d0540500c10880103240d01880480c49010f01c80005007680c400007102108110756503a16041540040055a4080e040890300c20092072105c0261000000d408103192441d606200d0b40d6801740c8141c054014042541d118504004030a05803d120000c51300300c01100e0a001410301c640001d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 511082473 1250 511081223 511081231
    0x90c04090908041401051c0b01110a0b06090c0a12110403060f14060303070b150d1e020315040f020118090606030b03060604090c1a04120501140a1104121a0f 69
    0xca02c4c0d0b0000c82090340c4108112040043d0b100841c181c0c0081d003400c3c40010b00114450141401440245058405010400000c426028045100450415501340400001c018099030703900d1008210030048290020004000d08411450004590300d052010003440e008030b820003042c040c00c00001c040750780e5044d00603481e01c4e000584808210f44401c0304050382c9204900f002000c0000242c000358905074507556002c1810301c003503c9a01d58000940d0b071210600c1c5030f54a03207000780000640d02c205509040019010381041038118003414242601c6819a55880e004000e040107502040e0601e00e5400d41d0043c402008000824004540ca40360081c0182c4076440303806000e4803031940001e989140601803a030301a5003006036103100600305000b04407548102c05030481070040030400010007010040d010300a00b4010000010344104400078625040009404422030504041c4aa5078210f031001c100c900325000703406111301e0b00c203440c50030048143c4001025405030f4211420440840400304520380310b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 511083723 1250 511082473 511082489
    0x1305100605040807060e060c24070507080409050709030206190e0409020a05012726070806070f03060803040e060a09051509070e03060a0e010605040e0309090c0409090804 75
    0x10503140c040403180c0d4011440f544080b07500a10080000f103000e241c42000411020309050715064503120713102d18145c8000d8602e48a030039850307146821080c2e805c8445402003014607200b0301c0e00400c0d0b01c03540280e018a0185c09600c55440c004121403a01565401c00250f901a089a0315a0081840c100742d008811019a001c07800e494041d0309685003510443d2a40d6a00402160215040200460348641e010190746211451900002c005d14407514108000f0404a070b5403071002460107101c1d21006000c030440c1d69180d40030381c005200911000c5117403a80300100f89041c009464000d141240580947e038040c06a6010020307007c03403608844040c5074420710041e103981400b140e98000704412545e040741c8030740c0003ca4002e079041183c038005441941043d402d00d080e000380d010041c0042e0402000307580102c091580d441c2d0a034003005013030280c83c0003007400721810000110396481540c0c682c882d001d807441c480c1d00503100103060800e1a10540e0058013403000c3c100122207442c0341c0180503034414002d40782c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 511084973 1250 511083723 511083751
    0x608090709090b0103080a110601240e0306010b030622020d150e010509040f1212051f0b07140a0303290609040e21070b06030f12090f1305 61
    0x40c0000240a402c80140d4082c202903030b16840d588614040d0b410903907604c000c2041280403da05a01c1c100105401b9200e07546100c001441415004a0390383c0504908100b4004050010784490341d0106441c0d04542056075415a6176031540d002440310a070300d21000031214000c1020080e4902641d02506006121440c00c22841c803601d200c0c0260041c251080f80c046488100c01400346080100050b50014401c0c01d19525003e0540d50b4940020811110b40b0005000d8919031811091113002369500032450700e03210f0070700e038602c042c038100740c01d007113006840f00428000307400c004200c55001808621f1a2044c00d40c1c100125620740240070700780701d0714491034079004481d102c81a401e0000500a2031340d0b00928843c03401d4040c00134400542078460f18030b40107000c1d0325281c20382d10740e0340051680c90121191500b943c802e010301d060041003002802690003a845a003440d140840000b51031440c1c10315840c110754a841304000000c168178412074030150021010703001103070000503a030031881c000d40c1d480c00e0200d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 511086223 1250 511084973 511084979
    0x3070503010504120e150706050a05060613030803250513090c05041224200c0c0603220c061101050919050102070204020c1f0c120b010c05060106080907 67
    0x500741c0b242518003405141448010842990240840615034840a404140595102d003028803568201075401d64200c0d8460f020440c00c007145208555111404075000341c1403281a000080c041c0b0410301005040c16800004554800405200100604140b42214000341d0943d01300a0058020240f440d80f4006200c4011500100074014030301c40b00790996600c0d046c1440c2896140131012852802e40e11001c4604000760380c8204000760030104061100046106070000d250300d26806450030f10130f409550f09000241d0110000308565000c070404603a84c1d0b8030383c0c82d513a042c1c0100d400441040400d064007508107208003c02440c1010440b401500d81100a250070718001d402d903241110008910307000b9480c10380340d10105404958205004600050800d00075602090481e0b101580071031440d4000041c0c401038041e08004061450344580303003404000c220740c5010300b4140100c0d4840e40c48944900d0812810391041c20041c0d9583e810200716403540d6035508014014030401d644850700390248100c04 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 511087473 1250 511086223 511086229
    0x603080703110d0306080c130905060108010b011d0d0f1a01230102060f0106030509010609110d11120f0703090f11040b0609150a1808070612050613091e0c05030705 72
    0x501d00711940780340130f42a0f1034411f034100103403020b001c1d0518084981ea08104404a40c08004060181010400000f42ca4100b080050440300602015001003510303400c803601ca070703100c6440802000390703c14074100c0500200d19041c2d04465880e0b2410f00c5100882000240302c80c0c0b41280d04a150041c5d00c120911200c0708401242c0380c2c00202c0f490302c480c4451000400005100364041c03540715038000000500191100346032002e07200c4020012810240124900034640803503c541c80410451070040761814503c007500350041c0c10010301d40d4400c0c0d001800000c9000d40290007010590380c2c040315040c00340701c8900d000180c0403003290402d4052460480c03540c0b01402c0000444030000f000078504041e02150b0480790840e030f8012607009080101c800e580c480d030003031000888001f80244034081e0810f10708181005001c010100d0103a800e16027441c062088644030392404006560b446503020980b00b000e0304002070740303141c0840c10101105c1000030120500950000780810b407001101580c0c4150f0380d130410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 511088723 1250 511087473 511087481
    0x9050402040506070b1f171005070c140a02060403082106010c0b040609050313060206070c080901050a020705060c0c0103051b0316090f030b07030b03010e06190603080703110d03 78
    0xb503903802c40b03070810846001c0b0b11032080300742d44940d0888134022114041c014008148006034403051166840880d50740d2000c0040c0251054039065043c01c000601e00100001c2a0940295014000801d0702a0f00500c41c04140802c24940d0b40181043c2c1e5159601d1400401e40d5000c03520803003409428000c0c00c0701a40c1d03010b0105004201c16590030044074440d44540111340000b0b8011550309550300b494000081e01400904154100c4c081e0304200036107446030290030480c0003000030081104070071441000444507020b8a0b07030720303000380703441520740c61000c500b80d24044003904000c0e8802c02c0450b58010010000445441143c02030f41c052000340c50300b82100b00e103545071000c0c0c9000250300780b001910440780c05041c200300102d9868000c2c01c4582d110515030298100e500b05070749051481c410804c2080c8c060246506e24901500204036031905462019140c0e41d0240110308422100054440c1107202c130341010005e5a00182340030f599014514001d032004002110900d03080c000c03003020405d02da0081c82 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 511089973 1250 511088723 511088729
    0xc0c020105030a0e0c1e2b06020f0d0509030c010605010513090c140a03060302041b0f0e0a05190303030501121101030914011404020f0604030816020307050d0501050103030905040204 80
    0x440c0d605640303410540b030740075148664514a0f00d21408640d041755940e401c401c030324200c411079440303240402460300f4800d10241c80ca440184e10311503030b20080700882812242c911005c4c1c01040c01a1940b5003006201480d12840000340440c9081600f80b10034110080014101c560081c002003004554a20041d181703401401c109040c400541c403800c101c0b0203440e03000080d50003070501d8400c2007190004d501400a421030740f24140080d68601c1c0900c21420306204441050002440401c0d02d004d8000b070083c004040da4003003108014a045c0c4952140e00c1c3c8040c00c001810000f0901e812010305c0344100520000c203440141c000a042c4000024101c480900c249946500f000000200d0b0042000650180c07111060032940c1c400882040c0b5145070080c07060003c0ba5540241e034006a0602e0300404c200307040840010703842414104020000116864210354400d8240024408030740e125000090402c0c5e03080d805160000d0200308000c080207411350100d23050303234401d464840510ba252410300c412401280 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 511091223 1250 511089973 511089977
    0xc030e060109021b190506070c02030d0c11030316110a15030902130f0203070201050106030506131107080c071a04050f0609040b10090e0609060a0e09010e1603060c0c0201 75
    0x640180084001c0382c00800e013080b07040640040682c1100800b0b4903229006511400102c411503140007004824000380e90407803880e15140344143c0d5950006503c425480d0000b8042c8103100d5404020070a01c0b1100000c8500020f0680e03071511000040d140d90724030000c0045a00ca050305500c40060700c2e0805408040d41c1074041c040c0720554513000300350300510859078146da12855010200610403054000c1d50308020111901503100d0412860183c20b5540603004402491b061000304543c4d034641000303031003044901c104082066806103160800c2c0e0300c51407001420744000000d100c808141c00182c005c0440d0300000750004e03154204041c600850045004199218840e80c00d11107207480c0c80c4011f400701280007400000e82e0502e101c0000d0001c44606004030106651b06420000c7d6217601c030b03481e0b034040307000c1e16251502c2c580315001802040032070041c0100c01000038041040000e095000302002e504450480700c10712a00c642003502202e2612003240c1c880e00b88814521128450080031180a5040e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 511092473 1250 511091223 511091233
    0x4021206090a0b060a0803040501080a0f05040f0b1501050316090b0307020304170a0206040b280305010819080a270e0117010c0806100c0803040b150603130209181f0c030e 75
    0xb09c01161078450180807010a2901c0d02c1d10741107680240d20489001340d1244001c0b030401c103942e2070300345562400240b1405103406160f05810650f60840101c0c1d45c021b20b40d0428070141c695000090301d5010694201002c110400720402c4070183d00003004006440706240d0941d40003190305820341d42c0d00340880300290031000a020400200390210040c18403003031605003c4899480225900c8102c240740320b0001c0019449000401c010f8030203200d00c41020100c001c480c80b03205804e4840388024821049010104131043e100d08014102800d22014803401c01219a143c2039034403500e4001d29102030007202005ca1220302c072451150414401c01c2002040e03a11648510ba8551003008074408442c10400244168503c8038000284403800031031141e807041420700078a0a0000e031850181e211490200c1c05440100244802c81f40c407001d108840e5a0b046884010aa640b001c0e00e1254400090601d0040c0c803510840c0d04000b840340c2c4c0c41810780b95200f20b041102185840e0102c1c243c2c0d8151856802135005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 511093723 1250 511092473 511092479
    0x9040e060705070818031c0305130305071520032211010c0309080f01021209030a08010e06010e0907080405010e03030601230c07120c080a1203020304021206090a0b060a080304 77
    0x201e20003078208070300b100368211040c840310740101e801c0c00c7d4002034114840001c8454000c120b0707058480c403900900b15064041ca64072899401410f0351080c0800501141300000540b280564a80c22003a42c41002c0d408080d1040e134070415014460300f042c0d6601c3e2152819041c1c1500b045641c0c0c070362142050300030302c107904940c81d074000544110b44074402c01d81c1000060140803d02030070030403040c6440b001c52400183d40ea0940600495880700245c16180d4603001007020341e200c1e0b584201e6250660fa05102c2d030124503210b4000684440c02002d5945400010900401c0368094002e1120741c860b502903802485803100c011301e240e4403440110b59450115803044455032081c1d0342d84851010501e80300324014540308420548900d00007250380441d1600e1400f10b6440104041c066114005100000041541d250703146d4420800003c4c14104e07504040d8040b000078150b68440700c0814818507520291078050410095041d00c4d0324034144180c0b200c6055801080c03c505001c2005030449901c0d80141d8100b5003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 511094973 1250 511093723 511093733
    0x140606041202010909020a021b0306100b0c070503160303030b0f10050c030706050f040309090203070516390e160c020303071a01050406090b030d05090316090209040e06070507 77
    0x1801c560240d041101404010901c00081e00c000c1c50004120340080101890810032103402c2c0d40c0320b02d206402600b180b000d0240800390380c940f10040c0c401c0c00032115110140703091581d26042040e0302c0242e06202d0311181e00242c80e08190040280c0340207540070300c4030280080500072a03000306c940c0550803024120102031060b01c1240033340040c0c03800ca801e8916000b40c036103400040c0e5070141c074804107104081052004243d001003138400108886982075084d894111001f84c001e001c2c010315140e546400645a8040010004180303403052408070110080c440d0250300050300c14120701c1180b0301101c0342a00401e29000044a6070b00c0b48415100380301803040220412a50001700d901e0817078241c882440141e0001d10f1620440c0141d5002c0c500703030403070f0758942401c000542d0400e0380b00d94642850282c010465803030204d000c18a18465007001a80d03450b03860080303483d2060070b00b18903542c1304c500e4402080c200c0c01c640080590150488052100d6141c148586480324800e5a000000c60720400c45000040c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 511096223 1250 511094973 511094999
    0x302071718040e0726060609090601030605060d080c010522020906060906040e070201090b07081e100f09051918110a0e01080c100305010f030206071e03021014060604 73
    0x1c00070003034650342c0e9540d45690151250078442d880d03c0f2450400c2c0c900d800b805c200322036688494101d404003000c1c108444016220403041c017001c0c010b01c0d2100c00081254480610203c3c40302e81c4059010b0b40c60240a00080c001d1905948400302c56078452181c4242402282c1c0021040350001c10504290702d43c40c0c20000e9070b0380b00851244d00000c0911001030a001d030054a46c1c0314403202d40000c114984d45182604030101c00070850b03c01d00a108044c44200761894014a280d03440c00d58641c1a2616925104101c0c140a50302900b442901c1480c040780c4402950080742c01034144001e00001a244500c012040c0d600715826860258101c9428501003036a05c0002400050042c010f00160354a034400c491070038000f6007204580d42c0c01a18901e0380c1c0d040c1419141000d65552408122550400c20010600720191001903c02c2030041040c01c00d2054225803403008001490300030407511918500a0b48401014468100c1c1914024415420303420f00741030750303115840003071600d841c050401980b0040d0b6 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 511097473 1250 511096223 511096241
    0x807081f0918020a080304030b0a0204120602220915080109080a1d0a0e040b090105010308090f030f011b0f021b04091a0c180406050609010f110d030207171804 70
    0x2070400b0106100258075001c00182c05013202d40301840c3e4440c10750505081520001d003040801901c10002041081000f405458100d0360244000d41d90ba9600d8618002540c000b00c0b00b0413403118503d0002074402020f50220001702d202c456401211a5200d020b00d089484514000d088144c040005502c4144207c94008030160f441406044032400b50004c2440300040b50090403040024105100c01d0118900301c440e448100c0200030f114a6045650b02c0c481401004142e502400100c09003961360b0741c3c00d11010025840f400001c2041c0c07054014000c5400c500303032590501050144c194050342c1440400c0082070810403500d0005184040c0040c040100003090066986001310701c0451b81c0040c606d228a8054060311200c0c030303107070000c00b03100c104020074003000c49110b5441d08408002d66164103041e01c2092509080c929440704041400341d0f4000001400416280030b040c1c01c40504d90f41503406054a00d010300c91202c1c82e465854400f1300740e071050040101030801d000f0621211441c16421003510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 511098723 1250 511097473 511097501
    0x106060e030a0b0612010c1206090b032820150c06220614180d170402240a09060801080a0f08220306050a02090901170106150807081f09 60
    0x305e5030802c2035401c540a84c1d07484c2c4001055aa02420140c0d100e0140e200034250910081001c00a02400680c0e649080c81c551050080e04420036901085511524040c00d40c000e210b00303503c0e08817401041219107079003070218851a194544040c0c837030441d006036070480c0e0540d0010b0405481da441c865481c05030040c140c0094109100b140f000295403070207003030240070300c540070b82e40f1a091a203810144141580001c0b90301c3d40c4410f51201407035074000c1c4825414002c0f207440e04200d855600115002202c0c0e0000f80e00c0d0a110795541c40d106182890042201c0c0e40940d9030761040984640c022a01020284118100c0b41e12528241000c01d1109d40f414401a1103040100c0c546403101c90440c65440c48198210b1201e92402c800f0801c1c4105030003002e501000081c0d007141b418182d44c0008882d174006015601d040492039078a055941c034250f208001420380c80310600f0240300ca064005144600486696000034081d10100e0741c10224021000301c040d0004104c0d075922400d00c86a803004240b0341d400940 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 511099973 1250 511098723 511098739
    0xe072c060609060c06060a0603050c0d0b031603080d0b0402040b030106050904060302210f0304121e1e1406155d0309040b040902090901020405030106060e030a0b06 72
    0xb003a550348002000d52040c8400581500d26140d0100401050190310460a140c140b100300b0111b203101904891084600348800500d070201c07000802d00d01441500d03125520203812002005000002c4d01800c5a000428801c1c07201c1c0c485103080c80f084e0700a620454050f000140700503c00540148060044030340041c0000808580c7c9400048a8401201e9409405580852000c1c1d00120610020091101d0b10300258a800d00d420b10b1401241c1e40303d06e0140190200500341144940070001b034030349043d080801c1703050342d242044610002d0075505004070b0b074028000010480ea0171012642d9407180e500d01c4420001c04c4010000e10030752040c01c480d10391040c081000c0b03100c1a000740b0284682041d103c1c03011007010040445044540c22200309014042c0c1d5001401c02c44003400000c01c4410320030050394003061030304500b00450090090054000d40c402005030422054110560160040311001c8000b8040d00f940c8030304c07d0700c2c0204a03104c556011382003840c48602084500780110303007085002e02501 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 511101223 1250 511099973 511099987
    0x90115091d120a0f03060f0b13080d031a010f1d0a0b040801091101020f100f0605280b04030807020d080f070308011505031e07030e0a05010e072c0606 66
    0x203420000c41203140300a0030000b242d0f001006901901c0001c01c1c0c107490904000342814282c1c040d10404c01481800c5521100062103002c3d40c05050003c3c0017080f0303400450f101810440c40c050060407108540f0011824848415401580328014410b00160702d40c555800c0504141401d0074102c2105413401e81003020b0190010b442042c09004000400080c0d00010309108a80781c04541c0020300003000341103500c00c4484000000340403401c880d8034001c4031000039242c8034000401e07024111650140790700141d10840769a2080500c41d140010301e600c115001400394544000c68a035020364040984012014400040107040c4030107000b807050700070b54106040500c08081107103650b00c0681c04a0000c0c071028010040900451410340e0910b1450070228110728001c030400c4060311401440852000340d0744041510076000707600c640001d00c3c020f0701b030714501049400c06601800300e51701084424400d58800103942042c04480600b840e0b25800032201c0980d1201b204050b10350041d00e05030b84540100859 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 511102473 1250 511101223 511101281
    0x4020417060f0a020405210705120c03010f1505040b06130618060206010b0a0c0f050313030c0e09030a050a0302090618040f1a0130050f09011509 64
    0x28500d11021401070020380340582074080c02c11000350249082c140144002d1003d0390b600e010007403004845032800b52008040011007868104150700c402e0304048821801c002140e004501d141160100703800a20044141045400496180d00700f0408401c0050034140510b16254100400c00f060040c50f9608040b103039804c000708018550311000104546081d0a5100c0080350140b00023400d09001401140d07140000c1e501482c4900c00c980741c20084580081c00400840e800e07440001c94004046035280c89008801c2020080d46000682e1190710182c0009440c0066201c4144510580c0380514140601c654040e11180c0040462800785034080c4070420769520b404015011140110010008032029003017400304444010741080c5440341015015410500981c2c54140c0d03420b42072a01d141754101e144c0c6c0580c1c0102c040a8031200c00001d1200c142d0a40819402640c0141804485400142c5846000600725181d00300c0e80a0100002001000000050b60200440c081c80e440c000513040142c021ba = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 511103723 1250 511102473 511102499
    0x10e13020c0303011e0b0307141606050a0b09092e09060f0e0a03090e0c0702040504050a11100c030806011224050a0e040b0a140f06031c0518040204 65
    0x68801c0da038004401000344141c584040f54152041321704105205007010f0206915100042c01f01c1e00f405182c03021310085a040e50107c8109440b40800360151121928000024010581d04010028149640c4100602c2c0006020b8002c0010400600c2c8040004101031040d5140c00da0000d105c03e40a103c1c150082503c0c003407208a0f41c4103020000d00c40d003003140448c0031511040c90340e41d0982d105480c008002500400004180c07820b01041c01d03902d0303a88841c1d8441e2881031460080d0028240006d000803c1800100122414410310a201404400f413081c4006100c04052100001d9000701000c400b1a0158800030b40041d4185070010300c20104101c5e003802d03180c8a1002840820031150301d07850100700410100058941140d450000c0c2d403070004103401e10a00070300094102505480400c864070796540c080000d5800d07445222840746030145011140034811118540607008841703181b000701c018801ca81c00c444419440700c5082214404880626403409005160000d0b803c0002081c01124401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 511104973 1250 511103723 511103737
    0x1030f0213090c362301030b0301061e0806060301020702031504110d03050a031103070504170313080601150203030402010c0308090c03060a1e09020a03020d061b030b0910060806010e1302 82
    0x4003000013500403902c50340301282c0c3c0800059001480440000c1819000400f03c5450928011640284020019004012940c8090040c001050b0010041800040c0d070000700d0f000c410070703546140e4070b65041c1402d0388580b000096068101001400100c10590704036900140101c4651400d030340703c2c002040c00740510b40015004201c0200e84104803d61500515101c0c00a100c3c4981c254145141c0141c0180a68000c507540407141d9000650050406c1069401036510030f00f004a42d02d903107903116900c0e29028000c540000101781d1284402d80d00001c1140d00490341030395240e4050881b078608480e640805046c28109004500d03d030145587c003040100d00600e001c1800040683d00a02c0781803131072104490807600c1904041d038a9015980343c04000301107030b8065800550000e024501a4020604042c0e8601c0710841a071203060b01c203900da030004045107010344901c081c940f22250301d5402519540b003000005141100081c2181d44030b1000055901c401030070441104c112088028203030781085e8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 511106223 1250 511104973 511105037
    0x403060f05070e010f12020d0903050405012303181911040605090c072303040602030901090b191d030f0c091b03151302030907030201030f0213090c 65
    0x20048403441000388502600142142411501140e5580000c1c251052545540302400001e08104aa0352001e0301103c0e289020030710304000c08511868041c1407a003040c01582e0005d910301d174680800d409085c55500d8141c80e5101c0841c1181c1d13901040040326006045200c0f018080c19042c9151040c854140840c0f00c2d10411402003910111000c1c80100d8026038495441802a80140700040c0010412101e0084d00025051110b01841172100803090440910f40c4061000183c00155142c1c040064212a10243c1c0c801081c1c995415200341c07203025170200e43c640c2c0001501c01c1d80029000340100304841030500340001000300d080d40000c0c207200154510034120380100300094410702c1d1048001380d01c070700001c6000c48101218805c800c243c2c0030042030440e41250480d03405003183e40d080e01c1510310b420340003400c0d0343d2807422014840d11820707540f000700e000c01d040440100940c203d50007a110660f43c04c8940c0015540381810400c042c064202d84001440031fa507804200c05510300b100040004a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 511107473 1250 511106223 511106231
    0xd05070305090c010c020f1011060117010b0603011d0a1107200d0c140303070209011403010b24180d0804030b0a0b0d0212070803041203020c041107020d1502040306 72
    0x2c285950300786455000a00d0401000c8074007a8010b96584501000e01082541c1c0401c94280903942925942e00c100e04941d00b070f1040340000290030500d110890000c009075402445125407007414000540001e00800741c2c0d91500e0399401c0307003100040c03841d01d901400290300842c09581101d44c0140c19801038605603040c151301401007000785a461004240b241042e2a108445d508076219105110080c0c02051544540185411110755041042d05d14050f00107200c41c2103565202580d00d004004030745941d019508100003044035207000320400380001d456611006507205400050078003a8000b18918040c032030380c84012601c5858840d01e50300c1891240c2d80b4907070b5490035070400a54826004100340c4d02d039418209985203136101c078500f2013002c41e070641d1588840d40605107c6810b02602d40c0166003a0303c004100064003083c07042c1954601406902940c00702c0e0139007014401510f480c1c1130711910107041000386c103005040940308001c3c00d50103050120a02d10041200300107030713030042c0e0042d510b540d11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 511108723 1250 511107473 511107481
    0x1109040222080d0809070608130501060e0703092001021c02120c16090506030309060d140907140405010e13170d0c08060d03020d083c0f070518060d05070305 69
    0x80c0c40e0f15080750b045c00041c400145001e1000f046261300400078110300c00d0801d00042008000d401c4a8003512105c20000f04620308042c0040041082c014250b40640058508141c204216451510b00c4241a8081c10054000b14092071180c40d07151598000c42c45094141d46080108402074040c04c9030420140c01285075011032012400540d41004007802d1401c0d061012070390b00042285c04002c0d00713607280b0f03452f24680e90b0040001d14948105d0070ba5101c2075000c2000d603140c0070a02e0001e5504d002d40703a0841c400c011052104403042406a210b603482e0407804a240904260702c6908400e200d1034043d95071100d10084070b5550303003188403916089034441b01d01410841e00481002c1d03010000784d422412000450b2030080d9204440f406910a1005c86000728070325135070b0000103a00004c0c1031090011501c5407655030840c1552060926480d42041002184558901c0e10517140242125940c0e941028114101e10000d0742c061904164442c0c1d0800102003080002e006041c81269a614009040d1030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 511109973 1250 511108723 511108727
    0x130e300316230724051503060c070f06090c050a080c031009050606010f030b03030435070e070903060f0b0a0602070506040b0c0307020418060f1109040222080d 70
    0x110011030322040c0c1c6000d0b078000340c12442d00720550380c84641213580e0181c0440740400392000001c0c041c1c2c3d003601c0386091100300203408013088001c0304000c1081e0100d4515617903c1c10040c125000f10080148002480c408000c00b04030180c210071300582c05425101d80e041e6440c80000c8101000e0780c0120b60642100b00076001034134061120a150f035040000500000f0b2403a40c8980d1580030081506050000c40300420301150b10a40c440c447c4c0c0074001d01100e42e5607440c6c2d8814000b00f040040701000d40a14411070104000c50204207a005007030b014005c12036581800c10201b00218010a0b00007088518580000440c41900a4110072a45040001001a9030f03000b403050b2029140c110b80c06540c0011010055501d4a40444017180c0342c1c0601c1a444a82c5406028218407540c03401961017400c028150310a80ca5a10410725080e1080c9420810750035a408107105648100007540001101400040c0d5070f0708080d0018a85600a11220031140d0481c004c00c200d1032004c0d80010203980d01035040c1140c296 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 511111223 1250 511109973 511109987
    0x4060b2109070b040b0a031b051210080a1203180b190c050405040b0f03030703092606010e060d12020c030d09050f0616080a0806130e300316 62
    0x5007040548400c83c1040e005001c02e21843c0700d5600d007603d00207004803d0b90721a900c1829102181e10a0623001700462100803d2500442030b40e900e1103996402080c450144201d0035022105000094203680c045600da0104507010320300d40100f81600d4403140032440400b0440400c02e0b0344611944415420a580480301d12900300e01d403004028a00040c507201c25810030240c40458104442c041070045048010a810005a0407155014480800c000b01010742043c0d248040e11400c110302d00c1041e43c03801c02d5483c810050550b10740b00b500000014004610b9a040726507001f00e02401c0b08070425100c0c1d80c2d0980041071010102c0068102005048440c941031240e00400055841d01c64440360814000510310242c2c000c60620a440c009058280000080003001000341c02106258840800d54005001168101c9140b8072032600560304030403428692003901509410b260050800026240e81c8a4801081c1000000f080502f00000d40805410030300441c41034405144110343e10b480000054054 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 511112473 1250 511111223 511111231
    0xc070807050d0e09061f200102040603051609030f03030b09100e0a020405030619110a0206060301141509100f1805011a03040f06020f07031d031b04050604060b21 71
    0x40c81044007403099550f9901d4001c0d500f040041c1054081408101c400c1e41e8034014400340c0e0801400007c003007404410194050002c55895072000d08c1031380c0e00c60a40a840c080c0c4030307000d41c000c190f450740180b002c075000c000841c074946c2c860b007000140c0010002c0003424002d81100ea1400c10390799248184900241c0c000c20903080724900806500740350170280000c0e103c150040c0000486860002c9051000c21039030440c407458144030b5055a03880d15030690003500c42c00121429806903007450391002410300481940d42c0300e0784034880d0071001311006c0d00c104042c1d9176020f0000504000c8010380895540d140403480c0004004801d0304500000c4450038550a1300ea05910698072502c4000340d41600780b0340e04003240c1e8055841050001d001c24146030040081c012000170300302c50800812002c0c10150004404405059001c85022202408000f01507071403180d260041501c100304140c0c2490784c20a50485500030744001e04c046546074880740c0c1020941c01881d2008000c0d0004001440c015018800355070700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 511113723 1250 511112473 511112479
    0x141308010b03010f020f070201230c07030c06080f010b0d09050706051c020f0301030206030c0d110d0518030417100f090b010815040b040204150b2a0d080c070807050d0e 74
    0x600281121406c0180240d6401030706128520402d000340e6031401041c903241e0403000520303940307a2a817825013136a90300c0503000c00c0300c0c14800d6400209429004038802c030307c908208001400305a0030302d0742c1070b2403d0300900b50118141e038454441000080c014418940a8002c6680702500c071141a419420503807903541d200d01605104106c0f07403814101c10f2040360705494068503869501d0310307014210043c13480b030310340700501c0a840d15103e1001a20103000034401100c40c50b4003440b00c1c1d11003a9800410781c410321200442d0341d03c02c2100300901c95803001c858032010990f82c260351898046140a106445905405152603076540402c44100006646a0fa01400a8900601100c0800103180ca0a804d000d4070180c0801c1e000c074000f600f10742e5a5080100d05506051b11909041c2d92160710681030b4001640e11101026143c0c214409190002c4008002a4420b130007807070301310143d420644075100041c0484c00c040303030100300c11008910b5100c020044184103100511f40c0e41c48103000100303000061106144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 511114973 1250 511113723 511113727
    0xd03031a010c0803060405060d05031204021503101e0b18031e0706032a020c030f0a080910180b3034030e06060906060307141308010b03010f02 63
    0x10403d1036055980c0100c0079100000e00351104c1d80040c00074140341100512500c00080c04a80c0f0903140c0040c1da00440c0309490300b4440400403490069180001c42c2c001d040700ba2100300411201406400810000c25041d4200440c152101c4561006500091480a0991580c1c454540509040010540100e00d23101c1e980800c00031861140d07150b40c200c0c0725140070580c0394600408481010103050404001c261442c1448103c40c4c000651038020481200b4481d0180c440891403502e40402c08030105a806500a4078121440003040302028241c1d0651040100715451580704614041d06030300a407031001da006440300441c11602d45400b502c03050600c10800b070750501180b0200c4400d82e050700300e512003001c2c00740100703c0b05103441c0c90920385030002d045a05000d82048856003542c0104106040c0006443c1280d41e004203210300d070101610001d030045420000220070b144a0481c144201701c003a00c0071460180d000344000d502d01d641e6000840165510741c1c0701300d03661400740705640300c4800465044d8 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 511116223 1250 511114973 511114997
    0x70b0103210f1202120f07030b09130305030c120c070c0801140426040611061815090c0306040305030901200912030f030406060513050c07060c05090d03031a01 70
    0x40c0001c682c1000c98007031060103000005080c0b5503405485118090b0000700c011031400e25000d22a401041d00c407a070100385007612408c140d00f041c0003c0391085400f102982140182070794216501d5000411500a9100c00d0040c6590260000c40c903601500724550b0481d01c4903640c0c03c000500f182180d0280c040c0d40e03d400e640581462100700a1940150444001c54400b1000003a400e100d01c01980c207502a0a070014004c11419001100c00b04066590340459100f5594115210641400e203040007406030b00030096507211080d0060a90b81c001c4115007500d49290000d000b0902c1c046081e5070840c0818004010030140507030912885034542c103c09644000f8a29030302c1140c00c1c03881a9004640203400422480300c007502d0400c02c031a05806190010b6503289003e050000080c1307500d0040c07034411800706030f000c60b01400c03601669028100000b40189004120380e540c900802201441800340700e130a1181c64510354510000c4071417a800b0b9140810341400280080b41a21079540500e4180000010f4007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 511117473 1250 511116223 511116227
    0x1603050903100507080c21101707030506010533072018070e0d110306010501140f0315031b0909030403051506031606030c080106030504021806060c0102070b010321 72
    0x3560405044061981c0d150087d2503420078600c283d180c00340c80103801201744220300e602605d017642100e445119200c41984017030855502c070301e110312025046c2d600150062286160052030707803e032128500d1304178282c581da04c20180d019070f2800c2e00c601605030000c1240c60500c400311940100c41c0c1901400e221b141030000c000140043c4540740c06111841c0d01800085207107010b078048100b0b42d00014035480145030945440c5200340c9844c80c3c107074041c0c0100400006e280d40104508012032540d5520306041001c5905211441d42004040c454100210b02148409031400c1c80348144c0300c9401035100c2e18400b81042400207036040a032400f0050752003040104040348000c151903004005410401c2e0258407440b000a207400104a485080300800c0c0400081440c1c049e03001c0c1880d40c0701070f110042c55a0fa40c102c1038044840440d00030b5003014030012041160401400e459500c400c000708528140906050700c0ca0898100840455003c0c15800040c0140f048411960307001c00380d050441c50032400076240c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 511118723 1250 511117473 511117487
    0x901081903200a120e10030f0626060c0a1202030a061a031e150d03031113050906030316032001090303020901030b0d0507050d081603050903100507 65
    0x140360384002449058004152240c1d100300b0362180010a42414034009050742500e9000a05007110001901110746000f01e008821590307415500a200a41e4042c401d20250090220107884e042201c2c3d03120800301d0641c40076801c08a10300c1b1001103088419135000202803030b00e140940140008001402145030190744034422700e0b1070740e03030350900543c9903120440720328003401c0a50490704200d004001064102d10b8500041c1d44124041c0b00c05440900760050140600e901c145c401e0040c02e10036180030030300b80c1002c1601a6038a4400d00d00010401d44550008a05410647d04c00e4281c0000c0c9004111601d05880f1191300310074110069464600c502c442c004001f40464001814484404510310600380ca40e42d03034103d08140c17a002400581ea40e0b00c5e00600940c001654103010900d015084c1000b4103054242d8407a5076031001c010000fa41c10310040140c411240d03582142c9121040019201c00c048441180b0080c2d4800d4032040c2e100c03403001b010036042010840c04040503d14003401c001c111030740644 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 511119973 1250 511118723 511118743
    0x402010e1206190f1d070608040b0637090b060313020d0f0813091a1005130314070305061b0403030e010c0807030f020f3408070b0a0e090108 62
    0x1ca03c00a5071084480406021101c0196a076181703800052515a0800703212040450359400544001c0c03926180207070743c1c020054401501440b60000010110b080040701d0b10300e07407140c0030321170400b0f002c0b15052032200c0030b03009142000b01c0144220070800a141703802a581d0641049400900354500901201041ba40e0102d003e44282010710421003031084202000e0707500398111600e80c0d580c009900b140c0c0400f02c90f51198101c0586801404560341414085241680c0c800070300b02d00008000b00c1089400c2d4210007840d039000310750380b0400000101a241207400d44401d4101401181d485e41c00c0085c282140141500c2003207501c01c0055010b229034030101c6007035907807500f00701d00074100070030040b115031615030001004154001070f11801d1507000408807030030311213550807505125001724146860304501d03290094841802c0b0f803848150204410407400300e943c409a05860350f0354420100b803034485103a20603510000300040c0404010380c4140319548070303034043c1c4042c0c4040d450302c0c0086540703550080e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 511121223 1250 511119973 511119991
    0x706020634050903102004030302060a050603011d1c051c02160c031110021b2101051807150503070c061103010603270f0312060308120402010e1206 65
    0x40c1d00d010426005070252032501501a084030041c0b1403010701040240045404c5500084039218a0748000490710203c40650740e15601400290b1100d500746d0024203805044e940c0e25540329001a10413030240c00f801c00341c00c00c241c00200401d08181c00103008280340c1c03065040800c02d00700540e440d00035898091079031780e16030303030100584da9510950000145410031170000d1001c0240c6000100b0320620181c800074000c01107940d1a00e0550004003a81c5d90a61407104400c88102101060883e02c0c002848203010303454071150085051151103281e0840c0c0080392118070400015031401c1c04071030b00300441c0340985041294803074004001c15000e443c50000410140030132600407000810044d0503042242113000300038100e9201e5841d6400030b0082e00844000440340d450f1100e1102c1486030400a03101c03002d810600e40c45208000b40c6045074001c4480c0e0140290949810000000038544001012401c074013128182d4181040d1000400c189030440410b0300c1103800121140b542c02c40410350075004007140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 511122473 1250 511121223 511121311
    0x40803060111030c0a111002011e0914100c170609041212110a021501030c03060e0f0321010e100501050915070506180a030806090402041b0207060206 66
    0x80081d80d89140b01d1801c20940d1390040d4020030040240c0405c00d420a828103c95a01103403256540c101d088819000c103502d05081c00c1a420810f440940e0b2103121868002c003104000d903040052050b280c1a26140c81c1c0107030b10769941c0c12038007056111282c645c0b9a103155918594034103050300040c00352640600050880c14040d000ea200c4a0700690034010035284005050040450b5011943c602d40c00c10007400c0e025004e00c0401c80d031602c5070303041480c0c180d0344d000c64800c3d00a8255240c0000401c0707040100c4020348608103035020029030406c083c00703140070161442e0a1201c0c046010700101c41041e846406461249001d0200844045010350203444081c41c1054440c941d0000052400e0340244030b80c0038000d00042d00c4024428085021845403401c881c080000c1045507444941d2035070395940140004001c03402040040c580f090300f080e001400100040350365841000010310003d03c000c04c10300964403007241044101e805000b042d50000d4250086510b0103007800060f280e00001c9031341c8a4015040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 511123723 1250 511122473 511122497
    0x1f06020a0b060406030f0b04050607050a09030b0403030b091510140910180303090509101802030a060e0a14150f010e0d0507151805130b040b12011a090408030601 71
    0x1030f07507000c0c2c40250740103001d642c200011801c2201d41e0060035603068410340584400a1032003401f940c2190000300da5544c1c2c070f242043c916150076140c204040e10032400c06481b80c1d0084d013540d940001f05c0b40289000b1080180c400050380c200161548151003480920060103c40b2512441c80c1c4244c94407100e0a5514a0400c15400c50454030510892580317600d031000c0400101c2032503402154030041e14029141b80049803075035212032503000c4c00d0f0710038901c01000e0040301402c1940c150700038507000880100e0110707407981c83d400c11310080e01044981030f044507901c5001c0074110900280032901b00f124130f00f400380d6448555004c2a1800e1404048078103204200c80c40445a40b91664400d072103039000340581c1e103100e4680c0041300521881c4164a40050740306509000c0052000800d2021540018004050140115603101c00780c8586040a82c0c080c0c3c0d80d0f106050380b501e408010b1824070980350000210b1201c0c1002d0301807181c0381200c406004885031400c100015943e5000c43ea0404401d00300314802c2d50b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 511124973 1250 511123723 511123729
    0xb0a0b1c06031a060a03150b0306010b03010e04140703050d030504031d13020f07140d0206090d0f120f140618010b030a02160c08030904140f0610180b031f06020a0b06 73
    0x4146e4001001c1c030340103440a1441c41403950020112038821401d403541640e0f01c506681c441e001c01c0c024400074040d00e0300400c001994494424000b044401e042d514002d990307440c2d5906018210a008011a03160420442019403210300401d031800c01803179140030b101c1c0c8136001c00c81c00000710010005482d400220000e408d420401590302080d1b015465001100070003e4a5407100d007104141e8000d071082a01050500f4404107207070925003225134600b02c448203062011210385c00100301d000b84041e40d40300c090348601864050341c0c04d1100229200000740c1007243c10b03c1150058280d480790040107040c010700800d4848021203030400c1c0c0f12540541c03a600e0024242411210413035004040c2c10204400141264010025020103001101c0c104a24107040385801500102142d14940100003003000071102d00c1c020204081c41e046c00e140008071a039030b14880d03402c02e000c2070b0407107642d514011042101c08071000c03002c00c81d894500742e01100c0b806d1404401039616101c010006202d50402d00005d9aa03071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 511126223 1250 511124973 511124989
    0xc18290f1c1203141504091a07090806060f0105181c050c04110304030c0f0311070b040320030a060b1503041202070608060d03080a0b0a0b1c06031a06 66
    0x55201d0030000c600118034a454180340c80c5000307080000c2400c040e007044180e210084407901c1200008140005400f28808100081c120144101d41164030084c0350306612020f00000740c450261500da0009250414140c0347c600a00140038902c25200e000328628a03980c000241c81d0b420301f09000d0034501c03a00e103200055042c2d60760b0143d450038541c0c1807500d106001c0009940c9015039020b80d4200002c03460001e54480e107110440d809404140c03c88103000014512080c0e4000b81400781c90411620320211030200d0412200e907010b45280b82000c20103006200c9900d84001002030945c6090310140782c2038011907191001030101504035581c440781a010390f200d000c0b000300882d1017002c40316030368503107803901c40765031080b20985e98018454180b020030194000d402c22070142e007008000480380f440942d03040366614401048401e4094039456241070940b113200b02040a010113100d500e0300d4000f2284001010a07580740340070030040c01d03c102000032920003100c40d0400e80d0806005440350744c0c0d031004a45d8070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 511127473 1250 511126223 511126249
    0xf040b0c0a060908040e0f0c040302120a0507091406240d060e34120c030f05010b0712030c12020706090516051e03060c07050a0c18290f 60
    0x183c1040075060400c08194010401c2d24039048034400c458175111580790141008550404807010100014005854001c001c45814070000080b20003510061b42d480f410142c042c0d0003050314a450350798603400c5c070811060503584003100703031514606034110640c0e046410090700005110600d000450100c0b000e46500404064401c1e004100b440e401d103140100078010412080e22030381c01c0c160301c4d04003001110354403907503101507150b031901c91401500381e1600040c0200b0b0f40760001c0c1541e501c1c0010107041640509802440307090b8050303403228460709082d03200840c044140d4041600c2e02082c50203d50708028154031403a81d9001c0180c80d102c42d8a8590001c040c050b13409005441351135184046d030b5541404030b070144d41c4140d4098000b04003484500da000000c056602e54036402c0b020002d00304c103040401800c1c685000d202255400070b20364442c00c100340d0446e00501d02d001c800c40c60038000112540240c08501d0020a10b0040d031405520180610034001d80d80c1502c0744610300c450030980e0355250440542 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 511128723 1250 511127473 511127483
    0x60902060714030a1412071409041802010e090103201305090607030c03060501050405120a021f1803020d020907090b1602100207050105030a0f0603141005010b0f040b0c0a 75
    0x845080c0d80c03100343d07403500000741280000d120452a02c2c030145013142903130301c0004007a142d02d905489034032080c0c0b5000c2c5400581d164403a01407103024050383e118003031100e0b49d00301c82d002000030b0710031400010842601c04c0081401800194010000520f00d251380803002510b890700004c0d5101d0810001d803c116640c0202c0030f0345420201486a2800c0c04240103009040b20f0301c04004900b0404007c1d01941c00510407640804c9083c441041a400d000403002c50701c02e13200c01503948440c444d0f0300050310090445500e10200000721508041e80d03801c070340b200e0710011050305007441e128a03690018912402c20080203000b1500c0c040412407241c05401c01c500175081c000c0c8640d4442d0a042800100011040c900360300c41c40d81e402c9041b540c1c80c0040342c02802d541c01a5180c626655903201203501410303070000300c501e0640d03a0392000030115191408004480c0303a50070181c400c0d012003040c4482a80c070306800001303100800300941c00e0032981d89800c0390100c0d04031880c0c203503c91600c2c809082c10043c441c0b8000e0a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 511129973 1250 511128723 511128743
    0xe1903020c10031a0a151409030d02061e010e15010e03010c021005010e060901210b010303112109190e01031a01060509010509130b21010e0c0d0609020607 68
    0xb48450f01500115030141c2074244186400107441d08005515100d4821302d80010b102d000c0c00102c051080e42a40040c40004514524200f1a8004245849105d55428005030000410300150010307100c1c14001004d05440c2400c165410440fa5842000001d8203181030742d66142c240110590280b0b20344480c03003030001d008100000c07840c1d001944138510b034464500527038602000880d036a0301801e4507900601015000815982c208240302041c4003078800012002ea10313000e0309200049061203258040c520a80e40c110380702101c0e544079454560705042128900718900305082c40c04403814156100100211a84404074024803805090b20029800c0040105060800481071001a8010f0f01c51121404d0354407a841ea07a401c0d080320240140c100650000350100300441140c50221000c0552116520740014101c99820000710100d031300e440362480c00e12a04e03401888028081c8154144c460002c40540080e00440340000d100280c05800140469940d041500542d11600c2c240e5554a6012003160 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 511131223 1250 511129973 511129999
    0xd0b0d0308060f0108040f030f020a3017061c0f0f021906080103060507110a0c0f060c03050f070303020c061e070903030c26121006030e1903020c 64
    0x4081000c200d0b000c0e406014100c034050712a520513170099100300c1c2c1010403050361342215502100c119504000c03c00851059440f48408503491000414a084403100710a020012041c5040c40c044080c444982c144440d40e0000c4004485e0102e43d181e22800440380c09503046c5004031000c482144488000d03024020700d48902081056401000e410f80307000311070104105940013514140c1407400e010303040000c1c1284004000040c040d03040190001580d040406e0101c1c1501c14641c508203904100740c4410200071000c100d05909100c116003d0607aa01d044003001429481c05081ea00c2407e0700c007814a0030004000050610030f40c15a206011440155249030034101c0e07a01c1c3e040d10ba95900400240d5141002c03d0b101c9004045c5074088035410b8035203440540864407140e0701c14100800c03042841c10000940c03514468500000e00306100c0442c8030346000d040050f02c3c861940f41c15001003051515061040c200b884000030031a402c50a09900c00618a6443c9070803810700d240c41d040c007038101709040f030f1074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 511132473 1250 511131223 511131227
    0x327050703020a080a030c1e06230a0213180e03160512030420010905211c021906090602030c0d052419080601030b160306030c05060d0b0d03 62
    0x200d41102e0080720100c1e0035648031064103440b21107012005011075840b511040001d042c0d00b581000d6199510490f0720a15900d4503042c0555819258030500c1850b0810592140e140310f8405c40d1304480c88640450616000e48100d012001c094001d50340d4002c01d1804003805555a0381024025a002e181600c1d15000c0d10a0820300160611004403030a004260f10420b80594070760a5074419074000780316000c545020340c1c080146941521500c1d04200c07440801180a4036000c0b200c94071011600c3e585103000c5060810342d820004641a080c5100144d01504002181e00103000c040072180d0b40d0800c11300c0001480d1000080a5900000b00003030700200400000c06005005085081700580c0b0500840d5900341c441c2641c83c0528060b00104608040405114140b04200080b542d18a800440c0d41c1a1a03401c00e03441c221f402d90003214941300b07000400071140805405140f01c1c00300d44c101480051300b9a038a12403904070038051035018100101d000180820550428000b000020b050002605198200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 511133723 1250 511132473 511132483
    0x60803070c090c0f0e0609030f03130621111603090f0806041502030c0c0a060b2815030b0d03080609150607080d020c0607090513091101032705 63
    0x8240c403004000980056808201e0050710000115a81d400c0c0c03042c00c4c0c211040c1d40b012195030285030804400d010070401a1810801c1c000350040803802142c1b10700c0f291390207081d03a200039001700342044004140f10310301c00d021402d0380b00c0c001d2000d00042040c00201c80c241030340307000c4c0c2c04840c14203070700c203c10013428160845207020580b5079204052000e00e0301d8881c4543c0e10f080070349005040c6a00e4442c01c50017650a0380c051500101080b5020f031170507096000d0300c1c0c6000555070090710302c55500c100c82c0e41c081c0327001c4045407080b06001e9120895a4a00d45100b00080a98410b102d98070501c0c4015400c400e22aa100210041006045081c2c0e05451705000f03100c0c190440324203000710b003c1e6001c03444000c280e5018811020005001c80d250140130784c2c03040d606821145542c0142c613001e000c01c5080f9041401001d101e00d40315038541005900c1d000400024244100e007240c80c3c7d5140c0314619002c2100340b889034286150a0901040440100080c880c8000d404280340c0344c856401c031880020840d0100d0b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 511134973 1250 511133723 511133737
    0x602250c0e010e06060d0b01020712030504080705010e060711150a121a031209190e07260f060f0a09060609050f0f0d0c03020406060e030607090501080c0c0a0501060803 74
    0xa0740d03241ea070f82c84500740c0018541c10354415034803a500b40519580f148440d0020b01003800c0c10300c19900c086030f80d5281c12550051010044020030320100f014005010100001d000500d02441d03c02d480000081c00b09069105501d40a001d40d4141402d22507a0388a0000210303d81010020003a6140810a0020f00c00c40109409100b5141861f401103010302c1d0500040c00d402e90004e0150880c0c1c011085440340303c2c0c0c402110590850184082400704c1d40001078200020400c85070a260035180c0f90400801024030a911740c00030200703035511075032580c1566144130381c8500503052220f15912440005407900070a6420584d1181c044c4001280300c3c80c0300e07000f1004490407900d84800c0d041c0c42d40c042000c0554411005070b0851700c50500b2070028038041c000140c065026210166001352070b0340200d4245c03a000d410160205071080c07a000d519080403c58070742e001007240f4100032082e04140000741020710240c51f0141072a00400c81c000143d5091010600b00c65020000708011a6550139264032900111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 511136223 1250 511134973 511134989
    0x1b040608060117040507060c11090c0712020303010f12060b030615030f07120303110d1103040b01060302160201050a0215010305010905060603030304050309010315031505040b0c040e040602250c 85
    0x141c0040414500383d69042e008a03841405800c020f400c1c0b03070702101c08a40582c426a00014803030800000d90300d80c240494007400d0304d00b40255880300f050600c02103140c0c0b5000064210340c020401001800d01000d170300c0041d00d5008540300c50800b000d060090240108005d4107605004030028000000c500400141c4100703010390035201d202039503100d80da490350f8452281600002070714401c50000791203a44031b903a00020220084c0d05100300d0ba06124100c640341900003d80a400000b8842881042d108140c0180154502989030965a65900c04400300c1c004000b8140b10000c10980e6100f40244280f0f40b402c4c40c140700840d00ca627902d04240f030207002508020b031524010900820310350b04011045074865034221004606d45488000118000c10324820101201d0110010201c00161810645e200d024030013100071030541028100f803442d2910147c0718682c8540100420002e10b804c20400c00d0b4003582009005890752000b10000c228148134203143c240800c1e40140f50002c01003d844100c080c5c43c160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 511137473 1250 511136223 511136237
    0x40e0f09010b040c02030316210c12090302030a0e0f06120a05090123070504092301050f150d020702190e0c09180405010e0303102408040b1b0406080601 67
    0x34014001281c0320108041c0c0180c00800000d034030301e0020b080c050388402c2303146002d00402e030b8040507691721072819540501c0700c25100c007981d40c08154444040c800c10707501c2520400200c00d00d070760b005c1d40d244141a1041d00f4842d03030030314443c0303180e44030803035141c101c40c020b0076055940001c42c0344002034070b6089171076501c1146845c002c10304d40d080520a001e01c0485140d04400141c02c1e040220242c614010a00820050204004208100d42d405006461840140b16482854103020000621030058110501841011440000c2030703507004085072031003110607507203540c500780f0a200801a2140c4407002c0d40001284082c1110300300e8000e0f108007142c1080340140002d4581c4220b0400501c1000b0181d58070802d50705008040419980d45590418841c2c4000111f240c1640c1007503080d034000b2a404180600c10400130099001d1712640345510381c0600c0e40c003c0700c0e1811803202509001015101420500b000000100e00000c1c4181304003400c03445200c91600d80d40c2e1004000d1600808560ba540043d0312 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 511138723 1250 511137473 511137491
    0x2209050711071401080621030a080708160206150a08070305030909130215030702250602121201140114030406020304031b02031209060409060f03062a14040e0f0901 72
    0x840c0d443c4002c0b20507994504079803190001c000606007425a917441d20700440102c400c1c490030810080032410300948681c1190b00e00360034040d040e544002c0c20004103000800980b5002d541c00720f5803641c0031030340400c00c1e404241c4690103e0035645190300b0a44241c0324285010003800341c0000a8020740704211941ea80e26510140350789100019150020b41003010b00d02150b00141151003c1c60340401d2500c1180d8049802811141107012901040f90201007107030360030b0065580c14080c040c01c03611038031038030380c50440d1445030b4022032070051040c0c800041003041c04110582c41003600000d04441000d11580340d08050038044003c0d0f0007601c0c21408200c081e400c100b9005114051200740c01d8004020340305440b803c12500b0a641c1c071055499603c903e00300004030300d4011620500003c0c0200c40150700e9281d09514103202211060410704102682c0e440500003218013205540240307400c1c52401ea01151554583c08103940941c0d0002c0c0c221942840800c05010aa51070b2103105080c2c210082c080003003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 511139973 1250 511138723 511138739
    0xa0b010b1c0504170d1d011107171201030501050a23070c14011109030f161502070906060c0201030f1503020d0c050d1401050f0606220905071107 64
    0x4102401484965641c00e111010003129a20180e4454081d42580741000110410440b29601101c01d045600341d5a8841c1c10111003041d660b15072015514000700100f0b1410580e00141e0b001304d0f100100324034091040303004011414800e48401c0032200803581c0055031245131190290108841241c0b800c1d20b000007c81002c0c0301d0410b41c1c0c48086500072441d02a484511040f90348007150001564401036907200e03065540800d01c102900d024001541c107440c2c1940104050a00d00c80d0290051181c0c0440308000d58100420805001c990505c070036007400e0a03080038160705082495001d101d90a151040c0000c0c816001406059110f200360b038100000d085031502581229011080050100c1c81550b042c001420a80911602e03940640c0c102400169200c0011303a4003d07410000f1503545480c82c0150001d4002401407a4000d513028030200c180c0d1400320082415800398075001040002c1624000060400c20b840980c0a000c41e20f90a000034540b580010703004a980c281490303824803801c0c1c00052210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 511141223 1250 511139973 511139977
    0xf0306090d032d0216170a030f060e0f0a0e0a060b09071403070309030e03010c020a1e0206090f060904150f0902040b0414150304230c1f031d0a0b010b 66
    0x129507200f0005000c912424120080d00014a0440340003400405000450b500c01220b41d00c1c1410f540020350780d4460303140000e05640086040050301810200309002d04075412001e02d43c00440c02ca01441c240d070f100403040000d020303104108891800750030500824450030386c20003106484150389401003600c6030749048910081c00f0516440540c81400410645071280e0001d02e01c0501a1804985d1000b0318030020742140c1c544040407004d070b40908a0082040003070744a840c101c034190100c500014000d034021422911895807180e10488070194180a00d036210400c0e16030012001e4010010260340d03210b00382440340d42d4003030340301240012540000c1060309070085400355401c0608142c01d040c070b40b05101079400750000807264040c2801601a042c19183c80c09548140c1c0203000d8001d500003070030500310401000910302080380c0c00501008402c1c0d128280604007801000b0b207011031034002000300310020700741002d807074082c1e0180340c009100b41800000d0702c810543c01034014017010390703940d01001d00318 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 511142473 1250 511141223 511141271
    0x70e04081207050c06041e080f04140607030503040209070306180c08220b040204060e15040b01090608040b09030405042301080114070c1104020304050f06010603020306060d09020f0306090d03 84
    0x2036100c43c00003000118100c466144025170300560382e5110300702350b881295503000100b140c1701d61400032508003c3c0817100903000912500548901e450240701743c4000300a0b2000802c040d000e5554500800d06180c4030f41e0041e0700070f0a01c80e11044800c0600003003080607200030b450040000c2c69140105589040c0a10000c0c2d900c04210403070712a0b600255580000c20100034000c0c1d90007661640c0c001003801c0b10301ca00d2489410303016040e01f08010418100004c45401e80c10f068100301006005100a541061010342c1060f002281420f86a0301c80c00003a01d144250b402031a089170500042091324204030242180b42c1030f0350303c0c264205a0300c0d07543d81822201140889031189122030041982c2da802091008801c50107800b40300810808180881c003642d2003030700c01b12650f91250041804c028002d00440b0b02401c22480e041d40703142804000a28a4003c0801080c078556031805a1400c541d1241815844920050300b6610f6070b1820b000040e40310502000d0702070119007000c0c1c410f411040c81400c20695 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 511143723 1250 511142473 511142497
    0xc060709080d0309050c060a0207170a1101110c0613030b060405270304050306010f05190e1603020d060909050f030405060315041d030d0e0106080c01030b03070e0408120705 76
    0x10b42422058101c010707008444003591140690f25611071503440d113400034041441c49400408446103045581121040c41c03443c14800d0341c1040041200080140d440c207160b6000034a4108503d07801301e580d445c01c04030600d030303466804940020580880321804090100f101d014030f080070070075030318031041c002907603801c54800c10403500c05181c0541d0128115004c204bc21181812203040546a0300807038a009001c1e0042d0405804040c400c02c01458620082c1b4044d1038031001c2180d03180d00c0d22840c02e195a0f4051703d51951901c10142d078030b5605211b0390549008030041081885116901c11518000b0030035a4800d5409001c1c1c28450528114000111400c84001030b000d80e196598204a0340b640c0301195541d81d80c07080d04e600d81054031102032411082c00581d010003860343c0d911192401400c8482400d0f0003403c5904010307003001181c1020800c44803d49007070134042a0400c5460010f41420201d03000740780703450008424401442000d2000c3d01c040101c83d05040040d4440070030599070380c010b0b40d240d080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 511144973 1250 511143723 511143733
    0x10905070504151205010b10031515020111040b03040215030903120a0902060c01270201120f0b060307050a0806011419020106170a05010c1b060507050409110c06070908 74
    0x1c1a03040a0b400b103e4011041c0d0114040751340c9602c12262a003a078041c4c103894aa444240722030081c41c0440c2600b4100c0d036581400c01201644074030072480f1541510411828205500410350540e000790040c0e81cbc20280490704039070390f5071103031484101a00251010b9010f14900050402d540b420b1100b160f01030380b1030000031814207008941144038040000c1015080c11703161014180161185030180201c10f04410011521703070180345690000b00c54000004901c140c0c10803460300942d80040d02004011002c0f41c0c089141e454181c1c106d00074001041c2665004500081004203503584000500741e840055a168111919544011203250b0314011500304030b46010400c105d1100b0f00045407403240034050001046440d50ba01100e62803404c00004850260480c0d501581041001e204496021106081110b803265580d48400700d4400301c080020042c5a0349c2c008103510a005000b95401406400307024040000042401d5100350400e8455441038400c800110b22064042d6041741c082d10141c0700106 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 511146223 1250 511144973 511144979
    0xf0a02070b010e1012030201020913150b0306030a0b040b07030c051e210a0207050f0111070201050714060414010b1e060901090306020301080f06090c030601060c02010e030a0b150301090507 83
    0xc100404007502c4107603034854926000171041124028803a250340aa000142c4641e021428000344c4601c08181031142071400c2c0c200c1c4a442d4250141400f51031038081e81d15103983e6101c2c0480d02e04148207a002d050580841e080004209030030301e242c0d204502980d01408200601c0707605881d507029100c1e020818552409102000d800744001903c01e80d18207003810741140d001c108541c8003120050700c964440c2900000c0990074420200040102c01350b03810001c0000380346003032200c010790140510007410000d0010380c000c18030000c030600441c1502c020781681c005c0c0c1482e1810206544040404401c207500f03000ca120304501d000c0c1c1c1c444c04070420a25401034040c03100030802890340d124035202414082100b0012000c280a0302c041e5010b0311416006198200007240101d1400e68010030042269010b0060350400d514082159811521075081240500543d84010707110180c140044981610504640700c0c2800300005150380180030f0141002211241c440a141c00c2c1e49608401801540c03021400b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 511147473 1250 511146223 511146239
    0x406120939060210060501020319030b18010905060f0d02150307050d050412080609150d02120109031e0512010b161e060b09040b1504020f0408060f0a02070b01 70
    0x441c00040c803840d15107440d8101601ca04008501c1504000d006070b0200203c070030444260f2182c3c44c09448240011400c1510384e00c8109100d002c0d034a078940406840301601e03a81e5441d5900c150500711240460b400007980c41d004410010311040f10828841d5125032540a010b04010a07100c009580180140d0301c0d5a40400707a01c1500c0d03001811080c00c003c01081004240d150900c41c40c1d020358400c06003032941c101c0890001f071900401402c030b079206912002c1480401c0b028a0800459100140c801510909042c00084c2d48895031480c50005542400c441c11704040d031254014245140c1d00300d003c60901402c6004907500c1c0191060352003098500d20040c844203100c00c0c090705600c80384440c42100d0030801d640c0c050703100d2100c1c02515400000414004104110f901410301042c00030740754645186099101c59600708c03405040354100001720324800c581503e90750100d905451403d400c055440369204a219900d90080703400038802d40040c0301142c2c16041758001c448446800c00550041c0d0b034203109031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 511148723 1250 511147473 511147523
    0x10b030610021603080c1006060504090b040209040204140a0f06050a080a0b0616031b031e021618050915010501141903020414030c010518040207061104061209 70
    0x703400194031800e9402040400400005400340d03201c0c40f0225110b0b00d160a0192400b80030111118000d82401c03018441e0550140070340b01190ba00d2080811100702900c0858000d129040611703800c513000042c04910600280c0104100c1003080d64008000ca940f9054400d1002c01c9000d4680000c001300410000f8610800f10103412440b038150000f0151044c0f400541c86501030b1420001d0348160100e15000e146d00070110f02013413606808a9240341e0305559004282c501d02500743c0024142c2a050004454820000b446404401c0c201b60b03810943c6603003440200c00700d0004014612400d1200140c1070007000f1501e8094006c0740040404940d0034100191030400b8803002d0345445a005000d03885900c44404038048030704850307440040c0c3d00e608007007840e00710748187d080507406a40240000b041e581d0740b00c02166020071405113025003d800d008001000f9205084000c0c060390304041010b511407107210300900444580782c4500c8a2400c040100d1000e5078281603000c1c003102c50551010040400e0010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 511149973 1250 511148723 511148749
    0x9050d1407031410050f071116090618020403020901050f03030d0c0905010306210602090111010e030301050118080c1021090c051806130b030a1203060e010b0306 71
    0x2103582180c0200c41407500c5219402964048904800c0d41c440720401e10001024152032207091240703240c41c04640c0108140905400e0820400c0e010b0750703400d20814000000012030881005c00d020303035941d40d0301002e807071540030300c08015040d0240c00c04a59294801c55040b00d90142800d01030780e1030701c030400034400041c0345034907010701041280500001e81c074402c0c0c40315122244c84002c001130800c0c000600300c909941210955a09407000344909080081c280641030340e20140250b40c455a410040ba0781c202c01c01d10010309076082c03000f80101440040091410780724280c0c1c07044281c000400070207140c009640318484850304120701c0300003241880b15100142c81c005091a1b51032247d504420034910b507084e00e0114459650703c403080c042012130250b2900030035040324400c0b00c17051980c0051080e48001b4012512a01d400800a2955180c0d034100c40d80000000b002c3d119602c016080c60b0403240c0542c801200041c1c605240450800b980c159680c0c16501c90100060641c1d40390343c284000d030b4031002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 511151079 1106 511149973 511149983
    0x507080a033c1a0a0f091a0d0803270604020111010506012f060718090204030c05091008010c0c02090f04020f061608040b0a0e0d0309050d 61
    0xa00c42c0d000040c44240005041e407525889035907999580c42d4541d007206030901c2c005500c001c409460302c2100c0030a6014894900781c91440e03464009808441540100f200000c0c0380423400b45809954040415280c2c2442c8402c07101c1f0080450140b100780d100c69500c0381c810003003196441000c040540408030024403103410030301d0029241e03100c1821220782c0c840c02d440c24107101c03080c0d0300080564030800f001910740904140754020450724140165017800424111300051080a0f44200c40440e90001c401040d294100410040614400703840445140118103011900140c00c3c030402c0d50481103905c4451401296205004000d08000c080a202d58034420401005d600c1309111039540e400e0031202103070b823100c280f002810b14211403c0c0103860910f0101e4080303140b001c00002050920700ca61039270303140907910070104250200444801030000d00e1611003004642441f080c0840d4883c424 = true := by decide +kernel

theorem cover : BRFrame.Cov 510971223 511151079 := by
  have h0 := BRFrame.cov_init 510971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 510971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 510971223 ≤ n) (h2 : n < 511151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
