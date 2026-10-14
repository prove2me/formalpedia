-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2649
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:11.025025+00:00
-- url     : https://prove2.me/submissions/8adad6e7-4ecf-46e7-bd93-cc47f53b700b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 476258992 ≤ n < 476438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 476260242 1250 476258992 476259001
    0x150a02120412110a0510091a03010e012108040611100605030c01030b1804030915110712030e030a030203090a0b09090402010309030504171e0613080c070e01030f0b 72
    0x2040948040b1864a0350002d05008503941d2800040110542c03550000d681a0011445540e20380e10a00311308500da4031030061030f161004001004501d4035221203080001c000502c15403030680320343e0703040d01c10660750031144003903103a09402c041041100140c1070540101e004640c43d50720050300c011252210342110ba08815054913001215914800c1c154075601443c1599581e500a070050900c41c20001c0015060345030300701600124103c02c032400c0b40000c4511800388503003041b01e8000010104a86004000a140c0c400340b5560f4100a000304440e1610700584007003050f10a150381582140050240c1380c4040d00c525010307650341c1080c0501d40c42001c40700000f0170a801c040c4140c0e8465107004000b0107550310385400540042481c442c3c260104007080202103180401c3c0f5240014000b240c50040034407009628403c01a80009024030409401600610418141d180703903211321240c1142c2815078500d149003142d46056061f50019010f11441c40c000410f0143d1401081c88550107119452591750301c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 476261492 1250 476260242 476260273
    0xf03120b060315090a11070807060501060809250b0d05010e060d030212180303040b2104030f21060905010906060c02010c030c020d080c01020d0f06051804050309150a02 74
    0x8562907101c0d8414642c14508626260000c0350300582000d400007459584220038074520346c000d8030148c0300840c00146040800c1010701c9403500402c0036152070319140c200782c4841502d8449924a10b49940390480300c152141c0200c00c001c80003030060035002c41d6030300c01603201c2c0c5010300000d210740d1070f50141960004429051a01055500b154944c0c003426511000310100704080c1c002e110039510745002d25a4031300c00382c2c400700010001f0340088010a91a08010752001043c074007038012014142c0c02000a1200203030b04a406001c1d00d00060400f10418080350290806040d071a0100c0e24030503003800c10000c0d2000700c80c0e0105058900c0040140000e5440b81c0043d1b41308500c988000340001d0314604a1008030f0712441041c15040e10007005c0846c61034544d00c0d0280590405401021581d40c00104180711500511032485004103417101403014600d4140061083c03a014680360b10820519800201009424401c5450845004280c4403204800401d00301d9141c201c140381a0161203180c02c070081c2109d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 476262742 1250 476261492 476261497
    0x15270c03060d0816020307030f151812030f0204170c15090108040804091401171507030b1c0804030b0703020423010203070605070503101d1807030f03120b06 69
    0x4405000d64402c0005540c4506144e84000b1442c243c40f4003900780100146c0e018020381000354040c2d01c09504140705420011a030b41d140008903101c96140040000390340000130088008550031404105202044010540103010840348110340c0c24400500440c0384081d030741e010140c25607040d0498011118102c00c0c0010802c250903a1007401a041c8182c071540d610130840c0551261054004500341940c030f002a2040d614030001607001d6981c090014050650402110144025400010170190b00300b1071940d124582c2c054120130070151038154807005601c407050100e00d0201204505c8050306428217144c404c41d040b0780001c80b50f84a4000c00304140034424000d44084d03c1c000c041c251f1300307545242c8000c4049083d0302600d90660000307114030342c08a01944980c82c452461521819503a14109641180f20081ea404c10a03402c0f080843d0310500030320301039003c0e0b48205882c42d1502c1000e41e50003e6860004581e20007030000c060303090300804140c0c0c40446195a1044207405000e40100c550030002c290 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 476263992 1250 476262742 476262751
    0xc150e0d080d052a0406270510170405060f06060a020d08130b09060907120503030f1305120918060d0201030c03020904020705010b0a0b0f0304080315270c03 69
    0x10841809402e05801240d07101941002009003400f0b800d90600e44c4032101d510301d6426840c20701501003802c010b41c039000101c4041104080f1203004900c030f40b80f81400b6100605c1d019030390241443e0020751207014020f05511030011911801400c861030540f51580d92018111103521190031100c0104060703042c0310040d0340410040340c0240202850810301156682002420001d00e001d001e015103010504180c1c4490080341c501e4080c026501d00844c241c0d00e0510300c1d5100c0d2103503020403080301d000b28030080241c0b500620b6890054406440306030f940389034540b240c00b010b00580150118180ca40103800700500c200711081d80c0d00f41c040d19400754400c803640c108807030540e000005440e0240042d886648404078106a070704005003410014000b0404036008440c04407626035540800c2e0a0a14009503210300400407014050700d4180300c4e001c1284580400790008140c24008808501031400e04068449101009014481b94614000c4440203148040e114004156100c101050500c42c030203049a105 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 476265242 1250 476263992 476264003
    0x61103090a0b09030d02030702010c020c12030a050d0608250b09060a0302031f0617010e0c16060209030a111009063606030c17040c03030c030302070c150e0d 69
    0x481102d450700080003100a10100c01c900040209100c01903a51001e03500803102e66000040c2c0309844400a854146491201d0384650706203907120800e964004103c50510303031180381c0341e0f49602d808440100a403030140c0212105005000c070390005840103400100340494990180440c4903554070707404203203100d0450540e0300b06004022080419000b9001541c1005011094100842080d203105184030080e0f040703000000c0c40c0b5440c009800d028442141d000d8841c1e41d003d03010f541044c5810f83c281d442061000c2c400d071006070600c8014040181d05580c0c0540c005020b079507500c6014601140c0c031541d004850307031051004640c0c5020381441411000c0a80340c0b262607020314400c00071250345043c2250540d05100015004040d2440708000ea1403e00610710341d00c0116003100c01600142c6145c1410b0401c405400042c810030000c03490040304403045070b4150030072402012182c14107c019125214018000c6564034000142048084ca030300c4c015071056640c1c1e122000f103008104213541400402c00307801d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 476266492 1250 476265242 476265253
    0x1d06160903030302030c07120504081225022e1103030702070302041e09061b1106060d081204050a060c0f0804020915031005071e080712021c05010306110309 69
    0x2400f9600954201903211902801d00b001980c2c2c82c000710801c0740281000600106080010500030054140c01101c00a040c1d418005441010a0751200f1044018030250009010301d040d522529020b80d8103580c0751080342c0200c942c2800c68007030744031950002c200182c5694260300fa80d11005c0141c07805402c060b80540b071024690307000c0001502c44054050142040074401600004241c4070300c520301442507401107443c0c00100944024000d07079a6903a0b084c080c24101002004002103401688054203c9844e0303140b840703506042406000320201542d0032041c2c0d20602c07080c46400a252a54144188000d1041c4012800100d13290403604401c4804543d121011a006142c042a01940070701c00d0000400d41204000000e171910b201c3d40c9032107041b9541d81041c00a29030f0300c503005a200000d4040e0b403140c1d0140e00f510051021000909403810400e4020105010030342c4c580441c2c813a2000d10320910201e02d01042c00100801080c4811144240340c80303840717221013050000350791003540c03603a01420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 476267742 1250 476266492 476266499
    0x2031b031305120c1e01020903030a080615071509061b05121015050f0705060c1206030607081812040803220312050a05040902030f06090f0c04090b12011d061609 71
    0x48800c0000c1d50b1041c03175540901034142241c03030030000750a0411090796210042e04014090000c3da40703805041c2010280c0c1080300201007484000307017000440b88214005a044c5482c18003600412f621800341c07250111000d003000c1200d034008040d104001485a6480b16601c1e03038540400300000318451081143d14644401103050301403805000d0003c6200f401900d441c1c59655000c3c1401e88c11910303040d048101154640c648240b01d0300c4582e02c01030640c01008a0b0428031000380641900070901da61502c440c00c440c008405c4180302c0007000140c400c0080d078030360361205a540d0f12034211a00300030350460804190384541c1c0030740b400c50301240d820035605034203128000e408a0301540400500e80c14040e00304400140310029100031403040c03002094014107424140b00b000300500000d0040e010000c0500180700da4200000700715002c80d4041e00000130054030b07510110b4a020f90703151585007607503c1c100c02e010007003502401c980b01342d0313000d102550744695170046e11002c8440032464010000c1c01010060 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 476268992 1250 476267742 476267773
    0x106080f070f210501060201050103050f0c0906040f02120412120b060f13081f050603010b1302391207080403171611011d1302031b031305120c 63
    0x2c18251540c2c2c80f1100b035684102101079807020303417090005030b5442c801041480b000b4008003440e42011800b0f0040c0a8440000074441b000250900c0d00c140c1c0d40342c035400c40340703c203ea0481b40341495042040b9818546400d1034007030454004c03059804580f40080c4030100012510030041d0000c001410030381025150140402160491080c064440c0385841c400b084042e42002522003c43d01810648090b1040ca040c000c103864015081c00d0181c0c0c14426032070255540c2d080c906990310911a001a190349041e0911480401e50030342c1920341c100c02e64401c070107ea5940500c0c2c0d00008500084684000034500080c0c0f0781d110319180604126024081030000a00c0040d210544810710b2044a00f41020208400005010302c4000ca072642c0d0303602c0080206517003002c00240710811054a0031000c015910214881d1413a03941c848581541c0000021502411080840c00e5851340d8110300b516854818410320301c3c03c8140901b0f0312548070b03242c001510400c03182d040300c01342007144001e00340a01c103100b02d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 476270242 1250 476268992 476269007
    0x12020309010b030625030621020a051003060f1a030f13240b030106060207030b060402070c0806100b09130e07030501020f04061805090f040309050603040b0106080f070f 74
    0x114070354032408444203d503802c00c8414020201402d54108000021075050712206205a8500030305041c0542004001d1410200308030314140c003c1c015200d08000c1c8001030800308650005507109000d0321a4010641d41540601c065400303e0301070401480d01ca000d08800504d4801d8100846c00081001030041d43d41c6070a200d4106154400403c1555003a541d00c90182501c15088078184003444803d84442c02c89000e03140c00340c00c050300200595810010020b440c0d91180c0030250084000700041070384c540f00d641c1250782c0d680d000fa00d06180c268803441110745841d000c0d03ca542000b62852008a0242c150300126101424000e0070400c0410260040801500081e44c005969010f0307050008040b420030700040042d40a4034070090b40e164101140507090700040e0700e142101811100060002c0c0d180c00c4086900404000d0020b02c65503070741e160803108058070340c0040b90440004014081040340381d15226040c1e42c0c454944e01d005541e42e00c498550030034100c0d0a000001e6180d0079018019028119 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 476271492 1250 476270242 476270251
    0x32a020105071b091b080f062101020d021309140402040c1b08031602060103080421172505070920030108070515070c0b030a02071202280201120203 65
    0xd000c0341c95144012035164100c0b0340c1c012410603440d883c9a130b111790303282c54565140409a0402580f81d0038518460941b80070002d016900404104892107030305100b200d022914080680001d554802c4045003400107908a880b0329807100e104448d0100300e58405008482649803171102c100703400e903070395003c0101611414003000c0501007806405091040e841c1004080c190103150301d41e507603080a00515a0728089109448215000708005200080d800c104139011100001406c40c001d802188003403d0011440400034011450f10868800341e9005001074600c00d4001ca621460311203000c4a40d010003010254028400d40002c1d500388856080f0b6813142001c0d601c21941c03000460103401c51485164401c1c2c01160741ca5201d000204220302e00780fa105030b80ba03040c1d40c2a880c14880a9580c15890000d81e00034060700107030100005d5042007941e819a21180d40010360400d5144401c00040e40314002c80c2c0420f12070652002c0310800c00c0031214180011039178182c0d07814020f04c050605242c0250005070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 476272742 1250 476271492 476271503
    0x7120902181003120302090904060b0414090d020115030302030d0e241005190608060f09070e09070f020307080f1210080c010c0f0b06012109032a02010507 68
    0x80307068441000034001a4402c98140d03080401090560030305600641c018455a000c06004004008458450404850b0041d501c070344081501c40311800010302420f8072003107100603080d520080020112001a51410b0744825030020405021030004900c80710405020260150344200040074050110b580b20b0142091200e09648284603805203240d0400c242100052500044409000704210880d011100410341206ca21a01c46684e21070600300c04002c0c8511001d22414a002507a19180c6080f820000a402040329410346480388014020768403c908680c05044c02c2c400040125000f1034081558620b01e0b001582049444e90303481c4800d600503242d00d40c01070401c2c801d4041c0300761174a0072580604008520101118181094185050f0041010504100d0b00720072490120f0a0010708803a5140c00c5224400d580e030300c0b41c005072988000a00c48103400c01c4c2090940c80807807000e030700c40c2107103034802c0c0e03620741c154a40110840440b040a544020340e0700e0501c40d10300c00543c0a40001c0c0400b61184 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 476273992 1250 476272742 476272759
    0x181202070b0f2b06030201022505091008011509180203120a02010906060b0c0d03060e0f0403031407030c09050306010803030c160c08030405040b060c07170c040e070e070807120902 79
    0x640031000740407007282c400d40b000c1c4d455980134403c40d81c041c08030002010002c1408249221440510300e55080540b0130f080c0684110b03000300d04200c40564062015014500080c480c3c41c88072024401003020341d204000c545460701012881044484002240c01e0790001c004203045200206402c00c6580507042c0b80c000d41d235958100000040090280038020302c0703040507041d02c2d8101351000380d04100540c0000790425280260a1004000780c6604541214000e540c03504250f032586410303001084040040010f500070b601c00c001c01d082e8160460481c8001d40d90303c04100396601d400307040c0c2e076101c28024001c1640040c40000c011201401c0035010310390b15104415003161454450a202c1500c64201204035000094280120b00309801081e0781c00e40160351b880e20b0302c03e511f00c44035101c03401c600500050a564060101c0804c40c1000700c81c1038208002c00230440d41c01882486503680e84c40d0320801da049003101380010381d01030084006901c910380980310201c90300103200c00a4010261070200301d9101045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 476275242 1250 476273992 476274037
    0x151602010e0d1b0b0f0709080723060d020c010c02010b03030c070e07050f0301030303060906150c020f060408070602060a0c180e0910060905091e070308070203030706181202070b0f 79
    0x441d484c850203104d14110010036400c1442009102509507042100300d42d0120600300854145c10b054402c0505a400a085902c410b0100142840c86090141c806076800450662074052042d8800c4a10a030181c00070068500b5102c10b00d030712030207403000d0100d042c0c010480c208442c0e241d141000d0b5002d641c51a0807442c007094030810820941081c0c1043d0006582d44809200315407183c400c8030301900c014101c5100303007013104c00000c18406103854001e00461000741084100e4860ba010b5030050302d80b0100f582c4001c3c0d194000250340311403c0310501003442c10840301d9a40140111980040e07c040d044813000f20b1424152804103080c00a440c03c85144a04080740e800f1808602c01ea070060551003101260b18104000107520300a4903071700c1c100700301e441d214504106000008211007200e0b80b206c1c40c1600c40c06680000390450041007000f820303c2d400d01d40c581c000d80704901d1807000702c14072402520b26a040050001c0342d8605060182038600d000410200094440710340191103043c04030300308000d201d50f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 476276492 1250 476275242 476275253
    0x305101e091b02010b0102030715020c0a17070b060a0308040510050d051e070201050907060309080403021e0a140d03080903070f030207090609050609070c080408151602010e0d1b 78
    0x1842e1400038401c10300307500d80301c48694203018a03040c0410901c000c500f00b480d261103600c02a240c07082600078469001440c011032010038002c1c0302c40b05c2d03003001d0411881c882d03800ca0840c0c560b02c811030440d8603c0054001608074940360b010b08050320303084035041d82800d0514080c008003049884803a07040c06400d1001e024040d00c0380c06064811f00c03028400c00040c0b68070400c00c2c1c0d04108098400005c0d6410101080540280006c42000f25141d602e07001c40c04880074140f00e4134034460381d00040e4100c001e110104010001c284070b50140c20ba410341d04884803982c0e992640003651201607126601400200d07801001ca03200c2c10080e50060515800d40345400626520034503030f05441c10046001d0b0300660300402410601c0c2c4101801400c0664007400703c0d14250307000a0490500500c0711040c841c0110010046c0034641056501070310100d411200c01c03e03c441000c5403d401e003101d0513040001200d070b65200d00e61040c014251180c1070300d8014050094003c800341da0040301c6084038071180d0b254059800c007180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 476277742 1250 476276492 476276501
    0xc08040e090a02121b041116080903060907150c14010213050405070c02150c1212010f0f0509180c0a09090515040c0306051b0c0115060305101e09 64
    0x1d04140007489070307120610611900c1d55050010041c0c0780c20034026180c0c1102c52640180108900721030008200682034840061401540c0002c4210f2074040340040401c1360b410f0080101c0d0000328102c0b406c13136a5000b042a612600d600030805009905100780951600450325286407a101d0040c812100b200d4900b03960072608505050b00c950310341e0040400803410b083c880c00e5005400703840d00f1544007003590080b43c61051401420a6a82d07000652020801014408140b40100240065546041d0080d41c03404000e820b005425154940305000901289071680c1001100e44c0038081003040c0d51001040f0601421108581509000d000c41e03000b00c40e0349050144000d08048100010040b000e0308055141803141072030001c28a42071810b010205440e030030b1784022207a0115000c0742c40d64402203c02c418203075002101081d02008204030354100c9064101c110340c0b051500c26072103426540d2004909660040d240744d0031020101c036051007681d0041081d8164034601142101d241c0c0ea50b40c81540403607 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 476278992 1250 476277742 476277751
    0xf0f0a080712050c0406050705120406080906070f0e130b04180b130b0103240513031805090703021305060a0918201809071e0516030c08040e 62
    0x54948080249442e000140040580ea10280402261a04510100c5180324030300401052010101d0000100003040010411048003011543d03122691654064800c40701603075201c44034000c0c1400101e009120305000402150190744a05000e6182428000f1003070054001c101c069480e01fa80351465112406458181c0c440d01c2c18049041c4054184403012007000703010142c55203160702000380480c00c01c200d2141541c1c0c110072500c0441c5c50760401ca80c030700012680442016802d082c20400100030007221004201c2c065220030322942c11514015000e00c85c0c0340146035210000c00042642d551080d809070004165400750120010f0301e450001d40c0315006140400001645003c0520031810b0981560031004011001407240040da41071115480c51048428842503002048030340112c640c4e505000c0754200003030070f5103601d4104420000e00311807511000420b0196015101c03031031940315008889182114454010407e0384641e0100d03200701b404201510000b0301130001007500f008800420303018 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 476280242 1250 476278992 476278997
    0x13020a030b0907050406030b1b0c07061e0201020a0f120e07090209010f0203030c07020d06090b070315080d0c021e060c0a0209070c0b06040b130e01090b011403120f0f0a 74
    0x50b25128040030b1902602c0d40003903000e1703420080300304009000040a47d81102641152a1035840070180c000d14034010302d01c2011652040c08000034440b07401100300c1c8081030a02c90107843d0303154000400d80c280e00c40d5004840004003101c3c0c2842d000361154002d00b00b0400381c0360000c00d0010301c03150b22600d004a540c22820000764005103082042da00b10140c002075003840d00145055250201c1c41c0b4610380900503010340990401000c540401200c1c1d8482c3d0441640242c10f81400d04007a1070060052403414020350600c11901d4022a41050000d8041c20420140da980d2600021a5081c400000c800d844902d0003042e02c21140a015902c00c0f0203071201c411200014540d079100c600400c481d1301401b510b50814007003600351070804101d413559510750004d820303503000c110066040d0211301d12440448100040b140791010880c030914064024003000c42c02a003403d038540e601c0301001545068110f00d5503130306602c11404070b000c100c0e203040038284034134000d00400d0825980b000100340942c41010302400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 476281492 1250 476280242 476280263
    0x411040c020c040e011b0903050607050c150103060f0e03090d080906040f0305030a2304050118080303010b0c070b0a050304021c05030d2a1b0203010f0603050102030610030c080f13020a03 82
    0x46540621030050008428030b00307c080b9034a1900c03416240d840242c5160108500011074003104403042105c040300b070788044541865076a482c280000100031240100d035059041c6402c85e841150000155a122a00100003000d4000135a0340c2014561249502d030b40c00c018288800900c031140d0781001d40003180203e01550751440b207994010011b00c4030b00141420040000c440051360100141524243d440a081c0000d00a1007804041015080c130b5000380542c1c0b0002001040c4170a50340090701e1031410680855101d5901c50a88500c14010400310f170300001c03c00d0000402500c0c2c910304490b145a54080c81d40b0700020a52100340c1507a03c0800354911b201d071601795400040301001c450305411103c0005101d2850815071008107045900f035188040358581440e00010b66500b903100000c40440044208030607640ca1610398040c0d0401c90b0801c1c480d20031b4010780c101840c00f90055401000703c564038520b1030341c1c9001c0b0705a5605000380111907800f1110710b1030030068656410940240d40030b55000d00b0b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 476282742 1250 476281492 476281511
    0xc030c080403030507120201051e07030207050d0306140d0203062802030a1401050d02031c020c130f0c170406020315190e13030503041401020c0304151202030411040c020c040e01 78
    0x6e032401d10181d04821607140c1301c20000300c81031000c00031001441d0700d210b102d1030751a0480300300d003c0e0051000c05001806034280111445405a00050407079201d12102d1303804c0440f036000c11900c500c900070f020750582c00030030010300c40e889804804e05c42c0110036461016800100d9242d50100e030000c807807450200c3c0c2d882068110110004094a00400080b2055100030503a540400e4603034071082d028680d900c0e8030030890321840c0c5c024041c043c108040130b083c2c0700d0414801c812030380c007030301d40781d40600501032034801e0600e051407050008a010b2a0290404801603c41c0c4d42d07070000940c401400390b90541103180100c512903450903010b03461329a95002c1e138044e0a042a0000c0160103010700518007005060007005c00084d000b409995009402c902d024000a149948540c0607100c0c00c103100f1344170701000078042541d402d044592210544190380b8508024101601e03030040784426903004d40303c90038149052000d440c3c143c1151900345094810b441021140c10302081c1a1108106c01c0b00c0c41c1d944840d81038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 476283992 1250 476282742 476282753
    0xa0203090109091107060b130c020a020a080115061101021e13060801061403150604030507090e060402211e0109030305160e0d031b0c0512120a0c030c080403030507 72
    0x4901400c603c60f010401c0a481c00c121802510400d20010300e55078482040b00d10550b21015080c0354210360080612880d02d80000084d151900110101d10600c20f51001184417201441742d005034521110070b20050b6410814203441100300d880507a8020341d0200010301c6001c4241d811426000c49618035542c03980006031103000e0314851600040c0030420b80030700412105070300402c600300180c110350f80c15980c0e03164508056401c010303041d49950003000c002000070411200240c05c01c112628410100020384450005503120582690040d6105806c01421030340881c0130400b00e000300200c0021154540411848241c0d030003405050403025941d960401d00c1816054054181d002401d441d155000690780369014010000c1c042d002c0740035000ca105440c04250140b600c45038008440031520211041a2800003000715140c0502c074000c850284060345000800101c0c2000c80c0704218045003840e441d0071044038400b40b1900241c04014042044c02d0104055030700030700240d07020780c1e141a6604070b00d0070b00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 476285242 1250 476283992 476284007
    0x712110103110d0902030307020306010303050703082a0c010b1005270d23060907030c120209010e0601020a06020d0609060f0f2c070206090d050f16030908030a02030901 74
    0x9050506041c0702803000103aa80c0022a0742d440000c9000299a00c180e0020034954024980300941602c1480004420305404c4405007000c60b219507615096665451080ca03941c0c1e15003242e22003059400c10409003811601406402800d0203078000007404c0d0000d000040b400c03c1e080610b600030450010300c1c80c0402200c100c0c0c4609029000508015101050010070010000c004014100408903010503083c0c103540e4039543e915012040480d400e070304008205684030083c510040320580354641e40000e030000e800140e403400540003444008213a180c01d0241c1c0070000000d000c82c0c1103000d0041084000368061002d000405032050f40041c59508045d140c0044074070030303002000b004041c05c20401c0104001c030749030702c291043e244e04400d400010101c00743d048212030003501c1c0103140c941c0800c03c000d0ba0001d5120311130750705402164414151b10a00b615a0701c5403075005072080c40300b000b45807000700000404038142c0d4400c1c81c000426554482c1400c0c190f40201c0902e4006810000d041c001035030380301c0c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 476286492 1250 476285242 476285273
    0x2030a03091806050f04021803030409062402060a0c03110a020703061d100209030c0402070b09060f06030c0f031c021501060e0901090c0c1b0e090304060912060e0712 73
    0x30b080112074100b60015042240031031003144901e800085490100c4c62100390080b48d400041d049a1300c440e2103a8401001d03003260b000701600500c030441c220640800c6144254a22245038010300311548540c00d41030042d1080105090505443d044038101a110010040c00c03048110750140032440e082d851b2130350540b08003007510014010203606201c01030317401282150b2032400c0306400598801688021034200302c9103031540c0e40d001c0d00c04101101440b0343e8400c0140b20f40c5583c1d05076005695580710f082d14440044e03601c1601544070a400340041e0420540c0c941a2031001070465109004040c403800c840100c0400001c010f80202c28807410000011a0881c007402003401c1c004a00340d030320004100d0300c070414860665040c0c2c4562110b12601d014441413415140c0042c54003206440383c0e900008410400d00c21210074500010000d10b000c0804001c0e2b81c165040f990f52005201e01e45505544030fa100060140c0c0e05d60384d00c401007003404408101d018001e1200d001c0e90070f0300407490f003000340040c961040d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 476287742 1250 476286492 476286539
    0x601080606010e09090c03010507030b040c020d080105190e070f110a120503070c2109060c050a060e030d020c0a020a060203130b0f0403150207060513030903021c02030a0309 76
    0xa0078008035a03005052920904815200d04525a4440ca40b892410b8408549070303400d94a000188007001341e03d6001119601e005507002c2c0a0407080a20883c1d43e582000c100c0303c0081c5214006206502d00b0500b0b40d200265400c001c40f1089856122500000c4025244440800ca81d03109044000d900103604161981284024041c00d511030b032503501d1410481071201c402c0240000010350030f503004035455468150008c1003d01c00b94031b0020500440340001024001144640c400040d80b01d01c5001032540e0542d126000d000003502640d14280a8039104c0138a90841c041403040310030048051020300030a07034504004003074050a6005102ca4144190004811034100b005405100070509104204684c4031002007507441c410115000541d000f03580008100341c2c44600c0c07102182c81c094000c0d103c0030f801000c080100342c44e9040190384c00220711a00902082030300e00100098900308580d100d444044502e048256503403030340000e04049207840214040f0b0700c102d00c00d11140c1c0b22941c440702e4614004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 476288992 1250 476287742 476287753
    0x15010e060612040303090c18060e0c1e03040804031b031709010c200618030106051002060c090d0b04030c14160e130503030f01140402120403050306030a02150a02060108 74
    0x4010b2200d5100410107014951294502c004010702c3d0f244c1800204800f8604007901e1059003841c0c005440507210340391040d4074500100b018000034104417007201800124900b5174100b003990086a5820060044c1c1348048240000000300d0081c0301b0a0100169849034000e5440c1185000800424900302e0304034889014000c0d0a0300b83d030800700003243e682d00036a40107184a6800055224000a000c40680000e00440c1d5009042e17041c0184101100b002c0380203005640d265810721090700c200b6210b000c01640060045406908084001c00000001a01d0300ca00322646444003c0c0000c03003520102d00046440203000c0c28000b000034401c50384007071782d005800c10304110071203001b201c100c3d03001c2d40300d400f4250808203011a00c02c0d02c001c1881784e4810103980e120b1070114849a07440200344619468200007504e90640d510303251086400100d0748440c00c109507141ca40b000c942c10b40001300115090700c5001400c8005d81c0e10700d211302418105000d000780e80d602e09610020f060010680c084002d50703001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 476290242 1250 476288992 476289007
    0xc07030512090a12020304030204140c2b1a0306150a090e010e06130c0806040308010b030405030903011a1302070c03020f06041208040302121501060e011115010e0606 73
    0xc00c4440c0403154100004894581030300b03041c01e0041c19003006040c3d00c00a503844032195008005070080307a008503400c02004c1002411110184801c8518400c101800c2001114250400f651107141e45080600700004c8800b8030f201c07904403810340d408003100c0508250050080d250800444da4401400316110703c103400b070f06005c00c0760014107008d04548551100c452240140d0254808021841020122425400c08641d0803003a02c2e6000816126400a008041945840010b009001c1d030b915540701201a80fa03c03082c80c2c0183c001410858050008000900701540c0034010300d0100c0750061942940f0384040c1d000c001c6c03406568003a05c0c241078014810b240129007484180c0d01140d8043c1c0345200c10309080000140e81703100b2a0828648441d40c24101c4060000140150041d2482505c6407040c100280007203654803d210b00c500c2510030b8000d001072200c1d5204403d4005074000604045003050002e0703010310b042080c1031061007109042c03000100281c01004000d55042101030320710900c0c0156 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 476291492 1250 476290242 476290247
    0xb06010e0a0e1f090f061d2a0d0c020d1d0409031e0201020a180e1602011d100b040204080d2304030f2307170c060c10050c0703 56
    0x200d100d01c0b00d001041030b0001e00031018101c1c80741c04a060140310001600d803240c03110402048110406400e0910705680459050341a41c00a0075081c17920441502954804040d4241030000604000c00d0b80e101d000c106030a240c294000d001c07085d0748004041101c118007a002851702074080c140108100c0e044070040300d03131844551a880c1c0080142c501241e0341e1210b0505440d44130f01840c040d500b012240c1c400850456065010b05540501d070b941d0314020300f000100c0070580c02442d000d00c200085054003c500d003000e21000488030544540004924007500d11050b0382c0040a1549180c826044100710324610442c901c907404c42d014080314118102401c02e0300c219940c468480c0c0c010144802200c4400900c41071a45440240511071044d944c1c4c3c40d00d0b45009210503261420440b0201e088003c4072109940c48005060810001401801d001346840b03410a904006c5000c0e0b1508d501a10000c0902503c4d0302c030003044540106001400040c0500c1590400c4071001014030042c404c0500a1900203039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 476292742 1250 476291492 476291509
    0x1b030509101b06020306120a030207030309090203060a050906030a150e06011a12040302100501091d07060e01120f0c080403021b06070303020c150103061d06010b0a030e0a05060108030301030b06010e 87
    0x1d07040383e0011303225a558400b142c40f0954401922082d8072841d02a9802c05030300080e8001070720b1107a80e451881d640d0354039501050b0300080ea00c0300d03840032807039405014030300f450314041782c0c400d10003002c40359044500d48034007115460040c2c144280c9a2a10846400c0507010416030780103103040c0c00702d80d03844004e4500880e07650103041c3c12a11034800c20004070b02414820800a10107594040d01006196500c0c1c03145401407200b5040009d8154206941802c0c0360b0340402ca242c1210039644034203030245820001100d90041351011031510307079900d026000300400f16104118842040341c641e201681424180a4a0302c0580c5220410380303100d0b10000101521101c05031400315905040140e25400c210030135a0516080200c0d8065450801000200f03200b0306401c07001c043c00c50758120b80740d00d551141382e117920703001c09002c1c65084140400420907120300ca9030050b002110100c05860b07280040c2e42d10380382000c00aa112005591001c8014424480101d00d4650446424244000c036420100302281514 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 476293992 1250 476292742 476292797
    0xa140f0301090b13020c010c0e040e0607120f0e0d110a0528050f01150602010c080c090a05060409050601120b0d0b2503021b03030601140702011b03050910 68
    0xd0388400d011212a104c0030700c421020060594203540b140d031800c10303103802400d0a400d96400200203a03c0b4103054107107442760044a600c403102500c3c0300e035949c00e800d40322030707404036021498203517a04600341141c1e403240701e110045540040034000d41121550028400a507101074480d581c4c1207500d0040014400103803400c00034a0001c1d8495208920981d001c10f01850048003070010301986010201034038040d8002d80d0700d0b98040c5c410000080d1140740403402c0b5581a0481c20100e0511404182d4080c22203020f02400c0b000284440c0e40d0350b480740041819a000b0707034407030700e0a0360320740b0141308096822083c12000c0042c144810007986050000050200c80e10510103070560115030007003a504102c6891140c0110810520a0032130040c4900040c001d40c00914484529511a94429103e00012044030b0146505a5a902408031241a410469806014100c1c184004074031000b2130743d442480040c0e82c85000b07031a010344441e0454140091504034020f0348041102d01c0c0c5800881045004911119 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 476295242 1250 476293992 476294009
    0xb03010e130c0602160e070e09060303090d0c0e161b060b120a1401020a022d0a0c170604021507030207080a140f070315050606120a020a140f0301 64
    0x581c40c0e00301c40e84481c685161029158949541010428a40000c4c1c49510b207500488000c402c02e903201c04101c20440141ca011001a00403801020030345001e80360303980c10840c01420b407031420f01d83d180002c01030188460221100c02020300c01704960708249015a03071000003060b0034004802c24034002407805a40022042058803041803210602215030303c000c0340c000c80030341092141681182c0e080ea481c9a045421514442c1088a00e8040311042c0242c403003c030420340040642102806810340b5080d4402e404140301074990410001da071004100f009810341c050a83c1041c03890620707404201d004030364030a440307595004005000c01600c0b4244941a0301e02c0c80caa501d40c8030141031078103e08001056100715007a1164003100e034144404408040262600407007200d0000d482d010821b5140e08003807001030501005400c0413030316552641c10a07030744410000e00f041e1912a11054240c0e00170b6041d00c0d010001603010984a441b150083c000c2582d010200344d542e03080c01020207059949100c140250080d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 476296492 1250 476295242 476295269
    0x204060e100e0d08090301180203120304021f0302030a181211010905010e162702070c050d0f0b070927020f22050f03060403080c13031103060f010b0301 67
    0x40a8410b0006001c90035005042501000345818192555044503d00034031035407920501030502444111050031507a405005009006034131442c15040c0d4000510690700101a07000500902d80d80b080c4052151003903840c0140c4a047c090407400403140c01082c440c0701c001f440400f040202d40c20405c0d81c1c20383c1405140c65103120030351821142c05400e00e0300e030082c903543c242014800b003070501046104c045418038900142c600c1d613a04550b040d60820098000000a41840003d01d1442d950014a50706001da00401011fa9544000c50800c0180d20f200f59010f1140400540c108805160f0340c903000011440d0802c1401d0070000c80c92620130454051040c07805e80114054007003085138050700c45900c580305441c4e4480460b2506540d13080c08140b0806032100040d00045003603e440c1500c00b2010708041c006080f50398a6a40c01e4900c0000500507510504040c4a81e4108602980083c40954400d9a00c07800e82c0c00c82c070040c03610300349014045080c0c20750050010300c681c003900c02c10791717044400a082028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 476297742 1250 476296492 476296519
    0x6221a0403020712050307020906030303220f02100f0f021c180801140a051e040602091906050d060e01150c06060e0f01140405040c050103110c060103120f02010204060e 74
    0xd242c403c080d0b011003401c404148080c000e0083c0403002c2c02505000b40e5000c7d04d50340e50310b01010b0f100d01c41120701e076110410b00c0349694001c0b9114040300103100d2040d1250550308416400160024030064108000220200502100e256204101a90f9000303207000402c065400e0a1070144480e2464074140308001c865640c402080040d400c03a08001c100c1a0020440d6080046006011a0088480805090500010680c03081343c5c10740d2170b800c40c0724848036a07002d511180d075044017070740c02465100e030710944d11040030226044146d07804000f013110340c40710b40e5200d0256403004156091503026881401034400104014540700c072000981c0442490250300e22501868810020f01543c0c1200d0004000e51040001c0300e04c5d20078040d81030344d51003100d900c0750040080c20042a244210b400400f14504c110040140d540650003a440100d03038580301d241021150550140703021803d0703000341d0760074081a05d01c43d81143c208401c0c0f46a2000e520007545410308141d80030b4201000440c100d402003141c50440f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 476298992 1250 476297742 476297747
    0x10b030a032709060605070c150e01080411040e01021809060a0510142b02070f08030a0e0f031803061311061b070302040b0a0812070f0b040506221a0403 67
    0x19030243c001c9050400c4140c1e141c020052003500480400c90b055061340101040d2007130105903d007699107803503481040c10034841004448103000600b007220b6901c0c0d910070740d004507a103a002d01801c2c500f03030800040e110601480c80204070810a40300078022907900050010548400c42210140c0380c05403003400040c042c0842c1102d1800355043c1201c401040440c0240e4548903e07500c0c18080c0c841e03014440d41c0c4040c1c45128408a201d034039401450a5a80d40120001415200c059a071040c1c4981c0002401503195001c3e908080d9030380100c09468100003000c01661442c0862192013503000d074002c100d14500b10511b03800b40d01808102178410310154080c071b4000d43d0b541003113509628a8240c811244891400c03401e960b9442030004030b2043d4102010f001c2d46042441845040f0380d408030041a07030092855100c84503500c0303d6402d03541d0400101d5030401041c0b41c245030078010341c418802880507180000341e0000040c41c0403020600c9015408200b40400c3c3c1c4900f078080035180c084581e6565859510f000d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 476300242 1250 476298992 476299067
    0x40506030402012607020114070f0e01020f0d080603160509180a210e100507060b2b030f0c1a090c0907030605030105090c03030a05130506030a0c02010b030a03 70
    0x119007504201c2c1c4058003665480130300b00f8041c000d681c0090000c030b036000c961480c25a03c119501c40c00211080003e1107214030403201d03000c02d0441030055a06000c241002c184c2800c1401021201003030744201889800d050400601c0c2da42116041a12011070800700000c00b80800038280c00d5403d84031510015404500f403010300c488690160140d0314102d2103500c903411240308115500007003600c15180d21310078145245072008803010f079550315203880c0e0750b0750710880100000402d50307421441c00c100f1441c00061070551610345030300706100da500d0b2155518004050381081d42400e0100440c2c0c03403a02000400d407540c038201c029208041a882c0f560351038400f910b40440340c04050341c001c0f084c42c00d020656405500203000c0e81c400f54000e11280d5183d81c0200c0d501c500001070543c041d8030801510b0000b51103030003d841805581628648120381c0c0b0000031720103400c29520070640a60307480024240c0b80d024480c40420315000e5029041d00d2419442c0a020301e072200d1802c58510070360040051400c1d100100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 476301492 1250 476300242 476300267
    0x5010605040c110c030d02100c020c130207140a0b0a0902010e041409011508031827150108150f0d060e010b091b0f0708091c020f041104050603040201 66
    0x3041000b01d61441000301030300c07040c80380340aa40c0038100c0541c0d03d0b41400b0030001ca800a16400074a40101d46080e5280100304480301c1d141140102288002143d8a00301605403c20f000ea101585440c40c50034908007052904c51020074503070107004500b00180d00540d100780d0000e0140b4000411600c02e0005031140b044580c802c0f640507103007260b554065509050702c240251410300c000c000001403410b801029408034000c48185600510010058400c6000c4040d441070025008408100502d014a0107018180003c034650b41c0d0001e08004000400c0f000c07980d103840e001d20b0b20a10a040481c040c0c40070044056282e4094100019040155142c81201104050303020324104401ca466140d0036008051003404184610f800c00c2c082150b0580160b6032040d02007910004ea880d00c500341d008440c0641c400030088566a00c1030026181e107646144456200e00000e050110000117544104000d9021000c03117244500e02d1300d50410101d4a203e070a66040d204d0544400e660f0303440d9400169144921500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 476302742 1250 476301492 476301499
    0x31b0212070f1e06050a06030206090402161505010303020c09011d0405160320060306010906030507020a08030108030a0210060b0f1c020c0307120504050d080702011e0c05150714030405010605 84
    0x2c074000c0f001c001440303024545601800040080c4c0c2c90304148102594103601c00a075000380103000c501928509a0300904480786170f80a00d000580540e0745d000f40040c00500500c01e20380c3d440c4010030906806101442010310220f510f44000e40c144050003854034100749040006020002c000b03410000300b001407280c4c0c0b1250280428402d642c91034880f131564880c951007141061030340c040e4115070824900b540d0007440161600d013080303400e01504500500d8000d00b07000442c4544500e92000c242114000c5018081e80e201840da2001150341c0686000c4000b01590206880c180003044256691425150070700140c116040d910907112904150305c5051004144020b840000d43e06140d510010050410358810040003080390880c140c01c9e0341d80d020f103110341c90700540280144000980948024207440e48141008001010303c1014a4141d04010740c440c00440d600c0000001405420030240035080e00340e0000024518000d28002c2c0705400451000300c0c103140100104003006829000103020f490b014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 476303992 1250 476302742 476302763
    0xb10081903090e06060f0309120a2c0a060e0f0a0f0303080709080601051203120103050105070909051603020c120d020909090a0f08090a03020a030803040201031b0212070f 75
    0xa06002000420350390880c0400c0c0b0150740000c103224091010b91288600030001820300c203440468484c42c1d80010000803080c0103900c403001d06d03200c0000c05001865480c1c1c1c0c030320080c00600e4070b802c00e001e180000000006c00c840d01030105285d80b1060408113a5940c1d01d454401505900c010413800c000c90314103d0f030710008644011410f608100401c0040307901a544000664441c9071058a61602c2c0b40076000c09901310000600c00c5003071001c8103142d800c400340c00326031070901c2a0019507442c1e042a0000c07a0b003a5114802d00491951000308000588103102042145050190700c00b105d0030b04c01d04d814014160042144003800c5c106000305810b982e0b4400d0325541c2c070181d41d2444030095022400c154451412400407032000c980c001140320846a05c09000b40210445448010140c2c0200c400941d1014070b8120110068640642030740045104840154032418548009001d0f1603610002c3c50b400003542c900280901c3c1d0000715101c0388000e1200700790381c802c1907050918030080701500103004842d29 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 476305242 1250 476303992 476304013
    0x10b0d020402212e08190f020414040c050402120402040b0307080a12030f02070503220801020a05030108100c02061501050403060e0f070503030405030c0913050d0c06051b070b1008 79
    0x122130054a007200380070100d0204181002d513164071651409115025404510200b07141201510340e24000341c01520b6801c400740e1180e00240544180b0200a00040c00840c2400200240b008046024010840e0250300746089228282c020440041c40a4459a15113007400c0e8113031014801ca8019004620980381c0c100c1c0e032030600f440d16200941a0800191034880002d071661464402e4a0320070740d202c000b40d031404680c4840c0c0194108154080640c442c1c0d24100050740300424030041001000688602da1690325007010941010240d55060340603c0c200408940e0305a80415100d030310034003006061044a500c80e00485450047d50002041c140c030708582880705800000c3c45814181c1c5600c2122841622801807580704e00461107440c0d01f50f8442090701c0c0a914181140320352103010780b8400440c028240e100e0624250518440c040400c030255845030034844580501503010900340382400c862001e9200340c0c00e883c401e1201c040c00303804503440407070000074581103e48010030050045516050a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 476306492 1250 476305242 476305261
    0x61104032306060d0206030a022206090e011208040308030c07060507031a032109131103040c09022107050d060303090504060e0105090c1c0f0203060f03010b0d02040221 74
    0x1881c007880500741c81900d00007080ea20345030b0035501a156018080c0d90941c0c0314400504041e42050104071880c4188800095142952062190040449907201c440851824000444402d810f07004241e0a00c840301c070400101d0747e2032041300d00302c0e540004ea6542d00c8c3d407807402c819502e004601000345a242400305000e00305605030800050788004215003200110080201036846070040d031500e800c14104521000c06660076005040b4591000d00110f01303000b64040b00e0340850703440c8203d1900b0707a4408401d0000b4080150030302005052815000c5252203120f9000490b00a1080e08102460300382800203080d040c8207005a800201c15418103012041d03d0b440c0c0030303015000c207000d8680510314006001580b491180720080c102d035805040400325448e4035111803c282d021030b11003031a00c82c0e25414030040c2840ca118001c241d00701950010b0b00d030b042c500100040284031580d0300e40719a05110310000142d81d00f204039108994104e8005960300d902109080400d040d8020201c0114420420400080b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 476307742 1250 476306492 476306543
    0x702060f03150901051002070e18030403061d0f030f031302060a0c020306092103070527030106060804050c010e040f0f0b0f03060c030f091002160c09020307050706110403 75
    0x11040f140410f89a80303034014040f8190071400d054005078031403c1c00b0807440e4200303040240c20542c1c141032079214942131090702c0d196900c10360003181c0d12641c40320700c20300e02243c0b81180e00002090702d0140641d0300542e0144c039603c2c0100000390411202c00404190710140c1c841600d28195401b40c101a00c2e140c200780c01921010150100360702074052078000a001d1280442e0700080c001d240c18000300815401e1000c4410358000074402010b1010803c091000b01c141100d0380d6000401541e80e46c410030000e2401d160079904035500c40000d1181c6034040c080040e0002c1140702c4801800e01e018085d001600001a010701400640207540500e400307160180e01280d40c2089601c400c096901c11141c80c4070409060360f88000300d13404140c00c002071000c2040d882002402c50b800148013003ca0380c02541940d0f500040360b00c0540c111450300608509642003041c020400001000d00d400111b00b94941210040c01c1485401c10062190b6504c003201c000d07041c0314205540140d5000000e2000258200301c4c00102c01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 476308992 1250 476307742 476307781
    0x6030c040903020c03011512150f15140118051903060516031107080702010809010e061005100914010e0103020c0d1827050406242603040501050702060f03 68
    0x30350907d03600c0c40d954642ca03050141280d9804201075600c0c0b01e00d0701d41900c42c40e26040c8100406494814103102084035000b10031084580c104030500c034601c2c00540082c0d0140540d00300e41842401c4070201c0440c81c14843d680b0448001340c0302d4035488510001c58118800d820340006201618080c1448142907202040680d000030076107041018590740441d20303419014042e001054004104140401540704000d9240c0048110b00045001c40b1700c1c466982c1007850031107540100d030400031001c2003285420b407008008120b8a040c940e6000741008441300d8014010b9064a040c0421034a45c5610307a440303a41202c00c1081c4100a442d481c003c1e0b807000038504040082600c0300c0080303088000c21090942100700c00100100b0310809104507149d00c00c08045d183c001c01c25103040d591411555488689030b150305d0000b1302610f200c1078100d420700714400500b030007818401a025400c10a118410f0100100301d41c00c0e0388007400c219489408900c0002c18034410b00208100400f00802405900114400c603107012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 476310242 1250 476308992 476308999
    0x1a280305030c0f03070822030b010303021b10020703031b21030c210f02120403020c01080a09080d0e070b0703031e05061c060e01020f0405040501080c01090e06030c040903020c 77
    0x568440f034842d80d5640107000c8081d202c42c070f08104c4040302c2401a01c40300c05044500e51609119030380c0e40c81d20306240d1400d038403c1c0d000d40c12049824100c0c00340e001001d041078808441c0b03140459003018000b552181940001400d0048051185549042c103c6008800c2c0754402d03100314004021038540760f9110091290100400c1c10124010105400b809038010303070406102c9070303111030b450350003909018202c40e2588016080d400c00c00c0c4038060170000662449140245c00031302035010300f64001482d01c4002030440c2981407500c6044000030f002c10003100c0803103d0022020131000c000c00e08203400c10f801a8071290180b04006044000c150b0103400040c54181d01c07c0c3c503032101c3e003044600710080d110101c17810390b885040c0c0150440c4182610702040403440c001d82002541202e0b20204608a07800b2540c0e51452150106081116140034054140501400d4010b00600311b030390000601300015030b0140659240c603400c0051420b440030400c4c1d0720304410041c0203000fa600142006519140e1802c1400e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 476311492 1250 476310242 476310253
    0x40f090615090e03161109040303140603060c0a0305090102190c0b0a1802100311031302040b03011a0d110303030130030e1003020d051008060a1a280305030c 69
    0x804038602e1007001c49400b5580b0155140503001c10144548881c40c45d01150380d0710f42c00b00c080901d030b25460100c6104510035140010041ca9140c414080d814006080d1132080c0e200404108907140c1113825945091158100881e01ea00c40031400b0780640200003000c1e40b020300f03010501c50000d50010001484901410307240000741c891029100030784404c001000d1700c00184001d81c0c001420b04050b0f49000640d28a00003d010b103811100740c8299005940c14030700485200b03182c40070b602e082d2080c0010308504070000c006081140c9089807194603ca0329551154409100480c14480040d001e081d0600000b0241c0383e507986c4589440201c031983c4000d100d1014010402c040c05094010811480c198060319452411168a0b0030409401a906211405c0580034010791122072414040c1900640b246555280b032682071650480ca010001041c03103007040d040040e454107003c0400d9411010390300550720300740040d40c880c101d40d0000b02103e081c84101040114000180300780480540400701c226010b444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 476312742 1250 476311492 476311499
    0x909090606030601050108070c050706020313090504020d23030304051f0b0108190b03062a03010e1603060302120105071e051b0f0d020114060105030906060f040f090615 74
    0x6035110800c544890301a0300440041c00340b5801103020580c0501f0902d440d034460b4056503112400d2400e035034442d10141c1d1001c41c1c02c5a18014008101020342250b0008002c45d00e466000507004220350704000c0e100e4442034003024000c91201c1c02d9000c0c00074902c0704403030742d0b81007a1402030340c3c3d45900f024050b4500d1264100494111050007a40140b000c160349180694440341040118040e03402e07003000840740c1d03807403c00c0002d840034402c0912500303441e12810401e03084288001b494008100c048414010208014400c1c19008800781c1c1d00030010000c5d00d490303050a5401540140150740003e5449111102c0c40000e1202c1500001c0c0b20b007580e5914074075119100b00c2070f01c03000b1803d4400c981c04284c060000d0320700c405018900d507401c546418200d5100700c44992400b410b0032500408800181d44034801150404481c120b1280c120000b0310700302e4030718a4a56140e075221000134010501c5001c2c20047d80341295220780003a02000181c513420801c0510500c0d00000400e520b1403a1100d81d030180301c001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 476313992 1250 476312742 476312761
    0x307120513110103061d06040c09060503130c0f0e15010207120204090c030804030b07270902031e1014030a0b0f04140706030f15030309061d0907050909 67
    0x501074101e911548000c603000d030391440c42c003080d0740c281107040590b84c03c000203410020003101d0401035141d449802c800e040480501c0302380d038004806030060090340c000401056500200f00d9501074030b400030002c0c1c0100b0510303240c902c840040d405814030309242d800109000031504803982c0110072025003086411800c2c3c0c01a615001c82e8454540d0500d5489280800340c101a00401a201d00c11011000341d0741d281d40e60140309402903001039691006403010801c0d055005060001c0c01801d006107070580c2c11090b904200004018003c40c0c00701d1740c011000c1403c0d0740321604000503406150300403184a10703002d0168441c05002c0d119001f0000340e151000010f904000c10584c0d0529000035120007156252451081e035044007030400c5507502124038a002900100b841032a01030a01c0da640410300c60302e280401015075114010300d01a4500b55401000040c0d00328042001b202c01900f000b20386000109618030300c1000001c030803034004a44404210b080c69100000b4141500211084a441e40320500036 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 476315242 1250 476313992 476314001
    0x4061706030606010c02030304050405070203090a0e010b070311033c03131205120403030605040b01020c030a12030608010f06080105071409131b0201060806012304050402060915030712 81
    0x3a8054100401169040d4424019451010300141c11203182c10b5564000c1412268125083c0d00160804100c42c50686014109100140310144048842d94101198200c03980f04010004091044240e01c410f80d1a0040c01521780412212030b4840904c404824014015a0b40b14442040c0300d80304111040c1e400348490171b5030b0080a1003041d0800c00350440d5a50b10f22401c22140c0300b0240700c024040e21515080c4020030314481d03440307940d02161840c034200920040c0d800104d1401d055412001d4401101e40740007401d211044d8204144080801061905070024006504500080d5007030482403c0c1c0200540c20a20459070140000c0200740c4e038540084480060324113010759200e000b004048a186070666440c914450880030000342d980c607036912112400e212a01c5030015035111704007000180d405002040c01000300141e00c00c0000000c0200100903910554505c0c4910b90700d0000c02c0a54403094142d8042c0400900a440c6500c0c032150607200c183c10450308040060554a248100942c440c002c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 476316492 1250 476315242 476315251
    0x3010c090f0510020304030804030602120c0a0e28031b08060613020a0323071112090915090712061a0d0f11031006030b030d020a12020102041a040617 66
    0x40d907034001410081000034000c24901d41604522090101002181b9144014801148030703440c0165541704501003c82c0d504002002c00700030520901c48050845d0700800040c541100031a400c00c0301d000d1541014400706009040f40104258025010040214010703100c3c5000c100c605400c0e000c19610001a66102c9089076a260042c0700d6000901074141c968000e00a01251400c000c140300c10088000c080780c030540503d100074240c000381070151070b5800454004401c1d01d030308007604c1d61500081c401c49143c0300300c0c46018060a005030003d42c400010030507501d2044802840d42000b41041040106101c4046803031407043d603d01100001c042c042406148881651605240e08000c8485c61050081041101c066a01500e900f000e8003078464070001944034100c1d1192021985040c0b40c0010b0843d506002414066880524520b0030283c0001c0c800b1000c59009440b01c421100c9964100d01900683e8045113140704d10002691a81d4000740140c006d41c0d913107594030b603418040d01c14803000c590300c00d49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 476317742 1250 476316492 476316509
    0x3010612030f083403240b0c120a050a020f07030c090b030c0a090c12020c070b0906131d060303071104200d020702120f0c0d060f14040203010c09 64
    0xc1c02d034208500615195500450000d60500d0202402401c010491944001e07482e84141110403901314680620503000000707540c0e03450211100d00340b51031294105130760040380301510b40424040c00d034403402c0041100c140201044261100c0b8101c074047e219800001c42c3d44054000c85031491400d040c0010307800c08a0380c0040e545200b851516012a005107124000f0540600803a46007929540394000c1c070304014480114001040740403604020500d00328540b09050040c0104180c0d6882c101c0010300c0c806403030304162510354450309000054014842c01840710403036070784010001640100180381821551000700004250355032201059241e04c108034005164032124180300d0200d06040d0301c9005030800d80300f1f040d024659500c0c002c0060b40c02800000c0d040c3e41e0001504001c5051075002d0520203140d080c01040414074601c0115182c2910000540c02568110441400d0051680001c07c0d030810000f0200549801080c00d0780c00c0800442e8281c1c007030340c2400780e081400fa10550001e4122540c0c035 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 476318992 1250 476317742 476317757
    0xa080a0c030c0b1801060609061e021f140a0e03070b0c09191406040b040b090103110304050607030c0816180806100602010f11040b0c100f0b0301061203 67
    0x5680c5100160800d030100030204480340005036810381d03094011100110704915000400000d5404d4440da81c01150401850311000c002d80b91f080500300001c0508401100c800c241ca10a04910b0401c0e08403000d90580031900d4001c645100300d5004250800c66022a23a00540c0c2e9640900151030541421010640c010070402010403101c60311550021809200985000d01a20014121250b8480341540701810084c040001600d0098110203c1c441501d0050a06181600c3d141c014000e5100782503010600250b41c071100c0e8071a61103544040010400541c076410142045a6200b0701113603035001003880c014a3f03180090180c0c640700d00c01d80d01160800542d00704503134216212500414201400c0d028080c000c107540f401406241d01c542d0703100c0312901d046494080000d003541c0c4495488d0b40c52a252410003a40d20400808a80aa0300031114443e510ba10314482540307030200050782010641e20740007000421010907080342c44001c10440080c05032507182c0c00101403400c8640310040100b13805c1c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 476320242 1250 476318992 476319007
    0x6091a0d0903021509152508070e0a03080a021608060106120e100905150c1602010e04060e1b0910030c0c0f3e060c010905100209120a08 60
    0x26005804068070038070598944c1c9940c8000d443e403a0740143c600030030b01e4100110010f05c188041e060700c1e03806035410292128101d5100b82c0b4402000102c40141d040008100c0054a031074017418a98010200140050051507604e08201c1c0b074503000b03d151400140600451a0140b5181e0007401d41501c02000c06401c2e26441c0c54816a02c540c07000c103c4002c03554a80d1255440d80781c0a004030400c0d920081d0000c10000c20600c0d2603400c000c181009120324082c01c00034040000740d000151a00d500041c41c0c25035074400f5500040e90216449a0040d03440750409501041808000d03140d0b0340940c992800303080d45401901d0103021540243e185607038000d030b11521404015842500802242141400c0c42e45141c0030750344030301102e0840020309a80c0c00f4076040760f445408800103106490340d00f00002e0300407040d80d0103020340340e030640c0880c1861207800041501e01d13072100c0a502069030b070b80e400340480d0002d01c3c0d418040d41c06074202011042c4106440d42c0d4501004d500426081c3c140c03548050782d00c0c07400e002c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 476321492 1250 476320242 476320267
    0x40b1308030a20120408010204090c0809060105090402010c050d1106010f180504020105090a03080a080604020720030f070f170a0312090c1a0c010501211518080406091a 74
    0x403096000240c3d4071482005440f2089030800520181034904005680d540c14014104282e481202200c02041030040c20800b04440101d800c505441003211102080d0700c460004803441806d00c0409401401407a00140c0c440b40c11401120254903044140c503207603a61100126030711402c0d0700ca031034801c2520308250f20900401c0d51200354040e10505001c3d06007220507010034107900103600100c0c2c0203000040c4071481140c06c040c0c0b165104504a60a40c0382a5059981e028080004031004501241d9103048100c00c0d6070500100d1202076040c1f04503000141d4489040910700c41c54413031a0218090415072224041010440c080c0e01c94040c1c40ba40700000c4c80603840f03002042803d6007522420f004c0351020a52181c001640d0740740903902c02996464240e150301150840318180e00210546c01d0003a41d000582c10b602e06180c401540061001d001c1110780420180945a5452445881110148074504112480d0040c00996440d42e44141c601c0352200b018050340b41781da102603509180b042c0980c100010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 476322742 1250 476321492 476321537
    0x601062010090b10140d080c0a05011b080c0304210302071502041d0121140724170406020c0c030d0801090c030207110f010c08040b1308030a 62
    0xd05003000c4560045a00345a40c08a482d0600122901104282441000a41803954501800782d100040045030490300006641e80014140240300320300100701c210481e1010320000c1001a0000d00038080b1401c0f07014801e0048059841250108555001150b045070380315080c3d9219580c01403412503100b5881e00110803880203410355000b050780803c04000080c3c0c1c03015010460300345611000d030f107481c28480500d444006000224174403581d40e1004100441c0840b59828092803900207280b076031030941c01d0980c040030111600d241365100b09035000510310484920b91440183c06c40407109a00041482240d040f4a42e203070555451914201280102c2e10b294014080400e411048412101911004c681400c10320314505010803100e1004005906050050f07428000140c03904614080040d0b541080100c1d07406c0e00703240180b40190649074264040c4001030341e80344c2c101c1c60309034032180e0320803c00856511484a680104404140001c0c4040c00041661001600340d240c400742c03028515407207800d59 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 476323992 1250 476322742 476322797
    0x70605070c030b090307080d050f01080a0302060415060b0304050c0312130e07030207060f05060418020a35030309010617031905091e0a062d0c0b16020708060106 71
    0x40c0420407484001440100c010a00600c55950209c0c445c074002030250903111050f441496603810a030640d8000980c007107081640305d40d020b0090440102000310940c0100000c0e0090301c91314100206010500500081421200d0f20847c103c030310009a000032035055010b48008454050011601801507058086c09564409864500141845081c0c0c07165015103800348a0150341d1a40c45050086600300350248054540d8080202008209284d022a08100d05845105245201a841400780995100031014600043c15000b10241c0e8107140303003626540156120700580d0320700000040d0b10003612800101c5101c42c100518140040d00210b600c03000040e0180c00d04026041004810903603410390b01040003001440f110825181075003e102801d555134108909206c528590541410715a81300c01c5002c00c5900c902203820240158155030070034006000600d2060200200302140400c240141c0c40344040b9404c07110301a640d03100c81525a0000c0c0144c0001400e400140ac1c3c50240c82c08801001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 476325242 1250 476323992 476324011
    0x1803140904140603120a09060c08090904051e0604030e010302071b08030703030e0c092202040c030f0513120507020f0a271e0915090503030603070605070c030b 70
    0x810340e40000081c2200d914010310300000d4451018003601c3e08041000b105004e008050b401d103084540c2c000035003010814072401042007036241c258030070400e9010540e841d454000c0c2030030714981460300c0c00030f4071014030194041da00810480302940000340001ca5501036a019110407035294464001180a51f10858007511700021800910a0007620a40c1402c000c1801070043d603240c40241c83c0003815682c400311144103e41c00800b0703c65080e41c4007038200c0d030043c03640748801c45510384111803d4804456140003030351141c5841c142580d0a42c2507007005828174010300042005a840c4040504003603401131000e080302040101f80c94505004030001d0800301d0000b0031409104e100b043c00100a4004d64001030040b600d80030fa0b03d401028480d103420480300543c1028061813003001842410700780001ea03010f02190702c410703001041c043e0040003d000001740140500070312005013402c0e80e883d030055601c41d00900c1120303000212540301e1402e0769501d9a1007160441d0062131a1500c5100c0c01c00130341042d45 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 476326492 1250 476325242 476325247
    0x30f0209030a050c0f0307241103040e162c0406090e0a1101021203271b030601060e0603010b34110a0528080312010509010603180314 59
    0x60780c0400080001c144250001c00c2034501c08010720030403403241c84900b8000e50011000344510404c021044103070118052040c0ba40d00d0012a003142c010364082494101d9000009010070ba010b11100030324850304480c4d1051014105280c002c98841c40887e20144401c0026003a40c000301108214048054100810115116445986000480d40041103042490780400c9100c001c00c141d010080450400c04d0001d08002c103107001100085101c014000220503820070f040080884e60321903001c103403100ba003084515141d91001c68000030658800c1081c401d1207500000279030140304d0302c1d03044107000b070141c4268150303480d04111001c207402000c0382400004526844955461110700c8104107202c0c2101b01c41404805418844c0820800d28043c1c2c4c09188851020b104c1c43c0c071782024580444c44545c1e14501e8200c46480f2900c0c03005103e400449031400000340384805125440c1c5858180d030700032035420200d6681ea5000303908980194040c86024107080096501080c081d280003003200390206003091 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 476327742 1250 476326492 476326507
    0xe070c02030c06042736170909010f061b06021e1c060308090f0a08030a02030d05091b090a0b04231b160309050405090717010b01090501030f02 63
    0x1141c50300725800c010b17051286010490030404182c4042191504100802c01041ea0008003440c0c40c80144070b03001c009071282610307501d101214000b100180a801841484011942110a01080e401081200d00c10f801c2000003041c4807000650030300c111056501c0315880c10b00d0f115078503070032421003030015503103d039080c0461010407810826007136060f01100111551084402d1402d0950180007500302200e42c5421424000151004100c4022400c1102c00c0716840828500240c52034945400030800c07408045450003846800001030000c9890f980020f000c15942c3e4001c0c0750b5240748041d0560030380ea4900c1641000e9007024842945c0015088001042c201c1f11000410706640418801e82c905044408620380e0038100e0308040340c1c0081280220101c0c00c41d01c6260304401d4000c4080306803188508004190806002d0b80514008050241c800d1150b031500424154441844d446110070070b0b00081c240074036540044c442d071a6600030584071191020700f8140110010960b640340340c5003c507401c01806 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 476328992 1250 476327742 476327749
    0x501021c02030f0307030522030c060b03010e070303200c1302030c0d05010609090c08100b0a020a1e0308060d03051207050c2a06120103080309190f110a0e070c02030c 73
    0x451141c0f85c103880100d00c0c2d0811840e210071003d500c890001d1503007881c11458000980c85541e0303506003500080080b0740000424000ba0060000d01c842d10654400c624001040540103c180c005ca08017280340c8800420240603076940b108280003c40c2d030300901c6044040311000c0d2540c00785030800d0100341c403141882c020030380c40d408a44080c0c00c0b07440843c110305001c20044031107004148403020685032241040c20031495846040300107010b801c000c0000072491080c0c20b40b00304a000505c5400042405031700490445d0b020300c04000482c16000500e01000107403c1d810103005050324594150380b510328020031200d44044240c0090040410800200615003815201708142284145000014030840a200700c08045204801c2100c40c082c2e00306100c102110720f144040d641c11240c000e1032030340c0d0fa0b5540c1c440b00c50620b2103550003286a82190300150080c003ca044210038081d01c2009000058040030081140a902a00c60300a0508080e800142018481d0340070701412480542110030380302c0c950001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 476330242 1250 476328992 476328997
    0x1b060a1a22113c0a08070c08090301090c03231b0301060e1e0a050c07080d09080313050106060206040209060f12010c050c0606060c0c010804031403010b0403050c09010501021c02030f 80
    0x43c1c406214000c3c003210300e5a441d11520154815290101903c1e040d54250041c0802100800b808280000c00030440c0520124204407040740100400801c0105202d2038034031164005404141d40f4201c05c05000d541c215500141300c415095040003d214401d08201c1c85091906000f01d03650b019522240c0020f11000c94801807402502000001d0200c6201c585841c1f088860040107501e03090f00300014803040324820412180e0b5030380c210080b0741e6618004024039003e03011024009080340790000c1081080220046010917281c410350007803000742d0765941c08a9442005642c044c0d884441d14010035061316000e0000302d48403c001c0c020f1544071001e10b0402d400c5648807800600401d00001d1134103034064080c8a21a4400412504141400c4079651803e9460148a549606001100011505144c00751406680008400c482681e0301d6171070b0b5015400903001840112a24401c0e143c1c5100c686c6801c00741c01e41a114182d009040110b1040e88400100c245c0c40c40c0d00d010b40c0810811240c2c2150361400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 476331492 1250 476330242 476330287
    0x903130b0702100206042a0b0d06050108010f0e0105120a0605072627030d0f06051305090a030e0609040204080f120a090b1b060a1a2211 60
    0x500e603120440c50060107110400e40c1905802c64100c02d0400c00003c50102e40345842285100b0401c0c0c0340844c843c1280c0c140b003900d400c80030414601069056004402d604000142d131401e0782d99010710707662007103025194441c902070b0fa0796000c0e0402c0140400d040c189445241c501801048900c400300e661102021601c0503203864000404541381c48900b420825180f010410544100d4034940c90035442450000d10307084034580c04c1c9506200d00d80b80c4a00108103680c1100803103c410000201501c80311401013480d803040500582004481aa1308480c5114280c03040c500d074000303449480301e03540c2c040f60030145401040d40c0c0b01e030092150306520b49030391000c0c00c05001001e00400a03c10340d015081c1ca059a80260081642010491800180d61188000702101e840c201c901d91030313003003034603440a0882303a42100544a202f4801003000406191300080d082a0041c609440071075007040601080640718040d90244d01c1c441c030141400310035a6400700720005185000701e818201011700e8402400f04e500c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 476332742 1250 476331492 476331509
    0x110f030a060503010b0303090303030f0402010e03070e010807090b060a081f0902030612010e0d03051e09061005030c0f06091f080103052b05030a0609060803040603061a070b090313 79
    0x500340b101d41001d2045000300300003100114100304540b07000039a40d100c018468100110314001040441e409903810404070744004081c0e0348215181d49420448144c02d12520036184500c001c0000c01890300d2280703c000d010051b01052030490b0b1060141c8042c20050b20f000550b010a00c2c01c4404d4801008404001d000d202c0e10150b0f807405d19070204489204141084003569160000b0031102c6c03040002e5801c83c0b01c250307050100c1c40da42d902e12803031048400241080700754100442000007034200841c0062040301805445071710310740c80787c013403559401602c40c80b5504075036022200803043c40d21a01810440b040107041204030035090082d0404000c0f4040048081402c0d80014003c011040c40705908030502200100382410606c807240401d00c400140c00d206001002006c12000c00c1c00746c204202900ca2400705000040d55001c41c143e03254014400c45000074038201e004103540e0052044e0352840c0501c0110242822241d8680c0241024054070108ac01e110810086e0075040c001402e203070080c855031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 476333992 1250 476332742 476332751
    0x7060201020901030e0106060512150904030504091803050d020f0409090f0c12050a02150c1501060f0c0b07050a0c0b010b040e060409021003050c040e090607171306110f030a 76
    0x2c00240a4a10040340001c80d82d05000c01844440d07400001d442c03004507000c0390710070107803221002404000809001240c0203c018004c000605130000028400c45003902010012031000c0a4a018407808001004000400070426100100c445401403c00310a00c1c60166103400d5480ba0302208541c00d0860888040c0c0c4c03044900420311080c046802c3c001d0101c00d2083c01411a240d54003610f80c0c03095000244143c685648000c0c0610003841980d508100381030484050710201003c0c040c944d0400d129510025003e214441c0e58a4030548919203165403120f09482c0503221140e09584a41000c1107070710421160122880c003003402084024000d01c0d6040c0550b59913070500b00101d072403140c0200b0050066060801800042c0c41e007141d055141c132200e10b00054281c0f140c4204292030701c62a40040035800c034650522111417070104d04c0c2c40c026982510b0309111203028241054912504552102d0400e44000c001d001260042d04410014040307244024a081c0d00c3c0a2040c886400a031b030803044450341c2c0d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 476335242 1250 476333992 476334007
    0x12071505010b04240c02130e061803033909010e10020604020927030414010305011d0901110301091a19121a01060f0f0f0801060507140706020102 64
    0x1544699400b5049201c503143c035050505007480d0f60280700c0031200090020045114020300d2064414188007580141407402081c3c0038101c60020b441322400b0346656024400c0131660f82c007510717040c034160300c04040017640c199500e031190a40b090750048564100c1d2032500c082d090084052070300c0c40b03150b0b010740780302e041e00c51080c080010324207403e0341501401180301c1c0704810600b0360001010b50744568100e400d06401d40d25264030007012030b000c844465a00061015000780001c01001403c20340c0c207050400c5000000c103800440543d0020b110310900d610002c031000458481416071a40c0c0f00700c050001045080048248402581c400d0b40121209951002401c0a44202108581042c1011500c4030303000700b00e4048102d103090040c800c21106100c8210240304100c1c0d06420400300701505070886031991b03920103002c0c104045a41c0780f00000394161f80041604c50041115210f00e00c160754404182e40e08080003a01da03540604400d4801529002d2041d4114104012081c040d0103503600168032901c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 476336492 1250 476335242 476335283
    0x20a052e0519050708222a080111040306150506040605030403030207051504150c0503060d03030609090c03150203010305030406141909090c05030112030e0d0519200f10021207 77
    0x32402680c008040d000b11b5000c082865007480c1c52030841140d021400e0140401c444580c4c000304c0d540003049a50804042503106090f1401074021280901400e02c07601488403103843d5015104d014190380131009000c03d109842c03152014540c454446d0600615004964480e940b520203055800540240c207042040308000c2c04030300031801001400700c00d0003056000e4001810a020041605002c0c0d452100e800e4103041c0f2030f0b04030100810010300d080001c2a1141407400320206980410f64480315141d182d0b540501c69842140d0490360400301544c10b1600b455030464043c1d007101002809800180000001c1d0104186000001070040e1264482d0314501a075003000d80700c1c00c058910a000c07050004200803918800783c1c02034031394907242102c4a01034030800503040c220b0307007400682984034112540c00c000402c0040d0f0b4542030b01880c0c0c1c0b0140c82040c100c1e5000400d0364140f0498000d8aa0f8580348480d0911040b4030b4140c82840c0107980c071040c146800d4501c80d0b0009075041d20741042c0b00c0b2052100340c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 476337742 1250 476336492 476336521
    0x30b0a060501140a0806010e01020a14030d0501150203090d020a0503031207020c03030408070b160b19060b0406051b100e0a0b0109060305030301180204090507020a052e0519050708 79
    0x800c0343d50320300b13220350309202802c0458010095418084141030105860f07201b80841d1042d10b0f400140c2c2e400b1051041812070381d0b40c00c03460404268078a0f1000105080201c101e0301ca0a0640030341c0203528052064050040700c030001001281c1000e01b03c000442c1c0c56405102500003a441d06009031090300c0d01900003840e180310207034202d0294104210074008180e010a86005607095911207a0343c40d00302224500102d00300c040043d00007820354081c07100301204c41c3d0004004e221141d4060045079214450410184914800c0001043e000c0015001c02c2d2458850022140e0b4908140c9860181000540d0150303161241c105407160032032074100e801c100721a008507015201c100000c10441381140e682e690349110600030170000f55058044031030030100c5501110041c1c64107502c03d100ca4109564003a581c0d031404002100d9900406000c0103640b00b0700c001c0c40310b8800c41104ca0752540520311100700001c15003e0285c941016405030703426918155409143d000f04a2071f50f82420300d02d051181500c418 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 476338992 1250 476337742 476337767
    0x16060218040f1a0909030706181a07050307210f02221d090721020907020c01050d020a021908070b150d0201052203030305011e0f03031107030b0a060501 67
    0x30b40341c042e50007a03180c0c49058880140c0826140c002054690b2910ba41c030f14001e03008024074080c20110b80402038640d1802700c080d107d11075980030402c2880f041c50024a41000c030b036850000349040c00080c918030300c2650301c4810a80e8400004064910119000c0151500e5101d00399405400058600681c81c000580c0700040c402c5080ca10b200d10b0501d04c4078410304030100075038608815a4000308030314a40034003c41c4018000d4100101e178040c50249224090004400264820078602c00003030141030000c984290808416506e861078080c07002d0f02c00e00250000c0c1e890008510400305582800d0410007074a80c5000d010710701c89c64403280030785400162148020f0401d40b01130444161642191182c2c1d6141d030b005ea0342401d10036103602141000940742502d610950402808400e400810f1541682c4049e05a5168441c00c40000b82c82c030b031400944407142e1080301c426003000c1d402080468803c3c0b10039103207074686105a5143c685d07207848040e044203068542c80c0b546990f4480401440d80c0040d0660740c1f4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 476340242 1250 476338992 476339021
    0x402212a06070b150a0e071706090f0106050a0c2a05030d0203031302040b1012050a0e061314071d10030213090302070b0a020f0d051c021606021804 65
    0x40c60b00681d2020305001014107203e8501810b40b07038141d90b56651641d4140500200b02c215800e5281c205c0c0300900104024407101c44084e1520082a034505014010034402d00a590014a00d6442e06008480550114034203500300903064003054005007021240911101c05203c5003c0c1d241c8000b00c1410314950315a00c418400d600c070201d00304d09641c02009490703110700c04911144000d856400070502500d0803412044d400400c1909040b0600d0308410810f10391030510300100b100da5103441c151011101c0e01d01c00407000b03074031500011ba2403041e2070307070101c5c202d901c0381c3c5803541070f0381a440b43c5501d880180e8001c50b102038003000000c0a01504260070f203074400074417025081164070715008074420301940c4800301807c07502c80c26941c2c18036008010342c1d401040c000610994030440060000d40361101c0b600072110900800000400c032610481c180c80038000600b0507560507260030a001c1000b980301860480754902c090007800c0c0811003a1010303018900000840e00e4203804284200f2046881e0301540300b20 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 476341492 1250 476340242 476340247
    0x30706030608061603060f03050d030f050106090e090f0703080d0c020105060a0b21012603040501020d0f1803030f0e030a15020702040b1504030209090111030402212a06 74
    0xc0e02d4001542d40d040741003030038000705110b1307050b004501a2410790090301094928910020410400003500c001244981e60200042c440744600201585c5080c41004001008040c05100501d464002c080e007048140040b2031451484149007420001141d10a8803120400f00d10142005100d0103081d018080c01d10003081503207001c0b030008203e103403280a014410000032603151150301140011054600140120b50125070392801d140402880810070f160503c0403042c0601b029540010079101a108141c01511000c50140c0b002c55003451602c2800b02040460341c0319150720024018070001644c060342e00c121107411801c05c0580009401000c03680654800740203417000c108542415500401d00c400090394580450000030060040d82c5142d550040d40200b500240c55407400003031044a01c21703621a15659581900c0c9030032110412000d01c3d42c100100000f40c0145000503d1300044142800c654a281940021580c50300c401040c1601c810b05019011407068022420281c0f146002140c0061 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 476342742 1250 476341492 476341499
    0x1d13050108010e120c070e0606070c0f050406050d0206121902120610020d0905040507120e0106080606010503070804081e03100915080703060507090314030304020f040506090f330307060306 83
    0xc1c0e07610320501c5a0070310345101e81f0102d4015507a0b0303411146982d401c42081c0d00e4064a800c1c6200d02002c0c18421503102c1c5280010020355030902c00d0034203140c19001040c0508107004420030110428006040d02c84481c0785d03810380d8403021250720140c41c4420340900140068507000013030000207a0701140910555101c180c10051481d802003248040d15001d6a0210725902c40c000160740c4071501014542e5603030300384003601c41070000544c004400c075056403080b5000c540f03c44005540620054400000143c0f107600004c0c00308044500400900c1381c0241a10262886802d00303e01c2c40d0000e071f03008419506041010070684c0d0076806441017401c000081694101e2030040359583c0c491252100401140d19040000d03c5c01c0e0043d640500250b812100b40c40b03a44003800c00c01ca48a034402c480480c42008550200f0301541803510403280f103a000500900031320b841d41c441313050400800528001c00d421400007000803800003056460f00c980c06c89041040c031140004205814040746400c500101881c114041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 476343992 1250 476342742 476342767
    0x303090213091a243d0f090317041503090209010b030c12150a0b0a09273318020f0306011d1905040b0307061d13050108010e12 56
    0x25100440d00c12508900400c6001140804070b00a124190b4007001d001d0345e00d203202114040800c10302a00c0f429920062821106440345039032203c1c150009a07103e80107200094401c0e484621022115092a0805560f00582c0610354411349000c00081d403074000c0b800850038040001030141c01000c3d02c01d800c520305200c009071203006010a0b04105c401ca4000300d03054000c4000e00d0307480504094042a08680c441ea26214254800441a000140c103400c0004200718203500c00b18042205201c10745016030346d105003001821003440880030344090030170308802011411500a03c4d0700041c0c1020703140d81e03103818120200c816800003030071030060040245103403d20f041c0c811254003100908040708204a142051680b461000c4400b540158041c0d5080380100250780400702181c900311018820708071480d003815203030030f0f8503c2030750003142c0c00c03003103114001c0e031211b211145920700900700d000d0341000010a030060301c030b080c0c0c042a13440e55148244041c0040c284100700c1900c202080302c51a015880074071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 476345242 1250 476343992 476344021
    0x4260d17060103020904140103031e09061b1e11130b0603040f0c0b07030305060901080c0d1527020a30140a120f03110906070303090213091a 62
    0x582c101980024204001d50700c80d0b00224000c1d01c103000c1d00d00e413581c507454087e005042c2c401c2e40e152400c2408130403005c007605ca9041c840507585141c2d00d0090081c079006003202403041c80c01040b11000d00e008050340d40d40042e01da40c3c07540c49025001144940f600700c0240a4444d40c0b89522646882c20401c0c4d010031a02c58204881c0c02c51b82c04003090246000b01d0824a440304081c0d005680d5082c0001601014035615411075801020100ca80100c1c0b070b40d0300c0722001e0381ca243e1081c3c040c0e000603d0700c0404000c29900f500d10860540d040102040c0b06107040c1c1036981011215042e001440011000f500a50074242001005402c0381d10700b4802400c074040200c04d0500c401d046660500b403802100004100ba190b024880c40c0c070040d0100c9030b801c0c0e03c0e40341c51035005100e600ca12001540300351503556014402c0c09400816058507100d02e20780402c03a0b00b030210b02c0d400701c04150700b03050302c41841d0300c0162103860030049107808031b80000400c8151450720303900380032102032041c00ca811410701f80304422019040 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 476346492 1250 476345242 476345251
    0x4080610150207270b0919050c04120201030506120f010906050c0304021804021c0818041b1107150801080d05130e0a0f05010b0a08061e120304260d17 66
    0x54051380390b0043d030000029040c00c3c10704e2900000f000307081c03020120042c459142003499800050290759110118940d460041b03200781100c5c003021124907405135000f40d0080303410000143c04a01ca0010307004400d481c18030400071040b11695111840402d005652040a03045081d2130700051450030540c0000d1036141c0300200e01e00c640d48030100803400f10741d40d1300c441c0b1003080000242c100118441e802e03c05050342100301120389003c40034030302921700e141c40d2241141d000c481121010026164280c200c03902d1300c120403c1c00d028803683c5c90114042c480c5003014102c40340e0701c0d40e604035290304011301d503410704e001001320000f4401c00744007a040240b507a11051081d540c540b1070a28071650f1782d21214002c2c025070b50080e0401c40c80c100c0040364100c002c0c0e000b096031110948840180d52924000d22014240007010030840f010001c5540009281c010b14171801c0d2036550301105d0410ba107481c4015900040f401000b1413a03945111807403072010080c03014080d80713412800c1c540751401d12103150b003010240040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 476347742 1250 476346492 476346539
    0x41d15030d050315040516030e011103131112030406110f030a2a0c060311090d0b1f1e062102090102071706010603050c18090c04080610150207 63
    0x40003560004d0600c40000d0102c40043c403c0c08941000c0340c034600007d68107416040003074200700d010003810005029614074405800740d650710750380d00c41000c05030891140c1c2c0c0032a2051290713420f1030040d03594600440b41d140740c03050103990b9a9242402c0a1300031006c01072201c01940042440c440d000d40003000703945800f1801c0c1001c0c440d07030405400409010302c3c00303c0501d08202004080078240400d88850340c00f0340d0b103192010083c510740d01901071b420380a02990036501601501e01e09001540d00e04006803c80013041005040e1040e4008490302010a900180c80380c100d003e50741e035400d0308041150300041801d820040a00c000e44003030148050080003a03044240c0c1c00240f044600e0340308112481c001c201100984504d0000c009006489800030300c90344002038203100119283d010345c0303030854500c8500ba8110b004801208402d100b402e0380024560034030300c80705000008450f90188483c51199001c42e40d0703d00da050030700c1c15001250b50301450301d204651241c201804001c4501c4050000c6082c0613 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 476348992 1250 476347742 476347747
    0x610020d0816110d08010f0f0b0403110102150c130501030203040807020907050408010903030203060a06030b0a120606030602031302090a022d0415110c0405040206041205070b041d15030d05 83
    0x941c00d41c3c0e14003c0e0104809988102c004086806a2214410381a9441d01d580090010b55500c0803070501d082900510a5551080000b0800a8142040c19640368018010340348086580784086402101c00c0b5082c1c030800000180001c40000341038100d5000d81403d00301141503041584030708640303000b03812009000c0c6195034040707201140218180c0d402001280e00034445140e2a1500034060342040d00e4041c081c5000060204109010f40580854081d02600f422741081c5411800e0600411100059407550355070440070010461030300045100b440d103230340000410820752040c04003090008100d460800e00c1402840b40010b01180407044154403803044680141d00d480c1412020311a590012055000c244100d02c50160800c60b00080f190807041507421007108002130200f0b41e003040b90001c1d0f012000300018044562881815040d4501800484160b103440d4011041c199001c0d81205e000e0248200405480040401c103242d841090424000050303042c00003c00d541d20008107410090280c00b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 476350242 1250 476348992 476349031
    0x160b0c0f070b13050102190201060b0301062705061204051501050a0501050d0b090a060f09050708010501032c0c0a0503010630121e0e0306010b090d0b010e0610020d08 73
    0x80e141c403c9800b90b003041c001c555a030030341d18041c41c43ca4034141448025508040000030301030280c000756412201c42e82c03142c01e00000d82111603c45203055107034085500007038103404149612510007401000d100c8800421942c105410f240d1b140404040c40621156004e00052180303880c2c0007100341c211102800e0080d25203985020080c040d019501c0e4460b0480100ca041041201c00340e00507000310761415016803901c64903010800300396007086a0060100320024010130855120b54890701c0000f62a1604000c09524070100090074403001c59683d096a00505c103101051031b041000e00e004010480c001c00c5030340d240c80d00d40001888110303a4400c07480004555007031a00c0c03611004401c601e43c401207400342d03411045000f500d0f02000c04c00c0750b94226141c0020001881c06075800c07051102000303008000e542c2c6030140e10407090b48040d400ca50010898502400000e403100744d0781c0c0c041e207520b00c2048400d02c0d100c005d01c440e01c01000c11010442d4480068039091035008911660000e4039280c0b044201a80b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 476351492 1250 476350242 476350261
    0xd110315150f03190506150a0f050702121b0402040302090a02092101020301030516030203061302040618020403050d092603040b031312031e0f0b06160b0c0f070b 71
    0x103808071404181c10000030455210300c55401c03440b03084d03c00c81c820080c6403034000500011641c1750307858001c0c43c1001c01c10058620301031107072540d40804500d8001d00d070001755804903c440d1000707450101c0b240d01106011002100841174000303020360540703045007824a03680004000c0d050140c83e040300c250b0b0009100d07005032110840f49601e01c0005260b000740d140c1c07500c3c400d4002d510901c420340c0ca602038406610001c0441039182811640c000b402088951141e12450380200140038040b83e021341d40d5100040c80c07000325a00c400031072940740d00061311075155041450130039841300e01040c2004012101441180b4000c0584441225090188490000091801c41c41c603c62a00060b200c03241c08402c00410311010030240b550203100345201d40d80c9420718a416415200c44140800c0d2440a00fa2804e084440541c03256030602080390b40030850181c48008140c10b5441a802d1210034111041d41100b0b0200e11588503030490090f0203a14684103104818422030301807804010300165160010948844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 476352742 1250 476351492 476351497
    0x70806061306051c090305030a290925021501090e03040b0c070f0e0103150b0604060309020415140109080d080c07020d230f070305100b150406050d11031515 69
    0x13841c1c01400c2120070440c1c03d005c2c1c07003600101c0e640d900e0141080c40c1039106006d140b005076071204029449030b043d541000200084a41d005107045c0401441000302600c040c1c3d03000300030081242c50303005001c01c01216969480e4040d4160041e040761810301c0c46650100d0000001c0b00d08443c0b500120b1911541e01c0042c03e4100311080c0d00100240e05a1000464407503000318481e8120392080c0d907201319007000c10351a0f80a0b00c0c602d1011552010003408104109402070304410a500d20040001490305800c100c1410343c03490581000782d4804145803908820350708285d5040c09400d8800082c000c0d10b100041c01401044010880702da0762102003016003c41d02d40c0c0c80d1002442c4d40c0501100c83d2045944650303183d00d248880642c040348100d41940902c000045186001e40b038100c005030080440c510f0460000d408000c4000740c0000c041c80c0c034140601500b0001e03101811450307444030f55440f000034203c000e0310000a043d00034400100240301d0704c0b200d09507900c00006000e0300e64034a0021010640350306030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 476353992 1250 476352742 476352787
    0x504030c051f0605180a0216080d023103030f09090212100605040302240712080a050f280e1204090e0312040f260307080606130605 58
    0x1403060a000045010281110445981541e00100060b0fa84d0300100104040c1c1c000401c03940e0158440440d52003440d50300141554403041d0704c83e084a000556419006900c8118403244281e80404c0200c2448050b01c1140b01c2805d54074080c8654019210b0303950b001222901c40182842440c50070f13082c034603002e680844001c01c40c21104546030310030f4080442440c8000c03a4210a205807000e00410038501510554060b030360042c1c245044000c805e103040d1060f114411000221200030302030600081c0520f03003101e5214805a0b944290350078109880000e0381d84c043d180e8443d00c02800100b1000c241b03091246d01040e80c4c903158820b00c2c1d90190031500d00400090070104076038000d80001194105003c40104112810f5020420880c0e50818417240c07a400b580c20b148401e1610b2002103404a0250350220140078050401001c18501d05041215070321194090025481130100801c00181d8210403280d51040094902c0c03860702c0032104403120701001e1800744001744440800e415030000c8510b146940b49 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 476355242 1250 476353992 476354003
    0x3150905071b0501050711030c150a02070219030b0a051b160b01080c150c030304080c031c0e1b010e120a0f06050412020a20010c0609080406021203190504030c 70
    0x110b1020b09005010348012102c20002c150100302074039030003400004442500300c402c0c000c0c11041d001107080040e140c201a01d4402c1c04c1c0d03028440d00700981e07544510003d849c460343d1078250b642d600d1441e202d950524000e111014003032401c0c4c1023004903520a00211818080c18035040d54502d5800a00a0300382220f600c0544190b031004000300303103620002041509010126400c20341c2c2000d006c544d403d54400c12500030216002400864006112030000d00550300714101541d0520f1000c80180c891262590a0000102c0d1200f1040c84400024072405d51022243c1c0c1040d0000c50900002801c0b9420004c522400348181c0ba6040700d004006214084038541d011003004641d01d91420b029014020944042c0e640316081a80440b020307000054202c440c0d80d01440c9a000c8900c0c80d9160f4130820017804409047c001c0024482c40068404d2041c00e07030252040301810380303031401c00c41d000b442c00364100042901000c2c04c1080c807c20b07418080400d100c0c0c0c403106101080659030307481e003202c0041c64440002e08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 476356492 1250 476355242 476355287
    0x7050703081c09060606020f030c07060827010c120c02070e09011806020a0e030a0b07050304170c15060607030503010306110712050a020111030103021815120a0209070315090507 78
    0x4101d110317000709044426a41c00c48148490022a040d104d00c03034003d4054140d44002c00401000e8000e0030602d03171203031400c161072040d01100c0101c07580281c40590994040d9660340d01c0c41354034580240c1900c144c6200b0140411800548940107595455075000300b84d1100c18070710020b00c1008003508404440c41e28188038000510061600001030341200c5840f4010a01d99000c0d22500c1c100012007250103500004000c80c07640b40d159080e0758980c4098419070344180031000818415412000074100d4100c0c1c4c100400240c1003800b24111040409040103200741800c1000c540803e50003415a810b580d00080c000402c01c5000c0055065482101b10040c402c0010304003403080e90750000c0280021a40f41c2d00203120712000c804c1258594071090000941c040c0790340300076100d1013180c2022241d010024804040032035800200013500b081c1160011406544800ae0f0380c01103040c00032904ae0400511705040c44140c061145000b01c01381e00b8041c440216688100080c50302d4451a401d4040c0403080d0390044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 476357742 1250 476356492 476356511
    0x806060d02210705090105060c060a02130e040311150601120e01061a1e04060f180803030a090618032c060f0702030606030a030906031e0e03030603060a0207050703081c 74
    0x2a00d40f042482028400c41c00341c00000344070b00700641111035000c00c08020f0a2241d07945c0d03540c08020b407c658010748100419017008100c0c01480100785010300c0c041e071280e4520480585030240350022041c86000459036403014800140d80005602d500700741c0315500400d4661001c041640144116805940c1c0d26803198800302c00c0801b503800902604c40d00050801d1703810040c40740c25403d44030714854240011501140d80050501c9409480045c0100b4400004607030342e95489246160005d5a41c13403401c59541502404001d014468031002142003007009904a84a032000341400c1688980c440e080750400c0700c08000002d02150b45030300c400c1c004010350b456410001c4402841d801c8900102d0007445501c01080c030507c0c000860350070703980c3c3c165a082ca0050404800300c01605007c3c0145014004440d103082148645004907c02e101c80200116120300d0210201407070494080c007410a038600c1041141c0100e10b020070706030140ca8101711015690041d583c1e00100e4885401c2010803190701c1c02c40c0e401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 476358992 1250 476357742 476357809
    0xc0702010c120819090807020d0f120f02070602010501030b011a040b0a090f050303030423030f03090109030f090612020a0c1a070f0e060304230a0f12090806060d02 72
    0x500400d0808130038041c100034068a5004c540002e503028081d0341d014010b440042c80c0000c4420800303840361034100d481351415602c884000f8500034055002c562243c80004038a54104445001001c00348000d101071352542e22038807005501806050b080707640300d41c10403103044a00001c0b075004080085003d50b54032003012009003040b0b180e000740e44c42c2c2c03005040000b405240000a0302c4c000e54001c0405191802101c070b00d10702c603481504002d1054042400241002c00184010b544204544000800d00011030300c1c0040850100da076424050160b0880b05110f100d070702174014400c02800c440c0043c3d89610440c000d488164504100428800003e810080d411840c20302e607a01030807013615107050300608007400380c820034418205d90380c0101051000034003181c3c1b007000b00700c061241e031413801c90b051075080451402d041201030142d80b2800c100550390304110210701c48580824070b6190807181503003440901030700c0301c6010303001502c135460900d00310081d50340d2440d205030481d0752800101642011200c2e003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 476360242 1250 476358992 476359007
    0x190504050d0803040c0b040e130311071409220f211e020c0303090f040908040b1206011e030506010e03060106090f05270c040806040311160e0c0702010c12 68
    0x22517054105003800500d810540d410740d010360f0304110940c280d80d5178241580001d191280010781c100700f85820800c0f0b038418140318040190400c00d01d0031103c0b07000da1040c4000c48201403d40041046015034400503201111070110303106500045e40c806c07030700e1a410405500030079003940114a40030312440d6814140c214401580b40d400b0204100651450904166111500054503c0e0540c2080101d0616032409600607009624000e10018081c1c1e000d45400229802540100301c004200040003000c0d4103481030300c00c1d030002d03007403819141610100740458800e614104619050540f20400309086038001d40c2012001c80010b001c81e00c0f030390b07541e02c030007000000148940301c56104031040209040c1050920448a01402ca0003a80c0f00030200c202d5888130700c3c1c0281000d100302802c1c01b0105011209000060280d8000c2c2e85016a03140541302007428110707203c42c0540c070f10003071080c100300b03040076440319903840700d82c0007106a00c07036070b8900050314444041c01d0010541c0d4441e006c4440c0310364000b0780 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 476361492 1250 476360242 476360251
    0x80f090102190c140a05070504020c01020408010e15010f120f030302160b0717040507030b0601120f0f050a0e070303120f0510060f0206040b0a0c0318060c1b0305190504050d0803 78
    0x110110140100351301c40351528401100503106800400090010382807030b070001d02e2041c00c042c0005142c6565242d10500311040b0600c041c40301c1d08204440c107070302c0c0c05648405026214286c2445c04591801c03000e011054140c107001040d01c08280e070f1a0041c0340c026030503a0303044059100a954880914038103c1c9503400d01b12441c0c0040785c20030f0007000c000d505a441640c07169a105005080c080d003103403900ca0344820300615160401c804040c00010050490103183c0082020590120340c00070010384400c1034a400070041c0d0b410314074150600b03241c810005440c00481c0d0b0181811030762122030800ca0700203000000e4440d03413a6801c100500a100048003581c0c0112005692a1904210000001c0342c4524041d00c1c0a0820003200700801d4004c90a54001ca80c03040d65030400140c1d5448800c4020700e055808401620081c0d07940042050b621780080305c0340c11110740801301c46041103803560050454002d8540c1d211194407150247c40d04a4001c80456016042c01848001d01010030310705400c0c80d90040341c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 476362742 1250 476361492 476361503
    0x70c02040b0618100c0b062803060f110702031c2705100e01020709150302121501050a0503330108061801020a09030f0230011506080f090102190c 64
    0x2940d2100684610307010050913502900e00800e540b940c904100e885078200c8009005065408070329808c0e9020803404000961286402042c03602c00b80310b00d241100d50031045d40c04040b0b0204488001603034041401c145400e44c508a031940544582e0003107074080300000c10300904005a041029080041c241000215038040303500005c0201540011907520492121081c0564802c0000f889010225040f9440d40352030344505083ca9503491f000a000812442e8111416403c1441003000da403c54400312400b500d8250b501080481c0750030042130b503560032100c2000d044d942c2d500b002e030200b210303120003140f800c6149a820080c5503102e018140e11101c041d035850100c4410807229030200b08040c000d89441c14040d80316040014559155090207908403d001c03a8450602c0301500b41c582401045c43d08510503210800507180f002c281c206084960b0759103103101c040e034107071010002503511004507580301c0c8010800c082d40340c41d03a2100728060700410000140401e20440d00000e00d680c13140e507219100c0c0c01038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 476363992 1250 476362742 476362759
    0xf140703090507082407030b0607080406200303071103071202010e10051302090603030912060105010f030204290415030c1d100f050409060e0f0708010b03070c02040b0618 75
    0x740031180d40c0f0008400f034401700443c03508040b42d14080b5030680d103511200f6424041200e0640000003500f9a020002c00c858a1034089024007195078000716400c0c282d01c101e40501b2140700c400e047c03641c0e240402403003401001840d040c12000c030b6809000b030710f040c554840c41c4443e84007040c0d88041c1c06085000c0c11408948200490032100c0002d5000e2580216802d088211f10400140c0a2001c0994000c05d20303a00340c8030810041000c0e40340c8800405407a0490b102415155041400050144080608076030030540140014031a41c0500d1603090508a01c2d2032409220707101c8400704102c9801141c1c0071100080f4049807412046070190041c0e02c00d90102d41d11001001000403100840c181640a40d940000c5440d1407400700c0350203010304100c101500c0c10a5828140e440380c200341514503503001115446401000c0c0807100020170344143e04902e113400d00c140250306001114085000080010003046482482041591225070201c04d1081c1d0141c0b4a5a8078442200c2030202d00c1038240400d4062a000f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 476365242 1250 476363992 476363999
    0x2010b060406170604020405060304060608010b032a030703050a08041806061d0103020405031009020f040903170a09080a050703180602070e06031e100614010f030f140703090507 78
    0x1c480a072842925101d08040312222401c3c050310b00148002c4d0881e90070800804c03182c2d200c0001d18800e41c481c2c10003142040c00c1145032802c1d2000c01c407007075000f60f0280b00720311000c5030107108000305c040032984c000c1803800d000c000003841d00b20181c1c40504503009000c401ca0034814054010310546403500508246007a4180d003030811101d4600c200000a040880004021070b46482c080620101c149005818181c985c130000f41443c2d88031032001d126907554060340342103090420b1000d04c101c408030741c108035412064801501c807801d250500c114440010300012001c001c81c0d48000b10003908410140d4648030300d120058032680c082c60041c0c0106000c808509186410040c0d40b6094681c1540600441882c044000c0709007000503082070360500820081d00d20300c0d400d041141d501840711000409000c000740081030b0131902d03290012002c0001c0e04001540a176040709102050003001d1900042c1099240d0300c020003091240c00c82119000048180040607031b0580085a440d8010015528015507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 476366492 1250 476365242 476365249
    0x102042c0c040b12060409150b011b02060f0304050a06050103031d09010317090607020d06150b1306120902040504050c0a0b160201050903160308190f2708070b0a02010b 74
    0x954030552043c280d08000c41040d501e044221a600b103a0302500104528046698108132645200b43c0c0c042a5a5292480700096900610070b004554184142c142600c80580100e4914441c20003691040e02001000c01c08009c3c00b041b20350f54507a0442e2040119507100c0c039008000750280460041c14035105400015a454644071b080e040b282d00c00404900180d0104000200e6080891400d074840018010f51001d620750080210840784280c2c4001130300c0c10044501c0d8115402508510380d07240c802e205070131404c0c034604102425a8101d0500303a8010490701c03071032070250074042c0000b9082402c10341403104000c0f00280c4c480c89104c0440d0096502c9454049241c6a8020708405058103502440c0c0318009d54002c0008000303030080039007600d403143c1070003040e50450086640111200702002400200d04003080c0d600c07864200591610108100d6070b254014103c102d40b44960088080d000145407020b48400903140c0100518002d59070f1159945201e0303001e0b90490a004005542400c050165030300d03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 476367742 1250 476366492 476366497
    0x307140301090c1d032e2f0f18060d0c0c060b0117040206071a010e090c0d24021b0f07060e060a030c020102040e04050a0c0e100b0304050102042c0c 65
    0x2002e07004046420300a02040d10750481442205403410710511442c0040fa5207007e0800001140c982c03005210001d01d460810070705010040f244006030070f01040743c0d00c80600f000c41c0e20600101c500701100240da5000a612880380c01051a60180b405031941a203e42000315101811700909003001005065070064075014805803440f50808041c4d80024010f22307015000d0503009009039005100d0507410b40e000c0382c1500382038024a058412460030080d0380c4504020031004401c05840c2402026a40c0e036559101e4464911114154031841c0701180350341c1450f03070640344404450b001c4072185401088011342c56031040d109148040c0603070140490800e00034421980c5003440a41001c7c070341f98003d28210000c1141611a03002c55408220001d011014012030354019802400030340481c5246281c05050180300b5404010040c1401003007005480720b030000042220340201805540741c0d01c40c03804d5030080c8a107400803521080082300040b401d42c000841c0c11031000900343c100c00b080e02c0d039124460150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 476368992 1250 476367742 476367797
    0x1801090614040b0c030d150e09070e01060e0f030d0e0a170303061c02190602060702070f0b090f1305060306250f0309150509210904020307140301090c 66
    0x2070010001000301903071030300040070145540310507039003000c60b03001e891420b070340c401900c1105c03920311480103102c0144c03e02d1655411103032140003402c0a5142101716580d14405100f100f05226803440d107240f442c2c6030120103820580d401800d564007400c6114015026403003541d8102d0041c482c09001262880e10b0882c076111b0500d0344170007103095942d550b0401180c66901d0300549030102c200c00102e00181c0380c0c0d20360300c607150119034007100e182d5061070b6000303141c010024031800071944038040030041c1d016038403042c01c1030381c10384150141d4528100d8041400b10284050361a00070315184001e0401c06a15442203001d004101c003500d000d9121010003540c440d40e20a9100420010800701004c01d6005a412070105425818007196000c2540c8030392081050409141001548480c01c205003a44144131b503c00280c07040d440d0b07091054410b20740410901544a0703540c081c541c00400314a03018092188012010326200015641e90386841c0b03400e020300030b107400180c086109107003400313860704601c850752114 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 476370242 1250 476368992 476369027
    0x15030e03070f02010c0614040614040209040b0702030f0f030703061a0307050306040612060f0b0a032a0b04080c0112090201050904110903010c17060306090d0305091218010906 77
    0x80c101d030341d1101820450151000ca0600c0365107401c20f0300182c001e0043c1c01a01404d010641202d10301400d060003615010000c142240b80c07ca0104001030f600c0390601c07500310f604460b20b035007995101c5000364598811890114010345000c228040c104000c0002144204525502400b245d540c94040640c1c81d1000440074020034802e000103101c1078030070350280da8032440c000c1011485a507600c1c045452404007960581c0c1c4103407500e403140e10112190062001c650b00070b952508a140ca135883c4c1d04048583c1d1100849000326820001080c620702030750b104040d1902490b400c0c0d41c1d41c3ea4034240b81c4e0780c81d540304013a0301148500b80700d04070310000b1340b149400e02901070f12481e1815840e807081100a0540c03401d01000c400342840070415a840900c544a104100c4d500d0310045644200200803070004028030240c42944450f00300003421401040361140c0c2d5038981400f0815441c0c02d080c941c245120103030700444203080070070a000078009440c8104400c0800b80c0702d04692588480085600d8810400c0c0c9040d0b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 476371492 1250 476370242 476370247
    0x6070c0905091204030501090c0e01050d03030f02130b1c06050d020d030c05010609060302040605040c0c08250303061701060b040b0c10110306090901020a021c02150405060115030e03 80
    0x12100680280d0b41c4040c0031000e8a000361026248a4803d4026800c03d8071b0584d501d0030300d642001495403ca00103030110340c2100c3c04070740c034140c000354030800c100d2401001c25880782c007120100344864050b5402401c1101e840c84c2d8594881010007681e400c840c50104c000c5250080c001c5203041507200c0e400655401801c4403041c02803035028080701c1c0c00098000c03000c100312a81e40c07a0124400703116850190414010100703e0314035600401c4150396240e0002446036140c140340e1107100350040411014035521034105619801d01c03211340040110145030707112007840180a15420564158405015070710445004c81685840e8800e06080302c240703000f5428031100030401488010480005016904845030446405500c1e034103c034819a51014049101c408003c0213101c0d0300c1c40c0451484bd841042c68000b1810a60040d100035600c00c089150040e8170f900c0380380507400803482407190a0a48003002111201c5d82814900740c1d6540318240305144c0e051558008164155220380141922034001c48025030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 476372742 1250 476371492 476371499
    0x341b050906060c03120a050a061a070215040306020f07032a14030405031b0306091f090609050604050f060105011b150e1b090109050402090727032006070c 68
    0xb60941c00a01c00300c58901c0309000c00f4403001e0706000c109126035260007000c82c00d800c28105810540e1050b4010003040d500d0501d800e00044c114174299445a074040741c2c05400600341030389090051180d90005008a40000396001c9040032050007880440c0c0300c1c1c0d4541c840c003282d440460044681ca0103026007016032004842c00030903098800308441d680031000752031801e6aa9800a0304c0c11004000440100308101408940780c5001e210941d4031081150207400032807881c030032201c883ca000401c82d82003956529008000c1c042994001c211244d800000c03030b0010700f80381c204255141c000203c001210710030f62001080c19481282c00f814480351000c07080d400c13009581d44900c0154203000c10040920394a045265103010200100941281605034206040b1150001e11070405016000034040509241c00c1c4801a00c81d25521035010b08545815489580408841040d1070072004403001310072031034503020041c00302c01000031550252199400c601c042d07448052160302d004003400602200b04580c800c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 476373992 1250 476372742 476372749
    0x10080f0604020c010606081905010f0306021e030c1309020903280f0b07090905010f0b09220b09060d05071e05090106030f0b030f03030a02341b050906 66
    0x1900480e0003003025040c1000c0308615821030b461640554001751204091110310158034840c030b1084100782c00240447c0d810050622800811880010034850b4002502040c2c403404010190180c24054811903a074200200d1401d8240c104810020351107003031400004944c006032088420090002d005001c103e02420340d95401c8205111044502e06941000d000000300c000304c52031f110910441d01403d1905044200410f46005a00800001c03032818005108803c0c06034402400c48407102c005964450320100031800019030302c40380e00740c2005000140c5500e40d0503a000070a00050a80e081d14659844008112264442c42800ba06d6504000700601982d03488603c00c002003c07a4030754520100340e40d10045807011009902080002c2d0740d402c5210149140d90103031051000d01100184822140032203890b450b03120103000c07c8003403030f400a42c02ea070a00090900c50800031401c41651702440d0b281c0a4000c18464084086403008100309400c070b144501c210184d003e540014150310030741e81e030701000d1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 476375242 1250 476373992 476374021
    0xa090f060b03161803020d24050a0204300209220507030b0c12070e0a17010204080712080f1c0f0b210303060f0f0907080103111008 58
    0x1015140d4450402040001c1140000c41c05501c0206a0358490301c0819070040c41c001a403032441101160203141000513070344a800c101265500302c100740c3c036190b4141c3c0070f83e0303981035010081744011400c140c20410740c02101c0e030240c0111307200030240383e140c0c0c920301074100e0b10004201d808030400c1042000e40005030801000d45907011161581c08032666203524150058040c440310704031081d0384030714020302c2003140485015410039404030600d402d007280d486025074031000041100c000c019980c1032088803a41c030134030700c54024203441001030f080800489078240070313601c5805104541c1c840c1840015001c1d0003c41030003c1f039500312034958100b4404240c3c1c640300e03a00a56030b0020881c1052081310100c440e038481d8000d07007102c0c03a40004a21040e002480002403c101e401510405100c070a080e80d0709012045030350040044580c148a81602c40c00543d19284840200d0341102018007000307500740e0005d800d941a01e002d02c054070b55501181080011502d00c4180642c001003408000c108000c10460301c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 476376492 1250 476375242 476375261
    0x1e18120812010e0a18080706090204060f0305030304060b012c0d0606120c0605031302010e030f060921090a060509040e060c040608100e2d01060903020f01020109020a09 74
    0x3012403409507200c00da0554901c0030f0700507000782e40075001030001501c401e214203000140c950501012000d0303039072100c4119000d0340384007070603140c0c95120050456403540d0250002d49028901c98512503141d0071700d07a031b482c2c00440b070807078403940342c81d0b0347e2503296020780e484000c18502e12400043e51307600d0002040445d400d24180c2a00145011004000a007032405840054400c18061444503111800e04240442c0c0c1c83d8402c0e000d00604000344030106410403003550403240c080c20010f10100c181e0700420f1a000071084821042d004070424801180000701d805201e42c3e101d039840748040f22911340f00c1c1d2075034030501e40d04c154020030004c810450320340503c010b0848080300800002c1c40d40d84001e01607050401c100c0342c036000313200c0c00102441201e402103407940d0032000078958440b405003040c00d0103000b0301000c0d00302080c0c01404038403600d2210700d02c820b0441d8100b00c502c2d17000c41c82d42d607400003901c0311035170b408124461407219403c803259520500c50149aa07130000c16070422a490081c2c0800240b55101 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 476377742 1250 476376492 476376503
    0x103020d21030c030b181b0d182001020a060c050702040f24031205030402030a080d05071101091703070e0a08030d0b060319020f0d0c1e1812 62
    0x6404072000014428880c01c0d1404a880104640c10a4240103003100c0300c001c5028450700003000c004a00c440300303056440c0d010058034220321000128494149080c0522035400001c3d5091071240c8200340e455059260850b4851084c8201c0c002e0f0701c1528503040c0d0841c061590040e40070701d4500000c649250088030603071104e828000d1800d121600414207583c8940a46076486445840c2801e41041124900c6010402c0e03070015400d031415076884004014030000e00c0e504021000c00450290765040c0b22100c138150388206100e5903650103007815009810f003101c142e80442c400c0e03041c5400d0140103014403003c0d15030007c0d4000100d200b6202d190020341014101c141041151711400c040c58403481020360141c940000159107583d0101d10f160306482200f40220b0041c41e040c0b052040d00c1088200d403100c1700c4084500540c0f134250861003612540030755134002d203225050003501c1d81200e8105192003d444100c80c48201160220032040e5a000c0540e420484000d6441404101100c001095a80c0d40352240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 476378992 1250 476377742 476377763
    0xb030322080303010e241903200607020607110d0b07170c0714100c0302030f01060219060c050d0f0b040b04200309160806072601050f13050a0b03010e010b090103020d 73
    0x42000c0360247c449103d400101d2842c100c414400e0000300b800c0070500c0820211182900700c81d60001c28018010035100a000d650b0108203042080060900480305820203000751500c00444d003048080440c3c02c0d101d81020610701c01d0b680603030784604181d441c483e9401e44030303d83c9055078940d01d400030555080704c008c1d0709020784e40c024102c020300740c085c08052000301d60700562203041140500c800200182d12801c150342c0301c1980e1b040e05810702d00401c0710503500000000707080502501c0907100392040c0c00030143d070700340f4000003a00d056040b80c1c0001100f400079101003164003032a60a000440b00303400c0820451001c1100300360b51506054008680c060b0b184c106644e1450030480030445540b0240d00032168070b8111200f00014658841e0a4019400e070801c41603880044010a9403078419042c003506002d0710940705400c3c4282c4031040d000c00020710f041010003e514026010350f005200100025211703501300740107490039803014001d0407a88a0001d00d0910207074030f140e003041507408080c0401c4603448400c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 476380242 1250 476378992 476379061
    0x604120c17010e0f0a0302061b070c170105130809060a020c0604090c0807050301030c050f030a020901060f180b040501032f04061413180b030322080303010e 69
    0x1c40800c2049900361030020030503955031442103041045581041c0000d80c055203009011940c0000c4d801e03080246d90284c01242401e0824459480c4035002c00030b8510b0200b8040000d03034030010502a010395021a000700101c6d1a412400c0a90082d010809801d44505018071480b510f000001060726a20500445095085650100c1c85981041c2d01086e078041c1ea5110001c0b1117a084101d0a500404034902070f03155604680e0342b51a5003200b8011140981e4042c0842002514200300303c190058005040b28031541c3d40740320080080760f40003070180011350f0a1014448009034800840b0544a46501d041c2c201410070004400914211500203065006030103981050b80080c03214642c0e44035107400c5030781d48500389a800303890100c0d60894840440c10400c01507501c40801801c1c3c8094130b014451a800c940940c84140c1b0182042e13405803907140c00f000071000070b03200724104261203581c1501c401c203207400e507a0780c405502ea000c00d00c01d00841b180c1840c005542d400440001c5100452102d5014400380b80 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 476381492 1250 476380242 476380259
    0xb010516050303062103070609020f04092001030c09090c0c0b0109050405190203061b0f040b2205010203040306240305010b0103050a05130b0a0e010e0a120206060604120c 75
    0x1581041d41c041e0070001c140555800e20701c1c240780f0181c0c60b44071071014402c1c5681e01d00340e90b8401e0245c06800f103941c0e140b03030030219070700c0c00544030280314024030030700030204141000442456190030803019070803a01c800c040f03254003034040c00c040c0c29002e4507140304803072610358000040d00c50764100b1001c2140d80281d881c0000c41c8418424080c14190702c00050320301c2d0615080707140403000503d2041e4170448082440050341c0002d01254002c0c4102000501c440f40c5842c00b40c02c034000c035818070250300c0340440d0200c2c07445035140c05441c0c1030700b61170103007103030720810400140d40d1100500501d401600100b2007440400d10359084148100012008515100d4008030002110940703500b04695594684400441d10342e450300a9581000a01d242001103041c6255004105110007000400b00d018600018981180036440041c1603401880288404145001e81700e80719561100219114040d000004c081d403032000544611801c0c003c2c2034249890709160740c1104200300604120348445003100042000c3c42c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 476382742 1250 476381492 476381527
    0x20712060216080a050d0f021201210b07030e06180c060c07150309060b0306070219060609060e0f0705190c060905070e0907080c06070201050313050a03090e01090905100b0105 77
    0x604559491b034499000707100c004203807800700c582000e1190060148180c410102500c450448041d25608503990039011800180314440a10117003024601e00200014107030150411041080d0010a8440540d5a840c0a07002c101d50300909182c1944181c1010700941451401442c034108034008448505039201000c059402204000d200069290713903641d0304101460190392074081c01200031304101e01c1e00307a80080d554240c5401c1d0442c00400401c100c402d11005522036030142812150038403c3c25146c49041c500c03042c05031041d01d404155240050300c02071003481624003a041c04400b00740c2c061709101040300e13580141f200c21780d00c0d42e03920f504200000d0020007001000b0100d260614032286410f040340b505081d020303840280c860f0482641d06a244d540d40046402840c0c0c2400c00c0c584944544107140c1e40641480b500a100b0b2041c41440028150044034400441e0312849000c1c02680e201e401d00004e8038142900241507a006d0000a907059501d90082030b080e01c01854210b0a1490841600c489135 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 476383992 1250 476382742 476382757
    0x110d0507170c010e030309010c08030c0409020f0705190c05090a110a0908070f06020a140a0b15040510050102100c020322090c020703080403140705090702030a0f02071206021608 78
    0x662051840029958108045504c2582c0880c0658181681440043e00e210f5102900900380c0d00300200003007406440d10141c40203000400c204544071040111500200d83c0004002d442074441c1000d4019010701c007000d1246d000ba48600042e8001e840c041c140507415502030a20040e0645602ea0788400302c820201406002c40a603840060b040c7c90f00442034144032040d040455075051442080c0400c507000610306021a40c0325060f641c4100c85206d4090410301525401016040803405003d5590030580071006186800c9408100d1a110340000742203125141c1304080c0560482001c0b1048a0781c607504c803060800385030040d2843c00c0803032000f01040f11080c0407241c4c0120311180092081c04041d11601019581a00013000c0c2d45042d82c99054035030045102c0108102d115018452056000b444064018440501441082e082001c406902c03030f00515100f10000b00041d80c0b0100003480010004c00302d542d10701c6003002030340482c1c03180030183d1b00052204400103060310380d0b1400500e021009040c413 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 476385242 1250 476383992 476384039
    0x203060f1e09100602120c0f0118060b06041805090a021c05070b042d12030c05060703050412032705011b03091a0702150a0522110d0507 60
    0x28541010200440c4400c05000b52031800c030f22820a010342e5400154024841c1000b1211070344810710074035040d240c05103124004030194200700070580058400c100510b42e4901c1444c0a01c182e00201040c45a180500e00c50701800d2201034407100805a000e500c0300d500294480142d882c5200c2c9a004a070031914900d00c1c2e04292107440d14a40103001d010302014000c1e20a186400b0318051038200099003080300400c4c0b80b000b0110010340310351124a42d5213020014488080c1801202c04a0706029180016158080d01d0a001c1c210009440c2480780c4541071289500166500d01e2210321542100201034499030f06004041303c00200c429224640400105140b00710700214036a140c2ca203031085044058403c001c281410803c4590008581c0c944048010460702a940416610314608a01c0d20351072282c404500d01e1030b5400d00892074469003081c2d1081d416548803035543c0924001c82800b400c0b103158080c003e800f100c000c401042c0b920800080d107803806841242c0755691680444074050300401c490088 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 476386492 1250 476385242 476385289
    0x10515040b0307050307030209181603140607080f0901060e19060510020307030305190f0b040b010f0504050d050c1302040317041d190204030f0c0e040f060203060f 72
    0x111460a4000d19503188002e40c090070302d152034040880d5696601d0300009104640d42d1f40041d540c40c04c1c1c080c5c0d80391030b5a5040c0c210340f031591342e402440d1070b009080d0005660850f401640c066442100013901ca0044c0500d47d525070076503445801c031009156024014504030354a403003001400d8401b400300d07a8059004441100602d0011041c40000c40309203034011b50040907032500c0d8810007a00401520b296907003505020901f41e0b80e500810402c9500c905283d041d00346842411910b0f4125688448020030b000c0d1000c2222107010b000644600c98955040c40000740300300010301c0705061221540c4415440b03801110380d0b80c0103c030000b42034034103035400c1320402641c003003020401d11026800c0003544007160720b640c1d440d05041c00c40b00e188d481c40009064244000c2c0101281c001080a40525660000040f0440d101e80d03c92074168020000c0080580d01e29020b140f01081c0f81281c4c10080b402254003039071221400b0303203e5a5400107500300411203588540480564401500c51a40442115800301007507070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 476387742 1250 476386492 476386531
    0x20903160e0f130b13060905100606020106080a0f0f0203060f1006080f130507030219061107080309010809010209060f0306040e060403053a05090708030c0307031b050105 75
    0x550940300401400b0310580c0034003444405001c00900f10325158000128501c40e58501c441540b003100c0c4d039a00100754907d00f10164084c0718005c541c0300748895000d2000c1c05003a41d6140200d0070381c4ca003406a02159000002000d002070352485030b48026500c82c050b5901c0d2003609400080c10000222a000c0070080070008010301d00c0d21185c1d210000e00154104403000d81000c01c2101c00c1410001c100079550400300702c0000034070030100451801503a005000c483c0c044820440b030b8220710242e01c075207800b0440c0c541c02010f43c00340108084090f20078900c000c1d420500c0c00c1e801112101000b50001c011550308010041d141d4940d030004009250042111541e40d090140500c0b080700d01c00c403050300c00e9801440a00000030343c4002240c812018464074500b203441e07000302511015011161004104025044011b41c0d2810740e00242c0c0b00e0154141680c07000c0e070755841200d403240310f54003818129030003c01411001030300500c00c0250402d2115400034440c5449e40d40c56085820a648200c40c000c500e1601c0d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 476388992 1250 476387742 476387759
    0xf0a03021c050f12280f110a140f01060504090512250305041a120a11040e0f090f0a0b0103170f1602030705010903110d030e131a1509011202090316 65
    0x1404507182049829003480302d8040010402c0183c41b00c00001c1201d00f0012040100003045076160441c3c001c030300c00a01d03000280110340d503141084c071400740740d508000001039986050710415540d40e4000c4003502030000341510441c2c60b64040c00715416a2001c0d100364444c40c480486030280c5681c8a520b4040e50f543c1001d920f00e80a01200b180400c080340200400590082d0500c5001c0d00081345010206d182d0917190289402c80c001e0b60007049040f0312103c20098a500c0c40c021090090002c01d040e280e01500c95880c80c0c0c0c80341da0008001e040d940640ac010030019010a21110180e090003002604194030400526603a91040244032010546e1444400c15440e051284034001c213800d003413241e01c19285680309203e0480d9440c80e21710680c03a4030f4006c030034580035440042c4184070040981c40071a188202804c0203100c00d00381b032040644400400c9210342012026140244069441c02d4104600d1800454001c000c00108a000d980c0a02004509072010011025259060058940c01d603007000300d01c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 476390242 1250 476388992 476389027
    0x10f0506040608120d0b0414011502060a0b06090d02010212070b0f070c1e020a030c0303050703020d081b2505060f06060f19141305130c05042603070605060f0a03021c050f12 76
    0x4237500c0501d01030700c0d010150343d4a401c4840c0940140c551290800702c41c0010303806e002c51010050b81c1020006141d1013082060010f0a2085100341d6018500b62651002107401c2c2c2003d01c0014a00c902005406592a5407441401d0190384000d095040007622559003020074803055004401040020548004042c0c0600a2011521061030500700518245558081c89200104076000610000a04c2c013101d0048240040610240c207101d0b03502503a01c1c1c50466900c210803540300c1345040010010500c3c44c41c0100494080c100301142c4141013043c1c0c4441d415030048505901400c0c0041e50b100714004802d184c5c06000c503a240690302c0316107031b841e140502003141e541c0d150484075a03140c091488883d50b000340903541982d20880000c0c0304070800b0350b0305031002c0c03103c2c02c0c0f40121341c8004180c0385c0810a50381c004500c9000140d03003004019000c0750a2100010007408002d5010f103071380c04a07002a200c1a00002c02c04c501401c00c54281030001400541485181c0305003040c0c10100084042c40071200214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 476391492 1250 476390242 476390251
    0x305180a09090203101401060c11090907050a060801030f121b060203100506030c030a0203181c12230a09020604030c05010f050705120318010f0506040608120d0b041401150206 77
    0x2d041c480840d041d4803c000106c8140605828000302046400a126070440d01d400e03000c4014101494a0410b60181c40c1e81c1c48243c0308061044c4100c081c040b604074464013030981201d41c003803c04040001c2c255500504101c40560711001c000400012140032007602c05015a00350189400690300d091070700e080c4101e40d2440c1c011a00510042060001c801602c404480d802040ca00d40142c4030380f50b000c0003143d0429103111a4a0512420049460a09041c0c16441600484d52245581040c02c580c40409640040c40702000780c1c0d42c0d00c403107040029014401d0310f610ac003040c28001a00506540003c107290050340040d100510800c10600c03503541c1002501c0070b4203076607041c05030030590240e84140c2e4400c010406003140c076074003101058900311a2040d00c00051041c00003480751068883c40c02005180032125548503508104000481e034030041118007201400b1844140780c03506103050000038001c00c840181e0002d40c4c84903615160100c00c611a030181100381c503452090401100c0c020304d0460080e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 476392742 1250 476391492 476391523
    0xd050a0b0a030b0a02090415060203040f32040f0603080309120c0303011211212a0943020304270e0708030912060f01030305180a09090203 61
    0x2500703102255207003d01c0c0b580408650383c0561354106240118001d4290550503000e207200b85000071842d2078020010b00291040f81c85c1c06001e03036603142048600074161600d01c10140d81c05405c41005d599410b0b940000400e0003030008a20892018000421961654001d41d048200842130004000b410b0080940c85900702912505000b2000c180c940c0320f11042c49807844011074411200700b040b140041c0300c1566039000300540d203041c100341c4030f000d203070308040e5000d0302d860060900c0400d083c0141085110307003c05210803201d10000042c14001e10f201c000c2d10150f2001a00c10420300c0074010b0450600c94110401108920440c40c40171018400586031030350300640d0010300c006e12080c02c0c5141e217072200403440711200b0011402d140300c0f5001028406007840c000d014a00010403454000401050514015500903600909031b12415403181c0040c0d8640340c03d41505001000031900c50000780c00040000402143e42402900004903807080542c8146c044a8032030120000754603042c420f03c208044841c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 476393992 1250 476392742 476392759
    0x180501080c0924030d050307031409030a0f030612050a0c060903020609040903050d06080c031203011809030207080307050706090e0405060621070f030c0b130620030d050a0b 76
    0x40d00098264100428400d4503040b54901d41500f211000400751030000040c00307443d001c140760140100a68400c44d5104007107400c1a000c041070503944c0020a00c1107009170051401d141c42100111a0202806205001c06840c0da4010030241e40b10441e034540588030b4001411251a18070348aa60300610343d00c807109010025004101688541046601c588000c89000883e401245000e4449000b0b40c050b540105141c500013041c00740f0005110400c0f03110860403920042c2e4021803000b880d00c024042c000c8024600301440d1007003800c0740c0060400714400d00540d00301e6500c642003145507400c000001c1e00c1c04c1e40028030810910b9000105c000262a81e000000614903081d200ea56030340401521482c001d22880c0c82004044043c45181410980140c0541c0c10080d80d40d080c01c1c0e06120140020742e10039900c00400111a45504116441840d000c6034690030145000700540354404040042c0c16042042c0c54902130030381d0240018900440c400000145a08240d0381c40c0013140d080455a034080d203200b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 476395242 1250 476393992 476394013
    0x1060f05030a0c0504090f080315090a020f0904090507030b07030506211c09050d030503150306071b03031104080a06060602010e070b0c01020903030406120506040c17070e06030118050108 82
    0x43c5041002641c000340d0b004100e8004516121806660841c07000e00740b41c20100030301c41100002c001034405d14a007248c030680075454031032212040348111060b9100481041280d01410b00781908410074a50040054070600c6e6960f445001046004484050002c1c4d40c51041041c24645053b42900c03401c507269080b000d038081171034200c1e83d80310103c0d02c022800d000410010560b92080d02d40401500000d4900b0720000100c2c50040d005800c181c50310020105115500c4046060000700300340700e80740540d039800d011503480c1082c07600f1011a88003502010340300c444011103034440e003000700000e0041800811a40615051040440d51131390800b40c11a410019200031007100014003070b0584080c0384840360340316509032841c2d0082c0300f046003480d0140008074002840303076000040d00c1036481858030309101e40c0d03480311308000440710400407520101c2c1030a1181800d104520b208241e2000da1420803850401b2194001485a0001d80c80045680c2c80c28030081460326490041d140180340301801407003c040c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 476396492 1250 476395242 476395253
    0x61116140604120e0a05040c0c05070b09030a1e05061e0603010c05041e0510030902090108070e011205102a09080601050d080d020d0b0405060303190807110f01060f05030a 75
    0x200c4150f01d4100b02e81030f051801c035651400209401040024410004404404006400710b070061405941c280917251000686406400444032000d5008014001d017004c42d96600700c480d41c0d5413003000d5408054a07c5a40040c20800c03040d4000c085070710390421722500d650f00100c140c3e034000b0101c07400385c0d04207800789494a800c241501d0985140d411140c124041844400b811b00c4240e41c40f4644c0032000690881a16030154428140e0300d0080c2ca09402683e211000c6540d120f401340b00c0e0b01312000202c001008448090182032075140d00c50000d803104004210003010503913003811350070307400f0b003110154040c402c0b4804d4051402813603490074501101c500d44451325480d14014401c0340d02035000050810104521181105c90b44401003408645030200504100c0007030045c107000c1d41c000d9141a002c901ea514000060310070b0b91558003402c208100080e1421101ea1030040c000009001002c150401c0703200003449030b9000c00e80e070340b400021541c1c41d10b41c0f018403081695002c903000703070003d250b017102242 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 476397742 1250 476396492 476396513
    0x803090108040b151315050604030b0a020f040801050f07030506040605010c0f02280918020907030b0310021b0c040b03060103140c0a1205120f090d061116140604 71
    0x3a0410310520350307a030303c83c441111a00396a10044d9845182203100b0701900c1d80b40d511034002c10042c0840080312944139803e1100510641c08090600c40344013001a0894055070024034883e0315400d804c84c20300d5134880619094400c2034420800c030504c01e07070810901941c1407181c5540410125805d201461410001803d28101c102d40034200341c0034980b210095450b1a80c00203031010340700482d00416040d503a102c4900c0c3d0114040c1c0c4008904011550b0407000c00703500014861074004000e00c2d8242c8402e042500242420301e50360b6098080d402803075215000340e10190a00c0c17400c00c52a8010740b0104c000040c2070945140200d481076290410b18030f0542c8002450a0541c0c1d800154502c000300d07440c1c0c81502c3d041581d00116440032036550b001c14607519500d510003415100d14100c80780001e40c000d400b221030003640f81c2d403100020184207043d400e18200f4940b45071103008040010b100940045072900c1940f02d40b0110080d410401020007c1011002c49400d10f414108082c09c402e09150381d4164400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 476398992 1250 476397742 476397751
    0x26060703021c02280804050609010614011206211e0507050d06021210090e0715051602030d030506031b0f0f0f09071101060503120909040c090509030d060803090108 72
    0x550120794640f03031004644840c0072011600e003004c00300741c107000401082a4000c03a4202c075507018400106500341014003441056a10402ca200d0100002a0044400d0000b00c030b91040c8603030316100001003003882d90012203000c58070303028103151200960400c0c03440494540181e405507424000d103080840c5010441c0d1040e240c0407510060190f0361418400087d000d00d03542011484210000d11000b03078400114442280c1d0411030500008035000801500c50b1020310901c4240b010003440440041c1c8103c000b008034a0000d20244602612500460302c0c1400f220282d101103903484090211503d0200514803080070582d40304d41100c3c4645002c82d50b0f40b0b400109030b40c02543c140780039a00c82d50320b050f8030400301d443c0034080160070302d81740200400c1030442e40600d2265518055006c645414080380b1040407048081c81c140c0341000010501032036120041044d58a0702e103540c40030403078810b14020355010301810401146c848180e141440112003142d4004c3c402e40d0310421040785140d82000b05151b22 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 476400242 1250 476398992 476399047
    0x10512250e03030d0c09091811310f0e03070201020f0a11130f020c16142101061212020d172412030d180c090e01062606070302 56
    0xb4018101c5d0503910f40c40c103a00301c0c1c00d40c04d0900c0407086d0451a0340c0c0404103c18081c022103880d04400c8418409c40918680140301003400315682c000b003031940d00341d084c0f07070b90030082c100040c080c58071004000844040780d0000d0026080090200250b40e410050740d1481d02d000009400c10b0141c41d940c0e0100c04040091030b5018041c100c0c1100451503d980c0561b01e003031041c50055598189000d80c840d218400407058558111541c038001c0740c1300c0c804400d9001054070140600d09540300c170a000a145404003144e4840d40d40d210b641c003042282e0b841409041d07040c881d5001c2002c6030003071030b0064140a5a0820f00b0204500d101d0150341c85629825480c0d0800c1c400d0007505a01d83d20351100e071040d925800c10355500107540f40c01100710000008010021003109030303020002100a040f480c03140180c8844050181d94080c0400c1c0412042c541c4005035203240c02000207011903a61403070144035881c900da111a101c180079000618020180b00c6607034810f62030b10b803c40c586840c80b0000c18000c0180742c00300f00c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 476401492 1250 476400242 476400251
    0xc0a08070c0c030b0a0f27021207080303010f0b030f04060e070504150e060901063c050703021b061e0d090609120305060901090b010512250e03030d 65
    0xd41500070310008460540003011456000e403641070080080703c056441e4150700d8070740411008880124401c564204907a00b0350166840b004200038031041c2900d520590340540c468120100c1a002000039400a040d1500919240d6141003000040304005038482c040c0400d08104002d5000b513200d40c000d43c000c1e80b0040000d41d10604043c13441c0780881e5904820b412520b0003005a010404038103d100032a50f80c50017810700c0e03075640f40500c411082c007882068042440800c1410b03c00901e91b17034075441361603102d003542810f04600c160210201c61031031008000c20f00002c2c050090542c1401038130582070205d8041084070b00c404000c00c00e01e21880b518a003101d00782d240c11401f5031000e80103d441800c4419400c0c00448100c0c10104002c248140044800c10500964610168024083c1d9071243c40000e00c0700d0a5a1f217841942d6010b0121403440504000042241003a9041d003550101d0041020031001c00c10f800b051019400c0780b80008c01c0c43c1052059a2280000c070b42d80c000221800b40313511400115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 476402742 1250 476401492 476401501
    0x40b13020d03320d150b040302120f07140906190303030218040213050306060108040c050d15021216020304050607080a020f0307050d140f030f0601120c020615090c0a08 74
    0x71102d0204109001041485154040030a00b1a20240c14048142d2400300a060345417030f0020041c81c103510031040b01d210144420805480c020305003040300301c49103003030310402480440c4450608115130490f5086034031031256000c0c1402c040001c507601c04000c1d15180c088038414110004c2801180c80010201500007848034880c103020300a40f18a020094001d54071108000e160311200e12060141900a200d0074000445561007001610700940e000392040a07040d007010240a54000d0744141500d0309010000c00781070048091004202c21003642000604604011881c210480515120803085510078401405965180c034101d40601d588416203540d00e04440b102681490181500041540000308040c01806000b054040d1600300d281e44040d403090702d88101041d00d015688426400450910001d013003014481c9405422140504000110141c0d086221050f200e0682a020041e040141440420800066a8000038404039842c50a902c1e2840914078980a100c800c0000c000d0101d011a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 476403992 1250 476402742 476402777
    0x50d0e07080a03080613050601051806042d08010501152006040c0905090607120509120f070311010c08221a090d02070803160317010e040b13020d03 65
    0x40e00819a403401e0324198001c03030801809412007101c0d0507001e090140301e0621840b195108052103183d058450310308040c915440e810100c0e110700c03149900050100804030b00161500c0d100c07803640000c6000300441c00d840807217800c00818580d00540090b0306203001842425220000601c200704c1c6458503400840014001e1080350902c03c1100c98640201810701050100c594280b0095640e00c01e03050015448a51031999213500407142e0400282cac0442d250302c160319403504003603040809241100d480415503910694260300c0320114402015001529108054001b450010100300072002040200380085000d0712020b0b005258140b188249003141c8151004107240c0c6441070f400c0f00000d002c0c60300328400f09251000580301114140300b41c1a50406852000407458107580d0303480003031800d092a40600c2156500d070b40c40c048080c050511010400c800500b0b00450080075120000714540c1001e0a00c0c00803803030041d10b02065580d5131134030100580c8400c2c0030002d1a50740351400c09030402c1c5103482d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 476405242 1250 476403992 476404003
    0x605160c090e0105070207060801031205030703020903011506170c12040c0e040c2310110102090301111206010c050304061b0b10030c080a0b0f0912030108070f09020a050d0e 76
    0x440c10b480c20880244804056014500c105031603002c8170440b946441003503907000d0742440014403413040708040c0114248504055074108846003405030030440b5100c0064251154100240c18910301804104580c662080302c1d07030140c448000c0800c0b001d0610414054191280c5100d9031428230100c400b040c200080b40342d0042c01012519519900d90900385403949119507e4030a1001c00d4803201942c84007440b000d9000c0340c080d80002c086600c0160303007800c140c2e00845210325000b2155802d01c04990552030038062001410181001507560720840600006c900002500d9241008601e0b1500320004a0020464090301c086080900d84602d40252900c1c0c00c1051200040c4401d281d1810701c5150b8140121181c10340348142d607010800c3d5180c6242c942c0d150550100030f0035500f910408a454026206102c0e50081c180d1000d4403066540c030a0320303420f580c0c000c1c0c2c8010803540c4102ea007004000c20007001400a8420364006500c0c04000d5400204140918801907440503550910f060000100b00071 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 476406492 1250 476405242 476405249
    0x213140604080a030801091b0e040e1e100516020d0819020d0203070806090c0a0804020f0603090f0d0504120b070e040f0e100b100819020315010210060605160c 70
    0x4503000f400385450018003680782031081044203424a07000103012100d11455030b0819a190b9074071014550030800b00809007c143c000c02c8103e0151400700c076464003045150714140c402d030700d0007000a8107008584804559000b0058a094200c00d0b0f98640103d0b40420b520403c1005450101403a0f220081032a08408200c01e00c10911440012503111032081034014520940e559103175140d4a56800b0140007183c0011142032510203000c0014114450240c02c4098110380042c0c4940b08000541001c6074031580195161075046d0700001020030b5a003800c0240110b4065a8070f801401d1601c1c10903040b515011b82200186995068000141f0782d0f0300c10404000c400f900204140044038070404800000c1c6821180c42c5454019441020161729840c000c2004c100005050310b0307601001d118084550b184041c040640b0040200741a112050711030010f140501400a811150300c10310f00006440c02090701450103007a400d2080402031140c100080c0c5c1c0d041454074088449002040c900070071101550381 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 476407742 1250 476406492 476406509
    0x1305030a030f020c0121090f08030a09020307060e03100f181b0f0302060a052104030e0117040b0c0306040b03011401090b0312070f0f06090f030306090213140604 71
    0x1400c18181d10a0ba01c0c042d64180c1d03000c1e1800b0781e44080044800e801842045801c1050341c001d120205006a03000d5000b19000f0405c1260110040d0b13200b042c2a401526a805c00c0d0b615030301510294a0148821f0380180440c0c04c0100d44622803201180d141d80000d14146409030b034443c0f0008401c585504a40d655101d0030000c924181c078985010561141035010000302011250808164402d4052807442502d80050510307041591400048030641e0044580b52000c02da89075000c0008191100501c7c01103100b40c0311081d00540c4c0c240010314545611803081c0003c800041800701041c5c0c030400040e08000d400f1109a0360340c2c1d80d400414080c0214205e225050341c41e190580d40c0d6182c22801b2181a1849660140f102904078001c247c0d80b081c0c850140000d02808200329800104c808003540e8820348140f001c0c400b2600e0030340302c60080754040c203400d0b140d40001001981c10990306200d9480a80301c40c1504506102030148041080c1680b805411031001c0b0302ca40c0d55680d03a54103401d41d0700400d11803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 476408992 1250 476407742 476407753
    0xe0d080c090a05060703120f06031502160807080309211909081509060a09150903090504020706020901080c0a0e120f0303010f06031a0f19091d0601090b0a0b130503 72
    0x500e0010881d00c580711104291f10314191003040122150f020301d4007200e03085180c1d00310508001d850740b0029440225140da68800000032100085c1d41341004c1c000450040c10743e80d40300c0c580311860341d060109581030100a4481d80d40c40d90200050b0303809a41c00761110f0403840d104250848420707120100303aa0010a040c0c804c40400411a50b149440b180c4644005030603030f401d5884800700d61040e101d41080c0281079091610003d582c00502e039010f0818a4042d28060103059916000310b0100d9005071070564849400064440e102d58000141c540c00c030506a02091500a80060085c07005190f41c81c0b01e48144030903020350054050401c4203401140780502600d0752940d503852260501461485217001080c10641d22210b06c6207400d40340000f04002a00007664440440c080290034409403c240c640c45400c0c04000c03510702c5481c8240c11924210030210078400c100d050400386050416484028a00d0502000e580301b40c40700005002103031004005580c1301d000010032030b40c050703840e5041079400d072252 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 476410242 1250 476408992 476409007
    0x40e07031e060501140301150f0203130b030106020c0108012702190806031e10022b0c090504050402060a0818010c05130605030702120d09020409150e0d080c090a0506 73
    0xe5611070b2044407400d80f10304e2500e5085502c0403000e800244a5420b901c0e184101c3c007107041b40a260100808445c52050340d18144403901c4100000c1e2140c0c01031015400007100500c1040d4040268844c0c45009081107110b542c0b50144c40240c100140001080501080c01402c4807610a0b4050740e00c000c80c112030610341169408001808210112486407103840341705041d0b40140009a801055000007c01400c0c440b45c240d4201e80c0070f5440f00c0c0b407510030340c0f454501070080b03601d00b42c1100788080d5804a001c2010344003021f0003410540f580c0c00c90f0384942c0c906410301006075140c00440711104901d00342040b480c0d50b05515240d00c0c41070700603003408039420040060302880c0c0c418014207520b0144103600040607210710302250340d40170840303044016a100004d000864005c860280070806034242000c82e12119950115081d500c00e079030102e0304006e0b598030312a006000c0c0d01030842d010510000800c15400b51075402000844094600d0321140c1000464407001c0e110f40c00c0c0c503001f83c8406000707181d0340c442 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 476411492 1250 476410242 476410301
    0x90f020a08011e05010c031106150a090b062d04080a02100c0b071206090c0513061407060b0f180907050a0f06080c1b0a110306010b040e0703 62
    0x1180c0402030001e800200045000d012568288071403002401041c0105400c15005503100c3d80c2d114000d60034461414031184081c102008040d1040c00311002c0d66003400124000e000420190750828a00b180c140b0042004136200c0f802980e0095180b954904013139545144c0040c0c450156400800c2c5203140000d0104809000282540b4910701c207980a008101d20002c046039506850b8100820200e00038000c140007910440ca15650703440c0103400024659504c89141007144c07240745a0002003a0045071003400701d45085030510080031181031007580401c46640155a5104d445402059940e0fa0380c0b0410082d1508056a110541d01420240324107241c0c002d0040001001c50710a0094801e180f40030034241404500041122240303071401c000325052860540e0000c07401080003000380b205002c4410511804610443d00d5a00d1502404c442640b07801d00c801c0c407103050604070307000354000d4004008612504003183d00711107110101c01e510781c4070302c103040b0042d00700c03a0030464460300640ca82030703000d00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 476412742 1250 476411492 476411497
    0x110a11120a030f080c03151e030f0c090604020f0405090a0e030301090203220b0105060c0102130e060312120a09110a1e060206060609010f02120309010204060f1b03030e07090f02 78
    0x803101c1d204d4503803039030301c1001c1610b292108032000700320300c981d00d52149264203229a07070325a01d54002550020034a000d1003c01d10300100144420410f6009402c00e01c510700303011002c9a0401000c0e0740c15031500d60a40445130a030320841c82102d0044543c10000760b681e00143c1d00c041d50004940040e030350340c1d5075280c00703460281d0000c0d43d0341d42d00500010f200300b50410700d9a000c60b4000380d02a002d000c4907843d220810941d600700401001c3e0301d540810110307100c0d8290845000162828440c4201241003c0c020b040c58104140e030b0140700c0c1c40007008030018051078203100036445102c000740415014081d01d03040300c0341d07100c12000c9034102110750b8001c24210401c038020302c40144d0784100d00d1a00c80e6a44000c0b81c0d00c01064030b50f035401c130030108003074210355202d0880c407440c481c3c4c40d004032010f001c01281012501d1303000701c400765160395002c5828800d250303100a60315080003051818400709003071070421884201c0c0e070b82001001d05958503103050320340ca0284040c00040210250410882e4622801c02c0040d5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 476413992 1250 476412742 476412767
    0x20c032d0f030301240f051608130617091b0a180902011b02060301170304030803070c03121e0e01110c01060f0504150b0a0201020d020d020c0607110a11120a03 70
    0x21444903004410744116240c100003510840daa41c2a06c1c41c3c80311005440c84e074003804144c00c808810001c1280403a09840040c4441c60a404888042c20300d40100100184c4000380d64138141203004040c4007081c00005400e40e50a801602044000c80100000843d004107541c00b003072041120b080d20601241031640843c0b1360354000c0c0c0758080540c150303010961041c90300c3d00b002503200c2024030040c00f0389028070266210580004007240d141c151280ca0b641004c0d002110f040c1c1c006611511808201503100000345442d01c0c03030010602520101c110322903030750400a00525281e65170b91214810207002500048101d04d8008030319913807840d00c3c0c9581406820107001e4020f03800a060000191810a840b0b035180e44900703415515011800c00168035900d40c0449068011503400780322190142d01284000c140c40b07840108010703620341603005610b0030510000c2c00003003884070110400c0c901c018007003000c1d0189544291205112101c400004065842e80c00b4058010702c00d030b80d0180205a0403c200030303041c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 476415242 1250 476413992 476414009
    0x90c050402030732070507031704030209010b210c07050f12161a070804150c080610090b03070801030c0b03070504060819052401020c032d0f030301 65
    0x5844200380400e920068031120b000948900c079608410714900280c483d16011040b56880348004001601803940000034107031703600e0300240003c2040280b0003507003210880c1c241d10003504140c80c5400080b400c00c0148191048094000390324003500480c9058110702c801c0c006404110760a260084000603007140d901100c051040300b5841d0100c200001d0610785c4515015021031601c540384085040c00c6030015012a600320a542011100342880713454184510f1503035844003440e252170f003002c412400b04081d00406c05842d1142c0382d0301840c1c0c0000c203180d010300103a1719401017204c4100215a50401584090031161000c003e02c201c8551080009040b02d00447c0c07114855500c8102c1e605080c03205035040404100c0410003002668040e01485600c100e2030045e100d003602d00c410500066a000b260840381030180c3c1500820a094a54403124002e8800e10052085000c4480465511051030f081c00201d80c85682d500ca072010140040d20070200400c01c1070700c2081500f401c00a0b941e410a000d5141d4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 476416492 1250 476415242 476415263
    0xa020f0111010e0723030c0f01110f010b0a0e040308010b0306030c0a080f06061009050904060e061f080102072a03050a0302031306050712031a04090f060c05070b0106110a1509 77
    0xe1030241c028410000d517030010054050844210104080404410741a034103001ea403041c200508030040c00300b10349610310580003145001e0000f0070001203c9190704003031701d002072800c00d200c003081e800320445054031502c0144c80c0d139076103c04000a160000100a41d44c3c00142e448001ca1011070103d01000851000c608890342515a10100080601052a00350000320101c034100601d10700f0700c104a4026000d031000041042c3c440801906012084a07103a18a10380b994980111070341142c01d1348002c01b400300003182002055510540c40300f0707410300b48961408940700842280d001d40710307000700110b5001048488840c7d444c50043c0d1260400302c180c4409560003000021018016021900c1d01680544d05801c040ca44400a034020a0741e050005920305500700c0c24002d41d00d4920650604d140903428010481d416490000159030200c138075441044424003014000a01e101002410344505042420500c446000041d01d49a070300900908101580818964040c50301e6010784011409a52200f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 476417742 1250 476416492 476416529
    0x316110f0616060f290a09060b160206040801020a231213050c0307081b030d0e01081905010306050106020f0c011e12022a010e0a020f0111010e07 64
    0x606000324842c0c48202120310100200042c001c2e40f0088070700600c01c10001d240d09211900161a14034111581001520700300400e00703a20346004010000c1c1407075001400b03640e007084c80c1c1011074055081c064140d003040580342801c546d0355074162000303030460300003c6494000c00c00c00207001e501c0608040c070204018000c1d80d0352043c40001103ca64029041d400401d54132550340c4270761841700c120300a079624011408004a180d80034800a00200356201c000c04035005104088a0100081c040c424070036440410864603164010784181c80b96003003402d105211340d60b5552402c04008084e668400d03103a14020000c020419140e02050584119600f211a00250720300d585540702d04001b159030128025003c0641d8054688400600503006460121161030f1500c4028050303801200400d00c14410041e01406806a01c00c0d50020081005009100c1401c010100c5521019040c4020b401801c8521341801e81cae900520510107580903101c000c000b00702e220980c2d1510340201b03009031880c0c2c018002088 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 476418992 1250 476417742 476417749
    0x2505120102090a03140309031002030702010606020105011d041a04150f092001021e0f0c09070906080c090607200d0b1501030e03040611120408030d09050316110f 71
    0x1c40c040396024088001071804d60311100761700030510103688410b1008101d0010306031000d0051411001c3c03911000f58036401c2151020f801d40c9c5030b0f41c00c21811681342c08010000415200b02c602e10a09418104d0540d0b601c13a820100d20f54a001a540030166003c0000c3c4406c00500c440651500301184104005440e02c20000f0019105040c101901c030b00c4901d03c3e02621800004000d00340158140111000e480d071400c400e449810401e49070403540c0d009181d00006402d000d10800c090a68111550152441d003108050650a02c41c0107940402550400140181c0e07814000c80303030b008800501d1141c84100178039204100e442c4081d00d00c00b205411454032010381c200721307055044181c1c0c06804034009950b100050418401450589410140c9802044081010a100400c0540400da40780d404120380c7e039444514080103110b80801c2c0884c2000100400400401690302d0055040d1000c41c01500ca41401d510358005c5a201280c455810b940d070900b0010b0009401c010400d0a503950041501c1720002c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 476420242 1250 476418992 476418997
    0x7050c2e0c121407060e030d1103040605011502030d020c0c0d0b16031b0c050c041803020607020a02090604090c030818120705010503061c1a06040b0a050319052505120102 75
    0x141480c20b4061000710300040840e04442c0d01b00d050482182c0c10018514000070594104d0500d0b50750384200001404240001070041d140501208800c2482140030710000a50b02e219035099800c0450380854404046513041c0503000008e0001081e101d030100c0c05040005010600703558134690003003200d6040e04420b000740a8040880c920003208002c25455650540c1d00d180c0c200011280d9001c0e0780000e5202d40d680f4404c025140c0300520a080c20359000d464080d103043d2000e0891019903014442e0500140e07280082190f0046080e2004200f40e82f80f890002c4410350b06401c020400c2501080300c10b102002d6103451001702404036501c01d078015100d0301032078a40a507130140e540010780401c0042c9143c2405d40380c541280e02418680d4841072800e03100c1101c001e8440d22555090460f94061020318a001c1c020104003244c211240c0b4540e618080009a4401c12010610000c1d900146440c061010074020b26210706004100112100242440d04404850341d0107006d11408056200450042c014030a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 476421492 1250 476420242 476420267
    0x240b03030409020f04080a1b08061015120c08090106050a030c21050a0b04060c031b030b0d0c0e040b0c0c1b0609100e010305010b07050c2e0c12 63
    0x295107031900780b4428102035846001000088034003000300060060301040b4024901c1e008460211020b46020303501c0740e848029070b004c42465849071040c030113081000c2c4011f008441c1000380c10744e00505c1560b41071355030445003041742107024070303002010440c5a00310707095511804800008000164503081000501d40160101800000d184d40c1e0a0180d4502d2802ca0b25030440d08038105858030030766a43e65890202c7d20341d000c94250140c01c00388020000c0758020301800502c40d00f07041c0b012481840c0d180e140405540002c1080544584181c1c4940e103592500a2103150040e0039465041d03190408070310804000d84003220040c40d031030300040d410490003040c1d4038001305c80e00c050200030380101c18400342500300c000e100e544400100889142a036603a409410000025260b407d02c0280900000d001c440c4d050b0b0002c0c401c94030070002000040d4000c02d004104007802c8510b02c0244e0300c21008100140000c84064240e160200262480c0b6500100c0b8509403074843e0640340d00c1030071150b1048030000d483c1034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 476422742 1250 476421492 476421499
    0x3070807030b0a09030e0604091406040501080c0d02220e0c011803060b06190201050603060601050903030a050310090603050708010e0d080c070512181f080402060d06050904240b 78
    0x10500e001c0f0380742c1009800c640645441708445032508002851980180e0168071901d40c0c42d203146200200d4140810750005049804202d90f6140603042078881c440d40486c01e10a01341c052400085507035003180c803110215411011404602207030030070707170003000e035a0041d1714035110300001101c2c42d42c8a42c284140700030b00700014001c25407440d55003001a2410080290303202d00c00340071700004510b00c4da004920740d0700f09500100385818207000345800d000018100c141003140401aa070016180003003144e000306901e01d8030656136510200200c440b880141c010030b07031150502c1c00010030301800082c6841036598440080201c00d8441440c01e40e9841103034119804211030500003582410800c000d4900d10380500199000107044424400c6036030320104028940c460030000c000c0950409003000c00f444840840d900c07808010031032011b805104004e000a01c15500000c182c00c2440b0680c01c00c00042c14040d100040c00d050503c0e205040d801c08241a40c4807518004180e03001c0b018501500c4200c0340043d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 476423992 1250 476422742 476422763
    0x315040e0a11090c0c0105070509010806030d05180d150506100305101202060c1c1205040503040e06011e0507060b0306131b03020a172e0906060b030f04020307080703 73
    0xb0028411044001000d01d80100e04c01d00c0052410b400a0084034817400c40d070350b255a5500303950f40016010304005409580241e100c14240300c80c1c550804100c1c2c0903445918140d44c1c94141c1903000500c4211188002442500205051400c052541c3c1200340100ca045072500d500c0055408114102d8a08645054002460707540170019500c498202800c0c4a001502d00c9142072100d0484d00c2c5010400842140c0540d14000c1c071660290340403102c025081103040003401641066201c0e16030728040c50083c1074034800c0e03c0003c40c80c5a8010030813071088031407904500c1c20b507848004c00541a1b801030042036801906000720700202d8540400d80750300c00c01031003161050400c12030f16003042d603540b4182c40103400315150401101580e0f503c0080b00c001d000d90580c0000d00b014201c010360600c055800e0040c1c0322400111030a201041c1c9000d41c02c0541d404aa0000d0f00c2542030038680082c06907503120811095002050000b88021002c0c42c46c030990084d41284d090320360300d060f0346555000c80c0c8070140205188 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 476425242 1250 476423992 476424023
    0x51e0705040c09120c2102130b1207030b010509071724060c0304080c0402030f010314070b040e071106150f0f0405010e09011515030f060b0315040e0a 66
    0x2940c00035041002a142c42d8443c2d039100d080d8698550140c030003d650402c1000310401121054551304100d04c1c401003011028007620368041480840c000109051043d1900060003040d01c41107807401d0b8030311245045031407103540da0400445064013030050700d00a60304d050006510300c0c003d00c040052904891181c0c6100c3c0e8454140007401b0001024103040c00071031401d0491a542d442025081c10b0796040c1c051641c652924a40d06d01e0080ca4084480c0214014403c01c0701c0008510034590441c0d810034201c445240c48058054203000a5810800c1d04480210740410584501c9009520a6615483d40c00004400451441d03480204540c500c40c0d54121260041003070030000d41c4062840000390842c121025080700040540c1c4092704103600c0c41c21403508110106109001d130054032110816184035650500050241881520090700300b40758440452821405043d80807070010459610540d4403800c091b824912807a52001d181c40c4503905000080d84403620210701c00e0b4046506c0004040c11644 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 476426492 1250 476425242 476425249
    0x6010e160207050a0f14040b030a150905010f090b070306080c1002030712020102280207091a1509011206120f0c03080d0f11030601020a0305030a0e0f060103051e0705 73
    0x45800d40908502440c000000d8a40f620300b0198040c0101080d41e4070b02500f418600c00090702c00308125482142403004820041e01e02055581d022034100440030f44007410114100003034a400d20f0010001c0d841c295600d500303038000d0f50110070f0f101e2003030486151a4503410320403400c0c7c41e603602851409030401c00c21a030740b41c60807001c03101c140d0410340140c0381004096101c644a064105040d440540d400145189a40c07001c00780c045040d00b1000c030b50225101c0c8203400250380d00500d0050391100d954503c01c040c4540c041d61501421800c00030300010306403c032414001c145811910074640452000d00d550200e4041c85d0045005030381c6125501190200c1d2500c8006d800d00341134000742c801545414002c0040b607a40c5004001d890320440c00482c1003071000c17688800b240c0c12000b5003140c0c55010f10078412a680d000c00c1c0ca00099400d843e180341c480c1c4034090360740d009101c0174680f0b050700c0c070460081184a0002286450480740a40c0075038401d90611205a6442c508a035030001e12508491400d01c603619 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 476427742 1250 476426492 476426521
    0x30801090b0f062a030c0c01080604020c01090f11010c0f020f061201120c090204031104090501060503550614090a110307062c0402070804060f0206010e 67
    0x290010004a000c00c1c0410116610ba44091104001d5202048400c954102e2044c0421504102040298982941409403c0d00c0c0c00c0d90b06c5c0e44904014030180403800b56600c0d5010f0350038000061008002c503c140345080305666840d0740c0300312520380c00d04000c04004c3d03024504410b02203400c03201c000b43c0400d02e9420026040d407000da51540c40300061000118000380305268034083e000300000b80041460508203040b4181c0c059000060241c01084180b0000302004820700340c00d40c0560b80440c2c00c07100d82c6025800740019421003500361207940804001a8401e462414008525801e01c4100c2a0004940c03800603c1e918100c42c019540d2a005100c80c81860300d420b14032a00a02c0700181400c8030b04a28004c04c00b068440b100d640c0d002508520a00c2107441c40d103540400b0480c010404149004805401805400512541c2c0320b0b0045d601d001c0c41007880f400f42014903000f0411982c0309401d14002e0080d03045809400000746000303000414683c0001040c2d4180c9010304c841440640d02c0140c50112072 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 476428992 1250 476427742 476427761
    0x50a0902030414160e010b03041707050709050a0603200a152705210601060516020d060203100e010e0606030403031e020406111204060e030a0c08101803080109 70
    0x34450b00c0540825140b0521211a058600703aa259038601d26000d005c0400d10340607009105207020410620000440740c400a84030390807a01000c80e1204158142142002c429034031961105051408000820849520000a49119003c1d610490b090910182c0c0c01d41e58402c0d540b03400c0303030032408207005050714240c4a05602c2e405142c145071807000030700c034100300703042c40b003690001c00c1d042c92001e001514004604040304580c0020400e13142c200c00290503170300c11042c40341d1814403c0015400100c0340842d00001903003034002d0001180004107151003002503008a864140c8855002400b1079801d600030b0020341240e1200305881d081c0c0d140c030010054294000750084082c1a554440e0b049804000a00c03070010710805040184c44034075242006c2c021564088000407e5086600d88074441040e403010b031400d442880c80e08070861a10a00070a1800c007a40d0b0000d42400091000080d040e000014480c10340c2032075031410b00c0300c6596054502c048000a00005001c00c90010040c411401d542d400309011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 476430242 1250 476428992 476429003
    0x90d0b06060d090b0411091006140f0c0601150c0809060310120f0c140102030304260f0a02160e0a11160804030611070206030a020c0a080a0e0906010504050a09020304 73
    0x1000c070003200741001c40700006011121301002c1d80401007440802e074880380d5000d400303070b907039201510f0100d0100c0c600c0c1d1031a0040800784002c0010a120212002042e0f60920072183e065a5450841e03049041e69420700b480f0341042c4180c1c0241c40701d41c80e882a00c43c42215a4040003407070812a1102c100102034000900c82c2c1a91460704400290603080741841524050080026404840c134a0030309040005964020118008101101c1909664004200ca03807042e0000ea0f40403d1f200d95200c50141c81c0d1906100b40c8803036501007032140413200b800b0300070404402103800701c80c00528258081c00005200307204d05420240c5400016142c280c2c00d40140b2424000b00c0703000c43c5004584d1185014150000310192040c40000c2418001c00200784240c0320340044030700040f410035206030700060f0188001400d42004640106182c107180b6010451200119480002184c94030b00100d40140b20312040c00c4260f119008400100c0e509501541c100d40c181e94015020200342c0b420242040060744c070251003102d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 476431492 1250 476430242 476430247
    0x105040b270d110f03060106170606130303080f070e09041b0e0c0909010e060907200d05031f050f060703020c04020c060f0c130509060d0b010602100c05090d0b0606 72
    0x716a62007500304540c00e4418000045000809024000c0b1020b00c0c01d4024081d902c460010701c410303600701c001c0c01e510b0151100b80c1c21003075903a40c011030740c1070140010b580441d94200c400402016007104505104118040100109a445070350480d40c003113000220365001003408010402050b1b44295680d5160018101e05210725030740d241d42000b020044400c0d00070742801068248d281d107443c004090042604a074014124100000025041030025002a09028205482307014140114550141060b104819076544500c00240541243d0003101c6070b924030040020b00d4090b11014a9200082d40c3c0050215840c5c4420075050000342d501c0b0480680c25031007000350380942a07456000a20340340038400041c000300e0510b01400802141c0140580c0081c040a00c0250302c075100380c880e0402120b0044590a40603101c84010403080c684100740980052042800411001d400045068202c141400c04000080024030210352602410740000c2d84001d01400300e8000c101007002d0745402940040140c1e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 476432742 1250 476431492 476431567
    0x207153b060702010c0314090d18120b07030f140406110c01050c090102010e030322080c1506010f0c170a0203090d030c0c051c060504080f041e050105040b 68
    0x1071800100300c600c840143e454455000c0125403501641401641a402403801c1c0d04102248a848100c2d0441c8601004113400b9800900c043c2c000c1c1d20001014425051005c100550130040c45552040714520040b9040400d1409002700a104038100d03c9030b00075403000c198440d90342c1c40e005066065a8070040250500030300d00713520300c20320819000341c114105460b500e50000c00007a09441c40c107064110250818010040e040c048140010501018100c410141d441146001400d074020244d506203644508440301c041c034510b814009000343c500341c0390340d0302112066500f10b40a0b040328400808105035522400942d111000260a60444a0042d00d040004110200b1950602d114042d00042d0070a201d904c14801581d91030800361005407120403d0010f480119041d10300724183c02030000f51b803070340040c041c41041400d840d40b1003000d021547d500d640d92000715150301d6084408100b450ad5030f0b05d0010703466010314100c90888092400305420400c0c11030b4410f1302c006461102e02e41100d620984c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 476433992 1250 476432742 476432861
    0x90f040510140f01080d1e170c030405010e0d050d05101212030b06070201050906090d080309030403030e03010e07170a02220f0e1c090513020715 64
    0x1451440341e12000040b0b0341c80c015048000101c8181c2c40b91003650030039001c60303200c01c0e80103011509100100c0340008214602060482c0c4418502a002c54030f09404001c0c014800c607100300850045004030000e0041205003c085901d8040e0742148401240041000c226003941c1504a55409003c02804541c0240d0310041281d1104001c10200c60030f009220030a42a5600f610075080444400c0d01d6850500300d503a40044c1491242480c0184184c402241c03c40c40b5980b1111f0855602c0e91010100e9141d00b03180780590360b82d8005000490200e02c2d0502c1c840311600781403041745c1010075040010050145021051000402000049916406043c02d040d0260b191780d1000440c0d80c4580020700c5100c000ca0f400c10084031800320711105201d041c0844003202c4000001c0d0303902c1c1412080140c042c00000000280c515083d00d80c403040d0850000b100300f8807564aa540582000c82c0151048116158080048022550380c0801486000e2140b0344010300f086034000040314a8400340c4100f1400707503864200 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 476435242 1250 476433992 476434001
    0x31b041e0f050402100c050303040803090c03100e100203040809090c0d0510060801050d0f030509040f0e0c0f0114030c03130203010e0c150a0203040506130302060307080f0f06090f040510 82
    0x7014000c40d11031041c0411400c2418241d8400601898030300760340d4045a46240e160f21014001601e05000400401c0d1a100188011114004014211191500400c9951000d00302c41e024464803401056080c41003007006000b124480c03503100762000d190040400802040c0e6401400710694610103100c1c0311206441803050340c0c00342e6050b0304200542881c02500500f4540c0580203075001e464240d84600c0010a070b010810740099040c02d0041d182c4c4254008980103011300c5170801030541c02c3c40514194400c0204092004100c01c2e10f1720b998911030342005407003208070010000380380c02d4100002100e60155a0145400a100030200c00c0c9986454002034292030781101160240d0700080c613a00c1d001c0c42c210108403400507081313072003901341803400e90083c4d10385c000c9124841c0200c400048030f440320074840030560003450340202203640340c1c2000c14004051110884078000c80030031500100e400d02c90804400344c89408020842d1070309944034050b5241c0300b003015004483d24414040a000c442e55039015 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 476436492 1250 476435242 476435261
    0x807121403091504080d1d090402010e0a032406061b061806290a050405040507030501060b0d05010f031e0c050a120201020616020a0f3002010b031b041e 67
    0x9400d844d20f00381090241005000c440060a004512001c4d0424092031081c415004900710b94801441c3d40310300050b24106140d0300e020780c0c4083d00d03500c04020041e220302000505014412816888100d0001000484806024020200c4c00084c4001001c0361134500001c0348522684002c1040300300d400d400070b0402c0d0b4480b812500700342c603039207003000507181c021030b214203071081d101c5110b82c80e4100b902013400c400f154003a040c000c5450300001028800100114401035900200130442295603524a6849800094510b9940c80c01c1600005100b030b560148402520f42048210600042600820300213640c0201c2c111445e00d04132500041959443c1d4989004059481d01504d2070740c1d052000a040c100024100210b0b4445105c03842d200390360000d80c44490b84e5201c103c02500d600d49040c610003850300380d41d40003603060600c0c510600d410003034450007d88051a800170700c05a904041050b4460440276141d00c00f43c034401d0085c441a1525411094121703040748112452a44c2c4080c01d001039849405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 476437742 1250 476436492 476436529
    0x80f07030315032102012702120a0b1e0613020a110f06150114030610020f0a1b151710050301051302180103050601030320150a0501080712140309 64
    0x104402400710314103100c405441103100800005071000034421102400407c030b040c9030043c01901808640761006100f04034060002213070300700341d102d10300400026800c490b01e00488038806140c19042427040c24983c002c0000030018210416000c400f031000350451001401000310900d5407260340d1205011a0303004c41101c0000e40568505070702e0010400f1981c10409040061103034454020303421010030f4a401c09002c0f905440003a410030005c070302d4841c0004410b815406103038554410000202044141d40b8040c110b001d920303560f41d40e030800340003031094015000f0400510596103c2c616410700076034440341d60311408840b0f54952012a0841b601211052200f4004d64100e034250302e414404116007800038150440f0790341c119911180c440d88180720042c203020203401517210448084c610422110f50203000c9a0303500d0201070101040120503070300052a82d24107000441c0501000c17400605880d40003110b03168502c465910b8140c101290808081580403c0c02800540d07650b500c210309442c10000d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 476438848 1106 476437742 476437763
    0x6070f0803092505010201062106090312110903010e012007061407020a170406020d05030c070b090604110102011a0105070510023004080f0703031503 66
    0x445101c20300d4040403441e80051104004148121013003680244030140d5a40382c8424500c0c00c0e40c00007120710b0409031280000ca109030b082203040e40d100740b03070a0311001580203444046510b050102a010000044ea00e000781c502400360b00c4c101d0b20b10070000c2040e00700000002c01007455003004060041e00c0401c5107400d00410303500c82c1054240a00740040f035460300003002074483c094900c00b15a41d0702c28600100115180106580994210b40c0040c000350304040e0301940c464200330480d10054000b00000d00001d01060714250091240c070008004506040c640110703c00012180350f811603162140b40a4524042d40c038030030b0081401e0030f1090f40c48281d4100345040040d1544c2000a942c00069049000d211000285000c090440310500300c6401c091000500024180c03000382076610113000202c035207492940141b640170311900780021003000340c10031035000034203950090b00d003854035 = true := by decide +kernel

theorem cover : BRFrame.Cov 476258992 476438848 := by
  have h0 := BRFrame.cov_init 476258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 476258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 476258992 ≤ n) (h2 : n < 476438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
