-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2421
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:39:56.999+00:00
-- url     : https://prove2.me/submissions/b1937aeb-a0f3-4dee-8024-336518b67280

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 435251798 ≤ n < 435431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 435253048 1250 435251798 435251809
    0x90105010e0d0302011b0903150b0f06071110050901030b0111060c0c030f07050d0813050316020301020d06090506131b0807020712060605010e030c03060114030a1e0b0c0414 76
    0x1182c00c1e000e65583e490480302e042d96011024408080c00e907030301d803006401c0d4a440518101c44e4081d0100451a049420806071128102d039060b45804885041d12482c09141c82c440111174000040d8004c1c0d1102d880d1401a50000302030311451109807824825103070041c0046928483e05c01320181075503c200040b032094008a8028020a10384409817032030040308040c1034480ea80404001c444580c0011100c0134950f5101c3c0354203030404122600c02d098800203899003945d80c040c0184002038120200501c60441d0360960460700c0c104040101803020303a41e15030028000b01800c44241d8068554401a110070842034070135040e00024080d9501c0b001100d03124103c03586580141540c081d480340640c0401c0d000c02080101c20480e100301c0010659501b03000004054060000005029034003e02400c0d04695011404505452480000e4031044001c480020f1500113500700140c4012a41c908440700d80440c650580300080c001c511100703444d120710108207a1481a40700d6142d1080f15510b40b410380749800d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 435254298 1250 435253048 435253069
    0x120a05090a090207211412010801060f0305150601210b0a0503010b1806180406050601030c03021213060b04020f03150603010312050d0207060e1c0e030d0318060e1605090105010e 78
    0x51402e00044850030700d262400340d07c030800242800c14503a00401440409001d044060615045050081803559542c0d640d1810a218840380015400b03001803c980d20500c2080814079140a411107001d07070042c81e0310010302984c2e050314040c042c41d010100c0c1c50700301405400d1070140094110030759200c5101c402050100090300d0503174080d0781701d03c00d54403013500c5d006168050340c042c20001542e400c2280025003114411807204e0f00340342c01405034064050700c04030281d501441c06419034100c0c1342d02d03241c81c0d0014914643d034079601510100d0307250b4055488001961150140b01c000d030031800000e10800c2000d000134800100351070141265400c00522507401343c0440c0c1406140581800440d680300d1090b44c1e0458086d1040d5407201c401d2452007079a41580701e248040508294601c0c41d50308000c02d8039168404005d1081c107803104840c4040c1b0000031011550700b6000b6800300509120802c406464400e02c042c0110181140503000c1482e00c1d00d159402e048507416164104508442d406001c0d14111 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 435255548 1250 435254298 435254363
    0x6020d1d040b03011127061b07090204090b0321090d03121a010216140111070506040303080f09030c060105010e18070f09061e0c0203120a05090a090207 67
    0x700c40c0d107032440c2910240a00780c911001741911075191403851242006010360034040d003500c00c40000c01400035484410880c0e0300d411411a5292010400032082c0d880e040c0141e004079901480081c00007050103130b1341c0c46074000800480036641c3d03005600c0f2a04010102d00e581c1d0090300f0404001c0c80c60145842c00c1e15906061003410112a400703140200c01d4102c4144a5200071400c2c1c01400c030304419a03041c45010b2407800740e82e624005040c00c3c40c5140340e0300441c3c4404103052005044401d16020001c1045030010f10000307203100c0d80c4680301e150003002000c0030340c0c12940360781050010416000011044d034040c898544010011607103004011184460340311001a00201c14a40e400350402d0754041d030038822412511150b103401e02807000100542c0b25039212204101c0040010300c5c42c901f011501907c089421720b0224640005400002d0803c090310310480c4680d000050042d0816401001070701c0da6000031610501e00d20780d80c0500005a21860034000c086911029000b25054010b01d1800320400b0f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 435256798 1250 435255548 435255551
    0x1061514090f0a17070e0c120103060c170405030a020706110a0602070f06021803061005010c08030604110a0f0912150e2814011e020f0f0d0c0906020d1d04 68
    0x6030313120800400501450920340c281c1e0088802031000742807400707200d83c00c10340c00c140103440c003401c036841d074021020103010040c9003584400108031003901c50050a820340c848402c000c00c05080602d030959580c1d00841410000d4023601d4070000c1c105025558440300402800041d0108003942d82d034040003580150011660142c0c000300800100e0b20034806010400c800054985020405208151030090010803504d00c00c58030040a220f81d1368440000c4046a03884002e41d0b881c1d0702c52100150140a010b19040c401d00c2c000310b9501e00543d40311040482580072034844660558541c004901c02d50b4a00002412103a42c420031011a03100562010000b1031402e016905040224a003049030510041200712101c000400320340705200c20704124075040807111000300460744c56040d140c2080124510180012030380400c0c00c503414140d030002c55054000c002c00c0903584079591084000104140e842e900c0c005030388604085031880c0001040d21145a50f522030000d403c1d2680e543c0c3c00d02c00b24100782e654005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 435258048 1250 435256798 435256819
    0xa020307120c1716120c02040f05010815060303161211030a0f080613020a02011d07120b0a090501060f0326091318210c0206091c0b0901061514090f 65
    0x40101401e4803240c0a546c0d96512440d9444c010401a81c9003889100d0a07c0c0c0b03408010088040b0000d40c02405814003401c1c040f940c0d0300c54002a080d801103d9603040b403c2d59406501c1c04000e600c00604003505815142c10441031581380c03506980340206041800440c0035005101d40c1c0d180514059030340088001c240c0d44916090142c3d0308280c0e0042c103007c1025039111050321410303a0960145051403240c01008141b003900c2c100902c0042c100784000641900035580102e105100380d40c1001c0b0308143c02034024402565503040c401c0c1c401200380700c19111200c1410303149814903255403c088110b007003031440604014400d01001000c210100c01c07001e210b551440e82005419002e00341c80f903060300580321004036074000c00310f000c0d0307040f0020402010008600500c0c80141d54960a441f4001c9040d00c0c00355080900b161800005041e10234013400c200d140d1b60401179000340541202c402c0d1031200d0070742844858091000d941c0012404d140340300c031038000c0c81918014105500041700d00035000300350103001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 435259298 1250 435258048 435258053
    0xe1509041a03073218041203050c0307091a0714030309070501090e040b18010509010b010e04090c0e04110d05010903030b0604050f21030a020307120c1716 68
    0x4030340c0c11810801401000d0700429000d03280030f01c00d0340c000b010140c1c088032407002901c0e07180c49418440104401401207800012055403591300f82501c1e070114000d0405094146401c0404031002586600b000280c18103001492485692013900e00868241e211500c1040c144045141150725080106c42c0069050180c0c002042c0020064110b05c01101c0107540e40b820544030b1141001d10b160001418080d019034200141003038801c0d0b050b886a00503400c0c01e415180c0145514441311110b080000940c20041032120050041d800400022001d80761800c83c140758406202c1642e40e030359406001c4420a02c010400140d003511084e40c854420078410500c0c000b0303000003409504450b80240d403585e540342c15080c02c05802d4400c0400a000840300d0314101854440082e01d074044465080d80540c40101d01c0380700710035900b20a212101c603860b050743d032942c0800300025926005440c1c2070352202039003c003d008450168201407002034114407510f00e01c1c0031500040760f5650168595900722040010540702 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 435260548 1250 435259298 435259301
    0xe0f010e0f040f39020607021009020f12012421140607090303090b040506031839060405011b030e0a0f0303021b0307090c030b0405040b010e09030a0e150904 69
    0x180d80d07404004c3d8401010700e5141c0240b480c2c41ca03a038005e5502800511900580000390800503880710f401c0810021317010310125600b0341d16070683c03e4001ca0400740000c070b9002c064210254581416840a000010800410980e002140b0404c1c440071071110140807118800000d4058050003603802c280d00040305a4100d00d021001c641280000302203203c03d000b019400392130a002050360504440c1410308180001d00e861202900301c2c01d11088580344609000b03001d0051102c0081c0180d0000100701e42d03074250780c00c00345a04450001d1040c00c0403003121140703400401c1c0c40640f01c06949160840104a10045040d0341000d002d03000d02c00f2030010324141c3d554699520020707140a1040ca0031140c61450040e01d00000a07880c10200703817250741c030f4449940b00010514102c443c00180480c00c4444968190014140300032002c0d0024240800c00090040c000c5699040366009030741c0d10b08503038840c40d519840b0701072000080d00207100102ca44540e4a4400e2501000b4110b461000c0c0c40c2c040d90400080 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 435261798 1250 435260548 435260591
    0x71b0228180903021c0f08040524010f0f030807020f03030d020c0d080f0f0c030709090f0207050705010206040f260c06010501110d1e090302100e0f010e0f040f 70
    0x8034441d484482d45401c0590600c0080303180e181e04103c0e880da88100f2035000e0485a80544c40d00c0411071511700150901c03030104071080080840c005842c2100c9074410032244c0300c400034015646c0003583c980d400510320703400590175400c0300c2d08007541f50706091a80d8200000c80c074400000700e526100512515400c08000d2000b0001240d0403c020040240005005806401c0c000c0c02480c1c821521005c0280f98070310880000e5001c085041c447d603503a60740d441e0030b4815012a4011a20591a04c400b200f20003910f0f40c01440c009020301c0c21100781556507001260780300303800c4034020006144102410f00161046c1a041448e641c1c2c051039120100908081c0c0d0103036000041003010580c0000010031095030003d946040c13420404015004030300c0551806060070241110a89030b4860302c003002448c4911920300b0801440d8010a480b8030b0b5910004000c01584400d46114460b501c00500c04d2070700d60060711085a0040090111542100820100002402c0d1944a000301c5c0e40c40310148204aa201074620 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 435263048 1250 435261798 435261839
    0x711040905031e03100b0901050a082205070f14010c060905010207080f0702090c04060c030804060e07180510030309030609110a1215230907150305071b0228 69
    0x43e40c0303e03c0d007042039603031102d00c981c890300c48500100148009a6844021181007824905003031206868110501d842a08000c3d0b45020b20300c451010101081004540c4004680148800d86029501c5541000c82c00384e47d248014081428001d201d000544980c210a0344d00f1f008100040c20a252903c0d4076145038054090340625020000340c1100314606400d40c243c200031040c19280c201401c0100203046002c20040c05000d0061a9000600f0004140c112408500b030b0380d4255211243c2e03844001c0c032070406400c4041901360402000840741200c1d8000c96049a8050342c402d01020f241d0b441d004010107800b0f10030348600701c0c261100c0a035500d0700d4a404000f48505100b00c1240403081c01c00383d0504404048142841d0b041c15801c0081e6042d00514500780c025110010a0f180c6030b06540e14034107219036100c0c20880640e0065101c03a15019032000f07200b25001c0d2601c0c800b2090f5001c2030100c0104030348001303501c0b0100541c040041c881c13250b198019081e0a1003074070351380b944800c100c64020320800801e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 435264298 1250 435263048 435263107
    0x10806090403112d0109020f0105090316030f02180603060c211f0e060d170c1f0b090613110906072a08070303440903071104090503 58
    0xb03042c19444001414200341443c41300030032901c2a10350010328034002c1e020a00c1d0400c40045442a01c40d941403114548050318080c00980f45942d07031510203241401d60703005a104d070310b6002010148032194244180b050700020050901d903911410b494200d50490340152034106040100002040d640e100806d004401410100101a501005030007045040b904185406100385c0240b00d215207070780c6100c3c000355030700c0744810600c1c40890400405034080d0440240040c41030322690302e01e4101c0451905203200a005083c013010300e2600034060304110a9680e0b940100c1858462861040300303601c01143c011100401601c1c203d03c4100090194001860a43e951508042680101c0040c400c580c071400b2a41c10004403101c1ca8a074217107450700a540310280501c034001c4000c903180c1e10500c81c2513101d030002031580300400020740c8650a04100740784144a40c0f40c4203401040103982c0000c03e85002503800540b0301406c044000a00c0017034105240704403414407080c088008a050380000142509218128 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 435265548 1250 435264298 435264343
    0x70801030f06320a0c20031207080402180403050a0f02070503070609090b0906060f0d020403063806041205150c0c010c050406080c070212030a0f02011a01080609040311 74
    0x2003880d103205002e0450010540382400529000d600400c0e9034901c10170b18401c2640c00640c070404542184038035a18100040c12350810440d00325009103083c1c0c0114001c1e0b50350754002c2081d400140b411141600c0c040c020030410f20003507078624840c0e180070f00d05502e0b51064070212a0b030340002c20701e40892500000c0101e40402c0302802022401e100d0304603030000440d041d0b400741c1000c10200d65a841017083c05100d414000516084805483d0101c9001f940c4c000c3d400c10111109802c1c00c1550030340f9000780390003407a00381c0c40b40c030100117180806040004001c00b041c0c41e2600e0000134046100405600f11158020031340c81c185452012000b0a200ba100003010750351b0bc1e074103441042d084440400c440c8080c00b07810b10081c41860350000060b80e001142c6499aa91080680002500d9642080c10700d070891100080e0031501950000040084e140d80790003d00420241e550f5502829201c00302a40c00140d507a00064002d2800452032070b0440d0081c1800c1c4207a5045202040c2070a000000c0c0929074881d051 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 435266798 1250 435265548 435265631
    0x306130b091f090b1f03031211030c0405040b15091e09070305070f05070b22020d030e011205040210140705011b0e030d020c0f0a0905101409070801030f06 68
    0x801517008485a1010710b00404080110300c0416030740c003001e000c100417400c0b1800ca6100c00e900c01c0301940381d0809295100d00c4d107a07001d0850703903001c2c0c06554040c505040700c000003401e001d180900b00c4023201504130309200d00902400a03001d0001050316680400102001d02600c038400d28a0248500c0d940206091170b1401d005440034a0088000e810050b080010340d010030080921282c0040f030001101424081c05580d40d200c2c518143c3d8040e61102680e22917100701034101c0c0d40c15090710000e890351041c600c90014034004540b001c5402a400480301411f00800f0b0344034400c0c40140480040390a4101b99068550b603084550f4811703c000019003e84440c0e500c82d80003062446100790460040c6100c0d003c008009486000032000e040c002c941141d428886561007005550142218903010880740c68400e00c0a00701c0c140500c100c0900c3e078181c09420035141080b003000d61040c610340c2c0b5464207030391035550b540e896504410b20944419035501030809240c0a6030000d00244a015903000d5070384103895 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 435268048 1250 435266798 435266813
    0xd0f060207020f03030a05030c0304033533010311030a05010302010e060a0f0f11010222060201020405010906141b010b0910080c01050306030102040906081b0306130b091f09 76
    0x3d0804a219620a1082d80d034525480402c40740d0000028002544035201e914090b18060503e84481c41450140c00b000400014642c801c45600d42c1c103c0c0034000941c0301c0a0410919400308501091516082203040842c0703d1004c5820206540c180340011340e0404492004980d0340041c0c0d00d50401a450b40010420f41d81e010000c0000c1c45000c8901500e01810303088007808420305030200005000c02c9144442c2050f01442010002025140c001c2d0b585100e90502c240c1c0c40d03c011410080c04152992020507154414400d60b002d4550607103a405030f80d0300b000c1d0f0644d51000400c1010381c0a03d400c04c0045500e20011180a060515800002c0f0325419840b0030131010440c01841e0f00640450400b040180b0040000c1d00122000e003030a184d992910340358003080c0a441103400000c1200d003000350004080b400041c41010b212110269070a907410803901301a01c401e41522903c0892450785407072070108190b41c140315041450348040b2080e01d42c45080130001404076441d0300030a55900c4100d2424000d41e0f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 435269298 1250 435268048 435268069
    0x1a03061e0907050105031f03021309060516020607080a020c031216031b0309020d050f070807060c030e04020a0203130b4302270a1113140d0f06020702 66
    0x9620207000d82600f400002061404002c21004007008110b0303503040140114050000039580280401403803000d19072911003d0104843d044413054549800504003000e1070010904411596000d03140d0b640312070504032592031000d08040782c015400c04c102200c0004c2080202480844210101490b2801e0001c1d0314403251400d40402c1807508043c500c514007207003022400f5100300c003070a00144403140307400416034020860030014114443c1d44a100708024000070f00c0301c100d400c404201c0322038a456810468060031800802000b01d030400142020714580b03500a0101d140d941d104590400010550382255038a00f54462806e9800c001020401a140c650b018081c200305d0558000c0041031001c204c0410a11480c2d8024003240507405002c03c40d0b0b91101d80748605003440b061084441500e101c080d80001d801e50304e51401600d032900b485ea112042900340d84801a038008180011498a1404140d442e03644202951201d80c02550320006042d6040408045e4010100161a101e2a10501410040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 435270548 1250 435269298 435269311
    0x901090606150f1209080301090b0a23090c0c0a060f051f0306090303150602150f0f060f150d1e060f120807020d03020609010b011806031a03061e 64
    0x120401402541070f0890325030041105585041381303015940da044a40141140c03103004000e02800400000c2500b008d8214070b502280448010741110fa40c0c0d031145550068085040d0b0901c0b20726103032441e0710b182c4030004540c015203408402d03140003031000606090001e81d07501100c066a64001c0083d41003021310800303920500c91110641d0151142480700d0301860240300007003215484032404010544030b9000802e0442c200c0c0c080000315916068065254903a01c404114a0444640040c25004800e00054000d003010010300303003103484032000c4c44420003440601540003600d20f00080c1e50300100d0f000914040d012007000040e0940b0042c8141f40303400b15a4402042c283c207018041c07240851000701041120601000d41ca0050076506d0308683e24002d40401039440300106800388103041e00458080d210f41c414400801484402a00544800520a0410b0300845078158103008042c000e6012200c2440c07582c01117001500c2850003e032502c142114079400c0e041c1d1807040b101400071504119a00a030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 435271798 1250 435270548 435270569
    0x10c080c03060a1e120c14010305040209070305040f0506100602070e0405030a0c15090f0b1b1606023001060207141e030d05180306040203030a0e180901090606 70
    0x40040004043c00f44901a0341308000707915140c5150300d000c00790120001c3c603060080c4105110f042c02c01d0045e060a51041364041415401c001c10b81f0340c400d2066602c942d60051107141c86890340401240105401002140c0070082c103c0c00f44081541005024403c500b04440f000f05e0608110000382003c5c1d192f800305078480811401e00000920200944020340c0c0700345002c000c14007243c10491082008022846089032400321881c080c4410b041070420498000c0f42401400d4941c113001c0b442d81e041214503c40b041d4018000d014180d0500e44901d5005800b8131405800c10303614407108250002e000240c5100083c800c0302c140303460081c000065004000c24005042c1451624440e440804000740403244590241c00224100c03004601918920000c00f80803070b110402610300c05800c0c0e030f20a00c801d11512441c0c444d0141145400145c0c94070895002c1c0155040c0090030a0540b21314400e000c2181d405200945206100e4162604842c469030414001041140303040c10a10202c80b0703542c12425500c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 435273048 1250 435271798 435271801
    0x3030222080708061005040507120c1e0e0109060518040e0a29071404030812040203071205030d02030406021b030d05010918031103221a0301210c0b0c010c080c03 71
    0x11100b2031781180440300700307036804641a038410301d0072076011840c00709100f0354500e032100d03803a40c1c20b07400302c40d0700f2420b040402039a950382030440041c1e40d2448164600c40c005041542d00b8030a451250010708186451342501c0b0303817810320090004007031701c680780f0f42400d4075444004080709100c4020420080c1c0c2c2103044070748203020700284147c0c0351203400525803800c0c0100400c0d0340c030b000c0c080c04040783d0003903411017131a588071000920398900c07403a800c0e1030030b83c400d1240745800320f507aa402c5071803000300320750050040d45415591544c0502a400090003aa041c6509000302c1c1c03000401d0007005030541409a01544d55001e80d801524202c61043c1c20a0075510300d0183e4000340c501340d40052000b03031901410a820031240e220312070351451140c503640c4070110011403042c15402c0804034086054968051109084030758a40c00d81d00303d80824418503100e40c40301c06a000101012820f02c0c1c00d201c0c040d55401140c0ca403140b154415a520130a10281c0c81d80d500c0e15682c2607070b94403040054000c421050001e245 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 435274298 1250 435273048 435273061
    0xa18050307060228020c01020c031c18030804150305010e04020117040f120c0c0806130f0311120d0e06071409030c090a0c11030301210303022208070806 67
    0x40c1d0086100003441c0341d60001e060a808011319480349000025440041300f0b12400130002515030304800031341405403051f0010300c0664038001ca01e031a110ba552000c000c10800b41400704481840b440890900c0148a0300c4000c030101d24054020005003180c400051030f5203003965001000c4402c140d02c2a00a01d62070300a103c0140c2e4030250054400790745068007806500d0707908245c01c040d110450010203500740354605d02500360704031a049003618058046100c0d01682e804120b0745904e4215003500c0e401c0d601e106850f0004280043e0345800718041d1800c20101c01e40a40ca0a103002014402e02501e03003030224072802142114002c0c250440b003c80f002e0000c50420b4a0064102001c18146a115403404a07805500e51805c200440500b2001001d05080d400d0001d18200101600303914240000c60b480750808a0000020403203040359150f503180902e445030802ea25800014400301201056000c01c28440200568003aa15520f20040c441940701d40c5050307040f0b8074101403607100c00025080581004039 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 435275548 1250 435274298 435274303
    0x30d0c0506010e0a0e0703030e12010b281d04060606030b10050c0a0c030803040b06090c0306060706020c0115060e0a05210c03060903070308071103030a0f0f0c03050a1805 75
    0x445064014040b82c54558840d100007905e03100040d0409441165000028598804900c1c1003d0606486040341c0541d83c100c0a401d86001500c0244c00851321081c946a00c00700e0340d5224407100700e01c46003203c6140c840c0c1404c0c64140310700040070324400d4103c0502081c041944181d03030003450742d0b00f01000305d42c16200104005ca40010158020304c000450f0008000c0000c1c442240d6160b8130011103400300381c0320300d4000866002030700d051380c446407008000780c954102840c0050013040340e0039111382075a44410400410341e015913003c50380c85800340502c0380103c0d000d001d4160300c0c044c40304800c10701c0bc0c10184000e010840002042e8460104100100466110092491568030b403480d040102040f208000c2c9140100d00b45801e03800d480f0b220200150740c0c40100c00341000d40c1c0700b0344d03c0c03001c01d031208442200c01211030a4100c08680082001ca021010281e0010400114519000c500ba09050380140c044600081322040807079150070400030441e900f031241e8216038182e1409016000f1854a0b8582d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 435276798 1250 435275548 435275551
    0x13020a0e0d030201111c110406020a06020715050411030d051815040308071a10060e040e070b03010f061101060f0b070f0c030804030203010f0e0d03090212030703030b030d0c0506 78
    0x901801e903401c81c240915100390041e5801d0818048225a101c2642455055241464152603081480d210b000052070680c0300031602140c20550082540010603101d41000b0f41c0018411a13811044c023000b081c6280d154080c80348103d0250002c803581075000360a05040c0700340100b00c01c0410008201103030402240110840f10b100f8203440d035052031100100403200902c1142c2000c0c1240c48082810410845000000e41524072401034a540640f510349040003058400e018040101d00000030081c07403418160702c01d555001c1d103202200c4a15a42d000e040d03081d80d2083c0c0080c4500005003005108864104001c201404600e4000704811440d000581c4221590b0b4000c03940013880000b01502840203452104003d207400049259246540c1d281c144602d50251000328081d50a04903000b04c03101c00c51140440e65402d444c0a083c200c108510101c00174454001d0403640448503200e000f207500d00820103400300701c0c031940380001c90344c1c01c0c18101403810100382c0c002d504005100b06030b90001080400c046 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 435278048 1250 435276798 435276827
    0x5060118061b17130905010b120a0917130503161214060709090e060601120b0a1d04020306130f080927040b0606040e0103081e0d060513020a 62
    0x1500700c0e1108a020b0007004400040034208401c000c541a44055600c0010002010218a03190603143da540b134240903a0001d10641d94560010710101c7d00d01d01400d0b0740c0070780c0300724038410000350f8a04650310014922000030f248140ea40b0080b410381d06030400207665002810045008110078000702d05955445d40d101c0c011240032400b0340303a0820030460174901514806100c3c600b504d0350b51800c0c25008100c211144a0048203c2c144001405640b4002c03d07914042c2d40103a482c2d0006041413002c5501078060b404005420406013100000c4000c2c0c0082040380741e5450306c000c0c10b0759040c2030041500c2d008010700a84032405107000c202c1d00003200301100041240d88681125100d1500350001012203607031424410072505e482d00340703c00c4160101e502500c1217106540e01119511044d05000e024000e0b8024242c840041c0001413001c03803056409003020305403008030065102c802c80c850440329007240058000079501c0301000d102e1071070501421901040000c204500300807260500801400c0d0f4032551 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 435279298 1250 435278048 435278057
    0x1107020d0201110f10060b040e1f08101505062104110604060c0c0806090309010302030a021b0703030207090203040f12020a02060310050a05240a090e0a0204090506011806 75
    0x261000c590041c44030104407406841038501051340c0d8282c164440b14000c5035041100d00d0901d01003034600b6080190303426900496560106c5560b40143e40c0da00802500b402c40c1030444001c800241c1e410100801c1c490310990203804240e04003040b010003051074068002510130070080c0508110814070034181c0c10404000c1340400039507200c40c204007000d8410300442d81c0d00f041c000580840c260750480c030182c12280c800c011f5103c00c5c0780c1d25500513841d21020798400306981c000b00a5005550702c44e4011b15003003140944010f00e0b28030090340504460000c3e18007410301d504621001c00a25070184800300041c12550b8080d481d503d01a5103c880d880740c107450041500321400701a8541a00c2000301c000e0f11030380540f41c1a0f507810403284200161a80740b16440c488c0380c2d51000840c4900302a12200420314140c000440000300b03040e91101d0070781150500b4000c00c00000c0000642a10040750b139401102e0310440141e5881c00c091000090b298010f200c00c1c1803100e1812a0900c6440c5840180e00300c50481ca007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 435280548 1250 435279298 435279319
    0xa1d04060905060103030f0210050103031e0203090a24020d0e040903020a0b040605091b0d112d0f0402090d11032d1504050601062303040b19110702 65
    0xd01030028100910054043d02c01c8400200405800051101c902030a503000c4450036000304d002081582c01c00d010080000706542628a204a855240c05082014900589040250300000b10350203580e0340c3c1c400001103508000c48081c2f211042c206d0502c0c01d11610141060b09810000905919240600180182d94400c0f400040c54400d0100ba603040e948028080319508042c00c0c1a0701030041642d04406034001c500d0500001c4205814010700400007900c2c150101c0c8d250b842c0d414104900040c1184c00010f03a20002d606104002c0c500d04001081c3c0c2008c1d14440c00c0a02880305982c1410401801144104140c2c549583d8084801d8203203540000388000030810780c1c000c01c2c2000204202001c4044130140e05150010030482c0c50061280d07240b08581d5007170b021484036070390f41800341c6000c0e11540080b80140318640c0302d48034070346082096074050303800c17002c0e0b820b0101e94540c0103c2d02500c003035003c0000d02c650720b22507800458040c40d5904040c046501d000c98520179510440c2c070005d12411051a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 435281798 1250 435280548 435280553
    0x21b24071d0f0f04020a030501031101030c0e1c0510140109060503030714010204050604230306071b0c0510080a0501061107052211180405100506071a09030d0b0a1d04 73
    0x140d01c4040c14018100707541b540360240000d03001d060203000c126a44202c800414070954441c2c0f043c80608407080d88e4280d031801d00802400b8001b0529011000740d03038480d036a1800410070410404681400c2d0180019055418441d821450407041c0c02866110742004c0d0b0410040e41c002059810281d044001a90300180160106009114a0b80400e81202c40031400003643c0c000840f1055603040e50259401c05280740608141d1201400c81c0d401020801c80620a4074400306800e000142a101d0030460803400d89550000340c40f1801004404006003e0400b0000c0b2808a401000d004001a0034043c0080c0e5140d1070303c42c0c54889070302440c0d01420083c51311001200500e12221254000c40900b00030340c003160708040482d81c0c040700c0241c1540302a90081c160906140c81020301c82c0a00b84442540c403410b00341001a5540003000a55007400405400802052501c1c54140918084801117940d684072a038490161101c10f80b6842c0305071000501040440507030a0117522664509841c1c030745036551403 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 435283048 1250 435281798 435281809
    0x3050709050405090a051501030b010e04030e030a060524031e2a0a0e0402030327030714130204030b0a0207030c0807030513140310021b24071d0f 64
    0x641c04141c0c4039051405004071800e01296402d4140e00500640307030302d91113401810301114400c0c40010b02c01850303c001086001c0f691020b00d80c11a210303207004a5840b0b04100020b203001da003810180e4801e661136080c0f1a0196420828100180511541420761051100000c2c1c507120700117140c1d41600d00d81240800c00d84401c0c0009842c070012404071001101c0c8001c12500034803403244940e03000700f418035004501c8000b1801c156105941c0200198601042001051080c5100e40c40e040750360203800b644d4000f2550284456000b410203040143c00700a0154100301030b003207031481022030b810310400013400420501c8141e01c0e07000c4185400543d584603c1d241c1114491009040038096420208054041550040003030203410345c651401c0c0d04e95a1903030500c0380c4a091170f80e030082e40f5500006003070841d421550040c10044011103000520351801c80b00b11400c0090440d8100c1d80d10000c0c6241c0142c0006640850303400001514240000031401ea16800250000014161141421050700b00580e03482 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 435284298 1250 435283048 435283067
    0x504050a0b22050102030a0c0c120e040f0912081308071403160b0105090c16331d0a0201140904061d1b0a0c1412031e0a0615030507 58
    0xc0300c0b21400d600046041c41d500035003069448224441c1418001402d561203040032014158102d061180803441000054800070012030070300d0303001a00d03007403140356a13280c6105400c00b81c1d015151486c1c000a800070028810308005080c83c031002216207110340072800301c005079507803d80d20010a2074680a190a06480c5004000e10f1131101c9994050440070800c0010300e6034121041910500c040d038540711040d1074076018141580c5c61000d0002000001324841d010704140c2c480d030900c428189041e4400d03210940050314183c1c1041d194482d542104404803000603803005580c04400340c444c00c010790b40020054822042240b00f042c4020640e40b0166880b80c0c8031200034602e10680400003900c008010010410442d03600310f0f8140000f140d00000540d003000c43d90003c140e80d807260001400303503558040700000742c1c03081c0d411803050035900c4021120b4800114003c040e16011010020803501c61a04d010500901c550b40f81e6007420307010807402c1030000f14000420030f0741c00d001c203059a40b07070402c0b14402071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 435285548 1250 435284298 435284341
    0x2130b04020313120c030f2133080309011218060c082a0708040305010c03061703040b03010b090d1b09061d0a0905030d1a0f040504050a0b 61
    0xc00014410450050b60000c40a030348513440c010440f010764a0207032070440031010064045510807048590082c0f140090854205d110010015452600040300040710204c011703801200451350700c01085070071b0f808821001c001d024403807450482c0c1080c85041d04c9010710390600c3c1c10f00c05403210b0315483d5969030700509a09007003000c5c000c000c95603900b07000c000307049440185004100e80801040080c0030310a401c01001c1c501c60f03402ea079400d5003501c00884952281100b55103e050034000400091001c1c01040c260801c25a0003140780d5040000315020401e22007201c04d060741c4208010010b901400d4152411900807840181e1601941d00c0400e24034862400014984100b003210320340a458202c0c080401d568440c1e108010040c0c980a40745440d022059031101801c0f060000504114120380144088910810a0340d0510100e000d00c030f0152110f55880da0b1040200341410404d5003814541001d240c0c10441c1c0500050520b074555948038044040c0140c0030951000c001900c0d083d00e41c00401c0001c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 435286798 1250 435285548 435285551
    0x105030601020a0f050a030f0e090117070302090a0e01060b0703170604020903010905011b0914090a1d03071502070b040f02060f0f0903070f06080c070c0b030103080c0f0d0c02130b04 80
    0xc4c43c0c0390854a99070b103a401100429101c06d0302c1086584220840400050301800074129a401c054403401490450600c01055110754000440161141c07007510b8080d04c1e488601280d500c4480800b02d007034801a410401000c02c0510045020942c040c190544c0030781d420150751a43d803120380101d0702a1050b80c3d1301a425600f000c05c00e0007007020541c40b00016118818009000c282031203400c5031240381d42c1c41008001d164080341c004640c5464808140c0001521100003519174020340c1010081d40c413040c0f5001c0a41000c2a440305100c9203003000103c1c1d81e0055011840c0100e01d41c1e131800384204c064030143c0040342074250783e011034031000c04442c003000c40450f8440e190504c4100f40811940000c041500a000fa020000351403142007102c00c5c15201240c40c0c000303166403941c001c0145a00314581c2502c011b51043e1002412000440045029600403040240c0e00c90504000c82e16045510302502c401d41d1081000e07000066010ba032495940794100e512440c0000400003000141c480303c403e40e135009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 435288048 1250 435286798 435286823
    0x50105061e0901350f0105030a03110f0a03090f05101d01020f0609011d0d0c0b040c030f08030601020105090d05030a0207050f01050c040e0903192f010c0225050105030601020a 77
    0xd80d41030300e001004411140b244c900703940c409920081c402000e114940d0154003188040300001c3c0661456400c4851140440720009000c9a401c2d18001c641041980890303c2e1941c203000e1004900101800381c801a5448008012950341c010510040e902201c041340a159030342c5a8241c0c0700717101008400816108460700760a12020650003001c004910480f04d03003d41c45042070307411010582c1c8140041d1515840319401d8561076000206e10010001c8844400c80d210201c0091501804c9040c0c2e00d00a225660312490010006821140045c04001e1254450700b5035500710382c1e1050440382d00503000007001d40c5486887c582945004000301030700a182d401c02d820040310b8005140904121018440300c0c000e80e84034540d40613102d00c506000e01e89040d10116400030102d0080c89002a221341c480042c00c40f114034209040f0790300b0415a4840352594548222a4040c0d40c10404200c1c1c0425050304907803208056480c204603d00300d44122030603c60003100141c50f6078000d00c82c5581103600420041e541d07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 435289298 1250 435288048 435288107
    0x4060f0e0406170c04180201081b07060507030b010e03070b0d0f061e15020604030c0f0203030315031608060a1d1207020a09020f160c080a1104050105061e0901 70
    0x80b4a0f51000030340c1c0500c905060101c01e45014010350000465280780c0b0407441e105900116003a08004004c1252001c4200c5a00c2070a100c0000a1a00074098640000c0e903042c40c08004003520034481c2d41a0400602c01d02d0000c850380c01291120031910700898132640c49250b4840c04001c1c203140030140040d94580540020900e0f060402110002003042c202c601281e2030303070480c00003990b6030076000b401a800000020300190240c3c14a0502078050741d91103015810b030340c4c0000e295078401c441c2c0a000c140d4050301c111003410200508401c400d03030132200604040c00d10041540d220030040c208001140c40d95420b0044900c0e0841c1040d024400b01b06035075147d28a90b204181c02d5004840480c02080d00034400a14902a4820b4442d14040d0300740491034032200030400144020400010380303600300343d03140005450f0010400310080a104e50310000400044408220071580f059101c903005100c1042504080c520340c00c3c0281c9200d800300c41c0c8648a60440004841c0c642c0f6000000f040852803448034075a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 435290548 1250 435289298 435289319
    0x1104030c030213020705100c020a06060b090a300602090a06080f010f05060a0f02250e15010c080c19030c2a0b0a0509040501030f0507061404060f0e0406 67
    0x2503a0003070f2502014015080258030891156101c05041500700e4000c0905080e050707088041020510302c1207541643c9903494030300072148a5802100946000100e0b810142003801c0d440c8020000394294485940543c0006400210a15903259404840401000812a03a13905039a003804000c0c11241c511a181c035009049103105940c1d040050031240300005500e501c0489150a0b50030241c441800c0c016210000d407880c101c100320301c6080d8001d21181c0d4a000d146100d1826803a1038081e052208185481414884044068144600c20540d00c107611020f9801030110111258090b010f01d9890911301e1402d8200141a2500d20b1540090341105c01810303800540031440701d0040b41c65650f8114203038040d804c1384414288101c018083c08008001c81400070018141c15207990415070b20344803115000804031034090b00202d9078603401d2158601408010401a4050080c6080c0942c10140c0c0f4040c6410714042d502c130b0300703080000d1220001c5e04c00d031148240032080c01c0064024040d0f00c1e100c812111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 435291798 1250 435290548 435290573
    0x201180305010c1b1e2a14040504020a05010e061306030b09150f04050912030c0c060c0f030a0504060e0f0105040204050c041d070c0c06020a050d09150c06110403 71
    0xb000526400000e1488000007003501400303c0c0d101e0722042e00c41340c00c42c44000740c8245441c021b0703070b15102449040044400c00d61070381e10f59140001041103142d05001030500400d07900003001e0f000307528104c2000016100d04a0081c1903030402d00380040e40b450444005a003500c0781018844000802c500c0004005805030009005440f08403540010340c0c1c0c070300100421034070381ca00d442e03640000a404840c096042c198050f581040821040c0c64200610b144540c0980d4000d80312514640400500701e00044414006e10b034000708260180c1d8540361402c0c030180c5407400007600d0224540d41d1140410204903041d4003558922958070151060014180c0c031960003803500f140c2c1a80210300340000039411000d00b40840d020ba450303e5620031075404e4007804160b42444d001349002c052219104880011401d4031800c44010300355a40103040000305842c1503800c0c11150300348802406808841884602d110300c4041c02c0e151024500169411402c0c10140d0240c5013844041a29000000d0080240a207840044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 435293048 1250 435291798 435291821
    0x1e2d03040b040603110a02060a0908190806030724050a02190605041104020307020a110a030b010e150f0d1509062301080307050c120c030313050f04060e0112020118030501 75
    0x7080204c00800d0600110701c14030354806c0050300310340005184243d007035102e200071501900040341031000c09146010801040342400d000700300500e0403c001450b0070072608016194070104801111340c2c0003801d13400b034566138040d1000d003c40403407002003062080003281d0760700584000320b0080340e000c1c1c101a4000c2005039026503c4e405408628505030606008482c0580407960003861924280c3c1c65114039600c4051810b0780c424508040040812032581e60140a8040000c001145040000a04045052890656008120a00c6d501c04a03a94401c00281180d4019918402404040c0ca0420042c4003980000340100c1c41c000d40c807905040d040004e0800015940901141d50362140c412550360302411900034050b5001c0c4e088180c7c02e052034460300309601b030f0900494802111180010b41981c2005590b072660743c0400c80708011910b8462408041c02c14213440c02c0100038101501d41032240d905004400800c81102020811a442504c190341422140613154442c69240d20308a4040c02c84407008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 435294298 1250 435293048 435293051
    0xb040501030c0e0109050418120201050702060a0605060702090a0f1d0d030501050904020f061c090c0510090b090a08030403050105100b0f2a01020a030507021e2d03040b040603 77
    0x1100b15140901e0508030583c0341615400b1056141008210150440d410b4810020761174080500c005108043c91494008958001040318500050700030301e0182d005100c02261410028104110340303501e000c80340c0c59501610402c2c1c0c551b032511514000345c030404d50300700b102500c1c01413410b0940070740c0082e40c070661103100107076400d0011a000071410b80b0f1080c09051350003ea090701080051800a05113415450040e01690501919074421102c030302c20494418401c64860554004100d02004200050107003114007110003150340f10018403210701070199001040300000c05150a40d101c1c10260020083d4204495407070380c03030b8030308180030740015520400100301d806130105545c44120f068035030003034080085c17034102105841c504d81c0c0d0280c0600b05c40d0b00061400d1400d5513895081c001009404243d0300c000c242c038200030900901c0c001c0d0021540d00c08994103141c1340e003030000200300c0d40b1b0400702c040c101404003000b2105003604024100e141c9400c82c8000075000a01d40e131010040c01c1182c045440 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 435295548 1250 435294298 435294311
    0x1090b0103021210150f08010b0a1b0b0105150708030a050411031f0b01020304080d050d0f090602030403090506090f010c0218041a0a0b060a0302031f061112070506160215010b04050103 81
    0x41546d0984210441002182c1e0b1100107008412440001c1d0440c08598504206900c00011400d6200b0403000020b81e540d215003401071059040c036411454071001214450752500c1c4d01a00c40c601e5601000c2c007074001540d1242e000c1400c1c8204041a1454120000d0a0b160442c00d9000100190410b200f854031344030f401d15802102d907600203c140c0742203ca4010180034140c10440e422070310769000c00422254181c2d102c501c0c510900fa10700c1040c0d00320b445424016582c2c02c103401c020307190700c041e03902103441004100f08070b00d0103803102d440303205010500307081c4450b00102c20b200140e0b0305910044400ba858000320100024408812040c035008207400030100d0050b10360031404001d44a5650b000c40e0882c400b00088000c16120b50300640e8400b5207080d64007107403800f1040100c0d0300301c0706600c100c0c00150521425222150140612020b0440000000d0b18000041d5551900c44400070f04420300894415003c841450007400204400a1302c410303074a804c0c0da1605d94040c19504a4080c9a0020b40f0b8500c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 435296798 1250 435295548 435295589
    0xf03070201020f0d021c12020f070201030b0d021f0309060510030b0903030f04170702030f07090b040b030a03050a11010606180803030708011401020717030403021207030b01090b0103021210 83
    0x115504c00d910503030b02402003c1900078500564007401d401400420903014880c42c40c518051010700308185145040a546040c40d000041c1030740c58035101d1134402c00000c08408016502e03140318002564505a803411030740a42d1005800600b8052000340c0120b0030001040143c00059500405583c454140700441d40c50302500300355030340012954000f84010410225010511000c0440701000603800c9040c681062540880d041c000c0240c0c0d91581c0e584144000e102401d194000e01500042c2500c041205e0700c80400000ea89410008011f410310600142e10005544103080c03c1e00c91041e01c100a1050300d66842c03008080c540010304502c03451120180100341079101000700c0b806481140d69200c1c23240d080102034600d045042070000d06600c00d41c000014945034101d15030680c100d816015503100c500e140103011201c10304a016200c1500040820310008030310040140c1550060031000070300100510059000748501c44091460065000c1002001402d210041040d101180c405c01c8031000d055 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 435298048 1250 435296798 435296803
    0x915020705070b0f0f181c03020105220204020708090a180612030806090903133003090303030213170604050c010801150503060d08040e0919080a0e040b030f03070201020f 75
    0x10004204d0354104010800c551030380107010b0144c0700c0b41481900c2c8429a88400038070903504240000c0c0440c4241d00d1100c0c14950203100e61a442100c2c0004808e42110030503040d03510f00c0e04488000e100f298041003a505000440c0c003920300e1240301403d105030064031402d6030030280362815601c244860501c030000c40c0c400540c401c1a0782207a032640b01c62100e03449180421000718002032061001d4402444035100090a081001c0300600380078141800e031600740740f180c0c08006100a4134604450801e80c5550009505c089110204ca402d860016100c440110282d0156074aa03070040007031003a05030820681410104826010700e01c0b40048805080c440401910030031002d20030003081d11590103600215034060002194490002852109003145a59030070300c041c3c01507000040400101000c1010302001041291919020400746121115403646c90700e10034890100444100400080003500c5a00d50b0340040c1c110381401030030780c3c540c0d00d0052645940c03074000444c1640140f1650740e40e801087c0c0c02 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 435299298 1250 435298048 435298057
    0x120c0f0a11010e030f032710060302030105100e010608090c1f0807031e0f0912090e0c040807180b040903030f1413020d02060d050f01050111190201120915020705070b 73
    0x1d941819a9a4622960481c01f03002540106240700500c2002c00d01005000c4203005265050001510905500502d803c56000a10721162011144c030140005000b01e42d00b941107400c44d00e880b103c181d0300c41c190b4906240c034000804c0c0c1c02001312108007910040e900c0c59000742c0200c503940c5980554a02c0022400e0301c5601402a40c080c2841a5440701d03049a03800202c2c041980c40f8011a5240c81c607138541c07507480c1d11120b6403030004400c081d040c010309440200103500510040d100c41d0400f0300700001541ca43c4007520903100300c0b522040e4030444040c0d480e003008450600c003d000304600916404c0103005000d402ca025070000d890001104500114180300b203000d00f040b101d840c00c009000e40d003402810b04802078185d034007050070702400f10302207505e0160f284214114041c00d41d5a500d044000740210364003200340c1401c1d0b040030080341b208446240c82090000d40918018889a210800010062958120190040d18030400a0071013020741c2d0003c00d4118401d00459004940d078010750010fa014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 435300548 1250 435299298 435299317
    0x80c18031f020d0c2d170c090906060a020c041e2a02071a03040c080307122a110a1a0913061206231f08060903120c0f0a11010e03 57
    0x155050000c0f0200800030100c01003072406d05002050648030610100c21450858000d0050b03400014403482e2810001900d40d0010010b55006d8100b07a41e41c072010707440380002c05c1d03001d0140da42c0300c542c2c000701500049c071003141d0035a072501046622491201a040a815200782c02d02580e00d031906c030045548002104001c54401300ac1c8040b0b1490f02c0c030a04900d03a800513105980d01268540301060804041c40200542c43c072a50740301d043d00c400f80d90003400c0c400201500c0310b0300e610007500444d40500c0c1107180062007075002a02d8a034107441000040d500710501d40140c040b400d00e4050303007202d031407a03180184150305081302c9403d0003110080e20403040d94624091580c9554600e4003490001d421034001d9000200c10030355040001c41c4007910380d40311203c200c0d202d50345007610450a400707070800b01389103201a115100180c41c130780c0341c544003643da03034410303080b201c2d030346210030f0700090320043e8240140c0754850407005105903511941c030002030080c80f2102d04118103518104c59686100700004c111140b000d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 435301798 1250 435300548 435300587
    0x6050306010b0f0c010b0a0806010801060e1303050705100c020a050f010e0d11030403060c092103140a03060806041209060e151c090602030115080c18031f020d0c 71
    0x3681160400f203801c4580d07441c54135902c4030025420b680c0c0d03400142c4003a0014074000d01c955858005041d09651182d40802e01e044684c0c42805540110114540c03511505402c060307076a5842071400c18a0b0485400c2103c40b80d5180585901680368046014489140910207d407409100140480e0803207034111405221a84120080480d05000308284c06200c03c420003600e0403d1342c2c035141d00f4140e4280710810000102c800b0006c1c030250311f4210410021058500e4074819800790343d50040c141c03800d400c11040d410840403d000b92058400e812a4001e0903c0c00b081d00d5490516240003090081d9109041e800b00d480d800f0301080881c8640461004800c00602601d90006040c0000401e03500200c00340b84800c0f00c40244030b0080381c040c001e440815120300e00c01a900d41c50f1055800000c0c0e80483ca0904002401e82884009070352001034501c01850b11789080094642c0d800028036010f80c02e52845010039103604804a42a066030117044103410250041c08140c1c69210219140c48030010b41c1194003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 435303048 1250 435301798 435301807
    0x20a0c17010c2c0102070305150604051f0302040b0402072f0102030309150a02071b0602010e0c0303070b130203070b210105061204080c03070620030f0f0403020c12030c0106050306010b 81
    0x110140c0403030340f4070007418019210400c1c5c580c1c8517a4106000c0c81c1a40c85400f5000052240303500b02031107a16480411110305000b801c18006000e8020216848081e10540d2a0140f008695456130304031500c5580c001c015021821081e5201c10340f43d00041e103404520388010211207036550010048030311903ca404041c040c2e0710161604032600e130708003034510f01c4015824007506000581d130f07076800b4107a0003006400c8071a6518141000342036a0703c1420040782904120100040d984000040d68a0554000c02505c40c580c1c03407a1148400c1c41e404034000c0c0d41341c03181242c00116a0713850f00040c0b048014a1480760010301a005040040c03000078854560000000c101d0040030009504405070031510900c0c1903441c103504070320040d01d541c0003150151096981c60480c1c40881c001e40c0210740318004107529150840c03034088545070844200905140c2880d00080c00141054428004a20a100021f000440704400700c510b20381e42c2c3d00311440a45d8590720704400030890346800600c0398102c1c0c070040c8115140 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 435304298 1250 435303048 435303107
    0x5070c050319050f04060e0a090c0914040905010603080a090e071403042102250e1911131403010509060703091703040f1b0303020304090b01020a0c17010c 68
    0xa50200d1490b04100a4180007002146003004021700003490140d6501e010264190100400c01c11140d001c0d41c0002c1c500308c03084015a0304030401c071048a070358602c0c003012501804c011a0250038804030041c95540307002c0001c0b0400400401402003007900c1c1e510100896240c0402046180040c0c60040120b031140b00b1208241c05030b040203650107031260039407080e1820b51030114460300b1800340c0f0601c0503800c00802c0c51a03c803051311441c18008401005213023142c3c40d00f41103001c4044083c102181e1400c5070f10b9411081440c540041e0f825011344403007265920350142d80c50b0403842044c00380014000d40b65910307050b20300d41406040d009144d16005050b45841c1c400c003d50041ca589402120300c0e819403982c000d582c07800d0b00701641c840d0340030700c1c004c0a20f60007502d0301e00e40b00690110103034404100301c007082c004282d0000681e4180c60000d08000744030154400141d16244e90740000402c1030744c1100c40810604403140c03004282c004144000d00c1001d1801d90b050760301720b00e900104089904142c0c4070701e10 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 435305548 1250 435304298 435304327
    0x1b07031a070c0b0a0501081005240d080c011a01030207230a05061905130f08030c1b0a060b01050406120b0406120501410601020102040801060e090105070c0503 70
    0x2006078603030408480d0500107544100c0c00650880c0c400144903030b50001044018001e214000d4101781103c0100880d2900031400340c0f58140b1402511612212030f41c1c800e1070303900c41031b200d007000301d8000101a886001c5045981d002e40711070320840802225a25425a4650081c0240d4030583c0d4452070160410502070b41c1002c60141c42c00d0b10710154400e201180021a0044c04110300440343c90034030001100f8144034590540300c014200d80051440c0f1a119404140780a040300c1c0d0b010f07803080d1016038941350f420a400950052400c140fa4070041d4030041e440402c000070304a02c1c0a40310b0340042c03041180c41801503a450140b842101d01083c20456040c00c03444503507024107404903004000040c0c0701d455240c000c03003455440314215002d0b0b40d00c00d48101d030b4048a008400040110146920900c41c100111000010b00074610400c58100b2402268140e8001c2d0182e501070640c50001700240340d036400005080c482d041d2280d41e482c0d40381c0f20226145610420101400a0b0044000c61826881c0c0081c0078 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 435306798 1250 435305548 435305551
    0x203010b0a032018180c040609060e010512060f06030304030605090a03020f01050c090d02150a0914030105010b0a08040302070b0a031a0d0f02010f0504050a09050a2d0b03030d09081b07031a 83
    0x41684c042d050000001f551140b180390041d00e01d181002824078100344802d4120041a0030032486000301d54800c00340c1080000f41c00d984400103039a0007025883d80c0c4042444e6000702e810083c070b140e08120803c00146800a0102c8541d03000360300b100d43c214090b0782441e00f212401d480c4020070b00300411200c88039081201c4003842542c030107002040d0890502d0f0002d0300a8018000c502c00142c0c1d01e0300100300501d0400e1a908400504800030001c41d40741020300c0300300d8420106404240b04880c000681414002d02c800b900602103501155920302015800a0040081c00400710908000c5c6408650303d0034030410303100015510408a801d0241a82c005581c4c800d040c1101c0c0c0108035007048082200e440c0c0321102c100030030860300c002c240c90900038028016a04c0240d00400d0001c004203120540c80404111001490440080020702c0348000001c242035201d0f017810250201d04090251003044198401132282030f116030146030b16244603103009901c2c2c00d400d01c805005182c000142100021459192030b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 435308048 1250 435306798 435306841
    0x71416060926060a0209150a0203070b0c0c0703060507030624210207030f080601030510150908060c0406020d02030f0a0f0c060e101a090a02070203010b0a032018 71
    0x1240302d40c11140704a8a090811a1070488564012030301b4811410081501102020100c0c1454140620030400964034065940003238208171507a80490980d9003d90b08441d4440c1040341601c0c852a10fa041560140c002a10401c1c0080c0c9030100002d0803006180145030b9250b1b00900030000d64681c02c0003111100404984584880c032002e50001c49042288000c3c00319034802d8417030b00c00918407820f000c2d2100740001c0c541e41c1494101820030601c50818212501624103011140084d01c8080000700c554900c0e039003088030303c1d203e100d0030b002e041c3d0030000c0900206c030b040344d01302c0e00c541c00000b1080703841e805228400100950140130003e009802505600011401c51904036824446512010709650702a40c1d20a042e400010035061004024040d0100028140d440503110114020100b00861070040120305881d0b80880d503942156002c1d00116082c60008101c13128031501e90915030841024944405154641000760420a040c07020480014200341180d00e0311a84d6441031404020840380d524 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 435309298 1250 435308048 435308099
    0x40503150601020c09040b0402091e1b0903070e01240c030509041b050c0f0601260c09091f05060109030209040f140c1201020f07080f07080714160609 66
    0x39511651112609581b103036024808100003400c080c0148507403a040a00054807182020141c0c42910700d40711102078102d001c4003408c01d40004005000c810f180100c05885515000d28000050342c0048150121305032009901d443e80c3d5078146060340b0405c070b004601d1000208074144588408a4043c030080c02482e90702130004503980055120000c0d0200c41680a00003255000c030f100d402000e010046e071014402010010010395041c02400b68812001c50400803907082c100e814400c4805060100822000000e08003106030308044044035200c17003000f0180d200b50b41015207544184c101c130307004241c046c000686a10703850500719000c0c440b1048000b001900e42d42c040c9240794001410b5450b0b00000c0b034400c5e10240022080000810980c0300303c450345140b29070b00600407038071a40290000c0350012a07002c6951555011a001d0800c507a01030071401400c1c458000c1240400d0040550762940c0c0140c1a900f075819070b41a06000034102e42e03050140038009000c0c040180601c04141940101000c200003e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 435310548 1250 435309298 435309313
    0x1080c03070518041e020913140a020916020111030c07150203010b0d2309030307020d090503060a0b03071e05010801091b031113080c030c06030c030601050901090b0d2004050315060102 81
    0x440c9807040c080d25001c60f2236043c6400841440701d0143da41c1d8299503010050500b4062603000900142c40c0506041c96002007041d2001c1841e00135030201c02e01d030080a5240740c44c1e280494500c4441c0d0000f800a56061800341001c0b40c0c040094400c8034140c0386a40c04290400b03520300301d10303070086c00040150707200300c0501c81c0389998803814004954170800e0160003d5503240341040e40282013005045400080c440e842c20148002c0c1e50201d2811342c031039480180010300f5158180081c1c40d003600396100b2142c0c0001100c8409180d600c1b01000001e0342e0007a00c0d00043d80e40d03a2802001280c0c11049118180340d48240080d14240c42500b00c40254055014000d08007008400c0c61600784040c0c1d4400b0036141d2000064010714201800364180b10319080304d559045240000328401c4d60720000740034a04004e400104007046070b000d0000c200140400648881d1180c216210210003068808209a04809010820170000e0200d400f00e030241d610180c058000a0007001c40c540c00500003800a0f41503001c0e0a1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 435311798 1250 435310548 435310553
    0x801060f0c030e1c0b041407081207030e0d05100501060e2206050612011a070309030f020d0803011401020c041a0d06020c010c0507030311030f0c1e0301080c03070518041e 75
    0x40c1da001c0c25170058a070040c031424645883c209400d0102c00b000c207280c200c0e00007001320b440c0c00700e00b5450300c244c25001141d0710b080034038040320030742c4441ca0f005da4480f0715001d082c004c1c1302002402101c480f458000812070fa0f40c03641401d9500c2e1000c0b2400d50b511121040603807104002c0c80c01e0040511284400101d0b0241d00c84002404c141c01c403040041c5a082e10b200101b10090107200c840f00c514040b01421860705205031401000a01540001340244107209800300c21074803034881541403250010001d039141d5031150700403044071190400281c01841444d40e401e106e858540b04400358071410442c1e1000084c801018091380030500354060341c3c0d0750ba00b800b50300b5200000b0301409041d43e000d80d440702e039140c038145030240864103e600b0080c4016014800c002c0fa070301304a0050fa07080030160b0302c0c2586502d02503650f40c81201111a0507982d80b04040000110310200040311203072500110103403010b103074940051046201003000f008011140100104021502924120441c0d601a00d1301c142c1088c42c030b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 435313048 1250 435311798 435311839
    0x603150509010b0d1103040807080315100804050f2e0e010e010903020709180308090f0a03020606150f0d0b010507050a0b0114030c011d06090910060801060f0c030e 72
    0x3d034084094104001001081041148a8842005884c9800303505609283e100d1540601a440d4003c0c071000000022503460803c4400e800d46ca903000030a003036948a244540141801b030f0030b07102150030b44a041060350003407a020401c080c3c0d011850003024441c010119001c0c51000103940110100d907034411100b580c4200a02400703110700e034000c0c0086403840403850003d1500480b40d102c110742c03901d00a10b140f1031140045140740420740528024403a52103084030641420644600c0180c3c52042c550150101600490240d1003031004071042d00c101080c40016100c07612481e0346001c4044c500300000a4044000c1e400f07a0b0302e0641c18541181401103940d902031900b081c089040e924148a00010020a0b16541c01d501c0e000d80103402400511480c1c50000e8440880c10700a0190f040d1325100001c059116841517600f4554028041c541504202d03500c02c18046140c00380d10009120000080743d054095806150403840b2941d401d80c9440d00d64600719001c400e03240c1d0789540700b010520308001040a2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 435314298 1250 435313048 435313051
    0xe0307050d0f02061e10120b0a110f07020d080c25060c020303090d0201300b03070e0c16060203010602031c060501020304090b03010e0303090a03030e0109020a0603150509 75
    0x250010720154101240203854114141840c6045521100030010459086003407085840c44000e1421000d88422990a100030b070390b40c0000c00c00e80c0c10a441d1070207009440300c0643c024642386804206100c1d5003401e04100340b040c4030079140f00740d808010050060500d82c150115850044028500701184401504e08103510041c1d91841d0f0f20100c828454a0350450380240024460350410382d03102c01c5c0c00d50100307480f030040c088070078030860341d111a0700196405042032078810f40d180c104160360070710034240d5008a40740c440880746026150145c0c0c8500390400050810a40d122504900d04a0b40c64014030b03441030b03000b00810644d2469104038100017070f6440c00903601811f210303006540c0312084900311540700d036405080d024840341030003410045a6008030840e400d88405110110700a443c140c00b09014281c001d211500502c80001000340b0300c003020500d0b00c001842517600b0300142a0100800f800d0711114000658008020482041203078001d40c0b0500620200240751910740744d8540000300360160 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 435315548 1250 435314298 435314303
    0x80d06120c090605030d09030b1305030a320f0703020109020a090e0d0c030e0105071b081509060f010b03150315090f031309020f0d0908090a0b120a0c030e0307 70
    0x11070803041c800035905000c0c5801502060f4010b00148104500003071a0b04803500c00035000780800400305503695a0034240e1035016400c0421256a4520b1040c02030180100307007100007021503954080410303401111140610303240203010340c44c00c11401d079041d209147d1040308200d0a5641c4c40112200680760040500000c01e40900d001076450303c03400c2c0711414461812100700400080450311000283c01004080811400703103051a182c1384c16281c84246040d065200607650b141c200c50000d009000002d000503605115102000030391124107806680c0e0390b0554000a00c524814018055500c5138406190b004003254540d00400c0c850780003080c207103145502990b035180e045004104e40b0a1042182c1c0318008501c1c80150300d4030340900059181c100c0715000e1030200a030000350300041207038000151107035405121001c002d00741c01442c0241d0b540c0e000f5011280118800c10700040c1d0b800010701590a00e041c28965030b10a591590034900041c00b08480d24020305668076000120444d041024203140303803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 435316798 1250 435315548 435315563
    0xe07030c080c0a05091e1801020f19092304111303021504120b07030213080607120b010c0b06040204081207050708070b0d0e070512012301060c080d0612 67
    0x1580b10a000c2d0541054001d1801054010140f1050240210354003048211044105001d9203441d1510b40b001c0c46400181c1507190b0022580244182c1400001d150404083c4002051704c80c000a0503252180c00d4401d010300d8106446044401d1840103913003042c11a40140001040b4583c00003034040b6400002c215064020f00c12400d10460410b4008440e45107402ca00030384c01e20b454281c0400c83c200b4100c400901021501000c07540140c00794040e6103c4030101480d043c80542c446d1010b5503103920864421001910f507070003c80400d510f501c50414203003810ba558031022040d0f80c5507035007050780c046c00c16a04151f01700000510007005004a0400c000c40001c96985d9030705c0c0e810000d241801c140c00103404d90308000002c0041c1e01304403040718109000707a00003082d0005100880390a00001d640706980060010001584a5906500c02271041c0820395000c98040e040254802c1d00000c24082ea401086aa00c480c9000c0f60b5284054112000107500103e03c07107450304d440021112203000c1c100c5415 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 435318048 1250 435316798 435316813
    0xc150b01030c1103090d080c010c11191205070215030c04030303050c031005010f0509191502010b03070512030d1d06361903090618080703060e07030c08 67
    0xd6900d4050075880e09624074081007420580522562203100d9080f135248102100020901088402c1055441a442c0c5030000c009080c0d0034140a03000401c082d403c00b2480c0100c20076001c807001d54040d90b0411176002011604030282c8c3c00e0041c1c40a07070103980c0c26603101c4004241001d0b0107081c44000c500c542101c4810b04c0e00e403850351802038180c1311b010f0100d4415040a0040080c80000728140108591003440d00c2c5070b0000318003c0c152104c0c032807918455000700c40d00d10507000440f0052610400c641c1c4d82e10100d009203840303080403400c80b03101c0c9840d0f81d45034015070410081842d0401c040386104d1006000e4902c0c2c25101c0d0b03048000c0b0b4140c100003488400300c0554202c1c1c0c007942032000039440285c10100c041c11403603688140f44480031000003440540d0480362001010300d810040c00e131b034413640b0800325507081205040143c0880036500c18200001c4101c600c158580101008201c1210362690041100d2400c540d210b0707014001e0051548083e100b8410008040b50300700031108010440d940280445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 435319298 1250 435318048 435318071
    0x201021902010905030304060b06070c030b04140c01170603030c100506030d170109050406020403060c0201090506010f0f030f06020906030c120c03070e0f040f0911180c190c15 77
    0x98068500e600959142907410b40200d88080226940145d105100154031501140001d0300350003240c0015014201080c00841000502802039001314001d83c040321180140c14071721940c503000f80901d5800035206031a4010002c003400943c5801501c01402e82c0c1c10140d0011110b407400e0814959000e1035a03c400031f10441e414203118440303403a08945030100109007034030300d928021034040c481d0035105541c500009051182690540d005140d02820074082c202101100074040c0c020140700351032a01a0138000a500d1000f51809000c4818883c4940c0c86685140c945060043e00300a090f03418a40030041c15125a80300c4000718071540541440c1511100710f50303080115094004c28214810b0810401e10002d82c0e003148150f07900090488401c500000c00c00c0c08a0f024241c0355842d213481a04050300e00f420032001807a01400c00c40c05484560f10860030a5100019010507564004500c004005203814501d202c2c15847d02d902c0036051040c0600201e941d000b070010050711041d01c0741a5140d504051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 435320548 1250 435319298 435319327
    0x14010c02150a15060c060212011401080f07020a02120a02030d261909030306080601091a06090d030c0302150709030b100b04061805040219081f052b03020102 69
    0x802c509403020401112000354071410319802140a040217010b00a043c00003000501e404680512521000c0300c185540c0d240048495441201d01460200d81c0c0080000c00c0b00e03a940300c8031442100781d9402000040c3c002e40a00c8070b00c400a40039030016000b03683e4440c015803000c0100c590f03407000c9541c03104440c0d480c1c2a00298400324648441418a5440080c070018808880350a80e09404140b000207200000345001d6004003010340c031000a6000380700001900d041c1ca0744c0001c2850b003900098290055110381080154494088803603800403c010000f40480e2141c0030031005240302c4e0049965100400c002003407411011070780f410000f040141c06100b000315800845805c00c1c501c107882042281441b00a4800d805540280130410689811845281602c040408014900604115030343c0308001340c18248a600c1040b4040415100004035400416406500c40b001d076040c041441c040d41408100328001c1c0c4440501c0a0b10201208690b01d12004080c0c0c0c010b071a4880e40005a90340c0c5503407141d50 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 435321798 1250 435320548 435320551
    0x80f09010501050904110112060807060f08090613050304080114060a0e1510090e010f06080702060403120b0f040509010903031a0102060f0c16060204080c1e01080414010c0215 77
    0x5405074103010041040c2d85034031074950340080c2c0c0301088007030420400d00120780b0f90000070411107a481c00c02c40005040440465004240c0d0702a68a004150001e800305859800c01600d010340b06074803e030002840504480c03407518800f4810020399160507603407c042829988a9081090044107103000c1c01481d144c91004040100360614002c0001d03e083c0749260001c811082981e805007c036103007582041840351500304040d0100c0c100240065850b9041107800c241c07540204400300700c1210100f01c03001d00000b0b03030a20035035042c0d9841c84684694403c10010b00b203501c035a20f40001010554484907601c601034244101c948400014001d980790078010b00740c0c2c000624408400360f074900510303900e0340c3c086800740d848400c101c003000494640b40c85500d51481005161890b540c004031403030082008075001001100c0995080f900314216070703020480d11240318070ba0844943c1000c0030440280d40124100b5502c44d02034032011064a901444903401d54132241e44820058002c041842d07207011122907640d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 435323048 1250 435321798 435321811
    0x41e09060311010822030809120405101b0206070b15010918270807030207090623031f06090f090203060601110c0a090f0e0c030d05070201090504020a080f 68
    0x3400494515110600c454001c003000c241042140c000103058030106050a01010455455840010b800c9080040170800c040e10010400d0040c40006500000d1510960301911740081c0b0201ca060450f200a40c3d00e0074030840d040f012a000c0ea03460710056614000a403100c140500a8212545002102502c0c40101e0480f00e50611011171810701c580c0300e0721402c3d280c3c6810007140000d1108107070380c0306101d201150b012100c2d01c0400d40701003200b0010108003818985200b038013146d0203103071110b41710340035280c0134000d8805a40303041d4607828000b00004221280000040d041d61140700f28045541d18010140313003202c280c0c0e80c0b110410410740780c491148009420062400304090314903540001d803101e20141200303040101e0303050001804001841800c4d40d80400415404d200b581c0c41e03080002804100c20000c2609240000c090080c2e140440c501d107120400601400700c45003041400d03625908038038020b0741002411040030800740c84a200400100c40c99440e404603610b88100e50107008039009001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 435324298 1250 435323048 435323051
    0x1503010c090e131b030302030a180e04030815030d030e0c01051e1e07060b010e090403090603020c0708070306050103020405010506120604020a05160f0c0b07080909130503041e09 78
    0x400c20070081c8803400e90850301881c05583c100600b070801e01340701380300b500c80300c00350324420300c400010150008000d0003c0e41d01c81e110313aa0808041d20000c801018a48503506a582c0c132900005c0000c0d21549540758051045000c0307009800c0740d5404640381c8450750100d10082a66800741c240c0b00082008170240100c1c092900d140740002d001a480008807081c06440300003040498854a5007004000c4220251000303088613403200080d0501d400a01090820b00b03000c41d144010000103400c15035841480b0782d03056110002030034500302e03048009601c0f0a81d0500d00e4000d164000c99030b40003e002540081d0300509000c629541075004000440c3c0b0103034801449081c08001c2407016103642c04c1090f90049040300d0050b2586840441a1a14861881d424000381c40c01042c241c104508840f804818600a0001d8007900743c8540380303032019101da000c016204074010700c0500c203686000c8a80c56071089070340210041c00c140303641c0c80c9495900580c00003441c0042d1043c0d80c9960b01004400c000040104810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 435325548 1250 435324298 435324317
    0x21b0708100c0e0d11090c180a2711161406040215030408161202060105120a1118090714060406050406030f06051009080606060a1e020f061503010c 65
    0x802901c0c0a01d40c0380000d00503519013222006003c041a52a145d140300640342000e43d16089040700304d150b20800c12000c0d079100c0c82d071991105d424650f2840003902c038000c1c0d8154500d11800c80d001a0928611141a01c0580311642950954a540d0141404643c3d10401c3c0c064032260f4035200040100b42c0030742c3c400742e0303214400b08001359503032012400b444180c68581c40e81e2504da40c20440d4a034405c58801c0b45244204d0f07007031031013082082001c4140100035039080e50450b903242c40800441410420500e406607100344eaa600116202909a05090500034500c4060b440e80c02e08403941c881c02158280383c82c0d0042c41003080880304401209041203003c0b03c0b118500342c02e000c00507081d800b076801000201560307030481494685007940b141c8007800c0003c00001e18a0460107004066070084d00464440d40a040042445420705100f955a062400e444203142c1d103c20201d0110103029680c00d10045210300c604008501e8010f0007020b02414000308508a0f0300d421906050941c3c40b107800445c00c0240d5480d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 435326798 1250 435325548 435325571
    0x5010e0f060603101505040602061b040b0c07080a03050a08070c03020a030806210303240901170a08120412020a0c051903020a09020904060f031a0a021b070810 70
    0x1540d2580000308464080e120b460f850b10115229001d508a800300141e4a0080c94580d03400102920440d1200e508548030b583d640030313140a9000d8030401c1e002854400b440107000110780e89000d0210028000d003202c102c0c5075200c0802c2d1825100348400c0d40401ca0014004e01c140c2d50040d5800d920030311038244a603420320705c0ea40007550b900c2d002a01030200154200400c2c1540d4440d8518000c1c4c51024410b20f00342148a10020780f268015030b40711110604402c661130000000304c0703c038800080d0082c10f080e0f09038649032000c01c244030510068540d900030301d5107540c00034106c64058110707091800f41103040c80c82c10f4a01944194404c0c01124155030000b2a20070010b11707549100c0302070b91000d5031210b4006050070394070100780c641c07504000d52000401c0408560400c040d0b02030b00b0702c494125003d1001d1941c032003c075140c0c0300c11400b0141507210009501c1407e4003915224a4228650301d078010300c3c0c83c41418801607604a608081549900700c2c55042002d01410040c0b07544801c0d100c5c1d820855060f591 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 435328048 1250 435326798 435326821
    0x13090c110a0b040309030f0c090c02010b03030f09210a030212120a0c180603050a050105040e0304060e240a020d050c1b04150810181101050d0902210105010e 69
    0x300c100402c07a90160001400b014801ca00440086a01849102c001c81131480c101d290740c44580031300d02405140000060540b0300c140281130450202401071032810f64820354a10940d0310095019410110100c8003000b80e40b00484120300c1c1129402c0134009400540c81c0003801d100c41030b05070151102c01803100740e407801c0740c0701d80300358000c02a2007000038032240000007925041140d581010302003245110004132a034050300300394420b80c0040c20800c2503a80b650100411070751074101340209588244814041300340100440d100a6000500100215032200c960b08103030451801d100c120a0000705800c0728480c0c04120300d181d80402414003500300b407000d1107404da61740c01c00e4481144000040c0c403c101d071603c603684800480846504c015040c561514881651150704107241040c552912030460580c2c428040451030659005000b44100b000c4c203001100e140e009030709140c503a20303a034000c0c080c0103030b8800446020b1002c007503620091055129401c9821100c0592206010f80000401c1203900c2146 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 435329298 1250 435328048 435328063
    0x4150503151309050d030606020f0d09030b070e1c0605070c0819050f0a0207050a24030e19031d0f10110f120904050a02120610020c0613090c11 63
    0x5558442c18503040c400854050100b0040284c19070090704941480964141c2048040c0c0e80c05800302e80c041840c10b00342c02d940300301541c035520000f03000d03007c107100240811881c01c4d0000700500e054540c0c601d200001604002c84100100c69600e5800142c0d410400c132801401e81c44405802c0104500d502c1e80c0342c1840c01c2c42295803503001b0040c040484c1404500401c1951354901c8054601a16400c08120295a8900c0b500071288540303510400090704c0090030684d4040c080012403110800c0c1c52005007900940f030000304059480c0940d14008150b6441c4504084015020b1755507201083e02001c030320b00c07a1810160320b1500601d106ca1104d1400d460702d106c1040c07245414a00540c0c1441c010755840d052215904a0038014001c25145000d5000400c020307000c85142140e04001030384900a00c00100d100b47d03031b900420b012a410021b240c601e042044100b0145d418010341d0302ea074440c400029401d500460040070f030145c41b0a418003d4503114468030201c4085810140210f060352600550f55200 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 435330548 1250 435329298 435329341
    0x1504080a23071403030d050a06062c09130f110a1a041a090a0803030114090f0f27010e010b01020d14160b090d0807020d09060c080f04030804150503 65
    0x10030780f8804806071020021501c4000d0307804001c0119050000c5410050021442048005040307c400e64a40c610b01c80920450f0fa440100049a1414800240b1860003002088071040c9810800c40c3c40124160720b00c035043c0640304c1c10a0000d40c0c40140104841005203800c50b8401000402038102d44080110440301500c4089850000e61504002c400c8030502c40d006c6216000483c40710001024400080a103050700c0c002255140209102400d0004041d02164000c0e915514000420750303021b031405500d071300a00c4641c00c0d42040411901d05010703180c4100c44000b21603544200b007001d400c50a01c1040340c0da1200344080d00c2d100c4440d080060a42208441089280300009202031200f400d03002ca000c54554005810440b0340303080d814041d1aa02c2c00001d41011503500c0000500302e07072020441c558214180e032a5001e5550074444100c81d00b500301e00341250031203006c0049003492000c49011f40000c5104a003040c0d43c0d60b08196408810300a036200c0303a17040c4081031083c8148002d40080003841c070380c3c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 435331798 1250 435330548 435330569
    0x415050d03030e07080715020105011a03060f03011b0c03091a04151704060f0e0601060503010b0a09030506040b060a170c0f03011803110d02071d061504080a2307 71
    0x1605482c003d0304006640e48401114800e0250010300c4106d090320f42d0343d414000380c0007080325030b81e00c0c0501d900300008480c01e00c0d92880104002012458403801c2881c12072005000050f1601d1185004280400340d2000c18000c02e0012060804042d8002c920402a104090010004091101054059001e18000c200c17608031152100d0841500c02c20702c400b841c4403400f001c03031100d0a203801c041000b04000400b61003480e003040c00c440302092000600724122151681c0302c40c03640e80ba240c00c403101904040c580c0410010489800004200d0410810380154010030403405a810854108000704906038062007079554070b90300106500c5000f0a0300c40508800f41c544107208040500001d0041c076101201d42400200305019030207055000c4610100380000400312a4900a00340040e0303952000b9211741410030048598903003400750b0924003540c000c18090054030342004014030160b6a40c000341c0200c45141c2c44050b0802c10f11401f490086500640b000d00040803001012000361500043d005d20708506 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 435333048 1250 435331798 435331811
    0x30e161410020a080a0e1f1223040201081305010501090b1f0206010303081b0d051f0e010530030901090906031509030e040e100614011b022d0415050d0303 68
    0x207484071f4502e104031000241c0d1000e01e41084080203003601c0181c07011a04001e14040b5049040400209100e02004541400c40755542e01c070380c011104010020402c0c1404020750030101e0025409000c2c007406803040901c04200040f400003400840160740c2d0550403007a1502510028098002c654079040d00c0c1c161a01800c540e446604d95101c032003102c070b001081945c0004101450144503444607016804090448040b0b018038424040100154015000420410f40040189140100b80c000d01c10000086400340004065000c00311038161184a0b861234100080c0c05516684c4035103100e01500820004020060560300c841080658114011480943c0c9000b034409050041c62200603d501c01882807201603044990075494101ca610403244840c1480c42c049524541c0708100801c1c1c89040e510035406107900310152964004144007640c0144135454940102c81a42c00e40e8098250110b0131100d400e1040001c0c0001c850001c04524103074183c0e0b0b02d0501050380c81d001d1440e1700036050314021401 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 435334298 1250 435333048 435333077
    0xe0c03040c12030512090c09060619050327030703110a0b070c05070305010c0f0816020606011413030609050c0306011a07060b09070915020a020303040303030e161410020a080a 77
    0x2d882038500c50352510070040b04001b2000c000091104480d4030a503440f00c19500c800c002c1c440341c0d010302d40741ea0080038902201800707080e2080e409144e101041d14200070513020080c4a05407400084103008080d03400010704c0354241038000602c544400380c0003004080e01c0b0041c0d16a00d41210001c0c2c0441d082098042098050110800c00720014582000081081d100748032000b40035501c12110400105a181000034500000d400100008100c0c68004e0041c44d83d81c1001141d0500e01503204102c40c0382d091020089004018510ba4091441000b00042d0741555040c05803070300901740481c41c841d41c031840c0140035440804820b18030010340641000d84480302031070540e000d81064101c45420400c4502003101407035002c2c10460488804245105440c840900200d0700d0783c8140101940681c4104000c10000744258440e02528805100303841000f610b04210b0150400664410342042c0442181c18400f440c007504040d00b071036003500040480014564444020b4001e00350b114090044241c80c0b41034 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 435335548 1250 435334298 435334307
    0x30403030c15020c060f19020304020f0d02151614010c0905130204030206070b040c06110c1504090906140703020a1b05120a02160501170406110409060f0e0c03040c1203 74
    0x181d8134034031081e44c0c002d02c1d1482d41d426841e00e0403601c0403407000c811108070409080c00d100b00c9000d0741c0c01408801101010109100c5200391107282240c00c1002c03a10314a1140c41c80b0006841c2000c0100d200f0f031803940c0399040100341214a000d0b05045c0b44d2400d0700ca6510f11390800c040f48100c61082d905c100e0501ca01710b0384540280100d510280d000800041d62504000301e01c00d40e00e21451041452095643c0c650500300c40c01846074981324159401051148014034100c10346443c28580109003a01e041e4590000d0800d880ba2290b00304e820f992503000d051440d112428070b150348540345160031400c120210320700404520f1500201c44130960035803a141c062010a000d03c0c010b491340105070b0780e6190f0194400035980c001b00d41c07545c54041c82110b8085a070358070071415243c100c80c900c0c0140242d511241c448000030034006d44008083c0c0410040003030b0461450107440300402070005429410751900303009100300e1400600d0402c241b0000c00030800020021400b5000307540151180241c090064901900c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 435336798 1250 435335548 435335557
    0x10f06140d0f0e010c0509120f1002090a0302041a0406092c070f06050d050a02031b18150c070b0a091505070209040b1e060109210209010803030711030403030c1502 72
    0x3c1d51542880400c83d4041e400c14010640c41030700b51040035000100c5025942c4450b10f5100441454000c90402502201c00360090003082000905100d02d1a03900d50028045030101104180340a1450b00000d115140ca413080c1e000800c1b5540042c00340f81c3d0b500590841406002250280c080c0a00b141042d9582c4100030b400040e0420088408085860301c43c054800e4000248020046041c0000100c1b00881402540d0040c07400c25604824a41c81341d888403459000300004030354080800b00000340f82d07603580032255504a50444c08a5503a03050344103141c10040281c100741d152010420110465680c0300090400700c6035941280300c64015a900c0807649441703070f0344019502c446075a041c402480007100c00319000f01c40a020f0b040c803030508010001c2c3e001c0c138112200c9020a48212040200d40001042d40c10f4800c420001d0030759085c103560001c5d4480780d00b078100340c0c03007070748040b080006490700320009440101c9030744011421306142d580c006080c2c90940100405514500b05241e00c90940d036015a03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 435338048 1250 435336798 435336821
    0xf040c06050f0f040608060a0b09150c10140a0606020604020306040204020a05161505160903080a03020409020f09040507050403120e0609040c0e01030f060803250b0a05010f06140d0f 80
    0x4a6542e81d175604000e019040c10340315a0b2007a0300001000454a185404603184864064a109098041918807a41503008042c031908035001c0d9800c4517501d803206204106081d400c01d9100e81d8141000c1d10190304462a603007004003594814414040540c2d00016003540c0301342c2c11103025a81c2d406185048805000350210b07070303002c001c00b0000481040404181440500914181040303180c0d0b0300091000541c8a0071307071080c081409501d040c404103030003400601c0c0301050707400d016250079a20800c8400700ea00c012642d002242002c149a9001e01d450b001e141d4001c80c003850a241454115181c1c6205051402d038400188020082d064100380c6550b401d82e01c032403400520070051000b04003006880c003c0d0240409001078a0301c0012114420709110b04810344080d00001e41c2412603000070328040369038440c1155455035174619100001800d201c0c441e88a0a030707040001c0781e03551400b0444103c1940e6030700031905001d0280c2040d00175030401c1c02079a8040781500c101041040714202d404c0b00034568003454 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 435339298 1250 435338048 435338077
    0xd02070506070c051005190903031503110405060f130213050a0b12010807060f0c0606050409050d09050414040201030b1201020a022a010207030b0703111602090f040c06050f 76
    0x2c014000c0e41086004964601032000d40c1d8490030a011010122402110801d440100c0c4041a42c200394a5a0101210511a040000c0c071701184040c11598015103500494402c4c002036104401400c0c10300400d03400c01c20964519000729000c0c80010040d8420035070600c01b940d400305496070078030fa45595900003400090003d4a219880d000b44140c00c0d03008294176400e81159000006041030f0010314801145d880e5540d20303061243c1c140080f0b6142141040546603551103840201d629940e5105141d400761103030000b8070424803103140c0684000803581c803143c03145103800e2003501241903154006501a0703091a0000c1c070161030200203010030101780c901c54680e40c804030b100000d454001036240e04400c0c80c0c991980c80140c8240416041000e8000c0b401d0044c1c000314010400165860300340358004510b801c01142c0c080c074808903940305070002c03441c4100c54503282181200f9410402c000681040b801d0801d94032618007510340d07100031500341c4a504200b000014280c0b481000d544140e0309000c200d00d24 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 435340548 1250 435339298 435339301
    0xf0c0c09090b06041b050d020c030c0111040513061d06030a141b090907090e10090b160c020901060806011107081b12100902040209031903030f0c0509060d02070506 72
    0xc2450b04050304071261400703a40b809081d50500300c0341c85d9404084003a184c0e6400e2809000c03280d2030020350401d00d40c0c2d60861005000309403688c8400e01071080c1d035102d40c1d01c0960b1114540420850034000c0c6c0e0201e4142d051401c2d0051043c0c520003122000725011202d100842138030b5000c00300386405400d0768090404110043c0b0303070901c154080f40042d40187d0b90944401c1c203a039200104840346405459141007544030042c20040c00c1140d820034143d4414038000c1d603018002d55490b03c420350f41c0b0060121b510380201c001b08000b04074144407911030103507103180c00c3d8048560340e4045600c6d500180180d10601c001c2d00c0004070705070b11071406030f04600350010988098030b681e950515039800d150820510445810700315443c2e5401c0c003502c000c4502c003188009058800d940071041006040350b107426a0400d400300652081614200318120a008028500740744241c3c65080003000c0b0341d2a44034028209040074200c0d808260b02c40141e943d02c890888031181d40c0c9811505801c024440c5800041083c001c2d1030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 435341798 1250 435340548 435340553
    0x1d0c0f040b030f012309040f0f0b0708090d05030408071103012d050c13030b07051204050d080c0a122c060f0601080f07110f070f031103010203070f0c0c0909 69
    0x241d83d074102c603814811008084040707900c1e001c80c2840420078981024191000402060003005c0c5c240e0080e0113604c2544018000d0f0f01c07a0b044032481266800f0200309840140020008204144a405215032a0050450806a5400c0e11600ca04040600b03001c00851124589550070340c00b203210403c81c0d03903101c1c02e0310403808c0d0b01079190500c040c58501400c0c030f02000106a4090300c001c641151840c0b11481418030706541c3c03880c0da5401c02402c55010841c090140c00c40390040031030041c1c040c0f80200700403c8680300b01003000f0194800141100300700c2400380007121100b90800000b5401e070039540f0000ca80301c40e46481150f40d00114403055480e204815841d159151400b01d071860040c043c00c03030404929500c0c403006448442003901c492150000700c00c0000c00140c89030784c420088040e050241c0d09401100c9449914041c01600a84d4000c20046010400c00012110034101400240d00941c20f40c90b041c0303400340c000100804004240a00c0d00e0070b46042160b0a814072001d014030031001c010500709030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 435343048 1250 435341798 435341821
    0x510090608010c02120f160309030b04140c0a03240e0307110a06090e01061202070b07270315090f050615011d0901060f020c09010b07020405011d0c0f040b03 69
    0x5503111409801013802c01102c80c1700200031100c02d912060503240c07415404100085072440e4848060342006a100320200010390600300321070107640581c0e1070706010f51030902d546052a01440d9814411078070450104001000b15926428605d14a14210840040c0352b440b003028290b80c1640781801e010003e440810403003a0202c16004243c10781d04801841d468010030380c0c0b110f14078015800c040c1601c03030041080302e200d006a8800e802c00c890015003864440d83c0c912502c040241c980d400412a110700c00e101c3c0798202e400d4820340010b01c0725081a507910759252540401e1b23070340c00300918441e240c0c03406100b408104090921000c1c0d0200890303a55103040000c10b8400c0c0300d60615240040e00400b1113894815108040c10b00500d40101240e82a13442c0440641c1c060181507100070a60084148000745560b80510300c1d4001c040c00748074107940392800c1c1b04010484405030401525010306001d01102c0113100580c07143d2008250000750350f12210311402000c03601030390b40502244400001040700c045a071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 435344298 1250 435343048 435343061
    0xa051507030c02070602120922050a0506010e090a240902040807061403071d060703020a0209130f14011b180b1905090d081603080901050c070204051009060801 70
    0xe0395030030000010904402c907141c1400d4414400140d0103042500959448a0010034200e0001007d44042d910303441d6035000c42c655401d585550050b0341d4010000101d0b0240a40d0358400404d20b4103a0140c282100000c550003400b410940206a5540d0803039071840da40806a0b40f640d443d200e103502200c0d503071103455010394090301503892107000d88080002d00d58000c44400d050401102c0600e8110754903040c049410000380540500c0c07080f03155140e44100c4d144d40e402003602078020380c050034910070f2600506c42c1810740076000804044038003c402d8081102c0c6840c80e072409a10900c202c28496010b50014003409003c80034000311030390f844100d41566007002e680391010744040e40b035100fa981d27180c080c1e15907400380045240d0240608030f07140010714800d00c010800701720010168001d8074069200e8010381d81003640c10903080d480c2290001c042c107030001171103503100e0035400c000d105500d0484020b21040c015248028002c0b9110703408965681e90565001c0c0c00741c08035440400c0404d940350f8925010b49103 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 435345548 1250 435344298 435344311
    0x3070b0c0717070608070e150412050705090c1b0307120e01020d020a030e0d08040b19170601021005130f0803010f09050114120a060c03020316030219050c0a0515 71
    0x8122010200c2d401d40442c41000b1203140341ca6803807242d5107000301600d20440214070950f01c000354420154081118101410250140008400703a40c20a8030f0003510300f0030650019842401248100310540d2640d40c22108820104041038050349440750100d40b950042d001c4c0103213848054259001010741c413021014400500740c0c00c503111a0f1440006130b849903003844014000514611441c035260419401c80780f011442400050b203840da0715100141e0704e0300100f890404d91551900880713511540002c0d410246a0228169062401d1500005c0c1d40c070780a030300d0190251a100e0740024200c0186031032101c851500200c1d0745d01401d200e4076001e0b009074424003510030844404000441c120600344101c6040e11b12034181000000e502e00c1c104150000415000040d5200d141200070020f0000e000303070681604191000b40e241c0c03d0038000440401040751854003007501c14001c001640b030005d06084100502400c00395501c18001c407420b410324842103c0503119102e450000b040000c0481c0c0c3e81881000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 435346798 1250 435345548 435345569
    0x5032b050a0c0f180e07090306020d06061404081914010516020f0705030a0f0f0c090203061008070f03150f1205011401050604180204180f0f111803070b0c07 69
    0x34000c0106a880001d110442d0304c1848480c501070220544000c0115002110350070b00b107083c3d9580e6992801680e1250582ca1403035500c412040140760f421088101090000d4910541010f041c0141c00b0f070785034801c9040007401300443c4450024480303400c1003800e90a000000074031030f614182c140c1c003000d030010f4401c6600500c00d6044250081c071003c03640405071400207000e041c80071000d4440c0458044103c1c015078414180310700000015203400c00301c8000b00404240542c40303203000020400c403102c0034010703901803100300c4040240d2a98000c210b0ba51116a500f00081d101d000f4280a02e803180c4150400030b01742906040c0414102040c003001c000142c0b05e07800038070070301343ca030f05121001000a105035a0131480c2440140120355498151108040e100d00d00181001c0d601c0e1011141c00a00420111020b60350741220234010946008a10000c01014000e000d5941d00846000d0540301e03841c0d005049200c2100040c00e2175074144440c80042000c4000c40340c0f55170745140d50075124020b41c0302d0388060a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 435348048 1250 435346798 435346817
    0x150a120e1b0103020c0a2003071205060606040612020c0c04020f130902070209010303140d09080a02060f090c1302040b04030c0519060815040b09090f0f030705032b050a0c 75
    0x350300c07a0080f21801040c2030058124001c1c1c6550301d07498222425146982047c28410b403071031544041043d41d004001c024041501085241426801c01001801c2a4000c0304108824401d0700c2c0c00403d5a15a209401c1c00141d95213001c1d01828140b050705031305290302c2400045e8040005a40c3c5004d012040000d0389004001981e0390744a00880c40b60260003900410b103a401040400d020b4145810010f40902c412032900001203403c81c210f41d42d0020844102402050401e0b0310381e0b0400615900a40c0c02200001303a0034aa03820f00c0e61803640f5000075208141c01200841c4900403501520000c045844080f526151603260003111500140195401000c01800c01c492807400810540102c46990b202c00b1010b445076001d48007030427898141c058100340c8030f10144205807611111188145041c40241c4100801c403604142030940700407040e500c0f640700340001c0020a42c0482112820350350340c0c005203000e650845800210010131424110a54502400c201d4a243e10342c10a0445150315034401904 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 435349298 1250 435348048 435348103
    0x51c06080c030a11040c091707090b04180b091f0e1203040804030209041106181002010b15031005091003030f091421010207031211030402150a120e 65
    0x103403024124080e0490400c0b05884d02c1c0303801d1a501212800b9240d241c448542e544a0400340b150384078a04035100c1a5001c0d07002000881c040748076541c01c00b601101c0074004034566860090090003965006440a0b040b01c02103080e21404000410032480561514103031450340001100c010820365080355a01d01807540d0000a40d00c85804680c4590350102a0604260840c0c003840030180008104440301404158507015565130300f000742412400e40040d800560510006000744481032411601c256030401c8503418282c0d907415070850080c03030b91903c0e01c2d45941d00c0710810174580c0b06580c482d94110301404144081c80351031440803015a8005d480780702050300e1010301200c501c03c0c2c0b07102d5205040002c0c00c1840c42440c0121300b04e240d0010010011140c00b404041050032039200c007400300d01003500c00d00340c0d100025a80c040c000082c1900740510b8110314090300452062001c0c07010740e4900540000341c0c039441900410130f442e810021010304114401d4004000c556a07495029022a4a000d060121b800c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 435350548 1250 435349298 435349303
    0x1401021b0717010c050a080402040b04020d090309050a08070e040204020d06060c0606062f011410140913150e060a0903030f1a0103020a030209040e071502030f0406080403051c06080c03 81
    0x42c0b861903a80315071401d51a190f00b147e000e40060400c1344e002303071075078090499966113001502503048003100c0001c0c03000c02842e014203c03080c280d102c180a441c01c0242084424400f2810204448070121702072144e9860b440007034000e11400140340003e51030914080354070360744451080391482c400c420420505460b80c905072200d10403940848080390394180440a03015007071540d15001d401550011a41d00e42c040784010b2030340011901c070b07111507542c002e00700074a114186020105010030344a006041c20300e0351003402d28050410003d0b04141680c5024556004244d01c8441d0410300c140940e0300d1030a014000304060030101c401a80000c0c00d240700302005091a205511465502c01784a903454502c1000560194215000c40804c0c59400e1060007015112401074400b1030312283c001d85486800e01503100c010131280c50044045500c184611449204044221010350b0107905180003103070b4075031804427141d00c6168039041c2090f801e80044c0940854a810010944880c98152900c0695840030701d86e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 435351798 1250 435350548 435350561
    0x506160f06050906130f0f0203100e100f020f07030e030f1f0f0b0a0501081527010b040f1e090f09051b090a0b01090320030c01090b03041401021b071701 67
    0x8000050801c10700c4001400c40201f05280b034409816a1a4031840c0964202100d068600429158001d80d405010ba5011482803100a018001f811030500a10000030701c5940103041d0010203002503941a102c0e030703650403c1880f101d14452000c45606004428001d043c0c50400700c051403425082580b41941d004545c00341c0540c1c02006403105024901c0c00c0011141c0400160030280d40e06140900702241e5140e288070340075005c0c1c0c10b003203100205070307403e00400003100141c0c0a107100c0c46050000b4080f001c003d0f401c1c001183c03041c9030710407090100701d41030450840003540602c1c000da1411500840021a42c0c00600703466000d2401e0301d50740c400401043c0c880c829451540d030703401000540043c100e0161940b00001051041c0341c03034440d0300c0d10780d9502da00c85129218041040c01e03940104503101c0c030301080703e02c81c200000c0ca03101c0b5140c0e103044020009804003500c0205090010740281604c0348095054450b03200f505011881d060034100c1701180c85d10030600a40000010443c80552000014003401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 435353048 1250 435351798 435351803
    0x3021c0908071d180a0f02061905030906091501060e030312010323030f0a110c0306190b0d0309030b31030212031e10090606050d0b01090f0506160f0605090613 70
    0xc1c0742d1a841a1b954208180081c101243c0c40001400f8100704d18966081e42600404103450345662400d19040d107500c3c0c0302004080c6e8880d94480e5086a4103019600710950442c1c18604cc5610340d0b030100c100090031401107414180810200100002c01c0c01036160480308644046101004401280b01405ea2039125a08240b040c004c010003a1255240c410050041c51542c2d0300241c0d4289500307640042c0c18070900b40c1e40c5100700b8a945032840c0001e05140305032420000103c0300c4c651807108a580280c0403c00601c005854802450300040c1e0f007403281903100c00a2184016005000d0048144460907031000340ca00340c005101d40101c0d0b004211210084074007030280640305442c0040000c207068040b00004103108009000b00b2000204910580201005081551100707500c901000000c0e10032a0313a10080d141c1000b80301181040715007040001c207401d0714815640d1310fa580820414448e91344180110040550140c04004000c1c440c1682c4160701130300c90003065a980761904000200a80b101d281301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 435354298 1250 435353048 435353053
    0x40c031a12010905060702030a080f0702070b1b0f0f1002040e01051005070803160f080f07050a05090a030c06020712051c210510060c03021c0908071d18 67
    0x52105107060745040c00300c040404004610300d01ca0b95103960404106940e848096400484c0c40c0c003186401444159000c1c0d485100000a032810034002951404540f054110014000070400600d40048002070f81c40c6d071101003215075002e0b00c9140d00d60340f1881f070316400c5024050100020804c030748900032035086401c07604a141003a42010200250800407000c07000c01d00008002090000b21500041c42c410360302c10704200102610700320f02600164506ca1010104001682000010304904100da42c00505034640640c03074200c4080305540910410407030a40c4a03103a2a000002c21511a000c041518041d5090361415552140801071421007200c004200d81c00015490140084503900c007405038210340ba25444401803007040d5071001e0290a05135600c151140304100300751241d804180c000304100d144c81c921814154400075100d54400d08003d100d802800c070381004151107004588050014007080d140850b584c0c0c40c19000d0140c5442800017a40600b90002d5503245600f03d402402e100100701 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 435355548 1250 435354298 435354341
    0x50606030f0d0804020f1c080304050c0904021807110708030706060801052716080a02100f2703210807140405011b050601080c0108061f050708040305160302040c03 72
    0x700003003010140d03025500030300919103147c0a8000d00c189005064054180141c0c2c03828141000b60406129a01c1d02e80107002d07480034480180c685100d07201031814240c690003c15219a00c0440303070b401c00207412500f079104221000c102040048002c25030300c1d1246600300b00090355405002d0913594200c3c1c528603400c585440101043d1544084031181465050640e41d0800700c420035001156200d420000c540d1380b05044400440c10014030080e1070018906211958100e90b80b0300520480d0a80304201c070a00362003203400740038004003c07100c01848d80b0003e900100302d00402c1c441d0444005003ca01c0000c0c80050101c0c110318002c2c8501250300c0303011f1101c82d15050038a80191084904404420b00c0d40f00c120080e100407540a012950207003507403101400c0c000b081d95000504204025000ea48143c0104c0300007980080441c488103030b10012800d1494803662282440d4825000701d9101034901d0080c6482e107042c030030b8102000b40541f40308a81c00c000d10700d8040411403c41c2e0344424088003180308000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 435356798 1250 435355548 435355553
    0x60a030807031103040e180c0405100510020f0102070303151d01060503131407060e040e070e07110a1b060809070501030e030c0123091207030302070c0e04050606030f0d0804 76
    0xb00b40f07007482e440c12080f00d01d05981d55441502840b4200c684080b80000b200600147e458103110254121004441c148400c0c00c255401c03100040007441610f200d2030350303403106180c1c0500034811042608031b040021900c070081810f014014240f0402c1c0030418003000301020403103848005140b404503a80f1441c44905a081250586466101800311422011104188000600e850480191621110020303100031494424041c100e0b1185980e04e61186d4205034184150780400101c400031248600060035031a1124442540c4603905024000b0a60064100300002d000034001d40054910ba03001081d1196179603482c048800c1c100a503000720458210000401c17140d8072980096910b41e0f03031039007580c8c541700003110031500312200880c41c910444800c40701012241e403a84d007040d0303220384030901502044654800c003000c079204400000301032590104407070090103030a4640300003034171a400c2510310600705810541d07650340044540520a00c0b51400b94904114040762450f03001600ea00c4d02d01040d11540d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 435358048 1250 435356798 435356807
    0xc03020a030305150613090c090821040e090105010501120908090d23011b050f03012102090106020307021e0a0b160b070c03020c031203040f020f091e060a03080703 72
    0x5000c1400d0500c41090480060342c0c0d482c001e10b038180440c007030780742c06da403420403024140c1e892000c1030410300603c41802c10040c8400301c0e079900304101440181c04540e445800d00303085070017030340c1040c2620501e110402c00041e805502590594a007600c074015003102d20016401543d403070a8004051007428001c86d241414a0400390104510034034281c80000c42081510404800c44040c26615079120109800030802c58090004040c80904d0901d26007101c1c0031407079020b480184114011000001c1107101514490024000e0607640200101d00659403900000d560780c200e8402a0f105401e00e014003100c088603804a100c00d9a0094011020107207031016400050b00220f02d803568400c21902e030b800001e2481c91815103d0362094443c0e40302c454190a0080c80c18807000080d50090313001203c11810041c3c0b01c41170340c1c0d0150380b214940c007848405202150140341c210300d4164002c416281030103941d440010118200c082c100010a60b66030b5064100201c0c8811b51102030701d1500300f0046080806c0c0314 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 435359298 1250 435358048 435358051
    0xe060306010e0907030207020108090601080d0807022b0e0a030c090c030e010f1e0501030305040e0612070b0a0e1503010e0c19121a010905010e040f05040605160c03020a030305 77
    0x50500000403000d000c0803074851441200c9180001c0c1c2c6c0094030100319070b0003610161300130100c44020704c0e04c0d41c14910843ea403803110a152909100901c13000800c014800c0182d0030907504000d1034002e501003124201e000e0503120040c0c180c04200c2d81c90950302c040c241038010300100c1e40c0001021041c01d1070010f002009110492900c010151504014440d4110901882d03c001040c0c6100281a4005254002141110b0907000560b5402d0900420200ea8002d01ba02c05442102d4240e043c4c41e181c0c540001c550b117000c200f840480f0f0244100014858010101074039024500c0e88038503c6841402d070410440b108000c9601c0103030f02043c4018071103034102e00a1142d10032500740b259890803091069841c200160f07110800001021840201a402c44600448010082600707440b40000625400a0000580c6d40241c50400020090398001c0ea500c540200ca01c111110500300520308280c03c010b8090034041b078910916142c07403800064403d21501900034200c0e090b50207031481c10125178088015040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 435360548 1250 435359298 435359311
    0xb030c1309060e0d031d03251a07090501031812110a060204081006120b070201020d110d061401020709020f04150c0605150a0902210106200c010e0603 66
    0x360303000750100045091051000c01c45900004240c0c07035001140003002d64050b4030310400c081c40c0349095000510170020544040e051011046614000041528940740034040d101400d403c0040604204030340e040e8421501992b5540d440014180c0c41e0f20064040e00c01c44074801120140001c0d10b0000f0503201e01d54521417804c0f624060000e0005128038a00e040d010740801d8610a0380010b04000005e0100151002c0581034042848894070b400391701c100b0000700e442c0141801c4400400104034510039812280c428410400400c80000950b168104980244a410040d81d28004c0c021440c500300d08510201c055050703000b00015030800e480900030390403600d040e0b04008814440418544c400104001010482e036450488071941da0400c08152000600813001030174000001d842c840e00d503026100241d030254031300582c0d158114149480c0140300440c0041c0e80c150313544004900d1315031040076140511200b640358035404245045c0c650711101403401d09808102c6061045c445070030302001641e40f210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 435361798 1250 435360548 435360551
    0x2010b15041a0d0c0807020705040b0906010813020406140319080910020102040306061404290f0f0a120b090303070903020d080c160915050906010305040f0c03080417010b030c13 78
    0x600f0b00141c0582d0282c1a50340c001c40c0c030360f0040050b10769040101c40c6c0200000c85060080b0400b10b808224a00c0000c0c0c5a41e04000c281400a01ea00702c81d500d845007801c3e030250080020703030b58030303600010280c0c03500c10070f181b00f405240548a590680781c1c0c0404503e40d000001340340340030420401c000d04203031004c0036041507540910001022400340c1c40f42c0d80c000d2003000000300000491304200b00403225502048024022240384940f126100c1d40c48000c11414151a044035440300100001e4415443c2041e05c0c0d8480810311010500035803281000240610540310f40c0c015448410f081c1e40c40340030031100c2000150f41003404001500e00402c00d00004e5000c1c01d811450004281101810400b010700084094a10301c101041217030005d2050310b80701008050981d688a08280005e41010000b9080074105629440494140001c003401541785584c480ca8460394203940c0d140a07e4280c2284c8036001c1d0281481d0702009641006014664400f20b0040140122545240801003900440701c1000b0303a86 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 435363048 1250 435361798 435361807
    0x7240f09081515010c05071a04170102071118071b1506060e0a0b07151508010e01050105040905060f15030a08190201150e22030f02010b15041a 63
    0x266042c8040003801120501c070850340e150070703960f58000e00900095581006182d60030702c0c0111794046100360581d000c4511850070a1003901040b022401103402001100100341d001362100b0805500510003280318014125200020074200080150410074041040c20400c0004044610621120a07a00c000d51000301c60a21192281410f030403900000400c0d880e51407a0130720071a0740100700d0340081c0c201101c000a034142403e00300d45d4140540341005003480c00c0003070740345030301313151a003141c80820340050050100d25a603d603040d010700b080e48500c0c8195480d150021866003000e01552407000d07080001400142c031190410b03a03900320010600d2840d211420038000250303405028164105006081c1c140d22407400c000a091034410300d4840401b561300d4032642c0d46208030306d01741000440d4920b185208065a0f90b1404107201144c6d4582145600c2c42c03081c0344810150070080501e2014102c0c0d008000c1404420140203115800c00708000428038140300070054007800c0005000c601c0d04845500381403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 435364298 1250 435363048 435363059
    0x80415050403021e121b072c0906011a0903070f1d01142b05030a0903060e0a020319210309031101110d11120f060307240f09 55
    0x2140c0d425182100180c11200c410115820602e22a503011034140018284e031401102078000c4511548031085503004a040d680c01c40d00000f400311900400e036090000c3d20558100c0c003051605501d030400501c1c10a07007080443e5407008005800b078140c8105801200e204002c00e900c44420b41c0110b503156506120712400420101c507010109001094215920b14404007004e00c5030180c080c05030032000c001e40d84008030107000e40d2044800f401f20150b03040b49407c6602c08101c0a2500802d004020b0314922000800c115200d84c08003600702164001e20082103030f00c00e914903049c5c0340c10301c421020390701d54454600b50059000003048c3d04034075886241c2c0c241600e90032845c20002c04a802c489000400e5542a9010625401c5240c85031002c8000300200110740701e10009603680d0040702c04c0c001303040380c0d2100740f02250141841100d00f18104130100c0300b01ba01c1e0422900c6116002221034601030b0081800c000b40005c1c02c4180700c2d111008503103000b4010f03c09034500f21040d06c0f103004848100485003000090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 435365548 1250 435364298 435364301
    0xc06070e01050f0325020c210a0305031003060507050301030c0905070c03120b0d0f11010c03080112030512160207060c030806060c0114070f020106211211030f030114011e080415 78
    0x2c0024179030040c15440d803800c4104a4240d5120304180c0d0b4542040342002205078000c100c41007069410705101da2239454903841c40071243d031b05800c0240002c0c82d11040c0700405420001450407a84500b034140c03180ca85070841e40050320710585880d004505200700f408000385c01000401000e10010b000000d54012900000e016102d01706020380b804992110410180b0030207a0780012604070030300f042d403031400180d58010300c000d80502c900401d00a44001103800c00d481785007101c5400e480480408890304125005d21401901810310001512811200041603030143c071410320f0241d05910740280f40d640b41814080247d00180e070810895584940c4500c511407003066081c001d004030f1759a00d41180031500c000c1d003110318581028600c040c0d55184082ca2444a0121183e0300d039000e1116070611001c50801c1c0e072134030004c0d00030f4035880c000810b5481d900c2030f090024604035102d544040902d451041c00540d2041800c851400710020b40b1501ca01c90036000d1481e160300144940e01c02c14624500103c0d6a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 435366798 1250 435365548 435365611
    0x30b0303190c0212160612020d140711010c230408071205010b0306061f020c0616031d0a03080f040f3b15010207090609020c06070e01050f03 62
    0x4140c240c00400c00354101654040c00000240c0000c206004445035105d0324569188500410091003d8030f4602090090b019187d1400e01d400701481391408213404a81d01e60011181400081d440b170a01612103001405401843c011946900c05c1080120f2410a0482d410310b621031f800250030080001d0045040054400400d103c14541d240784e0043d02c0d1050030b4a40c00340103140300f64010000e004c61030f40c8a0500700e030b00e030108001240c16901c1d06c8030240d00300b4047c5100d19038003510214031140e91018481d44901080c0c400da55001010722440054080f41005020064018104400c01c0c80010853b0000f0705580011303201e09824540c0d50002e05154402c260001e424114000c00c0d907048000101d40074400c41d00b1204420401f0608420b0b06100c441d000400090b0071101c0381120380f210364000c0c40715602900380d1200600806860303400300406540191901c1d6264818600091364407071040807da801860142d4a00d0320b030540c44400c0c2e621940001d0a0b484c204001007080031702840350900c100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 435368048 1250 435366798 435366847
    0x10e06160c090c0f020309030709021c0501030819030501080316080d0501140112140424021308060c0309071e05040e0705040513080d05040311100e0c0a15030b0303 72
    0x403e1940843e40003d240c01c5280c000e49081d507200307010720030450ba004030300ea0050ba54071400058403a81214030031010740c601840380b0b0300d83c03070700c1d100012003030100c4603005040c0c0f00182080d0005030204030800710200d8034240308843e015001884032030310040740e40e00035100d40b0740507032441810329030382000f00000c40b0001e0740100ca0030300c81c81d041c041c0709503000300c400500700820003000c01c1154441044841030b4000140028150788500f107100d034803042c1000200a08004968085444e190f103c0350190a118050281607420300c58000000d844000304401c4a101d21404000303088070502c0c00c15000030300440c000408600e0b040414002c07441d0340f40c6124039403807542258020100301c1d20340f00501003100c070060030076289404d000d100c45c40440d2a4030304981400c411404000f0785907031141021200b018002d202d444941c0201c3e110703c0b04803245034000c007168010100c1900c02c080600070070860012400c3c0b280d0b1281c0781c28026070325441c60003940010741090340039042e245821804601c0d0f031014800e00690 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 435369298 1250 435368048 435368051
    0x180304140120031e0a02100b0301020f0a12050a1b030f110703033303020105030411060c0615270907150908070f05032d190b09010b010e06160c09 64
    0x2c0d0841c1103880f0156403d001c4c0004192504440c004002d4070b40d0a0742c61500e44103902c030082001540c5007503040b1014100040c20817a202c240d841c0c030042c2201600d42900459a08000100e180340b80317240304000c01001d40a202c405a04d03000d240c02e07805084000085000982d68000d80390103d40404002c003286842035500141012500c45049440384880b01024200e40040030541201e504048507241500e80900342030743c807540d8a00e009a0070b29903002c599a000640440c1030705d101d00c3d0024180d070107040d2044502114654201c1481541c00e21648001340175422009241491071120448035000142c40c415141a00d480e0000d0002c6240030303c1c40040060180798080013001c80a0044001400d0007054180d4500e240c500000d0781d8100c108000001e0507403418004400e40c00020340c2d07071044003001041c0d80d00111010728401c2e20610008083c0c852a0300000007411029041c8950000084140c46090854035001d0500402d50400c040c4100741815805a1300041100c4403212801414600b50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 435370548 1250 435369298 435369307
    0x816120f030c0504090914030c0115080c0108040f02010c02042903060903040911130f03110607121d09150a1a03061e1305040b18030414012003 63
    0x100811690105540008152034014a46015588032080303408507440e240006c41da1001500741a4140040e98003070a10034400000c603e25504810340198021001c1e4038441403005946000341921164115086400103218000240c0054a603a1940079010b0041c508000035058560200e011200c1007a058000f4445840000d17201d074404200c405103800090700507020509200c5609942d90145d40a0b04603d551105032501c122040310f01070350340003282d0104203882c0c1d90340c40004c1000c0325110b00007a07682e038600b5000c000e1103082c0300d8110360419074003038015022584903030012100b96a0241c22840000e400140314600c0f551045001c3c1d0141c0e81d2107a4410b0301c0c5541c00c080004603000c0740d100c465a10b1200e9001244d05806800356540100252020003244202e040e0480070900505000c075882985030105088280c0070340d0145104034416159400f8644a1300c880101802d0324000441c4541d10804c421300ca044118036141204800c181440740c005611050550b00b4072070650110b0365164008034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 435371798 1250 435370548 435370583
    0x9050306070c17070f08180306012d03031b0302070f03050708010501080d05070f080906030a1e1e110405040e0303090607030219081806090a050708070b04120816 71
    0x3480000a960020300d19490624035503520100360030f8401c405801440082602e91007894454000c007c41c02008040d600c40c0d40c0c43d00380c4002103403114501c0d500003040010180c001016079181020959415840701c4c0510168802d66200541c90028200c046024003e4001000402500d840002e94812805808414100201e13070f03084a50592004039540e21120010f880c0070342000407103c08540050800b008801241002403503880303514a01a0801d0000040051b0390940d81d004c412030718418042e5508412210000c1800d41d41130013880c040d6500a9a810401c00b126540440c0020001100140c1450741e100300040c00c491403c070380040960000000c0010001c01030040680c00f0005080c00c5007400302038858032021044880c01c8200348860800498401103078801099411400c10f001c5a2240c03410682254039800300d502e04850768801c01c98045900c0340089114000c1d94080b203c12410a840c240c400100701c100400181d035a404204251080c03180c1654207050000c0c0198a84c044404205 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 435373048 1250 435371798 435371813
    0xc120f090b060307030c12080c1c0f02121b0c040212072c01030507030e0109110f0909030306010302070804030b0f0f150a030b09070f0e0702070b04061b0309050306070c 74
    0x402d40ea120b6004034109200282103001420155100786103000d14000c003600e440f60240c8031b90100360308503124402c43c4442c2a980300c180c01586121a9880c410210780c1e4132005d90340da0305040304682c074180c810300c10b0301c215400b02040344003480b0520003282c400050400102d4220f03400861502d0080c1038410400c0040c0360005001c036030b20f21528050b03003202604607615540400c8141c50441c105500c0c1e4010401461280d0009a80d04160704020003044c500c2d45818183c401320045002e01850a01e11885681d00c5e01803007281c031620044024524565a4a004400130f502500c0e0495001c80c05000100120700102440c1d0310405661060002c60f04090042d40480c1c0c1000706412215030840300d281c03502d5180c5065200c2104d41c0420f04046944641d041581004050b4101d01c034514125000041c0400b00b801e482030281c0166000c1d284034a0b2201850710040c46503000342c40100c0c1c68107984a882031401100300801d540a8645000b08070b85a00029080c048241e070041c000407601c50355a03081c0710a9 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 435374298 1250 435373048 435373051
    0x180602120718030b04022130070615080703031205062706010504090c0e1206060117040c170102030907050901210f0b040b0a15030c03060c120f090b 65
    0x8038102044550340c0403102d581050300c103020040102548001043c02c546401403802244120803400c41040201d0400040c1d8800c0f410030341c0c1030440d40e403909204d003401608141c4035103e5030646030b241c6026026200c50000d0700f45810030401c0820051f40016003210288880806548650340b4a034100e1b0480100905840c000381502d03106240d0340b11040c207200c4521480b0313800d00c41c02c1940104542e40b01001614140116401218511f041c50a41c80b0116401000445103d4003240c02040700f0495508080e902d00b02100d116000c200c5104a085202d580321b2602c03075025116000d00c082c0c00740ca8911040b036040d94202404000d81d0080240104000144009005080e040e601420558500310701120b1510f450b800c99004250179042000c14400341886010b10307513130440b07503254140c20545410740c888101299104e814034946008960390034110f078141004c981c0c00c01c0c01d80c480c440c1180c940b5070040540d0681c0c8020b00c116049084551802c0e4040d031002084078000002c0c1c00c03140d40c00e200140c680c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 435375548 1250 435374298 435374311
    0x504050312010b16031818020904061217030a0207020414070f02010507051e0c15011e180209030f010504111e150c1203010b070c092d18060212 63
    0xc0622450800c9804d907440f10400d2a010b160080c1da041a1481d2040c00c14480c4d0411607055180b19481c001781581ca40080c03144420540302000060303a10069540c51450000001700f803a00386081d6054420101c074050360308000781000061800100c2c2d40000c003225441401d5240701140c8004100c03400d0307086680140e1070710f000e000900003894202001046481034450a1801d40035003a4002c0c0305040364010744003608a00d500710355040c0083c034140541a04244117000508440c1c1c0301c0500c090000568031422a070700c00741004010801e41c010340001c0d4004030035103500b42c4901c200bc21794101003406018050741c0506000322031801c102041c480c42e641102e00f61070201441c002240c8958841d010500e405c00b1000110580380c00d41e00042d241012082d454035092a00040008104056041d00a000051141c0e00440b91a03550780c41ea103050340c08504040070781589865210722910028407061402903440d4000007900e010482030554150050b0500fa68241e9000c544001a80c1c1c004003000d41006 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 435376798 1250 435375548 435375569
    0x100e060f06120c040f020c0f070b070f11040f06091b02060408070507230406060f020303063303160e150c030d060303031b0e0a1208070501050405031201 67
    0x540024540003012026044502070400d002a80100500a2000b14000b0f44028803d01c00801c1e04403020019402240811105000d04921440302d18030001755001210b1400700b0503810400380c0c0d1581180307403d0201082c2c0d0b118092441d0164207541304d11440e40d884841c060009040b42c03d007004082254074154500880f0310000c8605485603800182a946c000c5e44540482d59036207180c0b803d070b800c1038581c0e0301a000395444030340900801701c0328088044450308103850410916a035a44101c0d060b9800000d00c00c0540c0080000c02d41c20f00f40745420807840c003020500020310381d0b00e8002c0100c4803105003000000c2d040012040c0610002808008441c07a03045181c4900c0000403800014083c03c4500c04103e4540c4000540901e088824010b460f5664410502006901d035242009005000604084001d03401c18080d828004c50203442030f00d444c11300103418802080c0c18803242e001420301e008400e58404070140410f800040d001d0150a104a104401640e00c1d12840d1110002c0020103801004500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 435378048 1250 435376798 435376801
    0x204030b0c040305061b1b100b04020924360103090c0e1305030c010b010e040501051f03060e0f090d0f0516020105071502120c0304030e06030a0b30031603030504170705100e06 77
    0x150760703808034a14840040280a002c00c1702d00459103005100cec6819005900304110a900705440d104116149000c6080c44080c0f01030302032000440031198444002010f1030070240e001e000749034002040c00d0307002000410400c0625455103e85203150804003e0218076911200c1c12550765a0180100c2c00382c040a440500c07543d41850700142110310072020003a900344132803421a864a1294001070000c08071003965010351306008880111550b0111003e41c603a02c91003807586003252040740400c1c2d05050380d5584a0500d40c1c4404004031081103940305904115040c80384402180d0211031220402c0b1100000680d1381c000400e100c441100000c0c107078070450809004200101c0e4220040740b0035a8400c4510076581c1d0340d81e0041c04003c290310490b072030f00725603281001304180b81c11100c030b8803c6045000c0028142089814950f603a0f204e08020810305803c02c03218440040c0c002c1c0c000540103403040529103a13040d450b512001040c0c0145005855580c050910400c220700c451140b0000c2c0703070900e0f0103090103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 435379298 1250 435378048 435378067
    0x6080f010c14040504020f0409020f0a08150a0608100e010b090a050118050603063f0a0c15030204120302150f1314120d0204030b0c040305061b1b100b0402 68
    0x10b009a00c030344e500490300080c603008a2510941290041d1242038811929210140e800b81c031140c10841c602c03000b055124011610341c24049000c100701f030000500100201c0d0034076800702e401e020301810709801000b0740280807070a0100130203454042c1101c1c40005842d0150001007200084490748000e0610070740c20101d42d0482c842d00450070a0341c0e0140d4690745d036511610041588821054202101c428050b0142480a0b2402542d2020703621210030240d00728100c00c22480d11102c0f00c2800801700c1c42d07403000030062100c0c40c0045495030841400c0050800c0c1c0c1e12107500e100c9040240003140180c0112132a911241034508140350400da81e80c03100c000d207240803440c00d0702441a0440241c90f62407403020b10140201c0c200241f4140041d80e0f044d0a483d5aa98100c60010350803a00086560f69642c400203541080c000c01501e04513031300725004001946468001d200c0b09942a929940d58041c100800c44c40e0b041940c0440c640002514001c004005000841d28100c946c4a0b083d40c0c403460040011400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 435380548 1250 435379298 435379337
    0x50c1e060c0c10170c0a020c060f0315310207060e030a0807020118140a0204060b0d0b0909060601110a021c05010506010309020a15020a0f050c03250303140c0106080f010c 75
    0x82c059079607203c60755220304100781a450034401030358441e440f09c07001501840c0341c0031080240d4040c00b185068090f51004134410413814606480303d03690042c020700744009461a008a6081d080803d8080040c5170040d030352540004d41e844000401c04603440040c815100690080000f03a0004040c4000c001007050020104040254100d010b0110020003c2152803200280b208000882e802401003250540c4c502c140703001a084080c161001610701503007240582040040d06219136a0040035103c0340e075a42c8010342e5604c400485804003031081132040c00068840c00707141000d86007442d21000d02541d161401d04d00395500103010904144c1480c29000c0103071540000c0741c040e2180c40c82183c41c00340e5201c00880c80c100d00868060300710f2550b106c095051240106400342d400c40240c0544203480381c2c8101c1e8560303140d040d0300c0300e60b02d88905040401c04244030b03210b5844070080400c0b0203481d0451203080309007500c00e940c00140a076000440f06111060091180c0529502e090402c4400c98452200383c0a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 435381798 1250 435380548 435380551
    0x13020711060f1908010602010609050105030c090c0f12180a0c0303050d0b0d0804050a0602160b0307050f07030306050301230c0c01090c1e0f03050c1e060c0c1017 71
    0x5000700008242200c42d101d50005a40ea01c584802080d00012150300b801441c050003846140059483c1c804040303040318940c000d1a0690f00058028001100c6803010310201210041400c43c00f9003041c4050b007040c140140041c1032990303444001000c0b9090052400c41584040108481d15a00c40009007000609405d020001c032505820180e4480d0b0350240c030380317000e0080070301c0c041d600040d40041c0d8806c1000c0c41000d0002c2d504180c8150704800d0f1514001c1e81d566480881c8807681c001403a408110583e20003004590000f018607086017071000b44003003200d2a4201a8044012036203820045c0400d04091080e50040f10b00c44c8003901e0146281100c800f5140005014030014441c001600808e5001c01d402462000f80d008440da502c040c2c0d61080380b1049184c40700013551036100d00600003441c41d01c520518050b82d4001014080c03000ca08001c00520f6001c1c032150200036079008191f0b0b41c2540d6050007808404080c1405440814614010401c04152071000c00007481403621148c10b201c0390286403903 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 435383048 1250 435381798 435381833
    0x51c0203061501030b0406080f01060603020f040902090607020d11030622020d020301090f0305030411030c010509040f2004030218070816020307020a0f14010e031f090804080a02130207 81
    0x9100b010505401280503103203407000183c206007001d4001640e1540041c0c89200018150000c0180c1c0d91200400c03030aa04ca02c101150ba1840184018405050180c0c010010f03044004c0c0002d2420060f607003c5581d80601400c1075500c04114a0903014500b001e200c460b502c0000580e901a994120180c0409910300114010340103d0160f00c09004548096206800854101c250801d03542000e10b0010304a0748119822100d00703003040e030069420304000802150810058644130709110f204014040200341000c4041c042c1600d48138070490703250f41c851007280403600c080035407940c030b41c1540180121a0072107540c00c007550b24844100461558000c0e4099040306100507003201010380801c003249036001d990400b952044051100080100111700190203c640045007010a2042c030401555259415514507405800202540000380c0700c40480703080005900000040204603a02e031009107804c942c102c41035a41c0140d00f040305602c2c1001d00d0035000c08041c0025482e04182c0e0355060504125521030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 435384298 1250 435383048 435383071
    0x1005040b010c120c0c09060816061704061a13020d06050303120103110a03120305010905012103141c0203150603370509060f070f08010b0f0f0c07051c020306 69
    0x100410891204002c0d0006c3c01d0410b070074440c0507221b140322a113031090341c3c02051f5002024000028401c0c01001000203042e1044044c1c4402c1d9100e0b03d8890140c4110a40103980030100c1c1791042856a965050034850301a030200147c95045c450140c804a5455402031441313580305000c69034480c0f02c040e11080c1500d601c0010b0412221004000c691600d91640000f8844104d092506141a40c9644401d049441d62070043c483c1d660b84039405585880b070140003100181d2000011008240030740081d440301046034010034904914100c03008030725082079544e01c0c0312a4000041c4100c0c000120450783c103059040300c1d070618606210b1411040c98a41d92414071300407000580300c1c0703100324259070b010200f80240c80b41401140f818aa58648460084800814030315690b07000c070315041e100b503014860020658850106030303400d02a84640d15007106010b882c1c0300c20208103170001c0714904c0d00641003040340d00e0014000141010100411803130060b851a5982d4145001c4a0160f41e00017080d941243c441c025 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 435385548 1250 435384298 435384317
    0x32c040f02070f060207060c0c0816020f03070f14092401020309090f160305060a0918061d1b060d09060e0318030f01051b13030b1005040b010c12 64
    0x10a201038011902d0180100c25409400ca09101e5590010484948200d80411500303080003404ea54680b5107020140810700b0074003804410001800c1030f0344510703000502000d0b02040400c0001d00e4654641c0040902c030000400400525560f01d924080d1030100701c8441c007941c80c1428082e0000851270755038100000100d80c142e0700c640d000303000300d400501000d0852100c074500004213845690080d41e51010b1000362124442406101c1d01c2018000c2d0b400411030340311145000b26001c064444100000294802c4c22001c2000031280c1c441c0748922140203140c1c9511011030303410103003851009480c4e10b10300c05200c18166510380e1101c0440310550103180d000901401e050402070000c0c0a03040c4144014840003d003e55107000b50026081450012011100b001141c5000c490030303240180c40b0b0380484800000c59030701c80c00c4940041d1003843c2032202501e45c080e03a00e403500d00206c0400e480007200d00080750424861030416010b0005100c90a0070322259604803607454075880743d092410303602004150390 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 435386798 1250 435385548 435385571
    0xe0a03030203120c0d06060f0806010c080301050d030504080102031003022b03052a010b031018030e030a2906010f02070e1503030d0518210a051b0604032c04 69
    0x1003a03a82d02c0c5c13504102003080035254003000d0800704402e418400420200310000e6040e41c4140a4051a0395000c800c90381142d103880280000c0c000591000c0b01800414071020541070000d02c040c2d8400c050401c03c0c110b0a44c40e60040c4030840006807124425026102045e105c1d02c0401c103000c0000755030500e0480d90b00d80c1c0d2400d1084213405070101c0d0950400c03034044180c140b0501500710071018003044080d907007040b0107040c5000854200d0440c40700e421081681e02c50100e03000b5904000c265a01078261082ea000340d954400310000d01140302c1011940c521140d40b100c00200c40010351025080c00c001d03000da0411180603644045a100d048a0071004600041c48001d01080e41003081102800302d98440250110a44c06403600300d459043c5500c088010503403918000400c00082d00035418070001800700f144104446600000110302488070400803e60001124414007545000c180058400350810703203001420310010081c0e503d400503142001e001400d00305000c4201e400d90032140080c4400561 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 435388048 1250 435386798 435386821
    0x120f060423030a0f030c09050a1814010906030b01060c0510111605010b0310090209011206062c0c0a0905061b1e010c17040b090106240e0a0303020312 66
    0x51244a030364007011800f1600c2d10b800c5007100c1c280700c2d0f10307031001e0000a03407807075040303484210a00c10181c1c807461806080140c00e00c400040c90740b0303840205010400d01034107040d01c0c00400080e8002c190242d0f0b106030400c00e114001c44054054810307490070b401c6030340454580503a2091070041601440e42e41c1c114419220b2030350411180c3c0760503445821900300030b45080c124000e0031042c090300d010740030320782c845811700d00a44540c101c1e0301e0f80107245807021703401c242428103509a4001c01325665951210085038a109192566240100000c011050030300c50040140c0b0040d005408400590002e01c59504c00741c1d04172070981e05848040d5a0381c3e07140c00c1c5018042c410500e000c905088680203604085e00300038040641c0a00707000707032035000b03111701c084400c41213070282d0240c0081c114403e0380c5004a0000342c204c101a0360864685070020400da071f02c41100302c49a201c040403240031240640c1400381819040b003040c45035803d080f6109400e6074910384010392030384101d0b000c405c5400341c0d0000164a4181c0c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 435389298 1250 435388048 435388103
    0x3081f05120a0c0b0702010203120c0d09060b240405010e0d0c08010e0f060405060f0402040b0907050a110303010509010311031903020c18070210023402120f0604 71
    0x1400d0380401c01e001c81c0c15035126103030000140c403420007526001c0b5800080d2401c482c02a60b041e40194507091100004c0c2c0700150015282195600f0200203d000c00c50580c01146955402048c0000310707c030001d403c001c02502c08595000380030b00d41003040c45a150386403060714112882030a22180301e2a003140021401d0551600040c0450b012050204010031305500c1020783c0020b5800301c0751b003210910307181c95546000703d8008055511180002e100e200f56955a030f900544090001719441c01c0800009000c002c0494144001540c0481c144d00c082c0e84c0940d48031841100c2c10083c41c90740d4142400315428010501020700b1035004000c42c2410740e24100900403070995190b4540000304520f1800035207031000b80c0c00c0d19115a0640c1062000c6030041d072001e60041b026a0000c01d02000e0f01140d64000c0c2d000080c912207144c03c0030760040c004905008413402d5922144103c0c0747c42000d14810000302d407045415442069100001c0841444400079025404c5904410318000d1080c0010500c581441c0703 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 435390548 1250 435389298 435389309
    0x70902030c030906010618060318050105070e011b0f060504170301091a0609030d1101060b0f030a0c090302061b0703080a020303090705010f1719060303050c0c0d03081f 74
    0x10000410000032803110140d80140034940035071384140d0383c84008441885031100d503441c44020034181003200601076070204c0014a000d5181c060188129120503007140c03804c0310440c0206001c6043da00c0250380c00780303400042c03404a60110311140442d0700d03003030102001e45800a18555980000c64244030713000039a2030805404892159481d81c41d03d5048015010404209440921720382c941103503480c040059440b00c0e140500180300080940030704030781c80d20060340c0c1d9854555070742402050402c40f48004058a07290103000c29681d05203005820304076804d03c6186400c00c400c2d0202440103030f68020480c0d00050040d819650107940c40f80009090071ba080d4001000c0712000220b4520071900800554480d4400c841555803d990702c00042d22030301d84001c40c001c0000d0701540c20b880340b400c910404907007050342e19141064443c511940802140c900c1d40064001c20170120325030501d05804c0120341000c00c800d5444500e25400c90761702a02c02c480286c011b00b61044040503c600c42014107441000030503 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 435391798 1250 435390548 435390551
    0x60b04060f0303090303020c04053c07030b0117091f0209090114040b09092a090f01030c0b0f0301060e0f041e0b0103061518030507091a0f010c0201050c0709 69
    0x30b640b4500940401d0325444110094090300c001c3d5a2546401e00c02c5074460f0780501c0340d03640c14014007803004203501108411a2840050820011103141ca0303600b080f8800d40050714009807812203013001604444410300d03045080d030034410402c071042d40007040c040400b241d500d00428460340400c0d420700182c000c2001c100c5d0440b1106000080010b60a403031400000c0701680d08004030440341040c40701c2280101c41d640942d601042032207507961420a4288800410010b910074491010000502201c5050b14101086100b10005109201202c0140c1008203011040c02d0300d407424880e0b100055010500c10a028001803401304815070312214510044000c0c001c000300403c4400d4940d0345024003454011122042c0740412400f25940a0b104140c00d840f59101c0399029007800060456564906200100203012041000400108100140b0b000741115a5010070100d4000c880c10070884050501c55200d540118000c0095907005840781580540a180003a518085030f20300c1e914100480d8003402015 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 435393048 1250 435391798 435391829
    0xc0303040e1009020c060a0b030a0b0f1302270c0c060f0c0706050f01031104060806130203070b0a03090516061e05041502070f05030606130b01020a080d0e15070c060b0406 75
    0x5c82c1c0100b62244a90142942040310b40001c2c424903584441c1d150f002004440c0042c080b4601c4100d64045540c4600040c0e5948a0b04031540d000c00e03403103008034000c08908500c10140400c00000c429060b81d10400b081034240c2886408108540d8640001e0501ea03030010400d030106103516040d1048500c95504441d081c400d40c10000076070751018809120540704200070029091300c0b45800d0150f1000c8590240007401c00e925074460041d03450110f610200d0b803500c00c1c410006820348223200500521116602c00107045006428001e0420300c2100c0b48809802132148107015260f0000b045d150241a2100e00f4040c80284d0b1009603214481c54205400c1c20100290724164590b0000c0c91400b614099032070100107035580c0d01407560700c00c41a16031980c46202c104030030410390007550102c56948014070450300c0040d500e132140920b0390302c401c0c1040c0c0b440c0c0e200d8040220080d4104084150449207059052241c90404402028030700203240041095844a00c83e0995035200c0d0402c02c0508555420900f04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 435394298 1250 435393048 435393067
    0x308062b0201020c01021b04240620010c0804060f06030b0115110606030703020d030c080307090305061501020318030a0c0902040602060a0e070e0403120920030c0303040e100902 78
    0x4145500300124014490242e0000180d4400309054a841d514003000c05802902c030005c00c03014280340c0c40001c0b9404d82045640c60a2a602280d03c8001d2141c2c0d21100d0f0f5030030900340465030564000600c45610307810322403844c5215600c130080c1035100350000e10010320701c038120074a54050a51a400509400007100c0041071031400003030000c10084160f112203400d5440003400b1500c881045407200d130706400c200020000350501c0c070030320718501d4405e280400000c0340c0740c0d9504030150401c1d41e419000131069181401044070811042d0b1b00000c218905c031405480080c0002c1d40e9228547d40081d003004280301d91461500d0400201105a910160350b000003038035429454020342040c802c1100500c28640400c48410240c481c030880c00307540001514000703041c2011400c41000140084041200c024030b060603111f518410002d6861040e40c0032044611002420750b0006007940c00d0368800e070049030903c007140d5800011603044074a0107942e40311a543d14030710800c0c6c00d0780a6204580382e90000a24408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 435395548 1250 435394298 435394369
    0x320010507060504140c030705152a0c010906080402090106031125020108130305070201051308100608071d0105040507032d18020612060303091801080606040216030806 74
    0x441d06002c0c04803041c021b0781800309aa94030141c882caa8201d400100501c0b0742405400081a15844840f0b07060404031844a20040c0e100b809030050140d40c1040414100d29030303000d03907a0002003119161041150130b1079000103980300010303c00c000505599040300c2d05800850000e84111500c00d0806607000001644000c8020204e00d03001c90002d10208001100804011090031010307405a4500e400e040ca0bd600541d8507900030803000b14051203805002074102c004000640c2d646200d40c1001c16244d1811440d14600007041d0403010304640100820380c0805200c0710b1250454004030307404134a545403000b080d001001c01d031410303500e0660f83c080a40f190100000e40c14100d01c0716410100a42c3c1c5a5946c0200b10a003000c0d4002d40c406001c0080642e040c040c0000250011401415a0f2038035117840c2c00541614a0b401c8040010748000d801005800401c1c0003256203e0b1059406510300240e42150010a0ba100e0b403000302072140c2031000c60380b9a00d402c41c1448600313023100c4010b411f0b141030f0081c486 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 435396798 1250 435395548 435395573
    0xa020c130e0304091406060a080a0207020a030609080705070e0603120d0603050610030506010e01030206090409471015031e0204080c0d030f200303070f180320010507060504 76
    0xc010354404181c0c941847e00132184054807950302d00700c06446840e00140030f0361200c82c0503a4031042c2003202001048003441400c2409100303024040d0303503d1041c40c100d400c001c00e507481811480c0b40c2c070041101d541c03000710b5260340f200f106001c04d030f6450020b2072410005080640001c4c3c2a0703c0394900300050308210400040540c0d0150040f522541c0c0d0f5582c040080080c24000203402071400d1100004a09261700417440e114469075512a008500020344810070b02c643c1710090044050b203042d00d030450a0f01d802110b640f04610380e89403152401c1c0c1620111101d041c030480a1100381204080342c1076109901c69845e0400c0f13a02da4101e44254951504041c3d081805a42c0c400d0180e502d4441661800041202c0b0f540d515499160130440d07040c0051380d1008100c1c2d02d108500c02c0c0403010054081e020700c01076200e0b807030f15112064003010360305008207100304c42190030424401c0c0541c140003003041c4001c0000702c0404100d5a6070310501e20801281c0c180925040244086c0c01c000030301c81004a000a102d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 435398048 1250 435396798 435396821
    0x3040b090a0b0f0702060c2406040e191712091c02010b0d060e1e030414010804030503150d0f050705040f02041d06060f0304060c02060c0a020c130e030409 68
    0x80c501c00761640d4200b840e610414049645294040103481c00508108021700010100f8000392079102d032080740d40d113a0075103050809441440c1010100076051600c0c2c829201104201ca009003a1012445840b2002103c511805008000b02d00c000204402d0710700d0440c1c0640305400991503480c100750652a644088001c40a41e00318840c09018215070320510500d6500c3c000103180d1055452180c98403030040c102010078180d0b6000b4042008000d400550700288001851030095654a2401020f42800510303a20003c0c108826031050001081d40801561b400c001d010010010903500000011080c55120000500404e0080007d0050003c013050803421100d00740c90034080c90b40c3d1001600e04a100340d0107001c030904990000080100185400d541d44040e0103454103150440468042c0b9150b041110110b0314240c540c5803880032568140000ca4001040e00d04043c1001c04065000c3c1d1107020345911580070b0f04052208850390300081d008552101c02d2034003602d03a1a500c078190440a0000301c00c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 435399298 1250 435398048 435398059
    0x1902060a0f0203060d0609020112150906090c023705150a0b030d030e011814010b04180b0601140a030c260c1b011104030308060a0e01170a0503040b09 66
    0x26080a0305180c022a4441c4c00f00070211040c1c5001941c540000700680441681040200080861100340500ca000301c600000c110300d2040a01c0e0000c0e41c0d090700c2c0c00b40c000c00f040300c0c24454040401500024105045010080309007a044240301d54909040281d0142031650070f5500c1d0300d04248040818400d0041c88150b00424807070380d442100005450010080c542c05a00ca01031020200d4440c1d8004801001150001b064800c0820629050303481c06107000da0301c60031180d0203820045400d2064904030f031025101440f10064894078900a54055800035111420190000e0b6041c0e01c50407114120301001c02d200c6454000c4503900900421305045101c010450160341e03e80241c09040c042409034225000d0251941e58004003420160000ca914403000303098040c0d100c800c6c200a0140500e901010110992240d2660800a1405070007070710b001e002e03914130322051108511018626041d07600d00700d140d403e91041e00a00a28109000c58041c199000100740840d08800704d000400310510300300e4a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 435400548 1250 435399298 435399311
    0x307050c10021b150106080606070309050402031501080a060605030a1e1a0307080c2404080f03120705030f040308070c0506040c0e01080303070f030c050706020d24030206030406111902060a 83
    0x300f146407508203015280106641c000000e231145001e000a0404030703c03a19258641076912404201681c006a40c8080392481c0c038002c90303525503404001d5076030140c40303080244045450050090603d1001508440c12191503658150341e101c0702d940d032062040c01c810300801c0103c4110000141d0304d00105001c0b0300c01d015848001403220b1001401d0075a960004008090f0142209034889a00000b81e00d600341c15030080c000003c0c0c80d1341c00d00c0076408071140e000c0607640c5c030007117110b445049420041c00d19080c05014001c1c4910058030114040d4003903410f04201c84542c031003620694204030030400050480c4607000801041181c0b40c5509e000701c0302c0c202121151643c903521071940368007040700c0120024207000081e06601d8400e40001c40921001c2c01e200f86814040c3c0c0315101031341d0201c1a51002d050b200c26000b0304400418910000b00c50002c094103e6050450b030004d21684006040500817540360980b40c1d860b500f10340c045480c5010942c030514131500c4400300194032010101c0700c088140349031030b4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 435401798 1250 435400548 435400573
    0xa060b0405010b07020922120507110a03080a0f020709150306050a05090604200a08031207030204050a03170c01020c0f0c090114091f0603020c01060b04030203030307050c10021b 78
    0xf01924031459005050540642e40c1c800c00714401070f403c070618841d0915184511021400d0591361680381c0d007850f900c5039035403030250034508040d00030a00500d00400f0044000c10204044c0002e81d076154202c3e10300f05140c4881101c04910304040d5400610b9100c1ca0100c088103440c2046421070308482c82403000340b0060796104101c5003101e5003242d01e02c4a94014100080008004c2c403a070f00e441c0d041080300c6c04075081100cc0800e5681c02035411404940d8400103c102c0c1d01d81581608660027405454290f150608200114000600c5031100030080900c02e1403092151002038103450020f402000215241c0c0b040b0341861b40d07a00700c011001d0056020304109800281415045503050342c0144000031078500820060207103603a001018684034400c040000b10b000800f041e42c8600801141e42e002d41c8560400f180c141c07c45049521641c031495040200300300513100401907035400300d84c40c1007103521000701c07500c01414070030000d43c810001440080d02490000d4203c1180c004d840c410011a1000d0702000d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 435403048 1250 435401798 435401819
    0x170a03090b150a12050708011e05061207061404090c05090108011e1502010b100f020d050711090910110a091205070510030b030609250608040f060e0a060b040501 71
    0x498034243c0103142e00d10288200d4540c00e02d02c01300310703101e1402c4840f00340d55a2201421190305d59144503c04d00340c01caa012110303101d805040c1d040507003120620490808050781d15a64103851042009001000012002900c1d04509403001040e030700009022042824100400903400902064042045d001c004951b01c28a40c03600700c200c20241052440c02d03418684020310034016026540e00310341d2600b2895195403108501c3d4100309000351181e582070010000080d00b0040201120802c2142c00e20180c400b14002010f482c3c0d1540040d50310a10584446000c58241a00100322445081c01e004030030040c0c01d011002089140404d594000320700f601d401c503104615140000c050b141c1c0d0712103081805145080e071101c00d5500900c1c200014240310000120b4242007040b19580c0c1c8a070410303048441030411000020700080441c0520510013400c00303c01401400c0c02602c054090201282460200b28070b503446050844103074030880c1c109881900e807690103080004c02450003a41042c000103420083e0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 435404298 1250 435403048 435403081
    0x50d050301030c06031104031b06030c020a03200f0304330e2806030b12011b0f02030d1d070e0c0702061e1903061e060c170a03090b 58
    0x10003d403c81541c0b4011013140035200c80c00c0d1240d8100c0c0d0801c00000003030021003503107003444103541140c92a1740c9000b1000c1d04a03506100e0b21015500a54260300029a000e0052850f03112070710120b9000c8440565950719082c1c00354030300003c43c0710005002c10702080200e1505000c811407002c2d4003582488000070000209071010304004a440300a03408800c0c58a000b4000c500740d01200341c881421a51501040300d2902c035840007011030b956070440181c500300345e01c0d410031100700e110084c0b080d056184200740502d12000c100c03408015029512418a920903c101c3c0c01c51400803100b8800003044c0390515813112052803d4003000e1007824800203045403403054640c803079484000d00d60304085940c1c0900c00a5400130a60001120b1030013214a0b4900b500f00c050310701020324500107480c0406405c4040e017116101d4008110a1005c5080110400207880c5210151000780c640001341611601c1c1584410040c865401d11143c8041101c903e1198558400c660b000d004450390b688a444604002129440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 435405548 1250 435404298 435404303
    0x9030414010e0114090d1e1502040308033705090c010206100b180d0b0615030112080d0219050d230c0f040308030a1e0b030c01200303090604050d05030103 68
    0x604503031400001c4031403400307800040e80162030458903202035514647d01041d6480c00c04088105815040f0500100d005991031549041c0030451800d401c640303844c00180001009061001141041c000010040440e080400341070300c1c080740b440c003c002d980d00c0007a041c02c40e00542544101d5040d40d400b50301c009495030040795124071a543c10350408003209204e07827040c0d4a1040d0840000250201c0d41c40368200407003103c0c0200e0006240d8102001009032892070141d420030540300c00d200620225004000303d05c916580004d085684601099190010380102071440d0003080f144d01c92104041c0e040402011002d80b204000c100941300c1030031902d0040081c42681c40d031a0780d0a0005540c030450b080c02040404100110b0381e04199503a0b441c0c02150307004440718a401c4c0d84900e8050b1891702d40742402c0382540c15004081c065035400e00c01099580d4503854210b03040000c4481400049404140101c040400c0501500d50b070303141c843c138869501c640940382290030b441410700c40240240b10b84141ca05883c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 435406798 1250 435405548 435405557
    0x6010318110f120619050907030809090402010c14010615030e06011404091506060f051204230712021003050705070339020108010f1d100504020309030414010e01 71
    0x10071040910107a1900c2c0050760b6008010a0749050700c2d4002040300c1ca00c14900f480f0070100f00002c600c0c1c214103031000a84929406da1003213a09000180181007560400c0406869294003599030303000480c2c4540c3d080c00003420b062041a580030b00400190000010385901c0040c10300560380c07c60084080b207070010781408c02e40e00104010b001c0e440e41001891032000d0300500106100c40b05889030b12406040c400d051000075902e0300200704850300100941c041001d5402c100b400c22030060308050200070001c00080418142881505a04408421140b284480c6800300d8801c2a01d807444042c0d035201c0544140d10480a00e518911124804e001c2d061148443d940c4440c24442995030a44040000c10010112612040c0c400805120000c0707240c01d50b0940c140e1003001050840c0009003480e141030b08081c2100d2103206c1c007449101d04010a00c80c07900360b48400c40b020780e62800a103c5055181d9040150b0060001040c0f0022110000182c030a51724080100009090701800644003080708244150104 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 435408048 1250 435406798 435406823
    0xa020c010e0310020318151902030709050420040605040e0a0c091509120b04061406240904020310030c09020a0819180c0f080f100504020d0f060506010318 68
    0x10750781360040c60700806d034940e030700c44d94500451005060008543d0900c1190300e0440400030ba0030580d507040c4600c00200395045103942800c1d14010a900060f000301d5003e80c0d2140c612000c6000750f0901150320300c058510043d155a158070008025601510a41072400005804206c510310f103441618403004560700e0700d00d09070340b8001c5003558012486802009016900800003098004200c0309081e59106142c80501450986010000c99028142d1780e002a1184410060640c8814160719001c1111078446a450320b0003460030304840c0300700806a40c0060021042c44600100c589002003524410a00401840d071038a039010203c5c0100b82d4428001001c0e40e011982c04080440d0310828854500008513035903200581c1005480c10b0040f040328501403024040101600444880011b002c40801514024071211009580e60105081c00510290f1b01c002080440d80c50030100e4040e00d510084914005801b17003490001444204c3d0b030140800d0034044603a0115a110045c1c40d040782c1e100c0b5501034007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 435409298 1250 435408048 435408073
    0xe0703030e06120c120c09031e10021911060f07030911060703020a0302060105192c0103031d15030a15091119050a02070905070201020d0905030a020c010e03 69
    0x71007084806030041c004000c80840d0160480e0820f20440c0f03481070301c503039602c070440c01403e400034010201c00c2c0854080c4103007005640c0100fa0f0034410107940b80100d1107032210304101410000304040707401b015440000ca00502c0c100f5005d445800c40d1058594030b080002c5002241c0d1a0041200e1900002c48240c0008011a0003940140070480c01401100106000540410442d500008040c0e01503031200d8918010141e04100039405800166220301c0a1485840110012075850040420084102000343c40c20b181d55070300050b03010144802580c5a594a0401a020800080341c850352840000800b00309400d10246c880704c00040390303580714a036035950b001c5100180b500c48100307540c1d0a00c107000091000201e0085903c0c030b007031040150707507203030f65540824651621645e06003041c40700074010401c003550089030718002c4807050000468a9503500030100e00a100c0c41d01c0c42e441491605100e0f005200c0004050214007400350221500381801c0e4006559290700e000d00c2c1e81c0d050380401c0103c80c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 435410548 1250 435409298 435409307
    0x1201060b0307050a180816150903140c0a06050703090602030a0525080a05041e140108070c0b040f05060f220203010b120105070206010909050c01030504030e0d150f0e070303 76
    0x82544040c07074101c044205c1c040384c051030a10b0313550044502d81d022241007a06103a074819a18024010f0940b81ca0a40140f910090414075072403202520b4080c00b081c0050f4055824007402c003143c40011b050001e600d40b10750018106401c003180540004201b01c10102d0101e0000040321003042140c0c41d01b90404080f101000400c05000f20300ba091a081c003003260f00003600d410090a80700d030031901d0b525100c600740381030740030100f20000c1440d2072000c2c085800c012482841b103000b207000b1001c1c03804071400d6581e400241c8240445560080c698910001000207100075044510082071040d0b00355070880d202d602c83c1151011040e00c90480742d01d09880712241d030703040403103240d41010b101030004201c2d5041c01c00083d00d0700140c42c803041c480765182c0d01008407203076041c04002e0141800c0c034020016803905440d03282e5110403046445050617a21004141458092400c03a0f0301004001c16903600031802d49000e40071000b00100380c41c40541800c0c4408002d04480c003509034402065001000d90f10320319101141c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 435411798 1250 435410548 435410557
    0x7170304300c09050915010f03030305182a0906011223090f0d0206040807080a030906092a03080304150e0f03041809152a0e1201060b030705 62
    0xa0115004400040000c180b600709000030b011251002070145850102c0904200050358144802d800020043c0700c1c058031410000103490f0140340c0000c80c1e0380d540210820107000c42c601100d0350b01c04c80c54400e540c102c0664090f500c4d03a1b01204540f441c5050345043c07021640e010340380c0034086003e04240030002880c581c444e02c3c96028650090040f000c1c40a6210581181506c0c50b440e11f030003c400c4200c3d09042008080b055503058030040c1002d14141e1101050b9024500004109000000c0c40001d954440e4000f80507042e04000304008000c3c462030801c1c203200040024400e04941084d040680b54400c944a0342140e8204a9052840e03449030b4400e2101c1c240150034101da05da0740c000160386203c0800940c0900380500b4000c55a490a1650314086101e0707240c80251085c0c102264030f0000307184d0043e1451158070070140400c0c1d0000c600c0d14044a00035000d101d00708403804022881da603640c4030580400c0b81c501030361010450514a10b0781c1c1e00341c4c4c05c1800f512406010402c0070a061070b20480c003d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 435413048 1250 435411798 435411869
    0x3090111012304061109130b0f10050c0f0714090a09140303041401060609060309030201090813321005070605070801082a040b0406120507170304 64
    0xc01c0c0300010700b41401d180803030184040c00100c481c204810080a44030b4101242c5103031801d81e0401503200f000500a4a030400000c2c0c2c0107071985601526500c800f0b9210150500040480b030140c0110034005203550070040d0402d8040c81614208450706c0c1006c00e0360743c241c400180d1000106180c503410b010500c4009008054020b0303907840300c00089403094030b0050300e00c6c10041c081d65130b82c103084c14410000020043d0001c5136905d000d00802c501c0d6000b607521802c8543c1410003140b0410f031410180d0040c0070000002d060f00500240b0600031100c1c0350301c0581038403010024101182ea400c17148500c203c1c80d0003088591007181a090301014509441a6001d419641c41c0c41464000c0565420060700c80585041c0f010403a0f550040c8150380f01840300d01c2a0520300c180b400b0001000302416519882c1d217010450113583ea400e030141464a8641091000d08207402c9910200d0019213000c075a902180c5c401c5680c048805a01a015480701008072001c0320300301d102e01540700c25030303001c0d2a420042041c40c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 435414298 1250 435413048 435413051
    0xc0103150e0915010602010506010e1e0409050c01091a1e0c120711090402180a0902030f03040504050106090815060f040504030201140601030606230c070915050609030309011101 78
    0x3140c0504012891188101c03101600405290f50f600184582c81a0820410359040000300f00059901003209428680121541941007403c05403040c03030039102d8042c00d600b284c105001e0405100001803032502400081c1d9925030481c2d502c1000340c0840c608040350030550b080402c0400350840c07000045802e0608104a158038041c1c60040a030303d49555000304001c0d1300c40205210f418400101c0503441c00c010240c55042440c5000e50001f02c40c0000040d10382c00c4039118601141116209034084401603901604803400108903400c8a0703502e400c5885858862800e0400100f051071082240100f01e07180f6400405049003032901000d42d031030b00140a250041780c0003900c00300d140d8441c040c01d4041d90080d000003c0c090040024001c903188006e01035814182441401c00034154030810444070785415441c0400c200703508100c0d84101e03104a6140c40600c1c40780d00c401081946407a0b001c2c1a41d9465100c0d19190030ba07450050204502a101ca220b5154005010a41895000c5c0102c6001614010300 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 435415548 1250 435414298 435414341
    0x50a021009080a0f2006041221170c041206150f03050f1e070e0601050906040e090607081003020d11030604050d120b090c091f1116030209011e030506070c1a090c0103 73
    0x50710308140b03600130810b400072b2025800c150001800f8000320750800c0c1c12000c5a842c1038200034014012548081c0300912266990740c900c1150020116400098a0784c0c0307103104602a41c0c0d00340f02e980c4070410000010305009015481c206c617511510b2400c1a06424000741024515004030601115001800b4a05014040204101503503ca01c001d1000d002010300c103641d00e0612404240c41d0180040201003440040f10500c8a190500800042180d504032a51090120903180c01d440080380e00c18265058882d89061008110010511440707000c48c03940c0e881c290000d40076120b415101840c0840303800a04c0480071550981016004140b104d2010700809441e901c4054100c1d8500e9140300042d0005407041001d0750240c6060001702c10b40301084101246046c110380000d50006010300c5030007501002c690001141200350a016001941c100040d61042d28000f00007900c0c4480c141022100814400b26441d03940c05200e1046000b14180f400804c103004034900150000c0010b88810030070490340c1003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 435416798 1250 435415548 435415583
    0x509090d08151f0e130e241803040810090215040b070308061230030f0c1c0207120e0415140102010906020d0b010e0607050a021009080a0f20060412 65
    0x8525038100c40050000144807071b80300c01c800e041800c4180c2840840801200000c120340759000383d1608108021085698004e003880424a5807040382e00961071030007119a5020481d80b29031002d03290900030307030340da81c010901080e00da82244142d01481900950600107407011030f102c0c800c00360b0b00c214041e001003030b54401c10715400c0c40d00c84001c07603529043c1c1c8403552003101d20841d41510001d80740200001c0341981459071603031810040060010719150302c04203429541e4030a00520782d0032448030110466441803241407a0702e20018001e941404925518240c1216007054070510f240b48c46410034915400707003403c400e81c00301140d1500d824115901e03603500401282d06440203001140c2404400a50390350003400241020805070802880380e10244200300125501090f0f02e0913480c0c1c1113606c0c14803c1340190054451000b0764000905612418010404020b100d4280c55000760007201d240380b8000c140c60308021610303010014030390040c1c02884200101b10911001303906052042030311038410309008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 435418048 1250 435416798 435416809
    0x60f0d0507140d062105070902070503040e0f060901051806090c0408010f1a0103090210030207020109240e06031612020f030906100506180108100509090d08151f0e 72
    0x140400710710742d44100170446035400d186940c0340010103440c000000595511000c3e22072480b8810021110380000d5a6010040203200702c8000e0032030211701d030003030307040052003005c9440084420b1030064140b1070003c01c1c140380180c407050111021035215100e56989005004a96201034074580e2079813018000031076240300c28091130318001c0c0902c0380011031886c0d011007032900099a0310303014141440c103000c00700941c40b851558900d07070045040269a4103900c1c40102c440504070750100d02c151121451a801c0c2a220702100100400c8654440c0c866a03003c0c810401c81d8442682c000b107840186c21064894039010740044010212103000060414101d041004442d40c401c039100d100a4025400b04460740b46000c584401034030702603a640b41070102910070140301c0da1642503014140500b150010300311058150748a8090540a0140380042c01c01a401ca581c44110f0008c0c4000b14641c030700012400701f40107410000c280070003060394515031040c080e041720395420110603e0400c001e41040c81c14a8440c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 435419298 1250 435418048 435418057
    0x40b071b05040c110105180304031e080d0603061a0f04110f040905041b06020706120b0a06020303060f0d1a04020303120403170108010c08061c0204050123060f0d050714 74
    0x494441c0044035213001034150840300010302103640c041102078000040a000000d039400d8075030180c0080c00c621b0440c00c0e652034103001c050b00208113a000050040300e2408642050049038801c60341800842003141e5101800e0580742e41a40e041000d480000916280a8010b10091058684102e1403d2560a18014194019000800301585841c148000c0114072068401010030b4110f48010850034803500070b44940b9075104020411910f03004080003001c1541c00480380cc0c1d001021400c0041d540c800c065103c0d00100c400600c1507018030801c4025080c040090049107500280414031303030020308450203032508060402d80e01444280321082815201c0c1d104c007805a03000303071124130013601207100011100b03405800c0f4407640e9040c402c5002039a500100510742010b0101c03010559059010174006884070541d8010358000d082000018200308c0a1a00710100488501d105007040c03201c1003402098401d8901c1d0780c9424204125031003602d000e81d40499009803031807403c007003200000c1c4140e03255a080f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 435420548 1250 435419298 435419321
    0x30b04020309030c070501080705070b18030714010612150c0504080303010f0503061302030a0f05030c070e060a060f090e0a0207020d140f010b0607032106060c05060c040b071b0504 79
    0xe11852007072010003203680140800d2078841240c5c07400d270070010402c0c003904400515180120020804c8a00c40c605a517516203040700880b0b84800250515075420030144c61707503407969440c20b580402d410000f03840c0025001d803c034842c1c13079442d234100d04241d0041000c04411030820000380004110003070248000c0d4000c11000035140142810329082609081c000f80941642c401400b030342034016103020a2024602e80c0224000c0100304c0242000c60035441100c40d5030005000381c08002c180740207401040380c007990b01039034020302141c3c07508000e40341f48814000b60b1001c00d2420f4000c011541c2980308066000c16549005400c0050b554042500024500d2040703c2ea40c00d40c0394950a81482040743c600a100d01c1d20007402518500804221030b885000009020400e903140600d01420000c00b030900f10710502a41000050380d10075000709046600b9408a03114000c072004200f0140d00e02c0c090710281c030384084155240203420b58441802510100f0510501c5d9502400040c01c0d0b078540c441da01d00040b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 435421798 1250 435420548 435420553
    0x10061d0616032c0f0d050601080706121116050c1e040e0615010509040e150402150901091401030f0f201206011b05060c07120c05150601030b04020309 66
    0xd080b03242c042d00c0c0403814140000030400d2803644100790403042040c03180c108810746800b040c0103040004030701e4079000d0200103001849000000125224000b42c601d003103901c1c0740d461010345000c40500c0c100780d42c000000a0140c91080c070001c004042e14a04411015124000316455554600041303950f01034050780c3c441d40054084c200c000f283c1400d00400d0b030788040311005001d55203855198000030710300000070349041110109000907540c86a9003c0c4030000c044104803040019204152514100c0469040380034100c94840480100400000d5550f40107050315a0003016081c1401e80700c00160060920b410183c544a0911a02020b4410f0140c6950000f00104195103d4a1441000680011010245035081082c59010003500d91910342010007440c191469800c1481152140c4a840c10007910f03134001e03001800a000d400c0c1005108052080741c01961540d0345884c240c5e900645c4070400340c1250001c043d013602120301b05a0440d4080f0f8141030018400040801040483e001100d0401841c1d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 435423048 1250 435421798 435421837
    0x1030c11070303230a080c0a0c050a141c300c031506020a020112020c1203010b0304031209111306080a0c0914010b0d05150603040614070810061d06 65
    0x5020592413030605021180c416841c1194062000744240d000800b181c45012004c01c0d4030000313601c6100301a48242c0c00c4004c503414580d141c10303c00608150f21024462078414400c55210303200440001c1108422140c50750514036840c012030402c1d003801d001c655a07010440d46040510101c06100f85d00004e2420b03580024940c8020480c80702c200c0e050b8000906650000c01c00900607070f4460180070404803203610143c1c0f0740c4010000c6c2881c00780e40003860070b00c601001c0000b003072440e24000910f02c070342c1c002d41d1103841c03d2100350800411070300407500181c12940b000d0a00d0069040c4416008401611040000780c134a0750b17032410900344801e040c3d044620890303040d4100701c181d5280c010707504807a0201d01484d40952500d01002050304c40e01405040841c0c4403c0003440031441c070310800c05102c9000c4c0c810b583d240b8081c60040e0080104c1000f01403041e0f0540e0100351042d118090440c4074074504007040540f2414800c0543c0c503e08403401140d07061026543c200c41d03d403030b448007038441d080e48402c012801c0b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 435424298 1250 435423048 435423077
    0x130b0403030905070b03010b040b070c0909031205010518040624080d1d220b0d080702180103022d030a03020721020a0311040212010b03090f03031501030c11070303 72
    0x4c0c600182d00402c2d10203428401804250444402c94044a0f40004199a1441d00380b9249805490581c0001803080c5045164170a054005501c400d00c4040c40d50100520f80e214410000858419440404506130a50000340011440c0e400072414203081003d05a1140000700210301c2d98070141c11019440e0010385030b024080da08590580060002c082c01e40100e13070301c11400b1990520721141103c00c0b8081d84200607010100680c0549120b1401a200b0740707031080e060809480320340c40250224028180076a41d034030311030304602c50241660390040ca15a03103200100b404982408440c9449410700c0356041307111030681d504000c981803880c800c0c0c0103800c1f22898400a401c0100145202c2581c0c450701441c10001079550260120540b948080f2201031a003010010900901458048490f6290240001314141d00b00f00c0186200e0030f022400c450389052a04103031901d900094400c0b010b41a5144000c0d0107540c080c0d004010084124a00f401c1c3d20a404800303246494500e9000ba004035002c48044041e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 435425548 1250 435424298 435424303
    0xc0603150301060b0415023f040b090f122d1015050d05071a09030a14010b0d0b150d0515070806010804021e0310021b0c0f060d05130b0403030905 64
    0x1070440c00a41200c810b03c21500302304a030710003102c81030000803000f400700c0e003040303840c034502c04250f0382d049692110780300c5508074000d40c042011144203144d0401804103520341540078074240c2507940013414148040b20080034001c0b00662411480004070a100a00c0b11001c2102c45102d410342000030900c4044405100200a41908890301441e1100502c1c0c0102c1c00010702da504a0b8a1400c100c0010043c824180000c2d000e1040855410b0041e81040400c0c40201e160500525207407000030072103404064108050254480002466600070700f0000c0c080300407405c440c52400d6805044076040420b40c1d40d60707500b07140300401c81031541601d09061006050344203408660046082c00c144010f810139800007a903e0340c2c240c41101c00e05c40800610001510305101d8600b031807244007401e649640b038400c003800002011a44406c4244101c002c81659450507440f0801c0740c1d403014226070b107020b0340001d101001e00320041400320001c0c1101c900ba80010364401d40c40d407040f030103654006400c00380e924200c2d0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 435426798 1250 435425548 435425579
    0x51521060103180f0c09020f19120c0503040302010c02071202120307050703080403110405040209060409111002010617030702010918022205100806010909091109010807050306010f080c0603150301060b04 89
    0x40c1980b06000000c44820500c040b6094008503041a180c1c14042c0042200c480112440302b204c680d050480b449012600040590701441c400d400a0100090300b9400300e9541c0a00e2140d000a5580c1c902070740c0242c2081c00b13100441d0b10180068a00d801c8841e1505840d190095208440e00c4000180410038001070700c40c1c0c00ba8102040350103211500b001d80011300c414001400f81803165607211115010800584244214003c003c0c100b203100d10b0b00088007078000c0c002e610440d00007040c02e07420780e14501c1c0040304581e03c696050310703050229030070310343d05890102d4200d0302828965800c00800d2481207a40b500c1204000300e4507040c121450901c41400404070000c0c8102d0188002c600520030941e0b0018a1034054072030655000695a03610304000025040748005940c201d109580003150803000451414141e410a40480e01c890340e03100300201c4010720921808a02d5009444586420701c0e000c801950421030318054941351805180009007100c10b140d00105944d5000a01004031070307500d4000c507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 435428048 1250 435426798 435426809
    0x120607052d030712090206070b090c121b030f0709020708040f090209040609020307080a0203060d1b0e1303020d050a121d0c060708073009051521060103180f0c 70
    0x144545e0103c3c0d4049550780c05401c130001c04800c0c2510006070403880412614a104400a00c45603604103202d0070242c40d00b0740e200d4100d911003c01c0040d207485040000e860714151925600a0148034940300c1045c00030742285804894520040200040c2030f4419542c440207401e07140c20060792041910304020403254940d0040f0205ea005004012442d0f41002c89035600a0f02c1000150781d0343e0318200021a04401c5e0b060081030480801050300c00da079141604541540c3d03001202d0100c50300c0f90700da00d0910044422000b00180c0c020408c044030325119001070b140900c69418075010400e04c041c0c01d64143d800d00901072101201441c01c4800c018020440b94a084005481091400c04180c40f983c280c0e1003501d501800070704d422441c0d2400e4006540221968001c0c82843c0560700680045c01001400b4038411306114408210040300c6401440040740d4600f14a510700102c01c010900b0070813140c40c1c00800044c1070550751002d0008004075a203924000034800c8000c1c0e504950756240041e0140110f0300036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 435429298 1250 435428048 435428051
    0x4050307090614010c060f11041a16120c080d050a0b040b030307082505030c1b0901051210050705040602100606172d06010e120607052d030712 63
    0x1c00c2203100e01c6903941c040e41030030310f041141e01c217503820910302510140c840c007071040303140410000ba407868500142060780c42c100d0704510030700040040c001440c010b10031b140c50314031340c00340c802070000303560300408010242582481c1d0444404c035141c0c1c00c001d2300041180007003980c507a010803c05002d035216092242a0403038080040e0000c0501203940c90051080007001c000c8005414107070041e00e038000100c0088220407820851800e4900b8a46940048081d0307200e42c801c100d0f8a4003806103140100c0789621000d440414968039010410050080181000cac160380151007081c12420518064a4841c02045c0c684d07543d240c0c03403d9402440c215440b2a06810649084820311416620603c6004102551405507030507403103440350780700002c0303080c607001100055101c049030210701c031000c1480c401c1e5401d0b269a00301882d84000e0041074286060f551009411020004030b009008070082d124103810060a60602c2d01410804016403429100d96901500d000c01003102e6544c1c44401c7e20040b4046000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 435430548 1250 435429298 435429311
    0xf020306070f0e040c0201140a0603020111030405090c0d020c010f0b0f0306040b04060527150a0e070317070206070b01050a2c071202030709060801080d0c020607030504030b0c0405030709 82
    0x400403120010f07560711898503015582c821a1007500301041d00b4078844c20013089400c024204100401803880124089103144e0304000203203801006450859a0140c0902a41d507512107002140c0d5002e18111100c043d030a024044060700240306001d24406502400103021444004000107181107040d60b500ca89c2c441d0040200240380b4010058000c1c0d845800030800d51161708d00c0c6903914164a240304042200c3c643d50621a0a0002c0c100303209480c80302641610703485c0d86030044151100f070811902158049201040001c15281461480741c21000f8007500b0000c91707a000600e02e5000c500c0075201812624014403003442c002104100510103041844211100e03562446002108d003941e0030400d80e40900001d03030f81030042c001c5900c10181800c0841d981c1c0751103d0060b003400800d000e803c0c002000d40c0c00105202c040020760075040d05240d00e428030303806038642c2001095070010f0300c1181040b4092200100045000042e5030140d421060360b5900e4900306400d040c501161503010f01a606d08000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 435431654 1106 435430548 435430577
    0x120d050403140910140f07050c03150f1807050a1e05151204020f09010e010e0718050603060414150102011a0102030909040615030f02030607 62
    0x1200c1c0b8010341210b00003004540510b141c040c0e0003d82d00390040712040e005105d0342422017500f0005910302007440c00c0850303c1d500a150110380c25400201070850501d814401c2545c0b62442d40d0182800e41f03003c03c1070811480001d0701e03a254940c400507001c04801010711940020b000c0c06045141d503140e40341d07010040d001c10b040526401c1ca01e4a40c1c08078482c41c00a03c0c03080f901c038294400301d003400c50800903442021000383c0200d034003191150049115858100d0310301c0c020140301c06502415850011818110100280300e0000c0069491723402548050400c2c1200c251034043d10f50384e03200e64460022070000c2c203d095105814101d010104854203403001030440c000d50080e4028842400030038414183c55014a0780280580c00070f00500a46051003020654464090f40020901d00049100400034441d2500103640424003241004294101001655000921032501c240d50301c0441 = true := by decide +kernel

theorem cover : BRFrame.Cov 435251798 435431654 := by
  have h0 := BRFrame.cov_init 435251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 435251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 435251798 ≤ n) (h2 : n < 435431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
