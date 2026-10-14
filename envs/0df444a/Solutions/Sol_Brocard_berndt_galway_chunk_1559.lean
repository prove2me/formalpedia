-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1559
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:34:17.366884+00:00
-- url     : https://prove2.me/submissions/3b46cfb0-b625-43d6-a800-60a20c43ceff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 280215827 ≤ n < 280395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 280217077 1250 280215827 280215841
    0x5010305180613080409091a0a0603020d110607060c0509030c040e1005040f0b011d1f05041109060403050717151f090905100c020c01020703110a051503 67
    0x8480e0080196410404041d091580701625481d028041d014801d5620610908000d1210180c0c2c005003806c4800304040038040c1000a800380d408c030a091441481c5100040c2145010312030002940c1c8c015001d800c095029540e00e11820010070240c541c4080140908000141c19004a0213024a1a5203603501d5440450a140c076007400355124601c228102408000440000a4030b2086002c8020f0003141036225800d1000b00e030084241e01074070801c0c3e4880003241c1c1010b00e051004000683d00340b641e1080e5120b82c12695100c13a0107100b040111a9080c0411191500d83c1140c2203a00c1c07005a92468006188002500355004c0ea00454007900402802c012100203540040e255540c104060840906c440c0e030400c20050000380300452040d00170117081202074595a8140180803810001c10503c4164204180d86107009252100303c0c5080c1000746041c01e101090040001c18180c00410f84541542e40301340c07808001c07034080c0750048800740e4002040d03a02c64a450240c500b900b811513541e410135030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 280218327 1250 280217077 280217081
    0x1909140c031630050d031a10021c032418020405030703060905011e091704050f040504020d0804060f110606010c0f030c061d1c0207050d0305130b0301050103 69
    0x4002c0e03200500d4801d00c20424408500c0309640700c2d241d00d8941005150b98900c18201a4600c4040501517108440c0041c000541641c09040400030212841c1101100a4100040d1141044045005810070325680a520b0711000c154420040e0500340407550021a8140600c403c05e4051001c1254541c2101008480d0f90490103160404c00b0540c10351406003410b0101e0b550341081d11005040b1136070f5000b00410f2000a50059103a100307025040c02e207121080752244050b09204d01c06a840b44020a00c5482c6004c80e801160115140502a682e40f010484204801040c006005a0300300a0700101000042c0070100108007603d0700f42ca0b801c60480c240c0350020074185071803981e502180e10500600402d83c0c1c0018489112960002c094016601140350445600030303240001000582461040c0d5280ba040000d81ca00b806000422078240410441c10030040001218060740540c210000500079814400721000321140281082d40c41d000c40d0200800440000340d102403003400b0040b0043c4020360b03244c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 280219577 1250 280218327 280218343
    0x21209030301050a03150f111801020604230307050304031a0a0606080a0e01020c0616030b01030203040c031407032907020309091f1823010e1909140c03 67
    0x800011801c56042c2400320740600880c0c0400352650385030700e244040a170b02a82200c008111016814030546249039030340f910701d070800c42c45140342031646c01642c9203a510004d4800d20460300040a0110040765400d41c6064844c034184950b4980410404000800c8080008100851007800a44554039189000004051015010112150424a00304141903008a035641c210f0040c15001810310303000c00d00c030b034020b20402e064070155028400c03c0206031000407a0542c4400b080781c07800e014065080c00110200c2c402121300074000c88030b65200744041401010001000c051490032100d0160b2242c07100000026101c0d414044049680c4002c0c0c45100d445030000c0c7c010410b03000030b605080d007803000103d58450007044c400d8040c58950b0b40a6071041d4000300100102166040080000e081455020143c0602c0d080d0035180b4680d460b104a0100c150415981254044509407100392030f0070700149c260511045030000e140f82c03540034480100d00c0a406034019502c400005100d00c40180050604045103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 280220827 1250 280219577 280219591
    0xc070f0503070e010302041112040c17033408030a021e09010f122421170702180a0207020406060327051212010602061003120e0d02130212 61
    0x8074241c104003e01c0d4011100e07043d80c1e8126000b0503c022680065410760250b400d5014641c81c0820911043c40b00020b0541c050b1843d254100413a40030702d25205d60f0706e200b40108400954190344200c58500c107401508be0202c00409403a480c50400c603152014179800c2a529120540d60001e10a04112100f42d502c2c000c0d0f44562100c01e00301280040040e081d00582514201840b5000c400d046030264642d00c00d198940c0982501e40c80c040102003150180c0c8801d0144078545e001407040c0341000e200302800142265030021681d4900c00e03040318000416000540d00700d0b003103c000300c001c0d101c500692001074450082480e0050300c4003603030300400068642941c0002c046c0b43c901040d0006a0800301a000080550503d200c40344484c5441c25520b040180b02c10031035503100100351015440040485141203600940c22183e042d151505483c0200c0d40c81e01c0014002c84400d00000d0321580140c11000b0a40ca004290034036683c42c03a0042104911000c0544d4521540041d600c08542c146254844e00844 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 280222077 1250 280220827 280220833
    0x310052805010b0715110406030e0609010513030f030e0a030309210e1009080d0302090a060905030706030f0f090b0604110310030209040f080c0a1401090c15030209060c070f0503 78
    0x450243c0306080c40c0b08120b809040c0c0d11540241c0300c45909507030448210074000941c02da07611036039040014001c1040c00760f180f00720b000d14000310b440750005000d0b1178002d16001a01246422440d49c0030344150214501c13403401d064440301e407640341e5003050154964039030285e00d0200c7d24800710311b064403820100288007a0904250041c041701280d210700f04a440c02d100359048202150141b40035141100f05a202e00850710440f80076000865241d000b9015100040c0ca40800041c1c40344420348a254035400380d1905a840020204505071281c0c01c8041858000f01000498904201915050b200e4404056a5540110b020701a91381014482c500340c43c203c181d030342821070071b0989100155001d14400a1f1042030310501090a0103001c83c138070281c10740d10000c06550b03031540310403264070f84041e014182d482c0f095450484034612418000d414a05503c00e403014161400c2440c40001402d1900c500c50030140e0030b00512071141c90300b1004100c010362103402400d20610f4002a4580071820350041c6020350 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 280223327 1250 280222077 280222079
    0x909020a090b090a0b0f0c0106060c030203070f02042a0e060702061c060b040e07020709090b07080c0c030c0303150301060501050a030902060f03163902031005280501 73
    0x2650100c01e8206581da00300b00241e5941100c0e0001d07910300e0564101c5940b8810002d880042142464020041a01000c000740000ba582c0d00d0180c0c1c80d5615007102a0240e041000f030074001038031070030f03140c41e232280300501c0094940341c403580104030544084521100420340d54450602c1540003244140054012135401c1d152130200e6000c1446d0340510b03041540c280c0c40c0170012201c0c0070f20507080700c0d0180c4007144450f40c4980d580c100c003020004095525801500a00d2070110b80c1d4100390060820503a0402607100312500c07503540854071064000c0003400700700801c0c0942c440400050008180040039900210340703034200959402c0f900003c4a010500c070344c2c9412000c10041e60010b0540d2015032844c1000a100401400810114072598188075105900001044031450003011414004181c659a4548007000c41c40c00816052100200c61410020900303941200d44880c90100745640c40503055a465900c18070070700081c3c48054651698501c240e48a00c07407207204a03c2c919444004d0340344148003075 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 280224577 1250 280223327 280223347
    0x30b010915050d091103010207081c061202060a0e040f0603020909190b1f0b03160905030601140d08030a0b1f05030a0e0c030703050c1507080d18060c0807090902 71
    0x5840740010000f6141d441d60403039020f002440c03c00501017440a00291740c1d13010039140c0380001e980044a0701024181c191041e1a242c0d08512601c8143c0c1c030203c04072080007515808001203074018141000403c480c0200b80d0000740c4581c0184000115016404100741b0f00f5441040141c48004011182c030340e00c940c10351100d044449810380c050310382100e00d016054460400c103031140240981c10f0318001c4031880d0001040c044100041d842a404580c107000360624000c030482d01d0700e00300d10a031581940113000600001d291400d00303c61022008201c90419441540d980c401d079001101d104148a5440725200e82c0c07800c1c14013100844122a5210a400313924a04000d01079001c041d0082d44125030b00c02d000080c00504003c011350040c0c0c01800c0341c2c4026582c2c1380155845107842c034180c1c050f058070350104a04134580d900780c1e28281e50002d11681058a807042c00e0300240034034407584d5142101c0044002c0454168419142c00002c030340c0d5102500c2c03400100140503400560300c0803031a284100000300031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 280225827 1250 280224577 280224587
    0x6230609031506030703082a160303030c030209040f0e01140f0f1e0906160309020d0b2d01050f10020c0d1b1e080601062a060507030b010915 62
    0x10314050580320302d410f0f102c0c44042440e01d4034070380000741198800181201c6da194018203d82210740301004450390b12190804207901c64a007540d8212000f0505002480080e0180c1c00c09508408586001400c1c481050005030668100d146a00b8000340d40382101c810b101800e004030a0041c3c1001d920412034140b50300640300d0301e5001400805140c80b0000820702010794000030400d0100204c800d28505d00f1300303405264407481c054030740e800c103540720401100c001c2e40640030b090080c0341c004010900e0024952a01c3d4007400d8010007405a00048240e0901c1030006829802c010031b030420319800ea00c0d810041801045d17001ca108e454401e90441174848641540021280601c410544107a594000185003003200c00d00c20340d0000248504046010804100300d00b0070012070055040c603034030b41c2e990f54074800d91a00020702030b03000041c0400c100300e00d03280100e1034015408150000990100d03545503c2da1004c659060340c0c48000039440d8198100e542d17a10485400203000503100710400300e50305c5580a05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 280227077 1250 280225827 280225843
    0x61122090b15190201090f060b0405070905030a030810080d050307090501030b0d0204020a210e15071e120203010f0e06040e0615030c04151e0501020d110a060623060903 74
    0x850903e0100059008900c00e4020003016680910281884c1c2074030b00e000c2025144481c0c809014500e000b000844041c07080800c10121103028010f81585419500d04890054008004407900354000c003002605130340411454100100590f2000e4990030003550040201030302d5440305040508021070a1007503505c010203581c41580c12140180d455a003034505845000c00015119890100c40c866401400d007183c100b0b00d5000a40e800307582d009410381030210342450064400c1c6d400100e0120381c42807025401303840040c5844590408131300c0303d10115052016603009810410312549009410000c1454800003640c02a030103c030709100d1a642c1115041d51440010040040780e110040d5152403500c1c1800050418100034105101c1450b040d844140b07080305510501012442c6c0301c044000a480c40c030001010789505178050035006107015400c03600400106903800003400303070795074110008585114000c000c0c8404080c0000001c600e43c00c214050043d002d50310300560f001c22080346950b4010030740007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 280228327 1250 280227077 280227097
    0x3070b09030306210c040504050606032515110d05091507050c040b0d0615050108060a060f05091f080403030b06040311040e0a0c0303080f0106030c020a061122090b15 73
    0x50a020b00044c0070300e8122065030181d009464030007844180100850070310300c5600706030200c07011000d0400784544840c2140c0c45068881c50001d1040c072550300e109602c0c1413040c0c80c0c3d107080008503491001507420888d0400301000490000641d640c814105904090020b18001184a04195071a10380c07503111415080c4980c8075039035840700040c0710340c4d90181d80d4140c3c41c1c11010400c0a503003405030f6030021417190f01840e400701e0f40b03420000304030b46061f11407807007a907590b50b84501411105d1102680c85400664509500049a00b4803003400b05565010b0703040c03460740d5900c81d01c15051505014080321405070440b40180c4d401c020900c0460a602542450304006032400142c0242460300c450800700544001000c04080d00d81c00005d043e4000d42c7c40c1d01400448601b500b05990ba0f00041d0115120625132001582001c11308a0200d169540190150b010702c50b0303118644070100c0204c0207440d00d0003108140c03100c01040207101c0a100c0d0711a1105491080c1c0f072076101d40300700d05011001806804001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 280229577 1250 280228327 280228369
    0x1404050d030e010e07080a05011a0a090504020f1807080609090d05090a0e040c03060b0402120a18021f03140603061b07151a01030507120e0c09010803070b09030306 72
    0x356060b030380941c41802d42108072000d89510581307030038856449048515082d01d032503080c80040250b880205d02041c4010b0801405620503628120710315000d000700031300990740411182c000421039251801e0100c51818856440c581350310304288041c0c010740e40a460580141c41107400c00ad01e6510001d084821444941401034403100b515000070301c2c0340f030150804403032858640188810005500300900a5138070858062156034001342c1071004038090118424820b185410100e01505c0650b4400d1103054404901421084402d0300814090b850311017503200f90306400030020060541c580300d400c43c903183c0c182140095042c4000080c1c0d803504040c10380d40395a40100c0800c03e4254106084a052540c4203030b0b0020341d911a043c52100400e40c1d02011100c1c0c108004400740703d903100c1d1040e28818181030312060351208515102500034003074840602030610078481000720958401e038115008080301e0340119076621203441e00300302c40b68016003292003c1d8014400d111145c1d4030960307074010010f081196 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 280230827 1250 280229577 280229591
    0x604050709090816110a210b061206090322150516060c02030703090905040512030a1401180b010801030305040506030a06050405070207080c0d0b13141504061404050d03 74
    0x3034103e500c203107452070740003d00400140b0104001241c03154481c1d0380449000848555400c90003011103a8904800b900521400c61100002c45801140360030840140c041c8588065101405151100a4811004581c8041640481104c11300f003403040070300111500f0540c183ca8022840d455012034421038090040100c4c1090b00522825000b48000780c000105000c1310311038003000f9460340d012a6040c3c00113030715400b000c00c00c1a194080c1500903580b120080840c4000d082c0050419000030b40b8901d641ca8561f0340c200c02004a40e588540640520030403c026050352146440846814132015070500041d80300403c003007600a41928119241500d42070358a644003155034006281a800443e0302902d0241802000c1e540040d0f8a07007650110300480f8200101c501c10440307102c050f014021301d1000d07807000250341c69190410701069148910404a080120004a00d080241b1108400401d1907000100020b001071800b45064205007640032500908094940580b1141c17081e44640501d5110b40c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 280232077 1250 280230827 280230833
    0x41a24090607080c1005011d2203030b040f0f05090a020a0902030c07020a0602060402030d141e09030a240b010e040905151003050105160905121204030c0302010809060405070909 78
    0x81215581c403a01020f5440d55400005ca40009010038040c5080d5110100c048052140044464038028130201e41a40300c0b021844807000321382030b02350720118201511200240f06944540c01404640240c41e0400301d00e0710160f5041d1021a0002001e00c070301980040c42d108056101c8618440994071410710150380c0f0f0751030510aa01603c40d02d0402500b00350181c41c00107016074007148860007984220191070318140118021540e14454000c15445000f0402071122030780c4a480501d4940925100540c0c1020184000203003171415540090b03814205421151002910460f8074540043d1000700802603e004900024212840d00d1070f094000c40d61141c4074400d1210801c00e01740841071407141e007961840e1800508412003036922044a40d5801c00b008220b00b0310f40303001f140360b5412842d078a40c50403e20340b104101906005503030b40e140e03a008070b0300c1010070402400c00400180d40034106141c421442c1d40300041c200140104501892741100c000e01c0001140460010122000101e000c610b110f01c40c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 280233327 1250 280232077 280232093
    0xd080c0703030917040302010e04060f15020f0d0f09080106180f0209040905011b020106080606040518160501080903120a0507021905010f0b15030c0f0405041a24090607 74
    0x45805060400e20001d80300000c144e0b24002c01c00e8a00c00c1c0c1e500c0c2c40c580c103054144802d0301d01b00d002e56010244421014801455511711082034520705104032096401800315550070302c0110b90044001400744501c4900310341d0403c000e0300003804460020002640b41594060107035807035150b00d00d245900c1c1c0d401103001c50860b8050380c00d0890000d008010001240c64010b001b401000703519602114000ca003405c4640c010b10034001180d086402404407599807604000003440e00400441180300c8580d002c407601ca01c10001d00d0862801c03558000e000c10b04240000d000200c0050000c2d1803030303004214110240d28200c101c25004001c4450100703c50300c407040b0581c00d040000740403c0030307510302c1100c2c00217110054000101ca5442424100019041d03a401d0020302d02541b001c4445456040000c81c0c0764000c41402801c00b40409900980cc203600c0e040003a09a500c3c07418070124600c0044407c1c281032134004008400c010b888214400700e42e500030b504061502404174601d21070343c001701751141400066 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 280234577 1250 280233327 280233341
    0xf06060c010507030b09061005030a15120b0a05010f1410030b03013305010c121808150601080601090909060b06130311031209040c0c0206030c0405120d080c070303 72
    0x1000c000d00652401610003030051100b451007a110301616800304900d410804540b0300d100c1c0155030707080e10715a070700f0b081030019209040305c514451950400016072414000000718219205e1840040e2604208151070140c40c8181c21020b032491244800304443c8026480107c000842511103c0b0000000541a0001d1030700039100c1d0307090750a00b03110684482c4010f140c480000c9035031140e0500240000100c460b203c0c4540110740c00f040d03c1c00440d1010038900911241c92840602d400c0711401c1d42181d004da160301940e40300c25a25488040c202085080d11004590701607420b103000c140744d02c3c00400080444e52548220300415950704114814400d594001401c6140042c101030340d122103180c5803042400789403009881e14070007911070f9101446c0101c1c00800007804603440c43e047c04c2c200340c2000000d1001100305024401c1c100c0203107006031903000c091445020844c1c0e00c551501c0c0382c0f4003442118040c05081d000c00350481c06c201c028a0b500305005603040122200e989803901001e00e01a0010010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 280235827 1250 280234577 280234597
    0xe040201020f030d091e0203030405120f0709020c190b0703020706020c1e060a0507170903070203120a09060504030f030e01020f01090b0103150e0a02040f150305010b0907020304030b0f0606 83
    0x40000c9a2007070301003642201140502c691b02c4000c1203401d1410205012064040095150308200420046441d0070590000410024420344011102444809180440342d52052941d0340e008101403100600900c560101d6244041d50001000125558040384100003040e00051603800b00307550040c400740340d050340c4804100c03c00721040300c01c05005900031100c030109503a07943c5c03040000198801e5614001c40f4010031190301c5416000001d005401d212500050040526110a001e01c80c050390301000ec070596050025101039407243c1d003c074014184141c542004061110805c41000002c1c1810200c1050a41619208c03e20303420080c0101d040483c94440301e240340d030800d025a010701c090541c0d080d040328031559490310034160342d482d0348054420114902060390020050080541019040440700c000c8002002070703135009020900285840c950000d4502d40e545400010060401c410701eaa0060011700007541000d140d40d543c00303001c90300100030361081c9080328081900c503191036003507030782c2c06d82 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 280237077 1250 280235827 280235833
    0x1501181e050a06020f0a2303070b010f05010215040206071b060906020105070305040f110a1205010203101a0313030e06040801021306030b0303120c07020619031b090e040201020f 78
    0x8a8201050301014280280351107502040e100081c070038000103481003c88014000742100311019101c4c0c90b601146000005d4100d82080340300b42d18068244010441d461040080350841d504000080b00d408985801032815980000120300751810310007021a03002c2d5040320000da41d40042d00c1d02640c0f07044040040701516880b1480840c40c90740001420f000e40d0305950080096a4416034110b003a188190745c00342c0800c840c8050341c00801c40e00e05074105c00b2741000d403400049550764809002c00c1400b030101075445075030200034000344102e42c0e01400001c200303824030140d03408d000b0104403d45120183c5044002c040c20b0403600c08160068413203a107040e100410b116262a03a82c0d0b0344a0103540700f800c0035100080c80800100310503000340f0526428180140080d820309101c040f451518800251180010744c006100020040c0c4e2030200404010343c03e40c00f0114000440742c0c1c040c05840141e1003040260708980a0044042e501035282c9044507a0f07403004038281c2e2107500040c2d00f440c2000c0c800f554180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 280238327 1250 280237077 280237109
    0xf0307110a1d04030201500907030b06040c0e06030a0906020a0e0f0d2a03120306080610081f150e150a0e0c090a150f09050603150118 59
    0xb0b140301041a220b18042d0f00284a01210b80c510f45110205004505c14030307410300300d4000311900f814015101d24032841c40c0e01c40c0c11500804201d0b40341e5882282c40c9491940002070034410081080705198014100b5a000d10001080c110041d2007101807061445c007580021001400000460b00700c251b41e5a0010021507031050015401007000184803e21805054206026810340c03c0658a601c1542e80002c2072010242000c4e03280881c8036007920b4117900c51501d90001201003945040481902c40d029200060041d00d4a4002801c044c0010600c1c02d1080e6910001c100c521004506d070301095240aa40105400d440038200e0000c2000d01c10300c0d20700000340807000c2401e038503840440e401181e01304d4109407258034050411142c1d01090044640d20440280403c0560300140050304440b2401000d030f00902ea1516407104400740c5108004c400a2400050160501e400c030003064041c0606480542c5945410103000031116240d205590405c1101c200c00348000100c2c682400140003800d180403012 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 280239577 1250 280238327 280238369
    0xc0d0c0813090504021c030f110c06041d01060c05030405010507170d0b0102010509030a0c020d0203031b0102040504060b0a050a080703060503030c0f060a0204032001090306110d0b01020f0307110a 86
    0x81504540403030082c058510342c00301b1440d8800d103401030036a16650300820515400011140c006421004500d680304203c1145120355a003009440500f000b550760082c400941c0b0300c01c0f401171030180d10030b00a210041c54075001086012003180d00741e030b078207081041d0303180d0030783c81d00c000351240001c1c1404d903800c0040f81d40001c0001c0e075049191040c41c02d900038051515003104403034a9100e101500e0000c5410082c4460050801c0c441040c0c0aa0006040c0c82c01c2009000d200480101e426102651503540020140000c1c600785c400c02000d440079007091424888030000c0035006116a5180a043c0144800044d103920311136007000c030207400003070181d0352200c0072400482d9031090702c10b800000600440d03000036075044503482520112a0071541c203003d900500c14a08510080c408146410480e00280c04004034119006203009150b1a041c0705903102240090001110030f12100f1a0443d041841c009800030000001c2c1e0b101c09230008074ac816030340101c034002240048960710200d400c06031121191031b1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 280240827 1250 280239577 280239581
    0x71b0906090c090b0405130509010207061b080903030601080406020c0a150b01030501170303070f030f05130b0f0702030d0f0e0d020102040501110303130602031305060c19050c0d0c081309 82
    0x40040d440b00ea03034060710383c901340d0401e0049000c0d10740c0000101c03259a0031109140c1010b41c10201000005141070140e450720b400f503c6200071450006160310703201c0700c1d603030794001c00c126880b9800740051811411701d000020200030300917101400494006c990094a076400344409050103902c1b2922341c000018641318000036000040c030307040c0428900300000528076481260f00e00001c5404000c0e40c40c41d40d8030502070300c88040003040c001c10540c2c3e030303141000000520300c15103005860142106481d8105072030050b00122005007105c50308988171080c0904150000300fa100d18502101c800714424481400010080c401c80404201d40d114010b030410b41e180d01903000300283d41003030b43d50004001c01000c0403039482c44140c54195420340e0306c0b0241404104594040c54000b040801a80825070264844c40d141c031409403624000100f00045445604000c507441d491060920304020f404d103c070780d0406a4407440e80703086440a01902c1040c07a002c002c10030040b00c03002c900c0b0031800c00e00241c442c03c1000c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 280242077 1250 280240827 280240841
    0x6030b04141e010e010b01090302060405040213030c120b06030109030c11030a0507030c0e0709030507090b0d12080108100c0e0603060301200a030c0c02090613060909030206060a0e0c071b090609 85
    0x1145d413800d0900525540302c0c08841064030740240c106881d05141205002c002e610401c2210702c5401552000300010706030500b0304009041a4604c81c513a0009800d10b14496103000e444584682c0c98002404c00013500802032548d03864112101c000c00c06200c401017400d103840741c90000c00343d000310b481c040104040c0384c450b03105662404148090035030320b02405603410300a174000030300240d000020403c0003500e207805ca081642c20181045201d000390342d650070603484101640c400480c0900c00144500e00d010014183c116030503003010301c8441c0c20380d07030090801c8414515544c020600080022319603107094010380221004036120b5000d005840300d4540464020742281c400190801c094484480e1054540318103041c2c0040030800d80361508410007802d010800b2284642c036440c3c42d03000420200358419285028003980140000380340c01810003210556540000408209003030901590220300400d0ba800e06074407918840e840046a40401c0641115500c0410601c0c00c010300800c41000b00e0f08400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 280243327 1250 280242077 280242101
    0x302010614010e0a1a04050d06090312050c040e09010e060f04030f031a0112110f0703180f1203020a02150408010f0507050f0d020702060d06051306030b04141e01 71
    0x915005410044490140b08910b01e54040130001081c40f034641c4141c8440291107100044034942036494000c118001c82400042d11f00e1903840308181305268020218100d1290701c010100101c0c60140c46116080c051806041c1d9041d00d10400510303000001d5000850f0690510122612454103175030034000da0108230340440c0000c0c040c00c0c1c4450300174001c0c003d80700b403030094002d540c0444e10304e02c00440c0c480e050290020012600e48004180c0001200c00a05e66504070a0b1026511180c41c01c001e4014000400010b01c0105101d104001040e26200384a050303400103000b80341403c600c0d08003240740108d02440a90303c0240c3c100c20600e01030b02c035001030045980c03c40090103440d888101010441700d08899120120b441080120000c0c4500d00040480c1d8841000050070b00c02c0903004140c95400407500e9000d040da076580c0512692500760841c030304100810740705214241c06d40d03130b9800d64800e0240008048500341d2085540d0080140100390280e207141258240300406072140c28044c0450091203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 280244577 1250 280243327 280243349
    0x501170d030506031506060d0c0201060602010b030304152d080114040b030a0206090a1a09120303010810020706021213030f020109030801120302010b0d060e0d0306031e02060405040903020106 84
    0x80940320307000703002c0d031442410000e018021800800c000c03031600a100400043c1d1010040041a4075007805104032a42540a5400010321a003001401707421103000405241c03007548180000c0007a20504840c0d448038070003d103402c20f10844900380e84011602c643c40e207102c0441d0041c40c64510300380d1028a0324101c98075040202c4001c4540c00502013119011090144c064100c40d0b250b80c0541000c0d402040340d0107014000826881c0c1c3c800c42a90150361241003142400400150740d01d00f49403441c1e4a000000b4440055455540b402c000c00340d071035006c20070400003181c000c916542403040350760503550324050b41d100c0e407a404c0c0f07401c0030714920754481b403030044010400300040c01c040c0c03610501c40c0481141d41500d0b600e5231039080c114600a00640000101e0440d900e600d4031016580700c21840030020b500c5020302089400e103400c1c550741030200311241802010300d03004041021540302d00d901e0582d03804040000c3c5110a042c0041001842960820740c1c205050040c03034420107a055201c002115290440 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 280245827 1250 280244577 280244593
    0x30d24054c02120403051009110a03030323090601060305040c0509090105180111071e050109050d0f0e010c02010315030c0605090310061a0a2d1b1e050c04050117 71
    0x210070780102c0c00041d103164000b00e0070304051f91180d4410b0b580103004843c1d01c4038090680c00094410306168000b103001a854190000314101600340c0328404000100e0554114035014417182d564036014401d00d4101629840468141306600d4140400fa10020300b4112084c90a60045030180c0b00695440d02201d50340040c0c2c111100040c80b481e44041d015040c4940f5002d8162108101c50204800d801d4104040d92440800035400340714080b44e5074440c001506441702902c0e80605481031909004040c003408821802c200c0c0c0e40400c501486aa0908000800c40c4490310b402c0b203103118540009008982c801408074690750081c002d401c01040480443d4103081c4901480016513072544640151408400c020703046a1034903801a1004414610f03015100e0302e80d4406440d0181740803400d000070b01070103041620000d544500058400301c0404400c03011304c0e8040d07940714500042219114908020364600074100032041c0007025444800800500407940c44050400100034543c070007610758890141 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 280247077 1250 280245827 280245853
    0x1305011d0f01060b0d09150501030302070501260f091f05340309141212090a030f050a0201060e01030809040c020a031707050705030d24054c02 63
    0x3c1e1400303880207510704905040c00c0700c1c5c0100c040d00310080c0803070f0010080c1d01383d18080a40e0344684e9000754060b500070301d41c1c94039040000d4800003034011f41400f44840c0b00752300051074520035401600b110300c0d001030041e10340d5800000b07400c0480114502082e509001c400e800700d41d005800c0940203841203102d08100811805c0500c044445840707030106c0400b00e202c0600c0c4080c1c0260b00030b12440d40580c04003a5908611000303942040101100d5891912004c10b14405407908800e0740d83d8000c00c100003c0c40100084c0d18060040e00140e040c51042190005480103181e20070b401c40b0000744004030710095a56140e10b00400e150b0440b01d00c150046107003014280c1600d200190043e8901d405d40c40b4460060403000210304201002046241440010000b41b000264200000c001c140c2d410400065503901c2010050b5004101031540c2212509000042c8580c0d1344140754641c484915041c1c0064a01e0603240c428120143d181689012f09090444203994a49800d0702074030401c00d650a840c8440c0000c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 280248327 1250 280247077 280247081
    0x21150108012d0e0f012003040201051206041506050d0c030c0f050f040e150301110a1b06060512030a031107080d0b030c060c0706080a0b060702091305011d0f01 70
    0x204581c1c4442404150114100c00184020b10b80200300a80800c08594001d02c081c074013281c40d078500d01c42d60764503100300100300003030400706d403120a161490340c0c07460030503030002011805001e00600d406002a008620640e690b80d2140000c0d4210307425041055542e018054040d4224088940c00c0d1803c0c13a441080e114424441c2c0c2c0203c022644440344514500c1104587d80e401218011038450410400482d803100c45452080c498005002105d1a054480007490300351200040f0401440000f40070404d151900320344508860032089c0100d990b18000c9042c500d02401c0310341e200070b800207040b040d20044c103c0040020b044254060f01c050101500700c8809803001e109e40780740030780307625020300915840810580010b843c0c400001d08540c0a03a0034880000d0056021400c1c0360f8050380415003c2268941048255130300c4030250504000001c0c40c1004a6250300ca003c500034070a001c2280050003819540c00b2250500d50054004c00034040e8000c000840cbd10101100e0240602c01c80381c1050a0344814 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 280249577 1250 280248327 280248341
    0x3070909050111042d1d0106020c010f0905061305040c030203040b1b040302040509152703090604030605090304080a0623131214180415080303040308062115010801 72
    0x780c1c5c000c60608480000001c1c01d10032540b00e130051640300c00750000b5698854810400e01d081c100c40c2510080d45400300c064505451440fa15050003c211400070034650001364503c115003007954141d40c1c40c6012200e1500511854000e50f52151034504a0203000303030b0590145114600ca052000131030b403915030200b2690f080c0c0945528031554104418001414103820181d00005800100c5840c20361700500a00ba030b080032103a14007400c0c10145c00c01e02c3c43e0003649030300507141d40c408061450034920502280c80f41c8502e0001400043d101c0c00841d8508104008840041a06005942ca007400030701d4000054402d1800483e00160103001ca010100806c401d914002e01c518501602041c2c41561210f40107200070241038107011660800865031a1803400810380c3c0400e501070207030b100d211841080200c0720307400301d035030a4248402c000b0320508000204590701700d6018140443c199950f80d0010b420800c011b03050341c0720f00010b071820040b8514001041e201941031581d00800503078030340c18440d08136141 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 280250827 1250 280249577 280249589
    0x213080304240c14060604061d060f2803060615080f06030705060a03060e01080f070e04020d08070b15030c0a03060e0f030310090b01020c0d021e0307090905011104 72
    0x201a038400010461258020041d0760301c1c140840030000350346901c100031351600d00e8041503400400800180f0f1409204410180840c1459400c0c00c0311a594406a1a640148024002d107940024048241d9074241e1042c00701d003c1040104854000f1800c010703500400c1c3c441110f0301414840d0215141c0c0780d914021540d41c1d00c03039894000503500e030201034088100c09010503405020b250004141619444018045181551000f01c1d42c01cbc6849801d8854910591145034140c1005500300c010f44004642c100c00c039001c240c0741011646850001505030b200c0c080c030040001c0350028501c400c00c2890244240b2a0740b40c0c5080b0107850b10042d042c55103800f26521800d901801080c8148001402c07a8071820f080754451044403032a54003903d03128a960b005a0f5407502814943c00d040100c2400e41c0105404e1a4080c4043c0505c0407241011650481480200a204204160543c1d9080c5400544034280e084010201c408113591240c0203001014000011344441d420310200100541c1c29000311030445030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 280252077 1250 280250827 280250849
    0xc0d05042108030601030209040923151501051b060109090203010c090b040510050c0d051902151602010b100504150e0f0904140a050d08010503010e2e0509010213080304 74
    0x1590130b00440081d480003034601c1d44075030344070b201e180494183c0410360310304109051108030b401e0f45006032500e0103610f0b145200d010203814003003105000c401c20540c0b4401c402801c24545480c051454100801032240040c0c400703225440000a20808a4011901250082e8001c0044111024080b2010075440c0604484008104010081030034503804e4030030074440303616105007819900b800755400c0c6429060008006031000c204581d0345032102c125048a48064001041c42941c0c0c405c0314683c1c5c24000708106103030641c00c4a50010507000307410152130b150005150035158490600003800c00c0d0001e0050708400c50400e00c0f90035055000c5c04814041260086c0140600f506280130403a00d03d4006101711001d90307866a0368221000c1c10030500030300601c504d003c1c00c01c2c20b0050100070f056040580c00f841c4240c1c140142c0c4440c040e400300744c0101e0008070a401c1c0e6083c2100c11039030480e511020400d501c02d03515010401108050640c09000090302c03600c2845400c559035080715641c4e0281c0c0c0140c2c0c801403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 280253327 1250 280252077 280252081
    0x16050306030a140f1204030506010b041406030615070b1501050406200304030f050c100518010e0a050604090e070f0501080708060a0b070b041a1302010e0301020c0d0504210803 77
    0x1603400c041c0400f0ba1001804480e4034050b1210144d060260b803500c2035500314000f04040c400c200c81441800d015024048410b41014500040c1141c581a01c3c08014000c8000002244654440c0502800a800700751003841e03440b0a03c2c581000d412404403414084440d4414060001d584500121030031207070541d40c0c440c0c81c48641c80036100c1401c41c020950b1040c0c8000c0000000281780000690001030084014100c0c440707584080c0706900300080300b58801c200381084640841e0310100700e0f0814500003840c0c40032404110300d0100d603c0c1307029030300002e42c0030002080000b6090000d03042111491400390540d90282e43d2004043d1100b680c5000706400700744004005030030503208072546a030280d0700618a00036107a98803110415648651001d03925034030028108006c1c801c09502140a4040701d010320010362a0182000f00d520f406007070000d04001c58460071105a40e0250107a0301142c00001c02d60349180340b4608054600e83c458424241c0700400d1010301d46405140c0059401c06a41099100e4615 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 280254577 1250 280253327 280253333
    0x1203180307122009091f18150938100b0a02030d0903050711011e0f03020c0d0305011503020a0207090509010906060605032a09090717090616050306030a 67
    0x740003c1c42d008036030004a000038900e1503445140250141c0703003140240c0450300ea0403211051004922054000d82d0342044480000c00c50451754898080c0d0b0072485114030344445e0b030201d401a200c0f002028003410422002003459040c2c4800f0a1440110002c51000026940301a01c5070020200c030341c1c4022001c02001040440600c5004242c01c52017841034925180c1200040f01c102e071802c520907000140c3c0880c8103820440103001c0c07440c0e4420309007003038680218041540090008501c440750104040030200e104030300d00940581c4e2000803080d050b0b441071984400024010007092060366500586441000c0c081390107032086444015880d809040c2040c1001600f034060840500340c01050365031031003030b100404e10510860b8041c1c1842c3c0c3d0b420795030341001680702c1d0b5050722441030030700081081c0030f0304a64001580c086840b0b406090b1000d0700c2d19917900c4000e5424600368103003504d16076030142c10805001004134a4030712070091502c030300c0400188070008071802d002c103c80c503a81691100c200603000c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 280255827 1250 280254577 280254593
    0x70c0201020a0c090504060507030e1209010c14030d06150c11010c0807030e10050f07110a030c06030e15061008270c10020a021008040f02120318030712 67
    0x156401070045036040b01d9240d85112800e44260b11001e41303d0f540302c00380320800c415030003580d40100061505100350180944104e443c0c0c1e009003000380542d07100060840b03159020302d4400c2507980e044542c01070150460205561a907000c0485681c5040c9014000708203010480f010000150a5a44054050300c0b40e64131625051000310350181032105a0390b00d0400588600018400c00e4429039a05442034001b4040c4034980300c1111076101401014014080c1022402c0142c88102c5e400551210390101a4000304a050074035400c090407810221b038010500503015008001510740c510200c50340f40040401da0a04080242d03001a4081079515054911a00c80c820300e40d0024290101400403400c2624490380c0c210036800c00140c213400610074442c1754a008100d0050144c2030380080d00d11107866900044021202080d00d03428451440d01050501c140c001c03134551690b40c0030707180d20b05603100403a610740d99800049480a0303170440401422100e050100d04901243c01c2c2c60300040d4034040a56500072 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 280257077 1250 280255827 280255847
    0x1091a0906160f03080f011824060807023007020111030a030c120501030506010b0a0909090f0209090109020303030601050c1006120c0611060c0f0705010903030b13060305030307 78
    0x80d0044003840200705804451000c01c0302c440c0b05003000c1548500a00e0090044000200100c5400030310000421091503068014a081142441c001031041e40402070300115400182d0122150000c4080200344282c1060409000c0e91141c0c00304e440e0369101511603440545002d0b0070a100300426004116125564400303000140d105041c8401700340400b0700b142e490340d0460740d02040040c1d21900310780b61039900b19007100a80c0300310950a003c00c0d030541d215255244418800e080c040500040c0c6410518419001c44001e0300310003c0c280828451801c003400e00324000c4600b40d00c10388100703000c1a60000148648108694082d010b036045503595070041d2911b800c00c111401c0030303028822810802548a04c101e5000d007900000350a010000d40c1400008400590001002e001070707540d0b0221542d400242c650781c4003074249480b6039110081c0f02d201806014800000f0b01540c20201c8041c00c0640582000380000000e544188900201c0c51400c0709590300303480054425041080820402d034481c2001003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 280258327 1250 280257077 280257079
    0x721020d03050d0f0518010212070e0111072907020109180204050405100305060f1506090a0b0d092001090306050c09030604060b181e090c03010903050904060501091a09 74
    0x90510302c403034040c0ea01380d0756014044196560341d0781c02c00200314500007642c08581114002107007084100c1d0701404400e0005813680c3c0c14010301d24180e4050f40c0c46000d40180319019102600c0030b01d55128011660041448a604003000110090103614604c9209079280250140c0d120003105150041c03510502c42113020a10a06808010100c3c86440e2800350343c0c0074414088501c0c8425156040032810503d002d0b00300d0041406d00c0061000b1481e0b074015041c80f0f03600c112685a1368002440000c0e01804165100315264040420410306070b815a5010020303d074001d07014005503800c1e00554202200c503603d0100e000c42c0780100c0c28004500d00e94450f41d84030451915a515003c80340d00000d15100301154101c8e40203846624010003070030007082001c03001d90104614459803c101001071461200c0d20031404140c902c1e4400520b0a120401000301c000d0006002023003900b1582c10300030302c154010742c0201c0c051420040700043c2944160303108400c0391001040d13110600d100200c00821a800034a190b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 280259577 1250 280258327 280258337
    0x6010306150c050625030203071812210f230f0a1b120e190b070314040b04031e170306030f060423151003050721020d03 53
    0x1103030014548040c555980700a0300c0d0a00c00160a1034264500603000b0000d03c0d039845102d4081004000503036040509140609025860769910b2108540c00305100040707040954401c9400030309005010341c500c40260103a2124a413000460642c401405070441ca40800160200400010b040c03081854500c02c1c5601c801142410801a00c180e0080c1c208400103104408001003000d800c41e00482d04050340300350054840f000141945841070110b0b920521a000d10600076010190303959402840700124905460350000329495024440460b0032941040f401b0a050002100580c0d91f090140c808484400040601d0681580e50303601c8c0108030101c00a5200d0411814900092030703090000c441c1030007500c1c0782d6449140c1142007500e440804900c2c84201e420002c10301000c80d0301e00408103274203400b00004035864003503158514070740b0050400c1113550099800521450103036072941c0e141100c1c000c2d81202d603c1511418582510309845406040c04010400c20034010b00f80046840121406401e003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 280260827 1250 280259577 280259579
    0x3090305250602040902030f0106030b0d110103140411040b0303040305060c091215250909020c0f030f0304020f1804020d0804080d0e030f0a0b01091107020d080a0207270506010306 79
    0x5400240e8215030800c00c0300c290003204210720f03448c05032030007401042180307001c0c0001054000031500d071110036140500502c40c140c05600c4103900917008070201d9440748820000c1c520301030402180c00c0c0c000800c140e10036800c01c110503039607160001c10350f420380c0d070004080c06940e110318500c803000764000101d007034100f021444580c2c41300364180099070070f490080c8146450b5227002200d41100f0410100d800010004299901e034440c2d034030042050598203840c20050395652622003052800801078400a100e00c0001140d00c1d85400342c0000c0c500403803080e80c3c0648080100000c0000d0200d0700c0c1c1c0900480c103000000640545405d1035400c1c000d60144402e20301e080c0e202c039200d50070851000c45603001b140b0700d4070152100e0305003000b140f010221003c02501072403074030f5074600d071005d0410f100e2080380c40c4e00d403010f65244203410011620f1051b0300406a805040781c6141469407600104003020143c0540d10001421040503040240c0c802ca610141d601c403100c90400038402000003900040c101513840d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 280262077 1250 280260827 280260833
    0x1031104050d211106130818061b10110f07030c0323030f0106080105030a0f080c0a0b10090501052b0b090307050106170706050c160e0114010309030525 67
    0x20001443e0302c60382d55002942410118445ca0b0802c0070300304480b00c3c8003603400000801ca86c54240d030755100002401c90728140c1003800007055400356441000c00080186244d04020400150380549078807015420b210010403201564010700421580da18400c00400c06030000922900086401c540f09041c0404628040d020055047d81c503050703d0080e00000005100f90910407214503070041c40c0d01d2900170090340c104070110751100030005001309070352201110724080055040945407003440b41d500b262051507440c1480b41e0105800e46285241480300b69000c92101c00c6401494180c2c0d601070702c1c00426905c046103980880301d9208490440d0103032100ca13035001420314440307d8000c10952000350740b40d6460b801c0450840d521980b01c2c69480c941c41019201410000c6600e108440311401d01c6900c64449160302e43c2015421804042100030001c40480d904d003131088254142c1d0080690301d083c0048181c0198100c9001e518050003191081c06141513407109951010303020880480e00107504e60003a030f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 280263327 1250 280262077 280262123
    0x709021c090b19230613060305250902161505040c12050a0203060f191e020a021203072006040b1513020d05041208010303080f070c0210020d030b01031104050d 70
    0x114208101440c00f401744076541c600205c441c00e14109541040100e84d1840d030f5820b0350b480c1040c890311403e610000800503480d00f200c19450081048807019561381900d6121144020307480d00044903408020580401124924402c0612499200069142d040c1c00d080e40d03e07400200c240340444141c41195a004010f0324240a2103000d2002800320401b41e0400319803a00c0112260b10035022190b1401c80c02d010010322140c260302c860a004240143e942d03a140d00100d0400381410f000200d804000028812400d501030085000100c0f03411401c500d8405101d10545c40c0c0800381c0300600010741c81c0c0c2c0030900b07403000c40b0444054a4001080300180145601486082e41c20807089222035654400070001400202c9404d80014030040c0741a00321507041d6900584140005440001000c282c0d20000d84114050540703000d5041d0000c25081c030301110002c00941e6a0060071071140001d01781081c0b00800d50180c090950380d503080b03a2200781800c0c01c24043c440c40700c410080c140c07025825801010b200d62030034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 280264577 1250 280263327 280263371
    0x1060f0509041e0c03050606070302070e0709050a0f03051605010e01031d0d090503010b01020f100c140403140106080304060c030804050102044208061c050709021c090b19 75
    0x3031003002c44c900f9010207001e0300f1a00003c0603140511001c2141400090323010071a1401d0f200c6c01c802008203921070a0049503850004c3d00300c16080903100101043c403800102d21181128032510480f005212104081c454910075842418042511220860265030082d000118860241c00426841c0304955800b00c0c54480d9021421022030b00300041400a03040a01507446c541d0302c20b0004182244034000c44565400e0035007054034000c0c0d0340d01d040e540d48500c2a40d00d50030b6036029080c0140c50300e481e41070001840c140704003101819882c101d0005070610000c01039804859150316142881e14590702c1c10b4505500091044400755800c00010901c042440c204403050481d1520704500201a0403c190f4203488000c0c400f46004a803940300c2c0e08259120f203076a54800b1058501d600c81030321801000b5034010100d0002022030240e81c0000c6003100c0e06502030300710401d0b001e4002c00d850000c01485422560848806000c0840241c002507500904002c41a0701ea807902c0c10000d0b104452408240d184814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 280265827 1250 280264577 280264631
    0xe0918160303030b040e0309060c0703080f03180615010f02030904020403121412040f14010f051e040b0a0b01230301050108010e0f0a05060d14010e1501060f050904 72
    0x2209420300a06901d40300d42c410400302910704011b071044808000d0340d28020f6008003446418005040d10080a06010b8000116844034110b0b4607034104001d026615003003200c03001c50050341021201508040001c030640160004072000f50844800c038011610000c0c104242820b40c07104010940064869100400c0118000d00d248082400c40207002807a1500520410301c1203641071203032411110070a8065038006501c142c0081048445140c10341c5600e400f1344562805502e40401c82c02c04c503605401040c80741c1802004c00d0b4611080c4c003200e41213180242d6020f440425002d001038070000c215800852810340504020035038072908088800d4a6212124100c0c5c441004401005a5600140c10724058036400c01d0380a95071424800e00d810f9a4401881b070881b2603141d102044541c5c96402103103480d903400c1016940c0b12a400c4500d01d000c1c16003214102a1489103076000c21640003c801454140d44180e6580c11f1070340e0311418215030360b820640300c25038019900c5120582c82c1401407894200380309 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 280267077 1250 280265827 280265863
    0x2032a0a2309010c020411030703090c060f02150703090c030317060a05030d081f08060108190305030a0e0327030105011e03030c0614092107030e0918 66
    0x25000401410219601580e186851075844581c0c58070100341c054600c401020b180200010001e40000303009001d100c022001000c07000002d000203103a041e040144813500402403400315641d0f40703404541e642034084c072201c0103801c028203e080c0c09c202906015081806481e0106600401b500c0e0721740980d54030340c41200841e02c0c2183c00300701e1070051821300b60b20500c00c81d561440c0034039080101c0d4444201c84003950802c120000010308007152051044254142d440812004139200c035400b9a580c0350a019403586845070740203150450b04e64528451644e45e2540d00c01c1d0941c0c883c560640d0240040590054a03400184842e66103600508181c21004400001c0c0d030b0300c0780a074001032600310741e01030704041c0a01000c01302c2845424039140604007181d80c54a4886101c6a16051030002401003100d00d100000c0c1901c1031050421001a0000da252184403017546108540c2802d00190310070118000c0c08507441c1d40e1058904e180ca1012a030744040444a0304900c40000300d420713401c6c80541d482e482200c00b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 280268327 1250 280267077 280267087
    0x5090618091e160f050a0b0703091707090b060a09030219082d0c06180102030c190516030c05060a0507020901060f02071d010e090a0609030302090111030a080a02032a 73
    0xf05007014900000c015105402c0b00b02030514011071303e900c055008000c842e00d0001200340800d0310451804004200e40000005110301c200c4040e40c4a01c002d00ca06a2442d04042161b40c8601c0d08030225a440c09140e161411003510b15403d20008050040701440391003403103140050704c100b05207c4120710310003a0b4000b034141507822000c0700100c0101c2e84980c01d65071102c0003211071615100210303190105a804400754108003070b07004138607500c40c04078092800c1c007a411661a031310400b40b80c40d4001911072000d9428030807150607079100d00c0c0341034800a411444409020000e60805000400b425002454038501e8001c80f0780101da8210030030f81c840000940b0714503400a0003681400b14002070a0245612412407014000006000c2418041d03071b62201008000300304c420f2002c00c9410341c0c41c0d90001041c0888500341c18090001c1d00598401130120b40d41100c8509014004422035031001200e4071a40003a0b102d00d07025a009405c001c011811001d1710072010a6110050070107000240d500701030031903a030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 280269577 1250 280268327 280268353
    0xa0c060e03070b190e0f030c010c02060c0a0305150418110d0b150d0b010311010305070c0839010609140402010801060c0204060306050a09060605090618091e 69
    0x2109080000d18807604180086000244070071503442c0c020040d04080031a00d04403412035002008600e400003030344d218003010f102407910302002400509004100030010200e00c840b00366120f400443c0da5920300c4208005d47c01909001e07a0102e038000aa24801621034000329010604684003001c1c00703c201c0c0015800d0000300700a0700b40e4001040802d881d207c821940c0b540e00c0c24040400500394442d100c02c80300c0c07002803980b16000b080c2c20309034110301441101e507504d003403e07480c500c404d842d002c1c0000d0074000001c8c5914000c200b12804203900c13019951400041017005000c00d41900e00d189036000105d07408040030b030100e5822175013503800030000160642c82d04080390100d80085034a02901c486100070000544e80281503a41191918102090f07042010300c00140200300300e405c01054076180000384540342d00c0b21703800501c10750300c0b07031004010554131801001048481150226800001001100000d00842e80d0b110340008101048691303101400034500880404030207120301552121503402e01c5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 280270827 1250 280269577 280269581
    0xa05150d0f060e0106060c0602180306040c030b071403010b030a090204020a02010c02070909050d0503190507081f0b041202030c03030c011e0207120e060904061401170f070c020310020a0c06 83
    0x408101000070400e1750310f030110203801210103440c081e080c42c0d800b003045807071606843d0150142c640c0003001d54215140c54581180b2400540c0401c1e100054179100103100300340540c03072480210000c4034403e03017140c0c40c10140c0546584020b001c00c1204d40c07525070301c00060b12a4009803031441540c1d000891141d01c100c0009207048040d0303024070099410050f80402051000c02c0e4841d42c14503520384642d807036541180308820700300522080608a031a050400880c2c95100001c580078140da10400e200820604441c0c052080c540e000d551164102000201300c0c8c03171510000d000c2c0288c0302500b40c450710340c1d065001030304541041460000c0f69446100446088021910803011419411030460404025032514041100880d22003c28040d00902c05902681c59409580001c5c0c1c004009002080d00c0c3c10303a1541c02903058481601040d2a05d00000c24050f00d071740110300c180385940c20211140e440e100101d50405c0180780c240d8140c09064540142d00039240010418520103031101aa03074040351400c1c3d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 280272077 1250 280270827 280270841
    0x204090e0615010f09030c081606080f012904090c021e0303010e070314070e040e0a020f0904020a080303070509011407030c03030905011b111011030a05150d0f06 71
    0x211600014100050a00c007060450740440702072030150b13043e4040540035070b52220140c001070905041d0060000c2c40010004920b215103034a8248491103035500e980642d144882078640d044045a100018000781742440c3c0340c0031000b20b003000011009400d09030000b400d0303400364101c4124142c5840800e100d903030701084507080d81803405c0301513040d04d01071104050301c1e030006006002c90041c0c1c080c04507100c0c511a401841000442c682d40768168245504003501807040d004101c0e001d2824144041c05080f800300e203400302d0540140804544e141e1003000c1100781d12009000700ea01a50040011900d21420400b45204140e140c8501d81e646a01c44009040f401c600c0c523041601010800030040040d50103006403000f242e05060106e110f0085160045c050304507a06d0394620310b4210301f4500003803980b0511000340c0182420a5071009181544000190360102c0320031049402c003040800c0c1800709940c40310f07600003503200703a20240e840908001160050b01100c10b0311401c5412100009000381403040c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 280273327 1250 280272077 280272101
    0xc0f0203010615020f0d11030301170705040f0b010815060f0d0207141605090c120a061a0a03050604051302090a06050d08030610020d081b0d060603021e07050c0d0222020409 76
    0x5042840407e80d12681ca21050241104880c00700e9540c05590600f00403a1016240c010014008291509280e20080840c841020b00091000000c00c081515180800c030700c1741c001800c202e1500260910700e1000e5444401d4520905a00300440c0021524090700403855984900c0a0090460000c10920a07a07001e078009502c150020000c0c05458204681102d08c12081c188040e41c642c0d80b061005c0d0700a2540343e00860f284800702d541713224180c81020007420101a240c40c100015180c0106020403a4801c441044a13280440400e034091310b40b908081c2d5102007241030124215442c1e80220340313402081036048130091008000c0c00711340d16007a902140a0030203440204005040d1520080c811136005d0581c5001450021450b01e01400240c12540c80349001c610511007166507a00040080d8840000c02c0c502d500218000440044124222400a80c1000051000030041410462020428901240c1c8400150303841c4a2808845801c400005a41d100c01070320b4628084208003665040d80c808 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 280274577 1250 280273327 280273337
    0xf0b040b1e04030e0105091801080106120503120c071e02040e030304050c010e15030906040210110d140d0f1b020a1a152206060503070c0f0203010615020f0d 69
    0xc5100081032207071555120350546002650f60580000680380d511441307400b0368001b101c004445042c0c0f281e00321824101d40861008000c035035505c2450070950300384110000c06036001006424121b100c0200c2c21500b00105062092030440243d560b000e44032110f28001e039145000b1004842946802d100758a810700b2107201031481e42c50b0035550103448004642000d8140094240511141e407290342c4658450a1603400303590f92414140c5410740d41c0c44003140c08a2003250160149501a40f1480b000010107124400400d41c00340240800d50300341180d4001134044403000e00803850040442d01554021914a00001845e01c1680407110740d4400401d4911040d540000b45040c0014412141e242550b10395071a202c203035440f460b0b011103a94148251550380643e00751400610b0312401d840790350a94582081c200411561500c0540b81400101c0e5101d004c94006000180400d007030a4441910510003400001c1d1980c031075000c810400aa00441801640455084041008100040e0800e5050380c200 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 280275827 1250 280274577 280274611
    0x6080c07020409030509062205060c060703050406090605010603021201090b0d0803150a06020f071d071101150906050405310515040b1f14010c08070f0b040b 69
    0x2148192098050081c000d50361014041c05051059050300c242c80c40040030940c0e07a5403806000c2c0c940041100e20542083c50344d100005861070600102c0b1a2480700c00068032080d640c5180940c020400104196800742c0c0328450131001038000e206060207400c0e29240180c80303a81140d0220380c0d0150580040703549030301d469206c00569a411519400c12948161069520360300c44400711701904002240f50340080703044202190721034011030101400040303c011940b140d42e440f00c80840000c803c0101c02118034211001c2038030980324000303503a00b4003501c10012541e0341450a10304540480e41e880031110650720007080c4428502401072540040285002d0031101004000d00250825456a0030071354050914591040081c14081b80d402000210a2060f8030b113010704204622900480e030403216000d0034403507617030341c81403002e40e58098a4240300401101130641c4e0064903006007500e0140c50f608800c6c00b128002902c12100214468450402044142024940810790090140c4200520083e04003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 280277077 1250 280275827 280275841
    0x1e0320271006080a020d0204091109011107060c0809011806030f0e07050a09090f051506040e01050708010b130e0c0a17010320010e0910031101020f0307061a03030a020a06060608 78
    0x1083c80d4115444040c0103a984600050850081c412070b03100f00310160405043e4085114540007500c0e0b50202030300e45003070030000040c1c0f0700e0f1500301c1c034000c09000c0b4059040c14000f040c0350300054003060308107051028031001a6119808610110307400640000c2d2500103098555403107014140440200c00001c1a8090030440090100c40c1e45000340300318995074030450402d200b1109030702454a50410281c1d00c00503031207a0181401030086940c0c90040341003001d41000e0400520400b07100c1e0009030340700082c03a4244503045003194040d031140d044000007108041a10071003010400d0203030b80403181c5569561203401c0d0240103400084181009c9074084801040032940b1860440014160803180e08140c00a03d001030750f40c0304604038484d800c104500c0400441041e402500e00c10b5a0040f0b00503920101035200480c1d45500c25010810160014031020001603169003002825080c20b20700428141404030109113190064080080140d0007007444400344103680c8a150050442480c050a440c80d2881c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 280278327 1250 280277077 280277087
    0x5071a091e152d010909060b0616030e010504050307080a260a0f050d0c0309061a06070201050903070e070f031505150306010903080309010606091e0320271006 70
    0x82a40c0c10b200c0202111402d0100446106521201184080e20f0740f540c445006000a12040004030f402c24940418034642d8945082610144d0074000140d410a49540ea801c54582c009181482d05000c010700c4085907954040c0b0105002c1e1110720000c2144440c1f03800c00850b081100402220710b10480701c02c500844003580110b40b03c2c07070102d0034a00012241c510003207680d44030b50307002825500d2030f280b02d04402503403580141001a00a00d014400c200110490b402d80b00108952079900501c1040742c00e005502403409424181c00044c00e407802243d5840301c03221204000c9441d0300019825103400030400750140310301c01c1c50340d20305c02da40301506043c400800c5071034550f03208204071110040300040c5a40e200304001c2e0007a43d800000240c030380c103015060fa806007103980641c00c0414560703000402c460ba0308502d400c910001e20702d05150010702c0c50722010490540026188141d07002100c0c00440e0b07458007545403071030700f0048003010049840c4000050083d40081e04541106242040411100340c1c08 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 280279577 1250 280278327 280278331
    0x2180d0b0117031201180c030b09010611070302041107020102061b090607140f0102040f210b0601020f0307120f020d090306180c0906030201030c050708040605071a091e15 75
    0x200724400c1d8000d40c011481c0f0f0750107448107008400389044004901002942c50010001411500a004c200e9080400b50159401c0010b03841d00540c121004101e00344c0b140c03001d0b907a0340b00c0d190103440c84c107522500485c05071469503900b52001d2000203999002c55070f04001c2d9175131100700d002441031507500d0704068031028410f82c14010b201c0da40102d034050511072951000300c0e80004030b030210b41c04101204042400f035002481001c40000c2c200c0000240b00b850720700d00d032001d00d10769032081c0c0f090441d5540c0c00918a401904444c118410004507030341d100030800040a161b4015040d10380070f10b40301c1c10010400f2645101030003c540022540c04d0640c1e40042e64413060b41e910800104e00c40101a500301e0351760000500151100402c00400180306045900150940c2c0c001e90741171041302d0111005031a10300c50100011705008041000f00203480c4560091b115503441750000d83d80c1c0d401410446100321400ba1407840e0940c000071003d9200311807240c2d2400b000307840340d0064181c1030402c0304840703d05500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 280280827 1250 280279577 280279589
    0x1e050c0105042d0f020d1e050c0301060605091f030b100905040f110726220e0408041202061204050309040f0c020c011d21070b040b0307030903110102040902180d0b01 73
    0x103d02190407c105485125031001e501c01d244100785020b00b42401580e801d9031101c020b0203035203400c40201c0d49074440d40882d158040054100c900c011010a080c1c001d545c44210b112081550340c84141c0e401d43d681c003505d0004520310b41c2c3c03624011814a8104012038003c403071504002e6107003030003c00c08800680c041c0c8203902d410403640340d140050089850700146594036004030a075400528241d00c0d8821141e501241007903c4100200a40c03114841c00c001042030301c2c060f142e075034244002c118002c8000041c040007480980414200910051700303504490064408031144c0d0008118056503040900c00d0702d40e52520300409104841c803069000e91034101c1e14682030b0402c1107911140d40c0c0011f061a0000f0400e001414084504102c0c0000d11281054075012400d00d0050500c000340401c140c80507507050729400841103245445181040d001003a0130b401c201c080c07101c1e03040c40070042407003803020b070005105942c80541e499002e8802c1100b40c0003038203c0248500186590000881c8c444074206044d580 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 280282077 1250 280280827 280280839
    0x507091a1e0307120b0f010815150306040c0518041509080412050a0b07020a03050f22140f120a081c15050907030207031e050c0105042d0f02 62
    0x2103454003540410904a0700d80d601442030610000b04d0703076411240b5103041c0d0b00030030710311207107494951000c000d60f1002c1c0b240080c0d541c4001e240582d84115250f00541100840c01d4809241000d880404e00301081103e0a59140c44c04440c10003490030401052500703030200e400c0042d2070380b070300e41c1d07807000034820b4800c817a400d650352150342104004d100400c072006040d1180c5161860074051403c2584c4808400084820490101c0895030345d50002420038642c0b981600c3e00ba040104101040d1010f402c1030614410582c0d05000c000d0498080603410406444004011011034446406110311400c6e1400b00b107004101030000009452400b080c1d28411560008543c1d944070aa480300021507045070095014003071926013911522182d2007540001c440742541ca03100d10390fa990b88290100c0c02032000180201e41d5030110000013250076035282c1ca6000440c10182e0a00c10b105c8103160842d50202c408854803407000c5130020034203130040141ca00d000a641e098800c0e030081e96440403043c86010400a00803d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 280283327 1250 280282077 280282099
    0x190212150409020310060311060f070f02150d06090e1b0d0326010501080604050f0a09052a2107060f030605060a0e0915030a0206280c0507091a 63
    0x181d03580d000301850980003000c503500c04410f8840b410007010b00e03100c00c60348101107808a400600342981581c1c803003100c0041642c2042443e071120613007000f410808990001e01280aa1810400e020150031130302108000056100c3c00c190385441110f80192800d40c9640c000c03201c1107034284040144030301f50301d015a0004003c210516082c1c5a00310454507460800300458184000071440d000c046040311b00981e14031219071070708003d20048880594072910240001000075100030070320b402100045125408881c20310101b0407a1142400c4108030040c806542152030204600d0860420140c08010740d0200d0b005410f46407405a80c0c0e070051044106010800c030001284500940c029002803101070038081c1d0b103450138000102400d120b906402e120701d42d02e00102d00c0c1e000d4507140000140c80c02400403c2c03a812550200411034002c03011064482d02010b40f011102103440040c0c1507080c0302034950002030b0748245086030401055412451545151940d162003141c1b08981d00b000342003003601c20b000d9917 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 280284577 1250 280283327 280283329
    0x503070513180f0506010509190c020a020411090a050a080616110102120105091305060c07062307140304150c050d060b090a05030a1101080907150819021215 69
    0x1910341c2c2403480500a106805100c00d10206032202d48800d4800e105a0700140e0b00d40042040d2000c040c1d8841100c010500d5481400e08400da2058040b2401401103460f29100c40c0e0019081d42e8100411540780900411400c0103406c00c51401c00140500b202d4080c0c00908040440c1c1d03684800411580c0000e8540e101c91148500449000d06880d0601000395610104282c08401480081c892280608015000a420710128003201c00c615544007002c1e04c2c094450350480003007900000c00c1541d03a50740d500d05102940180e00e005080762071034000b40c051a072400318030291940341d0003c020210f40604000300000070f40e88941032000181d601400003200030b81d03a00111194004c0200c1c1203040d9250900100b0b0804101026154840701100c0700e00c14151220241526521901001444145030340e082200540c003554103a0b074070000d900110741c001980c80f050000042000e0000b01c000c01c00c0b47c2b040c4130074000034001c02529400000030940c13415601c0b03003440043c4103000300b40d000309048000c584103071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 280285827 1250 280284577 280284581
    0x110402031012120f0305060a05040b0301020f12070305010503031c0c1e200705010518010309020d03030902100309110f0105040815180105040203030d020702040f060b0c0d02070503070513 82
    0x15282c5100001088101c5141440c84101c0411141020078001440484507074801e000d071501c201d001503c0c8184403890703e8107200c090b05c0c00320071039a030554092103000c009054203000f91148c161012070400c140d041010000d4212141030b00960300a400c100710342948072024044034248004a0b160004d20b4400c650022240545403503403c00d0ba101c1034a19a000c442e510048a41d1807848012990300029074010702d4958800891013094007241003480740c0301c4070000701c4c11489041c5106040106401c10b5950002d001190201411008240c2c7c0300d44060039800c10b540c1414015085080410140066898565041c088003050310303c01e1003d0201100d683c3d114100b511b0007001130104a0b6445449031006002e480402c480c1d8500008000481d90f580f00d405000b10ba0065030003501451500f80e42c02c003120060360000c002660025140d0390390010740d4040348900001040d14030361841d110b08400d03d115003046529042902107501401e81030150760340100c1e0200440d1403c848461212002d0892280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 280287077 1250 280285827 280285829
    0x4020a050f07110904051c02030903100e010902030106080d090608040f0210140c0d12020315090408071a06210303070f0207030c03120f0201060b040303142b181104020310 75
    0x10300001c1681c00e2000b0080001201003003251810840407c2c0444e1000c01c0741da034041c10400c4c55043d481003600c1c001ca5500c0d41d02a141d004a072000100d1860b0b66138000c20b080d61160351240c0c0465001e03140007109181d0000c0843e01600b824603000d411030030242c9801d0000040340102a1180a1245185440301d0040101c102c1e560198081551604404009070341c80310001c1205e98040781034008446807500b110303c00c480c442e01440507021948002c1100344004800300500480d0303040d204111450204040c14216541404a415000d02c036107002024005501d402101c104012601e49030a00c00402020040c2d80d440701c003500d030038041c2c0780a00b00c0032460700c90f440d8005401428500c00c040305010041c9103c503240f8155071510042003c01e044200d00300c403010f10500d1081c50b418003040c000284150b00c0f2007140001c0c48166800c0c004491020500300c4d503203183d044d681c0c1c0100340d168046488540640c5403001c00c040300c0410219402d844052600189940031803155500000241c1454182c9a40c40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 280288327 1250 280287077 280287079
    0xd06050c04050f0d150c02100f0209280608070e09010803041d090604080901050c0f0106090612020108310b100905070c0f0303021c150504020a050f0711 67
    0x1010608140380c800d04954841e006041c05607000b950810400e00b020329820b200c0a52250510149240784c2e10400014480d803541c490071800341b2803100b40025004d0150192464030950016903130040d00d410014600d00c803030700381003840e00840d15002020480400e02c0c070840380a818414032507603503203608681402040441a03030009840c800403504160020141003910351200100c401c0005000420300d060030100e41016041d48100d000030300040129010f4020a80c040c10620300b4007200c400d000c0c1c10710b4282c1031210060b039501ca00c108122040ea000e180014208090092640602900000c0207450003c0000300c0004d8503030b00c003074000724512181c046060300c481a07019018443d8500b4242240c0c080c0c03400c800e403005455001ca4005994440d0b180903c40c50b4440400c41c042c0340d600c150404148800030b4051650a103d0210308035840705845c540707101000700004102c43d140c40381c016490440c1d00a180140c1c418081004655084821a42c0400e4205102503c800d1681342115040e0120143c2c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 280289577 1250 280288327 280288331
    0x60c060b041803030609050c07020307031101031811030c010302041a03060a1a030a06150e1201140702160b030601142b0e060703090302060601030216020a030804030b15060a08060d06 80
    0x3040c5513050703020900392800ca80c0c0500607070700c0325a580c03c2940150030029515402c5801c0400c00100e0b10152000c0c400301c181000709007481c104c60f1a221041c28104141e80031207000c5061030413481d0502050009000900381141011f06001008ca041f900810006d02041000004640c030b55a072504010028542800e64521111a00c0c1e01d8603403640098a86140c401e0800c070020680610480c44580180100e55555116091880403c80d031f5040021020074195641c0d5000d54540144651161182d842d640040200001d0f0014401010800d80d202e41103032103081c4144a800d81e800500741071403541e0b4580564464000301c0c0c44041c3e540c170034900e00900c0030444e030200106078880d0708080340d5404d10b04103568050f07943e600c0540580350708d0000100140c00440c00250550b020b9409080301c0000789a00720440700d0350754042b80c03640865810649410101280c10010001182c40c0c15500c2210100c410409550560104030280542407010041c018100b00050158442004000c107040d041402 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 280290827 1250 280289577 280289621
    0x521010906020a110102180402030403030207020306070801081506030d050a050d050a0f06050102060402010f1d0a1e1a031303030b220e07180213050904050106050f0a060c060b04 78
    0x180c0082d0300c00c82c00c11010807244ca1011018079018820b40b9003018042c001c0540c1e00a032001044025480204100d0a06609101c0800942c82c1002600c1c40382c0d00c10f441e0210a941006086840c040c10420b941e0b00c8604c1d6401001000e48011031024020310300c60034142e407078201e000c078145d03072a01400e207101001c1403800c01000204010b070303000a07840d8440c2031010000562100d004a0315042c0c201c0d07010f40402c08140d8440c42c014840c0030651002d44d500610444030104a2002400d090055409080d480740c462a442d0943e4560607001401403007110281910080607400c045024003000b40442c843044400c04c1c0325402d040c043e400002200f500140021400c0142208040c00d003c0e0441024003614500106100c911400013050b9041d201e01115230702c10244410148800ba41c8000c002840500c6c0c5104000b60303d44404403158001c0d4800c0c4004568030382072a0071300c00c0452a80001c030348a204000820003c00743c001c0001032034aa0860004150102c29901040250001c0b500d0500400c1c00e03085 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 280292077 1250 280290827 280290833
    0x90d08120a0504120f0807210c03050604380301140903030405100c1d0301090204050f040506100b0a030b030a17040f1a1c0612080703080a0e0705210109 67
    0x10209101d184144840036040725040e13011650f00651001d10310120320000c001c105a43e0054202400c8411500b200c0c85428940f400d060041e11481003e07040800c1e11034051004500d854000c2c0d0760b0802d82c492041c200280049854010a00c40030911501a24400d00c44e0610303072420340240010307031101c17962010941056114070f507580d8800c030b805440a01400101c40101038007409098410308e426942c240840510080402c66540020306443d855940d031f621040050315503000d0944070365602d501d0f020203403425042c1541030450091005e00c00074204141800300368085003e40e208072901c0d1034002091485c0b00c1c0828070b045403080b030113070001d403c0c41003145581682000501c01d54070700940181d10a41e43d00c4821100140c2009513040460303003441a20b0110345650f0b034104860301401d0340407400d1130761501d00440b0340e41120780503030321035000040b0401816082810f40303801c1601d0544c10056601c1c1c0c0b564a5403100741d2409214401c01c1c40441c401007420f10b00c042040c034811400001c10520750246 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 280293327 1250 280292077 280292081
    0x140d1a011106100b21090601030c0e0705030118020c060f0601030608120928080c12031e03130b0c04060905090f07030507050c01021b01050a0e03090d08120a 69
    0x1040240020190307910760040302408a80c0303500801c45000b442c8011814018103003900d8200500700650002c001c8054210040c00300030030b60050601d9006809a94190304000c0042e51b0700d038020950004500e01408001a03200303081303d0446c0e20304020013031008820000c1c44042d105074290b074076840c410003003401a04c19008a0442c02180240c90800c040c0c0c1e40e03075141545681c81100380b07010982d001d101c407041c02e00f070481c0180000c0d51702111500200644881400c0445402d400004650307102510301041800e205000510740c910b810300035401c04451040c942980412542c0100d4140070100205456040058906448540c0203c10040f280340c801c0b40c80300290007a12581001078200c42000901d82011401140070784055a8034400b5a69041e6058010b040c1c0036200c4010018100f0010a821800b13101500d2018290f004240140105045260941c0d201404980c0c00c9840c007582c0070355100000044401b00d0f08282d9441080701c1c0c2505280001d0b010301c14100129001c550100401c074644c076 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 280294577 1250 280293327 280293371
    0x6070515010512120304020111060c0c100614040e10060b0306030709050412050711060403080d050108011a0103150504140a050c0702011b1401020a0302040e010b1207140d 75
    0x8688a4029030b80e0352810001080d10b0b224028605800c0502844040c03c01c2c00000c6501c64010704007568a0401c03003640c240b81c104115100e074200300740420300b00f000355418800c801101c04880d07070a002080c00c10003841030b245d05040b0154490340d92108940c2a03810241311074496007505003010407000d584c0d039900d44100d83c812940280300b07004140000c11000400d10455002c0e03504008400c40f0308000540075152503001c13400a5030881456040140c1a54074100248042c6103d50102a02c60005031052006d071413041e0041a820790400b020741c1060600c0e410900c44400d4240383c0403440c82a122103011900c00207800094029090500c014000c648800ca43c034080d41c4840410041d9076240c5a0310a502d004001009000424a0484203a0290074400e0309200d14000c1008030544208280064220780c40712040c8000300b500490104460f0b40c400055600401c0c40143d5107203040c03000030000d0315070000205054280011402d50850100410050b90b4034030122104c10810020b0f061a064064104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 280295827 1250 280294577 280294603
    0xa122d030e070b25151107050c01020a110d060b100302070203060903070206030c0a022406010215010e04170408030c01090210110a11030307060906140702060403050301060f0905060705 81
    0x2c1e18000046802500303044500030030801202204540c0303280039520020302c44500640703002d504881c8a20340e980c06803240d02440411030180303541d1000f080c0380580c10450f0b40d2400c02d042d5009449070700041629a204961020b400f2651054000194680313980282801211990800078442030b044031940c060b0f0083c412540210b007200c00e00c0d035410031280d0742c0b80300c1c40d40029082a81800400d4009100c10040d000001c501e0054030380950025204031400d0032101842c1828091003c20700c0b56a507018443d030224404125a13401c42507041c01c4483c88600c2026000500244d4020004070300445d100c0261005011a60286c0b075a5078123013455640a4501c08500780d1003921000055500310303004e00031180064490b40047d02d44139507039032101607034003840e280000d825000c20050400040c1c42413184d6030320284100400907100782c50070307030000c500d81d801440c040965021500f0b00c004640c00c001680d046810503e030440d402d880c4000121041041d9502a6401c1100821480300300000031038a9809489 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 280297077 1250 280295827 280295833
    0x31e07050a0b1e1b031305040f0b0616050703021002061e160c03020705040f02040906090c120504030203040e01080d0201051f03020120060f0f090a122d030e 69
    0x148682141c0740c18440d0b0038100350020700314030380041e03641e02c2c880c0584003400703401132501d8401210055160440d071145515006195000c0c60a01103840d091040e00d05004200004001419045002c1580b40c03103500c0100c65210064103134007080141c00c000d2400a55405811903269045200c4081c0d5070300c01c00c1e1441210030040c410846064485680c0552207060000041c1c001c4503c103520a80c1c00c02505a4181c0441c000c120021859448600445910741101e21005a4903860181440110340080c0c006040003404d040720108442c0d885812078000c06080b46001459480702d1900742c0c03541c440c80c0d20905100b5801c100004000502142a10b82c3c0802c0d40c0081c0311590341c3c3d00569002544070a11140000445c00b0b040c0090f502c54020070352500c0084003003c03201122101d40c940b8050048440c03c646000d0b603410410f29101d9480c240b50070005841c020145504290340d00a15906003408200410907002e1010030b50082041110461000c0c0c100d03ca4195000030070002c016005080b014442c900c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 280298327 1250 280297077 280297079
    0x1903050702120a050319021606110f030619030204050a09120e03070902130308120621060604020d02070b01030c150503090c0607050307080c100e06090706030b031e07050a 75
    0x6400410110b032049500d509040c0761403140e40341500d1a030406003034416440601c102c010001100c910080240d11141d08129066000d541313042070640c3d04a0007084110401800030280c0303121000241c035088002140c890f0f000d40c40355910001c420703400e44c0c0041c0d40141080148680a101540701c0c00701c45003c0c0d468850310b190321071420380340c4c80f00100d0403c0d007503400520104480000350740a000500c412914400800b030356522070350300d903401c18850348640b403d04c281441028902281445615101e17a0b401500b025045031105071030303003c01858107006079000280f54000c5800344c0d04031114258001004c0c00395507142e086c5601090603a010703142101d08030f040d1440d1068080d2007528422400b01000700410200e203000e1006a40028104460a110522141e000191090080c110910440c0d008000e00e4113290343c05070030740382c1d02c03180708001da0000d0042c44407151001c0b4000381130350031608002c9402c01c01000840c0ca00100c5101d002803858610303142c100b003401c011071100d007100d070201d410160303013 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 280299577 1250 280298327 280298341
    0xa050105030120030a0902031c0e0d11010503040f1401090302250302040b0607290105120309101b06020711011106070f0c080a020a051218090a0f02190305 68
    0x8a240d01c210720110b001d000050100d00f8032803001198883d011450200380c1d00c503681d01107454441d010040c214181488a0310443c0c6d540d000b0740c111090001212051100b85003900d541c1603031001c03040c01504214000001805102500148100a0f42e02c038102c202c008418101d220b002303200d514012401409503d2a20781201000d88107019800a00180b540400c0d155a00b044014440c1400440d08030800344401d20106082003091820821400e40182d004002c0c503609000180c0160081c9203da14500a41001a680001500c42d280c40c02c0d5602000303041100801d64a66440841340001201c0043c180010032000741c02800045104455401c4039a096800543d0091410f05082c0c20603840640012840c61080042e90304610260074001038130b016076100d071403865000304000809644181d81c5042000401c2000e48a0905034113007560400301d84c50000c5280604a031607452040b09060b01103004500c0692000061403c81d040841d6100d803441010800e408240e0004408285090001061 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 280300827 1250 280299577 280299581
    0x27050a020a05180d06020a0207090e0316060507030603050304060905041104080316031403010626040c06050703030b1c0314030c0f0d141005031b030601030809011b0b0a0501050301 79
    0x1051880d440b01410403070b00c0341007916807021152420341e10080920201010805601c010410307410f85502411401d070405003214182d41d001d5592128a074020071910003a034826050a00c000ca51140d00030030b29480310201140135103c3c0d900050101e000024000030025001a0a41c044910580c0c1c180b14040108049030380d140078030f101d212820303001005015003188440d17400920b80e40c868180b1000718861000100a036030800d820440107e10385544101700f42d000c0107142d1580c0c9608862040191a15944210b4810303c1403041070305100e0041500b40c2014001c1c5c222902044010707007801112281f50518008500c0303400c00980c04502e0024048100742c002c001100e100d0005400c80034501004c0185c03130317125035101c2c0c00c4142c8101d9442034040b9003403510100c030728050707030f0340c2c200c000401420681007500b8010102c01d00c000341d07050742d04100c015440118220381100d40003800c60741c07502c21000060340c088041920008424504032100320800411040c642d001d200c942e41c0403c141e80c0c03203200b80340c2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 280302077 1250 280300827 280300837
    0x602060a140c071b0e041a0a020306010e01350a0b0d050601030b060f090f0103051b012f15010810020a080a0902040e0102070602090405070c030c0f050727050a02 71
    0x2105950801850380130459a0240c4105105815005603105076610504e514808098804481030200000841c400405801003103400415903c002c600c2c5042c0400060a2190186a0700317041c082c600005600180c3d03030044803403482d090920943c001000d11552410311030411103040f203000b4601070f16900c907810114481c1c0a0294070000800c8039900310f440e80c507110034000708640c0e03000152074115407480d00c42d101405e0003103400020341c07180c55044d403602c00d0501980c0603480c502c00f0000e80f164646a0b038480301c0c00040859018041e40d6548020600808240800c80380300c0079446441d40f13005460646c80c0380581200d0401083d02c1d421100c500701a0182c1c031860480c140000c100c3d60100703030010141c0c0d205059482c0300610010780009450019403d9800c801000d0b5541070b40070445c034a43d0f06140c0100e9501c8507151500e40c0d44000300b80c2e00584140040d190123000c00030048410800c02004002c444090282035141042d0010350592421b41c0f0b00c0d025480400701c42c18500031403041505402610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 280303327 1250 280302077 280302091
    0x2010906030b060f04060f080109110403080702060f131403060c090f130e0106051806010507080c070e0103080a2c01050a031b270302012015010602060a14 68
    0x12212440c00c501100541918000240d211004000c0c81d100703440d0503002400140030548401402c0815140003412448050340b04120381402d21800030112001d00c41214213590b88a00c0c1561195000e00201c0d071180991007502c04140000120119402d05080700d041c2161825611884003c2107041895266601030310907541c00c60b03090003608094039003844103503000c2401519002e62044005680c20940348002d070003042595513200c0521541c10244510302109406e1190612542000f1000800501c00c0101c06000d642000c81c44c108180e200703000d008000c02803000c460107276586900b041320207a0f00440444001c501c480f0740200141090500d95072400ca50040d50038880e88248005541551200c1010303000c140d9200140c0310107140710454400e0380141c40d074607d042030074107802c180f2007000a610742200d051000318080006030b0344400e038030080104880d00c18000300d03142910b0500d000815828009031480b40701c00810700950020303403240300b003111644c00e00105143c6e040e01c050300e041c00d41d050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 280304577 1250 280303327 280303337
    0x80c0901063e0c04020405300a0602032403060403050a05130b070203150f19060e040605060907110a0b0405030c0318010e040209011b020103061a07140a0201 69
    0x4212981c0035200c224003071400015a500d060b4440c142c0c421900c1c140c00200e1401041c01c0c00c40401d40308040020002603c000d4908500d8141841c000500e00041481c2c8031350400d6035101d034001148220b00d4000500010315040350f440c1a9180780440280d0030803601d0240c050a40c2a9141600048148071340b2400b4001d40508110340742c984040720940e00005540c01808010041a03940c4803104c10050001d0001d0b0302c402c0e17100c0ea1507104160502e215a003000501c800318074140000c7c2005269056009011040e072016210745e401d03000c3c009041544e00189102d50300c10200310620000d900f0052040e10126800c0f900b558032030780144c5400e82442100c50071940b08003140c10008040740146a00300b4010b0044034102401407449600e980c0c442000103225040300801d841103540c0000c18141151003c5400f5400c080042000030310140503042c0d885042341d6141124030659020394000340140c56000184000c00e40c0950000307401c5e078051801100c40e110030034080401c5039800b0542c140f00580c141c0d20 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 280305827 1250 280304577 280304579
    0x30207180b0d0b1510030b181608190504061d070f050108180a05031c0513110103090213090203070504140c07031b0308010311010905030c0d08071b0f080c0901 70
    0x1d6010f120710018200e44010900551150312a50b0350030450305c1a40d45540c0c04580302403488280450b040c5150482032450710b0744c00070f00690980880e00522403103000d1501c0350903552882112014003105070300c0d80007841d00d0042407005012140e006410031a2000d01242c01200e00884001d56030b07081881032801c5080595010300c011340c404c59055821a905450039500340300b086600f18240017081c2c0044403254030001d1b15084002c4601e03e00c0880180c401420040e51070000c04440b151b20b010070001703160494040340010750740c1c000d9100c0c18460f030700034116807030401048800b480103001c0c01e00c0507440303031290040001e12860a4050280e000d4041c00440040391105c0070501e01c40d030403060b0308805026020810459105a44041c0e02c0d4007030203a92800d20035455420242c1000100d090110304104541200780a142c800180d082044031080c1c0ba500d1600b0700c2ca0a001d01c0034044d0400040c1513203000101003650200641004059030700c1c0a203050021a1b4a290203a610f61000c1032aa42004641c80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 280307077 1250 280305827 280305833
    0x9030c10120b040219020304050102061302030c0f120105010b0904060506031302010c1403070501020d0509160e094314091905100e0603070609170316030207180b0d 72
    0x201c40c0202c040544003505052018240500d00d81e02c00c00c407100103a002041c20001ea603410450290070120f41034440b00e42914a0700804e8454000c0e51601c0d0040d00b910368081515202c51484c5440318000000811071541c40d096510105d070b04c101d65407031080b414841c0c045140c4c070b08902102d01030101d100901115440b26401560780d802c010300d060303c1400110700341c0c000704501030000f841c0280c4150b0005030354030080c0e01910102c0b03001504070001503010300b0f030aa00038102c19120340181d40090641c0e6402d5540d044c0600e01d4040446400e811100412a41d9190071182503d0325407103000c4134681601c00f60341e038891281a890b05200700310042b901c5c0e03201502c0320700b0b1910f46142c022114121038032215100400c100c05445059070a0301c40329074900020400710241c10052a00102c00302c000d0030380c5914004004203180300900604a07041c0c0c0400306000c081d40c080081711000550060414946601400c019440b2050351040c1042e541c40d400003505035000d40d10568100c54002400049130f003205403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 280308327 1250 280307077 280307081
    0x32206210e0304050a08010507090909050a060b0f03070f1a431505070207080309040b120a0c0e061504060e03011d33060907121109030c1012 62
    0xe81c09032540000c2001085548496082c1c43c058103629001281b0b5052191006001036102e60200680303528115154001174000710380b07a544203810560100e03200c11407000054454101d65aa40e40c140303c0c1b1a030028030b851045044a044401c00710002c20403014140e4801c02034400c0410a5400740c50003190b841c2143c1c0841800f402c040d04d6001d822000102048070708210101c880010b403840c916a035003ca509423500d0140355407001040c070182080510300011140d60f4002c81c1d0030a4071441e25422039000304c1c0c03a0119030350314484003c011902d52a0f01401c0842a50040b80103480d4100d8070345000840a04001d008004103417031940354035107058a040c40855843d0401e25405a0654840d0100c07800006490b8008000c0815140030b4031481d000b50000c00c2c000b0380c07004811502e00c401000800c106205d5182c100364006400d44000800380da8200d02150300e80741c41c00048070018034110051010340da0420141802105c2039080f540b26021100802c8040f0030035010240005102e050301c5d100814a0f5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 280309577 1250 280308327 280308341
    0x15010c030503100807060507051b03030306010509061608070213050105090105010c1a070906020709090c05060901021c020309010e2e0e03030706020c0d0804050601090c1103220621 79
    0x200742105806515008140c1c1171645503440340c0300003040840c0c0001480014010780358240388120071200500111404251a4003005051605100002c103030a10152614400c03500c0f400c08040d40340d0051030f054545100c440c0c0020788240e01813820340880401020700c61107141c4c141c520043c080c2c0c5080e0720304001182c441ca20610f0440b03d11001600107105910072044c0c00740103181d01d8a9008216090480c000d1405029501c1400468145a90003020a95988505003601c40c255551681c0781c0078400144e10302203c000001480d040d44d051380202c0701c6d5001c0060040d607102680c030500b030040b00504210185400381c040c6010703c50120f808190b404541858128201d829081a40c40100e08500003421070300b00c3c5900790762a030340009140c1c41c5800140243d6809141606040042d403c00d42ca0306a96030307105005070184142e0fa0741c465034043e409140c5070290356064500b01d039507600380007024440140c0260810044410910030109060340281000ba03d110030000c0c0d107071000390300984400c2c013405407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 280310827 1250 280309577 280309591
    0xe0c0705030d33030209101215060f0603050402030601050a080c01030f0b030f0307050c0306070c0b04030e0411070c05121510260c10120b0a2102040515010c030503 72
    0x16031901c00c3d003007000b160305498405100e808851a03603145006000360903000406280c0050441e42050020441c2c000c1200e0001d50803941c01c070003101d0104007100c01899150085002090922000102d156050b000240701d0340c07007a001e6404a9076950184110f00c90a801005815084200e0300f490f5540300b03034402c0f1952400d00b00701240100d030303810100303060000000ca01e24071500009022001d0107002c0001c03500f940380680080143d4941104014048440301c000105400074220218061511403030560710040d0004104002c4040e815064100c240d0240100701d0721036842002c001118980440c22200d0f084640d0041c1c21101450b00e864041c00500a25001034040c13030107004030b01442551500c00820301000076019680a0980b10a480c040000400e588990f010f0b101c0325036429803100c1000d6020301501e07c080744544802000600c0c1440d90740112180100c42808484d25010300e200d2001000d00943d002c009544986500076120320f40840000c1c08a101c00c150171000070310505c011684001c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 280312077 1250 280310827 280310861
    0x80912010b121513030806060a050409022b06030201120207170d0c020f0f070e070c020d0302010b0109140d14030d06031a060303130e0a020f130e0c0705030d 69
    0x41c00400092180e011104802c42c16071018001000b6203a401c500550071108900b0f0300740420400b954020b001c5000101110b00451020815041351409501950042e0040310025502d8021140d80d48178551180c3d45002858021004c92181001c03041c400c4006581c2c069480110392002d040d0400080d602801c4103d440407000640f298511094102070003162000c050003103239142c1081c1d002031800b500e80009244076000740f40380252140b000502c0d0011034a40200840407652080816101e0041c0c002e40a504003c030140300c3c10415a040d801840b040200341c035503811464442c42800c5105840070b5195401030410004500424501243c2d950040144011a407420540302280d40952b01d00794000c440d45a1902c0c043e08510401a403c10b03404003050700198200659201164281c070068031451a070700054801103992024150102c44811038802d050030b545064610071300001d050280b240d0880b4500f12400300c1e02c2d181d2041d033103680c0f041c0c00c0002903017000c0384009100001d01a41c002082d5070340d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 280313327 1250 280312077 280312091
    0x1b060408030703230106030b0a0f0902031803190e040e030c01060315060f0302060306151204051b090402090415140a0c02030403030c08090d0210030b0301050c091509060c16031a010308091201 84
    0x2031050b18150010340a02f510140c0c490401503030089041c850300c003644c200c80c2c0042c00002c01003260350100290440c402d10f0513080221001000ca001405004458450350200051020501310150000c404481c417489074850000d40b804e00c20b000321152409404c8140c44c0d2001d0402c09842c143e0007568001800829a01980410800d1110380303500205070414902c114030100018042d05109113a2000746050101d0700566000001071103d40000b08000e10902c42c0b00d0128040c0540c80000040d1100710802c10030441840d2051160500c40484802c0c42083c00c001561405a101005540c103d030361503100c170920524642c1d80c110260300501103054111020010000159580d500c4200c8100c0458400103200807408040c1400d4400c010400380c102e942c1000251015120088509d10340c0c3e20902840740c5402c0e552001403254400d64000380c50b50b1181c0c00300484080c40c0669180100c0c0c1c880c04400c0301c2d4291440c0ba00f02481d000348030190400c1000e100035800307030805460688080c03a0b0000006840 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 280314577 1250 280313327 280313339
    0x24050f09030706090905070e0901030f170307030623060a1409040903050703020d0c0b070c020301020903010606261005011b05010c091802031b1b060408030703230106030b0a 76
    0x3284665204800141d04ea10040120758110303c40c05411400c189000d1890a58281c04500b0702041840014200e001c041800b0b018011180e407458412001c03403030004c0e030f24101018000c000e0502c50181c10103c618040d0110340c02e900522880c091641c01401141c109010000103a4068040900c2d180c5002000c004509850b40c0e644500014140301c0d0b11707060381b500d110307082c004e00d051500b02a88003072107003424901c400301e02180c1d006175000446280001043d0054400b003406401180f50498041d03083c854003181071908108088600070801004407512031803980d4030442001e055402042a2b050042c043c840355205043d64005a50440406500100d16075509821511455492400200c070450305016543c04e0b412400740c0904034100560450400c448000c0f400c820a104000180c1c00020f48840b080342e46008031039080f03a0000580d40a407515040100c0968007c542540010b80b0f805400100741082801041e9085803c070496426a0b003091815802040c100240e00d03489480c5000c0003604d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 280315827 1250 280314577 280314583
    0xf0d0309170a0312020a02250f030b07030516050901031505090406050f0a140a0b0d14070312032c01021c0e010e0102030606031311060c030a0924050f0903 68
    0x708840600c0104080c1c0642c1c00e00402462207403000c01c40d0b60740100000050a0360000e180c41301c414017078090400305420319420407131641c5c00b58040c03400188444c0c0008280414150410310424080e142480ba03541c41b5104180f10b0410b03c00c01402181092100b000c05503c240d1040d0041c2c8011705080311034a0b00c1c1c1c000120004000c590854030140c9402c1040842e1241c0707000660081030900f001d210349005c0130809070103610018044005640d030340c1c08040071542c425088816158000306040b6007141000040350b180d540030300003520551840c0000207511b034803a02c80d00d40d0124041082035406071a81c02040c0d090079440d00da090140d9006d0201c0000600340099580100090703c5002505081c0620103030301b5214403241092140c2d106000b0080c0036100e132412280d0003c10f00303401d0340343e8108034540300c0c0800420303911300b9421160104007042c7d054800802054614060784030b032459103030355070317441c808004003144003d00401e041e64108645901031341c041c0c60440340301020700d820310fa591004a45 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 280317077 1250 280315827 280315859
    0x7140a14061e090a1e0c030503070507050f0a03080313050d02010c1803051e03040e01030b150901030312020c0703060c0e09010e01060e0d02040e07180608010203060f0d0309 76
    0x200d1a0092070912035414440c51110149040c244420482840c00c802015240d03500842c0260081540011810601d03111128411406500c1004d0700e00082d01da0400a0756500316080440301d0303118905010507107150101e02240b0001004040700b4826041d03a9130540306801c083d00796103401c0d101444000000301e041c0803021100c05260700005044048400080107801003035000c00c0c60000180090000c900301040780035041e0f4241900141c2c0100b10b0501c0e07451407003240d1014282548180000c001c000307001c51040d00413818031038001c4816008004100b0401028440100030034075070b14901030526483d13009002d80384111026210311940d2030300d401c0d042c1d41c601c07200040080c9919030014298505046075a025004031003c1d80115810103c0c003902080401d19403a102d082c411092804654554200761010001e1710152485281c1d601001c90003010a07035181e80081e41000000300300780005100b03581c42800001c2810940e0300030341c000e101d00c006c01c5804c00d0341045400c03100400c104250007290301c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 280318327 1250 280317077 280317113
    0xd0b040609150608060603070311040315050604110a0915090902040b1b07060f050306061c0c0f0f080c03150d1b0e010308030402090a06320102060c07140a 68
    0x400c03221444242200840040d0300f10f5000d001c44141441aa51074100940c0c5d80499241000201340280001c03e210600071b5500052800e00aca226400da402c91580196010701420340d02403001c401001c88545850141d0404640061101d00c0208245402c1c032003541111906810080c4101d500d80c2442001c1e64400d4000c140440c0c0002003418950118108411988142c08080c0014038200b503c001c1c0766240c82504201002400300100b112541c0d0141103981803032914138136400803000c03440d101004d0f00758a070911010540310104084a80d00032198660a06160f950705005035407030803901e081c03d410141c03420010584821044a00d601c0d40c0c038900024a0040c0d280780b041c901c0c1c02c1851962200c035a0030810380c3d03003030490041001481e40b0090302c0e041503044554800969924610000400556119010707031720035605258260209004482e590f46600001c0149580c1050016130791800151038104074044200014030104071948071200300b011002042d64011915a100d4203d0961008404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 280319577 1250 280318327 280318331
    0xb070e06070605190603020310020a031b03232a0c01060b04030b060411030f04050a02190914060907140708040605031503010e030d0f110a09150804020d06020d0b040609 74
    0x1110882010b56640f1a001c203500d001804251b0850340032a80f24440002e042d2300c2c1c147c0100e036108800340290414042000071380c25408030103001c650001e000c3c21050344003f6a1001003400611284c41000c070302441000c02440c080140c0c0c00c00c0700b800020001c45c00368a07043c0304080c0310090100d0000c0c043c0c3c40c010102500030315166401c50520000001000c0c0003644211b1619000241c280590b40039258020100ca0305d8441540d903074141a0300b41017500600035400f03812040c0540620304a1001074094450020040040c020a01040c84089406039030045e80031138404005144144980509041d0180d12842181806440da41c0c1c150705401136005640401c4000c070070840d04040700c2409010640c0c00720000d0003801c01560344181c880c8601e603c240e824a03203511245286041c2908008071400d01c8603017a554910317400340c0040500c1c1c07040c040d140710350152010310010300b442200540d010315001003000d509003c0c06d68a0300002c1d40b1002244540b1600d074195a4101d0b41e841c401c10008102e81000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 280320827 1250 280319577 280319581
    0x141516020d0f0b10081b09040f0c0611010c03051515120a0207030e030a0308040b0606070b0c181012020703090b0a0e040f09110f0a030b1e0f040f0b070e06070605 71
    0x11201070500a6001001c17075601071145103030303414542d400040d200340050342c1d4900d194545007054002321b60230050240c0a5074036080005042944410885491078081e002000de4242c0c2c50011000d440d0b00707035010000350503207039580c0c0f00d140b402e410b00c503015070100d0084920340118210798503103c010440320b1012003540440c42c1018103402044070390700c00c40e04501801c43d076400c5607406815500f018101030504460f46d070008501d51104411621030b9600550081403910340b4a07001801a840000d215000e02d58101c200d01c55820241c03040c20100407036884800c111740e501d450b51002504105070540800c10342c6100001c114814400400120030780741d0b0340400340c10f00350042c401918511651402c0c4030380341c80d00c100040f031400f012200c16140d0803a44010300107403400004140c424560405070050b66048244051844034081c4540066805042401a60346220000001a030f0441f4064491004404440000360203508110752111040c01d00c1c080311f031101004290f0380c0e00503030f5003100d5040c2d481e01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 280322077 1250 280320827 280320841
    0x50a050709050c0a08040302030d290301020913020a090e01080604030215090c010309060207120c0b0c0301121412040807143a0f080301141516020d0f0b 67
    0x403859000d44510002402181000d10f86688075206104c0d1810070058000086030425100f44100d89221103452001c0c400300d00a80b901c1191400c00c0b03003210b4095582302c056001c081c04c043c0241c4001050040408401e41d1781c000b8803030007950180000e402040b031420404030b0f552038080750042c06005035000802c101d140c2031a0182c6405032070040b0714440714081c0204090070800150040402c0c80c2840c010890030a41d1600501a020303068004002044040480ca003065100d50075811860007200e0340c681c0c0307407203040001407148002e014051000015411402c041419100070100d008001400c8407207241c090804003005e600260007030007494220203801c0000c1d61119281071000041110000b540d031511151926620440b00b2540380280c21411020600c50411030012124503080041507489005a1518000c154400d0040651440403000701c51b071309080181c002204a020600c2c00c034074024900400003504154030074200da0041481d01200c2c001001c1110180b106881541e011040f420950 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 280323327 1250 280322077 280322083
    0x30c0d091a090106050a050d24020705070e0402030304030f2301020901030c140301122607031124150d0b0403090611120a120c0903030905040b030604020405090a0f050a05 75
    0x1600b2541e06a04052040c00143d64003442c1d841111400c5403111641d62503441c003900069603d00601c41180111281840000c1e207940041880d01c2c8284182d510107500c8070203550400701e00340c6019406500500007800014851200e81c4451401400700001d0740407450055007804038074000d8408240d40200b0020529601801100c1c0080c01c2c90034130300c96581e0b0b0080c403651140814807941103800105080c14041c082c0702d1000030b42c10406e402c00c1801d02c5400c100c86e01c1241d40014002c50006852402c0d80e80516008944d481d1401000403940d070078900003000d092500b0002078000f0041101d80303401403600380c2d10200c40103040e0b0301c030f00034515592819013809030100311140e0144050018211142c460000c020440360000c00d0940750403a10303184061812989059520350180609150141030300318a608050644203d9101c2c0d03880d0384c82503032920301740426203500c1480c3c6901548007001043c0140f070b01d500040d51045030f030701c11111280c0307842d21040d545124001003580d194102440310f0027844014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 280324577 1250 280323327 280323331
    0x40b0f15031f0e0d0804060207020f31020a0507060e16030309030b06060a02060a020d0b09040501050f150604090b13050c0c0d0c0305041202010c24180b01050105030c0d091a 76
    0x510250560000c4c211000d03006800c000e000600703403540000c80f8011584d815032800c80c9080c014050162080050b0103000000c08001503440d4130200400c6801542d05260088440440041d9103042c209021990798501510050b40301c1c04050140c0c034803000358600000d0041004500a80d0fa5540072440c0d41001003403580c005d04003e000c1d03a410030900c080607400151058000821400069661002d0944600100754142e03c1c9035100341d02c1c0e014001800415040240070340202540b00384140c60311040304c011203062031070f51a0800c6040c07200f003002c811682d02140041c1c102500b0092054a9500c118003104e1040311108006c14001c220040302e020f0401a41400203210705080703040340c2450b00c1c0a00380740150b108603600c0d44460580c100859224001c0205029440340069010200382d04400c1c0d480e0000515002c1e030b0317500d401c8160213481e44054002854503000000200183d00307040044526500c010681c6001103c01c0100c3c102090482c17240c150243d02803d5241a2610001d5803800c01d9200 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 280325827 1250 280324577 280324601
    0xf021822020c070f080304050d022b0f02100c02091f08030301030f050708030306060421050f010c030e060c0a1b12030b0405010e100902030a11071b0509040b0f15031f 73
    0x1808144180e0701e4100d00c9c1c10556804644440f0908030703080340c03e61401c9092800881080f0b01a200700c0c20048000e516150052084400d01c031020a8580103c8003042b0781d2901945c08000000418185103940d556000e90484100040041c00e4403191761a14550003a4811944216902505401c2c0081800088080c04644001d540342d403c0c81030006905000e1800744000e1841750002c400f032030322500380004003070603403103025180b4600b50b5019943c000d0102e12440b102103401e0032a150701189001c44e40c1c603c070743c4010f02c0d40c40c149180c1c401c0c11a8207141041d0b0480342195038284410114001001030b0b154640d103540c01280b89107085092106445041e8040e54400300c20303909004000a4040c480340580306030030801170305d9a562a8030035000c0c126103550090401c4001446e0018410540d05185072030b082041c40070341003a629418424002d008840150481c0101c90120b107c01000d04000c0d5080007054088840c5601107a000a00303105070140c9560300c00c01907182d0003042c1806030240c0c2e4449a9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 280327077 1250 280325827 280325833
    0x6080609070f1a0301140d0210170106020c010206191401030f120c030c0b0a06050a03230606031005100302040e0616020106050d020d06020f040f03060f021822020c070f08 75
    0x1a80c4a52041c0f9400180900d9008143c0e04820001c1030316542c03145040c0795002850b6186862003014058400c5080385c1c0c801c40881e504000219105000068810100e40c042e401060980c0d42c0c8032107501000e581680d1542c0041c1c8520115492000e0b0f106040e010310702400c0e0b00c0e2001c0d651441c003262507003442e101d1101402842900b003404a5000114468946e400c285120400d9035100b40010042545030000d41e0b00c800c9082001c0144444030305080090f4100e01c0c000c4841002d00e01c6141d030350300e0f012030b0b4a60381588040c680c1c10082a0b29000917030000c06202141101c2600c0740c1c0054143c1d4104001011a03610000c01c001d1a40b1038400c4c1226a00c1d0b041c002002214200341c081a203402850002a001e5a4203108000030080558100ca008003203162080d52074a481b88041d880d0700901b0310040c0d46a6040c03081021300880141300300c441140d965400d030580c2900303031428072407550b2114030a003001410200514088507450300080684540d0400504441410200500300840c443d030050f450350b038 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 280328327 1250 280327077 280327109
    0x180f0303080406021b0607090806010509460507030c0807020d050a090503190b0f010b1806090a03051609021305061605070b0304020a050409111306080609070f 70
    0x40d801c00c25681d001900004003585d591aa41d901c01950740708991804014440c83c8204603541d5401840102076501003400da40c12640d850040040e282010b98210024682c1701d0403242c00d404d88060601044c8955000c010552840780800e10701c160000d40b02c2d04030071038072a41040702035545440380c08001e42c19820038000c20304109100a43d5a01c284401000f800000115060751600400541c0010b2900400300c40490384075a0440ca0383c05603400c4100e0718401047c0108031103e40c043c100e541a140000c824506045414130044040503038a805560004000c11800545441d402e00400c046d40c01000182098450384202484928130381e44050381c0395205119020141d2000d401d0001102c00803118641c4420404c2548040148143c100030000c3c030600c0c100081e200300b00006140700341d008440d41c0107a59600c1081c00b007a201900b500405c0e00d00b4680c0c4a10740352501c02c1d89a001c0c07403512035001035400d0310390300d40b0380c50710b03c0c259124440d50744425005c00141d0a10300d00d0101030210409807400705 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 280329577 1250 280328327 280328333
    0x20a050d031a1c050105010509070f08070903021801032307120c05030a051c0905060307030c0504120f060b0103140f0402030307060606030e0708030c0a02010c051903180f03 76
    0x500e020a9100c400c154a880c41c0701000c0202ea000c040d414100102000d003919155814010b0308021000c01321803650808000041ea40b4207480c255120b04410388400c00b04010101c4101c403da400108048141320b5001408000358484907000d52441800c1100d40070994110708001503400c40114510b4000600c2112210f10100007062500888040c401c454881e4000e52802074009e0805410054040c42841d08460034000006810300c07501240c90500059045200400c55801201d400b81c2c6401003000c00100f40002d12070392101c0031010b070500d051805c10303407102402500c0c50720400080d511a89042e400b41c0900280c0d12030101800400d00b010001008440c09406158500802d20112655810002019034809000711000150f0020381000283d44a08000d0010301d5210602201849242c20114654200100f10740c2e009060400401c24451558011650b03101101c0f0221658061280c820324211740124241e120039210303450307406c2080351954402e03050b04415401943c030140036200c10004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 280330827 1250 280329577 280329583
    0x9070e0103060b032a0d06020c01140f0705070804150c1b08060112021f020a0b070309050606101b1a0c07021507120503130c030311010e0f0309100210020d05010312020a05 75
    0xc150594000b0b591b02c0c902c0c2030003002801081340c1000c1550030644000301c0d08412181c01c1e03208050011428060351a8480c044403103011310440203281103420041402001025402e20303414000c946032241c0149034554942c9800c14425803442000d9440340010700c4a042c050103154050080c2030b40c007640d05156600015041c03546500c1c66201c054202c0e02c0820254801d0000c0c004040d0010350320b0b100b906003180001d00410100340151098041c00b00031441c5464108803201d280e051765500d0120b0503d0101c14010400740300e04040b2416441480b9a00c00d149090300414481da1503100003035101c500c0d41c014001d007185192040141c5490070401d490009401c9841c0f082e4118442c0750145e22079a41d408800c0344114200009482d0b00d101050000415a1040c0740314031203010f64000f800b4941300c904005550380300f04003501580350018401a4820700702002d200c007010045104403148185541d803d041241c0c0503045450885459100600602020510013100350070301d44028100e5515903210107071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 280332077 1250 280330827 280330903
    0x9030406030b031005150109120b040308060f0a09020c011803091203051b07060e03030a2003070c15030b0901060e0f150f03040516050a03060509070e0103060b03 71
    0x9040d0340d080e4540b400e881c2005000c42d1a101d240040010342403444011980040c07414071507002624204001c01c190b20b2032100308244070751100a0f84801c1d10f031a6000d840d95030000f000d0361b8000040c80304098140da41c40c141c8000602c010000184e407107011038002030075500032002d61004c0440500c100c10000b50301c150000200d8600012407540d1454524044a40d4452802c41d11101002c04040c03500d19803000c0f07011400c840d9640c4441d043e941580060588074010751880101080d114013a001c424070601000e10010f5801c5410341e031401c0b09079903801407012804c0d00020301820081c030740384180f42c0d01845a5520010100c070703070404035858000010540c0d402c160002c0e01030f400100c1c0c00310700c1c2d13120004030442604e0202e10082d2a19100099508950011503041e00e8510031030075032510314165207041c035003a246d02070544065681503455070700250001500c091000d200740c0c54000b40000b0041c5406020703510804010a0342201c0d10101450000a018400002d2401c3c41c006044c0402400c10a8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 280333327 1250 280332077 280332089
    0xf070b01050a08060a0b0307030f051b04050c04090207150e1501060302040e0a090213050c070201120b030705120307020411121e07031815060e070201090b130f020a030308070e030105090304 83
    0x4960820001e022030305003c1d0f141d09c01400344400c030318004100800414505882a600203410703140c8141c42e003c102c20389006031041c0558080411041c00301f10400c1d00200f20250141e810811000c903e00302000403120054443c030090b07002441002da901c4100780049004161502e03041d03007002e081c848022000800605811040c0e60764018510440d01d4016850b010082840e900704a2840c2060b000c00070307917101c20400c07030015411340c010326201c3d10345110303404000001800501115052030244a5000c190610510451005001da60016501d5016480c03088410309400740c1c0754900d0205204400d5409402650402e1030418510007400610000c0383c1e00680340d01d00407035954111400c43c1004072200401421006640f0902001c2e080250045c100b102d02d01c07240e80c2050b03a901c0908134200c44000000410000051001ca55402013070300802942501442c0342c80755001c1c4a078005080c44241b42e20880128a02504004500d03800150403140843e065000340300a1408021143c0c0720320940c0100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 280334577 1250 280333327 280333331
    0x30c060f0504440f0f0303040b0601050c01020408010605181b090d2018010303020a150605120a060b0f1503150a090614010518090c0f0f070b01050a08060a 68
    0x503c06094840514002d041c6070340162030320b4422030007090030b07924030040703000c0d21849003589984200c1800248000b108001c4d00245085032120750703032101c400300003400c2d540c10800140301480e1649020310080004000107400040c81c03c2ca440e00740184070703c03070200d20301c0005901c1c0104402d2a0305000700054200c0c0782d04e103a0340e072400c0704800610010b8540e0f0000e040a21303039405000c0c80b020000040f43c044481101c07010012040e0840c809120482400000c0c01604000b0f12540019171686a0032550260790340c010441c0b0f034607480030070864410080c81e0040ca42c0130080e00420721140b4800c0c0d0014860030740c0e410050000d110007240034504c000004492001c40000000e144800c50560a442c8541c000d0040e403001e507660f5044e070b014101500602c0c01e046511241c00300558080c00031a4610801e41c000301c482440007c00708204040c00030042514123100300840808045c0e00c500902c000c0c0c461545068031042c00f0304250080d9441600094004d199140b824002410006001079104400c0c10340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 280335827 1250 280334577 280334609
    0xa18021c1403160515011a0706061d1b0a23070c030803040303060902030f0a18080409020711060a020a0f05070e0103031d031209130b0d0507030c060f0504 68
    0x249011000c03208844154040403c20310b520010302d149083c07445000b80115807840c004522000c80548080c0710302142a00001d03800042800520042c06025008500018880781d0318130f00d08141505140401c6004081c500800c40a0552030003408016003000e610b050500102000241c280e40342400132652401c44446046540e800c0b83c011650354603802102e0f02d180c681d403454416425002600c0c00c801007400c080001c104250180300b40c1e440f460703528212000b946c1b118003503c0000c10120307404a140440d115054008240302600410003000e00c000c0069540e540e07401d021003a040c4941c1c640c2d110700020843c0c0c030031065000820000468100c488080c2c503d0451400c10b18028103627106040c2c41e1000c0000009043d00720300c0714500c059611601c144501408420542c4810300901610222101400501102e08002100166141c18168000381c035082c0c440020340314104049003114207900015040c03082003e0303101040c000f05603505180810044400c40a0700e40d008602580c6420064045 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 280337077 1250 280335827 280335833
    0x7110d050901230a020609122802250911032412010608030a0e0d030804060e0f010504120207050603040b0a020f0706020c0d18050307090c03061503050a18021c 70
    0xb80605030500c3c00c184580d441d04050000394a5040455a0f1782060007009094503240800c0c0044501c1e081d89403280c00003400c450452401e2056070101d000c02107100301c0800c654104d12810001d00d030b0240c003c20402d603443c904001e80382030324101c1c904e652215606000b401034586000900150803214020507007294012500443c210039000b0070000d5156090030b4000520400100007070041c2c624990310200c0e21880340c024010205d191440060000e14044006400b01c0c00944c011211000c0c500d00742d905001c115081203003034034010f0718162075070000240125146601080040024030043d44c1c121b0a5251680b12401000001060305498580014908035181001411208110340c441011911030714156010340c1d81c0c02c3c2c0001c240010580b1300844a884581d000d01c1101207070002001095000d040c11107641c058a00300d2083c006140e20fa4030013149544160704489054080c03560b000549117403070407281c0c00351641c8001010f1055882e02c611409a100d00002d40544a1030303940c3c4e036a01c0c000e13600e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 280338327 1250 280337077 280337117
    0x80d2a081905030609060a150305060418050708070602061605070305040f0306090510020910050c1e0d1206240e060c010207030815030c09040317040b07110d050901 72
    0x790305840388001444454910301d0304503002d1800741d0020b6a255442e940c458003408000d20290042d540444060400304540a2090b0803050340b116000c0c02c04203e50900c0000d201704000e00c03207400c0350280c201c41002d012204003042030340001d0800d440249201d051040030b501907000101058010004d0000d100c1c018035000d84110390040004030703002c405280d40ca00340340e00240440c0c90111024011100807100003c2103000780ca480c03400c018180c0740044064042a65103501c07903030310f02070b5500800240075021026180c0c05d40c07240c80c50002900e05441040340003000303032501162044a442c5003100600c0030b184035030400482103100306100d41c2c1c0341c01c1204003680c1800d07851081c10703030100000401798cc0059064001c1c0fd00c4502c030380c4a124042c1c503000307e2800684076484903e07405920800860a2074030b0400d0803a5042402424130007200744040c0c4451182e03031030032901a99900125802e019115074000c403065108103210025142c10044490020070a00c910038116040010200201c1d0a00300c0907 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 280339577 1250 280338327 280338337
    0x7081f0b0301120524011e0801050a140f0c0405010f02191209050307050f0402030612191a060904110609030304031a0f0405070306020a2106080d2a08 66
    0x440303200c5071690b03511002c412038080b82d620104c0b07150150701c0581c0d4034030b4254480c04040e9104644800016820442c0c8200f40e80307021000d2018218150f03200050014003842030718082c54043e103010402c03064150030381c180076401070030440f5800301c00000c0110b00c01101c4140c401f510b50910380407910544211049151000041c0070680e0750801c0b0b15080f0410120610014022045481c4c401600341e48200f0545c039914944141604810303043e4002c0b0752850035500070b507172101004004040414849400390b15020f840202d5604618441d5201000d028807034115801c201c44e00401c00d2824908040855076001d8054002003001540ca4040728042d520501590110310307011f411240c989680e410070341c18031004254030381c21042804000c40c2d03c0a012069161090780c00400501e0402c1c074641c0e501000b076100c3c0c0300c000200200030b0301030106401070324466000070301d01d610041450342c2008604c505006504001e40103101d1007641480c640030407580401c007242504d403580d0b4154034640c10004030611032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 280340827 1250 280339577 280339589
    0xa091d16091e15030e0709110c0304060806130b01023d020409060608012909090a09141c0309050c0904030f0206060d150504170a03090b0c0307081f 65
    0x90b0444a81c0044840c0342c0034111185400b02607054503400c4402e900310791444e81504c50a400c03484041c03104000c07580146031151105500c0a10342940039200c1d0b0b055400940160700003459480c00d00c620f80c548858841481a000c2c45c0c2004004041310000c1c0d501e0604804d440d20302c140850803000036884145000020340810940c01145a144c080d081c0000e40c001d0142303001140ca495808598144901c801314140d800d1444490403000642c440c05a495080b051452826a801c0014641548070708030083d006503440180410310a03041e00e0300344100ca8107605110211f80c840300c08074000c812101c01480000da45400c3c009510206814201e0802d401c0140f015000803206040c4410160301580c094a40720b259402c0e0f503000c0d211101009400031030f0140c06000b40400c880c2d112443e0b405580130980052044070b00040703c40b80d9081d400110382216130f0740c0001c45d650380c400c42c0c05e0140b40310015511a030203141132495840c101b0070203003021102401c14020314444a400b200c2c00044040388002400e1703 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 280342077 1250 280340827 280340849
    0xc100c240c02012a21060504150305011a010905060a03020403050604050601083901020307060c0504080c011e0804030c050106030b2d060f01020a0b0c0a091d1609 71
    0xd000e070007030b0191190b1499490041203010b000303074840c1030415130703258005030a5030b031111441c0d010031030820900c010401c015042075455000244aa443c1c1c413505080c10141e05400f00403601c0c60502c1421609110b6402d00c910000940c4c090340c0e07a070305c03980b01d0060f5541190070b9600c0d07042a01c0118028015500000c00500c1081c06200c02d1240009040d41207682c81d03411100f070301e80c03a0640c0343c50600c0c1c03050124100721420300240c00d5211408844c50b041784030620440f0b08140300c9490320b0301031f01d500e0025000401c0002405008401d02440142041c0c0800e080204c0c1c4000300c1104000e5030340c11192080300b00b007280c001142c10107114a2801d200940c000009100e095100d04009524507400e82d81c00c035820081d080c80121420703581c01009140c00000403045401d42d9408107000b403645c00038640781d0442c0980f43e0000005864194881e0140800740304580c1c6449885001410410ac42d03001075500c14891040c101c02c4145058640b44d12004800f664003448070343c0801580e80c50843c0d08055000d403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 280343327 1250 280342077 280342091
    0xa1403090907050a1b152f160203061003050c0409031202031506040b09100305090a060b121209040e0c03060103151413150612020f130e030301080c100c24 68
    0x200403142e900a040303910401c1140311002d80c42d10f0206c1d21f60413000300360703941d1220580038449010b1002e0600030007000c0f88820700c0b5005900180c2030400c1241c840340d9090b11450300b8010b120040007101c55a810030307642002380c82030580740582410b00310140841000d40020010b82c0300d9190b840b62000707403000906032030303100c58654003000090b0b0851702c002030040300d0001d59442c2a900c42d0250318050001c0d0000342c07070b03a0821500c4142c09407007070181c416007010308038000e81d200180401c95564614424681d01f51941e5a0408020580f480c1c8240d8405942c404801201c03641e5000c81c2e000d045981c40314030103400503a5280244050a1420404c8070740f4000c010801c2421140541443c001c1c611a0107001c454600c03d4250000f15080341c0208000c0d031080303125250050402d40000d040c03611000740007140c02810903410f0003c1e141e9510080215400100041224105c10441521005402c40e006501007807450802000c0000c0900050704c40a610a540300c3c60030001c15001c006089500b600703100107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 280344577 1250 280343327 280343333
    0xe010b06040b181f0f03061a0a030b150c12070206030106180803040b030708060a180906020909040c030209131104020d0b090702010c09080a050705012f0a1403090907050a1b 76
    0x1c3d00a403403a40841e058050861085200c0e101f003d00b80c618249200f07000b80100708030101242c0028915806055683c01000b20a41c3c8000c004030802070215001e990390716400c400b0905003100c442030104010300c20301c00b80c401603945800360b9040d2403040c0b40401c180003461200503001d0800381d0000d106030100080201d82d02110300b00031807189009890785000742c3c480c0805e01c0b124541c641708038014210301228184251901d81c100e00e0f201d0340204030141c244a0320700c0029801402c141d90880e11445140c1040045040035a50990701500c9002d000107121301d00c0c1c440c0303081020079a05591240f503000a1441104800f80c0c2f0050f00e000e03010300342d07200928101c00c1c041d0080038a8800d40c80881c1500d40001405400010800f05c8180e0100181011500c0c000c019140f0742410075910625020f0949500030f0161000c1021007002d2181c4010001002a410300c41141c1284006146013074200b0480d5800e15102c207a034003900903080340703402a640c06550000311004410341e45a0000500c5d289202400c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 280345827 1250 280344577 280344619
    0x111512011d090a020609220605030c0306100501081003060c0306080f031305040c0516030302190305070c0f052a0f010306061706030a170a030e010b06040b18 69
    0x5880c0c0300e1a412008141100c07820488150485210500e5845050010014100180900340e07086011380050300014600410310b1030070800804c4030740000e9035440200b00c0e0380b80400004a0804d003d13000f4001e9404c088095240090441c01014180941c135800b14202a010025000003140c00900400c4200320f0004011702404151040301c2c1c80744150121116001400b000f2a000c0c15520301c002d642e084c0c600420302000d040585005414410b00f84148640801400144c0c3c3c07009103c0e640050352000b02c2c8030710a540c00a40d0088004040c41c00003000302e2103030044070b690211034004040c410690f0f01454414609540c0b160711500c00c502020034400280c0701410740b606068001c036146070061100d10011000c9400b28400c0c50700283d6200c071898003610302142d0440d00a0f0700902036600c0488182c0f0f0b1180464402000c03112031050000e8030344001540761080c180180400c0740240021040700c0001112802203020724000c80f42d0020748205402002c00d141449440301400e09040c003d180195409 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 280347077 1250 280345827 280345829
    0x320040e01020901090b13060e040204030204020406090303080a05060d0303090f1e0201120203040308060603070c050303010303081e06100e03010212010602030702090f0112110d020415141c11151201 87
    0x101161580350042120f1021001351041113801c0c0e2070003034009203844803c0389c07481d0b591464280c00c107908010200260722940020000f510346505c4031400b0a18518000f0014203005101c0258680782409104040d542c0b0035046112a406280100d42c05089040207102c01d4613042004180f08806086592046251840c1c000749074003d80300d039451001081c1c3c5100c07c0c0d200c00c607401000100c0c450001049480d10802858120500b4541004d001210f6502ca40c5140e00a8205801007000e100800c140100c018070385804268848810380c20314282800410040b0318051020b40600021180840003510b01354190f07001e91600c90142d00007540d4614029440741d023b094160f014800a000003203840701c07840c0c406812640c030098034010b041c00301d448095007201001c1b80281d02c07041e284522405641d450240341081041d2142c60100d1502c0c1140380c0c1f41d540e0f805602180502031006003050402030403100215180e41040d41c0f0f11244068100003000981509103514130300d01d000c5003440221b9200d15403d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 280348327 1250 280347077 280347079
    0xf140f01050109170304170708030a0e1203090901030818041104080f0303040b160c080a0207060201180201051b0c090c07020901120209070f02030c01060801020c060a150320040e010209 81
    0x182c21a44c640b4150488818085071201c030700e50040104000038074088541400180b085000d58040a4581d40c005045500c20b426810014420003030309031081c901800c0001c5420a540d00071890300c91180080752885405100183c500c00012444a1a03620240004800b0b4440140204038040d40900c000100d50080c1c0940819803180c402500b002e84c00000403039020ba5080450840c86503180c401c0440640e450100400400008000300d2000a40311405002a015640c015050950600c10000c0c04c4980300065890700828441c900030150741c1100490b451000218407081d6441004545246001e00381d41a450b0001040010092a241144040c11100c2d2080716800300d00d0340d8400424003c070a4861010354400c04210200b0402c6004281c0c1c580d201c101030041c4da0030050500d0109007181c1080c1d01141d8280d400007054a1001c000344041d69000c0d4180d00104001c103284101e05402003020302004144450030601245070368040c0480c10b0b03154800400c1800200781d0040250b0207900301200381 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 280349577 1250 280348327 280348337
    0x2a0319110604030b13291b0301060509062d031506120a020c1e070e0a0c05030601050a11010c0e0f010906081918031e0305010305100f140f010501 64
    0x61441c0c5014000c440c11690010001c0c0480d44801e40c01c41160b100190302114841601e1442035488001c0141210040303414218140380f1b480c0148082017a07001600c000500640200014060079401805032502d001c810369140b81c0701c00314020641c2e00c48007045400b0f242805201c0900c6c1d0055500801148540b032540340300d1591003602d10501016004001d10030300c3d415050000525103081c0d5a01400d00c0034908821100000002066401054000c81d07451059400041003484030130320040e481904100c60303100401c1481342c0404010642e00020708039a0401c0000282c003195035200c0d01c405110082d901000300b0840da903c0398044c00c88030f00c10b140e140c05003031000195890740d0f01401650003160030070340700c000d8103641e00303c1ea034242e040020441c401210754030fa40e144002500b80420f054050700c01c4d02c0300c48c060302c3e2441c09013001c0d4809500750010142404014000550013159903040e01c2c6102d030000c9056240e181c1807001801041e0b0341040f02441c450200540d4556085100d812030f4003c5c0c0394 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 280350827 1250 280349577 280349603
    0xc0503060a0c0908070503030301030b071b050706030b091308030702070b03090d030c05160b060a0f1203080f0412030203041a0a060905091204031101030605030a0602030a0b0d052a0319 81
    0x10740317501c0c1c400c684a0300340e15801c1440104041580c1e4030000d030b400010351900c0980120b010445181c21400c9110940d107650010505010050300340c400c500c5250b0044440301a10300e0000304c81c007211b404450f0300a001c4400480030411150082100300054182900215228904004030b170f5503480c1c8452500e8006070070903910f00c03e075601500031181452201006c04090510584580031001e00142080303800c2605844005034003900b03880d039140600703d8404d012403000d2440c1802080c0110150601b5280801c40e028803002030380c80403031203840c01d103503050160722542e440c24034010b4a0007462240c807c1441d88000c200d8003602c150301c00e00640b1007528007041291920101c0c03940e9000008042141203108220501c085207078050030389926801450046080d541340e0001c00d0a00c440d008048540715004002c2c4003c4110074014a01041d1064170a520341000ba40c480035500d000d10141d00500a405c0201c41514140c0700804120502015048803102c5660515280d450984802d003510f8448900384 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 280352077 1250 280350827 280350839
    0x30201090b010518070e060c0d031e0c08040b0a09140a02010801090c1d0402090315040c050301021c020a0903020a0b1c05010501140d060e0c1206040c08070c0c0503060a0c09 76
    0x144800502d040b0790584130081d591001d05890151005129a6100c0420f101c0e00012405c10010400b02140503540460b084004910609801c0d000740c5104118505011201090030741c049502540990400e0340601c103a19103601610040c03000c00ca01902c150703111901c0304000d2000240360041e0a10070b80c0d644240360b91f1526004100c82c8518042070002e110f003c2e104007090001c910301c42440c10b00610051903c50180006851315038482c030311601035409281000207005558001c00010306c8107a009621b4034405081505110f01c02e004200a25640404c500c00c2c4180f25101c07000185902a14841d9560344541c071886071600f000340441260340c003009040c0340d80b05003401030310304079401a11220180001611800706540010074940e58165548100140e80a000841c0d44e001c1d0300000c9500e41c1ea583c01c00c00548200c14010a80c5010706d04040401c0355582d030001344140d0144661508030585111460440d081075000c0d40480d6051041d84140b02025000303520500c0d0540950320341c8846156640 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 280353327 1250 280352077 280352089
    0x20c0a0605090c01020a05060c1b030408161d061201201305040905070302121921480b0105010224010312030921020618031b03120103030201090b0105 66
    0x6c100280b0641015004c25140500c0d50050107081c0c3c400400d02c01007070b0041440074699001640f0410aa03489242c04c0201c024200d0440000741402041842480301d05044008084002600300ca010f001c541000700342042c401c3d4420030404265818022006050b404081860f030400001c40407540304124001a040c505031140b10205a4002c01400041d45540c081026251700a52110124041ca40859601d14400484c82c1102031041d1144030707014a0f00300423605c0103d030040c4800c0603c2051072000218001341680c05e0b6240a0441d90030f0f840b001140515410b1a90602000303008140b600000c208000c1b520002074181c82007a401c40c2e506c07050703400300000c106a2104100e100200440700601c08620100308120a10f2a2410301040480c10ac0d66850740c02102c04072528100484680c0e0540a581e040c403a0a403c15171000724912210f5011100c2c40d120701c1007820301c0e803500c0c00d030000d400044030040c0107a944040700042c0c2203000d580e5071304010b4003801075080102d91100002c2e001044d11310f004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 280354577 1250 280353327 280353343
    0x409051b19050306010b070303021e0307080c0306061b0708030a0e0f040501051c02010c0b07020f01060504270203160305070810150302121516140403050d080a020c0a0605090c0102 79
    0xd000742101c0c6d02c0d1210380c050b95032165100380e08143d0200400030340341840e0300703000c12203035405080d42e541c0e85011000100785900140c40d01c100c103042002030003110f643c2c1c00103944da080600185e2519504000c011035107080d51a41c00170155003c0811005c4020780c001c0d0455074510801d640c140822075448040004a800034000e42e54006038800c2d45c0c0c1818801c00748030b000e103c0c0c27040c180f089a1550507201d03001512800c507019001030f441480c0c0318201d02028003514008150540f020701c051141b2551103051089030351020b01e05034540d6001d02041d90740800000034294a2404483c984079128200036480c0c80e485d0207a80710314450f00000c040110031902c580400050300c0c55140503501d046074200a18001d91600e00318140c49004205520b80c0d16401c42180103454a8800c0176030a115604060440c440b09010402c1098040c03000300701082c070100e104010300c0d01d540307024940e60380c0781200030f4001d0103101d2040540380708103c2c030b0300100070b8658011801218240c1c1121030b6419580f004a170b5403001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 280355827 1250 280354577 280354579
    0x1020a2a20060d090228090e011508010b0901080c1e130f050a060503061e101e14040504260903011a010e010f080f060409051b1905 58
    0x300480000030a00240c001e0329100d1007040191000404200000c0403908070465591841c0d642c0e12102e001c601c1e05203aa03c43c04500380d00c500f40348072940d00d81014580841e114000c2c0d00c6444d01c100c00b034807090a501501c25000c9c1c2c1c810800400c0d0f100c1900b0b6000b4080740201601a518040002c01c2080c1c0010342034140c51001090303080700a05224102031840d00c1141c1181c0c02002a1150b454100785500511b889181100b500188a1402460b00416607529a01a03070203a0040001d0183c2e2000082d00080e00a80c1410f00c0c040c26100c8070903044080c481c9a000d5030f022100515107180350410b10030408115003c2d140201d1418400070200b000301c3e002030314014200280030302a0020504803804410a01c402d201c1d845044c4030f044000300742510254015001e1001e4050003420b150340c1c21075a0700c20203240c00e10b000380c0c1010545002512074030700a401c803082c0040f03c0b00040c950f075403943c2041075035a5000c42900d142c14600c030041e04d9684070500240f4401d00d80f0607500c01520307400c0c104040072200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 280357077 1250 280355827 280355897
    0x516080703030c170a080405070b090102121e070515150f040504020a050a030506013014190305121614070c0504050405070915060f1206080105070201020a 68
    0x840d56800340e4204024000880d401400707500c8540c138030050580a0421310615032100d50a030b15103458240e0514045070400c4c0f000719024810303510b0741e0b6400102d881514502d4021030f81d480710f04422a041300c2422404a40d104400020380c00d0810802080c0d5140ea034400340700c1e0401a8035a158100c1e0501c8000070101d402148038100c0b803c040c6040c1d00314641160000d4601480c49460b030021440150700c58005940d0345c1d2200f4010001aa8541c00300802d007401050103204120b0640c401c08130f4510aa40301811036401d40c508014100c0040c0141804600302d4540b1051700d036400d1502826941140139000c2c43c060014002484100044107003003911000d654034009801c6504040c140550030a03c41590403803006d08001c00c2c503840354400d641c041c600800003041946d03c1d100c00142640c2051048201c0d0301c6800d4002c1110a40000031914007030510b0524180802e07032080b02d00014071007036110212a40c240001e1001480d010740c020112000300343c5d1842c000a5010140306c007110040310000700209 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 280358327 1250 280357077 280357079
    0x313060f12054c18060317070303110a080103140d02031b010902040903091a090f040209030a2321040b0a0513150305060d020a0306020a020102070515010305160807 72
    0x1103092000c2403901c0e00030415034816411000c1c441c1c0c12528080c40003d2540420035081c0308052650080b1140080006002d101550451341c45408401440d40c2c5819500f90105500d01014003d4002410140c10f82146644929903020001d0503144203120076a0318004400d241902204003181c5124114000c0d00110f01d0008183c0c1d10003606041c40d1b0001030326551351084070006030342d5401504c2000c3c0c00780d079501a07114240403041000c2c803241c10080b1160001081802c90a4503089510301e6807002c2210010303251402070002c0b90034140d510000a002540140d070a48124100040f078450343c54003907040b240030040701c0c46c2e0310706050100860040c05503010301003048121560001840340c2c41040c9415814600c2408400c1c401d0904c54001c00044542c1031001050b15600d840b81079840b9804966206044045030045030007100180000361803140c0001d00d815100e8000d40448400e1907001c001c940c6a9083d60301440c100044c2130200322524090078920442d0264030381c030814107980d10721015141c42 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 280359577 1250 280358327 280358371
    0x905010819020105220b030403020601120c060e04061206090c090207020d0b07050415090e071704020d111c0b0937080c0d120c05090405090313060f1205 67
    0x54200303500e1003080142c20b190502a11017400400d01c000e19038000340b1903c9042924020341415016041f05000d0240c2102e035501240812480800b03c9a507070038030000c002c108401042c0a84055086144410300c0b0b0281d405c20440e90740d00525119001e030b106540c3d6540c84003a40d00981c0719000c07002e980060240c0300103001c100c0d0080b00c0c94005656080052805039141d2031801083d0156407071b44041118041e04000c007200030700c102d644c0450286403c01d100070541c1400d40305644040c102a00401105084d501086603800c2000001c01e4000c1c01c400305548a1100c2030702083e07054004444110076000411100000001c20070441d0600d500001200d005c41109586a4200c07010000185510800c0b1607003c00c0e02080285521110780004e400318a000b01d102810803060880124141c03468580c206440c02c0d03000d0180c520380841142c0221340e9071900880a403450113000c2d41000c1e07800140e14001080d640185000c0020f1802e40c44002c1c88180a0052008644040707443c03900d0321103140a15602 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 280360827 1250 280359577 280359587
    0x1140912010603050d09030302010b0a06050f0901231e070b0c0307020111030411030610031707050705180403120c0f050a050c07170f01020906041221050409050108190201 75
    0x4251480c00000600303079540e4651900e004080c1c1071003404540140c0050091543c203000d0f403109807800792441265a0b04c0c12000400f10700c42c00203401c4580c41301049807662607104500a14043d084050103210b0040c0c1c0b15044030b41c95005864a0f8000c00380c14600145040c3c500c000d036920036400c00d00207081e42e0350304c00e1686070a900050044003155610645040796818090140d4025406401d0500c64040920141454440d0140c03c0684c0140ca0010410000320166114a001c141c00080152100e03001c0c9422450014190420380d40011150404440c461484545902c1a03001e039490440700c03403076034034482d0803921189035142c0012001c0007444c40481c02a0000d2441114900c3d1131881c010130700d18090b09050007500700f07a07811480182500c5a031042000a88140d800240017140750001d0040010741d203104074414048140d495420ba201402420310420b030070100c1014090041541c1500d000b4440c1e4002d000b9507244514180c0042058080002c1c0c0b8011030340c000c8484500c07245e9039001514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 280362077 1250 280360827 280360849
    0x151611100c230301050f030a0b1b1c050f160203071b05090f090c0f0f0907020a050f06010317040e0402010c050708010c031d0d020d0f17150f011409 65
    0x1c00e00910510941000c00d00c810540380b807000703100403640ca95041c0700402c80d13596203038a032592190740210300078030200d544041c2d40341d000655010311510f02e42061100e4000c134012a030720322041c8041201d400b140340505400070341c40380e0700c6504003603007607035801304003003103440c0c2c0704c1130142c01640140108ce00041c92400107c45111014034452141c030743e10400500c0312a0b0031980351010316946c00502c21600020400540d502100300d400900701400340e0089900400312482251140c1c0d89800410b5450707000b4044c1312190b0b90031030191441038401007030300f560700c4500303100c1103d9000c0820855405070155100b520107032082403d40040e2611180c0044908108492041d03a46000741800012460402d102e40c02001e0901c1d240070421b0403401d2000010341c000206043e83d0f680161350322907a0380d5400309011446c4001d900300000c100c650600111840001c5900c412000f04022041c400d00c2044640c490144131411074050030000004001107554151100e03042c2e0840b00d0901041e295440c042000c41 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 280363327 1250 280362077 280362101
    0x3170c010207061109090a0605100806040e010213080f01052403011401060c0c1706160201020903010606050d0c0f0801052806110607080f0610030e15161110 69
    0x7606184003621540b04590711911003010300d00c4005514402402c0545070a54000d070246401c105107807420300440c00304e20740300c00d011041003e0400002d9040d551039006502001010000319142c0301e18100b0111101c0041c02002000d21600c0d4001c020800d0501445115000383c80e01603a0800c144010350ba844400304140c42c0d419500d40c02074400300300070103158500910090f92441304039070541c182107041d40a5134100f50170300c420ba4140600300d4880055001e03080a08514403030b2002405100490080c01510540766240d400c1030000150198010003402462071441c20400a1810701c400503180c010b0750040d21404034441000410803440e1407030351610151700b00540e00f0b00c846040e500d80280208181c02c0400800da154240e000c00003070030070266078400740c5801d1008640c100700c1c10881100400400700740c407840d401011803941d24402d81120590786000400c540c08072544059141402008440c0f00b0410b85002618011651080c884000158000d401034071804642c40b0318030003c0d029541e000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 280364577 1250 280363327 280363331
    0x1c0e1507020a050a062007020d0206070201090b040906090e0d02070b0a020708030f030a060e1027050f06040e0a02060f0307090b0d060905160e04090c1a04031b03170c01 74
    0xb82c0c0450300901401c802103100f1000018202010340e08010081c4103070040801002e000d0014a00603203800d00516201501120103a0f102c0d4818401255040740f40c0e00034203c414000302d4005902940c0f074008005560f040030041c4001003408081c1d507550f01408007103c005a0140c81c0421100031600014a040103851058480e03880e11030340b42c07624680c4074441e03000d40040d000041000d01002c0d4401e000280045120344011404c110710711301442107807800b403000000700604403c0d000641e410030ba00c0c401501035505002c00d21305469015034203503086030780703c1c0541d0900c0c1c0f488000c0000440c03541e44159000301aa0704180c540014041242c0008180300184003101d0b81c049840d07a201c50240075100248000481c0303040c00d240c01c6a094070f001a10750b49082d2000d06126114a40102400032684800e40e80090364040500b0031040c0d01c0144d0b40000d101c840703000640d069114400006106490041000303070461910201c02c512166424880500300300d0704052401d220070a80401407902450340800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 280365827 1250 280364577 280364593
    0x40f0204021303030804110d12030c050d09050a02011403010b0a0c05030d110a1e05040302062b060314030909071d03030a08040506150a09020c150c1c0e150702 70
    0x14032452800d0743d001034010a000c5d00402003000002d000c0100e80f240140c903880c28410195070381501c3c1c0d1118000960915440308200050503100d401580d0100302180028080322010b1300b4030703507121103041000f6400140b210b4448075200a0f5241180e04a980070510b16161034a0254110784482200c0000c80d014081085101400e0803580250000540d400310601e55a031000c03035001d003442c1692034082c90500b1038841c04550180c0c010040c0e4007180d40660f2041d0740c40056162070b28416605148003902600c0300070220041d80311715809002600e00c03d003284014240c15400c09590303070140c40d02d5154881d002c40c0000785014812400f2504180002272040701001540c000281580c010051050025101c0402c0206110003004002e4018240c2500d0000407001000441c0700c00b410790040340c00040c0c0014983c404408200710054001c0f510319021402401d10820341c1040394403840c2ca80a1900310800d603c3c1194805126404401008200509114080c0ca00c1d19030ba03480010181800c1d4001e07610 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 280367077 1250 280365827 280365847
    0x20702120a0c0602150603061305011407030b010e1914120f060f01090b0306071805030601080c030c0910031221290114160c080f0601060314040f020402 67
    0x807444282d200d000655003641c203219000b032a150f80c052201031013178004030501c040d41d04c0125201e900500321002240f890146818418050a0740005c02d01d05c200000c020071041c0c6505610103c0700d600240d0b250203512140100708241681108401c0c4114100b4500801c5a0f1034800390f4001c3c04807001d05242c00380d0071155201401d044618030120840d800c8a820030040c1c801c40c0c00090301500410701c08100101989010035620800105100c080c406070748426200c00180b0381d02c07030780104002800c485180d070311000719948440c800130410380a4415100410041d14104245a100b41207041d8114100d9165403500c0e8404001040c0800600c00d035000034070510007186500703208802112002084a13900400d088248028000000c280046c3e0081545410303079005411481402648070b00c551143c0108245940c80c04190320001c2001c5100c140000e0001400b1902030b1030000200c0550345a680d80e814140d050b00c02007150420039448100000303002500c006c49600c0f855001810060420881c29 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 280368327 1250 280367077 280367083
    0x31005060304080901170c0d0908220504110c03030408130504060b120f062211160c2405030a140c04030b01080a030f0c0302210901080603070f060302070212 69
    0x1903415601c6180001c1d4622139540c00c1031113482c6801851248400a2500c00403031341050141e00c9170001e2081d1030b40040e00500c06004141c4907003002954206e91039181826a5601081c00da2040c58011810300520b400714a998030705648004407808041c40c55983d0f0783c0e50b140c005500c200104415500c0c1c41c0e4001c06c050302d461081d48081c01c4032080c6180d03244084d43c0310002c0c18500a26078450648050104181621109880000500300000b842842c2401d40700200140c101c80d0f085070205500850012086000540004403c07405400c008000e10b40300c0940c02003041b50442c0031208411f000c001c1440140c41080116480703501d2020020304480152914807000200307407180e80c0e402c48082810b1083c42040d402c914010030076540203201c0e9107000d580c06043c6211100c0102d0511094000010a0600074003038021704600c4c002c0e030384e000200c003540036607040d0b00461f103070724001080140081c0f01c5080002c0c143d016140c4458180108520b496001c8010f94004181281c000c01810406842c050b010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 280369577 1250 280368327 280368331
    0xf010c021e0109151d21070c0e040b040309141c030e100f020d020c1e120102030f070e06090d17071722030f061d030703020f07060c0c05060310050603 66
    0x413201080042c1c40c811003261010b01140181d9803034018200701c001e090011207411003018824011141c4907144c908042e8003e250b036511603801060503004200810480f1009240708a202c3c0d1100c0c0c1905031201c8125042400d0b03c002c4581000301210704d1501c07450b4000c0c161403035521a14003a41086021800304808020700d61421002c126071010b110440e54042c007000780e0098551005080490401c000a18540c80d60130405950b05020100001540c4540300840c01010b2600025562420912034554084104032030340c0380054250f800c10718091418108907000ca620082407800c0341410b03134852440700c1c8454100c0c1c00c810380041122000113022460100c1e51105000e081e2a2116250540c2d0b0350010414801614106003800c42400041c6a21300610f03511034200e0b20000e2010004a46100010798a0140391181e102c080b402000700f550010703a141d140b41030341d0240c452946e6180303004d0b5040c2440301002450045600030601550a11801641e408170f00101500e00056483c00410304660003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 280370827 1250 280369577 280369613
    0x1091202010507031401090c050c06040809040b01030e030a030509010617060103050d090803220e0123010f0c0b1003060903050309010c050a082d0108030405030f010c021e0109 77
    0x11500121111503020320465900091030f080c240f150550303022001401a505015021059544840b003c1100e0f100e07800b07840420380a0000c44d000303030034282407174459034000e254414811821306015016030b5110b80206514110100011814011620000d6014000c01004000c1c2d40d944c03240001440600403640000f040402d001600895042d42482400c0080b940c643ca010311450310420030481c1750001c1101e20b9111070300310a52032098410720014a41c021940000b180d0b031201c030004030b214440364202c0b0158580021054072964074600065401d1000741d075044000c41e1000d40c400c0702145c80d4582c00c07640b004c080b400746144241c0303969659003110f40854090300015408020844201800d01c070300b40c042041c13030a09509003c030010340104092030042040514444000e504500700348604401c0d26142c0300080c0a2109684559030320741e8a81144c400d4912034468201613041520040c418444085440c2e4050046440e061101110034a0b003030384130000350341d0780c2c2c021f07040403c1d0921b2000c940142 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 280372077 1250 280370827 280370843
    0xf0301180212010e060615090603071e021f111b010605090114030703030509040207050a111e03150702030c01060e0f010b030709090c05070b0a0902011107210f050109 73
    0x20300da0041c014140e800d403000045a03854100d150500f03000c0011503550000c070482d9003942c40c0c130958541c039880c2d02410303681c2d40d001790022081c401074640100307984030030103280545100c03040e8608038104c4e515203010b05510f00702103891030810849415a003001c0c80c0868682220b61415640280303a000c0d04110703000c42400381e55a00400d01c000e24081d26414014040c5c00c042404000d40310700041d40b100c02e180300007428480300140b101d01a484640680710420740000c1580d040d00070605080c951354914908803445034100c0d1800c5401004d1b003880b200d44076180030340140451016500481c80020000d45042c09601c424001c2e0407414001f4003500c000f0b0010284505440e081003514404a4081030300b041600c00c0040c420418a150f0005030300040311080703c00418500380c0c1007001d0b600d52080e800040c2003090032104000001c2c40b141c2000c3c0c4003600c00e82c2c4078403083e9078a00030603448012a0154101b01700342e4071100051243c00791100700e487d50140000c4590000c4e07681d00c60b42103810121f41129405 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 280373327 1250 280372077 280372121
    0x90513020c0d08070e01081b0714071707030803071709010b030709020a020c041e0623150d0c031815050702031602062d041503020403030c03030504020f0301 69
    0x11006001d88090b5864508001c5164100303040c1c06002000c006003203904011503400080d00180202c1d440210003040810504e640c1c00e4036003003903442c2d500080343c803007064400c111001800d26900840d25440300d103940f02814800d411599041d03404ea00180c2000c0400c0190b40b9007282029903004003d0041c4a95000040c203000104241070800105d588004040c0d0b10501140c5201c1d5004150641000c004940018810045401354125062107003d04c07000c040c544880441d8584c5481c0203c100c00c1811700341f403d0400400000c01400c9180800c0b42c4094038028403e00d0b5426402c2d41250748649014107001c01c43c003a03c0603a03079010340700c940e000751342c420800d580c585000740c0d00d032169640041c21071018600d0310040601d0f602450682d040000d0040a000070041207219504083c0c1d0400b01d01c1058402001202c844a402c00e84c2150080aa023002e4815050001074044c0c400c07503045950540300c0d00d424081c00c0c0c03000d9005080003807082e81c21a20b0301c9800c82c1196800c0c410350510f4034405442c91000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 280374577 1250 280373327 280373347
    0x6030106270308030609070c150605042004061103250201081803030615070204090506010602070609031a060103090f061d0703050717030c061e0c1c0c09051302 70
    0x107410140790307a04070820001c00500210303602c0c0741181d601070801c0e40c00c50700648580008480c2400003007000b400c042d5500c41c1400c03044459403c500100d90046909000c1d1329800031104011a444810000300524100700400215005005800b40c0640c017000b0b0702d0800540300d810122100803801c0b05408280144840c00c11980c11807045504803914055147c41403800540080e5244400b5142600c00d10a40940e011811415000ca418066015005224a0426182640d46c0c1d100c280180c00c0503004400e400311b0300c144039035014000c40e50040140e910350809482818103d50700505014101502c8049900c04220a035100031101846481c0014080d4170003070b01003c00302c400301c5841807190003490017040030a0000415505589008000464014154425510f144640319800c841409a82c0421207040c2595544400c41003d0072480c0c00c59071380b080c05440d40341c42070400409412540a50b00c0483c3c0c034096020003035085c80d03814408001c81e1034000245007070b0403140000f12419000640903400d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 280375827 1250 280374577 280374617
    0xa06030606080307050d2a0b04020a120b0105040c09050603090d0201060b0a02030409050a021309050403080c03070f0806060f0d0e1c0f0c050c09070c0c14030712060b06030106 77
    0x2c1000b18007031810a851981c0300c2c0d4a58a41d0506081003042200c203d4004403050401800c0da940780791011040c2a10b1840c01e24078124007114103038030031488070f24006015118102400380d91030f4044c1091005a09110412004182414102c3c080064035940803940d925800c00840c01540010003c0c0f412900103240242540c04c1d0381c00c5851f184000744001900c1c2a0000143c0742a5004100041095500c0003c9000240a0100f1100095058100008944401d0751089002e9406541c5082c00b559418909a408d03120036a072000010b000352140c88a80e62080340619080b0b080145020b10b02120300b440400d0640080394155600e41d5070749440094460104142986841c00102042010300203080c042c1424070790f4030703010050003424500ca5040001c1030000d1602c00b40020a509005d00b401a80240001c00260703048031445403e400205042652184084182500a0051243c0b506203083c01c40c0c0f81c61201021500640c942004d0410b0f9034074000914060901a516280441590407025603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 280377077 1250 280375827 280375829
    0x140c0c0d060b0a05010f09180905030708030f0c04050609101107140f0d1a07030b04020706020406111b010507033c051c0902030c31050c090409031103030a06030606 72
    0x2041c000440c0d1b15800300c58200350060b04941c000190303140e1100403a100300d0b01810342d1003802880c034000050701e0b00801200101640c06840091249000d40d41c4402c84102503105a01070030740d03c0081803001c5140303803030400489903058503145841c044030000c2460303039032070005a038111a80c070b01170311a11280c03a030603d00c03005e030140070044880d012441280d0300d8031a08200080760b080e02c12075103400081c4803d8065003024680c5603014100315640d603c5401e00c20003e4000d401000d0005807441844040703101b0003d540514901d52449a89a03003400b0001035489920000045050101408400a1041c01034a86c4901640f0903e440440b00f0350b4182d59240701e480d46031681043c0002440b030421071000d08007202148140b903000002c0d14450500009181650351954182d00803603c00e60800000151500950100703001003003e01042c200304551425103800b00d03129030a8003407d10a800841c58581c1000031000d0290034200c2100340001d00c00e41c296442100c00002ca181c980c00104104803940c41100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 280378327 1250 280377077 280377079
    0x240507064a0a1110022b090537051806010f021513081b0c100203070f0204020d0603080705010e06101203080a020408010606031407020c01140c0c0d060b0a05 69
    0x311901d0b6941e51402c0300d251685442e0390041c08040f50f00c5807194001c0020f18040358100516284028414070520520340002c030807480005d40c4400005003031b040c10904201c400307210058200e80183c1020110309135001425038000340d0100e4800006454a0701064816520000721480c030141c81c18000141c55001042c101c501198800320883c05003101200000b50003080152126884019a0a00700c0c04c0c0d0250507260f24050082d2804110103410001d8155180c14090350800c820030021a0140e0707c3e8000e008000d001c01c03400c41d084200510703103580203006030f00402c540022400d80b2516000c00b00c0d002900c04661681d51083c40000800b4100020b69000c50742040202d080d5040c100f0300e02d08035a04240003400c0c45a1100400d10783c031242e8041d640900b4443e00204005903071201c00401900c0b072020001d94102403100454200d5201040c018081d07103060311501000c141c000b05e11a80740e440140302031070034040c030503500e44103940e5103020315002c6d40680300c086281c0712140f042080c0625103900c21 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 280379577 1250 280378327 280378333
    0x60c050408121c23090706020d08093408061605031005030105100513060b3a09230d0f0309050a0b01240507064a 50
    0x10000090700240000880c072101c02c08075240c030320403040c240d0381548500301845600e061008030380000900e100070b2240320151080001582d116080c00c0c0e929400c4034010100141c0151042d03110660207009200d4101000d841110308500d8060740d61300c1d0b00c035218cd6451140c81255030002d00c10603510290340002d00380c5400a0406400e100403450121200194801c4c1440740110000c3e003810b080800080003081c01900a2015280900c9005c074510700700d008840c0700d542d84254894030f0300d81500c114025502e62444030351829120013800c0c017504100408001302902041d490035401c0a0500d140800b00d1035140d0041400183c2d890302c03081c030360008642030107251140c0407400b80720100000c07588142810b82c2007480320859030703142c220090074000c0d0f40541680b18032b00c80002005440c0a01c0b40c129141000841010803400701c4100e901040b41d050a80042c0c01801148080352180c0c3c4422002440f91003005541c803a010100c1002d01c00c0c0b01421700724030711955244200108014028100e0101a13005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 280380827 1250 280379577 280379579
    0x807230c0d08011a0d050a02130f05130207020a05060310172416080a060504050c09040e060103081e0405031c0e030c0112021e030c0406030b12031c180807060c0504 72
    0x130a41c058020162a60001501c80c00440c616442c250704454140e5140840c0b020751a86501c1600036610052140d1030103402c00500242d071441c1c1501c00e84038960b0b40104200c84c078510302820001681c0010700342d0600001040c20004003032060302d80b40b8580032151405440511703c0440c2c07101034500001c1e141a141700200f02000b1405900200b0b5046000240c2400c003059201c01902d00010a9141c0245070064580030911410041d81c10181c03c5090040302c06103e200e95084101d900ca003001e02c001800011b0602600f144080d5020719040c3c8040e0300c4030600d007826600c000082c5060380343c00d90032103051114800b50b8203441c1d1009040c0c0013480250001c1802e10306000009015402c140c500704121344d4003103145d100b140d09820361000542d442020b030a0305c0b070421201c0402954458030850300400d04d02708c5081081e0034021041081505500e0165041020002e09851540c500c1c680c4030402ca03035510a80074450f12100800304409004c0d01c80b49803256818540201101c03005c01d200010300006100c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 280382077 1250 280380827 280380869
    0x709031509080a0c0303020405060c010b1c03020601031410050f0901050903090d03030f0e0102121e012d030b0702030c06060d0f03180b041401030c0f0807230c0d0801 73
    0x80f168074280d0b0345080d0203011001e0030101c00a008503084540d0004c03001030301036040c10054105d1000440c0459166100010340b048d200c0b10b10841c104024003580220700104042079107070809090501d04541a03d02030300008166000300e690845841540303407010000e04c105841e00f445903aa01c44101802140b034103140e840015085943c205c1c2c000c2c2015104d4541580050550700700c607083c3e5010200035501c41190003a203121511040780d51a40201000024030000d800c14100c480c103c40c5414049030301d003c4d400c56460b0341c040500782d07014080180f11030004000f9840c0346800e84101380300c1d8091501c2d0140014003505028001e40385d940304003055101c4401007001811032141266140c105406031034400d11746082011002d91049a19280100340010f07440302c0070981c2d1452a400b43d8081028100c200016038110445582c0c0348000f45849002541d00d5024403101d01190525505c1114204480701c0d2500803a4082040c4001070340000414800d074035040383c90a4054610940d41000c0490441 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 280383327 1250 280382077 280382093
    0x40c090507030623220b130902010e040209030319031d120306040e0715051b032a0c030a06020a080f010e041704120c0501080105010c0503040902030606120709031509 73
    0x710503c03070319440070b415a100c50302680d005802c45d41410825422004001c000e0002104190050a4462200c0c59142c8244104080300d50705840c2c5280c4c1041c01428040250840c05c40142c041c80300300700740b100780c0400c0302c100c1c1880c22059401007058081d0100181450040105030702069100c0d181e2700b240c4080c800140d983c400000e80d4009540405000d004d0b1074440558020100c0c40c4206a010744029408002400080d0f01180304038481d000000065070b60b0320650401b048203020014070300e01b1915042c1803040a1240110440c0d14002c0030a00090038062080400c0300c8403680010300388945600050744a85c00350010407843ca1540c90641d01780d09000000340300030518210b00b490f81c40000c1541d41030341c0141803000d441101c009020328180c82d075040140182804039158000002d0a036200702d00c072000180d03001d405142050700d0044403901a40016000541c02002400b8100c50280048411441102030755902c144451850505441c5120822100405030307060403c3c40700031841c56 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 280384577 1250 280383327 280383359
    0x50a1e031101020304121209061b3e1806180717040308100902030903090d11040e0303070e010201150509060f031c18031e0c0509040c0905070306 64
    0x40c0d00c221071441e907900100d05600c0307140c200d56903048078507018505000042c2d00144510320540c03548000c640c1c80b43d8090307408000b81c80b419000c1c000100300b5078000801d11019000e02d40d962404880100e10f20031041074aa02c2e909000d418106050580c5003030130324000c4455190400c4002d0800010f040000104030044000c541100c9032002c0d0b100032814003841100741e01c00c00c003030319140c4034018101890020208076007999281101240c401020039000c29602c00c8902880116008501d00b051880600202d0a00004e0070390392010600c2844281e43c48902400a444003410007541d03507854180d0020302084c030307240003840c11689030040f6049910341c09404030b01910800c94005907180d030f078140045e1007858aa00120741501030000e40303508541030013102500341c0c1e06a490313080000c05001d01807001d001c403c1c40094003200a2103049a01c01d0308003c01c1030006401000c0c501380180d141c00c00b10f420b29805890444441e810103008226840d024442d05070403180616042c401c5602d0031080c81944011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 280385827 1250 280384577 280384583
    0x221030c0c070308070f151505042003090c1207062001020c100f0b030303040f0305160c06052a07090506011205040501140c0f0f070213020c07050a1e03 67
    0x50850802a070400c118001150700080c41035450342c2d145400c07070444480d01021610b036001d034040582000312174001c8083c2d4105981502076414a40010400500000341c0510140340003071012000b00e980100086100c1c840020040c071042e4280d1041c0180c0c20803118500341c2c0b5401c00807060056a42c00074a5000103042c02e1407042d0050b08501080cad0081c851940c410100d40308400780340c641228903402c01003400f102c0c000104404a00a0240740d1030b803008460003000390602c1042d500009010b8030103000003208403100300203030480940da1003541c00318503040000460740c0400c1c500c070410300405c008082c1c010b20442c008030900209510319034030030725406102c244a40b2a4001401d41e4420030305080401300b091001c6c0402e00301810028001c180c94040b5603124203071180081c4640031001d084614812040e6251450001d01c16205546508a85400c036805603006664040e050300d01c0c000361070210100409000035901d45000c0081011095001404030300349440c0014102d60f4101301d28040b80d030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 280387077 1250 280385827 280385851
    0x6070503070f36120b061c1401060f090204050f01030f0f141b030907090e150405010e0106170312100504151508242e022103 55
    0x10070b40415980040c90008000320b241169490150480405881c8422420750043e108612511041c01c000e0115144201910f081a9400030403c1400c1607120680c560300480d151103404040c0380d4508419580da80d600300c80c140c0d100c941c01c1c0600d02c58401c900d030040404450841c60316107480041a04a509029050b0515555810b400c0027080f0640007100d6090390000d040080e0942d00700003000004d410f8480d000d00c0c1105858603007940c410a0212030140040600911115140241d40406081c620800d55500e0054035102501c0a00415200e0b00484c41040042012040c0c40412801c442690388021208216001c110141241c0072044941e11840020034030364558034658445c85010b15980801c0e04945010716005440b10720082c01829103000d201d400c0310035100f124040301c00c044113541d8454400602e0001161600300c2840c801c190302c0c4041c00415090000140030340c01c8908800301c01440d1480c011600c6c3d070303055040c04002c9a180204c22030303900c400340701c03e1420810301006050b889040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 280388327 1250 280387077 280387097
    0xb030f130f0f06061503151d0f1306050c3001060311090a081606170703021b0105070e191a0703020f03030901090b0c0903101802030f0c120607050307 66
    0x10342180001d010942011895403140d648000c0040070705682441c1040ca201f0710225150400b5103489100b0709841002c1d0032580c9a800440e1000c0101425580003420004040400110580074003481035074155521515588070700303a4004491a6100b40020441a000380e640c0070000440c0041c2c15140b203850006110301082c02005424800d9240442d0300103104070000802e0740f0002400070f10303085008883c1300007565030042900d08001c1101030044100703c000019030240e102e07a000e081e0b0020742c1c0600c00c0d8007036a500780c0c0b0303421124203940483c00503042c40d44664141c01e15200e46041245410904146c0900d041e02c0015007000c0f00a04c50070b4020005010000d0510801c016030310300c4000c2c401c1e01d035a0704000301614000c29409000310b5103959041c002501c4401814140e80098070003601900a0041184e103140040c02e044007a41c41920741c3c20381d0304001d6213040008840c500142030003442c0b40b003012010080d000d121680100030507484103042100c81c9510000f6250403014a0070206445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 280389577 1250 280388327 280388333
    0x20d020a032f0d0f0c15020702010e041b0f0203090303092709030a1d0f09040314121f0302011b0201120c080a0605040606170c130b030f130f0f 63
    0x100c07146180040d01d5800340040b01000000118591540401030b48a20190302c00c403a500340c03a1124481c0000e4143c501a00c400c0b0031b21082034004200c0544140341c03d012002003a4005421030708415090544079901c091607065058025508030101e04082c0021400d0100540002c0d42ea880b42c900c10318000c511605055039284070001c001243c0000079001c5c030901d4030b00020007603541d030420582d1000140400e90b907007522501c040c0c1120086c15002e8010b0400d68081018040c161602800840800c4059410041030f441c10001a0004501e8142007192905003100114145613802031070380c2d030600351194100010b03a0800d2003030a540c0050544a8001d00040c00141c2e280626010074a00d224101440c4541d91031b4440c5c2114400c056141c0104800e035110700900086845e01d00458020508241e28011601c00800720503900000d1a10010304e050240d020b04401104580c2c400c58840b80084103210b84078249125003680036a640003982d10945a68a60075420300342e0950143c0662441d007003210034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 280390827 1250 280389577 280389617
    0x9060409021b120d061a030106110a051b15040e0612030f0403120f03090b060d05011b080f1305060703090503160c05010207060206010b071704030b010902090f01020d020a03 76
    0x254001c1c80d01600d81440da000191100c65100c00c220096280c98a580460318111030300d0403c1b51300c00ca14400605682c02d202003954141c805510304203c1e40701d0701c0e1070a00024010404124403c1780c1d010900300940c4140c0502c024420500d4111034503000c01d0000303000304540c0b4096280e102030304a40894510221030304845c154400c508080f54181d40c001804801c2c030822032121400c21b4031981c0d411220074448142102180c298190050004880c40c02084a0340b4058a412001c5402040001140c0300e0003c440c4036020020151100800d20600c1044410484c14500c90b502100c0ba00e8500070042040c0d50b604d45810004040d03d080c19503c500e0402070190810550350744180007103072004000f906080c00d84850f8040d1161030300510605c140822820301c0441c3c0340b4129807941030380c0303810608565034100c03041c410f07400d102c00022400d00000010480d00c2010600a0020080060ba0f074070310603061103400202c0e02401410340d032240140c000482e500083c00076801e50189010241c01061900881c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 280392077 1250 280390827 280390867
    0x3070807031b0c030b130b1b04090e06090c060a080115090306050907030209100302010e102703060c0306140114090307090506041401030308191401060201090213020906040902 77
    0x3000120440800400414010503003d5174004c030106091580c0b080f80c190340e0300005007802000f00c071710180801c0340000400d107051041c8000b1030707a1905003038440e04110b08682a607261601c0551001c010310440100900014148202c107031403961a100b080d9078041d01c010340600c248007800112407900390540e442025200d020f954007030700501c43d90412100707040e6504114001a40b060300008042030701c00420411003011668103071515406040e02408110140b18201910070620204e05500c0100d00d90661450380080c0180640780d02c041e046040800842d41e20304821814940782920a21288941004801d000c010920b4104000325404001c4562405803400d15a0144191040850400419009203104103019141081106000054800605000e20005c0c011440c2440071800506c0b43c1c0d8130030443c044232050041000c103400d102c541e000701d500f684504010303550f440c03800046180c4211086041c0114510a40c10801914001805442940b140300d03112580007404000d1026000300101c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 280393327 1250 280392077 280392107
    0x30803060a0b0a020a030e0604080d0e0d0b0403020f0c0301050c04090c11060709051815010c06061214011b0206060f1302040306060e0f0403211b050406030b04020c0307080703 77
    0x952038240b80f0002035620036001d40210040380030b201500d06141002c43c16a01211003900041c40c80c8048401c0c140d405421a50031150051a880d130b29a000c109040303011070089209234018042000510020340c200203070b40909034420307414102442110351400003910300341e401150000511074203000c4241d64203049440400014012031f010080d00340d4018022004a0b44259401000c4071822640003132520811555401640f00d410002041c80d48101c1c4001403240c420180003034820780b41c51441c00c180803d403000301c0346410079001036128040280200342c04100319410348040e8404c203e0000c0e40790a8010030032406404000824903030b1341da43c21038a01745611450b804660700c0741c80f810013001070045801a680e4808082000c181c0039507222640030701c11501a40e0305d818030780c41d83c2160314420514490003c9100c1d01c3d900c11590111060f1420b03207920180d0b4445075030344c03440c1070f6000c0c056560b400302d0540700350f105209290b0341d07240100840e01c00d2680310391007550f1880980350945000030010b01003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 280394577 1250 280393327 280393349
    0xd0203070303021b01050405090a05041e0807140a02150a0c0b0906090c01080903030a020f0403020909010c0e040614100302041e0810060b09040f061502150c0403050304030803060a 79
    0x41c141c001c00c0158100304030b074000341041e0580301300544e0b0740c5c412441000e0300308900c040092201811781e445190018441c6140c0b8105054a044101c1e419140c10710a0b981580d000030349408000f03502005464220030340010704101e24190300040c11100d80c90704505001e400014004030601c0c8502c100d040000d40c8459210308900304001d00319a10f04088480302c01da4420604066402d6005e2642c0320b200d0011500118515551041c049010b9000130741210401302c1c05002c0440180e0350401d04510450f080000001d207040b055078000e20041d0315503c4640103d16000b0f00b032080d41c0c3c0201001140d003a056400b010601c0920f04114024480ca80c01440c060000c069040c000b1605007410604440345802241e075580341000007441110018494030401c0201000700c1041e41c1025006040301004e02000019102d81d00d0925611102aa80300700005802816002c0194002490415000b03546000c0e03841c101410340d81d80a9880c4120300010300784a01c0440003030000d564060278000640192038030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 280395683 1106 280394577 280394579
    0xf010e0f031201150c0b0103030f170603100207050a02150304030906021209100c061a030f0d051b010605030a031d010e010e28080f061303090608060d020307 69
    0xc080074884001d0345d400102e80043c0c40c0314003d41c00303a165524002c1180a0007070803109a00c0d1401030a1080d5800d100b5143c0300046c810800404000300141c3d03400d03841c18a40d1a043d00441c00941c400c10060750904490b19031000745005a01c6600d88078046500da010a984502c00f0003000c800440d81486601c16624141491642240d1181070102c8441402d84900b0155001131410420500c04042101c2b003a0804019105100c0c4141d0301030075141c13100740b20040c25442001350740d17070011a214910301d844176401e5110b01c0003808020211400c003499494007422100800310300303010b01500040c1540d6294092110440b0001d0305070352b820f01017080030040090907040120f00030f4000340c800c1800c004600c095031800d400b4052580007462000c1e5040c15242c81e0550041580202096030100d0800203900070354000151840c0b820b00840d140e4031032003c600400e8510102961501c10008 = true := by decide +kernel

theorem cover : BRFrame.Cov 280215827 280395683 := by
  have h0 := BRFrame.cov_init 280215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 280215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 280215827 ≤ n) (h2 : n < 280395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
