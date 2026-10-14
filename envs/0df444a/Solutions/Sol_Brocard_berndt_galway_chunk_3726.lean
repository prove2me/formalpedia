-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3726
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:30:21.032831+00:00
-- url     : https://prove2.me/submissions/4e2818b1-94d4-4949-ab00-81125428d582

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669964028 ≤ n < 670143884 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669965278 1250 669964028 669964039
    0x606051e03280e1917030f070c0501060f03030522080601170f1c020f030a0801051e09150a14130e070918291911040305011505 56
    0x2d4810604800103100005120040324007000701c1c1e4600c2096000004141001c1046600e10300050080c070055018034441910603c40d403803e089401603032001140c0c0b240042995031480c40d1549801241c504500030300554080d543c8510200300c400b40c0d43c6102c402580030341c4c2c8440c0c82d0010880c60140d600401d00340f0b1007000d40300030001c100c0d94002280e001d04481c2d01030343c5250080f014015440c00c0c40c014004055030750250032402808465440505035643c0d05035401c950b01c000300c1f103940550728800c02800c10042480300b40104100d00d003003400c9540c600014180c2e0b001070421500406c0403154191400521180c00901d03922190074070344c0000000b0022000d043c07103d202c002020030704078620031111020940c3c84081d500d41102c000c02c8010020300700e2840070440165140e0304040060792090080358081111100d4040c0000c84540702461000401148640c0d5140c1c806412613044913040d1007042b00352079203142001640200050300085001c0d40001c1203001c050a00000d4107481c680180344100f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669966528 1250 669965278 669965281
    0x70818010512010b032707050f0a170a060c1727010216021005040506070f030e03030a020102040e0106090b18011412010f05010206041a0c090d060e160b0a05090a08010606051e03 78
    0x203400047c21138221041603465040b244608400700e1808005034010792104480503a074080c0b05440014801c100780d02507070013000341030a1140d007102d002c030100a4450394822007001003501492240810050220602402c4884102442d0a02d007aa0402c0000120240d01c500d501010f500340702c2c141842c0d602052400030315040c20240000c445019500001c1c007091a401265801c05004160130032000310002c0c1220740f03e90210b02c00901039401400342210103601e0300000500c841c09103160b030041d01c06812245003400030580c00d070b400c801c05080c809810400d9202c2040c8120002d079009001074455485c82202e25030410400c1c2e801d8010551020381194045003c01c8089004803528403400486010414205c0e240c01e00001070502901111581c8960f038011071340700700320a551044400d00055030550780a621a0144071003502c41c00d03c10100030304410440440083d20030300040500c41e400805101d5042d44548216084640e141c10040100e80c0010380003850f1a01d60450038040340c0f0740d802c0765285 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669967778 1250 669966528 669966601
    0x3160201050c070807140703050f0106050a030b0606070c0504050c1b03091c0f0204020a0807021506010207140103060b04030501330b460203070818010512010b03 71
    0x250700c52003d014102e060013040e5102040000c5080e142d22100b24011100140d4580c28903e80350380780c894031030b045980b03082e400007502c0c10144038580c1129086501402503603202000c0c44401d60013420210740c42d401e250b0011400b80e80c0d03403281c030380a01542802a03849000013114a1002540c1c03e42c815001e07030007486071604680d51006c01c0352102c03818005c3e0004c0011141351900030b416a40b42c00942c006d0011921a10032540400c001d8803c42088e42120703608c0400b80e4668041420565816005801c101c0e400d0220561b0052064a0040103240004000d561030828800300c0d0015001150141d450f106401840d055175407682e4a08840202400300050700030409410500051080b0038418030041009031a0a88000c04030325109404020400442d00d070007007120300f070307980a00d481e6600030f0701e080c2d030400c040d01c00400c0d10070180d030200c81d062501d10030714440441c00440314102130400804202149170310b48401d1041f8002c14901e0a203546a0910b0110386c11700e00040075002000107890554140d9 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669969028 1250 669967778 669967801
    0x30d09080f061006030209031c2a02090a020c250317030705070b04020a210501061a12131b06020c06090303070609080906040305030d1512080a02070306050a020316020105 75
    0x13140e51500740181d032031010350082410010b0301c804888002848003004e0500941001840f90480c803e4503468a103051000c0c5264000b041c00100a5008030340d0f04001030502446600404020303400b60200c5072045410f40b015014401c4401c0060481100d10100300104045164a4000307000401400c604620304210014038a0082103400703020811b246020031300355102c40000d03001525001003030b82c0c060740c20301d81000603a080301c0204850642c60100001492070350920090041c03280d42240300c4c90002d560182443c4410050000d190300748580c07051a0010340c20000f080c40031100451090004d5203002406030606805403500d60040b05c04112002c21640c01004582e4102d41c02100040c1c1c5200a040c44403441c00703a8107000d44c016200150201c1404400800750105584050701400319444040005010355098031a40c1c1c485400070f440a400a0b01d509c010300002b407010710459404a5803a114441074400a48501d20302c981d001003404041c1c0812407034080b96011a0009011606091a8241 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669970278 1250 669969028 669969061
    0x301050f06030d0f030209150a090b0307050d0e010605120d081f0314010608011802030709060b07031d0d030905030d0f1e0c020306010f440a02030d09080f06 69
    0xf8100400c049044242c240a54107030b40e641e410141c00c500b008003000c3c02c0d00000e80c1c02040c280012a004020008110f881d040c22a445507015036240c4d410b0160803000b00010304000a404503040d500d401d008038494403880303581480c3d451840e0003003034440c0144d21f0140021801502c6280c841c8180b04043e0124040d581007042120f0b848800c01ca02403d01c0d90180c0e0041c015030304a092103500b045141e1002171103441e17032004801e00031015100034030742d01c00016080f43c01ea4416022107a1003803160301c010070b0040c410004500c1030300e10742c0c84101481c10002090b05030300c000100c010854054040c45942801c02c4a8040e02d006030078104800c00010750050300c1914082c0381c8002c200701010f042c9070b1a40c8a0080320321083c0d03015044a40c030f075846030f030380240e00c044a016031034420380100c200c082d45c140c500082441a025034480000102e00400b59083e6001511143c00c00301c0c86201c1e103510068404001c2caa85103061035544602403420003015034101040700c011a00d542d40700c82c0038841359142d20300110 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669971528 1250 669970278 669970303
    0x10603050309012a1b060206060a0302010e21010213090203040228091104050102210301140418230a03080f0a060806010f051504060e21030a0203090301050f0603 71
    0x6440e00a42030040d00300f40e100110b00b59191300b201c0740750420083c16910f030100c40f05403034041990369a2145400c0b40d44080c111109035100341101c0080015500a8100d20803609010341441411507551442401d02d0482d071500600036940024100c00d0f400b1640f43d031308080e082c015025495820301d030300000c510640340d1081c92112031001100c40c02d02c14500c40c090008000b018401d102500040b034445c245c80d00f003031203120b000d40a61507040070b02c0384090160554102286c501c10b415a402c02204040501d900440700760080c0d034804c141e040104415907034a080c548292080c250001c0c10a03185075480b01c40c44017140c02d40d444101e0036800290403a4446a0041341710129040c1a660700c00110003800869100040740e00403600040b40190006909209640058441d4821b642080c0620041841584a80000184d0010605080c2c0c034201c218000184901100c4c14184544000c2650440d400b001481c409a0300000d030b094801d04081c000c007544040f006948140c2480c003075000c280c41d9140a040c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669972778 1250 669971528 669971537
    0x15020a030212090603062e03021315021519020c0604020f190e1f0e0702330603011d10060503010e0606012a0b01060305090105190e190b011701060305030901 69
    0xa03071401e84d19a1500080041a460303900424540014008ad401115800d403822465003002c5525900f1061109034498545d0081903102c018401140007071a0180ca2403c21540354078180305000002e00244c051610040c024125506292042160300c00c1030340000c5000d14031401c6202d0034010b000c01342c6001c40e05070084480c2c0300c1d035a00320303110401d03840c82032144114008801c001c5100c9000810b5540304500c0d540031201c0305803c1010890100402180304094038424042d018242001100d6084c1c002c0000740011a0342204140e0b0601c04103040320b046481c030381c0300d00d200b14244249805400002c040640c002c00c86603685075202501c0303400080225043c01700395086080e0301d24014440015500350790a00003013a210500d842c4912440a104490009040101082a5140c10b202d05401010400d100c202d92004010502c0007500c01c00b40d80d0030180c022101e0300840300d0100004201003d00c075510180c10381d0304000341d80c4241007c0c040000c50390f83c540142400020f40000440791611f0003400c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669974028 1250 669972778 669972799
    0x5030a0b01210c0e063405190201050c100b040617030306010e010504090e06041112062a12040525030201210c020c0f030115030602030403050415020a03021209060306 73
    0xb05a9403444022003440d0004030000b55000200348018080e10b0f0100c034256941d4100345407200e07074401105890310280c016000500d855080355602d4103a262070270300c103040481c24040340500e01404e2519000b4245912a180c0d2580d103407a00e41880758001901e6074079030f00d040c1e0b5000c4941e020307580c0c01300401c010b06003c002603903c8002da02840c00d8038001d2080e001d09002e154a003c0305251108016602212440c82c9000c80105900e00814008002d11182e0010400c03030380d41e130000c483c403d25600808840403c0380c1d02d00c080c1041c0c203600200010300c82c9414690040c1010715202c5c2c50100d91070710000002c110559070003c00400e544120f0708513602440c10340015035494031000321941d609489a42c13410314202d144000c070ba8002c56106180c0c0400c5070505907049501d0280341c04d89807811303851501820400c2050000800a40c0510340180c01ba10b0200c0c01c0640b500d10070022010940e02540160344070f0012134007015810011702d13a00800d40d0300325030304101084001c94464000500242d2143e100b001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669975278 1250 669974028 669974051
    0x1d0307060216020607030c0b070519210e01140921030601031d2109010e010309050a02040509060f091204270f0f05130302190f0b01030305030a0b0121 66
    0x3042e9400071a00108255910512450040e02c0d0004005044030502d05103000507803801d02070f0041d80c0000680101c00f044207035203a00101d411805480b1103101e02c2481101c20910300c14144503101c40706e0764038000010014000741c628010907500515503561a0300c400c0f100c0f480f040e241c40004071400c0ea009440c640701d80310320700143c014050745400d03041c100180f0034032440f80d04400200d5400341c103a20108058212162000007201d40b16040310745010560740081c24103903510030351005003190b020302c05039102c2c0001350b4009401d891082d03403c003103640d04c030701e0a108840d00c0c0c84400310f403c150010010300d415400700107800b8080c0998420b00c0041400081082c03c01caa00b6108562000605002006030121440350381004200d030000c0c0910040c5440c00250345031100c050002500c58140d001001302c841c912a90130842c503d080800c5818030031b20388581000400054482d8003952003602c03403646900d0035680c024106c0301415a00d60402c00e100c030020f01d0304e05200400740c0c50f16960080c0401c4411244 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669976528 1250 669975278 669975307
    0xf0207080d080121030912170403030c140c0f090415061806060914040b060d110a03140402010c08031f09090c05030304030b0606090117090c03011d03070602 69
    0x1580190060300900c030540381542da11400706416114013400803034054002d0303550380c0300303070304484000401240a014050044841000a0b80001482940e8040d0994901c61082080da0801c0d442200410140c4207a0030402070003605041c41e400c0140c00504017046148001100d1250506030b05000b0300812000c071303080c4113242041c11840440060700f0700c0352560b20071403a4800d6210b8604442c15615020010071954400e6144000301c6846181c2c0e641030321507039000c201c001c125803205641c0c4100100b103a19a65211800f903200c0307010401440a0b11002000c41c0070302960444903080490303074000d40401006030303041a03d10240ca50440d05103a126a102a041644ca01c401c20400c00340007041c10002030304201c1d50300504031032842195044101d607558400e1550b00d009600005240078004800251a42044006415103440514001d40911111a450400d0020030b0380d41480703a80040100c05003c0c1000d0144203920681c00c034046c01c641c51981d003043e889001d41600180a103030001450b102050b0b40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669977778 1250 669976528 669976543
    0x7050f0f030a0e011401081c02120c0c0d0b0720030a110106080a05070510020303010807060e032d1b01050a0c060b150301081501050a0302100207090e01020903100b010c030f02 77
    0x8203c02041040012103409054070000d04c5000050712580790140b201c08140c83d22285424007580050a083e030110300042d445401c50b043d112a40c2c030403519201283da42e01d14080c203826010b400c0c90407403414540401000100d0445485503c400c40d1000306500d0407000003115229001854039002d600304100d030a5024103207552011849205004113801409004502e1500300c0d50129a1004400104401680c03030f804240702e080308030b40001404110882c05400d003102c3c5000d008041d150110315890303056001c002510f0498640c407180421484908c03504020b106c94908022a100003483e5446000134010f21500300342e84204420360031a07004101c41e68001e8801464001d00c00c510b2958a61141c1402d03400c24405c4410034412558007081040060302c00e80c0c1a901d000e4880103525041da0240306101000c820080214480c0e03a10002d00300d1090301c40c49801e0b020442c005030340c420160301010301d866903c501c500066840c11080159583e0000b0310700c55203941c9030a08107105003d000c01a03051400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669979028 1250 669977778 669977801
    0xc0b07110616030f060515070c0e01060c021c170c07030602030106020d020d0305010e040807081c020c010b011b06092405180c090106050313080708030f07050f0f030a 73
    0x2000d0502c1881140c4900456480030b0395502000760380b81c1d401000d000c0c4ea5a602c200e40d008034403081480b502d035407050300510200e8042d031083c0302182d9841441840c610002d0380a040000d01e5a070004086150a0b52064500d44146207002c03e188184d03103407410145031404881c030070020005562400554144000d00c010f58010104540769a03544002a4651074119255801400303001504074490307010380304582c16a20345000c0c564040d5503e60313481500d41c1c048002519580818498043d580748c3e40c540c0c240740c0011400026880e0401c440186080d909405181418030000348a15000b040c0303825200ca0000d0340000d408145d18030b45003080c0c0e02c100c4041124a01260001c0c03c0c0d0301d1840303401d41000d401010903808618100c203035040344986420780100603035807003090320004101aa11031070142d0b0b04039504041c1c10140b01c0d110340e5142c0070759000e14405c031120f840c04000c1011129448152507808041420414903040310003045d5102d901c500c0c180184141300c04408119280f0090740076041041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669980278 1250 669979028 669979033
    0x2010e0303041b2c040303020403020d1209060e130902010c020a17070e010b12151314060303040f0b07060b06030108010b030f010b012c151b0d0c0b0711 67
    0x1824180005030801c9841c0d0000c4084000d1800542e0480b07500c3c0c2500800303011285810b400700404040d07134022102400c1603007050f80a02001c00175a4812510404652107008200c10b1101c0005020342100034981c0004184500600319a0680c0c0302d1481d0410282110309002501060510060700c001c062058065008510302d003001c20a02c010702c0d12005541c414600b100c1d05690340f40503088090100340201c80d0500c0003403002d0000001d00c484000d4021110210f902600c0b80340300702103620f800c01d0382018016682c40b02c20245081002283c01d82d0450380a07005145001c1c100040b05c1d002e03c20510803081200e00000d0810140312045d4403141001c0700c01040303140d030ba5945410650281c01c007002114828092118000300c080170521550004c100c040c0c544001100c4550820b1440944101c030300140c5144002d04202582c0d10f6105c0b0044803040c292440c2d40391f580c4146050070203004681c403640c8550051000c0c1298a412015a44d10103a0000a1614903030799407904440704038600300c640ca02031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669981528 1250 669980278 669980281
    0x4020d12020a030201060b04032f031902041d03091302090301020a0f020d0804030813050c131407020f0307110316060801061404180504210807080105040e1b0102010e0303 75
    0xc0d03501040c1040054000e500074081152510b4000e2583c1c03041d440010031041050808152481d001d441d0341c858800c5001c50f02250001000200742020b0700c0c0c900b5880000045118501180b0f00340c0b09402501070400800c038007a144100300175030b50b4401c80c1d01c0c0c58881c01108650200100d0306030100c13800f6141c094000e41d00d55140c4940a403d098480c10084098002d0208150a192240542d24402e81d01942c0f400c0c09074441d10403d038403801199409681c54020a0b8201c2216251818110140c071418040040c070149d01e84031000311081e01a0984003150004040e100921000005445003582c0007000102000e0709180040c1c50b0140c02c21854000c448020400244a500848000c1c100d440315164500b26140c2c0001402140c444c2d4000d003410714107107810360f410541083d441144d12134840e101140c200d2070343c1d0452111006a800899002625403810820301d240c1c000016401450700380c80a1000c0401c1042d0662202c00400c0d00e141c038050a1500c100030783c1e03c00d40106010045032400c0d03950700e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669982778 1250 669981528 669981563
    0x5010c05090406091a0f0f150403050c22180f031d0411040e0903070b0a020307090e04030f0315120c05030105011a070b04150e0d18150804020d 63
    0x240c01c1448050b201e1440c20783c001940151a001e1015008550b0807401110302c160b00800146c448050100c0b034024031040043c039441d45401200488280340c0c240040d442d54a1490242c2c07030030000700f040601605d01e040d089841280303810100c40e40112820340100d00900e50034804080241d540b4005000048000751000600d504504c00c4032052041c02607100c40302c1c80d40d40038003043e0380110982214601e000c0008000c2000d520711419000860344090740e20340341c0d054803000308140e800e0380d03004403007035000062224198000111100901240c40e09040078940b80d1006007813510315031490410b040e19902000e03c17040b90203603000c4c060a80d8154a94401140381408888900607000d5580a036180500108041800b24141c29584007123510881ca403100303a03074038402444d4002d4000c0301d0441300009041020480c50290a0034104000010180641c131448010100d1701c06041c00c8031462201d1105000503006030190703141083c0581440001a1540d20200711382c03004a4401031308415080c60301408 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669984028 1250 669982778 669982787
    0xd0209010305150a0513020c030301030c0f050102012c0a1407080606120601180e070306050411010309170a11010204140a0b12010e060303091206180a0b0c0309030705010c 75
    0x410080a907400c110a54038642e0386003c0800340f02d40303554480500c0904000c103140000c9500c071003540c1c5031400340c244046044c0ca107280d60000c0c2c10480312480d540e84107015400c82e0b0a1124000c1209100034456031000006021a0305d01c1041f100150319454810041c0c0118100b041402d81e0758445001c242d40f64080c1c0103a07454108030f00407003809001e40000709405189c07203110490754074007407006410039901e06030580c00d408142885211003182c880d0704400400c00284511001540549000709040c0390500d000d49202d1704d2114140d051624181c00701e00031070401e0048140c030421607040700e603490805420a503200a924900d6410960001a02083c0c00200c007013104540c550a03903081c02c90540b83c4035049241d0081720355046144083c0001080000c0145141f15001384001d42503038500510f06003c07407011a00c1075a008040c3e03114400307210a4840c051044841080c0c1c0c5c0024214030700250781d55200c50304000c0d01c01540382c4408004501050414411100156031240c001c20502030170320700180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669985278 1250 669984028 669984037
    0x6070b0a1506030b100f020703080403060c300209010c0204051006030b03060903091005040806100f0f140402030703060509040c0e0a052e080114040606050f0306011206110d02 77
    0x59010301c010380c0010524064000c3e15100038004002c440c8518032010102c40e405410030300c1e501107200e41c400020100d44010000c0c00998040e82c008202002c071b810b40503041814168040480d500d09200400318000c10807007290358540a407402680d115101e200407100c418a5907000b95020f03207031105015032650400c02550840300340341c07028411180c10204054681604070f4040301950020446107081c1d00e0702c2c0e040284802c0490401134202901e4800d6903107044000ca80b40c0f00480284241448008200c1078404020010411181c00c1d190034114454080300c95a00005d0003640c002c0085403409019800c11005070001800304102890300b400d000002c07155522540601441181c0400c4190241d03006461007403201c0040002401c40e107101301c002c0004180b041c00303801d03803200f4000304040f0700078041d8240c501c00c0440c0c440654100703420240d08407130344c9500c040e00c105400300350000d00d43c8001c1105030448501c84150f1044e100307182002000b40c079002402c0d81c0e900724000380b2494002042d9002c2e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669986528 1250 669985278 669985301
    0x1200706021506030111030c070213020a030213050a0f061d031c0e06070b06010c1b06020f0f010911011101110406030c300e030409050c03040b071404060e06070b0a 72
    0x50b04552508402e140c22502508a28088454100b0000b0703242c07000f40b401030064038070150031600800100c01c0004101d0b0840807080000070780000e010003198164120210180408480c1e5030480c40c039125803584140d24034403d01041c0711041681550300100100c03c0c80e5420300160070b442ea071000e101008280005d4001180b0080344400e212030145040031804d80c2c1160b54400c50030f07002501c4510040d900b5141e19102103c0c1005030041c3c6034074402300702124000814441d0020172504811080c0d0508090546c1c43c42c2206a1500b007c50010952403d00004a5078080c01c1ca030a4140d0035603096409050180c80760100620000350010382180d1681c081880c500044d40c0301c0350100750003031000d9400540b2034181c0440a021000e101d4003074a1a0340a900d80c00f450004032850166078940c001c05544080f00e5200400c0000300410061010491416600408910b003042c0a82c0766100001c500340104c0c0100010468169054103031a2102d0b4126026250048404000751510380c0c01e00c0040e24001708075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669987778 1250 669986528 669986563
    0x308070206040c06080919051e0307080a11190c2c070302090409050f070305190b070804020103020c010510090e07060e19120b040b0708040b060120070602 68
    0x24401a1001c9007450045911070b0600303120380d290602c01c5030064006843e0304542d0081ba001c0d004c8800706046950f00142c0312380c01820aa429948441d800440e140c0351081140d0400c2007200002007c60302210881e120341c4c1000c042080e0000540751408491820b003102146413170303c2ca0030521940408000850b0800c2182002400250701031104800704842e81600e00e84440c008904103500036005443c05480141c4009140011034480c41e2601c03a07014001015134120120500c1442414000c0d40d901ca00d02200f1503103041141e03070f2213031000c601c01840c0c40100941540401c0843e0721940440b446007031404001e00140c02c0c2900b006000704070034403a500d256807605c11310a00514011850000306d030b0840d01d81c1d483d80988082401424441c030381e103070070780c81e4803c800c040303080500e25540101141c054640c1003110700c3c0500c0d291061100180061091201d240704000014412418082e4004ca080c07800340030a030304109426440d00303180c0d440203515000381d0001044842d4005405c12040959116 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669989028 1250 669987778 669987781
    0x50d110d050c03030415110a03050a1d19020102123c09040b130e0604150203101203020a05071e0f0503034504050603070e071b051005040308 62
    0x409031450b01ca010248003468109000003004941038120780f15800300b070b03140d0219450215284004440d4031080191000c6a500e400b401580450b43c8500070500480c250071040a01c01c482007107503541646004041c04030742010411045902c24000d0080219446544030744619110142d0416013080c60018001c485416201ca010300e40d1904501c0c040703545020010740b0707240501c0180b01c043c000542d4096001000840301613030340d401c54807070507060803680c00c082c0805080c40e141100900e00000c9004400600500501c00c1d4001d03504501412550a0b46080d003040080d0700d800d0b42007407800d03c809007460140886c00102500c4004c1610382e030107050000e104c1c50540b13410780009124040d018180e01540113000b1201c004a040c50300818107160040d040309204c0d45a40810410300c0110003c032440c0040359001040380c1007070b015941c1c0182084000e44503242c1000c070000d80c0b22100130010410801c0e801e140c4991801111010754403650004103070360040340600f80c505c000e81403d913001c8002604000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669990278 1250 669989028 669989053
    0x2120c040303020d020a030801050d080705120a080a090222180605091e1203090708060702030409140603120f09060f18012d1e11070501030c0909050a0603050d11 71
    0x880030400c40c1d050b01d8041852b400c100500c80c41c1703501900b044504400410044000c90020007014140c1c05010214940e10450400001c1050401418460030740b8140711001c00180e03145d400da51000340034a44017801c82203101c550113014080032039100c108501d02140c50301c103120302d6030040391048100004a582603450b0350501003441144908035040b0742c00014594060b0420540110b801c0380740c050440d2000c0391600150743c02d00000b43c5240026038000201002074980500070180d155284c070f182520249028000300b9101d40302c04800b134a403800000340c01c000d003868000640b100801c0142010303890740d091100c6040194400c802003d98440c6a44260380550720076802e00f0035904c8a00c0071a2040e038802d0f00c071081e10503050590002480007821400f00c0040413860700d40351030000742e03451032060040c01e92054203280c01600401e0416007006048042584c2001f071001c00c580b1694400150359a0310003100f001004190001080c40c0510341403640e80540c854612041c1c0e044000907900a400602c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669991528 1250 669990278 669990283
    0xd06060f051804081b06070206070e150d091e05070504060b0316050906070209040f030f050a1422030b160f08040609241d1207080c0102120c040303020d02 68
    0xa072070104040d0600003d00107800703400580130104907080001704040d105009203090a1080b941e0b1001a40135504200b040ca82c003401d4040c0ba940290f4080550f081381070b8a8000300e00c03a0340042441a500c403001d28040012654078190034070b8040166031441401403070225202c050340c0c840e9030b118a080001c0420340c0b201e25421a8003030315101159100440000c00700b9143d0340c2101d81070580c002c0c0f00b441074102585444101d20b1243d0b115210030040040d03185001b40c07039111040d440d1410030009114651101c3c0d0400c225038031821382c0c102096110065a220090001c07444d014411701c00890724000410170420f210708901584003004180c000455035241210a0720800b050300c400503403e0404900071a45079400904450b000719610404111800c0303011840310104035421030700c155583e600341d85020001c0100c0c814400210080d0082d50880c0303102480354001c0c00005041e00e50005030200c10041c0c01d504507401007001c402c1d0f600507440c2c81c258240d00c0d0740042c8403c0e000742c050101c0d45903465101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669992778 1250 669991528 669991549
    0xf020f0d0c030c030306051503060423010b09041e0516110a0209090a06050c030603010b0103140103081309061e0905040201090e151801030c0608010825050d06060f05 73
    0x35a90748421654450b1021666403ca0f1a0140e00b071580d41c000202d50703038079170b010180d40c100a8500342036640d080c29002e000480700b0300740342400041038401600e484030103041001411114880d980503111001e040004000f4032500c18a048210303016840c041071305006810491140c020b010f2041010151140b080d101c00840c901d100e02d90f41c001110b145c00618150840300d40040c0d85c403084609231282d590700d6808582d419180c0d541040030100030001d03a45000d00070700f20002000c2c03a0a125101d20903105400c00c26040c00002c0603070301e008c42c0c0c244100d1284880c1d08001e05101c0011f0101e25034480580500b000008015024051494000300744c0840900543d40a190f06179121080a03107021114002c00e00007620551525100c0d03c2c1d594079035500c203401d114000711202618403e0754910700d800c0b80e003d0703078960242d02440102401000784a0300400c1803944102444c0707030300c828615150301d01c180000080d004243e024072450440c005002c007940c0503030280c50803000c0b40c0c040030707407202c04108045d10f9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669994028 1250 669992778 669992803
    0xb011a070c09050406020f0c0601260a060c0e1504091512150b0d21020f0a0308060a030b07020105041a15010e06070204020313060c0c020609011116060f020f 69
    0x4091000304107000d1143e01955001c0e00070800107040c4102c0500c8024664450801d00b0312603402440180f162900d11300f8800c0f0304102c40070140c4440074414541a4581c2d40c02840540110b41d1448003a081364003c0d01080490500200240520b000c00c02c5c00c000180c005000d601083c600e8095450423000d40106880c05480c040302039031440741d505644140d42e014007088040c540b43d8a030079006e07050352141d007503211000d80f01e000c40402685c0c0800e240107003100704404039011036020045500d09a80089251442d564040c90b0a010f1695104045100c061650f03000601a171510010001c07441c0e41903200c00d00441c8156103c151204a20180c61094401a50704100c0e170740422400c08580d41c0100c24000700703410058110350902456800250490300226641c5c5080c0440f201d08000300000c6124103ea92011814a02020b01980e00031078240d02136105100c0c1840740802d000c0c500d1100c200114107201d07090803d05a625901d03010020200795036145450094400c0e0840740400f06000b1035000c08081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669995278 1250 669994028 669994043
    0x20c0405060d0809010c32010606080712060810050a05420907020a030f05040f0e040201030212070e0a0e16031104030519411006030b011a07 62
    0xc2c400d4490740000d5000d81c2a03c0c4c14042510850340c0010b400310100100503099851448044007110042013854000040d45421a4940442071140a800602c4c2c1034001c3e2031480d05d0941c091341518954010081038000362510312078844010260740154000300d2190022410500c41601c034144050455292903100300b02c0c1140c06110b0300005580480824900d00e4049250702d1902000e2000c61b02c2d80c0790580300b107001138110140c42c40c14507400034007006440c43c20707103407152034140f401c40b00c0c40b81090702e40180d080c1d01d60b864001c1015a88660141d032000300180700ca46d0f410703060111010b400f840c58400700b140290b104800000d0242c104108492103003407021000b0080c209086001c50080000120007082480103201c040041355080085098401c00c1140d0010000000d0400c29842031450021300c038020300050b1149002c2e10520907140c045070007039104002c02010380492a0074120560504200301d0300e010800800d004581c904a81200d002150940c0d041842c00b450308500e100f8440c01034501c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669996528 1250 669995278 669995299
    0x1140c0a0b060d1403041e06090605090604081902150703021b0a080a0303021e091806032113120f120c021e040b120d0c060f06080d020c040506 63
    0x641c8451140d900020003420f107001802181e40b80e80b180618035010411642c400f08081c05160100d41021402c600b1403900310a030185441d000400001f414001c410401801050100007a15400300340c070302500081055070a100c58000d000d900c4000340d84000c2c2e108000d4400c03042c9118000300203c410075034040c1e0160000c82c2202c00310000b18801c490301d654014038210800500200306001d0100d0703e81c03107070390056528501c606901184d100c4c66800304600300001c10000446542e80e4401070380754040510707070784583c0da40c1d100000c1c1490740d280780041c05044d44040703025500900328000e148032420035010004058444500b81d81d00c0440d0400104424030800502000c121500b0411410034080c1c038090124220301d070b000c41c296481001040c4001c495006119800b8941400b03080c2c10054207848080050442200e165600c2a03090303c500280580080e4001c103001c110f170070824400c1648001801601d55840c403150313451401300000c1005000b8005150300500e003600409005d4007000300710102c130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669997778 1250 669996528 669996533
    0x130f080c0103110f07140a0b0f0709080601140405100902030a020703140a14180301020d0f05090a0c140d05030a0e011b0c031403130608011403060912030c1c090201140c0a 75
    0x20000303102c00500b894032500c1041c5002500703941d060b034411521400327160205d080040c4043c1081d00b140d04040f0031030b042040140b1104203c0d10b100d0503006811100885c107621000800c80c86005c031a001a11854000020072040f020740340c00400d1014031a40e00d070501c01000d02c1c10910940691a8240c001078040761007924a214020003070241d451190180c4040318a40301300217422a4800840c9103092600e4404003209400f1901c94198080c079901b005e40b09071059640d50419880640c0100d207007146100d210030788103444502c1d03208030060388041240da44080305a4043c2c00d49078400803850000b10342d4280e40444030381c88900c0342c1250742d211030644290b60075030399520003a502c4900c44014501c41400030242da50300c4025004010451603c03070035003d50504c2e400111a50011210b507000703a07c01c1c01807200b0081d0018003514072426403140651241c41e046101e00c524032414141c00c180c02c0c0b2081144900d82c1260f4040c01c8034a2007601c514145a42c540c621112501a400c1924070982100c2403140c007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669999028 1250 669997778 669997793
    0x30901200109210203090f13060509010902030a150303050706020a12151703120a05040206090909070503010b0f090a110c161a120408130f080c0103110f07 68
    0x151441032030101060288555608445900074251000d028241040c028000c0c0701450343d0440640d48003440c80d000d403c0020422546010000c0713400341d100001050700c0a9696070000d4050074000f800c003000395a6400f6501c01a40083d94100d81c2246400110000a04030501075012a41e0580b146400c0050b00c0c0c4544009401588002060155002c1c000211042c14402c0e49881c4442c1440903d1281c10918221807000400f01d10130368a80c000c000503903c0c0d80e0420b810036441020f07140c01068035610b40c40420f826000700c0d288960004000000e2003012400424001c0c180c403c258000c008030b842c00400c0041b0f4511501d43c1581044010000c19240c80998201501120350840503a240c10072540c43e980c0382c4603101920000407061094203128074044294005c8204c582038050f64107007682d000c451401d070711001d04010f01569000604507040c00709580c4820050003002090f812182d50361140a80700d00e06c1815190002c2d1621100c1100442060280e071500050601800e08040d80b9540c1c408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 670000278 1250 669999028 669999047
    0x70302030c0f030c070b10050d24090c0e071e030c03090c0b0403020901050a0b03010b0a020a080703030626071203020f0706170f0615071a010f0807090608030901 71
    0x2005034003007042c02c000e1203014004500440c0311412195440030541402810000d01401c1004807404000c0c08018981e00c01050038030494210031000030100071040c1840403a1020f841621500f4104035001d001d100b00600d941085846a840090981d62201d5040321582c001100d41c079221000e0f00402500544283d00c8192600594240001c1c400c205895586031400c043c0e21008000c0c4000509004609051f800301d4010801560b01181070780c20000c1e010580e010500402c81380200124882034058420000c12203010f4124944540c0c8103100c0c02c000380a4182ca0007940902c1aa000e0b0070500401c11803c040c541d0200c074405003000504100008806140f01041a401c500c1050103100b1007410070b00800340100260389503032815100c0c010850740d1040e40285030000c0515014200081c0b41c83d41c2c07030300a4841c0c2543e286c07180d81d0000e070710300104040c40405400002d01c00401c00450748114640340241076840b078004540700d0316135400c00034041d0b405034060a01c064005001051243d4000c2c001d80 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 670001528 1250 670000278 670000291
    0x605060118081014090a0f051609021305060304050a060b030c091005030111040e0c0a050708070f1b060c0221030f03061305070c20030f010b130e0607030203 69
    0x3100744180240841101c000c80c1c00c2040c00b5000b01c4240e07289002a4402c140c0300c5211003114083d60301e040d01480b40c82d0001c0d1800138201c2d00402d0b80f10b2040280038030142c0d80c40c414202c500b560090302d90109000079086404180121415480b01040528199066034032584c1d000009000c1070660b40d55800241401e416050340502c1508200b00003503460780c82051203601c00c09040307101c49251004150946641d0031041d01001020030091111006400c501c541c130040b82601c4681d0b0f4140844d00700c607944203000015007003540205922041014618070b0b070208901407407040258214100c2c41d04078680f01481a503011850703429204005003080b000080d840038a035002d1390125400d8000c0a070450f030081c20701341d2000364000100000d0b4902001d04019680c031541c070821003131520341c1c0c0107030a00205400280c44c00720040003400d014102403400c00e404c044c0c041c080c0d4200702c00c1c5140090207041d5444003a0b1080d0700040c0c0480448286115102404e04880010041502c4840060f002940080d211 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 670002778 1250 670001528 670001537
    0xc0c180a0b011110020c0c06030408040911040302040e030306030c040b030c09040501151d010b03072c03010c120e01020c150c09150307021509070b09040209040c051c050105010c06050601 82
    0xa00388950b044c00049020f064840026a50f142c1c1040400d007009055170716984180f03070a1051001103940e12042d5021303203d40400010304410b01c2c40d5001d185000b203900007980141040b1030144c0029022018601840d07081e01211030654294042005445000b40081e8160340a02c03464a950b00d001c00358544c01500030300000031800350142e0718001111264000c440b080141100c2c8040c8582040701660040c41e0006801d401c40c140b0300c200400311321210390040c292050b092980965280045da012480b50030090080200c80c0040380c01804c7e40c4c1e038201e40079070a80d1a08100b020141d5044c021035140d02a0407001d03184601c0c1502c60f10101c0c280140c00364100410501404100f03884262840e00c4000044459507224075014000a00d0401035081d01c2e51a05003001c01c0c001e88070300004071002510581d6104984885050010030000d00894140759440307428010192007040d0006c006205443c6050a035945a0619011075020f4640a2250b68001003405000b0000702e807865010b207411480500d003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 670004028 1250 670002778 670002797
    0x506090c0f1c0f0209010206130b010501031e0c1d01030b100525050c1c032001111b070b0c060a0209120604060b0102010f0e070b0a0908030304080c0c180a0b01 70
    0x1226002c80700f201c079010380c2043c1d0014001e5482e42e0100510b5900051200082038130440c10b03074800d40201c03030621450341855211080303809607802c000c1c03410761404044d103400c200c01a440c2038018001d05070000304641004000d000107d10303510a0082c12411000504050301e59414441c0031284d580c0030100341182d1070000c0c200d030001c40d00b002200c400300900400003014281c51034000c0011810400c1001520004c50224150020760410030040a1546920b4445c01d40c100e8a41304034090601050728031280e0000140d12904020b1071009a0050305101046680301500c5001881891191411151155114900041c080815600202440440503000e0040d40b00c00c040c10601d0054103440032a0325503212005620340e1350703091040045014002d402070183d40c0801c000c058980d4098000d14005e03220020703084511394050b582075401005101d04491b901d1805042a0b040b035000b02801103694003645a04a0080c6051a40401c1c0802c1c41350900d00c50b80c80300b0951400605041d0303481818040e0f09034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 670005278 1250 670004028 670004077
    0xc1d240306041508010b090606030126015a1a09010605071a010b070b0c090d080318030909060d140105070c02030106051806091003080a0c05010506090c0f 68
    0x12120b0f801004042c001184c100c002000300504450000c144034014801440104040d039400182190700040384c0c0700110221012500c0c207405031001e411900000340d80c41c0041c070003180e50005050081085044500321a052080840398541801081d101c680311050009241070a0680d00c01e000004544603201112880d100c0451640d90003680210082080464107d0074410080c2c051400e407076018690100a40c108410145280244c1c1c0d005804c14100c0400111f11000712400c03556041001040600710781103d1070500981c0d841120207025441107004140d440785000010b880d80030000400784c0c1041d580b07000900c021221a4282915100801049031540130801e100c1d543c01440c0507a2454010341d1580141425200e0940c44035019041f2000c0c0780d080b140c1c642400b560048021100c2c0019611400e02c1c900101d8095040035000001c00034000500d560092600c410003442000240b04907607074007007005540003040341d041d0072841e01044140980354811004118283c1000d0128144140e501c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 670006528 1250 670005278 670005311
    0xb130e070e091f090b100e1c1e050705030d0201020403030801060f2303070306081207020103020309070e0c03040c060e030a0206210108010608150106120506010e040c1d24030604 78
    0x1360302c01071415a0700d0600403403a0900f4160b00c00051490300300280d040081c4404100c8204003e984c0244250014040c841045464408400b000928102d00f042c007400782d0804d0340d2030307411030f03c1880c1c824840c030180405454018000ea40c100ca401d40c0f01d5005036840e200040d19008089aa401c0400c00c02041d01e80e103400c00386462100c819940c43c94641c90b840c010102400701c560942050392103600c480b460329081807560301155034841c2d0a02e009030b141e0300e4a180c40352400c50190419a84200700c0c008008410b1001c6016511a600480b50780381c0042d682c031001c1e1200e00c4288829600750f00520440005410b103a4000d00c181140345c802503888105c0d030703036001c8103083d002c1c1c20001c4540d444513410031010038100441003841e42280b800600552410f8005007149164020303280c51240c651000801d03e1b0f004001604100c80054002e00c840c01080c00b00800d5603501030380e1801528007171400324080307040c400c8855404501841a619110b0b030480300b041072031f81008041592040d2110b2811844801c03d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 670007778 1250 670006528 670006591
    0x41e09030e01080a0e070b0a180608040201031104030b1b13180c0e030619090c0311031c12020705010b030a0f110d150c0215010b130e070e09 62
    0x10340e07164180c41814a000400144001c0c0180410f14140400b9a01c40e000c0031400d0421181c0c10710126584101ca41e070161144030025004001840018400182294200906601c160303c01da03400c01440d010940c494206025501024110b1010000040d40200140703021140100b501000d0b1410001c1107051b01803052025007100304c1249418090354503082c00c601402000011a0400480084a280100e42e55900c010a50701c0e0102210305280d03c154210b07884404aa504400e2001b4425140d0905840c3c60162258150083c46101215440003030f0080144a00d544036980d1180540300d0201c5100281d04802000c0d60350f9540c1300d4510030280c1d403c001a01107540f04104112016016040c03440c1d082c2c411142c054040d50401601d640000c07201c802c80130282100d444000ba4441401500b00e2500c181c0100007028000301e0b07030020401c00464405011101d402e40105244141c48050340441c03150261103c0c00800c1601c0ca800c420383c0703083c10b00c0d154130420802c081c041c0b101401005504a000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 670009028 1250 670007778 670007783
    0x11d0604061101200d0b0a27050a0b03060606070f0506070507050f070b160c0b03090606030d020105190533040b0a0f0e040212010504080a030e0f06160c05030d020405090f040c0302041e09 82
    0x6603008e071031031100240c001e1981c0f01803101410450407805101098494800501c1c1c00d11170100014514104000301e00590b00b026004030488080346440640542507500080c0c00307580d00d2007140140c00060300002440f0094410002c41542800511009140080301c1004200c0e2000d45209020500c3c0d11080051845a4100c200800a90400344107050800380c180b8910f00459040c01c00300b0410704150190f074905102e101c80001a82d5a9801480c080d50365040c0003010701e104100002a5179034400040b60401d110111410006000880200f20a00d00240700d400e2140504c240d003001610f102d409116031203800502780035141e040030108142140c600710b404680c031341000b180b82c011503545481503002d6102113030000c1203d00070814269a072100c0040030440054401202202c281e803060f4418444141d00504480e228158005190065005802503038040e0001342c0004105482d010011800f481d008588050030034255028807000c0e00207001664a40ca8800d290403000501d00d11a44070001d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 670010278 1250 670009028 670009079
    0x506030a0b15030403020304060e18070806090a020408070513060b03070c050d0504080303060409060e0f0640020f091302010e01110c011d0604061101200d0b0a 70
    0x1540200280e074a070400d40103814602c24004c12001a400004840c25180ca600b070800040c40808005110810040501c46140c40c01800340722030140c00c0700c043c502030300b01110f01032859038500381800104d00031403143c01466401a80c040146040c030b0003008050f0310002c0c4003c111a911070040e10280e5009580c170a0001ea0b03141240d00078407100b0701085040099a140003440d0900d01424640d890002800c000c1c850b9654801c40c0d000c00600e680300c811100d0600003918070000c048a241b80c2c903514110745d074028030103440c0c2d47c064400718909100c0c2c455070344041d1105603500e01c0c10a29140011100000c070381061425007079103000c0e80c50b40c0042e81b03c1c50000303039802c004406520004007401501c1400c9418804844030a0014140c040340860342c0e00000c0c6801c082017041c01312a06000202116403a4000700006403b08065500100383c44410307000350024081801d0041860203c401038100b0506600300c10300000880c00140e402c031880003034008002c8040241c070b9040c086030b00100d9614100e140c1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 670011528 1250 670010278 670010291
    0xf03050115050f0103021c060602010c11060915150a030f051b010518060405040203040812010b130902030c071a1f050a03110d080a020a21270506030a 66
    0x4082400355481402401464449807807621010412620790444402d05158000c1200401c80780700740e5a0b0b0f0020600d20305d0131300c04c1907640c80c2c01038000c0c2507026241000407100b407c481b07103e4030000b81403170080c07520800600100c0300264090020748000362440380e40c0004038223495201d5075045d04990103540601c5100f80c20820b20b20707001c4d29000d071070b40418101000703140c1c0844c100e07a0071000b0381c0d001c16940ca0100100e007082c50000f60103841280c000b168040e10110500c024071191901505c0c2040a440d00f4840c1039803589020800360203850f1042c441456a84000d20464105170007454110514103459810600c59583d50003000426100181c45080c00804000a42160f48100390780260361840b001701607803d060110701384125900000e0a40b100b903101140c0c0036116070b41d6a40b1025005500f803030f01e0f000000402511401521002c2c1c40c18007a2114681c3d6a0300960041540190310f031b01c2c0c0008210520594071a9245004603400c4c601c0c080c1c08002030300362601002548540c8401300f000540 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 670012778 1250 670011528 670011533
    0x203030409140711062806211205030c0f07020a05060a0f0e0625030c1a060a0510080609060310110903070f050117040c1a0c0f030a020a032001060f03 66
    0x901c54454000515910036001d00006c03051802504c0034061900c16280f009080380142d160140c8542c0d4040350300078400034440c80444040f4039062594503c1741c0380c2009448803076241203510f804203a034003081d01d00c0300300000c08ca1000c800004280c55480544820368590f680c20004e8000d41000502c00041070110b10401a125400723000c5901d0f5a034111807213420b000c4509464840002c0200d1211113030342e0500303c3e04080c03500071035610092581c041c01c20050340c120703042c100c00e05070704c00c0e10510f000d56080c42d00843c491402c1410f540016050ba610030348141c1da02c104108814074082c0071070342c150082c69401e460103103650050540c43e100801e45560785004640500d40381c03000c15401104140794440060046e41c2c0d02200f007100541d0404032142060b10356041c05942c0c1101c070b51208010292894400101d120110b001c1c0141d108148107030340c3d104034000c604503140d124a00a00300180c00c40d112030000a401601c1402001c0000c07603164454200c9aa84c3c030342168103541040301100d0300180d04004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 670014028 1250 670012778 670012787
    0x3a0605061318020d06061e060f08010e15040905340b070803070e040914010b0108010b1e09120a02130c2307060501150e030f1902030304091407 63
    0x7207811a800c0800060300c21034030b12800e40010340e800910400180080400b030090640001019010006503d69180d0b600f03200380680c1a100d10560300400c0e4a6464440e0f00fa0046241e10304a407000c1d95040465a01e0b40500c16070112590b02895019a54940303031004a07104000f40c880703200118001102c1041d85100701031425486585007000c9148555003032000350710fa002600c0d81198400c01c2d0340c0c3c50340c8070302c0b00a542c0344d01e01044036504145040c5161b020300440e402d0401c00c0ba078580c0004c203c0300040000441d81541c00b4050200441d504000040318000c01c2283e140b0510f07096034800c1e0030320084030009030b884440700e45ca00100e64070592180c1c0c15483e10240c10958010781e031001b08211030300c103d03014000040c20800c8407002c003c0480f0402e19036003290f0032a40320703e42c0420200001d684030b0b2480d2105021741201c04000951119130510141030020b1221903c00201000b000c2942550081043d024003100707013260103000600000607801349901a2a402039007400481c0d0a6142c200c10040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 670015278 1250 670014028 670014049
    0x1609021b03070f02240c0304170313051003020f16050105092a060c010e100b010e010c020402030c12010b040303080a14060f04020c030f090a0f03023a060506 69
    0xd900200715500006055403500104a507040e07494111400d8004000c000e42c0b210314035100c854500010310007a00f04000b00040098540251801c6081401224090350b28050810310030b6246da4001410f008a1418041d1425000d6003450094035041c1d8211200b1200c1e04141031401c020544180340c101008000e0144a61043c0000020100303a5251060185003503101030705010700380c11401115489440b00c0c07044481b500c00d010024811120110010782d51000c0ea0200c05920515011a030340056119103ea011020416900c0500301000d5408110095202500d001080c1004010394200c612590450500030079814106a40b928518200034194000040070007525900e001120f1108c9a15140010340010007560000b211016100205009100300202b15032948400b29001000c0c1c0c3e4080c0040c0700b1040181c600724061075484c01b00c08002d0401c2d0000a41c41080c1403103074000025038140800f1302000d0340d415181003c01d050200801403400d070b002503d1650b1151b081080034200300e042c1d036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 670016528 1250 670015278 670015327
    0xe0703140607140d06320603012610150f091103010b0706090606090b2707050f09130b120a0305031609030204050711150c040512160902 60
    0x700303240c2c90082801002d2607003032100c50100700400b24403040348440951016001d80301075041d00700c0341c1e85003145608940104c5810988418000c1e0752045080c14050150380c1218080f00b0070701113481c0c0160740441502d010310b03c0890f061241a03038105107940c09000b40320b40703450703051030750103d071420284100841210b070f4000704038442c24402c0210700fa551020440c2c0c1110200720301d454864401d03282542c050004003c02500c13060601d40302192080640c0d008284484003140c85285c114030403160004112800d84250481d0820340c0c0008000c98003c40c003c041401507180d102c1e00c2e24115100144200041c603278002043ca41d07688101105050503a00e030190020b080c07000f0065114161703070041c92444000c0c080c28040c445088074001c650b0082c01e44801469000380184031070325080c80001d04100840300100c507544a841e0160f201d0740c1c4003400c0f560064200719252480c1074182828848080e480041030911442000d59803d00d1500707800ba00400303800e83c0350016955182c50101c0168480140d50034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 670017778 1250 670016528 670016533
    0x601060309080703050708071a0a1a030307141507031b02010e060403120b030a060f180c050f060d050a090512132105030a05030703050112050307170d0e070314 70
    0x80082000745003a00d1050b03030305281103546d0b11854a8003812901860a0003841d00c24420903062032003426100480c0b096135206410807150141d44482006c007000548460341603001005080b001c1784005482501110044040301d2400103941903130105041d08842c40d0300002c0d030710004600d00c00961400c0c1c003011541d46c40244034101104119030344460001d4001005e011b4280e0f41c1c4c484004098000d44a034450050544401e40130508090010f005810400f5203010714055900b1050361091201c80b500c19000b40c540503104d0708180a01c40c1131001d01f56144c2d8044c205000542140da024080e9511a001070300340400e074604ea80c9451464524003024300e4898038000e01c00482908050b503030010880d854080070b90b42d1924141e5010108501c05c420107841c601002800720703107480e041070040d80100b45c965020000daa030f8550940070031840014005140340c0082003560003082c0501481960701d1032078114145041c0011903480c0883c0c0c031560440c08039400280c810070031b0103004041c041100703805501 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 670019028 1250 670017778 670017791
    0x20105010e0432100615180e0a1503110102300904110406050a1119020d210c0203060c0306061b011e0609050907052116090e06010603 59
    0x115a14420703122140300d00031080c6002c206580030391400c59079007000083c40c1a540380d8605085034102411542c003801c2034200000c0e9040342e02a05c078402040003ca00801800b00440c01e151100034001005043c444e911920788034003480105412480b54021171144001021502c0d140c400641000300e0181c64444c400c69410b10301c05e54034030320461340b55002d40c46400705584020b98800100103050805862040040228000c150740c0c2d040309c0103145091840c1c403000142c25a00007500d964034100301c040982e034520900c08400505003412881030b403910400c000350f04442c05204a074100c1c60140340306000900c440502a055003030070712289402c080e0f01e9090514500e00407000c903070948150040c094510b002407040e5010000294041c84c0360a00c8044506c1b00401d5143c0c0e40400341565016804110b450107001c1401e0101c0002c5a204581f409009511800d6040c244044005c82016003084507004149601043d1032405110328060101480c4c0060401560702d00c3d1403070940141c02c040b05045c03a000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 670020278 1250 670019028 670019033
    0x11b02010509010c08040806010312080c070213023712090f1403190503010f050f0d0803060a0306180c0f06020a08180316050102240a0b0a080a0b010303020105010e04 73
    0x465203080001c0c04e08440d4800940303865441d40c85140c4c070400c680d005410021080000400c06a1030040c1705594030441034540009a410901c0f400200a5210444180d0000e00350480e4029004c54803e0710311894000c079841096000c90020b08021000781000d07128120035290b080a650351445003004000c2000c0710302e5684102d98000686d0000d07200d0081c0c0440050b04503410400c1721110b440401d02e50500020424001c1c08903002030107100400c02040c1c1c00460b4a0518000800c0301420042001900e61080d0b11907002d964006000c4c01c0d0002600000030000c00d09a008070501c1c29403601214181034683c0c2440c0301c0c00c81c0c25800581d4035490513030b400c11005a00041e9080040c0e00844c1a41d1b844012102c0c50b26824280b89055030103010b201d6040d400013425010f51070894100382c09941c9611142101e500b80c03441101c182d28902c541d50400700d00702038003a501510900e00007620310011241c4820701c1500d00f0250b1070040b55400d104400601c10194203004040c01403561188015080c1045e9 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 670021528 1250 670020278 670020287
    0x20601120510050c13030b040308070c03051b1c0e0f0f010f050a03090204050403020c01120b0114070f0602120a0b0306060d0f0215030106032004140112091b05011b0201 74
    0x32070344841c402e42c603040880c0c41c020050089401d00311390f0f24000c2603a01c3c0e6030314021070000c208a8044e000302d4000000100e115014243c10030146906680301454415280080d0a0144841180f000d4a101d00c3e00b81a115240500b15407085100c1e85d00c0f4800181c550004010b000c1c5048980c40c7d0280c1d42e810a58540c0307136023000c40c030000b401160400c00d0303c84800003001c40060151010181d445801c040520040c143c0100e5040025032003139a40c0700f0710740001501c070000e4070317044910940090300c2030202c20340c040b440d00003521b40c441c4600c031240b554a80075240c0c00f06980001030310010b03042c800300038401040ca603403040c807800300c0c81900078100c545091b40000d030818100000103411540000014001c44d0342d820b040b0400034415040283c1c07a541c481c04010700401400da60004052444c1000400744059801035a085075092400c0140b880c0300e1800441d140381e0740781d0106201640b14908800064000c204052070850220b10240815140c00001401d15845100940700c1c00d0b0301140c1d40c40581d030311 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 670022778 1250 670021528 670021543
    0x50a26010816080a0b282909011401121d160e0f04030809010b0d030203210c07062004062a0c03140304030f05030702040e0f030d0b0622060206011205 66
    0x10309408441d03d248410505c0c0c081100030043d0980b03149803005d031005c1851b298441008035887c695004400311000c20901205207000c1c0201144207041328840713580b5602c030348520400c010a120000c0740c0c0c2030038000394400d210711605906000d504841d00000d2280c5803c003080b0700400c0503150540d00c50030304a00072284580e0140020307040114440000711400000d4000c0400010058a01c54428290b418001c1d180d0b040340384641041c441c42c0414000d80c070080c030f2aa5025006003007a1526200d11396458400070950f110f0004503c0004209880d81010142d02920003024141c50701c3d068407258001810080200c82065000090f95408070030108901420250a80303501407004146032141e514a2883e500841d80f0050a159080b6903500800c600800030300031003031090740d0902445d00050070b11601c1d1041720b03003ea2102e40c800e01c260350599807030f5041043c0600020703208601d40006255035400340709082c059591981801441000304550400049005010307034114810000c040d95170f16a01ca903d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 670024028 1250 670022778 670022791
    0xf0e0d1404031a04031103071a010914130606050a14040501170a03030b03030f0a0c0c05040204060c350a200d0c061d0a060e010c050a26010816080a0b 66
    0x3c2200240415000d4180c0441e03194000301125281c203902c0c90700d48090502a4040d030b2551a05000020384060140030b59003003007050036068000f07952000709060b40e07100d40340c2040c1c81846e11610700243c151150000180a008118002000ea8001c4010702042d9001070388002c845841420360641170203004121100038130351510f400305140f4201c60000f0b02e140075072950014200d100140480109400105071410703e80305a412140040c1e841e07041000300d015034801c440209030f550045d45c00143c0740800380307070200d8013913204019944090f030101c86202d0082e605500c03044400151040d0035507006100f02d5008181d01489501d04800c892915495030f06a10258083c02200b4510904000c2d007a007124684030401106c00443c40e921482d280e680e078900003001d8962902d800500042c820040c002d911380c1400640f240392800b514544101d80c000d02110b01c4290200c00c18189095030750764940190300802c2c00f403004125002d140d0036100c6201e10f4030b130b00140703890b0321040c40400001d0181c4c10050b8804c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 670025278 1250 670024028 670024073
    0x12160c080c0109151d070305030a1404030804030f0302060907050a090c050f160c060513030b0402011110020a02070807150e03100c0309230616030f0e0d140403 70
    0x80e00d0700120760140100000042404104581d00761300b040c110f91240711603c80c1c05103004a0f6120b5009219207840b481e00028060b03400800814442d64090090350111240c01d03c01e81d458290703261240086900b03c1d400c100c50107007250410301e080c150f04100054200f09440e002c3e1280c0c1d80741000080a2003040d210749152203841e4808180c82034010015102421955070081d40d81e1846002d0070346070141c52010480d0810200d200110340c0601c00c10948505c102c0000c940c000c51401c5840e0344920150040c0101d04200220392005550032086c405035031041800c903005a201c0d611203801074240002904a0601039225071810096034bd444105032100b800307681002418203034140042814066203a090b00300c01d904110504030040d42c0742d071008150300e0040c0344040d0f00824503054551031154042c51359440340c1c441008a019013003140030307080d03c0c0041801d000914401c3c01d0310f500c090711026030000d51141c10104400b81d925800c0841704a1010507617041c0b034540740c1175a440c806402c0600c0841030700072 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 670026528 1250 670025278 670025287
    0x109030311070e090705090f09030406030908040b07060f060504020a1b050f16150908100c05090a0b0909010b210402220509280605060f09010b12160c08 67
    0x14001484030700b0141000c0350100019251904040f907450640744900da00a005680005801c1211040c0c401d010710b54078005103203490301c3c218084004c0c0152000a0f506d070042040000b0b010301c200350003028103620840380801d40400d0b40b007440c02107440a901c40d41c003550040040f00c0080c1c2d400b09010195800c1860340d6007404a01e414280d28200c18030001c10141d106030241d011441c0c00c20030940e0212000010060118021004119482c400030700c01ca1840791712160700c040d02601d0719000304000039414a4024201030051002070341e076114550014810a10018410000b82000c2500c41c1c09084080402d0b40b5254500010904414011076900c54800100c4042011580e4001d000d42c0c44100c2d601c091095044101040b9004000c2902c94a01c280710741d00d003002d9010880b508002e24130003da11080c15982041d00d406001d498002d1200303512003e20000628140e0b10020103074060030b510503225484103000c00d00100884009004900b4900ca04d8a900012a6209225680b040d0340041100e446 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 670027778 1250 670026528 670026557
    0x5010f09030f150204060c05070602011b110c1c15020403080f0c12030430090b0d02220312050412150209040f0c020d110c010c020117070e01030e010b01090303 70
    0x1000c1c20340f240001803800020000781c040d9021016a140500440c141d030701c3d0b950799000603070896400c0ca4103440300008106140d07d850b4058865038941a00d0102560440c441c100c00081c280c56031000311894401b01070300c2410034090660982c01d90300720b40c40d50440c50141182c40e01c4041d4003d11410021034980066022603100051250b941b6500b00c100d0704641300e08103442c2003040038072220078401104036600710110354020201c010124809031500c52241c80d40c240030140085900c40000103a00b107130200086000101a00e202c010760641e03800c0c51144d01411440c000804075001d103009130400c082480180b026945a03800d840c1c0c9180d0200420a00c000703003060000c0640030f59041503901600d03103491030f061020349d07411003e1011802d074240c4089044c4004103a51807142000018165400120f00716481d501441c030ba080d400380141450007640c4071807481e9000c0000c0480e208000200301c4001e202240d42c16004100d00c80034440028015408000c000800f48621888080d082140003542c1d45817 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 670029028 1250 670027778 670027793
    0x606050309013801210b1f0c1e0b192004090b0103110c01051504150e060a15020709050a0e0c041e0c0908060c090307030b25020c030705010f09030f 65
    0x3200311001700f5100300340111840d80c3c004000a41003140111207402c0400c40302001ca0035034031143d41d001e894000300300c3d2007034583c40d200900900c2c10480c0e40b161003801c00b002c19207015003244144000f48102c14181074074041a0142c03012820002c3d4a0a4600d07161007141c1002c0090300c00391440100c0016581c02c810740102c01401c3c40c04520561030b000011541a100010742200b803003403080f101001c1031801c9010030f000c00c5803829000e04c1c0e1190a0464184802c00c107202c505500003100900e900300c2c2c2603c41c03c0c2c0c0150b20071200b080c5c80150303001801c200a607090340e01401d68000b9102c030003000f900c020803004a8582c9a0003030602e109542d21044002007024043d001c1d00041c16104041244540762800a86004a2402070b02e030103102c0d5500081240d00d041c02210310790b003009005020050f18507520a68400c0b0050304102040c080d0182c11410307002036028980c1e0490b56a801010040c82c00030926003040c04030b4029a040010200d030311400940c2004142088951113084007183d4021410100c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 670030278 1250 670029028 670029047
    0x60c0d1a040903050c0616170406020930060403050715090507090e0714220e0102031510020d140705010b0a060201090308010f030b0403051b010606050309013801 71
    0xe5000b8a0000035009042d4442c019180c00d003003c1c000c6407030680b100c001c0c0b011380240b80d04407480050280c501a843c0851080300c2103400510541016081198a0380001c0b8244140d02d100400700e080f54560700007181038030314400728000b9410064029801d194400270058840c4060280c00b62903200c1204e03040f40a00d5100941042c2c103c0e0503181810b0711010325801900104130411018840e00307078007040c004d680006400d40c21170b00030728031402d040d452008654000c401260801d0415a2000401e005000a000451003402c581800c1c0030550583c10030080d246c1c0581d4154411903025403580c51510346c100071030001da0300f00e81d12002d0f01d5242c9403504e1070140041c0495035401051b00400062842e4054101c651090302c03903280c065170b5a0700e03104401d203005454070025080c1050400441e021a0103100206508610000c805134201c020742001070941e40f00da8010400500c1c00400c0181c90602072042809070b801d4024198650409500c0401409400e030051100c03180b01503c0c0560170740c3c0511542d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 670031528 1250 670030278 670030331
    0x5030c190c152004051f091a0405010f03020a081f03020a030c0e16080406050402010e0d050a031e02120d1409010e0d050906031302040f090609050d02060c0d 69
    0x5400609010700003c0d182480c886203100d11400031084031500600283c4080e40e40141c045030710068a4110b0746440a0304020580c1400700d0f0004c0855104006842681c10b003216050460342c0b2403610000604409801030b1401c10075106104851409600c42031341900101c0e107081854510402c861079040d002d2003a44002e60140444200008010102c40b18400320380250444600a070344140359164401e242000d0300002480c154005000100164800c5810600600d40640c6810080001c80c00000c0b4074201a40d107640000318040030594881c03ca40c542c10f40b80e840c00440d0804000010b50307030301e035070306145c00409001040f80d40c94502c10b0b41c030066210f42034610408030380c1070200580b4001c1090000c00c3d00b82c1d000d08400f810b50319001e1340840700000c9019085034a150703280c603012070100102a10032030307120740c40350007c0003408500e004282c14580140b9000031802402e20340103280c02403500d0403c0954000d48200000c1045220540740310340c02410b004150450307082100d4014245881d0300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 670032778 1250 670031528 670031543
    0x1b0e1303050408102a0906080c1c0504060f1514041b18091104090e0a080a0216090b0d020d03030f06030804080d0908070902130807030605090d05030c190c 68
    0x85207810400da801c0f1200e03240b110103601c0c903181c40041031074400b17422001003800480d00949081004506c00c6000755400070203160300034101081030040544643c0d000310b071000c10580350824030042c0141e500c54011284d40949081189050040000407081e102e403080d4a4200181950761405440f40d402010804001c0c00841482c034601c00d030701505e582803014a0790f00c1c11180076001701d8000304910070b0b038011583c501170290500b490000300b1800b80ca208540c00c1054040e407481e420025a60402501c1c0e1002c5607000b82ca221011a20700c07414000c0e150340100030366800c0c80d800c4045c0703495644100e900c043d010b5800c4036070746506040c05d4000d890304180380203583d441e14800205024104015006841031003054422030001640216404440c0f400342100c2e64120200c10880d2200030790081c9405501020503000c0d0a640e0321000d81808080d51064131240c2c0c60b101045445002400443c0c960491410160f0641c1080b15401160340582d54041300c2106401e04442103150140c0303090350029030301111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 670034028 1250 670032778 670032793
    0x70501030e190b10080325030516030201060501110c06030c0a11030a09090506010f14030a15090501031703090703030c02040605031f0506030703020f2403010306091b0e1303050408 79
    0x109070380341c0b69040b5070040c003868030b906000c03c100102104840041d00030012003091807c510110401c40441c904c01101070180070441c0c031f00e07444644c20655104500a80000882c00d107428009014006090000b00d00c44d000810292040d940714016603820520b40607810384c0301e2040b000300303a0721801d0909080c42d5912022400301c0595034040416425100442820311050b114200103541040307005074101c01043e10314007407809090203070000c0c50703101c4585040401e2106412607080c0002d2810342040c40d44d9502c0310014002d00070885810342c11071214403602803951415002c55038072014103020090800c0001582c0b641955640c0e000f00f07025080c0181910b5003c0030f004c0c03000c200d070050b2140c0344603150304043c0011011300d400315100c4c0c00c5a030080d00302c48810007258200205103180030300c038015844100841810341002ca82c0550301941c400e06001a9000d460f040031942482e1003c2d00c0d80c8549001c00080c411317404504040f98004c40c0c0044c0d00d0000d03c8403480d00761007500841c0c02121403441800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 670035278 1250 670034028 670034033
    0x801020d0f020906030403120f0606110706140d05040201030f0e010b130605010909021308061305070f050d030c03032009090603010e0c01110c091006030506030a05070501030e19 78
    0x50040c100d0124004003040048208066082a4001c8108442c0e1102051000502181c020829003d0f1500920000034603441d007248004100c958503084600011450f10b1100d440c00402c00041010b89040d0504030b094144d18041460b81d4420583e0000040d501c4030046070869000741c11019051600d40010710228000313816040c020504890201d204101907050700212584920500c0c0079294180d590a0f160ba050002000296000e245d54000e514400440010003410038880607000700704a0781060016100303810300c1450100c607078109045000c62141c041200f40d403070601c5507080c01c1d4941846803c403034503824240c00502400844900c41c0c1004081101000c40080003890360b0788007184e0516141d00c03030006050032250141c2103074102d544416084034040d070246142030812091a012186000440b03c0840d00448096548501c00b0101010a20480da014003c96a0010094000f41640380c4280c031401e42d03030380c20380c40b429042c1941c4002d4950200d80511002040c0c2c404ca10501e241a04240b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 670036528 1250 670035278 670035281
    0x906020a020c0f01052502040c0c0506101212122d090f0609260d0b040c08040201030e030d05011e0509010e011a1b010504170c120a0e0a0801 62
    0x24440344018018000080d100746030402141c844940180e41c0d803420506007080c8010913021001c940444a50840c054500580d01e9002d1003124100c2c0b5a07900740f00f0a15858668513045018007203401c3c001c1c0500061140385440c6e400030781080d4010522080a0a80c054280e81c50803103280b00740d03407a40c181b400c0b202c62030000c100f0103405100454400007200020040c0c8004403008070b1001442c00e65114002000302e50140c00c001003043c018407012060b1714250a21a1032121003000c4a88403070350215480f210013056114541d20413600795800d120000344118000c01d00007005000038141a9540304148440314100300b43e411030224a00c00b00661b58441540b00141c00720f802c4075070f43e2210b61280110707407400c100199604079a20104e07600c034164203044203250b100b240220400811103051002c00301d04805181c42440008a680001609042ca41803110400001b6510044000000c0046e890714640000325030301c0390015510001c0c1c8403000188100c0d41c0168030a002070348554091000700321550103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 670037778 1250 670036528 670036537
    0x31d0d1409030f010c09062c040b1c021c020d0b07090906030f050d03110a120213140f03010b0d15060b040e070206090105100302060a09050919050108030313020d050c04090602 77
    0x10f03881d1180e2150342c1da1011a541000c5107440b415101105085555603544234800800240000700042481812140450003441d184c1802c0581c400d141c0f42c0d50320550078251542519002d0350f2004281803c12900030a0101d801408001e03c040d50700d00005c3e15151050804078041e0442e040305000082d41c9051020001c140c022080d12a8060080d0006049000740700390544000c0303c1507c2c80c20f100702c207031083d982080a5010300400c240c00b00035a2904031410350310070010707020500f0030003542c4585400707000a100341020b51500070b0385030004055082c0c0e502e40e003148034280c1c80510308030b10021500f0103402411540d80101000c0b9804500820041c0101001a02c5004242d00300d90f0103035180c0c4901800c3c2c0302d05460358056134841c200240050300348036004140301c500d9800e0101c43c0c40d41da00c010a0305c455040342ca03654180d6241011025880050043d03030b0040c00c80c2401541075042c10a515800c59a81990083c45004003118180810005009812203944002e10400c0701c060f440c10080060f500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 670039028 1250 670037778 670037801
    0xd060b0c0f10060305070b0f120c040603290d0507090c0804030225050409030512010303091401140301170f0a03020d26190906060312031d0d1409030f01 67
    0x51000803940d44103441c403900f42103070341000061041c41c0c40c1183e0001d8031341c0303d02d45031030811604100e2a499040c1d03242c03e407809424400c041a59680c03520b40000c0840340d8880800c000c000220180481e502da0021529070322200840711010003094501c1d00d81d03c1c06020341c1c0f00c030303281900384840000307495044004103200700d010b6000d9442c0582500e03107601190034144103900800c15045024803040c102603000740c68003031003820420304e042c1444901d07506184090b0310450008054817400c3c080d5203040700e02000041020f00700006a212240d41c040c1050005000c0c90409540e040140e440c8c0a00421155550301307030410950300880e005050094a032605001c1000c08a1400d01c1144038800300741141a24200c13a07000d41d44030756180c460680352a908410302411303115441d00c1c510000300b0309910410005502c2000c00d401d1043d81504050141c1d81c02089445108808070700c00b880c5250042441c800604103450f0a443c5954800c0145641e40a0501c215401d4030500410b80f002c0b000c154440071103040e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 670040278 1250 670039028 670039033
    0x10b0d0c050a0e01061e03230612010c1d0102030415080a0c090e071d3007050d14100501030506090705040209060d15171b1e01050d060b0c0f 62
    0x242c58043c1c1c0401c00100788505400950040946851003a400c0705918540c9601d24002c40c449001c01d0118281d201948400c0c001c040b00c07075091000314506144d40c0c9a0a80b0000c0081c8100301480101900b05281c03c0d202d08001081940c1902c0c640c4e20900841d400b802810755003100100792598001c19240044400c03094281ca4145205041c230b004844400c2125495503080c0300a540b0003c0c112000b0005026070340603005940f0300c060b596500d11104940d00c01c0340381c810503a64105c26584442070001041075485a4115050900060300d07003030200d40c5003540000303000c14012605104a40b9280e1007500b0550355614040000c8100440868080d0180c00c41208030780301d40f500d070030422040344100c01e0010740c4620104048402e070f601c0d40c0c02025404004000c4545060380e107a1503480c100c03190f0620719440d80c200c10400760011181410300042c07160152031268407200c1803d0920060150a08060705001c1d01003001c0915500c075030845d0018010010069072600b00350503d00342d42d41c03c0b19400c0c07650760 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 670041528 1250 670040278 670040299
    0x3060303070b130c09061a070204150b0c06130804260a03050414040b06091002100903020a17040b0403030509120a0308010f05090f0705030615031005100302130b0c010b0d0c05 77
    0x41805c5d0051109441c07000140e9110502c5c41c1b0000143c5501400c4120b030403d80702c0800314120035018690300700a2180390368480d90b17610140f01d200e0078201b00504e0301c98020000045003010480f00c5042d141034440c641448140d07100000d40d203e40685c2403014408603441580c01c0039040590200140086482e140700100d0441058400c010544419800751a00700f0400d21500f2050b24112080c4949883e503070040c2e40c0c0d080a000061015503031859001c1d40960710006100003003210800c400003010008100701410b150404403d110107109905c0f0180820071302103400801a034a14086056000010003241c00340002440c0241c000b1009128541c62800c0b500c0c8009000e0801c8001f0f10301c201203000c4820981c0d5942001174a840c1c001604a03500208404004035414075018006c1d80205480c501c0001c0b1245000200048051426150810107005002032100a648042d100d010b0b82c0900800c03a840b400100026801404042c030300d5a4040100034045040c400a03505040a4803025241040b40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 670042778 1250 670041528 670041539
    0x192408010b03060c0a0c0f0605040b0c0307050306010c02011403090d0906020304080703020d110d0f020906010f0c020907050c0304061e0309050d0302030a111b011a0f0603060303070b130c 82
    0x8035261541c060342c143d000000011425142c400c024400c1e88094100501054400d86440c102001da4080440d0400d030307205c00344001d00415080b05079019402d451501d14503c0c11103401003040c0006400700341840003584402086a00819038811041440400d00d900c91800c00032040d501d440c3c0c181e294000c80c04181c4080b4141d48040220f4054414050013003016900e0b560030301c880c10b00e82c540c2c1038524448001d404089070741c2c0c2c20312951043e4000d900400300c24015004000c1d09040241c011418000348600032001590080c003010880c58040351001aa07540708174041d2100d115500c1114240e000000d004140690455803c92034002121250240341c40d800b6411340444028a9002d08154042c280c1d8082d0184660000c6601c088041408030382c1c1240800c0b02446d41d08070704590b40c80d45103c04110360406c4024070070b0f488031441404001010716030250110740e0740816240f00d58000d69000000840a48040007120000340d481402c0410764907003500b8048034040000710403144100c3c2c44000042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 670044028 1250 670042778 670042781
    0x30a060905010b070b100503030a0906093f0b13050c030c011e020a02060414010e041509110c060901050624040b030a2306150c030702060319240801 65
    0x694188032007407442c1211300e441e1074a100300010514400388071440360200c0d0948061020700b10760511034640c210b103139042c21400750038040ca80e0014002200600c10703080c83ca01540c66a60325800142083c120041848801c114104103d0200a03100a101c2c0c01441485203500c08500d10302030240c1d06849600c51443c041580b03454024029038000341041c02c0700160024034450665803044280101c0706003107007613404183c05401c0755000f08076038100c01301002020350300503203404030525040b6401c01007036213134114001c0070128500455840903910184950881929800c40749024141c004449041c500307071900c90301800c41180c0450055402c80010b800c10310102c0e000018450034949594141410844281e40c41d800040564040070b4441e40040c012610681c4405240c10340c0340305428080c03030200207001581030850000040d107001040300b4081290044165540941d0480e00140d40380ca40e0740e0320380e0103044900000707400c01f03203090001024071001046001007078500c0704400362803d075500384150 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 670045278 1250 670044028 670044031
    0x14030307051203180609101d0a031407080301091a03120a0810033018150c08041715061f02120a0806030c040e0a080f0d020f030a060905 60
    0x2896903204050302c00070181148080d5034424040da0b541c15405060010b65440d0072801d88480004c4c1d04010802051858640160180302140305290075101d426054151794038071040c1c001078100010014140034840b003420480d5003a540001d02d0b580c0b203503150410750000304075072190b4030b803840c16801c140256401c0100c5c0d075880000c20844154208515042c0944424038005c1400c1080048840e0210004802000203c00c1816600c007400c49601c441c1080c22031010003d0300581405166040f08040c0420b400310041a90b041990401440184c00d009503a03158646c10018041c1c900401e02240d11036009001811003050b103401c8502004490f000002149000e50300250881d40365181c2561481402c04580c01c028080e104440d502714010304814000d4100070308090000d07401e0b8050048a103070030030a900e80c1d540211401c0040c44c201c5807c8540d509802d0700300820040f0082040b0518003204c02c01c1d2003455816680555580b05d02440c0c40c046644201c5c0c444201038600100405e08064a12989 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 670046528 1250 670045278 670045283
    0x15040f141918051003080c151503030417010605150c060a02040506030f04030c0b0a0c080901020f090d140303070e180103050705360117010c0e0d050109061514030307 73
    0x282d90b000031030b4034618040c0030b00402c1c4a88180071008000000740d0080d00501a150f2101e02500103000440a041c04d00c080150003004107840b0ba802d82c50066902000322011150036030548081c0b403c12805076805044a0361106901c42510b14118550704080c0e402048203100400c2502c03d03c0d600c1e189144101d001d5070048c80d03005581400018180d81504041c250054000e003000c000d841e200d952440c00c42a0708550400008d510380ca02d40c224150400303050340c0c000d003641d8000d50500000080c8001c15008032110b0b54400c07891462080c090110311808204128036400c01c0d02d5503440e28101c042c0000c0801c143e070750b0040d160042110418500b000585040c0c90b0700c100540505441c14041064042803050000b820202c0042c5240d4030b138011071b00b044080c1182a003000402d61410f07546c0c7e030741001c1d422803810090b410907004c10301643d8489039814045604031583c150f40c81207411300c83c1c01080350080080c042c0b80751100d401101c41c0d4158070002129005506840c40c042c40c0028991240a440d100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 670047778 1250 670046528 670046549
    0x615020607020c010e0105120c0405030d020a1e020613031109091c050a03110d0c02011b08040206032d06030d0201090c050402071a010e04150b060915040f1419 70
    0x20701005611801740030002241c14503145042080d0001c0140c425001501d0701e0380d09071030001e410401c50a082c48029886001030020f000c020500ea2100440070000000208006146515480c115600c500a948144d030718840894041e03620307881c101a80c000c0d4002c0c160300c1000301c50001250018000380c0c01141d61640d25001545640c8420251160f4010310b15890a05071540150b01514960b240a040b5107007401c01c010426040c0303000042d08541c00350510301100c122925521811640045429070855816924140d03a55900701000c10042914513200b02c80312072140121303d500442c08030081c06058214240c0740d001601020603400ca5403603641c01410340c400c0c070204000e40d14180e03010f000598042e4425461014207460b4844c580e800036000000c3c003017080400e002c01d02c0a02c441540515414000070006c00c0700140c0041c1c5640588440c42e03100c1c0318400181900280c242c400e540007000503900a00501e27031154a0001d0715000c1504480c0102c840803009500408000740703c1c402c446540b9103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 670049028 1250 670047778 670047793
    0x1b030c070f0b190201020d09050a0215030c0307050304020303070c080a11010f02070b09030703051906060803040f05040f090b0c091516030f03061e090c030606052a0304030501061502060702 83
    0x2020903c1e514896405056541c00c1c03004c2028244a80224184144500050020200c2d0351041001068540020420600050040021101504084a030070264034103005442e543c4520000b4078500c24120001c02451a540000400c2c410015900d0b020f244141e5906c14154505001101e143c08a0060b90b00180c1c01031008000b11a0414000c0841010103001c1c0c601c1c081d204d841e02490420340c0040c1d21a20344510141d00c0612226208040c0500591790186240c146040c200507107161450090754031450350381c05980300c2240c0d40da001510142d80b00c2561201c9242100c0340c24000d42140c04011700880303000d503155113501c0102e011114107513501c0714407054039040ba0b04e080343c3c2c500740e0340f40075014075503101e2010403560700c410400384249010307460799601c40f424030304c40000340d60b111102c103401c0c1070030400140441c1d80c20800307a9110640740c110015554410072340303100c418110340100751464000010013005015040d00315409440340280e103606609201042240d482074103d54030b4006800245 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 670050278 1250 670049028 670049047
    0x130209060103090503120405032a06040320010606050a2006071103041a0403061a0306041e0b0108010c110a05190c051e0a12110d081b030c070f0b 64
    0x503c000358850042e800ca9081c0104030200000d03054003520103459a42c0082905803268a1207203150525004481055080421100c1090354499002d8801014400c0385020705802e0822005a04e810405a0009003d00740d5618400380c00c0781d00010701000012300442148a00100c400ca01d0780c0c000c002500180000d07580c45900b110b03d82c0c0d98040c1c840042c0000c01000a03004840c29030f050042d40c004820703a9940f0303d503107848002c0300d801e03d91001207007503140c003c0c000503500800c0080d4440d80000380021502d15803440c6810841c24a4401448819410004a0503020540c00000b840f003039a181c0030018690480c1040e80d42c0f0b08918010b00076403201e030482c0e110041001c01044582d00c10603182c0949926080010030305000c11400a4010351301c500121040e01c0c1083c5d0900c000c1403c100f42040851094030740ca0039008000380b1903070141d01c813245202d00708a07200040300d0001d8405112016080b64481090781c40b030344251041c01c0c003845102c138013140d1075042042c0c44003190b01c044040742c035040c0f80b072 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 670051528 1250 670050278 670050281
    0x5030304170f1b1c03050a0c060e0a03093807030314040803060a061b0305090d0b10090e030418050703090c1818030507020105180406120209130209060103 68
    0x507400300280e4080e008051819090402642c08004584840010211150003e00000d02d6081d5000200e404c003009203840030903049821580021414036040000d1282428100040c2030780040441445c400c0403d01130606620101040c05c2d59200100c280c20002c0b5480c06c01c00410084852160000045407646006032443c1c00403c0c41c0c80c42420049120b4001260010203e00d0459050300c4e460400030401c00d0a10f4049500780c0a0003c0d42030040b40340b01074007180b9152401c0c4060082c28000006590001d076074030b50800a407180e5010066640300d00e401d40c00400e805403144143e03082da500b0035450b00000380380032054406481c1d8040060190820119000014140280603034051586d160a11030110b9218070607840682410080043c51070302035110003040321040301c450110388005092880010f68003400f201c0400381c0920740151035162508100c2410191010115801454141c001542c560704500a0215900840341410169a28098150300007a0039000a6001641e4000a00d856019 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 670052778 1250 670051528 670051559
    0x1006060e060a0309020409030302040602010e15160c0507150909180305070f170a12060e070f02032b18030e040507051e030a060501021f02030604090f1505070905030304 74
    0x1601c1c01103134540554000c6800c94004010640000750005814001d044d024000c8400e0f2500140080002c2900b2602600364a03070b01508000c0b4603d14100c0000b01c403031040360f81c0044240c1240c01da81066a5442e2540041c0c00c50352107000114041803000140280c6520034980c0c01110441100d101c5c1003655400c032000d038421001114201e043d26101c00204024038130303c1c5a03541080a075907507190101e840c050821503800d119040d54509291043c80643c1d01038104079004261420210401020b04100703900b9405020207242c1041900d42d007028400c108a03101070f00441c1030b0b40d010440c0510205103e0103030340e211074020300880d00d8444001c00701d041a6000542c0b05400e490301605010110107038502c5000c464a03914450900441442a03040252143e68000d0401740024208a4524280d000300700003600540e8901e1a800710000b641e03038880c0d030480010b0503071146202d10307401c61078a0f0141100681324440c2c0d1000c3c0c500300016902500404850060fa00c0060086003064a00308414060029 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 670054028 1250 670052778 670052797
    0x9050a06080a0b0d0506070914030c0a09180209091015050904030f11030a0302030f0f04030c0f1b03150501060305013002040531200a0302060a111006060e06 69
    0x1004d0060b03034049042070007003074050002ea980d6018524948048294010f80342d4020034843c0d00f081e0048031095440ca00c00c0381c12210b1001c000325411070b0b0944050000c526041001c1c0d0080151400c00104a4000c01c0c42000565296810045e048400030300c01d0340c0840d07901800350000103c101280101e401120301e03107038038940b80c44c08181d0b40424a9100d400d40d0031031181403011a4021041c481d00480003204940d01416407004801d4520341900c005100c00c0d000a0003a008850404028040c860b003d181c4000a41c8500301d0440280d54900d4a030201e0210f4400c11311125107480d0001c00c04134403074010742d41220300c9071401304044110b00400c4100d010010002820480d00c0300600300060700c070381c002e642c4244200d80e51120417240c00040307564118004500d0303007010100c04145000088100030000100a8894621041c00d142c140108205003810741001c0c0d07200348007207a49140150b2255035981004003041c03e88030b00a803031040c1c101c00d550041c01404c002c00c43e10743e000805800c003075028003488e40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 670055278 1250 670054028 670054039
    0x3031806130b0c0d0f02040801020901090e07020303070521070c020306091b040f0b0a091e02090a181d060916050d060c051605150609040b0a0515060c07030309050a06080a0b 76
    0x5c0e040460350081743d10952118410703035008940d801c250b41c0c05c196000002c0000c4001034a20303151150009480b440000e103410140040824201502c2801c0f031280745190f101d00003250100d0400b004050108180411b04a120b4403640c030000d448030001288806150040c1d043e0081c00c424900304003c054040d21549807001c0d980c2e40486030556861615610080c03001001c000b5440740c2409003030040035803110101c98200c3c01081200d41070384070500c0ca00c085a0401c40004031001c59190b0040c040d122890088000f11950000d64864035000300340d00d4058581a4121500c0c03206d400c1d1380c1581e114161198a9002c456110408082015908121044030441ca00380785480d90342c140f8600c40011003142034896512011340d410011420301c0d1410b13040401250011070502e003e03a900c041c08080204128448c0c2d48641c0494690807100d507801c2000d140080116446050404410782d6511440c402a00098286000020070303040c10300340402038030390a990708800d03030b9a0900c02e80049c055030700040d034215 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 670056528 1250 670055278 670055291
    0x31236120e0409062a091202060702040b030604030e0a1a1c18050304060e0d210e0a081c080603100902011707050c0105060f0102030409150803031806130b0c0d 70
    0x81c081d480385101030354a0325060403020810180688a008195170404207201402c8800e0020741d85d0260076040440e8101c452907a903080302e20116014001034840c264041c81040103000070150000c51007c400202610001c460654420301200000a0800154140c403010042340e2001060307100003071528560060003080c801110400200d180541041c20b44054001103800e0101c00da0000389903002000c11141003c80c05859115060440304081000e6440a40c01c42c92800389401000e00709a0740c0300003030402e0031042e501d003078280c1c0303810213010165840c03078490902905143c007808040d0301600c0058000c041030188125080020002e0100c00e07814071020126140358581c0024003544940c1e00d41d91605e07101e2001d2000306c0c1c2598006010076101c0d8500001d2403200e079a0000c20340d0700301c0d5000c0001080c400071100592480720915002070f03c82c0d0200104000170030b6904081e8100c604600001c607411030752001c0340c5400003108203030000c12840304000460004200d1101500029440f0350303001501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 670057778 1250 670056528 670056533
    0x9050406020c070303080901240501052a030706050a0621060615050403031b0308190204080313030209070905061206180a05060f040e030313031236120e0409 69
    0xe00703d0310b500841c00254800100074211201707004129405050604ca1818547c01d0040300c0500e5115000b65030400030046041c0408500b440840c012141801d007210440b00ca42c1c200440e140c0c1c0c004242600e07142d0404000c101c01c2c00282c400e101c00c035401101102c8142950388030f10b10049403841300594015403604d101040c1203442542c244142c55540d20b900ea61a46946005005000301034558803000100c000000042900300808039030007010811181c010407002d070582d4000340144d40145155100c04500c40340f4200004003020b050b24022103651509684d144801c40e070040d04e81c00f80036007281c0705000d1409281640c5c4000e6401070f9004040903148103003640d071040300c00c80881d4410301e950b451300107010240c2025408413070300c3d09007900c0512901100c034604a6880c4005801c0d0550240000c00000605100d540341c1e002e2807aa014003401580c8003076003070252008400640380c806590b001c20010708441c00c1d4038800010b50b440303901e080c40c0004100b01a02d60f14041d01d46960840d8944c11720000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 670059028 1250 670057778 670057783
    0x32a0d0c09090221070314041209210506060a150302070303021b011b02030f091017010303030209031b1309060f0e0708060c03040b1b070b0a0f0b100909050406020c 72
    0x100c90007a031204c1c00c005012448842d0310318010f4010010305d440c0042944454003400c0760305501a07040812510311401d011811216030300da0794054203078082941000c0c008030b90000000c003074280c000e00c21144035883d00c90810840003114401e046254018098041900d4040d801404070180a801d006080103c1913800014030000810080e010740d41d980801c0e0001e0b100141400c81d0014503200841c04c1406802900c403651080101082c400d00340a410301030218481c1e19418180012940c0341089541c1d2490041c010750407100099110340500c9085005401c103050720303156020300051407410041101d00b0312f9001020070b048142e0b801707912034000b00480326140c00707034200e00c00341440185296440c0100141c1404000341110050704010410300000c0754250b40d14135002145150004500e00540c40c503012a1700c43c070701000784039140407801c02c000e540d60340d03000c400000018282400150302c07540c1002400d52140c9405030101d80440e2060040c031805502440e8420300c1400010f1034080020803462 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 670060278 1250 670059028 670059037
    0x150901111b01060b041208092b03081501080a02030711070602030409060e0124110a1202060f010b220515032d0a23070203032a0d0c090902 61
    0x14041c2284000c81007041d03400348250303401045100525803c003802c1150b081540765402e103001c0d10582e80031800001c150750310045428250055208030b0203003c1842c80002a0a0f41076005134041419400014060101403900c5400b40c0816920f0301e08950310036044900941000e0003140c00c004000202000040c010880c0b00060721f5242c00450b261817801c0f40c91020380b802a00082560f401010041180c5c18150310080f140c0c0502c0c1e42e802c4038803590500e044400c1c4030114140e00c0c0601c00c0c181c1d084240301405500140181c407541c01d5406984d1a0800411058428841e0001007081001041401e4a030203481032901c418100840b0341c20f070b580e0030002d001e4081e15981ca416500c0c0000502880360480030042c1c504807006a0994800c09220081c0e548080000342386009043d101d120001180c0c0d0a196244040c8281603031034007c50030460384c02503403500f08032010010380c18070041c06001c4c00401c41d094060070240d040c01c5442c02000000c000040c01c00c045100003885080000031450f100d40e0300180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 670061528 1250 670060278 670060297
    0xb040b2d07180e15031c140f1909060206040b0103020108071b05030910092916060b1003020405030c060d14010b0a0f08070503060d02030c03010905060603100e15090111 74
    0x3800a4180480b0300131041410250312803099000b04034a080b001c0c00c0a0f0190004c8580b801d0100602d6820071040da03440c42003110140000c40002461080000c9004900200300803960312080026200c80c000c2c0e035100d01c1950082e0030f5035481c0c001000198403c40100d9403001d03091803d00401020a4405c4440c52042001140c8680004c41d544c8641d05000c00ea8040c1c1003040e10740788007802e29014001c0244072496075040c3c3c0b200e01e00030419015003403140c12142d142d00130140d00c940011143c10180300404002081510a040d01c0e012098058400d0080c0e4043e50b00040142c01002c40f40b50400c1801d80c81130200201050b180d0800c0c14103030090701c0740c15000382a46c000040d80c591314608011701025900302c1401c1400b10a0041c0b0844551110980c0e600000503600038040c481c090001034904007030009000d500d58240b0f20a0f0080081c0801c0e8107004e001e040e400c9075000540c1110400070344601000780410750380030903078000c00017440443e029017001400d0000110107490b001804031507444110345 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 670062778 1250 670061528 670061549
    0x9040905030f0f18151902010b1e03070609051302070218040507030c060302190e03121603140f03190b03010c21110d0e190b040b2d0718 60
    0xb40c030315106019000400d0090445203481c0c3d10104c404252174a0181402440c5240f041401c0703a1b001358000d5015000b80100141019100a0003160070300d403107445c10800601a01440c07000040140c0a40300081c01d60380e0003000b0f0002103114031074000094010b0038050b41e0040111001d00002c9181064a0b0b01075401180900101811414030310705c054038550100080501c104000301c550b02d50510808150901031803d90070450f02d00001074500407484105182030f1030009414045410000e41200d900b6100340c580c4107d45e04c1000103688940210301d2405807101c0c041000454020801e001201014514000010110300300408a030845840840703403c00700d680417241c025020901c1c2c1c21410501c0ba011070a1018207030100c4d185040380112410380b26090384480e40351507004001d01104901020306003d0a603800701e0307400c00058001c0241c3e804c0c0c8142c441000820001090600120100d0b10081c86d49052070842c110340f0b0310040130007800407080020f03000100a080300480c100400400300740c5070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 670064028 1250 670062778 670062787
    0x21090306010b030403120c020f120c070b12010324050f0a050c0304020d0b1003150203041e030207051e03030307020a0309050d030c060207081204060c081005010509040905030f0f 78
    0x281440c080303060300700d0710032040240700300070020740e002c618000300d16416000481c1c031030441c2c0400d074542a03c00c04c2901650060302030b4180c1c2c082040c005000c444007840112014182d86240400c41031140e24001c800e011081d90050001c1240d0441e0316030b202c3c09a2130710038002c1e5003a007050030849000350380d607810780c008101c28068201020300480da0040d1a0802c02851350406500049031440805002007801c8c0c00e09000a03450312110b19000c0007181c01206440606514800401c02580700300c400310307903500214030070350f92807038581c0940c00c1d1480d03144d0003c01085040c070040050341420a580810440400000710245e40c50901c09036015507074a40040c581c6002d0340c600540905e45640159000e02c480c08001c3c00880d500150408056420880040e690b05e02c078101600c00e0301c00c9414140c0c1d401e5412050001300407042e81b100580c001c09c2c1e510702c0617039214049101056812031169a00040d0207009000c404d02d4981c1c0020402e42c490012240381c08442c0c44c00708041d07017050700ca818000c030001c603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 670065278 1250 670064028 670064047
    0x211e0306030302150915090c0a080106031e0309060503060d1a1e160c110a03051c050f03060613051518180412021906020a020d11030406050c21 63
    0x542040f108003212403261905e0003018241e950610b40800d03460368003064011a005c02d03010b01100c95880c80140496140640301c5a0440c081d044610044407402070780425551485450200400c071554503030f40e118400d170b00d030500846042e00082c105592244da100d10140021383d21a6124103203e01c000d0b4812500d00e443e0842c884111043c141c4070b0b10804014040201c00c0c1540801e01c0b0000c1041c0c10b1004030040310b410b0030320219140c0309001e9005003030340300040103100c0001440508404000081d01200c107a5442c00c070380c903015143c1502c0c840c1d4028000b0900c103141c19406007208030844080d82e00c003255118002580181e21684500c8546030000c0c440c100074081007942080d0f44804d0f500101303003415400110089010060001d13119072000326106c0c078064402d02c07442860041030403454887d100786007841da0080d030280d00c58401500c0f415400101241c01403403404840c548002c09117042c18901a000d41d01c6a200c0300d0713441ca0354041e00031034850049204d00d048502c1030441002946902c0c881 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 670066528 1250 670065278 670065283
    0x150519050418051f0b09100905102001020405010c030804051524030a02030a0209090316050102120901050702070306020307030b0901030c0515120a020d02040b1801030b0d211e0306030302 82
    0x704c060600181100380240720004c480c10072074441d1242a0b420040103c14420102c0743d071b8800c1e8200d60b6104c040c0e280e0070300d21598013002c50300400100c04191416280320354201d9080b03100c0c1e80304041c045000040c4000100c0d002c1c0d80d02c0360b8014000e8003524100c41d050190708529000440f42e4050b103142c6c0c240c0c0c0c0b00b10b082d1801c2d1086029681500100b42500d45a000640e0750880328000070b11a0030000001406082c050090f20051100c90030000314404a503d00f03c0d000c0c1d0445013400a03460721040004070143c0050151601496039034001e000c2403170071a00d8403030103948000c0030b5000b456190249100940c4403107550600840c0188007a0079500c0c1007030108203201708510302c160701130310042c0144180201c0c0c840316076030000300d40400140d84c2d0300c000942002030301640d406010f00c0c0034041a5010391080e1281e0f801c40c460300981e010001c80002d00104020352600d0f85026101c18a49803200501d041806289001d113459404c2415130244075042d402c60000310a400303000001d80303c0c032041003010b404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 670067778 1250 670066528 670066561
    0xf0a020d080108010c091202010302090a0b04050f0f060a11030408070305030310080127021c08030604050106020d2f0d11100902060d020a0309140a0c15051905041805 73
    0x80324024046055105c0c0b00410040701c5000310b10301c0c07128050b081d05c1168004e5049482041004d00200112350b0f48002d403036074680140c0320b0103024203540410350b0200e1420041c9101e00c80c100030112810401d020504a84104032008904000d2108200204e41c031030007000f00c18015440381000f560360b8079154990310741003104c507800404941e04240181040304565170114045904801c10003408820500028141c600a495218a070310007078502c910a0220740d40007184144000c0d102841a07076a584002c030ba54031002a201c1e400202212580f11281040000d51540e080c10304110030a0040f55a08940c2408240c018120100d1400e0040c003600705c83c140504070320001000c504001c0c902e450b4020070414803800034594102ca6000a600c00f204d80071307070312040c00b65401c800c0300703201007200c01d003010f5403440145c00130380d007807a040100000c80c281c0244c4a0f42c0030b250503a40e410305000300c00d151100500020443d400c02c1c04001d00000c14103040e2541074100e038083c0b008001c00d450520120440d000c241 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 670069028 1250 670067778 670067789
    0x603150209130902010f121b0e010e0102060403020c0f03030c1203041a04030903080d0f0608101113050d021f0f08060d02090c0319090b06090c120a0506060f0a020d0801 74
    0x2c01050b4001350703800000c400041c0c0307040e0030841e95905024808000910f4403003007407240031000c03c030104040c1c6d03845080c2c82d214400a80350300944185001c01a80d45141c1181d0003801a8090856401141001c9502c0c801e440d801034126410a09820072140c2402a11907901072010404002c01c418408514941215500300f054000e1080c01c20f528010602d410702d00020307210b0f02000441c0203016000d0340c043c85c200403003040100030746a2201c142e19152800039014040f40ca0600340802d02d142c50081c1150030941c1c404041c400000c1c070b41001d200c0700e00103018041ea07000050450741c81b40540100254482d84460b41d880007032005d81038001908500010340803d02503102820380d4030050b01c0c1c0b2044181c00201d034083c06a02d03039131a45141d002c0150001003409203142425688010001d02c42e03501e0b4003c00003101c055400c0c0c0d4030524064124010309407101c1c121002078001c105e0320690782d84056004070018041d41e182c20713074000b001e0305240d010b01810700041e23111a402030401c0e80d000c40418090030703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 670070278 1250 670069028 670069031
    0x303040e1b0415081915051311070f0318090203010e0a0501050319060b030a03050414030109232d010501060e01021506030c0a08060708160f080a060315020913 70
    0x1420302c69003a0483c0445581101485055000308420780f006030460f00145025a40178441e11383e848569500c80456407240c0d030300034009101d020500c1040b500803900040c0390180302c83d0801400e47c4a0303d52104219100340c05004a2001500503c181c0011540142c8408140580e49524141c40d024070540024000030030703985040d005003d181c2c0e010600e00c8030180401a071303540503006414542d008000034591590306114090100c3c0c05c254002c000f0300b0031a80455650585102900141401e840421034010070f0703c0040310040321100c000c900e03120a0601c0740740458a01e15241c020480d0010407104a80c241e4a2030000c005400c49001d00400e800740c401440c143e070755014079600103035030341344440310100507581c808000a0007a24104013844000d00002d00c42c2d85410341c1c52000b0350321040152840400110302500250200341b0b82c01100c0b5000a250765901005000c04030700b180d001d03a015041d075500b5904c40e00000701040c2c0306440106082c0c1c08031001a6241c201348100039800d5050f10641600e00d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 670071528 1250 670070278 670070287
    0x806150f0c0f010b10030b03072d0f06021903030b09040609151a0f01030207020402070602030709140303030117160905091b03060a020a0c0b010603150506070c0504020d0b0303040e1b 80
    0x90b101c03840d05c4021426241008113201d46070703000082c10405550883d07001044031074060501416064000ca08007114804d1302c0320300548418004294420030b00400016030300c5894100686105100604251400307450f001490400700d5001500d41403003544c064405540350740b030140602440401034008940b01c10820454000c2c140c0369080f51400004010f88138111301455415181d0103a0115174030309a000303208664451080c03900c078000b504103698550001d00c0c503d5021a0031500042141d0b01108018000c504507071070700194410450f5919802d414034051610030703142941c081c84929003d8800480049120f151540a0502e0803500410b500d099951101d001000b544010451540010107601301503030390303984070344165414100030100030186081c14000040c541d030b043e40300d42480301c411820b10200075075440400405005039940680894102c25040005241540c0103141540740c0250106184241d90000781c103640080d400000710108400030844040d0108420300303410707910100144d080 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 670072778 1250 670071528 670071551
    0x3050d14090907030f0f02030f01031202030f0f031b0a02071a131404110d0f0f0219200a0c05030706031509090206040312020309010e09160806150f0c0f01 68
    0x2c03040b000e0458414950380d50403139190070006402400c006031134407105640c1e0b03040c0542d14000422003403000361501034903410815040d51010003212440035000340b03100d09042c0080c200841903071001c0c041c00d2074624148403003441e11403108013406180001d60080c05c1c5840c5001e941c0400c25201107100e0349040d00400410301640c1404503464161200704c207045003035102510128004010040200000c100b01240084c1c000001b80c12071608013031041400d101504045000d00140d01801c41e0207000000e6070344400402604c2001e4080d00c0c0111640c49032550000982d005061640100d0161611020b46506200e07606041050b0001081146020091a0658510a403100d0454010f5144480c0c44202c69001d5554802c10346003d142c000c201400c4602c40418040c0d600c1e80211485c80c04620206001c00b082e00d00650710038810540ca03142440441110f80d012100c116000301000c0e404405420070319160303e0714102605417070101c1004c0d5940c9446031a051031501c202c803a0b0802c0c4580c1440c207078851 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 670074028 1250 670072778 670072789
    0x1a0105010516150501030c0f050306010513330f05150301060f0c0c15172a0f03042312040b0306030c031002041e0f03230703050d1409 59
    0x1c0b90981d0302602c82403019186484241c030016002040309190034880080148001b4103282c0d411100f5104804900d01d5890090545441b0244565580401410185030500c9003517004445c0d00603500c3c69905000401d920044564452102c24000151020405000b1817480301c2e0120082e0104507030401c1846e50300c1c02804043d110501a20041244039200c60503040d00030700005486645c0070351142030031604c403154000103000c000d607000c0000f10300317083e40d020001d50300700814006d400300007032110600410020700380380484d110f600001842d02080070741040c031405c0010710701843c0304101d541e0b805400700300340c0d040701c007904500b8400f950044000100c0c2c0e000c1c400102c500301e8400040031912995000002400c0c03446d06603903682c060162102c0806400316650061040d43d040303c902020740701b4802d90401400c6c5440c083c0b00d8075000b5080f0280045034210790310500810510780c0100701c60060088403420944207a2084075941c1c00140d81c0b03a082604032013001c2211100400290401c10794000168 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 670075278 1250 670074028 670074037
    0xf0604080a0807170a031509021309050c0d09110102071703071113020c060f0a0606170a0207020315060102060a140411040f1127010504030b06060d09030c1a01050105 73
    0x30821880000d07030701d00301309601e84c81d0341500700070396030140c0c58210302c850140c090829080282400c6001c1031000c55134a1851098807003840700d1544100e0714034203000d404002800041c2001a08201c18028100c002e405409070380515413040032101c2f04554038900185c81c04005800c905041c0700240d0089810440010541c3d54940d001a074084c96041d01c10301158070000c01c00c1039840038500018031081000400180140030300d00360700140400e0381d41c0e0886041115000d010746000950001c2d40d90322284081850290483c41c101c1d4010300c0d10502d40d00280c034128800c11341084025000c3e082014071740c1c05003c46988505102c00900c40840d6210500c00d07080c81c000c00041c0640e4003000d00f55503588560340255071031200954104903007500300203c24035170b130000b40b5210b040244282da090035070381c01d00c0c1c1e000c80c5420040c3c488a0603e0304640d180701001b00c004245a81000050010601c4405180900840c031402502d0b01c0705070200d641080f40500c91241c18078200b003948400108481d90780001100d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 670076528 1250 670075278 670075283
    0xf060b010509090c1e0c06160e0d080c070503010c0f09090b0d02043b06092b0c060f050106030e0c1014090a0b0406260a0b1c0309050f0604080a 63
    0x3550760001d0318004414444042c0b040c17031041000314107214840780004115001c0c4802900850b2a10615079044400845000e50075030403014100240c800580400042c10000c00150141c5556503210b00200e0b003121100a456400240d1882c10040c0c0c8981242d5a070f800b418044806020310b11100001c40d4240e081c10740000d0243d950707000502d049a015011140c40b84d101040e00300c81c0c10b50305448003a10008602000c2140d4000d42e008a00103a00005082681e10241001d20103405060008648840440085242800b0104070050700040b2188640c401c1990180d07400203032541406401004c8421040002c0070a03804683d40aa10369550000d40c0f100180901c0c240e0841000201e680c241d034002d050b0141d402c41940f21000c5001c41c060f20251082d107802c3c0e528800350f801c4c51f1031449041003445003102600d0403400081030000280d0b4200584143c400350000c0841d85102c0203100b0ba0204200040d000651100c3c420300403440d001070f8161400c00103c40c440e017440c2c10303c00c04540303503850401300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 670077778 1250 670076528 670076551
    0x703021c0303020702090a06082a09040c1a0d0e0c030a0803060d0204050a0501170a0b0c090a030803251412100e0f0402010305060a240207050a030f060b01050909 71
    0x4240070036200390115040d03158094007250444c10851404000346c80a401600f02d240141d6210320801294950304000911341c43c40710074140e240200911103040d0003d0000c3e90110000e40c07000c030b0b86481e0420402c503820040780c03150f03076101d032101d1a0804546200741001602d40280d040348156a90000c0c06c103815642064002e50340fa2221000180404803007100290024180750030000c00c0c120560040d4125243c2101c6c03a40044130030010543c0341c4a00076801840140901d0100d41c0e50035a002c090040d03420b01400d5050700c00d8407a211a512600101c0394107001e503041500c1d180c040c0303904d01d240100e150f0541c2007000c800103019200c40762500400e07002004404841d00043c01440c05d43c00324100416154000402c1801d011001d012018400c0b42c040e4082414040480c02908056a451040b102084d0740010b0301c031000451100340040641e541c030300b1807103083c03804542613550782080030040d03100b1051040100b00074940202903030002c00400d81031050502034900d0a84548091540c011020f110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 670079028 1250 670077778 670077829
    0x30412141516181505070b0c04030f0b0c0d09140f010204080c040e15010b13050a0b0301030204050a09050d050405031005130311100504080c0118020f0d0204090206030702011508070302 81
    0x1c04840040d540b2100581c103451544030510703900840289030b4203020310f5107007d0540d98090f0b490343c0c509c81e5200042ca0224124018404180440085030300407864803000303890004016000020f50304590b0055075120b8040c001c103100d41004003e00200680d0800081d8242481e03d440d540c1c0715458030301078500982e141c1c419446001010b001052a428400364403180a507182c01490126400800d40203200c4140341e50041681d207040140c003000c4902d0080150714680c03c507400c0c4030140101405841045464030180c000142d024415038001d0052591280d413913a14145c100f501c0d04064070b6a48015a107468140900d01d07010015201003940c06081910b0b0340309452042da0301d040c48804441c480c0c1c034070b4182840100401c00001302209600340c0002e000518200d403049400000c80f0100a5105200d09085e0020f400c2420425a42034001040001c2e000318640203c1c03520f0f80126042001030355900c40300d02d400d1044807030a8002e080b1800041c00303041c0c21903011801e0700c9504040841c05103034610 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 670080278 1250 670079028 670079057
    0x160603180204051006021605060a0c0609050706111002090f0d03021002040905070f051c0e03040b040b09010906080709290724181103030412141516 65
    0x804000425501402c01c2165240908059280e800613021300401070040803140d0450f101ca41d22100c0548400400c02854a6000750041d600207000c3c0c007080361415219000000443d000f41b00314002401c658031640d6102039007200090078030503024418003030948180480107c548825000ea030044034196510b0507080660b04082c0e2419406114a103c0d40e400040e000c0f40030480c94101d68050300190710b81000840300c011042d0780754050000c40255000b058407040c21703c041950400940c040002045d2450039864213403400541c0c2c0941c0004030b00e4000000d100708a540d00162031001440345140c510058207000c04010051442c622170100c1800d41004803242020062a0340f180c508841d5151039544d815a00d030005400e805038801d841c1100034a19018040b0b45035001c2c41209940110040b44004040e0703648001e045a5500301d560984428000441e0042418250034a910f010302200c07903081803a09607180c94480180d00d01000203075103200340b02e110309100d0140b86002005050200d1b000101d103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 670081528 1250 670080278 670080311
    0xe0c090402010314011d010e04050316021309050a1106030903031902040504060e0405101806180b24060909070309030e0307060504060212040f050118031a09010b03160603 75
    0x182c0b0b4100007081ca907000042c0701b142c03403014140c0340c5916451600d60b0783e9862610f840d1402c0b0880f0050314036013080000150f80f8151080016005100030b00091400705101d079118111440200b080781c065104001180038800100d4a80750a003804880d2a441d601d00002c1c4940c40f0300000e8180312646181412003616124103406580c0a024003a0040003820381e00d8800c41005039050f10f05454502810010a0035241a4055040c03900c4142e5084a0260303450340d0340300700601d0034940d04101048403049840c0041d050141071800b850f2000300c0c0080103200c0c0d4000d000c0400350111101e2051500700a4442a503d07100c0c411980f008550030000340d0000241000c1d80c0610302507503140d506020315040421115000000307001034401550071a40d061011300c906848510441c0501110360030740c001c0800540d84141b9012860901c44100c0340e4801c2d81c0c036a02d00d031103504403e103000e50b210484802c020081000340b0074103803405011001412040d45196840c04c03400214040c010800d0740383e170000031103041da0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 670082778 1250 670081528 670081541
    0xa050f0405030109080d0f06081b01110d08071403150f0f0d24060b07081c050112020112051005121504110f060304050d03150b0c010f06090e0c0904020103 68
    0x94000c0c402c80c807141c9048200ba80c0f144410044c0c007031600030b1f0000070f2100c5100d03200540341003100030b000d07141c1003004102e20541d10b5411203040011400380c488a4440a11025400e01c0c2151034401050520250203454109008491000c1c071405208001c00c0c103108030a0441500c209561260440b2100c00c0171a0030600714003601900030038424108070400510301100400b4400710441d07081030303406010400048d07690620507903280ca18203100076804900a900104080002d40001c1d0f00c0341240000c3c01020350354242d2041911200340c04040041d540c0024064620441c0030b0340820140c44c00321911300f9a40c25034018070f4042da616002100d150401044000f06040520b40800340901d000d02c2c2c4000c0d0704049518550081c10000200542800e100c8140c0e4000c99001d0041c00120025060490041c19112414090700e1288200054242078000c0104140e980407400410310300043c111000588120340c0c40b1410bd1792400d50f440328009004070301c14560b480221618032403a1147d0004030302520700e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 670084028 1250 670082778 670082789
    0x70c1a0d0212060a080f101109212407030e010b0303070f12080402010206070e030a0b1e160f14120c03040b0c09130507120606090501091a0a050f04 65
    0x4000386080c9400e030118020351085400b01d0300e11a121351142c2c5501d41b0313240146151030701c0d0f900c030100d141da8072401500010522201d10b40560b060641a034002981c503450391200c0034050040c0091900000424840520407101c00c91904144c107042182c00d060101c0d000302064200f5a40380702034041c103042900b240b075052600804032900c984441c2000d40f6000c207100822960034480d580c0101506009558491045405030040d04455550050540340003880341c9950b90305000d40b550080c0003c041082d001e0141c241107800d403c2d140302c503100c0030000f41b13000b4010b699200d00304002c075980194400c0707403241c00c4c030240d00e00001e01804004044e0000d0050f003580c07002c1564008100170030006910090b6120303d004401101d4551180719141117544036400c0703665000300a04281410244181d081036801841604e08000e02c400c2c4541d40e48121645030300408001403000004008545c1d00440c254054400e000d446d810140b00524185214850856a05c0c00c0c0000400d94841d500c00c2c04040e18002d05 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 670085278 1250 670084028 670084031
    0x6010f0309170c15091504140304090902100804051011120a09021914090915100f050f03100e1f150b090f1c021810050105070c1a0d 58
    0x401d000c074565031600b24203110f45581c410381503c0c03d40f01e582452140d0244422002401c2a04020204050f10751070050094424401c4034120020007841040148003c004410b00003d80d400b00740704111159005148150030002c1c3c0a091101095001c110b00442120040001a044480400b40522030080443c00e00041a000d020404507959030380100d80d0b114800c481a40106003000c1940d031010101d400b54040700c400d84041e550a50800404041c1c00c03c02402c111000880c840d1903401522100300c90983c1c1c103e43d480802c203c140d01c14408030010701000c50305203071100c40c1031020a0380d900d0003000c019407158944445410089052022142081c0d00840810f4030040c0100c441c00079191804103042c0c10784000100195960300c420545411036402850107525030b003850208010001a24906000c105001c004540180c0d03e04645210009844040300d01c01c0c601692619040d0311107901460500c0820002e21002801d100321441c296001d0a0a02c00443c00d442c403100c2d1103010f1181003d4115 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 670086528 1250 670085278 670085303
    0x112180b100807060f03020d0b04020d090507170a1b05090403020d0807030c05181c0b0f0619031202120414130b0d0204020706020f13080607030b0906010f0309 70
    0x4030300e8400e8070a0705000074031480a55100e40660b41c418080c415040021340254501d03442030700c07a0300100404945000c0101c1c0031503045000400320b1b0300c40c55040d030b19030b5600c8107110b0401c4418007400700144440c44c0e84903c01c1c0d04980b0301985498800e94010840d00c022140e1039248038100100c10040c11000d00302450710b01e09864080d42e0f8005070b142c03a9010603030351800511211300c80e00a030b1883d00201e5a500303040c0040b078006a8000c1c902c10000070340c0030380d940c41c2003a07403901a10130340e54995020308510305040c205109040c05003c0c0c050071260007404003a11003404500a1303a2800110b03a4844502d00c000812500f040b0709040703481c0e5000c2d003140000200040c007408501244072103484129242021091596212000c4905404001c1e404c1a884003c2c0320151509501801d0440d008a40141c54040030007101105503201d00ba40342130901060809200010381041081c0e031040050601f081503d071501300162a201e0010521410400000c590300143d5100381c014802003588814440e654 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 670087778 1250 670086528 670086533
    0x6030507060f08010e010f030209040515070e01080138070807082a120a09240807030203040203070504020904150303110f010603110d02060f0408070501031a0a05011218 74
    0x7890707803034210704001502d07080000c1840d111010905040b644140b0307070b5187d05850360b8248043d990006005231000d00403040b981d41002c210206d52403161165036211071041070300c00000b404004068000da00d0300c0079900b0b91105883c403400b600e80c4031110304d07079800000902c1c04500c10007030b8851040300401920380804c8080c10003105002030030030f00c80c1e078910b0007148143c086281405a2342003460008158000c0103400801034112000740300c210024546403c41036104c8980204880c9440c80134003600c44040304020009a01c0300f000c1c2d0300180c140c5400e40c51410710b0f4000079668556030041a01c00c9600003418100b80d600c0d98051004000d42e148501140c0c3e0f620f040c007529284180c00850b0340343c0540240b00780c04880c1803241109881d0f200344407400d0340d040b41d024000c605490103000c80c1c20020400100c40350040c075101a1000f00200001408603500300790006040d00c0c8000781c0303130801040300108062540d46584c5041d0507140300f031070086a44c14800d02108081c1c030884010310100c0054110030801d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 670089028 1250 670087778 670087787
    0x602070606030b070503061f0c0c0e070233060d021c030e01020c030316140604060203190b01021f200c010b012c060d18120f02031b010603050706 64
    0x840340203c094a10540e01c52106a41e1840121000c50740800a402608200000384003842c040007082c0c608640484615541c003224080f680c0c000c2411003050104200809904215201c1d114440c41043c00b494021000d008900e03c83e5a80c12000707441e001c078001102c9440b981c0d14490915002022848110070000070402a08900c550560000b843c0400c0881594000203c240c0d4482d0040c4c025072400c0301d09035200d00d03940c4440d082220404480c1f01414280001001f02c5405580a40c1c0c00594034204500e01481d503407181c0c2d1078191018140320100c03074181c3e00460704c3c83c5003c03106030350780c2182039a0b0030000000b049002c4812403407030121015145183c4004025000d00e00e0070000801c1a14150030065421120b40514403220340745a000c9810244840c0b60302d01000700024100d0b03400c140071480d00030309403450940d42e02a0314030111000d1040c003021342c034a04109102c40c01d2200c12800e00e21f80080d00c0e8402d0706048041d100b9041030781d0701e01000950001c0c008503000420346514603100d150040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 670090278 1250 670089028 670089041
    0x170109020a1403060d02090c0f030403171501052a03040803090405060a0e070c050c210d0810290a020c010809010b06030403141306081603050f1305030706020706 71
    0x80002e0900c0e4081950a081004a0340241001440c0d02004207140c2d08002800b2002803450020010500c03003041085042c9001d540030b03030301c03070f480f404c0602124810092501030010903030b115107030848089040c81c0c1d8000c0308984009483c40c0300500c14040c468552404001e0050b004049032200040c0082c24500101c058800003100300d07001e201a03140c413010004059064010b01c1c104001e10408241c100740507081c0f006005e8407400648056042110018440c08003808021044d0051503000b2a11080c0500480c02c8030105400c040e481402d000612100505d02d034061940304004101031410180380000280400b403280c0c0e16503580da240a400003d4441848a82075400304c0c105a010070704400040c016194502c90251a0506540c0c45440c112046c1801c000e2407005018104007403c00504107100241c040c00b41a00d03000c642d03040068491984e04000108001010700d0101402005a01c081d5201e410111590140d80e8400300f6040142c118442c0c0c442c018031861001440c981040165080749 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 670091528 1250 670090278 670090297
    0xc09040b16030504050d030c0c17120a09111905041a0a05010203160320010504140f0d1b1703010906140105071a09210903070f0f09050717010902 64
    0x9080c00407001c0001e40903200180c500038256004424404241c61080e4854030f07411000e4504595100b4a035162590070a54040d45001d200d140004c030070000183c800350598004600c1c40d02006040030315200d9124403890b0350700c058403501c4181100759407030341000d141c0c0c070113054020000c002e51000700239450310880310048a2401090201400903080d030002c82905e50094010450a10340752466404988c601c42c529400100d48008141200c00f111003446014450382c41030031900324400e24800c4003450402403080c40040b0307030b100c20201d0036000d601c07001c001059800c4200a0304044150b2401c0c41a51a000812002c6450044000688800982c00c040c044541032a030321a48180383c1001192903118440e0b000d80314109403c00c5004450515030b000d9400b174400420340720818080b00d000c0c411211401d019061011011448200c5894103001c07540040c03100700c041a251600d400e4405001004e0361141210384d0303545000003000b150054106a604040c4403a8451480d80c40340041c0d0000d402c0002030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 670092778 1250 670091528 670091551
    0x11030a020f1c02060415110c0105042f1c061b090b04060e1306090f0b040b0616150207050a080c0d090501080a09080c0a14120a0f110c09040b 62
    0xc0c2c41003200030081d02e544090342a400340c01d25a8550322010b11705128445100b80740d503038803189210540d00c6e25014201550407200089514101801c00203940307000b140400b04e03c0d14004130600e40000c3d1030b401e841d005000a46107122039035444e140c070303070004400190064980760801c240407105000003581c1c03420000003612584100f58440749501c40500a6014480100f070007058050000c0c1350803140040c4d50818100d021a00c15154400d58080d94612002c0d0041c4980b1100904810b2405000b1031f40b0350841502c8003030516000c0f1856414614280401920f5407140c1c0210310505a520f404503a0980d07041411070781569060b01d40150700b07600030780e140030103801940104403406219144030412254160344010580d00e54054400040003a014122487c05041011441140041c040310301964003a904101c03a4840452410b420b0602041d040c50f0720358020070056448603040f86040100209a15100314802004264589444954424661720001c0c2c41e0030803042281d5090001d11840070b42c8035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 670094028 1250 670092778 670092793
    0x30a09150207030917190606050109050d0b0402210307030203030109110304021005090d050f0106030c0501020d0f0e0a03061a030d0f08060d11060403050703020406050609130c11030a020f 82
    0xc40004038000e103003008000600a000410250182421000e000c203402420342d801241015004089030440204c102c1c1c040792074040401ca95a080445c0c1c000900c2c0c20795038044000015660b6600c0c440008100904c40d9061040e40c907480c1000303005c0d40c81c40b5800c1c20110381d034030782c02414040d640750000d1207007094543c142990405800342000c2924040d660103040d01d00c0c0740024510130754075900300c0300986401804044040020480030003070b074007503020528000500181581802c1d43c8401260300503c3c1550300c441c01c0c002c0701681c018501c3c0340004d040d282c031f046400520800120b07030110f2940094a92403c188084001c1081500003001c03c120807030407100e4017081140151044154441c124020442c0e110000d40c00b03042032588442094410b4540d81c201e180342a00244850b001074105444541c8001000c0c000c5081c81d11640c406001c044540340c6c10007030b842d400a1024410b800441c00d404d138031481059001c500800084100b108000182d0386c1300c14201200135030f00c21503600109100e06c605503 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 670095278 1250 670094028 670094063
    0xb04050c0a030b070c05010b0604240503070912020d2103051807121103060412110c0f0103020c21070b010b030f0f04140a12080a15120203030d02030a09 67
    0x1020304102d90740802d0643c0c0c69581c02e1800ea5483d2450035007070fa219504d4501d0b4141a6039504000d00150054051008a2100e00080315090701c405d07503140b0701840710404c188802242c100286104803a90021418215942c51021407200c107408100244003410f0003403032810341e4401d500200b07075484c01a9001c12041d900ca181c0080b40c04403065010b20241c01c072002c14004501e00450000c6200d01074a80c950717000481e000420f14284040300c003640c14040b00c07a4640341e8184d20084003880c0e05032071402803648505900001c0e803103503480d03041541450360010b100c480004c802c0c4203030203d50281c030010300c4201c40e40441703420403640721070300c111382c200721100000c29200351040680b40900b03013028140c1942d603034440003003c05000140041d910861901044002101c08001a80700288249845203039210b0b00c02c07020300b030003801410389000e083c203145085400f040501030401c01c480c0c0c112441001013020b0f00220342144240303880c82c3c02c1c081c00001013080e91461504810403480c4500f1540c051081110b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 670096528 1250 670095278 670095289
    0x11060403140606370e0903071208090d080703230901180f03080402060c0d0e0934030608010906150501170c1e07031d06040503060c130308070b04050c 66
    0x500510444d070028114140000c031081d0044030203150381d8490510242c072212075800b4540112100c06695200185039002c021f00c01c481c1c40e00c0d4100a0811700701d1420904080d64035840481070707000c2001150b03030024040c1c034420342015600e003500320022242004003240030403140d00215000b01066003040ca10601440070690400d1101f5044043d55031220907a50b01140d46401c0600140d130300c06024802100d05240522440c4000341d01a01c40e040d503607141c4014013010440041c000440540e02604d03801481072144041540343d514412000b511545080003a4004c00c1c0c0307a00322031100e40c606144503003040000d03401001d00c251041081031296a030380d07004403401302c0c101e580b0321192800c000100f8820300e10400589420b440d00303100c0e001303150740da4203103010f981c0c10002058000403884444566005018030310401c60301c100761911442c00e030a000201e6036440740036000440c07030203000846001c1d04a007000c80340e0280d42d211790f0351543d032071403410141c910a8080d2020345260291400004240c40c2a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 670097778 1250 670096528 670096549
    0x311090d0b04020a060c0c12030905060f22140103051807080f16180905120d0207060e030f071b05030a0c090501050607110616021909050606030408041211060403140606 74
    0x21f0040707d085050101c1401c2c040a0f240084051201c84e4802044a54910300503041c41100890903607254803000103d10304440e100c46044900c03c0031400d00f4000c8144c0d5050710700c034258007070a01182907114080ca042d004007016210f0302040c06506404203685102046400c801c3c1000700496401500442c9460344810062080000c10b02801204e070459a81d0b5400003680e50b401a019242043d40405a44407540d010004070004039500140340c40030401544280320001d500b030780c000c0d41000c882c1e80e2200200e1280080150841003400c03141003030782c60f0301c00345000544000341c140e0304085014645040051014004d0402c0103041c00c00110700c81c14003105455803070350454217400c02c4040d81001e101c15030303000503568004801500000c50141e00c4800c420358103414000007001034070b85441310305412243d02500340c510580e804c0041c032000ca0050300650341501c0131200e003003121109910304500143c11030030301140c00c0b0001080001c20b0018030501d030f101d00740211080d50403d590300c03010000501030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 670099028 1250 670097778 670097783
    0x3070e011106390f071b0501052d0c0d0801090912030e0c031c0e0306010308030a0b030a050111120601081303030f020c120406020706080c0301060311090d0b04020a060c 74
    0x140c20403482c00b2072003d46000165105043e280800400b00c1c001c9800ea5500c5024030480019000511508000c1c401c01c91502180c04801d891400c0f0f4200b50009200c0c0c4500b42001c0c108100b213204000d03c8180c100480d8603185d070055165035650315806a510b440d0202e455000c80410108000001c9001c03540c000c040e9440e902a49821a18402c15402d50041000d10310485152180030401c1817151000c0062403e040601d12099a007414a884002c101204c080c0005001e60056401040041c8115050341c0e004420000c0c081241100100480c3c5001c418010240c100d41c2000d802c84041e000303c000400c1201008942c0e01656518880190764441007a1418600d8035014543e120100c0d10a61000704500c14801001d1314101420200d02e141c8900e00818a50840d8001001c0180b103404010707840007090507040400d402c0c03409810661260105110756020316860300440c09004480004440c480c220062a4a10b00b0203541410490141c2c201e81c224010610508042001400380850040403036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 670100278 1250 670099028 670099051
    0x11d030a090b070c030f030206010510140d02220f030209060a0605031501090503120409061403070e060604030b0411010206150a21050d05030702010609090305071101090b03070e011106 81
    0x203261030742d035080550007198191400c0310046000b0000404180403040818002e40c0284000d5051504112418009030301c48001e0002410114580080c40d44c00d55201e042e44401c01070300c0d1081ca01a0f07041c003074030126800e503400317204143c04940d0401c41c01e80d10056a000707031181186942d5030400d010807104540524404902c0c2800092103911a130107c00141d01c0d01854502115540c07400824985603180e482c030618440c01107010700a1101070300c2100020000325480c0c21300e659541c4c01003a2181243d0180780c811140c5040040e0072901c0b1001210015603114801482d54507160070a07144c0e0000c8a40c031103005010301401304464040c581e40c40c0d60240b9000f01560720145ca030414145001c820341c840032407001d02011410300030807018081c0d4404080b203900c0d030507920b1511b9880242107a825070001d4804038600b40140000c00e6000083d6031019a01000c1841d00c6075003180162403080c0e069000b140c3c00d0500008110301d40750700031841c45c462035007a200c3c8400d0000f101c440f00c0d2100b00c22940341c40c00e207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 670101528 1250 670100278 670100297
    0xd09080610170a02060309011d150612010b1306060206070206150f0a0b030f04051903020a0b063012030411010c0206070503070c0e09031e0c0304080708011d030a 71
    0x141000400e1144082c85441103a000041d03a502045150f04125040d90340e607503588601c400f02024200c1c0141c183c08184004d4404812410188001e02e84040c003403501990002d0101942820f00350f016001e01c3d24010720061610310301d40e89540c00b902c2c25004400043c0074900105840e04e0000685a01800c060010b80c024604d06400b80182c1002040005610400702d200006418004030000c50240848545040f0286401c0c202982f402c41041456142003003405501004698049480707408a1361000f0860050b0b2103810010b0b0b101c0c2e8407240a0341c0301524180d50b22583d130009142c80300c0aa400f0606070380d8050008400d0b0300141c001201e0107000418428207003482507100c0c041e0074034214801891036003001d102e0b855091841c0c001c03820450310910b00f100c040c040381101c071240c203038030010b202e0040d490180d84000c0b21003008074030454032004082c0030510861a0105005940250894004541303d1f01d40c0d40601e41d01a003090380030082c0ea48140d00401442c6000881120340e0708482d03844a40b1403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 670102778 1250 670101528 670101539
    0x806010e040218131e0602040b130f031e0c1520010c12020304030c0807050d090b070f03030b030c130614010f0f1b0b04050102180301051302060c0a0804080d09080610 73
    0x72105d021a1007902c1c40307206460000641c891000d40050300d80b100f095a200c1c40300c20040100401507800c605241120124104005420449c00c548002003414813044918942e00e01140c03859010341102039058150501d08560503404411523021300c046110501040040005182c22101c904205500041d8460341c1c070f41016000c0c0d002990064428684440301c00d40640300c21615401000341207403503130003410003602ca41d540180e41c20302600840501d9454040c150b0b0b00c048090084541c0141455100c1d800c94010359402e001841d15004003603c0401c4ca1111010440020034080c06004140c2c80100c2c04215039501c100d00980c10100d440e11109014410184240d03100f00360b03036600000381300340150284002190450300701e000e980f10390005038840398003280b104507542d0443c1d6282d000ba80340c0000c21000e0141503010201043d0140c488030f98482c6055000c900f03141401c40c028184440000b00000c500c0e00006141100901c581d41c1d0720f200640314056035803030f042e05441105019082c101c00f03014 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 670104028 1250 670102778 670102793
    0x1b0503040503130f03050607080105090a050405100c021015030b0f19020a080103021c0c060e181f0e01061e02010b030601030b060a0801090506040b04020a0806010e04021813 76
    0x10428010350441c3e080c0314824058842c400d18a41008001c0f6035014020010404e0800541ea0081c41c9401c05018a41c144004a012020000c0c0005051900c840100c1e0911034140301074441c1c409281000d01c4920402c880181d510664441b000c0301c00362403d0040aa018000460303641546da10034020021030321109400c442100340641101c000182400400946000c648000c28522150342c035421040c0d1f2560040281600c1c4103000b410308074960150150000305419901c0042c0c640c581010700d00315a550011074000f200c10083c0e004034074004810701c00c51041008842080750b00891981503140e44a4404c090000000e204036401f090044105101d211072407015022a04100e00c000030f61240c9000002e443c180342a0700c150b824401c0082400541d090640740503002d09500f80081c0a440c009660755070b542d000060020303250843c100003240031542e690329800c00401555048803030558640e10b0206e600740080e10109d2082a03190710100b8001203081d4460310034080c0441008404045855601 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 670105278 1250 670104028 670104031
    0x203060c1b1b010309033b01050a090b03090a080414210a02090705072405061009091a06071406070905010f0c0212150a061d0106030e0a060e010e060105041b0503 71
    0x4047c40f2003218070030428080c001247c0c41c051800558603000c603401000d1310681e4128124540c0c10403404001d900507103500f100380031003101c80006900b41d807590348000c61400c02c03244440081640e0000540064080350701d10106081881c200d80344001e410120780300056820610340070341c0f141d400c07106400025280c402c0740c1c1681300000d81080c0e89084419a103905c030000306030821260228021200c0c100100692095552003001528102c2502c42403180c09410380900c0d204060582c3d46562081c5500c903030507104101c03010405001b094480c0300500d8003010998003881002d0683c403c20000078085071140b2494400c5507413386800d4074900c044403046030a040b08002c140d8110607500d00d030b1500483c2c20003030b100c0310105c0c00c803080010741401101c0c10142c4029900c0f2001c050403649a03440d0001c000001281151a0340c140020881b6200c1500760030018030810203410030346032400142c07042d40c040d00910200d8407841c2c00d4691603a03c030b030708020850780c025110743d8841d40241d000c1c860144c091030045 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 670106528 1250 670105278 670105283
    0xc030703091202010e07140d0b0a020904020703020303070e0607120804050a0206031518010803090d0f1509020f12030a050c031e04060f0504140f0d0203060c1b1b010309 74
    0x480c265840c0c1c0c50305215600c0ea881d10b10300507959443c070071460080501c5401d006d03080c0c4c2c098201f6100704403000a604225845005800006008045002007085a0440e01c01d0040584255140c0e80203090194036604101e032204049100e0401d85c811600c1d2140485801c1940090030089001162204460001e0010822a598800d241702480540e0700d0714041c5118000c06915a868451008140b2001c1181a2040001101c103031005100c1040088195810b8400a80b000039a80c14141000103a54003a4000a4101c1c90805030300c0d400580da580001f400d46009503850b0303028120003820300500d56500303910039040d82c10501071901141e109100900c1d044001d0310441c7e040040355002c00c020410071a2110980d00da00080401c012a0040c0c6a001c0c50f0000e4106981444d1030201c02070b60742035040c00381903c80c1e043c3d0581103a40b552118444115103401908603440c0f031a0030311000840341c4c0402c030010b0301200b0100e10505101000109400440e2140c0300704819035000d6030066010f1f0000035803c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 670107778 1250 670106528 670106531
    0xa050d0b04020d0e1b04091a0c0409050103030f2604080f040b0f07030206220210090905070206151e040203060a0b0c150a090302061314070f0512070e0c030703 70
    0x54041a140e10301902e0488907285020304403035840c0409461704c5000c640358a07400b4a007000b0300100070030310001d0100400011410340a03c5640d404d840c83e5110700c1250448495240f03000000b00c141640200810035941aa03121201c012070b003180c94859130103552103031002c050200c00014002a21325409001d004807400c02082c02c00380c451414481b41c3d0040803008a04100100c1d9090905904102a58200b00050070181602407001c2c003410200c031691034064011071000005200301d42c071540702c440c01442040001c00c05801c100708025150342060700e02c0541448207020f041c105182180d001200c5100c0700003800c0384e40b084142132001940005006039400100749400042041c1d0f060700038803c1807138a6002d004070549200b0805030020000e0903281c0300f503203072030b4041f00084d400213082604448002c07800e080c461118501040103400410240485000741000000e007042401e90310416601d0441d1450950f004180d9005c0d9648254070805048100c000042000c05000c2c000554000425160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 670109028 1250 670107778 670107787
    0x81c0b0a0b2b0e0102030603060f09030f0a051201060f11120a080406180b010603061d0705030402191205010e0d0f11012c15010503060601200f06010611030a050d0b0402 74
    0x401821503c118420304420f07500001000013a103030a214456010003e9804092a401c00100c4142c0e28017405081d660003407030020340154a41d0144c003d40300660109034417100e0030368440c140100406100101240890030a40c0d51209104021540124105521404d00c0c02c000448500302c500e040c0141043e999542d80746484455448514172406902e8051030201e0955403500e40d0003811620298400380501c0400d090940e000070002200320b03081001e0b850035607160340742e90000498104107000c1816100e038621100003200c070198404002058040e4008001e0100305c004c2e41e83e02c070940c0c283d2000c00109040c05603402c950080c40310060031030700071000080e140c0c900e2242140109105041c80002d040500000c120140d04019030040050a1803440909501d4000030965842c8003900560502502200c0a41c80d041c58045580700008100b00710740030300404664840c0c94400a02034200040e2030240072030a42100001114004003090761502e1921910314150341c0285030074104258025002c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 670110278 1250 670109028 670109107
    0x14040f050f1f0b04030303020c0712020a0b0315030714150301050306060904080d0e100c020f0607050f0c07140a060c050a083105010e010e010c0f0c03081c0b0a0b 71
    0x3d0142000d54030a03200180d03500111000d032442c2070955481200f255074402c84100050700d4034608207044920f034405068480d110051a281106d46d5030030341a41600c40c94000240f44884190510000c43c0e06031818213003c00c124544c070011348800d016440d0181c0c00b40e0081240c40c207081d00456400f03070184440c1d0b410072902084910548584030f0520b402c035403214010412801e0a4881d1013541050303030000303180c008081d094554903a00010581018010041402c10700c0c0a000070842d20f04241800c190303280c0030b0f16601400c8000b001d103061a405000040c601250140c000e2240001d0385405c0402422500c629a8518181e40c1c041c03c4940e044c1c0d0b80e0000107500500c2803900c081000d190301c83c41941c0c12418030b0001481c202d030100c0d280d810070160881a4403143d80043c3c662840c6a0003c0300224441018201002d41005984c0001c201702000124900b038010307203000120040000034424040003080d031040044407946030003100b00c9007404002881c041e404003e018607030910501c0b00040c032180070303d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 670111528 1250 670110278 670110299
    0x603180c05060a020a08042304020a080a0b120102040b0d050c03010806040f030e0406030807151a15070206030c040e16080a020c150a24210f060614040f050f1f 70
    0x158464040c23160803504050340d0041d00481c01002c070905480440c2014070314207008118250280a82131425514120f8013015212010a07001414040000355903170f9580704684211540300841c600309240c0750901094031668694112412107490100500007034a440c2c40b4580500170000c412000e018203510750f403d054541340580320045010b0713030281d5291031180c240518200301c407031103901c030480c902601c031016085068400f50180070207403269141d041500c0c840003060310940b40041d601c81000302c200b00744541c2a0f8010803d4840c80c2032406401d48655816645400340700c40043c010544540000d40c40002d642c1c0a0000000d2a908840720a40c40903003404e101c072000c2e0381050f111500c0f465103241c40040001400c3d29104010a055611441c0c004801556040050110113000b6803002031000d114418076106000e6400884c1000b0312070741ea81540040354422020315001e981050f200c900c5a504d544622441620141c0c94043d5035912803c41034019a0b070318001d08103000b10408049402c5588 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 670112778 1250 670111528 670111537
    0x1545011503110d02030615030a060e0105040309061d010c0204090b04060c0e0a0b040623191b0309031202010917040f0e0118050c04081005010603180c05060a020a08 72
    0x2140c440c404000e0035030601c1a40c2c140d24408150080b040c1580d040c00503240010300b80d91100f1034013100700b000103c2900103070510f58000070182c8400c2c1024000e480c03d034010f40c0103a014600c240c9a43c0c2d0300541d9001c05440c4d41d4030395000803e40c4038100c540780b026540100b090810161000300005640d01d12640e51154000c0103603016680d0580c1c80c940c5204507504400030b50080182140c1e100c01d800c0c941a9015864400d40c02a4020008040c515088041a4099000c03800b0700c0303500c405071101000780091a1044090481074001002d42c08201000350002c0d03400344130b66815959484000b411030703d800800328042002c0100b1036694001d20000309840800690b001d950071030300280d2341e40c50940d00380c0091480d90890501031414200402c8408104800c02c012134540f0200414941d94850518000380103030340c4524440d0241c507004a102126030703449203050305e40c25103080200c00103003080d00d414561102002859504030381390500851a2980c042c180e40b118500c100c84274040241e60b40d4030347d81c10 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 670114028 1250 670112778 670112801
    0x206070935010207030c020406050406030803040609050c2205010b03060603060111120d020702030106060311030a15170a050d020606181302041103070908010c051b100e154501 77
    0x90106d0803a045103458042e08004150441f420b100c80f90a5483d0303009039100180c002064950341e5456901044001d0002005844004040060f00040348620000d0304050610903404145010f002056404501090f203000e510f0160107a400c542e02c480041d100542c1d05009002e0a03c10400700025800400000b005e01400d6a5005601c4101503c1410b01355030003a00510309250401032882074126461054961004a07a1000b2541e020283e140b190018a079420000b02c4000a0750200f04070040041c0c444540f600c03440031503030281c00c6001c003240c03601010745805034440d01507107440c19a24034048481350030050b0059882e490721601c0c1d0000d01100c12501c003503241a0360100800c2242a0018448001402e41c03100900405860b0003005000344143c0042c900c100d50950b4041226000822850410b00241801009034140b41c0300525034a5081d040c0383c0c060707400d181c00082c16140c0c01d402c05400080580e12640c262007008034070303201440790480c41c0480e0000b0204000030010003d0081c1c51040c01d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 670115278 1250 670114028 670114037
    0x8040c0f08070305010b030f1f0e060a05070809061b0a0516030309051009030e121e0c0312070c061b061404020103051f0303050a02010e0f0d020607093501020703 71
    0x1883c2d85000c030701351429950f503584260802e4103414402180803130901202400d21881255101c42104403200414404114020600c111030800c0001e000952060703008000c642c03103034242943c4100751240c1c1c03042d04803140210f03140314071001c642e1020140003410801c1c4041c00d0007030805549461111030078203200b40503400203445000e102c00303010040c482c0301004521028288408680c9440c040c02da01c00840d031042c01000000c1c40b0807002c03038081c4040343c85d4203070b0421b42076162920480400d69460640704c000b803090007640f01995804800404441000d41d100c0d1203100d0403072074410140c806002d495005044103012940da00b0024000d44a0400c81d0480031003504411304184c00011704441c0020320440e44040c0c80b0050100c08158107104200322a414a0203a640f401c0184080313016007511010541d0602c02c04100e61042d070004504aa0608040e40c00c40b0902e6403800001c0b6002d110781d2042d82e91068010103002c0c40113000c06001d4810320500100760b4100070002104a00b20303401010180c0024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 670116528 1250 670115278 670115293
    0x20102090d0b04060e0304080c0f13140429040b04020102010608060a050703050a020f120703060f1211030129031c0201051506180405100302220c09120308040c0f08 72
    0x105882103030381e04807218001b5401d190510300307020382c1d64080d54059403103068106481d24041d5900c041c1c0c0480604050018441c0e200e104d03515507100c2100f034170304441901c21038400c100c0320303040300d100707454240ca5044982c501515580c803228071584d03000d00203a045540b80d00c070100302034204000a5004022200700000c0301c0c50100e00c001c00315540602480b0307055004010380310072510120152001090408041d45680c0c454020960041c035007644003410328150000c00003604004643c0003014a4021030300f515503ca41c60040600f00c40e101a0090030031010382002d040e90360460210b034074960301d003c2d003116a4401a420071080310307000c0941090041c0c1d1180100503079103050215414903008144c0e4072034288603031003006010b031218420103203002d244d07241c0c0040d82c01c01c0e40d00060300086030080d0803e4070404410000381804a80e54010f02c0c50705003001d188602c0b15101c2c4401c0da00300c49203030520340d290507026501204e02c8080a0015252034400c0300000c2031521080c480600200380c443e0040660 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 670117778 1250 670116528 670116533
    0x30c0601030515090111030106050d200c06060f0a2306120105041a01140a090f0608040210110c1e090109061a0c0304061809020a020a03110102090d02040b01020102090d0b04 76
    0x3c8070010305480782c0b03074103000103541048610015241581c03030508080b0b48506113000600c00810b40c0b84010b2480c2c6002548402002101030010040c0004200030f80780151340d814140201c8029140c0110b0b00700400d62000c11050030751003080e10f40310190b804165032000144000817031640185807002c03852070b82c8900400061809100c2c807070601c00c0070441d40345260111000038100c9000030350b092002c045c0c0020912a4188140014809041c42100ca41c0c0c0c0b0540303462000306054802c0b18100c0c01a50000c80c80c1d000107000d10031606071010400010501c1e0031040e170603c00303040c2c0d001c040814000e81c0341c61840b07103e41c0c80ca0b800d64041e1041d804001419490102e0b4070114103203014211403603c4081140d04003501c8080222416550642440760184401c07144030005540103900c4044064030204012908603804a07228038014020399941c4200d8191035610380c00c0348503984205078403854070702c5240014282500300c01d0701c2140500005040400d880b010a00c0749503100011180c0d41042c1040004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 670119028 1250 670117778 670117813
    0xc0302030f0703090201020a03051b060c040806010b04030c03060c032304030212120604090203030712082a070f080c011409100608120d1e02071211100e030c06010305 73
    0x38400703628602130050181c0c03900040d480354000d6802804100e4005501d20b004500c010f01ea11051903102c00b01c590516180302000b0444d00240590703009401210000600340307010704252401e50380c001301150035181c5555078440040c5003105001040c1500c3d000f0158841585801119030590f020301400d0346450a450000c0c109006005107040c20001403003c546500307461025203034070040548000480b141d8034000a0300d540680040105080c0d201c5201102c00c0340e0012106000e02c000c00a80e510b000c0003003030603240c030501c0e41300420b003143d0052280c8008640240e00106849000301e1402e440c00210000090941c0c04044c03601a000e50043c0510030442c03c204001c0120400030b0f0810002c141c204201c541c1c0300c11101a802840e500081044010309005a100b400c03803030b02d071110100554040155078400b9421005040c0c426050070010540843e000d03001001a01002c00042c00b00c4c0b507000300a1f0401132400c2e04950010388020300c40401c3c82602088202d0107980103800921030106204800d92 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 670120278 1250 670119028 670119031
    0xa140c0c0114011d040203070b0c1006050d03120b0109080d0f12050402030c090403021911010f0305010f05060d0e03041d01090b0108040b06010c0b0106081008120405040c09090c0302030f 82
    0x210030241c0e1004001000c2c0501392a840002c242c524a185030b2a240006850010141c000503101c030400903c041540c0e2000819009175100000c0c2401261342d54400c00c20645415400038000c41c48501c40d0316032840c5143d004000c01601410414942601c41c1c0080307181070014000a03001c120190200440f8580250000c0c40c5c240b4441d20620851402e5408031b900c901d6005207040c02047c0201c04a010940248184901e542d4540c03003040314103015003000c0c6000c1c4540300d01d032070100c1c0c001100807003818424041c842c1a40c00b404190346001c0c2c9804140651584031010070600d15940d0100300030802da040c00200000d04503020f0804031604213070394256140506920003041c01d46022100f031000e03604029460341c40307a005400a90217540c0d280050360040042140201084103800c0042030160300009511b008003c000600e00e0341940300c030b00142e41c85003142000744c29200d05000c204114542600154000c60403481d10142d0f541e910b41890003522100c001820100c1e4010080280d0704d910142d55030b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 670121528 1250 670120278 670120301
    0xa0e07050604061b140313050d03020c01080712050114031c020d0804140d0210050702070f17071503050a0b0103060315050402041d01020c0c03070605040902030a140c0c01 75
    0x52005034a0040040d140e03100390722400082c029154a0f00100b08003084044258a42000c0d01030541001c2c1500e40d500c3e64054204484882c12042c0081200c1c20000c034007086143d0300d90010541400c56800540d40944020080340c200010429840720040150180318020910ba40d0a0003540b005c2c0c2c004c05082114500c504410400c100c04048045c0d6400202c1d904c00c0ca80900741409940c0708c6007050f00b06d40d03980c10510240c501c41e070308502c60384c2c0c2d42c00903040c203c00314000c204020680700c4090490f02c8108511810b001d01c91080814801486a000355141010840d405c071520307182c1c1c07541e208001e0906407c280c2d0129a6420030880780c04070902607010000c00920782000040c1c15a43c89140700d18181e0136001045036940001402c5445540c806441480d050031031b10103465944940a0203503221404280d40ca0041015804140c100040c005040d21625124281031a040036400e0000350801844c5c840403035100d44030054050801c0d1003a03801104140001c40d903a107805682207080d54400c030b801 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 670122778 1250 670121528 670121533
    0x10090305070b0309060406020d02040f1205060a110409050c090909150601020d0f0c020d020405010b090a12030e0603041533080c010f051306030203011701020306010c060e1609050a0e 80
    0x400c43c0f13a201c0402c0595106d64030000c01603c40740c0100301e4800071300942d00310000f0700e08103410204040f04003c4115420b035120340100e81c220b81d1440c02c3e00e01a02e04410841d100510248014402e160703091700181c1c0e1020b08110800c1c144100800002d04500d0306980d20b10090f040100403503d0f0024980b030a580c84882800146030009112000030322007801b00815030104010b69030400d0441d901c5000d0003484580003402400196111140d020240d48050780c03543c8505000040000c1c401158542c4c0c00e50580c154075603205040344c900512440c2e5200070f00480d0382401c5504105454003d0b4030a02c54403200840703440c2c20121501c0007000310910b04c640071413008043e545041147c9400001e070760414641c00c0c0303004820310008e440243e03024020f44464550502492002145043e4103502660495a011458080b54905046114201e101c01d450744c9000a00c50041100411020341001e1100c103001307001c41e24441290b81010440d01920f8000301d00c1e054035001401a280c1d114001c0c4242c00185501 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 670124028 1250 670122778 670122781
    0x6070606180903080609180708030c0c01031e0203040201050f07150e16060e01050409020415180e01060c0804091e15050619050c06040606060906320910090305070b03 73
    0x10f003d481388800900c0c03140f041c60a48006141ca0040b100045440b4403010300711340003180c99010850300c98108031040011846038440490749903220b80159840313020030105034400380401151120195000802c00e070f0606c2420828040d1000c10300000304141405074801700096000c035840c4501ba682d446116282030b921001d040c40c045002c1c02c000b201290074900707244580d03a60010040e51075000e637034092060f06201043c0000e528501100c1c09402004950f640b02a04040440ca1001c00d001da0240b0b0411100e0750303005002503401020902d110318050700700d25041640d50342059050b01ca085500e401c20620603200d036000000c85005031401c1d04c000c0d00744843c8141c100408903101e4001c41a01035043c0b560107100312402c5029030200c48160015100341e43c014a003a05059001d82403030b2050000207242d9090000c0d20511982d05440740031a58600411902c04807a10b42e071201c40004030844000c03004000300c203800d9032490561506020700d03840e50340c200b41c42c2d81000d0b41444c681d80d0058826110400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 670125278 1250 670124028 670124033
    0x7061503050c040f0f0911091e0c030705070b0c0909060307180b0d122606060d0207050f032116050715230a1506020723060706061809 59
    0x142ca62110801503c0002e0340c00b45003292007024000441c08982c2145c64070668000b48004034500c0c5180100942d0303220b01c99201e548006c180d482490005a04400040380070500544031180215044a158130300542020f0468561100f070f00c5007070f24420180d10380010078000c181802c1070102d6000c1000c401500b02c1d186401c240000c07280b2010144001c20780d4481d020781d45552180614601682c019444d921480b034817040182c0304000740490b50320b0b00020031108540c90894260034900ca080007404003820030418401a1000e0340240b00c0488441c010484284422001040500070013061002807000890900c03204507170320f400107010b03414444c03e2b4580d040c00f07894011040b500300320f610441c48051481a05902c134020102604145c044130800040c8072007808000310200e0140000c00310800400340c0c400d0140c45080158425140903800550b010012100c1840c0201c4005074030505003c80c551704034001440540c4111011a074607603403140c00b80551400320003242668204204108035407010354 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 670126528 1250 670125278 670125283
    0x10b0a030b180a090303020403320c010e0d020d151d01060f030305030414010c031406030c0108011a30010503030708091c0f0b060102120715050c19050706150305 71
    0x9003090b001d1134030340c81c1d903d0805110354110340003143c100d15034108600c041c0c1d14003004821202e8000050181407070301242e001e10081025115214140c4070180d12698003000c2c0b1204000000e8142d91004040342e205001c640c1900c0030964546203503500040c0050041203140401005840030b518580c03509105104104152030740300140c9416013001030f1a661107141000364405108100741c19542000c07036881115400d90030084440038485801059652a42d09050b03480c8a407440340c074000f84208004024904400c500110135041d0910751524241e903040d084414409500d000300c0921903103940b810082c4d00820921409003008902039071400d81c0341d44401042c1d008003050648610103840380119040001e01000c1900c43d40f00c1003503810300c0803074140110362500844903640036014000e800340300c9550381c07400c03240842e5004642c0d242d40205959404001c00c4000c004948051040107030342e8541e00360115503225590299101980d45c2a2840c0c40300503220440c065111380341d4140000d10004101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 670127778 1250 670126528 670126531
    0x1b0827060613061208031b0901020d180f14090f0108030a050a050d051e060319030507050c0a0b0703020708060709120c030212070e0f04020d0f0c0e010b0a030b18 71
    0x200c41070000c10107642c0c107a4004180a030b0104d0b0485007100c00c20010000d0f000055441748000e1b200c40320b0f08611901ca440c604d44900440140180c001090b400e0610b0700034240721100c9100c640540c50215190b10b0310300c0720120070b41c010705101014000c00840c81e1038a0703924036901550079101c840182d4541902c6507600d000e40301c64031041c45400702d00303621028881e9080e038001141a02013440282402c4c007243c410410110641c2e02c22a02c28400182d980c01d000502030072403100b01c07039080c042010030346089806801003981118203002c1c4041c41030036552407c114102601e00b01e103040340e40301094070b0080c0c0340100a034410680750b080304c4200142c1c29003220051003200c0c5451180d071100802464005940005908001e601032416001540708510014104060382c80b071a0305003945469844c40f0a00429045030000d41c0000740c5000040002c2c031441c082094184500809840541c0303510301d00308207013000d03001044d16078030215070307a500c055040c001c000e0060000c0c0c4422804115808000160140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 670129028 1250 670127778 670127791
    0xc0623060d0528050706050421030f0e0a09050a05060306070c03080402040e100c0201021b160302120a0602030f040c27050601021e03030f07170112061b082706 70
    0x161920f031202d2a0710148110301c4640e808002e071001c00c4c4c3c481c04042e0103900700e03020b00d24440a098445252403030880009510b0250551110000b500240408440b49030a000401c3d07084043c41c80c00240360b081600401d40903401c0c041011603070b03240a2041c0b5240103402031400f0204003511302c40c03202098100100d10f802503011749e0080b0302009801d91a500c1e014072805050022031500c54400902c540c10b601611100c500c5184410f184401031042d260741d9a00f400011504104400d4208014a03154081e154860040703025145510f000351078640803038200700d54100801c0850410401042000ca4030080031307080b601403200d0411a0314003032480c0704005000760f684059480c000300d500350307000b0400b401c1c076200003000030710041d01ca910782281c49403c203440b040040c916035008505200c0c05866051105503001407628403607882c04540611100c80301c0026101d440e5520ba05440c032090f03400c81115503010702e448038107003800e0180c00c160b01800f403000302c4a00d410800101810701c0c6404a22250000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 670130278 1250 670129028 670129063
    0x170c1c2001030902030a1212020903100b1207031401050705030c03071d13060e18120a03023601050910031a0405071d0a03080306010305070c0623060d05 67
    0x40c0e6540c0141e00401c00640042c0d0301d8492000b41008000f508180c80c82003203001d95510303107190748611505060f40100241d4560540042c0004440c80140380d0041c4e4603c40c00400c42d8020320180c410040c1400b0003a00140e03100300a01100b48000c0c0024080c84d60404000c2c50528a1031074901c90515903404080c01900410600848e03200c221404080e441c05d00c100001c00741206503260310000c00042c2854414611450303907210000b0130000208031940c20b08a11704000d0301c2d80d00d41d09203904150358010f10324001459401d004120400004040240c449070382c8010220420391508500074514031115801d5040107000c00031540b080d11660700d145000804c1d410f0104140d0381d02565600080e0485903242d070068504001c01500c01c1d40010610030310000380504904003040d9100b80229546640001742c80d1003401c102089079544250b1115600c80e07100d140080144902c0d9170b8501c140c4a884204051500c4080494081c203204078980c1500040100c0f1b080048444c03c0c3c1d129034407180802a05103100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 670131528 1250 670130278 670130333
    0xe01080f0d270b030a1a040608072601020d09020f04050118090809030a0b04170c0615040e01110415080910020a020a080301121509150f0204170c1c 65
    0x511200c2600945140070f081500ca1a00640060040c40d40161300540d85400b000f0344c01a40c103082c401e80c001d07100d6040143c48507604040105001e03039815058041114250070349155a41001c0c4050b01440001c41c0f004115041719004001c2062a14040d0510032441c0200410407140303400f000d01c040d604001c4011030364520f01d007044041170140f1200c55402d802030540510400001052051103144074040ea00955031054404240601508a1009182e809000840c20703441c15418011030f03140000308080342d00904070100c142515040302859004407404103091201501a207900f610350440d510700000d4510b8628405540d5039110022180910340c00506600c501e80b00b800840402030f007140031580e49507501c0041d0804406003182c1501c0014030b84140a1610b00744d8002c058100c0c4e0080300c8004c2c1021000c4421000701b280c88620003070310740e08000010f1141c00c0b2a504400c0c1c2001680031f0002d000c030f43d105200f1085a003131182d2010441c510090710014070f400e50b60101c520f480c9400b41112 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 670132778 1250 670131528 670131587
    0xb010e130209031e01110406020d08060a080d080f07260406090b0f1603020a08041b09290a030c030b06060f07080315090907031b09060e01080f0d 64
    0x24410300c0c45441d05070242c0004c0803002000180000e80211100b13008000e04d00d41d40c1310f0020540280c1c040c001c0140c00280403540c0191083c08110340101005080c2e100382541c4010051410f10b8005000011a0741c5404000d2404901040154040ea007801e0203020a544940c800059001c8840030880252008020500340800d0350311440c2c180d94080310410550414140901ca04041160800c0c2c01c09241503100b01610f2290007503540448c25078031545500d0f00c4907550180d4039524414550b0350300000c01000207005920340100f222800da5803444e402018001c400c800080b98401034082e004140c207070310400c000380d604241741040320f41065003c1d510713480d514005a21841180d60003c0b150304080743d620107000307154004500410606001e03440c2000c00384180030000c14122411307125a0840001000071800741080c01441030040444c14503241d0b01d43c605503007203c01c80c0d003014400e04410030040c05008020041c08009442400c0204100c0402600c010940740760741205500e16040c48503070805 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 670134028 1250 670132778 670132781
    0x9050a030308090f030a0903050c011d0d020f0312070317060a060f1b0b01051c080306010c020f03070906080706031a010509010509090718050627130509150108010b010e13 75
    0x580c2c0d904031085d41c1e03490341003200085c603500c101e0009403042d0250000410480d070080c001d0100c04142e6810200c0c0c000d07440020000303000f08054003680c00c0748444114141d2641c0a012003059075826042c01038440405080082441d900031030001c4058541c48180441662015007280841d50145441d040102c00003200701ca89c0600c12808440e00c030360788a816000c00c1000031015043c1d442c02e03180018003810551a54a26640c07458024000c008100b000c03400ca0b51040340180740060003d400c080ca104100c07000320b49040352642c00b0050f03040e51564203019480040c04144014001e902d400c0c0581c581105501807518405514075050090000e030102090740950281c9088034401000c1840902d0000c10140200d449c442c0b001084c400c1000010855240c03240c1500c0c000e01c8404540600301d40390400341c1c2950004c5c040b005030321030902c030307400c1e03e14410314050301b032107528084041c1c101040645190b681e0040e060b003003240f141c0d061143c240081e980c40003181041385003c84617680c901100110310310 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 670135278 1250 670134028 670134043
    0x1806050405130825060204230f120c06070609060608061909030e030d030506010f14030f1b03101806050f1003020c070b03041e0b07051c0501060807090609050a03030809 74
    0xb2280002d8031032281808243c1e03014008131515848c080d03c21003094200d030490b042d4110a80e40c0d00c4042d0b21198001402c0c0a0528031110880004031001007094500041580d00040030884413643c8034080c2c13404100c01402184020081d0b44020034640c10010000c080d0b502290318100032a95aa040c0d01050500c01c0d0150000990007406403100c002e401417000b809000112049404a07640c590b011500c0c5100716150400b590404c4c030b208bc25a03e07041000b000d03060020389810150780083d04800381000c1440015801600b10041c45a55907182c1025640c00000203065210614030744041080b540d214054407004008046a1004040e03a8911040c1c0c02801003000700c1030039109004000c02c072440310000560007070b806000c1d0000785208e01c03440e0049040c1022402086422910f01044030903000c0c1010344125904110210b55411841004c0404c07202c0980c0f1000001e44804c0c1800f1a50350071004076400b420b41c038905643c1d054146000f02c0c80740903a83c03000170204808840042c4a01c0014041070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 670136528 1250 670135278 670135327
    0x120309080a02010203091606050f0c010902030304180b061905310503120a050406050c210a0816020303180a0c03050c0a0f0501140703020a0c18060504051308 69
    0x3036454400c1400000d00075081104c045203540b04955200c5c00e020301c80e140c540d044035895030303402e4540054800d00044580180d048042550748600c9014010fa500340040d201802001d810302c8030801410110905480000d0805030240c0000c11180e410303a00400500c84136801c550030716560f91f24a0314803800107481071400328810765440804210300b211107242400c085502c11021101c128000803041d541c01c6c490b1070100d10100b8010001003040a000f1310191501c510071400381e558810044213070f00341c90034148240030a075030400140b80c0000c42d040030318980c112041c2d800301030500403003030390180d941d100103032102110680400403081e400400b0802020501da01a41c0030b00d03032565900d010340d034030000c01c44000d10500450001103010f0300c2003c040004c48405955101f58001d1440822009901c101010380850003000b113024085424100c12800500403a1500c1724000c0348941c01e030301122120b030030152156041c074082c0700350b0080d41b241289030b42d9003214a007550351b0400040d01c81c031a2044010b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 670137778 1250 670136528 670136543
    0x403020d03180f1505090d0308090a1406071b0507060513090615030506120d0c0317130606051504031106120112020a060806030a0b07050904020408070503011a010c120309 75
    0x20400c1d011403440c41080303941c2607130a44202c02001000b80c96a0150090705d0313400165524a04001c288510503141c0c20003406c40a64600514640313455114142030380c480c800346d500940c01d2180060340311034510f009041301d15518040c0300e6183c0d034080c0c450b00309109401c10400f001c210001c11403003164100d0300030049620304208103030340d0fa030321070440c400f64521003c046403510f000500c0a007405900c0f00c1c070b043e401201604000880010035208042001c0080c2d0401003442d00d0080c91b80200300115008401488403114840741901d850026200d10780c0003140070380c4008144204c1c504c140310507102902e40c408642969081600c01051480c02001005131105005c04000609072400380a03c0b2003c3e40283c0e8440903098130340c54140c2d81000c0030307215107070541c1c8a110808086001121283d4008800e07240c024603119004c4005000c0c1c1c2c000da0080e5219030000c1008202d2850b0901c80c1542402d03049141172440000440081d000c03016000c005484848a000854010380c0300e86d2022240d154001c54 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 670139028 1250 670137778 670137827
    0x406080a0605010305071a04090f0b04060305060f101d090c03031207090f061b11030111090102100b0f100203070606030c15110c270a1b140403020d03 66
    0x2081e0303000d07100c02e01c01601c190140000c00f064801200945882051b42040841d1a05141400c89001040002043c0b400030760703224030202c0555590301400380150701400060806040202150301024801b0301080712454020404010b401400c5669007a0840701c2c0c6c4409040340d4910008070b0034000c400d43c1103541400001a420102e004a600e003038003910240c1d40b104241900c07040c2030b142c80380e070f80c1c09408046000d9003c030844c00040c4211020f019403040c000441e81ca00000042800e480c402603005404210101d019a10741d44d04001541814010010900c0b901d140340c07000c64440e1085050784d500031507902c04840f0b0f21a00820440b0319442c0e100f40c0801810f42d4905081c2d69414690080c103200b070500000c0200045c1c86002c2c10f000751030b0540b004d880b540309518100300300003103901200f036210140302038045010724541c1d40140c0700320f03540200461011130180425408102c003c02800622001c82c541400c1c00d00124107503800d6a50607907260039541c0d002d08041e50464901030079507542101529 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 670140278 1250 670139028 670139033
    0x403021c090803030c1e0c0709020901210203060f0a1a090a0b040e0114010512060f12071706060907080403120209041505030106060c030c11010c080a020f0c090f0a0b0406080a 77
    0x4005050b07241060389459024078003900c140300030b4420020340051fa50301c140c1050191034030350f1b07004006100d03050404000c8600003042d400750035030705400c048c0742e00c40d408020000da03800c0c0380040c030f01080c0c2d0841d8a240a1401c0100101d090403211141400600011034030240c55141e44c40c038a0054042e80c1100e5031150768685140040380310900440c084146620300e00c41c090b50044060394028000d400d614116030341e525052000648480c0007159000d07012202e40640000c05004060240001c0c9405103800030840080528026015000c5806401d684003080240c1da4170201c810380241d41480c000c0c000c280c010903e035001e402a00d12240e40a880c040481200040a18600c01203500584c02444403544e00d1500740c480845000707010b0003282200d0080c6000500300d107005015606c05040c00c2d029690741e501e4500003504450a050096484050725421a080401140b45022000c80d15400315190440d02c00d4000c60000d0041290b050703d4034007040d515601c0760000009010701c0f0080303401a50090 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 670141528 1250 670140278 670140301
    0x206040311010909052413060b130806090303040611190e030d03061a070204020712051e0f180a0302060d14060f0d0f05010f09060504060c080403021c09080303 70
    0x90703440602003507000d040080c00075524002e840c8280d05c2d030310001c10042d08543c8900d4050404140665008109809182065003144220009014019403d9469a11003218aa2102c52913005040b19074800301c104058584004103c0764071551000000c100d54031102d40805440c0110b10030f003001e0b445103081e00640140d00060008480e8000c804036003500c00e0043d400e4044038a9030040a0846841c00c20a15036a44100f00810301d891010b0401850000350351603910b03520080c41502070004400081c1c0182d074041c080c0b03101002040e85070103140703010403458490701d05105c1c901d100701d00c1d503003c1e49041c1c295030b440d12211070045030060003481c1d07075101c4408840c0042400391600c031590202e04010030b03290305140d8031100c944180a44031620411568a88140d004001c1c481141c040d9202d48024901c40070901803218070611840003c600c0d800d051804000f0b4413848410300e01081540c90802010a07800a07158102a0b08095032400181110b00200c03041c03030070b0703400a07402e511000080c0800d45000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 670142778 1250 670141528 670141553
    0xf09030b041410060305280b0c04080d0906020c011407050a0b0a06080c060708070c090e0a0b0f1b090d0501020f07030324062109030c02131e09050a02060403 69
    0x2e4010340704040360350310650088501c54003010344542c0c84064243d079a1110081c841c0e0398508103107880005c0c4161991a180c1c035800c11503080b03042e1500031800300f0403c9401c00000840030440c4c100494114100f0394002d40d20455060454108440c0d0100040c025101c0c1089880c0300703070440241c131680390642c10124074000c02502c0300560145003a200099040c0c01094807230320300800402651070800c494441c11030382d40002c2400d41e50292508400603802c2c07408d00c00c0b8001d01c1d40000c0648494100350030084181c41e0020152060703010160100800004250f80802c0881905092140c07201200408075000a040010041c070a45c40002c150041111a10160551a02c641e8040c4440c3d42d01000b61440c0c000403100745140402c42d041c0a102da10b000d4140c921001c0103144548120340640f5034a00300b91100c0305002c3e0040303000414507000790700f0031008400e854101000c0034000b1003154405048031902c00c40f04c0000695944504000b0420240300718009550014001c40e22140c9a05042028880 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 670143884 1106 670142778 670142813
    0x1210050a23010807060806030616020313090f1503030804060c020a080f0703080906011802070f02040504150f1104030f170c0d030e010e0d0f09030b04 66
    0xe5000c009804200c032024103045540f6100d5101d0034040240c1200f0200a8644100481d43d10001201074004121984038030981c1e403c4501241035010710003603c000003008040000704510b2a800001c90624440380810501c950301c40382120641d0548402408201c101c800680410459440980110032030b006951204031203136180c580c182c1c01403082074003094002c034501c0c0070b040d40000c2d400d50201c045030060145504203111415040f00301460049115000100f94003000602c0e0108410342d80c0c003030011700803800d052030003031081d80a41022070856490f046102c039200a4030700440c46a040e01140092401e42075890f800d020b00d2032000141c45e20503120f226104070529080c010424489918041c01540a8070b61004040c2c0704a001c8840c0309a0600c520210112800301d08101c00ca100e60600d90f6004409036815244044542d0002e4800c0c480182044107201000003840c12004 = true := by decide +kernel

theorem cover : BRFrame.Cov 669964028 670143884 := by
  have h0 := BRFrame.cov_init 669964028
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669964028 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669964028 ≤ n) (h2 : n < 670143884) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
