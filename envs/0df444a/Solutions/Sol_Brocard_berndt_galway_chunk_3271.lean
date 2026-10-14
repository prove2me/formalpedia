-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3271
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:10:19.122597+00:00
-- url     : https://prove2.me/submissions/ca441f8f-7a17-4b46-b0f4-85de6c58bee6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 588129496 ≤ n < 588309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 588130746 1250 588129496 588129517
    0x90c09060501172505040b030108160b03040b0402010809031927120219090504150b01020c1e0f0607081e030f01180b0d03080702071a090402161e05060714 68
    0x445008003103031303030091040d075014203100c8540e20340707968448c00c11955661400c01c058000e00b881110010b00074502008a911850b48100440420740b95913005441d40c0002411040f078601050086040c030642c0050080d4900c0415540d2002d1000d892042500c0d00040c0365543e03142401d121800d1103502d10201e43c5464059050703d03d00c8800055849454005c03102da00f214140e03d0505051000b441102805606091b203450000c0110328091001039035501003144406400480f4050007080c031894854034800b4560000d84060807403014040010826070004008403074016004c0703140d920400c10780d0345002101c9403400440c1d285041000400c504010b052003120841050088074031001c0703185400c030001204001e03080d803042008601d005440c0c4081250b0b0a001481140000110807605910310440c0c1750701d60000d03524041c0b1a0092001a5209040c400c807a00c0da0f80c075554001a00440800b180d02000c0341e03030301c80c0805c4030303140844c18100301a188408020088150103004000034040b52000042d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 588131996 1250 588130746 588130801
    0x15090102280e030703050a02030d081510120c0c0b0f09061519090c03050a05070f0c020f190e01050402130519081209030c06070b19090c0906050117 65
    0x55603104407001014600c902d030701400f6900d800020440f00103480303a501c51080f13040d00c01d1040c40a2003266201c60454080d03c50240c06030700a9080e0130841d4220715003400500d0411554440b001c00c01050b69402200c4000198000000380103110891070101d4205a480504803260b0829a40c5135980310000350501011107001c000009180c1c0c0c0c0c10031902010007040028404207a503600c80d0000800322001d81d4004682040d0000b0b1104507984035040c41954103441d5603072070a90740d01040b1481040f0f66012030f0011608000d440890741c0391035081c208120f400c099044c0c518100050f69080680603400a0700542c01440304c0e40a643e05062100180c500580e202d01a011032030001c0a075800840d40700b00980e0003804000041d051814008181220702942180c140500302c1050244500c1070700e1000e441a402d12010641c0580c03014200d0b00200c41d0700f2008100d00e841900da0000c081e4a950044001c40d548400800865070840359002418060b9031a0150307519110b0b4101000c0000300444105031071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 588133246 1250 588131996 588132067
    0x18080702120304050a1d0f010e0712020d050a1d010b0a14060714030c190b180f1006090c080603070311060c1608120c070e130f0515090102 61
    0x402c1564001e000080281070382907070302d01c20305980b0024004c0c11800009080b001549030881806851f0403103002080094866940041c1200d5880345400c0901003190208805401c603040303409000e004102c42c00001450000c0041c005140d02d00c00c55001c23180f82d051421041c856070740c5d000b041003143d00c0c1080c0d40c000402800d00086107440b80c1d035001850002d1070b102983c1c184000001819440840d001201c18010b200302160340062a4408001e000e41101f00c005455403100d110f9003a18001550100d5000d281c58008031420100d0884081030300542e00c01c020001035406015a4001400c0340c14881560305211011a880d40446c1c08050808554009030b5505521110304540881c4001c0b026a0200c840500d116111000300d41b0503800284104403408648080441c01c8403440c0b4a440014020245000c6000954120042104601ea0307803a14034107012030704428030070101c00e2140d0040c0c020014403c51407004218041d08a402076881800040f0704451300c2505034081000d10740000c4082c4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 588134496 1250 588133246 588133279
    0x103030c170d0b09010512030d200a020a031b03051b1207060e210d09030203090409050d031b020a030509130912170708040803060a171018080702 64
    0x701011880d0799840540014a03100c031041d00e900c54404040c003190b030507206903a9503042241000c00345210341926041080310a0040e94181d001803820703c4111020801c0c00e410801700b140540015a10760051703003000803503808041c0e20058100240108150141c504003042d01c0061140c05035444082c1c0504e40383c13140c0c0c1c25014040107032a1255215501c055558201442e00d840070308180d104d0004113102c1d0601d00c00c01782620840100e642c540c6c20b858581032044202080001d403210702c0e400d40560004001d03410003500c40b03006402c2d021f0b016500811518190701030042c21148103448410b210041d201000700c1d02d0354085901e401068140c03030119144d00030030000500024842160880c594030b08201ca01c100070345a84441517180c02901d41c0301d00710070050140b0b020204115110390005000304001030004030514051a0410070241004003000d80750b031003060300018201123919069000b001c400405880c24065541100302a161040c100c11190b0340d4212140a00d200081c46400818107503c0071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 588135746 1250 588134496 588134513
    0x504120507060b1302091504060e1c150b180c04291908070c020d0605040f0f050601330c0f0501110304151b0e04020405120f010e070803030103030c 65
    0x40c5000708228002113801c01094025400310a045004074500340d9069103054664003a1422943c080c2c40c1c82c03002c2c1c4003010412050f4520742001c041c090a20b0500000400e1b581007a6601500d06410002040c504500c100481d11034441e801074880b10680c410001d4100300c00c1e09803021200c8101c2e00c40045110f4070b0b81440840c0810592034100a408202122101650103900103568400c1c1c48005a60f00c500c20212903004408501940007880d1000c0200011140c0c2d11055105020f100348880d6284540e5031007006020a00d010b54651303025000500074000003420f80240c40c000d03144018283e00d2500c00c01c580c000c40034103400c02404200303807000c0244446012681e110562000003000315441209130030302590030503a000d40b080c0c0c00b00c02080119524610aa80880d400710008000c16141c1103021105080c002982507049902404000b9071500c03003449103c400da420001810754041c802c91343c24211070549070341e151350f644021802c001552000c030440e8192505132134940865245400c00508 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 588136996 1250 588135746 588135761
    0x1b0806040e0a0f0614070c03180e0f07020606060705190218040c150c020f1504080d0305040b100f0b0703140301140a0605040b340305030910050412050706 68
    0x1e850040c80300d00b8040004032115140014821003081000c0a6181100c3c1e01c02c5000701c55460200e07501202c030380c0109000b01c2c44401c05903400c052a40e241ca840d4002400440820703520486001b9040045c0010542c040c00b1130303070344801d060b282c46080000c0d6403034840c0d588540c500e001c43d4040c0c0f06070700c00c0e040d91034072000d0703802c1c1c0b1289490125050400e8601383c1c2c9021001d220701d185d0b1030305080c0d012030311a106110140c1940d400801078407140003091700b040003400b135180846600c000d080100103402201805002c40c4800c0540b0300040301e00e010b0401c0c03000c0d200014841883c180e09840c0a200e16044482010299078014201540f134000701c1c902500c00a4503181170251000b004800020007200d240300d840c0c6030010583d83c82000503076440058034503026038080c0300900c010070300c070791113201050714000d0190058800c240e4101c1c50403600c006405c0300369143c0130340000c1c00020410090756002c101a4a94590000c410429890b080e1584418402810000010820001914003d001e0250030896 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 588138246 1250 588136996 588137021
    0x612060f0316030314091302090a08010c0f03060f0807230303040e060f150a0c0f0204181709010c06091a1008010606050c102f09040b041b080604 64
    0x21040480b15810040326585403000b24005a00001100c104040e290156018064050640d228020a05600c24060340082d02c01c0780d084402c020000690b07003403d0040206080c890713201c00c420061207010040a80c0c1d140c1d0450188490700d1102004040c8000802d102110504c40d41040c1e842030045074102880c40407140103a00d40700100b404501c141c46408000e0041800b1110070300601d600c64144070049681108407420201c0502c084003200b0f020306075000300503200e00450303828001213500290445111200024401200d80c841c5d8042114281c084501600380c012070324141050381000a141d0001910000c000720f480780d2081d03040102000008484020340b10007402240b43c00c003200c0c59034641c940b080c00010f6080040000340700b405001200d03c3e00c5102e0014220f10700161f4108800790060503c014a00400c4ea00c42d010700880c50390110060310f4400e0103e641e80c60704c007801c12042d40c6484480611541c6020381c00c0c5482c1082c80d00d0345e0710404d498201a41c071640d9680c0054010315280c2c5548 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 588139496 1250 588138246 588138253
    0x90b03030d0204090f1805060f2a090918060a15080a05100b040204051c1403040803030603150c0d0b03032502090106020f0a030c051c051908060612060f03 68
    0x4c21400c0e0300c1c1d0020005d411040f402003010540b4901042500070308071030054050381108001c90080c42e8642001039000c0044039000c04004016001951541c0d1448181d03103c5c5100403c00003001d161031038219030002040e0b00c41100c10803203481c40f680c03030303040250030b1603040c40d034507013a03520b01a4444040304000c026a0003076448203141c5040050b101c1c1000950b10904910b41407003180d0314980792080d103090f104080e212014080c9030010b42c02d4140d00d4440700359510780500c640045e450341c0c2000100041d007610400f440e00ca04000c024146410029100003400c5174210040054024840d81552400141d0200105000b401c51020900354480c2c200d900740c04c807030b818280c814004c00c00840160000d20988000101c1d80c0c0e50b1400300c1e1250f5030441d880203560059161440400e21404040c4034a6014001782da1040780140409070700c05c2050700011010450200b42050701640024600040f81560b041c074030540d00d89240014039900c201d98200d141c10b0101408240700d0340324584113480e0f070100074048 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 588140746 1250 588139496 588139499
    0x3006030602071a010f140316060906080106080408030a0b210309011407020102060106120b041b030f1401180608070308120a09022d0a0b0c070b0301050604090b03030d0204 75
    0x140195000d01c030b058031a007804026001803090820711203812030f442c507403c801703456061410140c0c5081d0344411541e4144259010f144002d40c0c030704102001000b0546602d40038070b141400c09411004140d2001c01804406020803010810704801c03690f000d90b12180c000f4400d551040059403680f028458110302122036840c001034018004000c0c10f00b103600340c0300d901e65030030f44e1031a18060303220344d403002030040c0c011400420480380504044500c2c400b04001c0403a015807018081030403606003207829a00c0301440c150030040c00d0342510a41800000e468400d001800c48001c481c101d80e04113114110340440620300c08a042c070f03000e0b0300c61000340100780c0c00d03180000d42da810114000d800030390221744105074210226404104c0c5100714100154080c0c008881c0c0f00f000302c01c0c001d240002549201ca51142da202240156984501000c00350085126050304c566124001038074181040d0032400c1c10403000c0005104964a50007500c0031a48580e8010800c2e0311408003080c214022003004034211400410b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 588141996 1250 588140746 588140753
    0xa080301062601090c1824050409020703020a030e0f0d12020a05030316260408030c0f03160f0f02030306040203180a110907050414040b030f030a170903040303300603 73
    0x20505c48039003540d881140071011860205c810040030711508207141e04141c1241c981494181047d50f000e461801c00390306055481d80c450f03041ea0300c820011401038000e59030320f004141c1c101259500ca1002642e2500e620303045400440c3c84003400040c05002d5a20411410004da80300704540b081d034039030090540740c5a090410541c4610348a01d4040004500c80d802c11600e0645c0140009071003080113200a201ca45484e00c4041c400e80c07000c0d0070a40044810003180c2d828040e400c00450161030503128400c0c8164840c1001090180d00b40544010049051402c12110340e0003c240e0740c10034402c4400613545d8403107001e4960f404204411603d214001c401c0d2203805d00c00c0c00304842c00c1e0a00c0436246014030381d80703040044a8902c2140103000700e0324001000c0c06142c1c1043e030b00803031b40310300003404840105030000640f80c80c40d0004401840082d2452181b06d02e84d5114a4030031313420510320ba000b1400d184c215600039085034003912080348914041e82080b091400c3c199010101411050f20400000f900da04 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 588143246 1250 588141996 588142001
    0x131a09100c08150d08030109021e0f030a05090304151101200d061d0a0213031e110307060f1101060e0f04051e0318040605040e01050412020a08030106260109 69
    0x80d074103da0261208038030486070034150303160795516a01c01d190b545075a00340b0400400a40141e01418208421203103c0d0390958032140c000d0200c1c2e40c1416442d9100d10b0030810382420b560300140390358901d4009001c10042c1604041c0f19101c10b10b081e003403009c1d802c0001785d4014010301d08082d80c01d045030814222080205540e03c001c201d001c0003400f09102c0d841c0c840051a0b4100038120003d0040e1481d030780020322034141c03a406480308204802902030f140d0350307a4481c10780702c0c10100f501b0807001b08240905c90400450f2205008040d1055014043c600e00d41080980510792170301c074880c2030101090394010209403e5202d00c018281101e001442414812461850580111021a000c5c450012042d455540d40b002c060038403120714000710300d043c110221010f003c50004122940050b168600420a59070301c0c09001341d03c49588000041034a000c0c14600c0d480e402d030000342000d641080400c0d4001ca104c2008890544031107040c812503010800804600809440500d03a075581c01440000c541c000164 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 588144496 1250 588143246 588143251
    0x1801120b1305070302010c02190f06110105100b0310080a05010902040c11070510211a010801030f02150913060501020c011701033201060e131a09100c08 67
    0x40000190316039802904400794032940c41c014100340c0c450502040150301c54000d60880c80c1c130241040c0d14881814031001e0442071103402445200e81d05080500c0880ea1141c140400222504000d11190600071070f02e90403184240507500c8010300010001e8201c40080d07a1500c0104804021507044000904005000b0a1844030803403155041401c13a030502c9200e240001c200983c0f00d009801c04514000401004000c0c9506130018800b40c80000f5191440544000e040001c0c0200c001c124070703140300d10030101c688021f00e8090511038000014404150751003d0007411590558448002082c555220000390140700c44059008114002c80d40005000b80c11660032154203800300d58400200d0030042d036078960943c100e10102c641010042001c100b15081884856600d85000c080c0c00001d4102c00c00c002100d5400080d003030b0b4507000c0c01c000340f240c4054100d92000340a2a10040840103640d600b00c0712000c3d19540420700455400b15601ea21300b44041d003034051070713444d00f041000003100015103881402c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 588145746 1250 588144496 588144503
    0x4080f06100905090309041e14010915060206072a030e03010606050f07020d0f0206070302070608090c10030506031f060326191809020405030f010b0a05040209180112 73
    0x50740e00008503101180506030003910741078091401c142030b5406100c000c081c0c3c80319042500704120108044002507205e035041c2034092504400056062002403001d40b10740014080f003a9180080811643c0c6d80810800e810503801c0c5008140713515203880314010341e07130500b800608804600107004105904001d8204c511790090340240116a921142615039015000d14540c40d02030410120300145400d48426070143d1042c4029818004240c010650035042500d0440150780560020b001041d00003590651103840880100755162a42010031040c2d0480d00000e030501d07484a001ca801c0d0754041c000145000700b20614184032420407083c6101510451000b51514580369540c1c2d400302d120008104000840360091602d0190705c13111a686041a82c0c0e0304000300040d001c0c610300f0840403c0354201c010301e18000701684940c1000101030900c600c10310b800c1410b82c07402006503155100c6050f030f0070403038000303e0f80140c654000ca4007103050307580008a86005181003000209410b0380780c83c41441200d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 588146996 1250 588145746 588145771
    0x31b03050f0f0c040207051f020309150402031203151012111201030807150207081207050304020a140406030804030f030e0612060d080c0604030207080f0a111504080f06 74
    0x89007091911542d1104885229421000118200741040c1d0010b0595a20500441c1c4549002c44181c0805014000808844640000500c0884002088100302d402a04020007020b07081c2540041d5031810340c202c00c454140c0700400000c10710403200c000ea01000002074503280304024050f07801000c0c0002248044030300c6182131710517642011001d041e100200411010414641d003940c645d0007007500030800403641000880170b41e9000080310300207400031034070480c010b585400070100d81c40030041d001451081003040074000c00c0050f070b5444403514200c58034021a1280c85410801040241c1110340016000c0c420001b0000100500180711404c428084e56072030000f858130001b0444207101d10340d0031155100c1c001c00450f01c24030f02843c40c0440301e4490700065160450f0411000d0502008403420340240c0c01c407030410002400c09011220119220314060580d09406a43d981104c0060b0300c0c0b0580502070405501901020740411107010342201002c80d00703101c101d101c0c3e907a40c844045404041615 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 588148246 1250 588146996 588147013
    0x4090c090501140f0403061505030a06020306030105070c020f0d110a0e2212080907050d05060709060503070c0f15060324060f210c090218030c0901060503070207031b0305 75
    0x200348003990140b05080e070f2a80e1a2920315100c07070000c2c05008904001c0600349200024862b5420011601245d1240c280540c891070403401300360860364018443c0c81403000c100800ea0050b45d07420f0031130a0407030044810a006100b42e09000140350009c920103500040054000708401003520710342e900c6250201500b075110902c020030340c0d10600074410010202d8103030205044020f80541c2100b0391060744042104ca05581d00ca002848003600302d402a034283c0c021400703000a4540c014494000703841141407681c5141042c0c01c0c003d2000b103c1d810040c2054031032040210400103c081d40d40e00b040402d41040c40826140d080c16624030348040c20210802c0c0340003c21303501e001c407940207c2048406030904c0f100c80500c0c051015503000714240001880c5070300320000c3c500042c0d00301540b50213403051200c0103854015200c6001017296015100a100790b02a60b84002c031643c9902c400b0b41540c000e80b401c9922a05c9035a016031610485410050031884445104244501d8030b01d0a4400c8034010f104a0b1981d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 588149496 1250 588148246 588148277
    0xc120f06030506160302251209050609040f0204051503101203020d140c0d080703060b040e010b07080c030a020109150203070f0f0e0303040801050703061505120402040204090c090501 80
    0x2600c2070301c002415500582c0004040b140c03c52180098001035040142c5400750002c10a2890000a0060050807440445490500c0315100c921003240c10282041e0180900744030000b00383c0d010381c6958a1017141c540d51810076444841c0c054400401000d084045c403000040464283da400407940104041007500001a00c1c8408030120315005416402074442c292402e04101c40301000580c036106041c00402030749850341303010007a1101202d030741d03550f007d1503003480d200c010117851542c2d11021441d5070900082c8204074800b4410750444002c1210142d65403418607050b80c050103424190300280c00b020580940f0b1a07010f420040d8023502c0364542c00050100c4415002c1240015160500010040e9140c000f243c2d0040404000356040d03030501c030040660020010749503900c2134111800a94485003407040c0350741c250107820060034140d0804040700382422002410340c083d54108a00030010f80c4042010740d00d03254100c5002e000c40e940140700c40001010080d1600e15644195400201502d50941c140c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 588150746 1250 588149496 588149501
    0x150d021602040c09030f08090103061206060806090708150604180b060310021918050d150e0c0d08030a110406030e060906242b14010b061209010f0c120f 67
    0x560f50302401b2664100d0458550040b55040040c41c58181a99002c0104034a0300c41c00030184040d204140c0421140c1c14026034a003010320141418915038400c14050008250208450103c00d148140e0007186503102000a4003800d5401040030700114400c21030f9041c00741c0580d01070f01c1000c00303900312841020703041082c404038410410301811643e528248011260301ca004800e03400201c0720341c00c1d004240c6400018101c103180403421582010720b2900454204d2660180600c540190700141508403400300100c1c01e40f040d94440141070703203400000224400c10990002403d11640e000301501e854071100c0160050009505101c0300c0c0c0b2031080094a4280c002034000d108009400d0040121014000480b442c900d83e000050362008486020036055801c03001c81840341e0075040d2000c800b10115052100300801c120b6500c040d40c0c0d04001086001740c0307a240440e01424402c261b2054903940e0104000e0041182e21140c203103490420301071a00041d0303c20006035100030390138001c1009050750310b5010708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 588151996 1250 588150746 588150749
    0x7080f03090108240306070e04060e010f06180b30060a090e0c12010b090a1b0e040906090510060914012606010e01031403031302150d021602040c09 65
    0xe10030740014400c019204000c41360308400041000b2204803100003c0d0030103034102e510a002440c50300b403c0101c1c1c0381600654005101070356141400354101150b032407038000c050140c82e0522200035108642a005a1000d6000b40101c0c8240c544401d100301920600101603504103002d1440d15501c152160501d940c1c40d40113906c010011308a0a2920700040060007141174808014003d03800f14180c1c1b91280e5500780710f001450000014120304040030042c0c00c0001400001c003c0e07203420f0006071405042c041140c0c41c1445400c0c0a20b407141c039000064058074030500010100c1d4100f0310703801700300400000da004048640342c6081c00090307164035144080301c1c0784201071410741480c030f4010800203c0710203244200440d52500d00402c8582c0039501d07880d01e0800ea000306007145035400100184407a0400924103100080e0142d17255050504100b105104005000303845013401c8101c0103621654501200c00c182d241610540d100d06829a80c1c40d61303040701d843c041e806a4200300f916086244291079a00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 588153246 1250 588151996 588151999
    0x30606031505090a020405040207050303011d04032a0203030706140105151e130b040911030f18071a1818070507110405040f0507140310090c0e010807080f0309 70
    0x5025518207000c10841d4031011344032158140e402c00000c03070306d074640f40010040c0354021001195207500d000340c02180514079090140c02541080140070010381d010003012042e042103e4203070260458183d84070645025584000d50610001a408003005a070344c006180012540301e092169a80c0c0d0001d200d41280c0d080c07254403070607a041290300080c907580000348500300500403500f4204011040840b04400f5250019141000081000c0012114500800c03158015108801e0f056007040075a90400400191400c0e89440291021211060080011100401c80c060600f0485640035016070b0300c56110151030386803048007020010140c00c182e500340450003040d400c00016036481100c01ca8450300400d00884900c10260f14082c0a5035440c01414010f034000c1c0c544080200d4903140c090721308a003d40c4100b45459410390390240c203940216140c910700346241d0010030900f072245000034075211030f41c211082c020710100c000b2804072000102c00007640c10840441d2051030ba10105550359014004000303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 588154496 1250 588153246 588153281
    0xb0102120a050d060b0a020a050d051813150609030201120e030417010207080f2208030d0c030b04050106050a0906020102040e04030f0e1305160903083f0703060603 72
    0x12903070303200b50000d10100e0207410300062425200c001c04900c43e4400302003140143e1100d645902800003e2014007114451303400e00a20b8031070b044070a40a001500031031140705a0018020074030510b440c3c5c20000020541a0811403031a440c0d41c806001c1403003030300040e40015610303112121440c0303940c480e503001c0c845500001e41c1800d160050456500603a058191003035502030004030f0020311f06102a004004036203000b15115094109815620104560780c03845031b84480c1000c21510340c0c08411100040c04114000c81c0d501d00b44401603000d40885044550040e10380800040c0c1c0d00d41c4000a0450402c0c6956800c0c0c0d07666503044100e00340d02640c081d01e0041c4008a0100f00020f0048804a107440d4140c1045030803500914002030001c407080a040d1490b41c0c6030000c11000900d8050f89507001521405d02052940c2951694401402030004d00a9a200191182540150524100d806040d004220010140c02c0102104d0000105444d19004070341000e4004c10154001c0c050548680243d500741c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 588155746 1250 588154496 588154507
    0x6172503060e03190e0108060d020a03060f2007030807020303070f0804031101050a09060e03120f0406090b1806060405010b07060f1e020c07050301060315020a1e0e0102010b010212 79
    0x640d80103012400c0703500b4907480200106119507091030a07072a101c0d03009465694010311024005403190b200282414482c81c804030614005039502203152003501d40180e00082d0b40c801c03032002c00004080c48068500c0d2a05005840001c0200f0080280009440303650b4060444c0c890000c140d030360303000070780e20100416110781411161500c26001c095209029240c002200914542020b00311642a1140d0002c25125a0403800344040e5016034204008140001c2d40303448616210746803142009003e17410a1032054000c1001c0c0003807500110625500f09100c1d150710708124404815042419882c000305010b0480041c00e945442e206842c1280c040c00d100610b0901e10380c0ea030308010700407018100511030b0788903e00c03e80415a182d80c034444100365900141d07201d400340c00b038900c1d028095105a110785e05003802840050882d10030100058050f920250f16584030344401c0d0b8806e00024181f50408141c010080c405a5100540403030b122403e8000f000302003403500c012a1500b004d00303841c80d916c0a04001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 588156996 1250 588155746 588155753
    0x302030103330f0b0a3503040506130314010c12090302072102041406010929030a02030103120c20010212031e0c070c140d0606172503 59
    0xd85401e00c090405840403900c1d50424454215020f2101800c0482c1c0c0c0c40b000301075182000d11001010f481882e8003941c422034041d0048841800e0546201c210318110040803020450400540740a01001400c141c0c84042a0070210f00c001440d2100351044600c4442008901e901803103084051745083c1d60b406440c0900c807038201d0207040e20442c200d085200e028400a41c0c0c10f1081089104081c60044034840c11416004000540d4258002501c00003000d1040c05842da030402c2c42102251044d92140e06400b03021010402d01420460052090030000401c1140c1c000040d40107505880c4100d01030034151625042c02c580781c40d85001b00800c07501d1481c1c00710502c1c00c4022102105402e0500c101c4400348001c5a08481641096400003d640c0c99203088241811204180315800b5071542c03900d82c100205a225100c00c1445482120b40440104000006a845038042040460341028043c8450f5030303512215590180307d4032885625001e14003442c9482e0401c0da48800c01541e6402c0c8070b0301164115203 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 588158246 1250 588156996 588157043
    0x9090503071e060e0c01020d08090a02090402060d15030c0b1c05060607050307080a11160e150303070c03020a090b0d0b06030304080a030806011e1d030f12190302030103 74
    0x32001104400c40b101000a4598010075004051420141c45400300c10000a450f03c1416071040003488034240c1003188a41c0700051248019404860080c641d40321070000c1f4075944a0940107088142c00d24010035000511110030000700c9103e10520810f0a40d51001c82c0158003403130580c2d0018191482c0e026184404c030340c0195800410040036581b0746441981d41a2440d4008003086401ca9004500743c00480e40186510580c2c50040010341464040181a0b0100d40528014005807045003004a078140c001c0880d00c00e602007018040340ea0b61a040c0c04c013101c50311001d02c02244192001c1002080805640c0914501484003802111810f48071b603842d2502100d0007000d05070144014840014941010010b030424240692900d00c40d5040c10b000051680e19491059040c0c002a0350080711034581c401c44a40015081c0308001c0c0303401c0c004030300290501100c0001c102103481425082c2140c20300b160000c08414149041c1450280d01c0c40c0415016070109200180244500f034101c0034215031440d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 588159496 1250 588158246 588158273
    0xc0c040e031309090c0f05030d0f05070b15101404030312110a050c072909030705060a03060e0108060417030a02130f03020f09160c030e0301090305090a0909050307 72
    0x242a641010841d58407420982441d034081c520b1039840b801c120091050102c03a24000e041880e9a00c2c9a040c10140840e92760340b1045641d40401004e0000c181c40c4034499400d486150341e200c80f40da00d85003010400e0b06040180f0b40f40591050006040940d0164090b12990400c0c401c0301d9076403410b1900c0d60710242c9404100c0c902d000e03000c58a82403a41f0380302c000903004001c084160b440315503c070351448010b58a040a507800c1007100b2100c15a06000600000600b00881d5511100c0e66517a2000840072a044c40301c198402d5030010300100e6107204281e0035400110582d400d49071882c52680c0c2c3c031544140da502c800e587c042d0646948406020341c00000c0401107503c521058400f624105029a0060016078260300c00150f860400e07070240114075128007040d0242d54100c8038001c0d10b0414003642641d0701a014448414800c0c1a00d1640030580190007007810300c40010700820a40d02c2600b8003420707651220f1000d5100300e44811000c04d010003a8401c0c649a80e40081c004e604010b1240c0e12070b000243c0d030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 588160746 1250 588159496 588159521
    0x140703090305030301061808160311061b1b03120306040c1407080702010f020307030806060c010e030f13050303120a2a021605011713111801060905060c0c04 69
    0x1905030200200301e00304011345c000c0c0301ca0740e10b00c0110714034034010f803000d604941c005c940ea03604080e01b8a07940501c52541d01e07068079000340c41c60340e860074140001101ca1080d5a10706255105c90700800c0c05900010644910304445010550034425880042680360722045c40241c094a200344080795490409600250000210f802c1014000c13036842c1d00d041d03490300b00300030480346142d00080c00c0046580c003491490001d0841e000075070502c81542e40c0034041c002d004000a01030400400c80c110340381025000045650002401d4942c4d8034880c8980010300c0e48844d032181c001c0e01c4290740019071410008105da90300700250004140c00d8444450140150002008885d096080000b0420050945213540c0028864036001405014071440d101c4070341074415806541406602961460000508034000e40d10010b03010504140d40d0240c0b40041c901003e045420340c100c491007032a5000c05400d003a03158140c0e007081d12100e041d282d4581c01c220562080c500308400e01d81000c1c80c1d0614a09150700042403282c00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 588161996 1250 588160746 588160757
    0x9030f0606050a17010606050c0a032703061a0f0603040311012003150402090a030314040b160b09010b2b1b0e0105041a0607030507050105040602030105011e140703 72
    0xb074802c0003079210102500a82490510110840c02c03070b074024400c42e402404942011030801d02c1d8130030380343c0d15144042c8024007440180341150162181041e04061805030b0a0b140f9000591a07061100c020500f209403c42e044864482400300c91800da00d0082d41120024240c0b441d41c1e4480d50300700d90294621320803510b29074a42c050783c612030004601681b8024050720300c46480340361001c25221990f403007502035400780f841080500c500741c40e841100c40030b69816040a885a940410700d409080c072590b84542c0701d20304040362b500340841e56a0515086103018451192464540e07020300350880c0c1000d000f0070751010035001d4070680c0d0300521500c69580031001d1601d20b0740c8082626003805c55200804103129103010030400707008006417003003180d01510041da01080a174691240a4074104040c5603094419100491700b001014861000c417400310fa88000284060306080c035040e0080d4000703000c1d090104250b0f0303041115001c0f41403d8096003240c159a10011040d90481d0302046a009c1a415001c000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 588163246 1250 588161996 588161999
    0xa060501090e070b07023a0f02092404200318070608060d06091110030b10110303220807030306090506040509120a020c090108060f0c031005040c170a060905061009030f0606 76
    0x218582c150360141f502800402d142d070b040302e10410580080082112400c2c0e010381513002c4085a00e844148203410080d00d0005400081d1901c182008e10880f8140c042070400004010350295080041180941228103c4140503110f1000741c2d851001102c0c915086181c08480c0307030108110340c2001c000140602541e101c50700c000c0011a490184201d030510201e61981e6204000c0c2c14001c42c9640703081c0c1e0038600700514603400c0c12841d071240700161820b514080507003a2039074801100a03040301c0e400d510843e2541d80300b0441c50080e010f01a00d214002c1b505107030600007003003414180601441a4500405025400004141c1544a40142484004512455514541d40d80760401064040d00d910b4008000c40e107042c2c24424042c0c00000d00c50003802e130040c4140300c141e208a415a4003641c60858012a04511001003105c000d03100103100c010800081040c841061301c1c47c4d104e901601c960b008107202c96541c038420300c00180302310034600000440300103003000403c024442c0300b2803940c86aa4045042d9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 588164496 1250 588163246 588163339
    0x2e140c0a030b0418230f060c2101032105180907030f060b0301050a05040903230d090b1503030f1c061e150804030f110a060501090e070b0702 62
    0x520051000c071001c0f003c2440d4102c0400030380c1040d00317600002c00c00802214403078030441a114034000e45051b0000c100032480034186001968901032207040420314000380e44c2d6070309140b40b207601e8400e0042281d0b20315145032238045201d80121601c0d2400340c214800c1c0046004140072803424020110707020160703181005070080c03200340143c4005043e4112025100d50500c001c00421440c1a80110f1245141c0000000025003150111200c05028105400b6200d14410f0f00c100c503101d005000282c0034a0300d03d08400300200000d400b40254640d0700407103150315941c0181070352403140a00c4400e000d1070078030640001451641d0344a1060390610008100d850b42e940542020b0480e82400e0f00e1180c08120040c001e002024024030580056490164403078105500c000d070000710a409108100250940100800d0004001c4904410340c0500c00300040d6039107031402001061020000300c668040c0c1c040c0042d07640d5810b4251aa071a03002042803001c1c00072851003160b1050280c45246440c00c00481c105086d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 588165746 1250 588164496 588164531
    0x31e060904020904201f0e040605010e060703020709110406020c15030a1503050a0b0103120302040b1806071202010e07120506150109031218082d2e140c0a030b04 71
    0x14840c5140c11100400d00301c95007d010070859840b002e01961600804000c280c0c1d00820306030050310140c0c0c0c007036074489a50400301d0411580381c02c80855607040191315858155514000e0045800c2da0b4258bc50380d44024041010b041c81d03844810443c2d05040c008910050015809450042003403108291043d68950f80c440c100f450205003035484040110041080c46505003800030440303c1850114502030074500042414001c1d4010140040180a144c01180d06c03900121900c00341c2003440e00b001040e207018000d0184c0384200322001c2a00030780a0001e030405901e01c04000c2260700c040500044da031050307038420060030750240850400818900000102c3c1c0c41c0100703003031044900d940d40b002510789640307a00321080b03165102200b254031884200080c41d21185002600c0850031085079035800c80c00107000e01e0700c60400c15019040c000612007d145507904a142d41610249000038040031802e03001310a05080c04991a481e624010841014000c0c4268050090b02100402c00245580c0d0006104030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 588166996 1250 588165746 588165769
    0x7140a03090b24030f030a12111b07050301090218061c080a0906090b07150605270a090c0605130b1b011d0309090a11031e06090402090420 61
    0x3140040e034003000c511001c0845003122200820360045c41800c8211240c6980da200b14000d2030204040506040098516074000d40507031160b208819854111135a60002d102c216402446141e00c036010b0001101e045c10f00a81e4030554000304076440f045a100004001c5150040c05160f1048109100c02032441c0901c42c041040d5001d490341903182c1030080e801404c4100107801c03410510a401108121b011040c4040b10460356020301010481d03082c880002c400f40502d60041580910a00003211591040080c40c90502003000e400485070344841c1013082c100c80e60f9903806000e10748024420310485019a00138540e101648800e20701c080e64070f589481c0c081d000a56840c850621210b1400c1d00050309006100310710102415440600b0410009030f030b543c0c8507841445004070110000501c0c144569881380d00780749400e0a5040d40d0b03107070030401101250080c00c011907054088001182403400d00d03105881c0b05075406070108040d9212510340d441711070034441809489010f65880301c821625180e00018 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 588168246 1250 588166996 588167011
    0x8160504270e0f01060b04030b010b0d0e01020c010222050916020c0306011212020105010b2a0601030f0c0f050303030708150d05070603110c030a0f110105150a0503010507140a03090b 80
    0x84210383c241241802c0d14007a03440020300190500043c000b04042400700b50449003094040c035542c1c5840c50254010b8070014020340c91551011800e601480419001820042e1117003c8080c02d003100c1c4003504440400d00e0040039006581c0c040015410703100705507107485104082c0111001c406c0104002031400c20240c008101490002c044001000b00c1c2c01c03012200904140028072496062450000c1c2d94040c02c210451880607510560502c984140200b00a9210640540b1620f41c0c41c0e04107142c00c01d152540445130450040070010740d54058091100075a040200036502d540c44200c01200c02d05409040171107400600b0000b210f2170303900d46466495061051000e001111f1405501500315051a40c1d042080c0e00104100380b20024003008541011426061201d00c5c80c00b1020122820646003a2010140d8a401c0a10550400c81c0600754882d04044449413002e90303d800a041c00c0e00c0d0251850310210b058140107202c1c1d044c615000e000414518940002c0008141d1104281c0410948200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 588169496 1250 588168246 588168253
    0x303160509011710050108180d0f0512090f160b0403080d0209040218041104030515100e10080d0c080703210c03050a1505010206010303050c161508160504270e 70
    0x100106e58000d005940c0c003841020000c22120811480c4a84540301c00c94417104003c001c4180903560b0340590103840c4200d4018002c100180342612040703981c1c0c10741c145c070205a8450240000040e47c0303030300c8011054940348203030a4103062856490004541101100746103687e000c3c011003240d900d440c8042c10395190b01508481184085030180030880388120707095040d0300c10401050001ca40009400c100c11010310055034001d580781100708031444607c0d040300324135075038000c00d2058500801c003050098035840d506844440000c448160750341c1d49008001821034138103005a0300840d00501d03080500c03100022101c4800381140c407101c0101e0304501061b0020965035010b20031810300038411001c4000070b1002c000800703400d00f00040d5440d80148802020004001080380800340203001d1440c94080e1800064519610380106c0d980d03102c22010035a001440030000201c0c258400710541c40c2c424400e4541e140303090b0504484614810365050343d02140981d540251070880b0ac18440c0340928000032015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 588170746 1250 588169496 588169499
    0x513020904050703051506070203030d050106211a010c05070e1915080703080a03091e12090b1608070b010f080d020c01080609150901030c080f0303160509011710 71
    0x8200490b40040d20710b0080516003405c0200071341034402881c5c19400101c8005840704024400a40317103100b41c1850100b11401c0c03d00002d103907a0030a1080717107090111901e500035104405400c400b00c8070030304040304000d601d641645203154050790b01102c049001d9000c2d2000180c84d404c000c07820b1a0250b84c000d664070414204690f503c22140302c0e01034898151055036400310315022940b076645c001408080c2a025002a140d0a194007961010400c0756011041c0070800c4500c040c030484085140031700b51644110780400c8508244112406800c1d42c006203c4070342070000550048503c20091001155921810051100801e980e131101c44e009111a92541040b142840c0406040c0b80040070001c065500c03c0f8921841603800c8881141e2002040da420051a522401000500f1020140b09134010100000120500203404008015188000200c0c0c0411b61094803050392407104030348283d1441c0440d0038840d8290301c140f0003803042c12014540101d21400f120030208000308152036003840e00c141000c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 588171996 1250 588170746 588170749
    0x5010b0a0f020a020a06030203071206030b04170a140915030c03100b0f0f0904140711010e0a0c15030b0303040803071506140d062403140f10051005130209 68
    0x850040711254805850b5103015580803c2c81ca41d00750107050103140d0088005012203200b03940d0290805d4600310103004403a0749003061080c00d907084c0c4041d54041030f0310b416180440d0800e0101d98600b8501c0c0d5400710245400e4441401c60307044040020f60101594180c100302070031075000ba5000c0d41011405d80c3c2c2d80d05100303041501032900b035407081e164010207020301640d503291b88082d6052500c0c0032403000d65800340140010300800f208468101001d5011042c021030342c0d0300800380c001301c4c2c0400000700708410103200c400342da50160f00350080006034251014821203026803a0348a03001c400d401e000c15030006120000b41142c007d41c0203d1150360003c80c2e40303424054010030020a50481c1c180820030f81d03081c000f030102e1790340e02c2c41001d6001c1e01200104008001c110352000840d403c600115040303a000d050041c0c034980c245403106990340c404402e069025080c011a90300f41c1c1030f9849000f0310b02080300c10088070103024020001018205010800241c60305ea2010f0b0007120401500e0040c0e81e03800341d40 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 588173246 1250 588171996 588172007
    0x6030c0307060215070306051305060a051c020f0402070203063c01140118060903060f060e1f0f15120c022509110309070b0a080612030c0105010b0a 65
    0x105540310780d01c403035400c0022640104004104e03034a00e081c0d0740c0903039a0341c4100350040c2c4500c1c5d01030b58206d03010704000c1c1c15055060780402e01880e8120f034944000f1ba9200c04108414090035000030585003003000355001490300c10305629a400003d4405402c0c00003540000381088c01c201c5c0c0b08141a005010500d000c0c0708071604241d00b000c07080004019000466000c9006820305000340c07030a0090080030480140e0141c2c2d03840d6444400c02000d5a101c40e122500205039540e81d110481b0a0b9080110b840700d0030085010b05400c0da00c041003601c4071590f450b0220b04060714a001040d1804503542c2000c900a0050303111200a0042122000c00c60000c2d039000030a189580c500100c2e08910b44502c00c40c0c0c0c5540400c04400310300141116030500d140e01d40380c001100708103038811340101d4a452828025622408061445241000c080e10861035803190701c041c062180d0b0320440001030102c40040c44c54a4012103000381c01c803400c0d04503400c101055a12a003114000e80000c45280c9011500c4c15240d40e008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 588174496 1250 588173246 588173263
    0x2030912030a02120327160501051801030b0a0b0c0d0f030b01020618120c0d020f1902041a100201060915080a23031b013c0213030b0603 60
    0xe400651401034240e100a4965100d619415411907001000c101001c0c540d0352041011b0820f03000f00500751210b100565910084051101c01d4021000d50000d01580614242d414001c1907420140f5922204801100188444200707d40d1180000801042c01c1036200040c00031605a00018401011403d402414410103940102d0406042205040c0031743d80c0410303038941041d4521421444c500c041f90a031406c040c10548a503650300000715141c0e03503070a40010115083d1b0882d0b0241c55003007404041c40b81c0ca401095640c0b240c500b1903141038500504051b030006180070300400740301204c1c546400002d85045104241d403c0141e440390340c00e003c07401880c4900b10011000150070f034540303440c10300003944516131850007520300400c01503201c1c0f200080d5084d80303403410042000d80e40c0e662101e0051400c3c901102c0300800043d0320f00400506020b24803014030300403208680c20706404a040800d051241400a514006840d4083c06105101c80540d900314021794401c540d07900705481e15009051420411 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 588175746 1250 588174496 588174529
    0x2090901090603020d060507091d01031203060b03071103040f030f050d0305011809060b0607080a0906020c010e0d0c0e240303071a100302060f1b0106050609010c11040507020309 78
    0x10b0500410040c1e03140905c5002c590741c081c4010900e69100e64040d03e9213159540805100040152111960b002418400b816031740b0400b4030b01842440710000301d00311031150142c1c941400041000c586080d01481c114807440b0080f40449161503240c5a2600020034544e0084900c4507102e580c1c18204002840341c3c2d045607510340380401480d0f1400900000784000115950034545e50340e524041486400d41200c02150805081d0a540303025a2928079481e42c00703060f800c40012000440070400d14808500e07100c480405942c7c40e003a00b90400100843c90990000884215101100008490b41c201c00c40c103100d8240312420021141c0003039111ba10741200c2d000224460780040001c44006078102141c90b250f40403a91030300710640c1d0f40e00241c0302c4003401030b007000c1c1d400140854907003a00c82802005202c10796803004182003410008080380d0a842d114007030340354003610910400110754803c0b143c402e140c9000707402409d80d8420303000114046440c103440c68001070304000b480c4201418030741500580d0010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 588176996 1250 588175746 588175751
    0x15010f0e420102010b03100f0603020a03030f09090507021002030c09030a060b0102010b03060f0c0702151c18020a0603050a0902040e07060206250e12100504030f090609181506030209090109 83
    0x185d00000c3d201c001d00211198420340c0e8515400480e0050f81c0004055903000d44035881258407410060015140345200c1d0740020000b00c0e01140c202014042e41e070003100f01e03400408100c0030250054019400061a018195400b80f012001c03c0d03a0400401d1001d50240c0e000240c1c40c40c000e1b000900b92011851317490b000f40d0001050142110502000701d50001c1950082ca49a10745880016482c036122804a100c981e00803e000c0c0e608070f100d260740011161010707801c00245a015404d0070780c4140070030001e540488485020007030a0300039000558092040c0c00300086614069000604a4443c0e08042c03030694440003003440000d8040060b16048800640e030420107800e6030a038014048200c0b64904100000036414000d180c9071520a6a49981c40c40192070241400178104402000c08503015400924200c1d044032000c2d024020312001d03645140d84100c1e40742d0400c150850b0120750b00d01109092940c5080e441c945400600c5504058100355401580d981d501c001000b11206041e001344030718a1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 588178246 1250 588176996 588177011
    0x4020616030804050f03090310020d022b0c0e030a060902280317161e0605250806010e0d02031908040812090d0b1b040609060215010f0e42010201 64
    0xd80002d814027003000600e80150f0380d41c84518942020340101c0c10004c50440030014103120100c0c40c240f100410340e4510300200328040c10703070800b160490800800d86801d5001060920301087d50354000c00390040c00505060100e1300c4607408290542c6562081113524022011300307004001251035040106074141440c40d08004260201007000c00300c2c103034003c101350180c000d01d1009030494441c00c00120341112080100d4603001d407907010800310300340c0610400100e607514101d9103030107074040f2401840184c0d80c101d2410180c009011001d944510203070fa16116190580e03c0442c800e0000d200d20a10030761030035850320328001460380340c40350202c0444010311b001e00c240303071142d1182400c44400c1a002a94824280c540c01240703100c002c2c1070700002101100c0010041b0f09035030460600c10840303003698220340e0a10540401d104000c64203000d010414002c00c2c004210000c0032004c0142c105114100322400411000c0c040090b0301041c2c81100c2a041141491500703804d0101804c4400707040178002400310703c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 588179496 1250 588178246 588178249
    0x211803020a0b0705070513020c0610242313060206010b071e020a081f0504110d05030d0501062001200a14041404060b0a0e060304020616030804050f0309 67
    0x4206030b008803207001201007056801e0040030018180100400f41400810a6225910344040d42c000c1e00e80d501c207032180c1300124520fa80a04081411035001072600f5905480006190342c2030440c55040004221525000305c500580d010744100b00400118111941c0d03011b0109400c0401c4d0b026804138041d500603000410104c0740320700c102e4149a03070080707201c1170b5201e602441706003c030401c040280d00300c1144000400c20f181c00294600e940e245040b10742d404a8412107120341660405c403001410b4252503910021103041c54603042c91250b100b4000c1d21700300000628070380215a8242c3c4000b00107040c500b422103508080c8202040302c96008d0f4024070488146068200408040c485440c3c92840001660a400e40c800ca440340a000c0e20010308a560300d50714035098060840400009102d07a14240000418020000840d9100c002c180c46201d007500c00c242c200015504010026138200008201d411101d40f20300d003480014520a4a41f07a0041c10181005850901c40e55400ea000e54010800c02205 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 588180746 1250 588179496 588179509
    0x60f151a0d0504020d080304050a05011a0d060c0516081309090f0f030504080114010e100807030b06040f050a020d050606041a1c1119051201031e21180302 68
    0x707041c11040042615100c510104080d014529809400700c5c0011083c441005004283c21000f10700500003400010309040080403545409401c0c5076002c01d5400d01080003a03116000340c0c10240b82c0381020781c100350100d2160749142400c8007040391684400a055011030b030840c07601401810a07207804120a00103540da05185602c95640a40840310ba071810904040c440d0040740d0191171304000038007520100c0e00c09400000421300031016000000400a04034980892080d01242c103c0c130002c2001514544403407005410103403406070899280c5420405038140c07405118000d0f03140060041e62089a060004200c03040900450b2140030f00300400c1158104010301000d621040c074200315a604910801e503180d07080c0e403010b610b400c0740c100404c440003502020f011341454454030107a60141a10340100712490311412018040d40c1d81040014004219031340720b1920700a8140441904181c01c68480c11b40701080c02550783c0c69008000c42c0446203d42c003001c200d203841c51601c4060a940d09580c00940e1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 588181996 1250 588180746 588180757
    0x10204120b07030c080f19021b0f0c03030307110a020604172406221b08070810090b0640080703110a15050406030509030c0a14030403060f151a 63
    0x80850351500070442c0007e40641191b546812207201f195a604084030203907069443e480208400c0c0a0a1108006c23900e000c84d0341c0c9044180100990302d1580e8060007660f2203440002198414428113645600684480006101030003030b24884160b004540c09041d45401c00145450415550210010b80c0300e80c1c1120407260800c2040740c220b0f003400c803041d0748405401103401d0080300041c1041ca0340300010103080e00c40c55602e5400d94a83c06965200502a100d0708400d0703c09400e0780160001c20030260078160b1242c68241001401c00d894080400d584010804041c80c448800c4070428010211240203000d82104070b988414140c102c051829064540b103240703611001c1c020b82d07140c0142544c181c1c0c8046034040039000940c1d225142060300c0c040148150424000d00002c00c0c81d010228000e1540041a03520305002c150040801d08166070340c003000800c000b05400a28802481701100264080c020308290311011710340001c0c8003101085003140d10002da8803240c2e07000820780b082906500756008444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 588183246 1250 588181996 588182011
    0x61803110105090a0b04090c1e18030b04060506010306062d0504080f1b01080919061b0809010b01050304052a090702060f0703061401110708010204120b07030c08 71
    0x1200c00c194103005982c184111044580e0101d0034000104196401401410503580c0c0c41f5030400481483e181c095a900100350403003078015840d0300c00504080d03c03031000803d8000000304c18180380c0c2c0e80c9584950500c0f40a40d01101d40d02d440c2c2c003c0050039641481080c0041080307141010380d05c4102c0d58405524040d40074800b80c2c500b0310401401000f8095401c5030002c1c4948800c40d0000007804000030307103c0842400c00c169500700b01c20009401e41c4120080d502402c02440034100400610303c09541d040710080c001c650391515544010b80101e01200031b21641011511441c0076858604000c0d4212444103901a046c44014400e02010841c0001d0b11000c01910300100e100707000d2105a281d00a20410740116844451b240c20050034950200d5500d0140a0500582c03d20f502c941340d003a41501c906000362107542c840c1104150b415172141c0c2c000820317032130108255802d0589a500d0f15003603034003c1e0003215482e40321b95802010000040407450740102070345010010781b0400007005244500240c080c6 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 588184496 1250 588183246 588183263
    0x30c0a051803030a120501090b0603160309120309021521070c170a11010902010e191d06011416060b01030209030706081506041d04140d03090c061803 66
    0x1000e20061201640901c8001030480b600d82130390110060044030304032110f2010350305260001407109000e0080005540780201018150b0751207244414002910140d52820542ca130f030801e07004507075546411203512040ba5008540c1080c54014000e01080603d0702e401868820018080074640200c004006403600d1f10b040c4242e525042e00445009000000240540745c008801c0d0710724601c03a00040004407100c2c2c0f138680300301412043e12801c8550402019011400e1500c2c07540d458075280c0035041e042e00842584141180e128054030008a01007807400903204954000d00100d0360704420440d020b22100224203192a90740c12000c1c031400810350000f405151030f401da50566031302907010342d0409500641211100c96a98600910540050310040c1154402e500300c00118186a402c6805540c4211401120302050031084401e000c801001501c0c0b5800220754031403150014400030741e100c00d00341c1c0d021030349105174105406078a46a5000340c05000314031803d105144004c1e030120342100d0701310461 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 588185746 1250 588184496 588184507
    0xa35120f04150515010e0303120c031b1b12131203030e0d0c02040c050703050f030405010914010b130506030604021002070b042301050301030f06110f03070c0b0c030c0a05 75
    0x803945410b6840102805400d1104203c0489031520180241040036038071300d82904000d00502d6100d200d140310007000414600005421811000d0003560004d00400d00c200d085070711490411102d801c0390341c0c0803c60702020b03488080205410011642e0702c6c00fa1181052821480e540340b42c0b2401c1f49841558400c03603070340517210300340f5010f81d00c440c003541013a8040da50a19240c5800030585621030404a1140e0f18040010001501c01d60503551702a506444542c640b08480c1144550342e003001307200b20b40d01d6494000b80341c00200794200c085540312100c0008280300c80d0322020000d203c100c1900b07854146103801d007044800d43e40001c001e600f1580603280c982261204007001ca0502e200707904100036803100000e0014004244146044071012030b2401c5181c0725080500454284c80b00f84030142012407940410000304000e03501c804070107a0780d5520b051400c000e403162103a998004540e2080400c3d4820385000178002d40c000001d6104601d24440c900e1858480718295481c008c4980c01e41c10090042234 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 588186996 1250 588185746 588185753
    0xa0510030b040303180609020a1a0904180c0b04030b2503090c05091509010b040602070303180f060503061e011416020307030c1a03010303020715020a35120f04 70
    0x2217200c4044075a4880c3c040226401c080b40640b06110049014980e0154001100f9449104155002c0c0b240302c2000d00c7c0800c002d0030040541402a8003048001c11942c1550000382810071280042441c1094183c64a10354109226101c00c020155001101000b000540d104c100c01210083c01c942c0b42000a060703030305070070541c08040c041e03000160024a5a030501420421665034481e2041e412140b11085030380310072071528940640c0c031400015910621b03007400024092105445040c1b1050015144a0380e100c07518002620395502110110703000100340039103402c0681c44182e5054081d05801e8550720641e0008200b50450240e241e05041c01003070958038600c41c400d95a8883d60000c003100d9000d5101c1c00e240c02215147d20800a90903034407812440742c0300042d0f0035070341226015000b501c0500d00d00b013080120035110100c01d07030850190a00400008404207100300c185441c0300055240790b00c5002844101c10308511140201c0b030f506000da24803480495600e0b582c0000d080b036103079102d07444514 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 588188246 1250 588186996 588187001
    0x90506040b0711010903031d1c20011109130c0f0e0f09240306041a0711011b020601080a0215070203030c030d0e06010f031203050910020a03050a050a0510030b040303 73
    0x403c030300c1440d400c0c83c4140d8189075240c2c2200340c00213070038150580c00d5106181d50a43d00e1024440702d041d1100e0604016101c54000c8015801c1c4000b83d03020428030540206001f070842c2e059900352100050003050142941c145076181041901c070200b010080c922080c03101a15081601034100d040148040da60300041d1240b01e200154005e000d028020142400c61000000e1840b0070405000d44040d420160301c00d00e0700045a5002d5504462240a2840c48041c80c04500c0350003040b48003403200041c000141c43c1002d106402c6185012001451200f0280500a0400006900c24402c9900289920015943c1c0c1c2e4011915101c2da0361290f9641c110601c042429402200848440c0740000b03c0c42013043e404a811159451084070261102c90303880c0c105080c01052540009080ca8244400d0301080f80c0c0207a0000f40c0111189086a040c0f016443c08407060342c1c4406000030000e900c030428051501814003589410424200c1d0500c6146054400c41150f1b4860b44000340c040303002680440c0a040c0280e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 588189496 1250 588188246 588188267
    0x306060518010e031225080f0705070f0e0402011101021323030a1b05010503070e0105070317010f0e010b090d120504030f06050411031b010f1205100810090506040b07 73
    0x740503107620f8404401a04142c0d00a148981e01c03101b15251640ca40c0d91034084a001d074140d04c2180350b0b00301206100178100e107802c40c020440e5244180e2202107038108605013400e0081050005803042c41c5800c1c80010500c03400c840c040c0f0884d82c0144030146101c480c1d42400030a03100d2007154406c0f5104440c21010b030440c01003140f144c02d0300070703011607006108a0034021141e4920003800480f0b207035a034800441d0300e84001c48a200000340e2001c40c50312150b119600412104d4060f1401741821101152511002107003030b40009600d903240403080080210200b0f5460050840f00412070505c80d0701d002140c45020300090003004040e040614200560090090342c01a5070000003810840d03145141000003800140d4042e0355140501e2a94a081c0c9000078030401b060305020012454060140f0055850f0b19050702110b003809001074040320380c200c0c00e2003a68400c11070b00c1a540d0781d007071074106000d060013650102400820305102c0c0042c041400025079940040e408017604c121030b6100d101c00c0b02c1114a0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 588190746 1250 588189496 588189499
    0x15140d051011040501230f0903100f0b040e07080c01110708070602010b1f0c060b0312030a0f0e07080a0803060103020d0207030305040308060a0f12031b060603050d0306060518010e 79
    0x420302803040340320a250243c02a240b0030380743c0716503c41010122030b100e012a284002800c020030420810041a81400303849410b4018003212142ca030000c4156054442c2e45007003181443d40c401c00344855107050700800601d403004a020b044224107081e00e036034640c48654181814020030452240c45d800701000881c000f052203030280c602c3c96450300e03402400ba007000030075030b8031841c0701e009a9051640e01c858044c0c02d01c01581c5a1019102c40e0740d8406020b80407007005950300d40540c18401440001103002503129004003480024144600004c0408445030354001c9501390707100030014001c1d81030003e881600039411004440e1203039681d10048019104e407031600300b0300c680040354110400d505500710502542c030a4844403810b503195824032172243c0041c41100760302c03d000386040143d00340a03500213048a0280c80c054960279081807181843c140b8002044a407150f46100400c140711051256200140691800b4481540b4140d4020001c0c017030030002010940c1d56400f4085140e00501c2c548568920 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 588191996 1250 588190746 588190751
    0x804050a1d0115081f050d030c02031b06030a02030402030106030f05010219050f0f1830031309051801051014030703050304150e0a0f03030315140d0510 67
    0x403600031000c06071206115a00801101200124000c40c1c401002981000640d40d450b10135035540d20b00944481740c3c4400d0a00d07201ea121404142c54850720390f0011814000e44074009103503078a2040c14174082503c0144131402071000070026250b544d00046a80180d4808405601d907107031800042e006003e0340d40020006102102d0241c00c010f019006807208480084d024165062414000c0d1200d109020006a03500e01c01c0119104000c0100d0290510000c001580810300b144000070880c6504000680e500c0ca0194119004d07003081c03000141080e1030309c4100a1402c003c00200c0d0485024014000d0180c115100c2c40010b000901d0540003640e11091080240070504000703290488803c050300649000207680054440b0b1030400107920400c0742c0d030160042d868149042100000241001c03220010000b607940c100c2c0d4990f40300320303007603010b00304c2c00071550174480c514a0060f0032030b0014018800409582031040200045003410940c80501c2600d461030317140f075240741040c02e09110a00c142d00162 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 588193246 1250 588191996 588191999
    0x705100228110319030b04020a0306080f0102070209060d051f0e0c010e09011511010f0f140f0a020a050c15060a06051206010302090111030c160b070b040f0804050a 72
    0x142840200701c454010380300094038114407040200c0b01c81d0782da51001d4009034002c00c0100702d0100d5949007440240840d02e00025000e14100028082c1e90002c0000f02c0040e0302d4580a10035940c0034800154516141d500071882c0c061280d01050240758024049849110003079903043c103122050001e018940b2103444510b0b12000000b102000908850583c500703148601c880650080d4040c41c0d20300c081c8800281115901da2030000744c0315000b60752200540422007101540300481c503003405031000c00f508400010075901d02c0f2240d45011149010f503151141c1003010180714090b0005030300c4580200b401640580c0d1816261801c7d5002c5c40b070310441d074085d0320941c06007442c0303802c0040000340150403c4031003610480e07803000103c906008485d40780e29001085004140707e0343c00b0b54010601c000c2d040c100095468600b402480c210b0300300d00e03026841a08080b0f6001046d0b6900500400a01840368100c2d04013170701526003101c642c0b03004000500c0c0d10400a0820705202c0c00c4010b94005000050500200c1d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 588194496 1250 588193246 588193267
    0x1302042310030b07050406020a110301090c0617060a030213110f0c011a0103140a0c0207090c050c1c0c0611120c07030210140f0a061a04031b050d030507051002 70
    0x108030740e11003500c8a0700301d0703c0802c0e05148150100c0e01100e1881c0d00a01c00d10010780c40340c0382d41d111182c00f895450346d41c80c03a001c0001400f1100c01c00060801da03c031040d8810801d00030103444030005100301d214960080050006130354420400205041000d0001520016000c46046c04c0c0324002c25039000c81004940b0766a0300f40150051980d005c1200d0f0f66400480d1000019419a101e11440501c00246203000800c4000541c0c04110756800a104646189580700c504104840309601410000b880000304440400381c10071441c0381c1702050440000c9100c043d00390040160102d40b80080100d43c443c95010005942c0005860060a01d89082100ea0070584251070710703540304800403005405800c1384604451101e01c102c511a885020283e905990340b010380c40c0c9112001006030040c42d0f540d04010620b581000c181031110300c40b294440795190304604000d4038034182c40e071808106101e421801d00c4a62510282404100d625082480d11000380b443c0c010f08155005907002c1e0340b28400704900b00c91 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 588195746 1250 588194496 588194521
    0x717010209040b030601050f150403290708063f01021e1201051c0501060f0609050a08100c090e07080417030402150c0c1903030207060813020423 64
    0x1101150100881003c02080c1900c0b20005d00c18141c0c005000c0d21424814103007000e200c0c00d15031000110f5481e003031f20307075a410200700300d00c1024010603a201014280a06517140113160000e02e1814045458500380b40040d1b0382440501c152104032a18904000380d007105003480d00401c400c0448003150328111408a107000707401c80000801d00f00b400d6541201e1324000300c0110303406014504000f0185030b003882c080c09404842d10441713a042c44050024000410000e03c108005480034000c0d0341c003000d191240042c0794180c1a00024400d0f17482d550204600c8030002115008400800390129000c1c4490000750f403a8011640700e105280200010404031030750014900744a14441d80403035084030500c1807081c04a0000300c5009400c03402103c0c19200204540000d051800e4101c0b0840c2c0c3c080128070041a100114102c0c0b002412944000900c201038051107130b00f000d40b00780c0c80e1004241c44c00036076540710400303604c102070700030765865003003000d04c101c41c149465200c1290312204a6504200142114 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 588196996 1250 588195746 588195757
    0x4050112050c240c06070225051504030213050f01090e061303140c010b09010f0501020318041d0c0f010201091e020105130b034804082b031b0c0507170102 68
    0x103016906401030300f1400b100c0810107000a804042c103003236050005000705a00104905000020103000010050f0385402c41d80d00d20401e86800824541014000920060410f030410702803281050007030091200c4c00100b95520082c074441a010003802c0781020b40741c40b030308203204d1003011000140400b415441508031500c164026600740341c8076030740c030b1080b1848017030340780034250051b0001c001101506103501c0032049458001400001d0f1600840d0741c2903040c49010803441043e07004241007030708500c0e014048006512083c00207010044845d607445032400d00318410f061041701d00c00541c8066901c103405440300510750311003a04907030303440b04c0c5680342031f030012501103d00a4108861548164645001e0552007044c0000c90840d403904244007800c01044405082180d4801d000000e140f00081002c101814140c03400d040c020300c04a00e48507415020310842074240b5040c42042001d402c0768820500c800e000c41e1030100707a0400c1d240341503420310a480c0d0000060201c6103e0104160006500908 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 588198246 1250 588196996 588197011
    0x30c0403120207151101060f06021b060c06060607031404091d0703031209060e071412030f0d090f02040504120201140108030304061808040f0504050112050c240c06 72
    0x29184281e486040307a40722064022100e585030340410346403500d801007400720088031200d4000f081d0313030380c841c5464a001d100c03d92142c001031340305604450411101c041d87c00d0351000180e64030351412500319038103580c0c0e120203421140144030008848042c544154030740c220014103000c0d500e54551303070741281034040c0c00aa14401d141c403940d2004034a441c00c0008886c0c040701d0345074030746441101080012000904190b0001c2d82c0091312042c0800c040301d404c0c0710405c00782034034510741c0c02e0a040364403e000200d0103030440e05035030750301c10494002440c0d581e1003079039480410004041070712035881ca0a48009080d02c40001c0d001070416041c402000a810360f03401c880c1c0026802002a48040e002e10a1018028403035811950030070004500131820a80100c80e500140c4040d0b040982d44680c0d03000791542c003980c401100c03412a24801e110516040c000c2c0b600400e40c1d12052020007800d83c968076150024485128895014400044809184144005c0040c9440001a41c40d0080100540c0d243c074021210031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 588199496 1250 588198246 588198263
    0x304051608060105270703110d05010b0a08010609032d0203010e15060a0f260f0105010306060506120f250c02100807020a0f0819030b0f0405071b021203030c0403 71
    0x1c41750145c0008490507803030b03107100e084e01c119240ca00c1c00b0b0f00103104001c0001350705142084181c01e43e074140c1c0525402400d480d0b07a9950741d4507613080014070550040e0801e000308008030f01c0400c0070580d07900901d4a100c0c500c0d803e02200e031300f940c01c03601042c0d6031141000b13416508145101c0748242010511410340e0800d5898901d155680707404005084440d800380301c032107800c2d6032814400d1510044080b8416500c50031404002d45444500d40d140684c0e00a103080300360f4540006000f0820340b030240e0801000107490040c1007a02500c1100d2146000400012a08895600007402c11406011213014808080c1214186c0c00700408001d090740c0d04210240d000d410f05030030b1052801c0c4504000d610031403160b4050196440c0da5903640e4500c102540e8141d0700c1e02d0062001091940c400308a00d10b04001544002030305601c04018045566513a1010078481c0c2d16090400c045250400c80e01d440c8409042d082582c0c40c1880d00c002401c00e04031005c09210b80c40b02104000e240c0a1600c02002a640500440c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 588200746 1250 588199496 588199519
    0x30f2009041d210f04120309050d0c090902150c01360b070c0b1504050a050108030a1107180b03120c19020f13020a0e0105040b09060304051608060105 66
    0x2941e16401004410394919840a1141d10010100da0412120f12a403800140c0c13410040d02400000c030740041d00700d103100380031b031400083c10180c0001d0480c0c01454251850441001180c80b540501e01c07149c4030340c4120740c1d00c540f2080c04540c2c1d01030315200d8100ea1003540c0390716000f6940100f40202107002c02e16040244401010501d44082c1042080c4004a0440080170a4440d41d80c00e40440003e042c0f201840303a202c156000180c025141c1a204d110f1456a00300c444548a0402050300c002903c01d00105103400010303c1924000b004940001c001c505181c1d000c540301d1f022040c50162554032220b0080e0b40c4074200e003080130303843c0c100340c0c4550070850444040f43c0c005c08a40c0b0343c610441c002888180e2000040c2d00e241c0c0c45000341c035a00b460000f40010b01c200c18540208081445560000030038039030000d01442d405070080d060287c407070000c0c80c08905280c14800452601d20034405128880c0f00003100040401504102088805c8014407001450541c0c82900c07503904c840a029507846000040c06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 588201996 1250 588200746 588200771
    0x60601172706091e0601060c020a03050a151d070b0a120f060512150613180501050f0a06030803190e070b0726120414010c0503060f0105070f03030f200904 68
    0x1400e03e035503601314080c20080c0d1030702c6401d039071419140008907000010301c500000420012320140c410786001e2481b6018140d11303541e0100441e264030aa400c0d03581d802c000583c10b13900000030013506603418040c010340e980510905c00d99080f0500c03401507403481d0071310002d0388505034150003007001c49100369080200c4004030012076403526202c5007041c0300440c5800c00035140d0702c1c00b10070740f0b041c540c5903440004c0d10000b130500983e1611040d4205480980d101c0d010b000400003815081640100c5591080103480d0440e40d0341061440042c2501180d0010441c0c090307040c0b0707800d500c2500c500940d02c04071a40c1554441066800b900900e109546188650417030789c26822022000d813500210825046240c0b130404625281803248c054800c0d64000b5034455000b0000760b0034440c800e60041561120340d10f07460400204804e100b8400b40503410031006201200014003210040e4425540c5428042038480e01030300300000525a00c034905042081004400050390a500e0007085c1e45903003500c051251541c90703003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 588203246 1250 588201996 588202033
    0x5070f03031b030c140303061318020108090c120d111605040f060306230a0603020120120304120e15160305040b030a02120906060117270609 62
    0x40064003003250300705910740d421445403000161600c01d08000c003800d280b585880045d44a201c4000285603c00000c0c000c0300d18000708807401c030751500341042c828241d4552007245202c03009a0000d040c85440000300d50038034410720105100f4540508080340c46c0304d101111690b0743c00e10450410101f0f5521a540e891008082740ca2105500d524008086480c40c103070a00004224241ba5510455680c00c40400080c12901840c01d400703404d4504819a00a1408503d03803160001d4030103c40c1c603143c480c0420051b43c10441011b070807407031000802845000103804d207043c41c04584004450020000c1088200714000d560550764080da9501d41c942990f440040c0805040c4c1310b640550301d600180946181c0d0490f001d2400017085c0710749480760501d55100c036481c4403500190b8625043c1900441c40d2001d103816011400c2d8000c0d5080b0081c001b904080c80081c1030080c0c100d40c044442540e8a002a0040c80440c00c9942d422402c00254910004440007139502c0344800d44500f0114050007019034140f03011803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 588204496 1250 588203246 588203249
    0x90c0111060f0414100507030b0111150609100f06032a0806090a1508031e040f120201031e0b1504060512070c020312180405010305060a0506060d06080a05070f 70
    0xc03030040341c4548858030791408982d1303d540482c81d40e12840005685168071400b6240c003481d540e131004070388220b11200240000040010401a6600c40301c0100c0c0304801140100d500450140c2d20b05040362100c4155503407440140e08061100080c100001030619031650017011850502c059a0a00c145050070381d4050030b00e40e89035070740014000c1d0f005c512589009804d068102c80352100000f141301c10074507270005000c0c1d2944502c103240c01c0498502c03107a000e00c07001500c00c4620f50590500d06402c007055048291224050001c026482101140469000754442048100715a04a0310415001d0100c50b014010000103035005480c0b8601821241704500c00740c6003542c0e01602d1b65030030101c1c41d82441e070050400420702c50402690105400142e1170520825a40c5a00008081c1c2e940c5020118a1920700c1a5500c45000703a01d0b0000401c041078020810329040035140d030b00800d65449190028049018484400207140d240000000f0001030010785030b0041e070301c28002c0d500940d030741e41e911418500d080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 588205746 1250 588204496 588204511
    0x1110080f0a061d011701050705031812030c07021905010f030203040501060b0f03040b060d0f0204050604110f04060228030c030540060f14090306090c011106 69
    0x80a010800540103921500d921a610240024140d540c0e400128207079203481000303c00c0001d00c0740052089982d6080548a0b84040300002c0c8000c1c10300540040a0b071100800c0c0c080c21060901c0a01a0444140b00a4500003d40103000c0c1c0c6a00f0700c9a6070742075680c0844801c912401e0030440c0496a005440c2014044800507102d214a103e9040000d80c069400180b04498a550752107011030040110170151044912103000140c0320729092401074011303580500458441c050307064440300010820688411036a50644004c5985c2c0c4076040421301030900840301040c0400041000f0307584170707001e001810846047d0360807111600058a00c1d43c088460b00344103802203c0100d81503501180c041c0000d0000d07070b40720740750980c40d0040d24403821040c81c10070340044034018207041805000308144002c40304420f13414648060030610305440904031001c0c080c024000d002200413103607275001d545c1c401d40b0102040903054070340d0b51074031001345510f031204004400e010500ba0b1482c0203809400080242c0701d41003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 588206996 1250 588205746 588205757
    0x150a1b0c0b010924080102071a1005010c050c09070f020d030621030912050d030b03032d0904020d0e060c031303030b040209060d06030b240d050c0910031110 69
    0x800b04668003400e08500e0203003070382c0a04d8034003058003522007882c1c80c010541340c0c00050320b90301580303080e0740a05000e0f001003180c0000d84081c41070046c50503440100700c400c24203001c018140305281c05410140301d0320b4500d5001031140100103449411421071405451a50300b921101a01854181c04541140c052081801142111207084c038060320310354a2418000c1c00c016000e1640d44031074805158489808031150340040300d82501040d018040c0d4940b48008401841c00d00c03450714094000e906044212000b071403010200c04000d810030804031074888101500a5540e42d20001e14480580302040188549100b03840006126202d03600980740100c200e08400d415481c10703510114060324550b101907500036402c200400749940c1d4007000340f00480030b14a01045484c914200803c0c902401000400c403824080c2e00c00d40c4800c2695402c0140c401c085850115440b41414101d1914440f50070094210070300380d007808401900158942c084034030600322030031040000801e11003039203449842000481c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 588208246 1250 588206996 588206999
    0x601050609060c070b0403061505030c0108041b08031806070c090b04060e0f0f071b02010c08070b04031806031e0902040b03010606030c110d081305150a1b0c0b01 71
    0xd091401841840401420b0741d0a040081404905140c2e003a03202c00d602c0c1000090810400c0100c0c010003945021007011040076618002c0840e440d02205440c4038100708104001600300700e0b6100c082c810034944141016080303602d500083da540c1e4401140d010703200d1201c80d140035140c82c1040c1101c4080e588201c448005a00c0d10180101501800c0042c50380030b0340300c24010035100d0b200814184905000108060241009215100c4005026008008001c00020810b0480120511041c0d9299081c0307441c01c081a02424400a0360043d41401023080c3e00110a21090643c802c200a84045448581008442e44c2340416000c98404281410481c1e1080100c1140295640e01810105002500116401c100e4500003030854080d50000008640d5551840f646180d2010fa180c4100460300300030034200b0803980000d822003c004003410040394006800c0001c202003846544044032142c0441c6019081c0b0708003031805402111288540580c80104e0340a9061041701c000000301e8020380183d178142d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 588209496 1250 588208246 588208249
    0x806090d120e0118020f04140c090a1d0130080307050915040810150e070210140609060102031e031b130311031c050714010c0905030105010611060105 66
    0x355003618191009540c0341c02428910b2028010006500c049440c08200741e1102c0c410413a5001100401c54003507490150300d0041d00401011154005020b04101d40e10369425400003a1090b1503604102c81c80d208d00340000e6a5802e0300c1113024140c0300c0c00c0c00d20903c04003c15032460304107118002c8400703904641401c0f04010480c03800c01183c01c0036440c03500d00e281c05001c8001c0340218502c0524101900300c00a01000201e4080c030005848010009040c001e5920100d2294503d8801f40194400c4082c01404201c0701c40c000c00001c21040d260080c10b00c0004221144500d100d00b003151100d02480b40200001c60030340c03010040350384802513803d500340601262091076125410007409446942448010302a0300700c10000542450080c82c10407515850840c41c040c486220701e0036102d80654494110081c03401c240d5410450103a2082c5001602c505070781c14003440070802800c2c002e05551810018611540e070100380c1006458058000740001d9903070304000c07151400d9920207000ca43d0044401030003503 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 588210746 1250 588209496 588209507
    0x60b031e0711060f091c170604090b040c06030b151e0409060305160501020a0206070b130b131b0524070c0f0815040b0604050a060b0a0c0303060806090d 67
    0x80601403030496108021094080c3c50034078199202400108100c08004843d0002c1240080d0401001903841c00c000c0c42030006001030b5030b0304079181d02c418003060015081c0c1e240c0f44c0c8403040007034000f1440c1c202030407d81000261400c4901a41002908080c495076042c00d10360b41411076984c0d044040e0f8984501030300040c030b9040704401c8089a1100c1080300258043d0341d40104400b441c0114003a051982d24203006203401801d96010b5415904a0b01d80d030400359a54209640c1e240350084800089030780e500105c081a6080034100405081542003401a42c04508200018040c8501e16140c880401c16441c0d00c0301e65528410315a0108128000482d20000141d641c08103080348100c0a080130b800340d41c2c0840118540d088281d600843c40300400c1164820494641151841c2095109505090322206082072000302854051611074000c10315600702503000d41d00900742420400c2d00d607050310900401000c00644260006401c0030300c00710381c0400c040b0700706002e2003450700105500404079400756807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 588211996 1250 588210746 588210751
    0x606030105100e13020a08010839031219031e0207021305040f0201020d0309033e0c010e0a05030d0305061801080c101e051b12030a060b031e 62
    0x810100c0c5500f41c2c1d03a6103800586030051000a1405a11074500010040080c0d00590103032015a004d41865801c0c202c03082078a000215100002620400f46524044c0b0659403000720a5010702c28600242ca0034004070000d40300808a18241003490030b60110118141e40071700c1440c016505d400b261704010408654000c102803071024249943c2051800a82c030100d920407103082c0d480c21004640c3c0003c42d81c0c14040c01c6801101c50404005149254034000c0c020412882d101c20312112100400b40c10b610304102c040d0503240201440c516202e07201e801c80e41c43c0e201b100f100a000c103900c0364095060b8541030103030400303845010b00100800c24880c03008601410002e000250092499030411034031302004d0720b85034040c00700e000c02030065203054010300c00842e41012804c000c002c008140d92081e0710341c00d10101448210b42c50115181c55514111060881c81d9a00000652254440550b840b04150026520401400324100000703566048150345030710048500c0980c07010150741800d81d10400d400883e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 588213246 1250 588211996 588212029
    0x609040c05221802101404050d0f060207030201200a0206041709361e1f0e0a180c1e0e010e04020a150e060706110708040e010e0606030105 61
    0x8400c2c4070500c046011a03004405440480c0c5010b00d142c1c0560030601a0350450418618000043c5444110051460302507406500e04c280c8441c1e4101051001d685603168049401c81000c550319901071401a000b082d0601a40003031003000a2060b01d601c0e900d4080c0c41c00249141c019001e990f4480c0d482c800d0710b0100000c4086004070500800301c180d01c80030200030b0785490541407403e080b020314041c3c031300480c003043da40d040591503031040240d40307100250500400441010510105d44407002c500e00002d2081286100c01004e0f01800210810044000b83c00b584081200308090700c00000002841c92074441c0160070605c0c00141044080d0900c445c4016032108003102109203a2600c00e8400d01460a84c00100c031a980c000c2408294940240200000e00b0440d01100701c05141c1340014140800611506100b010003107802d02c00c5c440c141d008a491040392141d003698402140c50b003a00160483d00a90300a00d03010000491107840c11114503002d040700502c400d003140e28040401140c40750303110424 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 588214496 1250 588213246 588213289
    0x5030d05031b19080a02041d070c05030d0b1504081f060302100e1c031e03020c0f0f0607090e060d03020c03120418110703031805030f120609040c05 65
    0x4001004101d000381211041078401ea00c4003d5038a2401010100044d01c00e0b110b0501c100030821110328201a0351602c9a1100042042a9203407032003034440000b900c001405a0000103440180d44840d58006c1c10ba00c1000c9514001c0410701003140540d0340290300031802c095001ca0300c90074204c2c5600341e0007008842e400001082c0d242d01d950100e0083d00f01100038a001c104e06200301c10051803e0114011400701081005c00a0a0030352401015450400001114000010004504188281c0485050f0748004048818000310760180550b80c0110110140b1079014110228008030322854404003220710150340481982c030703900c040202c03500b0903410813015489544007208140e2414000c0d11340128515503155129850244440c08031500042106031140c40c2162483c4c0340c103242c0c41070320304040d0140760004060b003a86c006141e00f0000242c02414920020814411040c0d40074010103500d1031004100010b03072a030400384441c0001c1900c004202042e911020b010342d061003900030510040c11100b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 588215746 1250 588214496 588214531
    0x160b07023f0712050d0e0d0906030203060f0a03050607020f030304030c02220f0b03010f0204080a1548020c010822060209190b0d111b030c150105030d0503 68
    0x200d2520340048003c2e140412804144208250402d00c58038150803100030103002c5054855100500d41c069500a15060640c08400f1170919121848a080c03c100702515500c9096200e0420076a10002241d2820041c4181031035501052030102c01c0ea40265030646406848820940c00c001250b2000c1211344851050301200e08010b07412030150682d01c0d90030110005000b804d040c245030035982611541000c030750040208011311080000d11101d0f040c2c0125140040300c1080064002504c81c402107070800303202c400504400816032403001c4003141c41302843c54414465940340038840107004d503000c6002d42c000c5501c049039035000d580207582c002c1c00403414400900410f4108601160086000e44070785601140b015400d0409018464030002502c001c00301851825882126601c541c003100340003903864608110a4043c000181c40d50600d0340b0108006600c400f9207044e41c0c98100b4040003140e441000389503003298900c005250b06032500640500b005140344034064500c0e81c006010343d501500030859 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 588216996 1250 588215746 588215753
    0x120807062406110d090f050910030512040e010e0408040b0a020f0111070204060806100303120e0a0627210c0503040b042907110303160b07023f07 64
    0x40c0c0c003801c2c0d280c55104020045195581c58000a06140010710100d240284041a4081c41e80021540708440b50b18aa89c5e48501d80c02c14007030f0590000340306218800041e140011540050400d4810090103880e940e030ba00c641500d03078000141c5001e0a5440d08210610032221020000c0203260814011510310750b07000341a4500311400c140070280e0000021882c101103103414083d510052011400074240c034101002000101c00c031030721000f010f20001c041101c070005166000aa0007800080940d505942d06040071030103041c2c00340e8001017a00c0d140c0c100c0440c1900130103040c42459080880b016400a0100000703040b004207890300024061200b5140f00003e038100000c1014080900c81075850743d203014080c4040c09441d400300d003144244004217000c1e40301114145d442c89038200401748030511448012070701310312400c1c00c2c040180083c10f1402e0284500d03000c0d140d00401007542221a501c0c26490032031501c110080e038000d12040e81012411260361060225100b4500326021149003030141d54 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 588218246 1250 588216996 588217061
    0xc0c1203140a0e010f02031608060a1d160315031e0510091406041e0c050306070e030d141210080f060609011502030a030c0909020f03010e0112080706 66
    0x200c5030005161640c80b460b00040d002c0c01144d200701403045e019415424071103d00c090780c490502c041800c001d42c40300020025924200322000402c40301514062480b0654240d02030f0403012038602038060080003445032110300c40d100700340151b05044083c10307046003582d455480c860030103141e40f04060f41c1c1600440c08070314284080751081074490b07000070303031060640381071051075481d000603000b550030010400011901600380d8580e61403c01c036030705041d01d2a40c070f410240c0040039004150140314180800c100b040e00b180007441e00250032000c803001d130228804101e45081f2030794a0320340542c2061040f09009111840b1441d048515401c0c407801c01c58075034041d41e02e0107041d10203498140c0e00840038402c10f4200004014090725007505c0c0050728120101e4086e64034170921140700c0c2019982c1103030980301441400c2d44000303030942100070f56450302c7c41d101c1105503030000c1c0145a010041203000060b038004c1c0d1420a85802e41c0000414242099074070b901c001080c01c80c2d0074104101070802d44008401c0703c0f5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 588219496 1250 588218246 588218251
    0x305041104060b1b03030613051f08031b0102030c1803010b0301020a1206080109120522170613110111101506031a0915011b0501060501080702010c0c120314 69
    0x40f001d07142ca80010228901300404a10030149031500100280300c0a170711010300c0803800c0d00045402240710340383c40c686080c500c14851403080c881c540a040c04180030760301200a011440380d401c03005030b42d9507280c03120703a00300c0c813081c1d030400342c8001e00f0040e240303081c94a00e00c3c019002100400001c1c540094401003804da03407008080000040c22552200002011445090050310741c610003001150a6941c50503001800a154002400760200d565041c1441c1ea4a25080d1080204410316075195034070129000c1021300e09801146002c1c50000a500c400654000c4001a4008000d00313880f800e07100041d141c240442000c50b42c0360040d0aa01d040d90b0a40d4003c0c41c6081d02080300c0d0b0302d5402d01d0b24100500321480ea001d14031550a00000304806640c0326444150030800000e80716261040040042c0e074245142007150040711800810320061103419480380003100c07400c1c0c0b102070b600d03541c0b44000c90072980d81013507590100d92a10380200125054003142c50514207182000500c080c20680c00d6140003008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 588220746 1250 588219496 588219509
    0x8040b031b03090a0303090f020a06080a0b0915040e0708060411010305150901030803190e010c0f020f0a11010302040302030a0b090d1d042301060e0a051f030504110406 74
    0xa104600404065a8014410455a01e8214103050b02150b48840300d41034083c0426031100300820500400c8c507034906500d5802000c10341102d40c2d401c405007060504448601c8018038010760b00700c290905038070b850b104a80035010b0041e4582c000e402c1000503e100c2041e00200d220721580820100c0d4200030b55400b0300d0007144003c0e960714940c1e0004080d10401800d4016090000708000000d48071855404c1c1981c4d80505265180c0c0c0d83c102c11041c5081c00d8020500d15542088056120100194029444640b555903002104603070b1000903a9034000c101c1c4000ba0b00c0d03200c1207004000c1002002a8045994140340161034160ba03500000d01d014418582600c400464406226020300200030f2210260f90b6810f11944019101c0740c82410058890501801142c640c1d0f1000041281d282003510081550070400340346503159180104261401d8001500a0115400208003440c0080d900d084280c10307910305800303810000324102c0140c940a4011034a89004880040d07055a850244102610f035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 588221996 1250 588220746 588220769
    0x170c0d0e1914040e010f0207080403061424030109080304051f0b030d080406330b0906161a2a0901050909040c08070b18010905031902030106030804 65
    0x200310410400320341c680c1104222a00c41e50040210791500140ca0381c401204807070015140c04004003c60260100e600e000c03414510002e021800c010468000d40142c90042d0400c01920001c840b4072807281c481550303001c684800045015135200c408088564000f0b50140c00820701d0a100e50326424903800c00d4608496039048000c2000304500b1600d410040d03414010014094810f0100200b9194405160341c50200f1150790300080c103025181e0403208242d60003d00a4005506040001d003101525003545c0e003440c0b0000000086001d40b100907201e4180004040c00c1c40c20306940d00743c0001c12080c14044550030b14404410320210002000c01d0f00c500600250100b0461204004c42e481261030890103080c003400f4050035540b40d9000d0160741e00d0000942e61000540c8940c1001c140d0301c0010780c068050791080f103001260000e05c00028040600c03540d0050041c0801c5100151070101e400c0c00f405e60554450600745c48841c0450582840040c009000059045e840303444548141e40a03401031070030000c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 588223246 1250 588221996 588222017
    0x1f030804120209090a0c0510030b030303130210090e180a0506071101240b1e0408100605010809060f130f140f0601030b060d0c0915090506060a020a170c0d 68
    0x3c1c14090140c0c0b080600f0003070101e03002540d6071074441c100203000b0380340240100200005440e0007a409070f91000f030014122900c038500114900f5080d000e02c4e004a018003180c0980c002594000d005050a50780f841880c50150781d600c4901c80e40b0140c0f80740005e075a0f07115510000d0003241c0140000781c002d16070307540d9090100c0e002c401c115080d40d02840c902c0345040c0e180d1030f02c00c0743c00c0d980c0c88070350040d02e02c4810300c6a910883d80081c006070242d100380f90404070100043c009008100010100f0091341214400d010390380d640c1c801035814a20494440000f50046d034001307080e18002c90103031580014011004004405551180601c410320307002c00325140307903410203003000c03400040114000b40c06240000380441d60560765060300b54040600490b000c0c140460000c1c040011030100c100c06004d0202c07081014032030324414120251940d11807000410324040c0440d60301d043c41c4003200c1540306250020054880613a59954205e660f14041d04100941400070b07a00c040f10520003241d00340255900c041420 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 588224496 1250 588223246 588223249
    0xf06010644010f05031b0118090614060702061801052a07080d0f11030403080f0d11040f060509040e19060c02010506010804080a090305070f0305070506121f0308041202 74
    0x4800680100c1c0c1142c03c030000070807060780c000940c21000b915013480c07203070581c00c6e010050b1801411070320905d408040d61480130614015641c0848100c2e915114800e41110150050042c1803103075080203134005c0d00c2041421080da940800e842c2e441c10042c908640b0709524613256545480000318000840c404c10900c0131b4214a08200c600e0141c2410405060007018801015000c008410829014041e5a6000b80d200301018001d80d00255081011a551558000d00042c0154006604889003030310300343d0450121403080c0c058800342c9002d4850b1802c02ea080c02e400340d840d40c2058407030503402900c40c1e0005080c2c04043c000c54509580703200d48a5000b40c65031905034140c07100b00701e5100071680b418041055603070388000da154229411001c250ba5681042d4401c85d01c0c4044d0340c0014045214020000904101028000080b03901510540781c4a40c0c0300c1003041220300c90180040c080c2d00c035140100741030200d060584d0b0030081c1062000c00c0d80d140e4960f40c2000301d4005600c401703c071058024011065 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 588225746 1250 588224496 588224627
    0x3100b0408011d1605120f0313030212060c04060e0a05120703290c1b070311011205100b091c112701090b01090801110d0e0f060106 58
    0x4110702c032016103854000213135010302c1c0e40e0003032041c03d00c50407066040d94040c401c1809001142c0065405480c0d41c0c48031440111540e16191000b00d000b120a8418803000b8500405c00e60300030f80007a0149458640303081d00072a003040400004642c020582c007000140da5940260741040b03018603401514070649542041200307103103001c0c0340d81d030403a0280a10300c1e002c40f0b01840e5a0b0707000d6500b50080c1d0f00d0700c00c4d124918001484016070300c54140b180c0d030004401e02140b0071010407400000d90311503000b1040c079842c100a540098906440c1d443d2007803402d0220035888006491020009000c0550303003040c125010003104064281616114011a5640503d05104503048142c43d441e540400c8907040e50250000580414424000c001ba55400f0304045603200c0c3e0504070080c0301001c0207118044110b102c07684168000c4c0541d004140c600343c41c507800040d0204000040e0f4210b180940401d03880c0080079260303031b542854402d00d59407044e9104000802030400302084c013040309041100c101640e01c2504d14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 588226996 1250 588225746 588225791
    0x604050d140a020d03020f040b071a070c02030c3606040b1008040f150606030e0105100e070e0d14010203090d0206101e05030a052416030203100b040801 67
    0xc00100304158030700b03035400180701074160700039183c0186d8941149404e0744190165400600c81c5000024901c800d1095010281500045003107100a00c0c1d180c00c0c109960141807000c000390035800800440d0010b207040d80c0b81d00d6140040311840144603045440a02e1761010030055508440c14840030b01c04c7c24145407003210350b41c044c281d80c0b11b0013400ba101400340a440340203000521981949074124100820300355036101404014006108054542502801910811031500c0c41c40d864800000c038001c1115080008a51907284d5800c01603c0314a82200c2c0c00d0351409007150003108855000000503a1070300d005030302c07003078401c00180c03030b405e0001290f4246280c0450040840d030050b0107120000a00c03507845011290340a091a2402141c00d01d1450001001e90050380e1601900c1072217424043c2c0030850301208501144041c0f002c01d02c03400c0710f81941c20705035460880e1041d4401c0c05140d40d4001d034011500718202c0b000d07042d03000307a4911104820394015045400e00341d46a84000341420000b016005 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 588228246 1250 588226996 588227027
    0x1502091807110d080a0203130206040b210f070507030c02302d0705040e0a152901031b090f080c031011040801060f030c08030313061d0604050d 63
    0x41c0e0101c100600313008000d02603c0d0f91580c00000301c0c042c0640c00d0800040c542d405003e0079203650b514140c0c14035903003101000c1c040d05041c01104044601d40300508500c0b400100e140705109440b80c080c11100c0c0d4005010440900c15442c00300409642c4100c081d0184080100642d0150145220a4071310305050303131040001540b005003081c9501c0500000c03013a084481d114170b180c03d60640846103140c041c4e03603403000e031b0818a0200c0d94040c0c40004501c0c4510f0f20b00600b6404008804900c40307204640d010440800e075025441c175200982e22042554220034074051502240d00c50f174a03401582c0126035006000045000e00780c0c100891102610020028103e4401518040712118040b9071508481e020910160b60f603805807c643d61140025507003d04040402003010030f0300c80507441c00415a41c0000d6070891442840011901000030880e449604800420341d1600c065580b8080070300400c1a50150800a0b105031815485041120b5407103103004000030030f100c285807880507181c01c0956440c070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 588229496 1250 588228246 588228253
    0x50a0b010509090402120a021201022d032212020616230a0908030d06080705060301051c020303090636010804140c130b0102010b030705010c150209180711 68
    0x1030342e903a0368102942d801501607404200010703061504a04190400c0c00c000d5000503144191401c28805601030300c21182007032a10155084000400b2000c4010341d0a880036404040000070302180400c0700d20380c1c14280600c01c0e520305c0780440d6608541810011001801a4881d20800807190f1400b41020740050450814220881314203100107600741032800030300350720300d800504100001d210303040460080a80409036a00c8415440c55030002c3c20ba18801c0208500c00d2581c085075616048003244d0480f980148101e402500381c0c900548134442014090340d15010a11850005850342801400c5584c0e04544201000101896031402e4000b240d41001d120f5800c084ca402e03071740e60840c0b441038005801c01c14071035030844144c0c00300d03140091901070380d60014030742c404408008409030803c01c800305c026002800800b6510092503552410340c0301d40741c0040c1c00c4141c110086002c002c0301c114410a00040940360040a0b40801d180d081e410803111101004c4004115091364488061040c812a00016 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 588230746 1250 588229496 588229507
    0x170f0f0c0337080c07020907110f01271b060e0108010e0c0403020d080c0d1e0f0f2303040f0203060f0f040209250531090e030715050a0b0105 62
    0x1070710001c054502c454040c0070041000c10a040c6481d000d807081a42e0081118011f481c00400040840321220000c01c414400c0301051000c240c41800381c08410440f0891805201400003c44078010315620f40c1038034614200303040d030350034058042800c201400b607603250103003080c52100c00100305000503403005c5910001a014003502010003421a41200d404880c1e000c2c1d01500c90421200b5803184020340c1c00c161042c2444090401d403c0f014400224000d0440d82d1061000442d054071180041b800b01c01c00508802180341200d03005038407814403c0030140f1443d146040d0841003414561064905803480d010112002c011886c0030805564404103d122840e1141030240c8407d582820190009220309040e030300041409085c00072001039020350600ca46c0c0311030429200a08030780d00100700d00400600b000d11240f0158800403494a036138000b01c50542845103408100c0005200e18070040080303000800061000c0765440c9003032103a28140f4580081c0c1410300c029110b00f00c409100740c003070500030117022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 588231996 1250 588230746 588230827
    0x207120b011e0f090504120216170a0506090a060b013209030124050418080f132304090b06040e030c15010504050112170f0f0c03 57
    0x280d1411103640b40c2c14400b9280408030700082c03011050708a65020356400c0c0380000c40003020f810880c040d5009046030300c0c0f004600b01040742c446000740c58466035412405004c22422a541110b0316280003160142c03042d1000c40d80e90541422000e8600950607400301c0300100512502c1d00c24540718402c00d080102c1c0e10250801100003001ca40d0320400070b0808a00100e1516000c00c1d8111212010700400800ca5101700c42c0d40e100c101d00b240d1000e0083d10514050105440c1858840c2d01c400e80c50700710a0f2070542c42c03656030314400c50740982009250a00b0900c6243c20070241009000c02a00d0801140d50b01c0750081c81000c0d02e180842550684a50300300301840e0045440207100941100741610049200c98040000d503181d0321900360072001ca4803941081038240e8880c0d09000c4d060303400468041c4039990341c81d07440301c46c98040d0003000340c0303082d2226000420049284000301216110f010459040c1f220301444103c0b0740d000f00403803120315040040e228000c00000c00e8540d1a030300f084415401c3d0124291b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 588233246 1250 588231996 588232013
    0xa021f06080d05070510050106020d080a0c050409050411180702240106030e0f070b120603070b031819030305091606020d030209030106091b14090f010e01170403020c01020712 77
    0x4150824014006444e4080c40010311900700c50101412082c021569101030096968140c0c4100303100160041c408545815490300800000405556070301c1d051078181003901d001410054002c40702210644c15144403a20b03441c4000b0b0420510031041c0004c0e20b003542c0082d09224072400d116400709102550614052445840b080c1034400c5468001100d81d0800c0180340740c01c1d6004010303c0e00e44614075000543e1441e1070018540340800604a88141d1a2581490f0b0b0300e010500449506110a00001d040382c2480064101aa05c2c4a400c07a1201500b255005610721100c800c25030000ba06e5201b00101071030100600741c1d008914114080034185441030003526198803000307200c00c050f000644ac00b015030b000d4219601401c01d08000708202c9001c0001200009207070354199021810b080c5c110200480132109464407001c015009560940c102001181c0c1c81c203000d10000d0620285007000350b950000741e8030051040340b09400600000092100182c50032565a10010250004000340303000900c256 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 588234496 1250 588233246 588233263
    0x4050f01090302030f07060f0305371b020f070e040b0402060708030a0f061203090b0307050f030a36080d0204180903090506072402160605010317121611030a021f0608 73
    0x240260000720110540034001c0b03510781d02f01440724509019407100c4d80300c4810748004a080041e000c6480603440c070030800f17440d40000d10402c421402c10f080020702080860b4001a4032500c010403240c6004103503554081c0c80e80040d6007240c5a19580c410004805d81d41b44203480240c10041c080d945050031540d0020300480d924000c4010803407011002c520100d01580c152441900c038105410780300e10b0040f211000034907115810442c4905000603c000c0b0704000442c0c0c0a074165000c100003c81499a210099540c0c4840000c0d18201d6003040002120001c842c0f060070006564180440c0e80107007030900074541c181982002c0d00c2074400700440e900140c40c8104a14500c4100508442160f01ca007074000f0090140070b0743c02c8501a0140400810003150341d00c000d047ea8425038403258800701c40808400c0034060a802505000c3c903850102d00303503d16113041c0d45006585480c10102c4a00d90380209810b58000201800c0507034000c0040f4500c414a04141300d40104a08a080000034030b021152541c50040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 588235746 1250 588234496 588234541
    0x203031801030605030a150606080105060f0702010c300801060f1101090503040609030b070207060e0405061306260118020d0305120c0d050a090804050f01090302030f07060f0305 78
    0x8503440300a09034040d8015800815006050313070410002820041508420320003490407140c0380c1180070a2950154540c0d505841c400350507282080d00e003c00241c10f03035101d000c05905100d00140100006103020410491041080b80d8407400920451012b84c40c000e070107607040080c01400c42c0103124950340801e40c864901d0b610b02d0141012940409481c0c01003c0d125405085400002000316984d9080240302044900c501c9030070100d0340e5a01d00890f00c1d502c450161200040c1c00c508400041e01d410f421541c2c01201c0100ba0201026603070800c202141c606a101c0305000c0d145240708d524485140c102c20112000c0035000b407041044181211810008090001f481003220384c02060600d842201624210a400402c0c40303070a003401c0795001c80641000c00841107141c03c100014105040e0350103a861040d50282c0d1843c10203050004020711602200c0d0564100301c50804000050b950070018586410f0844010704132003030810030b00605070305641c00700b0001d06042c80c080c00580b03044e00c0c10740c01c0e802d1308 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 588236996 1250 588235746 588235777
    0x20313050c040b01122403032d080403030e19060614060306131e020f280c1412040e06091b0901030b010311070b010f0906060e040506060c0601080c011b020303 70
    0x380c00740401c40841d4030b1645140c01c0e5020746c80100406400070341701545008072913130a240300000d40c0442040c00b480800810001000c10020a0009020780c000041158000d416a011405c81e4155800903030b0b03541c0e10a848840e21454200700c10101200e080b02e513404281c0da040c0c44c42c03034030601003030806c0000452043c2440eaa103110415211090354450302110b0b00c1d100540d6030f06c0c2c0403840b8002e1608403002140100301d08010400d0307a01e040a40080c01800b03e40c0341c000351481641c58682140b400c030040329040340928112030706828404c40081000d03050b072001004180c1001e2040c405a0319000f06420b85010146030100c0440c0709000c10b440c041c030400d00e408a03c0c1840c500040300a0400010a080340580114401c1c00700300b83c00c2102c074181c82c982a110291242e581051005441e50340c030032980455004441e4a0090506405c1164040000342c20b5520b400c001003100d61078404268003017003a503001004204002e40e8402640d4a113510441d081d81c52003c11a00001d80328490301043e140e1602 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 588238246 1250 588236996 588237011
    0x40c0207061434080f0c0705040614190503030a03090b070801051c020604050d050607020d0206070e21300a0f0c1505070309020315010305060414010f020313050c040b0112 75
    0xf005521128820343d0b00c200481e49811290b90101e0040d08a0020b41000e402141e001064504141c802c4c00d040b9614400c01400000c14030f0f040c005603190347e5144001041444801040f9501d0400003003040d0781269400268400712410a01c0204401a06800801261000400c0503036103a580c0d95140942401d8203982032409440006e80c43c2c4601e03481180c204000818105c01d2007004100140f05a00b0f640a039041040590b10482e01c410701110060041558161111098200356454003002d081c421142c480d07600c05110075600e4800300c40c1991100b00b0500750300c0060040b110300341e405074200d05a80c140c20803488500240454050407070300001c0081c0c2102020034401f110b80c6480c0c2c650302100701040076090150004019120100b81a8020b1007810b8589100008210b012030403a5000340203030010f85ca40303588400148842e5811445291b48903000c00701c0d411103038401180100440c40e0a2201210035140c100e050411810007188541d241001000d011b980000502d100d19010b82000140813 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 588239496 1250 588238246 588238327
    0x30115030209040507090518010308042106020c010e1606020a11010e0406030c290a030e0f0304060f090501111b060c070e010608061f0507030e040c02070614 69
    0xb4002e51160552060421050080d0386802c42c0f01c843c01e40e00c007a20005c441c0314803083c004807040c034288001444107004000030019214031848910392010907900c410b00d21a16505c83c94181e1300400ea200d0304d20b0b5511180d080004408001000d0818004165540240d10303007038010751500580200a03000c01c284205200d95a803080c0c071a4540c03c40001c1c42049400d031079080c125130080b518000d410700c0c900058001e80c451101904190303003000305580f08500c0d011081500f14003074000241c4e86a881d214032000c0f52a0351304140040c0000d0031040d546c40f003001645450090003400c1c51350041d0b05015120200607698400441e083c5001d0dc88143d0302d0480c20911004500284200d41c8011002d0141950208101c4040c0003064100d40650b030b40c42509444100811140d100e545030401c59443c28112512041ea0003200680502c41c060308005940300422800316090b609031281000040e0806403027882810381120f41c040350f50a418915600307003a0700c0f609248165009000c140704140304100c641142 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 588240746 1250 588239496 588239501
    0x501080a172104030305040c3f080c01020d0501051516020102072612090306010e06180c0702130c0905060309100204080604030906020a0b071d04051806060d020603011503 75
    0x4903400c102d01c0302000c0c500b904004008140603a0f040780c1c50007840d4030000355420030102484442080000d013003092460380140a0741c0840d808034031003420b911070f5500c4010a000002801c041c0301e0380c80000d0307620a000c107041422183d058010070f200c0d130701034607810400c0e0000b401074556440104090901007240f500040c0d2800404d40e0015401d2882c0745a1440001c48545800488422060480d40c0c9400d200c103003d4040d00a000c80c00340c06a22005c010814102101e003540d0300002d0191101e20742d80d100b4800035018040407610002103e0002811800718104140786405034030741068100011048440002c4c400c000038442c40e8400d00c40440070820341a018000000c42e040003d004540e034070b40c1e41078802d8856030b0403581503000c5540f00a0005500d800801da4904a035400000300107980d0b41c0c040305071894078403400d9048101c403160b4000b112680b954070a4a01424070001100c010700140b8403042d15108008120a025400301e001040061b20f40b0810b82e415550790072001401e01d15644003c800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 588241996 1250 588240746 588240787
    0x150f1003060c2709050c040e0f07050d0f0603050c09060f040c030b0405010f1508010602070b03070e091f1e090e0f0d09030201030c030515061b01060b0d0501080a17 72
    0x41e0045103d0345039515080e2040c44000316000c408051045503150001c807802401503100710f0742c0c400c241c0d400051201a0110300c55501a640d42811424106003c051001312004103040c452000e030780b40e0040c01444010070040200038801c9810583e989055801310b1020a00d00c1409406551070384410b0302c999000f600f042c426003034007500410031981c1d0340199004016807482034030f900d101070703a40107000640700f1038001c0d05803407a40c5c000340b1660740781141c803034060740c001000c04080200c002905c1500740d5490f030555010b03a9400039128000c6c0070302000700c0702c08012a4001007080210a01c051851100400d846049401a14000400e0014828288d0030410034400b00300b0140141c0c4019040c0c00d420103a03060a4a000780d90401014011003802d40407a4030a40b0706190006000300580900c1c6810b0005000f0b11034920801e010300c04805c0d142500b511038a801602e203905020503003030030904081c40340030300511000008003500385d1369840ea114400d00e0703440c20000c12000010f10003030501e400e146596 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 588243246 1250 588241996 588242027
    0x301090b13020901060c05070e06060f12070f1b150902130e0111090d11151c142a040e090d0908010c14030a0e070305150f1003060c 58
    0xd4281c50700800d250140715824a0803072140f0020300021541c1440b400100000580c004003c100c018144544003003010070050510381d1080c000c000700c0d41c07460302c00030140006030403c0c50040241d0400000141540008401100402c0311074003855200740450310840c02d5191304242c40da800310441004100c05081110f40180d003001125012700c80c0c03500705601056200400400800081c8000d4110090383c0c0b00d2403c01c070342e000c9040ca000201107901d203015100d03240c200510104aa080c0091109102e4008150b502100110b00804a00e490601d01400031038188011450201c3c1c0340ca6803121112080304401c491001900880c94050342000c00200c07005806003020048007440c101c13000365526202d01c405079000035840c04001400310700500504403d80c400b5259030044801c00c0110240c1908020074100c041502c410041d507040d41c0602540f4050350240f000341040241050400e804031101612181000d060708003040741d140c40801d840310659a01c541c000c510349515000444844042c0710295 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 588244496 1250 588243246 588243263
    0x302090a05030d0203030901050c130513141018050705161e0b04021f05180a03020409140610081f0f0c050d0b04021204020f011b12110d0c11030109 65
    0x502a43e9000005148201d514200078032444c0d90f040f400000601400c0c00c104c04060520000740403500c0c06c084550407000100d80300182254134140b034000c28081c1540c41c28400000c116051111120802411072000d501d031106001074141410020282e100e8003800d0500c01403440800700400081d03854140003140d038030b0030464000b083e80c05d10320050b802c00e0f2000c078840d440d5188030200104860340b8498107001c081e240c50342030910b4418810381c05c0e040d1941c3d00e940100104c20100050b521841506822405040e015048505d81c1030081e15060004e000041c032000042070030088840000f80ca0b080c40c50349406070080c07078400ca2002c1000b1305868a13500c4040e40c1400203070442580e020000d4442214004005c1c0002e0741c1010620040b440303840d0482000410502c0003a000d82030001e009500d42d4010314104140d00c121050080e0703020382c502411504030402e4000b40409543c80b240d140004c00c031200c043d0000c074840b03c6014006000c0302d20005c1816001440810710f0340e070294007130400d00d40c000031034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 588245746 1250 588244496 588244513
    0x12040302031318060501020a020a05060d14010f080c0307080619110c1b01030612110303040e0c07020102150c16110d111002011503062703080a05071e0302090a0503 72
    0x500c85806039002d03031101307282100005482d84000f404014083e009480c0000d014201000d00c84180c0c0404075941d140d40d02d030680d81c0c030102070b1488103c0c003d10400d9070030b11541c3e04000030581410200c46000d4400d42c803540c0140490310000c104950441104002a1409240960172802402d40f00c0304004034040b020401d00001c1c5804510556514401e00d034494000703100900660841e0500d0203540702d603100140d200380c000798540b5121200e84078010110303400d290365000e503001c417110101c0c2c01c0045080045120411940c0401840c01c0300c4409401394640e80c94250340d00c664030300803603003000c800d908046400b6050000082783c8910846000e01121041006810031a4220100e20002801108000d41c0d4108103403040c85449440e41540321201e00315855516058085c1240645076010245903a003851080401c2d08075400d00180b19465181a91500509040803188014615420f111b0100100000c250414118882041d050b0500503101d1354440c012030242007803500600d41500c02c0292 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 588246996 1250 588245746 588245759
    0x31209010f050702010c090f0b0901080c070c060507060b1e04053303060f06011b0507090c030b0f0d110d06060e070201200708040603020d0f050f160212120403020313 73
    0x407046e20113800c0e03101c02c40070950f5032901c00b03115a140d2044c10f003021420f100340921580f00b0500c2a41010f00d02d06907a007032007a19100c0b10213405941e48108085140029504100151409107581d00e050172180401c0700c920f06003280d4072800d074000001c0c1c841c071b644070006101c0b003414000081ea5420000a2111020149aa0100c0f02c8056942035440f910038500010100c001603c0030314410324040e5156811450143c0700d4041407904c00c4800c4880b806070800c040340c0056140b040b0041e000d2140c1e00800d040f000e1105003e144031700500c44034000c8071105100d00200c0c144100510b441748068603178221551003030410b0400cc0c0312039007042d0605018102030280e115415082540300c00400c5520340c101d21034000480c000c074400c00100a200003020301c000c1040c0da009902420030700310140800302d100c0a05042840072100100c07090140c18015900384882c2140c2c075540b211603100c043c0014066004aa5117042160007000301544403042d54100007010180309000780ca01e440d60740d800440451340c81e0711 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 588248246 1250 588246996 588247001
    0x20c0a060605030f0105040507120201140a020120090102210715020903070f0312050304060b130903080601170a0213080a060603020319120e03010b13060515040305031209010f05070201 81
    0x20502d8030030701c282044052481c40c1031051900483d4400001c00440b4039018880c4552100b50701d0503418424074845c0d250920200034000c0410b8681540000340f15090b4420100e800c036213084001350486000d1003001405c0c0d80000d11900c8562041c5007144400301182a0842107124001d4020040341c200c641c0d80c0c0402003640c014015544044050300c043c1a2a2040c2c50140056440081e0031110202035155445004400440d00117005c2d950216000000741c0100f152030418480d103405484e030303405485091561124142da000340003440d05900c14810140d040c48d4610015001061442d03000034208600c503050300c501d800419080c03003551602c0d90242481e50017456607106c240d01074003400420302c5100101348125070b1440d03409006101c0c4089280421a100c4c465100c00980540d80e81c016618140c1e181d007881c84000b010300304046289070410060001e445643c0709400f80d0710710240814030010360044166070044494120030308096581144640c054943c000c100528240707031034240444d156064 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 588249496 1250 588248246 588248249
    0x6020d0c0203090a0e060315150d0503130e0105030703150219080406060506070b0432010608100207170a02010b19240504060e0f060406200309010c0204090303020c0a0606 75
    0x8995800003e0f03905d0700c580c0c02d65002220020303850b400101025403080030418590f40c0200311030360300300300c4100c008001c20f501c485415800c1e601c59001041d01000e440011000310b024182c9015012034551400003c03941c1c0718150301005002000d0100040306402040d419140715003a4110f04020040702140301401d0f0042c01e507002d40b403940c24200b005c580b1b802d14004440c106035000070300b480c5564590311102c81040200394000e02000c0d1110303440c040a20344100b030134482c203601c100019850b490f082d00c49140c0740c001c000c0385515500505c2000003042c1d100f007215406100428419039148103a5030124010240041d110303030711200e07141c02c10300040d0f6a1440300d41540c1701244a02c0e480d0903142e480303d407250200501440000c0007080140038243c440c2c00f854031ba85001501d4030210b0402c010005455410640114000031640d00c6d10b030005c030128940b203c1e04240e00002441c5042c148200003042d640441c08080d0080303450310316000c00c05210364102c810807010359094801c1c8207040e00c0c004014104d607 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 588250746 1250 588249496 588249499
    0xa0320120315210d031e06060815010908120a020715120513230a050a08130608131b08011415010302090f040c051210030c060816030906020d0c020309 66
    0x48185026015200f00c3c8024400f4074010007040002c000c0603040b800f4004400b0090491000c603501d0b4507800039940592000f0f40745c0d90300c4007130052821200f0000c00d004503684c3e20b41040003043d81041100e2001c03076001102016800d078156101642c1c6410f030320341107450340030002d030086000c41a02580d9100d90b070780c2100025210305000726218401d24050104602002511029043c00f0003111640e0541116499004030005d0302c2c14140c4584441d4145030f541c1c070040e02e4460000a40303100c40820944103501600c203d09004569007080d0399101500419140010884d540407201c205801c4507800c40e1100800301c010003805a5545d178140300300c12030320542780c0717120a000648080351158068000c2d152000400380811107040803000c10040502181c8a401050190400040307500842e419421841200d200405441c2d00b4a1440d001a665900b503100c0001c001160040c05020005a102c0381001020b51170082108103190600310004e124500d0381c0c2004600d004c044030752030341d000300c06896641d10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 588251996 1250 588250746 588250759
    0xa0e0907030210030c050a0c02040b06120f06030f1002071e12080603071404020906070b0c0a09080307020d0b04050705060a0e13152102030d030f0e0a0320120315 71
    0x80d68802d030140c03500c485c81500456421300120803401e01c100745003c0c55900007403002c0380800c103090120344194420180c40d0072142ca010308001c0004007841145070450010b4000f4900c821002c88820b443c1c068148180c1502034000440806000d1007411840f000300d9001d03d08142d1888902e8074003c041962a0343c140402c00c00e80c00900a403a0200b005da0450300d812882d0101c3c5031031001000000d501000050b60300084c1402008040f5940b80f40840c4130705000b00ea150381c0c90b10318403c041c2010909030b00c414800c0d401003007d0070050300c401ca0200c000780d0b0301c100740502948451a055040442c2ea170080c0350455004180d04261035401805000c518405032226110340c99001c0304402606d00d201c185003002d5008400030860000950440d094115840700c24a40c0410241e00080c113002c032021400c800240c85402d04180c16650303218010072050340000402440540d5503000c1d00c0c0360403c50322084004031105410705055028410241444c4074003000701c1d0340f441d14080d50310000064400c190b02414 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 588253246 1250 588251996 588252019
    0x506030a02071e020114070311120a110c010c02040506043b03030112030f050408070b040905010b03040209010905150d140c0303040b041e0504020307030f0b150d05060a0e09070302 79
    0x4400400ea5a00709806031b45042d64140700101900c0690b001c0e1800b01e04101c101262220209001d1082d441d10480c2c41166641d41c8100640c01001000716096000880c0c101c0401c120325a82c103e18141002d9a060b100801d40e641c840000400801007a161072841c8560095407511410181d8200d104281d500310b0006100200e0b08200d80d500d0009015118903006058041c0d030200c1c3c000c075224003c201003442d245140c1520f0b039800d40d06004a56002d0102c140000c1024000344165000d0180507001e000b1145042d450140c00080541c03c041c03217074074406603680e804110b503000103003a08114100d010f230400d000e01d6094580703600342d048507a00ca02514091800203e0251802008460071036000301422400e16040c481c000c43e40c0226041b2800c1c0000a04000140c0ba485030b0000e184940516100000c0201c0da140d005070035541c0186d4100d100b40c41d241b1250f4002d003c0729007920721408001d00c0005682c1d0320070010074900215034002c091072044000c00c1120f015000510340054900c292210744081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 588254496 1250 588253246 588253283
    0x32d0a060e090a02011403040c0b070c030c0605070305070311012004050f01110d08191415010509010c03030b0f03150117070e0f040609150e0111120c130506030a0207 73
    0x3c15040400900181034140840300c110181c0340510b81183c0521701041442e03668105406807a844108121010200030004000380a00072428100030301060504624000d21554010f1107882580b9000702485000c07907071511403034000d41c8507169640000440d980150080c1142503400e070464030170240318402403064544603512503000c0301d65000307403140140181113810303070309891051000b002c26499640b00b4180000f8402a8000d01c43c0701455181f0540160410107103904aa80060021505000f000c118a03074560346d0001310380c00880e400d40b40005a03007524500098400c403035040c3c03080c1e240c407a41c04c860081810300104541212091040e103183c009038401615200c043c58400c41c4d41c1085141d00082c03c1144e090015030b0300c103109020004000700640d880200c102407031421540c2d419650000031200d044244602c502e004a20268141440e00c01140f0b07201e0064002c01180d412603000c11064000f010002e03a00c406000d000302110f8807480c0002c4504001d421192041c2c601c1c41e075458001801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 588255746 1250 588254496 588254503
    0x126010b3c0a05071a07031407090b0a0504050a170706140d02030402030c0d031d0102030c1c021c03090215030f0604020c070f03080301150206010803032d0a060e09 72
    0x10030021562020302000c00c0071000c0c1468205124290a0010402c0b400c000039040c5507072844d1114113006859224200190010200c922104032803010014000500034229005075018044403c07600310669641d48120088611b400341d98440c54203c1c0e40300b000882d480090303003d18074502d1135800c222003815550320403c1fa80e64007034030030301281c3d80c0d010006191110762136001940d2160001c0d00703c84c089844003000c200c507210b8882e810f40c0042c414030400387e5900201c1c0b01074600300c0c0c024402142400b1950140c0f0b6101d2400c8010018403226040b0058103280c0280312003001c41c54080805102c01904200c0607010703108240003203200d07020000e442d604804a1505690046024462148440e510300c01808020b510000302010280321340100040d07489030102c9810050740c425001e10b5200c1d45825501c4401060301c0b10040d042d90040e000501040c5000001c0d80e5003c400306d0124600e40c1d04c082034103040403500013413810100c200d283c10021102c0454200d01d08032000c007220b2520f640e07110300744540c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 588256996 1250 588255746 588255817
    0x809121f2007080304061d010507022401090509150c0a031b020316021201020c07140a08060705091908061e060310090213050f040c0603060e060126010b 67
    0x44200305100e50b40c04203002402641e80103100d00740008001e8100105002ca6500c51000d00c001ca82d1aa001c2040056040c81102c03031800b4401c150054145a0f85c401d0703012030034140641c00340950b5880010340e80c00c504010340c800201041090641a085c408207110051b4003040f902001700c0e0802409200d032b0807038000c25410412240d80910b0030480461190340c80c2540b4020142d80c42030303003000c06000888080c0b0041142103010030050000318500390401070700340000b1030b0301d40c81104604810000c01c0400f1480c1940003c2600e04030307036034800407000200300035500d4052000105410301d0200e1000000103600e405205036088188402c8420480140380840841e0103075056040102c04104140440e00611211031000b40140c00c1c2d031740f50038402000c46008503450f050050902c01030006011000d0003407005006c03a0328052023240d0a2003541280d2400c054642410041e18034543e481e071040784c94402d03190100350520140c039565a210350704141c0d0444444d04607041e401380c440401d040a6102c0c400c1c17 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 588258246 1250 588256996 588257051
    0x2120a0512131e1b03050a0215070c0e0f180c0103180807030305011d060f0114070501110c070f0509010302060702031906060e070309030c0809121f 65
    0x600d03004035200300981c4264040c00309181c900c80003540000281c81200b180010020040d80b101008040e410410891002c0c5080810003880948003070000c10750108140740b945405441030448410f881600c50424866424045c03d484403401c808224120503201960142c44008070503902502e61545a0720820901503042681e503000d03012541c0d0075406608968507500001d011418546156107800c2601d40c0907141c00c030000780da41c90051050000c60040b2118051101400070503624000c3c01050040c02d881c00001d041c8001c42d460300c071044010f5400c42324404d50010080c0100921462a10742030740112003c0306440c01084030104d46c3d2001c0c0c42c4000116100200685080d905e540c00f8003d0b254442c4030142e802d03024800b1901d09059441080118842c8075481c0051558a0700c00340c540c4901028100100705803c01d01e03500046580316900c01c2210744c0041c1043e944004081c0010f0380700611a907545424040e500140ba20340170802c000103c0706003860400c1c40403040201004180000701d641e0070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 588259496 1250 588258246 588258257
    0x3140103110102070f09020a080903040803040306050a0207050f0a0b07020c0a1a2502010f080105180c040f060e180f04060915020c100e0106060c060203040c030807030503010602120a 80
    0x400104600e11100001441c06005450f0b59035100c2c0c041510f002c05580128031000c0e00010701d5a64168010f0540b43d102001d40095414203081410301342d2284210720010b040551200c022402401280d811110b519500c202101c903003c008955440c0c44050446055501500032400105110300100702045002070090030100000c1c284009001d40d095407085166103804284050040c3c1074002030385114614004103c180c00000c28800100f14050b00301000d010031104000410030b41d244d81018210740750b840301c40382503580c0c1e44810b06000d030f0040c1d038400981040c000e000091060703040030a0200c1d0340c02c00e17142c3c218601100203401d0481d031400e03603081c04800a010005000704455920a000540c03282c258489585092a000c00907a04101004a41c680050b021a6183d154510951019006281c0240650703883c200000e032056005007070103021280c00200140c1080840368248000c0d507445151180c49100b0303814014500e070002d0040001510070300c56201d0030300f4000c100b92401440c05035200d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 588260746 1250 588259496 588259499
    0xb070306092c0a02100c1106130b090f03010f060306060807060e100302040504140105102102220e10363909030c050d0804090905010504020f01031401 66
    0x980b001d800c0001c5281032140203402043c0c00503039031a2090001c51a8544e51a03103d119075040c8510b440381a81302461103043c0400018240c10100304d0f4940490314001d45160b114050540425180c000031500303ea0301d540381610070282003004d60b01c901e003903c0c0038000410415071524805903480060303000d6040428241010320040740b50066030b8540114081ca070150070035a407040818103032090003140c0c4614000003070040c840390510301d540d454071020301e00d000d03091581d401e0700c2007600c1d88503000e10909a680016029031600e038480d50b410b800200304002c0405c415039440305001d00090556010440040d00302000074850340c0c1140045982942051006076120480d012203041c402c00400c078a100c545030b0005400002903806011040801c110181d420a00c091025000c46a07103d01e0400a0207445076081c8045102c014180c805e41c0d134103036100660201d2500f402991405258030000b8001c1c1040100010004103400890155100b914000410080d0070b00550580b118140c01c22402c0755603900 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 588261996 1250 588260746 588260801
    0x9060203090115030804150c0c090605091303080414031201080105070e0607030801090f060509090d180b19021906090b0a06030b04170c0f0c0315010602250f030b07030609 75
    0xc241c0c07240e1a142400c0800c6031240c1e0341d10034070b05030a40c001405a562f8200c204000d0502200c110b41c01402880340244920040d903001d841704001400141038076410710036409a6520400807141d49403100241b1603400e40e942c0245901801040344d01d0400121925121889418000162010345038141c881e05a541c6c2010038540c018010901c11044141d20f5101c00111034954132001d41c00b070b0a14801a00d0804036103a0058500203401404000207041c2c198200203404040c815a04140c0c158a011010074000707001c01c92500c03000742c4460a000c00d454880c071081005070351083c024603105501c8941940c0c5c07036101240403030b51203200280072079101d400050009078817040c0007020381c0310080c41e5504250001c1c6666140c0030700180101c80317581c421910b241c1c0c40c1c50200120710210700c0c06001500d156040581c005d4070762141c8000003145280c0f1315030101d540020241d811000c0c1c01200300c49401c4e250341f4140303408038040c00e840c140d002c0b074030f0410003103800e140c1c0c0d028401a81c46a110300d201100350651 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 588263246 1250 588261996 588262019
    0x2521020304062a06020d060803030603070e090102070c0f0e0705030f0103080703020f03030a090203010e0109080723120d0c02060123030705090a0603171306110309030109060203090115030804 84
    0x411410100c1020040f60b240802d100c0054108103015990050705c0d4016002039501b1158a80c02000c01070740140b0030030100e9900003d090b001e40d00c84003100815502d403c00c442c2c1c06401500002800320207420340209100e10314800600c11200c00d00300c002240d0301c4041701624248016540c001d00140c03501c00510204050780020118903101e881111070603202b49000301d045420a9400780c90f4182c41b48030044c150f240034007031590302c5c0050400130003030001d4990b00e5080f2449481c50081448440422480d003090f01c440007112071700c0440c0140c44145107400e401c04015800004c0b1040c415150070090743d8030501c0000d07843d06071420040c039040720b40c048072100700381204640080743d81032040800101c3d041d1922a169130188a0400c0d01203403481c01c0d850103202030701501240f040c02c0f450a0007980c0e4401ca2942c00d40040b90b803a410801200841008081e00f140b04001000c1d401d58200b0350300c8410084940d00a52282410900030005035843d51f6016646440074400500302003028801440a8030b034a4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 588264496 1250 588263246 588263267
    0x90a02030105011d06070b180f0c0a050d150501031101090e090a150b1c03020d05130b0d0b090906011406040317030604020403050a05030706060b0702060a0f0302252102030406 77
    0x1745150f0601d81599144400c041c0102d80d483e40b841200b40714000d5001003000302150400c42c0f030002d4594074002e0404100d034849144150380c0700d541d030001d02409009607140c400480c40c401f0030041c0090740e1281081c881c0089403062150004031034000000300720301044071450007032000c43d0140030040c0740b58036003680940b13008140550080d03807492009050b50b00d29503c8a0680d02290f0f82c01140300242c1006410301c0c0282840c01c061240c100000813040d2000c0701d41314141c0b1103540749281c40340c4001d405c5200038103001c03030f0180d0400e2141040c030100150008040e0304031080019030400d030301e420405010302c40c003d610008160210155802c4013203000c12000d19404400500b005042958030b8031218a403080340101500c0a420009090040c0405400b4080180070034440c420300e0b0840c0ca50204009200c1e140b9039208004c858414115494800d070110b07070715502c00340d5031003884150000500d1a010000700084946845040d601107040e460000c1c080114011500914100b03850b00000313840c0420700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 588265746 1250 588264496 588264499
    0x60d060e0c0414041a07091809080f030a06050a140103020702030a0b0705190806010f0809010f05010b270d1b03050307060204080c04200904020705011a090a02030105011d 75
    0x4001e50711005032610302c2648100243d1680d40782260504d800c00108090402c0450446114058100b1061940001c113075001c640813010040b1800d0780d0b03140b1807001403442c40c4004020100010341c42c000d042050b4099070044020043c2040219610400c00c0580340403441601c0d40115103131154011580a40d02500c00c850001c0c00b5212001115a210040c2c1c00c4101d5404d000f182020440d815840f602003045190b1707003043c0c10300c013025003405000030301000c405001520402503020700140500c51300303402615007226500da0a1081c4d58407818000925001540c0f80c01c40318814050345410f40e0b00702032440341300c081c004d0103200070305d6100e17128402103684e890310500314000091400400500104010310a0a015031401a1038604020b030f140e0410800550740c600c03444c2002060301d1250282500406040175041c0095030700c0b0741010109019002d9060090b00c107518000c400b03400213a6880603104100c900b00c80c100b0f074030b5441000300c00403070201380a641d00166070041d80d040100e469602c40c02040d00b0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 588266996 1250 588265746 588265753
    0x10120e010b06040b1c09031e030e0604060b010e01020309300609100c02150a0b0a0b13030b070503090d050306011116082a09070315060f17060d060e 65
    0x1d0241c08109a503003d94003244903a100042c18502a0b50454985114442d448900780444001078030024803105228400156090400c440008118041e900070300002040e54142da045141c242010f0b40107004c0174510b2404541d0f0052041525880031040b1024000028910000c8006124801c00c020340f0744c080d0506c0f40c04101c0380b5805244410001e2a1144500c1c0000f41904401c0145100030740380521500c406561005034040744149410690952100b020803000404404010000d80b041c04660f0010171180b00c0003c1942c0c0c4c5118411702502a00c0c02660050055107480304100c0302448111601039072038001448402455206000441d0032610504d8618000e0016010080c10164201008400780c1c907544800c200e040c00501c541e03002c0c02c0d071082c040b0504020102c02580303021001500c03644107a0580c1c000543c4180264031505c00e02048100d41059642c5668028104030604000703000824000040c0e80a52030300700403490310980003d00448a0803901d40d4a03080030f810940d980707140602 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 588268246 1250 588266996 588267011
    0x1090f06050316140409031707180306050f13050703030c0201140d05070806010e0f041104030506040305180406050a18061e18020a0807270b07030e10120e01 69
    0x381c0420641d8403182c04665128846444c0165414a044108240c24015070030451800003294110384440303565a950072a2001c540d91b61013003240d0b403003a01c4030102800e01c5d04a80120901c01c0c540c0c0000c2c400c41c42059017440a44810200103808011b1650044c12548240418000139100d254240813851060400c50102549070115a509410007600301e0f8026035103008100050b5030003440d040d00309400b800c11101115a40000c200f220481100c4107006a40301c4940c405550b410b40e084400440c6c100702034401608143c6030041c403d61003001c41d8060346040030b1f1601040e00d0680324200803580010316400b0314a203002002d04d015a1183d4007000d070543d4a403000a185074040d9044100e003280b032003c21ba903450401e40b800b104c803254518520b80d03062040c0501c4044942109005801c102d403030410301084188074000c400b40240340c1074258841418400006401034100b0050b0001c02d11035114101e4090442040c44a40f00c02020754000213030b004006140b601d50307258003011003000442c00200701032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 588269496 1250 588268246 588268249
    0xc030c010603080903240a02091302030a020702092805131704090f0608100504021908070e0a1b050d020f03130c1212030b010c12080601111501090f0605 67
    0x100e180360b1094405901c00149050280303801e101e540e200300701d030400e49880c8130038181d043c56041000402c06200e4030781c00038914400360388501c0c0c20048543c0f41c100030755a030300d4034645881c042d401c1890100d019000c503c000c01c0483d0080301500d80e941c608904040541408120070340c000c0c10010308801d03501011030400c80d02044109884d842141e40c01038642e50740741e00e4803214034211841c80d00d8003c2d41c545019002e012600300403c0410005105d404007140c241caa5000003100145040d1a07110303c9002c0803030000700160301040e40d404861803074204880301d940d2001c8210a03207141c440b006d504401141702c0350b40064052005424450304800c0c0050826004101e00c114513401a2a0300c11001c980f403905004110440d040b4501074001c03402d0108032801960340304580e0805a00c0c2c40d0b420300d40c403001c030941241d202d0400f08419a40080b01800b5400020030050180002614610b00146085d0004c0c41c03481000210803581c4d501920562100d0381c070b88035944c002096000480d510383c0340c83d908001041e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 588270746 1250 588269496 588269501
    0x40602071a0f1006020f0a020409020a05120d0e040902090424152c0705090f040203070e03010b0609240c0f06160201140c160c06050703031d0706050c030c01 69
    0x40818104400983c1070008041c06100340702e5000100310b500c07468071038031050300204111072840e90540f4040341a1449200040701c60045412840e00401030110555002800182049051510fa22000d050105400c00d02050307e5170400d0180d00a130450000c180094002030200a440801c7c10311209200b00c0d42011800707880d899081c5000c20f42c1801401c0c00300030009003c1c0f810351b0344039a400c40200300540c681080112002860b41d018450f020400c45259242c60001400124000340215130ba460590005450300e4880003032603019619180b1554071310304004085410340b640040810901007078552030310303511421100c80c03907444003001d00200e6201c49040013424820010340002d0143c2c0c0c80e0101101c5a1146048140740840e8180514100c8065243d002c0355080000d41c0002a950f038403821082c1c0c01035031b81d09801041d1040701e81d40050081e6004001c0d00b00c0300d11a550030301c802d099486428030410450090400150803e0400b04440340c02000100713005800402500d04051020101d5403c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 588271996 1250 588270746 588270751
    0x40e19021603170708010303050a05090409060e10060b0906090105090a080f16063608030901120203150f0d050f0a0614090c1e090c130509040506040602071a 69
    0x1074403029010000300305a04005003400c5a074041c0c4854040d482e104000401100062001405016001841010041c8a41c0c100c1e1702000c00680140101030701450a50002d0501d0000810303a0700070300c1c0343e0030400003003801401e00f25041201d0682c00c040c0740d9401c124890307108042407030602800700424007458030740c80304e0350009280000c040e2804c02c4045100604280c02c455417001800443c203011321106800540345480051075074403030f503007102c46819907042c1031556806101410b4040701000444040000c010706000000f03a90301400c8030400c0d40c40c43d040c0c0c001500d034810003682d11003203d452428804400480300400800d8a040d4003040d4940034103011600043c10059004000500d080c040180604076101060030040c00303040c07420382101da031916942c03a2150300c10b0100c80000035411509030801c20411000074603201e01030501c0d02210b00281e00800010f00906800c20b0000f8040c50004411845550488041e02c0750750f6403590344000070340c04000d04448000110200400164a20300821f1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 588273246 1250 588271996 588272017
    0x10201060315050601020105010e0702030a03090c0e1816030b1522020a02120306010f0f02030409060f090f0c020304030b040c09060308070204050603120d1a120a0b01060c08040e1902 80
    0xc3c060804200090075030714142c10081850314203c091100143e4008100d0f034400e41e60303180002385052103250040700c0355240d82c0810003038003807c0248102e54810388110300000700140111035200220101c181041d00381444064400c0c1520300001d0307c003418801100c1c00c0c8000c020b010310030008542e480500c4c64ae0403051141083e40c1d01092a070f92958041080302d40c0c990712410f045007145030400c0002c1130707401c00d4003d0a04024a0044030404035008000fa03901400d03602e10700b40030705a01c541180c00000c145105030421581084e2490341c0850a0344036038400800140c0c069031805e419901c40000140000e0300440f4601e0708a00c000888030f40358840d0740301a503c11000700c1d075191140c0c010402542da008d041144a0f1b0012154003130500c009a0031030b008030701c00400203e9052580020254241c0708a89800d4008202074808030880002144102c01c41c3e1050708d00d1b42e041d9803203403070440c1d4060346424010140b00c2c0402091002c80c20014203264000e00e00440240084107856480050360440c1e288007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 588274496 1250 588273246 588273251
    0xa090503220509060d0303021e1611040e0d050a020705060d021804052703090d11010f020105011202060903010e1f1a0d0b040525241409010201060315 66
    0x1070108240050118002c0904440c031035039900b81000000e0490650030030050515600160f0108210726200484113040d01038064161900c041c16104400080c5980c0d08481400d6104036600341c80c98a445054039942c000001030030b100d8000203007551254020722804007940b080075030004455440c030307000701038244000002507202c0c1402c3c001022903e0450503540d200e03e00701010032101260f04109060010040d50344000040181c400c42c2d401e52081a001c6a04010450162001d110808007007000000d02aa2100c0d600214507108a00300d503401c1c05219080c02100c2c40e400e0151070300c2d401800344200010000603040712000d401d6484d103d0041c0c010300e0255003058074440141c04138803516224119681c0c0d404900c070000e40024404642d4100000c2000304c11901042c2401010003a44164600640308480411200b00c54054894242e00c101244446400c0c22550010403140c920031500d00b89032503030145142050280902904101324190466507141130000104002200c04c0b40c8912a11100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 588275746 1250 588274496 588274537
    0x305190204180e1b01030b1207080f15040c0509190f0e0706030204080c04020c0109150b0306180309330d05100f030b04080f0d02090a0f1a030a090503 66
    0x200741c1070781c2c56440d0806044e0890050189169030fa1000300c03016031800d20b0009526088a000142c9111007141c001040344103c4001186403880064102240d0780c050048903180c15500e4000700310703550201d0b0002c0c145200c8641c2005a814050a41034000308680280900d41d00c03a440c0d414120b1b1020740202c03e05580f1001c0407080e05c8801d00909015002c03070300d400d601d00760070f1001c060750342c0048a00d0140120740c00159594658801c1d4403c00301c0701d5210b1030310791041c01d0b5062038801503d140543c0074400e0003070102003000c4481001c0842090b00302000a9400d01840004115100108800b42c00841514011414895032041692100c5031080036140e034580c0c854480c6070085070b000900d80345d02d400911105120096440380c1420489030b000703040c00302690b10340c0ba0501240c000c840d00903004c1140807411101040041d00070740061101506e10404071036a48800c800144403902c00c11410105406041400e164100c0c015540a078600c00d001c0740c441c900ea034649145074000066101d40521400c1c2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 588276996 1250 588275746 588275789
    0x50d1b08040c15170615070c17010606090501050c07240212040503061305031903051503120f09240403030f0c0c09180209010305010606020d0305040f030305190204 72
    0x814043c000c01845a009441080d202402c940345000c0c008410060080000d00340381d440502e0714402d0300c1c500203000d0311588145485405034045000701d24410080004100542c541481030a046409542e944051076107801c0040d1403030790110040a2030b078017a000020400c002d180c07800014405c0403101c58071000811840003400d24414282c00d1500c59020081040301e60b23000916140c000104a02010724080076140041c07a5104441403175411580070364082400c190554083c030722481201c9039829020401c1d20805407603000240703150080800501c481550b40f0480d1018010000d80500b00c104403003250000e5404020103411008116000080c0510801d68403404c070014600301c1d810019501c000c541d8070599681641c1c000c900581d581e43e102d68201454140710b0400c07842d0080c0c281c030071558680c10024080c042c1401014050300c609582240000c0c402d22400d441203801c0340115406040139503044010f004045c00100c26159590b600e400802d10342d10042000708035160703d01814201500 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 588278246 1250 588276996 588277013
    0x2061e0a020f1c0f02240412050a020a11030307021c122a060f05070207030c0506090603010e0606190903110913141009030203070605060a0b040303050d1b0804 70
    0x3039907241c02c070410807070407044042060401c0c44000d0130b2540780040076007822803901b800340c0a948109a80f40346041c0d44054110742141c012030064a8480598061700c00c01d03199442081648001a8444040440403031035800b4001540c490003000d803071600d40113400245c0d05203c00d140350680c101d180c42100d0304021859104108095041c00d1040143c064101d4004541d4000040b8985840d0701c4401d60b02000b205912907081d0175220b000c00c03c8982002c44009558014a000444814042d020081424030380307002135500242000384606d14623800d1105078000070f0000303030000d40c20030300a004552403003c9480720b03904503040710341c0d60000951941c102420034030b00000c0f4880c0181500d20603c1021344041054074031090700000da40308150801d4020340c2c070304100508140e008501d410741000c201a40070004011150081c103050006458060400420140714030039611450030030041000040d008402810101000c80c40000d644000341e25022441c00120020200240e0f07150200800c01170103c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 588279496 1250 588278246 588278263
    0xc08040f27050c030711030409050c03060907020708340303110d030b010c02040b01020a05070902070c050618150f040b09041d061512030a0302090a060212090d02061e0a02 75
    0x10010700043c10600a03600f018800034009508000c040e5802d0018150208200d800501c0c202d90708000314a40310141c101a60002c0d00c415115042d00c0d404140203a1001403420b00303880006000e09001c0044000a0311103000001c00805101c0c41034851001c981120050701008600070b132684407120886011032030807c00c4859080051514028500c3d0b00344c4d03440070031940c00b16419540000c08082120060b071608102c113000402d07034412400c01251010b82c9070050701c05c2c14071890700201c0c0d04d51030342c04200f40c2d4041c080c281c0b0021646a5110851450112139042c0824520b002c05850141081002c8001d5446034001c072462502c0001c00040d1400c0034810144884082641c5090040e11041e10701e17140c80000d0071840002001c0e05601500f40d0750701200b02070044400003201d0740c80102c0c0d14050060b400c1544003a10425042070000340c0340340007080344c000e2080d1310b0340500c0ca013a03003440412004500e1454180c0e000f92041c008a0403440c1050710007140c1c13440c54171082e61144c80c07107100240f901804 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 588280746 1250 588279496 588279569
    0xc150e0111150c0c0307020904030e010306060e06070303051f1d0105041e020c0f0a0b0103060e0303040f030f0e03160513021305040b0303090303040f081c050a0c08040f 74
    0x200e280806140d00e40700d410b6810808050410341d8489000d12028a14011007102941c402103600500c010150040405245640c0c02e0720288041a503682c03003a602003060402268110908004400000c0e00c01c3c1d11040c0c1c86054214007030034400700700003c86190703040d54106044c0708d5081882c40440c00c059030b40390307401003500f280c1c01e00490907828208000c0198500320744003402d8000c203600004030800c0c8050040880c4c2c0008540201410341090300e0000d0081c0f01c240c40c481c0c81c25080e00716a00002c070440e031080c1d400100360782c0c080400d41d808031240340030030751040100510804003982580e000e0081c014400c0350001551000d41c10a02040104482200040e940510400c0003100c0d100c012440346040780e20450740010180306504c0442c4c118070801c4059585400001408198998040c4c0d0240a80c2e2440e070841c0c01140003244240c1c0c0c2610030a8283d00410f0040c400755010900c10502044440d216000080c10681c2d100442e03a040030b4180c12040c4074908802041500400000302c4044150700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 588281996 1250 588280746 588280753
    0x18060408071b050d02040b1201020a08041203090210080703090f0f03111b06030c0d050c0d0c0f0507020f0a0803031e0a06050901051c120c110415050d0c150e0111 71
    0x3a0200051a136000944024016502ca00c0342c20420340d51242e0706004a8881002950396030f903220801024400101c2d0112501c210980b0800d00340380c071a11450b4800d03030f405000440d030450101d000356148000100b405007055110b812800000c2e601183c0c40d414036101e681c22111900b40d920f0003030200e92102e6480e520503402940d030903410006803408148800410380d0203661300c0c0c0703940103034000502c83c03242003080403070a24060080002805009060340c1c035100c40704100303180003c40d0032501a030030707011080c00054061043c2c4001d4a4000102d14192000500c004070207591000031505640040720310a8a14909400011409031003280b1203500c000010001c200300d80c20800041c141d203106010700c5e030141100b034840711942c036006217000b0015500b085143c00b07038907a6080014401520481c003281c60665040c11400d443c1040c0c02810081c0d804408115500c034103010038002c401607501c0095481d0360048000140c0c10300316440760121000c030b55861030b40c02c0707508000150100c145d0300312002c40d40d071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 588283246 1250 588281996 588281999
    0x10e030109050304300804061202040609030b0604090204050c0a0f020a0206070b07050c030c0d0e09040c0501030c02120c010e0705090108030a05130308032703041d18060408071b 78
    0x2c00200443d42a41d500c062007506000005480154070040b00148807160080c1c400044140403c14000c0c1c02103502c80c0c0c0e42c1140c0c2a4206c2c00c20710a80c0501d118942c0070030141842032001035986070109a00c090003600024901c0c0f03e176000681138540c1524180000c21001801c08a035a602810000396060603000420900e400365002c40c046120703040000d00ba070800000071800e998890011501d001840034202e07520b540f900f407220340d00c4c0d0070008d0680e03010941c00c05145a09081c2065050721854100f40f2505c0301510344001980506082e44c201d004600882204024049100001c4c080c00d500b0480006a030754030750107855207024030a400c00d51041d00d01000402402c0c1000080318408641858219207640043c0f40c8a41d9400d06604000d00c55880801082904001003050444240d0801c4030414080c485044003603ea01c25030143e0105100e41142c0744010010340b264843c6c01c00c0780d41c401c44980c010080b1820341800790545044602000c000b07511400d00030010445080e030740360b40000400b1035 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 588284496 1250 588283246 588283253
    0x10c03060518102601051503030711150c07050901050d02060403030c080f033402122d030a0e0309010f110a0b070c060f050126010f0c030b010e030109 66
    0x10070781100340c1e00380c00c80c0c2000111a40e25684550004081c0c640b000070a490740a4030011040741c103400441490b40ca0500016240d83c206603921f0101c00c2c0141c0a14502806900c031449202004920903400884502d0f4111810440070010000666514060300340541405d04206050384103034401c5100d00c1101c110140075075102000c0701c08880d450b061940d0700b0405480c1005950046117988080d001c8040208100c1c0480034000a910349400000f00b580298011032601403100300e44e0804005911040601650b0a030440003852908102144c04114a03c801ca44440c00108400105901180807092105410450142078444075500010b142020704120000380001c036400c840c0c01c100f000f40f2003115551841400f0b507012a03a0003150210303251034116005024541802001c880240c500708444071001004e20602d4141c90a045d056100a00707180b54488108041e82805000c070b540c1d640d4191264501c0344940c040e051030070344000c50100f601000140900420744040e50103039040c4102403001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 588285746 1250 588284496 588284509
    0xa2903100b030403020109050a0b0f10030302030d0c0903080409091203020f030f13052a010809030d090c0f0f050909150c16020301060e09060907060915050c060f0603010c030605 78
    0x169410700440742d403669510b042c101d026088100d400f4005000701007941041c0b0181c403488a225512003c107821058651002c44000a4150311010b801a0020301403140c202805400002028032103140940c9031503160b032200c6005038441d50140008903a101d001108010b02809002040b60f4203080450400c0707009a07811407103100081601920310050030004030414002e0000c0c01080707400c00b08694a40210480000c01c10810000c0c4e101d0f401000068100c0743c2d84240324461043c100c54000e1410922140030100160140340411541c0c00c48000c40401c05640d00300401c002080020001c512051400d0213100c891a40501820b501e5041822280e10090000540035000591006210b5940221040c458600907030f090000394035509001000407807140c22407406000d03407124400d0310025214201c5d01541c0700594403804c2c000c50700c031290400c01042c454064442c22011030800f0761810500c032052074280041100e0100c0510440001e02155040074403c105000b41c0c80d0408001e61410f09001854 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 588286996 1250 588285746 588285749
    0xc21040f03030906020d0e06010306061205070e040309120b0f070504080c01080c0d02040b03011401020a021f090b030109020304030f020607020309060912010914010c0309020f0402180a290310 84
    0x5141e01c55001d10100046175045400380b0f92003002c100000303607192500d030380c544400b84800c2c0c1d0305605151021420340c3d86188075500c9542c1c080001c2902a24041070b5040d5014010000d0703041c03000395031001501d082c000b0031103c8002d10420042c6010702e401c030310741100b2a5000c2d08000c04c0103c1803101f8041c6100001d8204003030442400c200034103940e9968454000d20404242c0c13901507002050001c1e000c0007402c0554180c540f2842e00d15940040031004a030b4078211201c01952204070005c001c81d4a0400910980d50b0308014580714030070f070b0745800c0360030000d07482a4810074072503600000700f00905078404058070300d0002034030107040c1505003010005d60700c1c0104154030b48500710001300310034169201113040700405910b20003440140040d04008070001110507004c40e0039421300300140f242520a20503820805d600900b49224640328bc801d1000075008403582c1183c8410083e45c90140e6905c00700b01c40010000414400600403518440030b85480f02d81da80d46072a03078010300a20826400b840c52590 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 588288246 1250 588286996 588287003
    0x2070b0304151d0319080a0203060a031707080304210f23090a0f0f0801020c0d030e0a05060103150e0601180c090902181e010c0b15090c21040f 63
    0x8041c62080030040308602c0070000c003450f40c400000c0c00c030700f150743c41150b821014800b500c903403981d0391b218170106080e84000c42e00190b000302d0081c824030000b107036255078410301440c820000741447d5041d624400c4036801070b1815a09012000c0c8890a900e00400002c01079040b10301d07041a180482201c05041011004401003024000d00b0304070482c191f2401c1955001400204003480300303680c82c42c1d40c1180c1d072214044e08030441800700010500c44414000c90f400022154010450071910030300841c001c2006442e083d116001c1c07011540007150042107a0341c00380d800f90201c28407610120307814030200d41c02c080711505250807070001044600070568614000640c075200102da0324400c030f102142c0192181e0060340610344041542c03400f240c4c10307a400c64119442a01c80028250f144000c1c0b0f1100b10000c0a942c0c0043e0701c881000c40041d40d41901190003940802441d400d203556000054801401140d01c03200000000c6910035010031104001c08081064a85100300c600341601c0b0b03500d00d44580440039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 588289496 1250 588288246 588288251
    0x31e040905010b0c0a14160e01090c09060504031e050307030201140a091a0703091403031006110618011d0c0f040519020f0405040911040c1b2006030c0a02070b030415 73
    0x119007180b002c0c0030070040000c0c00c241800041d40c6441316480720302d10a010b2440c84a19003cbc0d0b8610143c0140d04a40a035400e9458850a0518594500410910906440341903400801c1c542000507000c20140007040d2180d000030030800f00703241d0441d0f0200307001070103082c403141030800c030780301040201030041080d901b0304654101c10740d0b030520158046c101d10310b4014042c0c030040000d0910787d034010014500801c1055441e90402d03a480b4000c840708801c2d02d192540c83d81001c80441c0c95020a140f003088501649400411158501e09400b4010140181d02c82c545802010040c0814a413844409600c41411101040b05045c40c481008400d0300c00b40c0d0502102d0ba0001b280380d907403214034090798020b00d402002444584228540100d888030504030042c0600e042c80304002190b401a42002078180e00c6030304444010710903882e9000802c4251400208400c4190351440840c1c40c1e110040d4825000d01605668421190134000c0c5003400582c4083c84c01001481030000040010103480145607014401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 588290746 1250 588289496 588289523
    0x140f1611030906070b0103030e04061413060b040f05010806041a0603041e14010c083705070305040210050a020a0206030603011407020601080c03070b040504020705031e040905010b0c0a 81
    0xa007840c61181018481d40400003069200411896040340f074103036031103503441301d4000c01641305120540c0e446004503010313400b00301d40901c0c1c50b0600071540c10912160f25004640699114424111746e40710390072070303600c006100c0010310455030440c0c0300765000700040d2800c03c480c103841c8030b204181045d60300d8814400c043c00000f180078031100c41034858202d1010301c440c0c811700c110b0b40360140000d0a14040002c465081031642c680d0603010b1403000d440b6165081103046041c144203002220094140c0c41580d8800c0c007110904002c00352031140e10320680c61500c001860f803d1a00410844915480368801041420820482da540d0701003500081d903581039503015102e4a40b440040d015100e01d44441448aa80c1410000110750015402d4101e030b100d1006d84500803a10420b0580f00e954a005e44aa0140300f00010440b50a15500521015000740140ca0400d10701032018031404407c60560000040086400c1c05000308904c0341e140100031881410303207094000540d10391a614200d90262424064862 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 588291996 1250 588290746 588290777
    0x1080c04061d3402060a110c0c0111010608060c030406060f0b0414060d0905010f061406120702070506030a09050607030c0e09150301090305130515070b070e0402040306140f16 77
    0x4144264500041011041c5030f0300358009503501011103c0c4003405003800007403940d80c59101c00711904511484054991988008010741700e403841c000c4c00c0856903580c1e00c00020b03440410700c400382c043e03100341440c035507a41402c1c24010305599440d0444c03098501c1c2e03207804018403647c40e0304607400c80f07850301d040c0528044010009900c40c0104143e00e040389080c562032104020040d4003003213a411164101f00701598031028a200c3d422528411190890010021340000e1000c401031540e0046031481114009500c80c004201c0b0754006031983e81d6182c1d29041c4000c00c1110911450303a20040c10301e800c010003440e66000811030f88001d544540240c4259001c074004292039400100d41110240c02400462698900140540d1188610806002200710041890710345241e44e42464605c19100c141030040311784408507192000350110003404000140c0400c2c586850000c1c00007140541030008401611400940b009100100b4821104880c0000c010740c1c00b140903113421540d24a072501c2c1c08100317407a02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 588293246 1250 588291996 588292051
    0x312100506030406020717040501020a030c15061707090c0804020d02150406121a031218030a0602070302010e06100909030e06160507080d0e01030b010e0901080c04061d 74
    0x1044641c00a20000401042c40542d030000d05610f0b100b110001001032070050250414002c600846006070400798044000c02d101701542004030307000360a648102119040c42c101203804942c010003580f0100d0352580c4c48041c0c00e0220354002d01000c4c0b402d104132018240f0040400c0c80040000340b00e00a030396254010745d190a031103220403100009802d0340d02d03038580c8c1c3c024050603e102d000c01506404c00c413001c0000d6200900b8828928009001080d41e2420700f03001c5207103504101004003034540e94060500340380e07504200301403d560145a0050303980407507044c000d0940d40503207980c40c0e090380454240110102c8010000b400c40b0030b8440c000608550300d02e000c5a01c51140c540250780001c011688100c0e00b00368414100d10644600b04403040c846d9155001340d280c8084888220100f0905d0502c00d955500980152182d540c0501d442c02006030410300103000c02d41c003a00304001070b501c200d800c129242850301c04c50700501044040708410400c140c4c440704455030020003c91407a915861101481c80030032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 588294496 1250 588293246 588293249
    0x6060d02120115090501080f0a020f060c1501060807110615090709090204140a060c1a180d020a02010f09081e03160305120c090303030f0c25020a06030509031210 71
    0x31950f0400190740c0d408040041c18080c0130700d001d64021040280920340e80008ca200c0300c030b54058401080843d09404209080d04998040704080c01041a06c1c8201801022101c3c041c1c5200e403203411541c00c00e940c2c0142101d28110307845015274017140c103101803400404403000204004a500481c3c0f1741e941131044402c00d155900101c8017a001080c00704000d03d025030b007680041000d4501c4141c5030b54440c0c1c1100d511040d0080904035800550720b0141e201e0507440030503848400d000700c1e444450b080041c1d240c0380101c26080341005802110b000011580c1c07041000020603500e107842e0300c42504250b5020384881403595400e035807501640c020001c6103414000e0794001811203590200c00c00c00d60402508a500a007610700034911392400040c100680c14081c5c83d064172003d002181181c2d601803001c4100100074202080c0c58100b8000900180e22020709800c0010002400703604882c4c492041c0405040c86821843c20f0504001c1040700b45080042641d242c003402428003036a503202c0e500b1066041255 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 588295746 1250 588294496 588294521
    0x30c12190e070320011d03010207121e02030f160f290105040603080a030b04110328180b070c05060f011502010e1f1803110f06060d021201 61
    0x10100920141d45000c0b44107812a802110791a60b1440070542c1c100003c1c4141c0b0415001c02c2010410351080003503100f01c2d8102010103000180303844116100d525907018100801e0700021441103020983d0682103a0030180404940000d5085c2110512007088500581100100b8030300040820800d01807050010100c1e990800e064041030f400035030040344030300c3d20405043c180010b46000024103003014414401125000444642031607101e5604901800310303940030f90f6010307485040c010a8904400010340c041c000b00c0000f8440c80325005101c88440e50803809034801c15203442d1010a01a03040d82802800720740c850b00c9444103685031031050b00d8005002c140604030707116400c00c01c220361180c85803060586e80840301514105c1800c2008900341c400e00300b4200d090382c04c4a10786158403034101d00b003010007014148021a0501c025290500c802401c00ba06800084000602110101007809154148010540509140c1c0307004004104800c0c030180000303000c0c000c16984681400001c1d48641500e061 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 588296996 1250 588295746 588295751
    0xf02040b030f0f01060207030201050306040504031e0201230609151c11011d0102151018020a0e18042010020c0a05040c02150a020f0a050703090b030c1219 68
    0x1880a0451100901243c100020f000f0b00000403e96900010301c00d0101d030790582d24180381d540d5034801d00003e0607002c4e00071003d0240041c0da42d118400148500e10808801e9400018500d083c80710200601c4148210a942d01c2090300501c8041e865015400764070841d428105400d101c0c651000c11401d0700003c0e40c20000e44a4074044d0400c00c034102496564040c0300340da60105130400041d10b1000034000a40321405a44102d5142c0c0131030380b61b821150b501030204986400000e6030340f12004214a40c0d541000001c0da400545494a203420010090418006403090045052082c14800c0041805400a8440d00600f8500600c250103080340039200304000d480200c03016501d02000c0c0d0390b80309003804248181190040840d990802c0d1060124000c0c1c41d034010002d1014041c459000a2005000d0202e260b03000c1014010718410745004041e0300420b030b660103071307a441030307007802011000c1540105000ba42c00704180071345821014250f5004440e10014403081f0b407203c0781450003280c90030120100c42ea0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 588298246 1250 588296996 588297001
    0x140304030210091a0a021c090b07031710050d08180d0b0f06041b18150810080a030503040206091306060f030e01270c0902030c0304050c0a030b0a0f02040b03 69
    0xa510034162812504c03205002440751100a441c144030380034038600e00c001a03002c0035801e100c44030842c8541401c803600f41060203c1648841d40c034484c41d403000e5025404104070b0f0303203691400940c40c00c12030303449401d20f0388964009080c540000d02c4039082c1000a04886c1004c100000301200540c810480c024008080412111040ca0070f14101541200c12480305102200025114103041c042e0780d02e059010800383c1001d110800041c2c3d82d4851404403005000f071900804a8001035000f07805c8800c89594568604c2e40c40c00000741400c1d0b00ba5038000c1e01d541d8006009080010f6000015a0741250341210600d403954003001c08101c503400d030301d501c465035641400800564540c02c061780c0905041156030900c1203003425401103003a5403d428502000c0414500b1003001001c3c412108a01244590750101e01d9030341e6406040140d0f0825909004000400002d2104004041007001003c60060710340100345899a182e003d410f98008100014094890f00200c0044025a040320042d00d02502500d450b030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 588299496 1250 588298246 588298279
    0xc03070f3f02010e0f090c071401020c03030412090b1b2104060e0a0302060301060c0f15142401080a09050a0501090b090609060115030902091302030616020a1403040302 74
    0x2252120410b0b4041030303001205240c0e074101030202440d00400a8420015511444a0b440312544010401d440e401300003181000000d02c01e0000f801010328801c01540c490410b0704105096094245c800c5081c4480d10b8820804180c01c10241c80001d41c00c0e460003c0001643d9680a081c000136100d4544220001c0e642d2040c50700da140043d200ba12843da442d4002c00303080509000ca40349207800040c0d4002c3d0140b0042000e5480707000d08c0c4500034801c10b190458121160b0751041c00c04040c600502030b803919140034220741400391070300c5a40724035401003001c000026005a08498600112407504001410000582c081034903001b61162642c08000ca6058614a04000e40209217800f800c82c0c043c02d080000c02c40c008000903003d405203980350040c0c03155910b0320000030a1822040010014551182042c6026079210f00d51a84100e048100f1103820070a203104150038864000d06410786588503050340d001540c2e00060901e0455031104445421030007035030a01b4a94010340e40001e501040948988640 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 588300746 1250 588299496 588299609
    0x60c0d0b1003051501230306010201090b10061b02180c0408030a0e0411070b01090b040b0409060f11130308070c1a07030f02070302010512060f030318030c03070f 71
    0x906813426901a0300c41c0010011246504124010855002001c0ca0210111014001140c000d0414000040c00058a5440c000c100c003084522552110310760030204082600400341056120202c00d411700a0300d8150300140c00c0c0751b001804285148201c03000500d0f8400190111030240c4049e50403a62688a22035005103c201e8483d0300c580924103007041c02d00030510301010f5410190b8030182f440c485030300b00f085800081000440195115032074620480e200c1e01da502c910080640290350200d0070004440e049408e640c1501c03148001e0003c00c0100d10768003a05d45410005481d80b200031250f41c2c03c410b05280c203d01c0d5082d005a481c0c0401e8405100b0300d4a002001800654400e440d911260501c07204180e8440c0c40c180b002a01180301084007050014070b08082c00ea121900901500000c038007200843d00c1c541200d02d41110807130154454040a00d0100b00b000754140007180100241e07400d101a80d00008002d21840f50201c070340700c1c2c2444044100c9a2102c0c80900403003901011060f011920381c08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 588301996 1250 588300746 588300751
    0x5040b070609081c1a06071e060603150507110d140c06100e0702061005010e19030b240d08250506060a09050702120a05121510050c060c0d0b100305 65
    0x11a541740522155a82d14902024030f103503540202003505045041e101c042d0508000c280c900841d2600d2500000040c07100d2088102941c000c20001118a120040102c00c13130f08054414002e22902500300e000905d00041d40103212800e80c5806610441d1080f0880c840f402080020400340c000c1d681003011100c542d441d03003401c40b469210303122451b8583d000107130b0f2185c205903648094095210300501640d4041c02c0080c805440c0600700ea1408410300241045000c40c82c0c00450341500700805100c24a42d00383e800f02403005020071615100f491820004400354030000b4014010710000c03c2240700216900e4886420b2030104900344024055860030726200e6001b140d2203441000511404107c203507040c403841344602e18540007810280c003800c03c1209160488180034081200030406085289014107105015840d024124805000352404104180502220781010040d0030312900703400744000100603401c2081070362166a2a107514450001806182a24603080304405d035070340c601194580c0c450751 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 588303246 1250 588301996 588302047
    0x10608060f1309020a0e1005090c0904150314070501090f060e0409030e1201020307031b0c0f061b0504081002161b0b0a050c0f0c03150903090909160506030705040b07060908 76
    0x24007e58880c1d00b0050000e00c242c0702c141403008280641246414282e03c10b000d12100040f1344a00c4540c1c0341e03030392074500c5100707505810716030030181e070400695800000c41006010055000304110b4104075000b8000703440c00c49094170840d269560300c0d0606002e640c1c01240b5141c0070309400500000d00142c00d001c0d500a80700103000a2904542031011118210080d0b05000f2542c0d41026101113911980c40400b007400701a01c40942c1c5441501da42004180302c40744160b2151105a180d614000400e030400b40c08078000c601d10b6004221000d11000c80c1410285000d07480300408030300b81942101000c090072940c001c0034022000207440302e08290014040c2000c0140c00f001c80e10700801511a1a4403100180d4003260036a0101d16000800c00500d4100c60b0f101d11440c00b22410144240001346112000341c079a554150840c1d02021444001d50345640081c01e01512940d1079410320f41c00041c030768440c3d8405c40740010404a030140030444550041040305802080b00c0362100340417210600011141c4c01003c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 588304496 1250 588303246 588303271
    0x90d030203060a030204060f230a0b0c0c04020309010b01080115020705060c070f0b1c09030e0d020d0506010308030f07030e0a1e060501031103010e1c0c050a0c031a010608060f1309020a0e 82
    0x6509ca1b11400b013045903017110251440c0c0c220740c80c0012000868010b0085680207000309040900d01d82c490b403001e544100011400460741c4180e5100140003541c060b049401e00c03200e01030140300e21940001d04c0f1021900d05851031a5900701e5441120f080070070b940c0003c0315942d0401400140c2c0000800503002744004c4075041c00520000e814080c084074015400100462354040c1c80d00d000c0d15068440b101d400b80080d0820340400c400756a03940c10310b41c09030022617202d0804028800c400c4214002d90b5400382070340c14204031240281503984d0341c2c0c2000d00c20060540d0050f0a501034054032140128201560100c0305020550716480d0008000e41c1c1d261400c3d02a61900c038010f0104000080c8042040b4210460902d08905040701190b40c03507015a42680c0b00d1280c82d00000001c3e01440200000b075002d104a1504145a658004c061200681c003810400c5454000d0114035603c1c25003845581c0c07000c48200e14a9a840c3c400180900702140f800395001c0900100003c2c50208845120312500700030101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 588305746 1250 588304496 588304529
    0x3030b13020903060a02092b05011116020d0201050712091e0506070602180d051506010905033a230406050304080903010b10030f05070206090d030203060a030204060f 73
    0x310000c0340a08401c0c01d83c16130249001c0350500d400c07640100301c019009440203061442e404007456911101100000c42d0302d09140c80c6405000080c8500070200c0e01c402e2229180240d500c0e20100e503000c423448040c0c443c0140c208683d04580c050803c40304403a910140c8602900041880940741d42d005118410991a40c800b074a1401030f0500c0c80b80065643c014586400c0c0b0324942c8404000b90807000340041c034050410100144c560300c1c4000c0c0c0815078810b20040c08517242201001c0f2407050040c0107070381403104100f001c1c08240e0700402c25250901541038038041310b14850315902c04c8041c80d042c01840c0c0071641030040c19401d51106210406012003007010b445003200854168940c400e07442500300145091000c0f40000c0c20440042614110080020409502c40000540d00c1c48445403081c0c04283c0d218210134031740185001c0c50f41c0c00081070000c2d03c46443e000c46865149d0f81c9007403e141c2050742c000002125aa103410311400515000b50041020603111441182204420701038070041260a0f01c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 588306996 1250 588305746 588305779
    0xf0f09050705010201060609270e1e0109120c030207050a060e0a0f05060a110705040203010e180a0b0703091b0e09160f060c031b05011e020c0a140709060303030b 71
    0x10308011900c1c5981c03442186803030b005007211216900040100140150205072748a54003a0041d0500c10302c5000103404c0d801c03540081015250008605428140d0408c2600f8010814001100c003254030b060501e260790400070324040b81442080d401241c0c2c0900c0e40d003000b0a84039402610541c0d940310030750f45000c0d081c4c2c6585440c001d0325100d01ca0745e42d0003d001c0100c5c90000d8814800e090014680d1800c86003110340705c82c0010300740e030000d0b04451220a440420400c203140c01407000f18400188401170403000300d05840d486441140181503009240d1249640740400150020101c00807055088000c181a140c283c61060303103800343c50b44400c51082c0e5405100841000c1c2c6410119414482d00c02e203000c0c600320341aa0114030540c0e081c0e09002149408503605c0342c44210108442d8031a2000142d403041234031001d0030882019662451591042c17125a03940b0100083c00380c8143d0300030140148200c006e031009403910181381c0007121060b08240c0004101a0148c100c590b506c0801c841d80300d01c0e03048810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 588308246 1250 588306996 588307001
    0x1515140a03201f021f020a080114150309100510062f4c0f0e19020405150105070b0702011b02160603150b09040f0f09050705010201 58
    0x1c05000009040390464040c000340503890b001c00d40c00b070485915800f0030a00c490158a0701450440035070000d6285008240124503090304280c0340b40e20850421010303070760040040e581402807051800203038040c40e4290740c03803001c0c504a10600e00200b0b907032850580c0300710703803214154610403001c00c0c00c010125000068011000094030b400d40d031400c2d8514030030407604030548940c143e0680010701c00c0c42c170710258900900848481c004101e42d070451480206410440c04c101008050003591000f07d41890070f17402814082c0855403d6410100c0d0b0003444080100007041c010b1080c190034840c0d44140c1c2c21014400c0800e01149008903001c010320303070300c0048030380d103c00f801000b141c002401001040001480210410740040f142e00c000035074112010300c880c140c0900142c0c00b50160b4080c1031203c20f44c0841042880107401c4528080c00241204001a0446600c41c041d42c0496000443d12110303a44a95020300b003038526070841485107503804140c12004008640060380e84c0d00550358003250a50050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 588309352 1106 588308246 588308249
    0x2040e04030e01090b1c02071a1905070804030807050310081603170f120703020d1b0305070e0f0f030c0301090b01211a041515140a 58
    0xb5000900301c1e903440e51080307841450030413540b65505500f602c032000410000c400961112094a0f0817020001540000c450404040707042001da45040d1104280e9901c0b4a441004a521188000c4802ca101210040c022608500101d1800c3d403086006603803142201002c0c0e100c072a100e80240742400c60101042100300907240d400e2060003681031a600d03140f501c1c80c615500d0240109441009030041070241410b240382800060b10036070080e0121104200042001c00c54404110075243c0a41802c04402001070f10705400280381900034010000c7d03134a0000d090380ca401c0801070030460030301c4240b5421030300742c0140301018116490902a205003948518065000d03581480007520146400390a50142148512001c00104100c0540c4500b1500841a81155641d07039040c510000d0b08410701030030503140350215165051401800000948130000e4500079903070b000400f00300c00100c0b00d = true := by decide +kernel

theorem cover : BRFrame.Cov 588129496 588309352 := by
  have h0 := BRFrame.cov_init 588129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 588129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 588129496 ≤ n) (h2 : n < 588309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
