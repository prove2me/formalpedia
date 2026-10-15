-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5557
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:15:26.6504+00:00
-- url     : https://prove2.me/submissions/19f26fd4-a411-476e-b69f-7ecadf647706

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 999280575 ≤ n < 999460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 999281825 1250 999280575 999280613
    0xe12030a0f0306030b150a0521070501171b04090e0d0806011b0201140d05040b0f011211040209031507090e09060f0403361502010b0f1c02090112 64
    0x8143c040000c29010400c403079210400045802c650010a40044e41c1071031250015580002c032030f1091005042e48031102c2607201e01000440b0318103034656005480c3c0303480814481c002c1c2c0c219100011284184240e0003401449090303280e60406803a491721000361543c00520b10555030021556105403603100201b907401c994203007000860900200044104070809010185c14004a6030321483e554100504032800c41c07880400404c15810149842001030800f03991208001522500110740b41200d03440c0b140d04c42d6400600003070494001c5060102a401c100e0070542d250296010812044c0040c10b0010710400d941c0d540c9a0b407103418048074103015400603290154640c09101003004003803400d0113a542003a01340c14810402000c4001081459602c29148815804a41c8803441407000700c1c0d5811055030145103a00c046414058001c07400c869108641e00c1e844412203c0c01841c9060400220006a8207010011048051900801c1d04200203a002c00c4c6407500210036801444070b07d41011044c2c1c200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 999283075 1250 999281825 999281831
    0xa030f08060a30060e0303160201020913050903090a0b0c010c02010b13020f0c0706050909070c120e03030706020c06101d19020d091101030e0a1e030e12030a0f03 71
    0xd004040c221542c5402c3e0110050550400c040b100652030408801440e5000005000880c5207411880d01c0c0d400603038074440c85d000071020140b00c20b03006009449882038013410303240842c072042d25140013a02018105038400d00003040800d041e901d542c00300301c02a01c403408581340d403407038801c00c09801c4804042042046924190350303030750103a47e1002100a5000300100160f12106502d0141c1d0491280c0c80b041d020600c12001c000542da90084040c0090310400c44548a007682c5051003602d4294841e0b1000b0100500c0007059031586015041408000d00003404580c10419142e03a0310040b82d101403610045035000c04100700c0c99410f6428090050804080b403015440140c00e02401407180c090301d0340108103400039040300343c45800c0c1d06075419017180f0b00d03040c041140c641c18542040000b20118500087c05c1c80c22107804d0960014080e1603403680b0078522480742c03110400300090202805c07800ca01308400303d041d680040da92083c00c0003400c540180550703580c0c2d020b01d402804005840e09520103140c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 999284325 1250 999283075 999283079
    0x801050a050f09040b0603160f0602010f11070f080c0d02010e06010611031818040b0601120606050d020310080a23060118090212100b0a0b03010509060d050f0a030f08060a 75
    0x715001d180382c1151788030340729441035110100000d0030429508075040e500c4004410003d41f40085c00300f04c03030459000380c008100000c2c0c03031900c0e2025070b444854600359290041042400054400120102d218002d8481504121181c0310300c50074404210580d100507912488164090340307003440031038010025801c204010401901c03000303881e8024007145100c45601c8600c40c8000c0e8072440e5002c851001000c0351aa41031410707142c10380c031612081d10b040d40046c5506800b8240200c90344291001e50b10b103070701c5450801041103845c04c080d61004000e001c3e1181d0704c00b400103040c1010880d80303004510071004600040c2407152082c0003056410315940c19075121900400c100d000d0b070501d408820700b14400201d0020418004201da00d03040c009404902d1145920044500349568400d240d1904101e0724040300c1569101c84080e11f00082c0101584100300f54042102c81c60700d140c3c6614458495001da43e54420900c0c00c0c0e40c1000e504e4003060300405c042901c1d2034405503100204550003c030480700445418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 999285575 1250 999284325 999284329
    0xd0612032f060412080a09110f130501030b071202030f130f050d050c0c0609030d030e0a08030c18010c0f15110c01021b03040b030a050601031b0801050a050f 69
    0x1ea1440d100d014420203038840c456001c003181d107004420786045000c9410754185464030f02010728a043c1e008000643d50780c04100c0e0202c1501980f1440d035086908214400402d00801c06c9c0824080c2c3c007158804c00d4030291400040040c01840d00940c0211071554007882c2020026008401c0014080d40303080c410810040c41c41400700c0455001100e030160b00c009901907190503074004080d000098550f00c5541018920954004010721100c09510142e0380031150982c1070040324019034442e658180c0240214001c254425440524101903c400f00d031a400f0294a4611040d407003034459a0660303400180416071010903140e1200807a0007843d1000340a010f54444880ca1004114010710611000c0d04d82c100100036504401c007032815050400350340d00030f0b01c2d902078001d43c4403500303a000c281c4a4107826101d000020060f10b0403038402104551840e5120841d00005040c014442030606036101104600f00042d00e801c00401c01c040e403185001541003c0c104058420075600031440b91000f41801c090a03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 999286825 1250 999285575 999285587
    0x3161208030408070206310e01050d030915030b011e021b0a1a03011a0f04060f1809050609012108070c080a08120703050c090f21030d061203 62
    0x9a8200c20101d0300c075115860000e02c03a1148407001395002e4404a209038440f0948180b1074140344082e03251400c02c1188000f0100c4500d0103218506207980c0c041700405c03243c203089041e02d00361b85c420314104840b503448490324410454840d00b41d400095940502c0d040a50300700d8080404100140003456003071005982c001d507a108400846000d20344203c05c09400d07030304e900780080f000c1c02c00c0138a8844452070705071032604550424490381103c01e0030f812a880c0c1d13200f2060308486e21b9440e592a128901400c09a0649a0381c1a444c004001c04c404542c02c1c5100b00314000e034070f03400703801d4220000c03425080c00c40070040c600f00c040c0c0001c2c0303488410740c1c829626243e5029900d02c4240e40700e80110340341d40c0542492105040c03a40d020b000503000344410f11040002d001c000741728101803114290019204e180007281241c1080f680720308001e500704065002480d01041014004000070580b410781c0c01c140d40310134550b89001d41c84410307503400851408210307001030107010054002520010f16420701501c1c001c0403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 999288075 1250 999286825 999286859
    0x8070c18180b0105010f092c0a09051203090a0b012309070203030a15030503030f1602060412110322080111091f021203070806010f1707030c03290316 66
    0x5100c07441b101a0b0a01d405655650001d00300401c0c07010640d144000c0c240c000040c1602580301c0c0da92450001170384500640b10740318807185c000c0018010158000c0000c40558005046041c040c42186501000500c080042d140600701c04481c42d44904a01100b0309078080c1041c001e684200c10300002c204040c3e81c00003c4c1d9a000d10441f00c0804c1e002003448211100b1503081d0400b4155000c00010025a05940d5140b14011418107142010302011428200d8076001c05640040c050700c5913005c4803032102e1007640d101c145c00d900c44094902d084030501c40109021040b0076a004507011075442000140400c0c49513007445001070103850720f0b10048800040201d00080c42141d0300031160094207d40b81c0c400c006106140d00351110f11075a03400c2401003c0d01c2d00d1000c40b902070003d041c0c28a500c0d4040d00c5000d48441c40c02c4541d0708203009031200803040c0c000e001103030304101c1090340c0c0da01495194418000c0d880400064103030b0440c0c40c5a9580e041c50300b00744a41c2461000c600c0c290b1000c100c018900205900 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 999289325 1250 999288075 999288077
    0x1b0902032e030b090d09080f06130c23150a0e240a0305040c060903150c0201150f0906060804050d03090219090f0605030c10030908070c18180b010501 66
    0x20108440074003007550450180c20240c01c401410003004014000040e01c105001001e03120343c0915666002c880d90f0710014460030250503002400480d0202503000b2010701c04a20511041c5400d070740316012403882c4610528051200101904102c806d406d0801d8854070040083d00ca4070f107080605800034100c50144008540035542e05558400000f81000034081640d01c1c841e0095130711907490704014041e00c41035900380c65060340044002022401a0411000c60303500015110840c0303411000c540041100c250aa0150354803061441c09000504c0081c0c000352017010405c81c5c2203418040c1203c101c41c80742d0480801d21540906101c003281000403490041c101d9403401048402562000c2000d1098440d440041c59403620404600e0360f0645e04040f0b003040c00a0310411130075658000301541e40d44080080e41e006402c031810313441a540711b034029005050082c0030b018604507460769440079070750700c50340919980d51000d001d102c034000141c003803060300302d142031281c2818441503202c0c100f5008041c41018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 999290575 1250 999289325 999289381
    0x131a0f030d0c050307050d09140303031605031b0d270c050d0c0f06030c0f0806090121080712110a0c090c120e010e10360b01031b090203 60
    0x8010003e04000f1116101d034040151390400f903582d0006494081c072809400d210710420b0280c2001420f000040c1e0b482404580e5090403640080c8009440301c1d80050200381e0900c1c015021214411103070350081040c6414100002890340c10407003408901d0107030b40c200218440c0c0840244012440d241182c50a45604450442640e1124504507c00c0c1d4070303543c001c80341140b10302d030009180303501343d0302044820110b500c030030f412540c0b116000c5608002c02c860042d80032031b10304010302101a40300004020a0702c07114009060308017036180e146298102180458010005003050442c05900000803001110071400420004200396140d491030300b040e0145022056842192a1405108a01d895515411b085041103101c104220300c5029041e1030308900080d110703948540b580d100700d6100b050070344403c0d124150006210407035409903800034202101c1740340c8141805030022482494040c0d009520a0707003035954404035080d403c04500c0880e80140343c6c95106008001079078554005c0792a04034001c9500c4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 999291825 1250 999290575 999290597
    0xf05010513030c081c020c210a0203060a150e040b0619170a05010c0203040b040b030703090b0f0a060b0901021015090908030604050a2a030b131a0f030d 67
    0x4680350070003540b01400080241000140301301010a011500000c604140c031906803d899007030740e5a0354498049904a81440702110340f02580300c1d5146040c941040a80b00d1314440754002901e05441502c3c075016156880c0804185081c940346070700d00030b06640d008414603251039100c3c50907014009240c00c1c000c44011074120301d0a28038203480005800c02c0841102001080c6211a903a07001c040340c212515807038802ca136801140008280c40c1201d000c4e030200c0b880c05051540b9410070381c00c0a00300000f45900c0d100d0000014040f02c2140f0301ca00e442d00300001d542e20b000c000910682d1840d0f407100ea0b947c1d408000c0c41101c1c0c0d07808a507641c20030000b07a41c049901070700383c0c00841c4a8074150303100802c0a45080d41100420520000950155001721030a0116480f0411024201c8000101100c0d521110002e40d0007001010760007150700303410b1402d0000b07061010074003103100b911400d40f20b40111075447c111017101e11414080d503282014103441d000e1604002d100480c1e9031740521641d1006118000403c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 999293075 1250 999291825 999291847
    0x905060a061209080f180f060d0f0b04051e15090f04050c1002010b03010e060906191b0504031505010b090111100e07053c0d02041509060e010f050105 66
    0x40a030f13203e0301856540160454a22039600114018491400b003140d1581281c80d008003921045540207014a00d429060340f11070006118080141c011545c035456142c089688500c2040e100307403c10449505041510450700f0840c0c01e00500d4081500f104449182c0e40c1d4031207001455002400302c5010f0403d4890b03007421880c00c2c21a0650590000d110740030300003000c0d4190400d03e0800c200342e00074443c1a00030388080d40c4074101214250401d80c030440c0001c3c690020b40a1040001000d81c000050300b21a612181820701c040d8202000440c0000604000300250078080c088500b031100c030104219418510b520400c1c1c454680441d0420144008190880380140110300240604140410441c0d5009803103c2c0c440003540b00703007803041905221000d02c40b2030250001c0c14140800c010b050044c10700c451a0900501203406854201900154040050700c4230300c119074924012000740d504652a003017101c000c2d0f4000f40c01805005032004010841003c13414144001c0d60000d09140742c81d46c4007905 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 999294325 1250 999293075 999293081
    0x60f0f1d060903010f0b0406170606040c18080312130f080904150305070509011505040e10171005090d02070b0906130311010e0402090904021909060608010f0905060a0612 75
    0x1a0540d05510309100050a050341e94480f40183d4020b4405000f00390381d44030384154840f41e41c040c04442b504510001400f030310b000d501207181c44006003880c6085090019241050840d26045038040d07070720004442103000b840c0d44166910411f00c0501035080c43d250b69a0000d10113540304001c0c14150b010036801c5041d030b00c2d500801c480401074030204034101e903070342040e558940705071081a00071001c0700004a058448903120851000e074946409150a10703040c94140c1100c1c0c0102268911144200041860301081845001101401d0003e02d00406600c108500700c4901a05042d0143e10803086c1c0d00fa02030300820f00f841140d02c15204181c65070980f402050700d6110b544600c00054141c00720210401500000780f001003a005c1c3c4c0d41001d00040344092008a129150050740c3c07100e1900e0000700107117030104003c608004841d104404203542c0e280d41c0300c10b450441e0080c9000c03c6105006024005034100030381e0041800640510407420814003040402103540580d20030408199008110a006c0f50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 999295575 1250 999294325 999294337
    0x4240e0307030f23071106090d1707231e10050a0603020d030f021002040515030406090c06270b0319020705070f0905061008180a0b010f060f0f1d06 65
    0x44400141900000300790264007039601100c44046e140071040e414140b000c02e8508036507014141074170700d1031140c4aa0310110045c500441c40c603c410807100c00000c070400010b5130f0001031315080c400304140400002d41800907079a88520031f0b40a004c0c000c0540200040d920040d1501600005803d1325016044c3d409040260030180d0420400c0400d1020950700c0844c03100040039a13400d40c1c0030201c00c00060b00503440f6504c21280d10038060141030300d86d04a400c0c01190040e206000001d00d4103466035030f4142d800e13000d5010310007060421009000f03440910007400c41202209015a0009017440d0003565076000242c10304c8030b07100080c0201a0b1520641d4101e5613104d401400b1a03081559402e01c1140c0c12109000c0c0844403801d040201e406030030003141c004a00c0d60030b91905d410329503a00040f00310304050740341c607010f162040420700800316040d00b0000d4042c0840c03003080084141031580180c011080001040c04001d04511110030050b846020301c103860200e200c007660f40a800300b0001e501c0340105 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 999296825 1250 999295575 999295607
    0x20f030a0e01021216140703080d2d0f0606030207020607030c050a0c091512020f0622090b0f060a09030803040609060c11011a0f04020f0403050604240e0307030f 71
    0x40e04000301440300361203190b01b4824405100c0b420303c840d404030788954003884002d11040040c03080c001203036410303041005000684442c10f03818141d124902c503034800f03512000810a030340d51a680380c2c0041490280c28080c5c1101c2c03d06614103903040d40841d11502c80d186003e020481885851410450144031070003203542c02c100e8450181d40c403801588004d00000078520b10b1002140c1c0300242e0403083c119039110142d00204880500c2290009111b00b40c0c0c040d142d0040421406a030016802401c5140300014218242002440d41d0001090240c0f112000b51301600c60b010034031401650300c0d80644500c09a80d441000c1c95100c1d251407410402401b04c0820040c551401c105050300180da10402c0800c07955808002801012000c54106040c104003a030307940d80001d4080024121030420360018140f00c5030f0411914541540ca0715081d090070025a030490341000034104004101c80140b55100c18179110040c1000340700001c041c155528030444030300409120050703070541140c9009021b100c03007003011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 999298075 1250 999296825 999296827
    0x2a0301021210080106051c030e040e031803120408070909020102010f02030103110310020a0f03180c06020303100503010203070e1009030b10030311060919152a020f030a0e010212 78
    0xc0703591094221a02c5004a103607070740ca0800001024a004141c424030180020340380c00200925407021511314102c690b40603000ba4448503043c0c0c2a800800090500010b801d0348600c2e1501000101070030007603460001c01c20316006010a001c426030210760002100d04101002440c503e040c030042c0e024180b002144c0e840584080000030030301c4044182190600c0c411415101041c54485081c42280608202900041c405645072000380d4000d90001d02c441d0480003810044103910740e98003d032035626070403013130050b040032050105002841282c3c1024110441c002d60943c40c0c050b0740204200e6a01412034450b100603a1078501080c0115224409160002203d07541490f103804808100f0301244000c0300000c005002a030041c90700400c2142c080d40303c46000e00140b181c0f40c02c222030180a500e1041c0d486549900c817141c25415544580a140855020109520540028070140e24086c1c02c1022096401070354220f000a8004822540c10070540d0420390f0f42d20801100403443c0c5021a40c560b01d5200d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 999299325 1250 999298075 999298081
    0x121905072904020f10021b0a05130b0a0603061206020a050c011431021011030c010c090e1308030a060f0308071209082d0a0309030b01082a03010212 65
    0x9065558244180d009440c4615590071070b005005c0c40e007030812002c10040c0c00461820354603480803281401c0c0d00c40d0041486546030388440005445c0e403100e03100c42072aa07031b40d030386070302c2c0c49040a05850000b8132680c2410052507180801019000b80a020020f2502d80c0c0062203407552800707181942ca00300c1001000700b02441c0707425042c21403100c0980320180f5103500c0b51003c0b0024621810104c81070111802d801c200d980744e55003031100a80004094406100d6845a880c00d220307020070103044011604000841c900900c160003030b183c03046640200c1c40c0300001908001030440f01d210603900080e4031100c055565581c00c403142d8001c04540d004000c0f00302c0e07200070020602c0a0180542007480c040d07143c1409030451013605480c0e0540d580310344401c83e080550b001e4824100d40c08402c18209080000d2801d83c00c1081d00e140c10203103040801c9010888c0c0b480e044c400c2c80802c170000b6000d04400401061392180c0140900751060500c0d142c00c807a000e071446200c04c82d46080d01034a1091810849490303040c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 999300575 1250 999299325 999299393
    0x312030903140c030414010212030906193815040e0a06060816090905040308100603020a0e0f040f140a0b010305010501140a030b0303030c0c12190507 66
    0x1000c601001d40000c1d2901c44001d10b822610812030300a212103c000b145004c0ca0400106600100c0320b003221b065000e030862180041c0b400c01c005521a8881001600840c42c01d500e901c4000114461206034141ca4600300f13528003101140c0e02c3c500c500046814812030a440444a560082d95a4845800240c5401c401030340340c04c07a002030710a03500300c0c0100d12007695640800100b26112131150b100001c0307042001c20060313103590038200c41da0b50b4686010502d440c3c07208100801c1d118262021000607001e0410002100c010b050220050107040c6815464a00c2c0408c1c01040542000341d2035204010b22071240d00e031995198007900c08541c0d03440040c0b1102142603c154031007a41100d242c410302d41004030074562580300c0e209060580350705854030802902484c64410498022008441c141542c0390f03008115a503007080510700c28803610440e1a95540e10443ca82d040040d01c1102c1e03000c0075814007100d08a4801158400b4403d0054540030303440340c0301c0d0300384008200201c00b41c80c003120954402c845101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 999301825 1250 999300575 999300581
    0x3200706111b03060615040f0308030103050d090609051327050f0c09010b180a090b03160f0303030e0304090603060903030605010f080114010e031203060f01020312010915031203 78
    0x1205424003a00d01902000c03000c02c000c1c03980801c1555254210300c0002c0c100d403500000a40c21000e040c3c0502c0c0c185a1148416006812241c0003500d0030980440100b0800500300003540000000c1e103810401246020070251038844203016481c842c205048400c608440594811070aa08280c0c8080d011030511355001c00b98040c0c00300c01a00c0354002c0d2015962075007000900d42c00b107000f004d080780c20107a01e480c2510707440b03401040460642480485800996903104901c100140c444000b00050300d0418204041c03400d80b89008401a107200c25404001c1030b01200c02c81412030703804d030902040d00090000094158465600100340d41c03891b106011003441290340c8403040480c0700b81c600b0007a0a4960b0b0054908014a980b00c400251760b0600600a124680218066240040c1000320b5150320315000039040c07014814007842d4001c030103c1001400d03e040100d40080c0f910a00203140b9000b15016201d08111050103541c1c41107407102a44110078070242c104600468202038030445100c83c2c50001009 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 999303075 1250 999301825 999301847
    0x2d09031f0f1401051906050d1e05070917240a09050a210e0904030c03031b050310051807081b0304081201090e100e031204120201061e0303200706 64
    0x170840c181101c000c144030000d90405a5000341c4690f8201006694000d0140c81006907100b002030514005907014030081c05414014035140d215035881904011070700f41c03d800c45c003000d0b031202e030310401702d003032401802000e0700c0c2400104809000700c1381d44a0000b40b01805176150001d0282c0303d0f25114000340406100f01d0044000303402c88480b0250380b01d00d01110001d8500c0303140e96100c51a00042030020f40100e1041c2c404d80e10a0501141070b0300d60791710101343d8001800c582c1021400c00420070864440e80c501e814007600040f40ca21640c4800c0800030101d802c0014412000d100481000ca8014803211070200021302149003900c0d96880c140c54510000e4000801c0784d4083c1e02250300115610700c1740c0c0102905500c07100c006000c410000302c000000b07082402a50b5030341c0d0200704101411104601c4840c1d00c00e60044000d5502020039040080c210b8030242c4c4075807010400c48001e1088000101a401304990700744c0f070500788518003100b41c4800b003d11440040064480d644000580d0742d080400010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 999304325 1250 999303075 999303079
    0x1a1006020606030c10050c011b0207080f070308030708330f0d0201120f0f0c091503090f14030d0e100c09030503030c1b01022d09031f0f140105 63
    0x4007900d0b03000030300d0b80e101c55460749030382c0c41042e201c58070309498400c030040d0481c3c071165000490320140a8a0030205800c00000030710068000441c284882c2c40204006089103504034001d00001b85141c0b0b80000b00d02002d4042410801c000011400303403d865808407501002c14148141a80204194801000080d0642c0c3d030048000200d012460b1400c4640b2085c0380d60103864a00740c00101c0c1c1c0c10603008000300f40d1040d9030981e895050340308140c014400c000c0e4041d19034480798100d605084d4280c04407203040c0701e4602007500b019103100000310b616070001d0368580c1c41f000301e960a20060b140c181c11801645482601541750946000e49540700003005030311516031000c1001039400d00081101d1188140c040500380758800c00c0800d8009401d4801072000c141007120f8440150011044207007681d000350b0400035041d104008110080d842c1e402c0601d445610101c44520344500180441d07190441484001c00e01c1a1030003e1294503101a0003001c040c00e62210108200e1411152800e0b2680e02030040b06c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 999305575 1250 999304325 999304333
    0xa0503041805280e07210204050123010309030e0402210606160b0901060506160b010b0c0a020d0320100f020906031303020c060721031b03091a100602 66
    0x203004800d41036038039444903c0341d004428031030310307403d144001418294403110204d01c102e50000428040c52030820f1414019900d90b91140103d9004108c161101a080391450340000140c840005211f50040d6000c0c86082c20f011402100c90700f81640c2066480a240390800e0000505011403903001501160320a11901e4096903074981a0600105000700040c2403031501c0d0303542203034005c604060500c9a00021400010420644079404034929401c0580c003503001e02c00e9644100c00f0051080a49401b40c210517420314289104420080c5d070380c0e401004081c0c056003422400b50705040c40f544011942036100001409402c099441540d174480c2070350b80014407140341001020300c0840c070f030080b0365140000070071660450f20f03242030108203010701100031401c1d0320520091000d2510707001c01402200f802440d1001a49503020001e900080c030380b0055508040c070b0f1080c0d0341d030080400f00c44a524840d0780e18000070150800e1401104107590400075400c4a095a0104290110302400c41b50640d4440e500707407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 999306825 1250 999305575 999305581
    0xf12020c010908061003020603101703031e040c060507140303100f050405070c1b03060f0212061f03020a090b041724040b0406091208011d04050705040b030a0503041805 74
    0x1044c0c852a00341c1d046650021080c0d420000751910318042c5401c410107200301d820722540c7d90315129440e0711034400c05102e41c00110801440741d071640300001c3c104081e40d0ba544003074a81f03542e0b030b00058845405010180400442c00ea81840010541401c443e1101001c4030fa413402c1840e10b0180b801c7ca14030400812f2003c12001141c903091074001c075402882c1ea40c6a000c85806940c0d43c2c4140b80c0c452021511225103640400004102c441c010000c20700c030344e0310005980b80c0d0311070050340d54400014265401403000140003c04182204580b2000096a02d00103896a04400702144d6001e002c0d030000c0c80220010802280040c1c1c07200f0303140f860403910380c01c42d43d0320070a04220707045c9201142c6d500d10281c64001300150104d0300152030107074003e20038880040e417044950745800b18410004001e40020303148000500030a05c101c44405c248100c0994030360403601e401e9444c03a40c1c6903024001c82c3e0282c1d8442004070200d440400850041e50351040640341c482d80c40b8107440b80d4460b05850210100da04201c04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 999308075 1250 999306825 999306839
    0x5070204020a1806200312160c05010908033301030b0a1d0115140d02090402041701090c06021b0f12030c100f0c020a030806131103010504050f010509040b040f12020c0109 75
    0x1102c02018a9281d42c10301d80e501c002002e420703235060108040522040c19000340000d40c00380f10345460a8810f1200f030f9140d0030080c01c2d0121402e08000300c1da0340e004903800340420228a1443c0b6242040e400d00c0c01249400c011804110f0010307560b03102000c00b804012030b517049045e51401d0f903170698107844034274991350302100011980e000c003601d54007082e0002040904242546070700140503106002d8001343c9456a502c011201103140b03100b00180700e07590b50900608000501440100410480c402081821013103c041035040d01504c52052041f1040c3c0441c1e4111745440080d081e114628400b52915994210001900d803441c0103a184010b5250941018100107544500c04407441c00794020012070341559000e651001d400f41c1000d61003480c510a0072180700c0d55004480000019114513622540350100307200640704040c02c107500780542140140483d0712190000c5500c990040c43c000c54075122410032410040c11100007402d410310308c120300030404d030b00012800d00e8174400fa80c2d450507055451603 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 999309325 1250 999308075 999308077
    0x5090a0c0603050403051608181009120501060806042001050a0c060c1103180a09060b090d031e03140709033f0c0318030305070204020a18062003 64
    0x21006108880d03042003409990311aa0000313030700134844d00b03026140180300404040c1d58800d0030011210480f0007d01031004091500080032404001c0d2490703d07280c2d80000d40607204642d20301482c00400040f146444c1406000d4100c040104042000d07100709007058102996803a0340002e51040c1d003190f82b10020f80d1035100314200ca0341200155a0140a4980c03a07031440c000d804030010900801119a10042000380284000d0444407002000034022841d1070341844114050b0b07500c484041882c10f4010000740044804891718000101d500752555a194902941e80820350f403950710220951038801c04000303805070b000340200019295403e06980d2209412940941940402894405950f000c0000a007281d84911100c022118514a912640d40c1860b8180c8102d01ca600000481d00c0c0c1002c0c00780f54000c640e07080301400740070b000f030300c030604540b030140086c860400001d015a40c00909840300501c90403022a40e1020003a0325405070343c0e1400000d01106022000601c0c42c1010042c0d4000f0f100004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 999310575 1250 999309325 999309343
    0xd030c0804090204082b05030601030917031519090506130204030c051c0c06030e1e030a030608030705030a26091c020f070b0a02030417060a0606091d0c1603020a060509 74
    0x100901b604000d60340e00c00c607501d41014080f04d06142c0c8445100000401c0300c8006012000e08100781502c900c0d08100503c7c41d00208809140a40c80800d1500c00c4c08400c002c91100340e0300655000328944c2c84140c08615080d02e5000e03e03c52042c40031802004200448010f0000c4403011207180c4a86504c01c04d44001068568100500c0304c2c5901d901004402d0090304012000001907059403103003501400c0c15040b08592900007090f5801c00140507030b5103501441580c000c1c1113490011414505960b84196403403103171404036000c0c0443c0c0140403000c8107020101054010b0808556003580c00c0c00f1070f0242d81c407600c0c0200f00030608550040c40d207aaa100040103101a4000c00080c402c0a140072086039860384848001c40442c0010003000c81c40001e00640c0c84410310244004081d24035100c80200d045030060b400080c02c0080e1003a0801c52641140c254060f5201c040c1500d9030705803247c0c61540c4041c400c0c02034114048500921040500d40c02107200241c4d240284414002d81e50342c1d6020945940d640c3e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 999311825 1250 999310575 999310633
    0x70b0f07110102100c0c05060c03012607030204061203031a060711190f0f08070b04050f04060801111c0e0a0b09012403121d0d030c080409020408 64
    0x40c0540c101141c4440900d4240d80d2060050b6899900345285203c26a0307148010b00021a00c582c54580800100b04001da5001c4280002c80c8c0c25541880404d01140d01100036501e003e4240038000f0b1040711060041000641d4002c01c2041069681e004c5599011980d1f50290081303031920024a0500c8070710040090b004030000d01d61850181c0c2503650742c0440b90000000758000703141d41c1425030124400720703c1c0070290103c80c0251140d035240031036000d848465600200156000300c00100010b46011041d0f41c10343d2011200890314900000104005201641c40100e041d070810781d115145900047c01232114a107524a0103006048188038039041d602540728a0f0000e0b40704c4080400414a40e2a40c6901f143e1030000110b005c140715031045a041034074203844144070382103440c01c008010b80480a45207070415401c18074514049500d40094030903ca1451600488003100084205840703070558400b0039602820301ca448984990700c040c000d410502903030025114840d2112507080c1658900c0e4021210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 999313075 1250 999311825 999311827
    0x902010509010309051f0923030a110316031e090b1204030504030c09050a050a18080f0708030f160c0f0303390305010f03030804022b080c070b0f 64
    0x45800440042c292803001707139864019030f26909010410541081100d00c100b003400300b40c2d1200707030400d058101d483d040340d92440d1140c02c10858182d0304c00700036940350340180e00b0704d00000301c0c04140260843c450100400d840c0c400c0c40c40320310b0415070001210741000c9a604821000710310440015600b04419026000c5550002e2055102c410055000c480c2d0291003441c05034145582d907501e00000b00c00d40d40102d20150b8a400801c40440c04a220345940024014010711924410b03144071410800d0250b009810070000148800e9003008080407144510741c4150000e0382da10340310041c9040050b050350003581c0c2c400343e4880300c500d0174811502e400050f90010301101041c0c00ba40c1d4180c00610081c0400d603540042080a00b00c4084d810450603d0300030004a50ba40720700d15404001d0454005801c076103100c0c3d8142c0c40c1400482e500442d650b44c42031f070644100e21100d0710341506980341980c0644c80d5050b00b01c0e04010400308044600500564890304080343c590603101c1c40d68a800d40200300f050460058 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 999314325 1250 999313075 999313087
    0x10c11030f180a09050901052211120706031d0a080301090902011206060c0c090c21020c070f0f0602030a0f0323010b071401020f071412190206060409020105 69
    0x2100010b10310003954a510718205109180070400c104000e50210320b180f992042040081c0b002805016889030b0740d16980301c9002009885440e02135141c627070280000149100040b00c0351540c2401c0500e00310008103e81e00d403039940d50003d0191082420340d521489180400b07038195180090010001c66110480303d066070300340300803180200340c00c1d0b00030790410011045801340480d191150102604485d503ca031080552400d009201c00074a03400b030198645801c0400c1c0010b5070041180040c4900c0c44e922881c11803a1980390300282c0100c071075043c03a0b8081c0110028140c039007002e50404441c3c0c0040c400c8d0000340d440c4000d907120b0103450450780101d4400700c080080288240c1c1f01c25455410f00c07480c000340d00705540002c440c1420980000c0201e4800107068003e21015000000390096a00000e40c54419145c2c45e4030b019008992005200201014154004150500100300a460380070a5140c44101071038218512140100140015014010114a090410b4040d8414003901038445502d004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 999315575 1250 999314325 999314347
    0x5071b0906080a11060a09051e222004120c170618010c0c0b09210307021203011214070e0928030206040813090204080318010c150f0209090a0608010c1103 68
    0x1000200b84240742d20960901120b580ea4150040ac0c0103140c00d03a911140c1c0345a6150041100c00154a848000c0c0302d0a03042e8699103400390072201170700c169031007031442e903541407811306150a030540000a07064800d9035240900400050305503c0b4020450070b404802d03003500b1803582200e0307a0400040006080054650106118400040d0000209012500c200320051091000104813108940c0322000000501450380d504006103030050001403000c03450741d4585100d07400c1ca0064044000e180080050b40810f5810081c00704800030604140f101c0f10b24034040c0c41094540c4084803040f1800c02c0c401844200c4800c440400c95079465041d00100200d072240d40f90a82560013403840c04c0d88441c014840400e41e0269070000c1d000501d4200001c5883d0028900605403d0000d580c529040041000424010071400860558085000400003604058088460f0040c0c070808003981c1d0481c072044140120b41c0307610b0780444100c2e00702c00020031075201c00391400c903408040c922443c3d03841e6106000c01c00000b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 999316825 1250 999315575 999315589
    0x305060d110f0d060219120c020709090314070c23130b0a08010c090906060201050c0d090f020a0617010801050c071e320d05071b0906080a11060a0905 66
    0x900030080601409902554132502640d03c80740036240024a260f084018481e00030288a080190b000401d10400b10420402075880c02d40e0304c2118201910b07501803605050094006c5000090401c4255039500c940307003440d045c0c1a10790320444125110403514040c84202c200c3e50307030b00300701c40003003281030300b805000b80c41405450000900c642c011803030f00d80050008024415024200303c1c64490121036454441050f0464080d98084010348e4141001c2000707070f074109011078081841590f400204201c5504010321942003240000350003a45003400031800e42e030040c0d80e640d065012044440e540360f0300c0e900c2c0349080c0d4400340c0700256955024800000003505100017155804904200d40d113408444d52500b0162003071135021400e035042140344c02048070300d29081683c410361036100100000142040001d116204052000e02000f403040901d030343e002d41c603810300001040020424800709444008142e21084418011110b080352103080940c8c03410494181c1d440f044898889840951400c024041c01c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 999318075 1250 999316825 999316849
    0x809100903092702360d0b0a1e0501080d0201060b0327010204090207200a15050c010f0b0102070603060e06060a09081617060f04110609120d0305060d11 67
    0x75440c0000340040c001009101a2540401103040c90900c94250382c0c4040c010443c0c2c201205c480c08144203048184d84804001c0c83c1d80b942c0c026544040799848141c40c20007001745409261024401c0000840310500d1600000e060760015020399150100010381682200c0c80d9110328001100240000707054003c0e55400041000101522400400035890300f45e0708a91090300300440e071960101d08842402445019401e8480901d01001411000c510001d160703000d0512500000980240b14000d81c00d1051050361212a9420002c2c0056414049140050201000300500504c01d140b4001840e030f100e409000700315501090b880b4481d440d00010300c85517500140c401000e101c11808000350020f0108441c20081c0d00e03003500303240b03050f080c1040c1c80c160100720300c0d60f8070496010800340a0036680c4800300c5a00598006d4440342d180c03241602252003030207420030f010b034480d81e071802182c09030001164043d501081a41e007005240d41e8401040f4070205d03000d9014081c6100826810941d040030000116 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 999319325 1250 999318075 999318119
    0x501260c01050c12040308031503061902250510050a02180402070f08160b010e070806040506031f050115020609100e010209060304080a0809030c3a080910090309 71
    0x145060240b030076104e50707a01aa00031034040c000041000141e01c6101103000c000072080303001e0401c5082c00c11000c105000b95183c88000140d0009814500a0000700034209081e0f4030382c2501c07003541050500c1c684801c540301c0c1c90042d80c0e0520002842d095440c1c0700b11800a000c0102c240010000c4105004c002d40000404950a14500200c600824113140c054061604011010900c45a940c1b40c80d2030980410b9110300d00601c81c030024007841e5a04490010350207801234400141c50b6494000081c039105880043e0340c1d5070200343e54040d400422a400c0740d8181c40558401c2c29981e40090400c0740d03101c41c102c1d46100302d500180c91581c2c05e6a00e07500840903440d085000582000e04600000d10a03900981c1d003101c100f1070005500d0103442d0002001030788500820091070030000b450180d2a01d41440565406841c8400c034401c80c4e182a030440d00d195600400c6010040c0401e9211016003072400c2501c44840d684184034a20b981c40020f40100c2c8180c5070316584010f0441c3c0b4206482c540c0041d070a00420b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 999320575 1250 999319325 999319333
    0x30b060c120f130f061704020f010318060c020115081c0807021203100e10030c0b0a090e040804030209010b090a0b1b2b03050c030705030603030705100501260c01050c 73
    0x703c0e1880114898024003825004000040d142c404080c2c001c035500c00002071548005020440983e94000790610204020b0a0110705d68985540408140d51342c180000c00c0366140215000e0b400350705501c0203a4501118142980d442d1b00d5583c0103644a20450002c0c00120403101107003503040c81906c0c0c041c1c00c81c00074011180e007803004a4038044540c0044440c4258620740c0c5104102600510751a40e803c440c240c1c40b0007003094110b0300c480442c0d14035402460303d0390100140035440c051184000c500141380f1401c4a402d2414546001b80301580a4030040e44200c40d040000700b082402c15049070500580200015046840d210b0010400c2d0070a0084101300644019180c91901c3c091103003c440841000e00181d103210980240e02c549090300001c0401c2514020800244480c404105c030b400000380e041c0191203950360000245544071703643d401070003402010b0412414003625040f00741691085052104405404003403401c1940c00a60b00d081107600c5014200d2035540241300a21000c031017a4162 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 999321825 1250 999320575 999320587
    0x303071412010305060403080f0601080a0222030b010f050a061e030e15180106050a0e0402030c06221208121801062301020a05060f0a020706060b0a030b060c120f 71
    0x281c00d2180c401d90040d500c0b42c10080802007019401000542e00c9005144584424101207000a2400100030a1804003942c0050105a06403230303411400a640d00030441010b0054880c83c10000803c028403815252801c6600007251619155030013006490f010b644000c00a03400c0d00003044078007440b243c090189a62102007001c0320300c2c140040401ca40307a108000c0c800e428840c16003a4030245007206041c01e64035002d42030080b5501d61070328074102c0710500e0003510107031501e0000034140103c04600383e81c800303c000f60b81880c1c40035000100e9808081c407110808901d179602404110003501003001040c500b001c01240c00202c2d00c3d0307017001d0b401524140a011245aa840f202030840e00c0700d8101c525409030150400390345007803550074800f6010081c806080480b06036510a582c03080081c202d0301003180f1090010310f4103240383d41500d8140790001414000e0551300c00f41e11019900c100e9a040009042103101a40360405170101c0c1c0d4070941c144014039460394140c26500140d042003000b40d107103031410044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 999323075 1250 999321825 999321847
    0x507021507030f08070305090705010305271e0a020d020904050a02030f1515091909020d0f02041404170a020a0c080c01020f0a0c0506070602130603020d0b1203030714 73
    0x907082181c03283d01c4040c000c035240000982083c030f00401181c1050b080c80100000300b0780110b11b01e811181e003800d01152503112500c546190300a40d420460703800d26444111140c545001601041d040504c69841c030b040001008625260086420040e4120160184010050070304d10080f0741d1141c000e100f40c402140b5240d0009041980d50042044264000076480000030700c00072101d50080c0808403a0700b130010018010481c802401092103a200b02c00b0081c10b95034000315001420890340c01081041c04440500d0085400e800f1003406030300451a0040018104129200c50b502036604010324100150300c02681c0089030340041240300c21070245003d602d0001d07001c4101c001c00760080e40c5c0505005040c0d08002840d03c03540b90002c403981d501a04881000c64071100000b01550400ea039030396510401401d204001c2c0c4038061784a071400904040002c0c02a51503401b80166101100040c031030905544100400684000f000a150b500100046042140540b0000c0000c0c01910280c1c0d0030200d901e60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 999324325 1250 999323075 999323077
    0xe010501050c030d05011427040f05120706140901050912130302120f0d020a030c0b0705070b10080c06070b010909020a0f06110c09010e0f060a18090614070c0305070215 74
    0x2c4a10703c0d1447c5004800b1062418040c000c0c003d2540645440503007504070f014180070b031400303000605140b105030190700501009101c04208070f660602c10658440c551f181c06c400821035600d00441451400380424031555040c041c2d24011060300300204001c0504200720343c040c0e400000015070f1060800300010042c2c81d1007056003007862480c001351407a81c030080456410110a081d0240854002510880c0001e401c00d6110603a40c1d040717201c2954907501c081050303a4600c51500040d200c043c4103003c1103184903074a0500029075039180c06031503c0340341d140e06010725806090700042901e0a9040180107540066100c809203038001481c00d0742c2981d8661090342d0032401500701030006260842268035508040242e41440c0d641501d20f41c00c59894040441403500001e01403c010700400c00200304207944101e080009040101000b002c105890071540c1c000f0700051004a0381c403810305441c902510101c079040d9215881a4a130303011520029135003214560f20800c0c0403a40524050105810489508 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 999325575 1250 999324325 999324329
    0x2a0118090e070509062413030f08030402030706080601090e0a060b040303020321060a050d061407030b01080a02030114241207080609070905060d0209030604050303060a0b03010e010501050c030d0501 87
    0x7002818000d8100020710601c104001c1100340140d04c2081c8940149070002c1c140d80426502030300d940d403610f10f01c0c04908807542c11640003a0a000c2180b030701c1c4052043e804019409107100310205c2b850180c1d0303090180d404403030441c5c20302c0c0469024501084040000060130f03900c81540f40001422a85402404003d6082a00154010f80c40403402c00045003151100b081c480c01c0010b118802454004000742c600c843c1c5000e014002c2440e0807402c82048680d410010401008038078164a520345050010000c04884116070700180c10400401c0c481c1c140e61003140e050711f070441d450361880c0c80c44006100e01940c071a4072035505203000341c00c08003022000c1070141c41400c05a5510682904007030000800720000030704041d10540081c07041c4000c941d0400014000c851094641c2c41d107030444050a04000d000d031909903501030141800b000704104022004500c2820211400a0847d480f45002c5e09203000034040c106422080703030014407042d13000b40050b2200c0314609044034500b080c0200135409849003a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 999326825 1250 999325575 999325601
    0xc03050a030908010522080d06150e01111b06190f0806181b0c01020f0307030e0d0c0215190905030106050103021c0902181303022a011809 61
    0x92034040d010164400002d500400c00e0350000d010742d0030840c06060500c0000710200080c401c10301d0030001003181035819201c240c10070714010443c41c0d964009540f0706078410752074030000809100f100c03900e5600950074580d400c181280140340c09074120504000001d01c90300882d602c0b030802d114010300d006c1e203034406210000d00c65407080302d00031022101410401c0083e083c0741c421010400d2604104482c0c88825600100302d0728451f141c04c4d81c2210303610191160368000803482d4000582c90440f48440401103015a220f507404000710550100784a480703814111081000030001c400081c0075141480c121144c4d181c868024510b000c40d8511062541804418a0000b080307000701708209031b02c1c0a11501000f490203080952a0032071885d001541d40e0035200c0144543ca03964030112080d91181441c020680508459000003420310301240c0280c420300c00300850040c4606041c11380040c5c200c410400c804450300c0241440402c40000540f1232100c0402c516002c62246c840006881e010341c09001550b10071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 999328075 1250 999326825 999326833
    0xd140711070b03011514040515090f12031822050f100b040b0c07030501060f1a0708030112020d02031c02160b0f0c010b13061d06091801090c0305 64
    0xa56600d941030294507407202d1420242400104441060840c070700060f00b0003450010141c20302001c0d44050350080750001074011140a80c90b4107002c84002c02048030240c203e503c41007442c80e05041005100c01c210040c00990801c0c17000c2201026a0749054044d402c00901030181e203101c010781c126070300c1c20016170381d010951940f0900014001c141c1030180c100c004004a900359030b09003600415180f1407032003543c0f1045030000d4607075034184007888070201441d400790087c40f00030303a61109105030391204d00a1043d031300c0a004821002c0200e660403500526030058100d41985c3c6440b1944807441070547c8107a07000110ba5059000594040c01511414011030809401c01046d0010080c640701b079a018202c507008140409000b1695640e003a14000e028000c00207980d21000254240074091800b1007030f400c0701480d580780541c68056004181943c18080300c2c3c04070001000c101509242c01524080e80048852001c1202461501c2001101115400020030301cec03444c6544500141c44c03554825145504 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 999329325 1250 999328075 999328097
    0x503090a1a073b0f0405040b01170a020d021318050f0c010206010e152805040c0f09260f030c010c02120306010c1403190306290d1407 59
    0x90041c80d0114003038040194003e00c030058841280388048a66120b14420b54444140702013680c4100700e00001c000064414011820246003120b440e4200b070085c2d144038030b940001d890060710300040d06072900e50000e25144080d1700d07580a0180354412085003e003071030749480c0c1181e0b004040c82c94036902c0c01d10640003000e60440880300d403424003200c11070300341c1150001801003240800d60110300e60009000300c104d24030316030038400181c0d0310401031507400c141c0340340460074804035840201c5a504a400980d0300340b090780e04508c4100c1d03d0188050010000c0350818400303000060400c507600010042d4200b8418415880001e030620b0902c0e070741703444410b99100242d82d02245c3c074280500b10242c1c1e1540018040080d0300c0b50b2102c25808000c200034100a6001400340034046c0340c000481036400002700740c1e07030790300d078010006202010121100d10209003801c900046081525202c45820400010314070809151040c03458100c6e071002d00240100c0b500c074411401446074000c040d60180f400c40d118004406 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 999330575 1250 999329325 999329327
    0x2703071101080705210c073003020708030f04080d02160c0902090a090c0909093c02010309060e01060f08070f1202010e040e0f010903080604020f04060503090a1a07 72
    0x40b10083c000d00800a007401442c15144244000000030305142e00b051280c0d070f644071003441c0d050180c283d010f802e000e4508641490070000c90300700a04000703030103804070b80741c005450154281c0c03280d90740c010810340382040010560208503144030340141c46041c125250440b9007481c0d000760b80209410044a0b00c4009100c8104250a1400002000721030800d41c2003a0390140013800740d5180c1d110301003005450700100d40c2800d2003085284003800d89080c04100b1441d603030424030071a443d4581c0228240701b5800b150040308000c41d090308070030b400d1000611908101940110007070b01c2c04a208840043d19201509080c090a0066130041c0c4524602c800e0301c90f00c0e00071504d02d043c140e07602c000501030110100b80500a4410080307281d1a4080c00c10105241c664404140140f81003182d04069009020390070040c1c07a01900912500350082d07407562640d49031007007040202e204040101d01e00c80070401007040220300402c00756600000c19400d640d41e46d44180c446000601081e088001e10481d180e007045011 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 999331825 1250 999330575 999330587
    0x90218030c0406060c02060a090e15010f030e1903021c2a0203120711130c030b030f03040302010309260d0501090b0f09060d06151a0f032703071101 65
    0x1000c002c9030300340441407910300f010700b41007540d21005c0d005080010f601c90010380902d00030700c0180004c2082d121a4503220750740c60019841d60105500003240d40e400d415403588a4020388180c208050041d220100c2c05842c100301c85002100c045041d07002c1c2c100d0710045140c0610209000f040c103a200c0b06180380c0500005a600e03404005440b000c01892400d5401680700052200307401d2065084c950703a104002c2c2082c4100100c9003005030b91120341d90f070000c104040290030004010845480c18442e4091000401da140c5209400c03140441e80280000c00c09036100c1d401c00410380380100700b8005a5420429a048410090718020050600000d901c0507404101e02c511401002d040c80200000d19a21001405020900200920404d10040810083d9443e202da00540031382c0300a00b080f1102d05e048000c07516030303018480e100703507c1040411210025124401c4846c640c2d501491a4919a224443c0031303090000c1d0781c50306030b680801e243c01c900c2104041000f400c519000d482c2c25001d044144000401e2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 999333075 1250 999331825 999331843
    0x3012901090812030c04050d06060302190e0a2f03040201230d200a0806030c04110a0f0c02090109090c050a060f2a23120414030709021803 61
    0x1000380680e4104000080814205000c4203d038202e182c2c3c98aa0b0615002c071405550001c0380c0c07160444041340f040109070b92254045078403e5a000078401d40b000e541c410504080c1c4940c07070002851400144c0400301a5216180d48080c20303810789041c8080c10000e500d1100301c0980c403000e04030000140029903030030946c40000749007501079080e84a8075203680013041e8054081c485e800c094450600107019240310610034140c02da1200e000d80c07184074014000f0000d00b0280d80311406401a15030412903030030030740600c50700341c400700407080c3c5441c040d807070115000803580e07a05004004c1200114001a5a00b0038034600801107240013048440a9051001e411140d503844248140510542004880d81140c00b40ea0304000074200309500c1c2c804145541c0d10610000700440e10300a101410000300003107003a5129008002440c0002c01c00020011160b450700b12681501074000c05000400403288a8480c0611069010302039543c615515401c81044c1d8105208080e14071030f8114450340340d0b080810625003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 999334325 1250 999333075 999333077
    0x6140103050c0712091716030f0201020f01020a0203180906030601060c141c170f0601050d0204080111040e0c0906300c030106030e03120a05090a170706141b1803012901 74
    0x39152003a003a480362441f05100040401031002510001d681c0248040c0301004c110400966484440700c4000792680d0281244864801c1a010109440d06020403268403c010150040c0303040d908122081c2e900c080c100000b10f84020031000c00c51a844014452615441840300c460070404202d0000a04900710034a1704940390b04000c4200100a180d401c6002d0b0480360038203005555200a40c10b12001c0c3c07080d900047c60560070042e0100e91004803600a0080720603c900c50001500c5810b6181c0c1e0b541304a00516601c4081403240c00d0440348080020024807540950f15048502c0c80480641816421106451031f21404401000200e0301400f4a81621034207030f01951510b10050060814020040c0041403441e80d10000583c681d5000c1201d0360b26036030000da038004280c15490040d0241d0740129002c681c40750070a00700325160316814402e179003e500d032220080f1035000103200740c050b90780100680079900b100e08000781d4584d072001c0c8202c100001070111703180d943c00c0d040030707440c068507441d811194 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 999335575 1250 999334325 999334333
    0x913050a0605010513050f07050a02190506100602030f0405060a050c010906050412030c0203030f0a0b030327010806010e09040302101503110d08031605092d030106140103050c07120917 81
    0x203c02c0301d00003103041c1c1c86007041c14040d807204070300002203180c0f33001040d100a42480702e40c0340030b003407003800120b40c0e11800c14203541c00c41e020384909007280c0320301404440ca0b50304a001d0000344110301e8880050030420f581c5150a6041c040884000341c01c0d9410000252842940c5800307001c18004680c00307042e800490350805002c3d14504a0000b1f640b80b100521f82003501302554049076601c1e80c40c0d0802c0700c072403000804494450401220041d070a004286d041c1c400004a0300540261303500030702400d446000141c40705280c201a00050158005000b401103045003d5034411070000c02203845030080d681004c200000d02d0504501d002c80b0f9005590007082d100d0711080c0c21060024800c80d04070f80c1d0010407440b40340001e409403201907609004c1d000ca540d6110b04120b10301c200d0301c411100803d0701c0419030042e0441ea45021410306080741c0b181c0c05400003942d684409903510b9402600003e8001000d0145286040c1e15500e03000c2910410000d03c20016103403240c1041229408807910150400da03070060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 999336825 1250 999335575 999335581
    0x30905060f04090e010e0a05160602070e0109023103050c09040803130609060c17390706090506010608180d080c070501050406200403110913050a060501051305 70
    0x1010702802180316005405071592074141d00e4880a401412845c20700d00102d4441e0441840c0c02070312031501001090f00701c0103640b03001406910014a1070202d5483c2241c0c816164242055040654000d4010500c1c601683d1030303240003901040c80490350b40360503203108c54405040d480d201d428546446c0940c0d00c198000c2c428040864184001c0700e4020351100c07031076140c0b40302c540303031040c05001c03210005001c1d107281c484103640701ea4000c070300d881180320010300114159558546400d80840c0300220a1400c4014071814084105860913207101060495035803030402d0700300d640e00310a44100030f02c02c950745e4000720b00400626801c400580d41003180e040907103102280a080da941c1d98503286110302c0400081002042c113200c00300049484a5800000a00c81740c0740a041c464043d0003040c024802d80d4210410001d08440c0301020388056070760214405805101da01c003048002c1f080a05506070f54101003001c40009001000f607503d001c0d10620000c06da80d03140404100c0009800d601050a407400c2000f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 999338075 1250 999336825 999336847
    0x10b0a2d090e2509120803040c060201050f0f1005030304090e01050c0a0f0c060b1201060303120b1822061505060702060a0305100506070606050907050918091606050703090506 77
    0x300000f0003102410984815204480482c0c01c0415603000b5845c81030404a250113000d0418000c40c07107103025086000015980d03031801c0b030890750101d070010301400c00d00001c581145002c041c00740d009a01c4c80c694401d4170b0b4842c00000e0840c1e20603409141075681e140c02c412001003007030007101c0e41300301d0541d402810201c419601400c1c0d9466018900b00700142034009000b0044c09a006480d5080c2c064580c420800e0456219030003401140429000716018042d4800e81038010b001e41070304490003801000c0d6003001030301000d0718048090080000c0c8140c24800423200340700341c1880054a800750307d0100c1d0060101c480c54034800120b800c4540103050412054006d0b0320780e14110b80120f4031034600010f0a5860407400344021100e604101d620a4000075800b06110b456000182540c208440390141a11a40307400e654600c5481d040c142c00504c1c1490b042c1403590f0700352256600c221103400f032314500e4517101c0030703223031500c62a4008002142c40072501d08149503201607100050034003640c40074980b01c43c03500 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 999339325 1250 999338075 999338101
    0x1a01080c0307080c392409100c081b0915030712020a020c011206080c0607030203090303073002060a181e02090a020403030503010b0a2d090e 62
    0x2c81030034000c00c48003145a40e40c0003002c0b92240c0510070410601c0c40303985003c42c80c450101c19840316214580d0391452005460108080e182da21403174040101c12514040102c06500005002082034055004981040e5005018010071b101c0715540e820300c28075102e400700c00c0e402a40724030b41c0b090800620207401e01d030300c038086120520b40a02c0803480d1280e83d078075012075121100c00d000c003c9090000c5034044400f030700000c84004000d0240c035821401400d040081d0212071041c030038254940d010500c01640340c100030004041c0c4900030b00c150381c070b8088100003191842d401194212008955504280380820b2103041710130100c52b9034540d00e6485401208000d5683c43c000c1c00c41040680d07a010390b05c0303c00303496805e401009980721241e00410041c90345482845612002c00768001d80d49400060b0038515180700321002c2d80e07450703154607095900b80b60040400c0c0d0444241c3e0030078000260a10030740000d964102c0e038500c3c0420b00017000d511501142c020100c0c0c1c1d480e840050140641c0301480a2041509 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 999340575 1250 999339325 999339331
    0x90c031b140d06091a190203040f080307020a061505040605030a150b01050706060b0a1b0302120304111824031c031e0501080c09130f02060d020d1a01080c03 69
    0x1074200d00300c0380841c100000101004003008020080040c5409171030003554a005100f4409082072440b030681c207000a0090740b000700c3e00100410071a00701030000030f1016001e150440e80c540f04641c4079407900e82c6c5400840760b21001d03005650802c0c2e80100035070724182c024000a0642030300900420072059a035011071039481030402c603056413290401e401991040003595030890b0818814808a540c030400c2096507403042d4100340009019480f864280038503c450595510740c164001c080c03220001000701080e42025200f115010790400358a01d456945804a0b001506048002c4d8460b0405070310000c1510004000c40c44883d80d0f4140b030b02a180c5c0c000c900480c480c2c0a0720711894030300c0f10f002400ca006211002030746c800d9400d0790001c40380e4004d035540b149050358241011100007550180800054000c1182c185042441c000c45410002c3c01a002410b215413001d414181444050232a010982c0c204603802c2038662350b030b002050211645400c0c00c00c10540203007019a02c504102c518081148001 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 999341825 1250 999340575 999340579
    0x1030b06032404020a0809120a0804110103060504021909091b050c0f0a0f0506010503210702030f1b0114161b05090c0409150f1406090301090c031b14 66
    0x1c0c0003011281d01042c079140d214060002c0046554003403404001d42880803e44800c0503034821014a0580100380c2021a00000250340300d0070410380d140d5613a102e0420114000504250715000c00160343d48071030018045147d4500b040c900c442c02100401441c0c800c16230300201010b03061428014003850000078080c1e16101c98a0482e42e02c001c1c04040038602400c2c8800c01c078a40c03052548081c1488021000781001500c10402d80b90b0326603070740c400c2642d2041041b0b0b4045000552440a0444044400c0203040703051001d015034504a440e0002c0300c0c24150717040313400c466144c22189901510760b84509040b000e882c52060a5080581c5942404419080994000d007100b0302c5207246800c101f00c030042c0000401c00140b03100703554640214803613080d8000d403056049650a0a00500031243e010300d04009403042040300c02c000340c3c43e003001c41c45004141d80c6040e820002c2040205540d4900303000e02103141c1d00404040500a00c1c520708105503041c442c40603030100311a05010700401c882002864100041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 999343075 1250 999341825 999341851
    0x3070506091c0b130b0c070804260a03021006060507050703081e1801030f02030f0402060306190909050f06090601091112190501050a0e0c070503040509041a010501030b0603 76
    0x241900540b101c0c10500d03014000074003a0040001100c06460241c10741481017885d40c440d920f500d171400240d0302901c10000c02102050206110107401e58103050640408607000c8000345e030584100ba41040080740040d801a000088a0002d0b0f04140c02401c00802c1c907441c140d8900004e9460b100c0c4c40e011280001001c40e0f03c0083d00300f0b000c00b1010117006240c002400d41c035503160919401d41e41c554840140140c046410000c000443d015540700f0b80f4451022081d2024103503031590300f0000140d10080840391300623007400f195802803c1101c2060060400050f000078030a842d414010700d450078064884155601a0080168000c00490070904445203620085040780540001480d00d0092060703000e00b00c2804820030503600001610607416a560300c2c0104440d9072500240240101540104503140304140c0100d11003001c103c0060281d14010000e9905280e266000500c00082c00e40e41502d500300c034160040007822a004003207005040c00d00307040000120460118076580001001300c008030030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 999344325 1250 999343075 999343099
    0x6030605132f060a0306060917102406090839040b040207030203030a24031b410d0312090c06030212090a05030702120109050604080403110307050609 66
    0x900000c0c18507410000c203c02c2c1c07a0001028014010034084c490200051080223000a0707000e131201c0442500000000501400030762200006c02038401042c0c4141c2c22503865041a8082604000031170161420742c1d030f0301519500d0641402d2800440703009805245032078a01086c40e0b4000da14140c809050b0071484540d0b60300d904800140184440b11165400900003c0d402080503808001548030b56101030b4100554800c1c4a041501c0c2c5d400341c80b0051510402080c1840130074a64002341e410089521801b01a123500c4810f40b44500c01801303100380000b010403080191160403071541900400c071002042204840000001c1c60303203d007070036000d41400b10001d80c0341d4500c41607421a06070903400400e540051665414014000e5106c801d020030003d00d1100890300030300b40401d0745c40c0c141d50032000440c1014098dc00700441640c0d50800d821880d9650040b040006170f060090600c00c50180c1446920f4900d0f50404031403418607450028800e0f0040c440a001d42d5454900780d0714000010345040b1902c00c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 999345575 1250 999344325 999344393
    0xc090a0828080409020f042402030f0f040f270b010c02100c061b17161b0605010b0909091501091d0708010c111204050613030b0403030603060513 64
    0x84584e4101581c01d900003e00c000c0c1c1101060001c0003120b1050185d0119000c800c030f102d224555007074048200503082048a12400c4203410040c06e02c0061a5600500c0c241d80e412404141020540c849040c442d507550180c1d0200314090760307100d007c210082d428840300c141e100000b04641401d00c0c000744030328250040014400d2145003151100c90780140c08014010401000300480740e440c50310040000d00780c1c54004e410052000109000d96000a05c11b074000e100c120059920404600c440f4222840c5400c0d40e1004c03c1507409003074001e040d2107000f10790b100340346c2081c8510404010000720b00d07580b1004025030300400182d1654111810f005000448101001c1c94606004500c82070514500c60000c020900e81c2e019030201031075007050b850741c003219607514003007540f035108000002c1e0503810184002c0001e81052401403016811160740c4070041c0c3d4503035a5100c40c03000165403e50009640d10320a2041025510506410212310481003441c840e0507510102988928900c0c40c3c02481d4074800f01d540c3c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 999346825 1250 999345575 999345577
    0x80c0c21250c17060c0d02090a140a0b0a0e01030515030d11010614010503041118010902340602130b0c0d030f110a0302031e0c090a082808 61
    0x14601c9482040d021003800078511450810031441658401000d00d0000b9080c3e007616401c01c02c681c1e200000d42607550713070301c441c800c01c03500100200d491154082014110f1950344001c0000940444a4502250200b0710b007482154200c42c0c126201c0130408102d41009d20703800540d4540001000d10300480c055075204100143c0c80c91082e804e07501442102840c0041d41e400040000c88800d004008101e11980c400b410000750140028050100c0c10400114010400c08030325009582e201808400c9040c0d020b4446a0b20001c00340d214400c0d80d50f001c1103c131403400c0d464860444021070940c1003010992140300d20701031035011000040041c1d50018144590345840340b0700000818500c1105621900b485d5241505e507013104038840002407501012400c802c840b84110750010418201070b50802e0741c2c02e04241c00a520180081c00006141c654100000300b07501d10451081660300003564940c5044014014003407416005001560454042d45404d80c0c900000d802c0c2d056038114169801041c1800d00b007241e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 999348075 1250 999346825 999346837
    0x30406350a1e050705180303190f14181c02220b120d120903090902030a0f090c06030b010212090402030c0d15060f08100611070902120106080c0c21 65
    0x2e0350402040140e4150030001804409040903510410603080d0303410103849114403400000c01403188007111400501c503401c100c400c0d0000341001c2d022050f8001c4104219040300480d0340b503129594000a080e81418100c40280c0b0303445032003284c82404158005000c98044440c104420b881042510480018a41000c1d281b8031010b402e003004168401c05503501c540c00d80c038014000c20400395102201c0c00d660701c101180a50540c0d2104c10300c501f0501810301a60015201101d202d0b2288145e8003026181e00c1481c92592041050350910392502a0140581d100c05858a056400000242d000c440e50803007180c421201c2180e0069495885034444c1d80c403402480e040c0649189491504a4807818050900041d503050351a801e00c0c0c8824047c1c221080d140032200075180005202042008a0080e01c0700741c0c201e220300c81030705d143c1621030704000700300c1c1c004440d00240342071000010800b840d000845c040c0c01c01d400d06449490941c200f24966607480362641441d07488541316400161914090b0290340e4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 999349325 1250 999348075 999348131
    0x5100905090c1215011803080a03020904020c012a020c0901031106040b0a030f0f06080c0d020114070302160506090319030513090c0906030209030a031d03030406350a 73
    0x3d242001280f00a00071096400d06020032010f44c950b41440c418100d5003011241d210305014901021240c045001c2e4101d801e0041c2c001d41c00740040b01040c002800340c5c1642444400d1203c086251219144a046003c100701e10107640126582c2c05513516003c240328107507030304148002c003042610301c04909c16200b40c1e80110010640411103454031039154001c02c01c00e040900c0140001010302c03030108111203451180741c0c1198015040801181003411003014501c0c01410300d4503200d600d09601c50540d0303005002c00c50040e0003c04400d00c0a480014a030b2002c3c00c0291002410f180b50103020070303900c10300350606096041c001c995031010113124804031400d1400d0214402e00c550b65030300d4000054110010204003141100b034010561512034400c4d81c1a5001c000d005202e8a80c0301e0b202540d290b03440045e0903c01c40070320251140f098404100420060982e5a221400052840c0a040e4405080c0203220030070030320410552000c07100c1c504016003144224000103440d00c0e6409203400c8075540c10312110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 999350575 1250 999349325 999349357
    0x120b10090c050408011a0f01081e151c020102070e0408040f03060902040b19140414161116330302091018210b0103110a05100905090c 59
    0x141c8250b101010b00216424800240a52909007243c82d00104050118580040c090b40d01c2c4c1813158851100c2680007003082c03000103007811050383c00690310301048882a10f8196a0f130248030540c28044203252860101c6079114008010a80c0005d4440700544100c3d1100002400450300f4040420220360003030200701e2410050303076501c0c6040b1001e0608044164401c030b1400c041c4c026103040001d51030144004000d2100202d0b410203094001408070380c030500390171039130342e8040d030240c1d50306400c03414040c0c154400301e080b41211400d0002c04a56440900e41c3c216003000401800b5844801380e0903040d914180318080082c20300a0044166042c40c081c02d526440e002d840c02c509503501a4002c00440b5411354410240700c0d03440f4019551800c413502d1008014081c008100048284441583c040c00040e1085c00d802e00c0d059110044c5214080e0000c2d1407104440f16469840c0c544109508000c003025a00114480032104001c0c2440d55076101700b90041c0d1800300003801450950003114131a6041e04040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 999351825 1250 999350575 999350591
    0x150e0c12060a0f0e102103140f030f27191e0311060c040807030206210c0306040b090f06010c050f0a06050a1808071205160f05010c09120b1009 63
    0x100340c1040e4152041e11524042e00c101046d03590034914000794110346200c03021a590301c10384e401c0300e0110311503110740b029100a1090000c4841c0010055014500ca42d4030401c07581094003803100a0b810540e0380d44c211400c0c0f04000c80e081000841d407078143d680820000506000f103402c1c05400c0e103111086020702c2e0b0340500642020507400010000e0000c410504440701c5503100190803140e8410340c014a482c40d880f54004000614000006100341f0b08030300c0b0349a6107003107543d0710b0301c1c40708000f80c40c0000581d002108001541c10644107400619104a88411060400c0102e800380307010050421410007442c4000001071000801c140c9040f035441c0000ca0340d0450117410300e840100740c2030300d01c0386580b42030088a1047c01104003510281c103810500c41d42c600341160380d40a4178040465402000d018042c841208c2c6504c1c800481807a00f07000342c5a11804000034640b95085031a415030840034882a02414070001040340c64001da1540e000901d800303282c8844285e00c180018650244041505000031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 999353075 1250 999351825 999351839
    0x90106020a110f0a05060c010b150c010f050c070b061203160209090a0c0605180a0612050f0c19020a02030f160e010b030f07050913150e0c12060a0f 65
    0x4020480c082c0e024207295090032810840780020302140283d100c442a0003e00441c43d0100050031612800d9000042281d00c081c0030804840309a0b8141b401d115000c2404140c41d4400c0c098120300004040c020019494082080b0742c841c052540302034200c003c40c90000d00181c40d030002010040701008102d81c1c482544106001030740480101c1207010364682401708040781400104804407583c40110f000b0080d082c202c044440f608900400b03005800d01040b003840c02c1e280c1c25000805070050390b407054000c5240b0042c0605441000c0c2100d40103c9841042020480390801910700040580c4d00d107044a0341c00c404e08078030700700200c00017a43c140112603600108900c000344025545981c441b1415038143c1d65450821a95401d200704115003004000051955040b104480d500600c1ca00308281070811202c0400d42059001013444810faa881c000380590414006401c001002c03803006500d85858041d0030a0b0080c05940c58a042e11344800c80850082e0750b8041d20500542030451044031450b5881803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 999354325 1250 999353075 999353083
    0x60306020c010b010c08180d0b04030206250c0312141509010503150103060507050403080d050a111c02090a05030f010524180402121009140d090b160209010602 70
    0xc01c1c1071040d881d003403801c440395000702407840445030089182402c11070403191500e000350080840301d5004a0f002000340024080d1604507011310b000e1760041c10145031111001c1c0409000000301c0ca460602c04480300c252644c001c82600c41141d1515085d0b80300c031802c924200c05421414100c101d0610304030700300514010521400e60820200305c41c110040d990b0f0700141500d882c4446064584034a6500040c000300d8045e4012980100f403034902a4038040d030702d40300c000c47e40c2c100c07006a00c0480e4480003800342c414158060340d5804030101c05100c1c5032010340102520440030343c03000c00c00c0303250300412904425030340c107145000240740c054113461101c001c0e499041d0082ca011903c100c1519084130180c030b000746001c9c01070200c540c07016180c05840c0c004508800c542020091089038005604683c0d0482442c051280141751140960701140601345440c01403200d600b0103503071504951011054141c0705a2041c034150849054400c9145d440340c00c10701c02c8502e03070441d000107034100885000010701079500003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 999355575 1250 999354325 999354337
    0x1a130f0e0a0f020f010306050d0b0c0f030a050907350a060c0504090c231b030d14010e09060f04030210090308150d33060b0a140c0d0f0c0606030602 65
    0x90b160200c41c8004c000541c2161514001c00e82c01880c18850000020300c000031068100d0603240015051555007081c1002a900495103102c2c807a4407003040c0b1545040410869028180300c4000c0414001814654240b00c0c864010f28180d18182c1070301d4206400050281c00030315074101b402803010b000c5000003e00303558003d100341000340c0d240044200c5014407890185441540c1c000b204c24100d1151444034103d900010a031800b40c083c01060040e060b0300801c001c0103100340180380410303d10501001c890050005034000009103400720100030740e01c0c601041c0980d004514081c1c000f550703200d45c20124a4900c24403503252501d80b62540c3d1714145900303e6070352886040c240d40055100344051051040300c180100d0002c1020f14020543c0500040ba8822640701207401c01c8500881c094003068002a1220f0f40d11148040d03400040300c00029038411080d604008018510a1804400410413980c843c521081801040b805400e0540e80f24442d42d0345015554101100380019501c03070030050002d5101d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 999356825 1250 999355575 999355579
    0x160210020109050f24150409150c1106060913080a080f0915040210031e05060405061e010c0303090b090607020d0923060906030406020d1a130f0e0a0f02 67
    0x50b113144820701c8001495101c80f082502e03100c4208070743c15000c203101c16805030a824898070744504420746c613200c51092209145c00b83d41c40a00740201c00d05010b045501c2411980200104100500a080c0740080c403590490b0040e2210016580c4031f082d03124503042c10040041018800141c9600c409511246040c051840c4042e1a54035131606c400c031617900e01100c44004c40e01c0c0d0200000a0262801d600d0002c00c40c0794a02300401e80e000d620600c602c03210110449210015518410300000d41002e1140d00d41c0440e0685100e105440c551000040d08008414420b04001160f03050300308051282d040300010310b50055601101703050120820f6101c850490b6000010307c22422004a900c1c4100c2401c01200d00d044d02c2d0003d00f1a03002c2104090301c018152413604503404011001d40c68861800031071145008000050710b8003d0550028151008860400c0c5c08415031900c400c0c2d190740e4982c0d480f601c103030101030002e003e02c030f4101e41102920f0807010038442d0f4000d5018040a0280050124000340c0c0f007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 999358075 1250 999356825 999356833
    0x6040b1c050606070308070f0207150207140913060203040204090b0a051602210f12160e04060302090105010c0516080a020a0911090d050703080f0c1009050d0516021002010905 77
    0x40b1414040940503550001c0c0000d8000e80109800a000b0000020a00494419611081e03107a04a01e1005036084166000683c000c680411641c1c900340c040502412040f58405918100030584034101290b40340b0141c01036600102042c11507a40c1d910a0800ea603001504000515010440d0b600410707007141d241e07008024008040054610201d50b807135550200510b1851502c000c480d101e00d803600021043c91207000200007000c8515424000284a01c18411051780d5400c0c04020051414125143c814003650424900b800107a880307140310f47c1034841c00e18000360b007808103060140c5441190358403038801400314400840e10f04c801190382c840c581d000f501e520062640c1d0f02e044404980702d0204c0020031000a025220b990700e40083d070701e5007031130049044a1a454480d1914001c0c1d078408214695076100010350388031034800501c40310f0035038400450300300140c01464558685030041c0d541c9800800070b0004220300c05007882244081f50715005001c02e200700c000c07100040d000b003110a80035500c51007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 999359325 1250 999358075 999358081
    0x31e030406050906062b02041d070605040e0c090f121c1b11130507050a17040c030209181c090e07170c09040515150f040b0906040b1c05 60
    0x20002030b0050080c0f45c05050b0036012226480002c15803403410040c010420a212030002c0580e455000e4910341100c8080c07444003a62442040134907015080d4001800d00400384420003003207580070f160ba903005c0703040300866550b0300600c0c001812500ca10001d80d9805450701000f01e1502600180400101e0718090314104015040030003a54150340c240b900b03031583c4003030365130603000a5441c50025030000c6028082c03050306140b5985941c00c0c1d6100300c1c0c440e4002240455080d103c194080c0000d1461803100c50015140d0030513072142c1024820500003c1e0181c80c13000301181c0c01c01c0300b00b124041c2c02080c5030190740c80b011a580c00307131048400781c02114002500e0b5020120702c8140c4000340754041c0000d81c8a0090280a0448030010400024018140110244805112a00d45009444c0f240701d0400c0c481040704d06c1c0604010345007050350410200d1200a00c592601c2a0b1000c0031202904e10210005403105c0034040091030324411a00140d403032004c080340d15020029074202160b02d16540c3d410a00441d5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 999360575 1250 999359325 999359341
    0x203030c062d06120a080403120e0402070b270f061005090105011209050106051c030f092904050a0e04120203070f03030c03060503070f06110105060109030311031e03040605 76
    0x2c2c00c10880c1840c0c802c40c1c507020554074036290000b01201c00c50345003900c40341c0d0503603110100ba90f0842d0744250f0380408040304680c030b040d511400c0a060710804940840c00e1211a450b003081c81140203203030300740d102c891001c41015083c4450b41c001103424100100c903074100d45201000d448503007e840c59107180703410200115851907e1003034503051300e40680d6900c0700c40f44060b41d044050500038009980d155610507010406031a1120036051131090038140d03048840451030004d12407108544900700304461050188240c02c01e40c010b080003034074940e6000310440603815904030a44141e5024590003583e107100000d43c4440006007920030b50150070022a103003a02a4266100c1c480c0c0c00000308802440c4071110300190082d4080410781d44030340b900080550702d170004a440e140007038012001034404800c00708206031340501c601000d814480002c0c041c1c2e040190020b050100640001014002c0c84403040344000703003c0041d240a051f00d40f8031440d90030600301d43e808036984242c409a5102e410540040e00348 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 999361825 1250 999360575 999360631
    0x10501080c010522150305010e09070e01060e06120f0412030b01050d0e1606030506043902100504210309030e0909030c013e040614070203030c06 64
    0x82041c1c40d158504102001104213451460700c2e8404040d640742c0c000b082e100c140312845c003003201e185c0c3c50001b5154140040c0c0d01c02542c00070000d810766801007009202d041e5681c0e05050456506060421030ba540c1c110018101e40500c240800e0315900b2542000603003000b05071124016030082c0c000903501015003404805840e00801c420740800c07810890141842d034650302c00408950100b013a20036640c000d200003c0c0b0310303405906c080c00003070f01c410600003030b40b40500c20120040c4505450b00825480f44400403c4151401054000c51034805281c0d44000c1c000d00c040050003e000b04100050328085c68072036203000c00d000c3d20f1341d0b1a9904001546c0c02501910819030780c40d030103032107003120014103204120781350f203006044c9207140c0414450b03402008824001c0d4a42d85030420b030170b540c0d030070355070080514002821490f0103c010091007021645402520407a016074106140035006501c2644203c81c06100d030304402074040c44001aa000c2da0000400c8050007111040944801000d0201d01c055003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 999363075 1250 999361825 999361843
    0x20702121b031c120609050405011a0415150504030b0c041e061b081603110c010c020117060102011e02070b0c13091a0607080301080606030d1d012c0301050108 70
    0x100480805883c0c22140907142003288015615004200541c803003944a0a0354400d0303404071602da4442d40d1842e5071222108090702e2120042d81d081004101500e000071003814540308040d00c44045000003504248900304503405550044240140c5040040840e006a806840388104440b03041003017505680c024540d0a04803110f5644001407204240b03500402c001403500100c076a41010001803107510110b40e01d82420600075107031007031303900a1216110305002805440c1810011284000c90040c0c1c1c11a88096044141d0a5144459903c400c010b0307006000a450029030020351480c034040c0d0103490780080444601c20661518070323494408280100e400f82c9009055035100c407000030300443d00e80d0b83c4031007100c0b05103000c02c840340d40d5a800420480e5000300d4041d500b01c5400401841501c4042086507001300d0140c0040200003034401d0014403240d90007565401360303d9010001e81040c0c1c454101c10381405011241d00f540c103c1c405621100704800516824002d50034000001400c4201142c03041d1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 999364325 1250 999363075 999363103
    0x2710021c08010f03020603070c0b0c0a1206030201021f0f09080c15090613060605090403050903150c1218010e1c080f1503100908030403141602040c03020702121b03 72
    0x50030703804c0d542007005c1600300500440c10084002030104c085014800c40e103025011049406544500880000b0301101c007400200754264100030003000141da00041c0f00c900c00441000c54034400c800026104042c000780200c0c10b8243d41401e0030741c001d00007030f440200412443c40044a8402d40c0c242d170b5903002c809040301c141782550005800201810041407182e52518410f000c0001c500f91504002406480e00361400d80001d500441c0b040b199007820440c9600e49600a01c1d851154505078a809840b441003848248013407a044020401c15078031070741c45541c44607001009200040da00c0c41d41964034841000784054160658405440840c001d55642d80501c04205400801c1d55600d40b0b100464541424895014070a0303111001c0891818410145507a2103840b03556038034140b90600030034640c1c81c003940c0706400800b0401828602c04819510302c100b079056401140d0508010010750007800303400c6010b5004103104244010500c804585c11078011981d0314a640c0e000c4c200401c0c15518504060144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 999365575 1250 999364325 999364349
    0x1a030601031502070f0c030501200d0b011b0b0a05070906080a0207030c12030501141509010e0609040f0209040c0e0102030301030b0c070807110f12032710021c0801 72
    0x40702040c10b490711584200026030b805890701900396244600140c6a59082d50003040c241001d00030000b0a00941c1c000401034003e180e41c90035580d1512540c2e21406615011541c2c2d00c600ea000b069001d10030003a1840c0b00c0b0f102184020410b4246840094021128188410700d480700203044203019031003201c156440e6a0b41c0440740d5072510106402540442016814464000d00000c002000c20070b8007a4001c07101d540100703095241041c2020090a0425a148103501c144800e0185c164100141c0d20b5061007443c09400c0b802d00d120225615102d41900d00340c12a0810100c403801c880d0b15001807203000d4041e2020000440a400f04a5008940b440c004d07005030006c0004002040b508403c031034000441c00e01c2541b0304042c0795a8014150301400301225215958250419941b6000c40c803220a01410340c2c0721500e0089801c1a01e80324842c0e80c10742d0325140078000b0481000c05401000f000780d100301611151030a08a0f4401070341d00c6003400c060200360360160701402841e901c10b803c558101c0f08605101 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 999366825 1250 999365575 999365579
    0x909180215040b0301060c110a05090a050a110d0c08130b130302070806070c060c020d02100c0203040305190b011208070f0302010e2506180e041403030a0204091a030601 74
    0x20518050390901d9840000340700c0881c2810800005600808031521224205a810726140d20345e100314650407403180ca0700b60000c010f5038452040056000802c50300001d15540c501e000311000300040d08090821520100d550749001f9116400001e641c143d6894130307403090ba150700482d0b041d803d01c0700000307150114240125007c100302c02520380c00c1ea44680103171060340fa181c40b116403401034119104000541640001814800c040c89003c8001009101400d01540e007504007075501c0000074200d54120342c4e14650307200514400e00649002e5a07200d4150360055460708a0320000ca10072180c151801d440e008000142c100e50030f0b01841c00e05900503d00d8ac01d18213141c0365030038601400348060703042d5500c4810800198500784884909050411214110486103120948213a43d050308a1414000c6c43d40c4d8003e18919a650000b0480d03810002c10308155603985041406c600314004040380b98032020003072158071443c035000b030720648205980030407042c0307070a540e450f0b140340c850300c41190140c0ac49801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 999368075 1250 999366825 999366829
    0x114130b0607062d06050a0501032003101206021210080a1b05062106010f050322020a09051605070b06010c08090303130512060f0f060d080c0d09091802 67
    0x2500d02d4042180004c200004261141601c81540982004400d40d44035424020344c40d000c408a030181c50700386400c120801000b08900c6203581c0e4601e07282509040440020080ca1100c1a03000c00746c0071071103942900e84000e1030200c0c0079400c1004112079a01c00c0c0400034404512a40b04101103a03403074002820f0704000c9d52502000340c190f880c0704201d900c0b41c6100204450b1500b8008149501c201050342540c0c0c030f0401001c17515403038098901d234100724000142c01d6100c0d52141c140c0360804801d9107410b20b00321041c070040c9500c04d04800004e4200d80c0d840c41c0051f0031300599108a00c2070003055454401510440412134140c410510010070a045207004528654070807180d45620b01d1240740c600d482c151004000a296800095032071203012103030038090015040007403200d140750702d000340241010304007038401c41c4007040c0040220055501c070500060b038607582c800c0500e806d40d4000c88e843da0398050040201e0746500300c001c01072000c80c20105000840001c24461003240711040150f5500d079070b009a013 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 999369325 1250 999368075 999368081
    0x812040b070c0f0612060e0714161208040c140108010e09070b0c101103040804121505070309022404090f14090d18050307030204020306030a05060114130b060706 71
    0x1400d440c202d0b500503000ca081514030208002501154803201010f414508003001070b00d42caa0407603814081410203004403560401960400e020007241d030b035a12401e1004105001c88889180606003018075503140c0320140e0420442d60090f401f90303c0203c52151a60084180c9581d011700c26070014244100400c40903140399410b94005905030141da401c0355481c4040e440d550401000200103030080381403401c0020862080783d000507040300200f403c41c509a118039000c4e0203948240d0007114a0000040304103d000030a000d40701d621004200704c2401d221a00800904503100708a02800300131202811085500d822080d40b420511066403403d403d00300d041000d1300384180d8030150645c990700c1804048880d075603181e22811081c1d0042c405000c094000410740340a000030b034600c07280340070014403403030318085144c2c410b03260161000760f50303515502c1c0400c2c500380c1b116101a11901071040081080c42031502e00901c83d0b0003c0b1281844030390081540000ca840c0007009644c000030401140700000c0c6036270 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 999370575 1250 999369325 999369337
    0x2030309040f0b030a08270f060724020403061d1e030408030c03250b0103020f01050903011a10030b0a0311060403050616030f0c080f100506040b130812040b 69
    0xb40d40400c04642201c0402c0c82c0217540381e4111034040c0040303000c001100b000c0e510680e0301c01d410141c1450055085c00030480b040300e0b5100b80e9015000c00070791001805041c2d100144c03400c0540680044c00e001c403103800d000a40050008580c19030801c00040c0c00802c0c88458681c450170044054020921800b005002403801000c20032040c0c007052000080c801014005400052504d030040e40c1d82c0c0042108601c58251007d01c079841200e00040c503e0f010070b003d049980d041d6981600c50507100b005281c0165454003900f5829607066007004400b80c0001407000391404401020b0350b054192010380c5400364189c0301d04003480c3c0c0e0040600c010410206044403a0380c4403952000d082c661030a03449444480c1441c00c00c43e0405020034400245101140e89803261014540c0440c008102d0808076110007040c091780504a80d0006170302c0e0020030350640d41e0b015504010900101031342e0341c441e941d51402a2a8100c0d0f001c000301c0c041d880700005501d92020940c1ca40c150200030300e0382e1234141442c1e87e010f0a90018 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 999371825 1250 999370575 999370601
    0x6050424140a020f0c090106120c0507150b10261503010e150c0f0a0f020f0f10060f080a1b23131104121a010b0c0607030501030203030904 61
    0x1d004518101000c1e40001c0c0002c04855000e03211480f6410400740c504211455180e0190b205100100801c50740051130640c4256900700204e01c01e031001500b1a400e005000c801b40130910700d9041c209480c071275a402280b0001c4203951300050003542a400b41e4400361660001502c07030701c5440c2c00700c0302580011001035000c296000703a00910301880010034212541c0251000655110b64030a103c83c008141c080c90380403401d240a14035141d40c008800c6803500440c45024240015a00700300c1c4842c0c020b12840c0a43c02d0004119042c00b14001c0c039003503842e050a4900c1803400c0c5071540102c0c06014500070007042d00d51403401400400342941e01c1890055000100600d0501d46c00e4012035030200076141d451454a09808040c11020140104050600c072180d0300c148031850542501e01c2c601c420000c3c0c50881d84107040414441205040210103560040c0da2400100b000708004543c111680002d42242c03078661045841c166507094007602113803001c1c000a54940e20900400d41c1c00c1c9003640040814441c030f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 999373075 1250 999371825 999371837
    0x402070812040f15050c0901110f01092303190f1b05030a080f16050c010618090303060501090b0d1d010c020105040203060a18171204050a020a06050424 67
    0x2a07070761142020380a41e001c4500c5002e810000c001d026880718048400c4403040c104120a0800d41e01589062084000043c10700883c90b20361020801c00780a0000d04401d204024071030150b003882e1441c803141d00e11040200b118003403002c0d00c0341c0d41c2c030020030303282c00b4102d080c01b008601e00607680c2a184880c040c0841c0b010010010380810440002a401c04040340c8124021612584080ca01410505004144584100b03468003007107960381618908034007810960810580d15100204107901403c251380200846c5c80158514881c184250760003807203d28040d0740c041000036243c0004550740e5455105101c0704800a01010415614a9002d80c1040c9100740400f200000303445081801d407260050380e5009070755210104815410103100707030303584400000f10810800e140c8807940d10382840e60b6030014250003002c0155015000c140000c850220580c0c03000c0715201c0c035003441c149950348078a0204a010300089507001034940e000305c0584099442c0e03822140c3c68a44086012038900080403103000c10404 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 999374325 1250 999373075 999373087
    0x90c0d02040b1308010f090f03030902030c18060a080f033a050403111f090c0e0408030115020313060c06060b1303020909031905070335061e04020708 66
    0x400c40700240780e0301c0c640a68001c4124507000204d400c503011360a40c0301440c3d0401c0071404c0001c07480c0c54411405070b4141400181c0048a002082c070b444420380c846170b007280403603281c00d00c41d04804100501c00d0b40121001c41c8126224100c00d0740300c015880080105500070700440b050401041c49080003e1040e5200510920703030860000382482682c040b0008a035134400901050603030107480c02d03203144a00c0d4000c1902c036080842200a40101c2d182c4000b6140d91415040104140042400d0007071100c01107a981500341428103001a80c020b108541c82c11a6070582e03861a0303800401542c6c0f0758100f2a1a4001081c0381c03071025a62800031600c21985141d480300d005c110040f0050140c54505030003107002c0a981c1c214810320440410141a59066034020700c03504030140703035401050380144224500651282420320741078400c5100406c0d22820005000405108500d1081c8900e042240207140348404c0c0e1281010f12110444800c4491841581c511511b44c0c541840e8009110440c07203051814500700b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 999375575 1250 999374325 999374339
    0xf1e0406030309090b01090522020d0e0321010302030706080c07060c180b0414040e0708030712351008011b0e0105031009050a110d050907060e090c0d0204 68
    0x40e480d07030400c0b03001c40d402440600c180303a00e070320443c81c02940a0030190440380c24a0005509030340440c00e240401c0311120180c8506001c560180e803080e40c8505814440742120035140307a12074104c49014601c080070001c1c40c2c21180845110b140c1241c6d00038028140060a203041210090002071804440c2d45007045650005180e51155000014055555a0005c2d80c030030104181c1c2c40c00c1d070f4402200c02c14280300070b0001c0044949240712145048400054103614103014070705202069101c107003140408150501813001c105a03040354140b80f541c070181d50300030090310000c0c1000c1c0103c01804026000200180c1c4000007021188c1004481030720090b05641d4807559800d44152032138109400d41c2000d8040261034104080c0344140da02400c2c40c604602d0105140400c240c02c80c4100c03080f00d901c0700040740000080e50f00050381c0180c0c20f01010754640d0f447d91090040e01090700ea0004500c03650030009141440341d100d0841511000b421a00107480d600e1001300c007a007048101c00009a800c002c001005 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 999376825 1250 999375575 999375581
    0x1150e0402280207080f071202031501090902040501090501080a0b07030204080708030c1e0607050901122301050f010c1115120a0c0810210b09010e060a09020f1e04 72
    0x103503982c11a1440010101500a0601c1c031540d00c10410303680140e42d02c0403441008100207042e00c01086030301c9000c1d419400000c1c60174524408484090044000108000320103400024129009031000d000590307a40c00c2d00411503509104007001c0d60840483c400028500c80340168100000e0300d0094281600c468006003444621b900900742a40009106d84070044140b08000e400200c010f0000c0b5041c40a0310020b0703d80c10000c0a8004001c0009106026a80501c010702824501c45c8400c010094000504481d569a11482d01c1c0d0103091784400003c080ca08100c011030041010ba40b2070740e440d191a51030800281c41303014055441040d0f0741c044820387ca050405450b048009194100182c01d0800ea020110390050303403010200702480c030812800c032010600310f5048407502c0d68001007601c4004809a03007018044801842982c504003480303c80f0905401ca28910413042040d00d03481d13101e40390110102c44040b10002e4000300300c80385c105810714096071164a11351840c0d4000c020042080300003811 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 999378075 1250 999376825 999376867
    0x170402010e04060807030302010f0c0206061005130b070201030b030f030d0207020d060219170402010507320106060e0a2d03050a0b0f060d170a0509060c2401150e0402 73
    0x3d40d17002030410402d2581c240119100750150000401400a40c50030003500d40070000c0009001c2c21400f140f01003201e106004513560033310080c0f0041110358841c80034000933407000100786d0000f03082000c01c006524020400655541e1104000c52605003c0c01d1000080c2d04503d909aa0003e46a410301020800900003000070fa4070308001c2c035001102440e8090241d90001510b2508140035204000041c0d030008111444640c100501741002a2000d074040d01c5034030b040300070b03010414840410b014800415046001034440c0307038458503055150a800e020000340544a450b6154001215505103149540852031450580703c1c00c5004c9580ca0707495907440c140810904580d0101114104240004a11000e40d0402411182da401d035070401d4803520007503450014020310004002803000210350080c0c0c111a880c000290015450f6148080f03410748030310051520342005881c02010858110001075101d050324003814081403840f08050302240d0103205545095005a0f08009840382040d0400c84454 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 999379325 1250 999378075 999378089
    0x30b0a0e0a05010306050c042106090f03090302010201060902130b0c070b03240f09181e06040b070e010c0f030c020a08010510150c021c08280906170402010e0406 71
    0x2c03294514903100c4111440200b44044c108014002440b8030844100d000c50034a0b003401d00c1d01401034613414100000d09070580f000f0f100202d9403010504064005c2ca510007280d000760001c02041c1d941e42c41a00c203a200d0300b0488140004504406e110707555840340a0100d80751104102c541494a4420701d10250380103132000592440070302a641000951001c1c2a817856038141d030328000c000700e03050201d54414000340003031500380c07c81080343d003480a080040c039100c0ca0611042c11283b02d0100c1c095616080165001d4680c581d60b14001042780c0d01409a0701c103283e00c1a900e100200e081c5031030714481108010070840400c07076047c2c4142c025a444100100c041d0441100001d07041c01d1410611000f55803507400702c0c0c400301c0c40141540d20036400000349000c107038054419003081e00303820000f031110f2072400303400621800e000300d16900321028601204100c0d035000540e0521650240030b040e1502d050740d1085c000096a041d40c2100706400041d4580e80003441810301c40044000280040c00303484081d04018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 999380575 1250 999379325 999379331
    0xc030c2e0914010201060b03012102090a0b18060a03120504150e03060601020c01120902150309161707031509020a090f0b0d0c0b0f0c0307061a060c060601030b0a0e0a 73
    0x1c00b030103521410b401101c032824002002600d180c0686280d050105200741d9034000191040c43d00d000650b1107906d000c15a008100240030b203080802c500041001c448601c1c00380c0340034901c51207404000c1c0c158a010f0040107200b034000f1465a079480c601a40001c2e054010000103000000e41001c5000c0c15401c0c22100380c454040920700e24050510f0910001c2c45541154000c0f500e03400180d0b000200c0c20700d4064034404c00708091803180040368007101c2e45a03010000d03410001c100200c0302d201082c04042c1e00d0101d00201d201c10382e1802102d8803a901c0382001100d50304210070820000d0b102c500c40340e20400d11005e02040e04001500020307401e40240c0c0c440d1940d207485611040500055109581d68140304541d00000000389072120b040440081c0680d0301c41410000b10144200150000d440401104108483d80e61040f0726140c40030b003d204071100c00001414807411080e15290040d07a00385c412000041801ea071f140c5004401501c14141c0040e040481e003c40812241400d900c2e01e40300d00c100c0300000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 999381825 1250 999380575 999380579
    0x224070807022e020f0301030602030901150308030606181f0f03020c0c040f09020d0501140c090d1209050a08010e0607020c0607034b020c030c2e09 65
    0x40c0c0a0300005081000319086040102c10301900c0079481c0035140342e0301d00080f0b1505009070300c8100a00c1042410304055030040f00010400410360011481521440c0091052034401e41020050810600005000d4002400014620f00f400380140644148000c0100d0013054a04042000d8146041c903c0544036021400070706529042901003101c1442d41c0380031881c000c0d0f02da00c816180e050a610540c441c42d05d0f12429000030210350000c00529800a100d40070040d00362071310300d0003801841400c004c1d124417400010340d81d6009d0810358006030006081000c0c4049140c4c1c5121480080e902c08000b1722031001804600b0781c4030700030804003030010000002019540304401600e004002003c840031903000114559280d214001940c0c00680c2c54142509803619815401006400030700c50b034011940f403802845141c041203030031010340d01c4414208000150780c041080780c42d101525007054140c0d02940c8a02e1140c245860701c0500001900c490304215032080001440d0101c0303c85812002271003100c42 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 999383075 1250 999381825 999381827
    0x6050702030c0109440d030f0c05030109020310030b0702030405030f0d020a1212020d0c080609010509130602070501061415130e040218090d030e0303090c0f01022407 73
    0x380060020242042e458807460907224482240c1a007445444d62006803a148040705041c040925001034017107207290f0340c250308054040c0d64140d42c48046c070010303041c8040c0c0500f480903131141c50a41c0655941c0d40f442c603070811800302c0180d40702801100d0440c4940d04000003142c00d12004c41e0294031964043c42c3e42d113280104040c501101c241c251903980c4c21100d203040c0c96540008290f218190b1100f00071008000100c002d90703e82900c0000c00201c01d00000e44946413402c0d5610441010740e132512141640d407514014016499002d024840d00303c0a0b44001c0390110009010401f0702e544551005480c0441c6903486a094414640c002e0701d190b8582c202000c01840d1601913140c0f0407045070701c420f0500b120b524203018030b0345040c840d040700402c500b004038041d511021a42854030a01c021001c40030b060a43da21a540d411000301e80300000e00c1c12110041c0800c000c0216030040003034000820741c0d40103940c20051000c2c400b45006041d8801c420085400803403103040300c4031640c141d41e5880e241d4600010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 999384325 1250 999383075 999383083
    0x6040c0c052509110901080402031203100e0a0e0a080903120d0b01080c0f03010302010c110618040f0603020f21060403020606041406031c050d0213030507080d050406030b040906060605070203 84
    0x4210158106503a40204a480c138090340c003e4942481d0030030b0760791680c0c00032909052544180d80c2c41d11800008105c0c00802c40ca000004860741590803c02c43c2c0d1340c000c0b41c9002c4600c16501208a60004c1559070045079069000e064502002003c2d60101f42c105528444943c0c018030703c1c0100304c0e880301c010000300d41c2c0000300d60b80d0252040003468075040c1907074a507442c0f40c4170501000b410b10844484400a0008000c81111480809040d090f594903a00380e410660203405212580315600341380695050808500419003100e90107402c0558650109082201c0400b074446688680301c030f00344a054002030100300060156009801911050034100c082c4000d81c1d14290b540302e07007012100f0501c0350f180c500081800c0c55803003200c146001041580340c100c5040c460845403440c06400030400c03000642e0b1b0081414200c0e40b298041355212036175012041d417603a001c0c0480b000440c8092008010060182d000140e0440c2c00403c00910418695540b40440328160409400a480400d20a007141030401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 999385575 1250 999384325 999384329
    0x15020f0f010213030f0f06051f060e132412060606031509020307020c0402040815090706081b070c090204060305060a0509070c0312110a14030f06040c0c0525 69
    0x9000303600e40403406001c1c40003800e051000030080045083c21038140300d60110518003155007c4810321071400c03d610308240c90040c0d07042d0f4005402d000580065000d0060441003415072000d002d0039501a04203165400800300c0707816851024940600c2e41406400900d2010090a08a0490344a0034200d040c00c100301c82007504800145445d0500042c154032a5030100700840e0b941c1000175a40e6074900c90700302c0c204000c441d00142c10034004500450110b030049040c4c070b40b407007c00106c2007071a592114225540d410600c107041c08940e040740401c203808450320301015203d0600645604c0e0098540e41c04c8107440f0540e010010643d40400c082c40302c15458012709420480465600c5503030350a01000590f10344001d030421080c080c4404950301054080c50303031101c050a014504101040c1d204484980c00d070b0108001000084052a400e9500705244c0140c80c05000c0140e076500700f81e51480280001005499a50750074044500881c00000d002001611054220b40705104080310103611070040c08041c503 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 999386825 1250 999385575 999385603
    0x3031205040c0306111e0c010c021506040504032007050909010902220917040e06010207080d0f141909080a0f08070602090d142a040906020415020f 65
    0x81c40041800800320900740c940006000404031a9a080b004152082541691150801d4011000360031600c50190030041f00810080c0481a03140701c04030b13150b0b00c1e072082140311034081101044450919a2140c1d40c4144a41440c00c503048100d2280d03807001803207101007000340d0b016000c24005070400000d07586c0c02c0b00d030500c000d1000381203070383c0080c044400c1402e1100e0050402c2c0d4030250107029130781011340300681001c0404002c3d4160044542644d200780100c040a9510102042495100060603c200c5668001510740c0742241c10307044600c148012084400c101c1760700f64030200750001e00e0081c0744540d100a1580c00203106400054043d144c50751200443c0d404c100040c40120786c1d03007407040e651594400101c0360358018619011000740109000b0a8004000c0d82d003030310070400d880039481810304402c021210807600b5403660204405040044040e21030ba0480051005d007420341100e00101d00c540c201504154031800400c3d403440100f01c541005034850703003160105440503c40070f07281e42c000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 999388075 1250 999386825 999386831
    0xe011409030711011e020703060507051e0705010f0204080c090a0203012702040e070210110702010f0336171806070302010b1801090e0625020f060c0301030312 70
    0x1041080e551240540800544410b110201840c220ba200c0d20820b800d020034091107054111072440000c1d9034407245e0008498403031410020558190041d01620740b08150307040040400d490052420005030407050301100e07a50740b200407402a8095500141c000342080400504503c40300c5001c000e442c52000d80702d030001520400c014419040e4014611440c06402c81083c100060041c0305e5900910850344002c085900310390130300c2071644e800300d509a0701025421040c0103030550018010f10510900000a012481e42032482c0921341c06070700281c00800c0e41e4040c050503038100c45010401000040640c5005070301084042c4101f1a002c085101e004966a071641d0421240071000c1c0b800300341342c3c006248a22004031307007002018400d401c0596031841c0a011000c80301104201c480c4110820b0003030204460500c041c0341309224000410b20703c02c403114a002034010302885440e4081104000a803411070180220016030030302c08108481c050f52800004942e01d6141d4100200041d00201c554480582 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 999389325 1250 999388075 999388081
    0x210309050a090209210c10050c01050a0b030609030a0f0f0c020a030302010b100306050306040b13141b01030b0307091805010e03030a0605030607020607030507111605090a11070f020f030f010e0114 86
    0x40d0000e400c0748455007d0304c4007404180040401e550038003c80f05000c08540c2480308100004055402c1803035005410f8044502c192544805a5124003600301800d0010f20b07214241e1840303500c2180d4200300c4284908280480302c01355004100c40c40c019400560150391220201c440c14200900b004d50b0002052404005650405000036290407018001600c10100080800c455503003039407020000580c000350407218403a0402440d52101c50818007100790f2503101d59840c505500038001c0550180707009024200240c200660003000301310060b09408850140c00c49800015805d10a0031043c103000402940c036890034281c49001c2d9880d0340c001034081d800039028040855000290075410000d107040200300c9944501c003c850703000c1c0b00c0c82070b04900d00c07541d01c007040c045990010007001e84209581901c1c1942d0350645000503540d82480c0000c04203800c0091a0100e0402115000200d100501924094041d030340000d161201d600d0070340e02d5903599440c000c903010f80300f40f05900d85d42d481c545070104c00349 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 999390575 1250 999389325 999389389
    0xf0a022d10050604020f130602060606070b07031a030a08090a09180f021305190e0303100b1e0f19020a0f061d0d0c0516210309050a090209 61
    0x180450280441d035036103440102e906aa01c0390141e8482c0917131090225100d40010000c03442c0000b040c4607100160040d4404110503052020032202c4171604400d07aa6042c1d00c881e4070440041c2400c9003012015070040700d8a41041e1b40a20090100741c1c025403032291909255410030900039603680c00040c1f000d1400d8040390781840382050b00404035400a01e0418492680e0000c035503442e240900301c03100380d860102000f6904500c0b8800120300015200b00b00b24030003003e5807069891205841154403402c00c2c1000b04460300c22540108a80150030046d0302e0300440070b130b9aa0403030340c0007800203035000d003008905011031070b129100c86100d1324a140300800301048031362207a0394104041100600420b40301c1084448100c0d200d440c0003401c5846c0002c07240762038070021008002ca691100304540340d008403841d060302c90305c00040240640d030b6465880e40e05c00f0100c655560214920940803428071400640004035070f0340d801e10480c02810130190241e51000b040d004c11460742d90403c0c0300f02120080c5003988100d5 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 999391825 1250 999390575 999390583
    0xe0c0a0909061a0a03020c01020a030603150504200a031b03050d03020909070e0607020d14150c0f03071704050a0c1d0a0c02010b0d12180b0d0f020f0a022d 68
    0x1601d181030341340c1c0d9106000089019100d00031000c110b5600000d980f0075843c0c0e05901c15000c07039004e031456207507020b00a46940700342c4406540103007030500c3c2d0107450040c2007414156811048801051400080c4c0e40b43d42e440b0b0200010407814900c003042d07002c01c100303001c02403040105001c00e601c0c0851805107100d000650f08a40038241744100a503800c1098400d459131407c940d41c8ca03070002d010350308400c0f151401800ba4540c07200462008e0040c0181407450800d5109814052100e07055402e0505280e042004043d800050070501003004010741103502108400d50a03010301e00030000f07095210032504040c1c4070a000c41c4c1c004210080034080701d082c81e0300f6900c545508225808004144841c20f03030030480c0580b01c3c1130320495000803482203103405c102d4146c0d902604200da94807500c0c500c0781d80200484041481d40301d0310285000800c05003980080aa120389804c1e0a4075000500348030f010b4a004181c2d420030001480568400e07410012502025540821107088504100824200f069840354031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 999393075 1250 999391825 999391859
    0xa030b0f060a031b0f0f0806040605060301090c030311070609321c11030303041502031015030e01060f0b040519031a2202091503070e0c0a090906 64
    0x300c0c54284000c0348050307544446240c011500305414660901e10861142158001c6101c5c00340051070a51000800c4800b412400041700c1d10300c00500b40c1c581d615264200589401001c06030b15540e141e800200107043c0031000030240d80696500e07544c0c5480f40c001145080080c0d000306040c400203580030070140c00344c00c08880302e40c01e05184081c0c9140c441540e4200c01e1080c0c0c44050b07407018819044035105a004461010f0240c09564454001e4181030b052680702c0c070055801404000c070b00307094500d45810540045802130300101440d030401d50707103400283c04451000e100340f0009480b0308001129010034064440a0404010340400d45850705244600c0382c0304511500c0c2c000d20f440041000a41494400c200c0116000030421140490010007508001c2c0125002c2c0c0c0150140d0800750340c8007540c4514481100e034058104103458658030b9480c20191041e1603040e502d485804004100c81c203413142258081c1d00c501c0c160f640c85480300c400142443c8880e81056030ba032880c00100708060f140b81d00f0310440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 999394325 1250 999393075 999393091
    0x10051015030e190201030b0f090112050a02100305061305010509061207090207031707031533080a1103090307031803062d0b03070b0a0203161209050a030b 68
    0x804100404401d6001c0c0481180e010140e00a421070300d4800140984040241c82c0300341d03000c002c00346000b41082940d9581284c11307900004010010301a00d010080e0141c88140610101c58440c882035000843c5071062001c0c540001e61034409101241c103080003511010301551105100f20340c10a0007282e0741e0b050041019124540c80c20311044524414440c2070080d20741c0c20030540d40d42010741000b520b500980081c0401d130301a501c000440691003031286a090600c40ca407050301c05403400718001034408050384504d1490745219031004400c10490340b02e0714502c480b6140c0a58618001c0403000407544212400791103290204108248040d02100711115281d16050501900c45906e905201c40ca50715000100402d142c08600c40b0f0141640000c8500d600c184455880904400b1041d481030b25101c0c503015815030310140c001c0c0940c961800c007500e0704038110305c100d07030400c403944080a400d00d0508100b41c038103c030240729031601c0c658044040d001600060f510b00506501d10b03994a0011207009003040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 999395575 1250 999394325 999394349
    0xe0402030a020408070e06090c0307020309010c02040204090203070309120509031f180f051006051c03020c15070c0504020306010f030902010512070f0305060312041a040305070e0702100510 83
    0x1d2400320141d0640d4041d062a1046507980ca444011195000c502a1042881640701400203500301c0340020482c0c0c1301d44840e078051070900303e00d48010b650b00c2c0902d00049a12580900011411414501c007843c46081a550301040916442c10030312210440707907049204001c401c100e00d0340c0d192000034107201605080301410044001141c0e82c98001d1440000620b01e004104c0c1c018802d016000b005c030074207107010301d080d03400000c0031400440459a1a11600da000080c000d00307110024030700149441002d01900540f40d030240c00c1000034100f00c4048e03440a52081e0085094401c0c4201580b013440900320a0301e0862070750400f003001a01a1a800e0140000c15882c2c0c0e0000003103901c101c0c1a00c005580782564411907081c00030018003002079003103803080000d1612000540a1500081041e8805d100103051440c0508002c01301c00388400c0204480c810050030440000002e00800050000300009991902c0d5405e1003440203080c00031120301400c00078102800c0c05280161003000e201240c0e6070103150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 999396825 1250 999395575 999395581
    0x60903130e0c04092f161401090822080604020a050d210201150b03010302010e0637080f010b0a0e120f060709060e0328020a15120219050703021203070903020406080309010e040203 79
    0x940927000301d220007480e03404e01140311a000b220840b0110746a4001000350702803543c645214a59400d42281c01940c809100502001305062181c91480041e00a440341c034031004003464250201c4640408000041c0c0d507401c0910340030069125000050106040414a5545141c00003411032054400051068500003000002c50140510301910030703080400d40d070188501031194001c01c01e03c4411704c01c081281c0320009045074441c10340c3c0074161114120140d0910012007022140301948810b400e170494424130910184080c1007000030348900d04140240f19a140c0010300800c5041c0c3ca42c004028044914224002a500402c40004c90305244074030309414600008040d03502c91008002a40007411600b0120303030309048030340e00c190a09103611000743d41c09495503000c003203102d00b140710075000d0380d000420500c40748640c004041f078501034812030740c103040103403098100c3da4015110000880c03442c03d42042181010f01035080141904030181d8103080038400003904900c091910301e80324642c00800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 999398075 1250 999396825 999396863
    0x82e0605090a0e0103030804110301054f0606060206162615032802090601020a1704050f011e0804021f11060903130e0c04092f16 57
    0x600080083c10740d041815656401c01a080070f070152415541200da0003500055800d050080c28002c0b0340322017030b407010000100d141801d0443d5490100e0265200c004161401418950b9a6100c001c920742400c0703140d03411442c040049644981c041c0c02076411103004c001000c40c000c8070300c1d180b4040b0350610313406021402d01c40300b50340401032080c080c02940380c0d02401840740390705c403048040d46002c0d0102c8040b00e1045400e11090390920700c90302111191101c0446c01400c2030310704940c0002040c0104d62080c1c40303d60b1030641031203010420070581a804103017001700d0310703029900e111041000c0c02c101c4d5402580300d02c080341c0c03202c00070740ca8414480c041d004981151030f11401d14444400f000b91943d01310402c042d00030800003400f01c13008000e00c0b41d5008541f040c0b42c0481118408845c05914001e0f941c038000d000c0101c200c006040c40104142400b002580038114083c4203052030030050f4003072001c4121030480c59044c00403911091010802e02103095000455848107408940000c242040e0303081400c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 999399325 1250 999398075 999398089
    0x307081009050112030f09051507021302120a15050d24020d0e0c0604050907080928021207180e121809010806070801060503090102070c06082e060509 66
    0x100001c01180742600001302d0590b08071240c6915446039842c02d0707903000d916200b1903041d03040703005550344003d400c138800c83c505002100a00820344060440705003000c29511207001c0f078100602c10001c1e0300d13140041008039031440c81480c09a500c0c3c0107a030002c441c00d0a02041e014840141c00030030440300b1288041c069522040c12620700d007441c0000390b41e0f174400c10714102c020300340b140e0305035040e84580c4401c00501d02d0450f0994050354809003c2000a070389007101202c140c0c1c8007a041c0c0490340182041384185c1e201900610000960151030480d007a050b5105002000342020107500b85904018028060441003030843c4048840c039080c0410800140c0d240d150524140c0200c401d0764010004104010460201c0921100002100e17144c0180e80e840003c4d03903c03000c0459000d800204003000500810b40148081c5810050007070005007001c08075034600340420312a402c42404a030700c40301082601c0205031130f15030107a030001484525200c80c10150742195061801040d0911101040e081c00c0d941f6004 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 999400575 1250 999399325 999399329
    0x61418070c15141f08030f09060f0714060601110a0b0601080907050303270a030f15090b0906010515040e060d140d03090c050904030e090a0f0614040c0c020603070810 73
    0x540440160600b851005051406040c0301c1448001c2904001008800841624174103041d80c0c034810310300b88c3c01b072040180c103a11250300060300c44c109120150100e000c00400030f80e82c186800060109080140c00980804c915040c189095400305042c903001560022460390030100a08000351140c0300c030f1000c20305050444e0042601440301080b002c0c0f185000d594107810f410080e040d54426200081c0a00c485a021800084c00642101202d400081c040281c4020b204040c801d000031001c2e203d540d60f17014000280e0f0450000e41c031403401845185000c800b8003003142c5901e986d4514003440c1200303d00003e1030040050b0301c501080500e136028000e02422580051000c0c400f134400c8a2035600d8080c000744444402079519030401180428a41400074050f8011501910340007100c00e007020410038410341c024580d480c0e2607119504600b440300c0900800b40a44808800e40e5000d07208281400f084508540a00c000c0100080109016840780d00840f40c02c40e2052401d00c0c1c0316521100d50240b031740c0d03551b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 999401825 1250 999400575 999400601
    0x606060327010e1f0c080403020a0813050d030806030d0914090402042a0f0923241804061212020f0d053622061418070c15 54
    0x40004d2040c08070000040150000020801704040c1c0080e00d4200d488190480c4d005001d27a1000480201050f02d2401408502c0700c0042d082d0000c4d0b4035600460420052004101c0104507080103120300c07880c0906c9241c1c0703030082e1403038030240c4540303003444411217094642030300d500441c05035010900b95119030300144a801c44002c101030311110310540d480150004440320f0400544034500c8001e0031031040800c80200c511400803e1035141491782c8400c0f050724040d507155405207040b42c104145080803e00c0e00350b51602001100e460700200080c004203200000456449541740c0001072010580e04a500b00c9610340003102c030141410856801d81c03034a50406031b2003003640300d1032421202c5950b0180050505088111400001ca110420007030400064640400e2002104103407240150502c41291181594003190604a041d101c09240c0215001c81e08403101c4080003000a01060820030548814010591081c844d203240c00c6400500a000c1d0f02c4002b06119104603005800c291150084842c0c1d20107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 999403075 1250 999401825 999401833
    0x3050f130506070c0501120e06241002030c16081914060c04150c02012123220c12080d02160605090c06040308131806080606060327010e 60
    0xd24100101300746010f108060000306a11403070701c2d4440c02d5016102c40c1101c06030003014075403a5006c04050850849800c9210078800041100080d0b8800c103100d000041543c002c1d640d500d54502074241032040302c89008010f074080c0070701080304010001d00c40e01d258103042c414035000c80080c40c05a0a018603602c101429228400c2401000c8840a004100700c4054080e0240c1e9100036002c259136140808102a0114043d80c031b8140300108880ca40301e203034840c0b1a0b000103040e6500c0c002118140300050400a450f100c3c141000901c0c05d400b2150f02003489030109078200100580d60305030520246004400404044550030420805000f05854101c44480340a54995042800c54240302000d0081950300a0800c800710b00300c880701207451004200041c0500b80f03400d04540b60b541807503020118000c42406882c80000e0441800d0583d0115107291060110f0764614015945103002c0c40035100610400c0100240200b44000d207071400b040400010888100580d505012401800d160421000c0e84c02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 999404325 1250 999403075 999403087
    0x7030602030a0c030515040e01150608090c01210e0a08030c0703090918020f0d0b01121b060e10020a0204150810020c032a030a030c020d020a03050f130506 68
    0x9100d4001d0341c03041521940402ca01e640014044042c1d031000d48a242614200f0b0a068290341080d41020904201e003c00205402282c2e45c1c0c159408503ca034420400104403c0501a0820f02031021203030f004001d2905218101c102407903c0a42046175901c1052682d58042c2c4001d0b0030410b103c01e508498000140c9912071a1101e0f0b800050307448420101c0c0021606a00032807500c40511030350b8075121150203018240f01441e0300f485070701900c2101c0300f40e01c44076040364000055030101f0064040d06028401700002c283d1450040302084c1d80800b20000709800d4181404001d520609024201008480b9600c1695401006a0a0803a0840d010350403038107004000100f2005041d264084644070000c4400d000020042d02c012400340b44e48840d400c0e001042107207510004401011201031003008540c07041c03400340c44001d1450b80300b0305411021984400740305442540501c90a060ba003403c4c0007411520940e95402070540c0304a00302040385d01c0340800c60f411700e0000c094208010300000303000107594803 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 999405575 1250 999404325 999404333
    0xe130c1e21060603141e030409110f1b06090c090c0702121b100305010b09040b031603030e1f0903080d0f050c07060b191511190201090f0308190509030703 68
    0x510045e000600500c1507800032a44d442c50280460100c2d00c140c8003840c1032504010600c07014103500304030303190f144500b030140300720380118800181800d42c5aa0410004070440411640c20404000c00030ac0c400d0b04043c420118540b20303e400c041d07101003503007c07207590344001c1d10000701d1000c8400440c016030301c1094030180c482484440b881960000480e01d0030140107031000110705440090113180a1214184420340c9541010f030403a1001680080559940d100c2a01046916101c103502c00d40015014481000b03103414580c03102160030001c0c40503240004c0c03034000301405201051000800c45103000600e180013121075800382134144000304081c80030f81006582e440c084c1d000040c00740c85e0300d4079012809669150010b0b001c490700e03141d43d44002c0f2081ca00b04460310031809500c82c140034400c00d0740ca500c00704901032065443c3c0003035a034140d0812a070240001850f4441c08c2d0805005040e0965050021400350f23003c9c0c986a00305181c05003000c4c00c3d943c0c03048803540900a0142d40610a5241c040204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 999406825 1250 999405575 999405593
    0xf140a0506090c061e16241a0117091009080405040606020303060108160207270c091a090f090c0304060f020405060d0c03060e130c1e21060603 63
    0x10302245003c40e00300c2001c00b81040410703c1070000001d5105891511000b502069502402ca80b81ea0403004081c1c0a03581d8541501c0600c52140342500050345510401c0c011070944071354159040d0010124400c600602d0020701000d4100b0460517607403080000142c1c0d0700c074081085010808c0c6002081c401c03803074a413404040d2500640a842d1103541401e1002c52214800000d99215181c16502c07840a5119072148a509817621001c0d0030840c02071302c2010071051840d404998030501e4a03007020007018040f080709003c40740760044400810141010400071920340c0351408822001120165580d054607900080d40110186800380d04144107404002d18410500042c62046009090512104050300e2404040340304d14052150f00c124140000400d44000c0d5102811301401c47c24000b403160745600d12807030b6881d0304031189683c072503040364128100101c4022001c01405d141c081c800300c14000000240d418038060203a0010164107000d0055020301a1200c01400c0f41c01000030440b0585a00780b1000c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 999408075 1250 999406825 999406831
    0x1f090527030a030e06072a0615090b0d03140c0307020a0305010e06011509090e01020d06080d12050c030412230d0b1002100209030f0f07050a0f0f030f140a0506 70
    0x1013440c0c10358402c1c0c464030125483d071286055580b09403020780071008616241c440041604c41000390400680c000440302e21234245207803c580030104103940f17000001c05c26a11140d92081c06210016010000641c018122031012403e00d41d0454543c006c000c81d41c0d01d10700440700d0195210054000c008144881940031007040e401031410f480d09a82c03200b10000d000c0c400b450304880010703202c0d42c04004020040d446000312001c440c00261501700d181060405645054001410a13080410401c0300c80360840301c10820081a848103110713030b140c81c40c003c5c0c016000090000d02402181c03500084124490032108900030803400f8011401c580c01e200b03461072604148904c8a100b807400c520550180341004103d0354403103c41c0d0003000c14000c054940d001940000c18040d07054416001600680c02e402c1c4648030003a8000b2000b0807180745060108180c0b140700380d02c1001e0101d44107005100485c5800c840340c040d20780150320a1582000c070700d496582c03070744107000c015031600440045900300200806c004e80 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 999409325 1250 999408075 999408077
    0x1c050414070305070e0c0405100f031a01200a05191703060d0201030905010b100c05100c0518060909040f0b011e0302010305180d0210051f090527030a 66
    0x481100c01190349a4070121400702900544c8488810007903811800c030855840403a40441c0360405586202255080c0c006580d400c0115109001d202826503151092091a8102c0000d1601110f01c0d10b0004e00b904503044032404106589039040d443c0003404101900030f0300c0d40202100d000010800c605a42019402d1085513a4a03d1441f030f02030300842c03081a2402004010b0111901c4610396005400500500004503a2075403648026103266031100110003e103d481d4845d280c03940502d1800307074100724600000d800d249103448254400a5408010745000002c0e103650340b65034018803000940c01d401114041d036840529103003000204030003402242d005500c01c985000c1c2c5643c941401602d0700c01039000a0700504a145410009980b081d0842500031032080c000c0752000310820a502d0610030b022606030050391109501820314501842210360140329981c69911140a1081800e6405024031520a20075120404038009800c03c0310b5450340f0b407103200b0000d540701410120481d10303500f101c84004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 999410575 1250 999409325 999409343
    0xf0a170304081f0f050403210b130b0f1e1e040c09060210111e0f070c05120d02030703110c04060f05041a09070c170c2128051c0504 58
    0x100864801c1d0250501565148d2a48510a04140c0c0b000300c610f1100d00007941102d8542c24500c03039075121203111210400c03503a0408116640c81d00d0038444101c080d10a4540a40c119942c00070701e8070050f9030f019866007003c41c0d51082c645072107011003000e0852000842c3d4401c1c6407810104e807041d00008520b01701e4080d60207644a000c03000505900b224410a988540c01e00e0801c0b00d6060048101c84a1a69a0031154028100b610300c1c0c030846400c3d0805401191180141741041c410340c41c00e000c0c24103030b4540c001c0041034465480c600094907170203424002001d011031380e90041000981803100521414000c0d00803c001541c0722403a0281c4800d0340324503070240e480e00352034100c1903011713141d1020a202e0180464000361a03c603021185950b2032501a59100c400c0d0780e4061489800700024014007150000901035464004040b01030080800030005821a04100003910056641c55140c042407048030341d0342c00b048440c0010344207880340e42500754116007562140100001c242e48484d0080c1d010318050 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 999411825 1250 999410575 999410591
    0x504030b09061501050a121a03070b0406020c011b0203151906050a0e04020315010b0a0201060b09090a0b030f1608210708070201170702010209030105060f0a170304081f 74
    0xc182c496005803084003000c0030b0414031440d41c1d4000c2c001484c503101c49140c60001898070070340506c121f5002036a91840210500d06004041c5800c0010300040d18205440c42c0c0b0307141ca1b00801a507605202d9500764140301c08680c0110b4074000c105442c28010360050156807456014604810f00740768202c0386140e50b60f280c0480780c1601c0e82180300f407134151207001c2c0c40f402001b410102c400030a824004d0040381d051103a0031510304e46a10702d0031118000c102c1c00b28025125009160080d080d00c60541004441c1d99081c0f288446079a981c41c1d40c0c0c0c0d0003540750080020203604500100e814203082d100d601503e0300c01d4000c072025610102c1d03204021601c1d0601a10030311080b4603001d44c05003080741c0002401e801c00740414004107aa090041c1050b0f4814140b10300d4581c2003806038080c5180464041000d41d42c00302e01b6580c2070600380100380c0c0c00042200d41c1050b014601e030001d110380140780601c6584000c41140e8410f608010011a0083c01c03400b02205d03419103078a07401001094100e003d801d651800c1c0624 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 999413075 1250 999411825 999411841
    0xb010902270105070b0a0216051b0402070c0308130302120708011a010801150c0210030f0b0111060a09030507020d060902030d05180d1a010e010618030506060603190c0504030b 77
    0x11503a500350143d4900d4078214154541c08291480501803130200c2e50308200000070404400d04004401d88100c000d44980400070300404220101161414000c1d40100100c0000414802c150310551368482941910703403110411580c06554142c0000f504840c100c4040031503e0400035000c4103c942640c020f1080c07202800032001040c42e40c04425010944440041c0b04903811100d80748070800d900c2c504599244115000500e01c032070303e84039010109a4440607a501c05200b4040c1d019816400e003020030000100b0b0303280300c0e5140b600600b0010500d5494050108040c03154040300d00c03654000300720080240150030148024400010700b20300c02d00c1150070b088003050190040d2030116184e40c4041d0003c801c0d100a10010804160003180c481d40307203024907040030403000113090181600c41e824150070b40c1485d00c05082e040f65034802ea0088440b4040400000e0b1001a50640c8031b14183c4006403644c403203002400b080c4e80e05034a0700d041c1904048150ba20f042e40100031340112030040c40d01052a85803008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 999414325 1250 999413075 999413137
    0xe010603080310170d0c020d050703210c02010c030e0a0902030108032503020601120c0b0c06160201200a0e06160203331902160210050f040915030b010902 68
    0x29000130350401a0041040f07402540c200e42207a0001d0190056040d042d9611802c0050350b80040b1691401c140f10b030f51060f12501d8140c0c00c6050141489120031519800280c6100308060006040050202c00500c06031030384a5690020301c0100019500c0e5610f030801d15032203400522929a401344005110114214041aa450015010b03000b4200c00d9003030140601c07441d0f080000940d000080d648000503c18441801812003190307a01c054001030a240f1849112003a8080811085a0410095042002c41c201c007424000485140e1503a0f038003038800b0141e41140348500415400100800c06005000151303058500f01882107059600d510121581007074400800c080f0000d46041018600c03202c22350481c1e01c3c0d42c0021002d0498022900403124000599000081c42c90610401c1107000381141803080041c1c0e000002800c0c0581805179840142406010f244504403000740c0743e0410a0500c004100c146000d190002010917403983c4030381c4808065400030322a1500054000074100000c4410780e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 999415575 1250 999414325 999414359
    0x9030d0806011d030307080703110f03211009060308041d1302041d010501091a090f060126130b06040b0a06050a120e0a05100e0c040c02010e010603080310 68
    0x1071510002c1680d1020303c12164100340400f20380510080104c0340100d042c40014040152096990b800c009008019080c1800890207005c1200c6d4001d1003607400d0302c1c4c1701c05c0740914540d502c503100b0100c80d5074001c842601c1101f95446071084519115000c024461203000a105641415010200c041c0c4000c002c40d2921404990400c0004c81e801824001490310381c021b6112058400140100703841d4400010b801c5407020b9100150300c03075503890814100508805201d21080b030441d4130110510700410664440c40e40206014104545842d00112201d4036029440280344454100300d10b42c900660102002c620082c03007541d41500d0400018414542409140e02014010f4104450a407409a09031001c0d04a05090400d0103425070320f880c8429850320031100c01c1829000280b822609504102c0d0401225407080704a003421b221005002c02000940040c0b0501c050300c00041c6440e84141c02c1f401454446115841542060800018800e040c1d0185001d0241b181042c003d00e40e0301c401c0400540702038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 999416825 1250 999415575 999415577
    0xc03070504121b15030e0a020603060405072021093a11010f09230a080607110118030206150406120f060615020a0f08130b09030d080601 60
    0x4000034014160020305640312030707120f69840000d9003c00003003240b6190480d0094807124400c150301d000c00e207601d0302940030040c0c0c000000d06210760980d00410705500c8000c0030b20f40210344035008150f0141c1f140b0400b85030300c040c01c481c1000c1442c01e100035580b03400640070180c403543e1420052201c0c0d981c0e410106c1b500040c0c01480401d00e0300740748504224a0181c100c140e5842c02400c1c59200201f4041a007000040b40b0500e131032580c0b059450009811043c0c0c400c03068081041056080c8000c601030300d0500c01c1d10300c440c44100d10700d1010200181c0342c503c00d0f41082c0c065006803000d024045401210400040d201302000303108610b03004d00482480400e500c0301400590104010401d50f0080d80d6007070043d0710002c0c00100d00c10303407142e40043c2c00030b0a644088030700c40e58002080041c441d0a100b02c001418002e5414040e44030042002941d81d040d5100141501940c84654403c0162410807a0b804101414141541580e1950400070b90380051040da03019009010009490030303c115500ca02c00c1d041 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 999418075 1250 999416825 999416827
    0x2072d0f0b0a2a03050c070e010e0c0702060d24090e121602040203041a0a06060c0602030601170c0d06080106081f0603230d080609060d050a0f050105010e0c030705 72
    0x4070340302c2110300c00c01c01809000c000e16100800c5550391594100b2000d114042e4a5050743e6403a0b01400c5031070980075610414844280400500c46040070301c49580c1c0254074284441d80312078090000034954030586a17110f00c42442e040204498100c3c4c10403000007040405110809950f489900400b40c900c4840820710b0368101c100700c50203500d0600040c0141d040108009010400d4590104040707a10a0b034042d13030319115540c01d0740301170f200c0c074840142c1c0521100390a04c0745520b00807000c0c2c803158005000901441d00400000c0e81a44540301020801c48624802402e0b03081008800c540f582c004150701c0725041c10a4004548003a050140004840500d0001c003000345c0c2d00d841100716440315001d154821901c900d00000411a192410070080240d58269a139051028592038500749198002c40305100010042011556500125540c0000240c5205510301994a0014140710844000820354440070a464092040543c4094107071405400c400d442d94480041608003800300b25901000140 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 999419325 1250 999418075 999418087
    0x20c01020a05071719210e03060a0209040905011514031614030f0f0303010518070f1115090d0e01080114060708040b190305010f0311060a02072d0f0b 66
    0xe0410206481480080c0c03e6491165905c080e81c05194401d5505850b5581480b1603200c900e1540000210581c140781080c01d81c0c1e24941c1d0100c0d8a80750000c0c846e1040c0383c1c2c041400405520380d60071448600340d2000003040040c10103d880100d101d403078011820342c0503181507503900310f040000321400780312220710a0700c04803890300d1083e007400400e40c2e0500d0341500900707040001e0340c1d8007008020164040000516220340c184070500902e00660b041ca94841d044140a102e100380e0010100c001125052a000002c100d81100c02c0d45419040e41c0030002a000300400c00801600c00f0480402411040d501c0c03001c42c446417001100c0c100001c0c06280c0d1844544020200c080c43c3c0310b401072141500c5440b00342d00300780e43d440f00d48019400c001c0000c04117003089150008030560602c078842c090140613200112003829901d0303141034400607050a600690000450340d010794020818000189502c09005169420300000c50060410b40003003400006580200445c0450442d000082070b5102403000c6400c080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 999420575 1250 999419325 999419339
    0x506040b0615030103120f09030809130219031a12100b030127020102010e06090a0609050a120c05010c1e050d0912020114090f0705060a05250201020c01020a0507 71
    0x158010380303090352140701840445029568200a11300030b50195818000401c1c8454010b07000d40303a0100d001e1308100d503c003403d10016501500b91244076000fa80c005036149242d80d903c0e4001d101c0c0400f0340c100c203006810a181000c1c2d050f006561031132400915001c21900c450309100c1000c2100d0803030642c03904000d0301180781c40041e03409160703201c030024000b0401c502d0003125028100d120780d02219441030762495940c20365070240180079000c01d110b801021b69207002110251100e0803207400401203a2207070038038418000c00304842c59074203801440c6001106200b401c00340c0800111807045885500b00700c0c4c02841d1300c2c0200d5140c520305800c0207020200c000038800855003a401428204205503440300c402d400b180d051240c501722451580c000140010303204400a042c610024800802c0d0380c4120090305416401140903011100c00b070306d22a80307035400240155a00e0042050030010304c11101c41954030070a040d1080c9030030a000381c0950f500180f00000483e02c2d1411490b0203441507000210400c405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 999421825 1250 999420575 999420593
    0x50d0215040b0f041d070906050d0e06101503050c09060306040221190902100f1106130605070527060c06101509180203150301150303030612050604 65
    0x2038000038501460551282c80c41e91060300001e0790a45803070004034003417011100030040801c00811108101d840c034680490018124030342405680100701d404220000340c400703160000f84102c0c98040951300b4928107000c001c81015217500c608100d01c0110340d24896214081e120b92402a0f03429941035103801702a0702800200d82c4040e00f850b411580c03c0001c03d500010041c801c0051a508000c500100d04200124816800040c41024803a510308007030000140c4d980f550311100e0a94070708100c07919084d040c0f81600ea541e03051400c01381e1405900300700a03105140d1070008114501c20003003040a0b440d032003400c490300c0c00342503030081200e10040700e005212118800300c50220000217189503e071580a1040c1410000c050b942c42900c2d80c0c03202800d1044189030004001d80b4005840c0139008180f4200c61a0080844c60140c0441c50360700202080700d644500c4410b0500200c050028454804030700011409d400303d41c4000c2d800030380381400101e41c0d4006020390740340340c54000780102850345581d00d44200c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 999423075 1250 999421825 999421849
    0x90e070903060510051207081c0e120a050d09061b02060c0a11040e01020307080a0504061b0f030b120d050309030919240813150e03130f050d02 63
    0x14000d1841000000403094015248074051003a4040b41080c940014000c0d0038981c0319198040c0d4101c000140300360352001030540e00d4070031035081c0750401d503080383d000b0748420707071507000b5190420705041984000450001d03001181030b22034411a4021286101c007201c640b10203020b00c1c0d001810848080d444521000020003d10b80024289440c0140840c011440c3c26250f610485040701121f2050b421483c043c880e410b5a0440d1100961451900020080052500503c000042c1c1d540b4000b041c180301155001d2442129484100e0034048880d5801800140c091640e400010b805c013130704020349081869610110210381c2004040144131280240c480f42c1004111a07034910040c8541a4196243c0c41c21502500500742440211800d01140049507100c048000da2044ca8202c8800302d5168492101a8010348901c40c540f2400e041c4c2c07806841c421031120f680c00705a41072101035035403400e0200040030b080c1040b25030300030a160348816001c0c618403a441440e074012140d0b02c4142c05802c182d48081e80c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 999424325 1250 999423075 999423077
    0x1060806060c1509070311030105010b1b0c0414041101030b09060d030e0a0b0a11070b030402090a02160804140f06070b06130c0903060c0302090d2913031e090e07 71
    0x280e211020120a440303001d00b1113203c0016844070070204140000e001c88a6040581034000388103660502144a506100c1c02c003040301c00002e02203458582540901072400621401882271042d40ca496110040c195800d44066401c0b9912040c610303800e40c0240701303840b44420051b004007500d540e010104560b6038000c8000b6018044084414817941d9216450b00d8003078500541260703203640c074000000b0700014000c00c0c0015294070024044c000010b082c82903e030301680c1220201e40b00d41c3d41a24210107070042240da20f151103152400e00c3c04101000c809442500c0c200d004280460120408012000d02c05012030b54012001304121000710f07007044910343d0301c14406400202d445800182d0b41003101c404007032110028124000074400c219946c01624480c5d0260314056040800880004403202c2d0790a00c010010049410060740205100801e24403013803408120380203a00e005090280c540e5a0514124009140054604058030006640030790300d09030303640c40301003072070402da00d00c0b003050341c042c0004c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 999425575 1250 999424325 999424333
    0x50903031b0109060f021603050f2203060e15041b03050a06050411010c02180402010c12050309211215060403110a1527091b0f0e011205180316030e04020301060806060c 74
    0x20014230032f140003050400d0a040002c15840d891418002e040312149030410055801402e440c012075900c2252250b00141c214048003502c100b0f8400c0d140e130103516548020541d02501546405000301c5500c5948543d000380c00503060400700307100450301000c0c0c4400080d8021100d0072040f091810b84031041c1c2c0e11a1043c1003083d24640d59444034485042d05910303030070001b1000070821908900034009810301941c0c646420a80c1c081d0b61085880700d000b28803100c0001b8031900d00044131241c0d038504005030000040d0215a985482e818407062044400280c2c900510303840710006a00c9044040c0c845480c0400d81c0c805c2c1c00740743c60300304408106010746031004909140d001c1c0860200b40f01d1043c042c040401042050a1040c107d001421070984080d1010901036080c80e03040713603a40c200901c0c2002051f03051000505569002c00d000e40b55002403540a001c0c071004c14012620901405010600b81c082d45894880c616020204800c0c1d100901481d000902c841021843c1814401c0c06002c0081e02e4105403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 999426825 1250 999425575 999425587
    0x1803010b090f100603090b0105060c10020a2307110907030204081b010e030d1d1c1103061f09092405011403030415050903031b0109060f021603050f 65
    0x501181e0241c841c01c81044000302444400d80b00c1c8940070008003190304043c45520840c0d19260a807120500c1414003818001800b40c0071200c040c052404010705440c400c54039003a90b00c8005261035036075101403c070441400255400100751500f5500d8141d4031031a8000c55108510503c0801c600203025582455028440490340760000e12168030aa9000103000c2c9046828100052079400044c00c958000d4100042c580c0c2d102d45c0c0070003141a84142c5a080c025076031456408034000a580904408843c1900f40ea183c0030030110208684168004030122159074450719012440c088210b484880010b02140701000a0200c680000203068000c0000310001d5601007074040c411491411040e1a06a660005000c401e61800c580000309906400440c105420039800001402e90207003107000b80300d00883c0c10329203690100210380e8864102c0c0100880080c400b4a218040c0c070000a04a40c12400d050b118000700ea594420780b8008040000106501341c0c0b59107080c1c501e64004005070041142c10410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 999428075 1250 999426825 999426829
    0x91b06120a05100923071701030f052802190923010602010207200a051f081b1602040b1005340b0703020714010c14030c1803010b 57
    0x440c41c4150705101c4045400c1c50079a102c0e811640040d0042000b20b49049009008500302002081200d50070340002c91954440140a94525006c1c0d01d61074015401e940c000310810440c0e03243c0428451241c0202e4410f0000140058901e0300d99030000c10341e48075040c03074140261a1131910304854040c02c0c17082c010501d031550650300a0743c8128896280d4944800f40441d401d034514014240180030a10085050074155070b41d0701d0300c100d21aa540c00034550b2070044d010752940c4040303003c402040f0040003148001c2d02e0540d081034a041b4a40c2500110300901c0000d2500301480c12100a04911b510a0504e012280e040e03050342d02c0003591050783c111350b89049042058032142c4038001c501d0040d842d400c5d1100e0100200d01d119410030a828003080b070071285c524004029428a804440313621141e0503940d0b17510041e044000340209075000e8641000c1103105038010106510280c00d8043ca80e50301340c03103101d94a034502d08600c02aa0405040001080071801c004428446164211340041c000302d1400c0501c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 999429325 1250 999428075 999428107
    0x915100905090a050c0102030a050405041a27060d08070303020c010e0717060a27170706091104090b190906090c0f0807030203061314070311100206091b06 68
    0x1c2c280242d92080d14240c0510404021440035840244025072410030319040082803030182d4456503010f03d46400500e0341c4006010f001c03040220010b03007a00038035a8541405c84510300c108220138403c0c0041c0003c98801e0404c41c1e0003051490b00075048924020646d03908500950125600800b50f550310389144014030302c00d0108600408546c00809030400e9026982401d10340c015147e810b4140c030300080b01180c226202e03106101d14180f114036018421083c104030640a0000d020b14101c21400684081082106e40c0150b101a00645840810f00340540034041240c103100009001d031410100010108140c1114000300041c8603100841d1011140d603441050f0303920610121009600044140400051814204000e080c500d00038007016165402098485034060300700d141c12000c4c0c00529081c4904480d64a900700c038000c04075550150760381011800c1103100d1000512814a04000403030461000a66070700030340001d00a8401c031030034003003895220034a480d2220f8004200b800203114003040382c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 999430575 1250 999429325 999429331
    0x81305071707050a0f1509031a01170115230d0c090e1f110c0f06180d0813020411030705300402010c080f0a11060703050915100905 58
    0x240c00800c440e6000d80965050045a800c0310b1301a003016801001030b54600f51380d0300c0032210241d480181c03440d05144101e803081d102d5080601441b102541400980041c1c141c114103c0d40040802000001c0d40b141c0322382650001080c001050003414818884100d003c4502810a070740000c2070150144110007007042c5074690b8509550078800c01504010034880d50260100001200002d404070044a201c6820202281c00410900755078440121540c90920401c43d03ca5030000780c200c0f004c0c80b403224607269460001712951641d440400b1214000340400040191940d52075840b078030100ea6a00501001400c484031082e0b900c280c850340350790030500007600203500403500f03903440940e208005d00030f400c0200001042c260955201083d03222401c0d40c6955144e4206e503091926042440160800c04142e0180c030b071a4414a110000f54024042d400800880014600e20261081a07482240c207504507103040303440040703d0300020718100c400b18680c0225075001101c540c50142071600e074039010302100d401f2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 999431825 1250 999430575 999430589
    0xc03080f190e0606030f06090312060f0409080c100e0312091903090e0c0f090d06060e01080703030908060720010e0105010608071205070e010c050a0210090f090e030a08130507 77
    0xd8140980c508050040701b60b01c11291008054500f130405070b0343d0b0b480c426003400d601c490710a180410b00540d10843c0000c2c00c540d0080c024040c4040c0d60070100219407001c009444c2d1440381c45888019880103004028507803c0c501c01550622558103c40404404c00415002150003100006524101e070603501040150080d03440b41d440c41c0c20101d100503030080241000850582c280319406011f5a8402140c071118401c0d191042405868030300700010b02904d030040750082c3e000c00000b180560b4001000f900300c0e4041e80d101c3d50a259600d100310744801c0c0603140c10002642c80012041c00d0383c04209010304070712400000045402d04806101e08440003070b0040303400900004140308a42f030303224456008501a00c041000302e4180030303001608056850103128140a0403c1c8164140482400b00048140e00581124562502141d0081111f041809413816000340304401103000c14803441074825a601040c01185456403203242998031000042c428101841d45880100004005001c003000071f0a030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 999433075 1250 999431825 999431833
    0xf080105040203070b1c1820010f0509090406020f0409060906180b0a030209070c060e0604021008010602150a0e0f1006050f13020a050405030d020705100c03080f190e 73
    0x140c0704240c10005294041c841c2d11790180845c1c0c18003014a03000d0240180411000039610520b03101112048060484c06030640840c404810b8000716020810100000c00741c0c0e038580940c003d01c0701601d882c00752010494129900400007000181d06500030007e03807200c041c0c800d040640c0c0c6c0c0030407019a007854100242031a1140c8080084400707007110315104d10905101484011a41d5000c9050300c01c481c031000c1c0c410907110000c910454000d035405000c40342c200d101071050706e46040c8019598107040e10300302d006501c2c000c08011854480c1014070b040e40c910341e0207048803a0217001845030407400070308540b0380c02e60345d1607502022240400600700d1a0101201500c0001040c0458804540241d0f01482c0990300354180c007a01a9114401002108070131500140c8840d240c2a088032b003070107980c001e190584916460b026019400164000c100c81d000c60b441c000565025108845400448400030040303410240400d0035014810b40c60741c1c2c401c00c110f1040e003030140c11034000026102245841801600 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 999434325 1250 999433075 999433081
    0xa05100218220c110106030c26210f0c0a0b1501140d0b0d140622061a040203100302090c1602060703020c06030103152412050102040f080105 62
    0x203a5052080c1810303001c40d0080b0750b08448078041c0803803180006602050b640e0300e52030388581c03501603614401e0a0316040c00070050903449150964140390783d40209200c01c24813001405c00f0100315402d01070340c070710200d001d0420398101308042c150030207118039000c85000c01480003c1c02c079180500907100c140140401081c010206082071030790314001500c2d050a26203d10410441a46c00c4080c2e401c0200d5042e00c000e0390f801007142080d0040c0302c10f0103810742c0600d03598000f20502502148040058581a058031100e465000302c201c000c0c040281280500400701c15060003042550f8003100409004c011400382c92926100041c00301d9004550040300c020a4a81c1030096090030b0f40c5103544800c3c01c403d040d24140780990f070780d04000c0d12020003d00c200300001e02c00c404c162003404507031140f070000b4012607120b584a28040038001541e1000d990705034a00f40c0001d84521886114a09400ca001d081074849410544001e8131080b00441c160303007640d020040040d02101c240c00c3d0800030101c02c00002010b003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 999435575 1250 999434325 999434347
    0xa02060a0302223602041511060912030606121023030705060f0d050112030e04051302061b0f100b01080f0105040b1807020604030206090f031b0a051002 67
    0x44900b009060505080e030303c00d000084104011010134008011420103058420045440300c1e041041440c542038004240040c4a0b0180d0f00822401142c9845e10841c603600d07144410740d107010445052490381c1c000700e2100362040700f0000440d08408040d142a14141480b100315018081c156003400510305200d80400404040503100300c2c3d0f00c401d92034070012800e44407000076500c2066010301d6200f11800108028642040d1040740c640e036408881c14002581c0d50540310344800e00c2c80c3c50584c04074500030022280751400d0304c106403080c0c441c80104200142035400f40100d5400100c500b43c500302c002c0340711005202040106502c0742000400500070688040142402e5a5516905038141f00710340382800400202c404940341500e00c140d400154000511002508412100002d0840040d20300d013848591680440c01b00d1042d0300940844400341c45c1c02d240c19a0314136401c044080d0940007032107200403000d2508035050914000c841120013080c0d40303446103804c0290424244052039400a252100b02d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 999436825 1250 999435575 999435607
    0x301020a0206101208040b1303050703111305040819021006030507030212010e070306020706060f0902130f050d0201030e0715050703020c101e0311031008071212110a02060a0302 78
    0x5481300e0140311350001c03001d40e91010240154041c4242900d00480e00f000840c3d84103416100843e0800c00b104d000325a0307410860b55000c0c4c04201c241c0100c51806910340012038900035580610740c00321401c2d2401d03a2000c0340e900081001c0c08040214080c040010680e04001d0049070301640c0141c010b0f100c1c03903146104002d008403c4011114459040001c0005030040109107641107a40186015955011030f01d8139400400ba81d41016840d0035299a010500c183c01d58054004410b810341250182901c50605103035644480c401c0641c45082e0701d40340001540300c7d80058001056400c21220b00c0c5807209030744196110071030380c008000340c400300342d01e024554100031614a00342c06940c01210340078506401803c0d0700c5051f049507120017815400701f180c503119501080d2169100888140c40b414003010390143c1c03900f20320425596214070300f004941c61046207103c038007141d807240e0703140e1164842040035251421160204803640c09158100c2c00542c82d00340040500000650f00185c0d20b4110034491504 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 999438075 1250 999436825 999436829
    0x20a0b03072105010f030b07020f01050a061e03021c02131b0915120228110d1403012106050c130b0a170603010609111806031515090301020a020610 65
    0x4280d007000010095200202110400c0d07e070000d44a14140ea10041d00f43d14000010400c41c0440d86424200076032002c03d0790004041e505001d03214070f44201b4240130701080600f80d00010394003440e85400102078503841865044000d202402a65031901417400c9102200d40704913440c0b03002100c0d039240c8102c09a0104505028002d2848604241400700c04000c0c00802d030042c98580143e40014500f44103249500141007103514040409500302d440345005001000d111a9800648224014141d099028003084018140e200c0b66650850b0310b4250b8008010300c0452034014400590f050b04404904580111071084000c20a419034580d11001d0f224407204440d480510480c07020320401203426440f04000000d0310440042141507291200045c2c01041030b548000c29541c641030705094180e001c500a80b810007601462054100105014049240b108580303250400204c00c003204610310f44410000714a01c502008281070203108070100b800ca81c003814190000d64051000c00004603046071050340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 999439325 1250 999438075 999438137
    0xa03270b0f090a0b1005030a0515150f100903051005060a0b0a0509040b270a0c050403030f030905010603140f0606030d020a0b090a06090818010e1c020a0b0307 70
    0x924580600700b6510703000007100c020100c1c4a0780303001c54620307035944000d60041c0500a05854003046a490417990301c5005a07140003003001c002e00000e0304510140540700196002415942144001c1010420800920b01c00c50041c045404400b00104a04110996210718130200005007400c0140c01c20a01072102c3c1d10a03944a54200324582d00c040c2c0c06030a444a40105940100b40401d41800080d518220610125882c2c0346510542010b0003c942186024480d100010844c06101d03842c200d52070f224602010b400318240000000b089807080c1e02c00c4841e6401a00005981c03512607640c07030800c60034071808540e143d022403100115220144442e41d040382040f80100011110444045d459211084004d003c0120b4580004e000b1181844560050750340000204401c0c400c41c40c1000840d00030100c145075409415034a4450342d4010788034040224801412441c904043c840311100f004042c140c12030300300401d070000148400700d4401460190360710303440700d4035800985004015080720050b5a01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 999440575 1250 999439325 999439351
    0x2070e010518090c03030a05070309090506151e0f1b1605100c05010e0601060219020102150903091003051506160b1803030a06050a0e07020c0103020a03270b 69
    0x4255902d0404042c14010760840c03038034980d0781e4010b2041c241080d404040b6014003000914941c0c10b94460300a011803840317915100f52050706c0d0340501085520031a0754a4200654841c1c5014007054000913194811841200c41d2a91902d600c1c0c0e9102a0010896038241140200c0c082c2e00c02c428040c2114401400c44005000c0e40c0b9005e810044c40d5141c034403030a4010850b00c50400a41841000d001041c103401a0007880034050076001503a480c80301f40704060050050342c0180201e04881c994a0503101d0301680101907078484480109a241c2c0301800901180c40304004d0008540c41e01140c0c250100b4603500c00041c50302d09528105030100314100078030310801c0d00300440c0b18043e06120701c1903035480e04200c203400d440c3e892898003441001040750f079081c5444040b04000d00240c0c0c80d084801500c009803046003c440e61000304038409081610b507080581c12540c000005548658090b000742c600c180b4001c958209070400c1c2400c3d1303088940080c3c5008104509980a0010545841d50400380d0b9030030031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 999441825 1250 999440575 999440579
    0x8030103140d02070302013e01060e13110a12030c0b010605040b0d0b0103020412080901120b01120b061c0b09090d051210150e10050a020c011211130602070e01 70
    0x291038001318000281446920144c0000205140f04545402082c20090200c1002c03580c218070f288201c0101c4096040d070800c2c801180f0f03d81a140c950307000e100f415800400000b11603403492100401c00c800035070040c00c44900000e01c11000b80440740200d01948030300e1050350041c14441c0040005030005824048100800c00c044519079044030500d401401d000101089a02d00403006441160b10014000700350807030310400e21000c02c00400000000341ca807010380024901c03050003a180041c1d101800f0442510105684151a8103e030b881c410001b0000c0d454012231541a074480d2600c0c0c100e20341142c3d80d88107104603074100510b229821040d4007004003506120701d10000d025100300c2a540600d21030810114000181e00e0901c1c10103003a0401e003c590603402c01400410140080c0d42c4644920305100605005c0780c055012034444207065800360200210318001540c400313902092040a5999440d00b085400d040180503000c01d29613002c5a00107145000c2c802413070061190800b42c000c0e0100401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 999443075 1250 999441825 999441827
    0x6050a05151f08100801020307021f0b060d02070c0b0d060e0112050307141903080603060a050606030112031e090f090c0e01030f020909070f140f0d02070c09060308030103140d 77
    0x2c21100509500d0000000c2d55408442001c03190f4a40c0035110540c004004d0182903178000c00d03110748010b1164403040c090107817031000c001542d401c42d03074454102c1030030804a521911983c008001c4180a6000c8412142e51211a0071031940440910145141d65080502202e40c00c0c941d0680145081001d108442d940b545485840380b0a2401c02400040c0c00c2d00c0344134002c402440701c42c1401d50a00c0c0b10486501d0281805809030208540c1b940c403074017411000071410006440392900803c00a0540d034110381c02c004c0e0007200e02c031030080c00707505000d03e10524070b00d80d070840700509001c008142ea680c00c41d2464605482c1991100340c10a80c0043c5c140b08040051035400180344c0400f600910300440e15285440e540e000034402d43c20403d412003011001c0003102a08061080340203107055454040c11520300403445660700ac3c0041c0001071070f404100300d03602d80d12907402400f4002d0049403106165540c0340284070072622030b5841200c1e8048040010000d00a0720750198586440c600c0c050100c013111410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 999444325 1250 999443075 999443119
    0x50105152809121b050306160503070201090618020909190b07120213050a050a060212130e011d0a0506010c170d06080a060b150406030f020706050a0515 67
    0x1804040e41544268140c50561007021450001c020fa010010f040d0085030a29201d01e810008103410104959040081e06040001e072040c4540700b544180c4110f440010300031289540b000c1c00190840d901d819464010075050f12034005c446001d8003041c02e06603194418070524680060a041642d0008100c003030712200c150510100d501c0c1e0119641d5840d81d2030203420381c0e14800304104003070140e2002c24100c000c069000c04180949004590203004036030748000300315400081e4000c6400513040307001d800c00103c0600002c5d000b95042100b0200001d500c0b81d03070080c2c0e203020980c4900e02c00105150031124130120700b8140ba03084180038005000358540b09002034121041c0301c40080440d41808c0c80c90309200f800800780c80c0d4142c1c080344280311050351010001d0765800c3c0100256405440c0000346a042d2070800810610303500448046420585820406d400614014031a88155502004100d001038114400e440c42440200000a004c1c18410340c514041c66080b2413580c000c1131080e00900814900750 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 999445575 1250 999444325 999444367
    0x216090c050f0a0302040b07050a03232203050f0303040c050f1e030c1c02150721110102040617060a0803030a0207020607141c140a0f18060305010515 66
    0xd140c0c42c3d82c2d0810200300320000e110f81d40c480c020707052020540c9400c00c600440c0c0b80311036a010365100c10004000496086144844481c92020b0010400c202c03140020034400e0603e48421001040c03021300e42d40d40340d09040c044034400d0342105400000c100b03c10031003806000701c080c11056030209800540507020403065807500340c4040c1400c0480743d1240c10b59608020f8203400c02c10140291040c089080d040081120400f001284501062030040d0303c40651507007a91100c80d0040c00035280340c0408030304040755040301d40006003009980c001c0d010485d0000d00040c4001c050755596001e40e48000e04104110070b201610f442d11800d070000041107116000003d40750844021000180d4500c0f06100040301032040000081075801c400414004500010401102807008600003003004540c6071401c6891040c00001c060320140d040c42a07201891140702101e00039000e5042c0ba0754a00050f0809400100141e07000740000b80d2a500148005d0419510648180098404c0942040501c1c00c01c16a8003500c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 999446825 1250 999445575 999445597
    0x91802032d01050102070509090601090c11010e03040e070e131802030f030a11070e01030b0a0f051303030c05120103060207080405060c0a1109070816021c0216090c05 73
    0x4000700745100c0241c800503861074014008050007403031100c0c1c04405500c09100c1c0c00d01502071035400003000d0910310107803403003281d4110187c2100ea0910b50002e00070207002d1403000400c1030a0030840040002481000d185910590003107480c0e51070300340010706981004041e6401c201c00c40921031015203400c1d4903100c51030b03041800420344485504050391681c2c46010007079454070452903200842070b000310081101c10f80c941d58441c2d003008103220013680c81015100b9030600e50411401040403d41c54070806800841000700855210700301c200d04402d41d00701342c03580f202201211513540100343d090301c141031405400d4101181014107070134641200500511020308056000505c0e4010440d0001c11103014040080549031a460020304c003d50307415208108030b8500301c48450760140340c54050145403003182c0a40e141c00080d07841064034124009810f181c1c81c02d510079a00615032400380001d98003101c050382c0d40284072040034444d0699020506e07a04c07803c4090301e00200000226409000c40710105a1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 999448075 1250 999446825 999446827
    0xb07050c150c190c02090a110a050903030d091103070e0709050f0409120512090105100603020901030906180b100b0702100e090106050408010b1807030b0414070201051006091802 78
    0x18000390a1680c8a02c0306461144003040c030711200c032242c001e04070714034a074000d540d5003d050341c0c1d0030150b40885504608c48060a0028000002d046211b107001300512040030703094a0404001d82304e444280c0d09050003c5501c0001e6003094241401c00304203a500528107608030a1040c14210f0f4007800d464007034010b850161a1a42c4106403a85a90308118040c541c02064200a0115072a000f002d54000c2450606116480c00c041465900c0500446000e803424031089142641b4010098000f5441400c00070306050700c0e6041e00300070501c207114441c05c0300031010075a1301502d024079014100210040007000c00400c2c014040c00040920410b83d203070710394152410440c0300b030884020354910200580f6a580300c4000400842c0856106018100b2524008000d110311000700d01000400400c1006001864458000164101d48030307030806070803c0c2c406040060301c40101094481984001c88030b0b00c01507034594ac14085400585074240002345040e203840850309040019501200042071042e01ca001d0f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 999449325 1250 999448075 999448081
    0x2071a061f020f03031e0a0603120302030a0b0409120e010309170c0a0816140303072309060c031206031b010309060e0d02010b09060303120a180f0b040b07050c15 71
    0x8000c020f03442c40102c40380b0480e610b915201000c07a992010700c440c101059201078001c20a80e15a901420f01a0b95003c406000c9460503000218000c1d0002060f00c104c030f0340c90b03015a0703500303403130350300c213001e08940211100039a0000021001e099011614541e1781050325005030300c001308642000c0700c21105400240c1a90700c4000012103440c05610100c041c09a00c7c0c00240d4448000c1c1001911251341d200300c0b0a00c03c0500c80700320540c0ca9002c1120300c840030aa0b51800d54100c050f0a50300c841c0c0c0c030030100044909100340e01c0080707621508460542d04299000142e180d81c2030803075010007980480220001e00904100b112a41030038812007091505164580700343c3c504100d46d40e007060820702d404404647c5405440b9a000b03018000f2180c0990280d01c0c80b40200c1d80e1810084100c07040700714410148802610b440e20150000c000c07800b81c100c0181c442a2080c00003070710400220750380d10301030080303000713181028140440c040300f010b0260024010208100004820080342d0107100d100e903468800f005036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 999450575 1250 999449325 999449327
    0x201051005031005270606010e0d1a0a06080114060a0f081002030903190e150a0507080c12210109053303060106051308061e0705091302071a061f 64
    0x4002c003a940c0540110201702d10303803a070005145840b41c1402da13980201d494a040070b001c044c14035444003030040090450f4800301030a0101c0c800c2d4200005080004003113655440301821120008a01180c6521000905c00b640c40d0100e004000b600d03a4141070744809103840c0c14103903680900e9940c411180c1d000303c0000d42c0010113105580d0b00040c01c541031078030a0b4101d00c00524502244a909128213144900e20f01c0804903441540c207070300c401c0d44980b07180010701e4840b200c090700012218845407240342c1e482400c2c1c58140014002c86100d0900c41c0300c1c0800741e030120426003a1305030003241d0501d1514040099141c0c06841282d0f42484520240110140440110b0940880468015010301c202d070000540554048001d12026039200f103800c0d1204d0b15014201d403030b12002d41d02060301d168200c60124a41c45d00c1040343e0303000b000030305200d45042c8000e03001c114250b20051047c2c01c450340c08180c180900000c6400351003800d0700030724106410301c0c01c4c80004102c00c028110340f5071000349200b2504911 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 999451825 1250 999450575 999450601
    0x20a15021207030506030613030f0c0228080f0f1b03100c203c060901020714062403030f07140d0503010e04030318021905010201051005031005 63
    0x42061007400054a00d09210090050141560754078043c1c85400001b4064414101c2580f001544c9603513000600c00d00c003203084500105035001030340d01c45034028910100b0300d079100040001070740340d094161030b40f490850200e0902c1071401c1c1420480d049001ba12590300b401245024092405038100f0001502ea440420702e0071000301040d4030300f103161a1000300e900d60808481c45509180a0889031004c0c10514070f01c0d03e03002c4c0c40001c222458101c00e000d50403034180452148011409066100c009480526002e150140070340d0b01113144c0e5800107014040c0410600f10403602011403000741003e0524000040c070119500b910f500e141d5502404038511640e0a108803001c460b02126142e4450301c0c88c0c14000400314001c03510040758881c1d0501d04110a0003203054030304a4019070300441581d55103071410b4010700a40c03104445480015440d280c010380d144a4080d2680015540507a002030805001a085400107021114408240c00f02086155000074812000107141c14000c585611800d21142d81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 999453075 1250 999451825 999451837
    0x10050703060e0a05061c08040e0a0221191e09051218040c030c0203032215140c04050a0603090501181407090207020901030b0403200f0106050f01020a1502 68
    0x121803202c00344042d22016811842c001d5000310b6400c10303043e5411080d1000300f102c0a02c0104011303810f10040210344980c50301a0b078010315907000585003401e8000000c1c029101d110b5000a000c90500a1000c20940740410b5200380f4160030302002481d8030985010b07502000808221101a11108a9410806d05022b14180800c2070344038140c903081c0f40b00800f6103c06580820030b0146142c6805503524610038040d001c080385094000c1c602d1525048425800c0b42d0f502030150743d01e18800404080015102c00710b66000c9a42900005800c03071040d10b000050b804064403a1290349820700081c0055030340c40c0c0001044a8907401e002a5900716450301e240034040f00413141d01d405114000741800e01c03a100301c000789150404004d0b540f1140d200d060340c1e4202d006500029402c481d41c0001400001d440000060304607019003890414005100307542d800c03c0006210545064101308545183e04c42d09010f503201420049a455000d1240240000d5880115a030003a01d0010038542406082d0129811246 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 999454325 1250 999453075 999453089
    0x10e04032309040e19030c050a0c090f0e0c03060c0a021002070c0305060f070905060703110a0c140609100f050715021c020315010f030b030109060912111005070306 72
    0x7a080340000c9000800d03811001100e80294100850080f80c0500860984012056207003403203586501510211101503081001300c03482d10605100c1c5002c02e10490300c500c0184560580400d084040d80d140800392a040380e601006503001809801180d6408960140e110541318517031520b94940340700891030300000c940e408061520020f1075506100400c40b608003541d028034115981500c8030310550906d6a02142c2c078100161804c80300f4032103440c00f01c0040806a0091a120150380c4012107070904000c034981040ba04083d000400700f281c14107801444491250440e0341750304203000b080100700c1c03c005400260b8104420740008040c1d0900407026140c3c803d8102c0d03819a03203503008190b440f00079401400d1040c90b0341010100f00718000c9181c000c40703100ea41d110039600f502d41602d20064442219480b42d96090545030300071070640b618244100328029008071004100f140c00ca0800000d04400806418100f181300c000d41680441c000454452000c5007003000503141c0c0d03039040100d00070400d40d04014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 999455575 1250 999454325 999454367
    0x1a07060b4908130e070212090f030607112406060705070305061906050616110105040909050610060f020a0b060d06090302010c0909021608070611040308032508010e0403 74
    0x284a90740000e0002840242442d0340c0f0291100c15910f842ca10481d852801680b00303e58840c2c100c211130005d000c4d902e0f00a0500b0440c031001a00080c20650201c50300c0d00010034480300107103598020072114045158915940140711052441003c4420300101124003031070000909404114082040c00700440e00b00301690414240b031405003c20447d544411041c3d1428421b0200740ca103040402c841c0c85002600036038012030354035a1414071220b00314180c00d0611005000004038000a03000758040c09100340003500311440e09015150f025101900300d0010480c180440290240d000160b014181c1e0700311000381c40960300c18001440081a4450083c403441c03d08400c0003c041c1c054004c03110b0801680c5400c2c10103a15904000f0484c080c2c0000011460011072401e00401d00100c020b1001c14042c0d180071881c0c11001c070b2003025076070256008585680307001041000c180300003403807010030003403ca42c00341d11b43c1d840400040141034180109903c01c034414022408040c001d81d00414004c5240000f1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 999456825 1250 999455575 999455719
    0x13030209042d0b0702070e1306060f0b07050f06150913050d051216210e030408030901200a11032d150115080c041a07060b 54
    0xb06007200000740c07044440000303500106980c0f500201c1d0950642e01c01c94040c501603074880c00c031104000d25001007921540d95450010a90030055200d40016101440d4069626412443c0191902c2260303406441a034110800341300d00d4410b8a6003a0407202c0d022a05030312143c40d16180309000e6a031500c8000c0c045c0c403540c02c44800c0e81341c201025210301001004890000d540310382d4000c068500d808000400030b034101c02c00900c0d10081c0645428400d011180024075140d21b90081803441e0320640207440c41d68004205c3e02900d6900c1003100070200035440c3c09442c7d000040c0c06c02543c0e80100000100040000c0800101c00d840420600442c65010081900d55400c04c0fa0981b4107020301803c0240540603500c01101d518004010850480b001c150b99140ca00c42c2c46032048801104c040c14100c6803a80402000070b1542c0d004035940c0c241629001459030700d030007519001381260304180c6114000e4500007107401c2c02c814690540d04d06030708004850020680b10003d0104c141e506440302081c111200450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 999458075 1250 999456825 999456893
    0xd140304081603170a0c031803050601030f05061303020d140f12010603050a09050c190b1206010207240315090e0106090507030603020306010b090612070509151303020904 75
    0x404100c0b4051010301494604070103c1034002d125070003010010445065403040044c0c07042600b48d06800c05003007610320b119225541c51f42081020391090300c051741340c40524411710809201c107507000f0f5101e24400d81c0402c00365401a441301308481040b01880340c15000045800100d0317044407081c440e030741c100b0f82e0313114849005065000c8081c040c16000a142a00154410041e440b4100e1025000001452010b207404100890340d1698800e281d042100010001400361002c4068040c080006025183e075141000009140074200da0000c9c0c0381c0903c1010104042d11034075028600480c00349408100c1a440cd4103c00400c00103611a90950b4a070115007a01c3c5078065110106440c503041d401d00c21512503c104900780c44013404040c0d85500001d00422078000707140c0040050f082301070203150802d034138200005003c210443e074003000f08400003031f03442540c0350284050071074034000c150b02401d0076104042c0301c48041041c000240a04030b002d0101e81440309c1c0c48210a00c001044c96034108621041c0c1c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 999459325 1250 999458075 999458113
    0x349120507090e070201091a011d1005060729060105030c1608040f081002182101020d06060e09070f0c031215030c0815270a03050306130b0d14030408 66
    0x103844100403140e08103d80841c0188231412a20041d100f0064100d921314450721143e0058010068100071000016894a494010307100b4035001300c50582d0100c822170801e00c86030350301d04031200100c03441000304081030f80c00c44180c981060100841d00e80700c0e6075054412001404508024101c0c12010900165602d1a04000d20984100030241c614181c0c1e11b80980059020707070204440070f00f00c079517404002c60408803805182031038071104000416000410043c226031242c9680705540d91500710501105811001c541c0c40b0100589040145180c4480000d180402039600c842c20880801004411305200391261244204000410442c28100949608100005100464034240c1d0600e001804560228802c1074002e01c2c0902e2010580e100c0f03460f1008464102d864640c2a02806040000e92500300700e50f1382c266103c0e403209a500d0034440100b1100074a101c54004c002810070390307204030940360280310001450348603076400d90712500580c40e141140a03070b070401e10301c40c842c140b2044a103403d511 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 999460431 1106 999459325 999459341
    0xc0906030a0b0c030a29150c0304080f010605060f190c0605130b060a060212070303020f0d0506150c1b0349120507090e070201 56
    0x5910074405041c02e480c41e1600d981d020040100d0801d45200c4c5100319000d00d002c1c0603d04401c001c0003103200d001c60110074018400c2c80d01c1200c0d60307d880c2c0282d45240d0285800e070b03502d442d12824071b1a500d1458050004903503003040000592414a18111582071094404040c5000c08030201030340c0c910f801c40c41000402c00c943c060030b000b140c00d40c03190501861034000d256424025500342021180c1004d08058840c1c610b1b40010080c03543c00080d8080b40c1d01802c07080540b40c18040c201a40203004281100071900c0c00020803400d0050313550700c40b600c1040c00f101c400090071003481ca0082c0c28003030850f032074219500441c1400405d010501d41c0c20003c51008040b1400032860f8400c2d120010b402501740c0b003040b217403c11840e042c1c10100105440540c02003e9100700096208030003082c0c42000405840306030355410120710050302c0303039050034040c20b002c690900703c9040a00e8020300811140b = true := by decide +kernel

theorem cover : BRFrame.Cov 999280575 999460431 := by
  have h0 := BRFrame.cov_init 999280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 999280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 999280575 ≤ n) (h2 : n < 999460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
