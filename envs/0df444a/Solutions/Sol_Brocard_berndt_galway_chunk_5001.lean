-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:32.073652+00:00
-- url     : https://prove2.me/submissions/22f6df1c-b718-4011-bea8-3c0f28883726

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899280575 ≤ n < 899460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 899281825 1250 899280575 899280587
    0x110f0315040e0d09090b0909151306180201030c11071202063f22030c150f0b040c02070b0325080601030e0106050112090204020c0d030504120203030f06060307 70
    0x1240780b0400c403400e400307805201820b42811409586000c0b070504100618030300f0030220b0301d80249011402898135002d164000d21003d440030300501002020343c2003510125050740a09003100c80100302c03c8040d101c0500c009030450b0b6004103008148292480c0d0901c00034004185041141d10840c250101440705100007041071240440c800040c05480120100c1284a40039005c49400d43c61082c607103080030040500c2030311004544c60302081c03403c0010f1300da1001d00e01220f084c4151003400d0460324160541e41e80c1d400900740441c151803060381c80400d10512480c50250365010740c0c0a503010441d039400f50707400941ba10118050a040b03a00000b020400c003945460b11081155a201c9640540c58441d550090400c101510014002410840c203600b0340541885140d08440d016190981500404151600a000da45505a80c040d070309000044088000303022003c8104101da0b80081d8518040c030304110403904101d001c800f198030910800c440807140600a540000003158055101d503240e460448403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 899283075 1250 899281825 899281841
    0x10504051c02030d060807080d031413080904060306022d0403081b0f1e0628060b0d0c02240a0f0f090f05010c020a050a0f03032d110f031504 62
    0x10a840c2c20300009501b40e02041ca402965000020b45480700d0101170100c1c141c900c3c588141000111010108d801e030f40e0f00c000120303e0907201d255998280b4100c8000074048425580c415a045500007612000b1807451048003030843d0071231440e5850b18040d0b0000c0c0c87c030a002d5400010003040000a01807880d00c02421400942004036080ba0075043c1d8045103182c0300e0618420784c044e20074142e8030f0703a03012810206003a442242032041007900b6419601f045000d01c1c81400001c0d44032680c074200440c071030390140010007455005144c003041c40311105400915101a2050340e103400c01c40310401010b5080883d1480d40c201020300804566030b00003800c0c1030010080d07402d01d00c603402e180c20050030800c10b08480e50007045008000801102880c9001030380c5500c0e0301d200003400c0e074100f03441500000e4040110a40400d000e481e0015100d086003041080c10700310b00403804c065aa00b118032512038006809400c06524001c04010b0a000650004e8481404080e051004a0010981c208543d03100c0d0307840f03102 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 899284325 1250 899283075 899283097
    0x60405010602070807180b0a14030601050f0f1005090301060806040b010902070c090209061603021b0604060203070204020f0c0d020a05010e070b07023109061b050a080a15030c06020f010504051c0203 87
    0x3d51907550b10b81030303042840e90027024001d009038000012245844440b482c050300e4060078507e10300341580100001d8040601d18001841014001080d190f1803d00c2440c01806080c4014034190034242400300d80004143e000010035401045100300081c0c1c65050541162070104000d40c440b002200050f1460103000d01d403481c92040402e42c03006265000512440d2a00c9011507480100c0c00542071040030f21039400303840050b0b0b0042204078010300b001e500402e01d2054210fa00d500305030302c0c08101420280041c80100040c0c4c000c0740c07140c6c103001c000e02c125602e200c10400103150881c6406148002030107120b60181c0708071504041c0202c0070234200020102e070484180e035048034800541414000300100b070001c0da03000f0b140910243c000445640071007040c0005444c0c2c0380c2400d40c116811144043c009100d80710941d15008000310405400906501951152004803412410b040c4028a4540090050205a0704107414000407070404500c04910300200500f001d510903108070282d00e5032140d9100c410b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 899285575 1250 899284325 899284339
    0x30a0b07170f01060e0a08060c220b0a0f090e0f04080705010f0203010617090304030809061201030f02040f051009020f090d063c02130803030f060405010602070807180b 74
    0x320790000b503402141a54a0b40e240c50031042003910512800307030a03a0040400d07581c88007002c50307190b2103804050000006ca403413a410000c141c0251a0390903510350ba20070486d14601203118001a034100030f81c85404005440c0240f00103180036001181e03c0d001820400c0c01c01c400e003000c14140217140c0211140b04e41c0040081c4094045008410001d610910075240010040655046041c0528403003e0095150703100440c141070454a5014031680100d103801c2d40103004001308140e4903449441c43d4000e41c0515031400400103c1e0041c001038a401c88541f00d407140c42e02080201070f1012900d0002a122103090041c2ca82900d0440c0c40201d02c1a1500540d109031040c2c07202082103a01d4115000c80c0f01c200c02c840d0b082008a20311001c0742d0411184182c5503070242d280800901c14154094101c65102c0310f04085107595400055055500594031120702070080c0d070800180342081c5c01072500606041c4003c08210f0700c1c101703000780c9460780d0307010300d4110101c02c42e0010301030080d03904000d504407401002c103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 899286825 1250 899285575 899285581
    0xc070602031008070801060b25120801050a050603240a12051f05100b0703090302090a2a0203160c030206031305011104050a12060f0509030903010f020702030a0b0717 73
    0x44296040300f480380741070740e1240100104100b4410300900701141c0d007141c1c03464100885130581b500c080c2006008110300d41100381d04100411252401c0c00703e011072948542d141941084240071074400213402ca1030044408006110201198130040100382003840c03252850b504006000070315410041d8402042c41040c0740104090050120315a0356204203d8184d251101c0409030500a903a400c440050030b034001a401040183c01100082031030314420b150542105880c1c0d40010322030304081e07800c4410b042d40d500011440540914a003440d02c0004410840a00e480034002942d038461a20600c0603145494400c2c4208102c40300642c000e0755004100e90384a00e00940c2ca200b02c0021a48161495800c01c086500c040c00c60320210380545070040c000c04062802c00c0b6843c0d440b00d0651780101c684e2035030b824840ca10000c00340300380360141d070209010b195621030b040c00301400d440c1208812100c3c1441080403a006030b400107000404158400c51148c01551800f1003034490010f40188088407005071010 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 899288075 1250 899286825 899286841
    0xd05120a0b180c0d1514100207080d35070309080705010207030309020118151d0307080d0f02070b160305160b071b0b0109020f2b1805030d050c07060203 67
    0x107450084402c900400c2140c5c0c01c0c0c1301d50340c88050a8800e0340b03022000d40e01420001d042201c0c50131a150b8403801103e00584d900c40e401403521600c030151400040da40c4024400104904120300c211285003000b15a041000841103581e140001c0c001c802415036411f58101002040320640300c500d0b4128000319200c014504001d009015034401c22400503820800c01c010503444900228155001100c41107500c03000c100003030703a260041d89003000340d1170890a2041180d40e010407104c0c024005240140210710b03041e0b680a454001c04007156000e640100c034081c8040c1c0310303001c1aa11507194420380107485807080d060075a15840380c03060041c1342c925660000003e02169007400b60280c4c40584c3c07540309034001041d507082d401615817001802140039200400c0b0340010b81c0c000d006042d040f58030840c81c000d420568800e64400302424180340c20603030019000c840455100d0000c00e41400c0720130b0012815141d513180d8481c49881c1021110560b908081030b1f036656400103a984070f80e4404400c41d90390030040c1c2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 899289325 1250 899288075 899288077
    0x3150a031a010b0307020604060f0204030501230108070501080c07080c070f0f09021819270b0d05070306050705161109072105090a0218090d05120a0b180c 68
    0x2903400c1007641590000119030494008491003a010f6901030462038445d542c908001e0040d442c24082001e03000d01000c004100d00b031144400038241c08000c202d140624000401344050164400041070b00b19207410070099801400450b4000800c034105640c543ca107150003891409515021a401d2094400c0494508550402e500a90718001c404414081c1c2c0c40c00d851050740b00f00d04c04503400410390003640c3c60318100b66085100d425140d0110751003040e00e50000504000a001c5141c031101380da00301d041c0301c5124621070215810b2003510740001122541d2130702c0d035890310720b4071000740801d94407070001d0ba02c0c41c441c005854001180340b240450905840c1800381000140765040c9200e8044500030540143c01080301030416030303041880040d41f4655007068402090002d11000590044801813070050759465044441e10748072140b40c55050424001103803a00418406800078803d041210038030070800c8503840e80c2d0044e0f140342c2c08610030030400003050319800858081007640e56038001b0704c80c0300380ba110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 899290575 1250 899289325 899289353
    0x60301060e300a1b06050909090f06090a1e030203040302060a12060b0c0607080103031b08040902030408041a040e041e02032a010804020916052101030201120e060a0203150a03 77
    0x1140741c451210311398070900200925407160a0105004000b00a03050078036000c0135500c9a40d03007054528645440e41e249061800c01c0359844500d0308004503180411000d4107003010100c05843c0408104981554080e41e40d2140d4040640f042c0008074040700e100740300b145402141a510802400b00a542c0e00414a254000c00d00704030260240800080280b4810601c45049030f805548004c20380889000c001c4110300f20010980d0054020400801c0b8101d481c00114061407160b0409a52030b442d1a040c0c8860b64001c040c00c0c254000c00b00001c1004044000b51650810f411002c1d581070b042900610701041202404025014010b403880c0705030040703c085010740c11030101c40038030700c0382020a07004603035100084030020751120039207001c03580b2130410b8400e000d0540c845003000d41c905221514407401d864100440204180f416600500855a21143c0784103034000001c01401100c040c00d46464440c6030042c1440176550f030201c0003d5581c070982c105041d0b241c1000d41411409610390418104085801e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 899291825 1250 899290575 899290583
    0xf0b0106080705030720120310030b0702030a021f1d0a12021f0c051c0906270611041d06040605030f030a05130e01080606010e060301060e300a 63
    0x5040010b40040c0907100301c901c12195039403041182c0560152524032994488032a1807079200d08030ba03502405101d1402140a40c00c514086034481d440c5140050100350020b00d05811900140b080d44e0042c3c0c0c0000d00303421100da61020100381091032003040300080148400c03800e402c0caa010300e08001050040f850103401806005c031300b034140420742020b0340c0d10070010b00035242c041201c681400039806158032403204a8001d14102d4500045118070304141c4015600c100c00d02543c41c540582000024825130200e101d140800260031881903421000401c2014005800c1d1034076110301040e4401090100c4020b020f0380011400401b0f003840e440b000d0aa4122101c0c0e0050780303813403004078a0b4070340002c0ea515002191002145040b00e1007000700c61540180d02004162a000100854441c9924511a001e040514010043c5140c258001064003d0720715605000c0e5030108014450103603c6900303c0040b9909603207541403d410442d080081c0c2d030030001000031a1005403202c80c8080d40114061503da401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 899293075 1250 899291825 899291837
    0x50c0a0e010e0a2c1807050301271a0a0c080606030421090b0d05040b1b0306010f1b0b010305100e030909060319030e0411040b070308130f0b0106 64
    0x280380041d55400c41900030306610098040c002c011620008030f010804154072840700d50700b072035100e1507141110f10541d0808802c00381204c40d01600d0070100920401800e08400034000b40b19100c60b0a04c00450000c0c00041c031140308242c0b10288080c422861131176101c000170a070100d04d01040324100805030744010500150420011130b04620308001a42d002e150004520803074640c4480842c000001c01030b8010092100d0ba01000441242010140860741c21020000c610303441c091034030401c580001003005450307017200200080300349089426070f0b070b1102c404c0c01c0c482030800141c20140ca150f59104204a14442405510002c0000718040c2d02c0c122413181c8100d41e102d85140741e010064501410038210031340d00c1032116000603e08203203295005140078080c0c691081c2c901c000c00c0b0164030014410350110387d0340840d40505080c544900d0042200c0700c031105050900700b044c803040c0d511521801400f04204140030a00ca86031464051240a6120481090103a82e41c47c0c6210300752801d10480c0c000c030341 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 899294325 1250 899293075 899293097
    0x8090c0f09070324061206080a0c0614040e0c0403050d080c16140d0314060402040f05101b051f0c0c021917030310050604061d13050c0a 60
    0x108101a54103509004203640402c0e515040c1c01c40080c01c548042c24259036291a2041010755200c0d1010080c0c4010368030521803d80c41030200003a42e140e644a07400e160b0040308810003003081c207000202034502c0c0386443c0800301e008240400780b47c01140c003c2041c0e4044003007808803005901c0010300032207114506540b03111415200950b81168204d0320182c04903070400500e00000300071004092620300c036807003240c1802030200c034942c900448402d1401c08a0f6032209141c0d010451010241d030b000c0c004450541c602400d0200002c2641c00d13500c02d040c000e0002501c1d10001074000c2d50740d01d4203030305544c111000030a8142061a0303100742002145460005941c403440b1020399038000c06070864226143d00850034015401d022941080400002c003803414448046001a203441c41002c8100480d8011900d904198410250340c40040e844548180820481007044540050040400034103900340c030f6548101d014082002d21445510101c0140c0c6400d04100c10191200058501e090480e901c0d984221 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 899295575 1250 899294325 899294329
    0x70501140a12240315111204020102030f0c10053601020c030f03040c09200702030c0a15021c0807111903051c140c130f031a0c0a050d1a0306040308090c 67
    0xc2e01111175500c1b0040030001c002803940b0190b031058100c0e10600c1101d140610010080550742c0190620410300d401c40d41c0e61a903840310074010280c01490041900d244510b20503d20b4100c8001d0700d0740c003011000c40b1701c11390078280340030743c1641c2000c0c51117015642c0d90322143e0b00b03000c0554400c4804172400c490a140105001d8450310807500ca1828102d001200d586903241c44c18540d42000b8000c80c1d15214a84a203d850344441420300002e04010558407403903514404080d0071314410301100200501907008501410380d01240064200c2e84900381250700d1034844480c14103200c503c000308010440c02409000415a00a0040a02480c000c183c400700301d100d0005d0034181c0f0382030300e54402d11424503030100d00e41400c4500140f28408030500c0120101d59510441c010641840e8403d6407156102010480407054154185038440c800642451508000d0100a407060003403c00200c80c041d6648908140e0301144184070804007002401c07152189401e240c014809131045803143e01c0ca004200000006d4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 899296825 1250 899295575 899295581
    0x303040503030f0a0908093003040503010609110d0903110a03050405010801081b060d091e1103030c061504230702010c030908040504050a061a0c070501140a12240315 73
    0x5660100c2407d00d40651002000341501c0a80200611421040111203000c41c9482d00e00d000c81c60944051038490340b03440c0130103013100c00c50b030310001c0070030308002852a007460841d080b6210f0140460700090020700381d0400f1581d18544919450080c0f04d200c00342000d241d004800f400440e5800da0382c500080e80c9511120351075980e80e03d180f502c0012245c4010040d0f20303248001d8014054a0280004c860006403103100c0c42d800c061640a02014060f0f2448052091041000c2030152043e002549864140d907541503840f9402000051018a110b007540207981d2250414804d000e000b10600800201552546520650990740c01000d986004003e0030054028098104082d80215502d820580741c002030202810000b0100d03240580d44e030001240512441f40311110100201a00319261840400b045280014070340109051141c0d8030381c1c49030302c0804002214038400252410b14108203400c0f280340c1c05021510100142030400c0c40441003690004425030013180d0060a401044915031f403900000c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 899298075 1250 899296825 899296841
    0x40f1419110a0303020312090f1608010b0f10030b0319030e0306010603060807090b0310060e011403010501050f0616062f0a09050d03170103060f050f070f110a050303040503030f0a 79
    0x50380081c4140d80d200120701c0b01345544040d030f1405803101c001d5427081c4141401c4c11003a01c128007038244030007800032140034814100402c170705480da59981070212000075242d48900303400c2000c0544840c00340c1c0050b1407c1c0139901140c0c0b48050400c207200458a40603060070f1113035140c00e000344200740000400034824041c080445034298003510005080030f0031032014110082d09140c151003226401c500c00c401a00c100f00003410144100195541007006c5d10003542c8102e01c040340f00707a04150048c00141d0ba0242d0390b640040d02102d4103a6034850510a10a5a0365940e202800c1303240741a8041004010300e010100102c546001e0002541954200f04405401590041e50001b80000c6007400a8141480210b40181c083c1c10040501a0010040d0300c0c00c11003600221009601d850701c03680c158040e401902d03000f1010b03203405005803400c106d0041c81c0148a041c80d00800c048070f04c10706510003040c090108403a4021050303036501c3c5414100541e0f25401601d102c1d044849800000b507000c8114856004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 899299325 1250 899298075 899298077
    0xd02031518060627060304060b0109090b0619030b1905030f0f060606130308160c050d110105130e040602030402030c030601031a180a05070303080a0b09040f1419110a0303 75
    0x82018413040c010240b9120001d0340112000c00769040c0039050340e03200007440c810380c4203200124103030032180001820000c4c1503000819003030806240000a03612442a281908201c003c0d10001e142403240c00c130003502c90b0303102094100c0004151800c5d10407099043d003080c0c0c0c909800b00d50f40d05c1000b840a03551074003101d0101d40307113400c100c001c1030151400d0001000c440400304032a100050b101d480300758181c3c0c0f02c040e008140f2a4040744613010881000c240d5001010102e94641c1540c0344c41d00c404040c654510480b50400000280c03880300441005034807409072005e14120015440c2c146800c0000754404c0d6010b038420b10420002750780314640001c03114140d0380d102841d01c041d804280410a02d210300a000228041c11420201c80720761b20070030030401740e180108024a40320303145041c0074115160107001300c414181003205c202e8140d02e5200303c464102d94000c801c059146580e040c5407850804240d824130041c010000d030844140103a190b0082d20a000381c0c000301e100b071181000c000040300c00f0701c8010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 899300575 1250 899299325 899299327
    0x11071101080c0c0316020f120604170c1504060e12031801090c0918021519080c070221010513110303122409010f0f05100504120303020d020315180606 66
    0x102c000c200e17041d40460300901c090681c3c51105101c500040c00d43c00c0da0700c040d0003964407003403c000500007204200340e49024050041840e145a20710034645800145402e144260303068000b0030304000032940960001c4407850300b43d824860040c91640041ea0050300e00c2c0343c20038101c0011508041042c8076030002d2039403029004404510300b8200380003030540c030030901480000a0740d800000d6280c4c034000d0460f040f0000b554a0f0303503c800c481c4482e0304500c0b441701001006110001c000c80c121140c802c07520030b950102d4198a0050359015450301d90a403154400956508000502060500c0d0400349120079102e003100c0c29000d2110340603d99280100c1900d4068400014007040790f604403016940e2401200c001119400500140422100c0c1401c0c3e209681d02c51307107500304124040a091410016103002c4a460000c0d00000200420b14080c9000b80c1582a9850303054000b01402030f41290421544054195100c6ca0f155500900c0048076410080c0108403c0d10042c0354105801b030150302c1504028011 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 899301825 1250 899300575 899300587
    0x60a02010f1121070c170421050613050f010e0f0f0105070905040902040902040615181217300f060a0b0306030f01050a02030a11040303080103110411071101080c0c03 73
    0x1070f8200c080900070406006011242c040814842419000c02202c0800c2e443d640b145072540100300e00c002e0b2556140d203010b40550348400140e010901a81110500b850021119024101a030030a02810340d8410250318000141024100105c3d003481c40700b100d0030640324182d000001c020300b61035044424100242c0751000501c03040c078190740a15080c40c000382000801e02404d5010400315861500003080c1c54440b46e000d5003500340d00440080e50008003070070b5241031a2a0190350720b80045810f02c010458041001f4180c1000c0140041e260924000340c1000003200b000804031262032081c55840350b59800c40307400101510a1183c406008003400ba00b044c840360b02d000e402c115a034101420b01545400b4400c94000f10402c01d01405002d04851880142c2d241040e00301241240c0040c48000d44c01c50050004002080c0c0216031241140d8200c03d618a0390740030300c00001c00801c91042c15505407540440c2410a00c400203041d1030300b41a00ba01c403d001900c23000441c0096028100c7c244169034010022 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 899303075 1250 899301825 899301877
    0x20a110f0706092c0c07051f05060a21050a0209130302120c0d0e0103110409050a050a090210120605090f090c03210c12070818060a09060e0f060a02010f11 68
    0xa25030141a64208500305106d41d5221818042c4480f284140d0100400038041003071010311a1030340000b002c88458200c2032400381c1c01f07a50800e0380c60045264402c001699000d1101c28410814084e500800c2c14200b464800e140d00c6090070081c2c4240c00510400710300c030040510050840781180b182900402543e0307a404c030111480020341c403070241050f45034000078911400c0300d406040035000403840802c051070100605d1007101e034003c04900343e00b0b042c5a0108051780b2888252004100c05150503031b00c0b030701e01c416910060101c41d8420340d0408003040c2003100290800700841c0c042c20703502095401600c1e00000305a50713680b006661010780c00303030001070480e441c0c90440100707201440ea4080d01c11070054801d002000b0b030429481a110314074002a511648001c0c81c01c022116041107461508001054000400c1d02505000c0c100c28814201615072090741c91400700007155000400c6103988a03a4040c00901918244c02c1e50b410481c2400c0c100d40c4038401a03030070360b84048500304200300e40100603d9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 899304325 1250 899303075 899303159
    0x1090312020a06061701151409090f0607110606030c0a0b1c1803020d03020a1709150903090a0803030c07060b0111151506160204020a110f070609 64
    0xc6510107622a81101d02c001502c0c902403200104145403910070302c5a040d8908070700351a910404072100854a00d0103004000c140319001c0489507095890000c5669030f017091900c0d00001101d401064800d0608021195034050001381408541c1001e650494482c03105065407071160300c00c026403000c61007d040c041c10311702e20054001c1407811007650190058501c0d01e0800c0320003110518070001085000e20050540400242c003c490040c901180350003560080240107264841c40c02c881c007800100810100c00303080107c850300000c22088600c80741080c0c07100f070356264440c000719400b480e5140c0c4001200303100842500d10640741c00c02c078107141075802c0c2d6a0728000c0c2507080b01141800015101c11a40400402a85099900d0046128107a060000c3d550754940005e400b01807086804001198040718420b8440e101c82c0c0d07040da009070301c819585406491041c0710700d401082601c50314100220360360700000c2c0c04013100c00035240ea0000c940c072882220540c80000601740090508813100d11100c5600d11 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 899305575 1250 899304325 899304353
    0x206150415030b061513031101120f0b0306010f0e0a050624070516030807030305150d0f020a050f0102031b1507051201081b13140702150c09010903 65
    0x6000240e15805600c1d50007403201ea642003554100b035140d007003000038200429410b42c020b143e20b10031414150002000c04c0990420f0000406941004030202d189900807044821008101c2405001001c481011400104450134180b0b2081c8071309000004d03103465042680f4180c560b21030071604107540344a031180c0644400f40a050f00299500c840401070071011000d0080c03c0c1807005401c0d82c816050800d0391030100c03501030641041c0d0441d502080010800400c851065900d414041041d40d200350740711014511109005d03410154100d07402e010400680e4a403030722284200d502c00f02241e11a424481c10401190130103015070300401a07036400945200e40c08070b12034004002c40b00800d1106124002030002559644086040401e10742200c2113402101d0f40980800c034000e01d40c900e0b100c040090000440e0602c030380152907911080082080d2500010300128850b040000e0500f02440c00a41e144480c2e4425a9191544408030300c4c4005010212442c0301e01c16510100340600319218440103601c10 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 899306825 1250 899305575 899305579
    0xd0b060d020a05120f0c09010f0e031b0909071208130305010f090210020d0206070e06091c05060705160308090109200a0503060c0a030e07120b010f0e07020615 70
    0x5100c8221050308038001400010350b99a0780e01d8580b0070b2040f840042c1500500091011644c0c541086140010081580d40c21002407030000d0014048590540d110344c940503059030103000354000e9070585042907080403034400055031500c8043c1d580d1071f00a0740b160103a001d80304030883e1600817a000b040e008000f4182c1110005070090700e03140d03641c0d602400c423400440500d80450300d82102c0804c3d45090340301c0310403014850001e041c0744003540400070748820b0010443e10034019502881c0c120b03a1900b20a030344031517401401700c90021150410100d4074004242c8115410310850380028413007445a42034880c9010b0744102c452000311075035420f40c0d04001c0201076041c150750b81c2e0b4000300410208000c0400c210503000c0c16503101e4550724103200c030300c140540181d40070f035104105201d43c1c4100d80044035840aa5407400040001894601904001e2540d0000442c659202205d5052105084140d03040301c40c5000715220441d559011140e5404007101c156000d038003e4800128403403600c801d40c0b10f0410700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 899308075 1250 899306825 899306827
    0x130c051201030c050343121a01050609220e030304061b0912030c02041103150a0602120301050409020f0901080309241603140f070b0708012103170901050402180c0d0b06 74
    0x41f1000a01260b200240984141144140c0710018580d204281800b510b030680710b042c6000c0340030307012030081d00c50001c02000c848020072080051128944c011000030702081d003031340c3d0703039003014103016001c0c0c01c0c03110401c600d10954a50444042d80151200ea0032110f1110100103c1f00940e1010303030b829800c0e030005907000340d00c1c0c081032521121070000461081e0300700c2d00501c51040c80d24041c455590f18a40200065611202d02034104071024010b59044403011203002c41e40000728030100d04428030402445400031142400840d0100000c00903000b41341007956000000c044d221100c0b02520460714410381d504504000310301030b0300664400c840005000381001e10385c011049054030b8969200c1081a254100301180b40c00030410a01c0481d03411060300e281002d01541010800d81c4825102034041502c0e14400e00132004040c00b40104207010701600c60300f9803807441c10804060182038122404c078810341d5407035882800341c00c0388640c0c1c0b8000c155014009041401132082000100399020b4440d80c0690 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 899309325 1250 899308075 899308079
    0xa06050a0f09060e1b010c23030f04061b03141e0409020405090105040615110c04090b19050903040504020702040b090705042102130c051201030c050343 67
    0x1145000b0311825612440d0f00254004110100c20f007880c100004180c0c0102202001020303d80e809014841080d405c03900000450f030f01034080740701055521080f00c600e400003107080440300296401a1003140ca0503140c0301112205183c0d01c000c1504103440080105901c400c1098601c150440904401e0030510403050b40565035061211311500241d2101d041c064000a082c00a418140102401400c05860500806090544207144030340d111240008200d40306440e030445510402c0f102c0c071130542c0500200449609410002a06541107410f903412603d01110320320321401c00e2080500c50702060019604080c01d02003040065445840c059034410344402c0c0e02c1d00b141c2c2e2812040e0740070b90401d490f03503961241b920f95041c110341000303128030001c0d00e41e03144084003603224004c0e602c42195525070005004500940d041d0752034040e5400b46082d03400f1403800030040240c142c1c03c2e0019102c045040340c03004c640c0c00341c0401050501201701441e42a4514030400040d1240350315018040818201c0c032314140e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 899310575 1250 899309325 899309351
    0xf030c060e070803031b0309030904150b12040b060f1011030f0d050f0c130504090f0501021318020c070e090f030c071811120604110f120a05010302030a06050a 70
    0x28103800c400c00f50f40000040c00ba41c0d00e0601d119880174003c0c4c0c00154114074012159549901509406900035601d030510b040d90040c00e0f000200190246001b02a11001481d1041c20300c680210344c101e81d800c00c0340c0040b41a46c9062905518a000b0040c40f4403501d0117102001c07030711a00c80300c0304c45030144070500103c640e620a001c050102d4501400300000c0e0b500d44031144010b00c4001a00003400707542d0030841001080c400703000200c02d450080d100481c0c000d030240390031040c1c600d6151019005500c0071501e0318008180415500440311201c681000031a500c10219049125440d1290038550224404000c4100608041d035880009942038804d080340b4000c1490566200841c01c4e00a81c003c2402404580c00c141c40035511811404001c210380340c01e5421680951242125240d5000340c18400103011b940da5400004d928420800c00580707820010400d03d15541110000d0819941030b5000261540d40e1849040d04172030b0010020a414a02c81e290317480201009080300c136070903490340d000c00d87d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 899311825 1250 899310575 899310583
    0x91e0a08100e070e04030801090b060412031d09160e0409060606021c080c040501051810051e0c0304050607030e040c0c230c10020a061409070609030f030c060e 70
    0x101000c1c41c00881d601d401241e01c5800d00950703401402140708100140008aa805900b26042d1a120800050001c031014009401c0c0c0c02240d020041e0100070103110010140d000311032202402d52001804090b070310b10b0301003010304413086806505001c0d0141c004c611442c41010142004180175000081009403504c44200f900d01c1070700400056400003180c000e02c10090349410000d1030f140e10702480c55050800705015244030750320a49d4100000841c1081c2d241c0044900381080a0300189002d103103c0c500c281c00790013038100c00e60180000c2c070000e801140c5000c800c0c04550040d40840e01031403400b800c000410225800c4204150100241403044000300d40341c9110341020400c068a800c3d034513625030f1078030271030301d003180400500c0c10101005412124400060841c4000c2011240d03402d000b000324108a180c076018402c0680440d044c0321b1900c01c403010811441380144548416550041d48501003500e08089c0e912008100301e05520345c610106e40f14000098a0921070340c80881c00ba02c5400d42203242c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 899313075 1250 899311825 899311843
    0x1e0604090203010f030506091f0504021f0f030b0a15030903140a030b091e01030b06010302130e0603070b0a09050904081b0d0e010c05030d0225030f0f0302091e0a08 72
    0x13144082810038814400100111540100603078001c03c482060051800150302101441c0c030800c5890780c0c04242151344050b1032900d2507504104801201003a440020701d082c1402040c1400320f89003900942c0c2c0e504008450005a80c206201c1142000312400224000c110052041d400c10080243d02c01c03480701c00c140107007400903c56a02141c4103007040d04014805c18080c0c0f12a800c0303070340301c410400d00c0301ca0541e81c141101d0300021165241da6a59005034043c1c481c8a00341d2a40a05000d000b290700b440003080b86016510035811203a0468503410703106078911503030382c0e00c00c04038072109020041c038a080313402260301c03038441ea00280c02d0a28440b013421103c41400c420240070f42022510800040e0310000420601009183c140003400191b00d9080d00e0b4450b182030b591141c0d4000504800300203040140c8940344041d1003491006110702e0600030b000c020940d4288002409030341c019019030344a4001d40301d00000c01001ca541e02d1107482004540c469031076225a400c40f0302000d0000300d1060038085120 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 899314325 1250 899313075 899313089
    0xe0d0f0201051e07030f0b0303040f030b070c031d030a021005030414010203150f030f191203020414010309050a060218090108060106200a0203071814061e060409020301 74
    0x152452044000e42580d40040c540389040c200310902c0040021995503454001c2e4850400080c4032804004010241400c180701c26054800041c0008100030b160881e03000b01d900030000031104e92103c080481344451803007409000501030104603004521803550995074601c0003012100015425804a081c2080001e44070000c56004402c001c148101e06c2800c0d403024400720700031403552074089070f45484590b2591f0a00d0080c0b0510000f404030b601c04000c1c1030303040184030341200c8410700d400941268000c24142d003120032440a50a880c081c078001d000b80c0d0256000e03070756694407000b10703000114024075480500360740030305c00d4403010b1021407600e10041941c2c96451160140502010050085691042c0e20200c5954800700042100580c00307600b00144c00307114a00e01030000c074a076000340d02c1c1c910807c1d40179500d4000d0140000c1c100d150040a0000c040d1b66001c103001c41c51881100070046801110059000f003602c10700809000000c0500342c0d410f450007001c042c10b1a0308c0c0c480e000c04a0300260880c2c1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 899315575 1250 899314325 899314337
    0x60302040e09070303091413021207260403050a0201090c09061e050d0303050c0f0c010f050112211b1b050d170d11070b0a060602030a02070e0702010e0d 67
    0x48080c41c8036940042d4072a05010003420345501e50394000740b07000100c0c810780e044454106e01c10601a6910b440c105003000010b40c00b55146c050350750f240d042c407100a54074800854010843c0d0040349183c50035000c100d41402c036800205640d103890540f00e50740300616403c215581c0d54201340029441c90a07110141601d81c000082c890704101d590311103c2042c0524200c401c5241030204420360314481c1d0030048561518001c9610344034281c0c10140f41c05490f074058840300020540c2d2108110540c80042e0512003c82c0c1482180d80c2c56903a41040c02c10850098103d92001c844c040c090300c60700d052401c001503d40b501c03201c030000a01c00b804c4009826001103039448002c100e548001ca07820b030540d0740580001c42c4e464041c0e03441e40d0765081495922001075010307a0390105007542c0e5142e10390b00c2820794450040398140d84038032a150241c18007004484c14602c107890001c01061191000082c0c170140c0b0b200e5001030003141d0402c41003003240d02006180c58110741d02e1b070a0040c030705035090040c0d1700300c000161611 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 899316825 1250 899315575 899315579
    0x1e0b090709270305040e0403030b01030f05060d02360a110408100f0b090c0c121c020c0c0d0f030e0102030304031e09030618020111031603081005040606030204 70
    0x51420001240d001c400024148a018207a10942c0000305880a140014008207042c00349802e5845005961100c0190000b6204000a064164000c5103111100340e8040050300003119010081f1340d41507031a5904605550150030041c2844500b400710f4144500908514070031040b0b9440700c66522150359a180744448040c0140340200b0b01901c5140580101a0340c1031038101404242c0e0b9043d45440c4412050b1903814410041806070701c80d001402c00034002c1d140510708444a482d003603002420100d80303445118407010014815600b40e07034a03004000f4000800c3c100820100000e9000300d80100101e02130b0b00f1558800e50350b00c41c5900141031080c5602c0c0342502035800c0280201580d0b152076810354008004010000390300c90900c004840d44031900141044000c0821035250760b0f02d40008154500d00b080054420540d00d0082c1a118400da842e40710a01c00c0c0c80b1070035107902588004612304205044404d0020380100f07196580300c040005444a40750b43d401c00242901c1c1c1039800180460790019007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 899318075 1250 899316825 899316841
    0x10110105090f1c02060f0408130b0304050d0801060813020f030109060504020108011d13050322140103090b042d080d0b031c050c0a150b0315130f1e0b 66
    0x807200e640314103c0e641110500c00312001949409000f0040909250250001400c1107148d500b5103040d0103a03602180c4416850721800e01050b40305440c00d5078a880f07400d00c44001588148011416100150b0700c0420b1031f11072130800680c05400c3d000403a4010a040440a0709840074070513210858060072000c14241131500000d052102c040c0c0040407141c0300e19164084030714109030150b4021b255a03828170800e042a040c03050943c09480c6040644048181c4a480d64007414142007080e2421403d00c001c181400c0c200540441d620701c1c000900292102e4005408940c407681e805940507106401a00034420980b03e040352680704401c12188801d002c02c4079101804030b841212040e540943c000e080803403614803105207202e001e4014504000000a002c0601e0b401070110504866110104031641c0b5000c80e010340180c10221a0903002e0302c1040c0c01005400e04298881d1301038001d003488030150043c03645800f00350006001d001d60b00310700c01404043c00ba00401041110803402003070261101d04040755 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 899319325 1250 899318075 899318083
    0x15030a06020306210307171902070501080c04081c02120d021314130b0a0b0c0312070f0f0c0c05090109020d0e01020310061d0303030712050a14010510110105090f 71
    0x6814240c00c0e0101030005a01c130000401c0f1031045070022003031080713240c0b0403814070454401c01c5034011100558280c105081c5030009108010354000340c03030700c09882d55081c1c0407820300d01540c4508103107544004103440c8100d507019000200d104041c4190740c49410511940700490340141001a00540d0000350000b03d800006032074806407440c0310f00341503c070b2103010002d002a40b1004c0155034a075036400f04912a943e5038540daa0050102da006c0300c1e114258203090540b6030b005280840c032420440c400040301d0034414411083c01500c2c1da10742c400c04084001045409410b401002c8455802d107080118950f07450a0b000d6008200200c40540d98840031441c140c00d9400e85080c985980e801441440b40038100991a0b0058074181d180c5000f47c8102a04290b4107003216038155a050300000044c402c813283e100c002e8281005035410140a29110071080004480001e40031b00e514a00100046c003403403800c0c1050b445205a130703240100c040f80001c0c50242c211082500ca6003801d9021440324440800180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 899320575 1250 899319325 899319349
    0x11107082a0316061206080d020a03090e060904030f020309040609091b272c06010b04060f031a1002010203010f090204050f04051305190b0f1e15030a06020306 70
    0x10300a004040f00418844070030010354054102402001504002c01c030a40c2d41c0404000c5c420501181c82901000c00069252a010401580060040c0001148105c646440c150203194003602c084080d80d101d45003150b00d41a00f40200d0f0840c0400c00c8080c0320743d80c86000d25000740c00308801c0040d4803035083c505007100d2511046424040c0813818000c2040c000e0001e40c1040002c0d0000f40d000c21104010300c1c4500030b001e01c03080135110b040e0300100745a046a0020952035001b80c0c5404460907a62920003014182c01180300d00030000d2080d40340080114403d0704440c00004001031222110070103440012070741d4459400c1100103070760100c0100001c40c1c139007140800414900c8011480e10741032002142403951842c0a02c0e02030340d01e5002058411020443d55800e0380d07080300550302c1d100001800b4001d0254901c10039201003284401250050303c0c00c091940c000c0003414000211258813043c143c02c6180000c10140c034500b2403180c00405501c003409030034046403007004016900c2c0740460802c0300394401e0f0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 899321825 1250 899320575 899320579
    0x40302060621070302191a04080d090b090439020105161b0219080714040e06071805030d110d02010603020a0e131202010e0c0402031302011107082a 65
    0x40038510b0b9000d0003c00d002003138903015102d088490159074010b03420541c080d486001c2081c07040b011b03411041d00c550042c0044d034807010144c5186000e0720ba002c403135008041c041c12481000c1008500c2c02c0345015486010030000508a0010801c204007d1829540ae215007a4030514071180640c10026030a101c3d09902c0720400501d90b080040a04005149100841420502402c00400c1d807065607a10f113651210340c40400c2503043c8194548480355113581d00c40c860181c00c000b141a80b0f41d46071509016080807019454000d080c0c131351b01e0842c120343d640700541d03010640e42e0000700d011840c0d450a0141c032200140035140e1844c0f6a24401001e46449000c0340703180116450423006000595031400c0100403545040c00c0c6c101186c0340d8100074050144841402010b030685004130843c1e03241c06402610384020040182c6480410071000c1c13105901c000c496940c01c0c0307180e1000c410300540c0902e00e4076035680c0d540d10845031029100d0090f51b1920f66070f040b18806800d04030b40b00c4a0710741c5c1803072030320f60f0b0782441 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 899323075 1250 899321825 899321869
    0x602060601030b1203040509041505070c03081005090a0f060b03070207030b090a0b180f07090b1e150c030706020703030b0907090305030405210709050130120207030b0403020606 78
    0x404c240103880e4019400b440384038010f9030011800344203c1450307003e600707401020100700c82d0500c00c002820444000c1c0c0210003180e80080092142c00c0300507004c03000c4840140800056541d0410b00d9001011628050b210726541e645000c2011020080614400c0d00c4680061080e076007036041160100100404911407030b841880041c0010f0740c410070300398100780c4011074914125114040da40c2131802ca1a2910001d2160090014080d0650b40054100c00d90a882003a0f515040b0003480c83c520703440340003807a08290114100002ea00c0762000508080b540d000a40b820982c055840ca016640420740640011343c40d269064850720b0020109a00081e0a0030002c481c60318559505071a40503a102e0148500c10000e01105c0117a440d00310b900c0c401c02140b01390b40c4015101c10441000741001c2c05170740c070101e90003240b1f00b003503009506100801090460503c0c00c13040300350703503410702402e10503410300218001d0002c000005546195034502543c442c2e0041c115600c2c041c8240004066405152406845 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 899324325 1250 899323075 899323099
    0x70201030f0e061513020c1c0c0503070501140601030c36080f06010503190b040f121106090d050d02130f090f050609010608040f060e0f07090608070b0417160602060601030b 76
    0x10006008e00d8804481840c106012801c080b040d10101c0300518040c1c228080041c000040040641c007541c5280740c440009400c81c0c0310000110115619082610b0228862403600d02c081c0740350700b10f42c40d6050007002e480d0b44543c00e000900d220030004c87c3d01800c00340e807115000c8549100180007060142c141600280014805124007101500001001a24900302b4401040c28001072182e030844242c1c00c007001d9150442400e000a10090414841d28080d01949010560011020a040c0e00702203da0fa610340c1006168040e01c1d00070f42c030034048518000c44500700012440004082d500040c508000700182d88420103038214140d8000401517889092908014805c664114031900c5c1c0180c0c1100c54000c0842a0703242100041c21044101f030134500c02c54600c80c03054880040d031031044d182c0c07205050050a80d43ca2000d82da8120f140140482080d081c4014041d40b14040300030280d5008035000c6620380e0503000c9001071300c1d40141c0c00c002c0040e088a8204142c42d60035020f003160340c0030151040060b0364 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 899325575 1250 899324325 899324347
    0xc05060d14480c0307020306010e13060213051503340516020316061b0b13110d060b180613020d020c010501170d03020f070201030f0e06151302 63
    0x1001c92042c080049100c1464244020441040400140912a00c10b545030030112449944e0f80000f03004a103e4031410001107105440c04108600901440c0c08007064880e81d82c1d0380341c02940001d00388441008421800148903901c41c04104105002c8411241c4c5d2070402019900309465540c4020f10030000880c4510f0301c05003821212411001e0525120381c58282c46204400d00d050b40040296151003521a0402e035104031500e4803045aa0503154000c1d508120300d180000d242000c07801500401ea8080000c41c004c040180c21030707019214045416402480400051500540540c1955240c0e074601d040c441508000700d007194a102c0b0806189458039159000a100d030b01c1c0c0e06400d2070101e40100d190ba0303078000320f9010b0f00d0b21003804000030b120643e1904105e0030140c46404280c0301c0b42c410650001c206a00910859800c5c2c079007000c1d01c1e4600f44840d0010360103894520110380c1d071103540d80115500b006003481070b140616150810145107442d004208100e0b041400721452185204203e0f01240c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 899326825 1250 899325575 899325631
    0x31101050408092b051c110d080612060c03150f13020906130e0a050610090e060a0b0c0d180503030d0504020a03050d0e0a06030c0e0d0c05060d14 64
    0x4401c044501c8081300741948013141d800818001d51100e0484240c4400041043c0401e03184016820050311640d84040c10320102c0e9100040c40034003e050704210501c6495600c11590f042c0d0001001d80554004a180036a540c40d0200842d480d800d400030210602a0440940984103944402102d1840401110300c00040e602e0481c40e165003c0c40c2c4c0d0002e002d4085442d510103569074400310100e0681d0180e901c048550402801700c0750ba234422454034000541504e002008004804403550703c44601608100302d9800042c00508079980c048500c1c0340001d9203062041c0145415039008020b01004100e244d006072072041100d0003100d00e10301c1a0024001c5860010a0312041006044003003041d865900119011011a03040680341d405040140302207160000a1040c5d450b4090343d01c802102d603a00811421154282403860026007410f00815281c5008440e41a4040c007405007c00200e940c0e01c0000d1260b032040300c000342d1241e180c07928604d1080d070f14500b0541c0b1159500003003450130310316000d480c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 899328075 1250 899326825 899326837
    0x3170a05040c0609050117090f1f0c08010f09020903031204030c0201181a1305032409060412030504020103240f1a0901110118080702030c030f0d0309050109051603031101050408 78
    0x2002c81480000303405071010805142109880c8066514945c20740c54509846090884030001c01c50038400bc0c16a25481480518101c03002d06c0d030458603060804030b21001a41c0400b0841c0d030f06110a014000910041c121800d00581c42901c40c4000705c6240c0c030001d442045c280341301e519400100c910402c0004403070003804410050003c40300c0c0c2c0e500d6064144006102a90b080b15405105001649260240900c080e0340d1140982214115a54410003080c0d910b4104560081c0741240c204052160309002c0e4100c16009441410042400c8041107001c1c0780300d0910b03c1020070500307040b1100f041036254080c98000038145185000b41240304503d404c03e941e200c2d15003080d0400c4001407413844244d00030b42c001c00b850000c080300480041950304040a41c0c2d0000c0c1003d0341709003e455240344141c0b5000602c800003500e035101030020702c00c07000426401040001c81c2500d03155240c2c10101c00140040c8003401a4017003002d372000b85030781107050040560514003820722250b803600040c0800310b051a020f0b42d81e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 899329325 1250 899328075 899328107
    0x6062b050c190c020f040c35090705010e0906040f09060b100c020306130f05010203161209151a060424141c0f0e0d0f1b06020703170a05040c06090501 66
    0x707031f4410628003c54403103100d42124603100000514050000d032000780c01c1e458080114403410202e4070381c0045161246c40912401c3d010412085e0b101c42c2d1400c3c2000f556620643c010320004200c81c0d00960107050b15891031085610791f0f03851003021082d19004801c960268068608511880c201c0e601080e50707094080e08030000912440f2050003000505c070b80740c940041d8020f00954903401c22111000b64032400c0c11584004c12440c2112101d20815413158404184c0c000d004458070b8068500000f006011440141124042010603019691a2440200003c04558100e80640b074003138544200c070140041411401c000e0710700311120b4200c204805869002310002100100280780c8000d44000308801441843e000b81801c2d0505220240801e4500e00c540a5850f040d580741e0600c801201c11030810404050300b00c54003460b000104400d50302a181c40b91180c2080090000320807108094203008031550039210b61500104020806080c04050040503242007016819091000181c180402641d00301c1b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 899330575 1250 899329325 899329331
    0x321c0309210b042a0f031502030c1902010b040204030c030215030f0a02220b070b07050316030902040605040603080d062c091203070201140f06062b050c190c020f04 72
    0x1a81004544515000c0400d082c101800c40d90390317420500200c00080c4416500301070b114654a0704002140200d9120740503814082d85490400d00300111a0f041814942c021596206075800c02a00d66100410245010302c203d580c2c4145988100328800c801d400207101031036014024002c05203c40010706810441c840340260315070f000344540c0c0c070002811000c4d0003c031540c1d15a000030280d00b100d006000d080d0142e12500c1c180e41c1c540c202601c9034441903441780c2c416802d141442d40c146200c0e602c03403002284020b001180c16a500e000003020b441c400c7d04240c900f01d00000341810350040701d2007110700038454607910418503ca0701c2a601c00c40c245d03400101d41c2c41d035516400508120028031004000035140526140c49090601000340280041c981c8010402650404502c10700c40b41450b95120b204001c009034034003040c00d0080d034003006489614880303159550011109006141c00790b6481041d10b45540707a183e0204c0ea82060440801525203018800150f181034096101c00708140c404d5075040d40d001c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 899331825 1250 899330575 899330603
    0xe28020d170f030c0304050d031401061209381302120c0310020a1709120c1603060f060506070b01140d06140403030501321c0309210b04 60
    0x40301e40b181800c000c0c08002e0002c2006022000710001c0c0d0b006074081c904403142020040b50603070481d000c00c58280c4443c0c110400421446100b0620f900c0500c20240001ca908013440d5546009041c0350940003581c1440944000e4101c400501e9601d100c54440d031140003507045c240c0d6000840b4120b620b020307001d00d0f111203001103942030821000304d540741c018040303030190062018018001e41000f41c1c0c080000c3c400102c402c01c22196200303018040d407800c2e0040d1100d05083c81e11002d0f1a031290386454541d000711005420440100303034142c80118041c40012864901c0341c00e4500c101c0d4416080240301c1d60060000c640403400340010f0038107468483c2c0e0b2158003c5200c00c0043c8030145c08940041181d03007031240d0303045081401a4281d00680c400c1e101407100c0e0342c071101802d41d04402c0e04500b4102160360b401080142d0380308500038a14102c0030300051002c2040340075482c040c01240c007007035000c01d4807020b00b084400c54081403100d0181c0166240d030130004003a41c032540324800242015000100c01009 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 899333075 1250 899331825 899331863
    0x6040c090509150906040c1d011e02160b16110a080a0305090f0d02010503220b090102070c090501140103110f1911120306010c1103010e28020d 63
    0xd600007030a802841c8101038a802100703845000d00a9941900034611980030805608107401451051080740d04c82491810813501c2c0e40b42684c0da035002c4281085582c6004940b8844444001e1040000c00d40c0540144000c5081c0034880000700c0c0c3c030103502da8600300804da031840306080902d044030390700240e000a00c8108078005409842c0b030b80c100070380034002c0001380c0b0205500301e030080c0b41d5070b2829200d220130b4681101c200060362034901c070082d0210b03008200144800d4a12244160020004000c02d115200300e030316a4210481d04489080d407a030350000740e03582800a500810300080c503100d03200344815030401001110008041c4065818036480700100d4a414940c082510703e4a05204800e41d01c074500540240d0b1035143d60254100030561061030704100002c04640340030240c1580368140e240d0381320b0b100111561030340400300743d4182c0a6914031101981e4280260985150f0728002003207501d01c1700c174020003280044440702a102a8201020340149c0719500a146445d4211132850010740500b51 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 899334325 1250 899333075 899333087
    0x11d071103030a0e1c08061c12030c021501060f050a020309190312091d070c0203010515040b30070f0b0a0f05070f0b060301020c0708060f06030703030806040c 70
    0x2152080354080401040320160059203c1c50194050320101e5402c0c0842c904918811800c102c0c42c940042c004078001801030408404c4e00100141080c1242d407001c0c1c1c5501e65812180c041456180001d444960501c0700a034100602c14813080c10100120700d95140c140082c01e07080101c0c03000c1c018404042002c003000ca000740181c0e03805040c0a0f1501265000380130707444403810f10343c1c0822903442c541d0282108201e4800d155041c1034940004211126040048000003110001086041084501000c1d100181c50038016680144081015554002c64040800c026501142102401000e141c003000071001911119044490041c90b14612047e400b040c0c0b0b181081c501d500150140402d50030001002011030300103210464103582d41d25054605940c084a940c8500034001c5c180c40032820103030010074441c05c407a981000005000504e01042d032000142004c846502c440070580242d41088003000e03805c0c501c190f01c0b1500300c014083d014115070380a020f409010707215500640d500c03048400224046c0c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 899335575 1250 899334325 899334347
    0x3120f06130513020103060e07021f0f0c03060e06030c0904020d030306050621100b070b070e04110c060702060702060412020c21010f1109091b0f0301030605060108011d07 75
    0x10801e0245250240c0d05016143d1964000ca0019141504c0050312900300c1c14410701944031640a0180c0680d2650703204c12000041413030016440d0f031140e002203007051520400e440800c4503103010818920740b07000c2408001d4000c04440c000d4001c201080c256030781d4227014a511581c12100c1030000005802c00b14018440c40d0032194111800142600110581c1d044014001d41017121850b0169181c49401075002c200784182403a400c018819000003400740c0d140b46501150038540808100141c00005080d100d1309074015807a0180080c05204032030003407044580c000381500052a407403d0a2030f0080d070314203000780b0140c007044c074880031140e0080c800d12641258150040201800e01c940110b0381e07443c45202003420342c6561824010208003112401190a040c100010290508600c0030900c000200020440e008101c20345c0d013040b540181c2ca50160802c880b800304001d03120341c1180341c410210b400c080d003110f040c040e2247c01044407240354010f004070245045207081d159112180103880109280c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 899336825 1250 899335575 899335609
    0xe0a0e0c04030807080c07050301060b0403032105010609030501060504020a05090d11030607090e0f01050604060e120f030309060a090510020a03090c03110a09050115080c0d2c03120f06 81
    0x416071300340308001c5c014110305101c00c000e03030321901e66500816089824a2103040c08080c0d00740710420100380542d01e0707005c0000c0c40b0302c0040404011b034041641110005d82107000031910005007071050183c00d2180401410f03043d24114030b044441c240140c024001c00701e405200c1d410040201003000441c2c05c2090078004090201c4035103061280d006045402c0c079000d6114007008280c0005d81c05031130442032604950015181d01c1c40e107410044201c4818418013030080e04425414016082103a00700103540700030001502a640344e040641d6402d040200251044641c5030406007040702055011a2009954840000060b580c10210034103501a2440c1600030380039208000c800420302c84070207401e610b41c1c54202c80c0310b07070456104c142c01303000c4660038010241d5400888140000d094040c80f041e80d001700c503d14070746062860400c2c09100b903820343d5440c0340844010480422911403801c0000600e803071000d0145080001d0f2040034442024001d01c51103810904802040785a1616044490702041c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 899338075 1250 899336825 899336827
    0x30610020f03070b012102010e120f0a080316020313140f0904050703210801090b060c0d0f02060703290f0a030506060f060a0f0c170a0c02030d0e0a0e0c040308 70
    0x30304c0c102a10f000c4001d2040b100248030440c074460141d604084214000d07581611590220151441489070030704a4504135031291007070740d0488180342401c000d4116814070801207030341c0c0c0b0f20b40841c0c00c1000203428070102c000c6d54018440094640f010746124410750b02d242c000d08045a200700002440300035a100c01c150044220703004e000a1140c0400c4810940c1c1c0034482c05041c00506440c2030866550b01c504c0800090010401804000389030b42000343c0501c0e0050a9a00b824542c044490038a014440300707001044400849442150b0140040790380700106080811207031002c81500b0084181c0c861280701016464400c001080e46d03016010304088a02401c40d0b03584684a1424a9444c0d805480c864807495003026100858640350080710002c84980d920200301c03841200041e600395211141c11500822083d0f900002a4215005080000180c1e555140d1911083c0107040c185091341b42d15404020005008540d0b503150444203004480c464124401c06555054a03d005400303590401081000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 899339325 1250 899338075 899338087
    0x110f010f030509010b060f190206072f0312012306040303030b0a09060603020403032d0c080702040c0e0906092406070203070326040f0e0a1b02070611010e03030610020f03 75
    0x1c00b48010703000000d0031007040100a2382030f503400c3e0b1741c5002c1220420005604084000c1010320554980c4000b0000c0130780300b0010b4007200002500310b4108641610381102038100411088a007001c101a80307000c603402c0440c1203408a0302165140c03049000c041c0516444500300f201c192074941a80d03004142040d020010141c84950040180d4098031080d000109040201580c0c80304c0800340e41c828004440a100d40c01005450a8894085020007034500700341c20302c198409a00d8900480c1c0d645622951400301078110302003000301d25000582540e000e94806c90070080302184501e0011280260251150124911500010098492160025018046e440e400810040d034020040b400791140c10f2201c0c0321080d502c00c000540d001c1e41c0306484a481180401b04a00c0e02805c0c801038001e01c940a0204402d4001c12540e5144100e092241c001680f1010707040000c5684030035080650f03a4034074020b205d01c2c0c5580058580d01d00010f0076443c40b4801984202c042c13240200320341040b00c44070205903030300d40c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 899340575 1250 899339325 899339347
    0x702031c02030408070503010e0309090c040306050c300a1815050a110a02060c070804050d260a0e060d0623100311032a04080a110f010f030509010b06 66
    0x381107440b82813003d01c40d203400800c1518040c0a03140030206204019030030501d40104000200c80058207448400f8004c100100218130702d030040e00e01c5186031500302940c41e041c0891000200025800d002c1d0b005c0d542c85201c44081c3d4111882c1a04021035000120f02d840e4503020500c00c0c000c07103070401084404a0003a11a01465a420484c840e60444400304441c41c0c62100400d628400e481e100d00c01030304044006401281e43c0005004030324050b121240c18036454401090041c4800e000c1034803c02036064010409001c0b1101205400e9458a85035040000304880a00304d4400b40004070310400000c207008200c6046540400001d000261410a41c0246213200c808101d250304e11460240031350358030f14132050340640204401c0390000300700103145035a50b02904880c0c06d0300b40d08000500003841d60800c1c075000e502000d0001b41460b01c0c05011465441d282041241000081e400d0003441700c001c03420344e26a0440c08802107085e107820701250b140c0c4d5540d40303240180605c04180340c0c081e00c0807560710021 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 899341825 1250 899340575 899340577
    0xa0b2107170a1e0b040c05030c043609150b0d080702041b110d18290d0606090905040b0f09010204050d0305070203010e150c0a02070807030602280507080702031c0203 73
    0x4600195806c0049811a9000301d90f14802140c40f04401401044100482070803902d0700d002c050040d0310400380b4000382c041e03100501c102c2b80017006c142a03104c51044041c8080d1f1900d21008143c1c09008101d00c82180021564503804904007800c242c4002c82c1171815900c80750004030083d44030210305464540300c00d0300a0641c00000c40440030b10701c100c070044006d250041e000e003000c03c01c415400cbc00001d45488042c84048140400f010030030380000d00c9085400c1e030361001a103181011100040b4900e420000014821080350b88003040300d43c20b2000780808520030156203500034000a58980c06603580040a40c0a481160f00c413940041c001241c2c1424580c0c400098911107100324000c0c0498080e03142481d58403c4030941021215200340041010600722a00403d4641e030703c0c0c01911005030380c0320b400e5400c00650b5801a9030f0030b80c0001d88002501c1004658031905181c088583c051440d020030002c0240c052640000d15103400002c103182950390070010000401d0410468024550407150001e4032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 899343075 1250 899341825 899341841
    0x360b0f011a070c050904031206060509040b0a03080d11210a1d0c010e01020a0606080a050d1b032f0a0308090109050a08070c050a0b2107170a1e 63
    0x200d4075014200311500400c103401c03100c0040d0030078240b40c00f840c02c00b070400451a401400440c140076007001d40011500303240c00350310014200b40e102c09440b070382428148410b6550209090b44a404032220500000c2c800009541c1042078031400020341c0020041c4004641c81919515a40300c1c1c0e41d00070800710300524849407440f074580ca55003030000d80d4103002458a400e201e03591010854004220030641c652140f20566420541441164a10721403034a1716011504030b03030080d50b0180c2015101c42c4c1449010004100030403541c0c0313403404410341070304a80e040071181040000c003002500484961445500c40c6800f01c0c0607407071000d1000b90402001e1450b69404164011808100031a00140303800006100d0348040d02e4004000d402501d81e40c0e0348040b815806400211a00000c0210108054448005500203800e01883c81607649840240303000301c15503491800440c0b402c0ca00200301030650301658507075807941e140c92519510303100e4210500180650321690340d4520541030608114070407582160407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 899344325 1250 899343075 899343089
    0x120e12030901030f0e03030403080402040f0614090105060403050706110307060509150f06060909180a080c1501060c0201030e0c060d02120a05040506070809120a05070605060301360b0f01 82
    0x11044c00070542020b80352070702044103041e001840040c0200c0c1c02402c000d81d10520007000010600b02541c3ca48044403a2b903001014006203104000c03c05080400109014040840d15103003040c1c5184e070380d103642d9001406068108417102852211403c0100251429203134080d0003031106140013611190b586a1110800200040100200d00403594a041681c0141c1010f400d4a1a009980c01402402d11003e404440340c001d5480c0f50207002e02d001e01c0f00044580c401c0c0e1080e6500c0744144d100314500089900d02d00a0b524801004004180d0458100da407000e60a080c003140170f00e19080403500f08036984124540000c0005844070b9110950f80c01480202c080d18000c2c034454892454210848500311740c001c10079031140000c201c8450203100d000354085019000c50751045403e007001401c0303070062035951011a0780800c00300c080080a0080503401300c000d40007040250110301c1c4040000031403140040e81196812017010041d02d075107a400e014141c01140c0c0d0b21541c10000b51040c404d000900c6498 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 899345575 1250 899344325 899344331
    0xc13020901230307031508060907182306030f070b0901090b0c0a140f12030a14040b040b09193005070210031d060106030b01050f07120e1203090103 65
    0x12103210718101c8890b02c0d5911205815650752020550080c4100e0080380b42d1034002500000d110f01081214030b11484d46000a0104986400514940183e0440d01d21070280d00713001c046c01d0550106a1000c402d4100f503015102d02342c83c1c00010a05120445100d50b190340214540490f86074442d20062403109000c3c1d98000407266104203c4159010700071b1451200d401031500403020401000d94110000501415500200c0c05600001d1030510100c1c01034158110100c00c000e82880c142c1702e8020b445081034440d2616207041e54414244200082c0700a15010050f0085008001c0401064503103042c0f809650b00e50101034200160828401d908520380c6003002c104c290110001640e000b00c038001c072521110705183d55075003080240c3c92154404410143d4903d22802040780c0500d0030200241900007601d2a541444001400d4464006002c0d0500c5030400ca111004a201004c4942e2250054240c0401c0e41c421a02110b4400e0b445000c3c40d4032902925042c1c102d003070007000924000b04d09880030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 899346825 1250 899345575 899345597
    0x60d05190e12030a020906120103021801030819020304090c080a0c0207080307060c0201020d05130b060a060e0d06060b032e05130b010c0602030907030203071a04170c13020901 77
    0xa0240c0303035920003207040d5410081e003001d5500403010203590000a000b00140c1400c00c500c002c1035242d00130426007006801c8030001042903041800340620030203440707090b040c415030458581c05031520512080a00c140d80000b500342c0301c41d101307105550140442600c10f10050026003402840d800e000d84400d48801e1500035440c00f21400002c1103000ca5822002642c108402c2ea12043c0080c902e202c00700003595000c1102c031400c000b192007181d05ca000c03640303140e03486180c0c01e042428228a0040002c0d0045851520900605400c05d07155042c40c01d00700d400180c600d82d240b40900c090700c0d491b4000d0020100c08030600c854001e1012006a54040c41c0a4080e8400f6260018461a030007a125481d002500150111300700304154000044018040c109000282d50a944a10803a4000c5500c07030711a4008140900c11460180113241c000c1c03070300600c40c0da000e80e0344080c0414144103e114500029000d198080000ca10601c410f00000c2002801100b41d070707000d802504040c1d4490030780280040c2006140c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 899348075 1250 899346825 899346871
    0x905010f0b011101060e07050705033601020601050a120501020f030901020a0f030b0f0103051f170c01020a0209010e0615030f0121050d0f0c020d080a080c04080d0509010c02060d05 79
    0x3d918100d401865002d8000d1f2224001900c10f0341c0b041e41e082e03a40740000c100c080021841c500d280349400c0c0034044540181910035500d4000454015901350440d0080760040009aa031141007c00b920309035000261541c28030721b0308500920522421249100c8040204100c3d09010340c080c1c02409040d0b100c2c0e604d444c285080c200c084450022500da800744c01c6800e041c145502c41d074072440c3d01c00c509020752038807403141440c04120109603610622000340c80399101c0310058000e021103040c40c0740c00e000a001240195000504400050040c81c1403503a440740014507584c3ca0707a0405203105107070f10700742e076403420000d4814042c0d610134011811000c001c40c1d004224100b254544444264100e00500840840c450040300c408c0035020400081102c03000292002d40d444c40440003001d4490005c0d41c2e90360800a82c041c005620003000c500d0740d00c10a100030004110b010503411000c07907507440e1007542c6082d403c0059601d0306690402940041004c41c401128a070341e81c1c40303d03010385440d145001899900b121 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 899349325 1250 899348075 899348081
    0x1704030314120f0406093203090d06092a0317030f16020715050301030b010b040f0b07022b061a01022d0a1203060b18060d0905010f0b011101 62
    0x101c481d84109a00d03001590460384100e0302504684580b00204171b141caa5160310201d080d01004001c83e100d44944105030840d03021840724900c01c8042d0146051480e6440090003034a40640d001e4061341d01c405126040081022a8814611101c09489103100b0001d05020340115180400c5400c030700f1112840402d00c1c00742040e83c1c4905240d82c85185241e5854440d00901c018001020040d03100314080843d81c0c844100d600c40321070b40e00c2e80c0c0ea55125031541c1480101c0e41e03410380c4240d0448100f080240428064809480305640c646203d50760340f42041d201040c10309080544094210100c180801842c7d103400c010000b08038000c0c00700b4001440651b4101e10580040c2c82141d0240e0b1183e00c044034907909002003c4200050950b007000385140300420745060002e803076421500000700c808917016240e010b200d0b481c090044980c016040010b015004514028400003440c811500429107046c0303610581c0019040f00da0120082c4040c142c803003001e0000e440104200d03230110301044070394100c0f003034144 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 899350575 1250 899349325 899349337
    0x108090328030e061003140c030304180516021c0e030a0309081015180609050403020f060108060601080408090d0f0b06100311030c070302100531050606090606071704030314 76
    0x11882c4000b03103203541d54081d80c8400070701d04a8014000e403003041e80c2276541880600018100c040030703c0c05040301480d0a10403540010700e80070001107400d50250a01c2d5000505195022140c080366404899a40c4152a030307441c41801c1581c10f209a103503101c10035900203680c0c000c0382c8144041703c4000303c09652020943c2c24800e0030010421001d00100b24036010300a070701040201d1a400080c1080c0c8580031841590001c441c00d50159200225160300030780b04000050060800c00003a011a00b8010002044402c019102604141d00441d01403510799400e8191074890345c0c420402e0750841e19624100e00100c80455645201c0d403100c9061202190103402a868082e000701c200c1460b50b564480a13100c1d45d0803c2509030300314800c00400b03907440911407090a010b1480200d26110307000120071014030f180d0704040360001c0700d4040841e130400990005040c60708040c081359545d2465548201080c5103000c2d02402401101da00e00915407965040700060007600d000340d840d00f800801c4040320308902c0c440c02e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 899351825 1250 899350575 899350591
    0x11109041a090a020d06080a1a060109080309011d2d0a0303021e1204092007020102060430090f050a030b01030305090604260606010e0f0108090328030e06 68
    0x940000d5002e83c8150f000703088415045e84005038060301c6072000d034500080000101c481000030300e8031000a140c2d03410520b500030424a044856141089403681d200c1c0522600d99051003031701c82a0715403805130f0307d50842d4a154042c00101034012070701c4000d04d0201e1107800b0404001448074000d025420000900000e49030940c0080c0302403002010140899590b00701c001c1140e0241038400d14240c0703810701c014402070400100220309124000d84c503507442c0003010400e8003485c104002403001030f40c002c1005036003c6c0c0c004a00391400079074080c20944641514104540001c1040c0000d00b4407a040b6517800e003510741c018080046a525081885800041d43c00080c000c0c0d440803004200182c0309800420724400094842414a039803a0b09e24904104d01940003091005a99180c02c031503001000001d41c0300034246000c0c103070400454041681c0e07034100580c15040101290000700505001c004647c5204a1000d1181c40d503100e800b816540e203070050310200300180c01d00b018010800c500040070b0f4010044 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 899353075 1250 899351825 899351839
    0x12010e1005120304080109080d150317071a07030212010515190203210108300f0c07060e0102070e010b041202031009080301061b120e01020a05011109041a 68
    0x5040402c9401044410008003a101c10040850407031002c3c010741c1c80c0c083c4681030b51f035200c4c000355040b00300340c40501d0510013604880d002c0800214452456100219030440d812943d03441c03441c20145500000d0260210501c0340310b900b440303d03941d03240e80181070003011415414096600c2d40104521000b00d00d81c81460290103110400c0e1142032241104800e11040c0122071418404481400c422103019445880401c081c900412643d58244116086c1e01101d4200d0300440e4101408668a491507816180780d014001c9195850509003004903088410f800049600086ea07072080200707040c2d090350009005016403080000c500f42000000c0b0305032060b040300c0700c1c10715041c180d10043c010b4034218281c1e40740c811960003402c03d010902c20410303441c3c0201c0b26a543d9606104020700682e005a00c1406542480c1e40342c48082a041070540b1504400ca141940c092991080100d19010036260007501e25441c140c100d220040f40103000780300305075042d10140b001410404c11040720308244410b01c2c0c1c0102d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 899354325 1250 899353075 899353079
    0x9140d0914011b210314090703080c01090c170f0a26040b070b1506040b120423100c0507050c0d06022104060e1f021e0d0212010e10 58
    0x800b60454041c3c03006601d01c600384000880e265011106900c460700301840300c1d14054100026414003807840c590221000c050300f1810030301001c40d40d0f108103102c09440440d01244034041c049007074100c141e2143e00b00c0040c0928940340e805107803095001488208440c4680350301421620000300d0008082904503030300b40c0724456464180540d107009180040049001000003081c015501c0c0c001d004840d0080520b002c0e10b19102c0b910895410a8481e021b03c104005e220801400c080c0200b151028450680c0041d219220b501d00300c494001000b40703c0c403c4030313480b401222001c0c40c005165200809100014840c1c400362500079101441411005012a00301c529000200d0600f0081c1010403407161500501d41990100d240080d21407080b101d04030078a5009c00d11003407200754003420080c03c0c9081c001d40002c0c1e659003040840001e44140c10101c00d500480c580d0740c50362f220800d0082c40385121420303d60360000720200f040250b01c08069801005c0000c00042900c0f009031f813100f8840e020418100890764 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 899355575 1250 899354325 899354327
    0x102060613020711130b0f0913140a050304300804030605091501121703090c01121b03052a0d0b030118050c01120c2102070609140d091401 61
    0xd0b01c403c0c1d00780c0740480281121341064444c2c810009036048a040001101c1a100c020024145002101c03140319013a408180200780400c141071040695003c64141c401541c2008014240350520300007410f14000030600046440c40388a40205442031508041081124140c000741444225100600805002e000a000180c8150300c165000510201101c910329018403a00300d001009070080001c0c2a404510042002040180c240881c41c0750181542146060006240d0300c401e22001c1604100410a19240c00d168580c42483d52214040359160100384081e00a000f034203050394421990b050440360811040c0c0301d0100100b5620744600080d103000484040c607000780c0160002e00390305544e00e00741c01608490403044429020310036400341c00c00304a40f0001402c03000b0344031a280100d5040801c0204804c0d80a007403c140d061514400458242060103020000c2c080c50000400443c42d251580040c0700204e02041241110042104d104c446a001c00301d6020000d442880414480021140055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 899356825 1250 899355575 899355577
    0x14070e2403010f15140406111e01020a110102070b07031d010f0b0913200a050916080c0a212301080c0d0305030c090d0215070501050a0c41040f05010206061302 70
    0xc06101030427114287c2032180c2101800c00f54200c00c81840e036001a1800d00260814400344410460200844c108245074645074011030005001c4410180d0b108480b0081040c810b000c106404616402008550440c02c03083e0020002411401d118191040000e80e42d4900040821800f6a010fa0fa80300e45480d04044000046046242503621402a4801289580390490794510a0308501c042c2103000a443c14080c1007103101401f10001c66004104603621140c200c0c1003a400f1111034103414400b82024072941c000ae1104d1481c144100300e0304000203d409a1403480746040e10b007034505541815074140c0030000d86032500c00c002008504103000044c0b080403480003900c4000b0003d011135890031f10303a40c00100c0c20500c1c0d042903c22100041405814401c0910030390b80d0141c0090b500300107201d400040600440365185150502407942420400c400c80740384400d02d6900200f6007986002c041c04180c00806421a0040c00501c0c0144d400009803584000b0740180658070183c05410380609004285001e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 899358075 1250 899356825 899356847
    0x91d06010f0e0616030306090614060301060f030b0d03180801051b0306040e0d0c06050a020a120902040e010516020f010c050405060c070503030a110114070e2403010f15140406 77
    0x80f0603000d100b10403068450060b881001880ba0f540040c209040215100440b02e8940020302c80c900d40044030b403a02e40354902101d040d40d5541c00d00d5100a950100201d005d0141500c090703412084540071081050703040031524804a02c240c81e0082515140c00106089070b0f0100d505041c802d10f012060861503440400440c0c004802400c04265210b1501186203044000061103000504260b03000b014080588961904800b5100f8190f10302803041c0d40007080e0180140320740000f503598100c2c400456a9542c070940e14214410300074412440e01000390116583e2821144000d4018040701d514185418418a98185560784605052500704010320803141c10401180c90742d4400c82e903000c52680c1e8104087c2a1180e0244e03030f408003400070351815600350b078a5401985148a181c00601500c1c41e0007040e07082d8141c20039940c0c425000300b10b506551400441c42c90a0b03407000c00020001c50481380b9003800713000769003030349103013600905448108840a040d006400885c80a042c4000e1100b548160b40030381c8 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 899359325 1250 899358075 899358079
    0xa02101d04020c2a0a030b0c0c0f0c120c18090a060f020304140d0c0303020306060d330803030112150203100302040c0906120b0d0b0403091d06010f0e 66
    0x3500301403400c08201240d2201000795015400250740300c14030092001c1c803c01280c8025070340c1804000000102c0c00da0074032030000402050f0080c001502c464803450a4a0202542c00d040301c0701842c00f0403079603403640712460500d40030b401c0080c1d68042c02d8500142401d440741000e03208540380c01e10007d03420b078001805400b0600070701510180c0400b1a98a0007034101100c040b0800503a641418039000d01c00d9084100d410304079400c4212107558054000024060035601404d015983c0c1e035800002401b030344507100c601c41c291031410201e00c3d894910400540c40404800661107045070680181100091451240a155600420051100c8110108000401d0f84241d00c1a06481e68840d81b400a17031300112205e031643d80602008000350f1a2074003c1c5001083d10f400c144a6060906130700804003040c00058588541e100d80322201a5150168210b2409400c01e411202e80d080c14034006110384840d2050210080038001183d640c4441043c0c5140182c0051316400b1000404003000e03107940b88090352950f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899360575 1250 899359325 899359367
    0x306052a0c0f070f0510031a10050f0a051b070522020d05090c03060c040b0a1407020d080c010e0309060304110406030c152007031b0f0f060f020a0210 66
    0x2d5244142000080041c2c41080002c0030300b030303003401d00348020390161000b52800c1508055406007144a189031400e0a90801e50f4641c04040320340005503810b1207003040b020400c480c00210030002c594002d01070441e114080300d120402c80a14140d9a45e2607150740120399215031400c549100c08040754005032183c11909030098240340c0e510001700202c91b02250802903540010030003d08501e41805420381c0700e134203181c0d01f0f41010f050a034034444a0007103864040522440c03243d020a5021080c09486145900401419465140f03107801c121580240304842142c0d0309040d08040e2004010058038024000a01034034119501c0f070301c86507042c800c031a41c52500309035241c1e03010020681540c840070140502c1c201e004041102444010114580d103000400c025441c00d080104030034000c901102142e0300b124103002c01450110480b4426952030340008180d400d089000152071800b164960304440b86522100800151010140e0322400c180c0b40095000003001c00e030341d0350b460291036a0320b442c0ca81c0e4642d003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899361825 1250 899360575 899360593
    0x61d01021f140708090d020120070f080c010915050c030a02071a01060216061106060d051e011d21031302090a060503070f0b030c0a050c01150306052a0c 67
    0x42c21120000766021000501601c3c00c2050310f0204204101d00004244000c002030310300c020015484075880c0d802005c01c1d8100103104014031000d980b0780b69825810101081ea03a64107031000500800c058002141c92500d21150803201d1145442041d10480050040300e14590313501141d00020751000104a900707680e10020300c50002035041501d030180160780c000f80003060041185440341d030980d5001e6810051608a01084c0d441c01003510340e00044290344003031000a040c0f03000d50815800c40e80c164440061556500380341001500200da0000090078001501740c80c0c1a41a0386030300d10900d03100404122074080c00d13404118400103650000317403100e0710014400664000b402024094071070340304440d118001403005160502402d03008003140402100b03d01c4c40c014000ca801d02004044070302c49200411700d0089a40210121049407140d0300c020840c50074600c6007944000150701003914918500000640d080401044500d5a482100340c0184000744c04000140310350b00800c070702081e0740101900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899363075 1250 899361825 899361851
    0x120215030f130c0e1e0c070c1721131d040213021303030507060506040203011203121104031a090712020f0a0306050f0114040b010c020405060d02060d06061d01021f 72
    0xc03602079a101003591035039105c219416003040d200a0b00d5800028030400516001444840c0c00a0843d07607004007040c10780c2c41514a881c2404a84040c0790410100d90901b40300124840c4001c201080d01c0c0c0040c40c6213030703480310414107040c0140807032855403242c500042405460200c004018030400100003520f0845c480b041c0800e044a15803040b00030400210b045820050b8034042d0503070150040e80c0450442d03151101000720314401070300103014044114689804028260080003c03025001030f0075603515540c4c9440b408180010001d10b03040260072000c41c46910010644508599007140b2582100e4915002c0140d00c2101c550015442080c042d030000000780c0d0703800f03940c0c400c03082903c02072000c0d0b00d480c8840c0f014001c110740841c4110320780441440e40fa82c000d00d0105105805940c00103a5540b06008a520401c4d003c41c040e5118401040b64241e440458000005a40c599500d11840c610900e5101c80702c1c06443c4200c501581110700e40042d160170f41caa03107030410300e0800408900b44c050340720 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899364325 1250 899363075 899363099
    0x200102120f0a06350d2c0405040f0b090a020603010512070e070315080102040f170309041103100602030309122a070f0e060d17090307120215030f130c 66
    0x44102a000032801583e011200428401d80070132000710007030602402c10710f0004100c59200b545044400a1303102c110003514028030400f500c0004050000c004130b0800741046c07a4034003070304d0008440c020340c3d41c0c00103105078a001c240440002c0d4017600711410341e400c0c0420050303c801f0400c0041198425014000b600c2060704542c0c0d03008413034903200003840504070740c403000a05545801104a50b801044100519405c0d400403900710356110101c44500c105c00040d4904500c95205c0320f40d03006040c0030300d210f02c0c8010100214004c000500b98004504d640307140076a2240000ca6660189070030440c2c9001c0d800c1c003042d000b05200c5e401c03000c00040010310007a10051490088001044503404182c0902c140d030202d0751b29202501c0b070382000c0f00311460035000041c1d103d10001d0009020300c1502140b590165003001c10f8442d0401d00500f41d403030f8140c40c0c410490303a10316141e00a0b4802e400030701c15200500c01400c1200c1c003510341c02d1081c8499640d101480d2080c0c56280c03504542ca2110500c0c00660b100101c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899365575 1250 899364325 899364359
    0x70b300405210307030f020c030714070909081204020a050a081506013605060d150e070c0b04050c04020301090b0f03030f090d06021306200102120f0a06 67
    0x9045208542024103006203002c03840d99552a04080c02180e0403642c40340702054a6010300c00e03180c0480c00040049400b0040c0c006c4040201d030030b1002240c82010840cad1081c20050080450040300c05566075114090161040d20501401c1c1c0320341040744100130250300110070348c0a400540311801c4140c5d10404914800440d9022500d01c0d0801800c408058040307001c9290006030919101d8140f036081810400704000303d83d009240d01c5040101551450400003540e0024031001b00400e40340d56501d0303403000141c180201318407080f8442100202d801f80084541c1070044c500e640e00c48540460545e9550075058000d4401c4d42c2c14821555030240b90f42d5503000450183c80c1171400895600130103014003420309503491007c0d20035081408540c03d6444184280e0b202044101d44482a00c01c0d2030030283c0081c40340d290a26800c1d444035a0214609820900c01183c180d240304051080c6108622070350300303e01078003016001042c0b006010407a400071070800c040e0804048200042c44070780e11494007010030303030788 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899366825 1250 899365575 899365657
    0x90301090c260c1302030717150103051617070302040e0a230417090d0206120f1e0a020c1c09081e030301060f050c0118060b0f03070b 59
    0x5051031960314007203012003610205242c000c050f815403000000e04500000281c1084103070b40800082d1403184644112030841e0180340385c1c89aa42000b032005c980d80d804880d0001c5c04a4107142c00300314548000e4084002c80125540c81c1c001c40222840302a40c010006488141016000e010200e40b003514040894000c0c0700050001580c90359002c0d5a418402d001c10300d0b0860310341070740c04001c0800c2c842c0015030082c602c0c00c641260fa440003200001c804d0190301c0006900148081500310f0400c0300c00e18014000c0183d250b81c000c032550b5040b1090b99000714144050314080404000c03490141d0281c01401c0c07000c00c0502035880b10310118041c49008c0300d007202a280040c40c00d901c01c0281510502c0f007120310004811650600c044000980380c0e8038801071049008001c405290001d8807032081040c1ca0041a0101c020320001e08216071801140031403a205480c090302e0700c21040690b10702040710140391400540580085883c0c4000780d14217811604005c0450a5120320b031080c02c54020b1a00170340c1c2419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899368075 1250 899366825 899366849
    0x1101060e0406060602010b1008090f0618070f030305070303090c05120d0f020a02010503040f17040602031801090e13080903010e0a060e0303010305061902070b15181b090301090c 78
    0x141001c01c191200b5a1105045d645403d0950a0548620f280030000108600f44440c440e200c040c1d8491400e0040603030208030340994401d1083c00c002090880507114100000c0b00c034100d0f1503400c0c0e62100265840000c0c045041040040000b900a400c50a40d040c040c4000e6000c4079503d00c0415404800c21780244415000b1008120010780c20902c07034045c403003041c40240301d15011640044d080b4800640060060740803420341d00e0400408040002c484085078202ca501d0b641d803040081e5603600031145e02e8084804039910421a94810381c90041110011301d038000d26a2280100300360040c1540c042521140c00401c08101d864400f4061400d42c903080b0001001c070aa224104801214103291142c821608200010008a4400070342c2c560045286820340b000c40754400d04910091003003e000030318580d07e0004001c4a01a40c01c0c070010104800e0300d10501c2c41261101d080c004500482e480c015613400380c000c0140300401d81014003080f40d006070000614480707036140c161962846611003203690403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899369325 1250 899368075 899368081
    0x1031403131401030e03030114040906020d1401080c0d0b0115030908040611070906050607030f02030c0a031d09011a0d1404080a1706010207210215190e0d060c1101060e 74
    0x41c4c180b04809280c10380c1c10145003194140312500300d11008400704503100b40d80b070b8070b609400e101c0c840d0304640310003401c000f00700400c24950111024201c2c003449580c00900030724061281034180300c081c8050035540301e548009142e080c5a00510003a10f110b40b00d01c100742e500c2d088000021300d043c00800250801d504d4135189051004400b92030140141c110b0f03c05682080420031190701c03a807040d620441d5050900c503045d030211190480c5540240b24542a50f441650340035804c1c0368008000041024010307400e0708007010300b10140002c0395002c0c4a010442c1520300303070140710305850502030800c0c00100c08012481c9000c61a21100d840c1094405a5030100300144150b91203401c64450507000740440c604140900d08800043e468090f103106003110586500550602983c0c50101000303400c1c0d000b49540b408112900d4079800740d40200d086003006454020301600d042e0300980706c40943c2c0000925094083c4141c1d6a07060140c00da8031786660511006001e242c2c500c403001e01444001d8003102ca0402c036546 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899370575 1250 899369325 899369327
    0xb091c0302040f09290121050612010b0a0603050606090a1403010e0a0c060507060209030313031106070b04081b03041211040b0f09090f030f0910030e0601031403131401 74
    0x1035055110700d1444d46000700f040008600d190826411441d0030303020524a600d0703100161013003901c00744002c2a01c111021031114038003441e1700035401210705580d52100f036038038074907818203c48001010366800201c10f00c080140c54801d800240e848540a0207143c10400803c01184242c80c00790041d6045a00c0d2441183e003d045c01d100707205101e09030900600203440a600d5440c0d140129010341e00c204180080c0810a2045036011242d0b12034010f011607640302e88131010001005030f140402c03503640b24450401321540c60729405035101c41b90402040109a142c41d030350f1403840e5100b4043c0141c2c07440c0c8040e0344d84145030140301900041000c0c4d001d80c0105d005520b446220050910310041c481c5240072a90241520f410740c0901d200a000e0f1a04e00d141c0d2118041145001010340383d0504500c070009100401e852100040c050b00e000030344800450f130710500c00a0303050f210f1551100d50141d118400400114460030030b1410390306042030580385820404c1104c0072481c074007504982d8584d408a0074003031642d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899371825 1250 899370575 899370599
    0x507230705030a030c02040c0c0c140f0604060302030411040e0304050618060a09060e06030c0a030b0102120f09040e0d0c030f1106131a190e10020a0315060804050a0b091c030204 78
    0x1c8e119180c9914038041e01c0d40c03810b9940103d4001c00c0d01076240340c0d644c070b9600d803100d55400d0311072400146215100c6543c1ea000a002e54001c8500700d0380c1626143d0840c0a41c200390083c02c010ba100c0401030350505080809125568000c42e4850149000c00c541400780c5d0345805004040d8070b10310355215508141469000f0303000c18450750202d4020b60080080001e1074507400d060365028500d40c83c0100d003a2002c000100e20380303c1b1680424941300c400007201c016000d417540040148401c162400d218542c045452540c41e04807440c0e00401240d8400b25442c00a4482d003181e40c1c02070154101000b4600d6600040d5180c0320040f04c14100d50400300100c882481514112000706003042001282c032498200d07100340c042182d51095081d03882d00d51540106005c0e00b80040c10141030380322400c54913801d003864000c0245c0540102540940074101022590310311816045101e6074003e8010103000003c1d689040b42c2c22801851614980501e08080d01e00341101c45107000e41d003145035009070f02c41d401d00e1429095 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899373075 1250 899371825 899371841
    0x6090228020a050705010318120f0f0216060c08041208030f060607112112030117160618120b0f01090e151e09030c0106060507230705030a030c0204 65
    0x542d4802052400095400954081079800a00e00444c0321403003584900d0214644220041c140b510030034200744c00952001d810200151140d0b240f4028035032440041e40ca4008017030701242906405030702845070b81d00900c4403190003481580c1c000d03d4141c0c0c550000c03900403400d0701e0071141248000140120401024101c030b0f08901e080700e049203000041d0360390b040340c0140d5008482c02001042646a10301c680c0301180c0002c1c07506c03041580c00b100f240e031046c5501503009002c0c1c1c1d120b102088600940c1e0310070004070380d071800310201100c24071541002003d540c00744440509049546031900046240c11038603150114a52041c01c0c0c81d9482d041601301e55080040580101c0a424a0013130102d41101d0001284940ca092020444400c0c0c2c81d00003000007442c005a0b1100561100c06d070a01c07149690020043c090100540020009280c4401c0c0444941c890404050002c1801c811b5003141d80304002c030155a100340b002c0865410556070b0010030300702426840c1c15000314003101c50709415402c1c1030182c018 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899374325 1250 899373075 899373077
    0xf1b1701090b01230108072007080f0102040605040e0903131e0512030a050f04030c0e040c08011812020120040305160e1627091506140c0106090228 65
    0x1c01c0d2520321381c2c00150f04544118645c10010100049980113000d03880c00b90082680788032034202a441c1100d000d0755654a4410100d5900c20004400300701c00040c800c3d00c0c2902e202d07503102c0d40f4091511070854611341c0d000d003084600d40820059042009103480403140200700c000c18100304085a40c20840c1504800d9010034001c03661850004100c02c80402114050801d03402c00b2500c4251a1032910102d0042d0f0700001c09075030b21241d02095402c012a4441d104a1260704034a07000e640741d6414600743c45200d185018078840e440c0d501c00008800e0340c0703600d07404800c5100010b01c1d80c030030381d40b1400410640000c0785a8150009400e005004040c80202c03098001007001880c1707036150800e070072034501000700b249d14500c080a40b20ad801602c102d884407007800124401c00342440d40c0754101d44e0648007500c0707201d10aa25214030a84550103111a400448203541c688184ca10000c01d40d8014683c801205681d440d50b990401050a003e41c0c40548041000c0315000c0110155101000c8041c021800c0c0e684 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899375575 1250 899374325 899374349
    0x40b0603060901111c0609050c071209050d0b1e1504060b0405060a080c0c06011d0a05090d080a061a070c0806040809042a0215060109030f1b1701090b01 67
    0x604d0345500001702c078401c20412640c1e14040003e00c5004004101035045940e00758140410b04c100b01c0f001c01c002c0d18985000303003051b0048502d0b80304240e80600c0140b1a49401284041d0f2400100710006030255004030b0a00e9084103600d01e00414040701d5008580100070300e80e0070480c0480c0d5040622400b000780c450088141d207000d04040000e810ba009000904041113010000030308180c8034102650034507075030074017214200e50710388500d01c7c1100c0b5214482a2407000c10000142c0740000d5020b4140103000e5040502140200c11a0031590310500404100c01151281c00c001242954120407040b0341404040a40e00c4050030b20f4000c1d10500346038085c000c1603104800380408038202104490305914101c0d0b002498822042c955507103410b2140c1d0b0005c414041030a007440480d00401c5070002e41100003260105a61008010741c1c20039014007010700200c000b0021800001e000e140c511030100c03100b40d0540302c01d55a400305500b15200207440c5a0303a0781d4584c0c0e455030802260b40086070151125514031 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899376825 1250 899375575 899375591
    0xd020706060810140f180a05070306200a0c051612150e03042108040b030402040e0d02121e130608010501140d09020d150e10020702010e150d05040b0603060901 70
    0x810b440c0c1c100034203180c0c040001c03180400c0304003100c91142c82c800700700f80054a07202c7c2c110f420071949a02c2e1f140700950380c541c200a0818220904509400c0c0c9406505600c5402c1000224003164100800102120644505201001d1019800141c50006d004d04042c0201200c030074501820343e00f0a075400254114106244c821180c0e07004020744041d0b0f0852050405a040e981d030316248000500980540040310000d00407c100604000461182e070082e00d0a011151380c0c090343ca0b40d01e51540f4101c00043e007206141003403007075003c0001c02c0c80d1020400981d400d030b000481d20512070b4b030003501c40388800003883ea010000c40c0d0304000103d00500d02400e04145084051100c40d80c00e2040f90b803001c00041c0d5070860003045540b1540044541508410078030741201c11288030100910301c800a8000900c03072000f107856180054000c9807542d9038180d41d0ba003416044d00007400410703440f40804903d24401440071041e4002c56100d090303c135a0060000608a05001c0b05050900102404640b01e6034100680 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899378075 1250 899376825 899376851
    0x180614030c212d011404020603070e04020904020c0307020a0603200307110607030e0c041a0607050307060903050304020f010219120201110403050705010807110a0f080d020706060810 80
    0x1003404054086501100100c40090246003450060807481e40e01d0000444140c0866aa08000d0342c0103a18182c0200106014a54039405c0c1e2030080794000c0d800001080003685c0c00b41b182000c1c0c0b200d43d101520150900007803d000a042c2d8000441903d80c0740c0c4049000b00a42ca803041e40b60000f003074203040400070402c85104280b04480c1c5400c92010b08000000442c90700741c030510540300d0000d205030944030642002e900040107441c4080300c10200d84507401601903d0b247c244206814215549142e141c0c00b00840148062604954801d940f031380420300040002c1401070003251042ca110b55130b400e90300c2c90244100050010003501075411540041e000010301d020000c1d903050032640103940d00d000c041d0609422405000031141c850714260300807d00100304007001482c102034423026240c3d013520760703583c03a022144010040b42103c1c072507000c451030401003000c0c1c00080000c2400303880594a0030042c0a45041660322105044800903629003080211000034030040000c00401c0360148550b43d21048 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899379325 1250 899378075 899378089
    0xa0c091a180412050d1515110613051f0212010e090a20101220160f0803150405090303130b1f03050312010f03080406030c09180614030c 60
    0x2064000c8100b4103502c03d501580a40e010b00e02d80020071300020600c0310003003242401324841c642d5134500340d10000d41c100f4041c0244004d04005540201000c0c1d4582d0705082d100a0310610544440c0514a4540e08840d15550a102c81e007070283d07805691800107540b40421041c2c1640001050444182407202b00388022494841c5e05400100390100489400103250000600c40305056019502020310000103401c500c0b0700030201d881010403c044000b481081020b400c024101c048261401c0009410001a914454440038003440110f002c441c200c0d5111b402a600a075070500308041d401c103a050f814035060181341d5001421002a505604020842c10300a810003840201940311138400100c5204007d500e00c0050803400340e004010590b80c0c1441501c0e5448400800c00d0644080c0010601c0036101c11301c48100e079800038040b864907242080c214010040396640b01c042003000b00e0000b903800340d4420654002d0041000008280e490080029000c3e8080c912a50003904000c6440702c40d07a131068 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899380575 1250 899379325 899379331
    0x901061b05010b3d080c0304061e0603051c120e0c180619033309030203030a06120b181009050123040b07050c0a0c091a18 54
    0x2588020000940745802805031021240c1140c0090b00140a4000f6007003000c14100411071004030440e01a1000620407280c1c050707450702c0d80201d440c0801040d20881755400550307000e406008000b50303600c4210303030101805040002c800c00303031031301c0f1002401480428003180c0c940c1c0c20303040100140308004a030040d110341d00b6076940e000c46030f40c3c1d24005220351700c06204c4403c3c14800140900f141502d45104801c44840a81e2080d004168004111219a42402e50074041d0703a0040c28030203410310700c002000c012014049410003034040c0080c907010590304a02940340401c0c0700340c000d144c903071030050741507c2256034582c0005148002d0500c4030780810302070441550840300064a1405100d20100118a41005501c40c15030a92805807543e06100d41907004098580c80140c072640001190307100c2e000c170081c0598028202c040c120011440f40c50080c00204490b074003010a944109000d42c44a0b080c5048603032018408607181ca00070050b29003505002010383c4001c9a4004030301303211124031581c804000f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899381825 1250 899380575 899380607
    0x51305010e06071b0305010c110c0d02150307110c19030206130e09030703020709110d0b030c06070b0a05130f0809010903060501090903020c0405011a030402130204060801080c090106 80
    0x124039101c595484002c00c49000d10707040038004060040a0080c01c0c2c0c2c03c01144400d507029480d04000c1945241324074400310800401000503c000c8070b0f04810043c40705604c0d00f003281d0201060740341200b40003003480694480c821903180c000e5141c41290040717041544100207140b240000003000c544204440f2110020790b9010740fa8551500d1f0004245000b80800f42c114108241020b42080705244000004000080c80f0380c0c00d0783c80c1c1540d603065034000c0e10580100040d03c0d000a100070070a00080d82e00591a14800a04072600c510b100000b1403000c0d071081303100780d070000c281804001c0602480d0140380c0d00300eaa149558285688113856100e03000c1c1c0c1070080202420b100041c4100a03a2048640c000a150041410400e6507561003001d00144000c03c0214098010000540c6492401e407055a048440c0021401c210a00d003500b05960303640020822a4002084003c4107080a464806800a050f080c0c5a41585d541003d80c120300d45014084101d21031040d26006008455000000061039401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899383075 1250 899381825 899381837
    0x1180b06010f110706030e0c090c072d020607030c140304050103051b1c1e02090f010305040c1217030f09250501080a1b0206010513050105060a0e0d17070b0705130501 73
    0x4034800c071f030b05000e402900300c0d41c480040d00074050400d481e40001c104461141c502ca42c01040482d8036017200c031884074082215009582c0040c00581404402488104d100b03180201d025841c541e14016480c11601c58031140364030101f0180900c0d43c05104060300451500c1c10b004c0081da9031540304a8a108205401407007200c1c89203100042c2c5401d800c00d410030403414609405171001c2d09450300c001e400110701c043c0305042c8240503d9072940071341310b0a030207580c0100f000400203041c0000740914041d40001110b0322924001e030038020f61240c13405940201c04981c10b40d030040c20306441461400c03000c0e202003c0c43d041032800005107043c0e020381c0c00007100c500b800c08140a030b581d0b03103880004240c125914480d507554590b0742c690055000c641c041c142d507411690305c0c1c1d041c11055420000c0341d0b002d004860b00480d08024030245103000b5062981e85a00081a823070100e0419a94024941289084203c00060204008040049200d08550b100c00c0e80e10f41f41d401e0841d070b60a0000003480e144a41d0703040c0130b2 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899384325 1250 899383075 899383091
    0x5070f030c0215070605040c0e070c02060906130e0601031b054f0801020f090d14070308030105011409030a110406150c060606050a050d050901180b06010f11070603 72
    0x8501240ca240900d40002507030300c6200c1800d100000d0314040700c023219003050910010509991500701d250160503969546d140802a60b82400010b0780306a80440d84800c041c0301e224091403d5090b01d001038045155806202d08040c4000340c181c80401c40000c0a801116140706091540079007501d0700402d0101038944a520161003101c030310b400c0c443d2402c031701400d403010009040c03c24500056607a0001031030380010070b6852640c54201d0040003030212510f80100540e840b10310b40307142001c0d0a1401001600005081c80100c81e1916100d07a03c02c8404000200040045607040070500ea05941900907040c580085440000e440d0090614014061a0300c240004455142c03603201201034030491480c2c0040440c1c0f850040c210400054048810038140200451000e20a0054803109103003900c4007410003515090400c080d02c001880020250b40c0d440001224600c00c6501901e880d000b1414a0f0460030b100c00010480000c5412810500280c83d4800822800025041d0120f81c0540340015040c030b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899385575 1250 899384325 899384329
    0xa05041a1e13170c090c0a12110c01022106010305190c1103131e0f180906050a06060806090106050a030902060c06150109140306040f0302010e070e090d05070f030c02 73
    0x48660b40142030105101e58001401e101c0001d544c0c40d82c08001c4404894550754603134014024420200701c0800180741b1044400c0f0825160003441c0e0400e500030b002418007101082050880c3c01c01131009112482041d1040c00800d49088601c0d003048080c68140083d2034010641e82e141a014060410640e507070301030814072035121f00348091a8080384c4046e00e030b6412000415500b202c22600482d80c44945420051000c0a250400001110324010102d003002e441c104a20302d4008440b1500c0944e80d80b01c000200004019205451141c0f00000000a0403805c0480081501000905a41c000c0c00e564005105954010059580110542c039020a026240c0c0c80420030a011740101e144a52080505222480804412604d80d4210a9071400c1026503110443c3c480e592440441d00d80580194000c200816180b55500e0701290090001003041601004030f1890070100d80d2248494250420900000000501080400324000c0c604242445029282c070000c1c0301021500409210705031840c40115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899386825 1250 899385575 899385607
    0xd140a0606090203060a0509040510180807060515241606020f0d05160915030e2a030304050114030a060f030308150d05031207030e01020a05041a1e 65
    0x500e600120034088150b0318400b50029400c02d603901c52081d410a2408038040c02c02c035241c180321301d4000d801083d20386583e4608400805000200010381e10440006d040070864640050102c00e100380706c0000c0914044c003180ca06000310f102c1c014807501c0000e0803c00540070f408840016003d012110719915000c81d2419080c41d03124a000402440c008502c5c03080d0702420501820401100f031005001c01d6584002d0100c40404403d400320200710085010304c00b82884035100100d540b120301b400509401c1d010907581c40d1100ca02694000c40160000d44124103040203901c50002038146c3c019401d04d801c3c84000382405070202c04600858401000007002c03065281c1141d0010407416640c1d450540d200d09009080580807521884440d100d120030668238140010304a4005070000c018508050442c454070400c00000f40c4401c08258441621042502d0207200030b110f01d480c2e03615820780e19483e01081070b00a031005c2c02d40c00c210070740c1400032054440010904940e040391b8080d01c41c0d41c44440d40e80113507038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899388075 1250 899386825 899386843
    0x307053c030103060627110918091c1b0503070f0c0f0509060a0b0306031c0207050429101b03050409140c0f28030203010e0c07020d14 59
    0x101800c2030181004202001075040e00c1c0a8031040c4070460701c3e01d00b0b03420902d080d001202120800385c510400c80d9111944180c80b030042c4442c596181944030303c00541e03a60080108403e1f241c1d100c0d001c4c004024010170a00c030038071947c003140c103030300204440c800f400311801004e40d2500000a07200d40c504100d802d0007102d003895404102c252400c80d107030501a00c411041c0c0141140046c500b0b20100d4540f9040030811320076500280305040f02c03418100701e04040d0304003422283d0584a086442220f80e1003a4110926a8550781d00400400d45480100015119040704000780f118818031900f0600c0c00494041540c58010ba5201701c00400200003201c00c020b0681d0040350340c0c2ca5a20900c0100740d8041c004104070b4800c804140118801000c00c000c0f9110265030030159040300b000445070100b038800250401e801340007080500004403882c42460642c540c851040040c0d07001006001da415039040741608060010303201030401c9001d5002c1515424840070141041c52011656405041c080140b10b074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899389325 1250 899388075 899388157
    0x1203050d06141c111e03010912030c1b110604030804091506020c09010314150406020c0f06011a07080c030a0903020a05040b090123030319080c030705 66
    0xe1076440c82c0303040410554041480c40780010b0b8083d10040b03e030510348108511303040020108801d81d42c0703040000403c11104407802143e04180a00d502d980c007072040007000ba0203000c4118040c1300d5620010121403c080c190b8040c0803648120014041728401690303400f80d400340b029103020b1007840c00158540229803005140140010300401d0700c51058000c09003000c407001c2042d28880e100c0070183d031070b82c2c0542401ca42040b0400010404640318640f0b400028881100351540005011081e80300b00c4012682960002c1e0000b0b100d10032603400300a42180181004c010344402e50506c405481c80300314104d11148003020114412080c01040400c8030066a188401c07240c0e90003179800040c25a0750540b205034801c0c002804001802d041902a031421214018070b0008141c1c2030000c041403401028072020000f03142a82ea081c40c40e02c040009203440410350b2007440034001112030007010980028850107000d0002d10520404640080c15590106403061040ca001301d80724900845800c0242c03c820 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899390575 1250 899389325 899389331
    0x1020120a0b090717060d0803070f210b1311180102070510020f0d0809030901050c0307061d0d050f19020c0307060c050106050604060203040b071109310302071203050d 73
    0x43c0311600800719810a0501d091043d1440c2c0d140401c00000d920302041c068103809040000803904c0d4421000b510161585040260f0250102d4504c91500c400c1007100c0e01e101a500c3c854462240340502c0104400440c0d0030040c03203610074540c0314401f1400340d00f091030f40e2201f90b444846150ba0091000c600035200c09400030381c13418443c80000356181a4a03014a5890003000802200280b169428178441c2c0d20013001940b61443c0d000045480794001d105060890000b07000003400200c0ca40140b005e90b02e8120740c030310416880d101d0024101852031030070300140a010840e214901d400c0205488640c4d0440d6441c0200c0d820550b030503818215051007490f454001e981f00030031102d801800c0c07040c245000c1c0d0020045291180140181b6114500070b00000d80d1041c0002c0000380c0f035005c0109003040c8501801e003850303a01c0c800030440b04202913034401c1d0002e0104254402e14540400c980402502502038800c0240031350300c020307440d005ea5006581c14050302030904028140140e0884091a034907031020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899391825 1250 899390575 899390581
    0x20d050a300c020604120e06040306060605030105030f01050403170411220b01021f0e0313030305040302120613151d0c0a0506041805100302121020120a0b09 69
    0x101d2022409039580035082031800282036580c40c40050740d0780c400c640c02216201d50030303541d1a0688a004103102960b80c0a00c040201000003002ea0140b0030051005464450302c1c0d5041c0800c150800700d1580d003003002a89000e0401000c25030001c1302d00100c2c0c0004140340015100c2c2d0400ba40090003104030a40c000c880311010354503900e109100e0b441c0310204001e0400c0780c4a400b10049840301e40307200510149061403403000303000c001c065100c40c1c0d42c00714040c100c901e4031068299900303540d84170343d205401181c0040707001c20541c241080c2a00d4003241c4400034010307038a0144840c103125000488090318812031003c00344400005507101300891020b080900555000c0710719500da07030301d003002110383c00386078000c100040c07034280002a2401c0e50b12680304140f20001d107010481c02030a0003081d00940b482480d40010142c0c940c0c862854001c0304030f02c090002c0504a00d02d0310240c0e9039204403c800d40c00e100c4503003000c48000c402602d680e041e8940c000482507c0d0804094083c181d0541241d91242c041e80c24 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899393075 1250 899391825 899391887
    0xa030e031207110f0c060a0513030b0403020d030b090a0b01182306030402060a030e011d0a231009060b150a02010507020a120c03180f05010e10020d050a 67
    0x10548524502d660f1421100c030741d4040262240001c555445095110585500340351034900094a4841007d1400700e04240c91590680740c07000303442d441505c0c100600b00620007403650500804807210180d04050007c004400045000004011300c50b0206541e42d1000c43e1140c0c0c825100701000749070103050802c4094541c10311030f589240110304801491060351503e5060b003080e40c01c1d40d12494004004d242810150401603001d04004d03403000c00c50795a20034000c3c0c016042e2540b1240d090380301c040182203070040f505d040030006054005601806e1021340700080c84850003d40c840340c1203d58440495110000e141c450090700511741103035032089420540208036603405026155405c40c036402070003203480780300c07003607850390070f80036029004a00310340402200da4050640e07012841e2180c602550400030a908030301a0f03050580100351651a003030000c00c555130340158031042c3d94100b11241418460050300203580c4200500107141480400704a9800d0075000303019001b1080048003491000b43c0039902c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899394325 1250 899393075 899393107
    0x9071a09040f060305071e0302040207152a110f010912170408070f0201050d0903080a0c2c030a050a050709060b03060f0603220f0b070206040b010b0a030e03 69
    0x3106602441c034205a903a85600a030082c03004907500f203000f4006039802c000160400c01e82000d0203000400111000200589461004040082c024110002e150805c040914181d51400700c21303020030400c00030440f80c1c6081040000c1c00985807410600040c0d51800840d604250764260240701799460b18004405001080084511454440d51440c81c1c113141d029440d0340c420404c2e0760207440341000703000920004d00b00c1c948140d51640141411420100c0c4007600c003056803103a0a04400190814051242c4507146000741c00417140d40e401e1040c03140d505600e82c1140e5001000d42c060403614080c8000e0004e460a1200b852020340040a840c41c54480c1c2c10425610b03d40ca1060281003440c000b00010307001d0820044c1c9014440041910769600741c0d02080106c2a04060004160441c81486d000302e1080350051016101c0e220382e83e1000c003620340341804401110000c06101c00d54001d0301c1040001000c101c07410f030541d82040822074850402d9482103004100075445039070346110014480c600280c0d131803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899395575 1250 899394325 899394337
    0x3090108011d0408090619121a0904062703090f090207020102031c060f0f0504110c060403140d0509030d05060a300204090b15010c030f050309071a 65
    0xc0c8855149980c1e0741c00041e8441203a504092518507000085800902c0d10300051140a00003440e081c03c0c202c40700c1d15410310045c1009082c010a120142448450456004e0405020880c01348964204104030224003c8100200010010750303030342440140c4041000d8406030b401c0c04940c2c0329040e80c41e041c0780280c0900714a0213842d4505450310400250a401402205c04860381039014501f4001c2810302d06d868000403102c0304444c103440e0000842e1080680c141c0400130a4010380d03860141c0d140105100440300044c148622904080001c10182c51000815941269040c6021a600c43e62090310352070602174104081c18550404041c0040090000054080301c2d0107800c04011a40b219000c0200403122072240e14110014001e0980d4a00140c8081c809520304188503100500200e90005080314115041113940705644030600c005411702a040e81c0b501542803c000700302c40b200da1000b611404c800c081c00b00030400004001600108103001820040103d0f0603c0080032808200c680c100c4d070011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899396825 1250 899395575 899395577
    0x70f060603032106050d06021b01050a06140a1410030b090403080a1a09071404050a03050114010f03050304032a2319053105060a05030114010509090106030b09030901 73
    0x1810307100240c07114480c1303a04464006050811a90459840c9000ba41000035603000500107021a80c0c2c1591080c0651481044003030000101076007404581031841d0500a011405040a43c5041c07040c004c0c030b0115002031100440e8a00440b015a81085010b45075041c940703500001c0070001d1008054010616500079072000c881400000301d004680a03903003c240d160303607602260b940c0105940d0f5009120340381e248480007102034a03042e08c80001c2103014489034811505699503001c8150343d00d0f9807510190142201c0301d034583c4001d00c0d41d122541d9902490001610440d5110707a8000c485107440200c0d01444040c0050061039551440307003001482048190700e800f00c2031599a0401d0b0314015018200803580003503c441664100002d000120306a80c031659504403100e540c0301c401302002c0000340c442c19524600400d0500d000e01c2400800c0c80d01d07512040c0030b80c3c18a00340c0d80c500b03002d11144a05481e0161a81d0341290b480411650241003150300241c403004001d403e11000308404001401c2c004c900b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899398075 1250 899396825 899396867
    0x318150c0b070503070807030506190b04140913032114060a0602010e0615030a05060c09030d0c03021906020f070302030d150e011a1908180303090a08070f06060303 72
    0x5003a400c3d81c180c0701c200c88840024240500007000c4030b000364072140d0869006000003424081002c203041802505400550310603802041c100036041c1440e408a0044000303480a800d282060f140d19186240885402010b00074a50014061010030740b100f40f000885814050241190745c13043c243c03030054140c0e031440c081c0764111808680940140502074000070743c80c00901e441d40d5100901c3c4a001821785405625006110700100810410003405008180700060259110510420180707401c0000008c10144072440d495540465004150108600900901c251151140f4500000207114840c400115900007082e60014958004090805200c2d80136040098454128103520034000c10320404031500041030040c801d10010406400c2075124850404c0c4c1400d50002c28000220702c0d0501017000100c01030100882207900740b040461b0021104080e45c51814084541902c072170540310090445000007030b4013000c100c1d1003000800120341180042047e00d44030f03d0700510040348400300d1190050 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899399325 1250 899398075 899398081
    0x90c0c0609010b0609090a20040f080607051c0e1c02010f090807150e030a0e01020c0901140d05032104022d0d0303021603051b0115030318150c0b 64
    0x7a051280c00300240700101024181000031081011018000340003580742500da00c00b181c2c800e4040a140310b042050240500c0e115801e142072400c1da44411f0340820019407182e424001140c0d0403000700d625010307498041e90301c04440708039080c014107414880e0004a204074808041490040c1407080141d039084c5c0d00030b122640385130400c40203079800b4200c0034207010410041c160004000b4240d5184600380c03a4000b0800a20003d841425504010001408552103c0c410507447d80e061108404410049941da415541400b909102c1044000da056020341c00c800a4036050100400c1902c800001010b040207010364000240300c0c403003005541c00c0740144006000016202c00c40d544846405810490200b04001c0c0d180070820260075030319042d01415402c001c480c0e03040283c1103000c00d1b258004d03200c3d035075151a03010001d1950b00c05d0000240b4107914084a040c40845980c40803000c494041c50b001c00c100000790018001403840b540710308030300b03c41001030b0703903440d40c0105003498071600078034042169075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899400575 1250 899399325 899399341
    0x11b02031606050a20030a2303041a01080d0c11061612020d0c0b1f0e090c1005090f1002013801080f040204240e0405060a0c0c0308090c090c0c06 64
    0x16205c01200301c03541d0028046484050320030307507007480f1100d001c144015940008064052265006550503211a0012480e042d5900d090114090060000707030000c1a000c500c942e0010003031416800000c0000a8201000c038240d51440240d03003a0100b180070101c0c04032500c0c40c04a0320841c4401d2410050700955018641c110f01460f40100350300c0d0813039407030101030b03903110f4541001000350041e40c206072200400c0800d40c0d0070381042c04c0d48652501c0c40100001c0c1d0b180070411800b01003000c007070820000f040100c191142c5a55074050150842078803040700103a8519000e80c05480000192020283c80325403500e840304000c80310015180410900030300c2c0301c40300001168841d0f41140e0041284014201180040c02d05a01241d0814040b4071040a05030270200a41c00c0d080060707001503510070f21041480184101401026005005140304000707600110b040075064980c0310501505201c075010004110007814441001120070041441c00369180c10b00760030103103400060711000c0b203108940000c0c01c15 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899401825 1250 899400575 899400617
    0x40515040c03151413110d090807111c02010305041e0b010303120603031b0f0c0b090a050a12140102070c0b04170609060a0e03070204050109060312030b011b02031606050a 75
    0x328045c1113030031411000010707080542608200501019010802c48054110034401c00074030341d01c074039001c699036951400c00090341c00020000600c1104550101c490020300c101d8090001d40d820300700890070b650340d0705020b880308040c0e4041d20003072a8454044003c00c000341c900790703043c1c0b4440d803a01d008503841500c0700c0c0215226400000d010074103840c21070312403100240141c0645032280409402c0860555101161650a980080f0124001040041c8145400c4a00300040c01055851a624500d060458504021046806400081c035103403240d45088081d0111000d1907000014500356558800312000654054895183c0c034103407000310300c40400c0c4081407590044105800034030b003e440380044c5c1030013058504142400b0388804c002e0100182c445002e201e000340854000020300d10f1842c10704070304800b101c950f98810940b03000e049032401c1c3e030071003012400d40c511710800341030f00c60b0980f01203032034051303482e05042201c1c01003000040c1c22580503005100c41c80d41035980c1c030345642c801d00c400c5050b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899403075 1250 899401825 899401859
    0xe070f0e120a0215210f0a2f03090f010207120309021f090501030c031b050906040e090105010302030111070c0303050912100506040b030726150a091a0411040515040c0315 75
    0x2020546e04085030314041107810290b2054164102080500040026100c01c2040ba45181010360408020081d00380002c1c00314075404050361380207515115456446540c01101681e54405240d80d522328041503403501c2122010988503240008180c000b0708070041c00482d6903124582c00a820000c150700018807174080c2c1308079046500d04c108030015519405491503000380300d800d50426814840003030488004c10a5a0048000a00010b455410740c0141401c0d04c4e002d07903c10059140401c1074034002860021703003800b00d0f5050b25203a9160200600003544040c400d0b2080d0f1850700ca0520512044501d660080340a40e004481c00c110038603408050585403902c034440c00310094220360302c03d183c8034050b121140c01d00c0020030545102c841d5a814520301d070142070b42e03040e4035641d441111104105011941007160100c03480780d100b40740b07455950001901c141542003402240c88801103000485881002d0000140c020001d00080e070b00400010000c04a07000710f4000c000c119040058000e2030b1440402d2 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899404325 1250 899403075 899403091
    0x3090105150f01030506151b190309060f0c15020901031a0117130b09030706060905011802070c08060c07020a0b0f09270a060e070f0e120a021521 64
    0xc00c010b20400150002c00c0000c260780d802280d9800150355900c3c100d4001c18070108000c00c4109504a490742d100d20700044003036070b40703520708083c5502400300360001c4101c1c08440943c03415510b00c4162180842d00c14031f100310014035101061810306001d0900d0780140c03841c800700307a030200a15065000d00c94280511085c10b039011406251004507810121400c107940072003010603504034092036540d6041485d0007111410040d40011661108204d49402400010921b1010a022039410001c0d1001ca000748a51865103803030340041e01d07030104070340c1c445c28500504081d02034440c685400c1d2007884441d800742d4070891180c02e070950003162030141a02a0303110110700b0300300c03141040c903080d0a2200c4898804400c400021038000750003061643c00300c1c8580329802c0000d0220703109103080c0210001d40d501900d88030034002500c00100302144e01c09a02c0d0070144086400e80d49615480385018100302d0340c400b002e034110700d1a032484850740140c04002c111a4000482c4000141c050100000100c1010380e1184c3d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899405575 1250 899404325 899404339
    0x3010b010f0e060a03110c06010812030411090702010e010c0917060108152206021b060402030a26030a0b100f0903062c1e07030803041515030303020309010515 70
    0x4a0103062041c040c0004c56054240010084020b082c600c110350091610350117294080300040c0605801840400d02c7c8141e0404e84908505017551144c00b2604580f51a41c000c1c800d0100180046100350400005001420000c00c001c50925400804212050140c82640c00700358011800e044c40c001101d034104d80c0b00c5000303030020095101d0401b0001c40050201c80c0111010b13130080d604950704a0302021001e11030800142e460800c01c510048140c60924282d0700c6070890405c000260310080340c0007c503d13500c0703c688100c0500d440d152103840142003040e400c0364070b40881001880e01d40c030b0703004001d0b051040724107039010100da840c103c076240c1660303e0810010303d0b1844204002990f43c1c016081c1c1039030003800703250b64411711441c0030205100c0c0b6070f07481354a40c020303803907000b00e85601c0c0d01c01c441140e0030101820307005083d506c0311860381c48050001000030385102c840360140050f0750b114dc412400d80d4010703054690742d20300340103010350406e031030305511035181c0700c0441e03044c0204000c048200a0050441 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899406825 1250 899405575 899405597
    0x6081b0405040209060910030501061211191e181e1703040918110604060212030604140403200a0f02010c030306090f090308010506091c03050c0105040b0603010b010f 73
    0x1220280d0044084c10b904040d05004941103940c90f100c00b50400c0c0f009031780020712580340c420b00529031804124009010b600d081b01c00400740311200c1c21680024030300e6801001d801d02c04401140ca0340302081007080791911845030301140982c419100307030300002d116594861160700c500c0040c040c0218a841c002e92001d990303008100d6a20f50410414a05440c3d030180d03400c2980d2042ca2405a682004c1004010700c0c0e505c071040b08028900100c140d2400d41511028101424070001079030b100410b40703842080c0c2001000150841d5596003150034492181d2aa0362614102460701518000004414512104a50072101011500054a0805e0982162008034484085d03001990718900b8090150209a1070744000f083c0036829008180071428541000100c280180c1002044a01c06801c01c42c81090b04020482c0f841d650340c0d0311200c521906911422202a2600e001e0b2607910400010148075400c2804000510420b10001442100285c00a00900555000441e2418292100540418880410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899408075 1250 899406825 899406829
    0x20a2d03140705030328090b0a15051305060307120309170c040903020c0f030601030b010e10120f2001021c050708040806040309051806040906090f0c06081b0405 71
    0x40c07051501d803034285185402d0382c5403140c5003107610072103001c1070544100302100901d08800d8034003810303072a008100b003100d100f2036600d8801c0c080c0302405001e1440c0d1540c000300c81c80040c200065008101c001c003421082481440b0500c040c1a040704c4580c440d0044400008964481000b5000301c60781c180e0b00c20750901c1c06e0080c4540003407042100c003601880741740c0780c401c00c03030310380b03101d9140c60314001e070014498480c03070f1420055005040109035000c0d410001c010000500c80e0403144d070540f078802e81c0700b0680c0e907115000d540701e141d100d900c1022140f60341d0b00c4000602c5600061802501d000d8141ea075150ba9000203120000505940d416005a00401145906a009000500078100c0b2850700500c0c06a5544444049421581085000b86c1008060004041e00561000028030041d2150003140d0b0204c846042c00c00f100804007070084ea20b6034117100c10051207912415240c0d0380030000d0b021001103420441300241840c040d000205ea2140080342e40b107111080804ca1400040b1171044c039280c20141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899409325 1250 899408075 899408087
    0xc0317040303023703020709052a090d081305030c06030103021c06061d0f0a050910050402010c060e1f0e0304060e030715020607030605040c0e010e130c020a2d03 71
    0x49150250001d02070800c00c2c280e500904c0c02c4800e000781d00900c042030034401d444046480192075802d007000c0007034030b011440310700c501c505e4022504292400d40b1100380c4800709070303281c4e030012004000d59400141c4103e075250740d0a40e40140c480c150129400d1111150a00003544000c3c00042d601c03503803813014a00004901c0c4600c3e13007054800c400210709656a40c20a821111091b03d14800c4214450100f210f4403c001112503408200c02009024504150038500d84078843c002c007068040380c03101300041c19a406144808841548204d04100c00ca0720041101c0c0c44440c1a007120751190390908000c041102280a084440d034407607000f031880e2518040742075608440110041d40c00d4001d060300040e140d00e4500c86581c26161903009410380d0b10300380100408980342c5070803140c40f4034a401c0c15004d41c02d82c00680007820007000e0070070b102e0740b10751503001407070806c04070031400a2541032040c0d8200203070780406c51581301881782558001e848030407800c1150001020340c407210181905094040070070b10400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899410575 1250 899409325 899409373
    0x70608040b0c0306150301151206030305030c0f041e0806090d09210f060917030405030a03020313060905032d18180a06051f022a09040c031704030302 66
    0x70310340385880c0c640e2031610940b0b1b08240d0050039107410f0a0702c18132440d40c00600c00b149210b1040c400304041402c540d0040c1031800041e041c014881400708601c0078041010041310090454200340300c0c45068a00001c1e80806907500070320215000c0e02000c02c0d545940021111507a100310380301e000d250b80c140796000c288101c02071074040709000f00032036803400b0460401c600d03a07800c0c1c0500808100c2c0b5005007021480d10000d00c10030542608c04004020202d9408015505000d429150150340c0380c1b01c44017142d50210004801900080c03800c01780c00c081060020003000d5000800c5542491080c510222094041026428182d41c1404120242035002030540074210340c0c40c003c015214201d00b64035031215032101241c60724002551180b0500852030b1810121004013000d617000c14211404070002510341d000202c200c070b012040100c590410f5801454400c18501d80680260058506401c0030f00809500d131100f0b684d2220a40d1840c0d48070035401084030242c0750560000c100501c064001031030328400c3c007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899411825 1250 899410575 899410579
    0x30d1101020d06031b06080c0702090703060e0a0e07060e0312160b091632211005060109081c09050d060902010e030106050a0b03040c090510030302070608040b0c0306 73
    0xc000d00082d000142c4030300d101550041200c01d02c0120042400c0d0340c42072040d0130580c103109290b01005009003500c41260041c41d07055802c4007203902c81d0b80060b4007800940e00000c2c1d407200c02c075080000d41c2c44141c3c440240300c9401c00496603250707500c2c0030654410341c2e5105200d4140d0400c1c145020302089180c0108008000d04424040207120b90320790407080b03141914404040d400969050b0000c000e030350781001c00ba104c00744026043c04040364040720024260000680030110701c110400326550b03100101c40d07428008084c002e00c1c411460200640340c049400c020040d0a03d000081006544540c482c40b003500d1712400103200719582c52014100071240340418404000138440c004ca2651a80010100d40381c0c441d00c800701e41030b1298070001d0106070b41a05524001c1c1e160a5007000b03103944403011041110302e900c0141c3d41d2525142020000c2000c3c82e0403041040d4281401e00200c80c800180c88021203000358242c40b0140d40711030080303500c5c0005450141000c000380d0701043d54002114002c540080300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899413075 1250 899411825 899411827
    0x204020f0c010603080a0f0e0a120606090203130516050904030809030906120106032313020303220f06140a03050c190801090f27051005041b080309030d110102 70
    0x207444141e420b4601640003190400800b08000351500c0c1c019011420102c1c40e070401501404070320f004036601410034070500c1382101c400307035102d4103105050707005901400c05200c0c195660319200c000e4803031903501004119800d105d0700d0091014070f2a1050910280c40c0020808110b40d180e035101101d03220301c00761000c1100c7c041040810b002d03560f003034024600c1040918403030720310350714010018040381d41140b003c5549484003802000b11403804030203240d00821500f444102001c113800880d18501444100306201c1d03d101c20440a074107180c400d0034003200d017040b05d445c01c500d485a900315500c40d1a0718004c043c0f2001488641040fa009030003166000c400c40c00401d0900301c04050703070101310440c80184070101d00e02c1d82c0140300580c0140540d00120086c0300341805024100108240346400e081a841c0844807400401b00030088240005d5407500e0240c0001d00850074207080c821810b200407a44607000c0304980e0710000d500c840110640f050044014080c001161510070142c031420b242c0100d00005541c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899414325 1250 899413075 899413087
    0x13030216030c0906080c031f0f180204110f0901140708030f1b04050303030109050a0b030a050619050112260a09080c0109051c0807080a080901140c070204020f 70
    0x90300d011608001e501404180c2c2c0050b18000311002290000d401091940e004042c080071551000a8010b040860425091134440e546010300e8000744103540a14042c14144039031407907062000c0050600141c001c0700d08121000c0000d200046038403070f55801101003401440100314943c02600c8a200c0c5000c41070540d480d01c0711941d43c0302d505a004603030b00c0d0300c040a1789081c415511620f0009010480810311603524050802000070b07902c1c0014810655000e0700d8030000740ca0341149402c448481c100140480320392103602e142081d141d1f00200c0b0750400c0b079102442c000b900030f105070046504031000154080a00c90281d00e4140388210300b1600c80920f24400c071154000c1204170b00c024254498150360320483c0034101304849081060a0184c01c1c10408554404c0c051036a034401d1820303140c0c008852507800001a4503240b607880c0200072014200400100706507801d0354011440d5480703000030b94020000003101c0b6a808542c81c034191261600030b8014000c1000605040e401403101c60640707021103003414 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899415575 1250 899414325 899414353
    0x3140306030c1c050601061404031b0816060806010305010302090103110114031003020a0b0708190c02180609130c060c0201020f010e0c0a0608091002090105130e06030712050303130302 81
    0xf885019110481c000003030f03103103c20300c0300c20720425025042d0780c074003031b4200490074504081c203000743d020103065504d503401420743ca01c0380a90740b03000804409080c1c0315a6485040d0001400d03840d44188404206190001b070300070344c03081c440c0a05032507009243d0f004a13425602d51003051036443c1c003e10305001d8818480c0c0001222400950700c0385517003144910740d2909504c1801030200703656100454114043c040700000881c2c41c0d0035150302e418001989040084008000c0360740440c00040039420140b00811044885040017000f4070560007903c03420003035150070285c100c9003071013400080c01a40c1100800d2140c10301c83c81019035001c1c014811a215041c0e542d1103182110b05024000000e68801100d80c1d0709400e04100d45d500404c4142404c2c0700d03520300f0007421501c440000004840040d40002c40c44001d03800394040d505042d02c48c80b6180c04041d02c4126112540405440a40c0710f03104280000440c1c0c0251504010010b80c05005941181c82e054807909585d20074400850075400303003002c480820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899416825 1250 899415575 899415589
    0x1d01051b0d0b130f0e1c0e031501030c06030e03070c1404061e05090606031e13080a0305040302010e0a110418080f12060a06050a08040809130e0c0d03140306030c 71
    0x7901003c0c400007510880710000500312508880b071410541c0141140d004204105520800700000905002100821940010f414010790101d40d19941d111a8000710074000018860415140261000c010030041c801d0f40300d0b5030f401106801400101070190501ca102c40319403591004d140041d0022038100e442d0b071004292260520100600301d40c0900c0304002e6031400311402d5800c000190742440c51170401c0000d0030f00c100c145c2c00c0f446100c2d140c0000400c00c030700a9006070403825600406020f86490049000070041c04060324140c0056080c00d501d440c0000700420070b1585140d11440c1c0c1511031511501b400042c0403801d00401c4541410490480447c01e070400824100c104a11056507d029902d510860120050401030080b0314011b4140a041d0b00711040b100e45504600304060181c3e10740c07811034594440d00708038a4000340f4105202e81c40540c0341e0403201c410011503044d079401001080903c184545642405000654045485601c078101c600003140c101c40080d0a9400c40d20141c0046864 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899418075 1250 899416825 899416849
    0x30b030d0c0f23100b13061a0703180e070e0139020405010f030606090b0105030a1802041d06010b09100c030c0503130e07082401021f1d01051b0d0b 65
    0x790785d8841760000e80b1460314803070380351200e454000700300205c904002501024060300c0c0c03500d01d030303140c00000c50300180b50083c3c0d05405c8901e00c07481000310440e2035003411200d02c40103948030408204144c0790000d06600544000300803043c800180c81d0a00341c44129001c3c8203080c0784040b401c00e20088964405626680100d03400780c01c030043c1c1c00084600c2e52815404503001544000d141c10b01e44078841c0650380c0d00a0403240c114800340c0d00862a0701410070661030340710448000941c400c1c64030391940000e900980741d44c00002005c034261001da0707a80740f80f013410520900c4449980301c0703e11801c4254081c022a030301c002c0c190081ca054092000c00c1c0d03030744a1030341e402100c0408032404540c9003080400b0582090a60000c900e00d0042c1280c2031031200082c100840d10540f000461050034414041d0b40700300144103c034410214902e00c0c0544818480d0010034803410400702d81c0c481410010900d500502541c0d0103622641c8400c0c5c2d200400755840e54507900803174007000590f501d03104920815560070042d403007 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899419325 1250 899418075 899418103
    0x80f0f0c0d1a1816060504060c060209090403020d1b050a0b1819020f01210b220b0405070809060a02030a0f0e0d020706090f050f0103060305030a030b030d0c0f23 71
    0x718082c0f9039560701d8001400c41600c0280d0030f0942c14414103621070280c40445000c0c0c02c03c64842002c40c6421000b0b4002c0c1a403207900400300d4800c0000303165001980e03581c800a20b48070100f403045905012100049141009411070b809104103074001024070294550064100c45003404100a0000050925204800050b46030440c0780200e070542c07421082030500d158003401c1401c004001001000c242840c010f012681442c2d441180702c0340d9448402200000d020049030040c0020380342407030007006100942201c1d000b14501400100c880d80a194182e015440c140300420341599501d1745030000c0c0d0710042014411a4880b074004024400e1402142c12041d0305401902c003001c1e2901000345407011680c0326500300601c150003009484141d0202506407038082e01d550700400d200c1c03070058001d40419480140a84000100c071004d543c1c1c590302040301218214203459502050980031282d9103032040020380109111251070380010703a00000c0050716013400821113050210310000301c0c00c2840185001c8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899420575 1250 899419325 899419351
    0x9010c14010608070b0309061602030f040612060b070b16030207020907050a030c02031303030e041404260406080c0703021c0c0303180305090d050c06070804080f0f0c0d1a 75
    0x84071400f024440d20000d801c14840312070444c070740302c00341c3c550b10f540191401807825200120408054402d0040f611040700204880303984079550b0030024991040e4014550405142100101d910030000c001c840c01250400c1e43c100c96504c5200c03140d080038428944060500d50f0070007050005846180046100720032030b40360306480d10140e1801030300340c07490304044400f15001006500c0140f120184c3c0e10094a40603c0c1411034031101c04c01140042515448104400c05840d041000308560340b01051035041e0341c0004a40352002d0070240b922940514003843c000300f044c01d0006503082801c0300c050000c0a020b1f10456080040e08202c48003024050882d42001501c0800e02c201071503058082c44001c811420705050700400d040d1401042c0703000d4481118400c145c0700c584402405000c1004e9554a54010b00c02c560b18502c40c0303489205c0ea030051281c030546c4e00421440b048600004280204500b080c08050510b5240a00c00c10440003194581166446204d401c0e102c070310b52086504900c18440703041d03070b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899421825 1250 899420575 899420579
    0x1824221203140c1206030f1f0f05130201120b030606300609070501080108030306010f0921150227043305030303071d01090305010f0615051e09010c140106 68
    0x992182070000c0c1724078003d622020442c1046d40001a46044400306c0800b014510703c03e000491029010f026480720a20b0f0400c02405085001d007010799080e42c2c400d07243c088007002444103c4043e5200040c0282d8150080400160310741400343c0382c1d0200026225190010024040c41800052220240c100c0e0f01c0e488602001100041007010101920703090034007499035854584182e41e01d00c4010203207410081190030301c000b01c03030060740702d000038002010411400101d41d1500e010316011200044d20700b180e841d5104078000301540f080741e0a1449410010329100c4000c00c5044011000c4039140381c000c1d645100c403100d090040d0948190f54204200540c4005c8000c40c580940d02d00a40c01540c0300e40c0042050204054101810741c1051130304d00ca08540b581d1221006a41c81c04495001504d20b50070060036a044181541c005025035a914a2103188800e40120848207406030800000910480e01c00c0c094013a100200a404003010524284030900c3d040ea851004100c20a1800c446c0307a910303141c007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899423075 1250 899421825 899421847
    0x30c030909090c0b13050d05060f0a0501140f0f19090501060318031b080d090b01080d05040618090e060a05010e07050d051824221203140c 61
    0x300000801600341e0910510340262114080b0100c28840c000c0301d01d00000c1c41c961400b001600e00c4008100007481d42824a21500b055511484119190f00080030780c5800608003003100c0c4507190580f03e0501303e03030f44040e20080038009400c141030700709070340700b040902c8090341940d81044490010b02c60322041d565592602008909450040e0817200505042021164100046038400c9541503014a0021403103d613131481c80d030300305d203007148041c0814a0014403020b00b045190072282c0340750702c2001c814020340e0341c030701d07130740d0384510354003020f42c0012390104000c1040510030024003c3e51120301815210046d52400181c0c1103920070f4148400a400810030054248824405e1900401042200a840d841c00803070081052090001c0310300c9080e03448000c05c0e000c180301c0140e41500a40320b01102d00c10f910010120320028640041034900c8400040010340c07182c21144041098181c10b002c0740d03526070540d03607151403403a81c66074101c0816541d60b9400810200c0d4040c0c1d42c0c000c07030380703020303820390b18452080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899424325 1250 899423075 899423087
    0x70e0406090509030f0d090b0115390314031e0106170f19050a1505010c020d140f0304090504021e130e0c06040f06170c0a0c03030e0109030c03 63
    0x1001d07007501031924080000300c0102200315501401190005e680d00d0f02c014802c00001e125010015140a0300308001203904501d124010807803414544801c0c4001c06510000c4554501c1b003040007407004040d449042441084080d01001c15103e401e068440d526824403c3c5120b4004544000c42540c01501800d00001205180c07405449a881c0c040300c1110070002e815620300700a00322180c400c8002002902020b22002d00003400c40c56000244018103020f080c01014080a00a10310990104d041c009000d40c01100c0e0000da00390701403d5403043c10055203a041501189190b004424016140038018151050000304084d00c0c81180004690400e40107218440e01745a00d05207040310a122644203d41d030705981c1100e040c25915001c20640c00c8648020b0030180100c10740d5802030000314011940301ca04282180c1a40c0d4203558044141000b244200240d82066614a015803020485401d00c5841044031083c441d001382030104184040380c1c1c2880c2120300d400070580000da20684250b003003680c400 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899425575 1250 899424325 899424329
    0xc2e02030c0606190b120a0605060a08040f030903080f0a030c03020901021e010216050303420f131a15040909021201110703020c09160e0a0b03070e0406 67
    0x44000c600304006040c495944640140001c0e10450000c011101c407541c1c0307180460007070003c410a4a40310604d444190103e542c00f40c403816041d50404a004c5003d08011098402822181e0703141001030716192510824030310300c0c0000f5020404444000700104031114010103058481c5400c0c07a90306d20640c64020215802003083c0410140108010a443d80c0d000481000070900d1144040c1c1045014568900921410300b21250f0070005035015000e204000c4043d41c440e050b030340c0c508007500c00203e0b81d21152011041c00a80502100402c6c94020b000c8064015032441000e080c20310300d081824001103449030400089005580c90780960138805c020741144041c40201a103940380d20840d46c0103802d40c940510700880d500183d85440fa507056554888500c0280c2050744020013041d40c60242c0450301350f00055081c7c01512442c02c824441e4245080c26511908400d0007200f071050080d00c003241c00380710422080d80d10581050011910044401c000d50241285840c0c0c2641d0080d294288400c2d242c1035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899426825 1250 899425575 899425577
    0xf070b04140118240b03100603020f090403050316050d1503030e0102060f010b0d0b06040e0609070c0c060e01051b011d010e0606061c151a13090e0c2e 66
    0x303020000310011070516a10660781c0944103208844c98810000740a0410003507810700c504026001064082e6020100f43c1c0e00903240315103400d81200034480c0c141c20944005000a1081001a0700c41140210f207522060181ca480b03880c0420070704030841500c81a0385850043c0c1c004102c2042096084035040d01c28036000e002604092074689a513815818052040112a1074001002400c1c4401a072298012102c020b0072513481e03503290b10088800180c100c6425008440c50b40201e81c10b03d0090380c042200d10303071160300380c00100c2c24402c044842000407040e450500406001e07411403105201e58400302c1c0b04c81540002001c1000007517500c2e04040302c540c0c000c11a4907050f0b0502c1680b0004ca503407a070102c0d0607a8029a20280c9540006e209100c460302c90900380e10307000d954550714000348a0002200c4141c0240c000c4508210856480351241036000780070042c2001c0208002d01240d003100d801a401c2005039603280c00040c0105400030558803110101c1e0300800714a461840800c29109016001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899428075 1250 899426825 899426861
    0xe070306180e1e0114090f0d020708030409091a041a1b04091104030f03090e0601171b16150509010219140d0f0f06060503060a0302060f070b041401 65
    0x20082e042ca4441c00c22144586090a4503003003000d0f040803d400a12103080000405441860900e40c110344a401d40310365a40f00b07010700314070069036510002c0d58400b40c824807005149410324080d0782e80000c1000200480f8000b4004044180c0c003201c1d5030995200314012021003240741c240e20000d0b8034000c002030040030728001d514103145422011100303841c2036440c40040003507002021922182c2030b00565000400c411000c2c0040400c142d80031501070100e540b610046034850300c0d0640150b4060244010041c110301d01100001c00d4031f8805840e42c81e1880502244514009100c4503003060960140019603015980842c0421400a684500c0d030707120910800850918814249009280e2000402442008503c103000e5240190700c1048520102442c00208008100c10300500060320142c000c1d103c0700780c540760b000111070b03004d07100301d0744200b40c021f140107012811a806c003d82c90704010003202182c0001e0001d1340005440c00c05035401940504486013441025130f000c0c500b52840c4101d00c0c60160741c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899429325 1250 899428075 899428091
    0x105010302160b0a0908030c0c0d02071211010309051209030615090103080307031b0c020f090f0112050c04061d0c04050630151e060306040c05040e07030618 69
    0x82e24a040044042e0700c41079001c429202c18243c84094001e400020342031502c004180001d140440008004003030408040d00c07002e0031505001d07070302c8071003600c01d0b000e00500d450001070000e031500075490195801410002850030041e15088d00d040307230f03009140ca0b4000c40021954034910302003044552103050864800140d545d000082000f003081840000c1c018100800441c010301e01a811049201414008808030044400c1c4010143e00c0401000d03800768007801e055942600300455624890800924600e100d6413030084038801015140c182918139000c1c400303107000b281d03a5030f006210007010710b2412102515108416000400c03000742a0000d20b42c0108070800030f0352945c2040d6040c6400400400204a541554880400300494cd006400030541800c00c600030b107001591242410066802d5410807061101c55021306e0318150549911880c188000303401851716411016504043d032400750b04180e520148801e10306000e6400320003090b180c100501044440d40c030b4440040c12081c1090100c80d0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899430575 1250 899429325 899429347
    0x61009152108120a02090a0503011401170c1801050a050a120b070c0b0f01140a0303270b0a030504060b011706012d180e06032a0405090a0b0105010302 66
    0x204400c001d01100d007001044003010300c903540d400c0e11800c00190703007514100d18011007180000d40c086402140f145440400c007080340d080512620542c0440744002c0c0300540d003003003c0c040f2464000c00c210041d0344600ca1659000780c407050510078090b60403503951045541000c00f005074180f41600f040e0300403020b1070001c00020004100c0c080103203402202c0030101d03480e00b1758101e45501e600e04d0090988011041800366507075041c4040d134100c800d07016134003860102420070000c1407501484043c0010b034192980001180303000d005a0200e002d110030078141d00799070740341130342868100c2c2c40a03001099a800800c01440700340d000b81510f1490910380751038070900080d80c40c94070550240c03a8034104008810046500d0400e480c0e4058040211040c103900c9030012403004040102e601840c2e4800a02c085000550000f01e140342c0b8011800100a00b0018004500c8845070101c0d804060b009000030700c045c42c010b81c4442c800d103800b0b98488000750031032031420306049504a8060f84124105841000000d6a803 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899431825 1250 899430575 899430599
    0x4061710050601020c0102102f030901060b040f171e06010e0108010225050a24140702150717010303080105180702070b0703020309060d02120114100e030f06100915 72
    0x80048c0f041c001a0704242c1904016041c204250071103d052030041d500c00924008102461246480c60700034851340c0e46034081048180210b05ca00921a0549a41400304440d841d5241400042c0396003140c0e030f0f00c0c0803262002c1104003a107600301020b4010900500c5001030007000300d405821000002d526021100741540012880c0c5074101841e0003002e900401005004e01590441070741051104900907109545070440c00700752045050154a04408056225504441d49105103a01c0d0060804080c4d003210400c2d1062000f403034001042031800054100441c0a482940a50301a40d40e0481030741c10202801800c402c45600c0d64880f0140004101000d680001c0f8101540c656400f900c2d190401460140e16601039031313041d650b00201c045500f03c0381004560113403d5480c40c15807941d8060b41d0f40c0700d62655a0203601111a000b04000580860b400c3c015850a80742c20b0014040b501d01d920303000880303414403c09441c0410002d4a504042045212900907136145044207454142040d1a00c802c03d081 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899433075 1250 899431825 899431843
    0x30c0913050c0d09030c021801080709060806150a0801020430050a11030a08042c130f080903010e0d020c0f010504121b12060606050403030e0f04061710050601020c0102 74
    0x83c5845a4910b4201031050f9801c150301a4064a080c602d41b00b0740115040d421400d004142c2e03144101c08001482d0440d030b028640c2183c4007080a0052603c54000105110100c00402c903040700c81040001090340003480103100400c00c1052016200400101d030003000078508242e0649108c0240400010420105440c40740c80d510005507812040d00ca808070341021072000380505140404030300011305481042c40c10a0160107000c080700c0134103503100c217001468425191090200742034840c0c800000c5404005a080c2c0b402290450300308044140040c0c02c1d80e00705504103801e07401c000d4100410351b404000741e00951b6800c581d581a00403401e000201a4040e07480b55030348142003600e0800520000c88a1031209044080c41118020f84410400000900d8040121102c1d13140400000d0040e02c100d081d00c06985d07140e5a4140b4100810741005079456254601c0d80e4071642e140070004401c0d014070960744500002c9409050381c031049a00810464100814250644d0000304204403143c3e40800c2050b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899434325 1250 899433075 899433097
    0xf010308090d0302010e16030b33150307020a06050906240d0203070f080d05040b0f07030e0924041107020105180603040b040615050604150212030c0913050c 69
    0x4a02c0c206418200d014111004001e9028020701818050071403e070301840c02905e0113035003c01c0031781d1030b0089041d040458490710b500d446081864050f03050b002040b4000e0901c00e00500381e181300c0f607400400c031030a40c2c0150750310380240e03201d85824010000c0305e015995001f00010081d2900340351800b07071002d56200780d10600420b28a10f40714078100b955041000040690090100c484854452070b4a00c9210018056480d4174811001c04d030b00c00a10690450303081c1c5005031403031420241c0b18000d0b812107030850b0404606012040d14140d07032941300c01450601c100c44008080300d8124201c642c0c04c928a1303000741002d010301e080070205c480e040f10130b004a840e071740e50a03c0c00b9507581d00ba46910200612041e010305030700580c00070500007400001d45050f40940e0155000b00030b2560030810200089c1450300c41c407030b04203c00b4881008811400760340980c0381d545a0041e295060380c980300c40f44440d4001c07a4003070b10380c00c00452400c180e810840140f2110101d00c08080102d070030000d07a0380b0007130f015031ba10700c40d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899435575 1250 899434325 899434339
    0x614040e07051f050f0f07140c01021b13050916050301060f1a0f070b0f1e06010f020309060309010c020c1503011e080f010b03210d18120f0201050f01030809 69
    0x1c0c42840c403804c200c407121511001650f0f06c0c0c2c403880302104002d0b401901c0585042c1c6040302c024078620f40201d81054a800140c008150a400300d40c1510f000042d1842d072103921030120b070003400c0c0131140740c0189442506400c025102c10611251201c1120000b0b0300b2013402a85011010b01403000e0104034031080e00c4000c00141d0640309403032000c4400e41301e68119001c1c100c0e40810203504004015944a008907001a5aa9003a1b5110328600440102e1070a80ca4149102000801c42e9940113120160019146106681c40c1400040c0400c0560784252140c007050380d07540006454160f07050001c410b0800c030803114072410f001c110203562940c1c0010b000d240007002e0244080364802011681d601d0003000c09100381e490009a6104440c020020144518006c3c000e0403415020100c80803000d143ca62040c01e0070a00300038510f1402c4004114101011407424100e00c44240401c05081d000e030803898035075680c0216000320100090959102401c1403038041015401400000c000b0130545641c2ca505503540c07 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899436825 1250 899435575 899435629
    0x2011a0402031b04030b01140f06030f0403091e08100513080d0209040504030e0307060e010c0816170a180f0e0601090504181403070201020c091302040614040e0705 72
    0x3407440b624040f07014104280d4002000070402144803403c03812519410740000c0c10011364011f10640300305500515500c0081000043e140c00138124103140c12034041e25000800e10b07200d283d88241c0b848201180c881e041140001000100da04010b10505915038007824000c0d400d09100020260044d040000d1002101181c003030200b142d154107075204440010410700c40c0341841d04003d083c50100c181814080d003c0c049010614a0241280524402060351803c2a164803610303881d4283e0407402540501c00800178019012510715925850310b491240d060a985129541c170251400342a10603080c07004100c070703a007044954a107424410468291484031565030381c0d00001207600d501c8540240d03030710034500409603c4041b601c0f42000300b110312030109001d00a1180540310b54a0017282c02c000d0059214900850050403d00c244c150401861400d03100c116030325600040a85050750490815260011103c002500d4103008a001e8040140b0190448a003000c0200c1d0240c0c0180042c0940c81c5840503d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899438075 1250 899436825 899436841
    0x31b180a1119030c020109150209060c070306151202031e031b010c0201150f0504090f1403070210180306022d03040b0708091005060d0f0515010602011a040203 70
    0x1da82180401440e61565807001880120080120300d20000f842c121100c1d10450051048040043d00000c2c4004142804c440c01c0e4042d510807440690054014000c8807d198010000fa2000d0b40c8147d90104010720582009152022641e20602c11003110000b0200980c80108007182d20b6880d0a0a01c1c1c8456603860b805803031071007070034184d045200c0e080207036022052040d4040c015200e0154000d2000c4c80c442c0080c8103c4c0d0030747c2d004014000c0c01084c0f04004a2074a580b048500500c201403000075985207403074601c4108680c0c40c440c85190000150b071030452504050300900500c0f182441c03500c0048011804000c10710700d00004101076800640b003512a100c44d100074a095100032408440c03030024810b0401c0e00e410a4508a9036401d2103800702e1b50690285501030b114000007401042070741341815502002e820050562a0415050342130340c0c0115000100100c0300902940c001d001c05505120440341e0103030143c2c024800c69244c50761780c1c80040042d001c079501c80002120b002d41c8a0301d135101 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899439325 1250 899438075 899438081
    0xf030c07050a030e090c0901200c0310020306150703020a120918090b0c03160c0606170102180306130b09030d0c09090c02030a090b03070c0b07020c031b180a 69
    0x4054490700c81d11805000701540a02da94040d00b10517101e50a02e511105000d40090013205403050103d03c040a01c44221208810103001c000944403c4402021000010904090f524a0201103c03a000020465282003103200c0e01240d400914482d0301d005200e4800a45462400c100102a40c2c2d1401a200995200d0383e4001c0141c00314820038207042406024a50090a0010701118085260310000b0500007100003079030b20580c03901c1e0040040d004410802c0368440a484021904590f03078503000b2844104100242c3c000d00d079800001039071182c0c3c006901495600c2c14002d244a540f0040802c4814031440c04030a03080303035000c812120310b41c8601d00303400e055010b181801507255191840e21701451f030384030040004864072414100301059170100c00700d0305e910842842c03001089a000c01001a409200001c59219a00d460603405005055030b03980c051580648a890040c0c1c0003803921050f80c03a05112403032032402c02020f02191103c140000c24207410010145052440c180400a010081290 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899440575 1250 899439325 899439337
    0x16021f050411091e01120b01051005040e010b070b06030111041412010c09050a0f06050403030509040f060305010204050102071202090c16060c021b010320160b0f06011b080f030c 78
    0x400c1084680340c00c0c4d0f0103400c002e16a808124119412500009408904c0701c12074200301d400181b008000ea09040a1082e0304403140156800c1000804c0300107030080d45c1c2d10340c050180018901003560381e007883c181030303096040c0540900c1c820392409142a0441d8615801c56080f5100b44c00d4256141001e400003428000d0f25041e00310040d42000c0c041d80030560700802000599001300c441440c2e180c2c48843d50740d03103104680103d4000c68020403060021a000d02c000d80401d4500900c041802d0348a0405c580c20ba40003540221a02c0e90041001e005a40c1c052010201501215901658005080d00010062030f80500b52803c86031000540031400140501c540c008540c1042050019401c0d40200030340e90340307206040c01c105810240501d01550b219010b0808403400c111007040c50394001041c0e50000c0e42c054122500440c10342c1d00034070001601502c003584568039583c40300701c05140020014141509580058a019080b1400c810000d0390300341c140c0c0d0000448000407500d941e110005141d2510450b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899441825 1250 899440575 899440579
    0xa0e010b06030109051b0c100b04181407090b1c030201200a0e090f0402040c050d0617060c0702150a0e06040e15010f0e0603100f0e16021f050411 64
    0x8004a05061541c002d0b90081c050703040441daa1b460301d00f00403481c90060000d841c40c10740120501142642d0a500710126120b270041001810802569402c5401c1c03c11a10031250080026003000d2030070018070824006081c200001e2101241c030200042400040092903041b14080241c81c1080c50b200f5840f00c003c0c43c103081c1007551a040780d2001d9510f0380e000030722203100188244050b1a000e040c4011554054514400104180d484070382c2044040e0482022a004104090210340002c44403405520000c040c0c04603820004c0411f0030b00385042590042c5020000401013000d80c0c0180c13034894a808800c84003104087d1169240074013101c210340900c503107590145c8045070200b002c4051204081c0582040c011043c4080c2d404001510140000030380340000c20440940e0702c44c00d0500500030759100064001501e2459103070f1180e503040702041d801c89510b80a0721410803008a1001c040c5c0507400041e800100400d100c124500d00021402400d4141c2642c0c46601040c00c01042c602c25403184040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899443075 1250 899441825 899441827
    0x9140303010602301215060f07110a0e2206020d0501090b180703020a050702060415020f07140d140604081c0203130615030506040507090507170a0e010b06 68
    0x1650342c0c003d50359449043c200100101c6941c02141d03428442414559070b002d162806404c0803421026134159031002403030680208040e01c0303603065542e10203004004502020745482d494a0050905007807040c10038041a002d990714490a00000d50301400c41540400800c41c0c10780e5a221082c4031700c0540c22010001000315001103141c98119910b604003d0503500b500404000c0041904108400b542040410159452600d004500b040703110b5001040c4941ca076080441c0751142d15804520ba60b406a440701c001c0414500710541184e03410310079560141140402454914100f40e03400d0450314070704a6803403241b030321180600c0800c60702c0d20240710a2440d500c10764aa030324140c20000d240d036110000412140b800f428a8803000d54052080c6c0e030007102c1808612601644960300c01c002020788900c10945081c41c0080080002c1040140512480c0300f940645525807030040401c0645001803e01e101b4010700c0c2659185081d8008401c1e0780c80712091401144140450001c00d0051403a03a883c2504050 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899444325 1250 899443075 899443079
    0x3512090a0e0c19020a0c0335090301230114151209061f1202311b17040303020f0406050418060b041205071205010e0f0615040914030301 60
    0xc030806003082010590740200c45030503c803030480c1c0361404408000c00181008a003400420794030a000c0101c00803441d84c003c000c200004107440041c070781240080d4021000108006281028002c401514940704000601c0c9445000e0b21020581d05018501e811118040c482c100c990700c9514500094103850b0100f0354542601181d40400c00b1304440c811802d02c038041c0480e1800c1d2003080045218040080a0000c041c20300421300d502200507102640c2c001550301650403a075045c05501044254805a03001100e8240e400300c2003914201d13082c40e8980d4407501910400d040c1c100008141041c0e180103203400b150389500d0160024091414010306603400403801180b8160004002c20039240034801d00802400259100d2055904a024042100030140401c0201d0301040d070721151021b21030400d4400c40da445010380009503101c044c00b035900341c0d100e41e00c00c01c1c07001d010b00041d000c480f4204094001e6241030320b1000c60050a407a03505001c1e40e6109010014400c56049c803028611011058a903296 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899445575 1250 899444325 899444341
    0x7080307031404060b030c06130e1005030f070801060909021e1216060e040501061407060b040207230a020306070c030e040c0503100b030f0703020f0903073512090a0e 73
    0x105d0604140a441200048902031a007001510030030300d8414080b030343c218102040c1c1c0c018150007500c0c424081e103410303402145030f43c0c043c4070000c0d84016180003003c00c43e150409050a4460355071062865525000914000d40c03a000910320014441041c1c81440b01a201c0100e50400b00d444000503a601480d140040c415168100e0403088a07225600d00400d60401401c00c02183c8080c0b01c2c410125224241c4c1c03000500f1003402911025000f000d000070032080d094049000da912840084407520507080400504034100641c000311042105e000300001300b8694040703641d0b034501034901f8060058103400308040500c40e9034200d10740c100140090080008081010b0810717002030300d83c40c00e0303600e00b50301c08117443d1a1b010545e4400c0700c2ea281c50744000d858134003003a00254002c20540350f899208000300d034103a072400c221000003080101103e005809012000f034041e500045201c1900c2200041d400c005180700040740b80c050f0800e11820355032900000005503105c111035011040d807130240030800c4a94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899446825 1250 899445575 899445581
    0x8070c0c03050c030d0516111f02032503021f0209190521060c0f04030537020a031e052415060a2a061d0307080708030703140406 57
    0x90001501150304440c0007100031317160b5026541c49020000403882964012a98003104d5152002300540314211210300544e00002ca000540d03a82e0001da880011941c095544d040d4101c9406020701c0316980c3d003c051650002c1d2101107141568414200784007035106107a0182e4120fa0700f480b8010710401035106101c070f070701100c019140304052150607505240c007140c00d640182502d26081003c0a40781c643e44180b040d5080360000c0c1001017419406010110009000b0042c040304030a6400c0d640b06256008040409000502075044100e030382e60406c5180182c42d4035910b10240d95110300c004c3e00d03c84480e16225032400000720060118445c00c4008029107010007288080454a4a08400e80d40d841214071403038040303d500d009800110402c0983d510b24400c9100c5c00703500201a0038a120040a02d0803207451388103407041512070990f00c201310a0301496802d1980d484400315400395041c0720b16610b52504030302984130081c01d0980000001100640310781d0084024008410300f0702c981d420542009401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899448075 1250 899446825 899446843
    0x41d150703050c07120e040905011d0d0e04020304060b04090f11040b0a030b06030f0601081615050915040308030114030105070306030503030604091a010312080a05150108070c0c0305 80
    0x26211028000c40c02240c4a40200c9102e102403601c0c9901e40800703a80d600c0c4103006520041010131101d03d01c5c6903100d07940c2e40680d034021805100003080750b07418040f20700041004440440b9050340149520484660403094121040404540040e1250f0b40c9040240203810102409507005107054100020094a80031240300300340204c107010350841c0c03800203000840d03076030445003640040035681c02c00025060360241a030100b00641071b01c00085500c001c0a180200a807c01c81c12500301207841d02c4440e20228038440200304654040d0030940c42a00c001d03040d8801d000c075050041040241030343c41028044100c2d8011544414401d50ba580d42d14048001d204426507031502c86d50810001c1801c05119001c3e48c02500e800c070003c0d51031500ea40c410000104410102182c0d24108000959420744c030301c104c0c080c02140244a00411915500d500800c080c000800c0384507182e20705028030081c04a0b50380f16000140003800c180215469001c0256071343c0d60742d81002000d401d41400301004101003c102800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899449325 1250 899448075 899448103
    0x306040305220e0a020304060e0d050901030e0c090c0c0703140c0a05010305060f04050a060302150702041803020703030507140109060b0102010e070e1302150a09062d0e041d 76
    0x1625042c40391803500120503441903804072002240130688910b000c0d401035030094410a80002e41450403040c1c079003460010010343c400304401159001103940c00d4040c0c200c031091108003810081d011301d40001c20120004e05017540c1040301080c0401c0c1d03a54200321403005543c01081c001540403080c0b6505541d0042904098007035038100c84c1c0004c0340d500901a440c01928014461482030a042003400000c2c000101203440240c2c85010000150702e4100308001c0001c03092004503640c030400d0040c4402d861189400d101c074202c0705900b90b80403d5000c14032030280e03581440c02d26910358190400011180c500000a14154a03158101040146991100c6d1844000303800030b104114407112116200c0703c50748541c0322a20459400120030002c1e421040e0b02440c8014100300c95805550440c80c0359400c22003000d008100280001e000e03c580040e43d02c5464141c00f1818a203002d001110142c00b508a000070300c0134001082003c004c1582d8582206030042900c0d100d00401002d0400b50f59623407400301d22240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899450575 1250 899449325 899449357
    0x1090c020a1a070f0c03020c12100e03030604061a04030f0804030c0b0903010615090b0c03040305060415110301030807020405060d1b06090f05031c05091f020d08240109050306040305 80
    0x603d416010b079005c4142d080d0141c024020070007180c2c00340f1603a1a9080500a0300d8000d000030084071035428454914601c0001d0000c44d01c07490a40103220456259030803038a0301c40c003210b02c4159010f44000c22038044d039030700020b082214505850409000c1c05207805c01051402c03404000f00c0c1c0c0c81d81d40c4018200b460012002441450b954002d0749040c81e01c0a60301200140d0346443c10b0218201080c010400242e412049a03c1c0030f980b51540b0b810070720700341c1c1d080351001018549005600e4050140d10050340d990f01420b40307154919600c0b05034a10881c07100030f0185480d80d0025546a8405101040040e00b04044181e0001102c0120014440700e000d808046001d0840201e0746030000d0f0200c04c01d80d4006001442d0300030038401c0c117028100b40007240504000081249164940722364252002c54680c1001e07100d50070f0203000c0040d0902c071812044004210003481007060002c03212251001010180c82d01c5a025041000100c910007800c0e04210380504c1103000b0b000c205580300008050503091600c0701 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899451825 1250 899450575 899450597
    0xe03071403011a15071b080a03091d01060e120d03020307111f020310180903091e05090a1103040c0303083d260d1701090c020a1a07 58
    0x1002c04800c02d0101504103500d4144820704c03202030070003040ca650098039492004100c0200f00c0d801c506098100c0501600001007120815400c924010080d240d20509448800c56148620f150340310144110b104114400540c4030403908d070f0761010f003200080707042071304c503030304003101010b0041d42c0281c1d040e00004840da41c018100d2480498030307404424041501c040440e560203100030294002600030b2110303a150140005610349810300c0541468460075000c02c0210b514100a022030351503a008103643d1001070385422154448034900e1041e80e000300c0e81c51001d601d0b509504002021130a034000e04421001051006001c0620181c204030f0b4802e0307540c104c09540307001024404003000040c160301580700d840c46428008114100d6400d80b600010903a000c02d81e04c4001d0f51800004006038a031038854043e29071081e0b44203005050244280e418941e1441030282201d41100c0814070030b0141c3e8503611501c8409940c802e00c1a1402c0325001074410400494401070304000031415200312000c50104400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899453075 1250 899451825 899451851
    0x530010609081209100504080f10050109020301141018030c03060b011403241305040515100b130b1b0105060319020904170f1b1902060a0e0307140301 66
    0xe0743c84020b180d01d2502c2c20800d004040c03103d40c2c3c5004c6000340034840213000102e4902c0041041102542e11700c401800c10800c80c14403482120300617001801c0300c2c0e004000512111080c41011a0844020f988030a00780f082da03501190300d04c540100c005401c00c056031001040c00303034154405054070b000d6581041081007000041d01e040861040d07640f24103806000080c00110300c84c1500f01c0c0066401c401d100d84031110000208100d041a9081c101103944500740414080104070040d10906108140700190610a500c10900c003114400d54441150020f801e510300701c078600f010700041c0380807820b29403075086020007107241c20107801d040d10a030b61a010018515280015000003071240d00c5043e0941000c540e021701420f6000200140c80f11070000c50340c0c5030f0740001c20300108050403600c800f00b0b4940d644507035400180c0d03420210070ba44c660300640c0d070300c0103c60194140308411541240d5031946c41c0c001c945c0a40d50200d4948446605004144000840500720b40040303240b51001c078001c0002e004007a070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899454325 1250 899453075 899453083
    0x15110a020a02211203100f091d0a03023315010f0206040b06060a0c0510061521051305030403050d0906031b0806040e030c01090308010b0309030a053001060908 70
    0x80f10344150f405800044040b542100c029600801002410f030789081d21141401e0180005600803d11203544900da01d00512032480c01c6401c08000e200600b100400c541c900030b5844503042d0b4116048200690140700a1000060300c10f80f00d08517280317a481620303042d645101400e40c007a0780f0b2804160307200c5d0303845805440410224800d951010400c8401c1d11200140012a0095042e403428805207003480004280100074000c02c100c03a0b84030200c2d0f00c42c20201a40b1110701c0381c00048003804079140403030224989140010301100c40000c4005910b1781c81c0c2a40d4045d00100f83d0000d00107000020380402808404101c000a1022980303441074401e5540070304601700c458522070440411f40103034030101602e1050901c540c0240c4010300200d000340000100c5421a4013050140304269034aa0170b0801b010742040100d4010a844c2a0041c190710308030602d96182e10400ea52081040740002d800244000060311043d0400418002541c80203050010100d03500c8080c055040071030101c1c100050380c010005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899455575 1250 899454325 899454379
    0xb1804062a053009190807060203090a1401091110232b050a110d05100b03150924011b05030c06011805060d15110a020a02 54
    0x6500d400444000c0201151140c00c0302801c1e00e81945040070008050701a01c003000c3e02501d000041d4041410030080b254a800d0320380070b481541c00360010244002c0381481c0c050b10a2590031010140c1e417a91450b24407401c080040c50003c040760448440582980fa055020401851080901c8030406907080100070a10542850a0001400c01148030106421818044280465076090b642c00c00d03950802c13075011001c265482600748071042c0d00c081d0f00d80c40f55004158100801541c20003403108690800415442030501d15020386d52030f071000c0340d1041c0e0a0a10b02d4024445108043d8590170014002681b0403440c240da1889500500301003044446905406049a400d041c010b024014100005503003410081e41c09503c10303039400d1070f0500403401c1400140421400c4c80042d002940c14000108c240315552141c00d0307040e0f480c007002c2051a44402c0001c0010940000d660040b40001d074200c03101a10070022050a90390022880b01c0c60b03580c00003100309140d842242d02c065062492413500703014031f401d5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899456825 1250 899455575 899455631
    0x20c090105040207060b0603160201061a220803030f150316142806080f0c0703030207020d0f061b030509060a0207020105251713060f02010b180406 65
    0x20200401040c503160f802091110711441c0d021a00c10408000109070750030132140c600010b040b40d0071402e1459070a20070171018003a030b0306d00c0440703007010000020701c0c0d40a1a60b551007160701c4e00d6450a50b00d031740c4001c2c4030010300407241180d9880c9001c5640032401c00301a20561a0030070480d0700280306190105500c10150203c3d444c865000f494240403a2940a1120402d40c10030018041d10700d1042240102c10031104061112200ca11f280c400000e01d800320003406506007117065401c0c403014101c10030441d512203030580307405600c841180c00050326005240100525002020101c0400c0140d140c0010044541030500c000c980f1072100410380a40308100c4003a40d46403c007000290b40c02c10a98090107501d40185802824207810500d07140c0c8500908504040f002d02a4000b8005c0006071b1104890340f452a903070250501158600155524080d0b00402d0240101a000c20078460b10035031000000b104010122454243d07280c80032502d0b100143c80640344281444454070f003544000c1c1816550100c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899458075 1250 899456825 899456839
    0x90e0a0902100f0c050708011410060215040227220b180a0503030403050d11160609021201020f030a1803021f090c06020609070801060b16020f04140a060501020c 71
    0x80101c08403001c3c2c1200300030f01e0074005000d8440c004104200700038405008010300010780d940303501c2c80007202d58100405000304020390b60f2007809001d90108100303032039540a10356084140c8840c8009000c41c56401c0042d0755902c048100c40c008124020010707800b1341801d8000d4050142d410711002c46503040070001a05680c401808140e40e210780c21000340c0411484425100c3c40c145550b94581958000d484c00e400003000030400003104401885809103244010700c402c0d1800c0d81d5104510100c031402c000107401640d541020038199120a0459000030100700c0086641d81000712086406400a407500807016162210035118040401051601650503400a00c20540841c00484030300070f0308845410215142d84070383c00080d00c6a1401da000e4281c6401501551414401203440e2801e6984405032503030420f0b208201800d095000c0301c0c401d640046080c100000d007400415881d4000759240c5401601d003461500800d0300c0312840741d0103064803442c10b202c020f9070340004a07911500382d40308560041c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899459325 1250 899458075 899458099
    0x60705070206090f041509110712030c031e0c03060e010e06060304060b03070303030912090f090b06130b030105090f16082e060917070b0c150106090e0a0902 69
    0x1400304043d1060660051422144075070b00c1c030206090702d49800d030a880c07914005009200c945420300850941100106865082500c00d0b151030103502c54400c220b0f81819528032032001c07854800d422080300301090400365044480d65001c460024480004072000081c07034014081182c05400402a042f40c07500034414640b905c600781004050b0b40b01420403541260768090f00041501c3c01d0107800000c500940740020410b03020b041200348071055404071010410a10014031406000142080030307221281400507281e684176011407050300c41d07078a2049803101d00c4500091a86092001141030743d10540b071071412611501c85410f08060203070f50040781c00070044030869500740309000b060f50003041c0d0b18184106030032594000724a00c40322061409140c2546000f44900380d0020078120040901c01c1f162000504114171035900c1f403049025001a0b1500051052041c0101304900c420140110424608550350b8040c003030441c8400348a0291100d820704001284071641340318074030400742c02a0200b040d5030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899460431 1106 899459325 899459329
    0x12050a031209030804060c11060a15060c08040608060109031e06050c0903060f090a050f0106050307241133011a040b031005040515090106020607050702 67
    0x5420422210b0000e5844150f141e1300c50f80240c00040c40b80002e400c122241c900e88202c556682c4988000e100301c0707040507806510051104034029840315529441601c000643d4074001d04600c41c14003003000203034050141c0c984d012905141002c5180c3c2c59942d411003a00c440c010804d80515500c0584040100b10f00c10340d9004010300c410306042c2801680042e035142001402c02240c402142c02190031100104002c002c003a900c0803e8941342c1c1e0302c0c61406402403105101e024400c0c424004002030314610501c407a2541c0c1500c14100c0ba0003481c0c0d4106440b581540b02001c6028812054000703800e0059008c00c24040307240c04485400300f000c2403003804035044107810080e001c100e50b140d004405001c0000f141d0888001c044815120b90b9099013450708000703103500c1560400c0c18a0308000c0710707803611003504032008801c94616001341d1700c0704803ca90f1108221014070225500300308110241c = true := by decide +kernel

theorem cover : BRFrame.Cov 899280575 899460431 := by
  have h0 := BRFrame.cov_init 899280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899280575 ≤ n) (h2 : n < 899460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
