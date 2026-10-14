-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2637
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:17:47.132919+00:00
-- url     : https://prove2.me/submissions/0e7cc467-1ce5-473e-9374-bd3f8826ac78

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 474100719 ≤ n < 474280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 474101969 1250 474100719 474100747
    0x9030406050a0e120304060e033c010504030e040e010207170a0e0a030602091504060801121718030d05070203190212030a0822081207050415020106051503100902 71
    0xb02d40c00f81d0700070183e058100c914450000180089038450355403100000421000d0503144d59001c030550300e10700b03011403401c00078030802c21080c1038148544440040030a02240035900f940c1d01a01c06802141031080c034203540e81428010356034107030400b0009500c0c24001d41e503480380400b00b0f0541c0f0b42d01080c001ca0000d9003a40308041044c1141c2d030040c0b880e0b443e181c03a810440d00030360008410310700c03070404c0c2d00c0714110b202e001d00180c8007216050384480205038600140a40710f801a460103e500c0303455180045480110031000d80b80c1c4180d05005110b04e00e108100380740c80c04680001c0c40050142c14000200140d50020f40c3c5050326008006402c0140724604c00b007a1076101446100c2028000403507005c0302541c2c0004c142d4440e418001c8aa40c0100440781041e022070000a0084d000b82c20410140241040032144d0039001100c51508901d0302d0759440070340d06030030000e00b5000c0051b51103050401152400317406074464243c131040001c0c95800c1150442603140100d12425207020b4001c50292108102 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 474103219 1250 474101969 474101987
    0x2f03030724020403030504090c032703030f0f050603060106090807050d02030c090403050304060b09010b18010921050709112a0628140c2b0c11010509030406050a 71
    0xe800c00554843e0380320b250160054109024904416140c50504144144a0f001e0103e841d003d4440c180c40b807900e007401070709401d5235a5a0550905844507109101e40c240d5104082c3c020380c1e43e00d00080d02d070034290101400c00b60180d101c0720030805070000612060002265610465030f049910b92040d4007280b004c039003012942c1d045d080d8451062410403080c5500031000f503200324410002007006c50701e0300b401c01c00690002e0140b449080c0b0f0038000700c40115000c02c41c601d50b180c014102101c00503a6441c843c61003c0948501c4444500e0304103030007041100401209000e04208030741805000b50744511103501e07000c0c515031585d1640510503071410a020b800f203640b070440780802c180ca030507252030921000c20742c0703100001c08004429810302c5001c1c81014410081d0040f00d440c52b0050b01d03103030407111030070a8101020102409414a02401482d0700320b000f000300c182c0401c0008180304d0003903d00a4100c0c0c03911001d2001c10307414201089210b5102200721001c1d2111030a1aa0b21003214200458840750 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 474104469 1250 474103219 474103283
    0x9050a03030905090106051303080304020402160303020c19170906210106110d0c0303050c0c0604050a050c090c160c09020304060605120c0a03021201182f030307 71
    0x460680120505600050748001e803901503032601060399072014100c42c4c1b481100700680c03405503c020300744000385803640115001800108054140318140b840071201c3c080c000e108501295000860045410307003404080105d200c540d00030300407540652182c494000584004c5011b4400003c0c0d000e49603070352002565030080e600301046909064140110003410b10038001d0304046a0740711069240041d0005058400071000d40e02da00b691811950306801600002c0c201042010081c03214200c400010003100740b196001d58018000b2683c90b003080360a12201201071402106058100b00048070a1000c031145088100807400c0c01e00b406040c141034000c041e800844c0b106000100344000d01c02c4540120b0161003017120920264034050743c006646414000405410103a005401c002600c2c00500014203400d4540c0040b46015000c40700b01011500c101e402c0340c2c040d0b0300203404a00e0b541141418035503511600e03079002e41c12907400d0000c1d607039020303100e40140711404c0c14002e003040b194194082a0404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 474105719 1250 474104469 474104479
    0x100339081c030e0a05060411041b140c010e150603010b06181f1809382d09071e03110409140a09080406050717130302030613050d030b010905 62
    0x404078504aa201da20503101541e00b08c86201f4880f00700c0c5018811350700308180480480e8514400780c002901c0c94207031208a0102e180e4140510f16942c542030080400c0700f180c19000d025400c1605c00c0040081001614aa00030ba16002e0841442c0e210302044801100e0441d0f0000d0b25142c0140000300b00f03100f0410080750030b4412044107034540d90010640c890b41e80e8541002101192200c4040081307031000c07071900741d502000307008461004d00d451140070900748500c40b100c40751186400101e020303007500718494030801091052924201300c5105040000e0001201c0070350f0507040207503004110549035480d44171001400078a800030b00c0d00030340c014104c0d800460401922203a583d0354800080454000790103001002d0300002e5800c00d014890010019400b510603828541019822502c036000034404030340c1034200c40305003a00c101107400500841e0b11040c00c203120031400c2d40305250030200041c0503000c20710420508080060b03000b00c0da20740d0100d11303454001192050f0b91300488200c1c84961049400c2 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 474106969 1250 474105719 474105733
    0xb0402130f020d050609060d0209061306030b07050c07140907050f0705060c1b0a051c0210020414101704080f040e0f04050f2103100339081c030e 64
    0xd2100e400c1180f18185c1224420b1040e522041404850007003408000d40c4041440d002500c0e41c80c0c6002940403108800c18005442900e9070384550f003a60003039401c030000c50300108007400f100303104200c050041c01452840b06c034503003074040200d1400e03080500180140300f8042400c202c001c0341130090703400e596080000c4615a060458070800a50310240c6600d019141c1002d10012107040003030040041c5074414010040da01c2e0100703110f82160341208030300045019140046c590343c0514009040a4440c14a6110a5100300c50411400c9000c008294003481024950421449a620901680030350403950a5a407005808840840d501c00d940210311421100001c0c04840c06103040350710300c078521410440d40b452208000a0741c0d6800110200ca0721100b2140c0440c10b401140d501440e00312030b2040f40285100e80380e0380d401030865011904802084880c0b42c84914211800e4881d80340e0400e040201007a150502543d9501c4007001590749144002600180c1000d5200f40e105c240c41011034003c2c1c80306 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 474108219 1250 474106969 474106987
    0x1050d2118050a1815051801080607091512020f040f030b10120f0507030c1701061715040203070306090c060e10080f04020a091b08090106030b0402130f02 68
    0xd12505903203008512450520100b420705203c4140030075184401c031200c200070212a8194003811405070340d03d2010316403000029441e00e4030030f0050040c6180c40941d10107503041a004900e0100000c00c000c081000d070701c90801940d4042e042c020742c00c00180c07400c88903203184028070700043d05c540850700c00c00c1744c030000b400514044020f2030390047d179100700d4000482c0d44070000b0002502086000d54805808e818170007400085040f640000e07030364860310a03164400d0381c3c0e840c0d00810602d9a445190000c80c2d40808000200e0301380304100242000107146102e234900c1103402a0346407910101070000307009400204007903607000c221000c0119403001007030040800519025100c00c0c068070859000c00d01610690406140c1340c046494003212a0713807000d000340e0701c510304008940400751040ea00300320400700210f8000d66a000e105140c6a212503244a5038400f032400406440c401401d84106901d0903100744001a0116211900f00f501182c540d68102100d400070700060200e079141c0814a0710000b10114 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 474109469 1250 474108219 474108227
    0xf0c030839040f0b030601020d120e1c0f030509100f0f0608010c08070305010506190c02100201063602031b0c0c0f041b03020f0906370801050d21 64
    0x2050b502c00e00344101000c1e44d1030320380540500040c1e5499015801510a00d5000392281e4080300d8141c00ba10303400b00700900c140c40f840f400c050ba2301c01c58464680350400c00504880d00416041e50b60040c51400300708500d040c00712603480d0351840d040080c003244c40e1080600c507019180c12030b102681440600300916036036402041d0084c0388408945c404107040300001506076009101c6e06041323030005000f04d842d10f01219103040074088140d60110501141c00c5454000d6143d100d4206010f080c0382d0000611181403602c2c0c607026140c1603012040340741954680303d140e46201d070700050010f10016030240e12515000901c81600c0480c480088849801051201c00f4a000007680303103035440160743e901c00681000c0103100a0748c02aa0130072000c0248402c00e0070406110398014410407206006072030402000e20005407e650105030211480c0c401180c000354514081103c10340c95034100380c0c542803100c00400b070180070100c051140d2841b030002081040c090000c00c0c079100c0d0171f02445605003640c01c25007040c050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 474110719 1250 474109469 474109477
    0x4060b070308100602070614121503060a090206070206070c120602130b03040305070b0a0b0a0306060e0f06090f04030903061e0c02010c0504140d0c060503070f0c030839 74
    0x41e00151001010580c0c1d03442c060280c1c001d0303540341d0703010340311300c505008082e01c002c000b001000c010044100706c00804400050031203804ac000040140d01412040d5040610340714028156140d480e24100148005980c0c210890f110345078181d500720b444410a00780802c444110b40e00c40c050903611003895104000c03441c0c0c000c081c1100817261110f6815100d11100c0e045002c00c40e0020045030007040010003041c4495105030344981500d8012901c410640045840140700e64411100e01d41c90384828040580b281c104140e1009199020010701e1a10000007048414003600d00d404141d10040417806151203a22508040d5820540c1880424407020080c030080d42146400540c4500d41409458480d106014000b000b05566803880c1c21300341044000c9000388010200c00798401d058503513200020300b4114161000b4800c41c1c403050344a1501c03500241c081c081271110a410817064004ca50b0000741c11070015508802c0507001045030080300d007059001d208981c40405840135803031300c0041d021001d2400074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 474111969 1250 474110719 474110723
    0x903120f0f15062d1303060b030d05040314070914160806030601060e01030b030a05030301031b0324020d090b1006030204030803010b090307090608030a08060303070b1b04030204060b07 81
    0x1e8403840e41c030301607501c1921220010360740c0d00070010045042d05002d0700214585603606003041d0494820101209070565202012402d40c0301a201c0d401c10a100705803040c0d105004d019009001d103034111880080140c880d07030000402645540c1d21400c04443c0c20402c0742c1c0178092540003000035a2459071480100c5108580d1403101070703100011640c401c1e104552203030080d0300150044c1030990800c41d0940307080070808082d41c105a0342d50b44441c00c6942c00c10554501034021720156959505500700244a98441e1180700740e8501484420030000d2200004141c40d0b0940b20041d801340d04c6619a200041c1c8682c041c401501c0d070801c4040e03c00e00054014460145052112440d680c40e910351095060740a117110181c1a80000d00c010020840400000c004040c001402e0720300c80303134407010707031404980c2190001c220990010400003004d0b41c000700c0c180c0d0410001c90056091000d19620311060720b200a101e40249000140a003200c18610780a4601640e40180240030440d21031079902c55a8102e0902 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 474113219 1250 474111969 474111991
    0x512011a070b0a1e0b0108060907021203240a08030f0304080f0309011a01030b031c110303010b03070e0d021c08040914041e0b0106080c0d0617070f08150903120f 71
    0xa1841c00c441240708038000510107845503001f5588030303000c001c01454010114030035409090003080611500700c0045110303140300c3c0c01062000f40c2000400458600e20800d19000d014030f03020500007c0030000c103590f0300e103000800865a9555074503082c106c90054200c83e00540300003205100c0401c806400c1160a2a540f00c10740500d8000c1c10011410307035074205480c41d003507000780e40e149080050304000c18038031050313034180b00042c1c00805d4000741c82d40c1c2c13091784079441040000c0b090120181d8886100c01ea0b21101721480c8000c100030341c001074a00000070700b400103140388007030344c0c40200807440d0b060303800500c0b050008021082c00c0b40d280044e9444200c6045682c544a005100200000c890049005942040c4070f002e03542e007091020381d1000809044100e0094003440303001241e04442c016080604181c480c40a03410f00403d20840c900180c68004d0b52a2101c400c0003485542e00008104a05000346a000801520365005c03060030741c8210214a00c2c12a007034010098600c02c10750050780120300c80a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 474114469 1250 474113219 474113261
    0x307022b021203010f14030c10090e010b070308010608070306150201060302090112080403020d060e1b09130302030f0901050d05270705060910030e1c0f0512011a070b0a 74
    0x49040b40b91009000f000d40c41554142e00b840311b84421445142c103808050100c1b94100c0345003000620740320100c00e0900c0064074084c0c040c01070240d180c0d0014010000c1010f11804c00e4103594001d000380c41c05000c2c1c2400c1000450015544910a4015000400030b44000100c80007103180024048d040d540016801b500c5000c00014480300c2501000107210742084c8a00d0074141160b0030083c04c08226038054500c19244c03c0c407654441414444512074103004003070441c007540c60340d007844180d10000388107a19640281c0740003000300f81c01004960020401000d51a603c190b0f1a00688150040110345c5034003a18142c10048060400c100381340c0401c42003008180c4000e4560141d0303603203240e5401103640040091140074010304125810702d1083c5180e082c04240006144d00c2c4a00d02440c40076208036520700307a20071050081d000301e100c03035100c1c09503e4010314080000c100600310140611a07801108c3c010450ba10526107410180c0340c91030fa01c07203000c00c094103040c1148000b0f012190488101017070586 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 474115719 1250 474114469 474114493
    0x5091f1d3903030909062101150806060d031103040e0f040303060b0c1e0708060c12060619050702060c0a050a02010806030703050a35030a0b060403020f01030f0b03010914010e010509120307022b02 86
    0x25159100740400de204501c890f400d59400c03a00e860038207000c441c07544000e000104500840e18055072041e480015418814a41420000c054400d1640400c1c1d941504021000c080e0300049102401402d01c200c120007040007407403a00e0718104140d4420301e124040e83d000c1c440504100b4005011511140000a80302c0d156581001140c1c4185401a8881501d00c000d14039800e001b1805040d440d030004108a003007410700503e40703003480b200780c030b080300d05400c1400d19104541e08004401e0b00144190010300b0343d2801c51b62a03542e00c14040714050524104a2800482d41091031100203010a00030444041284a1002031030990002e0307808001460a25821071034a0801030140c030101e0b80c004010b00c101041007401500108030300c1d80c0c00c40500e500c0c2c0561000c161002d00800070780034840c0c81a43c0c1c0850041e00141c1c2110001d51510750325905200a00c111404c0000303054a01c650000030080d80ca0b10f9060059113090b1106090000350501c10701524400c15402c030560300004069020781d06030711803903 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 474116969 1250 474115719 474115723
    0x60d050412050f071e020d030309031403280906020406021f290109030605100f0e070e100504081501030605091f1d39030309090621011508 61
    0x780003c0e10328090080b007011400b03400503030020007441c0d03007500340000250700840c030b500c41d10315415401700e41c07502c0c0300d44109907102c50110030000385141e0042c210f040c05030440ca84640900740d101045500010510314052669020b003c100f030b0301180840d500da03a103260103922501d405070340f08a51180c0d1016041c44c16624003800701c000000c45008050300d14514081c04d83c003800e02514038104941d000012001600c5446043d015204a94440c03c08500c0c0410f0000c2c0801c03250002c15280316104207000c15190090709401003c40110350903d15100707850001c460b0b902032580110000c0c4184c0400b540019014450035058900a03001840196113007420240e40361800d8002c1240102d0350321342c2040030b0f202d9501409810302c603410720515403089540110b00e00591102c00130038128408881c8103100540130110009141880d486405200102000a45a00072422040c0c00341981400040b42c03036503040c1035080b48040500f075541c58407600c0d640060080001c0c1070039070f0082d07941c480081025900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 474118219 1250 474116969 474116977
    0xa1413020a0504050409150908091219290406060e09010b0a0b090d0b1f051503190b030d030b24030103080c01020c06070e0103110306011d030c060d05041205 69
    0xc507122103143c10b1800042c0310050130104c1c0e051752003d01c060b00020b02d0341824003500b65058080d004240d150a004030030490803d820880ea600c0d642e10031001082a6540d0440100844d5040707d90b4800d80f150b039050241c0800c040142d995141303000e283c05c210402c070b1207a00c07d4040d1200050b42103903d65901c3c800c0f03401c844206400980c814807100b0204194900304004105201001d801404d00084595400700400400d0ba40020000c1030312042a1900b00e45c00c070510300501d4111890450011402c4404059120180249002c3d00041403518074080294100107007610300a412503062a4200d8002001045240002032041c80c00031801d4480c101c40032030140000c0603c1104030f02d1646580e88144507a44185641e0990b0b5400740950810144140449840341500d030321070408108910000400b1152203100745110b02c1030900c144501c1340d0f401090407890f01050481d00c40010a06e600191808902c20003c07a07200500141030004940640c000398000d41c440d03c00581c580c0e208210a49241c01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 474119469 1250 474118219 474118237
    0x70f050609070603020f161401020c240f0c0a141606060509191a03010606090e090105070c06020a03290a0807030209040b041a0103030807081006051909050a141302 72
    0x21b001c0c001a40030100c010f187d503071010700c03c3c969000d24200100c080c0d42640c100f14040221038205285019840358080003141d0550940c594012052400c045050310041014102d002d401d1404682d0701c100ca800380300940115074040c1c000d244c5a00301606080038103114440700300d540c075044c05c1e0001024209443c1ca81e00510551070820792800440b03031510000c100c9060f00c8111040c1d003010124542c1c80078450700d40544103d960717001500741000ba15100056000d005101544c4c075081c200b14210740d102d000380c680e083e800040035036103010700301c4118041c140c4031480f6403002e094044c40e240103012906120701000010b6507411200c580e14001c070381d01c0301090f110280d04880d0410004000420031700080c3d51061054140d43c0d1080d2034000008c0d218002600100d0124240c030051280054105010540c81303c0700044213100582403640003032480c050400d029102002210103a000107001d072103500d02802c006080304540c16901c00d42c007070701c0c902e40740d42150060048154480108603d8002c46450b12 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 474120719 1250 474119469 474119497
    0x82d012d211202010504021e010e0f011806020309032505010503040507030b073b130e0307060605041503170901050c060901050f010503030c0703060b030102070f05060907060302 78
    0xe00d030208100d03900e010320300c07800c1d554880e100716a40015202e040a2100e070500d0707070000030980f4040c4140500000e9040000b5940d0300410120603682c4c2e400b0b004800400b4040c0d580d0b030b510342c5c42100140c0c0c80106081d081d0741c500b640700da0042000c5600001030400014100c0c02ca8020400c80d402c0107180c0780211109900e0305944180500542d4083c900030b54000780300b0011140807079501d40703030544184400d8a80c03000040b000c07014980c1007000d05400c0d0805003001d0b080701640b400c0c92a403070406020004151070251104001042c0300031190b5011120301c0c0880c0742940d41d40c1a40d460b00d18014a11b81c010f05200c2c80c0340100c2e080040118440503801e4a920040444200440d6655440b01f60040e040d030307504000040100c3c00603160280700c224000c02601c80085400c1c20040e285440d84407050700424000d5200380441c91403400009100402c407034004000180e204200701c042380c060710402c80f02400c0c58140f04210b030104a03000034003501c101074140c1503c10325a01e03500e08505038420038400007408c0e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 474121969 1250 474120719 474120809
    0x16090b0403031d0109080709020a080c25030909140f0f060904060b03011e020711031c050912030f04060206060103090f030305150a08030706061e06082d01 68
    0x110200c803c000751016050500a140345d51702d03040309180c910560080f28113150049043c00001e50070503012600002c000d01307100e04100a1b402900d516401000c0711042910a03912880306042c0034010480203445903000c1404074030b840d42e9075401d66120658040d099207640c1e8000030580d10703c00a08074000e400c01003104203a0b03100d0f616000702070440c4170b4043e94155a0342d03503a0303080b40d44512282208011a510003603164411400c020040003280f2003d140260488070103403000906166503544200140e04101b92501800c501244403c6000180c41c1807078400081c004c1e071140d03588130240c03089843c198200c800c940c0da90001141918016035000702040107211003080000d009810203640860240e406110003003002000507181c0c000390f84030450076000025400d0a20101380141c1c3d016080c40c03410200c052826080d10340d0200c10b80c0c030688041000c060013182c1c0f45070820707200c0e5507124440043ca5201c0300020307403281c000d5031080c030940700a1038001c04c0c00c2070400ba80c1c0121048150070002d582c2e8103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 474123219 1250 474121969 474121997
    0x2009010e0108070207080d080415050c1605070902071a07030b010903030f0302090904030e040b011403040605090a05030304032f070303300501031a090615130516090b040303 76
    0x80b11001c0d04003010750148510116908001308441900081a40d0382d400c898101428409084c0038000203414205081904200441603848110790b01c5401c41310240d0502056400c120b81440403981004103907900004d0740e00d090105180707176107a40c2d40c44407103886616258180305400b1501c1c5030000c14041008901704001203409101c0480d0402024140503162010540014281e0b84003181c0c110046140c4880d01c07495400d052150258602080c03e21100c04803100d940d40a00e4040100010100f90310303400003070b204080a10000c55820350210844c5d44909142c6001f4048006086400a0f41900002c180242c900350b0100403020b04907010191842034155181141c440b01d0039680d0601020f400d62000203558405540301004910420000640754114905944000241e000c80c422142d81c10050100200380810015048034292681c0b81541401c3d0740410030303100a2030716001a003407a1004000320805442d4954406980706d0351100805030b00e406455445029a00000d400241c903121500380c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 474124469 1250 474123219 474123227
    0x9061e060f081509070f0906031404110307080a06090215030618100f0e04110105030106090e0a0902060403051c0f020a02010e03070503030720031c05090a09020307032009010e01 78
    0x10308400d800c1010012003120700302096850109641e0b01d400946d008101c2491540d110442e0f40140c6458941846880d90000e4000c0c0f85050180018000040c0e410101e13455507010000c2000814120054400e20f0310b50f814400700034038582c40c00342c0c01780c075481d100e03090750314682000c4910444000b041e032140b11040000e00079038030a00501c1010f5001da80040818040c140304004402414041c1c2a41d06600e003503e0b01c0701c035000e40d07c803203207040c4001840140022a001519101a200f2500602c0302e65a104050f000180c0540c06000c0c0d008800001d010050044c0490310180e000302e01ca0300c000d44400180401c41c0c90540b50300341d00700140c1040f1148001503108103030000c1302040050840b5142525440081e0031540301103401c40e0520f6041000c41d4010030860b159000030081180a4100c2061f00024007c0b000d174228043d404000d07001034001c40135038035172030114050400314104544a00d0850005070081c244895444e1050140101540b184012141182c06041069468080701c03030780400191 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 474125719 1250 474124469 474124471
    0x160f0519060c1412220308070210021006060c050607170c07111c03020f03071211010207120201020d060b04180507051603200a0c05060307120609061e060f08 69
    0x15080c0d0401040c0c0500302c1c40c04c100c000c1c0c10580c2c0c600710503501e104010318407000302c0c0441c22040480c03444080420118401c18142ca0b11035806650000d030300402e03900201e00380030005840d061064508100441c06651204000d2541071048007258031640710108140d540b107802c480100404410398000031250410300d00506110741c4501111084200407000044c1d1541c60b4608404801c640c034223003103080c0346c0d0400205614030112070107180392440944a4440990f2805000401d01c0480700b01080e82e41000d504035000d07983c003c600100a0340c850744000b8080d500c001141046141000c0010034040041c004903022903406210249510006c10350b0306001d050010032407030070302c041400540b03020031100c803486400034842e983d100010207440d02038050001c000c1004003105e620100540b4002070781c1c0c0c0540c01c00c0e100d04446003a102d980c0e0070000c5400c48152810444c070142881000581850b040c0c1001003a162505000a0b95940603840903c420000340700d40b03800a100007c0c81510035005604003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 474126969 1250 474125719 474125723
    0x1002030909180330070504060206060120030318010501050a0b12151e01021e0604030e0a050d060e0d020d1409040b0a171608150612160f0519060c 64
    0x741e824610301018102960413131031524658400e001d038009400d111003000342580070301035060483c101030901800a40d50180200650705000d80310b400c40e640d03108900c070480c00140380d0200310307030b502d02d080c031141d0303807550603401d407100e15982004004103140c980a400c100c1031780d00201c606410b14580f01c2c0e0040d1013210203840550300720764000030480140c503025011844035006850340402284240b000920300440c0c0031004d004068002c1148011000102d4000d40090301490000c01062400b00011003540184e44015844600740d8512001c0180b1074002051040c100c9094944188601da4140d8a611040d40701c507001071044a40e08551849080280c03000c184050000504840c0007804500385080b01d801540c42a11512400203403c042040b18078110f4010104450141d46449521651844910b207208003c1805100003103841c0c07100220091040700e104102c89418020041402c0011030900944100c419071043c041741b030342860000040e200e040100ca02c40344a1424004a841d54100442 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 474128219 1250 474126969 474126973
    0x90c06030a020d0c09031101030606050714100c0e01081b0f0a090308070b160905091303030f0906090c1a0415021c12060e0105150a120515100203090918 67
    0xb80f5165080c240c4200302c6249543d45844c149641982020800c803001400c21604060400030144559503204064403074107075105281d01180b498200070a8203103102c0ca181242258504510401c401d0f070720200315000c000080c5c844802c1d40d1540c007240302c5846101d4280c207105020400c00c050104030600000c044070107441c0b03030007070205440e40e45520040c1d02c40c95040d100e004044080c8480c40c24250042c013803a2449080402d402ca19004c0466040c0c02c00512540350711280449260078907000350045003640c2c82c5910100107060692800c80020044003109442c00c2d842400007154541030560160314004c03803074000c10700301072400b1807003071880c1d05d440078910071400382c44374120301007540c041000085211510b50004094003110711034216946135001041d4004520010407054807410315030480881d1228060b591010480360685504958524200419107058104a1001d000380000e4080480031602c41c0303040115510103d981e0700400c0344040d400700545c3e002c00c0c02c68480705906018203911000b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 474129469 1250 474128219 474128227
    0x609010503091f05101715130206041502071a0301090908070f0302060711030418020304030e0d03091802030108060612070b0408030705071505070b0903040f030503180108090c06030a02 81
    0xb6200104982c3da226030384426072074006001085140250002c00b8100101204200307a45103448280d44074859070081200f02d0140020440341a14442c4111100313030007034546035076203039180c0301204811444400d1900500540c1c8000c24502004100b80e000c420076182c01c10300b1039003030074038910040030000030403920302804000c80400204041c0003103030381078001e0f0090030141c9060350300a094290030b42d40044081c0c104000c1440000210704d40119020035060006850355542c2c94159468580c02002e250b0124003a000c0d0785c101640b02c06840141c5a07603100e0050b51328220b09545060703000038010072210703800005c0000c80034140700d140c0b03409241103081200c134840e42d9030061251540c02a044040c90350000240c900900004001010040085142241101d1500900100b4900036134800802001d8a0000318401003c20000e5902500003100800c002a0717a902c0d0060340d0790b00111144a920940240c0408158011150144243c42040c0500001c400c000100300c0507030b00040c1010300c031a9080c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 474130719 1250 474129469 474129493
    0x3081501050d14060a050f010f03021e040b0c01060b1303060e12031f0b120712020c030406090e280c0504031b0302010801080d050f09010302071505060f060702060901050309 76
    0x3c0258034405a110341c0350001800c02c00c0900c40301718030540209004e041c0c0350701d050703070140d9228200c2c40000b4003030f15005840e005143c488481c0c0000c45082c050f90800b0100f004034420010301d00500d40d40c031449008011460b56819560194081d403501c558620740603d41c2000400d285801c4445910296403e85000e11205030042035242c20a0704e04d140944140200b40125020100d11071001d40141c4110341c2c14450140d001603280c0c98001c1000081221050708020321440d2601911a0390043c102038940725070300e900c0300400161891042c20561074524000c102000c0207080c10f181d6523030403441e1005a81d045074040d500503103000007020f810800304000c000040345c031030701c0011244040385888800d0703a4a0f50000422940060300083c4d89038100030150700100303070000200e0f1180c41120358035984850764000140d000b030140c401c01a01e0107c034250310801c4400180d000520949044551100612505040c0111802104002900a0800c100c3c2484c9580101c001d59808031001c021288204010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 474131969 1250 474130719 474130721
    0x50a03030302031e040605070e010e0a050f01090e1f060507030f03022203050106051002160e1e090c01031805060c070602270a050d03020c09100f06050d0b040903081501050d 76
    0x5c0310144c40640d900d0041c404d11641c0162814801d41d0700b40303003902a00b00c00d41c0c005141001c0621986110f004580ba055106034026078040c00248038450780e180c5140f800700e52580d80b6810820101690080c0000c003c11191f000b0b206503050076030144d49440b20580071440680080d0702800000341d05c0c000c10705592540540915015000d18800c00c00812850b02d01130a10003005152071044e010b54112030000c5809035941c5c4010400c513581b40e1011075040e00d50880c2c049583c1480b440500c2807603d400200700c014100041c919201070070aa0781040a5a80b80704840d250607541480140703103410030008900709003801da0203451442e01400c0018500001c21000c040c0aa8442e0201820044003005c01e18052034480c103c1e500504056400441054256030001d448225081070503128491403070109179259904200c1d1006400032181003840591183c00280c0550040111032004606150303c00544c0c0c100360042a0019500d9190340115866002a001c403000440c100f007410044d06101b0740a8070495 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 474133219 1250 474131969 474131971
    0x6050f1c0f061205011505061204020118030f0b07090602070506070503091f030b090105060f0711030118060e1b120307020a090204080d301104030624050a03030302031e 74
    0x308020400703c1e80c401e80381450030750300b029500d541403c2504208001d55160441240d15682c2060075024103a40e4502c0142d8000603519201900400b000901104008194a01d1003100b0b00441e4045004d90f0307080380c100e4541050740148001600241310130030480c244000503100c80da204200f0b4030706004002010451005030400c6103080c5100341d1a039440e19940511030f0210504c0241c6881800750b0400011130124802c0340c12003858400f00040200c180110100c1d0260117942c018020302c51040e40040d040400c101e14101950402d1401c01c91114510001035108001e01d0a0030392114144000d0040081c0d11801400c1100240800c1144500603030b2042881b00261a011400685950030800c84920380103c1101e00300520280180d0b400f44201910800080700c0d580d41101016008040c0d040d1010741301801440c0b0251034081804400c0015540000b036500036100d007130000e9000c014000c40c1d00e401280c0314554110700448024000b181c4260002d5501c06c0000791800051400000e080c451f84030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 474134469 1250 474133219 474133229
    0x105101e170706080c12070c142d0a020d0f0c0803030f070f0302070309050f040b09090105180a0c0603092414060f060301090b03010b03030a110706050f1c0f06 70
    0x681030603c211500803a203650040398030380001c0c2c00e240201c0c502d50750f0044060b00d400c080c040301510034010414000803010401c400340081c1d440c0106640e240c07019221b00a29820b94249402c0c40402040300b00041018016400901d2014100c0d02d6459103800410b40142c2910f004200c40c030041056031080008501a404030561016145040d9000800482803d520402014010403850340400c1c1d00480c10b0bc151071044074900c5a113200780002400030281c0a00f83c58128107200e0412031032a07411340c0050721600d4419540d031540a1040d50300c6498a2200c040100f914003040804e100b01d41c80ba61048010f14810032900400e960f500e01c0c2080591391084003401c5241c0c494200c0409104e0741c0020581020781540e03041b0050462200084490005008808005544880c10324055509402c54203030030b000a0240da60781c01c0c1c0c195008100e1546451611828403038802c00043e60352145003210010f12060100e281821402d1034a00c8140340100f21a083c826201c0340c40700070304507941c4a400d0040c9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 474135719 1250 474134469 474134473
    0x311040504020f220e1006080f180706020c0a0905010f0603090317090606040c03020903071701060e010308030f070c020d0f03090b0c100b09091903030f1b0e030105101e17 75
    0x82c50700e180c024410345c5c010444010300442d050204035080d084031503107800a03861100440d042d0344207440045558950701c00e0860700d2003050000180c49402107182d5030251010303100d10a5481e10b07a00750000f51002842184421030602000300a214801c0d80000b03409440380ca0048002200d04002c000901400c0c1c40311642900300000340320309443c00b4491103144180e0341c20194109490040041d440d02e400344954400c0100c040f0b0018000c4100f03500517405040100c80340613641d41c59040c0050325400850700b10b1043c91424000c651130380d0040c201c0054950f40102003204a580c940d0350004d0340e4481040803001e0080d8007802003040300c2c510340501811903440005100000e10a99801d00b5a1101a107150255a82d00c0070b010700d801020403000410b203d12100180c200d400c0b0b01e411801820096403c8a0341ca10b0070b454152031803016402038a0410240e61b4070241200c140c000c1600f00c1d0000e540c40480200399140410140e200071aa076400e1ba00c003070f075030040702c90303501c45140548040d040300c80c801c16 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 474136969 1250 474135719 474135787
    0x7052707030e100c0305060111060c070503120708040c06030506060f0f090406060806041d0606150d090507030b09010c080f0a02040801110d050f1303030506060d0c11010506010311040504020f 84
    0x104d9807600c5034a5025509103000031000014503411621548042c0269008a10026101d000d100d02001100c580d4003103006505203901c0e18010040044009480450700c1c40f43c0c610f40018414030034041d103030042000800682c41c118000b96800034030740c0820b4045250f424140104e444070f64452007028001c0a41d52903a5046207052801c101c21194540901c1080f1002007840028500c0000341190380403c0541d011040c080d041300c1001c1c1103016884601c8091130603d01001c080103000320780f00040764811103940440c1d4481d400f0b800e0903500001c2444002803001030014140b515032012643d0000c80c1c2050051400d40c41f60b1001342075800011b069520941c1c00644005480c6444c800d280d1b00090400a803c52820419003c1c044a442a0800f03820551aa0082951507540c4011150303220400d500400442142c204040d00000d90fa400100301c5500c0c1400007a020350080c060307914500100650a460142071104020080d08000b0042881c0c0f50280080440601c2e1100700410a07444039140d1449 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 474138219 1250 474136969 474136991
    0x303090213020f030c0a09030507060210051e1303091e050f030102070506130303140108061009020a0e01180302040e150903070f03031a041109010207052707030e10 72
    0x48022a070001c00d10035481041004202e040c104107498001c0c40c1c060b0402e55a030f041580442d4602c0d81b41c0c1025245020f120400a089a00000d03040c031400100c01045c0204ea0700e000041c43c049400781103290004803507000181da800f0a90015031456440783c1420601d0b60346800f081c040380c09035089014030181803450180700901d08400c10581908085009500d00011955480d449030805480003e001f0b0141070490101402a003240d40c0f400c01ba0680c2074a90343e903c5104a40da600f056400040d1082103003000720714071000d40220740b02e0310380544034140d100c20000011030306200c4400e0010151181490702200594a90196080310042c91000f8885c0003215407860460030300280c082101a0720401968002958030401c0d101803582506000501141e180344281c2540d0f0760586141d27100345001902030500707030114082d0411b40400c6e82142c0740035448105012030320031a50901501e1108d9040f000710b40ca09060004e603031100c29407030040380004100101601d800007001482168507111004140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 474139469 1250 474138219 474138229
    0x605040b060301050612131a0609060109061e030e010501030305120907030c030f032f1b1e01050c030d14150924030708060601020705030d0e0f1203030403030902 71
    0x21000c5086410341e10b154903290001e0510f11802d0300c5408007a21000c0040c88101890402d81c1215801980d940403401139040ca542c01d44008980d00352081c0e51980108020794820108281514419140e0b64015580f482205035003c1d001000c04041503190541440122401c0c040ea40c000e41c4603850341d0341ca5030507a10b140e407840c2d100209842100c0c0d02c10b0303004201103030907500c100045941010080014001c039080441e07102c40c04103004101c030800000030795562120b40071a03444000c002019a00780b030b44000d41030302c40814100003a80d4003020700c03000410541c4041c07902614002d01414000d260040350300c840d900390f0b001400607860165482e4512041e640007a12420761004111000481d1000903e00040d2840c80140c1350034a100d40c25203002081000c02d100d1655183d80007012034000c56602e2401e1690354000722465401801074807000680b42c100040c500070801d420f030b00c0780c5404d400d03150140302d500d10217480380d036502400b40b07000c0701d0440b030083c00254000c80c000c1d0303070100d50284a801846 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 474140719 1250 474139469 474139481
    0x90c080f060708091015031a01030204050601020c061801021c030207120809190c0f0801150b0703200c090a05180706051804021308060117030414010c051f060504 71
    0x38001120f041025001d00407030401003651050000041c580e404908140c41c407040c40e08010300ca02d801500342e144401086040074100c0f0320071601809950340394001245c840500c526a0b9400010500031403038410b074102040300350aa010310446000410340c418401604a9142d9170314003007580080c00c8014402407007805d841e8200705007000c0e903c41c02d029144a541d90034207003801180344010340030399080003034000040c1c00920200c00341c850015114010300d8028000c0403007a03044d10528400004d00c03042443c050f2220340c1c0d0980c442607110010810311041c02c884603e259446405205240e040a544d60701040b0300406804600140c14138021060a0085140d0148102694802c0704100304d820350200c201c91440d030140000101c080004000700b4003034001c40882c10310503004a01d010070207850021b400b50413034090010200308144481120b0303440340305900440320682c04042c181600c6501403c0143e00d07113031040302122680501060b0361150f5000c80300307000042030345843c3c00708110700e0036000314 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 474141969 1250 474140719 474140731
    0x6030f0a050a05070e0402030a0b03120414100e19150807170103080d0b0301060503011404031d150f090a1e06020609070e060102030c160608150d0213090c080f06 71
    0x8120500300540b001c5c0c0841c03242d103400c1d8420b0760000005600450300b81c0102c0c0316140c0c00b404a0f204105030100c01051500306003d129808101e590100e0304034a050b18209d103c082071034498044100d2264144000c004130307100f0310b00f030100210300300107459801050072442518a564465074581403200c0000c100103032181e0040c01c40c000310801032000c00d201da4101c8045021405001904420000120340544029800554107500c1e208010b00002d000c07081e140e11445c407a2b43c51038540c0740059101c1d80b030080340400b540c2d00642d8254010320b6443c1400d005000040d0314a0455003003521180005d8034903c0e4940210740c83c1e5602c80030f8505404075524900c40900072074006030906103030005001e0303075980152007503170281c3c6038200c00f08505034000c0c01107806100220050300d1005002078508901e204040c45201c00042c0c640380000c041c00424418070314042802444c146402090f6020132000402c1308424003842c4c1e55607110000000d0308034109400824001c40582081008101e01d0740c1402401804 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 474143219 1250 474141969 474141971
    0x2b0501090b012c0a08060c07110109060918022206020d170406150b0a0f0f0f080a09031404080f1b01020a030c080f0c30090f0f06030f0a050a 62
    0x74401ca48440e0340390781c3c95405a404102c48180c80000690031204aa0000d034550003004241b040ca282180001e001c5980281030303511071058407100460705241d840c4151f00c0024503404040c028440070f0800f50001075104e20003d800c180d0f041c042e100e0f050383d0f00507940003100d03800304c0204000383d014420841c4c49040c03418240101d4007000f0241d980c007a00100000d104e280d543c034004200002007401d00018141284505841c1d00300c15402074200317070145856070b02041004500918031403190580078000201c0ea0380c3c1018035252a5094070190117084421402d000b1340a02d100741040200000d00010054000200800c0311405120b03818540d0006100c44003020303071040b116a41c0d03000100060041d505191507403250030306040c404101d000d42002c00380c1e1450002480800020002034075403840404c064402c0e0300c11f0300b2510707001c091912100a10184041807248079011720340100290a2801301600c01c242c02c1d914240020003541c0b0403100700c24242904800d000400d6510f03c103203940940c017240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 474144469 1250 474143219 474143237
    0x20a170105060d050a0f020a0c050609071a03100302060a020c0f09090c06160609030309020f041a010e03010b0405090a1e0515090c090108060129030c2b0501090b01 72
    0x41909803141d00ca84000760f540300c04c04a19000c0540d8042940307940211411521440d403040020a1041410010349062054030041003810784040b035048201c950b4403d403622101c04121261805401c01401c10200c1102c034440000913843d040000c000781c00c107540c09006180d0388002008040340e4802c520034000c2140d8000c00400150001b42c41e2140d240c100c0d010340e210102c5085d000a0356512800c0104020f00308080780b0100341d05600304416407442240e61000b81244202400100e4018002d02e0004140f10400b0000e01d5005207910140042c001d400807034911000c1001c0303130903240195008400366104030048000d00200c2141044404841e01d80800c404002da12010303600d030724015595005145600208402c210108440300b09218050500801c540e554000541c940409100d03185500d120001e41c50001040304032110012010a00e80750305580b6181208800c0350030800d42a540500401034802c2a01c002d070480c800e0034010410040382035810000c88000b80d601c0c40652038180000d4031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 474145719 1250 474144469 474144479
    0x6020318010507020319060c03050c07030c0204051305120301080706090f090f14040f02040b0604030f0b070c0506010b19030506090a090602091005071b03050a0b0a060513020a1701 79
    0x464540606042482c10a80350a0980000703402c00820000c4283c00b81b0020036290b0410150b80c102d04420710316524200140d68070b00c02d40745880c0c4544c7e003000300010f4400c050000145004e900081d084031010046415014055540514080400e03803c0c400c280004401089504020041a0040d0049182c442078091405024103000c1e1014041c031f58290b40c4584800b000c1c044a6030040c1c5504a504040400383c1c01d0600704101c6000e82610140c1c012030034100d10000e14101001100c2c21254000d0702a0440903294581c00010080038125100b04940c048c0341d00b001c50020807645010308401c5103910390700c254103100300d24039100700700145050508100030401c0c42c0c0c0e656920a540403040080106c3c0e41c0d43d031403408400900c41c51000e60b900189040005111541c44406403480c0c901c189240081d0606d90503903150029500d2000804552284030407000054400c14101c1e0060079010010641a40300c5002804540140956050b075990209425050f280e1000303009044000d5101c0c0302d00345504107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 474146969 1250 474145719 474145747
    0x6040b01120305071104021912050c030915060f03150924130c0312020d090f05061903020d060b03190b0604090b0d020a031a0f0c03060f0301151806060203 68
    0x843c000d85030f010b85c0000282152600d4044511040200c00242045240750201030300c8a9482003480342e8441c506030000f80200303451401c807030007000c1e540d009014000c021500703126210401001190007003500b01d00c408158404022054920525289010151505920040c600104000c02d20004440a201810754403400300540fa00b0030154400f62045401d181000c8021310b289500c010000f105483ca00940c065000c50705040400035942d90906441d521b60b000c0050007814020309500c10010000c0100100300a4100c201c12425801c0143c101212000711a04540481d03103c0e1514000000400001600d04000c844502c46500c5007002815070704008140c0314001c5004030903c0310381c3d614543c41c0e1562003461402156038001e004032959500e91800404661182004034001c10030400070680c154030b50b92076144031b100031104085c1180e80d40d03820445060b2040e00c041c1e4043d540c0d41d000c6100750b009408a6009403440c00e0307452200e40c3c181a1103070120b64103584801d04540050100054134001303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 474148219 1250 474146969 474146977
    0x4021c021b1c0e01020307020d060204090e0714060a0903050d0e100f140d0603051905010b150307030216150504050d030e0307060c11031306080c070221030c0f06040b01120305 77
    0x401d02c1c050140b91030003c0142e1862050f004041e40c08044e084031700d4108040ea40051060300d207912020300c81d18202d11156503030342c003180c01035001d8a03107480c860b403155091680151100f10198a070100c4450791780e4580c0c03130038040d40011724000140403004c04580c90400403d0404602c106107410036401000400051030201c4d41d10035203001c4180007a0448a442150700040d01542d0444240c0d01b0000f1600185c0030168440307901180d003942024045586440c1102580c14550700d03e04030301d403a40d90703200d004400a40c09511580040708064078a14081100d6405541c40300c3c108082c0003c40c0d08042c00c0c010301d408040d0710340b402058100f0b000000c140901100740d0b039201c7e9100401051001141c00c00740c0d0b650242c030301d603c9900c3c071001ca01116a000109615400c654441e2130304207482e12403001e070781c120348540310000c1c0d044200b0043c8102e0980d0902703110011041541c065900780b603030f0319940ca4200880008000040d50150082c07100b480340c03a01685004001d00705684002940f2654042d000b030003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 474149469 1250 474148219 474148273
    0xa06080c0a0c06020d0e0c101e0513031e02090604060f030b0415050702060a06082113032009060a2d0b0f040608060a0602030f070204021c021b 63
    0x30259240b000c22005030152110154140d40601925100c1201c1580e00c4a00d481c2142c440c452030355100c0681d5005405465030710f040b6108480000702040410341d61540300b0041c0c0f240385880b4290001c003140e113041c3e80300001d01c003858450543c5030544c0100200010081d00b2030b40318a160020802c40314640c1060070080b20350202c50604140da540c00c013020f15201c04642110280d051000704141d02c1d902042c824400ea1072071404108041c0c43c0c031400e0765502c0e01c44460018050209107225034019800c4054141080342c505003410454580c0c1d1250f807000d0540f20954880022415510b01500d090401c8650108090324032490b11454924942c441c50081202c8903122510045422082100c410104000d4030b103030342586554401071006e001d06076002c0d1141000051102c0c01080141c500200580f085481e01d80c019802d08032404c10415031988094012644950308100d04450307a600c2900781d01480d61003d0005860701c4440121150606900c80601d030039400000d03440007082840e10090384a21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 474150719 1250 474149469 474149477
    0x906180f060c1119030b090105010608010b0318011e110c06010b1c09081c091511041a130609030803010e060423090c01090302011d0109050d03020303060a06080c0a 72
    0x1c05604004001603110080c007130700481140b50390394480d02ca50550804491242414201c00d58586c00c02c04d00300d901c280141c00024042c0e01c010407840001002560700110010801303100035103c07240d420308480464008402004948058840c1e000080c4154861a650219581e1a0900000400d40c890905015200325444045200d9440020500105200394880f1008003c0d11000703040104940d00061048445a030140041e803032800d420740a0054a59840004607003200030381c003c0301c00076094807000502015424800095140e54009900300b50807510071026a407074841660446010101d500003406005040c082080000e00d80021241150482c01f05491184c65050004014140d40541d460791188035840d0034003c00391418019000700321010490b45000040070040d20220200e10010380032694545c1046003c90050030840e018090524007810340b5070300c400004900100500c829401640007100300891070408211240c00350559040407901c514010050492510840d41828100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 474151969 1250 474150719 474150737
    0x4090b04150905100c20061b040605070311030c120d0c0e09010b0a180b09030106060f050a05070204090b090a11090c0a030b0301090c1203030f0b0a030209070203090301020a0906180f06 81
    0x1d511406e00244c81c00f950810340203c0700480501555034080544202c114214829440055810803008a44c200c0300651030700340c10030445490039102c0c0c81101c400e18155000400c13000c402c0c1003080c4245103007215122111a251200400c00f003007140c8084d52244c003031000c5ea17803103003400342d9501d078809044034014508260340d8070b58041d04503101d9004015840c54080f110b000850250019805031180709016802084125901d0f0b80817941250751403031a40100d4001c109200c0e010344240010649580007030f10105946c0d4103603580c058224800c85050615800004550080010301e280325441060116003041040c1844043e640481c0b041603520014559180c20051868600390803c01010350010000c81001d40d4547c60140000001c1200301c00080c0703041c4114501940c01d100f129140080235284142140c2590b09000f90614042c1c01031056110500c108444e44d64240000e24903c0c0290fa01c00781910300d406000780c803100da00d5041e8001a1402c46091040c504c1c1c517142101150a41d140036944 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 474153219 1250 474151969 474151991
    0x70302090a0906060605040311040b010e1311030702030a090e0702031902160b0c07060804080904020702130c0504051806090a05070306091b020d0c0b06060a0e04090b0415090510 78
    0x100b50741e1000500403401c24030b0005000703401c080a4003c480c012a10920f0f0a40c4000800c004c40d00d602e05168042000840103030342c54180b00402c181070f41e840280002d00202c00540440c8580c00888020005074030026103030080c182d2100e0544001d0596801c502c0302410b0070a8042d40700d01a4003004808603a4401c121003c0c02d100b0019800709885c2544003000d03850700c0b1206450207034410000024070380714400300014400e1044020501c500d800602c1141001c20a4003004042e510409083c1c2c1e0240001042d840b0282e01383c81030807900307284c42d110740c1c1c2c3e1540f4103c01d01c0032441c0e0b40348a02902030414401c112079511070068a0758800c0c2c1c40f2100159503034640c0d00980042401e900087c2d421031501d494203d8070004524042c60260340c0c2e800b280c01242c2a52002c4480261822000304088590400b150007401c298000d001d02d0300b030504100e200d402c00000070508a441c84070054880040706801d100600c50340340c0d141a4011a00e15040c050b030301a540310541d0780c0001840c2c44295550354800491 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 474154469 1250 474153219 474153221
    0x61302180c0403170d0c0e151303110102160e040606090507080402010e0a0f030f0b0901150605071a0a0203070f05090303042c04150e011b052a030a20070302090a 71
    0x5003010708540400042030541401007a0030303a17410741240a10700d036008850407003080c20181e271501c0b001e0702c408800e81804c43c0d880121442d6000c0441d8150b1141042c803c400324400c04c400400b0b407401c0b1028120920700390030650f051f00d009602080c0c20394548000c0c0303c401a80282d107984d01540a08150102e040302d0b0010a49a580c0d5501070401c50b9901c0d1408010090100e10b603600e050300401590655880d10100380b0300321600c550b2800d6512001400400a007801503021340403481c09002e008907060640303103030728100c0c120446800c4201d40d800030802030042c0e000034440c80d44240074580303103051100d19404a503aa100c0c038000ca0070064060383c030200a421400712a070042c1c015501c560711007030415141480342c000c5102e60f02c07801141041c0401c01e804005110300e24030300311044d000e50030054809000b40d503180e00007140c481c0103640039402c40c22005c18560b00c1055000400e8011640d40030050402800031317080c415420703c005050001d03d040319100203240c00a99404840d94030a685400403010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 474155719 1250 474154469 474154477
    0xf0c011b020f030a0b0a0c0305010f080307140102040f09020c012003061905102f0706080705190e100302040b250c03060b130207031d01030e061302180c040317 70
    0xb01781101d070303d0400c6820b81c0d1a4010291000f200d842c01d00c85a40c903a0303d00032051086024100040d4410320032003002c030320507201010f03007091310b40001460f090725100c1407885207a09801561141c1e400081031425507800b481a0502898403452080c0320802c203001395000c0e031002800c510702c110f002031023030482d03102e400380c200300100002491100391503000f0002601612001c0c0c0b45200003a02d800341c040c030001882012000711034502c8044c1c400d0a00308542a82c614101401c040d040040c2807154441440300c21094544280080e201c090404007810108441d12038070303a11181c01c150050104003c0d1100c95002e5540483c041f08003400c0c5401c10300c400b0b000c00700860401030550b1f580403d00005100040e8841c0c10700b0102034a9200c2200411440002a4031070b0100c018009107402c80106c0040d1091496030320302d900705140108481c0c40c80c4101078900501074812640c3c109041004400311f00e003a03c1191071150251288000350300c1e01014650480c02a840085c0030385d2164488030314030060f407804803 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 474156969 1250 474155719 474155723
    0x804092d0c0c030f02100204030c0e01080708250509070c1e050c0904080f1209011409061f120b06030c0a0e0c03070306180911030f0d141b0f0c011b020f030a 69
    0xc40d00c8581d02c0c2041d4056802b980f18071643c65210100205031110041651820f650ba824000c00507001d10006100e14040310558607541100a0313880402c0301d6803035a031101d00840b05a6500700c07040c105803c0c03144400045c1d6290001221980030703400009180400c0d41400c1010440324024185e590341400809071258611214000400081c07080310315218800c4540180104002002244180e44801d140003009490f08161343c0d01500000c0d1202ea0b82d401c503c20440c12403c80000c01580e00c4104110651511a007121142d0100d0b0070042c1c10b04040250140301d00341141c600720220310302a62141d0040c0c0c094400c404503140000000c082038081c4c0c11450040000c0740c54400d50002809083d0000c001b100c82c125404181c135000140240740019541c0b40207400d5202400c92840c40b814141e0302c00c0b410103156050041f06000d80006c01019100c1d440d520805040074041c10701301d0303030005801c00140707030409030512000184001422842d200c4e01021290f040c2c409620740405000003d01d051324440b00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 474158219 1250 474156969 474156971
    0xe0f15091023090c04060306080d0927152c010312020a1502091314151c0b06090f0708010614070212031e07050303040209040804092d0c0c030f0210 65
    0x91113030000d81a00140120780f0559020801c9649696686495000e802400e50005078420410311103400117a101d106843d808032005000d0142a01290b0140d0701075803007955081c246018104002c0c240c808800c481070340c2e40aa8645210304011207038002c0a410b020252030007007002261510749008214401c11950030400140d502002c10001c0c030082e61000c041c0c1d43c0616010078092401150b640100c0e100051404140011a030b59003096030002c030161100c0d19070015542d0700f8240407420310986103002a01500c200400c0d0300d014000d0042189000d02001c2240d100441040791940e4054007083c11b54034185400c025070100f11315002c402d40510340000c2e5200130303820000441c02400100500380110114140729085a01c20081120f0f406010390180503030f002000054014900808550f51081c440c440e02401e2503180d4940030700703c481c071419101250924400c01ca040c0205600c01d58961001d543c0188149100c48400505883c0c1c2010001d042c4890058207542880c000c1c0602040740c01480702c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 474159469 1250 474158219 474158221
    0x50a08030906040c090b030c0f01140f0304030305011a07020f0607051609050c07030905040506060c1501090b0603161808010c03091115030f0c040e0f1509102309 71
    0x40c40740e01c403042030314103c0348000050000107840d000c50048a41c1040e0003406080c00c024544180203d030f82c281e044039410840c80d0a0901151f04591001c0e0031000c84541a10340c5900d440d15014080310720681050748950704c000301c0c1403802c08440c000c40740401c0d819240e000b804044600402c0c04c42c011007800800e94050f20981c21508500404428111441000203001503120280c51a80500c510080500000c0000d402800103041030303001103400440141c0b05a00e8144800d0440e41405800c41817200c401c1ca00c0401041030400a014a40400340101d59142c0b441c2041c4901185002c0f119254030f040c0100c5c8402c0166081000031124000c01840c402840126441d0100500400f0300c1d4000310307544009450801440c1c101040e22400c4040e000300030603e10b4036070382c0404c111800020440d03401410204400300f0460b01c0b01d007001d070141100c003601c0000360415040c04caa20081c4250064001c21810003040210b40310b0102d404110b8100003d4014115411019a04a031400e00401d81e00240504 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 474160719 1250 474159469 474159481
    0xc09210114040b042303040e1f060804050c1e04090501090804062601080d08041b0b1209010b03070501050c0106080601080a0308091f0b0418061b0509030d0c050a0803 73
    0x8010b40d100b81c1c0305400c0611103c00c0068901d5245a0344440c1500c681c0c82444188076201441c0b8100303400c00110600c03e01c8518001c80840272841c01500003100003040107041c0402c00404024008510390101c44503002c1000548200c500714158404083c07007662641001024000213500419135503030002007941d03070340380c903044050007000f040c0f404004200f68100e80744000000358505a8180d410354400f50428000e80740d804c403002ca00141055400480f08203000620308440004c150003000842d403002d48400d000c40f10300352f01d0800240790f05402d0341080c2d00034550790350102c0c01d01c0079220242401900c420428066074010141900719000074441e00380081804440080e40d91030207031280c0c1d2004050743c0e91016030703520347e6004240120312501c040180740c044800c0c0d07088855946000b800000e560300b0315a9440c40051404034042e00d91030380d03402e58440c4021180700c118510301c01a060040c6041c2503140800d683c0d02c003070040c0300304000150b1804010403005000700031001e504000890740b02c0c2012 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 474161969 1250 474160719 474160733
    0x504060222050a08190b07050d0603150f02131e050409050102030603010c02030711060904020d02180f03070b030411030a050a03020309091608040210050d0c05070204050c0921011404 80
    0x64040d1521031210f80780b0018928130700142c2080c84030030001e055280c040460340d130303074048070b001424000c1404410310034809c5221051003401c0081d40680000008100008416821161074408030940e140c01003142181190125041000312910200242182000111528111041c1d03400c640d50150400246205024054000e07500810088008004501841c0402e0380c3c2d03032281d0000105142107011603070007149460400741034012070281015140c64241c810383d104a80c0605c8480e00c45405c03603040c42d4104c1c2404c2c0c01802c10307090b0642c01040c0705c03401c182006d05a8007000b0b10007440301e0960001c8146540b0b003480300529155114045429034412440d01a46a400402e140b6005000e80b00c00030b95a0032442c45c1c100c100d000c0f241c640c041c503a1034075002d0007001c081408081041c481e08001c160700c400214410b00c01c50903826561143c841e0214410442920000382c0803c02c070b0081840140050307030b0ba03802d14400c02d15000c6490145015020b0525001d4075054070103100c0c00c511101080148035031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 474163219 1250 474161969 474162037
    0x6090e0c0a0e04020306010e1e07020a0311060705090402090607050703080a030b060405090c070204151d09030c0d0c1e030908010b0405190213121415091005040602 72
    0x10031907201d403105454100309000c80d40100c0300654168881c50041000a800b017a013242c000303070308901038410600d05e00d22908200740251a21801644038203001c9040c140d204005070f041c2020b2002030101030400b006e0052003030042c038484501c0303181c2c00034602886540e80402c950f8001d84c42025a0034060f90f80c00e02070f0958200da1214400300e401c2c98480401894920112029030300002c06901a42c0c90707144180e0940d0b088641304982165aa481190742c4110f00203201c8000c1c1882503e600002080d04003520b100f030700c05400b121003507009005001c0c14003004214550000f0a51510074418015800c0c41d910900f8018030000b5040c2001c0d202030249603001c3e131a8425901d982c80240041c3d69910309120450300c044948221400380d03100304400c0d8110540051581a000c07401c1800c0054442d11190410041130004aa04030880940110340e24014003d08200758070307181c011324091910024030358880000f15010b08055a503000002c04118407a81940c04959130b941c600d0b40c0d509043d5590881c0340107 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 474164469 1250 474163219 474163243
    0x50108060901061206050c07021f11150f06221a0f01120f020702040e0a110d05120304301103070206041e0b07030806192706090e 57
    0x40d00001078000041401140100c510b20318112002c900c0c3d946840c0d00505000e03042c00c011020400c12500943e41e070380200d03100c0d214446400f20f1034a8412102803c030b41403000c0c0b1107407160040038421130700307150503114181d00c210f025403a0056076440c000040c80c0150703c0704c1c1038000101c2c400e841a600c6030441c0e01c81890516000e4140c080340f50024100400203450041850001d03c11071101100442107070064451807511740c10242c1005440d500040a4a240f076071902c0e825880507c1050a0101e0003030350308413261045c2c0e00706011240c02e8450319110340c0760101b81c0802200000104040001000d1340314038081c0074080f1502800c100104c8004c00544e890310500000c1c40418840704809400700440e190194014045403a203460009001220780c900b41c001c2145041c016800601158014001c0c003425209980d07104141c40c26900308032443c0e641c04054481052802c4050040c0b449581240c101200084c042c5015003c100c41c100b809004150814005179040102c0451603e80004015034502 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 474165719 1250 474164469 474164473
    0x111c080a110a0c0602040503100b04060b03040c0b03150409080a091a0a030902041b0513120f110301110a0201091406060d08030406060308120103020306130c0603180209070201050108 80
    0x515028400400d651881422000780038080140103942c500454525068502c80e8201506165641000a01740711a241c0410f805503201c00d1980d50300d203030911440b005405407241d501d0442c14941c8580c0010f82d50b82c0a10050140000b0114100e20100403072401000310042051285990300c0ca42550160410200a00031444034580410a411287c1000241004200d4628281489034008401402d07800340183c0e0041da036400c917102d0404110004900600540e101da90b51a012003070b40484002c059401070b120b444040300e100e40090b2240400c1d102080e00620300380b1001c4100400240101000351a10782a001c0c001600f03031031030342c042d00840401401200c0a911001e10450a191a41000c4441d9a4841040f0050400217170200001e980c01c42c2c0141d600194540d2a07966040c1c5036032000303501c0c000106480d401041107103802c00c01c165001102a01d1030007800550303030f501c940c0381115010310014191030760b9004080c501c0c0240f00d0404145c0042491401e4140584003074020102030184035007078 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 474166969 1250 474165719 474165721
    0x12140609070501022812030518030315060c24061c052104080f0309120a030c1211100c08160207031b0503100507090603090203030409020a111c08 64
    0x54030210340300084070410380282c040304288807051010740744c500d403101c0790b00b183c2501c2c0a0042002e0032500342d40c00c405070310006540c2c01d01428020700e44441948840c4554010800c0080c580c030740c0b012036802164166181a2501030078400c05007401140301c5060328004403035128148000442c0c4080d409000240d80848030811a40c58a80f12500c8815000d84543c1c410940542450245e664003030418161400c450300702500e980c126403c1402c0c903070b14094158004240c0b0b00c41c030b2034040003152181440301d005003070b800740e10350303002e466001c2280d405416081c55540710003a141c01115031006540041040d00c501684104840c0018100c2a01c00b0000800c1500082c2c010802511501c48000860f00103005031403440c0e0318608000402c402032100c0214000c2d000490351010014240701e0011002e0215561605c11402844141958081d4041605201e01000507031400b1045030141d40d20407501503601d0030549000c0d281446070707030010012442010b1f040c489449030b1090358064024035a4807101c02d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 474168219 1250 474166969 474166981
    0x506120a0b060a020c0d0218180105152202090d03030603050d0c02030a080c0109080c010203160212090402180d1b151d0d02030102030702010609180f030c0309121406 73
    0x20b00e0254209100140e0720000340c03107003280307084045d400007640f0003000390b40c020a601e41180c1100000780d074450170a42d000f4500c1600f0410a0007450b41c00464405d100001e1845600010000c07081c078107040d403056100420345407807468140c04950b84080041d004031900f00103490001d000300054802a1054042c1d400100740d042e00c94a1221802038006005000404072602c8500b80e6620041d80040190750b500303c0c40c0c0004500f0740282c003813a6901c2d000140c4a01d4004e6950f00a007012003101070854000c3d00c0d01b842410710081c295004840292001038450380c0718002590950f902d90965580021140f460300c0030449038004188103180721034001e558440d43c607124840c0c540301640c100004200c00e0031004054a07031425413602c00c4000140406580c2003503401090888c2c0c0241c400b180103075114403080c0305481c0c1d140507041c0000c90003106084000b0701c0340c07a40c025203440341d040101041071200d081d009152180d180e030703c060007514080710307a55821751508840c1c10200c0c0148440d54003540c40010b030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 474169469 1250 474168219 474168229
    0x6092a0315090a1e0b040318080d050a08070f0206180111070f02100201021305040509030d09060b01031a06072307090906051305071502010905010f06050a12080910090506120a0b 78
    0x1030181d031700030035030030080d1290703601900e0008101280280703003903141200182c064402c100e0003410b4103d0303858103903507030994030002401c0000040400b4103005040f144c2c450341d04d500042c3c030760741720105000950501014601d0b00d40940310b45d00395035049080c086500f5007801102509006064401c4850007241960030205074240e00070000c0c24080c04248030030411084c20700350803155200200b0300940307141044046e1180c040369051107045d546d4a0380c4142e00c020740c1d40c26215800d2102e022848030002032016a0004103284144080107050351012404023506030313402c1c0803a039140e03890700e010382d102d15855a4140d401040740c042c05540f160300f84404640d2a0b0688203c0d442c0c11500040a094030380d05000e400c0000c0b024050a40c01159a1203c40300c0105000384940301402c81c40005c08100c1d0340c6400204000b40807a500680c0510702c2d500f09000001c2e99280c11210750400555a40340019605203080d40d41d0310156105a80008001848041688006444d0f5201d40c0bc0e000c1c0030443d000e60700c2c09001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 474170719 1250 474169469 474169523
    0xb07020d020d0e010c2d0c0801060b0f1e03011710020f0a14160b09060a02030c03040b04030903020a080c010f02070f05040b120115030506092a0315090a 67
    0xe40402c0807503180603c0c81d4480d90100040c503000307030100c2280001300d041c1d00008010a600c5114400c03500d0f1080070130030001405900040074154004c1c4105030601c031052580d842200701d00c2044400c0001c0d418013a4a00303801c0602040b071500070494403503a540e05841c3e08286500c0071620300d80a000180c032032440b854801c5d5100307112900c01103420001c1c183c1040d1400000c0b48961803001109100300044003440a00180742c3d28440c01c11100c640c03c010f401580303804405020088058010301c1001401211202920f80c400e401c1159900561950f0038107913500a03c64101a400c80c840302000318600500245800c40703008280d031440c44c1001002400c03070312110103024048044103070800401262070a03820100903074200401c0e000c940c0616031240380c2100c03002e805020001c3c440c86800c00a008040c07012a034400c0c00031004d0520720380702e88a0400c640003070103110719811a20030164161518100041440813242801803a030030309002c0c124596803440102c044411409072100000541301c3c1c042d43d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 474171969 1250 474170719 474170743
    0x91806100f17011e090203060a0203041e0c09090f110d2006040902160312060509280510150c0c14060705011103192003060112090b07020d02 62
    0x6250340c07908205503060807035440030440140e5900c411284260400200345003052001c00180050420307094818541000e40041c01141c0c0740d8418420080401d40d07a8110720302d070388100c1c1c0c610751101002c1c1ca001d12840d0010380020580514204025040000b0034131103107151802150880c840c65480d104004840c01030304801040080b4580802404181125103944000e030002d240b0b42c1810b403240c0041003246c10030030f10200b0300100c03001034405040e00800c40042e41548050244186801c100100e1628800540b400803458140e519541100b00a00719104c041c5401050900087c2080b03084110700c188a030142e404c00303282200b8201041406604440d841031f50080c0c0c004180d41c500482d80e00d4460702d421900f0307080b990411200c070010f0400e2089228013140c1001e1541c907820f040c003c640303640d030200d80c22814980c074045030605c0d041c010200090ba101140c4a10545e6580d49400480d0030040304140c800380700e42007110b0402005644014248924030550880320840d00c0e9040899030b600303040682c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 474173219 1250 474171969 474171989
    0x70c0905190b010e040e150a0c030b03070803300a06030210020115170a0b0a1406040e03090d020103020408011503061401051005030c0f0f180111280209180610 70
    0x4c0310380710305050f00b056500342d002c04240d81c820703c0d844002442e00042110b41e550708507900e90141c8591505449514085102030300144005400c00e101c036541da02c50792401000c0440c40c8049404103a0307203c1914002e90351045104020743c10132035188000751049002c12482055500c030040c030b40c1441485a00d2142ca00044001030302403405a004021202c3c03054a25001d008000c240c1c800320b0000c5541e11b00414030b840300011905840c480d0039070503001c060182403050f4100701c1d40c000340e50000420745031845000c0341e0301e500015403880140d009100da81e011403c01d5080c904080301100c8405a140202c900946041c80400d42c1c814800c0701c00c030401d0085a03480070140401c2c6145902c180d01541d48294040081c0740b5110847d94018001d81103088805851000000d40c010300c0c3e580600c0350b008a50081c2402c04e207890182c60060f8503100c114881c001c204e5555420141510f013445814801150081c040c0c0c800350505e0660001c0149541403080d03498481d14000c600f01d040d50380700200c116419204 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 474174469 1250 474173219 474173237
    0x3080d051f03061802100504171903050a02010e010f0c140c070315110403061d1b1207030f050a1e0b0711210306100e100311070c0905190b01 62
    0x780310b400034065180714139550402100200700580300d040d0306a034407100c540c4459031600c3c5402c0d02620b044444068641d140c3e04182c0e104031046d040682644021585418030548501800340102d006042000b1400c04640c03c1040c0a03100f415158094072940c6270564a80c040220131071000080c911a040c2e09107101d83c4820810000b00b1000c0b000c00d0f000000007000494414086c81803112250402e0b0015074010b99138001d02a0b44203c2031002000c140c3c18170010300310b86003055948940c203a41c24030149006406114030001400710601a64018503480b030640711821089041083ea82c002c504011940448a8070244090102046400c5d41c01ca901032420703070007595034020894014803210703031000541c414010310250030421281a039807007407110360391603480e4a442c20030000c00480180d0031034240900c00210b111541c880402c030604a02c26402c01107142d60000e00380c0811480b030340e800905031403030301c1e140414580c1641d0042030040c1030054004200950241c032a4040721f10301c00760a40400d042038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 474175719 1250 474174469 474174473
    0x220602093001112107050f07081305090403080402010f0c0606080c030f0f0c10171302010806010e03070b030603070f080c0f0a08031e1306050c070807030b0106230403080d051f03 78
    0x114207a500101c1454180c4c100118110441f0f80b41c0c00c10b48044950020100e510286d10400c108a00d0081c4400c8a0307007051810143ca000e84041c82c0a0800303030400641081a091403805402a4254540c0c000030401c2a035a07520403050310764102d0f48c003441c400d0180d80f04a6840100004200320f8a44450010708426003c890801c299a40441d9140302800042e01031421410101c9464511500c100305000c2291110b0384001000c1c46030061155051140600c0000300c1c94800250400c20f80e0340c0c86a03255035a860310307000a45801e40e281c2c00514081c8009101141e035002c0410300c98904181950f1068080104004008126625010721001c591040c010042c002e004001e210b04080080440546003440c8501e00380030021182d0498000700300c00140b103d500300002c1150748004d01004025180c0a0306503550440c00c0e581c184210020007070f00f00801112100d11503440440d5490041141d540c0d40e0381c0e8a499401500a2a100c8002924040c005030356034070142c001c0c41d50fa8440c103802080c42d90850b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 474176969 1250 474175719 474175777
    0x818030d050a032409091502030c0702090c12130b06090c0a0e0d020306130308010e091c03060e0f0405010c0f08070f11030703080f22060209300111 65
    0x2000c059041041c1031946090000103040030500584600340000c80d15524906000200e5035403c07d80e81c0140303104008001d00010240700365440194120740c1410903440318516400c03d8042c092030402d20202c2141403002d205820790030300800c58421180c00d8003030b0b56044200301d0031213000c07901c2c004070480c20448002140e1080d4034048815400a0424800814640100e45805400c8421580032070b20030038244180754222403047d0050000c004030124500d0485c542d1764807520b50f80d062880584d4000710004001c3d0090708404050900044182c80c186020004a188144152170649070b552030201c40001c21171141c840041000c0c001d8541c4811600c81038011207402d603920304403508014284003c0c00100106000800312140655100c0c281410000300c0301003142c3c00984004800319104040032580710340350001c07070030040c1c000100513100c51050380030566810b65143c480c0860041c0301e00794060f0302003040c66000403c46d010020495015250b0080d03649100f24180604059140143c4035020022 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 474178219 1250 474176969 474176981
    0x4061b031209050f07080318040b0a050108060a03080a030b010f030b030714040e030c0604030f053103050118030f0c02090c0307031103070903150b0d02040f180818030d050a03 77
    0x10540c200e494042c121130700a81050501d800085994000081c424080d001040b0f21404d0790b441107034108142c0025400061601030144140350500180c200099280d40c0c1f03030465a40210340001840d940d4908020380140140889500d080c0411a20020821100c0c032a00c5181600354015005088441c1801c10540714042000145903025403141c6e6841422038050001e41008182c69005125074201881e0103442c20104e4403684041000501050069505003c9002c0c101d10714124100c2c502c540f5081c00c40030007a16608041c2096003005031100014000a43c1c101c940c030700990b140d108040d074825045612080b01100039502c0000c040104003442e544c8001590003030541e04002800e4000203401e4412600115130310303c0400c400100c108103100260400f821140c0d00c8035001c101d070708a14800a40602070a0f0000303030046a50781090100040598400600189640e08081d0111900c1c030b0003140031b42c015421194041c5070810859640e0600080da44809601134480c02e003000d68101040b001040c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 474179469 1250 474178219 474178223
    0x30f030804020f030304031b0e0915090a2a09020405010e04020d15030c080105090304260708100e1009170c0a020a06050712020708030f0f12010b04061b031209 70
    0x1041d890701143d40e8040004100540c03150540118061050890180c0f00d00350390300280020406404110f03000360080354030b4080c5103400e03c0018a944034480d901d0300c0c1000c440c5000741078103000350520851181505680e013003c4103101c0000881c640741d442c90400d9009620825021a003000c003114503900c1d207500a0081e441d0225030005900081e07601c5a842e8007241da2054138020010729092141d40c0d000c2c040c190380704c8854001180b400d031801d1102101d44c0e200040c4a0040c1d14494203010b14004180b1070000140711100854910aa01821800003060340841108191282600e0303c10311054902900740c400e40c01c40d81194190138100300782800b80c3d01c008582c0e0307580e00959003050016a2090004005001155262501c2d080c2920302800c580d854580c1460035540720740d030200580140042159001c104030181a41ca0709140002d100042c004d8001464255070a01e00105405803004042c108589003a903804d0b0411448000250b120b0368101000f800041841c0c0c40300b480001c444d08403060440c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 474180719 1250 474179469 474179479
    0x2a0a0e0a0b040c1211090a0b0a080c070215071a0709060e01020a23120a020a0c0e101a0d090818060f0403060c0e03030c011b11060f0a0b03030d05070216030f03080402 73
    0x1509000002e07071f4411294120369064034000c6402c04000354820000c81d413010410040740d01e446030f1600000e01d82080c08004000710140005c4075000c01c808444103102c00c02816101400c42e0038121005845e007580c2e405130400280301240c0407420741d0b1002030250051600092501005180e82600d40e51240c0c80003000011072181c2503d0443c42601072004000c1d481181d406090449640c1c0740800c8101701f02d510040105480105100c0b00d40c3c3c03200b0350340b404c4039400c403046140a20107400d0340005001c0d041e41000001c4c5001e41000034446682d00030410901c03010240c0d20358111040410a550003414640080c0c9a4144410310000c3e913540d2040c400600a4200380440c0c504180c0000c1c0b8552041c2091001d9944641b03100b5500355132481d011010f103a1605080362401540c031020341c0c2c0e40e038009054840003818480824000c0c20b03d60b0140d200f0b404068182c1e6a510480c019140280809480140052090701d0148a84005019001c2c040c2c035880f208900c20001c503610102c4003d034020b842a6444 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 474181969 1250 474180719 474180727
    0x50f12061501080f090d120b0d0b0105031204150c030c120e03060702070b0a050d090506180d0906050913140a0b0f10022a0a0e0a0b040c1211 62
    0x48042062500c1071510207814504210868001011200003400745107580309500300b403080b0510086069800b09016140c8080080c00800d4868003038100312408a40005a807101c5600340408841924103a82c400d03011070740a0511103903aa00301c1d120f10300c1058840850207440180491082c012103500601915064a0a50940d03c4039090100c1100041000c158001e142400e14241400350a41c0400d840c006015250b184c02e11501061145c58201170800c0740c0095415a01c82c455401942c1898101c001c075071940ca08400001181c2c1e0b01038850b40620310a115000c02c145115101e541c1c01d907145a50b45602b0152201c043c0803c0101410b80f003840d80c0d0302c6102911300c80c0b18017214280701d0904c14001140c8a001d90041c0415110390505141c05034103501c0f159008135800081503100d40d01018400c410207050840110764039079406106551107001e101c000078420100c65825405480b8109040282c2800070f41000700f00d9125449400100d4030954290f09000c00c20b40c4201c12000000c80c61504d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 474183219 1250 474181969 474181999
    0x10608190f0b1806100e04060e090309120601050109050d081b010209010909050103020d0b09071d01050103061e09020c030409090804031e0b0c091f0c020f030307030801050f 76
    0x20785414007a84507909540e088101242d1502c1c1d0044803204464100888540c00d002c0045514084a00c0010f410301040103800c0c1856266070b84031000602110042907482d040002c91603803a980004c111500c10000c0c041d14060024000c10424106e40707050311104800c500e000f05000c5035031b940d00780940e1807050078000b0810061524001ca401c00840744001070307403407010100151410036541c1225500c1480c240050005032946162484925041070326004e003940c8102c81a8541065900042c0c0d031104c0c64003a03071a049007007401c154140c0310b0989040c03040b180c4801c8000b0400c405001c05400c61800c0040400007030701164002c141c280c030b00f01c061380d1415032100c103a602944d0010a080710941c1c1e0005040080c4480318240070500350b0b66040e00e0004d416aa20388094200d4082e05041240000150300b01c42c0b41c0e00d1560740c0e10540d081e4490343d00f030400b40a0016252034107100d026802030340c0070f1240d03814619002c8225040d06900d501e51540d580d00340014840c070b00400b02c0c115034001c02c4c81800c00035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 474184469 1250 474183219 474183221
    0x5190504110705061e100e0c131809020906040c08070f020c1002060412020f0a1b270b0603090d0e03120304050304090b19060c030903120306031a060901060819 70
    0x3200d400103522140303104109092084c0a02c1000344007818421007140705100d201140a00142c0003412910899241c0c0060500e030800200c271640128002d4034200302c00400c0311107a40280c0406802200d44a0055443da0280416207145114920009400600040381030780030301c5010340841d00500c100c2d201265031901040145803600c031100050703880700040200b0081c03180c0c0300c1d81800c80140702500e4802c000107055030b03030394442400080c584100f00300e108624480001d403000c01000501b54084423803261410200ca0b00340e411030002503a90800c0343c1c41d0401e0030003108680c011704600c5c00030f255240100404030b4040d102d0958145d894081c9103a4441009101030213140030320b00a0029664603446e140d000710486800c02001d03402030007146204202d44444081400840b205410003160250062900304d508052980000702944100c010100300d03107515502c2002585d204d1040e14285031503010003040807102c104e402d6030740204008014040144610750540d0411622541c1c1240c440d413145101c8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 474185719 1250 474184469 474184471
    0x402030901020c0c04140106210c0c030e100e0d0c03080d02030906010f18020c1c050408010c1103250f05010b090601050a0905150403020a0308030a060519050411070506 74
    0xe041c0c1d000b107807800c02002c00784200c0340070040445040090242841c0c201c0e50115051084405010740107a544805008101c8540b00195040c2001c11000c0c51a000c05081d24100309015000508003000b56511410000000940d4901e01e481d48100d05091004028000000b603030200c0e400080c2410000002d048140544aa40c174450000740e264500303104407500d015016481840c0c0d4134500c0e042000680704a502444840b04032540c05a900c06030101c0d2030380781014000d851140020700c2540324131110340c4980504140c440b154020700c08010301c0041121100550340c94880036400c10040004c40310144214503482d0032141d49802c00003541e5850398a600c1040c0302003034645945544004500c0d1078144c000581c41402400c000d42095180c40c0c0080807868240240e81c025908601041603d0009409032001168020000c010031900d0b4901001c42d900159200c1c00054140b160229592034600084064680c007403400d540d1062800301044041c00c0070400d0320f000003070208481c4004c650180805 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 474186969 1250 474185719 474185731
    0x30721060e01031112030715020a030905030a03050711030903120711060d0509010c0c030f0e120d12050a090f200d0605040506070216050120070f031407050109061d040203 75
    0x20505844202d402c1c031a60070801e0b8a101703143d0f0070401007036001800040742100300e0080e0800c010303110242c240d400d07001000b02c0740c0090040c0c400417a2880102d903140c1c00691040d070960380c0d44a4a500b145041d1980d0303000c0d03c1e000c10740c190440c01410529003035a00150500600842050000c091014041200c80d808641c075a802d0319250001c1240142090088507200080c0307281881000e00c441c3c030b0042103003443c4542c500402500c004050302d40e5443c80001403c1c4502da030141c484401c540f000117005841c1d0113414105043c00c09001813090034080c8a103c0c42d06800800c4010101800c3d03071900d011190a01c4c03400c0d0814107c00c0301c0d015544946807455040ca201d00c0c00050a401d003403c01d140380240041103c1c00319400381d980403040801698441046800a0030055101740c0c48040b002c03104080403070940498802c1380000100c0301c46224002c2c0440b40500a088503140c0388801864880b9403500078140860f052141c104219489204289031140115040b0042940400300180c180ea01c25901 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 474188219 1250 474186969 474186983
    0x300903090f0919111306110d0807050412060f1a0301050c030115080a061e21080a031e0c0215070504140f01030b0d030e040e01020418050601171e0705030721060e0103 73
    0x1402c1087c4c0b4040001c00c40e040c2541c01d0182103440c103020014810310071390045000c0a8491a08981005a01d0708544440280d038030003400900000652960b5044910414500c02c1d03082c01c020641c1120640d080341e050741c40002c1c0d01507041c0042c000a60b80c2800141c11070420310340c3c54800080e180c11000c420000001904800d40c041403038914507000002c0000c0035100f40c3d00400c0d96050015118504481d080c00003410082003c003a2070305610300000e80219401d00d00350078100d03134001a41d804140240c110031606204075043d1500f103401c50380360045002d12200c2200110040149240c04800d9101c116014500415041201008103808542002d03003140484c100d0f008486440c81c19020300700c0c24000000c000c5040600d004066011034050620414805685402180450744142203409468140489a102504001c000f148503c020320480e43c052000320700104244500c940e04990007000507075206070100f0030fa901e00d220303c00c1d081219400c04d680c3d10203000480e5a11161078034001d60280503 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 474189469 1250 474188219 474188237
    0x2010207170306010903022202070602030105011b050c0103110409020d151d27030301030f1a060d0311160e01090c05030c300903090f0919111306 64
    0x25003010001410030410314808400d000f0480c19980c420860812a07030102c0c0d00420200f21200d502c01c100d81e01514422910b0b0000444105101c0c1e030350002c46c121102aa49d0151703050601410444001030484014655000003e0011240d0b1207038000d40300c12080b86e60214074090b40e4508580c01c03684258580e0002d10740318140c1c58404580c2c5001c900061000c14010100d110028800c1281d070030004009010862031001801c0d0000d110002d5086800990800c0303e43e25616820200265901118101d800d00e00b80c1044d0200c1550000c6958001c0b103000d000d001074948580d60030340d10290101d584107101e01c0703564011490055086420002441ca00e48a1403a41d414070a510041d162459244000c0c0305080081c0180d00c1003c000300c800104c1400b0001c1070842e01c5030050010800380c4c0110714207100c000c80c14807031080c80c040001c0100a5084524000c46241e42c005c2c020b044070101c0710121940b101d40ea0701e0f4940074a9070829a07200039a200400d28140070402d0224810080c1c1d000000000d603404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 474190719 1250 474189469 474189473
    0x10201020d0c0f090e0618090703050d080f060f181b0301060903030e2b060b060307120b030d0f0f030b04050c0903070e0609010302040f150e09121801030507020f06040302010207 78
    0x50f00e04c000b0300003614010846140240200e0010070f403841c0708030b00c5420034600090400800788a00f002441d80181038400900142d88001c2c07024000355030b01c0001c20702c45030108405260815024008510140c04940420001540a048044000d101882524503035041040304c03502640154060080740e120200f401d030031424000c00c8602c0758040140284d4603070031504e170440922040b96400d8426a100706030ba181b542c0c07918a000c0d001d088501c640001002c03003486252604a01070713001c3c803c89440f007001611300c1c4004155545040e2080c0c2808a41d60814060f071182c880e000b079902d0480981004181d1840d41004181116000c80740e0b81d00c1d48201244691140ca4184800c000400b441d0b00c2c88100d40c2025000280200c038180302c028480d07950b9503c8000100015088601824410000c0340b41c0c56a41d107254151041040b0750096481c0603100e1000c0341c1c04003040640d4500e4007040140405800e040c001074005050240011003036114000c4000c1c0c00c4d260400030701c1c3c4a0381c407a900250300c90143d4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 474191969 1250 474190719 474190727
    0x1e050108220b090c060c0c091003080304030f030b0f180a060308030c1206011d090601210f0c21090203070312030c0306050411030406050403110f0c030f0a08120402010201020d0c0f 79
    0x400d0040717202d084c1c20804d580781c400c000107491003c004d007240e202c94640c0b90100d00680740079440c0d00042c203010010003000107240c2c1205241c4d070400040d0304c3c18004072100e4400c202000d0b8005107000c4d800040c40c03140010060901945a603c4401d1180004a2584a8417002d81035001110806e400d5800003410080c241040c0030000c5c0c00c4117086c200300c61041e40002402d8044008030320428041d04080e0001141c989c4a160301c3c4500a94070503200503200e188180420241c020b2040c42c504040c2443d54282c9890300c603011188851001c00c0741011320001c1c0ca42010090900e110f010b9074103103d141008000302d0044840004c03c00203e860000704220076081c05429101d240e8050b61151741f44c209008001042101181e501c168001000580d99856150a6030fa18204100d2201c403481041c003940c0c0b9400d000a507040714600210122146c1c0304810703210b1fa5444245aa006248440600281000040030040c481d081441400094185000075014904032200d02280500080700c05558400140d00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 474193219 1250 474191969 474191983
    0x402010f0e13060905012927040f0b03060f0702031b030d05010b031504060302011707111e0f010608030f0c07052d01111c14040b0c06011e050108220b09 67
    0x940440d2420761541c6c03007840b510234001c01050b2880201001074110381004a41c421903030f01c0360000d00401c00180d510001d0130050440c01011406442003501250700d100d450905903201e801c09900440c9800c42c5400424608104038000d114103100c03c1c000b140550f0031038001e4901800c40503042039280c4c64000c5514615041000905026902c2e03c0c2042c00940d0b4059015074111128100c81c141c0e40d2106441200d04010704403c10402e40501001c80c880410340c590700e40c4035100000211841a51680941e901706c2d40d461199400c16401007140c80096120307800079200900d640c80c00c0e1109540e43e1030228445008002d420121082d00d0240d511090f144000315580300402840c105a1503520709c1c056503a50050703c0f012140660b001d1400c4150744d48540c00907000505d201d10740e55140ea40c3e8001405a41d04044540300c198001c210020642707410141d50410110070f409501c00541e4a840300640d0f9502018101d0800125449641d90039a400c80e45007032011441a850700210749022032406003040c203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 474194469 1250 474193219 474193259
    0x310b130902012c10052511040923070f031202071d0103031d0109030215070c090b090708070903080a030f1d060903090a0b090d0b040503070201090e0402010f0e1306090501 75
    0x50088041405038040586000f01e64031a0086c0b018006040951100011016070b0741e1060502c1b041c5400c22498401004496070165605030414003c4c0703220a4807201303a4000c4805801002508001058041001101144c0130f801510302c1039172074220209400401c1c1c501d00e111190304200402c1010340c0480300d001c0150f0745c010303a841c4032100c0500007401c2c0d40103884082c0c40b440100001054001c031507411200456807014400c40040c1c4d03901001c001808848042034428140b901c0004d4085010310001072049041d6628020a24195900d43e505a0400380c2111b04040da145ca10401b036810343d11405240d0318141ea2a0455060300040061800034010074011803a0024490007841392a0f000042c0c083d5138a503680360741c580b8550300110b01482c141c488007a0401c44804148010703c0303c040003c2107598000e80e28442c132180ca80b03030980c2000e001590024000b500c000503a4030f00504c01c0f04440c825800060841d00d6801c40511180241d407690307003226104950312001080125074a01560344642 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 474195719 1250 474194469 474194477
    0x70501080a0515010804031b1a0f09121303020d050c030106090c020d0c060e0610030501060b030c0d05040f050708031315050f0c0a02310b130902012c10 67
    0x4607010101c560180c2c1031440301130501410070046800c042c0604160700d580ca038400080030180c100c0c0d050029131080c10314404410750440001044100d004080038a00c1092080001c2420350300195105200c1d80c0203441c0d0841c45030755071202200607540c0e5468000b080c1c0c0240c2c0245504100503080500319407503070707012454040c98441c05040c0c464022450015242840c2001e0021051a007420030242002d80020201c5001d14420004214032409294050300d0280008104180e00d4007014a0148007d4400350490346062204008a0f18183c0281d0742c01441580365002c80181661281d242c170104d90003214a81d04003007115007074410310008090051403503038205c140c00b5110300d00140040c42907110400301008005480b85140508200e1002842c1d03002d0604042d4400c030460500c0c0c180094503540d4609038405640760217500d00c40c06610040c45c030080a82590300f10460b0309d28002c01080900f241882500c0090220114040454031010019070304041030301c0e41d04a0420081d4000042c82034144 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 474196969 1250 474195719 474195721
    0x6060e030a0c120201050c0f0307030f0903030221070c060e1242090d0306050f0f190e150901080a080f090103180614060d0f080a051902070501080a05 66
    0x2c80d05140b100c20841d064400d00061040076800104c40c10b12554040324100e10480d40350190910f00080203000b5140240e490b2035400c42c0c900e030103c0f91003810748030140060307000c000d083c000380c0b624141c4070300f40d415030a107110b00d0011190f9030244004041d80c4078034080754017546200180c0c10000030506054403440c0260408001e140d446c21b0140701608000483c88000c0d100da410301020300c0b03004410182d0b00c0d00380d200b0786103000c02e10166a0105050b000b8000b0341032a500042a040807900c2c0340c2e0000300102180403c8031448240181c038200348013030300c00d03a202c030302c01c0060794050030780069002d50200042d8880034245842840721420041c0e00060701c55021a00b8400450a0401900c1c501d02d5468008c650b41c0f44a0700040b03010f00b80360180700c40400202c000c0d20041015030b50001210883c0391071020340304c3e45e070f58081100806c0d440704080d10b940700050b030400004003180c0080c4010766160502d5402d110300c840545414504200c10040036a100b10000e00440da082200303564450310700034080c442 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 474198219 1250 474196969 474196973
    0x9010c1202150114031c091a0316050909060f041503080903070b1c020706090b011203030c230702131404060f0903120506011103030a0b0108060f09010506160b0a06060e030a 76
    0x9101007203c00b030148040c06c80c2c0c0f8083d0091140b01914020840710303d00100c2000c000c0820030240c1d200740e90403007200c10135901c4059101c1c008c0d001d4414441b0001c05521081e9544410301104240321b40d80160300550b200008004642003461130f201440c01780403010b03110658034003494507003501d9401c100079050050083c0e1000e100c06454082d40f2040c82040940c48101519003040a0048900001d0004600a002048400c1d0b001c01200c10b00d4000d540510004401c90410b0b615982a02c1904070944c1c0524440c00703e1001000c000c103282840607044200100d414920001150342056440d45400518024001802213a005030050035881030000c0001042c0d40da8081d004040440a00c99916142d80004416a01402e05c0a11581c03400d416295603151a50302d40c401130480311545800304100c0004102c16081000f055600044098a40300721380e4200746c10424075800006410211640d4541003000060a0b007000e01d000d401e46000106100d800c000c000b4001d100c0c01100c0d03034007e50000c490900 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 474199469 1250 474198219 474198223
    0x4080304090b0a03050a080c070905070305250e012a1101021510141810080106060c0213200f18010c020306060103050c0904021305191a09010c120215011403 69
    0x28106e0f50084a480e940c0b0040d120b0b0500304803059014075800740c640810030080e6501900309521901c500000007803a80c0d0201c48408a625240400c50002040c0a20b45030455000b9469524081c480d00911a12807002c40050400b1010554048441c07240362030003842c280d60104014801c1c0d421745010004545000c04c54105000b1291040d0000045805101604c41d00c0b44604010175507000d0080e540c0c11700e4138203040135481c00c140c4903100d001d600e810000620540300d8800328180340d6004040d280807003c070b03455410282980c20038401891041c22100c4208030403403802808503000c9001c03850b0f1603107110842002203c0c08502e042c0c0c103100c00006990010395000c0348066010200742800585500d5140705610240541e0a1441c0c00030f20000e0026000f40b03900c022202101c008490050010b0045c0425040140c080e2048034580280e04401d044104035441c054100204c043c90700039070800ea0f03626801c518907007901c00c40c1e0150b08100d085030a05030080c480b0601400500d07141d0381c2c4104a40d0003291f = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 474200719 1250 474199469 474199483
    0x7050405161e030209032e020f0702040506010e030f1615020a02010819090501050a05090f1e100501030b1b13030204050606071b080f01140112031404080304090b0a0305 74
    0x60002d5850b000e148854000c2d4140c41d05028042c04491826009406816161000100c0442c0b280000c880c030461841c04c1d4021a199180b10050480c00c0603440c0d4240706c040d044c00b420b40e03414481700080c0a030440d2000c000900365001d090b0020020b00446500001d0309422640003118611400c2200c06040741d000100c1060b00c99082c0380140e501d5072562400d5018815250712aa400b90a0070b0102c0f0500005400c2217010300f805000c204203a45400071025030319406115085490b40214503d60780360094404051000c500c1c4034191207403a058420440c00b203a000360802c59041030380009010704503c03229181d108040074152013501c0d140b01d0145045c40105584002441181c175040020ba160f01c0302c1c2c0944500135400341b404008841391280c2001c0344103250046d5111131240c50000c04000360140203040c2e45c09540b0805a5490342030a140014400c0d440405030240203101071041c9002c40d091380100f00070071034540034546650500700c100064462400c1000d10819000f8401e00118001213405 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 474201969 1250 474200719 474200747
    0xc070807020307240e010c3302040803040e0c04060c0f0302150c0307021908030a0c0513030f03080a02090d0f0302010b0d24090803010618090501030606051206041101030f021201080705040516 84
    0x1010294030780700a400c0d03001c910b0923a00c20442e400070400064410380000034000b0f50b2540c0480c1d4805940d6907405000c0c50203148103501c00030321206074034808150300304454521280a80f054a604a9a500c0080c501c01c1c4150303a1072210b40e8000042003010341d814003200401d040290746001d003003156074840d80c406000250000203416a1885012034450042c03044030703031410749054143c86090303032401c02d242ca0030402c000a40101c0c0200c00051502542c030710855456030001003072603083c408180c071001003070084841708030295965840c2c030045994807040402070103885803c2e40c07401c80b040fa55100c280710020400e52a54141400c4052000400160903207042d07420780e10b4004141c024000c0788042c0310015504c80040c0c18a844004001d00c0b25540001c4103039030003668070011326042600141c3d03503068203c40c041d0054202110300c03140c543c40b0b0b412154a00140c0000542010b00c181001c1c4003250082e0f1021b981c5034408031040100382804e02602e07134810358903000b03e54203040785003003c2c114800201030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 474203219 1250 474201969 474202013
    0x90d1b051815130e0f070815070203160f060e0c0a080a020a0e13020a0e060f061c090c150306090b030102040602120f0f0a02030c010f050c070807020307240e010c 71
    0xc0030318203207840d13200451080840701210f2003800306020a903107072226401031b10f19500400302d01030b84405e200b001e03a0340a00c007142e0095113042c9400580c5003420f08910350843d103245498a2203404a01240190f2544e110741101405061201d0001c104095003241d200c00c2c126000342d46128003590790034048108a807203a4521807810b0307035282c0c021500900300003002584080004000b14529101c1083c01d84604400e64400c4024540781c1c04010075401513004d1410301c0072010b4020180081340b4ec1018411600c1415548089511080300301c4003400303203612510009070744010401c1030580c14080e40c0020304058000f180340c103051003402502c5030750b444c107075031401300f000030f02c1112403016442240c0c881038920707092546900090900035101d50100034031001c55828a03d020220030314510426010310807e032051450f2000ea0b03070b9500e2141e00409400d81c0e150050070707400540c60719a14207070444d4400e54102d1300b4148a0211002d0101c079014100c0604000c44600204001420702e86412030809901c48 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 474204469 1250 474203219 474203239
    0x180302060d06090c090e070207030f031b08040b0901080c0f0f07080d060e090606030d020d030e0705040501030b010e0a02270316060801061115040206090d1b051815 72
    0x550700544900c0c0e00c0a5400c43c58001509203442d4480c000700195080800079810b292240c0200b280d680c4042c0c0001b03448800c54504680000e4050240d01c40803494000c1c40061070740c2d00b61200c11050300315a01011001c0d00000b01000c0940e40203911940c08490f0101d0241080c5401204503810b0150300c0c001c088414000400034144005001610041c4403c10000d00c0519100c3c9400404400305580c1c15000d48900000b1071114600451000714280300ca60052200c070043d503c044000d0a611101a03009005840d00410300c0e0700c81d405000e01075402500c80041c10752520404a8031440002d001c042864030501036007103500034000301c503441140101a081504c42500002900f0400c047d45d40702001d03568848005202c80d0172105650480381c268440d0616110b5801e11140c0721032088001920501400e40042c3c01407402e1000f8101000c2c002d000032a4140441d03491500c611100c4825000840e00303054101700034607189030400340c403941c40c142030700c01401c0110040d130749441c400c40810301c100c41880b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 474205719 1250 474204469 474204487
    0x1101110d05041502070615050301090302100b0a080f01140c07150b1210090302100209180901060e10051f1709030c19061419020d060b0d0c0201050718030206 69
    0x80c1035140343c6a4514215510070082c40c02800404601a00c5040000c0e08640001c207441c047c42201405a090b0b0007802401640403900c038020002c0c0385840303a01805003000441d200a04004075000141c11070000500380000301046a50201c00420740d14075504108001c03000207d05840e201d490106a05002c43c06020740d000268840300f82c0040880e85114010940743d1668190f048144180d010360265050703110350140f24030a9100d03505509411a0f00e01441a100c0030002d010380d80d00c09240d10000405a458104c48940400c040c4c8451a2508400d8400d1065162080212820040e10000324004141c80e240181c1a6143d0440c80800e0320000000100f0049060088070754142d0008140c1d51685070004004100c1880d4100554206207495410000560400a541d01482488052180004113503c0180c040d62101c1031404074543c46590000381e002d05d24015001810584001040365034600d00c0003821a6002800b039030800c8403000804544100300d09100c010f80ba01540c40070b560309684 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 474206969 1250 474205719 474205733
    0x5150715020f070807030906090b07170f0a090e0a09030819090204022b0203060127030b01030b0a0510050114090f0a0303081e09060a0906090b0906071101110d0504 72
    0x403000103500c1c0000840f0000c000d08500240a054400c2d103a9100306501d8410445281c03966000d02c80d03540c8020402000882c0c1520300f0342a507202c810000a00c0c2030851601202c29412014564003c00c041c0102404142a80d44045500c00c25204041191001503100145007440203011038039001070641c12090703070404c0c9411809030301d50060015547c44c84640711a40410310098510301c02013440141c00f1008001e54000c5034080c2c1016550401086104580314881c03498140032070001131000e240020000345a654400e000b10300031088800281380083d01c0100b603400c010900084005291400d004980c0c01032032000c2c1106182041c103446000100c0032600d4240f0214410307500100040000007016440a4858800c001d0300c1c40c00411010890444e12191005a8255550b41c22080008200c04d015610400c80703d401540c0101d008032054851040c41802074410704a650018030400c215035400c0b0b04c9050401400e4002040103141006100106000304100c1d10001919140400c0a01c42c3d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 474208219 1250 474206969 474206977
    0x303070f020d120e040b010201020c0c010e0118081c111e010906060e01030311031303060b041803120b1219030e0316060e010504050607141023010515071502 69
    0x8403500e44a07030803e1030040900146000700303045201c2c03801c0c000000700ca5441802038421081c0b8481c001e1a124072800d005540000e0040d0003075041208085221602040940e6440000c0c034282d40a040024502d604005441580320744080520a00c0300312102c4190340041c00f045201d11400781403200300a0500032034090180b24001a18160a00001059065104080c1c9040703a110741c803010035000f080ba281035181d024440c4c10f074901ca505c0440c00c00c08035a0b1070300050f4102c100203000245100850f402c01c84034070000c12098000800d90003420510300d415125548103800300b1a02c07540b1000c8201310941c0c0d601800c5400c44500c0d415418540e007014014103205845500050648424819401064001000d00c1c450f402c002480d400c20003c8550003041220103980d40900b00303034070b8903400b0b44038032442504440b55034a46108002c205010411903125040b05007200d805907010701846c481c02803403210b106030002403144486600e1566229014011118255800500c503201107500d80140c1000740a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 474209469 1250 474208219 474208223
    0x720040b030c1011070311030708010525020102091e310207050a120f271203020a1209050918031b010e03040f08060f1b0c03040b040e0f01140303070f020d 68
    0x4505100442040003991140208034015411941c0c9c041e65010601e00340d40e0140c07006030907440c02c0c0c0e1120440c052004050b640e020b02c00e00003d41751600110118203000700b032601c4018138660022410741545032182c0c10520f254820021181c20951060080c003900480e0710380781c030416600250a00420405020350000f480e007046541000c8100d00c0700151495100244810025200f07446103550524402a10b9000c4840384c1c60009001c0d0820160400309095103609070154800c4186601c0001d01031a2900001c0c0c0042d550341e40d01d245440c0c00c0c850b007200081c1c5980d103e0994035441040310038002099400d046244811032002c0e503190000d640c0107204180c56040c00b400300080209842e0250b2454800700e4a440d0102c482d00d80c0e40c1468440c1c2e081040d560350100c00c501c418486440e02140d07003d071401d44900800d480c0f03400d64035011482c0640c4258400d071030200d502003c005100e420360140c64010858072952814030801400020b4503845050001490707040380c0d012000964940400c844c0d00d0f1a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 474210719 1250 474209469 474209473
    0x30105190906060f0f0201020a02070605160b010b0a0e040608030d1e06090b0f0904150c14071203061e0b0a0e090a0b040606020a050307080a140720040b030c1011 71
    0x1d840f10070081c0b00d61548031010000c5075502c1e8002580d91b105200715a0740a107181d0142035054100b9008861582c4003c1d52514601814080100418200c100c0c7d0b500803d10391051964403d14040c02504d08080504524031541c0341a500304030850010040310000701100c00002110003c02d520300841900d20300c5041039107483c00c44041084030031036105901112040b140c02550701f01070410809a08400c460081c900030143d203a00301180d1b21604102407904103070074240c80d03911912002c100b003a00804420f80c0c89082c14021000515014480c8001900c00141c14000a901e40414408001e03014424104141d40004a0307040c01071080e0004090b4890062402009040040b6024050168081a184514589800007a01d00e0001681c0910986c1c0130020b541800100e456904564104402c007406002c020b190720061541442c0c010300030300c0d12035401030030002000340c9950030b51110b11301c080c0d009620b05880e000b070507640014229109201110110529005800201c8000b00c0d04420191a4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 474211969 1250 474210719 474210731
    0x3010225050f0607020709060e07020c0405060303161a0907060f0c020f0405010e0906070f12090f0c0608071d1e0310020f040602060606030c03010e04050307052d120301051909 77
    0x83c0e41c1c007140d0801115031f02c0702c00340001500d030008001407031802e43d404070240e4810030745179200c0e003401d80050b0362000d0024190fa003480a00e4850703400b558a400402c03180813888040ca41104080c0000441d0042d180100030310846040c24409070a10303840075001d80c1480300409103402150340d01c03246c0030038004014101748015690b0380034403030300c0d200255a00005801a4000138101030f200d50603100c1c3c82c0e0000c2c0c0e1034a0782d451000580c0d500a1071780b808207072031950f0048082c501050140c900c840091442e65504a11441c14000c028060403000b0000c0c0594500c2c03100e6107401e0398480768000c10000103c0707103881200b07142e10006403402c2003800b41c4880d900e002042b403408402100b0040c0c011a0059000d591040e0784580402501d84421641c002d042c41060006001c1e02005022080d0702600c104220381c60a00581c9443c0e280c8541070201e4943e65913002e0681c1c8682c4520720720406074460a40040000d4031066403100b5450105024160150316502007010203401da00c05030380010076240c2700402c11 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 474213219 1250 474211969 474211981
    0x62703050102042714010b0f0d060305030910030e030702010f020102090a030c0504180b04060e1f020706110c0a140c12061e161409120703020f03010225050f06 70
    0x160710b8101218071501d0882102218152002e030051800001080301c028000c6da0910180001d640c00049560013200020701000b8007603041031246001650103000290f40301d10107182000042503800300c170a010541004403008541100000341c81c0410350900b000d9100c500034801c22070084c01503800c2d03140e124072002e00c000b00b4031103000e031442c069410030b840a01c100303040707481d1025540341c030030308001d25041001c80083c011460503404105a091003034141c601c450840c0d0507403164500c484944209490340040c800040202d03030706c01d0380c00300e10805a0050500c1100710300e69403a803c40200181401c0d50b001e817800d840440501940e00300d45c41c01005480f500310989107035903481000300d038003001280071103007120140f04190310450f10448900c14062042c4d24803403002c44a022035824281540ea8081c440024241e8072180002d1103c1c0c1030400400640b4907500404c440e445e13562521324004e9104001c0c071943c480e45042d0450780340400c03020080b011752041c1341c010f28141840300c116096000b141d0501103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 474214469 1250 474213219 474213239
    0xb1819030512090105030a0e07030804030c05031c12240308030906061c11060904090b190b030a0615030c0b0c06010803180f040f0c170a050106270305010204 69
    0x3528001e10449015140340c200d29140c41c412003045502051007800010701070302c82900103078240c1d131b0b182054a07240e65403652840c000703030015002100d034030791030280a00203801c0c10054020120402c41690034503481504d0040c2c04604210443c0413030380c2d1180050502c084100c0f0070a4040c048540d180403440c1d5903070401a07140c0e0415503000f082030141c0b5021480314541141c0c180240040040780104150840d138882001a1840003507a0308800c0910285440369628800e440810303000d550300030b140b0324100407a4040492013006000e0f0303030703460002400481c3d1030010307442d41d0a0380d2100b4005031f25004800070411201c0d042c1d0004045565907000072a4001030000909205000719048a0180e604ca045444e1640203211007003054034100c0480c0112071030400110b90032075002610024220001000400030785100703540d40804900140700001d207480700c0158056114144000401c0b4650428100800850340c85c40f640c4c40445d1000f0404c00450311680304440111381c007100842d035030303603803051040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 474215719 1250 474214469 474214519
    0x603070b16050c0901060818070f030609060506030d0801150302070605130203120901020d0305060f040f0218011e111c0c030e040207260c030f04090608070305070b18 73
    0x4815020f0004400302038106801c4190689140d501e0382e45156844008040c52003005200d0710041340f08540000406225001926010711301541c030129050b19181041c00643d240942914040c2e03010b540c4040c01554480c25150641b1160100e5903000c800c101d00c00c0303001e4041d40c5c002500441c0340805001c031400d01d424100030f41900c01e178151042a6000c9481c038145000301201540540c20407003100480c81d110750302c941d034450b00003004055a110800003250844100048000c5141e42c0010f04600d94020800c40b400b40d40340c01d2800058032841e074a07000d40507028050040303042c410b420616900c0707071000b401460158651440b011b40040750702c0c2001044c07a01401c0c401c0e070101c1d503140d00240e61400c1030700890300c506070007100301811440b5210380c80800031410380c43d2a100e98403c0c40b6020081400380020320606c3e495214041e11142411482c0341200c2841d070100301e4946c4824404c000090300859560216940d40d040780c0d480d9402c491300b002c1c4181159050b244d0100c0c0c1c0148440026241e88116 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 474216969 1250 474215719 474215723
    0x110705010605060c1504140d03050106110106031a100e0405030414010c021807140d0203150a121e0c180c0f020703020d140316110d0c0b030603070b16 66
    0x1e00101c1d9640092001a1140e61983c24998210100c00001c000949404a402c0752140004422006080d050142402001812040040d4036400108561a4480c4e01e80b500c15039020000c01a0600e03580e201a025142c070443c814000030000009a10b502c3c4900b88a801000d403903d4070340240c5030034a40300303440390304c940101503c4091401084034035510409428940b2503014224441900c0e80030b600301c4c2d100100030010403c2015075120303000d65040043c05008455000b031000358480c21304464450020310345001141c000c0d12102c0042100c24820714082c0070281d000b54844134411101343e5511a552074410340039002540c0c0c48400200c0604082c0e15051703844941004008284107810121400d01c40912483c0042e44110303001e20243c0b41034030240b154503204a0040c403003041c022807001c0c20b54100c800d6034030544160b07000301d00510912808001d1580000c480384110781c541c944da2110f40a0880c00b409074003000120002d51107441c10401100688100744000d41c82e05c0a0092020380c1c1d60815400b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 474218219 1250 474216969 474216971
    0x27031107050a0b07060f1806020705100c09080c030c032808070c080d0908062805040b0402012303010b0306040e0609010b0a050d020a0b0309100507051e0a0903020f1311070501 77
    0x40d6151701c80da180301f114044c5a010142c070040c0e140e291507580c0030790040345041c2c415000741482047c0b8401c3c940f0461040160366200e03074041524254503e81458000004a80250044108440d46a60214407121640c1c000e01c41d4081000a021002002503541c110042201900090410610259030300d80350845a0201c00c90ba42d070100580102d0b629801d500c80e1b0b50040e40300a010405000d010f90b03080f00c0e1041090844814040810041d0b41034a1080e101916030b0b4241d5402d100c29540d00109580680d0044220000740f01400d48544e100d503c81440798511040e4044040b60a941d5a80c101114800080085400c41d08003000e0960080c0000092507224084804000805050540b481311186400034004032441d0700e042c2d09000a540000c242003014000c140304080c4007001031250900505640d41c45d02d0b11060f030750350000c400c01c041c03032064980600d052208980701d9034005000700c1902da05603417842410260070003080da005032100c8503551003030070002c4045a2414a4014007601401500 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 474219469 1250 474218219 474218231
    0xa080a0c12020a0c05042004090605010f081303180b070b2508040609020103020f0a110d05091f141c0b0f09040b061c060f27031107050a0b0706 63
    0x80c090b640c0da80300c040b000303141380c900400030000d910b07081d40700141e42a003104006180301e5411204003120b6100e138105103003159640304244a5564000c6000089880608049065090064141141d00b400e82402400c010301c0201c0b460640355400c1c40e80b4010420600200c1d180c02e550300e000610038004450b0807a0354018a0b0000d68100011400104005030303585603216203848a840c0c500151603420307011303410f06408000201c0c1c414102001088101380c3c65443c100140440c48480b070a1502c001c100f50200300041c000d000059468001702d00e01c000d400080c0308002c14948000ba902031003011600d603481c6402280a1807241d0701303034001c140f0800c8031800400c40c0c40c00002c1000940031084039055007103944980028001030b0308905064228000404005518600316040b03940b03800d9008080314015102d400d0f06440445074004c001300c1c40440041c5040800b0708101c94000340c041c03200040c0820a1407420004500d10a1004401030140901840f0006444011607601580300c00c00446001d403401c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 474220719 1250 474219469 474219503
    0x506060d0c051b0304061710030503040e1006080c032223070e1618030c0311130501061407060b1504030b070e0a031113050a06080d080f06040504050a080a0c 69
    0x31040301c0c182d40795900c6400000d520704001c141c2c51f240060411120159400c8080302146042000c1d00007090010300390300e01841c1044a00840110503840f48040c01501000d02110a0b40c11050300e43c803102580380c520f803c04115800922082c1c007824060180301100242d109103844041004d9180c140d444122600141c3d00c0d034540001560883c0d4001d00181465029500d02d841020940160041d401c0d0892046490f5102e415030404140c0c4115400e903203d80d680d000340d091809410a040340100808c101c6980b50a80113000c1d0408102c401c2501c01c0c000412a04100700c0d603100010000e0040c05903c020b06018440d242260301c01d00051300d00705400c000080b0b041784a000440b2440c1d8010340100602482d55846c0c01005900410310b50340a0b03058074105c2d0341c00c12640b15040c40340c0c1c042c0340301041c01e5150201e21414900c85100751070030010350004000d48505e00b488141d0b0002e4043c2c4001402e0346e2039040c1107044c5450400002c00c00079000903290a0f1036030042e00c2040303942c092190590005809 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 474221969 1250 474220719 474220723
    0x1210f0e011103160309080403080a1e03021809100e01080303010303031d0c0603060d120309120302070305040b0904060b041d1819110a060203130b09090a0506060d0c051b 75
    0xc0314000d090202e04c0d80920455886500100840c03485201e1244c00c09450b641c03880307031903006490700f00c00040d44a0f6041050089140074203800d8080ca04045240020b82c4003204c0107a103108004e1401981c001d03001c1904210a000c2080c0140201c04c0e00c0d10742540c40755411a01e940c428441680064200001160940440d003200081c00044000811400ac951000d200300f980004150952104070200c4010114001d4000d00c5c0e0190000d5400249044583c0380c01b03050600702145840401d07105220090000c0d400030202c0d000d0b156144400364844d04100d00081c042c28054015400c00940418001032446940c0d403003030b880b2000590ba103a0705070380d0642c24500c040300e5698020401e0380b0140220915901c101303040713400c7c1c030300501900c10543d45060108040c0c400710340c03241d00182c4c170000361103120040310500b05000c0c0c01c01046031407622070303014005000300c00040e01002d0566500c00104020750b44120840d0700e5941036042c1480344450750140504103402016204468140c0080c0b520094500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 474223219 1250 474221969 474221971
    0xf03060a0e10021b15060d0f150e0607120e07050f12010c090f050f060712020a120f0224041707050105130605100302060a0e0a12050f1e0c01210f0e011103 68
    0x1814501041d83d06403910b111116412100b580d05016001c1270100204107800b1f903d03400c020700e000a040506240c0700007041c040f1103100b51003045140c08004406800082280c00445504442030a10341805138005000b00c060303d403a25841d50301e0724a08141054110f050201101c001d1541c041c0899503c50610175010301c124075666120b00208502000608030070301c12152000d940c811113100000030b0740e4400401d049030180801244002c0d01524803254108100035004039188154814515139008400011101600060000204280c280c4241c0c0c400000d880c43c10f43c0040081c0250300b4154040c0386440740c080426900d960030b2400058404070728070300c000e049980c050881490250012011a0840100d80c000341c0e00000207180051500d0010010b80381850180d00686400844104014980600281c210a6070b03c000012000c040902045d007040c045000c0c01d0052b802103800554411004002040021540c034109110144c11a030381d1165402c00001d4000700b105104680c0c0302e10040c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 474224469 1250 474223219 474223231
    0x108061f0302060f0a030905010c030219020f0a020f0310050703020306011704050a02220e031908011401030c1205070c060b041122030b09010f05060f03060a0e10021b15 74
    0x22042008007030b00e202c0c200040102000306d180008194072240c1da40d900707407507074840030a0001c1c0d0042040081c2080309451810380e1801800101090341d8984032591f102d08803440042d118140d4040121000d0f2014003101d0000c200e80c0e00100124541a10094003c1d003094603542c0c0082c14400702d00d02100311281c0002d02464001000b003501d0280345e420441d2107000e904c0150400824020540701c9286140540c0c01e180ca46d40000d1521001e110001603d41c03140a411081040005001044800c4c01c40c048c070703a18204203280201c0e0307000003000c0650700c00c54000f8031b00613410300c0c0804020009600c443d01030030081c4903180c248401500c00c1d00704025500c036010100c080d80b608020b194400000c40903c0c10329080c41003400c0c039160740e9a40360500c1030fa40449a414141e51116460031041c481c500c0780d40d501c050b0440d48444007412860100b03a46500c020103084c10669602100d14451701c0400a4580301c602da103609650b544001d1102900c3c0320681200348410b48900480421041c400e0071709180704131 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 474225719 1250 474224469 474224479
    0x303040b010812031e04020102010209030f0c091f090b010207050d050c0102070e070504300b040b0c040608040b09070b030703060f0b04031a0c07210e101209030e06030108061f0302 79
    0x2c45e11700307012031040740078200f01e041d9917080006039240e0f2009e101c0b000a055101c0f01402d0702c0b02d5034a080c040030b403400a1a1030542d000e0040c119060552851316030041c0c450300c01000030407201150040c2c0c0f40210b15000b090340030b180480702e0420840c0014140510403800ea0030340300510fa8401554440c03000c10f4582c1d0b408554140001d22000b900b64080c81000c0b0070354100620340c1e082c0d01103007842000005100f541d811400200b04400e00c85d14414150708403140b0601949850f02d821001442140050030044c451000f02011458041040101a014084000c5956913a0901c000d0140091820703105c1d0703d0784032444a9000070f16482102c00c0c1ca040302d400a280d9100b811103034206e842840c00080c02d80b6600c0c00c0501c5444003040e141700103500680e41000004e509407440c2d95024003107050b04081c852041c803880d405070180d942c3c054034075030034824524800300c0c50501c10b2406482c0401400e101c2c0e0340004000c000081c81c40c02c0000d526008000c1c101c00c20301c0341002da03a06e0b03001034240d501000e9000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 474226969 1250 474225719 474225751
    0xf0603020906060f210106090e0402030303010e1503010c0509010306060c0f02011110050412030f18080309030c0f07030606290d1112041518230303040b01081203 71
    0x1d0900d400200201c1d0382414184d441c0c40e0041d02d0f20b282d8060052008121444148014050302d85c01c00c50a034042c01011502c0c0e1f5040c07800713a00181d03403403005010b413249445014003c505407e084800601d20800020000d004811081c44003c3c5690407214040f40028140b26000407018080c41204907680c0e0000501807180c1c0e006c4c0c00566418051441c40b446c2445070700b03180601400b084c41094040e0f840740f000c0464582c20008010b0030b0350440181c500e400ad1074245906500810001c1c1c0d0600c85611010350740e22076803445651401c1d0b00410480300750b14003409050725542440810035205691060504210868981680b41d118040783d40c1d900d1090341d20b400e011828424141c0241030f40030144103001c28808040c0045a905c1d07001a50710500c1a00c03038000348820000714070310b22a9850303030120b81004450040445502c001c0d481d40c8000e40b0b041891184214030034401000c40051941840c2103d0340e908040c07400c00300f100c10034440e1101390301031070001c4001d807010403003140e00881141c010005c071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 474228219 1250 474226969 474226981
    0x120612080903070509090307021908060414030f040306020c100504020102121e0d0f110306060d0203060d08040f06270e070e09090c010908010b420301090f06030209 72
    0x140e0381c040e006455043c841c10500090680e140554184654000005035031240c1c80c601c1840203000801560728041c8200b40ea0500103c4000164243d12036006918400c200301c41244550130743c840d000608441e140e000a0104c244521074000f481840105030440e2080e1360070040702001c84905940c001d00603048040003515251031040a0071420720b024401e82044141e0000b410210752001010341c182c00d860707480e08036400616204002c004005252a0b92075442d000c0c1c0026100d100f000c02d40c005550380030020400c59213581ca050a0040e6021620130342c3c0f41d8541c44006c1c1490418420000010501c040f40ca03900400e19401c0a200100d07241480c0c8011305040a210703015400514200402001c500707005150780e02c1b01d2956001e031a022014102101200c0001404d40c43c0c82c0e08250042e03818a01c09001c0c1d511103032000904003e2052800c3d60b4500c2900ca80d5404040d00815003050175100480d854800c456140214102c4041c0101008501d20000001064400318400a50301c00500400030300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 474229469 1250 474228219 474228233
    0xc1009030f051c0914010b0904120c080d0207060209032107080315031b0a1a190c0c151706100323040f03020c031c201507120612 57
    0x504078182c0000340041c210f031601d41c102c1e002654261404220360040d071008900a105011400300709445070701d1a031a140e111601c021821074801c104020500020000b40010041036a6080c2c031000d9081d952207049041003400794001041c941d1007401850b0780d010349031004034900d0f0f00c03a210942e43c0e81d0030a80c60340c841500700e40001706181c04140114200b42941d039428080d5004c00308042a151080c01e5180003070140c458629045829a07480902e403911030000310400341d454007002407185082d9009810411160208003a80060008600e180302145182d610b504d034441c1025280e882d100c1e00e00e980498681c6102080c6c42c607940007c40d44441600c514800c0d0090b01a450030350350036900640451000d90301000c1d04890030b540e0002c65030142c004141d418007481400704030850090002e01d000c0c448024511820034241806c0c41024600340c0201302d02c48070300300d41000d0f0700001d41d5400c5050228100c2100e00440f10100000c000711030194035180d0500c00d020558424240d40d0820b421a540c03480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 474230719 1250 474229469 474229477
    0x30307080f1510030b030307150b0a081b01020109020901060908191a04050c060f0705010509150106210606050a08090d020d030f02070b18060f060907200105010b0c1009030f05 77
    0x740401d45c8450144156440c1000200f400030b02c01c2c03883c0d50a035040d580c9004121003009541ca4401c1200420400001800140340d4101840d0b0342c5100000d240e240005034014100900700030341140c004400001c2c00d41e04410b13000200c071a0711080d240d42452040c400100703803a001c0001403503c070148031200400388c1c6400c442640280700d034088400031192900014025003141410240d02d010010350982045028080c5980200e800801080744d41c1e0800c07603014a459050250340300700512015540c2002d00e051455072800307051181c0802c0b5854641e40010800d0f804250b418010421420100700782440c00100342110380050340c083c00b20719822600172809046d1003410940f50980a00580d80424252a0f44034062000f42d500240010740865140c0e040c504010244035001c0c03916010017134541c485034201948000710f40340449040e00c00b011110b4001e1564a000d0165610703100c004100f80c681d050003840c90f200c0e40821109640e280344400b10941d149002c00400041c01d0a414484003401403003d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 474231969 1250 474230719 474230749
    0x1c08090114010f1706011a0d110711100804050d0318050304090203100e011d0402130e06090709151e08010c020610090207110603071808030307080f15 66
    0x20a200000651404103a1002c3c2c00140041e0100d11040100d40610ba0040d42c9000051003d815651b14010040b82c00c522440c0c0401401c11000401c103104001a502120f00f51859030400c036201c400a00f460441138040780b140138020418100d1901042d4050410141304d00c0c1d202c0c00400c01c40c0c0b1501403c40150000c190451800d44941c040e250001d04203001600107020340d51801a101d20303005221000c2400d840c0d001035104c00c6000014454040000720000300051300e10300c00b58258a451001c240300100c56400303890560310700411505282c40200c4d11900403400c0504a410301c030b454014110460b04402d408810880c4214404c200f849410766808580c105002d042c201c00c540d8400400342902d25032008400103130003120400103041c01440c0c5100241420090850900e05240d4a0800301501c0d0190b05214105c0840041d148030310900c2449002551480417034a03c990b01d01e00141c0c0c0b900141c03400d0000c01c88840005071501043d132055845900c44562800388a4124000c1c0041c09948401e1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 474233219 1250 474231969 474231971
    0x308061815211921230d05130507060f171503060103052a0609041a0a0b030a11072a031425080a11060409090b04050606031c080901 58
    0x80d034128540c0600c0240c00104080742054202d540c035203004d10384159551410320386031413014444001c082e444800603035078540c1d0391580003e65400d42c201d81e8086c01030307200c07801c40c0c1401c2a04000c41941800003203171105201c5c004a5203525120081610542040c0300d2034000103a5001120001b000c04031211904521060145403070200b013603001c030342451030981080d11142d1000d155600340c29948020020309061010303290500031114070000e40c00e4400e000c0c1c1c0328841ca8807080034514080c0d0100782034000c108000c1902110b50fa56007880c0403260800c84003010a10301c1c10040328040e40d9550f044500d0b9035407007546524607040407600d801d92242c007034481580d100c1c8021404000281005441d49000700380c00010000307900a4040b41c41140c15848003045006200e2100308003400b0b000800b44039042d804a6404090881031000c0b414078062a44901d03416824800c3d03c0b8140b00b072104001b8003d90103203040c0e456561724882455036178059504070b610351a905150a030010351062078031942000c84200 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 474234469 1250 474233219 474233269
    0x20304110303030403110d05040b07030f021002040f051e0603131a2401020f0c040f0e031207090824060301021e04170705060f160507030308061815 65
    0x8003003031450f0021281203001c02c00200510404004c2088169501c080f2880d00c0b0780707014200302070301040d8000c0d0f0074010b0612408070903040030540244006003c14101710000c41d1620f45c3d03560100100a954820303180904210000c54a80540100c100c0c1c141960180040c0d2450315444030340d5140515111003130390585000503c40d46440380142c40f0328010701c51070021165070348240c01d04664090861622a0565102030a0540c4010012078012080407049500051150a002190002d400d29015040f00c0c5e010019020300c80128000300300c3d0103041c00d42d64800505882d0180142c3d901241003110343e004442c0010301c09100f4014164a902c01c80180015041440c081c41e2480001042030003401082000b140a015445044481f800304000c1900100350151a150110381c3c68481c150f40341e44018400544590041038500e080303100345074010101d48650741e0301c0c100103001040644015105a1082c0342d00c0c48000ca00683c91402407464070490805010a40700700220342d100194450032081e0120303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 474235719 1250 474234469 474234503
    0x151b010204141c08030f041103010209031e071206060e13050c090717040c051509010801030b0a0908030a06180903050307180b070807110102061009090309180c0306090519020304 78
    0x138014600031005003400071020b04040c5019030a04d10406101e60191303105000141082e0342c0018452440110540030701c41c1401c0030031a0504003d0550044240d03407005941e4601007040982c00798003140d0b461000750500752141800e000311a04105001341c0701e68001e0182ca4914a802c012142e04501c1a0a1034011105e50102050211034211001d444c0240300801c2040242480401d0031003424442e04c080785800e99010000e0910030341808080c01d042020030004032803903a5030f07200c070102c25003192000c0c0e01e0b4600600c1d000d0140800d40a00d200c048d0511595a40701b1989020f401c41142d496168903045907244c0c80104e601d21002482c0b015143c20080d030016103510000300406841d8020b5070a1070f556074003401c0c440a12074046018504551001c010042101880000b200079500c5403400840e4008250404440f131031444d0300589400d0300300d031307030300c102c407074103207074400086000180c8043c0150359445c0280030454200702d68030028040d40001ea512801c403250300a5500c140714181c1402514501 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 474236969 1250 474235719 474235733
    0x1006080f0c090a06020a12030e0d08090c18100803030705120907050a090f0509070305060c210126010b0105160305070f0609020306100305030f03090a02151b010204141c 74
    0x90340150f0251304428841c03424080240d44d19040207d0a04041c007403050700c4a4450345c5d544580005c3c00412500c5404120060b8040c01885008400140340b4a007110702e0a038210101c42042d100195003c1302c6c0100000c150001005170b91103404152125410b024030506ca9201601c80100840032502a1810114059803404d0701b60b005801240750004142c0020340443c411260040d244d81c0007036000703c10030000100c002a4240d0301c01d0103a45000d446042e104001c000044a025070200c4580420780040790400d100d515146111014121030250f40010701d80c501c0c00c0b110071100c3c1c280001e40410481c148100039042200050b886882e0a61410500351101d4007944200c1c01c08039240c5480703122460940c6030800060b40c00014141442c07441600e50303070781d00d99a4490403540c8005654044000307512203009204044c1c0203900035000c4851812070070444070260b0321103017111074805001000008000014400d03a02566a1034078490104030303024007000881506907080d480703100c0040710820006860 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 474238219 1250 474236969 474236989
    0x40b130c0b030709120c060f090f0b0a0305060603090a0b130804080106090e03040e0103030309020607020913140a020f0904140f0a03020105070302072102191103061006080f0c09 78
    0x200944050716400d100b500141380450791362050866240704000203010031003c403613a40403180c41d401d2403150040c1c2203070103031190392050b031050b5000620908000794264641004042d890100d980811a5907210003c01c503280c042a111000e8552001c0c0c00c060008601c01e4102d034110066103441c90360403000750303507a0f011a8895006455282d4454104108001d42d0b8014401c400b00d0585c0514101420500f50b01050613051001134205901c0f07620900c299150b07141100c03a4290050710420842c0390021002e01c0c000c00c0c104003100e440b030b804290250036003404944010181d50007414800405420302c10480800005041602d41c21404055400c603a00e040094201c101d4060014060100c01410041d0850340010100014140108910400036003540b102c0e038506080c0407041c02c014090004224908081008191104001c840d480b03024490181065080c04001324110740b2680c1d01d155200c424410300b4450300011880c0034001c1000d0500000760381c0c1d0711440c41d1500360308100701d0310002110907017 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 474239469 1250 474238219 474238229
    0x31603020a05160605030703020d271401020903430e07090b09060703121802030613030e0607030c020a09051801050919020a0306091a160503040b130c 66
    0x7000e80700c541d0030418180102e8040c228801a5042154940040a41240701c024a4601010b80c00150304821b019958021207011100d0070386981c40041002c0550b07841c01c8480001c1e0b80c000b51100590071500014001c6441a074009406000d00e100b0f0300806484078804a0541d0640e0004a200100d09001090122043c1c4045050b405480e40c600540c0c0251120042d01090411011070f4050101502c0c074070031a54200025140c00c0e40d107441a007000c50300130380410440000ea60601c4140e82110743c0c054500b2680a0084054981076191071010101c003407008980240410701c02c21041c5220324080f405005514020300f441c04035003800c0d070700080d110f81c15900000c1d1400d5950041c000a110121607090503004810020031260501c02d0140303030385001a80e03c03904007d040204460454407105c16460046a20400600c00441039141009103001d94884480d81c02c2c0001d030002d10b0010750000b081c802340c05261105881c58486840f070140208006003110000751113851108005110309154000520b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 474240719 1250 474239469 474239473
    0x30c0a050321120a0b130606090b0307020319030e0d020307020a05040b030a06291210200d0605030c0a031e03170702070807080c1806010c02030d08010302030607110a020108060303160302 82
    0x7410102000106c1c2882d03100804c030946449000d002c40e9070051003030400da843ca111100c0d1241e480c58000c91035842204200468588040080b000242e0035400003003819003203501341d0703c6405a5000480e520700448030040d501c41c0014404010320f092541c4126036200c0080d040e100c0b20107260716040b007929026802e07030700c1b042810866070b2078104000060f042501001c996421100c0c1c101c008171961044180d100c0c42c403240d41c80072001449111030384140e0140b82859402a100d1080915030303401803209202d0304e40a07000d04030501e0024505202a001900c0c1d2108119801c0e89203e043d9114401d800c40c1d0072021301042c07405003954940702e074480e584151216401082030742e040c0002241454502d41c0301201e15804005080700c1955410b141060300d100c0803419a019a4500c001290022000003019406000e00034418060f01d900040350340c180c4c8d000342d040300c2407501d030070714119001e9075080100d192a40141e12581d00642c81600c003903400086c000c0032242041c0041080d01412100c55038200d01607 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 474241969 1250 474240719 474240731
    0x120c03060115030605040519110417060603070b040503120715050c0d1a030c010e1c080d0b010804030c02060c07050a0909051510030321050411030c0a050321120a 71
    0x1003a418010f13a4064070003510188280d04100b44400c480007280b010601c0b03c3ca484a08006600c2104030584005002c020b100c0c280e0031500c561800c0d02d441043d02c00a009015145010440c0f0030000102e41c2100c40c0034004213071200180c44881400d400404003284c2501d082090b11003c04000c0c01001c0c0940d0b405408607a8a4075185c041d0720440300203000c907450310901c801308120309031f4000c070756000003100030308212461401c00c2d0300060741c036020340e02e4038400d0041082e180d03800d1080000280402c0c0e0350810080102c0c1070140019544c200003284c0080016805841030b000604000d03001d45400c1417054100c8043c0ea41380e000103043c0075126007240d0501c55079104800c040c401c0801c1071ba070503c40f0204100318603082c04080024203599a0001034244142c60442080c1c41c01c0751044030641c1291203204000c181800d150101c840b2241c2e00200344640710f4620b12405600e08040d40200321080240100040b0081c00c11106291200c03c0300406d04940520500040e07200789041c8038440c2d5036454000601d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 474243219 1250 474241969 474242009
    0x60f07050703090b0f0c010f0c0509040b030f010c111b03030a03020715050114031b0a050402030705041208091f09030605060109080709020d1401030803040602091c06060f0b18120c030601 82
    0x2188c1c40c0300d0001010b58240340360a41048c3d001811105121015035020070007801c04000b107842e18088114410b1107610b02490303403841681c000c1d40c0040d0a084042503840b61848902e03024407181c42c0e0001681d064204101d80703004640281e00814a0600c1044e08000259404c3d05060407108241d1041e81d011100400b044c040c5d240600002d60700d0054640c407011101c41c0c900100d92140050b0085901603680040480d14181c012000d40303008020848058011100525090b159600080e0026002e0708024142c8540185904509030a0312020341d1035030801851a00d0382005420090f2210f4140b0110110205080c4000c4c09158080c050640c0b01684e00c1c898000000e040f1484d41c2c01c802480039003a801800061814400c4030340140e002040541c95406040c00102c4900350100c2605c01002034900e81000c11040741c1040d41111010703140a0010307030707503040101c40c00d10900f5201001c1003400c070640b861a207000b203403c81d840d00700441107074002160390003c00d00d003850030380009501c42c40745900004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 474244469 1250 474243219 474243221
    0x2707020f01050c1201051003090503040b07051606081915030c1a07240b06030a09170903030405150c011416091208071103060c070b09060f07050703090b0f0c01 70
    0xa08003030080c3c242803501c3d4400162815030101070140034421502c885821400501c03c1c4c008902580d0007100b600c2e962540c80300210410f501400d002c840354000c0300014404146041c400364102d8520303481e41940b50791003011801c00a840e1039003050503995203215003c500d255008810000d14440d1035442201410b06414007a03c2c6040080450340c0041000841d0000b101c0c03d944000040c0ca101c1106d01000c1d1024890340544010441c3e6034004201200b000000c4004e60080c0910380e0140180820454851041000702e10450740801d80540c000c100c20000f900b0140501e44107182c00b09880d9003042c02c0070400d5800c0d515044400403c80c403c0c08140425000350000c8082110814281452090320700f1800140724003481c0c0d0060980c01c808104141404036903d0b4000d401c0380001c1c150ba8491134055a55203581d04144000d40e2032000401c0011a00c043c005000ca0040813140c20701d184e40e94130003808035415840310601310f0411040082c0003a80c1300c03580001d04200318003c0d1640303807103174449041c80d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 474245719 1250 474244469 474244471
    0x18090c0302120a0506030304030b0403021207060f0e011103010b0f0c1005100f0f090513021002071404060e130807050601081b010f0818011410030c0b040f052707020f0105 75
    0x2403403d8034200900c24966000401c5408403644204070002507178980c14164280326541c1d00d001c1100d4000a050002c00240d98441d0044020195040045020820302c0350b00b2140b07905a03024143c0700402c014010085040050120309402d040214905403108600c41d080101192807604040c0d00d07030040c0807952302010864000740000b00e079401c1c01d0616020075180790031454843c0b5440c0603074030750105a010203d00c00c07549011741c0140c111284030140040095a55589204008172207100b02d407d411030b0f2030103000d0380701184c00031040312295448a030500074000580b06c10441c0c59030020414000010018819680201040e5002e800a000c0402e450024130200c00300c1d250420052238408001140c01207285908407003800180c08145203000c00d4640181004545000304043c0801048040e045c40382c2d840007520b2041242d080303096680c802e001c0303040c01540103507021411011400d020f64140300d101110717501d60030031035400c0300e804505081c41e6043c2c09481000c0160841001c880042909005407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 474246969 1250 474245719 474245731
    0x114240c070e0c0904020703030e030703020f0c04060f0509130c030b0919020306040f0c091104080d05072a030b04060e062412010e0304120c0b030708040318090c030212 74
    0x240081d460040c2d412625442030031303401446554045601c02c1410310a9001d01c0000c2010022a0741d00c0ca56410065550380000d00241c01c10710032020140d81506090146504803550b1594150b0001e091100f00b10350510000d205211502950402d480030030180c1c8a10002580140415140340c14502166410080841c4a40c1003a1400007113107001600d000803540e41c0305801288a400c074005519008010a4555200303010039802d01030b003401e4031703d580c0d8000c100700c41610084079054900c54405a41a011307801c0041c00e6079012816a0105094070841184070604d100d110b511511b449075607203040503c003960140e5103240c0e600700d04d140301d94042041a0b000140318500f00c00500030324000031204040780500a00070400d50810082c004425003003440341500200503241c689403112200c100440303119100b9103c01603a041e00040c2c03040b10000316406070b8601da51340710191381c86407410340314445811141401c681d00b1441c00186c864251046105034402c03603030056501c41048419009110003e011 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 474248219 1250 474246969 474246989
    0x10c1506120c15080a0f0b041b0201060512030f0a0504150302071a060310020a0513030b160309050c0d021f080a061703160302150403180e06090114240c07 68
    0x60080c0a58101c0c24142e400031012170045204000040b0101c06010480c0402d50400d0030800e1011102d180392401c0d28622041d903000304469545c800030880c2c0241e10300b01c4044560400c20640d41c022982c5401088800c200d802e0091904d540e5203204441c0d0440c070b51100002a5003c510b2004000021610901007600302c4078100e81c6040c40c40c0042d890342c6083c80583c44055000035190388181c00741090312074226201d209080b80a42d281030640300303a0400c07644110007101c0003040b0346016010380301d4080d60036080341c000c106c05c5039504144003620a00040583e84040e5091440040341800b01d8040114120ba548095590a0407018901550507941140d103000c0003c1c560001c03c030400009030b601c5d02100300380c0e0b01505545414280d042910000c100c40e40c03440031504108c141a0048405403100c5d440002200600765540d8000c01780b60016602c0310342c844080c6004019140114545500c482d8008100304040904c5d010300c000040e0503450380d0400c90001150880076a101408070711b00414048407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 474249469 1250 474248219 474248249
    0x9070c1e060c05070c09020d1e050a0c02031809040c09020d0b030f0a08090607170c030c120901080f1801020427230c070209010b090a050301110702010c1506120c 71
    0x5145c1d035003080140144060154045424210300c6002e811820000509150b1070311081c03035148580f0041c00b801c841c084d010604207411130822341e200008440c10841d2901e4030407811a842820000d681d00050003d03226901c0651010400300000e200910b03050342080000100a008501414244a444207980005410641b4a140420101c2c02100d652260071200581e48501c81d290034918101d00340c0710f00714011004105032102c40000402003d03480c554a0440c0c1910f040c03481c85801e51320824400314001030204002c036423418201200a41c00c481700000341002c1e0417060800380e0072600654800c2c0e9074008880040358107031101c00c1d51400e12010204003400203106101c40704a0210701d0660f000e40c19401e02c400200c0481da11000d40c0c003a2a4001c01009007540e46140c40d01d203031b8000d10b54080c40340c00f03d004001170320b01d414425072940701c91000549082c480d41d9001503c42e01c007169002c4d038016094038801301598507140b0030324002e000403802e203c1942c481810004810781068214150b0001c60007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 474250719 1250 474249469 474249473
    0x20304051503060319050d021002040f05010f0c1509030e1207061409040609020d180308180102040e18061501080105100507050d0818070b030609070c1e060c0507 71
    0x40300715118a403450003596a8440d81d000c20301d0f01601850440c180c0246080410800901150080010010350b0803581c3c11145c0119050480c4290300c1071215000007205c080180c5d5020f466114170f5644141060100740e125500c0d811400f84e100358099580540d141e080004040d0408140f00d290801a107821114071071444542d82e649140d03008100c1840050101420702c50b8035003046075131840000d4000d12295544170485d2000e5000240c01300605820058030f03205009403001e042504907015600e950703003600c60040c003a050300703a003e428a03040d5400700030100c0d184007448161409005d088071030340448101c54000071304044016110440c0d4020006400196a1f44401d5607410340f1421910511519404901500d651058a10040c640d0148002c6170f007000c3e403c49181442840482040b00a507000c111115444105900519140c1c200600115440d82480a4841c1d80100c060030214228849910303040c801d5103401907110003244500220b00200002802661840310f82410724a08090180e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 474251969 1250 474250719 474250729
    0x61b090602012f0c030a170601020a02100f050f130806091603030806010306030b070315080c1302070c050909010e0d080c030a050403091a07110f2206091a0103050702030405 76
    0x442c80f018583c509400c0341c00000e10032001c4034a8014103130103da07554018650702514001a50004c0850042a00005220307540080390207403030550300808241d0303d084884001c0d1658402c01c00484100a814841c00361405003510040c007402c0c1044a9568003145071580452408100031302c0c0e0301e40d0b40c0150455041103000c0c20b0707011041c1c0c2d501d418000c81954401004800400255001078021818601480101901540040703450050410556801501c480e0311a0751103603034200c8650000030104c2c61030007200c0a5406030020380c0c81692800b1b80540d4680005000c918151696941650340d40b0200300c0b017581c10440d004904410341481038451030260300b4810640001000f500b0181e03103d40008003050701c03658040010380742204003007031584500031306800d550308081c0048482c1030413507811040301d190000728150141c0008018100080b41d580e04403030040600386801c1c3c0059103a540100d2400018001c2d8407130913144003450b02c03154070081c000400381c40d000352009095420800c4240510380759 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 474253219 1250 474251969 474252011
    0xb100302060a081b0301030f1104231e01080d0801080604110f0d171c200a030b060f07051911011d150304151a090a0207061b09060201 59
    0x181c0c200038203280d071502c0e20040301d40c4e030001c8a02c806101c00800401000141603c0c082d0150041501124882106082c00300b1140902d94a0818200d92000140115180c00c03c3c40d9101c8504c4000c1a490700802400d02d032400c80a81007051950405803101c03590396405006140100b08840c010890350516444060030b440c0b80c050010301a074800100024a51100300100b04111340c0714807400c5030f0442c5444080307500d410071500e0500e0700c03040c9044c0383c000d0400d6001d14011a40006600032500c40d10700c98451a660014039880145074071180000465510305002d0043e40207032810a9994414610b1305030b050604844410740c1e4852034180e130502064441c60003880c44507017170070940d50000502102c0812500c10090095200650713604d056201354805010310b000310f1081c400400d8440907640c411050ba0221542c0c034034002c071030388640c00141c60b002d1842a04005108d07030051802820351250402d0340c4141000b0f245064540c0403152803103522034000c0c1d005141c107100801c00d65080d12034803464003003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 474254469 1250 474253219 474253237
    0x915030605090c04182d0218121507020f0106060201020301050f032109040e011b030b090f130309051f110a0b0406020f2a0c0f1008070201061503090b10030206 70
    0x41d07140c40714021001041d15070011b114070441441c0000382010744860181d0721241582c4002c225900c0341d90300746e0501044800313941c0304007809040008243d0a81c02c00d00c0000400c4001184035020403824811028494113015001584c00960340390304050510030304254485070380d030003a44402c030b55030b000442d824000041c180000260503998144440058054404100701d0922075182c20100450b005040c078001c00d1840543e2402c0c054100300a0400254184c201c0e80c103650354441c54001181340c005100404441e61003070912440941d15075010030710f01c0280d0461140040c500381010070b206500010200c0030740da841001884004e002d5038441000c80005480109007a40108104107007401c0b400c103a51143c11881010303012003a00502a03202052408044202809882400401428000d8203503030b10140140c650034841000343e070304846c1c5000041c100e81c2195690300000c101400c1e000030b43c1c50744031140d6601281e52411400e013000000d5004d81038204542c1502420001a04e685050301e1040d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 474255719 1250 474254469 474254471
    0x507030f0f020c04060909060e0606030a1506091e1a030d03090507030204020a0504090b0418080d0e03030c040303030605060a140d090c3302030313030915030605090c0418 75
    0x2404070390099291041403c64903078000d0500402254402e03070b42d030000e00d08600940c01444034103050f400890300c50f00c1c240c418680540019031110b0100340c030080e403040308856146001a05640e280c00144c00c5905400c68900d03200e40745600444d02000303501480c43d98200c0c40440c04440000400000c0c0d4507050006070000349a00c03800000248402480540002c6402402c01e41d40c238084030100405542c40b5002e541c1071541b4010f030010007420103100e00a0f504042d1a403040c0e800105841d034403040d4002d2010020301c20f844090040d01041c2c20b101440c040e10005240580b942c0c01d40c940134080c0c4555820441c0030310300500c2411110350344030490902e01c0c402c00c0d0800c1d0345c40c624002c903840034100e00c0a000e0021000108005000e1030765000b620008000d80ca500a5507051a480d0303207134240300d0341c4100d0005a00902c00304da00b1280316080014031034428101040389c9580d50908a0100015542d030701d010039584c550411040c00e2599100d5803054825a607245010708103100d003000c509060014507991 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 474256969 1250 474255719 474255737
    0x1201290402040314010c0909050f130f06060b031e090a030f0512090d0305070219021c0213150e0c0f0a0905121b041119020a0b01120506070507030f 65
    0x140d2240e50449018580201c80c180d046401424100e000e8200c800900b00010308845e00002c030f481051082c80d00500c00a6a007213120b440d99840060590003061095444c01e548400d51000600540f1031030307004254031803595407240750118015040e8110443e5412181380303644100440140c0204490005642c513040c40960030412020888690203014148080f282c070a034103221908100299010010f400da40e170920050b0f441e14412a15284166140e00f0040100e45001c1d0051504c0b4003031060203180405004a100d405070002071140c2e41101003a02180d07a178000d400e030201803098180000d0300915840c00c051781030880b10b4109520605d03010303200f03980c004280344c0c24061050f09514000c03d0010800c2e2400c070000200d2544600c4a4511444119458502c0500e0703410305024004d001000d4090090400303a8400f00c0e0400c0d4131601c90628218025040d0700b00c0000c0e82031101c50f02030000791304007056036107a51520750b251081c05001c0c0c0e01070200c1400f40e0800640c2c07090703030000d00002614003101740c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 474258219 1250 474256969 474257051
    0x603020a17150c13270e030712030e0a0623040201020a08030411090f070909050106090303080606070f0b040303060504140105010e030f0708010b130209061e04050d060b1201 76
    0x7007402542c0303c4c1c0c1900c040451000170300c1446401000d034040c031444038070350808020003101802caa01d5018504117680040c447c090105109141803402c4050034140412840b80b49020103040031402d03481214a82c1d80c5205526032402401000c403100052403041e01001c1c149500042c0d903e204c0c80c82c004010b00c1c0700000040c03c01c0510303840150440002380c6030100034104a01103c0d00700000311500350016944d058000368518840c00b600c0d0491740c0c182c0704d01018038215101201c1040c0c009110075001b0a08000c0e980005502d0764114061750300a03004602076041518005003900c02c10303480144a2030600c4d2501001140030280e0703504449090a04040701400c203400710707041034118800c1c00708502681000049640064005c4840c00408072035110f5000d07101c900002c01ca0040c2108140c000c0c80070b0119004400c034606141505591a28602d41440d0741c0c0e2001484100d600d01044403003c2c0c80311000302641c01e11205010309084604001d20101e000704c1c00c98440c5502c0680c94080d010410442059 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 474259469 1250 474258219 474258241
    0x1e03020117340305070804120c05030f0f0712081b0a0c15050907050105280c12020a0b01140906040f0e0708070e160207060818100603020a1715 63
    0x151002d46400039014407a50a0004056401918901c1e0007003400c010009006a120b00c490754410780d0b204413175151349410700c40200c4003e404c0e02d9040f586c0340b01c100118001c410000014003e085074055003140c0da410b86181c1500c81c07960614002061210220034400003201c1c001108c603140202e80149501e03018100812582c00b9041140600040c2c00e0180400d1030070101d4210a104092400858a00941e62001110300d0311903142030480b40d04440c2403218102c5440364a01c1076204003840d101c2e049841c0c548954010082d40076085016900c0408207804100003064564010003103091189000540c05000c02c640050041c0001c0c8031f00c6c0d90349180c4140c59020351004c01200c5181044540b82600c0341c500958881e100d000f5480034001603400651141419404c07900c082c1425070261242c2440d015003a83d00041c00750000c1d40a0ba584001c3c003603c4e0404001c0c0c40843c024080300455aa0300d50300600042d00c0482d04201001220881111007250000032080082c1c051040040c00a5490b600440c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 474260719 1250 474259469 474259501
    0x12010603090213021303060b1c08030a11030702010903170411010e01212906070b0606040e07031e15060503060d0204020c0f06060402041d0a0e0609071e03020117 71
    0x790286101085d207070b102000341d00200095a00c80c1c0c40410070341c807890041280300d108a20820041491302c00c04403002510740c101854000400000100b206181762200d65002c0c2c2040b00c0110050b903450b452002410740c00480d98000007841071b408c001e42e00305521200006006410010b05000070326030300c1c10440c0d02ca05e2218011840075402258400005001c02010b0081002d002980e0100c0c015111a0118a00058418444000d00721480c0c4111aa074211060303e0082000c0e500178002d11001072082d01020106e403054507240e81c00102c00791414940002c00e45254500301c002032030400c104074000c03c2000010140c90083c2441030312aa5050002240c6010b0560020f402078004900a9a4668005000e442c8921080113984556980f40140802c038015807003500343d25030603412141d01c81c640592901c1c0d0040d80201d0046002d951160b01c0324178100090f10554984c1d8170600d0700300030070a400e089402c00b02070f4450300b01c000540b07590002480c1c121240b41c600030b0610101e000c6030600c2400c1c0408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 474261969 1250 474260719 474260749
    0x106050411161b0f030213140417090d0f0b0f1b1b030d020304021e10030e0a0c060f0212040e07030b012601141008040305180d11030d05120106030902 66
    0x10000c41e41e1548561075504d0520b120490180780100070b401002045030046d0601034244100c140a65610368640a080482c3d1011070700c51100208030141c506d0b01c0740c03100c2040060041610004d5a030f45482c14070188100241103211100d14903051001d2400100c40300100c1c407a03000ca249889252259000e5034070340541c183d200d00c1d880001a1207450100301e0300510301c0756008035003864821013040c0c0050350017540190000d40c001d1900b942c100e280c41c041c0d03200c10010002074041707600c444100d81d00e0000640f55500140042989850724091440e03040003420302756808850300504140c03414030314070400d4034090144010f0507100e50008e0041d1344110f94640407010282d904505090007201260803486c001c5c00f41c03028404000b14100c40320700f80181d800403a80b043d55212151039882c6e13103040ba402e4000c5440303090302000c0f0642c05038041d90380c003040180e080c2c02114444496100c8904152070705400c02c5d1400180b040a10100e18140307440c4104504603156400c0101c2c1c40e6400d80b0000328446410b13140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 474263219 1250 474261969 474262013
    0xa0f0b01080303061807090e01180e1f1e05090609010b010509090411030f0a080d0f0c020a020d02040f1d100501030203060f060301061809020a06050313111203040b0a02010605041116 80
    0x74030b03021031050300900300c000304104102c00e0360399000d81ca4813200c42c1054200e80c010390380e241050413330031540070020921a40c81e1008000b03415500d49801c2c0e82c8155900c2026510503014409004400e100b0049112403d00b405450b042000c00851000100140b0107050b00c28100c14140c010b480900c0040a00c003400804d80c0d2602c0d0940c6484419600040c01e00340c1c6251608149020100c6903105940e00800d80380c000f015040ca182d800c110811000030310481c1c1144c0c0350001d0064111150165420001000c8140381080d140b0910803450900700f1450100040e040200420150701c010502ca0b40188400e6a00b43d4155101c80c0820f02400456100b080380f006828081000d15006a0083c1c4406100f1251070a00556441d41291640070940e0107500300300c0303141d504400082c00347c010030501c1a03018007001000282e00005a085821541c40603000358000602c10a14a40c203124241c082d00c000c070b4042160281541245543d0300521507a200f411040582c54010710140000c40c0f101001c44000c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 474264469 1250 474263219 474263221
    0xb041e09050712081b070b0f16060e0a1118040209070c1b0302100c050c100e0604030602040e240103020d1803120c080c0a200a0f0b01080303061807090e 67
    0x43d10020f45c0c0e1080005462060b081041140601004a0403204031501c185900d400c120081840900c82e5019050880d00004000400b000003401c9014154500304c0900151504403414203054000034031941c1b040e4429020258010b0034881c0008503540c10540550b02d50000345d5072520103940d80002c645c80900101110100b418002c00c0d44039901e801c0d688240d070748136810510369000703507000c0c5126017005003942c0200460802c9418a0080c2e481c4071070041c64101d00009408010412640c0190400e860194002030f0a0020003000c1010503040200615601d410441856a4825030441c140040c3d041680005d0300b01d0308180c1c1034101034001c0c0100d810801c0103228900d00509001101461b0400f81030401c5180c030501400384010a108452a44a117860614012f40c11159940c2c400c1085400e62200b002c0080001c0b0300f0054113032041c4c41401c1d003079525103050409003603505c0d050b400162168020810401d803a1074002c4010036003900324408242c036440d0b00310305032220b0300ea942100c0d0307403030340a08 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 474265719 1250 474264469 474264473
    0x6020c0a020114031603050705070206040801060f050d0317100e160305090106051807020106080610140f0d03080405120d0f050a110715021603050901030b041e09050712 74
    0x104000c54035901c01d80341c12070100c4038030034401030500044459020312843c0c0c100c00c1d0340040c002e0704102c0d80031409241c458540310240c1d00086a64011350400d0407d69034800040c030501c4030300b442900103018211240d1546594030340c0c00400f410f02c000d08ad208504005004583d5150981c0030060180c81c40100d040440d240021034500c00854000503440003a08250104215031010b210328002e49002420385000000c9a4512100c5a00c01401c0f1000310f6680e0900013030800000e2000c54002d0446240003007c1030310f400c0500580a041e50340840c42208803815032610b035038510307211840700c42d03242c2002c0f1344541c6d0f0380c18003d0a1000c2242221000b0343e00094842010659034000c108005d9001000c1019840b250500002c4a01c0300d2031544da414170800032107002c2140350320000710b5400840e0025260072a078034020750f150740090004a001c00d4010401812039a090301030640785020580c3d00700304285001400b44d03401c0c14004000004a965000102c0611400b4088440640700820171070708410118 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 474266969 1250 474265719 474265723
    0x1201020702030c01031802300a03020c03010c1b03021002040807051f0e0904110a030804051e09130212030310080f010c0519031404050d020f0c13150306020c 69
    0x3802280319000d003c030710070fa071580640f00b2040b04d130680d4103602d0b507aa0219420302024180f100f42111401d585c0e000c00c40c20442101d9848002417000101506c4654140d1901038030b04224080c0040c4684d04010f44800e009900204404044041020111031401c03c2e09043c0e00b4501440e102c9221980000f5001c02d40c50400101070007145c00503500510780f4803c00c44101483c04030110280001410300046181500d04a1251034011b40078811107140c101c18540015071350101e45d40110b500007000b0400300700c0c1c0c2c034220f003101f100314141d695200744400901c00064100b1200622401040040c42608025074944034012042e00c0b0811080f00e60300c5c103001d10f611210218500c00d0f082144141c6020880c640c0040c094090600c51545800342040c080006c83c172051149010411300300359a5840700104414004c0c0000c0c01240150b01500003c1d803065002828054000c1d081040c540c01418089156207406200b00780e1180903070400905100020381c40750350781f9000d61002d09498000300c2e00e50b00380200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 474268219 1250 474266969 474266977
    0xc020c01021006080d08060613060f0e0607030c02060f1e0c070f080c04021b061302011b050709020a020319050409060e06060306130618050115140406120b120102 71
    0x800d07000c40d951456100741d124180c51260040e015560403145040d400c4030300442000d6042800202010305200309602e0709801a041540048001348002582e508501c0d000000040c0040081d100c0c14640a1103440107807a41100442c0240282d0000a2a08400003d0410b451040c0c01500c1202403035289800b91001503049072680d201140109480002c5d0180b0781038101c1c00320380580010700155444001040025084003282103541d024100b40d00d550340708188045403144011141c4070f50101690b00004012180c0c0442515000740340810820120300c0000d800802c54007010030240e5140400f00c0d040b4118050110a4031920000880e5010480c1d007000140040c2d591071041041000e60f03405101d610440241d0310319422800c10004900300c3d04020f0a000320340760b80c20303201103000c030b99030304c03000c2c2d81d5000b11200d885006070349400620600e201c000592000d0105032924050840501171900a107100390301c50074041c0320400c0c50916007034903140c100c00d03041d40c00148842070140c00d0010190203544 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 474269469 1250 474268219 474268243
    0x424181a100f120201120603061d030901050d0209040b1c150506090112060b031204090605270414100c03050f09070b0c0c0d0c0812091804030507060c02 67
    0x10032080000d0360803085071a644102c889505001602619103030b1100441c1c0c1400e9402d904016070072000d540f011100c1c1c0580030080d40302da4000100e0112000c46103e003000342c2d072012110b6400802c500801a80d200c0c5c01d80b40f00c1420041c005940390181c40005008240350704045c0d800641031b40480e14180b25182c44020403e0255034400e003010f0162444904a91084400642c0070710b02e680140003e2860126000c40300c4c0c032441001a2604030b98000902d45920a1010b55900070002414820b5002c42d00a40d8020075050340c6080d90b19004642681c0300803054404114840c42000004040c00a80040c41040c0b4001200380d0b4804014018030001610b14081c121012a0411001c5029000003a81e40c510401250020b410050705180c1e100285502c50441c0f011079100320140a182991002e0103411407511580c0b00d03440380c625140d442820803036200300c51a031041083c802035069868034255150030710403008140c000c0c2c0d5600c2c50706495501400e50041d0809140c1003c0c10200e540000d0344e05110f003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 474270719 1250 474269469 474269513
    0x30c15050717211e0403020f1c02161428060507060b030f060117030d1d0c060307210e01051603050108160b0a0905150a03060b03042418 60
    0x1c000c00951040c51000703607000c15065660400101c1c2a860240310182c01a21910690f000b12500d006410315100004041030110527940300e082920540410440000c1001c040030003505a107007140b01c030681826802803d00860403599200145c29030f4a8480e040c6031400603004d90800d884c0ea07001056a001964122121454400340441c1ea180c00513040406181c20300060201d03a0805080706100c2003030031203106452106102d00040c2490764000e44075a041d0b06012541783c8520203020620345115440103901500d820814404000c3d17104a60f00781c2c0485541000c01001d00607000280144250391005d207440d4030300b10601030540303805410300840d455075a03003c0c49503903207076205151160203500001c80020351410003005501410070151840c003d940c102901c16503528000714078181c0300c00c0d4250040c01d50000b44140c04136090b1240501608484800034118600707070ba2900c03031200e800c551a1035a02c81c4154121030003496504040c1e090340c01c0f01c94410515586103001440d118840324502d25070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 474271969 1250 474270719 474270757
    0x1030c0e011a0a111011030412050307091512050703050a0e011a0111010902060a1107080c18090717030702030c120a0b15041a1306030c15050717 64
    0x1240d80403569071010008801824600680c065094031901484e885071903070b50040c400c4441c056540c921554401e0002d44451a03524a000e04d402a26040d0194203007040c404103100340000759910501c0002925015800803403090801300c010391300c14164401d04546541820200010182d05070800c0b8090b4000b40d030b00780301040041c205a801d0740c429100307401000031180005411903100b00e200000260340c040001a00f014940c010900f81e6000d19241d5022a02200110001c0031040044d400104200400381c0b1074003001c440000c078110421101c1010120102001c9550209c0c14452603001b8041c2c0003c402070504001121622900043c005901c00c0c016042d24054500b44865140d154841240191201e24035079a9502100c4601405070324101144540780d9025455a10503103070041d5031200301c404040851030400242020340550840303500e0504508100007139007104001c05480f0340ca80000f10798104148100c0d06ca014003280a404400c0c060140040b40003d00b008081d03d0000d00607220113 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 474273219 1250 474271969 474271979
    0xa0201091e05391c03030b10020105090c040905100510140301050c030109050702120c1507020a0b07120e16060e1233090601060206161409011701030c0e01 68
    0x1403d055420306500003201c40881010711011000d82008201000303100b00b25004a444400c44840c80940c0d048022a0313a0b08a80c1e54286840450005055074502c000d102c0c0c0c0c81c220190586491000740071a00868680014400300502841130032291415190108101d1400310728060711038201303120355404c030550501d00355503038241070040d544190040d012031fa21b10391800d460300c0c0c020b1000a01d0642140103165400c00c10744141402080d21406010041024203c45200f0603480c01c009807242065600814491001520110700240c1c401424100081c107070410000103030140502c6c000340071a0b40609484641d480b01c1c160040002c0e20500ea450399088482c00c4184022608204105050765000440414810040d840c4880280440cac18240c200c0e1032401401d414900c0c410ba0302ca80702ca40201c801404103a504104d010344c003800301c1d060710341d41c0403001030058400c542020b602c480241001030440e446074003071503c07002e003030358101c500e95155130f5281400004034000e80a1014007081035800012 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 474274469 1250 474273219 474273253
    0x10e04140609010f060c0f08040317040e130b070c140706020102030f0c04120602091305040503030702120f09011d060712030524040b0f03030408070509130b010b0a0201091e05 77
    0x2c00c1c5d03204d9840c0c1288004580d11380503202c00903038404503030081e410007011000825030600601c14084c0e14042c60b444500f85408045440d03002001906c00ac600883d5aa010031050a04d41c1c1c1c0009581c1407001500c4420300340b42451282070594600d00384190741c000100c0544c15401188a81c5180c1008815500c0d58850705400d44120300c100414080c0100410000c0381081d401081e800c0c400801a0600000c02c190000c2030303c504940c1543c40c1c1e000401088411601400426080044060030030b02e45001c5001401090050f824002e04010411601540d041d031081c09004c207451004040c9a210f47c1503182c2039184001103040788001900b0200808c2200c075000040c0c11200d0311090110100c0740e00c3d0410302c001081400c0303004c9e52050b03052581880c1c0761010700003880500440030280060030b081c9014052215000303000c0da000c503240711000b04003092040121a0540303042100103a55101031391003ca015006081016080c1c4c5110241045820380140d140b501d1903102c0c0041d00e0303001030040b150300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 474275719 1250 474274469 474274499
    0x10b120112050d120b0910030203010b19170c150309070b07030801030305090f19050f0111060606030402270106200d05030910110304140f0a02040b010e0414060901 72
    0x50541e03010a80d079043e128043c81107000400e0702c801000503c901c4240000720008019100c419104c000c100c800e20540c2001e005603d5024000e40d000c0c1c1307c50b008810103140c020800d00c0341c100c1d091000c40600c03100c10020700c941c690b5440c0c0207000c2d41c113407084a40d0310329090b8800c2ea9048500c1c4244040000c1241024042e9014541c064030f50448a03880c40e01d05907407a030310400d03401c0c0c0d1103d1034683c0c0d070001d607681000b104d00705800943c01801e01410308050200c803007242907080d41070000450040d000c08100081090703000100b03172102c47d2280c807107101003000715240741886902a800c84038445c54440b0003611090481c0c1e400c0d900c901d9201c4008030203951200040800c2c08040c0c00c0100f4050040f401007008581100c0d910040320301d00680240480200ca04815690415440c0003040c4414031060960350002c850380c03480a0841290940b10071642c4040345000207003d15151500d0910b01e0f07028104010700c0c404050014440121500316540403e607040310901d204004490001c11429044a03082c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 474276969 1250 474275719 474275723
    0xf070f020c060702150d0e01050a06030c05041a06030a0c0e0904260f04030305040e0a020f0d0b0a1814070f02150402040f0c0503010810110406080411030303010b120112 74
    0x26210100400d002d2140c258000c40e0240d03041300e586401e60105214060041020400c0008001681d4628000260079110301504000040303040600a001050308c0c0e03915082250f008540c00142140d04280160400104209035a84010044200004440305420150f4241850b17610300e90b004402c034040040040050700e000d003681140c4c80d070304121b0f03807120030b0000b00080c0b032035004606020340034488184551068004400040002c0740c200b003141d0000449681001d03660f50154240041020f503034040340100e10092034880d858a11690b4292a02985c80d0090510f01c0003103a0700844030b10442018103d012113500b401c1e001d82e00041d50443c8a8010030180c00010381c09000004140e00001c00102d00c064400e0fa489030f640c900c00343c6aa10288a44064149a900c40d15200d40c540000281050f40780c13494841600d0820b071280c040c800440040b5410380d1003600f02100152070300d0030800244020740032000d802d40320000002c2003c00034680501154a02c0c028103907c0d0f60f0321105050340d80e086010340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 474278219 1250 474276969 474276973
    0xa0c0e160504270c0203130e0105010816050408030a0806100314070e011115090f070819060b0d1506050f060a0c1b12170a120c020307020901030b0f070f02 68
    0x52000107030040442c106004048061181030030ba0300d90b0300007141d040161440240e400007e54405812031110280000e05507880700f08203541c5468001f801c20240140f40e800c0d000041c90071031450600a50586001d800c036941103940b51000075401030174041e0191541485803ca408075403407403520a0003843c0c01050500c0310b10415459a00040c0e411092403580c25045c01b01c81c03410340c0450482009030581c1c41204445440c101d041c070340703e01e5040c0b44100d03001c2c480c150401c101c1805060300c00140e032000c091407000700b61b0701d0140c6400d040c002008192222540030507400340d40018412440020040301c40718040c00c0003078a40c1e55007080010701c0c5040d1100d41000092021546290244804070141c50043d503180c0c05a601c3d984240320259240d42280c0030480c01a05c9102c01e201d82414001940040d03800c800e07150030b9503040080c022400003804880e0707481e103d00c4000f049500c00c1c4140c1e0710644c1d014114031800e503164500790291450807034100c070221103d80c00280300300b4070401c170182603c062600 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 474279469 1250 474278219 474278227
    0x13140910050405060102150a090c1d2809051605190b03180d0c0605070507031d03030c0706020c0f040603081b0307120f03151503050a0e0a0c0e1605 65
    0x2081c080900001003200d41940510264643c0c1c000c49150420f11070900010000f8201689d0314042e9458100c42e084003c9801d4a80da99100c05841c2d420100c0d046001c05202040d200109002200d039a402100d15020890a00c0c9a00081207030007d411961a160620003208268403030301030003c14000001000101b0060090400010111f0f03001560040f4000d01d0703042005c0d442c90900b84c600715620f00100002103030740303055030b043c41014407405400016603d00300c2d02d040c0f01500d005015803010703901c41c440c001c00e03c015a41a40c0d420001c6840d04900501901d40c890396445002e501c0320140740c2030a000f8490354451901c0352515100c2c51040c0c941c030001d0942840301c200c0000c2c151000e90f01d01d40750584010019600070031400c0d80c038100741410a0740c400c00703031740301c000d42c000c084d5800c840090f94038003040d038020300841c0f09810321021018200d15002819503038000000018101d40004115113020312809003082c010b004900d4010394a100030380b100b15484001c51600081042e29070000005c50502c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 474280575 1106 474279469 474279479
    0x807030203040b0c1b0d0c0308010801060b03130c05060d021809010e1f030f0507081c020712020f13150602240702070b13140910 57
    0x49419400c0d4186030303071560400c0b44060a02c8006420200300e081701684e258100054000d81c20003222038a041c84140905a40740c40c5078290700007000e04c070011901034414021641203441c0114143d1543e40c40d02e45481041904940444d42100108030014807552030802800c819004200c0059464074824810042d189146401c1030080a443d00100b0040c11a100d46550094801d00240c5821401c0303a90003080104c5500024400c04d180620740c428400000368900985005408030340000b80070004d0482080225081000141d016071818040e412119a1140110748043c1680102480f0340d00040c802403070b86102d41200da80d69000c2c003094200108030307000051035240058200c0284000c00301540c0c070f202407566441000c01c880408c00c031510801c5554000c00d448501c9503280d208140070032039414550300c0790400b0702c0001a261f0b43c191626405541c00781c0486011109914941 = true := by decide +kernel

theorem cover : BRFrame.Cov 474100719 474280575 := by
  have h0 := BRFrame.cov_init 474100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 474100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 474100719 ≤ n) (h2 : n < 474280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
