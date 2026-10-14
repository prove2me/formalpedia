-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:41:11.044216+00:00
-- url     : https://prove2.me/submissions/d1269061-f39f-479f-9244-509013e74784

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 380215827 ≤ n < 380395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 380217077 1250 380215827 380215873
    0x12270203012426012a0e0108060d02040b0a060905090f010509040803061f090f05090c090d1b030305030f0717040228080109020418080d2016030e030f 66
    0x8540785040210024000c00340285142d030f54500e00d84c1e502e0014986041031001172025248418850404884055640e00401440e405001150780a01f51651400828000c10b42c00e50602d810143c0b40c0e00110b5515044000c0707404940c0c060314241c00555a21a08000011080c040c0d1544802c4644c00700300403403940300103180c00600c0106202d4401c2d07840402c1d0a0100c050b01046c1e40812460701007001074100007030003440141416900e0182514181407005518458005e1051041045041c0d04040c001c80980c0c162665a11510445185441e800c001d00a600100c500340303216054000010580c0d0b1180d12040304401d00030160501c01d407500d9003042104110034030030310005030038141d8501c1081d00c0c1002082c01401d80701d00000310041c090047c0f2064a001d00c00014200c9415280807001424020071140d802e0640000007a0309043c07001003c2d041d01000c444049008404103041c1c0d100544070101f400c0382c500c00d456410310002d5560034542c035290301141c1c0d0700e1643c0042c0a10150403058040b508 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 380218327 1250 380217077 380217119
    0xb22031a0a0b0d050c011101020c0616030e06010621110a0f051e0301180e0d0c052d0c0301051b07021f02060f13020a0501122702030124 60
    0x403400c01e0881011404101d58002c041e50145e000c52450401c42d60003400e280c2142d00140c0081d46855404034040c0d6071078201421400010641c0c0821030136161080c0d005007040c4809800381c13800c5580d0307003c00401240701d0040e41443c111101d00d2511058026101c1e0105074000d0710b5803181040081c000a94000000c442c41101f0702104004031080f8201d80c05002c05554210840070ba1a03504048500340b00580c110f10405020346010000a9000000112035109000e103140c58183e144c110714090b0700382844861250020000c420b1349000f06030380c1500c091401414002294483c1c4005800c160030b90306c064800045000c1904d03048070148402400601026001a161549100085040900200fa404c0c014801a00400d0510400c0204032a07200c0d0000c4003544003d000305410380002d906800944903960612101d8043d0780141030040d0801c04485140030310155031581c1840e000113189060460492095107070480000d4a200340700c520110301c942c040070141c074950509031032401d51140014a0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 380219577 1250 380218327 380218331
    0x13030903020906121e152502011b030b03010b01170c0c120d1d15010611010b04050a0c0e01080f0109020715020c030406090e040201020d050f070c0b22031a0a 69
    0x2d41d140008100b0180385d1016500120b045141c0c040c21682400001c1c5000f41c52641d00a080c041e02c040e0500962801c96140510315041990484041c2d0042029004255031240e002000e2100300303406a11811000c0402d9000b80980c2c41c1e2840111056444045c08000001540d0040b480310410030b8045d01c01101d0030000c0313030078095081220050980050901c0000da6803a0803903144a51240c0100908401c2103a009080960b00304040a0070408140660303410010500d807485101c031025041401800030282c010080c0e400c1c142000d201401c0c414010401144c0045000d060340d500c00e1aa45115464030000007105074207048460029501c44241940e4286480e1108905000c26200421640210f0001143d58500c0d058000d09210030b10ba1040f00901100c200f0000580d8000ca9096001201ca02d0080ea80708522008500c40d40961807001e0441801180c01085510082e002481e02e0350104c03001c0d04180d8200c410b41c001d4400c141c00000e000303440049000440706043e05600b40c000c0740039140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 380220827 1250 380219577 380219599
    0xc03070e09040609031e020c040b0604051c0c0b040e060f0103090506010f09060b210a060f030309030506010e19020a09180507081b12041a07050301080613030903020906 74
    0x54412a050b90140c4141c0d84e500c0c003850030150800c1c071104070602d080e5900300500000000217920307024640b540714092511140c2c0e42c0d038160f51300d4003242c014100c002d203402840240c510081081192000d011115001950030205085030f00c04144c40c12641248040f40160343c2e0801400701094810140300c0c1819103c0e50407100286040c03125501800080c00e10007106403402415405032102a0704c02442c051f81006491204030b1001e171500c0c4004080300000c2d4485d1100640c0400410003680480d42c0070307000c05004006c06510683ca030302240e0140007144c0c035598846554100342541610349058050f803803003100003055803580150904d1103182c14005000c80d03840304030f01110103119101100042c3e40d28200300710542c2100c1c0058000d1403800100c070f481040041e1000c0c262040e80d250000100f1010001001c0110140c9002d0000f402024500b00e507042c0078034098600d800c03c0c0101003945c0200c40008091180c1060900d800700d07095622006400e1031502846581e0030003600481e0482d1305101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 380222077 1250 380220827 380220829
    0x1020f0d0c080c12031006091a0c0a0c0b09010921020d060209030132040b0a18050d0801080714060d0e010f0908090f0402091005090607050715080705070b0c03070e 72
    0x40d441d84044d111965039246408070f084095002c1c2900042c091040d034101c14810440604107456a0f0703046001c0c0c4c180e1720711044400a183c241c070900300030010b030300c40030020a54000711340c013030480340380b00780c81c0c0000064070f8500c10580e180d556100c10720f00380580d107450340261500400040c40c10380208001442d00c0780d0a0042420740e0b0100d080001c3c204040f103180d1014164040b03c0c101c1c00d00003011002141e043c66540c3c401c1e03003c40541410034040d114458800703421705184602c00c102c0c0d03001c0100ca404401c0b55070702500510b4240700d01080c902034181d00003001d042e5820171041c103100003444036107040314203c0c0c540d000b0141d074818142d5540d640c00080441111a10410000a020b840e4454440800400700071108140902c11801a801401604003d44940854211804081c101036842e9004503000c030b0054025010042d01a2244580c0040c001c0742800c04000d41e41120340e1410080d5035904800c1d110b501c42c0f0000182036254403000609500c900001454000b5407615010b600304502e50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 380223327 1250 380222077 380222083
    0x6031509131e0b07020d020d0f0908240106020a0302061f1706041101110a020d0512030c09100e030a24090b0a050106020c06190504030f060209010e01020f0d0c080c 72
    0x21030524100d0010082c84010322540d5200142d000c10b05200500400d949040000e4841030038803d800244045490a1351005020319251000740107684100d610700c9071903000d41805004c6150341081400e092100100d007541c808a60181230b41d41540040c801510303410442c81401d4600592404000c0d40802d0208004034003480001c445406400107040c14101070a06070000c042c0a50038038144a07005118139010b01011981d9a040c0c0c3d012250384041004904042d800d01031245940c0b00001d9000040184074100724028002017078042e201c4440045600710141c80008003017005503030550100c2c07601400100c5000341c904000c041c000c00303460f000825180a0040d00d0150404031103440114081090158261050b0350051060b440203154551070200860344a01c182004007000d8001102908900340c00b40c2c0c00c84000355882440c071941800c55040c460003c0d04160000d0b030000d0007e09680100d5840020b4000240700f4220103480c04444488040e990302d007a00c10100d803546000d01601450f45424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 380224577 1250 380223327 380223353
    0xb0c03070f050a14010b0d02040504060f11040315050106090e0901060e09010e010e0a170a0e190303030f0902060a052a010c0f050307050a0e0303090406080c0f0603150913 75
    0x1680100184190380c80c0c03a80045003151013600b203580c90f000d60f28660340e84a008070040301e41c05480000d40d503115070800901405546408601460034024500c0d20102d803440100100c9000f00b007401c40d802402d200c01815240203100f04400102d00c80c038140a0703407402800326a08000380100020b01144c3d50613061070564400c4130001d070141d540e480c00c2c0304da13403000b80039a0a4a4001d100031f40500e00086d038680e03520072542c0843c801444004540031414038003034540c0d4a9100c1000700200908251200c6005c075150340c50108600003400c10f0144182403031503002d8050340f5030b40101414101242194103c1e910340200c0b40000c295012055184d9500c44480300e0b0f1001c160000002156004501e03002400c1c14486510460402c8810010814000e6001040d030380c000e102c3d454154540c0703040741d00091643c092409002e5005290050000702d8800005404400f90301c10741380c411401035500d0400c1b0f028042111002d844808010b20f1201902e8400c0300190b0008008000300d65040090b00da11a5a003a0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 380225827 1250 380224577 380224583
    0x110c0109030e0f03060f16180b030a0f02070210080a090212010507091d0106140702041e0c020a030813060603050d0f03142401020102190302040f06050307090b0c03070f 74
    0x1c1c5500030b105080c40a800086900190028561824864800511984014800d0705090080c40036400d14521804410101001035a1910303030702c0351100303e600f40ca07500c2668100d5207549000b020a078403a01a000f40c48005400405203c1c0e108070035070060f03a6141d4000c1c1185240d6544911420040e581c04641d0b40306040301c08000200c6150503a000b4100305c85903000f0209409213a41504500e0a60b030f05c0140c1924007070300c0c10115040036600da00c40980600c03400250b0150401c03801c400d0100700d2104900651100c01028801d103101030034241d8444c8800d1a000d00050310754000220b14401002d0318501462003000d00107809952a00c41909200070350401c040020826086140103039410b0090882603040f241848482e42850080c02c91851511482c565a803420044c00c045180c0c001e5040c3d03405450203a108010403035114200038001e41c090b0040d0194164070070004203150b0310581c1074a01c80c002c50784070580c0030b07403c1c402413059a410070040c494451004010001c0081c40c2c9004210035544 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 380227077 1250 380225827 380225837
    0x6080609040311190506070804020d060908090d210e03030a0305180f0d090f15030c0311130e010902030408030f0a020c03040605041d040b1302010c020d080a020706050405030a06110c010903 83
    0x1440d2a000d81400b0011f0b0a45041100540500001d40e845901c14101c1541c46000090700b01260310b4050711a0041d01049030703104640c040b4070b0080c0408980700d99035420101407000d240d0000040c050360031428403040c5980550052000d540500d00a43c48035406c407403c5032811000d1045000d10f50716003100c0010f5a407654005c08840b202407900480904064410541c600c0e20303007030504607a403002c220500c100c0010507840d181405149400f9610000c24843c0011059a4410034480d24440c03441d81c42c855104045a0701d000000c8804040c42940e002d150301c27100d10b5255444292001104080141620362131a0f82042000111a0108010710080c42d003900c0340c94071145400f88154005228240c03044a4191380303c20040010001d0410715404501850700c2c0042a21600048034441034031030740290044c03d401c4180080c40400000351000c5600c5908654078135031102011030b924011445410b0301503028109690004080d0381203030703a8055401204c10708000786a4030361070035500a801c0030740c0420 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 380228327 1250 380227077 380227123
    0xf09030d0f20070312020301061b11090405011a01030509030414030f0318040623042c010204030212030a020c01050706020d0c0305191503060f0213080c090a050106080609040311 78
    0x5900100c50140140d00c5c1c01045040d9031604101520b48284244035840d01e402c03031036569040141c1c5d4030410103081c0f800f41070710303405103040c1c80e00701e00928504c800040c5107507192041a00c298441c0c007440b4030030101c82001d14201440e00d41e01074202501c0d401c0460707140c003999500d18000359041014144060848800c1203844900c5018030088441680002000d042e0340c02e202c1e1800075008280c171031000015900040c079040002d8180303084091454003144440c10003144161400415000340c01a64003c490a8288200502d0081d59910540c0001c6015070400c2415020560054020b400d40a00481c0d0161400c0c0307801040c10200d078a100c0000001c2581e41c0144114051160640170155602e07100c100700c204045090900910402e100003043c054440c8100300055003143c0649441010154005a03003c0c7c03540c80103074417480700c4440d00d030040c1d98610004c2c800600034000d07181202c10507212112a900d80c10284052035400030015000d20848104140c1078002c10048031403800c0580c4c0c6000104 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 380229577 1250 380228327 380228333
    0x90510092103202d010603060b04061413020a180e10050a08151509040803180307020d0f020d1707050f0304050307180e0102070c0e0f09030d0f2007 65
    0x50300c0c0c007108114003a084442100701c225400107800032072064200400d40300c41c654000c2c03840b00d80c4544c08569065400e210001003005000c1d0400c0c2c14203441200e0921000762600401682a003a00c4002a070005441c04802034200742d9034010503036918240781c6040c41e41511000700c1c0e1100b9896000d2291303a511202084281c00d4030441003400307440d049843d4600c5078607080d81d0740d60381c1520742c00c001a25044180820000c29003800d40042409014110101c1450030b0f05001105420480e12000c007031100601a002c0a603004c01200c080350341c0103245823464095500c80200096038040d0407600701c1401d004e4400495060500c442c0d1060200b14810f5482100b841c01608041c0f80c00c0c84200030358018042400544d4010a415090340c2540410368584441d44d000c4101404c0800510040f5501c00200d103000d010716240300409070780f00e10300b4058007501c60003070010ba080c4040b079007103905030000d2103c1c1540c16110342190352101c010400200310011001900d581c0e00a1064840118203400a401010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 380230827 1250 380229577 380229587
    0xe091f14010f080f01150e0409060c121e0f0f050907181808090109090c0203090109121104020d0209040f1b0f0212030403050d0207030905120d090510092103 69
    0x103641c00034900f103e01810180040350488106000d0107002409007500d1141d141e100b03101c2d024240800070010b11071f24400c0e081140080c0820f2078098000355000503000b103c41c0150090036030502241c4070141d280c1c3d40b150848002400c21b14280c0241507199020440e02030000d025203030017400e0310301c05081300515005104103031400341200e00c01d401c1c1c100301c242d842c20740c19590800b103c60b41040119a45010745001218003000c90703003000001902d0641e0081c2d031198004045c0590720340a807105500a0b4644d4a0020a0b0901c28801040f8000015412180d4181600a1720005009010141c02c06884200203004d8074807035a41d48200c141d61f60400e09d8040f031402070b40020300005080006004a81e400c00035150180902014409000007012504142c0708408a0b02c3c1c03040c520b281152201c01c285401030500d061889890701c10301035603060340e4814401103100c5d40540f00c143c44000c4900d150000303001000d0f407404200340610000c1d0a00103410241c00c02d01c9100d450300752520000ca400c2924010385 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 380232077 1250 380230827 380230847
    0xc0606030721060207110a090b2e0309110a03030201050402040b090f071d09010608160203190e060c01020a12050f130209040f020303040b0c0609030702010e091f1401 73
    0x80c00c82010180300030b10310030206031002c5950400b0004d83d039840e04d030a000403040901000c00c0c0c0c2104a030040010b001040e41d0202d4240d0104031011000c04002c0a56900410720030783c1c241d5441d00c0070240c4044814000d03071001180701d1252692030b200d0140180061084110f0368419005030351110200000c40c80c02c0d114220128104882a141904010701c4c2c800440030028480c00502c41c0381e0185000360200c00511480e07010b0028607000080d0b844100c02440700c48180c1d94800039500901c05100200e0010090341d0340020300342c94104448241ca0740c00c0310841200100c0130b0700000c0411488031001030030700041800030800d80300d050310b802d0003103908800c80d00010184440f51041d0010312000307a03018480300341002d4040b11204202c0d01d850801d041d016224000081d03052000140000e120140c6e0350181219880601c1500d0320756891442c20382d00e0703106500303000340021391008800e8003a240c0b1b4095150009044c00c400d513006a658000a54010441d802c0441503814420000246603404400c0711 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 380233327 1250 380232077 380232089
    0x909010204120206070f0602040308090102061006230d0c1e0201021804050901020904060e090d1d040e071809140307020d121202160b0610170a060305030c06060307 72
    0x61a00b8603002c5038030b507840c48018009105520015450040c00380c0001d03a10a00d40e00104119030320b81d0b0360302d413200150f4000040c190140c00303084001501c40007480340a00c100c0d01356440ba0902640b640041c105960840c000400a00e0030a203c00062440c10348205005c4040383d031911023081a40480d03580f00d12202c039141c4411a0b0040040c9030000300f2580030408012015600400c20f9100e08540501900800c2c030002d400902c0d00d02b001a0300c04103000301030301458a09044c1d40481880180c1202e0401c95002092003c1c225840d04200c0c43c1026809865031038061410b8902c502c0d02c5046030030814409800101d9455220483c40041c044074000c030002c4684032500071803a10b440da501251503940e400700060300d8134030964003000c02140542880c2811241c1400c0455a829201c08990800040858161046411003000800a0074841c6194a00d450680c541001a4500c403e4403200540c00400c846140754581c5c5002001580410107814503007036107400760103a450072005044c54003100b94444 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 380234577 1250 380233327 380233331
    0x30a0507091a2d1305010e03011a21070803040608100e13060b0d08040905060102030906070b1f090c080a0c050d0b150c0f061510030903090f14090901 66
    0x4840450400000c0f2500b416050581c100c0031042460116040d00c000c211030081900f001a800400c44001680707403080d21001d803680303020b1901000525080b41c04e6031030705105a040c001000e482629001c0e5502848240580321000b1904c1440d60345400c00065030b0110006510205050000d141c004002603480300c0c041c0c500e0b07000185030200ca00d01d462000f6000340107110307034112104180003854000007011000134064900110705440e00d034119178003900c5242062403600d000b0540302c1d8030220403907400400040c40c0038145002a141c0215441c000f0f4000e40644c0f500c101c19100051001c0c000d0b01c000e01180d180020042e2609401400c00040148481161407a00c40900511034102c010349801d503c400c40005070340c80c00f5101140c55449a08017004c840d59011908600d04000016a1225a00420145c0320a83c0b15116429894028801c0b001d0740003081c00800031056205c0d9128818007030180c5005c1d145140c0d681082801c4803007039003010401c0c9880304d0705024541080300301c00f0781040c0d0a00003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 380235827 1250 380234577 380234609
    0xe070e03011812030f050c07050106050402210a06050306040311010e070803041701060e0a0b030f01090c14030307060903080106021203040f0311070b18101b0b0a11030a050709 77
    0xb82c81c0c420301c0b0403400140100071601018034003901c0380d48845001910700b103080100341420040008103410195003200c2d03039070901078082232a00b020300030394000d40c0503040719811141e15810201402d110042c0107403c0c0726500c07000000c940da410002c6900850003611280008440112090b086d1016202d401c4550750041c2000c04c035040700041101e00b240caa11018942007039000200c070380540f1065002c90b9031102d546040c42020340c482d9100c01488030048048030f002c0c28695072100d00361076032440003500074401c044003041540c020000307088520f60000c00313a9150583c035aa4150480760503400507030000b070340640140300303154041041409100ca0b0b295200c0c1180303060740e070300714080e0080100203017000080b400a1280040030482180602004c5120a4807544039045904c101d0f40c550492030f104850701e400240d103aa000b1482980d290301d440070030640d0300e4066154800d0754400a002c1e10982c980d140c0d1100e00442480000d140148140714021806082204d00213144000d00e4101504120311a55 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 380237077 1250 380235827 380235851
    0xf180905010e0c0c1002390607080121150525020102070f020f1516060b0906061603050f0708030a0b030606010503040f170712091428030c0e070e0301 66
    0x1100800b03000b500c42c01503a14502c01c161f030315500d00640c0c0c4403406000b2000690300c2d160413000c000742490100070219105903940f208111581903080c0328908100b8a0503544000e040e2080060030405800760320004414414030510b9004c4a01c11680c10380301141c60408401001c0310302c1001a9550140c0c8002d50500109490302401c60720342c90802480b40c54001c41d10511911030103e00803500c000000d81e5a11100003020041c44a60080400c881c040c0c41e26050410b6071130700c404898007802e030140619007051003e0b02c445150f100a12400d40c2804418448040c00407042c1c001021850310400e40d00ba240c0c28074444150544402e45802440307504107504004080c1da000054a51042c0c10030803101d10106c141c1404001000b4240400d003070044009480d10500c1079292103444400b400343e445102040d81c0e04100c09110f03506490f07560307101d0b4040101070040c5825540c450001c0030300d82501c8484a540c0e5070b60041307044e01540a0302d88400e00c0410043d410307420201145d0700c11401e400078059203c20328 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 380238327 1250 380237077 380237083
    0xe010821212d070305010807241101060b04082107080a2c0f03150a1509020d0603051e0303011815030309150903050304060f180905010e0c0c 62
    0x140140068040d0000014281031401a12600d0400c01241c00c1d4882c16000750142c100040031a18032000c203003024000164620001821022031320320410200d0b114090707440180b0000f0769074100b00301304001f103200c1c0d00280d002031248200a000200c1d01070b41c1d0324540380d4400d0070700f00302b071010b04c03c1031601200f0510641d80350ba00f1500c4c1c581d4004400d55554441d02c1c0300b0b4850900c55400c940040e22000c1d103071001c454031a070300c0050b02501180d903480c2c46038445e02003540e00c00440d02100e10300341e00400811020701e0390340c03c80795641c0490086a603206444099400c00c0f6003010300403610312520b510040050150601000740301e0034074050200140f0152285281c2da03807206119100402d030125004072000d03d91580180480c03e0407040c0c80e403489a403400e00900d0340000d801441085100b5511242c2c1090149022400316548400913604043c901103082d41d0400c0001c2241c03050043c05e000c05290b84111400c03980c05004444800609941001000300e83d10340300030101c0005001c10801548040000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 380239577 1250 380238327 380238367
    0xa030c031a0f01050d0507030501090e2b0207030524060a1d040804030212070602012d0e15340c0b04110301141603020301031a0408040e010821 63
    0x940350440035002e03140040310300f417240d5100545401d2808060254155264000b14102d45101c0c400b48007000064030461b41f9592230b21700f91223851110f580150441c11444100d004000748600640d02d6070341d9a503d950341042c040b15242030f481e8003a0080c8000000a0350092500b0520590b03200c5116070030099401c40c000b000d61485c82050130040d0000e01084a03041c212000f95a024210384403110101402d16640c04850082e03c000d9400c05038441411b030942e400010340346000503e5503442000d0b00d15814000c2c00320217228502805814101402c0d1800038000718003d601048000c070000030060701a9510460045d4905050440c0024600003950710012240e50150042c10f0722003da250392801501031060310b403040f501135080014030b0f0342007000b032400c10b4410b41701c1c000720920500c0d40000480403131109000c0100008505121007a41310600c110542c1d00c18400c54640b03103400c1d01c60f240151510003d07440341c1803a9200c0002142030200d40407402082020410046d401c0c0000041c03500041500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 380240827 1250 380239577 380239579
    0xf061003080c070b040306020913020f0409020906040801020304050d020f0705010c031209020307090b01090e0405071208070b0a05070e040603120c050a0615050a140f090a09170a030c031a 82
    0x400d01030900b042c1403010b04010f1107015610781c0d46696a141c1040a50894100c5078842d00c5010180c2440030140d0003103c01084044c92440d1900b8140a0300c03c0094000c400740c0c039000007080c00f010400341d40900c011030041c1c2c010001006880210320001f4030304003510740e880300c45401c00c034030400841c4d8004160ba18a56450305103030480460a240c41d00044c10904d00c0654507101d00c0b00001440171140e070140c94141c5086e6074680d90151120552012407209890041250340640c00400400c40500c40c81094a48280800707840c100740358030b0306100c00400f81ca111581a40c0e4809200c28503801201080307101e8000d0700c060040c5461515491600e40d2803503818000d102c1425990b4080001c00c4c080250034950000b410410704000e4543d92003480601c2c0506030003407092103000b2030201c0030180380c0078110307000900e856040d558410500c184072001030031001107039440300510000595192500041b1120003044d5a440f100c90040050949407210950401e261614610328040c81c60609540b1080070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 380242077 1250 380240827 380240843
    0x2010209030c040c0e0a031506080703020a30200d0c05011d040e01060e1f05040c110105040f0b0c160209090703150203041101030209010f0831050f061003 68
    0x5002d100907203a030504081106c1e807051146401104100c075840000701904030400040001c0d54a500c407080d602e0f80d080c0030283d813004401508000c906421000b0444e5417101080c801c400b20011194080d80001c2044c080350322706c2d91462800360300844403081007002002101c10851208060322064940c520b540039940c1003012480030400070440f40c21542e031030120054030030015a011035015038000c1c42c05010701d5001842c8000844c3d440d200541d00c00700051090814170134400e180804020050006251410a000603100d040740700c85000e10440c1e121b41e018000d800ca181d2071030700d0190011040202181c4943d1414001d2400c072031484110b03407003020b5050380c0741e08840c0c90307000106207016000d510041c0b255001860340005000240c000d98052849001c4405d9445078000c01074060780294125180020b880d00c400f40132070b91140d001503401c4480300ca0f9600b0314501e00d515051001c104502800d040002c1400040d0820004001100034041050040c0c00300d4208482e800400702d20030320010f00010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 380243327 1250 380242077 380242091
    0x60708041a0709180603020418031d0d1401020d0b010516020904060905012f041505030403140a031401090212040b1008060114010818060a0c02070b07060203010f0602010209030c04 79
    0x280580b589101404034101c845440c0400806400045d0460b400120b001c0d504120341c80c008055840c2080100c45e50584a85411480d0b010b60440d5090380707500c82d0385d4400720100390080030071030000145e0381481001c800561f4441d050190101a9119800c515040140400043c9a0000078185010f016541261680483e07152420280b0240500d0307440a4070652070700000b10a03100401110943e003613150181c044410144045d8060075015511441c1000d88402c0c644d101c080c0e00c5031000b5a130261090074a096261020b01155034a6004080d45201080d034529246160002e02411180101321041044d490222010f0b010003000c1c4002d0002009412480c0110b4464008140240b0280040f803045424543cbe407458442c80c0c206a410040c0e020071621008210181e02010b0f04c032429010701001031400352525080c480040519180180450041401c04111119010010040c1c103000703c00c0541c49505161009800900c103611000c15a8410400c2c0c2d0079948000c50150061401203400042c0c1d0303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 380244577 1250 380243327 380243341
    0x7140406030606170d080c03040b1801060308090a0b04140415120c1d04020f0108070210060b2808150a1805040c0609030b061e06030c0408060708041a 66
    0x280465401c0100b00c030341803040114812045107501c3c149036844508440e42d000c004001500c103410140e81c10001c03840704100090101d8a1401d8090f006440140d450300b131194440748403402c40d40f40e90002c60794440002510092403521840e1317900030341455840c542c5828504180c544000b144101c0c0341e0302075500c0c0c0581d40114000c000d1030000070701c0c500503c41040b030107500e020454910240280c2010903642c22107000030303003c50605a4410b550280482c81b020186000655003080000e101c0011842051000741d15000540038500007800075007070070750319170003000500319a400d2058581d0b000c51085074503402c07015500090305904000070002003000d42415002007440e0a0841e0002000ba031441c070480b080100940c0c0c031940c070413801820116011611440c044507010b107140300140c003d002d03601c08119585054172a10785207000400c1411f40d0340006001041803904115604040b50001150800458500b4403034680d002541d49840c00d00303490256183c0c00e440c000701540ca00480000d40001d40c01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 380245827 1250 380244577 380244581
    0x90b12061801051509012102151e0306030c010c060b0a080105090618060a0507051902150c04050d06020c031b0d092403020c070e24030c060f070f0b0f180f071404 71
    0x251fa07000303040301060390103041410b4071640c4030910780d00442170241010b884502446007564058100100507142c0610810011602001c18600aa40641d91815403080e00d503510201d403401000d80710008581444c0280000342405402001d10f00c45001c2c401b2070030780c000c1d00030a00c41d511000e00b4031700003a5502c03900c004a035203000c1c500c0381072507580d0305000d44000390750000f8800b020086888003440030380d030350b415100c0e040d8040d900c1007036040354002180c000082c5458000c0d15441c205803040b04d00700350400c011031403800c0c114050030104d0340003503200c0c205044d4000d8000d000f500302503d81c40106603c3c20009084040d444074040b0400d580801c202c500c040062040c00000e00360030b003031040c09051219545c0c213444c98154940d12802c036203c0e03e05c071040c100880c070b03841c091400524060508428280311240c991085400721906005204180001400900014019241e443c64168986041c94013290301400441d04c0c03410507072003800c8405a10000080305000d4039070302c03621110200030803804500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 380247077 1250 380245827 380245889
    0x6010e090c0c07030803240303030622090f120503060d11240a0f0c15050606040b030903090a0602010b0d1502040b07060b0901061701090b1206180105150901 69
    0x403070740640e65001081c45400c5c0050f50241c201c0d020280d40d582c03101c07510083d44c1d8160040003601070300180000b0b82146020356048025000d0428044481c280c1d07103e2a400700e03141d07080203e4240d00c2e481e15a03c144288500d01c540b18070024100140b450901e04c0001d540c42414510080c080e01000681c20801e0b03c4060101040c00050682041300407040c611802c080c0e0800c0400f900051144d0712040c611078444e20100841d5038210305982101a06000c1904c050100205200c0d0011010032000802d0103000d8011881510540050754440140c501081031100081d441181160304100c060042c580e02c800269810742c3d4840006c503145048481102d029000d40d50101c2c0c0c103544042030041c24000c2c0c3e6045541102c00c2180d40b0300e55a070301d8100aa4407090003404000480c5429801071100c83c1c40d603409188107003401450361410680151120f40342000c21603941c01c04800c91403161007207030307005d0040941041401d05200b621508000c0400c0c1c18401c1481038004500101c6515400c00802916040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 380248327 1250 380247077 380247097
    0x130f06050a060510020304180203090f030304060911040608030307110c10020a12090810020c120414040606050f160c030206040608040b090a15050721060501021506010e090c 76
    0xc0698504000000c005041c00d2003040d006210003800208107a1002c0300301c034151001d11701c6200c048a1403000c0301009400c0282050b209228a44002030f08003003c00246100c1c0d441824042401c00145c0b406170701e64000e100c080c50180d0304050301030103604008010b0360b500c81143e103461904006451545460880f0381c144a9401144000d10245000d41c04105080450b0003900d9407245070049100843d85d02905e841441015085040800200346050b00105907500c1c40400b10742d49075444d004107034125881a8440001c07101d403005400c1183c2880e01551008010b02d09081d800c040e00651080350070b10a010305000740e8591501c4400401c06514046405540c000e010760752100d4455034054076062040d60103417011000c0b0b0700056100c0c040001c444400c1a03005905581071b002e80c2d00d5980150001418510601c05080d007001c00420201510b09038500329800c000c00c08501c0c3c000003a08040110f0720b0000e150761002c040190070791308608500106401035030545031540d140301c00d00b43d407806244414 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 380249577 1250 380248327 380248331
    0x12041b0e0118180b01050d150501090c1b02010906030b04020f030408120114010f080702010b040c120b0303090603011e0308070302060117160b1812030c190803130f06 73
    0x441c1801507006007181d0300550500400c00e40f0940c2d10100c001101803000141080070b1030340144100d00742030720000b10310b6103c4d00b9406840c603104050401500e10980110210030b0b981c2da01050001d902503000c6203070100c0546400791042e04c41c0c0008001d4807041c01290103240c0c80c0ea0081a040d119941201d2002c020704040381e4403410f0500e44101107900c100103144441e440040040303203400c2e11400050755003905071203040a006003401c007035403094002402c510646d540e8402c16599030321503000d03c0d00a4106503450503110b0401d160035000701c5031b04207030300d50080d80306000310000ac0e140c0c075085034155441c040482d960780740c8400b0960352280854100038440c200100303a490400d42c00141150695170003565520700c0c0d10381103070a00e698540e49101d40d40d003d036405a0411807046107400601d422100400c05070018080c400103d200514400c5801301303140d100150501d1113100511009a48041d040a44000007040741c4480040b40001f5040c00d4466040441d19010826403145c003180c0c0961080302 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 380250827 1250 380249577 380249579
    0x2030a0f021f02060a090606170609063315071a0a050403080402040e0705062107080105010f0315051806030f010203063012040f0b12041b0e01 63
    0x400480c0100300d9404074056400301280008114524042c2034400c48154024400e5588441c0c050010f8a4045002c0da4141e42e1000d000ca100c3c50a03140012501c450705004080ca4248240042c1c54090000e00e0503210351302c0030212281c81245e5014500c4c040d0388210092181d03540d408002510995041c03009000315100203480c00820086e041c08240000c00c0b02c420741c006503078440c148415030708101e400900042c030b82d0000a0052038160700841004008130201c0e0a01a12000400c0403580007010b03130302c0820070186c0c1507128505000550344e8840001c0c41d145400303524010020b442501030014941c01d258071106400340000b400701c821402018018401070400e5030601801090b060103172442e0340240101c80b45682009014002c8a00811010380001480d1381d48401c402071100701700d007501307003000d600d8100c00256000c10070040300078010100c00144d44500d410401d10585125078840e0109403014001031004642d003029841c4c4c0150032028100c02d242c0d003000410443c8402c0e80018407a0022200 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 380252077 1250 380250827 380250833
    0x230325020d1202031b160b0a090c170a02060f0f030a09050d031416030605030307030509030d0804120807050c01060e010602100b06040b09030a1202010c1e0210150302030a 75
    0x25000e507402140c1e44405200180c001c5800742a072100710b540380c55261030f203610019800f1582d002444181e58025036005204020341d1101202e00088e103003c00c000d03440746035040a001d0b180c040e00307004000c4107a0100d203003450034800039203900e0510000b9105140c00b054900b00441070800315400164008400c83d0340f0300e840c2c404000208100441628a846001c14041d402c0c0d0180c820398030006040045040c8543d02d5111a421a2002e1040f00c820035803104400135080c2c0b000c00180401034070989800d030302c40c03180314181761071f003d44038100404006002040c00b01150004482d19400c404c0c1c0d2070b04403419074450b40e040e51103124450325140a9031a12000060414400c03c441303060f20b10740e500389e491074441e844644095554001c071146d80a44200020003004c85c41400420000b030014055501003041601c90101481c0700142080250351079044000310705c0d40c007007a035040007850381256510f03d0141803030095490b05680911450190742d1800e13004040c448408240055500038100e80c0092501d107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 380253327 1250 380252077 380252083
    0x1091503052b0305311a01052d190e190b03031c0c020114010311030d0507030e041d01020a020f0601050d0f06090807020a030305120723032502 63
    0x3031038800b0002c06070076516400714802c0c0546409a130f03c00e201046070102c0003008120f06200c2c049600c0380b04844c80d042c800000c0a02c0c0701d41400c8007040d500e1050310f624180500815113028800281c840e04045042c00d6000c010030017800c49640262040002014100e0b44101c0ca0105904000d000010301c1027040160044418007a0240c58403000a02c0b006000300f09141e503034020102407443d04184495050b0030346580c3da0182954071014030002c10100002002d001e05075001307130801d0340c2c042c03100c0743d48030035a084c00c01c031522088540380380280c6410444d8500500340c0680240a030311550301d484040100d8901c0c0d522440c04041c540c0300071955400c840102a580c1c0c91485c07043c0c3d0041c06107100004079443c1074001165074503000703480c06c20207640382d07503480004018030742c01260b11410a011200250b114040d01d1009548030b51522540c4140c101c4044141420040420b010800c9552204142c841d20819018100400300c0c0b0450302c0e512212086698415187c405010211741e07114106641d075800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 380254577 1250 380253327 380253373
    0xf020904050115150504092003070f0201060f031a070306090c020c04230403051c0615030f050907063518030c030a0f030b030604120e0d0b0109150305 66
    0x1c241c2402101d03644111050019203425221030114500740020407c0241a030460f1101c00c0300403191308400f08103480156806c1e0010341e071040001c0c00204070305031280e80920074040034218550380b40d4085851a03031000603e03003030b4100b070381d040c180800701243c900c501907000032000c2e100040040c4001101c00d00002e603a402a0300850348100d042150030700c0401d407602c6000f0185000030240d08040d5880b91401d450a5004100c40ea0340d00748469139a103820001d61050708050706103030148400004c04042d0041c25a040440b039000600d1a12042c0b060000c000220102244d035641070000c002c0d00c1d02106c103d01d0b000c81c1e0400c5a00703240c030013440002c1a030b6154012842040740003e205130740aa243c44182e07880c0200d10b0240e045600410080d0b800d9401180c04244020a5140100e80750060002203818440c05030340c1120602c80ca1b0301d404e01c00c51b41040300b442c09040d00340c03202c104520141c1c481c000b28040603c01c440d0b05030765560040c8044019140402c3c061a00b0008960891803880740230143c090072 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 380255827 1250 380254577 380254601
    0x702040e01060b0903150103050c0d032109060509010507020a291015260612030703020717010c020307020f01050c060702030301080105070c0b16050c0706030e1002040803070f0f0209040501 83
    0x501c00301c928006c280009150b0590750048020aa90380480b000e015100110303040035801e21100d00f585140303080521240306c6480c0616840858800c0613850900190f0307001a003c02004d90501082041130340c0d0000300d58007610f0300104841d00111007070918104590040030510740300c0341388008001090158911001c1141c0c0020304444101810a604030349034034420a0080400341d54600f0040c13200d641e0b40c4d640b9080701340103080304038039580c0300d402c0c9141d581308200440150300302450801142901c1c3c183c82074003060000003800b4550f80b01000940380e11a80ca00244110400302e110a500d921413002d40e582c101640007147d85a01304144069901d4000f4811180d0319824040011070b00c51080700403494659220710f080c940f90312070a05406148010707602d160200700c1c1c180601c0940c98810882c1100601c0b59840014805e00c8940d800741c00c0403a81c1c01c190308083c0c0100b200b0800760000000311110346410240000b150040351038000815410940040e40c413042210500c401d004066224050b0024 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 380257077 1250 380255827 380255833
    0x1805160504061d07020c100201091202030f071416270b0604180b0319140610060f0e09010306020901200d0516021002060106140405060901050702040e01060b0903 71
    0x1a5840c00c000c250b0b21107000720800c40342d140b100c40341041c48210071940c0100b0180140c031905814400030810180d02c1140703c1006039128a802001d11083d002d0340031b075440052014526003040d00110140a10803460000c1102c556002507650422050140101080a1703a61045c92165102d083c10220610704206c030558031010000c4410024491140d100380c60400303131000d81804c2c82c0010b00c00d00c80d09049000d068081d1030b0704003e05141c3c3d0a00400c0c0c400b4100b40400c176007200340b038282a151400d01980c119010b621110a00007a05940400c500440310280303442c0303900c5004203600311007075034640120b507801541e00f40001c420800da40d0040c20107040c0130b0341c1e40541c0c1c4690341a051010501c409150100b608070a021003506417141001300303900080501c2e601c45e0202e95501080c0b01c0c030a544045001a0001401408080e5000300e4468000212040c024280380c141300001b1407030b10445880c3e505210b40003c5100454485420260007a031022001300410fa41c2c4035040031507a07002d12540d0344640 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 380258327 1250 380257077 380257079
    0x61903080c0d1701030c030b04110a08010509010c030e07090b1807030c031b0801060315260c090103110f01170f150d08090402070606031509050d090e0a0f180516 71
    0x1042911078103041765040340310050000d02d141c8416020200240050701d05250845141080362141402e1200410314a00006107070700d0b01501060031100b1441202080508007001c486240800042000c292040d21000003081d8091a001074040a11001d444000300750000070407000e26059030007400c48015a0714103020940030100c020440000f8881d070503011030001001803110350301c642c0c4038203107034080c090241c1200394541e80408801582d0714156410720640d4241103000d180c050240b984e01000a441320840f950465558003d54604078a18a001c1c0c60200020351140e03104000d800115030454001c41c0c01400d02500c120b001b5a8212030780080340d0980c0640001c5818202c0c50706d40e10f240c100c1c400c581000e001c0700c1080060f500c4040300b966000d4485101201003400c14a5040c14080c0001c4001811020b0703140c11810101e0400000c800c0c4012806c080000c04d9006040681c02185c50400007624441c41c0c1605006010111040e101066000c01080c108100040c00c0c486000200c1c0c800c001c41 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 380259577 1250 380258327 380258357
    0x1605030a020127030e0418080706110f04140112090609030e0a1d0402060424140f030a05100905070c0201110c0a061206050d0303090b0a060b03061903080c0d 69
    0x80c08400341c0c006599403000039030300c0130a1083c401a10524001000031035003c0d140e130603020351590351120603194100c00041e01707420442144540c40c24500d030318458a0070850140452003541c090ba210318094a103044100c185d291b0720a00c1d00340680307130888400300642d1300d02d8103140380207040040c802c40125090400c1d84c6074a180829580c0215804181520b880e1910b12094000460000c2d000f260004400e00020821000c0b10506418503040301d0541862a81c0c04030700102524401480810b050204011401d51000b135441101c0e40482c0c24040414240c440c4120540c401060794800820a440e05040c00b1149520a0103066020f001340c0c0e42403c4054040c444540b2601c200c40f240c2c2c4d100c02030980400490380140102c1d43c43d031082d82d00000d402540c82020440c1d018110408600007540d490180c020021803160710342d0000f110810420110b0308140078030086100103004907110701100d07004110078482c1034011101070f603803040f0756544a01c00c1d01401d51317880c03010914150200b603005440c2145 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 380260827 1250 380259577 380259611
    0xe0105090c0604090c02120703020309010801090e0a060b06070b100501020c030f071716061e080402180a0605060f12010501110c0108041104020c0a06052406030c1605030a0201 77
    0xc0030030010070b282c0c42e19241c65050401442c0d054a101c0c154081e141806c5011488170f405084140c2c000d401960707644080c04001802d002058100d02c1c1201d1401d000c503480f0700300008880f151a40d21100c000785c1c10444e900008c086010740b0078000e04032440b0100300606009138940f90021034500ba02154590701c4684101602c800301c0c0b61980d10705909c071410030801c25042544009200041005803001c00002102c42507100d6841d0b00800d010404102c26101c2846220140002102062130b0031030560610398001a41180c0c14000804521012404a207841c005c5612500060200400b403c3c1d0b582c41d1080794202d40c1d0000746000000c201030a000055550158006215403894a030150140c9800c940c01542c034041c02030003d0b5000440c4000010103074889100038001110224000c00c1c920b0203030b182c03540c00c1d02c0c030042003082450307018481c0c024400b603413000d13501e441c8030111a92510f135034481c1e031000380301c0c0206210700c2c03600c0c130301c0510aa042c00700101c002c0c85c04502680c0207021f59000040d00107a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 380262077 1250 380260827 380260843
    0x602131401050c15150d06060e180613020a0b0408010506040b0a0303021009150e030c011109131107230105010b09010507020609010c170d0b030106050a051302040302130e010509 78
    0x1001c1e00b00460415a80300411300300c980c0010501c24200d1012118030100e02c40d6034101c00101c4103250340301c070180b03c0c1000c05000b007a071140c080022001c040000142c3e43d030b12060302401030110340c41d880046004668940e000440035000c04104144ca55030348041d0540a08000c1d0b9181d40171714900151000e890400c005001c081d2601074005100740c0b03154480c03103001031081002c240c801e074024411000580c8928012003001c180101c000b961150b14141000342111864961119030300c03810080a2003540f0f07498030f110741650414400180510b00034110428a1050b50b03001000301250041441045001d8114000c2404000b4020000303603894654144840c8501960607000c100c0c10f000c083c00615200d40200020001850250310103110f6a8503900c4003100000c0c14100c1b100301003414111252244515a081d1a0480081c440c0da4604000304000b44180c2c010700d400341c110242c401c500401c03260120750040d81d015103404586401c1c090000c004002c10314404060b5401c004c04583c00d00400580c8907 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 380263327 1250 380262077 380262097
    0x90915060609010c021003090605070906110601141c05030c0607140412061a04050f091011030c031b0c070f060f0806060a11060f2a0d020f07060213140105 68
    0xc100d1342481d02003107450b0812114800400d61142c80b40c00000d819800b03698010305140c3c0b644d6114074140900548081540c02051505034007410040040d49072484c042114014243c1c0d03086181340e448401d110601041160292440c07100103a5880350700304c0021103901c1002285d58000d8008002c1480304154030540c4551440300f80044481c0740440c0e1542d0008100c08110488081340310480d030003003000c1d02d904840d40d0300145140400c0000041c01881400c0580750800c100300a51211034442070b402c3e01010300400842c11001c400544940081c0180e041011907080040743c4a40c6000c1c02d10f03130741d007229000d001d40d0a480c160002540500920b00034541e64405c3d100c0c4599072707039840144066a000111071900b0400c80c40c40f8900c8144d0207002090052200008101c1d007451708070b20211411908800045484007800e61501d4911500c00540700244400c84000d83d540c0505032400b020f900a102000d00454030002d086171354050090074007421541321200341c070b001d1828500150f807113000b944058 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 380264577 1250 380263327 380263337
    0xf0c15010611060f011802070b0703060905060d0309030b04081e0702011206080c01030c03060506070c030c05030f03031812220e070c020d05070b03010b030702190f03080402010e09091506060901 85
    0x1800700c076070a0780314202807001c8111b0040c107048241e2202d0b940310105480010120742ea030041071000d6412070042075031001090301c13003014060f800d40d00204000d051b8400a403040c41807401003400c0224a4045480303890314440c0c04030403512075010304190f55002810480c00b00321644102030500c1080d01540080311128806848030500c58001900030b8241c400088080540d42d0030082019a00c09000d4500d0030301605001051a055140011850034950030407071180d03200b94107044c1c81030f0002003100d5102e03800078903030401c0d24880c8640502d0136a80090300c1d0038451022039107202e00100042d140415590700d61070100100c0c0c0c1c43c4030340d01c1c003000142c940724009211035146101500348060b5018560340b054088480c400d985070700ca810030740c00070703003010311206000000e200030745034100f102410720b00c001440105034000d41c0d5a048007400b400000142440003250005080d68020006034841c0d86010300003003054500121104c0c0c84400000d1004184c3c1c040a000c00d01d9400e1000c00c0e1a89510181c40da = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 380265827 1250 380264577 380264579
    0x1081b090c0306151b070f03020604060c06020d020f19140405061e0d090b0f01050f040513061a03070f052808070303020606130911060f0c15010611060f01 68
    0x2011503990b0004200540122101d10b002c21081100002404c0c40d40030b030081c16044040426000d4204200c2d6482000608454002440565607020458003101d0b55402c0c0f85019542174980b040c041d010346510b5142c024408a030f62010b0151000040000c528004803009500c0700c035480070741d0103401d03e1074004013401c0c0a00091040f42000750003400d042400e4110052180412540014142d0180200301140354560b0640703401c000414046542041e00e0261043c03056040c600410340b46d46000c4842845070762580b0110710920740c080080740d08950050000d0120040010214221905400c0b1060203403140001c001070842842ca0b20500350340d40148540503810811224004160007100c100c1c490ba0302c0c00100103480c1108100610007948640c020303011034034201c400c03c146042038680c5c1043d07617400c00c0300d0800000c03c143c0b4100e01504003225040d4844200300c0030983c10340541c29214800744950414221440d07582c44409040b13500d56075602a1152171226260717250034007038482c56001007641c40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 380267077 1250 380265827 380265841
    0x60405040510050a0f05130303060e2a0903010c0305090c040c05030a0902031f20040303020307060504154113050c1503060406060e030c040f020d0203040b01081b09 72
    0xc03681200b900c13000800c42e50700c841e1100e0300702c0c4c800b5036083d110350001c0c0300d0300820142c15018540c01404c1352410300d030aa00e0048035000250f400079038040036105e0030040302041e444900c0c060383c0808002500801107566804c0001d00104004d884000e005e118014100480d40381a0082403140704580da44c0c14191f40324008500c000d0940072200300d03818090b000c0320341d5045000550302303900007400000100308080907085a80c941c540000345250880000c000520101c2c1d0004125034069511402c0000c242e40c0c0c0e8145150300c41e01da0001115841d0505070780e5481d50b0702d03110100100940000c00003815415207259078255031011076010048004085c00900e800c0040d450411109020304140d412010742080003600c02d40740014040c00300072000c802e1080ca42024400c010140001d8148071900886803000655620384c3d40c68030603c29070f222603a18100120a8051302d041c090140b9056489052501e0800c0f8510380c2400303211420321500b84030784140c3e0500e0590910342d8030007406034410358403419 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 380268327 1250 380267077 380267081
    0x1204050102031204022407120807140703030608030a350f0a060302060a03020d0c210b01030207060e070602060a06120b071b23030f1b0708010c080f060405040510 71
    0x40084e82e001000c031b40080d2000c4003002c10990b20400f0a82d030b02c1d41d60034061429032400c0065a08030b03020408508204101c20f50044d0241c2c031072200110748030341c45d040136180440103002c440d00010130501000c00c0111010b1b806c410640700020020b901c038030b50780311a0408041b0140482d1080b800054000010600c44160184030940124040c0e07000300318592250007245140d40031b0b1408000003035000840c1c100308000c1c1e20800f030b168500c1c3d01e00900d03010320796100b00401e81c082603118140f0301c0e0750f0f00c03101a10780e004e9411207a40c80c0d0300000500c1000d1140c00c1040d1039560070b103c1e032405406000300040342c980581c412040de540e034000705c0c440700b0401380e241d113142030340e0044c801c0d001d001c02d40c600c4500144060b02d0510b240c0344510828550618001100300b40314500121914007a8801c0c050f6070000b4503464240e86403420f409055400003200309140a28042081e4810810341d40f0702046040d00a600140c00f0b80b1a10180f04050984d840761014001100c1c8202c0d00500380e034000382d0303810905034590303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 380269577 1250 380268327 380268331
    0x9020c0307110a0e07081005010f080402132705060711190206040909120306060c030512070917010b0108130b04111203040b07150e0d0c0510020c0f12040501020312 72
    0x5891460100e4440054800590042d0703042c0c400320300050304010b03080d03c5080e47c1c000640420329121051014280018010580103040240300d41c030a06000282d40e00607a02122050904424071011609000600140c81d40e0601d4155520f010340750024000d103005103ca170885003500310090101d4003c030406103d0f0a05000812680a1405c110004500704203000e82060b00f40100814822001c3c12030003d01144d0303d5030301c0070301805202e00044022940280569480d00e8490284e080d503942c0c1c0c40781c2201c0103001d507001040004544610098203200552145101c0e000a81380c25119032604d0017030110f00307580000001c0c518203130180024009515039130b07c0f20003401c025046001d052400200c5074215001034104525513500410303680240a00702d0300c003e0240001102c1000340e0700342024460740711a10400c10005001c3e00c105400f00704801040700066443c0200fa0841d00c545800450b5a00e80361018a219103034815420040d100c8425841140c08540d0141c00440c54508200c1660b0004000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 380270827 1250 380269577 380269579
    0x41107030c1e03091a0405091f0603050c0403020904060e030309070f050108040b070509120102041401080606090f151306350a0902030c040507030605010809061b030910091b09020c030711 82
    0xd0100180700d488101200740aa0946244040c5880d5800e1b03541c0c8449c031803680310801301401d0109009a001408045030180c031b40503260fa4802c0da42d01c1c00d044001e466081441c0240c2e1000004002c0d00d00b0000ca206802c1c0c403400c05040c001c4950752170046441050541e000342100300c2c10004600510300400c014807506401410340c13007090b82d5017048182241c02a50140442d09c0c0c1c4070390a8520396a005241d541d000008480f4542051601d4001c05c02d1045800e808078000c006c1007008913084000303a000e444010440c000740c6e5070b005841302c00c001c007610b142022261550342640152081500300e4011070240040310002003c3c00c1c2d5481210034090114848181e800d0700600c0304558a42c2c5942c0139040c807070400b5480c0490050301d0540010031035680240a14560307000b8409101c804550071501e100044e40e07150f04036851307860fa001d500d4189414909807461341c9180c44452003c215248988503a42c801c12602c0301005550780507280140e1140c80c4d92034071190070030000d130000541801c092140c9074034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 380272077 1250 380270827 380270879
    0x3030a020a020a0507030302031b07080a0f05070902040b07020103061401020a02040c090302091602240106082211030c011b080c01090b010807031b0b18041107030c1e0309 75
    0x25031100c43c00c0140f15001074006803c005044007250410041a02c0500ad18600030400c042c40c2100c01031300c030303400540008e00e41d20001603070000380202009404042d0142c00f070210341d284e9443c45404a560310299049021900305100016a0502c503503e01114000680251100070420781c03c106c01025410405001d0010f0610302001680715403a00c1c0f032190b20042901e040200301010040d107070001900130140040e0001c0d44501c0c00010318880b9504403207940c20305581a45581070425600302d8040e40303c85d208199101060280140002c0900c8402c606078141c4081555150045990043c01e000c13043e10380d40c10000c20400611900c005108031503400c000020010001c1d900d034103400d030342039204451550280c00c0901c148862140c0c2e030055510700741c03070807608940760205107101801800c4007030000c800e0045000d2499190350b0046204042a90901a560325240c500503114640e15130041d030303181704440b0b90b10142c100440d425043c0e5a405071501d800891603c492000c68040c510b0950300312032 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 380273327 1250 380272077 380272093
    0x3060d020f130911040e0a150f0617011a040b030d0c14010e1f050103150c1e20070501020a0803091009140609010c0531090615030e03030a020a02 64
    0x2c42c42c8140c07200248244603d1440040c15010802900c4200c074441103c2c3c0c003e02181d0300069605101b503210315036038030004030740f0300c0030252418000d00c001e07444a9001c0500300580c40d980d10041d8032a40c2c5e61005c1c03031500003007245008140b0040341c111000603901680100104a5040d024141c00c00800c0c3c0f09000d1002094071020030389083d10001915803000d039000c0710814140350340392681d03c00881c00d244e40400036585561505c5840b4841e51001084080e03072641004543d500c036503542100f00e89403080d01c00e108041d01c18010407450700f881d00e0007140108841079141ca4500802c000044442c140e000303040411451700c07850307041c0d40040d00450040c0b1942044400d11141070041d0300b400b40c0105008003905140e502281d040080080080080b07900d050088003001d80c121003030700c6640311010184110002c0300308402c02804010341d04e03841c00d0800f000c030000e12038003541c1080f420b88112910b403c05458082e41c00b94252084030300001d0705900180002040f403009071b40680041410351048031561 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 380274577 1250 380273327 380273359
    0xe0d080601020304180b120d080a020c0606090c0d0603030503090c031b0609190303030501050405061807050a21020301031b1802030408091c06050115080a0c05090918010506010503060d020f 83
    0x103a50805825019400007141c1523141ca801641030f44e40480745075020f602d8034441c1141141c8035080100303441e20440b10314021a1002c0741940a5072600110b0600401c070307050710b90a0280c500d4004a403c5a40c51140040d24103141c02c1c0454640d9a00e03d40c402d4024448035a0400c02c0392540048440d82d420103c00705071500c0800c0d41c5c3e454800214020340f00001c0650400c0240700945000800c0d00340201c86010140d14001c584000c0141d00c00002c0c079115846803c1a030044400007507000000260082d260503111580da0603500941c1241c0c80358034000000c0100c00840118004907100e50041d242c2e000c081c6e9a400c1500790000d550081c1b00d448401c4c0380103c51380018a0b16144440384541514aa4a507001044000d210383c80c058400f01608906503801070134010703c40380c0000c2001e0400c03521000346202c1c1600070706c142c4120240041403040a441c1000d103202d906514050001005e41c241000319800e03500030340c00c0341e001380c1015000d14443e40d144c6d000d00064140c0d03000c04030342000850b0512844 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 380275827 1250 380274577 380274589
    0x904121806120b01080108030318010f0603200103090305030f06221401090e280524070e010509040e0a0203031b060603030301150c030309150e0d080601020304180b 72
    0x141c04141c4458000c014a98069822200c805102a060100650043c09020000003da950181010390f201c0e6034400c50161031405854403011891450b03080910100c02c004c4920461001840308801c0906461a000300450507034114500c040c2c0403d408201003680380c50b418a94a13800038000e086080c1925402848508032802421124990380c0e0b2904c012004a2041002900400b480c8400341700c0d043c15030071042d0304c0c2e54000615055a081c40b00d1000707154104000340811080e040320a841040c009900c41d002d0700300040c0c90304a009034907040024401401035180007401d05060703450710304000400c0c00384802001e00380c038035050b50b01c944064000166020401050000f1203641035509400300700307040502d00304018180a11a41040c8014000c0f400040c8415540d80072901d407104500400f414150010700d499800034050401001881506480540143c40d1541c4104111240d0311901102194441d83c19181c3c140141c10800c41000070099103940c40c40e43c0c0b00c10078400600740e0041c0c000501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 380277077 1250 380275827 380275829
    0xb0f071e0504050315061906120f0b040603050c030d0215010e061207090c110106140405040c0b030403021606030b01080601260a0b010f020a0b0610031806050402040509070509041218 80
    0x41d400d01804108159030828078101c10401505864072020a41001000b2700100300824070030040070380d215034540d511401c54206008200010b0000c10010b610b074144103484000d00c400c61400707442044404842d81e8800101100009000750f107200c041d07420001240d15000000d00065403200b14a400d501c0c18110601000004020a480004110444610191000c000c40e1003604c1207074902001040800080540c0d6401c0e94402c86001400f9a280d01d0644107000c9150019060140044200410590002030403642240f503802810b184607520039040f426144240c1c0308500240f00c0d080490b8003540500102078607030320006000751411403201c20320040c840b0102c452032440c40d21003030252590f50f08103411014049452014010380c100719201c0c020b903008003034182800352001d408813a00031403080e0f202c0008a003040020203411095810314801404040e14141e1142e45000082110048002108021540d000e040721040382d0340c9803602089144405050b9050000031a480e181c4940c52200c840 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 380278327 1250 380277077 380277103
    0x12170d02071b0501080601021f020d02161506090b0d0b0402030304081203061005040b1b030f040e0a0506030309010f0c111c0c080c062b020d06030b0f071e05040503 72
    0x1002149800c000405d030440c042d02ca0360545d0031000030603d90750788206540d0f5860040c9034015944900c841d04020003441203840214004c2405c01143c41040340b5050451265141d562062042c1525200040112140c42107042d50041e164484800010701c5228566440750008064a0905603612100c40c28880310b5041c410460400100300002440e0404044e2003240c05480c041d401e003030400c00c201143d0302c1281c2d50380c4000010001d0444100344200210741c000c188040107075031950313560003040c5402441034031030364880d50030000000d03120300b000401c3d6030100e00141d56504101d80803000a0312803040075042668050105d60841c079140c0c941c801d01c400030304d60385405211441c0302170034803180240950704241c0c4107800205c4054641e607188000d0b2034441d008400583c81c198010030320b85603109502d01d038a003c2d190011401224140b5168411411a8045c1501381c240da030b030750400110995000c5840e4808644102c0720324000c580d403000c80083c1102203007030842c038150700d43c070001e0f1501443c020f0791 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 380279577 1250 380278327 380278373
    0x9090f1b08150a0b0a02011404050a0f0807150603020f040510090f020f04030f021c05100507020f120a030b0a030b1b0c060c03071d090f060112090c030c12170d0207 72
    0xc0c5d08590912a003858880300884001e0607042a0f520b1a482d041819009001da00001d0482024803069008540140d0351014000c0261250a0403540c0540000e10050784102c00721a00c107200d500b01802524403c140c124503030307001d2a0030b10303122200800d48024074000d015800d0103000d5920720b42100501c00385010300801d186821103171041113441384c0107106200d4101907401800c00003170f800103001e0503101105030340480c442e51106000c078075060541d280da815521400c07500d0388500842038000c001d4422103a0b0706204d1110954207015541e15103200040291846400143c074804a181c1c041c20f00640b4808540d2821103410b559034034118007922800c90f8850000b0502c01d2068001811041c0003603520b16581c00240c100c0005036409070020015130010030740d00005880e0768480d1012807400100b44504101200c0c85080c03a03250782c810f41c0811141c07404c010384081032108402c4d0200000d90f034004080181c0100012100320150000780308285081c0d02407003200006030055550715442c944200f55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 380280827 1250 380279577 380279587
    0x1801020d0e0c1903030905090705090306040f0b0a020406021e25081605030a23070603021b060603070303050703181202030c1c0303050603120a09090f1b08150a0b 71
    0xc0003e241c0ca03006404000004842d4200006500140403c0498004640d0207400d60f50301c0c001030795284030360100558903004510402042201191110441a00548181040e5030352008440d04910850140fa80907901082141c100c1ca0092510844c1c0c03104c01e00180d0f0320303000c14818000c15010780000090200d0120200c05d0041c03036010050b0f003c400c500c0c888800d0b012460800800c2c2c4582c2c600303001608920004030700c80041d008041400100c00003980c1202c580300e9413644000c0094201c0321808161415650400c0c0e625000010128020b03a03004004d880c030289143c0e01590741e5031080c1c80840a110000b440da20b44c44803d545000018595140e984902841500c101810900e100c661284180d1004008020308140301300e840e0b2400d0782c03500300001c080d19110000b900d026410810b8401c9038400190380a12039030f01444080407208a0b65082c8041c5172101510300549a0f01022038070101c0d11020f172000882d11030190705800c501103070040102ca03446600491819451900050010f20b00029 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 380282077 1250 380280827 380280829
    0xc19120606090c110d03090c0506070204060f06170f010e07050703021204030c0602060915060613080d0f08010605030405030d050703021303110316050a09270b061c03081801020d0e0c 80
    0x2080d845c0713400c00c0340303000c000014195070b0b13881038540b59009240c0a09401301b00c00046441300d50000c0e004d0030510b150001156038995006040a50131155000e000c00d03041c011a1007600d00d031000350f06844102d480720034941d44440d802c0b1080e8010000035070452084503c001c42042a000c0140013079030003170442039110b5040110207487d043d0b015058201541c851a00308147c1d1401d8a00d1344c0c3c01581c120360440d9907050b08003100e8011610380e00074145900a0191b00800c076600500342c00c0c100714240e02c8000071680d841030b0649860000716805080c6401c01c00c50b020175503140c0c1e48041d6114816007001414100784008005191005410441d2001300b0034225041c249020008207900d041404015400c0f0381c240740102d030640110f44900c000c2c998440825092034080c5280410581f0440000121000701908190103040030550707603030380155241e4840041d840d6041324140e40c2e542e0162a0307004a83c40b0212140d801c203100c0d04800d2031955003806800d100e156280504240681680010041c03001110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 380283327 1250 380282077 380282083
    0xc270106180e1302060a030e071403010513050a08131508180a02030309060a020109080c030d0b120607200a0503030604050a090302070b0d020415110c19120606090c11 73
    0x1e0452203034640c060040040508545010300f80340380d410f03540301c0c2c1c032050002019006403852105502c4207006107000400d021005280c6218290401c40003880542c440002d01c904042c01c80d903000e00300e03400001c000008503190b41c00070f103032490640f102c41c2c00c50b60742c0c0e03200d800f4424a12030594001840d18420b000508010071484191241000068010340e00182d0000c0c1d13680c410340c1059401183c0204107044110300030760154100c2600002910780d03541c1440200f580f40c0d8080d0710180c10161410016828604120841d07941e51400e01c4d000341440d84038560165421391100c0b1180c2400b4401d1542c0461600d81071241c80038079445a00103507200d0400d002004140d0741c004000c44001d9190401c01004a680000c0d1f04040380e902e6003140c0e5031905450f071000041c0c030031900056407001b125420a030072181d2105109400d002c40005480050000004100b07401100c82d1241080300c2d0000e01c00d0019805003017082d609a481160300040c03240e518010783d4242c03103113900080c011441c2c0424030701201c5814 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 380284577 1250 380283327 380283329
    0x50a03020c0301230a02040b0a05070510020310261617060601080f0c04030c0303050703320a1713020901120305160807152007050c27010618 62
    0x1240203114012021001135071800b416040c00c82d6102104c4041100c0d001203038111780203440c551440f6507031688400c07009810340c1d10050702150341e84150007414070701400b9032007034a02600002c00c003041040e240100c44c41c00d0071001c8040000254210b6070500e4204410007229060700c0744025402409440d00c0da078111006071603070381c10740d41d82c00800820100b6030340101959400032101c40d142c0040c0d1240880402e035401a50002021607220381c5001c006c2c036400001030442e4900c280c0e520340281c031400c41d104560380800d40c4040c0300c6403450020140c0b44002940075004560407407070001480d40c2ca010b2074031080b00098981021407064200088107600b000c800085c090512003041d0306005000d50703030080c11032040005900308500c1044552081100030b000315010503405c1075940d18521076000340d920040c0070510400d610300c000e502d480008030107044140c900642e00280689a19100a001d024242c01d5111441c006809488041d110404220986501030010f5959102030b4880b0364499400748205 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 380285827 1250 380284577 380284579
    0x1090f0b01050c030a030903020a05030f070b060d020d1712160806010f0c060c0507050a050c12010903080a02090d050601090608010b0105090f010e03100f0207061103010303120905031303050a03020c 87
    0x2c00c03154664040000c211801c1c05d00394600011407400c181000c03420010010030040150200049182500030207070081c0c0701580c012030304031266850b840704220540c400c81e00e00a4001040c00c0001d0301003801e143d46040031480700304d913251030310705598942c0551010854008069400c240315221103154040212030b0f00c01400e080444000440c50000b5281c9000f0329401085240c44070307600340c800e40c419000c0d200011791000840305c0c400c446d4585261070300008011340340910030a00c4a03075040c000c1401888141c681503101c0541e60749800f003c0368041c1d84605d04c0c2a41010301c0a10a8000900400216000f8500402c00160050070000d4160075a44401c40c1d081c1008030900c03080440c0d50303420454940410003402e241c01c06c0c0101c840800d081100b002d000ea6502c0f491b0015001c0219084d4009101d40d07441081c080105194078621030a49000c00e00000d0300041a04a0a58051080d548101019030088044a05100342da1140035020807154004407178039001101c08070f0030183c04024003042d0303942c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 380287077 1250 380285827 380285837
    0x609150b092406070602120c040506040311030106081f060603060b12040f060c0f020c09010305061609080d090608090a030203091003090609050303010f090515010f02010b0901090f0b01 81
    0x400500090795154000d04058098425640b00149265000011075a00940039104607110b45141c00e0210082d00300355048114403111070f00041c401514039040324141c9000600850410781180c4804070b161a400c54000d030950f43c2caa002040801302042081b0040744603080d512044066440b800c0f003650b01d240d01900525052805c244202410036023170790301c400d0890f58405059541c60610b904075100045029080c2c51400c880d0a005980c0000141e404400c943c00f11a41480c04009014070404248000340040d0801780209024400350042b10407180f6542c03070250006525240034038104241500d0705808201103803c00c00040341c011110b158081c8005001e400c4001c1542c4019499104180d50303140b00e101c92020240d0110302a40c4600c1741207030040310400103e08140f42c00c0383e480d40203000e0f030323041c000d2800d000003001e12890040c1407180640405814946007084010740e000340341600c49500f595241d034646d030723420348411550500a000c40b641c0801c4021188440501701c2c1c0e1039005550403c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 380288327 1250 380287077 380287091
    0x140309030715030b12010c1103070f0209040c030503190f030e070303082802030f09060405150a06031b05040b030a03081b040e0c190c02211603060915 66
    0x180e00410644201c0c0c0d03040060110100c00644120020640c1d120655840050380600c95032009055110046d09005616480d1a10260481e1709942c3d01030035030010024248040d0320401170610441c0b40350041c0c030840748503840a88035070300e542c00d540101d125410001c4442030b200341459030010341c007040c004040c201000b040c50111405a01d5030b009000190601032082c0c007040c1c90800000d003821040403880315080410001301804400f07580180e1705040c4107900c91000c502c401d10007040c2c190065a0000041c43c15110002ca42e2700c010340000c060005181e41c611000020034620308035038113000c10011002c50068240403c10088034803205010340a035000d043c801000a030080b031b80300c0e007159420a070616005c0900c1c150300b910f07128581107003510007504014407501e0040716000c0c140c0e400301c0c21650709112181f044115032401c0101c1d8040c4d40090649080226040c1b40400b002c0c900d25540b0540e00c4500252814401280c1d842c0c0c8122001c03950742c940c08090002000341d400304503401c2c517810310406c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 380289577 1250 380288327 380288329
    0x30c0d1506020307060b060d0c03290a23040504060b030d031104140301061a040f080c090f04140d0e0a0e070504051c06061413060515131809140309 65
    0xe00400304028070190b40e40711020007a070740e10419207623501d10a0100b03000c02540048010081c3c03a10400d03001c6c8a0712600704c0c030302801400000d01c0b40d03a440c0150041039440d04c2d018158903680d545030003085440b151011120a80d48481c012144100d0042c00049034043e4624245850003580c440400d00f010303c1c2540030b400058051040f6821501065030600c03030111b120780084d00420044d84000c0107a583d0755458114a8071060181040f1059401035090240c0d42e5030303a1944030150b000e40c055004000380c0005413a035000c0e80000d50000d00910390202d124442161a615002440c0a2000030030410010701c2414503050400e10083c00da05040250f0301d0801c282c02900074021402003c4c803619506000700c0018407040ca030000c02a420090911106545690003105105980c0005016450340701c9480800303041c50003003d007118405800c5541d071000441490400342c0058030b0051504c0c4001c04001800d24000400004802681e10f0025444c0080d00e802010144800d0051182e038005020320700b42 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 380290827 1250 380289577 380289583
    0x703111203070e0f04060821040503150a0b040e07081b150307120203010b0310090e06010b0915041502010605010c030210020d020903011802030c04200903030708030c0d150602 77
    0x20b006800d012032424008800500c07002107901035180c00518201d00000d043c100005c0d0f00a0840300c000310880354681c0c48460540720702c6070340075480e01980140381800100030003034440d51b4400141040001c0e4500080c0018054500c14154030017035520000381131140300010b00660004a1804d40481c002d10940c40200344400d40d54010010130500100002d954103015548410480340d000000310360f00e684800e8003184540090302d0100c2c002c0c90101c40403c01c00c06500c1400d23004a6400e00a240c00e07071911040c0c0455030f2080c401c180e0040840c602c1c41c149040d00001820103404c14503584444070914000c020b003110102c0e40418104401000c2080109402164032001c0c14001c02000d80e031014042c41007400ba00c1001650383e095071825400500515010000d440e1040c0308a056440100380c0e0410007054810710a082c0c1c12072490402151440c01c0c8100c001e00400c9409004d0f01d00348582612407807620f070021110781d00d104070005a0004038900078070803807c141d10034200401085082101c0259 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 380292077 1250 380290827 380290831
    0x11030a3b040917040e040b01050618240409091412030a020a020118140f010203090705010c0c0e040b0a11030103030c14012a111b01141204080703111203 67
    0x401156180c040e941880740d0700f0355406000050f0b2606582d165920b010302100c1000072102607481100020002c07409103010800c030380c41c02030002e1134248182603100c10461068403070344450494461038922030a01c91700d0030020b4002085455030000340e944d02401c0c2510501c0441d45400b0071034010b54603498030900c4001c2501d03001a08950b006898083c0020182d00502c040e0702d14035511303205130b5420410090005c80300d194004030901510b0610b40d56103a914281d000a88115205802054040c8842d501c54a501e0340241c1c00785aa20031100c1d95040710b040503850945040d9a845503030741c200320300001070780100c01500c01c50840c01480c40d851610300800300c00f43d506004003049038001c11035440729000d4000c100d4016460360308168640650070008002400311100d0300110341c207d0140140481d002c115001c40d425115a100342e4a102c080044030380409072000c208016400703012000b0f60300101c44195118078132990810360344d01250304001d0290b0521174104066544920b25524a003070444044c1c0e5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 380293327 1250 380292077 380292079
    0x90c070f0b04030e0a0b040302100e0f060d0609050f1f030b01090b0301021b010509010c090509010302010f11010c0207060801151413050303033103090e0711030a3b 72
    0x640c0e442e2840d080f6a101070100d04070f81c0c0292040b801041c62010b40d0018022a4401c41e030006110091040680311120020001c552050782c1c013510000d142095802450941000c500c0043c10302d0315907076500207da000b91581864210803008104004803003100c00c007203103400300e44c29200da545540d88284c62a04140606840d45840f000300c80c445440c250180c5000780c010002e4001d00203660304036a4000c0c1000c807014440c0c5d6081454401704030f030240d5000c405854014250743c019070300355001500c0455140341c00c041042202c0d180b03500410b1083c402c0400074840c5601038040e0034507109000b00300c41d0043e0040c1c40c803010040c142101d800e40201d8a407140d031648800e00c544074070440508607030540e410390045030107000000812850440350200c550601c00420148400c1e615581c401c01454400c290009000c0303155104180400c601800340c06901c21803910340310f80700c12020130445d0b095030020303140b4901058652484207014030900c000c000406c0c0c403460700ca8544103100c1c0170b0b114445d2a200740007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 380294577 1250 380293327 380293343
    0xc061409040c14030703090308011205061501050c0f0a1b051c0618030e1507030c140705060403030302030f070807141c02030408040609090b06090120010507020c090c070f 75
    0x442c541c6030091100b102c4082141c14610b4881c82c20705009000b40c40049000c03000900c091001040e483e410b005040c501d150408000c15590b074030661040301d260801c8082c0c2c0e0500c0024807100071405020400c54030395020703a401512403170400740b07058624850000544030071900c0c00382c0f06000540303800703040840846440400380407290031400c00c0c0008101c1c15141d070354000d807281c3c02403050540000719603420190035038441c91140381c44554140c3d24050644000c000a15264a90000c5006204c054071000c20038000e8400e10703a650400142c0c9a4031590045003c00e401004018001002050040c1e0024007414482440d1a01c13400082039802681c0361a140060081031401004e03e820012009104140d0405c541d2801c203814949203d400511403800080c1c0c0c065400b181844080c0a010001840170b40711b28140350b000d100540f4a000d9854400000e09806986002010700034060103015007820740103840246510024800380b00402000481d9643c81004000d001030645411400e000da000041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 380295827 1250 380294577 380294591
    0x9070c1a0109090c050f012003040b0304030f02150114010c0302160305010207021309080d050a2405040c1403010605090307031b1d06090105060f07020901080a0c06140904 75
    0x40c41000e06404000085503010021074200072580c41501c40c03070300503681040465a60300410010003903008803107000070001101017020300c24100d10030910b440c6500660341015203c1c4060103040e08122070503000a0070f6030311403100341501488000391116504151030b109604040e010110a0961341100341040b001c807162a051510030700060b2107909a80d034507007608580d00c2c00c05134040d400c4000240c0c4150040d403185800c000031071285030740c1c0356401078030b440c10066180107410080200030030040e0342584500044082d545026031101507000340c18120207606080c241407208980e08107c0c00b0742803064201c00c00c21000c90140681c2c0c1141e000780b920716500d0002d41d01080c24400e15500003414071243c803160003141d0102d00c160340d00381c503003a203000c0002154400d41890345100139102550015038060040c005c90601000501825044240341480c0402940c007080b4605000d81c002c0301c0c19005285082c00704034051a0003802022246460441000481c2d09440f151040d100418402c0c2d030b803102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 380297077 1250 380295827 380295833
    0x306010b0c0c030105090604060e1507302f090d020a03080f03010315062105120c01090b01050301020c150910091b0b04060903260307090e0703050609070c 68
    0x49020b80c2c0c0040640240f0890074040341d602e6407000f090764121585818114100444400000c810128441605500c141358079a083c0a448086401104150909551221208210341106203500e0700300340346400140e48030b01a0070815503948442c10004d4200b8070300c00b02c0e2081c681d002c051701d16581c030440300016103130880e2000516000c481c0e07100070a14400810710303450340c8440f5030145048a02a0780c0d80d000c010300d8000c48004541075802034260740c8180c5c515141c0d4000724074102d4085940326000301d8001c000b03030000420142c0c001d9110182242c1d12a4040010400701c608030031f0040605400035070404480f1146151903402d8401c1c00303100020400000b840120040041c50703c0e4800440003040031800d64141542801d6220380709618240740342c800062122203074800c403000c5960555803100080d0542d503580c5406440c14420a01559814a605c221503500c00b00450003403403242ca8001c038103803a104101c0079005004142c813060528003020080b650301c2d661041540400145401c4843c01980d00d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 380298327 1250 380297077 380297083
    0x4050a060503060d0c030302030c011808120901060f0b0a0905030a0c0509070e150d1505010f0f02070302030f0102040501080c04122a0305060709080321101502030306040e0c0306010b0c 81
    0x14a01605c890106007002080c141c012009100070314513403000303020411200e61108003441c1d1410004204000402110114060510301c840e040000100040f1b28550b40798500c0c0001d4010b40c22407840c0d0303800050017242c03242d003020142c401000c042d000783c99035400b42e490740200c040f12845094050340d02c060020b03010510404141101050041200c14980703503287c4000d0b01600401c0e0301d984001d1800c1405484500c0700900401200d0050f03441100d02d401980d42180c4050800170b0313010039403281d458007000503602070051040d408800d800050300c4515001c0010a074442c0a85039128081c002c2106000300705107075504514039a003080c0c000c1c0b03807450118a004030407000c01c40c02d02401c00b000000401000f0020401c54094445541c2d4030042e0744d12004415100d2094801c401d500589003d00310440464101d8a40c2c1d0040c7c2e0000c00c1502d1991740c0c1d00303148054070041522001600b0000030054945000e110341040b0003c1800204004600d8202280da1090180524441180b0201c0e8070a043e01c010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 380299577 1250 380298327 380298349
    0x5061b070b0706060302100309051b0406120b0f240405070e041a0915090a110c160801052d04020604080a03020c0310051e06030703060c050c1204050a06050306 70
    0x980c103070ba451000b400c2020040c00c050004921408010808007103c5100b03015000c1419000b0010b449084000280c4480030303981224240d40003502e0b04000200980043c85060906024119007402407802d140e41c108440402000c13404400100400d0099880002e541c0c1380c00d246050f90001703200d44a5000c1521190b0310031101603401400d000300c0d0000c440c443c8030380c01d00700d810585010b049501ca000349100d0203100b40c106240c020b0031a40009542c803540d50480543c5818400e1800d03d880600c09450f410501011841412107400301000c1001c04802d00c06c840c0e100442e0f4440094100030031075040d810032110026204880c044101003020b56542d64221401400200125640f020f8240b401944a03008018883d10900848c40c842d0f20480040c060680300300c0e07a01154021404035030258a0354040c010308466003501c2100c0c00400000c076107200d40b9044102540fa001d4031460841c070340c18a00b9124111032004110244002c004e00d8442520441c01c0d1142820135580f0b036650000490062542 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 380300827 1250 380299577 380299589
    0x3061a0d020d0c0309050d0203030601120504080d090c080c060703051803070b0409060e010b03100501121113150903111311030718090203040503120702010b0907050405120705061b07 80
    0x548801c00090a4140c1d00400196210b001507d42a05c50002e003a40c0b24003048070760314049804002c10768644240b40d404243e0141c400c0803403500f421541c14018084885941d011544014154020700c40c3d40802c000d41e281e180340071101145800c0306660002c000e4001d1200d40460056484e0114040b82c1d401e01080f006011a40700140c0c480741d4403400750018000611a410000a14030000302d44915214212071007158110f1180003020315040c01100d02072003401d05080516a01c1c0004540341030385000a200600030400584881130030410b400d620881e140e5410014081c010a00b000059096074583c0d0f1404812102c0c402c002800c5000c0700c026154105640b0070029001041100c803030341000c9446103042101003841066a103a12200c0304912003650042c0c126481800700404030000c5c000d425500c199107100100d41c081019003c14000f41060761407201082021605000a00704014850041020403008040701450034000c500305100d107203102250440d81031301d00f006605007001a2802055 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 380302077 1250 380300827 380300831
    0x515060a080127030c140d03140105030705190f090504030305010602150a05100305010e01060f0f12020613231005070c0b0717040609090c2a060b03100203040b060103061a0d020d 78
    0x70b00b8206c1501c5044a0b696800801e1030820b19051a00a041040b41a40e501400a160b03003820300041090700d40c0003018189102c00310000c0484c2080100014500034000424086540e0905140203015549c3c160466401c40d4440902400603041211442d030300460300d0b040c0080e65860b01a5802da0102141d00702600e5503007030404000c5604015403081003280e81e80441000030030b0711040049003090f0f00d840351000801101010300e000d490300300000c00d105000c0c0c11040070b000c2d98968078020400840340d520254060452071002060034220340e0480501c1c22407030721a242c07881e555900310b0189541d00814040841c04901c5c0d00820003079524008661041c212030a494555815004020504900510960504040c0b2070342c00343d070003082819142c041d052006483c01c1a0081d158a50803c640350640d0f5040c0c445400c0004c40c2c03421701c940d090314000c2200140e924903203410890306505001e8030080c10549022410454194410160501c01e100e54000561b514603190303440c40603005011510305618 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 380303327 1250 380302077 380302103
    0x90803041101123206030d0809010b120a05011109060f07080c031207020d02030a050f0c010b040f0606030e15010b070501140c070203100c1409010306030515060a080127030c 76
    0x8910030310310340101e8900c1c4032038103030f07890300c0c109044513200b81517075065010750010741e0500304240103031700301c03540951034000000c1d02d0004400000c66040d164010304515420210600e0288031342030090314100e0104007585850410b9040c0420864807076070102109161011414100708007401c01115982031180301140d480d050303004520b03001300a064990101503c9405490340d80b1600210035100000000d441d01c0b400c055881140386140d61100080003800e568600003c280ca40d241d00c940710440200c0c5200003200c038240398002c0c04452144d98003825aa0004880d01c286c10715041809040d6051101c1003034440505142c11400340c02e840c03c58509207254a0f08004040c003546001d860f400707008030202e524038420581c6000840b9807040a8400080070841c0c180d2132541c40c000209040201890b002616960703e03240c1d241170060400d180c040640500302400300d91314040300b079000079058100003001061180664a0300c0501c0e040f154640c40d003034500d14039003814016079142060070b1f0040750f400022 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 380304577 1250 380303327 380303351
    0x411070605090d08150409140610141203030105101701120b0703200a110f0a02040c02030c030403020f0a0305010c120c0c0b0a110910020703020f0409080304110112 72
    0x90481182c10441601c280c2c50405190303441400c03414041c0185203481100ba0740d0001c14000035004552082d284241c540840340b0301d9a0040050318030554100031101402e900381501100425030240c0e05507c1500b082c00b80403448100442101c3c1103403801c41e0111480300c4040b4083d13540f40031f1000d502c5131950301000002032410390300c0101c5031103070b104001400c42d69441e0b40c0254100d0744041e001c0f4540c0104602c90840c500b004000411701744205060a1001c00382000d0450310b4400c00d480000010342041c4a58000c604142c09403048450b02800070307504115444070040e40da40102e1001902c1041c8012a101c810b4560840300c201561b0042c009000d2411048030142800381031484041d00a840d100d002c1190324410101ca0411030382c8048214100c0d2141d2084c1005401441b030701c00342c0c0610400041c41c0d1a80c8200c035180041505ea0054400c503880c3d0f004000305080036540b201d00541c10312991b440050040011294040e912144000c512000000101c0d0200102880401c10925060503d00d40e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 380305827 1250 380304577 380304581
    0xf090b0d12030c0e090c1207122d0c0219061404050d0909020a0c02040b1c0f03170f04150f050a021c0e06070c050f070315050a0b010e0f04110706 64
    0xc0080701e130300d40b010840c3c43d84040c00001c0600b10f0300074403681c030300b40018002d1402d10f41101340c00103454039000c02c43c0c6814603241b004440041d1015401050030580c180c50300b81c1c51900b200c18074402060708000d1b902408101035101c40c2140c6c0100340740e1115900c59400c202e503a078011500c0e4448403419a4587c5400d04d4600d940703030380b00702402c800301382e1082d0300180d8400240200c4010104590b41c101c0c2042d1f640c0d003444058070140349130f01ea00046071080320361f412089211010b01c43c0e00407000f201400c0581d08010b4007004407925544a800d80190800121030113a0301401d030440e078000390820180303004810a50003060b0700840c0b101d00c28240402d01c00c240d88580c024014034100200750403007032010800b122003140c200c18032100403030b00400700007503059000c1d0100082190007078080d02c02500495005a0a1007950f0b0022118983c1ca17400c030b1901038502d880384641c046c8100c070041141707a811381c0000e0105a095034245200d1811401e0700c00d100c1c0c580b0b801441c0c1d0900b138480c0b59512615140340c4000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 380307077 1250 380305827 380305841
    0x403050d080a0506030a1104090f0f051c0806031f0912030605040b03010e0a1b0801020a03020d050703050415242c150907140705010c020708070f090b0d1203 69
    0x102c0c150a0401003191842d01082c5010030560100d01030391908410400c6c40040c1090344810b5501000d51501d190100d00c00220084449110340d0290840c580003048450f502404140200704004641d802c0200d9601c000604010a0550299a0b0010101c50040340301030400700324000c102500031000108079540503007112041d05e404950500c032280c0070340306042c00c0302c589191060083c3e100c030382007074082441c00c1c8202e228540c03500715441e603803074076404180d007a41c4c002e01c43d58001903400600700303030100351074030407550080c000745824016820251501ca00080c10f40703008a40041e0f4400d2009640208041c1251110f001880b0304036980d60348199401111601e94009092188011400c40c0c003642c95445251080a2140000111140100a0100c01070300100306406102021090128003170208010700034651250001048041c07a5034402828000c3c030b0750001da03d81c5d00803282441021340110515050301d20742180003500740403d20015400c100d5041e000741c41002c200c00c1034264158950007800c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 380308327 1250 380307077 380307091
    0xb0f0d030e09180c0f1f0806180c22051e04060e0105280902180a0905090d0804050a0206040e010e102706030803090307060605270c0403050d08 63
    0xa680ca030390f03840000c100d41caa180d019001580100c43c0c525910700d49040d10310071065002c0c0c8592119820002c40081440700c041689012840c144104400e031300d0001031b131240e0b00f03103081000401402c0403070b0919400c1c023840d80c071201001600410051250000c4200d41c0080900a282d07500500007000000c00d40c5000e454964002c07801e04401080c0e04005041c1141240c40145c900d004222446c200c101042e085030814911100b20484005940002030010345160a44e0708055501040f582c4200410a490769100401c11400e2204110b2000c8001c20303050092451400e1002c8030395102d103040b50814410010081d8001400328011072030001c4160800c3c1621b00c0f1030344248043d100d64011f600b0b032154034030400c0038550a04841c19006061846402c031185000d00000ca2500d850350750704991034004640300c2001394404074640040c40014007400d00142000e85404c0b200d100d04600030035101241041c0790840c100c84402244445242d14104c03001076400c10255104c000182c40000e03e4000242c0d0300c0c2d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 380309577 1250 380308327 380308339
    0xa1101180b04140f120d230c250501050618010524090d14121305100c060f0209090906061011030702030316050d080108030a030b0f0d030e 61
    0x8401059020000e01d400c0742003810581d0701d950b90345560702000c1101d44094003e80310031045810081080c2038000402d8031031642c13200d080a0480341150f10468082c0c016141c0b041401c148030101034801078010350018040c5a548151010400720351020144120b0002c2070031446c18280a019880756001d540205c0fa00d445d00045401c1e0811042828002c0e654040c0309080195004541010008100d588206200307080c0003460b00090400902928251400c1c1ca68900701030720048140f20318021003821890060034098511107191840460b8080c1078000c0014442d02c0c1040c1d07001b4040022099032003002404001c1c002501c810294204000080c01055640f001c5140307144085909440303040090803020b45000c0000c412201903801c04c56810080c00108034000141e141440101502e0341980c460f00d84000503481c0c020b01c0c0018103d017610402c0400e5005200340d62000c000c444614a041c50302188000c120400100520360329881320ba842800800c0250400d40c1007084107140310001c07501 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 380310827 1250 380309577 380309591
    0xf0e0708130816140a050c032530031e091203030525180e0603070308030c090a140405010801051e0405150103080d061d0c0307140a1101 60
    0x540d0922940a080080010342c0600030705102c2030311015024071040c003a1803680000321031007903c1814001741510a99181d080002c0014950404004a0742d4101c500141e04414070813940c1001070380d8030b02e402400261149220301001d42c452194490091141c0e005610b04104c901d80783c06030444945010400805c420888248011406013101c101141c40302d43c513a030422140c0395021001840b00134104151051207200900c0d28410b25082140712000d00d031280c407500b074403c9189003c00b2800b03910101003118010f080040719100410031500f100da100888a03200d4948181088075070041c07441007034015041040c0004c25a006070340111142005490030800c60741c03920381142c00e8071000c0f100f404490b8800d41c2402c401035444090a507009000d50300340c6e0350144402c5c4070300c50038010070317802518030705000300d1038100038181032050000920b050b910521403a44400030804560800424608002c103010001640450182c1840c011210310a2040b907614416840c2c040c042c40d00e01c000300c0d0025840c2240b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 380312077 1250 380310827 380310841
    0xf050d080a15030c0603201c05090a050c0603040c0810020a030b010306030b13021c26040312080a0917030108150402030c090603032101030b0708150f0a0f0e0708 71
    0x11002c2c10740380c00040d000c00c214242803058011b440c1c201d1581503030b4002280c0310724041c41008040c0c0f24180c454020b1041d0b0174800d42c030007130541321b000e40312514540000c1000e01c00139030002900140070800303890705a12a030321390070219181f4516a00089090081c0180410081c3c6103900278042594144c40401481c240302c0011000c9600b98000200211010008980d04130a407060081c201440100515a44030303140d10001d1425843c24411290300305405012503650b8569000c0349031790069000541d040a282d03445008403608006001c00c2407100d2000818894040c641200b540395800050f03864403c0c1540c150442940d0091050b01e541b40134117108240b0103149a05407034080c3d6001801071455a49903000c210481c000505a6585880304100000d450b5401d49440c004d8140701130704002c00e640c51414507940444000300035000b080102c0003004141c03602200010340c100b6050301c040310b4058500010968a09058014140e01403000200003900c4440390185403080000b580c48030040d481e801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 380313327 1250 380312077 380312111
    0x105010303020d270b090411040b03010306050c1c051003051c03060803040320031504110f18070c15090b060f03031606052212180f0608040f050d080a 66
    0x18000348140d035003804c03040120240d040040c0070040f1000300005109000380c1d09026456000c0d03170141400500100c0101309000080c401d480d4845d480d40703003031464142512000c2900d000c02195140425540d00b0100d03461041c0c00042074081c43d0710008458030742c144d2000d41e140c07102e440664500024100070300459015404400d44045a910070145880e041e02c0f042e28040d54484480343e586c141c40365100c0c201c00c2510304030900e801a4043d03025484010604c10a0001c00d00c2041030b0f075030103869148a01c082c00e8021031140b542c45486450700240d0016185403900301d400303001c207103030151a05040c8a030301803202d510030080c000e140898482d12601d5080b41415100d008150ba000354920160b0050b202003003040e0010359000383c091000034451082680440300c01000040141d40b50a0005407001c3c80a400900100300072085500306000140b402c01014521541405241c04003c0340070007040070003920140265019902c5420380d503460582c03100003003100310102c882044507410300c540710300101840c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 380314577 1250 380313327 380313377
    0x6050a06020706050c120318010f020702010503060d020312130e090a050604080a0905030706120c09050901090902030102070b1f060809030f03040305070210081b0903071e080105010303020d 83
    0x1075005040410b00d401c500b0390312600100c250340044d004800c0c1400c0e8181e910700065106000140329030340401c042042c50350850701c0c480a402d22a074810030142025031381000a880d03002c8400c840c0015940454800b10f402c0601001c2e038030f00103440c042009040d0440e8000d80c2002d5900d50401c03080d495442e048626911402060040c00da50007075408075020452080040c4a1029181808410180c1c1c1e40046840c1c4107050f40b019002404124500b00800054068442e084165240ca00005414000005c50300d501c10301c601c103495695900d540c82151802c2d0190307001c468024860300010314081182e00c0c0480a541c1c0303a002c00b8103046030b010450f54060721400b070242c00958002c5041101d24580d07419142d00c00fa0080e01809028041c88006a55124000309015083d07030b103030704185c00d0035549100009913003010b10203441024010a4107036200054200101c0340d40c580490083d01301007144002000c9943c00002055092000100074150001848034801400e5030710001900e16001d02c0c20ba07103091b1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 380315827 1250 380314577 380314589
    0x1c06081b0609040510030c1d010e09150601030f02040e0f0106021212041109190e0d120c03020f03090109110402090f01080720060a0606080c03040f0c0504140a06050a 73
    0x340b050101d2400e055104a510043c900c1030304803056183d441c0c884103085194001c00c860205512400001c20b48105a54010803c030b80307901d0254100110403585940548034000c0392582d4000020f10b29078440c6e00500b04061000078115900c81e1a4007205010030ba084424541c6030404600002d465407000480c0602c41c195030003154200542142c0800c52060060000d4030321082c4030001c0300300c0b5a500fa2a150040781090f003030703048540092400d401640d88030303680400030381c000c00594241c5c0c68004421041d0880c1074140010416984c403820740080c000c0308070500703429002004001c45184154407880e1401e000e888825840b615070b0301000182d10440010980181000e2220600395000711100c40c1c001400d800c0c10030280d141115004104210105070700b9450384201c3c02e00558003000d00c11750380030303150628041c080d500e0540c50007011880301510040c01441c03090b9101e000d1201c0b0911450150000900030b0064802503024076918585c02e4519412032841c290000400c1d00d00f0180450845079 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 380317077 1250 380315827 380315839
    0x405120604080f0a03022b0501060237140d03061a120415240b18060c0304030213091109010807090e0a060c020313080c090a0e01021c06081b 62
    0x543c5091014054200307407654018140c080c080d50425410382e03111401d24005240c0f405c00c2c106900035410081d40c0c010392200c810343d0450305104001a0190650000c0d10342800352589500071a41e020403070200c021000a804d00384403e10350840c0c010301007460080070710070b03079024040244c6410a80305056000d520309100108200801c2c20054103c40701198460b003c1c1c2140c00100300b0052108040e42c08c0d0304a9007031034020340c0140009005041c0c1c4120050b004000c0401d040002d404116024241c84140c5640301d440f02060100b0050300410854003d5907024140003066019404520b0140014103001c5500c000003105540890500b26000360403541c0000080501034039002411006000c1120075031240c3c040d04000f0800301d5810b01994100c090304c0e034011540c81520b503100342d2071a81140c01c1000d244e0481960100e05036510282d0f950400042080026011041d0303039000c0c024422101a003013403401c80007104001004c00d90003041282d060406460596041d07654074010600c01d0840c26500030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 380318327 1250 380317077 380317087
    0x9020301080c0405040501021b1c0302090a03170408010c02060a0c020a020d03030b0402070b0f011d010806160504080d0306080c03070515070602091e0a0e040b0f040312090305040512060408 83
    0x443e0503002140c105001d040018540b06040c1ca4180d40c19010310004600f0747d1021114401903480700c0c0041080200500e41141465201c10004a07201c2d00c83c84050185d603041e00b212001e0020b40d1003210b00802e07140d0020008107003000c0010b501c07200110703490500d0620300800c140e5400e00100e200e030004c550040030f08443c154240c0d4190300814092441503002741d030a00080c00010140c00000780115500005140302e5031400c01c0d0258092500130001c07881440d8000104003c0900094094000c00e0145002d0b44a03504030b8401c0320f850080da802070300b85116201400306e0b015095401082642c0c81001500c0d807030100e0106040d41d40c1280e1045c140c01000600c49141442c4000d006088180d00c0b0b40b402500d810030880024030254030042c42c4000da800c03504c45071a154940040c60600030145108220450b01d020340780d05c089058010480744003265014000742c1050b110300034081008054103420009034505080c01000c5811130b0107000d001d5000003084d40c4842100003000f41c445e41d80071499600d02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 380319577 1250 380318327 380318329
    0xf1f0f0e1807030219020601031b0f0b071a04200603010f14040b0306010323011512050a0c0803070317090a0206070609050a0305030a140601200712050a05060109020301080c 76
    0x1c101c0090a07981059400d12808210f0b100c10708004000c0d04042e4014111541941800038002e04000d60300c81820026003010800700c159540b51000f00d50011389419150061401c07d20160080f42c00801110203018040108005000d203940c5006108201c01d680b403800c1400a000680c40b003802540d100f00c000d03640806c222a100381748103100c0306002d400803e0101c0c1200219280480a800c100c40e994800e60200b40c581c04c114080600d1114628004e01441c0c10300f07014011034803550f014254102002e19000414082e08000c0803407650750089440c0c0625503101201c41d02c1b40c1007018220001500f4020459600c0c5101d00203a01501c00e04002d02004940c5030b0821000b544003d0045072050b4a0700e1102010940a008244004d07001c1d44600d80da924000311000200c0b90a0211b10043d4204da00501116980c0078040c43c9071074281d0b4040c41c8554402c0c140d04c501d031900a50020301c1c2540a0b2440d03400b0442c011401141c3d06108000701e4241d640c0b01c00e4000c09a00090103102000c0e8000c4000c800d103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 380320827 1250 380319577 380319619
    0x1505120703020310020a080c130605030a0b0306010303081501020f06010506070212010609020d141608060d0804230324180a030906020c2202090f1f0f0e 67
    0x100004042103808840d50390740400d040c0b42c000c4503020072a0344c0c0450004446074008402543c800141c82d03200d07203400c0440290355405030882c0030b12400c0080200008032003010652101c0041e6200800b05c88042d81d507446d006209900c2114100c071180318050000c10306500019842000c40d800030302401090b824082801ba031500008000d80c0c1c400384d07951110003042400e204510240641c0c0b20056642c210b14098807042d11541c1108200c0b941841d400c010240507058104403143c0100c6c0b9000641d44c981400040406141c040068265400058001581e01e042209280d600c02c4002c0010f01070301c1c20504058450001c20054400603070612074004030408100801940107054544030005103414440c0300e8500001103401720080341101000b400015010013000b882c01d80210b52000b40e0032100d079451006d81000e4441e40840d1034020a46942c42c1d940ca0700692080c0c2c0c0003410980c0210070101c0d2402410190704060000300d41d4103c41103020703e21500602100400c0980045140302c0c0400b40208 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 380322077 1250 380320827 380320849
    0x913020307031b0f02070e15040911060d0204211e02130e0607080c0f04090b0a05101206060c080307120605270c04060207030803040c0308031008060a1505 68
    0x70425640d40150414454020200159074019135110300c0201409880a45050b2817904000180c12051082140380c1e00d910000481c9130009072000304140c0041c0c6880700d18241e003115040c0d8800c001040500000001d40e010307004031000554280090b80d000782500000c032282540103002280c4ad03d0400126003100c042c2040d00f41d01c06440301480920000060007207400040440106801810511015550005690740c00680044800b441d00d014000102441d2213a0303c154810551a203d608002c4e40e00c41c1c00e0076005100c090441c0c80c04401c15a40140300f0111040004149d51400354049022446207040c118090b6100e292070386141c80b40f070000d60742c00c100709076030703060194543c0d102180700e80714088134a01c4040c010400910207014400d0000a90b8001818140c518000380b00800c0080e80c00030304881102d410101c0c250360783d2100e06004001400c2c640001d02700e8400081400704403011001a01c003107980800503500e0701d484082f07007802621507480d10701d4402405118188500e00e02002004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 380323327 1250 380322077 380322091
    0x3090e0c25050312040c1a070b1501021e01110406020609100501050609060c0f070305061e06030601030f030203040e10091b0c141e0a0201080c0c031e0c1902030c0609130203 76
    0x5a016607c0c000324059124030a2000030125020494208025100241c02e41100092001010303c491210000b55580381e03040100b5406c0202c0c00c444415204203511400c02c151040c0c9015075510740300d040180d944d017000c1e035141c920361003941100300004949218003416070748001c000c40e15252000c3c2c10000d80d900541c10300700503401644605002d900c4d0410404c801103100307001802182c43c000f040105001d000b140712000c183c00f03440800c241503502003000c2c1d040d2503001c40248005c649500701249107005940103541030203c3c1e9030500803100d0f00880050115904210180301c0d442407101c1d440c04a1680641d01000300351044d03420000298070008025812086c44101c40c9030108a00d0440e1584c0080001032007030742c11041e161003e6580c8182010760050420095609e014040d516460340c0c1d22458500807d100e050381c4c15460b080030002c0440302c0345200242125503060141c280741d40560a400c801701d1080c400c451103500c0e43d040c4130051380c01640004011000c490310005c500006035000034094 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 380324577 1250 380323327 380323343
    0x50f0c01020d1b0c120507060806041505090408070209010b070b0106031e0e0102090303041d060d050a0605040f080d0509010e070f0314010902040e0f0c150306040903090e0c2505031204 81
    0x10031884000d0115051703240c0104011f2281610f001400307005124068603240c0a1800c082c0000032240308940c040049a00660700e451050b641c605202d5858003641c24000c0d40035134440c0c0009980501300d0301505c07031140565404916030343d9542c016007c944006903d1002c12028401da22842c868690003c05c0c079885810000d8a403840c0c1c00002030555225820080403100395480500c1d04400b0721038081c0d4419019a0259082840c41d00d406d03a44600c5407000501484c1c644000500700040503400111903076004168545481401a461000d08000c03500d0000941c6400800d8078140c2d8002078400442e0400f2014035480c03811601d65202045e950940d450844d03480e980d104006803158411604900d500c4c2010b080c49285800640b400c00c41060701d0307144a882400e0008116008045c1181e800c04802c450010b010003552900760340c3c500d070b44c0e4015002e1200c50401c0021461900004016141005c0d03c00300c0130061001541c10440240720000c0c0c150390080c07120300c1e100040d01c0c12098005020b8400c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 380325827 1250 380324577 380324579
    0x90a0f0507030603382d060909151627030210020a080d0209180703020406021203090d0f02120c01020a2d1b050604050f0c01020d1b0c 59
    0x25400030348505a6010300000c0d5200380400c1486207550410340e15050303421011070251101c403500f5000300403e0018002141501c00801c040c03560304e81040c00c00311081580704122484009210940c3d902c12103a490048190f007000504000001c00c0300d0b111b041064903100300c95220110b51910b030004a91080040c002846401c41007047d403445000c2e107031260380a01d0580c0307508500c14025a460258a42009c1d988035004100006003170304141c2c2c890040700d9800580310784090001031904500c03400e61710360b8402c06000b80b203140d0360306030000e10945090703400301d4120303140c10b4100030905d2004a4065001b42c000c0f03035011507404c2c071401c40303080220171500c116010246110300c0c9400560049952441503980000c100d41e66903002048880304007030000c0c401c0110b0608459030409200d90442903000c01c00079102c000201000e466100d00c04a800070120388045c6400d00e489540c8013a02061105a84070302004088e107584001a000d500107141d5842e000e8000c4c225a0500c600e8180143c225440c01c0c0c8858 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 380327077 1250 380325827 380325851
    0x90b0a12050103052409030403080d0204120c030b01150203030402042f0a0f030e0d0c15021303050114070c0f050a060507050a0305070509151c021209010f02040e06090a 74
    0x1202d01a50080d8040c0604e0a098032182e18461182d0444082c80b104850810080c000c02005440440b074128141e240d90329120f00c102d07002403096400403c15030080d03503052001d20484407210019280300343e00504c003d0b6215403000208103ca49024030050380b08000140060515410080c99054000f101d2412038108040340e15410a5903c0e030300040b030303401041650505034010012038540105050404c900c0031080c190549688030815010144200103091104109001c402d003044440720280444d00c5a005808542500080e032005484540c28607220121488015000c14017400082d1590384ca918610380c0d07103048a101c0c201e0141c0e002e000d0310020402069041c05032621916035907440035607075200c11030040c00302c6501404c030504103c82481405200d1310340c0e6080d200b1486c4050b00e420b841d010180003880d0075500c00c07005000114004a03600302c0b02c0c0010800e0500a00283c00288a012418469075089000d5407003549403141401001c29081e0505448464000c1183d01001c140c80516407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 380328327 1250 380327077 380327081
    0xa020307060c030206071701150e09131a060a05190b030703020d0e0604082d0a030203090706110a0f020d020409050c010e091b0c0f10060e0109020a090b0a12 69
    0x350001020035a1044807000f09a414050b850f404a494288110702c040380d84228032001a050280c1410074607030b85944815580543c00d45038507000003c01c030718500c2c42c0511021090704c10b11a400ca8107103180e070200c6036804058a8045108080281840740c100b480c010400a03407103044d10b0100741c0700c08210408180030350b00744001d51281500d51000b50307481100002b000c04503444084031801640280051000040c00f500c100d800c0c1004101004000c48503c0701e1403040280c0810030345003111800078204a1040d0150095445154004c0690f00511fa40300030035600500303200d04190407034002e0200c81c40024070003903580b44403c0c005030403442d1280342a4085000c88180d400107503410342c000c0e101c0200d55030b4400c1c4061a1002c080e80c0c0c515441c149a101c074850b201c0802c103003840341e9501141341c40991100308028281c10850741b080300c640e51180b03850407000706290300454814102c40000442d50380c28034022203000110b039907a41e40f807941c5022410f028940010701c13900d08100640310a100140414 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 380329577 1250 380328327 380328329
    0x203041a090a0b030f180d0e10090b0c0609010e0a120c0c050628020f0318270a060f05010509010e011e050c011b0801060e0a0b0307050a17010f0311030a020307 70
    0xc6401d80000341081d070540041341402d0100c0c43d140780d000ba2524a0059404441c403442c1d88d9098170041104260030301c0c01e0300c1d66040b5400103103e140001c6100c0000c0d071000a201d83c021040c0000801021120003070540e1544440100a0614500c0e00d81980740244100d00341460340e405040702d0342c6030b942c80302c00003456944014281583d04518500c0c0c9005501e411000001e10742083c0020a144402c160003035032207002d00c03049004034801c10240e0010310745503141e022248280003620000170701d00e64049200580b105680b6580964500200031138801030700010349040e140705840c1c0508051521004644207081ca1800d1410458484040300c00000c140300c19090608481d100c1c0703920f43c84001080d0342101e01840b00702d02c008285580d131800c515000403101d810340e02545004800000f6100c04110944003983c801200910004104100103074800d01400c3e0708113485d5038031944800342c1920154102420b01404005202401e42000003400b040c800c0740310780401606031f0326000e0007600003e060a20f5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 380330827 1250 380329577 380329591
    0x91502010f0603200a060909020c0307050a0c031214040308090d12050d0b0a1a0a110a0308010501080f0118020a0e0303070627030f0e030c1e010f0203041a090a0b03 72
    0x8207200c4c00410700e03d814007001003403400fa1003081c0c40700c0c50103070020000e0101c0d12a14502c03581c005906000040280101e41d5010341190445115264918017080c445203188026a07009803103c3c10508003d00c92810318412985085149043c42e0840e103c60200c0c0c1e000c44440703684480b680c59928000342101e5444a481406c64540e00d0704c49030701c200e004051740c1000b0141c07481480c1c4004184010406810240901c09801c10b4041d02c40440c900d003942c8a05124012030690301c00c0d00141020103a110700d85505270751080c0d0319545c9940380c180f0a402d1110b800e0040a4a01c40c41c00901088140b650b80a412182d9441c60440180f40a0304082030460780113800996240780c4480100342c0c0503c0e03900d218224a038a180f0030210301c0241303403030003003080040d0100b91040111010f000380031690104103107200640020054206d08044420501c515005070032880e000c60a02e0b01c035481060300101c250703411600001308610141403440c10300c0038030754049542242d010303102040c003080e9112044081c62142039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 380332077 1250 380330827 380330843
    0x2150403090617090a08160c03050d030b010206090a0b0903040b2106120d0f031e06050118140609060c1e0c060315041a060711130c091502010f0603 65
    0x20614200500040b40c144811080f601040c051064540002a5269070719070020002c1c1c0d103c85054500200c0c0941c8030fa0050b2000b01070190100902c680494050000c0085440070410f8420400c010380e10741108461104041c0c0162009401040b1542c0c00c071544940000d09603032505454049289094206201c4080c840d645100c0100d2483d400841468204d2804c45100e440c0702c001c42c10b0a076440c22031000c00c1e000c01c032282c0001d441c0ba07802500318021190600a1919049640d503170035600822242c80f40e540058041c0c400c1550345004512004196410103440d6950001d00c0c0c418414107030310248049400041c2006a07141400c41440710715407641c440c2d40302d01340800700b00c0e640d03910f001e031060041d51041408006000102c03882792408030f040720341a44c0108480c44002c0609200c680c0c0e040c42d00d60004800141c0c0c0c0f080029800f0f0300c1c3c6040c0d00032100c921403441c2c0c01c01c55004917801c800744400807603661031041c4510f010501c001903c400386440040340d11896000c1c1c04007a1145a4070485440b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 380333327 1250 380332077 380332079
    0x190b120109060f050c0304020603040809010c0c060503060103060b04120b150603010f060216150f201501090626032502011d0102030d020705122208011a040b010215040309 75
    0x1103d80605504948841042ca08500740f5030000b801038070010304003c081c0180024100c402c0d9015190140e81d5a40202e10f0600040d036819000d4200c1d40110380e00743c0041e160120100306282410191002c0e201e1201c081c1d404c00003141c0d00c590303020102070300f01c40400711000515051503441000440c083d003194400244030524101e00645000d0b42202441603c4295010a2125044c14582e00c8100000c0e4a40400040201401a5100d4280042c1078000359000d04405208403000100600034020604c41174000b130baa205510030071110b00b40546419540d80d00340c070a4400301d08900e41007840d0100000e69180c40c1140310741d101000700f1081001c000e0100103440405540e0444009028800f840c101c080c0e0340e400c074100007900d81c8150f05403030300780543c00721300349003480303010040d09080c0751003800703102d950b0101044400d410340b5000c002c041c0d5480071070b4004190041c040c0188900104081480c501c41c0c0d44040c100000380080e000301c5030441c801c420031621105100c02080740030341d0081d1915410a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 380334577 1250 380333327 380333351
    0xd110a0206031611010b090402100e100e0102101b0c021f02060118020a02070302060f2208010605030d0918020d05180d030b010203040e0c0f07050304090f05190b12010906 75
    0x4504c54042030092645440840c0e070381a2154011140e0003541101c00384109016400c0960b60b08e4101c09500780c02c110000c5074110150340000c20014000070903000c5688a9150340010381c2a20b8100380310307002d801c00044407804024051845001024070042046811940140540c1400310400d1881c00059200000400071100c0407000d480300da5440880070341c900303940134001079038509480c80020b018407000a0710031107610480c2c0644406002100400000a03403019240603840348074090020303103510384500010140f600080c211000b40c0b144e00c1d000090f83ca001a91190350003044051100346400b0421890952040e20810f48600211404a2132030300f4039062585c44c1980b108001001d1518029820070141c0e000025103041b140081c00c20109561180201c041c54020411004aa00380111b0a00d08015020000d40b080c2c900c074801c10004030102200c01003d40f102641e840ba45c0b403003c0103051403001c000f80c1011159110107170a40700494983d81c80c1c6801c4962185055480f9036480c0440c0c44a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 380335827 1250 380334577 380334587
    0x910020303070e1e090702030906120907060801031212060e1e0a05090a17070c03050604061109130c0306030227090703020f10020f030301030b01080d09080d110a02060316 75
    0x4000c2900d5083c0c0c0b42c1303490074120720104444404d02e44103902400c002040300340300f04100c0f103041d08040c0180303480310500103c0750320402081d03030039403803500588402041e01407042030128122904100340d948014212041520840343d80c0c01640d0816445e4040821214000751905004400b48816580c0103030a041d00100c1d10400645008003940c10070090200d0b222001803076085180d00a800c80290b040c3c07402c0c08940380c1c45140d500030403403012500000b083c44404940c441c8140e000380700600050350a907a050800344650360f01154002211400740d20401990303070090f8541a4142000507a691f107030f800050300481042406040d56050240d85419074898a1419070403801e500000d201060440d400034030b03d110000c49550182003a5128001024400c1102100300021441030301c0e41d13540c50703040031a035140b024001d4008903c0b403840b04080c600c0c4102085000c4a1120780a0502103541103022a00704958215400c91881000d4003d0003680c0d491004500401c40c4030a010a4079203078102c007030302c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 380337077 1250 380335827 380335847
    0xb0a1e11060c0a091e080f0a120f030906110a02010b0d0803040222060905150d1109090f03160501050c0412121b050d0801080c010c0611091002030307 66
    0x80080d851020401440001003860300030001d03820746503c81c8032100045071108100e90090307010303142c00c21384441c4842c402281c0f007041d50001400d031187c85020600b0305075a59458600100704d50401c151021165114001c0020030000310701c0d001c205608a62034220958100c85080c0b89a0400041c0c0f612840f602403165280345502034400c000303070144030b44415003035020040c800ba02520300e804540d0f4030b6440c00305810200b2484410200605611614400c00900c03007125441000700403111050f8840ca40194660486035101001c0c804581004061142040c0040c0c484c0d0780ca0700c00d10440460010051002d0034003050380c0e40c8014162506820802d01303542002e010b0780c441c11401c100511840140c10700003400303250080640d03140740c1c11084007100c54902c152103d1a9000d610b04820b810060701156590f40940d49648041d01e5981f5143c00075140d070241341c038081c042000702100c94001800c5400ca4000300200311a01410b0014400101c5d1004104c000ca000061b00b0020800801c1d0f13802000140c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 380338327 1250 380337077 380337137
    0x3030c140a0b15010c0b010504090f050607120b061c0903020c030f2410060c02030703022707031b27080a03081003020a0501031e11040807050d0503160c0b0a 69
    0x181a161158646009410048c0201d0340a182ca94042c13905020b003000f0210552680801220203501d00104010503941c500d100070880e040c10415040b005141000a441c0360110304107050a9408603210050010305020401b00c0540c0511451180c4d69501480042c8143c291140a004141c0c140000781087d000307642010800e101d584814400f40b849058400340580b0703c0e90401a50035a40741c00003a00d4100540d0000b948020012031a98500ba852404000a044000710205a50300d0f120f8090b000e036242c8610411450800303442c048680c620401c01003100e401040c004440654400d85200c07108800c41d00015410b90200e00483d0815501403441540300303206c601c42d0500389086900223014510284106410191600a10b0740f412044003006015400144c00030016240c000201c00c106030807500c1004583d002d101000541402c0a41e483d051555102c0d01031440d1212141c620040e15030548420798901055400120742101e11030001c3c003075001240c440c0c0300341680c405050b130000c202400c00e00f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 380339577 1250 380338327 380338337
    0x3010603030c0f03171315090302211e07140c030a06020d0b030d0207090e01110f0a0504031401090c06050c0a060f0209030a0f02032503030c140a0b1501 67
    0x800200c0d82c00341501c49410350040041c0141a80e43c28111400000700514180c0c00b100b0300d050181c03001010b210401000c1c807803106900c242c0c1c111b088410442d070400c0d00103405600805a0b503001e20301010308a0040d0710284041d94100482080000305e4080031b100c40e14a8104005030070003c4c4a044500000721100490040c10224400c0b404641c40d0030744240010646a008250410704600c2500000310452015045906200000d44000e64554980c40f81904d098034058050348107842c18010761040c1009001e01500d4500140084c10b010360000d100710302000411310022001590f0104420001c840090011400c119036080080d40c1e01e806038060801d00c00100814071000102040083c00160012000104011010341200c06407184119050341800f5003940356080103048500304064a000303408882c10041e000307a43c0d41c034410500000c00001410071004000083c8103007802000d4a120300c0310411078550640303810f0701d020a0a81d0886407200100104103e981c2c8000740c0c9421a80c00b440c00e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 380340827 1250 380339577 380339579
    0x7030b03011d0a020f1e040f0209100c0c0b04050105071e081b0709050402010c021e0a0801020d0605040c1d18090d120b0a0603200a09080f010218130608030324030106 73
    0x2990402028007044034055622103402c0c142c40b2200754140d2b0100e0001600910040e90300241c01000000056001c54008070020000300b5491424001e84003500c0b010f031075061600d041d584800c0c001038021900c81c250380072110720320390024420740003400f07500100c09500800940310035115801e103502c9803c074119561400c0200700160781d01ca20160300058040d41c1c204d940c690840d1801c081100c034002155009451880001010001540101641401c04c001004165121000c110660f0a04030b40380001401502003440b10002043c6160103507440108001c0c0c4011240901071203180003142c1000f40c030340103400e20802c1036400503401000c01d00103c0003008040b011b400002c1c00c4007980c0c003a13102010360700d41071800b028100040d094407800e80310129a8661902400080410751070780140351082c042c4102d0036a04601c14006d541c074002010044400c441180710034413100c0104448801d0103981c6420f030004000d84144000c6000305180300340400940a42041271081c40140c3e0700303030b0380240e02d8100 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 380342077 1250 380340827 380340859
    0x7031a0411060901120902041508030a0908190b1f0b04081006031509020312180a0f08030d020a0e041505040b01110601060507152a0c03020607030b03011d0a020f 71
    0x100c2c1702050440c8040040c4000d1140041401012103007030000209a8004020070444000400342c003517101c080e961070780b0b00307605d03032942c0750729000184045581e5461922003200000c0310805c01d21751003ca000a200c01c15692600d081d91030902903031042c02c0070710b40000c0a1244070300170b1000c0007030f0640440703082c0310091442d600c95401146428110045640e04c192110441d542400460046028000680d0319a0550450382c0c136040e003c08542d83c0b00710a42c03200000c100c3c040344181e108a64001c1c020303604000e070896501010f5440028044108001010745200607955840340c0c5010090300385031032082e04d003400103204c00c54400ca4106810301690b004400c1d400c08002070701a065428501d01280c80c2c2c2c280386000490092200b80c1c89944c14100034102c1c40700c3d02d081b01c01c00486003051030300c003450001c241c1c4c00b40c4031040c4088024005030820000590b080e402078003c1203540030090000154101e01c0720780120300e54001e980c05111a01324585401c1945081c200c0345c00712031000c03503028410100080e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 380343327 1250 380342077 380342087
    0x308030106080f0f06060d060329070f020c010518031905010f1e09030302040314060f010e0c03070809070911040f080d09061b1406072c09060307031a0411060901 71
    0x410046c450700e80040c040000e42c00c1900181d000310f9020583c0f01680341000740b012840c207160141c24480020001c0098a2544250b41c0c61760b0320070340c9030040c05040091800440e101e5005040c00d000700c02d41c007003c0f08469101002981511054490700d81810241ca1502a00750707440f020304128802d0501c80322721101c00840380c0800f103440e000d003000030301001c030381c5000c0c8c01a003d00c0d40050551844500141000b40b008108a0f2191850002d44d404d00e0b83c039190b450400400550304030307904040500000b1141406144000c2c1c01c642c0c91012110541d82d6850610155440c9407452402c1943c003040801c2040d103142c1d9410081e241001c0541400000c40600621407070252183c04100640e003214a00c2e114a00c880030003145401402446119940390b040b20380e219001e0b41c03108000b4000003503a20075105039220380c1c7c0140010180030131b07035614803804020041e030740540300d180d0600480c000000010354403c8001661454080080c2040ca00fa0030014004a031003c1180d000d00410822a4000e84e449 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 380344577 1250 380343327 380343331
    0x10f0905010509121203010b070308072a1a07120b0609031f090501020409060e10081903030b0907020c090f010e0c070303150e01090b12060c07050a0c0308030106080f0f 74
    0x1d842d0302d004c2c0d1300304810080c40d2081d1501c00100651001001148074501c1d58024165903003c3d841e03100703160302e03107000403620380381001c2d80322808a07851198044880ba1080c14504000d0086600d140e2000b81c14000c80710204050300d1240114600f04007590030007500d4020419002d0080b92103c8c1808101e0002c0380e16240300305012070440102e490b2030a060010f681c07118003540d400c18000c5491700d41344c0100780300800d503d004450820301342d800054030140e0380b02010001d860445000d000c2c5488510700c03843c40707903603d0302089060540355141c5c4070103a2100d00503648113030219401030014a6508081c04280c10024052543c4d40114400521030802c0c2410300c0303904045c010100a41e204c4103400c04800a080c1d4483c00040486104e42c0040e0741d802114040e030580700e00c400c04012a000f030710104a0721060b00d0440c0c920303a0304204009006022840090700300c207805141554401005ca917200a81c1074055002110170034004401403160130744c0042d403158005286044103026003488040500c0c90100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 380345827 1250 380344577 380344579
    0x1b1603030506030a050a060606030b09070f0e060f031303110303240616051513110418050d0807031112040b0402010504090f09050c03010c0f030b04140403030209010f0905010509 78
    0x101c001180c001d4a08100d401150380d00b00341034480c0c0c901e0b680380c1031024050600c03820001909080c2d01c1c0f02d0910341848070354047d41207500d401e4000000c4240641c0c1452104082c1075000c0d500784040401522254011807107046c481c003510744040014a809031001c0038644050410382e00a008020154003c8007002040c0080401074280101240d00000c001d4441c61031450219141c242034542003140002c0c00d07680d4150081c8102100742e44880c00346540400403c4044c00c104420041501c490030242d01c881d01641343c00c84d154040202d5030301c030b01c1e10f0a02105207000c0025015010004400d0345441401c00c0c0d8202144403d00d4050318442e100003441d005080601030300200301c080b030116030040d811100140b005d91824804101d480106034003e081600096841e400351500054040c6818441c2d000c1c03c1c520f64850004001004c1c800710001d0840d40d585136007169071072446860102c0400c0341688114480d980250391024035400040240410b02507500c14000040020302860ba08901503402c8080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 380347077 1250 380345827 380345831
    0x1503120c0d050a301d06060303030712020306030102070204022805070809010f11010f2013060c050a05010929060a05010c0323090a0e101205011506081b160303 70
    0x80e1113800c2c0e40480302c900640c1c0048030b00d810040030000c001d1861400d03401100c40c0c159101507807079030b00345520f0f48401c0b02d400c000130b0715808425411660a50103107400690190006003080c1013036010408a82c452545095100c0041440c4051348203200089118012580b600350300b002c0b160390314407429001e0301d00311906100048003120016031042801ba08000003000091100c00301e07610f4250020141140c1c00a02e11b600d248000c00d481c1034407c2103400210340754000a8000c0d1030900229620350f44518121100c3c06582a0b0002140090251200d52800b031414260280da9036101540c8110043e01c0740700c10120320104101850340c8200c0709608503002800c0800b401c03407103031501701e0300a10b01000618545120850a804003907003007000d03240d500d1050392011801600d0340c01079401003000b102c290203000c044220610206007079400050500d44584000f103030295080e000a0f4146c0c4440e0480d50020304808100134031240001c4c0420004580d02c0c4405141800c080000e158006c0c01c04d4014043c95 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 380348327 1250 380347077 380347127
    0x1e0f0d0908070f08040906050d0203030901030c0c080a02030406091d0a020a14070501090b130f150f0507030507020d09050d0f020f0d0605040501050708010605070b1503120c0d050a 79
    0x41c004640c152a0b00840104101c451840c291486801c58007684044c1c40c03030044049981d003001c0700401c003095002401141014071000c01100130301240b21744c288c104400100000000340e620400303040d02981c0d0750042c40e15541008001070603001c6540c4a1805980403080b4079100d5014101c8842d0004807404000d40d41e200d10702c0302030320380c403e07540c0ea4146001400100a01408419401001c886216100320703050364440c3c200810070044001006000104401100c0300060940340c0032246003004030401203600200c0a03000c0701142c0040b51606c000c20303104c03030130404119414000010440054141001224182740c0490804d00d100100141019803000003d4150360391a40e00c00c007a100010010034031322100c1c0c078021002d40303815141120076600740400b0481c1a4064a41c56041e1202980c507203080603929102d0a84199010f04410003c40070b580c02e00c1c078030b61000d0006104460209039055950880352a000386001707130040100003040710500c00c50542d10b52140c6d40481c0058030901c286808 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 380349577 1250 380348327 380348333
    0x1e040e070e0f060a0e090112170c0c06040e0906011e060311090d050a06111224040e1f0b01050306011d03010603230607051902070503070303051e0f0d09 67
    0x10060240b09203520036030109a418489600243c00c07150640f00703603000342080e41d039800a2014051900f00040c02603801da58a1454003407180050400101100203c0e0003401c603000102c0c01c0c580c800c1c0c1102e8050b0501c4420090102000c001c0e642c010000101c0440d10800650031114880700103000d503004058071050500660803202d01907504807800202017000c82e4410749000c99a990160f442150f0320b03801d21507102140e00d090310980d41240400b601404040d074401c0d402d0880c0c00f90003050014800c0710104041d003161204e119020400d0b210780000c00c541c5090030020350704c809240782c85c59041e5040c00074180c405d980c08010349422107000e0810004074401021500da0307295106c0c2000b0b8256207000c80004c14404180b03005040080d18020402404841c5a40240c5581040f510b4001081040141c820b02c1014840315a08001c134a01c15940902e860b100001d0614200d540250000b400220b06001041000c44e880c0e01080703140922686460000502d6000b42d008800301b03015101c2d9101d0b040028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 380350827 1250 380349577 380349589
    0xc0f0e190509101703070506010b0304080d09080301050312390303150414060a1403070308030c0c061810050406020d09230703020901050f03030712051e040e070e 71
    0xa4040241281c10610b07080748061000034143c45140c1c000c18184034444c280000c00b0045400b0190414083c1550343e0138004000aa0381c4090401c07680c03000704000000341082948910301065120750700150362549030404040c81c010400092072000c500812048244e6003000b800881100c003604101644812203020aa60044141c000c28540740000000c1100c440244a46400309a43c100c50400004002c5000c00c1c15800781119080c1e0401210941030040d01d110000190328080e0050444140d1512503817819056081602c1403440444042344030009080e0501c14070f42d006070707498004185126400740c865039491840304241036069903a00410f0a000c40c5804403101c0d4075401d9800c0c07081509514150691400c0d00c1d01406020900c1d56468a00010100c3c26400b120313001400103160380d007013030b040000d000c03210080c166240c40b0400c1102c00064859810f291030202c1a2140c2d070b101e080d01040d54001c004008290341489204200c1880f03500b074040384440e00300c1001e2a111054815403804070324 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 380352077 1250 380350827 380350829
    0x7090612060c0e030607210e0309040f02090d0b0a0605030a08180112060608040b0a0b01020d120605040908070b0f0c03180c210f010507021f0b13050603010c0f0e19 72
    0x18041c0144403c0010756500007121f40b1844029150b02544103d81803400001c80741580c14040c903580007008110307080d1a1a4000d40c0070f00344140c1e401131030b1841000028000810781c010840e0041500010000c0c0320042d441003034010310080c2c024103400b08150741d0707a28191040c00c082c00446020035000b100d0b280d10445542d444020280d00170000280c81d010040e0503170008a03011182c00561000141300c6441d40e001e00890814181c00a06200401d400156040000101141c510b607955450014540e52540590a0303514004c4004039610305041c186030b0300c441e00007032908103c3c00740c1d2002d01140c0c91050080700d900118660000c0e56424102c80500d003801d460a071415131004034940c1900000c070510030380e11480840001190350134038030344d46e21600b603d004030b6080d00075801003a81805034188001d2404180808504006400c80c14900040c0e02054000c10041305d280c2d640b0200b0025080034400c0c1c40c01c4d21894148403c240070346010040600e140e0303607240390150303d00c00500325030403840450f524 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 380353327 1250 380352077 380352079
    0x40b1206070c140a030507050105090f4303050f12030105010c05150117010e010b060409020f25020108060607020a05120c030111070c0e01061d06070212010e07090612060c0e 76
    0x625504d1050070001e006030004e41040e903080d4640804a404000001580083c1c00c41c628040c000b010140c0a02c02010313800f5110740c00004d51880c89580507460440c54903e24079074400c00c100d400c5415800c4c0a0b2514494500032015580b007c0e5200548405000952341110001d1078a810801e0907071401e43d040260141d00580551044000400e800c010003114580b0515100020010800d052034124261103156a01d00c2d0040810001032041081c241c005110354000c02d2080f40c071f030541400c06114078010040c04200301950900740380c000c41d030b03200c42540d0f0408800c445013418580325800141c08014030f40308551084103685103180c40c94900307010303036529080020000c20a12a541d111100c0e15441007900316643d802240c0301090b200c5d404000300d07058078580d03951810000b0310412912a4603118007102540400244100001a40c500f91243d000d0f2980600225050848003040c500d80111f42e04406405810500f042c4031950344402d806044075001040401e08400f008016207a041001c902c207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 380354577 1250 380353327 380353333
    0x90a05040c080712060b0702060702242208060a0e011b050304020306070804080d050603070b2a03031b070c0509010e04120804120818010e0c040b1206070c14 69
    0x181c00c190002c2c4018411a8540c9030780e1003851104820b0405c03a00d05018290101c035050001c1800350520340c0140128920103001c421240b82112501864511101001b02024000003020095410004040201c041c1807540d070000c03050030010241c0e03ca8034000c2003025a90b95804504020803c25080f0b20009012019910580324009900400e00d0780116000c0c0d000f8417031180882d44503880303030f08618800d5400c00501c9041003030f0441c0007030182c074010f04040d509d48150500819040d0101c4008c1203011304045c0c0d503c41002e5011150319035040c030010070300e0080d0420b008000d402e05454000700310400c80380910942da403403c0d15029013110342c56001140c126120800100c4c1c9900a1909030b0700071405120314254000c18080211042c1d0400c40c0d0007420250011848400300380503001154002c03103101c1140841c004414111070031607000b5120407801b5480b81c00c0c3d24550342403e04c50403110000948800080b202002101035032000058004c1040080112150050040c86401859111120016 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 380355827 1250 380354577 380354591
    0xf0509101707090e032a0a020406060503040311070b1b031b07030203101802060f0c1b0a0807150809030f0a090e0609190c1110060f150203030c090a0504 67
    0x200c15602c10043c002c584025160020b03022900400000392810044080c0c2c2c40f29018003004030f4122a030507a080c010546200e01c010000050740c450080c0e1025040941c1d4083d1a841c0500b0010304010700e0a0710103035140c00c109000d016041d40c8408480c1c000c0080103030480752900b0342080c640303584070b03803001c200c81000302c03e5041080081c081080c1089a0080701100c4400f40c0c080d551400f00d0f580c00c40c903015503064080507140103080041c0640740d826281c5080e18144002001c040d8100900d28403400b0810848019601c3d480c60410491005840c40f0002413500505204040f42001214070000083c00f02550004245000410440d09041c85c0e40f02110780340c020b60b1a002e4610b800501446803240e20309000120a800d240c081c0611903036030050003a46000a41001c4d400405588600e6010000c0c1070512003030803902041300740000f030329078040040c2441c945090070745018820b0b0050302d03c03803820070071a041c0540e000040c0e0750890b001d80c035816694118200025583c01c1136520032a0000d0034a50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 380357077 1250 380355827 380355869
    0x1030519050414070b0c060114040209031b03010c020f1513050d0c030905060304021c03020313030804050a05010e1311090406090b03010507020d0c0303050406021623070f050910 78
    0x1007040085084500b1134612a07107441e6400782070302a04184108650041d8010044040314480e00e0030742010240006150a2030400130905050204403034130300170281d0a030b141031181024824a6004e90092000d00300b05240841c50710303160303007142404084603a41c41000c580458004102078400c59030140480c1d070000c50b003540c042d11030094980e00340c0c00300f603403d07000050905020045910440e402005001d42580d904040c1d8040101e0080550452000380000c4903402020712801d00514000e10199480381d00d051301300591031401d50046410042001300790319568a03085a440701301c05035640302003130b01310014844964a018696107640e109050101c00184100a43c2c0703e55410001500240303d9a642d4000a90341c2d501020303940c600046242c0483c002003072090740006e0300507104c0c0ba005464501e48048440020f904507000b9070f010050300b0a145000300040040b01158072a08020b81411842d00ba042203550b01c003441001c1c0111007000c006a443d4a441444801900c50b2010880560350403034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 380358327 1250 380357077 380357093
    0x90a0b090708070816090b03040c0807060e03070b040f030209040f050d03020901021501031203020c01020f0a0e13050103021008040305090a030b060f04110405040c0915021605190302010305190504 86
    0xd91084046404480403038007170540740e403000480e0b00c243e40f681c4001603c0c140e500301217030303000030000c0d0380c030780030418000c02c07948428000100182011341d1000382c40d49102e0b080604050036035100d814121010881000145007000d400f504590701100d2046142e5103500b0500d0110006984c003c00310700501c200004036a8042e0702a01c0040801e0342101c10018a580d0351440014082c040684802e0b84007000755440f501c80d030010000814290700150902ca2400c10161082c0c100700484408030f60410b42c294458100b400040180303000580d004e001e81d514540104404000491100040055580c00207040c980924225001d19001a18031402d0b50307500d0800000e00602911b02e50300c1180f080c00140c0c5c05140c20700400f40b00303550500940e0300d00b526120812004000001800c03050203541c12000880504020b8600c5000c003264002c1c03c0202c1c203a4460710a401ea1603004a07100d000c00079000350b00b420142c50184140d82e42824005140e449004e000d010303c80011818604203030901e005c00007080500 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 380359577 1250 380358327 380358331
    0x32d020913060e0a0b031f0b0109030f230601030c0b091c0b0604110c07140d081209010b040c0c171603030603201e04231e010501020309090a0b090708 66
    0x680040207817640c10020561500b030f490a18040c0034083c1c1c040300240c401a1307800305101c80c00c141001c814480c5e9943c0d81c0c5035400354001040d1440070340c1c01e02c90304000a401d002e40346240480d001620302507065075610141c0032018010300305002030105070b448940e2101415042442c0c4205c916461104c1c09150141b00f00c0400c40d402c1d4012070070001c3c41e00d000c0c0501c4040d10070008000c005481c0e154140100f000c85850035842442c0c3c00000302c403500010a414500601134401180c070007032864980801560309542c81100214002e6140400154003154410a00b4000640c402c4000a402d00b00071720100131070042d00c0c094040480e40c500300804054141e07000400303c130301c10700c1b00300f05002045004501c46005107610540081050641210303e00f00c00303550345602c240c01800050241050300c1c1a02d80c4000364052110108514403d102c04410403c0030181d0348600380702090390b25030400000030745a01980e030001d4009c0a00d84081680410390f50480c07403404101802d41035042c03800c00f4004080c01d0f42 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 380360827 1250 380359577 380359591
    0x51603060f0b1b0a1202100c080610080601020c040213030b010518011701020c061509061509130f1b17040203070303260403050a032d020913060e 64
    0x902440001c0c80700c84109624200c5149507003580c01c2c40742c3c201900c0f050001d88184502a13004580e100800540c00001e01852541c0550050110182c1d0505050490300300a100784240040b400030450035541e18004040b000c04c903132920b415030b51940c00040c1e25048051039450b601c80c0c0085003200c103401e5035812280449009880c000c0c840e9a894061024110f03440c0d1903036011440c001d00501c06e85649004010b1544500c0c000103180290445480d801c061080d6000c2c1c1030385980200e15004c03480d01c18150f40c1c03c41c1c002c41d001480d6100404203240035215030542e060080b105a8500000d42d980c0d9448040c0c52022104280300104900118800c5000c1c02c0e07030010040788124041042085a0b0944a482035501400403c81581540c41c00e41d04000e810011510010305200c1010155100c0c0c1c1481d402a0300c65218a61210f10300180074064480110066802281c0740c0c0961498502032071602800480101c00143c3c1d6030342940208043c400e544810007001030030110005400710702c201000b0b00c6511 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 380362077 1250 380360827 380360831
    0xd0c170c011d0607170705160e07080103260d0c0201110418150503010f09150b031f060803030709060914010f03050a2304290106050c0c04051603 64
    0x140e49401501c10307060300c166050840060210b050b0060910900500041740115150720360408040d2000d101c0354440c1d4411149a000450071300d800c10f00fa01c0418000d032100188285551600e89002480c46205110103402c10540361b100c1052045524003aa405420742d60007103585218002c50440034088044880c0010740c80c03c4680c403612002042641c0c00d864a0214000b2004003807c01030001e0b106e801000e40e00100c1c0040d000a00380c0e0240f03c1c0f20b454928249001c611100030341070600404000b98849060307282400c0c400c0c052a40d01044100c0b0a41c40d51301401616401d50340742000810494204100a1200200380100030b9000700f07800d8101da525984080f00a030315842140c811314210a01c40d40071070320303105903540c1c424025009150b108421040c00129421940503840e030040600002016809503a4240403d00c148102d012013081c120442c050000c100c0c4260246985505100e060308000c004a9400c00720310f001e124564440070001e0061041342045802d0944d203640400c1503101081c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 380363327 1250 380362077 380362093
    0xf090f010504030b070f12060305060f0c160204110f04121103120307110f0d03020a03050c040308030f0901020706060b0307020f07050f12070806070e03100b030a110d0c17 75
    0x141c490360841e815264071110320915500da903a4103480c90f0752600b031b148040c00304031100c40011242501c40c1f03030010750040c4010310707003400c201c02580544480504400200c40c020013140c45510124074180f00c200d941910002010400f01c80c0341d0446002d01c00103000c41c00d6000074000703940e8441ca5030307400c4034a0050b000c0581c0c0c0d4848204241d6228400001005501418400181110b003d10f0881c1a52100c1500351010000100041ca007480c403000c80c0e030780c0425030205d80881d6156040c855181d122800c00c104603d800e0458492010b18040100841c42d900320b001c0c00908080429019201d0160340160706201640d1542c0700c158040cdc1080b2010001407003042c03410007041d40001420800c41390b02038030301d008c0c0041b1030060141d50f0464241c403081c540303c1c0c200300150740c2d2820402c1d00d20400c0940d0303a601044810100301414907207601ea0141c030440c1004144010f556000c1184595941c1c0040c03017050f054800b2002c02c6842403550b001600c00e00300c6000001701001d0f00000e4030301408134038040d80c40c60303 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 380364577 1250 380363327 380363329
    0x1602010506010c120e19140604030503030f0c040e04060219020102070f02100c080310090e1c050d180b04060501061107030b070302040b0f07110d11041a04020f090f 72
    0x2200115480c60010760503210040120710f0f511052410000c451030172080119007078001c194805074241000c44403903440103003013140311001900c000420f98100c902618007499030311801d0390b0b80406080458021546000309041000450482d0300800f00e64111032002e10701400d02d04000c2d04208100c404607121000c464103024030610880d640b5641c000110202c804094007448040c0031350416080030300550b00300b41c5000c10b00705406940b16125903100d41c0c00c50381c14410700340c040e6000c0c60710420842c0d111000e030076524441c00303480240d04044c034079069032603030b44000b1464060011080f18481801288101e40c05001c18610307524841c50180b1000c0c0440e076660398048515040160001d04070350020441031001404001c01c59801003001d00c0c01504154403000f00c0d404682c403890b034070a41920b0029445040101030b00c030340300d80c0341400c9641c400340f02401c0d110840608030707c1d41c10901c19940c5907090308810798103081c8149000c001810031912070032105041c6c0501c2d031201c00040d1242c010980c5c07081e69 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 380365827 1250 380364577 380364581
    0xa05060919150504080f070b010518091b010207050d050d0311090d080903011d0619020f0d020d14072102041d0a1103040f14010b01020c060913090506160201 69
    0x103200d80c40b10041103105140c4901a0081c1009041101d03c0002081011707080c1404102900c0890b0140d500c08003194580810800c4003282603110402d6404000c1c10849811001b0562281d00d94000d011500d800c20b42c140100c2c03d00e00150400c81d1702c201c24070303548000c0c040c002600d040c1c81840c0340c504101203400c26080c050940181140c141c0e101c512006007000240120000c0c0050b1640500046000c0368002004501c4440f00c0307080740101d5200e5020441d030b1014040716040700001c030301421032600101c04840d411901c5100b00c003a540640000d0141310214083d4041c02c1018a003984540c014113140d00003e0001e09400e0f0008000d0254001c141041c64451003114100c505803010782480303401d20065444110f41c01043c50400c1c650700c50a208a10540000842c421441450712180c044d28504e841401c654004030880c0c4980e2410030700840340c1e41c0005015002043c2100c43c0c64031100c0980024181d103542d07034003400c0a00d0803d5450f00421100007034040c062820000101e82543d446403003242 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 380367077 1250 380365827 380365873
    0x30706150503251401050c01020309061b04030308180a05060c03010f0e010b03070e0a080102070b1e0f01030221120a140a170408161a0106020a080f0306030f0a050609 73
    0x210714803c0e84020041290118039508486406050860628401401140c22038100300ea002c81c25070040c1e420084600410303004200031983d2411640e04080c11600d00501c7d60500074075682c0c541701052500048031004008006401f54040201d03100c070b142c40459042d01e03810a00c5aa14030004240b00410403001440526040c2c8200c03842060940d074450408862200d10b5920454000c0d011401c0400c1e101001e000610609001c3d0100001c98140420000001c0c45000c0c680864403040743c061110040940b17044a0440b42c0480300b948000500400c004071145103c1c210108512a4494100e8106158006442425455250036180610040d0700d0125889500700c4100040d402501c0c8031181d408078004d213034100e80501100b038205081c80d6541070301ca611b110001c0d60701100b0321075817141081c1d010384442d02400843c4060400302890f60f0701e008283c0140190fa618010001c0001040c1c0e07102046a108078140100c119070443c05e0301d0500640301c10055800d1095070155810030500074400c010961 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 380368327 1250 380367077 380367133
    0x60303050d02030606041a04050109090506010509040b31060e07051b0705210105060a05030c011b120c03020d031107060207052508010b090f0711030706150503 70
    0x6850441c041803040000e52004001d241d10590500001c110303620082604114003c261010941e200c4c1000d002510400039036000001d030794240010030a1f03591f0b10506840e151042514041488014000010441d0521504101c4281c00e03e84414001010f003080c44140c0252030501002501d44658520100d500101e4140011034010802d001741480a40b60981c0f120580d0401e58502548400004040300400a404924508200120a4007100a00c0b030560016421908071001501e0500400e440e1981c10754020306000e010424841c9841a07143ca1451542d80100c1640c5100d81d5020041d0044012600c203600500c18090041019030007441504100c00200c58bd00e400c02000ea84e82e100603612078401150385014520f00c41c1c0c9062007a40600621b80b00b41120342c0c0400b03040104880c01c49040a071214802c506c1d0506004480850f2408241c00035010326100d03c210410b00c58491551244010040290389040840c82039594000b00710015500110207442e540613550580822103038644c5103070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 380369577 1250 380368327 380368337
    0x50601030305030c0c01050709060e0f0310110c01181218122f03120f0714070320010f020f100513060e0c0103060b040e010501030203040f0605070f02060a060303 71
    0x50000c42e018801943d4080c000d9620945050386890b0000d09543c4240e0f56403012900000702400704c25084042c81e07105040640702e0305072640e040e0000950f2880760707598024403550f0b038501240c5800042401c41d13081494400081c400c80103200d400742035001140d10182c441070818080b0b8a80b0600c6036051401c09481645402912805e0960f000f00000450340101c0e0012550030313000072203080c81000400307850f103030910550490607813174207241c207050b02c60b9081240003104100800d202d94244040d60002c40d004904804080c01030004585000819040640070812280c00030342c95540341c2c0303041c0032111000e0781c81c00e004003c00d81e03081e80d032810600d140490642090003000c403039084e50f52115900070b0310b07104881d03200358890310342a04541c1d50304905036168005903038010095816004140c01071920003003841c60b091606d201c119035800180581410150000040390a210300741140c17503a03854020b80200040e06208101400ca8007000d9100005030003840006a80c5004511a090440e9095224 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 380370827 1250 380369577 380369579
    0x40303030507050d090b070809030f04030602070c0f03060603050c0a0501120b0102010b1503010807050f0d140a170c010b10050d052d07031812080a0603080d0f0b040603050601 77
    0x1600034080040c0b40104000c0244868401c0b1002c0d4069000d1880c0200204502c50400c080014800340c001851000d1540c020080d0500c58809881102c1c03c59030803020041e01c407040751410304c0d94144541c0c4803054961040001006004080c0d1003641268803900440f40f40040700c5092281c601824850b25010500b09801d101d034200003a00412100081440009450350384200001c41c5810010510121060b000c4014000c4810402068001e094100c031400155841d2070000382409030f054000411025400c040c07214400b004000300340704107900000d8101d542c684ca0400d008150042000781301c941d807c01c201031a090401008600502045a440d503103041e54429070f02002c2c02000d0018034000348200030118000d2514108240d00301005200402c0302d05041c04010280d03071000c040e00c0005c428503c18800062814000000403042c5c40c20030320495034a44080c0c13802001710f54800340c0000d6001070b0312011400035078014400110744900400a4404280038001240c00501000301250b00100c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 380372077 1250 380370827 380370833
    0x8330601120b091f0f03021c0618060b040c08060f060c0a02030f010c02060f010815070c020d0302010506100507050706050318010606090f0905070f0302030601020c030f0a03080f07050403 82
    0xd00221207011407004280340d0307912400304039452411110442e10400d840080c01a800748003d040005144196100021178155000640241e00c0c04164000c940c0400c0d280c0d070304000740360b0000094034081408509040e070321410304201070182042001c0c405c0385850040d101c200d00403100d00d40603000c00b030040c44000818505020260340038842802c01403081d001c0d0440140d030100040890b910032240046005590310902a16090000d442c641101308501c005009100f0300243c10b005a900102007000c02d5140c6100a5a0f45030080301e000e504042150030050a041c0c0540003203001d41415520203400c008070000c2250240a11a4014141d0704141c2c1c4c1080200c1c4154042c58100005440f03900300380603142c00340f40c2199103591000000c28007462040005004c442c012038024821200180154070348504000c00c081400d40680c02410b901001003246648208014542480d018088a488564088400c0d60b1050010700440000381c020001800c500d842e140d1540c0a61020f849403418203080d41d0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 380373327 1250 380372077 380372087
    0x30903141b0112060f12050105130308060f040608030703020a03020f0d050403060c091e0906091406090c040f06120501060906080708071209061d0c010c08160c08330601 74
    0x1c020b030118251a040081014405c29600100130204200026132000082c0350460a603840140015400e00d984075041011a4001d104542d01400c110b034035074090941d680005000341840d800402c0345100c003044140070540c0019100c00118040d07021202c0c030345080261b003a60b40c3c1740102100000749062004100041c482e8214a4283ca4503040c414003040e110032100c140f02d6100d40c003048010340e4114007001002244d1043c5001780035080c10030312010200030300024a07458081d00a40c0110515000240d01c61180c006403406000300900d420700c0503542c0c14004014101014480400614002c000100b6a00410794201220305540303c0311a1a80c035440b0907251400d00070144400e11044c41d6501003003400d41c0c45072002c102d10038040000c141442041c01c643c3c41004150a1079107500c00c0d9283c00c00c9a8001c1c5c0800c490719480780615684294000c5840044160240000e11103031514201240104010603d112801c001d090035901c01c0588091071402504900d46044000044202113681c3e544a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 380374577 1250 380373327 380373347
    0xc01051209070503060412120b0117040201020106090c030204140a050a060f0513030b070e0d02090a020c0c0301060e010513020703080109020a031b030501180504120e1c030903141b01 80
    0x70001c0e00d80c03a590780c0d8046400d0000450b41280c901d4007411810820640100d113464400b15050010010185201d0010f04039801500314820b80e010180000703011a80b00b5008000a01220760341030006124140e0090060b4000d4051200d81c100d40310b9401d051400d200041200b104c40040642c0106d61401c0020b4552b000ca440103103080002c00c01480014901c81d619480007140b051560300c11500d08154024510944001c1651090360001c0240d000350365464109a00031080510042c0e540340480d00087c03400301c80c460982e406500b0003500040280e420040305040380e009a4003415400c00100d11001244070701e40005021075003400050000d59a2035010b090340d02c4007402c0024840304140e4032503242090302c11010001a440703d0040c040303109598000005144180e44c2803105040c10344e80d0b112141c5261034000b01308a400184001241d43c1d10315241c05815059001c1843c12070f050500400b0441d4901042e2580805045400b103d203c0000f50b178902da444288403405d00b40c0b45040116011006 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 380375827 1250 380374577 380374591
    0x50f06190c0b01060518030102032502010204030c0803070204061a07170913150f0b0f071a010806090105070915110304090c0801170a02031b15040801020d06080c010512 74
    0x11492800c000901c0d007142c15029000369122240c40d0080a03a0800314260b0880c2d1082c02a401071050004c0c1021a0203000303c4604000103002035102c82e05001c138020301490303201411010022030b0006d40003030f01100030840280280c5051051a4540e14458010803050203d1880048100320f0316001c08c011150400a0700101e520b600e28000b000340018458103c41c004082030140c0e2810711108200d22079848100411064110302851072521104900c18003544d880da1603401d01c0090b42c5010082403070391418a800c4003032892080c0d07507120340d08255038080843c3c0c01012580b0b0030740840e200c10302130180341d02101d40100707034480f83c458040303001c42d10003485984103a6076100c1448003082c80e07001c03406070003902c502d2a900c000c036561404021018403030030000526040d4200203134001c0543c41c049503203000040700203c80070088601c1008030700d60102100c0307581052800440e001c2510b51044d002441c0300c41c1416801d1100e9500c0d503009548880501458501281003008001c250a250802d040d9025070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 380377077 1250 380375827 380375837
    0x1b03060e0a1104030f1a250806030709050a021e040f050105090a14040906061d0a110a0c0f0501020a1d040e031e04090c1e02010e0a02130b0409030305060a050f0619 72
    0x6018002e01d0081c20207450040c900510800401f2415203012075060801c0380c6490414514104030700440e890707240602881c3e002640310b0000480350401c90b0100e6440740c2c0c01c1c41000b14212011004000f0a4000e03004403422068901400030b01d641c82070080e00c3c0c20020040c85041414034064506900e0f400d4011003680154403000100c020419030b10800c40103000140702130482a480080070045401d000705803415551518a01d1030840d51407a0503078075080d00c01e003041d90700d0b8a01d0303052419003000111001001c560000400040042e481000c80302c001ea6060b80b40b01c80c0e550030500f00800e49819003c40b04140d40240040e20038610b49100711075110601503603491410392106001d105941c0d04d00d00841c0030424100c4920110141c1c05c03580e41c015405071008000d4804592101030300c44804000c040c3c0b05041100c0c0002c0351030403030350000e80c81540c010000c0240c405070b0328010b405860101c60a6100e050b2040d40040c6604145404000c062001002240f90002d00074851921480c1c0703101d0901005 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 380378327 1250 380377077 380377103
    0x121e0c0e04110c0d11070311030312010807091b020a11010903200f03030301030f0209100b0a08070e060406141b0304080102180a0e06131b03060e0a1104030f 69
    0x1469074424440c200c0b0400049543d03c00f01100c0340c92801030030700c000008014440310142051030300452900190790f44600711030800d4888100280c558050325002508c0c0c00c2d40040002510030700055044101ca07004001408940c0ca21344161442403000c008403405a009441050700007000e43d0703091040154141011221951661285000c15941a02d080304048131f80980c601203103086985010444e034102c00441c80c41d8110b590324091050782c4e00f00203008001d40008201c8071803125040134050089508003c1e10340b401d08a00511050042c4c0b000800b15030410303040c1c0c29070b0900c08100da040d291103480d075402c0e50f9003149003500e09078048d40c51504005040381c01c068060806000500051500c60b002584503040e800e100c60604400c0c0c03880360f205120840b0200b01007004914900d5103d80b04840c6681070907180350089001e005221404104ca00340080c0c41401550035a010805441803000618020344e034518040040f200d80102a0009060130701c0108001406001d1140d0340c24401c0c004144d481c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 380379577 1250 380378327 380378329
    0x10609020a05070203100623040b0607050d0f030509070608100f06121a0f041806052802120c07080c070e01031406040201050a03090501060506031303121e0c0e 70
    0xa03040103041c4400910300140b54029881d08104402410000f01400c00000f0b00c2d040c5c07186180300d001600d5016400c08400302c00b03080d9455611140f88070038007810440d80e130100d52805075261400003103040003140003041c500c07182520900c45d8a100d41c51013001400c0c0c1c1c601745501642c44050081c41c4003103000507080c004c1390003420000c2d000c0003408075481340d1125100d88400141961080706a009101c0511040040242c0c2d400303485000f1842c09440014002c0000c6158111500034003038003808550521041c09090b00b00014203000b50703c1d01c80e59001c0202410313181b100592040e03c0d9000d001e011501c000c500d074008544000d015080c0b240464928000d1308004030303030400c40107078003440c00c0c2d20310800100241b00008041c03504203041040a0a103e280540c0064414020745a0302010540e640202e1010843e0960054000e860f00030142601c9280540000601c50b031035001c03c0f0001019100130940366451401594421003c90341c8800c9280690780c41c0d00000c0c4800110082000065020704d801 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 380380827 1250 380379577 380379581
    0x507081503070b0f0307081602030f07020d0c0605030601020d0801050f060310090c0329090403030b06041703210403020c0112020f07150c050403080f030a020910030c14030f1503010609 81
    0x44070001c140d186449203041e41b4050000100188500414000c00d00c0d005c50803603001c8120b51000c0c0c1b10350303c5244c6800e01ca001040030740320790365802040c140c80020042403003034210f006144108001d9007158058014090103c40000e0284a180e030000300004600c0c246241c60b001955103d0042c803440c0000a6a6850210984040f0b50f05100400e0f501ca11012100b40203041d80a0f04403110150b03819000d12100126012100c001c0003c0c0070182d03503c081c58095035800f01250010401c1d0021000c9041520900c6c540f21740c404440103010fa210401e038031007114103426400d81300319095005040341c07230b12160064500030349000c0b1400c4150340c03c000d2401e5429054021713001c82e03801200d07444a49580444200c00b1038400d40440d1042c84010300c4200f00295034942100c1100c08106030881c0c990701d40031181d40c003a01420003070650012400e46161096a07140d40702800b004259510340b0320101c40c1241e03140c1c00b4481921004001055040040c460010040808000c0d9402400025030283e4131035004007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 380382077 1250 380380827 380380837
    0xc010903020f0d06020c1c0f080906060f010e1210050108070f1a04030b250212041202030705030312090601141302070c05060408030406020c0907020a021c081b010f0507081503070b 79
    0xd2031803404111440e587c1d522103001ea00200607030070180400c2c148030f405540e803500c000b09003130710854504850b206a41d219400760400010040e00d443c0d00b075102e1040003a120704189811602051801000240700395001420800300c0703070300110b03000c0d04c142012680d07200220700d10405070009800700070000004d40f00c034240ea84140f080c00b8441c060124079903920040c8549990341c1c0c41c01c43d84800300519a0548080882c0d0071518800400106c00c03050b840840d00b03015955010b80d034140404207841c501d03441034030f20051290b00f0700b405907465a030f240c41d5404804810351080700d410a000103c83c103900f0540307500a14000d4055802800c18541e160002481a4020f40241046070004542004403540410408141c007004480f01d541c945059a002940d13900e1814019100301546850003c260a6030100c103180b094006e900c2c1540c48503a0360301185d0030980001014000d40c42c0003040012506039115090040708591740d002010788841020100c6920000b01d115030501404000154112a0a000742 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 380383327 1250 380382077 380382103
    0xb03010b0405010305070f0914130203090c1302180918060405010b01171510050c031303030e0603060d11120a0605060a080d020706051305031e0c010903020f0d06020c 73
    0x50360700e5040c00c2c00102a00c00185c4801e040c0711842d20701d005100d400030188000c0d1505400c500c0c2c0c074164034000090b03049001041d014041403000060201d4041d001c141c010814100395407891440d1050080d481c00c034440d0081d40001d965078442000707024533008050a81210003010f00710013418400040134109103094408840d260355608500304c6958002c981519580c0b0300d810b86107010b10708115801d01820803e80040d2045117603da50030000c030300a200340c42c8a403c0c0501240e4903254010f8081209030300c079000980200d550b000302d540491a150084174861a00500b0802051605a03110a040c0e01a0200345500020380760b807107401000d080000c0c42540740030350404521800c21006005035144190000d07400c64100c807403241415030f0005040401c41d0075900e8042d0b82d902c805032444105810360b0f003085503d80030b10b01d0140340f200121400020310000910a40300e2500d00740340107644a031050710009400c40a010240c54040c9881587c0b281c4580c0a000d000d440d001d40941d080d41419000a0f881c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 380384577 1250 380383327 380383349
    0x12080a020d050a0903110d0503060d08070c0b070b0c0c031615151401030204051008060f060a0201091218061b0804031a010501180509040510060902090405060406120b07090b0301 78
    0xd134050560004140b2900e5581c03001500500c0d1000100900d940300c018104d90040522021000400111300304031491940c02030303280c800700398440101c400280d01c01315065540d140c040d00410b5600c0c082008454a04d40c80d040150b2405884242400712001e0904060b514026855041c0e1800b00d0b482c010031a40b070880c13440d03142c1b0180c00e041d050035120511650042c1054818001406035032076421451007002d044d0300700101390396038403000104501c4041e01b225810080104410140365015001508064491a0003415580381d100c400c490001c0480a070302004c0300390b41001c0000b0703401850140040520103202c1c600348810307501d40e01440d50156004460b40e282e40504330207007454141405c0c0c003610f000d00c6d08985091021055030015050f03800360074440c142c02001f0804114041110340544200b03c802070054a82c1d85805500030340040c1c0155000e641084e00080d1540340600c510002e07101c1806400600c29220380310244030381d400401c0301c1c003405005000800d0b40c03030620002d107000300a00681 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 380385827 1250 380384577 380384591
    0x207061409010c020d0c030204020a0c0506060904020a0b0f0408060c130e07050414120d080a0608060609011a13030f15020313032a12020f03040312080a020d050a 71
    0x38160000c080820380da61005021415150382c0c00030180c050a501220000c02d643d1241c1480350701d490050b0301c000d40c0544005003003001c2ea0b4103c041c0d1a07115024a05690701cada900c1209000b06c0c680c0c111402544012003140c24095800305d40701400107580605101d03401c0079100c41c0803518080060b501d5002c0c0f00c401107060101150b500c04084060300c08100080c4090030201c2d00507142d8043c07070003130803203940591400100b00d8a4940f941500d8102d035a0486d559001e0f41c141c0507041d15003c0c1c030035552650034440080b96600e400a2414060300005d8000c080ca6840c2140c0d4151080110900640c40c4104210800c0c800c2d42415480e03004e5401040341402c80095031800c000c6013551010314046440c0180108401d070700b440c00210404580500f040e074134040d031200c0703404010402003504a4818854101400074020b8901480b10700c030b01283c0841d000f0b80000c014060381ca0180784002000e0200c07984125041503c6011404d8121121040250074000d4420501b0103641040f0381d201205692080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 380387077 1250 380385827 380385839
    0x3120117060709141003090b0411040507020304080a0f0507170609011404030509040902150403050f01060e1611070e091609020405010212070c0e040c090b011812030c120207 76
    0xc80c9801602c0c2e0304040070f0032440d00c1d070003060002214a01c00c3c13082e060141c40580031070007500501c5d074640d03008010104514141c80d0140b00f1a982081c2203004914000c0007131103150000041b903050312858801401080103d50311401310030a002401c8801cad00036001d00280c851103c0e10000c802d114844044d1800b8941510380d1421140490090100c120500c070612000c244c02204444d10900d007130314080381491a5001040342e16501c0d000b040da0b10307200024000709110300071800111540001000344401541c5100d0100b1402042d2004c5440462007807203e407049000b80700003440703900b8100c190381c503041d650320704031150407801c849908080d0001581d145942c421f400c0305001425100604600301414540000c0d502c0c035906030810305590300011120f06104558400d00d004083c200c0d2003240d01d1030075142440d251034686c42041c0c902c0b4284140f5007002d6004104c000b031100014541c0000c1c2600e04000307080380c001c20744030560600045505800c045041c281541c0c11b0041103400070310380c0525110b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 380388327 1250 380387077 380387083
    0x40602091f1b0c0b0c010e030d140c0405011b15020703032301081c210221040206070b0411040509010b01090602010608060f060a0b040303020a030813050c100203120117 74
    0x25004a03489040c000b28000080d408000e40c41a41c294203070058641644172051401045141c01c2c2d9045444085030010801c001c9800102c258403440ca0740440a0302c0d200440400c0b03001303501800340840d4060007082000308401c140782c408640603a5803003182c200308030040812a8030010003940020307183e41c50144122070600c05514110003d5503042d22540c500840e140c0c0f204200b651a80c69a16241240c50900e4415401c138848c3c0340810402c00e0b000e061350488031001390301c800300d608940d20014082c10b81600300c1d0220148100d8010340003503e0302d81c140d81e0302802c5403c0103004903201581800c121120b5200e40c420a8840c0e03a89100004404140030005007112610ba4081001c40e0b040000a100f07005000c12516006882600c00c1e0501c1c1c5c680000080b1451800d070081c60031000c01103400014968006100070702c9034000d4990490580340e032202c01e030000e0890721007c0d200340d000320201c80c00c50508010000c8801d43d03910580e400e040c109074842c04908002c2c5d000c107103103101554112001c22424 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 380389577 1250 380388327 380388347
    0xb0c070c081504080a09030503040b0a02010e03131428080f0a080d0b01110a111e031b040b0a030f050c030c0306010e0405010221070201060e0c0f03040602091f 70
    0x807100030702c41c070352000b0100308440320000d00040c00f408000c5a00d491030b0b4010350340c1901940d07000e4150b0b61140d44503a1300315103d4008142e0b0710015800c0c150801c2c1f503250084200c43c1030418a100f090a5241882840403600d42c2980000e5080560344148102102c03442806030f201c090310f10366240240c0d2514201c5880c010001ca9462544c2d00f00c050900c000940321000c480c880100e0000214518a144d0010385940d41a01c1d8a1545800380306006000c0007c40801080c1c000300440e00d10b441400a05012030072920a0f054264043e40034160032041024000d6000c005010010700101d801c0c11000701150b03511b01c050f40120358120380b044210f01080024488403a1a0340c0980040c8000b034100000a0307035950301807060f0514281540046401c1c45800e4044540d04140d00c45014940080f002d480010310b0001c031201001540b8105000c00c400d407006070010b02501560100702e0804480e502026100da20240048550960070860141591035040038401c00f64001c00803c40107030a120700180c00c007814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 380390827 1250 380389577 380389589
    0x70b0c0c091b18040902030610080d08040b07030f0605031002041d1512012a12060f05060a09031b18020901090e0702010902030a050304090608150402120a0b0c070c 72
    0x6504007081c0c001416000b6190f414407000040102407001501040050007100070194060003440104540e0100e48030510b0203c1d03448900f21150030188210407103400400340c1c1c0c028800c0c40c0720030110303625a10035040b07040d0285440c1c070700103012507903000002d1800103441000d0921a801080c00c0011a00f04030f01c120010040300403032040d524091810380346e01c00580c0000c40c8520480201d150880d002540031850396440f04070100d00c0b4002084001103501811002000001c4106076441c045000c980604412501e40b400c80e104114200320810500303801443c4000c0030450b20300000008554118805040440000380440300c0c1c0c0d082c8480480d80c40300488501d9078040c010003403100c50303076400741250003201c902c042451901c4e1100b030300c128054000707640040d51521407101010103001010000b4407c594051804114003aa50198a5180c07148510003207e038502140001d80507003030180380720280e0042e031026200002c0701d5586200079020160f400e102c0141c1c002c580c0c44100441500c1920281c1b072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 380392077 1250 380390827 380390851
    0x1214160f050c07060f05250204050c0c06071d090f150324040c05040e060108010b0406031707030507240b0a0b070215480307080309070b0c0c09 63
    0x2004016650b552a244198010020528070001070103100d5401d031100074401a08100c1c11143c034034440781d0107c00c0c112069116900e4100451040c03c051000c44a5a20380c040190030a0340d40c003501614800c620344241d1a0741340039020b0400311951149030b4540f14000001075105203052804249030b5602c2210001d41c02603100c2d01c100f12050951201d22000142d4070000c40285071345078907203070300a014158400c0350000d007440012114640d0110f5501d06170340b0303030100800184c3c2c4203100300025207603070348406021000c1401c0900f030751100c80342c000d048007402400c11600d8038800307036070b0040d41c2055680480a07001003503080025a002d03500a040f41041d085501c3c0061030300b403a5403041c10344201c00009101d04036820940c554030320074800303503410001c9072024540408804021610081424008c1c41c0541d0604241000c510325014440c900082c0310301c0045041580341da85003605540054004681449165000502400080d004020800100014000311060315051110022010b8500340e003940d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 380393327 1250 380392077 380392087
    0x5011104061d15070b04060b0103111602061902060405120a0e0906030a08030901060303030506060f0f0f0c1912090509190605030703030e1c0809011214160f05 70
    0x381d442828601400001c0e0b445801c01000403001800009504207004144180032650b0f80c14801c0d42d20009104034090701c028860f40c074951004400302c4840041200742c104007444410701034060403090030201da101600d01c40c40c041c160f10002c04070650181603030700140d01c40e400300b101700b020511440c0484030b03000c6150b41c24081c840b10081c2440070315021240c010f000c2e45000502c9994200011040c517a04821425070303071308040b4143e078080c10541c0000e0b404039080502142843c14001c048a510041e0304285a081110740c0740303984410751000e0704d0301c131348180103014020f03803204c062080c6c0d10803044c102d00039141c0031586c0c60710040d00c07025039088206102d010039042140742c5236064647d5001074041c0005010301c1c1036954941c01049150010385e014450004048101a04a20b00212240c012500601144c0c3c81e001c40d240030043c0002c0092083c03409002c2d9600f154022003903c1038118141e10089803074a50001c0fa2241c0000440d8444a80100b6480c1c696845402c5807541600c040c6515046180c2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 380394577 1250 380393327 380393339
    0x60106140703080f0601050d050405030415141602010c05010f09110d05120a03020d02030108060703060f1a1c020703030b01120b011b1a0c070c06050406081f090e0a05011104 76
    0x300e00003d052138141c886180000d0a680e02c20b008403103050200c0322007000f541c2068101240d5075002b5000d4012064002161500900c0c002d00c44000601040c841007881c1c0054812200415201188100e060000103050600060801c0c001ca650104e407500d80002c1c2001d40d0308100c8410701039581704500544140c402c0001142020030318078030000c19000745c0c907a141008102103000b40b06064101e400c0910110000c680b088001c984039000310107594050241d20f880b10000328120059200d051641c00c0f0400030600d0321a0b0007000f40042c049a56210604a08603040c188240d0380f00d580200d0000341d40e049908119a0010000310400f010f180c4100030f8015003900181c6055030421286601c080c21320034010410402c000301c481d171342c00e4030702d6880d10030304004600b03c00a4004040c12501001204008601244200c0a650803540c0d0380c1d40312002e586440140c00040508841e0094490b0303441400454844814017420f03640c3d101c101d005000d194250305006084505400cd030007482c801c100420000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 380395683 1106 380394577 380394587
    0x206160e030c0405182a04020309150601030f0501090b120606030c010c020607020406030c08101401030f1104061d0a05041205130e0f090f0a0507140f0d05060106140703 74
    0x90746c5070b01007c201c1a0f020450f2591300d1503101608281c9485440112590000010b060001d40c048a126004054807000d800000d81036032101c10500c900e090008440104500440141c200c0e42082c07800291296140003181d41045041200c46e000e55032004104c0b08400c0d070013041001555607a1414140c0f01c4590301c240c0708180640000c009034014903018101441c14141c009000c0e5a09503610030862280040c8180c9840c414200c1a0340d59031620301c01c100150210f01e4004048040d41c440201880400804005002e8280003e120020303a06009561b40d494840c1005604e03080602c2d4442c0c49560303a17500c00740344a1042014070001a108400850003040d10100b80d420300303481a20015034440400c40b000b0400d9000e16001c00c407200c081708402e0725621000303100070341380036191000030313400c41d661703034007075034503410610042248070303080031540b440103c40c80d044d142054419100a41 = true := by decide +kernel

theorem cover : BRFrame.Cov 380215827 380395683 := by
  have h0 := BRFrame.cov_init 380215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 380215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 380215827 ≤ n) (h2 : n < 380395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
