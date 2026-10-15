-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4748
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:25.69745+00:00
-- url     : https://prove2.me/submissions/1670cbf9-584f-4a34-9b1a-9aaa16116eff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853776978 ≤ n < 853956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853778228 1250 853776978 853777019
    0x2040e04050a0201091d0a11370e0a03082a060105010e010804050a0204021b060112020a05010504030507090b0414070305040b06191214150601080a020f09010f0e0613090605030601 79
    0x503152410445911044c08031005500c01040c0306071520b1010b100c1015124005da808803030000380c0410303000d03454028110b203804100010700000c841459612182d0066000380c07007442e14007840e060a1601780390344ec9098000311a41c000208034560404002400c84480d000c896030502c1011410800041c0c00010851013481d41640e0240c0c880e48022200d4080ca01d400c41c1851580c01940008600d0310b40c45070034a000d007802290031812071a035503401918184038a000150803134015400c2406035500c5500b02c00101c81000e0400185503903040a03d0f44030780010358013000000d444009100c00d02402140040c0c02c0750040b0340c00c0c036941040c0498840716104911074003510002403075100c01030011a11a5004030211001612070000780c0807400b5030400c00407a40d031404182260003080058185200340c0d0849820ba94416240030704881c0150344a000f80e1000d0300c104007032095500c0c0162114000381000c0c1c400854560f03d101d040400138000c3e200141c10480c000d6102da4010407964000101d6081d03140f5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853779478 1250 853778228 853778231
    0x406080f13020d2411030a0c031404170405041d010c02010b03210c01090b010e1302103213080c09011211040c0c12020106060807110102040e04050a0201091d0a 70
    0x8441c5070f01c041c40d00c08054044c1e24501040241e1812031200194031407040b07200c007004850396808040c1e0460700650000c0c0c80149112000030001080884d45444e0a0004407002c0c1c1861742c0d81d0000360580d00482d004800740341901c0c0007003d18400c01d01a41c0800f9032540020301c07080c41c01402099031101401d1b02400c1454036152027039003090a1004965005206200a11030181035041c01a120f10007803045414024510001800365040c0c100343c0d0792040c0c0c3c020845200e11320031a004507517001d085c0208604030303440207940e08c09150303195082010100034850b5450325070700120314029880c14154051076150b0081a03c107801a03071080903890641d409c0300900301d4041c9150a103c4101c640c40c140700f43d0130070700c0d101a01034000d40103a040c220350380c890344100d071580318044812401e80703825224000200b0640800b14011a0088070380c4800300e010b0704001810a0390701e03204510303046010b580542e10398110032240415035920000d40d4001d441c003034044080305003005a043c50340c800c1c002c200c1408035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853780728 1250 853779478 853779503
    0x3903140d210e0d0c050d09320d0501050910151703040b030c03040c0b07020a030b0c0c07030c150f0e01030b040e250603180f050a080406080f13020d 65
    0x1c801d6940704204200e050b1044074200122444003a02e8142d803000142e9040c410700440410380e42c03007401e405041c0d546000005070740c00210104000c081300400c0d000d0100c0102d01407506881e0f11000000c0c1101802100085268280f455407642000740c03060060100c42e051425040300c400e02e0303203515400c0300d2010f804ea405c4150598202d034118080c6800c01d6442100010038810441c0902d0090341c00396024074100310a03d952003051024a20071050001c0d0000700b040d00070404540d0003020030303500688118519103010404210141030903d250012038072480144405e00c85240d103d4500d95900f451818071703108071113000c00701600c0e905000041c1410140c907029600c0c20394403140c00c01402d400001c011128490b14103140c1c2e0345403604c000880c0440d61054040003420610030300400d0010380c04021007030001d0050761a41014491000b0341076400e072140c10003071400101c0010040005285a03900c2e24500c0c180000c0003900380074060980005a109404c850b0301503598501204000343d40180c40300c110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853781978 1250 853780728 853780787
    0x15050f01051c0209090703021002010203160c0b0703051018062d12051219110c060f0c010b0d0b09060604150b180306070e0103050f04030c3903140d 65
    0x1886e0b11380c1c000942008540d0007040e06550150081c5001d40e1000c1402c9030402a480c0701204c0361105900040c2c54104407201007140315020ba070045400117081d0a4410f41d09032500c41e00b90010b01c446210b040306541e02c01003004048903007403918591494445103441c404801d50402003e03001c05010701e080e10b1403410b0303030002088801c0000c4428041440c100e01d480b02141160b44194100800c0d10001050000000103880000801c0503104988000c041c5130a02e4a0b0045501c041c0d08610079148440d07507500c10460146d503a500a100d00184144203045140c80c00004950402d00f029041134012410000c05094505a04041e07800365684005d40f10380310b1303682111000d4011180c21615403d401541d0038001c13181e13801003030990030b188280c0b4140070766103035180b0349c0b8030496003101c0c040c00141c030060640d4005420030740c0d09030544010a556103121510326540340103400d0071421003c0b000b800c81608108000e0252050348042021402404c5031006140b0040e207241d110711100000b4641c031711b0840c10b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853783228 1250 853781978 853781983
    0x180603040c17030705161e0b03370903120204050604050402090103020d1e060b030c030a02070311030a2c0315180609031b07140409080715050f01051c020909 69
    0x10020b4001040320b0004406c203100004040880c05201840d02e817500e00b1050520740035104900300c4084c50700252031982d07080c81c80a101401020000b0481d000708030450f03100b02500038554001c00ca82e100001d081ca05614000e0171909101004048090044c441040681da07480150707822a44181d5025a89045080c0124000d03c102c080f5078401c5490000380126000d015000b8031501143ca5508100c2e0726284d903010581ca01048a80d40071041c01000012801e40e1150040d10240707229017000700802040c08420780c2980c201651040000c0c10700c0158039060301380c08034a4801c60f0b95810b41142011201808603880700e6110100d82c901084880100b091008000e0002c28200704400035500a424400442c980700da002c16882c0c401c80103001a45c40c180c0308040340007412910030385000c50b8507080c4202880040c0020103c03d82e5008c3c0e0920064000c00c0e00c81c2c00300000c0c03088200000689280000400c8404101071304254001c8029100f496019440d164400c28181d0b01140c030241a955030000551 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853784478 1250 853783228 853783237
    0x204180602120108060a0209090c0c070807080d1407030f03050c0c0706031a01030b09040609060b0918161202060903010207171b0a0803010b030703090503040b180603040c1703 77
    0x5065610002e407401070410b4200c0c01c2810303203082009403800f940710206010280d0045005540c2e1014030880820011040d40d00209503a120020558481ea641d07100040e08082e001d50054a01d600304400441002d0b83c045050030000c0c003441981e606044061b2001016030036080cbd500e50a0580c0c0d0070201c0c00d0f140101007903641f010300d07201c1180c0000d501e07000c008002d4046100c410310106202d0b030503102158060b0050b107040384c101900740c0c1283d80d51600e64001402c0c40b801c041e100c450b41d6034544181a211918200e106440b80340c44405d4000d50810130a01d0150000320003a4000c00500e010f03c039001a100e907800740d60750100c07407107519080c140c40041d00a2140e060010301c0611000b01c603042d00a8508060911003108070f580c000b500202e5503132103481d41200040101441c1081006200e884289405903400110600e400512132526070f4070186190706c00e8001e82c2e80c000000c41c2001c1e14880e0040352115400055a1050841c00d040d640d19184204a00401c540d242245070084210030b41041600d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853785728 1250 853784478 853784483
    0x1031a1306090b09070c03120b041506081015030e0c060d090c1703030a0f1407021b12030703030509030d05040c050405090316120e0d0803060306061c020418 69
    0x1503200c0d05554080c0007080300d0720070581c02d1800d0080002003490480703040381c411149078a0304a81030345030360b4044402140c0d079402001c01d04d03510110421151a244030f5400c0509501c1b200da0451418480064240000100201c82507600b511040c08a0f11281400c00600c0720241400b10310759240b01c425a040440c10343d0314581100c40819080714600d000d42084052070300030300e19071303444584a18540c400b100c1e003224190420390041021641503600340d4410700c103020002c1d40005003808680c20400c80c3d03310990705c12005138421181000281c80c0b6500807240503000302c80b503406e42010040784903124000d2850150a05554000103007100200b48119900d2041003101000249071915018160441030b01031103000e50305d007800207001400c2c000121100c1868090224101c03038282d5841c1d06400866a00400030404001c0d0310040540316140c0b231860540c801c9406036201d2a00d102414a041c00080c6030501c11a50080d90f14690381c10300c0d03e000007481c0c041c0c4020810b16541e1000c1c030450154881c00 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853786978 1250 853785728 853785739
    0x40c0c11150f1806040819080d02070b070807020c0a0e04061503140723090403050f12060f060a05311403070f15030b0d0b01080703030e06070c0501031a 67
    0xe002d907880001442104140305a03410740309010307000c0c444240100d010302005503000c3c80590307082211b001e0a40845610403043d071403515002a61741c005036040740340129200d030303590428490b44036040710301c5036488142440140400700c2c1080009010400070310580e960168400049414130034a900890b00410040b010b4455940d62440d181d240d1410841c103038001ea000c0e04001223001c3d501048601850508400381441c0160640704003c0070380b07400b41085003808000c01c0107d1036051500040e018040c40500011140e00d000024030043c01000002144103e108120310064a038202d800e942d8a078564050200c002c1400c1c00a003070b20070018503040d52004a6040c8001a0000414144805000d0541c20384011940e02d907101204540d0900400707070121420b4084101030340c0709502c192404040280011229040c5071180c0e03c00c65000e030070621068000240c1402031680110801c0d083c40e005444280c90054252903880b0701d18541d014041c1099100c00a01a0103408800b460700e00706c100400c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853788228 1250 853786978 853786987
    0xc091503060f071d092d07030e210307050304030c080f0301030510110a0c0c09050f22030e040902031c09052e0503071202030103030806010e040c0c1115 67
    0x1000c8201e040b60403200207030301d0f001604c0c0f060a501c1c0c0d0410701d0b03c03000b500550b80d684442124840d0b07000710341d0321000505a26980b60040c144400d0001d4028181d42d2400120080f00d00e80c158140000d0690001d84041c00c0e40c102038040c1c800ca0100e0360f0002583c50002d440351940e1038102c43c4001000d9002d0114040800c0c10407032b500d0810001d40c1264451421a06071520001060f0156509030030a00c9102005118030151240121590204e481c4181038000545494554680484105a640e42501d449110070045031586650245183e958500fa0755000e0044070781c0d0041422810404050040e40c03900454011500c0811030780c109282000c0f00c4046010310110010b0002c50b981c03050758818412030301c0340c0e4000074200e110311084000c0b510402451f14074050303003a80c05510151880b01040f5171403080a0143c0c00307610146000e544039940741126401c01030700062280611110903846145811460340355150009403042c0841d5105404000701414140054210160f01c0b5940b0300741080000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853789478 1250 853788228 853788241
    0x5160204110c01051609080a020109172118011d040906060914091926090d030509012616110d11250b090a091a01030b030f0c09150306 59
    0x1403d4800d0801c0c0d0398641c07019903101f814075690380c2002e001a003c10410b040912150044030100f4881e41309510840342a4180da842e44801c40c80d0880544802c460081201d0016008400000764001d00034a000c014800580b0060a4a404000001e80c4501d035100001d504000090300b0a10082c84440b0b000c2080940c800426200501d0858907180b05004101c40c070001740d01200315401d0441d402c03811980d03d00600c815a03558130781c14611400c0f01c8941c14000e0880655511100e511814440d584203500c1d035030814009400382d020f2074a00001c018020300203803607602000b00e4141d401030591010b1070210300180c4065810500c20300003e05a400740461000c03800390012100d504580c040000c0740c445000c006c840610b8644410050f107112440340c0c000f00304680542000e42881080144500300507070b40d402c0038000711003035948000030403002ca500f561419030b0103105103030740400280c0143c8210458100e40d80d0b1071344504004c86100d004a41c0100f4001d040c0c0e014008080b0070054219003441c249030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853790728 1250 853789478 853789501
    0x18070e040f022b150e0604080706061211010f0905130e070b0705030415020705031f05090a0206090409030905031617150f0a020d050c0405040c05160204110c0105 71
    0xc05a01880740f0741d416464240c2c1240303501100d80280e502200400f1115502c444c41440840c00940801e6180d96940090100c140040380c0034a210b255101d0b074840c4d0514000e801da520740c0c0d00540800c0c43e101002c8010410544290022031070034600061009030800c8103840501036a000103402612403951503140c0c030417603400360950400701c500310f40746250342d0071000e00d45100d200c1000b40300390418482000582099842c4c41803085a50054a090b2506e41010a217408100f200301c52a000a02c80064200314030b0340b081541159046001c0c21a51900d03070042400d51081d11000c0f40140d5450345600c06041c41420007a001d0315004081d09d0709580c0e0440d071a50400e09a010341e1b130010140004410581e44006059040b10041380b80126140d030361038103080d940313200040045e400c80e50200891402c60710244221440380001c20b100d90f440e541088188000c98115030030240a002041201400e042000103102d1940d6034112030218040d040e241c009042801150078455041d802d110520040c490302 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853791978 1250 853790728 853790753
    0x4031707030209011106102912070f0c020a15051e030703050606130b070215070302010507020f210a090f0306060504050609010b03040b04020f0a17010e030901050318070e04 76
    0x241e0350316501c108005d0400d9243c0505941c40031040603586e1003000740d910f41044075a2808502000c048101c544626000c109900440e4200507202000007000101130f04001c01c2505c00265103441d2404191642c045a0108282d015003604c0a07200071081007164401d00490f1650388000b017a60300c0d04215600310000380d41040da82c00000c00d0901c0002079450401c0010340340c07291145441c3c4000c151801078401601c0c1e1200c0d0007a45c1011000c020340b018502587c00034101c551199000050500e0103500007401c1c25600811241b25400c1440080003184107103e8041c004682d000e40a07559002d039003010349002c911640700100d245481c000000502240e507001d141200c1007130b20244201d42d941410041e51403402d00036800020814400306000c5100340a0995105d880503002e9254090483d0015612010551003144045426100300903520001c1c000d400d60407004400650a100103000043c0090000402101c03200384051503105003540c081000754001c2c49840036400503401c16090030b1410120323 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853793228 1250 853791978 853791997
    0x1e180703030c1502032202190b071101030b06180f120601080606010504060f0806040905161706060f0613030804141e030607030e070b0c0a050f06090309010305040317070302 76
    0xb20640f20501003100e41c02142c1c070804c2c99544500e400050b80701400c1c42c004441d48180c1e0020485284560003480300b202000281980c240d00e9621102149881240702c0c1c00501018100360524048030180c2e103c0340706950203401158411500f0300920408900f81100d07003c07016911070711401014200070070108255060380d00500c01c0d45e489980c1d51005445038403480c45503074001642c200340c2a51940c81592104d40182e00100082041021501c41c1d5282c0313060302e0801a000484104100300c0b960707001c04074104030001e0001518181c40c120300003982e101c060481003801a200000c040c0d021034648600203018650001c1555111500e030700310f08941c10401211113000305e100007103071025010f410184100c980c40043c02440c1036a41c11000304c0250844103403440983c0b042d00e40108201100d02c000d01200408440141034100c02401e000c1e18026032900c03526020307001541400440346001c01101e004135003e0801240741e460b286403c40d86841e070600103070b17100f81c0f240c0c0c188694154160000c10300140c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853794478 1250 853793228 853793243
    0x112080904022a1501060807030f06080c0f0d051519051e0112170c03090301111201150f1805120c0a06020304060c020f190b040f0e1e180703030c 64
    0x10f228003000360b4a01c1e03002c099102c404000001005901d10441c8129402402d0745404203c1c0a0b00d0305144050344c04a8004403515005a02e00b11505c6c00c00301d003140ca0f500c101f04c9020541030a26122140c40320180c00c00031642c1041f080c0060445101c0081101c8841343c252802c01003403a00c041c0400d4240700e190850b040c552001800018500600c072815402907401c10a01c0010308030b10b079042c82803580320000d0744000d8001401414a565000c4c0306207004280f0f01201540e031b0340b80800f60361207101016000f0024410304804100c0d40c45034444d15103000a0100d05003001041c0000c3c1d030103c0000c0081e4440e5600c80030007000c1072003801c0046210900e41005513030b1140d45a0b1a40c100785e0f22030155019000025850b00c3c3c0c20005441e20b40304866a081c0c0c05010020384405003171a05030312451796000002680c000040c100600444442e002c402000340e10303000640c9040070040440c1a101c0781c2030498040501001082c003544403003851258544002048070109503407460068030b22280c041c015038241 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853795728 1250 853794478 853794547
    0x50105060607030512072325080d020306010e12010f0c020615010503181e070e19020702220903030f050912130f0311030607020114011208090402 64
    0x30308190707094900c150b50503100e281c140b50b000e403242800c0b444001e010b10300304203001403030310300a000803010950180c1e000d4921a0766015488a2680c0c0409100b10200300c07490f00c131f184040400d00490942d2280c54404c20b0142e6a51200c01c01207500e1012400820b900035805c2e20b540d014407005500c417806c2d08070207401c140000c10503020141e89a850842c1d40a60314031a10070840e04662180d07009581c072040b407000b0400e02d01c6009020a2400420101019001d00201d507043c04400007004020700402522000b8074451412002d4183e50070b400d0003013007242e19000b081c40c4045640e0400300600e032950654040890b00c28000240029000d0310f801500820f180c0304955550707410900442384a200180b005001c60501e400d4051980d40c800f0710504801c20f0a80c00201d0020101600c6074020b500030140d1030390300094001014200a8042c00503070942e03142c80039940882e2018010036046030041b46070b020f2440401c0c21305491610403600351030703845440001d56100200240074400e902c07002848060040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853796978 1250 853795728 853795741
    0x103030e011e0311070803010312020601080a03050f03090309040908091206090c0f0a090e0607030c0219140f160801050106020303042001030902030609011a0316030b100302120a050105 81
    0x441604034069503204000c00e02200303680f4040e400404542c0e103040000d900d000d000e0b84645d40c60341c0084e08212002d810100303803c2090780d410400e140c0945000c1b0050400542c1c255806403c41c46008914000a0320200c00100032a2051043da2a41d081c0500144006030061a10340100d07413003c40c8040c0310b0000c182d011402d00030300146052040b10003400030304c2900400e00410600b01d5084c410213612042c1441d000c28007003034030b0003030702c1101480800400c411b040004001e001d40c0ea00c503402ca01190b000130100c8000004c0428440005c07a0050710b060803140c1c2075486241404a020010259881800f10000104424002d010f00703c1d043c0000070003642c1d0721200104d03140d10098901600c40c6c8000c07181503851240f03440360090303240d505040c00514a807460340402c6c02e20404031402c6034280d54440204032149141540d200500d5401c901514030405414409600707039145000140100540760005200d103d000303c018005550014140700940c60a29080b40d5210100741c4112625420a4041500b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853798228 1250 853796978 853796987
    0x7051003060305060a0b1f0302030a0b011b021207171c020c0d0308060d061e0f060b04180209060301030c1a07080924030c07030314040807121e080103030e01 69
    0x50320f5100c00074100c1500d503c51000054910128101e80c04501c0b0b44007660720342c4c81c1d8451821111b581e0344000da168078140030a9812104070440240c11710020120f080f210410909402040702d40c102c80c60740f42c81d0091400b0030300e00007283e0045032050980f2034040d45100c81c0068001d03560400d03a00750318455485410203d032550550f110450b0801360f000322030800207000e83c880035030040d4050040d030b14549007900c900069907407122121b00d4820602c0c03001501110b40d4043c42401c0060307441c0501416147c40b046800340d00c40c51190740c0e4250081c100f94090076620350100c4a06540c002c080907200c0d6100c0c00c050030313a02c8540c0b15048800246120310003159150400b540c640903004902e05051070b20740700a007c511301c1c0c1c40c40300d040ba42d00708800c00e0002903500c5000d5030141d030010300e9040d1074200c107140c050204ca095000068882d000403041200040401e01103818813907101010b4005444816804d468084200f0221400c041e0b84840b0a01000d6001016604880c003e1741d43c0321655003140015078 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853799478 1250 853798228 853798241
    0x150109020a051608091f080f0601210612080c0f1c0c110306012303071809170c060a050a051005040209060714010b0a06020313030314070209040507051003 68
    0x7030214030107001691600c0e4054518006182c01034885a1400e00300d40f0000b00302ca0409591903050440c2011800c001e0303544989102c0e40071241200e504614200f070b200181c00003c15000640c41c4114003407002c58a040c041d00700200606042e003c1001005c2d507440d02d0101c58010044d0701180e03100380752052048420024184140080b045c0c01c201d42c0801c02c44003103e00c1413145400340c030402c2ca1941941103a03141040302c42e0003003c4003511310300000ca150326102050360715151001d100303038880078081c001000031641c0e0240c0091101c0c4009104102d5140181913450701117045a00601d000c0364a80c0740c918003007019449105024801c220070790341c22031003d0481d8800c0d10542c402200c503400601660070710b5401485040c40040c2818207000710707551803c0e007035507201c0c6907400b82da511400b2072403480c10074210220180401d4005182050200b040050f2400114407016040141c0c0300c0101242a60349422550500c1e00640002021714190524559a4003c7d00c81c09010300c82e40322480034024402c4c40350344c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853800728 1250 853799478 853799497
    0x140c040e061309050f010e0c01050403032a020d1a0a05150d0302010612061506052d07061b020705151206040b0d210311030f040515070215010902 64
    0x15480351a0907007842414128500300e403081c2640e030880c8001180c03042210b000b0070a0342400100303d207550903001c40c3c108142d0508442c180002440309200007900f000a44151a941d94201d5251482e000106000c075007001901a400012000184041c80880c0001d44010300003583c107a40580c0b54469407204a40044070301e010404a440c04d9142c1901c0c2c241c58030040d2a00910000c50341d103441302100c940d45016003904407040e030764594044582d03000407030349000100b0450510a0070070304004a14081c14041a56005007640020721400b40d0040718025075280c25003001c402c010703e0b809030000e60f041180d601b03444030144c03140e01c4c40050649042d1500741e5000c00901d02071400c1101c503d041007a007650140030705034059125507591a0030b07204ca0451400c400c5c09041000f2101c4130341000c0b50a41c1c2c1158196104260528051b40c1d0703900645011079030000220400e1503115035481c100207080c0549143c030074400a061206004803941c4c00903505444142141944c1c41036665080040100c3c807400000c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853801978 1250 853800728 853800749
    0x406151403100918050601080a14070e01120503121305011a0f0f0312071b090e0c09090c0a08010614011107050f19060f090821031e0109140c04 63
    0x41c071083c507254000346018040036407000c0703011106030368183c10500240c103c1c1d1420362106046009200c3c40785103660000303a60502403c1d140781002c0100c0080c01e4140522444020704403820300400070204200c84001d40490200b4200c0c0c284503040c100d00145080081d1415070034159000b14103050000030900c1e002c40102032030b400e440c40600380042440e08500032035250040302505011240007034000c10340716200b103504102c0345121b4211003c007040346801c0504c010346032050a101e01c00d80044c504d0705904080310000c0b515640d266400d46064040f0f4800c1d600120305a02c0012164015085036050b01c20300e000c80150322111800443d054252000745100303503445074500f04141c0c1044010445400c0024100a0301039004402c041039085242c0c0c04000081d040800502406a0100344403018003d82801303064002e00c401095045c0541440501c04031a0001000c90324119843c1307118103d040c40c2e003481802640c1d442c2c90410040200300c080c0c900d011030010010383d40c0e02c0d1031005c440c10350302e40094 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853803228 1250 853801978 853802011
    0x1606020118060518010504061508070609060309080910020d081e0613020c0a080301030c0b0a05071104061e0e010605090901090b06160609050709150506070c050406151403 75
    0x45500c0601405002061500501d03550001004401e000c6e491256006803008114100046400b80180c1013550041c22280c120030301c00c0c0003032030788098643c2c122200c928010401e0049418899094804c15420550200a80159020306138021444072501000f079140c00c2182d0f03a581c0c100c03031901801e0010005c0c00290f0580010072602d4290314002400009400060920b040194014039105da86001690039200120041040044003811071000e080d40c035210a080107028103000e0450f00807142c00600d10794200000c10310726281c41d801039008201c1201c2c0350300f20306400d0a2212901050b80100440301210300008280540030303004446c0c8006c0064101c0c90305070729003000140140503070340050b07500c0a42001580c5c1d0100b03040e5141c1d85518051280010340c0c46480c500240751019079030010214900748110504140c1084040c041100e405481e116650902d078030b0f120204542d0b0790005544103292401c0810341c01403803a074400c1030142c81e03165000b07284041c41d112400c3d0f000844403100c00c0b018510 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853804478 1250 853803228 853803233
    0x20402131e140d140a1a0f1b031909122c01140a03060b1206040b01020606010f031a0603040b1b190c023124050910171606020118 57
    0x6450f4110f0303611240c01d0f107950010681e181d0a031258031403c1540710800c3c0405000c0b1501590000a030441d01c80a00c8c515010500c0c1d2000700c170703404000e00030401c0c100074550300840e200040d00104113095100c02d502504540010340503152020301701804c0030003030360019550380c00c12400d50140d41c03c040507110700154440d200f854001950104102c1400c154a031100002e6040a4401400720041c0c050800505031826609000c00c442c006100241154804030600c0a5a42c03ca40e1240300a002441d01190405203640882e41d1181503003100764010301c00100b00802c1c0684a01d0b16400f407074490502c600c9031462885440c0d454052030035101560003001c0400c4803482d009420318030216101502000340c03800b043c110150418242d0244030b02800121154558501d12441880d20210507482d0000c10b10002d4070400b07102d001640685c0340a0604c000200b948141e6035841e0360028151140d000381c40300080e8001d15212914041040b98898682c440460007a0040c00b8040401000d081c1d20380c401d24294 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853805728 1250 853804478 853804493
    0x60f05041509090602040531180f080d0b030a08121b0d0b04051f0911190201090203190809011d0a030309180903020a0f020402131e140d 60
    0x1140311020103041e01c400280c1403210b0041d4940c9074000c180040c0c8441c980b20038011003414102070810004040c082250340e20842c00b040f0800d0a048100000c0c0d02568035581401900c8100009000f140007000041d0420a01c00014078901c02200000c2c8440081102415516849298004c110341e8042c840110641e00b513240056002150111038004000503180350038203680414402d8040f01c1d1210100b00c00c03030501340552a009040940d2604c81103035001404078480010380100c0356070304e888180008260802d407060301e088543d24001944001d09580003c1d00070401c4040c200c5c0a40540c15540c800800b40a110801242e0048200d62074020807000444071100c0107403814480b102c0200c0211615110b104001014600c130f0384070142c1940c1083c02030a58405000d40ca05201810200d8100001e07a020030700715025940701c1580d2030035018034800a8082e02400130504900e4006110000b8080c3e0385981103e24040d00b407180200e403507140d215a600c0248040d040681148503078401300009800ba = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853806978 1250 853805728 853805741
    0x1103010918031b110607151a031902041d030706061d010608040c030b0907180c0e010c0303020f0316030e010605150a0201020d05131716080903010f09051f060f0504 72
    0x50340d10340c60030540600005c0c3c42e9005404140d078240203020919009555620910469041c042d040f1070301d40c5050400680e650f02c040c0f1810403c4200001c0d4001152030325040410500404000f1040700c0c440ca005c01030340c039004007005417031007420000001844000c80c0c1e41c540302050a10b840040c2603003454001d41e012a8050310444020300b0a100010104400142c40d40c002c8007001d001e0103000d4a003551701c64030840039035a038680840c9410012028a5040042c0d156100360a0804100003207143c202a0028090078250145240000080210150001c0211002251591030400000c0308020001d401c0341e074540502a0030115600b00300004030f079014060810020a07100141c036102c0d2003e4810309a03141618501c502c006441d240c0010040d525201928401c80d5807511410b00195001a8056100c51500036080f03101c0041c1041d4980c4082d0022042003100040901640400749403032561915040c1c007060588459000c8a5025484d601404044400d94803090428a00741002c010003041c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853808228 1250 853806978 853806983
    0x51c17130f05060703060602150c0301140d0606121502120402041d0f0f152517091f0204060e04020d021b030406200a1506091103010918031b 62
    0x72081090000102c003000301038410307072069a011468515104001c2d1601d450aa90000c05c0c0d00c4103401c104580c0729940a80741101e00c1002003111101d007400102e200c5100b003620180009051500c04198124a00c80d4500c61601c207041162409509103444400c80c060b101120001d2189400810090f150941080c541c4100860504800d021b81040d6549008a00c07005040181c1184506943c40130040c0704003010800f86045501191a05c0d030309811190501c04980d46110710400301540c0d29502c135085941c04c400d0031245100707850400c011100e036110841103580309006005040c0521038a0140207440407580240c40d0603401c1480e100410010790441350040d40b00303a60030700401044854200b03110180d5080355010316070711030502c200104000c070841c514101030840b10400c0c40b080500012402040c54016601c1e000c0c060319288403401a04066010349942c0d070401c4040c01e03140340900c00945c129888050100035201d400c405500780d80d881c080010780801e82242e1008244a162220480c4591 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853809478 1250 853808228 853808243
    0x5031b03010b06041206050a0209090a24030605060306071b03030504020607021903050d02060f15031006090b0109080d0206040201180902030106051804151719051c1713 74
    0x308071030100f400b0303400c0756005444400d50028001d0500c090741c460b03990003801c0514250302d040702050101d0034904020381000010307507484409120007180e15450b00c0203206203411003c00c00d170b80ca06081c00904001d035511442030003018042040140111003554020f10100c0c2d03404034404941e1000e40092500803c00e0b42c02000c10801100160f54001d012402c00080c0f400303000c1c0322400d609109282c801489000003c3d58000400d21507038103c1012030a5001d185d50307422090001034240801c0c00c10340c0f108001d0608a090010104141d01250050360304030000783c0e0780c240c50b07075030b10415540c1c2c031032210b00042c025130804404176002d544503410020000320114203401520ba40c96409104a9109138040c10000f100031912402020342e51004000e4084110380030b00c80c4202240c05074582101c68401c008200041a084842e5200188810515001031185480c0c40b9150380c10302c1031321482c820489000222400b01101e02041c012403040250001c0024020465030b01c10703124503a51000d1a90a48061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853810728 1250 853809478 853809491
    0x90402012001020405030f03041a03040503040e0a090605040308191a0103020f1b0a020111030c060c090a052e08150103020a0905100903050c0103023c0d0e070501080105031b0301 78
    0x1b51000c00805552003503070f100442d501d40c85c004201c0002010740c0400a0640390400034000810ba00209590a48401c8964481241c441c00c0c1c0c0031004140b0088028805820241008141a0407174540e510482683d183d14001c0c00c1100c041c503040703440c00310302154800d04d00c0f8510f03c480d505c43c0c4c1c080c000c00440300000760700d05003042541d5403804a85c03c0d140c034150351000350111b0865a01100d00700349480210010750910710030140803a1140d00082403c400c580000c00d1069242da240c500c40300003040061700c0100c03c81d003a600169031031030702201003000b4151038100540881344107650540c030803403501c41108100600400110b001c0c0d403002095104000c00c2000100e100d9031284681000c080032a10344050141c0f030752400d64200500d11742e807107051501c1403000318002481f81d42128803955280809001c00d1803400300c42501700c0c0c1204c0c018040c0e1100420201c61ba07240c980e0082c00d8250b244421200c0c02955500111404a02400b500750503070084e044030070240580c00c1911406480050010a00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853811978 1250 853810728 853810739
    0x30c0209010b030603240406090309091109031203090d081905010b0a030f020f0904020f16050f1006050109090f0e0318040f05010302060f181f0e0904020120010204 72
    0x1654001c2c0c010100c0010004203100c0949400c0101030412244a417540540340f0720b051040e00c0c0c440c8010000b90049445070350314402c06115440050262414040070450322580380340b021542e4000d1032900340a4030580410056009018082e40d2007130700074800500e035628006004940c550b0028210711304520040c160030b0714120842c09114060100d0546543d02e9080f11080202078900107001d402c562441023059490a038140021203900074010360300580d132114504044103652051031129480f500d060b109043c104040840d4054040301400d04541c04108440742030001c0f104184074070380c041603110745c04200c116900d0f00145500b40d074120002a40115120b1700c41d0540c1c0c0002c0d15548000c0505d151103000d81b6103032050242c142400c0008000d9581141d001c40c0c1d091154203612140c409010409000c107600f0503a06028040c005040943c1380c1158500c904d01b85030340400c40c07070085000c480000c445414541c268500c2070b90148e503520314104034000190740d01c20702d40d2000c84281d5001c0001254 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853813228 1250 853811978 853811989
    0x50d061506080f060904170c0a120206061e100c150c02060a0c0201060b07110d15061403010903020a02010e030c0603011203030b01020718150918140d0813030c02 71
    0x34010364940350036514110b0300070302c40c1c50001132005118880c0c01050001040705000d50068901c681000079946c1c00a10880c20700e02814410018600384000f00413150095006c188076009107001d55105140285190b2401141c0c4400410340780c11035881244842654030607502254401e02500c40b1120a6590314601c40541d010340300a8000f60f40618244052440300d4840c254200c0d00a01c004c2108609007480f06c0141d2103142e070094003404407580c4811107940d030700000c1c0d4201c0e03034010b4090800c190516002d00c05401180300b10204050507940750002414107000e540b824070742c542c2c01b900c0705481c6a80155060300044040c0c503098800c8598444540d124500150301070000da03503c020300d00a8034a8028295880d02c80031038119080f94004000740c464480c80280303ca8100800440e41800c0e008109400c80444c0c3d120141c41d40c01d1440f11300c0d041100700444040d42d80960004d20303500200481065803500c0e00100300000602520010750401070158000070b84c0c80c460324240040111640010780d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853814478 1250 853813228 853813271
    0x3021902060d0e060103030f09050913050708060a050a0606090b1210051806040605190603020307030f050106030c090503010501120828201204170120071a01050307050d06 75
    0x160390115005005058000100d0f81c0c05208c18a80140e02d50708050100e611110050080d44501c10790b200084204081400000050007690040b558546400c0d070b00034029203000ea80342c1a01d40e14040020030a82d01c01c044030000d03203030b250074058500308004180da1030b0041d00a1540e01603032140000898907a660540c411400e400419481c0078500b07280081204544003503000c0c1c0e10412580314103039840c46050480304101c0782ca5050060b140d668484058000e000701e144085000c40c5044008245203405910540d2084141c1e83d600b15420340b00c2d0281422542d0a004541c240c0070f08201000001b20700e940200504503030029103000c0403c0056016802440c0f504000c00400c845010030610000840c00c01c0501c21004001001e10171605520300056200d503000d01241c0d6a121040d12460000940105031500c050060000c2c4043c0c041c200d01c161a04003200c00c84030148280380803540440701250383d5040c1d4200801070f1034403504d000d0412200300c4130003d04a40d96503c41820340d00034030900042c0f5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853815728 1250 853814478 853814501
    0x60801020d09031716140403120503040b0703110d09020f3102040302100e042a0f0207030c12020112020d0209043909080307080c1903021902060d 64
    0x2c038001e4400e25000c1e105059010503a01c486152808028600d241422000b84145260401400307159002e9400d02c01c5101d00c0d0000303030081d1044209000740700c1d0f01c180107510640c02555034004a0b182e0070421070640309110f407141d5410005004000030352500341c0c0300d84c2806100400e05402e0b08070710f9010078404403811294412014080000c0000f00303000e540304514100c03210800710b00e81403d550004120109041c500420012946a015180d0304e60ba44001b91640041040741051401e03038040744d107a590580c42c0c100c00118032a0a004403240002181c4041d030f584081c88103030407800c0c201c0b00b050800c88034806904010540c0c1100c210801d5900c01005264050040035079201240c00c140030544003200c60401c642c5100c2c204c1c0c410031800c02686d01e0840707102c401e040d00c40840c242808541d031420b25003100c4128000003680313900b006003000080440310600000e5031501554070709880480c40c81500080c02682103501000501c000c1c91024803071243c802443c0340e040000000c110780444401d840d50 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853816978 1250 853815728 853815731
    0x105100302070218130b0f160c050307031416060c1803110909010b0a030c05090c0315090928050d1701210c0303020a1b0f12020d120f12021305010e04060801020d 71
    0x2c0c2312030304c1ea5900301600c1e41400c0e42070190b00c41100795552640c030b20502c9406020014410640381a020b02e0800f1a00c8664180000e144107030000c1c1407000040c0900b05035031010450b902000368641e40403594075001c40382c00618148049032104180401c4040040c44500103540e035580da15004e558400c0d103031010314061508a086035003000309100300b0b03034806401100e0100091082121108101c07805140c0032605483c00d0702c0640701c46103010714144000190b10601100301e404240550b210050164256010340200d0301d40c04030480c025100002201101d801803400c840040c45508400e01c004c40080180b845407080011203901c0b2101c00d55a1500700b100140c0201003201c0500c6a081403504541c00c000d0b088413099494103034000600c130b10502caa5070341c04040700c0c011819540d17903c01d080a1550008030014149014502c000c041d80f642402d031202065151124400c500414400d452f440c030740c0702000c40c618909041c01951000a0200d2403a07200780c8074400819045800e001602500c0c508000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853818228 1250 853816978 853816981
    0x4030206010b0f09041d1f0f0207121805060d020a020d030c05041202030312040f0218101703160c050f030309090708040804030c08060105100302070218130b0f 70
    0x10000d0416006910011044900340020103040300860111a0364030000c550005d00705035940e960200c5510700c00f0080005004640d846c00205d0b01802045a03181e405c08010814008032100c0d030800c030300440c02d000e08520f039010f044d800041c1c0215201074040000610300c4010a541ea0b0014010f0f50020150401320b81d004500c0843d03aa404202008040e80c031400c0901c0507820368000117015000c5c91140190034107200081d070080d51428400c03220000d207000090041890305040014185221290803800f840c4403815075252a0342200506006208040aa41740c003403500d28203040d4541d0b00302003812a4042003210300300c000b411214070285d184c4908240d107101e070b2800e01008052900d40c076000b13019405c20040c504070742da80c0590300d0358421102e0604117082d449a061a96841c01240c20041600c25803240c003003018400040c10a0480e042141c0030920801c150004500742d000300c000081d00070000f03000c1701b44a411a204065804003148000c00402c0d14291607036010700300f007540c09848580c400d00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853819478 1250 853818228 853818233
    0x2031009121209020f060307110102071415100e0705090405241203121b0a0801091a0607030e1210090c051203030c070606031a100e0108070504050901140f04 69
    0x920440c0c07810b000d80100105001d42e004240c01c40e01403070b99140309010006c00148054010682c80310024100c4000b15100d800c03e1910340005070070240780c94030310700c02c5d01d4904100c200145082c52054403140542032506180c1001c4038884800601184d0030f011050100e08a43d880f00e01ca014814812030040c180c0417030400710f01508072140b039200b80d80503052403a14070350481c80000c2114400c461844100c00140d840d038140e00c420004400a20f0980040000d200c2c3c0c210342d0044810b410b84c2d440c050200710070322140322982c1c01c091103801c025802032801d02c01900424081c5d51b090307036200c40285c034520074880840f0134a41414041110840c60b0356540d09034200307009040c0008009403109460064803601500c04440c0d40e0b000013821040d0f83c020001d084003c00440d600040010755003d210407114000003440014102000c42d8007959039038a031200001c4040e500150207040b5440702002e06200c50414003404060070006001400c1907403140a86803020358107040c2d2512800114032264100c5c2402e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 853820728 1250 853819478 853819487
    0xb06040c030203160804050a1a0103050705030613060509010f0509010e06130309230406030803010806130b0c161407051f080105010f170a0204080c090c04120203100912 74
    0x1a15500d08251052080184400b0144130810b810b4495081240d115903462412620344488550000c16501c03007134070000c0d40c070040301c160181030364420005e4481c420741f604249592801e08940002040795464149004a1100d502c0300b600b14091000105a00401120364819108240c13a915000e80d982c3c3c0400041802c24404203800c05120f00c00d001707400b2103544005003000c0070790040d0141003a8164044030203149005a041c45e04401400c140100f40d941d050a841c96002441040664095200040e4443d42070f5072141450036440340e84040d1580365140d403903100e030f04050342d580004805150000c000c10344110641c00490901d600402115080c0401d000c0301243c0c01c41540420407101200c00e03602a0040d00848c10b40fa02032a010002c040851011105029030b240c89408144200c0140444001d044d00100141c5112404452070180d00d801800401d0a0499210748040010f000034090012194240d4421500090841d4880d402050742d5104880302900101c9855007016800e28619402 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 853821978 1250 853820728 853820741
    0x322110f04060f050405090f010905210a02060a0e07030606300506040f080f0a090311030304030b1305031209060103020112050402130f0f1107020307140105190203040e040b0604 78
    0x7554103000d118a005404036400006008103442942c459001500f000340c2007194507024030441000f4018131415007451134891070040f008407030340c002c601800340203203034058101c2e0000c242c5c6a008105980c1c45e801c2e0300c4000c0c999403c0303ca55034041d103800000421030364000d00016065615070a03d04058201d4501004445203091090645a20b41c0c64800704401040c1294843e4101e000043c01c0001403610140b54442d003200d400c0e40c203802088040410b40c2c0f0071f01180c03d40e407040300c600010082c2803080543c0c03402184001441c130780c0e203140025114805d0710780300f660f502d101e40203ca0802815526030031001c8022280350a4076800078004105560348040c030380300c1a858000040000d400c1540118652080c11255403801540305d081018a251140d80800e103043c0300c04808110880701d407800c1c402241d114900a038468880d148000ca00c080400d4031402d1304100503102c107450004814201c45040040038150f4003540400d100c000340100da424150b510031440b41c22800d046241480401040f40c01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 853823228 1250 853821978 853822009
    0x20c0d050f011d0723060f0c0c0118170a0b0106020d09090612060902130203070e040b040e0d080a020c070b04080f16060e0a08030d0e0f15010506032211 67
    0x4180f05240c03a03101021407000700780c8040002c2c00e0840e0b40f04442c00c1556000607210690810310011f120480e0560a40180c10407486003c140e4120301e5000c4011594801680014103190281e00c104001d90922a080881190f43d0501a1031f80c6404646400411078026488000540c100c281401e10781d940c8029081c000d03299400301001080d09024040c00546802c0000800255880d4100025503543c06080b440c04844808195a6882c1480c0b0003022103410100d000d019508207043c00d03119103018040c00501c0c4103070380010040705201c00c908a454010240c9200e4403d5400c02071104158000d02081015015149078140d60f03521b04400d1905c4d25554882c0c80a45801941d90030107110316a021141c201c4100c2e00d01101c02074108000196012403d5000c00307005c0c44000b0724070300c0540c02c9030000c0f04040f01c52800d484003400b4115403552a102030600e00a00d9002d414011f00c89840c000b00510b0b04540c5040b02c00a03a9200202c0e1119580b00c54002aa144800c03422501910300d851102d00d4030303041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 853824478 1250 853823228 853823261
    0x303020702091008030d02030c1612030c03021e0f0c060406090b0105060a09050906032406010314011a1819240519020102070c180501050a06120c020c0d050f01 70
    0x9191040403a203d008806d405220150000007080903010f1020556000d0001001201c0102e440c91500a294a4005403180c001c6030a21200c05c10490217071007522440c038402507040a14010250141c0c41561059031011040d80c0c0620070203040607010040c0c0f91040d48142e00019940b4510309211582003016404503100342800c05c00100c82c19400b80040d02140c2050301c0000c010b8450341c1c0000d04040250307081940c82210240c20040000b80782c00900d000d600c0c2a00e082041c0c2c2d44100d08500498000d00910400c042615a04000f048881d8001c041415480540650700d0b12080c00140828003110210104802007103010f10055410850307844002c40b500c05072246100103080d0282680c010459441e1004882150142c1024001c3d01240c6c802a4040800c405c03994440720555012803220b4804650603141a00100305403c04c58810029950291542c0c908d1917a02101440581110038180f401c502800d00e4403802c40d1225610f0496482c40740024007411b4128880712800c44851861260000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 853825728 1250 853824478 853824511
    0x11e0b0114210606041707090b03010c09060c111507060e07060f0503040c08030309100b09010b090609040e0d1d2e030b06030403120c02160506070519030302070209 72
    0x2d41c04182032803855040d4030580b01860b6200300010b0f585016541c040b18510b0850040c50440ca40041419400e0f0303102140c0c10404160940b080c0340c22244034880740c0010a5074a0024404580540728000344030b0f100c0c0d606810206e0005000c24030700c00303c44a400c0c5205801159020030011540102c1c101c1c40140710040103003a06d0098010099014215080140400000410144000895030303001a2603910304882d960f041826a0698070b02030070b0800f094982c500200300559192840b41c440c103c50140f0091802e0070512001c004141d80520201a8881d07550480340303c0343c83c8284624100040c0300d49079000d0200c6951040c1c4900c0390090030f2070748140100d03c20310752b50709010008800c000103c071114105031041d00509034000e1a400c804603030712010210802c81011b5014182003a44031100505005510144c8816651103603040e0702a00c2c0d01024100902c510708002c3c02801e1898000c104031061101c0240070f03241e40081c01c5a040d0006600043c0c4182035080c03d00025400000040341840b0f01d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 853826978 1250 853825728 853825747
    0x408011e050f4b0117011a0f190306020301090e1c050a0921030f080f0106050d060504021303020319050c0d0c080616030614060912011e0b0114 63
    0x40c0d128218501210441c0303807402c3d0640c01e44100a440500d03003801c420308503001c419801c00150707109200b0b40300400b43c40400c4400221044c06445144024000344500d100c520360704119008a03c1406e080e0068201c0d00096844140400b03424002c5004150050f541d5040c03c1c068010b0f240041c400204a6002003141075490101900802d440007981c82e01c00c0e1685c603003501c01c80319202640c1c083c10003a0725402e05294540e2403d003287c10000d20030b44403018031103042102641c1083d000c4504060403500000100301d4517003da0006c01650000303100000b59281c45030002381c220780104152120021030640107004500742003101862250240c842d0500c0c000f501c1d540e6640e00c60355081c6150290703520721520350070027001c40800c40190409205075a0701e46010f2043c1d040d210382981e01c5500090402400213200c1420a4005921103800fa0045141130981401d02a0384400d9440d20171080d0340e9412a0a0130b91a22041e0240c0100319840101c1c00701034080c0010015003a0507041a00f2040401c2002103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 853828228 1250 853826978 853827001
    0x3140c03040201050f0a02101424030f0d08090c0103110d02090d08070308071e050901080c040803160c0509070c060b040902030d090501080c0a230408011e050f 70
    0x24804089002903580340e40710301c0102d03002d004410610000d06004074014191503000300b00720002041e002c0301040060050102a44441c5080e02c14450f440c828011103c202070203600902e0b0342020250031100210084486145014001840900091607250500c0035000c000d01000c11104000d103414000800340344041480c9210340e483c11280326a00082c801001e4031460300300c6c1040ea03040040c05032600454140a03106007811600f0100046481003c40006007840c050200c020185985007801e004202c00152074508000c3e000d482d400038140000628403508200800c2070010980c00c5108542040c680895950f00e1600a68171a2803075a0401c025a5070003201d032030220741c0005005c04c0001007600402c1c000d01a8480103900740c014482451500c0750000c3c2c040c021a0420398416403941d035102d100813964081c408105000036030103101d0403034017a001c88461004800640d4954901075607105020b007110f040c11203142c04180ca42528490181180c8140d650010403d10090003916044000340d4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 853829478 1250 853828228 853828231
    0xc0f0f1f0e1e0f030d020702040b0d050c130204080615010224130f3e030a03030b15070c14030a2f0a09090c08031611011b03030c030b010314 62
    0x250955818040039845041243c103000c03a5282055039075800003c1300801c0650310051040c2c0c040c609103c07205400f07082a100b1401c2041d000b030060031055583e4010804003560780920340600507001d00000c282c045044c4541c0d8003581c4012044204c0038100400a4100280c410703c0c1052803003200e1182103208042d80c0000d40c4460951804044040e03607181c0954048001c0324054a19004000c41c070400320828200c0aa1002103e501084505d079070000b1002c0e0300c0e4a1080454050300510346807070009010b5001004424401040420303144400c3d0051801904040416101204600000c22401104407511396030190194041c0029070685e0310344030b0043c0303004026000c050742c032903505041207075a0a00700710341698010003060002d680c0340e0030300f8090050a5030030349016448100c0020461800001c80c0d03682142d41070f2551861045440c2d40d07114080c540d10950502c48926140f0074288820704010340ca840c4a900d00051511503844014110354911800c14103061401e050340c500c2010b0116440d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 853830728 1250 853829478 853829503
    0x10b0a0c021f03110a0c330506130e1203040f20093d0909060905010f06031a07021f02030f10050d060e070801060e09060c03010b040b0c0f0f1f0e 64
    0x18001d03000d4011211f00800e02c1004245a50011101d000c480c072120b403c414022803003100c03056802c020300e5451104032145014110116409416482d034902d00100146600501031003d100c01f07000e003600d44a8121688a80c41c0c0c801c03141c0030510590030b151080a03603030420a28200c9020400840150b1940121090b1010f0781840d1074042e90126480d060010354080c1400c0f00301880401007900e80340c030140c030200c5811a002d500700502042c1d040d00c248996011241c003d4004940ba841c0320f0681c11070f03601c0c054001001c5000349074056046240c2003455a110030b00d800340040c0d0f207151500344480b8400000e400c40d07a400390b4441c0c04004640d1034000c0e001150f03801c0f600c00258185840d002900c0c0c14141e9104516035403c1190008520603c240d00c0b61084924401f950b00c0341c1c3d9580690252840240180c18128a09000901008034180003030400000d60308201c1d080d91160780300c40c1707190040101c188404d540c44a11807000b1003609600408051040007424072000000d1541c143e100c09152040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 853831978 1250 853830728 853830743
    0x10305180f03040302011715101e0c0b0f0c0f090d050604050f060f0405030d0b030a170307030f0b100f210f0b0f0108010b0a0c021f03110a0c 62
    0x109010051010204448044010071101c9880605a5468480e082807000780d01260081180d480ca000201036a1442408000080b0525002100c2000400801181104c04200b03501d6542118600603030000c510308680d9440d421803201051914020300440100a004001c40100c20300c45180c0001041c4c4005804e00c1a00c542c95220280c0030070b4004a0141001c0c0641c450182400203212012a000c00600c40700030944049948079100f20110081c10384000f440e036482006403128442c05036100c4504d2240007010394200341103e40f907500c0c03480c401c40e0654100103000006e0000068052088200d000485501442900301c0400010101d015041e08034041c0312015014040322403142a2803107070a00c2401d0280b000f1806041c0c00c80052000e0718007030040c5403a000c0200b00071301d05495149003011050b59803001580c01c01c003c2c0c0704503801c00001035040c85242d5190200590b100180507101c0c41102d440341101c0c2c10001c0008046d10809174841c140102c00308145449075500000300398006401615 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 853833228 1250 853831978 853831981
    0xb01050402180604030b06090106020a21090b031e1b120709051315060926010b0301180c05010e06250f240e190606050301020c070e1f05010305 63
    0x4102c400e00080c820103d034010750000c0c0100030000c000302c07114081d00054039005040c0c0c0e256003082e651101070010140c081c1e5050054000710080009003017200341e041c0d10340450101e68404107106240c00c01e848014911401ca005100c52841b2032904550282c2041ca55a9080c00a41d070020110b2040c0d54840341012070200001d1020350244401000400d00500700b80041c1803c2e584035402006042c3d503800101c00c1201d0b0010fa842d02c10503007034090341d10110100580b40b205885460041922419075800b554840389404096502889810345d10381010380c40c20980500c0c0d14000481407011341202d81440311032800c466003130b22020166007401c134003035102c026004044d0207001c501103089280103044100580044080000f254442c446441c0758100a01c010800810b0442c2030750004c4103035200d140c0c007100c500681901414100c810792030141c4000900f0700d07250008a03099a0103c86086401e6012403402c000c0601c030a0012907202c3d0100c0754190442c029150560b55845451207501d04040e01c420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 853834478 1250 853833228 853833247
    0x1902100c051b0607360b07050106090207030e0d030e03240a06060906050a0c020d0f051506060a03180609260903030315130905010b01020c0301060e061014030a0510120b01050402 78
    0xb4005e00810745c400003200381403907544c2d075001203942c0302c12002c0f0382c2c0b0350800780c0005818040303000f0b5650883d8951940102e24a10001340240c44034413420507000c201c01980106000d84081c0040c80340d0705095210060032140c100b01e403c04d50700340689412002840c0010410400d0703400782c08801070b54554601150307107035003c40040300d98540f11003019620107400907481080080c0d00082c031840c07510a20075208480c01202c040191244121109508060100986400c01e4400d034044004440540031400f0840f01030384074a405c886102c1c1d41103511030b60041c000b04000130002c180541040746401c5c1180782200e100007080d2240406403a4000303610180840070000d0f50744c0f40c0040408010f41c0030401040c541410458003801250310b110b405406030700b00d08001e038101030084200762403804030748c11525160b400501c07685013a007591450402c0010501e4540d1041c5020055005002c45040400c050500300c0c1c2d00e0075900d10f25481031101c4072400d0380700800a1521300c0c0d05030440d0303011140181c031403000e403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 853835728 1250 853834478 853834547
    0xb060f0a051f09150c030905060307080a0f06080613140f070317040503160e070e031908090904030c0c060302120a1a0a180f020304081902100c051b0607 67
    0x60300541c4c02042446180f080e13550b0f0181c01400c246010b5610b0f1007a00d075035501442420300c400d443c040009158500001e4002d10a0f40085514410490380040c5460355119003504208041c5ca1302c0d040d0a40d01c24400c0203000003032090000316001500a0108038500400340f03580c506c0e042c8130081841c2200e450801030741651106a034003d11002d426200c101060301e0b04400b50311014001d0f6100c00807100045a40184984001001d2242c0500201400912200480b005c00c2e0340300c40c00c6508442c100031000190300d07054102070181c0d01c03a0b1600201c0ba01c4c9450407088036062030300031100701881802400422101400c101e0780020308182c0c0050303030426010160b100100c45540d800c1c0c00411103c40018004042034400c80440c1d25280108083d58401c000041a40300c1960041c244040c113002c3c4450902d401920168401d00d42c0c012605004045105201510a42c0600b41c010480204480c08445007840d003c9218418440c0942014540440060400c0120303001d444020300103080112600d0052 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 853836978 1250 853835728 853835747
    0x19050f0f06011701091e0c0c0807020402040308070b0f0c1201060f0e060c100501050d03090e0a1401030b07020d0c1e0302070f0e010305070e06011407050c0a030b060f0a051f 76
    0x10480d00035001c2d0b84401200d40500b032401042c1800b040c015131b000600c03004c58411080481100c0d0f4800c2e4850461740c580003141d40041009a82c03040d420880040003c2c00800145142841048001034510b04201041d200c039600401c01d12440000b001142002801810300d5410b4071807500f0080b602a103182021562820540d65064004600107001080c0003400a0020261407083c0414402d5070380300c2c418030804110300d01c1c0003804101003400034000319480741e04a50384441540000103400f1107a1000d00c0d4401c80030790080c1c2c0c1d081d412001384504640c0c1403058806d0700340d980c01c00c8002c035034081c0d0300c071b4003213a60408450040341c0700d5140e610109032080c001c00c402040058900e060700d90b2520204200300c07400f84030840312482268000502c10a82c084001d00c5044140c44d0b100c2503c110b0041e020b89984056400c550700d025881d08000e144c2d484183e44401740d4020f5011464629000d001e210210300b111400134030400303050400b000541d460004104030107441e0700403071020000c00c040a80b40c1141c07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 853838228 1250 853836978 853837007
    0x30909020f1209060121050d0e0607052a0d12030e030705011a09060307150305060d060c1d04060b030114040b0909030a031506120c1110020319050f0f0601 68
    0x1071002c20b00210002c0022907070b05071010710b1404004015900540080f80525160041164011440d5840030f180074240110310510041e04144c03034504940da0392400c100c60340c0d2500f281c503820307403220000b0f545800720901d28001090b2404c0345824255202d15007030050400000c0c00709511000507241c80c00090040d600365a500200034402691540c552400807546815801e01411508000920304e19001900d641100e0007102074221f00c4c5260350049014100c024a221f030400741140e0000000385561048841c0503005a444680450001001c5601d03980c0c000c0c0b20718411401c15074184a200c1d04c04084904446242c0800710010750440c020038040c000140800380d01203081c10820200045c0800200320425155804100c0c0700b41003c00c10f080d0300000e01600000a102440c8044d11602e03e40c842c044403041401d06100840498820501d040c2c03400f003082030078903004001e100007078603542c18488800c540c412082c0030900c0d11a41c20300c0d403140001c118800e075050440c0455605c4e400341025408480 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 853839478 1250 853838228 853838257
    0x40905032709090c01120e0c2e1d01120e0111070b1f1214030406050403020102070e130f0c0e18060708060108070f050412030c1202010504030909020f 66
    0x1d058003401d480307050800c515004a1079071000501c0580045115a100b480584034024014801801030b001054060428902e500c114041c494440da1744090440445646081d9071400f043c07800080c0301020010b81c3e86005122051940000c400f40c101e89601e43d044007031a00403003405040030801c01410071003160328050f501c0e0044415803c1c80d6400204200c0780114070348041c0303898801031115054040d9a40c2c1c00d6094081c1001d010304880341e07408202c070078011402c019803101d20288060031503000da48007402041002030704004658040c046040103200850781c9a4480c0340c58010721600c1500f200300140703180e0030301c5a894100a103034801c1502411202410407503501e4048030010f10191260442e800510a410005140b5403240020310700c103c4043c1d45e1004152540041a21100242d02482050200520010030220810400c100c50300d07000c0d95594000c68440c2c2010094004440005000c690401e0100b0010982240380e0070704445243d24011303070f07640140540800c980141c058102261 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 853840728 1250 853839478 853839517
    0xd230a0c12260c041701150906051c1a071202040e2401020705010e0a030f050303040308010f500a270518030a0801030501060e011404090503 62
    0x50b64856400000d4001c4480841e14400ca641c64001c080302c030440d5280410007040100f40240508170115809214002001041506031440300e503420007500d40081c00000d0303075510304102514242c0d01c1c8403140800d0500700a0000c1e040d4503034820210184020601aa04c2d8001007001c091080349d1008405420002c01c40d11580c640040f010899000d684000403101b0010350b10301d488411000400544e07105030006c0400501c2c203801900c022484000b21940f102c070440b400004140d8122005c1800c92141025607a2458540b40c0980403002c1a0031417114140f00503404c1c49602c002c02001c55054240307074002c0144490701e01e50300c0f07910040d142000c40a4102c01610207682c4a180f1407807802c56200322402502580c0703550340072084c840007040c2950f9075009581c499411030141d501554016040c0d420b03030003041d210300008500d958800f40085001032010f000400c1445800e209020103400d000084940c154902a90324094110700c1c22100d11071540c4902420401c1010030031505004203031407819291 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 853841978 1250 853840728 853840763
    0x150207030b07050a080a06121112030403060b1e030d0804050a061107050f0d09051c0204020a021006080a12031a0a06050a0e030c090c1c14090d230a0c 66
    0x15030880b416490100300702c5c10124041900b14002c0c00140c03500f40381a0038a41070a5100d039907190360003003d02c6810091300403501142120620042c00030b0750003184007144d20b42c2c00b101842036600005048101d0b00c005107016410390740d00030813205800d14540c50211119119810514103003250030400924507031030031980114a02d03014026050450140c03081e1001c41c40d203400340c0c58907404881e914800041d0034401c1032102d4640829450b0402c120754540a81c002900c1c1c0c0420100c0e401080301c1c070050f90000c80310000004a901640b27000d44120070107031001c0111591190300c2501e041d41c0031001e0580b0340c0303800d25003042c06100565085000070b0210398115911100a004e81e0302558540780018610450000c1c00d013030001f4000468032014000c1507070fa40c1e034070740e2741049a00712a074516405480101400c0d0100180d000c1e0140c1303e80b0400c980d9070340d81080c6400130b250000400c0c02d2024080714045001d40311042080c2400024010180b1a9458646080448948202ca40c0051442d07114181b801d0f817 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 853843228 1250 853841978 853841987
    0x18060901180e0d091404050708160e090114120a0b010b07050a061407020f0c1c0321020d0509152706190c09080304060e1516030324150207030b07 64
    0x105e0301a070a41c3d103060300c1c5a4007880b050b25011242d00000c9901040851403005d401d0410403140c11207442c0c0038022032809000121010020b13841400c80b100b444400281a1501d50356814541a00c3c0700180300d0b2421075550009840b4052080c48003001001c0749480501000344504e00300c969015004100c03e517407140c12003a845909880c0e500062244d01e00110888500140c82992001c0c02800c9407142c1c644054502c000c4018075a0840410055041040c05085600f80e441c0140e95421000768483c0c420160071411181e008002e4a80c59110448020b4225407804c00305400c0007922070010303542c548440c440e13490a8500c1112124502c00c1104000c044030403200060348180f00310006000d0b41e240e440c01110510801c8c099400749400402080101d18001c0f5140c150450024112011310b0003c854481243d42004119000440a28040c6010580c0c181b150754503d09a4000c01d005034035250030640e54010841c002d00d0001c0c03800840c1500799a00800c0841300642e80644100d04500d00343c1d40003072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 853844478 1250 853843228 853843247
    0xc19031e05061305071401090308040602010902030c01030501030f06200403150606080601080705220306020a140f040308090d0204020703020d03060e010302011220041418060901180e0d 81
    0x12050b01680000c906444103520743c82c0000c0760040010070b001030815104030220703109011002d061000601c3d0000020f4071110281000f0010f079000003c0e41034444c018141021040c122030b40c1054a1f0030014000034600c0f0001d0000300d40c00100004140c070407000c100c4000c0d2420040c00048070b00c04100042008414124040104c4116100303000d0107075124019500d4000654002d4017043e44000024400ca20079405080d11400003050440d09200780001d900c3c1d403008541083e15119000681ea41000ea00182d1040b9845d901000540c50301042100c960003a000b1800001c1411a00060040ca6690394032003091700395800a004543d03031985450003a548440032034002001c68206080080d0350038211b504039048a0b010b0311408a0242e00e08607190061900030461425038031010520710002219102402c09400b14070031a004520f01c0034200701c288010306150394904201101000040d807100000281151842c011028952540b042642c0241080c250046901e00c519090940030f85d0340b010044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 853845728 1250 853844478 853844483
    0xf0a020109050607050604021302070b072c0105160204020d14011a0301050d02040c030e060412020f12040b070503220501080105010201090f0b0907091118030f0c19031e 74
    0x70420309603101c051048601400c140600250410740000e409801c0c84859035804810405005142440c10f036a07420b4050800d551101c00140407120182000c829000c0d4020019140444ca4081201000000f007080c071400c1e1440c0c8203403240d0f02c80c220854a654040e42c0c5110300035502480340031410381e04810302e0982403040c80c1031f0340341100952440030041000c49050b103801610b24080f00300386400f03100203405040700c90410555140020021000c00f0300a00e8000c52141108100e1140c0c080f034020310345006024442029040202c0000b04c168911f01100c1c02c0b070700c0201c4d40c1a00c62480e414886c2c1940140c20000e500241d070105000004561010850203564098841182c41d980b02c000483c09c9542ca00340c001c001640c0e50810380085041640400d501c400c001c000c4a5115440c2d4048a0035900110f02c4218200300c08181c0084418251034058500c000c164010440c0403000d505080c4e88a054a240e60b001d2845051050908da00d4240b0403009981c005c01c600314440c3c0e803a16281124014a8400d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 853846978 1250 853845728 853845737
    0x15020706050f041e03022109030a0f03020c030111030a0e01140c0a17040b1f05060c03040f0b090603070e0109090e0a150e030a1b0b180c061911010b030f0a0201 70
    0x360f41c40b450740d201315a000e881e00740e801000c0101c0c02e007040681d60342c2c0200425031440b2040c00310710382540e020000c4e08401c2e4070400045945000c50b00d00645880151030305039210381d041c513110780220200300e0140d940c0041c0e40c52002c030b100307101e082c2d580c0e00410400c07260f581c1d030868400030001d4003850340c4005d02003d80c46d81da444042801c0442071075140382051750000c04440d068008682d11014000510641506031040d1401c85546d810000713070b003540000018050740d0004142045064641005600203203000c8003070510f0881d0341d40014407144001405c0f4070620101c13121403607490740724440f030328050119800200511141501c100b550740140c110100c8491100501c00710700354119010341d20805150000035400c0a8207401d064421514803540d020384090034560315000318005103142d80c060002c00001c4040c2460703c03489541008070301614039000d100700f0444440c821090514004102105107006044c2d5070502c01d28a001d01800903020350b040c03240ca801c510603400d01180008055100740c86 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 853848228 1250 853846978 853847003
    0x5130b0c03070509040b0f0a090905060c04030201020309130e060403110d02070b04140102010f23070c031b080d0510080d0306050904020d0f0f0602120a0b090415020706050f04 77
    0x3120400e03200886041001500500007503140b802c0940101c400e03040024900304611012401141440015a0080c0c0c48075859030741c03400c180b1006118031500040c500c48010310b003a0a54001039030303034850358010b00e000d801140c4007105483d025034040103020391141c0680b40c050520f42401003c0c1400d07481b65a849000e019200066207000140420468080004c04c078242850020f00c043d02c0d1800304016810740d501c5d030444c1c0349000c1451042821490620155841030050314004070b4050b840140401d0034066094665008242c100000e2420441100d07041c1c1505d550910b0010702c030b400795004d503c20060030300b418011280e11440c036030704c11b843d51441100c80104008001b24103440c024810350340c00c0354456010401500b4055800a02940121046600101d250b07480000c2802001c40540740c0e01d41c08221002440c0c0301600064220380e600000b8401d0001803800629181d1001e4001400c41c0168030b02660b4140d02601601d0440b600900b040001d41740c901d0101403808411a02103da913111044c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 853849478 1250 853848228 853848241
    0x8011a090f16030507020c030604060c0e091b03070e10090e091914071a0a1d21010f02040608011802030403090e040c0504020f1201080106080312061305130b 69
    0x490a44100d800c0706002066042c401c0003034006003000303058501180103d44045035103071410040c0500030b6129100009081d60b000000809a220366001c0e41d100d85c1c03189090101001003100945503060341c7c603d820782e8036240d828041c2c2e4040d01e481c60440d08094400701c031090450700103140004403110200224115650083d049896441c014038420a02d6100940d0a0100d6504050721102c1e01c220310440c0c200c151a100100414200540c03c1c50185000103003445070030364810111404c0e80100d103002d04c40c0643d0400044d202c2100e9141e03d8280703000d4400995007001e030942029075409140c0004550340c0d82c0303401c5d0080c4000c07000d00811170740e0100c03034104004901003032003102d10482d010380e249500d80d401c080c104440381102400a6441c4404403a01144581c0c40340b005250b01604455055554600d0990381c041c4c4240c1640501e0b0b15914040007040807540200c201c1f810142e14ad100903425580c0d407800030b80b1050000c81000000c80c500020001084001c50b485070304603000b0090b2041558076013 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 853850728 1250 853849478 853849501
    0x60501080d1b060b1203130504050415020a350c0708070b0405250e10030b070c080705010e06070809010624050d151703041203050903030408011a09 65
    0x5640010024441c0e0b1070444640607407802004515110794804a0030744080c4d800203021801c140c91801003034100051009240e240611120b00400d0141c82c01d00076480d094894211001d00c41080c2c0300c400c0e800040402200b4030032400c106c6219038502e4104071520f01945c41c0c03500c4080c0c445555103d401c210300891040c01140c4180e446582c1d00c0003045d840c02c489950740d111541e0300504201c46c10300c82da40188281d80108041c00440504803460780c20303414680b42000143c000007414040741400803000a00200e240d42d00c0150380510542080280700d1143d10704200981724054018100d5442c1006000601d01e0210341a40249207a80d200403050b111080396a00300d45a034459000709090015030080381080020314100c0752001d6081050400e5143c80d003120580310840600355220b483c0840911100c0c412030260029000454001d41c2418244440e961040c801038001405010003c1007000d0070755010400c8078060b03c8070200a11000494090480910448000151007000e1000c00a520b24544 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 853851978 1250 853850728 853850743
    0xa0e070305100c0c11270702030d0b0105211b0c01060302090606160210050c030304110109080d120207080f0c03180612041101050415080105040f0b09011e0e01090906050108 76
    0x916261403074201000c0103054101d81001c081d4a00002d100900080d4401c0e0b04039200d24036540280d03958881d02b114820448408459413414448244040203454a20819496a00440c0c800310311964072005011091180e240550302040080010901840030043d04001c080700d02c00d4542180c1500c03020104101d501502e80d2007400041c0000c040e00240c94100d0401400503030030f0501518003c2c8076000d29066034422182640c034110440100740c07072968171080ea20000c3c20031a019140710607003008001d14207503a110400328000d40100d40c2c081804590421075040c03c20182d040395980ea4510080da03202c1d000401018845010003241d1134541c00d206085440401c154090950242d680343d4540c403030324962040c1d1a0412506010100325102c154156226401568030b40311803540c5081c00f00f0042d1303101c49084058a42c01d1a07403618080d21a10b004c603040d07590840c8c8500b000c0300229180050112260f2006000d0740031000000354a904550203e40a0740c003c440500c0680c3e244c000c8036a032884c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 853853228 1250 853851978 853851983
    0x504020f060a170a0e2a0604031202060c0c150c13080f28060f0b04050106030605150a0c02210d08010503160f090f0b131d060106090e0a0e070305100c0c 67
    0x401034010130740d1014144400041b10025001001301c15209010400a40203031b00121000310b90101c0514056404014040d481101d064180d464503180000340350b25110500c3c038495041c01c140300880d12200f410020f0b070760b0001324a138a0b100015601c0144580e241d00d0350351107410317502594071508a40890380041c0001c035901306041310050480c95842400130214044484902a541d5105611a42c1c9070302035140207001070b40e00800c81c0c07820101013204070441d4000c2c00040140400410f8446d503003115002c000d15404a840452000c0c100b0850506859000868002c0d07009410942103000d4002910354103071401a81103500c940c8031041d10103035002480c00f070b150008032290b1080000c070b00141c000c9200400001004600d02c58400c02080d5020940f031401c001d01a1200d84946031802c400b00c81d061680d110400030810765240c500041c000a21a000d802d40700781011002841a00341c1e600114140c20001048480344ca41da8200180c60b8441090348a0b84a42442004002d951160841210464 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 853854478 1250 853853228 853853233
    0x150e09060610230307200321100b090d0605013b0c0a0201140c0333010521040c180c050d090501150b07150e100504020f060a170a0e 58
    0x94160403c0080384c100030100c1e410420300c00380c0c12000301599940407440380c29010082d9110004c00ca60b02d00d08074954207441304d440310554100403d007072842c1c001104860711010419a9042c14001242c0242008280989100e00304000016400743c00e900091040c4002d1401d080710052140300070000c032205242c00340d0304410000c0441c080542203002080300341c006000001e500b0720200c1c60f038100100101c0b10071040c11000701c100100007190385042d00c0c400c1c1c4042ca500e580a85482030003a483d00c0d030607090604000000c14103032510046d040000d00a080d6034107140d0018a01442c0103994940729000b05003400e6a8412040044096030040184100e410340711b06080440703d1800000811840da810307a10b40d9200c240740d0a040004075002400b40028211040c1d07140213030f04002814505100c441941c551a011282e801c04e580400c072502030b4070410901280c01d85481c000502000404070740d15a06c840b001030070426040e00181d40407803020a142c1401d110365a5000203008884280d170300002c50340c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 853855728 1250 853854478 853854527
    0xb01030201091505120907080f0c03062d071b0b0403030f020a090b07080d02040e01062c1c1707050606030118030810080a060204091401050f04150e09060610 69
    0x21709500c18081c2e4814485c00407030300c032243c1c1c80780b9903880c2499045441215800c00b0241e00b205080074000030380c0c809003500303580c0e44501c21794201c0240f921045e1400741c0852500300101d44824071809450f4403201c00440d048140142d1802c00e01101401510204d0200e4a403e1100341550071138002d40c5c603008030355103c000849140c01d4030921264802c41d0210703040d07181004070f003d130703140b161000c2d0024141d45040c0066641c10b08034050060010b800061844420291446843e0340c002880e00440c80d40540d8030081c909469603469503a000400d10051112100d10112400d45200d100a1321101d4050f00445080e600d4510916089035403c1e58070040410303440801c040864080c1801d50342194101c14200803c5580305056800c101d01c1c91001c03100250009420007032480f00b80112089019042410801c0b5450000040c1c014800e0050160185854860115502808004480040c4070000844101e4505010080d448074811500da40c0701c0c0208007440e035002131150800354000358010400b1b800c103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 853856978 1250 853855728 853855747
    0x150c02030705010e1302130302091b09040e01020724110408030f0c0f1b0907020303090d030b13020409060e070c1a0a060510021605100e06071a040b01030201091505 72
    0x41c4c038000344085400804441c000c006500140c801040d0b803980903c0c404080d1411441004850100507280100c2401c10002030301c44c540e40c9074210f444500044900003000e11a000a06c3c0c003a0089c11005484040e03400704041c03a050181e070981148564400c0c2c2040308650f4030740c3d090014040c4d40030704045d503030043c04030106d1409004010300c1c024801c0d07022100f1366400c00d0201407618021a20b801c40301c545240c01100749003444803c0c00c0e0014102d00186056140c0002d80030740c2d4528004a0504154030741c0798440341621032806454802c2280392080d50340f151035828150140125100e910340076410f2000140e0124403681c1201c1c00305500c5008180d07501c6100308910003514018040150f801c0ea0340100203056501c40821011501c1c290f0050918140251000440c0304079030750002e4090055180c0d12001142c3c00340e141c0d01c0700c200c203e034415101c8645042940404015041070750380c0494281c140001c0c4444007810034102e80c400d80c0c550300100c0d00e0307070015000f50107040740c0c51001c02d2040c89800e50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 853858228 1250 853856978 853856987
    0x1090c0c080901090b19021e15040303060f14030c01030207080409050a0618150801050712091a090a06052409040501110d09110609030d050d11040e01150c0203070501 73
    0x42e10b00c030514114090a0701d89100200c5541b000980c0d20190003040b00807007125805200343c406040c07201c819207000c074000544054072082006200c0640101c502c0019040501aa006101600aa5515007001c0761254100e00a40d801c01490510a10440200440c2c96110b4003c8641c070307542c0503070203c1c149490150360030080e10000d041c0388582c0361500030103d00c0541c40a5441c481c0205041c0c0800c862015000c0c5100d5400c0c242c000080c2a4181400c00c003500790014103903140c3c2c415030803002600900c9820410b201038918095844100c0c0804180a0b03c2e010000340709145a00600040040303840d10070462884441481d41300300040e031100346c101154a407071042d05a200303020b400041a01c0305130785c00c135280960140e000031100035592591b80703051080c00c170403008242100b5249517180c0310403500042c4d44e13400101e10300300c108600010510010a1503421415074002540c10454030386860300c071880d00903c1c00b4000d802c01107400c2c407540580c00b0303c15910a9841900507000c0d001c414200401100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 853859478 1250 853858228 853858237
    0x20c0603090307080304030806090a06050121091a0f0c0307120209061e0c0d0509090c0c070b03010e01090e0a4115070c030503060f010c082101090c0c08 67
    0x500d40d010a00c003e01c04a58040c0042d84140d2090fa102c40d082d1074070100b0008007540140c039613400503180000901941c1d800005155819080e0b01c01e5120000300c441d070032000790a60a40003070030001c081200d94031980002e52600c0c0100300071403081c080c0d03030f03199101540d850200300d03251400520702910030318070400d0680c000c107205030740600240d2a010b03101004150b507144558204c45604c0d00001c003082201c0082c8110004c2c1070040c58000c0c03034a045e5a0004001103000f815104581200180040000303800700034103002000c10241454482da5101c10617012150b003480b0b2610700c07900b840780b902c0c40b512003c1884451164400b0041c000c0308015180c84a50383c2e15030f021520419601091085421124003202210348900c01c0146802e01544441d40828500a0008002c0c0110380200b03900003500007040e44c1d0b00c800b0a07240d1002d034041b580012a5003101d000c50203084590009240410302c00f030b03090314031451844c8002442c003990362080204110f41c8030f000150002410085c1e480f0026a12000070f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 853860728 1250 853859478 853859491
    0x21215011d13091a04030e0102070f030b09010212040302030310051c1202070b1c0c020c0904110301061206090c08060c0d051302100503190b1305090f010f09051c020c0603 75
    0x41280d001d9840d03c0b0102d900021340c10400040004000c00c02d51700181c04a0008020300c0035080e0b00b8641003981c448000e59000050201d405e280020f88810400d5056a092070400e00100f40325003002d040c041d441b40e20996010001d80b00c1140081000d051036020208a80e8854101c8014180300e902d640030401140f44116045025002e000a01d051400014041c9110004052100c0202c03404400080f181503041403010b54100c078418844907515911101e034480e030800d0440c21b61080900000e80140099048547c0ea420503801c0c00017803140c06d900c0b11090610512240c403886e41c80b022142e0366040f0407a4102e03144079040007810035040c014cc2205400003040e98808031074459950018103034440074944040043c10110401c0115046985078034040641004104000b00c40d8902150001d201321360940401c507107800c0410340881e001c01c003000d40044c1010080008280c0f0940301c1012b040081c1c0c09807100c1c840e910003501d545280d409400d00034201074008080241d00003052203919003004000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 853861978 1250 853860728 853860731
    0x905130b0306010617160c1506090603030905090723090d35030c12131505012619050a14060601030e011b03110d021215011d13 56
    0x542545040110902804c0552075080c4524411480800c0001004101c029100c0e90150074a103240d81040100c4100d94024141801c004000c0c91004040c1c00c40d6486400301c0c502e40300c0008245a0b01008450540d0001c0340c0b9185941c543da50211005144c5070784642b81003203074200b0401408130b1040103100115001e00f030940106102c1d140c4140c5207a10a0500b600c51003070800c00b8415041c4100c00800b0140031001d01421818030100c0d00d0b03103d0003441000414000307010045065000d481c40f0866640f540901c00034003034444040100041c100038400c668854000e50000c80f021600c074070a20030701c400c0c440000c0101c4400014a06502441128103035683c1c015150440e011030409042c09440140c581c00401e0f282c10040f0004040328040c12500610780d144c01c868422080300f552901a0380103103454041503810040c0d100d00c00d54480c401c240510310344005903e4502080c2285a90300c56045450540c003688050001900e08001d90580070014401d245051800c0f442d0960148001a083c80e00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 853863228 1250 853861978 853861991
    0x60f040e0313050904030f030f0e0a03030e01060f060507060b150f220e042012070e0705030c0d0207060207020406032a0f061b0f0c2103090513 63
    0x10504a498206500300300740c000062030401c1156070316054004200c01d0b20318100070300e01901c0052998018088070380402d52140c00d801e01c2c44615411084114541074141c501c11513040c90050028505041660095402c100001605004503410300c000c46180e034a409280043ca95600c0c8028a8030f8980703907900a00c003007041c1d1004407114000c0c00c40c6031500e0004603078a01400300500b125010b40907005000e0701030454107000c3e141304c8800701078000340d0043c03a00c0c000c0c80204100201c40080044003c1d00100074080c4000040000078041c03080320700901d001001d644a0301401c455521080b900c048448500b000440704581103503004180207806114014180700c200e40c0020159007050b030055071101c251741110803038045400d0918244c148210001c441082c5003079800120071905100700c2d4140052000341110004144a48004c2c0581c03040c100c0e0325442091130a076412114602843d0020b5100c2c1d5460960722800708180094581c0545a04420520384003c1050710007401d08a440c01a07103985 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 853864478 1250 853863228 853863259
    0xd2a06111614010c0e04020d060b2a030301051c03031103040b0702150609011202010905030105041b290a0314180d030b0d08032e030210081e06 63
    0x5001814055140d04181e541141404181d10200184903034490f458411a9101c1d10b8010a48600d031020070f580c0945c80d900f083c0300300402001141d02c041504440012070503a590148003000c24103e401382c0c009101842c1c120440d1740e9a0100340505a000018129410038404422104480e800d11074038000c500b9038400c0507802c81caa0415032b03017201c4c0c01d00c03203e040c45221501440b400303d440c617003900f050900f80b90032400600c290f04c041c41104ca0f1482c401071200150b9100c5d15012000d0300c4003800a02003402c081c90310415000075540c10450700b9241c40804a065400100002145a101111446500e0413007900e8041580400441010f0650305c21071004040c03200820280300e580c400120701d074150452917500b4100004c02d10385404041c03401c207140400750b460300c1720b0071100340e0841c007115200e9680000e030000c007088215600154000101010a503000400350400c01c2e06d10030b880109a5000c00351065035040e0042e00e42c8420304510740c88440007040740020b19607001000610900b501c15a50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 853865728 1250 853864478 853864511
    0xc060403082d09100c0b010506090d0506130204050f01030c0e190c0207090c0c0b0c0d090f050c182503060b0d0501030204061413090c050a0b0a020d2a06 67
    0x2c1e0901c000402011411070810b29081ca000031100f42203081c4904110120b41d2009055181400340e00c0c880c181c080388000e41d603204e072170009504a6005c82128418100f140050718044103400040303124900b01800103074500c0c4040001c1e8101c950010350034649904000c0105094900101a4401a80c480c403104514001c1c602034100444071940281c100907050224400c11740e054035880109001c1c40041c1c1d50002a0f15007505c81c0d110710700750500d545480802850101030544503001800605c208541e04007480302c0407522a15002c0101c0b2641c070b00b04040781004102d680100c4801c45007804d84003001980001d44403041e000d03000e4038940040e6041d11104040311681002c80e0703004205076034078014030031410709118030000b90202040c0f07405003440050014401081e641a080a22603d031110401006003100c40a009460003d0000040c540c884104815035000348402500621600322a01031142c0901940c45410341610b8003042d042c4002002c0b1030482160540c1100e483c0e680319403410520411 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 853866978 1250 853865728 853865797
    0x305040303140106051809070c030315090905030a0813021f120e16140f0d08040306020a0e041401060e060a0c0b0f09120c15040f0c03030509120c06040308 68
    0x1781c503010b031144c0003464100d1190221054090160504209000001d90064030301580701d50b040c03802190a140b00c0e0381c104004607199108010350360800306414200000407000d00403c23000703551110820b60343c022860200155450010750401c06041d01d04e2029584041240d111603001d04010086400480e001401c03030380d852600708140d03004201c0c103030105509450100018418001005c00c20a92100002c8001a0327400d0b41c940308441d41c0040c68104034043e01640c1c01181c015004644404032081c001d01968440001644140c1c2b03040d10b170030720b656000b10f001c60584189990344060001c6501c18007600c0d500c0a14100c060000e04150100080c0c0c907055000d126111551841556081c10284070f458a403024074480034400c0207201d00f400e010301c00154441c1543c02010711881540742e9080c0000e80300d5188101a00d0030444410220505400400810044c2e406648540a145168410544a01c07040006646c070240400c0200081005030001c0c20b07400015500b5040e0009800b000300208020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 853868228 1250 853866978 853866989
    0x1090209090705270f060d06240b1606020c01090c171204080303070c03030e0610033f02010e0a050a02040f0506031c050f040e0a05010602031903050403031401 70
    0x1c01080c030140c02c2150010034540030152141244c0501c0000d40030081000608a03152100320310700091196a44214400400c0d402c044104403d85021560704000400c0f01005882e10f51078600c0004c10041080c01c13541d49240b84000100c1805050b40c80c1d8000e54444846500a5034865250300045000001010014503080300a40b003003c001c1c5520034205080c2640205c02030b03a0a0004212a5030040102ca80c000720743d10b0f0164180c560f900e000d030000d000d1886901c146204500c20004008110803040054a0041c800b402440259000b0480c8000c0d07040900c0c40c031070400802401110a2401800795101d40781d000106c0e80c9116500c10500d4180907507415507007036002440035020741c24644984108000e50603003d021601c3d0440100b82d45080e00080070f070510001d00424103486115034103071200c100b402e40c00a5a6a0f03954504542d5800c01916106011444c280c000500c01e4000000c640101460003400c5290012558060f401010300500075401d15880c5c1c500b040c00b688210600901808 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 853869478 1250 853868228 853868233
    0x170919030b060103290102031b2a0f1c0f08040905100f1502010603080d0b0a09090302060c0309010b09070309030336080d020301091b030207020109170109020909 71
    0x18554284541100c10103008141131518004035071294000c0406041404544840600d0804540400403441e600c12040c150710090004619280b41c450003041906c14031a500030202c40d1724640404148254150a55850f800002c80c0210034040c2070003400c1550044400e848220b10020300e4845400c01070014904950314140018244043c4803031b4030a00303401c20510b0040300780c11401e0100f06d10300d5004900640c18601c4102d983d20504ca80700f5044440915445403456868401c40009900a40340102400d8824503210301c0115120006100340b804080d015401013801c0d4445944960281c2e00140801d0707a107540741d00103003110340c641080c440e001e403103280d0b0009a81320f003c0c140203045550790a0702c000411000188101152070540e01d5500d100c170740c0b102c00e00aa48161030440054400c0c0214003e80340d0001c400000d450800da4410403001d00c4107804803804040300c0000302c04a1081510081c04910815001e100201380c1038480341000c440c800000980010341d8002a05105003158169040da = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 853870728 1250 853869478 853869529
    0x15090803160b0c03100308072907020c0619080612060f01242a020d0b0105010801081609150815090709090b060607020307030c030c0e1605071709 64
    0x81003540b205540701d00580300755801c508000301d98200611607440085c261210106841d012310055007400c1d2003400158a4020075450400c3c1014500c2d03808a9403400076025608a5030010308125007110781e01c4403044c140300d8032241940415103820501402068020201401c4600340300340421401e0700400003003250700b45940c54028049030741c02031405500c02040c0e441d1007030700503560800307000d03c000100c4140c92800083c40500c4100d0b13200f8411000796120801c1a010001d0100c2a4441416240300b0380e504040e503a21549040d54032898081e85880041c0d00100401c24805254480140d5800b2042c4070388032559652455441e000321952070007030358681c030020301c40f46840070041c410040240c4142440b80b10001d4681c9004400024031080c020040041c0360011590300780000030155a001080c5a46261282080f0840e031403d40102d0940c0d50000b0003280c002d100040880e0100d18441c0c0e0b61078034040762660703185203e10001e0122520b81c80140a0700c1255512182030007a194510b00c03910b18607 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 853871978 1250 853870728 853870733
    0x2b111e041a04091109100807030e0304240224100314010203070e010e06070311100501060c03020c03010902090a1509020a0f020606181605040305030721020d08011509080316 76
    0x4441c0303401e0b2044e00d280d500304030340d800c69114144400a00407403400d19449564a07440d0540180c0103c0304002d90354000001c010512040b400c0c1c0d103207881880940302d90314001351032800760703a250031401c03400310944015600241c0400400a103076510402a1100101c290307602d54400b82c0300300c10508038204a9402004014410354010384103220340b0801d10340b0200303070b40d02400800d80c41d1051b48005402c2003400f240348072800c0710400181c0f07049a100401001650382d54200140b56148045040f401401f40c00740d0202503140c140100b203101d0b40c004100c0f1086171150341006005002094644d034003050540d03000200c480c01351000c3e10650903280c540c1d507442240396000900b000001001c41e4403030404040705407410445151031540c0030001c80d000340d0000110003820398150169a1004002d0311002508404004007e00c1052240b184a00b11100c0c00044010a0b03031128524503001c0000349440c80100080c4007940c556003010489420103052041c0c071500c8003030455102d0030541e0100302d20003007070404 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 853873228 1250 853871978 853871981
    0x121c1d0102121606020909010602010b01090b0418050604090506011e0807150c03051905072114030622060e010e040c031212022b111e041a0409 63
    0xa0010003440500103001c0508119030031801141c8840c0b81e1060504242c80c01c01c4102e034111b0b01c1d98103004000c100c8641e910740c0c0c002d003e0844070080381e001407242e02001540030503500076030b01070b81c00481700c002084076460401401414002c0559034841d0301c801a00d400301e0000d010542c0a0210317207507440301111400c01600c1e07082d10a42c0c00950698030400d000c01c9415070760b1503600600c6480703141903202c0c00540e0504840900510307400f0040549550300654045400200501d411441000d2890f0b2070710b943c01510510281040e621310129490714401401d5421200c025540054014608000078001c0c0b5003000e50313141c03c031040b5002140e5170320381130241000c22074005004260a1501c2101850a550b568a082d6680d1000030444200e105a04200302e00400c868028140e0016045460768004c0354400e030546141103807c80c90b801150a4240340f40400d000b0303c01d1014140003141c0ca00b0b420403d201004859061001c0c41070b5009210106d680528620b0543c1c40302e401c00300107919103082415200 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 853874478 1250 853873228 853873277
    0xd0507031a180c07020d05061003020418030509010c1518021908120307021c0e0906010e010c0b040f0503030c13050d0201080408031306020c0f120315121c 68
    0x510030160714544628508620b070803554804412400300c1d448260610204400350044075006055001c2c480410400b40460031800003103c0c02103809003c41c100003080102d10140c2000040c000030001c000041040d4042d2510ce00b14a00c01c0850854148024020004035001c001081013380c0d01c0413040c3c415803420b150660302d42d01d00c2e030f4071098a142c0b5104105980f250104401e00700c01c94080300180540703000f0304c860a2040041b9089803911000610000c1008010b4041507200e2000c9202088103548641c510424605042e113583d003036030b000342d00d8100c2d095a0081041b07525400304c2c1a4640000c40510280d8001d1048a050b152a41d10ba460101c907110041d40249006440083da03030030161303900071380f2150825001030010740d8a446080c4440d10f1034124100c0585140c0c000143c188500e40b00142d00f50380090342e00255517881000d80751429186c0b0044e1200001070a0b032002a94103807130701c51000b0521486250880301d031450000140d07802015030150600110b103500d07459188040c5001f0359813 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 853875728 1250 853874478 853874531
    0x91201020313021e03060403080106032003060d2a03021c02150c21030a0c050301030c1502033108190320010e01050105040b0d0c0603090303020d050703 67
    0xe5046240c010705004030071075a1000a07124200000002c0b00c6a030740001000c500c254060252a4245890304014001600030310400c0002841c2100c4405001c01401c228521a100da03040c1600d9a20f400c42080840c5054800694440725481030b85480006110841c1d036105861042c8410001c0c0741d40108002100410540f403452900700d000c03403005075940c20b0300d051030365041104203840301c5a59011618101c0c0348044401003e201a000c1000554a6801b4503c1011f40c500f0900580c1440c01e01103459000c00c0c07200034119003681d030040c0441480303c02c031240001c20600c12070f402d00d0000000e14120800e00d01c208140039a03e0380740382c0303103940326a40818041c0281000034a900c1c00d115001ca4050b511000010f010420b540e140301c061540b42c0400c1d41c1000030314000030b010030601501198002c11081c400d042c8038614180c80041c40d1308010010b412019000705800010620705401913024040c840e00440405900700300d40d071503840151154034010340080e60005074016400016030700c81028071441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 853876978 1250 853875728 853875731
    0x6040614010f0603051302030d0c050628110f070303091502070b0f1008010c02010501050306090706021f02090a090b13061401110a0b011508010f14010e0307080106080102091201 78
    0x18040d840c801e11526003110020f260020755a07881046c0c00c0312080844000a500d0b00a10399205465030380403074100341c66800750f01581c0d05510396001050400c149818005a40d85040c0958600d24842d580181d00040c03030035007c07915207404a0b030b4040e000e9000780411008690f440158000340801c259980c415070520440031441c1864548685002020042440c29403c45c21400914402c080c8200d22000303100c01d4000344a012601a00a4083c04c02405464000c3c0314503000a180454001100320407614650003405034017180614261035003070a140e400802613020020b182458440225190041c050f540c00003a4003050342c0100080c0301c55021245405038206a01130150750302e850820300310080c090070104408142145054104800381e04060103e00c0d2420002540b031700100c0c002844101c1d9541e031008980c0c2c86101e007018011042c0151100021101c1410040d94021001602c3e0340500030200c44005d980d82d140c50b42581d9054101103081d9401203901c9200e81000203070340c510010013500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 853878228 1250 853876978 853876981
    0x1b1505031b03010f092d02091504062a0507030b0708060409030509100903020a1e1a04091a04050a020a020c1816050f030f06120a17130f0806040614 65
    0x80c40e490005003400703005d034010b595400400414000c013070864800301ca0310150301c1d0715541111408000f5000041260b00038843d200d0a02c0620504000300c60079075942e51602c14881b94481c6c000b40000540c3d45400d444011036065a43c0800ca00b00445002140b0461380899503180508004100780400381c1540c1c090340c1405049000650050b081c0c801100d400da81501801c2a8148200c0321091a40d0019400c800b40c0c22000c1600c6031240c48111312203040d10442c51441781da460715181c00c0720202280003510142032000388085220350701318090701c030341c0c07501110180700700900002d04440d000d44510b81c1c1958005542405240c060090304602082210700030f1303651421040124000c1e4000340640101b0802e08010080c0038041c0d001e45000c40c143d001c00e982c803490400d055207a4030005907050b81c03080c0c584808584503207400003910160070390300200319540d17100700240d41403a540100300c2c000d001a003040070202d442420718002e200244108070040450341000c0c00e24008498452410100741000c100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 853879478 1250 853878228 853878239
    0xe15041803020a12120617010b0105160f1718030106050d0b010b0d061a0c06060a03050d0c02210a0b1609060c080f0a17010b090109031b1505031b0301 66
    0x501e80702401c0d04015034041308000d030701003141e03500c2c84800d01d84c1d0f5061800501060300e5842c1e101c400402103800d0002c00c14111048015141406000440c5001503103113030000000039035001ea40102d80d807058070041683c400900b4009000d400003a24440c0c0f0341103080f0380030b5075440c1c240038000041c0419141407052004646500152034014090709056180003d400718001d28194010300040503e1244030803100706a040490065001d6400482c50b07100c1c00e4003186052a20031105000c8942c0040141000b0240304000e442c0c0700b01d40304043e80e001006d040c9210b0725810b07400b000190101d0200c0503002c1841ca51800004081c409480c642042e40400710584d070741c0e40c0010159003943c2c01070074156061071440c5040107007403080b01c0c83c0045500c0046488025541c00901181458a60754a00f0b00c09a07244d64100725a03003e000760b014006800c041040010442c00d190003100c44d08000c007141c43c2d4945070150b00040200f083c5814002800010030400c1030758502210101910750b24001900c0c5503d0003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 853880728 1250 853879478 853879483
    0xc100f0b100e0307050f01050703030e0c0a0308121b180f040f020c010509060702283c05030a051c02030c1908061806060706110309010606030e03180a0e1504180302 72
    0x814024281034cc2c071820b11070600e80400240003000320080502c50303440c1d242e00e040211600070041d040c004012101c041609400202001e1559031f100321781041c213080f0840340782c800300e0b8500d9402a0300320b040c51201d4803c130b49550051904500d844240941e541841c60010b60854900604541d850b030800d0082c050900e5002c00c90800408681100c0308021900481440c90703255140e03001010140ba000c003a482c0f44128503540f515000d42c12000e10200c10500316142d1000c3c0c12100d006200360002c1025000f00e90188019210300404041d203030039404907645414007240d00561380718031006000300d13121480046004000c11066a035183c140703e1800d10034017045030f4035481070480f0b501c84680380000308143c41c0c9205564100ea0004028040322107820a405400d40c415a100c030403075402c104010500902134007402d520040340c54011407605141c0c00080a500329003056080d480154140001464800151028010705070101c407503004100d10410441282c5042103040320301004010a07001080d0007 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 853881978 1250 853880728 853880737
    0x12030e01152c0a15270e031903050903042105060c0c120906090d06090b1e01050f1203070c0915140103050702031b0a060507050c100f0b100e0307050f0105 68
    0x208001040e80095011111541103064102c45225080c03624400d160303216141c5c4030030112410680400c2052002c0914940b01d208000c5140248460724a19a008034440e81c0081e41c00500501078030b043c1360b1191064562415030803922960061800881014850140409034005442480c1245400c0b080c0d1859519048040000e2420300343c003080c07800e0261130300d908035410084000d200080d140c0c03d52419000404402070305440400c6620001521815042d14907445000c040000321120b81c40c0000b00049040540010398010103446540c0758110701c100060421188210019010f050400c0c83c0e10085401380f805841070a100401c040006000c020300c6000489420718010032956211182681b0354840c03070000000c2846282240c0e9000b03d00801c080c030740c09109003400e000c252980c0b034040f81c07607010301612081907401410307078500044915880240340b800c03004008980174240a00242c09005210503040c0810001c84040c404c1d03203400d0000d0310180004030b4002445802d2000000c219008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 853883228 1250 853881978 853881991
    0x100504021e0607060906020d14060a0e090705090c0c060a02130b0a1e0507140d0e12010e01020301060e030c1e040b0409080c03071e020102060412030e01152c 69
    0x903607409480d11034440c40100d405480c0c000b03406014080b03c5141900c000d40c00b07401c44052151030010034000240d1000741241c0503280c02850141d8450501040c1d01000c0b4002e040d0b250f461040d89400506a20742c074110390f1007480d192805584402e40303408901c0c02c01400400e80c9a540e48108003034100400380d10003001c20758200350750650303c882000400343c44070000403180411460800d84120906d940c0304d0010b000c01481801029504040c1c15150f0341d640e110910301030003142c00c1c4020030003035040c456912411210600300224101c100d50301040e0881c0d00a0700820002480b00e03c0c1c928060404114160010f1010344034103d40340d680001900071840d10082151040740c0300c29000a480e0b41e0394220381d200c19040304046035500302c820001980d95001c0c410403a0702200c0c41d1404416040750102021040e601a00a4915580c0320f50351a8030203104c481c041c070f007030541c1c0f900391014410b024410b00c40c1034041c3c0d20000030700c2c900704415909400303c10b92140540381100a090300c002040c04d0013181c2c1022 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 853884478 1250 853883228 853883269
    0xe010f1d060301090c0b09040621030e01020a150902120615010f022e0b090c09060310120506010f0b16060f14040c030c05090c1206030708070b040810050402 69
    0x1103401c4002800760001800c00313003802034240c1c8045a420000c40c0107148030402140c0402c07495545a500c8600384000186005000c0070341e85100c000f103802000100300b0342c03d051050790701c01102590361100049180d19015500d80e036402e0140210f090010344040041c6000c03004065a14040c00307041520a6103201d02d41c1044135203040245858000c00c80c80100400702100139503c00c02d5041d60120707180820700c010002e40d04142010b8244d0900d54110b5001e0304011100502e404007a01c1809851b80c40170744503040e58107020f040040c00341e0104610200b041c5c420710152180b949084c0d99014100c01c203070441500b44c241040440081e40e41007075544405c0c0e0380400b001c40c6418031020b00784c3c01008665110380520051004000c200300440d00d488003584d00c6090309d468840e85400038030090386403c481d142014641000719942007031a03129556031041d801000c440c04c0e19100d94200d41081d100e81c2c00a811070a000c10107015801d0700f407120078040c070460082040540f030150001040b004010b400103c022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 853885728 1250 853884478 853884481
    0x9060315030c0301020d050907050a0f0e04150c03020c0d0e03070303110a050303070f0306060915182c15060f0a14160308090604080f09060d0908040e010f1d 69
    0x381c80c144854203116600400840d102c06200c032441d405040c0440d000c1c110340c010f00e01c0108180c0b500c2520007047d15400304480130b446042c015003560344030010b0070586105a02c0126031405803007038080c0c8440c0350299500540c45208459009241a0056038000c05100ca40e40c0c84c071400ba1070000d03802d01102e8142c035100c100011003221007801c00d0410040a00b4074007001003000034043c2c1003000400100354590b02046072030354491044030b689620b4052101ca03807a103044882042480340342e248050800030008610384030b07551291081e10105100c0f1030034022200501c400922703003940c42e400d6403080c8100005502094a203001540511903039400741c0030608089424440d09104655401c21300c100b0200140c2d0360800e0088581c4c1c5401d031740204600003062080014825440407440c0b900a0343d10031522410400c400d060038605030446103400740c008500b4002c400e002000c60152600c4140202080c07030351a402e01040744495441604280c5420003140000c1128403100d10303299100c200e141c0743c0388189 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 853886978 1250 853885728 853885771
    0x1b0a0c0f0806180c011b02060301270c080a051e09010618090b0103080703021c020a060e030a32040e012408130c0e160905030c03031204050304030233090603 69
    0x806d800c650042e400c07001c04030020070305004421020300b11161a0007808110301c02514080c2c1501c0003032114a00054041010404641190300b00ca600202c0c148a84040c101c0030700200c01280200b11524100d0341e4503003004209041040110f14174035402400c0500c0f480016464401104c101844002c107003100002c0c04006042c4244145144820004444be4141d20724500007540c85d00409004d80b0340c68a010201d00c2046800130031a00d4800c21600e441d210030001d100c036069120041410503000c10700003c01d0f00840e21a030340048c1301400c40c00d10984000d5040150360071341010002102c40003a402c140300920315640040c11903a02c036146d860038003550702952400c40340d155034640c080503031345041c0c0c400d10221403084400c0036880042a0b9498400c00d03230b5036081582c0d441d9a00b01164254004100c041c1010901c03e9001d9801805032007181e01c0c1590300d40c082000c030380d10301e481c558802e804d45026550106111038210750030380210041030b04000d0200300085d40c0307110103060701e401a50400180c110 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 853888228 1250 853886978 853887017
    0x11e03170906072009070f0c0203030f1c20031302150403030201020705101b030203101502030409051308033907020906060406051b0a0c0f0806180c01 66
    0xd141c1c9000e046252116440d00d031105401d2448444441c050804404850540c00c1980115104001c00e698542d0f048180c0c0905a40031101ca034170680c2c140c0420842040340580c07a20007020a8240350304644d041505c1150110221016010b50b403483c2031044c90125041031075041660303040001401700880b440040e2000694000382c0300c0800648503404140027042c5030701940070704042c500400c1620141c000702084007040300c6c501c0240c4400880304030b1541042d18400d40c00b860b031241c84d591800c581c5a80300ea4800089558110b16600141d00004060048010324007840381c1100e400c450b1070200364255076a2030241c0c0001002250340c603d460b5840482d40c0b440a00c0340b562803948840408002d080182e150115a008a0003640600a0400403903406e0130302c0000c460486505540b050304081d00c1c0d03911a1030481d20f241c080701d8544685003902c00880c0d6290342c0744006280408548182d1485c000d202c07424014000e081c2c105400c095102a0f4082001164004100c2403d00c0e1000d00003901000010 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 853889478 1250 853888228 853888237
    0x204030204060b0406110a031e0302070b0f040c08010209130f181b0e0103020303031f0f0f03060b0111122505010b0321090108070509190509011e0317 66
    0x294441d042c40ca00080c142803800041098507901d171b952952501c020140c1c581d4030924400010001100804c889607010941207558408520920300075152840360f07140c84803686002e54207481811543d0b4144000c0110450048000f01508070003941402c2251001403031825004422500e0701d500c03041d0004540c1e90683c071007422016000b111169001749420f101c20181260301481c845903d84000116020141c5040035040700d50040095103141e450307084402800c980c04000c44012580a0b10106141920100410107016041e86a41425180d4103041e4180c803407216101e8144503c00c444251200804610b45a6120240309213076500c0200d44584d1180500e024a80c00c011031210100d08100103064004020b4514114222081d14041e80909071400310f0207104400c601c07600300300c83c5440354021040e00343d1210072400c0c020b0034418500003140c1c40481901808280c034030003079014052460f210301d41502500b5000d00c82c101c100500650f904106c1d616020103800000e840c03440031554a1500201c9 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 853890728 1250 853889478 853889483
    0x60807050705011b110f070302040e1504060509061b0904051b0705070e1f0e150d0b0702071403100b04060515031044030313020901050a06050306060c01020403 70
    0x4c10090910842041220340c071046414001451071104904680001030020501d41d400000341000f10b246a003044001c200291491010780100c07101c2642d155201d030921803107035014010108603442c00582160500000a044034036a0340000c1c0c1200c4000d60b02020b0b20251081502c0001d0607460304103518458414061484020800014094081080c04102c00c0116481000c01c04029100d10088080c070340158081c031252004031720800c0240818084100ba041501d113401c00940b10ba0b1000442d20400441c0070666129020000b80907800d64104400f100610a500850004030701e0480002d40300c0906011141000b0f03116078080025550f947c2c03104004000091102110140f00850880d443e04121111b8114094030381002501d2039030310310320300384503408442c2681441d8842c030b00003101d40004440318a9240908400204240c0c401c20045010700c1e001c0182049084140c4104281d504058002c3e80c01020f051804200300c0d9008019203030081401c81d106511020004001402401164400b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 853891978 1250 853890728 853890731
    0x1a0310060c030e101808070b090d1b141206091902150a0801030b010b090607082505030910111506030a050706030b13290d020a0b03090d020a0c06080705070501 70
    0x80b6519822030703c010500c0e904131905e5040b0655030001c00d500c4101c24030500300d00d071000b08035802d090310344800b6145a081c4207518045c520305a00080b4480c0c050242c004501409688020034800d1810030800f08000c44070302c0003016103142c200c00854480340c0c200900d4150b000744007810011035807408107003241541003141c0aa207135882c031240280313520420b00c0150341c048c003030030000701d1001c0c0a5001c5031180040909144e242c1040e03030352460001e034010f10075410600c00c0c031058440701c0040d05034a000003901070401551241424030800103001014040ca0b01404282da51104c0c480b000490b00c03c0d0703041c14a900d26483c4d59150300200381400d05c04000101700b4040e0f0003004c9070f890f8140d8860701e01030740d0554071042a000b02503030282c11140a035440e0a810452001402c400408402c3c4146d0b13480707030140500f244040c2503030102d044843c6541069510040110404c21032040c10811a004142d4038401400020020380f01d408003502d0900441c000c12007280002407000b40100102c40805600100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 853893228 1250 853891978 853891999
    0x10b041107110307030b041209050316050405090705130902060c060903130e04030c121b030507060b0405010308250c1706010b03160e030f030705071a0310060c030e 72
    0x11404440d0701204040350032072a0690b10010302d003000980304003560b600032a510030545454a600758100451202c8504020b402017010403aa18181b022010b000c16841c40340d0004c41c00d0504001c10b036030340105982d210740e200329020041035907002d072800002c660b05c000015011849001241c0b0074030405a501445128042c1840031058000000302294451f02401804958803082c0781d214038030050714083c001034010b503a2100030560041100c643c03504c4908000f4081560106110071403c0001410350208001003240c80034441680074503040c04508917000c019075811580e03100203038003130003444444c180c00040c5480340440703226000c4804281c0240c1114402030361465403094803402c020203140c05000c2d85e400010008000384c1900d0040e2410318242400d640c140e8821103041c3c141102c1550301d44200491103503940b4061001f446560300500203040603a0a2007448003040c02084041d0b0800c003c1082002045540458948151500c5162007840d032106400c0071a0741c2220100e220364030000c45030707 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 853894478 1250 853893228 853893251
    0x6050703110c1c0c0522050a09030804020118031209030b250807091a040801200d0903050405150307180e010b0304140f03031503060103020a120f060222051f11010b04 73
    0x10f021b0780020401c1d0003484290340318104901601c00103c0010081032416011600640c0654004c0c0350300007036104908603884d96074031990ba2400c1d400700310ba00895120101070090050800446500014042626076020f01c2c404401c40301c0b1082c098000b04200d007030000308941503c140b54500050070300104100441c011000010107a60142c4582d00c504c0d0300c0d04120b100282103102516048800b034100050800114032100f0f0043c014910048081110801c0046581d9860003150800300007101c22990300d900d00400c0c0135202d6103c140781e14800e50144541006144601411141581c1c08100000c0d101d8850346064503800a8624113003205020310f031144103c1d050000040c601c40c402c02e82c1000440c0400c6424541ca4003400c1c04003a4010f98506d84c00c1c4800916889581041c61080d100350b0124403903615074004a8100b4400170400c0100034209401400c182c00d0b820026080c00c44618910404010030240707860401c58140d0140001d0341e0031a940320400307500c040903114002e8810710040d6281c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 853895728 1250 853894478 853894519
    0x8130b041a0106030f1a0a0e060312030a05010e070c050a082a060703150509010b030702030702030703050f480d0c0f090608060411030a0c06050703110c1c0c05 70
    0xb994200018a02400131030107200c541b100c0840340001034130b0205882c2c1000d24156201c00c006011503050702c94007018221410030440110300c00c4524010001d400d5040821002c441c442c094a0801040a00200a4045400410310342e503101e0380102e0040e07544201c441d274881c940010f4048074000c0700e031303105000d4030300c00000c10308e244100401e680801c0045e030340d5140300e0b400780100e010302d64000090000601c13000303000000841c6c02003042d00407642004455400203107001c0c4140c0048441343c11106170320070400002c1021401151041c03a5840490040e00c46415000310b100816907068054442c41c40d40d41003c1c400c805104160103000c00e00004462b0400070441103c510800e01500110240003070440d00030300ca40d4040e0794401c0c010340b0300d98440f9241c1c0d507481c1800850459040c05440003400c009414a081c03400203112030f4948a403200901d05014085a142c0110a41c1d96000741075045aa691902c12a4104075000d080c0c00c180400306040000c40c15289800c07442c2c101300d0030b000201d01c10700d0f031 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 853896978 1250 853895728 853895741
    0xa14030708041103071d0c0d060b07211e1403100f15020a02100302040f090603140607021f0f02030702010603051608120903010216060f0c08130b041a010603 69
    0x2607502c001c1c2200e014014076541d5134680c805e010308681e0251b42460f80348010a6440e0b00203548410503414000616176901c12190582d1108000c0301000031064100405070040140c000c01d105d140c1041400d525801910307840c9241d008189114484100d494524007070000203900c45d0003401d4160322072601040004509000c3d00030340d90311840c10800068640001001c01010f040e156016181902050307091101c810400040c41c01455003c0c0000708141001c00d16200041414000c0480d14901c0c500340120744403000440079125400c00c0c410450016000504006071444c01d281141200035034001c01350060110414070740b4203a000205100c04d06905400c09400e0b81e0046040d42c4004000740d01c00c900250b0240328040d4540c00404160071081442c90250034482d4020b0f0003d440e00b45006030b5420551440341c01156007540e80c1c404803124036124820405408141e091803041400e2200d890003000041c0c0c40000c000101d07c00000b410411748200ca9101060300781c48405455840e800041c0c007410303c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 853898228 1250 853896978 853896983
    0x1706210606121f0e1906050402011d030706081f120b09070303210209121506060903030715020c061905100e0402130e030412062f0a1403070804 63
    0xc0400b00c40041a401040c2c0d201d425142401240c8120510301c050406481028801100c3c0c4c029065500d440102c2e2030019043c040c4034a5002071185054030015010b07101410041040502c84915080503450005202050701e045003401c00150744c400101842050140001401940c0c0b4050b0000b6611500206904210701c662103c0045a403422419036036508a444080c0008101c00348046d5030458031456020100100c0700098602401000802e10320541c945104440d0307442040502d0000700542c07080c0b600894102d41300c51a009840e4002940c0f402046405485031015100201424040c2c1c0d0480342c42d1000d600503240c182c82c0902907902c0380d1404002c0d00315058104000919207001e1313542d400d000e07641140120025900c0725000d106010320f0303095442c3c0b90155108103174076207584108054401001942c1c400306e446c147c40e00d4041c060340c00542403201d20303001c20341031490070414841001031095500201144c42d29114001241c5441c10001c011405c2d840000030f001c1e9441c0e120114500c901e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 853899478 1250 853898228 853898239
    0x33090c0b030c030109090f0c0e330402030a0b041104081006062127140d0206010b031e01030b0601030b0d1115090a0b04180c1706210606 60
    0x150398400e1009244411a09524006000c00051041300210f9004025017801408204011005591404c0c60040c1641187d508090744408104103035075a800080c0c0b0070241351000040e520044038a07165049030940d41c5500c65a0040000792a0100c25404403004000c000c1c01401404014003152541d0f6010740980c8105006841d0b50000d59400d41c05142e007140c00c1c0b03a5940e43c0300001101d90500341070b80648400419a140d07581d004e500800c0d01a20720408403000200b04400040d4600007210842902ca6004640c10a084d11690940c010451f03c1c1165000a0459925592000c903003440092905047c81c3c8070400038008401c0c403030301c0a12588100820b0320100260205401004410420000c3c003c1640810503440110f40c01c10a2041507448210032200b810110400005031421040740c10072120944080350401c060402150030541418000348100100d40c214034000741000507425851203c4e044030004a80c00745c440f40c00c0800085c02c821000c00c9090340940b4410b0f110882560380b2807181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 853900728 1250 853899478 853899503
    0xa080601120605031002071e03020d0e1203041a0706110403141902040f0b0406032a060c080f1213050d020706020a11011e021c0306080a3309 62
    0x10501c282c02c1543c070020000d143da03004c803004840180d486a10700300c0301103a41d44010b0801071625a141900036200703030041e02400c1c58000000b00203640a10f803451140413031062a589100c4040121019140314050810a040055200e1040c5102d1034030000d01080c50314a0400b5400115000b90042d2403140d00c040000c52100c0c9185940c540a203450340912200d80d8035001e005241c1a0b0191901691024011403d40407400006044811942c026682e081408079420000b0540c940c8410000788607841205026080000042803402c003c070008080007000140c2310080300720901070720700710328400362091154078022416604400c0c1c00002100c0600c039038000c061405002107158821380c1d10b194020018202942c03140f519001456404a0500803450303800c01d042004000003651000e03094008085800340c1a1510b600755000107440d600b0545411420300403c0741c0856134541881c1c20a21255440d60402c21910741503190b035030815202241e072403201045003015002140424042d51096844 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 853901978 1250 853900728 853900757
    0x5060c07060806062119060e09061e0c0310030803011e0506390303090d18050d320703060b0a06080c0c01060e0c0d05100803041401020a05030a080601 66
    0x101c0c002c68981d03604841c00403003054914030541c405142e221408007404110350b94046d0b01c41d81201c2c1e40d41c00034494404000100407900c41c00304040c50300600c40c2c005602c03010b51203110b0399190440242500c0c0c0c956034000045804904180350500c040c2d80c01c11082a900d594640749d00c542301041c18052081c0000f1481d000416141007030a80340e82001105410000c81d0540d0301078120a0840b00c0d0400e031050480c5910f8800640401c003440c07141075510014440603c20742005829881c4c6c0104610f24001c050b401031003980c0f500c00140c0d802e03a80c032107000c02078154912001030403030320440c0c0071001401c10b2400074003114600041690403039008102c00c006840b200c805000056449010310804241000301042c140b100c800c001b000c04800790800003420719250a21411304941c00d071450480e4140c0407540082c0200e061241c01d400a0881e40d5035120703e031a00300c04645a0149104246500000301041d0599134000c1c8803c0c40b0099101050380d46c0c4610010002d01184801d81d00c0782e0014040d01828042e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 853903228 1250 853901978 853901989
    0xd110f0a0503030a0906020403051606080108010213060813051626031b1002030106050d050609190c02070b03041a0c0a0207030f02130207050a0b0a090308040f0c05060c07060806 78
    0x403680e008800742d4030303655851200c5400390201650489401d5404c01000010481c01e105103802c54505002080e81e051500e03030300400300241a000580164030401c2602200295500c550342116443d0a040310361b540c4d0071420404282180401a0050180410000b04012860300c0c20013610203040d0180038015199a07010665080340f401c510141e0300421101c14242407052086185c0007000003103070000d5001980c05c505a030801c0e0701000104201044040c000c103202d00a913030340034009440c948070926200b91802221841c8502052205564078010800d00344203100b1940a041d20710b1410381e680c20a031070581914580c40c0c09000c1c1e004081c10104092018003012560302401d01c0c1e006008a60542d110085605880d0904036440703440345260410a0750140003034002d150042d409030040784414200b005079240e008260066483c90105c0300300c002900103130602c1c0c21a401007490b800d40d01081c605002e150040b5081a50f101c100464034a22419000520300c080e50080d58a8111a44441c1705204 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 853904478 1250 853903228 853903243
    0x7050411120408030a1b020f0706080915180a0f050d030506030d08070513120302070b03011a030a1808040617060901150201110a0521160f110d110f 65
    0x100e4540c15800454081100b01000c3c580042c0e014000107034005186c2510804000ea51140401603000001c02050051060101200911190801103d1441d0800045441c0c0148820940c070035540c10010440c9111880100c0e110301000b5001c898282056003811180e00030414403c80e4075104003070010300114842c0c000c041c09100e0280c001c0412610b840000d07511b07a01d0052100c070404c43c0a02c0a014200c04004801c0700411029254024000c01410000d06046841e000704030b40c65420801003120700c4101c02e0085c4503200c040a01c40e12502c41203c46c0d0080c201a8004000102c0b51100340414403d4030001402118100c0c2c075003400701c85d030b04404501344010481d0b1150b0f1100c05140100079148952100c0301011002d880009001d0714003010444168000039000d40c0041c10202d000d025004070b240c445020354010401e9007190f0f1810300a003c150a0404c4450000c04c4a511079148005024180e40f079658440142540c0340b48010711001004407075410000c074a42d1140d003201c0c2c1c004030408900c15 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 853905728 1250 853904478 853904497
    0x60c0c0503121903200702011806020d03090f0203010504110907020d0c03111e010213090908040303050c16032405040210030507090513141e13020a03020402070507050411 75
    0x50802540d01c0c1124100c3c0c1412020000385901c80004111400c0d402c22901c5401904a00f081c1c0c8520680c00014079620748000305186030076040105000340e51700003c0000c0c8040c403d1501003100c0d0414a021002580350308030082d055803c180c280002c01041d02d05503d18620152141216540c809500300e0f03890401c0129000413a030a221544042846110703200f070482c010f041100c0d034184174038401410303001d14004d240159943c0820401200348001a0000042c0401101449a8020350f100c0104078400d40c40001c052002c0042c9261101005000384684414186070644050b0380c4d0703040034640300d80004000c0d5000300d07900d540c241e14042180725460003290040c100c41c40454200da400e070000c000107403648080c04800400040c5039952a000da40e842a044c0001245114800310b1140c0b803a40094900c1c248400c1c204000010504040302480c0d2141c01045101f48440c118004191070201940019402c01d00005650092040003d2142d00711032082c1c80401c1018407000e114200e5000d4030078070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 853906978 1250 853905728 853905763
    0xe0604120e060405090a050a0b010e13050702070e0705040519060503040f030302090d06140105010e0136171203060618030c03070e07020d020a230a0c060c0c0503 71
    0x1001803040c8180452284000c024005a107015194400281d2000e0116840000c168403141000f0591409008004034044d080c01c0400000e1100e10010344204550321045c08036554070f40c00030b12041d2080100c60028209680001000d041041c0000d0955105008450113912405640005181505501400c0701d145d80e5605045840750b90f01c03071110312084507081e01016001d0002c0c00b015511850603418851049100040400c0c1c1c1e0110b1582c2210b05902040c180000003600003400d0360850081101100d6500403100c506804007013070503181d00c0d07020b00ea4512002104c00030500d2190504178034641c0d65003c0031100ca4503880c0d43c10b1034136440304036509038008005110024604403011103804007000003c0c00d0340c85102400001c2880e00300154000f1600100140600902503011301542c0d036910070620140851025641b1500049000480c404417110b20340b203080c0b00c40640c24065080300c03a600100d0402d540d03503188001840c51015110641308407000802c0082c1900d400074500f031100b0000d081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 853908228 1250 853906978 853907003
    0x122503020a17151e01050702190b0403080a02061609120f02091302010906020102341a07020c0f1302030601050d0905060126060115050f04090f0e0604 66
    0x14114080d401400400701800900d00d001c42c010642e06000a1045580c60300d0314009003419001c0082100c400700c41c00011940305580c8481999015049981136174055a803800c20354034251896a00303003501d91202d90150404103010040002200003030050300a06c1d030840d0400e4554003541030791151480d0340c02011a9820f9010050a1000b000044050b40a01c050818a84154010582d000c90489489100f25040400842190b070810107400160000344021410801441941c003400c85c400e400c100003241e10300142d203a07550510341400c170110fa445505d04544c10840e9860b11070103601500c407031000d80101b12001c04d0608003098103510485009004484417181860311500035031000c2c1c400f07410044200001e1484858038000c41d02040d20503401000a50324040706101c41404800c03801c04621603048118403241000038996040d0303251123903049a0450b0700301d405d0b20503100380f415181c0c000c04086800a038404103030384110320506005d641400700e00d580d00b030000d8981501303d40003010350001c0344 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 853909478 1250 853908228 853908301
    0xf080c0a0510120f0b0604090b0118060c060902060702031c03110a090b1605120324060912011b0e19081b012c0f0a080a030507060f0c0512 61
    0x10004c42e1002500300300000e00355a20004900340e80c2c4260040d240c02500d500f641da40c0d07544d201c0310324142c03269180100328810f420540d0040c9100d0b10080060702c41da45131104030007599030b04001c483d042980101110341d65120086820388080d0701345001004240341407a050000002c11089944c514803580d9100300701406d01100f0041a005200c6c041015002c98111900055040203015800c0c12160010781d103a00d001c040c0343e44120941c95072014113050303104503001c464803001d0a4548015080724030b04103004940c0c0815004241440d840340400c0681c1031701d10280c98200d00c400d0a07a00080e50308204031006401a086960558843c0b5002c0707501070b40300c00f864480f1048a450401e0014034090795a4242d0800020030304080d10700c03c2100d40c28981c1000e0742d41c50000c2c0a5201460151100c40401d46840d4000e6151407009501070180000007071000c041009a91040078000385d285010084209807484c001c040e90007414142e01010f401c0b80218004d0350010070411080201d20b1070440040d038119 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 853910728 1250 853909478 853909481
    0x12a1101021f18020603010f0305192003100203181e0303071815050c010e011514040207080328021801050702031f02090a060c0c030303150f080c0a051012 68
    0x2a030006100340c4420f0362400043c0c0d5400f00550080140c1d12a1500b00303815420f00078280402c207503031401003c0700340452000040f005940fa410104c0074400400c941c4036041d01103400c15800d2218908194030010810816129183c640d2051354106422a400410703080140e08649242c411400c615620620005042070b20405107800403002540144070040c0d95940e80c0100d503814081103402080c000300e030400c0060030910903e1f0704581250001c0c400f0010700130401300414a240280721880c40340008641c81c0340c4944e0111030b8050b40c404501550b03031800c8500d81030901c10034081c154a9004800b482101c0142c41c0c0280ca424003451048000c0b00c0c0c42613801520250300034102240c15020300c00489545450840b80b0b507007088000c0d240581c0d510000d0b8100b0148141607004034080c008415600008100e580b08801c0076a64182400204883c2016600f8020000380e44850710000301010042151000411401480082500d2110303000d62a07004025404a07410a8003001034405202044401c096 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 853911978 1250 853910728 853910741
    0xb09060f03033c090a090509010603080c030406090b04080303010b1c0903080f0703110d0b01110f0309010e0d02060910030f090305120c120403030902012a1101021f 72
    0x408aa15014800c0c20f5540d0140385058a01100e00344500c0c40c0103c4844181807038401e6405004803407074032080400160700745506000d1031504556402c0040e60341d4409501c06009503030403001054a50312030b025596a0b0b0341c464051403001a481c03000c00a503d00350a0161025128070b00040c50a6a0070885000d92507040406864158100f0301c80b0320070301e4652440707240280da004e6503030201e091400200e080a02c40d4050144010149043d0018002c2a282c5090b9038280211000c007158058105004855400c501c0c0c003142d003c1c0c0140ca48030f015007400040100041130007a29040701e2446004208207644001d040080c0d000308080002c003085103420300e858010010309041c0000c00c000c0e1014504100d6113041c0049010034000a5201c10f0610403403c410b5000f9202030707405203070410030b0722504003116010380020181a1600280421a80a601c50b44145003490305100c00741c04840c0f5003920003888a407400c0e00d4450250501301ca1552000c00d0608600e2580c0c518000302500400090300107064 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 853913228 1250 853911978 853912009
    0x2a1e0301060f03090204021c02120105270903092106010506120403052802031b0708150712050f041109010f2115021b07241205091b040b0906 62
    0x1c2c00c006c451908810500d55111058608c2c1c6c006032a01d003c0402c003080c1c1c0c0ca06030051071043c194802d2141c2c1c03108103144c2d07160544c02442d1b9070311860313190341c1d41f40c070310718000c41d03030043d60190400b0320600c0c10300045a900107240f14103404a85280c3d03a80d4007485018860918100322030720300300002038007086c0030740010720280b078000680032141240c60328640321030200b0304c04880040e000010ba166401c0c0201c2e000304500520070001d0100d0a10740b401090340d401c4090680c2602c01c002e840050b110714080c58140d000440e003100d00380003c0c0f90840c00f4034102d0301c00711030444405150b00c03a095014103100390614169402da42c5128045420301040514887e5480005081d440d8450100c4000440c104860f4414041406025854803007800080040d104010030f940120781c81120100306560f00d1400101000c94110560340031403200e614102d03040f201180b58555486d050009004ca00b81e40050821150711405207481d50300c070045410002941d1503034500c142c0c00414100412468901f0045901509c003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 853914478 1250 853913228 853913231
    0x30312111605070906170303060d02150a170a050702100f0609091b0515030703020a050405030f100c031416020c0a030609120c020d06052a1e0301060f03090204 70
    0x210350036144031100c0c4201e003040b24242c0040350100808a12406400c0103040240000c008410354001c00301ea42e80802001c00d40310710f0034081e1700001d64480d424108000c4800800035540c40b081e0f154081d01082c500e46441030b130005030038000341c940e95551044501828203a8044d041030040684424040e000c055034034801c031a034a05d400121280c45119200c0107a1140765251142d0b441f4685140031620b503588200d0084a141501000304442e000460740d0042d03260800503258488080c0407100ca0003282c0020b1341600c00c1240480c3e60303810014020441d590b5452003840007440360340085082e9041c0140c010704190000c804951416807103090740020994030b00c100d4900d203400000084450140d80d006541243d542e02d80c070800e0000f910a41501d50301c0d07600b04540580c480d40d0105000c080040e10103880782d5138980104846260f07008419514040b0707c104005041400c0c0031008081d40440c034019624024141c4c407c101815100590307040760982d48400f01c481011710019405000c06940c200c0e44076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 853915728 1250 853914478 853914487
    0x8030901050106020d0c050c10110d09050a08070605030f070e04021204051b0f0d0204020706060e2406070818130c0201050906040f02130204090c270b030a15170c0102120403031211 79
    0x140822504000429533552401c00303601e02000d006210002d500b1458040d0405c05003408215040000c4a030013040c88014101c842e40e4000c8100c8400c01d1031680c0315441400014803034011002c1c040110301079401042558902c03081c0b1000c100b22550411071068110742d510030081d94a1a000300c03582c1400d030026001500d41512039a9000c211032083c0c01105815400c80e06009240200e100c1c101c01e84003403004c0c01135450f08840c000802d18080e080d002458560000707810304143c05005803d08005102400082c1528000c2100e10701426250032404c00661814000035698000003949038081d54000d9050300045686030244180c0b00070b458450100c01d0340030400043c15207124854840c02c00500d40c3c0b4901c03484041d101041c0326584205c1d01c20001c5d04080b0083c01001407000880c1c1e041100000005031030100440600e8285070b55510090200c0740740c10700042c0350200132401307040d100000d90a803201c5040c0100803240c603000d9400042c000a0038511010507101d12030340b105a1501d50300d603815007003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 853916978 1250 853915728 853915757
    0x9030e0117071101021c060303080109091707060e010609020d0e1f2f03180d09050111120706050109140405030703080709031e170f09190308030901050106020d0c050c10 74
    0x2590802c031103206206903240410230a00d43c4c00800f1a01400c1116410310602d4015219001d001130132240130aa9402c00280c41e80070041301d070b801150321620701c070700900030350b41c0d101016002500710303070328034403204e404c0104070368990101095807103901e40100c809004002012141381c0003030006560882001d00250280142c02c8148808091020301503541c0aa82c0d2408003e91054029500511551540070800b054a240d070842c03101d43c2a03c500b8070b411304410b24282010b0b49040140c03642d01504000000d038410502c50a03402281c1039070300042003448101c90a0081f800e0328a0704503070180007904113101a100091080c1c034103940103025480e1082106869840301d4003060510001002c201040c501c1002c200f0101c0d01c4200b040300b20701030300541005925070b00d40d8a07900c03c228802c0e124029040c5080c501e000a1160407001c2c6400007800d5460386448050b46001b00000e0064001502c41e11610340700e8140f0030042c0d80c1510758440c0140201c18044001c0c072088103000310399501403010313400340e6002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 853918228 1250 853916978 853917007
    0x1e03030f03072f01110a0f1817030304020a0b0f0412020f0a15020f120706230702150c0414130e010c0906080c040e07120e0d0309030e011707110102 65
    0x3400070500e2000f000e841541c400840c211425030b054101212000d00c107031800c0329088220603011407841e06021a080030251074030a291429900084031981640300501a035040000c00f96200301e00c259a0b0522650b2516001c4605024524000d198100300b08014407144d50700c0080f1000882c0f020780401542010301c2e000412168154001c1114402c1c401c02181d022581080040e4151200201409a03210045007803807840c4030b040400340c00140c90726240c218561040a40300801404554407564504000600a440300382d2140c40102d82c80510010401c9500e0517800c590850764184110700108c40040b003800040060140311590480c1d0301e00c403500041000380078203080c1007040d50b1000c0c01141002d02c0503086103405000720118660034001440403140304181303c1e41041c200c0c01c2c00c0070500302c0520884042c180d14104800c0c180030301c00038407a0741c5401d40c12101503103200340c8981d40c1c030b8021180112001c4040180340c04082e1070a03804202c005000b5188014007154130030000d45800b007001e030030740c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 853919478 1250 853918228 853918277
    0x603020d0312150303020601060e030a0606060c050d11030301090e0102160303060f06030902100813050d17090a030c030f02071208070c05060f0315010e18061e03030f0307 75
    0x100800c0703000009908001c064490900c00b6103103c0c00e076468040c1541c40003540c1303a00502482e01031042300315128480f540c08206520000c0d030f10030414040241c840301c0040a80b49543c030120b80754070074400e5012107035001d1410a10240c000d07900860460b03207417090359000b4000300310075020155800c00c603090a14103004482c41d00c5501940f00441c03140e1038004a000d401019034043c9041601d494000c400581d16049102000b1140e0f241400031038907a11000003003504d14090040091280a1520706201e03000441540301840d0b00703040f602251385241c10302e600d900e00290020000740c008040e000000b402400506031801c514070444001988072140382c002c0092841c8250f88540011621000300a200341c1c2420103000e0035621141400090080c2c8e000502000d003d49a10440510101000f40d04c580041e2082c020000d10081c200720f0000d0a880f82820180e03041c5004000d1620010742940400c105240d41b0080680114a0011100200861034002406407410000c42d9820b2125124400102c079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 853920728 1250 853919478 853919483
    0x3020f1201170f120c15150907030606020a2012030d05010602030406120506030c060a261e0c04120308010602010605150304020103091103010608010c021614130603020d 74
    0x144295410b0802000749441440e425a09540c05800c40440340100442c0201d100c44158450710b4649440034003050030100d03600f82140b00c2c01800801c11003504100304c940c100050040d00e01004548610004034255446070082401581c000048800000c1c1102800301d1565030300e6130180c940c0380c0100001803803482c10072505000c0780d2000c54a00c00c2801c1030f2250900400c1c00c2d0000b10314091610801a0199100070900080c490b0745100054503a2020b0082160b06840144416503400c1d038000060807503c2520204480d42c44203080581f020700c00d051989009007494024074044112904543c454000300078010591040b0034000043c003c80700070140c8481c0c0d4030275141c110071981084402801c407045030303000d1841100081041c4604507880c6003120340298082c40e01040c010b103641011000701500c10220394143d032800e200007560400640c4014282c441c15407d54500243e030002c0d1075411555400740d4520003220200212091400f0312890341008010240403903081e80e0380d00020450040081d0070b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 853921978 1250 853920728 853920757
    0x20a0b040612150b0a020c0a03030518030a0206030c1608030103212c0d020a082103040c3803060f0d0f0605100b07060f0b09090a030c0303020f 63
    0x80c048142c000c0d02c4224007031000c6070104100e540080304101c00321054821a94a24030005501c010644213014405200202070900807000d90780e072400030043da0121240c0481007020340704c1e000d50741c6008105070081c150020a0581952100302d11080640c1c0040507000c0004031501d0904c00203000c3d0401380d8000c1d809843c4404c00f03000001c0f1007e820101e510b01423070401054294600d10000401d4000050f56491150b1480c00441c00e0086081f01015820281d8070030b041050004401030000b1382c44800009144842d1041404106031805d50b010a49000f4224184060148188103403103984880b90080000390541c2030109100f64050341c0c681070041140003500100704621814081549489224241c4071090b0500307460b2110083e02190030b03c003c248644a0020400703080740c07003011202800714141c015070b682c055458280000c120051320309080c0c0341015911261850680665841507164101504404425a908880d8001c1c010812070506609210440070101c51002610082c80603551 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 853923228 1250 853921978 853921987
    0x1c060b09030606030f0a060f02160c0807060e1e04020708030a0203010e01050901050d060b010905030106060e0f0405010806130221300f180409050622030503060913020a0b 75
    0x2854104100140014045d0717000c40030741c0c0320007000014001e02940d0000c0000030015140e112a00203407055000d40c3c2c10300181318140c0d03004d004980400030100d03183d02041700c0742560756602c1a5100803540c49034640c00142c0701a003031010f0b6650002c0e42c0c40903034010001403400200b641c80c0c485e10703001036030f030980380e0360b07000c80140000b0340030018007409040125240c08956141900280584506180091440e910798a0b40015640520544800350000900030b0202640b40d40e4018072007007150144601c0b400c14407058082d1070070325101e51030603501140090403865079101d0b844162500340345000c90700308400c03521242054031806810b00202161501400c070250f2421f10241c541021032070039411150004044040300510711003220150a0400d80950303da0598030030300c114800d164580550081d0411400310100308001c03510030b108040e442c8480551029500f110840008a84001008a2000c0010480c01d20300049080d0f8020340c46180c0c0403a052465021440c3c500c01c1c0c0d40000030401c0d0108 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 853924478 1250 853923228 853923247
    0x2040902160b01080105010e1801060e0a15090509070510260105120d1b02010207080601090c0801060c0b010e06040209040e0601090f02190c140d020a03030b0d030f051c060b 76
    0xe043d00401c00c0c0c00c0280400e5041c003c44c0524268086c0c05c41d40c105400c08040c0c04072407002c0d08910001c000c1d140d0010410324107950070502429100c0d52271001c010002c080407900140fa071140b940075102a1005100140c2400103100c82e80540180420511144421040b54400401070000c014000d40504a043d0751600303084c80a100c240e00000c1c901c503049400f41c0c49046510a0b143c20707a0410002d01203c0105050006070b0800c041500200740314051040003042240e2582c008500821007075440d015581c0e40c602c0d08450715002544028031041c0d82c400104103c0618010458000340010310041c64042d231a4001000c4640c101c0c01070206030042c80040160f00c180d8491050486140d040542c5002d10300300c0c0b000381c0d4810b203c45043c03c0c00601d508000921820b843c1260b41110070204030350841c218100069900d03000f01d14118002070901c07219070b00d2801d001d103040d058241d06032203041d841034525009a03080c5e0006c04a10300304c5402c103818511403900f24000c4000410158060303903580d80d04103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 853925728 1250 853924478 853924493
    0x311061303030c0e090c0d0b06030c0405030c010c0b070513091d0d0c02030a1203020909010e01030c06050c100c03020c150f0a0203011217281101060b070f060204090216 74
    0x20100f840074048035014107149621100b0445600003030400c905035446200d40b134410700400400d0b401540103800401004600c54503100200281d40c0100c02700c5003065000b00046903c12294000180b0107061070002c9405540a03101410000400c0d840011042d900ca1501000311107160207c5180000d8003155089882402e02044010011074034181081a01c44d801280d519000c40ca801000d2401012014400da80f295042e6100002c000305400410b596409205410039800e001c152550401e80000007500384c01442220916031442002e0000c000768584144000c010210260003416002c10110900300001d00400e13158804c03070a020150380c1130007201400c0500c1e004000701040da03c10401406100b0410500701982580540b00355441300e1030b004000181d00035052100110407041e000803102c182d889807a04055070181d1380e1122043c17490b1402c24242c5891348208078802804000b801c000c02d49003000e022200340103545c058035180d941c01d0080c040b0790110b503031460510307080b10404080040d803 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 853926978 1250 853925728 853925741
    0x190f02041112101e050f061608180105070c060318170c060907030b06060a030e030f03012d050f0a080714030d0e09060906030a060504080c010c0c0b0112031106130303 73
    0x100c0e261480d410f1380c142c81c002000320f104d0190360300c124010905034010b5030700c107000c071403044140510402d01d612061810030026040745c80c07a034031009031000001079554400c909644000d90001c03464a074540c80c00400703500030141c0c40c030902800700700402001c4c00b282030480501070221480b9200380d503c110750500a414000050703d02192500403030800c001113521041c0f1150800e10444000d0f41d10008003500b5001080801c02c80c42140c0008a2081303216001c1901441c100c03542081040720006074031080031034248400c2c400000224044405100d1400d00080150180718054101e030320140d1258059403a00c5d03d41d61080d60a90f1400b40c280141d41024482c0c0b2482079000d00305910840b0591001540000f4020103481c0100300703100015545550400015070350a400c42401c1209043c607007088851980301940500d050740c24140310300706081c4180384500a694122407008003990030546c50320a4502e00b00030a8040100324003168035095818407400707000d00c1e1100c50541c4624a1881c015090300c01 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 853928228 1250 853926978 853926989
    0x1605010e1b0a0605130b030c16050c1005090a030624080105090d1403060607020d0f060c0e032404051e160b09031c05160c1403190f0204111210 63
    0x1005c0c0003a803c00c80251040c0000e0710000c2d040742c0d03165600c2c143c1c034031024041d0351000c1120040000b84902441804520700c0c01c40541542d08002d890901b10058a85114181445820a01b024420408180e040c1d01070504072014422240b0103840400202440d42c3c45500200760300d954400502c032b0381c0e140400546c503200286040505150111100a2016002c0203001d03501030070f0002a800e0840d5981c5003038600700c9501c50040003400949003441c02c0185030150180011078161401021149000580c103a40201c03400c401803c01520803900843c2d0300b1010344100e0380391103032000e460100c1c800f00d010603d1880f000c1e4002d040415145a5407807907001c99900c520680041040403400603140801e015a810b10110f05280c288010107008640e540700d12010480f06801d0080c551080000e45c0c2d50403001c03212904c0201d0310000d0400c003015242d02c000340c2c89118852000494000081c10303031002200803400240700069403034407000654203d5001140e1180c50038001d0042080ea16003150300368010f8030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 853929478 1250 853928228 853928237
    0xf06050a0b0306130e0628020d020c0d05340204090f150204030218041a1303021b030d0c080c010501090c0f08191104090f0e10111605010e1b0a06 64
    0x1010394449a4071100007070001550030003100000c04210001c00d4901f120690860402c44d40d0b40e0041c4d508000139041010340768035502902c0b540b18900352180b0140d950003018005800c9502ca100160804a07100101c110026011003c503e080969560311960a843d8011045000c50044521b012a8154001101c1e040c0951060100b400540c440e00300420607414040c94014071030701c682c10410500b003110320015010000303003010000c00343c185074082407a6a200b50212818400008850356050b021a821190168400100324a0721403244a49444140c01115110300e0034003040301d040d003903071400d130003440d1900d4462907440b004039032040b1400c64601907843c3c108500c1c00d011340110320407004a054010983d44461461392103800c1c8004440023071050750002c1240103689000c0401a0525030190246401028203011031f40e035142c061511140c1c0400c3c01c1c20f1900c2030b480d602c100b0f6885804015a650b6603038404500c04400104003008038400c151300f078001036104403003c101d25002c50760008070401 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 853930728 1250 853929478 853929491
    0x70b060315270f0a0c05190e0a11040f080a02011101090b0a0203150d12020d0f050723031810020a020f09060301090f031205070309150f06050a0b030613 67
    0x9200c105184910042c00b49249496482c498000d24044000c103694100d4000c3d0f8041c2d00c1040001c840d01c0040714026240348080300840ca0070351340159000e114680701d00342c440d8001010030b03403a50302c00049080f00001140c103046e298415043c8000c1145c0000d000d80e404070080005568003d0040801109114020300020b111680c0e21040c0c04c602503d070700d01c0503401001043e105880340000b104001405013000901300b081341012021052a0030007c805806910801000c440c810314186403040040e0b200c5907c4d01c040750f07540d030640c0305031085113000c2c880588141445003602400104404200011010003203841d550400c030b112800d82c0829400d65000044810050b1941c40d01c02ca20448100c86100071a40e581c4082400361500c07480041898103119441e50401d50803001800c0002c03500360041001e956a400e040d4220780c890703403010700301040d150f6840415003100d4002401074142c03802c0100750613a030707100400c600d160a03402044040e0b0010040240030304101405000084840001b071095 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 853931978 1250 853930728 853930741
    0x606140f090d020a12150b030a05120a020a080f1801230705010b180412080c0f030a060801020f040515250303110d020309060f01050307090f0902030102070b060315 72
    0x154450741c04418001e40c0491468425075981c0005600204401d880039900d096031850700780742c0f80c0c0c4001c0200380103030b1030110b01c08141e040016208410301d504c40c0c0184041660b50310618141c0e0332003880c880c110b104001040300001c1d201c00161052015020f00c481d01d4240e088428020500c0e210002810480c008542d5030542280e8500c0d9040d030032900c481a56941c5070b5081550160500b0f440130303604079405401d00d0480d415110a618812406035462035040c4040c014126154407007a100d0486c2004140101200703207036980300460b044500d00e000010882d45e15007200707007a070b00000c00d081000603010170100002d06042d0030136542c2e0b03020740c92074525000e604151000c1010780d80c65000101b00701c104240c401c25000764080250020446c1880d6195088800494081e510403580401140121004646030b069902841070507200f0003405008402c1c1805118801003040e8400700400c1c0d5210113035180540ca0a20042c0081802a42082160324080061516000f04802d03020380c00c10078141007029 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 853933228 1250 853931978 853932007
    0x100804050705120f011407120203091203150307290c0a230601090204030c0801140a1a09091507022e091a06090108010209012a05070603060614 63
    0xe442d02203d90200e020b501c25681c81c54041050281c03050b96103040500c10b1a840307101c407200e21840442d035540d084444140e011009130700007594621542c2d4030091110403081c0044001e9507004030150f182ca40c100745071000082c5404801c5e4000c0c4031244411500c1141060000140d507084a821740c1d90503d031940c080b030b84035660a00700701d002e080500820b000034030a5030803442c1c1c0750000100104441c1d071940c540030214000e50051204403401c0641344000601c209040c002c090202c0009905004c6965400203000040e04000c0112030740c52141d200c1e144441d6640c0030078a07010382101001426081e55140c1d10f8819004082d205c40d00b550f1000914083c6030900000240c1c03500111100495400d80d882e00200c00b07044280c0004121104e1041d80129003010400310a12030345084480740440c3e640da81c0c0c1d8600301c0c401c0490944c002410b181c2c0352150307215041d0f0041e107498601c0209031084103c6403201428210079400100c00603840b00f40801c00c041e4020410803104054012051030280c004041c0701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 853934478 1250 853933228 853933243
    0xf15080606060c0f0d03060815071b020a0f080312100812220b090405100b04120503120408180a060819110a03090b011a030103030503091906060510080405 68
    0x2841280700041c003103600300d0144004c40003a64103104544c404000c0113005005400d01d0700611460384a4002010b4070344000d4001d5034012401a00d800c204190301654402403000744010980e003007160700b840011045080c0700340030010030140780610b85400303490103c81040207000e00403010580000c58203126404001c03a001740082500b481c0da6656507140107841c5040f0503040d07421703099038008250024070400000300601800d40100e40030131082e6115205608400958021401000c50900041c003c0103507449001000030b010700304890a010200082e140c83e198120ba080303c20750004500c80b0781c02c0c4c109607048040350320104c1e40f0000e07003410720302c0081c60303100000c0c442e040e000b12100b400c501c0d010141e40300114601c81200c03500da407000c034408043c0140c16081002c44035450100000502c0c0c07001c1e8444541c2401f048828245540d01e1500c3c02c40d12500041c1c290f82d031a000d1301d071150b02025450700c460030045d407090102051451828040103c001d00d1499032001380708010040100142003c107900 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 853935728 1250 853934478 853934491
    0xd05060d380f1602060c1b0a0f032606031207030c12020706110c0d110114070b07081305060109110409091505010503030703050a0509011704060f150806 67
    0x800810052550a007100614041a051091111402d0004400480180d03a1042c48140c0b045010719541c40c4049070740b02c4007115510030034001072003040301c2080005052010144103030203d42180400d1703100c09500d407500c171000300c002c0344a034100d80d815204104800d02074001081d07401b00301403500d07901080c0c90790045011828503000014004082500504118898076004203440f45a440400406580c48804d4002c15011840c2c2c048400310151002450f801141c0b8080d02160002d000c43d0366000c1244031411526041c40400d200c4260b51200e060060310806001d120b031030005007001ca201520944014243c0d0403203980314070030030010410000b80203044507003117003001481440b449104c220a02994000e021614103114110301802503a48040c0c08400d1041d204100990380c5000301075580c4140c280040216406104a41240340910042c02e0014010304051810355113040884c0d03a100c4c0211001c585060340c4485110a008039407040300242405240711340c8599090001c030f01d58485008004 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 853936978 1250 853935728 853935773
    0x211507170c030f0a1b020c0f041a060d020405130b101403150109051206150a0320010e0a09020c0c151b0f060103030206070f09140607020a0305120d05060d 68
    0x108004d443d0552145000b055241c010f4803c1804c2004029192540400b074a071154079415061441c6240c01d00c03a00703d400340d4502c049402d85076404240140364000384c1d05151000d5080c08005000c3d00e4141c0c0010082c0c1c0130032030015145203140c0410540c2c211603010f070700801c680300c1c10f504600850f41c82103031b41001200e20810b2024072807800494400800d508080c0c0c000f000d40307078819550710001600c240510024040401d009002030144403040c0e000340b1014180780c28608854503c0c900c3c0e42c1c00d50003c468181342008130aa03e103c007080a80b4016880302c06203543c0020403030680081444550a05042180d503c000000d09455080050040d5420076000c0003203050342014070903003002542c00b00c425440990b5055a500c1c1000b07912800c0c100e031100c0c00304210041084441b0f11941c2c0d00420303556000b288950449001d010b00c241c9401580c8100d8110b0301450010000c240c08102040d01489100011640c4100c1980e40d0700a59402408140c000c000220440000030041035181d000107511001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 853938228 1250 853936978 853936981
    0x10f0333090c091802120607080402010f030e030415180f05040f151512020f040e1f0e550203010306060e090a03020c211507170c030f 59
    0x20102c51000c05540018203507031400c28859019107031064451031050081b9011041c600030100360b2a00ca0104541d5400060241d0f1b0010340158041d200c44100c0802d68a00010300c030312003400403880d40d80b094120040034106000c0458245030b10040c0c101e5041d10140001c1e82031850a0300c0800100510301482e44507984900003d080c0340350030303480b00c1d00c0c0c50b0f804000e858040c2d40c1d032420341c080c1140714030201d400100c0c1e14040d40d00749030050007142e02e042c410a07a413500c0c0525280c3c003041a5034028003804512600100070741d05d0000382c4644070300640344501320300c01da80c1444004061420220400b41d200b80500300b498000d03140c0c62000c0140c54102188030b03224510244500d4100a1240d4512003400d10310100000c001d1100c81d51056003607600300030185410782c44403a0301e26914020b15100800580c4010b0040d81c490810520070b801d04440b10448840980c50902c105050118103034415440d00d06a07001c00c03441c1541705a81400042c18801d0030521800c14180b1203c1c28800100f01c3c0c04440c00400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 853939478 1250 853938228 853938233
    0xe011803110c190f060f0c06090f0b240f090a0c0203160501020901020c0604180906020c190209010603060605030f0603030f0a0c03080108010c0903030c02060909010f033309 76
    0x141e21102d00000c00e41e190400c0516040c5000c03481074014503180401d16100461040e0240b03d80110001094032030540e144201d503900400307403000020485026102d8000f2800058400c02c200d4010850004030026403c00807460001052504600d603100c1e0011074030282280c1c485134881c0b50480c41c1882c01144051211078113914620843d0b00214400104a00d01c0080c86010341c050111488260300740c0f580c4101100c20401180a180520924840c401100c03281800c1580c0c04401024819a0054286680c114545007840491a420504901d402da03015085250811181e0f000d08800d0800b00996424404000e02d02d00000b000c04564142c042e0100e05103940c100161056541c10b0740c0400e940b520150710041160f5030511003100828082e40000c2015a018094a402da01041c0e50b5070313000c01d01c1d54400300c0300340c988048280e030800001c00031002a03481d0050b1690290288129040c2442c3c030b989050190344c8400f039100c03c4c80300c0e124501c0307021541e43c010780c407445450030800c0865021100e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 853940728 1250 853939478 853939483
    0x40e0c0f2e091503060612050406090b01080106050406090203090a140a02060a03060503102d09082805040819080d0507020d020c03030f03010504150314100e01180311 73
    0x2041c00c440c280007600140c2800d00d0b40180c9440c1698503414030309043c01440001035042c1c401a00920002c551031041e4071403080d42c0c59000c00c0d80b01b40610404200c0d000d40d0744034802e03800002c0e0440c800c10b94440d1411301250909001d0b04006028ec00000c501e1450001c03282510346c00d406000500e5800460142810054104039901d12160000d10b00d554035911010082d0050081d40b00c2d1b5406030141c2d500c0c841c4459214801ea200a40c50b0b80c0c041c8081d907004c840004540c05818080001841ea100c07002c10200e26035902038a84040040c00f030070718000c141c040d901e141040038900c40007000800c10050000fa100403904010382c80d090010300440d48254030300404113024400464005031b03d004204108164005515000c400c455002c2c1c40150751000c041c0340e11b0f881055400350f40341008000420075418550301601022282c08160280c1d40e03203030f41d83c61002d0b17804603031b0588441c1d00c42000640329490358400d072214005890001c105910300c4c0e0f00280201240d82c8005014041036018600544106 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 853941978 1250 853940728 853940779
    0x301030209090a08130e010605210924070306050a0f0501050a05090d0303150b18280305070905180a11130608061b0a2001061d06040e0c0f 61
    0xc241d1207038840300342c21145c41c2100428807466003404118000068507602a2048454462868a004414800141031045400c0c2c01814508a5204120b4440382441c0480c03d6840f00b490071303440150319070602d8800103040da02103400c40c900c40c00300c01d00200f00305461101c201e0110341d4203080064a414004405484901444203410f400c500c041945404050380740d40324407140700e40082c400c0030040e02c1c1c200e0f100050003800da0002c518103c88502e51142c0c07525074042124402032340a40640310107039203180c04070300c1310582c412942940000030600400101307010b845d0340200d248211845001c03102011558036442000d000c0d0541c048010301001c1500c07a10002c460818010b041440480c0c0d40306119543c40604840510b4030048070302d9080440010f250445014840990b00c031440e45144066a040e4510401c4000c111076603900c50005404a403464007130288070030400443d16601d050030901096404030043c03203040f82c000114503e02035131601c56825001c0c20561300c0100c844035029001002400 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 853943228 1250 853941978 853941983
    0x10110f040b0901140307021e100e030a1d010c03030b040906060b040305060903090d0b0c041a040314280510060b0705250905070e0a08071703030c0301030209090a 71
    0x10025020030702940c07a20007000364403420b0366083d0602915101c41d0000740015a9040010b03040304085803000c041c491140c070708484c1ca1070309641c45241440500030031030b866501924120f80021075908a00398004003500210003100c0651541140c030040000c05808415400a06240c0e07140e00032402625941d01400036140d000c1020804261110b1101c0840d402c00d04c0b040f9a640301c0c180004114441c044151034401074041c22110200700039580d043c1c1d40900081031240301c1c02d418000060b000211008000e42a07002c0b02096075110701303504110b06003c2441d802e10b28198403241004545244000d04603060351130002c3da411007030a6602d41241021040400003055a003400030115030b002e001802000500d10540440391444d00e0110303611200c0c20740c4980d110440c00c00d40002c0150b050300340c1010b5800820ba16118101c00051030009034889400e4201c07036460ba2080100f8070203540a4a055407010781000025815490140d10101c003600c01400000d000d14659000300301144020071082d02d885a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 853944478 1250 853943228 853943257
    0xd03120209040903030516140301270f06031e0312110904050f31020108040f0203010905060901150506090d020103060803030a0e1c17180f060412030e1011 68
    0x240c3c5402d00034050b0030103850704400d0000441c0341d2050f07540141000000e614200d142507007540e1a0501015180074622140000304c00510160b044040903441100a20b031201000011150308504158180e46e00511445d013070703401d2450290000c00d400c0b03d00051030f40314164001c02e08506041002c50302d4015844102d80050501040c000d100401801c1d070752007590041c01d004420144c1e8041c100b00300c44d18040d0810813100007068000594421028217074030034000c2107040c3c4114025408207003124a20b41081c3c03641c0d0800d4041c00011642800391054180c0d0304008621000d0070803002403814401e0002c0f55104000d42c43d884821a4004e400c602d005220034001c0d240c9900d4610030103000341c42030080c90b480c18094031141500b00d0100c044a6210b40031a50b0f034000300709104020440002c1c8000e80407003d22410480c00c0c2d4403549040240b802841050005455281064034002c01c051160750303515420b16050944040034208002070039050317035003086400304581c80e8154248005100f06840c0300700b0b00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 853945728 1250 853944478 853944491
    0x1090f0801052d0a020901090510050316020c21010f05010b04090608070e0103230714090a09021005030403090b04060507110406030c050618030d080412020c0d0312020904 75
    0x921042d0b10240c81000c0407010841441c46824103000d1001c0b10000d00038901c4281e00104030038014039030251451031303010b04141c407a0507103603400162903000400310500000c0c000020080030035008028040e5103a40d0340024010f290310940094040f000d81c5040a060380b40c5e81c000951944800d410020b9848080301e0200011758582503074040310382c080e004000040341803940c0007440100c00510041280c46400400c02203900f16500c46842c018041080c040829400d021800200c4041c0885c170000c201c0041c81d05403440203102441062100207008464481c903040183c40961110104e0329040000d6180055882e9100e01d8142c0e221116a000080c04910115020400b107811034001c1034010b0042e010020419030740800c00060340c0c0c00380070040c072145610408000c0d03800c211025010386803c0703410030000b04807a100800e141014401d4110001034005090006004076404039481c171050501c0607005006c000d0f00072441411420800500f0009451a114410501c9074141e071181c00008200f44000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 853946978 1250 853945728 853945739
    0xa020a03150305012a08070c030e3a0b040b040507091a0a2909040b0603101406031510031103040302070e0c09030c33070b0105010f02030d0b01090f 65
    0xa00c01d100034400302c005805e00a004000d100c00030740d0b050003500d603a58210b41d40c8066046600082201d402c030709102111401c860243d8910401e480c0c0200040940c80000c24125140c1e8111070402c480d4000407172085e002c20000c41c514142d40340e0f01035001806841c030b640307c03171a0082c070b411210340c8080949448e02c2200341d402031800120340030300c140444403c60401d07180c84103004418401c8030a0350102c45140300f0451004840406003140410040000a955200304080f540b00e41c4212482d5061900c09642804a82d040d20301c407800d1240c05072039050451420502c500d13901d803c420807041c401d000c121401c00c041482500b00405807103520346020380364180382ca40a503480c8003d00812000f1721240c000600c0e03800840040d1188218014000d003107003525141448403148024803611007901807108204500400e40c154010603100e6070750071036507071040b41c01d000d402e00006822950400600d101c0307a504140e800000e40d860101603c80004000c42440c0040e19020103650065000c01c00c003410000340b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 853948228 1250 853946978 853946981
    0x501050607050c3c0f010e010e09100b0a02060a0c020d0203030127060b032a0d0f0e031606060b030106050906030603010905160501170103050604260f031e0f0a020a0315030501 77
    0x1c501005071010384900170300f04010f50f0040c00e003803070a50000d12600c0c01c42d6900d19180714525040071641c248540301585413036070701c11668445400440903034089814014018994070851982c4000e07440a400a041043c000944a00c4103114207115910b041c50100000d0207082c61718560003a080500f00300d480d0f80c8a05e03942c101d800031a2078604402801520444d805960520b41500510b000c407907500c4c10300031140b450000d103512281d6080c0720b940d034501d14204440400051403000d0344240904800907980c5001020786201c1d0300413941c2c4000c103000401840d034000c0c003551007441044400d90f03203d03078500010900400c61004040e01510800a40c500c800c50110400c0054540070b0f81e0341a04041003aa407150344800038400280303a58000c03800039002c44d1201c10812820644010464010302c425071051210340c101c04c884901a4000109000d1601f5400c501c0b254001158074054801d4030384a806211040c40c001d061009598000030700c43e1085100303500242c1988d00b008021915581c036420a90f0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 853949478 1250 853948228 853948339
    0x90c09050108160530090c130209030604060908090405040b10060507080708130b030406021b061902030a02130b040905130f0f02012c03010501050607050c 68
    0x740801d00403804580d502590202c40d24030f03040c0e5602d50502c2c00c03000102c284107107084104200807030020070022480c102c01d103011150140b28000010912101d10a0400030b5048400891850161042100c440e80341c40215842c0c1c0e001d9001b03100000d07a07102d035003440c0b1142d00c00c03142c0a560141c6020100010012081441c1d405020002c0340324807802c0e02c40406445034890003d02401c504070074030243c0c00103160700f002040c020140c44400b4003100e42e50802203080e5002520103c518036004106220192288401102c0b1028140010819800c140c040c181566105041e28020903400000158023130740300c1e8044a00c1d000700070315160b010345d0380c51300c40c0f080076081170042004c0c0908103808150113442c88450303003001725003160f10001014802e58940700b9141c2c840c8001c0b41408490007800c0c1c0703500c1d194520282c1c01c0300348c4240b4003c600d0701c0a040500b150816003100e84143c00c140540400311b0000204041803070b4055410060324400c0000202041200c2d24201840c003100d51909021443d0048400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 853950728 1250 853949478 853949489
    0x91504240515030705010210091a07020a050c090115030e011b0909140f0a09030e280e1612020405150a030b01031103070c151d0601051503010e0907090c09 68
    0x1401924000c1c08050300d80130940f0030b19006a00101e1100150071480e88400903143c0700d08008021750510003964000b0038001c036507600150b0080105001440024040341f10394403000c94006050b90f0404146200d140c01a8104000305903079001502402c1c0300c00d50003c05001c413207050002d124041c0400080c00d000140c0603c00e115030802c614069080c15500289000e403903110708607042555540c188500615045406a0800c9840c01c1620520384988081c2d1402410840070b661443d11001c01c07034003400115a01c01044d50044004101e00d40c0c03074000003004200c8151500540400301540d400d4042d006a400c000e5018a08000a1881c044403400034110282103850034000309010300010b404135000004001404e401c20000105001e12440f07421854601c40c140d00035038100180d5021080f1b8440711000280058103800c0081c0c01c60081044500401048464040d00d080340c600e0202c04e40018465001d216a401d404285540350600c8024050035403007004125a1014005c011b10121143c89013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 853951978 1250 853950728 853950751
    0xa031103010e1b041d0706140409181e08030c090f19080d020c0a05040c121d0c041a0d0f0807080405130b1e040f020c071d0915042405 59
    0x8884035541045c0504455a2000c00b4029191411805642c480d103910441c00f80383c103081201042810984c825901c40c12400b00003100c410440e4500903070350f03000d05410000c00c03c0941e054000080c800b80100caa01568030f803001a03e400c03000020440040c18001c2a56000d0444170080704401b50b9a110303007044640c0322045030119003a0703c00503a11a2811006280c00a654810030300142c01e103038214200ea0119482d042c40543e405400300300480b4100400c0301c585500400220070804000c01c00341320307400c4044800700000907641100342c84054006080b80c2c0220060a25041031011403040c0010880d08099404d07a140518031f8403587d05c0d4803d0017400d11070019407503008005c544921603602c40c0712001e0700346502c407801140c0079141020103400440d03016444d041d17a0000d01c9400d0015000001c13120000b46001d0303042100d040401c001070038000700d80d6000841009880100000c46551240340302b01d0043c160b0700e641c207010320003400584118843c03d07401800700741d81440607800f881c4164510005c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 853953228 1250 853951978 853951991
    0xc1302090303180913050d080c0903030a02010b0a050114031f03020915030d210b131d1009081603030b04062616350a060f02090a031103010e1b04 64
    0x10030701616074030005c007905640c040c1c00500c2c481802549516040301660890703500b400700c0d050000745143e00440f09100143d445044280c81400c0003012100544000d080800b50a441c82d65000311501000f8200e00c0c5014070000020010804003428801458000d0b04810031460080c40600c404411403100d9800703882071104210072148207140d0b0320207908941d00b45138004084100c68034042d21304041100e034048100307140004101903074420320311111004595000c80d08522001642444819032003500c50900b01700251000890b124110392560180001c600c0e103032015424100d000707001c0030200e41c2c0c01c50301e4000042107245441d008440010014903000161500050006031a1200001ca8214103e050b542c103120070203007040c0044103071400d0241d140d0305620407405d0302003009100e01c031440e040e0412150300050040314002e103409082404000d506d07140345070000c034000200c80e00c00581174078075000d655001523a00b9001170300323541c0402003241c2c0001c52080807000f2006008030842c1c8164070300348 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 853954478 1250 853953228 853953241
    0x30503220815060d03020c030d2a0201050f0307210e1c0e0d031101140f1b03062205010b0d0c09030b040f05030c010609090c05060304050c13020903031809 68
    0x7004000c0403125826007005840c2c2d00240914828406401c85c20743c0101c4602d04130940342000400072a240c0d84d41d44d4050210051001100c02600d16950803d41c41544048030160740c11070110f400d89007451030140ea0340d40c0c0d00081210340300080385044030302000348400015070000782c2d0811303007240c4ca0140941d140d207030300800c000500007254031210010840807241003195151030b0030701c450326500900b40080004010300e20a4210b548000c251100d203418081800f48421600c2003040c1e0294071900c031000d201100c5503013102c2501000380914821101c41042030702d040302202c08141c40c0418420103105c50750f101e070058405a000f2140c0d5109580ca400040016288120003100880390040d40010203500d598441c511446c12380c000c141c0b150f220800203281d00352424411500100001080080c03208014074150558a1050348158424041481030001040700070504002d12201140d1404a01422000f000064091020000d0f0302d40404241c078a1010902c0d0b03d5641491400c440d0040c81d5510328 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 853955728 1250 853954478 853954483
    0x120a0f030e0a02011409010c060906020c0c0108132d05060402031605090a05130f1101090504060605090909100e03091906090b03061828330305032208 66
    0x3100640061540750b4101c4071703507040c50000c00041106150540c2904903c0d201d01c000c1d500144000c0f280250300194181c107180050020b1315440f9000d03c3c0040042c100242c1120545150041c050003810b40180c0242048102e044481c6240742c0c5d040c01410212080d0405036165102198168040c0c020f2054402c14010001907034403e6402c002c20007107180e01c900d601c0100404008020044c10f203100b40a24010403030070b61070800d002c0d124090796081c10800f800010000c148a9009030300440c00c0040070310406030441c0640d200000181d070040400c0c0d4524443d145014a200c02403900c951500541c1450060080003d06100d0020f80e10b880d01c1c3e1007a401d60140f0395503188a0300000074268001440814a800002e581040000300802810701070024030f91107034081681d0541141e030007200040c00550768906078030382d2080141410003a00782c5108000001710b2030807000c4100e040c030940084401c0510121020091500102180d1b200d410311800a0300424000944102c60343c840312002611030b400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 853956834 1106 853955728 853955743
    0x308131a100605090f0d050a02090a0e07151b2103050405061311010c020a09060b220302010f2a03020c210c12120a0f030e 54
    0x10301000c169100785a0005061000c00d00000300c00380d446807842d021100702a51100031805052404605203100040000d5010480b40103101c00c2e030320035500509010104208070f4140586807101c40a05104403985039000902000300c40505101c10800101a548592a150f46610603100b203082516440603000d00000c0e540d400f0803042c00401c04c10b15400100c020641031003c900c68036091031402c01c1c2c644090601c980c0340700410031034176904465402003031005ca0400c071054541d4040c0744542d111050b058182c43c400c02c00b521000c2c02c05c20b164411240c3c1619040c1e2a030080010036038281d10040710146485041c2800c030b0203c0102c1c060640503892007503018118440f006410003103d0300050040c16104c081d1407440c8000c960000440c0410b250701141c55151079500400c030b50f850404e001281c48104207003c00c2c01c0f40070743d801c0201d0028944850320140714100c00c0134000e035582e812 = true := by decide +kernel

theorem cover : BRFrame.Cov 853776978 853956834 := by
  have h0 := BRFrame.cov_init 853776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853776978 ≤ n) (h2 : n < 853956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
