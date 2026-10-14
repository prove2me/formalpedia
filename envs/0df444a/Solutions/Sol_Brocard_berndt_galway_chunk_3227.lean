-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3227
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:02:28.552717+00:00
-- url     : https://prove2.me/submissions/e8ebc742-1dca-444a-8a14-8ae66e841b8b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580215827 ≤ n < 580395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580217077 1250 580215827 580215851
    0x203061804151d0601080102090d0314040e0415050901151401050405030102030903041e0303020d0e03030d05190608030c070521070b1c0b01120c03060806160801051909 74
    0x22842c110303103944402004070759034146003c40400801d41140d200d9100e4180080303134585060080d40c00340440a40542d82644d02560140c0c0d41c02c0400301c455040c0d8105000c0041d0031544280428041c90180e0100d60380e1190421019003501c01c0281100d24036810102c00865410328a21a00101c130f00000f1f025441010000040320644580e920680c0e266001005000e001c60b000310041c402c50b603600c3c0d8200c14480301e0403200c815483c41840041e01503004259110741003405200d08148201000741683d1408440b6600c400c101c50081d1b405404d20aa03541d481c10084126202c0d01d0040d010f194001d5041c4032440940c07a94607551401101c3c007d601c0c3c041c592807200507901082140d101c2d4402aa840d42c3d845488000c11038018820b018007082a000d03d2050b03080c86445064841403041e0741d200c80420070007402c4c0016100c0c59145234101030b81d89400141c450410710059002d042c02481c00c523911103011400134000751060f0403451041c596040e4038003410480b401d4080403580f20742002b04406400398 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580218327 1250 580217077 580217093
    0x2090f07022509090c080115080304090203130b070f0210060e0a02070f020603040602070b060d02100c111005041806150e0f0d060b150406020c04050a0608031b010b040203061804 78
    0x35101070b00540c203211303202c403c01249030084815245083d008004007e011031800403010100d10403041c05030030402082c0b10005403600110350084c01100c02810340304181e0ba4903988603000700e4002001403400d918102095905000300c50100b100107000b40304550410309981170038040508468411580021440200621002100c4040f038000780070b42e889240900f41017001c6d43c0084d2003100e41c01e4520740015400c0c5480c0c4c1594044580280c620f0685144d11501544c02000c1c504040c1d409441d45202c901c0b1650340d403000d00303581142642d503582c4c07038a02e01040e41d030050a29540744411a0309140003806011400300041504104a00c0d082101c0e580600c003003207050000d484401d812041c0410a013040c4032040d0071100700440e0596420319040100ea0b0010494010b9001c0d950058201c144042d01034075168010701d0704040d0004001610580d60501c66265501407021500034040203c00c08a10f080300380b080d8440c44009513030035480c502d0210300295241034540c0004850a40b44800300b428010341e0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580219577 1250 580218327 580218329
    0x61b070509090d0e04020a120b0a050306010f060e030304060f0c0312060605040303111501051513090b030708010b0a05010309033b030a1106070f0f06050402090f070225 74
    0x24045079000d042c00b0603002d840300000b407110004503143d80c03000542070078a4401c6550300009941c50403030a044a180a802402c5980324150340240d541d00003040135541031118a00a0065201099074140361000142030b615000760043c6c440e80046c0010400327603420417000070b03642000f4a40001d1041c034030314040c2c1d84a080c3c000041210303442c12401140980c0c10a00900aa9000340c560b5410000014085075a9078032483c00d200b03610500600422050901c00c0b207460104412a0034107042244000c042c8034030010310303031004203201d860b500c881150341002e100c080040d00c8424001c0c4921411071012451202d221700c80c0c3c1e1704044c0d6406800045c580300d80390064013400820400d20b00b011b01d0061104c4120060310241d00c0000c000000c080161a00060405010f0f43c4400000e4000b07a000b42002095000220b00345c1d412102d800c4610b00151100c0464180d242c81040001120305050040c00200da500a118800c0600d052013449156a000220010014054801c0c202401e10041c8800c866140b5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580220827 1250 580219577 580219579
    0x302040c1103031003020f03010915110408030f031012050619021b0a02040c020c031906090b0703020d05010b07020f090a0608150a2a050f120a14060f061b0705 70
    0xb1041c04139000f44007900e0f908907802200d0700c0c4081072481c1c2c2014201c0b1030030308008198020110038518007200d56004100c88003000321000703040564507240542550301c9240c4c00bc01d5100004200800740d8510076000c0050318102c0200b4042d520310f0f6458035030310007000d007800c880c40e4003001a48903000290780440317020482503400c00c51644841e01c1c0700c640c0d92603a06000c078460750030543e00d03030503492000465040f05d410007001841811851482d4594410105d80180e0365140c03548003050104038000303d101e014400b00e6600581d2001003d41d014200da0043e00041411001040342001582d940d0102060000d82102e40f051161035881d41c0c080100300d0755000c58442d007e104100c03a400302800721294443c1540071018001e1181d42c01000d5080c0a00e240300c556012091b0f848440c0301803090700902584480442128940f0109905030f0510300003c0f02c0100d07182e92200c113059019802c2009454000c03c0503110611720311194000142180900c0364240103048542c000302c7c101035000c005410003480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580222077 1250 580220827 580220833
    0x15060d02100804170a170c0d0c05031b07030c140f01060909020102150919060b1504050f040501032102190c0608010e01121202010e01110309150609010302040c11 71
    0x41e20250103000d520040303c0c1980c640400f90816444c00c00d11408803100c141c016600d10302001c0300d54014a0545001401c1e02d00156001d03c40080050030307500c01c581c240340c01034840d0358992800202070400c10303589100f614400c0d0018010640000e4000b060071504541c04540c50b103482840340801c528180321440c0303a2640350300300200020f190300320350300c0f0401e140c0c001c0e802e4401074145c01c03101001001c01a150400350b688246c205840320040101c0b80d16107684076a2300450a10b08800005a003260500300000c86070707000150030019460091071415a200c015502031100750b141d03031120f582c89424680641c2c01c40d0301004034410181e01c24404886000c600040300d00c0602d146082c4031503100c546019400204184038004076001c2c440700a83c604a40c41c40d600c07503044480340c5d611440307420791022045055640300c05c0c0c20030780c0040a008070b191400f48612829101c0c50f080a08a16107400303940d4114400011106018058807020212410b403038040d2400700d100c00348090100d170211440281503410340 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580223327 1250 580222077 580222099
    0x32090c16030e12011407030b0d12122a03020d02040b07060603020306181f0608150916051806010c0b0f040302060f250e06040806090f0a0515060d02 65
    0x2540210741d00361103180a54a004028150600c003501322450f201780310728003080c4800001e4103548a44c010082c00c01d4060000a080200d565480e002c000b0054021404101029003200b880001d0744a20340189005807130a101d01400c0951103000a28620241810181c0004940c40c602c50b042d01280c0c02800c64907091980c07007455003481d100a00311070004030700c00c0c05208080b13801d0468508911002040000151042c000c850724031140c401101441b4454a5468550020780c0c00001d0080401e02c01c14090100c0641c9019503c060600e28001488000c203c3c503200184050303112101c146800c003100080d114619211600103960a01584d0002042541c0c0c84007004495420001c031140140d200e80c080741d01343d8540140d502400001114520b081d150b15403100c07050344400034510000e0310068100000c2d62402c0708003051595119422502840e4010800c4c000303040400c2250016424495015000fa41c103d0750b20b00761186514000410381c298600d000c00c02595408025881c56172340240380000031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580224577 1250 580223327 580223333
    0x220f02150c030304020f0301050f0c1806030a0507030b0102010507050f0f0d0207050715020705060904021809100e09071a1b0d11010c08061011010209060c0732090c16 73
    0x60351080790121300801d006c9080302e0580c1014080c07a405040250402681552130030984c0c945034101c0100450b8103101c01e401041903032901001140031328103c0724080307810319000c88013405862030309074000e045a250004220b4015448003c1c0c41c4c02404152425907243c52000d01d20a032800303501d84244400d440010041c08001000412200b01c0d032603801220440d00300000e040c1c3e1554210300c00d0a41103034040145051380c0c43c083c2e00800900c4c20301c807034048030010002c001c640c82c1c5030115102180c0c450030160511481c078108a045910000e020300400d90503041400c3c00303013805500310035084000b002150712062400c1e4080d81208001c0f5000846200d8414140d004003618050142c00600c1d5180580c8080100c2c4201c0c2c1c400d105400c050401c1805d10403610080700e2040302c001030b8010a542c248400c0f552a034402000340100d040000090404d9801c210741948181509002c800c0700c0310084039141c039110044103605001741c60465040d6002d07920242000c0f1b0354820038103104103100812800c4810 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580225827 1250 580224577 580224583
    0xd0b030106260f06072a05010510170102090607030806030a0803090a062a0509040204090207050a0c0e220c0306090317070509030a02060306061917220f02150c 70
    0x3480003442c2116180071035801815100c0341e0664070000001c0b03800a00c5881003d041d103102900c082c075060350741c0317101446894241c00c49205490200c441941c1500c20841d41c0c0a0031800450706001030000c501d010761400c00185148030f001d80c000e0034444507800003445d0303a0302072001d400100e07081900b0307a0b034a01d0305003d00c48d1a40701c0b4500481d442e0b482c243e41e1f0f4068002460030700321901b1b240e00920388104079000044d912a00420034490f44550200804140c1144c94006403208910450041039a209549407203a50f25065070404822025140e00308201140942403400d03041d6000c08501c0d54180f0b0314246410710b14040d40002d054a42071101d810100f56000118254440451381d015005446500c01114030b8410418200d5041d030004204c400035191010003542c0006000f440300d450441e040e0b03400b5420001d00e0700c000c404a504860160030031070010600542c094240c0059a10004c04006d880d45000030714032000c1d000900102c501070454961800c0b541184400764451911505407a0155a0b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580227077 1250 580225827 580225889
    0x60c03070303181e061104080705040c2105061f020604061413140a020d080d0501050603010b18180a0b191d19050103060b04150b0d0b030106 62
    0x40020f00d40514000c0d180722000800c00c026500003d03800c43c0c0b003400a0540011300004009542c0c0e40c1c0d860880b200f980c081580240300411400c0c000d04000d0345081c0030001150a500c9400d03082c03211980703203c560150985c09101199400d403038002840d0300e40c1e80c082000e104a03050188800d111101c600341078180c000440c244941c0c424442409105c240002100e03100900340d812260f400290401140042c0039121070b204c4200c2d141080700c20400a940000f503190740801c100780e900010000300f010b41c4015502465002d0002910304c94519458014070100a105841c00040c5951041000ba038840c0e0315000f6804c081252071080a0b014100841004024002e405e00c2030b1244030b130000401204003c2e40d4035001281d500018101d00b40c84100760001c61010020081d91402d64100860400d503501842864060f40c040c2e400000e01d401c450003400104e030340d04840001802c80c006010001000c0c414200c442508042802040d2080721001081c00b521140c3c000c004110030020003482c102c26030804602c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580228327 1250 580227077 580227083
    0x280b030303010b280e0112141f060311040504050a020919060f1706010804080408011e0f2d15090b010f1d19150c060c0207062c060c0307 60
    0xa160804e0011180f41240c0b1440905002c240f0810400e191580520306402036074051407400300700d40d44504500441a1811a124022040c50199024810041e00490005041d690400b0040c2003410303004404280250700c2000d10898848001614410841d010740315030910140070721060520150f02c81501703244030301405001440191021130380500c107088500780205c56041d03c00b4203884950044501000080c0155243d20040000040d211000d200750340001c0c3e21007071800d0081c1081d1204c8030982d0500084840307441e040c14004042d100d0341c8100d100005000c8418501c0111b41c07401144042e03d920301040c107040710103003400a80035030f45420088c20b08009030303100f9603070002c060019244100640c0400140c8401078401400d141010010b120300300316001c1c0542d04517075468081060124001141400296100549004002880c02810a032104a00181444606209008100329100d0700030f0311114954481c407422440c40d00d0a01c0d80e08079009026242d0322001c20724250360700e5201d03140c12 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580229577 1250 580228327 580228357
    0x307140a091a09060706020c1f060503070e0408031501120c0207030b06040510090902060712020f12180603130503031006080a050c0a030b03070806010824280b030303010b 75
    0x204000b9100c4004664000308010b0140c0e06001c92034450400a410404481e510340c4604982d001c039030708441000e1421100b0080d80402c11074284070505041c0780031580100e100d0f031082070602001072080000d40754040710400040e4001080c48004a80c15050311030300e940304902c1c1c80c81100c100395001c60350b1810349000b0381103819036131126010300003145c004a900480c0c040d005201400070090f6600120704003400102960b0502149440e941481078850740100301507881008040341d622010b100b540e02c01c0e1410700c2101d00340982010740b030f8103041036054200d00ca40da002002460701143c100031544007035007100071030307480e0724243d07416606054150280030049110480024980b007118050144140e0301c4e44061410708814510a03405007544005450741401a50008114440c0c00c00200d030003440040d006188a55a42c1c40c5510314400d8aa05030306032032160800c01070300341456038600c07058030034031034004480300f1107861100021700a10301800d6040c0400400000c00010200181810001d24540303 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580230827 1250 580229577 580229609
    0x90303090b1602012702010c03120f0b0405070c05100b0a09020703030204050a08030c070e131b051003150501050309030708120103061d070501080a02090627031603080307140a09 78
    0x1407120206544c1170240c20704003113a0b0424019446a0984002c041c42410100020310568031b040c0190341c0d8980949416a546040b0080396240c603000e40c0e82c00100c00e051410044841d61540b80c0c803074860701c030f04c041055124441d034007440d140c850b100d00c000c144651045480d0f00c0c43e03250050295000b0304c52a84103401d14040428404804400c803180455404010040365290000ba901048002401142e0b0624030b0107034100030806d03a402e8054100c1d40d00403860b5031641400e08104500300600f440034100742ca0301d460301d080c04041490020681d4000d0810540342e42c0c910349030034038512071000300515a01c004540414940103601c95030f4103981c031800c000c1c4009441d076100d03050740030115204069a503011400400c90755000c1c8051907000b84400c0f8025182c020300001194140d0b00040c00b061102032012542e4041d190840424036407004102c0107070131146940c40e9075002d0031005000c050040320b000070215106500038061003035404100000940c40c0d000c801c0001e41940f14a104181d441c20320010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580232077 1250 580230827 580230851
    0x9050f060a0e01180c09080f060603100e03030c16020319022403131b030506010302180702030a110a0204110d05010e270a0b041b12021003090303090b160201 69
    0x2605040e52802e007a84445000301c2c4e90013501401d91940004140070710070a0220b9030840034480100d00000070402891a4205141414a0916041e07036002c00300c0d141000c100170703410000c1308036504003407020141c94941e1511301c10703a00d020201b0b02d00258548103140000315802c400361544200c00d4000c861401c07520042d45200c0f80c08070050820301300030810410020f803101e14005681c07200d5038054411300585190008a01400c2902d5410984240e40301200400c21450b01c20380032501000d109440103064100010047d680e8098072100c2401d00008c0305800c07040e44401c01c100342465400400c18000703c02c201a440344541d00558488210b40d00301000800c000c401042c1c2c0d24052624404030300c2c901039607580c040c80c12490002580045000701041c0720b01042502030300601a50207000d005180d054078803803c0c0b501303c0c0c00d588008940403c0054034005a554020702c050b00c0445401c0c082071701103103031500310b006000b4003e0050682e414401440340d20512483c0d101a1542603030001c001c8065160 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580233327 1250 580232077 580232099
    0x1005062706121614030903040e0907030c030206030a0b0a030812130309151707030501080d02070612090510050a1a0f1f090e0c090f101706060409050f060a 68
    0x15102140d014002d801080c000c00f4500380c03071110002e403842c02000c2c0d41e94001d40150306a0094455040a520200e810710a0300481d540c41c54011004400510340c4501e90b503120141d480207840045c0c491900800003407092038507900140407900d4002d08540165481e441d0401e8190000c1d0700303041c0e0406c2e14200040202c01c08041151009825464448480e071501c10b003a10396450642c504410460152084250701c402044428003034940c0e6200410310350304ac5140d8a203090040c58040c000c41d804280c04018494205954810307002491801040d1030465041c484d107050741d40c1940c098030318500000c00c40f295141ba8401c10b64003e0003404502c96070902420050b210a603a4441782c1e1103501001d0140c4003195400c0c030105000054280480400d0740c1750030080d40701100722000ea450f40d4000031040c2c058940104000800c02c4100c40d40c100e5604130344c900400c405949030030b841d40f0002400200b88541c1c0c03908140d80051070b98610601480c42c00b6000f2018200084d41e015016a940003c049080c2d0820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580234577 1250 580233327 580233337
    0x20c0a030e0906030c0f01180801091101050a0813030c05030c0106090501080f07090e0a020d1212050f18011806090501060b0a021209150706020c0715090302091005062706 75
    0x14000c29545d80c080b0308201011050030b4045052100b5944920781c1c1551800c5008010310f0400000102d251850074010112084903118504005041001301091a0440d00180c0c00c05002210502e09a0861900766403c44000d207014081c1e20011030040c12003501500f0030010303200507400a10241c1d80e10b0300c07040c0e580c0d6802c0010602a13000309009000036001c980c0512500d890000484030104181e802181c102001c02c04280c0d488074071030403d0055140c100d03421805c085241034080140d450300008000380c80c0d0001d480708601c0c113400300b44460034603425048484600b4104d210340c1c8002215203400401007001c110110b03055401c082000440c006110155074070304025402801c01a0000300382c144850703025000c010351000310211021040410070b00034001ca144107100c010380c1ca50b041000580742c0169070340000400c12500d642c0c549840c2d4003103484800c032a030503142c1d034105131542040e0080280040d000380e5007040d0049140e02e00728407114048043d1101d240f003445004411101401003501c62 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580235827 1250 580234577 580234579
    0xc09030d0f0f0305040c031e060b0a120b0603010e0f071d0106020c06070f0b0a0903031b052d0304050a0c08060708220203161508040b1501050409020c0a030e0906 71
    0x5128502e50085000c0c2e001958000e100b00c8020304015243e0303460f064000030407002c0c4210714805118020800c15184140c2500c85d00442c0c442400500c0c19036410b140d27101500c00100307000312100c0410501c0e1403d4001c8080e00d94039a040e41c03007040e0f00400984d03480300c003032140407101010b00040e250003218480800d416100c0075409040c00000f10310a1081c103608c1320004581842d0010a40f01c00303d004030503014041c03045407202151686103810001c0030f03034504001c00c15070201402c115541c100d0f0440f040f110b613010040c40b13103151a8100c548001c000540c5d450411803681d400010001046008210b03009180d00c42c46450102030b490b6801e155660790112156030110351050003194100c030112136a0681095402c48080781c518140d40800d051290004000800d02c400d40800c3c4900d031403580d410320702d000d82840c092070b440c030340f64a403c1044c00d006004440c08440c20400c0f004964490340845024009a91065544e4200d0b416140e564105407002500017800c1d800517442d040c60010105800b03114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580237077 1250 580235827 580235837
    0x32107020d080c18060c010c030c080105061c050a090506040c080105010e10031b0b0a0c0501060b0a02120901020f070602070914060d020f0609040905010906050a151e0e0c09030d0f 79
    0xc01d002d1400485138540340e603400038045c030510418110074054102c1c50040759801241d40404024040c21894040c4c120038405c4001744080c01e01d110751035032104071460510700f0100307017511000031000040c00040c00180c0035002c0d500420061100300000031084400d61030017081117a030380b181c0c1755440c9007040d25010301507113070b40303004002007190b9141c50701400a0300103c0d203810554071a000c2840d580b1030f020100205414221500520400b0b100b400018404490315521704034074080300035103030305070800000610780c00801c0400c03e6910030040302c5a0315100300215241151603000295031465103115000c02d003401c14294038280314801d401140a000060701554206109900f00103110f2844803030560001020321031001e65998034010f0520b0140100000940900c03141446810381c1d41c018055076009003040e4101003901e40100400781226a410340040008000304a02511041590322107500c0d01c9100042c8000303100018000d2074a403030200d045900b94101100e0a0b168403540380130040c0494 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580238327 1250 580237077 580237087
    0x30903170c0f0301090f11040501200a0204290102070b0702090702010f02191803021f030b0d2009011a09041e060f0b09060a050c032107020d080c 64
    0x500c00c110680d040701c90841c045007010503941581c160798009a1000a64507142d90100000d15601e200e248401502c14001d1440c185c00c10002800d01540c0400004045c50103007025049004107102d48280503a004005001a6508040582031200c1228201940c0110071160031b0b140d42c00001c4501c204c4a909194600f8520282c080000f042c80003000750043d9500d8004005103280107100921a65401001c440a42c142840e00180141c040c02030000c1e22901ca5501072026940d401d4410404c142c0d582d078000c1c01001f446004801800140e541c29030000c0e4050510006c1000700c202c10318000d121007540c0f65000c1c035003004014200030300f8402c88100304400e002e002248040d62004114601014202081a6155040c1800f001c200c1240e03221209a80e000305018114007038105c4001400c001c10140d040c4081900010400c0c400c040058040c848000341030f59424400f8801d8440c0440112400524039800d55a10160780d08101c405034014020082a8040c050045c6041d80c054002c0c2c0c20b01302c5c100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580239577 1250 580238327 580238357
    0x71b0801051f12083010080c0303030a020913050a021216200c03030c210c0d08151c0303060506071a0c120108010b040f0b0f0904031806021507030903 66
    0x5a105075214145e1401200100044109000800040d2071080030340c5000351601c2118840420704030b0b04541183d8001d202c049455a4002066907041245440010390310382242c0700054002030350740d200700c1c8800d06180402c4820002c2d54007800b910007084444c145035035604124034107404141c80d01d2a011400751000005004030846500a51000900c00c5802d07070120240000d00d55040203541c01c8841d030111241042c0800702044410b00313111001c90039420200c008980c60f80f101c0317130000d40d0780801c0015800a1840c200c83d2041f100c035a034014103c68503202800d441010028150f080541c0031906005c0b0001d00c5007000c000b11061a5041418400040e41c0c15280d850041e4025040402e0f890082c040000344040da408903500030003020000052800740e6800707100c203075a12281004c2c00980b400406142544641041e8104203d0484101400d40c2e540e14082d21110b42285000c5400b50070345102168481d00001c905460002d0a22203020550311240d085055944694000f00010009000030104d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580240827 1250 580239577 580239593
    0xc010f08040b1504180818040605130c05040f0909020906030705011407050309100f090e070903060f06170a1b0f05010f050702030615010f03140705071b0801051f12 72
    0x404400180040345c28035904241e0b0131142400042030340d40f8000020100748603000c0180d07041601c1c40c01d81c1c00380449860200010807000b08181840c1070340d502c40c3d2602d03581d140704401700e9014001c0c14010503044c50b16840e1041c0107106c2c8ac10201c0c050f240503000b192030f510300041d4a40440c3c005a60315000c602c00b89a84d001d041d001a40c04071294030050140000302d43d240d440ca15500d08240d81c64191401491000901241c0e05500007807400d00c0741c106000b14541c2c007003403200c2a07079004000030900ca60540301010003082c0c02c1c0d012490750072030b401000440c031401190007141306000343c03128500401c0208080001c50000d01c40c1001d4807140117420000c0d03500407088906911a141001402d100c1d054000c24203214080b914001d8451990b07002904940c2c1040e20080d1900e00303464204090740c403602c84c242c034281d4043c0c90780c02400f9010601004020f0481040c0c0558607020310079a00103a5103440d0180a02010381d681e40084c182c80d44c2c0103503800804070940003210410060101040c545440750b9038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580242077 1250 580240827 580240861
    0xa0f1a061011070306181a0601020a020d11031002040f17030912070906080304030c0e102105030d022d030a0f02040305030a020705010e040c140a02011d0c010f08040b 73
    0x24070b901403040c0010124030703540316200201c44c0701c081e01c81503000c051500c03821801c0d40c08168a091b900c000140441640d001030b501c43d5580d4156039000c022001c2d401c00c07400d030401224071a0ba0522410039902000e401503006001120030a85003c400580c5030070300102400c1034101d00003902d40c0305002d194030320704d45030582c2c0c03d0448001c02a100d07040c0d140c54140040c0c07010768202c10001d0344005020410090040031711030061a001208410031704110f84400c2092503544500703074140b1003105640c5199030016900c0645294800304032580c4d4107410319800060340215010000d880718444400b03504000c1d00c11000300280d20a10114655950b007a00103004214140010020b642c0c2800080001342c000c200820300749002d6002070941500d000001080c41c0c140c074110701e0050b414884514a1190002c034000c1c0c01103c000c1031503445a0307500008a00500d41d0b96460f00c0c078403c0700400814490404030308200d2014003a41c4014104c0d00c1c0c00710a8030041426030f8010424480302c000216000340d8240c80030303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580243327 1250 580242077 580242107
    0x1a0d051e090a260909070507110a050f10030e0109031706010f05040911090a06361a0910080108070824040201020106090509150a0e03030412050405030a0f1a0610 71
    0x5080c04044004503012103402c44019001c100001082014000c4520139082d4020701140d0010142f410b00c0d010485104416801c107005002d003a40e000100ca010381c000315846080b64000300603502003400c0013800c1483c513a0410351091060000304005500c110403050f210020f030340b109840d1501c1d08061100400c81004000c11107d41072040396003070f035104042e50700240301956520b401c0740c600611280380e10300c1d41e00c0002c000d500e00c0203101013040e001c140d52208440040c0c602d01e0360100c20511b41d1308944140c0c0e428503809980803151001d81904040582c0c1a06c1c1180f00300d17507060341c40300000760359076590b080e9054288c01c15602140107a002d548001e684140b0620002c00c4196540740100240c07241a2258000ca4102801c031095408110025552000c01000103000ca024018030480c1c480c40b0190024201440040074030b050a4000c20480d0300410001d009c4071030b414054100040c1c46031042a0403211580fa0034940d02100003821012400f8110085c032078409520719040070349603440450320315 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580244577 1250 580243327 580243403
    0xb04030c020d060507020c0f030c010e060d110a170405070e150a030309052b060b0114031303031b091403010608010f0f0e07030c1a0d051e090a 63
    0x4401070b26602c0503619400e129034004111030070520b90180c100341c03040440c0c9000d6501c541085049070713400140040301c0340c401c1c28544603058940011500701d00c10f258501208500f0101000c6501c500d0304018842030500c0da8440030003015140300c201307028100382d901400c01c0e0b001030401e001c2d241c5490300d000e4001d0b191018000c21000081e0204d10880c03499402540030486852041141d402c01c11b5409c01d40090f40c1e40646018164840104c440c1261018040c01c6c1c16921018803001d83d01507000c0b09018100311040c03e1303c03880c1802d40c5050744a181102140007a091946010a51500340e40b01d083d40a100d48032120401c0c104025070120300071000007903070301d503403107400004a029080c401d4580c182c42c041400304003018000085030030b0300c80110040c142580000e03010404240414900c0c0c0a481c40402c44030541c040450600445018081c0d4490b0350510789420b1107550247e45440c02c000002000780c042483e980c3c1c4540688514811101400390104401031011100a4801d1240001d42c00c2c211 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580245827 1250 580244577 580244597
    0x306090509010f0b0a050604090c03060302220f0501050f0f1314060a0b0304080a030b0105120723040f17210a0201360501140c041a03060603040b0403 66
    0x11120546205444500d416590380c1c3c1809103491113801248034401c4240c2e09604103602d000089980e134880c91040c2643c81ea92038148142030f51080c0c203c0c41c01540c00521070641c181486036103140080501001448403850700c0b00c00d031300340c64050103503034121000140482040d8100e501802141c00d0900c0708250700000c1c0d80d801035900e400b5441014806810028ac0445174500581031003420b01c1c00e070300040d251100610400c80010680c1c004c403500c00703c69142c00f0541b030218500690b0940502c1c0c0a205803103960904000c041da5000c284c3e00d04421a4101260008860010110003840b450140785219403c06100f0b0000c20407152381451100101e004544400341001080c180580340d00850080c1d0040c0050412400383d824004c002000d80f04420400d01e40003150b90084039052004994441407001400301c100703009080d408068411640d4400c42e425250041e21200c480c0e2080c0581d06641c0084c92000d840c000f11401a6072080b00040c101b9480c40e2031b940c6800e285044010011010041c02d0b40b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580247077 1250 580245827 580245839
    0x1b0c061a041a2106010302121903050309010b0409020307140109081603142803051902010219050c030a0c0f0501020a051306020604171b0105040f03030c0804080304120306 75
    0x110b40440d0544005648490214040800014000d10803240004103240c1500c030003041804510f007811680c0c1161110745000101080301c0c2850880051a219189030f22142001c0c140c2000055216607201c0008000000d98102040121783d0301e23401c007035010b5120800074081c1c60960604000b0b209070504081840f9235031605d516103800b900c0004005041c50f0b102c410401c10481100b5180300740c6108024144c1c02d415200020002642441036850711406802e40c04145402102200c1140c805400500e03c205070502019002c0d51140e021106000d05100054030418400c00940350480b500307a01031407421221f018100c80b00100b0b0001a102500c1c01448040002c0091004002c43d201030b80b54251103500b107000140c070071401d5910500c20764005404000000380d58080d08000203104203d00364540244ac42046030000c10504460081c0d840d00060009111411581c069054800d44c0c090102500900d806c50314890203440c01850080240003180020321501d0340246091441d00c0c0001c2c440f40c0e505 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580248327 1250 580247077 580247081
    0x703080a02031b0304080607050309030a0e0d1a0f01061d09090f030319060b040b09011101060f06020c040c09151416140c0609011d04061e091b0c061a04 67
    0xc1c408000f41c1d0300003e070400000900f404115840722040c00d040d803d5240003283d10f0340b41c3c4103c40c42001004030024010080350b6407018102c070426001390700303031020009180030345819400556041620001c0000005040742c8241110459400f403081c011900e1403a080030b00c03a002102500c0c0000340d0007210701c01880070000f0406544104070310240c6c2c2e02403d48410b0080100c0d41c0540151079441c8003040180310a01100c01165544071080c81c011901e02903200c0598010300701034016841e500d42410700083c0895000035501c805542c2110308100c1c0001e031a0b400d444280c40c91080c4400b01c0005510014560701840100768084c5501048625103503410f421044240403c0030201d40ca5006070f0f8805801e0700c02080554903d0409841907031500c01c0d003070001fa090790b44008080c10150364070301038240b158039180c000100a000300211294a5680c64919074038003003090107102004c1e8075008038549140c01c1600c0114940c9042e17140d0030000303403450310f40c0030107403909443c6d52000304126200381945d40c40e18 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580249577 1250 580248327 580248367
    0x7030f0f30030b06030c07060b09090c040b060703091e0b0f0d1a0102060a0e07080a0602091201090f420b0402131401090305011503020a080f0703080a0203 68
    0x1080641071190703404240070890759009000001090700e49444241d507621400100ea4002000d0802145c8503045032500c08050004e841085401161180500188003000100d045074040c04880902c4000022014444a27002d040d84c06070024001e00b40c05c0060b04c2d03000c440c1100c00c01030b08000e040031710346500c05800b2603403098440c902c0403400000c0b0b140c51641213204000d103560094070005409070941c0d0000f0343c1e0380b4001e80311050b2656941d03e02080c4440c1003200d030b8000c01c400b206803140c6000b03034100b22000750400703108a406081803901c02c100814042c803541e405164440120311402406488142080a41070001142c0743d6005c5030710094045410151201041d800c002c1d0158480264840c5003600d0303140d0115801030340117014460305103020a8030305080e1041c00c07040308843d40a29004a81083c0b05a00182c03c40d46002c07160200b07007903100d0a54041c2c0303009841c4c03c150305a9410503155511190700100300305030003000060002030050401000c1c1c6040500c112410240440c074444255198 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580250827 1250 580249577 580249613
    0x1a120c03130807120801081c05090609040516081608150f04140103170c060c13230910080a0209060102011b0c170f040e0a090f1a0f0907030f0f 63
    0x2481134070718516a000c203196014103140b0300501384009800307001c11800700d14000d04800f03000303000c5007c2c40300d511b64034142e5001c0c44004005100504050416a4011002051803000640c0c0c05c80096210540302074a40001000c0360385424459440b40890a6812a01c0c40d0103075201d40c030b550b405c1c6c81c1c6544a0288540701c00c0c00c0c040000007540356180801c501461040c5040c894002031141d44040c02020500d640d2210300702e41c1103603986800d00c0c01c2144030300407a006130340300000c540c82c4c0002d0550b804a540501c01800e451514507519201c0c00c403840c103001407160384103a0703000303000c1c0b1801801c084420301c0d0844418000030400c0080c0c071004094108544200070009008000d088040c41010a050303000b12460076580c601d070400e6094040914800c0d4010328021481d8840461000b0b0b41c1607000c11003854001658080c2e050031032820025010503034500048525149010885400c3e40100d9240103094800c02040802e156a0b075910004440f0700701928a110703d590700d1400b02e03000740068014110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580252077 1250 580250827 580250843
    0x30a0c060f09210206072a150e0a050f011401140307240915050313140102030106090512072303070801021b0706020601060f120209040e01061a120c03130807 69
    0x8500b90080c41c1002c002d1008080096002c0d60740c0102041142280c801103001c00c1c1c0795041d81f0705040080c550a80c1003c20070310286001305003100081d0116041001500c9601030766070041044000ca826103240c03004e136007204500040100b04590b034021080d00c4021010301600d41301961101c01902d0400c614491a2409104001130703044650b128031a81c0c060484408010f01c49408503030010004e01004220200025501c0c40000901016040441112010074003d655030b42e1240d1004151f1413071441800c6c0100203a0099004207072011070741c9025200004246d02100c60036201401400c0c144594080d058002c0c82800b00b104042030004244040b60a403004401740000180c0c070f4540a0507134401300454201a0061140030b610200100007840e4500e000306540d8a00c045080007841003075522640146046000c0c500e03104107401240440c4c007146000c285070004800441c0c0140f0415003001c16040403080050250701203980a940c2204103910240c102c0d9010340e440c002e0704d900c41d22040e40c3c910 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580253327 1250 580252077 580252133
    0xe15040507051318030509011107060210060b120a0c030e010f0617150703021b0a0b0403320705070e0a09023d051c060f08030a0c060f09 60
    0xc2015503c04040b503400300c00810019110f103d80c5041e000c0050307070060801030300040001c0a46e1203000515412620b9005940c000380e61480069914050104d0403003c0d83c0c281200016281621015241e4080c000314200b12203a45030a5801d0082084816810038960303202c50742d00b0400000d110b10b490800030b40c0b000040541c01c04d20172040e40f000c1d43c2e140c06030542c41008082c160705610648a41c000c0b0040c2800742e11241c8036800c00011048000e40449144500c59500090116440609004034007075282c11160813120312a192075404a50f0040746080d0007501c04034052034400005040c1d131030003901a150550703283e9080112031002518481c401940310102401940341a080c45400480c041000d5404c00c6218030101045900308000d01c807c0e0f4646100c50320720780d8050001c5951410f0410580300141c1d06414000d07008240a00802d03080400d081c030081100700300082121700d9400c89464004414403503507108805004c60070011441aa00c490302c1c07100249000c0b00d440840d12043c0c40101c415 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580254577 1250 580253327 580253329
    0xd020309010e061b03061f020307030f180308211003050c0109180203060a1814060604060203030103262701170105040f09021305010f09020a05030a0e1504050705 71
    0x2d20909004401650090002d020401a84100c0c00e004521801529a103e560f440b00245540545883d500d03207600c4801c0c40c500301154040010143e1610036110722014448000d0100c0d40d20380c030040010031200e82c4140c00d0004c0362203c0094590005005a41c6030700c0f403440c01d07130341401c50000e4a400041c1d11035044240700b040400d00c41d144c403622003840e003062040d00e401c15036048001290780c8016100e0340003000c07407415125030807120042c003025020b991081c5841100f02009044400380c201c00c00c0c00050119003145402e1045034210784003940114196401c40d00e4481c00030090540600c14808008031050b0f443c600d05020340320b1014203284072080f0000a03002418540744440f00381d810001c142c41c011450003050750085064500645d000903000440c4105c1c81c0003401c890341c000e50300c41401a60810f0892017038000c14103840c0c0c0c0450302c04205682d512503c040c0d0194015500120f01c05000081400000e0b034070007012003201c0130480301c24161240d140b021508041d074040e07d00b0f410601c0d09100b5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580255827 1250 580254577 580254581
    0x7030b090d02060112320f010504020f091008060403031b0201180312022701030b1002060a050c0f07030306050114070201230f03070806040c08010509040b07050c01020d02030901 78
    0x444064440a84650500300304003c0d12640c05005d40401600c5054022050000300000403200c514445c4100d0310364804410080490001c41070601c17160701c911620240c08000601801340100c0d4082c0452055400050400c108000020010340d0344294241d0002080442002a030b40298040d40300018040104d00804610300540740c0503a055a05003960010940c64a02c164440150907203003841102c500c03104d0f000080c0c411010781c56604d943c80500a0110710410001c8288104262410130400c4645014002c09900c012030390070250700040001007080c0d50940055900204c22052140341c2862081a001c040c1c2150a003680081d5840105201c84d50f045050182d0352202d10034240d0900040f070740004d290000c1c100c4a40102903001c000616514580f6003641c41d9402251920350316850100c000030308030441110704a00c650309082d0400611070060801131b0584401401590441d50342c3d454001103c40083c000d0420000100504802d01c40e0a1010b030000300420480980d40e41480007115003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580257077 1250 580255827 580255831
    0x6030c0a050619020115080f06090706141c050a02030403020607090b0f13050a230a0e180c03030a020706021203070206060d0f0f06020d0f09230307060e07030b 70
    0x20180203114000d00850b40c40c00b054440071001c1000340d000080e05024101e002d016003600021800141c1007011030540804600505541140401c8501030b5803090307c0280e0710440d902c685000310300001e56105143d0641e100808641c07510b4464011602c06506801c0d08135041110035441030f070f9010060000b01a410300c0001e412500600d40404400e0070900e141d0010710401030300b140034110008100f0300c44407134030340e0b01c200a0200802100e101c0f07650300d0084c8070401010300351948030358000c5031408580c5807001c0d00300c060700c0303502c200c448190f501c1e0806000f905510413001240b511521032050025542040100070181c0b841c0d0191203050300d0700e0000ba103000c1c00040c104105040a00030040c1080d8005211517001d01d0031912064910761170b040403012401000c102401000b0001d64800130700c5102e400502c22104050401c01c8030a9418081b00110707103821000400c0303c0c002e00c001c0e1104c0641880c1c0107841a0071401070380d24141d0300c4d0b80c890007110b4002e921556240c115441c00c105101000b01c1c40ba03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580258327 1250 580257077 580257079
    0x70509010b091c1e021503090a05190f06020a0e0d05010605030c0102120a0e210102041a09030d0302030a1103040506070e120a120c1a01080c0d0c0e1b04060806030c 72
    0x1104010441c0d84403120120300201004802401c544e0060640d503500d0300488080d00000741032556810710a0f00b003501d5044101003502c02c0d200e0880c20404500140003905103250300015851401c101d15501c00d0040d611000526081010318104a4229a02d003010940705038030801c0002013051910341410f0411012071241415034114100025456401a08540208a01d460800f0400364110f000a2080c400c09007001d4480032840314500304a5015802001503c443d11a440410300718040824a180302e1072000d0350f0075400240d8890211402500519000032180802140c1c208443c014001c403504100c0b0103990550003d0b040c02803c541160a071a84000159169030100c002c0c4101142d0720001c03000010044022034028111140c0f0480d10000d030280c1c0200c040e43e12200c10406244626020300445c42d1900440406402ca450301c0c0d8107050107240e00800a00c0403501d00100c004906000801215000502c000c0c00c12402241a00900280c0210340750428542000b2052601e00482c16082d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580259577 1250 580258327 580258369
    0xc18090a0f051e061504150f0212030915250c0b01060503160e040f020a03090b090303270703021009140d0f0213090b130201030e070b1b070509010b09 66
    0xb2200c03101642002503032007001175507851404d4400b980104898400c503440a440c0880708100f00074911307070080381c45200112960880f081003016041080b802d00c03066803021000c1d44001020007040e0b2380c90152330b0340144603804042e010f0500c03a03402103880c0780180034000040c0c0c45103111010070018080b00f13400b602e079910f04542175107400207520f5298a206013460007481402030030042107a4883d0000805071781c2c100000e5460301040324014020744440d43d405c031401d00c80c44c0001150800e000050381d11030140c22000030700118903807a40550003842c1e249124403a008031100480503844014042204410030703a1807800c407a02e0240b5000e142042588070902c925a01c40704c0e603000ca146442c0d070301c00ca103404540240701050500e040c04000d02444900030184000c410400101c55920300032440f48070300070b880a00903d400303d40041d45030507090140582c00c2d0018012039004412402c10116803200c0d550480710100d44030400114580026807004114900000d403074005400c114221034454a0341c1d44030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580260827 1250 580259577 580259611
    0x170a0605011704170714060609070203041a160b0601110304080a080a1806030b010e0f09040f0804030c09150e0601020705120c060f030901050711060c18090a0f05 71
    0x1c00c16850001002558241800030030140958a2030520b100c0314208a42039545c0190b1412a2001e40c85803d1000b0703a0042c60000b552504009510324801c8a480d806546005c1c20140c900c1c100910041c4403041c0c915051107610303a801d8007048080c5040340600c11440c0c0d18a024800180004042000d013070a64005110403c00c102e00060400c0c0e0290b842018691500600c460443d01042d0384c0781908074100301031000040c60340e01940710141c4c0c11001c2ea03458582d21090802c0c0040c65042214050f000b42102d4000350101e13041c045c2120080f480746a03d0391402d5941e031500d900300020b40c0c10254010707a03158103554800d075005c1102d50042200001d444c03120300c1c080c40042e44850b0144510f5001c0c521800c0c000c91620b82c103101c1c420001e00d0080040e82c80781006200c030a4680c02c1214524000c6d0700e8440414618cc0c01907144580107420000288042d41d00e41441038019003000388013000e030701c1800c40c50104d103580f0300b05140c0c49241000400190b80180d120b504c402d6404c0601402d612900100c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580262077 1250 580260827 580260829
    0x302120304061d060f1c180f120c0206070311060f010b0d1e020409050406200706091104110d050c1309020f0f03040803091228110d170a0605 62
    0xa1031110b4400c1d441110f1503c60585000304a043c0b00b01140095078110000e00311500b0042c40b20900308800518008111543d600d4802d418902c1e14400b001d020410a04090800140700750142071107040c0515000508105a6003c034606801c02d174022800306c0d40b220203074a034020302000515480407015800c2100c1e54036107040000b01e4841c200f58520b1650312651127000501d1550000e0031400490b60046507a00d507124803034030040c90309840455605082c80480007440b0b80c50000c7d0229055aa08040c0c41d01c029aa2200000c000030102107903480d8109c0382c030f200e00e40e840d84a244401d004e50074286e41e448140ba80388004036480200b140c168040305204101c0e180d5020b1182e44c045d00d10f0003d0041ea0b900e03903070b21a400310303014510001d40f040400000b040100b1442c4800795000300011000c40f2045101a11100024001e8003100b0701140a070300000380015110395440f00400b0843d09040c040c14210340e4581c0d04000c022500c140229110344034014112404000c1694001c411400070003110713003064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580263327 1250 580262077 580262087
    0xb060603070c0201031a090901020a080901090209060d060f050106030218012f010219090620060403080619080c030c0901050d0b100f06020705010809150609070e03010f06030212030406 81
    0x802c0180c1007568034440006c2045902c0c50014025900400b040d600386058440d0502035071054502200140c3c00300049080c0310414000d401d0880d90007401c07803d55564103030900c20807845051003690ba8507200e500c81d584c00316a611606020f0035950754050b0780c03603641036982101500450907060400c40e020015020008002d503601c85418401505042c5915002c41c031a07001e8001c4c0c0c800b14103e54018001d2070100f61300000040c0c200d03100ca88441003441090820120400c0f40014100d8407a004580080c0000f407162075481c1c2e0000e801002c8006844280044101c10710007a003180c03c0e144d100020000b030910f400c106000040108440c0c0075150b60408000c600c0760416580d005140c81100004210340c101c1c000303062006089092620300000d40c3ea270341c1c000e5440380144540e602260800011900d0714901080c151406443c0c003980300a2619203100b400701848008003044204880810300890f150740a0150b61011107203054003042050950041041d07144013102580601d900c10001000510b4000d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580264577 1250 580263327 580263347
    0x5120103060b031609050f0f16033602041b120506060c150a2a0c020310020f090405010f032a030b180c061c050907030f0c030b06060307 60
    0x807074070120306000b008001c2880c242d00312034400f000301410304002ca0b00600c994003039403042c104003030044a0f40d100d40050705081c4074195855155400603905d03245940b8042e4200d00c0d10f51604d150392076811900c0700c080382d014000081d42e103021640c0c0c0314080c000b549400d0281000c00d08589141d02c03101c44030b40300082d1086040c85443c02c902a2110b0014085640304030980343c80181040c10350380031180d080030710140d0400450324908134a180c4a81402c4800c400000d881c0c007502d0b15240701440050307065007a9108200c0031001caa051240d086010a443c4250001d4012507000c40103079500c0324080010030040e120141c0200c213094003219810008030b0700c59a0741140f6011940c0700407000b085d156003d080c80301301c181c201810f40d1415001707000c0e4040380050310070f02e0074480c10151820a42260304121062052070b4450045998010307038595070b5409944050781202c0346400301c82c2003a9482c3d40c4c01d500c413500c1d2002541c047c03024100c100700340710152542c6607200c81c2c2120326903d03510707081d103001c1c4c8203042e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580265827 1250 580264577 580264583
    0x20f0d020d0804080c070e04030f0e0d020d17161109070903021c0501050c07050c150307050d0f060b0c060a06060c140a060e0706020d020c18100f2405120103 69
    0x842e2010505100d035400071600c80d600258140c90703034652035641c40d81042a0554088000a05034000098040d00c0b5103910750300404014004503080c66140c0030428004102c1c0d40c02c4e0b0300c40c20070301160000000740750014640c0120180010250318098246241001e081c03005090050391050200880c41d40c2c0194283c05586c4c0c1102e840c0e41c0085101070500faa003289020052447d81fa0005000c00c400d1301402412909209170201d60a4807400014800e040c038500c1025600a0b1007030011a68190050014195403060142c000498155005614068405c0740d400840c10307050000300385e4060b100610081d075000c01d41e01e600740101440c160f001030090f013403080058031507600324015440c445001d000d0744c900c13540c0108050101d081403442480d01c500c0c03940310b01c0300944910883c452290f40081509444280010010428250b03100d61080900400400d000840480c0da1008100704020041c4900500082d4520f0865480840c0c507100e0ba6802000d842c0b01400700038008000003080c4e120ba15410342e54 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580267077 1250 580265827 580265837
    0x5010b041a0705070303052502030c150c12030109050906010e010b1305090a050a05070306050d020f01170f010303090f12030c0503130b070c0b0c07090b0a030f1101020f0d020d 77
    0x400d0900003000b80500d0000a1260041e043c1c000141b680c451301a01c3c10b01c0b21020f040c1d24219142102903400c3d004020020b405800170411001c0c0c3d440e00030100b204200c0001d4440d0f140c03502c8021100e090078208504200c5d25440400140320250300d91044680c4410004000c1c00c2079414492a5814080d0510032800004000140302d015070f00b07105c07207550082c20003a042c0c1d030340d40c2000d4203100080e100407030b0100d044526140004503d94846e000d03082c1260000341c00401c07036080c81d400307022003051401080780c18003806100b07904401081002c041d04c00c06025209001c15415460014280d0358140d008108d8510042c80074007400d02d0140104801c41d40c5070411f00781401691a081e400d501854452591503400c0311000202038100701c00030000144100020842c2e2600c6039062100c9020b40c12121045607c0034105115400d034aa10040c1403880c004c0000c00f0480e569540c16a041740500003c44400c140d6201a200039601000b451082095903805854240708070a4029515046420b900c2e003000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580268327 1250 580267077 580267109
    0xc0b0715020313030212090a0306050a0608061618060905011d06040b04030506060d2a09091101020105072c0a050a0305011b03060819110904050d0905030105010b04 72
    0x30040404002108491840c2551039150034142d440b400780b41d44500754054004e452504511864840448040c018024818080d550543d00d03000700808009103c6101c0355592800402c1e544010010140300e054051465005a207180c080203150200c0e41c010f10b0714280d580d000621807660458044400d50f070081c40e11980c03038850158903c603903883e480c03542a008030300001c01140c1c0d1098140104181c0c1e020f8803c6500c036840e040184134001d0810b00c0302401c05040000c1d0042d16103080100b441441121415100e04035071120410011034082580448000e140341441d141103513020b0003180d1b80f03c0c126080a16284200790031010300100e4203800001c0141c5544461a507075554110903101502c005048500002e0700c901e080c40c0200207140c0c41586220200c28041e41e11882401000300303840030603001c0c001c0c42918820209400b07a007030710201c0d0900107035081500e55480b800071861166000700020040e4212101d0041c141e1062900003a009074140801803000c002200200c800b00c41006080034201c0c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580269577 1250 580268327 580268333
    0x322180b1f0e1002120301030303090c03050312060f0603070e091e130c0506040f030b0604020706150501030506030309090f0601050f07060b09010906150c140a0818030304030c0b07 79
    0x20a40320716054036072101800001ca0394552001c0300104801d8140c400c0d80b03500f404524140e0345c0ba0024648080b01ca0010001480040d1103600700720115446885486521038a075070300c207401c50b04001c080b016000c4000003003121030319010b0510f40c09a031007901c9107861030402c1d101c01892940680e04d8140240403a2001c28841102c0f042d04281e40b66980030340b03100a081030700420340c042d281c00c1016140c1e10488200440c06180600c200c03422110a044c0762429245180e40d807009026000b01a40e500541c24007413880419614020f240055204140300d0301c103d4101800501141d50140442d400f03035100b40f014032419151010840d0b0081400220b014960341c40500480b02403042002c0c0c6111424042003940c00c100700c0380c22403044c4600486400c910342e0780f9200b41c181151030300c2c4a40780700101e1600741c11400c1c038082c42c0c0d00d00c50075014449080394100005106031810300810421a414000040c03d07441d200360601d4118107038181203024502e01461a11410380858030341c015880d0140c2c0010f005020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580270827 1250 580269577 580269589
    0xc0804260c070605030a140c1903060b040b0c06150d0b060a05271f0b1e0a02030c0705120a021c0501091a090a0803071214090322180b 59
    0x100350030304210ba01203501c4440041590b001541c0305a0220304200c021010381d85030202041c41030318000300c01342c100280c0304242040c414044c110070b07041c1942c070100445c40300441c100030400341500c4441b881c3d44030340e442c0d10b03540303420401800f83c0001c2141081032500c039034a030002615003641101001c640b80e203c5600098052034180c1c03215030f20403001c0044180c5880c0c9034024180d0341002901c0643c0790399586986900d109410300e00e20034100c000d52010302220711280003515513110442e0040d40407002010400c10f41e07074402082c4402590000c124120200001c200c80005000300350380c440d00165a0000c560f90700c108a103002132050070700d00f4406410f40c00c164188031400390024000c0c01401c1d0242440c007880421410a6020b0050020024001703110001d60286955401607840345141c0d240102103d0561005081c14a85511070107660746050b02200c12a015074040800b8595400742150206400303182902d040c40c40074074600c000c00c076100500304186a121242c075004610b0380209000126 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580272077 1250 580270827 580270837
    0xe0717220804090c0c14030a0206071d0a090e0705060702060a110a06051608130b010905100504020408070806071112070206040902030415050a09020d120c05031206040c080426 77
    0xd1000c0c82c104d41c51394440c3d07021035903031180b9005144941031075021020041c2c0b2441a03514810260b441000401d4002d403040141c42c583d131641c08109205403091100041e105071a66004443d11912194401d419550504c0b100c001040221002c614102c001da022804500036661008140100c10140342d0750b9200512610028550140c8108205e24124103600220107000c980840014981d400060601800c5107110b5602c540001825440da03103050a2200038090007000203144101c010340024180d00c032400584050000c41002d0300c09035040c00103032890030f04020b007901d04001f002c20480002a0000c81c41c0040d444181c411240e544802d4004620b6510560b4021009544004100402d2000c00e007030708900c182d1451410300080d19030030580b8040d1540c142d000f03035000d91001c08000010303d0300310005c409840c030340c11304410074100758503150300716041201440d202c42059000c0041c68685485100360200c081d08140c459030809807110522091648402c02c401d00f41c0c440016400d203082d8082c1c2d8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580273327 1250 580272077 580272089
    0x90302070510030f0c03050106120c1b0f060c08040201210204030812060906040209030c01030203090f0109030c2a060c02030c0a08030a1706010f050708130e0717220804 74
    0x2802c040b101e0000200140b02001d03154a506103003400c107600f4103119010f214100c074250798900401c150100100c10041109020a205204038802038020b242446a4942d807460301079030840342e902109090050544910310304060403c0b110400b0000140c5c5c01501161207010a13910285e10400400c2d035030030091040c0d820280c1004004612016002c14440e0072610840040c1c3d100d0078039881e680c09010a9000c0c083e03070f040d85900070803407800d03195201e079015590102d515821902580c40790340b501c0742158040d500036000520304455140078014540f10b1501c0c00c0ca95011016100010740d00b07003113031007109070194004002540d0706090565404200e41010b189004200307010855450205030f0340c1e40d01042c199004900c2402003a03e120781000149481501d046c3c40d4144050304004049945910882003100c03409400e10000380380300554860703a8040c4c1401c40120781c242c244884054419104419001c10f41c9080c081005181220108180b41c4c0d18680d03461211056080c0c07500b00c0740343c042c0307401c90 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580274577 1250 580273327 580273339
    0xa081003150e0d030605030c06070314030c040302151222020415080f030915130e09010504111905060d0e2505090708040b0a0b0303070f0302010c090e01090903020705 73
    0x35007210380c00307510884103441003208035420400c2e408000e030207030b070103d228042c2c2c1078014078400d2810b81013120080005910900c1c10300312049003184490519081a0745000c240d002c08513042c811410030602030030710440c112100d01e003003140c1c0310040746141000a090b03110721110104600100e442003510b009901d68000c20070b110a200e1203811044040b61031003203031218801d42c8400d0004500210840e106040f0182c115850000c41900380c40b090b9109000090f1642c4c0032a00001d545442c2d801202d0186038442c0000c94517007090309201214030b44d65546c06120b2083c48200011440041d01c07800102c0c0e0042c1c40d00d40d1035218402c4524003e2a0b000001070840c02400300f0025a00264050400f155640110705144140c0320000c0c0b001c001012076001c0d000c100f01c0c001040120780c1020009138440341545012a040543e100420f003990009201180c134154105002d408150b0280600d0301c540c00b1034a403054800e46001981111614184500540b10382e80c4d849030400d00d4801d0060902400d009009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580275827 1250 580274577 580274603
    0xe240a030609050c03060705040e010b03090f15060405060603011d04021518100f020d030506030316061a03010519051306090c0306050a02040605030c130e0117060a0509030a081003 79
    0x102d91280c85040d8580e05c00e0040750005030920b80158246c6080e00e08036071030340c400fa81c20131142d00a154805003e020b20f500c181400e41c2c9007801c2c10404074070b245501036030481440c10b01009100594001402551181005100600124050010084042c2103020400103203890700c1c0086102110070b0510b07a5001600003403d58200c40c401d80c43c20300070550a603141c00d110010400d080301c1c000944000d107401030704040d55500b0810311940050307030170030700090581c3d2030001c07519800100000046001c503400b42d00c41d2005080b03d211a2002000f00710190002e10051030596054003840e803280d0040d6000b00d541e54082440803001504000a96038400c00070040304115045c0460940c07039520046136003e0030000015000d800707a009950440300e0544400341980c449000001242e000307841d400b114a205400c000941010081026000340f140c041035440342c1619481c2c10741080402061691041d0401060000700c640003c00c41d0202007003458441100e484519078440d80040315800a8080006409 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580277077 1250 580275827 580275833
    0x1207090e1f0503011404020909391807030c03090804030f020312120c03181203091902030c01030e03040b03040308060f0102150106030f0e0709020d060e240a030609 72
    0x12106001d1500154049666600d408040c00d035851080e202d04a0700c091008500181005911983c100504030700351000d60036040480072075948520f000c001e004140800401060725a02e19403081400d042e9050081d501c921101c02c4060300024140c2c00405960300c6d1400440c82c4698030108095030f000000720760741e55903410700300348c0c01040702d100b644240551510090003a20030012188020208052041d8560b1041c250301070340d4000070404c9409824200c034500410310184501000b1000c0d48080380e44031300700031001610b84141c2c02c55604542411445110141c0d40000705122103030381c2480e0100342009503540c920300354007556114100f9294040144820140c2000401d407040000703584071090346859000490391030340008400940384250200603c5040d00c04d0f088030500c001c0c91440850315802245526180c407000341e00052052364041044400468140564001000005540c1081c0d0520300a450788130242c2100d09449040f803003c100305251912103c4600654004070100700c90078042c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580278327 1250 580277077 580277101
    0x14130f0b040905070503130b0a090b0711060a060303091806031a0403030b0405041e03020708070303080a0509070501120b030a0209040b0a060905270c0909030c0c0105030c1207090e 79
    0xc0a100709480c10000044c1d12079204400796803207210042c121090034402030f2940c0f241180060200001c2c9911440040c001c5520b1100035401070f219642c0d9400c0701d070300301c1001134107182d000307400382c4079040c1031010030000b113a404039041040da48001c450b400c01a0340b00c2002c6005101e0b41e40700809107491031500420140d1151038080c41140a0385080c81526402c1040104a64080310300400e0300f1681100b602c040f0307088610b02d00c030082c800c3c0100c0740c10640f110303035052814610307a104900180030030007005a0800240901600840290000c0180d50708000010b4440e040b218808070306c0641c0c0307000640c90b6940030040700502c2900030380419094145428612844d400441c3c4104c98603041c0038000401c2140d46c406e09115401a03400d40203c4c12490b038060a0340540d0100040e5a4491004d0345181681c4600d9501c0c000c01c0904002c607568650780d5a8a03040101110000c2d06001c400c1c020851031440f030800703c0702c0040904d070711714840b641c0c4c44c0800d654080042d0806401d0201500810410005d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580279577 1250 580278327 580278329
    0x6030b07030e0a0305030106080402040603140307020f06040303080402091003060c0309230613150606021c0201060501050307050a110a0309060e031207021909050a06050a050d0314130f0b04 83
    0x3541e000c0c02401003600c1241c2e0345201003031000303000444c2040100300706d920403504250010300c020400304016070f0303a898880f110701d507100e507042664000003451011803810b11411172503501c05885c003e0030309140d910b01400c8004000e0000e4001c86031280003a04803d260b400e071401440e0700030400c020041ca2010020001c100d4400708a96110800b02c00600f00c0040d2810003c02078a8000141910b50358245503022000050108039010060f42d0000340d980d0703000c2d00418000e081e259000f0400e5440c1240003495409260001d2020759243c101c1c14422640c3c800d044a83c811a1802c0a80d600c01918004807040c20800c06842414014282d0000800d54051601d01c03c42d0500d0f56030900b003800d581c041540b0360b00990100700b5121030400c11b0b180103080003070a1442881c188948880641d0742c58409905841d4121250010f00c0e60b0b85c08280854a4210515000b4000a1b038502c04088002d540c090a9984107054a401003100440e5502850311100c0311203020f004604000e42034943e8038404c1400c15000b07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 580280827 1250 580279577 580279591
    0xc010219080903030405060a0f0902091501090b12010306020304030c1202070302210a0f060b10080f07080c030f0a060f0f1a0304050703151808090f010e180c090406030b 74
    0x401d0000c52508180001502e0240b43c000e40503200b1500c17512004002001650b180c540010380301d0404801682e10b21041500c299940b5100c4284211514001010f204264201019154050060829413400c02c80202e0640b0342c0941c0041e40c86d12a810143c07021411224000d18071020b1501c840c81c0070f0b1340490001c044910981e01c1c060203021480c0d4001c410342c2c664030401410740c0135014040101d0a215026410a030003031340c0024030b41000b840030900e094122003490780450408014070940c6aa00000a54070a04031700e868042030400c100f244506103c00b0b85000740000354040071501000b241e500910090040e04402d05c0c41c55513444aa0b089002035110710315900e030105034054030245034801100d105582c810060710159082d0b0360380001c40b20082111900c10b665a010400b100d821203070000003590f0007485040d89507002c0908110a021800c84100c0c100f10480f026070030b40f070300c41d200100c91a841c06c41c41c00300c1d00c0c2c0d1504981d80c03190150204480c1c2c4130b400e1110004c24480c0d603101d0a030240b03903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 580282077 1250 580280827 580280837
    0x11060f0d11090f060d090501022a0d0504140f221409061f080610031b050a1814040305130f030209150415081b0a0f05040c050c010219 59
    0x1895092405240c060000d01c1038011803103040300b02d100d04e8000d00030490043c450b071002a000c20552102802ca030000f40022158070141081d038103203004d50384244004d0011400c010b0140242400000305140030303610031187c0b02c5480042c0b0303280c40d40e41c42240032003031100030304078100341d0040924a156204212010115251408201131002170250444a00c0f8125000051249486c1ca030036010700e40b004005581030f1043c1c0480041070f1060b080c0304090089581001000c2c0160560070403100350510064203500d00c1c1d90900c001c11003916503045a000b2134030701c800c02c0e500b100d000784008006481d213240c6218100c00e4407002c200070140c00402800514161035242281350b0b454502d0401030320580d010280d40094140c0000d00c2ca00a040954040d41001400102e150104108100410314580d0000e00050700310008820004e03a8080300b040c9078400c02c4400d44210703854404001d40100c03550141d5805640c0390780668102c41e0280085902d8420440000c56130b40984030340000042c1e48001808001a03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 580283327 1250 580282077 580282091
    0x150106230307210b030610140603060f01140d060f1a0306010c110f04020f0711030304080303040f11030d08041205090d1b0506040f08060a2c120703110d03060b04060c11060f0d 77
    0x10402740140c2e0b208100141c1500c00420260005480071700f02c407444d041c40108200644104285940500f000505581402c845218201104507000e0091441042c156031400d104200e00c90f030f401000000c009412011001c142207452003c905002c4030000050341140c000144086000c00307120003410140d02400144218070312500425849201e54420012035038428408030700400c0d0305066400c9024401c901c0c04c950804090017003401c207211000d5072000b1541d200c08110500450061316071032543c45240c0507140504000c00a0b492502640000e80072041e80c0200c0221504d101a090340a410011f000c02d8a80e66501c00344032420740c40c0d0160004038040c100c04515034880d6401052007014500d1110700d91021140410b5200d81090318401c80a41f041d1103851044440103002080098042d50f509201848100740362031500010310900700826103088402c0095a901505503400c2c0c0f407403131812040c462181e060040e0308587c104038a82d440040010040011080380f4000c202400d1b82840c14451a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 580284577 1250 580283327 580283329
    0x2901080403050304170403120f081602030d1e091203060801021c09030c1407080f060c0f0d020403051e100b1c020102150106230307210b03061014 64
    0x806800e460040c049030051000c00c000a8041c00f005210101000c1c1035410243da03500d07a2000d001c104a000c0b0701181510304d075138912590003140241c2c410720140704400724280945d40207650b442208102e5000035550230200c44446c00710500001e020403d50810311034800e86050540c9800c21800e01240400d107416400100c2c80d8040c006d440907204010b0101000c2c5401071000300141c2075600044040200501210000815100040482c21561001810880d05015116240c0300021000c4c2c6060b520060400030000606d80032100c004050814054841d949159064040e0242d500010254081c6503624142d41800d50403045c00418141d003200d0440d2006104401164841c5005680050b440e241200301900c3c6d00401c1489940f0601c1115810403240c600c040000768280c124000103200b800c0c1c00030f0752003142100702c440b9519409001e03245061645001e030481c1c0c00d6410560040d03191042425442200d0f80c407980c00044058151034451808003101e1080310401d000d500510300496050b810710b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 580285827 1250 580284577 580284587
    0x601020f1606140d140a06050d02060702010309021c05010f2906031b0d050703050601051309050c041e1502070506030c0d060314030301060f030207050d0e030708012901 74
    0x4600224110008070300d0030a034003241c4442e203d00c040e0259840c1003000242e0300c0d40c544070b80081c2c5240700c0e00d9201181010300e07191050380d0060744070341d110742c622400003c00350340d90104996030107074242000100c0070414808540001440c110076144c004201c0d040609002042d00070740c000356680b41c4100700081600d80868034085078442074250301c0010000c248101c1c00c02c9801941c000d411000d03c0260014400c0c1403000369070010350300302d40f0030b51604c003409604c2d6014040d0304c0d0400c0b42401c0c03550030a0300c1c001405107429000d12500000c42d460380007284144042c8030869014007806030440f607040340b00e82016240124148990b0100400701203207071850902c003040c007500f6110010030705451030304c944000c0b03901a000900506040d581c0c0d0341002000a020042000c4020b5581340555100c2d0316200015204862050842041c18010040300e00010780c0412003078050216801c2c003201e42151140428508400c2d43c101c0b20f10303507180128002612040c0c0c504032200301042c0114140c107080070001120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 580287077 1250 580285827 580285843
    0x30106170c040f0b0a031104060b031b0f27091005060708092803290a0c021c02010e0c150f03040809090f010e1003050705040c0302040e010e0601020f 66
    0x403403500180c00d0440c092038a90809490740c0c0503181d011400c2c024000014618000940c022182100001ca0645482c02d0900681000b0401129060700350310344080419540010380318802800d43e80028003040c10041201541c22114600c0c14040301c0f43c107071030b013104007007190541e0591145281c103000901c9040c12010300d400752980038181500784402d95448001070340006c110150320000c80e100c21950410f0040c500c0c00200a81c010070140c0d03d203542413603140389988004a80000d0320304840503602420740508030750003080c000d50001d40941c19080483c00c0ca030784883c22040d48180501c402c00051390540121800404480a03114000384140400c04003c90448103140d0f882001d100c88808a00480065036100d4050030080d803404400f04c0024480840480e140c5803840c426400500c00707000c0c4904082ea1060043d121003e506e420358850543d00c03041c0c0d01c80c0394421030300c03601d0300c500b400d221350140da00802041055580558407078950b0120a41d0869841d80144034452541c0c44403540019041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 580288327 1250 580287077 580287119
    0x315040201020c011d030f031b060c07030507031205090709180b1b1b03041703070b150120010c020c0102212a07030203070b0a09050402210103030509030106 69
    0x20030f00e00022401502c000b00c0d1100744211100070240e000c0381d0740d241030104118a18800c07000d50340e140c403454440c00040320a54103611090b0710401c01c00000711b00c20412102c00039010301302940c5030300452504895040c80010581da40328240400d1008030f2000044910a03241108400d00c2008004500002542c281c030300701902001d03405002c1b4111154255a1040c0e450340409a580b0303005058101012044602d0b20441c1e0507400000d04003c5119422601c0d80e42a2284016610b07103615501d418100c4400a40000300c0d0040364848a1540d80c0070b103410b000e004442610311101c1c034110384051802050724032500400360281240c0307440f00b90705c041400035030700300004810f040708000d14103c1041034201200d010f042c10880e102c1e4014101160050421a08064004101080c1140f040c1824102c4aa00801e00200b080c07060900c0070383c00c1000c090a40f58241c8005885041c060440413248510780d070300e40e4002510200201c141035105000b043e10a405400900440c1d40e43d2400140400710107400d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 580289577 1250 580288327 580288333
    0x6011a03010306020309121b0c010f02030711030c12010915020c0613080d06080d140f1c0b120d18061d010309051609060b04150c0c2102031504020102 66
    0x10b2000400503400783d0b41010070303101224400000c5c03141d042e44a9010f50784a0005602c0c010554941c0c150422403c00d040340203292044020400d002c0c06980c03030089010040c501d02042410034003070b8808102c03408010b2401082081401e40d00102c0c1c07402084c0c0030381c041d00e60036100102c00d0000409030089940c0c02400c40002c20035a514048032450120455a0480303999a04104034840b0f50080d005841c003802c2c203e40903003a041411035000c0c0c4581a21130322240541020300c00107019036500760950f00311400301d0902e14950320b1010b00c0900100400ca110b41da00c83e038072403101c001074140040c2565914420340c451068402c0c171040d03036030301b0020706200d1800054401944201e00040e0503489605030302042c1000f1808424607500e840c2480101c0720b10401680d5501ca0070052002d940c0120802400340034102450541080c0e5003a2017482a600c0010911603500b40c45000c014400741560000c003041c0f520300310081080642003488404031070080c0c0c4244280b0b10410a00d540b00442d40b1f000d103a0580003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 580290827 1250 580289577 580289579
    0x50f06100306110304020a1e0e010b0a0206150f01030e150106030203070f02070509070509040213060f0e0d1115130806010302040b040c0e120f07090c1704030806090408040918030206011a0301 84
    0x234180100c500100007054984030003000156005d1442c1c1a5001e04071440c815500c41c0c80b2480001e26003007009219250049690a001500d40c842480c403594000f800e01c0d001c103003101884200c5280c0420102c015500501c030000000d860355255010398082c1a4981c2c03090031022107004105c1e40d4880601409a02c41c41000118013042e004400030460850b0242026090100d10001440384c6802c40d8054004543c09040c458800d591040c0703003001085007241e40c0348400c0b1081c1c4600b04002c2954942a0240c4410800d201c002810300017036640080a039803503074031401d07281c14403603031030344820312049004d18104455540545800c0c060201c500703040c0c2c1d1300c1c85110503816040156040c680c24500c02680595252803001c4841845030030301601c1da130400412240040c16004101c00308080d02c1d41c8402813a0350a00c03000a52150680d60840c0084403610003030344950078244194071641e80440041407a006100d83d08001c46401301000e14042c4e002d5411907a40ea00c00b8050004c42c1d040101200d03d82000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 580292077 1250 580290827 580290839
    0x90f0f03040b13080a0506060103061a0f070203150a150909150c050c0106091505150304060c020c1f09090203010f09020c01060812121b030a0504050f06100306110304020a 75
    0x40d24a50741c0d41402d83c0c0520395101c00c01414000d40c80c500380c0c4e040e000300381008469600b502a55008101c003d00e81d00710301c0090641480e080c0510980c200c1c9542c0c0c0015002c00350350b4204454174040404168489450a003080400300400303003040d0030729181800b0100000c00c640c85218030110b0b107410514624442c10501030803402424200c1c004410721a0901009040c80d1b024852803015001c903107800101d0403c002c2c0020003040b0b0310391109108a90006540314502014800d40c0e03000f41d8803800215000420720000c0c0d040075003503088940c0203c3d2070081400640c1c0941c00d1a41111043d88580c041c054880d04020184c1c4008d014071070019503480c004010f4a42d0039070003030070b20105800c00096026283c4402e1400c0040074510404ca2450120710620000040340c00b194108402017904858110b556640d581213010081041d96039507686c40002e010304c1402d0004c48a5400340c2d0b41038078402e25054410a004800711700050307407020f2810ba8000d0400c10440104c1e40200e0300100006400303440e00e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 580293327 1250 580292077 580292099
    0x50c03010e04150e0d020105010504020703090501080711010c080103110f011b02060c010f0b100302040f0e22060e190804030b07170106020d1e0c020f15070803090f0f0304 75
    0x54011620042c0500080080c0000c134072900c10f141c82c480740601000c00710311400900b03441c4183c01a03441107104010000c0001e412103074050840c0c6080c2898400d42d07030380e1030094801d00c0c0b8030b4100301c80d15401d0001508405901c1080300381600d10071071034000747d081440e0502c0020803d203900700f408161401c600d284600029824038203260300c020103907498030000e68155400e4810b0b0544d01c1c00340c692602903a031110314003940702140c1c5200a03d0118245840d05821100340d070054491101070002c0c210200d4240300610903001c440120241980705648c08614100c40202200071085403140603207070030141d8112490305401c02c907a81201030700341010f007140c0300c000c44d1440180c0928240b05071072120380c040419020201e402000b07640c0103041d8070768580c1005003c4504c51521340c016032088a2910344080e0300034040f00b401e00d4066411415070401900442d5540c3c429604c01100074202092110402c90f001c001548912280c0066800e0700140d1410b8030f66a50381400c1903681c0390028402449118070803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 580294577 1250 580293327 580293331
    0x3030614090c0f0c07170606010f020c2b03080a0e0d0512090705030607180e190f020d020d0506031603030804080901090b0f0a090e0108070306021c2904050c03010e 72
    0x1440343da8907041d1141d404900d81030440c0e015031446460580915014081404100d504c42c400382030050200030340000007911000e000d1030b81886032490349540e00700c084041c07100390b04414400115012130052400d01a204190841c1c0300581c50317041045500007660040b80c1142c1500080d03e8050030049414819076000300000c200610512171a040010303540e0781007110502607065902d0b0300042c84034129000c0300c00c0e20b00360030032548034158109220060100c00c0c01d4240280d84288001707500c000d030a5002e40a442840c03402d0070701c20f0010070450340e209403650106002e40c204608485040982e080d255180c0b00705880b018004c00d10000c002800b0416002c010040002c05151506895480703202c140c0c0d480d00304c40303001c0d1080c5101042c04540150000b00f420090102d89207880055850940b4542da940601c3c0001803080c0d0b00131660742e2541104007140f550800410300300348041c03c014202d03501401c40b084036552641024006030400d90519124190103140314004140c516800d14012403190200 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 580295827 1250 580294577 580294597
    0x60a0204061218080304081c090309053003130f030f08031e0a0c0e0a03020f060d11211005130509030d05160e06090a060f0c050f070303030614090c 65
    0x43c0d01e4084000440d070354000c52240d0310900c2069250001c18011090f00045114009029460b00300e100010980081414040390812a02c01c0305005807100840b030824205201002c4424441a00101010001c8090181d00198402d50a1682c3c0c0e140258020a40544009020600400180030205e000c074001903034072030100c042c202c2c45c1d040b07880d1014640300c0f805c81c2e1500c0070564600c0c40c110310690140160280f100701300c441600f004c0c1941c0014408002d101082803050400040d01c40c49001c440c0c200e405c207000904803054540c0d04c0038001c20030907010b024203030b16442c80e0f11000074030003040c000c1c4020039148040c055441002d01c56400000501c005042c00310b00e48414010880342c4044d07030040b103100f00c00c0c8001000c4a50b0042c44060505c0120480c11481904103005802c4203450b0b804c1c09400301c48840c41c041d02640c03801201903541000780e11019040340503018103001c2107040007e01744c0440b032190fa420000e441d0b43e0404800f0444032083c285030f00c4410800071540c0c07600320001410700030007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 580297077 1250 580295827 580295861
    0x30703090c17030702040e061e06040f06030503040501090f060e0411160f020f01020c0d08090f09070203070507050603060619020106090e06090f030a05042702041403060a02040612 79
    0x7854074070b80b040080d50480b400500d640000f0311001181070902036411102c007c0710052110b070400c0f0301c0c68481c07080312402c0c402c0500031a07000140380d550380350480b03900c2060b008820031400e80c403030401d981c403a44a4002c0902081080c480010182c1c0e030402c0c545c003210f01590b12410303480188030411018160b210301051629030180a1074610a0804022162141c480c01a8450510b500d00c148694200150003082c1990041005103550340c0b9402e080c1d01d032441d800020540e888503203500084c03000c4940c00110380c000c800c6004211610390000000c00429000d0f508030f8070110343d2070301001403030302c0111006a042601071169200003280810b2348110706209000110781c8544500000040341c0c041d043e003026550117002400b1240606211100451501402461401d561648003034000d11a5200300740800c00381d14182071240e640d8007068442d60399440402e660303a0f65504020070b0300c88010442e15100740101d00c00b04550b07400b14401c403001c86441d600d404407203050b513005034001040c100a0400c0000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 580298327 1250 580297077 580297079
    0x9060b120d05090a03080c010f0617030a0c292212050a0e1c1502070c030f0303061a03090c0a0602100c0c120903170909010e0604090f05010b0f04050c030703090c 71
    0x50120809030040c018040d0000501084020308070303054440ca0303800050507000e9180060410b0bc804000c07507161403020b041c400862030540c90041054011101c40c08100044c5001b800c940142d00c0790007078016100051040c540c0e5852500d1040365400ca120024000c0900d980f40e01061805039020344048003e904004400350348010204510741c040e01c1c01c1d40d01440c510682d00c0104800c0000a00c01400441c804604000302d6035102801900c0502001d010401c171410782004251007a000362000d0429840d211140c108aa0b074024081d400583e0320a446005486800d0b401c1c0c1030900b0300b80300b214881d50061060b1000e0055001c0100000d92004080009441b0b0590104c1c064016003c1d41021750756482070007a185046c03a400e040c0b802804484000130800100c5040e5540041301815204241c4420165440f03c4000400611034514020080810103c4540902c1410b40c44042028000c0d0340e590b0719401480100001c4500271101e1000041092011079480c51080d071001c0c46452140002540c2a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 580299577 1250 580298327 580298333
    0x2040e01060b0d1103010e0a02220608011401050c0d0302180a03051b0a060507030f0302092e0c030818030c100519020909060d02040b10020109060b120d05090a03 71
    0x750304207030007a4908500005100f00091030b1849200c10010303c900c03101e070135941016194240404003901601d21640c011501c00c0301003682a4032240c00010121585010942d00c08014209071024468440c1d501d101740c40011942d40100203c0e07001914042c00f401c1d4281341004107800075044030051044100380740c081034119480e1041e44030050760040000b4001e06072894800300710b8121030700c1080e0060a25000030000c0725040b03400c0e50603040c4e05042900c081401c0403812402401034111f079907440f901d071202e002e00409000d507540003031001518003132000e82103e010948212041080080010b540040051101030802c000c0003091590202943e00d400440d280c1c0034a010820890b40040d10b569500380100c00c04441c400718600315101c01c0a500708881e001c0040c11107a00202218060820104102e04543c2e03168004100e900c4000d0008203401c24003003000b03000381618081242e00d580b40108550f2146800d0354184070340c00204005042d540c650147c100c49542100e580d00c1e8104c8100b030004400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 580300827 1250 580299577 580299581
    0x50a09020301064406030609010c0207030609050c0d03050d0b030610093b071409040318180905071d0402060a0309020303070b061314070c1104020408010c1d01021902040e01 76
    0x300013400c0c6030000500300311041508003003000c0c0540f0381c1d5a1509103180c08150300032a42908403908030b5400164030380ca6040107820070108075011580b25928110443c01c0681200240c820140482420070080303008c00103056079148241c4246100004a8004104140b082d401040d01c408482e01e0b0190078a040d8160340e4003c00b404420b0703201d01541c508039050314040410401000b80702c5104001c5aa80e580000300b2001980580068208800c10082540d9084036000b944024000c59004103180d1001d88200300003080100c104660303d01400c0800580319032a071410f4502c00b0740d02404100305450b240d0030081a07910064206c070501d51564110b4000da40c090024050440c05540c5190f11232070074204010b00044030365511101245411790180500180004d07065000081e800c0c0f003102030426003080407020032800700c0d0310b82c02400020041098603040d0811402080030b81c41d1100050350b03040420b6400003026100c1401640003002e82c0000c82d42641c103480c003060025000241e024052180345007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 580302077 1250 580300827 580300937
    0x60d031209030e12060118020c01140709080111030108121e071b0e0702060106140409021c27030e0f040507020c0306070903030206011502031210050a0902030106 71
    0x102143c1206004507250500c0702038a0700a0758940082c20096050003104207003007841c40910108103a003ca10401c0318a000d6008a90780c4544c0140f01c402840d03c084028003200c120300844903554201304140d03005800800680c0d050341d0030fa03400b800c4210b54040d983d520b10780064035442a8045940c2c14110480b40d620020100c0600910300848800103100980c0e603043c41650000301c29a00c1c010401414131744c04241139044d98a1413808800c1249020301c024524001c43e0045400180300151042000111920070800910701c51070030311080c0400380d500c5400c45c402082d80329030301e40328002e07a100081c03045c5020302c800c6030001d00141250b000f03003002c242254002ca4162015038030926921103103180811159501000c01d10703109910f14110303138000391103507018891814070281e1403d810350094000c0c010b4544007403208120561038a070810002c00e035110648141e60056641c10130220780e9050078002c690613620581c81740d90030802d80781d0f42d04400400003070400e000b04070003c001e65442000b600100ba = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 580303327 1250 580302077 580302083
    0x60a090b03011e0e06220605130b04050705130e22080703030f050c0a050c030f16110103050c1b0c0913060e0105280207061803030e15060d031209 64
    0x9481800d880f0480c0402000b01c0c1c111525014801c0104050fa55540202d21011204141d000402032007002142000d0441600902e602503403500f950306a6465a61140042c580103c0e0140a5500d510f80700395030307d12807143d0311080c404043c0e4007885280300b0082165005140d5024003200754000300e01401c8040000a8116000e1500044075004c0c16850f0040a20020100c0c50030080390034034030301011003441036181ea00d090100104240040400030f1051f1503030240c44107070b215902c1c1038000d9494190504400c007101ca182100f40001d11952013480381c0ca00c90400001c0c00c034036080d031180102655031420322070790701c0c288142c060440a50b01c840e100540503400100d01e42412001a20b0300000303a440c0c92041420b01d86c9420208120044200301160302040c00109900320b40711510560b1020b0700c07441e500505024240030303400702e00400501045000c00c2c002e82d41000040c0124103c5900c45008201801045010401040152031f00c080e620754420b200b030400741001c0c0c0709000d0810036180c0c281425 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 580304577 1250 580303327 580303349
    0xc0314040306091b05010f18210201080c07050c0d1112060702210304030c02180114090903120403110304090501080606010e010c0305030a0504020d1a0a230105060a090b0301 76
    0x50302c20000e04d07062030380c1c05010b002c1d03030954414100f0000903c09151200300004005030f107404444481400c8080b00094140100100503080303800c50741802c16403081c48104c1c00036411800107400c003000074050f6030940d40e03c8000381007413044400c00c00020703035031421055802100320341104d445a80d80c1044000c0c2d11031084041c0c011031401e5840681420003c40c1c101c503040200c107448082551034641244e034003640c1401e0001800e03180e400492290703000e014520802080381000400c2c94a42c0c01318006682c0800c5802500503038628130310726181d000b80300707100800340e1071140410002401648903e00102d5084107c82c20140da400038502914801e900214040c0c00c444280701c00ca50b400b14000c16580803c0c240b401d81400280c0e0001c0461000030203600c0d5569485020030115950b40e880301d807070b0301d4200c00b003040d03581e0300d040041c00d46007003d540ba44103e611300603200c98000d000e400c4c1c181800b00082c0940240368604070500c24107500c2491002c041180714100495984500d40203540a0a0903080c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 580305827 1250 580304577 580304591
    0x904020d0e0f1905100c110f0102120c0f0928120c050406060801061b0f030e0f1f0503040212060f01080f0318040b0103111c0614100c0314040306 64
    0x2102e0304200701001c02d0140e44104020281c0407400001e0300b0721242c5450200000e1690308071004071020b500704010b41207580165546030b480b40c1c105401400c120700007000c4c1014180c03124449181d40f40b02e120401455034034140880701c454900100d03045240c42e00c0d05400d21544419280014001d2240c0c0c121041c501c010041c2401880310340d8241070040d10050750108240e606000c0042d1800b841403003050308105180e0200d404640001071a284801d6100d4000031400d0014030b00034000070300142c0840d001d070700c44c07103a8804a403820540d20b584603440b0211050042e0748803c0e040320981d00c0100309070b070490b64584829981c4402000341c40d2180040142c240000c5d41846419418036191100c000510b81c820300034480d0703000009200100068003154005a802c4003074005a002c4c0020607542c184590000c40d1001441c4044481c502c034041450004008403034841fa10344607001281030b0400d810010a04400c1840d601404c10a5811800383c00d00c05004100820000c0071684940c1049907401d880d420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 580307077 1250 580305827 580305853
    0x130e120d020424090e0c090301050f0106110703031e090f0306020702090f01030b0c070201260a0f0504080a03091502032715040201050f04050319140307080403080904020d0e 76
    0x780d0310400c43c2c80303103404000b41907101e0010008030140c015600c101102002184407003130501c0480c0c2ca0200040e001b0300c124a03201003480c0509109204800110300f490b08414144032001c1440001da0303a0542380d1003101c100c0030481e403403110b6004400303806108008001041c12044450301000031441800c0c0907039102d000c0c4c41171002c00403001e403c03891500c40500040c0000384070070354059400381c0419503543e12500a400101d410ba841508000404007a00c0c19014080f0701030f103581407282900c0c07031050140b445020090b50440d05c0440c0e025002d40018070150080c18844e030065546031740a422218038070354028a070041268016102c9940c40440702c681d030102602070901034002c0c0b92900303026004030400344031000028040240b000741040400100d0b01c4c0e23440e094406440c0580301c0501107600070340b005000c00404610030b0006499640400c010040e1980d8000f0449801d15403194141c0c0c107043c41c0d5621444241c11542c1010350098082c418688051142c4c4203840150550b0402001c900d1000b030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 580308327 1250 580307077 580307099
    0x506060c1e070506191218060b0a080a0c05040903050c031801090e15090711194209061a0f030118030810030b010608010806010509010302130e120d0204 67
    0xe0f00060003041c0030b01c004080301c00c20422241001c2042d040100004403584207601c000c00c1420111758180341e10940392401e00002d64007010000314203440c107600b141e4882e118540d4800070342c00f0080519003984c00500003420302c0d8000e4498140f081c208203003014111103945045801c0340b046412980210000c0f082190f9106003208001c0401c0044000039060441503d52000800ca8507980107070900030101e00000d2240d10800c0040c0d840b0020f5596180690b2810701d00002900e0741590840034261101c505007029084140c6802d8154403e0010340091400484d100c545110089000c142d5400400700807402c1405645900c0410078017800103540020700700301c4488281402c4034001e82c503008034446101181140d2506c45c6416082400c525a203594030f9400e42d2100da040101b040b05003500010f0040c1c1c00c142c0d01410f03039a2600540b48681c1e00c65050150f122800d01c4044e50003088689244140c806562007902c0303070a011002d403210301c441c2c1c521002c51640448140100706a001070100002c0c0030007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 580309577 1250 580308327 580308329
    0x10b03240a0b070201120609020d1d060112030c1203050619140f03070b04080f0f01050603030d0903020f0a030e010905090f0103020f0328140f100506060c1e07 70
    0x8415084030110201041c6810341034082c816900c0000503024007560f015010501085404900a201d850b4860b1a041d000c0d4002601a0b0f10380e504003880c55010320721641e04100030801001c002c2c2001ea280065100381c020107900c1c181c0500a01700540c002003003040c0b1100310780c00e01d0b503100442c0c035041000c1030000304d90452008111000d000c86040c8120348100000c0c3c14682401c40322416141c0d0b02900003810003107180d00c030a03ca0360000500184045020035810b101121000039610000402c06503a0700b80c600840e001c6900d80c000704406006120b00e03034020001e5500a01c1107500c003088505805241002c2010241c010600641084295680c0508414003400068801c9100c2d1306185a04041070501800024841c3c907460b0300348801504c041100c04031171030368046210f1103002d47c10040e107161110b0034070980b00f14514403540c000c0700703800188013892402c0340700043c2403100c1020605d030014000078118945c0b07c0300821600d03076044000c01c4000c80764080c4050000c0884c0b0b50218203442e00707204d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 580310827 1250 580309577 580309621
    0x403030b060d050a1e092a05030304031a010e0103080301180b12070e01060e061605010b090103061a0103050705070b041103030c1606030603030207150201110313020f030f10180803010b03 82
    0x340070380303400098004d5492100301e1087d1002d0300798010200c3c69032046400c680d001203401d4800418000300b07201000022001a000c0040020450f0740c07508016160f072102404041c0060008000400485000041c0d1030341111044c1000909070301c00340700184c00c0d66034540060000ea0700440f800e01400b640c1c1c224407801803da034200040984502004200d850041c038417014010210350b04550280442900030130184030004201c25000d41e180d01c0d00703100401114840c03004401c1404120b10725540a841100e000e41000c1d102e85080c004550360304154800c000380101c5060310050f5060030191030400c090140010401c0240035040c07000d050002d42c00c403039540038408043c02c0003804c01c082500440d2507001e03038815603029040044100f405074050100c034001a40380001c000304000aa41c400e80d4004203041c400c840f480c50340d0411000701662000e030210600c089420440c00c1c2d40130400c055200c1401c904074440054000c00311070b2600790701c039002644900600302d000420011140c80050a0002c0f0b518 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 580312077 1250 580310827 580310831
    0xc050904080c0c01050c0706050306060c0d02030304030f0c0209060d14030309010902040e0c06090909030c0703140607030504030815180703020a02150405030d050c0706060303050c0706050705060403030b060d050a1e 94
    0x1d542d1b14059071018a4481d10f014003134000086441c41d2201c00441d146030319001e046800c061403141000395258000c482c140c000904c2c500c4030034a05481444010700d003540040180660342c8a800030008101c40c2c80204170b41a440303240300e4455a0b24148040c0d446141010b0000480d0b258500500c019195050a0184940c014440c01159641c919081d5240c0d01c0f02524400d91607510202d00c1c610b1841540350703c10070352007000300000800030b01c82002c1564a0050040d100f10b43c44003034040d41551419180280491500b00010711001c24003200c010b11100020040c070a901001640328290001c2a6280d03030002c0e0300001c07001601501040310303419134406910111007520309a2100c03034403030040503156a01341d916000851403c804110035503109a0708201c0030030100c1c4e0fa03490061302592103180145400c0c003480c0000a501030092055454250700103002d040c0035500d9031360440040501c40c921a81c80759080c88560100d0b581407042d28420a0307100c00015642841c01d41c0b44640d50b41035604d00003924 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 580313327 1250 580312077 580312087
    0x501090807150e1c0c0f15120e03040b1c050c070503120421090906060302040807121704150806100c20060d1d0c03030a0c0c050904080c0c0105 63
    0x190440e482e800c0304107054038007101d0354400c5400045a8842c3d41d40140d8212800d410b0000a202140001104407111a200031075201c0e40c8400750f420315888281864049000d80d60954000c01880d000b07035108101210540b403030903840d291510440e40210103281c040b101c140f407c0840e07140080c400c00d1342014041c1451400d0612603a2440d0b501d111314001c1c00b04015102011504201c40c041081d030400000c180b01407000c900066009000307002904c20300c9500c50038414000346c964080e2003110207071200b100c0948605414071140325070300101000d040300c040e8009245108038800807400b410250506400c035140700d2040f91700080c8016000340030184034242c0b2440b41c80004d904441c000d41d110743d10005207201d8140d0703080a442c031042840156a00804001204c0d40d5101d4150300100c1c00740c001684403a14000c4040406d540c82d10701d00c0d00c80d90154010800040c20900070b884807203840384282d0703002148c0c070b031507001040c0c07111010b07207088450b5040820002204070050014015051003071800700d00709 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 580314577 1250 580313327 580313339
    0x8010305101415040204090c0e030601270e071e080606040212060906010201060305010507180b2b0b030109030816181406090d03020604030f11031218010c0503010501090807 76
    0x25020240030f02240c120007802c0700c4078580301c0e0340540b0001c045a0104010086650b8030141010190f251030501c24004d480c000300d002071842c1d00364881c00c800003260816280051592100130640200f502155102d841c1000952031020040c014240c109413603054811854040d24618061000e030903e40b00c0e600500003407502d840400850b56118004640500d000d4880800613401411a038201a066500b0802000071003500400040350300e02e03022502d400701d90341d900e200d0100c038081e442072100c2d0890004116600d003d1800b20b903000d031600d51a0002081581040000c1c01c50321511001c50200303c1031810802c00c20380d00c0040341c14242403420084000711903422844034088460040941c0c0c44411110182a502c58809459126a0240c810501a019805c029548407402c40b401c5001075036003210f915011b407280d011815401c41020046041440200700c040144400910140e20100c82103e9441c10030401d0041c180c504c1c0864990a40c1c80d4100000180030041c41c2d0800c40303007503221540030488 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 580315827 1250 580314577 580314611
    0xf1b01020307030c0809151806040503100b2710060f0e130b090405030702092820070c050901060f08041707050a0605010504050f01060c0b04061b0801030510 69
    0x9010f03030500e03012030030401c54500302e90b590180c030318499000041384189000481d0810001c00c0240d8545602c000d90810382c208018851207a4011950190400118080502ea090b001410591001040030140b8503903115403401c501c200800c6411311140807801c0c8a55241c0c45590030024100e0b5182a8100c48404c100250071740d2400c503d82030013014415072200b2100b806602060510100404c4440c1904041c14456500d07000305000b60311960105000c5085200514400407401b000c1200380c0040950035194140205000740d840300300a824400d0040c03090300003d00412426210390b0704101468108014030441c90f905801c1001407150008031404440d40051740a03500a50103240402c3c03140e004c0c48600303024040ca40f40148503204141080702000340681006050b520242d90801269452180036552040280300d260b02107081810101d01041040182541c058040c00e400b0940c80030b2000c28400c0c840a101c01c240019101000500402100307010103d900140210240402c800c13400118039 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 580317077 1250 580315827 580315837
    0x18050306060d030306090c02030405100309031e090b071514060a3b01140901240c14010603140a230705100302070b0a0c052502090103050f1b010203 65
    0x102c16014091036004142c8a60071110140c41c851609100009a0140c0a9529001800f4052007a042031081c151890f2082c490608000d0305076590610801c110280e0150301c0183d291500c08000984001007800c249032002803a10070301c0f808507001e20b80b1030841c4090846600c028400240075401007802000d41e04c0b414213109031030300311000650756022085000307020490030300c4900491100c4486001143d03e014a0f080c102d0301e0b225156205522100104246240709000344042d0740e4240d4012104403800389888000c943d083e080200880e01691120b20044051200d0b095840c0c1d1222b8080c42000700c21012008003665840050916400d5503403802e00407803404c1c03c3c0c41c1c250009450204020304041040c1001444050710300072282e422500010041d6010740c4003516075607114004074031241600d209007001000c059407400e090039500d0b800c29070304030480f8180006609140b80384c40017507614000024000c600c118010200c0301c0706402241e0801c5464403010925500ca40b0711600180d0700030040759 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 580318327 1250 580317077 580317079
    0x7230d0903210f030e0a0b090106080607020304060903030f020307060e1e1209091f031a060609030a0204020a050d110a03050f0412051b010c1206050a0b0f0d140a020a1805030606 78
    0x1c164180e00b00201840d106d608640907000d8803443d03040c0414144190700881c1920440e000380c0c0d09603a210712099a491165208480000710140701c2040441d10480c1c00c4070490800384103507498805039466840944014410202c4141c0140980c414031114885900c803a4104181c040e00e50b900c5800a0039500d80030f5007021038040c0c101c200028a00052805545000d40c0801000c10719540e03da0070b00f5091042c0512101540c3c56541c0041921894400141c0b218100014000c1070a0b0a0a44c00e02c00a034200b0b40500090000600a403010400c16000e5204d480801258003038503584441c2005090300d002030405918550306000f88400710b001690089520b510030b040642d45e66101c07054144104841c41400301403035183c925403480865002036051001460207405000c0fa50305c603001c10112284500c0303412a1440100484003109440e00c000c2c0c002001206000201010650031000901c1801c960744500194000394500d03900350058811031a00b00c1802088050038145004291f0720840a4845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 580319577 1250 580318327 580318331
    0xd1202070302010204050d050105070f1b061a030109200d0c030303020702031f0b0306070504080c27040302071a0307170a090c15080c03090307230d0903210f03 70
    0x5001d060003501114000c00020300000807000d00c0742482402002c040e14901c001503001c60b040d03010544501c0170301e5101e9808840310701c0500c0c100d5172203400410205504070046000c40242c081b0a075400e1080d040d8243c020b4010b01448810311080c1d1645c41681d911380c52003003a207048110041448801e0140030f480c0c0c903050059880c209800040d241080d480d0010b904822030b0064201a00c03400c0d048440850419001c6620320385500906441d42d014038050b0355810341c0905040c0c1c142d450007610000905070110b00c204001a00c00610150050341140d0603009a40819002c000044e09602e100d424051406c1e1010f007142403842c0c00500e0502002e001400808035400450030f01201548592842e80d03004040c060304583c2c5110081c0c038481400709070404961600005000b48000c40c007200d02c00c10386100a1031500e999555140c1c0b25058401c1c85005203004401840ba5006d000c000c030400416454a030150202c0c503601d44400e0f05044114440c1200c01040c0301c52100503040700121401c80300c81c0c140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 580320827 1250 580319577 580319587
    0x110307170a0f0213090b01170a180507030308090f0a0f110f09100504140f0112030203120c040306060603020702240f03040609051e03090405070302040e04060b040e0d1202 75
    0x84409406120302c0031002500c0002e0840500c3c0c0e1140300c401c1258030140c000d00588100d500159100e0607403222010840306a00c0014800c03540d41d51000120030500041400e100b121038540c545043d01c280c0041300400c00355402d0144040c01000311142010701c41009101040d01a03a074400d6805101e607009060100300100481c080d5264885400d03403a00150400c041494403a0313000032540b04900c2514002e5280801803413185400f994194469100361074041c0c0240d20300040d8000d18042c02c40284c003180800d004920b1907840201070b0901940c9500240c0740c54900f1400e058044840c00d034030002c2814410005500140c5070045802c012140000240c89010303124120f840c040c0c4250400c090900c04000100800c0080b180c3c0540d0071140107000b121400070b01001507c055115030381803002e00341c6c818030a000c15840d09402c81c40d03105007a03180c054206540c0d9130000d420690191000c5034083c0d20b9001c9100c07241040d01c40c4200140c090001000f02c8002c0c0c070409088200c010303194844260300011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 580322077 1250 580320827 580320841
    0x120e011505060f040b0322030804060c030905030f0c1f1b0c051f060906061716200c0a030b0402030d0810050d0c05180108070e0c09090a09080408030d11030717 70
    0x4c0101b0321f07070100c174525042042503850001d116850482e02198100e00c2c00204400702032080c8100c24503168070200844c80e0581a0f2494403281d045060034551030300c41e4041c1da004809803801080214078100300003007080c081e14010203003035440026250080002c030300c0002d1f01044000669044007140c0091401c10909100300401c05806a90003078000d0340d00b0300700001441540640180804130307031811000b02903140c19680d004100e02c150010700c0010843c01c0c49099200a100c3c507400309000200c211001c52110350082450710b001340c0c1c020781d00d100b00e840400041d814140511901e101c2c0d140341c940040d140014060b1203140360790040c140181d81d2040d80b031040200c1344641e040500f8000704800c4c1407043c001300f402540442405810028001c0600001d001d01405c1d40e02c9000d080028203080c1094985010b1000c14513000306814249034641c030007040810540350040000d0185030029565444900c8001c0007500d2109020f5520f09004104103d04903038404880600c5256080707150407030740c031090 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 580323327 1250 580322077 580322101
    0xa050709091104050307051005070b1005030604030f0f0309021c030c05010212040210030b010c0b040515090303100617070c050f0d05040501080105101e120e011505060f040b03 77
    0x1401c2240294541010980d421001c88003500403150b003102210803240d1140c052100402860b1170410124a05100d80707000289001251503200d004400007844081d43c42d000a440c000098a065004c0f8401440c814a4107502a20803c81080642800d100041065010400a9541d2101c0e000c01d40d000c221003208041c89002c10304c103040c2d0801c0c0255241c041d201c2c401a0410400e5030104d21800340390210281c482d0190080084000c0c0503151206c0d076921685a0104440340140100c0d030034050300b45a0100c5240e101d10040c021a4000700035900d91425100b0716000c24000d0704032a007401000324418406007401100709500c001701d0310303091646800c1891300324504601000c070f0003083c2c02151441c1940b05c0e4090003400c100e03642645c5407145a680c610601070300c140c56034644d800240250041005444040d4914150042c091a11403050902c6041c0d81c01290348030b01c040744461b512140a60006411301042d00050a401c0395803130310f094520f01052a26204600c11851010030100024400c403e001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 580324577 1250 580323327 580323329
    0x60a030f0203180c09010614070212010c0201050a0b0402070c05040c180e04050d0509030c28030f140114150117090d030f020906041e0302180a050a020708030a050709 73
    0x1410030741d120309040403801001c541c01402001c091003841c00c003034a9440c005074924101e551070b8480c400401c1d01403118035200e40c000482a07812840700b4512a840c1802486070b04e1903002d007a400002e81e0305000c2c20141c1500d45803c0c21510550042c409013003c9520f080a08044800448000800401d401030580f50361407402c00781c0c1a10310410000268185c20319010620681c819410744040540150040d6014007070f5245141d055441001c14401509041e004a88007540702292081008030300c003140712071180b007500200c90255402034103070204441c0c1c0318070070501c01101009000354215400b1241809000070049101d401190400c805240d0050a2410000011101d0340341d0170714000d01255503c0f40c603044550002407609112442484440c801d950010b807004002d145401c0c074100d055090407005420104030301c000c9060000060303031800801c007002040702c1c0760a5a14a003000701201150402016002103a0040000700009501a001c8a500c0058103000041c01c2c1c980b07400861f80b0080e2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 580325827 1250 580324577 580324601
    0x40b09040905190302010c030204260f070609140604082112150f030145060b0a0618170f0a08090a0b0c1e2103161d060a03 54
    0x3a064440305081e40410003000100c0c045d800a000c05c1380c5055040301244a688602c83d040c01e40e5004a00e04560b500054203203007080300c0110703802200d04181260800b00e095110b003004c111a104200400c1030034040004c0b0311007080305c016003010b29015803191110309000d00b01c83c00742100040160800b8400050320905c0b200f1406c89411307440c00e11102e50940b01d00080c039921400c1c165211011501d0140039001d1050805a24900014090f50f50350050b05000303401140800d2110401003109202203211840c821b001d84000b2484420104c11f1001c0007001d42c028504100104030240022800c01002800b198607290083c0b0105494038821030030503c103440703001580d014140c811402d11080c680039090035030040b03455440842e030f0381898440d1440303000d14040c50341e00881008100710450030140242c580031001901e03980801501003205c035407000380540f11401004801e1295482458a00e51003034019410425942e40000c3c00041c03240b1050b059a5104490005444001611270b410003104906 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 580327077 1250 580325827 580325833
    0x405090907030f030306090e0c030d031d0a052b02031903090b07090e06030309150a022d01140402010e1302160c082413080702060301030303020d061a040b09040905 72
    0xc0f01c0d00d4002c01802d8a032080c403202e541001b0b00f00c1c2c1d5100c0041100d1000c600018000d103501c1180c080290050101e404d0f5800c0e00740c84072029098094030600c90781c2c954030b100700054a406401500030040e11800441203102c120074a4900040450f000411035900e58400c16601c2c0004882d84d03000c40181880c0c8100070075100c034140a20140c103030816900d10686801884244040e910007045c16aa40148401c907607114003000d04550803480b8141c000d18081c1c41c14419507040d5034289641c40081d520a42c04280034041b5101c21900c8650b0a210f0b0802a03400f2045d00c200070706103900020701c40a11000f100748034807201034540c2c00c8001742c0d030b040300c0241c04404035581c030103031103820500714442d0540700340082405144455407030000b4160102c6252040202080703074645a80e4040011445160300840c0c102d0401c000b4400540c3d5084003950085109560250790350400e268803200b81c401c980d0180c0f505800c500485118088039405031000d0712946044103031100c10340c50014002d01254980904280 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 580328327 1250 580327077 580327103
    0x1a090408092d030f010c0903150608010203130302070602061003020402310302010212040506040b03180a0f11010e06030c090103020417030901230414010e030f0d0908070b040509090703 81
    0x2404001c40400c030310403004e5481603020045080c4c02d84948088020010300d0a039000c0c000103820050703c2c0800c0c040c2c01c40000b20399440c0c0f014182241d01c160b174421110766034400d4030410180c6c1044110007030103552003e000c807801c14980440045009000007403040e038020036400e4a62900c01400006001400c002c2d550100040100c0c1d1401051404164018040c813a03d168050821108072411610040c11a5250a01e0014299010340003d1726244c040b44241f03203d984004001c0004d00c0c541d034040c0710702c482c0c41182c0d460501c500c601d140d01054140584a04042125580e02003665846015002c40959070041c1c580120000d20480e0000b5400b40d0708035560300180035001005d050f03d04000c2e00d41070302c00c504059100346110040d00034607044903410001407200c01c10406000044120604015041c42004000a81009140000f4003000c0d07000c100340c40c100b1684100b401c4000d1000c040600b107120f04040300ca880300c2c032580c026507002c1c510301c07004213504c141d0411440d001140c00c541341405503 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 580329577 1250 580328327 580328389
    0x5042a14120105191406130c0c0501240905070c1b03020315070e01080c0418020403140607020709020f03060f03030f0c150a0612020409030905061201030203011a09040809 75
    0x44c80c807441c0c1801300c0d1500700d0320300b048060400024090200103081400840b03140c001c0001805c2070f10101e60801142d40094000a01e090080000300141026030140c009200c0740448040d0f1340680c0725012039814103050004040e0050304000d60590051501c540704a070000300c2500079035490340000c0d09842140b2a1018184540c40004c1c080c20841d50ba54500040d03039030046425103000c1d00d1245502104010401000300003400d0128503200030b03207025041079074070388075800340805000070349003d60012810003030030b5035040c03044030042c00d000c0c24110700780303180d0310b10500301ca010042400d4058401000345030b03201d0b40c0c00c005581e064030700c4092082c1c0e500003002010340c9886110359500701501094000c40e0b52407000e4003030702c002d80e0100310f40a1494002c0c0d400308005002c0c0c1e03000035001e101c030208000c607040e1106401805510380c503001c000c1c115403640c418107084a81403444d41804c2042465480301039548c00f8502078116030030074a0151038190031000603181c6001e001030500f2208401c4032074168 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 580330827 1250 580329577 580329601
    0xd0206090a06021612050601120c05150d0605010504140f121218221a12010b0108360f24090a080a030f0e0d0305042a14120105 56
    0x1100d0460000352641d40c82c0c030a480000c482201c000c04581107d4010711203501d001003980b68080c001c10700700c2510b80c0d075507000c6640340e08403106101140000207001c0705282d841b030082c0c1c0001c040038609036213041d05d4040b00e01c04008203420281d01c10740b00202d40032034968500c1c4039824081c241c0c1d0190f44240468125a5900d80d01c44094803801400c1c844c1826490324160078042c21001c512a01d0160803464202200020300ca500c0c10881d1905421003031515a0b11203501041c01e01140500014000c035010002605101000b407801e82e50f80b0401030580300e02440c00f6814200c146000c0c40307040c0d48420408800342006c40c0da0040c50114440c5c2000e0300c0303840740b0110300d0303900101d4020340400320b030f0711801045511122006800342c00901e082202c03d0049110340d1129400c140003240010319004809442d03070030012080314030000280c0f51030038407040c08440042c00740d1680850007500d580e80d0f11140386d41c803448100e120b08a500c010302c00c51903000786c803080d012040c0d2880c00700003007010b446c0200081030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 580332077 1250 580330827 580330843
    0x40c0504260d080c0702041d06040b1008010603020609101209050109020405010801090209011e170102031008070e0613091a01180c021504020406081911060301140d0206090a0602 78
    0x4241c8524040c40b82403074024a96a8040c109480801745407100030340900c4080c116013a00074900b040712210300512003500344105809a44a001c03180518144501400305403042a002404564949202080141c0d1500221043e050f400c0da070103038040c008076206075030030703569400030a440a0416040804100d41076005e21042c0744211010007899807034039a69402c98003a5880203402124400041c030983d140140b484842c0740701252001c443c80c0d1250b41c00c100c00012000c09070f00381ea4003c003c8c00300a003005011540505104001130200510b88098048465405000310340a50b8142281500210003500003502182e00030900f00c486200b44d140d4102807001c2480b030401c001c0d01040011074510020300a91880c54801c3d801004a4540d071112010314000c043e20403070703200d99903100009400c0c00a000440c00079040b0400c201e048000ca04200c40d6002030080c00d036107c0e480420050103940a00310400700014025101600204100c0c070101d49148102e043c0c03964404500c00000840340d03030000c1d041e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 580333327 1250 580332077 580332149
    0x44160807120f0c0f1118060406140612060418050d030c11102c0f10051b130e0a1d0109020312280c02010206150f040c0504 54
    0x200c0041c10703201c0c101c0c0d81c590310990880008204000d000041042c00420f0480d0718029120703200302010060000e80d030002c4000c4100c1141601c841044254501885044018901c424580107012000d000182c614420324a04000c00507c1d00007285c5503484561100d14010203103c0e28000259250400301e50354144c141e910f200103030034180070021310307841a0048068004400004c11070055100d000201070958460608040c03030101410b500d5178405a10030005c030007104c4c03000d4420280d62000180c2801035010312290041e060030107018a030580c035821840c01065007940b45845881c14120b00030100f2295000d03900340c1c1d1a540034082041002d5000304c0c03075900c500440644080c42004100c1c00e841890a0103581074004071040031041d03003541d000f0030818920070321082c814490171805800d020348814a90001450094629086580404c030540d00180007018042a6400312400038070f407070715100315290081c0e49443c0f80c0680c8a002d40d0959016060b8803602c00c403811000006030a41300300ba000c0d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 580334577 1250 580333327 580333343
    0x80604061b020703230a0204050a1b031a0904050a06050c09120106030f080a09121505090f1b040e03030f09120307080105041e02030f0444160807 64
    0x842010b4000228541201d80c0450f079100440a00d60301700e2030250000c2c0311003525014040b030300301c0140e82e244903940c81184402d20000303240c411111407145c00d8045c0344911040c14640a030b400f1040d4402084150451002c030303103080f201d9449140441c1004107240000740741d5800d01c020710001404038809401103041c2581c0d802d82400080340302509030f6515100103000c540c4046082030205203a03400030308804801d8102108038682d114500081c3c0d92400105540d685803d0003040d1201d055070055907007154000004005c2c03000049034168070f40540710340c6400d00f4001c901d0304a500c1d4943d5007000382c4184150f025a501c0e4505010300111180f8101c07031801d000d000300144225052040400c0d40c0c06641d040e6100d204681c28901440000c3ca9803142c00c607040340701d850308040503000c0c0d800150320450740060554100c5c1441c1c41d00554134041e0103c41000342603080384481072100443c0c4542c1c4425402e20170718039a40260585216540300e070540310180c02c5000c1381560f060103101c5000b041c400d44200b001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 580335827 1250 580334577 580334621
    0x110a0e0f04210c080f1b0102030f011d07030902030f0706020619020307090e090c0402162303090409060905010603140d08060603131505150f03060c0a080a0608060406 73
    0x550b00e48001d2101c902804a4102031101003c01c60200160501c000d000b0741d00c614205140b10242250381d40080c14501580d0000100051501c8403402c090060295454000781003270203c54800701c0c1f00d001005002055078514800080d503404000704180040b0f09815a01a41d03103400c4025100c0204070380031200d40d6060300650595049078401c5920880c03c5a841c1640c450410702d10035038401c2c01500e102400d00c540c001c0c1a201b43c1d560b20060580310b032008040321001d000e51401d040c000c1d02030580d540070031008000c50803650720302108880070614101c1d400940c513800340c50400c1c0140104000901250301c4e01c01c002c0f0030401c104400406091615080b1940c8400c0100101c485420840b41c194001300d050001c65030100b40c0c500412429403051425001d04880e84443d201180c1003128000100021203001003000c0c204882c3c07010710400160080d011a151404031251030307124185c1c0a00800081800003916030920350f10020141c951030068812a00300b50a0050203842480344101c100b80320925 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 580337077 1250 580335827 580335863
    0x6030a020a020705100507020d0c0f06050a0e01020a030206010b090d12051e1303080c1c051309020301030f14031308030d0e0c09010b0f0d111201050319110a0e0f04 72
    0x4078400c17106546083c90102e0590078000300300710484040f15850f05560f004200302411201142c0540700503611252030708488880200300c404100074150541d08240300700c401080d40400c0460540c2c040b40035050f03480c2188000314001d2010001c1c0a031402c0070408680600c981c1c80b2004150b89050086144110030180105034160b205240101c2c07220341910008000254aa601412030941c40006842d400807088081c2017500305d000d10000002035000500400444c0d086980c01d016105081c0214199811550341c15000c0c440034001034500040c101d03580e2031020301007080701e03516174074407004c6003283d9aa00c5142d80c0c1e07900004408212142002e441010500c2d0000300c801c451040141002a56403070840070301d000f80e0240010000d1030b9010091241140841d009800c007001081540a40c1d50041001e42c2140361810303003086109400007102030002c3d1a8044400c104541c1008582070003503a82c2000601406a42e0300c00b84141c3c501e0020403010301c03c0d0602c0c00d8400c038006e03440516000c004803 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 580338327 1250 580337077 580337089
    0x140c030c01080f060d030c0803042d0b011403010e1002030406110901020a030f1218021e280e0109150e071704050c030f070603110f0406030e0c06030a020a020705 71
    0x82d0290101121980004c500789801111a030440d80a4101000d0010349500c440042c5d82c000c42d800d031a01c90700c030002c040c0401141d000207840300301c94645d0058055003603035402c2c1c1410b00610039440e1a4a800060703155550303081d402113400c441c4d9042214041c09800041002a4008a07425940503103006600c607001a100d800311808408140c1c0035241001140d9015200d032254200000108801c009803a144411180302d500d42d10078910791410b030602c2d0719104001c01e4002c0e401209004081e504499240e681341c0118508505003013076022844200c08401c24250651198449074464600f0000001c240d00c0c40c0c0e01040c401d40d2101204c0340041c0d2507041c101d130050002d0701c4050009031880c20145d1198910100aa0441d125030207035408900c4200000340b5014440359000050b030050041004016090b10902c0750184100c10390900b84281e130b0302d0b9032456005038800c44043c5070700d482c1e0790210207000b80641c405001000b00120307143d05001c034520b0029003003903142201501c2600008035a070314000e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 580339577 1250 580338327 580338331
    0x80f070302010e1c0b010b0702120c0d1214040e1e06061c060f0b090a091401050915040903180501020312010b070807050a05010b01031109090a050c07140c030c0108 72
    0x1a19405441d0400701c3c24071402803905400c449080c11604181c030001119440503a000b0120324403070a442d81c18500400506000d4020315001303607400404141d1003a1603450708621855044615009942c1c015001500e1190b480038889400c0d100004000c01c680340303402141c03400303000c0d0860b0860613841c03010802c0384101b1082e60103c2d07120b0700c107100b0f451801c0d00c1e4910b0034404000e00c01d004950b690703649810210100c06a0020310090754045422006402c040c1215070050a60000c24480c0e580019108130049006021790303401111110b00240019005d0143c1c0c3c1c90704e42c00500101310030145130400421140f0764418401c1c031002500400a101c0d0310001c03c1d100e02118250b00d0309090303403808440001d503500140701110030031000e000c1130011507414064030429174020800801c0001410000604446400c407071f01a2008040c45102c4454030344030802030b44014a40000280e07a00d42a0120385540607424004101d2080b000781c0e40d41010010640d0000500c0c107404941d0500816001075401080c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 580340827 1250 580339577 580339579
    0xe010e18062206020d0f0e2a010306051f030c0f0815030a0c030c0905060a1401110f100603060b0301050405120a17010b0c10110403020405150603010807080f070302 72
    0x900c00704181d0120000b58100b100e0000b0304a161946065450340160303084003c146044a6850080c0d41a00c046401034500744450355010306041c090202c8414004a88650440d82001007040c0300c006990007580801c016041c02841c2a0300c0c1d18160180c080b08201485110001074285045014214000d1840e011420590f854080d642d070f550790b203090b010401d00d03400b8a40c5441459030750000324446e019484080c40c02403644100d400d0400e0451000e0f520701801c05801603000204c200f010600808001e1001002440c0c254809411140428940741d40f00301a00d2103406640c0e101402c500d041e0f0700030030880780300c0d501c248100d5030300c034042500302e039003c95000d0010b401030940b00301c5a20011006088450a904049401076002003100003061130903006075009180002d18202c84c134404002502c405510007100344140c080f00c1001440074065440028017480d11400810003900c01c488010750b0030f00001e80b110741c4a41c1d40c0e104403a6181c140c4d01c24803540d805114005428804085107000550350 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 580342077 1250 580340827 580340833
    0x31e0b0f0105032e0312020304090b030d0f031a04020d1d0106030f23010219030e0601050f04090501061e05011107150819240501081303080903130e010e18 68
    0x41380399a040038020035814640d0307000c0324140200004648015400d414610795000b03544035810070300140c08030307040000368610030f901c41e002a04403694010444505c07c2c002e485c01148a4000100d0180108914405030380c0c4540082070440d403c1841d5032004030350442c2e10703030740c0b200044140b010b8600700c0710a404060640050429000e000c2004031034451042c079a03c44041c2102141310a1190880e00246484000581d040d8000408680d05008a0a2880d0f044004d0641d40d403510000400c902040308076107014644074407007035048c40401e5000700001c2525016008414808241005003d42e10380265070200d001c103c0700c0312042d140094018103880055410140c5020400410b507000580104000c44001c1c0d42c0000e050f1800d2a0701804040302c94401490000d44084a02d540c0500100c1e00554100040d01c4104400c6002070f501c0744283c1e90301410809200d407942d00d042411449400701c3c071501444611720020b40d28200c0e254080c103d034510314410700607481c2d04680010200a0302003c0e45958 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 580343327 1250 580342077 580342111
    0xb1c0b060105030c12070f080c090d060b030f1b030f0f1b040e0f07090b010509012a020910090f050c180a150509030d022803031e0b0f010503 62
    0x1502500003180c1082c04a40e2132030501400140d04980403004442040028040b17000340708181d508084c2281d00704c072440c0030140c18102200041583d001c0b80d2140540115128038500280ea101800341e25400c800780300540d0f030080450700044508007944404940079100c1e400c0482149034000c55100c0010f0402c002a00000040410701c17000041104683d5074401d645006000c00d00004112200384044a0303000b8001d00c2e0f1a003280d1104440c0039546860600c6420008280b017680c6c00300750308155440500c0000343d500718818a4110600e200344009400030005c0040c8042110b89070110070403140350910501000302d0200290099610a8031080c1e00c4420a00a1413005400750f9042c0040c80e00150045041079502c8540921b449504284180440e030002000d11549c2418804610b07002c68130700003003566070744103001e5003654043d48004d10b1064001d0301c103190803d80f194203e442c0040c10900c44070309500701a2401401000300b0401b00d4411703c000d1030082010b5029201780c0341319402c0c80c0810071201c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 580344577 1250 580343327 580343329
    0xc060f0408090a0303120506040b03150c09040c050409050105150d2d020a090510022107061506030513080a030e0c040615020f070f2706090b1c0b06 65
    0x2040038104640c000d41c00e00a0342515141d0600040080d806540c40c044507445500c06581217500c0030b01014051400e10344e644501b40c4000403822074044044503248616030b1080c02c445014090b406100e540301703081820303500034a0b921101910a50760241000c01959030ba07001000f0f03245610002103440048107114007880300006901c03400c4280444034848004a0720000b20340b20213240f0080014800b41d01044561607680d100100d01e010f040151082401c4003511040030b0740c3d84c0b4220b1301c04181d6410f410b032551507513092181a1484681c1c41076041c400c4007140040322410380c2d414018400024131b050001003a0314021001201419000304c5c1d02031030484d00501c11806030010b46100c041522911240d60a5912140700764030090150140e01c00341c00e42c0c072000083c01c10602c0c2002162990252500384030341c40b50000ca030f904885015448080f2800c01d43c01c005120f1800344d0405048034030b024000142041c0079041038801500803145041d00c00c91000b2007080c2c00e105414050641a22800092030b0b07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 580345827 1250 580344577 580344601
    0xf06030a02040b010c060f0519060b0d0507020f03030108030a0e0d020f0103051f181b0e040b0f060c0d0806010c08030a050601050f03040302030c1009110d060f0f06050a05060c06 78
    0x30801e81817404180f1035410b902c1d0340b0244e406112425880c503070f0714010400000202c43c6044800450700c04148070207490020036603018050001c0d0f0205c2e0b10380d83d40210b07004a000700066142040c50300d042e42d0301da6130340d40b0b4000d803030340c02240005011940c4101c41c14481e141c241101007100d907004001840309494100114000c1c18000c1c032000b00722002d1101c0e18000181e00e5480c0006008010124502a40400ea00c0c4141c1d02c0c8080d00e05101c070f00300d01c021a002d51700700c0c0006282c3d440c15a400518214898000740c3c07188041c15105400c200300148480c0500e2000c6900301601c01c1ca0b032203405258403444011548040350070300203010b4031401e00120302d1800c095001180c002205240c694189205040c255440b988285c80440159000044007401c0c0102409440841000b40780700300103100040d01e42e81445c4003068141c600c1400d003401000304100441d80420005500401c04101c403c2c1100310240041c0440e001d01442070308009000242403400b0320032284c0044000020f000c0686031074184207a = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 580347077 1250 580345827 580345841
    0x20303180313081b180406051e09010207030e0105042612040b12010f1a0717042c0915100b070c210804050d14010c0809060f06030a0204 60
    0x980c50104202d40007040741c240c242c5401030b1041c0c2028203115452031400307040c02d102403000701d0302441465041c3e003c0112400c03140b07907000d50010300105041c0c0e42c15403031444102403901c40541104880741030149960055000d010311911135210200010b06000066030140102d10540180340c0300603011540201c40a80c1c00ca42c010020300c01c6a0500d40d407004a07000c0340d0020f070402d01c0c1c0160041400c056441c0d0783c3c02410300600044440c44d005030305080000c4628900351850880310940000c2140411016410701e14051404080d22906c413030320703400c00c01d0840082509642c4030f0400c0d40c28010f102d10060185500509102c002400000360b02250844101c000034006c400b21100c0050000344902c05d24014a0741c14482d200341400300b810702644600040c0ba2112145000c03031890350700b0380000c80714030444d0b0a0303410854180c0c119200914040100c0d40d44c041d01e0010325420034852000494100e80c40501807401c0005403290341d6220015002c00c4c020032115140e16920000c44000503040c0317580052 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 580348327 1250 580347077 580347121
    0x5030d0c020c090103051501090b060406050a02190501050907140a0302040c140307030f0e010c02120f04050d080a020c0303191202120f070912080711040b1215070f020303 75
    0x10b45401e02c0d42c000600300d0800345e1041d07a45800c0030384403012a0385c030084003d0141c50008010416540403102161035402180240030134020300107500605e01d07000300b05081c041801403602c1407241090b498442d010b400d066034440400d01c5444008075400400120b4240c10110250511508602d9902000098030104c00700340180041c60b5140b0300c150a4140003980714960310b0302d002c86c844458807485000c5640c0d0301500c03001039152080c00d400c02540400c3c01e05143e5a4800f00a440e026440c403252160322959001c0c81c3d200b44000c51020401040740081d181030017054003a0385500c00705000741034481c8201036498a114403d11400f0f66103601459605408800c00c000041c107107007040e01c65035203041050701c80540207420181017021031640510b104014207103d40040c0d01d842105d41e11030019005000e40203000c1000c0550b40c4041c0d031226800036a41580c02031814450404001800340c4900c1040c824407502d1008100042d290b40c00b850740700824030025030045240d40c0d1280d00054000551903400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 580349577 1250 580348327 580348333
    0x190b040b070e21060f0403080a0b0a05030304090605030c01030b100819090f050d1110020306040908070c090608060114060a0e0a1e090c200708030307091d0405030d0c02 74
    0x540c0c0c50341c54600c010040d00003003203010315503014280010f6142c944003c1001100d00d50400400c000039a00101d0190080381c40700e40415844840e400240801580f60400d607018071022a000030028996081402120419001e5402083d01c0300011026191783c02a0150080c89900350603418911680c580caa0041d00c0c0c28001181c0210021408142d071034000d17096031035001100f05107090203004d00c0f004410240c2820064159005030341611b4480280011070350040fa03010002034000e031917a400040300755034060381c0300303a544a6038603000b200c2c03c1c1280541840280b401c030780410320b0b01d00040c240781603030b0b84c0c041c030b1410784c444080410100d54001200c40c410410500445d6403980c44a940c0540506405c01e110704035280e8800d4040403c14850b44a00103850a202401c200a6040144843c041c10b02d0b99401480b089604000707450924180d1003460184000001c1190750340e81700c0d45d0303001505c00349071003655400c0041c00d9020211800740d03806031031034108014141c1c46031050b5102102a0340a401a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 580350827 1250 580349577 580349597
    0x110c01090b160917031e030a05070309050d030e03040f030b0708070504050303030f04060b09160e0d02090403050c12121602060f06120c040906051017030a140d0903020d02190b040b07 80
    0x2046d8250445500d005142c2e503000701c140140450140111a800046880c04106414558507415076031008101800e0505942c1c2c1006130030060140100c2d006490451040d00c95555030346410100c090088907400700045802020507132091061048030200e0b40010011819501c405800104034100944111401d91b51445c40c851161191801c05220b41c40d5140c5d01c100c80401d0810162145c4180c8221502c01c0403210f8507000141d882400250700150145050f689840300400e1092030b00501c080c60382e01ea02804140110031058546101d0301c02c03072081164000213540e424080e6960f040586450541240490024416042452040e26210183d1040314140000040410111074411134140c801707503210802c0101046803e03a0210003004038080900c460310f1044106a100c0c0111204a410810181d404681710007401080c2d035500780c680d002c100a444503d1070302035a14a00e442d01c2c400507029200131900b050003110700004115801c224118042c1e569951090403001d0010306200900c2501d0340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 580352077 1250 580350827 580350847
    0x51f110a26160c03020406050f1302034c08031c0b120109021f1b030203070c0b270a050105070507082508030405150d110c01090b16091703 61
    0x5100710b08501900440781982d0030750060105484203508040e000300f54040d21203d80c1d8580c1d100400e113150316403000584035210307520040c0d041c044401c08002c04d603070014034074001c04060b1690364501c22a0a81e210b02e0200403000117400c88500742c4109140e60300148400d0504c0403070100503940a0300d09160009405c032040300010070001a003402d0f44802c1c0c0d035460010303045040104094000202c0b0380d1102704003101005005020310307035064042d00b91801040c11142014020420780b0707070056120004d2140d007034030ba007800c030070301d03000424503078207280360031840002008045844070410781c805424a40142d08007001582c4a034407690086400b031150407000207446100b809500d0b2072032100a002d808010350103407800c0e40c800d443d820020f001d41003000100700307503519400c2401c1001968a031494072407001e00c240b0801070002c0d81c6501c82c40100060004c03a018819800040418800c1017241035585070207042055075501c00c4011008205d00d1042070008607070405c003003c4030ba21584110392034449044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 580353327 1250 580352077 580352107
    0xc0509100b03090705010207080c090103020d03030603150506090604090c0b0a11030f0703020f0111030f0910110a020d030b1005030916090c09050f2107051f110a26 72
    0x1683d20615030002c100c1070042d5a07051040344000e00c116402000c18510000010f140c41c441880000c1c424510303910310b10308060090700071000443d08140d4080101800010700006460100c6006d4403da10f204e0000740949000d208001c40c0c65000040084ea0704e060903510225a440350041000348200c402070700a07a16001c000a210f10800b1208003502c864803864041d2070644c09104211040c2d041c460300ca00c8040504003500c0d40039440b03c00080c00c2e0313100d5500c40c6040c10048043d00808606154400544406071802005900b403c0d508a5110304e44001c2e049044400d60011554003002d0b540f030081000d407091002c0c5400c803580300281c0e05c0c004c0310600038411080060b071144440903104c654000909802c2100c1d200103200035240c80b4807842c81040060742d1061030bc0080121914100c002c00004201005a840a08809009002035400c00039002030b510309083c00b42400603004c1002c11041c503001044082c02c1680c4621940008030742030070700d07210500701d410a400396104144140d001e804580 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 580354577 1250 580353327 580353331
    0xe041118010e1b2a0304140409060e010c02251202040902010e0a0305060405010f0e0c0112020409111e07030f111903030e0f06100603020c070e09100b0d0c0509100b03 73
    0x212015260790201c135011101c20360942992580c009000410003031001303048441d0110411a00054540c01c0303403500760010014240010050740c03030310004030720346a00010615075401d00d00388599500000781401c05001c001070f00998200200359031860f00142030640007039940910505100180c3d12204000c81c040075204d61041d02c0740ea010500b804140b060a2041e000f844001f080103200c4000d400400e16615261f81074840e04001724142c4544041030158142d40113040202c1c02881f18100c49060316401d50056503e903100c10601c1c100b001c0c0240c02c1c250458200701d0341500c582c40d8260740d080081c3d460350b5100c115181c540c014030718880280198602c2062082e4420f84001848400441c8c20910703141840300380d041158044c006104c0200318107100c2d20100c452902d405a51840f203100b04904000095100c180380d043c4840c10b100114001183c1313010a40305125080010303248000400117104041c3c807001d4288a0f414030306200c9030a01120240c1d101c043c02d141c880030250b5404c034604080e441 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 580355827 1250 580354577 580354597
    0x503030903040e0901060f060e0a080f0f250501050c031201061d01082703160c06080c0a14070f02030d030204060e0f0a2d0e041118010e1b 61
    0x200003410b100000700004603d80084c0518001c01030030781000c08048411145019500901c20303100b0040440da502c214220780a05580000d0303508241d1404a0103903200d0309500304840c2c0340100d50321819a6541d080303000025a41001030180c0381c0c1c0c80c000040d40c4c5684801e10700c2070140010011012074140c0c210060303008280b40d5440a01c4140c990400aa0800300d8014a9042102c0c01061040103d5900c0040d02845040f90888480550344d080b905d01d10710a1103000603d00501c1002e1905004100c01900100c0d5400d40320092a5503070040d10440502c0780326040340120300f504201865440d82280134040031481185010111703d01070300044e00d03100c00410f81c640000e80004060081580c00000d410104005071403541d01044d1113400242904118050f0304400203000041c080402da80032602d00100380c0340b142e9200f00984500d403d2030304010840301545c44c100b0003001082c2504120030246006801e51902c285640d0030070145840d010005064820000d1303c010803500510b65460062096501c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 580357077 1250 580355827 580355833
    0x9090c0504090f020a08191d0706080907230109050301021206041d120313121806050703022505060c0303040507080a0b0a090206040902030f0f15010f0e0a0305030309 73
    0x1107045011000d03104592200001540140503180300c2c280c1012101f9004880d40c03420303075480000004110010b00304181110303281070300c42903a0348000c0004103502064456664840900e03030b44004240d41da841c458801c00011914000c3d008001005981d40038040040c1403509000c461b640d04002030030790700120109101200345000380119440d2030310801d41e1901d0284054a03007000d40c800e8140e10b402002200503401c900c0000090010b00340210a0b045265110900c4581c45080e41c00042c810100b403c11080c41017030402e00072803154010f80c00d45140790352640c024009860909200905101c0500001221608001c0041803e507141005841319001c1c0c00c00540c2c0f40d01d001d05240b0f2528800c0d82c13000342c40340c01001000004c1080304086c107500c15011840400c2000300d070320106d031003403087d603114180391407000c410311285105c0b41c1e5500b8003a001c134155984a0362030381205104c2402c44420345501051821403030504541c00751003103441c84c3d87d00911400505035651202c03815580210b800c07003940c0d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 580358327 1250 580357077 580357079
    0x50f04090614120c01361d1e01150306050307180f06120b090f0a1a0f06010f14090607050a0308150a03170c0a0303060503100e0c01080709090c0504 65
    0x1042520300c020f40408a08020040b1542010028003200300d08444155103601c01c40360415240342c807036904808038805100c1e86102555540006110750034a41d41c0480d0440c1c1200802c0c1800c03240d43d400000351954690200c02a46050410040f030343d032005c220001d054440d000020140d4051080100a20410003564820007210b040136003244e44040c20038045030b1800303a041c001e15081140001d80103900600c440d9254848120803440c098040e030340d4118610070b405e14002003240449450403220604210329402d5155609816440541180c09034001462829203c6c15144102042081400d003540c9440c0340c0100c01c4080303245ca85c0820004d0b10710f50b0041d410041055440788220394000400815000074100c8000051100185131001a105c2d4010000c03010007542280100c0d0000104a81290b1a420aa10340a000713400e4600c1814480e000b1901c1c40003440010f806241d404020040103450480e5009006441da081c0180c01c040400440f641d001c91100e40c10b05c0b41901851154654075119 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 580359577 1250 580358327 580358329
    0x91306090f0506010915080c012d20060f070e0a050d050d08090318010302072a0f0503010c0c061a090a050a0f0e031e0913050411031606050f04090614 66
    0x40c6d542c0360341c09881003030014020845503d01040b0074804070320034038203908090038440004221b250f8400c0c10200b1100d9810071040306640100b00d44000c2001d40072511000540f180d540e41c1c47c1d51044613000c0004c0c580d0000140260710440030120003101c02024141220f80b603d010400c2196140c600b15500e03480301c0070503024690081d82e084e0f8004840c00003940b40c0800c000d07000a0341c03045d5000702410305070040b404004100c0083c0c01c81e0840400f602031047c4102e52a01108000e40302489a500c80c1d14604401180600b0b0601840d80000440e403260704400a0540c2c40c07100600e0034400303101e041455845410147d0b9100d0f00344a000704600040860340d82010360041c6c044032004002c440c062403828640107404c52000c0305135003860818000d141d040750169049003c0354803a8140e0183d110051840d0003900e8400c6500c0301e0f01582c0a054482100307190042031607503883c04004110303012070309400104940f600c01c2004103a4142182d001c0d60802d561400f11030309031051900300c0e40c0c1c41c0070100350078801 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 580360827 1250 580359577 580359581
    0x50901030f021e03060a0509040c120303020d020a0315090216080d090f1a070507020d0809130e0f10140606070602090301020d0605120d050f130e010803041a09091306090f05060109 79
    0xa0304080f500707041141014ad03601102060700d0300c60902804010101c550a16002c0e505440a40d0100203041d5a01d03008200010010100d81e41003003141d0342008d5022030002114403d4610340c0700b1907503207180898115114500140c0000308564aa940c864900000289840640310368680c484d00781341c0c1030f03009245640c0f003000d4001049142081000c0c89081c0160b80c81c0021030103400e800c503400a590340061408140c490884004002407203040200e18003904074001002a002e1034000b050340c10b8030050301105400c3ea9088005801e280702c90502041d402e140c02c0004000092069000520384070400011a00360381012280204241c0e50b44010466800d0500b090a07440407100040d000002d00c0030030140c5213000c0c074200c814520b8000b08e14404028a840129000790215483e600301569490281560360360040c0150718500b105003480c9154001c40d0421340d064100002c109582ca5503841140d140888041c80d8140c034510341fa02c0ca40d0011501a4042c07819040c0282d0180c0b54940c145403040007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 580362077 1250 580360827 580360829
    0x1504050a080105090d1d03070e090706091505090315040c031406060108041101120207200a060905010e0109051e030d02030c1527010609150501050901030f021e03060a 73
    0x11542d0400301003080d00403020420b07105d8091581400c03940c130b8880c0c510b8280003203040d4140581620031180045100742e43d55000603c1a00e0203004c03145840d0325500c1c21941c40f0428480e503100300100c030b40703182440350061010300f11480014007112000d10054040b0202d00070141c80c15146200f0100c410310500c002050050b1440c490b0100511003400c01da40002c114820080c400b801030012021403803140ea00c90294005100300d120b41c207544414440c02c100888882e4002e0303090a071003019103408420700b0802096812510503440b03005403580751000554020303030b810b0070250402042250101e2582e450521031041d001035804c1c10403514008405040c82d085e0304104c2c07901903510a100403100404001070b00582c440141c40c000030b10717445040e406002c4148401c203902108003001c1242c600f40e80154060402c40c0c1e054807040c410001d00034108000c8110b940603d90005000700702c0700b80194003c0d00400d03c0015901d100500e421380024075500c200c900c3c4e013440089100004140441807901518541c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 580363327 1250 580362077 580362089
    0x10b01080c03060d020105090d060204140904080706020c03071211010c050c0a03031802030d08040c0b1201060c0302160602030d0b060325020a0203071202030d0e10110c1504050a 78
    0x91850074501e01561031408010b24440c41500e80201c000c0440e4407400a840407400003818041a441e01032400c0000782d046401303107000300030710803040e004203241a12610f400b694000080d03600c2c00386a5212800654011184006c2510003001210009101c040c0e140800c00a5503559110044036034140c10309580c91075801d41c0400c0802c1c001000a8800810a01a080e40c0341c10000382982c103810407540d040201a0019506005030781c008012942c01070001803040d07102d54000c2e400242c43d548201554002c00409a0020b0011070041c49140d024090b03046189000c2c1c0101c0d480550341202d02c11091b5296044503005800c081a21003100b0540d0052401d07001046a01e039046150985c0008160380103602d104803542058100074041c14003e1110b00380c500d4024050726030080d25000004c240d400708074022802840b521410a0b80301c3c2c46400d626240c80e20082070072407901d135501e80441d4007a01c21a000d108a02400c43c00440300d5541c2c0802c2e04507035428511060721140b4160170006402c035103074054 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 580364577 1250 580363327 580363337
    0x20a0e07030b040b01020d0e22061d070203030a270836280306020405011e021b040608060a05040c080708071a0f0c01091e0b18010b0907050c010b01 65
    0x24130542e80100302030300c13107001c285070410180007810000b03a4010640b107000c44503442c49481d0810000c1403904004246c500850030080da5034003203000c44418140841e00500140c1041c07000c103589280e070760000d818400004080c40e4071100d2000c0301080540d54444201c40c5e031100012414590104221014100741c040410100d03052a0030b040c02c0e241e0701008600701d00c200c48019000c0c2c0c0daa46504007040010801c2c0041c81c00e85500c0f4038100c4002c0d44540612400700e960790110020403848800042d08140140c0c0c090001c20156000080c4018081c9042a50007511854042540581001128881c2c1c2d40d03200041035a0030f040c1426140c20304e00303030815146508961024009000c000404004484210807500ca5215501d407075022030340103d2221442011001400500c4118150040c21390389002d10340003114141500c00c0c5100d1b01e080c20304005e02d58140c0c02c001441d2f2122030f40b0024510441100082103520030711700040c4550404551001c0407070404036550420740710900c50650701031820b00340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 580365827 1250 580364577 580364591
    0x60e1f12080d050601091e1a0f0901110f0321090304031a0a0b06030403020a171c020d06080a05030301030b0109051005100903060c0c02040e0c0607080d09020a0e07030b04 75
    0xc0d9048500c107452400b0300407602e45000c20300592069620200a03c00c40181d41d5003007615400828110580d0320034602c0c44041100c4000001c641d10040360500b810b00801c45240c412000e0042d1603203010403660020600554091049861041c0f00501c018401d8000c810b0488980303181304503584502400d001c0796540107000a1000907000540030746040d110104111240d540c0f580600080e160303044201741c11090200500c07007050740008581c54141d00c41e41c03001030301c401060000d4006004550042c8040d2000c0114440c055400e40e008240130018280041074264941c80c6991601d85144011505a400080100144a0207102c12405408454406d01250803c0c9848010b00f4105014044c424110261445030403070203104607130001e46c0d01c46000d01c0110315042c40a45620000f08003640582d050003940310303203940c011440f0220305c50300030b08847c03c25900c4e0f00d5441e030a03004603030301d000d07620381c0d0320070110150b82c1e900f400e02d00821103000b42c6960340c61300020003400c0d1149210468003680c10422 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 580367077 1250 580365827 580365833
    0xa0503031305030d020406170a0903021c0e03120a080a05040b06130e0d021c05030c0a0c050f01050c09010906110a0303110f0d0f0b0a0605040e0703060e1f12 69
    0xc4075007000701d0701d526590010301c0c0d0078142d0940c801c5030150110309100180000f20305400040502c0046080e009005042d80c0e206102400e6600500c0c0c000e00607080351000801414448802c0ca40c1d100e00380c40c21151800420003c00d2070701841000d44106800086014580f0560101500da40a54110340500442c14140e5800d0b80c4240082e0806108a96030010f180d030900e0f43e40e11030310500405104485507625110400f035100c1d01031240f440803a0428803074401c4124091011a4051007403c0d200c649816040002150540100754088075180286010401d414109000b41801201d0a840341a0743c1c40c03446002400480c10355100c4400e10290100e0540c2c0800003080e582003040d05824042180150b01040030000d2040c907601c0c440e00c1c000428210f031660303402e07805061901d808030420824540e40388200720341081c1520075a40081e000304001d00015891518168100d0f4450801003811034076190840340101046410498080088408000d41d501c001030840041c04844a106040aa00d41b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 580368327 1250 580367077 580367083
    0x32e051507050d030b0d0f060903111b040f02041502010501050f1e01080718030f05060a05010f060e040f021210061d210d050a11031303061e0609020c0f0a05 69
    0x103c030207414141d40e500e14a10603161056103418441e442100540c0c031030164a0410024580344000b540000c09000c03101003d01000100420b0450041c00034039120b2044404020151a90001c02980305409000014001d13403652405694100c0a0300041400d60400081c0841c01c0004450780d40f09445002469218461002011034443d40031303e00b808076079650724802e4500c40c5071001c912146443d406000014000684090b00c402072081003500e49944452400b41d0035980c0c28002c0090300500701c24204045c90107443c24080c0c1060103080482d202070420301d01400c0f0b030410303440411108191410400981c0d00b0b01c680340d000d402907081071701c03a070505c004081c10504c203a009014000e0404010941a213a404d88070510703484041022529107000701070000303210744c000007550008500030a5141c200c14002009868200360210845017050f481e40c1ca40101410428000500a8480040c0d0004408050045402520380b80802580c3d030344166420038500550030910700c825800401c0754000161000c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 580369577 1250 580368327 580368343
    0x15041512230c03130c121403090a0510140a030b01030b01020d0e01050d0b090a090201020d080f0c0714010920060f07020409051002190306080f0a08032e05150705 71
    0x419a42d94a03640c51030554031441080d1000908014000c2c503001640100317800a8405c00c1d03208140d01c0e000d01544c0c02100d5a28003d00200e01d03440b80607000c0501160801c0e00c001d008010b07043c5841c80703143c5103030701800072194010207021002070345640d00083c0c80c0d41c0502607010445020300c000c1c98080283c1310001d02c000924601d0a0411070009110201090103401151444e04010990b42090030044020380007002c840700b040740580609001c1d5410240500d411901c1002c01d411030000644d40c0082e0007003964441c040031640007015901100092400b44208068a80300310140c021b0048465900c4043d80d039404c903020300c01d0300c040200301c40d1109840182c03a841c540c1074801181d240c0181c6081401c0c000f180074007040851020405e007084c04030311b03166540c407640c00c1e850800c101901c85a0440e10f68004030000040d07680315101e440300042511006550083e400c80114401c41c8419102117003041d05001003d000159003403051019241400e8003517001507046801c50700d0f0000a54400f62200c1c01e03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 580370827 1250 580369577 580369591
    0x161412060907032004060e091005010c0c15090503060c2802010603170325020318040b18010e070305070207060f020a020607051f05151504151223 64
    0x5070003080145009130440c0c0114086443c0106075011040070380f960760b400c0b9215080001c2c0032505402c0c0c40e418030a070206e0251481c0c071864141582010019039101d0070301441245c228005880004030f010303c08820740d20300b000740d0340c40310121841d060802d0f190201c06017014008a204001e0740c034031f40c0e10542c0c0c811075540d030700d504072801d450b000981680182955440500500c01545142c9012080701009511a207000c2295146501c0c00b0500400d2251241e0f400d607015034800c1107100130041030180480c41101c40107001084189050f404109100508194403804649500060100490400c58958000340c42d20b001c01551400010003560750780180b0034407061241a10026044038802d001c02d02c0059009400c00c2c2ea40e801b203203480e80d56503144192064032000c1314104049020500c0c000d03d070284030071003420990700b1052030801050b141ea8254903801050104400690001c12903200300482c2540c2c0c031482510020004940c082c0c4140c6040c050561413480304088400740d40c80e81c00d41e00440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 580372077 1250 580370827 580370839
    0x712060f1403030d05010e1801050c03071d1216120305030115030212101e060e0f06040e15031615140d1b0f08040b04080c1516141206 59
    0x72201d0220382584203405040340c0c6103007800004200420050b1005004400200c0e640e060b1080c1060550b08a40c4142d0300b0000c00c0e2010404102c8513032240c0407403414200a0070401c00c103010181c00140740c46440c0207980d107048e0040918800145c212848500080503940c540004200070740c0d6000b0030501c41401150341030b850000d12591624400d605540801c1001009071103035007000c0d545400c0b01340740b41c842c40810b590000c0303000403140110300c506c03c201c0d20f141d2a070400a48401c800c00000f4200c40f1946a006002480005010141c894649005540c0b01444003010504401412705000000c6001002d0010081042040c01c503002c150f0f010240e5039141603803102032065544c040604c21035084a0101781400340214074140b030700514151036a40d07900e03207180b00b0b03004103070541d103984080741d0250010b8000e500150200b54a80020134143c0d12420607544490030030044848030324416120031040c941c0c0102540400c0e42c002540b0301d03c00b100411a80e0501071526540e6606001c01040507020303903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 580373327 1250 580372077 580372109
    0xd21031a0d23100504111005090d1101031404142a0108040201140a0f020f012003072304050f0607021020010c12061e120206040504140712060f 63
    0x1d02c0c240b10340508000007040030711150800d401d01a001c40c04043c10144601184180c00b41710b14023441c219004003001a11001e5400c0c0541c075406411441074860605043c3c454200083d03000030552500d2003503118001010075501d20302d0f80c1d02c0c42c141980f9224039590740c141009502d16628010760a041000910b06101d950383d55200407100342d207070007a04004000001c141c02c1e06094100300e180d404d0158070b60881d00040011241035003640d000b03140400b030a120b8114030b4503010003140c000f540d003e003007410054010707030b8801c12100300e01600b1141d43d511800302050901c00e618182e10b41182054044851700e09009050b00003488020744802003400340104203c0500030b415554941c0314000300100000c1056160004000d00030b401444201c11a4901d00320022814000d006a1070110040016021769141e040c40e491400759000d8060590380400d0620001031680c0e07403401441c5501c403c2d02c3e03083c059801d081c40081e24850300d40300303240c01003420000c050000f903240091800c212000810703058500f03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 580374577 1250 580373327 580373393
    0x131401082a0c060702061513090c05090106050403030905030a0321110c0714030304260703150207062f1b0106080d0f0306030503090d21031a0d 63
    0x1a07164400300c4400d00728042001c0141ea200401c10b00d204940540aa9038561307140400d440d1405802820240c1c040340840c4011303040030341c5600580200780b044080c142c9040c0c0b00c44c001558450268071010010304001000c1c000c2517403008030b25008040c01e40c010b000751403050380c01070030030142a4451001c20440980c800ea4003031180d0082d6a2105041c04c101d548c0d000070502c469200c03010790007541d1108280311604031950a0000071201103400c032154403086807540e6603100e12800e01c0c591a02c80c240c800d54a000c004190912010ba80c1060000300c01640c840c15803810300e003910340b07868079014030035100c108006400b0b207054006c0104518444d4140d5503820344007101010082e0314207807541c480d881c000000c5068070300010f108100c0049074480308440300b2413100881c19984240001043d030742040c40001414281280d4082003c0e21403c021006004280390012034003c0e8029040c001a4641e02d40400300024032541c90703841402900c5400f008a100d440d50001000c0105210b080340c108040901c1351 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 580375827 1250 580374577 580374631
    0x12070614091e0105070e1507020a0905061203041a03040f0c0e01060806010f170a021b01050609060607031e11030a090608070c050a0f0f02030604031d0607050a120513080313140108 79
    0x10249c0c01098051056110749142004040c12a0b07224021700c40321010790040c00002007907804031481074100022181300031040c5640d41d0006082252401c000f83d441c03400240604c89580c01500c0c0d240b03d40d90140d07143c03810003400d100740034220070b06000b1514500d2004561181c0600c3c0b4417000303004507098580300c5200103030080c0710702d00110418140200002d850400c0c1034008074028441100d40d0b240940ba20350410149100c0e2400040c042081c01c0c0f048452011003407880400205541032490750301492240190665110040150000702c0e8030b40140090f5801c2610103800091300d240031010400f00c0e03940c9a83c5c1e0450202d0107401c0c0c40b101400041006a8039515840c1b090340a0241d90081c01c20b071030090401c1d5240714058284900c140003a4400d420140242c03020340350000e0003008012002c2d00d5400611040900307440070410108610242002d401c400c2000804010004503541e0002d003c0f2502030a940f600012040318030545048a140c0c1c0c0b02e513080c1d81101c5885170440d1210760070120158 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 580377077 1250 580375827 580375837
    0xc0203071b0b0a0c0606060905180c0d05070c0c060e060426030a120c0c0b130218011d0612070b0a110105040c050414060312070614091e0105070e15 65
    0x490b02c000024020300c0254010202c40301140700700c1c004c0c0021902d402003640c40c2c4107070b0301850f070b0440750441c0922039150f10040c005401240f030721096858007140080e401d066440442e072503008141c0d47d0b0504c0d400c000341c0c042201c0081c2090310b05103566016010001c0ea5521407407159075100b813840e24a6414840e545c021303817090062088200d07542d80c00e40c8000948556015007005138030324503051101c2011400b42c81c02c4400c00ea400504401c2a5446840302c0c3c3c064000003800b6604034031000103640100b5030f1108124040d0070180d0b452100750900e046d0200c0520002003115001d04800c52904900550014080c820388000e03426154030741407030503001c0341e02519403043c0180075030801c030911051004407400e41055900588060004500704120305611103000d45500780c00d40c0c0028200014841801c01618a5038400c24001c90044940d406880b00e9032400c2da09003000380c0018040050f50020451900041d000d01c1000b84124034103014003405003084000c22074002c40c6200e100400c481d02c0e08041394 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 580378327 1250 580377077 580377089
    0x612120d0608030a02010c1b0f0803090a0b0a0f0608011112072105060a08010b2202070f0c061814010503190e010c1404120212030405121b040c0203071b 67
    0xa40c881c612007400902034107d0b4031006000c261134517414148211026002ca25042c4c010805250342c1489664590042d13100403d049054010366003108000741c0d0080000e8028110020003140303502d241d503442e104441842c2d0102086030f1408079245030a41090003940d40c8031140e003040118994400405030f80d4020b040034094a01e240344090708070140456072240f80a00410758045000c00d4448000350b0880d10008a0298051481d101500040481d042000c280301030303400d005070030b1020659a4001c0e900303003000111204000c032202400940d40c40311340c0540e003014100b84119000c3c40c0021522085000314241810801d0001c00140c2d00c16090008010910142c11f04204101c515400240200008000e000005400c1445400807042060503681030714820340680e2040100e690801c16143c41c0e4000c0004180418800010300e42d81d032603005d4015003050009000740203103a940d200ca2240c0e01d2505c0900c980d140080b0100003030340c000f0070b40d0b80656121a1b501c90703040014598110074182c50b4804 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 580379577 1250 580378327 580378333
    0x150e030f0705010603061109130c030b030d26010e0114010c0b04050c03060a1a09060a2414040b03070e010c0605100302130506060702100c170903060612120d0608 71
    0x10042042c1540b10788110ba000d002d08100200c16000844c1c2284108100740754003c80300c06409164403c9a4401e00303007203a040c140000c1488400e004a1704200c1c0c181c001c50041528004d51091f066490660340c1c0c0041142d040e030b05d86c035606004100c0000341041c0281002c40d141c0750b003000d2040e4094085441d01c2508450786c0b122524041c5010340d0340e5900750041c14024010307500407500c0b202403409440c2d00b184640005240ca1080001880310a00300104a2079004006045c00074403c2d0048146604e919180c002c141c0a903205a00c024000c02c0e454030724060600d00c10001084089082070035683c10107224a03200c1c2600f00d15600403510142040300281c8100d290000b4041c4804500d60343d002120f10a44509891422003000740040f11800c40740c0d26004102040507200514100c5a031980050107170400880f03508030341e103c2030b186524014030030035041000109d40350340307140401c4803c0d4800c5080b581500b1a04411075469190641c03c800f905d4040c81c04a5a20008030460700400c02501480b421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 580380827 1250 580379577 580379587
    0x80a12060e0106170c04150c0f030203030916150c0f0209160e0a080a030f1404081f05072c03030304080702041b020705011809052a0403150e030f 64
    0x19100042100f07105603004901600d01d0f8003805050350102c1c41c45400071042460925180040000201800f100b03d04208a8400368040020700c680b10f00b010001d000758010f580b01d241c00f03002c0b917240854548044101d948407031800c00a90310101e034445001ca6817864200c0500980d032400c449901c1c0e031100c0084d0320071800070401c04042440c1c002815641e950f42e6860404221440034840c500299020381111500401451000709004080c0c880c11003001d4602801242460481030000350040c0e001129107401841140a91180740084101690003200040049040140c0c0207000540c554840381c00b0b407080c11080602c6041522100310b10f5500240582c0d035070f4030340341c03800c0452a48101012481185800e64442c41d50f01c90107103051405c52542c00415529080000550311000c001001802c40f40000601289801c52800f4040c0941c0800c008144104d10240c0b5012402d160305499511102c0c0a220410118400c0c04d2240d03a40445504005081c01c03c8400060542c8500d128130310080000207a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 580382077 1250 580380827 580380839
    0x31709011e180906080601210b04050705100801350708010b13140f3105010e0d20240912040e0403030c02012a08010905060607080a1206 60
    0x2c04035410b0694003560080a48a0380781004031011402444060f80c007141c018800300483c2000700c001c0c0c044d0320601c40c0604049548000300c0321006c03181261203801168080040d814000503669141543c2e0a02d6141c40d81003c0c010144860000c1080c0e1202c48045002044295442da074000781801c60b4040c2e80c00940c4404101c0e029101503443d85000750030722a10940d045110744100c450a504204a03030300130780c5584050040e1100c02619010703030003401089041070050381200030050401c10b03900c0f071440d0345100d05006084504442c01001c1d5030300408015100c5651107041c1c071a17010850b000003403a00e42042e80e840e00d82110083c681841c1240b602e4090200301e02c420009200f00b0f42082107455506a410740328441d4003c40c4101c1c10403150910126001034060342041e55403401610000031852034600c1d10803e800c0312044003030460f0001071a0490400d50140c02c40d40504802c0505022500303044022450502c5900d00c05002c1c0200071a040e02070a1003822240381801c2038450620000742c480b1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 580383327 1250 580382077 580382087
    0xb101805100e0f0f0a03230a03030b03060a09030807050c070b0a050c070f0e040204050402030a060f0c0f0908060406111201230f0a05060c0f010e03180901031709011e 73
    0x40c400f4424042c0049500301440e0481d0b03070780680c8070003501e8805450b1a507a15078004808501000c90311034010554200c82c040100848030103070340299004a419620441810b040400162050090354244121100030076009402c06800c00110b01c1c013169651251048181011030b02d0300807460704980001c65200d030992240243c11848081420741d01215a542d280780704044252060342220700382d03440010702501d4240d11055205001800342d500c580c490350ba0314030490382a508503140e078651b640005892254400c44102f00311410f410021451400c1603486139440400401c01000300c0d0322980d10b200b00d400c07424107445004010462205c0d155845801c281041d034507a2038030444032600407040091510702410b47c0292903401404002e619810482401003a510444000d9250302c101454060052424071078081d510400801650300c3da1491103143c1c1030354241201991046426400505c049010f01d40740d810b500500e0000c940d61341e9115070050b100345522214030a042030100c40b0700308080b5008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 580384577 1250 580383327 580383347
    0x1b050601060905060a021218060d050709080a0309120c080d23030609070309080405060d291c0303090b040f0c09020a050f0702043201090b10180510 65
    0x80c1c44000c0c500d030f03d85080c040140212421100182d1100c2603141e28541c1400050007a4400806002101c89500303000c21724a07070000000c8030030181e45404228000d0361248454000c0c16010700908000c081c242c0b00181004002e00680360360500c54024841000140b44900c8000c090240640d40720001107000900409a4030810205682c003003402ca2003019203080c1183d00c214001070a014113916101412001064145002c849058041002064554031b804c0600500300f0003a8001c1120317079a21f10316030b60445262495801005031035403520b0459603014502003000090a011000794a070341e0800701c01070006104050200c0300c0032030500082c4185504544d034624042c50112807120390f100c0001d004c074895100040c000031014004c0014110201e0020050307280010404510382840e08421800b42c5401aa40e4004120f0703000b4091120f042d41880c00d004104105081068500010100715070b520100c00010070042a154800241007140b0b00410281c40003801410035040b8210014008480d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 580385827 1250 580384577 580384589
    0x7031404150206011707030309031103010e010e07031a01050f09100504020406052104051c0908031803120f07023003040f0b1306050318010911010807030b030a121b050601 75
    0xc50700c01046817042c000745490440c0c1d070541e030704000c0918648404180320070160085526548484410154050074043c5203800310300f0002420207207145150901002c9005401c10303410441d0003004006903510700354100c12400041d1040c400300d0f55a410444a40e8201e6040340350f115101103800708032280e0100c090030011030007250780340c200c00791210441074526088070000c1480d0712003404c100e200c0c0d95046407607003020b5032810001001500d50320383e14159000b004125003002c01a405444052500b0010401a41040c2d1407807803030403001701c0342803060f48280c02d00a40502c10940300d2001c581c5140c0403400e07030002a5801500c50084d400480e036100d92062140340d1101001036000304401c105a81200c0000740440c540c1c1d04664030300310054445400c0200020142044c0044a91503c0405e0040e002007070300c11544014421902030000d030144a01400900406280903001c05c8240c6001405614403500151000b0b503440300c41d4412189607400f050514403400c04480081c0400c9000176400781a00c030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 580387077 1250 580385827 580385849
    0x7030606270203090a110414090a1a0709290d0603060501080d12151703040807091107020d0203102309190f15060b0c010509010e030703140415020601 66
    0x4503a4410030ba00041c0c44c2c0c40450740000400c040010685103191840e540090004182c0d40c40c50b0143c074440d080100c549200d15042012004200100b8440329254010302141c0b11041e41000340d002040303041e042c060001d462400c04406071200412003040e8001d4589007c00b01d561b108000d0900000e8141480103c515a003844000305107050045104904803120742e42d0b0b00f041407162042d4502600142c1c0c8044402c0d0410300e00821041112900e82044243c1132000755601c500e091902c500c2c0901a03488422407616000f9440410510304088a401c03c0e011228201c810140b400001e0900344071540d036048152600c0000c0803110718130605245100854124103400f0b6880084182d00c402013a01520412400c5030b4402c80024100c01402c4450340c018040c0c4800110030501c2d07001265525000800c1c803202c082003c13903408509000c0c00c4d81c07200048009010403400340c485c3c00da6038012114000e050068018201c00d00d5006081074800070b1041891041044500c0350380039490301e00a00650186034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 580388327 1250 580387077 580387139
    0x307020a0c060f020f061b090a0e01080303070e1c030f030e030d0603030905040b31021803060702120307360302010801090b030d0c060b0904061a0904110d030207030606 74
    0x41e4041180c6d071040a08400410034441c020010301260307030080d00403580c0b05e400d101010990404a001060280c810308000f15624140b01f84040d01650014224903c030f0f00014007602c8081c1c40c0c2024a002c0f40b9414101303070032400300d003a00a13005050750105000140c8400b0842610121694000c1c00441c1c0c002e8079040149601c40c01440142c4001440e1160000a400c902c0c6820385144008103a40707220001c8502c1d002801c803240c0c00c0c10f81c1d0041056101c0250442460101450305004041d005940750000700304035504084540d48600000303010f00e090211001d0142005c040c2d541e98040340700c1e0349070310880012180c40260245802c0c14002a40014400fa0010070480c00314401c0e1000c4450045c0101180740e01c00c1e20440d9060fa0549007100c860361105a80d5410b52129503000740030300d1040d0804140b2944440018848001e151407444c8181007200038080490103c41d1184002e010542c2c1c0e4403202c00013420f041e0300c0d012091380010100c43c54840001603481b0440c501200080700b0f100081200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 580389577 1250 580388327 580388353
    0x2060703200306060f0403050106121e02090c0c07030c0e09070f060c020405040c0e10090c03110304110d0f030512060a0617060120010f0c02030408120307020a0c060f02 74
    0x10201c419000c4501d02040002c62200c4c90f141c0041d25070001c10202180c54107483e980c0300d031700751241c1c1d0b0302011100140801101c100194070200300c90360398040c058451a00402d4001402c01c3d8030250400310800d00000b404a0600414480035000d103822056211000d580ca071841403990310110b4442d44079000d41b80340800c14980c04d06022080340c9441c0c2d51421410465020000207001c068000c07a261500e45400041810300701d9803982c41580c115421103a25440c0c80301510a458558030407104041ca89041c0c440b043c0c40c1d0400f52904180c0184209010860103000300d8460010501d0181100440d034030703414100343e406001841001400c01d04011180c542c4c1003130100400190051501049a058440b985a0321648200d80e002405240c008095504030b410300e41041814100034447d80d4681c07c20000c440c40501400c10601c015200542c40c091500caa41a00c230f100503015088c40171800030200741014401c02482c1e140c0c1d40c0260507400c1a5035030b500f025143c00d070403c8510016000700c020402c01 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 580390827 1250 580389577 580389611
    0xe070303120f05161110060b19090515183a240b120c030613020f1203092e0206010e060d020a080601030b0402090c0702030304050f0d0b0702060703 65
    0x1031340b903401507107240411a24155000302c550071300d0700d0080c803031003407104070f05090780c09407174010b0900705441e03a40c0c2c3c500313203a440c0300d4880c01c90b0012051241c0d1400c20400c52700d81e07411091940941510303894032403043e0840300c41e040d4050750765194000e044183c40c01d11212990386804207100110100e07142c420f5044030604480c5c100e0790014108400e2071969213590074014031081d8080c00134840c000b642e6883c4e88000b84114561001e06100c0341d010761100040b9050410540b500070220a601480f0018a540094281081e88127418007411850980f000060020000c2d204002c40050401d034010400943c000105415031020041e9480071203640322181d400850494146ca0300b40f0701d8483d00365200d4050001070980b9030b200303c0e000b080e10f4000198440c4140502400385110b100b080459081a00411820031001351000008030400c10000300141da00208071411030703009503001c2c60003008100c009405a07584c0c2c2c102418110b080001c00445a6021a4140c854203236034038100003c0c5520455844 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 580392077 1250 580390827 580390831
    0xa0e01060210020a1e09090c022a01200c01200c01110a1a011a0406020606090601090302121507020304030b060607060908040b070c061103030f0405010e070303120f05 73
    0x340c2c01020240780c40c8400358006110412440c2000400f1600302d0024000c15200d643d5140300007843c0040500801c00c241c010540002c1051006048054190711400c1844d4020860b41000e122602c080c440141d01800b5242d076000d4803007001910300102c0380320340d54480ba00358005134000380e446420b8030900c0302d24206105440c003050f00106601d10130704005544000000d000c085d1a88280c401c0b40d80040d181c140d04017681034103041c24040d1545021807c22130396040003240d2000400500050042560002e0400d034030a008a070005030a80302d480068500440e2604042e41081d03c4040420344102c0004940d1089100d90035404002d42d210b1500b2a20b9001c0c0380002800b242c0107001040d61464120054090340e40900c00026401525035510f9440350b00552110ba40340201181c01d5040c4689a084a0700810050410000d0841145a21526884014450040f01010302e000c5030500109502c41440044001c08071508152a03007001380a2040720202400c1090600740800150030490003018 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 580393327 1250 580392077 580392089
    0x70e0c070b1f0b0a020a02030c0a060c0615090e0d0f1404030221010212011404020403210c060204060909051806010303120f090305030402030d0f080a090c0807090501050a0e01 77
    0x5801900c03400032100b450030002d000c4010a4061501c00b15040385160700608405203150000c2c1800006c900c103060902d0160f02c2001c0c81000240001c00503a5004000d0894141c1e0043c00010f00d4009071143c0c00c01c5842d01e40064450300e02c0c00000c10201c140009070051490f640d5284c0c3c03035100b88a03860480303000c10112100c5021038401d110400042c1001581c85554207814038480d04014004184182282c02c050800ca8000d000100100309103614a8804031040340c0c2034a0075441c240c00c0d52500c040200d440500010790710700401c102c81c038580c49407951628031540300301e007596519134a40c130040003001a4010307001e481d4501070110720131301ca10030750440212030080c002d030105a10b1178605840f800c4072907220300560f5854043c508075542c224070440318001c0c031980350140c6900701401450300c0e200181c0d0719081130019038081901d1098010300746a50041101c000840d00e0242450603015200813a8844130003403042d1103003c1034400454010b141640c078180c40c50105950740e800b0600c1172803000e1082d0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 580394577 1250 580393327 580393343
    0x316030f1b030c02120c01060312030905030a0f020c03071e060306150302071a01090c08090607020703080c01090b09010e0c09010609140f0607150c140409150e0702070e0c07 76
    0x46680380d4000c2c1c000000c5100703c1c1c0155000c000d0f0005200050350f004800703503800340e503403500c06008004821030783d5080f800680c9000c11841c1c0c00d6968443c0e40348200d005d40c6080c03100100e0100c0c0c11318820001959541c10103020742d103986903505460342c43c900f5120818080090000000305903280320b44901c404860155001804904025906600940c080c1105803094540710b03624000d040c0d168050380d8000d241ca9800007070f03101003005008018182c042d0502e0b540d908003005000c4401d50004520003903d4001c0b180e166a002c259008500403c11480000d02040380e00c0d0401402e0307401980b201a81038031100c00d0780c00d902900010805549000d01541b40421500d22051001e03000070000b00780c4200300034003210000d54240c00080d0068000c1c02c81200c52441110200d6070300b04541c011502d200c455803c10040224211103202040d006502410b590195100c2c40c01e003409602424060080900c0031a030301d52800d1045d40203445403254051001030714026004110f50262404c21110300e02e8109801c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 580395683 1106 580394577 580394621
    0x4050604031b0b030c120a022203050c03030f0d020d060512100b03032a21071202060f01091503051608010f060b121b0316030f 56
    0x4501042c20382801403010817000102640c4403004134002c170f41d18a07139419003650001e00404035401907014814240100c5000301480080540c3d0142041d81d03103855004e0133040c1d0b24442e0003221f140c041310401c64904c00d503140d9406000500e0181e0700c04290296544002180f102c0e106018100c2c581240340b05d02d04070511407140a003515401d4000e50705001044452a5910581c03201000320703000f0320002503a00784014080d0000719000da00c1501c540600001d180001a0030200c02100c15411584184200500000f24a481500600f00b00c4240743c8c2040852070140c080c400c110900038000c0d00d00480055000d101c2202038428008241d195a40b400e551642528581540d0080051400d442481410181001c6a5811042d00c60505d003603100d07500d400040e189603411004011202106001c5d140681038882025040660740c144124500404036208030744e500060702c601d081080032 = true := by decide +kernel

theorem cover : BRFrame.Cov 580215827 580395683 := by
  have h0 := BRFrame.cov_init 580215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580215827 ≤ n) (h2 : n < 580395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
