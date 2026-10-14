-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:39:04.512985+00:00
-- url     : https://prove2.me/submissions/b6493b3b-8313-48e5-88df-4aa1824e71e1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 377697841 ≤ n < 377877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 377699091 1250 377697841 377697847
    0x70b0d020c2e0b040204090c020a0218060d03030c0c020d0c0501090e04050606091e010305010902100c17091203120403030e06010e0604021c0507080403140a1b03031103010b 76
    0x1ca0010014902010402c0300300c052508842c41c5054800340c01c14240500b071544402101c80710307481d980e04840003042d540000304444851060b0080d25110104000da100f10401219180f8407061400350f21f006440c010012614902140d600b038001c1c1500100c0c48060080c4070b00080301589944c184c0d8091a403084804111841c102000948801516003120082d4040c0c1001c01c0300040c0002074071604101e0840d00b910b60783c3d40700c86030b010047d0003007000e400d110301c009000001040307415000848454402c42d50302a00c0086000c044881160103d0050001c1d000e00d903080552010000092500800c040e102050394030300184e0300e500c0d540c400707503c000c4501c000e441000181641446541441000e1300e000d040310f9403420020012850380504014495035002500004c1d0b8520203101020110300101d0510140c40c1c844006409298200d4080d00415032910f402e000c01c0b60507600311000110191144d6590700c0009607660031030801018110241581c404541624011070b20140d4001c126842015035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 377700341 1250 377699091 377699107
    0x316060f1e0f180203071a090a0b070203070b030f04060b150403030203090306061c110406170c13330f0b0403110604060906030b030a060513110d02090402010f02070b0d02 75
    0x1260441c00d54038030103850010080006980c0446c03207000300d41c0c007400117505610503500c1c4c00c1d03068842d100310140c0c400201107001a0310300310755019121082c0210b0560300903568500483c03180e417004030742c9603280100000010b00018025400a0740b4031102a2210600d003031040e003000c0c01544590000e4016a002050101062400700451a07010700142c6c0c04042a54030403054906138189010000d12503035140754928101d854903880741d0b0043c03d41f0417483c01d0b208210f5900903254200304100354000c9085580c07445400c0703054002d814229000b07882090b1230710440a841002d8001501d0502c10303403507550100140030030700b000074070000d0040c02e5003050380c0302d145141110818002030070341c0d801010240010429541c00200d150111901c40c28041a03c1e02040c001a007020545103000344424544406e1109803080c1c3c41e0351094841c401e4000142c0254135900700031151040c00d0f0020360040c44e810000b40154030510034100b00022a004030b90100e41c42d0340c0d5078515602f0800340310321426030101d0078039 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 377701591 1250 377700341 377700371
    0xc0516050306091903050f0d110406170f0a0e0a050609060712050702070909050f0d020105011a0403080405040209030a050703030203090901090c1215030c09140105030316060f1e 78
    0x1c3d410000020040c4440b160182d41c60702d14603c40207001d002d024001c2480001034446030100d95800c01c240a003008001c10155001d4426002030103071100051203a00780050b1030003010b400c640107031111141005103641e11803000003d8040208290f4890082844039400908200019030059445201411443c6403c2c00003c16601e006c000c0b46440300d0a010900c2496900412141e050750701d01d140100b4051094103210307282131242d03001c0d042540328a08080e14119130650004e8141c079271103e0340c0041d4420b400c64405070350145002c05001000700b008108507510b0250300400c02054050140c40750104d00b52501810001541d00940c0940c00020700c05410b032074803065131400f520f28400d0401c0080c525050040030550356180140101c5c2d40c9038100001d00c0100751304140110392083c016850b0549404928000e0401044105080c19402001280c1f5182c0401a59684884c0e1079203007a0340886a1a4500034007074004891040316034030001c6042c0c0d01c40600c410203c541900c1b90104491410f13003004 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 377702841 1250 377701591 377701603
    0xb0c010e03071a060d120e0a05010e0f13090c080f011503110d02030319031d010908160c050901080109050c0a0f05090c0c0a0510110405010512070c05160503 69
    0x1030140d07401c100011400104203020b02e039102d00024480301425a20000428010074500c2c001401e2010304440d00b480c10b95010040e80740d0807105880c0c600d800341da11001501c1148164001302d0744120724200c00300705030825038200d2404020301000440d400d40c0588504029015580081d07a641e04011951540d10909000799040d050400b413410320328a1440d21440c4503c00e402070b0051081d954961140c2c1990390800a45820003000e81e8244155040754a001c3c3c01001e05848241000740084e40e40c64880c041842504803107a00503046903e003550b50112400132000e80d40044940d500000c4011503552605406207010301581c900000f042c2c0c4075402c000b480c1010b8651041d05c1911910010320210700049920400c41e00c0503104040c85444220301c200c82401140310071002c5200d440224014804002a44460401c0282040112540401d04072019100d00c5c001c4501203801005003502c103815034540b113640092603240c62001240c6c1603580da805c1000c40490007541008a46e8203200705c0c0b80c28801 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 377704091 1250 377702841 377702861
    0x31f060909060b030408040b0a021203131e05070b220909021e011b03020f1b0a081b1011070608091002210709030b010e010e060409150b0a0504060b0c01 67
    0x4140c2140f1705543d034140684100e008810340c020001c1010000c043c002c122088151034a020b82a4a0346007010384002c8075400d079841039074000041802413209500d0030503040740e042c1d001005080308500780021007140b5070054200d02d000002c0501d1007041c114201d00000041d003800d0720085800c0a02d401005003800c5490754400c60144441c050010300c0c0e8102d0030485501d41010013404c2084d9090506070f04007164036200c60300c00c0c02162074035000800c410402116a82048a09032455a103404c2596a82c5c5500018540301c00504100e00d000343c07602d004202c40380c50b00c81c034101d07003400c100c5140c5a0601407141e201c8808945d90320103200e100103041c4801940042020780441c28016010f07a1501d0b1034846100100c502e207040c0340418506480b40c7c038a18040e680040a20040d07594402c10828491424450500380010b010081605850b140c052840420382000112001710580c1340c0181c0240001e00c00c00e0390103851200c0c0000c0d580c41d24018580205070142c01142c403800e550300c82d07509440140003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 377705341 1250 377704091 377704109
    0xa080109030216140907080703020c06150103151d06131803090b070803010b13030503030f10090b030307170c0a05030d0e06041a06011202071101020d0503090d05031f06090906 77
    0x4062020340c50320340001d0351103586ca2801c01060740f02c0070410340c000e01c124224021280030340c804001c41b216405103446c1d020402070ba8200000000300d03982e61080c4a441c084e4401401d1244c0000f6070840002040d02d0300b010009055000281e08603d0400c01c80702150858000c0c1d06400070b41d0030070f264001c00800700a203407030040c0c1898504d8036981c1303449a2205005a206040003ca001403aa10340c1c0c07200c4101a40d808000c4035500e0401111007185110200d40d8000b2800b807200000c2502c40150140b40b4000c0009001107050a0465440108414200c1c5204c03a61203801d005d16814035808100c0300d03900c035001d240950307650044003039050207a4a01524004080d0720440601c000a2890130f00f00e0030f1490007121144494548100488030300c1c0018200c841c00c00d00100d00d210a010711042818410707103098080340c00e0b0b0030300041d0980381c6000c21913080f442174000414400156020f00015648840d0324881c95500c54090080e19458000680000c40010340201e800d03c0060824414032010b0580c001d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 377706591 1250 377705341 377705369
    0xf04060c0e1c021807120908070c081506040b150c0f06074107030203040e100510080106080601051b0d27050312090f0a03060f0b01030e06040b060a080109030216 71
    0x20041c05d103444000002c000d15540c2c0c0c84d008140410310f02566880c82c1e0000351400e42c40ea5418500355074000e60800600cc81c1c11740030120b80c1c249170038414844040c0c0050400310040a250705d80c102580c102b6440f4034a107001740003605444c3c5d501440150701c140265141c2c02444014007000000b000c002d18407000068402c81c00748011802003a1041c0b1401e0f8001e402c0982e00c51107071a040341103009a900c07480103002c07940140240d24010b440c0e03101c1516420307030b09580400c00e00d8008840d030315002c0c0304400210386c0910204005500c41c070010030302030340001d500c00b00040b0700a180034a0f0100d200145000940d4114030324581c0c0b01484484080b9100450025030000c0c140030009444007503501a04034145000501c0c02c115440c0c40213003591440c4028402034900e5aa42425805801c2025407007120381d2600d15a20074640c002e218080751503140b030300200308503990303a5208641e44802801480d0310486004000070054024040e4510b001c1c403a0303020304981360004640282e440103e41017406c06086503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 377707841 1250 377706591 377706601
    0x190816121223070519080a0c030b150f090303030414210f36010f02150c0703050c240c0f0d0b12120712080f04060c0e1c0218 55
    0x38602c610054480780781846503034443c1002a12680708481414468040301155015810342113240c05115a8a100b024003005c0200c00c0110100c400c0912002d43c4100111a078000489048014203803000040d80c0c51407411b200300300080c2c51600200c804445c0d0002400085c0310b03140381030201c14080382007103c001d01084414184098240240c1d041900d0242d03000c5000020342c1060031074090b1082e8221232406902250407080702c00b07040ea502d2a00e010820041848101a01c006007900c10701c101c0300015141e076210f030f00d40403996902c036400980030401d0070f000320200f4030320070300c03800460781e845114203000340c401c3c0a004000c0940090a031114004c00b03000b20840900001c00302c1e0900f41601d900001c49204040000b0012203d0500505a070703c076040d02c83c01701505c91402426854016205540c0c0070403022800c6071441021104041240d00c6200407500144131504100d00040f80c41c01d0a0f05003420700800320341000010301b18a031179284001d10003c1541001540c3c4200381d08040d5000085140c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 377709091 1250 377707841 377707871
    0xf17330f0f130f0617030a02070b0a0207050d060204091e0b0a0b0906070303110c010c080906040201021f0603081215030606100c080d050f0105120304081908161212 72
    0x1480544601594a40040e000c0030002a403001000d80481711407050710344000c80340e4a9880d00410b00000142c4540321000c909a420307601512401c41c120340c001d08610303061105001282910140c11502a40c00340004110341440d805040503400c030a00b03080021072001507052090b02c2c1420034007400760b0725401b41030111031483ea08031541000c0582d8040d54a030a00c1c83c0c00c40081203001040c5903140340100c1c060603000c0041d041820403d01e19503e0244540780d030300342941c642000f80c800034003581c0002d13000c0140801c07000b0f0b81c8119841c4070300e00040b03807662501c58900541c852200118081000f00c00c01081040405c100700c410740c0c00f44c0041c5410319143c00400d0340c040c09c41070a08103010003d10540200140e000c100c42504078501403d01c41803c020310107070704082081c000c0f64410451a19103d035440000001e4604179540400107040c101d103640e14040341112544030035200d03800104440d4000f8030b00000d00c0b0700603501c10280c1c416698040c000041400c0c1344050460307541400c002e1034100c103440c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 377710341 1250 377709091 377709109
    0x10203060112111602031606120c021c080c0d05010f0312020307031d0409230706020d020d03110c03161704050a090506060910080f01060f17330f0f 65
    0x60340c60050082074554000a440c0160306501f084100d500e190307021500b158000c002044044d20040140240c102282c0161b840e82114490207141641d520b51a20b060303480341c4040d0703030401b0701d10810500c0c2071122142d04040e29802d0b001801102e2090f01c0c100100b05240001e407400004030320140d8203107281940d00410b030503010210039001800787c100d0340c4001da895a012036071160307000b0300c2c00b1071061906547c1080316140600003401030180040000e040b90001c00c0110300c0800c90350140100005015081d0005c00c40881c4482419006100c454403103070041004001100d0700302e112280010040ca03081010b000c1054090ba60903005000c00c000c103450b6180e10105072000c446001c580360740c0ea603002c941640183c00c516980007008020520342d0f80d0b044078286001d02103d02020320260707290345090b5205000031051100003010124860040307410154466004811008521700d044c0c40c051400ca55038071001039603000b914021420048131b140084515904044c103440801c0f10014000024000d86 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 377711591 1250 377710341 377710357
    0x7050c12030f160e0406170706050c06070f1b03020f1b210309060f040608010602030f0702010e0f1302091903050c21060c03010303030f05010e0610020a1401020306011211 75
    0x110b0443c2e02072400307003d5400c4101d4000301034030402c00207980c0c50b10341c0001041034084d00258090424007040c41032054003110070b80e00b8543d00804c072584611104598030984843e00700704000205141d1400c04c0407040380c2000060003680101020700c3c080480c80c1c20080000d00d466038500f10380001c00d00985510035112003402203d0b814501c0011944100c41c25442100034141d8803034400141e004d40325081d50007400c149c40c3e0a0b5110581c4da0b89440d8203a03940d1003812015848010140b00f05001988603a51030503001c88003402304040d4102c07500c0401d250030703401056856815004a1804464104220b52400e801e00030000c1400291454599540701d4462036192401008080c0c84103da000301070868800485407541200c580b45040036103201b441d0030a000480000c1e0800c04000894103490140c01d060318441d0348000003640364601008503065070080302c00c041d0b00620a0070400b00c0c0400100000c814881d90000d6941c0c40c01e440010801f410780154241490b00d0b0810749003201e02004247c81c802 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 377712841 1250 377711591 377711611
    0x60303020607050a090f060c03080c03010302010804080904090f14010c0503061813081303020f040902031002090112140403090f06140d062111040b060904090804030b07050c12030f 79
    0x4e402040300488201a10740c01046804041c14400501c0c01e0b8081d0351900228007a0b40d84070031030b4503180c2009009200030300c0040c0c00a80c850011401248488004200400b401480003440f00700ea5038400341140341d0b44000359401c031456442203200c44030078000d4003030145492811601d5458100001451231100b00088100d00c400c2c1e1001601d996601803a41d4110360704a504161107142e800d010003040702c0e0ed8081240204040131000c00c0ba41000e0080104030b550003006084a007044c0342c5076a0094010f4180d15040001a050b0143c0c00d40403845940c80000e8105d04a05140c0b0706410060003400003a07001c03d44e520041101044103680c400b00d03402c242051107815960b01c2503102e00da84040c201030781000000020445400e2040c60301c1241c00c41c0510310801d016240500c2d036404010403500703144030040e004902001609114906503201100843c0720303240d518145a100c0c1c607007408a940844184010580020740a540c2000400074031804440a060040c95441d000d4200880602c0127000d40702c00e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 377714091 1250 377712841 377712847
    0x4020a091e2712030b040c020c0f032503050118080a03110d0204180b01050f07021908030301121a010f03080c0a051f1512021908060c0901020d0306030302060705 71
    0x19607500d1680a000d10050600182c180b400070341000c2c07400030040d41000740424a040003400003400d02c3d0160801c1d01c01d071030f005014407080420601000104c0f6021541d45805450301c100388179002810b515080005503000002c0d100d04515281c1e003103e400c1d0440e040082800d2425400003424071080720802011490082002c0d240b1840b119030500800c03a00b958254004100801d542c0204012000000c558a80c20f211962417a401135449100780c21144442d034104100b4000075040c03140380485038910300311840005640d14802d031415500283c2001482c5102c1c8882142801903429601440503024403128045503d4102c10300903e0b116888000d04a00000c01c0640b00e101041c040300c111150032000b502d005104181520100d030f40040b603010100c901d007200d10301000380300184241c142d544801c09010009040d408200b068403506c02c5204072a10300d4138010401d900188030450040403500c61f4140c60351b0b1303408006414a400500050308141c07034124204003280d03001075515003040140c00c155903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 377715341 1250 377714091 377714111
    0x50a12151a2b060c0e09010f060f11030c1c140a030908070219170f0606040b030f0a0c060905030303040c03120203040f03080301031704150f1e0804020a091e 69
    0x5841c0d0600e070404941c42607182c0503001400420303080041d40310800e03078031900040405810414210001c4c043d58500b03081810051007001c0c094039541c4298112030034035030200c150302920385156911011101c2c2c01600002c008040304001c40c004c0d20b100711403504200d220b0300d03400d80b0b14401034080d900c0e8440815803a0700544090001c0c42c012110015005004070310104004030300e88040700403911400ea02d0035064130010719000c03c0420640d1824410501a0030152074803000c01002d0044490a40d515016003800c201c1c80510403c4018801031148001c1c1c40100d01e8603c0103070031502607a1019000c0d40007041000300180c3d41c1005401030f69444055a844e140e040b000407843c60003181c2100d1040b03000881c0200501003110302440c103d03407007502c004072400c6403000b02c101c45010718030484500c90f00501000482a0040200c2600941140740c0f1040394008005d040038011400c50b0307000d010644c0c0c001808250b060441d00711001d4100300d5010720200e140c26180080700780d08040c07200707260750381c0342c00c805 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 377716591 1250 377715341 377715379
    0x10051603140c010c02101526032110030203100c09051035011203050f1602040c020105090a060906201b06070f0f0207050a12151a 57
    0x7207030000d120762464590600040850080c444104814094130680d416203a041c000c5005a8001d461401c00c16800c4510b4015255040318220003150103000c6032055503081c03020201b0160080f4944940b9500140b0055220341c400341380040d003843c002640c558000c1c40907807030016a00740d0f01c0b05602c80000d1b50055042007110038920341d402880c0c0c0840050022100b440d4041a4403801c9258400c12440e80c0f140304442480c40807e41555022a610101c010404040001a5215103038064101a0300c0c20b442e01d201c003880b41c1e000c080740240f1441608000000c0d414039101d10300b0710b0300c02400204a54100890741e15518150b4050040400b07032035107040c404000058001c1c1004481310040d015031002542c001081c0d58201194001c4170000e40c01030112039010006130329002d19429280e00d1185001411300b1038401f2200c80c0c03d401540b2a007000080d107a02c43c05071440c02030031003248e200c2c500002440d024244050715021320312218240307007110741d0046100954002d0740c0400c550010700500002e0307420b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 377717841 1250 377716591 377716607
    0x1006170c0d11040b0c0106050405100302120c0612160f02120901020312040605011a03010f06080408130e011a13060f12090c03020a1205060a021e03090312010510051603 74
    0x9442d5007202080020360344902101914441011000a020f000e4a0b002030104498003210070300c80141c540356042015003005540584441c401c41c00b0f440030a017521000c0740170f40e4401c005030300d940804c2e10308011180c041160519209080743c50014008500e8400c000d5944000c0c5c44021244800003d1a00d103507802081280c40000f030190714420249401c1c108034005200074070460712a80301010b0030202c95018442103e0580e141c07140030541403414868100ca080e20014000c441d103000410104003c0400d034000d207401400f02c11940c0032a9814840c2c9420080b00045114443c00001d01076070707241848107200d02c0251141842c04c100240808001181c00c01c011000000c5c3c12480d0240400600084401c8441030320b000342d4584a04503582c000902c0003c4003d4ac02408030340185c804a101502d881d0003c000341c4504850b91341e0351001d80b22065044d54400c3c0c800b0341c116030001440040000b002602c15005200807030300325420202424010380b00741714242180d404008102d0703d0300c080500803054 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 377719091 1250 377717841 377717861
    0x303030e100f020a0206070c200f03030d061806050a0e25020313060f02031210050a060305060f0306060603070f050d02160b0f060f040506060d0c0203031006170c0d 72
    0x103000d9500b1001c245030083d0700c00080c880050113101c0001e611580240d03400c10045038030000c405648a482c0707403c080d440211401c0c240d8844501c804041c00f541d4100060f00700c0d412041c800159692800600072200000458010032280c101042081290742e500a490f0841d8076a40403803c0e40d68070440704812a4050000c08060001410340002e02c4941c00000390040c2607000c502001503030f4440c0c0d41541e034070b0594850b210059000b00702040b0740341c0880f4541034002d01e200200f07903219130300c0720006100100c40390030500000f5a91000c0048a20705800722441042059000d00128245500800e030544002002142402562059644620720900480d103108586041c1107442d282c841c01404c0321a0049102540c80d900400081440642c0da025254040c041c0201049101c15500c010321000d000024011580700d981840290002c0d0581d0007043d201014580c059552490181c00c81c0801c060550131040c104080322414104514403800c0c5281c124507900d00301512014904010b601516119030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377720341 1250 377719091 377719123
    0x110a0b0c070609140607210218370b030106051c0c0c03020618030d0b0d02181803030903030a052a0d200a0c0503040f12150203100303030e 61
    0xc070f003c080c40000d411007130840e0400c80c15581c81d03444004044401c06000c2c08924044840e0380681c0311240360b160300400682440401e005091004d80d800100b8040c09004c0d103131100300003240794101c0392290700c1c0314800f81048070b94404891400e0058032912408140980740c2440800280d10b100c805c010000003109040e00c54003031090744040740000b030580d420420120050320910011580c017011b40381380f0401000c40c0e88019070401f40b07148286070203031000d002c03042d4102e6102030180001d600c0314041803440c9241c80c0d51100460410030440c043d03030602034a4001d1345030414814040703061004001c807038101c1c032041408180e40d03c8101640d411207110580c0640705819188044424030440c00251244118003a0200303c618080b501204600395401104c600e880760400c10500350368002c02c000b151481c010303000c4909207070303c65200403011007581c2c1180e07110311003099080007000380411480d03905044409003903085040422008442b070340540070080c28152940f501c001c06000401c00c038105108854 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377721591 1250 377720341 377720351
    0x3081e074206050108070221030c1b06090c0d030c1b1203020d020f210304050c090907091802130e0321090606030f1b04020403060e06090d110a0b0c0706 67
    0x1880c0700e0020140c501c00e035400b1825160003d00d0007030011171642002000d2084110008800f0155600c050380300620303a841500301445031004e88403001d0641864000d045000740014102568003074038000d044031120303114820360000540041e0380310000d10a03c1f5400509101c80c8070011003182c02d5048a504096105d0400140c0301052582c00200d40c00c1c881855001d90314a00001d903600340d111410b9010607826201981c0c414040a8007800080d0b510a0180d416038030130115040010f41c040074203a9000711648e01c6110188130804542c801c4c2d0f560030304e18811044551080703901040c61000342d68031141d6a50781e00c15500c0d44044007881125012181d03401101c20710141c2030780e203100c5c182c4240c2c0c00030b070548640d0b000500c290070000f850124a4060300020300018a45010f010b60301d00304038001c1d43e001074003408000009201c1e400340c14031040108014080c0c618003401c40c1494085484010001c0107495804003244030408203400000c29003081a208985d81d454000444921480d44000c107100d1a05d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377722841 1250 377721591 377721713
    0x2030121170309010b0901080c1c0807050f0a030906050a1e09150507051e0a15090203060c04031203110a110c061615050c041401020a0c03081e07 64
    0x40d07020080700b6000319407100441c1d0b251b0072055135038105c5275035280e0843c181a0404651740004c110315840345118900300c5241c1121550b4460801da12901503007081c0d44020344450406030041d2031000a441580741a03410800b9001c0010309800b103d024081981381c0440021450030321070714107903010308150f1209508004210a0042c8654000102902c0758040d0200008100911200300051500c07a81e005240380700700c070f88a40040782c403294641c2400075580c250660041c3c40501003603120305045c00d00c3e80d03207541c99420615141954800024201480e2400d00248203901c5000c0c0ca4003550b0628150000c00d0046035503600d008121140075a0021010551410004140c0060920b00f4480c040d84600c1d0560f401c02074040c0c0d00c0076601c0244a14083c4010710440755040d10b0a100303600144111105e00d201522941030b8145250400d03524500d000405451130703008030061501013204c8124003460040561102c81300c411950f0650400c2c142402c800c580c400c44441072009450750210f50200c100241 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377724091 1250 377722841 377722843
    0x108010b0a170c090307050901030b0c251a060d030909050a0b0604080304060f05250c030204020706050a05060307030503031909120e0114030c0a080711030414120102030121170309 79
    0x2e850b90174420704c07038810085120700f00042c02d80d0480f944181d0100c580d880d55800090550064207010004460300c58031072a07010701801c81509098000c0d620280d00c45280c001030744080000074001401102800902ca00095000c2285402c5800981c00003403a602c4588030f000c068450750150550202000c6408074035011301000030412120aa240e03680086407503403003600c0500078805c03010304444d403103500048a841e49070350702816103128541680601d5120360025049800c20403003640c91958407010403d941140d40704480e081542100142810b034030b5607071869900c1c413000780b200b580341030012592540400c0540000108540c8404614030000c0781000c000c00c0c1c030380300042881c0010a440c22000c0c8031074901080303034050090322200340d03c1e09208403c02d4482000c09032801040201c40748254012030310602c0030340050310203049036040000c0c07a1000c001801c1c142407007081042c0d00c104010052890703007a04002c0089469010104107500500706811150007541001d124000e00204103c09010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377725341 1250 377724091 377724097
    0x1060f091506120b010e04020307030209040c110c0103020702040e030f0a080a0614062a070501080901050705090d05071e060f02010b03120d110d0e0d0309020108010b0a170c 76
    0x2248000c00c01644141440c10001081d8810440821030300305103894490a10341104241c900c06041140441511402240032644100c401c0c10000b40d002c01e802613030345003078011841d0040c2d6610700f000810151040079611813031071a4a450502da4001280811500c417a0007800340040b850043c0c03500c460348142001400c0c0d00000400001541110004400c0021407080e00262030b9203400003608400000f0a12a0b554001031001d11212a070455183d200035084c90fa082c080e0602d8806022424501070001d0310820700a40304019a07414002089013455004060b100c00140c201c41c0c425030058141001e90030320909400020b000016046841c442540b010080c2080303400a80d02c5501c40c0345007150890886021a90701907154100d04041c650100e505800744c1245804090000303081c08036500b4041c000e41c0b18900c1c07001690786403031102c50300319018048800a445130781070510402c011760740001c0c410b1005003d025102c00c0c001c91142d14191054405101340c5100d03403e05021401c1080009074107030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377726591 1250 377725341 377725349
    0x180114070203030f0a051303050d0b09011514071106070c030611030f060f2809090609051501030f0b1905101502070803041a1224060a0c03030506011101060f 69
    0x5644da801142001e915845118030629012103025101c0b65076550440e08c0394080801d10b10402d84800b010180c55640500d014024041015801ca0800072010003404004080d50315588000081c1b200402103101011340208529045810582e24800c0c3d1500740c214041d10340010341a41d24000e801e420100d8018001c1d030080b1080602c0c05420f07510708040010030000d0200c0190448044902940c401100d02d02782c43d602120a0080000d180d102e42c146012a454050240e68254403039114800340a024894030000c80007125a28041d507056403a5440300c0c9194203802002d82190000040301c0c2c2c074010440310030f003001803c003d1206003040072030043c2121003401880000130420a401c40c0300790000030303500704462814014604103868000b0400740120304c042c950034800700030804040080c0281200e507100381c1d69242400c50140c518542462003110000c1000e020f41420442e044619400420500d1016414500441c85a0b2550300485441c0303007115040d42e10758203010010484401c1070b59030800359 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377727841 1250 377726591 377726611
    0xa0b250f110402280306080a081c09030219030507060e030706051f1e0302330a080408030a0e010507050a110109020d0221030a030e0f0609030318011407020303 70
    0x6200c2101000220b01c01e1303180d99014529409100084503140140c600240306050500040c019a25229542849a10742c011100c0c0c20340050350660025800e9050084903c110100300800c15043c0c0c1c019541d455184138000901c3e61443e000d0741094810000c490180e0b5000e1010701002c2c458404c040d80d01d4101c032508907003082c204400643c860794a15050302e80c5000741d40d103452403d441d10b0b480c0e40c00c03d041001107160340c295800c0c0c0880035071100015500286156003120701022080341c03490900d103440828001e10f084040000441040d44030319260b4000c1e80000b801a500d071110034580000b07114007030340d030415035090030700b04008141c104025081004244e2204104180c84403502801c030348250310025400b0842c05403038009400d1540c40070520444400c1d218191407201030001f0b00d150404c00700d10340001d0721241c41a1004009010351020310407040014a180e007407002c2019142d00000b0403244980e03150100801d440c150035080749a1043d040031072404141040100203440340d008940082c06 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377729091 1250 377727841 377727863
    0x61f26031303051c050d0c0908060f060102060c0f0a030c120e0d0201140609011412011a01140304030e0616020a0f05040b0a1d04020f10020d08150a0b250f 68
    0x1642d040d40321120405a481c5c2d0300d1519050060342c02000078541581c4442c100f003042c2c8000318448104100702c40c000d0b000c00403404c905140a600080c42d0240c01001c146062a041c40307600102501c0c0c03000c0d11600000c60402080c121043c0070201c503401d040f040d88005140c10b040311224687c0010a1480c55030140740d009115806000c600300e40000001d641050b00f100c0c8200040080000b4202c0d00e102d060300c01007040c1550382d548401c90b400e40c0c0d22405150712078510307800140f0342580c0000901c4d421000340130301c041c11443c2940740503089030a0134003458010500010000380500d024010f0380c02d01030b4018020b4020340e4503119030071601e114a000b010700444c5008404925890a003c4a0048580c0c50b1004100d8110800c406060054040c004a030410801e2021815541d20824002c1c0694034030760041038076081480c001042090098405100a081c070100301c0c0f2640c036846583c4042d50348030654180d071000018440308844072503c55103520601d1038102c800170408054070f180c02040c0200a0000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377730341 1250 377729091 377729113
    0x20a1704030c141b06030411060408030d1a090433140106020109050607050d060b030106021c110c1c050d090812030c0d150b0f0705061f2603130305 65
    0x10755136406242c5041510303103901d40c0c265107282000007154000d200c2e20001180303100c02e10104580e50403e0300080d080760808242100c00e51f50502c10700c0e000380180c0c1c0107294a00c5801000c40c80980c40900040c004031800680d028482d410540314416481c15034010210101c52203010500509078020440c48984094000003682c0b841402501d03074858100d800340103030340c413a83c400340c59982c04400341c1c802050322000700090300704460b030183d402400309030043d06a840c2c0d41000c2c00515a0f6001191050101043d900c00c1c0400000480d54a0903509030b40d00c00c409076030310900a1024a040c003004055100d00d0740b810b201c1070740c040b255100b02c501c26001c841680d032407a185c3c688280804c940003d8004000e004040c4c1c0c800702d0380c1101089103072040514245030b44460401702e07130383d1007603054007030000001903074070100030013001566400101510806100c440032508803001e182103208024284e80401c500540d81c0103140416441c031030030a8201ca56401c03044e49002c5411001c0d02c01500c0340d014103800c0030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377731591 1250 377730341 377730343
    0x7020c030f0309090711070513050105042018030a120c0b01080604110607030512040305040f0b030606030103032a11010801090507020c10020c03060a0b0a05060a050706020a1704030c14 81
    0x100c40010042c151340c0f141e600c0312000ca40764074020039542030b40d10aa450004054a640c071481000b40a052408511503050006100c2a9500c521a10b1084409085c002ca09549600c044c0d51144910806101007022010002440d10000d1680a0000c0a00000074503c0d20703084442616800d21400c008540760b80d035a0107158896004a1b000340a850300600c030407915207003190042c0314041c0300341841410042c0c44241948058000c4a084012440002e0103108003080d603d5210018100301560525601c0c188010a01c64003061000500b80941080c40c0c601c2d02d000900e441c2c421891121701c1001b0b07103001c0d08003c081700c55042449404a00150700124100401c0d000795441145c442d00201a01c0e07603800284840c07d1018800c400850042c2c0e41001540d54003400041d0140d002101c0200306050001d0400041100d0b075840741d41326200400c00400103507004800c0d903110719001980181c5804854006584508112048006c40c014a204000405030410035020030307103000384890800711401e043c0031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377732841 1250 377731591 377731597
    0x90f06030b160f0c0228090608010b030a020913080703050d050c04080d12020d020d05041205070309030b0c09060403081201050a1202190f0308210705041e080607020c030f03 76
    0x44400101c0b0807091a030f44a025280c10710025101410210000000348001c00e00c110b1000c01229203028100c00410840d4403034040c003409004550002c0085c814580006a52802c9151009004d40c0308140016100c14a10040b80c6007030340c0000c4056070380d103114034006045500c48024140701516010214a41c01883c400b510181c1c0c9d2401c0044c200b1000c50300302910824148013446041c150204205280c8940034006000814040f110201e89806c143c80c02c010000c0b0480809010010240000c2c000b2070360041c20b039011650410b000e013070543c80703010b4050f00a1065525080e0801ca00090000401c01d040c1c0050884a85001620030181d899204024103040e41e4840d0b6068480d103407840700c01518240d00c841c1c801451500e10402c000b035890f01d401071b0500807940305503101c21010641c1800e0042c03040010034251110b82c1c074070025180c1928058058003890003588400742e00740b003c0c540400c004001c8080907155203000c807007252412480096460b528540c03043c0c001d0203400c5040c60301c2c840000036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377734091 1250 377732841 377732881
    0xd120603150203042f0a0504090c0506030702030702100504090f0e2109030f070e28020724051008070b0307081b030a021b0f0a020103020a09090f06030b 67
    0x451416444096016406500044c1083d41d2a05c17074404150b45a072114250450803c00c102c481e1449410300318100030454440d503000b280513906003040d903000602154902d4007175a608030f400e10b40303a0f2034204040f46907000385000250003243e2110b0074001e05405c91b02030700440359052418005495590b07103201c2552195010303a211588208118040341160416103494035161155513810321254078000f07460012885080a095001080103000c45c2805407133156010140141207003030042c03006003a0080036403081d000010180c0c0410a88108421000342c41e8050040c95074100f80c2054002d0300d81c0041006450fa642c41d0b4180d444005641900482c1d80c400300d1b03014212590540d5038007030094400042c000c00598401c440b030005414060032507009180140e0f921800140c540c03c88116841044442c05034151082e4448074485034492400190b5100c11903081c40c0c003503143d2100800903503010605401c0445128104070342c00484183d0f1782d000608503806500e42d05420748486101220605407600c0c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377735341 1250 377734091 377734103
    0xb0f06060a0905010305070e0904060203060301051e0f0c0f0307020105060a140904060b0402040b04030f0209010905060f2407030215060604030816050a02060d0e010e03030c0720040e0d120603 84
    0x202000a0341c046e6000c00d074170900d10b01b46a0410040c8000040c1d130f020040747d08859182c0c2c084140712090a003440f4050348080e9040740d80e04108a414008030031030741c0c01032420742c05110301c00000703605407120030a454401001c812007580340d0a0240c8040c0c00780008440c0300e0301440c23040e0800102100d0202061060000c09400236203586c903070780c84090141400e00345064006800700400180a04401c000703200650040485020940300e920401074503160603840b08913014100b9051001c2e0b035440704090801e42d2411160303041e1950084824902152100034100005040815040203058010603500c1e18040301296001031540c2c0c50381001502c1c0100e000103000360400340020040c1e441500f5442c00054001d004440d101d00241d400243c0f1903020f00e4140c48255150b440c1034014000901400c1d4040741000050760071132a007082464082e00072810051708500c80441454128141c0c103505d20788101000d00103112a6a000d01c0c110341d0f039240c40c51400300040206a80511042242c4039810a1702d030710003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377736591 1250 377735341 377735357
    0xa031a090a0f1a07050f0f0706020c030705150f06010801090c0201090b010f0603050f070912080405040204030c030b1b0a050a1404030305070b0106020a0f08030c090405270312061203040801090b0f06060a 89
    0x8581f42100317070040e040458035540c1c00c000040320f8040c00c10241001c1171144004240da03000710644c12041c40c03000303003200e03030061008024000103a030043c10003410368a07503510009005003e1301f012030142580c20009886001c03e0750010910140602045003a1019500c09120a440d0900c003112100802c88483d40020f40000060000c4000210b802c2070260040061f18285512000094101e03400342e4011140f102042c5020001c0101b1484495440902c1d00700c501c9420242d1101000680315049250003007010000352400400e00842c002400c1c00c074064a0103032959180d19000d02107520039541640c1c509a03000c00010703150710001d15042c045500009441d50f00d4001da0350700c219508003420002c2c00500a000000e000e071030754483e05228541d00304040f1080800403806003a0f10480118002540d00100f045012984852100c2900224140c070810703018007040d43c105055001d6500b00600325403e2070589010300003050b10b05406100e91440500307542c0c8549041000c2445500100804a02c642e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377737841 1250 377736591 377736607
    0x31415090601030209060102070801020c03030402041a1e150d0e0f0d09270507020a0b01051818120c0102090a0e0112140f1006090b0a031a090a0f1a07050f 68
    0x100c5d031540c1254047c0111802a900ca640032400e9820403205104550b1011040009503d4140202c218000702c3e801c0d000100911040403803000c190200c202e114020741107010300e2154a880c01381c03007010004029829200c40c10703100100050001854000c00e40c0c0b0401481451401000c50f02ea640d990880e142c4450192410142038000e188020582030310701d9401c5d00c45d10803803803c0d004440c80f034042d55014052128075480d00f0b81c0c074850b060308070307a020b54601c0f83c0007040f6000310020240c005031800a10000f0031080c14500b440c0101d0310403c1050368101080c070748000c4405402801e120308085820041c2c55488100d07003102e12600340319038101e80d03401c0c91075070002c61035034a888102e8800038402d80b20001c084900e00d41c5031840140160610175910582008541140c1c8100e280c41c101c12502600c21902d5903c40b60f04035158815178070050380040c00071801c2c52200b0002c11514a603c000c200c0300840d0319090200c03412011600d03000c1075507070304000030340c030a8031410071240c1f2030004480c0b1130b082c6501 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377739091 1250 377737841 377737849
    0x6060406030b04230403090e0702030906090a030c0b1803190f05011b0f08060312041502031201090c0206070c05030a0e030307050303010902040f0603060302060a030504020607020405010314150906010302 89
    0x4840c8940760010380e6070205203464841d1140244c441c100f03403002c881560519107001026150320368070001da40d140f81403d00040542c08822580c00210444140b51501403260008000d0380195000805400f07006800203440007016020704901c0c0070303440310725000c1c0c0c190b5414180c4030b00440710000840140c4400300400034000c20386407a6070758014800050701d5940365100c401549058403000d4081001e0103040140950320850080d8045020b0f03000d00b2a109a12100d100305000318001c041c0211051154034498600c2082900c0d48590b2598900c90f4559481c1c504100a01a00c21818014082d44002988441c000d614003580958450010b44c40c00c601c400d01164199200c034440340d4940400c000750000b050f000c2000d54041c0c948140b00603540c0d8074081841d090341100d9404441890308240080001d0b940300d1054070b5010805040119041d070319840000c01c148941400254420325040000c402c0c400b00c021640e0048a20b80708031000c05456580140c00c0e281c046402090641c4910014401410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377740341 1250 377739091 377739101
    0x90f060804050a150b1e0d03050c030d090c030b1501140a02190b060306070807050307031d010c030608070906051c0203010209030307060e16060e010806030c10020a020f090606040603 80
    0x406032041e9040700c6000d9840c02d00d0303280c0c8130a901c0c2025850341c5003178407a407400364040c800320902031684144000301c420105803881705040002c0c090201c040351130f4585040c103100b00c030001030541c4405c001050042ca010000c1d5402400b05a80f0701d1109000100100b142241d1540704c000140c50f25000b29078041a5217442e503108070000c2045000300c1c126503100340e04680c400010f0610907801d0310168503080c400e040c909800248030a042054680c00c1c8544540c01c802260f4104203c0c0c500072aa0b0003130381f188150186008002d41d5029844e04440c40c843c03c0d41544041c041d500e051054070410303039441180c1c07025a0303034078003400f5030007101f04000c400e2032a40500c03880324003440035001508040301440040d0a5401c00c50040d1030480d101e2115403000d4400f402000d0241002d41c090091050070070b40001c00c0c010700c59401d2410300034400003294660f541005000103590340144139801003031000384000c0d00c0d0480102c080340250040142c3c4451854020700951141d400940903a04003464080d040780500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377741591 1250 377740341 377740343
    0x1207030c0c12050f0d061503060b0f030a0b0a150f091d0a0b0901080708010b010503160305090f010c020309041d061614070c05100804050606060a0504080328090f060804 74
    0x8030401018081015440160020600360000000c6c114504140c0c55011941c0400d418101860100240300d0700c0740c0c4005079140500d0803031545480c0e98548146100a04100341855482040c112000a408015407c40200e034545075580c40301990148006807460074180c02560201c0c4010002400c200c4c0400c40182d910444201000c980c644460000c1404c440e02a00880c141e0340010b9001d200300d081c00d0050400114081c600b0324034500d040ca0407940c1c0f48901e44003a108041d00c2c2d0010a021035401c12040c400000000001c000d5010314550280d5039074000a9074a01860401102d44030000000808850103060000030303025035a81c03d90250f08030090600d030350041c40000404c1c1080b010384030018040107807180e600d190038141800f04001611811110030010003015000b040f00048020840030740016090741c01d1074a404021380103039400d0059400405080c0720103d01e0880201c00c0d401c400399901000d8002820b500d40760794040392075145e240648554030700e0070341e0108040303449000c0c002c2d801 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377742841 1250 377741591 377741597
    0xa02030d111204030503091e01050301051522090c021504030813050a0507090b190608130602121006021b09061302070f020a171c0c171207030c0c12 65
    0x400307950355802582d600b00e5001034800d540041060354880c1004020003c10400a91511002c0078521000030002e2105004060042701400e02110070740d100781c8151078580182c010120340102110b4807440c4806070354405e202d101c604200d20141e6807400030856075181041d42c030a01500d036503282c406854401000e0900c08011a6000d5008041501405a103031214407500103042a01d24100036441030f5002c0015280c4500d80d8a07000b050365030a528980e000b141c0041c145109695212520000e240e26803c6004d1b20301030000922444a20840b401c0521a00c410892190690384426089958803031301c0720200040500ca0116941600c1c2c43d401050f0311041c010032281e1414030306040c02e001d0303800c008001c9031001d00312501d90046290141c5044058500045038108894020a52940c0c8000300310303890000e01204481c01d0300702ca00c5501103a03003254008403004c0811031041103016840d840400c8510907003540201040c00ba038828040c0da25041c81c0c5585964406034141ca9040454062004050074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377744091 1250 377742841 377742853
    0x40518061f05060d090c050a06021c091a21090712020d080f0a0f02030c0d20030c0604050606010320090301060e0a02091305060a0308030a0b0901030803040201020c030a02030d11 78
    0x469680500500d003540008134003090b00b05141c603045400c007003030741c208074401d14001900303101c055800129400342e007211008007200181541d1051342c030304002d074120890704404031080d094500f201c080200b094080b1195011942c0c000e15554000044082e601900c0d0358010303030303010030088040403241e45606000810001e1550851ba413488600e511028000042e64004207800140c190480a08030b0400124009540342001e4400d4594441d900740c528103091245000d245000d43c5112140e05801240c54400c90f665589001d85299540404880c00c644920406c0001103480d48030f4084e48801c1300354104540c24400c512203401e03960703800c58001190035641c0c41030001054180c0342242030181108030001680d036071114051140ea1034142844507490344c14402444001d48488505400304c940091740d55489865103590540038011340c0030040e5110381301348004420b1104610045000e541700343c0031540281d08902c01e254881074150806035054200c2c1c00c900031018004c000381c1e0711003002c034019507403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377745341 1250 377744091 377744099
    0x1f080105090403110312012102031e16030308011802040b04030b070e100305071205010b03011214060c031e0622020d0615020115180903030b0d06050402040518061f 72
    0x102e1508821b8100700d6015005004102e42c2c08000150f0707880000e0402c51110448090700441e603101d1440520900d90940d6803002c4038840014010070f41c0400041000c0030303400359a4100144581001e016180c1034140302160000040e1040c42114202c036083c5c00e010341402d01e161a601071801005200d841400190502c108542d5221064010724405989002620f802e180c50001d20542001c0c4400510528000040c4201c0c000d14080d0317811200107032040b0f4209109850040c611075100344004140b880741c402404011072441014500c60b07001c40c40c5640c0310b01d00e40d280d013030000071081d900283c04c000c88000725030403041d810207a070b83c9032000c0d62009443c0503840c900c1a01104d103da0712040c450707071100901c946e000c0d5080c042e14424003440781e002d03104a42440159466441c600036a034424956071101041014000d130840c024102c001464a10050484d00b08500901821903040344124034080001d00e0217100c0c200c8044800400c04001d00325070382c078601f41701d09088201030383c843c400740c10304c200203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377746591 1250 377745341 377745343
    0xc15020c06011403031606090305070b2e050609010c020f03030a09080f0a120806011205070509011103030114010815040903121a152107020c1f08010509040311 70
    0x31400103040c40c0244402e41c0741222940116036080b1129100e500100b05030400f0b010768041d400c1d52150401c01c00912000c00d031409603014816100010842510341c01001b034200032078020020030079507500c260400c410310004c50f4510550303079014095018601340010101c552042684204442c4050508550350035840000b07469500711040c0b841c00615050000d10030381006228044035825284003c00140031a540c40351a0346900528400412000c100020071300c0e8425811a290400d52580c200200d0600301e60040941d4415401a4007060810480139060301d400003c41c0c1c1284d041e40e20ba104a800100c004441c0d240c1c01522061441d4110b600780001a6140e205480701c19100b6103401a000c0ea00311241c206447c100d40c02e180580908101c1420980c81d606040c06040307407510300007030f0b642e010708000e2040c603011004c480000c4045201002461500001d40056418048500660041413040390503600c0c028089403a00043c04800100814213108180742e400c030744641442e2501d0407080d0001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377747841 1250 377746591 377746597
    0xd200301060932070c0f0c0603050906070f0e130b0303130e09010b060a03020c01020c0105090d1d0604031730060108040b07320a0306080a03020d0c1502 67
    0x4902c0e00c3d0355007034080061501e000038842c011194107800c0c0b5031040c94103045200348600510340814021036680c842d04000d00e85c965601c4843e40f20b403042c90044c0d2036a00080c001c0c80101d98140141c49410045030306a401030b100c644003008540d480008024042080c422078102110102c48038907103480711200a85e4050000d888940031004404603203c0c9000c440854240b00544400300d40d92600c0e0000040d0b450b80030440b05c0c003c116013009039441c225400714500911600c4010741e015440d01040c0035502001052540312008581c0c0e441c0400d0b48007000041311200208503456114400304010000101d1913040ca82481c0c011044103401c1400561542a0042088130041c3d13980000c3d14100180000341c41350107402480038038000915203007903507030340d600a90054085410711030b40c007481c4502103142c1080300c4001103580d174031003207542c903040c200c581c0c180c2025019201183c01e0000106032040e000030030407142c54156000300101c1070560f0055410704c40c4450166601d110f00c0780c52046410481c002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377749091 1250 377747841 377747849
    0x130b0720060c0a060c09061d0108130609030804111c0210031b050c010c08060d110f030d0e03100b0a0909030314011212091805090304030b040516080c0d20030106 71
    0x80171450140d0140014154405071b0001414000031084641140110b071400d032080781402e0a02d0382103911a04140c03801c0500b8054001c20403130610700c20340c040507400590700c0e008070b21a00700005901008801c00c02c0200342881c0d100514051908035402600d41083d00c449580c07094100059440141414040c40366040448500810000076402840c010309104170800041d5611b050405400c0100008000342900312000e80b105c1c0c1d100702c400c1c2c0301c0d665826803000c012900400b21100c020062101400b92110b00c80400e200c1d001e03605200071448030034099003880f240e009003012001400d24190f400207009000065041664a680d4610202070691002d0b020b408421305201e204d003aa450614000c10480c942c00c01001201d0b07504004020703c0440071645142825000300b110366034080c05624600580e032014242d002601c2c2444144000410326400b252849141c2d42055500c0f4218140c2e41c6041c0d00e040390b04003441c100b00b40d01081c8844030020040807100c8003540860040d5000038290b400d0303508 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377750341 1250 377749091 377749103
    0x6071e0f0b040b0702281a07090302090f0108060606031f170f01060e0c091201020703030b09100b1206010e090a0519060302030d080c07080708130b0720060c0a 70
    0x4140000d008030703c40460303400390940c8028402c1d0000d48507903c0b081c0e03511000071041c00c44a69034407010041c0c050f002e03215160403031452507102e18002900034441412840140e00a40c06203000c40d9000c82d810a8050581d1140da0085c031494031040c00f400f2180d072005218840d9140000c481040312008481d800c0010030520007c0180e5603114004c2c22f05042d441803003940c1030780c17601e0410404031080c1e1076015885400030340c01c1510340c0e82c40404180c180c03000414200710740d480002d0a05c2010703015131061031000c01c180e42e401103503500c2c0002010526201d0060119051040c001c0c06a40031212030382a0b4008010b147c01d000030003841c00460800b18050f181034608540fa2403c110800020802290000340103603024000c1920315008a0b468400318180300c000c00c4401e40004201c615a60b0888241560141c0b95551316603aa08007a9002d07040181c1407103020414050008a9a031440c00b501c400c00e8000d031b8540c900b03007000715180605110000704503412034401e2180c0c13256aa424003807050100e000704 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377751591 1250 377750341 377750363
    0xc060501081c050304020d0b0c07140a121d04182f0f0105070f080f160302070e0606030f1005190f050a0b120606070c0303030c090b0906071e0f 63
    0x1498200c2c44844040480c41005020300c200130159a49800f5a800c0c140c00920082ca142c86520ba002424400c401001d01b0b000407028218041c80ca00013161a54280240c4a5414007801e29600702ca490305009840c7d41d003c61613a0102c540c61406030b100030300c2c94a246000c0706400d40c19540325013982d401e41110003484502d40ca00703601031181072580c0c8544a03400315801c001c2d2601c800000780079070040004c060820860907950070300f0060f12008a49801c3c110300c1c1001d854440500b000c21351400301c94001c41c014001d2070b8000031900d051140d5640130b13a0000304003030708580e9001c0d240500041c0c006c0c6011030a43e5003c10000d410b80742c0030101101008071401444426081110b030145000560b80080d000c3c150101c0108140b1900b101074a107024002d00e1068031075100e480c005031560040302030191070520b21401c0082016010780c0041000c0c2b00791384620071030583c3d0b10024507a81c010191191f800c5603081041d0400564170b01c2c6002c0c1805030544880c00f580d200350700ca083d11103456510440b1014888 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377752841 1250 377751591 377751613
    0x5100302100806011d0a1710050c0316170a09050115060306090614031905150c120708091905101107051e071a19080601030b0d081204030c06050108 65
    0x1039030f20322020200036480c1c1c07032a40c00002003004031166200768400c1f40304c2c0c10700400c0001c0051005103400070180000744603a06203203040c90030b150710940702c24000d040001603030300d03400303000b044100400702c40310581c4005d0741e0380c507520799026200700603080b034070781d507031031004485959014a692018019554002036103078101a180412117200d81c0000c50116044088030210346c1d400669209410601d09550240c03540914110740b9000703110400e001841005401c020f011984400506501d9400080710030b125122994146d864105c140c0c0d00144540220b015480741580b082c07203802078548980e08603648000d0140c00213048449040ca40780e804071000440e5400e11074100142d0a98400c030343c2d106003416034444083c940e9003040344100046690b0a046205400d00c0500541721810b2030200c0c2107810700000d101c001d103120800c42d0040e021920707014508985083c000b0030702403080c2e80039460900d41090015000d04400b00184100e00700a82215410006500c6005203170003009110020100c007051 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377754091 1250 377752841 377752847
    0x6030a0507090b03010c03110702010e0a0b0d02030f1f051207080a08040e0105010237020301021204060e0a030504030605062806022404030819060303270602100510030210080601 78
    0x110002a10405083c03035142010200020704885e160750742403c05070b401210583c0810b8140744107901403108000c2c0400d201c4fc640310103400442c880e506c01d810a8565688a07044140c0240d00c0844809030041c804905004e90b0401c0c2c0c049003201201310081f00c0c00c0681d1407140d00c0c9404043c02c8111420400840d00304222007040c3c000501520007400078003944490703100c803240028440b071007000e022071032054007103002c0304c4404c03821210a4011b4001d6503510302c01c2d0700168078940103980c05c2721800d190842149025202050070004554103564403480c162070340d1140c40241c02c0181103554800030501400720034030320540c103503403a07030442c007040c038400c1031814070301a040c901404c0e0354000004c001071481520781404102c131a40725a050411040c561940a0f1039105094000d164030840c6103010303400300501d900014900c3d0000311410700380f800245a82c080c82c81081c1144121400340e44035912164004625802c65a840011040841f500c259641c001030030200c100101e00b8042881e450070300a103568 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377755341 1250 377754091 377754101
    0x3031512120201110324090708060316060f111203040f030e030606130e0a081b010e01090308040320011103060915090105060a0504030f0c060809190b06030a0507090b0301 75
    0x7000340000c01890072080c0c80d8603103503c4010001608450300001d0600784000d0380c0c4802070807280160040e056841c006d98003038450788003a03e03070a10904c80c040d01c60001c02541000c120035551507546100c205124040e060710300000c0d103005010140510071224004c16043c0c0042e510440c003c0161000703020341740c04c0c00751081081c820442d010b5000001085050748a6200d260b007081a04a80012840540441c0c41e040180c8018010300d01c3c0340020300c0c41442501448968400c0d04500004c000703001115048500f01c1e003a800e03004011601d21000240820302030350042540340f10100c00000310b18000c140a9003103403200450150340101c04001d02060b070800c02e00f4907521040319203d40d105042c02c030000400d43d070380520a40d44601800540300030014480c1099800440e4804542c0c20350303403140d2034181b010104038000e5400184000d03000039017803e0b00148201c05d041022040a0740035000341c4405d0b2080b40020b11094043c0320701010307440041c0003040440000e052140001844200000402d42501d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377756591 1250 377755341 377755373
    0xb04020910060206131104060f14040204030b152403040b150114090607080706050103020f0616080904021209010606080c0a090b0a0e0303070638040903031512 70
    0x1108060007030006a03000a1302d2600a03400e100a0f0b00190040e1403c00c0c180703600c800103650043c0c01e20400168482036090b08c181a079900d0502548802103010501c8100e000324480940750080ea000818256001c21109416100025102107d00307160300a18000c0d040364021880b034020000410003040c00441150140c0151543e0420b18080000c030740024801101010301c140103540c0042e8011256440c1c40840e0300080d84a41d0700c90315035101d0f040c05c2008020034801139014540303020807240a4600001126030064160900b0102b46e010303619026880c0d0440c2d802560459400c205400d440d1800441d0513218050176000424100d042140007442d500000d0909120840103000c50103d4542145041043c0c59021000507194485444126490305600c20f080307800d0b010019401082c00142e401c1182400810102007001b0f158511104814604030100c1c606505c88110103c58180342940003e26250700901d0701180e000d04c124141068401540e000555110b94580030000308a4280c072500c8000c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377757841 1250 377756591 377756611
    0x3050709061203080619180b01050a020a0303020a0e060d0c020f011e0b03150103030f02070f0e01050906040f020406020f280b090708010f020c0c0a032a030506040b040209 75
    0x15519040101403000b0116000a05200d030720030002d031103500c58032242000c0590722180c2c10150790f5590548015a80000041c140c482d081016103048e55003e0011200522080d90041c03406140741e8800b00d0082d00a46a0300041004019000c1001e950b40d0380170740a1039012801c002451842c0392030107440c000300b8514002d5182d04010f0301c140b5000c5000341c0200d8007264a14003181c40e074440c0001130300300310840f80c500d1000c140520020080c59070100c0c164065000980032107102a44036030603880d14404c540310740044e81502d20010700080c2418840c442e0444005400800c0c000301e0201c08030705a070010b030403220041e4000104041044010848002107544005001201280d90281d9440109244c000a005440c040b004901180e00420200d8000d103d100b000b0840c0c02c1040c1c0d07400d0080e5001e841510b000f0b11914108080b00c0c50800c09040449034044107040381c1d9500864450101e03205c00050101d0500d4600d400408510b091000c244568820120405035103030a01c108000c1c0000600a0204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377759091 1250 377757841 377757851
    0x1009051f080a1118040609140405070e191e0c020f0c1e0906120118020a0b2d07020a080106030308090a0503030106030f0906140a0e0c09060609190303050403050709 72
    0x2083da00c08088071070004d40c400d03001380f0302d40074540468003134110b580c808801c461510000d0800d41a0043e40d042c0030302d104106948003a0781e24031003811140300035200e074949465080a40c1c1032000340d50b8801501c19400440008000001030420b4040300c000a50040248c0c10070030101480700c01c24811806a00011101098250040c0303c811950302c51031f450741800741c07400202007403813030b42c2c2da07101c100306903840e2402848000030701c0039003031252000104200d000c0c03075080300b012440060b000217403500c4110807031100341d526404a006400d031014445510007000b808000c02d10150300c1d01810040640044000801c0382459850024039002d0001c00123615900311810102c00164084100d84c1142c00d203180214050102120484c000c10603008028150751902179010040e8005445252142030080000c10000e1004810541c0340d400c0703203840782e03400f180c807a0000c1c0c1d603440c1103001740c4000c180241011584400c28504204400280d41081d00420000700b020010043d040220701e002d803c040d481445 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377760341 1250 377759091 377759111
    0x6020c0a1220090a0204090c05070515040c05040f0614040207020102030d0c032a0e1c0b04080c01020f0705010f0c050304060902031219120b010203091009051f080a 72
    0x900c0d8007440c00001c000041e085141203180482d00750201c2c00d560b00070600402e40c280a03640d18001d61251060380c10003400d00c06000042ca01403c00c0d140d4040c1c000c009403429007250000c921300100001c00031245c586405401107095250b034490f1070051142144009545800e2040c443c50307a1490200107849070b4010000580140d9000c000d1b9098000c1d00e04001c00c4140791368405402070300818110030100b0907c0c0032800564000e4040445444889440c1e500300317814408244000c036041981c1c42c2050b00909420ba400168421b1400c170b500900806540d414000045d080c242a42d118006d4507440440104120040c40002e20070244010034000c1c0400640c2807644e8050030a010082000d0451595609000e00b075460038041005908010001c9664a0801c07000b80f030a0120a4500900040e800c1200104a10319520682c00d24041c141c00460800300c030f07241000400b800b115146400c005110100040c00e4882c440040d000c1501000e45003241011804002c1514400130114031780325007030122101d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377761591 1250 377760341 377760359
    0x6010308070b090307150b010e010e060f0f090603010306060f06020604050705040c03020910030c090e060d12020708060f06010f080609010b0c0312040b010e161e111606020c0a 77
    0xea00c00d40c00402d0b00c1c115500d0458407400c50041038000b03401a003401c9202418031000390b0189500c84001d0f01c58012220090307004444821001c00743c1600b01c001080340780900104500030b041c2d03454a90005924290314a40131030b480d0b40081e0f00031606072313850b100e0910200900c2122400500407910050080b4a4161180399540e10544511405155154000384940e0305c2501140d4a43c80058040c801c11075034204d0050013842c80001000000d01045804106800e40c042d00600a0000600095a041c1d00c1e40750b209040c119041810298841c4440c00a01b14506020462003074106240c00c240502c1c00034005400000f1400c292801c00410004100107036540c8090720b419140206000754440400086c811f203075118030741d0848107100d030000802040110000001b03042c2c1d8107251501e04184c49140031402c0c90f6500c0b80405000c503c16541c0d0740c1c06102d49122030000c1082c540341110b240124018014240071700a030080c0481c9600c40000d10030150100003800d0042016aa40c05050340b43c1880c1c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377762841 1250 377761591 377761597
    0x131113051f020a1b0b0c1605060f0403111804050303041523040516180b040b0904140304030b090a0308100605070222050106020a060507020607090509040f050102030709030b060306010308 82
    0x1841d1451801507105031031040c01c190b4000e4503e548065968a418036403071b035520071058400c5040c2410018011a541c20041d0999114003801c3d0340d411304042c110340d41c03100440c00c42031805400c00281d00c50407903152028280203020324040c002031560b80c00c0c90b00380b21241c11680011415407a04101d801400f1415260308003800c40c0c400d10f0a81721a8559141003030400101c805100aa04030544000c0350031032480c0150100b20390607100801c00124000300b40800d4950f2200c06551040d540e03000200403c0060b1101980c051500b01a030345050b0b00d95a0783c03965920180c0b0b0640f4a6809a11510205608904155082010300e20030b009054681907004040d44a80b203c000c0c022585064542c06030003c100100c180030600b0082800b0641e10341100a5841d82c0d0714070159a11818540402c1082c1c0c00865000d003d0803040d81c1c0c2002141c03c040501c4030070000a0001c8407000140c0c40e44102281d020300c040c40c000d200c0d6684090005103141480c00c8100009001c40d44641c1140b401000001ea00c1812 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377764091 1250 377762841 377762843
    0x91404021005090f04020c071701050106090b130f0e0a0506030a0b01060c0807060504030509031b0a170a06050f090706021c0c0f0f051005010e060a05131113051f020a 73
    0x95a41c0c810103808500001c130400600c3d5000b82c000324540a681d01c010400130705403240801e0041e1240700034007586081e070360b0a218080200d503e030203050208003042c100400303100030030080403c0340d59600c080300710078034041c1d0f03200d40b502c8910181405440e0702135000745c5801460440083c0f01c1c60704c46894980c15414184900402d10030300940c10420014103100b544d9010342c0001041150b032070075080140080d032251380380030301c00d0090005804d42d24460001110207807501822002d400c1e03040012188162503241c680390240d114044070394002440f14011188108803000c0b6460071411300620040c54420117400c0001590032110f0118060351078040400c000380e070546440348480d811800c04400400c2c05500c0504041d0400c000a400d001c0f000a92110540c51544200420382c2e0b03940b46600c00c0761041d10308a030b101003442d900304820301c1c1410306491013150341c1400069101210703e04089a6005100d84c0c101212801010081c500d0814802c0c80c01500000c1c00d0481c141000b200251507103035007c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377765341 1250 377764091 377764097
    0x60e060c0d080a0b15040911130b0d0609020c0c0114040501080c07020406170a050709110a03050a02250b0601020a150218120f07081f0e010f06030c0914040210 70
    0x2209000c544e00220f403401c0c0c0c00b5000c0c0c0d811070740c030b00c00303611007503000b80100100c00f41826040e00680c040d0f802181c40c4800c481207540006401d00e01d155403146d100d4026040c449807202c00201d08d001c46440100070110281c00104a4600c05400150a81900c0c540041d00540203010801281c1d8100000c00d600c43c0d502d0040550300c4090f840010b00a0a142d0001c0c200240c4080081d4200440010800b10301801182214901c540e04c070741c60b200755509881e6080c04004c0034003520014034000d402054010600ca440942010300409030071002064030001103094802070305801d414400243c01c0160415400e1014100e80700231502c07503152030703044078841c0020f1903800140c026081014038507200e0301d5640140100b005682c42e01034035a440b0050f004242c8280075041002410040014607030a04011f40c20490002400d280402c00050100f5000d07100d50b035494040e42c2c440c9181508c0368002540c86200c050f440b10382884c803203030122008241000d072110000c0051201680d40c0d14412004442585 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377766591 1250 377765341 377765357
    0x90a1a0909030d02040308030a060e07090b1605061302010306080721060e1002030103140a05060a09050a171209030a170408070c0f09181214120a06060e060c0d 70
    0x14920351443c8100c0c103032541e10070310108000c030800a4500095000d042e800d2801d020054941ca002008101c05072040804100400c80030008110700d82c0c00b42c0740030300b1000351301c2c0220403694a07040c1c140041203485d0000c00ca079000d2020215038052007518040d089050007042c81600b4420b00d404400c0e4001000c00004420075128001c00580d904a0034050300c4030b1040c0d9841c407542e008440080c0d0420b01007202d1a014581801c450305400281c080a02d40c5c1210040c50680c5594442d0001018003090684040c081c000c130380400b042c89090401ca5550000380e01e2945d1b80d4408801000c12500500300c00072036041040b4000e145641f06941d100d1407090182d040c2d44c140c1719480c102000348110711008181c0000648d00243c240e4100d0560760803110001e500b80000505000042c508004182c0005c00c01801558111405480b03108880d0918591035800c41c50010300520f46c204464003100c0000700661900e0301030117003650141100b101400d0503101d5a0520110f0f40d2400e1300c07142180c1e0708504000c004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377767841 1250 377766591 377766601
    0x411060702030f070f030303061508220507030b06041d210c0105090a020f010918020702030102160b0406060b0909070e220b0906010c050607030504020d02040204080c090a1a09 77
    0x18030080d100f00c8a07010480f484141e851121094a44003031009a02082c500a0005a02203602c8040814054103540b18109130b0f0b601e082455002c540200d98490000040c4041030000c1c200700079141c003550003282006000e1412204010980c0d20703c1d4140742c803e00d101e0740510005034000400d03221860021454440d0090489101042c60142a12085c4258280020301258080c0811940c011900035030302140c5400c007540054806080511906c1051210f20488804c5090b10750f0140014a1000700090300d4640f0080a4081c040b818007001e84c0e68400001c01c0c0300400c40b441c401e80d0001d040c210495801c0000000026080c02c400070404000e11440b407850b080295150785143c14a00d00381b10010190104440d000d100500c01807868a0003080c0300c7c1c0208850398002c51015520f650700ca0020715840da5800000c4010300006030013240c000c00003d2541d40165154000381000c1e016520080c0300d1088560104000410702414112001e807a04549080703242e42d03001c80009590003940c4e8a1425164 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377769091 1250 377767841 377767843
    0x906080105100f030b0711011b0818030405030a061e020f270d0b061503010b0a1205010b0712020a0804090b0f090402030c0d080c0312010f14060406030504140601030606080114041106070203 83
    0x3a642404003009c035120882036250000441c9003d4126040c0b140c2e6101c401c002d041d60750340300358081c03030798942d101d8240000000c849800121754600b102c3c240800f5820a91040300598119401034080c8040c003080700e05e0440c07404d000720030040aa80f20300718145120000031a0301000140c1c0e014048a43d40b0700028141c0d200c08181c841c0318146040d519599603075609048166400c0300c0c3c406000108481c4e85404107044502820b8181c4803040340c007901d0300f90555501c000000103101003800394015070902c00085110030004d4002094042000b044100c9814208515010500c51203441500003805210150302c2c002060020904180c517000e080c400541040c40c201d0043c80c0301c0c1d018a100008825030116a1289514100c0f581c803c0d401c1c0c00c013521860300340000c402031000103030007400078001046004d210340c101541140c0250082d8580454004115041c00c200340c005075034442c0c40d00c00420101d00e00744100c0000707041d0001042400d0500e50740704032072005132503001807203007901140d500250342e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377770341 1250 377769091 377769101
    0x6070602210a0b0a05030c091b0d021329090a17030a09060c03020318040204170604020f010302090307230306090a050d050a020607180906080105100f030b071101 71
    0xd08503045451850209101e101c04078100ca000803500e0400808544904006040900703450f0000e000d4030b1501100000d01080401c014210015101d81e0f80b0341142224040c0014485141054030269031555060001040c80b2925441070100c03649452000390060401c00022285d0140040c00c4d84d940d00300e42c1e0000701d61162030b400801a072003035006080100b0318004010074600541e40c54840229a88100a0381c54605481c00540960000c0202d12000c90030221a854240c4008000604250b115010049030000700d81c50100300d54032400a210030741c0380c101d100b00307440042460154608000c80002c40d40340c0d040b81c45884152114081450405685a145248000c41c090100c5000d450685c9002d81d9807d00b4803001d503491300901c01c0002d601440342044903202840c83d001040380391030315042110181d030050424002410f2110002c51500d00b140034030340080003410004115410000b5085c03150001d668005030800001c004100006101c0c0100e1a6002d0b005041c48958021100c1420780944 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377771591 1250 377770341 377770357
    0xe0303160212070b030a060e010302090a050615190306150f0c0c050d0f031b03050a0807020a05070b1206030109030c030810030b0a0204090c0207061d0607050105010b0a1107050901030206070602 85
    0x1020b40080404c00c4100c4102130b5100701c24812062144590f030790000c0d04400420301000e5045410b80c0c2c0000d201c0c4007030b0340281c0d03008a80604101c1d1021900e500c002455000341d11141d001c0e1607a4850a0460b59050243c0700241c6011300350b42c0c4030780313181001c05071403581100c8490060041e404520800d205000403c03000800e4054074070392800d4180d1500782101d020200080700032902c00d034819508400e400c0c2480c40121f034582c454038030b01591842e080d82c60030743c000d20f13034400c51055480320700000b0810311140c4010001400100c5d1654400c003d01c8581c03040003040385009070b1400d0b1040300032941c41210448003540505110010b5110b982050300c0c20750841e0800b4201c1c00c005002c0c44460081d0b0360041049902c001020004103520f000126111102403141000050080020305540d03114101640c4140c500201f00616040660b541c4030b00356642681701402c0001d010505200007030300701e4203540d8204946c0c0f005e0311605040c40d000608604040c0006801190041412820080d40c1d904881c010 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377772841 1250 377771591 377771593
    0x6050607050c0a0906030f081c0e06090c010e06041502120a050409050106110c0402030a140a0608060702060c040e0402010c0506040b060a120b0c070c12080c010c0e0303160212 77
    0x649501e040040d070310288550010b002e0141c0c404001607a03a1284100c44c2030b0781d0701150682044005407074001d015002060307180000b042d0741c50300340c000300300318802c50b4440003208001e00740a241403c44541008400003019060241da96001c1c3c550303944580413542540d45034a000c521641d00500300328a0030460860031200c5a00c0040d001012a4010018000722650240c0503c1542e0301c0300340881d580360484444020550101c020041d4900d040d40103035901052050001a078070011344008011840150380d240b860382c2c0e44000500440a041c410550b100da05c0c0c0c0010a03180c03e02042007641842540705582c00c0c40f040001050031a84919055400280c000007180c00710b06007801e0154020006842d0188102d0352000c0020b01595000c03007140c0c200b904844000740541c0d82040200319644071550480b074455200c0c00c003142c0000040c01e01d005540c0a5220b098407026111846400c40b1125140c50b014040312198084080e0303800070403940f0390020031108150490143c404a00c08514600c403400003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377774091 1250 377772841 377772847
    0x1905150d0e060106092301120c0e150415180608090304031203050f18030a1206030204060626280e0607111507020606060c07051e10090621060506 64
    0xb54450b444c1000e881800b0340d021481da5401001c644c06c3c1c400340070780a000c5914045040800c510070740c8000202d00003401c2c03c3c440300c0c1f261400110740c625a01001c1c01100c3d8080b03420b100301c00c400003100042c41154101500f02402605160180103118443e10040204850000b010b4040510649005507030000b0144e4410f41ba0600c042c024207c04ca90000c102514500003134a003a00d00d080320391003982600081e41c5810701a58041f526018810091710001b0344035180040141c80c0d030b228010060641d40c2d11407012190f50641e0702000d10410b11030726500702c180303001e004400802e020000c00610303000c064515000c560390643ca01400d48484092024003915040201041d0498103a43e03140300004283c40700c20410804481a22030266100c0c0c005a20070800240141003c00041680e108030000300c5403c0d95450f00007510031390380d03003803804058611000601d0442c24a0007202c0808901410800300c00e600704240140b100c40c0c01982c0c44441e01a58008400c0c1621503030005c4098070016081d135903 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377775341 1250 377774091 377774099
    0x9020f04030209150a060f02010204051309051203010e01060c060f14060a0506040f050603100f080d08340c0614040b0f2814151905150d0e0601 63
    0x15030018407060f80100083d500080030740c504241442009540180b44090843c1000c01c201c944035541d005034415503501f00b1000c0340c90f41c0c8241e100384001800400100c1c40400c60714200d418500004030280e094002840140001181ca03041c09056178032500c0e101038101820300b03188014102c01e0114072507683c904080c0b0030100566040300341c8685010b98400520351354407010700005210303511603d00c040d280a107091003d450600300075a00b00006070b090841c0303c1d465503a6184542d640b03034407640c09036000c401c4c4c0310900358110f80300c694040c03580c5002c0c140304841d000c9006080c00152a9080303c0740c00050080b0621401004803242c0c42d50051010041803a1a40c03a00c540e00d40c042d035095440750403020005801c5a241072a040c0301d803064429840450f0407160041d042c03041400591070150f51a21040c0b4203c030201070100d80714045901c1d240d00c2030f15000c400c0c0615408140c0340606010850359082c420380c0c0383c18046404c000a0f0110007540e0325551a001070092034518840550340c000c0307000010b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377776591 1250 377775341 377775367
    0x506070f061b0801060c020f120f0f010b0a050d02100f1413090e16030b06011205161103040f05011101020c0a03050a12150b031e010807031401150b030903040902 71
    0x44003401842e10703400b010b41d03205c00d42a20391403110000254420383e41c51100c12141000500c0d0184444124211108003110401700b506101c424011240269074441c0121840e01d42030340030100420081d2100321707001d10140c011a2017644640d44500a004000901c001520300c01e2040403034405007400301c00d44072074504030302c141410100d100d0120300500304541d8400c03402001c43c0391460112500d444481951941c1c0c0c66000e01f0000501c2141840b00ca00d030b1042201129004903840b40002840d0340ca14540703c08405480356244502d01030b00355105010a04c00389541142c00c8054840c00d08040081c40d00c040c214502a201d02480038079180614240c20007056080070207464402c3c26030321081030080c841880b00c03044928219011100f8640c038001000303d101c00c40000e40e040002c00c4001d4200b080c5d035640203040b42d482030f446002d03aa445828100300344082038a41c401201024002070010311204110055159594001d148500e02d00101080480b50104219801807084103001c1d503c62220314114 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377777841 1250 377776591 377776631
    0x504020409090204051027020c0a1a09010912050f0c030c071d06010203030f13060606080a060b09060f0c07030b070c11030d02100c230706240506070f06 67
    0x40b1300803400d003008602e29086440c00781060350340c0403d40d5400c0c0c9012080b10341090801c030104841e50741c1c3c00c2110410104080c01502040360081e80e031506455071030307403812040010040500c0980c0c0d1510010500284030710b002e520354620f0a1608907154240890040b641d4401e04040654602c4001140b4545450100700312040b140c251410500285010715119284801118070a005230010400a66582c40310548070381c01101d01000303544020031a50b110340131600070743c01100200300c4060400c00503820a0003050082e2900d40d45203420300320300101241d40c40c0076503202116058004101a00b80103000c2000e28001c5411249040b56801d100c80c002d05400cac4d24610645503c518024400c4a500b4009130480354024076030300070481c0030240a071400c01410604000420880c81d1255003581c0728000c0c1100c0c00d90210301c03182680d038840c20710b4400c0407542014101c002c1050380314418000990003002600442d44150703071503641c40006107020400e027012152700030300c103d240501c0386450701110081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377779091 1250 377777841 377777843
    0x9050d060b120312130f0501022d04031e061b030213050f030c09371b0519030b1003020a12060f03020409050307021206040b06010801150513050402040909 68
    0x603510b1100c40040d03103584a00c90241400200c03c0c540004c00c0421810b002c134945418090b201041e2000119a101402c0e42e00c02d4100707285da00c200030b0b0310308406802c1244041030f042c40c0101c41450030f4a035544255241c854203042d0124654901c0c1c403c003c1c45003503007041c0c84a507220350a031466403d00070005070003900510030000c82e50f0f0704110041650304114103c001840d20050081000b92188020015035050041c89042d1070241e400d039400707201800e0065400d200c0c0d680340000058406007800c41080310f01c03440d92100d000d001c0c2005200117541160841e002c0540c40d50721014a65500311040e8054079980340000e40000500d94001e101c036900d58050170388200395985000c02c0700c11208803c230942e4000d0045c0503120203c44c1e4100010310b0698000303402a445442500d0030b000e01b940004040207858801c80002e500404104810001030724420765020034242850a0781c0c3d41045599000d440b00c120b8a081848400540c050800317141920b500001d1600420656840b80c4480908002d441d02c090 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377780341 1250 377779091 377779099
    0x20d061b0216090c0e04180204020414150406050a080c130b03010e090d0207060315080709021e07050607031a031e0d02010506060d020f040b0c0106031203020c1c09050d060b 76
    0x80850480c00c00e014404902c2413550302c40c40060000000c00c4000d01070820414a64404c907020480180c45600260009080d91025003a551000308144207504501819a2158880030042402002d400800b036640e851020b00e800a000d55070103203c0e500758441c01144c80c203200051580042c3e06440e9200a5060303078080c0b000603200d40c0366040c15035510791142ea030002c0540c11482e41405400e10a5015280c0078041a4a04242a1761160514144042900030380c80d0242c0000e42802c0b00f48000c08501c4228004045040c80c1522a0301d1f015164840a005a020191601000308890015802228000e480181981c0c444a400680c4801c0a1803944502c00680a02c16030000968011710841d4810740c4050701d80c0b03141c2021144544001d50081055004001c0c0511002c2800b26411025144e07030840c0700000510242141440d80082015290718810180101b04800a1903004145004011652502a1503410304100d09540d0000140c1005400c003480040a81c180306141e004002e1011b4161 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377781591 1250 377780341 377780383
    0x402100c02030d0e03010f0501090614030f0a02090a0609180302061003050303060d210c06060504060621240e0c070b1501021204030f0c0603020313020d061b02 70
    0x410a951040031040042d40c503401260004401078000c2507860301c4060018000603010b941c84090004542c400e070880740d429952885c050010740550001c060590300c0c110f00500d0744565402800d40e6400030484000e00444011000c0751a08005402402c040c00640c1418003c1e51205804407601c00e06142042d00144181c00204504171004410311094a402101031451a0340d440c0900942130000b420813103034002c00355130741041500c1c104840c0c850100540d075080c01c140150b0400130155240e580000740309510b480810000c04e40c00040303001c48a0b0905060140c120801034010004000b02c070b07212030809105900d01c0114440610301002a94484419048ac5031940c4884030000d00a08900030b0070404c1c820040366000e1042c551210507010144121030704500e01850303031406a00964001c540304002e141803d8104420701154102410441c41c04508618010342c01900c45134404401a0240d8616216203080c84803c0d04012081d013001c0c007013007682075502080203640340840e8002000707540c191 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377782841 1250 377781591 377781619
    0x605060316140a02030406050f1624020a0503010302281805090607050a080a180b012607060e040906020f03071e0c060506060706090501060504060801110307050901050418050402 78
    0x50b505071840c0c81c502e9070003141032905140741a2a907070b0140086021041040c407149001c0c035205a0a252001d1084020100550301054181122183c0c50203801c1c00c14014002811079a85c00f278196030440e6012140905c12180c1c00700ea0b000800d84000d01445c0d0014901ca010950256038014407240c164200800c00c01959805036464480400340e52003800220b0401c1690102c41c89005c8a9030046101403001980e480c151a180200f02010602250307041c036504010820305000004111500d079007410440e0007010180801a101c82060140f0b400b0300884180920280d26580d02c030362000c41c0c1c440002c540d5031480c2d0045a415400c110368100005500400303a07416100c144000b180b01710040d851b41c080300951a9601006020700401603900204248015004584035001d910101401040000b42c0c980c10302c0c0030711003502d0701c60b080007003d81c0c1400c849403560903220081b40d178000d100d0314005807030300312110040b43d040c404c0d039004000703082c60500c042c01c40748050350026001d284203c44150507841c0b8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377784091 1250 377782841 377782877
    0xc0c04050c0414060d0608010504032607030e0c03061911070b15040905160f0b0405062a03040b180d150903020c04090506061203070b070f030605060316 67
    0xc2210000039010050000f04510350f244400364114910052200307007066036140b50102100d0060b803100040703a4441c0c1c18441819000070b5143c01261040d4000c8045003040c6903000101c040140901013055a60000c05404540031701640007805030060640d80b480c1070400e100d01e0300c0b108d4000d003000b1151402d150000b1401d04241121422913006014040035500c1c180301c0e02c51396100ca44515005a11858000001a010700c003081c00300b4440c0d5403491100303050608101903080304d500001e18039a0204020301180c0d444c0c2c1e0550710b207440b403c00c001901910b000f801e42c03449200f40d20800c1440c440802c021035120080c202410840c4460114582501950001c0004800b620035028041c0d000c03240c1e290005410a8020041c05030290040b210501c00344808102110341042040d94190800001e001507442c2001681002c8010300f0001c6080c0302454950000c2d000e000b400900c14070040c0744034811010700a0b0040ca005060044c82c1540703030300d0300940e40a0120f0f5641d072a4000150344119089240784 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377785341 1250 377784091 377784101
    0x11502010e060a0b032d0c0f030c0603090c090c0c0c1906080601090e1024051b0703080304080309010c0c030e04020a030b1e130207031d04090605010b0c0c04 69
    0x400100104a9910360790403070001845000030b441d0701802a0003e420400c207810010010003030b040030300c1400c02443d000e0301600b44444440140c0c805c0c0c8c500c000d5214155400940041040c0088039010f60720b03184c900125251040600c01542c00107110800c0124164150300030306028000082030f2072001d401002080180c0004924140e207520010105005483c410010f503a8840c2c3d06040c82c1a815850f40841c04101e48101d9070500c001d50009000d0100d69000a0b2442c3e0062515410070b2400809040181140c0505a0f041565104000b80c02d044be1b00d0410a02000310741145165035a4101818004020b51080310301103850740c245244851440d10071101c0414094260f590a6200090081000041d6229038802001c01d0340f10380d51007059a031500c98240791403045081c011031480d04002030051102424094400071031040c4000300c0841d8100391034806108000810300104166040042e00070040e6440180000e450107001094252400e0018400c8801c039000b01d42d2100ca0100401040d98 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377786591 1250 377785341 377785361
    0xf02070509040b040318080c0f0411070f1727060712140c010609090c230603040303180606030212160b0c011b080a0f022b060801090b01150201 63
    0x64070501c00100403482c070b4219550018886d02e04410080150f5510300a2481140c00c40b12441d08000d03190711161500d00700d543c0c652007003507905002c82481d00c19403420b540103c0c0000750106407048014402c02800382c1c03001c2002410280b513291104403008850400c7c0308040c10000108440c107086150701d03c5c192080e0b03000b26502151003c40b480e1451000c88081101070983e405200081c84070100380300003800b40ca0081d0900c0300c8002030b0b2080d82d0a00c58040f2803e43d111a03020403000c410841141c100d00c84d690203c12094610b10307500d03120b0746011001480002070040101c1c81d460a00d00802940360000b0003124001c46030060044030f000300250320352580d01008580303070011001c10440840c10700003a00503212401c000040c0d400b42840d401c2c44800e035111141d40021100001c1043c0f88040d40b040c0e03141002454411801d01d80070905206070042c100c2c28070048600010305004074910581c21990203400d0900c0280100c582e14603124004003c00c1c00b6000e40e20f500498500043e6105104e642034039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377787841 1250 377786591 377786599
    0x70b01231c06150e0906010b03070215071b050606010207080f0705090408090306012403060506180d0c080a0312020a0c0f03050c0313031203090b01050415031509030f020705 76
    0x100041092455203034110100446001c2c0e1203d50b9060610495403071100209000700c80b012141c41e1500e811403c0810507081808161030034000e00041d5503000513440c040a2903908581091b45070003c040e54101c00c0e03007103040c48c115010320390401040001b00b2903a000f14020380844201c65222903d0544441c003600b2320003c9688a25420050b0380341c0208016007040c0205800c0380b42c043d4000100b802c04000742c210034000380c1c14000b41c44003010f20070b0000e664000360345002c105490038400080c00390b200e100342e004184140c80c120040280d40381001d0f280d1055002e6445001030f540c0d00040ba44510b41042c0580c0412120402c01034405030301e00071688030907915513481100c01581d03030f126940148405401d408012051080741000e0760104003c0600c5008004007500b41031551411500360800340b250101098100070041000a40540713460741500c40445010869420701895031070750706041d03800a00118040802403d02d60b803103900c4921958060703903882001d101840d80582c1d603101c080c8185604 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377789091 1250 377787841 377787859
    0x310030b0f07050f0d0b1002250f170c10030608010b010c0b07141209070509010816090c030920090f090a030e04060e07080603061b1905040803070b0123 67
    0x1013800c000c401407074204014100014004c0e186804280424180d41c07200000d070744611200d8400034080c07a03028044d941c007410441242810000030000c808030ba403145005c103842044a11001c0c803001c4c00b459502c1d00780644000803004840b035004000d040341c4e10803a0165480d2009040c59540721340b030303507215071500a08429803136218140c0031074100c5111402c9104440c0280070f100c0e0225103070050700b07009448010003840858201001c202d60810f0613880059141d00a8020742079454141c01c220302101c2c10044001010909200c05901030010b0310b800401c0c030440750300c182000c40a01e1060412808095648620540d15004100c240317210540b0000f145901c2085c4c841d000a1203904060881c18002e000480d425035140a200e03490682500c407a00819000000c028107801c2c00c000a59101440910340001e030003c030a00342105202d0700008124425903040500c06060107542120300524641c800c8036910101070030302803082130081c01010812088030b504a813080d0901050412078050051005107 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377790341 1250 377789091 377789107
    0xf090317040606030b0903090102100525050f0417070603061a03040614070c020f09070903170415110c060a0f080910020c150f010807030f0302010f020310030b0f0705 73
    0x64840c4000344200d4040b911404080009016440340703e02502c003d00085441d003458800181c20014001d000c41c8003a80341c54108504000c0c001d809000d12030803004140140c07902e40740100d41500c12038009800c54400042d00091000c2c110b07171208000c100758002e85036060b8130f82200b1420364040707205190b070004079400040b000410820003560020f200d020000b41c1d014000b48030782c1501c0c00488207580402c0c0c2110521040d4104000d140203002011120844c052070b18013030280002c1c695000c00751000700d400140008280c070180494010b080039110343c000111340c1c8000200392108014480c0e00c1401007030340c0681c0c5030601c0d005884503034410713445904c4907801c9904102c84400000b00030442c10320521400d600c030b1802601c002c0003059101d801401c03000d082c0d501400a0207802030288a00110003000411440101250701c10035290701c00000b170b03440422800c00728003500000e400781e40c01510010510655803c80414801100c0c0f00b034000007010740c2c403015104141c200840e1322001003202006144 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377791591 1250 377790341 377790377
    0x11090405060106210603110103200a05071a09060403020d02070f050402030a15030b07030b09060a090c0507120807260a110c01021812030403080a2303070804060f0903 73
    0x502141010f50310042e20084003611300c0c1c10750f401c507841694007101901e904003280d6414042c0303d0400c0c00487c240a0010010000210300f849603480ea0420041c001c60704100700005030b541000e100400f10f84a016600b02411500e0300c1c0d0b0400d441c00c84c00340c0b2401040c00c107081c0c0042040300450b01900007030100140303080240f101030341c0300512542070183e5840c0408034603041189a5800395000703006000042c501010042c04039000b105132684500401c1003000420f581b0048201c003550116000417130b0440d03401c2002c6e00d1500545a008100c6001c1c010322501590f404008148910081c0d07842c00a00b0740700c8180c6000c2ca42107012a81c014190580018040c0c02c520b030400e001d4000c642046a24007448d2401040c220b0b0002d4800070038114020641140c41c0c988154001d503900f1600c2c01940c545071542c2daa1508901c60b003808e840c180f00054242403580061440145540102d00328515aa8a00714400030105801200e080354413902d4041d0b69202400c552041860f0743e64541c80321440300800640f80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377792841 1250 377791591 377791607
    0xb06120d08070f0c02130c030b0d1104020f040b04080307061d211c02040512030903100e0102070b0408090307060f090b0f0c030c150109050c030604021c020309070311090405060106 79
    0x810038080590b00303520058446086c0525048000c844c005589811444014140d030701032801c0c94420503c0e0150300011a9040e42c00e814180000c890042e500d88140d40c07402e207580910307805020340d0500410002946c1c0700204c010304109101d0802000205005003600e0b0301075000c2e0ba59150f050340700d00c81802841c82280c030340440d8030f00c00c00040c0d4108286406040b0b9210006983c0008040e00400d08001a05001520901d480c8109020314140070104020954404900040c16a10f9890303006100e1018001e604442e01140c00c0003a40030719203080e00b0801c40390390112401c0b50007446502d100080c2c540c850030210341202220381c0c0b404400e40c64074505000301c0d0450030610035949010030841304016070800040c5038581c103000c0034201103131410343c500d061201c0591210a5050a200030440041104d00441c0c2d03106108650050310340d0360444014610034100c04151140303901c0001809240308001803020704481c80780c4150b1081801041c1403003000041580c0003407440c3d00000060041038010008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377794091 1250 377792841 377792867
    0xb06040b010c0203011d0c03010501060e09070e10081806160f05130807050325150509032a06090904020603070c05060103030f08071b06020a050d06030b06120d0807 72
    0x244882c0740e099000207084a40d07811804601d0560070140494050042c41801001003045008011780d601d4684050080b12124004500c030700c6114001908950207680b80d80343c2c004000d861105450010300010388040400d44090b642400a420210055580020030510524802d0300c41401d03000e440005441640c00502000140034040c0300110202c0090302d03003500140b102c1e40003041341600d030009243c200fa00c40b580c50b010040821200c060060040001c0c20202c61031041d01088186400b07800303c845020780036400e07078507002d15031126041181c0c0034402d400d4020f0341440c81040c14120007c000b8240300c2c0101c0c103500065a03000050143c5840c6000c4c1d070707008109092a40041480380d0b00c807410950309820440c0882c4180b8032402410fa0f0010042d80e01c00c086080103038407060074581502011032004402001070790001141d449841c8500e007540c680c140407035000d00c14070b40c691400c4043d8000c22a048d40c05034402d07042800040c0000034190b82050915207555015880c1c401044034078941d25a0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377795341 1250 377794091 377794097
    0x5040b0a05030102120a1803020d08070302040e070f030c0504060c020f0d080d0c0e010c15050a1d010605180606043503090f093603190311070b06040b01 67
    0x28001071545081c001050070030048030010200703107031400e004003c0320301040303612070444030b0b120942c030000e40c0016519075074403524200b9040b41d6966510440c0a80f069410041c10701020005012885400503101d4802c03050fa5141070102000000046460380114443d8200040359a5812000750034084824038541e28044d0510f04101c541d51502c0e0041c0d48004411040907654100500c00b07107a0180007202c0a01c0709107096603c900181d2900c1c841d8000200141050f03950312004101a100c8030750140d039000a55103001c1c3c44140c00c00034024020905449480c0c000c10300b031010100c1d5600c280103c1e0b0711500008100600303107801c0030310079803158015000b401e40c0c140080341078407140855015010746001d495401180c1d5485d1003018012000f04040d1f403207008008142c207100e40c41c90180c04c0c0046103513010a840c15001c441c8544c000202c528140100150b000000d9070714030002d4400300d070310026019500c0921600e9407181c61421940318926001e0310b20f0b14604045180b5103081d821240310240149 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377796591 1250 377795341 377795359
    0x3040501060b03070f0311090d020913061109030730080904020d0504050f060c0f0a091502070614090112020f0904150807140306040201080612031305091f05040b 71
    0x3541c00ba1281d200b990600c01250140c280540c0480d41405081c02c411444d0b03212a04055a03400030449100341700340020300c40e25aa4001520020002c030b81881300d80c6d00040306001c250360a192000080c1d2003c081d8a0181c09400e9000c255108800c4003c16074003108010a0f42c40d501400482020500c8444126040c5104003c1d82d0340782d54450015010340c200b29040000d644c10709151140c50507110034404105070300b01804001d40c4811032410344443d8039a1001e0700c1e0355002a140e04859012042e0401c408024510105140c404c1d400a2000140c901e192900e03030b407001604864130540c0c011120f505000814400e10003004800c2d51700903192991002080c0c0c0c0c00c0c10480800035040e12103100b020407154258403000c0088060420400c0005c08443c40401449101080401e45807000240060306001c181400305004e902c0f44d0b05160415040b940a89884884884418142000500c20544528113040210309002c402c0a0641d200402e8040340008140c5001c0620000d0800c102c12154030210300c17 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377797841 1250 377796591 377796599
    0x7030e0a120c0c03060f050604060602010e1b030a080d14060306150103110405120d1b0c030b090c0603040c03030e06041214030405030a06290915040902060a0c02030c01031e020304050106 82
    0xb82c00344400e241e1b071220011a092800030b0a00084400c268000b80031a810701c0701c050303141c47c00400c05640050880207044ea51600d0740010034504030102c00001d24a00001404901586d82c0e9072082c4450280100c400600781c4035070042640c0ca0505945181d04256040c05841d1158042c0c0e000075240d030818042d01d82010741d900009018251428001c02c0039800036102c16a4495000004140882c1d045004410b5070748079490700c440702c50040c0402051005c0590118407070380c2003008502000d6100030146540c074501481c00d51418052071000701c020409446045007a407400c00284c0701032700c1d2210381c0c8404a411607207990740c401103c9080450300340000c00c008502c0d03880511a00114602511005c1400744551920903d0b00c082e5001c058082d003005910000e003030366000768154100c1e014410b10440005040c1c00200241954000254007910008a602815402c4a18840c0c1e00d40224150b030000004a0015001d0319a14880c004c03510b248000c41070507218265001d143c119000b0b000000e904ca0311 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377799091 1250 377797841 377797853
    0x605042c01080a0b09060c0702040b0a1a070506060d0f2901090c110102090d02131104092306031c09030203070806102c0a0e060f07030e0a120c0c03 65
    0x2080e000011150071048283e002e2014060400d5000112940203020f186880b11105003c1c2c014410004e00c84c0d900c4074010900385d5500350251002c7c107603031901a00c007018000191102070f44803220880d603e000f1000010294903024502c2a800d9400590716a501318180d500c3c04074010000220300c1c070404100305003491b40521464485c0c040c0030709071800902c4500c0d000c030282032a03446804000903a0300401c0554126100e20f48081c0d4101d0341600e210300380b02190002d0b000600000c41c01305401890200740041c5907245034108429208031040501c000801c56158030f8082d0904440d015003550103126048060817201802c0a4440300b070303117804008181c0303d03800282450000c0e80700030a154412014400080c2050004100811a02d032200d0310742090000758502c05c0f00740741d000146100a02d000070f001100309401c844400b070400803e842840c50b018502640c004002d8494600082c07030200c0448003d0000114001e02d40e4102141280d005503c0e0002c441d000c001e168125220890004d00000140e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377800341 1250 377799091 377799179
    0x603030706060e181903030e030c1c030e031608091201020d0c032301060509040b0d06060305071707350d020d030c27120803060f0406060504 62
    0x1900080c02c2031418108483d20a5814540354138103103811142d84034000c10b1007081c11800f000d90506012070102000e010341800d5005142d0802040d0190040101084880260302000703071100f51420009104102005540c6e0701542543d0b00a01c4c01243c1d00d41d0204078603001402e40d14200906480304020f600303807a00d0076a00008804444c04e0b03100c1002e06105030309401003411a4460050f8107034048a8054070090b690b9040c03103090f0612030000351030b4900d600c0c0c2d03800001c00800040c0c84101b219006140034001030100d448151198050f010020860f450850600043c62010500a20740203061004501135038030000e081480001020300c4024500110021a11402d00c51002403c0c00c03401d0400041d081140c415800001c0608d04400110065004280a0701d1030103014907100c000d42c0f51501c60003450009410400314130f4050410b01c01000310b04c0b8004c507c100010340d00764061007088028001511a1070044101140c0b00340b00c1803010001c50320a41c0040c2801d80c0c15060b140041142c0240c07084 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377801591 1250 377800341 377800349
    0x40e06240a0804110105071a0601031821050a0e060c010207023a08070b060310150f0506130506160f2018160507080c06190b01090b03060303070606 65
    0x940c0410411080c0a104c40c001c082c01002800c05c103280040a54072004a000d1400345144003203410000306e003c0764480e5112071945445030007c0b0f03445d600030b4200f400250301d001c10b040d8201c9040c0182c7d210090700ca003080c2c5480790407940b1408140700c005003c111071038112801c2c4203410340d4288000005641c070200101c1903060311021400d0446400350401a28110441d88a01c524140c41000000500b4010845000d03d400103030f0740805841d188002420801c08140004450781031902034040000392181503030403540201241c605455aa03418000c00d400f8484020100342400d000402c29410041f000b0444407444464000800500382e42e401031106491500b6034500d41110050600741a10401c0254455030495090700c0d0403840c4158410031500c0184005032421401060203d50f500a0301618180c82d07000b41040c1e1200810980650360b400304071a0b14031003030b040d04080b000750003841c0300f07032102040180e50b1841601d00b0641403100544c4080d142035014801000108040740461142e54054 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377802841 1250 377801591 377801597
    0x4090602070312020a21180302010b01020705011115060310090506060a0909020f12120d0b01081f05010807090509070804020109232b05030406030c05040e06240a 71
    0x40c01c03550038001c082210b540303140c10040d441088020700190b0401c051043c0645808052040910202c003c0d40c00740498000a00d8081c024801d14000c00d40c06410124001500307a00301c880e004c1d500c0004480340701c240c4100015507040a070201988596510f101c1c1d90066000c0c0844640075a241481011101e504209a4071a0020010700a0310301c0c0210301d0000a09180a00b409040c5070350300001d03901c0140c3d040b03c6105001c07d0f400350f0000c1c81c050200c50304210011000325102c035480d9102101403e40d6042c1d982c001241c0800291307101c01608240d40305503900c0c2007850841da0030b04005580c03135003002d860304050041041d00000c1d55a2a1403100340b041c0700650b40c062007810140300141c4021000c2e08940054059201098018a100e1901c2000044200ca800c1c59100500d94681c880c180070071065002c0c070b40a420340000b8454008014012645150380420040c01c41220841d4180121b0080c0e892014440700415028541711203000c9001c03c20300640c1c03207a802d502500c2009a40910304030004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377804091 1250 377802841 377802847
    0x306140105010507120c020a05041805010b040207030f0c0302070905071805220b0d0623091507110124030c090614060c0f0706110607021c051804090602 67
    0x91450548040e0041c0800e00b44141842942e646001d800000d0070007110406c52451064020755440014501c001d100186c03040160817403004000480b82402e07201070382c0700c0d03003008204152800c003842240c0219416549616510040744001c0310303c42c425010540c214880c030480402c041c4050301c240c030300030303071454566901c0b00c07443d180c41c21400a4070303501039441111503400c402d41019521403800c4100010f00c00018041070050006a0a00a82a40601550306d4011200c014a0100130700840120050004100360b6507000e0380981e442034240d4803903940890400c003142c1094000d000000500c1000800841d0351004403600f10351b1a03001111581282034098000c100b40640c405400d00501a00030b020701c40b8505001d10f4500c854618158140140070014240300080700070310032000b0140c2030905a468040d91b510000b8105c5404504c850040e0040d0004142424000142c5c041d0799107100e100d104030111400400d03a5180c2000c4010300090f0305644032002d0983e6213208041c8410300c160401a2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377805341 1250 377804091 377804111
    0x307081c0e1506120c131508010c17150d0201080c0d09060b0f010908190f06020f03100504021611060c0a080403030f0516060b1f2106050108041103070f0306 69
    0x401000c040e61451440e04100b000041c0e5440359100c0c0b00146c00c2001000c91042c1980300190401d0640b80c0c020b0342e40303500c3d00741c0406600b0b5011030300c80703191070500c0300d40070340b42c0c56180701e21440702a62501158080e0030300c81c0e1200154090305007a0340c0211801003003030405045140440a0304c400c808100c039900d5030354960150500d40003504207a03201c0e0a01e80046031a041240e1340e42d1b030303112640181c07801d0101508550300708052060000c0003280d00c10b00030342d2034017680f0404400036001036416000610b400900416241000e1080c2c030305500d0020b0548400002c0340c0c403a41c411040310680b40d81c11a40070046c45000d080104100942d80d8464082c41341d545145040082108000040d03850801104020170414903141d4641c900603250884c1c00007448001800014a016017081201c0010300400ba6001040c150401300e803640c80c1c41601d100201000300c080941c022544070380905408a42c5804c003040201300c0c0865403880414014088810003511042080b0134409280c2c0304541180e103405a1103 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377806591 1250 377805341 377805349
    0x9051003170a02061b0f0c03090405131a07141201080c0901050a0608070203070c080604060b010e01020a0b0408070206030906070201060608040c12030201060e0915090307081c0e1506 80
    0x1800d90007800014605101405500135181e20000d08079525a150000c6055540010401100c41c0c4103c3c00494591714100300110039200e400c11b8401911841c50040000c111203091300d0b288210581c008036401f80313070119060b000b40382900a8000e50407ca106040101e00681082c000d01c6082800050f4120962500001610f4107910a1561340984020801003026480d001d0811090b1000c90031b007000700d40c2e11103100301d195004120018040c40720584000810780e03c0490101c2c0502d014103018440e030b0700e0b11001911070490b000b1a25005030310411850001c607620100b6650480c0c410b01c007152504c034040c0c00062013030f041965990250b4204c54203000545809114201c01485107090041c540d10741a20780300d4551029214218407070319200200c070308151007036200501400e01410001220b06007014259541d8805003020f000880900d000f1444014000042d2003240354808101d618040c2a0302e0540b4003d0344c800c400e012410b072135102e22082c212042c0321158812014031103000781ca14000f4100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377807841 1250 377806591 377806613
    0x15091107062301122d02010f021c0513030b0a051008010c0207060806060903070f06020d110d030e031204061e18120e0a0b0307021c0512060a09051003 66
    0x42500076002c6403034440c0000107410400d0444440c00015400da6100e42420071041a20000c0383c1010014903208000c060408004405030174000c1e42d85100d2066034401c01d90361154080d0300d80400c0c8904030280b91580744968000c00040302c0741000320052035a070b642c1d0011350160644d0080d0006445a00708509030b80840780303a030000c06c4104000c0c1700000207403e0217901c525660140404204030070340043c14545070a81181c4075150050210f0380c541d5035581020200703d00a004010050141c441141491445504084038800b5803c019101e14600d105003a002003605c8007500400307020902c03c84542c640d1982049219a0189001092007204050701101612013500d00c845164a81014041c1e1a603400d0aa040d6903a446060501c071141c52200960b00094910400395001c0102c1034007041c440a80005140100f4a03034003218004180001c00a01000d50012180700042040c4503420009401a40854002c4d0700901980103c5803035105407400d4810849150341c40600d010000c00400c00c00c241c0c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377809091 1250 377807841 377807861
    0x7050607020f0703080d0510051309031404270e0d020f070902040602060a090507080f0a02131116170d0c0215100509040507050303030709060906050301030f061509110706 75
    0x3e42107180c1940d481d041c03180140e02e4140c0740d00d039855002030b4200c1030074094400503280041014210590006a07880540040c03401100051482c42c0c688521010000c2504c1c140c1d5640300802000421031500007441440606520206036102c540d030b091100ca051110340c00ca42c04070b5018040910454036460316280c910f9000e182c0107031040108214456003c90780076000400d0002c08680e442c003900300640381c201a504080e04c070340a4010380144e101c800061881c501482503503409001400807500008441070006464181141002800c1541e0b07000d1100c8101c4d248580611013801c443c881c0c03010b901d07030441c81500410b0b81d6a8009070200d241c04020381140400c150a1503440da140000750341250746820700c580b80c0144400c0e00414204003050141402521018084031b889140c043c000514200c840e101d0f200c0070a1002d0404200e041c45142100c0c107803500b05580da600490569141402400404902800c007149c03c480400d0800d400d0103030540c2e0703e400381c40d26a04c540712410301c10112155440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377810341 1250 377809091 377809093
    0x51b0a0207140102120406050a1106070507030305090303041122060b0706050901060b0a0f02010912030504021f05030c0702040905100608120903100b182d040c2907050607020f 77
    0x2488405c2403c0d05003c4038261045031170204d488800c00740f410744864083d94130940490160600304030740203a004015249590080e9400c1c001916400056074892006903000340185642c4101e000843c2404140b8414281c0c8403d208001c105001510404941450f00101405000040c440301480054004d0541040324400200010b9150407907a40d024400e03800707a6400d10800050078000305000f94440c885150308809030044c0064403180090081104950481c403600804842d040016040b00719004241299105c2d1031458840408444c1035400c0001c04076441500c502012001841c00d0180c2c0300140d129840c003049440c106402c860502d68010111a000d1005010f000d082ea5000075504100000f001000141c04c008800412007860210100c6c11310800004280401c6680700342c09810500602d01401d00c20f4210a004130705450b40c25113001d02003240d03420090200c0d664212800408404180400f5030006c02c081090480d44c0120600f650703c1e41141c810404819014130a007141e200680c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377811591 1250 377810341 377810353
    0x20a1202130302010e18010b0a032a0302070f020607050a03021e0601051905030703030e0901270507031d0703110f01020d03051902070501020703030f020906040603051b0a0207140102 80
    0x1c1d6940c001c1142031002074100640b499104400b601c0c0d07544800c01005010fa0301c1c0005603160380c00300c01e25511940342180000e2a120701468038400780145000040301c8201800f5810620a1044029403c214800d440764410f8014000050351250000c0045602c9000604071901e05030602078203003a40c00c910f00c6a42c0c4500040300c4490b96003c500c0c2130544008803280c1c07407084407a40044200005607000f05815106801012060581140c0c00e407114040c2280e00703040d142e88503810301c0080102c2c0d41000380050703e001640400013601c0e0300318991000c3e2918000480c1403211240020403221000044016006a042031003808441d00c940d0340d0300c09007a10100240c000c060b00003543c81e00d00d03040c10f80030035aa41c00070540d818611400c1000e00e00e8070101c1592119514240b1f18001c0d4810f0104501084c68504410041201d0340240e0707841000052807541400d1070604103502030700004014048500c4000c03510000b4103040720240c07020f000b50750b005040c6142403c801d201b103050305200450545d40300e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377812841 1250 377811591 377811607
    0xf1202030115080406181401110a050d1812050903010e0f190c0b0a09060f0305090c0607060f05010905011a03060a030f0f0b0f1504060f2606070201020a1202 69
    0xc0d102120040194584a1050791366814008010140c0740e010107045040f142d210003d01900a90801c102440c41000f008500d4803030004141f6889003001543c00f26506122212524607598400f5180c0207081045001444d00c0399130ba02d0742c03544806181e00115501142da50441e08091107450348a40d40140206480d031044880569140c5d0f820404500c03482e401440c040130015184d00348401058a241c41c1c83c0c07518405c41c0003908400c0c0384c2c00b410700082c0101c0841c0034940d201c1e001d0700b4015003005014100c178101314001e2052641c0010000d8881686403061703600103401301d1064030b00901c88090006041d504208503200f9403039032010301910702e8809109100f0296611180c800449510091f0ba190444052800003c0000460300c00f4143c2c40c4c0d83d03403c01a002e00d41a8981d4803c0e25000130425840c075204080008407640c5018070401035201d07103c10311210016101c03640d44050301414150310311588104079807924800b150319400517500840c41d00d040641000070f4013610388103000298102805 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377814091 1250 377812841 377812859
    0x801060e010f0905090703060e03070b0901051915120f03020609030301030803280504060506030c030d021005070201020c030406090305060a05040203060402040b120106090615080702030d021305100f12020301 91
    0x4140140f80d616035031070021420904080203c2001158810010b0090b020401681511380c0c10281d0242c450502200004080c2d03441807050b83d120340c0c421f442114001403841121402005945810032410900b101c021404580038100404190720036081800d04803082e240080c10004041e1480000e80d00a10040c000035003075030300307807030f446a000000d00c400c250300c114030710341000c0000d00900710143c0780c0404d1009000c0c15410540c03107039005400300c1c0d803d42d603800e007410386d81d01000700b40c1d40c016000341d148404011455000320b03400610038030000d41041168010142980d0003580040007040b00c1140800c200082408010780c480080c000400a615158022030707207503000200024410f030fa613182c4400090382e6170212408040d0b9007a0080103100e440e000d0320310040c0030714000c0c603c42c980e4100c0c61441403407094822503c80c0c5010b50281d418031030100c1c0c0d804040e4000c0203c8029a40070004041101d459523141d102007460941e40319402030b1140000030340041584281010b0b030500400041c004920 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377815341 1250 377814091 377814119
    0x16080601030303090203010f02030a1415060f0919081f0c0f030b030a14150a0507091a07170a0e03011104180b0306041a090303060901171f02040801060e01 68
    0x905800c0109400e1801d100290050551140c0380e02315610100c14400030416560020380000340480324641642c454000d40340c0b540381c0464640368007170000c1203c0c14030300300301001800c01c088010b0008442c60324500c41c02c000c085d5080e0440e5020350310409442c05c1100311100119400c00800000b00300b0304507040e1008050490b0000c81c0d01c1410b445440b040c9660724104500601d01d9001104140e00b10a5490081d85480c081b480d0500b0702100000895000c6410740304a0f4040c0707689803960114a49011401c80b020210480c085020b61007d00000d80890307503950440041100b17140540707644815803d80501951440702c8800e00036850840038098110190044409072007619003d0302c4003130740b0f0361005009440030749882c1d40c150003074000340800c0040f50b8820a0544200841902540d520050480e07500d000c21504c2c15444035200004010684400c0301c68403808039040c09071200780c46c0035000c80c03412002001d0021a110345c002010461240f080c86a00054510111806e0b12549841c4616031465 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377816591 1250 377815341 377815343
    0x1306061502010902091b0f0a170403050a0909110301031209031a06270f0c040503100209012303010e07050706051f0503011419060e1f0b070203100902040b0414091608060103 76
    0x101f000650ba0007145d01601c1140c1c100c05489185c1c03826440c051034010140d8104405204c04a143c030140402c1080f50b50040104a0f115540101c0c11607107542c4421000c500c20045140030300c040c00002201140c002114406a114440156140c030b0070800140071040c421181781380c512001032424083d9008100c20280d0700b10032491507200484c0c844070350000440c82140e10040d4540b01d102a00c0c04810f455802030302030380f242601d994040f15280c3c140000a80b0540c07501035984001013006102040034401800d40190035480c0c07085c00e059050781c485c801c450003950782c0c000003000389070322412043e007041c000c901401003038000b40240070a501110700121805401c2d07401c03a1160003003151700c070ac0a5a115800a024500f08410b4a08040801000603800c40300340403034035400000c0225200800b001142c085aa001e402011721004000a0100502007610201d07401074590b800074a0300c0d5154001c042e2420900030b890b041c5030910300112450300d10032140021105004103410460f115010031500d04403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377817841 1250 377816591 377816617
    0xc050c10030b06041707050405010f0b0c0102070c09020c070b0f0405120a050601030b18030f0301050127260f1e10050109020712080603061306061502010902091b 71
    0x44000d819007940642401085036030040008038000900b4404110041a503242e07113026281901d0302e503000c1c4000c2d80c80034002c94610201e034000c00c000490007600203202c070801840c001400d004040d550300c200030543e0b40c49150401e0f008100000644420b210303100007014003201c1e4901d401c10f161195a0349010340e200b0341d48100d81801c1540d40802084c01002551903000e0155881c0e0b686a10303252041c4030003034070b0300800c0e0b0f0302056410314110000411501c42000c04034000b03040d41e190000458203000310040358054550303604032244461541400c18006840540100d500a005034841581c0c015181610300e0361f41da0103900d098502d858003286001214118050343d580980da40d080284c90064102d1a4018940c503107000007540c1e600d075501401800340320f1a419510300b8060b1000b101c40c0002914101e500d904243d021603200700000580d030f042140b050f0408900c0c242d89000041d491981f011304000540d440750011011460a0042141d01c1800e0400c1c44400204541607002c06003d091035003030301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377819091 1250 377817841 377817859
    0x1d01080c0702041e0212130201170a0b0d030503061503040f08070f0f110a05010f02060a051503160614070510020a0504080d0c05060709080c0d030302040e0a090b01060c050c 76
    0x2d540720307900480ca01c8080303c00c2d15024800218a210000c0d031101c0c0c3c980b0650140040801d2490421200541c1b142c2d40595881020030104442861890005024810001c1d610651003941d516212030440e020782c025202c49884c2e00c6c10109110101d007492843c201c02e41d00030400c100015901c142e800a01f40c0c1c11641c1303507072944418580031111452166000d000003105030000010010850100400b00c00705598aa501d00c0d0386000645205503e0007098000d6084400000e42c00139807644015840000c4100d4403d401d040703480800d08060299428a400e441030007000c2c040320342c004c5500d070300b140b9608040e10b1905915845054458019004018159800064841c825031041c0c0c20345018144031802d0b2403440340c43c134102a024a0030030000701c3c0d41d400f0360030000312864000c0402070100ca14030005000c0741c0031214100003520403449000c5040c141d081c40003085074500c0582d0203104070320383e400008450105080c05070404078160b1184080020380c282001c000f600100342d101c010442540c4a2107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 377820341 1250 377819091 377819093
    0x3030c08030417071103010c0305071205060105040b04030320120711012109110a0602120f0c03030c0301090e0307031209060608030c1006080106030534030f02011d01080c07 76
    0x2a820145498078140c042d0101c0c15070180301711040509840001140208001e2921803401e5044d12400c458a00100c1d49070740c80d01d01c120b10710390009980100140b51191901e629020a429a600035400a8000661035400f41c4002c0905103c151034184c0071030014042030b15864840541c51007816401811008074424020190b40500000300c0c40400c0d001a0072200c1a90b409101e008104282d07064402180300d403017482587c100200c070300301a10341c01e5000c1c282c1d03000354419440944e8046150220428410014049013141c2400554001d82c2d40c82c0e03000d543c1b54941101d0314192000450441c000f40c00400c034000000e504001e403840700b45920000400c000081c3d04210009000e1a130060071719000000781c4085140b00860211818000c0385404c000b8544c941015078200c50721400006d04692060302c400300090302541e004400110740d0501c028540e04600802d004806240d4030071034003142001c01840856030861000581c9420a1100f081d69000510000341140400380c415040c0c01d8000230954 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 377821591 1250 377820341 377820353
    0x1a0c030c0703030816090f0506180907112406100210092901182f0702040c030b1323041416230109121407080703030c080304 55
    0x5180885000545600d1036403401d02a042130310855060002c0703682d0712000d0740b005010b0910343d029600c00382e603945a82400c0205100c100c2e400541102210701d425010b280c0d80e0340d1521a203520031001641c41d5645601d0210b00980b034a200404000c1e44181199500d1003032003000402c3d1540600c0842c0d50070241419144103030708000c02d401040004608040580050200c41c8031a0f039200705004010f450004040c4003102a021400c5c06500c503e5555604415a2081160440382c0e5070390b000d01c002081407024210311607808010f0b010705c59940707001003094400d52a1034440c00c42000c0300d40c1001c1c08080741d8200010310090b80741c4282001166a00724400d52400503825180c00100d080765440c90342d007041d051015231080b1300c41030101b02e0300c0341407a401b03240e4800405030700c102c8964240c03940d11700c10300c18280000c40c030540045504000340400006811401d4240305c02c01c0500407a50040740d070710f4241d0101e003804c00c1c4e500400d415603c40442040002ea002c05500c40d04c542000d40e407078407a00c1c0e40c40d01b6 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 377822841 1250 377821591 377821597
    0x1080a030f0f0c2d050c010f030c020a20060a03060801050f070806090a0e0d0c110301020c030d0e16140a09110a0309060e1608010605031f0c0201200d0b09011a0c03 72
    0x40c40c01e0b04c2c00c40d503644041117000910741500450903221490781070020707030088081d901d003c600c1400603040740701d0601c0001c40c2083d84241d400485075a84c040000c0c0c08010901d0380e04441210320000f80c613174804016084080c400d080e0010102c503407200d46842d18050203003030032501800a03800b546079000000d803100e0f000e6000042100c001000e990b500c9400000003007280c08104401d8440304205503140109150510031184600c3c031920107141800000503d050040001b4110351a290003810080080360401c0e180c240301500112010038091602023041c02100e020702d402410205141c54925200c000c00002903640c0c01106203004a2940a203182c910041c0041d001006098810100c1070700e4070442620361031090b6520305008009041e6150105aa120f00c0801a80c5002e01c03011090301d26403040fa00320101c1c4403404c0c000811039000c1d1001a04860300c002802c071201f02d9012844100e070b031000340070f218041e41013283d2903280380d410004076100741165601079402c90035000407049844007080c425 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 377824091 1250 377822841 377822903
    0xf0c1204021c122006160f0203070609060603060b0d02090c0a0201150e0615090d02130905060109050a0e0303010b030a0203060a120803010f2702160b01080a030f0f0c 73
    0x1075041d048580f000a042040050304003100342c2c54200b00022110130001e5624446c010740441c40b00702c1440c0303010a9884019071094041103010400c101d0b80850b11902954680e544134000010300289103080450440b100d404041d44240d5100c3d05400c0541d5545810350b4022401e9610303113a940380400416401060202120394040041d5040040c808600503484c500ca01d0050307a562188c4280750300174a21520505a58941c4000581c000f04c02600700f5044030044038526100000d12089903440e41c9142540c264802e510058841c010001c942d46c81d809001d0980380000c00442c00c6504003024074882c0c0c00300a11100c104d41e03001c070020307100380d0f618143e000051050803a01c03001c6800c24248007e095101740103060303503011040000144410550000745056050720052242150306a41039000381d80b1000c0c003003141603641d500180100d181060311034001c000d54002444080010700e03014110354160038800084c441622403884009403c861011a00703503011415040d1200003039a440340848030803070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 377825341 1250 377824091 377824103
    0x13050907051204110f01050703021c2d02010615171b0408010537050405010b10020106140103020a09150915020f120c100f06050d0b0f0c1204021c 64
    0x203002c1130003080c4812404004080e80c00c103416040c4500117480e17500c20400000d0050780590f0f8952603965000812103420011890000e00112a403285205501a1108002e59a03c40054402078258091060310b000f0403141d5041280701e05e41110280200d09015004141c000940307001410381e1011a03285500c62402020542d100c0b44c41d030f41070314000c05d81212045803d05110090700d494086004407040b1942428141d190740d11422070050000e000c020340102c42c19900c4010340203480ea40e00c070402611000a07800020054500340030b030b0f030111440243c9641814410008440b110342c0c0240c9000940c1c144209140d4003c0d50000d0880e010103013a03011140d140740c01e0b011a0380c03090707000c944030103103a040808a4142440c0e02181680c40d20904107010300e242d00200c0080d1380c4464607084501800c00c500c43c0050322943d1140418001e220b014030481300c01542004201c82d030500005142d0304201d4102059042403401081c0610b41d2201600c040e1084c104410f04003204c0e8110a80c141156901074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 377826591 1250 377825341 377825377
    0x30906060f030507031a0408070f060e06011805010b03060d14030f040905011806080c0409020109050306070c030f0903170715150f0503030c07060f022a13021305090705 74
    0x104101307440340784c50f01088510140d01c840c12580000070741407450207280c20203c0f05141500541d61004140c0c610002110210380b03403003400000040900c9058000d00418412240d4100070f0034542c0304482c816040946000d00c103105000d065200d80c21042c5685510514000031110303c4698140340d40521340c0786404031030300042c0110700180d5a410043c100d039160300406000105030104c040c180c034224058100940e201759030726025803906400c12a4098010f0402080d50317600d0f8404a814210101d50500c00700d09440710390020103501500070800103805142503031000e03003180d4602d030031403001d00845000d004003c20143c0520440c5103020030117418040381000700039520b4009002c0c2c10000c2c8078078656100340d82c1c00003c950801008a0700680d11101c09042842c0c10944203032030300d00d0b41c07255940c114403840451000f40441d002025050181038840e030302440000c01d040010310320914418444c1c150050241809100001d41148182c03402241d0104507503507140700450b09401031059103800501d4003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 377827841 1250 377826591 377826593
    0x406020304050f18151302160c0510090306090c08011e1803140a020a02060d0506040c0e0105121f06180609030206190309020d050c0f03011506030906060f03 69
    0x1402210010b540c40c4082985031401c0140b41d50544544c00440c40400c000250340b0300c4460304402d00401c2c01020001a180811804000c03a085103180101c400104101001445408218840280b508540c111219140c2b4413001f081115944002040c040d25440801c08001048038010301400354030700200f01028a030b0074007051504134030300746007800c61400c141c00c0c1c07542c0002c07860b001c009501602c603003901e802090300740e6500e03501c0400d001045018044180c40140d88020081143c4008094041820700780f020400089880e0800c40c00103010300700300880410398000d4143c407004c410824017480c41c0e0b590000c007082c0c281c0c454043d0103811940f000d008146103410003078251516600c4441141196191700c3d0588111000c1e01020b0340c070803020300040d00c074007071103c511802d04400f83c940030821052640c0030512840d0354003030440b904e03048070100d18003500306030380b000140d203908400a000d40c441c2d2040042441016001e44805c1644904c045001d00185400c404010980c1964640c0d5003962 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 377829091 1250 377827841 377827843
    0x3030f0f07211103090a0b07060b04060303081807050d0803040204111306180503070506030a090b100311101b08090d0b0105030601121205180406030c0602240c0c0304030602040602 79
    0x2022419000303c0c5000c0d400360811180041070310a1503001034120403807603040c00700051581d00702140413214185c4410365420141c03503d00034040118440d80300c0801c6810042e15041a0914080c4080385c40c2d072152404104603030f0b884009031000c0d80c102403510341d29140c5001190242481e45091903440f100050b111010440003402e070811601d9031350b0340704c00c8580c10312440c01030003c240c0301d0150300d5880300f00c051000d403601000944c0c0100490a00182c200e10a684000c100ca00880d2030040640102200304113106103417082120b0400100c40d03004051410040280028054a0040c90658180c4054104104c5640200c41c000b040007040412110010b18003c14034074800d000340c900a01580c400007400f032181030503003011103a0083c4441d152108450040384c0741c0d001f50080140c1042c83c40400700283d2510300c030300c101650040150101d103070304100780079103014902c2d444d6040c24204c15105c41070150301240c8194120408031403241c3d82d4000080103920b140101d4001034901c0344001000258250 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 377830341 1250 377829091 377829143
    0x9020612160f03090839030a0809010207150507020102070503030901020409201905040302100f180e01030b040206071e05060a110a030c02030f070c0513020903030f0f07 74
    0x1c1d42c90540c00c030340e0b200c0b040303040c0c606002004105c0d800c148a00102c100440b00c801d11744eaa001e1a2504201710300d02c01c00c1304524207440e920202c80d000000c224410360b030f0221043d64030081e00e40081d40303440c4040d030303038443d1008119015861080d60b410114260034400e404640f03001d0703000310480b0385038108105218001d42c07044c03069000c014600349c104451460707101507504010407400251802c00300c2110018a011480362060802c04c8410400030006a80d80d5940800c240346a580f50715080e50728031400780c0010842c0c02c1003081c5154030350f41008400745010710703627041d0799102940c8681c5440307510220700e0a000e045002451b5202070418510181c0c005495940c001d8040d000b205c409454600380f40d0101c031411382580c00041400c0290382607a5000742c1207020501090b104803407426050141100711600700c05811290942c00050421007440c0c440c03010603070ac0300142c40462500d030200d00040e5072071140c401e001c171404030003044000b030908001c0141d66415801443e5803940c0b103030010090080c80 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 377831591 1250 377830341 377830381
    0x1060f08010c080603150a090b0c191b021228030f03092a03061d010f0204051804080403120302040617010e011e090f2003060f0409020612 61
    0x50700c0c203a0b000004034450b100c4240110806000360400d000301c00d1354046d09140c01050500c030292124030450008260305032070b500c2800c80c80d05160301c8035801280d507101a46038984241c100a0504408000070000741031100c4015411505000c9200340e00010f64200450050544035440c07220391415a84150041d0100d00e1500c00e80d900c50311500c0380c000a604585404038060444006c04031760315038401c0b1783c1c40300d060707100301604900d141c071656543c0344c20a030b13100044031826254412050f0750300f0b0074007409901400c641c4d05409508183c01c1801103402c142a07810618084580003012409110f40101103c1c0a5a04080107490391694154050041d42c4503200d5100041d040143e005070100300401042d050319070b002045041a441e0515020700304042d0310050840b00004440010041014480e0b0380014070340c9000403070400030302d40030000c0d98a4003480e04a0008030402c1040300700c2e5102e41c0c1c2c00d124003134121030018500c1228008902140588100c1506120800041c0300d4a660b4151403040c000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 377832841 1250 377831591 377831593
    0xf0e03040f0906060c08360319150c091a091c020f040e01020f0c0f070b0a0801050103272d0c0905071b03080108060c03013501060f08 59
    0x465452180000702c0703506100303130070000741c4031105440050740c51402813420b40d6201c2e42c080015041402c21010945202d00201120b000051060b010340c00c0030303c40f00d00a00b504844079503e10381141c44035401c02210b03c1540f41d880b561660b20f028058000c030300d03c00140c401450341800c05421007041a405a10100000b0310511515039004440e110745080d032080194003408948084884d1b0041c440500300c40d0841808654090169190310300030800138007001d070440340c0146000d41400301102d04100064200321605481009070060903508000c040381152001e1074001070b042401c8108800c10095050005240b050454000080c85030354000301c0030041800350f0481c0404081c0d0001d82e145584080c0060408c28900010000300000385d01081e40300702d881c10030750f0803a242d045501520100310003084011900c42801401242c104011701c5a0001c00494418034650418076400300840e01c0c0f08607070014081c92640102d140405118075840d11611074000d0000c90344880d1004aa01c04a005403691 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 377834091 1250 377832841 377832869
    0x1a0906041a060d120e04020c011b030b010215040c0512060708070906020a08090420030411010e0d11040f1506020c0a0509070809010209090c0a0e0d050c130f0e0304 72
    0x446000d40075480d006400081c080c1c6030840d003550328002c841414256480500803080c1003503455848600040c07081c5c031159000024028910390088080b0f44242002d54101841c242d41c83d40c40d642c0024111600070b4085911b41c200303550b1071826041c000e4131600102d4001e80b0f0030303407440c05031880003d04078003945142c0c94440559403981c0c0c041354102c02d6889a4001030340b20180c618085818035000301804070004d00080364050030794203c01c0743d03c1c204010441c00480000100801d00c615400502400002440d200c0d80818441002608140c0300c50005002c081e080640030369560346039070001c0d0384a05410020b01c402c5292031074441858010f449280b0160007104030b08000c519103181c0344002d9410050110b5142c1d03c0700903080780c0901005180c00083d650800541d00caaa892042503071080404241303280e59140792245c000c0c40d030002c0101d090b008039187c2c0800c2c0700241020910340802d5009a80c0151a00050405480501620300a0350340c000c1c50310a400840002c00701c01441540e5480c0a5040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 377835341 1250 377834091 377834123
    0x30c04050d0309080f0f071401020316050f061b27090a1d120a0f0c0b04050706120b01090302040f0209091306051b0a0e0f13060504060b04030b131a090604 68
    0x21b00d410b00c2d0b4113404a95041028280441d01100c50358a080240610403a4140081c1d90642c200d080381c048029260383c0c2c030011150403002d100f0000103900003c100d030403040c40c83c00c0d820859290301a2a503565030007180c2c0001c4081d084224000d601d01d000307000b13000b61054241118111300030f05010420015a03640b040e0344031640039000504c8070302c1c000190740c800d20b01500d4410468103940160301141c100b02d0740d1038031000480d82c03071280c0f280540e004e40042c1415614216002d00b11368103e802034801e00d0b041080520060b81c20048240803a90141d4000c1202c40352801818028810304030f54503880b11094040c40005030143d4044413405100f400f080045803031f1000400340c106100100d607034000108202120303d291141d405c1641303505003d07022400184c0b0000000301101c600b6041c66184965a400070002454603014140080a00c54440c0e480c0c41e00315181e4141d5400300038074024500407540c07000c4040084080c807080ca2403148400e81c2c5894100b00c8210b039107500c030503201500da81f41149c2040b0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 377836591 1250 377835341 377835343
    0xb04060b031e030304060b060403050601060207062006040b060105041d0105030c190b07030519050a030c0e010906030518060f040606151b0312020301060302040503010e21030c04050d0309080f 84
    0x14541e02c0c02c100c01981160b45a0780c0d25005000417010301c41e00503000380070000000754100185400303440d494024100c56820100010321001100e1f10f80c04441000c0002094200740104000e6006034100c0c011040664820b0b00589040c403999101c080140001c003a110109918a43c0c454142c488c00c806a4400848884c00c0081c41e8600040955041911820400c2030b240380c44d000b8444503109040c02c0d400e048624480049500e1444143e6000c03410000702c0d442c1441d03040c0320b90100703043c030b1303040a03040c0402c524002809040940180420f250b99400410303c80e80d41e410b00480215401c3c0111400707894084c181c444481d00a4408071a89400c1c00c9010030810050b2080d0b808bc1880c0f80c0d207440154540480180300171084440a078148031840003824000241030000714060442514056600e51a1a003403500b16404590780d008580c000c0c101c0d10411110320082200e031401c4031914540c8944503000e400034144034641c082d65202c2d041c450a4000c164002d5150021164420306940f9081e4040c0003103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 377837841 1250 377836591 377836633
    0x30e010e100e16140d060906140f071403010b09010e060703020c0a090605030c131b021c0e060306010f050f070b0f090d0f0318021815030d090501030b04090b04060b03 73
    0x81c0d128161502c824480350034100c034203030b170303218010300d40441c002e2003035110342c01128000042d800c2c85030301581c2003195101c8284d460703d03001174151424404801c071803141e07a1541e000600410031484070018401c0f000c0d03031107096080240c0c080205521340c2d03143c4518020b5500d2020f9440d00c2e000b07212503038000840342154031560080302c00203805084400c0f005820032100800710704188034620b03640c00992072514040b1200003001c12654006002400840b4100c540000a41c142c5408001659171406038944820090f01e811600070300b01a100b0101c00041560a401818281d001d00325022070850107226003074403854080c1003002c244038001d440ea00c0200d510303100744d8401d10000c901900b904c0781445100e94080a14800745e125544107100ca5507001880912509032404820740034a01404000c41d0b82c001c511400c044100c00800f00b14001d603031301034080d9043d84605410b06a541e0001081d60301e9582101c1032a6034028a20515032519240840003400f042c0c0c1218064850f070300d6213000c4081103580e8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 377839091 1250 377837841 377837849
    0x4020409050105092404050a0f180311030a0c020607020a181e0b06070209061504090209031006050108010e0c0d020403030518010201050106090e090c03060c0322020907030e010e100e16 81
    0x45142c08417660000c1c040604005880084010790314000c00c00c2040300c52241c2d1f188080d2840810403030150340d09004103c0d8800070008038540e00304201d03c04070710740c0055290010301d40c1030b05c0c050344072001c900000e0030340c100303e5000c0703070000200f01001211003601e86d12200400d00b010703002c4e0000d04169003001040315000940d45030400410019440945460700c41d0540c49003000340b14100c0c400c0c000046840740e402590081880c281c000c035400040c1d01c0d0501c111140d21191190410a507850980028100708040c0f14000d69100d85402144071498004221601c250000f0790644d515a940d184c004d0090703000c00e0000703000c2049248a10311079031040c042c590490350141e0b1a074843c541000310f40c00c0b0100c00034040b12007074400c100c19003140b0303141404070302c0c418240b400333a144e05d916280d816101d010128803441c403040000440d20a00682c0e500f0111038104040740350000d1000c1e143c584150051025500c41041803043e50750390b00b81002103400213141100b201d400e849080d02507208000040742c00c1d0103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 377840341 1250 377839091 377839141
    0xb070803060f040f0c030209011d0a061407050a0c050306090c01021c2609070b0a0818011503200303033c09030a030608030306090a05060f0402040905010509 69
    0x10032000e1400c19111884004000c3c000128a84100032120464041803112000f00c0d401040c49090303982c00a50602502c425040c0d28042d920301a00000c908085601481c0244081e805c00391903c0203514060303910303aa40c0001100d81d528454102407002c00b0706881194403900c0707042e0001e100c011010444070100340d03041c0c0041800461410140b2005212561018200301d40ca816000710621030b1044200c1001300080b80c60345a082040e15941444100d03003020b003030f44100704592051a9801001c05a1042090740816081e508121036035000d44801d550320b20121000d8070380441030001ca140c2d01007aa801c801100c0c10030400031428540c980c0011911208c000d28200c4402240f007100d0701f10026400d14880f940700c09406071103a01c0341d00c91010f40c0c041c000c1c0e80c404903004000540511501c00a0301d00380d0029421031509500050030004000d08210900b80c4810200d4400c0d240c4004020000303200800a5440b00c0d02c0d68800360052809200b03442c403030700b00d04020509005082080342091481d4503 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 377841591 1250 377840341 377840347
    0x80c1f0f08180303011815140f0d231e06010306020f040e0103060f0c1d040905010204170606360924100f05130b04020d0c09030c0b0708 60
    0x14006403035920000702000c20781408000800d0310b11205000860107025a6003120210340b1159150400719907424192000c1e00b8a054020301422803480b945100b43c090440c0c110364607001400200c2c0250058a000410182e00601407d00007807042c032005080100c42021503100c00044005030701c00005c00d4050b800300c0c0d00040c00600201e2000d800070622180595480c03860700d961001c0c01101503030240d00c250b03505aa16062100c295070540650300c401300c00c41c5030408001d0390b10742c000746030100c008240c144511f651300c000c41c04000d07081d01913070001c100d40c030784040c0c00c5030020b41c807e170722880704a640710720031100400000c0c14407101100e135801d5080f948110404680800024080c0a84080d100840380e00c00e40c281d40b1b5401121159a075600081503021550b1030609001c0420b07250fa0342d401101006032900000d2105032030380442d161601d00405004107140da1500045402031040c402d010080600703001c24110306541000461003264820146c1c41d01c559901c0b01030051078000d6000080c140e920070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 377842841 1250 377841591 377841617
    0xb060306100311070506090303010f1406040b07020f06040f03020307050409050604030807020a0c0609060f0201090503090d170705030405030601090e0a0611190e120a0b070302030718080c1f 83
    0x7603100f055507816245101d4500140754440303a143c1b8404850700c003002d910000c018400c082e221154480141000040601e903103102c000060024012405115001d800c007088020540d41d510315507549808020f4003496445880351880d40305400b45001c164043d205102000035075080c284641da611fa0b4204000d800ca94a03656000c0794001d50282070031003184a0801c1c401c01160f11075641c86c00405440c0c5994036864545000980b030f201c800030800d803d5914040044000c600e010003210255001229016403150507483d00ca03414030f1009081c421094408580310003002000030040080c1c079400c43c1200c0c2240c0c2e8503c0940d003a04c850707a881c03542c02d4025140d044001160368220314604156040001e00340300f442409541c0c907107070101190340016404030038403805007010035801914000d40e1024201d000c4060719034034040310028109108042c0c0c000005000144154560782c40341031841c6140c0302c41d668034070a01780c0d601401e022643c800e0340c8030621501b03079a25590f40c0c00528002c2c2e4481c00b03140e00321 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 377844091 1250 377842841 377842847
    0x40c051e0c07090c030504060e15011509090f0207050708030f09060703360b0a0c0b0a0902120703030206130f0605060111031605070f030c0902030601090f09020a030b06030610 77
    0x5800c0c510500c10040c000c505110a130040740b40501c01c55500140328605402e0100940b00720211180140e007009808003120005c000313403e0f0550b4404041055000041082250b0000195100b1080e6238a8801e02c005005202d030014070101d0300550803038030404c2d03c030104075071284288100c00f52420001c0203036900e141400c0002d016128003070304040000c0c034616100d00071107494040c640064400b00384e10304c0c000c00c0d08852140b40070b0a1150940f070b007044458000640349a84125018200328815000a0501d0b103407038005104a03607010b801010f01074586011540c2d20b10007404210058000e92000030000250030727000c80c0d141c5801c602070000d10b04a076120300b1300401c03011744180e042082240d100d504521007040185000c000d05079000c207980c10581060b6003829036075080507814900c3c1d081c04101140203440c0407000c3d100c01c800016600e84481006030350b01c84050b44402042e00b4071210010f55015a640901b5020300143c070f05001e174103407a8081200c1440103c440b56403000c0384122090710703a48 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 377845341 1250 377844091 377844097
    0x170d12060f090902150910030e0c060c0d021506010c020105071b08030c01060b03060306010302100909110901030c0315060507031413080d02060609041e060e010506040c051e 76
    0x52418005505600e411100001021642100742c0301c60301da030441001c600b041c80000c1e80e113000419040d03080401c4d0400082d401122014107408140d11000201110482406030650794600103020995a00c5050700c8030352200c410b40504400b6019a071300381c8000c1044445540c1c85541d0594880326820380c2a401514250400c0380182c84440400401040c00c14102e03440f0b402828081d80150749412560100600391810341e04007005009082c000e000750354030b00041c81e07415030398110b8140081018440c01214984555800041614101140c8194880c580802400804002e0703909003d1450315000503415985501141c45040348407507030421515100360068580107200f031805074089010280344500b070b50002040703c05044284007081007911b900b009184103010060000c0c103824549500010084e075002003028012100604e90010407885008003070350001e620000403c84101941e910b680241800c441036400740c0d00d403100201d20356000c0c0c410303203607610070895a4811103201c03040006402e070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 377846591 1250 377845341 377845367
    0x20601031e08130303020102091009051f050f0a0818060f041b03021305071803050a0602072307050f0406030b190b060a02010f1506020a020907050d0903020313170d 72
    0xb4018440002880d0015039040c0046000f03600140c0c40740b88a8080203030b480400d120410600043c45002c010a072108100d40c2c01361801d0460b550107500d0302c0c1c101600d6070b10842031040d410900024001d43c01325040825907000d031103290300754000503588884056507030070305a50f502c01c204440e0700050700082000d0b0520100e2000509050511540c07680462a40c0c400c0c0300c0800b217150b8071002001961603200040070842c001c110440785080e45140c440c2d42d100d2940031005002283c00240312814811040c4c102e50805094000841c407060038000c0c1ca41d10f560603405001e11076203008165105078a00344c000d25054a401406075441a103c000030514001d46500c0006081c0c2d4940560550356036840b80034109561490f000810309006001d00c07003003102c041010325402091100e4081c00869400152103d40d20b40c141c0f0350564036215000300751002d004801ea10919907007081030700020103074040060032400d52408210880151a03400109020308000e0000070b81d980030b80b021800e058030410b00c501e428 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 377847841 1250 377846591 377846603
    0x60703060503061f05030a0c1a03010323030f0d090b010605033c0702160f0b0f1c1a0102010b0a1505030c0421020111060601080a09051228020601031e 66
    0x44d50f01c1000c00c0c109513000f07405588007022238408101c502c8480310705410910004402ca0703c1c44d811030ba035001c6242c41c048490801e404200342454001e08040044519000d0460351254840c0d0425044101400308108110b41080c885000040c1c0140108140c0707002c1c0140d44810314480b154000148807100298418402d032550011400d04596610300190380190480c2c1c1c043c11011001c451064550066a40890b92414025808028000001c0162131201d050f0100842d40c5001082d95140d10500714030081080c0383c6081c0740061b04000206440018400a80003031181090b01c034100030a020a03846000c6512201d0940035942500c9180255407100c0b000c860a410183c5910082840b84070460b0f5115401e48051005415503030081c1070390070107803142c1c0e00508880c902030000911841010702400b01283d01c854440040003410300c0340e000b800320602245500c48203400380c682c136100b00080103a50120030340083c040607144081000740c10b894015241c49840c06240c03c0d8444105841c11003a102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 377849091 1250 377847841 377847901
    0x3151812110a08031b0415021612050a03050f090301140108010b01080105090403111903080f1f0510090905090c0a08070b0301211208061314011e0b0a1106070306050306 74
    0x1d041f1050701c0741c000b0f10074241d00600f0b0303c0d050600d0400c04540144c0100d000741c600c00705070b030000410003e1003001c0c141d407600d810f9840b440501c0e84000c0901681c2502c540c55401e01e1400400440309450f020b0407603c600c0c00034000702d1010001500d184600f0f001351a049801100040c0119020340e01c8240781000e26021628849056020301e03e0b1090410011400926007600f0300810ba0390012019801c018894089000210501c0c1c01048410152040502407070300304144412450207958080d004182c80c4609010074a03090480c0c68440c6c59074001c8501c41d01c51080085154a4002080c10a8603507206000345541d083c120590000201d505116038020050030341d000020320840c4102a0340305458031090b40d036061180070842a030140050003001c542c5401550703414012107087d2181100c18040d4020302ca0000d001000d80300d14007a40000c1580040051180480e1b0751010140170786000000a03202c2a0b101c02d64100c055540314418030741c0c981e100401080260681484503a0615150000424 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 377850341 1250 377849091 377849099
    0x7030e1b0f1504030b18030702460b1608090f0a06050c011b1b020d12020a031403040308270607050705010b0f0a03151812110a08031b04 60
    0x310320300044040c0c2800b100440d08004214040864940000d801d15141c1d8100c9404003006a5900a4105c003a105401050341d407840302d02c651000380d03c0c5a002c24a00c420044540065071241245410300c3c11140703c0c1414000303030040d800307400d5034a112181d04410080c1b08668070343c42421380140c0039540e4095001410500a0741e20b9040c8a4018402511942c6d25456403d908908445083c21104000c600c0c112590400641c8040409641d40042020280b200614008a41410700050005011505480709007444a40014003008510300c41c0c3e8402000c24071100e82d40609000507140140465119400f00b04d130560300d03c120701040740380c0d04141180307441800b41043c0b0306041a50444d021900c00550203050003020301418105400568208090f001c600010030f0072800c40f440b01400c0c070507692000f0405044039412900d02d903504040915002100d0b401c0c03624050782e04101103c046800360f0410209407202260034040c0e1a0044003503800c41c0d031f9691340c2021702000e440c0c04c03131a03c5100f040049 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 377851591 1250 377850341 377850349
    0x30201020d231309140411010302250c1802190f11121b03040b0d05061c081308010b09010501031104080303041b0b0f0a0507140a1a07030e1b0f 63
    0x70b2a40102088081d034a0241d500f13003150340c1548600c01e0f4038070180410000c901c0c96501840044001e180061385c50307140040c0180811800032030244108403203040f0302c05004041c000841513075a8614504001da1003000d0b03842c224402c0c00c031030318031201c114132103569240d014000f100251500f608101d075001e036a4491560030a025903025801c580d0001c1a950048110410350303c3c07141e030000004515050402105034524010765000a041540707804c0020041c0e120750b4036941e252081242d00c04952102460701c4681e0303810001e01d421085c41240e0000070110014021100120340280840e42140d080100440142a41c0184600c030100200400158480308000951003140200094090403140a11114001580c4da002c4d182051041c0403034411002a2800c50380380c2d0840d8240a035a61190b0301c0d0030002d000841042142a0268030790441c1440001d90780307a544281c4403042c180c101e030380d402402d904817a02c500050929501c0400c007030404211040f81207002c100c6c000c000d00c5040032140000307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 377852841 1250 377851591 377851597
    0xb0d080309060a06050102010605010c110a030f080c0606040911090604150b0d060b0307080a0e10020409050a0c26041502030c0a090f0308070f150e070f0e01030201020d23 75
    0x30075075104008009211043d4894240609002d2000340055850718000800407150b140b070141c220f1208001e400441d5594006002c02194040d1140c1500f19950a1408207a041000c03142c400e07000b4440001c030107107014400c6a0352250b000c3c00c400e641030000c0c1c00707001c0c42c110010441130300a9682c10044000d0709240502170014495440000d0350b030380181009405980140e03100840900c0140144aa2160018112980480a0f440004a43e681a030303e00d4070340442c0050040d080381c4002004641d00510b038001c00d10420702d20340d0038001c82882841c1290540e0300c0c400c0741120340000c507041e090200c00040303c698010380110b018659100c86000e92034126401030b550b1100d5640e00003026059190496290b800424103041100300c081c0c91516948003e102d2031400400b080c4000c826031082100070f1b0109038484111035070030813a003503082a00304d0b85d0382c1c414007030300b800c03050400c03000191020310166103811703a94103034054000b981d015041690100301c819032108a482e14030102d116286410405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 377854091 1250 377852841 377852851
    0x8040302011d0d23040519030b010f03021806010e060702010e0a0f0e0702060f04080904021606020d060e0c090f0109030f1208070206070c08092107140d030806040b0d0803 75
    0x40c080141c3c0e1450050010100008182c1d0701c802d006032091010240c050940f412144140d84450b00300c0e420359003a11002c81d040e04020b20b4010908004a641d2050000d80410f42e4400d1703451441c2403612420011460b0b00448070f0364005512000c200c102c60400d40040e10b85248181081c005003071450300050424a90f68006100641d08032504002c8003512045540d0000c020307001520242c01c0509660305070041c002c02c09008241d000403809040d8450780c0c108c0705002d0340b00d004022105c0540c904440a503004140c09140c0c0e90034601c01040600d42c40b908140034183c80c51409280001c00000d100c0f81c0e00314052820b0510420850000114440c03000114800c1d10451992800360700202003d01012009400c50702150711100c10001b0207900161030100c1d46030440703003142e20b80c0010400940c0d0b80300d4a8425204821490f06c0c886d100c003500013800d0b0165204400301b4040b000c1d500d802c1c40040c103030419020740003e5075600400d2050900e6408102004006070154041007015107429480340c1c02691 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 377855341 1250 377854091 377854093
    0x24030b18012705040f0302011104030b2701290105041d04020a050306090a02040f090f030c170408011a0907210f02030411040c0513090e011b02030415090b070308040302011d 76
    0x305040406d982841043d1540715810484ca0416040d40c5401008260052240100ea190407010070300305644544404000c2c41010024031125052081540c1c8a4544c6050401c940656001013034896014800760b8017540e44000020440000818407028002000b03042a600041e119101140c40e480030302c082880340e072549009000201c0c8030710511007103c02d0905084441403514101c14000350103408442c1d8140d4151400d81d03039401907820b050030038940a00c0c4011200c0d4000a000481d5507042d00a010110b00843e40c14110740420401d110090740200d402c1c400050560700d0400703180500113003030140328403200e20000d407204c2c424158800b2640203450a0f84c0b002400286540c4919050042c8803070000345150060401c190b040c00303c0180e885a0181c440500d489e844c0d5410848000d41c8120b40c69010030b51140b065a04810300651603501074018600402201804200c040b800fa0a10034101ca000500302c038641402910101d40c0090f01a104904554030340300c3c0790398641007169090340740a084034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 377856591 1250 377855341 377855363
    0xa0c020d170301240c03050c010f1802030f0309030616020a0f0b092a1e03070e0405070b04061b051e030408010f090b060d0c24030b1801270504 63
    0x25002400c00300e01c500aa01e400400356003440352503172103103800020651500300103888900c0001500e01504428003c046400e00c0c0070f800303001030607800f40c0c0d89801500176004d944c881909010815142d2140081c800e03015409803010543e910412051450074180900c1520652806503844c11407001c0d4400d004e4039040c0e003460510080b92014807003607a111540302020718010301821082c4408607a004501403069419503951500d07500515262650000c0003000e80b40102e03110310b05500710890a4030180c0351803190000109010003c90102c80035940c0039112920150031145291103d034848040c102c4590040c0c00444500c226044641800744507088091a1aa42440c0a950842e003002d41410f031210304000c114404611010b024070b4000f4000c4c0c1e44030003060702c981409440100c040d8082800380138072240c400666a603110a49007044525a0103021b018846420010171005401d984036690780c1c001c004024014106c2100719001004d0b80f5040d4040b150b1410340c3e81190070446055840940741 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 377857841 1250 377856591 377856599
    0x5010806030f010c032901140f09060d0507031b0203030619050613051504060917071203080601020d0e220b13090506011d0106050d0b040216031808030a0c020d170301 73
    0x1b90720b0b09611903940340404202e180280002d14005500c00e03200300540000840341110880c80080301d1001102402055481d80785003140001001c0468840d070010340381c80b50f031081c0443c0200b080600580994011819070b103c0408000c10407807643c4544444211080d00081c25442ea1005440041c0703c0107414010586040e0130300c00801854542c2d24180802000f05001444c0c00c10030080aa0b28800403440003050001881445d2601030f401c12455200c003140994201680061114440c1100381c0c01e50f00180c1f07485605440c05122200202d900a40c5504440e4440c0790308800110000c01c0741e0004251114081c2c007199490b80400c0011940f65102c010000070301404100d03150040c10304200d6000c00741d861610790b00d07503110180500005c000c0000340010400003a90040c40c002c1d5001042150742e00e5003101c425651140c005070403070104040008d111260a48041c290044a6103680a5460403103007000464900c190141f00300e80c054601e440300300106101a82d221359140001103a00d84d25410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 377859091 1250 377857841 377857871
    0x7031b1703040323180409020d0f0c0506071505270304080f071d0a020405060412060e1b12030f04151101060302010c0f06021603050a1704020a05010806030f010c03 72
    0x40d26400d213400101491041152100c40200c40e4032601c0704040070401700c14840000c02506d800030020754003001a02400e014482c82c060301039400b6224480c40110f0340e94070414840d01e0300580f00c02828100c0c941c030f504000c5c509140c0240740d220603e500c2598440c01c0781c0004002c02040e00385208840c1e40089014001e110040051009200d0040700600056103054100c501c085120440100030462010101d104019550196000303058010a1184c9a40d207460351204800785a22069030854108450140f5000c00440d182c402100102100c040384c08600041c490b2000104035a006648002c10017032900c040381401800282004403c5035102c2c0c1400e480040c10001819134900d41d50345040c0d002c10061b0b07000030b442d61680ba440b1582c0784180c05142854802070142480c102040d41ea0b5120728010154001d00a010310003242d1119014070b1142c01800710110350460300250000e03801c0d0014032981d8000d0058a0f40807000908551034501d1401000c3d0946803110078036400320b0707200e19890700000c03d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 377860341 1250 377859091 377859107
    0xc010e011d0705040908040302150d0c030209040b01050901170c0f0706091112100b0a0810060806010f080a081b07140f060307022e0603051e030306030307031b17030403 74
    0x14100d42c1404020701c5c50702c586505119503c4001c3c03240c001d00c0320301001d018550003542c42071401044200440c5c0c10703005d4040d02035030050700c145219a1400100240560080c0c0035101d100c0810394420200c0400343e07540c00c03104040a0310f4154018018441146d0040f01c00c0c0040002c0c1e841924049082d901d81d00d0585c010500d00481c05c0e1240310b81da13000e103c0c1c082c400204119000b0300d00c0c4001c1054078100307010500c00440e607049005a8021141051020403103604603800300e500001c129006a0f0ba10410322202c40c2070b90141d0030007a00010b00b96408030300c1c0e5078054141c90000d40160580200004185880c1c2074890b40001400344607900000c003540703464100550b800354241d69075443d51503c0d040081d103400302102598214864481c1200305a80701e60740800c10300841e0381041000c0342d201d040c5142d541030481603619000b815540c1c8045c40301008001d490041c00c01134001d60030600d031981e090b500704200c040900d40b46a42259000c010540c06000d00c1c24401a5012030b82e980e00b454100101010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 377861591 1250 377860341 377860349
    0x8041103011808120604140c071109090a051612110411031810050c040302010804050a05010f2708041203210507030c08060a060e011403070503060112060b030c0c010e011d07 76
    0xc0c41c10307404903035500e84107c907598040c80022201d0b40e00d402e680390004050412803800b68100788520200200c007000010400002805102101e404801410700005040c0c50b500030540d408051900c0c4900150751200102400580200040b440000315210004650811195401c8541032a12010706200301803280070000701256038240311900d4400b060340018452441700030b0400403140c000400b48003050000ca20b4140c1c2c00320007807100310249010b030400350142001c1780316080c10003141007841e000c1207448202110b601694543c281031030207140d9120324400003410b0b418401e5550031501000d2544080307043e0406c07182400241420034280041c11542d10380031490034054000180041c5a0324001c1c80e000302c0e04246451202030080c00c0040b5910010b072036081d60742201c0071060084035031300080654881c1ea400e90365500d00000038400075040d16074034440c8031761000040001c5110108000020540100420700214030585030200c82e600716218405082400c2c400c43d080392003442c0060009070010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 377862841 1250 377861591 377861599
    0x509010309140f240606161e0506180604051005060a031b1a09031c03090b010806010311181f0b030f010e0901090b01050d030309050616120606080411030118081206 72
    0x50700d170050102e0301504c5400568503041900c0c2e2401c208001c0003a0042401107455400742c41340300c1003480e01e2650340310f041d200d000641401c0043d000b680c000c0000c595208580100040202c0400242c2d894014003000d0042c64001c00c46180100c085001010031034445030490451206071840d00e000c41da003240e480740361008460f40821032820315070342c009000d9081504030b0082c0c03036500800300c605a00406a842d03000340031b00041000055101004504107040741d002c0d0544219080a45007000180590300480025420900700802e08034041b152032820580c600300001c001079030320380311036000507041280c3c5481b005200344014030450389440000c07600120074500900540c03034a6554441844c805000e05402072070604070440a05220b078005d5504540c1000c03e90f04c0d10b050030004009021085840d4070041000c40038110729a540c0c501c140400c80da4103a944c006152159902c02188a03105903c80e0703859074948000c0108030349555850300540d84034101310366071415018804941920010300d07052007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 377864091 1250 377862841 377862913
    0x5150a0501032a051306090509010207030801060e030307060603050f0f0f0c061309050c0406080702031206010813080a050a11060606070f140604060b041a010509010309140f 76
    0xa00c4080100407410048801100c2180643c400f4129090a50b07100d00c0d800180b02007552034540443d80100b042d12050311041c401691a4a0756600380d2003807060040000700c031200104503c2d84070304031260001d0001800e5038035160301d940350201564600d80013520346421500b41e020710703040100480341e01142c1900107001d42010b4200020385503081094040d005400024000c0d4280f044d81038081701130100da810400a50420a14224a940282c010036010600050118107014000001c1c5c4600350081a10441550b035174100440c1c141c080504030030781141101d480c00000654010152041a0383d07555519118941c0c0d15000304610b48030904083c1170b40200c0c0600c580c60316503004850f00b482e00020030142d031441e249059030529079802002000d41c0075030300501c004c00905400c000f20322601203e0521400c0b0800400f240b600c0300113000d2038041a020841240154001c0c1c0018011500031084aa18400711b5503500b4105030442c17052180300c2c1c014a02000e960b00f5070f0a00c9240d940304094540031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 377865341 1250 377864091 377864093
    0x503010815010f1512090b041a0f191503030320040b04090b0a0816030303230109180204090b0f2202060702060c0312010e01150e090702010902060705150a050103 71
    0x105400d07020f4568260f8402c0c2d5004d42a500884030071a1016000318100b06880090401030b101c62829901114192143c0ea401070317102c005250307514010030120030640b0698465800c0700401040003070756103403900d4803a42e404071440d5100c00c14000a502a8034040f03514182903402d002850602d030442076a0f031000744014051a400101a5020f541ea050000550103840e1000200401803d9100309580d01c1491804000c0c03032504d20700070003182d2013a1405d22251800030303a88000402141403201d101454400100200259031300f021020300001a03084050260b00d401240681e001884290780000540c0203000d04c4002103440581d00c5403488200b500c0b41810440801c3c504201c80340003038820134001c600c100641d0340304000c070b6864082074001c49a07074180081080100c11024496203103441c81c168000200c1504103c04c4007140c07042595411440c01d40e0030208402c01c0400f901210841d0760b2290002c00503203c4030000d22016000740700506030311401040804d02120b00500c0c5a41c401c1c28840100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 377866591 1250 377865341 377865359
    0xa050d0503070b13020d1202010501120302030a2106090b090c040e0118020f1204051b0616081e07050d170f07210207030e0301060b0f0c030712050301081501 69
    0x8071070755407281c4510303501e840f89542071513001442800079520018030131180e41048401201031100b040325800900007a80c0e40c0ea00b05407543c41400028000d41c0040000b100c130a8401c03110005690040c820400912480c041004c0c01c8840e590003050030580e4907803e906841c50700040d40d43e072010311040c5152400b410181c201002c0d410610030b5001443e01d04500518200300c035015110000c8650504075110326000c160000420003e071402d4400c0d0180c882c403c00508182c1025091520000c0c1203541703042d2002c0c0c103903003030b100401009680d1010306100480c906110040c230b44c580c0414040300d59807203a0090821030709150500c44410140f06103080202101488010211f40c0510903200307440382561a00815500c0310521051070b02b6813813080702042c03400765555015150303060196807505110305a84041c142210058001c40c248800c06104206070310040500400c0c0b10103084040ea41426465914019022901c0c4500c2d00805c00200c010301440204010921130914184001d107403e51501183c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 377867841 1250 377866591 377866597
    0x1e03200301150c0302100504111306030305091003060b0c033a020a110607051c0204050604090b060f0f041a18041815090b01060c0305040e151e0a050d0503 68
    0x803009001100e84804203141c024001c2425940d00b0840510131f610340741c41e20050614000b40d216108407401a15020140c085100d50010740341d06440300c1d0301d00184c840c200140c03410385000741402c1580780c040108074084810b01030166007010900841d1031700e40d01030303140b42d058903039496801244100000344548042800c040c0c0034410301c417582c010781d10300c003c0400711050141944c6003000c078810030040c440c0042d0700c1401856294101010100409800c4804400b0ba11443c8180340d8007107424802400040c400341d00510340790a0003088039251144152a40c84950428130801d0314201c00480c003004910740300382003000403c410b100124035101c0710300c00200048241c03602c000c1c0110b60307070110304944081501c8015001c9801501596040980c2c2042c034001e04694201140c0d403510610000800500030300808014540c16120741d4101030900b07014160703441e80148010001e8000c154a20b0440d1141f4100c0ea460b04c22840204170b140c902802070001d00d007000d0340824054181a02848080340001c019 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 377869091 1250 377867841 377867879
    0x10050703080a2c0a12020c1f0918050907060302030f040b100909080903010c080c0313030315060e102f0f010c0f09062c011e03200301 59
    0x107101c901c82d03040703c120003016120b43c01140c140e0703002603042288001520302c1110300c10a0100501c40540c801240ca40e04040a01504680561000c190705c02d0703400e40308001c02a40e45414902c1580d00c0740c64040e81c0102c10b02c44c016055460092280007a0240a51b0021300441d040940c55401c1c8440b8040301880e00902c00740c000e41810f07020a01c0190007201000061000350420f2003101802d00304429aa031140300da4611075841c3c0451401d90f2800744412903c51224490001d08658442c42c600311800340c0c18400300d007016580c40c2481c8401a00180e10005815242e80b030841daa40005d0910603291000c15085084c0080880c2c612200c036480e00003000c1c4111000000130300c0380e0302081098600241102c2008a5508000e200103105c0e40c0440000001d012135030f40d2183c000c1e03547e03009841c0c10204030f030840c03940d03c260b60380d508504612520034040c0000624142006d1415521100c900c1106003450b00d00190700c4032607011035101e00c00440c0310542c0d00004000d28551401081d640c0400400340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 377870341 1250 377869091 377869111
    0xc0308010815070804050f01110909011211090c070b0106050a030f11031603060503062508010302031203060d020901030c060201060807150f02030706090c0f0602010b0f040b06040f0e061005070308 86
    0x8000f174108001884584000b000d510001d00200080d400382c1510303500000411405240d003e00001003a0080700d00100850390418510308120a840c814400c0801c4000c000b0402001e04004540c001032680c8201402400a5034503e80c881880d61002416986414400c0d0122400c100d0701d40c0c0000c010303004498110380841800c01001c0310440c000c0d00901500e0340119818060307001044902030710401980072540c124440c945491b041d080e000d42d010300007800042e40561200712110201c0f1a20801507821010081c40d4901041c010383c0000c20619090308120340041880001708504c5409004240190241001800c0d8190030801c03c00400702041c0380800400c54045940c0410600a0040322016908000e00748190309580c249014040c2c1d95200d112030b100d4007043c00003012481032091311034820005220140c002c410400b008080d001c8a61081d51005003000000740c01c10107028200001d000c003140c85c1d441c3e0301c0d004041040040545403403005001003048502c3c00250b000800700d9224240785 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 377871591 1250 377870341 377870357
    0x6031d1b04060e0c03330d21030e100603080f030c09030703051b0427150e01050a0c020703020a061407140109020a090209060d0e150103030c030801081507 68
    0x200019000c0e005640c030442118075003c0c00d103c480c07013001008601c68052103245851040300142d0000e018807400c40c0320340000700e078254030207414940031140da900301c2c0c041c80755801c5171184110000300d4044081c4591001c00e40d500d6052441503010b00002104940c00f20082018502d140c0314500b06109504148221600010026240c0c0c0541e1007560b03034903403000d0b04544032507490f03160a9564290701000c0050110341540040c040385007034001c0441d51990581306143d100052444c0244042c0011000c4038140c4c0f80042e030078503052007031055001100c0002c00101f01410141304580843e41b40a81060842d0450300061000d600c89070703800b4046030440e01d844180d0b6555103144880d14003444c1c40040c0058000356070b40600c5681500194003482c0211002040c00b83e4407010724040b407085041d19600100c09200b8480c0c19052507202c2540707803100c3c50944a051105a0b450354998030300340c00c220007060605540405040c1c0c000740c076501400011009007000040d8220502008030002c10020401c5945 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 377872841 1250 377871591 377871643
    0x4080a122a171e100e041b0b041203051308060a1415010503061017070c0506090109020307050d0f06060b12010605210c1204110f1503040803100807030b0106031d 71
    0x55042c000080c01034540340c00441c105440c00344844442c18561001c0d210b000d1f000490400300d070310201d4041f03d440c0c0c0342c4c0c4103098400e40e80c203a07507540111180740c610b130210110004116505000003403180b440408005880907405d0b0413014040f00c050400070601d80038014151b03150340c00904903500907101720351104112041c0d59044880f03005d8488071400303031030441e0203000c0c0150b00140074405041c858001e50340d00703682d892f482500301d4a41d200042d505078406501080a0f0038265100035031980200701d10402ca020503224070b000c0c0c2e855503218031420789001030340340100c01003845407602400380d5107003403842c000c1c3d044100c0400380050580d031803c2c0c0e00340c40b02041d9120940400c03502d1821300c3d01e180100b1440c00e410400c0ba004c505c904024010326809605071418a8604241c2c0d074a0034600c51001d081d515151185005900000c002c0c0c88644c2c214040070035940c20030000c2d0070065109130050311b203c0d07051107801019106106200604011b94a80c1d00181c0503010038000280c3c81008100782c102854 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 377874091 1250 377872841 377872861
    0x1803040b0901030e0a0f1a0f0424020d1e0b101d130903080901050c04080a1103070302060c031c0b03030711060f1204050f030304080a122a171e 63
    0x450100105000d11810b1404100400c1224042552160401c7d120060340d9016940407002404c660040c08074058511400030462100d901a600324060200141400b007192003010803a0480c0510b0056520400e010220785041030042d032842d507609881c0c1da18420010140a014412030039448441c03080d50002140d001d403503002c0b0202c0321210764081800406800c2c00d0141441005a510748825420f0000003600304102c14215800c44200c400140b903070303525584460340e5000c54032900341da00d401042400405a9140f030090800007444002850769964070315040c40d000000060710783d95060805074041d48076075020003035400c140e410400c480c1e10101c0ca10006442442030b5024210790080118034144014049032104d4407481c807542c12104041200081d159488c042141c00402d044800c1202c40d4940d07203d541c3c0c90195014800300802d900304203040305802c3c5040b25a1444540c01e141c908810300c1544880342d41c0800f141e89080450900f008000c00401806412001c94084616404101c40c0c80e1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 377875341 1250 377874091 377874103
    0x90907051615050405060a0b01050901050c070e0f0114030c10110a0c080c01020705060304020d0f0c0305100b0127050f060c07030302030408060a060e13020d0b010902031803040b0901030e 82
    0x80d021190242d2095100c03440002001c0030754060f00c2500c40e00f000198040e21501c254966144141c44982c00d000c00ca00c0111029805418056014024844001000390b001d025050180b02d9801d220205581003030408803201d11900c00c1580310381c3c03000c1d64604180e191900030381c0680005251942c0c8600c6a200d00358500f0f550b4410081202c4201040015075500204074944600002d030300b6a14866600d20400c5480e001c16600a0b40c0901d54411a0f0001090156144943e82c421001c0303820180e5640c8a19041011000c0c0d1a0011a2500b04601c03c0d507a000203aa41070307200e4100c070042d0714640450620b011100d01e006980c0116032002c5c44080c82e0380d90105072210b01480350100c400c642d803280340081d103a0300144100c901500c515004111544d03d640200b07426140f40480e2844295103c43d0030002002000d002a42c00003500101c680c041011041498040d001100d07000d41e4a09001e811003a1200114070010030a80007404144100c01c00d5400b121401e003024079003c503890b00da20b205141400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 377876591 1250 377875341 377875343
    0x90102100c0905012006040302030a0905060301030218070c051906063204060317121312080604090506070e030c15030c090f030715080109050108030706090501020405030d0206010314030909070516 86
    0x2200f0321b8104420540d0000c02862003501030340c0e0b0700d81100c2d520b4050010b80d00003800020350003071090030840c0180101110329948500b05190414100c0703666101c07213042c01c015080020313182207a6045002441110b00914005126940d20100f40c008030070a8104014090780c80c1c0003500c03808180003032407660b464029401031a0800d401445a0702c41404160403548520f1a13140440c1420001443e00595070f031050103841d81210301c140403460301840c2120960301c001c0c45594400d40c0e8007903000c041401040154422003158442a84101040c0201890700d20015280c030311504025030045000301403441038035006018002c6213500d80b403070342000468202d091071550303401d0b10965100003408051003007507910074496a224116070766222108582a00d00901038444940d00070880c510000b28903620001d040303400340300010306254654000a00703240045d543e280040c0e000c0001070060007008a41040d0b800c121400a5242000000204000c184002c3c002424000c1c08119400c50b8004080d040fa221 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 377877697 1106 377876591 377876593
    0x312030e1e030d060806060108090d051803102a091203050a09080619050a090209180f030f03090d020604030801090207110405090102090102100c09050120 68
    0x8081c06412246035102c20031950b0140382140c46224042d041410103441c41d4100540018801140500b5085d0b0981040c0d0712035010540003003c854007080401e03800c806906401c00007a040903040d80122042c80d081c01c90092191f480000d46134040c48010364803c0c5581c04105c0100c036121224012503412400e0a0f40c0000400c0c0a1009804480154504845c403d41c9442803141072040c1500e46907a20398680204243d60200b902a00b644040801e41c00c000d03118143d000189510009451a2080c4914601c8248010b10034407401289005801c00c0360b44d21020421600d0382030307004231240c0ea15402207210f590f45003403011410f80d0103143c05a40e1191643d0a00c0d00da80000d40c8814000c4628030029220015a612940150340c03140c0c1c0351000041c0c0703611b120b00002e400e00d0100f03650051610300c2e1084504c10140c00200c40c10031748074203180a2640140801000c4442001e00c3c000c25a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 377697841 377877697 := by
  have h0 := BRFrame.cov_init 377697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 377697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 377697841 ≤ n) (h2 : n < 377877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
